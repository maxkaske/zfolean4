import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Insert
import Mathlib.Tactic.Attr.Register
import Lean.Elab.Tactic

/-- Simplification rules for routine combinations of lifts and substitutions. -/
register_simp_attr tls

open Lean Meta Parser.Tactic Elab.Tactic

private structure TlsContextMember where
  value : Expr
  proof : Expr

private def collectTlsContextMembers (set : Expr) : MetaM (Array TlsContextMember) := do
  let rec visit (set : Expr) (fuel : Nat) : MetaM (Array TlsContextMember) := do
    if fuel = 0 then
      return #[]
    let set ← instantiateMVars set
    let fn := set.getAppFn
    let args := set.getAppArgs
    if fn.isConstOf ``insert && args.size == 5 then
      let head := args[3]!
      let tail := args[4]!
      let headProof ← mkAppM ``Set.mem_insert #[head, tail]
      let mut result := #[⟨head, headProof⟩]
      for member in ← visit tail (fuel - 1) do
        let proof ← mkAppM ``Set.mem_insert_of_mem #[head, member.proof]
        result := result.push ⟨member.value, proof⟩
      return result
    if fn.isConstOf ``Set.insert && args.size == 3 then
      let head := args[1]!
      let tail := args[2]!
      let headProof ← mkAppM ``Set.mem_insert #[head, tail]
      let mut result := #[⟨head, headProof⟩]
      for member in ← visit tail (fuel - 1) do
        let proof ← mkAppM ``Set.mem_insert_of_mem #[head, member.proof]
        result := result.push ⟨member.value, proof⟩
      return result
    if fn.isConstOf ``Set.image && args.size == 4 then
      let map := args[2]!
      let source := args[3]!
      let mut result := #[]
      for member in ← visit source (fuel - 1) do
        let proof ← mkAppM ``Set.mem_image_of_mem #[map, member.proof]
        result := result.push ⟨mkApp map member.value, proof⟩
      return result
    if fn.isConstOf ``Set.singleton && args.size == 2 then
      let value := args[1]!
      let proof ← mkAppM ``Set.mem_singleton #[value]
      return #[⟨value, proof⟩]
    if fn.isConstOf ``Singleton.singleton && args.size == 4 then
      let value := args[3]!
      let proof ← mkAppM ``Set.mem_singleton #[value]
      return #[⟨value, proof⟩]
    let mut result := #[]
    for localDecl in ← getLCtx do
      if localDecl.isImplementationDetail then
        continue
      let type ← instantiateMVars localDecl.type
      let typeFn := type.getAppFn
      let typeArgs := type.getAppArgs
      if typeFn.isConstOf ``Membership.mem then
        if typeArgs.size == 5 then
          if ← isDefEq typeArgs[3]! set then
            result := result.push ⟨typeArgs[4]!, localDecl.toExpr⟩
    return result
  visit set 64

private def tlsContext (simpTac : Syntax) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let fn := target.getAppFn
  let args := target.getAppArgs
  unless fn.isConstOf ``Membership.mem && args.size == 5 do
    throwError "`tls` could not discharge the bookkeeping goal"
  let set := args[3]!
  let value := args[4]!
  for member in ← collectTlsContextMembers set do
    let saved ← saveState
    try
      let equality ← mkFreshExprMVar (← mkEq value member.value)
      setGoals [equality.mvarId!]
      evalTactic simpTac
      unless (← getGoals).isEmpty do
        throwError "candidate did not match"
      let equalityProof ← instantiateMVars equality
      let proof ← mkAppM ``Set.mem_of_eq_of_mem #[equalityProof, member.proof]
      goal.assign proof
      setGoals []
      return
    catch _ =>
      saved.restore
  throwError "`tls` found no matching formula in the transformed context:{indentExpr target}"

syntax (name := tlsContextTac) "tls_context" (simpArgs)? : tactic

elab_rules : tactic
  | `(tactic| tls_context $[[$simpArgs,*]]?) => do
      let args := simpArgs.map (·.getElems) |>.getD #[]
      let simpTac ← `(tactic| first | rfl | simp [tls, $args,*])
      tlsContext simpTac

/--
Discharge the bookkeeping side conditions of first-order proof constructors.

Besides simplifying lifts and substitutions with the `tls` simp set, this
tactic follows membership through contexts built from `Set.insert` and
`Set.image`. Optional arguments add local simplification rules without making
the tactic depend on a particular object theory.
-/
syntax (name := tlsTac) "tls" (simpArgs)? : tactic

macro_rules
  | `(tactic| tls $[[$simpArgs,*]]?) => do
      let args := simpArgs.map (·.getElems) |>.getD #[]
      `(tactic|
        (try simp only [tls, $args,*]) <;>
          first
            | assumption
            | rfl
            | tls_context [$args,*])
