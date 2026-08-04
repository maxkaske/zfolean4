import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Insert
import Mathlib.Data.Nat.Order.Lemmas
import Lean.Elab.Tactic.Omega
import Zfolean4.Tls

set_option linter.style.header false

/-!
# First-order predicate logic

This is the Lean 4 port of the syntax of intuitionistic first-order logic and its natural
deduction proof calculus from `zfolean/src/fol.lean`.

The representation uses partially applied terms and formulas together with de Bruijn indices.

## Main result

- `formula σ`      : the definition of first-order formulas over a signature σ
- `proof_term σ`   : the definition of proof terms of natural deduction over a signature σ

## Notations

We define the following notations for lifts and substitutions:

- `X ↑ m ＠ i` for `lift X s k`  where `X` can be a term or a formula .
- `X[ s ⁄ k ]` for `subst X s k` where `X` can be a term or a formula .
- `Γ ⊢ φ` for `proof_term Γ φ`

We use the following local notations

- `>>` for `set.insert`

## Notes

We wrote comments whenever we felt like a topic wasn't really covered by the literature referenced.

## References

* [N.G. de Bruijn, *Lambda calculus notation with nameless dummies*] [DB72]
  -- the original paper describing de Bruijn indices
* [J.M. Han, F.van Doorn, *A Formal Proof of the Independence of the Continuum Hypothesis*] [HD20]
  -- we followed their implementation of first-order logic using "partially applied"
  -- See also: https://flypitch.github.io/
* [I. Chiswell, W. Hodges,*Mathematical Logic*] [CH04]
  -- first order logic and natural deduction
* [M. Huth, M. Ryan, *Logic in computer science*] [HR04]
  -- first order logic and natural deduction
* [S. Berghofer, C. Urban, *A Head-to-Head Comparison of de Bruijn Indices and Names*] [BH07]
  -- for a good breakdown of the proof of the substitution lemma `subst_subst`
* https://github.com/coq-community/dblib/blob/master/src/DeBruijn.v
  -- as a good reference on lifting and substitution lemmas for de Bruijn indices
-/

open Nat Set

universe u

namespace fol

/-- A first-order signature, indexed by the arities of its function and predicate symbols. -/
structure signature : Type (u + 1) where
  func_symb : ℕ → Type u
  pred_symb : ℕ → Type u

def signature.constants (σ : signature) := σ.func_symb 0

inductive sorry_nothing : ℕ → Type u

def trivial_signature : signature where
  func_symb := sorry_nothing
  pred_symb := sorry_nothing

variable (σ : signature.{u})

/-! ### Terms -/

/-- A partially applied first-order term. Applying `a` more arguments produces a term. -/
inductive preterm : ℕ → Type u where
  | var (index : ℕ) : preterm 0
  | func {arity : ℕ} (f : σ.func_symb arity) : preterm arity
  | fapp {arity : ℕ} (t : preterm (arity + 1)) (s : preterm 0) : preterm arity

export preterm (var func fapp)

prefix:max "#" => preterm.var

abbrev term := preterm σ 0

variable {σ}

namespace term

/-- Increase every variable index at least `i` by `m`. -/
def lift : {a : ℕ} → preterm σ a → ℕ → ℕ → preterm σ a
  | _, #x, m, i => #(if i ≤ x then x + m else x)
  | _, func f, _, _ => func f
  | _, fapp t s, m, i => fapp (lift t m i) (lift s m i)

end term

/-- we use ＠ (U+FF20) instead of the regular @ (U+0040) to avoid conflicts-/
notation:90 t:90 " ↑ " m:91 " ＠ " i:91 => term.lift t m i

namespace term

@[simp, tls] lemma lift_fapp {a} (t : preterm σ (a + 1)) (s : preterm σ 0)
    (m i : ℕ) : (fapp t s) ↑ m ＠ i = fapp (t ↑ m ＠ i) (s ↑ m ＠ i) := rfl

@[simp, tls] lemma lift_func {a} (f : σ.func_symb a) (m i : ℕ) :
    (func f) ↑ m ＠ i = func f := rfl

@[simp] lemma lift_var_lt {x m i : ℕ} (H : x < i) :
    #x ↑ m ＠ i = (#x : term σ) := by
  simp [lift, show ¬i ≤ x by omega]

@[simp, tls] lemma lift_var_eq {x m : ℕ} :
    #x ↑ m ＠ x = (#(x + m) : term σ) := by
  simp [lift]

@[simp] lemma lift_var_gt {x m i : ℕ} (H : i < x) :
    #x ↑ m ＠ i = (#(x + m) : term σ) := by
  simp [lift, H.le]

@[simp] lemma lift_var_ge {x m i : ℕ} (H : i ≤ x) :
    #x ↑ m ＠ i = (#(x + m) : term σ) := by
  simp [lift, H]

@[simp] lemma lift_var_nge {x m i : ℕ} (H : ¬i ≤ x) :
    #x ↑ m ＠ i = (#x : term σ) := by
  simp [lift, H]

@[simp, tls] lemma lift_by_0 {a} (t : preterm σ a) {i} : t ↑ 0 ＠ i = t := by
  induction t with
  | var x => simp [lift]
  | func f => rfl
  | fapp t s iht ihs => simp [lift, iht, ihs]

lemma lift_lift {a} (t : preterm σ a) (m : ℕ) {i} (n : ℕ) {j} (H : j ≤ i) :
    (t ↑ m ＠ i) ↑ n ＠ j = (t ↑ n ＠ j) ↑ m ＠ (i + n) := by
  induction t with
  | var x =>
      by_cases hix : i ≤ x
      · have hjx : j ≤ x := by omega
        have hjxm : j ≤ x + m := by omega
        simp [lift, hix, hjx, hjxm]
        omega
      · have hinxn : ¬i + n ≤ x + n := by omega
        have hinx : ¬i + n ≤ x := by omega
        by_cases hjx : j ≤ x
        · simp [lift, hix, hinxn, hjx]
        · simp [lift, hix, hinx, hjx]
  | func f => rfl
  | fapp t s iht ihs => simp [lift, iht, ihs]

lemma lift_lift_reverse {a} (t : preterm σ a) {m i} (n : ℕ) {j} (H : i + m ≤ j) :
    (t ↑ m ＠ i) ↑ n ＠ j = (t ↑ n ＠ (j - m)) ↑ m ＠ i := by
  have hij : i ≤ j - m := by omega
  have hmj : m ≤ j := by omega
  rw [lift_lift t n m hij, Nat.sub_add_cancel hmj]

lemma lift_lift_merge {a} (t : preterm σ a) {m i} (n : ℕ) {j} (H : i ≤ j)
    (H' : j ≤ i + m) : (t ↑ m ＠ i) ↑ n ＠ j = t ↑ (m + n) ＠ i := by
  induction t with
  | var x =>
      by_cases hix : i ≤ x
      · have hjxm : j ≤ x + m := by omega
        simp [lift, hix, hjxm, Nat.add_assoc]
      · have hjx : ¬j ≤ x := by omega
        simp [lift, hix, hjx]
  | func f => rfl
  | fapp t s iht ihs => simp [lift, iht, ihs]

lemma lift_by_succ {a} (t : preterm σ a) {m i} :
    t ↑ (m + 1) ＠ i = (t ↑ 1 ＠ i) ↑ m ＠ i := by
  symm
  simpa [Nat.add_comm] using
    (lift_lift_merge t (m := 1) (i := i) m (j := i) le_rfl (by omega))

/-- Substitute `s ↑ k ＠ 0` for variable `k`, decrementing larger indices. -/
def subst : {a : ℕ} → preterm σ a → term σ → ℕ → preterm σ a
  | _, #x, s, k => if x < k then #x else if k < x then #(x - 1) else s ↑ k ＠ 0
  | _, func f, _, _ => func f
  | _, fapp t₁ t₂, s, k => fapp (subst t₁ s k) (subst t₂ s k)

end term

notation:100 t:max "[" s " ⁄ " n "]" => term.subst t s n

namespace term

@[simp, tls] lemma subst_fapp {a} (t₁ : preterm σ (a + 1)) (t₂ s : preterm σ 0)
    (k : ℕ) : (fapp t₁ t₂)[s ⁄ k] = fapp (t₁[s ⁄ k]) (t₂[s ⁄ k]) := rfl

@[simp, tls] lemma subst_func {a} (f : σ.func_symb a) (s : term σ) (k : ℕ) :
    (func f)[s ⁄ k] = func f := rfl

@[simp] lemma subst_var_lt (s : term σ) {x k : ℕ} (H : x < k) : (#x)[s ⁄ k] = #x := by
  simp [subst, H]

@[simp, tls] lemma subst_var_eq (s : term σ) {k : ℕ} : (#k)[s ⁄ k] = s ↑ k ＠ 0 := by
  simp [subst]

@[simp] lemma subst_var_gt (s : term σ) {x k : ℕ} (H : k < x) :
    (#x)[s ⁄ k] = #(x - 1) := by
  simp [subst, H, H.asymm]

@[simp] lemma subst_var_nle (s : term σ) {x k : ℕ} (H : ¬x ≤ k) :
    (#x)[s ⁄ k] = #(x - 1) := subst_var_gt s (by omega)

@[simp, tls] lemma subst_var0 (s : term σ) : (#0)[s ⁄ 0] = s := by
  simp

lemma lift_subst {a} (t : preterm σ a) (s : term σ) (m : ℕ) {i} (k : ℕ) (H : i ≤ k) :
    t[s ⁄ k] ↑ m ＠ i = (t ↑ m ＠ i)[s ⁄ (k + m)] := by
  induction t with
  | var x =>
      rcases lt_trichotomy x k with hx | hx | hx
      · have hxkm : x < k + m := by omega
        by_cases hix : i ≤ x <;> simp [subst, lift, hx, hxkm, hix]
      · subst x
        simp [subst, lift, H, lift_lift_merge, Nat.add_comm]
      · have hix : i < x := by omega
        have hx1 : 1 ≤ x := by omega
        have hsub : i ≤ x - 1 := by omega
        have hnxk : ¬x < k := by omega
        have hkm : k + m < x + m := by omega
        simp [subst, lift, hx, hnxk, hix.le, hsub, hx1, hkm, Nat.sub_add_comm]
  | func f => rfl
  | fapp t₁ t₂ ih₁ ih₂ => simp [lift, subst, ih₁, ih₂]

lemma subst_lift {a} (t : preterm σ a) (s : term σ) {m i k : ℕ} (H : i ≤ k)
    (H' : k ≤ i + m) : (t ↑ (m + 1) ＠ i)[s ⁄ k] = t ↑ m ＠ i := by
  induction t with
  | var x =>
      by_cases hix : i ≤ x
      · have hk : k < x + (m + 1) := by omega
        simp [lift, hix, hk]
      · have hxk : x < k := by omega
        simp [lift, hix, hxk]
  | func f => rfl
  | fapp t₁ t₂ ih₁ ih₂ => simp [lift, ih₁, ih₂]

lemma subst_subst {a} (t : preterm σ a) (s₁ : term σ) {k₁} (s₂ : term σ) {k₂}
    (H : k₁ ≤ k₂) : (t[s₁ ⁄ k₁])[s₂ ⁄ k₂] =
      (t[s₂ ⁄ (k₂ + 1)])[(s₁[s₂ ⁄ (k₂ - k₁)]) ⁄ k₁] := by
  induction t with
  | var x =>
      rcases lt_trichotomy x k₁ with hx | hx | hx
      · have hx₂ : x < k₂ := by omega
        simp [subst, hx, hx₂, show x < k₂ + 1 by omega]
      · subst x
        have hk : k₁ < k₂ + 1 := by omega
        simp [subst, hk, lift_subst, Nat.sub_add_cancel H]
      · rcases lt_trichotomy (x - 1) k₂ with hx₂ | hx₂ | hx₂
        · have hxk : x < k₂ + 1 := by omega
          have hnxk₁ : ¬x < k₁ := by omega
          simp [subst, hx, hx₂, hxk, hnxk₁]
        · have hxpos : 1 ≤ x := by omega
          have hxeq : x = k₂ + 1 := by omega
          subst x
          have hnot : ¬k₂ + 1 < k₁ := by omega
          simp [subst, H, hx, hnot, subst_lift]
        · have hkx : k₂ + 1 < x := by omega
          have hk₁x : k₁ < x - 1 := by omega
          have hnxk₁ : ¬x < k₁ := by omega
          have hnxk₂ : ¬x < k₂ + 1 := by omega
          simp [subst, hx, hx₂, hkx, hk₁x, hnxk₁, hnxk₂]
  | func f => rfl
  | fapp t₁ t₂ ih₁ ih₂ => simp [subst, ih₁, ih₂]

lemma subst_lift_by_lift {a} (t : preterm σ a) (s : term σ) (m i k : ℕ) :
    (t ↑ m ＠ (i + k + 1))[(s ↑ m ＠ i) ⁄ k] = t[s ⁄ k] ↑ m ＠ (i + k) := by
  induction t with
  | var x =>
      by_cases hhigh : i + k + 1 ≤ x
      · have hkx : k < x := by omega
        have hkxm : k < x + m := by omega
        have hsub : i + k ≤ x - 1 := by omega
        have hxpos : 1 ≤ x := by omega
        have hnxk : ¬x < k := by omega
        simp [lift, subst, hhigh, hkx, hkxm, hsub, hxpos, hnxk,
          Nat.sub_add_comm]
      · rcases lt_trichotomy x k with hx | hx | hx
        · have hlow : ¬i + k ≤ x := by omega
          simp [lift, subst, hx, hhigh, hlow]
        · subst x
          have hbound : ¬i + k + 1 ≤ k := by omega
          simp only [lift]
          simp only [hbound, if_false, subst_var_eq]
          exact lift_lift s m k (Nat.zero_le i)
        · have hsub : ¬i + k ≤ x - 1 := by omega
          have hnxk : ¬x < k := by omega
          simp [lift, subst, hx, hnxk, hhigh, hsub]
  | func f => rfl
  | fapp t₁ t₂ ih₁ ih₂ => simp [lift, subst, ih₁, ih₂]

lemma subst_var0_lift {a} (t : preterm σ a) (m i : ℕ) :
    (t ↑ (m + 1) ＠ (i + 1))[#0 ⁄ i] = t ↑ m ＠ (i + 1) := by
  induction t with
  | var x =>
      rcases lt_trichotomy i x with hx | hx | hx
      · have hil : i + 1 ≤ x := by omega
        have higt : i < x + (m + 1) := by omega
        simp [lift, hil, higt]
      · subst x
        simp [lift, show ¬i + 1 ≤ i by omega]
      · simp [lift, hx, show ¬i + 1 ≤ x by omega]
  | func f => rfl
  | fapp t₁ t₂ ih₁ ih₂ => simp [lift, ih₁, ih₂]

@[simp, tls] lemma subst_var0_lift_by_1 {a} (t : preterm σ a) (i : ℕ) :
    (t ↑ 1 ＠ (i + 1))[#0 ⁄ i] = t := by
  simpa using subst_var0_lift t 0 i

@[simp, tls] lemma subst_for_0_lift_by_1 {a} (t : preterm σ a) (s : term σ) :
    (t ↑ 1 ＠ 0)[s ⁄ 0] = t := by
  induction t with
  | var x => simp [lift]
  | func f => rfl
  | fapp t₁ t₂ ih₁ ih₂ => simp [lift, ih₁, ih₂]

/-- The largest variable index occurring in a term, plus one. -/
def max_free_var : {a : ℕ} → preterm σ a → ℕ
  | _, #x => x + 1
  | _, func _ => 0
  | _, fapp t s => max (max_free_var t) (max_free_var s)

lemma lift_fixed_points_monotone {a} {t : preterm σ a} {i j : ℕ} (h : i ≤ j)
    (H : t ↑ 1 ＠ i = t) : t ↑ 1 ＠ j = t := by
  induction j with
  | zero => simpa [Nat.eq_zero_of_le_zero h] using H
  | succ j ih =>
      by_cases hij : i = j + 1
      · simpa [hij] using H
      · have hij' : i ≤ j := by omega
        rw [← H, ← lift_lift t 1 1 hij', ih hij']

@[simp, tls] lemma lift_at_max_free_var {a} (t : preterm σ a) :
    t ↑ 1 ＠ max_free_var t = t := by
  induction t with
  | var x => simp [max_free_var, lift, show ¬x + 1 ≤ x by omega]
  | func f => rfl
  | fapp t s iht ihs =>
      simp only [max_free_var, lift]
      exact congrArg₂ fapp
        (lift_fixed_points_monotone (le_max_left _ _) iht)
        (lift_fixed_points_monotone (le_max_right _ _) ihs)

end term

/-! ### Formulas -/

section formulas

variable (σ)

/-- A partially applied first-order formula. Applying `a` more terms produces a formula. -/
inductive preformula : ℕ → Type u where
  | bot : preformula 0
  | eq (t s : term σ) : preformula 0
  | implication (left right : preformula 0) : preformula 0
  | conjunction (left right : preformula 0) : preformula 0
  | disjunction (left right : preformula 0) : preformula 0
  | universal (body : preformula 0) : preformula 0
  | existential (body : preformula 0) : preformula 0
  | pred {arity : ℕ} (P : σ.pred_symb arity) : preformula arity
  | papp {arity : ℕ} (body : preformula (arity + 1)) (t : term σ) : preformula arity

abbrev formula := preformula σ 0

variable {σ}

notation "⊥'" => preformula.bot
infix:100 " =' " => preformula.eq
infixr:80 " →' " => preformula.implication
infixr:85 " ∨' " => preformula.disjunction
infixr:90 " ∧' " => preformula.conjunction
prefix:110 "∀'" => preformula.universal
prefix:110 "∃'" => preformula.existential

@[simp] def preformula.iffDef (left right : formula σ) : formula σ :=
  (left →' right) ∧' (right →' left)
infix:70 " ↔' " => preformula.iffDef

@[simp] def preformula.notDef (f : formula σ) : formula σ := f →' ⊥'
prefix:115 "¬'" => preformula.notDef

def preformula.top : formula σ := ¬'⊥'
notation "⊤'" => preformula.top

/- Compatibility names matching the Lean 3 constructor API. The implementation constructors use
descriptive names because several short names are parser keywords in Lean 4. -/
abbrev preformula.«imp» (left right : formula σ) : formula σ := implication left right
abbrev preformula.«and» (left right : formula σ) : formula σ := conjunction left right
abbrev preformula.«or» (left right : formula σ) : formula σ := disjunction left right
abbrev preformula.«all» (body : formula σ) : formula σ := universal body
abbrev preformula.ex (body : formula σ) : formula σ := existential body
abbrev preformula.«iff» (left right : formula σ) : formula σ := iffDef left right
abbrev preformula.«not» (f : formula σ) : formula σ := notDef f

export preformula (bot eq implication conjunction disjunction universal existential pred papp)

namespace formula

/-- Increase every free variable index at least `i` by `m`. -/
@[simp] def lift : {a : ℕ} → preformula σ a → ℕ → ℕ → preformula σ a
  | _, ⊥', _, _ => ⊥'
  | _, t =' s, m, i => term.lift t m i =' term.lift s m i
  | _, left →' right, m, i => lift left m i →' lift right m i
  | _, left ∧' right, m, i => lift left m i ∧' lift right m i
  | _, left ∨' right, m, i => lift left m i ∨' lift right m i
  | _, ∀'body, m, i => ∀'(lift body m (i + 1))
  | _, ∃'body, m, i => ∃'(lift body m (i + 1))
  | _, pred P, _, _ => pred P
  | _, papp body t, m, i => papp (lift body m i) (term.lift t m i)

/-- Substitute a term for a free variable in a formula. -/
@[simp, tls] def subst : {a : ℕ} → preformula σ a → term σ → ℕ → preformula σ a
  | _, ⊥', _, _ => ⊥'
  | _, t₁ =' t₂, s, k => term.subst t₁ s k =' term.subst t₂ s k
  | _, left →' right, s, k => subst left s k →' subst right s k
  | _, left ∧' right, s, k => subst left s k ∧' subst right s k
  | _, left ∨' right, s, k => subst left s k ∨' subst right s k
  | _, ∀'body, s, k => ∀'(subst body s (k + 1))
  | _, ∃'body, s, k => ∃'(subst body s (k + 1))
  | _, pred P, _, _ => pred P
  | _, papp body t, s, k => papp (subst body s k) (term.subst t s k)

end formula

notation:90 f:90 " ↑ " m:91 " ＠ " i:91 => formula.lift f m i
notation:100 f:max "[" t " ⁄ " n "]" => formula.subst f t n

namespace formula

@[simp, tls] lemma lift_by_0 {a} (f : preformula σ a) {i} : f ↑ 0 ＠ i = f := by
  induction f generalizing i with
  | bot => rfl
  | eq t s => simp [lift, term.lift_by_0]
  | implication left right ihl ihr => simp [lift, ihl, ihr]
  | conjunction left right ihl ihr => simp [lift, ihl, ihr]
  | disjunction left right ihl ihr => simp [lift, ihl, ihr]
  | universal body ih => simp [lift, ih]
  | existential body ih => simp [lift, ih]
  | pred P => rfl
  | papp body t ih => simp [lift, ih, term.lift_by_0]

lemma lift_lift {a} (f : preformula σ a) (m : ℕ) {i} (n : ℕ) {j} (H : j ≤ i) :
    (f ↑ m ＠ i) ↑ n ＠ j = (f ↑ n ＠ j) ↑ m ＠ (i + n) := by
  induction f generalizing i j with
  | bot => rfl
  | eq t s => simp [lift, term.lift_lift, H]
  | implication left right ihl ihr => simp [lift, ihl, ihr, H]
  | conjunction left right ihl ihr => simp [lift, ihl, ihr, H]
  | disjunction left right ihl ihr => simp [lift, ihl, ihr, H]
  | universal body ih =>
      simp only [lift]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1) (j := j + 1) (by omega)
  | existential body ih =>
      simp only [lift]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1) (j := j + 1) (by omega)
  | pred P => rfl
  | papp body t ih => simp [lift, ih, term.lift_lift, H]

lemma lift_lift_reverse {a} (f : preformula σ a) {m i} (n : ℕ) {j} (H : i + m ≤ j) :
    (f ↑ m ＠ i) ↑ n ＠ j = (f ↑ n ＠ (j - m)) ↑ m ＠ i := by
  have hij : i ≤ j - m := by omega
  have hmj : m ≤ j := by omega
  rw [lift_lift f n m hij, Nat.sub_add_cancel hmj]

lemma lift_lift_merge {a} (f : preformula σ a) {m i} (n : ℕ) {j} (H : i ≤ j)
    (H' : j ≤ i + m) : (f ↑ m ＠ i) ↑ n ＠ j = f ↑ (m + n) ＠ i := by
  induction f generalizing i j with
  | bot => rfl
  | eq t s => simp [lift, term.lift_lift_merge, H, H']
  | implication left right ihl ihr => simp [lift, ihl, ihr, H, H']
  | conjunction left right ihl ihr => simp [lift, ihl, ihr, H, H']
  | disjunction left right ihl ihr => simp [lift, ihl, ihr, H, H']
  | universal body ih =>
      simp only [lift]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1) (j := j + 1) (by omega) (by omega)
  | existential body ih =>
      simp only [lift]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1) (j := j + 1) (by omega) (by omega)
  | pred P => rfl
  | papp body t ih => simp [lift, ih, term.lift_lift_merge, H, H']

@[simp, tls] lemma lift_at_lift_merge {a} (f : preformula σ a) (m i n : ℕ) :
    (f ↑ m ＠ i) ↑ n ＠ i = f ↑ (m + n) ＠ i :=
  lift_lift_merge f n le_rfl (by omega)

lemma lambda_lift_lift {a} (m : ℕ) {i} (n : ℕ) {j} (H : j ≤ i) :
    (fun f : preformula σ a => (f ↑ m ＠ i) ↑ n ＠ j) =
      (fun f : preformula σ a => (f ↑ n ＠ j) ↑ m ＠ (i + n)) := by
  funext f
  exact lift_lift f m n H

lemma lift_subst {a} (f : preformula σ a) (s : term σ) (m i k : ℕ) (H : i ≤ k) :
    f[s ⁄ k] ↑ m ＠ i = (f ↑ m ＠ i)[s ⁄ (k + m)] := by
  induction f generalizing i k with
  | bot => rfl
  | eq t₁ t₂ => simp [lift, subst, term.lift_subst, H]
  | implication left right ihl ihr => simp [lift, subst, ihl, ihr, H]
  | conjunction left right ihl ihr => simp [lift, subst, ihl, ihr, H]
  | disjunction left right ihl ihr => simp [lift, subst, ihl, ihr, H]
  | universal body ih =>
      simp only [lift, subst]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1) (k := k + 1) (by omega)
  | existential body ih =>
      simp only [lift, subst]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1) (k := k + 1) (by omega)
  | pred P => rfl
  | papp body t ih => simp [lift, subst, ih, term.lift_subst, H]

lemma lambda_lift_subst_formula {a} {s : term σ} {m i k : ℕ} (H : i ≤ k) :
    (fun f : preformula σ a => lift (subst f s k) m i) =
      (fun f => subst (lift f m i) s (k + m)) := by
  funext f
  exact lift_subst f s m i k H

lemma subst_lift {a} (f : preformula σ a) (s : term σ) {m i k : ℕ} (H : i ≤ k)
    (H' : k ≤ i + m) : (f ↑ (m + 1) ＠ i)[s ⁄ k] = f ↑ m ＠ i := by
  induction f generalizing i k with
  | bot => rfl
  | eq t₁ t₂ => simp [lift, subst, term.subst_lift, H, H']
  | implication left right ihl ihr => simp [lift, subst, ihl, ihr, H, H']
  | conjunction left right ihl ihr => simp [lift, subst, ihl, ihr, H, H']
  | disjunction left right ihl ihr => simp [lift, subst, ihl, ihr, H, H']
  | universal body ih =>
      simp only [lift, subst]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1) (k := k + 1) (by omega) (by omega)
  | existential body ih =>
      simp only [lift, subst]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1) (k := k + 1) (by omega) (by omega)
  | pred P => rfl
  | papp body t ih => simp [lift, subst, ih, term.subst_lift, H, H']

lemma subst_lift_in_lift {a} (f : preformula σ a) (s : term σ) (m i k : ℕ) :
    (f ↑ m ＠ (i + k + 1))[(s ↑ m ＠ i) ⁄ k] = f[s ⁄ k] ↑ m ＠ (i + k) := by
  induction f generalizing i k with
  | bot => rfl
  | eq t₁ t₂ => simp [lift, subst, term.subst_lift_by_lift]
  | implication left right ihl ihr => simp [lift, subst, ihl, ihr]
  | conjunction left right ihl ihr => simp [lift, subst, ihl, ihr]
  | disjunction left right ihl ihr => simp [lift, subst, ihl, ihr]
  | universal body ih =>
      simp only [lift, subst]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i) (k := k + 1)
  | existential body ih =>
      simp only [lift, subst]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i) (k := k + 1)
  | pred P => rfl
  | papp body t ih => simp [lift, subst, ih, term.subst_lift_by_lift]

@[tls] lemma subst0_lift_by_lift {a} (f : preformula σ a) {s : term σ} {m i : ℕ} :
    (f ↑ m ＠ (i + 1))[(s ↑ m ＠ i) ⁄ 0] = f[s ⁄ 0] ↑ m ＠ i := by
  simpa using subst_lift_in_lift f s m i 0

@[tls] lemma subst_at_lift {a} (f : preformula σ a) (m : ℕ) (s : term σ) (k : ℕ) :
    (f ↑ (m + 1) ＠ k)[s ⁄ k] = f ↑ m ＠ k :=
  subst_lift f s le_rfl (by omega)

@[tls] lemma subst_var0_lift {a} (f : preformula σ a) (m i : ℕ) :
    (f ↑ (m + 1) ＠ (i + 1))[#0 ⁄ i] = f ↑ m ＠ (i + 1) := by
  induction f generalizing i with
  | bot => rfl
  | eq t₁ t₂ => simp [lift, subst, term.subst_var0_lift]
  | implication left right ihl ihr => simp [lift, subst, ihl, ihr]
  | conjunction left right ihl ihr => simp [lift, subst, ihl, ihr]
  | disjunction left right ihl ihr => simp [lift, subst, ihl, ihr]
  | universal body ih => simp [lift, subst, ih, Nat.add_assoc]
  | existential body ih => simp [lift, subst, ih, Nat.add_assoc]
  | pred P => rfl
  | papp body t ih => simp [lift, subst, ih, term.subst_var0_lift]

@[tls] lemma subst_var0_lift_by_1 {a} (f : preformula σ a) (i : ℕ) :
    (f ↑ 1 ＠ (i + 1))[#0 ⁄ i] = f := by
  simpa using subst_var0_lift f 0 i

@[tls] lemma subst_var0_for_0_lift_by_1 {a} (f : preformula σ a) :
    (f ↑ 1 ＠ 1)[#0 ⁄ 0] = f := by
  simpa using subst_var0_lift_by_1 f 0

@[simp, tls] lemma subst_for_0_lift_by_1 {a} (f : preformula σ a) (s : term σ) :
    (f ↑ 1 ＠ 0)[s ⁄ 0] = f := by
  induction f with
  | bot => rfl
  | eq t₁ t₂ => simp [lift, subst, term.subst_for_0_lift_by_1]
  | implication left right ihl ihr => simp [lift, subst, ihl, ihr]
  | conjunction left right ihl ihr => simp [lift, subst, ihl, ihr]
  | disjunction left right ihl ihr => simp [lift, subst, ihl, ihr]
  | universal body ih => simpa [lift, subst] using subst_at_lift body 0 s 1
  | existential body ih => simpa [lift, subst] using subst_at_lift body 0 s 1
  | pred P => rfl
  | papp body t ih => simp [lift, subst, ih, term.subst_for_0_lift_by_1]

lemma subst_subst {a} (f : preformula σ a) (s₁ : term σ) {k₁} (s₂ : term σ) {k₂}
    (H : k₁ ≤ k₂) : (f[s₁ ⁄ k₁])[s₂ ⁄ k₂] =
      (f[s₂ ⁄ (k₂ + 1)])[(s₁[s₂ ⁄ (k₂ - k₁)]) ⁄ k₁] := by
  induction f generalizing k₁ k₂ with
  | bot => rfl
  | eq t₁ t₂ => simp [subst, term.subst_subst, H]
  | implication left right ihl ihr => simp [subst, ihl, ihr, H]
  | conjunction left right ihl ihr => simp [subst, ihl, ihr, H]
  | disjunction left right ihl ihr => simp [subst, ihl, ihr, H]
  | universal body ih =>
      simp only [subst]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (k₁ := k₁ + 1) (k₂ := k₂ + 1) (by omega)
  | existential body ih =>
      simp only [subst]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (k₁ := k₁ + 1) (k₂ := k₂ + 1) (by omega)
  | pred P => rfl
  | papp body t ih => simp [subst, ih, term.subst_subst, H]

lemma lift_fixed_points_monotone {a} {f : preformula σ a} {i j : ℕ}
    (H : f ↑ 1 ＠ i = f) (h : i ≤ j) : f ↑ 1 ＠ j = f := by
  induction j with
  | zero => simpa [Nat.eq_zero_of_le_zero h] using H
  | succ j ih =>
      by_cases hij : i = j + 1
      · simpa [hij] using H
      · have hij' : i ≤ j := by omega
        rw [← H, ← lift_lift f 1 1 hij', ih hij']

/-- Bind the first `k` free variables with universal quantifiers. -/
def alls : ℕ → formula σ → formula σ
  | 0, f => f
  | k + 1, f => ∀'(alls k f)

lemma all_alls (f : formula σ) : ∀ k : ℕ, ∀'(alls k f) = alls k (∀'f)
  | 0 => rfl
  | k + 1 => by simp only [alls]; rw [all_alls f k]

lemma alls_succ (k : ℕ) (f : formula σ) : alls (k + 1) f = alls k (∀'f) := by
  rw [alls, all_alls]

lemma alls_alls (f : formula σ) : ∀ m n : ℕ, alls n (alls m f) = alls m (alls n f)
  | 0, _ => rfl
  | m + 1, n => by
      calc
        alls n (alls (m + 1) f) = alls n (∀'(alls m f)) := rfl
        _ = ∀'(alls n (alls m f)) := (all_alls (alls m f) n).symm
        _ = ∀'(alls m (alls n f)) := congrArg universal (alls_alls f m n)
        _ = alls (m + 1) (alls n f) := rfl

lemma alls_lift (f : formula σ) (m i : ℕ) : ∀ n : ℕ,
    alls n (f ↑ m ＠ (i + n)) = (alls n f) ↑ m ＠ i
  | 0 => rfl
  | n + 1 => by
      simp only [alls, lift]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using alls_lift f m (i + 1) n

lemma alls_at_lift (f : formula σ) (m n : ℕ) :
    alls n (f ↑ m ＠ n) = (alls n f) ↑ m ＠ 0 := by
  simpa using alls_lift f m 0 n

/-- Simultaneously instantiate a block of variables. -/
def substs : ℕ → ℕ → ℕ → formula σ → formula σ
  | 0, _, _, f => f
  | k + 1, i, j, f => substs k i j (f[#(k + i) ⁄ (k + j)])

lemma substs_succ (k i j : ℕ) (f : formula σ) :
    substs (k + 1) i j f = (substs k (i + 1) (j + 1) f)[#i ⁄ j] := by
  induction k generalizing f with
  | zero => simp [substs]
  | succ k ih =>
      simpa [substs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (f := f[#(k + 1 + i) ⁄ (k + 1 + j)])

lemma all_substs {k i j : ℕ} {f : formula σ} :
    ∀'(substs k i (j + 1) f) = substs k i j (∀'f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => simp [substs, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A formula is `k`-closed when lifting at `k` leaves it unchanged. -/
@[simp] def closed {a} (k : ℕ) (f : preformula σ a) : Prop := f ↑ 1 ＠ k = f

/-- A sentence is a formula with no free variables. -/
@[simp] def sentence (f : formula σ) : Prop := closed 0 f

postfix:max " is_sentence" => sentence

lemma closed_all {f : formula σ} {k} (H : closed (k + 1) f) : closed k (∀'f) := by
  exact congrArg universal H

lemma closed_ex {f : formula σ} {k} (H : closed (k + 1) f) : closed k (∃'f) := by
  exact congrArg existential H

lemma lift_closed_id_h {f : formula σ} {k} (H : closed k f) (m i : ℕ) :
    f ↑ m ＠ (k + i) = f := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
      rw [← lift_lift_merge f (m := m) (i := k + i) 1 (j := k + i) le_rfl (by omega),
        ih H]
      exact lift_fixed_points_monotone H (by omega)

lemma lift_closed_id {f : formula σ} {k} (H : closed k f) (m : ℕ) {l} (h : k ≤ l) :
    f ↑ m ＠ l = f := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
  exact lift_closed_id_h H m i

lemma lift_sentence_id {f : formula σ} (H : sentence f) {m i} : f ↑ m ＠ i = f :=
  lift_closed_id H m (Nat.zero_le i)

lemma lift_set_of_sentences_id {Γ : Set (formula σ)} (H : ∀ f ∈ Γ, sentence f) {m i} :
    (fun f : formula σ => f ↑ m ＠ i) '' Γ = Γ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [lift_sentence_id (H y hy)] using hy
  · intro hx
    exact ⟨x, hx, lift_sentence_id (H x hx)⟩

lemma subst_closed_id_h {f : formula σ} (t : term σ) {k} (i : ℕ) (H : closed k f) :
    f[t ⁄ (k + i)] = f := by
  have h := subst_at_lift f 0 t (k + i)
  simpa [lift_closed_id_h H] using h

lemma subst_closed_id {f : formula σ} {i} (H : closed i f) (t : term σ) {k} (h : i ≤ k) :
    f[t ⁄ k] = f := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  exact subst_closed_id_h t j H

lemma subst_sentence_id {f : formula σ} (H : sentence f) {t : term σ} {k : ℕ} :
    f[t ⁄ k] = f := subst_closed_id H t (Nat.zero_le k)

lemma subst_set_of_sentences_id {Γ : Set (formula σ)} {t k}
    (H : ∀ f ∈ Γ, sentence f) : (fun f : formula σ => f[t ⁄ k]) '' Γ = Γ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [subst_sentence_id (H y hy)] using hy
  · intro hx
    exact ⟨x, hx, subst_sentence_id (H x hx)⟩

/-- The largest free-variable depth occurring in a formula. -/
def max_free_var : {a : ℕ} → preformula σ a → ℕ
  | _, ⊥' => 0
  | _, t₁ =' t₂ => max (term.max_free_var t₁) (term.max_free_var t₂)
  | _, ∀'body => max_free_var body - 1
  | _, ∃'body => max_free_var body - 1
  | _, left →' right => max (max_free_var left) (max_free_var right)
  | _, left ∧' right => max (max_free_var left) (max_free_var right)
  | _, left ∨' right => max (max_free_var left) (max_free_var right)
  | _, pred _ => 0
  | _, papp body t => max (max_free_var body) (term.max_free_var t)

lemma closed_max_free_var {a} (f : preformula σ a) : closed (max_free_var f) f := by
  induction f with
  | bot => rfl
  | eq t s =>
      exact congrArg₂ eq
        (term.lift_fixed_points_monotone (le_max_left _ _) (term.lift_at_max_free_var t))
        (term.lift_fixed_points_monotone (le_max_right _ _) (term.lift_at_max_free_var s))
  | implication left right ihl ihr =>
      exact congrArg₂ implication
        (lift_fixed_points_monotone ihl (le_max_left _ _))
        (lift_fixed_points_monotone ihr (le_max_right _ _))
  | conjunction left right ihl ihr =>
      exact congrArg₂ conjunction
        (lift_fixed_points_monotone ihl (le_max_left _ _))
        (lift_fixed_points_monotone ihr (le_max_right _ _))
  | disjunction left right ihl ihr =>
      exact congrArg₂ disjunction
        (lift_fixed_points_monotone ihl (le_max_left _ _))
        (lift_fixed_points_monotone ihr (le_max_right _ _))
  | universal body ih =>
      apply congrArg universal
      change body ↑ 1 ＠ (max_free_var body - 1 + 1) = body
      exact lift_fixed_points_monotone ih (by omega)
  | existential body ih =>
      apply congrArg existential
      change body ↑ 1 ＠ (max_free_var body - 1 + 1) = body
      exact lift_fixed_points_monotone ih (by omega)
  | pred P => rfl
  | papp body t ih =>
      exact congrArg₂ papp
        (lift_fixed_points_monotone ih (le_max_left _ _))
        (term.lift_fixed_points_monotone (le_max_right _ _) (term.lift_at_max_free_var t))

/-- Universal closure of a `k`-closed formula. -/
abbrev closure (f : formula σ) {k} (_H : closed k f) := alls k f

lemma closure_is_sentence {f : formula σ} {k} (H : closed k f) :
    (closure f H) is_sentence := by
  induction k generalizing f with
  | zero => exact H
  | succ k ih =>
      simpa [closure, alls_succ] using ih (f := ∀'f) (closed_all H)

def not_free (k : ℕ) (f : formula σ) : Prop := ∃ g : formula σ, f = g ↑ 1 ＠ k

lemma not_free_trival_witness (k : ℕ) (f : formula σ) (h : not_free k f) :
    f = (f[#0 ⁄ k]) ↑ 1 ＠ k := by
  rcases h with ⟨g, rfl⟩
  simp [subst_at_lift]

end formula

end formulas

export formula (lift_by_0 lift_lift lift_lift_reverse lift_lift_merge lift_at_lift_merge
  lambda_lift_lift lift_subst lambda_lift_subst_formula subst_lift subst_lift_in_lift
  subst0_lift_by_lift subst_at_lift subst_var0_lift subst_var0_lift_by_1
  subst_var0_for_0_lift_by_1 subst_for_0_lift_by_1 subst_subst lift_fixed_points_monotone
  alls all_alls alls_succ alls_alls alls_lift alls_at_lift substs substs_succ all_substs closed
  sentence closed_all closed_ex lift_closed_id_h lift_closed_id lift_sentence_id
  lift_set_of_sentences_id subst_closed_id_h subst_closed_id subst_sentence_id
  subst_set_of_sentences_id max_free_var closed_max_free_var closure closure_is_sentence not_free
  not_free_trival_witness)

/-! ### Proof terms of intuitionistic natural deduction -/

section proof_terms

local infixr:70 " >> " => Set.insert

/-- Intuitionistic natural-deduction proofs for first-order logic with equality. -/
inductive proof_term : Set (formula σ) → formula σ → Type u where
  | hypI {Γ f} (h : f ∈ Γ) : proof_term Γ f
  | botE {Γ f} (H : proof_term Γ ⊥') : proof_term Γ f
  | impI {Γ f g} (H : proof_term (f >> Γ) g) : proof_term Γ (f →' g)
  | impE {Γ} (f) {g} (H₁ : proof_term Γ f) (H₂ : proof_term Γ (f →' g)) : proof_term Γ g
  | andI {Γ f g} (H₁ : proof_term Γ f) (H₂ : proof_term Γ g) : proof_term Γ (f ∧' g)
  | andE₁ {Γ f} (g) (H : proof_term Γ (f ∧' g)) : proof_term Γ f
  | andE₂ {Γ} (f) {g} (H : proof_term Γ (f ∧' g)) : proof_term Γ g
  | orI₁ {Γ f g} (H : proof_term Γ f) : proof_term Γ (f ∨' g)
  | orI₂ {Γ f g} (H : proof_term Γ g) : proof_term Γ (f ∨' g)
  | orE {Γ} (f g) {h} (H : proof_term Γ (f ∨' g))
      (H₁ : proof_term (f >> Γ) h) (H₂ : proof_term (g >> Γ) h) : proof_term Γ h
  | allI {Γ f} (H : proof_term ((fun g : formula σ => g ↑ 1 ＠ 0) '' Γ) f) :
      proof_term Γ (∀'f)
  | allE {Γ} (f) {t} (H : proof_term Γ (∀'f)) : proof_term Γ (f[t ⁄ 0])
  | exI {Γ f} (t) (H : proof_term Γ (f[t ⁄ 0])) : proof_term Γ (∃'f)
  | exE {Γ g} (f) (H₁ : proof_term Γ (∃'f))
      (H₂ : proof_term (f >> (fun h : formula σ => h ↑ 1 ＠ 0) '' Γ) (g ↑ 1 ＠ 0)) :
      proof_term Γ g
  | eqI {Γ} (t) : proof_term Γ (t =' t)
  | eqE {Γ} {s t f} (H₁ : proof_term Γ (s =' t)) (H₂ : proof_term Γ (f[s ⁄ 0])) :
      proof_term Γ (f[t ⁄ 0])

infix:55 " ⊢ " => proof_term

/-- The proposition that a proof term exists. -/
def provable (f : formula σ) (Γ : Set (formula σ)) : Prop := Nonempty (Γ ⊢ f)

infix:100 " is_provable_within " => provable

/-- Closed instances of excluded middle, used when reasoning classically. -/
def lem : Set (formula σ) := {f | ∃ g : formula σ, sentence g ∧ f = (g ∨' ¬'g)}

namespace proof_term

private def castContext {Γ Δ : Set (formula σ)} {f : formula σ} (h : Γ = Δ)
    (H : Γ ⊢ f) : Δ ⊢ f := h ▸ H

private def castFormula {Γ : Set (formula σ)} {f g : formula σ} (h : f = g)
    (H : Γ ⊢ f) : Γ ⊢ g := h ▸ H

/-- Weaken a proof into a larger context. -/
def weak {Δ f} (Γ : Set (formula σ)) (H : Γ ⊢ f) (h : Γ ⊆ Δ) : Δ ⊢ f :=
  match H with
  | .hypI hmem => hypI (h hmem)
  | .botE H => botE (weak _ H h)
  | .impI H => impI (weak _ H (Set.insert_subset_insert h))
  | .impE f H₁ H₂ => impE f (weak _ H₁ h) (weak _ H₂ h)
  | .andI H₁ H₂ => andI (weak _ H₁ h) (weak _ H₂ h)
  | .andE₁ g H => andE₁ g (weak _ H h)
  | .andE₂ f H => andE₂ f (weak _ H h)
  | .orI₁ H => orI₁ (weak _ H h)
  | .orI₂ H => orI₂ (weak _ H h)
  | .orE f g H H₁ H₂ =>
      orE f g (weak _ H h) (weak _ H₁ (Set.insert_subset_insert h))
        (weak _ H₂ (Set.insert_subset_insert h))
  | .allI H => allI (weak _ H (Set.image_mono h))
  | .allE f H => allE f (weak _ H h)
  | .exI t H => exI t (weak _ H h)
  | .exE f H₁ H₂ =>
      exE f (weak _ H₁ h) (weak _ H₂ (Set.insert_subset_insert (Set.image_mono h)))
  | .eqI t => eqI t
  | .eqE H₁ H₂ => eqE (weak _ H₁ h) (weak _ H₂ h)

/-- Weaken by inserting one premise. -/
def weak1 {Γ} {f g : formula σ} (H : Γ ⊢ g) : (f >> Γ) ⊢ g :=
  weak Γ H (Set.subset_insert f Γ)

/-- Weaken a proof from a singleton context into any context containing that premise. -/
def weak_singleton {Γ} (f) {g : formula σ} (H : ({f} : Set (formula σ)) ⊢ g)
    (h : f ∈ Γ) : Γ ⊢ g :=
  weak {f} H (Set.singleton_subset_iff.mpr h)

def hypI1 {Γ} (f : formula σ) : (f >> Γ) ⊢ f := hypI (Set.mem_insert f Γ)

def hypI2 {Γ} (f g : formula σ) : f >> (g >> Γ) ⊢ g :=
  hypI (Set.mem_insert_of_mem f (Set.mem_insert g Γ))

/-- Introduction of truth. -/
def topI {Γ : Set (formula σ)} : Γ ⊢ ⊤' := impI (hypI1 ⊥')

def impE_insert {Γ} {f g : formula σ} (H : Γ ⊢ (f →' g)) : (f >> Γ) ⊢ g :=
  impE f (hypI1 f) (weak1 H)

def impI_refl {Γ} (f : formula σ) : Γ ⊢ (f →' f) := impI (hypI1 f)

def impI_trans {Γ} (f g h : formula σ) (H₁ : Γ ⊢ (f →' g)) (H₂ : Γ ⊢ (g →' h)) :
    Γ ⊢ (f →' h) := impI (impE g (impE_insert H₁) (weak1 H₂))

/-- Universal elimination with a named result formula. -/
def allE' {Γ} (f) (t : term σ) {g} (H : Γ ⊢ (∀'f)) (h : g = f[t ⁄ 0]) : Γ ⊢ g := by
  subst g
  exact allE f H

def allE_var0 {Γ} {f : formula σ} (H : Γ ⊢ ((∀'f) ↑ 1 ＠ 0)) : Γ ⊢ f := by
  apply allE' (f ↑ 1 ＠ 1) #0 H
  symm
  exact subst_var0_lift_by_1 f 0

/-- Equality elimination with a named result formula. -/
def eqE' {Γ} {g} (s t : term σ) (f : formula σ) (H₁ : Γ ⊢ (s =' t))
    (H₂ : Γ ⊢ f[s ⁄ 0]) (h : g = f[t ⁄ 0]) : Γ ⊢ g := by
  subst g
  exact eqE H₁ H₂

/-- Congruence of term substitution. -/
def congrI {Γ} {t s₁ s₂ : term σ} (H : Γ ⊢ (s₁ =' s₂)) :
    Γ ⊢ ((t[s₁ ⁄ 0]) =' (t[s₂ ⁄ 0])) := by
  apply eqE' s₁ s₂ ((term.lift (term.subst t s₁ 0) 1 0) =' t) H
  · simpa [formula.subst, term.subst_for_0_lift_by_1] using
      (eqI (Γ := Γ) (term.subst t s₁ 0))
  · simp [formula.subst, term.subst_for_0_lift_by_1]

def congrI' {Γ} {t₁ s₁ t₂ s₂ : term σ} (t : term σ) (H : Γ ⊢ (s₁ =' s₂))
    (h₁ : t₁ = t[s₁ ⁄ 0]) (h₂ : t₂ = t[s₂ ⁄ 0]) : Γ ⊢ (t₁ =' t₂) := by
  subst t₁
  subst t₂
  exact congrI H

def eqI_refl {Γ} (t : term σ) : Γ ⊢ (t =' t) := eqI t

def eqI_symm {Γ} (s t : term σ) (H : Γ ⊢ (s =' t)) : Γ ⊢ (t =' s) := by
  apply eqE' s t (#0 =' term.lift s 1 0) H
  · simpa [formula.subst, term.subst_for_0_lift_by_1] using (eqI (Γ := Γ) s)
  · simp [formula.subst, term.subst_for_0_lift_by_1]

def eqI_trans {Γ} (s t u : term σ) (H₁ : Γ ⊢ (s =' t)) (H₂ : Γ ⊢ (t =' u)) :
    Γ ⊢ (s =' u) := by
  apply eqE' t u (term.lift s 1 0 =' #0) H₂
  · simpa [formula.subst, term.subst_for_0_lift_by_1] using H₁
  · simp [formula.subst, term.subst_for_0_lift_by_1]

def iffI {Γ} {f g : formula σ} (H₁ : Γ ⊢ (f →' g)) (H₂ : Γ ⊢ (g →' f)) :
    Γ ⊢ (f ↔' g) := andI H₁ H₂

def iffE_r {Γ} {f g : formula σ} (H : Γ ⊢ (f ↔' g)) : Γ ⊢ (f →' g) := andE₁ _ H

def iffE_l {Γ} {f g : formula σ} (H : Γ ⊢ (f ↔' g)) : Γ ⊢ (g →' f) := andE₂ _ H

def iffE₁ {Γ} {f : formula σ} (g : formula σ) (H₁ : Γ ⊢ g) (H₂ : Γ ⊢ (f ↔' g)) :
    Γ ⊢ f := impE g H₁ (andE₂ _ H₂)

def iffE₂ {Γ} (f) {g : formula σ} (H₁ : Γ ⊢ f) (H₂ : Γ ⊢ (f ↔' g)) :
    Γ ⊢ g := impE f H₁ (andE₁ _ H₂)

def iffI_refl {Γ} (f : formula σ) : Γ ⊢ (f ↔' f) := iffI (impI_refl f) (impI_refl f)

def iffI_trans {Γ} {f} (g : formula σ) {h} (H₁ : Γ ⊢ (f ↔' g))
    (H₂ : Γ ⊢ (g ↔' h)) : Γ ⊢ (f ↔' h) :=
  iffI (impI_trans f g h (andE₁ _ H₁) (andE₁ _ H₂))
    (impI_trans h g f (andE₂ _ H₂) (andE₂ _ H₁))

def iffI_symm {Γ} {f g : formula σ} (H : Γ ⊢ (f ↔' g)) : Γ ⊢ (g ↔' f) :=
  iffI (andE₂ _ H) (andE₁ _ H)

/-- Substitute a term for a free variable throughout a proof. -/
def substI {Γ} {f : formula σ} (t : term σ) (k : ℕ) (H : Γ ⊢ f) :
    (fun g : formula σ => g[t ⁄ k]) '' Γ ⊢ f[t ⁄ k] :=
  match H with
  | .hypI hmem => hypI ⟨_, hmem, rfl⟩
  | .botE H => botE (substI t k H)
  | .impI H => impI (castContext Set.image_insert_eq (substI t k H))
  | .impE f H₁ H₂ => impE (f[t ⁄ k]) (substI t k H₁) (substI t k H₂)
  | .andI H₁ H₂ => andI (substI t k H₁) (substI t k H₂)
  | .andE₁ g H => andE₁ (g[t ⁄ k]) (substI t k H)
  | .andE₂ f H => andE₂ (f[t ⁄ k]) (substI t k H)
  | .orI₁ H => orI₁ (substI t k H)
  | .orI₂ H => orI₂ (substI t k H)
  | .orE f g H H₁ H₂ => by
      apply orE (f[t ⁄ k]) (g[t ⁄ k]) (substI t k H)
      · exact castContext Set.image_insert_eq (substI t k H₁)
      · exact castContext Set.image_insert_eq (substI t k H₂)
  | .allI H => by
      apply allI
      simpa only [Set.image_image,
        lambda_lift_subst_formula (s := t) (m := 1) (i := 0) (k := k) (Nat.zero_le k)]
        using substI t (k + 1) H
  | .allE f H => by
      apply allE' (f[t ⁄ (k + 1)]) (term.subst _ t k) (substI t k H)
      simpa using subst_subst f _ t (Nat.zero_le k)
  | @proof_term.exI _ _ body s H => by
      apply exI (term.subst s t k)
      have hs := subst_subst body s t (Nat.zero_le k)
      simp only [Nat.sub_zero] at hs
      rw [← hs]
      exact substI t k H
  | .exE f H₁ H₂ => by
      apply exE (f[t ⁄ (k + 1)]) (substI t k H₁)
      have h := substI t (k + 1) H₂
      have htail :
          (fun a : formula σ => a[t ⁄ (k + 1)]) ''
              (fun a : formula σ => a ↑ 1 ＠ 0) '' Γ =
            (fun a : formula σ => a ↑ 1 ＠ 0) ''
              (fun a : formula σ => a[t ⁄ k]) '' Γ := by
        calc
          _ = ((fun a : formula σ => a[t ⁄ (k + 1)]) ∘
                (fun a : formula σ => a ↑ 1 ＠ 0)) '' Γ :=
              Set.image_image (fun a : formula σ => a[t ⁄ (k + 1)])
                (fun a : formula σ => a ↑ 1 ＠ 0) Γ
          _ = ((fun a : formula σ => a ↑ 1 ＠ 0) ∘
                (fun a : formula σ => a[t ⁄ k])) '' Γ := by
                  apply congrArg (fun q : formula σ → formula σ => q '' Γ)
                  funext a
                  exact (lift_subst a t 1 0 k (Nat.zero_le k)).symm
          _ = _ := (Set.image_image (fun a : formula σ => a ↑ 1 ＠ 0)
            (fun a : formula σ => a[t ⁄ k]) Γ).symm
      have hctx :
          (fun a : formula σ => a[t ⁄ (k + 1)]) ''
              (f >> (fun a : formula σ => a ↑ 1 ＠ 0) '' Γ) =
            (f[t ⁄ (k + 1)] >>
              (fun a : formula σ => a ↑ 1 ＠ 0) '' (fun a : formula σ => a[t ⁄ k]) '' Γ) := by
        calc
          _ = f[t ⁄ (k + 1)] >>
              (fun a : formula σ => a[t ⁄ (k + 1)]) ''
                (fun a : formula σ => a ↑ 1 ＠ 0) '' Γ := Set.image_insert_eq
          _ = _ := congrArg (Set.insert (f[t ⁄ (k + 1)])) htail
      have h := castContext hctx h
      rw [lift_subst _ t 1 0 k (Nat.zero_le k)]
      exact h
  | .eqI s => eqI (term.subst s t k)
  | .eqE H₁ H₂ => by
      apply eqE' _ _ _ (substI t k H₁)
      · have h := substI t k H₂
        rw [subst_subst _ _ t (Nat.zero_le k), Nat.sub_zero] at h
        exact h
      · exact subst_subst _ _ t (Nat.zero_le k)

private lemma liftImageCommutes (Γ : Set (formula σ)) (m i : ℕ) :
    (fun a : formula σ => a ↑ m ＠ (i + 1)) ''
        (fun a : formula σ => a ↑ 1 ＠ 0) '' Γ =
      (fun a : formula σ => a ↑ 1 ＠ 0) ''
        (fun a : formula σ => a ↑ m ＠ i) '' Γ := by
  calc
    _ = ((fun a : formula σ => a ↑ m ＠ (i + 1)) ∘
          (fun a : formula σ => a ↑ 1 ＠ 0)) '' Γ :=
        Set.image_image (fun a : formula σ => a ↑ m ＠ (i + 1))
          (fun a : formula σ => a ↑ 1 ＠ 0) Γ
    _ = ((fun a : formula σ => a ↑ 1 ＠ 0) ∘
          (fun a : formula σ => a ↑ m ＠ i)) '' Γ := by
        apply congrArg (fun q : formula σ → formula σ => q '' Γ)
        funext a
        exact (lift_lift a m 1 (Nat.zero_le i)).symm
    _ = _ := (Set.image_image (fun a : formula σ => a ↑ 1 ＠ 0)
      (fun a : formula σ => a ↑ m ＠ i) Γ).symm

/-- Introduce fresh variables throughout a proof. -/
def liftI {Γ} {f : formula σ} (m i : ℕ) (H : Γ ⊢ f) :
    (fun g : formula σ => g ↑ m ＠ i) '' Γ ⊢ f ↑ m ＠ i :=
  match H with
  | .hypI hmem => hypI ⟨_, hmem, rfl⟩
  | .botE H => botE (liftI m i H)
  | .impI H => impI (castContext Set.image_insert_eq (liftI m i H))
  | .impE f H₁ H₂ => impE (f ↑ m ＠ i) (liftI m i H₁) (liftI m i H₂)
  | .andI H₁ H₂ => andI (liftI m i H₁) (liftI m i H₂)
  | .andE₁ g H => andE₁ (g ↑ m ＠ i) (liftI m i H)
  | .andE₂ f H => andE₂ (f ↑ m ＠ i) (liftI m i H)
  | .orI₁ H => orI₁ (liftI m i H)
  | .orI₂ H => orI₂ (liftI m i H)
  | .orE f g H H₁ H₂ => by
      apply orE (f ↑ m ＠ i) (g ↑ m ＠ i) (liftI m i H)
      · exact castContext Set.image_insert_eq (liftI m i H₁)
      · exact castContext Set.image_insert_eq (liftI m i H₂)
  | @proof_term.allI _ Γ₀ _ H => by
      apply allI
      exact castContext (liftImageCommutes Γ₀ m i) (liftI m (i + 1) H)
  | .allE f H => by
      apply allE' (f ↑ m ＠ (i + 1)) (term.lift _ m i) (liftI m i H)
      exact (subst_lift_in_lift f _ m i 0).symm
  | .exI t H => by
      apply exI (term.lift t m i)
      rw [subst0_lift_by_lift]
      exact liftI m i H
  | @proof_term.exE _ Γ₀ result f H₁ H₂ => by
      apply exE (f ↑ m ＠ (i + 1)) (liftI m i H₁)
      have h := liftI m (i + 1) H₂
      have himage :
          (fun a : formula σ => a ↑ m ＠ (i + 1)) ''
              (f >> (fun a : formula σ => a ↑ 1 ＠ 0) '' Γ₀) =
            (f ↑ m ＠ (i + 1) >>
              (fun a : formula σ => a ↑ m ＠ (i + 1)) ''
                (fun a : formula σ => a ↑ 1 ＠ 0) '' Γ₀) := Set.image_insert_eq
      have h := castContext himage h
      have hctx := congrArg (Set.insert (f ↑ m ＠ (i + 1))) (liftImageCommutes Γ₀ m i)
      have h := castContext hctx h
      exact castFormula (lift_lift result m 1 (Nat.zero_le i)).symm h
  | .eqI t => eqI (term.lift t m i)
  | .eqE H₁ H₂ => by
      apply eqE' _ _ _ (liftI m i H₁)
      · rw [subst0_lift_by_lift]
        exact liftI m i H₂
      · exact (subst0_lift_by_lift _).symm

/-- Remove a fresh variable introduced at index `0`. -/
def liftE_h {Γ} {f : formula σ} (_m _i : ℕ)
    (H : (fun g : formula σ => g ↑ 1 ＠ 0) '' Γ ⊢ f ↑ 1 ＠ 0) : Γ ⊢ f := by
  have h := allE (f ↑ 1 ＠ 0) (t := #0) (allI H)
  simpa using h

private lemma liftImageMerge (Γ : Set (formula σ)) (m n : ℕ) :
    (fun a : formula σ => a ↑ n ＠ 0) '' (fun a : formula σ => a ↑ m ＠ 0) '' Γ =
      (fun a : formula σ => a ↑ (m + n) ＠ 0) '' Γ := by
  calc
    _ = ((fun a : formula σ => a ↑ n ＠ 0) ∘
          (fun a : formula σ => a ↑ m ＠ 0)) '' Γ :=
        Set.image_image (fun a : formula σ => a ↑ n ＠ 0)
          (fun a : formula σ => a ↑ m ＠ 0) Γ
    _ = (fun a : formula σ => a ↑ (m + n) ＠ 0) '' Γ := by
        apply congrArg (fun q : formula σ → formula σ => q '' Γ)
        funext a
        exact lift_at_lift_merge a m 0 n

/-- Bind the first `n` fresh variables in a proof. -/
def allsI {Γ} {f : formula σ} (n : ℕ)
    (H : (fun g : formula σ => g ↑ n ＠ 0) '' Γ ⊢ f) : Γ ⊢ alls n f := by
  induction n generalizing f Γ with
  | zero => simpa [alls] using H
  | succ n ih =>
      apply allI
      apply ih
      have hmerge := liftImageMerge Γ 1 n
      have hmerge :
          (fun a : formula σ => a ↑ n ＠ 0) ''
              (fun a : formula σ => a ↑ 1 ＠ 0) '' Γ =
            (fun a : formula σ => a ↑ (n + 1) ＠ 0) '' Γ := by
        simpa [Nat.add_comm] using hmerge
      exact castContext hmerge.symm H

/-- Instantiate the `n` leading universal quantifiers. -/
def allsE {Γ} {f : formula σ} (n i : ℕ) (H : Γ ⊢ alls n f) : Γ ⊢ substs n i 0 f := by
  induction n generalizing f i with
  | zero => exact H
  | succ n ih =>
      rw [substs_succ]
      apply allE (substs n (i + 1) 1 f)
      have Hn : Γ ⊢ alls n (∀'f) := by simpa [alls_succ] using H
      have h := ih (i := i + 1) Hn
      rw [← all_substs] at h
      exact h

/-- Remove the `n` leading universal quantifiers while lifting the context. -/
def allsE' {Γ} (n : ℕ) {f : formula σ} (H : Γ ⊢ alls n f) :
    (fun g : formula σ => g ↑ n ＠ 0) '' Γ ⊢ f := by
  induction n generalizing f Γ with
  | zero => simpa [alls] using H
  | succ n ih =>
      have Hn : Γ ⊢ alls n (∀'f) := by simpa [alls_succ] using H
      have h := ih Hn
      have hl := liftI 1 0 h
      have hmerge := liftImageMerge Γ n 1
      apply allE_var0
      exact castContext hmerge hl

end proof_term

export proof_term (hypI botE impI impE andI andE₁ andE₂ orI₁ orI₂ orE allI allE exI exE eqI eqE
  weak weak1 weak_singleton hypI1 hypI2 topI impE_insert impI_refl impI_trans
  allE' allE_var0 eqE' congrI congrI' eqI_refl eqI_symm eqI_trans iffI iffE_r iffE_l iffE₁
  iffE₂ iffI_refl iffI_trans iffI_symm substI liftI liftE_h allsI allsE allsE')

/-- Formal proof that the domain of discourse is inhabited. -/
def let_there_be_light : (∅ : Set (formula σ)) ⊢ ∃'(#0 =' #0) :=
  exI (#0 : term σ) (eqI (#0 : term σ))

private def syllogism {Γ : Set (formula σ)} {f g h : formula σ}
    (H₁ : Γ ⊢ ∀'(f →' g)) (H₂ : Γ ⊢ ∀'(g →' h)) : Γ ⊢ ∀'(f →' h) := by
  apply allI
  apply impI
  apply impE g
  · apply impE_insert
    apply allE' ((f →' g) ↑ 1 ＠ 1) #0 (liftI 1 0 H₁)
    exact (subst_var0_lift_by_1 (f →' g) 0).symm
  · apply weak1
    apply allE' ((g →' h) ↑ 1 ＠ 1) #0 (liftI 1 0 H₂)
    exact (subst_var0_lift_by_1 (g →' h) 0).symm

example {Γ : Set (formula σ)} {f g h : formula σ}
    (H₁ : Γ ⊢ ∀'(f →' g)) (H₂ : Γ ⊢ ∀'(g →' h)) : Γ ⊢ ∀'(f →' h) :=
  syllogism H₁ H₂

example {Γ : Set (formula σ)} {f g h : formula σ}
    (H₁ : Γ ⊢ ∀'(f →' g)) (H₂ : Γ ⊢ ∀'(g →' h)) : Γ ⊢ ∀'(f →' h) :=
  syllogism H₁ H₂

end proof_terms

end fol
