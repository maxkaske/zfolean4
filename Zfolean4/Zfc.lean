import Zfolean4.Fol

set_option linter.style.header false
set_option linter.style.multiGoal false
set_option linter.style.whitespace false

/-!
# ZFC set theory

This file defines the signature and axioms of Zermelo–Fraenkel set theory with choice and
formalizes, in the natural-deduction calculus from `Zfolean4.Fol`, that `ω` is the smallest
inductive set.

## Main results

- `omega_smallest_inductive_provable`:
    we show that ZFC proves that ω is the smallest inductive set. a direct consequence of
- `omega_smallest_inductive`:
    a natural deduction proof that ω is the smallest inductive set

## References

* [K. Kunen, *Set Theory*] [KUN83]
  -- for their axiomatization of ZF
* [H.D. Ebbinghaus, *Einführung in die Mengenlehre*] [EBB03]
  -- for their formalization of axiom of choice

-/

universe u

namespace zfc

open fol

local infixr:70 " >> " => Set.insert

section zfc_language

/-- ZFC has one binary predicate symbol, membership. -/
inductive pred_symb : ℕ → Type u where
  | elem : pred_symb 2

/-- ZFC has no function symbols. -/
inductive func_symb : ℕ → Type u

/-- The first-order signature of ZFC. -/
def σ : signature where
  func_symb := zfc.func_symb
  pred_symb := zfc.pred_symb

/-- The membership predicate. -/
def memb (t₁ t₂ : term σ) : formula σ := papp (papp (pred pred_symb.elem) t₁) t₂

infix:100 " ∈' " => memb

@[simp, tls] lemma lift_memb (t₁ t₂ : term σ) (m i : ℕ) :
    (t₁ ∈' t₂) ↑ m ＠ i = (t₁ ↑ m ＠ i) ∈' (t₂ ↑ m ＠ i) := rfl

@[simp, tls] lemma subst_memb (t₁ t₂ : term σ) (s : term σ) (k : ℕ) :
    (t₁ ∈' t₂)[s ⁄ k] = (t₁[s ⁄ k]) ∈' (t₂[s ⁄ k]) := rfl

/-- The subset predicate. -/
def subset (X Y : term σ) : formula σ :=
  ∀' ((#0 ∈' (X ↑ 1 ＠ 0)) →' (#0 ∈' (Y ↑ 1 ＠ 0)))

infix:100 " ⊆' " => subset

/-- `X` is the successor of `Y`. -/
def successor_def (X Y : term σ) : formula σ :=
  ∀' ((#0 ∈' (X ↑ 1 ＠ 0)) ↔'
    ((#0 ∈' (Y ↑ 1 ＠ 0)) ∨' (#0 =' (Y ↑ 1 ＠ 0))))

infix:100 " is_successor_of " => successor_def

/-- `x` is empty. -/
def empty_def (x : term σ) : formula σ :=
  ∀' ((#0 ∈' (x ↑ 1 ＠ 0)) ↔' ¬'(#0 =' #0))

postfix:100 " is_empty" => empty_def

/-- `x` is inductive. -/
def inductive_def (x : term σ) : formula σ :=
  (∀' (#0 is_empty →' (#0 ∈' (x ↑ 1 ＠ 0)))) ∧'
    (∀' (#0 ∈' (x ↑ 1 ＠ 0) →'
      (∀' (#0 is_successor_of #1 →' (#0 ∈' (x ↑ 2 ＠ 0))))))

postfix:100 " is_inductive" => inductive_def

/-- `x` is `ω`, the intersection of all inductive sets. -/
def omega_def (x : term σ) : formula σ :=
  ∀' (#0 ∈' (x ↑ 1 ＠ 0) ↔'
    ∀' (#0 is_inductive →' (x ↑ 1 ＠ 0) ∈' #0))

postfix:100 " is_omega" => omega_def

/-- Uniqueness in free variable zero. -/
@[simp] def unique_in_var0 (φ : formula σ) : formula σ :=
  ∀' ∀' ((φ ↑ 1 ＠ 1) ∧' (φ ↑ 1 ＠ 0) →' (#0 =' #1))

/-- Unique existential quantification. -/
@[simp] def unique_ex (φ : formula σ) : formula σ := (∃'φ) ∧' unique_in_var0 φ

prefix:110 "∃!" => unique_ex

end zfc_language

section zfc_axioms

namespace separation

/-- The separation scheme with its free parameters exposed. -/
@[simp] def free_formula (φ : formula σ) : formula σ :=
  ∀' ∃' ∀' ((#0 ∈' #1) ↔' (#0 ∈' #2 ∧' (φ ↑ 1 ＠ 1)))

lemma closed {k : ℕ} {φ : formula σ} (H : fol.formula.closed (k + 2) φ) :
    fol.formula.closed k (free_formula φ) := by
  have h₁ : ¬k + 3 ≤ 2 := by omega
  have h₂ : 1 ≤ k + 2 := by omega
  have h₃ : (φ ↑ 1 ＠ 1) ↑ 1 ＠ (k + 3) = φ ↑ 1 ＠ 1 := by
    rw [← fol.formula.lift_lift φ 1 1 h₂]
    congr
  simp [h₃]

/-- A closed instance of separation. -/
def formula (φ : fol.formula σ) {n : ℕ}
    (φ_h : fol.formula.closed (n + 2) φ) : fol.formula σ :=
  fol.formula.closure (free_formula φ) (closed φ_h)

lemma formula_is_sentence {k : ℕ} (φ : fol.formula σ)
    (H : fol.formula.closed (k + 2) φ) : sentence (formula φ H) :=
  fol.formula.closure_is_sentence (closed H)

lemma lift_sentence (φ : fol.formula σ) (n : ℕ)
    (φ_h : fol.formula.closed (n + 2) φ) (m i : ℕ) :
    (formula φ φ_h) ↑ m ＠ i = formula φ φ_h :=
  fol.formula.lift_sentence_id (formula_is_sentence φ φ_h)

lemma mem {Γ : Set (fol.formula σ)} (φ : fol.formula σ) (k : ℕ)
    (φ_h : fol.formula.closed (k + 2) φ) {ψ : fol.formula σ}
    (h : ψ = separation.formula φ φ_h) (H : separation.formula φ φ_h ∈ Γ) : ψ ∈ Γ := by
  subst ψ
  exact H

/-- The set of all closed separation instances. -/
def scheme : Set (fol.formula σ) :=
  {ψ | ∃ (φ : fol.formula σ) (k : ℕ) (φ_h : fol.formula.closed (k + 2) φ),
    ψ = separation.formula φ φ_h}

lemma mem_scheme (φ : fol.formula σ) {k : ℕ}
    (φ_h : fol.formula.closed (k + 2) φ) : separation.formula φ φ_h ∈ scheme :=
  ⟨φ, k, φ_h, rfl⟩

end separation

namespace replacement

/-- The replacement scheme with its free parameters exposed. -/
@[simp] def free_formula (φ : formula σ) : formula σ :=
  ∀' (∀' (#0 ∈' #1 →' ∃!φ) →'
    (∃' ∀' (#0 ∈' #2 →' (∃' (#0 ∈' #2 ∧' (φ ↑ 1 ＠ 2))))))

lemma closed {k : ℕ} {φ : formula σ} (H : fol.formula.closed (k + 3) φ) :
    fol.formula.closed k (free_formula φ) := by
  have h₀ : ¬k + 4 ≤ 3 := by omega
  have h₁ : ¬k + 4 ≤ 2 := by omega
  have h₂ : ¬k + 3 ≤ 2 := by omega
  have hk₀ : 0 ≤ k + 3 := Nat.zero_le _
  have hk₁ : 1 ≤ k + 3 := by omega
  have hk₂ : 2 ≤ k + 3 := by omega
  have H₀ : (φ ↑ 1 ＠ 0) ↑ 1 ＠ (k + 4) = φ ↑ 1 ＠ 0 := by
    rw [← fol.formula.lift_lift φ 1 1 hk₀]
    congr
  have H₁ : (φ ↑ 1 ＠ 1) ↑ 1 ＠ (k + 4) = φ ↑ 1 ＠ 1 := by
    rw [← fol.formula.lift_lift φ 1 1 hk₁]
    congr
  have H₂ : (φ ↑ 1 ＠ 2) ↑ 1 ＠ (k + 4) = φ ↑ 1 ＠ 2 := by
    rw [← fol.formula.lift_lift φ 1 1 hk₂]
    congr
  rw [fol.formula.closed] at H
  simp [H₀, H₁, H₂, fol.formula.closed, H]

/-- A closed instance of replacement. -/
def formula (φ : fol.formula σ) {n : ℕ}
    (φ_h : fol.formula.closed (n + 3) φ) : fol.formula σ :=
  fol.formula.closure (free_formula φ) (closed φ_h)

lemma formula_is_sentence (φ : fol.formula σ) {k : ℕ}
    (H : fol.formula.closed (k + 3) φ) : sentence (formula φ H) :=
  fol.formula.closure_is_sentence (closed H)

lemma lift_sentence (φ : fol.formula σ) (n : ℕ)
    (φ_h : fol.formula.closed (n + 3) φ) (m i : ℕ) :
    (formula φ φ_h) ↑ m ＠ i = formula φ φ_h :=
  fol.formula.lift_sentence_id (formula_is_sentence φ φ_h)

lemma mem {Γ : Set (fol.formula σ)} {ψ : fol.formula σ} (φ : fol.formula σ) {k : ℕ}
    (φ_h : fol.formula.closed (k + 3) φ) (h : ψ = formula φ φ_h)
    (H : formula φ φ_h ∈ Γ) : ψ ∈ Γ := by
  subst ψ
  exact H

/-- The set of all closed replacement instances. -/
def scheme : Set (fol.formula σ) :=
  {ψ | ∃ (φ : fol.formula σ) (k : ℕ) (φ_h : fol.formula.closed (k + 3) φ),
    ψ = formula φ φ_h}

lemma mem_scheme (φ : fol.formula σ) {k : ℕ}
    (φ_h : fol.formula.closed (k + 3) φ) : formula φ φ_h ∈ scheme :=
  ⟨φ, k, φ_h, rfl⟩

end replacement

@[simp] def extensionality : formula σ :=
  ∀' ∀' ((∀' (#0 ∈' #1 ↔' #0 ∈' #2)) →' (#0 =' #1))

@[simp] def pair_ax : formula σ :=
  ∀' ∀' ∃' ∀' ((#0 =' #2) ∨' (#0 =' #3) →' (#0 ∈' #1))

@[simp] def union_ax : formula σ :=
  ∀' ∃' ∀' ((∃' (#1 ∈' #0 ∧' #0 ∈' #3)) →' (#0 ∈' #1))

@[simp] def power_ax : formula σ :=
  ∀' ∃' ∀' (#0 ⊆' #2 →' #0 ∈' #1)

@[simp] def infinity_ax : formula σ := ∃' (#0 is_inductive)

@[simp] def regularity : formula σ :=
  ∀' (¬'(#0 is_empty) →' (∃' ((#0 ∈' #1) ∧' ¬'(∃' (#0 ∈' #1 ∧' #0 ∈' #2)))))

@[simp] def axiom_of_choice : formula σ :=
  ∀' (∀' ∀' (#0 ∈' #2 ∧' #1 ∈' #2 →'
      ∃' (#0 ∈' #1) ∧' (#0 =' #1 ∨' ∀' (¬'(#0 ∈' #1 ∧' #0 ∈' #2)))) →'
    ∃' ∀' (#0 ∈' #2 →' ∃!(#0 ∈' #1 ∧' #0 ∈' #2)))

@[simp] def separation_ax (φ : formula σ) {n : ℕ}
    (φ_h : fol.formula.closed (n + 2) φ) : formula σ := separation.formula φ φ_h

@[simp] def replacement_ax (φ : formula σ) {n : ℕ}
    (φ_h : fol.formula.closed (n + 3) φ) : formula σ := replacement.formula φ φ_h

/-- The axioms and axiom schemes of ZFC. -/
def zfc_ax : Set (formula σ) :=
  {extensionality, pair_ax, union_ax, power_ax, infinity_ax, regularity, axiom_of_choice} ∪
    separation.scheme ∪ replacement.scheme

lemma zfc_ax_set_of_sentences : ∀ x ∈ zfc_ax, sentence x := by
  intro x hx
  rcases hx with (hbase | hsep) | hrepl
  · rcases hbase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl
  · rcases hsep with ⟨φ, k, φ_h, rfl⟩
    exact separation.formula_is_sentence φ φ_h
  · rcases hrepl with ⟨φ, k, φ_h, rfl⟩
    exact replacement.formula_is_sentence φ φ_h

lemma lift_zfc_ax {m i : ℕ} : (fun φ : formula σ => φ ↑ m ＠ i) '' zfc_ax = zfc_ax :=
  fol.formula.lift_set_of_sentences_id zfc_ax_set_of_sentences

lemma extensionality_mem {Γ : Set (formula σ)} {φ : formula σ}
    (h : φ = extensionality) (H : extensionality ∈ Γ) : φ ∈ Γ := h ▸ H

lemma pair_ax_mem {Γ : Set (formula σ)} {φ : formula σ}
    (h : φ = pair_ax) (H : pair_ax ∈ Γ) : φ ∈ Γ := h ▸ H

lemma union_ax_mem {Γ : Set (formula σ)} {φ : formula σ}
    (h : φ = union_ax) (H : union_ax ∈ Γ) : φ ∈ Γ := h ▸ H

lemma power_ax_mem {Γ : Set (formula σ)} {φ : formula σ}
    (H : power_ax ∈ Γ) (h : φ = power_ax) : φ ∈ Γ := h ▸ H

lemma infinity_ax_mem {Γ : Set (formula σ)} {φ : formula σ}
    (h : φ = infinity_ax) (H : infinity_ax ∈ Γ) : φ ∈ Γ := h ▸ H

lemma regularity_mem {Γ : Set (formula σ)} {φ : formula σ}
    (h : φ = regularity) (H : regularity ∈ Γ) : φ ∈ Γ := h ▸ H

lemma aoc_mem {Γ : Set (formula σ)} {φ : formula σ}
    (h : φ = axiom_of_choice) (H : axiom_of_choice ∈ Γ) : φ ∈ Γ := h ▸ H

lemma extensionality_mem_zfc_ax : extensionality ∈ zfc_ax := by simp [zfc_ax]
lemma pair_ax_mem_zfc_ax : pair_ax ∈ zfc_ax := by simp [zfc_ax]
lemma union_ax_mem_zfc_ax : union_ax ∈ zfc_ax := by simp [zfc_ax]
lemma power_ax_mem_zfc_ax : power_ax ∈ zfc_ax := by simp [zfc_ax]
lemma infinity_ax_mem_zfc_ax : infinity_ax ∈ zfc_ax := by simp [zfc_ax]
lemma regularity_mem_zfc_ax : regularity ∈ zfc_ax := by simp [zfc_ax]
lemma aoc_mem_zfc_ax : axiom_of_choice ∈ zfc_ax := by simp [zfc_ax]

namespace separation

lemma mem_zfc_ax (φ : fol.formula σ) (k : ℕ)
    (φ_h : fol.formula.closed (k + 2) φ) : formula φ φ_h ∈ zfc_ax := by
  simp [zfc_ax, mem_scheme]

end separation

namespace replacement

lemma mem_zfc_ax (φ : fol.formula σ) (k : ℕ)
    (φ_h : fol.formula.closed (k + 3) φ) : formula φ φ_h ∈ zfc_ax := by
  simp [zfc_ax, mem_scheme]

end replacement

end zfc_axioms

section zfc_proofs

/-- For all sets `b, a`, there is a set containing exactly `a` and `b`. -/
def pairset_ex :
    zfc_ax ⊢ ∀' ∀' ∃' ∀' ((#0 ∈' #1) ↔' (#0 =' #2) ∨' (#0 =' #3)) := by
  apply allI
  apply allI
  apply exE (∀' ((#0 =' #2) ∨' (#0 =' #3) →' (#0 ∈' #1)))
  · have Hp :
        (fun g : formula σ => g ↑ 1 ＠ 0) ''
            (fun g : formula σ => g ↑ 1 ＠ 0) '' zfc_ax ⊢ pair_ax := by
      apply hypI
      simp only [lift_zfc_ax]
      exact pair_ax_mem_zfc_ax
    have Hp₁ := allE _ (t := (#1 : term σ)) Hp
    have Hp₂ := allE _ (t := (#0 : term σ)) Hp₁
    simpa using Hp₂
  · apply exE (∀' (#0 ∈' #1 ↔' (#0 ∈' #2) ∧' (#0 =' #3 ∨' #0 =' #4)))
    · have Hsep :
          (∀' ((#0 =' #2) ∨' (#0 =' #3) →' (#0 ∈' #1))) >>
              (fun g : formula σ => g ↑ 1 ＠ 0) ''
                (fun g : formula σ => g ↑ 1 ＠ 0) ''
                  (fun g : formula σ => g ↑ 1 ＠ 0) '' zfc_ax ⊢
            separation.formula ((#0 =' #2 ∨' #0 =' #3) : formula σ)
              (n := 2) (by rfl) := by
        apply hypI
        right
        simp only [lift_zfc_ax]
        exact separation.mem_zfc_ax ((#0 =' #2 ∨' #0 =' #3) : formula σ) 2 (by rfl)
      have Hsep₁ := allE _ (t := (#2 : term σ)) Hsep
      have Hsep₂ := allE _ (t := (#1 : term σ)) Hsep₁
      have Hsep₃ := allE _ (t := (#0 : term σ)) Hsep₂
      simpa [separation.formula, fol.formula.closure, alls] using Hsep₃
    · apply exI #0
      apply allI
      apply andI
      · apply impI
        apply andE₂ (#0 ∈' #2)
        apply impE_insert
        apply iffE_r
        apply allE_var0
        apply hypI
        tls
      · apply impI
        apply impE (#0 ∈' #2)
        · apply impE ((#0 =' #3) ∨' (#0 =' #4))
          · apply hypI1
          · apply allE_var0
            apply hypI
            tls
        · apply impI
          apply impE (#0 ∈' #2 ∧' ((#0 =' #3) ∨' (#0 =' #4)))
          · apply andI
            · apply hypI1
            · apply hypI2
          · apply iffE_l
            apply allE_var0
            apply hypI
            tls

/-- An empty set exists. -/
def emptyset_ex : zfc_ax ⊢ ∃' (#0 is_empty) := by
  apply exE (∀' (#0 ∈' #1 ↔' #0 ∈' #2 ∧' ¬'(#0 =' #0)))
  · apply allE_var0
    apply hypI
    apply separation.mem (¬'(#0 =' #0)) 0 rfl rfl
    apply separation.mem_zfc_ax
  · apply exI #0
    apply allI
    apply andI
    · apply impI
      apply andE₂ (#0 ∈' #2)
      apply impE_insert
      apply iffE_r
      apply allE_var0
      apply hypI
      tls
    · apply impI
      apply botE
      apply impE (#0 =' #0)
      apply eqI
      apply hypI
      tls

/-- For every `a`, the singleton `{a}` exists. -/
def singleton_ex : zfc_ax ⊢ ∀' ∃' ∀' (#0 ∈' #1 ↔' #0 =' #3) := by
  apply allI
  apply exE (∀' (#0 ∈' #1 ↔' #0 =' #3 ∨' #0 =' #3))
  · apply allE' _ #1
    apply allE' _ #1
    rw [lift_zfc_ax]
    apply pairset_ex
    all_goals tls
  · apply exI #0
    apply allI
    apply andI
    · apply impI
      apply orE (#0 =' #3) (#0 =' #3)
      · apply impE_insert
        apply iffE_r
        apply allE_var0
        apply hypI
        tls
      · apply hypI1
      · apply hypI1
    · apply impI
      apply impE ((#0 =' #3) ∨' (#0 =' #3))
      · apply orI₁
        apply hypI1
      · apply iffE_l
        apply allE_var0
        apply hypI
        tls

/-- Extensionality proves uniqueness for classes defined by a membership biconditional. -/
def extensionality_implies_uniqueness (φ : formula σ) :
    ({extensionality} : Set (formula σ)) ⊢
      unique_in_var0 (∀' (#0 ∈' #1 ↔' (φ ↑ 1 ＠ 1))) := by
  apply allI
  apply allI
  apply impI
  apply impE (∀' (#0 ∈' #1 ↔' #0 ∈' #2))
  · apply allI
    apply iffI_trans (φ ↑ 2 ＠ 1)
    · apply allE_var0
      apply andE₁ (∀' (#0 ∈' #3 ↔' (φ ↑ 3 ＠ 1)))
      apply hypI
      tls [fol.formula.lift_lift_merge]
    · apply iffI_symm
      apply allE_var0
      apply andE₂ (∀' (#0 ∈' #2 ↔' (φ ↑ 3 ＠ 1)))
      apply hypI
      tls [fol.formula.lift_lift_merge]
  · have He : ({extensionality} : Set (formula σ)) ⊢ extensionality :=
      hypI (Set.mem_singleton extensionality)
    have He₁ := allE _ (t := (#1 : term σ)) He
    have He₂ := allE _ (t := (#0 : term σ)) He₁
    apply weak_singleton extensionality He₂
    tls

/-- Context-polymorphic form of `extensionality_implies_uniqueness`. -/
def extensionality_implies_uniqueness' {Γ : Set (formula σ)} (φ : formula σ)
    {ψ : formula σ} (h : ψ = ∀' (#0 ∈' #1 ↔' (φ ↑ 1 ＠ 1)))
    (H : extensionality ∈ Γ) : Γ ⊢ unique_in_var0 ψ := by
  subst ψ
  exact weak_singleton extensionality (extensionality_implies_uniqueness φ) H

/-- Universally closed form of `extensionality_implies_uniqueness`. -/
def extensionality_implies_uniqueness_alls (n : ℕ) (φ : formula σ) :
    ({extensionality} : Set (formula σ)) ⊢
      alls n (unique_in_var0 (∀' (#0 ∈' #1 ↔' (φ ↑ 1 ＠ 1)))) := by
  apply allsI
  apply extensionality_implies_uniqueness' φ rfl
  tls

/-- Pair sets exist uniquely. -/
def pairset_unique_ex :
    zfc_ax ⊢ ∀' ∀' ∃!∀' ((#0 ∈' #1) ↔' (#0 =' #2) ∨' (#0 =' #3)) := by
  apply allI
  apply allI
  simp only [lift_zfc_ax]
  apply andI
  · have Hp₁ := allE _ (t := (#1 : term σ)) pairset_ex
    have Hp₂ := allE _ (t := (#0 : term σ)) Hp₁
    simpa using Hp₂
  · apply extensionality_implies_uniqueness' (#0 =' #1 ∨' #0 =' #2) rfl
    simp [-extensionality, zfc_ax]

/-- The empty set exists uniquely. -/
def emptyset_unique_ex : zfc_ax ⊢ ∃!(#0 is_empty) := by
  apply andI
  · exact emptyset_ex
  · apply extensionality_implies_uniqueness' (¬'(#0 =' #0)) rfl
    simp [-extensionality, zfc_ax]

/-- Singletons exist uniquely. -/
def singleton_unique_ex : zfc_ax ⊢ ∀' ∃!∀' (#0 ∈' #1 ↔' #0 =' #3) := by
  apply allsI 1
  apply andI
  · apply allsE' 1
    exact singleton_ex
  · apply extensionality_implies_uniqueness' (#0 =' #2) rfl
    simp only [lift_zfc_ax]
    simp [-extensionality, zfc_ax]

/-- Separation turns one-sided containment into an exact comprehension set. -/
def separation_proof_scheme (φ : formula σ) (k : ℕ)
    (φ_h₁ : closed (k + 2) φ) (φ_h₂ : not_free 1 φ)
    {Γ : Set (formula σ)} (h : separation_ax φ φ_h₁ ∈ Γ)
    (H : Γ ⊢ alls k (∃' ∀' (φ →' (#0 ∈' #1)))) :
    Γ ⊢ alls k (∃' ∀' ((#0 ∈' #1) ↔' φ)) := by
  apply allsI
  apply exE (∀' (φ →' (#0 ∈' #1)))
  · apply allsE'
    exact H
  · apply exE (∀' ((#0 ∈' #1) ↔' ((#0 ∈' #2) ∧' (φ ↑ 1 ＠ 1))))
    · apply weak1
      apply allsE' 1
      apply allsE' k
      rw [alls, alls]
      apply hypI
      apply separation.mem φ k φ_h₁ rfl
      exact h
    · apply exI #0
      apply allI
      apply andI
      · apply impI
        apply andE₂ (#0 ∈' #2)
        apply impE_insert
        apply iffE_r
        apply allE_var0
        apply hypI
        rcases φ_h₂ with ⟨ψ, rfl⟩
        tls [← lift_lift ψ 1 1 le_rfl]
      · apply impI
        apply impE (#0 ∈' #2)
        · apply impE (φ ↑ 1 ＠ 1)
          · apply hypI
            rcases φ_h₂ with ⟨ψ, rfl⟩
            tls [← lift_lift ψ 1 1 le_rfl]
          · apply allE_var0
            apply hypI
            tls
        · apply impI
          apply impE (#0 ∈' #2 ∧' (φ ↑ 1 ＠ 1))
          · apply andI
            · apply hypI1
            · apply hypI
              rcases φ_h₂ with ⟨ψ, rfl⟩
              tls [lift_lift ψ 1 1 le_rfl]
          · apply iffE_l
            apply allE_var0
            apply hypI
            tls

/-- Convenient named-result form of `separation_proof_scheme`. -/
def separation_proof_scheme' (φ : formula σ) (k : ℕ)
    (φ_h : closed (k + 2) (φ ↑ 1 ＠ 1)) {ψ : formula σ}
    (ψ_h : ψ = alls k (∃' ∀' ((#0 ∈' #1) ↔' (φ ↑ 1 ＠ 1))))
    {Γ : Set (formula σ)}
    (h : separation.formula (φ ↑ 1 ＠ 1) φ_h ∈ Γ)
    (H : Γ ⊢ alls k (∃' ∀' (φ ↑ 1 ＠ 1 →' (#0 ∈' #1)))) : Γ ⊢ ψ := by
  subst ψ
  exact separation_proof_scheme (φ ↑ 1 ＠ 1) k φ_h ⟨φ, rfl⟩ h H

/-- The union of every set exists. -/
def unionset_ex :
    zfc_ax ⊢ ∀' ∃' ∀' ((#0 ∈' #1) ↔' ∃' (#1 ∈' #0 ∧' #0 ∈' #3)) := by
  apply separation_proof_scheme' (∃' (#1 ∈' #0 ∧' #0 ∈' #2)) 1
  · rfl
  · apply separation.mem_zfc_ax
  · apply hypI
    apply union_ax_mem_zfc_ax
  · dsimp
    rfl

/-- The union of every set exists uniquely. -/
def unionset_unique_ex :
    zfc_ax ⊢ ∀' ∃!∀' ((#0 ∈' #1) ↔' ∃' (#1 ∈' #0 ∧' #0 ∈' #3)) := by
  apply allI
  simp only [lift_zfc_ax]
  apply andI
  · have Hu := allE _ (t := (#0 : term σ)) unionset_ex
    simpa using Hu
  · apply extensionality_implies_uniqueness' (∃' (#1 ∈' #0 ∧' #0 ∈' #2)) rfl
    simp [-extensionality, zfc_ax]

/-- The powerset of every set exists. -/
def powerset_ex : zfc_ax ⊢ ∀' ∃' ∀' ((#0 ∈' #1) ↔' (#0 ⊆' #2)) := by
  apply separation_proof_scheme' (#0 ⊆' #1) 1
  · rfl
  · apply separation.mem_zfc_ax
  · apply hypI
    apply power_ax_mem_zfc_ax
  · dsimp
    rfl

/-- The powerset of every set exists uniquely. -/
def powerset_unique_ex : zfc_ax ⊢ ∀' ∃!∀' ((#0 ∈' #1) ↔' (#0 ⊆' #2)) := by
  apply allI
  simp only [lift_zfc_ax]
  apply andI
  · apply allE_var0
    exact powerset_ex
  · apply extensionality_implies_uniqueness' (#0 ⊆' #1) rfl
    simp [-extensionality, zfc_ax]

/-- Binary unions exist. -/
def binary_union_ex :
    zfc_ax ⊢ ∀' ∀' ∃' ∀' (#0 ∈' #1 ↔' #0 ∈' #2 ∨' #0 ∈' #3) := by
  apply separation_proof_scheme' (#0 ∈' #1 ∨' #0 ∈' #2) 2
  · rfl
  · apply separation.mem_zfc_ax
  · apply allI
    apply allI
    apply exE (∀' ((#0 ∈' #1) ↔' (#0 =' #2) ∨' (#0 =' #3)))
    · simp only [lift_zfc_ax]
      have Hp₁ := allE _ (t := (#1 : term σ)) pairset_ex
      have Hp₂ := allE _ (t := (#0 : term σ)) Hp₁
      simpa using Hp₂
    · apply exE (∀' ((#0 ∈' #1) ↔' ∃' (#1 ∈' #0 ∧' #0 ∈' #3)))
      · simp only [lift_zfc_ax]
        have Hu := weak1 (f := (∀' (#0 ∈' #1 ↔' (#0 =' #2) ∨' (#0 =' #3)))) unionset_ex
        have Hu₀ := allE _ (t := (#0 : term σ)) Hu
        simpa using Hu₀
      · apply exI #0
        apply allI
        apply impI
        apply orE (#0 ∈' #3) (#0 ∈' #4)
        · apply hypI1
        · apply impE (∃' (#1 ∈' #0 ∧' #0 ∈' #3))
          · apply exI #3
            apply andI
            · apply hypI1
            · apply impE (#3 =' #3 ∨' #3 =' #4)
              · apply orI₁
                apply eqI
              · apply iffE_l
                apply allE' ((#0 ∈' #3) ↔' (#0 =' #4) ∨' (#0 =' #5)) #3
                apply hypI
                all_goals tls
          · apply iffE_l
            apply allE_var0
            apply hypI
            tls
        · apply impE (∃' (#1 ∈' #0 ∧' #0 ∈' #3))
          · apply exI #4
            apply andI
            · apply hypI1
            · apply impE (#4 =' #3 ∨' #4 =' #4)
              · apply orI₂
                apply eqI
              · apply iffE_l
                apply allE' ((#0 ∈' #3) ↔' (#0 =' #4) ∨' (#0 =' #5)) #4
                apply hypI
                all_goals tls
          · apply iffE_l
            apply allE_var0
            apply hypI
            tls
  · tls

/-- Binary unions exist uniquely. -/
def binary_union_unique_ex :
    zfc_ax ⊢ ∀' ∀' ∃!∀' (#0 ∈' #1 ↔' #0 ∈' #2 ∨' #0 ∈' #3) := by
  apply allsI 2
  apply andI
  · apply allsE' 2
    exact binary_union_ex
  · apply extensionality_implies_uniqueness' (#0 ∈' #1 ∨' #0 ∈' #2) rfl
    simp only [lift_zfc_ax]
    simp [-extensionality, zfc_ax]

/-- Successor sets exist. -/
def successor_ex : zfc_ax ⊢ ∀' ∃' (#0 is_successor_of #1) := by
  apply separation_proof_scheme' (#0 ∈' #1 ∨' (#0 =' #1)) 1
  · rfl
  · apply separation.mem_zfc_ax
  · apply allI
    apply exE (∀' (#0 ∈' #1 ↔' #0 =' #2))
    · simp only [lift_zfc_ax]
      have Hs := allE _ (t := (#0 : term σ)) singleton_ex
      simpa using Hs
    · apply exE (∀' (#0 ∈' #1 ↔' #0 ∈' #3 ∨' #0 ∈' #2))
      · simp only [lift_zfc_ax]
        have Hb := weak1 (f := (∀' (#0 ∈' #1 ↔' #0 =' #2))) binary_union_ex
        have Hb₁ := allE _ (t := (#0 : term σ)) Hb
        have Hb₂ := allE _ (t := (#1 : term σ)) Hb₁
        simpa using Hb₂
      · apply exI #0
        apply allI
        apply impI
        apply orE (#0 ∈' #3) (#0 =' #3)
        · apply hypI1
        · apply impE (#0 ∈' #3 ∨' #0 ∈' #2)
          · apply orI₁
            apply hypI1
          · apply iffE_l
            apply allE_var0
            apply hypI
            tls
        · apply impE (#0 ∈' #3 ∨' #0 ∈' #2)
          · apply orI₂
            apply impE_insert
            apply iffE_l
            apply allE_var0
            apply hypI
            tls
          · apply iffE_l
            apply allE_var0
            apply hypI
            tls
  · tls

/-- Successor sets exist uniquely. -/
def successor_unique_ex : zfc_ax ⊢ ∀' ∃!(#0 is_successor_of #1) := by
  apply allsI 1
  apply andI
  · apply allsE' 1
    exact successor_ex
  · apply extensionality_implies_uniqueness' (#0 ∈' #1 ∨' (#0 =' #1)) rfl
    simp only [lift_zfc_ax]
    simp [-extensionality, zfc_ax]

/-- A set containing exactly the elements common to all inductive sets exists. -/
def omega_ex : zfc_ax ⊢ ∃' (#0 is_omega) := by
  apply separation_proof_scheme' (∀' (#0 is_inductive →' #1 ∈' #0)) 0
  · rfl
  · apply separation.mem_zfc_ax
  · apply exE (#0 is_inductive)
    · apply hypI
      exact infinity_ax_mem_zfc_ax
    · apply exE (∀' (#0 ∈' #1 ↔'
        #0 ∈' #2 ∧' ∀' (#0 is_inductive →' #1 ∈' #0)))
      · apply allE_var0
        apply hypI
        simp only [lift_zfc_ax]
        right
        exact separation.mem_zfc_ax (∀' (#0 is_inductive →' #1 ∈' #0)) 0 (by rfl)
      · apply exI #0
        apply allI
        apply impI
        apply iffE₁ (#0 ∈' #2 ∧' ∀' (#0 is_inductive →' #1 ∈' #0))
        · apply andI
          · apply impE (#2 is_inductive)
            · apply hypI
              tls [inductive_def, empty_def, successor_def]
            · apply allE' _ #2
              apply hypI
              all_goals tls
          · apply hypI1
        · apply allE_var0
          apply hypI
          tls
  · tls

/-- `ω` exists uniquely. -/
def omega_unique_ex : zfc_ax ⊢ ∃!(#0 is_omega) := by
  apply andI
  · exact omega_ex
  · apply extensionality_implies_uniqueness'
      (∀' (#0 is_inductive →' #1 ∈' #0)) rfl
    simp [-extensionality, zfc_ax]

/-- `ω` is a subset of every inductive set. -/
def omega_subset_all_inductive :
    zfc_ax ⊢ ∀' ((#0 is_omega) →' ∀' (#0 is_inductive →' #1 ⊆' #0)) := by
  apply allI
  apply impI
  apply allI
  apply impI
  apply allI
  apply impI
  apply impE (#1 is_inductive)
  · apply hypI
    tls
  · apply allE' _ #1
    apply iffE₂ (#0 ∈' #2)
    · apply hypI1
    · apply allE_var0
      apply hypI
      tls
    · tls

/-- `ω` is inductive. -/
def omega_inductive :
    zfc_ax ⊢ ∀' ((#0 is_omega) →' (#0 is_inductive)) := by
  apply allI
  apply impI
  apply andI
  · apply allI
    apply impI
    apply iffE₁ (∀' (#0 is_inductive →' #1 ∈' #0))
    · apply allI
      apply impI
      apply impE (#1 is_empty)
      · apply hypI
        tls
      · apply allE' _ #1
        apply andE₁
        apply hypI1
        · tls [empty_def]
    · apply allE_var0
      apply hypI
      tls
  · apply allI
    apply impI
    apply allI
    apply impI
    apply impE (∀' (#0 is_inductive →' #1 ∈' #0))
    · apply allI
      apply impI
      apply impE (#2 ∈' #0)
      · apply impE (#2 ∈' #3)
        · apply hypI
          tls
        · apply allE' (#0 ∈' #4 →' #0 ∈' #1) #2
          apply impE (#0 is_inductive)
          · apply hypI1
          · apply allE_var0
            apply impE (∀' (#0 ∈' #4 ↔'
                ∀' (#0 is_inductive →' #1 ∈' #0)))
            · apply hypI
              tls
            · apply allE' _ #3
              apply weak zfc_ax
              · exact omega_subset_all_inductive
              · intro q hq
                tls [lift_zfc_ax,
                  fol.formula.lift_sentence_id (zfc_ax_set_of_sentences q hq)]
              · tls [inductive_def]
          · tls
      · apply impI
        apply impE (#1 is_successor_of #2)
        · apply hypI
          tls [successor_def]
        · apply allE' (#0 is_successor_of #3 →' #0 ∈' #1) #1
          · apply impE (#2 ∈' #0)
            · apply hypI1
            · apply allE'
                (#0 ∈' #1 →' ∀' (#0 is_successor_of #1 →' #0 ∈' #2)) #2
              · apply andE₂ (∀' (#0 is_empty →' #0 ∈' #1))
                apply hypI
                tls [inductive_def]
              · tls [successor_def]
          · tls [successor_def]
    · apply iffE_l
      apply allE_var0
      apply hypI
      tls

/-- `ω` exists uniquely and is the smallest inductive set. -/
def omega_smallest_inductive : zfc_ax ⊢
    ∃!(#0 is_omega) ∧'
      ∀' ((#0 is_omega) →'
        (#0 is_inductive ∧' ∀' (#0 is_inductive →' #1 ⊆' #0))) := by
  apply andI
  · exact omega_unique_ex
  · apply allI
    apply impI
    apply andI
    · apply impE_insert
      apply allE_var0
      simp only [lift_zfc_ax]
      exact omega_inductive
    · apply impE_insert
      apply allE_var0
      simp only [lift_zfc_ax]
      exact omega_subset_all_inductive

end zfc_proofs

/-- ZFC proves that `ω` is the smallest inductive set. -/
theorem omega_smallest_inductive_provable_within_zfc :
    (∃!(#0 is_omega) ∧'
      ∀' ((#0 is_omega) →'
        (#0 is_inductive ∧' ∀' (#0 is_inductive →' #1 ⊆' #0))))
      is_provable_within zfc_ax :=
  ⟨omega_smallest_inductive⟩

end zfc
