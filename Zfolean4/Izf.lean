import Zfolean4.Fol

set_option linter.style.header false
set_option linter.style.multiGoal false
set_option linter.style.whitespace false

/-!
# IZF set theory

This file defines a first-order presentation of intuitionistic Zermelo–Fraenkel set theory
with primitive symbols for the empty set, pair sets, unions, powersets, and `ω`. It also
formalizes that `ω` is the smallest inductive set in the natural-deduction calculus from
`Zfolean4.Fol`.

## Main results

- `omega_smallest_inductive_provable`:
    we show that ZFC proves that ω is the smallest inductive set. a direct consequence of
- `omega_smallest_inductive`:
    a natural deduction proof that ω is the smallest inductive set

## References
* [P. Aczel, M. Rathjen, *Notes on Constructive Set Theory*] [AR01]
  -- for the axioms of IZF
* [L. Crosilla, *Set Theory: Constructive and Intuitionistic ZF*] [LC20]
  -- for cross referencing

-/

universe u

namespace izf

open fol

local infixr:70 " >> " => Set.insert

section izf_language

/-- IZF has one binary predicate symbol, membership. -/
inductive pred_symb : ℕ → Type u where
  | elem : pred_symb 2

/-- Primitive constants and set-forming operations used by this presentation of IZF. -/
inductive func_symb : ℕ → Type u where
  | empty : func_symb 0
  | omega : func_symb 0
  | union : func_symb 1
  | power : func_symb 1
  | pair : func_symb 2

/-- The first-order signature of IZF. -/
def σ : signature where
  func_symb := izf.func_symb
  pred_symb := izf.pred_symb

@[simp, tls] def emptyset : term σ := func func_symb.empty
@[simp, tls] def omegaset : term σ := func func_symb.omega
@[simp, tls] def unionset (t : term σ) : term σ := fapp (func func_symb.union) t
@[simp, tls] def powerset (t : term σ) : term σ := fapp (func func_symb.power) t
@[simp, tls] def pairset (t₁ t₂ : term σ) : term σ :=
  fapp (fapp (func func_symb.pair) t₁) t₂

notation "⌀" => emptyset
notation "ω" => omegaset
prefix:110 "⋃" => unionset
prefix:110 "𝒫" => powerset
notation "⦃" a ", " b "⦄" => pairset a b
notation "⦃" a "⦄" => pairset a a

/-- The membership predicate. -/
@[simp, tls] def memb (t₁ t₂ : term σ) : formula σ :=
  papp (papp (pred pred_symb.elem) t₁) t₂

infix:100 " ∈' " => memb

/-- The subset predicate. -/
@[simp, tls] def subset (t₁ t₂ : term σ) : formula σ :=
  ∀' (#0 ∈' (t₁ ↑ 1 ＠ 0) →' #0 ∈' (t₂ ↑ 1 ＠ 0))

infix:100 " ⊆' " => subset

/-- The von Neumann successor of a set. -/
@[simp, tls] def successor_set (t : term σ) : term σ := ⋃⦃t, ⦃t⦄⦄

prefix:max "S" => successor_set

/-- A set is inductive when it contains `⌀` and is closed under successor. -/
@[simp, tls] def inductive_def (t : term σ) : formula σ :=
  ⌀ ∈' t ∧' ∀' (#0 ∈' (t ↑ 1 ＠ 0) →' S #0 ∈' (t ↑ 1 ＠ 0))

postfix:100 " is_inductive" => inductive_def

/-- Uniqueness in free variable zero. -/
@[simp] def unique_in_var0 (φ : formula σ) : formula σ :=
  ∀' ∀' ((φ ↑ 1 ＠ 1) ∧' (φ ↑ 1 ＠ 0) →' (#0 =' #1))

/-- Unique existential quantification. -/
@[simp] def unique_ex (φ : formula σ) : formula σ := (∃'φ) ∧' unique_in_var0 φ

prefix:110 "∃!" => unique_ex

end izf_language

section izf_axioms

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

namespace collection

/-- The collection scheme with its free parameters exposed. -/
@[simp] def free_formula (φ : formula σ) : formula σ :=
  ∀' (∀' (#0 ∈' #1 →' ∃'φ) →'
    (∃' ∀' (#0 ∈' #2 →' (∃' (#0 ∈' #2 ∧' (φ ↑ 1 ＠ 2))))))

lemma closed {φ : formula σ} {k : ℕ} (H : fol.formula.closed (k + 3) φ) :
    fol.formula.closed k (free_formula φ) := by
  have hk₂ : 2 ≤ k + 3 := by omega
  have H₂ : (φ ↑ 1 ＠ 2) ↑ 1 ＠ (k + 4) = φ ↑ 1 ＠ 2 := by
    rw [← fol.formula.lift_lift φ 1 1 hk₂]
    congr
  rw [fol.formula.closed] at H
  simp [H₂, fol.formula.closed, H]

/-- A closed instance of collection. -/
def formula (φ : fol.formula σ) {k : ℕ}
    (φ_h : fol.formula.closed (k + 3) φ) : fol.formula σ :=
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

/-- The set of all closed collection instances. -/
def scheme : Set (fol.formula σ) :=
  {ψ | ∃ (φ : fol.formula σ) (k : ℕ) (φ_h : fol.formula.closed (k + 3) φ),
    ψ = formula φ φ_h}

lemma mem_scheme (φ : fol.formula σ) {k : ℕ}
    (φ_h : fol.formula.closed (k + 3) φ) : formula φ φ_h ∈ scheme :=
  ⟨φ, k, φ_h, rfl⟩

end collection

namespace set_induction

/-- The set-induction scheme with its free parameters exposed. -/
@[simp] def free_formula (φ : formula σ) : formula σ :=
  (∀' (∀' (#0 ∈' #1 →' (φ ↑ 1 ＠ 1)) →' φ)) →' (∀'φ)

lemma closed {φ : formula σ} {n : ℕ} (φ_h : fol.formula.closed (n + 1) φ) :
    fol.formula.closed n (free_formula φ) := by
  have h : (φ ↑ 1 ＠ 1) ↑ 1 ＠ (n + 2) = φ ↑ 1 ＠ 1 := by
    rw [← fol.formula.lift_lift φ 1 1 (Nat.succ_pos n)]
    congr
  rw [fol.formula.closed] at φ_h
  simp [h, φ_h]

/-- A closed instance of set induction. -/
def formula (φ : fol.formula σ) {n : ℕ}
    (φ_h : fol.formula.closed (n + 1) φ) : fol.formula σ :=
  fol.formula.closure (free_formula φ) (closed φ_h)

lemma formula_is_sentence (φ : fol.formula σ) {n : ℕ}
    (φ_h : fol.formula.closed (n + 1) φ) : sentence (formula φ φ_h) :=
  fol.formula.closure_is_sentence (closed φ_h)

lemma lift_sentence (φ : fol.formula σ) (n : ℕ)
    (φ_h : fol.formula.closed (n + 1) φ) (m i : ℕ) :
    (formula φ φ_h) ↑ m ＠ i = formula φ φ_h :=
  fol.formula.lift_sentence_id (formula_is_sentence φ φ_h)

lemma mem {Γ : Set (fol.formula σ)} {ψ : fol.formula σ} (φ : fol.formula σ) {n : ℕ}
    (φ_h : fol.formula.closed (n + 1) φ) (h : ψ = formula φ φ_h)
    (H : formula φ φ_h ∈ Γ) : ψ ∈ Γ := by
  subst ψ
  exact H

/-- The set of all closed set-induction instances. -/
def scheme : Set (fol.formula σ) :=
  {ψ | ∃ (φ : fol.formula σ) (k : ℕ) (φ_h : fol.formula.closed (k + 1) φ),
    ψ = formula φ φ_h}

lemma mem_scheme (φ : fol.formula σ) {k : ℕ}
    (φ_h : fol.formula.closed (k + 1) φ) : formula φ φ_h ∈ scheme :=
  ⟨φ, k, φ_h, rfl⟩

end set_induction

@[simp] def extensionality : formula σ :=
  ∀' ∀' ((∀' (#0 ∈' #1 ↔' #0 ∈' #2)) →' (#0 =' #1))

@[simp] def emptyset_ax : formula σ :=
  ∀' (#0 ∈' ⌀ ↔' ¬'(#0 =' #0))

@[simp] def pairset_ax : formula σ :=
  ∀' ∀' ∀' (#0 ∈' ⦃#1, #2⦄ ↔' (#0 =' #1 ∨' #0 =' #2))

@[simp] def unionset_ax : formula σ :=
  ∀' ∀' (#0 ∈' ⋃#1 ↔' ∃' (#1 ∈' #0 ∧' #0 ∈' #2))

@[simp] def powerset_ax : formula σ :=
  ∀' ∀' (#0 ∈' 𝒫#1 ↔' #0 ⊆' #1)

@[simp] def omega_ax : formula σ :=
  ∀' (#0 ∈' ω ↔' ∀' (#0 is_inductive →' #1 ∈' #0))

@[simp, tls] lemma lift_extensionality (m i : ℕ) :
    extensionality ↑ m ＠ i = extensionality :=
  fol.formula.lift_sentence_id (by rfl)

@[simp, tls] lemma lift_emptyset_ax (m i : ℕ) :
    emptyset_ax ↑ m ＠ i = emptyset_ax :=
  fol.formula.lift_sentence_id (by rfl)

@[simp, tls] lemma lift_pairset_ax (m i : ℕ) :
    pairset_ax ↑ m ＠ i = pairset_ax :=
  fol.formula.lift_sentence_id (by rfl)

@[simp, tls] lemma lift_unionset_ax (m i : ℕ) :
    unionset_ax ↑ m ＠ i = unionset_ax :=
  fol.formula.lift_sentence_id (by rfl)

@[simp, tls] lemma lift_powerset_ax (m i : ℕ) :
    powerset_ax ↑ m ＠ i = powerset_ax :=
  fol.formula.lift_sentence_id (by rfl)

@[simp, tls] lemma lift_omega_ax (m i : ℕ) :
    omega_ax ↑ m ＠ i = omega_ax :=
  fol.formula.lift_sentence_id (by rfl)

@[simp] def set_induction_ax (φ : formula σ) {n : ℕ}
    (φ_h : closed (n + 1) φ) : formula σ := set_induction.formula φ φ_h

@[simp] def separation_ax (φ : formula σ) {n : ℕ}
    (φ_h : closed (n + 2) φ) : formula σ := separation.formula φ φ_h

@[simp] def collection_ax (φ : formula σ) {n : ℕ}
    (φ_h : closed (n + 3) φ) : formula σ := collection.formula φ φ_h

lemma extensionality_mem {Γ : Set (formula σ)} {φ : formula σ}
    (h : φ = extensionality) (H : extensionality ∈ Γ) : φ ∈ Γ := h ▸ H

lemma emptyset_ax_mem {Γ : Set (formula σ)} {φ : formula σ}
    (h : φ = emptyset_ax) (H : emptyset_ax ∈ Γ) : φ ∈ Γ := h ▸ H

lemma pairset_ax_mem {Γ : Set (formula σ)} {φ : formula σ}
    (h : φ = pairset_ax) (H : pairset_ax ∈ Γ) : φ ∈ Γ := h ▸ H

lemma unionset_ax_mem {Γ : Set (formula σ)} {φ : formula σ}
    (h : φ = unionset_ax) (H : unionset_ax ∈ Γ) : φ ∈ Γ := h ▸ H

lemma powerset_ax_mem {Γ : Set (formula σ)} {φ : formula σ}
    (H : powerset_ax ∈ Γ) (h : φ = powerset_ax) : φ ∈ Γ := h ▸ H

lemma omega_ax_mem {Γ : Set (formula σ)} {φ : formula σ}
    (h : φ = omega_ax) (H : omega_ax ∈ Γ) : φ ∈ Γ := h ▸ H

/-- The axioms and axiom schemes of IZF. -/
def izf_ax : Set (formula σ) :=
  {extensionality, emptyset_ax, pairset_ax, unionset_ax, powerset_ax, omega_ax} ∪
    set_induction.scheme ∪ separation.scheme ∪ collection.scheme

lemma izf_ax_set_of_sentences : ∀ φ ∈ izf_ax, sentence φ := by
  intro φ hφ
  rcases hφ with ((hbase | hind) | hsep) | hcoll
  · rcases hbase with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl
  · rcases hind with ⟨ψ, k, ψ_h, rfl⟩
    exact set_induction.formula_is_sentence ψ ψ_h
  · rcases hsep with ⟨ψ, k, ψ_h, rfl⟩
    exact separation.formula_is_sentence ψ ψ_h
  · rcases hcoll with ⟨ψ, k, ψ_h, rfl⟩
    exact collection.formula_is_sentence ψ ψ_h

lemma lift_izf_ax {m i : ℕ} : (fun φ : formula σ => φ ↑ m ＠ i) '' izf_ax = izf_ax :=
  fol.formula.lift_set_of_sentences_id izf_ax_set_of_sentences

end izf_axioms

section izf_proofs

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

/-- The primitive pair operation defines singleton sets. -/
def singleton_def :
    ({pairset_ax} : Set (formula σ)) ⊢
      ∀' ∀' (#0 ∈' ⦃#1⦄ ↔' #0 =' #1) := by
  apply allI
  apply allI
  apply andI
  · apply impI
    apply orE (#0 =' #1) (#0 =' #1)
    · apply impE_insert
      apply iffE_r
      apply allE_var0
      apply allE' _ #1
      apply allE' _ #1
      apply hypI
      apply pairset_ax_mem rfl
      all_goals tls
    · apply hypI1
    · apply hypI1
  · apply impI
    apply impE (#0 =' #1 ∨' #0 =' #1)
    · apply orI₁
      apply hypI1
    · apply iffE_l
      apply allE_var0
      apply allE' _ #1
      apply allE' _ #1
      apply hypI
      apply pairset_ax_mem rfl
      all_goals tls

/-- Context-polymorphic form of `singleton_def`. -/
def singleton_def' {Γ : Set (formula σ)} {φ : formula σ}
    (h₁ : φ = ∀' ∀' (#0 ∈' ⦃#1⦄ ↔' #0 =' #1))
    (h₂ : pairset_ax ∈ Γ) : Γ ⊢ φ := by
  subst φ
  exact weak_singleton pairset_ax singleton_def h₂

/-- The primitive pair and union operations define binary unions. -/
def binary_union_def :
    ({pairset_ax, unionset_ax} : Set (formula σ)) ⊢
      ∀' ∀' ∀' (#0 ∈' ⋃⦃#1, #2⦄ ↔' #0 ∈' #1 ∨' #0 ∈' #2) := by
  apply allI
  apply allI
  apply allI
  apply andI
  · apply impI
    apply exE (#1 ∈' #0 ∧' #0 ∈' ⦃#2, #3⦄)
    · apply impE_insert
      apply iffE_r
      apply allE' _ #0
      apply allE' _ ⦃#1, #2⦄
      apply hypI
      apply unionset_ax_mem rfl
      all_goals tls
    · apply impE (#0 =' #2 ∨' #0 =' #3)
      · apply impE (#0 ∈' ⦃#2, #3⦄)
        · apply andE₂
          apply hypI1
        · apply iffE_r
          apply allE' _ #0
          apply allE' _ #2
          apply allE' _ #3
          apply hypI
          apply pairset_ax_mem rfl
          all_goals tls
      · apply impI
        apply orE (#0 =' #2) (#0 =' #3)
        · apply hypI1
        · apply orI₁
          apply eqE' #0 #2 (#2 ∈' #0)
          · apply hypI1
          · apply andE₁
            apply hypI
            tls
          · rfl
        · apply orI₂
          apply eqE' #0 #3 (#2 ∈' #0)
          · apply hypI1
          · apply andE₁
            apply hypI
            tls
          · rfl
  · apply impI
    apply orE (#0 ∈' #1) (#0 ∈' #2)
    · apply hypI1
    · apply impE (∃' (#1 ∈' #0 ∧' #0 ∈' ⦃#2, #3⦄))
      · apply exI #1
        apply andI
        · apply hypI1
        · apply impE (#1 =' #1 ∨' #1 =' #2)
          · apply orI₁
            apply eqI
          · apply iffE_l
            apply allE' _ #1
            apply allE' _ #1
            apply allE' _ #2
            apply hypI
            apply pairset_ax_mem rfl
            all_goals tls
      · apply iffE_l
        apply allE_var0
        apply allE' _ ⦃#1, #2⦄
        apply hypI
        apply unionset_ax_mem rfl
        all_goals tls
    · apply impE (∃' (#1 ∈' #0 ∧' #0 ∈' ⦃#2, #3⦄))
      · apply exI #2
        apply andI
        · apply hypI1
        · apply impE (#2 =' #1 ∨' #2 =' #2)
          · apply orI₂
            apply eqI
          · apply iffE_l
            apply allE' _ #2
            apply allE' _ #1
            apply allE' _ #2
            apply hypI
            apply pairset_ax_mem rfl
            all_goals tls
      · apply iffE_l
        apply allE_var0
        apply allE' _ ⦃#1, #2⦄
        apply hypI
        apply unionset_ax_mem rfl
        all_goals tls

/-- Context-polymorphic form of `binary_union_def`. -/
def binary_union_def' {Γ : Set (formula σ)} {φ : formula σ}
    (h₁ : φ = ∀' ∀' ∀' (#0 ∈' ⋃⦃#1, #2⦄ ↔' #0 ∈' #1 ∨' #0 ∈' #2))
    (h₂ : pairset_ax ∈ Γ) (h₃ : unionset_ax ∈ Γ) : Γ ⊢ φ := by
  subst φ
  apply weak ({pairset_ax, unionset_ax} : Set (formula σ))
  · exact binary_union_def
  · intro ψ hψ
    rcases hψ with rfl | rfl
    · exact h₂
    · exact h₃

/-- The term `S a = a ∪ {a}` defines the von Neumann successor. -/
def successor_def :
    ({pairset_ax, unionset_ax} : Set (formula σ)) ⊢
      ∀' ∀' (#0 ∈' S #1 ↔' #0 ∈' #1 ∨' #0 =' #1) := by
  apply allI
  apply allI
  apply andI
  · apply impI
    apply impE (#0 ∈' #1 ∨' #0 ∈' ⦃#1⦄)
    · apply impE (#0 ∈' S #1)
      · apply hypI1
      · apply iffE_r
        apply allE_var0
        apply allE' _ #1
        apply allE' _ ⦃#1⦄
        apply binary_union_def' rfl
        all_goals tls
    · apply impI
      apply orE (#0 ∈' #1) (#0 ∈' ⦃#1⦄)
      · apply hypI1
      · apply orI₁
        apply hypI1
      · apply orI₂
        apply impE_insert
        apply iffE_r
        apply allE_var0
        apply allE' _ #1
        apply singleton_def' rfl
        all_goals tls
  · apply impI
    apply orE (#0 ∈' #1) (#0 =' #1)
    · apply hypI1
    · apply impE (#0 ∈' #1 ∨' #0 ∈' ⦃#1⦄)
      · apply orI₁
        apply hypI1
      · apply iffE_l
        apply allE' _ #0
        apply allE' _ #1
        apply allE' _ ⦃#1⦄
        apply binary_union_def' rfl
        all_goals tls
    · apply impE (#0 ∈' #1 ∨' #0 ∈' ⦃#1⦄)
      · apply orI₂
        apply impE_insert
        apply iffE_l
        apply allE' _ #0
        apply allE' _ #1
        apply singleton_def' rfl
        all_goals tls
      · apply iffE_l
        apply allE' _ #0
        apply allE' _ #1
        apply allE' _ ⦃#1⦄
        apply binary_union_def' rfl
        all_goals tls

/-- The primitive constant `ω` is trivially unique as a denoting term. -/
def omega_unique : (∅ : Set (formula σ)) ⊢ ∃!(#0 =' ω) := by
  apply andI
  · apply exI ω
    apply eqI
  · apply allsI 2
    apply impI
    apply eqE' ω #1 (#1 =' #0)
    · apply eqI_symm
      apply andE₂
      apply hypI1
    · apply andE₁
      apply hypI1
    · rfl

/-- `ω` is a subset of every inductive set. -/
def omega_subset_all_inductive :
    ({omega_ax} : Set (formula σ)) ⊢
      ∀' (#0 is_inductive →' (ω ⊆' #0)) := by
  apply allI
  apply impI
  apply allI
  apply impI
  apply impE (#1 is_inductive)
  · apply hypI
    tls
  · apply allE' (#0 is_inductive →' #1 ∈' #0) #1
    apply iffE₂ (#0 ∈' ω)
    · apply hypI1
    · apply allE_var0
      apply hypI
      apply omega_ax_mem rfl
      all_goals tls
    · rfl

/-- Context-polymorphic form of `omega_subset_all_inductive`. -/
def omega_subset_all_inductive' {Γ : Set (formula σ)} (h : omega_ax ∈ Γ) :
    Γ ⊢ ∀' (#0 is_inductive →' (ω ⊆' #0)) :=
  weak_singleton omega_ax omega_subset_all_inductive h

/-- The primitive `ω` is inductive. -/
def omega_inductive : ({omega_ax} : Set (formula σ)) ⊢ ω is_inductive := by
  apply andI
  · apply impE (∀' (#0 is_inductive →' ⌀ ∈' #0))
    · apply allI
      apply impI
      apply andE₁
      apply hypI
      tls
    · apply iffE_l
      apply allE' _ ⌀
      apply hypI
      apply omega_ax_mem rfl
      all_goals tls
  · apply allI
    apply impI
    apply impE (∀' (#0 is_inductive →' S #1 ∈' #0))
    · apply allI
      apply impI
      apply impE (#1 ∈' #0)
      · apply impE (#1 ∈' ω)
        · apply hypI
          tls
        · apply allE' (#0 ∈' ω →' #0 ∈' #1) #1
          apply impE_insert
          apply allE_var0
          apply omega_subset_all_inductive'
          · tls
          · rfl
      · apply allE' (#0 ∈' #1 →' S #0 ∈' #1) #1
        apply andE₂
        apply hypI1
        tls
    · apply iffE_l
      apply allE' _ (S #0)
      apply hypI
      apply omega_ax_mem rfl
      all_goals tls

/-- Context-polymorphic form of `omega_inductive`. -/
def omega_inductive' {Γ : Set (formula σ)} (h : omega_ax ∈ Γ) :
    Γ ⊢ ω is_inductive := weak_singleton omega_ax omega_inductive h

/-- `ω` is inductive and is contained in every inductive set. -/
def omega_smallest_inductive : izf_ax ⊢
    (ω is_inductive) ∧' ∀' (#0 is_inductive →' ω ⊆' #0) := by
  apply andI
  · apply omega_inductive'
    simp [izf_ax]
  · apply omega_subset_all_inductive'
    simp [izf_ax]

end izf_proofs

/-- IZF proves that `ω` is the smallest inductive set. -/
theorem omega_smallest_inductive_provable :
    ((ω is_inductive) ∧' ∀' (#0 is_inductive →' ω ⊆' #0))
      is_provable_within izf_ax :=
  ⟨omega_smallest_inductive⟩

end izf
