/-
  CubeGraph/FregeModel.lean — Frege Proof System Model

  A self-contained formalization of propositional logic and the Frege proof system,
  with soundness proven from scratch (0 unproven axioms).

  Structure:
  1. Propositional formulas
  2. Evaluation / semantics
  3. Lukasiewicz axiom schemas + soundness
  4. Modus ponens soundness
  5. Frege derivations (inductive predicate)
  6. Soundness theorem
  7. Size and depth measures
  8. 3-CNF representation and connection to CubeGraph

  References:
  - Lukasiewicz, J. "Elementy logiki matematycznej." 1929.
  - Cook, S.A. "Feasibly constructive proofs..." 1975.
  - Krajicek, J. "Bounded Arithmetic, Propositional Logic, and Complexity Theory." 1995.
-/

import CubeGraph.Basic

namespace CubeGraph

/-! ## Section 1: Propositional Formulas -/

/-- Propositional formulas over variables indexed by Fin n. -/
inductive PF (n : Nat) where
  | var : Fin n → PF n
  | fls : PF n
  | neg : PF n → PF n
  | imp : PF n → PF n → PF n
  deriving DecidableEq, Repr

namespace PF

variable {n : Nat}

/-- Disjunction: A OR B := (NEG A) IMP B -/
def disj (A B : PF n) : PF n := imp (neg A) B

/-- Conjunction: A AND B := NEG(A IMP NEG B) -/
def conj (A B : PF n) : PF n := neg (imp A (neg B))

/-- Verum := NEG falsum -/
def tru : PF n := neg fls

/-! ## Section 2: Evaluation -/

/-- An assignment maps each variable to Bool -/
abbrev PAssign (n : Nat) := Fin n → Bool

/-- Evaluate a formula under an assignment -/
def eval (σ : PAssign n) : PF n → Bool
  | var i => σ i
  | fls => false
  | neg A => !eval σ A
  | imp A B => !eval σ A || eval σ B

@[simp] theorem eval_var (σ : PAssign n) (i : Fin n) : eval σ (var i) = σ i := rfl
@[simp] theorem eval_fls (σ : PAssign n) : eval σ fls = false := rfl
@[simp] theorem eval_neg (σ : PAssign n) (A : PF n) : eval σ (neg A) = !eval σ A := rfl
@[simp] theorem eval_imp (σ : PAssign n) (A B : PF n) :
    eval σ (imp A B) = (!eval σ A || eval σ B) := rfl

/-- A formula is a tautology -/
def IsTautology (A : PF n) : Prop :=
  ∀ σ : PAssign n, eval σ A = true

/-- A list of formulas is unsatisfiable -/
def IsUnsat (Γ : List (PF n)) : Prop :=
  ¬ ∃ σ : PAssign n, ∀ B ∈ Γ, eval σ B = true

/-! ## Section 3: Lukasiewicz Axiom Schemas -/

def axK (A B : PF n) : PF n := imp A (imp B A)

def axS (A B C : PF n) : PF n :=
  imp (imp A (imp B C)) (imp (imp A B) (imp A C))

def axContra (A B : PF n) : PF n :=
  imp (imp (neg B) (neg A)) (imp A B)

inductive IsAxiom : PF n → Prop where
  | K : (A B : PF n) → IsAxiom (axK A B)
  | S : (A B C : PF n) → IsAxiom (axS A B C)
  | Contra : (A B : PF n) → IsAxiom (axContra A B)

theorem axK_taut (A B : PF n) : IsTautology (axK A B) := by
  intro σ; simp [axK, eval]; cases eval σ A <;> simp

theorem axS_taut (A B C : PF n) : IsTautology (axS A B C) := by
  intro σ; simp [axS, eval]
  cases eval σ A <;> cases eval σ B <;> cases eval σ C <;> simp

theorem axContra_taut (A B : PF n) : IsTautology (axContra A B) := by
  intro σ; simp [axContra, eval]; cases eval σ A <;> cases eval σ B <;> simp

theorem axiom_taut {A : PF n} (h : IsAxiom A) : IsTautology A := by
  cases h with
  | K A B => exact axK_taut A B
  | S A B C => exact axS_taut A B C
  | Contra A B => exact axContra_taut A B

/-! ## Section 4: Modus Ponens -/

theorem mp_sound (σ : PAssign n) (A B : PF n)
    (hA : eval σ A = true) (hAB : eval σ (imp A B) = true) :
    eval σ B = true := by
  simp at hAB; cases eval σ A <;> simp_all

/-! ## Section 5: Frege Derivations

We model Frege proofs via an inductive predicate `Derives Gamma lines`
stating that `lines` is a valid derivation from hypotheses `Gamma`. -/

/-- A valid Frege derivation from hypotheses Gamma.
    Each step extends the proof by one formula, justified by:
    - An axiom schema instance
    - A hypothesis from Gamma
    - Modus ponens from two formulas already in the proof -/
inductive Derives (Γ : List (PF n)) : List (PF n) → Prop where
  | nil : Derives Γ []
  | axiom_step (prev : List (PF n)) (A : PF n)
      (h_prev : Derives Γ prev)
      (h_ax : IsAxiom A) :
      Derives Γ (prev ++ [A])
  | hyp_step (prev : List (PF n)) (A : PF n)
      (h_prev : Derives Γ prev)
      (h_hyp : A ∈ Γ) :
      Derives Γ (prev ++ [A])
  | mp_step (prev : List (PF n)) (A B : PF n)
      (h_prev : Derives Γ prev)
      (h_A : A ∈ prev)
      (h_AB : imp A B ∈ prev) :
      Derives Γ (prev ++ [B])

/-! ## Section 6: Soundness -/

/-- Every formula in a valid derivation evaluates to true
    under any assignment satisfying all hypotheses. -/
theorem derives_sound (Γ : List (PF n)) (lines : List (PF n))
    (h_der : Derives Γ lines)
    (σ : PAssign n) (h_hyps : ∀ B ∈ Γ, eval σ B = true) :
    ∀ A ∈ lines, eval σ A = true := by
  induction h_der with
  | nil => intro A hA; simp at hA
  | axiom_step _ A _ h_ax ih =>
    intro B hB
    simp at hB
    cases hB with
    | inl hB => exact ih B hB
    | inr hB => rw [hB]; exact axiom_taut h_ax σ
  | hyp_step _ A _ h_hyp ih =>
    intro B hB
    simp at hB
    cases hB with
    | inl hB => exact ih B hB
    | inr hB => rw [hB]; exact h_hyps A h_hyp
  | mp_step _ A B _ h_A h_AB ih =>
    intro C hC
    simp at hC
    cases hC with
    | inl hC => exact ih C hC
    | inr hC =>
      rw [hC]
      exact mp_sound σ A B (ih A h_A) (ih (imp A B) h_AB)

/-- Gamma can derive falsum -/
def FregeRefutes (Γ : List (PF n)) : Prop :=
  ∃ lines : List (PF n), Derives Γ lines ∧ fls ∈ lines

/-- **SOUNDNESS THEOREM**: If Gamma can derive falsum, then Gamma is unsatisfiable. -/
theorem frege_sound {Γ : List (PF n)} (h : FregeRefutes Γ) : IsUnsat Γ := by
  obtain ⟨lines, h_der, h_fls⟩ := h
  intro ⟨σ, h_sat⟩
  have h_all := derives_sound Γ lines h_der σ h_sat
  have := h_all fls h_fls
  simp at this

/-! ## Section 7: Size and Depth -/

/-- Depth of a formula -/
def depth : PF n → Nat
  | var _ => 0
  | fls => 0
  | neg A => 1 + depth A
  | imp A B => 1 + max (depth A) (depth B)

/-- Size of a formula (subformula count) -/
def pfSize : PF n → Nat
  | var _ => 1
  | fls => 1
  | neg A => 1 + pfSize A
  | imp A B => 1 + pfSize A + pfSize B

/-- Size is at least 1 -/
theorem pfSize_pos (A : PF n) : pfSize A ≥ 1 := by
  cases A <;> simp [pfSize] <;> omega

/-- Depth is zero for atoms -/
theorem depth_var (i : Fin n) : depth (var i : PF n) = 0 := rfl
theorem depth_fls : depth (fls : PF n) = 0 := rfl

/-! ## Section 8: Explicit Proof Structure (for proof complexity measures) -/

/-- An explicit Frege proof with hypotheses and a derivation -/
structure FProof (n : Nat) where
  hyps : List (PF n)
  formulas : List (PF n)
  nonempty : formulas ≠ []
  valid : Derives hyps formulas

/-- The conclusion is the last formula -/
def FProof.conclusion (π : FProof n) : PF n :=
  π.formulas.getLast π.nonempty

/-- Total proof size -/
def FProof.totalSize (π : FProof n) : Nat :=
  π.formulas.foldl (fun acc f => acc + pfSize f) 0

/-- Maximum formula depth -/
def FProof.maxDepth (π : FProof n) : Nat :=
  π.formulas.foldl (fun acc f => max acc (depth f)) 0

/-- Number of lines -/
def FProof.lineCount (π : FProof n) : Nat := π.formulas.length

/-- An explicit Frege refutation -/
structure FRefutation (n : Nat) where
  proof : FProof n
  concludes_fls : fls ∈ proof.formulas

/-- Soundness for the explicit structure -/
theorem frefutation_sound (ref : FRefutation n) : IsUnsat ref.proof.hyps :=
  frege_sound ⟨ref.proof.formulas, ref.proof.valid, ref.concludes_fls⟩

/-! ## Section 9: 3-CNF Representation -/

/-- A literal: variable index + polarity -/
structure PLit (n : Nat) where
  idx : Fin n
  pos : Bool
  deriving DecidableEq

/-- Convert literal to formula -/
def PLit.toForm (l : PLit n) : PF n :=
  if l.pos then PF.var l.idx else PF.neg (PF.var l.idx)

/-- A 3-literal clause -/
structure Cl3 (n : Nat) where
  l₁ : PLit n
  l₂ : PLit n
  l₃ : PLit n
  deriving DecidableEq

/-- Convert 3-clause to formula: l1 OR l2 OR l3 -/
def Cl3.toForm (cl : Cl3 n) : PF n :=
  disj (disj cl.l₁.toForm cl.l₂.toForm) cl.l₃.toForm

/-- A 3-CNF formula -/
structure CNF3 (n : Nat) where
  clauses : List (Cl3 n)

/-- Convert to list of formulas -/
def CNF3.toForms (φ : CNF3 n) : List (PF n) :=
  φ.clauses.map Cl3.toForm

/-- A 3-CNF is satisfiable -/
def CNF3.IsSat (φ : CNF3 n) : Prop :=
  ∃ σ : PAssign n, ∀ cl ∈ φ.clauses, eval σ (Cl3.toForm cl) = true

/-- Depth of a literal formula is at most 1 -/
theorem lit_depth_le (l : PLit n) : depth l.toForm ≤ 1 := by
  simp [PLit.toForm]; cases l.pos <;> simp [depth]

/-- Depth of a 3-clause formula is bounded by 5 -/
theorem cl3_depth_le (cl : Cl3 n) : depth cl.toForm ≤ 5 := by
  unfold Cl3.toForm disj
  simp only [depth]
  have h1 := lit_depth_le cl.l₁
  have h2 := lit_depth_le cl.l₂
  have h3 := lit_depth_le cl.l₃
  omega

/-- A 3-CNF refutation implies unsatisfiability -/
theorem cnf3_refutation_unsat (φ : CNF3 n)
    (h : FregeRefutes (φ.toForms : List (PF n))) :
    ¬ φ.IsSat := by
  intro ⟨σ, h_sat⟩
  have h_unsat := frege_sound h
  apply h_unsat
  exact ⟨σ, fun B hB => by
    simp [CNF3.toForms] at hB
    obtain ⟨cl, hcl, rfl⟩ := hB
    exact h_sat cl hcl⟩

/-! ## Section 10: Connection to CubeGraph -/

/-- Variable indices of a 3-clause -/
def Cl3.varIndices (cl : Cl3 n) : List (Fin n) :=
  [cl.l₁.idx, cl.l₂.idx, cl.l₃.idx]

/-- Number of shared variables between two 3-clauses -/
def Cl3.sharedCount (cl₁ cl₂ : Cl3 n) : Nat :=
  (cl₁.varIndices.filter (fun v => cl₂.varIndices.contains v)).length

/-- Shared variable count is at most 3 -/
theorem shared_count_le_3 (cl₁ cl₂ : Cl3 n) :
    cl₁.sharedCount cl₂ ≤ 3 := by
  simp [Cl3.sharedCount, Cl3.varIndices]
  apply List.length_filter_le

/-- Two clauses share a variable when their index sets intersect -/
def Cl3.sharesVar (cl₁ cl₂ : Cl3 n) : Prop :=
  cl₁.sharedCount cl₂ > 0

/-! ## Section 11: Evaluation of Defined Connectives -/

theorem eval_disj (σ : PAssign n) (A B : PF n) :
    eval σ (disj A B) = (eval σ A || eval σ B) := by
  simp only [disj, eval]; cases eval σ A <;> simp

theorem eval_conj (σ : PAssign n) (A B : PF n) :
    eval σ (conj A B) = (eval σ A && eval σ B) := by
  simp only [conj, eval]; cases eval σ A <;> cases eval σ B <;> simp

theorem eval_tru (σ : PAssign n) : eval σ (tru : PF n) = true := by
  simp [tru, eval]

/-! ## Section 12: Depth Properties -/

theorem depth_disj (A B : PF n) :
    depth (disj A B) = 1 + max (1 + depth A) (depth B) := by
  simp only [disj, depth]

theorem depth_conj (A B : PF n) :
    depth (conj A B) = 1 + (1 + max (depth A) (1 + depth B)) := by
  simp only [conj, depth]

/-! ## Section 13: Semantic Facts -/

/-- {x, NEG x} is unsatisfiable -/
theorem var_neg_unsat (i : Fin n) :
    IsUnsat [PF.var i, PF.neg (PF.var i)] := by
  intro ⟨σ, h⟩
  have h1 := h (PF.var i) (by simp)
  have h2 := h (PF.neg (PF.var i)) (by simp)
  simp at h1 h2; rw [h1] at h2; simp at h2

/-- {falsum} is unsatisfiable -/
theorem fls_unsat : IsUnsat [PF.fls (n := n)] := by
  intro ⟨σ, h⟩; have := h PF.fls (by simp); simp at this

/-- A 3-clause is satisfiable iff at least one literal evaluates to true -/
theorem cl3_sat_iff (cl : Cl3 n) (σ : PAssign n) :
    eval σ cl.toForm = true ↔
    (eval σ cl.l₁.toForm = true ∨ eval σ cl.l₂.toForm = true ∨
     eval σ cl.l₃.toForm = true) := by
  simp [Cl3.toForm]
  rw [eval_disj, eval_disj]
  cases eval σ cl.l₁.toForm <;> cases eval σ cl.l₂.toForm <;>
    cases eval σ cl.l₃.toForm <;> simp

/-! ## Section 14: Derivability Properties -/

/-- Weakening: if A is derivable from Gamma, and Gamma is a subset of Delta,
    then A is derivable from Delta -/
theorem derives_mono {Γ Δ : List (PF n)} {lines : List (PF n)}
    (h : Derives Γ lines) (h_sub : ∀ A ∈ Γ, A ∈ Δ) :
    Derives Δ lines := by
  induction h with
  | nil => exact Derives.nil
  | axiom_step _ A _ h_ax ih =>
    exact Derives.axiom_step _ A ih h_ax
  | hyp_step _ A _ h_hyp ih =>
    exact Derives.hyp_step _ A ih (h_sub A h_hyp)
  | mp_step _ A B _ h_A h_AB ih =>
    exact Derives.mp_step _ A B ih h_A h_AB

/-- Every hypothesis is derivable in a single step -/
theorem derives_hyp {Γ : List (PF n)} {A : PF n} (h : A ∈ Γ) :
    Derives Γ [A] := by
  have h1 : Derives Γ ([] ++ [A]) := Derives.hyp_step [] A Derives.nil h
  simpa using h1

/-- Every axiom instance is derivable in a single step -/
theorem derives_axiom {Γ : List (PF n)} {A : PF n} (h : IsAxiom A) :
    Derives Γ [A] := by
  have h1 : Derives Γ ([] ++ [A]) := Derives.axiom_step [] A Derives.nil h
  simpa using h1

end PF

end CubeGraph
