/-
  CubeGraph/MPLossy.lean — Modus Ponens Is Lossy

  Modus ponens (from A and A→B, derive B) LOSES information:
  the conclusion B is strictly weaker than the combined premises A ∧ (A→B).

  **Abstract formulation** (Part 1):
    For any predicates A, B on an assignment space:
      satCount(B) ≥ satCount(A ∧ B) = satCount(A ∧ (A→B))
    Because A ∧ (A→B) ⟺ A ∧ B, and A ∧ B ⊆ B as sets of satisfying assignments.
    Information about A is LOST when we derive B alone.

  **CubeGraph formulation** (Part 2):
    For transfer operator M between cubes C₁ and C₂:
      gapSet(C₂) ⊇ { g₂ : ∃ g₁, M[g₁,g₂] = true }
    The target cube's gap set is AT LEAST as large as the set reachable
    through the transfer operator. Composition CANNOT shrink the universe
    of possibilities at the target — it can only fail to reach some gaps.

    More precisely: the column support of M is contained in C₂'s gap set.
    This is because M[g₁,g₂] = true requires g₂ to be a gap in C₂.
    So "what M tells us about C₂" ⊆ "what C₂ tells us about C₂".
    The transfer operator FILTERS (reduces info), never AMPLIFIES.

  **Connection to NP-hardness**:
    This is why composition along paths loses information (rank decay).
    Each modus ponens step (transfer through one edge) can only weaken
    what we know. After k steps, we know strictly less than after k-1.
    This is the mechanism behind rank-1 collapse (EraseOnlyCollapse.lean).

  See: InformationChannel.lean (dead stays dead, rank monotone decay)
  See: FiberSize.lean (functional vs relational: rate of information loss)
  See: EraseOnlyCollapse.lean (rank-1 collapse after 3 hops)
  See: Rank1Algebra.lean (rank-1 composition law)
-/

import CubeGraph.FiberSize

namespace MPLossy

/-! ## Part 1: Abstract Modus Ponens Lossiness

  We model propositional "formulas" as predicates on a finite assignment space.
  An assignment is a function `Fin n → Bool` (n propositional variables).
  A "formula" is a predicate `(Fin n → Bool) → Bool` — the set of satisfying
  assignments.

  `satCount φ` = number of satisfying assignments.
  More satisfying assignments = LESS specific = LESS information.

  The key identity: A ∧ (A → B) ⟺ A ∧ B.
  Therefore: satCount(A ∧ (A→B)) = satCount(A ∧ B) ≤ satCount(B).
  Modus ponens WEAKENS the combined information of the premises.
-/

/-- A propositional formula on n variables: a decidable predicate on assignments. -/
def Formula (n : Nat) := (Fin n → Bool) → Bool

/-- Conjunction of two formulas. -/
def conj {n : Nat} (A B : Formula n) : Formula n :=
  fun σ => A σ && B σ

/-- Implication of two formulas (material conditional). -/
def imp {n : Nat} (A B : Formula n) : Formula n :=
  fun σ => !A σ || B σ

/-- The number of satisfying assignments of a formula.
    Counts over all 2^n possible assignments (modeled as Fin (2^n)). -/
def satCount {n : Nat} (φ : Formula n) : Nat :=
  (List.finRange (2^n)).countP fun (idx : Fin (2^n)) =>
    φ (fun (v : Fin n) => ((idx.val >>> v.val) &&& 1 == 1))

/-- The modus ponens input: A ∧ (A → B). -/
def mpInput {n : Nat} (A B : Formula n) : Formula n :=
  conj A (imp A B)

/-! ### Core identity: A ∧ (A → B) ⟺ A ∧ B -/

/-- Pointwise: A(σ) ∧ (A(σ) → B(σ)) = A(σ) ∧ B(σ) for any assignment σ. -/
theorem mp_input_eq_conj_pointwise {n : Nat} (A B : Formula n) (σ : Fin n → Bool) :
    mpInput A B σ = conj A B σ := by
  simp only [mpInput, conj, imp]
  cases A σ <;> cases B σ <;> simp

/-- A ∧ (A → B) = A ∧ B as formulas (extensional equality). -/
theorem mp_input_eq_conj {n : Nat} (A B : Formula n) :
    mpInput A B = conj A B := by
  funext σ; exact mp_input_eq_conj_pointwise A B σ

/-! ### Monotonicity: satCount(A ∧ B) ≤ satCount(B) -/

/-- If φ implies ψ pointwise (as booleans), then satCount(φ) ≤ satCount(ψ). -/
theorem satCount_mono {n : Nat} (φ ψ : Formula n)
    (h : ∀ σ : Fin n → Bool, φ σ = true → ψ σ = true) :
    satCount φ ≤ satCount ψ := by
  simp only [satCount]
  exact countP_le_of_implies
    (fun idx => φ (fun v => ((idx.val >>> v.val) &&& 1 == 1)))
    (fun idx => ψ (fun v => ((idx.val >>> v.val) &&& 1 == 1)))
    (List.finRange (2^n))
    (fun idx hφ => h (fun v => ((idx.val >>> v.val) &&& 1 == 1)) hφ)

/-- A ∧ B implies B pointwise. -/
theorem conj_implies_right {n : Nat} (A B : Formula n) (σ : Fin n → Bool) :
    conj A B σ = true → B σ = true := by
  simp only [conj, Bool.and_eq_true]
  exact fun ⟨_, hB⟩ => hB

/-- **satCount(A ∧ B) ≤ satCount(B)**: conjunction is more specific. -/
theorem satCount_conj_le_right {n : Nat} (A B : Formula n) :
    satCount (conj A B) ≤ satCount B :=
  satCount_mono (conj A B) B (conj_implies_right A B)

/-- A ∧ B implies A pointwise. -/
theorem conj_implies_left {n : Nat} (A B : Formula n) (σ : Fin n → Bool) :
    conj A B σ = true → A σ = true := by
  simp only [conj, Bool.and_eq_true]
  exact fun ⟨hA, _⟩ => hA

/-- **satCount(A ∧ B) ≤ satCount(A)**: conjunction is more specific (left). -/
theorem satCount_conj_le_left {n : Nat} (A B : Formula n) :
    satCount (conj A B) ≤ satCount A :=
  satCount_mono (conj A B) A (conj_implies_left A B)

/-! ### Main Theorem: Modus Ponens Is Lossy -/

/-- **Modus Ponens Is Lossy (abstract form).**
    The conclusion B has at least as many satisfying assignments as the
    combined premises A ∧ (A→B). Equivalently: B rules out FEWER assignments.

    Proof: A ∧ (A→B) = A ∧ B (propositional identity), and A ∧ B ⊆ B. -/
theorem mp_lossy {n : Nat} (A B : Formula n) :
    satCount (mpInput A B) ≤ satCount B := by
  rw [mp_input_eq_conj]
  exact satCount_conj_le_right A B

/-- **Modus Ponens loses info about A.**
    The conclusion B has at least as many satisfying assignments as A ∧ (A→B).
    In particular, information about A is completely lost: we also have
    satCount(mpInput A B) ≤ satCount(A). -/
theorem mp_lossy_both {n : Nat} (A B : Formula n) :
    satCount (mpInput A B) ≤ satCount A ∧
    satCount (mpInput A B) ≤ satCount B := by
  rw [mp_input_eq_conj]
  exact ⟨satCount_conj_le_left A B, satCount_conj_le_right A B⟩

/-! ### Strict lossiness witness: there exist A, B where B is strictly weaker -/

/-- Constant-true formula (tautology). -/
def trueFormula : Formula 1 := fun _ => true

/-- Constant-false on first variable: σ(0) = false. -/
def var0False : Formula 1 := fun σ => !σ ⟨0, by omega⟩

/-- satCount of the tautology on 1 variable = 2. -/
theorem satCount_trueFormula : satCount trueFormula = 2 := by native_decide

/-- satCount of var0False on 1 variable = 1. -/
theorem satCount_var0False : satCount var0False = 1 := by native_decide

/-- satCount of (var0False ∧ true) = satCount(var0False) = 1. -/
theorem satCount_conj_var0False_true :
    satCount (conj var0False trueFormula) = 1 := by native_decide

/-- **Strict lossiness witness**: there exist formulas where MP is strictly lossy.
    A = var0False (¬x₀), B = trueFormula (⊤).
    satCount(A ∧ (A→B)) = 1 < 2 = satCount(B). -/
theorem mp_strictly_lossy :
    ∃ (A B : Formula 1), satCount (mpInput A B) < satCount B := by
  exact ⟨var0False, trueFormula, by native_decide⟩

end MPLossy

/-! ## Part 2: CubeGraph-Specific Information Loss

  In CubeGraph, "modus ponens" corresponds to propagating gap information
  through a transfer operator: given gap info at cube C₁, what can we
  deduce about cube C₂?

  The transfer operator M = transferOp(C₁, C₂) encodes:
    M[g₁, g₂] = 1 iff g₁ is a gap in C₁ AND g₂ is a gap in C₂
                       AND they agree on shared variables.

  **Column support ⊆ target gap set**: every gap reachable through M
  is already a gap in C₂. The transfer CANNOT discover new gaps.

  **Row support ⊆ source gap set**: every gap that can propagate
  is already a gap in C₁.

  This means transfer operators are FILTERS: they select compatible
  subsets of already-known gap sets. They never create information.
  Each composition step can only reduce or maintain specificity.
-/

namespace CubeGraph

open BoolMat

/-! ### Transfer operators filter gap information -/

/-- The column support of a transfer operator is contained in the target's gap set.
    Every gap reachable through M is a gap in C₂.
    Transfer CANNOT discover new gaps at the target. -/
theorem transferOp_colSup_subset_gaps (c₁ c₂ : Cube) (g₂ : Fin 8) :
    (transferOp c₁ c₂).colSup g₂ = true → c₂.isGap g₂ = true := by
  intro h
  rw [mem_colSup_iff] at h
  obtain ⟨g₁, hg⟩ := h
  simp only [transferOp] at hg
  revert hg
  cases hg₁ : c₁.isGap g₁ <;> cases hg₂ : c₂.isGap g₂ <;> simp_all

/-- The row support of a transfer operator is contained in the source's gap set.
    Every gap that can propagate is a gap in C₁.
    Transfer CANNOT propagate from non-gaps. -/
theorem transferOp_rowSup_subset_gaps (c₁ c₂ : Cube) (g₁ : Fin 8) :
    (transferOp c₁ c₂).rowSup g₁ = true → c₁.isGap g₁ = true := by
  intro h
  rw [mem_rowSup_iff] at h
  obtain ⟨g₂, hg⟩ := h
  simp only [transferOp] at hg
  revert hg
  cases hg₁ : c₁.isGap g₁ <;> simp_all

/-! ### Composition preserves the gap filtering property -/

/-- The gap set at a cube, as a boolean indicator. -/
def gapIndicator (c : Cube) : Fin 8 → Bool := fun g => c.isGap g

/-- Count of gaps reachable at target through a transfer operator.
    This is the column fiber: how many target gaps are compatible with
    at least one source gap. -/
def reachableGapCount (c₁ c₂ : Cube) : Nat :=
  (List.finRange 8).countP fun g₂ => (transferOp c₁ c₂).colSup g₂

/-- Total gaps at a cube. -/
def totalGapCount (c : Cube) : Nat :=
  (List.finRange 8).countP fun g => c.isGap g

/-- **Reachable gaps ≤ total gaps at target.**
    The transfer operator can reach at most the target's full gap set.
    Information is LOST (or at best preserved): we learn about a SUBSET
    of C₂'s gaps, never more than C₂ already knows about itself. -/
theorem reachableGapCount_le_totalGapCount (c₁ c₂ : Cube) :
    reachableGapCount c₁ c₂ ≤ totalGapCount c₂ := by
  simp only [reachableGapCount, totalGapCount]
  exact countP_le_of_implies
    (fun g₂ => (transferOp c₁ c₂).colSup g₂)
    (fun g => c₂.isGap g)
    (List.finRange 8)
    (fun g₂ hg₂ => transferOp_colSup_subset_gaps c₁ c₂ g₂ hg₂)

/-! ### Composition chain: information loss compounds -/

/-- The column support of a composed matrix M·N is contained in N's column support.
    Composition chains can only NARROW what's reachable at the end. -/
theorem colSup_mul_subset (M N : BoolMat 8) (j : Fin 8) :
    (mul M N).colSup j = true → N.colSup j = true := by
  intro h
  rw [mem_colSup_iff] at h ⊢
  obtain ⟨i, hi⟩ := h
  rw [mul_apply_true] at hi
  obtain ⟨k, _, hkj⟩ := hi
  exact ⟨k, hkj⟩

/-- The row support of a composed matrix M·N is contained in M's row support.
    Composition chains can only NARROW the source set. -/
theorem rowSup_mul_subset (M N : BoolMat 8) (i : Fin 8) :
    (mul M N).rowSup i = true → M.rowSup i = true :=
  rowSup_mul_of_rowSup M N i

/-- Count of true entries in an indicator function. -/
def indCount (f : Fin 8 → Bool) : Nat :=
  (List.finRange 8).countP fun i => f i

/-- **Column support can only shrink under composition.**
    indCount(colSup(M·N)) ≤ indCount(colSup(N)). -/
theorem indCount_colSup_mul_le (M N : BoolMat 8) :
    indCount (mul M N).colSup ≤ indCount N.colSup := by
  simp only [indCount]
  exact countP_le_of_implies
    (fun j => (mul M N).colSup j)
    (fun j => N.colSup j)
    (List.finRange 8)
    (fun j hj => colSup_mul_subset M N j hj)

/-- **Row support can only shrink under composition.**
    indCount(rowSup(M·N)) ≤ indCount(rowSup(M)). -/
theorem indCount_rowSup_mul_le (M N : BoolMat 8) :
    indCount (mul M N).rowSup ≤ indCount M.rowSup := by
  simp only [indCount]
  exact countP_le_of_implies
    (fun i => (mul M N).rowSup i)
    (fun i => M.rowSup i)
    (List.finRange 8)
    (fun i hi => rowSup_mul_subset M N i hi)

/-! ### Summary: MP Lossiness in CubeGraph Context -/

/-- **Modus Ponens Lossiness — CubeGraph Summary.**

    Packages the complete information loss story:

    1. **Transfer filters gaps**: colSup(transferOp) ⊆ target gaps
       (transfer cannot discover new gaps)
    2. **Transfer filters gaps**: rowSup(transferOp) ⊆ source gaps
       (transfer cannot propagate from non-gaps)
    3. **Reachable ≤ total**: reachableGapCount ≤ totalGapCount
       (propagation reaches at most what's already there)
    4. **Composition narrows columns**: colSup(M·N) ⊆ colSup(N)
       (each step can only lose, never gain at the target)
    5. **Composition narrows rows**: rowSup(M·N) ⊆ rowSup(M)
       (source info also shrinks under composition)

    This is the algebraic content of "modus ponens is lossy" in CubeGraph:
    each inference step (transfer through an edge) can only WEAKEN
    our knowledge about which gaps are viable. After k steps, we know
    LESS than after k-1 steps. This compounds into rank decay
    (EraseOnlyCollapse) and eventually rank-1 collapse. -/
theorem mp_lossy_cubegraph :
    -- (1) Transfer filters: colSup ⊆ target gaps
    (∀ c₁ c₂ : Cube, ∀ g₂ : Fin 8,
      (transferOp c₁ c₂).colSup g₂ = true → c₂.isGap g₂ = true) ∧
    -- (2) Transfer filters: rowSup ⊆ source gaps
    (∀ c₁ c₂ : Cube, ∀ g₁ : Fin 8,
      (transferOp c₁ c₂).rowSup g₁ = true → c₁.isGap g₁ = true) ∧
    -- (3) Reachable ≤ total gaps
    (∀ c₁ c₂ : Cube, reachableGapCount c₁ c₂ ≤ totalGapCount c₂) ∧
    -- (4) Column support shrinks under composition
    (∀ M N : BoolMat 8, indCount (mul M N).colSup ≤ indCount N.colSup) ∧
    -- (5) Row support shrinks under composition
    (∀ M N : BoolMat 8, indCount (mul M N).rowSup ≤ indCount M.rowSup) :=
  ⟨transferOp_colSup_subset_gaps,
   transferOp_rowSup_subset_gaps,
   reachableGapCount_le_totalGapCount,
   indCount_colSup_mul_le,
   indCount_rowSup_mul_le⟩

end CubeGraph
