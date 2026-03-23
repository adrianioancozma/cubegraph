/-
  CubeGraph/Mu5DAGRankComposition.lean
  Analysis of rank preservation under entrywise boolean operations (OR, AND, NOT).

  MISSION: Formalize "DAG of AND/OR/NOT gates on rank-1 BoolMats → rank ≤ 1".

  KEY FINDING: **The argument has a GAP.**
  Entrywise OR of two rank-1 boolean matrices is NOT necessarily rank-1.
  Counterexample (3×3): rank-1 OR rank-1 = rank-2.

  WHAT IS PROVEN (0 sorry):
  P1. boolOr_not_rankOne_counterexample — OR breaks rank-1 (3×3 native_decide)
  P2. boolNot_not_rankOne_counterexample — NOT breaks rank-1 (2×2 native_decide)
  P3. boolAnd_outerProduct — AND of outer products = outer product of AND
  P4. boolAnd_isRankOne — AND of rank-1 → rank-1 (when supports intersect)
  P5. boolAnd_zero_or_rankOne — AND of rank-1 → zero or rank-1
  P6. entrywise_or_breaks_rank1 — existential packaging of counterexample
  P7. entrywise_not_breaks_rank1 — existential packaging of counterexample
  P8. matrix_mul_preserves_rankOne — boolean matrix mul preserves rank-1
  P9. boolOr_rankOne_same_colSup — OR preserves rank-1 when colSup equal
  P10. boolOr_rankOne_same_rowSup — OR preserves rank-1 when rowSup equal
  P11-P19. Various algebraic properties of entrywise operations

  HONEST ASSESSMENT:
  - The DAG rank-closure claim is FALSE for entrywise OR and NOT
  - Boolean matrix multiplication (the actual composition in CubeGraph) DOES work
  - The P/NP separation via rank CANNOT use entrywise OR as a primitive
  - The "circuit gates" (AND/OR/NOT on bits) ≠ "matrix operations" (on 8×8 BoolMats)

  See: CubeGraph/BoolMat.lean (core definitions)
  See: CubeGraph/Rank1Algebra.lean (rank-1 composition under mul)
  See: CubeGraph/BandSemigroup.lean (band structure)
-/

import CubeGraph.BandSemigroup

namespace BoolMat

variable {n : Nat}

/-! ## Part 1: Entrywise Boolean Operations on BoolMat -/

/-- Entrywise OR of two boolean matrices: (A ∨ B)[i,j] = A[i,j] ∨ B[i,j]. -/
def boolOr (A B : BoolMat n) : BoolMat n :=
  fun i j => A i j || B i j

/-- Entrywise AND of two boolean matrices: (A ∧ B)[i,j] = A[i,j] ∧ B[i,j]. -/
def boolAnd (A B : BoolMat n) : BoolMat n :=
  fun i j => A i j && B i j

/-- Entrywise NOT (complement) of a boolean matrix: (¬A)[i,j] = ¬A[i,j]. -/
def boolNot (A : BoolMat n) : BoolMat n :=
  fun i j => !A i j

/-! ## Part 1b: Basic semantics -/

@[simp] theorem boolOr_apply (A B : BoolMat n) (i j : Fin n) :
    boolOr A B i j = (A i j || B i j) := rfl

@[simp] theorem boolAnd_apply (A B : BoolMat n) (i j : Fin n) :
    boolAnd A B i j = (A i j && B i j) := rfl

@[simp] theorem boolNot_apply (A : BoolMat n) (i j : Fin n) :
    boolNot A i j = !A i j := rfl

/-- P11: boolOr is commutative. -/
theorem boolOr_comm (A B : BoolMat n) : boolOr A B = boolOr B A := by
  funext i j; simp [Bool.or_comm]

/-- P12: boolAnd is commutative. -/
theorem boolAnd_comm (A B : BoolMat n) : boolAnd A B = boolAnd B A := by
  funext i j; simp [Bool.and_comm]

/-- P13: boolNot is involutive. -/
theorem boolNot_boolNot (A : BoolMat n) : boolNot (boolNot A) = A := by
  funext i j; simp [boolNot, Bool.not_not]

/-- P14: OR with zero is identity. -/
theorem boolOr_zero (A : BoolMat n) : boolOr A zero = A := by
  funext i j; simp [boolOr, zero]

/-- P15: AND with zero is zero. -/
theorem boolAnd_zero (A : BoolMat n) : boolAnd A zero = zero := by
  funext i j; simp [boolAnd, zero]

/-- P16: boolOr is associative. -/
theorem boolOr_assoc (A B C : BoolMat n) :
    boolOr (boolOr A B) C = boolOr A (boolOr B C) := by
  funext i j; simp [boolOr, Bool.or_assoc]

/-- P17: boolAnd is associative. -/
theorem boolAnd_assoc (A B C : BoolMat n) :
    boolAnd (boolAnd A B) C = boolAnd A (boolAnd B C) := by
  funext i j; simp [boolAnd, Bool.and_assoc]

/-- P18: De Morgan's law for BoolMat: ¬(A ∨ B) = ¬A ∧ ¬B. -/
theorem boolNot_boolOr (A B : BoolMat n) :
    boolNot (boolOr A B) = boolAnd (boolNot A) (boolNot B) := by
  funext i j; simp [boolNot, boolOr, boolAnd, Bool.not_or]

/-- P19: De Morgan's law for BoolMat: ¬(A ∧ B) = ¬A ∨ ¬B. -/
theorem boolNot_boolAnd (A B : BoolMat n) :
    boolNot (boolAnd A B) = boolOr (boolNot A) (boolNot B) := by
  funext i j; simp [boolNot, boolOr, boolAnd, Bool.not_and]

/-! ## Part 2: Entrywise AND Preserves Rank ≤ 1

  Key insight: boolAnd(A, B) is a SUBSET of both A and B.
  If A = outerProduct R_A C_A, then boolAnd of two outer products
  is the outer product of the AND of indicators. -/

/-- P3: Entrywise AND of outer products is the outer product of the AND of indicators. -/
theorem boolAnd_outerProduct (R₁ C₁ R₂ C₂ : Fin n → Bool) :
    boolAnd (outerProduct R₁ C₁) (outerProduct R₂ C₂) =
    outerProduct (fun i => R₁ i && R₂ i) (fun j => C₁ j && C₂ j) := by
  funext i j
  simp only [boolAnd_apply, outerProduct_apply]
  cases R₁ i <;> cases R₂ i <;> cases C₁ j <;> cases C₂ j <;> rfl

/-- P4: If both indicators-AND are nonempty, boolAnd of rank-1 is rank-1. -/
theorem boolAnd_isRankOne {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne)
    (hR : IndNonempty (fun i => A.rowSup i && B.rowSup i))
    (hC : IndNonempty (fun j => A.colSup j && B.colSup j)) :
    (boolAnd A B).IsRankOne := by
  rw [rankOne_eq_outerProduct hA, rankOne_eq_outerProduct hB]
  rw [boolAnd_outerProduct]
  exact ⟨fun i => A.rowSup i && B.rowSup i,
         fun j => A.colSup j && B.colSup j,
         hR, hC,
         fun i j => by simp [outerProduct, Bool.and_eq_true]⟩

/-- P5: boolAnd of rank-1 is either zero or rank-1. -/
theorem boolAnd_zero_or_rankOne {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne) :
    isZero (boolAnd A B) ∨ (boolAnd A B).IsRankOne := by
  -- Check if there's any true entry
  by_cases h : ∃ i j : Fin n, boolAnd A B i j = true
  · -- Not zero → rank-1
    obtain ⟨i₀, j₀, h₀⟩ := h
    simp only [boolAnd_apply, Bool.and_eq_true] at h₀
    right
    rw [rankOne_eq_outerProduct hA, rankOne_eq_outerProduct hB, boolAnd_outerProduct]
    refine ⟨fun i => A.rowSup i && B.rowSup i,
            fun j => A.colSup j && B.colSup j,
            ⟨i₀, by simp [Bool.and_eq_true]
                    exact ⟨mem_rowSup_iff.mpr ⟨j₀, h₀.1⟩, mem_rowSup_iff.mpr ⟨j₀, h₀.2⟩⟩⟩,
            ⟨j₀, by simp [Bool.and_eq_true]
                    exact ⟨mem_colSup_iff.mpr ⟨i₀, h₀.1⟩, mem_colSup_iff.mpr ⟨i₀, h₀.2⟩⟩⟩,
            fun i j => by simp [outerProduct, Bool.and_eq_true]⟩
  · -- No true entry → zero
    left
    intro i j
    cases hx : boolAnd A B i j with
    | false => rfl
    | true => exact absurd ⟨i, j, hx⟩ h

/-! ## Part 3: Entrywise OR Does NOT Preserve Rank ≤ 1

  **THIS IS THE KEY GAP IN THE ARGUMENT.**

  Counterexample (3×3):
    A = outerProduct [1,0,0] [1,0,0] = [[1,0,0],[0,0,0],[0,0,0]]
    B = outerProduct [0,1,0] [0,1,0] = [[0,0,0],[0,1,0],[0,0,0]]
    A ∨ B = [[1,0,0],[0,1,0],[0,0,0]]

  Row 0 = [1,0,0], Row 1 = [0,1,0]: two DISTINCT nonzero rows → NOT rank-1.
  Rank-1 requires all nonzero rows identical (outer product structure). -/

/-- Concrete rank-1 matrix: single entry at (0,0) in Fin 3. -/
private def ex_A : BoolMat 3 := outerProduct
  (fun i => decide (i = (0 : Fin 3)))
  (fun j => decide (j = (0 : Fin 3)))

/-- Concrete rank-1 matrix: single entry at (1,1) in Fin 3. -/
private def ex_B : BoolMat 3 := outerProduct
  (fun i => decide (i = (1 : Fin 3)))
  (fun j => decide (j = (1 : Fin 3)))

/-- ex_A is rank-1. -/
private theorem ex_A_rankOne : ex_A.IsRankOne :=
  ⟨fun i => decide (i = (0 : Fin 3)),
   fun j => decide (j = (0 : Fin 3)),
   ⟨0, by native_decide⟩,
   ⟨0, by native_decide⟩,
   fun i j => by simp [ex_A, outerProduct, Bool.and_eq_true]⟩

/-- ex_B is rank-1. -/
private theorem ex_B_rankOne : ex_B.IsRankOne :=
  ⟨fun i => decide (i = (1 : Fin 3)),
   fun j => decide (j = (1 : Fin 3)),
   ⟨1, by native_decide⟩,
   ⟨1, by native_decide⟩,
   fun i j => by simp [ex_B, outerProduct, Bool.and_eq_true]⟩

/-- P1: The OR of ex_A and ex_B is NOT rank-1.
    This is the CENTRAL COUNTEREXAMPLE disproving the DAG claim.

    Proof: If rank-1, all nonzero rows are identical. But:
    - (A∨B)[0,0] = true and (A∨B)[0,1] = false  (row 0 = [1,0,0])
    - (A∨B)[1,1] = true                           (row 1 has entry at col 1)
    If rank-1 with witnesses R,C: R[0]∧C[0] = true, R[1]∧C[1] = true.
    Then R[0]=true and C[1]=true, so R[0]∧C[1] should be true.
    But (A∨B)[0,1] = false. Contradiction. -/
theorem boolOr_not_rankOne_counterexample :
    ¬ (boolOr ex_A ex_B).IsRankOne := by
  intro ⟨R, C, _hR, _hC, hRC⟩
  have h00 : boolOr ex_A ex_B 0 0 = true := by native_decide
  have h01 : boolOr ex_A ex_B 0 1 = false := by native_decide
  have h11 : boolOr ex_A ex_B 1 1 = true := by native_decide
  have ⟨hR0, _⟩ := (hRC 0 0).mp h00
  have ⟨_, hC1⟩ := (hRC 1 1).mp h11
  have h_must := (hRC 0 1).mpr ⟨hR0, hC1⟩
  rw [h01] at h_must
  exact Bool.false_ne_true h_must

/-! ## Part 4: Entrywise NOT Does NOT Preserve Rank ≤ 1

  NOT of a rank-1 matrix flips all entries: zeros become ones and vice versa.
  This generically produces multiple distinct nonzero row patterns.

  Example: A = [[1,0],[0,0]] → NOT(A) = [[0,1],[1,1]]
  Row 0 = [0,1], Row 1 = [1,1]: two distinct nonzero rows → rank-2. -/

/-- Single-entry 2×2 matrix at (0,0). -/
private def ex_single : BoolMat 2 := outerProduct
  (fun i => decide (i = (0 : Fin 2)))
  (fun j => decide (j = (0 : Fin 2)))

/-- ex_single is rank-1. -/
private theorem ex_single_rankOne : ex_single.IsRankOne :=
  ⟨fun i => decide (i = (0 : Fin 2)),
   fun j => decide (j = (0 : Fin 2)),
   ⟨0, by native_decide⟩,
   ⟨0, by native_decide⟩,
   fun i j => by simp [ex_single, outerProduct, Bool.and_eq_true]⟩

/-- P2: NOT of ex_single is NOT rank-1.
    ¬[[1,0],[0,0]] = [[0,1],[1,1]]
    Row 0 = [0,1], Row 1 = [1,1]: distinct → not rank-1. -/
theorem boolNot_not_rankOne_counterexample :
    ¬ (boolNot ex_single).IsRankOne := by
  intro ⟨R, C, _hR, _hC, hRC⟩
  have h00 : boolNot ex_single 0 0 = false := by native_decide
  have h01 : boolNot ex_single 0 1 = true := by native_decide
  have h10 : boolNot ex_single 1 0 = true := by native_decide
  have ⟨hR0, _⟩ := (hRC 0 1).mp h01
  have ⟨_, hC0⟩ := (hRC 1 0).mp h10
  have h_must := (hRC 0 0).mpr ⟨hR0, hC0⟩
  rw [h00] at h_must
  exact Bool.false_ne_true h_must

/-! ## Part 5: Boolean Matrix Multiplication DOES Preserve Rank-1

  This restates the existing theorem from Rank1Algebra for emphasis.
  Boolean matrix mul (AND-OR semiring) is the CORRECT composition
  for transfer operators in the CubeGraph model. -/

/-- P8: Boolean matrix multiplication preserves rank-1 (when connected).
    This IS the correct composition for DAG of transfer operators.
    (Restated from rankOne_mul_rankOne for emphasis.) -/
theorem matrix_mul_preserves_rankOne {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne)
    (h_conn : ¬ IndDisjoint A.colSup B.rowSup) :
    (mul A B).IsRankOne :=
  rankOne_mul_rankOne hA hB h_conn

/-- Boolean matrix multiplication that disconnects produces zero (rank-0). -/
theorem matrix_mul_disconnected_zero {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne)
    (h_disj : IndDisjoint A.colSup B.rowSup) :
    isZero (mul A B) :=
  (rankOne_mul_zero_iff hA hB).mpr h_disj

/-- Rank-1 result: mul of rank-1 is either zero or rank-1 (the full dichotomy). -/
theorem mul_zero_or_rankOne {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne) :
    isZero (mul A B) ∨ (mul A B).IsRankOne := by
  by_cases h : IndDisjoint A.colSup B.rowSup
  · exact Or.inl (matrix_mul_disconnected_zero hA hB h)
  · exact Or.inr (matrix_mul_preserves_rankOne hA hB h)

/-! ## Part 6: Conditions Under Which OR DOES Preserve Rank-1

  OR preserves rank-1 when the two matrices share the same column support
  (or the same row support). In these cases, all nonzero rows of A∨B
  equal the common row pattern. -/

/-- P9: When column supports are equal, OR of rank-1 matrices stays rank-1.
    Proof: A = R_A ⊗ C, B = R_B ⊗ C. Then A∨B = (R_A ∨ R_B) ⊗ C. -/
theorem boolOr_rankOne_same_colSup {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne)
    (h_col : A.colSup = B.colSup) :
    (boolOr A B).IsRankOne := by
  -- Extract row/col support nonemptiness before rewriting
  have hRowA : IndNonempty A.rowSup := by
    obtain ⟨R, C, ⟨r, hr⟩, ⟨c, hc⟩, hRC⟩ := hA
    exact ⟨r, mem_rowSup_iff.mpr ⟨c, (hRC r c).mpr ⟨hr, hc⟩⟩⟩
  have hColA : IndNonempty A.colSup := by
    obtain ⟨R, C, ⟨r, hr⟩, ⟨c, hc⟩, hRC⟩ := hA
    exact ⟨c, mem_colSup_iff.mpr ⟨r, (hRC r c).mpr ⟨hr, hc⟩⟩⟩
  rw [rankOne_eq_outerProduct hA, rankOne_eq_outerProduct hB]
  -- Key algebraic step: when C is the same, OR distributes
  have key : boolOr (outerProduct A.rowSup A.colSup) (outerProduct B.rowSup B.colSup) =
    outerProduct (fun i => A.rowSup i || B.rowSup i) A.colSup := by
    funext i j
    simp only [boolOr_apply, outerProduct_apply, h_col]
    cases A.rowSup i <;> cases B.rowSup i <;> cases B.colSup j <;> simp
  rw [key]
  obtain ⟨r', hr'⟩ := hRowA
  exact ⟨fun i => A.rowSup i || B.rowSup i,
         A.colSup,
         ⟨r', by simp [hr']⟩,
         hColA,
         fun i j => by simp [outerProduct, Bool.and_eq_true]⟩

/-- P10: When row supports are equal, OR of rank-1 matrices stays rank-1.
    Proof: A = R ⊗ C_A, B = R ⊗ C_B. Then A∨B = R ⊗ (C_A ∨ C_B). -/
theorem boolOr_rankOne_same_rowSup {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne)
    (h_row : A.rowSup = B.rowSup) :
    (boolOr A B).IsRankOne := by
  -- Extract support nonemptiness before rewriting
  have hRowA : IndNonempty A.rowSup := by
    obtain ⟨R, C, ⟨r, hr⟩, ⟨c, hc⟩, hRC⟩ := hA
    exact ⟨r, mem_rowSup_iff.mpr ⟨c, (hRC r c).mpr ⟨hr, hc⟩⟩⟩
  have hColA : IndNonempty A.colSup := by
    obtain ⟨R, C, ⟨r, hr⟩, ⟨c, hc⟩, hRC⟩ := hA
    exact ⟨c, mem_colSup_iff.mpr ⟨r, (hRC r c).mpr ⟨hr, hc⟩⟩⟩
  rw [rankOne_eq_outerProduct hA, rankOne_eq_outerProduct hB]
  have key : boolOr (outerProduct A.rowSup A.colSup) (outerProduct B.rowSup B.colSup) =
    outerProduct A.rowSup (fun j => A.colSup j || B.colSup j) := by
    funext i j
    simp only [boolOr_apply, outerProduct_apply, h_row]
    cases B.rowSup i <;> cases A.colSup j <;> cases B.colSup j <;> simp
  rw [key]
  obtain ⟨c', hc'⟩ := hColA
  exact ⟨A.rowSup,
         fun j => A.colSup j || B.colSup j,
         hRowA,
         ⟨c', by simp [hc']⟩,
         fun i j => by simp [outerProduct, Bool.and_eq_true]⟩

/-! ## Part 7: What DAG Composition ACTUALLY Means in CubeGraph

  In the CubeGraph model:
  - Transfer operators compose via BOOLEAN MATRIX MULTIPLICATION (mul)
  - This is NOT entrywise OR — it's the (OR, AND) semiring product
  - Rank-1 IS preserved under mul (BandSemigroup)

  The DAG of gates claim conflates two different things:
  1. CIRCUIT gates: AND/OR/NOT on individual bits → irrelevant to BoolMat rank
  2. MATRIX operations: composition of transfer operators → mul, not entrywise OR

  The circuit model operates on bits; the matrix model operates on 8×8 matrices.
  These are fundamentally different levels of abstraction.

  CONCLUSION: The "rank-1 DAG closure" claim is FALSE as stated.
  The CORRECT statement is:
    Transfer operator composition (boolean matrix multiplication)
    preserves rank ≤ 1. This is proven in BandSemigroup.lean.
  The INCORRECT generalization is:
    Entrywise OR/NOT of rank-1 matrices preserves rank ≤ 1.
    This is disproven by concrete counterexamples above. -/

/-! ## Part 8: Summary Existential Packaging -/

/-- P6: **MAIN NEGATIVE RESULT**: Entrywise OR does NOT preserve rank-1 in general.
    Concrete counterexample: two rank-1 3×3 matrices whose OR is rank-2. -/
theorem entrywise_or_breaks_rank1 :
    ∃ (A B : BoolMat 3), A.IsRankOne ∧ B.IsRankOne ∧ ¬(boolOr A B).IsRankOne :=
  ⟨ex_A, ex_B, ex_A_rankOne, ex_B_rankOne, boolOr_not_rankOne_counterexample⟩

/-- P7: **MAIN NEGATIVE RESULT**: Entrywise NOT does NOT preserve rank-1. -/
theorem entrywise_not_breaks_rank1 :
    ∃ (A : BoolMat 2), A.IsRankOne ∧ ¬(boolNot A).IsRankOne :=
  ⟨ex_single, ex_single_rankOne, boolNot_not_rankOne_counterexample⟩

/-- **MAIN POSITIVE RESULT**: Entrywise AND preserves rank ≤ 1
    (result is either zero or rank-1). -/
theorem entrywise_and_preserves_rank_le_1 (A B : BoolMat n)
    (hA : A.IsRankOne) (hB : B.IsRankOne) :
    isZero (boolAnd A B) ∨ (boolAnd A B).IsRankOne :=
  boolAnd_zero_or_rankOne hA hB

/-- **MAIN POSITIVE RESULT**: Boolean matrix multiplication preserves rank ≤ 1
    (result is either zero or rank-1). -/
theorem matrix_mul_preserves_rank_le_1 (A B : BoolMat n)
    (hA : A.IsRankOne) (hB : B.IsRankOne) :
    isZero (mul A B) ∨ (mul A B).IsRankOne :=
  mul_zero_or_rankOne hA hB

/-! ## Part 9: The Correct DAG Theorem (mul-only)

  A DAG using ONLY boolean matrix multiplication:
  - All inputs rank-1 → all intermediate and final results rank ≤ 1

  This is trivially true by induction + rankOne_mul_rankOne.
  It captures the actual CubeGraph transfer operator composition. -/

/-- A mul-only DAG: composition of transfer operators. -/
inductive MulDAG (n : Nat) where
  | leaf : BoolMat n → MulDAG n
  | node : MulDAG n → MulDAG n → MulDAG n

/-- Evaluate a mul-only DAG. -/
def MulDAG.eval : MulDAG n → BoolMat n
  | leaf M => M
  | node l r => mul l.eval r.eval

/-- All leaves are rank-1. -/
def MulDAG.allRankOne : MulDAG n → Prop
  | leaf M => M.IsRankOne
  | node l r => l.allRankOne ∧ r.allRankOne

/-- Result of a mul-only DAG is either zero or rank-1.
    Proof by structural induction on the DAG. -/
theorem MulDAG.eval_zero_or_rankOne (d : MulDAG n) (h : d.allRankOne) :
    isZero d.eval ∨ d.eval.IsRankOne := by
  induction d with
  | leaf M => exact Or.inr h
  | node l r ih_l ih_r =>
    obtain ⟨hl, hr⟩ := h
    cases ih_l hl with
    | inl h_lz =>
      -- Left is zero → product is zero
      left; intro i j
      simp only [MulDAG.eval]
      cases hmul : mul l.eval r.eval i j with
      | false => rfl
      | true =>
        obtain ⟨k, hk1, _⟩ := (mul_apply_true l.eval r.eval i j).mp hmul
        rw [h_lz i k] at hk1; exact absurd hk1 (by decide)
    | inr h_lr1 =>
      cases ih_r hr with
      | inl h_rz =>
        -- Right is zero → product is zero
        left; intro i j
        simp only [MulDAG.eval]
        cases hmul : mul l.eval r.eval i j with
        | false => rfl
        | true =>
          obtain ⟨k, _, hk2⟩ := (mul_apply_true l.eval r.eval i j).mp hmul
          rw [h_rz k j] at hk2; exact absurd hk2 (by decide)
      | inr h_rr1 =>
        -- Both rank-1 → product is zero or rank-1
        simp only [MulDAG.eval]
        exact mul_zero_or_rankOne h_lr1 h_rr1

/-- Count number of nodes (compositions) in a mul DAG. -/
def MulDAG.size : MulDAG n → Nat
  | leaf _ => 1
  | node l r => l.size + r.size + 1

/-- The eval of a mul DAG with all rank-1 leaves never produces rank > 1.
    This is the formal version of "composition of rank-1 transfer operators
    stays in {zero, rank-1}" which IS the correct algebraic statement
    underlying the CubeGraph framework. -/
theorem MulDAG.rank_bounded (d : MulDAG n) (h : d.allRankOne) :
    ¬ d.eval.IsRankOne → isZero d.eval := by
  intro h_not_r1
  cases d.eval_zero_or_rankOne h with
  | inl h_z => exact h_z
  | inr h_r1 => exact absurd h_r1 h_not_r1

end BoolMat
