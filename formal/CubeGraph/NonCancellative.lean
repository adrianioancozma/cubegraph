/-
  CubeGraph/NonCancellative.lean
  Non-cancellativity and rank drop theorems for boolean matrices (BoolMat 8).

  Main theorems:
  - L1: exists_non_cancellative — ∃ A B C : BoolMat 8, B ≠ C ∧ mul A B = mul A C
  - L1': exists_right_non_cancellative — right version
  - L2: zero_col_non_cancellative — ∀ n, zero column → left-non-cancellative (GENERAL)
  - L3a: exists_rank_drop_2_to_1 — two non-zero, non-rank-1 matrices, product is rank-1
  - L3b: exists_rank_drop_2_to_0 — two non-zero matrices, product is zero

  L1/L3 use concrete 2-entry matrices from T₃* experimental data.
  L2 is a general algebraic theorem (works for any n, not just 8).

  Experimental source: experiments-ml/018_2026-03-11_negation-complexity/D2-STEP1-RESULTS.md
  - Non-cancellativity: 89% collision rate, 14.2M collisions among 79,816 operators
  - Rank drop: rank(A⊗B) is NOT a function of (rank A, rank B)

  Plan: experiments-ml/018_2026-03-11_negation-complexity/D2-LEAN-PLAN.md (L1, L2, L3)
  L2 plan: experiments-ml/018_2026-03-11_negation-complexity/L2-PLAN.md
-/

import CubeGraph.ChannelAlignment

namespace BoolMat

/-! ## Concrete witness matrices

  Extracted from T₃* elementary operators (experiments-ml/018_2026-03-11_negation-complexity/).
  Each matrix has only 2 true entries — minimal witnesses.

  ncA = {(0,1), (4,4)} — rank 2, from ops[35763]
  ncB = {(2,3), (4,4)} — rank 2, from ops[9040]
  ncC = {(0,0), (5,5)} — rank 2, from ops[35788]
-/

/-- Matrix A: entries at (0,1) and (4,4). -/
def ncA : BoolMat 8 := fun i j =>
  match i.val, j.val with
  | 0, 1 => true
  | 4, 4 => true
  | _, _ => false

/-- Matrix B: entries at (2,3) and (4,4). -/
def ncB : BoolMat 8 := fun i j =>
  match i.val, j.val with
  | 2, 3 => true
  | 4, 4 => true
  | _, _ => false

/-- Matrix C: entries at (0,0) and (5,5). Disjoint column-support from A. -/
def ncC : BoolMat 8 := fun i j =>
  match i.val, j.val with
  | 0, 0 => true
  | 5, 5 => true
  | _, _ => false

/-! ## L1: Non-Cancellativity of T₃*

  The transfer operator semigroup T₃* is non-cancellative:
  there exist A, B, C with B ≠ C but A ⊗ B = A ⊗ C.

  The concrete witness uses ncA and ncB:
  - A⊗B: only (4,4) survives (row 0 of A hits col 1, but B's row 1 is empty)
  - A⊗A: only (4,4) survives (same reason — A's row 1 is also empty)
  - So A⊗B = A⊗A = {(4,4)}, but B ≠ A.

  See: D2-STEP1-RESULTS.md §2 (Non-Cancellativity — MASIVĂ)
-/

private theorem mul_ncA_ncB_eq_mul_ncA_ncA :
    ∀ (i j : Fin 8), mul ncA ncB i j = mul ncA ncA i j := by native_decide

private theorem mul_ncB_ncA_eq_mul_ncA_ncA :
    ∀ (i j : Fin 8), mul ncB ncA i j = mul ncA ncA i j := by native_decide

/-- **L1: Non-Cancellativity Theorem**.
    T₃* is non-cancellative: ∃ A B C with B ≠ C and A⊗B = A⊗C. -/
theorem exists_non_cancellative :
    ∃ A B C : BoolMat 8, B ≠ C ∧ mul A B = mul A C := by
  refine ⟨ncA, ncB, ncA, ?_, ?_⟩
  · -- B ≠ C: ncB and ncA differ at position (2,3)
    intro h
    have : ncB ⟨2, by omega⟩ ⟨3, by omega⟩ = ncA ⟨2, by omega⟩ ⟨3, by omega⟩ :=
      congrFun (congrFun h _) _
    simp [ncB, ncA] at this
  · -- mul ncA ncB = mul ncA ncA
    funext i j; exact mul_ncA_ncB_eq_mul_ncA_ncA i j

/-- **L1': Right Non-Cancellativity**.
    ∃ A B C with B ≠ C and B⊗A = C⊗A. -/
theorem exists_right_non_cancellative :
    ∃ A B C : BoolMat 8, B ≠ C ∧ mul B A = mul C A := by
  refine ⟨ncA, ncB, ncA, ?_, ?_⟩
  · intro h
    have : ncB ⟨2, by omega⟩ ⟨3, by omega⟩ = ncA ⟨2, by omega⟩ ⟨3, by omega⟩ :=
      congrFun (congrFun h _) _
    simp [ncB, ncA] at this
  · funext i j; exact mul_ncB_ncA_eq_mul_ncA_ncA i j

/-! ## L3: Rank Drop Under Multiplication

  rank(A ⊗ B) is NOT a function of (rank A, rank B).
  We demonstrate:
  - L3a: rank-2 × rank-2 → rank-1 (ncA × ncA = {(4,4)})
  - L3b: rank-2 × rank-2 → rank-0 (ncA × ncC = zero)

  See: D2-STEP1-RESULTS.md §2
-/

/-- ncA is not zero: it has a true entry at (0,1). -/
theorem ncA_nonzero : ¬ isZero ncA := by
  intro h; exact absurd (h ⟨0, by omega⟩ ⟨1, by omega⟩) (by simp [ncA])

/-- ncB is not zero: it has a true entry at (2,3). -/
theorem ncB_nonzero : ¬ isZero ncB := by
  intro h; exact absurd (h ⟨2, by omega⟩ ⟨3, by omega⟩) (by simp [ncB])

/-- ncC is not zero: it has a true entry at (0,0). -/
theorem ncC_nonzero : ¬ isZero ncC := by
  intro h; exact absurd (h ⟨0, by omega⟩ ⟨0, by omega⟩) (by simp [ncC])

/-- ncA is not rank-1: entries (0,1) and (4,4) cannot form an outer product.
    If M = R⊗C, then M[0][1]=M[4][4]=true implies R[0]=R[4]=C[1]=C[4]=true,
    which forces M[0][4]=true. But ncA[0][4]=false. Contradiction. -/
theorem ncA_not_rankOne : ¬ IsRankOne ncA := by
  intro ⟨R, C, _, _, hRC⟩
  have h01 := (hRC ⟨0, by omega⟩ ⟨1, by omega⟩).mp (by simp [ncA])
  have h44 := (hRC ⟨4, by omega⟩ ⟨4, by omega⟩).mp (by simp [ncA])
  have h04 := (hRC ⟨0, by omega⟩ ⟨4, by omega⟩).mpr ⟨h01.1, h44.2⟩
  simp [ncA] at h04

/-- ncB is not rank-1: same argument with entries (2,3) and (4,4).
    R[2]=R[4]=C[3]=C[4]=true forces M[2][4]=true, but ncB[2][4]=false. -/
theorem ncB_not_rankOne : ¬ IsRankOne ncB := by
  intro ⟨R, C, _, _, hRC⟩
  have h23 := (hRC ⟨2, by omega⟩ ⟨3, by omega⟩).mp (by simp [ncB])
  have h44 := (hRC ⟨4, by omega⟩ ⟨4, by omega⟩).mp (by simp [ncB])
  have h24 := (hRC ⟨2, by omega⟩ ⟨4, by omega⟩).mpr ⟨h23.1, h44.2⟩
  simp [ncB] at h24

/-- The product ncA ⊗ ncA has true entries only at (4,4). -/
private theorem mul_ncA_ncA_entries :
    ∀ (i j : Fin 8), mul ncA ncA i j = true → i = ⟨4, by omega⟩ ∧ j = ⟨4, by omega⟩ := by
  native_decide

/-- The product ncA ⊗ ncA is true at (4,4). -/
private theorem mul_ncA_ncA_44 : mul ncA ncA ⟨4, by omega⟩ ⟨4, by omega⟩ = true := by
  native_decide

/-- The product ncA ⊗ ncA is rank-1: it equals the outer product of
    R = (0,0,0,0,1,0,0,0) and C = (0,0,0,0,1,0,0,0). -/
theorem ncA_mul_ncA_rankOne : IsRankOne (mul ncA ncA) := by
  refine ⟨fun i => decide (i = ⟨4, by omega⟩),
          fun j => decide (j = ⟨4, by omega⟩),
          ⟨⟨4, by omega⟩, by simp⟩,
          ⟨⟨4, by omega⟩, by simp⟩,
          ?_⟩
  intro i j
  constructor
  · intro h
    have := mul_ncA_ncA_entries i j h
    exact ⟨by simp [this.1], by simp [this.2]⟩
  · intro ⟨hi, hj⟩
    simp [decide_eq_true_eq] at hi hj
    subst hi; subst hj
    exact mul_ncA_ncA_44

/-- **L3a: Rank Drop 2→1**.
    Two non-zero, non-rank-1 matrices whose product is rank-1.
    ncA × ncA: both inputs are rank-2, product is rank-1. -/
theorem exists_rank_drop_2_to_1 :
    ∃ A B : BoolMat 8,
      ¬ isZero A ∧ ¬ isZero B ∧
      ¬ IsRankOne A ∧ ¬ IsRankOne B ∧
      IsRankOne (mul A B) :=
  ⟨ncA, ncA, ncA_nonzero, ncA_nonzero, ncA_not_rankOne, ncA_not_rankOne, ncA_mul_ncA_rankOne⟩

/-- The product ncA ⊗ ncC is zero: disjoint supports. -/
theorem ncA_mul_ncC_zero : isZero (mul ncA ncC) := by
  have : ∀ (i j : Fin 8), mul ncA ncC i j = false := by native_decide
  exact this

/-- **L3b: Rank Drop 2→0**.
    Two non-zero matrices whose product is the zero matrix.
    ncA has columns {1,4}, ncC has rows {0,5} — disjoint, so product = 0. -/
theorem exists_rank_drop_2_to_0 :
    ∃ A B : BoolMat 8,
      ¬ isZero A ∧ ¬ isZero B ∧
      isZero (mul A B) :=
  ⟨ncA, ncC, ncA_nonzero, ncC_nonzero, ncA_mul_ncC_zero⟩

/-! ## L2: Zero Column → Non-Cancellative (General)

  Structural mechanism behind the 89% non-cancellativity rate:
  if a matrix A has a zero column (∀ i, A i j = false), then A is
  left-non-cancellative. This is the typical case in T₃* since most gaps
  are absent from each cube, creating zero columns in the transfer operator.

  The theorem works for any n, not just 8.

  See: D2-STEP1-RESULTS.md §2 (Non-Cancellativity — MASIVĂ)
  Plan: experiments-ml/018_2026-03-11_negation-complexity/L2-PLAN.md
-/

/-- Point matrix E_{j,j}: single true entry at (j,j). -/
private def pointMat (n : Nat) (j : Fin n) : BoolMat n :=
  fun i k => decide (i = j ∧ k = j)

/-- Point matrix differs from zero at (j,j). -/
private theorem pointMat_ne_zero {n : Nat} (j : Fin n) :
    pointMat n j ≠ zero := by
  intro h
  have := congrFun (congrFun h j) j
  simp [pointMat, zero] at this

/-- Multiplying any matrix by the point matrix E_{j,j}: the result at (i,k)
    depends only on A[i,j] (since E_{j,j} has its only true entry at (j,j)). -/
private theorem mul_pointMat_eq {n : Nat} (A : BoolMat n) (j : Fin n)
    (hj : ∀ i : Fin n, A i j = false) :
    mul A (pointMat n j) = zero := by
  funext i k
  simp only [mul, zero]
  show (List.finRange n).any (fun l => A i l && pointMat n j l k) = false
  rw [List.any_eq_false]
  intro l _
  simp only [pointMat, Bool.and_eq_true, decide_eq_true_eq]
  intro ⟨hAil, hlj, _⟩
  rw [← hlj] at hj
  exact absurd hAil (by rw [hj i]; decide)

/-- **L2: Zero Column → Left-Non-Cancellative** (General Theorem).
    Any boolean matrix with a zero column is left-non-cancellative:
    if column j of A is all-false, then A ⊗ zero = A ⊗ E_{j,j} but zero ≠ E_{j,j}.

    This is the structural mechanism behind the 89% non-cancellativity rate in T₃*:
    most transfer operators have zero columns (because most gaps are absent from each cube).

    Works for any size n ≥ 1, not just n = 8. -/
theorem zero_col_non_cancellative {n : Nat} (A : BoolMat n) (j : Fin n)
    (hj : ∀ i : Fin n, A i j = false) :
    ∃ B C : BoolMat n, B ≠ C ∧ mul A B = mul A C := by
  refine ⟨zero, pointMat n j, fun h => pointMat_ne_zero j h.symm, ?_⟩
  rw [mul_zero, mul_pointMat_eq A j hj]

/-! ## Corollaries

  These theorems together show that T₃* has fundamentally different algebraic
  structure from a group:
  - In a group: AB = AC ⟹ B = C (cancellativity)
  - In T₃*: AB = AC with B ≠ C is the NORM (89% of pairs)
  - In a group: rank is preserved under multiplication
  - In T₃*: rank can drop arbitrarily (2→1, 2→0)

  This information loss under composition is the algebraic mechanism behind
  the absorption phenomenon: random walks in T₃* converge to zero exponentially
  (λ = 0.947, half-life = 12.8 steps).
-/

/-- Non-cancellativity implies boolean matrix multiplication is not cancellative.
    If mul were cancellative, we'd have: mul A B = mul A C → B = C for all A, B, C. -/
theorem boolmat8_not_cancellative :
    ¬ (∀ A B C : BoolMat 8, mul A B = mul A C → B = C) := by
  intro h
  obtain ⟨A, B, C, hne, heq⟩ := exists_non_cancellative
  exact hne (h A B C heq)

end BoolMat
