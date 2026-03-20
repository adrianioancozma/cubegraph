/-
  CubeGraph/RowRank.lean
  Row-rank submultiplicativity for boolean matrices.

  Main theorem:
  - rowRank_mul_le: rowRank(A · B) ≤ rowRank(A)

  This is the key algebraic lemma for the T₃* ACC⁰ result:
  all elementary transfer operators have rowRank ≤ 4, and since
  row-rank cannot increase under multiplication, ALL elements
  of T₃* have rowRank ≤ 4, ruling out A₅ (which needs rank ≥ 5).

  NOTE: rowRank(A · B) ≤ rowRank(B) is FALSE in the boolean semiring!
  Counterexample: A = [[1,1,0],[1,0,0],[0,1,0]], B = [[1,0,0],[0,1,0],[0,0,0]]
  gives rowRank(A·B) = 3 > rowRank(B) = 2.

  Dependencies: BoolMat.lean (mul, mul_apply_true), ChannelAlignment.lean (rowSup, mem_rowSup_iff),
                ZeroDivisors.lean (countP_le_of_implies)

  See: experiments-ml/018_2026-03-11_negation-complexity/D2-STEP2-RESULTS.md
-/

import CubeGraph.ZeroDivisors

namespace BoolMat

variable {n : Nat}

/-! ## Row Rank Definition -/

/-- Row rank: number of nonzero rows in a boolean matrix.
    A row is nonzero iff its rowSup indicator is true. -/
def rowRank (M : BoolMat n) : Nat :=
  (List.finRange n).countP fun i => M.rowSup i

/-! ## Basic Properties -/

/-- The zero matrix has row rank 0. -/
theorem rowRank_zero : rowRank (zero : BoolMat n) = 0 := by
  unfold rowRank rowSup zero
  simp [List.countP_eq_zero, List.any_eq_true]

/-- Row rank is bounded by the matrix dimension. -/
theorem rowRank_le (M : BoolMat n) : rowRank M ≤ n := by
  unfold rowRank
  calc (List.finRange n).countP _ ≤ (List.finRange n).length := List.countP_le_length
    _ = n := List.length_finRange

/-! ## Key Lemma: nonzero row propagation through multiplication -/

/-- If row i of A·B is nonzero, then row i of A is nonzero.
    Proof: (A·B)[i,j] = true implies ∃ k, A[i,k] = true,
    so row i of A has at least one true entry. -/
theorem rowSup_mul_of_rowSup (A B : BoolMat n) (i : Fin n)
    (h : (mul A B).rowSup i = true) : A.rowSup i = true := by
  rw [mem_rowSup_iff] at h ⊢
  obtain ⟨j, hij⟩ := h
  rw [mul_apply_true] at hij
  obtain ⟨k, hAik, _⟩ := hij
  exact ⟨k, hAik⟩

/-! ## Main Theorem -/

/-- Row-rank submultiplicativity (LEFT factor):
    rowRank(A · B) ≤ rowRank(A).

    Proof: the set of nonzero rows of A·B is a subset of
    the nonzero rows of A (by rowSup_mul_of_rowSup),
    so counting gives the inequality. -/
theorem rowRank_mul_le (A B : BoolMat n) :
    rowRank (mul A B) ≤ rowRank A := by
  unfold rowRank
  exact countP_le_of_implies
    (fun i => (mul A B).rowSup i)
    (fun i => A.rowSup i)
    (List.finRange n)
    (fun i h => rowSup_mul_of_rowSup A B i h)

/-! ## Corollaries for composition chains -/

/-- Row rank of a triple product: rowRank(A·B·C) ≤ rowRank(A). -/
theorem rowRank_mul_mul_le (A B C : BoolMat n) :
    rowRank (mul (mul A B) C) ≤ rowRank A :=
  Nat.le_trans (rowRank_mul_le (mul A B) C) (rowRank_mul_le A B)

/-- Row rank of mul with zero: mul zero B has rowRank 0. -/
theorem rowRank_zero_mul (B : BoolMat n) : rowRank (mul zero B) = 0 := by
  rw [zero_mul]; exact rowRank_zero

/-- If A has rowRank 0 (i.e. A = zero), then A·B has rowRank 0. -/
theorem rowRank_mul_of_rowRank_zero (A B : BoolMat n) (h : rowRank A = 0) :
    rowRank (mul A B) = 0 := by
  have hle := rowRank_mul_le A B
  omega

end BoolMat
