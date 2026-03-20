/-
  CubeGraph/ZeroDivisors.lean
  Zero-divisor characterization for boolean matrices.

  Main theorems:
  - mul_zero_iff_disjoint: A·B = 0 ↔ colSup(A) ∩ rowSup(B) = ∅
  - pigeonhole_nonzero: |colSup(A)| + |rowSup(B)| > n → A·B ≠ 0

  Generalizes rankOne_mul_zero_iff (ChannelAlignment.lean) by removing rank-1.
  The original proof never used the rank-1 hypothesis — only mem_colSup_iff,
  mem_rowSup_iff, and mul_apply_true, which are defined for all BoolMat.

  Task: experiments-ml/014_2026-03-06_synthesis-foundations/TODO.md (T0.1)
  Plan: experiments-ml/014_2026-03-06_synthesis-foundations/PLAN-T0.1-ZeroDivisors.md
  Validated by:
  - T0.2: gap_count_distribution.py — frac≥5 = 100% → pigeonhole always active
  - T1.2: zero_divisor_density.py — zd_fraction = 0.00000 across 10K formulas
-/

import CubeGraph.ChannelAlignment
import CubeGraph.Theorems

/-! ## Generic list helper -/

/-- Monotonicity of countP: if p implies q pointwise, then countP p ≤ countP q. -/
theorem countP_le_of_implies {α : Type} (p q : α → Bool) (l : List α)
    (h : ∀ x, p x = true → q x = true) :
    l.countP p ≤ l.countP q := by
  induction l with
  | nil => simp [List.countP_nil]
  | cons x xs ih =>
    cases hpx : p x with
    | false =>
      rw [List.countP_cons_of_neg (by simp [hpx])]
      cases hqx : q x with
      | false =>
        rw [List.countP_cons_of_neg (by simp [hqx])]
        exact ih
      | true =>
        rw [List.countP_cons_of_pos hqx]
        omega
    | true =>
      have hqx : q x = true := h x hpx
      rw [List.countP_cons_of_pos hpx, List.countP_cons_of_pos hqx]
      omega

namespace BoolMat

variable {n : Nat}

/-! ## Theorem 1: Zero-product iff disjoint supports -/

/-- A·B = 0 iff column support of A is disjoint from row support of B.
    Generalizes rankOne_mul_zero_iff by removing the rank-1 hypothesis. -/
theorem mul_zero_iff_disjoint (A B : BoolMat n) :
    BoolMat.isZero (BoolMat.mul A B) ↔
    IndDisjoint A.colSup B.rowSup := by
  simp only [isZero, IndDisjoint]
  constructor
  · intro h_zero k ⟨hk_colA, hk_rowB⟩
    obtain ⟨i, hiA⟩ := mem_colSup_iff.mp hk_colA
    obtain ⟨j, hjB⟩ := mem_rowSup_iff.mp hk_rowB
    have hmul : mul A B i j = true := mul_apply_true A B i j |>.mpr ⟨k, hiA, hjB⟩
    rw [h_zero i j] at hmul
    exact Bool.false_ne_true hmul
  · intro h_disj i j
    cases h : mul A B i j with
    | true =>
      obtain ⟨k, hAik, hBkj⟩ := (mul_apply_true A B i j).mp h
      have hk_colA : A.colSup k = true := mem_colSup_iff.mpr ⟨i, hAik⟩
      have hk_rowB : B.rowSup k = true := mem_rowSup_iff.mpr ⟨j, hBkj⟩
      exact absurd ⟨hk_colA, hk_rowB⟩ (h_disj k)
    | false => rfl

/-! ## Support counting -/

/-- Count of true entries in an indicator function over Fin n. -/
def IndCount (f : Fin n → Bool) : Nat :=
  (List.finRange n).countP f

/-- IndCount is at most n. -/
theorem IndCount_le (f : Fin n → Bool) : IndCount f ≤ n := by
  simp only [IndCount]
  have h := CubeGraph.countP_complement f (List.finRange n)
  rw [List.length_finRange] at h
  omega

/-- Disjoint indicator functions have total count at most n. -/
theorem disjoint_IndCount_le {R S : Fin n → Bool}
    (h : IndDisjoint R S) : IndCount R + IndCount S ≤ n := by
  simp only [IndCount]
  have h_le : (List.finRange n).countP S ≤ (List.finRange n).countP (fun k => !R k) := by
    apply countP_le_of_implies
    intro k hSk
    cases hRk : R k with
    | false => simp
    | true => exact absurd ⟨hRk, hSk⟩ (h k)
  have h_compl := CubeGraph.countP_complement R (List.finRange n)
  rw [List.length_finRange] at h_compl
  omega

/-! ## Theorem 2: Pigeonhole → non-zero product -/

/-- If total support count exceeds n, the product is nonzero. -/
theorem pigeonhole_nonzero (A B : BoolMat n)
    (h : IndCount A.colSup + IndCount B.rowSup > n) :
    ¬ BoolMat.isZero (BoolMat.mul A B) := by
  intro h_zero
  have h_disj := (mul_zero_iff_disjoint A B).mp h_zero
  have h_le := disjoint_IndCount_le h_disj
  omega

end BoolMat
