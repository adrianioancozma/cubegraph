/-
  CubeGraph/FullSupportComposition.lean
  Full-support composition: when every active row of A connects to every active
  column of B through some intermediate, A·B = outerProduct(rowSup A, colSup B).

  This is the algebraic mechanism behind rank-2 → rank-1 collapse on paths:
  "misaligned" operators (block-diagonal on different variables) composed through
  a cube with full gap coverage satisfy the full-support condition.

  NEW THEOREMS:
  - mul_full_support:          A·B = outerProduct(rowSup A, colSup B)
  - mul_full_support_rankOne:  IsRankOne(A·B) under full-support connectivity
  - mul_full_support_rowSup:   rowSup(A·B) = rowSup(A)
  - mul_full_support_colSup:   colSup(A·B) = colSup(B)

  See: experiments-ml/019_.../brainstorm/RANK1-CONVERGENCE.md §4 (rank collapse mechanism)
  See: experiments-ml/019_.../brainstorm/PLAN-L5-MisalignedCollapse.md (plan)
-/

import CubeGraph.Rank1Algebra

namespace BoolMat

variable {n : Nat}

/-! ### Full-Support Composition -/

/-- Full-support composition: if every active row of A connects to every active
    column of B through some intermediate k, then A·B equals the outer product
    of their supports. This subsumes both rank-1 × rank-1 composition and
    the "misaligned rank-2 collapse" mechanism. -/
theorem mul_full_support (A B : BoolMat n)
    (h : ∀ i j, A.rowSup i = true → B.colSup j = true →
         ∃ k, A i k = true ∧ B k j = true) :
    mul A B = outerProduct A.rowSup B.colSup := by
  funext i j
  simp only [outerProduct]
  -- Goal: mul A B i j = (A.rowSup i && B.colSup j)
  -- Prove both directions as hypotheses, then close by boolean case analysis
  have fwd : mul A B i j = true → A.rowSup i = true ∧ B.colSup j = true := by
    intro hm
    obtain ⟨k, hak, hbk⟩ := (mul_apply_true A B i j).mp hm
    exact ⟨mem_rowSup_iff.mpr ⟨k, hak⟩, mem_colSup_iff.mpr ⟨k, hbk⟩⟩
  have bwd : A.rowSup i = true → B.colSup j = true → mul A B i j = true := by
    intro hr hc
    obtain ⟨k, hak, hbk⟩ := h i j hr hc
    exact (mul_apply_true A B i j).mpr ⟨k, hak, hbk⟩
  cases hm : mul A B i j <;> cases hr : A.rowSup i <;> cases hc : B.colSup j <;> simp_all

/-- Corollary: under full-support connectivity with nonempty supports,
    the product is rank-1. -/
theorem mul_full_support_rankOne (A B : BoolMat n)
    (hRA : IndNonempty A.rowSup) (hCB : IndNonempty B.colSup)
    (h : ∀ i j, A.rowSup i = true → B.colSup j = true →
         ∃ k, A i k = true ∧ B k j = true) :
    IsRankOne (mul A B) := by
  rw [mul_full_support A B h]
  exact ⟨A.rowSup, B.colSup, hRA, hCB, fun i j => by
    simp only [outerProduct_apply, Bool.and_eq_true]⟩

/-! ### Support Inheritance -/

/-- Row support of product = row support of left factor. -/
theorem mul_full_support_rowSup (A B : BoolMat n)
    (h : ∀ i j, A.rowSup i = true → B.colSup j = true →
         ∃ k, A i k = true ∧ B k j = true)
    (hCB : IndNonempty B.colSup) :
    (mul A B).rowSup = A.rowSup := by
  rw [mul_full_support A B h]
  funext i
  have lhs_iff : (outerProduct A.rowSup B.colSup).rowSup i = true ↔ A.rowSup i = true := by
    rw [mem_rowSup_iff]
    constructor
    · intro ⟨j, hj⟩; simp only [outerProduct, Bool.and_eq_true] at hj; exact hj.1
    · intro hr; obtain ⟨j, hj⟩ := hCB
      exact ⟨j, by simp only [outerProduct, Bool.and_eq_true]; exact ⟨hr, hj⟩⟩
  cases h1 : (outerProduct A.rowSup B.colSup).rowSup i <;>
    cases h2 : A.rowSup i <;> simp_all

/-- Column support of product = column support of right factor. -/
theorem mul_full_support_colSup (A B : BoolMat n)
    (h : ∀ i j, A.rowSup i = true → B.colSup j = true →
         ∃ k, A i k = true ∧ B k j = true)
    (hRA : IndNonempty A.rowSup) :
    (mul A B).colSup = B.colSup := by
  rw [mul_full_support A B h]
  funext j
  have lhs_iff : (outerProduct A.rowSup B.colSup).colSup j = true ↔ B.colSup j = true := by
    rw [mem_colSup_iff]
    constructor
    · intro ⟨i, hi⟩; simp only [outerProduct, Bool.and_eq_true] at hi; exact hi.2
    · intro hc; obtain ⟨i, hi⟩ := hRA
      exact ⟨i, by simp only [outerProduct, Bool.and_eq_true]; exact ⟨hi, hc⟩⟩
  cases h1 : (outerProduct A.rowSup B.colSup).colSup j <;>
    cases h2 : B.colSup j <;> simp_all

end BoolMat
