/-
  CubeGraph/Rank1Algebra.lean
  Rank-1 outer product algebra: explicit composition and idempotence.

  NEW THEOREMS:
  - rankOne_eq_outerProduct: M = outerProduct rowSup colSup (canonical form)
  - rank1_compose_eq: A·B = outerProduct A.rowSup B.colSup (when connected)
  - rank1_compose_zero: A·B = zero (when disconnected)
  - rank1_idempotent: trace > 0 → M² = M

  These formalize the Scalar Composition Law (RANK1-CONVERGENCE §3):
    M₁·M₂ = ⟨c₁,r₂⟩ · (r₁ ⊗ c₂)
  Verified computationally on 1.3M products (100% match).

  See: experiments-ml/019_2026-03-13_topological-hardness/brainstorm/RANK1-CONVERGENCE.md §3
-/

import CubeGraph.ChannelAlignment

namespace BoolMat

variable {n : Nat}

/-! ## Outer Product Definition -/

/-- Outer product of indicator vectors: (R ⊗ C)[i,j] = R[i] ∧ C[j]. -/
def outerProduct (R C : Fin n → Bool) : BoolMat n :=
  fun i j => R i && C j

@[simp] theorem outerProduct_apply (R C : Fin n → Bool) (i j : Fin n) :
    outerProduct R C i j = (R i && C j) := rfl

/-- An outer product of nonempty indicators is rank-1. -/
theorem outerProduct_isRankOne {R C : Fin n → Bool}
    (hR : IndNonempty R) (hC : IndNonempty C) :
    (outerProduct R C).IsRankOne :=
  ⟨R, C, hR, hC, fun i j => by simp [outerProduct, Bool.and_eq_true]⟩

/-! ## Canonical Form -/

/-- Convert a Bool iff to Bool-and equality. -/
private theorem eq_band_of_iff {a b c : Bool}
    (h : a = true ↔ (b = true ∧ c = true)) : a = (b && c) := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- A rank-1 matrix equals the outer product of its supports.
    This is the canonical form: M = rowSup(M) ⊗ colSup(M). -/
theorem rankOne_eq_outerProduct {M : BoolMat n} (h : M.IsRankOne) :
    M = outerProduct M.rowSup M.colSup := by
  obtain ⟨R, C, hR_eq, hC_eq, hRC⟩ := rankOne_outer_product h
  subst hR_eq; subst hC_eq
  funext i j
  exact eq_band_of_iff (hRC i j)

/-! ## Scalar Composition Law (L2)

  For rank-1 matrices M₁ = r₁ ⊗ c₁ and M₂ = r₂ ⊗ c₂:
    M₁ · M₂ = ⟨c₁, r₂⟩ · (r₁ ⊗ c₂)
  where ⟨c₁, r₂⟩ = ∃ k, c₁[k] ∧ r₂[k] is a boolean scalar.

  Two cases:
  - Connected (⟨c₁,r₂⟩ = true): product = outerProduct r₁ c₂ (rank-1)
  - Disconnected (⟨c₁,r₂⟩ = false): product = zero (rank-0)
-/

/-- **Scalar Composition Law** (connected case).
    A · B = outerProduct A.rowSup B.colSup.
    Row support inherited from left, column support from right. -/
theorem rank1_compose_eq {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne)
    (h_conn : ¬ IndDisjoint A.colSup B.rowSup) :
    mul A B = outerProduct A.rowSup B.colSup := by
  rw [rankOne_eq_outerProduct (rankOne_mul_rankOne hA hB h_conn),
      rankOne_mul_rowSup hA hB h_conn,
      rankOne_mul_colSup hA hB h_conn]

/-- **Scalar Composition Law** (disconnected case). A · B = zero. -/
theorem rank1_compose_zero {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne)
    (h_disj : IndDisjoint A.colSup B.rowSup) :
    mul A B = zero := by
  funext i j; exact (rankOne_mul_zero_iff hA hB).mpr h_disj i j

/-! ## Idempotence (L3) -/

/-- **Rank-1 Idempotence**: trace > 0 implies M² = M.
    Rank-1 matrices with positive trace are projections in the boolean semiring.
    Combined with experimental rank-1 convergence (all composed operators
    converge to rank-1 in ~3 steps), this shows the transfer semigroup T₃*
    collapses to a band (semigroup where every element is idempotent). -/
theorem rank1_idempotent {M : BoolMat n}
    (h : M.IsRankOne) (ht : M.trace = true) :
    mul M M = M := by
  have h_conn : ¬ IndDisjoint M.colSup M.rowSup := by
    rw [IndDisjoint_comm M.colSup M.rowSup]
    exact (trace_rankOne_iff h).mp ht
  rw [rank1_compose_eq h h h_conn, ← rankOne_eq_outerProduct h]

end BoolMat
