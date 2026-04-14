/-
  CubeGraph/BandSemigroup.lean
  Band semigroup structure of rank-1 boolean matrices.

  NEW THEOREMS:
  - rank1_nilpotent: trace = 0 → M² = zero (nilpotent of index 2)
  - rank1_aperiodic: M³ = M² (aperiodicity, Krohn-Rhodes complexity = 0)
  - rank1_trace_mul: trace(A·B) ↔ ¬IndDisjoint A.rowSup B.colSup
  - rank1_rectangular: ABA = A (rectangular band law, when connected)
  - rank1_rectangular_symm: BAB = B (symmetric version)

  The rank-1 trace>0 subsemigroup satisfies xyx = x (rectangular band).
  This is the STRONGEST band axiom — implies normal, left/right-regular, etc.
  Algebraically: the simplest possible semigroup structure (KR complexity 0).

  Combined with rank-1 convergence (all operators reach rank-1 in ~3 steps),
  this shows T₃* collapses to a nil-extension of a rectangular band:
  - trace > 0: idempotent projections (M² = M)
  - trace = 0: nilpotent index 2 (M² = 0)
  - multiplication: (r₁,c₁)·(r₂,c₂) = (r₁,c₂) — row from left, column from right

  See: experiments-ml/019_2026-03-13_topological-hardness/brainstorm/RANK1-CONVERGENCE.md §3-4
  See: experiments-ml/019_2026-03-13_topological-hardness/brainstorm/PLAN-T2-BandSemigroup.md
  See: experiments-ml/033_2026-03-26_tensor-dynamics/INSIGHT-NOT-CANNOT-HELP.md (F5: rank1_no_right_inverse — T₃* aperiodic = no inverses = erase-only machine)
  See: experiments-ml/033_2026-03-26_tensor-dynamics/INSIGHT-ERASE-ONLY-MACHINE.md
-/

import CubeGraph.Rank1Algebra

namespace BoolMat

variable {n : Nat}

/-! ## Nilpotent Classification (B1)

  Rank-1 matrices with trace = 0 are nilpotent of index 2: M² = 0.
  This is the dual of rank1_idempotent (trace > 0 → M² = M).
  Together they give a complete trichotomy:
    zero (idempotent), rank-1 trace>0 (idempotent), rank-1 trace=0 (nilpotent).
-/

/-- **Rank-1 Nilpotent**: trace = 0 implies M² = zero.
    The supports are disjoint (no self-compatibility), so M·M has no witnesses. -/
theorem rank1_nilpotent {M : BoolMat n}
    (h : M.IsRankOne) (ht : M.trace = false) :
    mul M M = zero := by
  apply rank1_compose_zero h h
  rw [IndDisjoint_comm]
  exact Classical.byContradiction fun h_neg =>
    absurd ((trace_rankOne_iff h).mpr h_neg) (by simp [ht])

/-! ## Aperiodicity (B2)

  Every rank-1 matrix satisfies M³ = M² (stabilization at ω = 2).
  This is the defining property of an aperiodic semigroup element.

  CONSEQUENCE: Krohn-Rhodes complexity = 0.
  - No group components in the decomposition
  - Recognizes only star-free languages (McNaughton-Papert)
  - Computable in AC⁰ (constant-depth circuits)
  - CONTRAST: rank-2 operators can generate Z/2Z → KR ≥ 1
-/

/-- **Rank-1 Aperiodicity**: M³ = M² for all rank-1 matrices.
    Unifies the idempotent case (M²=M, so M³=M·M=M²) and
    the nilpotent case (M²=0, so M³=M·0=0=M²). -/
theorem rank1_aperiodic {M : BoolMat n} (h : M.IsRankOne) :
    mul M (mul M M) = mul M M := by
  cases h_trace : M.trace with
  | false =>
    rw [rank1_nilpotent h h_trace, mul_zero]
  | true =>
    simp only [rank1_idempotent h h_trace]

/-! ## Trace of Product (B5)

  For connected rank-1 matrices, the trace of the product determines
  whether the result stays idempotent (trace>0) or becomes nilpotent (trace=0).
-/

/-- **Trace of rank-1 product**: trace(A·B) = true iff rowSup(A) meets colSup(B).
    When true: A·B is idempotent. When false: A·B is nilpotent (index 2). -/
theorem rank1_trace_mul {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne)
    (h_conn : ¬ IndDisjoint A.colSup B.rowSup) :
    (mul A B).trace = true ↔ ¬ IndDisjoint A.rowSup B.colSup := by
  have hAB := rankOne_mul_rankOne hA hB h_conn
  rw [trace_rankOne_iff hAB, rankOne_mul_rowSup hA hB h_conn,
      rankOne_mul_colSup hA hB h_conn]

/-! ## Rectangular Band (B3, B4)

  The KEY algebraic structure theorem:
    xyx = x  (when all products are connected and trace(x) > 0)

  This is the RECTANGULAR BAND axiom — the strongest band type.
  It means rank-1 operators are "forgetful projections":
  B leaves no trace in ABA. Only A's own supports survive.

  Algebraically: rectangular band ≅ L-classes × R-classes
  where L-class = same colSup, R-class = same rowSup,
  and multiplication is (r₁,c₁)·(r₂,c₂) = (r₁,c₂).
-/

/-- **Rectangular Band Law**: ABA = A for connected rank-1 matrices.
    B is completely absorbed — only A's supports survive.
    This is the strongest band axiom (implies normal, left/right-regular). -/
theorem rank1_rectangular {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne)
    (h_AB : ¬ IndDisjoint A.colSup B.rowSup)
    (h_BA : ¬ IndDisjoint B.colSup A.rowSup) :
    mul (mul A B) A = A := by
  have hAB := rankOne_mul_rankOne hA hB h_AB
  have h_conn : ¬ IndDisjoint (mul A B).colSup A.rowSup := by
    rw [rankOne_mul_colSup hA hB h_AB]; exact h_BA
  rw [rank1_compose_eq hAB hA h_conn,
      rankOne_mul_rowSup hA hB h_AB,
      ← rankOne_eq_outerProduct hA]

/-- **Rectangular Band Law (symmetric)**: BAB = B.
    The symmetric version: A is completely absorbed in BAB. -/
theorem rank1_rectangular_symm {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne)
    (h_AB : ¬ IndDisjoint A.colSup B.rowSup)
    (h_BA : ¬ IndDisjoint B.colSup A.rowSup) :
    mul (mul B A) B = B := by
  have hBA := rankOne_mul_rankOne hB hA h_BA
  have h_conn : ¬ IndDisjoint (mul B A).colSup B.rowSup := by
    rw [rankOne_mul_colSup hB hA h_BA]; exact h_AB
  rw [rank1_compose_eq hBA hB h_conn,
      rankOne_mul_rowSup hB hA h_BA,
      ← rankOne_eq_outerProduct hB]

/-! ## No Multiplicative Inverse (F5)

  For rank-1 boolean matrices (n ≥ 2): no element has a two-sided multiplicative inverse.
  That is, ¬∃ M', mul M M' = one ∧ mul M' M = one.

  Proof: rank-1 M[i,j] = R[i] ∧ C[j]. Either some row is all-zero (giving a zero row
  in M·M', contradicting identity) or all rows are identical (giving identical rows in
  M·M', contradicting identity). -/

/-- Helper: M entry is false when R[i] = false (row is zero). -/
private theorem rank1_zero_row {M : BoolMat n} {R C : Fin n → Bool}
    (hRC : ∀ i j, M i j = true ↔ R i = true ∧ C j = true)
    {i : Fin n} (hi : R i = false) (k : Fin n) : M i k = false := by
  cases hm : M i k
  · rfl
  · have := (hRC i k).mp hm; rw [hi] at this; exact absurd this.1 (by simp)

/-- Helper: M entry only depends on C when R[i] = true (row equals C). -/
private theorem rank1_row_eq_C {M : BoolMat n} {R C : Fin n → Bool}
    (hRC : ∀ i j, M i j = true ↔ R i = true ∧ C j = true)
    {i : Fin n} (hi : R i = true) (k : Fin n) : M i k = C k := by
  cases hm : M i k <;> cases hc : C k
  · rfl
  · exact absurd ((hRC i k).mpr ⟨hi, hc⟩) (by simp [hm])
  · have := (hRC i k).mp hm; exact absurd this.2 (by simp [hc])
  · rfl

/-- **No Multiplicative Inverse (F5)**: rank-1 boolean matrices have no right inverse.
    If M is rank-1 (n ≥ 2) then there is no M' with M·M' = I.
    Proof: rank-1 M collapses row information — either a zero row or identical rows,
    both incompatible with the identity. -/
theorem rank1_no_right_inverse {M : BoolMat n} (hn : n ≥ 2) (h : M.IsRankOne) :
    ¬ ∃ M' : BoolMat n, mul M M' = one := by
  obtain ⟨R, C, hR, hC, hRC⟩ := h
  intro ⟨M', h_eq⟩
  by_cases hR_all : ∀ i : Fin n, R i = true
  · -- All rows of M are equal to C, so all rows of M·M' are identical
    have hM_rows : ∀ i₁ i₂ : Fin n, ∀ k, M i₁ k = M i₂ k := fun i₁ i₂ k => by
      rw [rank1_row_eq_C hRC (hR_all i₁), rank1_row_eq_C hRC (hR_all i₂)]
    -- Product rows 0 and 1 of M·M' must be equal
    have h01 : ∀ j, mul M M' ⟨0, by omega⟩ j = mul M M' ⟨1, by omega⟩ j := fun j => by
      simp only [mul]; congr 1; funext k; congr 1; exact hM_rows ⟨0, by omega⟩ ⟨1, by omega⟩ k
    -- But one[0,0] = true and one[1,0] = false
    have h0 := h01 ⟨0, by omega⟩
    rw [h_eq] at h0
    -- h0 : one ⟨0,_⟩ ⟨0,_⟩ = one ⟨1,_⟩ ⟨0,_⟩
    -- one[0,0] = decide(0=0) = true; one[1,0] = decide(1=0) = false
    have h0_lhs : (one : BoolMat n) ⟨0, by omega⟩ ⟨0, by omega⟩ = true := by
      simp [one, Fin.ext_iff]
    have h0_rhs : (one : BoolMat n) ⟨1, by omega⟩ ⟨0, by omega⟩ = false := by
      simp [one, Fin.ext_iff]
    rw [h0_lhs] at h0
    rw [h0_rhs] at h0
    exact absurd h0 (by decide)
  · -- Some row i₀ has R i₀ = false → row i₀ of M is all-zero
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, R i₀ = false :=
      Classical.byContradiction fun hne =>
        hR_all fun i =>
          Classical.byContradiction fun hf =>
            hne ⟨i, Bool.eq_false_iff.mpr hf⟩
    -- Row i₀ of M is all-zero
    have hzero : ∀ k, M i₀ k = false := rank1_zero_row hRC hi₀
    -- Row i₀ of M·M' is all-false
    have hrow : ∀ j, mul M M' i₀ j = false := fun j => by
      cases hval : mul M M' i₀ j
      · rfl
      · rw [mul_apply_true] at hval
        obtain ⟨k, hk1, _⟩ := hval
        exact absurd hk1 (by rw [hzero k]; simp)
    -- But (one)[i₀, i₀] = true
    have h_id := hrow i₀
    rw [h_eq] at h_id
    simp only [one] at h_id
    -- decide (i₀ = i₀) = false → True = false → contradiction
    simp [decide_eq_true_eq] at h_id

end BoolMat
