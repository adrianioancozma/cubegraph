/-
  CubeGraph/InvertibilityBarrier.lean
  The algebraic barrier: OR vs XOR — why 3-SAT is NP-hard but XOR-SAT is in P.

  OR absorbs (true ∨ x = true): information irreversibly lost.
  XOR cancels (a ⊕ a = false): information recoverable.
  Rank-1 BoolMat (OR/AND) is never invertible (n ≥ 2).
  Same matrix over GF(2) (XOR/AND) CAN be invertible.

  Part of the 5-Barriers program: five independent tractability mechanisms
  for Boolean SAT, exhaustive by Schaefer's dichotomy (1978).

  See: experiments-ml/012_2026-03-05_fiber-algebra-topology/RESULTS.md (§2, Barrier 1)
  See: experiments-ml/011_2026-03-05_polynomial-barriers/PLAN-L2-INVERTIBILITY-BARRIER.md
  See: experiments-ml/010_2026-03-05/RANK-TOPOLOGY-DICHOTOMY.md
  See: formal/CubeGraph/HornBarrier.lean (Barrier 2: Horn OR-closed gaps)
  See: formal/CubeGraph/DualHornBarrier.lean (Barrier 2b: Dual-Horn AND-closed gaps)
  See: formal/CubeGraph/TrivialSection.lean (Barrier 3: trivial section)
  See: formal/CubeGraph/Rank1AC.lean (Barrier 4: rank-1 + AC → SAT)
  See: formal/CubeGraph/FunctionalTransfer.lean (Barrier 5: functional composition)
  See: formal/CubeGraph/BarrierSummary.lean (Meta: witness failing all 5 barriers)
  See: formal/CubeGraph/FiberDichotomy.lean (fiber size explains WHY 3-SAT is relational)
  See: formal/CubeGraph/TaylorBarrier.lean (no WNU3 on Fin 3 preserves ≠ — CSP angle)
-/

import CubeGraph.ChannelAlignment

namespace CubeGraph

/-! ## Section 1: Scalar OR vs XOR Dichotomy

  OR absorbs: true ∨ x = true (information lost).
  XOR cancels: a ⊕ a = false (information recoverable). -/

/-- OR absorbs true: once set, cannot be unset. -/
theorem or_absorbs : ∀ x : Bool, (true || x) = true := by decide

/-- XOR self-cancels: every element is its own inverse. -/
theorem xor_self_cancel : ∀ x : Bool, Bool.xor x x = false := by decide

/-- OR has no additive inverse: true cannot be "undone". -/
theorem or_no_inverse : ¬ ∃ x : Bool, (true || x) = false := by decide

/-- XOR has an additive inverse for every element. -/
theorem xor_has_inverse : ∀ a : Bool, ∃ x : Bool, Bool.xor a x = false :=
  fun a => ⟨a, xor_self_cancel a⟩

/-! ## Section 2: XorMat — Matrix Multiplication over GF(2)

  BoolMat.mul: (A⊗B)[i,j] = ∨_k (A[i,k] ∧ B[k,j])  — boolean semiring
  XorMat.mul:  (A⊕B)[i,j] = ⊕_k (A[i,k] ∧ B[k,j])  — field GF(2) -/

/-- Matrix multiplication over GF(2): XOR replaces OR. -/
def XorMat.mul (A B : BoolMat n) : BoolMat n :=
  fun i j => (List.finRange n).foldl (fun acc k => Bool.xor acc (A i k && B k j)) false

/-! ## Section 3: The Invertibility Gap

  Rank-1 boolean matrices are NEVER invertible (n ≥ 2).
  Proof: rank-1 M[i,j] = R[i] ∧ C[j] implies either a zero row
  or identical rows — neither compatible with the identity matrix.

  But over GF(2), the same matrix CAN be invertible.
  This is why Gaussian elimination works for XOR-SAT but fails for OR-SAT. -/

/-- Rank-1 boolean matrices are never right-invertible for n ≥ 2. -/
theorem rank1_not_bool_invertible {n : Nat} (hn : n ≥ 2)
    (M : BoolMat n) (hM : M.IsRankOne) :
    ¬ ∃ M' : BoolMat n, BoolMat.mul M M' = BoolMat.one := by
  obtain ⟨R, C, _, _, hRC⟩ := hM
  intro ⟨M', h_eq⟩
  -- M[i,j] = (R i && C j) at the Bool level
  have hM_val : ∀ i k, M i k = (R i && C k) := by
    intro i k
    have h := hRC i k
    cases hm : M i k with
    | true =>
      obtain ⟨hr, hc⟩ := h.mp hm; simp [hr, hc]
    | false =>
      suffices ¬(R i = true ∧ C k = true) by
        cases hr : R i <;> cases hc : C k
        · rfl
        · rfl
        · rfl
        · exact absurd ⟨hr, hc⟩ this
      intro ⟨hr, hc⟩
      have hmk := h.mpr ⟨hr, hc⟩; rw [hm] at hmk; exact absurd hmk (by decide)
  by_cases hR_all : ∀ i : Fin n, R i = true
  · -- R all-true → M i k = C k for all i → all rows identical
    have hM_eq : ∀ i₁ i₂ : Fin n, ∀ k, M i₁ k = M i₂ k := by
      intro i₁ i₂ k; rw [hM_val i₁ k, hM_val i₂ k, hR_all i₁, hR_all i₂]
    -- Rows of M×M' are identical (since rows of M are)
    have hrows : ∀ i₁ i₂ j, BoolMat.mul M M' i₁ j = BoolMat.mul M M' i₂ j := by
      intro i₁ i₂ j; simp only [BoolMat.mul]
      congr 1; funext k; congr 1; exact hM_eq i₁ i₂ k
    -- Rows 0,1 of I differ at column 0
    have h01 := hrows ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩
    rw [h_eq, (BoolMat.one_apply_true _ _).mpr rfl] at h01
    exact absurd ((BoolMat.one_apply_true _ _).mp h01.symm)
      (fun h => by have := Fin.ext_iff.mp h; simp at this)
  · -- ∃ i₀ with R i₀ = false → row i₀ of M is all-zero
    have ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, ¬ (R i₀ = true) :=
      Classical.byContradiction fun h =>
        hR_all fun i => Classical.byContradiction fun hi => h ⟨i, hi⟩
    have hR_false : R i₀ = false := by
      cases h : R i₀ with
      | false => rfl
      | true => exact absurd h hi₀
    have hrow_zero : ∀ k, M i₀ k = false := by
      intro k; rw [hM_val]; simp [hR_false]
    -- (M×M')[i₀,i₀] = false (zero row kills everything)
    have hmul_false : BoolMat.mul M M' i₀ i₀ = false := by
      cases h : BoolMat.mul M M' i₀ i₀ with
      | false => rfl
      | true =>
        obtain ⟨k, hk₁, _⟩ := (BoolMat.mul_apply_true M M' i₀ i₀).mp h
        simp [hrow_zero k] at hk₁
    -- But I[i₀,i₀] = true — contradiction
    have := congrFun (congrFun h_eq i₀) i₀
    rw [hmul_false, (BoolMat.one_apply_true _ _).mpr rfl] at this
    exact absurd this (by decide)

/-- The invertibility gap: [[1,1],[1,0]] is XOR-invertible but NOT OR-invertible.
    Over GF(2): A × [[0,1],[1,1]] = I.
    Over Boolean: A × B ≠ I for any B.
    Proof: from I[1,1]=true derive B'[0,1]=true, then monotonicity gives
    (A×B')[0,1]=true, contradicting I[0,1]=false. -/
theorem invertibility_gap :
    let A : BoolMat 2 := fun i j => !((i.val == 1) && (j.val == 1))
    let B : BoolMat 2 := fun i j => !((i.val == 0) && (j.val == 0))
    XorMat.mul A B = (BoolMat.one : BoolMat 2) ∧
    ¬ ∃ B' : BoolMat 2, BoolMat.mul A B' = BoolMat.one := by
  constructor
  · -- Part 1: XOR invertible — verify pointwise
    have h : ∀ i j : Fin 2, XorMat.mul
        (fun i j => !((i.val == 1) && (j.val == 1)))
        (fun i j => !((i.val == 0) && (j.val == 0))) i j =
        (BoolMat.one : BoolMat 2) i j := by native_decide
    funext i j; exact h i j
  · -- Part 2: Boolean not invertible
    intro ⟨B', h⟩
    let A : BoolMat 2 := fun i j => !((i.val == 1) && (j.val == 1))
    change BoolMat.mul A B' = BoolMat.one at h
    -- Step 1: From (A×B')[1,1] = I[1,1] = true, extract B'[0,1] = true
    have hmul11 : BoolMat.mul A B' ⟨1, by omega⟩ ⟨1, by omega⟩ = true := by
      rw [congrFun (congrFun h _) _]; exact (BoolMat.one_apply_true _ _).mpr rfl
    obtain ⟨k, hAk, hBk⟩ := (BoolMat.mul_apply_true A B' _ _).mp hmul11
    -- A[1,k] = true → k must be 0 (since A[1,1] = false)
    have hk : k = ⟨0, by omega⟩ := by
      rcases k with ⟨kv, hkv⟩
      have : kv = 0 ∨ kv = 1 := by omega
      rcases this with rfl | rfl
      · rfl
      · exact nomatch hAk
    subst hk  -- hBk : B' ⟨0,_⟩ ⟨1,_⟩ = true
    -- Step 2: A[0,0]=true ∧ B'[0,1]=true → (A×B')[0,1] = true (monotonicity)
    have hmul01_true : BoolMat.mul A B' ⟨0, by omega⟩ ⟨1, by omega⟩ = true :=
      (BoolMat.mul_apply_true A B' _ _).mpr ⟨⟨0, by omega⟩, by decide, hBk⟩
    -- Step 3: But I[0,1] = false → (A×B')[0,1] = false
    have hmul01_false : BoolMat.mul A B' ⟨0, by omega⟩ ⟨1, by omega⟩ = false := by
      rw [congrFun (congrFun h _) _]
      show (BoolMat.one : BoolMat 2) ⟨0, by omega⟩ ⟨1, by omega⟩ = false
      decide
    -- Contradiction
    rw [hmul01_false] at hmul01_true
    exact absurd hmul01_true (by decide)

/-! ## Section 4: Monotonicity vs Cancellation

  BoolMat.mul is monotone: a single witness path guarantees the entry is true.
  XorMat.mul allows cancellation: two paths cancel mod 2 (1 ⊕ 1 = 0).
  This is why OR-based computation can only ADD truth, never REMOVE it. -/

/-- BoolMat multiplication is monotone: a single witness suffices. -/
theorem boolmat_mul_monotone (A B : BoolMat n) (i j k : Fin n)
    (hA : A i k = true) (hB : B k j = true) :
    BoolMat.mul A B i j = true :=
  (BoolMat.mul_apply_true A B i j).mpr ⟨k, hA, hB⟩

/-- XorMat can cancel: two paths annihilate under XOR.
    J² = J under OR (both paths contribute, OR keeps them).
    J²[0,0] = false under XOR (1 ⊕ 1 = 0, paths cancel). -/
theorem xormat_can_cancel :
    let J : BoolMat 2 := fun _ _ => true
    BoolMat.mul J J ⟨0, by omega⟩ ⟨0, by omega⟩ = true ∧
    XorMat.mul J J ⟨0, by omega⟩ ⟨0, by omega⟩ = false := by
  native_decide

/-! ## Section 5: CubeGraph Connection

  Transfer operators are rank ≤ 2 at critical density.
  Rank-1 operators are NOT boolean-invertible (Section 3), so the monodromy
  monoid is a SEMIGROUP, not a GROUP. Rank can decrease → UNSAT possible.

  Complementary to Rank1AC.lean:
  - Rank1AC: rank-1 + AC → topology irrelevant → SAT
  - Here: rank-1 NOT invertible → rank CAN collapse → UNSAT -/

/-- Transfer operators of rank 1 are not Boolean-invertible. -/
theorem transferOp_rank1_not_invertible (c₁ c₂ : Cube)
    (hR1 : (transferOp c₁ c₂).IsRankOne) :
    ¬ ∃ M' : BoolMat 8, BoolMat.mul (transferOp c₁ c₂) M' = BoolMat.one :=
  rank1_not_bool_invertible (by omega) _ hR1

end CubeGraph
