/-
  CubeGraph/IdempotenceBarrier.lean
  T6: Idempotence Kills Gauss — Boolean band vs GF(2) nilpotent

  The same boolean 8×8 matrix can be:
  - IDEMPOTENT under boolean composition (M² = M, band semigroup)
  - NILPOTENT under GF(2) composition (M² = 0, self-annihilation)

  Root cause: 1+1=1 (boolean) vs 1+1=0 (GF(2)).

  See: BandSemigroup.lean (rank1_idempotent, rank1_nilpotent)
  See: RankMonotonicity.lean (rowRank_foldl_le_one — rank-1 absorbing)
  See: Type2Monodromy.lean (local consistency enabled by idempotent trace > 0)
  See: experiments-ml/021_.../T1-RESULTS.md (band vs nilpotent empiric)
  See: experiments-ml/021_.../T6-PLAN.md (plan)
  See: experiments-ml/021_.../MICRO-MACRO-BRIDGE.md (idempotence = bridge saturates)
-/

import CubeGraph.BandSemigroup
import CubeGraph.RankMonotonicity

namespace BoolMat

variable {n : Nat}

/-! ## Section 1: Boolean Dichotomy -/

/-- **Rank-1 dichotomy**: idempotent or nilpotent, no other option. -/
theorem rank1_dichotomy {M : BoolMat n} (h : M.IsRankOne) :
    mul M M = M ∨ mul M M = zero := by
  cases h_trace : M.trace with
  | false => exact .inr (rank1_nilpotent h h_trace)
  | true => exact .inl (rank1_idempotent h h_trace)

/-! ## Section 2: Idempotence Barrier -/

/-- **Idempotence barrier**: re-applying a rank-1 idempotent does nothing.
    M · (M · B) = M · B. AC-3/propagation stagnates. -/
theorem idempotence_barrier {M : BoolMat n}
    (h : M.IsRankOne) (ht : M.trace = true) (B : BoolMat n) :
    mul M (mul M B) = mul M B := by
  have : mul M M = M := rank1_idempotent h ht
  rw [show mul M (mul M B) = mul (mul M M) B from (mul_assoc M M B).symm]
  rw [this]

/-- **Propagation stagnates**: M² · B = M · B. -/
theorem propagation_stagnates {M : BoolMat n}
    (h : M.IsRankOne) (ht : M.trace = true) (B : BoolMat n) :
    mul (mul M M) B = mul M B := by
  rw [rank1_idempotent h ht]

/-- **Composition with idempotent is projection**: MAM = M for connected A. -/
theorem idempotent_absorbs_middle {M A : BoolMat n}
    (hM : M.IsRankOne) (hA : A.IsRankOne)
    (h_MA : ¬ IndDisjoint M.colSup A.rowSup)
    (h_AM : ¬ IndDisjoint A.colSup M.rowSup) :
    mul (mul M A) M = M :=
  rank1_rectangular hM hA h_MA h_AM

/-! ## Section 3: XOR Multiplication (GF(2)) -/

/-- XOR multiplication: C[i,j] = XOR_k (A[i,k] AND B[k,j]).
    Matrix multiplication over GF(2) = (ℤ/2ℤ, +, ×). -/
def xor_mul (A B : BoolMat n) : BoolMat n :=
  fun i j => (List.finRange n).foldl (fun acc k => xor acc (A i k && B k j)) false

/-! ## Section 4: Concrete Witness -/

/-- Witness: 2×2 all-true block in top-left of 8×8 matrix.
    M[i,j] = (i < 2) ∧ (j < 2). Rank-1 with trace = true. -/
private def wM : BoolMat 8 :=
  fun i j => decide (i.val < 2) && decide (j.val < 2)

/-- Boolean: M² = M (idempotent). Two 1s in each row of the 2×2 block,
    OR gives 1 → block preserved. -/
private theorem wM_isRankOne : wM.IsRankOne := by
  refine ⟨fun i => decide (i.val < 2), fun j => decide (j.val < 2), ?_, ?_, ?_⟩
  · exact ⟨⟨0, by omega⟩, by native_decide⟩
  · exact ⟨⟨0, by omega⟩, by native_decide⟩
  · intro i j
    simp only [wM]
    constructor
    · intro h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨by simp [decide_eq_true_eq]; exact h.1, by simp [decide_eq_true_eq]; exact h.2⟩
    · intro ⟨h1, h2⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by simpa [decide_eq_true_eq] using h1, by simpa [decide_eq_true_eq] using h2⟩

/-- The witness has boolean trace = true. -/
private theorem wM_trace : wM.trace = true := by native_decide

private theorem wM_bool_sq : mul wM wM = wM :=
  rank1_idempotent wM_isRankOne wM_trace

/-- GF(2): M² = 0 (nilpotent). Each diagonal entry = 1 XOR 1 = 0.
    Two matching 1s in each inner product → even count → XOR = 0. -/
private theorem wM_xor_sq_zero : isZero (xor_mul wM wM) := by native_decide

/-! ## Section 5: Main Theorems -/

/-- **Bool vs XOR dichotomy**: the SAME matrix is idempotent under boolean
    but nilpotent under GF(2). Formal version of T1's Band vs Nilpotent. -/
theorem bool_vs_xor_dichotomy :
    ∃ M : BoolMat 8,
      mul M M = M ∧                    -- boolean: idempotent
      isZero (xor_mul M M)             -- GF(2): nilpotent
    :=
  ⟨wM, wM_bool_sq, wM_xor_sq_zero⟩

/-- **1+1 determines fate**: same matrix, two algebras, opposite fixed points. -/
theorem one_plus_one_determines_fate :
    ∃ M : BoolMat 8,
      M.trace = true ∧                -- nontrivial (has diagonal)
      mul M M = M ∧                    -- 1+1=1 → stable (band)
      isZero (xor_mul M M)             -- 1+1=0 → annihilated (nilpotent)
    :=
  ⟨wM, wM_trace, wM_bool_sq, wM_xor_sq_zero⟩

/-- **XOR is more destructive**: boolean preserves (M²=M),
    GF(2) destroys (M²=0). Invertibility (GF(2) is a field) does NOT help —
    it makes things WORSE by enabling cancellation. -/
theorem xor_more_destructive :
    ∃ M : BoolMat 8,
      mul M M = M ∧                    -- boolean: information preserved
      isZero (xor_mul M M) ∧           -- GF(2): information destroyed
      ¬ isZero (mul M M)               -- boolean result is nontrivial
    := by
  refine ⟨wM, wM_bool_sq, wM_xor_sq_zero, ?_⟩
  rw [wM_bool_sq]
  intro h
  have : wM ⟨0, by omega⟩ ⟨0, by omega⟩ = false := h ⟨0, by omega⟩ ⟨0, by omega⟩
  have : wM ⟨0, by omega⟩ ⟨0, by omega⟩ = true := by native_decide
  contradiction

/-! ## Section 6: Barrier Strength -/

/-- **Gauss killed**: for idempotent M, the sequence M, M², M³, ...
    is constant from step 1. No spectral information to extract. -/
theorem idempotent_pow_constant {M : BoolMat n}
    (h : M.IsRankOne) (ht : M.trace = true) :
    mul M M = M :=
  rank1_idempotent h ht

/-- **Band semigroup = dead end**: for any idempotent M and any B,
    composing M·B·M gives back M. Information about B is erased. -/
theorem band_erases_middle {M B : BoolMat n}
    (hM : M.IsRankOne) (hB : B.IsRankOne)
    (h1 : ¬ IndDisjoint M.colSup B.rowSup)
    (h2 : ¬ IndDisjoint B.colSup M.rowSup) :
    mul (mul M B) M = M :=
  rank1_rectangular hM hB h1 h2

end BoolMat
