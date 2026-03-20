/-
  CubeGraph/AbstractCSP.lean
  F4.1: Rank decay is universal — not CubeGraph-specific.

  Key revelation: rowRank_mul_le is parametric over BoolMat n for ANY n.
  CubeGraph (k=3, n=8) is just one instantiation. Any boolean CSP with
  arity k uses BoolMat (2^k), and rank decay holds unconditionally.

  This establishes: rank decay is a property of the BOOLEAN SEMIRING
  operating on LOCAL CONSTRAINTS, not a property of CubeGraph specifically.

  Consequences:
  - Any boolean CSP has rank decay
  - 3-SAT is a boolean CSP → rank decay
  - Any NP-complete reduces to 3-SAT → rank decay applies to any NP-complete

  See: RowRank.lean (rowRank_mul_le — already parametric over n)
  See: RankMonotonicity.lean (foldl, absorbing — already parametric)
  See: BandwidthGap.lean (gap definition — on CubeGraph, generalizable)
  See: experiments-ml/022_.../F4.1-ORIGINAL-PLAN.md
-/

import CubeGraph.BandwidthGap

namespace BoolMat

/-! ## Section 1: Rank Decay is Universal -/

/-- **Universal Rank Decay**: for ANY dimension n, boolean matrix multiplication
    has monotonically non-increasing row-rank. This is NOT specific to n=8
    or to CubeGraph. It's a property of the boolean semiring (OR/AND).

    For a CSP with domain D and arity k: n = |D|^k.
    - 3-SAT: D={0,1}, k=3, n=8
    - 2-SAT: D={0,1}, k=2, n=4
    - k-SAT: D={0,1}, k=k, n=2^k
    - CSP over domain d, arity k: n=d^k -/
theorem universal_rank_decay (n : Nat) (A B : BoolMat n) :
    rowRank (mul A B) ≤ rowRank A :=
  rowRank_mul_le A B

/-- **Universal Rank Decay on Chains**: composing any sequence of boolean matrices
    can only decrease rank. Works for any dimension n. -/
theorem universal_chain_decay (n : Nat) (A : BoolMat n) (ms : List (BoolMat n)) :
    rowRank (ms.foldl mul A) ≤ rowRank A :=
  rowRank_foldl_le A ms

/-- **Universal Rank-1 Absorbing**: once rank reaches 1, it never recovers.
    True for any dimension n. -/
theorem universal_rank1_absorbing (n : Nat) (A : BoolMat n) (ms : List (BoolMat n))
    (h : rowRank A ≤ 1) :
    rowRank (ms.foldl mul A) ≤ 1 :=
  rowRank_foldl_le_of_head_le A ms 1 h

/-- **Universal Funnel**: rank ≤ k is preserved under multiplication.
    Once information narrows to k channels, it stays ≤ k. Any dimension n. -/
theorem universal_funnel (n : Nat) (A B : BoolMat n) (k : Nat)
    (h : rowRank A ≤ k) :
    rowRank (mul A B) ≤ k :=
  rowRank_funnel A B k h

/-! ## Section 2: Aperiodicity is Universal -/

/-- **Universal Aperiodicity**: rank-1 matrices satisfy M³=M² for any n.
    Not specific to n=8. The band semigroup structure is universal. -/
theorem universal_aperiodic {n : Nat} {M : BoolMat n} (h : M.IsRankOne) :
    mul M (mul M M) = mul M M :=
  rank1_aperiodic h

/-- **Universal Idempotency**: rank-1 with trace>0 gives M²=M for any n. -/
theorem universal_idempotent {n : Nat} {M : BoolMat n}
    (h : M.IsRankOne) (ht : M.trace = true) :
    mul M M = M :=
  rank1_idempotent h ht

/-! ## Section 3: CubeGraph as Special Case -/

/-- 3-SAT uses dimension 2³ = 8. -/
theorem sat3_dimension : (2 : Nat) ^ 3 = 8 := by decide

/-- 2-SAT uses dimension 2² = 4. -/
theorem sat2_dimension : (2 : Nat) ^ 2 = 4 := by decide

/-- k-SAT rank decay is an instance of universal rank decay with n = 2^k. -/
theorem ksat_rank_decay (k : Nat) (A B : BoolMat (2^k)) :
    rowRank (mul A B) ≤ rowRank A :=
  universal_rank_decay (2^k) A B

/-! ## Section 4: The Key Theorem -/

/-- **Rank decay is a property of the boolean semiring, not of CubeGraph.**

    This theorem collects the universal statements:
    1. Rank decay holds for ANY dimension (any CSP arity)
    2. Rank-1 is absorbing for ANY dimension
    3. Aperiodicity holds for ANY dimension
    4. Idempotency holds for ANY dimension

    CubeGraph (3-SAT, n=8) inherits all of these as special cases.
    Any boolean CSP inherits them with n = |D|^k.

    The ONLY things specific to 3-SAT at ρ_c are:
    - The specific witness (h2Graph)
    - The Borromean order b(n) = Θ(n) (empirical)
    - The treewidth tw = 3.07n (empirical)
    These are QUANTITATIVE, not QUALITATIVE. The qualitative rank decay
    is universal across all boolean CSPs. -/
theorem rank_decay_is_universal :
    -- For ANY dimension n:
    -- 1. Rank decays monotonically
    (∀ (n : Nat) (A B : BoolMat n), rowRank (mul A B) ≤ rowRank A) ∧
    -- 2. Rank decays on chains
    (∀ (n : Nat) (A : BoolMat n) (ms : List (BoolMat n)),
      rowRank (ms.foldl mul A) ≤ rowRank A) ∧
    -- 3. Rank-1 is absorbing
    (∀ (n : Nat) (A : BoolMat n) (ms : List (BoolMat n)),
      rowRank A ≤ 1 → rowRank (ms.foldl mul A) ≤ 1) ∧
    -- 4. Rank-1 is aperiodic (M³=M²)
    (∀ {n : Nat} {M : BoolMat n}, M.IsRankOne →
      mul M (mul M M) = mul M M) ∧
    -- 5. Rank-1 with trace>0 is idempotent (M²=M)
    (∀ {n : Nat} {M : BoolMat n}, M.IsRankOne → M.trace = true →
      mul M M = M) :=
  ⟨universal_rank_decay,
   universal_chain_decay,
   universal_rank1_absorbing,
   fun h => rank1_aperiodic h,
   fun h ht => rank1_idempotent h ht⟩

end BoolMat
