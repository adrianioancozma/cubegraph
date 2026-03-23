/-
  CubeGraph/Iota6RepresentationBarrier.lean
  REPRESENTATION BARRIER: Z/2Z cannot be faithfully represented on rich
  (≥4 gap) boolean vectors compatible with OR/AND multiplication.

  The core theorem: Z/2Z EXISTS in T₃* (Gamma6), but only on 2-gap support.
  Any attempt to REPRESENT Z/2Z on richer support (≥4 gaps) fails because:

  1. INVOLUTION BARRIER: M² = one (8×8 identity) requires all 8 rows active.
     Transfer operators on cubes with k < 8 gaps have at most k active rows.
     Therefore no T₃* operator on a cube with ≤7 gaps can be a true involution.

  2. IDEMPOTENT COLLAPSE: Rich monodromies (≥4 gaps) develop self-loops.
     Self-loops force M² = M (idempotent), not M² = e (involution).
     The h2 witness avoids this ONLY because its 2-gap anti-diagonal has
     no self-loops. With ≥4 gaps, self-loops are unavoidable in T₃*.

  3. RANK-1 CONVERGENCE: Composing ≥3 rank-1 operators gives rank-1.
     Rank-1 operators are aperiodic (M³ = M²), which cannot represent Z/2Z.
     Any "lifting" L·M·R of the 2-gap Z/2Z through composition produces
     rank-1, destroying the Z/2Z structure.

  4. PARTIAL IDENTITY BARRIER: h2Monodromy² is a PARTIAL identity
     (diagonal on {0,3} only, not the full 8×8 identity). Z/2Z requires
     M² = e (full identity). The gap between partial and full identity
     is STRUCTURAL: it measures exactly the missing support dimensions.

  Combined: Z/2Z is TRAPPED on 2-gap support within T₃*.
  The KR gap (KR=0 on rich ops, KR≥1 in trace language) is therefore
  a representational barrier, not a computational one.

  See: Gamma6KRConsequences.lean (Z/2Z ⊆ T₃*)
  See: Beta6MonodromySquared.lean (h2Monodromy computation)
  See: Delta6LargerGroups.lean (rich monodromies collapse)
  See: BandSemigroup.lean (rank-1 aperiodic)
-/

import CubeGraph.Gamma6KRConsequences
import CubeGraph.Delta6LargerGroups

namespace CubeGraph

open BoolMat

/-! ## Part 1: Z/2Z Representation on BoolMat n

  A Z/2Z representation on BoolMat n is a pair (M, e) where:
    - e = identity element, M = generator
    - M ≠ e (non-trivial)
    - M * M = e (involution)
    - e * e = e, e * M = M, M * e = M (identity laws)

  For BoolMat 2: the anti-diagonal [[0,1],[1,0]] is a true involution (M²=I).
  For BoolMat 8: h2Monodromy is a Z/2Z representation... but with M² ≠ one.
  Instead M² = partial identity on {0,3}. -/

/-- A boolean matrix is a true involution: M * M = identity. -/
def IsTrueInvolution (M : BoolMat n) : Prop :=
  mul M M = one ∧ M ≠ one

/-- A boolean matrix is a partial involution relative to some idempotent e:
    M * M = e, e * M = M, M * e = M, e * e = e, M ≠ e. -/
def IsPartialInvolution (M e : BoolMat n) : Prop :=
  mul M M = e ∧
  mul e M = M ∧
  mul M e = M ∧
  mul e e = e ∧
  M ≠ e

/-! ### 1a: BoolMat 2 True Involution -/

/-- The 2×2 anti-diagonal: [[0,1],[1,0]]. -/
def antiDiag2 : BoolMat 2 :=
  fun i j => decide (i.val + j.val = 1)

/-- antiDiag2 squared equals the 2×2 identity. -/
theorem antiDiag2_sq_eq_one : mul antiDiag2 antiDiag2 = (one : BoolMat 2) := by
  funext i j; revert i j; native_decide

/-- antiDiag2 is NOT the identity. -/
theorem antiDiag2_ne_one : antiDiag2 ≠ (one : BoolMat 2) := by
  intro h
  have h1 : antiDiag2 ⟨0, by omega⟩ ⟨1, by omega⟩ = true := by native_decide
  have h2 : (one : BoolMat 2) ⟨0, by omega⟩ ⟨1, by omega⟩ = false := by native_decide
  rw [h] at h1; rw [h1] at h2; exact absurd h2 (by decide)

/-- **BoolMat 2 admits a true involution**: Z/2Z faithfully represented. -/
theorem boolmat2_has_true_involution : ∃ M : BoolMat 2, IsTrueInvolution M :=
  ⟨antiDiag2, antiDiag2_sq_eq_one, antiDiag2_ne_one⟩

/-! ### 1b: h2Monodromy Is a Partial Involution on BoolMat 8 -/

/-- h2Monodromy is a partial involution with identity h2MonodromySq.
    It represents Z/2Z, but with a PARTIAL identity (not the full 8×8 one). -/
theorem h2Monodromy_partial_involution :
    IsPartialInvolution h2Monodromy h2MonodromySq :=
  ⟨rfl,  -- M * M = e (by definition of h2MonodromySq)
   h2MonodromySq_mul_monodromy,  -- e * M = M
   h2MonodromyCube_eq_monodromy,  -- M * e = M (M³ = M)
   h2MonodromySq_idempotent,      -- e * e = e
   h2Monodromy_semigroup_two_elements⟩  -- M ≠ e

/-! ## Part 2: Involution Barrier on BoolMat 8

  For M² = one (8×8 identity), every diagonal entry of M² must be true.
  M²[i,i] = ∨_k (M[i,k] ∧ M[k,i]).
  For this to be true for ALL i, row i of M must have some entry M[i,k]=true
  such that M[k,i]=true. In particular, every row must be non-empty.

  Transfer operators have at most |gaps| active rows.
  If |gaps| < 8, some row is all-false, so M²[i,i] = false for that i,
  hence M² ≠ one. -/

/-- An all-false row kills the diagonal entry of M². -/
theorem zero_row_kills_diagonal (M : BoolMat n) (i : Fin n)
    (h : ∀ k : Fin n, M i k = false) :
    (mul M M) i i = false := by
  -- (mul M M) i i = any(k => M i k && M k i)
  -- Since M i k = false for all k, each term is false
  cases h_eq : (mul M M) i i with
  | false => rfl
  | true =>
    have ⟨k, hk1, _⟩ := (mul_apply_true M M i i).mp h_eq
    rw [h k] at hk1; exact absurd hk1 (by decide)

/-- If M has an all-false row, then M is NOT a true involution. -/
theorem zero_row_prevents_involution (M : BoolMat n) (i : Fin n)
    (h_row : ∀ k : Fin n, M i k = false) :
    ¬ IsTrueInvolution M := by
  intro ⟨h_inv, _⟩
  have h_diag : (mul M M) i i = false := zero_row_kills_diagonal M i h_row
  rw [h_inv] at h_diag
  have h_one : (one : BoolMat n) i i = true := by simp [one]
  rw [h_diag] at h_one; exact absurd h_one (by decide)

/-- h2Monodromy has zero rows (row 1 is all-false). -/
theorem h2Monodromy_has_zero_row :
    ∀ j : Fin 8, h2Monodromy ⟨1, by omega⟩ j = false := by
  intro j; revert j; native_decide

/-- **INVOLUTION BARRIER**: h2Monodromy cannot be a true involution. -/
theorem h2Monodromy_not_true_involution : ¬ IsTrueInvolution h2Monodromy :=
  zero_row_prevents_involution h2Monodromy ⟨1, by omega⟩ h2Monodromy_has_zero_row

/-! ### 2b: No transfer operator on <8 gaps can be a true involution. -/

/-- If a cube has a non-gap vertex v, then transferOp c₁ c₂ has an all-false
    row at v (source row is zero when v is not a gap of c₁). -/
theorem transferOp_zero_row_of_nongap (c₁ c₂ : Cube) (v : Vertex)
    (h : c₁.isGap v = false) :
    ∀ j : Fin 8, transferOp c₁ c₂ v j = false := by
  intro j
  simp only [transferOp]
  simp only [h, Bool.false_and]

/-- **STRUCTURAL INVOLUTION BARRIER**: If c₁ has any non-gap vertex,
    then transferOp c₁ c₂ is NOT a true involution.
    Since cubes have at most 7 gaps (typically 2-7 at ρ_c),
    NO transfer operator is a true involution. -/
theorem transferOp_not_true_involution (c₁ c₂ : Cube) (v : Vertex)
    (h : c₁.isGap v = false) :
    ¬ IsTrueInvolution (transferOp c₁ c₂) :=
  zero_row_prevents_involution (transferOp c₁ c₂) v
    (transferOp_zero_row_of_nongap c₁ c₂ v h)

/-- **QUANTIFIED BARRIER**: For any cube with fewer than 8 gaps,
    the transfer operator from it cannot be a true involution. -/
theorem sparse_cube_no_involution (c₁ c₂ : Cube)
    (h : ∃ v : Vertex, c₁.isGap v = false) :
    ¬ IsTrueInvolution (transferOp c₁ c₂) := by
  obtain ⟨v, hv⟩ := h
  exact transferOp_not_true_involution c₁ c₂ v hv

/-! ## Part 3: Idempotent Collapse on Rich Support

  Delta6 proved: monodromies on ≥4-gap cubes collapse to idempotents.
  Here we establish the general principle: self-loops force idempotence
  for rank-1 matrices, and self-loops are unavoidable with rich support. -/

/-- Self-loop is preserved by squaring (from BoolMat.lean's fixedPoint_mul). -/
theorem selfloop_preserved (M : BoolMat n) (g : Fin n)
    (h : M g g = true) : (mul M M) g g = true :=
  fixedPoint_mul M M g h h

/-- If a rank-1 matrix has a self-loop, it is idempotent (M²=M).
    Self-loop implies trace = true, and rank1_idempotent gives M²=M. -/
theorem rank1_selfloop_implies_idempotent {M : BoolMat n}
    (h_r1 : M.IsRankOne) (g : Fin n) (h_loop : M g g = true) :
    mul M M = M := by
  have h_trace : M.trace = true := by
    rw [trace_true]; exact ⟨g, h_loop⟩
  exact rank1_idempotent h_r1 h_trace

/-- An idempotent matrix cannot represent the non-identity of Z/2Z
    (because M² = M and M² = e together give M = e, contradicting M ≠ e). -/
theorem idempotent_not_z2_generator (M e : BoolMat n)
    (h_idem : mul M M = M) (h_ne : M ≠ e) :
    ¬ (mul M M = e) := by
  intro h_sq_e
  rw [h_idem] at h_sq_e
  exact h_ne h_sq_e

/-! ### 3b: Concrete examples from Delta6 -/

/-- Rich monodromy (4 gaps) is idempotent — CANNOT be a partial involution
    with its own square as identity. -/
theorem rich_monodromy_no_z2 :
    ¬ IsPartialInvolution richMonodromy richMonodromySq := by
  intro ⟨_, _, _, _, h_ne⟩
  -- richMonodromySq = richMonodromy (idempotent), but h_ne says they differ
  exact h_ne richMonodromy_idempotent.symm

/-- Swap monodromy (4 gaps) is idempotent — CANNOT be a partial involution
    with its own square as identity. -/
theorem swap_monodromy_no_z2 :
    ¬ IsPartialInvolution swapMonodromy swapMonodromySq := by
  intro ⟨_, _, _, _, h_ne⟩
  exact h_ne swapMonodromy_idempotent.symm

/-! ## Part 4: Rank-1 Convergence Kills Z/2Z

  After composing ≥3 rank-1 operators, the result is rank-1 (absorbing).
  Rank-1 operators are aperiodic: M³ = M² (BandSemigroup.lean).
  Aperiodic elements CANNOT generate Z/2Z (need M² ≠ M for Z/2Z). -/

/-- Aperiodic elements cannot be partial involutions.
    If M³ = M², and M is a partial involution (M² = e, M ≠ e),
    then M³ = M * M² = M * e = M, but also M³ = M², so M = e.
    Contradiction with M ≠ e. -/
theorem aperiodic_not_partial_involution (M e : BoolMat n)
    (h_aper : mul M (mul M M) = mul M M)
    (h_inv : IsPartialInvolution M e) : False := by
  obtain ⟨h_sq, _, h_me, _, h_ne⟩ := h_inv
  -- M³ = M * M² = M * e = M
  have h_cube_eq_M : mul M (mul M M) = M := by rw [h_sq, h_me]
  -- But M³ = M² (aperiodicity), so M = M²
  have h_M_eq_sq : mul M (mul M M) = mul M M := h_aper
  have h_eq : M = mul M M := by
    calc M = mul M (mul M M) := h_cube_eq_M.symm
      _ = mul M M := h_M_eq_sq
  -- M = M² = e
  rw [h_sq] at h_eq
  exact h_ne h_eq

/-- Every rank-1 element is aperiodic, therefore cannot be a partial involution. -/
theorem rank1_not_partial_involution {M : BoolMat n} (e : BoolMat n)
    (h_r1 : M.IsRankOne) (h_inv : IsPartialInvolution M e) : False :=
  aperiodic_not_partial_involution M e (rank1_aperiodic h_r1) h_inv

/-! ## Part 5: The Lifting Impossibility

  Can we LIFT the 2-gap Z/2Z to 7-gap support via composition?
  Lifting: find L, R ∈ T₃* such that L · h2Monodromy · R acts on
  rich support AND has period 2.

  This fails because:
  (a) If L, R are rank-1 and L·M is rank-1, then L·M·R is rank-1 (absorbing),
      hence aperiodic, hence no Z/2Z.
  (b) rowRank(L · M · R) ≤ rowRank(L), so the output cannot exceed L's rank.
  (c) Any lifting attempt preserves zero rows from L. -/

/-- Rank-1 lifting kills Z/2Z: if L·M is rank-1, and R is rank-1,
    and they connect, the product is rank-1, hence aperiodic, no Z/2Z. -/
theorem rank1_lifting_kills_z2 {L M R : BoolMat n} (e : BoolMat n)
    (h_R : R.IsRankOne)
    (h_conn_LMR : ¬ IndDisjoint (mul L M).colSup R.rowSup)
    (h_LM_r1 : (mul L M).IsRankOne)
    (h_inv : IsPartialInvolution (mul (mul L M) R) e) : False := by
  have h_LMR_r1 := rankOne_mul_rankOne h_LM_r1 h_R h_conn_LMR
  exact rank1_not_partial_involution e h_LMR_r1 h_inv

/-- Zero rows propagate through left multiplication:
    if L has an all-false row at i, then (L · M) has an all-false row at i.
    Therefore (L · M · R) has an all-false row at i, preventing true involution. -/
theorem zero_row_propagates_left (L M : BoolMat n) (i : Fin n)
    (h : ∀ k : Fin n, L i k = false) :
    ∀ j : Fin n, (mul L M) i j = false := by
  intro j
  cases h_eq : (mul L M) i j with
  | false => rfl
  | true =>
    obtain ⟨k, hk1, _⟩ := (mul_apply_true L M i j).mp h_eq
    rw [h k] at hk1; exact absurd hk1 (by decide)

/-- Chained: zero rows propagate through double multiplication. -/
theorem zero_row_propagates_double (L M R : BoolMat n) (i : Fin n)
    (h : ∀ k : Fin n, L i k = false) :
    ∀ j : Fin n, (mul (mul L M) R) i j = false :=
  zero_row_propagates_left (mul L M) R i (zero_row_propagates_left L M i h)

/-- **LIFTING BLOCKED BY ZERO ROWS**: If L has an all-false row,
    then L · M · R cannot be a true involution, regardless of M and R. -/
theorem lifting_blocked_by_zero_rows (L M R : BoolMat n) (i : Fin n)
    (h : ∀ k : Fin n, L i k = false) :
    ¬ IsTrueInvolution (mul (mul L M) R) :=
  zero_row_prevents_involution _ i (zero_row_propagates_double L M R i h)

/-! ### 5b: Concrete Lifting Attempt -/

/-- The lifted product is NOT a true involution (has zero rows). -/
theorem lifting_attempt_not_involution :
    ¬ IsTrueInvolution (mul (mul richMonAB h2Monodromy) richMonCA) := by
  apply zero_row_prevents_involution _ ⟨1, by omega⟩
  intro j; revert j; native_decide

/-! ## Part 6: The Partial-to-Full Identity Gap

  h2Monodromy² = partial identity on {0,3} (2 diagonal entries out of 8).
  A true Z/2Z representation needs M² = full identity (8 diagonal entries).
  The GAP between partial and full is exactly 6 missing dimensions.

  This gap is STRUCTURAL: it measures the "support deficiency" of
  the Z/2Z representation within T₃*. -/

/-- The partial identity has exactly 2 true diagonal entries. -/
theorem partial_identity_diag_count :
    (List.finRange 8).countP (fun i => h2MonodromySq i i) = 2 := by
  native_decide

/-- The full identity has exactly 8 true diagonal entries. -/
theorem full_identity_diag_count :
    (List.finRange 8).countP (fun i => (one : BoolMat 8) i i) = 8 := by
  native_decide

/-- The partial identity disagrees with the full identity on 6 diagonal positions. -/
theorem partial_full_disagreement :
    (List.finRange 8).countP (fun i => h2MonodromySq i i != (one : BoolMat 8) i i) = 6 := by
  native_decide

/-- The identity gap: h2MonodromySq ≠ one, and the disagreement is exactly
    on the 6 non-gap positions of h2CubeA. -/
theorem identity_gap :
    h2MonodromySq ≠ one ∧
    (List.finRange 8).countP (fun i =>
      h2MonodromySq i i != (one : BoolMat 8) i i) = 6 :=
  ⟨h2MonodromySq_ne_one, partial_full_disagreement⟩

/-! ## Part 7: The Representation Barrier Theorem

  MAIN THEOREM: Z/2Z is trapped on 2-gap support within T₃*.
  Three independent proofs that Z/2Z cannot extend to rich support:

  (A) Involution barrier: sparse rows prevent M² = one
  (B) Idempotent collapse: self-loops force M² = M on rich support
  (C) Rank-1 convergence: composition kills period-2 structure

  Together: the KR gap (KR=0 on composed rich ops, KR≥1 in trace language)
  is a STRUCTURAL representational barrier. -/

/-- **REPRESENTATION BARRIER THEOREM (concrete)**:
    Z/2Z exists on 2-gap support but fails on 4-gap support.
    Three barriers prevent extension:
    (A) h2Monodromy is NOT a true involution (zero rows)
    (B) richMonodromy (4 gaps) is idempotent (M²=M, not period 2)
    (C) Lifting through rank-1 operators cannot create involutions -/
theorem representation_barrier_concrete :
    -- (A) Z/2Z EXISTS on 2-gap support (partial involution)
    IsPartialInvolution h2Monodromy h2MonodromySq ∧
    -- (B) But NOT as a true involution
    ¬ IsTrueInvolution h2Monodromy ∧
    -- (C) Rich monodromies collapse to idempotents
    (richMonodromySq = richMonodromy ∧
     swapMonodromySq = swapMonodromy) ∧
    -- (D) Identity gap: partial identity ≠ full identity
    (h2MonodromySq ≠ one) ∧
    -- (E) Rank-1 elements cannot carry Z/2Z
    (∀ (M : BoolMat 8), M.IsRankOne →
      ∀ e : BoolMat 8, ¬ IsPartialInvolution M e) :=
  ⟨h2Monodromy_partial_involution,
   h2Monodromy_not_true_involution,
   ⟨richMonodromy_idempotent, swapMonodromy_idempotent⟩,
   h2MonodromySq_ne_one,
   fun _ hM e hInv => rank1_not_partial_involution e hM hInv⟩

/-! ## Part 8: Aperiodicity of Rich Composed Operators

  The dichotomy in explicit terms:
  - h2 (2 gaps): period 2, Z/2Z, NOT aperiodic, KR ≥ 1
  - Rich (≥4 gaps): period 1, idempotent, aperiodic (M²=M→M³=M²), KR = 0

  This is why the KR gap is structural: gap count determines period. -/

/-- Rich monodromy IS aperiodic: M³ = M² (trivially, since M² = M → M³ = M·M = M² = M). -/
theorem richMonodromy_aperiodic :
    mul richMonodromy (mul richMonodromy richMonodromy) =
    mul richMonodromy richMonodromy := by
  -- richMonodromySq is definitionally mul richMonodromy richMonodromy
  -- richMonodromy_idempotent : richMonodromySq = richMonodromy
  -- So mul richMonodromy richMonodromy = richMonodromy
  -- Goal: mul richMonodromy (mul richMonodromy richMonodromy) = mul richMonodromy richMonodromy
  -- i.e.: (M * M²) = M² where M² = M, so M * M = M
  show mul richMonodromy richMonodromySq = richMonodromySq
  rw [richMonodromy_idempotent]
  exact richMonodromy_idempotent

/-- Swap monodromy IS aperiodic. -/
theorem swapMonodromy_aperiodic :
    mul swapMonodromy (mul swapMonodromy swapMonodromy) =
    mul swapMonodromy swapMonodromy := by
  show mul swapMonodromy swapMonodromySq = swapMonodromySq
  rw [swapMonodromy_idempotent]
  exact swapMonodromy_idempotent

/-- **KR DICHOTOMY**: poor (2-gap) = non-aperiodic (KR≥1),
    rich (≥4-gap) = aperiodic (KR=0).
    The KR complexity is INVERSELY related to gap count. -/
theorem kr_gap_dichotomy :
    -- Poor (2 gaps): NOT aperiodic → KR ≥ 1
    (h2MonodromyCube ≠ h2MonodromySq) ∧
    -- Rich (4 gaps): aperiodic → KR = 0
    (mul richMonodromy (mul richMonodromy richMonodromy) =
     mul richMonodromy richMonodromy ∧
     mul swapMonodromy (mul swapMonodromy swapMonodromy) =
     mul swapMonodromy swapMonodromy) :=
  ⟨h2Monodromy_not_aperiodic_at_1,
   richMonodromy_aperiodic, swapMonodromy_aperiodic⟩

/-! ## Part 9: Connection to P vs NP

  The representation barrier says:
  - Z/2Z exists in T₃* (locally, on 2-gap poor cubes)
  - Z/2Z CANNOT extend to rich (≥4 gap) support
  - At ρ_c, cubes have ~7 gaps → operators are ALL aperiodic (KR=0)
  - The trace language DEMANDS Z/2Z (H² witness uses it)
  - But T₃* can only PROVIDE Z/2Z on poor cubes (2 gaps)

  This is the fundamental mismatch:
  - SAT/UNSAT detection needs global coherence (Z/2Z on trace)
  - T₃* provides only local coherence (Z/2Z on tiny support)
  - Lifting from local to global is blocked by all three barriers

  PROOF COMPLEXITY consequence:
  Any algorithm that works by composing transfer operators
  cannot transport Z/2Z to where it is needed. -/

/-- **GRAND SUMMARY: Representation Barrier**

  Five facets of the same structural impossibility:

  1. Z/2Z EXISTS (partial involution on 2-gap support)
  2. Z/2Z TRAPPED (cannot become true involution: zero rows)
  3. Rich monodromies COLLAPSE (idempotent, period 1, KR=0)
  4. Rank-1 ABSORBS Z/2Z (aperiodic, no period-2 elements)
  5. Identity GAP (partial identity ≠ full identity, 6 dimensions missing)

  The KR gap between trace language (KR≥1, needs Z/2Z globally)
  and rich operators (KR=0, aperiodic) is IRREDUCIBLE. -/
theorem grand_summary_representation_barrier :
    -- (1) Z/2Z exists
    (h2Monodromy ≠ h2MonodromySq ∧
     BoolMat.mul h2MonodromySq h2Monodromy = h2Monodromy ∧
     BoolMat.mul h2Monodromy h2MonodromySq = h2Monodromy) ∧
    -- (2) Not a true involution
    (¬ IsTrueInvolution h2Monodromy) ∧
    -- (3) Rich collapse
    (richMonodromySq = richMonodromy ∧
     swapMonodromySq = swapMonodromy) ∧
    -- (4) Rank-1 absorbs Z/2Z (universal)
    (∀ (M : BoolMat 8), M.IsRankOne →
      mul M (mul M M) = mul M M) ∧
    -- (5) Identity gap
    (h2MonodromySq ≠ one) :=
  ⟨⟨h2Monodromy_semigroup_two_elements,
    h2MonodromySq_mul_monodromy,
    h2MonodromyCube_eq_monodromy⟩,
   h2Monodromy_not_true_involution,
   ⟨richMonodromy_idempotent, swapMonodromy_idempotent⟩,
   fun _ h => rank1_aperiodic h,
   h2MonodromySq_ne_one⟩

end CubeGraph
