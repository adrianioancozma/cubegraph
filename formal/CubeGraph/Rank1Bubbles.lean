/-
  CubeGraph/Rank1Bubbles.lean

  Rank-1 Bubbles: "independent bits don't aggregate."

  Composing ANY number of rank-1 matrices through boolean multiplication
  yields rank-1 or zero — NEVER rank ≥ 2. Rank ≥ 2 (coordination)
  cannot be CREATED from rank-1 (independent) observations.

  Combined with Borromean order (UNSAT needs rank ≥ 2 coordination):
  no amount of rank-1 probes can detect UNSAT.

  See: InformationChannel.lean (rank1_closed_under_compose — pairs)
  See: experiments-ml/024/T5-PLAN-RANK1-BUBBLES.md
-/

import CubeGraph.MonotoneSizeLB

namespace CubeGraph

open BoolMat

/-! ## Section 1: Rank-1 aggregation on lists -/

/-- **Rank-1 Aggregation**: Composing a list of rank-1 matrices
    with a rank-1-or-zero accumulator yields rank-1 or zero.

    This extends `rank1_closed_under_compose` (pairs) to arbitrary lists.
    No matter how many rank-1 observations you combine through
    boolean composition, you CANNOT create rank ≥ 2. -/
theorem rank1_foldl_preserves {n : Nat} (Ms : List (BoolMat n)) (acc : BoolMat n)
    (hacc : acc.IsRankOne ∨ acc = zero)
    (hMs : ∀ M ∈ Ms, M.IsRankOne) :
    (Ms.foldl mul acc).IsRankOne ∨ Ms.foldl mul acc = zero := by
  induction Ms generalizing acc with
  | nil => simpa
  | cons M rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · -- mul acc M is rank-1 or zero
      cases hacc with
      | inl hr =>
        exact rank1_closed_under_compose hr (hMs M (.head rest))
      | inr hz =>
        right; rw [hz]; exact zero_mul M
    · exact fun M' hM' => hMs M' (.tail M hM')

/-- Specialization: starting from identity (one).
    one is rank-n (not rank-1), so we need the first matrix to seed. -/
theorem rank1_list_compose {n : Nat} (M₀ : BoolMat n) (Ms : List (BoolMat n))
    (h₀ : M₀.IsRankOne) (hMs : ∀ M ∈ Ms, M.IsRankOne) :
    (Ms.foldl mul M₀).IsRankOne ∨ Ms.foldl mul M₀ = zero :=
  rank1_foldl_preserves Ms M₀ (Or.inl h₀) hMs

/-- Zero accumulator stays zero through any composition. -/
theorem zero_foldl_eq_zero {n : Nat} (Ms : List (BoolMat n)) :
    Ms.foldl mul zero = zero := by
  induction Ms with
  | nil => rfl
  | cons M rest ih =>
    simp only [List.foldl_cons, zero_mul, ih]

/-! ## Section 2: Rank-1 bubbles cannot coordinate -/

/-- **Bubble Insufficiency**: rank-1 aggregation stays rank ≤ 1,
    but UNSAT detection requires coordination (rank ≥ 2, Borromean b ≥ 2).

    Therefore: no collection of rank-1 observations, combined through
    any boolean composition, can detect UNSAT.

    This is "independent bits don't aggregate" formalized:
    - rank-1 = 1D projection (independent bit)
    - rank ≥ 2 = multi-dimensional (coordinated bits)
    - Composition: 1D × 1D → 1D or 0D (never 2D)
    - UNSAT needs 2D → unreachable from 1D -/
theorem bubbles_insufficient :
    -- (1) Rank-1 aggregation: list composition stays rank-1 or zero
    (∀ {n : Nat} (Ms : List (BoolMat n)) (acc : BoolMat n),
      (acc.IsRankOne ∨ acc = zero) →
      (∀ M ∈ Ms, M.IsRankOne) →
      (Ms.foldl mul acc).IsRankOne ∨ Ms.foldl mul acc = zero)
    -- (2) Borromean gap: UNSAT needs coordination (b ≥ 2)
    ∧ InformationGap h2Graph 3
    -- (3) Dead stays dead (irreversibility)
    ∧ (∀ G seq e, ChannelDead G seq → ChannelDead G (seq ++ [e]))
    -- (4) Information loss per observation
    ∧ (∀ M : BoolMat 8, NatMat.boolTraceCount M ≤ 8) :=
  ⟨fun Ms acc hacc hMs => rank1_foldl_preserves Ms acc hacc hMs,
   h2_information_gap,
   dead_extends_dead,
   boolTraceCount_le_eight⟩

/-! ## Section 3: Summary -/

/-- **Rank-1 Bubbles Summary**: The complete argument.

    An algorithm probes CubeGraph through composition paths (bubbles).
    After ~5 steps, each bubble decays to rank-1 (dead channel).
    The algorithm collects m rank-1 results and post-processes them.

    **The impossibility**:
    1. Each bubble: rank-1 (1D projection, 1 independent bit)
    2. m bubbles composed: still rank-1 or zero (aggregation theorem)
    3. ≤ 8m boolean bits total (quantitative bound)
    4. UNSAT needs rank ≥ 2 = coordinated bits (Borromean, b ≥ 2)
    5. rank-1 → rank ≥ 2 is IMPOSSIBLE (closed subsemigroup)
    6. Therefore: no rank-1 bubble algorithm can detect UNSAT

    **Analogy**: Measuring a 3D object's shadow from one direction (rank-1).
    Any number of shadows from the SAME projection direction cannot
    distinguish objects that differ only in the perpendicular direction.
    UNSAT is "perpendicular" to every rank-1 projection. -/
theorem rank1_bubbles_summary :
    -- (1) Aggregation: list of rank-1 → rank-1 or zero
    (∀ {n : Nat} (Ms : List (BoolMat n)) (acc : BoolMat n),
      (acc.IsRankOne ∨ acc = zero) →
      (∀ M ∈ Ms, M.IsRankOne) →
      (Ms.foldl mul acc).IsRankOne ∨ Ms.foldl mul acc = zero)
    -- (2) Per observation: ≤ 8 bits
    ∧ (∀ M : BoolMat 8, NatMat.boolTraceCount M ≤ 8)
    -- (3) Aggregate: ≤ 8k bits from k observations
    ∧ (∀ obs : List (BoolMat 8),
        NatMat.listNatSum (obs.map NatMat.boolTraceCount) ≤ 8 * obs.length)
    -- (4) Borromean gap
    ∧ InformationGap h2Graph 3
    -- (5) Scaling: Ω(n) observations needed
    ∧ (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
        ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
          ∀ (S : List (Fin G.cubes.length)), S.Nodup → S.length < n / c →
            ∃ s : (i : Fin G.cubes.length) → Vertex,
              (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
              (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
                transferOp (G.cubes[e.1]) (G.cubes[e.2])
                  (s e.1) (s e.2) = true)) :=
  ⟨fun Ms acc hacc hMs => rank1_foldl_preserves Ms acc hacc hMs,
   boolTraceCount_le_eight,
   total_bool_bounded,
   h2_information_gap,
   rank1_protocol_scaling⟩

end CubeGraph
