/-
  CubeGraph/SpreadingCompression.lean

  Pas 2: Compression dominates spreading.

  IF a channel becomes dead (rowRank ≤ 1) at any step,
  THEN it stays dead for ALL subsequent steps.

  0 axioms. 0 sorry. Uses only existing theorems.

  See: D2-SPREADING-COMPRESSION-RESULTS.md (τ_rank ≈ 4 < τ_mix ≈ 13)
  See: RankMonotonicity.lean (rowRank_foldl_le_one)
-/

import CubeGraph.SublinearER

namespace CubeGraph

open BoolMat

/-! ## Section 1: Dead at step τ → dead forever -/

/-- **Dead stays dead on walks**: If the accumulated composition has
    rowRank ≤ 1, composing ANY further matrices keeps rowRank ≤ 1. -/
theorem dead_walk_stays_dead {n : Nat} (A : BoolMat n)
    (sfx : List (BoolMat n))
    (hdead : rowRank A ≤ 1) :
    rowRank (sfx.foldl mul A) ≤ 1 :=
  rowRank_foldl_le_one A sfx hdead

/-- Splitting a walk: dead on first part → dead on whole walk. -/
theorem dead_first_implies_dead_whole {n : Nat}
    (pfx sfx : List (BoolMat n))
    (hdead : rowRank (pfx.foldl mul one) ≤ 1) :
    rowRank ((pfx ++ sfx).foldl mul one) ≤ 1 := by
  rw [List.foldl_append]
  exact rowRank_foldl_le_one (pfx.foldl mul one) sfx hdead

/-! ## Section 2: Parametric compression theorem -/

/-- **Compression dominates spreading** (parametric):
    If the walk becomes dead at step τ_rank (rowRank ≤ 1),
    then the full walk is dead — regardless of remaining steps.

    Condition τ_rank < walk.length verified experimentally (D2). -/
theorem compression_dominates {n : Nat}
    (walk : List (BoolMat n))
    (τ_rank : Nat)
    (hlen : τ_rank ≤ walk.length)
    (hdead : rowRank ((walk.take τ_rank).foldl mul one) ≤ 1) :
    rowRank (walk.foldl mul one) ≤ 1 := by
  have hsplit : walk.take τ_rank ++ walk.drop τ_rank = walk := List.take_append_drop τ_rank walk
  rw [← hsplit]
  exact dead_first_implies_dead_whole (walk.take τ_rank) (walk.drop τ_rank) hdead

/-! ## Section 3: Complete argument -/

/-- **Spreading vs Compression Summary**: 6 components, all proven.

    (1) Dead stays dead (rowRank ≤ 1 preserved under composition)
    (2) Dead first part → dead whole walk
    (3) Per observation: ≤ 8 bits (boolTraceCount_le_eight)
    (4) k observations: ≤ 8k bits (total_bool_bounded)
    (5) Borromean gap (h2Graph, b = 3)
    (6) Borromean scales Θ(n) (Schoenebeck)

    CONDITIONAL on τ_rank < τ_mix (verified: D2 experiment, ratio 1.5→3.5). -/
theorem spreading_compression_summary :
    -- (1) Dead stays dead
    (∀ {n : Nat} (A : BoolMat n) (sfx : List (BoolMat n)),
      rowRank A ≤ 1 → rowRank (sfx.foldl mul A) ≤ 1)
    -- (2) Dead first → dead whole
    ∧ (∀ {n : Nat} (pfx sfx : List (BoolMat n)),
        rowRank (pfx.foldl mul one) ≤ 1 →
        rowRank ((pfx ++ sfx).foldl mul one) ≤ 1)
    -- (3) Per observation: ≤ 8 bits
    ∧ (∀ M : BoolMat 8, NatMat.boolTraceCount M ≤ 8)
    -- (4) k observations: ≤ 8k bits
    ∧ (∀ obs : List (BoolMat 8),
        NatMat.listNatSum (obs.map NatMat.boolTraceCount) ≤ 8 * obs.length)
    -- (5) Borromean gap
    ∧ InformationGap h2Graph 3
    -- (6) Borromean scales
    ∧ (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
        ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
          KConsistent G (n / c)) := by
  refine ⟨fun A sfx h => dead_walk_stays_dead A sfx h,
         fun pfx sfx h => dead_first_implies_dead_whole pfx sfx h,
         boolTraceCount_le_eight,
         total_bool_bounded,
         h2_information_gap,
         ?_⟩
  obtain ⟨c, hc, h⟩ := width_linear_from_schoenebeck
  exact ⟨c, hc, fun n hn => by
    obtain ⟨G, hG, hu, hkc, _⟩ := h n hn
    exact ⟨G, hG, hu, hkc⟩⟩

end CubeGraph
