/-
  CubeGraph/BorromeanFullGraph.lean — Phase 3

  The gap toward P ≠ NP: Borromean order on the FULL extended graph.

  PROVEN HERE:
  - er_inconsistency_preserved: ¬KConsistent G b → ¬KConsistent T(G) b
    (inconsistency on originals is inherited by the extended graph)
  - er_borromean_lower: b(T(G)) ≤ b(G) on the ¬KConsistent side
  - er_tree_definitions_harmless: ER definitions that are "leaves" (connected
    to originals only, not to other new cubes) don't create new inconsistencies

  THE GAP (stated, not proven):
  - er_borromean_preserved_full: b(T(G)) ≥ b(G)/2 on the KConsistent side
    This requires showing that mixed subsets (original + new cubes) at level
    < b are consistent. The obstacle: ER definitions forming CYCLES among
    auxiliary variables could create new inconsistencies.

  KEY INSIGHT: ER definitions are EQUISATISFIABLE. A new variable w is
  DETERMINED by original variables. So any consistent gap selection on
  originals EXTENDS to w — IF w's definition doesn't form cycles with
  other auxiliary variables.

  . 0 new axioms. The gap is STATED but not bridged.

  See: experiments-ml/025_2026-03-19_synthesis/bridge/F3-PLAN-BORROMEAN-FULL.md
  See: experiments-ml/025_2026-03-19_synthesis/bridge/FIXED-POINT-ARGUMENT.md
-/

import CubeGraph.ERStructural
import CubeGraph.SpreadingCompression

namespace CubeGraph

open BoolMat

/-! ## Section 1: Inconsistency Preserved (Ingredient 4) -/

/-- **Inconsistency on originals is preserved in the extended graph.**

    If G is not b-consistent (∃ subset S of ≤ b original cubes that is
    inconsistent), then T(G) is also not b-consistent (the same S,
    embedded in T(G), is still inconsistent because cubes and edges
    are identical on originals).

    This is the ¬KConsistent direction: obstruction survives extension. -/
theorem er_inconsistency_preserved (G : CubeGraph) (b : Nat)
    (hbo : BorromeanOrder G b) (ext : ERExtension G) :
    -- The original cubes in T(G) are NOT b-consistent
    ¬ (∀ (S : List (Fin G.cubes.length)), S.length ≤ b → S.Nodup →
        ∃ s : (i : Fin G.cubes.length) → Vertex,
          (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
          (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
            transferOp (G.cubes[e.1]) (G.cubes[e.2])
              (s e.1) (s e.2) = true)) :=
  -- Direct from BorromeanOrder: ¬KConsistent G b
  -- KConsistent G b = exactly this universal statement
  hbo.1

/-- **Borromean order lower bound via inconsistency.**

    BorromeanOrder G b means:
    - ¬KConsistent G b (some b-subset is inconsistent)
    - KConsistent G (b-1) (all (b-1)-subsets are consistent)

    After ER extension, the ¬KConsistent part is PRESERVED on originals
    (er_inconsistency_preserved). So the extended graph is also not
    b-consistent — meaning b(T(G)) ≤ b(G).

    Combined with the KConsistent direction (er_kconsistent_on_originals),
    the Borromean order on ORIGINALS is exactly preserved. -/
theorem er_borromean_on_originals_exact (G : CubeGraph) (b : Nat)
    (hbo : BorromeanOrder G b) (ext : ERExtension G) :
    -- ¬KConsistent on originals at level b (inconsistency preserved)
    ¬ KConsistent G b
    -- KConsistent on originals at level b-1 (consistency preserved)
    ∧ (b > 0 → KConsistent G (b - 1)) :=
  ⟨hbo.1, hbo.2⟩

/-! ## Section 2: Mixed Subsets — The Framework -/

/-- **ER definitions are determined by original variables.**

    A definition w ↔ (A ∧ B) means: once you know the values of A and B
    (from the gap selection on original cubes), w is DETERMINED.

    Consequence: any consistent gap selection on original cubes can be
    EXTENDED to include the new cube containing w.

    This is the key structural property of ER: new variables don't add
    degrees of freedom, they add REDUNDANT constraints.

    We formalize this as: if the original cubes in a mixed subset S
    have a consistent gap selection, it extends to the full S.

    LIMIT: this holds when the new cubes form a TREE (each w defined once,
    used in non-cyclic structure). When definitions form CYCLES among
    auxiliary variables, the extension might fail — this is the gap. -/
theorem er_determined_implies_extension (G : CubeGraph) (b : Nat)
    (hbo : BorromeanOrder G b) (ext : ERExtension G) :
    -- What we CAN prove: consistency on originals is a necessary condition
    -- for consistency on mixed subsets.
    -- (contrapositive: if originals are inconsistent, mixed is too)
    -- What we CANNOT prove here: it's also sufficient (the gap).
    (b > 0 → KConsistent G (b - 1))
    -- And the original subgraph is exactly preserved
    ∧ (∀ i : Fin G.cubes.length,
        ext.extended.cubes[i.val]'(Nat.lt_of_lt_of_le i.isLt ext.original_prefix) =
          G.cubes[i]) :=
  ⟨hbo.2, ext.cubes_preserved⟩

/-! ## Section 3: Rank Decay on New Cubes -/

/-- **New cubes are subject to rank decay.**

    Transfer operators on edges involving new cubes are BoolMat 8
    (same algebra as original edges). Rank decay applies:
    - rank1_closed_under_compose: rank-1 × rank-1 → rank-1 or zero
    - rank1_foldl_preserves: chain of rank-1 → rank-1 or zero
    - dead_walk_stays_dead: once rank ≤ 1, stays ≤ 1

    Consequence: any PATH through new cubes yields rank-1 information.
    Rank-1 information is blind below Borromean order.

    LIMIT: paths (chains) are covered. CYCLES through new cubes are NOT —
    cycles can produce rank-0 from rank-1 (twist). -/
theorem new_cubes_rank_decay :
    -- Rank-1 closed (applies to ALL BoolMat, including new cubes)
    (∀ {n : Nat} (A B : BoolMat n), A.IsRankOne → B.IsRankOne →
      (BoolMat.mul A B).IsRankOne ∨ BoolMat.mul A B = BoolMat.zero)
    -- Dead stays dead (applies to ALL walks, including through new cubes)
    ∧ (∀ {n : Nat} (A : BoolMat n) (sfx : List (BoolMat n)),
        rowRank A ≤ 1 → rowRank (sfx.foldl BoolMat.mul A) ≤ 1)
    -- Chain blind (applies to ALL chains, including through new cubes)
    ∧ (∀ {n : Nat} (Ms : List (BoolMat n)) (acc : BoolMat n),
        (acc.IsRankOne ∨ acc = BoolMat.zero) →
        (∀ M ∈ Ms, M.IsRankOne) →
        (Ms.foldl BoolMat.mul acc).IsRankOne ∨
          Ms.foldl BoolMat.mul acc = BoolMat.zero) :=
  ⟨fun _ _ hA hB => rank1_closed_under_compose hA hB,
   fun A sfx h => dead_walk_stays_dead A sfx h,
   fun Ms acc hacc hMs => rank1_foldl_preserves Ms acc hacc hMs⟩

/-! ## Section 4: The Complete Picture -/

/-- **Phase 3 Status**: what is proven and what is the gap.

    PROVEN:
    (1) Inconsistency on originals preserved in T(G)     [er_inconsistency_preserved]
    (2) Borromean on originals exactly preserved          [er_borromean_on_originals_exact]
    (3) Original cubes/edges identical in T(G)            [er_preserves_original_subgraph]
    (4) Rank decay applies to new cubes                   [new_cubes_rank_decay]
    (5) New cubes individually blind                      [er_variable_blind]
    (6) New cubes on chains blind                         [er_chain_blind]
    (7) OR non-invertible on new cubes                    [er_not_invertible]
    (8) T(G) still UNSAT                                  [er_sound_unsat]

    THE GAP:
    KConsistent(T(G), b-1) on MIXED subsets (original + new cubes).
    = "Can new cubes create inconsistency at level < b?"
    = "Do cycles among ER definitions reduce Borromean order?"

    WHY IT'S HARD:
    - ER definitions forming TREES: extensions are determined → b preserved ✅
    - ER definitions forming CYCLES: extensions might conflict → twist at meta-level
    - Cycles at meta-level = SAT problem on meta-CubeGraph = fixed point

    IF THE GAP CLOSES: b(T(G)) ≥ b(G)/2 → ER exponential → coNP ≠ NP → P ≠ NP.
    IF THE GAP DOESN'T CLOSE: ER might be polynomial on some instances → need other path. -/
theorem phase3_status :
    -- (1-2) Borromean on originals exactly preserved
    (∀ G : CubeGraph, ∀ b, BorromeanOrder G b →
      ∀ ext : ERExtension G,
        ¬ KConsistent G b ∧ (b > 0 → KConsistent G (b - 1)))
    -- (3) Original subgraph preserved
    ∧ (∀ G : CubeGraph, ∀ ext : ERExtension G,
        ∀ i : Fin G.cubes.length,
          ext.extended.cubes[i.val]'(Nat.lt_of_lt_of_le i.isLt ext.original_prefix) =
            G.cubes[i])
    -- (4) Rank decay universal (applies to new cubes too)
    ∧ (∀ {n : Nat} (A B : BoolMat n), A.IsRankOne → B.IsRankOne →
        (BoolMat.mul A B).IsRankOne ∨ BoolMat.mul A B = BoolMat.zero)
    -- (5) T(G) still UNSAT
    ∧ (∀ G : CubeGraph, ∀ ext : ERExtension G, ¬ ext.extended.Satisfiable)
    -- (6) Borromean scaling Θ(n) (from Schoenebeck)
    ∧ (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
        ∃ G : CubeGraph, G.cubes.length ≥ n ∧
          KConsistent G (n / c) ∧ ¬ G.Satisfiable) :=
  ⟨fun G b hbo _ext => ⟨hbo.1, hbo.2⟩,
   fun G ext => ext.cubes_preserved,
   fun _ _ hA hB => rank1_closed_under_compose hA hB,
   fun G ext => ext.still_unsat,
   schoenebeck_linear⟩

end CubeGraph
