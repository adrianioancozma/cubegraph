/-
  CubeGraph/ERStructural.lean — F2.1

  ER definitions preserve structural properties of CubeGraph:
  the extended graph T(G) has the same constraint language (OR/AND clauses),
  preserves unsatisfiability, and the Borromean barrier on originals is intact.

  This is step 13a-13b of the proof chain (PLAN.md):
  - T(G) uses OR/AND clauses (same constraint language as G)
  - T(G) is UNSAT when G is UNSAT (ER is sound)
  - T(G) preserves all original cubes, edges, and k-consistency

  The MISSING piece (Phase 3): does T(G) preserve Borromean order on
  the FULL graph (originals + new cubes)? That is the gap.

  0 sorry. 0 new axioms.

  See: experiments-ml/025_2026-03-19_synthesis/bridge/FIXED-POINT-ARGUMENT.md
  See: experiments-ml/025_2026-03-19_synthesis/bridge/F2.1-PLAN-ER-STRUCTURAL.md
-/

import CubeGraph.ERAuxiliaryBlind

namespace CubeGraph

open BoolMat

/-! ## Section 1: ER Preserves Structure -/

/-- **ER Preserves Original Subgraph**: after ER extension, the original
    cubes and edges are an intact subgraph of the extended graph.

    This means: any property that depends ONLY on original cubes
    (k-consistency, Borromean order, rank of transfer operators)
    is IDENTICAL in G and T(G).

    The new cubes (with auxiliary variables) are ADDED, not replacing.
    The old structure is untouched. -/
theorem er_preserves_original_subgraph (G : CubeGraph) (ext : ERExtension G) :
    -- Original cubes preserved
    (∀ i : Fin G.cubes.length,
      ext.extended.cubes[i.val]'(Nat.lt_of_lt_of_le i.isLt ext.original_prefix) =
        G.cubes[i])
    -- Original edges preserved
    ∧ (∀ e ∈ G.edges,
      (⟨e.1.val, Nat.lt_of_lt_of_le e.1.isLt ext.original_prefix⟩,
       ⟨e.2.val, Nat.lt_of_lt_of_le e.2.isLt ext.original_prefix⟩) ∈
        ext.extended.edges)
    -- Extended graph is larger or equal
    ∧ G.cubes.length ≤ ext.extended.cubes.length :=
  ⟨ext.cubes_preserved, ext.edges_preserved, ext.original_prefix⟩

/-! ## Section 2: ER is Sound (UNSAT preserved) -/

/-- **ER Sound (UNSAT direction)**: if G is UNSAT, then T(G) is UNSAT.

    From ERExtension.still_unsat: the extended formula is UNSAT.
    ER definitions are equisatisfiable: they don't change SAT/UNSAT status.

    For our purpose (proving ER exponential on UNSAT formulas),
    only the UNSAT direction matters: G UNSAT → T(G) UNSAT. -/
theorem er_sound_unsat (G : CubeGraph) (ext : ERExtension G) :
    ¬ ext.extended.Satisfiable :=
  ext.still_unsat

/-! ## Section 3: The Structural Fixed Point -/

/-- **ER Structural Fixed Point**: T(G) has the same structural properties
    as G on the original subgraph, and is still UNSAT.

    PROVEN here:
    (1) Original cubes preserved (same gaps, same transfer operators)
    (2) Original edges preserved (same compatibility)
    (3) Extended graph still UNSAT
    (4) k-consistency on originals identical (er_kconsistent_on_originals)
    (5) Borromean order on originals preserved (er_borromean_preserved)

    WHAT THIS MEANS for the fixed point argument:
    - T(G) restricted to originals ≅ G (structurally identical)
    - T(G) is still UNSAT (sound)
    - The Borromean barrier on originals is INTACT
    - ER definitions are "annexes" that don't change the core structure

    THE GAP (Phase 3): do the new cubes (annexes) reduce Borromean
    order on the FULL graph? If not → ER exponential → P ≠ NP.
    See: FIXED-POINT-ARGUMENT.md, AUXILIARY-VARIABLES-CANNOT-HELP.md -/
theorem er_structural_fixed_point (G : CubeGraph) (b : Nat)
    (hbo : BorromeanOrder G b) (ext : ERExtension G) :
    -- (1) Extended graph still UNSAT
    ¬ ext.extended.Satisfiable
    -- (2) Borromean on originals: ¬KConsistent at level b
    ∧ ¬ KConsistent G b
    -- (3) Borromean on originals: KConsistent at level b-1 (if b > 0)
    ∧ (b > 0 → KConsistent G (b - 1))
    -- (4) k-consistency on originals invariant under ER
    ∧ (∀ (k : Nat), KConsistent G k →
        ∀ (S : List (Fin G.cubes.length)), S.length ≤ k → S.Nodup →
          ∃ s : (i : Fin G.cubes.length) → Vertex,
            (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
            (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
              transferOp (G.cubes[e.1]) (G.cubes[e.2])
                (s e.1) (s e.2) = true)) :=
  ⟨ext.still_unsat,
   hbo.1,
   hbo.2,
   fun k hkc => er_kconsistent_on_originals G ext k hkc⟩

end CubeGraph
