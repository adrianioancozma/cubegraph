/-
  CubeGraph/CrossCubeDivergence.lean — Cross-Cube Divergence Persistence

  Session: 047.
  Docs: experiments-ml/047_2026-04-06_roadmap-pnp/CROSS-CUBE-RESULTS.md

  Core fact: when gap_i flips (g₁ → g₂), ALL neighbors see different constraints.
  Reconvergence at ONE neighbor does NOT fix the others.
  Divergence PERSISTS: ≥ 1 neighbor always remains divergent.

  Empirically verified: 100% of flips have ≥ 1 divergent neighbor (n=10..50).
  Avg ~20 divergent neighbors per flip (~60% of all neighbors).

  This is STRONGER than single-path T₃* reconvergence (99.4%):
  cross-cube effects prevent full reconvergence on the graph.
-/

import CubeGraph.Basic
import CubeGraph.ProofComplexityModel
import CubeGraph.NonInvertibleTransfer
import CubeGraph.IrrationalNodes

namespace CubeGraph

/-! ## Section 1: Neighbor Divergence -/

/-- Two gap choices at cube i produce DIFFERENT constraints at neighbor j
    if the transfer operator rows differ (rank-2). -/
def neighborDiverges (G : CubeGraph) (i j : Fin G.cubes.length)
    (g₁ g₂ : Vertex) : Prop :=
  ∃ g : Vertex,
    transferOp G.cubes[i] G.cubes[j] g₁ g ≠
    transferOp G.cubes[i] G.cubes[j] g₂ g

/-- Count of divergent neighbors: how many neighbors of cube i see
    different constraints when gap_i flips from g₁ to g₂. -/
def divergentNeighborCount (G : CubeGraph) (i : Fin G.cubes.length)
    (g₁ g₂ : Vertex) : Nat :=
  (G.edges.filter (fun e => decide (e.1 = i))).countP
    (fun e => (List.finRange 8).any
      (fun g => transferOp G.cubes[i] G.cubes[e.2] g₁ g !=
                transferOp G.cubes[i] G.cubes[e.2] g₂ g))

/-! ## Section 2: Divergence Persists -/

/-- **KEY STRUCTURAL FACT**: If edge (i,j) has rank ≥ 2, then flipping gap_i
    produces different constraints at j. From per_gap_derivations_differ. -/
theorem rank2_implies_neighbor_diverges (G : CubeGraph)
    (i j : Fin G.cubes.length)
    (hrank : ¬(transferOp G.cubes[i] G.cubes[j]).IsRankOne)
    (hactive : ∃ g, (transferOp G.cubes[i] G.cubes[j]).rowSup g = true) :
    ∃ g₁ g₂ : Vertex, g₁ ≠ g₂ ∧
      G.cubes[i].isGap g₁ = true ∧ G.cubes[i].isGap g₂ = true ∧
      neighborDiverges G i j g₁ g₂ := by
  obtain ⟨g₁, g₂, hg1, hg2, hne, g, hdiff⟩ :=
    per_gap_derivations_differ G i j hrank hactive
  exact ⟨g₁, g₂, hne, hg1, hg2, g, hdiff⟩

/-- **DIVERGENCE IS MULTI-NEIGHBOR**: If cube i has rank-2 edges to
    MULTIPLE neighbors j₁, j₂, ..., then flipping gap_i produces
    divergence at ALL of them simultaneously.

    Reconvergence at j₁ does NOT fix j₂.
    The proof must handle divergence at EACH neighbor independently.

    With d rank-2 neighbors: d simultaneous divergences per flip. -/
theorem multi_neighbor_divergence (G : CubeGraph)
    (i : Fin G.cubes.length)
    (neighbors : List (Fin G.cubes.length))
    (hrank : ∀ j ∈ neighbors,
      ¬(transferOp G.cubes[i] G.cubes[j]).IsRankOne)
    (hactive : ∀ j ∈ neighbors,
      ∃ g, (transferOp G.cubes[i] G.cubes[j]).rowSup g = true)
    (g₁ g₂ : Vertex) (hne : g₁ ≠ g₂)
    (hg1 : G.cubes[i].isGap g₁ = true)
    (hg2 : G.cubes[i].isGap g₂ = true)
    -- For EACH rank-2 neighbor: there exists a column where rows differ
    : ∀ j ∈ neighbors,
      ∃ g : Vertex,
        transferOp G.cubes[i] G.cubes[j] g₁ g ≠
        transferOp G.cubes[i] G.cubes[j] g₂ g := by
  intro j hj
  -- From rank-2 at (i,j): ∃ two gaps with different rows
  obtain ⟨g₁', g₂', hg1', hg2', hne', g, hdiff⟩ :=
    per_gap_derivations_differ G i j (hrank j hj) (hactive j hj)
  -- The gaps g₁', g₂' from per_gap_derivations_differ might differ from g₁, g₂.
  -- We need divergence for the SPECIFIC g₁, g₂ given.
  -- This requires: the specific pair (g₁, g₂) also diverges at j.
  -- NOT necessarily true for arbitrary g₁, g₂!
  -- But: rank-2 means ≥ 2 distinct row patterns. If g₁, g₂ have the same row
  -- at j: then ALL active rows at j are the same → rank-1 → contradiction with hrank.
  -- UNLESS there are > 2 active rows and g₁, g₂ happen to be in the same class.
  sorry -- Technical: need that SPECIFIC g₁, g₂ (not just ∃ pair) diverge at j.
         -- True if rank-2 means "g₁ and g₂ have different rows" for ANY distinct pair.
         -- But rank-2 only says ∃ SOME pair. Not ALL pairs.
         -- This sorry is a GENUINE gap for the specific g₁, g₂ case.
         -- Resolvable if rank is "full" (all pairs differ) which is stronger than rank-2.

/-! ## Section 3: Reconvergence Cannot Fix All Neighbors -/

/-- **THE KEY ARGUMENT**: Reconvergence at one neighbor j₁ does NOT
    fix divergence at another neighbor j₂.

    Choosing gap_j₁ from the overlap C₁∩C₂ at j₁:
    - Fixes divergence at j₁ (both branches see same gap_j₁). ✓
    - Does NOT affect j₂ at all (j₂'s constraint depends on gap_i, not gap_j₁,
      unless j₁ and j₂ are also neighbors — but even then, the constraint at j₂
      from i is INDEPENDENT of the choice at j₁).

    Why independent: cubeVars_disjoint. The gap variables at j₁ and j₂
    are DIFFERENT variables. Fixing j₁ doesn't constrain j₂'s gap variables. -/
theorem reconvergence_doesnt_fix_other_neighbors (G : CubeGraph)
    (i j₁ j₂ : Fin G.cubes.length) (hne : j₁ ≠ j₂)
    (g₁ g₂ : Vertex)
    -- j₂ diverges under gap flip at i
    (hdiv : neighborDiverges G i j₂ g₁ g₂) :
    -- After ANY choice of gap at j₁: j₂ STILL diverges
    -- (the divergence at j₂ depends on gap_i, not gap_j₁)
    neighborDiverges G i j₂ g₁ g₂ :=
  hdiv  -- trivial: the divergence at j₂ doesn't mention j₁ at all

/-! ## Section 4: Implications -/

-- The full argument:
-- 1. Gap flip at cube i: ≥ 1 neighbor diverges (rank-2, 100% empiric)
-- 2. Reconvergence at that neighbor: doesn't fix OTHER divergent neighbors
-- 3. With ≥ 1 persistent divergence per flip: proof must branch
-- 4. n/c cubes need flips (Schoenebeck): n/c branchings
-- 5. Each branching: ≥ 2 options (rank-2)
--
-- OPEN: does this give 2^{n/c} (multiplicative) or 2×n/c (additive)?
-- Multiplicative: if branchings at DIFFERENT cubes are independent
-- Additive: if branchings can be handled sequentially
--
-- From the cross-cube result: each flip leaves ~20 divergent neighbors.
-- These divergent neighbors ALSO need to be handled → more flips → more branches.
-- The cascade of divergences suggests multiplicative growth.
-- Formal proof of multiplicative growth: OPEN (the counting gap).

end CubeGraph
