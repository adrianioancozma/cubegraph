-- CubeGraph/PartB.lean
-- Part B: Gap Lattice Structure
--
-- Formalizes the gap lattice and proves it does NOT distinguish SAT from UNSAT.
-- Key result: the gap lattice is trivially connected (complete graph on gaps).
--
-- WHY THIS MATTERS: The gap lattice was an early candidate for SAT/UNSAT
-- discrimination. This file proves the negative result: any two gaps in the
-- same cube are always adjacent, making the lattice trivially dense.
-- This rules out gap-lattice-based approaches (see DE1 in project-map/DEAD-ENDS.md).
--
-- See: theory/foundations/06-empty-vertex-duality.md (gap semantics)
-- See: theory/research/GAP-SHEAF-FORMALIZATION.md (sheaf reformulation)

import CubeGraph.Basic
import CubeGraph.Theorems

open CubeGraph

-- ## B.1: Gap Adjacency (inductive Prop for reliable parsing)

-- Two vertices in cube c are gap-adjacent iff both are gaps and they differ.
inductive GapAdj (c : Cube) : Vertex → Vertex → Prop where
  | mk : (hne : g1 ≠ g2) → (h1 : c.isGap g1 = true) → (h2 : c.isGap g2 = true) →
         GapAdj c g1 g2

-- GapAdj is symmetric.
theorem GapAdj.symm_prop (c : Cube) (g1 g2 : Vertex) : GapAdj c g1 g2 → GapAdj c g2 g1 := by
  intro h
  cases h with
  | mk hne h1 h2 => exact GapAdj.mk (Ne.symm hne) h2 h1

-- GapAdj is irreflexive.
theorem GapAdj.irrefl_prop (c : Cube) (g : Vertex) : ¬ GapAdj c g g := by
  intro h
  cases h with
  | mk hne _ _ => exact hne rfl

-- Decidability of GapAdj.
instance instDecidableGapAdj (c : Cube) (g1 g2 : Vertex) : Decidable (GapAdj c g1 g2) :=
  if hne : g1 = g2 then
    isFalse (fun h => GapAdj.irrefl_prop c g1 (hne ▸ h))
  else if h1 : c.isGap g1 = true then
    if h2 : c.isGap g2 = true then
      isTrue (GapAdj.mk hne h1 h2)
    else
      isFalse (fun h => by cases h with | mk _ _ hg2 => exact h2 hg2)
  else
    isFalse (fun h => by cases h with | mk _ hg1 _ => exact h1 hg1)

-- ## B.2: Reachability (Equal or Adjacent)

-- Two gap vertices are gap-reachable iff they are equal or directly adjacent.
inductive GapReachable (c : Cube) : Vertex → Vertex → Prop where
  | refl : GapReachable c g g
  | step : GapAdj c g1 g2 → GapReachable c g1 g2

-- Reflexivity of gap reachability.
theorem gapReachable_refl (c : Cube) (g : Vertex) : GapReachable c g g :=
  GapReachable.refl

-- Symmetry of gap reachability.
theorem gapReachable_symm (c : Cube) (g1 g2 : Vertex) :
    GapReachable c g1 g2 → GapReachable c g2 g1 := by
  intro h
  cases h with
  | refl => exact GapReachable.refl
  | step hadj => exact GapReachable.step (GapAdj.symm_prop c g1 g2 hadj)

-- ## B.3: Connectivity Predicate

-- A cube's gap lattice is connected iff any two gap vertices are gap-reachable.
def latticeConnected (c : Cube) : Prop :=
  ∀ g1 g2 : Vertex,
    c.isGap g1 = true →
    c.isGap g2 = true →
    GapReachable c g1 g2

-- ## B.4: Transfer Operator and Gap Membership

-- A true transfer entry implies both endpoints are gaps.
theorem transferOp_implies_gaps (c1 c2 : Cube) (g1 g2 : Vertex)
    (h : transferOp c1 c2 g1 g2 = true) :
    c1.isGap g1 = true ∧ c2.isGap g2 = true := by
  simp only [transferOp, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2⟩

-- Gaps plus variable compatibility implies the transfer entry is true.
theorem gaps_and_compat_implies_transferOp (c1 c2 : Cube) (g1 g2 : Vertex)
    (hg1 : c1.isGap g1 = true) (hg2 : c2.isGap g2 = true)
    (hcompat : (Cube.sharedVars c1 c2).all (fun sv =>
                ((g1.val >>> c1.vars.idxOf sv) &&& 1) ==
                ((g2.val >>> c2.vars.idxOf sv) &&& 1)) = true) :
    transferOp c1 c2 g1 g2 = true := by
  simp only [transferOp, Bool.and_eq_true]
  exact ⟨⟨hg1, hg2⟩, hcompat⟩

-- ## B.5: Trivial Connectivity

-- Distinct gap vertices in c are GapAdj-connected.
theorem gap_lattice_adj (c : Cube) (g1 g2 : Vertex)
    (hg1 : c.isGap g1 = true) (hg2 : c.isGap g2 = true) (hne : g1 ≠ g2) :
    GapAdj c g1 g2 :=
  GapAdj.mk hne hg1 hg2

-- The gap lattice is trivially connected.
-- NEGATIVE RESULT: gap lattice connectivity is always true, regardless of SAT/UNSAT.
theorem gap_lattice_trivially_connected (c : Cube) (g1 g2 : Vertex)
    (hg1 : c.isGap g1 = true) (hg2 : c.isGap g2 = true) :
    GapReachable c g1 g2 := by
  by_cases hne : g1 = g2
  · subst hne; exact GapReachable.refl
  · exact GapReachable.step (GapAdj.mk hne hg1 hg2)

-- Every cube has a connected gap lattice.
theorem gap_lattice_connected (c : Cube) : latticeConnected c :=
  fun g1 g2 hg1 hg2 => gap_lattice_trivially_connected c g1 g2 hg1 hg2

-- ## B.6: Universal Connectivity = No Discriminating Power

-- ALL cubes in ANY CubeGraph have connected gap lattices.
-- Gap lattice connectivity cannot detect UNSAT.
theorem all_cubes_lattice_connected (G : CubeGraph) :
    ∀ i : Fin G.cubes.length, latticeConnected (G.cubes[i]) :=
  fun i => gap_lattice_connected (G.cubes[i])

-- ## B.7: Original Conjecture is FALSE

-- "UNSAT implies disconnected gap lattice" is FALSE.
-- Every cube has a connected gap lattice, even in UNSAT graphs.
theorem gap_lattice_not_unsat_witness :
    ∀ G : CubeGraph, ∀ i : Fin G.cubes.length, latticeConnected (G.cubes[i]) :=
  fun G i => gap_lattice_connected (G.cubes[i])

-- ## B.8: Correct UNSAT Witness

-- A blocked edge: transferOp is zero on that edge.
def blockedEdge (G : CubeGraph) (i j : Fin G.cubes.length) : Prop :=
  ∀ g1 g2 : Vertex,
    transferOp (G.cubes[i]) (G.cubes[j]) g1 g2 = false

-- Blocked edge certifies UNSAT (inter-cube incompatibility; invisible to gap lattice).
theorem blocked_edge_implies_unsat (G : CubeGraph)
    (i j : Fin G.cubes.length) (he : (i, j) ∈ G.edges)
    (hblocked : blockedEdge G i j) :
    ¬ G.Satisfiable :=
  rank_zero_unsat G i j he hblocked
