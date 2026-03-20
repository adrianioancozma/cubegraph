/-
  CubeGraph/MUS.lean
  Minimal Unsatisfiable Subgraphs (MUS) in CubeGraphs.

  Main results:
  - IsMinimalUnsatisfiable: first Lean definition of MUS for CubeGraphs
  - mus_cubes_ge_two: a MUS has at least 2 cubes
  - mus_ac_no_leaves: MUS + AC → every node has degree ≥ 2 (KEY NOVELTY)
  - mus_ac_not_forest: MUS + AC → not a forest (corollary)

  The key insight: mus_ac_no_leaves is STRONGER than h2_requires_cycles
  (Locality.lean) — per-node property (degree ≥ 2) rather than just a
  global property (not a forest). A MUS is a "2-core" where the
  obstruction is distributed across ALL nodes.

  See: experiments-ml/011_2026-03-05_polynomial-barriers/PLAN-L4-MUS-CYCLE.md
  See: theory/theorems/THEOREM-A-HIERARCHY.md
-/

import CubeGraph.LeafTrimming

namespace CubeGraph

/-! ## Section 1: Minimal Unsatisfiable Subgraph Definition -/

/-- A CubeGraph is a Minimal Unsatisfiable Subgraph (MUS) if it is
    unsatisfiable, but removing any single node makes it satisfiable.
    Every cube participates in the obstruction.

    The condition `G.cubes.length ≥ 2` is needed because `removeNode`
    requires it. For graphs with < 2 cubes, minimality is vacuously true
    (but such graphs are always SAT — see `mus_cubes_ge_two`). -/
def IsMinimalUnsatisfiable (G : CubeGraph) : Prop :=
  ¬ G.Satisfiable ∧
  ∀ (i : Fin G.cubes.length) (h : G.cubes.length ≥ 2),
    (G.removeNode i h).Satisfiable

/-! ## Section 2: MUS Size Bound -/

/-- Self-loop compatibility: transferOp c c g g = true for any gap g.
    (Reproduced from Locality.lean where it is private.) -/
private theorem transferOp_self_gap' (c : Cube) (g : Vertex)
    (hg : c.isGap g = true) :
    transferOp c c g g = true := by
  simp only [transferOp, hg, Bool.true_and]
  rw [List.all_eq_true]
  intro sv _
  simp

/-- A MUS has at least 2 cubes. With fewer than 2 cubes, every graph is
    satisfiable: each cube has gaps (invariant), and all edges are
    self-loops which are trivially compatible. -/
theorem mus_cubes_ge_two (G : CubeGraph)
    (h_mus : IsMinimalUnsatisfiable G) :
    G.cubes.length ≥ 2 := by
  refine Classical.byContradiction fun h => ?_
  have h_lt : G.cubes.length < 2 := by omega
  apply h_mus.1
  -- Construct a satisfying selection for a graph with < 2 cubes
  have hgaps : ∀ i : Fin G.cubes.length,
      ∃ v : Vertex, (G.cubes[i]).isGap v = true := by
    intro i
    have hgp : (G.cubes[i]).gapCount > 0 := by
      have := Cube.gapCount_pos (G.cubes[i]); omega
    rw [Cube.gapCount_pos_iff] at hgp
    obtain ⟨v, _, hv⟩ := hgp
    exact ⟨v, hv⟩
  refine ⟨fun i => Classical.choose (hgaps i),
         fun i => Classical.choose_spec (hgaps i),
         fun e _ => ?_⟩
  -- With < 2 cubes, e.1 = e.2 (self-loop)
  have he1 : e.1 = e.2 := by
    ext; have := e.1.isLt; have := e.2.isLt; omega
  simp only [he1]
  exact transferOp_self_gap' (G.cubes[e.2]) _
    (Classical.choose_spec (hgaps e.2))

/-! ## Section 3: MUS + AC → No Leaves (KEY NOVELTY)

  Stronger than `h2_requires_cycles` (Locality.lean):
  - h2_requires_cycles: forest + AC → ¬ UNSATType2 (global)
  - mus_ac_no_leaves: MUS + AC → ∀ i, degree(i) ≥ 2 (per-node)

  Proof: if node i were a leaf, MUS minimality gives (removeNode i) SAT.
  By removeLeaf_sat_equiv (backward), SAT lifts to G via AC.
  But G is UNSAT — contradiction. -/

/-- **Key theorem**: An arc-consistent MUS has no leaves.
    Every node has degree ≥ 2 — the MUS is a "2-core". -/
theorem mus_ac_no_leaves (G : CubeGraph)
    (h_ac : AllArcConsistent G)
    (h_mus : IsMinimalUnsatisfiable G) :
    ∀ i : Fin G.cubes.length, ¬ G.isLeaf i := by
  intro i h_leaf
  have h_len : G.cubes.length ≥ 2 := mus_cubes_ge_two G h_mus
  -- MUS minimality: removing i gives SAT
  have h_sub_sat : (G.removeNode i h_len).Satisfiable := h_mus.2 i h_len
  -- removeLeaf_sat_equiv backward: SAT lifts from subgraph to G
  have h_sat : G.Satisfiable :=
    (removeLeaf_sat_equiv G i h_len h_leaf h_ac).mpr h_sub_sat
  -- Contradiction with UNSAT
  exact h_mus.1 h_sat

/-! ## Section 4: MUS + AC → Not a Forest -/

/-- An arc-consistent MUS is not a forest.
    (Weaker than mus_ac_no_leaves, but connects to h2_requires_cycles.) -/
theorem mus_ac_not_forest (G : CubeGraph)
    (h_ac : AllArcConsistent G)
    (h_mus : IsMinimalUnsatisfiable G) :
    ¬ IsForest G :=
  fun h_forest => h_mus.1 (forest_arc_consistent_sat G h_forest h_ac)

/-! ## Section 5: Connection to H² Hierarchy

  For an H²-UNSAT CubeGraph G with AllArcConsistent:
  - Sub-CubeGraphs inherit AC (removeNode_preserves_allAC, iterated)
  - Any MUS extracted from G has no leaves (mus_ac_no_leaves)
  - Therefore every MUS contains a cycle

  The MUS is a "2-core": every node is essential (MUS) AND
  well-connected (degree ≥ 2). The obstruction is democratic.
  Experimentally: participation entropy H > 0.94 (Experiment 002). -/

end CubeGraph
