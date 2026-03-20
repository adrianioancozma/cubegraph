/-
  CubeGraph/Locality.lean
  The Locality Theorem: H² has no local witness.

  MAIN RESULT (h2_requires_cycles):
    An arc-consistent forest cannot be H².
    Equivalently: H² obstruction lives exclusively in cycles.

  This is the topological core of the CubeGraph framework:
  - Trees/forests: local consistency (AC) implies global consistency (SAT)
  - Cycles: local consistency does NOT imply global consistency
  - H² = the gap between local and global — invisible to any acyclic check

  PROOF CHAIN:
    forest_arc_consistent_sat: forest + AC → SAT  (TreeSAT.lean)
    h2_requires_cycles: forest + AC → ¬H²         (direct corollary)
    h2_kernel_nontrivial: H² + AC → kernel ≥ 2    (cyclic kernel exists)
    h2_is_purely_global: H² + AC → full statement  (4-part conjunction)

  NOTE on isAcyclic vs IsForest:
    `isAcyclic` (|E| < |V|) does NOT imply `IsForest` for disconnected graphs.
    Example: n-1 nodes forming a cycle + 1 isolated node has |E| = n-1 < n = |V|
    but contains a cycle. `IsForest` (leaf-peelable) is the correct notion.
    All theorems here use `IsForest`, not `isAcyclic`.

  See: theory/theorems/THEOREM-A-HIERARCHY.md (H⁰/H¹/H² classification)
  See: theory/foundations/05-cycles.md (cycle structure)
  See: theory/theorems/LOCALITY-THEOREM.md (mathematical statement and context)
  See also: CubeGraph/MUS.lean (mus_ac_no_leaves STRENGTHENS h2_requires_cycles:
    per-node degree ≥ 2, not just "not a forest")
-/

import CubeGraph.HierarchyTheorems

namespace CubeGraph

/-! ## Section 1: The Locality Theorem

  On forests (acyclic graphs), arc consistency implies satisfiability.
  Therefore H² — UNSAT without any local witness — cannot occur on forests.
  H² lives exclusively in the cycle structure of the CubeGraph. -/

/-- **H² requires cycles**: an arc-consistent forest cannot be H².

    This is the topological core of the CubeGraph framework.
    On forests, local consistency (AC) implies global consistency (SAT).
    H² obstruction — UNSAT with no dead cubes, no blocked edges — exists
    ONLY when the graph contains cycles.

    Proof: forest + AC → SAT (TreeSAT.lean), contradicting ¬Satisfiable in H². -/
theorem h2_requires_cycles (G : CubeGraph)
    (h_forest : IsForest G)
    (h_ac : AllArcConsistent G) :
    ¬ UNSATType2 G := by
  intro ⟨h_unsat, _, _⟩
  exact h_unsat (forest_arc_consistent_sat G h_forest h_ac)

/-- **Equivalent positive formulation**: every arc-consistent forest is satisfiable.
    (Wrapper around forest_arc_consistent_sat for clarity.) -/
theorem forest_ac_sat (G : CubeGraph)
    (h_forest : IsForest G)
    (h_ac : AllArcConsistent G) :
    G.Satisfiable :=
  forest_arc_consistent_sat G h_forest h_ac

/-! ## Section 2: Small Graph Satisfiability

  A graph with fewer than 2 cubes is always satisfiable:
  - 0 cubes: vacuously (no constraints to satisfy)
  - 1 cube: pick any gap; self-loops compare each bit with itself

  This supports the cyclic kernel theorem below. -/

/-- Self-loop compatibility: transferOp c c g g = true for any gap g.
    Each shared variable comparison reduces to x == x for some bit x. -/
theorem transferOp_self_gap (c : Cube) (g : Vertex)
    (hg : c.isGap g = true) :
    transferOp c c g g = true := by
  simp only [transferOp, hg, Bool.true_and]
  rw [List.all_eq_true]
  intro sv _
  simp

/-- A CubeGraph with fewer than 2 cubes is always satisfiable. -/
private theorem small_graph_sat (G : CubeGraph)
    (h : G.cubes.length < 2) : G.Satisfiable := by
  -- Every cube has a gap (from gaps_nonempty invariant)
  have hgaps : ∀ i : Fin G.cubes.length, ∃ v : Vertex, (G.cubes[i]).isGap v = true := by
    intro i
    have hgp : (G.cubes[i]).gapCount > 0 := by
      have := Cube.gapCount_pos (G.cubes[i]); omega
    rw [Cube.gapCount_pos_iff] at hgp
    obtain ⟨v, _, hv⟩ := hgp
    exact ⟨v, hv⟩
  refine ⟨fun i => Classical.choose (hgaps i),
         fun i => Classical.choose_spec (hgaps i),
         fun e _ => ?_⟩
  -- With < 2 cubes, e.1 and e.2 must be equal (both Fin 0 or both Fin 1)
  have he1 : e.1 = e.2 := by ext; have := e.1.isLt; have := e.2.isLt; omega
  simp only [he1]
  exact transferOp_self_gap (G.cubes[e.2]) _ (Classical.choose_spec (hgaps e.2))

/-! ## Section 3: The Cyclic Kernel

  After leaf trimming (polynomial, preserves AC and SAT), the remaining
  "cyclic kernel" has no leaves. If the original graph was H², the kernel
  is non-trivial (≥ 2 nodes) and still H². The H² obstruction lives
  entirely in this kernel — the cyclic part of the graph. -/

/-- **H² implies the cyclic kernel is non-trivial** (≥ 2 nodes).
    If the kernel had ≤ 1 node, it would be trivially satisfiable
    (pick any gap — self-loops are compatible), contradicting UNSAT. -/
theorem h2_kernel_nontrivial (G : CubeGraph) (h_ac : AllArcConsistent G)
    (h_unsat : ¬ G.Satisfiable) :
    (fullTrimming G).cubes.length ≥ 2 := by
  refine Classical.byContradiction fun h_not => ?_
  have h_small : (fullTrimming G).cubes.length < 2 := by omega
  have h_kernel_unsat := (fullTrimming_kernel_h2 G h_ac h_unsat).1
  exact h_kernel_unsat (small_graph_sat (fullTrimming G) h_small)

/-! ## Section 4: The Full Locality Statement -/

/-- **H² is purely global**: under arc consistency, H² means:
    (1) Every cube has gaps — no local (node-level) obstruction
    (2) No blocked edges — no local (edge-level) obstruction
    (3) The cyclic kernel is non-trivial — cycles exist
    (4) The kernel itself is H² — the obstruction lives in cycles

    In other words: every node passes, every edge passes, every tree passes,
    but the system as a whole fails. The obstruction is purely topological. -/
theorem h2_is_purely_global (G : CubeGraph) (h_ac : AllArcConsistent G)
    (h2 : UNSATType2 G) :
    -- (1) Every cube has gaps (no dead cubes)
    (∀ i : Fin G.cubes.length, (G.cubes[i]).gapCount > 0) ∧
    -- (2) Every edge has compatible pairs (no blocked edges)
    (¬ HasBlockedEdge G) ∧
    -- (3) The cyclic kernel is non-trivial (has ≥ 2 nodes)
    ((fullTrimming G).cubes.length ≥ 2) ∧
    -- (4) The kernel is H² (still UNSAT, no local witness)
    UNSATType2 (fullTrimming G) := by
  refine ⟨?_, h2.2.2, ?_, ?_⟩
  · -- (1) Every cube has gaps
    intro i
    exact no_dead_cubes G i
  · -- (3) Kernel is non-trivial
    exact h2_kernel_nontrivial G h_ac h2.1
  · -- (4) Kernel is H²
    exact fullTrimming_kernel_h2 G h_ac h2.1

end CubeGraph
