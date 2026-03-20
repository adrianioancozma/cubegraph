/-
  CubeGraph/HierarchyTheorems.lean
  Connecting the UNSAT hierarchy to arc consistency and leaf trimming.

  Key new results:
  1. Arc consistency implies no blocked edges (AC → ¬H¹)
  2. Under AC, UNSAT = H² (the only hard case)
  3. Full characterization: ¬SAT ↔ HasBlockedEdge ∨ UNSATType2
  4. H² decision = SAT restricted to non-blocked graphs
  5. Leaf trimming under AC reduces to H² detection

  Depends on: Hierarchy.lean, LeafTrimming.lean, TreeSAT.lean, CNF.lean

  See: theory/theorems/THEOREM-A-HIERARCHY.md (mathematical statement of hierarchy)
  See: theory/theorems/CORE-THEOREMS-SUMMARY.md (how this fits the framework)
-/

import CubeGraph.Hierarchy
import CubeGraph.LeafTrimming

namespace CubeGraph

/-! ## Section 1: Arc Consistency → No Blocked Edges -/

/-- Arc consistency in one direction implies the edge is not blocked.
    If every gap of c₂ has a compatible gap in c₁, then the transfer
    operator has at least one true entry, hence is not all-false. -/
theorem arcConsistent_implies_not_blockedEdge (G : CubeGraph)
    (i j : Fin G.cubes.length)
    (h_ac : arcConsistentDir (G.cubes[i]) (G.cubes[j])) :
    ¬ blockedEdge G i j := by
  intro hb
  obtain ⟨g₁, g₂, ht⟩ := arcConsistentDir_implies_nonzero h_ac
  have hf := hb g₁ g₂
  rw [hf] at ht
  exact Bool.noConfusion ht

/-- AllArcConsistent implies no blocked edges anywhere.
    This is the bridge: AC-3 eliminates all H¹ obstructions. -/
theorem allAC_implies_no_blocked (G : CubeGraph) (h_ac : AllArcConsistent G) :
    ¬ HasBlockedEdge G := by
  intro ⟨e, he, hb⟩
  have ⟨hac_fwd, _⟩ := h_ac e he
  exact arcConsistent_implies_not_blockedEdge G e.1 e.2 hac_fwd hb

/-! ## Section 2: Under AC, UNSAT = H² -/

/-- **Under arc consistency, UNSAT implies H².**
    If AC holds (no H¹ possible) and H⁰ is always impossible,
    then any UNSAT graph is purely H² — global incoherence. -/
theorem ac_unsat_is_h2 (G : CubeGraph)
    (h_ac : AllArcConsistent G) (h_unsat : ¬ G.Satisfiable) :
    UNSATType2 G :=
  ⟨h_unsat, H0_impossible G, allAC_implies_no_blocked G h_ac⟩

/-- Converse: H² implies UNSAT (by definition). -/
theorem h2_implies_unsat (G : CubeGraph) (h : UNSATType2 G) :
    ¬ G.Satisfiable := h.1

/-- **Under arc consistency: SAT ↔ ¬H².**
    After AC-3, the only question remaining is whether H² exists. -/
theorem ac_sat_iff_not_h2 (G : CubeGraph) (h_ac : AllArcConsistent G) :
    G.Satisfiable ↔ ¬ UNSATType2 G := by
  constructor
  · intro h_sat ⟨h_unsat, _, _⟩
    exact h_unsat h_sat
  · intro h_not_h2
    exact Classical.byContradiction fun h_unsat =>
      h_not_h2 (ac_unsat_is_h2 G h_ac h_unsat)

/-! ## Section 3: Complete UNSAT Characterization -/

/-- **UNSAT iff H¹ or H² (H⁰ is impossible).**
    This is the master characterization of unsatisfiability. -/
theorem unsat_iff_h1_or_h2 (G : CubeGraph) :
    ¬ G.Satisfiable ↔ (HasBlockedEdge G ∨ UNSATType2 G) := by
  constructor
  · exact unsat_dichotomy G
  · intro h
    rcases h with hbe | h2
    · exact hasBlockedEdge_implies_unsat G hbe
    · exact h2.1

/-- **SAT iff no H¹ and no H².**
    Complete positive characterization of satisfiability. -/
theorem sat_iff_no_obstructions (G : CubeGraph) :
    G.Satisfiable ↔ (¬ HasBlockedEdge G ∧ ¬ UNSATType2 G) := by
  constructor
  · intro h_sat
    exact ⟨fun hbe => hasBlockedEdge_implies_unsat G hbe h_sat,
           fun ⟨h_unsat, _, _⟩ => h_unsat h_sat⟩
  · intro ⟨h_no_be, h_no_h2⟩
    exact Classical.byContradiction fun h_unsat =>
      (unsat_dichotomy G h_unsat).elim
        (fun hbe => h_no_be hbe)
        (fun h2 => h_no_h2 h2)

/-! ## Section 4: H² Decision Reduction -/

/-- **On non-blocked graphs, H² = UNSAT.**
    For any CubeGraph with no blocked edges (e.g., after AC-3),
    unsatisfiability IS H² — no other obstruction type is possible. -/
theorem h2_iff_unsat_of_no_blocked (G : CubeGraph) (h : ¬ HasBlockedEdge G) :
    UNSATType2 G ↔ ¬ G.Satisfiable := by
  constructor
  · exact fun h2 => h2.1
  · exact fun h_unsat => ⟨h_unsat, H0_impossible G, h⟩

/-- The H¹ check is a polynomial preprocessing step:
    if we find a blocked edge, we're done (UNSAT). -/
theorem blocked_edge_decides_unsat (G : CubeGraph) (h : HasBlockedEdge G) :
    ¬ G.Satisfiable :=
  hasBlockedEdge_implies_unsat G h

/-! ## Section 5: Leaf Trimming and the H² Kernel -/

/-- **After full trimming under AC, the kernel is either SAT or H².**
    Leaf trimming preserves SAT equivalence and AC. The result has no leaves
    (or is trivially small). Since AC is preserved, the kernel has no
    blocked edges. If it's UNSAT, it must be H². -/
theorem fullTrimming_kernel_h2 (G : CubeGraph) (h_ac : AllArcConsistent G)
    (h_unsat : ¬ G.Satisfiable) :
    UNSATType2 (fullTrimming G) := by
  have h_ac' := fullTrimming_preserves_ac G h_ac
  have h_equiv := fullTrimming_sat_equiv G h_ac
  have h_kernel_unsat : ¬ (fullTrimming G).Satisfiable := by
    intro h_sat
    exact h_unsat (h_equiv.mpr h_sat)
  exact ac_unsat_is_h2 (fullTrimming G) h_ac' h_kernel_unsat

/-- **SAT reduces to: AC-3 + leaf trimming + H² check on kernel.**
    This is the algorithmic skeleton:
    1. Run AC-3 (polynomial) — either detects H¹ or establishes AC
    2. Run leaf trimming (polynomial) — reduces graph to cyclic kernel
    3. Check kernel for H² (NP-hard residual)

    If the formula is SAT, step 3 will find the kernel is SAT.
    If UNSAT, step 1 might detect H¹, otherwise step 3 finds H². -/
theorem sat_iff_trimmed_kernel_sat (G : CubeGraph) (h_ac : AllArcConsistent G) :
    G.Satisfiable ↔ (fullTrimming G).Satisfiable :=
  fullTrimming_sat_equiv G h_ac

/-! ## Section 6: The Three-Step Algorithm -/

/-- **Step 1**: Dead cube check — always passes (vacuously). -/
theorem step1_dead_cube_impossible (G : CubeGraph) : ¬ HasDeadCube G :=
  H0_impossible G

/-- **Step 2**: Blocked edge check — decidable in polynomial time. -/
instance step2_blocked_edge_decidable (G : CubeGraph) :
    Decidable (HasBlockedEdge G) :=
  instDecidableHasBlockedEdge G

/-- **Step 3**: Residual — if no blocked edges, SAT ↔ ¬H². -/
theorem step3_residual (G : CubeGraph) (h : ¬ HasBlockedEdge G) :
    G.Satisfiable ↔ ¬ UNSATType2 G := by
  rw [h2_iff_unsat_of_no_blocked G h]
  constructor
  · exact fun h_sat h_unsat => h_unsat h_sat
  · intro h_nn
    exact Classical.byContradiction fun h_ns => h_nn h_ns

end CubeGraph
