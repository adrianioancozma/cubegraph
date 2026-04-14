/-
  CubeGraph/Type2Monodromy.lean
  Type 2 UNSAT: Local Consistency with Global Incoherence

  Central result: a CubeGraph where every edge has compatible gap pairs
  (locally consistent, i.e. ¬ HasBlockedEdge) yet is UNSAT.
  The cycle monodromy is NON-ZERO but TRACELESS — it swaps gaps 0 ↔ 3.

  This is the standard CSP phenomenon of "arc-consistent but unsatisfiable"
  (Mackworth 1977), formalized for CubeGraph with monodromy structure analysis.

  The boolean semiring (OR/AND) enables non-zero traceless compositions:
  individual edges transmit gap information, but cyclic composition
  loses fixed-point structure (1+1=1 collapses spectral information).

  See: Witness.lean (h2Graph, h2Graph_unsat, h2Graph_no_blocked)
  See: MisalignedComposition.lean (h2_composed_not_rankOne)
  See: RankMonotonicity.lean (rank-1 absorbing)
  See: Abramsky-Brandenburger (2011) — contextuality = local consistency without global
  See: Mackworth (1977) — arc consistency in CSP

  Previously: FlatBundleFailure.lean — renamed per devil's advocate analysis
  (FBF-DEVILS-ADVOCATE.md). The fiber bundle analogy was a misnomer:
  0/6 structural properties of fiber bundles apply to CubeGraph.
-/

import CubeGraph.GapSheaf
import CubeGraph.MisalignedComposition

namespace CubeGraph

open BoolMat

/-! ## Section 1: Local Consistency -/

/-- **Locally consistent**: every edge has a non-zero transfer operator.
    Equivalent to ¬ HasBlockedEdge (Hierarchy.lean). In CSP terms:
    every constraint has at least one satisfying pair. -/
def LocallyConsistent (G : CubeGraph) : Prop :=
  ∀ e ∈ G.edges,
    ∃ g₁ g₂ : Vertex, transferOp (G.cubes[e.1]) (G.cubes[e.2]) g₁ g₂ = true

/-! ## Section 2: h2Graph is Locally Consistent -/

/-- h2Graph is locally consistent: every edge has compatible gap pairs. -/
theorem h2_locally_consistent : LocallyConsistent h2Graph := by
  intro e he
  unfold h2Graph at he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact ⟨⟨0, by omega⟩, ⟨2, by omega⟩, by native_decide⟩
  · exact ⟨⟨2, by omega⟩, ⟨3, by omega⟩, by native_decide⟩
  · exact ⟨⟨3, by omega⟩, ⟨3, by omega⟩, by native_decide⟩

/-- LocallyConsistent follows from UNSATType2 (via H2_locally_invisible). -/
theorem h2_locally_consistent_from_type2 : LocallyConsistent h2Graph := by
  have h := H2_locally_invisible h2Graph h2_witness
  intro e he
  exact h.2 e he

/-! ## Section 3: Monodromy — Non-Zero but Traceless -/

/-- The cycle monodromy of h2Graph: compose A→B, B→C, C→A. -/
abbrev h2MonodromyCycle : BoolMat 8 :=
  mul (mul (transferOp h2CubeA h2CubeB) (transferOp h2CubeB h2CubeC))
      (transferOp h2CubeC h2CubeA)

/-- The monodromy is NON-ZERO: gap 0 maps to gap 3. -/
theorem h2_monodromy_nonzero : ¬ isZero h2MonodromyCycle := by
  intro h
  have h1 : h2MonodromyCycle ⟨0, by omega⟩ ⟨3, by omega⟩ = false := h ⟨0, by omega⟩ ⟨3, by omega⟩
  have h2 : h2MonodromyCycle ⟨0, by omega⟩ ⟨3, by omega⟩ = true := by native_decide
  rw [h1] at h2; exact Bool.false_ne_true h2

/-- The monodromy has ZERO TRACE: no gap maps to itself around the cycle. -/
theorem h2_monodromy_trace_false : trace h2MonodromyCycle = false := by
  native_decide

/-- The monodromy swaps gaps: 0 ↔ 3 in cube A (transposition). -/
theorem h2_monodromy_swap :
    h2MonodromyCycle ⟨0, by omega⟩ ⟨3, by omega⟩ = true ∧
    h2MonodromyCycle ⟨3, by omega⟩ ⟨0, by omega⟩ = true :=
  ⟨by native_decide, by native_decide⟩

/-! ## Section 4: Main Theorems -/

/-- **Locally consistent + UNSAT**: all edges non-zero but no global section exists.
    This is the Type 2 UNSAT phenomenon. -/
theorem locally_consistent_unsat :
    LocallyConsistent h2Graph ∧ ¬ h2Graph.Satisfiable :=
  ⟨h2_locally_consistent, h2Graph_unsat⟩

/-- **Local consistency does NOT imply satisfiability** over the boolean semiring. -/
theorem locally_consistent_not_implies_sat :
    ∃ G : CubeGraph, LocallyConsistent G ∧ ¬ G.Satisfiable :=
  ⟨h2Graph, h2_locally_consistent, h2Graph_unsat⟩

/-- **Non-zero edges + traceless cycle**: the hallmark of Type 2 UNSAT.
    Each edge transmits information, but composition loses fixed-point structure. -/
theorem nonzero_edges_traceless_cycle :
    LocallyConsistent h2Graph ∧ ¬ isZero h2MonodromyCycle ∧ trace h2MonodromyCycle = false :=
  ⟨h2_locally_consistent, h2_monodromy_nonzero, h2_monodromy_trace_false⟩

/-- **The obstruction is in composition, not in individual edges.** -/
theorem composition_creates_obstruction :
    (∀ e ∈ h2Graph.edges,
      ∃ g₁ g₂, transferOp (h2Graph.cubes[e.1]) (h2Graph.cubes[e.2]) g₁ g₂ = true) ∧
    trace h2MonodromyCycle = false :=
  ⟨h2_locally_consistent, h2_monodromy_trace_false⟩

/-! ## Section 5: Relationship with UNSAT Hierarchy -/

/-- Locally consistent + UNSAT implies UNSATType2. -/
theorem locally_consistent_unsat_implies_h2 (G : CubeGraph)
    (hflat : LocallyConsistent G) (hunsat : ¬ G.Satisfiable) :
    UNSATType2 G := by
  refine ⟨hunsat, H0_impossible G, ?_⟩
  intro ⟨e, he, hblocked⟩
  obtain ⟨g₁, g₂, hcompat⟩ := hflat e he
  have hf := hblocked g₁ g₂
  rw [hcompat] at hf
  exact absurd hf (by decide)

/-- UNSATType2 implies LocallyConsistent (the converse direction). -/
theorem h2_implies_locally_consistent (G : CubeGraph) (h : UNSATType2 G) :
    LocallyConsistent G := by
  intro e he
  exact (H2_locally_invisible G h).2 e he

/-- h2Graph is UNSATType2 via local consistency route (alt proof). -/
theorem h2_type2_via_locally_consistent : UNSATType2 h2Graph :=
  locally_consistent_unsat_implies_h2 h2Graph h2_locally_consistent h2Graph_unsat

/-! ## Section 6: Monodromy Structure -/

/-- The cycle monodromy is not rank-1.
    Proof: rank-1 means M = outerProduct r c. If M[0,3] and M[3,0] are both true,
    then r[0], c[3], r[3], c[0] all true, so M[0,0] = r[0] ∧ c[0] = true.
    But M[0,0] = false (native_decide). Contradiction. -/
theorem h2_monodromy_rank2 : ¬ IsRankOne h2MonodromyCycle := by
  intro ⟨r, c, _, _, heq⟩
  have h03 := (heq ⟨0, by omega⟩ ⟨3, by omega⟩).mp (by native_decide)
  have h30 := (heq ⟨3, by omega⟩ ⟨0, by omega⟩).mp (by native_decide)
  have h00 : h2MonodromyCycle ⟨0, by omega⟩ ⟨0, by omega⟩ = true :=
    (heq ⟨0, by omega⟩ ⟨0, by omega⟩).mpr ⟨h03.1, h30.2⟩
  have hf : h2MonodromyCycle ⟨0, by omega⟩ ⟨0, by omega⟩ = false := by native_decide
  rw [h00] at hf; exact absurd hf (by decide)

/-- Summary: the monodromy is non-zero, traceless, rank ≥ 2. -/
theorem h2_monodromy_summary :
    ¬ isZero h2MonodromyCycle ∧
    trace h2MonodromyCycle = false ∧
    ¬ IsRankOne h2MonodromyCycle :=
  ⟨h2_monodromy_nonzero, h2_monodromy_trace_false, h2_monodromy_rank2⟩

end CubeGraph
