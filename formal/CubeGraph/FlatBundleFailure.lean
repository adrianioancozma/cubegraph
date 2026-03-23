/-
  CubeGraph/FlatBundleFailure.lean
  T4: Flat Bundle Failure Theorem

  Central result: a CubeGraph where every edge has compatible gap pairs
  (flat connection) yet is UNSAT (no global section). The cycle monodromy
  is NON-ZERO but TRACELESS — it swaps gaps 0 ↔ 3, a non-trivial
  permutation like a Möbius twist.

  Over fields (ℝ, ℂ), a non-negative matrix with a positive entry must have
  positive spectral radius (Perron-Frobenius). Over 𝔹, 1+1=1 collapses
  spectral information, enabling non-zero traceless compositions.

  Empirical support (experiments 2026-03-18):
  - T1:  Bool trace > 0 on 100% of cycles at ρ_c; GF(2) trace = 0 on 80-96%.
  - T1b: ℝ rank ~1.9 (multiplicity preserved), Bool rank = 1.
  - E1:  ℝ trace SAT ≡ UNSAT (counting doesn't discriminate).
  - T2:  tw = 3.07·n (expander → no local decomposition).
  - T3:  SP AUC = 0.67 (continuous relaxation partially lifts obstruction).

  See: Witness.lean (h2Graph, h2Graph_unsat, h2Graph_no_blocked)
  See: MisalignedComposition.lean (h2_composed_not_rankOne)
  See: RankMonotonicity.lean (T5: rowRank_foldl_le, rank-1 absorbing)
  See: experiments-ml/021_.../T4-PLAN.md (plan)
  See: experiments-ml/021_.../T1-RESULTS.md (boolean trace hides obstruction — empiric)
  See: experiments-ml/021_.../E1-RESULTS.md (ℝ trace SAT ≡ UNSAT — counting doesn't help)
  See: experiments-ml/021_.../MICRO-MACRO-BRIDGE.md (flat bundle = lossy bridge micro↔macro)
  See: experiments-ml/021_.../HYPERSPHERE-TOMOGRAPHY.md (flat bundle = inconsistent sinogram)
-/

import CubeGraph.GapSheaf
import CubeGraph.MisalignedComposition

namespace CubeGraph

open BoolMat

/-! ## Section 1: Flat Bundle Definitions -/

/-- **Flat connection**: every edge has a non-zero transfer operator.
    In bundle language: parallel transport is well-defined on every edge. -/
def FlatConnection (G : CubeGraph) : Prop :=
  ∀ e ∈ G.edges,
    ∃ g₁ g₂ : Vertex, transferOp (G.cubes[e.1]) (G.cubes[e.2]) g₁ g₂ = true

/-! ## Section 2: h2Graph has Flat Connection -/

/-- h2Graph has flat connection: every edge has compatible gap pairs. -/
theorem h2_flat_connection : FlatConnection h2Graph := by
  intro e he
  unfold h2Graph at he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact ⟨⟨0, by omega⟩, ⟨2, by omega⟩, by native_decide⟩
  · exact ⟨⟨2, by omega⟩, ⟨3, by omega⟩, by native_decide⟩
  · exact ⟨⟨3, by omega⟩, ⟨3, by omega⟩, by native_decide⟩

/-- FlatConnection follows from UNSATType2 (via H2_locally_invisible). -/
theorem h2_flat_from_type2 : FlatConnection h2Graph := by
  have h := H2_locally_invisible h2Graph h2_witness
  intro e he
  exact h.2 e he

/-! ## Section 3: Monodromy — Non-Zero but Traceless -/

/-- The cycle monodromy of h2Graph: compose A→B, B→C, C→A. -/
abbrev h2Monodromy : BoolMat 8 :=
  mul (mul (transferOp h2CubeA h2CubeB) (transferOp h2CubeB h2CubeC))
      (transferOp h2CubeC h2CubeA)

/-- The monodromy is NON-ZERO: gap 0 maps to gap 3. -/
theorem h2_monodromy_nonzero : ¬ isZero h2Monodromy := by
  intro h
  have h1 : h2Monodromy ⟨0, by omega⟩ ⟨3, by omega⟩ = false := h ⟨0, by omega⟩ ⟨3, by omega⟩
  have h2 : h2Monodromy ⟨0, by omega⟩ ⟨3, by omega⟩ = true := by native_decide
  rw [h1] at h2; exact Bool.false_ne_true h2

/-- The monodromy has ZERO TRACE: no gap maps to itself around the cycle. -/
theorem h2_monodromy_trace_false : trace h2Monodromy = false := by
  native_decide

/-- The monodromy swaps gaps: 0 ↔ 3 in cube A (transposition). -/
theorem h2_monodromy_swap :
    h2Monodromy ⟨0, by omega⟩ ⟨3, by omega⟩ = true ∧
    h2Monodromy ⟨3, by omega⟩ ⟨0, by omega⟩ = true :=
  ⟨by native_decide, by native_decide⟩

/-! ## Section 4: Main Theorems -/

/-- **FLAT BUNDLE FAILURE**: flat connection + UNSAT.
    All edges non-zero but no global section exists. -/
theorem flat_bundle_failure :
    FlatConnection h2Graph ∧ ¬ h2Graph.Satisfiable :=
  ⟨h2_flat_connection, h2Graph_unsat⟩

/-- **Flat connection does NOT imply satisfiability** over 𝔹. -/
theorem flat_not_implies_sat :
    ∃ G : CubeGraph, FlatConnection G ∧ ¬ G.Satisfiable :=
  ⟨h2Graph, h2_flat_connection, h2Graph_unsat⟩

/-- **Non-zero edges + traceless cycle**: the hallmark of flat bundle failure.
    Each edge transmits information, but composition loses fixed-point structure. -/
theorem nonzero_edges_traceless_cycle :
    FlatConnection h2Graph ∧ ¬ isZero h2Monodromy ∧ trace h2Monodromy = false :=
  ⟨h2_flat_connection, h2_monodromy_nonzero, h2_monodromy_trace_false⟩

/-- **The obstruction is in composition, not in individual edges.** -/
theorem composition_creates_obstruction :
    (∀ e ∈ h2Graph.edges,
      ∃ g₁ g₂, transferOp (h2Graph.cubes[e.1]) (h2Graph.cubes[e.2]) g₁ g₂ = true) ∧
    trace h2Monodromy = false :=
  ⟨h2_flat_connection, h2_monodromy_trace_false⟩

/-! ## Section 5: Relationship with H² Hierarchy -/

/-- FlatBundleFailure implies UNSATType2. -/
theorem flat_failure_implies_h2 (G : CubeGraph)
    (hflat : FlatConnection G) (hunsat : ¬ G.Satisfiable) :
    UNSATType2 G := by
  refine ⟨hunsat, H0_impossible G, ?_⟩
  intro ⟨e, he, hblocked⟩
  obtain ⟨g₁, g₂, hcompat⟩ := hflat e he
  have hf := hblocked g₁ g₂
  rw [hcompat] at hf
  exact absurd hf (by decide)

/-- UNSATType2 implies FlatConnection (the converse direction). -/
theorem h2_implies_flat (G : CubeGraph) (h : UNSATType2 G) :
    FlatConnection G := by
  intro e he
  exact (H2_locally_invisible G h).2 e he

/-- h2Graph is UNSATType2 via the flat bundle route (alt proof). -/
theorem h2_type2_via_flat : UNSATType2 h2Graph :=
  flat_failure_implies_h2 h2Graph h2_flat_connection h2Graph_unsat

/-! ## Section 6: Monodromy Structure -/

/-- The cycle monodromy is not rank-1.
    Proof: rank-1 means M = outerProduct r c. If M[0,3] and M[3,0] are both true,
    then r[0], c[3], r[3], c[0] all true, so M[0,0] = r[0] ∧ c[0] = true.
    But M[0,0] = false (native_decide). Contradiction. -/
theorem h2_monodromy_rank2 : ¬ IsRankOne h2Monodromy := by
  intro ⟨r, c, _, _, heq⟩
  -- heq : ∀ i j, h2Monodromy i j = true ↔ r i = true ∧ c j = true
  -- M[0,3] = true → r[0] = true ∧ c[3] = true
  have h03 := (heq ⟨0, by omega⟩ ⟨3, by omega⟩).mp (by native_decide)
  -- M[3,0] = true → r[3] = true ∧ c[0] = true
  have h30 := (heq ⟨3, by omega⟩ ⟨0, by omega⟩).mp (by native_decide)
  -- Therefore M[0,0] = true (r[0] ∧ c[0])
  have h00 : h2Monodromy ⟨0, by omega⟩ ⟨0, by omega⟩ = true :=
    (heq ⟨0, by omega⟩ ⟨0, by omega⟩).mpr ⟨h03.1, h30.2⟩
  -- But M[0,0] = false by computation
  have hf : h2Monodromy ⟨0, by omega⟩ ⟨0, by omega⟩ = false := by native_decide
  rw [h00] at hf; exact absurd hf (by decide)

/-- Summary: the monodromy is non-zero, traceless, rank ≥ 2. -/
theorem h2_monodromy_summary :
    ¬ isZero h2Monodromy ∧
    trace h2Monodromy = false ∧
    ¬ IsRankOne h2Monodromy :=
  ⟨h2_monodromy_nonzero, h2_monodromy_trace_false, h2_monodromy_rank2⟩

end CubeGraph
