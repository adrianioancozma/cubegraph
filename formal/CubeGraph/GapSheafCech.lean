/-
  CubeGraph/GapSheafCech.lean
  Čech coboundary operator and cohomological classification.

  Extends GapSheaf.lean (which provides the vocabulary: stalks, edge stalks,
  global sections) with the Čech machinery:
    - Coboundary operator δ⁰ : C⁰ → C¹
    - ker(δ⁰) = global sections = SAT
    - Restriction maps (presheaf arrows)
    - Bridge theorem: δ⁰ = 0 on cycle ↔ trace(monodromy) ≠ 0
    - Presheaves on trees have global sections (H¹ = 0)
    - H² universal defect theorem

  MAIN RESULTS:
    cechKernel_iff_sat: ker(δ⁰) ∩ stalks ↔ Satisfiable
    restriction_src_in_stalk: ρ_{e,src} maps edge stalk to vertex stalk
    cech_cycle_iff_monodromy: cycle compatible gaps ↔ trace(M_i) = true
    tree_global_section: forest + AC → ∃ global section
    h2_cech_characterization: under AC, ¬SAT ↔ every cochain has a defect
    h2_defect_is_local: H² defect preserves local validity

  See: theory/research/GAP-SHEAF-FORMALIZATION.md (presheaf definition)
  See: theory/research/CECH-COHOMOLOGY-SAT.md (Čech complex, cohomology)
  See: GapSheaf.lean (stalks, edge stalks, global sections)
  See: Monodromy.lean (monodromy operator, algebraic side)
  See: Locality.lean (H² requires cycles)
-/

import CubeGraph.GapSheaf
import CubeGraph.Monodromy
import CubeGraph.Locality

namespace CubeGraph

/-! ## Section 1: Čech Cochain Groups

  C⁰(G, F) = gap selections (one gap per cube)
  C¹(G, F) = edge compatibility indicators -/

/-- C⁰(G, F): a 0-cochain assigns a gap vertex to each cube.
    Identical to GapSelection — the Čech name for clarity. -/
abbrev CechZeroCochain (G : CubeGraph) := GapSelection G

/-- A 0-cochain is "in the stalks" if each assignment is a valid gap.
    This is `validSelection` in Čech language. -/
def CechZeroCochain.inStalks (G : CubeGraph) (σ : CechZeroCochain G) : Prop :=
  ∀ i : Fin G.cubes.length, (G.cubes[i]).isGap (σ i) = true

/-- inStalks is definitionally equal to validSelection. -/
theorem inStalks_eq_validSelection (G : CubeGraph) (σ : CechZeroCochain G) :
    CechZeroCochain.inStalks G σ ↔ validSelection G σ :=
  Iff.rfl

/-! ## Section 2: Coboundary Operator δ⁰

  δ⁰ : C⁰ → C¹ measures edge compatibility.
  (δ⁰σ)_e = transferOp(c₁, c₂)(σ(c₁), σ(c₂))
  A 0-cochain σ is a cocycle (δ⁰σ = 0) iff it's a compatible selection. -/

/-- The Čech coboundary δ⁰ : C⁰ → C¹.
    (δ⁰σ)_e = true iff σ(c₁) and σ(c₂) are compatible on edge e.
    δ⁰σ = 0 (all edges true) means σ is a cocycle = global section. -/
def cechCoboundary (G : CubeGraph) (σ : CechZeroCochain G)
    (e : Fin G.cubes.length × Fin G.cubes.length) : Bool :=
  transferOp (G.cubes[e.1]) (G.cubes[e.2]) (σ e.1) (σ e.2)

/-- δ⁰σ = 0 on all edges ↔ compatible selection. Pure unfolding. -/
theorem cechCocycle_iff_compatible (G : CubeGraph) (σ : CechZeroCochain G) :
    (∀ e ∈ G.edges, cechCoboundary G σ e = true) ↔ compatibleSelection G σ :=
  Iff.rfl

/-- **ker(δ⁰) ∩ stalks = SAT.**
    A valid cochain with vanishing coboundary is exactly a satisfying assignment.
    This is the fundamental theorem of the Čech formulation:
      H⁰(G, F) = { σ ∈ C⁰ : σ ∈ stalks, δ⁰σ = 0 } = SAT solutions. -/
theorem cechKernel_iff_sat (G : CubeGraph) :
    (∃ σ : CechZeroCochain G,
      CechZeroCochain.inStalks G σ ∧
      ∀ e ∈ G.edges, cechCoboundary G σ e = true) ↔
    G.Satisfiable :=
  Iff.rfl

/-! ## Section 3: Restriction Maps (Presheaf Arrows)

  The gap sheaf F is a presheaf with restriction maps:
    ρ_{e,src} : F(e) → F(src),  (g₁, g₂) ↦ g₁
    ρ_{e,dst} : F(e) → F(dst),  (g₁, g₂) ↦ g₂

  These are well-defined: compatible pairs project to valid gaps. -/

/-- Restriction to source: if (g₁, g₂) ∈ F(e), then g₁ ∈ F(src).
    The presheaf arrow ρ_{e,src} : F(e) → F(src) is well-defined. -/
theorem restriction_src_in_stalk (G : CubeGraph)
    (e : Fin G.cubes.length × Fin G.cubes.length)
    (g₁ g₂ : Vertex) (h : (g₁, g₂) ∈ edgeStalk G e) :
    g₁ ∈ gapStalk G e.1 := by
  rw [mem_gapStalk]
  rw [mem_edgeStalk] at h
  simp only [transferOp, Bool.and_eq_true] at h
  exact h.1.1

/-- Restriction to destination: if (g₁, g₂) ∈ F(e), then g₂ ∈ F(dst).
    The presheaf arrow ρ_{e,dst} : F(e) → F(dst) is well-defined. -/
theorem restriction_dst_in_stalk (G : CubeGraph)
    (e : Fin G.cubes.length × Fin G.cubes.length)
    (g₁ g₂ : Vertex) (h : (g₁, g₂) ∈ edgeStalk G e) :
    g₂ ∈ gapStalk G e.2 := by
  rw [mem_gapStalk]
  rw [mem_edgeStalk] at h
  simp only [transferOp, Bool.and_eq_true] at h
  exact h.1.2

/-- Coboundary at edge = restriction check: δ⁰σ|_e = true iff
    (σ(src), σ(dst)) ∈ F(e) (the pair is in the edge stalk). -/
theorem coboundary_iff_edgeStalk (G : CubeGraph) (σ : CechZeroCochain G)
    (e : Fin G.cubes.length × Fin G.cubes.length) :
    cechCoboundary G σ e = true ↔ (σ e.1, σ e.2) ∈ edgeStalk G e := by
  simp only [cechCoboundary, mem_edgeStalk]

/-! ## Section 4: Cycle Coboundary = Monodromy

  The central bridge theorem: a cycle has a compatible gap assignment
  (δ⁰ = 0 on cycle) if and only if the monodromy trace is nonzero.
  This identifies the Čech cocycle condition with the algebraic holonomy. -/

/-- **Forward**: compatible gaps on a cycle → monodromy trace is nonzero.
    If δ⁰ = 0 around the cycle, the holonomy has a fixed point. -/
theorem cech_cycle_implies_monodromy (cycle : List Cube) (h_len : cycle.length ≥ 2)
    (i : Fin cycle.length)
    (gaps : Fin cycle.length → Vertex)
    (h_valid : ∀ j : Fin cycle.length, (cycle[j]).isGap (gaps j) = true)
    (h_compat : ∀ j : Fin cycle.length,
      transferOp (cycle[j]) (cycle[nextIdx cycle.length (by omega) j])
                 (gaps j) (gaps (nextIdx cycle.length (by omega) j)) = true) :
    BoolMat.trace (monodromy cycle h_len i) = true := by
  rw [BoolMat.trace_true]
  exact ⟨gaps i, feasible_implies_monodromy cycle h_len i (gaps i)
    ⟨gaps, rfl, h_valid, h_compat⟩⟩

/-- **Backward**: monodromy trace nonzero → compatible gaps on cycle.
    A fixed point of the holonomy gives a cocycle on the cycle. -/
theorem monodromy_implies_cech_cycle (cycle : List Cube) (h_len : cycle.length ≥ 2)
    (i : Fin cycle.length)
    (h : BoolMat.trace (monodromy cycle h_len i) = true) :
    ∃ gaps : Fin cycle.length → Vertex,
      (∀ j : Fin cycle.length, (cycle[j]).isGap (gaps j) = true) ∧
      (∀ j : Fin cycle.length,
        transferOp (cycle[j]) (cycle[nextIdx cycle.length (by omega) j])
                   (gaps j) (gaps (nextIdx cycle.length (by omega) j)) = true) := by
  rw [BoolMat.trace_true] at h
  obtain ⟨g, hg⟩ := h
  obtain ⟨gaps, _, h_valid, h_compat⟩ :=
    monodromy_implies_feasible cycle h_len i g hg
  exact ⟨gaps, h_valid, h_compat⟩

/-- **Čech-Monodromy Bridge**: δ⁰ = 0 on cycle ↔ trace(M_i) = true.
    This identifies the Čech cocycle condition on a cycle with the
    algebraic condition that the holonomy (monodromy) has a fixed point.

    In differential geometry language: the gap sheaf connection is flat
    on a cycle iff the holonomy around that cycle is non-trivial on the diagonal.

    See: CECH-COHOMOLOGY-SAT.md §3.1 (Channel Alignment as cocycle calculation)
    See: CECH-COHOMOLOGY-SAT.md §8.2 (gap "connection" and holonomy) -/
theorem cech_cycle_iff_monodromy (cycle : List Cube) (h_len : cycle.length ≥ 2)
    (i : Fin cycle.length) :
    (∃ gaps : Fin cycle.length → Vertex,
      (∀ j : Fin cycle.length, (cycle[j]).isGap (gaps j) = true) ∧
      (∀ j : Fin cycle.length,
        transferOp (cycle[j]) (cycle[nextIdx cycle.length (by omega) j])
                   (gaps j) (gaps (nextIdx cycle.length (by omega) j)) = true)) ↔
    BoolMat.trace (monodromy cycle h_len i) = true :=
  ⟨fun ⟨gaps, hv, hc⟩ => cech_cycle_implies_monodromy cycle h_len i gaps hv hc,
   monodromy_implies_cech_cycle cycle h_len i⟩

/-! ## Section 5: Presheaves on Trees Have Global Sections (H¹ = 0)

  For a forest (β₁ = 0), the gap sheaf always has a global section
  when arc-consistent. This is the cohomological reason why tree-SAT
  is polynomial: H¹(tree, F) = 0, so no obstruction can exist. -/

/-- **Presheaves on trees have global sections.**
    β₁ = 0 → H¹ = 0 → every arc-consistent forest is SAT.
    This is `forest_arc_consistent_sat` in sheaf language. -/
theorem tree_global_section (G : CubeGraph)
    (h_forest : IsForest G) (h_ac : AllArcConsistent G) :
    Nonempty (GapGlobalSection G) :=
  (globalSection_iff_sat G).mpr (forest_arc_consistent_sat G h_forest h_ac)

/-- **Contrapositive**: no global section on a forest → not arc-consistent.
    On trees, the ONLY reason for UNSAT is local inconsistency (H¹),
    never global incoherence (H²). -/
theorem tree_no_h2 (G : CubeGraph)
    (h_forest : IsForest G) (h_ac : AllArcConsistent G) :
    ¬ UNSATType2 G :=
  h2_requires_cycles G h_forest h_ac

/-! ## Section 6: H² = Universal Defect Theorem

  Under arc consistency, UNSAT means every valid 0-cochain has at least
  one defective edge — but the defect location shifts depending on the
  cochain. No single edge is "the problem" — the obstruction is global. -/

/-- **¬SAT ↔ every valid cochain has a defective edge.**
    ker(δ⁰) is empty: for every σ ∈ stalks, ∃ edge where δ⁰σ ≠ 0.
    Note: does NOT require AC — this is a general characterization. -/
theorem cech_unsat_iff_defective (G : CubeGraph) :
    ¬ G.Satisfiable ↔
    (∀ σ : CechZeroCochain G,
      CechZeroCochain.inStalks G σ →
      ∃ e ∈ G.edges, cechCoboundary G σ e = false) := by
  constructor
  · -- Forward: ¬SAT → every valid cochain has a defect
    intro h_unsat σ h_stalks
    -- If all edges were compatible, σ would witness SAT
    apply Classical.byContradiction
    intro h_no_defect
    apply h_unsat
    refine ⟨σ, h_stalks, fun e he => ?_⟩
    -- No defect means this edge must be compatible
    cases hc : cechCoboundary G σ e
    · exfalso; exact h_no_defect ⟨e, he, hc⟩
    · exact hc
  · -- Backward: every valid cochain defective → ¬SAT
    intro h_defective h_sat
    obtain ⟨s, h_valid, h_compat⟩ := h_sat
    obtain ⟨e, he, h_bad⟩ := h_defective s h_valid
    have h_good : cechCoboundary G s e = true := h_compat e he
    rw [h_good] at h_bad
    exact Bool.noConfusion h_bad

/-- **H² defect is local-but-global**: at the defective edge, both endpoints
    have valid gaps — the failure is purely in their mutual incompatibility.
    Each cube "looks fine" locally; the mismatch only appears when you try
    to glue the local sections together. -/
theorem h2_defect_is_local (G : CubeGraph) (h2 : UNSATType2 G) :
    ∀ σ : CechZeroCochain G,
      CechZeroCochain.inStalks G σ →
      ∃ e ∈ G.edges,
        cechCoboundary G σ e = false ∧
        (G.cubes[e.1]).isGap (σ e.1) = true ∧
        (G.cubes[e.2]).isGap (σ e.2) = true := by
  intro σ h_stalks
  -- σ cannot be globally compatible (h2.1 = ¬SAT)
  have h_not_compat : ¬ compatibleSelection G σ := by
    intro h_compat
    exact h2.1 ⟨σ, h_stalks, h_compat⟩
  -- So ∃ bad edge
  have h_bad : ∃ e ∈ G.edges, cechCoboundary G σ e = false := by
    apply Classical.byContradiction
    intro h_all_good
    apply h_not_compat
    intro e he
    cases hc : cechCoboundary G σ e
    · exfalso; exact h_all_good ⟨e, he, hc⟩
    · exact hc
  obtain ⟨e, he, h_bad_edge⟩ := h_bad
  exact ⟨e, he, h_bad_edge, h_stalks e.1, h_stalks e.2⟩

/-- **H² defect count**: every valid cochain has at least one defective edge
    AND at least one compatible edge (from H² local invisibility:
    ¬HasBlockedEdge means every edge has SOME compatible pair). -/
theorem h2_defect_nontrivial (G : CubeGraph) (h2 : UNSATType2 G) :
    (∀ e ∈ G.edges,
      ∃ g₁ g₂ : Vertex, transferOp (G.cubes[e.1]) (G.cubes[e.2]) g₁ g₂ = true) ∧
    (∀ σ : CechZeroCochain G,
      CechZeroCochain.inStalks G σ →
      ∃ e ∈ G.edges, cechCoboundary G σ e = false) := by
  refine ⟨(H2_locally_invisible G h2).2, ?_⟩
  intro σ h_stalks
  obtain ⟨e, he, h_bad, _, _⟩ := h2_defect_is_local G h2 σ h_stalks
  exact ⟨e, he, h_bad⟩

end CubeGraph
