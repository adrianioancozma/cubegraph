/-
  CubeGraph/HierarchyExtended.lean
  Phase 8+: Extended UNSAT hierarchy with H¹·⁵ (arc-inconsistency) level.

  The extended hierarchy:
    H⁰:   dead cube (gapCount = 0) — impossible by Cube invariant
    H¹:   blocked edge (zero transfer operator) — polynomial, O(m·64)
    H¹·⁵: arc-inconsistency (AC-3 propagation kills a cube) — polynomial, AC-3
    H²:   global incoherence (AC-consistent but UNSAT) — NP-hard, Type 2

  H¹·⁵ = UNSAT instances where no cube is initially dead, no edge is blocked,
  but the graph is NOT arc-consistent. AC-3 detects these in polynomial time.

  Witness: bwGraph (Witness.lean) — acyclic path, no blocked edges, UNSAT,
  but not arc-consistent. Separation: H¹·⁵ ∖ H¹ is non-empty.

  Depends on: Hierarchy.lean, HierarchyTheorems.lean, LeafTrimming.lean, Witness.lean

  See: experiments-ml/039_2026-03-28_order-propagation/STATUS-IDEAS-ORDERED.md (TIER 2)
  See: experiments-ml/039_2026-03-28_order-propagation/INSIGHT-CONTEXT-EXPLOSION.md
  See: experiments-ml/039_2026-03-28_order-propagation/SESSION-039-FINAL-STATE.md
  See: DISCOVERIES.md (entry #34)
-/

import CubeGraph.HierarchyTheorems
import CubeGraph.Witness

namespace CubeGraph

open BoolMat

/-! ## Section 1: H¹·⁵ and Strict H² Definitions -/

/-- **H¹·⁵ UNSAT**: no dead cubes, no blocked edges, but NOT arc-consistent.
    AC-3 propagation will eventually kill a cube.
    Detectable in polynomial time (AC-3/AC-4 fixpoint).
    Sits strictly between H¹ (blocked edge) and strict H² (global incoherence). -/
def UNSATType1_5 (G : CubeGraph) : Prop :=
  ¬ G.Satisfiable ∧ ¬ HasDeadCube G ∧ ¬ HasBlockedEdge G ∧ ¬ AllArcConsistent G

/-- **Strict H² UNSAT**: no dead cubes, no blocked edges, arc-consistent, yet UNSAT.
    This is the true hard core — no polynomial-time method can detect it.
    Refines the original UNSATType2 by requiring arc consistency. -/
def UNSATType2Strict (G : CubeGraph) : Prop :=
  ¬ G.Satisfiable ∧ ¬ HasDeadCube G ∧ ¬ HasBlockedEdge G ∧ AllArcConsistent G

/-! ## Section 2: Hierarchy Relationships -/

/-- H¹·⁵ and strict H² are disjoint: ¬AllArcConsistent vs AllArcConsistent. -/
theorem h1_5_disjoint_h2_strict (G : CubeGraph) :
    ¬ (UNSATType1_5 G ∧ UNSATType2Strict G) := by
  intro ⟨⟨_, _, _, h_nac⟩, ⟨_, _, _, h_ac⟩⟩
  exact h_nac h_ac

/-- H¹·⁵ implies the original (broad) UNSATType2.
    The original H² definition does not mention arc consistency. -/
theorem h1_5_implies_old_h2 (G : CubeGraph) (h : UNSATType1_5 G) :
    UNSATType2 G :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- Strict H² implies the original (broad) UNSATType2. -/
theorem h2_strict_implies_old_h2 (G : CubeGraph) (h : UNSATType2Strict G) :
    UNSATType2 G :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- The original UNSATType2 splits into H¹·⁵ or strict H². -/
theorem old_h2_split (G : CubeGraph) (h : UNSATType2 G) :
    UNSATType1_5 G ∨ UNSATType2Strict G := by
  obtain ⟨h_unsat, h_ndc, h_nbe⟩ := h
  by_cases h_ac : AllArcConsistent G
  · exact .inr ⟨h_unsat, h_ndc, h_nbe, h_ac⟩
  · exact .inl ⟨h_unsat, h_ndc, h_nbe, h_ac⟩

/-- Under arc consistency, UNSAT implies strict H² (strengthens ac_unsat_is_h2). -/
theorem ac_unsat_is_h2_strict (G : CubeGraph)
    (h_ac : AllArcConsistent G) (h_unsat : ¬ G.Satisfiable) :
    UNSATType2Strict G :=
  ⟨h_unsat, H0_impossible G, allAC_implies_no_blocked G h_ac, h_ac⟩

/-! ## Section 3: Extended Four-Way Classification -/

/-- **Extended classification**: every UNSAT CubeGraph is H⁰, H¹, H¹·⁵, or strict H².
    Since H⁰ is impossible, effectively: H¹, H¹·⁵, or strict H². -/
theorem extended_unsat_classification (G : CubeGraph) (h : ¬ G.Satisfiable) :
    HasDeadCube G ∨ HasBlockedEdge G ∨ UNSATType1_5 G ∨ UNSATType2Strict G := by
  by_cases hdc : HasDeadCube G
  · exact .inl hdc
  · by_cases hbe : HasBlockedEdge G
    · exact .inr (.inl hbe)
    · by_cases hac : AllArcConsistent G
      · exact .inr (.inr (.inr ⟨h, hdc, hbe, hac⟩))
      · exact .inr (.inr (.inl ⟨h, hdc, hbe, hac⟩))

/-- Since H⁰ is impossible, three-way classification. -/
theorem extended_unsat_trichotomy (G : CubeGraph) (h : ¬ G.Satisfiable) :
    HasBlockedEdge G ∨ UNSATType1_5 G ∨ UNSATType2Strict G := by
  rcases extended_unsat_classification G h with hdc | hbe | h15 | h2s
  · exact absurd hdc (H0_impossible G)
  · exact .inl hbe
  · exact .inr (.inl h15)
  · exact .inr (.inr h2s)

/-- The three active types are mutually exclusive. -/
theorem extended_types_disjoint (G : CubeGraph) :
    ¬ (HasBlockedEdge G ∧ UNSATType1_5 G) ∧
    ¬ (HasBlockedEdge G ∧ UNSATType2Strict G) ∧
    ¬ (UNSATType1_5 G ∧ UNSATType2Strict G) := by
  exact ⟨
    fun ⟨hbe, ⟨_, _, h_nbe, _⟩⟩ => h_nbe hbe,
    fun ⟨hbe, ⟨_, _, h_nbe, _⟩⟩ => h_nbe hbe,
    h1_5_disjoint_h2_strict G⟩

/-! ## Section 4: bwGraph is NOT Arc-Consistent (H¹·⁵ Witness) -/

/-- Arc consistency fails from bwCube3 to bwCube2 on edge (1,2):
    bwCube2's gap 0 (var4=0) has no compatible gap in bwCube3 (gap 1 has var4=1).
    This is the concrete arc-inconsistency that AC-3 would detect. -/
theorem bwGraph_not_arc_consistent : ¬ AllArcConsistent bwGraph := by
  intro h_ac
  -- Edge (1,2) is the second edge: (⟨1,_⟩, ⟨2,_⟩)
  have h_e := h_ac _ (List.Mem.tail _ (List.Mem.head _))
  -- Get the backward direction: arcConsistentDir bwCube3 bwCube2
  obtain ⟨_, h_back⟩ := h_e
  -- gap 0 of bwCube2 is a gap
  have h_gap0 : bwCube2.isGap ⟨0, by omega⟩ = true := by native_decide
  -- AC says: there exists g₃ such that transferOp bwCube3 bwCube2 g₃ 0 = true
  obtain ⟨g₃, hg₃⟩ := h_back ⟨0, by omega⟩ h_gap0
  -- But all 8 entries of transferOp bwCube3 bwCube2 (_, 0) are false
  revert g₃ hg₃
  native_decide

/-- **H¹·⁵ WITNESS**: bwGraph is UNSATType1_5 — the first concrete H¹·⁵ instance.
    Acyclic path, no blocked edges, UNSAT, not arc-consistent. -/
theorem h1_5_witness : UNSATType1_5 bwGraph :=
  ⟨bwGraph_unsat, H0_impossible bwGraph, bwGraph_no_blocked, bwGraph_not_arc_consistent⟩

/-- H¹·⁵ level is non-empty: there exists a CubeGraph that is H¹·⁵. -/
theorem h1_5_nonempty : ∃ G : CubeGraph, UNSATType1_5 G :=
  ⟨bwGraph, h1_5_witness⟩

/-! ## Section 5: h2Graph IS Arc-Consistent (Strict H² Witness) -/

/-- Helper: boolean decision procedure for arcConsistentDir on concrete cubes. -/
private def acDirCheck (c₁ c₂ : Cube) : Bool :=
  (List.finRange 8).all fun g₂ =>
    !c₂.isGap g₂ || (List.finRange 8).any fun g₁ => transferOp c₁ c₂ g₁ g₂

private theorem acDirCheck_spec (c₁ c₂ : Cube) (h : acDirCheck c₁ c₂ = true) :
    arcConsistentDir c₁ c₂ := by
  intro g₂ hg₂
  unfold acDirCheck at h
  rw [List.all_eq_true] at h
  have := h g₂ (mem_finRange _)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_true] at this
  rcases this with h_neg | h_any
  · rw [hg₂] at h_neg; exact absurd h_neg (by decide)
  · rw [List.any_eq_true] at h_any
    obtain ⟨g₁, _, hg₁⟩ := h_any
    exact ⟨g₁, hg₁⟩

/-- h2Graph edge (A,B): arc-consistent both directions. -/
private theorem h2_ac_AB :
    arcConsistentDir h2CubeA h2CubeB ∧ arcConsistentDir h2CubeB h2CubeA :=
  ⟨acDirCheck_spec _ _ (by native_decide), acDirCheck_spec _ _ (by native_decide)⟩

/-- h2Graph edge (B,C): arc-consistent both directions. -/
private theorem h2_ac_BC :
    arcConsistentDir h2CubeB h2CubeC ∧ arcConsistentDir h2CubeC h2CubeB :=
  ⟨acDirCheck_spec _ _ (by native_decide), acDirCheck_spec _ _ (by native_decide)⟩

/-- h2Graph edge (C,A): arc-consistent both directions. -/
private theorem h2_ac_CA :
    arcConsistentDir h2CubeC h2CubeA ∧ arcConsistentDir h2CubeA h2CubeC :=
  ⟨acDirCheck_spec _ _ (by native_decide), acDirCheck_spec _ _ (by native_decide)⟩

/-- h2Graph is fully arc-consistent. -/
theorem h2Graph_arc_consistent : AllArcConsistent h2Graph := by
  intro e he
  cases he with
  | head _ => exact h2_ac_AB
  | tail _ he =>
    cases he with
    | head _ => exact h2_ac_BC
    | tail _ he =>
      cases he with
      | head _ => exact h2_ac_CA
      | tail _ he => cases he

/-- **Strict H² WITNESS**: h2Graph is UNSATType2Strict — arc-consistent but UNSAT.
    This is the hard core: no polynomial method (AC-3, leaf trimming, etc.) can detect it. -/
theorem h2_strict_witness : UNSATType2Strict h2Graph :=
  ⟨h2Graph_unsat, H0_impossible h2Graph, h2Graph_no_blocked, h2Graph_arc_consistent⟩

/-- Strict H² level is non-empty. -/
theorem h2_strict_nonempty : ∃ G : CubeGraph, UNSATType2Strict G :=
  ⟨h2Graph, h2_strict_witness⟩

/-! ## Section 6: Complete Extended Hierarchy -/

/-- **Extended hierarchy completeness**: all four levels are constructively witnessed.
    - H⁰: impossible (Cube.gaps_nonempty)
    - H¹: h1Graph (blocked edge)
    - H¹·⁵: bwGraph (arc-inconsistency on acyclic path)
    - Strict H²: h2Graph (arc-consistent cycle, global incoherence)
    - SAT: satGraph (trivially satisfiable) -/
theorem extended_hierarchy_complete :
    (∀ G : CubeGraph, ¬ UNSATType0 G) ∧
    (∃ G : CubeGraph, UNSATType1 G) ∧
    (∃ G : CubeGraph, UNSATType1_5 G) ∧
    (∃ G : CubeGraph, UNSATType2Strict G) ∧
    (∃ G : CubeGraph, G.Satisfiable) :=
  ⟨UNSATType0_impossible,
   ⟨_, h1_witness⟩,
   h1_5_nonempty,
   h2_strict_nonempty,
   ⟨_, satGraph_satisfiable⟩⟩

/-- **Post-AC is strict H²**: after AC-3 reaches fixpoint, remaining UNSAT is strict H². -/
theorem post_ac_is_strict_h2 (G : CubeGraph)
    (h_ac : AllArcConsistent G) (h_unsat : ¬ G.Satisfiable) :
    UNSATType2Strict G :=
  ac_unsat_is_h2_strict G h_ac h_unsat

end CubeGraph
