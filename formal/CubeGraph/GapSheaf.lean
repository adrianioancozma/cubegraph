/-
  CubeGraph/GapSheaf.lean
  Gap sheaf vocabulary: presheaf-theoretic reformulation of CubeGraph SAT.

  The gap sheaf F on a CubeGraph G is the presheaf:
    F(cube c) = { g ∈ Fin 8 : c.isGap g = true }    (stalk)
    F(edge e) = { (g₁,g₂) : transferOp(c₁,c₂,g₁,g₂) = true }  (edge stalk)

  Main results:
  - Stalk non-emptiness (from gaps_nonempty)
  - Edge stalk empty ↔ blocked edge
  - Global section ↔ Satisfiable (tautologic reformulation)
  - Three obstruction levels in sheaf language

  Depends on: Hierarchy.lean

  See: theory/theorems/THEOREM-D-GAP-SHEAF.md (mathematical statement)
  See: theory/research/GAP-SHEAF-FORMALIZATION.md (sheaf theory background)
-/

import CubeGraph.Hierarchy

namespace CubeGraph

open Cube

/-! ## Section 1: Stalk (Gap Set) -/

/-- The stalk of the gap sheaf at cube i: the set of gaps. -/
def gapStalk (G : CubeGraph) (i : Fin G.cubes.length) : List Vertex :=
  (List.finRange 8).filter fun g => (G.cubes[i]).isGap g

/-- Stalk is non-empty: every cube has at least one gap. -/
theorem gapStalk_nonempty (G : CubeGraph) (i : Fin G.cubes.length) :
    gapStalk G i ≠ [] := by
  intro h_empty
  obtain ⟨v, _, hv⟩ := (gapCount_pos_iff (G.cubes[i])).mp
    (by have := gapCount_pos (G.cubes[i]); omega)
  have h_in : v ∈ gapStalk G i := by
    unfold gapStalk
    rw [List.mem_filter]
    exact ⟨List.mem_finRange v, hv⟩
  rw [h_empty] at h_in
  simp at h_in

/-- Membership in stalk: g ∈ stalk(i) ↔ g is a gap in cube i. -/
theorem mem_gapStalk (G : CubeGraph) (i : Fin G.cubes.length) (g : Vertex) :
    g ∈ gapStalk G i ↔ (G.cubes[i]).isGap g = true := by
  unfold gapStalk
  simp [List.mem_filter, List.mem_finRange]

/-! ## Section 2: Edge Stalk (Compatible Pairs) -/

/-- The edge stalk: compatible gap pairs on an edge. -/
def edgeStalk (G : CubeGraph) (e : Fin G.cubes.length × Fin G.cubes.length) :
    List (Vertex × Vertex) :=
  (List.finRange 8).flatMap fun g₁ =>
    ((List.finRange 8).filter fun g₂ =>
      transferOp (G.cubes[e.1]) (G.cubes[e.2]) g₁ g₂).map fun g₂ => (g₁, g₂)

/-- Membership in edge stalk: (g₁,g₂) ∈ F(e) ↔ transferOp = true. -/
theorem mem_edgeStalk (G : CubeGraph) (e : Fin G.cubes.length × Fin G.cubes.length)
    (g₁ g₂ : Vertex) :
    (g₁, g₂) ∈ edgeStalk G e ↔
    transferOp (G.cubes[e.1]) (G.cubes[e.2]) g₁ g₂ = true := by
  unfold edgeStalk
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
             true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ⟨b, ht, rfl, rfl⟩⟩
    exact ht
  · intro ht
    exact ⟨g₁, ⟨g₂, ht, rfl, rfl⟩⟩

/-- Edge stalk empty ↔ blocked edge. -/
theorem edgeStalk_empty_iff_blocked (G : CubeGraph)
    (e : Fin G.cubes.length × Fin G.cubes.length) :
    edgeStalk G e = [] ↔ blockedEdge G e.1 e.2 := by
  constructor
  · intro h_empty g₁ g₂
    cases ht : transferOp (G.cubes[e.1]) (G.cubes[e.2]) g₁ g₂
    · rfl
    · have h_mem := (mem_edgeStalk G e g₁ g₂).mpr ht
      rw [h_empty] at h_mem
      simp at h_mem
  · intro hb
    -- Every pair has false transfer, so no element can be in edgeStalk
    have h_forall : ∀ g₁ g₂, (g₁, g₂) ∉ edgeStalk G e := by
      intro g₁ g₂ h_mem
      have ht := (mem_edgeStalk G e g₁ g₂).mp h_mem
      rw [hb g₁ g₂] at ht
      exact Bool.noConfusion ht
    cases h_eq : edgeStalk G e with
    | nil => rfl
    | cons p ps =>
      obtain ⟨g₁, g₂⟩ := p
      exfalso
      have h_mem : (g₁, g₂) ∈ edgeStalk G e := by
        rw [h_eq]; exact List.mem_cons_self
      exact h_forall g₁ g₂ h_mem

/-! ## Section 3: Global Section -/

/-- A global section of the gap sheaf: a compatible gap selection.
    This is definitionally identical to `Satisfiable` but in sheaf language. -/
structure GapGlobalSection (G : CubeGraph) where
  /-- Assignment of a gap vertex to each cube -/
  assign : (i : Fin G.cubes.length) → Vertex
  /-- Each assigned vertex is in the stalk (is a gap) -/
  assign_in_stalk : ∀ (i : Fin G.cubes.length),
    Cube.isGap (G.cubes[i]) (assign i) = true
  /-- Each pair on an edge is in the edge stalk (compatible) -/
  assign_compatible : ∀ e ∈ G.edges,
    transferOp (G.cubes[e.1]) (G.cubes[e.2]) (assign e.1) (assign e.2) = true

/-- **Global section ↔ Satisfiable.**
    This is the central sheaf-theoretic reformulation of SAT.
    Tautologic but conceptually important: SAT = ∃ global section. -/
theorem globalSection_iff_sat (G : CubeGraph) :
    Nonempty (GapGlobalSection G) ↔ G.Satisfiable := by
  constructor
  · intro ⟨gs⟩
    exact ⟨gs.assign, gs.assign_in_stalk, gs.assign_compatible⟩
  · intro ⟨s, hv, hc⟩
    exact ⟨⟨s, hv, hc⟩⟩

/-- No global section ↔ UNSAT. Contrapositive of the above. -/
theorem no_globalSection_iff_unsat (G : CubeGraph) :
    ¬ Nonempty (GapGlobalSection G) ↔ ¬ G.Satisfiable := by
  constructor
  · intro h hs
    exact h ((globalSection_iff_sat G).mpr hs)
  · intro h ⟨gs⟩
    exact h ((globalSection_iff_sat G).mp ⟨gs⟩)

/-! ## Section 4: Obstruction Levels in Sheaf Language -/

/-- **H⁰ in sheaf language**: a stalk is empty.
    Impossible by Cube.gaps_nonempty (gapMask > 0). -/
theorem sheaf_h0_impossible (G : CubeGraph) :
    ∀ i : Fin G.cubes.length, gapStalk G i ≠ [] :=
  gapStalk_nonempty G

/-- **H¹ in sheaf language**: some edge stalk is empty.
    Equivalent to HasBlockedEdge. -/
theorem sheaf_h1_iff_blocked (G : CubeGraph) :
    (∃ e ∈ G.edges, edgeStalk G e = []) ↔ HasBlockedEdge G := by
  constructor
  · intro ⟨e, he, h_empty⟩
    exact ⟨e, he, (edgeStalk_empty_iff_blocked G e).mp h_empty⟩
  · intro ⟨e, he, hb⟩
    exact ⟨e, he, (edgeStalk_empty_iff_blocked G e).mpr hb⟩

/-- **H² in sheaf language**: all stalks non-empty, all edge stalks non-empty,
    but no global section exists. -/
theorem sheaf_h2_characterization (G : CubeGraph) :
    UNSATType2 G ↔
    (¬ Nonempty (GapGlobalSection G) ∧
     (∀ i : Fin G.cubes.length, gapStalk G i ≠ []) ∧
     (∀ e ∈ G.edges, edgeStalk G e ≠ [])) := by
  constructor
  · intro ⟨h_unsat, _, h_no_blocked⟩
    refine ⟨(no_globalSection_iff_unsat G).mpr h_unsat, sheaf_h0_impossible G, ?_⟩
    intro e he h_empty
    exact h_no_blocked ⟨e, he, (edgeStalk_empty_iff_blocked G e).mp h_empty⟩
  · intro ⟨h_no_gs, _, h_edge_nonempty⟩
    refine ⟨(no_globalSection_iff_unsat G).mp h_no_gs, H0_impossible G, ?_⟩
    intro ⟨e, he, hb⟩
    exact h_edge_nonempty e he ((edgeStalk_empty_iff_blocked G e).mpr hb)

end CubeGraph
