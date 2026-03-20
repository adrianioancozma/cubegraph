/-
  CubeGraph/Hierarchy.lean
  Phase 8 (T2-B): H⁰/H¹/H² UNSAT Hierarchy.

  Formalizes the central contribution: UNSAT decomposes into three
  cohomological types with provable separation.

  - H⁰: dead cube (gapCount = 0) — impossible by Cube invariant
  - H¹: blocked edge (zero transfer operator) — polynomial detection
  - H²: global incoherence — no local witness, NP-hard

  At critical density (ρ ≈ 4.27), 100% of UNSAT is H² (empirical).
  This explains why 3-SAT is hard: the obstruction is purely global.

  See: theory/theorems/THEOREM-A-HIERARCHY.md (full mathematical statement)
  See: theory/theorems/THEOREM-D-GAP-SHEAF.md (sheaf-theoretic reformulation)
  See: formal/CubeGraph/MinimalBarrier.lean (small_not_H2: ≤ 2 cubes → ¬ H²)
-/

import CubeGraph.GapLemmas
import CubeGraph.PartB

namespace CubeGraph

open BoolMat

/-! ## Section 1: Structural Predicates -/

/-- A CubeGraph has a dead cube: some cube has zero gaps. -/
def HasDeadCube (G : CubeGraph) : Prop :=
  ∃ i : Fin G.cubes.length, (G.cubes[i]).gapCount = 0

/-- A CubeGraph has a blocked edge: some edge has zero transfer operator.
    Reuses `blockedEdge` from PartB.lean. -/
def HasBlockedEdge (G : CubeGraph) : Prop :=
  ∃ e ∈ G.edges, blockedEdge G e.1 e.2

/-! ## Section 2: UNSAT Type Definitions -/

/-- **H⁰ UNSAT**: caused by a dead cube (gapCount = 0).
    Detectable in O(n) — just check each cube's gap count. -/
def UNSATType0 (G : CubeGraph) : Prop :=
  ¬ G.Satisfiable ∧ HasDeadCube G

/-- **H¹ UNSAT**: caused by a blocked edge (zero transfer operator).
    No dead cubes, but some edge forbids all gap pairs.
    Detectable in O(m · 64) — check each edge's transfer operator. -/
def UNSATType1 (G : CubeGraph) : Prop :=
  ¬ G.Satisfiable ∧ ¬ HasDeadCube G ∧ HasBlockedEdge G

/-- **H² UNSAT**: global incoherence. No dead cubes, no blocked edges,
    yet unsatisfiable. All local checks pass — the contradiction
    is purely global. This is where NP-hardness lives.
    At critical density, 100% of UNSAT is this type (empirical). -/
def UNSATType2 (G : CubeGraph) : Prop :=
  ¬ G.Satisfiable ∧ ¬ HasDeadCube G ∧ ¬ HasBlockedEdge G

/-! ## Section 3: Structural Predicates → UNSAT -/

/-- Dead cube implies UNSAT (wraps complete_cube_unsat).
    **Note on vacuity**: This theorem is vacuously true for `CubeGraph` because
    `Cube.gaps_nonempty` requires `gapMask.val > 0`, making `HasDeadCube`
    unconstructible. This is proven by `H0_impossible` below.
    The non-vacuous content is captured by `sat_implies_no_dead` (Theorems.lean)
    which proves the contrapositive: SAT → all cubes have gaps > 0.
    See also `sat_implies_no_dead_cubes` below for the Hierarchy-level companion. -/
theorem dead_cube_implies_unsat (G : CubeGraph) (h : HasDeadCube G) :
    ¬ G.Satisfiable := by
  obtain ⟨i, hi⟩ := h
  exact complete_cube_unsat G i hi

/-- Blocked edge implies UNSAT (wraps blocked_edge_implies_unsat). -/
theorem hasBlockedEdge_implies_unsat (G : CubeGraph) (h : HasBlockedEdge G) :
    ¬ G.Satisfiable := by
  obtain ⟨e, he, hb⟩ := h
  exact blocked_edge_implies_unsat G e.1 e.2 he hb

/-! ## Section 4: H⁰ Impossibility -/

/-- H⁰ is impossible: every well-formed cube has gaps ≥ 1 (from Cube.gaps_nonempty). -/
theorem H0_impossible (G : CubeGraph) : ¬ HasDeadCube G := by
  intro ⟨i, hi⟩
  have := no_dead_cubes G i
  omega

/-- Corollary: UNSATType0 never occurs for well-formed CubeGraphs. -/
theorem UNSATType0_impossible (G : CubeGraph) : ¬ UNSATType0 G := by
  intro ⟨_, hd⟩
  exact H0_impossible G hd

/-- Since H⁰ is impossible, UNSATType1 simplifies: ¬HasDeadCube is always true. -/
theorem UNSATType1_iff (G : CubeGraph) :
    UNSATType1 G ↔ ¬ G.Satisfiable ∧ HasBlockedEdge G := by
  constructor
  · intro ⟨hsat, _, hbe⟩
    exact ⟨hsat, hbe⟩
  · intro ⟨hsat, hbe⟩
    exact ⟨hsat, H0_impossible G, hbe⟩

/-! ## Section 5: Decidability -/

/-- blockedEdge is decidable: ∀ over Fin 8 × Fin 8 with Bool equality.
    Same pattern as BoolMat.isZero (BoolMat.lean:37-38). -/
instance instDecidableBlockedEdge (G : CubeGraph) (i j : Fin G.cubes.length) :
    Decidable (blockedEdge G i j) :=
  inferInstanceAs (Decidable (∀ g₁ g₂ : Vertex,
    transferOp (G.cubes[i]) (G.cubes[j]) g₁ g₂ = false))

/-- HasDeadCube is decidable: ∃ over Fin n with Nat equality. -/
instance instDecidableHasDeadCube (G : CubeGraph) : Decidable (HasDeadCube G) :=
  inferInstanceAs (Decidable (∃ i : Fin G.cubes.length, (G.cubes[i]).gapCount = 0))

/-- HasBlockedEdge is decidable: ∃ over a finite list with decidable predicate. -/
instance instDecidableHasBlockedEdge (G : CubeGraph) : Decidable (HasBlockedEdge G) := by
  unfold HasBlockedEdge
  exact List.decidableBEx (fun e => blockedEdge G e.1 e.2) G.edges

/-! ## Section 6: Trichotomy -/

/-- Every UNSAT CubeGraph falls into exactly one of the three types. -/
theorem unsat_trichotomy (G : CubeGraph) (h : ¬ G.Satisfiable) :
    UNSATType0 G ∨ UNSATType1 G ∨ UNSATType2 G := by
  by_cases hdc : HasDeadCube G
  · exact .inl ⟨h, hdc⟩
  · by_cases hbe : HasBlockedEdge G
    · exact .inr (.inl ⟨h, hdc, hbe⟩)
    · exact .inr (.inr ⟨h, hdc, hbe⟩)

/-! ## Section 7: Disjointness -/

/-- The three UNSAT types are mutually exclusive. -/
theorem types_disjoint (G : CubeGraph) :
    ¬ (UNSATType0 G ∧ UNSATType1 G) ∧
    ¬ (UNSATType0 G ∧ UNSATType2 G) ∧
    ¬ (UNSATType1 G ∧ UNSATType2 G) := by
  refine ⟨?_, ?_, ?_⟩
  · -- H⁰ ∧ H¹: HasDeadCube vs ¬HasDeadCube
    intro ⟨⟨_, hdc⟩, ⟨_, hndc, _⟩⟩
    exact hndc hdc
  · -- H⁰ ∧ H²: HasDeadCube vs ¬HasDeadCube
    intro ⟨⟨_, hdc⟩, ⟨_, hndc, _⟩⟩
    exact hndc hdc
  · -- H¹ ∧ H²: HasBlockedEdge vs ¬HasBlockedEdge
    intro ⟨⟨_, _, hbe⟩, ⟨_, _, hnbe⟩⟩
    exact hnbe hbe

/-! ## Section 8: H² Local Invisibility -/

/-- ¬blockedEdge implies ∃ compatible gap pair (Bool contrapositive). -/
theorem not_blocked_exists_compatible (G : CubeGraph)
    (i j : Fin G.cubes.length) (h : ¬ blockedEdge G i j) :
    ∃ g₁ g₂ : Vertex, transferOp (G.cubes[i]) (G.cubes[j]) g₁ g₂ = true := by
  apply Classical.byContradiction
  intro h_neg
  apply h
  intro g₁ g₂
  cases hf : transferOp (G.cubes[i]) (G.cubes[j]) g₁ g₂
  · rfl
  · exact absurd ⟨g₁, g₂, hf⟩ h_neg

/-- **H² UNSAT passes all local checks.**
    If a CubeGraph is H² UNSAT:
    (1) Every cube has at least one gap (no dead cubes)
    (2) Every edge has at least one compatible gap pair (no blocked edges)
    This formalizes that H² has NO LOCAL WITNESS — the contradiction
    is purely global, explaining why 3-SAT is NP-hard at critical density. -/
theorem H2_locally_invisible (G : CubeGraph) (h : UNSATType2 G) :
    (∀ i : Fin G.cubes.length, (G.cubes[i]).gapCount > 0) ∧
    (∀ e ∈ G.edges,
      ∃ g₁ g₂ : Vertex, transferOp (G.cubes[e.1]) (G.cubes[e.2]) g₁ g₂ = true) := by
  obtain ⟨_, hndc, hnbe⟩ := h
  constructor
  · -- Part 1: all cubes have gaps
    intro i
    have := no_dead_cubes G i
    omega
  · -- Part 2: all edges have compatible pairs
    intro e he
    have : ¬ blockedEdge G e.1 e.2 := by
      intro hb
      exact hnbe ⟨e, he, hb⟩
    exact not_blocked_exists_compatible G e.1 e.2 this

/-! ## Section 9: Summary Theorems -/

/-- H² is the residual: UNSAT with no structural obstruction. -/
theorem H2_residual (G : CubeGraph) :
    UNSATType2 G ↔ ¬ G.Satisfiable ∧ ¬ HasDeadCube G ∧ ¬ HasBlockedEdge G :=
  Iff.rfl

/-- Since H⁰ is impossible, every UNSAT graph is either H¹ or H². -/
theorem unsat_dichotomy (G : CubeGraph) (h : ¬ G.Satisfiable) :
    HasBlockedEdge G ∨ UNSATType2 G := by
  rcases unsat_trichotomy G h with ⟨_, hdc⟩ | ⟨_, _, hbe⟩ | h2
  · exact absurd hdc (H0_impossible G)
  · exact .inl hbe
  · exact .inr h2

/-! ## Section 10: Non-vacuous Companions -/

/-- Non-vacuous companion of `dead_cube_implies_unsat`:
    any satisfiable CubeGraph has no dead cubes.
    Unlike the forward direction (which is vacuously true because `HasDeadCube`
    is unconstructible), this is non-vacuous because satisfiable CubeGraphs exist.
    For a concrete example, see `Witness.lean`. -/
theorem sat_implies_no_dead_cubes (G : CubeGraph) (h : G.Satisfiable) :
    ¬ HasDeadCube G :=
  fun hd => dead_cube_implies_unsat G hd h

end CubeGraph
