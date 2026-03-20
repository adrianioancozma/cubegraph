/-
  CubeGraph/GeometricReduction.lean
  T11: Reduction to Pure Geometry.

  Proves the tripartite equivalence:
    GeoSat (geometric)  ↔  FormulaSat (classical SAT)  ↔  Satisfiable (CubeGraph)

  The geometric formulation (GeoSat) states 3-SAT purely as:
    "Do the oriented 3D subspaces of {0,1}^n have a globally coherent point?"

  Each clause = one forbidden projection in a 3D subcube of the Boolean hypercube.
  SAT = Euclid (global coherence exists).
  UNSAT = Escher (global incompatibility, no single point avoids all forbidden projections).

  Core insight: this is definitionally equivalent to 3-SAT, but the geometric
  vocabulary connects naturally to cohomological obstruction theory (H², sheaves)
  and the Expanding Escher locality lower bound.

  Main results:
  - geo_sat_iff_formula_sat: GeoSat ↔ FormulaSat
  - geo_sat_iff_satisfiable: GeoSat ↔ Satisfiable
  - geometric_reduction: the self-contained statement for papers
  - tripartite_equivalence: all three views unified

  See: theory/foundations/06-empty-vertex-duality.md (complement duality)
  See: experiments-ml/019_2026-03-13_topological-hardness/EXPANDING-ESCHER-RESULTS.md
  See: project-map/004_2026-03-14/FORMALIZATION-CANDIDATES.md §2.38
  See: project-map/004_2026-03-14/INVENTORY.md §2.38
  Plan: experiments-ml/021_2026-03-17_triage-review/TODO.md (Faza 0 — import fix)
-/

import CubeGraph.Basic
import CubeGraph.CNF

namespace CubeGraph

/-! ## Section 1: Pure Geometric Definitions

These definitions are self-contained: no Cube, no CubeGraph, no gapMask.
A reader can understand GeoSat knowing only Boolean assignments and Nat indices. -/

/-- A geometric constraint: 3 variable indices + one forbidden assignment.
    Represents one 3-SAT clause as a "forbidden point" in an oriented 3D subcube
    of the Boolean hypercube {0,1}^n.

    For clause (ℓ₁ ∨ ℓ₂ ∨ ℓ₃) on variables (v₁, v₂, v₃):
    - σᵢ = false if ℓᵢ = xᵢ (positive literal)
    - σᵢ = true  if ℓᵢ = ¬xᵢ (negated literal)
    The clause is falsified exactly when x_vᵢ = σᵢ for all i simultaneously. -/
structure GeoConstraint where
  v₁ : Nat
  v₂ : Nat
  v₃ : Nat
  σ₁ : Bool
  σ₂ : Bool
  σ₃ : Bool

/-- A geometric formula: a list of geometric constraints (one per clause). -/
abbrev GeoFormula := List GeoConstraint

/-- An assignment satisfies a geometric constraint iff the projected point
    differs from the forbidden point in at least one coordinate.
    Equivalently: NOT-ALL-ZERO after XOR with σ. -/
def geoConstraintSat (gc : GeoConstraint) (x : Nat → Bool) : Prop :=
  ¬(x gc.v₁ = gc.σ₁ ∧ x gc.v₂ = gc.σ₂ ∧ x gc.v₃ = gc.σ₃)

/-- **T11 Definition**: Geometric satisfiability.
    There exists a point x ∈ {0,1}^n that avoids all forbidden projections.
    This IS 3-SAT, stated as pure combinatorial geometry. -/
def GeoSat (F : GeoFormula) : Prop :=
  ∃ x : Nat → Bool, ∀ gc ∈ F, geoConstraintSat gc x

/-! ## Section 2: CubeGraph → GeoFormula Expansion

Each filled vertex in a cube becomes one geometric constraint.
The forbidden assignment σ is the complement of the filled vertex bits
(since the filled vertex encodes literal polarities, and the complement
gives the unique falsifying assignment). -/

/-- Convert a filled vertex in a cube to its geometric constraint.
    The forbidden assignment σ has σᵢ = ¬(bit i of v).
    This is because filled vertex v with bit i = 1 means literal xᵢ is positive,
    and the falsifying value is xᵢ = false = ¬(bit 1). -/
def filledVertexToGeo (c : Cube) (v : Vertex) : GeoConstraint :=
  { v₁ := c.var₁, v₂ := c.var₂, v₃ := c.var₃,
    σ₁ := !(Cube.vertexBit v ⟨0, by omega⟩),
    σ₂ := !(Cube.vertexBit v ⟨1, by omega⟩),
    σ₃ := !(Cube.vertexBit v ⟨2, by omega⟩) }

/-- Expand a cube into its list of geometric constraints (one per filled vertex). -/
def cubeToGeo (c : Cube) : GeoFormula :=
  (List.finRange 8).filterMap fun v =>
    if c.isGap v then none else some (filledVertexToGeo c v)

/-- Expand an entire CubeGraph into a GeoFormula. -/
def cubeGraphToGeo (G : CubeGraph) : GeoFormula :=
  G.cubes.flatMap cubeToGeo

/-! ## Section 3: Forward Direction (FormulaSat → GeoSat)

If a global assignment satisfies all cubes (FormulaSat),
then it avoids all forbidden projections (GeoSat). -/

/-- Two vertices in Fin 8 are equal iff all 3 bits match. -/
private theorem vertex_eq_iff_bits (u v : Vertex) :
    u = v ↔ (∀ j : Fin 3, Cube.vertexBit u j = Cube.vertexBit v j) := by
  constructor
  · intro h; subst h; intro; rfl
  · revert u v; native_decide

/-- The assignment-to-gap bits determine the forbidden point of a filled vertex.
    If assignmentToGap matches the filled vertex on all bits,
    then the assignment equals the forbidden σ on all variables. -/
private theorem geo_match_of_gap_eq (c : Cube) (a : Assignment) (v : Vertex)
    (_hfilled : c.isGap v = false) (hgap_eq : assignmentToGap a c = v) :
    a c.var₁ = (filledVertexToGeo c v).σ₁ ∧
    a c.var₂ = (filledVertexToGeo c v).σ₂ ∧
    a c.var₃ = (filledVertexToGeo c v).σ₃ := by
  have hbit0 := assignmentToGap_bit a c ⟨0, by omega⟩
  have hbit1 := assignmentToGap_bit a c ⟨1, by omega⟩
  have hbit2 := assignmentToGap_bit a c ⟨2, by omega⟩
  simp only [Cube.varAt] at hbit0 hbit1 hbit2
  rw [vertex_eq_iff_bits] at hgap_eq
  have h0 := hgap_eq ⟨0, by omega⟩
  have h1 := hgap_eq ⟨1, by omega⟩
  have h2 := hgap_eq ⟨2, by omega⟩
  rw [hbit0] at h0
  rw [hbit1] at h1
  rw [hbit2] at h2
  simp only [filledVertexToGeo]
  exact ⟨by simp_all, by simp_all, by simp_all⟩

/-- Core per-cube lemma: allClausesSat implies all geo constraints satisfied.
    If the gap vertex is a gap, it can't equal any filled vertex,
    so the assignment avoids every forbidden projection. -/
theorem allClausesSat_implies_geoSat (c : Cube) (a : Assignment)
    (h : allClausesSat c a) :
    ∀ gc ∈ cubeToGeo c, geoConstraintSat gc a := by
  intro gc hgc
  -- gc ∈ cubeToGeo c means gc = filledVertexToGeo c v for some filled v
  simp only [cubeToGeo, List.mem_filterMap] at hgc
  obtain ⟨v, _, hgc_eq⟩ := hgc
  split at hgc_eq
  · contradiction  -- isGap v = true, but we got some
  · simp at hgc_eq
    subst hgc_eq
    -- Now gc = filledVertexToGeo c v and isGap v = false
    rename_i hfilled
    -- h : allClausesSat c a means isGap(assignmentToGap a c) = true
    unfold allClausesSat at h
    -- If assignment matched the forbidden point, then assignmentToGap = v (filled) — contradiction
    intro ⟨heq1, heq2, heq3⟩
    -- Reconstruct: a matches σ → assignmentToGap a c = v → isGap v = true contradicts hfilled
    have hbit0 := assignmentToGap_bit a c ⟨0, by omega⟩
    have hbit1 := assignmentToGap_bit a c ⟨1, by omega⟩
    have hbit2 := assignmentToGap_bit a c ⟨2, by omega⟩
    simp only [Cube.varAt] at hbit0 hbit1 hbit2
    simp only [filledVertexToGeo] at heq1 heq2 heq3
    -- From heq: a var_i = !(vertexBit v i), so !(a var_i) = vertexBit v i
    -- From hbit: vertexBit (assignmentToGap a c) i = !(a var_i) = vertexBit v i
    -- Hence assignmentToGap a c = v by vertex_eq_iff_bits
    have hall : assignmentToGap a c = v := by
      rw [vertex_eq_iff_bits]
      intro j
      match j with
      | ⟨0, _⟩ => simp_all
      | ⟨1, _⟩ => simp_all
      | ⟨2, _⟩ => simp_all
    -- But h says isGap(assignmentToGap a c) = true, and hfilled says isGap v = false
    rw [hall] at h; simp_all

/-- Forward: FormulaSat → GeoSat. -/
theorem formula_sat_implies_geo_sat (G : CubeGraph) (h : G.FormulaSat) :
    GeoSat (cubeGraphToGeo G) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun gc hgc => ?_⟩
  simp only [cubeGraphToGeo, List.mem_flatMap] at hgc
  obtain ⟨c, hc_mem, hgc_in_c⟩ := hgc
  -- c ∈ G.cubes, gc ∈ cubeToGeo c
  have ⟨idx, hlt, heq⟩ := List.mem_iff_getElem.mp hc_mem
  have hcube := ha ⟨idx, hlt⟩
  simp only [Fin.getElem_fin, heq] at hcube
  exact allClausesSat_implies_geoSat c a hcube gc hgc_in_c

/-! ## Section 4: Backward Direction (GeoSat → FormulaSat)

If a point avoids all forbidden projections (GeoSat),
then it satisfies all cubes (FormulaSat). -/

/-- If a vertex differs from all filled (non-gap) vertices, it must be a gap. -/
private theorem gap_of_ne_all_filled (c : Cube) (w : Vertex)
    (h : ∀ v : Vertex, c.isGap v = false → w ≠ v) :
    c.isGap w = true := by
  cases hgw : c.isGap w with
  | true => rfl
  | false => exact absurd rfl (h w hgw)

/-- Geo constraint membership in cubeToGeo: unfold the filterMap. -/
private theorem mem_cubeToGeo_iff (c : Cube) (gc : GeoConstraint) :
    gc ∈ cubeToGeo c ↔
    ∃ v : Vertex, c.isGap v = false ∧ gc = filledVertexToGeo c v := by
  simp only [cubeToGeo, List.mem_filterMap]
  constructor
  · intro ⟨v, _, hv⟩
    split at hv
    · contradiction
    · simp at hv
      rename_i hfilled
      exact ⟨v, by simp only [Bool.eq_false_iff] at hfilled ⊢; exact hfilled, hv.symm⟩
  · intro ⟨v, hfilled, hgc⟩
    refine ⟨v, List.mem_finRange v, ?_⟩
    simp [hfilled, hgc]

/-- If the assignment avoids all forbidden points from a cube, the gap vertex is a gap.
    Contrapositive: if assignmentToGap a c were filled, it would generate a geo constraint
    that the assignment violates. -/
theorem geoSat_implies_allClausesSat (c : Cube) (a : Assignment)
    (h : ∀ gc ∈ cubeToGeo c, geoConstraintSat gc a) :
    allClausesSat c a := by
  unfold allClausesSat
  apply gap_of_ne_all_filled
  intro v hfilled habs
  -- v is filled, and assignmentToGap a c = v
  -- filledVertexToGeo c v is in cubeToGeo c
  have hgc_mem : filledVertexToGeo c v ∈ cubeToGeo c := by
    rw [mem_cubeToGeo_iff]
    exact ⟨v, hfilled, rfl⟩
  have hsat := h _ hgc_mem
  -- hsat : geoConstraintSat (filledVertexToGeo c v) a
  -- i.e., ¬(a v₁ = σ₁ ∧ a v₂ = σ₂ ∧ a v₃ = σ₃)
  -- But since assignmentToGap a c = v, we CAN show the match holds
  exact hsat (geo_match_of_gap_eq c a v hfilled habs)

/-- Backward: GeoSat → FormulaSat. -/
theorem geo_sat_implies_formula_sat (G : CubeGraph)
    (h : GeoSat (cubeGraphToGeo G)) : G.FormulaSat := by
  obtain ⟨x, hx⟩ := h
  refine ⟨x, fun i => ?_⟩
  apply geoSat_implies_allClausesSat
  intro gc hgc
  apply hx
  simp only [cubeGraphToGeo, List.mem_flatMap]
  exact ⟨G.cubes[i], List.getElem_mem .., hgc⟩

/-! ## Section 5: Main Theorems — Tripartite Equivalence -/

/-- **T11**: Geometric satisfiability equals FormulaSat. -/
theorem geo_sat_iff_formula_sat (G : CubeGraph) :
    GeoSat (cubeGraphToGeo G) ↔ G.FormulaSat :=
  ⟨geo_sat_implies_formula_sat G, formula_sat_implies_geo_sat G⟩

/-- **T11 + T1-A**: Geometric coherence equals CubeGraph satisfiability. -/
theorem geo_sat_iff_satisfiable (G : CubeGraph) :
    GeoSat (cubeGraphToGeo G) ↔ G.Satisfiable := by
  rw [geo_sat_iff_formula_sat, ← sat_iff_formula_sat]

/-- **Geometric Reduction** (self-contained statement for papers):
    A CubeGraph is satisfiable iff there exists a global Boolean assignment
    avoiding all forbidden projections in all oriented 3D subcubes. -/
theorem geometric_reduction (G : CubeGraph) :
    G.Satisfiable ↔
    ∃ x : Nat → Bool, ∀ gc ∈ cubeGraphToGeo G, geoConstraintSat gc x :=
  (geo_sat_iff_satisfiable G).symm

/-- **Tripartite Equivalence**: All three views of 3-SAT are equivalent.
    - Geometric (GeoSat): "oriented 3D subspaces are globally coherent"
    - Classical (FormulaSat): "a truth assignment satisfies all clauses"
    - Algebraic (Satisfiable): "a compatible gap selection exists"

    Euclid = all three hold (SAT).
    Escher = none holds (UNSAT). -/
theorem tripartite_equivalence (G : CubeGraph) :
    (GeoSat (cubeGraphToGeo G) ↔ G.FormulaSat) ∧
    (G.FormulaSat ↔ G.Satisfiable) :=
  ⟨geo_sat_iff_formula_sat G, (sat_iff_formula_sat G).symm⟩

end CubeGraph
