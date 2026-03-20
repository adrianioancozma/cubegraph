/-
  CubeGraph/FormulaToGraph.lean
  Phase A: Automatic CubeGraph construction from a list of cubes.

  Provides `cubesToGraph : List Cube → CubeGraph` which generates all valid
  edges automatically, with `edges_complete` guaranteed by construction.

  Combined with `sat_iff_formula_sat` (unconditional), this gives:
    cubesToGraph(cubes).Satisfiable ↔ cubesToGraph(cubes).FormulaSat
  for any list of cubes, without manual edge construction.

  See: theory/theorems/CORE-THEOREMS-SUMMARY.md (bridge theorem)
  See: theory/foundations/03-cube-graph.md (edge connectivity rules)
-/

import CubeGraph.CNF

namespace CubeGraph

/-! ## Section 1: Edge Generation -/

/-- All directed edges between cubes that share variables.
    Generates (i, j) for ALL ordered pairs i ≠ j where linkWeight > 0.
    This ensures edges_complete by construction: every linked pair appears. -/
def allDirectedEdges (cubes : List Cube) : List (Fin cubes.length × Fin cubes.length) :=
  (List.finRange cubes.length).flatMap fun i =>
    ((List.finRange cubes.length).filter fun j =>
      decide (i ≠ j ∧ Cube.linkWeight cubes[i] cubes[j] > 0)).map fun j => (i, j)

/-! ## Section 2: Membership Characterization -/

/-- Membership in allDirectedEdges unpacked. -/
theorem mem_allDirectedEdges (cubes : List Cube) (i j : Fin cubes.length) :
    (i, j) ∈ allDirectedEdges cubes ↔
    i ≠ j ∧ Cube.linkWeight cubes[i] cubes[j] > 0 := by
  unfold allDirectedEdges
  constructor
  · intro h
    rw [List.mem_flatMap] at h
    obtain ⟨a, _, ha⟩ := h
    rw [List.mem_map] at ha
    obtain ⟨b, hb, hab⟩ := ha
    rw [List.mem_filter] at hb
    have hpred := (decide_eq_true_eq).mp hb.2
    have heq := Prod.mk.inj hab
    rw [← heq.1, ← heq.2]
    exact hpred
  · intro ⟨hne, hlw⟩
    rw [List.mem_flatMap]
    refine ⟨i, List.mem_finRange i, ?_⟩
    rw [List.mem_map]
    refine ⟨j, ?_, rfl⟩
    rw [List.mem_filter]
    exact ⟨List.mem_finRange j, (decide_eq_true_eq).mpr ⟨hne, hlw⟩⟩

/-! ## Section 3: Edge Validity and Completeness -/

/-- All edges in allDirectedEdges connect cubes that share variables. -/
theorem allDirectedEdges_valid (cubes : List Cube) :
    ∀ e ∈ allDirectedEdges cubes,
      Cube.linkWeight cubes[e.1] cubes[e.2] > 0 := by
  intro ⟨ei, ej⟩ he
  exact ((mem_allDirectedEdges cubes ei ej).mp he).2

/-- allDirectedEdges contains all pairs of linked cubes. -/
theorem allDirectedEdges_complete (cubes : List Cube) :
    ∀ i j : Fin cubes.length, i ≠ j →
      Cube.linkWeight cubes[i] cubes[j] > 0 →
      (i, j) ∈ allDirectedEdges cubes ∨ (j, i) ∈ allDirectedEdges cubes := by
  intro i j hij hlw
  exact Or.inl ((mem_allDirectedEdges cubes i j).mpr ⟨hij, hlw⟩)

/-! ## Section 4: CubeGraph Constructor -/

/-- Build a CubeGraph from a list of cubes.
    Edges are generated automatically between all pairs sharing variables.
    Both `edges_valid` and `edges_complete` hold by construction. -/
def cubesToGraph (cubes : List Cube) : CubeGraph where
  cubes := cubes
  edges := allDirectedEdges cubes
  edges_valid := allDirectedEdges_valid cubes
  edges_complete := fun i j hij hlw =>
    Or.inl ((mem_allDirectedEdges cubes i j).mpr ⟨hij, hlw⟩)

/-! ## Section 5: Properties -/

/-- cubesToGraph preserves the cube list. -/
theorem cubesToGraph_cubes (cubes : List Cube) :
    (cubesToGraph cubes).cubes = cubes := rfl

/-- Main theorem: cubesToGraph produces a graph where
    Satisfiable ↔ FormulaSat (unconditionally). -/
theorem cubesToGraph_sat_iff (cubes : List Cube) :
    (cubesToGraph cubes).Satisfiable ↔ (cubesToGraph cubes).FormulaSat :=
  sat_iff_formula_sat _

end CubeGraph
