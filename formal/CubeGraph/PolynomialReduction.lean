/-
  CubeGraph/PolynomialReduction.lean — Polynomial Size Reduction

  Strengthens geometric_reduction from logical equivalence to polynomial reduction:
  - cubesToGraph preserves size: |G.cubes| = |input|, |G.edges| ≤ |input|²
  - Equivalence: Satisfiable ↔ FormulaSat (already proven, unconditional)
  - Combined: Karp reduction from 3-SAT to CubeGraph SAT with poly size bound

  This ensures that lower bounds on CubeGraph proof complexity transfer
  to lower bounds on 3-SAT proof complexity.

  See: FormulaToGraph.lean (cubesToGraph construction)
  See: GeometricReduction.lean (logical equivalence)
  See: CNF.lean (FormulaSat ↔ Satisfiable)
-/

import CubeGraph.FormulaToGraph

namespace CubeGraph

/-! ## Section 1: Size bounds on cubesToGraph -/

/-- cubesToGraph preserves cube count exactly. -/
theorem cubesToGraph_cubes_length (cubes : List Cube) :
    (cubesToGraph cubes).cubes.length = cubes.length := by
  simp [cubesToGraph]

/-- Edge count bounded by cubes² (all directed pairs). -/
theorem cubesToGraph_edges_le_square (cubes : List Cube) :
    (cubesToGraph cubes).edges.length ≤ cubes.length * cubes.length := by
  simp only [cubesToGraph]
  -- edges = allDirectedEdges cubes = subset of all (i,j) pairs
  -- allDirectedEdges generates ≤ |cubes|² edges (one per ordered pair)
  unfold allDirectedEdges
  -- allDirectedEdges ⊆ all ordered pairs (i,j) with i,j ∈ Fin n.
  -- |allDirectedEdges| ≤ n² because each pair appears at most once.
  -- Proof: flatMap over finRange n, each producing ≤ n elements via filter+map.
  -- flatMap length ≤ Σᵢ |f(i)| ≤ n · n = n².
  show (allDirectedEdges cubes).length ≤ cubes.length * cubes.length
  unfold allDirectedEdges
  let n := cubes.length
  let f : Fin n → List (Fin n × Fin n) := fun i =>
    ((List.finRange n).filter fun j =>
      decide (i ≠ j ∧ Cube.linkWeight cubes[i] cubes[j] > 0)).map fun j => (i, j)
  -- Each f(i) has length ≤ n
  have hf : ∀ i : Fin n, (f i).length ≤ n := by
    intro i; show (((List.finRange n).filter _).map _).length ≤ n
    rw [List.length_map]
    exact Nat.le_trans (List.length_filter_le _ _) (List.length_finRange ▸ Nat.le_refl n)
  -- Prove by induction on the finRange list
  suffices ∀ (xs : List (Fin n)), xs.length ≤ n →
      (xs.flatMap f).length ≤ xs.length * n by
    have := this (List.finRange n) (List.length_finRange ▸ Nat.le_refl n)
    rwa [List.length_finRange] at this
  intro xs hxs
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hrest : rest.length ≤ n := by
      simp [List.length_cons] at hxs; omega
    have h_ih := ih hrest
    have h_fx := hf x
    -- (f x).length + (rest.flatMap f).length ≤ n + rest.length * n = (rest.length + 1) * n
    -- Goal: (f x).length + (flatMap f rest).length ≤ (rest.length + 1) * n
    -- From: h_fx : (f x).length ≤ n, h_ih : (flatMap f rest).length ≤ rest.length * n
    have h_eq : (rest.length + 1) * n = n + rest.length * n := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [h_eq]
    exact Nat.add_le_add h_fx h_ih

/-! ## Section 2: Polynomial reduction (Karp-style) -/

/-- **Polynomial Reduction**: cubesToGraph is a size-preserving reduction.
    - Cube count preserved exactly: |G.cubes| = |input|
    - Edge count bounded: |G.edges| ≤ |input|²
    - Satisfiability equivalent: G.Satisfiable ↔ G.FormulaSat

    This is the STRONG form of geometric_reduction:
    3-SAT → CubeGraph with polynomial size bound.

    Consequence: any proof complexity lower bound on CubeGraph SAT
    transfers to 3-SAT with at most polynomial overhead. -/
theorem polynomial_reduction (cubes : List Cube) :
    -- Size bounds (polynomial)
    (cubesToGraph cubes).cubes.length = cubes.length ∧
    (cubesToGraph cubes).edges.length ≤ cubes.length * cubes.length ∧
    -- Satisfiability equivalence
    ((cubesToGraph cubes).Satisfiable ↔ (cubesToGraph cubes).FormulaSat) :=
  ⟨cubesToGraph_cubes_length cubes,
   cubesToGraph_edges_le_square cubes,
   cubesToGraph_sat_iff cubes⟩

end CubeGraph
