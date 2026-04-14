/-
  CubeGraph/SchoenebeckAxiom.lean
  CANONICAL location for the Schoenebeck (2008) axiom.

  Minimal file: imports only CubeGraph.Basic.
  Other files should import this instead of declaring their own copy.

  The axiom states: SA needs level Ω(n) for random 3-SAT at ρ_c ≈ 4.267.
  Reference: Schoenebeck, "Linear level Lasserre lower bounds for
  certain k-CSPs." FOCS 2008, Theorem 1.1 + Atserias-Dalmau (2008).
-/

import CubeGraph.Basic

namespace CubeGraph

/-! ## k-Consistency (self-contained definition)

  Identical to CubeGraph.KConsistent in KConsistency.lean.
  Defined here to avoid pulling in the heavy KConsistency import chain. -/

/-- **k-Consistency**: every subset of ≤ k cubes admits a compatible gap selection. -/
def SchoenebeckKConsistent (G : CubeGraph) (k : Nat) : Prop :=
  ∀ (S : List (Fin G.cubes.length)),
    S.length ≤ k → S.Nodup →
    ∃ s : (i : Fin G.cubes.length) → Vertex,
      (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true)

/-! ## The Schoenebeck Axiom (canonical) -/

/-- **Schoenebeck (2008) — linear form** (CANONICAL).
    SA needs level Ω(n): there exists c ≥ 2 such that (n/c)-consistency
    passes on n-variable UNSAT CubeGraphs.

    This is the SINGLE canonical statement. All other files should
    import this axiom instead of declaring their own copy.

    Schoenebeck (2008), Theorem 1.1 + Atserias-Dalmau (2008). -/
axiom schoenebeck_linear_axiom :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧
        SchoenebeckKConsistent G (n / c) ∧ ¬ G.Satisfiable

end CubeGraph
