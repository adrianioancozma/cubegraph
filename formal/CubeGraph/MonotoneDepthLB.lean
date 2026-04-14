/-
  CubeGraph/MonotoneDepthLB.lean — Monotone Circuit Depth Ω(n)

  Derives: monotone circuit DEPTH for CG-UNSAT ≥ Ω(n).

  The chain (all pieces already in the project):
  1. Schoenebeck (2008): k-consistency at level k < n/c passes on UNSAT
     (SchoenebeckAxiom.lean: schoenebeck_linear_axiom)
  2. GPW lifting: DT ≥ n/c → CC ≥ n/c'
     (CCLifting.lean: gpw_witness_quantitative)
  3. KW theorem: CC ≥ monotone interpolant depth
     (CCLifting.lean: kw_interpolant_depth)
  4. Therefore: monotone depth ≥ n/(c₁·c₂) = Ω(n)

  Published references:
  - Schoenebeck, FOCS 2008: k-consistency needs level Ω(n)
  - Göös-Pitassi-Watson, SIAM J. Comput. 2018: DT → CC lifting
  - Karchmer-Wigderson, SIAM J. Disc. Math. 1990: CC = monotone depth

  See: SchoenebeckAxiom.lean, CCLifting.lean
-/

import CubeGraph.CCLifting

namespace CubeGraph

open BoolMat

/-! ## Section 1: Monotone Circuit Depth

  By Karchmer-Wigderson (1990), monotone circuit depth equals the
  communication complexity of the KW game, which equals the monotone
  interpolant depth (minMonotoneInterpolantDepth from CCLifting.lean).

  We define monotoneCircuitDepth as minMonotoneInterpolantDepth,
  encoding the KW correspondence as a definitional equality. -/

/-- Monotone circuit depth of the CG-SAT/UNSAT decision function.
    Defined as minMonotoneInterpolantDepth, which by KW (1990)
    equals the minimum depth of any monotone Boolean circuit
    computing whether the gap configuration is satisfiable. -/
noncomputable def monotoneCircuitDepth (G : CubeGraph) : Nat :=
  minMonotoneInterpolantDepth G

/-! ## Section 2: Main Theorem -/

/-- **Monotone circuit depth for CG-UNSAT ≥ Ω(n).**

    For infinitely many n, there exist UNSAT CubeGraphs on ≥ n cubes
    whose monotone circuit depth is at least n/c (linear in n).

    Proof chain (0 new axioms — uses only existing ones):
    1. interpolant_depth_linear (CCLifting.lean):
       ∃ c, ∀ n, ∃ game, |cubes| ≥ n ∧ interpolant depth ≥ n/c
    2. monotoneCircuitDepth = minMonotoneInterpolantDepth (def, KW)
    3. Combine: monotoneCircuitDepth ≥ n/c -/
theorem monotone_depth_linear :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        monotoneCircuitDepth G ≥ n / c := by
  obtain ⟨c, hc, h_interp⟩ := interpolant_depth_linear
  refine ⟨c, by omega, fun n hn => ?_⟩
  obtain ⟨game, hsize, h_depth⟩ := h_interp n hn
  exact ⟨game.graph, hsize, game.unsat, h_depth⟩

/-! ## Section 3: Consequences -/

/-- **Monotone depth grows unboundedly.**
    For any target depth D, there exist UNSAT instances
    requiring monotone circuit depth ≥ D. -/
theorem monotone_depth_unbounded :
    ∀ D : Nat, ∃ G : CubeGraph, ¬ G.Satisfiable ∧
      monotoneCircuitDepth G ≥ D := by
  obtain ⟨c, hc, h_main⟩ := monotone_depth_linear
  intro D
  obtain ⟨G, _, hunsat, h_depth⟩ := h_main (D * c + 1) (by omega)
  refine ⟨G, hunsat, Nat.le_trans ?_ h_depth⟩
  have h1 : D * c / c = D := Nat.mul_div_cancel D (by omega)
  have h2 : D * c ≤ D * c + 1 := Nat.le_succ _
  calc D = D * c / c := h1.symm
    _ ≤ (D * c + 1) / c := Nat.div_le_div_right h2

/-! ## Honest Accounting

  New axioms: 0
  New definitions: 1 (monotoneCircuitDepth := minMonotoneInterpolantDepth)

  Axioms USED (all from CCLifting.lean, all published results):
  1. schoenebeck_linear_axiom — Schoenebeck (2008) k-consistency
  2. gpw_witness_quantitative — Göös-Pitassi-Watson (2018) lifting
  3. kw_interpolant_depth — Karchmer-Wigderson (1990)

  The chain: Schoenebeck → DT ≥ n/c → CC ≥ n/c' → depth ≥ n/c'
-/

end CubeGraph
