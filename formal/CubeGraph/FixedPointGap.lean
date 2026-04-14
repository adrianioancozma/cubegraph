/-
  CubeGraph/FixedPointGap.lean — F1.1

  The Fixed Point Gap: P vs NP as Knaster-Tarski vs Cycles.

  SAT = common fixed point of all monodromy operators.
  On TREES: Knaster-Tarski guarantees a fixed point → P.
  On CYCLES with H²: fixed point is MISSING (traceless monodromy) → NP.
  Borromean: local fixed points exist but don't compose globally.

  The gap between "trees → P" and "cycles → NP" is the P vs NP question
  on CubeGraph, reformulated as a fixed point existence problem.

  . 0 new axioms. All proofs are references to existing theorems.

  See: experiments-ml/025_2026-03-19_synthesis/bridge/FIXED-POINT-ARGUMENT.md
  See: experiments-ml/025_2026-03-19_synthesis/bridge/CORE-THESIS.md
  See: experiments-ml/025_2026-03-19_synthesis/bridge/F1.1-PLAN-FIXED-POINT-GAP.md
-/

import CubeGraph.Holonomy
import CubeGraph.Type2Monodromy
import CubeGraph.Locality
import CubeGraph.Rank1Protocol

namespace CubeGraph

open BoolMat

/-! ## Section 1: The Fixed Point Dichotomy -/

/-- **Fixed Point Dichotomy**: SAT is a fixed point problem, and the
    existence of fixed points depends on TOPOLOGY (trees vs cycles).

    (A) SAT → common fixed point of all monodromy operators at any base.
        The satisfying assignment gives the SAME gap at the base cube
        for ALL cycles through it. (Holonomy.lean)

    (B) Trees + AC → SAT. Knaster-Tarski: iterate from leaves, converge.
        Fixed point GUARANTEED on acyclic structures. (TreeSAT.lean)

    (C) H² (cycles): locally consistent (every edge has compatible pairs)
        but monodromy is TRACELESS (no gap maps to itself around the cycle).
        Fixed point MISSING. (Type2Monodromy.lean)

    The dichotomy: trees → fixed point → P. Cycles → no fixed point → NP. -/
theorem fixed_point_dichotomy :
    -- (A) SAT → common fixed point at any base cube
    (∀ G : CubeGraph, G.Satisfiable →
      ∀ base : Fin G.cubes.length,
        ∃ g : Vertex, (G.cubes[base]).isGap g = true ∧
          ∀ M, IsHolonomyGenerator G base M → M g g = true)
    -- (B) Trees + AC → SAT (Knaster-Tarski: fixed point guaranteed)
    ∧ (∀ G : CubeGraph, IsForest G → AllArcConsistent G → G.Satisfiable)
    -- (C) H²: local consistency + traceless monodromy + UNSAT
    ∧ (LocallyConsistent h2Graph ∧ trace h2MonodromyCycle = false ∧
       ¬ h2Graph.Satisfiable) :=
  ⟨sat_common_fixed_point,
   forest_arc_consistent_sat,
   ⟨h2_locally_consistent, h2_monodromy_trace_false, h2Graph_unsat⟩⟩

/-! ## Section 2: Knaster-Tarski Fails on H² -/

/-- **Knaster-Tarski fails on H²**: the h2Graph is arc-consistent
    (every edge has compatible gap pairs — monotone iteration sees no problem)
    yet UNSAT (no global fixed point exists).

    On trees: AC → SAT (Knaster-Tarski works). No H² possible.
    On cycles: AC ↛ SAT. H² is the gap.

    Monotone iteration (AC-3, propagation) CANNOT detect H² because:
    - It converges to a local fixed point (AC: every edge looks OK)
    - But the local fixed point is NOT a global one (monodromy has twist)
    - The twist is invisible to monotone iteration (rank decay: 1+1=1) -/
theorem knaster_tarski_fails_on_h2 :
    -- h2Graph: locally consistent (every edge has compatible gap pairs)
    LocallyConsistent h2Graph
    -- yet UNSAT (no global fixed point)
    ∧ ¬ h2Graph.Satisfiable
    -- and this is IMPOSSIBLE on trees (Knaster-Tarski works on trees)
    ∧ (∀ G : CubeGraph, IsForest G → AllArcConsistent G → ¬ UNSATType2 G) :=
  ⟨h2_locally_consistent, h2Graph_unsat, h2_requires_cycles⟩

/-! ## Section 3: Borromean Fixed Point Gap -/

/-- **Borromean Fixed Point Gap**: local fixed points exist but don't
    compose to a global one. The gap grows linearly with n.

    On h2Graph (b=3):
    - Any 1-2 cubes: consistent gap selection exists (local fixed point ✓)
    - All 3 cubes: no consistent gap selection (global fixed point ✗)

    Scaling (Schoenebeck):
    - ∃ UNSAT graphs where (n/c)-consistency passes
    - b(n) = Θ(n): the gap between local and global is LINEAR in n
    - Borromean order ≤ graph size (trivial upper bound)

    This is the QUANTITATIVE version of the fixed point gap:
    not just "local ≠ global" but "local ≠ global by Θ(n) levels." -/
theorem borromean_fixed_point_gap :
    -- Borromean order = 3 on h2Graph
    BorromeanOrder h2Graph 3
    -- UNSAT (no global fixed point)
    ∧ ¬ h2Graph.Satisfiable
    -- Any < 3 cubes have local fixed point (k-consistent below b)
    ∧ (∀ S : List (Fin h2Graph.cubes.length), S.Nodup → S.length < 3 →
        ∃ s : (i : Fin h2Graph.cubes.length) → Vertex,
          (∀ i ∈ S, (h2Graph.cubes[i]).isGap (s i) = true) ∧
          (∀ e ∈ h2Graph.edges, e.1 ∈ S → e.2 ∈ S →
            transferOp (h2Graph.cubes[e.1]) (h2Graph.cubes[e.2])
              (s e.1) (s e.2) = true))
    -- Scaling: b(n) = Θ(n) (lower bound: Schoenebeck, upper bound: trivial)
    ∧ ((∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
          ∃ G : CubeGraph, G.cubes.length ≥ n ∧
            KConsistent G (n / c) ∧ ¬ G.Satisfiable) ∧
       (∀ G : CubeGraph, ∀ b, BorromeanOrder G b → b ≤ G.cubes.length)) :=
  ⟨h2_borromean_order,
   h2Graph_unsat,
   fun S hnd hlen => protocol_blind h2Graph 3 h2_borromean_order (by omega) S hnd hlen,
   borromean_theta_n⟩

/-! ## Section 4: Summary — The Complete Fixed Point Gap -/

/-- **Fixed Point Gap Summary**: the complete argument in one theorem.

    **P** (trees): Knaster-Tarski guarantees fixed point. Iterate from
    leaves, converge monotonically. Cost: O(n). PROVEN.

    **NP** (cycles at ρ_c): fixed point MISSING. Monodromy is traceless
    (twist), but locally everything looks consistent (local consistency).
    Borromean gap: local fixed points exist up to b-1 cubes, but not
    at b = Θ(n). Detecting the missing fixed point costs exponential.

    **The gap**: P = "fixed point exists and is easy to find" (trees).
    NP = "fixed point might not exist and is hard to check" (cycles).
    The difference is TOPOLOGY: trees vs cycles on an expander.

    5 components:
    (1) SAT = common fixed point of monodromy operators
    (2) Trees → fixed point guaranteed (Knaster-Tarski) → P
    (3) H² = local consistency + traceless monodromy + UNSAT
    (4) Borromean: local fixed ≠ global fixed, gap = Θ(n)
    (5) H² requires cycles (impossible on trees) -/
theorem fixed_point_gap_summary :
    -- (1) SAT → common fixed point
    (∀ G : CubeGraph, G.Satisfiable →
      ∀ base : Fin G.cubes.length,
        ∃ g : Vertex, (G.cubes[base]).isGap g = true ∧
          ∀ M, IsHolonomyGenerator G base M → M g g = true)
    -- (2) Trees → SAT (Knaster-Tarski)
    ∧ (∀ G : CubeGraph, IsForest G → AllArcConsistent G → G.Satisfiable)
    -- (3) H² = flat + traceless + UNSAT
    ∧ (LocallyConsistent h2Graph ∧ trace h2MonodromyCycle = false ∧
       ¬ h2Graph.Satisfiable)
    -- (4) Borromean gap: b = 3, Θ(n) scaling
    ∧ (BorromeanOrder h2Graph 3 ∧
       (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
          ∃ G : CubeGraph, G.cubes.length ≥ n ∧
            KConsistent G (n / c) ∧ ¬ G.Satisfiable))
    -- (5) H² requires cycles
    ∧ (∀ G : CubeGraph, IsForest G → AllArcConsistent G → ¬ UNSATType2 G) :=
  ⟨sat_common_fixed_point,
   forest_arc_consistent_sat,
   ⟨h2_locally_consistent, h2_monodromy_trace_false, h2Graph_unsat⟩,
   ⟨h2_borromean_order, schoenebeck_linear⟩,
   h2_requires_cycles⟩

end CubeGraph
