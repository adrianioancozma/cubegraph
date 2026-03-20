/-
  CubeGraph/Holonomy.lean
  Holonomy monoid at a base cube and the Common Fixed Point Theorem.

  MAIN RESULTS:
  1. IsHolonomyGenerator — predicate for monodromy operators at a base cube
  2. sat_common_fixed_point — SAT → ∃ g ∈ gaps(base), g is a common fixed point
     of ALL monodromy operators at base (quantifier inversion from sat_monodromy_fixed)
  3. holonomy_product_fixed_point — products of generators also have g as fixed point
     (corollary of fixedPoint_foldl: generators suffice)

  The forward direction (SAT → common fixed point) is CORRECT and proven here.
  The backward direction (common fixed point → SAT) is FALSE — counterexample
  in Witness.lean §16 (bwGraph: acyclic + no blocked edges + UNSAT).

  See: experiments-ml/008_2026-03-04_why-h2-hard/DISCOVERY-CHAIN-2026-03-04.md §1-2
  See: experiments-ml/008_2026-03-04_why-h2-hard/SYNTHESIS.md §1 (Common Fixed Point)
-/

import CubeGraph.Monodromy

namespace CubeGraph

open BoolMat

/-! ## Section 1: Holonomy Generator Predicate (T2.1) -/

/-- A matrix M is a **holonomy generator** at base cube `base` if it is the
    monodromy operator of some cycle in G passing through the base cube.

    The holonomy monoid Hol(base) is the closure of all such generators
    under boolean matrix multiplication. We don't need an explicit monoid
    definition (no Mathlib): the predicate + `fixedPoint_foldl` captures
    the key property that generators suffice for computing ∩Fix. -/
def IsHolonomyGenerator (G : CubeGraph) (base : Fin G.cubes.length)
    (M : BoolMat 8) : Prop :=
  ∃ (cycle : List Cube) (h_cyc : CycleInGraph G cycle)
    (i : Fin cycle.length),
    h_cyc.idxs i = base ∧ M = monodromy cycle h_cyc.length_ge i

/-! ## Section 2: Common Fixed Point Theorem (T2.2) -/

/-- **Common Fixed Point Theorem (forward direction)**.

    If G is satisfiable, then for any base cube there exists a gap g
    that is simultaneously a fixed point of EVERY monodromy operator
    at that base cube.

    This strengthens `sat_monodromy_fixed` by inverting the quantifiers:
    - Old: ∀ cycle, ∀ i, ∃ g, M_i[g,g] = true   (per-cycle existential)
    - New: ∃ g, ∀ cycle, ∀ i, M[g,g] = true      (universal fixed point)

    The key insight: the global gap selection `s` gives the same gap
    `s(base)` for ALL cycles through the base cube.

    ⚠️ The backward direction is FALSE — see bw_h15_witness in Witness.lean. -/
theorem sat_common_fixed_point (G : CubeGraph) (h_sat : G.Satisfiable)
    (base : Fin G.cubes.length) :
    ∃ g : Vertex,
      (G.cubes[base]).isGap g = true ∧
      ∀ M : BoolMat 8, IsHolonomyGenerator G base M → M g g = true := by
  -- Extract the satisfying gap selection
  obtain ⟨s, h_valid, h_compat⟩ := h_sat
  -- The witness is s(base): the gap assigned to the base cube
  refine ⟨s base, h_valid base, ?_⟩
  -- For any holonomy generator M at base...
  intro M ⟨cycle, h_cyc, i, hi, hM⟩
  -- ...M is the monodromy of some cycle at position i where idxs i = base
  subst hM
  -- Construct CycleFeasibleAt: the global selection restricted to the cycle
  have h_feasible : CycleFeasibleAt cycle h_cyc.length_ge i (s base) := by
    refine ⟨fun j => s (h_cyc.idxs j), ?_, ?_, ?_⟩
    -- gaps i = s(idxs i) = s(base)
    · simp [hi]
    -- Each gap is valid in its cube
    · intro j
      rw [← h_cyc.cubes_match j]
      exact h_valid (h_cyc.idxs j)
    -- Consecutive gaps are compatible via transferOp
    · intro j
      simp only [← h_cyc.cubes_match]
      exact h_compat _ (h_cyc.edges_exist j)
  -- CycleFeasibleAt → monodromy diagonal entry
  exact feasible_implies_monodromy cycle h_cyc.length_ge i (s base) h_feasible

/-! ## Section 3: Products of Generators (Generator Sufficiency) -/

/-- **Generator Sufficiency**: any product of holonomy generators also has
    the common fixed point g as a fixed point.

    This means ∩Fix(Hol(base)) = ∩Fix(generators) — the full holonomy monoid
    doesn't add any information beyond the generators. Computing ∩Fix is
    therefore polynomial: just intersect the diagonal entries of each generator.

    Combined with sat_common_fixed_point:
    - SAT → ∩Fix(generators) ≠ ∅    (necessary condition, computable in P)
    - ∩Fix(generators) ≠ ∅ ↛ SAT    (not sufficient — gap is NP-hardness) -/
theorem holonomy_product_fixed_point (G : CubeGraph) (h_sat : G.Satisfiable)
    (base : Fin G.cubes.length)
    (ms : List (BoolMat 8))
    (hms : ∀ M ∈ ms, IsHolonomyGenerator G base M) :
    ∃ g : Vertex,
      (G.cubes[base]).isGap g = true ∧
      (ms.foldl BoolMat.mul BoolMat.one) g g = true := by
  obtain ⟨g, hg_gap, hg_fix⟩ := sat_common_fixed_point G h_sat base
  exact ⟨g, hg_gap, fixedPoint_foldl ms g (fun M hM => hg_fix M (hms M hM))⟩

/-! ## Section 4: Backward Direction is FALSE

  The converse of sat_common_fixed_point does NOT hold:
  ∃ g common fixed point of all holonomy generators ↛ SAT.

  Counterexample: bwGraph (Witness.lean §16-17) is an acyclic path
  with no blocked edges but UNSAT. Since it has no cycles, the
  holonomy monoid is trivially {I}, so ∩Fix = Fin 8 ≠ ∅, yet
  the graph is UNSAT due to arc-inconsistency (H¹·⁵ level).

  Even on graphs WITH cycles, the backward direction fails at n ≥ 12
  (see DISCOVERY-CHAIN §2, results/ncrit_conditioned_ac3.md).

  The gap between "∩Fix ≠ ∅" (computable in P) and "SAT" (NP-complete)
  is precisely where NP-hardness lives in the CubeGraph framework.

  See: formal/CubeGraph/Witness.lean (bw_h15_witness)
  See: experiments-ml/008_.../DISCOVERY-CHAIN-2026-03-04.md §2
-/

end CubeGraph
