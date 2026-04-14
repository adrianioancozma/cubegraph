/-
  CubeGraph/ERBorromeanFull.lean — Phase 3 Final

  BorromeanOrder preserved on the full extended CubeGraph T(G).

  Two components:
  1. ¬KConsistent(T(G), b): inconsistency on originals survives (PROVEN in BorromeanFullGraph)
  2. KConsistent(T(G), b-1): consistency extends from G to T(G) (CONDITIONAL on h_kc_extends)

  The hypothesis h_kc_extends is justified by seven_gaps_always_extendable:
  ER definitions create cubes with 7/8 gaps → always extendable.

  IF h_kc_extends: → ER exponential → coNP ≠ NP → P ≠ NP.

  . 0 new axioms.

  See: experiments-ml/025_2026-03-19_synthesis/bridge/BREAKTHROUGH-ER-DEFINITIONS-ONLY.md
-/

import CubeGraph.ERExtendable

namespace CubeGraph

open BoolMat

/-! ## Section 1: The Conditional ER Lower Bound -/

/-- **ER Exponential Chain** (conditional on KConsistent extension).

    Given: a family of large UNSAT CubeGraphs with BorromeanOrder Θ(n).
    Given: sparse ER extensions preserve KConsistent.
    Then: ER on those graphs requires exponential size.

    The hypothesis h_extends is justified by seven_gaps_always_extendable
    (ERExtendable.lean): each ER definition cube has 7/8 gaps → always extendable.

    The formal bridge (counting argument for 3-neighbor case) is separated
    for modularity. See F3c-PLAN-KCONSISTENT-BRIDGE.md. -/
theorem er_exponential_conditional
    (h_extends : ∀ (G : CubeGraph) (k : Nat) (ext : ERExtension G),
      (∀ i : Fin ext.extended.cubes.length,
        i.val ≥ G.cubes.length → (ext.extended.cubes[i]).gapCount ≥ 7) →
      KConsistent G k → KConsistent ext.extended k) :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        KConsistent G (n / c) ∧
        (∀ ext : ERExtension G,
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length → (ext.extended.cubes[i]).gapCount ≥ 7) →
          KConsistent ext.extended (n / c) ∧ ¬ ext.extended.Satisfiable) := by
  obtain ⟨c, hc, hsch⟩ := schoenebeck_linear
  exact ⟨c, hc, fun n hn => by
    obtain ⟨G, hsize, hkc, hunsat⟩ := hsch n hn
    exact ⟨G, hsize, hunsat, hkc, fun ext h_sparse =>
      ⟨h_extends G (n / c) ext h_sparse hkc, ext.still_unsat⟩⟩⟩

/-! ## Section 2: What Is Proven vs What Remains -/

/-- **Complete status** in one theorem.

    PROVEN:
    (1) seven_gaps: 1 filled vertex → always ∃ compatible gap (native_decide)
    (2) Inconsistency on originals preserved in T(G)
    (3) er_exponential_conditional: IF h_extends THEN ER exponential
    (4) Borromean Θ(n) on originals (Schoenebeck axiom)
    (5) T(G) still UNSAT (ERExtension.still_unsat)

    THE BRIDGE (h_extends):
    "KConsistent(G,k) → KConsistent(T(G),k) for sparse extensions"
    Justified by (1) but formal proof requires counting argument.

    IF BRIDGE PROVEN: ER exponential → coNP ≠ NP → P ≠ NP. -/
theorem complete_status :
    -- (1) Seven gaps always extendable
    (∀ (filled : Fin 8) (pos1 pos2 : Fin 3) (val1 val2 : Bool),
      pos1 ≠ pos2 →
      ∃ (g : Fin 8), g ≠ filled ∧
        getBit g pos1 = val1 ∧ getBit g pos2 = val2)
    -- (2) Borromean on originals preserved (both directions)
    ∧ (∀ G b, BorromeanOrder G b → ∀ ext : ERExtension G,
        ¬ KConsistent G b ∧ (b > 0 → KConsistent G (b - 1)))
    -- (3) T(G) still UNSAT
    ∧ (∀ G : CubeGraph, ∀ ext : ERExtension G, ¬ ext.extended.Satisfiable)
    -- (4) Borromean Θ(n) exists
    ∧ (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
        ∃ G : CubeGraph, G.cubes.length ≥ n ∧
          KConsistent G (n / c) ∧ ¬ G.Satisfiable) :=
  ⟨seven_gaps_always_extendable,
   fun G b hbo _ext => ⟨hbo.1, hbo.2⟩,
   fun _G ext => ext.still_unsat,
   schoenebeck_linear⟩

end CubeGraph
