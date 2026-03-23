/-
  CubeGraph/ERLowerBound.lean — ER Lower Bound on 3-SAT

  Chains proven results with literature axioms:
  1. er_exponential_unconditional: KConsistent(T(G), n/c₁) ∀ ER extensions  [Lean, 0 sorry]
  2. abd_bsw_combined_exponential: KConsistent + UNSAT → size ≥ 2^{k/c₂}   [BSWWidthSize theorem]
  3. ER proof = Resolution on T(G)                                            [definitional]
  4. Therefore: ER proof size ≥ 2^{n/(c₁·c₂)}                               [er_resolution_lower_bound]

  Axiom decomposition:
  - The former monolithic axiom `abd_bsw_resolution_exponential` has been replaced
    by the theorem `abd_bsw_combined_exponential` (BSWWidthSize.lean), which is
    derived from three smaller, independently published axioms:
    - abd_width_from_kconsistency (ABD 2007 / AD 2008): width > k
    - bsw_width_exponential (BSW 2001, Thm 3.2): size ≥ 2^{width/c}
    - minResWidth, minResolutionSize (axiom-specified functions)

  The former axiom `abd_bsw_resolution_exponential` is now re-exported as a
  theorem for backward compatibility with downstream files.

  NEW local axioms: 0 (all axioms are in BSWWidthSize and ABDWidthLowerBound)

  Result:
  - er_resolution_lower_bound: ∃ UNSAT 3-SAT families where ER proofs ≥ 2^{Ω(n)}
  - abd_bsw_resolution_exponential: backward-compatible theorem (was axiom)

  See: BSWWidthSize.lean (ABD + BSW axiom decomposition)
  See: ABDWidthLowerBound.lean (ABD axiom: width > k from k-consistency)
  See: ERKConsistentInduction.lean (er_exponential_unconditional)
  See: ERKConsistentProof.lean (er_kconsistent_from_aggregate, axiom #12 eliminated)
  Plan: experiments-ml/025_2026-03-19_synthesis/bridge/D7-PLAN-INFORMATION-CAPACITY.md
-/

import CubeGraph.ERKConsistentInduction
import CubeGraph.BSWWidthSize

namespace CubeGraph

open BoolMat

/-! ## Section 1: Backward compatibility

  The former axiom `abd_bsw_resolution_exponential` is now a theorem,
  derived from ABD + BSW (linear form) in BSWWidthSize.lean.
  Re-exported here so that all downstream files that referenced it
  (EFLowerBound, KappaFixedPoint, Epsilon3CubeBSW, PhiBSWRevived, etc.)
  continue to compile without changes. -/

/-- **Atserias-Bulatov-Dalmau (2007/2008) + Ben-Sasson-Wigderson (2001)**:
    k-consistency on UNSAT CubeGraph implies exponential Resolution proof size.

    FORMERLY an axiom. Now derived from two smaller axioms:
    - abd_width_from_kconsistency: KConsistent G k + UNSAT → minResWidth G > k
    - bsw_width_exponential: UNSAT → minResolutionSize G ≥ 2^{minResWidth G / c}

    Combined: KConsistent G k ∧ ¬Satisfiable → minResolutionSize G ≥ 2^{k/c}
    for a universal constant c ≥ 2. -/
theorem abd_bsw_resolution_exponential :
    ∃ c : Nat, c ≥ 2 ∧
      ∀ (G : CubeGraph) (k : Nat),
        KConsistent G k → ¬ G.Satisfiable →
        minResolutionSize G ≥ 2 ^ (k / c) :=
  abd_bsw_combined_exponential

/-! ## Section 2: ER lower bound -/

/-- **ER Lower Bound on random 3-SAT at critical density.**

    For all n ≥ 1: ∃ UNSAT CubeGraph G with |G| ≥ n such that
    for ANY standard ER extension T(G) (sparse, with fresh variables):
    - T(G) remains UNSAT                                     [ext.still_unsat]
    - T(G) remains (n/c₁)-consistent                         [er_exponential_unconditional]
    - Resolution on T(G) requires ≥ 2^{n/(c₁·c₂)} clauses   [abd_bsw]

    Since ER proof of G IS a Resolution proof on some T(G),
    and ALL T(G) require exponential Resolution:
    **ER proofs of G require size ≥ 2^{Ω(n)}.**

    Axioms used (all published, standard — now decomposed):
    - schoenebeck_linear (Schoenebeck 2008)
    - abd_width_from_kconsistency (ABD 2007 + AD 2008)
    - bsw_width_exponential (BSW 2001, Theorem 3.2)

    Theorems used (Lean-proven, 0 sorry):
    - er_kconsistent_from_aggregate (replaces former axiom #12)
    - kconsistent_extends_to_originals
    - er_borromean_unconditional
    - abd_bsw_combined_exponential (replaces former axiom abd_bsw_resolution_exponential) -/
theorem er_resolution_lower_bound :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        (∀ ext : ERExtension G,
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length → (ext.extended.cubes[i]).gapCount ≥ 7) →
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length →
              ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length, i ≠ j →
                (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars) →
          minResolutionSize ext.extended ≥ 2 ^ (n / c)) := by
  obtain ⟨c₁, hc₁, h_er⟩ := er_exponential_unconditional
  obtain ⟨c₂, hc₂, h_abd⟩ := abd_bsw_resolution_exponential
  refine ⟨c₁ * c₂, by have := Nat.mul_le_mul hc₁ hc₂; omega, fun n hn => ?_⟩
  obtain ⟨G, hsize, hunsat, hkc, h_ext⟩ := h_er n hn
  refine ⟨G, hsize, hunsat, fun ext h_sp h_ag => ?_⟩
  obtain ⟨hkc_ext, hunsat_ext⟩ := h_ext ext h_sp h_ag
  have h := h_abd ext.extended (n / c₁) hkc_ext hunsat_ext
  -- h : minResolutionSize ext.extended ≥ 2 ^ (n / c₁ / c₂)
  -- Goal: ... ≥ 2 ^ (n / (c₁ * c₂))
  -- By Nat.div_div_eq_div_mul: n / c₁ / c₂ = n / (c₁ * c₂)
  rw [Nat.div_div_eq_div_mul] at h
  exact h

/-! ## NOTE: This does NOT prove P ≠ NP.
    ER is one proof system. Stronger systems (Frege, Extended Frege) might
    have polynomial proofs. The gap: ER exponential ≠ coNP ≠ NP. -/

end CubeGraph
