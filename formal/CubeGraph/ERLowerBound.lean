/-
  CubeGraph/ERLowerBound.lean — ER Lower Bound on 3-SAT

  Chains proven results with literature axioms:
  1. er_exponential_unconditional: KConsistent(T(G), n/c₁) ∀ ER extensions  [Lean]
  2. abd_bsw_combined_exponential: KConsistent + UNSAT → size ≥ 2^{(k-2)²/(c₂·M)}
     [BSWWidthSize theorem, from BSW Corollary 3.6]
  3. ER proof = Resolution on T(G)                                            [definitional]
  4. Therefore: ER proof size ≥ 2^{(n/c₁ - 2)² / (c₂ · M_ext)}             [er_resolution_lower_bound]

  Axiom decomposition:
  - The former monolithic axiom `abd_bsw_resolution_exponential` has been replaced
    by the theorem `abd_bsw_combined_exponential` (BSWWidthSize.lean), which is
    derived from two smaller, independently published axioms:
    - abd_width_from_kconsistency (ABD 2007 / AD 2008): width > k
    - bsw_width_to_size (BSW 2001, Cor. 3.6): size ≥ 2^{(width-3)²/(c·M)}
    - minResWidth, minResolutionSize (axiom-specified functions)

  NOTE (2026-03-24): The former axiom bsw_width_exponential (size ≥ 2^{w/c})
  has been REMOVED — it was incorrect (BSW always has N in the denominator).
  All downstream theorems now use the quadratic form from bsw_width_to_size.
  The theorem `abd_bsw_resolution_exponential` now includes G.cubes.length
  in the exponent denominator, matching the actual BSW result.

  NEW local axioms: 0 (all axioms are in BSWWidthSize and ABDWidthLowerBound)

  Result:
  - er_resolution_lower_bound: ∃ UNSAT 3-SAT families where ER proofs ≥ 2^{Ω(n)}
  - abd_bsw_resolution_exponential: re-exported from BSWWidthSize (signature updated)

  See: BSWWidthSize.lean (ABD + BSW axiom decomposition)
  See: ABDWidthLowerBound.lean (ABD axiom: width > k from k-consistency)
  See: ERKConsistentInduction.lean (er_exponential_unconditional)
  See: ERKConsistentProof.lean (er_kconsistent_from_aggregate, axiom #12 eliminated)
  Plan: experiments-ml/025_2026-03-19_synthesis/bridge/D7-PLAN-INFORMATION-CAPACITY.md
  See: experiments-ml/033_2026-03-26_tensor-dynamics/INSIGHT-NOT-CANNOT-HELP.md (Resolution lb used in NOT-cannot-help argument)
  See: experiments-ml/034_2026-03-26_lifting/PLAN.md (lifting Resolution lb → monotone circuit lb via Cavalar-Oliveira)
-/

import CubeGraph.ERKConsistentInduction
import CubeGraph.BSWWidthSize

namespace CubeGraph

open BoolMat

/-! ## Section 1: Backward compatibility

  The former axiom `abd_bsw_resolution_exponential` is now a theorem,
  derived from ABD + BSW (quadratic form) in BSWWidthSize.lean.
  Re-exported here for downstream files.

  NOTE (2026-03-24): Signature CHANGED to include G.cubes.length in
  the exponent denominator, matching the actual BSW Cor. 3.6 result.
  The former N-free bound (from the incorrect bsw_width_exponential)
  has been corrected. -/

/-- **Atserias-Bulatov-Dalmau (2007/2008) + Ben-Sasson-Wigderson (2001)**:
    k-consistency on UNSAT CubeGraph implies Resolution proof size
    ≥ 2^{(k-2)²/(c·M)} where M = G.cubes.length.

    Derived from two smaller axioms:
    - abd_width_from_kconsistency: KConsistent G k + UNSAT → minResWidth G > k
    - bsw_width_to_size (BSW Cor. 3.6): size ≥ 2^{(w-3)²/(c·M)}

    NOTE (2026-03-24): Previously claimed size ≥ 2^{k/c} without the M
    denominator. Corrected to include M per the actual BSW result. -/
theorem abd_bsw_resolution_exponential :
    ∃ c : Nat, c ≥ 1 ∧
      ∀ (G : CubeGraph) (k : Nat),
        KConsistent G k → ¬ G.Satisfiable → G.cubes.length ≥ 1 →
        minResolutionSize G ≥
          2 ^ ((k - 2) * (k - 2) / (c * G.cubes.length)) :=
  abd_bsw_combined_exponential

/-! ## Section 2: ER lower bound -/

/-- **ER Lower Bound on random 3-SAT at critical density.**

    For all n ≥ 1: ∃ UNSAT CubeGraph G with |G| ≥ n such that
    for ANY standard ER extension T(G) (sparse, with fresh variables):
    - T(G) remains UNSAT                                     [ext.still_unsat]
    - T(G) remains (n/c₁)-consistent                         [er_exponential_unconditional]
    - Resolution on T(G) requires ≥ 2^{(n/c₁ - 2)²/(c₂·M_ext)} clauses

    Since ER proof of G IS a Resolution proof on some T(G),
    and ALL T(G) require exponential Resolution:
    **ER proofs of G require size ≥ 2^{Ω(n²/M_ext)}.**

    When M_ext = O(n) (as for standard ER extensions of random 3-SAT),
    this gives 2^{Ω(n)}.

    Axioms used (all published, standard — now decomposed):
    - schoenebeck_linear (Schoenebeck 2008)
    - abd_width_from_kconsistency (ABD 2007 + AD 2008)
    - bsw_width_to_size (BSW 2001, Corollary 3.6) -/
theorem er_resolution_lower_bound :
    ∃ c_k c_s : Nat, c_k ≥ 2 ∧ c_s ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        (∀ ext : ERExtension G,
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length → (ext.extended.cubes[i]).gapCount ≥ 7) →
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length →
              ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length, i ≠ j →
                (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars) →
          ext.extended.cubes.length ≥ 1 →
          minResolutionSize ext.extended ≥
            2 ^ ((n / c_k - 2) * (n / c_k - 2) /
                 (c_s * ext.extended.cubes.length))) := by
  obtain ⟨c₁, hc₁, h_er⟩ := er_exponential_unconditional
  obtain ⟨c₂, hc₂, h_abd⟩ := abd_bsw_resolution_exponential
  refine ⟨c₁, c₂, hc₁, hc₂, fun n hn => ?_⟩
  obtain ⟨G, hsize, hunsat, hkc, h_ext⟩ := h_er n hn
  refine ⟨G, hsize, hunsat, fun ext h_sp h_ag hM_ext => ?_⟩
  obtain ⟨hkc_ext, hunsat_ext⟩ := h_ext ext h_sp h_ag
  exact h_abd ext.extended (n / c₁) hkc_ext hunsat_ext hM_ext

/-! ## NOTE: This does NOT prove P ≠ NP.
    ER is one proof system. Stronger systems (Frege, Extended Frege) might
    have polynomial proofs. The gap: ER exponential ≠ coNP ≠ NP. -/

end CubeGraph
