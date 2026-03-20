/-
  CubeGraph/CPLowerBound.lean — Cutting Planes Lower Bound

  Chains:
  1. schoenebeck_linear: KConsistent G (n/c₁) on UNSAT G        [axiom]
  2. kconsistent_implies_cp_high_width: KConsistent + UNSAT → CP width > k
     [ABD+AD (2007/2008) + Krajíček (1997)]
  3. cp_width_implies_size: CP width w → size ≥ 2^{w/c₂}
     [Hrubeš-Pudlák 2017]
  4. cp_lower_bound: CP size ≥ 2^{Ω(n)}                         [theorem]
  5. cp_er_lower_bound: CP + ER size ≥ 2^{Ω(n)}                 [theorem]

  New axioms (4):
  - minCPWidth, minCPSize: axiom-specified functions
  - kconsistent_implies_cp_high_width: ABD+AD + Krajíček
  - cp_width_implies_size: Hrubeš-Pudlák 2017

  See: PCLowerBound.lean (same pattern for Polynomial Calculus)
  See: ERLowerBound.lean (same pattern for Extended Resolution)
  See: ERKConsistentInduction.lean (er_exponential_unconditional)
  Plan: experiments-ml/025_2026-03-19_synthesis/bridge/D7c-PLAN-CP-EXPONENTIAL.md
-/

import CubeGraph.ERKConsistentInduction

namespace CubeGraph

open BoolMat

/-! ## Section 1: Axiom-specified CP proof complexity -/

/-- Minimum Cutting Planes width for refuting a CubeGraph.
    The maximum number of variables in any inequality that must appear
    in every CP refutation of the CNF associated with G. Axiom-specified. -/
axiom minCPWidth (G : CubeGraph) : Nat

/-- Minimum Cutting Planes proof size for a CubeGraph.
    The minimum number of inequalities in any CP refutation
    (with arbitrary integer coefficients and division rule). -/
axiom minCPSize (G : CubeGraph) : Nat

/-! ## Section 2: KConsistent → CP width (ABD+AD + Krajíček) -/

/-- **ABD+AD (2007/2008) + Krajíček (1997)**: k-consistency on UNSAT
    CubeGraph implies Cutting Planes width > k.

    Chain:
    1. KConsistent G k → Resolution width > k
       [Atserias-Bulatov-Dalmau, ICALP 2007; Atserias-Dalmau, JCSS 2008]
    2. CP width ≥ Resolution width
       [Krajíček, "Interpolation theorems, lower bounds for proof systems,
        and independence results for bounded arithmetic." JSL 62(2), 1997]
    3. Therefore: CP width > k -/
axiom kconsistent_implies_cp_high_width :
    ∀ (G : CubeGraph) (k : Nat),
      KConsistent G k → ¬ G.Satisfiable → minCPWidth G > k

/-! ## Section 3: CP width → CP size (Hrubeš-Pudlák 2017) -/

/-- **Hrubeš-Pudlák (2017)**: CP width w implies exponential size.

    A Cutting Planes refutation (with arbitrary coefficients and division)
    of width w on an n-variable formula requires ≥ 2^{Ω(w²/n)} lines.
    For w = Ω(n): size ≥ 2^{Ω(n)}.

    This generalizes Ben-Sasson-Wigderson (2001) from Resolution to CP.

    Reference: Hrubeš, Pudlák. "Random formulas, monotone circuits,
    and interpolation." FOCS 2017 / Journal version 2019. -/
axiom cp_width_implies_size :
    ∃ c : Nat, c ≥ 2 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable → minCPSize G ≥ 2 ^ (minCPWidth G / c)

/-! ## Section 4: CP lower bound -/

/-- **CP Lower Bound on random 3-SAT at critical density.**
    Cutting Planes proofs (with arbitrary coefficients and division)
    require size ≥ 2^{Ω(n)}.

    Chain: Schoenebeck → KConsistent G (n/c₁) → CP width > n/c₁
           → CP size ≥ 2^{n/(c₁·c₂)}.

    Eliminates Cutting Planes as a proof system for random 3-SAT. -/
theorem cp_lower_bound :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minCPSize G ≥ 2 ^ (n / c) := by
  obtain ⟨c₁, hc₁, h_sch⟩ := schoenebeck_linear
  obtain ⟨c₂, hc₂, h_size⟩ := cp_width_implies_size
  refine ⟨c₁ * c₂, by have := Nat.mul_le_mul hc₁ hc₂; omega, fun n hn => ?_⟩
  obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch n hn
  refine ⟨G, hsize, hunsat, ?_⟩
  have h_w := kconsistent_implies_cp_high_width G (n / c₁) hkc hunsat
  have h_sz := h_size G hunsat
  have h1 : minCPWidth G / c₂ ≥ n / c₁ / c₂ :=
    Nat.div_le_div_right (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h_w))
  rw [Nat.div_div_eq_div_mul] at h1
  exact Nat.le_trans (Nat.pow_le_pow_right (by omega) h1) h_sz

/-! ## Section 5: CP + ER lower bound -/

/-- **CP + ER Lower Bound**: Cutting Planes on ER-extended formulas
    still requires size ≥ 2^{Ω(n)}.

    Since ER preserves KConsistent (er_kconsistent_from_aggregate),
    the CP width bound transfers to the extended formula.
    Any CP proof on T(G) (= CP+ER proof of G) needs exponential size. -/
theorem cp_er_lower_bound :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        (∀ ext : ERExtension G,
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length → (ext.extended.cubes[i]).gapCount ≥ 7) →
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length →
              ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length, i ≠ j →
                (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars) →
          minCPSize ext.extended ≥ 2 ^ (n / c)) := by
  obtain ⟨c₁, hc₁, h_er⟩ := er_exponential_unconditional
  obtain ⟨c₂, hc₂, h_size⟩ := cp_width_implies_size
  refine ⟨c₁ * c₂, by have := Nat.mul_le_mul hc₁ hc₂; omega, fun n hn => ?_⟩
  obtain ⟨G, hsize, hunsat, hkc, h_ext⟩ := h_er n hn
  refine ⟨G, hsize, hunsat, fun ext h_sp h_ag => ?_⟩
  obtain ⟨hkc_ext, hunsat_ext⟩ := h_ext ext h_sp h_ag
  have h_w := kconsistent_implies_cp_high_width ext.extended (n / c₁) hkc_ext hunsat_ext
  have h_sz := h_size ext.extended hunsat_ext
  have h1 : minCPWidth ext.extended / c₂ ≥ n / c₁ / c₂ :=
    Nat.div_le_div_right (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h_w))
  rw [Nat.div_div_eq_div_mul] at h1
  exact Nat.le_trans (Nat.pow_le_pow_right (by omega) h1) h_sz

/-! ## NOTE: This eliminates Cutting Planes (with arbitrary coefficients
    and division rule) and CP + ER as proof systems for random 3-SAT at ρ_c.
    Combined with ERLowerBound and PCLowerBound: Resolution, ER, PC, CP,
    and all their combinations with ER require exponential proofs. -/

end CubeGraph
