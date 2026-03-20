/-
  CubeGraph/PCLowerBound.lean — Polynomial Calculus Lower Bound

  Chains:
  1. schoenebeck_linear: KConsistent G (n/c₁) on UNSAT G        [axiom]
  2. kconsistent_implies_pc_high_degree: KConsistent + UNSAT → PC degree > k
     [Schoenebeck 2008 (SOS) + PC ≤ SOS (GHP 2002)]
  3. pc_degree_implies_size: PC degree d → size ≥ 2^{d/c₂}
     [Impagliazzo-Pudlák-Sgall 1999]
  4. pc_lower_bound: PC size ≥ 2^{Ω(n)}                         [theorem]
  5. pc_er_lower_bound: PC + ER size ≥ 2^{Ω(n)}                 [theorem]

  New axioms (4):
  - minPCDegree, minPCSize: axiom-specified functions
  - kconsistent_implies_pc_high_degree: Schoenebeck + GHP
  - pc_degree_implies_size: IPS 1999

  See: ERLowerBound.lean (Resolution/ER lower bound, same pattern)
  See: ERKConsistentInduction.lean (er_exponential_unconditional)
  See: SchoenebeckChain.lean (schoenebeck_linear axiom)
  Plan: experiments-ml/025_2026-03-19_synthesis/bridge/D7b-PLAN-PC-EXPONENTIAL.md
-/

import CubeGraph.ERKConsistentInduction

namespace CubeGraph

open BoolMat

/-! ## Section 1: Axiom-specified PC proof complexity -/

/-- Minimum Polynomial Calculus degree for refuting a CubeGraph.
    The minimum degree of any PC refutation (over any field) of the
    CNF formula associated with G. Axiom-specified. -/
axiom minPCDegree (G : CubeGraph) : Nat

/-- Minimum Polynomial Calculus proof size for a CubeGraph.
    The minimum number of monomials in any PC refutation.
    Axiom-specified. -/
axiom minPCSize (G : CubeGraph) : Nat

/-! ## Section 2: KConsistent → PC degree (Schoenebeck + PC ≤ SOS) -/

/-- **Schoenebeck (2008) + PC ≤ SOS**: k-consistency on UNSAT CubeGraph
    implies Polynomial Calculus requires degree > k.

    Chain:
    1. KConsistent G k = SA level k passes = SOS level k passes
       [Schoenebeck 2008 proves SOS, which is ≥ SA ≥ k-consistency]
    2. PC degree d ≤ SOS level d
       [Grigoriev-Hirsch-Pasechnik, STACS 2002; Laurent, Math. Oper. Res. 2003]
    3. Contrapositive: SOS level k passes → PC has no degree-k refutation

    Alternative direct reference:
    - Grigoriev, "Linear lower bound on degrees of Positivstellensatz calculus
      refutations for the parity." Math. Notes 2001.
    - Ben-Sasson, Impagliazzo, "Random CNFs require high degree PC refutations."
      Computational Complexity 2010 (conf. version 1999). -/
axiom kconsistent_implies_pc_high_degree :
    ∀ (G : CubeGraph) (k : Nat),
      KConsistent G k → ¬ G.Satisfiable → minPCDegree G > k

/-! ## Section 3: PC degree → PC size (IPS 1999) -/

/-- **Impagliazzo-Pudlák-Sgall (1999)**: PC degree d implies exponential size.

    A PC refutation of degree d over n Boolean variables requires
    at least (n choose d) proof lines. For d = Ω(n): size ≥ 2^{Ω(n)}.

    Reference: Impagliazzo, Pudlák, Sgall. "Lower bounds for polynomial
    calculus and the Gröbner basis algorithm."
    Computational Complexity 8(2), 1999. -/
axiom pc_degree_implies_size :
    ∃ c : Nat, c ≥ 2 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable → minPCSize G ≥ 2 ^ (minPCDegree G / c)

/-! ## Section 4: PC lower bound -/

/-- **PC Lower Bound on random 3-SAT at critical density.**
    Polynomial Calculus proofs (over any field) require size ≥ 2^{Ω(n)}.

    Chain: Schoenebeck → KConsistent G (n/c₁) → PC degree > n/c₁
           → PC size ≥ 2^{n/(c₁·c₂)}.

    Eliminates Polynomial Calculus as a proof system for random 3-SAT. -/
theorem pc_lower_bound :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minPCSize G ≥ 2 ^ (n / c) := by
  obtain ⟨c₁, hc₁, h_sch⟩ := schoenebeck_linear
  obtain ⟨c₂, hc₂, h_size⟩ := pc_degree_implies_size
  refine ⟨c₁ * c₂, by have := Nat.mul_le_mul hc₁ hc₂; omega, fun n hn => ?_⟩
  obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch n hn
  refine ⟨G, hsize, hunsat, ?_⟩
  have h_deg := kconsistent_implies_pc_high_degree G (n / c₁) hkc hunsat
  have h_sz := h_size G hunsat
  -- h_deg : minPCDegree G > n / c₁
  -- h_sz  : minPCSize G ≥ 2 ^ (minPCDegree G / c₂)
  -- Goal  : minPCSize G ≥ 2 ^ (n / (c₁ * c₂))
  have h1 : minPCDegree G / c₂ ≥ n / c₁ / c₂ :=
    Nat.div_le_div_right (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h_deg))
  rw [Nat.div_div_eq_div_mul] at h1
  exact Nat.le_trans (Nat.pow_le_pow_right (by omega) h1) h_sz

/-! ## Section 5: PC + ER lower bound -/

/-- **PC + ER Lower Bound**: Polynomial Calculus on ER-extended formulas
    still requires size ≥ 2^{Ω(n)}.

    Since ER preserves KConsistent (er_kconsistent_from_aggregate),
    the PC lower bound transfers to the extended formula.
    Any PC proof on T(G) (= PC+ER proof of G) needs exponential size. -/
theorem pc_er_lower_bound :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        (∀ ext : ERExtension G,
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length → (ext.extended.cubes[i]).gapCount ≥ 7) →
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length →
              ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length, i ≠ j →
                (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars) →
          minPCSize ext.extended ≥ 2 ^ (n / c)) := by
  obtain ⟨c₁, hc₁, h_er⟩ := er_exponential_unconditional
  obtain ⟨c₂, hc₂, h_size⟩ := pc_degree_implies_size
  refine ⟨c₁ * c₂, by have := Nat.mul_le_mul hc₁ hc₂; omega, fun n hn => ?_⟩
  obtain ⟨G, hsize, hunsat, hkc, h_ext⟩ := h_er n hn
  refine ⟨G, hsize, hunsat, fun ext h_sp h_ag => ?_⟩
  obtain ⟨hkc_ext, hunsat_ext⟩ := h_ext ext h_sp h_ag
  have h_deg := kconsistent_implies_pc_high_degree ext.extended (n / c₁) hkc_ext hunsat_ext
  have h_sz := h_size ext.extended hunsat_ext
  have h1 : minPCDegree ext.extended / c₂ ≥ n / c₁ / c₂ :=
    Nat.div_le_div_right (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h_deg))
  rw [Nat.div_div_eq_div_mul] at h1
  exact Nat.le_trans (Nat.pow_le_pow_right (by omega) h1) h_sz

/-! ## NOTE: This eliminates Polynomial Calculus (over any field) and
    PC + Extended Resolution as proof systems for random 3-SAT at ρ_c.
    Combined with ERLowerBound.lean: Resolution, ER, PC, and PC+ER
    all require exponential proofs. -/

end CubeGraph
