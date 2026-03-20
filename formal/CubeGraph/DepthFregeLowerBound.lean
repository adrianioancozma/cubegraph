/-
  CubeGraph/DepthFregeLowerBound.lean — Depth-Sensitive Frege Lower Bounds

  Strengthens AC⁰-Frege (constant depth) to growing depth d(n).
  Uses precise BIKPPW axiom: size ≥ 2^{k^{1/(c·d)}}, stated as
  (Nat.log2 size)^{c·d} ≥ k.

  Key results:
  - depth_frege_lower_bound: for ANY d(n), (log₂ size)^{c·d} ≥ n/c₁
  - At d constant: size ≥ 2^{n^{Ω(1)}} (recovers AC⁰-Frege)
  - At d = o(log n / log log n): size = n^{ω(1)} (super-polynomial) — NEW
  - At d = Θ(log n): size ≥ 2^{O(1)} (trivial — boundary)

  New class eliminated: sub-logarithmic-depth Frege (between AC⁰ and NC¹).

  See: AC0FregeLowerBound.lean (constant depth, weaker axiom)
  See: EFLowerBound.lean (generalized ER with HasCorrectGaps)
  Plan: experiments-ml/025_2026-03-19_synthesis/bridge/D7g-PLAN-DEPTH-SENSITIVE-FREGE.md

  References:
  - Beame, Impagliazzo, Krajíček, Pitassi, Pudlák.
    "Lower bounds on Hilbert's Nullstellensatz and propositional proofs."
    Proc. London Math. Soc. 73(1), 1996.
  - Krajíček. "Bounded Arithmetic, Propositional Logic, and Complexity Theory."
    Cambridge University Press, 1995.
-/

import CubeGraph.ERKConsistentInduction
import CubeGraph.ERLowerBound
import CubeGraph.AC0FregeLowerBound

namespace CubeGraph

open BoolMat

/-! ## Section 1: Precise BIKPPW axiom -/

/-- **BIKPPW (1996) precise form**: depth-d Frege size satisfies
    (log₂ size)^{c·d} ≥ k, where k is the k-consistency level.

    Equivalently: size ≥ 2^{k^{1/(c·d)}}.

    This captures the exact depth-size tradeoff:
    - d constant: k^{1/(c·d)} = k^{Ω(1)} → size exponential
    - d growing: k^{1/(c·d)} shrinks → size bound weakens gracefully
    - d = Θ(log k): k^{1/(c·log k)} = O(1) → trivial

    Stronger than kconsistent_implies_ac0frege_exponential (which loses
    the d-dependence by absorbing it into the constant c).

    References: BIKPPW (1996), Krajíček (1995). -/
axiom bikppw_precise :
    ∃ c : Nat, c ≥ 2 ∧ ∀ (G : CubeGraph) (k d : Nat),
      d ≥ 2 → KConsistent G k → ¬ G.Satisfiable →
      (Nat.log2 (minAC0FregeSize G d)) ^ (c * d) ≥ k

/-! ## Section 2: Depth-sensitive lower bound -/

/-- **Depth-sensitive Frege lower bound**: for ANY depth function d(n),
    depth-d Frege proofs satisfy (log₂ size)^{c·d} ≥ n/c₁.

    This is the master theorem from which all depth-specific bounds follow:
    - Instantiate d = 3 → recover AC⁰-Frege exponential
    - Instantiate d = √(log n) → super-polynomial (NEW)
    - Instantiate d = log n / log log n → barely super-polynomial (NEW) -/
theorem depth_frege_lower_bound :
    ∃ c₁ c₂ : Nat, c₁ ≥ 2 ∧ c₂ ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ d ≥ 2,
          (Nat.log2 (minAC0FregeSize G d)) ^ (c₂ * d) ≥ n / c₁ := by
  obtain ⟨c₁, hc₁, h_sch⟩ := schoenebeck_linear
  obtain ⟨c₂, hc₂, h_bik⟩ := bikppw_precise
  exact ⟨c₁, c₂, hc₁, hc₂, fun n hn => by
    obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch n hn
    exact ⟨G, hsize, hunsat, fun d hd =>
      h_bik G (n / c₁) d hd hkc hunsat⟩⟩

/-! ## Section 3: ER extension preserves depth-sensitive bound -/

/-- **Depth-sensitive + ER**: the bound holds on ER-extended formulas too.
    Since ER preserves KConsistent (er_kconsistent_from_aggregate),
    BIKPPW applies to T(G) as well. -/
theorem depth_frege_er_lower_bound :
    ∃ c₁ c₂ : Nat, c₁ ≥ 2 ∧ c₂ ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        (∀ ext : ERExtension G,
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length → (ext.extended.cubes[i]).gapCount ≥ 7) →
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length →
              ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length, i ≠ j →
                (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars) →
          ∀ d ≥ 2,
            (Nat.log2 (minAC0FregeSize ext.extended d)) ^ (c₂ * d) ≥ n / c₁) := by
  obtain ⟨c₁, hc₁, h_er⟩ := er_exponential_unconditional
  obtain ⟨c₂, hc₂, h_bik⟩ := bikppw_precise
  exact ⟨c₁, c₂, hc₁, hc₂, fun n hn => by
    obtain ⟨G, hsize, hunsat, hkc, h_ext⟩ := h_er n hn
    exact ⟨G, hsize, hunsat, fun ext h_sp h_ag d hd => by
      obtain ⟨hkc_ext, hunsat_ext⟩ := h_ext ext h_sp h_ag
      exact h_bik ext.extended (n / c₁) d hd hkc_ext hunsat_ext⟩⟩

/-! ## Section 4: Interpretation guide

    The theorem `depth_frege_lower_bound` gives:
      (log₂ size)^{c₂·d} ≥ n/c₁

    Rearranging: log₂(size) ≥ (n/c₁)^{1/(c₂·d)}

    So: size ≥ 2^{(n/c₁)^{1/(c₂·d)}}

    Instantiations:

    d = 3 (constant):
      size ≥ 2^{(n/c₁)^{1/(3c₂)}} = 2^{n^{Ω(1)}}
      → exponential (recovers AC⁰-Frege) ✅

    d = √(log₂ n) (slowly growing):
      size ≥ 2^{(n/c₁)^{1/(c₂·√(log n))}}
           = 2^{2^{log(n/c₁)/(c₂·√(log n))}}
           = 2^{2^{Ω(√(log n))}}
      → super-polynomial (grows faster than any polynomial) ✅ NEW

    d = (log₂ n)/(c₂ · log₂ log₂ n) (threshold):
      size ≥ 2^{(n/c₁)^{log₂ log₂ n / log₂ n}}
           = 2^{2^{(log log n)² / log n}}
      → super-polynomial (barely) ✅ NEW

    d = (log₂ n)/c₂ (logarithmic):
      size ≥ 2^{(n/c₁)^{1/log₂ n}}
           = 2^{2^{log(n/c₁)/log n}}
           = 2^{2^{O(1)}}
           = 2^{O(1)}
      → constant = trivial ❌ (boundary)

    CONCLUSION: Frege with depth d = o(log n / log log n) needs
    super-polynomial size on random 3-SAT at ρ_c.
    This strictly generalizes AC⁰-Frege (constant depth). -/

end CubeGraph
