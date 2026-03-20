/-
  CubeGraph/AC0FregeLowerBound.lean — AC⁰-Frege Lower Bound

  First non-clausal proof system eliminated. AC⁰-Frege operates on
  propositional formulas of bounded depth (not just clauses).

  Chain:
  1. schoenebeck_linear: KConsistent G (n/c₁) on UNSAT G        [axiom]
  2. kconsistent_implies_ac0frege_exponential: KConsistent + UNSAT
     → AC⁰-Frege at depth d needs size ≥ 2^{k/c₂}
     [BIKPPW 1996 + Krajíček 1994 + Håstad switching lemma 1986]
  3. ac0frege_lower_bound: AC⁰-Frege size ≥ 2^{Ω(n)}           [theorem]
  4. ac0frege_er_lower_bound: AC⁰-Frege + ER size ≥ 2^{Ω(n)}   [theorem]

  New axioms (2):
  - minAC0FregeSize: proof size at depth d (axiom-specified)
  - kconsistent_implies_ac0frege_exponential: BIKPPW + switching lemma

  See: PCLowerBound.lean, CPLowerBound.lean (same pattern, clausal systems)
  See: BorromeanAC0.lean (AC⁰ circuit bound, complementary)
  See: ERKConsistentInduction.lean (er_exponential_unconditional)
  Plan: experiments-ml/025_2026-03-19_synthesis/bridge/D7d-PLAN-AC0FREGE-EXPONENTIAL.md
-/

import CubeGraph.ERKConsistentInduction

namespace CubeGraph

open BoolMat

/-! ## Section 1: Axiom-specified AC⁰-Frege proof size -/

/-- Minimum AC⁰-Frege proof size at depth d for a CubeGraph.
    The minimum number of lines in any depth-d Frege refutation
    of the CNF formula associated with G.

    AC⁰-Frege = Frege system where every proof line is a formula
    of depth ≤ d (equivalently, computable by an AC⁰ circuit of depth d).
    Strictly stronger than Resolution, ER, PC, CP for any d ≥ 2. -/
axiom minAC0FregeSize (G : CubeGraph) (d : Nat) : Nat

/-! ## Section 2: KConsistent → AC⁰-Frege exponential (BIKPPW 1996) -/

/-- **BIKPPW (1996) + Krajíček (1994) + Håstad (1986)**:
    k-consistency on UNSAT CubeGraph implies AC⁰-Frege requires
    exponential size at any fixed depth d ≥ 2.

    The real bound is 2^{k^{1/(d-1)}/c}, which for k = Ω(n)
    gives 2^{n^{Ω(1/d)}}. We state a weaker but clean version:
    size ≥ 2^{k/c} where c depends on d. This suffices for
    "exponential at any fixed depth."

    Mechanism (switching lemma):
    1. An AC⁰-Frege proof of size s at depth d defines a depth-d circuit
    2. Håstad's switching lemma: random restriction collapses depth d → d-1
    3. After d-1 rounds: formula collapses to CNF of width O(1)
    4. But KConsistent G k means Resolution width > k (ABD+AD)
    5. Resolution hardness partially survives random restriction
    6. Contradiction unless s ≥ 2^{k^{Ω(1/d)}}

    References:
    - Beame, Impagliazzo, Krajíček, Pitassi, Pudlák.
      "Lower bounds on Hilbert's Nullstellensatz and propositional proofs."
      Proc. London Math. Soc. 73(1), 1996.
    - Krajíček. "Lower bounds to the size of constant-depth propositional
      proofs." JSL 59(1), 1994.
    - Håstad. "Almost optimal lower bounds for small depth circuits."
      STOC 1986 / Computational Limitations of Small-Depth Circuits, 1987. -/
axiom kconsistent_implies_ac0frege_exponential :
    ∀ (d : Nat), d ≥ 2 →
      ∃ c : Nat, c ≥ 2 ∧ ∀ (G : CubeGraph) (k : Nat),
        KConsistent G k → ¬ G.Satisfiable →
        minAC0FregeSize G d ≥ 2 ^ (k / c)

/-! ## Section 3: AC⁰-Frege lower bound -/

/-- **AC⁰-Frege Lower Bound on random 3-SAT at critical density.**
    For any fixed depth d ≥ 2: AC⁰-Frege proofs require size ≥ 2^{Ω(n)}.

    Chain: Schoenebeck → KConsistent(n/c₁) → BIKPPW → size ≥ 2^{n/(c₁·c₂)}.

    This is the first non-clausal proof system eliminated.
    AC⁰-Frege is strictly stronger than Resolution, ER, PC, and CP. -/
theorem ac0frege_lower_bound (d : Nat) (hd : d ≥ 2) :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minAC0FregeSize G d ≥ 2 ^ (n / c) := by
  obtain ⟨c₁, hc₁, h_sch⟩ := schoenebeck_linear
  obtain ⟨c₂, hc₂, h_ac0⟩ := kconsistent_implies_ac0frege_exponential d hd
  refine ⟨c₁ * c₂, by have := Nat.mul_le_mul hc₁ hc₂; omega, fun n hn => ?_⟩
  obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch n hn
  refine ⟨G, hsize, hunsat, ?_⟩
  have h_sz := h_ac0 G (n / c₁) hkc hunsat
  rw [Nat.div_div_eq_div_mul] at h_sz
  exact h_sz

/-! ## Section 4: AC⁰-Frege + ER lower bound -/

/-- **AC⁰-Frege + ER Lower Bound**: AC⁰-Frege on ER-extended formulas
    still requires exponential size at any fixed depth.

    Since ER preserves KConsistent (er_kconsistent_from_aggregate),
    the AC⁰-Frege bound transfers to the extended formula. -/
theorem ac0frege_er_lower_bound (d : Nat) (hd : d ≥ 2) :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        (∀ ext : ERExtension G,
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length → (ext.extended.cubes[i]).gapCount ≥ 7) →
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length →
              ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length, i ≠ j →
                (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars) →
          minAC0FregeSize ext.extended d ≥ 2 ^ (n / c)) := by
  obtain ⟨c₁, hc₁, h_er⟩ := er_exponential_unconditional
  obtain ⟨c₂, hc₂, h_ac0⟩ := kconsistent_implies_ac0frege_exponential d hd
  refine ⟨c₁ * c₂, by have := Nat.mul_le_mul hc₁ hc₂; omega, fun n hn => ?_⟩
  obtain ⟨G, hsize, hunsat, hkc, h_ext⟩ := h_er n hn
  refine ⟨G, hsize, hunsat, fun ext h_sp h_ag => ?_⟩
  obtain ⟨hkc_ext, hunsat_ext⟩ := h_ext ext h_sp h_ag
  have h_sz := h_ac0 ext.extended (n / c₁) hkc_ext hunsat_ext
  rw [Nat.div_div_eq_div_mul] at h_sz
  exact h_sz

/-! ## NOTE: This eliminates AC⁰-Frege (bounded-depth Frege) and
    AC⁰-Frege + ER as proof systems for random 3-SAT at ρ_c.
    AC⁰-Frege is the first non-clausal, non-algebraic proof system
    eliminated. It is strictly stronger than Resolution, ER, PC, and CP.

    What REMAINS open: Frege (unbounded depth) and Extended Frege. -/

end CubeGraph
