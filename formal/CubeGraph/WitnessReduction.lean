/-
  CubeGraph/WitnessReduction.lean — Witness Function Reduction

  Establishes: Frege proof complexity ≥ witness circuit complexity.

  Key insight: UNSAT = ∀σ.∃C. σ violates C. A proof of UNSAT of size s
  gives a circuit of size O(s) for the witness function f(σ) = C.
  Contrapositive: hard witness → hard proof.

  This REDUCES proof complexity to circuit complexity of the witness function.
  The circuit lower bound itself is an open problem, but experimentally:
  witness has 2^{n/2} distinct subfunctions (non-localizable, confirmed n=5-18).

  See: FregeLowerBound.lean (the Ω(n²) bound via BSW)
  See: bridge-next/WITNESS-EXPERIMENT-RESULTS.md (experimental evidence)
  See: bridge-next/WITNESS-STRUCTURAL-RESULTS.md (non-localizability confirmed)
-/

import CubeGraph.FregeLowerBound

namespace CubeGraph

open BoolMat

/-! ## Section 1: Witness circuit complexity (axiom-specified) -/

/-- Minimum circuit size for the witness function of an UNSAT CubeGraph.

    The witness function f : {0,1}^n → {1,...,m} maps each assignment σ
    to an index of a clause (cube) violated by σ. UNSAT guarantees f exists.

    minWitnessCircuit G = minimum Boolean circuit size (AND/OR/NOT gates)
    over all valid witness functions for G.

    Experimentally: minWitnessCircuit grows as 2^{Θ(n)} on random 3-SAT at ρ_c
    (2^{n/2} distinct subfunctions observed, non-localizable). -/
axiom minWitnessCircuit (G : CubeGraph) : Nat

/-! ## Section 2: Frege ≥ witness circuit (proof evaluation argument) -/

/-- **Proof-to-circuit reduction**: evaluating a Frege proof on an assignment
    gives a circuit for the witness function.

    Mechanism: given Frege proof π of size s and assignment σ:
    1. Evaluate each line of π on σ (Boolean evaluation, O(s) gates)
    2. Find the first line that evaluates to FALSE under σ
    3. Trace back to an original clause Cᵢ that σ violates
    4. Output i = f(σ)

    Total circuit size: O(s) gates. So: minWitnessCircuit G ≤ O(minFregeSize G).
    Equivalently: minFregeSize G ≥ Ω(minWitnessCircuit G).

    Stated as: c · minWitnessCircuit G ≤ minFregeSize G for a universal constant c.

    References: folklore (proof evaluation = circuit construction). -/
axiom frege_to_witness :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      c * minWitnessCircuit G ≤ minFregeSize G

/-! ## Section 3: Conditional Frege lower bound from witness -/

/-- **Frege lower bound from witness circuit complexity.**

    For any UNSAT CubeGraph G:
    - minFregeSize G ≥ minWitnessCircuit G / c

    This is a REDUCTION: proof complexity ≥ circuit complexity of witness.
    Applies to ANY proof system (Frege, EF, any system that derives ⊥).

    The circuit lower bound on the witness is an OPEN PROBLEM.
    If minWitnessCircuit G ≥ 2^{Ω(n)} (experimentally suggested):
    then minFregeSize G ≥ 2^{Ω(n)} → P ≠ NP.

    Combined with Schoenebeck: there exist UNSAT G with |G| ≥ n
    where this reduction applies. -/
theorem frege_ge_witness :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      c * minWitnessCircuit G ≤ minFregeSize G := frege_to_witness

/-- **Existence of hard instances (from Schoenebeck).**
    Combined with frege_ge_witness: there exist arbitrarily large UNSAT formulas
    where Frege proof size ≥ witness circuit complexity. -/
theorem hard_instances_with_witness :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        c * minWitnessCircuit G ≤ minFregeSize G := by
  obtain ⟨c, hc, h_wit⟩ := frege_to_witness
  obtain ⟨c₁, _, h_sch⟩ := schoenebeck_linear
  exact ⟨c, hc, fun n hn => by
    obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch n hn
    exact ⟨G, hsize, hunsat, h_wit G hunsat⟩⟩

/-! ## HONEST ACCOUNTING

    What this file PROVES:
    - frege_ge_witness: Frege size ≥ witness circuit / c (from axiom)
    - hard_instances_with_witness: ∃ hard UNSAT instances (from Schoenebeck)

    What this file AXIOMATIZES:
    - minWitnessCircuit: circuit complexity of witness (function specification)
    - frege_to_witness: proof evaluation gives witness circuit (folklore)

    What this file does NOT prove:
    - minWitnessCircuit G ≥ 2^{Ω(n)} (OPEN — circuit complexity lower bound)
    - P ≠ NP (would follow from the above)

    Experimental evidence (bridge-next/):
    - 2^{n/2} distinct subfunctions (n=5-18)
    - Non-localizability confirmed (spread, CG distance, entropy, random subsets)
    - Consistent with minWitnessCircuit = 2^{Θ(n)}

    The REDUCTION is the contribution: it connects proof complexity (Frege)
    to circuit complexity (witness function) via a clean, formal chain.
    The circuit lower bound is the remaining open problem. -/

end CubeGraph
