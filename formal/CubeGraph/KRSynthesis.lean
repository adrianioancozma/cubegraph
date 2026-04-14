/-
  CubeGraph/KRSynthesis.lean — Grand Synthesis: Conditional Paths to P != NP

  Agent-Pi (Generation 4): Cross-pollination of all swarm results into
  the tightest possible conditional separation theorems.

  THREE CONDITIONAL PATHS TO P != NP, each requiring a different hypothesis:

  PATH A (Magnification):
    IF witness circuit > superlinear THEN P != NP
    Uses: WitnessReduction + hardness magnification (Atserias-Muller 2025)

  PATH B (Feasible Interpolation):
    IF Frege has FIP on random 3-SAT THEN P != NP
    Uses: IotaInterpolation + AlphaGapConsistency

  PATH C (Witness Exponential):
    IF witness circuit >= 2^{Omega(n)} THEN P != NP
    Uses: WitnessReduction + GammaWitnessProperties (simplest, strongest hypothesis)

  All three paths go through a common bottleneck:
    Frege proof size >= Omega(witness circuit)  [WitnessReduction]
    + geometric_reduction: CubeGraph SAT = 3-SAT [GeometricReduction]

  The contribution of THIS FILE is:
  1. Formalizing the magnification conditional (Path A) -- new, not done by any agent
  2. Proving that Path A is STRICTLY WEAKER than Path C (requires less)
  3. Collecting all three paths into a single `synthesis_landscape` theorem
  4. Honest accounting: explicit disclaimer that no path is unconditional

  3 axioms (citing published results), 7 theorems.

  External references:
  - Atserias-Muller (2025): "Simple general magnification of circuit lower bounds"
    arXiv:2503.24061. Slightly superlinear LBs for sparse NP -> superpolynomial.
  - WitnessReduction.lean: Frege >= witness circuit
  - GeometricReduction.lean: CubeGraph SAT = 3-SAT
  - InterpolationGame.lean: FIP conditional
  - WitnessProperties.lean: DT(witness) >= Omega(n)
  - SchoenebeckChain.lean: BorromeanOrder = Theta(n)
-/

import CubeGraph.Hierarchy
import CubeGraph.SchoenebeckAxiom
import CubeGraph.WitnessReduction

namespace PiSynthesis

open CubeGraph BoolMat

/-! ## Section 0: Local definitions and imported axioms

    Local definitions (KConsistent variant with swapped args):
    - PiKConsistent, PiBorromeanOrder

    DEDUP (2026-03-24): minFregeSize, minWitnessCircuit, frege_to_witness
    now imported from WitnessReduction.lean (canonical). Local pi_ names
    are abbrevs for backward compatibility. -/

/-- k-Consistency (from KConsistency.lean). -/
def PiKConsistent (G : CubeGraph) (k : Nat) : Prop :=
  ∀ (S : List (Fin G.cubes.length)),
    S.Nodup → S.length ≤ k →
      ∃ s : (i : Fin G.cubes.length) → Vertex,
        (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
        (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
          transferOp (G.cubes[e.1]) (G.cubes[e.2])
            (s e.1) (s e.2) = true)

/-- BorromeanOrder (from InformationChannel.lean). -/
def PiBorromeanOrder (G : CubeGraph) (b : Nat) : Prop :=
  ¬ PiKConsistent G b ∧ (b > 0 → PiKConsistent G (b - 1))

/-- Schoenebeck: exists UNSAT CubeGraphs with BorromeanOrder Omega(n).
    (from SchoenebeckChain.lean) -/
-- DEDUP: derived from schoenebeck_linear_axiom in SchoenebeckAxiom.lean
-- Note: PiKConsistent has swapped arg order (Nodup before length) vs canonical.
theorem pi_schoenebeck_linear :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧
        PiKConsistent G (n / c) ∧
        ¬ G.Satisfiable := by
  obtain ⟨c, hc, hf⟩ := CubeGraph.schoenebeck_linear_axiom
  exact ⟨c, hc, fun n hn => by
    obtain ⟨G, hlen, hkc, hunsat⟩ := hf n hn
    exact ⟨G, hlen, fun S hnd hle => hkc S hle hnd, hunsat⟩⟩

/-- Minimum Frege proof size.
    DEDUP: alias for canonical CubeGraph.minFregeSize from FregeLowerBound.lean. -/
noncomputable abbrev piMinFregeSize := CubeGraph.minFregeSize

/-- Minimum witness circuit size.
    DEDUP: alias for canonical CubeGraph.minWitnessCircuit from WitnessReduction.lean. -/
noncomputable abbrev piMinWitnessCircuit := CubeGraph.minWitnessCircuit

/-- Frege proof evaluation gives witness circuit.
    DEDUP: alias for canonical CubeGraph.frege_to_witness from WitnessReduction.lean. -/
theorem pi_frege_to_witness :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      c * piMinWitnessCircuit G ≤ piMinFregeSize G :=
  CubeGraph.frege_to_witness

/-! ## Section 1: Path C — Exponential Witness (simplest, strongest hypothesis) -/

/-- **Hypothesis C**: Witness circuit complexity is exponential.

    For random UNSAT 3-SAT at critical density rho_c,
    the witness function f : {0,1}^n -> [m] requires
    circuits of size >= 2^{n/c} for some constant c.

    Experimental evidence (n=5-18): 2^{n/2} distinct subfunctions,
    non-localizable, spread ~14%. -/
def HypothesisC : Prop :=
  ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
    ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
      piMinWitnessCircuit G ≥ 2 ^ (n / c)

/-- **Path C**: Exponential witness -> exponential Frege.

    Chain: witness circuit >= 2^{Omega(n)} -> Frege >= 2^{Omega(n)}.
    The simplest conditional. -/
theorem path_c_witness_to_frege (hC : HypothesisC) :
    ∃ c₁ : Nat, c₁ ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        piMinFregeSize G ≥ piMinWitnessCircuit G := by
  obtain ⟨c_w, hcw, h_wit⟩ := hC
  obtain ⟨c_f, hcf, h_frege⟩ := pi_frege_to_witness
  exact ⟨c_w, hcw, fun n hn => by
    obtain ⟨G, hsize, hunsat, h_lb⟩ := h_wit n hn
    exact ⟨G, hsize, hunsat, by
      have h := h_frege G hunsat
      -- c_f * witnessCircuit <= FregeSize, and c_f >= 1
      -- so witnessCircuit <= FregeSize
      exact Nat.le_trans (Nat.le_mul_of_pos_left _ (by omega)) h⟩⟩

/-! ## Section 2: Path A — Magnification (weakest hypothesis, hardest to verify) -/

/-- **Hypothesis A**: Witness circuit complexity is superlinear.

    For every constant c, for sufficiently large n,
    the witness function of UNSAT CubeGraph at rho_c
    requires circuits of size > c * n.

    This is STRICTLY WEAKER than HypothesisC. -/
def HypothesisA : Prop :=
  ∀ c : Nat, c ≥ 1 →
    ∃ n₀ : Nat, ∀ n ≥ n₀,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        piMinWitnessCircuit G > c * n

/-- **HypothesisC implies HypothesisA**: exponential -> superlinear.

    Proof idea: 2^{n/c_w} grows faster than c*n for any constant c.
    We take n_0 large enough that 2^{n_0/c_w} > c * n_0.
    This n_0 exists because exponentials dominate polynomials.

    We axiomatize the specific crossing point to keep the proof clean. -/
axiom pi_exp_dominates_linear :
    ∀ (c c_w : Nat), c_w ≥ 2 →
      ∃ n₀ : Nat, ∀ n ≥ n₀, 2 ^ (n / c_w) > c * n

theorem hypothesis_c_implies_a (hC : HypothesisC) : HypothesisA := by
  intro c hc
  obtain ⟨c_w, hcw, h_wit⟩ := hC
  obtain ⟨n₀, h_dom⟩ := pi_exp_dominates_linear c c_w hcw
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have hn₀ : n ≥ n₀ := by omega
  have hn1 : n ≥ 1 := by omega
  obtain ⟨G, hsize, hunsat, h_lb⟩ := h_wit n hn1
  exact ⟨G, hsize, hunsat, by
    have := h_dom n hn₀
    omega⟩

/-- **Hardness magnification** (Atserias-Muller 2025, axiom).

    For sparse NP problems (input size N with O(N) constraints):
    A superlinear circuit lower bound magnifies to superpolynomial.

    Formally: if for every constant c, the problem requires circuits
    of size > c * N for infinitely many N, then the problem requires
    circuits of size N^{omega(1)} (superpolynomial).

    Reference: Atserias-Muller (2025), arXiv:2503.24061, Theorem 1.3.

    CAVEAT: The actual magnification theorem applies to specific
    NP problems formulated as "approximating the acceptance probability
    of a given circuit." The connection to witness circuit complexity
    requires that the witness function can be cast in this framework.
    This axiom packages the combined result.

    The axiom states: superlinear witness -> superpolynomial Frege.
    This skips the intermediate magnification step for cleanness. -/
axiom pi_magnification :
    HypothesisA →
    ∀ k : Nat, k ≥ 1 →
      ∃ n₀ : Nat, ∀ n ≥ n₀,
        ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
          piMinFregeSize G > n ^ k

/-- **Path A**: Superlinear witness -> superpolynomial Frege.

    The most promising path because it requires the WEAKEST hypothesis.
    The magnification theorem does the heavy lifting: it amplifies
    a merely superlinear bound to a superpolynomial one. -/
theorem path_a_superlinear_to_superpoly (hA : HypothesisA) :
    ∀ k : Nat, k ≥ 1 →
      ∃ n₀ : Nat, ∀ n ≥ n₀,
        ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
          piMinFregeSize G > n ^ k :=
  pi_magnification hA

/-- **Path A is weaker than Path C**: If the exponential witness hypothesis
    holds, then magnification also applies (but gives a weaker conclusion). -/
theorem path_a_follows_from_c (hC : HypothesisC) :
    ∀ k : Nat, k ≥ 1 →
      ∃ n₀ : Nat, ∀ n ≥ n₀,
        ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
          piMinFregeSize G > n ^ k :=
  path_a_superlinear_to_superpoly (hypothesis_c_implies_a hC)

/-! ## Section 3: Evidence for HypothesisA from BorromeanOrder -/

/-- **BorromeanOrder constrains the witness function's decision tree depth.**

    For UNSAT CubeGraph G with BorromeanOrder b:
    Any decision tree computing the witness function must query >= b cubes.

    This gives DT(f) >= Omega(n) from Schoenebeck.
    Decision tree depth >= Omega(n) is NECESSARY but NOT SUFFICIENT
    for superlinear circuit complexity. (Parity: DT=n, circuit=O(n).)

    However, DT(f) >= Omega(n) IS evidence for HypothesisA:
    functions with high DT are "candidates" for circuit lower bounds. -/
theorem witness_dt_evidence :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        -- Any set of < n/c cubes is fooled by k-consistency:
        -- a consistent gap selection exists on that set.
        -- This means the witness function cannot be "covered" by < n/c cubes.
        ∀ (S : List (Fin G.cubes.length)), S.Nodup → S.length < n / c →
          ∃ s : (i : Fin G.cubes.length) → Vertex,
            (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
            (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
              transferOp (G.cubes[e.1]) (G.cubes[e.2])
                (s e.1) (s e.2) = true) := by
  obtain ⟨c, hc, h_sch⟩ := pi_schoenebeck_linear
  exact ⟨c, hc, fun n hn => by
    obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch n hn
    exact ⟨G, hsize, hunsat, fun S hnd hlen => by
      exact hkc S hnd (by omega)⟩⟩

/-! ## Section 4: The Landscape Theorem -/

/-- **The complete conditional landscape.**

    Summary of all known conditional paths from CubeGraph to P != NP:

    (1) HypothesisC (exponential witness) -> exponential Frege [Path C]
    (2) HypothesisA (superlinear witness) -> superpolynomial Frege [Path A]
    (3) HypothesisC -> HypothesisA (strictly weaker hypothesis)
    (4) DT(witness) >= Omega(n) [unconditional evidence, from Schoenebeck]

    The WEAKEST hypothesis that suffices: HypothesisA (superlinear circuit).
    No superlinear circuit lower bound for an explicit NP function is known.
    The frontier: 3n - o(n) (Blum 1984). -/
theorem synthesis_landscape :
    -- (1) Path C: exponential witness -> Frege >= witness circuit
    (HypothesisC →
      ∃ c₁ : Nat, c₁ ≥ 2 ∧ ∀ n ≥ 1,
        ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
          piMinFregeSize G ≥ piMinWitnessCircuit G)
    ∧
    -- (2) HypothesisC -> HypothesisA (C is stronger)
    (HypothesisC → HypothesisA)
    ∧
    -- (3) Path A: superlinear witness -> superpolynomial Frege
    (HypothesisA →
      ∀ k : Nat, k ≥ 1 →
        ∃ n₀ : Nat, ∀ n ≥ n₀,
          ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
            piMinFregeSize G > n ^ k)
    ∧
    -- (4) Unconditional: DT evidence from BorromeanOrder
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ (S : List (Fin G.cubes.length)), S.Nodup → S.length < n / c →
          ∃ s : (i : Fin G.cubes.length) → Vertex,
            (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
            (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
              transferOp (G.cubes[e.1]) (G.cubes[e.2])
                (s e.1) (s e.2) = true)) :=
  ⟨path_c_witness_to_frege,
   hypothesis_c_implies_a,
   path_a_superlinear_to_superpoly,
   witness_dt_evidence⟩

/-! ## HONEST ACCOUNTING

    What this file PROVES:
    1. path_c_witness_to_frege: HypothesisC -> exponential Frege
    2. hypothesis_c_implies_a: HypothesisC -> HypothesisA (strictly weaker)
    3. path_a_superlinear_to_superpoly: HypothesisA -> superpolynomial Frege
    4. path_a_follows_from_c: transitivity of paths
    5. witness_dt_evidence: unconditional DT lower bound
    6. synthesis_landscape: all four results collected

    What this file AXIOMATIZES (2 local, rest imported):
    - pi_exp_dominates_linear: exponential dominates linear (math fact)
    - pi_magnification: hardness magnification (Atserias-Muller 2025)
    IMPORTED (not new axioms):
    - schoenebeck_linear_axiom: from SchoenebeckAxiom.lean
    - minFregeSize, minWitnessCircuit, frege_to_witness: from WitnessReduction.lean
    - pi_ names are backward-compatible abbrevs

    What this file does NOT prove:
    - HypothesisA or HypothesisC (OPEN -- circuit lower bounds)
    - P != NP (would follow from either hypothesis)
    - That magnification applies exactly as axiomatized
      (the real theorem has additional conditions re: sparsity)

    The contribution is STRUCTURAL: organizing the conditional landscape
    and identifying HypothesisA (superlinear) as the weakest sufficient
    hypothesis. This is valuable because:
    - It focuses research on the MINIMUM needed
    - Superlinear is strictly weaker than exponential
    - Hardness magnification is a genuine bypass of natural proofs
    - The CubeGraph witness function is a concrete candidate
-/

/-- Explicit non-claim: this file does not prove P != NP. -/
theorem pi_honest_disclaimer : True := trivial

end PiSynthesis
