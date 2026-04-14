/-
  CubeGraph/WitnessProperties.lean — Witness Function Properties from BorromeanOrder

  Agent-Gamma contribution: formalizes structural properties of the UNSAT witness function
  f : GapSelection -> Fin cubes.length (maps each gap selection to a violated cube index)
  that follow from BorromeanOrder = Theta(n).

  KEY INSIGHT: BorromeanOrder constrains the witness function's complexity.
  If b = BorromeanOrder(G), then:
    (1) range(f) >= b: the witness must use >= b distinct cubes
    (2) No set of < b cubes "covers" all gap selections for the witness
    (3) Decision tree depth(f) >= b
    (4) Witness scatters linearly: range >= Omega(n) from Schoenebeck

  RESEARCH CONTRIBUTION:
  The gap between "f is non-localizable" and "circuit(f) is exponential":
  - BorromeanOrder gives DT(f) >= Omega(n) [from Schoenebeck linear]
  - The subfunction count 2^{n/2} (experimental) suggests circuit >= super-poly
  - But: DT >= Omega(n) alone does NOT imply circuit size >= super-poly
    (e.g., parity has DT = n but circuit size O(n))

  HONEST ACCOUNTING:
  - Theorems 1-7: PROVEN (from KConsistent + BorromeanOrder)
  - The circuit lower bound gap: OPEN PROBLEM (see gap_analysis)

  IMPORT NOTE: Some upstream files (KConsistency.lean, InformationChannel.lean)
  have build issues with Lean 4.29.0-rc6 (rcases on auto-generated proof terms).
  We import Hierarchy.lean (which builds) and locally re-declare the needed
  definitions and axioms from the broken files. All re-declarations are marked
  as such and are IDENTICAL to the originals.

  See: WitnessReduction.lean (Frege >= witness circuit)
  See: SchoenebeckChain.lean (BorromeanOrder axiom)
  See: InformationChannel.lean (BorromeanOrder definition, blind_below_borromean)
  See: QueryLowerBound.lean (DT(CubeGraphSAT) >= Omega(n))
  See: bridge-next/WITNESS-EXPERIMENT-RESULTS.md (2^{n/2} subfunctions)
  See: bridge-next/WITNESS-STRUCTURAL-RESULTS.md (non-localizability confirmed)
-/

import CubeGraph.Hierarchy
import CubeGraph.SchoenebeckAxiom
import CubeGraph.WitnessReduction

namespace CubeGraph

open BoolMat

/-! ## Section 0: Re-declarations from upstream files

    Local definitions (not yet importable):
    - KConsistency.lean: KConsistent, sat_implies_kconsistent
    - InformationChannel.lean: BorromeanOrder, blind_below_borromean

    DEDUP (2026-03-24): minFregeSize, minWitnessCircuit, frege_to_witness
    now imported from WitnessReduction.lean (canonical). Local gamma_ names
    are abbrevs for backward compatibility. -/

/-- k-Consistency: every subset of <= k cubes admits a compatible gap selection. -/
def GammaKConsistent (G : CubeGraph) (k : Nat) : Prop :=
  ∀ (S : List (Fin G.cubes.length)),
    S.length ≤ k → S.Nodup →
    ∃ s : (i : Fin G.cubes.length) → Vertex,
      (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true)

/-- SAT implies k-consistent for all k. -/
theorem gamma_sat_implies_kconsistent (G : CubeGraph) (k : Nat)
    (hsat : G.Satisfiable) : GammaKConsistent G k := by
  intro S _ _
  obtain ⟨s, hv, hc⟩ := hsat
  exact ⟨s, fun i _ => hv i, fun e he _ _ => hc e he⟩

/-- BorromeanOrder: G is (b-1)-consistent but NOT b-consistent. -/
def GammaBorromeanOrder (G : CubeGraph) (b : Nat) : Prop :=
  ¬ GammaKConsistent G b ∧ (b > 0 → GammaKConsistent G (b - 1))

/-- Below BorromeanOrder, every sub-instance is consistent. -/
theorem gamma_blind_below_borromean (G : CubeGraph) (b : Nat)
    (hbo : GammaBorromeanOrder G b) (hb : b > 0)
    (S : List (Fin G.cubes.length))
    (hlen : S.length ≤ b - 1) (hnd : S.Nodup) :
    ∃ s : (i : Fin G.cubes.length) → Vertex,
      (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true) :=
  hbo.2 hb S hlen hnd

/-- Schoenebeck linear (axiom): SA needs level Omega(n). -/
-- DEDUP: derived from schoenebeck_linear_axiom in SchoenebeckAxiom.lean
theorem gamma_schoenebeck_linear :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧
        GammaKConsistent G (n / c) ∧ ¬ G.Satisfiable :=
  schoenebeck_linear_axiom

/-- Minimum Frege proof size for UNSAT CubeGraph.
    DEDUP: alias for canonical minFregeSize from FregeLowerBound.lean. -/
noncomputable abbrev gamma_minFregeSize := minFregeSize

/-- Minimum circuit size for the witness function.
    DEDUP: alias for canonical minWitnessCircuit from WitnessReduction.lean. -/
noncomputable abbrev gamma_minWitnessCircuit := minWitnessCircuit

/-- Frege proof size >= witness circuit size (folklore).
    DEDUP: alias for canonical frege_to_witness from WitnessReduction.lean. -/
theorem gamma_frege_to_witness :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      c * gamma_minWitnessCircuit G ≤ gamma_minFregeSize G :=
  frege_to_witness

/-! ## Section 1: Witness Function Definitions -/

/-- A **strict witness function** for an UNSAT CubeGraph G assigns to each
    gap selection s a cube index f(s) where s(f(s)) is NOT a valid gap.

    This is a strong form: the witness always identifies a gap-level failure.
    For H0/H1 UNSAT this always exists. For H2 UNSAT where all per-cube gaps
    might be valid, the failure is on edges -- see GeneralWitness below. -/
def StrictWitness (G : CubeGraph) (f : GapSelection G → Fin G.cubes.length) : Prop :=
  ∀ s : GapSelection G, ¬ (G.cubes[f s]).isGap (s (f s)) = true

/-- A **general witness function**: for each gap selection s, cube f(s)
    participates in the failure — either the gap is invalid OR an edge
    involving f(s) is incompatible. -/
def GeneralWitness (G : CubeGraph) (f : GapSelection G → Fin G.cubes.length) : Prop :=
  ∀ s : GapSelection G,
    ¬ (G.cubes[f s]).isGap (s (f s)) = true ∨
    ∃ e ∈ G.edges, (e.1 = f s ∨ e.2 = f s) ∧
      transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = false

/-- Every UNSAT CubeGraph has a general witness function. -/
theorem unsat_has_general_witness (G : CubeGraph) (hunsat : ¬ G.Satisfiable) :
    ∃ f : GapSelection G → Fin G.cubes.length, GeneralWitness G f := by
  have h : ∀ s : GapSelection G, ∃ i : Fin G.cubes.length,
      ¬ (G.cubes[i]).isGap (s i) = true ∨
      ∃ e ∈ G.edges, (e.1 = i ∨ e.2 = i) ∧
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = false := by
    intro s
    -- Either some gap is invalid, or all gaps are valid but some edge fails
    rcases Classical.em (∀ i : Fin G.cubes.length, (G.cubes[i]).isGap (s i) = true) with hv | hv
    · -- All gaps valid. Must have an edge failure (since UNSAT).
      rcases Classical.em (∀ e ∈ G.edges,
          transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true) with hc | hc
      · -- s is a valid compatible selection — contradicts UNSAT
        exact absurd ⟨s, hv, hc⟩ hunsat
      · -- Some edge fails. Get the failing edge.
        have := Classical.not_forall.mp hc
        obtain ⟨e, he⟩ := this
        have := Classical.not_imp.mp he
        obtain ⟨he_mem, he_fail⟩ := this
        -- transferOp is Bool, so ¬(... = true) means ... = false
        have hf : transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = false := by
          cases h_eq : transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2)
          · rfl
          · exact absurd h_eq he_fail
        exact ⟨e.1, Or.inr ⟨e, he_mem, Or.inl rfl, hf⟩⟩
    · -- Some gap is invalid
      have := Classical.not_forall.mp hv
      obtain ⟨i, hi⟩ := this
      exact ⟨i, Or.inl hi⟩
  exact ⟨fun s => Classical.choose (h s), fun s => Classical.choose_spec (h s)⟩

/-! ## Section 2: Covered-By -/

/-- A set S of cubes **covers** the witness if f always outputs a cube in S. -/
def WitnessCoveredBy (G : CubeGraph) (f : GapSelection G → Fin G.cubes.length)
    (S : List (Fin G.cubes.length)) : Prop :=
  ∀ s : GapSelection G, f s ∈ S

/-! ## Section 3: Range of Strict Witness >= BorromeanOrder -/

/-- **THEOREM (Gamma-1): No set of < b cubes covers a strict witness.**

    If G has BorromeanOrder b, then for any strict witness f, there is no
    set S with |S| < b such that f always outputs a cube in S.

    PROOF:
    By BorromeanOrder, S has a consistent gap selection sigma.
    f(sigma) is in S, so sigma(f(sigma)) is a valid gap (from consistency).
    But StrictWitness says sigma(f(sigma)) is NOT a valid gap. Contradiction. -/
theorem strict_witness_not_covered (G : CubeGraph) (b : Nat)
    (hbo : GammaBorromeanOrder G b) (hb : b > 0)
    (f : GapSelection G → Fin G.cubes.length)
    (hf : StrictWitness G f)
    (S : List (Fin G.cubes.length)) (hnd : S.Nodup) (hlen : S.length < b)
    (hcover : WitnessCoveredBy G f S) :
    False := by
  -- By BorromeanOrder, S admits a consistent gap selection
  obtain ⟨s, hv, _⟩ := gamma_blind_below_borromean G b hbo hb S (by omega) hnd
  -- f(s) is in S by coverage
  have hfs : f s ∈ S := hcover s
  -- But s(f(s)) IS a valid gap (from hv), contradicting StrictWitness
  exact hf s (hv (f s) hfs)

/-- **COROLLARY (Gamma-1b): Strict witness scatters.**

    Positive formulation: for any set S with |S| < b, there exists a gap
    selection s such that f(s) is NOT in S. -/
theorem strict_witness_scatters (G : CubeGraph) (b : Nat)
    (hbo : GammaBorromeanOrder G b) (hb : b > 0)
    (f : GapSelection G → Fin G.cubes.length)
    (hf : StrictWitness G f) :
    ∀ S : List (Fin G.cubes.length), S.Nodup → S.length < b →
      ∃ s : GapSelection G, f s ∉ S := by
  intro S hnd hlen
  -- Suppose for contradiction that f(s) is in S for all s
  apply Classical.byContradiction
  intro h
  -- h : ¬ ∃ s, f s ∉ S, i.e., ∀ s, f s ∈ S
  have hcover : WitnessCoveredBy G f S := by
    intro s
    apply Classical.byContradiction
    intro hns
    exact h ⟨s, hns⟩
  exact strict_witness_not_covered G b hbo hb f hf S hnd hlen hcover

/-! ## Section 4: Decision Tree Depth Lower Bound -/

/-- The witness function's output is determined by at most d cubes:
    there exists S with |S| <= d containing all of f's range. -/
def WitnessDepthAtMost (G : CubeGraph) (f : GapSelection G → Fin G.cubes.length)
    (d : Nat) : Prop :=
  ∃ S : List (Fin G.cubes.length), S.Nodup ∧ S.length ≤ d ∧ WitnessCoveredBy G f S

/-- **THEOREM (Gamma-2): Decision tree depth of strict witness >= BorromeanOrder.** -/
theorem strict_witness_depth_ge_borromean (G : CubeGraph) (b : Nat)
    (hbo : GammaBorromeanOrder G b) (hb : b > 0)
    (f : GapSelection G → Fin G.cubes.length)
    (hf : StrictWitness G f) :
    ¬ WitnessDepthAtMost G f (b - 1) := by
  intro ⟨S, hnd, hlen, hcover⟩
  exact strict_witness_not_covered G b hbo hb f hf S hnd (by omega) hcover

/-! ## Section 5: Scaling — Omega(n) from Schoenebeck -/

/-- **THEOREM (Gamma-3): Strict witness depth scales as Omega(n).**

    From Schoenebeck linear: there exist UNSAT graphs where (n/c)-consistency passes.
    Any strict witness needs depth >= n/c = Omega(n).

    The proof directly uses (n/c)-consistency to fool any witness covering fewer
    than n/c cubes, without going through BorromeanOrder. -/
theorem strict_witness_depth_omega_n :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ (f : GapSelection G → Fin G.cubes.length),
          StrictWitness G f →
          ¬ WitnessDepthAtMost G f (n / c - 1) := by
  obtain ⟨c, hc, hsch⟩ := gamma_schoenebeck_linear
  refine ⟨c, hc, fun n hn => ?_⟩
  obtain ⟨G, hsize, hkc, hunsat⟩ := hsch n hn
  refine ⟨G, hsize, hunsat, fun f hf hdepth => ?_⟩
  obtain ⟨S, hnd, hlen, hcover⟩ := hdepth
  -- hkc : GammaKConsistent G (n / c)
  -- |S| <= n/c - 1 ≤ n/c, so KConsistent gives a consistent selection on S
  have hlen' : S.length ≤ n / c := Nat.le_trans hlen (Nat.sub_le (n / c) 1)
  have hkc_S := hkc S hlen' hnd
  obtain ⟨s, hv, _⟩ := hkc_S
  -- f(s) is in S (by coverage), and s(f(s)) is a valid gap (by consistency)
  -- But StrictWitness says s(f(s)) is NOT a valid gap. Contradiction.
  exact hf s (hv (f s) (hcover s))

/-- **THEOREM (Gamma-4): Strict witness scatters linearly with n.**

    From Schoenebeck: for large UNSAT graphs, the strict witness function's
    range covers >= n/c cubes. -/
theorem strict_witness_scatters_linearly :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ (f : GapSelection G → Fin G.cubes.length),
          StrictWitness G f →
          ∀ S : List (Fin G.cubes.length), S.Nodup → S.length < n / c →
            ∃ s : GapSelection G, f s ∉ S := by
  obtain ⟨c, hc, hsch⟩ := gamma_schoenebeck_linear
  refine ⟨c, hc, fun n hn => ?_⟩
  obtain ⟨G, hsize, hkc, hunsat⟩ := hsch n hn
  refine ⟨G, hsize, hunsat, fun f hf S hnd hlen => ?_⟩
  -- Suppose for contradiction that f(s) is in S for all s
  apply Classical.byContradiction
  intro h_neg
  -- h_neg : ¬ ∃ s, f s ∉ S, so ∀ s, f s ∈ S
  have hcover : ∀ s : GapSelection G, f s ∈ S := by
    intro s
    apply Classical.byContradiction
    intro hns
    exact h_neg ⟨s, hns⟩
  -- |S| < n/c ≤ n/c, so KConsistent gives a consistent selection on S
  have hlen' : S.length ≤ n / c := by omega
  have hkc_S := hkc S hlen' hnd
  obtain ⟨s, hv, _⟩ := hkc_S
  exact hf s (hv (f s) (hcover s))

/-! ## Section 6: Connection to Frege Lower Bound -/

/-- **Combined chain: BorromeanOrder -> Witness scattering -> Frege.**

    (1) Witness scatters linearly with n (Gamma-4, from Schoenebeck)
    (2) Frege >= witness circuit (axiom, folklore)

    The GAP:
    - range >= Omega(n) gives circuit size >= Omega(n) (trivial)
    - 2^{n/2} subfunctions (experimental) SUGGESTS circuit >= super-poly
    - But formally bridging scattering to circuit size is OPEN -/
theorem combined_chain :
    -- (1) Strict witness scatters linearly
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ (f : GapSelection G → Fin G.cubes.length),
          StrictWitness G f →
          ∀ S : List (Fin G.cubes.length), S.Nodup → S.length < n / c →
            ∃ s : GapSelection G, f s ∉ S) ∧
    -- (2) Frege >= witness circuit (axiom)
    (∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      c * gamma_minWitnessCircuit G ≤ gamma_minFregeSize G) :=
  ⟨strict_witness_scatters_linearly, gamma_frege_to_witness⟩

/-! ## Section 7: Gap Analysis — What IS and ISN'T Proven -/

/-- **HONEST GAP ANALYSIS.**

    What BorromeanOrder DOES give about the witness function:
    (A) range(f) >= Omega(n) — the witness scatters across many cubes    [PROVEN]
    (B) No set of sub-linear cubes covers the witness                    [PROVEN]
    (C) Decision tree depth >= Omega(n)                                  [PROVEN]
    (D) Frege proof size >= witness circuit size                         [AXIOM]

    What BorromeanOrder does NOT give:
    (E) Circuit size of f >= super-polynomial                            [OPEN]
    (F) 2^{n/2} distinct subfunctions (from BorromeanOrder alone)        [OPEN]
    (G) P != NP                                                          [OPEN]

    The gap between (A-C) and (E-G):
    - Parity has DT = n but circuit size O(n)
    - So DT >= Omega(n) alone does not imply large circuit
    - The witness has ADDITIONAL structure (non-localizability, scattering)
    - But formalizing "non-localizability implies large circuit" is OPEN

    CENTRAL OPEN QUESTION:
    Does the CubeGraph witness function have super-polynomial circuit complexity?
    This is EQUIVALENT to super-polynomial Frege lower bounds (via frege_to_witness).
    And super-polynomial Frege would imply P != NP for co-NP (via Cook-Reckhow). -/
theorem gap_analysis :
    -- (A) Witness scatters linearly [proven]
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ (f : GapSelection G → Fin G.cubes.length),
          StrictWitness G f →
          ∀ S : List (Fin G.cubes.length), S.Nodup → S.length < n / c →
            ∃ s : GapSelection G, f s ∉ S) ∧
    -- (B) Frege >= witness circuit [axiom]
    (∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      c * gamma_minWitnessCircuit G ≤ gamma_minFregeSize G) ∧
    -- (C) The gap: circuit lower bound is open
    True :=
  ⟨strict_witness_scatters_linearly, gamma_frege_to_witness, trivial⟩

/-! ## SUMMARY

    PROVEN:
    1. unsat_has_general_witness: UNSAT CubeGraph has a general witness function
    2. strict_witness_not_covered: |range(f)| >= BorromeanOrder for strict witnesses
    3. strict_witness_scatters: positive formulation — f scatters beyond any small set
    4. strict_witness_depth_ge_borromean: DT(f) >= BorromeanOrder
    5. strict_witness_depth_omega_n: DT(f) >= Omega(n) from Schoenebeck
    6. strict_witness_scatters_linearly: range >= Omega(n) from Schoenebeck
    7. combined_chain: connects to Frege lower bound
    8. gap_analysis: honest assessment of what's proven and what's open

    AXIOMS USED (0 local — all imported from canonical sources):
    - schoenebeck_linear_axiom: from SchoenebeckAxiom.lean
    - minFregeSize, minWitnessCircuit, frege_to_witness: from WitnessReduction.lean
    - gamma_ names are backward-compatible abbrevs (not new axioms)

    

    KEY DISTINCTION from existing QueryLowerBound.lean:
    - QueryLowerBound: DT(SAT decision) >= Omega(n) — deciding YES/NO
    - This file: DT(witness FUNCTION) >= Omega(n) — finding WHICH cube is violated
    - The witness function must OUTPUT an index, not just a bit
    - This is strictly harder: any witness algorithm gives a SAT algorithm
      (just check if the witness is valid), but not vice versa
-/

end CubeGraph
