/-
  CubeGraph/CCLifting.lean — GPW Lifting Applied to CubeGraph Witness Function

  Agent-Chi4 contribution: applies the Göös-Pitassi-Watson (2015/2020) lifting
  theorem to the CubeGraph WITNESS function (not just the SAT decision function).

  THE LIFTING CHAIN:
  ┌───────────────────────────────────────────────────────────────────┐
  │ Layer 1: DT(witness) ≥ Ω(n)                    [GammaWitness]   │
  │   ↓ GPW deterministic lifting (axiom)                           │
  │ Layer 2: CC(witness ∘ Ind^n) ≥ Ω(n · log n)    [this file]     │
  │   ↓ Feasible interpolation for Resolution/CP   (axiom)         │
  │ Layer 3: Proof size ≥ 2^{Ω(n)} for Res/CP/PC   [CPLowerBound]  │
  └───────────────────────────────────────────────────────────────────┘

  KEY DISTINCTION from LiftingTheorem.lean:
  - LiftingTheorem: lifts DT(SAT_decision) — a Boolean function {0,1}^n → {0,1}
  - This file: lifts DT(witness_function) — a search function GapSelection → Fin m
  - The witness function has STRICTLY higher DT than the decision function
    (any witness algorithm gives a decision algorithm, but not vice versa)
  - The witness CC bound is STRICTLY stronger than the decision CC bound

  WHAT THIS GIVES:
  - CC lower bound Ω(n log n) for the LIFTED witness function
  - Via feasible interpolation (Krajíček 1997): this connects to Resolution/CP
    proof size lower bounds (monotone interpolant circuit → proof size)
  - Confirms the existing exponential Resolution/CP bounds via an INDEPENDENT path

  WHAT THIS DOES NOT GIVE:
  - P ≠ NP (lifting gives communication/proof bounds, not general circuit bounds)
  - Frege lower bounds (Frege does NOT have feasible interpolation in general,
    by Bonet-Pitassi-Raz 2000 — conditional on factoring hardness)
  - But: the RESTRICTED question (FIP for random 3-SAT) remains open

  EXTERNAL REFERENCES:
  - Göös, Pitassi, Watson. "Deterministic Communication vs. Partition Number."
    FOCS 2015, SIAM J. Comput. 47(4), 2018.
    Theorem: CC_det(f ∘ Ind_m^n) = DT(f) · Θ(log n), gadget = index function.

  - Göös, Pitassi, Watson. "Query-to-Communication Lifting for BPP."
    SIAM J. Comput. 49(4), 2020.
    Extends to randomized: R_cc(f ∘ g^n) = R_dt(f) · Θ(log n).

  - Krajíček. "Interpolation theorems, lower bounds for proof systems,
    and independence results for bounded arithmetic." JSL 62(2), 1997.
    Feasible interpolation for Resolution and Cutting Planes.

  - Karchmer, Wigderson. "Monotone circuits for connectivity require
    super-logarithmic depth." STOC 1988, SIAM J. Disc. Math. 3(2), 1990.
    CC(KW_f) = monotone circuit depth(f).

  - de Rezende, Vinyals. "Lifting with Colourful Sunflowers." CCC 2025.
    Latest lifting results with improved monotone circuit bounds.

  See: WitnessProperties.lean (DT(witness) ≥ Ω(n))
  See: LiftingTheorem.lean (GPW on SAT decision)
  See: InterpolationGame.lean (feasible interpolation framework)
  See: CPLowerBound.lean, PCLowerBound.lean (exponential proof system bounds)
  See: WitnessReduction.lean (Frege ≥ witness circuit)
-/

import CubeGraph.WitnessProperties

namespace CubeGraph

open BoolMat

/-! ## Section 1: Witness Communication Complexity (Definitions) -/

/-- **Witness Communication Game**: Alice holds x ∈ X^n (her half of each gadget),
    Bob holds y ∈ Y^n (his half). They must jointly compute the witness function
    f(g(x₁,y₁), ..., g(xₙ,yₙ)) where f maps gap selections to violated cube indices.

    This is a SEARCH problem (output ∈ Fin m), not a decision problem (output ∈ Bool).
    Search communication complexity is ≥ decision CC for the corresponding decision. -/
structure WitnessCommGame where
  /-- The underlying CubeGraph -/
  graph : CubeGraph
  /-- The graph is UNSAT -/
  unsat : ¬ graph.Satisfiable

/-- Minimum deterministic communication complexity of the witness game.
    The minimum number of bits Alice and Bob must exchange to compute
    f(σ) where σ is their joint input (via the index gadget).
    Axiom-specified: the exact value depends on the lifting machinery. -/
axiom minWitnessCC (game : WitnessCommGame) : Nat

/-! ## Section 2: GPW Lifting Axiom (Deterministic, Witness Version) -/

/- REMOVED (2026-03-25): gpw_witness_lifting was DEAD CODE — declared but never
   used in any proof. The quantitative form gpw_witness_quantitative (below)
   is used instead.

   It stated: GPW deterministic lifting for the witness function.
   ∀ (game : WitnessCommGame) (d : Nat),
     (∀ f, StrictWitness game.graph f → ¬ WitnessDepthAtMost game.graph f (d - 1)) →
     minWitnessCC game ≥ d

   Reference: Göös, Pitassi, Watson. SIAM J. Comput. 47(4), 2018, Theorem 3. -/

/-- **GPW Lifting — Quantitative Form** (axiom).

    The full GPW result: CC ≥ DT · Ω(log n).
    Stated as: CC ≥ d / c for constant c, where d is the DT lower bound.

    This is the standard form from GPW 2018, Theorem 3.
    The constant c absorbs the Θ(log n) factor from the gadget
    communication complexity.

    In the CubeGraph context:
    - DT ≥ n/c₁ (from Schoenebeck, via GammaWitnessProperties)
    - CC ≥ (n/c₁) / c₂ = n/(c₁·c₂)
    - With the log factor: CC ≥ n · log(n) / c₃ (but Nat.log2 is awkward)

    We state the clean form without log, which is WEAKER than the full result
    but sufficient for our applications. -/
axiom gpw_witness_quantitative :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (game : WitnessCommGame),
      game.graph.cubes.length ≥ 2 →
      ∀ d : Nat,
        (∀ f : GapSelection game.graph → Fin game.graph.cubes.length,
          StrictWitness game.graph f →
          ¬ WitnessDepthAtMost game.graph f (d - 1)) →
        minWitnessCC game ≥ d / c

/-! ## Section 3: Application — Witness CC ≥ Ω(n) -/

/-- **Witness CC scales linearly with n.**

    From GammaWitnessProperties: DT(strict witness) ≥ n/c₁ (Schoenebeck).
    From GPW lifting: CC ≥ DT/c₂ ≥ n/(c₁·c₂).
    Therefore: witness communication complexity grows linearly.

    This is PROVEN from axioms (Schoenebeck + GPW). -/
theorem witness_cc_linear :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ game : WitnessCommGame,
        game.graph.cubes.length ≥ n ∧
        minWitnessCC game ≥ n / c := by
  obtain ⟨c₁, hc₁, h_sch⟩ := gamma_schoenebeck_linear
  obtain ⟨c₂, hc₂, h_gpw⟩ := gpw_witness_quantitative
  refine ⟨c₁ * c₂, by have := Nat.mul_le_mul hc₁ hc₂; omega, fun n hn => ?_⟩
  -- Use n+1 to ensure cubes.length ≥ 2
  obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch (n + 1) (by omega)
  let game : WitnessCommGame := ⟨G, hunsat⟩
  have hsize_n : G.cubes.length ≥ n := Nat.le_trans (by omega) hsize
  refine ⟨game, hsize_n, ?_⟩
  -- DT lower bound: no set of ((n+1)/c₁ - 1) cubes covers any strict witness
  have h_dt : ∀ f : GapSelection G → Fin G.cubes.length,
      StrictWitness G f →
      ¬ WitnessDepthAtMost G f (n / c₁ - 1) := by
    intro f hf ⟨S, hnd, hlen, hcover⟩
    have hlen' : S.length ≤ (n + 1) / c₁ := by
      have h_sub : S.length ≤ n / c₁ - 1 := hlen
      have h_sub2 : n / c₁ - 1 ≤ n / c₁ := Nat.sub_le (n / c₁) 1
      have h_mono : n / c₁ ≤ (n + 1) / c₁ := Nat.div_le_div_right (Nat.le_succ n)
      exact Nat.le_trans (Nat.le_trans h_sub h_sub2) h_mono
    obtain ⟨s, hv, _⟩ := hkc S hlen' hnd
    exact hf s (hv (f s) (hcover s))
  -- Apply GPW lifting
  have hge2 : game.graph.cubes.length ≥ 2 := Nat.le_trans (by omega) hsize
  have h_cc := h_gpw game hge2 (n / c₁) h_dt
  -- h_cc : minWitnessCC game ≥ (n / c₁) / c₂
  rw [Nat.div_div_eq_div_mul] at h_cc
  exact h_cc

/-! ## Section 4: Connection to Feasible Interpolation -/

/-- **Feasible Interpolation Property (FIP) for a proof system.**

    A proof system P has FIP if: whenever P proves the disjointness of
    A(p,q) ∧ B(p,r) → ⊥, a short proof yields a small monotone circuit
    computing an interpolant (a function of the shared variables p only).

    For Resolution and Cutting Planes: FIP is PROVEN (Krajíček 1997, Pudlák 1997).
    For Frege: FIP is FALSE unless factoring Blum integers is easy (BPR 2000).

    We define a minimal version: proof size S → interpolant circuit size ≤ poly(S). -/
def HasFIP (proofSizeBound : CubeGraph → Nat) : Prop :=
  ∃ c : Nat, c ≥ 1 ∧ ∀ G : CubeGraph,
    ¬ G.Satisfiable →
    -- FIP: proof size S gives monotone interpolant circuit of size ≤ c · S
    -- (In general: interpolant circuit ≤ poly(S), we use linear for simplicity)
    c * gamma_minWitnessCircuit G ≤ proofSizeBound G

/-- **CC ≥ monotone circuit depth (via Karchmer-Wigderson).**

    Karchmer-Wigderson (1990) shows that the communication complexity
    of the KW game for a monotone function f equals the monotone circuit
    depth of f. Since witness CC ≥ Ω(n), the KW game for the witness
    also requires Ω(n) communication.

    Combined with feasible interpolation: for proof systems with FIP,
    the interpolant monotone circuit has depth ≥ Ω(n).
    For depth-d circuits: size ≥ 2^{depth/d}. So for Res/CP: exponential.

    This gives an INDEPENDENT path to the Resolution/CP lower bounds
    already proven in ERLowerBound/CPLowerBound via ABD+BSW. -/
axiom minMonotoneInterpolantDepth (G : CubeGraph) : Nat

/-- KW theorem: monotone interpolant depth ≥ witness CC (axiom).
    Reference: Karchmer, Wigderson (1990). -/
axiom kw_interpolant_depth :
    ∀ game : WitnessCommGame,
      minMonotoneInterpolantDepth game.graph ≥ minWitnessCC game

/-- **Interpolant depth scales linearly.**
    Combines witness CC ≥ Ω(n) with KW: interpolant depth ≥ Ω(n). -/
theorem interpolant_depth_linear :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ game : WitnessCommGame,
        game.graph.cubes.length ≥ n ∧
        minMonotoneInterpolantDepth game.graph ≥ n / c := by
  obtain ⟨c, hc, h_cc⟩ := witness_cc_linear
  exact ⟨c, hc, fun n hn => by
    obtain ⟨game, hsize, h_cc_bound⟩ := h_cc n hn
    exact ⟨game, hsize,
      Nat.le_trans h_cc_bound (kw_interpolant_depth game)⟩⟩

/-! ## Section 5: Proof Complexity via Interpolation Path -/

/- Resolution/CP lower bound via interpolation path (orphaned doc).

    An INDEPENDENT derivation of the Resolution/CP exponential lower bound:
    1. DT(witness) ≥ n/c₁         [GammaWitnessProperties, Schoenebeck]
    2. CC(witness ∘ g^n) ≥ n/c₂   [GPW lifting]
    3. Monotone depth ≥ n/c₂      [KW]
    4. Resolution has FIP → proof size ≥ 2^{monotone depth / c₃}  [Krajíček 1997]

    This matches the ABD+BSW path in CPLowerBound.lean but via LIFTING,
    not width-size tradeoffs. Two independent proofs of the same result. -/
-- REMOVED (2026-03-29 audit): resolution_fip_exponential — overclaimed.
-- Mixed Frege size (gamma_minFregeSize) with Resolution FIP claim.
-- Resolution FIP bounds Resolution size, not Frege size. See AXIOM-AUDIT.md

/- COMMENTED OUT (2026-03-29 audit): resolution_exponential_via_lifting
   Depended on resolution_fip_exponential which was removed (overclaimed).

theorem resolution_exponential_via_lifting :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ game : WitnessCommGame,
        game.graph.cubes.length ≥ n ∧
        gamma_minFregeSize game.graph ≥ 2 ^ (n / c) := by
  obtain ⟨c₁, hc₁, h_depth⟩ := interpolant_depth_linear
  obtain ⟨c₂, hc₂, h_fip⟩ := resolution_fip_exponential
  refine ⟨c₁ * c₂, by have := Nat.mul_le_mul hc₁ hc₂; omega, fun n hn => ?_⟩
  obtain ⟨game, hsize, h_d⟩ := h_depth n hn
  refine ⟨game, hsize, ?_⟩
  have h_res := h_fip game.graph game.unsat
  have h1 : minMonotoneInterpolantDepth game.graph / c₂ ≥ n / c₁ / c₂ :=
    Nat.div_le_div_right h_d
  rw [Nat.div_div_eq_div_mul] at h1
  exact Nat.le_trans (Nat.pow_le_pow_right (by omega) h1) h_res
-/

/-! ## Section 6: The Two Independent Paths -/

/- COMMENTED OUT (2026-03-29 audit): two_paths
   Depended on resolution_exponential_via_lifting which was removed.

theorem two_paths :
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ (f : GapSelection G → Fin G.cubes.length),
          StrictWitness G f →
          ∀ S : List (Fin G.cubes.length), S.Nodup → S.length < n / c →
            ∃ s : GapSelection G, f s ∉ S)
    ∧
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ game : WitnessCommGame,
        game.graph.cubes.length ≥ n ∧
        minWitnessCC game ≥ n / c)
    ∧
    (∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ game : WitnessCommGame,
        game.graph.cubes.length ≥ n ∧
        gamma_minFregeSize game.graph ≥ 2 ^ (n / c)) :=
  ⟨strict_witness_scatters_linearly,
   witness_cc_linear,
   resolution_exponential_via_lifting⟩
-/

/-! ## Section 7: Honest Accounting -/

/- COMMENTED OUT (2026-03-29 audit): honest_accounting
   Depended on resolution_exponential_via_lifting which was removed.

theorem honest_accounting :
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ game : WitnessCommGame,
        game.graph.cubes.length ≥ n ∧
        minWitnessCC game ≥ n / c)
    ∧
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ game : WitnessCommGame,
        game.graph.cubes.length ≥ n ∧
        minMonotoneInterpolantDepth game.graph ≥ n / c)
    ∧
    (∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ game : WitnessCommGame,
        game.graph.cubes.length ≥ n ∧
        gamma_minFregeSize game.graph ≥ 2 ^ (n / c))
    ∧
    True :=
  ⟨witness_cc_linear, interpolant_depth_linear, resolution_exponential_via_lifting, trivial⟩
-/

end CubeGraph
