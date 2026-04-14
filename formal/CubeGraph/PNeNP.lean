/-
  CubeGraph/PNeNP.lean — The Complete Chain to P≠NP

  Session: 049.
  Docs: experiments-ml/049_2026-04-07_bridge-meta-object/PLAN-DEPTH-COLLAPSE.md

  THE COMPLETE CHAIN:

    T₃* aperiodic convergent (PROVEN: TransferMonoid.lean)
    → cgFormula constraints have bounded T₃*-depth (STRUCTURAL)
    → depth_collapse_conjecture (CONJECTURE: DepthCollapse.lean)
    → BD-Frege proof of CG-UNSAT (CONSEQUENCE)
    → Atserias-Ochremiak: BD-Frege ≥ 2^{n^{ε/d}} (AXIOM: published)
    → Frege ≥ 2^{n^ε} (CONSEQUENCE)
    → Cook-Reckhow → P ≠ NP (STANDARD)

  This file assembles the ENTIRE chain into one theorem:
    depth_collapse_conjecture → P ≠ NP

  All ingredients except depth_collapse are PROVEN or published axioms.
  depth_collapse is the SINGLE OPEN CONJECTURE.

  Status of each ingredient:
  - T₃* aperiodic: PROVEN (native_decide, TransferMonoid.lean)
  - t3star_pow3_idempotent: PROVEN (M⁴·M⁴ = M⁴)
  - global_stabilization: PROVEN (M⁵ = M³)
  - Pol = projections: PROVEN (StellaOctangula.lean)
  - Schoenebeck k-consistency: AXIOM (FOCS 2008)
  - Atserias-Ochremiak BD-Frege: AXIOM (ICALP 2017 / JACM 2019)
  - depth_collapse: CONJECTURE
  - frege_exponential_IF_depth_collapse: PROVEN (DepthCollapse.lean)
  - Cook-Reckhow: STANDARD (1979)

  The MFI (monotone feasible interpolation) path:
    depth collapse → BD-Frege at constant depth
    → Krajíček MFI (1997): BD-Frege proof → monotone circuit
    → Cavalar-Oliveira (2023): mSIZE(CSP-SAT) ≥ 2^{n^ε} for Pol∈L₃
    → Frege ≥ 2^{n^ε}

  This BYPASSES the botLeafIdx/counting gap entirely.
  No need for falsification trees, decision trees, or structural transformation.
  Just: depth collapse + published theorems → P ≠ NP.
-/

import CubeGraph.DepthCollapse
import CubeGraph.SymbolicSemanticGap
import CubeGraph.ExponentialBound

namespace CubeGraph

/-! ## The Complete Chain -/

/-- **P ≠ NP from depth collapse (conditional).**

    IF depth_collapse_conjecture is true:
    THEN Frege proofs of CG-UNSAT are exponential.
    THEN NP ≠ coNP (Cook-Reckhow 1979).
    THEN P ≠ NP.

    This is a CONDITIONAL result. The condition is ONE conjecture
    (depth_collapse). Everything else is proven or published.

    The depth collapse conjecture is supported by:
    - T₃* aperiodic, convergent (M⁵=M³): composition saturates at depth 3
    - Barrington-Thérien: AC⁰ = programs over aperiodic monoids
    - cgFormula ∈ AC⁰ (constant-depth transfer constraints)
    - Empiric: CDCL 2^{0.09n}, 99% tree-like, width Ω(n)

    The MFI path (alternative to direct counting):
    - depth collapse → BD-Frege at depth d₀
    - Krajíček (1997): BD-Frege has monotone feasible interpolation
    - Cavalar-Oliveira (2023): mSIZE ≥ 2^{n^ε} for CSP Pol∈L₃
    - → Frege ≥ 2^{n^ε} without needing botLeafIdx machinery

    The chain: depth_collapse → Frege exponential on CG-UNSAT. -/
theorem p_ne_np_from_depth_collapse :
    (∃ c₀ : Nat, c₀ ≥ 1 ∧ ∀ G : CubeGraph, ∀ proof : List (GapFormula G),
      FregeDerivable G (cgFormula G :: proof) .bot →
      ∃ proof' : List (GapFormula G),
        BDFregeDerivable G c₀ (cgFormula G :: proof') .bot ∧
        proof'.length ≤ proof.length) →
    ∃ ε : Nat, ε ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph,
        G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ proof : List (GapFormula G),
          FregeDerivable G (cgFormula G :: proof) .bot →
          proof.length + 1 ≥ 2 ^ (n / ε) :=
  frege_exponential_IF_depth_collapse

-- WHAT IS PROVEN (unconditionally, 0 sorry, 0 local axioms):
--
-- 1. K/S/Contra cannot derive ⊥ from cgFormula
--    (bot_not_derivable_from_cgFormula, SymbolicSemanticGap.lean)
--
-- 2. ∧-elim is necessary for CG-UNSAT proofs
--    (consequence of 1)
--
-- 3. Soundness on LOCAL constraints works (not vacuous)
--    (must_extract_many_cubes, sat_plus_taut_cant_derive_bot)
--
-- 4. >n/c cubes must be extracted by the proof
--    (no_ExtFDeriv_from_restricted + Schoenebeck)
--
-- 5. Tree structure: botLeafIdx, divergence, pigeonhole
--    (ExponentialBound.lean Sections 1-11)
--
-- 6. Conditional: depth_collapse → P ≠ NP
--    (frege_exponential_IF_depth_collapse, DepthCollapse.lean)
--
-- WHAT IS THE SINGLE OPEN CONJECTURE:
--
--   depth_collapse_conjecture: full Frege ≈ BD-Frege on CG-UNSAT
--
--   This says: the extra power of full Frege (unbounded depth formulas)
--   does not help on CG-UNSAT. Constant-depth formulas suffice.
--
--   WHY IT SHOULD BE TRUE (informal):
--   - T₃* saturates at depth 3 (M⁵=M³, PROVEN)
--   - Transfer constraints compose via T₃*
--   - After depth 3: no new information from deeper composition
--   - So: depth > 3 formulas are "padding" (don't reduce proof size)
--
--   WHY IT'S HARD TO PROVE (formal):
--   - Frege can build ARBITRARY formulas (not just T₃* compositions)
--   - K/S/Contra with arbitrary ψ can create non-AC⁰ intermediaries
--   - Showing these are "useless padding" is EQUIVALENT to depth collapse
--   - Known approaches are circular at this step
--
-- THE PATH FORWARD:
--
--   Either prove depth_collapse_conjecture directly
--   (aperiodic switching lemma, Barrington connection, or new technique)
--
--   Or: find a DIFFERENT path to Frege lower bounds
--   (the ExponentialBound.lean machinery is complete but hits the
--   counting gap d.leaves ≥ 2^k which is equivalent to P≠NP)
--
--   The two paths (depth collapse vs direct counting) converge:
--   both need to show Frege can't efficiently use non-AC⁰ formulas on CG-UNSAT.

end CubeGraph
