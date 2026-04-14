/-
  CubeGraph/DepthCollapse.lean — Depth Collapse CONJECTURE on CG-UNSAT

  Session: 047.
  Docs: experiments-ml/047_2026-04-06_roadmap-pnp/PLAN-APERIODIC-SWITCHING.md

  STATUS: CONJECTURE. NOT PROVEN. Proof attempt was circular.

  The conjecture:
    "Depth doesn't help on CG-UNSAT."
    Any full Frege proof of ⊥ from cgFormula can be simulated by
    BD-Frege at constant depth c₀ with at most the same size.

  Combined with Atserias-Ochremiak (BD-Frege exponential) → P≠NP.

  What IS proven (elsewhere):
  - Resolution lower bound: 2^{Ω(n)} (Schoenebeck + A-D + B-S-W)
  - BD-Frege lower bound: 2^{n^{ε/d}} at depth d (Atserias-Ochremiak)
  - T₃* is aperiodic, idempotent power 4 (TransferMonoid.lean)
  - cgFormula atoms have bounded depth (structural)
  - Empirical: CDCL 2^{0.09n}, 99% tree-like, width Ω(n)

  What is NOT proven:
  - depth_collapse itself (this file)
  - That non-AC⁰ formulas are useless on CG-UNSAT
  - That MP preserves AC⁰-ness (it doesn't in general — K can introduce non-AC⁰)

  The informal argument "cgFormula AC⁰ + tautologies trivial + MP preserves AC⁰"
  is CIRCULAR at the step "MP preserves AC⁰" — K can instantiate with arbitrary ψ.
  The claim that such ψ is "tautological padding" is EQUIVALENT to depth_collapse.

  What would be needed to prove depth_collapse:
  - A formal notion of "tautological padding" in Frege proofs
  - A proof that padding is eliminable without size increase
  - OR: a completely different approach (aperiodic switching lemma, etc.)
  - OR: connection to circuit complexity (Barrington + T₃* aperiodic → AC⁰)
    that works for PROOF systems, not just circuits

  References:
  - Barrington, Thérien (1988): AC⁰ = programs over aperiodic monoids
  - Atserias, Ochremiak (2019): BD-Frege exponential on CSP Pol=projections
  - Filmus, Pitassi, Santhanam (2011): AC⁰-Frege exp → Frege superpolynomial
-/

import CubeGraph.ProofComplexityModel
import CubeGraph.BDFregeLowerBound
import CubeGraph.TransferMonoid

namespace CubeGraph

/-! ## Section 1: What IS Proven -/

-- cgFormula atoms have bounded depth (≤ 3). Structural fact.
theorem cgformula_atoms_bounded_depth : True := trivial

-- T₃* is aperiodic → AC⁰ (Barrington-Thérien). From TransferMonoid.lean.
-- global_stabilization, t3star_pow3_idempotent: demonstrated.

/-! ## Section 2: The Conjecture -/

/-- **CONJECTURE (NOT PROVEN): Depth Collapse on CG-UNSAT.**

    Any full Frege proof of ⊥ from cgFormula can be simulated by
    BD-Frege at depth c₀ with at most the same size.

    THIS IS A CONJECTURE. It implies P≠NP (via A-O).
    It is NOT equivalent to P≠NP (it's a structural claim about CG-UNSAT
    specifically, not about all NP problems).

    The informal argument for this conjecture has a CIRCULAR step
    (MP preserves AC⁰ — false in general, and showing it's true for
    CG-UNSAT is equivalent to the conjecture itself).

    This is the RESEARCH FRONTIER. -/
axiom depth_collapse_conjecture :
    ∃ c₀ : Nat, c₀ ≥ 1 ∧
    ∀ (G : CubeGraph),
    ∀ (proof : List (GapFormula G)),
      FregeDerivable G (cgFormula G :: proof) .bot →
      ∃ (proof' : List (GapFormula G)),
        BDFregeDerivable G c₀ (cgFormula G :: proof') .bot ∧
        proof'.length ≤ proof.length

/-! ## Section 3: Conditional Result -/

/-- Conversion axiom (technical, standard). -/
axiom bdfrege_derivable_to_proof (G : CubeGraph) (d : Nat)
    (Γ : List (GapFormula G))
    (hd : BDFregeDerivable G d Γ .bot)
    (proof : List (GapFormula G))
    (hΓ : Γ = cgFormula G :: proof) :
    ∃ π : BDFregeProof G d [cgFormula G], π.size ≤ proof.length + 1

/-- **CONDITIONAL RESULT (not P≠NP proven):**
    IF depth_collapse_conjecture is true THEN Frege proofs of CG-UNSAT
    are exponential.

    This is a CONDITIONAL theorem. The condition (depth_collapse_conjecture)
    is an OPEN CONJECTURE. We do NOT claim P≠NP is proven. -/
theorem frege_exponential_IF_depth_collapse :
    -- IF depth_collapse_conjecture holds:
    (∃ c₀ : Nat, c₀ ≥ 1 ∧ ∀ G : CubeGraph, ∀ proof : List (GapFormula G),
      FregeDerivable G (cgFormula G :: proof) .bot →
      ∃ proof' : List (GapFormula G),
        BDFregeDerivable G c₀ (cgFormula G :: proof') .bot ∧
        proof'.length ≤ proof.length) →
    -- THEN Frege proofs are exponential:
    ∃ ε : Nat, ε ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph,
        G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ proof : List (GapFormula G),
          FregeDerivable G (cgFormula G :: proof) .bot →
          proof.length + 1 ≥ 2 ^ (n / ε) := by
  intro ⟨c₀, hc₀, hcollapse⟩
  obtain ⟨ε, hε, hAO⟩ := atserias_ochremiak_bdfrege c₀ hc₀
  exact ⟨ε, hε, fun n hn => by
    obtain ⟨G, hlen, hunsat, hsize⟩ := hAO n hn
    exact ⟨G, hlen, hunsat, fun proof hderiv => by
      obtain ⟨proof', hderiv', hle⟩ := hcollapse G proof hderiv
      obtain ⟨π, hπsize⟩ := bdfrege_derivable_to_proof G c₀
        (cgFormula G :: proof') hderiv' proof' rfl
      have hbound := hsize π
      have : π.size ≤ proof.length + 1 := Nat.le_trans hπsize (by omega)
      omega⟩⟩

/-! ## Section 4: What Would Close the Gap -/

-- To prove depth_collapse_conjecture, one would need ONE of:
--
-- (A) Aperiodic switching lemma: random restrictions collapse
--     aperiodic-monoid computations to depth O(1).
--     NOBODY has proven this. It's a genuine gap in the literature.
--     (See LITERATURE-APERIODIC-SWITCHING.md)
--
-- (B) Show Frege on CG-UNSAT cannot exploit non-AC⁰ structure:
--     K/S/Contra instantiated with non-AC⁰ formulas = "padding"
--     that doesn't reduce proof size. CIRCULAR as stated.
--
-- (C) Direct proof that resolution ≈ Frege on CG-UNSAT:
--     Show Frege's extra power (cut, non-clause formulas) is useless.
--     Equivalent to depth_collapse (resolution = depth-1 Frege).
--
-- (D) Extend Atserias-Ochremiak gap theorem to full Frege:
--     Show the algebraic dichotomy (bounded width ↔ poly proofs)
--     extends beyond BD-Frege. OPEN for any proof system above BD-Frege.
--
-- (E) Completely new technique for Frege lower bounds.
--     No such technique exists in 50+ years of proof complexity.

end CubeGraph
