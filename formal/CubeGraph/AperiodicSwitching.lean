/-
  CubeGraph/AperiodicSwitching.lean — T₃* Algebraic Properties for Proof Complexity

  Session: 047.
  Docs: experiments-ml/047_2026-04-06_roadmap-pnp/LITERATURE-APERIODIC-SWITCHING.md
        experiments-ml/047_2026-04-06_roadmap-pnp/PLAN-APERIODIC-SWITCHING.md

  STATUS: Algebraic facts PROVEN. Switching lemma CONJECTURED (not proven by anyone).

  What IS proven here:
  - T3Program definition and evaluation
  - t3star_stabilization_depth = 3
  - t3star_stabilizes: M⁵ = M³ (from global_stabilization)
  - t3star_pow3_idempotent: (M⁴)² = M⁴ — idempotent power PROVEN (native_decide)

  What is CONJECTURED (research frontier, not proven):
  - Aperiodic switching lemma (nobody has proven this, novel concept)
  - useful_formulas_are_ac0 (equivalent to depth_collapse)

  The algebraic facts (idempotent barriers, aperiodicity) are EVIDENCE
  for why depth collapse might be true, but NOT a proof of it.

  References:
  - Barrington, Thérien (1988): AC⁰ = programs over aperiodic monoids
-/

import CubeGraph.Basic
import CubeGraph.TransferMonoid
import CubeGraph.BDFregeLowerBound

namespace CubeGraph

/-! ## Section 1: Monoid Programs over T₃* -/

/-- A monoid program over T₃*. -/
structure T3Program where
  length : Nat
  varIndex : Fin length → Nat
  element : Fin length → Vertex → T3Star

/-- Evaluate a T₃* program on an input. -/
def T3Program.eval (prog : T3Program) (input : Nat → Vertex) : T3Star :=
  (List.finRange prog.length).foldl
    (fun acc i => T3Star.mul acc (prog.element i (input (prog.varIndex i))))
    ⟨0, by omega⟩

/-! ## Section 2: Aperiodicity — PROVEN -/

def t3star_stabilization_depth : Nat := 3

-- M⁵ = M³ (from TransferMonoid.lean)
theorem t3star_stabilizes : (List.finRange 28).all (fun m =>
    T3Star.pow m 4 == T3Star.pow m 2) = true := global_stabilization

/-- M⁴ is IDEMPOTENT: (M⁴)² = M⁴ for ALL elements of T₃*.
    PROVEN by native_decide (exhaustive check on 28 elements).
    This means: gaps of ≥ 4 consecutive elements → idempotent barriers. -/
theorem t3star_pow3_idempotent :
    (List.finRange 28).all (fun m =>
      T3Star.mul (T3Star.pow m 3) (T3Star.pow m 3) ==
      T3Star.pow m 3) = true := by native_decide

/-! ## Section 3: Conjectures (NOT proven, for reference) -/

-- CONJECTURE: aperiodic switching lemma
-- Under random restriction, programs over aperiodic monoids collapse
-- to depth O(1) INDEPENDENT of syntactic depth d.
-- STATUS: NOBODY has proven this. Novel concept. Research frontier.
-- Gap in literature: switching lemmas × monoid theory never combined.

-- CONJECTURE: useful_formulas_are_ac0
-- In any Frege proof of CG-UNSAT, useful formulas compute AC⁰ functions.
-- STATUS: EQUIVALENT to depth_collapse (circular if used as axiom).
-- Evidence: T₃* aperiodic → AC⁰ (Barrington), empiric (99% tree-like).

end CubeGraph
