/-
  CubeGraph/XORCounterexample.lean — Is the XOR counterexample valid?

  CLAIM: ∃ proof d of CG-UNSAT with huniv and O(D) leaves.
  CONSTRUCTION: d = mp d1 d2 where d2 derives XOR via ex falso.

  Adrian says: this is WRONG. Let's find out WHERE.
-/

import CubeGraph.ExponentialBound

namespace CubeGraph

/-! ## The XOR counterexample — formalized

  d2 derives XOR(v₁,...,vD) from [cgFormula G].
  d2 = mp (fax (⊥ → XOR)) sub_proof
  where sub_proof : ExtFDeriv G [cgFormula G] .bot.

  Question: can d2 have O(D) leaves? -/

/-- Can we derive an ARBITRARY formula from [cgFormula G]
    using ex falso, with the sub-proof of ⊥ as the main cost? -/
theorem ex_falso_derivation_exists
    (G : CubeGraph)
    (ψ : GapFormula G)
    -- If we have ANY proof of ⊥:
    (d_bot : ExtFDeriv G [cgFormula G] .bot)
    -- Then: we can derive ANY formula ψ.
    : ∃ (d : ExtFDeriv G [cgFormula G] ψ), d.leaves = d_bot.leaves + 1 := by
  -- Derive (⊥ → ψ) from Frege axioms, then MP with d_bot.
  -- (⊥ → ψ) is a tautology: (.bot.impl ψ).
  -- In ExtFregeAxiom: we need (.bot.impl ψ) as an axiom or derivable.
  -- From Contra: (¬φ → (φ → ψ)). With φ = .bot:
  -- (¬.bot → (.bot → ψ)). ¬.bot = .bot.impl .bot = tautology.
  -- Then: MP with ¬.bot gives (.bot → ψ). MP with d_bot gives ψ.
  -- Total: d_bot.leaves + 2 axiom leaves + 2 MP = d_bot.leaves + 2.
  -- Actually: let me check if (.bot.impl ψ) is directly an axiom.
  sorry -- construction of ex falso derivation

/-- The XOR counterexample: if ex_falso gives O(D) derivation,
    does the resulting proof of ⊥ have huniv with O(D) leaves?

    d = mp d1 d2 where:
    - d2 derives XOR from cgFormula (via ex_falso + sub_proof)
    - d1 derives (XOR → ⊥) from cgFormula (via ex_falso + sub_proof')
    - sub_proof, sub_proof' : proofs of ⊥ from cgFormula

    d.leaves = d1.leaves + d2.leaves = (sub1.leaves + c) + (sub2.leaves + c)

    huniv: ∀ i σ, flip changes botLeafIdx.
    At root: XOR antecedent. Flip always changes XOR (parity).
    → different direction → different leaf. huniv ✓.

    BUT: does this actually TYPE-CHECK in ExtFDeriv?

    d1 : ExtFDeriv G [cgFormula G] (XOR.impl .bot)
    d2 : ExtFDeriv G [cgFormula G] XOR
    mp d1 d2 : ExtFDeriv G [cgFormula G] .bot ✓

    d1 derives (XOR → ⊥). This requires:
    1. A sub-proof of ⊥ from [cgFormula G].
    2. From ⊥: derive (XOR → ⊥) via ex falso.
    Ex falso gives ANY formula, including (XOR → ⊥).

    d2 derives XOR. Same: sub-proof of ⊥, then ex falso.

    So: d = mp (ex_falso_to (XOR → ⊥) sub1) (ex_falso_to XOR sub2)
    where sub1, sub2 : ExtFDeriv G [cgFormula G] .bot.

    d.leaves = sub1.leaves + sub2.leaves + constants.

    If sub1.leaves = sub2.leaves = D: d.leaves = 2D + c. LINEAR.

    QUESTION: is this a VALID ExtFDeriv? Let's check in Lean. -/

-- Try to construct the counterexample:
-- We need XOR as a GapFormula. XOR of D variables.
-- For simplicity: just check if we can derive .bot → .bot (trivially).

/-- (.bot → .bot) is derivable as a Frege axiom (K axiom instance). -/
example : ExtFregeAxiom G (.bot.impl .bot) :=
  -- K axiom: φ → (ψ → φ). With φ = .bot, ψ = .bot: .bot → (.bot → .bot).
  -- Hmm, that gives .bot → (.bot → .bot), not .bot → .bot.
  -- S axiom + K gives .bot → .bot? Let's try.
  sorry -- need to check if (.bot → .bot) is a direct axiom

/-! ## WHERE IS THE ERROR?

  The counterexample constructs d with XOR at root.
  d has huniv (XOR always changes on flip) with O(D) leaves.

  Adrian says this is WRONG. Let's check each step:

  1. Can d2 derive XOR from [cgFormula G]? YES (ex falso).
  2. Can d1 derive (XOR → ⊥) from [cgFormula G]? YES (ex falso).
  3. Does mp d1 d2 give .bot? YES (by MP).
  4. Does d have huniv? YES (XOR is universally sensitive).
  5. Is d.leaves = O(D)? It's sub1.leaves + sub2.leaves + constants.
     sub1, sub2 are proofs of ⊥ from [cgFormula G].
     sub1.leaves ≥ D (from faxCount). sub2.leaves ≥ D.
     Total: ≥ 2D. LINEAR.

  THE POTENTIAL ERROR: sub1 and sub2 might need EXPONENTIAL leaves.
  They are proofs of ⊥ from cgFormula. If ALL such proofs are exponential:
  sub1.leaves ≥ 2^{D/4}. d.leaves ≥ 2^{D/4}. The counterexample FAILS.

  But: we're TRYING TO PROVE all such proofs are exponential.
  So: if the counterexample is valid: the theorem is false.
  If the counterexample is invalid (sub-proofs must be exponential): the
  theorem is true (by structural induction: sub-proofs smaller → IH applies).

  THE QUESTION: is there a proof of ⊥ from cgFormula with O(D) leaves?

  From faxCount: leaves ≥ D (LINEAR). Is D achievable?
  A caterpillar proof: check cubes one by one. D checks. D+1 leaves.
  Does the caterpillar derive ⊥? It needs ALL constraints to fail.
  For CG-UNSAT: every σ has a defect. The caterpillar finds it.

  So: YES, a caterpillar proof of ⊥ exists with D+1 leaves.

  And: the caterpillar does NOT have huniv (as we showed).
  But: sub1 and sub2 are INSIDE d, which DOES have huniv.
  sub1 and sub2 don't NEED huniv. They just derive ⊥. Any proof works.

  CONCLUSION: the counterexample appears valid.
  d = XOR at root, with caterpillar sub-proofs. D+2 leaves. huniv ✓.

  UNLESS: the caterpillar sub-proofs CAN'T be embedded in d because
  the tree structure of d constrains the sub-proofs' leaves to be
  part of d's leaves, and d's huniv constrains which leaves exist.

  This is the KEY: d's huniv constrains the GLOBAL leaf structure.
  The sub-proofs' leaves are PART of d's leaves. The huniv on d says:
  for EACH σ, d.botLeafIdx(σ) ≠ d.botLeafIdx(flip(i,σ)).
  d.botLeafIdx maps to d.leaves = d1.leaves + d2.leaves.
  The mapping is FIXED by d's tree structure.

  For XOR at root: σ with even parity → right (d2). Odd → left (d1).
  All even-parity σ's map to d2's leaves.
  d2.leaves = 1 + sub2.leaves (from ex falso structure).
  All even-parity σ's map to sub2's leaves (through d2's internal path).
  sub2 is a caterpillar: σ's map to sub2's D+1 leaves.

  d.botLeafIdx for even σ: d1.leaves + (1 + sub2.botLeafIdx(σ)).
  d.botLeafIdx for odd σ: d1.botLeafIdx(σ).

  huniv: flip(i,σ) changes parity → even↔odd → different range. ✓

  d.leaves = d1.leaves + 1 + sub2.leaves = O(D). huniv ✓.

  THE COUNTEREXAMPLE IS VALID.
  The theorem "huniv → 2^{D/4}" IS FALSE without additional hypotheses.
-/

end CubeGraph
