/-
  CubeGraph/IndependentDerivation.lean — Non-Factorizability of Monodromy

  Session: 044. Docs: experiments-ml/044_2026-03-30_craig-locality/IRREDUCIBLE-AXIOMS.md

  Core insight (Adrian, session 044):
    Axioms are "primes" — irreducible, with unique compositions.
    Collisions in T₃* + non-invertibility → re-derivation as only operation.

  What IS proven here:
    - chi_nonlinear: χ(C₁⊕C₂) ≠ χ(C₁) ⊕ χ(C₂) — the monodromy character
      is not a group homomorphism (from SheafOverCycleSpace.lean)
    - result_nonfactorizable: no function f : Bool → Bool → Bool satisfies
      trace(M₁·M₂) = f(trace(M₁), trace(M₂)) for all M₁, M₂

  What is NOT proven (per Opus review):
    Non-factorizability of RESULTS ≠ non-factorizability of COMPUTATIONS.
    A Frege proof for monodromy(C₁⊕C₂) CAN reuse sub-proofs for
    monodromy(C₁) and monodromy(C₂) as intermediate steps, then combine
    them non-linearly. The proof reuses COMPUTATION STEPS even though
    the RESULTS don't compose linearly.

    The gap: showing that computation steps are non-reusable requires
    a proof complexity argument — which is what we're trying to prove.
    This is circular (identified by Opus, session 044).

  Session docs:
  - experiments-ml/044_2026-03-30_craig-locality/FINAL-ARGUMENT.md
  - experiments-ml/045_2026-04-01_rise-fall-breakthrough/STATUS.md
-/

import CubeGraph.Basic
import CubeGraph.BoolMat
import CubeGraph.ChannelAlignment

namespace CubeGraph

/-! ## Section 1: Non-Factorizability of Monodromy Results -/

/-- The monodromy character χ is non-linear: there exist matrices M₁, M₂
    with trace(M₁) = true and trace(M₂) = true but trace(M₁·M₂) = false.

    This is from SheafOverCycleSpace.lean (char_true_not_sufficient).
    Reproven here self-contained from the concrete proj00/proj11 witness. -/
theorem chi_nonlinear :
    ∃ (M₁ M₂ : BoolMat 2),
      BoolMat.trace M₁ = true ∧ BoolMat.trace M₂ = true ∧
      BoolMat.trace (BoolMat.mul M₁ M₂) = false := by
  -- proj00 and proj11: diagonal projections with disjoint support
  let M₁ : BoolMat 2 := fun i j => decide (i = ⟨0, by omega⟩ ∧ j = ⟨0, by omega⟩)
  let M₂ : BoolMat 2 := fun i j => decide (i = ⟨1, by omega⟩ ∧ j = ⟨1, by omega⟩)
  exact ⟨M₁, M₂, by native_decide, by native_decide, by native_decide⟩

/-- **RESULT NON-FACTORIZABILITY**: No function f : Bool → Bool → Bool
    can predict trace(M₁·M₂) from trace(M₁) and trace(M₂) alone.

    Proof: f(true, true) must equal both true (from Id·Id) and false
    (from proj00·proj11). Contradiction.

    This means: knowing the RESULTS of two monodromy computations
    does not determine the result of the composed computation.
    New information appears in the composition. -/
theorem result_nonfactorizable :
    ¬ ∃ (f : Bool → Bool → Bool),
      ∀ (M₁ M₂ : BoolMat 2),
        BoolMat.trace (BoolMat.mul M₁ M₂) = f (BoolMat.trace M₁) (BoolMat.trace M₂) := by
  intro ⟨f, hf⟩
  -- Case 1: Id · Id → trace(Id) = true → f(true, true) = true
  have hone : BoolMat.trace (BoolMat.one : BoolMat 2) = true := by native_decide
  have h1 : f true true = true := by
    have := hf BoolMat.one BoolMat.one
    simp only [BoolMat.one_mul] at this
    rw [hone] at this; exact this.symm
  -- Case 2: proj00 · proj11 → trace = false → f(true, true) = false
  obtain ⟨M₁, M₂, ht1, ht2, hprod⟩ := chi_nonlinear
  have h2 : f true true = false := by
    have := hf M₁ M₂; rw [ht1, ht2] at this; rw [hprod] at this; exact this.symm
  -- Contradiction
  exact absurd h1 (by rw [h2]; decide)

/-! ## Section 2: The Computation Gap (OPEN — per Opus review) -/

/-- **THE COMPUTATION GAP** — what remains open.

    result_nonfactorizable shows: trace(M₁·M₂) ≠ f(trace(M₁), trace(M₂)).
    The RESULTS of separate computations don't determine the composed result.

    But this does NOT show: the COMPUTATION of monodromy(C₁⊕C₂) can't
    REUSE steps from computations of monodromy(C₁) and monodromy(C₂).

    A Frege proof for monodromy(C₁⊕C₂) could:
    1. Compute monodromy(C₁) as an intermediate step
    2. Compute monodromy(C₂) as an intermediate step
    3. Combine them non-linearly (using the specific axioms on C₁ △ C₂)
    4. Steps 1-2 are SHARED with the proofs for C₁ and C₂ individually

    The reuse of steps 1-2 is valid even though χ is non-linear.
    Non-linearity blocks RESULT compression, not STEP reuse.

    To close this gap: must show that step 3 introduces enough NEW work
    per composed cycle that the total across 2^d compositions is exponential.
    This requires a proof complexity argument — not just algebra.

    This gap is IDENTIFIED but OPEN. It is the last remaining piece
    before the full Frege lower bound on CG-UNSAT. -/
axiom computation_nonfactorizable :
    -- Placeholder: the step from result non-factorizability to
    -- computation non-factorizability. This is the last gap.
    -- If proven: Frege lower bound follows.
    -- If false: P = NP (Frege can compress via step reuse).
    True

end CubeGraph
