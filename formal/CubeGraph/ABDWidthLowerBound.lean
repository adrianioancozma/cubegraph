/-
  CubeGraph/ABDWidthLowerBound.lean
  ABD+AD Theorem: k-consistency implies Resolution width > k.

  The Atserias-Bulatov-Dalmau / Atserias-Dalmau result connecting
  Sherali-Adams (= k-consistency) to Resolution width.

  Result: KConsistent G k ∧ ¬Satisfiable G → minResWidth G > k.

  References:
  - Atserias, Bulatov, Dalmau. "Robust decidability of CSP." ICALP 2007.
  - Atserias, Dalmau. "A combinatorial characterization of Resolution width."
    JCSS 74(3):384-414, 2008. Theorem 3.1.

  Proof idea (AD 2008, Theorem 3.1):
  A k-consistent CSP instance defines a "k-evaluation" — a function that
  consistently assigns truth values to any set of ≤ k variables. If a
  Resolution refutation has width ≤ k, then every clause mentions ≤ k
  variables, so every clause is satisfiable under the k-evaluation.
  Resolution steps preserve satisfiability under k-evaluation (both premises
  satisfied → resolvent satisfied). By induction, all derived clauses of
  width ≤ k are satisfied. But the empty clause (width 0) cannot be
  satisfied → contradiction. Therefore no width-≤-k refutation exists.

  We state this as an axiom (published, well-established result).

  See: KConsistency.lean (KConsistent definition)
  See: SchoenebeckChain.lean (schoenebeck_linear axiom)
  See: ERLowerBound.lean (uses this + BSW for size bounds)
-/

import CubeGraph.KConsistency
import CubeGraph.SchoenebeckChain

namespace CubeGraph

/-! ## Section 1: Minimum Resolution refutation width (axiom-specified) -/

/-- Minimum Resolution refutation width for an UNSAT CubeGraph.

    For UNSAT G: the minimum width (= max number of literals in any clause)
    across all Resolution refutations of the CNF formula associated with G.

    For SAT G: unconstrained (axioms only apply to UNSAT).

    We do not model Resolution proofs directly. This function is specified
    by axioms corresponding to published results. -/
axiom minResWidth (G : CubeGraph) : Nat

/-! ## Section 2: ABD+AD Theorem -/

/-- **Atserias-Bulatov-Dalmau (2007) / Atserias-Dalmau (2008)**:
    k-consistency on an UNSAT CubeGraph implies that every Resolution
    refutation has width strictly greater than k.

    Formally: KConsistent G k ∧ ¬Satisfiable G → minResWidth G > k.

    This is the game-theoretic argument from AD 2008, Theorem 3.1:
    k-consistency provides a "Duplicator strategy" that satisfies every
    clause of width ≤ k, and this property is preserved under Resolution
    steps. Since the empty clause cannot be satisfied, no refutation of
    width ≤ k can exist.

    References:
    [ABD07] Atserias, Bulatov, Dalmau. "Robust decidability of CSP."
            ICALP 2007, LNCS 4596, pp. 128-139.
    [AD08]  Atserias, Dalmau. "A combinatorial characterization of
            Resolution width." JCSS 74(3):384-414, 2008. -/
axiom abd_width_from_kconsistency :
    ∀ (G : CubeGraph) (k : Nat),
      KConsistent G k → ¬ G.Satisfiable →
      minResWidth G > k

/-! ## Section 3: Corollaries -/

/-- Contrapositive form: if a Resolution refutation of width ≤ k exists,
    then G is NOT k-consistent. -/
theorem low_width_refutation_breaks_consistency
    (G : CubeGraph) (k : Nat)
    (hunsat : ¬ G.Satisfiable)
    (hwidth : minResWidth G ≤ k) :
    ¬ KConsistent G k := by
  intro hkc
  have h := abd_width_from_kconsistency G k hkc hunsat
  omega

/-- Combined with Schoenebeck: there exist arbitrarily large UNSAT formulas
    where Resolution refutation width is Ω(n).

    From schoenebeck_linear: ∃ c₁ ≥ 2, ∀ n ≥ 1, ∃ G with |G| ≥ n,
      KConsistent G (n/c₁) ∧ ¬Satisfiable G.
    From abd_width_from_kconsistency: minResWidth G > n/c₁.
    Therefore: minResWidth G > n/c₁ = Ω(n). -/
theorem abd_gives_linear_width :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minResWidth G > n / c := by
  obtain ⟨c, hc, hsch⟩ := schoenebeck_linear
  exact ⟨c, hc, fun n hn => by
    obtain ⟨G, hsize, hkc, hunsat⟩ := hsch n hn
    exact ⟨G, hsize, hunsat, abd_width_from_kconsistency G (n / c) hkc hunsat⟩⟩

/-! ## Section 4: What this establishes

    abd_width_from_kconsistency is the FIRST step in the proof complexity chain:
    1. KConsistent G k + UNSAT → Resolution width > k          [this file, ABD+AD]
    2. Resolution width w → size ≥ 2^{(w-3)²/n}               [BSW 2001, ERLowerBound.lean]
    3. Combining: KConsistent G (n/c) + UNSAT → size ≥ 2^{Ω(n)} [ERLowerBound.lean]

    This file factors out step (1) cleanly from the combined ABD+BSW axiom
    in ERLowerBound.lean. -/

end CubeGraph
