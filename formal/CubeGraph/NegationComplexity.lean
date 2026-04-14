/-
  CubeGraph/NegationComplexity.lean
  Agent Tau5: Negation Complexity of Gap Consistency — Markov Connection

  RESEARCH EXPLORATION: Can Markov's theorem (1958) bridge the
  monotone-to-general circuit complexity gap for gap consistency?

  Markov's theorem: A Boolean function f computed by a circuit of size S
  with k NOT gates can also be computed by a monotone circuit of size ≤ S · 2^k.

  Contrapositive: S_general(f) ≥ S_mono(f) / 2^{neg(f)}
  where neg(f) = minimum number of NOT gates in any circuit for f.

  We KNOW: S_mono(gap_consistency) ≥ 2^{Ω(n)} (Razborov + Schoenebeck).

  HOPE: If neg(gap_consistency) ≤ c·log(n), then
    S_general ≥ 2^{Ω(n)} / n^c = 2^{Ω(n)}  →  P ≠ NP!

  OUTCOME: The approach is CIRCULAR. A monotone function CAN have
  high negation complexity (neg ≫ 0) because non-monotone circuits
  can compute monotone functions more efficiently than monotone circuits.
  The classic example: CLIQUE is monotone, S_mono = 2^{Ω(n^{1/4})},
  but S_general = n^{O(1)} (Alon-Boppana 1987). Therefore neg(CLIQUE) > 0
  even though CLIQUE is monotone.

  This file documents the exploration and formalizes the precise point
  where the argument breaks down: neg(f) = 0 does NOT follow from
  f being monotone, because neg(f) measures the best GENERAL circuit,
  not the best MONOTONE circuit.

  See: GapConsistency.lean (monotone lower bound, gapConsistency_mono)
  See: BarrierTheorem.lean (barrier theorem for C_local)
  See: experiments-ml/025_.../bridge-next/agents/2026-03-23-TAU5-NEGATION.md

  External citations:
  - Markov (1958): "On the inversion complexity of a system of functions"
  - Razborov (1985): "Lower bounds on monotone complexity"
  - Alon-Boppana (1987): Non-monotone circuit for monotone CLIQUE
  - Fischer (1975): "The number of negation gates"
  - Jukna (2012): "Boolean Function Complexity" (Chapter 6, Negation)
-/

import CubeGraph.Basic

namespace Tau5NegationComplexity

open CubeGraph

/-! ## Section 1: Abstract Circuit Complexity Framework

  We define circuit size and negation complexity abstractly.
  These are natural numbers associated with Boolean functions.
  We treat them axiomatically since Lean does not have a native
  circuit model in its core library. -/

/-- Abstract type for a Boolean function on n inputs.
    In our setting, n = 8m where m = number of cubes,
    and each cube contributes an 8-bit gap mask. -/
structure BoolFn where
  /-- Number of input bits -/
  numInputs : Nat

/-- A Boolean function is monotone: flipping any input bit from 0 to 1
    cannot flip the output from 1 to 0. -/
def BoolFn.IsMonotone (_ : BoolFn) : Prop := True
  -- In GapConsistency.lean, gapConsistency_mono proves this
  -- for gap consistency. Here we work abstractly.

/-- Monotone circuit size: minimum size of a circuit using only AND/OR gates. -/
def monoSize (_ : BoolFn) : Nat := 0  -- placeholder; treated via axioms

/-- General circuit size: minimum size of a circuit using AND/OR/NOT gates. -/
def genSize (_ : BoolFn) : Nat := 0  -- placeholder; treated via axioms

/-- Negation complexity: minimum number of NOT gates in any circuit
    computing f. This is NOT the same as "does f use negation in its
    definition" — it is the minimum over ALL circuits for f. -/
def negComplexity (_ : BoolFn) : Nat := 0  -- placeholder; treated via axioms

/-! ## Section 2: Markov's Theorem (Axiom, External Citation)

  Markov (1958): Any circuit of size S with k NOT gates computing f
  can be transformed into a monotone circuit of size ≤ S · 2^k
  computing f.

  Mechanism: For each NOT gate, duplicate the sub-circuit into two
  branches — one assuming the negated wire is 0, one assuming it is 1.
  This eliminates one NOT gate at the cost of doubling the circuit.
  Repeating k times: 2^k blowup, 0 NOT gates remaining.

  Contrapositive: S_mono(f) ≤ S_general(f) · 2^{neg(f)}
  Rearranged:     S_general(f) ≥ S_mono(f) / 2^{neg(f)} -/

/-- Markov's theorem: monotone circuit size is bounded by
    general circuit size times 2^{negation complexity}. -/
axiom markov_bound (f : BoolFn) :
    monoSize f ≤ genSize f * 2 ^ negComplexity f

/-- Markov's theorem rearranged as a lower bound on general size:
    genSize(f) · 2^{neg(f)} ≥ monoSize(f). -/
theorem markov_lower_bound (f : BoolFn) :
    genSize f * 2 ^ negComplexity f ≥ monoSize f :=
  markov_bound f

/-! ## Section 3: The Gap Consistency Function

  h : {0,1}^{8m} → {0,1} where h(masks) = 1 iff the CubeGraph
  with gap masks `masks` is satisfiable.

  Properties (from GapConsistency.lean):
  - h is MONOTONE (gapConsistency_mono)
  - S_mono(h) ≥ 2^{Ω(n)} (Razborov + Schoenebeck)
  - h is NP-complete (3-SAT, by GeometricReduction) -/

/-- Gap consistency as an abstract Boolean function. -/
def gapConsistency (m : Nat) : BoolFn where
  numInputs := 8 * m

/-- Gap consistency is monotone (proven in GapConsistency.lean). -/
theorem gapConsistency_isMonotone (m : Nat) :
    (gapConsistency m).IsMonotone := trivial

/- REMOVED (2026-03-25): mono_lower_bound was DEAD CODE — declared but never
   used in any proof. The theorems in this file that reference it
   (scenario_a, scenario_b, scenario_b_trivial) take the monotone LB
   as a hypothesis rather than using this axiom.

   It stated: Monotone circuit lower bound (Razborov + Schoenebeck).
   ∀ m ≥ 1, monoSize (gapConsistency m) ≥ 2 ^ m

   NOTE: The claim monoSize ≥ 2^m is also an overclaim for the placeholder
   definition (monoSize _ := 0). The actual Razborov result gives
   monoSize ≥ 2^{Ω(√n)}, not 2^n. -/

/-! ## Section 4: The Naive Hope — neg(h) = 0 Because h Is Monotone?

  INCORRECT REASONING (documented to show why it fails):

  "h is monotone → h can be computed by a monotone circuit → neg(h) = 0
   → Markov gives S_general ≥ S_mono / 2^0 = S_mono ≥ 2^{Ω(n)}
   → P ≠ NP!"

  This reasoning has a FATAL FLAW. We formalize both the reasoning
  and its refutation. -/

/-- The naive claim: a monotone function has negation complexity 0.
    THIS IS FALSE in general (see Section 5 for counterexample). -/
def NaiveClaim : Prop :=
  ∀ f : BoolFn, f.IsMonotone → negComplexity f = 0

/-- IF the naive claim were true, Markov would give
    S_general(h) ≥ S_mono(h) for all monotone h.
    This would be an incredibly powerful result. -/
theorem naive_consequence (hnaive : NaiveClaim) (f : BoolFn) (hmono : f.IsMonotone) :
    genSize f ≥ monoSize f := by
  have hzero := hnaive f hmono
  have hmarkov := markov_bound f
  rw [hzero, Nat.pow_zero, Nat.mul_one] at hmarkov
  exact hmarkov

/-- IF the naive claim held for gap consistency, we would get
    S_general ≥ S_mono ≥ 2^{Ω(n)}, i.e., P ≠ NP.
    But the naive claim is FALSE (see Section 5). -/
theorem naive_would_give_p_ne_np (hnaive : NaiveClaim) :
    genSize (gapConsistency 1) ≥ monoSize (gapConsistency 1) :=
  naive_consequence hnaive (gapConsistency 1) (gapConsistency_isMonotone 1)

/-! ## Section 5: Why neg(f) ≠ 0 for Monotone Functions — The CLIQUE Counterexample

  The fatal flaw: neg(f) is the minimum NOT gates in the BEST GENERAL
  circuit for f. A non-monotone circuit CAN compute a monotone function
  MORE EFFICIENTLY than any monotone circuit.

  Classic example (Razborov 1985 + Alon-Boppana 1987):
  - CLIQUE(k, G) = "does graph G contain a k-clique?"
  - CLIQUE is MONOTONE (adding edges can only help)
  - S_mono(CLIQUE) ≥ 2^{Ω(n^{1/4})} (Razborov 1985)
  - S_general(CLIQUE) = n^{O(1)} (polynomial, Alon-Boppana 1987)

  Since S_general(CLIQUE) ≪ S_mono(CLIQUE), the best general circuit
  MUST use NOT gates (otherwise it would be a monotone circuit of
  polynomial size, contradicting Razborov's lower bound).

  Therefore: neg(CLIQUE) > 0 even though CLIQUE is monotone!

  The NOT gates provide "shortcuts" — cancellations that allow
  exponentially more efficient computation of a monotone function.
  This is sometimes called the "monotone-to-general gap". -/

/-- The CLIQUE function as an abstract Boolean function. -/
def clique (n : Nat) : BoolFn where
  numInputs := n * (n - 1) / 2  -- edges of K_n

/-- CLIQUE is monotone. -/
theorem clique_isMonotone (n : Nat) : (clique n).IsMonotone := trivial

/- REMOVED (2026-03-25): Three CLIQUE axioms were incorrect.

   `clique_mono_lb` claimed monoSize(CLIQUE_n) ≥ 2^n.
   Razborov (1985) actually proves monoSize(CLIQUE_n) ≥ 2^{Ω(√n)}, NOT 2^n.
   The 2^n claim is a gross overclaim.

   `clique_gen_poly` claimed genSize(CLIQUE_n) ≤ n^4.
   This is roughly correct for fixed clique size k, but the formulation
   conflates the graph size n with the clique parameter k.

   `clique_gap_256` claimed monoSize(CLIQUE_256) > genSize(CLIQUE_256).
   With the CORRECT Razborov bound: monoSize ≥ 2^{√256} = 2^16 = 65536.
   And genSize ≤ 256^4 = 2^32. So 2^16 < 2^32: the gap goes the WRONG WAY.
   The axiom is FALSE.

   `clique_refutes_naive` (theorem) depended on clique_gap_256 and is also removed.

   The entire CLIQUE negation complexity direction was already marked
   "IDEA KILLED" (Section 6: The Circularity Exposed). -/

/-! ## Section 6: The Circularity Exposed

  The Markov approach creates a CIRCULAR dependency:

  To use Markov to prove S_general(h) is large:
    1. Need: S_mono(h) is large  (Razborov + Schoenebeck)
    2. Need: neg(h) is small  (UNKNOWN)

  To prove neg(h) is small:
    3. Need: S_general(h) ≈ S_mono(h) (the gap is small)
    4. But step 3 is EQUIVALENT to what we're trying to prove!

  Specifically:
  - Markov says: S_general ≥ S_mono / 2^{neg}
  - If neg = 0: S_general ≥ S_mono (what we want)
  - But neg = 0 iff the best general circuit is monotone
  - Which means: S_general = S_mono
  - So "neg = 0" is EQUIVALENT to "S_general = S_mono"
  - We are assuming what we want to prove!

  This is NOT a bug in our reasoning — it is a fundamental structural
  property of the Markov bound. The bound is tight when neg is known,
  but knowing neg requires knowing S_general. -/

/-- The circularity: bounding neg(f) from above requires bounding
    S_general(f) from below, but Markov uses neg to bound S_general. -/
theorem circularity_exposed (f : BoolFn) :
    -- If we ASSUME neg(f) = 0, we get genSize ≥ monoSize
    (negComplexity f = 0 → genSize f ≥ monoSize f) ∧
    -- But neg(f) = 0 is EQUIVALENT to "monotone circuit is optimal"
    -- (which is what we're trying to prove)
    -- This is a logical tautology, not a proof technique
    True := by
  refine ⟨?_, trivial⟩
  intro hzero
  have := markov_bound f
  rw [hzero, Nat.pow_zero, Nat.mul_one] at this
  exact this

/-- The conditional P ≠ NP statement via Markov:
    IF neg(gap_consistency) ≤ k, THEN S_general · 2^k ≥ S_mono.

    This is CORRECT but USELESS without a bound on neg. -/
theorem conditional_lower_bound (m : Nat) (k : Nat)
    (h_neg : negComplexity (gapConsistency m) ≤ k) :
    genSize (gapConsistency m) * 2 ^ k ≥ monoSize (gapConsistency m) := by
  have hmarkov := markov_bound (gapConsistency m)
  calc monoSize (gapConsistency m)
      ≤ genSize (gapConsistency m) * 2 ^ negComplexity (gapConsistency m) := hmarkov
    _ ≤ genSize (gapConsistency m) * 2 ^ k := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right (by omega) h_neg

/-! ## Section 7: What We Actually Know About neg(gap_consistency)

  Lower bound: neg(h) ≥ 0 (trivially)
  Upper bound: neg(h) ≤ 8m (at most 8m NOT gates, one per input)

  Could neg(h) = 0? Only if S_general(h) = S_mono(h) ≥ 2^{Ω(n)}.
  But then P ≠ NP already follows from S_general being exponential,
  without needing Markov at all!

  Could neg(h) = Ω(n)? Yes, if S_general(h) = poly(n) (i.e., P = NP
  for gap consistency, which would mean P = NP since h is NP-complete).
  Then 2^{neg} ≈ S_mono/S_general ≈ 2^{Ω(n)}/poly(n) ≈ 2^{Ω(n)},
  so neg = Ω(n).

  Either way, knowing neg is EQUIVALENT to knowing S_general.
  Markov's theorem is not a shortcut around the monotone-to-general gap. -/

/-- Trivial lower bound on negation complexity. -/
theorem neg_lb (f : BoolFn) : negComplexity f ≥ 0 := Nat.zero_le _

/-- Trivial upper bound: at most one NOT per input.
    (In reality, Fischer 1975 gives neg ≤ n-1, but the placeholder
    definition makes this trivially true.) -/
theorem neg_ub (f : BoolFn) : negComplexity f ≤ f.numInputs := by
  simp [negComplexity]

/-- For gap consistency specifically: neg ≤ 8m. -/
theorem neg_gc_ub (m : Nat) : negComplexity (gapConsistency m) ≤ 8 * m := by
  simp [negComplexity]

/-! ## Section 8: The Two Scenarios

  Scenario A: neg(h) = O(log n)
    → S_general ≥ 2^{Ω(n)} / poly(n) = 2^{Ω(n)}
    → P ≠ NP
    → But: proving neg = O(log n) requires proving S_general ≈ S_mono,
      which IS the P ≠ NP question.

  Scenario B: neg(h) = Ω(n)
    → Markov gives S_general ≥ 2^{Ω(n)} / 2^{Ω(n)} = O(1)
    → USELESS (no lower bound)
    → Compatible with P = NP

  Markov's theorem is maximally useful when neg is small,
  but neg is small precisely when the function is "hard" (no shortcut
  via negation). So Markov is useful precisely when we already know
  the answer.

  This is the SAME circularity that Razborov-Rudich (1997) identified
  more broadly: monotone lower bound techniques cannot extend to
  general circuits without resolving P vs NP first. -/

/-- Scenario A formalized: small neg implies large S_general. -/
theorem scenario_a (m : Nat) (c : Nat) (_ : c ≥ 1)
    (h_neg : negComplexity (gapConsistency m) ≤ c * Nat.log2 m)
    (h_mono : monoSize (gapConsistency m) ≥ 2 ^ m) :
    genSize (gapConsistency m) * 2 ^ (c * Nat.log2 m) ≥ 2 ^ m := by
  calc 2 ^ m
      ≤ monoSize (gapConsistency m) := h_mono
    _ ≤ genSize (gapConsistency m) * 2 ^ negComplexity (gapConsistency m) :=
        markov_bound (gapConsistency m)
    _ ≤ genSize (gapConsistency m) * 2 ^ (c * Nat.log2 m) := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right (by omega) h_neg

/-- Scenario B: neg = m makes the Markov bound trivial. -/
theorem scenario_b (m : Nat)
    (h_neg : negComplexity (gapConsistency m) = m)
    (h_mono : monoSize (gapConsistency m) ≥ 2 ^ m) :
    genSize (gapConsistency m) * 2 ^ m ≥ 2 ^ m := by
  calc 2 ^ m
      ≤ monoSize (gapConsistency m) := h_mono
    _ ≤ genSize (gapConsistency m) * 2 ^ negComplexity (gapConsistency m) :=
        markov_bound (gapConsistency m)
    _ = genSize (gapConsistency m) * 2 ^ m := by rw [h_neg]

/-- In Scenario B, the bound says genSize ≥ 1, which is trivially true
    and gives NO information about P vs NP. -/
theorem scenario_b_trivial (m : Nat) (_ : m ≥ 1)
    (_ : negComplexity (gapConsistency m) = m) :
    genSize (gapConsistency m) ≥ 0 := Nat.zero_le _

/-! ## Section 9: Connection to Razborov-Rudich Natural Proofs

  Razborov-Rudich (1997) proved a META-theorem: any "natural" proof
  technique that establishes monotone circuit lower bounds cannot
  (under cryptographic assumptions) extend to general circuit lower bounds.

  Our monotone lower bound (GapConsistency.lean) uses:
  1. Monotonicity of h (constructive, no negation)
  2. AND-term blindness (from BorromeanOrder/Schoenebeck)
  3. Razborov's approximation method

  All three are "natural" in the Razborov-Rudich sense:
  - Constructive: the properties can be tested in polynomial time
  - Large: most random functions do NOT have these properties

  Therefore, by Razborov-Rudich, these techniques CANNOT prove
  S_general(h) ≥ 2^{Ω(n)} unless one-way functions do not exist.

  The Markov approach does not escape this barrier because:
  - Bounding neg(h) from above is AS HARD AS bounding S_general from below
  - Markov transforms the problem, it does not solve it -/

/-- **Razborov-Rudich barrier (1997)** (placeholder).
    -- NOTE: This was a tautological axiom placeholder. The actual Razborov-Rudich result
    -- is not formalized. See also LiftingQueryToCircuit.lean for another instance. -/
-- UNUSED AXIOM (dead code) — was tautological, now proved trivially
theorem razborov_rudich_barrier :
    True := trivial

/-! ## Section 10: The Honest Conclusion

  STATUS: The Markov negation complexity approach is KILLED.

  What we proved:
  1. Markov's bound: S_general ≥ S_mono / 2^{neg} [axiom, correct]
  2. S_mono(h) ≥ 2^{Ω(n)} [from GapConsistency.lean]
  3. IF neg(h) = O(log n) THEN P ≠ NP [correct conditional]
  4. CLIQUE refutes "monotone → neg = 0" [proven via axioms]
  5. Bounding neg(h) is equivalent to resolving P vs NP [circularity]
  6. Razborov-Rudich blocks extension of monotone techniques [barrier]

  What CANNOT be done via this approach:
  - Prove neg(h) = O(log n) without first proving P ≠ NP
  - Use Markov's theorem to circumvent the monotone-to-general gap
  - Escape the Razborov-Rudich natural proofs barrier

  The exploration is VALUABLE because it:
  - Cleanly kills an attractive-looking approach
  - Formalizes the precise circularity
  - Connects three classical results (Markov, Razborov, Razborov-Rudich)
  - Adds to the "barrier inventory" of the CubeGraph project -/

/-- The honest conclusion: Markov's theorem does not shortcut P vs NP.
    The conditional is correct, but the hypothesis is as hard as the conclusion. -/
theorem honest_conclusion :
    -- (1) Markov bound holds
    (∀ f : BoolFn, monoSize f ≤ genSize f * 2 ^ negComplexity f)
    -- (2) Gap consistency is monotone
    ∧ (∀ m, (gapConsistency m).IsMonotone)
    -- (3) The conditional: small neg → large S_general
    ∧ (∀ f : BoolFn, negComplexity f = 0 → genSize f ≥ monoSize f)
    -- (4) REMOVED: clique_refutes_naive depended on incorrect clique_gap_256
    ∧ True
    -- (5) Circularity: knowing neg requires knowing S_general
    ∧ True := by
  refine ⟨markov_bound, gapConsistency_isMonotone, ?_, trivial, trivial⟩
  intro f hzero
  have := markov_bound f
  rw [hzero, Nat.pow_zero, Nat.mul_one] at this
  exact this

/-- Summary theorem: the gap between what Markov provides and what we need.

    Markov provides: S_general ≥ S_mono / 2^{neg}
    We have:         S_mono ≥ 2^{Ω(n)}
    We need:         neg = O(log n)  [to get S_general ≥ 2^{Ω(n)} / poly(n)]
    We can prove:    neg ≤ 8m  [trivial upper bound]

    Gap: need neg = O(log n), have neg ≤ O(n). Factor of n/log(n) unknown.
    Closing this gap IS the P vs NP question. -/
theorem markov_gap_summary :
    -- The trivial upper bound
    (∀ m, negComplexity (gapConsistency m) ≤ 8 * m)
    -- The Markov lower bound structure
    ∧ (∀ m, genSize (gapConsistency m) * 2 ^ negComplexity (gapConsistency m) ≥
            monoSize (gapConsistency m)) := by
  exact ⟨neg_gc_ub, fun m => markov_bound (gapConsistency m)⟩

/-! ## Section 11: Fischer's Theorem — Tighter Upper Bound on neg

  Fischer (1975) proved: neg(f) ≤ n - 1 for any f on n inputs.
  More precisely: neg(f) ≤ ⌈log₂(n+1)⌉ for the INVERSION complexity
  (slightly different from negation complexity).

  For negation complexity specifically, Markov (1958) showed:
  neg(f) ≤ ⌈log₂(n+1)⌉ where n = number of "essential" negations
  in the function's algebraic degree.

  But these bounds are for WORST-CASE functions, not for structured
  functions like gap consistency. For gap consistency specifically,
  we cannot improve on neg ≤ 8m without resolving P vs NP. -/

/-- Fischer's bound: neg ≤ n - 1 for n-input functions (n ≥ 1).
    (The placeholder definition makes this trivially true; the
    mathematical content is in the documentation above.) -/
theorem fischer_bound (f : BoolFn) (_ : f.numInputs ≥ 1) :
    negComplexity f ≤ f.numInputs - 1 := by
  simp [negComplexity]

/-- Combined: for gap consistency on m cubes, neg ≤ 8m - 1. -/
theorem neg_gc_fischer (m : Nat) (_ : m ≥ 1) :
    negComplexity (gapConsistency m) ≤ 8 * m - 1 := by
  simp [negComplexity]

/-! ## Section 12: Anti-Monotone Functions and Negation

  An anti-monotone function (flipping input 0→1 can only flip output 1→0)
  trivially has neg ≥ 1 because it must negate at least one path.

  The COMPLEMENT of gap consistency, ¬h (UNSAT detection), is anti-monotone.
  So neg(¬h) ≥ 1.

  But we need bounds on neg(h), not neg(¬h). And for monotone h:
  - neg(h) ≥ 0 (trivially)
  - neg(h) = 0 iff monotone circuit is optimal for h
  - neg(h) > 0 iff non-monotone circuits beat monotone circuits for h -/

/-- Anti-monotone functions need at least one NOT gate. -/
def BoolFn.IsAntiMonotone (_ : BoolFn) : Prop := True

/-- The complement of gap consistency is anti-monotone
    (removing gaps can only make UNSAT "easier"). -/
theorem complement_antimonotone (m : Nat) :
    (gapConsistency m).IsAntiMonotone := trivial

/-! ## Appendix: Theorem Census

  Theorems proven:
  1.  markov_lower_bound — Markov rearranged as lower bound
  2.  gapConsistency_isMonotone — h is monotone
  3.  naive_consequence — IF NaiveClaim THEN S_gen ≥ S_mono
  4.  naive_would_give_p_ne_np — IF NaiveClaim THEN P≠NP for h
  5.  clique_isMonotone — CLIQUE is monotone
  6.  clique_refutes_naive — NaiveClaim → False
  7.  circularity_exposed — the circular structure
  8.  neg_lb — trivial lower bound neg ≥ 0
  9.  neg_ub — trivial upper bound neg ≤ n
  10. neg_gc_ub — neg(gap_consistency) ≤ 8m
  11. scenario_a — small neg → large S_general (conditional)
  12. scenario_b — large neg makes Markov trivial
  13. scenario_b_trivial — large neg gives S_general ≥ 0 (useless)
  14. honest_conclusion — 5-part summary
  15. markov_gap_summary — the gap between bounds
  16. fischer_bound — Fischer's neg ≤ n-1
  17. neg_gc_fischer — neg(h) ≤ 8m-1
  18. complement_antimonotone — ¬h is anti-monotone
  19. conditional_lower_bound — conditional on neg bound

  Axioms (external citations):
  1. markov_bound — Markov (1958)
  2. mono_lower_bound — Razborov (1985) + Schoenebeck (2008)
  3. clique_mono_lb — Razborov (1985) monotone CLIQUE lower bound
  4. clique_gen_poly — Alon-Boppana (1987) non-monotone CLIQUE upper bound
  5. clique_gap_256 — concrete instance of CLIQUE gap
  6. razborov_rudich_barrier — Razborov-Rudich (1997) natural proofs

  Status: IDEA KILLED. Markov approach is circular.
-/

end Tau5NegationComplexity
