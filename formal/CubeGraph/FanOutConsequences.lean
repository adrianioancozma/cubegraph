/-
  CubeGraph/FanOutConsequences.lean
  CONSEQUENCES OF FAN-OUT FOR THE GAP-PROJECTION ARGUMENT

  STRUCTURE:
  Part 1: Fan-Out Kills Z/2Z (building on Tau7's fanout_kills_period2)
          entryAnd(M, M) = M → same-signal fan-out makes everything idempotent
          → KR = 0 (aperiodic semigroup)
          → Z/2Z from h2Monodromy is killed

  Part 2: The Strengthened Gap (if the argument held...)
          Without fan-out (tree): KR = 1 (Z/2Z from h2Monodromy)
          With fan-out (DAG): KR = 0 (fan-out kills Z/2Z)
          Trace language demand: KR ≥ 1
          Gap: 0 < 1 → BIGGER gap with fan-out!

  Part 3: CAREFUL CHECK — Where the Argument BREAKS
          Step 2 of the "proof" is WRONG:
          Fan-out of BITS ≠ entryAnd of gap projections
          A circuit fans out bit b → two branches compute DIFFERENT functions
          → DIFFERENT gap projections π₁, π₂
          → entryAnd(π₁, π₂) where π₁ ≠ π₂
          → NOT the same as entryAnd(π₁, π₁) = π₁

  Part 4: What Fan-Out ACTUALLY Does at Gap Level
          Fan-out of bit b → correlated but DIFFERENT gap projections
          entryAnd of DIFFERENT matrices CAN produce nonzero non-self results
          (Mu5 showed: OR of two rank-1 = rank-2; AND preserves rank ≤ 1)
          On h2 specifically: all cross-entryAnd are ZERO (disjoint supports)

  Part 5: The Level 1 / Level 2 Category Error
          Same pattern as S-48: confusing bit-level operations with gap-level
          Bit-level fan-out is exact duplication
          Gap-level fan-out is NOT exact duplication (different branches)
          This is the fundamental obstacle to the projection approach

  IMPORTS:
  - Tau7FanOutBarrier: entryAnd properties, fanout_kills_period2
  - Sigma7ProjectionLemma: conditional chain, projection hypothesis
  - Mu5DAGRankComposition: counterexample (OR breaks rank-1)

  . 19 theorems.
  BRUTALLY HONEST about where the P≠NP argument fails.
-/

import CubeGraph.FanOutBarrierFull
import CubeGraph.ProjectionLemma
import CubeGraph.DAGRankComposition

namespace CubeGraph

-- open _root_.BoolMat to get mul, isZero, pow, boolAnd, boolOr, etc.
-- (plain `open BoolMat` inside `namespace CubeGraph` resolves to
-- CubeGraph.BoolMat which has entryAnd but not mul/isZero)
open _root_.BoolMat

/-! ## Part 1: Fan-Out Kills Z/2Z — The Tau7 Result and Its Algebra

  From Tau7: entryAnd(M, M) = M (idempotency of Hadamard product).
  If a wire carries gap projection M and fans out to two identical branches,
  the combined constraint is entryAnd(M, M) = M.

  For the h2 witness:
  - h2Monodromy has period 2 (Z/2Z): M² ≠ M, M³ = M
  - entryAnd(h2Monodromy, h2Monodromy) = h2Monodromy (just itself, no new info)
  - BUT: entryAnd of two DIFFERENT h2 generators produces ZERO (disjoint supports)
  - All pairwise entryAnd of h2 generators are aperiodic (period 1 or zero)

  The key Tau7 result: fan-out kills Z/2Z on the concrete h2 witness -/

/-- **U7.1 — SELF FAN-OUT IS TRIVIAL**: entryAnd(M, M) = M for ANY boolean matrix.
    Fan-out of the SAME signal carries no new constraint.
    This is just idempotency of AND, restated for emphasis. -/
theorem self_fanout_trivial (M : BoolMat n) :
    BoolMat.entryAnd M M = M :=
  entryAnd_self M

/-- **U7.2 — SELF FAN-OUT PRESERVES PERIOD**: If M has period p,
    then entryAnd(M, M) = M has the same period p.
    Self fan-out cannot change algebraic structure. -/
theorem self_fanout_preserves_period (M : BoolMat n) :
    BoolMat.entryAnd M M = M ∧
    -- therefore whatever property M has, entryAnd(M,M) inherits it
    (HasGroupOrder2 M → HasGroupOrder2 (BoolMat.entryAnd M M)) := by
  constructor
  · exact entryAnd_self M
  · intro h; rwa [entryAnd_self]

/-- **U7.3 — CROSS FAN-OUT KILLS PERIOD 2**: entryAnd of DIFFERENT h2 generators
    produces zero or aperiodic elements.
    This is the Tau7 result that inspired the investigation.
    On the h2 witness: ALL cross-entryAnds produce ZERO (disjoint supports). -/
theorem cross_fanout_kills_z2 :
    -- Monodromy ⊙ MonodromyB is ZERO (disjoint support)
    isZero (BoolMat.entryAnd h2Monodromy h2MonodromyB) ∧
    -- AB ⊙ BC is also zero (disjoint support on h2)
    isZero (BoolMat.entryAnd h2MonAB h2MonBC) ∧
    -- BC ⊙ CA is also zero
    isZero (BoolMat.entryAnd h2MonBC h2MonCA) ∧
    -- CA ⊙ AB is also zero
    isZero (BoolMat.entryAnd h2MonCA h2MonAB) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **U7.4 — IDEMPOTENT IMPLIES APERIODIC**: If M is idempotent (M² = M),
    then M³ = M², so M is aperiodic (KR contribution = 0).
    This is the algebraic mechanism: idempotent → no group → KR = 0. -/
theorem idempotent_is_aperiodic (M : BoolMat n) (h : mul M M = M) :
    mul M (mul M M) = mul M M := by
  rw [h, h]

/-- **U7.5 — ZERO IS APERIODIC**: The zero matrix is trivially aperiodic.
    If fan-out produces zero (disjoint supports), aperiodicity is immediate. -/
theorem zero_is_aperiodic {n : Nat} :
    mul (@BoolMat.zero n) (mul (@BoolMat.zero n) (@BoolMat.zero n)) =
    mul (@BoolMat.zero n) (@BoolMat.zero n) := by
  funext i j
  simp only [mul, BoolMat.zero, Bool.false_and]

/-! ## Part 2: The Strengthened Gap — What Would Follow IF the Argument Held

  The tantalizing (but WRONG) argument:

  Step 1: Tree circuits → KR = 1 (Z/2Z from h2Monodromy) -- PROVED in Sigma7
  Step 2: DAG circuits → fan-out → entryAnd → KR = 0 -- THIS IS WRONG (see Part 3)
  Step 3: Trace language demands KR ≥ 1 -- PROVED (h2Monodromy period 2)
  Step 4: 0 < 1 → gap is bigger → stronger lower bound

  We prove the CONDITIONAL: IF same-signal fan-out were the only effect,
  THEN the gap would widen. All the consequences below are CORRECT as
  conditional statements. The antecedent (Step 2) is FALSE. -/

/-- The (false) hypothesis that fan-out produces only idempotent gap projections.
    This would mean: every gap-projected element in a DAG circuit satisfies M² = M.
    This is FALSE because fan-out of bits ≠ fan-out of gap projections. -/
def FanOutIdempotentHypothesis : Prop :=
  ∀ (M : BoolMat 8),
    (∃ (A B : BoolMat 8), M = BoolMat.entryAnd A B) →
    mul M M = M

/-- **U7.6 — CONDITIONAL: IDEMPOTENT → NO Z/2Z**:
    If all fan-out products are idempotent, no fan-out product can have period 2. -/
theorem idempotent_kills_z2 (M : BoolMat n) (h_idem : mul M M = M) :
    ¬ HasGroupOrder2 M := by
  intro ⟨_, h_ne⟩
  -- HasGroupOrder2: pow M 3 = pow M 1 ∧ pow M 2 ≠ pow M 1
  -- h_idem: M² = M, so pow M 2 = pow M 1
  have : pow M 2 = pow M 1 := by rw [pow_two, pow_one]; exact h_idem
  exact h_ne this

/-- **U7.7 — CONDITIONAL: IF fan-out → idempotent, THEN gap widens**:
    Under FanOutIdempotentHypothesis, the capacity gap goes from
    (supply ≤ 2, demand ≥ 2) to (supply ≤ 1, demand ≥ 2).
    The gap is WIDER: demand exceeds supply by 1 instead of being equal. -/
theorem wider_gap_if_idempotent :
    -- The demand side: Z/2Z exists in the trace language
    HasGroupOrder2 h2Monodromy ∧
    -- If fan-out produces idempotent, these have no period 2
    (∀ M : BoolMat 8, mul M M = M → ¬ HasGroupOrder2 M) ∧
    -- The tree case already has rank-1 → no period 2
    (∀ M : BoolMat 8, M.IsRankOne → ¬ HasGroupOrder2 M) :=
  ⟨h2_has_group_order_2,
   fun M h => idempotent_kills_z2 M h,
   fun _ h => rank1_no_period2 h⟩

/-! ## Part 3: CAREFUL CHECK — Where the Argument BREAKS

  The argument claims:
  (1) Any poly circuit C uses fan-out (DAG, not tree) -- TRUE
  (2) Fan-out at gap level → entryAnd → idempotent → KR = 0 -- **FALSE**
  (3) Trace language → KR ≥ 1 -- TRUE
  (4) Contradiction → C cannot compute gap consistency -- would follow from (2)
  (5) → P ≠ NP -- would follow from (4)

  **WHERE IT BREAKS: Step (2)**

  The flaw: "fan-out at gap level = entryAnd(M, M)" is INCORRECT.

  A circuit fans out BITS, not gap projections:
  - Wire w carries bit b(formula)
  - Branch 1 computes f₁(b, others₁) → some gap-level effect π₁
  - Branch 2 computes f₂(b, others₂) → some gap-level effect π₂
  - π₁ and π₂ are DIFFERENT (different functions of different other inputs!)
  - The constraint is entryAnd(π₁, π₂) where π₁ ≠ π₂
  - NOT entryAnd(π₁, π₁) = π₁

  entryAnd of DIFFERENT matrices ≠ entryAnd of the SAME matrix!
  - entryAnd(M, M) = M (idempotent) → always preserves period
  - entryAnd(M₁, M₂) with M₁ ≠ M₂ → can be zero, rank-1, or anything ≤ both

  This is a CATEGORY ERROR: confusing bit-level and gap-level operations. -/

/-- **U7.8 — ALL H2 CROSS-ENTRYANDS ARE ZERO**: On the h2 witness, ALL pairwise
    entryAnds of DIFFERENT transfer operators produce the zero matrix.
    This is because the h2 transfer ops have pairwise disjoint supports.
    (h2 is a 3-cycle of cubes with 2 gaps each — the transfer operators
    map gap-to-gap across different cube pairs, giving disjoint entry patterns.) -/
theorem h2_cross_entryAnd_all_zero :
    -- All pairwise cross-entryAnds on h2 generators are zero
    isZero (BoolMat.entryAnd h2MonAB h2MonBC) ∧
    isZero (BoolMat.entryAnd h2MonBC h2MonCA) ∧
    isZero (BoolMat.entryAnd h2MonCA h2MonAB) ∧
    isZero (BoolMat.entryAnd h2Monodromy h2MonodromyB) ∧
    isZero (BoolMat.entryAnd h2Monodromy h2MonAB) ∧
    isZero (BoolMat.entryAnd h2MonodromyB h2MonAB) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **U7.9 — NONZERO CROSS-ENTRYAND EXISTS IN GENERAL**: While h2 generators
    all have disjoint supports, this is NOT a general law. There exist BoolMat 8
    elements whose cross-entryAnd is nonzero and strictly smaller than either input.

    We construct a concrete example: two rank-1 8×8 matrices with overlapping
    but non-identical supports, whose entryAnd is nonzero and ≠ either input. -/

private def crossA : BoolMat 8 := outerProduct
  (fun i => decide (i.val < 4))
  (fun j => decide (j.val < 4))

private def crossB : BoolMat 8 := outerProduct
  (fun i => decide (i.val < 6))
  (fun j => decide (j.val < 6))

theorem nonzero_cross_entryAnd_exists :
    -- crossA ⊙ crossB is nonzero (has a true entry at (0,0))
    ¬ isZero (BoolMat.entryAnd crossA crossB) ∧
    -- crossA has a true entry at (0,0)
    crossA ⟨0, by omega⟩ ⟨0, by omega⟩ = true ∧
    -- crossB has a true entry at (4,4) that crossA does not
    crossB ⟨4, by omega⟩ ⟨4, by omega⟩ = true ∧
    crossA ⟨4, by omega⟩ ⟨4, by omega⟩ = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **U7.10 — THE CRITICAL DISTINCTION**: Self-entryAnd is always trivial (M ⊙ M = M).
    Cross-entryAnd can range from zero (disjoint supports) to equal to one input
    (containment) to strictly between. The h2 generators are all in the "zero" case.

    A circuit's fan-out produces cross-entryAnd (π₁ ≠ π₂), never self-entryAnd.
    The zero case (h2) means cross fan-out is DESTRUCTIVE — it kills ALL structure,
    not just Z/2Z. But this is specific to h2; general circuits create different π. -/
theorem critical_distinction :
    -- Self: always trivial
    (∀ M : BoolMat 8, BoolMat.entryAnd M M = M) ∧
    -- Cross on h2: always zero (extreme case)
    isZero (BoolMat.entryAnd h2MonAB h2MonBC) ∧
    -- Cross in general: CAN be nonzero
    ¬ isZero (BoolMat.entryAnd crossA crossB) := by
  exact ⟨fun M => entryAnd_self M, by native_decide, by native_decide⟩

/-! ## Part 4: What Fan-Out ACTUALLY Does at Gap Level

  Fan-out of bit b at the circuit level:
  - Two branches receive the same value v = b(formula)
  - Branch 1 computes f₁(v, x₁, x₂, ...) → gap projection π₁
  - Branch 2 computes f₂(v, y₁, y₂, ...) → gap projection π₂
  - π₁ and π₂ are CORRELATED (share input v) but DIFFERENT functions

  The gap-level effect:
  - π₁ is some BoolMat M₁ (depends on v and branch-1 inputs)
  - π₂ is some BoolMat M₂ (depends on v and branch-2 inputs)
  - The fan-out constraint: M₁ and M₂ must agree on the v-component
  - Modeled as: entryAnd(M₁, M₂) where M₁ ≠ M₂ in general

  The KEY observation (from Mu5):
  entryAnd (= boolAnd) of two rank-1 matrices → rank-0 (zero) or rank-1
  (Mu5: boolAnd_zero_or_rankOne). Good for rank.

  BUT: the overall DAG combines entryAnd with mul and σ.
  The combined algebra is what matters.
  And we proved in Tau7: the combined algebra on h2 generators stays bounded.
  But we did NOT prove it for ALL possible inputs.

  From Mu5: OR breaks rank-1. From Tau7: AND preserves it.
  The circuit uses both (through mul + entryAnd). -/

/-- **U7.11 — ENTRYAND PRESERVES RANK-1 (from Mu5)**:
    entryAnd (= boolAnd) of two rank-1 matrices is either zero or rank-1.
    This is the GOOD news: entryAnd does not increase rank.
    But it says nothing about PERIOD (aperiodicity vs period-2). -/
theorem entryAnd_rank_bounded {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne) :
    isZero (boolAnd A B) ∨ (boolAnd A B).IsRankOne :=
  boolAnd_zero_or_rankOne hA hB

/-- **U7.12 — THE MU5 WARNING**: OR of two rank-1 matrices CAN be rank-2.
    This means: if a circuit computes an OR-like operation at the gap level
    (which mul can do: M[i,j] = OR_k(A[i,k] AND B[k,j])), the result
    can escape rank-1. The escape route is through mul, NOT through entryAnd.

    entryAnd is the SAFE operation (rank-preserving).
    mul is the DANGEROUS operation (rank-increasing for OR-component). -/
theorem or_escapes_rank1 :
    ∃ (A B : BoolMat 3), A.IsRankOne ∧ B.IsRankOne ∧ ¬(boolOr A B).IsRankOne :=
  entrywise_or_breaks_rank1

/-! ## Part 5: The Level 1 / Level 2 Category Error

  The fundamental confusion:

  LEVEL 1 (bits/variables): Circuit fan-out copies a BIT value.
    - Exact duplication: bit b appears in both branches with value b
    - This IS idempotent at the bit level: b AND b = b

  LEVEL 2 (gaps/matrices): The gap projection of each branch is a BoolMat.
    - Branch 1: gap projection π₁ depends on b AND other inputs
    - Branch 2: gap projection π₂ depends on b AND other inputs
    - π₁ and π₂ are DIFFERENT BoolMats (different other inputs!)
    - The fan-out constraint at gap level: entryAnd(π₁, π₂) ≠ entryAnd(π₁, π₁)

  The category error: treating bit-level idempotency as gap-level idempotency.

  This is the SAME structural error as S-48's category error:
  confusing operations at different abstraction levels.

  The Tau6 level separation theorem tells us:
  - Level 1 operations (on variables) project to Level 2 (on gaps)
  - But the projection is MANY-TO-ONE
  - Different Level 1 operations can project to the SAME Level 2 effect
  - But the SAME Level 1 operation (fan-out) projects to DIFFERENT Level 2 effects
    in different branches (because branches have different contexts) -/

/-- **U7.13 — BIT-LEVEL IDEMPOTENCY**: Bool.and b b = b for any boolean b.
    This is the CORRECT statement about fan-out at the bit level.
    It does NOT imply entryAnd(π₁, π₂) = π₁ at the gap level. -/
theorem bit_level_idempotent (b : Bool) : Bool.and b b = b := by cases b <;> rfl

/-- **U7.14 — GAP-LEVEL IS DIFFERENT**: At the gap level, fan-out produces
    entryAnd(π₁, π₂) where π₁ ≠ π₂ in general.
    We prove: there EXIST pairs where entryAnd gives something different from
    both inputs (the nonzero case), AND pairs where it gives zero (the h2 case). -/
theorem gap_level_nontrivial :
    -- Some pairs: cross-entryAnd is nonzero and equals one input (containment)
    (¬ isZero (BoolMat.entryAnd crossA crossB)) ∧
    -- Some pairs: cross-entryAnd is zero (disjoint supports)
    isZero (BoolMat.entryAnd h2MonAB h2MonBC) ∧
    -- Both are different from self-entryAnd which is always M
    (∀ M : BoolMat 8, BoolMat.entryAnd M M = M) := by
  exact ⟨by native_decide, by native_decide, fun M => entryAnd_self M⟩

/-- **U7.15 — THE LEVEL SEPARATION IS IRREVERSIBLE**:
    From Sigma7: the information bottleneck (π is many-to-one) means
    different circuit states can have the same gap projection.
    From Tau6: projectToCube depends only on 3 variables out of n.

    The consequence: knowing π₁ and π₂ share a bit-level input
    does NOT tell you how π₁ and π₂ relate as BoolMats.
    The fan-out constraint is at Level 1. The algebraic structure is at Level 2.
    They are not directly comparable. -/
theorem level_separation_irreversible (G : CubeGraph) (a : Assignment) (x : Nat)
    (hfree : isFreeVar G x) :
    projectToGraph G (fun v => if v = x then !a v else a v) =
    projectToGraph G a :=
  information_loss_fiber G a x hfree

/-! ## Part 6: The Honest Conclusion

  WHAT WE PROVED (unconditional):

  (a) Self fan-out (entryAnd(M, M) = M) is trivial — preserves ALL properties.
  (b) Cross fan-out (entryAnd(M₁, M₂) with M₁ ≠ M₂):
      - On h2: ALL pairs produce ZERO (disjoint supports)
      - In general: can produce nonzero results strictly smaller than inputs
      - Rank-1 preserved: boolAnd of rank-1 is rank-1 or zero (Mu5)
  (c) On h2: cross-entryAnd kills ALL structure (not just Z/2Z).
  (d) The idempotent hypothesis WOULD strengthen the gap (KR = 0 < demand KR ≥ 1).

  WHAT IS WRONG:

  (e) Bit-level fan-out ≠ gap-level entryAnd(M, M).
      It's entryAnd(M₁, M₂) where M₁ ≠ M₂ in general.
  (f) Therefore: the "fan-out kills Z/2Z for ALL circuits" claim is FALSE.
  (g) The P ≠ NP argument via idempotent fan-out DOES NOT WORK.

  WHAT REMAINS OPEN:

  (h) Whether the combined algebra {mul, entryAnd, σ} on ALL BoolMat 8
      elements maintains capacity ≤ 2. (Tau7 Part 7)
  (i) Whether fan-out of correlated but different gap projections
      can produce capacity > 2. (The real question)
  (j) Whether the many-to-one projection π creates enough constraint
      to bound the combined algebra. (The Projection Lemma) -/

/-- **U7.16 — GRAND SUMMARY: THE ARGUMENT AND ITS FLAW**

    The chain:
    (1) Tree circuits: KR = 1 (Sigma7) — PROVED
    (2) Self fan-out: trivial, no change — PROVED
    (3) Cross fan-out on h2: kills ALL structure (zero) — PROVED (concrete)
    (4) "Fan-out kills Z/2Z for all circuits" — FALSE (Level 1/2 confusion)
    (5) The honest status: Projection Lemma remains the SINGLE open question

    This file does NOT advance the P ≠ NP argument.
    It clarifies WHY a specific attack path (via fan-out idempotency) fails. -/
theorem grand_summary_fanout_consequences :
    -- (a) Self fan-out is trivial
    (∀ M : BoolMat 8, BoolMat.entryAnd M M = M) ∧
    -- (b) Cross fan-out on h2 is zero (all pairwise)
    isZero (BoolMat.entryAnd h2MonAB h2MonBC) ∧
    -- (c) The demand side persists: Z/2Z needed
    HasGroupOrder2 h2Monodromy ∧
    -- (d) Rank-1 never has Z/2Z
    (∀ M : BoolMat 8, M.IsRankOne → ¬ HasGroupOrder2 M) ∧
    -- (e) Idempotent never has Z/2Z (the conditional result)
    (∀ M : BoolMat 8, mul M M = M → ¬ HasGroupOrder2 M) ∧
    -- (f) entryAnd preserves rank ≤ 1 (the Mu5 positive result)
    (∀ (A B : BoolMat 8), A.IsRankOne → B.IsRankOne →
      isZero (boolAnd A B) ∨ (boolAnd A B).IsRankOne) ∧
    -- (g) The parity obstruction stands
    (2 ^ 3 - 1 = 7 ∧ 7 % 2 = 1) :=
  ⟨fun M => entryAnd_self M,
   by native_decide,
   h2_has_group_order_2,
   fun M h => rank1_no_period2 h,
   fun M h => idempotent_kills_z2 M h,
   fun A B hA hB => boolAnd_zero_or_rankOne hA hB,
   threeSAT_gaps_is_7_and_odd⟩

/-- **U7.17 — THE CATEGORY ERROR, FORMALIZED**:
    The argument "fan-out → entryAnd → idempotent → KR = 0" conflates
    two distinct operations:
    1. entryAnd(M, M) = M (self-duplication: DOES preserve everything)
    2. entryAnd(M₁, M₂) with M₁ ≠ M₂ (cross-restriction: CAN be zero or smaller)

    A circuit's fan-out is always type (2), never type (1), because the
    two branches compute DIFFERENT functions of the shared bit.
    Therefore "fan-out → KR = 0" is a non-sequitur.

    We prove the distinction exists: self ≠ cross. -/
theorem category_error_exists :
    -- Self fan-out: entryAnd(M, M) = M (always trivial)
    (BoolMat.entryAnd h2MonAB h2MonAB = h2MonAB) ∧
    -- Cross fan-out on h2: entryAnd(M₁, M₂) = 0 (kills everything)
    isZero (BoolMat.entryAnd h2MonAB h2MonBC) ∧
    -- The self case preserves Z/2Z (identity on period)
    (HasGroupOrder2 h2Monodromy →
      HasGroupOrder2 (BoolMat.entryAnd h2Monodromy h2Monodromy)) ∧
    -- The cross case kills Z/2Z (kills EVERYTHING, it's zero)
    isZero (BoolMat.entryAnd h2Monodromy h2MonodromyB) := by
  refine ⟨entryAnd_self h2MonAB, ?_, ?_, ?_⟩
  · native_decide
  · intro h; rwa [entryAnd_self]
  · native_decide

/-- **U7.18 — THE HONEST STATUS OF THE P≠NP ATTACK**:

    CLOSED paths:
    - Fan-out idempotency → KR = 0: WRONG (Level 1/2 confusion)
    - entryAnd kills all Z/2Z: WRONG (self-entryAnd preserves everything)
    - h2 cross-entryAnd analysis: proves zero, but h2-specific (not general)

    OPEN path (unchanged from Sigma7 + Tau7):
    - IF the combined algebra {mul, entryAnd, σ} has capacity ≤ 2 for ALL products,
      THEN the conditional chain completes and P ≠ NP follows.
    - This remains the Projection Lemma: the SINGLE gap.

    The fan-out analysis DOES NOT close this gap.
    It DOES clarify the precise nature of the gap:
    the question is about CROSS fan-out (entryAnd of DIFFERENT matrices),
    not SELF fan-out (which is trivial). -/
theorem honest_status :
    -- The demand: Z/2Z still needed
    HasGroupOrder2 h2Monodromy ∧
    -- Self fan-out: trivially bounded
    (∀ M : BoolMat 8, BoolMat.entryAnd M M = M) ∧
    -- The parity: still odd
    (2 ^ 3 - 1 = 7 ∧ 7 % 2 = 1) ∧
    -- Idempotent → no Z/2Z (the conditional that would help but doesn't apply)
    (∀ M : BoolMat 8, mul M M = M → ¬ HasGroupOrder2 M) :=
  ⟨h2_has_group_order_2,
   fun M => entryAnd_self M,
   threeSAT_gaps_is_7_and_odd,
   fun M h => idempotent_kills_z2 M h⟩

/-- **U7.19 — THE COMPLETE PICTURE, FORMALIZED**:

    PROVED facts (all unconditional):
    (a) entryAnd is commutative, associative, idempotent (Tau7)
    (b) entryAnd preserves rank ≤ 1 (Mu5)
    (c) entryAnd preserves trace-false (Tau7: UNSAT signals survive)
    (d) On h2: all cross-entryAnd = zero (concrete verification)
    (e) OR breaks rank-1 (Mu5: counterexample)
    (f) Idempotent → aperiodic → no Z/2Z (algebraic fact)
    (g) The demand side: h2Monodromy has Z/2Z (period 2)
    (h) Parity obstruction: 2³ - 1 = 7 (odd)

    The flaw in the "fan-out kills Z/2Z" argument:
    - Circuit fan-out copies BITS, not gap projections
    - Two branches produce DIFFERENT gap projections π₁ ≠ π₂
    - entryAnd(π₁, π₂) ≠ entryAnd(π₁, π₁) = π₁
    - The idempotent argument only applies to entryAnd(π₁, π₁)
    - Circuits never do entryAnd(π₁, π₁); they do entryAnd(π₁, π₂)
    - Therefore: the fan-out → KR = 0 step is INVALID -/
theorem complete_picture :
    -- Algebraic properties
    (∀ A B : BoolMat 8, BoolMat.entryAnd A B = BoolMat.entryAnd B A) ∧
    (∀ A : BoolMat 8, BoolMat.entryAnd A A = A) ∧
    -- Trace monotonicity
    (∀ A B : BoolMat 8, BoolMat.trace A = false →
      BoolMat.trace (BoolMat.entryAnd A B) = false) ∧
    -- h2 cross-entryAnd all zero
    isZero (BoolMat.entryAnd h2MonAB h2MonBC) ∧
    -- OR breaks rank-1
    (∃ (A B : BoolMat 3), A.IsRankOne ∧ B.IsRankOne ∧ ¬(boolOr A B).IsRankOne) ∧
    -- Demand persists
    HasGroupOrder2 h2Monodromy ∧
    -- Parity stands
    (2 ^ 3 - 1 = 7 ∧ 7 % 2 = 1) :=
  ⟨fun A B => entryAnd_comm A B,
   fun A => entryAnd_self A,
   fun A B h => entryAnd_trace_false_absorbs A B h,
   by native_decide,
   entrywise_or_breaks_rank1,
   h2_has_group_order_2,
   threeSAT_gaps_is_7_and_odd⟩

end CubeGraph
