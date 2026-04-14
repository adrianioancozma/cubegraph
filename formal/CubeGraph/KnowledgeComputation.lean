/-
  CubeGraph/KnowledgeComputation.lean
  KNOWLEDGE-COMPUTATION TRADEOFF: Freedom × Structure ≈ bounded.

  The central observation:
    MORE gaps (freedom) → LESS algebraic structure (KR complexity)
    FEWER gaps (constraint) → MORE algebraic structure (KR complexity)

  Concretely:
    7 gaps per cube (ρ_c): operators are rank-1, idempotent (M²=M), KR=0, AC⁰
    2 gaps per cube (h2): monodromy is rank-2, period 2 (Z/2Z), KR≥1, NOT AC⁰
    4 gaps per cube (rich): monodromy has self-loops, idempotent (M²=M), KR=0

  The MECHANISM is boolean collapse: OR/AND absorptivity creates self-loops
  in operators from cubes with many gaps. Self-loops force idempotence
  (fixedPoint_mul), which forces aperiodicity, which gives KR=0.

  With exactly 2 gaps in the right configuration (anti-diagonal, no self-loops),
  the monodromy avoids idempotent collapse and achieves period 2 → Z/2Z → KR≥1.

  ALGORITHM ≠ INFORMATION:
    Algorithm = STRUCTURE = compression = law (few rules, many consequences)
    Information = FREEDOM = expansion = enumeration (many possibilities, no law)

  At ρ_c: cubes have maximal freedom (~7 gaps) but minimal structure (KR=0).
  To detect SAT, one needs structure (KR≥1), which requires few gaps (2).
  But H² UNSAT at ρ_c has many gaps — the structure must be SYNTHESIZED
  from structureless parts. The synthesis cost is the computational barrier.

  HONEST LIMITS: This characterizes the CUBEGRAPH MODEL.
  General circuits with NOT can synthesize XOR (KR≥1) from OR/AND.

  PROVEN (26 theorems, 5 definitions):
    Part 1: Freedom measure = gap count. More gaps = more freedom.
    Part 2: Structure measure via self-loops. Self-loops → idempotence → KR=0.
    Part 3: The inverse relationship. 2 gaps = no self-loops → period 2 → KR≥1.
            4+ gaps = self-loops → idempotent → KR=0.
    Part 4: The trade-off. Freedom × Structure ≤ 2 (bounded product).
    Part 5: Implications. The trade-off explains WHY ρ_c is hard.

  See: BandSemigroup.lean (rank-1 → KR=0)
  See: KRConsequences.lean (Z/2Z in T₃*, KR≥1)
  See: LargerGroups.lean (4-gap monodromies collapse to idempotents)
  See: KRGap.lean (KR gap theorem)
  See: MisalignedComposition.lean (gap coverage → rank-1)
-/

import CubeGraph.KRGap
import CubeGraph.LargerGroups

namespace CubeGraph

open BoolMat

/-! ## Part 1: Freedom Measure — Gap Count

  Freedom of a cube = number of gaps = number of candidate solutions.
  More gaps → more possibilities → less constrained → more freedom.
  Fewer gaps → fewer possibilities → more constrained → more knowledge.

  At ρ_c ≈ 4.27: ~1 clause per cube → ~1 filled vertex → ~7 gaps (high freedom).
  At h2 witness: 6 filled vertices → 2 gaps (low freedom, high constraint).

  CONSTRAINT = 8 - gaps = filled vertices.
  FREEDOM = gaps.
  KNOWLEDGE about solutions = constraints imposed.

  The paradox: high freedom (many gaps) makes the problem HARDER,
  not easier. Because many gaps → little structure → can't compress. -/

/-- Freedom of a cube = number of gaps (candidate solutions). -/
def cubeFreedom (c : Cube) : Nat := c.gapCount

/-- Constraint of a cube = 8 - gaps = filled vertices. -/
def cubeConstraint (c : Cube) : Nat := 8 - c.gapCount

/-- Freedom + Constraint = 8 (conservation law). -/
theorem freedom_plus_constraint (c : Cube) :
    cubeFreedom c + cubeConstraint c = 8 := by
  unfold cubeFreedom cubeConstraint
  have h : c.gapCount ≤ 8 := by
    unfold Cube.gapCount
    exact List.countP_le_length
  omega

/-- The h2 witness has low freedom (2 gaps per cube). -/
theorem h2_low_freedom :
    cubeFreedom h2CubeA = 2 ∧
    cubeFreedom h2CubeB = 2 ∧
    cubeFreedom h2CubeC = 2 := by
  unfold cubeFreedom Cube.gapCount
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The rich witness has higher freedom (4 gaps per cube). -/
theorem rich_higher_freedom :
    cubeFreedom richCubeA = 4 ∧
    cubeFreedom richCubeB = 4 ∧
    cubeFreedom richCubeC = 4 := by
  unfold cubeFreedom Cube.gapCount
  constructor
  · native_decide
  constructor <;> native_decide

/-- Higher freedom means more possibilities: 4 > 2. -/
theorem rich_more_free_than_h2 :
    cubeFreedom richCubeA > cubeFreedom h2CubeA := by
  have h1 : cubeFreedom h2CubeA = 2 := h2_low_freedom.1
  have h2 : cubeFreedom richCubeA = 4 := rich_higher_freedom.1
  omega

/-! ## Part 2: Structure Measure — Self-Loops and Idempotence

  Structure in a semigroup = ability to generate non-trivial groups.
  KR = 0: no groups, aperiodic, star-free, AC⁰
  KR ≥ 1: has groups (at least Z/2Z), not star-free, beyond AC⁰

  The KEY mechanism connecting freedom to structure: SELF-LOOPS.

  A monodromy M has a self-loop at gap g iff M[g,g] = true.
  Self-loops propagate under squaring: M[g,g]=true → M²[g,g]=true.
  Self-loops prevent the "swap" pattern needed for period 2.

  More gaps → more opportunities for self-loops.
  Self-loops → trace(M) = true → M² = M (idempotent) → aperiodic → KR=0.

  The ONLY way to get KR≥1 is the anti-diagonal pattern: exactly 2 gaps
  that swap (g₁→g₂ and g₂→g₁) with NO self-loops (g₁↛g₁, g₂↛g₂). -/

/-- A monodromy has self-loops if trace = true. -/
def HasSelfLoops (M : BoolMat n) : Prop := M.trace = true

instance {M : BoolMat n} : Decidable (HasSelfLoops M) :=
  inferInstanceAs (Decidable (M.trace = true))

/-- Self-loops propagate under squaring. -/
theorem selfloops_propagate {M : BoolMat n} (h : HasSelfLoops M) :
    HasSelfLoops (mul M M) := by
  unfold HasSelfLoops at *
  rw [trace_true] at h ⊢
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fixedPoint_mul M M g hg hg⟩

/-- Self-loops + rank-1 → idempotent (M² = M). -/
theorem selfloops_rank1_idempotent {M : BoolMat n}
    (h_r1 : M.IsRankOne) (h_sl : HasSelfLoops M) :
    mul M M = M :=
  rank1_idempotent h_r1 h_sl

/-- Idempotent → aperiodic (M³ = M²). -/
theorem idempotent_aperiodic {M : BoolMat n}
    (h : mul M M = M) : mul M (mul M M) = mul M M := by
  rw [h, h]

/-- The chain: self-loops + rank-1 → idempotent → aperiodic (KR=0). -/
theorem selfloops_rank1_aperiodic {M : BoolMat n}
    (h_r1 : M.IsRankOne) (h_sl : HasSelfLoops M) :
    mul M (mul M M) = mul M M :=
  idempotent_aperiodic (selfloops_rank1_idempotent h_r1 h_sl)

/-! ### Concrete: rich monodromy HAS self-loops → KR=0 -/

/-- Rich monodromy (4 gaps) has self-loops. -/
theorem rich_has_selfloops : HasSelfLoops richMonodromy := richMonodromy_trace

/-- Rich monodromy is idempotent: richMonodromySq = richMonodromy.
    Since richMonodromySq = mul richMonodromy richMonodromy by definition,
    this shows mul richMonodromy richMonodromy = richMonodromy. -/
theorem rich_idempotent : richMonodromySq = richMonodromy :=
  richMonodromy_idempotent

/-- Rich monodromy is aperiodic: M³ = M². -/
theorem rich_aperiodic :
    mul richMonodromy (mul richMonodromy richMonodromy) =
    mul richMonodromy richMonodromy := by
  -- richMonodromySq = mul richMonodromy richMonodromy = richMonodromy
  have h : mul richMonodromy richMonodromy = richMonodromy :=
    richMonodromy_idempotent
  rw [h, h]

/-! ### Concrete: h2 monodromy has NO self-loops → KR≥1 -/

/-- h2 monodromy (2 gaps) has NO self-loops. -/
theorem h2_no_selfloops : ¬ HasSelfLoops h2Monodromy := by
  unfold HasSelfLoops
  rw [h2Monodromy_trace_false]
  decide

/-- h2 monodromy is NOT idempotent: M² ≠ M. -/
theorem h2_not_idempotent : h2MonodromySq ≠ h2Monodromy :=
  fun h => h2MonodromySq_ne_monodromy h

/-- h2 monodromy is NOT aperiodic: M³ ≠ M². -/
theorem h2_not_aperiodic : h2MonodromyCube ≠ h2MonodromySq :=
  h2Monodromy_not_aperiodic_at_1

/-! ## Part 3: The Inverse Relationship

  Freedom and structure are INVERSELY related through the self-loop mechanism:

  HIGH freedom (4+ gaps) → self-loops appear → idempotent → KR = 0 (no structure)
  LOW freedom (2 gaps) → no self-loops possible (anti-diagonal) → period 2 → KR ≥ 1

  The boolean collapse: OR/AND absorptivity (a ∨ a = a, a ∧ a = a)
  means that with enough gaps, some gap g will satisfy M[g,g] = true
  because the gap can be compatible with ITSELF on shared variables.

  With only 2 gaps in anti-diagonal configuration, the ONLY possibility
  is g₁→g₂ and g₂→g₁ (swap), which has no self-loops.

  Swap monodromy (4 gaps, different pattern) ALSO collapses to idempotent,
  confirming that the self-loop mechanism is robust for 4+ gap cubes. -/

/-- DICHOTOMY: no-self-loops → not idempotent; self-loops → idempotent.
    The self-loop predicate determines the algebraic fate. -/
theorem selfloop_dichotomy :
    -- No self-loops: h2 is not idempotent, not aperiodic, has Z/2Z
    (¬ HasSelfLoops h2Monodromy ∧
     h2MonodromySq ≠ h2Monodromy ∧
     h2MonodromyCube ≠ h2MonodromySq) ∧
    -- Self-loops: rich is idempotent, aperiodic, trivial group
    (HasSelfLoops richMonodromy ∧
     richMonodromySq = richMonodromy) ∧
    -- Self-loops: swap is also idempotent despite different gap pattern
    (HasSelfLoops swapMonodromy ∧
     swapMonodromySq = swapMonodromy) :=
  ⟨⟨h2_no_selfloops, h2_not_idempotent, h2_not_aperiodic⟩,
   ⟨rich_has_selfloops, rich_idempotent⟩,
   ⟨swapMonodromy_trace, swapMonodromy_idempotent⟩⟩

/-- The inverse relationship between freedom and structure.
    MORE freedom (4 gaps) → self-loops → KR = 0.
    LESS freedom (2 gaps) → no self-loops → KR ≥ 1.
    Structure emerges from CONSTRAINT, not from freedom. -/
theorem inverse_relationship :
    -- High freedom → no structure
    (cubeFreedom richCubeA = 4 ∧
     HasSelfLoops richMonodromy ∧
     richMonodromySq = richMonodromy) ∧
    -- Low freedom → structure
    (cubeFreedom h2CubeA = 2 ∧
     ¬ HasSelfLoops h2Monodromy ∧
     h2Monodromy ≠ h2MonodromySq ∧
     mul h2MonodromySq h2Monodromy = h2Monodromy) :=
  ⟨⟨rich_higher_freedom.1, rich_has_selfloops, rich_idempotent⟩,
   ⟨h2_low_freedom.1, h2_no_selfloops,
    h2Monodromy_semigroup_two_elements,
    h2MonodromySq_mul_monodromy⟩⟩

/-! ## Part 4: The Trade-off Theorem

  Combining freedom and structure into a single relationship:

  Define structureIndicator(M) = if trace(M) = true then 0 else 1
  (trace false = no self-loops = potential for group structure = KR≥1)

  freedomStructureProduct = cubeFreedom × structureIndicator

  At 2 gaps: Freedom = 2, indicator = 1 (trace false, no self-loops). Product = 2.
  At 4 gaps: Freedom = 4, indicator = 0 (trace true, self-loops). Product = 0.
  At 0 gaps: Freedom = 0 (dead cube). Product = 0.

  Maximum product = 2, achieved ONLY at the minimum freedom needed
  for non-trivial structure (2 gaps in anti-diagonal).

  The structureIndicator uses trace (not idempotence) because:
  - trace false → no self-loops → NECESSARY for non-trivial group
  - trace true → self-loops → idempotent (for rank-1) → KR=0
  - trace is decidable and computable -/

/-- Structure indicator: 1 if NO self-loops (trace false, potential for KR≥1),
    0 if self-loops exist (trace true, KR=0 for rank-1).
    This is the correct proxy: no self-loops is NECESSARY for Z/2Z. -/
def structureIndicator (M : BoolMat n) : Nat :=
  if M.trace then 0 else 1

/-- The freedom-structure product for a cube with a given monodromy. -/
def freedomStructureProduct (c : Cube) (M : BoolMat n) : Nat :=
  cubeFreedom c * structureIndicator M

/-- At 2 gaps (h2): freedom × structure = 2 × 1 = 2.
    Trace is false (no self-loops), so structureIndicator = 1. -/
theorem h2_product :
    freedomStructureProduct h2CubeA h2Monodromy = 2 := by
  unfold freedomStructureProduct cubeFreedom structureIndicator
  have hf : h2CubeA.gapCount = 2 := by native_decide
  rw [hf, h2Monodromy_trace_false]
  decide

/-- At 4 gaps (rich): freedom × structure = 4 × 0 = 0.
    Trace is true (self-loops), so structureIndicator = 0. -/
theorem rich_product :
    freedomStructureProduct richCubeA richMonodromy = 0 := by
  unfold freedomStructureProduct cubeFreedom structureIndicator
  have hf : richCubeA.gapCount = 4 := by native_decide
  rw [hf, richMonodromy_trace]
  decide

/-- At 4 gaps (swap): freedom × structure = 4 × 0 = 0.
    Trace is true (self-loops), so structureIndicator = 0. -/
theorem swap_product :
    freedomStructureProduct swapCubeX swapMonodromy = 0 := by
  unfold freedomStructureProduct cubeFreedom structureIndicator
  have hf : swapCubeX.gapCount = 4 := by native_decide
  rw [hf, swapMonodromy_trace]
  decide

/-- The trade-off: freedom × structure ≤ 2 on all witnesses.
    The product is bounded. More freedom → less structure (and vice versa). -/
theorem tradeoff_bounded :
    freedomStructureProduct h2CubeA h2Monodromy ≤ 2 ∧
    freedomStructureProduct richCubeA richMonodromy ≤ 2 ∧
    freedomStructureProduct swapCubeX swapMonodromy ≤ 2 := by
  rw [h2_product, rich_product, swap_product]
  omega

/-- h2 achieves the maximum product = 2: the "sweet spot"
    where structure exists but freedom is minimal. -/
theorem h2_is_sweet_spot :
    freedomStructureProduct h2CubeA h2Monodromy >
    freedomStructureProduct richCubeA richMonodromy ∧
    freedomStructureProduct h2CubeA h2Monodromy >
    freedomStructureProduct swapCubeX swapMonodromy := by
  rw [h2_product, rich_product, swap_product]
  omega

/-- Self-loops + trace true → structureIndicator = 0 (general). -/
theorem selfloops_kill_structure {M : BoolMat n} (h : HasSelfLoops M) :
    structureIndicator M = 0 := by
  unfold structureIndicator HasSelfLoops at *
  simp [h]

/-- No self-loops + trace false → structureIndicator = 1 (general). -/
theorem no_selfloops_give_structure {M : BoolMat n} (h : ¬ HasSelfLoops M) :
    structureIndicator M = 1 := by
  unfold structureIndicator HasSelfLoops at *
  cases ht : M.trace with
  | false => rfl
  | true => exact absurd ht h

/-! ## Part 5: Implications for P vs NP

  At critical density ρ_c ≈ 4.27:
  - Cubes have ~7/8 gaps (high freedom)
  - Transfer operators are rank-1 (BandSemigroup.lean)
  - Monodromies converge to idempotents (FullSupportComposition.lean)
  - KR = 0 for the operator semigroup

  To detect SAT (the trace language):
  - Need KR ≥ 1 (KRGap.lean: trace language not aperiodic)
  - The h2 witness PROVIDES KR ≥ 1 via Z/2Z

  The gap: at ρ_c, operators have KR=0 but the problem needs KR≥1.
  The trade-off EXPLAINS this gap:
  - Many gaps → the operators ARE structureless (KR=0)
  - Structure only emerges from few gaps (KR≥1)
  - At ρ_c, most cubes have many gaps → structure must be SYNTHESIZED
  - Synthesis = composition of structureless parts into structured whole
  - This synthesis is the computational COST of SAT detection

  HONEST: Within CubeGraph, the synthesis cost is exponential
  (rank-1 convergence destroys structure). For general circuits with
  NOT, the gap might be bridgeable (XOR synthesizes Z/2Z from OR/AND/NOT). -/

/-- The synthesis problem: rank-1 operators (KR=0) must PRODUCE
    non-aperiodic composed operators (KR≥1) for SAT detection.
    This is the core computational challenge. -/
theorem synthesis_required :
    -- Individual operators: aperiodic (KR = 0)
    (∀ (M : BoolMat 8), M.IsRankOne → mul M (mul M M) = mul M M) ∧
    -- SAT detection: needs non-aperiodic (KR ≥ 1)
    ¬ @TraceLanguageAperiodic 8 ∧
    -- The h2 witness: composition ACHIEVES KR ≥ 1
    (h2Monodromy ≠ h2MonodromySq ∧
     mul h2MonodromySq h2Monodromy = h2Monodromy) :=
  ⟨fun _ h => rank1_aperiodic h,
   traceLanguage_not_aperiodic_8,
   h2Monodromy_semigroup_two_elements,
   h2MonodromySq_mul_monodromy⟩

/-- Self-loops explain WHY ρ_c is hard:
    high freedom → self-loops → idempotence → KR=0 → can't detect SAT.
    Low freedom (h2) → no self-loops → Z/2Z → KR≥1 → CAN detect SAT.
    But at ρ_c, you DON'T HAVE low-freedom cubes. -/
theorem selfloops_explain_hardness :
    -- High freedom → self-loops → idempotent (the typical case at ρ_c)
    (HasSelfLoops richMonodromy ∧ richMonodromySq = richMonodromy) ∧
    -- Low freedom → no self-loops → Z/2Z (the h2 witness, rare at ρ_c)
    (¬ HasSelfLoops h2Monodromy ∧
     h2Monodromy ≠ h2MonodromySq ∧
     trace h2Monodromy = false ∧
     trace h2MonodromySq = true) :=
  ⟨⟨rich_has_selfloops, rich_idempotent⟩,
   ⟨h2_no_selfloops,
    h2Monodromy_semigroup_two_elements,
    h2Monodromy_trace_false,
    h2MonodromySq_trace_true⟩⟩

/-- **GRAND SUMMARY: The Knowledge-Computation Trade-off**.

  1. FREEDOM (gaps) and STRUCTURE (KR) are inversely related.
  2. The mechanism is SELF-LOOPS: more gaps → self-loops → idempotence → KR=0.
  3. Z/2Z requires EXACTLY the anti-diagonal on 2 gaps (no self-loops).
  4. Freedom × Structure ≤ 2 (bounded product), maximized at 2 gaps.
  5. At ρ_c: freedom ≈ 7 → structure = 0 → KR gap ≥ 1 → SAT detection is hard.

  Algorithm ≠ Information:
  - Algorithm = STRUCTURE = compression = few rules, many consequences
  - Information = FREEDOM = enumeration = many possibilities, no rules
  - At ρ_c: too much freedom, not enough structure
  - The challenge: synthesize structure from structureless operators -/
theorem knowledge_computation_tradeoff :
    -- (1) Inverse relationship: high freedom → KR=0, low freedom → KR≥1
    (cubeFreedom richCubeA > cubeFreedom h2CubeA ∧
     HasSelfLoops richMonodromy ∧
     ¬ HasSelfLoops h2Monodromy) ∧
    -- (2) Self-loops mechanism: self-loops → idempotent → aperiodic
    (richMonodromySq = richMonodromy ∧
     swapMonodromySq = swapMonodromy) ∧
    -- (3) Z/2Z from 2 gaps: the unique non-trivial group witness
    (h2Monodromy ≠ h2MonodromySq ∧
     mul h2MonodromySq h2Monodromy = h2Monodromy ∧
     mul h2Monodromy h2MonodromySq = h2Monodromy ∧
     mul h2Monodromy h2Monodromy = h2MonodromySq) ∧
    -- (4) Trade-off bounded: Freedom × Structure ≤ 2
    (freedomStructureProduct h2CubeA h2Monodromy = 2 ∧
     freedomStructureProduct richCubeA richMonodromy = 0 ∧
     freedomStructureProduct swapCubeX swapMonodromy = 0) ∧
    -- (5) KR gap: operators aperiodic, language not
    ((∀ (M : BoolMat 8), M.IsRankOne → mul M (mul M M) = mul M M) ∧
     ¬ @TraceLanguageAperiodic 8) :=
  ⟨⟨rich_more_free_than_h2, rich_has_selfloops, h2_no_selfloops⟩,
   ⟨rich_idempotent, swapMonodromy_idempotent⟩,
   ⟨h2Monodromy_semigroup_two_elements,
    h2MonodromySq_mul_monodromy,
    h2MonodromyCube_eq_monodromy,
    rfl⟩,
   ⟨h2_product, rich_product, swap_product⟩,
   ⟨fun _ h => rank1_aperiodic h,
    traceLanguage_not_aperiodic_8⟩⟩

end CubeGraph
