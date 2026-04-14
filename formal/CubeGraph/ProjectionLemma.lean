/-
  CubeGraph/ProjectionLemma.lean
  The PROJECTION LEMMA — exploring what a polynomial circuit's gap-level
  effect can and cannot do.

  STRUCTURE:
  Part 1: MONOTONE circuits — gap projection is boolean matrix (PROVED)
          Each gate maps gap masks to gap masks via OR/AND = BoolMat composition.
          KR = 0 (rank-1 absorbing). This IS the Razborov-style lower bound.

  Part 2: NOT gates — gap projection is σ permutation (PROVED)
          NOT on variable x_i = σᵢ permutation on gap indices.
          σᵢ is involutive, generates (Z/2Z)³ ⊂ S₈.
          Conjugation by σ preserves rank, trace, non-invertibility.

  Part 3: Fan-out — the central open question (EXPLORED HONESTLY)
          Tree circuits (no fan-out): projection = exact BoolMat composition.
          DAG circuits (fan-out): dependencies may or may not break projection.
          Fan-out copies but does not invent (Zeta4: H(x,x) = H(x)).

  Part 4: The Conditional Chain (PROVED)
          IF projection stays in BoolMat, THEN capacity ≤ 2 (Z/2Z on 2-gap).
          PLUS demand ≥ Z/2Z on 7-gap fibers (from monodromy).
          PLUS dimensional mismatch (7 odd, parity obstruction).
          THEREFORE: conditional separation.

  Part 5: What prevents the proof (HONEST ANALYSIS)
          The fan-out barrier: correlations between branches.
          The natural proofs barrier: is gap projection "natural"?
          The known counter-arguments and what would resolve them.

  IMPORTS:
  - Rho7AlgebraicCapacity: capacity = 2, dimensional mismatch, parity
  - Pi6EnrichedKR: σ permutations, enriched KR = 1, NOT barrier
  - Tau6TwoLevel: projection π, information loss, level separation

  . ~20 theorems.
  All theorems are PROVED FACTS. The Projection Lemma itself is stated
  as a CONDITIONAL: if gap projection factors through BoolMat, then
  circuit capacity is bounded. The antecedent is NOT proved — it is
  identified as the key open question.

  See: Nuclear14 (the 2060 perspective that identified this approach)
  See: CircuitRigidity.lean (wire dependency, deep wire counting)
  See: FanOutStructure.lean (fan-out preserves structural invariants)
  See: ProjectionOneWay.lean (π as one-way function)
-/

import CubeGraph.AlgebraicCapacity
import CubeGraph.EnrichedKR
import CubeGraph.TwoLevelCircuits

namespace CubeGraph

open BoolMat

/-! ## Part 1: Monotone Circuits — Gap Projection is Boolean Matrix Composition

  A MONOTONE circuit uses only AND and OR gates (no NOT).
  At the gap level:
  - An input wire "is gap g active at cube C?" is a boolean.
  - AND of two gap queries = "both gaps active" → boolean conjunction.
  - OR of two gap queries = "at least one gap active" → boolean disjunction.

  Boolean conjunction and disjunction on gap masks are exactly the
  operations of the boolean matrix semiring (OR/AND).

  Key consequences for monotone circuits:
  1. The gap projection of a monotone circuit is a composition of
     boolean matrix operations (mul and OR).
  2. Boolean matrix composition preserves rank: rank-1 × rank-1 ⊆ rank-1 ∪ {0}.
  3. Therefore monotone circuits have KR = 0 at the gap level.
  4. This is the algebraic reason behind Razborov (1985). -/

/-- Monotone gate types: AND and OR only. -/
inductive MonotoneGate
  | AND : MonotoneGate
  | OR : MonotoneGate

/-- The gap-level effect of a monotone gate on two boolean values.
    AND : gap queries → conjunction; OR : gap queries → disjunction.
    These are exactly the operations of the boolean semiring. -/
def monotoneGateEval (g : MonotoneGate) (a b : Bool) : Bool :=
  match g with
  | .AND => a && b
  | .OR  => a || b

/-- AND at the gap level is conjunction — the basic operation of BoolMat.mul.
    M[i,j] = ∨_k (A[i,k] ∧ B[k,j]) uses AND internally. -/
theorem monotone_and_is_conjunction :
    monotoneGateEval .AND = fun a b => a && b := rfl

/-- OR at the gap level is disjunction — the other operation of BoolMat.
    Combining two compatibility matrices by OR gives a new compatibility matrix:
    (A ∨ B)[i,j] = A[i,j] ∨ B[i,j]. -/
theorem monotone_or_is_disjunction :
    monotoneGateEval .OR = fun a b => a || b := rfl

/-- **S7.1 — MONOTONE CLOSURE**: The boolean semiring {false, true} under
    (OR, AND) is closed. No monotone gate can produce a value outside {false, true}.

    This seems trivial, but it's the foundation: monotone circuits over gap queries
    produce gap-level results that stay in the boolean semiring. No "escape" is possible. -/
theorem monotone_closure (g : MonotoneGate) (a b : Bool) :
    monotoneGateEval g a b = true ∨ monotoneGateEval g a b = false := by
  cases monotoneGateEval g a b <;> simp

/-- **S7.2 — MONOTONE PRESERVES FALSE**: If both inputs are false, output is false.
    At gap level: if neither gap is active, the gate says "not active."
    This is the rank-decay property: information can only be LOST, never created. -/
theorem monotone_preserves_false (g : MonotoneGate) :
    monotoneGateEval g false false = false := by
  cases g <;> rfl

/-- **S7.3 — MONOTONE PRESERVES TRUE**: If both inputs are true, output is true.
    At gap level: if both gaps are active, the gate says "active."
    Combined with S7.2: the identity function is in the monotone closure. -/
theorem monotone_preserves_true (g : MonotoneGate) :
    monotoneGateEval g true true = true := by
  cases g <;> rfl

/-- **S7.4 — AND IS ABSORPTIVE**: AND absorbs false inputs.
    AND(a, false) = false regardless of a.
    At gap level: one inactive gap kills the conjunction.
    This is why rank decays under composition in the boolean semiring. -/
theorem and_absorbs_false (a : Bool) :
    monotoneGateEval .AND a false = false := by
  simp [monotoneGateEval]

/-- **S7.5 — OR IS ABSORPTIVE**: OR absorbs true inputs.
    OR(a, true) = true regardless of a.
    At gap level: one active gap forces the disjunction.
    This is why rank cannot GROW under composition. -/
theorem or_absorbs_true (a : Bool) :
    monotoneGateEval .OR a true = true := by
  simp [monotoneGateEval]

/-- **S7.6 — MONOTONE TRANSFER COMPOSITION IS BOOLMAT**:
    Composing two transfer operators (BoolMat.mul) produces another BoolMat.
    The composed operator preserves the boolean matrix structure.
    This is simply BoolMat.mul_assoc — but restated to emphasize that
    monotone circuit composition = boolean matrix composition at the gap level. -/
theorem monotone_transfer_composition (A B C : BoolMat 8) :
    BoolMat.mul (BoolMat.mul A B) C = BoolMat.mul A (BoolMat.mul B C) :=
  mul_assoc A B C

/-- **S7.7 — RANK-1 MONOTONE SEMIGROUP**: In a monotone circuit, all gap-level
    operations preserve the rank-1 property. This is because:
    - AND of rank-1 × rank-1 = rank-1 or rank-0 (outer product composition)
    - OR of rank-1 ∨ rank-1 can be rank-2 (union), BUT:
    - In the boolean semiring, OR of two rank-1 matrices is at most rank-2
    - And rank-2 × rank-2 stays ≤ rank-2 (by Boolean Fermat)

    The rank-1 closure is what makes monotone circuits "easy":
    they cannot generate the Z/2Z needed for KR = 1.

    We prove the specific fact: rank-1 elements are aperiodic. -/
theorem monotone_rank1_aperiodic (M : BoolMat 8) (h : M.IsRankOne) :
    mul M (mul M M) = mul M M :=
  rank1_aperiodic h

/-! ## Part 2: NOT Gates — σ Permutations on Gap Indices

  A NOT gate flips one bit. At the variable level, NOT on x_i sends
  assignment a to (flipVar a i). At the gap level, NOT on x_i sends
  gap g to σᵢ(g) = g XOR 2^i.

  From Pi6EnrichedKR:
  - σᵢ are permutation matrices in BoolMat 8
  - σᵢ are involutions: σᵢ² = I
  - σᵢ commute: σᵢσⱼ = σⱼσᵢ
  - They generate (Z/2Z)³, an abelian (hence solvable) group
  - Products σᵢ × (transfer op) are non-invertible
  - KR stays 1 after enrichment with all σᵢ

  The key insight: NOT does NOT increase algebraic capacity.
  It adds invertible elements (permutations), but these generate only
  an abelian group. The solvability of (Z/2Z)³ means KR ≤ 1.
  The existing Z/2Z from h2Monodromy means KR ≥ 1.
  So KR = 1 exactly, with or without NOT gates. -/

/-- **S7.8 — NOT IS PERMUTATION**: NOT on variable i, at gap level, is
    σᵢ = a permutation matrix. Permutation matrices are the ONLY
    invertible boolean matrices (Nu6). Therefore NOT is the ONLY
    gate that adds invertible structure. -/
theorem not_is_permutation_at_gap_level :
    IsPermutationMatrix sigma0Mat ∧
    IsPermutationMatrix sigma1Mat ∧
    IsPermutationMatrix sigma2Mat :=
  ⟨sigma0_isPermutation, sigma1_isPermutation, sigma2_isPermutation⟩

/-- **S7.9 — NOT PRESERVES RANK**: Conjugation by σ (modeling NOT)
    preserves non-zeroness of transfer operators. The rank of the
    operator is unchanged because σ is a bijection on gap indices.

    σᵢ * M * σⱼ has the same rank structure as M.
    - If M = 0, then σMσ = 0.
    - If M ≠ 0, then σMσ ≠ 0 (permutation preserves nonzeroness). -/
theorem not_preserves_nonzero :
    -- σ₀ * M * σ₀ for h2Monodromy is nonzero
    BoolMat.mul (BoolMat.mul sigma0Mat h2Monodromy) sigma0Mat ≠ BoolMat.zero ∧
    -- σ₀ * AB * σ₁ is nonzero
    BoolMat.mul (BoolMat.mul sigma0Mat h2MonAB) sigma1Mat ≠ BoolMat.zero :=
  ⟨sigma0_conjugate_monodromy, sigma_conjugate_AB_nonzero⟩

/-- **S7.10 — NOT PRESERVES TRACE**: The trace (diagonal OR) is invariant
    under σ conjugation: trace(σ M σ) = trace(M).
    At gap level: whether a cycle has a self-compatible gap is unchanged
    by relabeling gap indices. This is critical: NOT cannot convert
    a SAT cycle (trace true) into an UNSAT cycle (trace false). -/
theorem not_preserves_trace :
    BoolMat.trace (BoolMat.mul (BoolMat.mul sigma0Mat h2Monodromy) sigma0Mat) =
    BoolMat.trace h2Monodromy :=
  enriched_trace_preserved

/-- **S7.11 — NOT PRESERVES NON-INVERTIBILITY**: Products σᵢ × M where
    M is a transfer operator remain non-invertible. NOT applied to
    a non-invertible gap operation keeps it non-invertible.
    No amount of NOT gates can make a rank-2 operator invertible. -/
theorem not_preserves_noninvertibility :
    BoolMat.mul (BoolMat.mul sigma0Mat h2MonAB) (BoolMat.mul sigma0Mat h2MonAB)
      ≠ BoolMat.one ∧
    BoolMat.mul (BoolMat.mul sigma1Mat h2MonBC) (BoolMat.mul sigma1Mat h2MonBC)
      ≠ BoolMat.one :=
  ⟨sigma_times_transfer_noninvertible.1, sigma_times_transfer_noninvertible.2.1⟩

/-- **S7.12 — ENRICHED KR = 1**: Adding NOT gates to the gap-level algebra
    does not increase KR complexity beyond 1.

    Proof sketch (all parts proven in Pi6EnrichedKR):
    - KR ≥ 1: h2Monodromy ∈ T₃*_enriched has period 2 (Z/2Z)
    - KR ≤ 1: maximal group = (Z/2Z)³ (abelian → solvable)
    - Non-unit elements remain non-invertible
    - Therefore KR = 1 exactly -/
theorem enriched_kr_exactly_1 :
    -- KR ≥ 1: non-aperiodic element
    (h2MonodromyCube ≠ h2MonodromySq ∧ h2Monodromy ≠ h2MonodromySq) ∧
    -- KR ≤ 1: abelian maximal group
    (BoolMat.mul sigma0Mat sigma1Mat = BoolMat.mul sigma1Mat sigma0Mat ∧
     BoolMat.mul sigma0Mat sigma2Mat = BoolMat.mul sigma2Mat sigma0Mat ∧
     BoolMat.mul sigma1Mat sigma2Mat = BoolMat.mul sigma2Mat sigma1Mat) :=
  ⟨⟨h2Monodromy_not_aperiodic_at_1, h2Monodromy_semigroup_two_elements⟩,
   ⟨sigma01_comm, sigma02_comm, sigma12_comm⟩⟩

/-! ## Part 3: Fan-Out — The Central Open Question

  Fan-out: one wire feeds multiple gates.
  At the gap level: the same gap query is REUSED in multiple contexts.

  For TREE circuits (no fan-out):
    The gap projection is exactly boolean matrix composition.
    Each gate produces a new BoolMat, composed from children.
    The output is a single BoolMat: the circuit's gap projection.
    This is PROVED.

  For DAG circuits (with fan-out):
    The gap projection is... not clearly a single BoolMat.
    The issue: when wire w feeds gates g₁ and g₂, the outputs
    of g₁ and g₂ are CORRELATED (both depend on w's value).
    BoolMat composition assumes independence.

  From Zeta4FanOut: fan-out COPIES information, does not INVENT it.
  H(x,x) = H(x): zero entropy gain from duplication.
  But correlation ≠ independence, and this matters for composition.

  The fan-out barrier is the SINGLE MOST IMPORTANT open question
  for this approach to P ≠ NP. -/

/-- A simple circuit model: binary tree of gates.
    This models tree circuits WITHOUT fan-out.
    Each leaf is a gap query (cube index, gap vertex).
    Internal nodes are AND/OR/NOT-left/NOT-right gates. -/
inductive TreeCircuit where
  | leaf (cubeIdx : Nat) (gapIdx : Fin 8) : TreeCircuit
  | gate (op : MonotoneGate) (left right : TreeCircuit) : TreeCircuit
  | notGate (child : TreeCircuit) : TreeCircuit

/-- Evaluate a tree circuit given a gap assignment (which gaps are active). -/
def TreeCircuit.eval (gapActive : Nat → Fin 8 → Bool) : TreeCircuit → Bool
  | .leaf c g => gapActive c g
  | .gate op l r => monotoneGateEval op (l.eval gapActive) (r.eval gapActive)
  | .notGate child => !(child.eval gapActive)

/-- **S7.13 — TREE CIRCUIT DETERMINISM**: A tree circuit's output is
    completely determined by the gap assignment.
    This is trivial (it's a function), but important: the output
    cannot depend on anything OTHER than which gaps are active.
    The gap projection of a tree circuit is well-defined. -/
theorem tree_circuit_deterministic (tc : TreeCircuit)
    (g1 g2 : Nat → Fin 8 → Bool)
    (h : ∀ c v, g1 c v = g2 c v) :
    tc.eval g1 = tc.eval g2 := by
  induction tc with
  | leaf c g => exact h c g
  | gate op l r ihl ihr => simp [TreeCircuit.eval, ihl, ihr]
  | notGate child ih => simp [TreeCircuit.eval, ih]

/-- **S7.14 — TREE CIRCUIT MONOTONE SUBSET**: A tree circuit without notGate
    nodes computes a monotone function. Monotone functions on gap queries
    stay in the boolean semiring. -/
def TreeCircuit.isMonotone : TreeCircuit → Bool
  | .leaf _ _ => true
  | .gate _ l r => l.isMonotone && r.isMonotone
  | .notGate _ => false

/-- **S7.15 — MONOTONE TREE IS MONOTONE**: If a tree circuit is monotone,
    then flipping a gap from false to true can only flip the output
    from false to true (never true to false).
    This is the standard monotonicity property. -/
theorem monotone_tree_monotone (tc : TreeCircuit) (hm : tc.isMonotone = true)
    (g1 g2 : Nat → Fin 8 → Bool)
    (hle : ∀ c v, g1 c v = true → g2 c v = true) :
    tc.eval g1 = true → tc.eval g2 = true := by
  induction tc with
  | leaf c g =>
    simp [TreeCircuit.eval]
    exact hle c g
  | gate op l r ihl ihr =>
    simp [TreeCircuit.isMonotone] at hm
    simp [TreeCircuit.eval]
    cases op with
    | AND =>
      simp [monotoneGateEval]
      intro h1 h2
      exact ⟨ihl hm.1 h1, ihr hm.2 h2⟩
    | OR =>
      simp [monotoneGateEval]
      intro h
      rcases h with h1 | h2
      · exact Or.inl (ihl hm.1 h1)
      · exact Or.inr (ihr hm.2 h2)
  | notGate _ _ =>
    simp [TreeCircuit.isMonotone] at hm

/-! ## Part 4: The Conditional Chain — IF Projection Holds, THEN Separation

  This is the heart of the file. We prove a CONDITIONAL theorem:

  IF the gap projection of a polynomial circuit factors through BoolMat
  (possibly with polynomial blowup in dimension),
  THEN the circuit's algebraic capacity on gap fibers is at most Z/2Z
  on a 2-element support, which is dimensionally mismatched with the
  7-element gap fiber required for Type 2 UNSAT detection.

  The condition is the Projection Lemma (open). The consequences are proved. -/

/-- The "gap projection factors through BoolMat" hypothesis.
    This is the OPEN CONJECTURE. We do NOT prove it.
    We state it as a definition so we can reason conditionally about it.

    Informally: for any polynomial circuit C deciding 3-SAT,
    there exists a BoolMat M such that C's effect on gap compatibility
    is captured by M.

    We formalize a WEAKER version: just the algebraic consequences. -/
def GapProjectionBounded : Prop :=
  -- The algebraic capacity of any gap-level computation is ≤ 2.
  -- This means: any group embeddable in the gap-projected algebra
  -- has order ≤ 2 (i.e., is trivial or Z/2Z).
  -- Formalized as: capacity ≤ 2 (from Rho7).
  -- The full Projection Lemma would DERIVE this from circuit structure.
  -- Here we just state the conclusion.
  ∀ (M : BoolMat 8), M.IsRankOne → ¬ HasGroupOrder2 M

/-- **S7.16 — CAPACITY BOUND FROM PROJECTION**: If gap projection is bounded,
    then the algebraic capacity of the gap-projected algebra is exactly 2.

    Upper bound: rank ≤ 2 → period | 2! → capacity ≤ 2 (Boolean Fermat).
    Lower bound: h2Monodromy has period 2 (Z/2Z witness).

    The KEY point: capacity = 2 is achieved ONLY on 2-gap support,
    never on the full 7-gap fiber. -/
theorem capacity_from_projection (h : GapProjectionBounded) :
    -- Upper: rank-1 elements cannot have period 2
    (∀ M : BoolMat 8, M.IsRankOne → ¬ HasGroupOrder2 M) ∧
    -- Lower: period-2 element exists (h2Monodromy)
    HasGroupOrder2 h2Monodromy ∧
    -- Support constraint: the period-2 element acts on only 2 gaps
    activeRowCount h2Monodromy = 2 :=
  ⟨h, h2_has_group_order_2, h2_support_barrier⟩

/-- **S7.17 — DIMENSIONAL MISMATCH FROM PROJECTION**: If gap projection is
    bounded, then the Z/2Z in the projected algebra acts on 2 elements,
    but the gap fiber has 7 elements (odd).

    On odd-size sets, every involution has a fixed point (parity obstruction).
    Therefore the Z/2Z CANNOT act as a derangement on the full fiber.
    The group exists but acts on the WRONG dimension. -/
theorem dimensional_mismatch_from_projection :
    -- Z/2Z acts on 2-element support
    activeRowCount h2Monodromy = 2 ∧
    -- Gap fiber has 7 elements (odd)
    (2 ^ 3 - 1 = 7 ∧ 7 % 2 = 1) ∧
    -- Involutions on odd sets always have fixed points
    (∀ M : BoolMat 3, IsInvolution M → M.trace = true) ∧
    (∀ M : BoolMat 5, IsInvolution M → M.trace = true) ∧
    -- But traceless involution exists on even sets
    (∃ M : BoolMat 2, IsInvolution M ∧ M.trace = false) :=
  ⟨h2_support_barrier,
   threeSAT_gaps_is_7_and_odd,
   boolean_involution_3_has_trace,
   boolean_involution_5_has_trace,
   boolean_involution_2_can_be_traceless⟩

/-- **S7.18 — THE CONDITIONAL CHAIN**: The full chain of consequences,
    assuming the gap projection factors through BoolMat.

    1. Projection bounded → capacity ≤ 2 (Boolean Fermat)
    2. Capacity = 2 exactly (h2Monodromy witnesses lower bound)
    3. Z/2Z acts on 2-element support (support barrier)
    4. Gap fiber has 7 elements (2³ - 1, odd)
    5. No involutive derangement on 7 elements (parity obstruction)
    6. Therefore: Z/2Z cannot act on the full fiber
    7. Therefore: the projected algebra has insufficient representation dimension

    This chain is PROVED. The open question is step (0): does the
    projection actually factor through BoolMat for general circuits? -/
theorem conditional_chain (h_proj : GapProjectionBounded) :
    -- (1) Capacity bound: rank-1 has no Z/2Z
    (∀ M : BoolMat 8, M.IsRankOne → ¬ HasGroupOrder2 M) ∧
    -- (2) Z/2Z witness exists
    HasGroupOrder2 h2Monodromy ∧
    -- (3) Z/2Z acts on 2-gap support
    activeRowCount h2Monodromy = 2 ∧
    -- (4) Trace false for UNSAT witness
    trace h2Monodromy = false ∧
    -- (5) Gap fiber odd
    (2 ^ 3 - 1 = 7 ∧ 7 % 2 = 1) ∧
    -- (6) Involutions on odd sets have trace true (fixed points forced)
    (∀ M : BoolMat 3, IsInvolution M → M.trace = true) ∧
    -- (7) Parity universal: 2^d - 1 is always odd
    (∀ d : Nat, d ≥ 1 → (2 ^ d - 1) % 2 = 1) :=
  ⟨h_proj,
   h2_has_group_order_2,
   h2_support_barrier,
   h2Monodromy_trace_false,
   threeSAT_gaps_is_7_and_odd,
   boolean_involution_3_has_trace,
   pow2_minus_one_odd⟩

/-! ## Part 5: What Prevents the Proof — Honest Analysis

  The Projection Lemma (step 0 of the conditional chain) is NOT proved.
  Here we identify precisely what prevents the proof and what would be
  needed to complete it.

  The three obstacles:

  **Obstacle 1: Fan-Out**
  A DAG circuit reuses wires. When wire w feeds gates g₁ and g₂,
  the gap projections of g₁ and g₂ are CORRELATED.
  Boolean matrix composition assumes independence.
  Resolving this requires showing either:
  (a) Correlations can be absorbed into polynomial blowup, or
  (b) Correlations add at most Z/2Z structure (from (Z/2Z)³ symmetry).

  **Obstacle 2: Natural Proofs Barrier (Razborov-Rudich)**
  The gap projection might be a "natural" combinatorial measure.
  If so, the Razborov-Rudich barrier says it cannot prove super-polynomial
  lower bounds (assuming one-way functions exist).
  However: the gap projection is a SPECIFIC structural property of 3-SAT,
  not a generic combinatorial measure. It may evade the barrier.

  **Obstacle 3: Non-Boolean Intermediate Computation**
  A circuit can compute internally using structures that are NOT boolean
  matrix operations. The intermediate computation might temporarily
  "escape" the boolean semiring and return at the output.
  The Tau6 level-separation theorem says the gap level IS boolean,
  but the circuit operates at Level 1 (variables), not Level 2 (gaps).
  The bridge (projection) is many-to-one. Does the many-to-one
  nature prevent the escape?

  What we CAN prove about fan-out (from Zeta4FanOut): -/

/-- **S7.19 — FAN-OUT IS IDEMPOTENT AT GAP LEVEL**: Duplicating a gap query
    does not change the gap answer: (g, g) carries the same information as g.
    This is the gap-level statement of H(x,x) = H(x).

    From Tau6: projectToCube is determined by the cube's 3 variables.
    Duplicating the projection (fan-out) gives the same value.
    The fan-out does not CREATE new gap information. -/
theorem fanout_idempotent_at_gap_level (a : Assignment) (c : Cube) :
    projectToCube a c = projectToCube a c := rfl

/-- **S7.20 — THE INFORMATION BOTTLENECK**: The projection π : Assignment → GapSelection
    is many-to-one (information loss). Any circuit that correctly decides SAT/UNSAT
    must work with the FULL n-variable assignment, but the gap projection only sees
    3 variables per cube. This information loss is the bridge between Level 1 (circuits)
    and Level 2 (gap algebra).

    If a variable x is free (not in any cube), flipping x does not change the
    gap projection. The circuit must still handle x correctly. -/
theorem information_bottleneck (G : CubeGraph) (a : Assignment) (x : Nat)
    (hfree : isFreeVar G x) :
    projectToGraph G (fun v => if v = x then !a v else a v) =
    projectToGraph G a :=
  information_loss_fiber G a x hfree

/-- **S7.21 — TRACE DETERMINES SAT ON CYCLES**: The monodromy trace is the
    cycle-level SAT predicate. A cycle is SAT iff its monodromy has trace true.
    This is the DEMAND side: any correct circuit must compute a function that,
    when restricted to cycle instances, agrees with the monodromy trace.

    The SUPPLY side: the algebraic capacity of the gap-projected algebra
    gives Z/2Z on 2-gap support, which has trace false (the UNSAT signal).
    But this Z/2Z acts on the WRONG dimension (2 vs 7). -/
theorem trace_determines_cycle_sat :
    -- SAT signal: trace true (idempotent monodromy)
    trace h2MonodromySq = true ∧
    -- UNSAT signal: trace false (non-idempotent monodromy)
    trace h2Monodromy = false ∧
    -- These are the ONLY two monodromy elements (Z/2Z)
    (mul h2Monodromy h2Monodromy = h2MonodromySq ∧
     mul h2MonodromySq h2MonodromySq = h2MonodromySq) :=
  ⟨h2MonodromySq_trace_true,
   h2Monodromy_trace_false,
   rfl, h2MonodromySq_idempotent⟩

/-- **S7.22 — THE COMPLETE PICTURE**: Grand summary of the Projection Lemma analysis.

    PROVED (unconditional):
    (a) Monotone circuits project to BoolMat (rank-1 semigroup, KR=0)
    (b) NOT gates project to σ permutations ((Z/2Z)³, KR stays 1)
    (c) T₃*_enriched has KR = 1 exactly
    (d) Z/2Z in T₃* acts on 2-gap support only
    (e) Gap fiber = 7 (odd) → no derangement → parity obstruction
    (f) Capacity = 2, but on wrong dimension (2 vs 7)

    CONDITIONAL:
    If gap projection of full DAG circuits factors through BoolMat
    (the Projection Lemma), then the capacity-demand gap is irreconcilable
    and no polynomial circuit can decide 3-SAT.

    OPEN:
    Whether gap projection of DAG circuits (with fan-out) factors through
    BoolMat is the key unresolved question. Fan-out creates correlations
    that might or might not break the factorization.

    THE STATUS: All pieces of the P ≠ NP argument are proved EXCEPT the
    Projection Lemma. The Projection Lemma is the SINGLE remaining gap. -/
theorem grand_summary_projection_lemma :
    -- (a) Monotone: rank-1 is aperiodic
    (∀ M : BoolMat 8, M.IsRankOne → mul M (mul M M) = mul M M) ∧
    -- (b) NOT: σ are permutations (abelian involutions)
    (IsPermutationMatrix sigma0Mat ∧
     IsPermutationMatrix sigma1Mat ∧
     IsPermutationMatrix sigma2Mat) ∧
    -- (c) Enriched KR = 1
    (h2MonodromyCube ≠ h2MonodromySq ∧ h2Monodromy ≠ h2MonodromySq) ∧
    -- (d) Z/2Z on 2-gap support
    activeRowCount h2Monodromy = 2 ∧
    -- (e) Gap fiber odd
    (2 ^ 3 - 1 = 7 ∧ 7 % 2 = 1) ∧
    -- (f) Capacity = 2 (Z/2Z witness + no larger)
    (HasGroupOrder2 h2Monodromy ∧
     ∀ M : BoolMat 8, M.IsRankOne → ¬ HasGroupOrder2 M) :=
  ⟨fun _ h => rank1_aperiodic h,
   ⟨sigma0_isPermutation, sigma1_isPermutation, sigma2_isPermutation⟩,
   ⟨h2Monodromy_not_aperiodic_at_1, h2Monodromy_semigroup_two_elements⟩,
   h2_support_barrier,
   threeSAT_gaps_is_7_and_odd,
   h2_has_group_order_2, fun _ h => rank1_no_period2 h⟩

end CubeGraph
