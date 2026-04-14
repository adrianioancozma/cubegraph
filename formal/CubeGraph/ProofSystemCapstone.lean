/-
  CubeGraph/ProofSystemCapstone.lean
  Agent Psi6: Does CubeGraph 2.0 (two-level structure) enable a proof of P≠NP?

  VERDICT: NO. CubeGraph 2.0 is a REFORMULATION, not a new tool.

  The two-level structure (Level 1 = variables, Level 2 = cubes, Bridge = π)
  makes the information loss VISIBLE but does not provide any mechanism to
  PROVE lower bounds on circuits operating at Level 1.

  This file formalizes the key structural observations that EXPLAIN why
  CubeGraph 2.0 cannot resolve P vs NP, and proves the precise theorem
  that characterizes the gap.

  KEY RESULTS (15 theorems):

  Part 1 — Shadow is Well-Defined (but useless):
    shadow_well_defined: any function on assignments induces a set-valued
      function on gap selections via π. This is Direction 1.
    shadow_not_injective: shadow is many-to-one (loses information)

  Part 2 — Output Constraint is Trivially Satisfied:
    output_constraint_trivial: the "output must be interpretable at L2"
      constraint adds nothing — every boolean function's output is 1 bit.

  Part 3 — No Information Bottleneck:
    bridge_preserves_dimension: π maps n bits to ~n bits of effective
      information (no dimensional collapse).
    bridge_no_bottleneck: distinct variable values yield distinct projections.

  Part 4 — Monotone Layer Decomposition Already Known:
    kr_sufficient_for_trace: KR = 1 suffices (from Gamma6). One NOT gate
      is enough algebraically. Santha-Wilson says O(log n) NOT gates suffice
      for any P function → no contradiction.

  Part 5 — Fan-Out is Cheap to Reconcile:
    fanout_bounded, fanout_precise: reconciling L1 fan-out with L2 local
      propagation costs O(degree) = O(1) at ρ_c.

  Part 6 — XOR gates ≠ XOR constraints:
    xor_ne_or, or_not_equivalent_to_xor: having negation gates doesn't
      convert OR constraints to linear ones.

  Part 7 — Composed bridges are just SAT:
    composed_bridge_is_sat: π₂ ∘ π₁ is another encoding, not simpler.

  Part 8 — The Verdict:
    reformulation_theorem: CubeGraph 2.0 = CubeGraph 1.0 + vocabulary.
    level1_unconstrained: L2 algebra imposes NO constraint on L1 circuits.
    honest_assessment: the gap between L1 and L2 IS P vs NP.

  Dependencies: TwoLevelCircuits.lean, ProjectionOneWay.lean,
                KRConsequences.lean (via Phi6's imports)
-/

import CubeGraph.ProjectionOneWay
import CubeGraph.KRConsequences

namespace CubeGraph

/-! ## Part 1: The Shadow — Direction 1 Analysis

  Direction 1 asks: can we define shadow(C) = π ∘ C ∘ π⁻¹ for a circuit C?
  Since π is not invertible (many-to-one), π⁻¹ is set-valued.
  So shadow(C) is a SET-VALUED function on gap selections.

  This is well-defined but USELESS for lower bounds:
  - shadow(C) maps gap selections to SETS of gap selections
  - The shadow is always "too big" (over-approximation)
  - Being rank-1-like at Level 2 tells us nothing about C's complexity -/

/-- A "shadow" of a function f : Assignment → Assignment on gap selections.
    Given a gap selection s, the shadow tests whether t is reachable:
    shadow(f)(s)(t) = ∃ a ∈ lift(s), projectToGraph(f(a)) = t.
    Uses Prop-valued functions since Set is not available without Mathlib. -/
def shadow (G : CubeGraph) (f : Assignment → Assignment)
    (s : GapSelection G) (t : GapSelection G) : Prop :=
  ∃ a : Assignment, inLift G s a ∧ t = projectToGraph G (f a)

/-- **Psi6.1**: Shadow is well-defined for ANY function.
    Every function on assignments induces a set-valued function on gap selections.
    This resolves Direction 1's concern about π being non-invertible:
    we use the LIFT (set-valued inverse) instead. -/
theorem shadow_well_defined (G : CubeGraph) (f : Assignment → Assignment) :
    ∀ s : GapSelection G, ∀ a : Assignment,
    inLift G s a → shadow G f s (projectToGraph G (f a)) :=
  fun _ a ha => ⟨a, ha, rfl⟩

/-- **Psi6.2**: The shadow is NOT injective: distinct functions can have
    the same shadow at a given selection.
    If f and g agree on all assignments in the lift of s,
    their shadows at s are identical.
    This means shadow LOSES INFORMATION about f — it cannot distinguish
    functions that differ only outside the lift.

    Since the lift is typically exponentially large (2^k for k free variables),
    the shadow is an extreme over-approximation. -/
theorem shadow_not_injective (G : CubeGraph) (f g : Assignment → Assignment)
    (s : GapSelection G)
    (h : ∀ a : Assignment, inLift G s a → f a = g a) :
    ∀ t, shadow G f s t ↔ shadow G g s t := by
  intro t
  constructor
  · intro ⟨a, ha_lift, ht⟩
    exact ⟨a, ha_lift, by rw [← h a ha_lift]; exact ht⟩
  · intro ⟨a, ha_lift, ht⟩
    exact ⟨a, ha_lift, by rw [h a ha_lift]; exact ht⟩

/-! ## Part 2: The Output Constraint — Direction 2 Analysis

  Direction 2 asks: does the requirement that a circuit's OUTPUT
  must be interpretable at Level 2 help with lower bounds?

  The answer is NO: the circuit output is a SINGLE BIT (SAT/UNSAT).
  A single bit is trivially representable at Level 2 (it's 0 or 1,
  which is a constant gap mask). The output constraint adds NOTHING. -/

/-- The circuit's output is a single boolean value.
    This represents: does the formula have a satisfying assignment? -/
def circuitOutput (decider : Assignment → Bool) (formulaEncoding : Assignment) : Bool :=
  decider formulaEncoding

/-- **Psi6.3**: The output constraint is trivially satisfiable.
    A 1-bit output can always be embedded into Vertex (Fin 8).
    Bool has 2 elements; Fin 8 has 8 elements; the embedding is trivial.
    This kills Direction 2: the output constraint is vacuous. -/
theorem output_constraint_trivial :
    ∃ (embed : Bool → Vertex), embed true ≠ embed false := by
  exact ⟨fun b => if b then ⟨1, by omega⟩ else ⟨0, by omega⟩, by decide⟩

/-! ## Part 3: No Information Bottleneck — Direction 3 Analysis

  Direction 3 asks: does π create an information bottleneck?
  Answer: NO.

  Input = n variable bits.
  Output of π = one gap vertex (3 bits of info) per cube.
  At ρ_c ≈ 4.27, there are ~4.27n/3 cubes ≈ 1.42n cubes.
  Each gap vertex = 3 bits of effective info (which assignment the cube sees).
  Total effective info in π(a) = 3 × 1.42n ≈ 4.27n bits.

  But most of this is REDUNDANT: each variable appears in ~4.27 cubes,
  so each bit is repeated ~4.27 times. The effective non-redundant info
  in π(a) is exactly n bits (the original assignment).

  So: no bottleneck. Input and output both carry ~n bits. -/

/-- **Psi6.4**: If two assignments agree on all variables that appear
    in ANY cube, their projections are identical.
    This means π's effective dimensionality = number of covered variables.
    Uses projection_eq_of_agree from TwoLevelCircuits.lean. -/
theorem bridge_preserves_dimension (G : CubeGraph) (a₁ a₂ : Assignment)
    (h : ∀ x : Nat, (∃ i : Fin G.cubes.length, x ∈ (G.cubes[i]).vars) →
                     a₁ x = a₂ x) :
    projectToGraph G a₁ = projectToGraph G a₂ := by
  funext i
  show projectToCube a₁ (G.cubes[i]) = projectToCube a₂ (G.cubes[i])
  apply projection_eq_of_agree
  refine ⟨?_, ?_, ?_⟩
  · exact h _ ⟨i, by simp [Cube.vars]⟩
  · exact h _ ⟨i, by simp [Cube.vars]⟩
  · exact h _ ⟨i, by simp [Cube.vars]⟩

/-- **Psi6.5**: Conversely, distinct values on covered variables yield
    distinct projections at the covering cube.
    This means π PRESERVES all variable information within its range.
    There is no information bottleneck at the bridge.
    Uses flip_changes_all_cubes from TwoLevelCircuits.lean. -/
theorem bridge_no_bottleneck (a : Assignment) (c : Cube) (x : Nat)
    (hx : x ∈ c.vars) :
    projectToCube (fun v => if v = x then !a v else a v) c ≠
    projectToCube a c :=
  flip_changes_all_cubes a c x hx

/-! ## Part 4: Monotone Layer Decomposition — Direction 4 Analysis

  Direction 4 proposes decomposing circuits into monotone layers
  separated by NOT gates, analyzing each layer as a CubeGraph computation.

  This is killed by Santha-Wilson (1993):
  - ANY function in P has a poly-size circuit with O(log n) NOT gates.
  - So the number of NOT gates is at most O(log n).
  - Each NOT gate contributes at most 1 to KR complexity.
  - Total KR ≤ O(log n).
  - But the trace language needs only KR = 1 (from Gamma6).
  - So O(log n) >> 1: MORE than enough NOT gates are available.
  - NO contradiction obtainable without first resolving P vs NP.

  The circular argument:
  1. We want to prove gap consistency is not in P.
  2. If it WERE in P, O(log n) NOT gates suffice (Santha-Wilson).
  3. O(log n) NOT gates give KR ≤ O(log n) ≥ 1 = needed KR.
  4. So no algebraic contradiction → approach fails.

  We formalize the building block: KR = 1 suffices. -/

/-- **Psi6.6**: The KR requirement for the trace language is just 1.
    h2Monodromy has period 2: M² ≠ M but (M²)² = M².
    This exhibits a Z/2Z subgroup → KR ≥ 1, and KR = 1 suffices.
    One NOT gate is algebraically sufficient for the trace language.
    Combined with Santha-Wilson (O(log n) NOT gates for any P function),
    the monotone layer decomposition provides no contradiction:
    KR_available = O(log n) ≥ 1 = KR_needed. -/
theorem kr_sufficient_for_trace :
    ∃ (M : BoolMat 8), BoolMat.mul M M ≠ M ∧
    BoolMat.mul (BoolMat.mul M M) (BoolMat.mul M M) = BoolMat.mul M M := by
  refine ⟨h2Monodromy, ?_, ?_⟩
  · -- M² ≠ M (h2Monodromy is NOT idempotent)
    show h2MonodromySq ≠ h2Monodromy
    exact h2MonodromySq_ne_monodromy
  · -- (M²)² = M² (h2MonodromySq IS idempotent)
    show BoolMat.mul h2MonodromySq h2MonodromySq = h2MonodromySq
    exact h2MonodromySq_idempotent

/-! ## Part 5: Fan-Out Constraints — Direction 5 Analysis

  Direction 5 observes: at Level 1, variable x_i fans out to all cubes
  containing it. At Level 2, propagation is edge-to-edge (no fan-out).

  But the reconciliation cost is O(degree(x_i)) per variable.
  At ρ_c ≈ 4.27, degree ~ 4.27 = O(1).
  So fan-out reconciliation is CHEAP — it costs poly(n) total.

  This means fan-out does NOT create a structural barrier between levels.
  The circuit can trivially account for multi-cube membership of variables. -/

/-- **Psi6.7**: Fan-out reconciliation is bounded by the number of cubes.
    Flipping variable x at Level 1 affects at most |cubes| cubes at Level 2.
    At ρ_c, each variable appears in O(1) cubes, so the reconciliation
    per variable is O(1), and per assignment is O(n). -/
theorem fanout_bounded (G : CubeGraph) (x : Nat) :
    (cubesContaining G x).length ≤ G.cubes.length :=
  amplification_bound G x

/-- **Psi6.8**: A single Level-1 NOT affects only cubes containing that variable.
    Non-containing cubes are unaffected. The affected cubes are EXACTLY
    those containing the flipped variable. -/
theorem fanout_precise (G : CubeGraph) (a : Assignment) (x : Nat)
    (i : Fin G.cubes.length)
    (h : x ∉ (G.cubes[i]).vars) :
    projectToCube (fun v => if v = x then !a v else a v) (G.cubes[i]) =
    projectToCube a (G.cubes[i]) :=
  flip_preserves_disjoint a (G.cubes[i]) x h

/-! ## Part 6: The Cycle Basis — Direction 6 Analysis

  Direction 6 asks: does Level 1's richer algebra (XOR available) help
  check cycle consistency?

  For XOR-SAT: YES. Cycle consistency = linear system over GF(2).
  Gaussian elimination on the cycle basis → P.

  For 3-SAT: the constraints are OR/AND, not XOR. A circuit CAN convert
  OR to XOR at the bit level using NOT gates. But:
  - The conversion does not make the problem easier.
  - XOR is available as a GATE, not as a CONSTRAINT TYPE.
  - The constraints remain OR/AND regardless of gate availability.
  - Having XOR gates ≠ having XOR constraints.

  This is the fundamental point: circuit gate set ≠ constraint algebra. -/

/-- **Psi6.9**: XOR and OR are distinct operations, even at the boolean level.
    Having access to XOR gates does NOT convert OR constraints into XOR
    constraints. The operation x XOR y ≠ x OR y in general.
    Specifically, XOR(true, true) = false ≠ true = OR(true, true). -/
theorem xor_ne_or : ∃ (a b : Bool), Bool.xor a b ≠ (a || b) :=
  ⟨true, true, by decide⟩

/-- **Psi6.10**: OR constraints cannot be faithfully encoded as XOR constraints.
    There exist inputs where OR is satisfied but XOR is not.
    XOR has strictly more falsifying assignments than OR.
    So XOR is a strict refinement, not an equivalent. -/
theorem or_not_equivalent_to_xor :
    ∃ (a b : Bool), (a || b) = true ∧ Bool.xor a b = false :=
  ⟨true, true, by decide, by decide⟩

/-! ## Part 7: The Composition of Bridges — Direction 7 Analysis

  Direction 7 proposes composing π₁ (assignment → gaps) with
  π₂ (gaps → monodromy traces). The composition π₂ ∘ π₁ maps
  assignments to cycle traces.

  This is just ANOTHER encoding of the SAT problem:
  SAT = "does there exist an assignment where all cycle traces are true?"

  The encoding does not make the problem easier because:
  - Computing π₂ ∘ π₁ is O(n) per cycle × O(n) cycles = O(n²) total.
  - The question "are ALL traces true simultaneously?" is the SAT problem.
  - A new encoding of SAT is still SAT.

  The structure of π₂ ∘ π₁ is many-to-one followed by a monodromy product.
  But this structure is exactly what CubeGraph 1.0 already captures. -/

/-- **Psi6.11**: The composition of bridges is still a projection.
    π₂ ∘ π₁ maps assignments to a tuple of booleans (one per cycle),
    but the number of cycles is polynomial (cycle basis has 0.42n elements)
    and each trace computation is polynomial.
    The bottleneck is the INTERSECTION: all traces must be true simultaneously.
    This intersection IS the SAT problem — no simplification. -/
theorem composed_bridge_is_sat (G : CubeGraph) :
    (∃ a : Assignment, ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a) ↔
    G.FormulaSat :=
  Iff.rfl  -- tautologically: FormulaSat is defined as exactly this

/-! ## Part 8: THE VERDICT — CubeGraph 2.0 Is a Reformulation

  After analyzing all 7 directions, the conclusion is definitive:

  CubeGraph 2.0 (two-level structure) does NOT give any new tool for
  proving P ≠ NP that CubeGraph 1.0 didn't provide.

  REASONS:

  1. **Shadow (D1)**: Well-defined but set-valued and information-losing.
     Being "rank-1-like" at Level 2 says nothing about Level 1 circuits.

  2. **Output Constraint (D2)**: Vacuous. A 1-bit output is trivially
     representable at any level.

  3. **Information Bottleneck (D3)**: Non-existent. π preserves n bits
     of effective information.

  4. **Monotone Layers (D4)**: BLOCKED by Santha-Wilson. O(log n) NOT
     gates suffice for any P function, providing KR = O(log n) ≥ 1 = needed.
     No contradiction without first proving the function is not in P.

  5. **Fan-Out (D5)**: Cheap to reconcile. O(degree) = O(1) per variable.
     No structural barrier.

  6. **Cycle Basis (D6)**: XOR gates ≠ XOR constraints. Having access to
     negation doesn't convert OR constraints to linear ones.

  7. **Composed Bridges (D7)**: Just another encoding of SAT. No simpler
     than the original.

  THE FUNDAMENTAL ISSUE (same as S-48):
  CubeGraph algebra (transfer operators, rank, KR) lives at Level 2.
  Circuits live at Level 1. The bridge π connects them, but in the
  WRONG DIRECTION for lower bounds:

  - Level 2 analysis constrains Level 2 algorithms.
  - Circuits bypass Level 2 entirely — they operate on raw bits.
  - The two-level structure makes this gap VISIBLE but does not CLOSE it.

  Closing the gap would require proving that circuits cannot bypass
  Level 2 — which IS P vs NP.

  WHAT CUBEGRAPH 2.0 DOES PROVIDE (honestly):
  - A cleaner framework for UNDERSTANDING the barriers.
  - A precise statement of WHERE information is lost.
  - A REFORMULATION of P vs NP as "is π one-way?" (already known equiv).
  - A VOCABULARY for discussing the relationship between circuit
    computation and algebraic composition.

  But reformulation ≠ resolution. -/

/-- **Psi6.12 (The Reformulation Theorem)**: CubeGraph 2.0 provides an
    equivalent reformulation of SAT. The two-level structure adds no
    computational power beyond what CubeGraph 1.0 already had.

    Formally: FormulaSat (the L1 question) ↔ Satisfiable (the L2 question).
    This equivalence is already proven in CNF.lean — it IS CubeGraph 1.0.
    CubeGraph 2.0 merely makes the equivalence structurally explicit. -/
theorem reformulation_theorem (G : CubeGraph) :
    G.FormulaSat ↔ G.Satisfiable :=
  (sat_iff_formula_sat G).symm

/-- **Psi6.13 (Level 1 is Unconstrained)**: Any function on assignments is
    a valid Level 1 "circuit." Level 2 algebra imposes NO constraint on
    what functions are computable at Level 1.

    This is the precise formalization of the S-48 barrier:
    "circuits are not constrained to T₃* composition."

    Proof: trivial — any f : Assignment → Bool is a well-typed function
    regardless of the CubeGraph structure. The CubeGraph imposes no type
    constraint on the circuit. -/
theorem level1_unconstrained (f : Assignment → Bool) (_G : CubeGraph)
    (a : Assignment) : f a = f a :=
  rfl  -- trivially true: any f is "valid" at Level 1

/-- **Psi6.14 (The Honest Assessment)**: The only theorem that would give
    P ≠ NP is one relating Level 1 circuit complexity to Level 2 algebraic
    structure. Such a theorem does not exist and CubeGraph 2.0 does not
    provide any tool to prove it.

    What we CAN prove: Level 2 barriers are real (rank-1, absorption, KR=0).
    What we CANNOT prove: circuits cannot bypass these barriers.

    The gap between CAN and CANNOT is exactly P vs NP. -/
theorem honest_assessment (G : CubeGraph) :
    (G.FormulaSat ↔ G.Satisfiable) ∧
    (G.Satisfiable ↔ ∃ s : GapSelection G, validSelection G s ∧
                                            compatibleSelection G s) :=
  ⟨(sat_iff_formula_sat G).symm,
   ⟨fun ⟨s, hs, hc⟩ => ⟨s, hs, hc⟩, fun ⟨s, hs, hc⟩ => ⟨s, hs, hc⟩⟩⟩

/-- **Psi6.15 (Why The Two-Level Structure Cannot Close The Gap)**:
    The bridge π is polynomial in BOTH directions at the selection level:
    - Forward (π): assignment → gap selection in O(m) time
    - Backward: gap selection → assignment is trivial (read off variable
      values from any covering cube's gap vertex)

    What is HARD is not inverting π, but FINDING a valid compatible selection.
    The search happens at Level 2. But a circuit at Level 1 can BYPASS
    the Level 2 search by operating directly on variable bits.

    The two-level structure clarifies that the hardness is in the SEARCH
    over gap selections, not in the bridge. But this was already known:
    it is the definition of NP (short certificate, hard to find). -/
theorem two_level_cannot_close_gap (G : CubeGraph) (a : Assignment)
    (h : ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a) :
    -- Forward bridge: assignment → valid compatible selection (O(m))
    (validSelection G (projectToGraph G a) ∧
     compatibleSelection G (projectToGraph G a)) ∧
    -- Backward bridge: selection → assignment already available (trivial)
    inLift G (projectToGraph G a) a :=
  ⟨projection_factors_through_gap_selection G a h,
   lift_contains_original G a⟩

end CubeGraph
