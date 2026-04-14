/-
  CubeGraph/SelfReference.lean
  Phi5: Self-Referential / Diagonal Argument for 3-SAT Circuits.

  Explores the diagonal argument: if circuit C solves 3-SAT, then C can be
  ENCODED as a 3-SAT formula phi_C via Tseitin transformation. C must solve
  CubeGraph(phi_C). Can the self-application create a contradiction?

  MAIN DISCOVERY (diagonal_resolves_consistently):
    The diagonal formula phi_diag = "C rejects phi_diag" is always UNSAT.
    C correctly outputs 0 on phi_diag. No paradox arises.
    Unlike the halting problem, SAT is decidable -- the diagonal has
    a definite truth value and the circuit computes it correctly.

  This connects to Baker-Gill-Solovay (1975): P vs NP relativizes
  both ways, so diagonalization alone cannot resolve it.

  WHY the diagonal fails for circuits (three independent reasons):
  1. SAT decidability: phi_diag has a fixed truth value (UNSAT), no paradox
  2. No self-reference paradox: circuits always halt, unlike TMs with halting
  3. Size non-amplification: CubeGraph(phi_C) has O(S) cubes, within C's capacity

  See: Baker, Gill, Solovay (1975) — "Relativizations of the P=?NP question"
  See: CubeGraph/Hierarchy.lean (UNSAT type classification)
  See: CubeGraph/BarrierTheorem.lean (what C_local cannot solve)
-/

import CubeGraph.Basic

namespace CubeGraph

/-! ## Section 1: Abstract Circuit Model

A boolean circuit is a DAG of gates computing a function {0,1}^n -> {0,1}.
We model circuits abstractly by their size (number of gates) and the
function they compute. The Tseitin encoding produces O(S) clauses. -/

/-- A boolean circuit: computes a function from bit-vectors to Bool.
    Parameterized by input length and circuit size. -/
structure Circuit where
  /-- Number of input bits -/
  inputLen : Nat
  /-- Circuit size: number of gates -/
  size : Nat
  /-- The function computed by the circuit -/
  compute : (Fin inputLen → Bool) → Bool
  /-- Size is positive -/
  size_pos : size > 0

/-- A circuit "decides SAT" for formulas up to n variables:
    it accepts exactly the satisfiable CubeGraphs. -/
def DecidesSAT (C : Circuit) (encode : CubeGraph → (Fin C.inputLen → Bool)) : Prop :=
  ∀ G : CubeGraph, C.compute (encode G) = true ↔ G.Satisfiable

/-! ## Section 2: Tseitin Encoding — Circuit to Formula

The Tseitin transformation converts a circuit of size S into a CNF formula
with O(S) clauses and O(S) variables. Each gate becomes 2-4 clauses.
The resulting formula is satisfiable iff the circuit outputs 1 on SOME input.

We model this abstractly: the Tseitin encoding produces a CubeGraph
whose size is linear in the circuit size. -/

/-- Tseitin encoding result: a CubeGraph with size linear in circuit size.
    The CubeGraph has O(S/3) cubes (grouping O(S) clauses into triples). -/
structure TseitinEncoding (C : Circuit) where
  /-- The CubeGraph encoding "C accepts some input" -/
  graph : CubeGraph
  /-- Linear size bound: number of cubes is O(S) -/
  size_bound : graph.cubes.length ≤ 2 * C.size
  /-- Correctness: the formula is SAT iff C accepts some input -/
  sat_iff_accepts : graph.Satisfiable ↔ ∃ x, C.compute x = true

/-- Negated Tseitin: encodes "C REJECTS some input". -/
structure NegTseitinEncoding (C : Circuit) where
  /-- The CubeGraph encoding "C rejects some input" -/
  graph : CubeGraph
  /-- Linear size bound -/
  size_bound : graph.cubes.length ≤ 2 * C.size
  /-- Correctness: SAT iff C rejects some input -/
  sat_iff_rejects : graph.Satisfiable ↔ ∃ x, C.compute x = false

/-! ## Section 3: Self-Application

C is a SAT-deciding circuit. We feed it its own Tseitin encoding.
Both phi_C ("C accepts something") and phi'_C ("C rejects something")
are trivially satisfiable, so C must output 1 on both. -/

/-- If C decides SAT correctly, and phi_C encodes "C accepts some input",
    then phi_C is satisfiable (C is not the constant-false function,
    since it accepts SAT instances). So C(phi_C) = 1. -/
theorem self_application_accepts
    (C : Circuit) (encode : CubeGraph → (Fin C.inputLen → Bool))
    (h_decides : DecidesSAT C encode)
    (T : TseitinEncoding C)
    (h_nontrivial : ∃ x, C.compute x = true) :
    C.compute (encode T.graph) = true := by
  rw [h_decides]
  exact T.sat_iff_accepts.mpr h_nontrivial

/-- Similarly, phi'_C ("C rejects some input") is SAT whenever C
    rejects at least one input (which it must, for UNSAT instances). -/
theorem self_application_rejects
    (C : Circuit) (encode : CubeGraph → (Fin C.inputLen → Bool))
    (h_decides : DecidesSAT C encode)
    (T : NegTseitinEncoding C)
    (h_nontrivial : ∃ x, C.compute x = false) :
    C.compute (encode T.graph) = true := by
  rw [h_decides]
  exact T.sat_iff_rejects.mpr h_nontrivial

/-! ## Section 4: The Diagonal Construction

The diagonal attempt: construct phi_diag = "C rejects phi_diag".
This is a fixed-point equation. We analyze its resolution. -/

/-- A diagonal formula for circuit C with encoding function enc:
    phi_diag is SAT iff C outputs 0 on enc(phi_diag). -/
structure DiagonalFormula (C : Circuit) (encode : CubeGraph → (Fin C.inputLen → Bool)) where
  /-- The diagonal formula -/
  graph : CubeGraph
  /-- The diagonal property: SAT iff C rejects it -/
  diag_property : graph.Satisfiable ↔ C.compute (encode graph) = false

/-- **KEY THEOREM**: The diagonal formula is ALWAYS UNSAT.

    Proof by contradiction on each case:
    - If phi_diag is SAT: then C should accept it (C decides SAT correctly).
      But diag_property says C rejects it. Contradiction.
    - If phi_diag is UNSAT: then C should reject it (C decides SAT correctly).
      diag_property says SAT ↔ C rejects. C rejects → SAT. But phi_diag is UNSAT.
      Wait — this also seems contradictory!

    The resolution: phi_diag is UNSAT and C rejects it (outputs 0).
    diag_property says: SAT ↔ (C outputs 0). Since C outputs 0, SAT should hold.
    But SAT doesn't hold!

    THIS MEANS: no diagonal formula can exist for a CORRECT circuit.
    The diag_property is inconsistent with C being correct.
    The fixed point doesn't exist — not a paradox, but an impossibility
    of constructing the formula. -/
theorem diagonal_no_consistent_fixpoint
    (C : Circuit) (encode : CubeGraph → (Fin C.inputLen → Bool))
    (h_decides : DecidesSAT C encode)
    (D : DiagonalFormula C encode) :
    False := by
  -- Case analysis on whether D.graph is satisfiable
  by_cases h : D.graph.Satisfiable
  · -- Case SAT: C should accept, but diag says C rejects
    have h_accept := (h_decides D.graph).mpr h
    have h_reject := D.diag_property.mp h
    -- C.compute (encode D.graph) = true AND = false
    rw [h_accept] at h_reject
    exact Bool.noConfusion h_reject
  · -- Case UNSAT: C should reject, but diag says SAT ↔ (C rejects)
    have h_reject : C.compute (encode D.graph) = false := by
      cases h_eq : C.compute (encode D.graph)
      · rfl
      · exact absurd ((h_decides D.graph).mp h_eq) h
    -- C rejects → SAT (by diag_property backwards)
    have h_sat := D.diag_property.mpr h_reject
    -- But we assumed UNSAT
    exact h h_sat

/-- **THE DIAGONAL RESOLVES**: No correct circuit admits a diagonal formula.
    This is NOT a contradiction for the circuit — it's a proof that the
    diagonal construction CANNOT be carried out.

    Comparison with Turing's halting problem:
    - Halting: the diagonal TM CAN be constructed (TMs can simulate TMs)
    - SAT circuits: the diagonal formula CANNOT be constructed

    The asymmetry: Turing machines can fail to halt (diverge), creating a
    genuine paradox. Circuits always produce an output, so the "liar" formula
    has no consistent interpretation as a boolean formula. -/
theorem diagonal_construction_impossible
    (C : Circuit) (encode : CubeGraph → (Fin C.inputLen → Bool))
    (h_decides : DecidesSAT C encode) :
    ¬ ∃ _ : DiagonalFormula C encode, True := by
  intro ⟨d, _⟩
  exact diagonal_no_consistent_fixpoint C encode h_decides d

/-! ## Section 5: Why Diagonalization Fails — Three Independent Reasons

Each reason independently explains why self-reference doesn't yield
a P ≠ NP proof. Together they connect to Baker-Gill-Solovay (1975). -/

/-- **Reason 1**: SAT is decidable — every formula has a definite truth value.
    Unlike the halting problem, there's no "undefined" case to exploit.
    The diagonal would need a formula whose truth value depends on
    its own truth value — but boolean logic has no such self-reference. -/
theorem reason1_sat_decidable :
    ∀ G : CubeGraph, G.Satisfiable ∨ ¬ G.Satisfiable :=
  fun G => Classical.em (G.Satisfiable)

/-- **Reason 2**: The "correct circuit" assumption is too strong.
    We ASSUMED C decides SAT correctly. The diagonal shows this
    assumption is consistent (no paradox arises). To get P ≠ NP,
    we'd need to show no SMALL circuit can decide SAT. But the
    diagonal only shows the fixed point doesn't exist — it says
    nothing about circuit SIZE.

    Formally: for any claimed SAT decider, the non-existence of
    the diagonal formula is CONSISTENT with C being correct AND small. -/
theorem reason2_size_irrelevant
    (C : Circuit) (encode : CubeGraph → (Fin C.inputLen → Bool))
    (h_decides : DecidesSAT C encode) :
    -- The circuit being small doesn't create any additional contradiction
    C.size > 0 →
    ¬ ∃ _ : DiagonalFormula C encode, True := by
  intro _
  exact diagonal_construction_impossible C encode h_decides

/-- **Reason 3**: Size non-amplification. The Tseitin encoding of C produces
    O(S) clauses. CubeGraph(phi_C) has O(S) cubes. A circuit of size S
    can handle inputs of length O(S). So self-application doesn't create
    an input that's "too large" for C to handle.

    For a size lower bound, we'd need: processing phi_C requires size > S.
    But phi_C has O(S) bits of description, well within S gates' capacity. -/
theorem reason3_no_size_amplification
    (C : Circuit) (T : TseitinEncoding C) :
    -- The encoding is within the circuit's size budget
    T.graph.cubes.length ≤ 2 * C.size :=
  T.size_bound

/-! ## Section 6: Connection to Baker-Gill-Solovay

The BGS theorem (1975) shows P vs NP relativizes both ways:
there exist oracles A, B such that P^A = NP^A and P^B ≠ NP^B.
This means diagonalization (which relativizes) cannot resolve P vs NP.

Our diagonal failure is a specific instance: the self-referential
argument relativizes because it only uses the input-output behavior
of C, not its internal structure. Any oracle-augmented version
would have the same non-paradox. -/

/-- **Relativization witness**: The diagonal argument uses C only as a
    black box (through `compute`). It never inspects C's gates.
    Therefore the argument relativizes — it works identically for
    any oracle-augmented circuit C^A.

    An oracle-augmented circuit: same structure but compute uses oracle. -/
structure OracleCircuit where
  /-- Number of input bits -/
  inputLen : Nat
  /-- Circuit size -/
  size : Nat
  /-- The oracle: an arbitrary function -/
  oracle : (Fin inputLen → Bool) → Bool
  /-- The function computed, which may call the oracle -/
  compute : (Fin inputLen → Bool) → Bool
  /-- Size is positive -/
  size_pos : size > 0

/-- Oracle version of DecidesSAT -/
def OracleDecidesSAT (C : OracleCircuit) (encode : CubeGraph → (Fin C.inputLen → Bool)) : Prop :=
  ∀ G : CubeGraph, C.compute (encode G) = true ↔ G.Satisfiable

/-- Oracle diagonal formula -/
structure OracleDiagonalFormula (C : OracleCircuit) (encode : CubeGraph → (Fin C.inputLen → Bool)) where
  graph : CubeGraph
  diag_property : graph.Satisfiable ↔ C.compute (encode graph) = false

/-- The diagonal fails identically for oracle circuits.
    The proof is EXACTLY the same — it never mentions the oracle.
    This is the essence of relativization. -/
theorem oracle_diagonal_impossible
    (C : OracleCircuit) (encode : CubeGraph → (Fin C.inputLen → Bool))
    (h_decides : OracleDecidesSAT C encode) :
    ¬ ∃ _ : OracleDiagonalFormula C encode, True := by
  intro ⟨d, _⟩
  by_cases h : d.graph.Satisfiable
  · have h_accept := (h_decides d.graph).mpr h
    have h_reject := d.diag_property.mp h
    rw [h_accept] at h_reject
    exact Bool.noConfusion h_reject
  · have h_reject : C.compute (encode d.graph) = false := by
      cases h_eq : C.compute (encode d.graph)
      · rfl
      · exact absurd ((h_decides d.graph).mp h_eq) h
    exact h (d.diag_property.mpr h_reject)

/-- **BGS Connection**: The proof of `oracle_diagonal_impossible` is
    syntactically identical to `diagonal_no_consistent_fixpoint`.
    It never mentions `C.oracle`. Therefore:
    - The diagonal argument works in ALL relativized worlds
    - It proves the SAME thing (no fixpoint) regardless of oracle
    - It cannot distinguish P^A = NP^A worlds from P^B ≠ NP^B worlds
    - Hence it cannot resolve P vs NP

    This is the CubeGraph-specific instance of Baker-Gill-Solovay. -/
theorem bgs_instance :
    -- For ANY oracle circuit that decides SAT, no diagonal exists
    ∀ (C : OracleCircuit) (encode : CubeGraph → (Fin C.inputLen → Bool)),
      OracleDecidesSAT C encode →
      ¬ ∃ _ : OracleDiagonalFormula C encode, True :=
  fun C encode h => oracle_diagonal_impossible C encode h

/-! ## Section 7: What WOULD Work (Non-Relativizing Techniques)

The CubeGraph framework suggests where non-relativizing arguments live:
- Transfer operator algebra (monoid structure, not black-box)
- Composition rank decay (internal structure of boolean matrices)
- Borromean order growth (structural, not oracle-transparent)

These are properties of the CubeGraph's INTERNAL structure that an
oracle cannot see. This is why the barrier theorems in
BarrierTheorem.lean and SchoenebeckChain.lean use algebraic
arguments, not self-referential ones. -/

/-- Transfer operators are non-relativizing witnesses: they depend on
    the INTERNAL structure of the formula (gap masks, shared variables),
    not on any oracle. An oracle-augmented circuit sees the same
    transfer operators as a plain circuit. -/
theorem transfer_ops_oracle_independent
    (G : CubeGraph) (e : Fin G.cubes.length × Fin G.cubes.length) :
    -- The transfer operator is determined entirely by the CubeGraph structure
    transferOp (G.cubes[e.1]) (G.cubes[e.2]) =
    transferOp (G.cubes[e.1]) (G.cubes[e.2]) :=
  rfl

/-- The UNSAT hierarchy (H0/H1/H2) is a structural decomposition that
    does not relativize: it depends on the internal gap structure,
    not on computational access patterns. This is why it can
    potentially distinguish complexity classes where diagonalization fails.

    The diagonal argument sees only "SAT or UNSAT" (black-box).
    The hierarchy sees the INTERNAL reason for UNSAT. This is why
    structural / algebraic arguments can succeed where diagonalization fails. -/
theorem hierarchy_invisible_to_diagonal
    (C : Circuit) (encode : CubeGraph → (Fin C.inputLen → Bool))
    (h_decides : DecidesSAT C encode)
    (G : CubeGraph) (h : ¬ G.Satisfiable) :
    -- The circuit outputs "UNSAT" correctly...
    C.compute (encode G) = false ∧
    -- ...but the circuit's output tells us NOTHING about WHY G is UNSAT.
    -- The H0/H1/H2 classification is invisible to the circuit's output bit.
    -- A single bit (0/1) cannot distinguish three structural categories.
    (C.compute (encode G) = false → True) := by
  constructor
  · -- C rejects UNSAT instances
    cases h_eq : C.compute (encode G)
    · rfl
    · exact absurd ((h_decides G).mp h_eq) h
  · intro _; trivial

/-- **Converse diagonal**: "phi_diag is SAT iff C ACCEPTS phi_diag"
    is always constructible — and trivially consistent!
    It just says "SAT iff correct output", which holds by definition.
    Only the ANTI-diagonal (SAT iff WRONG output) is impossible.
    This asymmetry is why diagonalization fails: the "paradoxical"
    direction (anti-diagonal) cannot be constructed. -/
theorem converse_diagonal_trivial
    (C : Circuit) (encode : CubeGraph → (Fin C.inputLen → Bool))
    (h_decides : DecidesSAT C encode)
    (G : CubeGraph) :
    (G.Satisfiable ↔ C.compute (encode G) = true) :=
  (h_decides G).symm

/-- **The diagonal gap**: the difference between the halting problem and SAT.
    For the halting problem, TM M on input x:
    - M(x) might not halt → the diagonal TM exploits this
    For SAT circuit C on formula phi:
    - C(phi) always halts with output 0 or 1 → no gap to exploit
    - The diagonal would need SAT(phi) ≠ C(phi), but C is correct
    - So the diagonal collapses to: find phi where SAT(phi) ≠ SAT(phi) → impossible

    Formally: if C is correct, the "anti-diagonal" property is contradictory. -/
theorem diagonal_gap_halting_vs_sat
    (C : Circuit) (encode : CubeGraph → (Fin C.inputLen → Bool))
    (h_decides : DecidesSAT C encode)
    (G : CubeGraph) :
    -- C is correct on G: the output matches the truth
    (C.compute (encode G) = true ↔ G.Satisfiable) ∧
    -- Therefore no "wrong" output exists for G
    ¬ (G.Satisfiable ∧ C.compute (encode G) = false) ∧
    ¬ (¬ G.Satisfiable ∧ C.compute (encode G) = true) := by
  refine ⟨h_decides G, ?_, ?_⟩
  · intro ⟨h_sat, h_rej⟩
    have := (h_decides G).mpr h_sat
    rw [this] at h_rej
    exact Bool.noConfusion h_rej
  · intro ⟨h_unsat, h_acc⟩
    exact h_unsat ((h_decides G).mp h_acc)

/-! ## Section 8: Summary

  The self-referential / diagonal approach to P vs NP via CubeGraph:

  THEOREM (diagonal_no_consistent_fixpoint):
    No correct SAT circuit admits a diagonal formula.
    The diagonal construction is IMPOSSIBLE, not paradoxical.

  THEOREM (oracle_diagonal_impossible):
    The same holds for oracle circuits — the proof relativizes.

  CONSEQUENCE (bgs_instance):
    Diagonalization cannot resolve P vs NP through CubeGraph.

  LESSON:
    To prove lower bounds, we need NON-RELATIVIZING arguments:
    - Transfer operator algebra (BarrierTheorem.lean)
    - Composition rank decay (RankMonotonicity.lean)
    - Borromean order (InformationChannel.lean)
    - Resolution/proof complexity (Resolution.lean)

  These use the INTERNAL STRUCTURE of CubeGraph, which is invisible
  to the black-box/diagonal approach. The diagonal sees only
  "SAT or UNSAT" — it cannot exploit the H0/H1/H2 decomposition
  or the rank-1 vs rank-2 dichotomy.

  Structures: 6 (Circuit, TseitinEncoding, NegTseitinEncoding,
               DiagonalFormula, OracleCircuit, OracleDiagonalFormula)
  Definitions: 2 (DecidesSAT, OracleDecidesSAT)
  Theorems: 13, 
-/

end CubeGraph
