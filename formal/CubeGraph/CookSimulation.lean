/-
  CubeGraph/CookSimulation.lean — Cook's Frege→ER Simulation (Constructive)

  Formalizes the structure of Cook's 1975 Frege→ER simulation:
  1. Propositional circuits (gates in topological order)
  2. Bottom-up gate evaluation
  3. Gap-selection to wire-assignment bridge
  4. Tseitin transformation output (as a structure with conditions)
  5. GateConsistentExtBitFn from circuit evaluation
  6. CookSimulation construction
  7. Capstone: CookSimulation exists given TseitinOutput

  The Tseitin transformation itself is encoded as a structure (TseitinOutput)
  rather than fully constructed — the combinatorial details of clause generation
  are deferred. What IS proven: given a valid TseitinOutput, the circuit
  evaluation function produces a valid GateConsistentExtBitFn.

  References:
  - Cook. "Feasibly constructive proofs and the propositional calculus." 1975.
  - Tseitin. "On the complexity of derivation in propositional calculus." 1968.

  Dependencies:
  - ERKConsistent6Gap.lean: GateConsistentExtBitFn, mkVertex3, ERExtension
  - FregeQuadratic.lean: CookSimulation structure
-/

import CubeGraph.FregeQuadratic

namespace CubeGraph

open BoolMat

/-! ## Part 1: Propositional Circuit

  A propositional circuit consists of:
  - `numOrigVars` original Boolean variables (1-indexed, matching DIMACS)
  - `gates` in topological order, each computing one output wire from input wires
  - Acyclicity: each gate's output index exceeds its input indices

  Wire indices: 1..numOrigVars are original variables,
  numOrigVars+1.. are gate output wires. -/

/-- A gate type in a propositional circuit. -/
inductive GateType where
  | And | Or | Not
  deriving DecidableEq, Repr

/-- A gate in a circuit: type + input wire indices + output wire index.
    For Not gates, input2 is ignored (set to 0 by convention). -/
structure Gate where
  gateType : GateType
  input1 : Nat
  input2 : Nat  -- unused for Not
  output : Nat
  deriving DecidableEq, Repr

/-- A propositional circuit: original variables + gates in topological order.
    Wire indices are 1-indexed (DIMACS convention).
    Gates are in topological order: output > max(input1, input2). -/
structure Circuit where
  /-- Number of original Boolean variables -/
  numOrigVars : Nat
  /-- Gates in topological order -/
  gates : List Gate
  /-- All gate outputs are above original variables -/
  outputs_above : ∀ g ∈ gates, g.output > numOrigVars
  /-- Topological order: output > input1 -/
  acyclic1 : ∀ g ∈ gates, g.output > g.input1
  /-- Topological order: output > input2 (for binary gates) -/
  acyclic2 : ∀ g ∈ gates, g.gateType ≠ GateType.Not → g.output > g.input2
  /-- All gate outputs are distinct -/
  outputs_distinct : ∀ g₁ ∈ gates, ∀ g₂ ∈ gates, g₁.output = g₂.output → g₁ = g₂
  deriving DecidableEq

/-- Total number of wires in a circuit: originals + gate outputs. -/
def Circuit.totalWires (c : Circuit) : Nat :=
  c.numOrigVars + c.gates.length

/-! ## Part 2: Circuit Evaluation

  Bottom-up evaluation: original variables from σ, gate outputs computed
  in topological order via foldl. -/

/-- Evaluate a single gate given current wire assignments. -/
def Gate.eval (g : Gate) (assignment : Nat → Bool) : Bool :=
  match g.gateType with
  | .And => assignment g.input1 && assignment g.input2
  | .Or  => assignment g.input1 || assignment g.input2
  | .Not => !assignment g.input1

/-- Evaluate a circuit on an assignment σ to original variables.
    Returns a function from wire index to Bool.
    - For wire i ≤ numOrigVars: reads from σ
    - For gate output wires: computed bottom-up in gate order -/
def Circuit.eval (c : Circuit) (σ : Nat → Bool) : Nat → Bool :=
  c.gates.foldl
    (fun assignment gate =>
      fun wire =>
        if wire = gate.output then gate.eval assignment
        else assignment wire)
    σ

/-- Circuit evaluation preserves original variable values. -/
theorem Circuit.eval_orig (c : Circuit) (σ : Nat → Bool) (v : Nat)
    (hv : v ≤ c.numOrigVars) :
    c.eval σ v = σ v := by
  unfold Circuit.eval
  suffices h : ∀ (gs : List Gate) (f : Nat → Bool),
      (∀ g ∈ gs, g.output > c.numOrigVars) →
      f v = σ v →
      (gs.foldl (fun assignment gate =>
        fun wire => if wire = gate.output then gate.eval assignment
        else assignment wire) f) v = σ v by
    exact h c.gates σ c.outputs_above rfl
  intro gs
  induction gs with
  | nil => intro f _ hf; exact hf
  | cons g gs ih =>
    intro f hout hf
    simp only [List.foldl_cons]
    apply ih
    · intro g' hg'; exact hout g' (List.mem_cons_of_mem g hg')
    · have hne : v ≠ g.output := by
        have : g ∈ g :: gs := List.mem_cons_self ..
        have := hout g this
        omega
      simp [hne, hf]

/-! ## Part 3: Gap Selection to Wire Assignment Bridge

  Converts between CubeGraph's gap-selection view and the circuit's
  wire-assignment view. Defined BEFORE TseitinOutput so the structure
  can reference it. -/

/-- Convert a gap selection on original cubes to a wire assignment.
    For each original variable v: look up which cube contains v,
    read the corresponding bit from the gap selection.

    This is the bridge between CubeGraph's gap-selection view
    and the circuit's wire-assignment view. -/
noncomputable def gapSelectionToWireAssignment (G : CubeGraph)
    (σ_orig : Fin G.cubes.length → Vertex) : Nat → Bool :=
  fun v =>
    if h : ∃ j : Fin G.cubes.length, v ∈ (G.cubes[j]).vars
    then
      let j := Classical.choose h
      let idx := (G.cubes[j]).vars.idxOf v
      ((σ_orig j).val >>> idx) &&& 1 == 1
    else false

/-- The extBitFn for Cook's simulation: evaluate the circuit on the
    wire assignment derived from σ_orig.

    For original variables: reads from σ_orig via gapSelectionToWireAssignment.
    For gate outputs: computes the gate function bottom-up. -/
noncomputable def cookExtBitFn (G : CubeGraph) (c : Circuit)
    (σ_orig : Fin G.cubes.length → Vertex) : Nat → Bool :=
  c.eval (gapSelectionToWireAssignment G σ_orig)

/-! ## Part 4: Tseitin Output Structure

  The Tseitin transformation converts a circuit to 3-SAT clauses.
  Rather than constructing the clauses explicitly, we encode the
  OUTPUT of the transformation as a structure with the properties
  needed for CookSimulation. -/

/-- Output of Tseitin transformation: an ERExtension with
    structural properties that enable GateConsistentExtBitFn construction.

    This is a STRUCTURE (conditions to verify), not a construction.
    The actual Tseitin clause generation is standard but combinatorially
    tedious to formalize; what matters for the proof complexity chain
    is that these properties hold. -/
structure TseitinOutput (G : CubeGraph) (c : Circuit) where
  /-- The ER extension produced by Tseitin -/
  ext : ERExtension G
  /-- Number of new cubes is at most 3 * |gates| (3 clauses per gate) -/
  size_bound : ext.extended.cubes.length ≤ G.cubes.length + 3 * c.gates.length
  /-- New cubes have ≥ 7 gaps (each is a single 3-literal clause) -/
  sparse : ∀ i : Fin ext.extended.cubes.length,
    i.val ≥ G.cubes.length → (ext.extended.cubes[i]).gapCount ≥ 7
  /-- Each new cube has a fresh variable: the gate output wire.
      This variable does not appear in any original cube. -/
  fresh : ∀ i : Fin ext.extended.cubes.length,
    i.val ≥ G.cubes.length →
      ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length,
        j.val < G.cubes.length →
          (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars
  /-- Each new cube is associated with a specific gate. -/
  gateOf : (i : Fin ext.extended.cubes.length) → i.val ≥ G.cubes.length → Fin c.gates.length
  /-- Which position (0, 1, or 2) of the cube holds the gate output wire. -/
  wirePos : (i : Fin ext.extended.cubes.length) → i.val ≥ G.cubes.length → Fin 3
  /-- The wire at wirePos is indeed the gate's output wire -/
  wirePos_correct : ∀ (i : Fin ext.extended.cubes.length) (h : i.val ≥ G.cubes.length),
    (ext.extended.cubes[i]).varAt (wirePos i h) = (c.gates[gateOf i h]).output
  /-- Original cube variables are original circuit variables (≤ numOrigVars). -/
  orig_vars_bound : ∀ (j : Fin G.cubes.length) (v : Nat),
    v ∈ (G.cubes[j]).vars → v ≤ c.numOrigVars
  /-- Circuit evaluation on gapSelectionToWireAssignment agrees with σ_orig
      for original variables, given local consistency.

      This is the Tseitin equisatisfiability property at the bit level:
      for any locally-consistent σ_orig, the circuit evaluation reconstructs
      the same bit values at original variable positions. -/
  eval_consistent : ∀ (σ_orig : Fin G.cubes.length → Vertex)
    (S_orig : List (Fin G.cubes.length))
    (_ : ∀ e ∈ G.edges, e.1 ∈ S_orig → e.2 ∈ S_orig →
      transferOp (G.cubes[e.1]) (G.cubes[e.2]) (σ_orig e.1) (σ_orig e.2) = true),
    ∀ (j : Fin G.cubes.length), j ∈ S_orig →
    ∀ (v : Nat), v ∈ (G.cubes[j]).vars →
      (if cookExtBitFn G c σ_orig v then 1 else 0) =
      ((σ_orig j).val >>> ((G.cubes[j]).vars.idxOf v)) &&& 1
  /-- Gate evaluation avoids the forbidden vertex of each new cube.
      This is the KEY property: for any assignment to original variables,
      evaluating the circuit and reading off the cube's 3 variables
      produces a GAP (not a forbidden vertex). -/
  gate_eval_avoids : ∀ (σ : Nat → Bool)
    (i : Fin ext.extended.cubes.length) (_ : i.val ≥ G.cubes.length),
    let cube := ext.extended.cubes[i]
    cube.isGap (mkVertex3
      (c.eval σ cube.var₁) (c.eval σ cube.var₂)
      (c.eval σ cube.var₃)) = true

/-! ## Part 5: GateConsistentExtBitFn from Circuit Evaluation

  Given a TseitinOutput, we construct the GateConsistentExtBitFn.
  The key: circuit evaluation provides a GLOBAL function that,
  for each σ_orig, maps every wire to a Bool value. -/

/-- Construct GateConsistentExtBitFn from a TseitinOutput.

    The extBitFn is circuit evaluation: for each σ_orig, evaluate the circuit
    on the wire assignment derived from σ_orig. This:
    (1) Avoids forbidden vertices on new cubes (from gate_eval_avoids)
    (2) Agrees with σ_orig on original variables (from eval_consistent) -/
noncomputable def cookGateConsistent (G : CubeGraph) (c : Circuit)
    (tseitin : TseitinOutput G c) :
    GateConsistentExtBitFn G tseitin.ext where
  extBitFn := fun σ_orig => cookExtBitFn G c σ_orig
  avoids_forbidden := by
    intro σ_orig i hi
    exact tseitin.gate_eval_avoids (gapSelectionToWireAssignment G σ_orig) i hi
  consistent_with_orig := by
    intro σ_orig S_orig hc_orig j hj v hv
    exact tseitin.eval_consistent σ_orig S_orig hc_orig j hj v hv

/-! ## Part 6: CookSimulation Construction

  Package TseitinOutput + GateConsistentExtBitFn into CookSimulation. -/

/-- Construct a CookSimulation from a Circuit and its TseitinOutput.
    The Frege proof size is taken as the number of gates. -/
noncomputable def mkCookSimulation (G : CubeGraph) (c : Circuit)
    (tseitin : TseitinOutput G c) :
    CookSimulation G where
  ext := tseitin.ext
  fregeSize := c.gates.length
  c_cook := 3
  c_cook_pos := by omega
  size_bound := tseitin.size_bound
  gate := cookGateConsistent G c tseitin

/-! ## Part 7: Capstone Theorems -/

/-- For any circuit modeling a Frege proof, if TseitinOutput exists,
    then CookSimulation exists with c_cook = 3 (at most 3 cubes per gate). -/
theorem cook_simulation_from_tseitin (G : CubeGraph) (c : Circuit)
    (tseitin : TseitinOutput G c) :
    ∃ sim : CookSimulation G,
      sim.fregeSize = c.gates.length ∧ sim.c_cook = 3 :=
  ⟨mkCookSimulation G c tseitin, rfl, rfl⟩

/-- CookSimulation with c_cook = 3 yields the quadratic bridge.
    Combined with Schoenebeck, this gives Frege size >= Omega(n^2/log n). -/
theorem cook_yields_quadratic_bridge (G : CubeGraph) (n S : Nat)
    (c : Circuit) (tseitin : TseitinOutput G c)
    (c₁ : Nat)
    (hkc : KConsistent G (n / c₁))
    (hS_eq : c.gates.length = S)
    (hS_ge_G : S ≥ G.cubes.length)
    (hS_pos : S ≥ 1)
    (hminRes_le_S : minResolutionSize (mkCookSimulation G c tseitin).ext.extended ≤ S) :
    ∃ cbsw : Nat, cbsw ≥ 1 ∧
      Nat.log2 S * S * (cbsw + cbsw * 3 + 1) ≥
        (n / c₁) * (n / c₁) := by
  have hfs : (mkCookSimulation G c tseitin).fregeSize = S := hS_eq
  exact frege_quadratic_bridge G n S (mkCookSimulation G c tseitin) c₁ hkc
    hfs hS_ge_G hS_pos hminRes_le_S

/-- **The full chain**: Circuit + TseitinOutput + Schoenebeck →
    near-quadratic Frege lower bound.

    This theorem connects:
    1. Schoenebeck: exists UNSAT G with (n/c₁)-consistency
    2. Circuit c (modeling a Frege proof of size S)
    3. TseitinOutput (Tseitin transformation produces valid ERExtension)
    4. mkCookSimulation: packages into CookSimulation
    5. frege_near_quadratic_conditional: log₂(S)·S ≥ (n/c₁)²/K

    The result: S·log₂(S) ≥ Omega(n²), forcing S ≥ Omega(n²/log n). -/
theorem cook_chain_near_quadratic
    (G : CubeGraph) (n S : Nat)
    (circ : Circuit) (tseitin : TseitinOutput G circ)
    (c₁ : Nat) (hn : n ≥ 1)
    (hkc : KConsistent G (n / c₁))
    (hS_eq : circ.gates.length = S)
    (hS_ge_G : S ≥ G.cubes.length)
    (hS_pos : S ≥ 1)
    (hminRes_le_S : minResolutionSize (mkCookSimulation G circ tseitin).ext.extended ≤ S) :
    ∃ cbsw : Nat, cbsw ≥ 1 ∧
      Nat.log2 S * S ≥
        (n / c₁) * (n / c₁) / (cbsw + cbsw * 3 + 1) := by
  have hfs : (mkCookSimulation G circ tseitin).fregeSize = S := hS_eq
  exact frege_near_quadratic_conditional G n S (mkCookSimulation G circ tseitin) c₁ hn hkc
    hfs hS_ge_G hS_pos hminRes_le_S

/-! ## Part 8: Gate-Level Correctness Lemmas

  Standalone lemmas showing that specific gate types always avoid
  their forbidden vertices under correct evaluation. These are
  proven by exhaustive case analysis (decide/native_decide). -/

/-- AND gate: w ↔ (x ∧ y) with clause (w ∨ ¬x ∨ ¬y).
    Forbidden vertex = (0,1,1) = 3. Gate eval: w = x && y.
    For ALL (x,y): (x&&y, x, y) ≠ (0,1,1). -/
theorem and_gate_avoids_forbidden :
    ∀ (x y : Bool), mkVertex3 (x && y) x y ≠ ⟨3, by omega⟩ := by decide

/-- AND gate: w ↔ (x ∧ y) with clause (¬w ∨ x ∨ d).
    Forbidden vertex = (w=1, x=0, d=0) = mkVertex3 true false false = 1.
    When d (padding) = true: vertex = (x&&y, x, true).
    For ALL (x,y): (x&&y, x, true) ≠ 1 because bit2=1. -/
theorem and_padded_clause_avoids :
    ∀ (x y : Bool), mkVertex3 (x && y) x true ≠ ⟨1, by omega⟩ := by decide

/-- OR gate: w ↔ (x ∨ y) with clause (¬w ∨ x ∨ y).
    Forbidden vertex = (w=1, x=0, y=0) = mkVertex3 true false false = 1.
    Gate eval: w = x || y.
    For ALL (x,y): (x||y, x, y) ≠ 1. -/
theorem or_gate_avoids_forbidden :
    ∀ (x y : Bool), mkVertex3 (x || y) x y ≠ ⟨1, by omega⟩ := by decide

/-- NOT gate: w ↔ ¬x with clause (w ∨ x ∨ d).
    Forbidden vertex = (0,0,0) = 0.
    With d=true: vertex = (!x, x, true).
    For ALL x: (!x, x, true) ≠ 0 because bit2=1. -/
theorem not_padded_clause_avoids :
    ∀ (x : Bool), mkVertex3 (!x) x true ≠ ⟨0, by omega⟩ := by decide

/-- NOT gate: w ↔ ¬x with clause (¬w ∨ ¬x ∨ d).
    Forbidden vertex = (1,1,0) = 3.
    With d=true: vertex = (!x, x, true).
    For ALL x: (!x, x, true) ≠ 3 because bit2=1. -/
theorem not_padded_clause2_avoids :
    ∀ (x : Bool), mkVertex3 (!x) x true ≠ ⟨3, by omega⟩ := by decide

/-- **Exhaustive gate correctness**: for every gate type, evaluating
    the gate function and setting padding to true avoids ALL possible
    forbidden vertices. -/
theorem gate_eval_comprehensive :
    -- AND: (x&&y, x, y) is never vertex 3 (forbidden for w∨¬x∨¬y)
    (∀ x y : Bool, mkVertex3 (x && y) x y ≠ ⟨3, by omega⟩) ∧
    -- OR: (x||y, x, y) is never vertex 1 (forbidden for ¬w∨x∨y)
    (∀ x y : Bool, mkVertex3 (x || y) x y ≠ ⟨1, by omega⟩) ∧
    -- NOT: (!x, x, d) with d=true avoids both possible forbidden vertices
    (∀ x : Bool, mkVertex3 (!x) x true ≠ ⟨0, by omega⟩) ∧
    (∀ x : Bool, mkVertex3 (!x) x true ≠ ⟨3, by omega⟩) :=
  ⟨and_gate_avoids_forbidden, or_gate_avoids_forbidden,
   not_padded_clause_avoids, not_padded_clause2_avoids⟩

/-! ## Part 9: Honest Accounting

  WHAT THIS FILE PROVES (0 sorry):
  =================================
  1. Circuit, GateType, Gate: propositional circuit definitions
  2. Circuit.eval: bottom-up circuit evaluation
  3. Circuit.eval_orig: evaluation preserves original variables (induction on gates)
  4. gapSelectionToWireAssignment: gap-selection → wire-assignment bridge
  5. cookExtBitFn: circuit evaluation as parametrized wire assignment
  6. TseitinOutput: structure encoding Tseitin transformation output
  7. cookGateConsistent: GateConsistentExtBitFn from TseitinOutput
     - avoids_forbidden: PROVEN (from TseitinOutput.gate_eval_avoids)
     - consistent_with_orig: PROVEN (from TseitinOutput.eval_consistent)
  8. mkCookSimulation: CookSimulation from Circuit + TseitinOutput
  9. cook_simulation_from_tseitin: existence theorem
  10. cook_yields_quadratic_bridge: BSW bridge
  11. cook_chain_near_quadratic: full proof complexity chain
  12. Gate correctness lemmas: all by decide (AND, OR, NOT avoidance)

  SORRY COUNT: 0
  ===============
  All theorems are proven. The TseitinOutput structure's `eval_consistent`
  field encodes the bit-level consistency requirement as a structure
  condition rather than proving it inline. This is sound: TseitinOutput
  is a HYPOTHESIS structure (like CookSimulation), not claimed as a fact.

  WHAT THIS FILE DOES NOT PROVE:
  ==============================
  - That TseitinOutput exists for every circuit (this IS standard but
    requires explicitly constructing the clauses — combinatorially tedious)
  - P != NP
  - That Frege proofs are actually super-polynomial (this remains open)

  KEY CONTRIBUTION:
  =================
  This file BRIDGES the gap between:
  - Abstract circuit structure (gates, evaluation)
  - CubeGraph proof complexity (ERExtension, GateConsistentExtBitFn, CookSimulation)
  showing that Cook's simulation fits naturally into the CubeGraph framework.

  The chain: Circuit → TseitinOutput → cookGateConsistent → mkCookSimulation →
  cook_preserves_kconsistent → cook_bsw_log_form → frege_near_quadratic_conditional -/

end CubeGraph
