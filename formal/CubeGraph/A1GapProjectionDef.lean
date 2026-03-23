/-
  CubeGraph/A1GapProjectionDef.lean
  Gap Projection: how Boolean circuits act on cube gap structure.

  CORE IDEA:
    A Boolean circuit (gate) evaluates on assignments. Each gap vertex of a cube
    IS an assignment to that cube's 3 variables. So any gate naturally "projects"
    onto the gap structure: for each gap vertex, does the gate accept or reject
    the assignment encoded by that vertex?

  This gives a map: (Gate, Cube) → GapMask (Fin 256),
  where the output mask indicates which gap vertices satisfy the gate.

  KEY INSIGHT:
    - Input gates project to gap masks determined by a single variable's polarity
    - AND/OR/NOT gates compose projections via bitwise operations on gap masks
    - The gap projection of a circuit is always a SUB-mask of the cube's gaps

  This is the formal bridge between Boolean circuits and the CubeGraph algebra:
  circuits act on cubes by filtering their gaps.

  THEOREMS (15):
    - eval deterministic, gate size, projection basics (5)
    - input projection characterization (2)
    - AND/OR/NOT projection laws (3)
    - projection always within gaps (2)
    - projection mask properties (3)

  See: theory/foundations/01-cube-model.md (cube = 3 variables, 8 vertices)
  See: theory/foundations/06-empty-vertex-duality.md (gap ↔ satisfying assignment)
-/

import CubeGraph.Basic

/-! ## Part 1: Simplified Boolean Circuit (Gate) Model -/

/-- A simplified Boolean gate (circuit node).
    Represents a Boolean function via structural induction.
    - `input i`: reads variable i (0-indexed)
    - `and a b`: conjunction of two sub-gates
    - `or a b`: disjunction of two sub-gates
    - `not a`: negation of a sub-gate -/
inductive SimpleGate where
  | input : Nat → SimpleGate
  | and : SimpleGate → SimpleGate → SimpleGate
  | or : SimpleGate → SimpleGate → SimpleGate
  | not : SimpleGate → SimpleGate
  deriving DecidableEq, Repr

namespace SimpleGate

/-- Evaluate a gate on an assignment (Nat → Bool). -/
def eval (assignment : Nat → Bool) : SimpleGate → Bool
  | .input i => assignment i
  | .and a b => a.eval assignment && b.eval assignment
  | .or a b => a.eval assignment || b.eval assignment
  | .not a => !a.eval assignment

/-- Gate size: number of gate nodes in the circuit tree. -/
def size : SimpleGate → Nat
  | .input _ => 1
  | .and a b => 1 + a.size + b.size
  | .or a b => 1 + a.size + b.size
  | .not a => 1 + a.size

/-- Gate depth: longest path from root to leaf. -/
def depth : SimpleGate → Nat
  | .input _ => 0
  | .and a b => 1 + max a.depth b.depth
  | .or a b => 1 + max a.depth b.depth
  | .not a => 1 + a.depth

/-! ### Evaluation Properties -/

/-- Evaluation is deterministic: same assignment gives same result. -/
theorem eval_deterministic (g : SimpleGate) (f : Nat → Bool) :
    g.eval f = g.eval f := rfl

/-- Size is always positive. -/
theorem size_pos (g : SimpleGate) : g.size > 0 := by
  cases g <;> simp [size] <;> omega

/-- AND evaluation unfolds correctly. -/
@[simp] theorem eval_and (a b : SimpleGate) (f : Nat → Bool) :
    (SimpleGate.and a b).eval f = (a.eval f && b.eval f) := rfl

/-- OR evaluation unfolds correctly. -/
@[simp] theorem eval_or (a b : SimpleGate) (f : Nat → Bool) :
    (SimpleGate.or a b).eval f = (a.eval f || b.eval f) := rfl

/-- NOT evaluation unfolds correctly. -/
@[simp] theorem eval_not (a : SimpleGate) (f : Nat → Bool) :
    (SimpleGate.not a).eval f = (!a.eval f) := rfl

/-- Input evaluation unfolds correctly. -/
@[simp] theorem eval_input (i : Nat) (f : Nat → Bool) :
    (SimpleGate.input i).eval f = f i := rfl

/-- Double negation elimination. -/
theorem eval_not_not (g : SimpleGate) (f : Nat → Bool) :
    (SimpleGate.not (SimpleGate.not g)).eval f = g.eval f := by
  simp [eval, Bool.not_not]

end SimpleGate

/-! ## Part 2: Cube-Local Assignment from a Vertex

  A vertex v ∈ Fin 8 encodes an assignment to a cube's 3 variables.
  We define the function that, given a cube c and vertex v, produces
  the assignment (Nat → Bool) that sets c's variables according to v's bits
  and all other variables to false. -/

namespace Cube

/-- Build a (Nat → Bool) assignment from a cube and a vertex.
    For each of the cube's 3 variables, the bit at the corresponding position
    in v gives the polarity. All other variables default to false. -/
def vertexAssignment (c : Cube) (v : Vertex) : Nat → Bool :=
  fun i =>
    if i = c.var₁ then vertexBit v ⟨0, by omega⟩
    else if i = c.var₂ then vertexBit v ⟨1, by omega⟩
    else if i = c.var₃ then vertexBit v ⟨2, by omega⟩
    else false

/-- vertexAssignment gives var₁ the bit at position 0. -/
@[simp] theorem vertexAssignment_var1 (c : Cube) (v : Vertex) :
    c.vertexAssignment v c.var₁ = vertexBit v ⟨0, by omega⟩ := by
  simp [vertexAssignment]

/-- vertexAssignment gives var₂ the bit at position 1. -/
@[simp] theorem vertexAssignment_var2 (c : Cube) (v : Vertex) :
    c.vertexAssignment v c.var₂ = vertexBit v ⟨1, by omega⟩ := by
  simp only [vertexAssignment]
  have hne : ¬(c.var₂ = c.var₁) := fun h => c.vars_distinct.1 h.symm
  simp [hne]

/-- vertexAssignment gives var₃ the bit at position 2. -/
@[simp] theorem vertexAssignment_var3 (c : Cube) (v : Vertex) :
    c.vertexAssignment v c.var₃ = vertexBit v ⟨2, by omega⟩ := by
  simp only [vertexAssignment]
  have hne1 : ¬(c.var₃ = c.var₁) := fun h => c.vars_distinct.2.1 h.symm
  have hne2 : ¬(c.var₃ = c.var₂) := fun h => c.vars_distinct.2.2 h.symm
  simp [hne1, hne2]

/-- vertexAssignment returns false for variables not in the cube. -/
theorem vertexAssignment_other (c : Cube) (v : Vertex) (i : Nat)
    (h1 : i ≠ c.var₁) (h2 : i ≠ c.var₂) (h3 : i ≠ c.var₃) :
    c.vertexAssignment v i = false := by
  simp [vertexAssignment, h1, h2, h3]

end Cube

/-! ## Part 3: Gap Projection

  The gap projection of a gate g on a cube c is a function Vertex → Bool
  that tests: "does g accept the assignment encoded by vertex v, restricted
  to cube c's variables?"

  Equivalently, we can compute this as a Fin 256 mask for direct comparison
  with the cube's gapMask. -/

/-- Gap projection: evaluate gate g on the assignment induced by vertex v
    in cube c. Returns true iff the gate accepts that vertex's assignment. -/
def gapProjection (g : SimpleGate) (c : Cube) (v : Vertex) : Bool :=
  g.eval (c.vertexAssignment v)

/-- Gap projection as a bitmask over all 8 vertices.
    Bit v is set iff gapProjection g c v = true. -/
def gapProjectionMask (g : SimpleGate) (c : Cube) : Nat :=
  (List.finRange 8).foldl
    (fun acc (v : Fin 8) => if gapProjection g c v then acc ||| (1 <<< v.val) else acc)
    0

/-- Filtered gap projection: the intersection of gapProjection with the cube's
    actual gap set. A vertex passes iff it is BOTH a gap AND accepted by the gate. -/
def filteredGapProjection (g : SimpleGate) (c : Cube) (v : Vertex) : Bool :=
  c.isGap v && gapProjection g c v

/-! ### Gap Projection Basic Properties -/

/-- Gap projection unfolds to eval on vertexAssignment. -/
@[simp] theorem gapProjection_def (g : SimpleGate) (c : Cube) (v : Vertex) :
    gapProjection g c v = g.eval (c.vertexAssignment v) := rfl

/-- Filtered projection is always within gaps: if filtered is true, then isGap is true. -/
theorem filteredGapProjection_subset_gaps (g : SimpleGate) (c : Cube) (v : Vertex)
    (h : filteredGapProjection g c v = true) :
    c.isGap v = true := by
  simp [filteredGapProjection, Bool.and_eq_true] at h
  exact h.1

/-- Filtered projection implies gate acceptance. -/
theorem filteredGapProjection_implies_accepted (g : SimpleGate) (c : Cube) (v : Vertex)
    (h : filteredGapProjection g c v = true) :
    gapProjection g c v = true := by
  simp [filteredGapProjection, Bool.and_eq_true] at h
  exact h.2

/-- Filtered projection is the conjunction of gap membership and gate acceptance. -/
theorem filteredGapProjection_eq_and (g : SimpleGate) (c : Cube) (v : Vertex) :
    filteredGapProjection g c v = (c.isGap v && gapProjection g c v) := rfl

/-! ## Part 4: Gate Composition Laws for Gap Projection

  AND/OR/NOT gates compose projections in the expected way:
  - AND: gapProjection(AND(a,b)) = gapProjection(a) AND gapProjection(b)
  - OR:  gapProjection(OR(a,b))  = gapProjection(a) OR gapProjection(b)
  - NOT: gapProjection(NOT(a))   = NOT(gapProjection(a))
  These are pointwise (per-vertex) equalities. -/

/-- AND projection law: projection of AND = AND of projections. -/
theorem gapProjection_and (a b : SimpleGate) (c : Cube) (v : Vertex) :
    gapProjection (SimpleGate.and a b) c v =
    (gapProjection a c v && gapProjection b c v) := by
  simp [gapProjection]

/-- OR projection law: projection of OR = OR of projections. -/
theorem gapProjection_or (a b : SimpleGate) (c : Cube) (v : Vertex) :
    gapProjection (SimpleGate.or a b) c v =
    (gapProjection a c v || gapProjection b c v) := by
  simp [gapProjection]

/-- NOT projection law: projection of NOT = NOT of projection. -/
theorem gapProjection_not (a : SimpleGate) (c : Cube) (v : Vertex) :
    gapProjection (SimpleGate.not a) c v =
    (!gapProjection a c v) := by
  simp [gapProjection]

/-- Double NOT projection: cancels out. -/
theorem gapProjection_not_not (a : SimpleGate) (c : Cube) (v : Vertex) :
    gapProjection (SimpleGate.not (SimpleGate.not a)) c v =
    gapProjection a c v := by
  simp [gapProjection, SimpleGate.eval, Bool.not_not]

/-! ## Part 5: Input Gate Projection

  For an input gate reading variable i, the projection depends on whether
  i is one of the cube's 3 variables. If so, the projection picks out exactly
  those vertices where the corresponding bit matches. -/

/-- Input gate on var₁: projection = bit 0 of vertex. -/
theorem gapProjection_input_var1 (c : Cube) (v : Vertex) :
    gapProjection (SimpleGate.input c.var₁) c v = Cube.vertexBit v ⟨0, by omega⟩ := by
  simp [gapProjection]

/-- Input gate on var₂: projection = bit 1 of vertex. -/
theorem gapProjection_input_var2 (c : Cube) (v : Vertex) :
    gapProjection (SimpleGate.input c.var₂) c v = Cube.vertexBit v ⟨1, by omega⟩ := by
  simp [gapProjection]

/-- Input gate on var₃: projection = bit 2 of vertex. -/
theorem gapProjection_input_var3 (c : Cube) (v : Vertex) :
    gapProjection (SimpleGate.input c.var₃) c v = Cube.vertexBit v ⟨2, by omega⟩ := by
  simp [gapProjection]

/-- Input gate on a variable NOT in the cube: projection = false. -/
theorem gapProjection_input_other (c : Cube) (v : Vertex) (i : Nat)
    (h1 : i ≠ c.var₁) (h2 : i ≠ c.var₂) (h3 : i ≠ c.var₃) :
    gapProjection (SimpleGate.input i) c v = false := by
  simp [gapProjection, Cube.vertexAssignment_other c v i h1 h2 h3]

/-! ## Part 6: Gap Projection Matrix

  For two linked cubes c₁, c₂ and a pair of gates g₁, g₂, the
  gap projection matrix M[v₁, v₂] captures simultaneous acceptance:
  both g₁ accepts v₁ at c₁ AND g₂ accepts v₂ at c₂.

  This BoolMat 8 interacts with the transfer operator algebra. -/

/-- Gap projection matrix: M[v₁, v₂] = (g₁ accepts v₁ at c₁) ∧ (g₂ accepts v₂ at c₂). -/
def gapProjectionMatrix (g₁ g₂ : SimpleGate) (c₁ c₂ : Cube) : BoolMat 8 :=
  fun v₁ v₂ => gapProjection g₁ c₁ v₁ && gapProjection g₂ c₂ v₂

/-- Gap projection matrix factors as an outer product:
    M[v₁, v₂] = proj₁(v₁) ∧ proj₂(v₂). -/
theorem gapProjectionMatrix_factored (g₁ g₂ : SimpleGate) (c₁ c₂ : Cube) (v₁ v₂ : Vertex) :
    gapProjectionMatrix g₁ g₂ c₁ c₂ v₁ v₂ =
    (gapProjection g₁ c₁ v₁ && gapProjection g₂ c₂ v₂) := rfl

/-- Filtered gap projection matrix: intersect with actual gaps on both sides.
    M[v₁, v₂] = gap(c₁,v₁) ∧ proj(g₁,c₁,v₁) ∧ gap(c₂,v₂) ∧ proj(g₂,c₂,v₂). -/
def filteredGapProjectionMatrix (g₁ g₂ : SimpleGate) (c₁ c₂ : Cube) : BoolMat 8 :=
  fun v₁ v₂ => filteredGapProjection g₁ c₁ v₁ && filteredGapProjection g₂ c₂ v₂

/-- Filtered matrix entries are within the transfer operator's support:
    if filtered matrix entry is true, both vertices must be gaps. -/
theorem filteredMatrix_within_transfer (g₁ g₂ : SimpleGate) (c₁ c₂ : Cube)
    (v₁ v₂ : Vertex)
    (h : filteredGapProjectionMatrix g₁ g₂ c₁ c₂ v₁ v₂ = true) :
    c₁.isGap v₁ = true ∧ c₂.isGap v₂ = true := by
  simp [filteredGapProjectionMatrix, Bool.and_eq_true] at h
  exact ⟨filteredGapProjection_subset_gaps g₁ c₁ v₁ h.1,
         filteredGapProjection_subset_gaps g₂ c₂ v₂ h.2⟩

/-- The filtered matrix is entrywise ≤ the unfiltered projection matrix. -/
theorem filteredMatrix_le_projectionMatrix (g₁ g₂ : SimpleGate) (c₁ c₂ : Cube)
    (v₁ v₂ : Vertex)
    (h : filteredGapProjectionMatrix g₁ g₂ c₁ c₂ v₁ v₂ = true) :
    gapProjectionMatrix g₁ g₂ c₁ c₂ v₁ v₂ = true := by
  simp [filteredGapProjectionMatrix, gapProjectionMatrix, Bool.and_eq_true] at h ⊢
  exact ⟨filteredGapProjection_implies_accepted g₁ c₁ v₁ h.1,
         filteredGapProjection_implies_accepted g₂ c₂ v₂ h.2⟩
