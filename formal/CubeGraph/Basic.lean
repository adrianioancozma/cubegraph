/-
  CubeGraph/Basic.lean
  Core definitions: Cube, CubeGraph, Satisfiability.

  A Cube represents a triplet of variables in a 3-SAT formula.
  Each cube has 8 possible vertices (2³ assignments of its 3 variables).
  A vertex is either FILLED (clause present) or GAP (clause absent).
  Gaps represent satisfying local assignments.

  A CubeGraph connects cubes that share variables.
  SAT ⟺ ∃ compatible gap selection across all cubes.

  See: theory/foundations/01-cube-model.md (cube definitions)
  See: theory/foundations/06-empty-vertex-duality.md (gap = satisfying assignment)
  See: theory/foundations/03-cube-graph.md (graph structure)
-/

import CubeGraph.BoolMat

/-- A vertex index in a cube: one of 8 possible assignments to 3 boolean variables.
    Vertex v corresponds to assignment (v.bit₀, v.bit₁, v.bit₂) for variables (x₁, x₂, x₃). -/
abbrev Vertex := Fin 8

/-- A Cube: 3 distinct positive natural numbers (variables) + a nonempty set of gaps.
    Variables are 1-indexed (DIMACS convention). -/
structure Cube where
  /-- The three variables of this cube (1-indexed, distinct) -/
  var₁ : Nat
  var₂ : Nat
  var₃ : Nat
  /-- Variables are positive -/
  var₁_pos : var₁ > 0
  var₂_pos : var₂ > 0
  var₃_pos : var₃ > 0
  /-- Variables are distinct -/
  vars_distinct : var₁ ≠ var₂ ∧ var₁ ≠ var₃ ∧ var₂ ≠ var₃
  /-- Gap set: which vertices are gaps (nonempty subset of Fin 8).
      Stored as a bitmask: bit i = 1 iff vertex i is a gap. -/
  gapMask : Fin 256
  /-- At least one gap exists (non-dead cube) -/
  gaps_nonempty : gapMask.val > 0
  deriving DecidableEq

namespace Cube

/-- Test if vertex v is a gap in this cube -/
def isGap (c : Cube) (v : Vertex) : Bool :=
  (c.gapMask.val >>> v.val) &&& 1 == 1

/-- The number of gaps in this cube -/
def gapCount (c : Cube) : Nat :=
  (List.finRange 8).countP (fun v => c.isGap v)

/-- Get bit i of vertex v (the polarity of variable i in the assignment) -/
def vertexBit (v : Vertex) (i : Fin 3) : Bool :=
  (v.val >>> i.val) &&& 1 == 1

/-- The variable at index i -/
def varAt (c : Cube) (i : Fin 3) : Nat :=
  match i with
  | ⟨0, _⟩ => c.var₁
  | ⟨1, _⟩ => c.var₂
  | ⟨2, _⟩ => c.var₃

/-- All three variables as a list -/
def vars (c : Cube) : List Nat := [c.var₁, c.var₂, c.var₃]

/-- Shared variables between two cubes -/
def sharedVars (c₁ c₂ : Cube) : List Nat :=
  c₁.vars.filter (fun v => c₂.vars.contains v)

/-- Weight of the link between two cubes = number of shared variables -/
def linkWeight (c₁ c₂ : Cube) : Nat :=
  (sharedVars c₁ c₂).length

end Cube

/-- A CubeGraph: a finite set of cubes with edges between cubes sharing variables. -/
structure CubeGraph where
  /-- The cubes (nodes) -/
  cubes : List Cube
  /-- Edges: pairs of indices into cubes that share at least one variable -/
  edges : List (Fin cubes.length × Fin cubes.length)
  /-- Edges connect cubes that share variables -/
  edges_valid : ∀ e ∈ edges,
    Cube.linkWeight (cubes[e.1]) (cubes[e.2]) > 0
  /-- All cube pairs sharing variables have edges (completeness) -/
  edges_complete : ∀ i j : Fin cubes.length, i ≠ j →
    Cube.linkWeight (cubes[i]) (cubes[j]) > 0 →
    (i, j) ∈ edges ∨ (j, i) ∈ edges

namespace CubeGraph

/-- Compute the transfer operator for an edge between two cubes.
    M[g₁, g₂] = 1 iff:
      (1) g₁ is a gap in cube₁
      (2) g₂ is a gap in cube₂
      (3) g₁ and g₂ agree on all shared variables -/
def transferOp (c₁ c₂ : Cube) : BoolMat 8 :=
  fun g₁ g₂ =>
    c₁.isGap g₁ && c₂.isGap g₂ &&
    -- Check compatibility: for each shared variable, the bits must match
    (Cube.sharedVars c₁ c₂).all fun sv =>
      -- Find index of sv in c₁ and c₂
      let idx₁ := (c₁.vars.idxOf sv)
      let idx₂ := (c₂.vars.idxOf sv)
      -- Compare bits: vertex g at position idx gives polarity of that variable
      ((g₁.val >>> idx₁) &&& 1) == ((g₂.val >>> idx₂) &&& 1)

/-- A gap selection: assigns one gap vertex to each cube -/
def GapSelection (G : CubeGraph) := (i : Fin G.cubes.length) → Vertex

/-- A gap selection is valid if each selection is actually a gap -/
def validSelection (G : CubeGraph) (s : GapSelection G) : Prop :=
  ∀ i : Fin G.cubes.length, (G.cubes[i]).isGap (s i) = true

/-- A gap selection is compatible if all edges are satisfied -/
def compatibleSelection (G : CubeGraph) (s : GapSelection G) : Prop :=
  ∀ e ∈ G.edges, transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true

/-- **Definition 6.2**: A CubeGraph is satisfiable iff there exists a valid compatible gap selection -/
def Satisfiable (G : CubeGraph) : Prop :=
  ∃ s : GapSelection G, validSelection G s ∧ compatibleSelection G s

end CubeGraph
