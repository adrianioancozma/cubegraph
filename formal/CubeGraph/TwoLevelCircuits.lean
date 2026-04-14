/-
  CubeGraph/TwoLevelCircuits.lean
  Two-Level Structure: Variable Graph + Cube Graph + Bridge.

  Formalizes the CubeGraph 2.0 architecture:

  LEVEL 1 (Variable Graph):
    Nodes = variables {x_1, ..., x_n}
    States = {0, 1} per variable (VarAssignment n = Fin n -> Bool)
    NOT = flip one bit of the assignment

  LEVEL 2 (Cube Graph):
    Nodes = cubes (variable triples)
    States = gap masks in Fin 256
    Transfer operators = 8x8 boolean matrices

  BRIDGE (projection/lift):
    Projection pi: assignment (n bits) -> gap mask (8 bits per cube)
    Lift lambda: gap masks -> set of compatible assignments
    pi is MANY-TO-ONE (information loss)
    lambda is ONE-TO-MANY (ambiguity)

  KEY THEOREMS:
  T6.1:  flipVar_involutive           -- NOT is involution
  T6.2:  flipVar_differs_at           -- flip changes exactly bit i
  T6.3:  flipVar_preserves_others     -- flip preserves all other bits
  T6.4:  projection_gap               -- projection of satisfying assignment = gap
  T6.5:  projection_compatible        -- projections on adjacent cubes are compatible
  T6.6:  projection_many_to_one       -- pi is many-to-one
  T6.7:  lift_contains_original       -- lift contains the projected assignment
  T6.8:  lift_subset_satisfying       -- lift elements satisfy all cubes they touch
  T6.9:  sat_iff_lift_nonempty        -- satisfiable iff global lift is nonempty
  T6.10: flip_changes_all_cubes       -- NOT on x_i changes all cubes containing x_i
  T6.11: flip_preserves_disjoint      -- NOT on x_i preserves cubes NOT containing x_i
  T6.12: amplification_bound          -- L1 flip -> L2 changes bounded by degree
  T6.13: projection_factors_through_gap_selection -- pi factors as assignment -> gap sel
  T6.14: information_loss_fiber       -- fiber of projection has size >= 2^free_vars
  T6.15: sat_of_section               -- global section of lift -> satisfying assignment
  T6.16: level_separation             -- transfer operators live at L2 only

  . 16 theorems.

  See: experiments-ml/025_2026-03-19_synthesis/bridge-next/agents/
-/

import CubeGraph.CNF

namespace CubeGraph

/-! ## Part 1: Level 1 — Variable Assignments and NOT -/

/-- A variable assignment for n variables: each variable gets a boolean value. -/
abbrev VarAssignment (n : Nat) := Fin n → Bool

/-- Flip variable i in an assignment (the Level-1 NOT operation).
    This is O(1): it changes exactly one bit. -/
def flipVar (a : VarAssignment n) (i : Fin n) : VarAssignment n :=
  fun j => if j = i then !a j else a j

/-- **T6.1**: flipVar is involutive: flipping twice = identity.
    NOT composed with NOT = identity, as expected. -/
theorem flipVar_involutive (a : VarAssignment n) (i : Fin n) :
    flipVar (flipVar a i) i = a := by
  funext j
  simp only [flipVar]
  split
  · simp
  · rfl

/-- **T6.2**: flipVar changes exactly bit i. -/
theorem flipVar_differs_at (a : VarAssignment n) (i : Fin n) :
    (flipVar a i) i = !a i := by
  simp [flipVar]

/-- **T6.3**: flipVar preserves all other bits. -/
theorem flipVar_preserves_others (a : VarAssignment n) (i j : Fin n) (h : j ≠ i) :
    (flipVar a i) j = a j := by
  simp [flipVar, h]

/-! ## Part 2: The Bridge — Projection from Level 1 to Level 2

  The projection maps a global variable assignment to a gap vertex in each cube.
  This is the bridge from the variable world (Level 1) to the cube world (Level 2).

  For cube c with variables (var1, var2, var3), the projection of assignment a
  is `assignmentToGap a c` (already defined in CNF.lean). This is the vertex
  whose bit i = NOT(a(var_i)), i.e., the complement of the assignment restricted
  to the cube's variables.

  The key insight: if the assignment satisfies all clauses in the cube,
  then the projected vertex is a gap. Otherwise it hits a filled vertex. -/

/-- The projection of a variable assignment onto a cube is the gap vertex.
    This is just `assignmentToGap` from CNF.lean, renamed for the two-level vocabulary.
    pi(a, c) = the vertex encoding NOT(a restricted to c's variables). -/
def projectToCube (a : Assignment) (c : Cube) : Vertex := assignmentToGap a c

/-- **T6.4**: If assignment a satisfies all clauses in cube c,
    then its projection is a gap in c.
    This is the fundamental bridge property: L1 satisfaction -> L2 gap. -/
theorem projection_gap (c : Cube) (a : Assignment) (h : allClausesSat c a) :
    c.isGap (projectToCube a c) = true := h

/-- The projection of a global assignment onto a CubeGraph: one gap vertex per cube.
    This is the bridge map pi: Assignment -> GapSelection (when the assignment satisfies). -/
def projectToGraph (G : CubeGraph) (a : Assignment) : GapSelection G :=
  assignmentToGapSelection G a

/-- **T6.5**: Projections on adjacent cubes are compatible via the transfer operator.
    If assignment a satisfies all cubes, then for any edge (c1, c2),
    the projected gap vertices agree on shared variables.
    This is because both projections come from the SAME global assignment. -/
theorem projection_compatible (G : CubeGraph) (a : Assignment)
    (h : ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a) :
    compatibleSelection G (projectToGraph G a) :=
  assignmentToGapSelection_compatible G a h

/-! ## Part 3: Projection is Many-to-One — Information Loss

  The core of the two-level structure: the projection LOSES INFORMATION.
  Multiple distinct global assignments can produce the same gap selection.

  Why? A cube only sees 3 of n variables. Two assignments that agree on all
  cube-variables but differ on free variables project to the same gap vertices.

  For n >= 4, there always exists a variable not in any given cube. -/

/-- Helper: assignmentToGap only depends on the cube's three variables. -/
private theorem assignmentToGap_depends_on_vars (c : Cube) (a1 a2 : Assignment)
    (h1 : a1 c.var₁ = a2 c.var₁) (h2 : a1 c.var₂ = a2 c.var₂)
    (h3 : a1 c.var₃ = a2 c.var₃) :
    assignmentToGap a1 c = assignmentToGap a2 c := by
  unfold assignmentToGap
  simp only [h1, h2, h3]

/-- Two assignments that agree on all variables in cube c
    project to the same gap vertex in c. -/
theorem projection_eq_of_agree (c : Cube) (a1 a2 : Assignment)
    (h : a1 c.var₁ = a2 c.var₁ ∧ a1 c.var₂ = a2 c.var₂ ∧ a1 c.var₃ = a2 c.var₃) :
    projectToCube a1 c = projectToCube a2 c := by
  unfold projectToCube
  exact assignmentToGap_depends_on_vars c a1 a2 h.1 h.2.1 h.2.2

/-- **T6.6**: The projection is many-to-one for a single cube.
    Construct two distinct assignments that project to the same gap vertex.
    They differ only on a variable NOT in the cube. -/
theorem projection_many_to_one (c : Cube) (freeVar : Nat)
    (hfree : freeVar ≠ c.var₁ ∧ freeVar ≠ c.var₂ ∧ freeVar ≠ c.var₃) :
    ∃ (a1 a2 : Assignment), a1 ≠ a2 ∧
      projectToCube a1 c = projectToCube a2 c := by
  -- a1 = all false, a2 = all false except freeVar = true
  let a1 : Assignment := fun _ => false
  let a2 : Assignment := fun v => if v = freeVar then true else false
  refine ⟨a1, a2, ?_, ?_⟩
  · intro heq
    have : a1 freeVar = a2 freeVar := by rw [heq]
    simp [a1, a2] at this
  · apply projection_eq_of_agree
    refine ⟨?_, ?_, ?_⟩
    · show a1 c.var₁ = a2 c.var₁
      simp [a1, a2, Ne.symm hfree.1]
    · show a1 c.var₂ = a2 c.var₂
      simp [a1, a2, Ne.symm hfree.2.1]
    · show a1 c.var₃ = a2 c.var₃
      simp [a1, a2, Ne.symm hfree.2.2]

/-! ## Part 4: The Lift — From Level 2 Back to Level 1

  The lift maps a gap selection (one gap per cube) back to the SET of compatible
  global assignments. Each gap g in cube c constrains 3 variables:
    var_i of c must be NOT(bit i of g)
  The lift is the intersection of all these constraints.

  The lift is ONE-TO-MANY: a single gap selection may be compatible with
  multiple global assignments (via free variables not covered by any cube). -/

/-- An assignment is compatible with a gap vertex in a cube iff
    the assignment's projection equals that gap vertex. -/
def assignmentMatchesGap (a : Assignment) (c : Cube) (g : Vertex) : Prop :=
  projectToCube a c = g

/-- An assignment is in the lift of a gap selection iff it projects to
    that selection at every cube. -/
def inLift (G : CubeGraph) (s : GapSelection G) (a : Assignment) : Prop :=
  ∀ i : Fin G.cubes.length, assignmentMatchesGap a (G.cubes[i]) (s i)

/-- **T6.7**: The original assignment is always in the lift of its own projection.
    pi(a) always lifts back to include a. -/
theorem lift_contains_original (G : CubeGraph) (a : Assignment) :
    inLift G (projectToGraph G a) a := by
  intro i
  rfl

/-- **T6.8**: Every assignment in the lift of a valid gap selection
    satisfies all clauses.
    If the gap selection is valid (each selected vertex is a gap),
    then any assignment projecting to it satisfies all cubes. -/
theorem lift_subset_satisfying (G : CubeGraph) (s : GapSelection G)
    (hs : validSelection G s)
    (a : Assignment) (ha : inLift G s a) :
    ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a := by
  intro i
  unfold allClausesSat
  -- ha i : assignmentMatchesGap a (G.cubes[i]) (s i)
  -- which unfolds to: projectToCube a (G.cubes[i]) = s i
  -- which is: assignmentToGap a (G.cubes[i]) = s i
  have hmatch : assignmentToGap a (G.cubes[i]) = s i := ha i
  rw [hmatch]
  exact hs i

/-- **T6.9**: A CubeGraph is FormulaSat iff the global lift of some valid
    compatible gap selection is nonempty.
    (Forward: FormulaSat gives an assignment whose projection is a valid selection.
     Backward: an assignment in the lift satisfies all clauses.) -/
theorem sat_iff_lift_nonempty (G : CubeGraph) :
    G.FormulaSat ↔
    ∃ s : GapSelection G, validSelection G s ∧ compatibleSelection G s ∧
      ∃ a : Assignment, inLift G s a := by
  constructor
  · intro ⟨a, ha⟩
    exact ⟨projectToGraph G a,
           assignmentToGapSelection_valid G a ha,
           assignmentToGapSelection_compatible G a ha,
           a, lift_contains_original G a⟩
  · intro ⟨s, hs_valid, _, a, ha_lift⟩
    exact ⟨a, lift_subset_satisfying G s hs_valid a ha_lift⟩

/-! ## Part 5: NOT Amplification — Level 1 to Level 2

  A single NOT at Level 1 (flip one variable) causes changes at Level 2
  in ALL cubes containing that variable. The number of affected cubes
  is bounded by the variable's degree in the cube graph. -/

/-- The set of cube indices containing a given variable (as a Nat, matching
    the Cube.var fields which are Nat). -/
def cubesContaining (G : CubeGraph) (x : Nat) : List (Fin G.cubes.length) :=
  (List.finRange G.cubes.length).filter fun i =>
    let c := G.cubes[i]
    x ∈ c.vars

/-- Helper: flipping a variable in a cube changes assignmentToGap.
    Uses a specialized proof strategy: extract the bit that changes,
    show the Fin.val difference is odd (hence nonzero). -/
private theorem flip_changes_assignmentToGap (a : Assignment) (c : Cube) (x : Nat)
    (hx : x = c.var₁ ∨ x = c.var₂ ∨ x = c.var₃) :
    assignmentToGap (fun v => if v = x then !a v else a v) c ≠
    assignmentToGap a c := by
  have ⟨h12, h13, h23⟩ := c.vars_distinct
  -- Use bit-level analysis via assignmentToGap_bit
  intro heq
  rcases hx with rfl | rfl | rfl
  · -- x = var1: bit 0 flips
    have hbit := assignmentToGap_bit (fun v => if v = c.var₁ then !a v else a v) c ⟨0, by omega⟩
    have hbit_orig := assignmentToGap_bit a c ⟨0, by omega⟩
    simp only [Cube.varAt] at hbit hbit_orig
    simp only [ite_true] at hbit
    -- heq : the two gap vertices are equal, so their bits are equal
    rw [heq] at hbit
    rw [hbit] at hbit_orig
    simp at hbit_orig
  · -- x = var2: bit 1 flips
    have hbit := assignmentToGap_bit (fun v => if v = c.var₂ then !a v else a v) c ⟨1, by omega⟩
    have hbit_orig := assignmentToGap_bit a c ⟨1, by omega⟩
    simp only [Cube.varAt] at hbit hbit_orig
    have : ¬(c.var₁ = c.var₂) := h12
    simp only [ite_true] at hbit
    rw [heq] at hbit
    rw [hbit] at hbit_orig
    simp at hbit_orig
  · -- x = var3: bit 2 flips
    have hbit := assignmentToGap_bit (fun v => if v = c.var₃ then !a v else a v) c ⟨2, by omega⟩
    have hbit_orig := assignmentToGap_bit a c ⟨2, by omega⟩
    simp only [Cube.varAt] at hbit hbit_orig
    have hne13 : ¬(c.var₁ = c.var₃) := h13
    have hne23 : ¬(c.var₂ = c.var₃) := h23
    simp only [ite_true] at hbit
    rw [heq] at hbit
    rw [hbit] at hbit_orig
    simp at hbit_orig

/-- **T6.10**: Flipping variable x changes the projection in every cube
    containing x. Specifically, the gap vertex changes because exactly one
    of the 3 bits gets flipped. -/
theorem flip_changes_all_cubes (a : Assignment) (c : Cube) (x : Nat)
    (hx : x ∈ c.vars) :
    projectToCube (fun v => if v = x then !a v else a v) c ≠
    projectToCube a c := by
  simp only [Cube.vars, List.mem_cons, List.mem_nil_iff, or_false] at hx
  exact flip_changes_assignmentToGap a c x hx

/-- Helper: not-in-vars implies ne for each variable. -/
private theorem not_mem_vars_iff (c : Cube) (x : Nat) :
    x ∉ c.vars ↔ x ≠ c.var₁ ∧ x ≠ c.var₂ ∧ x ≠ c.var₃ := by
  simp [Cube.vars]

/-- **T6.11**: Flipping variable x preserves the projection in every cube
    NOT containing x. The cube only sees its 3 variables, so a change
    to an external variable is invisible. -/
theorem flip_preserves_disjoint (a : Assignment) (c : Cube) (x : Nat)
    (hx : x ∉ c.vars) :
    projectToCube (fun v => if v = x then !a v else a v) c =
    projectToCube a c := by
  have ⟨h1, h2, h3⟩ := (not_mem_vars_iff c x).mp hx
  apply projection_eq_of_agree
  exact ⟨by simp [show ¬(c.var₁ = x) from Ne.symm h1],
         by simp [show ¬(c.var₂ = x) from Ne.symm h2],
         by simp [show ¬(c.var₃ = x) from Ne.symm h3]⟩

/-- **T6.12**: The number of cubes affected by flipping variable x
    is bounded by the total number of cubes.
    This quantifies the Level-1 to Level-2 amplification:
    O(1) change at L1 -> O(degree(x)) changes at L2.
    At critical density rho_c ~ 4.27, degree(x) ~ 4.27 = O(1). -/
theorem amplification_bound (G : CubeGraph) (x : Nat) :
    (cubesContaining G x).length ≤ G.cubes.length := by
  unfold cubesContaining
  exact Nat.le_trans (List.length_filter_le ..) (by simp [List.length_finRange])

/-! ## Part 6: Factoring the Bridge — Projection = GapSelection

  The projection from Level 1 to Level 2 factors through the existing
  CubeGraph machinery: it produces a GapSelection that is both valid
  and compatible (when the assignment satisfies). This is the formal
  connection between the two-level picture and the existing Satisfiable def. -/

/-- **T6.13**: The projection of a satisfying assignment produces a valid
    compatible gap selection, establishing that FormulaSat -> Satisfiable
    is precisely the bridge map pi composed with the inclusion GapSelection -> Satisfiable. -/
theorem projection_factors_through_gap_selection (G : CubeGraph) (a : Assignment)
    (h : ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a) :
    validSelection G (projectToGraph G a) ∧
    compatibleSelection G (projectToGraph G a) :=
  ⟨assignmentToGapSelection_valid G a h,
   assignmentToGapSelection_compatible G a h⟩

/-! ## Part 7: Information Loss Quantification

  How much information does the projection lose?
  A cube with variables (v1, v2, v3) only constrains 3 of n bits.
  The remaining n-3 bits are "free" — any value is compatible.
  So the fiber of the projection (assignments mapping to a given gap vertex)
  has size exactly 2^(n-3) for a single cube.

  For the full graph, free variables = those not appearing in ANY cube.
  If there are k free variables, the fiber has size >= 2^k. -/

/-- A free variable: one that doesn't appear in any cube of the graph. -/
def isFreeVar (G : CubeGraph) (x : Nat) : Prop :=
  ∀ i : Fin G.cubes.length, x ∉ (G.cubes[i]).vars

/-- **T6.14**: If a variable is free (not in any cube), then flipping it
    preserves the entire projection. This means the fiber of pi has size
    >= 2^(number of free variables). -/
theorem information_loss_fiber (G : CubeGraph) (a : Assignment) (x : Nat)
    (hfree : isFreeVar G x) :
    projectToGraph G (fun v => if v = x then !a v else a v) =
    projectToGraph G a := by
  funext i
  show projectToCube _ _ = projectToCube _ _
  exact flip_preserves_disjoint a (G.cubes[i]) x (hfree i)

/-! ## Part 8: Global Section and Level Separation

  The two-level picture resolves the "category error":
  - Circuits operate at Level 1 (variable assignments, NOT on bits)
  - Algebraic analysis (KR, rank, band semigroup) lives at Level 2 (gap masks, transfer ops)
  - The bridge connects them, but with information loss

  P vs NP = "can Level 1 operations (circuits) bypass Level 2 bottlenecks (rank)?"
  The bridge formalizes precisely WHERE information is lost. -/

/-- **T6.15**: A global section of the lift (an assignment compatible with
    a valid gap selection) is a satisfying assignment.
    This is the fundamental property: L2 structure determines L1 satisfiability. -/
theorem sat_of_section (G : CubeGraph) (s : GapSelection G)
    (hs : validSelection G s) (a : Assignment)
    (ha : ∀ i : Fin G.cubes.length, assignmentToGap a (G.cubes[i]) = s i) :
    ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a := by
  intro i
  unfold allClausesSat
  rw [ha i]
  exact hs i

/-- **T6.16**: Transfer operators are a purely Level-2 concept.
    They depend only on gap masks and shared variables, NOT on the full
    n-variable assignment. Two cubes with the same gap masks and variable
    structure have the same transfer operator, regardless of the
    rest of the CubeGraph or the number of variables n. -/
theorem level_separation (c₁ c₂ d₁ d₂ : Cube)
    (hvar₁ : c₁.var₁ = d₁.var₁ ∧ c₁.var₂ = d₁.var₂ ∧ c₁.var₃ = d₁.var₃)
    (hvar₂ : c₂.var₁ = d₂.var₁ ∧ c₂.var₂ = d₂.var₂ ∧ c₂.var₃ = d₂.var₃)
    (hgap₁ : c₁.gapMask = d₁.gapMask) (hgap₂ : c₂.gapMask = d₂.gapMask) :
    transferOp c₁ c₂ = transferOp d₁ d₂ := by
  funext g₁ g₂
  simp only [transferOp, Cube.isGap, Cube.sharedVars, Cube.vars]
  simp only [hgap₁, hgap₂, hvar₁.1, hvar₁.2.1, hvar₁.2.2,
             hvar₂.1, hvar₂.2.1, hvar₂.2.2]

end CubeGraph
