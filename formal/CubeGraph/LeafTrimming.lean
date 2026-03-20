/-
  CubeGraph/LeafTrimming.lean
  Phase 7 (T2-A): Iterative leaf removal preserves SAT equivalence under AC.

  Main results:
  - fullTrimming: iterative leaf removal → "cyclic kernel"
  - fullTrimming_sat_equiv: G.SAT ↔ fullTrimming(G).SAT (under AC)
  - fullTrimming_no_leaves: kernel has no leaves (or ≤ 1 node)
  - fullTrimming_preserves_ac: AC preserved through trimming

  See: theory/theorems/THEOREM-A-HIERARCHY.md (leaf trimming reduces to H² detection)
  See also: CubeGraph/MUS.lean (uses AllArcConsistent, removeNode_preserves_allAC
    to prove MUS + AC → no leaves)
-/

import CubeGraph.TreeSAT

namespace CubeGraph

/-! ## Section 1: AllArcConsistent Predicate -/

/-- Bidirectional arc consistency on all edges (convenience predicate). -/
def AllArcConsistent (G : CubeGraph) : Prop :=
  ∀ e ∈ G.edges,
    arcConsistentDir (G.cubes[e.1]) (G.cubes[e.2]) ∧
    arcConsistentDir (G.cubes[e.2]) (G.cubes[e.1])

/-! ## Section 2: findLeaf -/

/-- Find a leaf node (degree ≤ 1), if one exists. -/
def findLeaf (G : CubeGraph) : Option (Fin G.cubes.length) :=
  (List.finRange G.cubes.length).find? (fun i => decide (G.isLeaf i))

/-- findLeaf = some i → i is a leaf. -/
theorem findLeaf_spec (G : CubeGraph) (i : Fin G.cubes.length)
    (h : G.findLeaf = some i) : G.isLeaf i := by
  unfold findLeaf at h
  have := List.find?_some h
  simp only [decide_eq_true_eq] at this
  exact this

/-- findLeaf = none → no node is a leaf. -/
theorem findLeaf_none_no_leaves (G : CubeGraph)
    (h : G.findLeaf = none) :
    ∀ i : Fin G.cubes.length, ¬ G.isLeaf i := by
  intro i hi
  unfold findLeaf at h
  have hmem : i ∈ List.finRange G.cubes.length := List.mem_finRange i
  have := List.find?_eq_none.mp h i hmem
  simp only [decide_eq_true_eq] at this
  exact this hi

/-! ## Section 3: fullTrimming -/

/-- Iterative leaf removal → "cyclic kernel".
    Removes leaves one at a time until no leaves remain (or graph is trivial). -/
def fullTrimming (G : CubeGraph) : CubeGraph :=
  if h_len : G.cubes.length < 2 then G
  else match h_find : G.findLeaf with
    | none => G
    | some i =>
        have : (G.removeNode i (by omega)).cubes.length < G.cubes.length := by
          rw [removeNode_cubes_length]; omega
        fullTrimming (G.removeNode i (by omega))
termination_by G.cubes.length

/-! ## Section 4: AC Preservation -/

/-- AC propagates through removeNode: AllArcConsistent unfolds to exactly
    the type of removeNode_preserves_arcConsistent. -/
theorem removeNode_preserves_allAC (G : CubeGraph)
    (i : Fin G.cubes.length) (h_len : G.cubes.length ≥ 2)
    (h_ac : AllArcConsistent G) :
    AllArcConsistent (G.removeNode i h_len) := by
  intro e he
  exact removeNode_preserves_arcConsistent G i h_len h_ac e he

/-! ## Section 5: Main Theorems -/

/-- **T2-A**: Full leaf trimming preserves SAT equivalence under AC. -/
theorem fullTrimming_sat_equiv (G : CubeGraph)
    (h_ac : AllArcConsistent G) :
    G.Satisfiable ↔ (fullTrimming G).Satisfiable := by
  unfold fullTrimming
  split
  · -- cubes.length < 2: fullTrimming G = G
    exact Iff.rfl
  · next h_len =>
    split
    · -- findLeaf = none: fullTrimming G = G
      exact Iff.rfl
    · -- findLeaf = some i: one step + recurse
      next i h_find =>
      have h_leaf := findLeaf_spec G i h_find
      have h_ge : G.cubes.length ≥ 2 := by omega
      have h_step := removeLeaf_sat_equiv G i h_ge h_leaf h_ac
      have h_ac_sub := removeNode_preserves_allAC G i h_ge h_ac
      have h_rec := fullTrimming_sat_equiv (G.removeNode i h_ge) h_ac_sub
      exact h_step.trans h_rec
termination_by G.cubes.length
decreasing_by rw [removeNode_cubes_length]; omega

/-- AC is preserved through full trimming. -/
theorem fullTrimming_preserves_ac (G : CubeGraph)
    (h_ac : AllArcConsistent G) :
    AllArcConsistent (fullTrimming G) := by
  unfold fullTrimming
  split
  · exact h_ac
  · next h_len =>
    split
    · exact h_ac
    · next i h_find =>
      have h_ge : G.cubes.length ≥ 2 := by omega
      have h_ac_sub := removeNode_preserves_allAC G i h_ge h_ac
      exact fullTrimming_preserves_ac (G.removeNode i h_ge) h_ac_sub
termination_by G.cubes.length
decreasing_by rw [removeNode_cubes_length]; omega

/-- fullTrimming result: either trivially small or no leaves. -/
theorem fullTrimming_no_leaves (G : CubeGraph) :
    (fullTrimming G).cubes.length < 2 ∨
    ∀ i : Fin (fullTrimming G).cubes.length,
      ¬ (fullTrimming G).isLeaf i := by
  by_cases h_len : G.cubes.length < 2
  · suffices heq : fullTrimming G = G by rw [heq]; exact .inl h_len
    unfold fullTrimming
    split
    · rfl
    · omega
  · cases h_fl : G.findLeaf with
    | none =>
      suffices heq : fullTrimming G = G by rw [heq]; exact .inr (findLeaf_none_no_leaves G h_fl)
      unfold fullTrimming
      split
      · omega
      · split
        · rfl
        · next j hj => simp [h_fl] at hj
    | some idx =>
      suffices heq : fullTrimming G = fullTrimming (G.removeNode idx (by omega)) by
        rw [heq]; exact fullTrimming_no_leaves (G.removeNode idx (by omega))
      rw [fullTrimming.eq_1 G]
      split
      · omega
      · split
        · next h_none => simp [h_fl] at h_none
        · next j hj =>
          have : j = idx := Option.some.inj (by rw [h_fl] at hj; exact hj.symm)
          subst this; rfl
termination_by G.cubes.length
decreasing_by rw [removeNode_cubes_length]; omega

end CubeGraph
