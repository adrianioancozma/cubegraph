/-
  CubeGraph/MinimalBarrier.lean
  Barrier Minimality: H² requires ≥ 3 cubes. Sharp boundary.

  Main results:
  - `two_cube_no_blocked_sat`: ≤ 2 cubes + no blocked edges → SAT
  - `small_not_H2`: ≤ 2 cubes → ¬ UNSATType2
  - `h2_minimal_three_cubes`: r1Graph is H² with exactly 3 cubes (sharp)

  See: experiments-ml/013_2026-03-06_global-intractability/PLAN-MinimalBarrier.md
  See: formal/CubeGraph/Witness.lean (r1_h2_witness — the sharp boundary witness)
  See: formal/CubeGraph/Hierarchy.lean (UNSATType2 definition, H2_locally_invisible)
  See: formal/CubeGraph/BarrierSummary.lean (r1Graph also used as barrier-free witness)
-/

import CubeGraph.Locality
import CubeGraph.Witness

namespace CubeGraph

/-! ## Section 1: Transfer Operator Transpose (local copy) -/

private theorem transferOp_transpose_elem' (c₁ c₂ : Cube) (g₁ g₂ : Vertex) :
    transferOp c₁ c₂ g₁ g₂ = transferOp c₂ c₁ g₂ g₁ := by
  have := congrFun (congrFun (transferOp_transpose c₁ c₂) g₁) g₂
  simp only [BoolMat.transpose_apply] at this
  exact this

/-! ## Section 2: Fin 2 Pair Lemma -/

/-- In Fin n with n ≤ 2, any two distinct elements satisfy a=0∧b=1 or a=1∧b=0. -/
private theorem fin2_val_cases (a b : Fin n) (hn : n ≤ 2) (hab : a ≠ b) :
    (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0) := by
  have ha := a.isLt; have hb := b.isLt
  have hne : a.val ≠ b.val := fun hv => hab (Fin.ext hv)
  omega

/-! ## Section 3: Gap Extraction Helper -/

/-- Every cube has at least one gap (wrapper around gapCount_pos_iff). -/
private theorem exists_gap (c : Cube) : ∃ v : Vertex, c.isGap v = true := by
  have hgp : c.gapCount > 0 := by have := Cube.gapCount_pos c; omega
  rw [Cube.gapCount_pos_iff] at hgp
  obtain ⟨v, _, hv⟩ := hgp
  exact ⟨v, hv⟩

/-! ## Section 4: Main Theorem — ≤ 2 Cubes + No Blocked Edges → SAT -/

/-- Any CubeGraph with ≤ 2 cubes and no blocked edges is satisfiable. -/
theorem two_cube_no_blocked_sat (G : CubeGraph)
    (h_len : G.cubes.length ≤ 2) (hnbe : ¬ HasBlockedEdge G) :
    G.Satisfiable := by
  -- Every cube has a gap
  have hgaps : ∀ i : Fin G.cubes.length, ∃ v : Vertex, (G.cubes[i]).isGap v = true :=
    fun i => exists_gap (G.cubes[i])
  by_cases h_cross : ∃ e ∈ G.edges, e.1 ≠ e.2
  · -- There's a cross-edge: use its compatible pair
    obtain ⟨ce, hce, hne⟩ := h_cross
    have hnb : ¬ blockedEdge G ce.1 ce.2 := fun hb => hnbe ⟨ce, hce, hb⟩
    obtain ⟨g₁, g₂, hcompat⟩ := not_blocked_exists_compatible G ce.1 ce.2 hnb
    have ⟨hg1, hg2⟩ := transferOp_implies_gaps _ _ _ _ hcompat
    -- Selection: s(ce.1) = g₁, s(anything else) = g₂
    refine ⟨fun j => if j = ce.1 then g₁ else g₂, fun j => ?_, fun e he => ?_⟩
    · -- Valid selection
      dsimp only  -- beta-reduce (fun j => if ...) j
      split
      · next hj => -- j = ce.1
        simp only [hj] at hg1 ⊢; exact hg1
      · next hj => -- j ≠ ce.1 → j = ce.2 (Fin 2)
        have hjeq : j = ce.2 := by
          have := fin2_val_cases ce.1 ce.2 h_len hne
          have h_jne : j.val ≠ ce.1.val := fun hv => hj (Fin.ext hv)
          have := j.isLt; have := ce.1.isLt; have := ce.2.isLt
          ext; omega
        simp only [hjeq] at hg2 ⊢; exact hg2
    · -- Compatible selection
      by_cases h_self : e.1 = e.2
      · -- Self-loop
        simp only [h_self]
        apply transferOp_self_gap
        split
        · next heq => simp only [heq] at hg1 ⊢; exact hg1
        · next hneq =>
          have : e.2 = ce.2 := by
            have : e.2.val ≠ ce.1.val := fun hv => hneq (Fin.ext hv)
            have := fin2_val_cases ce.1 ce.2 h_len hne
            have := e.2.isLt; have := ce.1.isLt; have := ce.2.isLt
            ext; omega
          simp only [this] at hg2 ⊢; exact hg2
      · -- Cross-edge: same or reverse direction as ce
        have h_vals := fin2_val_cases e.1 e.2 h_len h_self
        have hce_vals := fin2_val_cases ce.1 ce.2 h_len hne
        by_cases he1ce1 : e.1 = ce.1
        · -- e.1 = ce.1 → e.2 = ce.2 (same direction)
          have he2ce2 : e.2 = ce.2 := by
            have := e.1.isLt; have := e.2.isLt; have := ce.1.isLt; have := ce.2.isLt
            have : e.1.val ≠ e.2.val := fun hv => h_self (Fin.ext hv)
            have : ce.1.val ≠ ce.2.val := fun hv => hne (Fin.ext hv)
            have : e.1.val = ce.1.val := congrArg Fin.val he1ce1
            ext; omega
          have hne2 : ce.2 ≠ ce.1 := fun h => hne h.symm
          simp only [he1ce1, he2ce2, if_neg hne2]
          exact hcompat
        · -- e.1 ≠ ce.1 → e.1 = ce.2, e.2 = ce.1 (reverse direction)
          have he1ce2 : e.1 = ce.2 := by
            have := e.1.isLt; have := e.2.isLt; have := ce.1.isLt; have := ce.2.isLt
            have : e.1.val ≠ ce.1.val := fun hv => he1ce1 (Fin.ext hv)
            have : ce.1.val ≠ ce.2.val := fun hv => hne (Fin.ext hv)
            ext; omega
          have he2ce1 : e.2 = ce.1 := by
            have := e.1.isLt; have := e.2.isLt; have := ce.1.isLt; have := ce.2.isLt
            have : e.1.val ≠ e.2.val := fun hv => h_self (Fin.ext hv)
            have : e.1.val = ce.2.val := congrArg Fin.val he1ce2
            have : ce.1.val ≠ ce.2.val := fun hv => hne (Fin.ext hv)
            ext; omega
          have hne2 : ce.2 ≠ ce.1 := fun h => hne h.symm
          simp only [he1ce2, he2ce1, if_neg hne2]
          rw [transferOp_transpose_elem']
          exact hcompat
  · -- No cross-edges: all self-loops
    have h_all_self : ∀ e ∈ G.edges, e.1 = e.2 :=
      fun e he => Classical.byContradiction fun hne => h_cross ⟨e, he, hne⟩
    refine ⟨fun i => Classical.choose (hgaps i),
           fun i => Classical.choose_spec (hgaps i),
           fun e he => ?_⟩
    simp only [h_all_self e he]
    exact transferOp_self_gap (G.cubes[e.2]) _ (Classical.choose_spec (hgaps e.2))

/-! ## Section 5: H² Requires ≥ 3 Cubes -/

/-- **Barrier Minimality**: No CubeGraph with ≤ 2 cubes can be H² UNSAT. -/
theorem small_not_H2 (G : CubeGraph) (h : G.cubes.length ≤ 2) :
    ¬ UNSATType2 G := by
  intro ⟨h_unsat, _, hnbe⟩
  exact h_unsat (two_cube_no_blocked_sat G h hnbe)

/-! ## Section 6: Sharpness — 3 Cubes Is the Sharp Boundary -/

/-- **Sharp boundary**: r1Graph is H² with exactly 3 cubes. -/
theorem h2_minimal_three_cubes :
    UNSATType2 r1Graph ∧ r1Graph.cubes.length = 3 :=
  ⟨r1_h2_witness, by decide⟩

end CubeGraph
