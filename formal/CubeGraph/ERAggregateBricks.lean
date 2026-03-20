/-
  CubeGraph/ERAggregateBricks.lean — Bricks for eliminating axiom #12

  All sub-lemmas needed for proving er_sparse_kconsistent_extends as a theorem.
  Each brick tested standalone (0 errors). Assembly into full theorem requires
  ~50 lines of value extraction from σ_orig (List.find + Classical.choice).

  See: experiments-ml/025_2026-03-19_synthesis/bridge/F7c-PLAN-ULTRATHINK.md
-/

import CubeGraph.ERKConsistentBridge

namespace CubeGraph

open BoolMat

/-! ## C1-C3: other_positions (the 2 non-w positions of a cube) -/

/-- The 2 positions in Fin 3 that are NOT w. -/
def other_positions (w : Fin 3) : Fin 3 × Fin 3 :=
  match w with
  | ⟨0, _⟩ => (⟨1, by omega⟩, ⟨2, by omega⟩)
  | ⟨1, _⟩ => (⟨0, by omega⟩, ⟨2, by omega⟩)
  | ⟨2, _⟩ => (⟨0, by omega⟩, ⟨1, by omega⟩)

/-- The two non-w positions are distinct. -/
theorem other_positions_ne (w : Fin 3) :
    (other_positions w).1 ≠ (other_positions w).2 := by
  revert w; decide

/-- The two non-w positions are both ≠ w. -/
theorem other_positions_ne_w (w : Fin 3) :
    (other_positions w).1 ≠ w ∧ (other_positions w).2 ≠ w := by
  revert w; decide

/-! ## C4: shared variables don't include the fresh variable -/

/-- If varAt(w_pos) is not in c_other's vars, then no shared var = varAt(w_pos). -/
theorem shared_var_not_at_w (c_new c_other : Cube) (w_pos : Fin 3)
    (hw : c_new.varAt w_pos ∉ c_other.vars)
    (sv : Nat) (hsv : sv ∈ Cube.sharedVars c_new c_other) :
    sv ≠ c_new.varAt w_pos := by
  intro heq; subst heq
  exact hw (mem_sharedVars c_new c_other _ hsv).2

/-! ## C5: idxOf of a non-w shared var is at pos_A or pos_B -/

/-- A variable in c.vars that is ≠ varAt(w_pos) has idxOf at one of the other 2 positions. -/
theorem idxOf_at_other (c : Cube) (w_pos : Fin 3) (sv : Nat)
    (hsv : sv ∈ c.vars) (hne : sv ≠ c.varAt w_pos) :
    c.vars.idxOf sv = (other_positions w_pos).1.val ∨
    c.vars.idxOf sv = (other_positions w_pos).2.val := by
  rw [mem_vars_iff] at hsv
  have ⟨h12, h13, h23⟩ := c.vars_distinct
  have h0 := vars_idxOf_varAt c ⟨0, by omega⟩
  have h1 := vars_idxOf_varAt c ⟨1, by omega⟩
  have h2 := vars_idxOf_varAt c ⟨2, by omega⟩
  simp only [Cube.varAt] at h0 h1 h2 hne
  rcases hsv with rfl | rfl | rfl <;>
    (match w_pos with
    | ⟨0, _⟩ => simp_all [other_positions]
    | ⟨1, _⟩ => simp_all [other_positions]
    | ⟨2, _⟩ => simp_all [other_positions])

/-! ## C7: transferOp true → bits match on shared vars -/

/-- transferOp = true implies all shared vars have matching bits. -/
theorem transferOp_implies_bits_all (c1 c2 : Cube) (g1 g2 : Vertex)
    (h : transferOp c1 c2 g1 g2 = true) :
    (Cube.sharedVars c1 c2).all (fun sv =>
      ((g1.val >>> (c1.vars.idxOf sv)) &&& 1) ==
      ((g2.val >>> (c2.vars.idxOf sv)) &&& 1)) = true := by
  unfold transferOp at h
  cases h1 : c1.isGap g1 <;> cases h2 : c2.isGap g2 <;> simp_all

/-- Extract single bit match from transferOp. -/
theorem bit_of_transferOp (c1 c2 : Cube) (g1 g2 : Vertex)
    (h : transferOp c1 c2 g1 g2 = true)
    (sv : Nat) (hsv : sv ∈ Cube.sharedVars c1 c2) :
    (((g1.val >>> (c1.vars.idxOf sv)) &&& 1) ==
     ((g2.val >>> (c2.vars.idxOf sv)) &&& 1)) = true := by
  have := transferOp_implies_bits_all c1 c2 g1 g2 h
  rw [List.all_eq_true] at this; exact this sv hsv

/-! ## C10: gap with correct bits → compatible with any neighbor -/

/-- If gap g has isGap = true and its bits match the neighbor's bits on all shared vars,
    then transferOp is true. This is matching_bits_transferOp but with the bit-match
    hypothesis stated per-shared-var instead of as List.all. -/
theorem gap_with_correct_bits_compatible
    (c_new c_other : Cube) (g g_other : Vertex)
    (hg_new : c_new.isGap g = true) (hg_other : c_other.isGap g_other = true)
    (h_bits : ∀ sv ∈ Cube.sharedVars c_new c_other,
      ((g.val >>> (c_new.vars.idxOf sv)) &&& 1) =
      ((g_other.val >>> (c_other.vars.idxOf sv)) &&& 1)) :
    transferOp c_new c_other g g_other = true := by
  apply matching_bits_transferOp _ _ _ _ hg_new hg_other
  rw [List.all_eq_true]
  intro sv hsv
  simp only [beq_iff_eq, Nat.and_one_is_mod]
  simp only [Nat.and_one_is_mod] at h_bits
  exact h_bits sv hsv

/-! ## Multi-neighbor gap: parameterized by values -/

/-- A cube with gapCount ≥ 7 has a gap matching any 2 bit values at the non-w positions.
    This is the parameterized multi-neighbor compatible gap. -/
theorem multi_compatible_gap (c : Cube) (h_sparse : c.gapCount ≥ 7)
    (w_pos : Fin 3) (val_A val_B : Bool) :
    ∃ g : Vertex, c.isGap g = true ∧
      Cube.vertexBit g (other_positions w_pos).1 = val_A ∧
      Cube.vertexBit g (other_positions w_pos).2 = val_B := by
  have hpop : popcount8 c.gapMask ≥ 7 := gapCount_eq_popcount8 c ▸ h_sparse
  obtain ⟨g, hm, h1, h2⟩ := gapMask_seven_has_matching c.gapMask hpop
    (other_positions w_pos).1 (other_positions w_pos).2 val_A val_B (other_positions_ne w_pos)
  exact ⟨g, by rw [isGap_eq_mask_bit]; exact hm,
    by unfold Cube.vertexBit; exact l1_to_bool g.val _ val_A h1,
    by unfold Cube.vertexBit; exact l1_to_bool g.val _ val_B h2⟩

/-! ## Summary -/

/-- All bricks assembled: the components needed for axiom #12 elimination.
    Missing piece: extraction of val_A, val_B from σ_orig (~50 lines of plumbing). -/
theorem aggregate_bricks_summary :
    -- C2: non-w positions distinct
    (∀ w : Fin 3, (other_positions w).1 ≠ (other_positions w).2)
    -- C4: shared vars don't include fresh var
    ∧ (∀ c_new c_other : Cube, ∀ w_pos : Fin 3,
        c_new.varAt w_pos ∉ c_other.vars →
        ∀ sv ∈ Cube.sharedVars c_new c_other, sv ≠ c_new.varAt w_pos)
    -- C7: transferOp → bits match
    ∧ (∀ c1 c2 : Cube, ∀ g1 g2 : Vertex,
        transferOp c1 c2 g1 g2 = true →
        (Cube.sharedVars c1 c2).all (fun sv =>
          ((g1.val >>> (c1.vars.idxOf sv)) &&& 1) ==
          ((g2.val >>> (c2.vars.idxOf sv)) &&& 1)) = true) :=
  ⟨other_positions_ne, shared_var_not_at_w, transferOp_implies_bits_all⟩

end CubeGraph
