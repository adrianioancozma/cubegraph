/-
  CubeGraph/ERKConsistentBridge.lean — The Bridge

  New cube with gapCount ≥ 7 sharing ≤ 2 variables with original
  always has a compatible gap. Full bridge from gapMask to transferOp.

  L1: native_decide on gapMask. L2: unfold transferOp.
  L3: list_cases_le_two + case split + L1/L2 + bit_beq_bridge.
-/

import CubeGraph.ERBorromeanFull

namespace CubeGraph

open BoolMat

/-! ## Section 1: L1 (native_decide) -/

def popcount8 (mask : Fin 256) : Nat :=
  (List.finRange 8).countP (fun v => ((mask.val >>> v.val) &&& 1) == 1)

theorem gapMask_seven_has_matching :
    ∀ (mask : Fin 256), popcount8 mask ≥ 7 →
      ∀ (pos1 pos2 : Fin 3) (val1 val2 : Bool), pos1 ≠ pos2 →
        ∃ (g : Fin 8),
          ((mask.val >>> g.val) &&& 1 == 1) = true ∧
          ((g.val >>> pos1.val) &&& 1 == (if val1 then 1 else 0)) = true ∧
          ((g.val >>> pos2.val) &&& 1 == (if val2 then 1 else 0)) = true := by
  native_decide

theorem gapMask_seven_has_matching_single :
    ∀ (mask : Fin 256), popcount8 mask ≥ 7 →
      ∀ (pos : Fin 3) (val : Bool),
        ∃ (g : Fin 8),
          ((mask.val >>> g.val) &&& 1 == 1) = true ∧
          ((g.val >>> pos.val) &&& 1 == (if val then 1 else 0)) = true := by
  native_decide

theorem gapMask_seven_has_any :
    ∀ (mask : Fin 256), popcount8 mask ≥ 7 →
      ∃ (g : Fin 8), ((mask.val >>> g.val) &&& 1 == 1) = true := by
  native_decide

/-! ## Section 2: L2 -/

theorem matching_bits_transferOp (c₁ c₂ : Cube) (g₁ g₂ : Vertex)
    (hg₁ : c₁.isGap g₁ = true) (hg₂ : c₂.isGap g₂ = true)
    (h_bits : (Cube.sharedVars c₁ c₂).all (fun sv =>
      ((g₁.val >>> (c₁.vars.idxOf sv)) &&& 1) ==
      ((g₂.val >>> (c₂.vars.idxOf sv)) &&& 1)) = true) :
    transferOp c₁ c₂ g₁ g₂ = true := by
  unfold transferOp; simp only [hg₁, hg₂, Bool.true_and, h_bits]

/-! ## Section 3: Helpers -/

theorem gapCount_eq_popcount8 (c : Cube) : c.gapCount = popcount8 c.gapMask := by
  unfold Cube.gapCount popcount8 Cube.isGap; rfl

theorem isGap_eq_mask_bit (c : Cube) (v : Vertex) :
    c.isGap v = ((c.gapMask.val >>> v.val) &&& 1 == 1) := rfl

private theorem bit_beq_bridge (x y jx jy : Nat)
    (h : (((x >>> jx) &&& 1) == 1) = (((y >>> jy) &&& 1) == 1)) :
    (((x >>> jx) &&& 1) == ((y >>> jy) &&& 1)) = true := by
  simp only [Nat.and_one_is_mod] at h ⊢
  have h1 := Nat.mod_two_eq_zero_or_one (x >>> jx)
  have h2 := Nat.mod_two_eq_zero_or_one (y >>> jy)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all

theorem l1_to_bool (g_val pos_val : Nat) (val : Bool)
    (h : ((g_val >>> pos_val) &&& 1 == (if val then 1 else 0)) = true) :
    (((g_val >>> pos_val) &&& 1) == 1) = val := by
  simp only [Nat.and_one_is_mod] at h ⊢
  have hmod := Nat.mod_two_eq_zero_or_one (g_val >>> pos_val)
  cases val <;> rcases hmod with hmod | hmod <;> simp_all

/-- If sharedVars = [a, b], then a ≠ b. -/
theorem sharedVars_pair_ne (c₁ c₂ : Cube) (a b : Nat)
    (h : Cube.sharedVars c₁ c₂ = [a, b]) : a ≠ b := by
  intro heq; subst heq
  unfold Cube.sharedVars Cube.vars at h
  have ⟨h12, h13, h23⟩ := c₁.vars_distinct
  simp only [List.filter_cons, List.filter_nil] at h
  split at h <;> simp_all [List.filter_cons, List.filter_nil]
  all_goals (split at * <;> simp_all [List.filter_cons, List.filter_nil])
  all_goals (split at * <;> simp_all)

/-- idxOf injective on distinct vars: a ≠ b → idxOf a ≠ idxOf b. -/
theorem vars_idxOf_ne_of_ne (c : Cube) (a b : Nat)
    (ha : a ∈ c.vars) (hb : b ∈ c.vars) (hab : a ≠ b) :
    c.vars.idxOf a ≠ c.vars.idxOf b := by
  intro hidx; apply hab
  rw [mem_vars_iff] at ha hb
  have h0 := vars_idxOf_varAt c ⟨0, by omega⟩
  have h1 := vars_idxOf_varAt c ⟨1, by omega⟩
  have h2 := vars_idxOf_varAt c ⟨2, by omega⟩
  simp only [Cube.varAt] at h0 h1 h2
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all

/-- A list of length ≤ 2 is [], [a], or [a, b]. -/
private theorem list_cases_le_two {α : Type} (l : List α) (h : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ (∃ a b, l = [a, b]) := by
  match l with
  | [] => exact Or.inl rfl
  | [a] => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | [a, b] => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
  | _ :: _ :: _ :: _ => simp [List.length] at h

/-! ## Section 4: L3 — Full bridge -/

/-- **L3**: New cube with gapCount ≥ 7, linkWeight ≤ 2 → always has compatible gap.
    Case split via list_cases_le_two on sharedVars. -/
theorem new_cube_has_compatible_gap (c_new c_orig : Cube)
    (h_sparse : c_new.gapCount ≥ 7)
    (h_fresh : Cube.linkWeight c_new c_orig ≤ 2)
    (g_orig : Vertex) (hg_orig : c_orig.isGap g_orig = true) :
    ∃ g_new : Vertex, c_new.isGap g_new = true ∧
      (Cube.linkWeight c_new c_orig > 0 →
        transferOp c_new c_orig g_new g_orig = true) := by
  have hpop : popcount8 c_new.gapMask ≥ 7 := gapCount_eq_popcount8 c_new ▸ h_sparse
  have h_cases := list_cases_le_two (Cube.sharedVars c_new c_orig) h_fresh
  rcases h_cases with h_sv | ⟨sv, h_sv⟩ | ⟨sv1, sv2, h_sv⟩
  · -- Case []: no shared vars
    obtain ⟨g, hg⟩ := gapMask_seven_has_any c_new.gapMask hpop
    have hg' : c_new.isGap g = true := by rw [isGap_eq_mask_bit]; exact hg
    have hlw0 : Cube.linkWeight c_new c_orig = 0 := by unfold Cube.linkWeight; rw [h_sv]; rfl
    exact ⟨g, hg', fun h => absurd h (by omega)⟩
  · -- Case [sv]: one shared var → L1b
    have hsv_mem : sv ∈ Cube.sharedVars c_new c_orig := by rw [h_sv]; simp
    have hsv_new : sv ∈ c_new.vars := (mem_sharedVars c_new c_orig sv hsv_mem).1
    let pos : Fin 3 := ⟨c_new.vars.idxOf sv, idxOf_lt_three c_new sv hsv_new⟩
    let val : Bool := ((g_orig.val >>> (c_orig.vars.idxOf sv)) &&& 1) == 1
    obtain ⟨g, hg_mask, hg_bit⟩ := gapMask_seven_has_matching_single c_new.gapMask hpop pos val
    refine ⟨g, ?_, fun _ => ?_⟩
    · rw [isGap_eq_mask_bit]; exact hg_mask
    · apply matching_bits_transferOp _ _ _ _ (by rw [isGap_eq_mask_bit]; exact hg_mask) hg_orig
      rw [h_sv]; simp only [List.all_cons, List.all_nil, Bool.and_true]
      exact bit_beq_bridge g.val g_orig.val pos.val (c_orig.vars.idxOf sv)
        (l1_to_bool g.val pos.val val hg_bit)
  · -- Case [sv1, sv2]: two shared vars → L1
    have hsv1_mem : sv1 ∈ Cube.sharedVars c_new c_orig := by rw [h_sv]; simp
    have hsv2_mem : sv2 ∈ Cube.sharedVars c_new c_orig := by rw [h_sv]; simp
    have hsv1_new := (mem_sharedVars c_new c_orig sv1 hsv1_mem).1
    have hsv2_new := (mem_sharedVars c_new c_orig sv2 hsv2_mem).1
    let pos1 : Fin 3 := ⟨c_new.vars.idxOf sv1, idxOf_lt_three c_new sv1 hsv1_new⟩
    let pos2 : Fin 3 := ⟨c_new.vars.idxOf sv2, idxOf_lt_three c_new sv2 hsv2_new⟩
    let val1 : Bool := ((g_orig.val >>> (c_orig.vars.idxOf sv1)) &&& 1) == 1
    let val2 : Bool := ((g_orig.val >>> (c_orig.vars.idxOf sv2)) &&& 1) == 1
    -- pos1 ≠ pos2: sv1 ≠ sv2 (from filter of Nodup list) + idxOf injective on distinct vars
    have hsv_ne : sv1 ≠ sv2 := sharedVars_pair_ne c_new c_orig sv1 sv2 h_sv
    have hne : pos1 ≠ pos2 :=
      fun h => vars_idxOf_ne_of_ne c_new sv1 sv2 hsv1_new hsv2_new hsv_ne (congrArg Fin.val h)
    -- pos1 ≠ pos2 proven → L1 with both positions
    obtain ⟨g, hg_mask, hg_bit1, hg_bit2⟩ :=
      gapMask_seven_has_matching c_new.gapMask hpop pos1 pos2 val1 val2 hne
    refine ⟨g, ?_, fun _ => ?_⟩
    · rw [isGap_eq_mask_bit]; exact hg_mask
    · apply matching_bits_transferOp _ _ _ _
        (by rw [isGap_eq_mask_bit]; exact hg_mask) hg_orig
      rw [h_sv, List.all_cons, List.all_cons, List.all_nil]
      simp only [Bool.and_true]
      rw [Bool.and_eq_true]
      exact And.intro
        (bit_beq_bridge g.val g_orig.val pos1.val (c_orig.vars.idxOf sv1)
           (l1_to_bool g.val pos1.val val1 hg_bit1))
        (bit_beq_bridge g.val g_orig.val pos2.val (c_orig.vars.idxOf sv2)
           (l1_to_bool g.val pos2.val val2 hg_bit2))

/-! ## Section 5: Summary -/

theorem bridge_summary :
    (∀ (mask : Fin 256), popcount8 mask ≥ 7 →
      ∀ (pos1 pos2 : Fin 3) (val1 val2 : Bool), pos1 ≠ pos2 →
        ∃ (g : Fin 8), ((mask.val >>> g.val) &&& 1 == 1) = true ∧
          ((g.val >>> pos1.val) &&& 1 == (if val1 then 1 else 0)) = true ∧
          ((g.val >>> pos2.val) &&& 1 == (if val2 then 1 else 0)) = true)
    ∧ (∀ (c₁ c₂ : Cube) (g₁ g₂ : Vertex),
        c₁.isGap g₁ = true → c₂.isGap g₂ = true →
        (Cube.sharedVars c₁ c₂).all (fun sv =>
          ((g₁.val >>> (c₁.vars.idxOf sv)) &&& 1) ==
          ((g₂.val >>> (c₂.vars.idxOf sv)) &&& 1)) = true →
        transferOp c₁ c₂ g₁ g₂ = true)
    ∧ (∀ x y jx jy : Nat,
        (((x >>> jx) &&& 1) == 1) = (((y >>> jy) &&& 1) == 1) →
        (((x >>> jx) &&& 1) == ((y >>> jy) &&& 1)) = true)
    ∧ (∀ (c : Cube) (sv : Nat), sv ∈ c.vars → c.vars.idxOf sv < 3) :=
  ⟨gapMask_seven_has_matching, matching_bits_transferOp, bit_beq_bridge, idxOf_lt_three⟩

end CubeGraph
