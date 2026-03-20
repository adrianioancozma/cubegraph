/-
  CubeGraph/ERKConsistentProof.lean — Proof of axiom #12

  Replaces er_sparse_kconsistent_extends (axiom) with
  er_kconsistent_from_aggregate (theorem).

  Key insight: h_aggregate (∃ fresh variable) ensures ≤ 2
  constrained bit positions per new cube. With 7 gaps,
  multi_compatible_gap provides a gap matching any 2 bit values.
-/

import CubeGraph.ERAggregateBricks

namespace CubeGraph

open BoolMat

/-! ## Section 1: transferOp symmetry -/

/-- Extract isGap for c₁ from transferOp. -/
theorem isGap_of_transferOp_fst (c₁ c₂ : Cube) (g₁ g₂ : Vertex)
    (h : transferOp c₁ c₂ g₁ g₂ = true) : c₁.isGap g₁ = true := by
  simp only [transferOp, Bool.and_eq_true] at h; exact h.1.1

/-- Extract isGap for c₂ from transferOp. -/
theorem isGap_of_transferOp_snd (c₁ c₂ : Cube) (g₁ g₂ : Vertex)
    (h : transferOp c₁ c₂ g₁ g₂ = true) : c₂.isGap g₂ = true := by
  simp only [transferOp, Bool.and_eq_true] at h; exact h.1.2

/-- sharedVars membership is symmetric. -/
theorem mem_sharedVars_symm (c₁ c₂ : Cube) (sv : Nat)
    (h : sv ∈ Cube.sharedVars c₁ c₂) : sv ∈ Cube.sharedVars c₂ c₁ :=
  mem_sharedVars_of_mem_both c₂ c₁ sv (mem_sharedVars c₁ c₂ sv h).2 (mem_sharedVars c₁ c₂ sv h).1

/-- transferOp c₂ c₁ g₂ g₁ = true → transferOp c₁ c₂ g₁ g₂ = true. -/
theorem transferOp_flip (c₁ c₂ : Cube) (g₁ g₂ : Vertex)
    (h : transferOp c₂ c₁ g₂ g₁ = true) : transferOp c₁ c₂ g₁ g₂ = true := by
  apply gap_with_correct_bits_compatible c₁ c₂ g₁ g₂
    (isGap_of_transferOp_snd c₂ c₁ g₂ g₁ h) (isGap_of_transferOp_fst c₂ c₁ g₂ g₁ h)
  intro sv hsv
  have hbit := bit_of_transferOp c₂ c₁ g₂ g₁ h sv (mem_sharedVars_symm c₁ c₂ sv hsv)
  simp only [Nat.and_one_is_mod] at hbit ⊢; rw [beq_iff_eq] at hbit; exact hbit.symm

/-! ## Section 2: bit consistency -/

/-- All original cubes in S_orig that share variable v agree on its bit under σ_orig. -/
theorem bit_consistency (G : CubeGraph) (S_orig : List (Fin G.cubes.length))
    (σ : Fin G.cubes.length → Vertex)
    (hc : ∀ e ∈ G.edges, e.1 ∈ S_orig → e.2 ∈ S_orig →
      transferOp (G.cubes[e.1]) (G.cubes[e.2]) (σ e.1) (σ e.2) = true)
    (j₁ j₂ : Fin G.cubes.length) (hj₁ : j₁ ∈ S_orig) (hj₂ : j₂ ∈ S_orig)
    (v : Nat) (hv₁ : v ∈ (G.cubes[j₁]).vars) (hv₂ : v ∈ (G.cubes[j₂]).vars) :
    ((σ j₁).val >>> ((G.cubes[j₁]).vars.idxOf v)) &&& 1 =
    ((σ j₂).val >>> ((G.cubes[j₂]).vars.idxOf v)) &&& 1 := by
  by_cases heq : j₁ = j₂
  · subst heq; rfl
  · rcases G.edges_complete j₁ j₂ heq (linkWeight_pos_of_shared _ _ v hv₁ hv₂) with he | he
    · have := bit_of_transferOp _ _ _ _ (hc _ he hj₁ hj₂) v (mem_sharedVars_of_mem_both _ _ v hv₁ hv₂)
      simp only [Nat.and_one_is_mod] at this ⊢; rwa [beq_iff_eq] at this
    · have := bit_of_transferOp _ _ _ _ (hc _ he hj₂ hj₁) v (mem_sharedVars_of_mem_both _ _ v hv₂ hv₁)
      simp only [Nat.and_one_is_mod] at this ⊢; rw [beq_iff_eq] at this; exact this.symm

/-! ## Section 3: bit value helpers -/

/-- If two Nats have the same &&& 1 == 1 Bool, their &&& 1 values are equal. -/
theorem and1_eq_of_beq1_eq (x y : Nat)
    (h : ((x &&& 1) == 1) = ((y &&& 1) == 1)) : (x &&& 1) = (y &&& 1) := by
  simp only [Nat.and_one_is_mod] at h ⊢
  have hx := Nat.mod_two_eq_zero_or_one x
  have hy := Nat.mod_two_eq_zero_or_one y
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp_all

/-- From (x &&& 1 == 1) = (y == 1) where y ≤ 1, conclude x &&& 1 = y. -/
theorem bit_val_eq (x y : Nat) (hy : y ≤ 1)
    (h : ((x &&& 1) == 1) = (y == 1)) : (x &&& 1) = y := by
  simp only [Nat.and_one_is_mod] at h ⊢
  have hx := Nat.mod_two_eq_zero_or_one x
  rcases hx with hx | hx
  · simp [hx] at h ⊢; omega
  · simp [hx] at h ⊢; omega

/-- If idxOf sv = pos.val in a cube's vars, then varAt pos = sv. -/
theorem varAt_of_idxOf_eq (c : Cube) (sv : Nat) (pos : Fin 3)
    (hsv : sv ∈ c.vars) (hidx : c.vars.idxOf sv = pos.val) :
    c.varAt pos = sv := by
  rw [mem_vars_iff] at hsv
  have h0 := vars_idxOf_varAt c ⟨0, by omega⟩
  have h1 := vars_idxOf_varAt c ⟨1, by omega⟩
  have h2 := vars_idxOf_varAt c ⟨2, by omega⟩
  simp only [Cube.varAt] at h0 h1 h2
  have ⟨hd12, hd13, hd23⟩ := c.vars_distinct
  rcases hsv with rfl | rfl | rfl <;> (match pos with
    | ⟨0, _⟩ => simp_all [Cube.varAt]
    | ⟨1, _⟩ => simp_all [Cube.varAt]
    | ⟨2, _⟩ => simp_all [Cube.varAt])

/-- (x &&& 1) ≤ 1. -/
theorem and1_le_one (x : Nat) : (x &&& 1) ≤ 1 := by
  simp only [Nat.and_one_is_mod]
  have := Nat.mod_two_eq_zero_or_one x; rcases this with h | h <;> simp [h]

/-- sv ∈ cubes[j].vars + varAt w ∉ cubes[j].vars → sv ≠ varAt w. -/
theorem sv_ne_fresh (cubes : List Cube) (i j : Fin cubes.length) (w : Fin 3) (sv : Nat)
    (hij : i ≠ j) (hw : ∀ k : Fin cubes.length, i ≠ k → cubes[i].varAt w ∉ cubes[k].vars)
    (hsv_j : sv ∈ cubes[j].vars) : sv ≠ cubes[i].varAt w :=
  fun heq => hw j hij (heq ▸ hsv_j)

/-- transferOp c c g g = true when isGap c g = true (same gap, same cube). -/
theorem transferOp_self (c : Cube) (g : Vertex) (hg : c.isGap g = true) :
    transferOp c c g g = true := by
  apply matching_bits_transferOp c c g g hg hg
  rw [List.all_eq_true]; intro sv _; simp

/-! ## Section 5: list helpers -/

theorem filterMap_length_le {α β : Type} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.filterMap_cons]; cases f x <;> simp [List.length_cons] <;> omega

theorem filterMap_nodup_of_val_inj
    {n : Nat} (S : List (Fin n)) (hnd : S.Nodup) (m : Nat) (hle : m ≤ n) :
    (S.filterMap fun (i : Fin n) =>
      if h : i.val < m then some (⟨i.val, h⟩ : Fin m) else none).Nodup := by
  let f : Fin n → Option (Fin m) := fun i =>
    if h : i.val < m then some ⟨i.val, h⟩ else none
  show (S.filterMap f).Nodup
  induction S with
  | nil => simp
  | cons x t ih =>
    simp only [List.nodup_cons] at hnd
    simp only [List.filterMap_cons]
    cases hfx : f x with
    | none => exact ih hnd.2
    | some b =>
      rw [List.nodup_cons]
      exact ⟨fun hmem => by
        rw [List.mem_filterMap] at hmem
        obtain ⟨a, ha, hfa⟩ := hmem
        have : x = a := by
          simp only [f] at hfx hfa
          split at hfx <;> split at hfa
          · -- both some
            rename_i h1 h2
            have := Option.some.inj hfx; have := Option.some.inj hfa
            have : x.val = a.val := by
              have := congrArg Fin.val ‹(⟨x.val, h1⟩ : Fin m) = b›
              have := congrArg Fin.val ‹(⟨a.val, h2⟩ : Fin m) = b›
              simp at *; omega
            exact Fin.ext this
          all_goals simp_all
        exact hnd.1 (this ▸ ha), ih hnd.2⟩

theorem mem_filterMap_proj {n : Nat}
    (S : List (Fin n)) (i : Fin n) (hi : i ∈ S) (m : Nat) (hlt : i.val < m) :
    (⟨i.val, hlt⟩ : Fin m) ∈ (S.filterMap fun (j : Fin n) =>
      if h : j.val < m then some (⟨j.val, h⟩ : Fin m) else none) := by
  rw [List.mem_filterMap]
  exact ⟨i, hi, by simp [show i.val < m from hlt]⟩

/-! ## Section 4: Main theorem -/

/-- **Theorem replacing axiom #12**: KConsistent extends from G to T(G)
    for sparse ER with fresh (aggregate) variables.

    Key hypotheses:
    - h_sparse: new cubes have ≥ 7 gaps (out of 8)
    - h_aggregate: each new cube has a fresh variable not in any other cube
    - hkc: original graph is k-consistent -/
theorem er_kconsistent_from_aggregate
    (G : CubeGraph) (k : Nat) (ext : ERExtension G)
    (h_sparse : ∀ i : Fin ext.extended.cubes.length,
      i.val ≥ G.cubes.length → (ext.extended.cubes[i]).gapCount ≥ 7)
    (h_aggregate : ∀ i : Fin ext.extended.cubes.length,
      i.val ≥ G.cubes.length →
        ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length, i ≠ j →
          (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars)
    (hkc : KConsistent G k) :
    KConsistent ext.extended k := by
  classical
  intro S hlen hnd
  -- Project S to original cube indices
  let proj := fun (i : Fin ext.extended.cubes.length) =>
    if h : i.val < G.cubes.length then some (⟨i.val, h⟩ : Fin G.cubes.length) else none
  let S_orig := S.filterMap proj
  -- S_orig ≤ k and Nodup
  have h_proj_len : S_orig.length ≤ k := Nat.le_trans (filterMap_length_le proj S) hlen
  have h_proj_nd : S_orig.Nodup := by
    show (S.filterMap fun (i : Fin ext.extended.cubes.length) =>
      if h : i.val < G.cubes.length then some (⟨i.val, h⟩ : Fin G.cubes.length) else none).Nodup
    exact filterMap_nodup_of_val_inj S hnd G.cubes.length ext.original_prefix
  -- Get σ_orig from KConsistent(G, k)
  obtain ⟨σ_orig, hv_orig, hc_orig⟩ := hkc S_orig h_proj_len h_proj_nd
  -- Define canonical bit value for each variable (from σ_orig, consistent across S_orig)
  let varBit (v : Nat) : Nat :=
    if h : ∃ j ∈ S_orig, v ∈ (G.cubes[j]).vars
    then ((σ_orig (Classical.choose h)).val >>>
          ((G.cubes[Classical.choose h]).vars.idxOf v)) &&& 1
    else 0
  -- For each new cube: get gap with matching bits at the 2 constrained positions
  let newGap (i : Fin ext.extended.cubes.length) (hn : ¬ i.val < G.cubes.length) : Vertex :=
    let w := Classical.choose (h_aggregate i (Nat.not_lt.mp hn))
    let c := ext.extended.cubes[i]
    let vA : Bool := varBit (c.varAt (other_positions w).1) == 1
    let vB : Bool := varBit (c.varAt (other_positions w).2) == 1
    Classical.choose (multi_compatible_gap c (h_sparse i (Nat.not_lt.mp hn)) w vA vB)
  -- Define σ on ext.extended
  let σ : Fin ext.extended.cubes.length → Vertex := fun i =>
    if h : i.val < G.cubes.length then σ_orig ⟨i.val, h⟩
    else newGap i h
  refine ⟨σ, ?valid, ?compat⟩
  case valid =>
    intro i hi
    show (ext.extended.cubes[i]).isGap (σ i) = true
    simp only [σ]
    split
    · -- Original: σ = σ_orig, cubes preserved
      rename_i hlt
      have hmem : (⟨i.val, hlt⟩ : Fin G.cubes.length) ∈ S_orig :=
        mem_filterMap_proj S i hi G.cubes.length hlt
      have hgap := hv_orig ⟨i.val, hlt⟩ hmem
      -- ext.extended.cubes[i] = G.cubes[proj i] by cubes_preserved
      -- congr through dependent GetElem
      have hcube := ext.cubes_preserved (⟨i.val, hlt⟩ : Fin G.cubes.length)
      -- hcube : ext.extended.cubes[i.val]'_ = G.cubes[⟨i.val, hlt⟩]
      -- Goal: (ext.extended.cubes[i]).isGap (σ_orig ⟨i.val, hlt⟩) = true
      -- ext.extended.cubes[i] and ext.extended.cubes[i.val]'_ are equal by proof irrelevance
      change (ext.extended.cubes[i.val]'(i.isLt)).isGap (σ_orig ⟨i.val, hlt⟩) = true
      rw [show ext.extended.cubes[i.val]'(i.isLt) =
            ext.extended.cubes[i.val]'(Nat.lt_of_lt_of_le hlt ext.original_prefix) from rfl]
      rw [hcube]; exact hgap
    · -- New: from multi_compatible_gap spec
      rename_i hlt
      show (ext.extended.cubes[i]).isGap (newGap i hlt) = true
      exact (Classical.choose_spec (multi_compatible_gap
        (ext.extended.cubes[i]) (h_sparse i (Nat.not_lt.mp hlt))
        (Classical.choose (h_aggregate i (Nat.not_lt.mp hlt)))
        (varBit ((ext.extended.cubes[i]).varAt
          (other_positions (Classical.choose (h_aggregate i (Nat.not_lt.mp hlt)))).1) == 1)
        (varBit ((ext.extended.cubes[i]).varAt
          (other_positions (Classical.choose (h_aggregate i (Nat.not_lt.mp hlt)))).2) == 1))).1
  case compat =>
    -- First: extract isGap for any i ∈ S
    have hσ_gap : ∀ i ∈ S, (ext.extended.cubes[i]).isGap (σ i) = true := by
      intro i hi; simp only [σ]; split
      · rename_i hlt; have := ext.cubes_preserved (⟨i.val, hlt⟩ : Fin G.cubes.length)
        change (ext.extended.cubes[i.val]'_).isGap _ = true
        rw [show ext.extended.cubes[i.val]'(i.isLt) =
              ext.extended.cubes[i.val]'(Nat.lt_of_lt_of_le hlt ext.original_prefix) from rfl, this]
        exact hv_orig _ (mem_filterMap_proj S i hi _ hlt)
      · rename_i hlt; exact (Classical.choose_spec (multi_compatible_gap
          (ext.extended.cubes[i]) (h_sparse i (Nat.not_lt.mp hlt))
          (Classical.choose (h_aggregate i (Nat.not_lt.mp hlt)))
          (varBit ((ext.extended.cubes[i]).varAt (other_positions (Classical.choose (h_aggregate i (Nat.not_lt.mp hlt)))).1) == 1)
          (varBit ((ext.extended.cubes[i]).varAt (other_positions (Classical.choose (h_aggregate i (Nat.not_lt.mp hlt)))).2) == 1))).1
    -- Second: bit_eq helper
    have bit_eq : ∀ i ∈ S, ∀ sv', sv' ∈ (ext.extended.cubes[i]).vars →
        (∀ (hge : i.val ≥ G.cubes.length),
          sv' ≠ (ext.extended.cubes[i]).varAt (Classical.choose (h_aggregate i hge))) →
        ((σ i).val >>> (ext.extended.cubes[i]).vars.idxOf sv') &&& 1 = varBit sv' := by
      intro i hi sv' hsv' h_nf; simp only [σ]; split
      · rename_i hlt
        let proj_i : Fin G.cubes.length := ⟨i.val, hlt⟩
        have hpres : ext.extended.cubes[i] = G.cubes[proj_i] :=
          ext.cubes_preserved proj_i
        have hvars : (ext.extended.cubes[i]).vars = (G.cubes[proj_i]).vars :=
          congrArg Cube.vars hpres
        rw [hvars]
        have hsv'_g : sv' ∈ (G.cubes[proj_i]).vars := by rw [← hvars]; exact hsv'
        have hmem := mem_filterMap_proj S i hi G.cubes.length hlt
        have hex : ∃ j ∈ S_orig, sv' ∈ (G.cubes[j]).vars := ⟨proj_i, hmem, hsv'_g⟩
        simp only [varBit]; rw [dif_pos hex]
        exact bit_consistency G S_orig σ_orig hc_orig
          proj_i (Classical.choose hex) hmem (Classical.choose_spec hex).1
          sv' hsv'_g (Classical.choose_spec hex).2
      · rename_i hlt
        have hn := Nat.not_lt.mp hlt
        let w := Classical.choose (h_aggregate i hn)
        have h_pos := idxOf_at_other (ext.extended.cubes[i]) w sv' hsv' (h_nf hn)
        have gs := Classical.choose_spec (multi_compatible_gap
          (ext.extended.cubes[i]) (h_sparse i hn) w
          (varBit ((ext.extended.cubes[i]).varAt (other_positions w).1) == 1)
          (varBit ((ext.extended.cubes[i]).varAt (other_positions w).2) == 1))
        -- Unfold newGap to match gs's Classical.choose
        change ((Classical.choose (multi_compatible_gap
          (ext.extended.cubes[i]) (h_sparse i hn) w
          (varBit ((ext.extended.cubes[i]).varAt (other_positions w).1) == 1)
          (varBit ((ext.extended.cubes[i]).varAt (other_positions w).2) == 1))).val >>>
          (ext.extended.cubes[i]).vars.idxOf sv') &&& 1 = varBit sv'
        have hvb : varBit sv' ≤ 1 := by
          simp only [varBit]; split
          · exact and1_le_one _
          · exact Nat.zero_le 1
        rcases h_pos with hp | hp
        · rw [hp]
          have hb := gs.2.1; simp only [Cube.vertexBit] at hb
          have hva := varAt_of_idxOf_eq (ext.extended.cubes[i]) sv' (other_positions w).1 hsv' hp
          rw [← hva]
          exact bit_val_eq _ _ (by rw [hva]; exact hvb) hb
        · rw [hp]
          have hb := gs.2.2; simp only [Cube.vertexBit] at hb
          have hva := varAt_of_idxOf_eq (ext.extended.cubes[i]) sv' (other_positions w).2 hsv' hp
          rw [← hva]
          exact bit_val_eq _ _ (by rw [hva]; exact hvb) hb
    -- Main: for each edge
    intro e he h1 h2
    by_cases hself : e.1 = e.2
    · -- Self-edge: same gap, same cube
      rw [show ext.extended.cubes[e.2] = ext.extended.cubes[e.1] from by simp [hself],
          show σ e.2 = σ e.1 from by simp [σ, hself]]
      exact transferOp_self _ _ (hσ_gap e.1 h1)
    · -- Distinct: gap_with_correct_bits_compatible + bit_eq
      apply gap_with_correct_bits_compatible _ _ _ _ (hσ_gap e.1 h1) (hσ_gap e.2 h2)
      intro sv hsv
      have hsv1 := (mem_sharedVars _ _ sv hsv).1
      have hsv2 := (mem_sharedVars _ _ sv hsv).2
      have hb1 := bit_eq e.1 h1 sv hsv1 (fun hge =>
        sv_ne_fresh ext.extended.cubes e.1 e.2
          (Classical.choose (h_aggregate e.1 hge)) sv hself
          (Classical.choose_spec (h_aggregate e.1 hge)) hsv2)
      have hb2 := bit_eq e.2 h2 sv hsv2 (fun hge =>
        sv_ne_fresh ext.extended.cubes e.2 e.1
          (Classical.choose (h_aggregate e.2 hge)) sv (Ne.symm hself)
          (Classical.choose_spec (h_aggregate e.2 hge)) hsv1)
      rw [hb1, hb2]

end CubeGraph
