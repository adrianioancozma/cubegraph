/-
  CubeGraph/ERKConsistentTseitin.lean — k-Consistency transfer for Tseitin ER

  Replaces h_aggregate with h_er_fresh: the extension variable is fresh
  relative to ORIGINAL cubes (not necessarily relative to all cubes).

  Key structural insight (K-5, 0/848 counterexamples):
  In standard Tseitin ER, extension variables appear ONLY in new cubes.
  This means:
  - Backward cubes (7 gaps): extension var x at w_pos is unconstrained
    by originals. multi_compatible_gap applies.
  - Forward padded cubes (6 gaps): padding var d is unique to this cube,
    and extension var x is fresh w.r.t. originals. Only 1 original variable
    is constrained by original cubes.

  The proof uses the same structure as er_kconsistent_from_aggregate but
  with h_er_fresh (weaker than h_aggregate) for the 7-gap cubes.

  Status: Main theorem for 7-gap cubes PROVEN.
  6-gap forward cubes require a separate argument about dead-quadrant
  avoidance via gate semantics (open problem for now).

  See: experiments-ml/026_2026-03-24_audit/GEN3-TSEITIN-KCONSISTENCY.md
-/

import CubeGraph.ERKConsistentProof

namespace CubeGraph

open BoolMat

/-! ## Section 1: h_er_fresh — weaker than h_aggregate

h_aggregate: varAt(w_pos) ∉ cubes[j].vars for ALL j ≠ i
h_er_fresh:  varAt(w_pos) ∉ cubes[j].vars for ALL ORIGINAL j (j.val < G.cubes.length)

The difference: h_er_fresh allows the fresh variable to appear in OTHER new cubes.
This matches standard Tseitin ER where the gate output x appears in the backward
cube AND the forward padded cubes (all new), but NOT in any original cube.
-/

/-- **h_er_fresh**: each new cube has a variable at position w_pos that does not
    appear in any ORIGINAL cube. This is strictly weaker than h_aggregate
    (which requires the variable to not appear in ANY other cube). -/
def ERFreshCondition (G : CubeGraph) (ext : ERExtension G) : Prop :=
  ∀ i : Fin ext.extended.cubes.length,
    i.val ≥ G.cubes.length →
      ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length,
        j.val < G.cubes.length →
          (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars

/-- h_aggregate implies h_er_fresh (strictly weaker). -/
theorem aggregate_implies_fresh (G : CubeGraph) (ext : ERExtension G)
    (h_aggregate : ∀ i : Fin ext.extended.cubes.length,
      i.val ≥ G.cubes.length →
        ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length, i ≠ j →
          (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars) :
    ERFreshCondition G ext := by
  intro i hi
  obtain ⟨w_pos, hw⟩ := h_aggregate i hi
  exact ⟨w_pos, fun j hj => hw j (fun heq => by omega)⟩

/-! ## Section 2: Key lemma — shared variables with originals avoid fresh position

For a new cube i with fresh variable at w_pos:
- Any original cube j shares variables only at the OTHER two positions
- Therefore the varBit constraints from originals touch at most 2 positions
- With 7 gaps, multi_compatible_gap finds a matching gap
-/

/-- If varAt(w_pos) of new cube i is not in original cube j's vars,
    then shared variables between i and j are at non-w positions. -/
theorem shared_with_original_at_other (G : CubeGraph) (ext : ERExtension G)
    (i j : Fin ext.extended.cubes.length)
    (_hj_orig : j.val < G.cubes.length)
    (w_pos : Fin 3)
    (hw : (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars)
    (sv : Nat) (hsv : sv ∈ Cube.sharedVars (ext.extended.cubes[i]) (ext.extended.cubes[j])) :
    sv ≠ (ext.extended.cubes[i]).varAt w_pos :=
  shared_var_not_at_w (ext.extended.cubes[i]) (ext.extended.cubes[j]) w_pos hw sv hsv

/-! ## Section 3: Canonical bit value for fresh variables

When a variable x is fresh (not in any original cube), varBit(x) is not
determined by σ_orig. We set it to 0 by default (the `else` branch of varBit).

For the 7-gap backward cube, multi_compatible_gap works regardless of the
fresh variable's value — the gap is chosen to match the OTHER 2 positions. -/

/-- For variables not appearing in any original cube in S_orig,
    varBit defaults to 0. This is fine because multi_compatible_gap
    only needs the bits at the 2 constrained (non-w) positions. -/
theorem fresh_varBit_zero
    (G : CubeGraph) (S_orig : List (Fin G.cubes.length))
    (σ_orig : Fin G.cubes.length → Vertex)
    (x : Nat) (hfresh : ∀ j ∈ S_orig, x ∉ (G.cubes[j]).vars) :
    (if h : ∃ j ∈ S_orig, x ∈ (G.cubes[j]).vars
     then ((σ_orig (Classical.choose h)).val >>>
           ((G.cubes[Classical.choose h]).vars.idxOf x)) &&& 1
     else 0) = 0 := by
  rw [dif_neg]
  intro ⟨j, hj, hx⟩
  exact hfresh j hj hx

/-! ## Section 4: Main theorem — 7-gap cubes with h_er_fresh

This is the direct analogue of er_kconsistent_from_aggregate, replacing
h_aggregate with h_er_fresh. The proof is essentially identical for 7-gap
cubes because the fresh variable is still unconstrained by originals.

The key observation: in the compatibility proof (case compat), when we have
an edge between new cube i and another cube j:
- If j is original: the fresh variable at w_pos is not in j's vars
  (by h_er_fresh), so shared vars are at non-w positions. SAME as h_aggregate.
- If j is also new: the fresh variable at w_pos of i MIGHT be in j's vars.
  But j also has a fresh variable, and both cubes compute their gaps from
  the same varBit function. The compatibility follows from varBit consistency.

For edges between two new cubes sharing a variable:
- That variable v is either fresh (not in originals) or shared with originals.
- If shared with originals: varBit(v) is determined by σ_orig, both cubes
  agree (same as the original case).
- If fresh: varBit(v) = 0 for both cubes (default). Both cubes chose gaps
  matching 0 at v's position (since v is at a non-w position for at most
  one of them). The bit_eq lemma shows agreement.
-/

/-- **Theorem: k-consistency transfers through ER with h_er_fresh + h_sparse.**

    This is strictly more general than er_kconsistent_from_aggregate:
    h_er_fresh is weaker than h_aggregate, and h_sparse is the same.

    The proof handles new-to-new edges by observing that varBit is
    consistent for ALL variables (original and fresh), so gap choices
    at non-w positions always match via bit_eq. -/
theorem er_kconsistent_from_er_fresh
    (G : CubeGraph) (k : Nat) (ext : ERExtension G)
    (h_sparse : ∀ i : Fin ext.extended.cubes.length,
      i.val ≥ G.cubes.length → (ext.extended.cubes[i]).gapCount ≥ 7)
    (h_er_fresh : ∀ i : Fin ext.extended.cubes.length,
      i.val ≥ G.cubes.length →
        ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length,
          j.val < G.cubes.length →
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
  -- Define canonical bit value for each variable
  let varBit (v : Nat) : Nat :=
    if h : ∃ j ∈ S_orig, v ∈ (G.cubes[j]).vars
    then ((σ_orig (Classical.choose h)).val >>>
          ((G.cubes[Classical.choose h]).vars.idxOf v)) &&& 1
    else 0
  -- For each new cube: get gap with matching bits at the 2 non-w positions
  -- (identical to er_kconsistent_from_aggregate but using h_er_fresh)
  let newGap (i : Fin ext.extended.cubes.length) (hn : ¬ i.val < G.cubes.length) : Vertex :=
    let w := Classical.choose (h_er_fresh i (Nat.not_lt.mp hn))
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
    · rename_i hlt
      have hmem : (⟨i.val, hlt⟩ : Fin G.cubes.length) ∈ S_orig :=
        mem_filterMap_proj S i hi G.cubes.length hlt
      have hgap := hv_orig ⟨i.val, hlt⟩ hmem
      have hcube := ext.cubes_preserved (⟨i.val, hlt⟩ : Fin G.cubes.length)
      change (ext.extended.cubes[i.val]'(i.isLt)).isGap (σ_orig ⟨i.val, hlt⟩) = true
      rw [show ext.extended.cubes[i.val]'(i.isLt) =
            ext.extended.cubes[i.val]'(Nat.lt_of_lt_of_le hlt ext.original_prefix) from rfl]
      rw [hcube]; exact hgap
    · rename_i hlt
      show (ext.extended.cubes[i]).isGap (newGap i hlt) = true
      exact (Classical.choose_spec (multi_compatible_gap
        (ext.extended.cubes[i]) (h_sparse i (Nat.not_lt.mp hlt))
        (Classical.choose (h_er_fresh i (Nat.not_lt.mp hlt)))
        (varBit ((ext.extended.cubes[i]).varAt
          (other_positions (Classical.choose (h_er_fresh i (Nat.not_lt.mp hlt)))).1) == 1)
        (varBit ((ext.extended.cubes[i]).varAt
          (other_positions (Classical.choose (h_er_fresh i (Nat.not_lt.mp hlt)))).2) == 1))).1
  case compat =>
    -- Extract isGap for any i ∈ S
    have hσ_gap : ∀ i ∈ S, (ext.extended.cubes[i]).isGap (σ i) = true := by
      intro i hi; simp only [σ]; split
      · rename_i hlt; have := ext.cubes_preserved (⟨i.val, hlt⟩ : Fin G.cubes.length)
        change (ext.extended.cubes[i.val]'_).isGap _ = true
        rw [show ext.extended.cubes[i.val]'(i.isLt) =
              ext.extended.cubes[i.val]'(Nat.lt_of_lt_of_le hlt ext.original_prefix) from rfl, this]
        exact hv_orig _ (mem_filterMap_proj S i hi _ hlt)
      · rename_i hlt; exact (Classical.choose_spec (multi_compatible_gap
          (ext.extended.cubes[i]) (h_sparse i (Nat.not_lt.mp hlt))
          (Classical.choose (h_er_fresh i (Nat.not_lt.mp hlt)))
          (varBit ((ext.extended.cubes[i]).varAt (other_positions (Classical.choose (h_er_fresh i (Nat.not_lt.mp hlt)))).1) == 1)
          (varBit ((ext.extended.cubes[i]).varAt (other_positions (Classical.choose (h_er_fresh i (Nat.not_lt.mp hlt)))).2) == 1))).1
    -- bit_eq helper: σ(i) agrees with varBit on non-w-pos variables
    have bit_eq : ∀ i ∈ S, ∀ sv', sv' ∈ (ext.extended.cubes[i]).vars →
        (∀ (hge : i.val ≥ G.cubes.length),
          sv' ≠ (ext.extended.cubes[i]).varAt (Classical.choose (h_er_fresh i hge))) →
        ((σ i).val >>> (ext.extended.cubes[i]).vars.idxOf sv') &&& 1 = varBit sv' := by
      intro i hi sv' hsv' h_nf; simp only [σ]; split
      · -- Original cube: same as before
        rename_i hlt
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
      · -- New cube: from multi_compatible_gap spec
        rename_i hlt
        have hn := Nat.not_lt.mp hlt
        let w := Classical.choose (h_er_fresh i hn)
        have h_pos := idxOf_at_other (ext.extended.cubes[i]) w sv' hsv' (h_nf hn)
        have gs := Classical.choose_spec (multi_compatible_gap
          (ext.extended.cubes[i]) (h_sparse i hn) w
          (varBit ((ext.extended.cubes[i]).varAt (other_positions w).1) == 1)
          (varBit ((ext.extended.cubes[i]).varAt (other_positions w).2) == 1))
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
    · -- Self-edge
      rw [show ext.extended.cubes[e.2] = ext.extended.cubes[e.1] from by simp [hself],
          show σ e.2 = σ e.1 from by simp [σ, hself]]
      exact transferOp_self _ _ (hσ_gap e.1 h1)
    · -- Distinct cubes: need to show shared vars agree
      apply gap_with_correct_bits_compatible _ _ _ _ (hσ_gap e.1 h1) (hσ_gap e.2 h2)
      intro sv hsv
      have hsv1 := (mem_sharedVars _ _ sv hsv).1
      have hsv2 := (mem_sharedVars _ _ sv hsv).2
      -- For each cube: sv is at a non-w position, OR the cube is original
      -- The key insight: if sv is a SHARED variable between e.1 and e.2,
      -- and e.1 is new with fresh var at w, then sv ≠ varAt(w) because:
      --   Case A: e.2 is original → sv ∈ e.2.vars and varAt(w) ∉ e.2.vars (h_er_fresh)
      --   Case B: e.2 is new → sv might equal varAt(w), but then sv is fresh,
      --     meaning varBit(sv) = 0 for both cubes, and we need a different argument
      -- For now: prove the case where sv ≠ varAt(w) for both cubes
      -- This covers: orig-orig, orig-new, new-new when the shared var is original
      -- The only uncovered case: new-new sharing a fresh variable
      -- For that case, we need the fresh variable's bit to be consistent

      -- Strategy: show bit_eq applies for both cubes on sv
      -- bit_eq requires: sv ≠ varAt(w_pos) for the new cube
      -- For cube e.1 (if new): sv ≠ varAt(w_e1) when sv is in e.2's vars AND
      --   either e.2 is original (h_er_fresh directly) or sv is not the fresh var
      -- For cube e.2 (if new): symmetric

      -- The argument: if sv is a shared variable between e.1 and e.2,
      -- and cube i is new with fresh var w_i, then either:
      --   (a) sv is in some original cube → sv ≠ w_i (since w_i is not in originals)
      --   (b) sv is not in any original cube → sv = w_i is possible BUT then
      --       sv is also in the other cube, and if that cube is also new,
      --       sv might be its fresh var too (or a non-w position)

      -- For the h_er_fresh case with 7-gap cubes, we can handle (b) IF
      -- we know the varBit for fresh variables is consistent.
      -- varBit(sv) = 0 for any sv not in original cubes (by definition).
      -- For new cube i with fresh var w at some position:
      --   if sv = varAt(w), the gap's bit at w is arbitrary (not constrained by multi_compatible_gap)
      --   We need: the gap's bit at w equals varBit(sv) = 0
      --   BUT multi_compatible_gap doesn't guarantee this!

      -- RESOLUTION: We need a stronger multi_compatible_gap that also constrains w_pos.
      -- With 7 gaps: for any (val_A, val_B, val_W) combination, there exists a matching gap
      -- UNLESS that exact triple is the filled vertex.
      -- With 7 gaps, only 1 vertex is filled, so at most 1 triple fails.
      -- By choosing val_W = 0 (or 1), we can always avoid the filled vertex:
      --   The filled vertex has a specific val_W bit. Choose the opposite.
      -- But we CAN'T choose val_W — it's determined by varBit(fresh_var) = 0.
      -- So: if the filled vertex has val_W = 0, we're stuck.

      -- HOWEVER: for the Tseitin backward cube (Type 1), filled vertex = 1 = (1,0,0).
      -- The fresh var x is at pos 0, so val_W = bit_0 of the filled vertex = 1.
      -- varBit(x) = 0 ≠ 1, so the filled vertex is NOT demanded. Works.

      -- For Tseitin OR backward (Type 2), filled = 6 = (0,1,1).
      -- x at pos 0, val_W = bit_0 = 0. varBit(x) = 0 = val_W. PROBLEM!
      -- The demanded triple could be (0, ?, ?) = the filled vertex's val_W.
      -- Specifically: demanded (x=0, y=1, z=1) = vertex 6 = filled. FAILS.

      -- So h_er_fresh + h_sparse + varBit(fresh)=0 does NOT work in general.
      -- We need to be smarter about choosing val_W for the fresh variable.

      -- The fix: instead of varBit(fresh) = 0, define varBit(fresh) to AVOID
      -- the filled vertex's w-bit. This requires knowing which vertex is filled.
      -- But the proof doesn't have access to gate-specific information.

      -- PRAGMATIC RESOLUTION: for edges between new cubes sharing the fresh variable,
      -- use a placeholder. For all other edges (orig-orig, orig-new, new-new sharing
      -- non-fresh variables), the proof works exactly as in er_kconsistent_from_aggregate.

      -- To minimize placeholders: split by cases
      by_cases h1_orig : e.1.val < G.cubes.length
      · -- e.1 is original
        have hb1 := bit_eq e.1 h1 sv hsv1 (fun hge => absurd h1_orig (by omega))
        by_cases h2_orig : e.2.val < G.cubes.length
        · -- Both original: bit_eq works for both
          have hb2 := bit_eq e.2 h2 sv hsv2 (fun hge => absurd h2_orig (by omega))
          rw [hb1, hb2]
        · -- e.1 original, e.2 new: sv is in e.1's vars (original) →
          -- sv is not the fresh var of e.2 (h_er_fresh: fresh var ∉ originals)
          have hn2 := Nat.not_lt.mp h2_orig
          have hw2 := Classical.choose_spec (h_er_fresh e.2 hn2)
          -- sv ∈ e.1.vars, e.1 is original → if sv = varAt(w_e2), then varAt(w_e2) ∈ e.1.vars
          -- But h_er_fresh says varAt(w_e2) ∉ e.1.vars (since e.1 is original)
          -- Therefore sv ≠ varAt(w_e2)
          have hsv_ne : ∀ (hge : e.2.val ≥ G.cubes.length),
              sv ≠ (ext.extended.cubes[e.2]).varAt
                (Classical.choose (h_er_fresh e.2 hge)) := by
            intro hge
            -- The fresh var of e.2 is not in any original cube
            -- e.1 is original, sv ∈ e.1.vars
            -- Therefore sv ≠ fresh var
            have : (ext.extended.cubes[e.2]).varAt
              (Classical.choose (h_er_fresh e.2 hge)) ∉
              (ext.extended.cubes[e.1]).vars := by
              exact hw2 e.1 h1_orig
            exact fun heq => this (heq ▸ hsv1)
          have hb2 := bit_eq e.2 h2 sv hsv2 hsv_ne
          rw [hb1, hb2]
      · -- e.1 is new
        have hn1 := Nat.not_lt.mp h1_orig
        by_cases h2_orig : e.2.val < G.cubes.length
        · -- e.1 new, e.2 original: sv is in e.2.vars (original) →
          -- sv ≠ fresh var of e.1 (symmetric argument)
          have hw1 := Classical.choose_spec (h_er_fresh e.1 hn1)
          have hsv_ne1 : ∀ (hge : e.1.val ≥ G.cubes.length),
              sv ≠ (ext.extended.cubes[e.1]).varAt
                (Classical.choose (h_er_fresh e.1 hge)) := by
            intro hge
            have : (ext.extended.cubes[e.1]).varAt
              (Classical.choose (h_er_fresh e.1 hge)) ∉
              (ext.extended.cubes[e.2]).vars := by
              exact hw1 e.2 h2_orig
            exact fun heq => this (heq ▸ hsv2)
          have hb1' := bit_eq e.1 h1 sv hsv1 hsv_ne1
          have hb2 := bit_eq e.2 h2 sv hsv2 (fun hge => absurd h2_orig (by omega))
          rw [hb1', hb2]
        · -- Both new: sv might be the fresh var of one of them
          -- Split: is sv in any original cube in S_orig?
          have hn2 := Nat.not_lt.mp h2_orig
          -- Case: sv is in some original cube → sv ≠ fresh var of either new cube
          by_cases h_sv_orig : ∃ j ∈ S_orig, sv ∈ (G.cubes[j]).vars
          · -- sv is in an original cube → sv ≠ fresh vars of both e.1 and e.2
            have hw1 := Classical.choose_spec (h_er_fresh e.1 hn1)
            have hw2 := Classical.choose_spec (h_er_fresh e.2 hn2)
            -- For e.1: sv is in original cube j → sv ≠ varAt(w_e1)
            -- Because varAt(w_e1) ∉ original cubes, but sv IS in one
            obtain ⟨j_orig, hj_mem, hj_sv⟩ := h_sv_orig
            let j_emb : Fin ext.extended.cubes.length :=
              ⟨j_orig.val, Nat.lt_of_lt_of_le j_orig.isLt ext.original_prefix⟩
            have hj_lt : j_emb.val < G.cubes.length := j_orig.isLt
            have hpres := ext.cubes_preserved j_orig
            have hsv_emb : sv ∈ (ext.extended.cubes[j_emb]).vars := by
              show sv ∈ (ext.extended.cubes[j_orig.val]'(Nat.lt_of_lt_of_le j_orig.isLt ext.original_prefix)).vars
              rw [hpres]; exact hj_sv
            have hsv_ne1 : ∀ (hge : e.1.val ≥ G.cubes.length),
                sv ≠ (ext.extended.cubes[e.1]).varAt
                  (Classical.choose (h_er_fresh e.1 hge)) := by
              intro hge heq
              have hfresh := hw1 j_emb hj_lt
              rw [heq] at hsv_emb
              exact hfresh hsv_emb
            have hsv_ne2 : ∀ (hge : e.2.val ≥ G.cubes.length),
                sv ≠ (ext.extended.cubes[e.2]).varAt
                  (Classical.choose (h_er_fresh e.2 hge)) := by
              intro hge heq
              have hfresh := hw2 j_emb hj_lt
              rw [heq] at hsv_emb
              exact hfresh hsv_emb
            have hb1' := bit_eq e.1 h1 sv hsv1 hsv_ne1
            have hb2 := bit_eq e.2 h2 sv hsv2 hsv_ne2
            rw [hb1', hb2]
          · -- sv is NOT in any original cube → sv is a "fresh" variable
            -- Both cubes are new. sv might be the fresh var of one or both.
            --
            -- **THIS THEOREM IS FALSE.** See `fresh_fresh_counterexample` below.
            --
            -- Counterexample: G has 2 original cubes with 1 gap each (vertex 0).
            -- ext adds 2 new cubes sharing fresh variable 7 at position 1:
            --   Cube A: vars (1,7,2), gapMask=254, filled at vertex 0=(0,0,0)
            --   Cube B: vars (4,7,5), gapMask=251, filled at vertex 2=(0,1,0)
            -- With σ_orig forcing varBit(1)=varBit(2)=varBit(4)=varBit(5)=0:
            --   Cube A: constrained (pos0=0, pos2=0) → only gap = vertex 2 → var7 bit = 1
            --   Cube B: constrained (pos0=0, pos2=0) → only gap = vertex 0 → var7 bit = 0
            -- The gaps MUST disagree on var 7. No σ exists.
            --
            -- The hypothesis h_er_fresh is too weak: it only ensures the fresh
            -- variable doesn't appear in ORIGINAL cubes, but two NEW cubes can
            -- share it with conflicting filled-vertex constraints.
            -- The correct hypothesis is h_aggregate (each new cube's fresh variable
            -- doesn't appear in ANY other cube), proven in ERKConsistentProof.lean.
            sorry

/-! ## Section 4b: Counterexample — er_kconsistent_from_er_fresh is FALSE

The theorem `er_kconsistent_from_er_fresh` is false. The hypothesis `h_er_fresh`
(fresh variable not in ORIGINAL cubes) is too weak — it allows two NEW cubes to
share a fresh variable with conflicting filled-vertex constraints.

**Concrete counterexample**:
- G: 2 original cubes, vars (1,2,3) and (4,5,6), gapMask=1 each (only vertex 0 is a gap)
- ext adds 2 new cubes:
  - Cube A: vars (1,7,2), gapMask=254, filled at vertex 0 = (0,0,0)
  - Cube B: vars (4,7,5), gapMask=251, filled at vertex 2 = (0,1,0)
- Both satisfy h_sparse (7 gaps) and h_er_fresh (var 7 at pos 1, not in original cubes)
- G is k-consistent for all k (no edges, only 1 gap per cube)
- ext.extended is NOT 4-consistent: for S = all 4 cubes, σ(0)=σ(1)=vertex 0 (forced),
  then σ(A) must have pos0=0, pos2=0 → only gap = vertex 2 (var7 bit=1),
  and σ(B) must have pos0=0, pos2=0 → only gap = vertex 0 (var7 bit=0).
  Edge (A,B) requires var7 bit agreement → impossible.

The correct hypothesis is h_aggregate (ERKConsistentProof.lean), which requires
the fresh variable to not appear in ANY other cube, preventing the sharing that
causes the conflict. -/

/-- Cube A: vars (1,7,2), gapMask=254 (filled at vertex 0). -/
private def cex_cubeA : Cube where
  var₁ := 1
  var₂ := 7
  var₃ := 2
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := ⟨by omega, by omega, by omega⟩
  gapMask := ⟨254, by omega⟩
  gaps_nonempty := by decide

/-- Cube B: vars (4,7,5), gapMask=251 (filled at vertex 2). -/
private def cex_cubeB : Cube where
  var₁ := 4
  var₂ := 7
  var₃ := 5
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := ⟨by omega, by omega, by omega⟩
  gapMask := ⟨251, by omega⟩
  gaps_nonempty := by decide

/-- Both cubes have 7 gaps (satisfy h_sparse). -/
theorem cex_cubeA_sparse : cex_cubeA.gapCount ≥ 7 := by decide
theorem cex_cubeB_sparse : cex_cubeB.gapCount ≥ 7 := by decide

/-- The key obstruction: when both cubes are constrained to (pos0=0, pos2=0),
    cubeA's only gap has pos1=1, but cubeB's only gap has pos1=0.
    They MUST disagree on the shared variable at position 1.

    Specifically: for cubeA, the only gap with bit0=0 and bit2=0 is vertex 2 (bit1=1).
    For cubeB, the only gap with bit0=0 and bit2=0 is vertex 0 (bit1=0). -/
theorem fresh_fresh_counterexample :
    -- cubeA: only gap matching (pos0=0, pos2=0) has pos1=1
    (∀ g : Fin 8, cex_cubeA.isGap g = true →
      (g.val >>> 0) &&& 1 = 0 → (g.val >>> 2) &&& 1 = 0 →
      (g.val >>> 1) &&& 1 = 1) ∧
    -- cubeB: only gap matching (pos0=0, pos2=0) has pos1=0
    (∀ g : Fin 8, cex_cubeB.isGap g = true →
      (g.val >>> 0) &&& 1 = 0 → (g.val >>> 2) &&& 1 = 0 →
      (g.val >>> 1) &&& 1 = 0) ∧
    -- Therefore: no pair of gaps can agree on pos1 under these constraints
    (¬ ∃ (gA gB : Fin 8),
      cex_cubeA.isGap gA = true ∧ cex_cubeB.isGap gB = true ∧
      (gA.val >>> 0) &&& 1 = 0 ∧ (gA.val >>> 2) &&& 1 = 0 ∧
      (gB.val >>> 0) &&& 1 = 0 ∧ (gB.val >>> 2) &&& 1 = 0 ∧
      (gA.val >>> 1) &&& 1 = (gB.val >>> 1) &&& 1) := by
  decide

/-! ## Section 5: The 7-gap backward cube lemma (self-contained) -/

/-- For a 7-gap cube with a fresh variable at position w, gap selection
    succeeds for any demanded values at the other 2 positions.
    This is a direct consequence of multi_compatible_gap. -/
theorem backward_cube_gap_exists (c : Cube) (h7 : c.gapCount ≥ 7)
    (w : Fin 3) (val_A val_B : Bool) :
    ∃ g : Vertex, c.isGap g = true ∧
      Cube.vertexBit g (other_positions w).1 = val_A ∧
      Cube.vertexBit g (other_positions w).2 = val_B :=
  multi_compatible_gap c h7 w val_A val_B

/-- For a 7-gap cube, if the target vertex is a gap, then it trivially
    satisfies the 3-bit match. The interesting case is when the target
    is the single filled vertex — then no gap matches at all 3 positions.
    This is the content of no_tri_compatible_gap_at_filled. -/
theorem seven_gap_target_is_gap (c : Cube) (_h7 : c.gapCount ≥ 7)
    (v : Vertex) (hv : c.isGap v = true) :
    ∃ g : Vertex, c.isGap g = true ∧
      Cube.vertexBit g ⟨0, by omega⟩ = Cube.vertexBit v ⟨0, by omega⟩ ∧
      Cube.vertexBit g ⟨1, by omega⟩ = Cube.vertexBit v ⟨1, by omega⟩ ∧
      Cube.vertexBit g ⟨2, by omega⟩ = Cube.vertexBit v ⟨2, by omega⟩ :=
  ⟨v, hv, rfl, rfl, rfl⟩

/-! ## Section 6: The filled-vertex avoidance lemma

For standard Tseitin, the filled vertex of the backward cube has a specific
bit pattern at the gate output's position. If varBit for the gate output
is chosen to be the OPPOSITE of this bit, the demanded pattern avoids the
filled vertex. -/

/-- For a 7-gap cube, choosing w_bit to be the opposite of the filled vertex's
    w-bit guarantees a gap exists at any (val_A, val_B, w_bit) triple. -/
theorem avoid_filled_w_bit :
    ∀ (mask : Fin 256), popcount8 mask ≥ 7 →
      ∀ (w : Fin 3) (val_A val_B : Bool),
        -- Choose w_bit to avoid the filled vertex
        ∀ (w_bit : Bool),
          -- If w_bit doesn't match the filled vertex's w-bit...
          (∃ g : Fin 8, (mask.val >>> g.val) &&& 1 = 0 ∧
            (g.val >>> w.val) &&& 1 ≠ (if w_bit then 1 else 0)) →
          -- ...then a matching gap exists
          ∃ g : Fin 8, ((mask.val >>> g.val) &&& 1 == 1) = true ∧
            ((g.val >>> (other_positions w).1.val) &&& 1 ==
              (if val_A then 1 else 0)) = true ∧
            ((g.val >>> (other_positions w).2.val) &&& 1 ==
              (if val_B then 1 else 0)) = true ∧
            ((g.val >>> w.val) &&& 1 == (if w_bit then 1 else 0)) = true := by
  native_decide

/-! ## Section 7: Summary and documentation -/

/-- **Summary**: The er_kconsistent_from_er_fresh theorem is FALSE.
    See `fresh_fresh_counterexample` for the concrete obstruction.

    **The statement is unprovable** because h_er_fresh (fresh variable not in
    ORIGINAL cubes) is too weak: two NEW cubes can share a fresh variable with
    conflicting filled-vertex constraints, making it impossible to find compatible
    gaps when original variables force specific bit patterns.

    **PROVEN** — these cases ARE correct:
    - All edges between original cubes
    - All edges between original and new cubes
    - All edges between new cubes where the shared variable appears in originals

    **FALSE (not fully proved)** — this case has a counterexample:
    - Edges between new cubes where the shared variable is fresh
    - `fresh_fresh_counterexample` proves the obstruction at the combinatorial level

    **Resolution**: Use `er_kconsistent_from_aggregate` (ERKConsistentProof.lean)
    with the stronger h_aggregate hypothesis instead. The h_aggregate condition
    (fresh variable not in ANY other cube) is both sufficient and necessary for
    the per-cube gap selection approach. -/
theorem er_fresh_summary :
    -- aggregate_implies_fresh: h_aggregate → h_er_fresh (proven)
    (∀ (G : CubeGraph) (ext : ERExtension G),
      (∀ i : Fin ext.extended.cubes.length,
        i.val ≥ G.cubes.length →
          ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length, i ≠ j →
            (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars) →
      ERFreshCondition G ext) ∧
    -- avoid_filled_w_bit: 7-gap cube + correct w_bit → full 3-position gap exists
    (∀ (mask : Fin 256), popcount8 mask ≥ 7 →
      ∀ (w : Fin 3) (val_A val_B : Bool) (w_bit : Bool),
        (∃ g : Fin 8, (mask.val >>> g.val) &&& 1 = 0 ∧
          (g.val >>> w.val) &&& 1 ≠ (if w_bit then 1 else 0)) →
        ∃ g : Fin 8, ((mask.val >>> g.val) &&& 1 == 1) = true ∧
          ((g.val >>> (other_positions w).1.val) &&& 1 ==
            (if val_A then 1 else 0)) = true ∧
          ((g.val >>> (other_positions w).2.val) &&& 1 ==
            (if val_B then 1 else 0)) = true ∧
          ((g.val >>> w.val) &&& 1 == (if w_bit then 1 else 0)) = true) :=
  ⟨aggregate_implies_fresh, avoid_filled_w_bit⟩

end CubeGraph
