/-
  CubeGraph/EFLowerBound.lean — Generalized ER Lower Bound (any abbreviation type)

  NAMING NOTE: Despite the filename, this proves a RESOLUTION lower bound on
  extended formulas — i.e., a generalized ER (Extended Resolution) result.
  It does NOT prove Extended Frege (EF) lower bounds, because EF uses Frege
  proof rules (not Resolution), and k-consistency does not imply Frege size bounds.
  The distinction: ER = Resolution + abbreviations, EF = Frege + abbreviations.

  What this file DOES prove:
  - HasCorrectGaps: weaker than gapCount ≥ 7, holds for ANY ψ(A,B) with p fresh
  - Resolution on ANY extension with HasCorrectGaps needs 2^{Ω(n)} size
  - This covers ER with AND, OR, XOR, or ANY Boolean abbreviation

  What this file does NOT prove:
  - EF (Frege + abbreviations) lower bounds
  - Frege lower bounds (major open problem, 50+ years)
  - P ≠ NP

  Confirmed experimentally: F5.0 shows b(T(G)) = b(G) for both AND and XOR
  abbreviations on random 3-SAT at ρ_c (n=8-15, 172 UNSAT formulas).

  See: ERKConsistentProof.lean (original proof with h_sparse ≥ 7)
  See: ERAggregateBricks.lean (multi_compatible_gap proves HasCorrectGaps from h_sparse)
  See: ERLowerBound.lean (ER lower bound — requires h_sparse ≥ 7)
  See: PCLowerBound.lean, CPLowerBound.lean, AC0FregeLowerBound.lean (other proof systems)
  Experiment: experiments-ml/025_2026-03-19_synthesis/bridge/F5.0-RESULTS.md
  Plan: experiments-ml/025_2026-03-19_synthesis/bridge/D7e-PLAN-EF-EXPONENTIAL-V2.md
  Gap analysis: experiments-ml/025_2026-03-19_synthesis/bridge/D7f-PLAN-V2-FREGE-GAP.md
-/

import CubeGraph.ERKConsistentInduction
import CubeGraph.ERLowerBound

namespace CubeGraph

open BoolMat

/-! ## Section 1: HasCorrectGaps — strictly weaker than gapCount ≥ 7 -/

/-- A cube has "correct gaps" at position w if for every pair of bit values
    at the other two positions, there exists a compatible gap.
    This is strictly weaker than gapCount ≥ 7 and holds for ANY
    abbreviation p ↔ ψ(A,B) where p is at position w. -/
def HasCorrectGaps (c : Cube) (w_pos : Fin 3) : Prop :=
  ∀ (val_A val_B : Bool),
    ∃ g : Vertex, c.isGap g = true ∧
      Cube.vertexBit g (other_positions w_pos).1 = val_A ∧
      Cube.vertexBit g (other_positions w_pos).2 = val_B

/-- gapCount ≥ 7 implies HasCorrectGaps (from multi_compatible_gap). -/
theorem sparse_implies_correct_gaps (c : Cube) (w : Fin 3)
    (h : c.gapCount ≥ 7) : HasCorrectGaps c w :=
  fun vA vB => multi_compatible_gap c h w vA vB

/-! ## Section 2: EF k-consistency preservation -/

/-- **Extended Frege k-consistency preservation**: KConsistent extends from G to T(G)
    for ANY abbreviation type with fresh variables and correct gaps.

    This generalizes er_kconsistent_from_aggregate:
    - Old: h_sparse (gapCount ≥ 7) + h_aggregate (fresh var)
    - New: h_correct (fresh var + HasCorrectGaps) — strictly weaker

    HasCorrectGaps holds for ANY ψ(A,B) with p fresh: the vertex
    (a, b, ψ(a,b)) is always a gap (satisfies all clauses of p ↔ ψ). -/
theorem ef_kconsistent_from_correct_gaps
    (G : CubeGraph) (k : Nat) (ext : ERExtension G)
    (h_correct : ∀ i : Fin ext.extended.cubes.length,
      i.val ≥ G.cubes.length →
        ∃ w_pos : Fin 3,
          (∀ j : Fin ext.extended.cubes.length, i ≠ j →
            (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars) ∧
          HasCorrectGaps (ext.extended.cubes[i]) w_pos)
    (hkc : KConsistent G k) :
    KConsistent ext.extended k := by
  classical
  intro S hlen hnd
  let proj := fun (i : Fin ext.extended.cubes.length) =>
    if h : i.val < G.cubes.length then some (⟨i.val, h⟩ : Fin G.cubes.length) else none
  let S_orig := S.filterMap proj
  have h_proj_len : S_orig.length ≤ k := Nat.le_trans (filterMap_length_le proj S) hlen
  have h_proj_nd : S_orig.Nodup := by
    show (S.filterMap fun (i : Fin ext.extended.cubes.length) =>
      if h : i.val < G.cubes.length then some (⟨i.val, h⟩ : Fin G.cubes.length) else none).Nodup
    exact filterMap_nodup_of_val_inj S hnd G.cubes.length ext.original_prefix
  obtain ⟨σ_orig, hv_orig, hc_orig⟩ := hkc S_orig h_proj_len h_proj_nd
  let varBit (v : Nat) : Nat :=
    if h : ∃ j ∈ S_orig, v ∈ (G.cubes[j]).vars
    then ((σ_orig (Classical.choose h)).val >>>
          ((G.cubes[Classical.choose h]).vars.idxOf v)) &&& 1
    else 0
  -- For each new cube: use HasCorrectGaps to get compatible gap
  let newGap (i : Fin ext.extended.cubes.length) (hn : ¬ i.val < G.cubes.length) : Vertex :=
    let w := Classical.choose (h_correct i (Nat.not_lt.mp hn))
    let c := ext.extended.cubes[i]
    let vA : Bool := varBit (c.varAt (other_positions w).1) == 1
    let vB : Bool := varBit (c.varAt (other_positions w).2) == 1
    Classical.choose ((Classical.choose_spec (h_correct i (Nat.not_lt.mp hn))).2 vA vB)
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
      exact ((Classical.choose_spec
        ((Classical.choose_spec (h_correct i (Nat.not_lt.mp hlt))).2
          (varBit ((ext.extended.cubes[i]).varAt
            (other_positions (Classical.choose (h_correct i (Nat.not_lt.mp hlt)))).1) == 1)
          (varBit ((ext.extended.cubes[i]).varAt
            (other_positions (Classical.choose (h_correct i (Nat.not_lt.mp hlt)))).2) == 1)))).1
  case compat =>
    have hσ_gap : ∀ i ∈ S, (ext.extended.cubes[i]).isGap (σ i) = true := by
      intro i hi; simp only [σ]; split
      · rename_i hlt; have := ext.cubes_preserved (⟨i.val, hlt⟩ : Fin G.cubes.length)
        change (ext.extended.cubes[i.val]'_).isGap _ = true
        rw [show ext.extended.cubes[i.val]'(i.isLt) =
              ext.extended.cubes[i.val]'(Nat.lt_of_lt_of_le hlt ext.original_prefix) from rfl, this]
        exact hv_orig _ (mem_filterMap_proj S i hi _ hlt)
      · rename_i hlt; exact ((Classical.choose_spec
          ((Classical.choose_spec (h_correct i (Nat.not_lt.mp hlt))).2
            (varBit ((ext.extended.cubes[i]).varAt
              (other_positions (Classical.choose (h_correct i (Nat.not_lt.mp hlt)))).1) == 1)
            (varBit ((ext.extended.cubes[i]).varAt
              (other_positions (Classical.choose (h_correct i (Nat.not_lt.mp hlt)))).2) == 1)))).1
    have bit_eq : ∀ i ∈ S, ∀ sv', sv' ∈ (ext.extended.cubes[i]).vars →
        (∀ (hge : i.val ≥ G.cubes.length),
          sv' ≠ (ext.extended.cubes[i]).varAt (Classical.choose (h_correct i hge))) →
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
        let w := Classical.choose (h_correct i hn)
        have h_pos := idxOf_at_other (ext.extended.cubes[i]) w sv' hsv' (h_nf hn)
        have gs := Classical.choose_spec
          ((Classical.choose_spec (h_correct i hn)).2
            (varBit ((ext.extended.cubes[i]).varAt (other_positions w).1) == 1)
            (varBit ((ext.extended.cubes[i]).varAt (other_positions w).2) == 1))
        change ((Classical.choose
          ((Classical.choose_spec (h_correct i hn)).2
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
    intro e he h1 h2
    by_cases hself : e.1 = e.2
    · rw [show ext.extended.cubes[e.2] = ext.extended.cubes[e.1] from by simp [hself],
          show σ e.2 = σ e.1 from by simp [σ, hself]]
      exact transferOp_self _ _ (hσ_gap e.1 h1)
    · apply gap_with_correct_bits_compatible _ _ _ _ (hσ_gap e.1 h1) (hσ_gap e.2 h2)
      intro sv hsv
      have hsv1 := (mem_sharedVars _ _ sv hsv).1
      have hsv2 := (mem_sharedVars _ _ sv hsv).2
      have hb1 := bit_eq e.1 h1 sv hsv1 (fun hge =>
        sv_ne_fresh ext.extended.cubes e.1 e.2
          (Classical.choose (h_correct e.1 hge)) sv hself
          (Classical.choose_spec (h_correct e.1 hge)).1 hsv2)
      have hb2 := bit_eq e.2 h2 sv hsv2 (fun hge =>
        sv_ne_fresh ext.extended.cubes e.2 e.1
          (Classical.choose (h_correct e.2 hge)) sv (Ne.symm hself)
          (Classical.choose_spec (h_correct e.2 hge)).1 hsv1)
      rw [hb1, hb2]

/-! ## Section 3: Generalized ER Borromean preservation -/

/-- **Generalized ER Borromean**: BorromeanOrder preserved under ANY abbreviation
    extension with fresh variables and correct gaps.
    Generalizes er_borromean_unconditional (which requires gapCount ≥ 7).

    NOTE: "EF" in the name is imprecise. This is a Resolution-based result
    (generalized ER), not an Extended Frege result. EF uses Frege rules,
    not Resolution, and k-consistency does not imply Frege size bounds. -/
theorem ef_borromean_unconditional (G : CubeGraph) (b : Nat)
    (hbo : BorromeanOrder G b) (ext : ERExtension G)
    (h_correct : ∀ i : Fin ext.extended.cubes.length,
      i.val ≥ G.cubes.length →
        ∃ w_pos : Fin 3,
          (∀ j : Fin ext.extended.cubes.length, i ≠ j →
            (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars) ∧
          HasCorrectGaps (ext.extended.cubes[i]) w_pos) :
    ¬ KConsistent ext.extended b ∧ (b > 0 → KConsistent ext.extended (b - 1)) :=
  ⟨fun h => hbo.1 (kconsistent_extends_to_originals G ext b h),
   fun hb => ef_kconsistent_from_correct_gaps G (b - 1) ext h_correct (hbo.2 hb)⟩

/-! ## Section 4: Generalized ER exponential (with ABD+BSW) -/

/-- **Generalized ER Resolution Lower Bound**: Resolution on ANY extended
    formula (with fresh variables and HasCorrectGaps) requires size ≥ 2^{Ω(n)}.

    Strictly stronger than er_resolution_lower_bound: applies to ANY
    abbreviation type (AND, OR, XOR, arbitrary ψ), not just sparse (≥ 7 gap).

    IMPORTANT: This is a RESOLUTION size bound on extended formulas.
    It proves ER (Extended Resolution) with any abbreviation is exponential.
    It does NOT prove EF (Extended Frege) is exponential, because EF uses
    Frege proof rules which are strictly more powerful than Resolution.
    The gap: k-consistency → Resolution width/size (ABD+BSW), but
    k-consistency ↛ Frege proof size (no known connection).

    Chain: Schoenebeck → KConsistent → HasCorrectGaps preserves → ABD+BSW → 2^{Ω(n)}. -/
theorem ef_resolution_lower_bound :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        (∀ ext : ERExtension G,
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length →
              ∃ w_pos : Fin 3,
                (∀ j : Fin ext.extended.cubes.length, i ≠ j →
                  (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars) ∧
                HasCorrectGaps (ext.extended.cubes[i]) w_pos) →
          minResolutionSize ext.extended ≥ 2 ^ (n / c)) := by
  obtain ⟨c₁, hc₁, h_sch⟩ := schoenebeck_linear
  obtain ⟨c₂, hc₂, h_abd⟩ := abd_bsw_resolution_exponential
  refine ⟨c₁ * c₂, by have := Nat.mul_le_mul hc₁ hc₂; omega, fun n hn => ?_⟩
  obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch n hn
  refine ⟨G, hsize, hunsat, fun ext h_cor => ?_⟩
  have hkc_ext := ef_kconsistent_from_correct_gaps G (n / c₁) ext h_cor hkc
  have hunsat_ext := ext.still_unsat
  have h := h_abd ext.extended (n / c₁) hkc_ext hunsat_ext
  rw [Nat.div_div_eq_div_mul] at h
  exact h

/-! ## HONEST ACCOUNTING

    What this file PROVES:
    - Resolution on ANY extension (with HasCorrectGaps) needs 2^{Ω(n)}
    - This generalizes ER to any abbreviation type (AND, XOR, arbitrary ψ)
    - HasCorrectGaps holds for ANY p ↔ ψ(A,B) with p fresh

    What this file does NOT prove:
    - Extended Frege (EF = Frege + abbreviations) lower bounds
    - Frege lower bounds (open problem: k-consistency ↛ Frege size)
    - P ≠ NP

    The gap from generalized ER to EF: EF uses Frege proof rules
    (modus ponens, conjunction intro, etc.), not Resolution.
    A single Frege step on formulas of size n can "see" n variables
    simultaneously, while Resolution sees O(1) per step.
    k-consistency bounds the "width" of what Resolution can see,
    but says nothing about the power of Frege's logical rules.

    See: D7f-PLAN-V2-FREGE-GAP.md for detailed gap analysis. -/

end CubeGraph
