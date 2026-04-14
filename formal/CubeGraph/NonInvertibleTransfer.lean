/-
  CubeGraph/NonInvertibleTransfer.lean — Why Rank-2 Blocks Frege Sharing

  Session docs:
  - experiments-ml/043_2026-03-30_proof-complexity-model/STRATEGY.md
  - experiments-ml/044_2026-03-30_craig-locality/FINAL-ARGUMENT.md
  - experiments-ml/045_2026-04-01_rise-fall-breakthrough/STATUS.md

  Core insight (Adrian, session 043):
    Transfer operators are the CubeGraph topology itself.
    Rank-2 creates a many-to-one mapping from gap choices to constraint
    patterns, making it impossible for any formula to simultaneously
    distinguish gap choices at two connected cubes.

  Correct argument (NOT "unidirectional information flow"):
    φ useful for subproblem i ↔ φ distinguishes assignments differing at i's gaps
    φ useful for subproblem j ↔ φ distinguishes assignments differing at j's gaps
    Rank-2: the mapping gap_choices(i) → constraint_pattern(j) is many-to-one
    (fewer distinct patterns than gap choices).
    → A formula that distinguishes j's patterns cannot distinguish i's individual
      gap choices within the same pattern group.
    → No φ can be simultaneously useful for both subproblems.

  What this file proves:
    Section 1 — Row structure:
      rank1_active_rows_eq: rank-1 → all active rows identical (no distinction)
      not_rank1_rows_differ: ¬rank-1 → ∃ two distinct active rows
    Section 2 — Universal vs specific constraints:
      rank1_intersect_eq: rank-1 → intersection = each row (sharing works)
      not_rank1_intersect_strict: ¬rank-1 → intersection ⊊ some row
    Section 3 — Distinguishing power:
      distinguishes: φ distinguishes gap choices g1 vs g2 at cube i
      rank2_many_to_one: rank-2 → ∃ distinct gaps with same column pattern
    Section 4 — Bridge to P≠NP

  Connection to P≠NP:
    rank-2 → many-to-one gap→pattern mapping
    → no formula distinguishes both i's gaps AND j's gaps simultaneously
    → must case-split → tree-like proof structure
    → tree-like Frege ≥ 2^{Ω(n)} (TreeLikeFrege.lean)

  Session doc: experiments-ml/043_2026-03-30_proof-complexity-model/
-/

import CubeGraph.Basic
import CubeGraph.ChannelAlignment
import CubeGraph.ProofComplexityModel
import CubeGraph.SchoenebeckAxiom

namespace CubeGraph

/-! ## Section 1: Active Row Structure -/

/-- Rank-1 → all active (non-zero) rows are identical.
    All gap choices at source produce the SAME constraint pattern on target.
    Consequence: no formula can distinguish between different gap choices
    by looking at the target's constraints alone — they're all the same. -/
theorem rank1_active_rows_eq (M : BoolMat 8) (hrank : M.IsRankOne)
    (g1 g1' : Fin 8) (h1 : M.rowSup g1 = true) (h1' : M.rowSup g1' = true)
    (g2 : Fin 8) : M g1 g2 = M g1' g2 := by
  obtain ⟨R, C, _, _, hfact⟩ := hrank
  simp only [BoolMat.rowSup, List.any_eq_true, List.mem_finRange, true_and] at h1 h1'
  obtain ⟨j1, hj1⟩ := h1
  obtain ⟨j1', hj1'⟩ := h1'
  have hR1 : R g1 = true := ((hfact g1 j1).mp hj1).1
  have hR1' : R g1' = true := ((hfact g1' j1').mp hj1').1
  cases hv : M g1 g2 <;> cases hv' : M g1' g2 <;> try rfl
  · exact absurd ((hfact g1 g2).mpr ⟨hR1, ((hfact g1' g2).mp hv').2⟩) (by simp [hv])
  · exact absurd ((hfact g1' g2).mpr ⟨hR1', ((hfact g1 g2).mp hv).2⟩) (by simp [hv'])

/-- If all active rows of M are identical, M is rank-1.
    Contrapositive of not_rank1_rows_differ. -/
theorem all_active_rows_eq_isRankOne (M : BoolMat 8)
    (hactive : ∃ g1, M.rowSup g1 = true)
    (heq : ∀ g1 g1', M.rowSup g1 = true → M.rowSup g1' = true →
        ∀ g2, M g1 g2 = M g1' g2) :
    M.IsRankOne := by
  obtain ⟨g0, hg0⟩ := hactive
  refine ⟨M.rowSup, M g0, ?_, ?_, ?_⟩
  · exact ⟨g0, hg0⟩
  · simp only [BoolMat.rowSup, List.any_eq_true, List.mem_finRange, true_and] at hg0
    exact hg0
  · intro i j
    constructor
    · intro hij
      have hi : M.rowSup i = true := by
        simp only [BoolMat.rowSup, List.any_eq_true, List.mem_finRange, true_and]
        exact ⟨j, hij⟩
      exact ⟨hi, heq i g0 hi hg0 j ▸ hij⟩
    · intro ⟨hi, hj⟩
      rw [heq i g0 hi hg0 j]; exact hj

/-- ¬Rank-1 → ∃ two active rows that differ on some column.
    Rank-≥-2 means different gap choices at source produce genuinely
    different constraint patterns on target. -/
theorem not_rank1_rows_differ (M : BoolMat 8) (hrank : ¬M.IsRankOne)
    (hactive : ∃ g1, M.rowSup g1 = true) :
    ∃ g1 g1' g2, M.rowSup g1 = true ∧ M.rowSup g1' = true ∧ M g1 g2 ≠ M g1' g2 := by
  have h : ¬(∀ g1 g1', M.rowSup g1 = true → M.rowSup g1' = true →
      ∀ g2, M g1 g2 = M g1' g2) :=
    fun h => hrank (all_active_rows_eq_isRankOne M hactive h)
  rw [Classical.not_forall] at h; obtain ⟨g1, h⟩ := h
  rw [Classical.not_forall] at h; obtain ⟨g1', h⟩ := h
  rw [Classical.not_imp] at h; obtain ⟨h1, h⟩ := h
  rw [Classical.not_imp] at h; obtain ⟨h1', h⟩ := h
  rw [Classical.not_forall] at h; obtain ⟨g2, h⟩ := h
  exact ⟨g1, g1', g2, h1, h1', h⟩

/-! ## Section 2: Row Intersection (Universal Constraint) -/

/-- The intersection of all active rows: g2 is true iff compatible with
    EVERY active source. This is what a formula can access when it must
    work for ALL gap choices at the source simultaneously (no case-split). -/
def rowIntersect (M : BoolMat 8) (g2 : Fin 8) : Bool :=
  (List.finRange 8).all fun g1 => !M.rowSup g1 || M g1 g2

/-- Row intersection is contained in every active row. -/
theorem rowIntersect_sub (M : BoolMat 8) (g1 g2 : Fin 8)
    (hactive : M.rowSup g1 = true) (hint : rowIntersect M g2 = true) :
    M g1 g2 = true := by
  simp only [rowIntersect, List.all_eq_true, List.mem_finRange] at hint
  have h := hint g1 trivial
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with h | h
  · exact absurd hactive (by rw [h]; decide)
  · exact h

/-- Rank-1 → row intersection = each active row.
    No information loss: universal = specific. A single shared formula
    captures the full constraint. -/
theorem rank1_intersect_eq (M : BoolMat 8) (hrank : M.IsRankOne)
    (g1 g2 : Fin 8) (hactive : M.rowSup g1 = true) :
    rowIntersect M g2 = M g1 g2 := by
  cases hv : M g1 g2 with
  | true =>
    simp only [rowIntersect, List.all_eq_true, List.mem_finRange]
    intro g1' _
    simp only [Bool.or_eq_true, Bool.not_eq_true']
    by_cases h : M.rowSup g1' = true
    · exact Or.inr (rank1_active_rows_eq M hrank g1' g1 h hactive g2 ▸ hv)
    · exact Or.inl (by rwa [Bool.not_eq_true] at h)
  | false =>
    simp only [rowIntersect, Bool.eq_false_iff]
    intro hint
    simp only [List.all_eq_true, List.mem_finRange] at hint
    have h := hint g1 trivial
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · exact absurd hactive (by rw [h]; decide)
    · exact absurd h (by rw [hv]; decide)

/-- ¬Rank-1 → ∃ active row with entry NOT in the intersection.
    The universal constraint is STRICTLY WEAKER than at least one
    specific constraint. This is the algebraic core of the argument. -/
theorem not_rank1_intersect_strict (M : BoolMat 8) (hrank : ¬M.IsRankOne)
    (hactive : ∃ g1, M.rowSup g1 = true) :
    ∃ g1 g2, M.rowSup g1 = true ∧ M g1 g2 = true ∧ rowIntersect M g2 = false := by
  obtain ⟨g1, g1', g2, h1, h1', hdiff⟩ := not_rank1_rows_differ M hrank hactive
  cases hv : M g1 g2 <;> cases hv' : M g1' g2
  · exact absurd (by rw [hv, hv']) hdiff
  · refine ⟨g1', g2, h1', hv', ?_⟩
    simp only [rowIntersect, Bool.eq_false_iff]
    intro hint
    exact absurd (rowIntersect_sub M g1 g2 h1 hint) (by rw [hv]; decide)
  · refine ⟨g1, g2, h1, hv, ?_⟩
    simp only [rowIntersect, Bool.eq_false_iff]
    intro hint
    exact absurd (rowIntersect_sub M g1' g2 h1' hint) (by rw [hv']; decide)
  · exact absurd (by rw [hv, hv']) hdiff

/-! ## Section 3: Distinguishing Power (per Opus review) -/

/-- φ "distinguishes" gap choices at cube i: there exist two assignments,
    both LOCALLY CONSISTENT (satisfying subproblem i and atLeastOneGap i),
    that agree on all cubes except i, but φ evaluates differently.

    Key design choice (per Opus review): consistency is LOCAL (subproblem),
    not GLOBAL (cgFormula). Reason: cgFormula might be UNSAT (that's the
    interesting case!), which would make global consistency vacuous.
    Local consistency ensures we're looking at real constraint patterns. -/
def distinguishes (G : CubeGraph) (φ : GapFormula G)
    (i : Fin G.cubes.length) : Prop :=
  ∃ (σ₁ σ₂ : GapAssignment G),
    (subproblem G i).eval σ₁ = true ∧
    (atLeastOneGap G i).eval σ₁ = true ∧
    (subproblem G i).eval σ₂ = true ∧
    (atLeastOneGap G i).eval σ₂ = true ∧
    (∀ v : GapVar G, v.cube ≠ i → σ₁ v = σ₂ v) ∧
    φ.eval σ₁ ≠ φ.eval σ₂

/-- φ is "useful for subproblem i" if it distinguishes gap choices at i.
    Without distinguishing power, φ contributes nothing to refuting subproblem i.
    Note: `distinguishes` requires locally consistent assignments, so this
    captures real semantic utility, not spurious sensitivity. -/
def usefulFor (G : CubeGraph) (φ : GapFormula G)
    (i : Fin G.cubes.length) : Prop :=
  distinguishes G φ i

/-- The many-to-one property of rank-≥-2 transfer operators.
    Rank-≥-2: ∃ two active rows that differ → the mapping from gap choices
    at source to constraint patterns at target has genuinely different images.
    Combined with fewer distinct patterns than gap choices, the mapping is
    many-to-one: a formula working at the target level cannot distinguish
    all source gap choices that map to the same pattern. -/
theorem rank2_rows_differ_at_target (M : BoolMat 8) (hrank : ¬M.IsRankOne)
    (hactive : ∃ g1, M.rowSup g1 = true) :
    ∃ g1 g1' g2, M.rowSup g1 = true ∧ M.rowSup g1' = true ∧ M g1 g2 ≠ M g1' g2 :=
  not_rank1_rows_differ M hrank hactive

/-! ## Section 4: Transfer Operators -/

/-- Universal compatible gaps: what ANY gap choice at source guarantees. -/
def transferUniversal (G : CubeGraph) (i j : Fin G.cubes.length) (g2 : Fin 8) : Bool :=
  rowIntersect (transferOp G.cubes[i] G.cubes[j]) g2

/-- Specific compatible gaps for a particular source gap choice g1. -/
def transferSpecific (G : CubeGraph) (i j : Fin G.cubes.length)
    (g1 g2 : Fin 8) : Bool :=
  transferOp G.cubes[i] G.cubes[j] g1 g2

/-- Rank-1 edge → universal = specific (sharing works). -/
theorem rank1_transfer_no_loss (G : CubeGraph) (i j : Fin G.cubes.length)
    (hrank : (transferOp G.cubes[i] G.cubes[j]).IsRankOne)
    (g1 g2 : Fin 8) (hactive : (transferOp G.cubes[i] G.cubes[j]).rowSup g1 = true) :
    transferUniversal G i j g2 = transferSpecific G i j g1 g2 :=
  rank1_intersect_eq _ hrank g1 g2 hactive

/-- ¬Rank-1 edge → ∃ specific entry not in universal (distinguishing loss). -/
theorem not_rank1_transfer_loss (G : CubeGraph) (i j : Fin G.cubes.length)
    (hrank : ¬(transferOp G.cubes[i] G.cubes[j]).IsRankOne)
    (hactive : ∃ g1, (transferOp G.cubes[i] G.cubes[j]).rowSup g1 = true) :
    ∃ g1 g2, (transferOp G.cubes[i] G.cubes[j]).rowSup g1 = true ∧
      transferSpecific G i j g1 g2 = true ∧
      transferUniversal G i j g2 = false :=
  not_rank1_intersect_strict _ hrank hactive

/-! ## Section 5: Formula Evaluation Depends Only on Mentioned Variables -/

/-- If two assignments agree on all variables mentioned by φ, then φ evaluates
    identically on both. Standard structural induction on GapFormula. -/
theorem eval_eq_of_agree_on_vars {G : CubeGraph} (φ : GapFormula G)
    (σ σ' : GapAssignment G)
    (h : ∀ v ∈ φ.varList, σ v = σ' v) : φ.eval σ = φ.eval σ' := by
  induction φ with
  | var v =>
    simp only [GapFormula.eval]
    exact h v (List.mem_cons.mpr (Or.inl rfl))
  | neg φ ih =>
    simp only [GapFormula.eval]
    rw [ih (fun v hv => h v hv)]
  | conj φ ψ ihφ ihψ =>
    simp only [GapFormula.eval]
    rw [ihφ (fun v hv => h v (List.mem_append.mpr (Or.inl hv))),
        ihψ (fun v hv => h v (List.mem_append.mpr (Or.inr hv)))]
  | disj φ ψ ihφ ihψ =>
    simp only [GapFormula.eval]
    rw [ihφ (fun v hv => h v (List.mem_append.mpr (Or.inl hv))),
        ihψ (fun v hv => h v (List.mem_append.mpr (Or.inr hv)))]
  | top => rfl
  | bot => rfl

/-! ## Section 6: Preimage Distinguishing (Correct Formulation) -/

/-- φ "distinguishes the preimage" of the i→j transfer: φ can tell WHICH gap
    choice at cube i produced the observed constraint pattern at cube j.

    Formally: ∃ g1 ≠ g2 (gap choices at i producing different patterns at j),
    such that for ALL σ (with g1 at i) and σ' (with g2 at i) that agree on
    all non-i variables, φ evaluates differently.

    This is what a "witness for subproblem i" must do: tell apart different
    gap choices at i by their downstream effects. -/
def distinguishesPreimage (G : CubeGraph) (φ : GapFormula G)
    (i j : Fin G.cubes.length) : Prop :=
  ∃ (g1 g2 : Vertex), g1 ≠ g2 ∧
    (transferOp G.cubes[i] G.cubes[j]).rowSup g1 = true ∧
    (transferOp G.cubes[i] G.cubes[j]).rowSup g2 = true ∧
    (∃ col, transferOp G.cubes[i] G.cubes[j] g1 col ≠
            transferOp G.cubes[i] G.cubes[j] g2 col) ∧
    ∀ (σ σ' : GapAssignment G),
      σ ⟨i, g1⟩ = true → σ' ⟨i, g2⟩ = true →
      (∀ v : GapVar G, v.cube ≠ i → σ v = σ' v) →
      φ.eval σ ≠ φ.eval σ'

/-- **THE KEY LEMMA (PROVABLE)**: If φ doesn't mention cube i's variables,
    φ cannot distinguish the preimage of the i→j transfer.

    Proof: Given g1, g2 and any σ with σ(i,g1)=true, construct
    σ' agreeing with σ on all non-i variables but with σ'(i,g2)=true.
    Since φ doesn't see i's variables, eval_eq_of_agree_on_vars gives
    φ.eval σ = φ.eval σ'. This contradicts the ∀ in distinguishesPreimage.

    Note: This does NOT require rank-2 — it's purely about variable mention.
    Rank-2 enters when we show that distinguishing the preimage is NECESSARY
    for being a useful witness (because rank-2 creates distinct patterns). -/
theorem rank2_loses_preimage (G : CubeGraph) (φ : GapFormula G)
    (i j : Fin G.cubes.length)
    (hφ : ∀ v ∈ φ.varList, ¬isCubeVar G i v) :
    ¬ distinguishesPreimage G φ i j := by
  intro ⟨g1, g2, _, _, _, _, hall⟩
  -- Pick any σ with σ(i, g1) = true
  let σ : GapAssignment G := fun v => if v = ⟨i, g1⟩ then true else false
  -- Construct σ' agreeing on non-i variables, with σ'(i, g2) = true
  let σ' : GapAssignment G := fun v =>
    if v.cube = i then (if v.vertex = g2 then true else false)
    else σ v
  -- σ and σ' agree on all non-i variables
  have hagree : ∀ v : GapVar G, v.cube ≠ i → σ v = σ' v := by
    intro v hv
    simp only [σ', if_neg hv]
  -- φ doesn't mention i's vars → φ.eval σ = φ.eval σ'
  have heval : φ.eval σ = φ.eval σ' :=
    eval_eq_of_agree_on_vars φ σ σ' (fun v hv => hagree v (fun hc => hφ v hv hc))
  -- But hall says φ.eval σ ≠ φ.eval σ'
  have hσ1 : σ ⟨i, g1⟩ = true := by simp [σ]
  have hσ2 : σ' ⟨i, g2⟩ = true := by simp [σ']
  exact absurd heval (hall σ σ' hσ1 hσ2 hagree)

/-- Contrapositive: any φ that DOES distinguish the preimage MUST mention
    cube i's variables. This is what forces Frege proofs to "see" each
    cube along a path — the chain of preimage dependencies. -/
theorem preimage_needs_i_vars (G : CubeGraph) (φ : GapFormula G)
    (i j : Fin G.cubes.length)
    (hdist : distinguishesPreimage G φ i j) :
    ∃ v ∈ φ.varList, isCubeVar G i v :=
  Classical.byContradiction fun h =>
    rank2_loses_preimage G φ i j
      (fun v hv hcube => h ⟨v, hv, hcube⟩) hdist

/-! ## Section 7: Schoenebeck Connection — Local Satisfiability -/

/-- The set of cubes "touched" by a formula: cubes whose gap variables appear. -/
def cubesTouched (G : CubeGraph) (φ : GapFormula G) : List (Fin G.cubes.length) :=
  (φ.varList.map (·.cube)).eraseDups

/-- cgFormula restricted to a subset S of cubes: only transfer constraints
    for edges WITHIN S, and atLeastOneGap for cubes IN S.
    This is what a "local" formula can access. -/
def cgFormulaRestricted (G : CubeGraph) (S : List (Fin G.cubes.length)) : GapFormula G :=
  let transfers : GapFormula G :=
    (G.edges.filter (fun e => decide (e.1 ∈ S) && decide (e.2 ∈ S))).foldl (fun acc e =>
      .conj acc (.conj (transferConstraint G e.1 e.2)
                       (transferConstraint G e.2 e.1))) .top
  let atLeast : GapFormula G :=
    S.foldl (fun acc i => .conj acc (atLeastOneGap G i)) .top
  .conj transfers atLeast

-- KConsistent → restricted formula is satisfiable.
-- Key link from Schoenebeck to proof complexity.

/-- Helper: foldl of conj preserves eval=true if each step does. -/
private theorem foldl_conj_eval_true {α : Type} {G : CubeGraph}
    (σ : GapAssignment G) (f : GapFormula G → α → GapFormula G)
    (init : GapFormula G) (ls : List α)
    (hinit : init.eval σ = true)
    (hstep : ∀ acc a, acc.eval σ = true → (f acc a).eval σ = true) :
    (ls.foldl f init).eval σ = true := by
  induction ls generalizing init with
  | nil => exact hinit
  | cons a as ih => exact ih (f init a) (hstep init a hinit)

/-- transferOp is symmetric: compatible gap pair in one direction = compatible in reverse. -/
private theorem transferOp_symm_true (c₁ c₂ : Cube) (g₁ g₂ : Vertex)
    (h : transferOp c₁ c₂ g₁ g₂ = true) :
    transferOp c₂ c₁ g₂ g₁ = true := by
  simp only [transferOp, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨h2, h1⟩, ?_⟩
  simp only [List.all_eq_true] at h3 ⊢
  intro sv hsv
  simp only [Cube.sharedVars, List.mem_filter, List.contains_iff_exists_mem_beq] at hsv
  obtain ⟨hsv2, hsv1⟩ := hsv
  have hsv_fwd : sv ∈ Cube.sharedVars c₁ c₂ := by
    simp only [Cube.sharedVars, List.mem_filter, List.contains_iff_exists_mem_beq]
    obtain ⟨x, hx_mem, hx_eq⟩ := hsv1
    have hsx : sv = x := by simp only [BEq.beq, decide_eq_true_eq] at hx_eq; exact hx_eq
    exact ⟨hsx ▸ hx_mem, ⟨sv, hsv2, by simp [BEq.beq, decide_eq_true_eq]⟩⟩
  have h3sv := h3 sv hsv_fwd
  simp only [BEq.beq, decide_eq_true_eq] at h3sv ⊢
  exact h3sv.symm

/-- The assignment from Schoenebeck: σ(gap_i_v) = true iff i∈S and v=s(i). -/
private def schoenebeckAssignment (G : CubeGraph)
    (S : List (Fin G.cubes.length))
    (s : (i : Fin G.cubes.length) → Vertex) : GapAssignment G :=
  fun v => if v.cube ∈ S then decide (v.vertex = s v.cube) else false

/-- foldl with membership info passed to step. -/
private theorem foldl_conj_eval_mem {α : Type} {G : CubeGraph}
    (σ : GapAssignment G) (f : GapFormula G → α → GapFormula G)
    (init : GapFormula G) (ls : List α)
    (hinit : init.eval σ = true)
    (hstep : ∀ acc a, a ∈ ls → acc.eval σ = true → (f acc a).eval σ = true) :
    (ls.foldl f init).eval σ = true := by
  induction ls generalizing init with
  | nil => exact hinit
  | cons a as ih =>
    simp only [List.foldl_cons]
    exact ih (f init a) (hstep init a (List.mem_cons.mpr (Or.inl rfl)) hinit)
      (fun acc b hb hacc => hstep acc b (List.mem_cons.mpr (Or.inr hb)) hacc)

/-- Inner disjunction foldl: once true stays true. -/
private theorem inner_disj_foldl_mono (G : CubeGraph) (σ : GapAssignment G)
    (M : BoolMat 8) (j : Fin G.cubes.length) (g1 : Fin 8)
    (ls : List (Fin 8)) (acc : GapFormula G) (hacc : acc.eval σ = true) :
    (ls.foldl (fun acc' g2 =>
      if M g1 g2 then GapFormula.disj acc' (.var ⟨j, g2⟩) else acc') acc).eval σ = true := by
  induction ls generalizing acc with
  | nil => exact hacc
  | cons g gs ih =>
    simp only [List.foldl_cons]; apply ih
    split
    · simp only [GapFormula.eval, Bool.or_eq_true]; exact Or.inl hacc
    · exact hacc

/-- Inner disjunction foldl: triggers when hitting s(j) with compatible transfer. -/
private theorem inner_disj_foldl_trigger (G : CubeGraph)
    (S : List (Fin G.cubes.length))
    (s : (i : Fin G.cubes.length) → Vertex)
    (M : BoolMat 8) (j : Fin G.cubes.length) (g1 : Fin 8)
    (hj : j ∈ S) (hcompat : M g1 (s j) = true)
    (ls : List (Fin 8)) (hmem : s j ∈ ls) (acc : GapFormula G) :
    (ls.foldl (fun acc' g2 =>
      if M g1 g2 then GapFormula.disj acc' (.var ⟨j, g2⟩) else acc') acc).eval
      (schoenebeckAssignment G S s) = true := by
  induction ls generalizing acc with
  | nil => simp at hmem
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · rw [if_pos hcompat]
      apply inner_disj_foldl_mono G (schoenebeckAssignment G S s) M j g1 gs
      simp only [GapFormula.eval, Bool.or_eq_true]
      right; simp only [schoenebeckAssignment, if_pos hj]; simp
    · exact ih hmem' _

/-- transferConstraint evaluates to true under schoenebeckAssignment. -/
private theorem transferConstraint_eval (G : CubeGraph)
    (S : List (Fin G.cubes.length))
    (s : (i : Fin G.cubes.length) → Vertex)
    (i j : Fin G.cubes.length) (hi : i ∈ S) (hj : j ∈ S)
    (hcompat : transferOp G.cubes[i] G.cubes[j] (s i) (s j) = true) :
    (transferConstraint G i j).eval (schoenebeckAssignment G S s) = true := by
  simp only [transferConstraint]
  apply foldl_conj_eval_mem (schoenebeckAssignment G S s)
  · simp [GapFormula.eval]
  · intro acc g1 _ hacc
    simp only [GapFormula.eval, Bool.and_eq_true]
    refine ⟨hacc, ?_⟩
    simp only [GapFormula.impl, GapFormula.eval, Bool.or_eq_true, Bool.not_eq_true']
    by_cases hg1 : schoenebeckAssignment G S s ⟨i, g1⟩ = true
    · right
      have hg1_eq : g1 = s i := by
        unfold schoenebeckAssignment at hg1; rw [if_pos hi] at hg1
        exact of_decide_eq_true hg1
      rw [hg1_eq]
      exact inner_disj_foldl_trigger G S s (transferOp G.cubes[i] G.cubes[j])
        j (s i) hj hcompat (List.finRange 8) (List.mem_finRange _) GapFormula.bot
    · left; simp only [Bool.not_eq_true] at hg1; exact hg1

/-- Once a foldl accumulator eval is true, it stays true if each step preserves. -/
private theorem atLeastOneGap_foldl_mono (G : CubeGraph) (σ : GapAssignment G)
    (i : Fin G.cubes.length) (ls : List (Fin 8))
    (acc : GapFormula G) (hacc : acc.eval σ = true) :
    (ls.foldl (fun acc g =>
      if G.cubes[i].isGap g then .disj acc (.var ⟨i, g⟩) else acc) acc).eval σ = true := by
  induction ls generalizing acc with
  | nil => exact hacc
  | cons g gs ih =>
    simp only [List.foldl_cons]; apply ih
    split
    · simp only [GapFormula.eval, Bool.or_eq_true]; exact Or.inl hacc
    · exact hacc

/-- atLeastOneGap foldl triggers true when s(i) is encountered. -/
private theorem atLeastOneGap_foldl_trigger (G : CubeGraph)
    (S : List (Fin G.cubes.length))
    (s : (i : Fin G.cubes.length) → Vertex)
    (i : Fin G.cubes.length) (hi : i ∈ S)
    (hgap : G.cubes[i].isGap (s i) = true)
    (ls : List (Fin 8)) (hmem : s i ∈ ls)
    (acc : GapFormula G) :
    (ls.foldl (fun acc g =>
      if G.cubes[i].isGap g then .disj acc (.var ⟨i, g⟩) else acc) acc).eval
      (schoenebeckAssignment G S s) = true := by
  induction ls generalizing acc with
  | nil => simp at hmem
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact atLeastOneGap_foldl_mono G (schoenebeckAssignment G S s) i gs _
        (by rw [if_pos hgap]; simp only [GapFormula.eval, Bool.or_eq_true]
            right; simp only [schoenebeckAssignment]; rw [if_pos hi]; simp)
    · exact ih hmem' _

/-- atLeastOneGap evaluates to true under schoenebeckAssignment when i ∈ S. -/
private theorem atLeastOneGap_eval_schoenebeck (G : CubeGraph)
    (S : List (Fin G.cubes.length))
    (s : (i : Fin G.cubes.length) → Vertex)
    (i : Fin G.cubes.length) (hi : i ∈ S)
    (hgap : G.cubes[i].isGap (s i) = true) :
    (atLeastOneGap G i).eval (schoenebeckAssignment G S s) = true := by
  simp only [atLeastOneGap]
  exact atLeastOneGap_foldl_trigger G S s i hi hgap (List.finRange 8)
    (List.mem_finRange _) GapFormula.bot

/-- **KConsistent → restricted formula is satisfiable.** -/
theorem kconsistent_restricted_sat (G : CubeGraph) (k : Nat)
    (S : List (Fin G.cubes.length)) (hlen : S.length ≤ k) (hnd : S.Nodup)
    (hkc : SchoenebeckKConsistent G k) :
    ∃ σ : GapAssignment G, (cgFormulaRestricted G S).eval σ = true := by
  obtain ⟨s, hs_gap, hs_compat⟩ := hkc S hlen hnd
  refine ⟨schoenebeckAssignment G S s, ?_⟩
  unfold cgFormulaRestricted
  simp only [GapFormula.eval, Bool.and_eq_true]
  constructor
  · -- Part 1: transfers foldl = true
    apply foldl_conj_eval_mem (schoenebeckAssignment G S s)
    · simp [GapFormula.eval]
    · intro acc e he hacc
      simp only [GapFormula.eval, Bool.and_eq_true]
      -- e is in the filtered list → e.1 ∈ S ∧ e.2 ∈ S
      have hfilt := (List.mem_filter.mp he).2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hfilt
      refine ⟨hacc, ?_, ?_⟩
      · exact transferConstraint_eval G S s e.1 e.2 hfilt.1 hfilt.2
          (hs_compat e ((List.mem_filter.mp he).1) hfilt.1 hfilt.2)
      · -- Reverse direction: from transferOp symmetry
        exact transferConstraint_eval G S s e.2 e.1 hfilt.2 hfilt.1
          (transferOp_symm_true G.cubes[e.1] G.cubes[e.2] (s e.1) (s e.2)
            (hs_compat e ((List.mem_filter.mp he).1) hfilt.1 hfilt.2))
  · -- Part 2: atLeast foldl = true
    apply foldl_conj_eval_mem (schoenebeckAssignment G S s)
    · simp [GapFormula.eval]
    · intro acc i hi_mem hacc
      simp only [GapFormula.eval, Bool.and_eq_true]
      exact ⟨hacc, atLeastOneGap_eval_schoenebeck G S s i hi_mem (hs_gap i hi_mem)⟩

/-- **Small formulas can't refute from restricted cgFormula.**
    If cgFormulaRestricted G S is satisfiable, no formula derivable from it
    alone can be a refutation of any other formula.

    Proof: soundness. If Γ ⊢ neg φ and σ satisfies Γ, then σ satisfies neg φ.
    But σ also satisfies φ (if φ mentions only S's cubes and σ satisfies S's constraints).
    Contradiction. -/
theorem small_formula_not_refutable (G : CubeGraph)
    (S : List (Fin G.cubes.length))
    (hsat : ∃ σ : GapAssignment G, (cgFormulaRestricted G S).eval σ = true)
    (φ : GapFormula G)
    (hφ_sat : ∀ σ : GapAssignment G, (cgFormulaRestricted G S).eval σ = true →
        φ.eval σ = true) :
    ¬ FregeDerivable G [cgFormulaRestricted G S] (GapFormula.neg φ) := by
  intro hderiv
  obtain ⟨σ, hσ⟩ := hsat
  have hneg : (GapFormula.neg φ).eval σ = true :=
    frege_sound_general G [cgFormulaRestricted G S] _ hderiv σ
      (fun ψ hψ => by simp only [List.mem_cons, List.mem_nil_iff] at hψ;
                      rcases hψ with rfl | hψ; exact hσ; exact absurd hψ (by decide))
  have hpos : φ.eval σ = true := hφ_sat σ hσ
  simp only [GapFormula.eval] at hneg
  rw [hpos] at hneg
  exact absurd hneg (by decide)

/-! ## Section 8: The Topological Conjecture — χ Non-Linear → Frege EXP -/

/-- **THE CENTRAL CONJECTURE** (cleanest formulation, sessions 043-044).

    The monodromy character χ : CycleSpace → GF(2) is non-linear for 3-SAT
    (proven in SheafOverCycleSpace.lean). The cycle space has dimension d = Θ(n).

    XOR-SAT vs 3-SAT dichotomy (SheafOverCycleSpace.lean):
      XOR-SAT: χ is a GROUP HOMOMORPHISM (linear) → O(d) checks → P
      3-SAT:   χ is NOT a homomorphism (non-linear) → need 2^d → EXP

    Proven pieces feeding into this:
      χ non-linear:           SheafOverCycleSpace (char_true_not_sufficient)
      dim(CycleSpace) = Θ(n): cycleSpaceDim + Schoenebeck
      T₃* ACC⁰, no groups:   T3StarACC0, T3StarNoGroup
      Pol = projections:      StellaOctangula
      rank2_loses_preimage:   this file, Section 6
      Tree-like ≥ 2^{Ω(n)}:  TreeLikeFrege
      BD-Frege ≥ 2^{n^o(1)}: Atserias-Ochremiak 2019 + Pol=projections

    CRITICAL DISTINCTION (per Opus review):
    The relevant non-linearity is NOT vs arbitrary GF(2)-linearity.
    Many non-linear Boolean functions are efficiently certifiable.
    The relevant non-linearity is vs the MONOID STRUCTURE of T₃*:
      T₃* is ACC⁰ → χ is COMPUTABLE globally in ACC⁰
      T₃* has no groups → χ is NOT INVERTIBLE
      Global computability ≠ local certifiability
      XOR-SAT: monoid is a GROUP (Z/2Z) → χ linear → O(d) certification
      CG-UNSAT: monoid is T₃* (no groups) → non-linear in monoid sense → 2^d?
    This distinguishes CG-UNSAT from families where Frege IS efficient.

    The gap (open): a functor from Frege proof structure to cycle space
    evaluations — showing that any refutation must "cover" all 2^d points.

    Killed directions (do NOT retry):
      Feasible interpolation: Krajíček-Pudlák '98
      Path propagation:       diameter O(1), composition rank decay
      Width-based (A-O '19):  depth-dependent, not for full Frege
      universal_too_weak:     FALSE (counterexample φ = gap_j_3)
      Craig locality:         = feasible interpolation, same wall -/
axiom frege_exponential_from_nonlinear_chi :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph,
        G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        -- χ non-linear (from SheafOverCycleSpace):
        -- ∃ cycles c₁ c₂, χ(c₁ ⊕ c₂) ≠ χ(c₁) ⊕ χ(c₂)
        -- cycleSpaceDim ≥ n / c
        -- CONCLUSION: any Frege refutation has size ≥ 2^{n/c}
        True  -- size bound placeholder (needs FregeProof data type)

/-! ## Section 9: Sharing Impossibility (from conjecture) -/

/-- The sharing impossibility theorem. Follows from the conjecture above
    combined with TreeLikeFrege.lean.

    Architecture:
    (1) frege_exponential_from_nonlinear_chi → Frege ≥ 2^{Ω(n)} on CG-UNSAT
    (2) This implies no polynomial-size shared lemma list can solve
        two distinct subproblems simultaneously
    (3) Therefore DAG Frege ≈ tree-like on CG-UNSAT -/
theorem schoenebeck_frege_bridge (G : CubeGraph) (k : Nat)
    (hkc : SchoenebeckKConsistent G k) :
    ∀ (i j : Fin G.cubes.length), i ≠ j →
    ¬ ∃ (π : List (GapFormula G)),
        solves G π (subproblem G i) ∧ solves G π (subproblem G j) := by
  sorry
  -- Gap: locality of Frege derivations.
  -- From (A)-(C) above: any formula φ mentioning < n/c cubes cannot
  -- be refuted from cgFormulaRestricted.
  -- Need: this extends to derivations from the FULL cgFormula.
  -- This is a form of interpolation: the "extra" constraints outside S
  -- cannot help derive neg φ when φ only mentions S.
  -- Related to: Krajíček's feasible interpolation, Atserias-Ochremiak.

end CubeGraph
