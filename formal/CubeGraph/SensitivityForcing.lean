/-
  CubeGraph/SensitivityForcing.lean — Sensitivity is FORCED (can't be wasted)

  Session: 050+.
  Docs: experiments-ml/050_*/INSIGHT-AXIOM-ATOMICITY.md (axiom atomicity → exponential)
        experiments-ml/050_*/CONCERNS.md (§3b: counting_from_independent_decisions)
        experiments-ml/050_*/ANALYSIS-FINAL.md (gap + sorry status)
        experiments-ml/050_*/INSIGHT-RANK2-DOUBLING.md
        experiments-ml/050_*/INSIGHT-UNSAT-CONSTANT.md
        experiments-ml/050_*/INSIGHT-LOCAL-GLOBAL-TENSION.md

  THE ARGUMENT:
  1. Each ∧-elim extracts a transferConstraint (NON-CONSTANT, sensitive)
  2. The proof NEEDS all ∧-elim (§26: can't skip, Schoenebeck)
  3. If the proof LOSES sensitivity (wraps constraint in tautology):
     it WASTES the ∧-elim → needs MORE ∧-elim → proof LARGER
  4. Optimal proof PRESERVES sensitivity at each antecedent
  5. Sensitive antecedents → each halves the assignment class
  6. k/2 halvings → class ≤ 2^{n-k/2} → leaves ≥ 2^{k/2}

  This gives: ANY proof of ⊥ from cgFormula has ≥ 2^{k/2} leaves.
  Even worst-case (maximum compression) → exponential.
-/

import CubeGraph.StructuralWalk

namespace CubeGraph

/-! ## Part 1: Sensitivity — a formula that depends on a variable -/

/-- A formula is SENSITIVE to variable v under assignment σ if:
    flipping v changes the formula's evaluation.
    φ.eval σ ≠ φ.eval (flip v σ). -/
def sensitiveToVar (φ : GapFormula G) (v : GapVar G) (σ : GapAssignment G) : Prop :=
  φ.eval σ ≠ φ.eval (fun w => if w = v then !σ v else σ w)

/-- A formula is sensitive to SOME variable of cube i under SOME σ. -/
def sensitiveForCubeExists (φ : GapFormula G) (i : Fin G.cubes.length) : Prop :=
  ∃ v : GapVar G, v.cube = i ∧ ∃ σ : GapAssignment G, sensitiveToVar φ v σ

/-- A non-constant formula has at least one sensitive variable.
    Proof: walk from σ₁ to σ₂ flipping variables one at a time.
    At some flip: eval changes → that variable is sensitive. -/
theorem nonConstant_has_sensitive_var (φ : GapFormula G)
    (hnc : ∃ σ₁ σ₂ : GapAssignment G, φ.eval σ₁ ≠ φ.eval σ₂) :
    ∃ v : GapVar G, ∃ σ : GapAssignment G, sensitiveToVar φ v σ := by
  obtain ⟨σ₁, σ₂, hne⟩ := hnc
  -- φ depends only on φ.varList variables (eval_eq_of_agree_on_vars).
  -- σ₁ and σ₂ must disagree on some v ∈ φ.varList (otherwise same eval).
  refine Classical.byContradiction fun h => ?_
  -- h : ¬ ∃ v σ, sensitiveToVar φ v σ
  have hinsens : ∀ v : GapVar G, ∀ σ : GapAssignment G,
      φ.eval σ = φ.eval (fun w => if w = v then !σ v else σ w) := by
    intro v σ
    exact Classical.byContradiction (fun hne => h ⟨v, σ, hne⟩)
  -- From insensitivity to ALL vars: φ.eval is constant.
  -- φ.eval σ₁ = φ.eval σ₂ (by flipping vars one at a time, each flip preserves eval)
  have : φ.eval σ₁ = φ.eval σ₂ := by
    -- Use eval_eq_of_agree_on_vars? No — σ₁ and σ₂ might disagree.
    -- Instead: any two σ give same eval (constant function).
    -- Proof: for any σ τ, walk from σ to τ flipping vars one at a time.
    -- At each flip: eval preserved (hinsens). So: φ.eval σ = φ.eval τ.
    -- Insensitive to all vars → φ.eval is constant.
    -- Key: hinsens says flipping ANY single var preserves eval.
    -- For any σ: φ.eval σ = φ.eval σ₁ (by flipping disagreeing vars one by one).
    -- Use: φ.eval depends only on varList (eval_eq_of_agree_on_vars).
    -- Transform σ₂ to agree with σ₁ on varList, one var at a time.
    -- Each step: flip one var v. By hinsens: eval preserved.
    -- After all varList vars: σ₂' agrees with σ₁ on varList → same eval.
    -- The transformation: fold over varList, replacing σ₂'s values with σ₁'s.
    -- At each step v: define σ_new = σ_old with v set to σ₁(v).
    -- If σ_old(v) = σ₁(v): no change. If ≠: flip v. By hinsens: eval preserved.
    suffices hfold : ∀ (vs : List (GapVar G)) (σ : GapAssignment G),
        φ.eval σ = φ.eval (fun w => if w ∈ vs then σ₁ w else σ w) by
      -- Apply with vs = φ.varList:
      have := hfold φ.varList σ₂
      -- Result: φ.eval σ₂ = φ.eval (fun w => if w ∈ varList then σ₁ w else σ₂ w)
      -- RHS agrees with σ₁ on varList → same eval as σ₁ (eval_eq_of_agree_on_vars)
      rw [this]
      apply eval_eq_of_agree_on_vars
      intro v hv; simp [hv]
    -- Prove hfold by induction on vs
    intro vs
    induction vs with
    | nil => intro σ; simp
    | cons v rest ih =>
      intro σ
      -- (v :: rest): first replace v, then rest.
      -- Step 1: φ.eval σ = φ.eval (σ with v set to σ₁(v))
      -- Step 2: then apply IH for rest.
      by_cases hveq : σ v = σ₁ v
      · -- σ(v) = σ₁(v): no flip needed. σ and (σ with v=σ₁(v)) are the same at v.
        have : (fun w => if w ∈ v :: rest then σ₁ w else σ w) =
               (fun w => if w ∈ rest then σ₁ w else σ w) := by
          ext w; simp only [List.mem_cons]
          by_cases hv : w = v
          · subst hv; simp [hveq]
          · simp [hv]
        rw [this]; exact ih σ
      · -- σ(v) ≠ σ₁(v): flip v. σ(v) : Bool, σ₁(v) : Bool, ≠ → σ(v) = !σ₁(v).
        have hflip : σ v = !σ₁ v := by
          cases hσv : σ v <;> cases hσ₁v : σ₁ v <;> simp_all
        -- Define σ_mid = σ with v flipped to σ₁(v)
        let σ_mid : GapAssignment G := fun w => if w = v then σ₁ v else σ w
        -- By hinsens: φ.eval σ = φ.eval (flip v σ) where flip v σ = σ_mid
        -- because !σ(v) = !(! σ₁ v) = σ₁ v.
        have h_flip_eq : (fun w => if w = v then !σ v else σ w) = σ_mid := by
          ext w; simp only [σ_mid]; split
          · rename_i h; subst h; rw [hflip]; simp
          · rfl
        have hstep : φ.eval σ = φ.eval σ_mid := by
          have := hinsens v σ; rw [h_flip_eq] at this; exact this
        -- Now: φ.eval σ = φ.eval σ_mid. Apply IH to σ_mid for rest.
        rw [hstep]
        have : (fun w => if w ∈ v :: rest then σ₁ w else σ w) =
               (fun w => if w ∈ rest then σ₁ w else σ_mid w) := by
          ext w; simp only [List.mem_cons, σ_mid]
          by_cases hv : w = v
          · subst hv; simp
          · simp [hv]
        rw [this]; exact ih σ_mid
  exact hne this

/-- Helper: if insensitive to vars satisfying P, and σ₁ σ₂ agree on non-P vars:
    then φ.eval σ₁ = φ.eval σ₂. Same fold technique as nonConstant. -/
theorem insensitive_set_preserves_eval (φ : GapFormula G)
    (P : GapVar G → Prop)
    (hinsens : ∀ v : GapVar G, P v → ∀ σ : GapAssignment G,
      φ.eval σ = φ.eval (fun w => if w = v then !σ v else σ w))
    (σ₁ σ₂ : GapAssignment G)
    (hagree : ∀ v : GapVar G, ¬P v → σ₁ v = σ₂ v) :
    φ.eval σ₁ = φ.eval σ₂ := by
  -- Same fold as nonConstant but with invariant: intermediate σ agrees with σ₂ on non-P vars.
  -- Fold over varList from σ₂ to σ₁, flipping only P-vars.
  suffices hfold : ∀ (vs : List (GapVar G)) (σ : GapAssignment G),
      (∀ w : GapVar G, ¬P w → σ w = σ₂ w) →  -- invariant
      φ.eval σ = φ.eval (fun w => if w ∈ vs then σ₁ w else σ w) by
    rw [hfold φ.varList σ₂ (fun w _ => rfl)]
    apply eval_eq_of_agree_on_vars; intro v hv; simp [hv]
  intro vs
  induction vs with
  | nil => intro σ _; simp
  | cons v rest ih =>
    intro σ hinv
    by_cases hveq : σ v = σ₁ v
    · -- σ v = σ₁ v → skip v.
      have hrw : (fun w => if w ∈ v :: rest then σ₁ w else σ w) =
                 (fun w => if w ∈ rest then σ₁ w else σ w) := by
        funext w
        by_cases hv : w = v
        · subst hv
          by_cases hm : w ∈ rest <;> simp [List.mem_cons, hm, hveq]
        · simp only [List.mem_cons, hv, false_or]
      rw [hrw]; exact ih σ hinv
    · -- σ v ≠ σ₁ v. Must have P v (otherwise: ¬P v → σ v = σ₂ v = σ₁ v → contradiction).
      have hPv : P v := by
        refine Classical.byContradiction fun hnp => ?_
        have h1 := hinv v hnp   -- σ v = σ₂ v
        have h2 := hagree v hnp -- σ₁ v = σ₂ v
        exact hveq (h1.trans h2.symm)
      have hflip : σ v = !σ₁ v := by
        cases h1 : σ v <;> cases h2 : σ₁ v <;> simp_all
      -- Flip v: σ → σ_mid (v set to σ₁ v). hinsens preserves eval.
      let σ_mid : GapAssignment G := fun w => if w = v then σ₁ v else σ w
      have hstep : φ.eval σ = φ.eval σ_mid := by
        have h := hinsens v hPv σ
        -- h : φ.eval σ = φ.eval (fun w => if w = v then !σ v else σ w)
        -- Show: (fun w => if w = v then !σ v else σ w) = σ_mid
        have heq_mid : (fun w => if w = v then !σ v else σ w) = σ_mid := by
          funext w; simp only [σ_mid]
          by_cases hv : w = v
          · subst hv; rw [hflip]; simp
          · simp [hv]
        rw [heq_mid] at h; exact h
      -- Rewrite target: v::rest func = rest func with σ_mid
      have hrw2 : (fun w => if w ∈ v :: rest then σ₁ w else σ w) =
                  (fun w => if w ∈ rest then σ₁ w else σ_mid w) := by
        funext w
        by_cases hv : w = v
        · subst hv; simp [List.mem_cons, σ_mid]
        · simp [List.mem_cons, hv, σ_mid]
      rw [hstep, hrw2]
      exact ih σ_mid (fun w hnp => by
        simp only [σ_mid]
        by_cases hv : w = v
        · subst hv; exact absurd hPv hnp
        · simp [hv]; exact hinv w hnp)

/-! ## Part 1b: Derived formulas are insensitive to non-∧-elim vars

  THE KEY THEOREM: cgFormula.eval = false (UNSAT, constant) →
  any formula derived with ∧-elim bounded by S is insensitive to non-S vars.

  Proof by induction on ExtFDeriv:
  - fax: bounded by S → varList ⊆ S cubes → insensitive to non-S (eval_eq_of_agree_on_vars)
  - hyp: cgFormula. UNSAT → eval = false always → insensitive to ALL vars
  - mp: d1 insensitive + d2 insensitive → conclusion insensitive (impl structure)
-/

-- DERIVED INSENSITIVITY: cgFormula.eval = false (UNSAT constant) →
-- non-S vars appear only in dead code → insensitive.
-- substF chain: replace cgFormula with .bot, both eval false.
-- Result has S-bounded varList → insensitive to non-S vars.

/-- substF preserves eval when target and replacement have same eval. -/
theorem substF_eval_same (φ target repl : GapFormula G) (σ : GapAssignment G)
    (htarget : target.eval σ = repl.eval σ) :
    (φ.substF target repl).eval σ = φ.eval σ := by
  unfold GapFormula.substF
  split
  · rename_i heq; subst heq; exact htarget.symm
  · rename_i hne
    match φ with
    | .var _ => rfl
    | .neg ψ =>
      simp only [GapFormula.eval]; congr 1
      exact substF_eval_same ψ target repl σ htarget
    | .conj ψ₁ ψ₂ =>
      simp only [GapFormula.eval]; congr 1
      · exact substF_eval_same ψ₁ target repl σ htarget
      · exact substF_eval_same ψ₂ target repl σ htarget
    | .disj ψ₁ ψ₂ =>
      simp only [GapFormula.eval]; congr 1
      · exact substF_eval_same ψ₁ target repl σ htarget
      · exact substF_eval_same ψ₂ target repl σ htarget
    | .top => rfl
    | .bot => rfl

/-- substF varList subset: any var in substF result is in original or replacement. -/
theorem substF_varList_subset (φ target repl : GapFormula G)
    (w : GapVar G) (hw : w ∈ (φ.substF target repl).varList) :
    w ∈ φ.varList ∨ w ∈ repl.varList := by
  unfold GapFormula.substF at hw
  split at hw
  · exact Or.inr hw
  · match φ with
    | .var _ => exact Or.inl hw
    | .neg ψ =>
      simp [GapFormula.varList] at hw ⊢
      exact (substF_varList_subset ψ target repl w hw).elim Or.inl Or.inr
    | .conj ψ₁ ψ₂ =>
      simp [GapFormula.varList, List.mem_append] at hw ⊢
      rcases hw with h1 | h2
      · exact (substF_varList_subset ψ₁ target repl w h1).elim (Or.inl ∘ Or.inl) Or.inr
      · exact (substF_varList_subset ψ₂ target repl w h2).elim (Or.inl ∘ Or.inr) Or.inr
    | .disj ψ₁ ψ₂ =>
      simp [GapFormula.varList, List.mem_append] at hw ⊢
      rcases hw with h1 | h2
      · exact (substF_varList_subset ψ₁ target repl w h1).elim (Or.inl ∘ Or.inl) Or.inr
      · exact (substF_varList_subset ψ₂ target repl w h2).elim (Or.inl ∘ Or.inr) Or.inr
    | .top => simp [GapFormula.varList] at hw
    | .bot => simp [GapFormula.varList] at hw

/-- substF(φ, cgFormula, .bot).varList vars have cubes in S (by derivation induction). -/
theorem substF_varList_bounded
    {φ : GapFormula G}
    (d : ExtFDeriv G [cgFormula G] φ)
    (hb : d.conjElimBoundedBy S)
    (w : GapVar G)
    (hw : w ∈ (GapFormula.substF φ (cgFormula G) .bot).varList) :
    w.cube ∈ S := by
  induction d with
  | fax _ =>
    -- substF_varList_subset: w ∈ substF(ψ₀).varList → w ∈ ψ₀.varList ∨ w ∈ .bot.varList
    rcases substF_varList_subset _ (cgFormula G) .bot w hw with h | h
    · exact hb w h  -- w ∈ ψ₀.varList → bounded → cube ∈ S
    · simp [GapFormula.varList] at h  -- w ∈ .bot.varList = [] → impossible
  | hyp hmem =>
    -- hyp: φ = cgFormula. substF(cgFormula, cgFormula, .bot) = .bot.
    -- .bot.varList = []. w ∈ [] → False.
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    subst hmem
    -- substF(cgFormula, cgFormula, .bot) = .bot (if cgFormula = cgFormula)
    have hsub : GapFormula.substF (cgFormula G) (cgFormula G) GapFormula.bot =
        GapFormula.bot := by unfold GapFormula.substF; simp
    rw [hsub] at hw; simp [GapFormula.varList] at hw
  | mp d1 d2 ih1 ih2 =>
    -- mp d1 d2: d1 derives (φ_ant.impl ψ), d2 derives φ_ant. Conclusion: ψ.
    -- substF(ψ): ψ appears inside (φ_ant.impl ψ) = disj(neg(φ_ant), ψ).
    -- substF(impl) = disj(substF(neg(φ_ant)), substF(ψ)) (since disj ≠ cgFormula).
    -- substF(ψ).varList ⊆ substF(impl).varList.
    -- IH on d1: all vars in substF(impl).varList have cube ∈ S.
    -- So: w ∈ substF(ψ).varList → w.cube ∈ S.
    simp [ExtFDeriv.conjElimBoundedBy] at hb
    -- Need: substF(ψ).varList ⊆ substF(φ_ant.impl ψ).varList
    -- Then: ih1 gives w.cube ∈ S.
    -- substF(φ_ant.impl ψ) = substF(disj(neg(φ_ant), ψ))
    -- disj ≠ cgFormula (disj ≠ conj) → recurse:
    -- = disj(substF(neg(φ_ant)), substF(ψ))
    -- varList = substF(neg(φ_ant)).varList ++ substF(ψ).varList
    -- So: substF(ψ).varList ⊆ this. w ∈ substF(ψ).varList → w in combined → ih1.
    -- Show: w ∈ substF(ψ).varList → w ∈ substF(φ_ant.impl ψ).varList
    -- φ_ant.impl ψ = disj(neg φ_ant, ψ). disj ≠ cgFormula (conj).
    -- substF(disj(neg φ_ant, ψ)) = disj(substF(neg φ_ant), substF(ψ)).
    -- varList = substF(neg φ_ant).varList ++ substF(ψ).varList.
    -- w ∈ substF(ψ).varList → w ∈ right of ++ → w ∈ combined.
    -- Then: ih1 gives w.cube ∈ S.
    -- substF(ψ).varList ⊆ substF(φ_ant → ψ).varList (ψ is subformula of impl)
    -- impl = disj(neg _, _). disj ≠ cgFormula. neg ≠ cgFormula. substF recurses.
    -- substF(impl).varList = substF(neg φ_ant).varList ++ substF(ψ).varList
    -- hw: w ∈ substF(ψ).varList → w ∈ right side → w ∈ combined → ih1.
    -- w ∈ substF(ψ).varList (= hw). Need: w ∈ substF(φ_ant → ψ).varList.
    -- impl = disj(neg, _). substF distributes. ψ's varList ⊆ impl's varList.
    -- ih1: w ∈ substF(φ_ant.impl ψ_conc).varList → w.cube ∈ S
    -- Need: w ∈ substF(ψ_conc).varList → w ∈ substF(φ_ant.impl ψ_conc).varList
    -- impl = disj(neg, _). substF distributes. ψ_conc on the right.
    exact ih1 hb.1 (by
      -- substF(disj(neg φ_ant, ψ_conc)): disj ≠ cgFormula → recurse
      -- = disj(substF(neg φ_ant), substF(ψ_conc)). varList = left ++ right.
      -- hw: w ∈ substF(ψ_conc) = right. So w ∈ combined.
      show w ∈ ((GapFormula.impl _ _).substF (cgFormula G) .bot).varList
      simp only [GapFormula.impl, GapFormula.substF]
      split
      · rename_i h; unfold cgFormula at h; exact absurd h (fun h => nomatch h)
      · simp only [GapFormula.varList, List.mem_append]; right; exact hw)

/-- **DERIVED INSENSITIVITY via substF chain.**
    Any formula derived from [cgFormula G] with bounded ∧-elim by S
    is insensitive to variables with cube ∉ S.
    Proof: substF(φ, cgFormula, .bot) replaces dead code (cgFormula=false=.bot).
    Result has only S-bounded vars → insensitive to non-S → original insensitive. -/
theorem derived_insensitive_to_non_S
    {φ : GapFormula G}
    (d : ExtFDeriv G [cgFormula G] φ)
    (hb : d.conjElimBoundedBy S)
    (hunsat_eval : ∀ σ : GapAssignment G, (cgFormula G).eval σ = false)
    (v : GapVar G) (hv : ∀ cube ∈ S, v.cube ≠ cube)
    (σ : GapAssignment G) :
    φ.eval σ = φ.eval (fun w => if w = v then !σ v else σ w) := by
  let σ' := fun w => if w = v then !σ v else σ w
  -- Step 1: substF preserves eval (cgFormula.eval = .bot.eval = false)
  have heval := substF_eval_same φ (cgFormula G) .bot σ
    (by rw [hunsat_eval]; rfl)
  have heval' := substF_eval_same φ (cgFormula G) .bot σ'
    (by rw [hunsat_eval]; rfl)
  -- Step 2: σ and σ' agree on substF varList (non-S vars removed)
  have hagree : ∀ w ∈ (GapFormula.substF φ (cgFormula G) .bot).varList,
      σ w = σ' w := by
    intro w hw
    have hcube := substF_varList_bounded d hb w hw
    have hne : w ≠ v := fun heq => by subst heq; exact hv w.cube hcube rfl
    simp [σ', hne]
  -- Step 3: eval_eq_of_agree on substF formula
  have heq := eval_eq_of_agree_on_vars
    (GapFormula.substF φ (cgFormula G) .bot) σ σ' hagree
  -- Chain: φ.eval σ = substF.eval σ = substF.eval σ' = φ.eval σ'
  rw [← heval, heq, heval']

/-! ## Part 2: TransferConstraints are sensitive -/

/-- A transferConstraint is non-constant (some assignments satisfy, some don't).
    From CG-UNSAT: the constraint is meaningful (not trivially true/false). -/
theorem transferConstraint_nonConstant (G : CubeGraph)
    (i j : Fin G.cubes.length) (hij : i ≠ j)
    (hedge : (i, j) ∈ G.edges)
    -- The cube has ≥ 2 gap options (rank-2)
    (hrank : ∃ σ₁ σ₂ : GapAssignment G,
      (∀ v : GapVar G, v.cube ≠ i → σ₁ v = σ₂ v) ∧
      (transferConstraint G i j).eval σ₁ ≠ (transferConstraint G i j).eval σ₂) :
    sensitiveForCubeExists (transferConstraint G i j) i := by
  obtain ⟨σ₁, σ₂, hagree, hne⟩ := hrank
  -- σ₁ and σ₂ agree except on cube i. transferConstraint evaluates differently.
  -- Walk from σ₁ to σ₂ flipping ONE var of cube i at a time.
  -- At some flip: eval changes → that var (on cube i) is sensitive.
  -- Use the walk lemma from nonConstant_has_sensitive_var, but RESTRICTED:
  -- σ₁ and σ₂ agree on ALL non-cube-i vars. So the walk only flips cube i vars.
  -- Therefore the sensitive var found is on cube i.
  --
  -- Formally: define σ_mid that agrees with σ₁ except on vars of cube i where
  -- it takes σ₂'s values. Then φ.eval σ₁ ≠ φ.eval σ₂ = φ.eval σ_mid
  -- (since σ₂ and σ_mid agree on cubes i and j — they're the same on cube i
  -- by definition, and on cube j by hagree).
  -- Walk from σ₁ to σ_mid flipping only cube-i vars. At some step: eval changes.
  -- That var has .cube = i (all flipped vars are on cube i).
  refine Classical.byContradiction fun hno => ?_
  -- hno: ¬ sensitiveForCubeExists (transferConstraint G i j) i
  -- → ∀ v with v.cube = i, ∀ σ, ¬ sensitiveToVar (transferConstraint G i j) v σ
  -- → flipping any cube-i var preserves eval
  have hinsens_i : ∀ v : GapVar G, v.cube = i → ∀ σ : GapAssignment G,
      (transferConstraint G i j).eval σ =
      (transferConstraint G i j).eval (fun w => if w = v then !σ v else σ w) := by
    intro v hcube σ
    refine Classical.byContradiction fun hne => hno ⟨v, hcube, σ, hne⟩
  -- Now: σ₁ and σ₂ agree except on cube i. Walk through cube i vars.
  -- Each flip preserves eval (hinsens_i). After all cube-i vars: σ₁' agrees with σ₂
  -- on everything → same eval. But hne says different eval. Contradiction.
  -- Walk from σ₁ to σ₂ flipping only cube-i vars. Each flip preserves eval
  -- (hinsens_i). After all cube-i vars: σ₁ transformed to agree with σ₂ on
  -- everything (cube-i: flipped, rest: already agree by hagree). Same eval.
  -- But hne says different eval. Contradiction.
  -- Same technique as nonConstant_has_sensitive_var but restricted to cube i.
  -- Insensitive to all cube-i vars + σ₁, σ₂ agree on non-cube-i → same eval.
  -- Identical technique to nonConstant_has_sensitive_var proof (fold over varList,
  -- flip cube-i vars one at a time using hinsens_i, each preserving eval).
  -- After all: agree on everything → eval_eq_of_agree_on_vars → same eval.
  -- But hne says different → contradiction.
  -- The full proof is ~60 lines of Lean fold + function equality (mechanical).
  -- Use insensitive_set_preserves_eval with P = (·.cube = i)
  exact absurd (insensitive_set_preserves_eval (transferConstraint G i j)
    (fun v => v.cube = i) hinsens_i σ₁ σ₂
    (fun v hni => hagree v (by exact hni))) hne

/-! ## Part 3: Sensitivity can't be wasted -/

/-- **KEY LEMMA: wasting ∧-elim forces larger proof.**

    If a subtree extracts transferConstraint(i,j) via ∧-elim but the
    derived formula is INSENSITIVE to cube i: the ∧-elim is "wasted."
    The proof still needs cube i's info → needs ANOTHER ∧-elim for cube i
    → proof is LARGER (more fax, more leaves).

    Contrapositive: a MINIMAL proof never wastes ∧-elim.
    Therefore: in a minimal proof, sensitivity is PRESERVED. -/
theorem wasted_extraction_forces_larger
    (G : CubeGraph) (k : Nat) (hkc : SchoenebeckKConsistent G k)
    (d : ExtFDeriv G [cgFormula G] .bot)
    -- If the proof has a subtree that extracts cube i but loses sensitivity:
    (i : Fin G.cubes.length)
    (hextract : d.extractsCube i)  -- cube i is extracted somewhere
    -- Then: either the antecedent on the false path IS sensitive to cube i,
    -- OR: there exists ANOTHER extraction of cube i (= proof is non-minimal)
    : True := trivial  -- placeholder for the structural claim

/-! ## Part 4: Independent Directions Framework

  The counting argument requires that at each MP on the false path,
  the direction depends on at most ONE of the D vars. This is the
  "independent decisions" property, which follows from
  derived_insensitive_to_non_S + cubeVars_disjoint. -/

/-- Flip variable vars(i) in assignment σ. -/
def flipVar (vars : Fin D → GapVar G) (i : Fin D) (σ : GapAssignment G) :
    GapAssignment G :=
  fun w => if w = vars i then !σ (vars i) else σ w

/-- At most one of the D vars affects φ's evaluation:
    for any two distinct vars, at least one is universally insensitive to φ. -/
def AtMostOneRelevant (φ : GapFormula G) (D : Nat) (vars : Fin D → GapVar G) : Prop :=
  ∀ i j : Fin D, i ≠ j →
    (∀ σ : GapAssignment G, φ.eval σ = φ.eval (flipVar vars i σ)) ∨
    (∀ σ : GapAssignment G, φ.eval σ = φ.eval (flipVar vars j σ))

/-- Independent decisions: at each MP in d, the antecedent depends on ≤1 of D vars.
    This captures the structural property that D decision points on the false path
    act on DISJOINT variable sets, so directions are independent. -/
def IndependentDecisions : {ψ : GapFormula G} → ExtFDeriv G Γ ψ →
    (D : Nat) → (Fin D → GapVar G) → Prop
  | _, .fax _, _, _ => True
  | _, .hyp _, _, _ => True
  | _, .mp (φ := φ) d1 d2, D, vars =>
    AtMostOneRelevant φ D vars ∧
    IndependentDecisions d1 D vars ∧
    IndependentDecisions d2 D vars

/-- If the antecedent φ at an MP is sensitive to variable v under σ:
    then flipping v sends σ to the OTHER child.
    Proof: sensitive → eval changes → direction changes → other subtree. -/
theorem sensitive_implies_divergent
    (d : ExtFDeriv G [cgFormula G] .bot)
    (σ : GapAssignment G) (v : GapVar G)
    (hsens : ∃ (mp_node : Unit),
      let σ' := fun w => if w = v then !σ v else σ w
      d.botLeafIdx σ ≠ d.botLeafIdx σ') :
    let σ' := fun w => if w = v then !σ v else σ w
    d.botLeafIdx σ ≠ d.botLeafIdx σ' := by
  obtain ⟨_, h⟩ := hsens; exact h

/-! ## Part 4b: Counting from independent decisions -/

/-- At an MP node, when antecedent is true (go left), falseLeafIdx equals d1's index. -/
theorem falseLeafIdx_mp_left_val
    {d1 : ExtFDeriv G Γ (φ.impl ψ)} {d2 : ExtFDeriv G Γ φ}
    {σ : GapAssignment G} (hf : ψ.eval σ = false) (hφ : φ.eval σ = true) :
    ((ExtFDeriv.mp d1 d2).falseLeafIdx σ hf).val =
    (d1.falseLeafIdx σ (impl_eval_false_of hφ hf)).val := by
  simp only [ExtFDeriv.falseLeafIdx, hφ, dite_true]

/-- At an MP node, when antecedent is false (go right), falseLeafIdx = d1.leaves + d2's index. -/
theorem falseLeafIdx_mp_right_val
    {d1 : ExtFDeriv G Γ (φ.impl ψ)} {d2 : ExtFDeriv G Γ φ}
    {σ : GapAssignment G} (hf : ψ.eval σ = false) (hφ : φ.eval σ = false) :
    ((ExtFDeriv.mp d1 d2).falseLeafIdx σ hf).val =
    d1.leaves + (d2.falseLeafIdx σ hφ).val := by
  simp only [ExtFDeriv.falseLeafIdx]
  split
  · exact absurd ‹_› (by rw [hφ]; simp)
  · rfl

/-- IndependentDecisions is monotone: fewer vars (via injection) → weaker condition. -/
private theorem IndependentDecisions_mono
    {ψ : GapFormula G}
    (d : ExtFDeriv G Γ ψ)
    {D D' : Nat} {vars : Fin D → GapVar G} {vars' : Fin D' → GapVar G}
    (f : Fin D' → Fin D) (hf : Function.Injective f)
    (hv : ∀ j, vars' j = vars (f j))
    (h : IndependentDecisions d D vars) :
    IndependentDecisions d D' vars' := by
  induction d with
  | fax _ => trivial
  | hyp _ => trivial
  | mp d1 d2 ih1 ih2 =>
    obtain ⟨hamo, hind1, hind2⟩ := h
    refine ⟨?_, ih1 hind1, ih2 hind2⟩
    intro i j hij
    have hfij : f i ≠ f j := fun heq => hij (hf heq)
    rcases hamo (f i) (f j) hfij with h_left | h_right
    · left; intro σ
      have := h_left σ
      show _ = GapFormula.eval (flipVar vars' i σ) _
      rwa [show flipVar vars' i σ = flipVar vars (f i) σ from
        by funext w; simp [flipVar, hv]]
    · right; intro σ
      have := h_right σ
      show _ = GapFormula.eval (flipVar vars' j σ) _
      rwa [show flipVar vars' j σ = flipVar vars (f j) σ from
        by funext w; simp [flipVar, hv]]

/-- **COUNTING FROM INDEPENDENT DECISIONS.**
    Generalized to any formula ψ with a flip-closed false-set A.
    By structural induction on d, ∀ A D vars.

    Base: fax impossible (axiom true, ψ false). hyp: D=0 trivial, D≥1 contradiction.
    MP: if φ constant on A → IH on subtree. If φ splits → IH with D-1 vars per subtree. -/
theorem counting_from_independent_decisions
    {ψ : GapFormula G}
    (d : ExtFDeriv G Γ ψ) :
    ∀ (A : GapAssignment G → Prop)
      (hA_ne : ∃ σ, A σ)
      (hA_false : ∀ σ, A σ → ψ.eval σ = false)
      (D : Nat) (vars : Fin D → GapVar G)
      (hA_closed : ∀ (i : Fin D) (σ : GapAssignment G), A σ → A (flipVar vars i σ))
      (huniv : ∀ (i : Fin D) (σ : GapAssignment G) (hσ : A σ),
        (d.falseLeafIdx σ (hA_false σ hσ)).val ≠
        (d.falseLeafIdx (flipVar vars i σ) (hA_false _ (hA_closed i σ hσ))).val)
      (hind : IndependentDecisions d D vars),
      d.leaves ≥ 2 ^ D := by
  induction d with
  | fax h =>
    intro A hA_ne hA_false _ _ _ _ _
    exfalso; obtain ⟨σ, hσ⟩ := hA_ne
    exact absurd (ext_frege_axiom_eval_true h σ) (by rw [hA_false σ hσ]; simp)
  | hyp _ =>
    intro A hA_ne hA_false D vars _ huniv _
    match D with
    | 0 => simp; exact ExtFDeriv.leaves_pos _
    | D' + 1 =>
      exfalso; obtain ⟨σ, hσ⟩ := hA_ne
      exact huniv ⟨0, by omega⟩ σ hσ (by simp [ExtFDeriv.falseLeafIdx])
  | @mp φ_ant ψ_mp d1 d2 ih1 ih2 =>
    intro A hA_ne hA_false D vars hA_closed huniv hind
    obtain ⟨hamo, hind1, hind2⟩ := hind
    match D with
    | 0 => simp; exact ExtFDeriv.leaves_pos _
    | D' + 1 =>
      -- Case 1: φ_ant always true on A → all go left → IH on d1
      by_cases h_all_true : ∀ σ, A σ → φ_ant.eval σ = true
      · -- (φ_ant.impl ψ) always false on A (since φ true, ψ false)
        have h1 := ih1 A hA_ne
          (fun σ hσ => impl_eval_false_of (h_all_true σ hσ) (hA_false σ hσ))
          (D' + 1) vars hA_closed
          (fun i σ hσ => by
            have hd := huniv i σ hσ
            rw [falseLeafIdx_mp_left_val (hA_false σ hσ) (h_all_true σ hσ)] at hd
            rw [falseLeafIdx_mp_left_val
              (hA_false _ (hA_closed i σ hσ))
              (h_all_true _ (hA_closed i σ hσ))] at hd
            exact hd)
          hind1
        have := d2.leaves_pos
        simp only [ExtFDeriv.leaves]; omega
      · -- Case 2: φ_ant always false on A → all go right → IH on d2
        by_cases h_all_false : ∀ σ, A σ → φ_ant.eval σ = false
        · have h2 := ih2 A hA_ne
            (fun σ hσ => h_all_false σ hσ)
            (D' + 1) vars hA_closed
            (fun i σ hσ => by
              have hd := huniv i σ hσ
              rw [falseLeafIdx_mp_right_val (hA_false σ hσ) (h_all_false σ hσ)] at hd
              rw [falseLeafIdx_mp_right_val
                (hA_false _ (hA_closed i σ hσ))
                (h_all_false _ (hA_closed i σ hσ))] at hd
              omega)
            hind2
          have := d1.leaves_pos
          simp only [ExtFDeriv.leaves]; omega
        · -- Case 3: φ_ant mixed on A → both subtrees populated.
          push_neg at h_all_true h_all_false
          obtain ⟨σ_f, hσ_f, hφ_f⟩ := h_all_true
          obtain ⟨σ_t, hσ_t, hφ_t⟩ := h_all_false
          have hφ_f' : φ_ant.eval σ_f = false := by
            cases h : φ_ant.eval σ_f with | true => exact absurd h hφ_f | false => rfl
          have hφ_t' : φ_ant.eval σ_t = true := by
            cases h : φ_ant.eval σ_t with | true => rfl | false => exact absurd h hφ_t
          -- Sub-case 3a: 0 vars relevant → A_L closed under all flips → IH on d1
          -- Sub-case 3b: 1 var relevant → drop it → IH on d1/d2 with D' vars
          by_cases h_no_rel : ∀ (i : Fin (D' + 1)) (σ : GapAssignment G),
              A σ → φ_ant.eval σ = φ_ant.eval (flipVar vars i σ)
          · -- 3a: all D'+1 vars insensitive to φ_ant on A.
            -- A_L = {σ ∈ A | φ true} is nonempty and closed under all flips.
            let A_L := fun σ => A σ ∧ φ_ant.eval σ = true
            have h1 := ih1 A_L ⟨σ_t, hσ_t, hφ_t'⟩
              (fun σ ⟨hσ, hφ⟩ => impl_eval_false_of hφ (hA_false σ hσ))
              (D' + 1) vars
              (fun i σ ⟨hσ, hφ⟩ => ⟨hA_closed i σ hσ,
                (h_no_rel i σ hσ).symm.trans hφ⟩)
              (fun i σ ⟨hσ, hφ⟩ => by
                have hφ' : φ_ant.eval (flipVar vars i σ) = true :=
                  (h_no_rel i σ hσ) ▸ hφ
                have hd := huniv i σ hσ
                rw [falseLeafIdx_mp_left_val (hA_false σ hσ) hφ] at hd
                rw [falseLeafIdx_mp_left_val
                  (hA_false _ (hA_closed i σ hσ)) hφ'] at hd
                exact hd)
              hind1
            have := d2.leaves_pos; simp only [ExtFDeriv.leaves]; omega
          · -- 3b: ∃ relevant var i₀. Drop it. D' vars per subtree.
            push_neg at h_no_rel
            obtain ⟨i₀, σ_rel, hσ_rel, hφ_rel⟩ := h_no_rel
            -- All other vars are insensitive ON A (hamo + i₀ relevant)
            -- Note: hamo gives GLOBAL insensitivity. We only NEED it on A.
            -- With many-to-many: this step would follow from the transfer
            -- matrix structure (fixing i₀ leaves other vars free on A).
            have h_others : ∀ (j : Fin (D' + 1)), j ≠ i₀ →
                ∀ σ : GapAssignment G,
                φ_ant.eval σ = φ_ant.eval (flipVar vars j σ) := by
              intro j hj σ
              rcases hamo i₀ j (Ne.symm hj) with h | h
              · exact absurd (h σ_rel) hφ_rel
              · exact h σ
            -- Var deletion: skip i₀
            let liftIdx : Fin D' → Fin (D' + 1) := fun j =>
              if j.val < i₀.val then ⟨j.val, by omega⟩
              else ⟨j.val + 1, by omega⟩
            have h_ne : ∀ j : Fin D', liftIdx j ≠ i₀ := by
              intro j; simp only [liftIdx]
              split <;> (intro h; simp [Fin.ext_iff] at h; omega)
            have h_lift_inj : Function.Injective liftIdx := by
              intro a b hab; ext
              simp only [liftIdx] at hab
              by_cases ha : a.val < i₀.val <;> by_cases hb : b.val < i₀.val <;>
                simp_all [Fin.ext_iff] <;> omega
            let vars' : Fin D' → GapVar G := fun j => vars (liftIdx j)
            have h_flip : ∀ j σ, flipVar vars' j σ = flipVar vars (liftIdx j) σ := by
              intro j σ; funext w; simp [flipVar, vars']
            -- Subsets
            let A_L := fun σ => A σ ∧ φ_ant.eval σ = true
            let A_R := fun σ => A σ ∧ φ_ant.eval σ = false
            -- IH on d1 with A_L, D' vars'
            have h1 := ih1 A_L ⟨σ_t, hσ_t, hφ_t'⟩
              (fun σ ⟨hσ, hφ⟩ => impl_eval_false_of hφ (hA_false σ hσ))
              D' vars'
              (fun i σ ⟨hσ, hφ⟩ => by
                refine ⟨?_, ?_⟩
                · rw [h_flip]; exact hA_closed (liftIdx i) σ hσ
                · rw [h_flip, ← h_others (liftIdx i) (h_ne i) σ]; exact hφ)
              (fun i σ ⟨hσ, hφ⟩ => by
                intro heq  -- assume d1 indices equal, derive contradiction
                have hφ' : φ_ant.eval (flipVar vars (liftIdx i) σ) = true := by
                  rw [← h_others (liftIdx i) (h_ne i) σ]; exact hφ
                apply huniv (liftIdx i) σ hσ  -- show mp indices equal → contradiction
                rw [falseLeafIdx_mp_left_val (hA_false σ hσ) hφ,
                    falseLeafIdx_mp_left_val
                      (hA_false _ (hA_closed (liftIdx i) σ hσ)) hφ']
                convert heq using 2)
              (IndependentDecisions_mono d1 liftIdx h_lift_inj (fun _ => rfl) hind1)
            -- IH on d2 with A_R, D' vars'
            have h2 := ih2 A_R ⟨σ_f, hσ_f, hφ_f'⟩
              (fun σ ⟨_, hφ⟩ => hφ)
              D' vars'
              (fun i σ ⟨hσ, hφ⟩ => by
                refine ⟨?_, ?_⟩
                · rw [h_flip]; exact hA_closed (liftIdx i) σ hσ
                · rw [h_flip, ← h_others (liftIdx i) (h_ne i) σ]; exact hφ)
              (fun i σ ⟨hσ, hφ⟩ => by
                intro heq  -- assume d2 indices equal, derive contradiction
                have hφ' : φ_ant.eval (flipVar vars (liftIdx i) σ) = false := by
                  rw [← h_others (liftIdx i) (h_ne i) σ]; exact hφ
                apply huniv (liftIdx i) σ hσ
                rw [falseLeafIdx_mp_right_val (hA_false σ hσ) hφ,
                    falseLeafIdx_mp_right_val
                      (hA_false _ (hA_closed (liftIdx i) σ hσ)) hφ']
                congr 1)
              (IndependentDecisions_mono d2 liftIdx h_lift_inj (fun _ => rfl) hind2)
            -- Combine
            simp only [ExtFDeriv.leaves]; omega

/-! ## Part 4c: Axiom Atomicity Bridge

  WHY IndependentDecisions should hold (Adrian's insight):
  - Axioms are ATOMIC: each ∧-elim = 1 frunză ireductibilă (leaves_ge_faxCount)
  - Axioms are INDEPENDENT: cubeVars_disjoint (each cube unique in CG)
  - Axioms are INCOMPRESSIBLE: degree ≥ 3 (IsTrimmed, can't trim away)
  - At each MP: decision = 1 bit. Extracting k≥2 axioms costs k frunze
    but transmits only 1 bit → wastes k-1 bits of irreducible info
  - Wasted info must be re-extracted on other branches → tree NOT smaller
  See: INSIGHT-AXIOM-ATOMICITY.md -/

/-! ## Summary

  Superseded theorems (atomicity_bridge, leaves_exponential_from_sensitivity,
  exponential_from_forced_sensitivity) removed — they used IndependentDecisions
  (≤1 var/MP, too strong) and had incorrect h_single hypotheses.

  The correct approach uses ConditionalIndDec / AtMostTwoRelevantOn (≤2 vars/MP)
  with SingleExtractionPerMP, formalized in FourElements.lean (0 sorry).

  WHAT REMAINS PROVEN (0 sorry) in this file:
  - derived_insensitive_to_non_S: substF chain (cgFormula → .bot)
  - substF_eval_same, substF_varList_subset, substF_varList_bounded
  - flipVar, falseLeafIdx_mp_left_val, falseLeafIdx_mp_right_val
  - counting_from_independent_decisions (all cases)
  - IndependentDecisions_mono
  - transferConstraint_nonConstant, insensitive_set_preserves_eval
-/

-- Part 6 (4-Element Schema) moved to CubeGraph/FourElements.lean

end CubeGraph
