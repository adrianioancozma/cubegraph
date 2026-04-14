/-
  CubeGraph/BridgeAxiom.lean — Bridge Axiom (PROVEN, 0 sorry)

  Session: 050+.
  Docs: experiments-ml/050_*/HANDOFF.md, experiments-ml/044_*/DISCOVERIES.md

  Proves: reinterpret_bounded_conjElim (was axiom in ExponentialBound.lean).
  conjElimBoundedBy S → ExtFregeDerivable G [cgFormulaRestricted G S] .bot.

  STRATEGY: substF(cgFormula → cgFormulaRestricted) + bounded condition ensures
  conjElimL/R never operates on cgFormula itself (vars outside S → not bounded).
  Key lemmas: foldl_conj_extractable, transfer_in_restricted, atLeast_in_restricted.
-/

import CubeGraph.ExponentialBound

namespace CubeGraph

/-! ## Part 1: Conjunction Extraction from foldl -/

/-- Extract a sub-formula from a conjunction by following L/R choices. -/
def extractByChain : GapFormula G → List Bool → Option (GapFormula G)
  | φ, [] => some φ
  | .conj l _, true :: rest => extractByChain l rest
  | .conj _ r, false :: rest => extractByChain r rest
  | _, _ :: _ => none

/-- If extractByChain succeeds, the result is derivable via ∧-elim + MP. -/
theorem derivable_from_extraction (G : CubeGraph)
    (Γ : List (GapFormula G))
    (φ C : GapFormula G)
    (chain : List Bool)
    (hext : extractByChain φ chain = some C)
    (hφ : ExtFregeDerivable G Γ φ) :
    ExtFregeDerivable G Γ C := by
  induction chain generalizing φ with
  | nil =>
    simp [extractByChain] at hext
    exact hext ▸ hφ
  | cons b rest ih =>
    cases φ with
    | conj l r =>
      cases b with
      | true =>
        simp [extractByChain] at hext
        exact ih l hext (.mp (.fax .conjElimL) hφ)
      | false =>
        simp [extractByChain] at hext
        exact ih r hext (.mp (.fax .conjElimR) hφ)
    | var _ => simp [extractByChain] at hext
    | neg _ => simp [extractByChain] at hext
    | disj _ _ => simp [extractByChain] at hext
    | top => simp [extractByChain] at hext
    | bot => simp [extractByChain] at hext

/-- The init is extractable from a foldl-conj chain via repeated conjElimL. -/
theorem foldl_init_extractable {α : Type} (G : CubeGraph)
    (Γ : List (GapFormula G))
    (g : α → GapFormula G)
    (init : GapFormula G) (ls : List α)
    (hfoldl : ExtFregeDerivable G Γ
      (ls.foldl (fun acc x => .conj acc (g x)) init)) :
    ExtFregeDerivable G Γ init := by
  induction ls generalizing init with
  | nil => exact hfoldl
  | cons x rest ih =>
    exact .mp (.fax .conjElimL) (ih (init := .conj init (g x)) hfoldl)

/-- If a ∈ ls, then g(a) is extractable from the foldl result via ∧-elim. -/
theorem foldl_conj_extractable {α : Type} (G : CubeGraph)
    (Γ : List (GapFormula G))
    (g : α → GapFormula G)
    (init : GapFormula G) (ls : List α) (a : α)
    (ha : a ∈ ls)
    (hfoldl : ExtFregeDerivable G Γ
      (ls.foldl (fun acc x => .conj acc (g x)) init)) :
    ExtFregeDerivable G Γ (g a) := by
  induction ls generalizing init with
  | nil => simp at ha
  | cons x rest ih =>
    rcases List.mem_cons.mp ha with rfl | hmem
    · exact .mp (.fax .conjElimR)
        (foldl_init_extractable G Γ g (.conj init (g a)) rest hfoldl)
    · exact ih hmem (init := .conj init (g x)) hfoldl

/-! ## Part 2: Conjuncts of cgFormulaRestricted are extractable -/

/-- transferConstraint G i j (with i, j ∈ S, edge in G) is derivable from cgFormulaRestricted. -/
theorem transfer_in_restricted (G : CubeGraph) (S : List (Fin G.cubes.length))
    (i j : Fin G.cubes.length) (hi : i ∈ S) (hj : j ∈ S)
    (hedge : (i, j) ∈ G.edges) :
    ExtFregeDerivable G [cgFormulaRestricted G S] (transferConstraint G i j) := by
  have hcgr := ExtFregeDerivable.hyp (show cgFormulaRestricted G S ∈ [cgFormulaRestricted G S] by simp)
  have htransfers : ExtFregeDerivable G [cgFormulaRestricted G S]
      ((G.edges.filter (fun e => decide (e.1 ∈ S) && decide (e.2 ∈ S))).foldl
        (fun acc e => .conj acc (.conj (transferConstraint G e.1 e.2)
                                       (transferConstraint G e.2 e.1))) .top) :=
    .mp (.fax .conjElimL) hcgr
  have hfilt : (i, j) ∈ G.edges.filter (fun e => decide (e.1 ∈ S) && decide (e.2 ∈ S)) := by
    simp [List.mem_filter, hi, hj, hedge]
  have hpair := foldl_conj_extractable G [cgFormulaRestricted G S]
    (fun e => .conj (transferConstraint G e.1 e.2) (transferConstraint G e.2 e.1))
    .top _ (i, j) hfilt htransfers
  exact .mp (.fax .conjElimL) hpair

/-- atLeastOneGap G i (with i ∈ S) is derivable from cgFormulaRestricted. -/
theorem atLeast_in_restricted (G : CubeGraph) (S : List (Fin G.cubes.length))
    (i : Fin G.cubes.length) (hi : i ∈ S) :
    ExtFregeDerivable G [cgFormulaRestricted G S] (atLeastOneGap G i) := by
  have hcgr := ExtFregeDerivable.hyp (show cgFormulaRestricted G S ∈ [cgFormulaRestricted G S] by simp)
  have hatLeast : ExtFregeDerivable G [cgFormulaRestricted G S]
      (S.foldl (fun acc i => .conj acc (atLeastOneGap G i)) .top) :=
    .mp (.fax .conjElimR) hcgr
  exact foldl_conj_extractable G [cgFormulaRestricted G S]
    (fun i => atLeastOneGap G i) .top S i hi hatLeast

/-! ## Part 3: ExtFregeAxiom preservation under substF

  substF replaces cgFormula (as a WHOLE) with cgFormulaRestricted.
  For K/S/Contra: FregeAxiom.substPreserve (already proven).
  For conjElimL/R: need special handling when A∧B = cgFormula. -/

-- NOTE: substF_conjElimL/R_is_axiom (generic, for ALL A B) is FALSE
-- when A∧B = cgFormula. The bridge_axiom_proof below handles this by
-- showing A∧B = cgFormula is IMPOSSIBLE under conjElimBoundedBy S
-- (because cgFormula mentions cubes outside S → formula not bounded).

/-! ## Part 4: The Bridge Axiom -/

/-- **GENERALIZED BRIDGE AXIOM.**

    For ANY formula φ (not just ⊥): if d derives φ from [cgFormula G]
    with conjElimBoundedBy S, then substF(φ) is derivable from
    [cgFormulaRestricted G S].

    This captures: the INFORMATION in φ is bounded by the ∧-elim cubes
    in d's subtree. ∧-elim bounded by S → φ's info ⊆ S.

    Key consequence: the antecedent at each MP has information bounded
    by its subtree's ∧-elim cubes. Since each ∧-elim adds ≤ 2 cubes:
    information per subtree ≤ 2 × faxLeaves → LOCALIZATION IS AUTOMATIC. -/
theorem bridge_axiom_general (G : CubeGraph)
    (S : List (Fin G.cubes.length))
    {φ : GapFormula G}
    (d : ExtFDeriv G [cgFormula G] φ)
    (hb : d.conjElimBoundedBy S)
    (hproper : ∃ v ∈ (cgFormula G).varList, v.cube ∉ S) :
    ExtFregeDerivable G [cgFormulaRestricted G S]
      (φ.substF (cgFormula G) (cgFormulaRestricted G S)) := by
  induction d with
  | fax hax =>
    cases hax with
    | base hb' => exact .fax (.base (hb'.substPreserve S))
    | conjElimL =>
      rename_i A B
      have hconj_ne : GapFormula.conj A B ≠ cgFormula G := by
        intro heq
        obtain ⟨v, hv_mem, hv_out⟩ := hproper
        rw [← heq] at hv_mem
        simp only [GapFormula.varList] at hv_mem
        have hv_impl : v ∈ ((GapFormula.conj A B).impl A).varList := by
          simp only [GapFormula.impl, GapFormula.varList, List.mem_append]
          simp only [List.mem_append] at hv_mem
          rcases hv_mem with h | h <;> simp [h]
        exact hv_out (hb v hv_impl)
      simp only [GapFormula.impl, GapFormula.substF]
      have hne_disj : GapFormula.disj (GapFormula.neg (GapFormula.conj A B)) A ≠ cgFormula G := by
        unfold cgFormula; exact fun h => nomatch h
      have hne_neg : GapFormula.neg (GapFormula.conj A B) ≠ cgFormula G := by
        unfold cgFormula; exact fun h => nomatch h
      simp only [hne_disj, ite_false, hne_neg, GapFormula.substF, hconj_ne]
      exact .fax .conjElimL
    | conjElimR =>
      rename_i A B
      have hconj_ne : GapFormula.conj A B ≠ cgFormula G := by
        intro heq
        obtain ⟨v, hv_mem, hv_out⟩ := hproper
        rw [← heq] at hv_mem
        simp only [GapFormula.varList] at hv_mem
        have hv_impl : v ∈ ((GapFormula.conj A B).impl B).varList := by
          simp only [GapFormula.impl, GapFormula.varList, List.mem_append]
          simp only [List.mem_append] at hv_mem
          rcases hv_mem with h | h <;> simp [h]
        exact hv_out (hb v hv_impl)
      simp only [GapFormula.impl, GapFormula.substF]
      have hne_disj : GapFormula.disj (GapFormula.neg (GapFormula.conj A B)) B ≠ cgFormula G := by
        unfold cgFormula; exact fun h => nomatch h
      have hne_neg : GapFormula.neg (GapFormula.conj A B) ≠ cgFormula G := by
        unfold cgFormula; exact fun h => nomatch h
      simp only [hne_disj, ite_false, hne_neg, GapFormula.substF, hconj_ne]
      exact .fax .conjElimR
  | hyp hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem; subst hmem
    have : (cgFormula G).substF (cgFormula G) (cgFormulaRestricted G S) =
           cgFormulaRestricted G S := by
      unfold GapFormula.substF; simp
    rw [this]
    exact .hyp (show cgFormulaRestricted G S ∈ [cgFormulaRestricted G S] by simp)
  | mp _ _ ih1 ih2 =>
    rename_i φ' ψ' d1' d2'
    simp [ExtFDeriv.conjElimBoundedBy] at hb
    have hne_disj : GapFormula.disj (GapFormula.neg φ') ψ' ≠ cgFormula G := by
      unfold cgFormula; exact fun h => nomatch h
    have hne_neg : GapFormula.neg φ' ≠ cgFormula G := by
      unfold cgFormula; exact fun h => nomatch h
    have key : (GapFormula.impl φ' ψ').substF (cgFormula G) (cgFormulaRestricted G S) =
        GapFormula.impl (φ'.substF (cgFormula G) (cgFormulaRestricted G S))
                        (ψ'.substF (cgFormula G) (cgFormulaRestricted G S)) := by
      show GapFormula.substF (GapFormula.disj (GapFormula.neg φ') ψ')
        (cgFormula G) (cgFormulaRestricted G S) =
        GapFormula.disj (GapFormula.neg (φ'.substF (cgFormula G) (cgFormulaRestricted G S)))
                        (ψ'.substF (cgFormula G) (cgFormulaRestricted G S))
      rw [GapFormula.substF]; simp [hne_disj, hne_neg, GapFormula.substF]
    rw [key] at ih1
    exact .mp (ih1 hb.1) (ih2 hb.2)

/-- **THE BRIDGE AXIOM FOR ⊥ (special case of bridge_axiom_general).** -/
theorem bridge_axiom_proof (G : CubeGraph)
    (S : List (Fin G.cubes.length))
    (d : ExtFDeriv G [cgFormula G] .bot)
    (hb : d.conjElimBoundedBy S)
    (hproper : ∃ v ∈ (cgFormula G).varList, v.cube ∉ S) :
    ExtFregeDerivable G [cgFormulaRestricted G S] .bot := by
  have hsubst := bridge_axiom_general G S d hb hproper
  have hbot_ne : (GapFormula.bot : GapFormula G) ≠ cgFormula G := by
    unfold cgFormula; exact fun h => nomatch h
  simp only [GapFormula.substF, hbot_ne, ↓reduceIte] at hsubst
  exact hsubst

end CubeGraph
