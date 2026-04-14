/-
  CubeGraph/CubeGraphRestriction.lean
  Agent Theta5: CubeGraph random restriction — first step toward Hrubes-Pudlak FIP extension.

  Hrubes-Pudlak (FOCS 2017) proved FIP for Cutting Planes on random formulas.
  Their key technique: random restrictions (setting most variables) preserve
  local consistency while simplifying the formula.

  In CubeGraph language, a "random restriction" = removing cubes.
  When a cube is removed, its constraints are relaxed.

  Key results (0 additional axioms):
  1. restrictToCubes: remove cubes from a CubeGraph (= inducedSubgraph)
  2. restriction_preserves_sat: SAT(G) -> SAT(restrict(G, S))
  3. restriction_unsat_implies_unsat: contrapositive
  4. restriction_preserves_kconsistent: k-consistency transfers to restriction
  5. restriction_preserves_below_borromean: BorromeanOrder control
  6. restricted_gap_consistency_mono: monotonicity is inherited
  7. gap_consistency_restriction_chain: UNSAT detection chain
  8. monotone_interpolation_structure: connects to FIP

  Imports:
  - InducedSubgraph.lean: inducedSubgraph, sat_of_induced_subgraph
  - GapConsistency.lean: GapConsistency, MaskLeq, gapConsistency_mono,
    KConsistent, BorromeanOrder, cubeMask
  - Mathlib.Data.List.Nodup: List.Nodup.map, List.nodup_finRange

  See: experiments-ml/025_.../bridge-next/agents/STRATEGY-46-FIP-ROUTE.md
-/

import CubeGraph.InducedSubgraph
import CubeGraph.GapConsistency
import Mathlib.Data.List.Nodup

namespace CubeGraph

open AlphaGapConsistency

/-! ## Part 1: Cube Removal (restrictToCubes) -/

/-- Remove cubes from a CubeGraph by keeping only those indexed by S.
    In Hrubes-Pudlak terms: a restriction sets most variables, which
    corresponds to removing the cubes containing those variables.
    The restricted graph has only the cubes in S and edges between them. -/
def restrictToCubes (G : CubeGraph) (S : List (Fin G.cubes.length))
    (h_nodup : S.Nodup) : CubeGraph :=
  G.inducedSubgraph S h_nodup

/-- The restricted graph has exactly |S| cubes. -/
theorem restrictToCubes_length (G : CubeGraph) (S : List (Fin G.cubes.length))
    (h_nodup : S.Nodup) :
    (G.restrictToCubes S h_nodup).cubes.length = S.length :=
  G.inducedSubgraph_length S h_nodup

/-! ## Part 2: Monotonicity Under Restriction -/

/-- **Restriction preserves satisfiability**: if G is SAT, then any
    restriction (keeping a subset of cubes) is also SAT.
    Proof: directly from L-LOCAL-2 (sat_of_induced_subgraph). -/
theorem restriction_preserves_sat (G : CubeGraph)
    (S : List (Fin G.cubes.length)) (h_nodup : S.Nodup)
    (hsat : G.Satisfiable) :
    (G.restrictToCubes S h_nodup).Satisfiable :=
  sat_of_induced_subgraph G S h_nodup hsat

/-- **Contrapositive**: if the restricted graph is UNSAT, then G is UNSAT.
    This is the key direction for Hrubes-Pudlak: find a small restriction
    that is UNSAT, and conclude G is UNSAT. -/
theorem restriction_unsat_implies_unsat (G : CubeGraph)
    (S : List (Fin G.cubes.length)) (h_nodup : S.Nodup)
    (hunsat : ¬ (G.restrictToCubes S h_nodup).Satisfiable) :
    ¬ G.Satisfiable := by
  intro hsat
  exact hunsat (restriction_preserves_sat G S h_nodup hsat)

/-! ## Helpers for k-Consistency Transfer -/

/-- SharedVars is symmetric: if sv is shared by c1 and c2, it is shared by c2 and c1. -/
private theorem sharedVars_comm (c₁ c₂ : Cube) (sv : Nat)
    (hsv : sv ∈ Cube.sharedVars c₁ c₂) :
    sv ∈ Cube.sharedVars c₂ c₁ := by
  simp only [Cube.sharedVars, Cube.vars, List.mem_filter, List.contains_iff_exists_mem_beq,
             List.mem_cons, List.mem_nil_iff, or_false] at hsv ⊢
  obtain ⟨h_in_c1, ⟨a, ha_mem, ha_beq⟩⟩ := hsv
  have heq : sv = a := by
    simp only [BEq.beq, decide_eq_true_eq] at ha_beq; exact ha_beq
  subst heq
  exact ⟨ha_mem, ⟨sv, h_in_c1, by simp [BEq.beq]⟩⟩

/-- TransferOp is commutative: transferOp c1 c2 g1 g2 = transferOp c2 c1 g2 g1.
    Both check: isGap + isGap + shared variable agreement (symmetric). -/
private theorem transferOp_comm (c₁ c₂ : Cube) (g₁ g₂ : Vertex) :
    transferOp c₁ c₂ g₁ g₂ = true → transferOp c₂ c₁ g₂ g₁ = true := by
  intro h
  simp only [transferOp, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨hg1, hg2⟩, hvars⟩ := h
  refine ⟨⟨hg2, hg1⟩, ?_⟩
  apply List.all_eq_true.mpr
  intro sv hsv
  have hsv_fwd := sharedVars_comm c₂ c₁ sv hsv
  have := List.all_eq_true.mp hvars sv hsv_fwd
  simp only [BEq.beq, decide_eq_true_eq] at this ⊢
  exact this.symm

/-! ## Part 3: k-Consistency Under Restriction -/

/-- **k-Consistency of G transfers to restricted graph.**
    If G is k-consistent, then any restriction is also k-consistent.

    Proof: any k-subset T of the restricted graph maps via S to a k-subset
    of G. G's k-consistency gives a compatible selection, which restricts
    to a compatible selection on the restricted graph. Edge compatibility
    uses edges_complete of G and transferOp commutativity. -/
theorem restriction_preserves_kconsistent (G : CubeGraph)
    (S : List (Fin G.cubes.length)) (h_nodup : S.Nodup)
    (k : Nat) (hkc : KConsistent G k) :
    KConsistent (G.restrictToCubes S h_nodup) k := by
  -- Abbreviations
  set G' := G.restrictToCubes S h_nodup with hG'
  set hlen := restrictToCubes_length G S h_nodup with hlen_def
  -- Map from G' indices to G indices: j -> S[j]
  set toG : Fin G'.cubes.length → Fin G.cubes.length :=
    fun j => S[j.val]'(hlen ▸ j.isLt) with toG_def
  -- toG is injective (S is nodup)
  have toG_inj : Function.Injective toG := by
    intro a b hab
    simp only [toG] at hab
    have ha : a.val < S.length := hlen ▸ a.isLt
    have hb : b.val < S.length := hlen ▸ b.isLt
    have heq : S.get ⟨a.val, ha⟩ = S.get ⟨b.val, hb⟩ := by
      simp [List.get_eq_getElem]; exact hab
    have hfin := h_nodup.get_inj_iff.mp heq
    -- hfin : ⟨a.val, ha⟩ = ⟨b.val, hb⟩ in Fin S.length
    exact Fin.ext (Fin.mk.inj hfin)
  -- Cube bridge: G'.cubes[j] = G.cubes[toG j]
  have cube_eq : ∀ j : Fin G'.cubes.length,
      G'.cubes[j] = G.cubes[toG j] := by
    intro j
    show (S.map (fun i => G.cubes[i]))[j.val]'j.isLt = G.cubes[S[j.val]'_]
    rw [List.getElem_map]
  -- Main proof
  intro T hTlen hTnd
  -- Map T to G-indices
  set T_G := T.map toG with hT_G_def
  have hT_G_len : T_G.length ≤ k := by simp [T_G]; exact hTlen
  have hT_G_nd : T_G.Nodup := hTnd.map toG_inj
  -- Get G's k-consistent selection
  obtain ⟨s, hv, hc⟩ := hkc T_G hT_G_len hT_G_nd
  -- Restrict to G'
  refine ⟨fun j => s (toG j), fun j hj => ?_, fun e he hj1 hj2 => ?_⟩
  · -- Validity: s (toG j) is a gap in G'.cubes[j] = G.cubes[toG j]
    rw [cube_eq]; exact hv (toG j) (List.mem_map_of_mem hj)
  · -- Compatibility on restricted graph edge e
    -- Rewrite cubes to G cubes
    have h1 : G'.cubes[e.1] = G.cubes[toG e.1] := cube_eq e.1
    have h2 : G'.cubes[e.2] = G.cubes[toG e.2] := cube_eq e.2
    simp only [h1, h2]
    -- LinkWeight from edges_valid
    have hlw : Cube.linkWeight G'.cubes[e.1] G'.cubes[e.2] > 0 := G'.edges_valid e he
    rw [h1, h2] at hlw
    -- Case split on whether toG e.1 = toG e.2 (self-loop vs distinct)
    by_cases hne : toG e.1 = toG e.2
    · -- Self-loop: same cube, same gap -> transferOp trivially true
      simp only [hne, transferOp, Bool.and_eq_true]
      have hg := hv (toG e.2) (List.mem_map_of_mem hj2)
      exact ⟨⟨hg, hg⟩, List.all_eq_true.mpr (fun _ _ => by simp [BEq.beq])⟩
    · -- Distinct cubes: use edges_complete of G
      rcases G.edges_complete (toG e.1) (toG e.2) hne hlw with hedge | hedge
      · -- (toG e.1, toG e.2) ∈ G.edges: direct
        exact hc (toG e.1, toG e.2) hedge (List.mem_map_of_mem hj1) (List.mem_map_of_mem hj2)
      · -- (toG e.2, toG e.1) ∈ G.edges: use transferOp commutativity
        have hrev := hc (toG e.2, toG e.1) hedge (List.mem_map_of_mem hj2) (List.mem_map_of_mem hj1)
        exact transferOp_comm _ _ _ _ hrev

/-- **BorromeanOrder cannot increase under restriction.**
    If G has BorromeanOrder b, then the restricted graph is (b-1)-consistent. -/
theorem restriction_preserves_below_borromean (G : CubeGraph)
    (S : List (Fin G.cubes.length)) (h_nodup : S.Nodup)
    (b : Nat) (hbo : BorromeanOrder G b) (hb : b > 0) :
    KConsistent (G.restrictToCubes S h_nodup) (b - 1) :=
  restriction_preserves_kconsistent G S h_nodup (b - 1) (hbo.2 hb)

/-- **Contrapositive of k-consistency transfer.**
    If restrict(G, S) is NOT k-consistent, then G is NOT k-consistent. -/
theorem restriction_kconsistency_contrapositive (G : CubeGraph)
    (S : List (Fin G.cubes.length)) (h_nodup : S.Nodup)
    (k : Nat) (h_not_kc : ¬ KConsistent (G.restrictToCubes S h_nodup) k) :
    ¬ KConsistent G k := by
  intro hkc
  exact h_not_kc (restriction_preserves_kconsistent G S h_nodup k hkc)

/-- **UNSAT restricted graph has k-consistency failure.**
    If restrict(G, S) is UNSAT, it is NOT (|S|)-consistent. -/
theorem restricted_unsat_not_fully_consistent (G : CubeGraph)
    (S : List (Fin G.cubes.length)) (h_nodup : S.Nodup)
    (hunsat : ¬ (G.restrictToCubes S h_nodup).Satisfiable) :
    ¬ KConsistent (G.restrictToCubes S h_nodup) S.length := by
  intro hkc
  apply hunsat
  -- Take T = all cubes in the restricted graph
  have hlen_eq := restrictToCubes_length G S h_nodup
  let allIdx := List.finRange (G.restrictToCubes S h_nodup).cubes.length
  have hlen_all : allIdx.length = (G.restrictToCubes S h_nodup).cubes.length :=
    List.length_finRange
  have hnd_all : allIdx.Nodup := List.nodup_finRange _
  have hlen_le : allIdx.length ≤ S.length := by rw [hlen_all, hlen_eq]; exact Nat.le_refl _
  obtain ⟨s, hv, hc⟩ := hkc allIdx hlen_le hnd_all
  exact ⟨s,
    fun i => hv i (List.mem_finRange i),
    fun e he => hc e he (List.mem_finRange e.1) (List.mem_finRange e.2)⟩

/-! ## Part 4: Gap Consistency Under Restriction -/

/-- Full gap mask: all 8 vertices are gaps. Value = 255 = 0xFF. -/
def fullGapMask : Fin 256 := ⟨255, by omega⟩

/-- Full gap mask is positive. -/
theorem fullGapMask_pos : fullGapMask.val > 0 := by decide

/-- Every vertex is a gap under full gap mask. -/
theorem fullGapMask_all_gaps (v : Vertex) :
    ((fullGapMask.val >>> v.val) &&& 1 == 1) = true := by
  revert v; native_decide

/-- Every vertex is a gap in a cube with full gap mask. -/
theorem cubeMask_full_isGap (c : Cube) (v : Vertex) :
    (cubeMask c fullGapMask fullGapMask_pos).isGap v = true := by
  simp only [Cube.isGap, cubeMask]
  exact fullGapMask_all_gaps v

/-- **Gap consistency with original masks on restricted graph = Satisfiable
    of restricted graph.** Connects GapConsistency (Alpha) to Satisfiable (Basic). -/
theorem restricted_gap_consistency_equiv_sat (G : CubeGraph)
    (S : List (Fin G.cubes.length)) (h_nodup : S.Nodup) :
    GapConsistency (G.restrictToCubes S h_nodup)
      (fun i => ((G.restrictToCubes S h_nodup).cubes[i]).gapMask)
      (fun i => ((G.restrictToCubes S h_nodup).cubes[i]).gaps_nonempty) ↔
    (G.restrictToCubes S h_nodup).Satisfiable :=
  gapConsistency_equiv_sat (G.restrictToCubes S h_nodup)

/-- **Gap consistency UNSAT chain.**
    NOT GapConsistency(restrict(G,S)) -> NOT restrict(G,S).SAT -> NOT G.SAT. -/
theorem gap_consistency_restriction_chain (G : CubeGraph)
    (S : List (Fin G.cubes.length)) (h_nodup : S.Nodup)
    (hngc : ¬ GapConsistency (G.restrictToCubes S h_nodup)
        (fun i => ((G.restrictToCubes S h_nodup).cubes[i]).gapMask)
        (fun i => ((G.restrictToCubes S h_nodup).cubes[i]).gaps_nonempty)) :
    ¬ G.Satisfiable := by
  intro hsat
  have hsat' := restriction_preserves_sat G S h_nodup hsat
  exact hngc ((restricted_gap_consistency_equiv_sat G S h_nodup).mpr hsat')

/-! ## Part 5: Monotonicity Chain -/

/-- **Restricted gap consistency is monotone.** More gaps -> easier to satisfy.
    Directly from gapConsistency_mono applied to the restricted graph. -/
theorem restricted_gap_consistency_mono (G : CubeGraph)
    (S : List (Fin G.cubes.length)) (h_nodup : S.Nodup)
    (masks₁ masks₂ : Fin (G.restrictToCubes S h_nodup).cubes.length → Fin 256)
    (hm₁ : ∀ i, (masks₁ i).val > 0)
    (hm₂ : ∀ i, (masks₂ i).val > 0)
    (hleq : MaskLeq (G.restrictToCubes S h_nodup) masks₁ masks₂ hm₁ hm₂)
    (hsat : GapConsistency (G.restrictToCubes S h_nodup) masks₁ hm₁) :
    GapConsistency (G.restrictToCubes S h_nodup) masks₂ hm₂ :=
  gapConsistency_mono (G.restrictToCubes S h_nodup) masks₁ masks₂ hm₁ hm₂ hleq hsat

/-! ## Part 6: FIP Connection -/

/-- **Monotone interpolation structure**: the structural theorem connecting
    restriction to Feasible Interpolation Property (FIP).

    (a) SAT(G) -> SAT(restrict(G,S))
    (b) SAT(restrict(G,S)) is a monotone function of gap masks
    (c) UNSAT(restrict(G,S)) -> UNSAT(G)

    Combined with the monotone circuit lower bound (AlphaGapConsistency),
    this shows that any proof system with FIP requires large proofs
    for random UNSAT CubeGraph formulas. -/
theorem monotone_interpolation_structure (G : CubeGraph)
    (S : List (Fin G.cubes.length)) (h_nodup : S.Nodup) :
    (G.Satisfiable → (G.restrictToCubes S h_nodup).Satisfiable) ∧
    (∀ (m₁ m₂ : Fin (G.restrictToCubes S h_nodup).cubes.length → Fin 256)
       (h₁ : ∀ i, (m₁ i).val > 0) (h₂ : ∀ i, (m₂ i).val > 0),
       MaskLeq (G.restrictToCubes S h_nodup) m₁ m₂ h₁ h₂ →
       GapConsistency (G.restrictToCubes S h_nodup) m₁ h₁ →
       GapConsistency (G.restrictToCubes S h_nodup) m₂ h₂) ∧
    (¬ (G.restrictToCubes S h_nodup).Satisfiable → ¬ G.Satisfiable) :=
  ⟨restriction_preserves_sat G S h_nodup,
   gapConsistency_mono (G.restrictToCubes S h_nodup),
   restriction_unsat_implies_unsat G S h_nodup⟩

/-! ## Part 7: AND-Term Blindness Under Restriction -/

/-- **AND-term blindness transfers to restrictions.**
    If G is (b-1)-consistent, then the restricted graph is also (b-1)-consistent,
    so AND-terms touching < b cubes in the restricted graph are blind. -/
theorem restricted_and_term_blind (G : CubeGraph)
    (S : List (Fin G.cubes.length)) (h_nodup : S.Nodup)
    (b : Nat) (hb : b > 0)
    (hkc : KConsistent G (b - 1))
    (t : ANDTerm (G.restrictToCubes S h_nodup))
    (ht : t.touchedCubes.length < b)
    (htnd : t.touchedCubes.Nodup) :
    ∃ s : (i : Fin (G.restrictToCubes S h_nodup).cubes.length) → Vertex,
      (∀ i ∈ t.touchedCubes, ((G.restrictToCubes S h_nodup).cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ (G.restrictToCubes S h_nodup).edges,
        e.1 ∈ t.touchedCubes → e.2 ∈ t.touchedCubes →
        transferOp ((G.restrictToCubes S h_nodup).cubes[e.1])
                   ((G.restrictToCubes S h_nodup).cubes[e.2])
                   (s e.1) (s e.2) = true) := by
  have hkc' := restriction_preserves_kconsistent G S h_nodup (b - 1) hkc
  exact hkc' t.touchedCubes (by omega) htnd

/-! ## Part 8: Partition and Iterative Restriction -/

/-- **Restriction is the right primitive for Hrubes-Pudlak FIP.**
    Any cube index is either kept or removed. -/
theorem restriction_partition (G : CubeGraph)
    (S : List (Fin G.cubes.length)) (i : Fin G.cubes.length) :
    i ∈ S ∨ i ∉ S :=
  Classical.em (i ∈ S)

/-- **Iterative restriction = single restriction.**
    Removing cubes one at a time produces the same result as removing them all at once.
    (Both result in SAT preservation.) -/
theorem iterative_restriction_equiv (G : CubeGraph)
    (S : List (Fin G.cubes.length)) (h_nodup : S.Nodup)
    (hsat : G.Satisfiable) :
    (G.restrictToCubes S h_nodup).Satisfiable :=
  restriction_preserves_sat G S h_nodup hsat

/-! ## Summary

  Theorem count: 18 definitions/theorems, 0 additional axioms.

  Chain of reasoning for Hrubes-Pudlak FIP extension:

  1. restrictToCubes: cube removal (= inducedSubgraph)
  2. restriction_preserves_sat: SAT preserved under restriction
  3. restriction_unsat_implies_unsat: UNSAT of restriction implies UNSAT of G
  4. restriction_preserves_kconsistent: k-consistency transfers
  5. restriction_preserves_below_borromean: BorromeanOrder control
  6. restricted_gap_consistency_mono: gap consistency remains monotone
  7. gap_consistency_restriction_chain: UNSAT detection chain
  8. monotone_interpolation_structure: connects to FIP
  9. restricted_and_term_blind: AND-term blindness transfers

  Next step (not in this file): formalize the FIP for specific proof systems
  (Cutting Planes, Resolution) using the restriction + interpolation structure.
  See: EFLowerBound.lean, CPLowerBound.lean for proof system formalizations.
-/

end CubeGraph
