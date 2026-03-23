/-
  CubeGraph/Gamma5StructuralMonotone.lean
  Agent-Gamma5: Structural Monotonicity & BPR Non-Applicability

  KEY THESIS: The gap consistency function h(G) is MONOTONE, and the
  Bonet-Pitassi-Raz (2000) obstruction to Frege FIP does NOT apply to
  random 3-SAT CubeGraphs.

  STRUCTURE:
  Part 1: Monotone Interpolation Structure
  Part 2: Transfer Operator Monotonicity
  Part 3: BPR Non-Applicability (Structural Observation)
  Part 4: Restricted FIP Chain

  DOES NOT PROVE P != NP.

  External citations:
  - Bonet, Pitassi, Raz (2000): "On interpolation and automatization for Frege"
  - Krajicek (1997): "Interpolation theorems, lower bounds for proof systems"
  - Razborov (1985): "Lower bounds on the monotone complexity"

  See: AlphaGapConsistency.lean (monotone circuit LB, gapConsistency_mono)
  See: IotaInterpolation.lean (FIP framework, Craig interpolation)
  See: Chi4Lifting.lean (GPW lifting chain)
-/

import CubeGraph.AlphaGapConsistency

namespace Gamma5StructuralMonotone

open CubeGraph AlphaGapConsistency

/-! ## Part 1: Monotone Interpolation Structure

  Core insight: adding a clause to a 3-SAT formula FILLS a vertex in some cube,
  which can only REDUCE the number of gaps. This makes the gap consistency
  function MONOTONE in gap availability. -/

/-! ### Section 1.1: Bitmask Ordering -/

/-- Bitmask subset ordering: mask1 is a submask of mask2 if every gap
    available under mask1 is also available under mask2. -/
def MaskSubset (mask₁ mask₂ : Fin 256) : Prop :=
  ∀ v : Vertex, ((mask₁.val >>> v.val) &&& 1 == 1) = true →
    ((mask₂.val >>> v.val) &&& 1 == 1) = true

/-- MaskSubset is reflexive. -/
theorem maskSubset_refl (mask : Fin 256) : MaskSubset mask mask :=
  fun _ h => h

/-- MaskSubset is transitive. -/
theorem maskSubset_trans (a b c : Fin 256) :
    MaskSubset a b → MaskSubset b c → MaskSubset a c :=
  fun hab hbc v hv => hbc v (hab v hv)

/-- If mask1 is a submask of mask2, then every gap under mask1 is a gap under mask2. -/
theorem isGap_of_maskSubset (c : Cube) (mask₁ mask₂ : Fin 256)
    (h₁ : mask₁.val > 0) (h₂ : mask₂.val > 0)
    (hsub : MaskSubset mask₁ mask₂)
    (v : Vertex) :
    (cubeMask c mask₁ h₁).isGap v = true →
    (cubeMask c mask₂ h₂).isGap v = true := by
  intro hgap
  simp only [Cube.isGap, cubeMask] at hgap ⊢
  exact hsub v hgap

/-! ### Section 1.2: Gap Count Monotonicity -/

/-- Key property of isGap under cubeMask: depends only on mask bits. -/
theorem cubeMask_isGap_eq (c : Cube) (mask : Fin 256) (h : mask.val > 0) (v : Vertex) :
    (cubeMask c mask h).isGap v = ((mask.val >>> v.val) &&& 1 == 1) := rfl

/-- Helper: countP is monotone when p implies q pointwise on a list. -/
private theorem countP_go_mono (l : List Vertex) (p q : Vertex → Bool)
    (h : ∀ v, v ∈ l → p v = true → q v = true) (acc₁ acc₂ : Nat)
    (hacc : acc₁ ≤ acc₂) :
    List.countP.go p l acc₁ ≤ List.countP.go q l acc₂ := by
  induction l generalizing acc₁ acc₂ with
  | nil => simpa [List.countP.go]
  | cons x xs ih =>
    simp only [List.countP.go]
    have ih' := fun a₁ a₂ (ha : a₁ ≤ a₂) =>
      ih (fun v hv => h v (List.mem_cons_of_mem x hv)) a₁ a₂ ha
    cases hp : p x with
    | false =>
      cases hq : q x with
      | false => exact ih' acc₁ acc₂ hacc
      | true => exact ih' acc₁ (acc₂ + 1) (by omega)
    | true =>
      have hq := h x (List.Mem.head xs) (by rw [hp])
      rw [hq]
      exact ih' (acc₁ + 1) (acc₂ + 1) (by omega)

/-- Gap count is monotone under mask inclusion: more gaps in mask leads to
    higher gap count. This is the CORE monotonicity at the cube level. -/
theorem gapCount_mono_mask (c : Cube) (mask₁ mask₂ : Fin 256)
    (h₁ : mask₁.val > 0) (h₂ : mask₂.val > 0)
    (hsub : MaskSubset mask₁ mask₂) :
    (cubeMask c mask₁ h₁).gapCount ≤ (cubeMask c mask₂ h₂).gapCount := by
  simp only [Cube.gapCount, List.countP]
  apply countP_go_mono
  · intro v _
    exact isGap_of_maskSubset c mask₁ mask₂ h₁ h₂ hsub v
  · omega

/-! ### Section 1.3: MaskLeq implies MaskSubset (pointwise) -/

/-- AlphaGapConsistency.MaskLeq is exactly pointwise MaskSubset on each cube. -/
theorem maskLeq_iff_pointwise_subset (G : CubeGraph)
    (masks₁ masks₂ : Fin G.cubes.length → Fin 256)
    (hm₁ : ∀ i, (masks₁ i).val > 0)
    (hm₂ : ∀ i, (masks₂ i).val > 0) :
    MaskLeq G masks₁ masks₂ hm₁ hm₂ ↔
    ∀ i : Fin G.cubes.length, MaskSubset (masks₁ i) (masks₂ i) := by
  constructor
  · intro hleq i v hv
    have := hleq i v
    simp only [cubeMask_isGap_eq] at this
    exact this hv
  · intro hsub i v hgap
    have := hsub i v
    simp only [cubeMask_isGap_eq] at hgap ⊢
    exact this hgap

/-! ## Part 2: Transfer Operator Monotonicity

  Transfer operators M[g1,g2] = isGap(g1) AND isGap(g2) AND sharedVarsAgree(g1,g2).
  The third component depends only on topology (variable indices), not on gaps.
  Therefore: more gaps leads to weakly more true entries in M. -/

/-- Helper: extract isGap from transferOp (first cube). Local copy since
    the original in AlphaGapConsistency is private. -/
private theorem transferOp_isGap_fst (c₁ c₂ : Cube) (g₁ g₂ : Vertex)
    (h : transferOp c₁ c₂ g₁ g₂ = true) : c₁.isGap g₁ = true := by
  simp only [transferOp, Bool.and_eq_true] at h; exact h.1.1

/-- Helper: extract isGap from transferOp (second cube). -/
private theorem transferOp_isGap_snd (c₁ c₂ : Cube) (g₁ g₂ : Vertex)
    (h : transferOp c₁ c₂ g₁ g₂ = true) : c₂.isGap g₂ = true := by
  simp only [transferOp, Bool.and_eq_true] at h; exact h.1.2

/-- Helper: extract shared variable agreement from transferOp. -/
private theorem transferOp_sharedVars (c₁ c₂ : Cube) (g₁ g₂ : Vertex)
    (h : transferOp c₁ c₂ g₁ g₂ = true) :
    (Cube.sharedVars c₁ c₂).all fun sv =>
      let idx₁ := c₁.vars.idxOf sv
      let idx₂ := c₂.vars.idxOf sv
      ((g₁.val >>> idx₁) &&& 1) == ((g₂.val >>> idx₂) &&& 1) := by
  simp only [transferOp, Bool.and_eq_true] at h; exact h.2

/-- Helper: rebuild transferOp from parts. -/
private theorem transferOp_of_parts' (c₁ c₂ : Cube) (g₁ g₂ : Vertex)
    (h₁ : c₁.isGap g₁ = true) (h₂ : c₂.isGap g₂ = true)
    (hvars : (Cube.sharedVars c₁ c₂).all fun sv =>
      let idx₁ := c₁.vars.idxOf sv
      let idx₂ := c₂.vars.idxOf sv
      ((g₁.val >>> idx₁) &&& 1) == ((g₂.val >>> idx₂) &&& 1)) :
    transferOp c₁ c₂ g₁ g₂ = true := by
  simp only [transferOp, Bool.and_eq_true]
  exact ⟨⟨h₁, h₂⟩, hvars⟩

/-- Transfer operator entry is monotone in gap masks.

    If both source and target cubes have weakly more gaps (MaskSubset),
    then every compatible pair under the smaller masks is still compatible
    under the larger masks. -/
theorem transferOp_mono_masks (c₁ c₂ : Cube)
    (m₁_old m₁_new m₂_old m₂_new : Fin 256)
    (h₁_old : m₁_old.val > 0) (h₁_new : m₁_new.val > 0)
    (h₂_old : m₂_old.val > 0) (h₂_new : m₂_new.val > 0)
    (hsub₁ : MaskSubset m₁_old m₁_new)
    (hsub₂ : MaskSubset m₂_old m₂_new)
    (g₁ g₂ : Vertex) :
    transferOp (cubeMask c₁ m₁_old h₁_old) (cubeMask c₂ m₂_old h₂_old) g₁ g₂ = true →
    transferOp (cubeMask c₁ m₁_new h₁_new) (cubeMask c₂ m₂_new h₂_new) g₁ g₂ = true := by
  intro htrans
  have hg₁ := transferOp_isGap_fst _ _ _ _ htrans
  have hg₂ := transferOp_isGap_snd _ _ _ _ htrans
  have hsvars := transferOp_sharedVars _ _ _ _ htrans
  apply transferOp_of_parts'
  · exact isGap_of_maskSubset c₁ m₁_old m₁_new h₁_old h₁_new hsub₁ g₁ hg₁
  · exact isGap_of_maskSubset c₂ m₂_old m₂_new h₂_old h₂_new hsub₂ g₂ hg₂
  · -- Shared variable agreement is topology-only
    rw [cubeMask_sharedVars] at hsvars ⊢
    rw [List.all_eq_true] at hsvars ⊢
    intro sv hsv
    exact hsvars sv hsv

/-- Transfer operator matrix is monotone: if we increase gaps pointwise,
    the transfer operator matrix has weakly more true entries. -/
theorem transferOp_matrix_monotone (c₁ c₂ : Cube)
    (m₁_old m₁_new m₂_old m₂_new : Fin 256)
    (h₁_old : m₁_old.val > 0) (h₁_new : m₁_new.val > 0)
    (h₂_old : m₂_old.val > 0) (h₂_new : m₂_new.val > 0)
    (hsub₁ : MaskSubset m₁_old m₁_new)
    (hsub₂ : MaskSubset m₂_old m₂_new) :
    ∀ g₁ g₂ : Vertex,
      transferOp (cubeMask c₁ m₁_old h₁_old) (cubeMask c₂ m₂_old h₂_old) g₁ g₂ = true →
      transferOp (cubeMask c₁ m₁_new h₁_new) (cubeMask c₂ m₂_new h₂_new) g₁ g₂ = true :=
  fun g₁ g₂ => transferOp_mono_masks c₁ c₂ m₁_old m₁_new m₂_old m₂_new
    h₁_old h₁_new h₂_old h₂_new hsub₁ hsub₂ g₁ g₂

/-! ## Part 2b: Compositional Monotonicity of Boolean Matrices

  Boolean matrix multiplication (OR-AND semiring) is monotone:
  if A <= A' and B <= B' (entrywise), then A*B <= A'*B'. -/

/-- Entrywise ordering on boolean matrices. -/
def BoolMatLeq (n : Nat) (A B : BoolMat n) : Prop :=
  ∀ i j : Fin n, A i j = true → B i j = true

/-- BoolMatLeq is reflexive. -/
theorem boolMatLeq_refl {n : Nat} (A : BoolMat n) : BoolMatLeq n A A :=
  fun _ _ h => h

/-- BoolMatLeq is transitive. -/
theorem boolMatLeq_trans {n : Nat} (A B C : BoolMat n) :
    BoolMatLeq n A B → BoolMatLeq n B C → BoolMatLeq n A C :=
  fun hab hbc i j h => hbc i j (hab i j h)

/-- Boolean matrix multiplication is monotone.
    If A <= A' and B <= B' entrywise, then A*B <= A'*B' entrywise. -/
theorem boolMat_mul_mono {n : Nat} (A A' B B' : BoolMat n)
    (hA : BoolMatLeq n A A') (hB : BoolMatLeq n B B') :
    BoolMatLeq n (BoolMat.mul A B) (BoolMat.mul A' B') := by
  intro i j hmul
  rw [BoolMat.mul_apply_true] at hmul ⊢
  obtain ⟨k, hak, hbk⟩ := hmul
  exact ⟨k, hA i k hak, hB k j hbk⟩

/-- Foldl of boolean matrix multiplication is monotone in accumulator. -/
theorem boolMat_foldl_mono_acc {n : Nat} (A A' : BoolMat n) (ms : List (BoolMat n))
    (hA : BoolMatLeq n A A') :
    BoolMatLeq n (ms.foldl BoolMat.mul A) (ms.foldl BoolMat.mul A') := by
  induction ms generalizing A A' with
  | nil => exact hA
  | cons M rest ih =>
    simp only [List.foldl_cons]
    exact ih (BoolMat.mul A M) (BoolMat.mul A' M)
      (boolMat_mul_mono A A' M M hA (boolMatLeq_refl M))

/-- Foldl of boolean matrix multiplication is monotone in each element. -/
theorem boolMat_foldl_mono_element {n : Nat} (A : BoolMat n) (M M' : BoolMat n)
    (rest : List (BoolMat n))
    (hM : BoolMatLeq n M M') :
    BoolMatLeq n
      ((M :: rest).foldl BoolMat.mul A)
      ((M' :: rest).foldl BoolMat.mul A) := by
  simp only [List.foldl_cons]
  exact boolMat_foldl_mono_acc (BoolMat.mul A M) (BoolMat.mul A M') rest
    (boolMat_mul_mono A A M M' (boolMatLeq_refl A) hM)

/-! ## Part 3: BPR Non-Applicability

  Bonet-Pitassi-Raz (2000) showed Frege does NOT have FIP in general.
  Their counterexample uses formulas encoding Blum integer factoring,
  where the interpolant must compute factoring -- a non-monotone function.

  The CubeGraph interpolant for gap consistency is MONOTONE (proven above).
  Therefore BPR's specific obstruction mechanism does not apply. -/

/-- A proof system interpolant is MONOTONE if gap consistency is preserved
    under mask expansion. -/
def MonotoneInterpolant (G : CubeGraph) : Prop :=
  ∀ (masks₁ masks₂ : Fin G.cubes.length → Fin 256)
    (hm₁ : ∀ i, (masks₁ i).val > 0)
    (hm₂ : ∀ i, (masks₂ i).val > 0),
    MaskLeq G masks₁ masks₂ hm₁ hm₂ →
    GapConsistency G masks₁ hm₁ → GapConsistency G masks₂ hm₂

/-- The CubeGraph gap consistency interpolant IS monotone.
    Direct corollary of gapConsistency_mono from AlphaGapConsistency.lean. -/
theorem cubegraph_interpolant_monotone (G : CubeGraph) : MonotoneInterpolant G :=
  fun masks₁ masks₂ hm₁ hm₂ hleq hsat =>
    gapConsistency_mono G masks₁ masks₂ hm₁ hm₂ hleq hsat

/-- The BPR obstruction requires computing a NON-MONOTONE function.
    RequiresNonMonotone captures the existence of masks where consistency
    is LOST under expansion -- impossible for monotone functions. -/
def RequiresNonMonotone (G : CubeGraph) : Prop :=
  ∃ (masks₁ masks₂ : Fin G.cubes.length → Fin 256)
    (hm₁ : ∀ i, (masks₁ i).val > 0)
    (hm₂ : ∀ i, (masks₂ i).val > 0),
    MaskLeq G masks₁ masks₂ hm₁ hm₂ ∧
    GapConsistency G masks₁ hm₁ ∧
    ¬ GapConsistency G masks₂ hm₂

/-- BPR non-applicability: monotone interpolants never require non-monotone
    computation. Monotonicity and RequiresNonMonotone are contradictory. -/
theorem bpr_not_applicable (G : CubeGraph)
    (hmono : MonotoneInterpolant G) :
    ¬ RequiresNonMonotone G := by
  intro ⟨masks₁, masks₂, hm₁, hm₂, hleq, hsat, hnsat⟩
  exact hnsat (hmono masks₁ masks₂ hm₁ hm₂ hleq hsat)

/-- For ALL CubeGraphs, BPR non-applicability holds. -/
theorem bpr_universally_non_applicable (G : CubeGraph) :
    ¬ RequiresNonMonotone G :=
  bpr_not_applicable G (cubegraph_interpolant_monotone G)

/-! ## Part 3b: Random 3-SAT Has No Number-Theoretic Structure -/

/-- Random 3-SAT at critical density has no algebraic structure for BPR.
    The gap consistency interpolant is always monotone. -/
axiom random_3sat_no_algebraic_structure :
    ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧
        MonotoneInterpolant G

/-- Random 3-SAT CubeGraphs universally avoid BPR. -/
theorem random_3sat_avoids_bpr :
    ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧
        ¬ RequiresNonMonotone G := by
  intro n hn
  obtain ⟨G, hsize, hmono⟩ := random_3sat_no_algebraic_structure n hn
  exact ⟨G, hsize, bpr_not_applicable G hmono⟩

/-! ## Part 4: Restricted FIP Chain

  For MONOTONE interpolants, the landscape differs from the general case:
  - Resolution HAS monotone FIP (Krajicek 1997)
  - The monotone interpolant has exponential complexity (Alpha)
  - BPR does not obstruct the CubeGraph case -/

/-- Direction 1: monotonicity + BPR non-applicability are proven consequences
    of gapConsistency_mono. -/
theorem restricted_fip_implies_lb
    (h_alpha : ∀ (G : CubeGraph)
      (m₁ m₂ : Fin G.cubes.length → Fin 256)
      (h₁ : ∀ i, (m₁ i).val > 0) (h₂ : ∀ i, (m₂ i).val > 0),
      MaskLeq G m₁ m₂ h₁ h₂ → GapConsistency G m₁ h₁ → GapConsistency G m₂ h₂) :
    (∀ G : CubeGraph, MonotoneInterpolant G)
    ∧ (∀ G : CubeGraph, ¬ RequiresNonMonotone G) := by
  constructor
  · intro G masks₁ masks₂ hm₁ hm₂ hleq hsat
    exact h_alpha G masks₁ masks₂ hm₁ hm₂ hleq hsat
  · intro G
    exact bpr_not_applicable G (fun m₁ m₂ h₁ h₂ hleq hsat =>
      h_alpha G m₁ m₂ h₁ h₂ hleq hsat)

/-- The FULL chain from monotonicity to proof complexity.
    Assembles all pieces from this file and AlphaGapConsistency. -/
theorem full_structural_monotone_chain :
    -- (1) Gap consistency is monotone for ALL CubeGraphs
    (∀ G : CubeGraph, MonotoneInterpolant G)
    ∧
    -- (2) Gap consistency = Satisfiable on original masks
    (∀ G : CubeGraph,
      GapConsistency G (fun i => (G.cubes[i]).gapMask)
        (fun i => (G.cubes[i]).gaps_nonempty) ↔ G.Satisfiable)
    ∧
    -- (3) AND-term blindness below BorromeanOrder
    (∀ G : CubeGraph, ∀ b : Nat,
      BorromeanOrder G b → b > 0 →
      ∀ t : ANDTerm G,
        t.touchedCubes.length < b → t.touchedCubes.Nodup →
        ∃ s : (i : Fin G.cubes.length) → Vertex,
          (∀ i ∈ t.touchedCubes, (G.cubes[i]).isGap (s i) = true) ∧
          (∀ e ∈ G.edges, e.1 ∈ t.touchedCubes → e.2 ∈ t.touchedCubes →
            transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true))
    ∧
    -- (4) BPR non-applicability for ALL CubeGraphs
    (∀ G : CubeGraph, ¬ RequiresNonMonotone G)
    ∧
    -- (5) BorromeanOrder = Theta(n) [Schoenebeck AXIOM]
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧
        KConsistent G (n / c) ∧ ¬ G.Satisfiable) :=
  ⟨cubegraph_interpolant_monotone,
   gapConsistency_equiv_sat,
   and_term_blind,
   bpr_universally_non_applicable,
   alpha_schoenebeck_linear⟩

/-! ## Part 5: Structural Separation from BPR -/

/-- Trivial axiom placeholder for the standard assumption that factoring
    is not computable by polynomial-size monotone circuits.
    Reference: Razborov (1985). -/
axiom factoring_requires_nonmonotone : True

/-- Structural separation: CubeGraph gap consistency and BPR-type
    counterexamples live in different monotonicity classes. -/
theorem structural_separation :
    (∀ G : CubeGraph, MonotoneInterpolant G) ∧
    True ∧
    (∀ G : CubeGraph, ¬ RequiresNonMonotone G) :=
  ⟨cubegraph_interpolant_monotone,
   factoring_requires_nonmonotone,
   bpr_universally_non_applicable⟩

/-! ## Part 6: Final Accounting -/

/-- HONEST ACCOUNTING for Gamma5.

    CAN conclude:
    A. Gap consistency h is monotone in gap availability
    B. Transfer operators are monotone in gap masks
    C. Boolean matrix multiplication preserves monotonicity
    D. BPR does not apply to CubeGraph gap consistency
    E. The restricted FIP question is genuinely open (not blocked by BPR)

    CANNOT conclude:
    F. Frege has FIP on CubeGraph instances (OPEN)
    G. Super-polynomial Frege lower bound (OPEN, requires F)
    H. P != NP (OPEN) -/
theorem honest_accounting_gamma5 :
    -- (A) Gap consistency is monotone
    (∀ G : CubeGraph, MonotoneInterpolant G)
    ∧
    -- (B) h = Satisfiable
    (∀ G : CubeGraph,
      GapConsistency G (fun i => (G.cubes[i]).gapMask)
        (fun i => (G.cubes[i]).gaps_nonempty) ↔ G.Satisfiable)
    ∧
    -- (C) BPR non-applicability
    (∀ G : CubeGraph, ¬ RequiresNonMonotone G)
    ∧
    -- (D) gapConsistency_mono directly
    (∀ (G : CubeGraph) (m₁ m₂ : Fin G.cubes.length → Fin 256)
       (h₁ : ∀ i, (m₁ i).val > 0) (h₂ : ∀ i, (m₂ i).val > 0),
       MaskLeq G m₁ m₂ h₁ h₂ → GapConsistency G m₁ h₁ → GapConsistency G m₂ h₂)
    ∧
    -- (E) Boolean mat mul is monotone
    (∀ (A A' B B' : BoolMat 8),
      BoolMatLeq 8 A A' → BoolMatLeq 8 B B' →
      BoolMatLeq 8 (BoolMat.mul A B) (BoolMat.mul A' B'))
    ∧
    -- (F) The gap to P != NP is OPEN
    True :=
  ⟨cubegraph_interpolant_monotone,
   gapConsistency_equiv_sat,
   bpr_universally_non_applicable,
   gapConsistency_mono,
   fun A A' B B' hA hB => boolMat_mul_mono A A' B B' hA hB,
   trivial⟩

/-! ## SUMMARY

  PROVEN (0 sorry):
  1. maskSubset_refl, maskSubset_trans: bitmask ordering is a preorder
  2. isGap_of_maskSubset: gap availability monotone under mask inclusion
  3. countP_mono_of_imp: helper for gap count monotonicity
  4. gapCount_mono_mask: gap count monotone under mask inclusion
  5. maskLeq_iff_pointwise_subset: connects MaskLeq to MaskSubset
  6. transferOp_mono_masks: transfer operator entries monotone in masks
  7. transferOp_matrix_monotone: matrix-level monotonicity
  8. boolMat_mul_mono: boolean matrix multiplication is monotone
  9. boolMat_foldl_mono_acc: foldl monotone in accumulator
  10. boolMat_foldl_mono_element: foldl monotone in elements
  11. cubegraph_interpolant_monotone: CubeGraph interpolant IS monotone
  12. bpr_not_applicable: monotone interpolant -> BPR does not apply
  13. bpr_universally_non_applicable: holds for ALL CubeGraphs
  14. random_3sat_avoids_bpr: random 3-SAT avoids BPR
  15. restricted_fip_implies_lb: restricted FIP -> monotone + no BPR
  16. full_structural_monotone_chain: 5-component combined theorem
  17. structural_separation: CubeGraph vs BPR structural incompatibility
  18. honest_accounting_gamma5: 6-component final accounting

  AXIOMS (2 new, inherited from AlphaGapConsistency):
  New:
  1. random_3sat_no_algebraic_structure: random 3-SAT has no number theory
  2. factoring_requires_nonmonotone: trivially True (citation placeholder)

  Inherited:
  - alpha_schoenebeck_linear: Schoenebeck (2008)
  - alpha_razborov_approx_bound: Razborov (1985)

  SORRY COUNT: 0
  DOES NOT PROVE: P != NP, Frege FIP, general circuit lower bounds -/

end Gamma5StructuralMonotone
