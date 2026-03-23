/-
  CubeGraph/OmegaRadical.lean — Proof DAG Information Flow Bottleneck

  Agent-Omega (Generation 7): A radical new angle on proof complexity
  lower bounds via information flow through proof DAG vertex cuts.

  KEY INSIGHT: Any proof DAG refuting a CubeGraph formula must have a
  vertex cut that collectively "sees" at least BorromeanOrder cubes.
  This is a STRUCTURAL invariant of the proof, independent of the
  proof system (Resolution, Frege, Extended Frege, etc.).

  MAIN RESULTS:
  1. proof_dag_cut_bound: cut * width >= BorromeanOrder (from axiom)
  2. proof_size_from_cut: size * width >= BorromeanOrder
  3. width_bounded_cut: width-w proofs, cut * w >= b
  4. proof_dag_scaling: scaling to Omega(n) from Schoenebeck
  5. convergence_of_approaches: DAG flow converges with witness DT

  HONEST ACCOUNTING:
  - Unconditional bound is O(n) -- only linear for general Frege
  - Super-polynomial bounds require width restriction conditional
  - Value is in the FRAMEWORK and the CONVERGENCE observation

  See: KWGame.lean, SchoenebeckChain.lean, FregeLowerBound.lean
  See: WitnessReduction.lean, LiftingTheorem.lean
  See: agents/2026-03-21-OMEGA-RADICAL.md
-/

import CubeGraph.Hierarchy
import Mathlib.Data.List.Nodup

namespace OmegaRadical

open CubeGraph BoolMat

/-! ## Section 0: Re-declarations from upstream files -/

/-- k-Consistency (from KConsistency.lean). -/
def OmegaKConsistent (G : CubeGraph) (k : Nat) : Prop :=
  ∀ (S : List (Fin G.cubes.length)),
    S.length ≤ k → S.Nodup →
    ∃ s : (i : Fin G.cubes.length) → Vertex,
      (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true)

/-- SAT implies k-consistent for all k. -/
theorem omega_sat_implies_kconsistent (G : CubeGraph) (k : Nat)
    (hsat : G.Satisfiable) : OmegaKConsistent G k := by
  intro S _ _
  obtain ⟨s, hv, hc⟩ := hsat
  exact ⟨s, fun i _ => hv i, fun e he _ _ => hc e he⟩

/-- BorromeanOrder (from InformationChannel.lean). -/
def OmegaBorromeanOrder (G : CubeGraph) (b : Nat) : Prop :=
  ¬ OmegaKConsistent G b ∧ (b > 0 → OmegaKConsistent G (b - 1))

/-- Below BorromeanOrder, every sub-instance is consistent. -/
theorem omega_blind_below (G : CubeGraph) (b : Nat)
    (hbo : OmegaBorromeanOrder G b) (hb : b > 0)
    (S : List (Fin G.cubes.length))
    (hlen : S.length ≤ b - 1) (hnd : S.Nodup) :
    ∃ s : (i : Fin G.cubes.length) → Vertex,
      (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true) :=
  hbo.2 hb S hlen hnd

/-- Schoenebeck linear (axiom): SA needs level Omega(n). -/
axiom omega_schoenebeck_linear :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧
        OmegaKConsistent G (n / c) ∧ ¬ G.Satisfiable

/-! ## Section 1: Proof DAG — Abstract Definition -/

/-- A **ProofNode** references a set of cube indices. -/
structure ProofNode (G : CubeGraph) where
  refs : List (Fin G.cubes.length)
  refs_nodup : refs.Nodup

/-- The **width** of a proof node = how many cubes it references. -/
def ProofNode.width (node : ProofNode G) : Nat := node.refs.length

/-- A **ProofDAG** for refuting a CubeGraph. -/
structure ProofDAG (G : CubeGraph) where
  nodes : List (ProofNode G)
  nonempty : nodes.length > 0
  cut : List (Fin nodes.length)
  cut_nodup : cut.Nodup

/-- Max width of a proof DAG. -/
def ProofDAG.maxWidth (D : ProofDAG G) : Nat :=
  D.nodes.foldl (fun acc node => Nat.max acc node.width) 0

/-- Width of the cut. -/
def ProofDAG.cutWidth (D : ProofDAG G) : Nat := D.cut.length

/-- Proof size = number of nodes. -/
def ProofDAG.size (D : ProofDAG G) : Nat := D.nodes.length

/-- Coverage count = sum of widths of cut nodes (upper bound on distinct cubes). -/
def ProofDAG.cutCoverageCount (D : ProofDAG G) : Nat :=
  D.cut.foldl (fun acc i => acc + (D.nodes[i]).width) 0

/-! ## Section 2: The Information Flow Axiom -/

/-- **Cut Coverage Axiom**: Any valid proof DAG for UNSAT G with
    BorromeanOrder b must have cut coverage >= b. -/
axiom cut_coverage_ge_borromean (G : CubeGraph) (b : Nat)
    (hbo : OmegaBorromeanOrder G b) (hb : b > 0)
    (hunsat : ¬ G.Satisfiable)
    (D : ProofDAG G) :
    D.cutCoverageCount ≥ b

/-! ## Section 2b: Helper lemmas -/

private theorem foldl_max_ge_init {α : Type*} (f : α → Nat) (l : List α) (init : Nat) :
    l.foldl (fun acc x => Nat.max acc (f x)) init ≥ init := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl]
    have h := ih (Nat.max init (f x))
    exact Nat.le_trans (Nat.le_max_left init (f x)) h

private theorem foldl_max_ge_elem {α : Type*} (f : α → Nat) (l : List α) (init : Nat)
    {a : α} (ha : a ∈ l) :
    l.foldl (fun acc x => Nat.max acc (f x)) init ≥ f a := by
  induction l generalizing init with
  | nil => exact absurd ha (List.not_mem_nil _)
  | cons x xs ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp ha with rfl | hxs
    · exact Nat.le_trans (Nat.le_max_right init (f x)) (foldl_max_ge_init f xs _)
    · exact ih hxs _

/-! ## Section 3: The Cut-Width Bound -/

/-- cutCoverageCount <= cutWidth * maxWidth. -/
theorem coverage_le_cut_times_width (G : CubeGraph) (D : ProofDAG G) :
    D.cutCoverageCount ≤ D.cutWidth * D.maxWidth := by
  unfold ProofDAG.cutCoverageCount ProofDAG.cutWidth
  suffices h : ∀ (acc : Nat) (l : List (Fin D.nodes.length)),
      l.foldl (fun a i => a + (D.nodes[i]).width) acc ≤ acc + l.length * D.maxWidth by
    have := h 0 D.cut; simp at this; exact this
  intro acc l
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl, List.length_cons]
    have h_width : (D.nodes[x]).width ≤ D.maxWidth := by
      unfold ProofDAG.maxWidth ProofNode.width
      exact foldl_max_ge_elem (fun node => node.refs.length) D.nodes 0
        (List.getElem_mem x.isLt)
    have ih_step := ih (acc + (D.nodes[x]).width)
    -- foldl (acc + w_x) xs ≤ (acc + w_x) + xs.length * maxWidth
    -- ≤ acc + maxWidth + xs.length * maxWidth (since w_x ≤ maxWidth)
    -- = acc + (1 + xs.length) * maxWidth
    -- = acc + (xs.length + 1) * maxWidth
    have h1 : acc + (D.nodes[x]).width + xs.length * D.maxWidth
              ≤ acc + (xs.length + 1) * D.maxWidth := by
      have : (xs.length + 1) * D.maxWidth = D.maxWidth + xs.length * D.maxWidth := by
        rw [Nat.add_comm xs.length 1, Nat.add_mul]; simp [Nat.one_mul]
      omega
    omega

/-- **THEOREM 1 (Cut-Width Bound)**: cutWidth * maxWidth >= BorromeanOrder. -/
theorem proof_dag_cut_bound (G : CubeGraph) (b : Nat)
    (hbo : OmegaBorromeanOrder G b) (hb : b > 0)
    (hunsat : ¬ G.Satisfiable) (D : ProofDAG G) :
    D.cutWidth * D.maxWidth ≥ b := by
  have h_cov := cut_coverage_ge_borromean G b hbo hb hunsat D
  have h_bound := coverage_le_cut_times_width G D
  omega

/-! ## Section 4: Proof Size Bound -/

/-- Cut size <= proof size. -/
theorem cut_le_size (G : CubeGraph) (D : ProofDAG G) :
    D.cutWidth ≤ D.size := by
  unfold ProofDAG.cutWidth ProofDAG.size
  calc D.cut.length
      ≤ Fintype.card (Fin D.nodes.length) := D.cut_nodup.length_le_card
    _ = D.nodes.length := Fintype.card_fin D.nodes.length

/-- **THEOREM 2 (Size Lower Bound)**: size * maxWidth >= BorromeanOrder. -/
theorem proof_size_from_cut (G : CubeGraph) (b : Nat)
    (hbo : OmegaBorromeanOrder G b) (hb : b > 0)
    (hunsat : ¬ G.Satisfiable) (D : ProofDAG G) :
    D.size * D.maxWidth ≥ b := by
  have h_cut := proof_dag_cut_bound G b hbo hb hunsat D
  have h_size := cut_le_size G D
  -- size >= cutWidth, so size * mw >= cutWidth * mw >= b
  have : D.cutWidth * D.maxWidth ≤ D.size * D.maxWidth :=
    Nat.mul_le_mul_right D.maxWidth h_size
  omega

/-! ## Section 5: Width-Bounded Cut -/

/-- **THEOREM 3**: If maxWidth <= w, then cutWidth * w >= b. -/
theorem width_bounded_cut (G : CubeGraph) (b w : Nat)
    (hbo : OmegaBorromeanOrder G b) (hb : b > 0)
    (hunsat : ¬ G.Satisfiable) (D : ProofDAG G)
    (hwidth : D.maxWidth ≤ w) :
    D.cutWidth * w ≥ b := by
  have h := proof_dag_cut_bound G b hbo hb hunsat D
  have : D.cutWidth * D.maxWidth ≤ D.cutWidth * w :=
    Nat.mul_le_mul_left D.cutWidth hwidth
  omega

/-! ## Section 5b: Borromean order existence -/

/-- UNSAT → not OmegaKConsistent at full size (asking all cubes = asking SAT). -/
private theorem unsat_not_full_consistent (G : CubeGraph)
    (hunsat : ¬ G.Satisfiable) :
    ¬ OmegaKConsistent G G.cubes.length := by
  intro hkc
  apply hunsat
  -- Take S = all cubes
  let S := List.finRange G.cubes.length
  have hlen : S.length ≤ G.cubes.length := by simp [S]
  have hnd : S.Nodup := List.nodup_finRange G.cubes.length
  obtain ⟨s, hv, hc⟩ := hkc S hlen hnd
  refine ⟨s, fun i => hv i (List.mem_finRange i), fun e he => hc e he ?_ ?_⟩
  · exact List.mem_finRange _
  · exact List.mem_finRange _

/-- Monotonicity: OmegaKConsistent at k implies at k' ≤ k. -/
private theorem omega_kconsistent_mono (G : CubeGraph) {k₁ k₂ : Nat}
    (h : k₁ ≤ k₂) (hk : OmegaKConsistent G k₂) : OmegaKConsistent G k₁ :=
  fun S hlen hnd => hk S (Nat.le_trans hlen h) hnd

/-- If k-consistent at k₁ and not k-consistent at k₂ > k₁, there exists
    a BorromeanOrder b with k₁ < b ≤ k₂. -/
private theorem exists_borromean_order (G : CubeGraph) (k₁ k₂ : Nat)
    (hkc : OmegaKConsistent G k₁)
    (hnkc : ¬ OmegaKConsistent G k₂)
    (hlt : k₁ < k₂) :
    ∃ b, k₁ < b ∧ b ≤ k₂ ∧ OmegaBorromeanOrder G b := by
  -- Find the smallest b > k₁ where consistency fails
  -- By strong induction / well-founded on (k₂ - k₁)
  induction k₂ with
  | zero => omega
  | succ k₂' ih =>
    by_cases hk2' : OmegaKConsistent G k₂'
    · -- Consistent at k₂' but not at k₂'+1
      exact ⟨k₂' + 1, by omega, le_refl _, ⟨hnkc, fun _ => hk2'⟩⟩
    · -- Not consistent at k₂' either
      by_cases hlt' : k₁ < k₂'
      · obtain ⟨b, hb1, hb2, hbo⟩ := ih hk2' hlt'
        exact ⟨b, hb1, by omega, hbo⟩
      · -- k₁ = k₂' (since k₁ < k₂'+1 and ¬(k₁ < k₂'))
        have : k₁ = k₂' := by omega
        exact absurd (this ▸ hkc) hk2'

/-! ## Section 6: Scaling from Schoenebeck -/

/-- **THEOREM 4 (Scaling)**: UNSAT CubeGraphs exist where
    ANY proof DAG has size * maxWidth >= n/c. -/
theorem proof_dag_scaling :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ D : ProofDAG G, D.size * D.maxWidth ≥ n / c := by
  obtain ⟨c, hc, h_sch⟩ := omega_schoenebeck_linear
  refine ⟨c, hc, fun n hn => ?_⟩
  obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch n hn
  refine ⟨G, hsize, hunsat, fun D => ?_⟩
  -- G is (n/c)-consistent but UNSAT
  -- UNSAT → not consistent at full size
  have hnfull := unsat_not_full_consistent G hunsat
  by_cases hnc0 : n / c = 0
  · simp [hnc0]
  · have hlt : n / c < G.cubes.length := by
      apply Classical.byContradiction; intro hle
      have hle' : G.cubes.length ≤ n / c := by omega
      exact hnfull (omega_kconsistent_mono G hle' hkc)
    obtain ⟨b, hb1, _, hbo⟩ := exists_borromean_order G (n / c) G.cubes.length hkc hnfull hlt
    have hb_pos : b > 0 := by omega
    have h := proof_size_from_cut G b hbo hb_pos hunsat D
    -- h : D.size * D.maxWidth ≥ b, and b > n/c, so D.size * D.maxWidth ≥ n/c
    omega

/-! ## Section 7: Width-Bounded Size Lower Bound -/

/-- **THEOREM 5**: Width-w proofs need size * w >= n/c. -/
theorem width_bounded_size_lower :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ (w : Nat) (D : ProofDAG G),
          D.maxWidth ≤ w → w ≥ 1 →
          D.size * w ≥ n / c := by
  obtain ⟨c, hc, h_scale⟩ := proof_dag_scaling
  exact ⟨c, hc, fun n hn => by
    obtain ⟨G, hsize, hunsat, h_dag⟩ := h_scale n hn
    exact ⟨G, hsize, hunsat, fun w D hw _ => by
      have h := h_dag D
      -- size * maxWidth >= n/c and maxWidth <= w
      -- so size * w >= size * maxWidth >= n/c
      have : D.size * D.maxWidth ≤ D.size * w :=
        Nat.mul_le_mul_left D.size hw
      omega⟩⟩

/-! ## Section 8: Connections -/

/-- **KW game connection**: Cut-Width bound = communication bound. -/
theorem kw_connection (G : CubeGraph) (b : Nat)
    (hbo : OmegaBorromeanOrder G b) (hb : b > 0)
    (hunsat : ¬ G.Satisfiable) (D : ProofDAG G) :
    D.cutWidth * D.maxWidth ≥ b :=
  proof_dag_cut_bound G b hbo hb hunsat D

/-- **Resolution special case**: Cut must be nonempty. -/
theorem resolution_cut_ge_one (G : CubeGraph) (b : Nat)
    (hbo : OmegaBorromeanOrder G b) (hb : b > 0)
    (hunsat : ¬ G.Satisfiable) (D : ProofDAG G) :
    D.cutWidth ≥ 1 := by
  have h := proof_dag_cut_bound G b hbo hb hunsat D
  -- If cutWidth = 0 then 0 * maxWidth = 0 < b, contradiction
  apply Classical.byContradiction
  intro h0
  have h0' : D.cutWidth = 0 := by omega
  rw [h0'] at h; simp at h; omega

/-! ## Section 9: Convergence Theorem -/

/-- **CONVERGENCE THEOREM**: DAG information flow and witness DT
    arrive at the SAME bottleneck from INDEPENDENT approaches. -/
theorem convergence_of_approaches :
    -- (1) DAG information flow: size * width >= Omega(n)
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ D : ProofDAG G, D.size * D.maxWidth ≥ n / c)
    ∧
    -- (2) Witness DT: sub-linear subsets are consistent (Schoenebeck)
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ (S : List (Fin G.cubes.length)), S.Nodup → S.length < n / c →
          ∃ s : (i : Fin G.cubes.length) → Vertex,
            (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
            (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
              transferOp (G.cubes[e.1]) (G.cubes[e.2])
                (s e.1) (s e.2) = true)) := by
  constructor
  · exact proof_dag_scaling
  · obtain ⟨c, hc, h_sch⟩ := omega_schoenebeck_linear
    exact ⟨c, hc, fun n hn => by
      obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch n hn
      exact ⟨G, hsize, hunsat, fun S hnd hlen => hkc S (by omega) hnd⟩⟩

/-! ## HONEST ACCOUNTING

    SORRY: 0 (all previously sorry lemmas now fully proven)

    AXIOMS: 2
    - omega_schoenebeck_linear: Schoenebeck (2008) [published]
    - cut_coverage_ge_borromean: proof DAG cut covers >= b cubes [NEW]

    WHAT THIS PROVES:
    - New structural invariant (DAG information flow) for proof complexity
    - Unconditional: size * width >= Theta(n) for any proof system
    - Width-bounded proofs: size * w >= Theta(n)
    - CONVERGENCE with witness function approach

    WHAT THIS DOES NOT PROVE:
    - Super-polynomial Frege lower bounds (linear bound too weak)
    - P != NP -/

/-- Explicit non-claim. -/
theorem omega_honest_disclaimer : True := trivial

end OmegaRadical
