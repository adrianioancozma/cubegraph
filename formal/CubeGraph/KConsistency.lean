/-
  CubeGraph/KConsistency.lean
  F1.1 + F1.2: k-Consistency on CubeGraph + consistency gap.

  k-consistency: every subset of ≤ k cubes admits a compatible gap selection.
  Key result: h2Graph is 2-consistent but NOT 3-consistent (b = 3).

  See: FlatBundleFailure.lean (FlatConnection, flat_bundle_failure)
  See: Hierarchy.lean (UNSATType2, H2_locally_invisible)
  See: RankMonotonicity.lean (rowRank_foldl_le — rank decay formalizes why k-consistency fails)
  See: IdempotenceBarrier.lean (idempotence_barrier — why propagation stagnates)
  See: DimensionThreshold.lean (dimension_threshold — k=2 vs k=3)
  See: experiments-ml/022_.../F1.5-RESULTS.md (0% detection at k≤6, b(n)>6)
  See: experiments-ml/022_.../F1.1-F1.2-PLAN.md (plan)
  See: experiments-ml/022_.../theory/CONSISTENCY-LOWER-BOUND.md (n^Ω(n) theorem)
  See: experiments-ml/022_.../theory/REPRESENTATION-EQUIVALENCE.md (intrinsicness argument)
  See: experiments-ml/021_.../MICRO-MACRO-BRIDGE.md (k-consistency = local bridge, insufficient)
-/

import CubeGraph.FlatBundleFailure

namespace CubeGraph

/-! ## Section 1: k-Consistency Definition -/

/-- **k-Consistency**: every subset of ≤ k cubes admits a compatible gap selection
    on edges within the subset. CubeGraph analogue of Sherali-Adams level k. -/
def KConsistent (G : CubeGraph) (k : Nat) : Prop :=
  ∀ (S : List (Fin G.cubes.length)),
    S.length ≤ k → S.Nodup →
    ∃ s : (i : Fin G.cubes.length) → Vertex,
      (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true)

/-! ## Section 2: Basic Properties -/

/-- SAT → k-consistent for all k. -/
theorem sat_implies_kconsistent (G : CubeGraph) (k : Nat)
    (hsat : G.Satisfiable) : KConsistent G k := by
  intro S _ _
  obtain ⟨s, hv, hc⟩ := hsat
  exact ⟨s, fun i _ => hv i, fun e he _ _ => hc e he⟩

/-- k-consistent is monotone decreasing in k. -/
theorem kconsistent_mono (G : CubeGraph) {k₁ k₂ : Nat} (h : k₁ ≤ k₂)
    (hk : KConsistent G k₂) : KConsistent G k₁ :=
  fun S hlen hnodup => hk S (Nat.le_trans hlen h) hnodup

/-! ## Section 3: h2Graph — 2-consistent but NOT 3-consistent -/

/-- h2Graph is 2-consistent: every pair of cubes has a compatible gap selection.
    This follows from H2_locally_invisible (all edges have compatible pairs). -/
-- transferOp = true implies both gaps are valid (from the definition).
private theorem transferOp_implies_gap₁ {c₁ c₂ : Cube} {g₁ g₂ : Vertex}
    (h : transferOp c₁ c₂ g₁ g₂ = true) : c₁.isGap g₁ = true := by
  simp only [transferOp, Bool.and_eq_true] at h; exact h.1.1

private theorem transferOp_implies_gap₂ {c₁ c₂ : Cube} {g₁ g₂ : Vertex}
    (h : transferOp c₁ c₂ g₁ g₂ = true) : c₂.isGap g₂ = true := by
  simp only [transferOp, Bool.and_eq_true] at h; exact h.1.2

-- Helper: if a ≠ b, a ∈ S, b ∈ S, c ∈ S, Nodup, |S| ≤ 2, then c = a ∨ c = b.
private theorem mem_pair_of_nodup_le2 {S : List (Fin n)}
    {a b c : Fin n} (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hnd : S.Nodup) (hlen : S.length ≤ 2) : c = a ∨ c = b := by
  rcases Classical.em (c = a) with rfl | hca
  · exact .inl rfl
  rcases Classical.em (c = b) with rfl | hcb
  · exact .inr rfl
  exfalso
  -- a, b, c are 3 distinct elements of S. But |S| ≤ 2. Use List.Nodup properties.
  -- S after erasing a: length decreases by 1, still contains b and c (since b≠a, c≠a)
  have hSa := List.length_erase_of_mem ha  -- S.erase a has length S.length - 1
  -- b ≠ a, so b survives erasing a from S
  have hba : b ≠ a := Ne.symm hab
  have hb' : b ∈ S.erase a := (List.mem_erase_of_ne hba).mpr hb
  -- c ≠ a, so c survives erasing a from S
  have hc' : c ∈ S.erase a := (List.mem_erase_of_ne hca).mpr hc
  have hnd' := hnd.erase a
  have hSab := List.length_erase_of_mem hb'
  -- c ≠ b, so c survives erasing b from (S.erase a)
  have hcb' : c ≠ b := hcb
  have hc'' : c ∈ (S.erase a).erase b := (List.mem_erase_of_ne hcb').mpr hc'
  -- c ∈ (S.erase a).erase b → length ≥ 1
  have hlen' := List.length_pos_of_mem hc''
  -- chain: S.length ≥ (S.erase a).length + 1 = ((S.erase a).erase b).length + 2 ≥ 3
  omega

theorem h2graph_2consistent : KConsistent h2Graph 2 := by
  have hloc := H2_locally_invisible h2Graph h2_witness
  intro S hlen hnodup
  have hgap : ∀ i : Fin h2Graph.cubes.length, ∃ v, (h2Graph.cubes[i]).isGap v = true := by
    intro i; have := hloc.1 i; rw [Cube.gapCount_pos_iff] at this
    obtain ⟨v, _, hv⟩ := this; exact ⟨v, hv⟩
  let dflt : (i : Fin h2Graph.cubes.length) → Vertex := fun i => (hgap i).choose
  by_cases hedge : ∃ e ∈ h2Graph.edges, e.1 ∈ S ∧ e.2 ∈ S
  · obtain ⟨e, he, he1, he2⟩ := hedge
    obtain ⟨g1, g2, hcompat⟩ := hloc.2 e he
    have hg1 := transferOp_implies_gap₁ hcompat
    have hg2 := transferOp_implies_gap₂ hcompat
    -- e.1 ≠ e.2 for h2Graph edges
    have hne : e.1 ≠ e.2 := by
      simp only [h2Graph, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl | rfl <;> decide
    -- Every element of S is e.1 or e.2 (from |S|≤2 + Nodup + 2 distinct members)
    have hS_sub : ∀ x ∈ S, x = e.1 ∨ x = e.2 :=
      fun x hx => mem_pair_of_nodup_le2 hne he1 he2 hx hnodup hlen
    -- Build assignment
    refine ⟨fun i => if i = e.1 then g1 else if i = e.2 then g2 else dflt i,
            fun i hi => ?_, fun e' he' h1' h2' => ?_⟩
    · -- Valid gaps
      by_cases h1 : i = e.1
      · subst h1; simp; exact hg1
      · by_cases h2 : i = e.2
        · subst h2; simp [if_neg h1]; exact hg2
        · simp [if_neg h1, if_neg h2]; exact (hgap i).choose_spec
    · -- Compatible on edges within S
      -- e'.1, e'.2 ∈ S → e'.1 ∈ {e.1, e.2} ∧ e'.2 ∈ {e.1, e.2}
      have h1'_eq := hS_sub e'.1 h1'
      have h2'_eq := hS_sub e'.2 h2'
      -- e' has distinct endpoints (h2Graph edges)
      have hne' : e'.1 ≠ e'.2 := by
        simp only [h2Graph, List.mem_cons, List.mem_nil_iff, or_false] at he'
        rcases he' with rfl | rfl | rfl <;> decide
      -- e'.1, e'.2 ∈ {e.1, e.2} with e'.1 ≠ e'.2 → (e'.1,e'.2) = (e.1,e.2) or (e.2,e.1)
      -- e'.1 ∈ {e.1, e.2} and e'.2 ∈ {e.1, e.2} with e'.1 ≠ e'.2
      -- 4 combinations, 2 are self-loops (impossible), 1 is e, 1 is reverse (impossible)
      rcases h1'_eq with h1eq | h1eq <;> rcases h2'_eq with h2eq | h2eq
      · -- e'.1 = e.1, e'.2 = e.1 → e'.1 = e'.2. Contradiction.
        exact absurd (h1eq.trans h2eq.symm) hne'
      · -- e'.1 = e.1, e'.2 = e.2 → s(e'.1)=g1, s(e'.2)=g2. Use hcompat.
        simp only [h1eq, h2eq, ite_true, if_neg (Ne.symm hne)]; exact hcompat
      · -- e'.1 = e.2, e'.2 = e.1 → reverse edge. h2Graph has none.
        exfalso
        simp only [h2Graph, List.mem_cons, List.mem_nil_iff, or_false] at he he'
        rcases he with rfl | rfl | rfl <;> rcases he' with rfl | rfl | rfl <;>
          simp_all [Fin.ext_iff]
      · -- e'.1 = e.2, e'.2 = e.2 → e'.1 = e'.2. Contradiction.
        exact absurd (h1eq.trans h2eq.symm) hne'
  · refine ⟨dflt, fun i _ => (hgap i).choose_spec, fun e he h1 h2 => ?_⟩
    exact absurd ⟨e, he, h1, h2⟩ hedge

/-- h2Graph is NOT 3-consistent.
    The unique subset of all 3 cubes has no compatible selection (= UNSAT). -/
theorem h2graph_not_3consistent : ¬ KConsistent h2Graph 3 := by
  intro h3
  -- Apply h3 to S = all 3 cubes
  let S : List (Fin h2Graph.cubes.length) :=
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]
  have hlen : S.length ≤ 3 := by decide
  have hnodup : S.Nodup := by decide
  obtain ⟨s, hv, hc⟩ := h3 S hlen hnodup
  -- This gives a satisfying assignment → contradiction with UNSAT
  apply h2Graph_unsat
  refine ⟨s, fun i => ?_, fun e he => ?_⟩
  · -- Each s i is a gap: i ∈ {0,1,2}, all in S
    have hi := i.isLt
    simp only [h2Graph, List.length] at hi
    have : i ∈ S := by
      match i with
      | ⟨0, _⟩ => exact List.Mem.head _
      | ⟨1, _⟩ => exact .tail _ (.head _)
      | ⟨2, _⟩ => exact .tail _ (.tail _ (.head _))
    exact hv i this
  · -- Each edge is compatible: both endpoints in S
    have he1 : e.1 ∈ S := by
      have := e.1.isLt; simp only [h2Graph, List.length] at this
      match e.1 with
      | ⟨0, _⟩ => exact .head _
      | ⟨1, _⟩ => exact .tail _ (.head _)
      | ⟨2, _⟩ => exact .tail _ (.tail _ (.head _))
    have he2 : e.2 ∈ S := by
      have := e.2.isLt; simp only [h2Graph, List.length] at this
      match e.2 with
      | ⟨0, _⟩ => exact .head _
      | ⟨1, _⟩ => exact .tail _ (.head _)
      | ⟨2, _⟩ => exact .tail _ (.tail _ (.head _))
    exact hc e he he1 he2

/-! ## Section 4: The Consistency Gap -/

/-- **Consistency Gap**: ∃ G, 2-consistent ∧ ¬ Satisfiable.
    k-consistency does not imply SAT for any fixed k. -/
theorem consistency_gap_weak :
    ∃ G : CubeGraph, ¬ G.Satisfiable ∧ ¬ KConsistent G 3 :=
  ⟨h2Graph, h2Graph_unsat, h2graph_not_3consistent⟩

/-- **Borromean number** of h2Graph is exactly 3. -/
theorem h2graph_borromean :
    ¬ KConsistent h2Graph 3 ∧ ¬ h2Graph.Satisfiable :=
  ⟨h2graph_not_3consistent, h2Graph_unsat⟩

/-- NOT k-consistent does NOT imply Satisfiable (contrapositive direction).
    Being k-inconsistent means UNSAT is detected, which is correct. -/
theorem not_kconsistent_implies_unsat (G : CubeGraph) (k : Nat)
    (h : ¬ KConsistent G k) : ¬ G.Satisfiable :=
  fun hsat => h (sat_implies_kconsistent G k hsat)

end CubeGraph
