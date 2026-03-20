/-
  CubeGraph/InducedSubgraph.lean
  L-LOCAL-1 + L-LOCAL-2 + L-LOCAL-3: Induced subgraph, SAT inheritance, forest SAT.

  Main definitions and theorems:
  - inducedSubgraph: construct subgraph from a list of cube indices (L-LOCAL-1)
  - inducedSubgraph_length: subgraph cube count = keep.length
  - sat_of_induced_subgraph: SAT inherits to induced subgraphs (L-LOCAL-2)
  - ac_forest_subgraph_sat: forest subgraph of AC graph is SAT (L-LOCAL-3)

  See: experiments-ml/019_2026-03-13_topological-hardness/EXPANDING-ESCHER-RESULTS.md
  See: theory/research/MISSING-FORMALIZATIONS.md (#11: Locality Lower Bound)
-/

import CubeGraph.LeafTrimming

namespace CubeGraph

/-! ## Section 1: Position Lookup -/

/-- Find the first position of `v` in `l`. Returns `none` if not found. -/
private def findPos {n : Nat} : (l : List (Fin n)) → (v : Fin n) → Option (Fin l.length)
  | [], _ => none
  | x :: xs, v =>
    if x = v then some ⟨0, Nat.zero_lt_succ _⟩
    else match findPos xs v with
    | some ⟨i, hi⟩ => some ⟨i + 1, Nat.succ_lt_succ hi⟩
    | none => none

/-- If findPos returns some idx, then `l[idx.val] = v` (Nat-indexed). -/
private theorem findPos_spec {n : Nat} (l : List (Fin n)) (v : Fin n) (idx : Fin l.length)
    (h : findPos l v = some idx) : l[idx.val]'idx.isLt = v := by
  induction l with
  | nil => exact Fin.elim0 idx
  | cons x xs ih =>
    simp only [findPos] at h
    split at h
    · rename_i heq
      have hidx := (Option.some.inj h).symm; subst hidx
      exact heq
    · rename_i hne
      revert h
      match h_rec : findPos xs v with
      | some ⟨i, hi⟩ =>
        intro h
        have hidx := (Option.some.inj h).symm; subst hidx
        simp only [List.getElem_cons_succ]
        exact ih ⟨i, hi⟩ h_rec
      | none => intro h; contradiction

/-- If `v ∈ l`, then findPos returns some. -/
private theorem findPos_of_mem {n : Nat} (l : List (Fin n)) (v : Fin n) (hv : v ∈ l) :
    ∃ idx : Fin l.length, findPos l v = some idx := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp only [findPos]
    by_cases heq : x = v
    · exact ⟨⟨0, Nat.zero_lt_succ _⟩, by simp [if_pos heq]⟩
    · simp only [if_neg heq]
      have hv_xs : v ∈ xs := by
        rcases List.mem_cons.mp hv with rfl | h
        · exact absurd rfl heq
        · exact h
      obtain ⟨⟨i, hi⟩, hfi⟩ := ih hv_xs
      exact ⟨⟨i + 1, Nat.succ_lt_succ hi⟩, by rw [hfi]⟩

/-! ## Section 2: Nodup Injectivity -/

/-- In a nodup list, equal elements have equal indices. -/
private theorem nodup_getElem_inj {α : Type} [DecidableEq α] {l : List α}
    (hnd : l.Nodup) {i j : Nat} (hi : i < l.length) (hj : j < l.length)
    (heq : l[i]'hi = l[j]'hj) : i = j := by
  induction l generalizing i j with
  | nil => simp [List.length] at hi
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨ha_notin, ht_nodup⟩ := hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        exfalso
        have hj' : j' < t.length := by simp [List.length] at hj; omega
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact ha_notin (heq ▸ List.getElem_mem hj')
    | succ i' =>
      cases j with
      | zero =>
        exfalso
        have hi' : i' < t.length := by simp [List.length] at hi; omega
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact ha_notin (heq.symm ▸ List.getElem_mem hi')
      | succ j' =>
        have hi' : i' < t.length := by simp [List.length] at hi; omega
        have hj' : j' < t.length := by simp [List.length] at hj; omega
        simp only [List.getElem_cons_succ] at heq
        have := ih ht_nodup hi' hj' heq
        omega

/-! ## Section 3: Induced Subgraph Definition (L-LOCAL-1) -/

/-- Induced subgraph: keep only cubes at specified indices.
    Edges are filtered from G.edges, keeping only those with both endpoints in `keep`. -/
def inducedSubgraph (G : CubeGraph) (keep : List (Fin G.cubes.length))
    (h_nodup : keep.Nodup) : CubeGraph where
  cubes := keep.map (fun i => G.cubes[i])
  edges :=
    G.edges.filterMap fun e =>
      match findPos keep e.1, findPos keep e.2 with
      | some a, some b =>
        some (⟨a.val, by rw [List.length_map]; exact a.isLt⟩,
              ⟨b.val, by rw [List.length_map]; exact b.isLt⟩)
      | _, _ => none
  edges_valid := by
    intro ⟨ea, eb⟩ hmem
    simp only [List.mem_filterMap] at hmem
    obtain ⟨⟨e1, e2⟩, he_mem, h_fm⟩ := hmem
    generalize hfp1 : findPos keep e1 = fp1 at h_fm
    generalize hfp2 : findPos keep e2 = fp2 at h_fm
    cases fp1 with
    | none => contradiction
    | some a =>
      cases fp2 with
      | none => contradiction
      | some b =>
        simp at h_fm
        obtain ⟨ha, hb⟩ := h_fm
        subst ha; subst hb
        -- Goal: linkWeight (keep.map f)[⟨a.val,_⟩] (keep.map f)[⟨b.val,_⟩] > 0
        simp only [Fin.getElem_fin, List.getElem_map]
        -- Goal: linkWeight G.cubes[keep[a.val]] G.cubes[keep[b.val]] > 0
        rw [findPos_spec keep e1 a hfp1, findPos_spec keep e2 b hfp2]
        exact G.edges_valid ⟨e1, e2⟩ he_mem
  edges_complete := by
    intro i j hij hlw
    have hlen : (keep.map (fun idx => G.cubes[idx])).length = keep.length := List.length_map ..
    have hi_lt : i.val < keep.length := by rw [← hlen]; exact i.isLt
    have hj_lt : j.val < keep.length := by rw [← hlen]; exact j.isLt
    -- Original G indices
    let ki : Fin G.cubes.length := keep[i.val]'hi_lt
    let kj : Fin G.cubes.length := keep[j.val]'hj_lt
    -- ki ≠ kj from nodup + i ≠ j
    have hki_ne : ki ≠ kj := by
      intro heq
      apply hij; ext
      have := nodup_getElem_inj h_nodup hi_lt hj_lt heq
      omega
    -- linkWeight in G equals linkWeight in subgraph
    -- (keep.map f)[i] = f(keep[i]) bridging Fin↔Nat via @List.getElem_map
    have hci : (keep.map (fun idx => G.cubes[idx]))[i] = G.cubes[ki] :=
      @List.getElem_map _ _ (fun idx => G.cubes[idx]) keep i.val i.isLt
    have hcj : (keep.map (fun idx => G.cubes[idx]))[j] = G.cubes[kj] :=
      @List.getElem_map _ _ (fun idx => G.cubes[idx]) keep j.val j.isLt
    have hlw_G : Cube.linkWeight G.cubes[ki] G.cubes[kj] > 0 := by
      rw [← hci, ← hcj]; exact hlw
    -- G has an edge between ki and kj
    rcases G.edges_complete ki kj hki_ne hlw_G with hedge | hedge
    · -- (ki, kj) ∈ G.edges → (i, j) ∈ subgraph edges
      left; rw [List.mem_filterMap]
      refine ⟨(ki, kj), hedge, ?_⟩
      -- Get findPos results for ki and kj
      obtain ⟨fi, hfi⟩ := findPos_of_mem keep ki (List.getElem_mem hi_lt)
      obtain ⟨fj, hfj⟩ := findPos_of_mem keep kj (List.getElem_mem hj_lt)
      -- The found positions must equal i and j (by nodup)
      have hfi_eq : fi.val = i.val :=
        nodup_getElem_inj h_nodup fi.isLt hi_lt (findPos_spec keep ki fi hfi)
      have hfj_eq : fj.val = j.val :=
        nodup_getElem_inj h_nodup fj.isLt hj_lt (findPos_spec keep kj fj hfj)
      -- Reduce the filterMap function application
      dsimp only
      simp only [hfi, hfj]
      -- Goal: some (⟨fi.val, _⟩, ⟨fj.val, _⟩) = some (i, j)
      congr 1
      exact Prod.ext (Fin.ext hfi_eq) (Fin.ext hfj_eq)
    · -- (kj, ki) ∈ G.edges → (j, i) ∈ subgraph edges
      right; rw [List.mem_filterMap]
      refine ⟨(kj, ki), hedge, ?_⟩
      obtain ⟨fj, hfj⟩ := findPos_of_mem keep kj (List.getElem_mem hj_lt)
      obtain ⟨fi, hfi⟩ := findPos_of_mem keep ki (List.getElem_mem hi_lt)
      have hfj_eq : fj.val = j.val :=
        nodup_getElem_inj h_nodup fj.isLt hj_lt (findPos_spec keep kj fj hfj)
      have hfi_eq : fi.val = i.val :=
        nodup_getElem_inj h_nodup fi.isLt hi_lt (findPos_spec keep ki fi hfi)
      dsimp only
      simp only [hfj, hfi]
      congr 1
      exact Prod.ext (Fin.ext hfj_eq) (Fin.ext hfi_eq)

/-! ## Section 4: Subgraph Length -/

/-- The induced subgraph's cube list length equals keep length. -/
theorem inducedSubgraph_length (G : CubeGraph) (keep : List (Fin G.cubes.length))
    (h_nodup : keep.Nodup) :
    (G.inducedSubgraph keep h_nodup).cubes.length = keep.length := by
  simp [inducedSubgraph]

/-! ## Section 5: SAT Restriction to Subgraphs (L-LOCAL-2) -/

/-- Cube access in induced subgraph equals G cube at the kept index.
    Bridges the projection through `inducedSubgraph` using @List.getElem_map. -/
private theorem inducedSubgraph_cubes_eq (G : CubeGraph) (keep : List (Fin G.cubes.length))
    (h_nodup : keep.Nodup) (j : Fin (G.inducedSubgraph keep h_nodup).cubes.length) :
    (G.inducedSubgraph keep h_nodup).cubes[j] =
      G.cubes[keep[j.val]'(by rw [← inducedSubgraph_length G keep h_nodup]; exact j.isLt)] := by
  -- Use Nat-indexed show to avoid Fin type mismatch on the map expression
  show (keep.map (fun i => G.cubes[i]))[j.val]'j.isLt = _
  exact @List.getElem_map _ _ (fun i => G.cubes[i]) keep j.val j.isLt

/-- Restrict a gap selection from G to an induced subgraph,
    mapping each subgraph index j to the gap at keep[j] in G.
    Analog of `restrictSelection` (TreeSAT.lean) for induced subgraphs. -/
private def restrictToSubgraph (G : CubeGraph) (keep : List (Fin G.cubes.length))
    (h_nodup : keep.Nodup) (s : GapSelection G) :
    GapSelection (G.inducedSubgraph keep h_nodup) :=
  fun j => s (keep[j.val]'(by rw [← inducedSubgraph_length G keep h_nodup]; exact j.isLt))

/-- Restricted selection preserves validity: each gap is valid in its cube. -/
private theorem restrictToSubgraph_valid (G : CubeGraph) (keep : List (Fin G.cubes.length))
    (h_nodup : keep.Nodup) (s : GapSelection G) (hv : validSelection G s) :
    validSelection (G.inducedSubgraph keep h_nodup) (restrictToSubgraph G keep h_nodup s) := by
  intro j
  rw [inducedSubgraph_cubes_eq]
  exact hv _

/-- Restricted selection preserves compatibility: each edge in the subgraph
    comes from an edge in G, where the original selection is compatible.
    Proof pattern mirrors edges_valid from L-LOCAL-1. -/
private theorem restrictToSubgraph_compatible (G : CubeGraph) (keep : List (Fin G.cubes.length))
    (h_nodup : keep.Nodup) (s : GapSelection G) (hc : compatibleSelection G s) :
    compatibleSelection (G.inducedSubgraph keep h_nodup) (restrictToSubgraph G keep h_nodup s) := by
  intro ⟨ea, eb⟩ hmem
  simp only [inducedSubgraph, List.mem_filterMap] at hmem
  obtain ⟨⟨e1, e2⟩, he_mem, h_fm⟩ := hmem
  generalize hfp1 : findPos keep e1 = fp1 at h_fm
  generalize hfp2 : findPos keep e2 = fp2 at h_fm
  cases fp1 with
  | none => contradiction
  | some a =>
    cases fp2 with
    | none => contradiction
    | some b =>
      simp at h_fm
      obtain ⟨ha, hb⟩ := h_fm
      subst ha; subst hb
      -- Bridge cubes via helper, unfold selection, rewrite indices via findPos_spec
      rw [inducedSubgraph_cubes_eq, inducedSubgraph_cubes_eq]
      simp only [restrictToSubgraph]
      -- Use simp (not rw) because findPos_spec rewrites in dependent GetElem positions
      simp only [findPos_spec keep e1 a hfp1, findPos_spec keep e2 b hfp2]
      exact hc ⟨e1, e2⟩ he_mem

/-- **L-LOCAL-2**: Satisfiability inherits to induced subgraphs.
    If G is satisfiable, then any induced subgraph is also satisfiable.
    This is the subgraph analog of `sat_implies_removeNode_sat` (TreeSAT.lean). -/
theorem sat_of_induced_subgraph (G : CubeGraph) (keep : List (Fin G.cubes.length))
    (h_nodup : keep.Nodup) (h_sat : G.Satisfiable) :
    (G.inducedSubgraph keep h_nodup).Satisfiable := by
  obtain ⟨s, hv, hc⟩ := h_sat
  exact ⟨restrictToSubgraph G keep h_nodup s,
         restrictToSubgraph_valid G keep h_nodup s hv,
         restrictToSubgraph_compatible G keep h_nodup s hc⟩

/-! ## Section 6: Arc Consistency Inheritance -/

/-- Arc consistency inherits to induced subgraphs: if every edge in G
    satisfies bidirectional arc consistency, so does every edge in
    the induced subgraph.
    Proof: each subgraph edge came from a G edge via filterMap;
    the cubes at both endpoints are the same (via inducedSubgraph_cubes_eq). -/
private theorem inducedSubgraph_preserves_ac (G : CubeGraph)
    (keep : List (Fin G.cubes.length)) (h_nodup : keep.Nodup)
    (h_ac : AllArcConsistent G) :
    AllArcConsistent (G.inducedSubgraph keep h_nodup) := by
  intro ⟨ea, eb⟩ hmem
  simp only [inducedSubgraph, List.mem_filterMap] at hmem
  obtain ⟨⟨e1, e2⟩, he_mem, h_fm⟩ := hmem
  generalize hfp1 : findPos keep e1 = fp1 at h_fm
  generalize hfp2 : findPos keep e2 = fp2 at h_fm
  cases fp1 with
  | none => contradiction
  | some a =>
    cases fp2 with
    | none => contradiction
    | some b =>
      simp at h_fm
      obtain ⟨ha, hb⟩ := h_fm
      subst ha; subst hb
      -- Bridge cubes + reduce Prod projections + rewrite indices, all via simp
      simp only [inducedSubgraph_cubes_eq, findPos_spec keep e1 a hfp1,
                  findPos_spec keep e2 b hfp2]
      exact h_ac ⟨e1, e2⟩ he_mem

/-! ## Section 7: Forest Subgraph SAT (L-LOCAL-3) -/

/-- **L-LOCAL-3**: Any forest subgraph of an arc-consistent CubeGraph is satisfiable.
    Combines L-LOCAL-1 (induced subgraph), AC inheritance, and
    forest_arc_consistent_sat (TreeSAT.lean).

    At critical density, H² UNSAT implies AllArcConsistent (no arc-inconsistency
    survives — AC-3 terminates without domain wipeout). So every forest subgraph
    of an H²-UNSAT formula is SAT: the obstruction is purely global.

    Note: UNSATType2 (Hierarchy.lean) only requires ¬HasBlockedEdge, which is
    strictly weaker than AllArcConsistent. True H² (after AC-3 propagation)
    satisfies AllArcConsistent, so this theorem applies to all empirical H² cases. -/
theorem ac_forest_subgraph_sat (G : CubeGraph)
    (keep : List (Fin G.cubes.length))
    (h_nodup : keep.Nodup)
    (h_ac : AllArcConsistent G)
    (h_forest : IsForest (G.inducedSubgraph keep h_nodup)) :
    (G.inducedSubgraph keep h_nodup).Satisfiable :=
  forest_arc_consistent_sat _ h_forest
    (inducedSubgraph_preserves_ac G keep h_nodup h_ac)

end CubeGraph
