/-
  CubeGraph/TreeSAT.lean
  Infrastructure for tree satisfiability: base cases, arc consistency,
  index embedding, selection restriction and extension.

  Decomposition into small reusable lemmas for Phases 3-7.
  See theory/research/PHASE3A-TREESAT-PLAN.md for the full plan.
  See also: CubeGraph/MUS.lean (uses removeLeaf_sat_equiv, forest_arc_consistent_sat
    to prove MUS + AC → no leaves / not a forest)
-/

import CubeGraph.GapLemmas
import CubeGraph.Topology
import CubeGraph.PartB

namespace CubeGraph

/-! ## Section 1: Base Cases -/

/-- L1: Empty CubeGraph is satisfiable (vacuously). -/
theorem sat_of_empty : (CubeGraph.mk [] [] (fun _ he => nomatch he) (fun i _ _ _ => Fin.elim0 i)).Satisfiable :=
  ⟨Fin.elim0, fun i => Fin.elim0 i, fun _ he => nomatch he⟩

/-- L2: A single-cube CubeGraph (no edges) is always satisfiable.
    Any gap of the cube works as a valid selection. -/
theorem sat_of_single_cube (c : Cube) :
    (CubeGraph.mk [c] [] (fun _ he => nomatch he) (fun i j _hij => by
        have hi := i.isLt; have hj := j.isLt
        simp only [List.length] at hi hj; omega)).Satisfiable := by
  obtain ⟨v, _, hv⟩ := (Cube.gapCount_pos_iff c).mp
    (by have := Cube.gapCount_pos c; omega)
  refine ⟨fun _ => v, fun i => ?_, fun _ he => nomatch he⟩
  revert i; intro ⟨n, hn⟩
  cases n with
  | zero => exact hv
  | succ n => dsimp at hn; omega

/-! ## Section 2: Arc Consistency -/

/-- D1: Directional arc consistency from c₁ to c₂:
    every gap of c₂ has at least one compatible gap in c₁.
    This is STRICTLY STRONGER than non-zero transferOp.

    Counterexample for non-zero ≠ arc-consistent:
    C₁(gaps={0}) — C₂(gaps={0,3}) — C₃(gaps={3}), sharing vars {1,2}.
    All edges non-zero, but the tree is UNSAT. -/
def arcConsistentDir (c₁ c₂ : Cube) : Prop :=
  ∀ g₂ : Vertex, c₂.isGap g₂ = true →
    ∃ g₁ : Vertex, transferOp c₁ c₂ g₁ g₂ = true

/-- L3: Arc consistency implies the transfer operator is non-zero. -/
theorem arcConsistentDir_implies_nonzero {c₁ c₂ : Cube}
    (h : arcConsistentDir c₁ c₂) :
    ∃ g₁ g₂ : Vertex, transferOp c₁ c₂ g₁ g₂ = true := by
  obtain ⟨v, _, hv⟩ := (Cube.gapCount_pos_iff c₂).mp
    (by have := Cube.gapCount_pos c₂; omega)
  obtain ⟨g₁, hg₁⟩ := h v hv
  exact ⟨g₁, v, hg₁⟩

/-! ## Section 3: Index Embedding (eraseIdx ↔ original) -/

/-- removeNode.cubes is just eraseIdx. -/
@[simp] theorem removeNode_cubes (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) :
    (G.removeNode i h_len).cubes = G.cubes.eraseIdx i := rfl

/-- D2a: Map index in removeNode graph back to original graph index.
    j < i → j (unchanged), j ≥ i → j + 1 (shift past removed). -/
def removeNodeEmbed (G : CubeGraph) (i : Fin G.cubes.length) (h_len : G.cubes.length ≥ 2)
    (j : Fin (G.removeNode i h_len).cubes.length) : Fin G.cubes.length where
  val := if j.val < i.val then j.val else j.val + 1
  isLt := by
    have hj := j.isLt
    have hlen := removeNode_cubes_length G i h_len
    split <;> omega

/-- L5: The embedded index never equals the removed index. -/
theorem removeNodeEmbed_ne (G : CubeGraph) (i : Fin G.cubes.length) (h_len : G.cubes.length ≥ 2)
    (j : Fin (G.removeNode i h_len).cubes.length) :
    removeNodeEmbed G i h_len j ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [removeNodeEmbed, Fin.val_mk] at hv
  have hj := j.isLt
  have hlen := removeNode_cubes_length G i h_len
  split at hv <;> omega

/-- L6: Accessing original cubes at the embedded index gives the erased list element. -/
theorem removeNodeEmbed_cube (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2)
    (j : Fin (G.removeNode i h_len).cubes.length) :
    G.cubes[removeNodeEmbed G i h_len j] = (G.removeNode i h_len).cubes[j] := by
  simp only [removeNodeEmbed, removeNode_cubes, Fin.getElem_fin]
  by_cases hjlt : j.val < i.val
  · simp only [if_pos hjlt]
    exact (List.getElem_eraseIdx_of_lt j.isLt hjlt).symm
  · simp only [if_neg hjlt]
    exact (List.getElem_eraseIdx_of_ge j.isLt (by omega)).symm

/-- D2b: Map original graph index (≠ removed) to removeNode index.
    j < i → j (unchanged), j > i → j - 1 (shift down). -/
def removeNodeShrink (G : CubeGraph) (i : Fin G.cubes.length) (h_len : G.cubes.length ≥ 2)
    (j : Fin G.cubes.length) (hne : j ≠ i) :
    Fin (G.removeNode i h_len).cubes.length where
  val := if j.val < i.val then j.val else j.val - 1
  isLt := by
    rw [removeNode_cubes_length]
    have := j.isLt; have : j.val ≠ i.val := fun h => hne (Fin.ext h)
    split <;> omega

/-- L6b: The shrunk index accesses the same cube as the original. -/
theorem removeNodeShrink_cube (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) (j : Fin G.cubes.length) (hne : j ≠ i) :
    (G.removeNode i h_len).cubes[removeNodeShrink G i h_len j hne] = G.cubes[j] := by
  simp only [removeNodeShrink, removeNode_cubes, Fin.getElem_fin]
  have hne_val : j.val ≠ i.val := fun h => hne (Fin.ext h)
  have hlen : (G.cubes.eraseIdx ↑i).length = G.cubes.length - 1 := by
    rw [List.length_eraseIdx]; simp [i.isLt]
  by_cases hjlt : j.val < i.val
  · simp only [if_pos hjlt]
    exact List.getElem_eraseIdx_of_lt (by rw [hlen]; omega) hjlt
  · simp only [if_neg hjlt]
    rw [List.getElem_eraseIdx_of_ge (by rw [hlen]; omega) (by omega)]
    have : j.val - 1 + 1 = j.val := by omega
    simp only [this]

/-- L7a: Embed then shrink is the identity. -/
theorem removeNodeShrink_embed (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2)
    (j : Fin (G.removeNode i h_len).cubes.length) :
    removeNodeShrink G i h_len (removeNodeEmbed G i h_len j)
      (removeNodeEmbed_ne G i h_len j) = j := by
  simp only [removeNodeShrink, removeNodeEmbed, Fin.ext_iff, Fin.val_mk]
  have hj := j.isLt
  have hlen := removeNode_cubes_length G i h_len
  by_cases hlt : j.val < i.val
  · simp only [if_pos hlt]
  · simp only [if_neg hlt]; split <;> omega

/-- L7b: Shrink then embed is the identity. -/
theorem removeNodeEmbed_shrink (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2)
    (j : Fin G.cubes.length) (hne : j ≠ i) :
    removeNodeEmbed G i h_len (removeNodeShrink G i h_len j hne) = j := by
  simp only [removeNodeEmbed, removeNodeShrink, Fin.ext_iff, Fin.val_mk]
  have hne_val : j.val ≠ i.val := fun h => hne (Fin.ext h)
  by_cases hlt : j.val < i.val
  · simp only [if_pos hlt]
  · simp only [if_neg hlt]; split <;> omega

/-! ## Section 4: Edge Bridge Lemmas -/

/-- L8: Every edge in removeNode lifts to an edge in G via embed.
    If (a, b) is an edge of the subgraph, then (embed a, embed b) is an edge of G. -/
theorem removeNode_edge_lift (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2)
    (a b : Fin (G.removeNode i h_len).cubes.length)
    (he : (a, b) ∈ (G.removeNode i h_len).edges) :
    (removeNodeEmbed G i h_len a, removeNodeEmbed G i h_len b) ∈ G.edges := by
  unfold removeNode at he
  rw [List.mem_filterMap] at he
  obtain ⟨⟨e1, e2⟩, he_mem, h_fm⟩ := he
  split at h_fm
  · simp at h_fm
  · next hne1 =>
    split at h_fm
    · simp at h_fm
    · next hne2 =>
      simp at h_fm
      obtain ⟨ha, hb⟩ := h_fm
      -- ha : inline_shrink(e1) = a, hb : inline_shrink(e2) = b
      -- Show a = removeNodeShrink e1, then use embed ∘ shrink = id
      have ha' : a = removeNodeShrink G i h_len e1 hne1 := by
        rw [← ha]; exact Fin.ext rfl
      have hb' : b = removeNodeShrink G i h_len e2 hne2 := by
        rw [← hb]; exact Fin.ext rfl
      rw [ha', hb', removeNodeEmbed_shrink, removeNodeEmbed_shrink]
      exact he_mem

/-- L9: An edge in G not touching node i pushes down to removeNode via shrink. -/
theorem removeNode_edge_push (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2)
    (e1 e2 : Fin G.cubes.length)
    (he : (e1, e2) ∈ G.edges) (hne1 : e1 ≠ i) (hne2 : e2 ≠ i) :
    (removeNodeShrink G i h_len e1 hne1,
     removeNodeShrink G i h_len e2 hne2)
    ∈ (G.removeNode i h_len).edges := by
  unfold removeNode
  rw [List.mem_filterMap]
  refine ⟨(e1, e2), he, ?_⟩
  simp only [dif_neg (show ¬(e1 = i) from hne1), dif_neg (show ¬(e2 = i) from hne2)]
  congr 1

/-! ## Section 5: Selection Restriction (G.SAT → removeNode.SAT) -/

/-- D3: Restrict a gap selection from G to the subgraph removeNode i,
    by composing with embed. -/
def restrictSelection (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) (s : GapSelection G) :
    GapSelection (G.removeNode i h_len) :=
  fun j => s (removeNodeEmbed G i h_len j)

/-- L10: Restriction preserves validity (each selection is a gap). -/
theorem restrictSelection_valid (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) (s : GapSelection G)
    (hv : validSelection G s) :
    validSelection (G.removeNode i h_len) (restrictSelection G i h_len s) := by
  intro j
  unfold restrictSelection
  rw [← removeNodeEmbed_cube G i h_len j]
  exact hv (removeNodeEmbed G i h_len j)

/-- L11: Restriction preserves compatibility (edge transfer operators agree). -/
theorem restrictSelection_compatible (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) (s : GapSelection G)
    (hc : compatibleSelection G s) :
    compatibleSelection (G.removeNode i h_len) (restrictSelection G i h_len s) := by
  intro e he
  unfold restrictSelection
  -- Lift the edge to G
  have h_lift := removeNode_edge_lift G i h_len e.1 e.2 he
  -- Get compatibility from G
  have h_compat := hc (removeNodeEmbed G i h_len e.1, removeNodeEmbed G i h_len e.2) h_lift
  -- Rewrite cubes to match
  rw [← removeNodeEmbed_cube G i h_len e.1, ← removeNodeEmbed_cube G i h_len e.2]
  exact h_compat

/-- L12: Satisfiability restricts to subgraphs. -/
theorem sat_implies_removeNode_sat (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) (h : G.Satisfiable) :
    (G.removeNode i h_len).Satisfiable := by
  obtain ⟨s, hv, hc⟩ := h
  exact ⟨restrictSelection G i h_len s,
         restrictSelection_valid G i h_len s hv,
         restrictSelection_compatible G i h_len s hc⟩

/-! ## Section 6: Selection Extension (removeNode.SAT + gap → G.SAT mechanism) -/

/-- D4: Extend a subgraph selection to the full graph by adding a gap for node i.
    At node i, use g_i. At other nodes, use the subgraph selection via shrink. -/
def extendSelection (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2)
    (s_sub : GapSelection (G.removeNode i h_len))
    (g_i : Vertex) : GapSelection G :=
  fun j => if h : j = i then g_i
           else s_sub (removeNodeShrink G i h_len j h)

/-- L13: Extended selection is valid if the subgraph selection is valid
    and g_i is a gap of cube i. -/
theorem extendSelection_valid (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2)
    (s_sub : GapSelection (G.removeNode i h_len))
    (g_i : Vertex)
    (hv : validSelection (G.removeNode i h_len) s_sub)
    (hg : (G.cubes[i]).isGap g_i = true) :
    validSelection G (extendSelection G i h_len s_sub g_i) := by
  intro j
  simp only [extendSelection]
  by_cases hj : j = i
  · subst hj; simp; exact hg
  · simp only [dif_neg hj]
    rw [← removeNodeShrink_cube G i h_len j hj]
    exact hv _

/-- L14: Extension preserves compatibility on edges not touching node i. -/
theorem extendSelection_compatible_nonleaf (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2)
    (s_sub : GapSelection (G.removeNode i h_len)) (g_i : Vertex)
    (hc : compatibleSelection (G.removeNode i h_len) s_sub)
    (e1 e2 : Fin G.cubes.length)
    (he : (e1, e2) ∈ G.edges) (hne1 : e1 ≠ i) (hne2 : e2 ≠ i) :
    transferOp (G.cubes[e1]) (G.cubes[e2])
      (extendSelection G i h_len s_sub g_i e1)
      (extendSelection G i h_len s_sub g_i e2) = true := by
  simp only [extendSelection, dif_neg hne1, dif_neg hne2]
  -- Push the edge down to removeNode
  have h_push := removeNode_edge_push G i h_len e1 e2 he hne1 hne2
  -- Get compatibility from the subgraph selection
  have h_compat := hc _ h_push
  -- Rewrite cubes to match
  rw [removeNodeShrink_cube G i h_len e1 hne1,
      removeNodeShrink_cube G i h_len e2 hne2] at h_compat
  exact h_compat

/-! ## Section 7: Acyclicity Helpers -/

/-- L15: removeNode can only decrease edge count (filterMap ≤ original). -/
theorem removeNode_edges_le (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) :
    (G.removeNode i h_len).edges.length ≤ G.edges.length := by
  simp only [removeNode]
  exact List.length_filterMap_le _ _

/-- L17: A node with degree ≥ 1 has at least one incident edge in G.edges. -/
theorem exists_incident_edge_of_degree_pos (G : CubeGraph) (i : Fin G.cubes.length)
    (h : G.degree i ≥ 1) :
    ∃ e ∈ G.edges, e.1 = i ∨ e.2 = i := by
  rw [degree_eq_incidentEdges] at h
  -- incidentEdges is nonempty
  have ⟨e, he⟩ : ∃ e, e ∈ G.incidentEdges i := by
    cases h_eq : G.incidentEdges i with
    | nil => simp [h_eq] at h
    | cons x xs => exact ⟨x, .head xs⟩
  exact ⟨e, (mem_incidentEdges_iff G i e).mp he⟩

/-- Helper: filterMap that drops at least one element produces strictly fewer results. -/
private theorem filterMap_length_lt {α β : Type} (f : α → Option β) (l : List α)
    (x : α) (hx : x ∈ l) (hfx : f x = none) :
    (l.filterMap f).length < l.length := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    simp only [List.length_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · -- a = x, filterMap drops it
      have : (x :: t).filterMap f = t.filterMap f := by simp [hfx]
      rw [this]; exact Nat.lt_succ_of_le (List.length_filterMap_le f t)
    · -- x ∈ t, use induction hypothesis
      have ih' := ih h
      simp only [List.filterMap_cons]
      split
      · exact Nat.lt_succ_of_lt ih'
      · simp only [List.length_cons]; exact Nat.succ_lt_succ ih'

/-- L16: removeNode preserves acyclicity when the removed node has degree ≥ 1.
    Degree ≥ 1 ensures at least one edge is dropped by filterMap. -/
theorem removeNode_isAcyclic_of_degree_pos (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) (h_ac : G.isAcyclic)
    (h_deg : G.degree i ≥ 1) :
    (G.removeNode i h_len).isAcyclic := by
  unfold isAcyclic at h_ac ⊢
  have h_cubes := removeNode_cubes_length G i h_len
  -- edges' < edges because filterMap drops ≥ 1 edge (touching i)
  obtain ⟨e, he_mem, he_touch⟩ := exists_incident_edge_of_degree_pos G i h_deg
  have h_drop : (G.removeNode i h_len).edges.length < G.edges.length := by
    simp only [removeNode]
    apply filterMap_length_lt _ _ e he_mem
    -- The edge e touches i, so filterMap maps it to none
    split  -- first dite: e.1 = i?
    · rfl
    · next h1 =>
      split  -- second dite: e.2 = i?
      · rfl
      · next h2 =>
        exfalso
        cases he_touch with
        | inl h => exact h1 h
        | inr h => exact h2 h
  omega

/-! ## Section 8: Arc Consistency Preservation -/

/-- R13: removeNode preserves arc consistency on all remaining edges.
    If every edge in G satisfies bidirectional arc consistency, then every edge
    in the subgraph (G.removeNode i) also satisfies bidirectional arc consistency.

    CRITICAL for Phase 5: without this, the tree induction cannot propagate
    arc consistency to the subgraph after removing a leaf. -/
theorem removeNode_preserves_arcConsistent (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2)
    (h_ac : ∀ e ∈ G.edges,
      arcConsistentDir (G.cubes[e.1]) (G.cubes[e.2]) ∧
      arcConsistentDir (G.cubes[e.2]) (G.cubes[e.1]))
    (e : Fin (G.removeNode i h_len).cubes.length ×
         Fin (G.removeNode i h_len).cubes.length)
    (he : e ∈ (G.removeNode i h_len).edges) :
    arcConsistentDir ((G.removeNode i h_len).cubes[e.1])
                     ((G.removeNode i h_len).cubes[e.2]) ∧
    arcConsistentDir ((G.removeNode i h_len).cubes[e.2])
                     ((G.removeNode i h_len).cubes[e.1]) := by
  -- Lift the subgraph edge to an edge in G
  have h_lift := removeNode_edge_lift G i h_len e.1 e.2 he
  -- Get arc consistency on the lifted edge
  obtain ⟨h_fwd, h_bwd⟩ := h_ac _ h_lift
  -- Reduce pair projections: (embed e.1, embed e.2).fst → embed e.1
  dsimp only at h_fwd h_bwd
  -- Rewrite cubes: G.cubes[embed j] = removeNode.cubes[j]
  rw [removeNodeEmbed_cube G i h_len e.1, removeNodeEmbed_cube G i h_len e.2] at h_fwd h_bwd
  exact ⟨h_fwd, h_bwd⟩

/-! ## Section 9: Path Projection and Connectivity Preservation -/

/-- Key lemma: A path between two non-leaf nodes can be projected to the subgraph
    obtained by removing a degree-1 leaf. If the path goes through the leaf, it
    must bounce back (since the leaf has only one neighbor), and we shortcut. -/
def graphPath_avoid_leaf (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) (_h_deg : G.degree i = 1)
    (j : Fin G.cubes.length) (hj : G.neighbors i = [j])
    (a b : Fin G.cubes.length) (ha : a ≠ i) (hb : b ≠ i)
    (h : GraphPath G a b) :
    GraphPath (G.removeNode i h_len)
      (removeNodeShrink G i h_len a ha) (removeNodeShrink G i h_len b hb) := by
  -- Strong induction via Nat bound on pathDepth, generalizing both endpoints
  suffices ∀ (n : Nat) (a b : Fin G.cubes.length) (ha : a ≠ i) (hb : b ≠ i)
      (h : GraphPath G a b) (_ : pathDepth h ≤ n),
      GraphPath (G.removeNode i h_len)
        (removeNodeShrink G i h_len a ha) (removeNodeShrink G i h_len b hb) by
    exact this (pathDepth h) a b ha hb h Nat.le.refl
  intro n
  induction n with
  | zero =>
    intro a b ha hb h hd
    cases h with
    | trivial => exact .trivial
    | step _ _ => simp [pathDepth] at hd
  | succ k ih =>
    intro a b ha hb h hd
    cases h with
    | trivial => exact .trivial
    | @step _ next _ edge sub =>
      simp [pathDepth] at hd
      by_cases hne : next = i
      · -- next = i: the path goes through the leaf, must bounce back
        -- sub : GraphPath G next b, hne : next = i
        -- Since next = i and b ≠ i, we have next ≠ b
        have hne_nb : next ≠ b := by
          intro heq; exact hb (by rw [← heq, hne])
        -- Extract the first step of sub (non-trivial since next ≠ b)
        have step := graphPath_step_of_ne sub hne_nb
        -- Both a and step.next are neighbors of i (= next); since degree = 1, both equal j
        have h_a_nbr : a ∈ G.neighbors i := by
          have edge' : (a, i) ∈ G.edges ∨ (i, a) ∈ G.edges := hne ▸ edge
          rcases edge' with h | h
          · exact mem_neighbors_of_edge G i a (.inl h)
          · exact mem_neighbors_of_edge G i a (.inr h)
        have h_n2_nbr : step.next ∈ G.neighbors i := by
          have edge₂' : (i, step.next) ∈ G.edges ∨ (step.next, i) ∈ G.edges :=
            hne ▸ step.edge
          rcases edge₂' with h | h
          · exact mem_neighbors_of_edge G i step.next (.inr h)
          · exact mem_neighbors_of_edge G i step.next (.inl h)
        rw [hj] at h_a_nbr h_n2_nbr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h_a_nbr h_n2_nbr
        -- a = j = step.next
        have h_eq : step.next = a := h_n2_nbr.symm ▸ h_a_nbr.symm ▸ rfl
        -- Apply IH directly to step.sub (avoids pathDepth transport issues)
        have ha₂ : step.next ≠ i := by rw [h_eq]; exact ha
        have h1 : pathDepth step.sub + 1 ≤ pathDepth sub := step.depth_bound
        have h2 : pathDepth sub ≤ k := hd
        have result := ih step.next b ha₂ hb step.sub (by omega)
        -- Transport result from shrink step.next to shrink a
        exact h_eq ▸ result
      · -- next ≠ i: project the edge to the subgraph and recurse
        have h_edge : (removeNodeShrink G i h_len a ha,
                       removeNodeShrink G i h_len next hne) ∈
            (G.removeNode i h_len).edges ∨
            (removeNodeShrink G i h_len next hne,
             removeNodeShrink G i h_len a ha) ∈
            (G.removeNode i h_len).edges := by
          rcases edge with h | h
          · exact .inl (removeNode_edge_push G i h_len a next h ha hne)
          · exact .inr (removeNode_edge_push G i h_len next a h hne ha)
        exact .step h_edge (ih next b hne hb sub (by omega))

/-- Removing a degree-1 leaf from a connected graph preserves connectivity. -/
theorem removeNode_leaf_isConnected (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) (h_conn : G.isConnected)
    (h_deg : G.degree i = 1) :
    (G.removeNode i h_len).isConnected := by
  obtain ⟨j, hj⟩ := leaf_unique_neighbor G i h_deg
  intro a b
  have hpath := Classical.choice (h_conn (removeNodeEmbed G i h_len a)
                                         (removeNodeEmbed G i h_len b))
  have ha := removeNodeEmbed_ne G i h_len a
  have hb := removeNodeEmbed_ne G i h_len b
  have h_proj := graphPath_avoid_leaf G i h_len h_deg j hj _ _ ha hb hpath
  rw [removeNodeShrink_embed, removeNodeShrink_embed] at h_proj
  exact ⟨h_proj⟩

/-! ## Section 10: Satisfiability with No Edges -/

/-- T1: A CubeGraph with no edges is satisfiable.
    Each cube has ≥ 1 gap (gapCount_pos), pick one per cube. -/
theorem sat_of_no_edges (G : CubeGraph) (h : G.edges = []) :
    G.Satisfiable := by
  refine ⟨fun i => ((Cube.gapCount_pos_iff _).mp
    (by have := Cube.gapCount_pos (G.cubes[i]); omega)).choose,
    fun i => ((Cube.gapCount_pos_iff _).mp
      (by have := Cube.gapCount_pos (G.cubes[i]); omega)).choose_spec.2,
    fun e he => ?_⟩
  rw [h] at he; simp at he

/-! ## Section 11: Neighbor-Edge Infrastructure -/

/-- T3: If j is a neighbor of i, there exists an edge between them in G.edges.
    Wrapper around edge_of_mem_neighbors with existential packaging. -/
theorem neighbor_has_edge (G : CubeGraph) (i j : Fin G.cubes.length)
    (h : j ∈ G.neighbors i) :
    ∃ e ∈ G.edges, (e.1 = i ∧ e.2 = j) ∨ (e.1 = j ∧ e.2 = i) := by
  have h_edge := edge_of_mem_neighbors G i j h
  rcases h_edge with h | h
  · exact ⟨(i, j), h, .inl ⟨rfl, rfl⟩⟩
  · exact ⟨(j, i), h, .inr ⟨rfl, rfl⟩⟩

/-- T4: Extract arcConsistentDir in direction i→j from the full hypothesis.
    Works regardless of edge orientation (i,j) or (j,i). -/
theorem arc_consistent_of_edge (G : CubeGraph)
    (h_ac : ∀ e ∈ G.edges,
      arcConsistentDir (G.cubes[e.1]) (G.cubes[e.2]) ∧
      arcConsistentDir (G.cubes[e.2]) (G.cubes[e.1]))
    (i j : Fin G.cubes.length)
    (he : (i, j) ∈ G.edges ∨ (j, i) ∈ G.edges) :
    arcConsistentDir (G.cubes[i]) (G.cubes[j]) := by
  rcases he with h | h
  · exact (h_ac _ h).1
  · exact (h_ac _ h).2

/-- T5: All edges incident to a degree-1 node connect to the same unique neighbor.
    If degree i = 1 and edge e touches i, then the other endpoint equals
    the unique neighbor j. -/
theorem degree_one_unique_edge (G : CubeGraph) (i : Fin G.cubes.length)
    (j : Fin G.cubes.length) (hj : G.neighbors i = [j])
    (e : Fin G.cubes.length × Fin G.cubes.length)
    (he : e ∈ G.edges) (htouch : e.1 = i ∨ e.2 = i) :
    (e.1 = i ∧ e.2 = j) ∨ (e.1 = j ∧ e.2 = i) := by
  -- The other endpoint must be a neighbor of i, hence = j
  have h_other_nbr : ∀ k, (e.1 = i ∧ e.2 = k) ∨ (e.1 = k ∧ e.2 = i) →
      k ∈ G.neighbors i := by
    intro k hk
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact mem_neighbors_of_edge G i k (by rw [← h1, ← h2]; exact .inr he)
    · exact mem_neighbors_of_edge G i k (by rw [← h1, ← h2]; exact .inl he)
  rcases htouch with h1 | h2
  · -- e.1 = i
    have : e.2 ∈ G.neighbors i := h_other_nbr e.2 (.inl ⟨h1, rfl⟩)
    rw [hj] at this; simp at this
    exact .inl ⟨h1, this⟩
  · -- e.2 = i
    have : e.1 ∈ G.neighbors i := h_other_nbr e.1 (.inr ⟨rfl, h2⟩)
    rw [hj] at this; simp at this
    exact .inr ⟨this, h2⟩

/-! ## Section 12: Forest + Arc-Consistent → SAT (split into lemmas) -/

/-- Element-level transpose for transferOp.
    (Duplicated from RankTheory.lean to avoid circular import.) -/
private theorem transferOp_transpose_elem' (c₁ c₂ : Cube) (g₁ g₂ : Vertex) :
    transferOp c₁ c₂ g₁ g₂ = transferOp c₂ c₁ g₂ g₁ := by
  have := congrFun (congrFun (transferOp_transpose c₁ c₂) g₁) g₂
  simp only [BoolMat.transpose_apply] at this
  exact this

/-- Given arc consistency from c₁ to c₂ and a gap g₂ in c₂,
    there exists a gap g₁ in c₁ compatible via transferOp.
    (Duplicated from RankTheory.lean to avoid circular import.) -/
private theorem leaf_has_compatible_gap' (c₁ c₂ : Cube) (g₂ : Vertex)
    (h_ac : arcConsistentDir c₁ c₂) (hg₂ : c₂.isGap g₂ = true) :
    ∃ g₁ : Vertex, c₁.isGap g₁ = true ∧ transferOp c₁ c₂ g₁ g₂ = true := by
  obtain ⟨g₁, hg₁⟩ := h_ac g₂ hg₂
  exact ⟨g₁, (transferOp_implies_gaps c₁ c₂ g₁ g₂ hg₁).1, hg₁⟩

/-- L-FWD: Compatibility on edge (i, j) via extended selection.
    Uses htrans directly since extendSelection maps i→g_i and j→s_sub(shrink j). -/
private theorem extend_compat_fwd (G : CubeGraph) (i j : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) (hji : j ≠ i)
    (s_sub : GapSelection (G.removeNode i h_len)) (g_i : Vertex)
    (htrans : transferOp (G.cubes[i]) (G.cubes[j]) g_i
      (s_sub (removeNodeShrink G i h_len j hji)) = true) :
    transferOp (G.cubes[i]) (G.cubes[j])
      (extendSelection G i h_len s_sub g_i i)
      (extendSelection G i h_len s_sub g_i j) = true := by
  simp only [extendSelection, dif_neg hji]
  exact htrans

/-- L-REV: Compatibility on edge (j, i) via extended selection + transpose.
    Uses htrans via transferOp_transpose_elem'. -/
private theorem extend_compat_rev (G : CubeGraph) (i j : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) (hji : j ≠ i)
    (s_sub : GapSelection (G.removeNode i h_len)) (g_i : Vertex)
    (htrans : transferOp (G.cubes[i]) (G.cubes[j]) g_i
      (s_sub (removeNodeShrink G i h_len j hji)) = true) :
    transferOp (G.cubes[j]) (G.cubes[i])
      (extendSelection G i h_len s_sub g_i j)
      (extendSelection G i h_len s_sub g_i i) = true := by
  simp only [extendSelection, dif_neg hji]
  rw [transferOp_transpose_elem']
  exact htrans

/-- L-TOUCH: Compatibility on ANY edge of G, for the normal case (j ≠ i).
    Edges touching i are handled via degree_one_unique_edge → fwd/rev.
    Edges not touching i are handled via extendSelection_compatible_nonleaf. -/
private theorem peel_compat_at_leaf (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2)
    (j : Fin G.cubes.length) (hj : G.neighbors i = [j]) (hji : j ≠ i)
    (s_sub : GapSelection (G.removeNode i h_len)) (g_i : Vertex)
    (hc_sub : compatibleSelection (G.removeNode i h_len) s_sub)
    (htrans : transferOp (G.cubes[i]) (G.cubes[j]) g_i
      (s_sub (removeNodeShrink G i h_len j hji)) = true)
    (e : Fin G.cubes.length × Fin G.cubes.length) (he : e ∈ G.edges) :
    transferOp (G.cubes[e.1]) (G.cubes[e.2])
      (extendSelection G i h_len s_sub g_i e.1)
      (extendSelection G i h_len s_sub g_i e.2) = true := by
  by_cases h_touch : e.1 = i ∨ e.2 = i
  · -- Edge touches i: must be (i, j) or (j, i)
    have h_form := degree_one_unique_edge G i j hj e he h_touch
    rcases h_form with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- e.1 = i, e.2 = j
      simp only [h1, h2]
      exact extend_compat_fwd G i j h_len hji s_sub g_i htrans
    · -- e.1 = j, e.2 = i
      simp only [h1, h2]
      exact extend_compat_rev G i j h_len hji s_sub g_i htrans
  · -- Edge doesn't touch i
    have hne1 : e.1 ≠ i := fun h => h_touch (.inl h)
    have hne2 : e.2 ≠ i := fun h => h_touch (.inr h)
    exact extendSelection_compatible_nonleaf G i h_len s_sub g_i
      hc_sub e.1 e.2 he hne1 hne2

/-- L-SELF: Compatibility on ANY edge of G, for the self-loop case (j = i).
    All edges touching i are self-loops (i, i), compatible via transferOp_self. -/
private theorem peel_compat_selfloop (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2)
    (j : Fin G.cubes.length) (hj : G.neighbors i = [j]) (hji : j = i)
    (s_sub : GapSelection (G.removeNode i h_len)) (g_i : Vertex)
    (hg_i : (G.cubes[i]).isGap g_i = true)
    (hc_sub : compatibleSelection (G.removeNode i h_len) s_sub)
    (e : Fin G.cubes.length × Fin G.cubes.length) (he : e ∈ G.edges) :
    transferOp (G.cubes[e.1]) (G.cubes[e.2])
      (extendSelection G i h_len s_sub g_i e.1)
      (extendSelection G i h_len s_sub g_i e.2) = true := by
  -- Rewrite j → i in the neighbor list (don't use subst — it eliminates i)
  have hj' : G.neighbors i = [i] := hji ▸ hj
  by_cases h_touch : e.1 = i ∨ e.2 = i
  · -- Edge touches i: both forms give e = (i, i)
    have h_form := degree_one_unique_edge G i i hj' e he h_touch
    rcases h_form with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> {
      simp only [h1, h2, extendSelection, dite_true]
      unfold transferOp
      simp; exact hg_i
    }
  · have hne1 : e.1 ≠ i := fun h => h_touch (.inl h)
    have hne2 : e.2 ≠ i := fun h => h_touch (.inr h)
    exact extendSelection_compatible_nonleaf G i h_len s_sub g_i
      hc_sub e.1 e.2 he hne1 hne2

/-- **T1-C (Phase 5)**: A forest CubeGraph with bidirectional arc consistency
    on all edges is satisfiable.

    Proof by well-founded recursion on IsForest:
    - leaf_free: no edges → pick any gap per cube
    - peel: remove degree-1 leaf → recurse → extend via arc consistency -/
theorem forest_arc_consistent_sat (G : CubeGraph)
    (h_forest : IsForest G)
    (h_ac : ∀ e ∈ G.edges,
      arcConsistentDir (G.cubes[e.1]) (G.cubes[e.2]) ∧
      arcConsistentDir (G.cubes[e.2]) (G.cubes[e.1])) :
    G.Satisfiable := by
  cases h_forest with
  | leaf_free h_edges =>
    exact sat_of_no_edges G h_edges
  | @peel _ i h_len h_deg h_forest_sub =>
    -- Step 1: Subgraph arc consistent + recursive SAT
    have h_ac_sub := removeNode_preserves_arcConsistent G i h_len h_ac
    obtain ⟨s_sub, hv_sub, hc_sub⟩ :=
      forest_arc_consistent_sat (G.removeNode i h_len) h_forest_sub h_ac_sub
    -- Step 2: Unique neighbor j
    obtain ⟨j, hj⟩ := leaf_unique_neighbor G i h_deg
    -- Step 3: Case split j = i vs j ≠ i
    by_cases hji : j = i
    · -- Self-loop: pick any gap
      obtain ⟨g_i, _, hg_i⟩ := (Cube.gapCount_pos_iff (G.cubes[i])).mp
        (by have := Cube.gapCount_pos (G.cubes[i]); omega)
      exact ⟨extendSelection G i h_len s_sub g_i,
             extendSelection_valid G i h_len s_sub g_i hv_sub hg_i,
             peel_compat_selfloop G i h_len j hj hji s_sub g_i hg_i hc_sub⟩
    · -- Normal: find compatible g_i via arc consistency i→j
      have hj_mem : j ∈ G.neighbors i := by rw [hj]; simp
      have h_edge_ij := edge_of_mem_neighbors G i j hj_mem
      have h_ac_ij : arcConsistentDir (G.cubes[i]) (G.cubes[j]) := by
        rcases h_edge_ij with h | h
        · exact (h_ac _ h).1
        · exact (h_ac _ h).2
      have hg_j : (G.cubes[j]).isGap
          (s_sub (removeNodeShrink G i h_len j hji)) = true := by
        rw [← removeNodeShrink_cube G i h_len j hji]; exact hv_sub _
      obtain ⟨g_i, hg_i, htrans⟩ :=
        leaf_has_compatible_gap' (G.cubes[i]) (G.cubes[j])
          (s_sub (removeNodeShrink G i h_len j hji)) h_ac_ij hg_j
      exact ⟨extendSelection G i h_len s_sub g_i,
             extendSelection_valid G i h_len s_sub g_i hv_sub hg_i,
             peel_compat_at_leaf G i h_len j hj hji s_sub g_i hc_sub htrans⟩
termination_by G.cubes.length
decreasing_by
  have := removeNode_cubes_length G i h_len
  omega

/-! ## Section 13: Single Leaf Backward Direction -/

/-- T2-A-STEP: If a leaf is removed, the subgraph is SAT, and G has
    bidirectional AC on all edges, then G is SAT.
    Degree 0: no edges touch i → any gap works.
    Degree 1: AC → compatible gap exists via peel_compat helpers. -/
theorem removeLeaf_sat_of_removeNode_sat (G : CubeGraph)
    (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) (h_leaf : G.isLeaf i)
    (h_ac : ∀ e ∈ G.edges,
      arcConsistentDir (G.cubes[e.1]) (G.cubes[e.2]) ∧
      arcConsistentDir (G.cubes[e.2]) (G.cubes[e.1]))
    (h_sub_sat : (G.removeNode i h_len).Satisfiable) :
    G.Satisfiable := by
  obtain ⟨s_sub, hv_sub, hc_sub⟩ := h_sub_sat
  -- isLeaf means degree ≤ 1
  unfold isLeaf at h_leaf
  by_cases h_deg0 : G.degree i = 0
  · -- Degree 0: no edge touches i, any gap works
    have h_inc_len : (G.incidentEdges i).length = 0 := by
      rw [← degree_eq_incidentEdges]; exact h_deg0
    have h_inc_empty : G.incidentEdges i = [] :=
      List.eq_nil_of_length_eq_zero h_inc_len
    have h_no_touch : ∀ e ∈ G.edges, e.1 ≠ i ∧ e.2 ≠ i := by
      intro e he
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hmem := (mem_incidentEdges_iff G i e).mpr ⟨he, .inl h⟩
        rw [h_inc_empty] at hmem; simp at hmem
      · have hmem := (mem_incidentEdges_iff G i e).mpr ⟨he, .inr h⟩
        rw [h_inc_empty] at hmem; simp at hmem
    obtain ⟨g_i, _, hg_i⟩ := (Cube.gapCount_pos_iff (G.cubes[i])).mp
      (by have := Cube.gapCount_pos (G.cubes[i]); omega)
    exact ⟨extendSelection G i h_len s_sub g_i,
           extendSelection_valid G i h_len s_sub g_i hv_sub hg_i,
           fun e he => extendSelection_compatible_nonleaf G i h_len s_sub g_i
             hc_sub e.1 e.2 he (h_no_touch e he).1 (h_no_touch e he).2⟩
  · -- Degree 1: same pattern as forest_arc_consistent_sat peel case
    have h_deg1 : G.degree i = 1 := by omega
    obtain ⟨j, hj⟩ := leaf_unique_neighbor G i h_deg1
    by_cases hji : j = i
    · -- Self-loop: pick any gap
      obtain ⟨g_i, _, hg_i⟩ := (Cube.gapCount_pos_iff (G.cubes[i])).mp
        (by have := Cube.gapCount_pos (G.cubes[i]); omega)
      exact ⟨extendSelection G i h_len s_sub g_i,
             extendSelection_valid G i h_len s_sub g_i hv_sub hg_i,
             peel_compat_selfloop G i h_len j hj hji s_sub g_i hg_i hc_sub⟩
    · -- Normal: find compatible g_i via arc consistency i→j
      have hj_mem : j ∈ G.neighbors i := by rw [hj]; simp
      have h_edge_ij := edge_of_mem_neighbors G i j hj_mem
      have h_ac_ij : arcConsistentDir (G.cubes[i]) (G.cubes[j]) := by
        rcases h_edge_ij with h | h
        · exact (h_ac _ h).1
        · exact (h_ac _ h).2
      have hg_j : (G.cubes[j]).isGap
          (s_sub (removeNodeShrink G i h_len j hji)) = true := by
        rw [← removeNodeShrink_cube G i h_len j hji]; exact hv_sub _
      obtain ⟨g_i, hg_i, htrans⟩ :=
        leaf_has_compatible_gap' (G.cubes[i]) (G.cubes[j])
          (s_sub (removeNodeShrink G i h_len j hji)) h_ac_ij hg_j
      exact ⟨extendSelection G i h_len s_sub g_i,
             extendSelection_valid G i h_len s_sub g_i hv_sub hg_i,
             peel_compat_at_leaf G i h_len j hj hji s_sub g_i hc_sub htrans⟩

/-- Single-step leaf SAT equivalence under AC. -/
theorem removeLeaf_sat_equiv (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) (h_leaf : G.isLeaf i)
    (h_ac : ∀ e ∈ G.edges,
      arcConsistentDir (G.cubes[e.1]) (G.cubes[e.2]) ∧
      arcConsistentDir (G.cubes[e.2]) (G.cubes[e.1])) :
    G.Satisfiable ↔ (G.removeNode i h_len).Satisfiable :=
  ⟨sat_implies_removeNode_sat G i h_len,
   removeLeaf_sat_of_removeNode_sat G i h_len h_leaf h_ac⟩

/-- Contrapositive: if a forest is UNSAT, some edge lacks arc consistency. -/
theorem forest_unsat_witness (G : CubeGraph)
    (h_forest : IsForest G)
    (h_unsat : ¬ G.Satisfiable) :
    ∃ e ∈ G.edges,
      ¬ arcConsistentDir (G.cubes[e.1]) (G.cubes[e.2]) ∨
      ¬ arcConsistentDir (G.cubes[e.2]) (G.cubes[e.1]) := by
  exact Classical.byContradiction fun h_no_witness =>
    h_unsat (forest_arc_consistent_sat G h_forest (fun e he =>
      ⟨Classical.byContradiction (fun h1 => h_no_witness ⟨e, he, .inl h1⟩),
       Classical.byContradiction (fun h2 => h_no_witness ⟨e, he, .inr h2⟩)⟩))

end CubeGraph
