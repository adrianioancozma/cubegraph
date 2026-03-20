/-
  CubeGraph/Topology.lean
  Graph topology: degree, neighbors, leaves, acyclicity, node removal.

  Used by:
  - T1-C (acyclic → SAT): acyclic_has_leaf, removeNode
  - T2-A (leaf trimming): isLeaf, removeNode
  - T2-B (hierarchy): isAcyclic, isLeaf

  removeNode.edges_valid proven via eraseIdx_getElem_adjust helper.

  See: theory/research/PHASE3A-TREESAT-PLAN.md (tree SAT infrastructure plan)
  See: theory/foundations/03-cube-graph.md (graph connectivity)
-/

import CubeGraph.Basic

namespace CubeGraph

/-! ## Neighborhood and Degree -/

/-- Edges incident to node i (as source or target). -/
def incidentEdges (G : CubeGraph) (i : Fin G.cubes.length) :
    List (Fin G.cubes.length × Fin G.cubes.length) :=
  G.edges.filter (fun e => e.1 == i || e.2 == i)

/-- Neighbors of node i: other endpoints of incident edges. -/
def neighbors (G : CubeGraph) (i : Fin G.cubes.length) :
    List (Fin G.cubes.length) :=
  (G.incidentEdges i).filterMap (fun e =>
    if e.1 = i then some e.2 else if e.2 = i then some e.1 else none)

/-- Degree of node i = number of neighbors. -/
def degree (G : CubeGraph) (i : Fin G.cubes.length) : Nat :=
  (G.neighbors i).length

/-- A leaf has degree ≤ 1. -/
def isLeaf (G : CubeGraph) (i : Fin G.cubes.length) : Prop :=
  G.degree i ≤ 1

instance {G : CubeGraph} {i : Fin G.cubes.length} : Decidable (G.isLeaf i) :=
  Nat.decLe _ _

/-! ## Acyclicity -/

/-- A graph is acyclic if |edges| < |cubes|.
    Valid for forests (connected components are trees). -/
def isAcyclic (G : CubeGraph) : Prop :=
  G.edges.length < G.cubes.length

instance {G : CubeGraph} : Decidable G.isAcyclic :=
  Nat.decLt _ _

/-! ## Structural Path -/

/-- A structural path between two nodes in the graph.
    Defined as Type (not Prop) to enable depth-based recursion
    for path projection lemmas (graphPath_avoid_leaf). -/
inductive GraphPath (G : CubeGraph) :
    Fin G.cubes.length → Fin G.cubes.length → Type where
  | trivial : GraphPath G i i
  | step : (i, j) ∈ G.edges ∨ (j, i) ∈ G.edges →
           GraphPath G j k → GraphPath G i k

/-! ## Basic Theorems -/

/-- Every element in incidentEdges satisfies the filter predicate. -/
theorem mem_incidentEdges_iff (G : CubeGraph)
    (i : Fin G.cubes.length)
    (e : Fin G.cubes.length × Fin G.cubes.length) :
    e ∈ G.incidentEdges i ↔ e ∈ G.edges ∧ (e.1 = i ∨ e.2 = i) := by
  simp only [incidentEdges, List.mem_filter, Bool.or_eq_true, beq_iff_eq]

/-- Degree equals incident edges count (filterMap always returns some). -/
theorem degree_eq_incidentEdges (G : CubeGraph) (i : Fin G.cubes.length) :
    G.degree i = (G.incidentEdges i).length := by
  unfold degree neighbors
  suffices h : ∀ (l : List (Fin G.cubes.length × Fin G.cubes.length)),
      (∀ e ∈ l, e.1 = i ∨ e.2 = i) →
      (l.filterMap (fun e =>
        if e.1 = i then some e.2 else if e.2 = i then some e.1 else none)).length
      = l.length by
    apply h
    intro e he
    exact (mem_incidentEdges_iff G i e).mp he |>.2
  intro l hl
  induction l with
  | nil => simp
  | cons e es ih =>
    have he := hl e List.mem_cons_self
    have hes : ∀ x ∈ es, x.1 = i ∨ x.2 = i :=
      fun x hx => hl x (List.mem_cons_of_mem e hx)
    simp only [List.filterMap_cons, List.length_cons]
    cases he with
    | inl h1 =>
      simp only [h1, ite_true, List.length_cons]
      exact congrArg (· + 1) (ih hes)
    | inr h2 =>
      by_cases h1 : e.1 = i
      · simp only [h1, ite_true, List.length_cons]
        exact congrArg (· + 1) (ih hes)
      · simp only [h1, ite_false, h2, ite_true, List.length_cons]
        exact congrArg (· + 1) (ih hes)

/-- Degree as countP on edges. -/
theorem degree_eq_countP (G : CubeGraph) (i : Fin G.cubes.length) :
    G.degree i = G.edges.countP (fun e => e.1 == i || e.2 == i) := by
  rw [degree_eq_incidentEdges]
  unfold incidentEdges
  rw [List.countP_eq_length_filter]

/-- A leaf with degree 1 has exactly one neighbor. -/
theorem leaf_unique_neighbor (G : CubeGraph) (i : Fin G.cubes.length)
    (h : G.degree i = 1) :
    ∃ j : Fin G.cubes.length, G.neighbors i = [j] := by
  unfold degree at h
  exact List.length_eq_one_iff.mp h

/-! ## Handshaking Lemma Helpers -/

/-- countP over disjunction ≤ sum of countPs. -/
private theorem countP_or_le {α : Type} (p q : α → Bool) (l : List α) :
    l.countP (fun x => p x || q x) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons]
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

/-- Sum distributes over pointwise addition. -/
private theorem list_sum_map_add {α : Type} (f g : α → Nat) (l : List α) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]; omega

/-- If all elements of a Nat list are ≥ k, the sum is ≥ k * length. -/
private theorem sum_ge_of_all_ge (l : List Nat) (k : Nat)
    (h : ∀ x ∈ l, x ≥ k) : l.sum ≥ k * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.sum_cons, List.length_cons]
    have ha := h a List.mem_cons_self
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    rw [Nat.mul_succ]; omega

/-- Pointwise ≤ implies sum ≤. -/
private theorem sum_map_le_sum_map {α : Type} (f g : α → Nat) (l : List α)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a List.mem_cons_self
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    omega

/-- List.finRange n has no duplicates. -/
private theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij h_eq
  simp only [List.getElem_finRange] at h_eq
  have h := Fin.ext_iff.mp h_eq
  simp at h
  omega

/-- On a nodup list, countP (= a) ≤ 1. -/
private theorem countP_eq_le_one_of_nodup {α : Type} [DecidableEq α]
    {l : List α} (hnd : l.Nodup) (a : α) :
    l.countP (fun x => decide (a = x)) ≤ 1 := by
  induction l with
  | nil => simp
  | cons b t ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.countP_cons]
    by_cases hab : a = b
    · simp only [hab, decide_true, ite_true]
      suffices h0 : t.countP (fun x => decide (b = x)) = 0 by omega
      rw [List.countP_eq_zero]
      intro x hx hd
      exact hnd.1 ((decide_eq_true_eq.mp hd) ▸ hx)
    · simp only [show decide (a = b) = false from decide_eq_false hab]
      exact ih hnd.2

/-- Sum of indicator for equality over finRange = 1. -/
private theorem sum_indicator_finRange {n : Nat} (a : Fin n) :
    ((List.finRange n).map (fun i => if a = i then 1 else 0)).sum = 1 := by
  suffices h_cp : (List.finRange n).countP (fun i => decide (a = i)) = 1 by
    have h_eq : ∀ l : List (Fin n),
        (l.map (fun i => if a = i then (1 : Nat) else 0)).sum
        = l.countP (fun i => decide (a = i)) := by
      intro l
      induction l with
      | nil => simp
      | cons b t ih =>
        simp only [List.map_cons, List.sum_cons, List.countP_cons]
        by_cases hab : a = b
        · subst hab; simp; omega
        · simp [show ¬(a = b) from hab]; omega
    rw [h_eq]; exact h_cp
  have h_le := countP_eq_le_one_of_nodup (finRange_nodup n) a
  have h_pos : 0 < (List.finRange n).countP (fun i => decide (a = i)) :=
    List.countP_pos_iff.mpr ⟨a, BoolMat.mem_finRange a, by simp⟩
  omega

/-- Partition of unity: countP mapped fst over finRange = list length. -/
private theorem sum_countP_fst {n : Nat} (l : List (Fin n × Fin n)) :
    ((List.finRange n).map
      (fun i => l.countP (fun e => decide (e.1 = i)))).sum = l.length := by
  induction l with
  | nil =>
    simp only [List.countP_nil, List.length_nil]
    induction (List.finRange n) with
    | nil => simp
    | cons _ _ ih => simp [List.map_cons, List.sum_cons, ih]
  | cons e es ih =>
    simp only [List.countP_cons, decide_eq_true_eq, List.length_cons]
    have h_swap : ∀ i : Fin n,
        es.countP (fun x => decide (x.1 = i)) + (if e.1 = i then 1 else 0)
        = (if e.1 = i then 1 else 0) + es.countP (fun x => decide (x.1 = i)) :=
      fun _ => Nat.add_comm _ _
    simp only [h_swap]
    rw [list_sum_map_add, sum_indicator_finRange, ih]; omega

/-- Same for snd. -/
private theorem sum_countP_snd {n : Nat} (l : List (Fin n × Fin n)) :
    ((List.finRange n).map
      (fun i => l.countP (fun e => decide (e.2 = i)))).sum = l.length := by
  induction l with
  | nil =>
    simp only [List.countP_nil, List.length_nil]
    induction (List.finRange n) with
    | nil => simp
    | cons _ _ ih => simp [List.map_cons, List.sum_cons, ih]
  | cons e es ih =>
    simp only [List.countP_cons, decide_eq_true_eq, List.length_cons]
    have h_swap : ∀ i : Fin n,
        es.countP (fun x => decide (x.2 = i)) + (if e.2 = i then 1 else 0)
        = (if e.2 = i then 1 else 0) + es.countP (fun x => decide (x.2 = i)) :=
      fun _ => Nat.add_comm _ _
    simp only [h_swap]
    rw [list_sum_map_add, sum_indicator_finRange, ih]; omega

/-! ## Handshaking Bound -/

/-- degree(i) ≤ countP(fst = i) + countP(snd = i). -/
private theorem degree_le_fst_plus_snd (G : CubeGraph) (i : Fin G.cubes.length) :
    G.degree i ≤
      G.edges.countP (fun e => decide (e.1 = i)) +
      G.edges.countP (fun e => decide (e.2 = i)) := by
  rw [degree_eq_countP]
  calc G.edges.countP (fun e => e.1 == i || e.2 == i)
      ≤ G.edges.countP (fun e => (e.1 == i)) + G.edges.countP (fun e => (e.2 == i)) :=
        countP_or_le _ _ _
    _ = G.edges.countP (fun e => decide (e.1 = i)) +
        G.edges.countP (fun e => decide (e.2 = i)) := by rfl

/-- Sum of all degrees ≤ 2 × |edges|. -/
private theorem degree_sum_le (G : CubeGraph) :
    ((List.finRange G.cubes.length).map (fun i => G.degree i)).sum
    ≤ 2 * G.edges.length := by
  calc ((List.finRange G.cubes.length).map (fun i => G.degree i)).sum
      ≤ ((List.finRange G.cubes.length).map (fun i =>
          G.edges.countP (fun e => decide (e.1 = i)) +
          G.edges.countP (fun e => decide (e.2 = i)))).sum := by
        apply sum_map_le_sum_map
        intro i _
        exact degree_le_fst_plus_snd G i
    _ = ((List.finRange G.cubes.length).map
          (fun i => G.edges.countP (fun e => decide (e.1 = i)))).sum +
        ((List.finRange G.cubes.length).map
          (fun i => G.edges.countP (fun e => decide (e.2 = i)))).sum :=
        list_sum_map_add _ _ _
    _ = G.edges.length + G.edges.length :=
        by rw [sum_countP_fst, sum_countP_snd]
    _ = 2 * G.edges.length := by omega

/-! ## Acyclic Has Leaf -/

/-- In an acyclic graph with ≥ 2 nodes, at least one node is a leaf. -/
theorem acyclic_has_leaf (G : CubeGraph) (_h_ne : G.cubes.length ≥ 2)
    (h_ac : G.isAcyclic) :
    ∃ i : Fin G.cubes.length, G.isLeaf i := by
  refine Classical.byContradiction fun h_no_leaf => ?_
  have h_all_ge2 : ∀ i : Fin G.cubes.length, G.degree i ≥ 2 :=
    fun i => Nat.le_of_not_lt fun hi => h_no_leaf ⟨i, by unfold isLeaf; omega⟩
  have h_sum_lb : ((List.finRange G.cubes.length).map (fun i => G.degree i)).sum
      ≥ 2 * G.cubes.length := by
    have h := sum_ge_of_all_ge
      ((List.finRange G.cubes.length).map (fun i => G.degree i)) 2 (by
        intro x hx; rw [List.mem_map] at hx; obtain ⟨i, _, rfl⟩ := hx; exact h_all_ge2 i)
    simp [List.length_map, List.length_finRange] at h
    exact h
  have h_sum_ub := degree_sum_le G
  unfold isAcyclic at h_ac
  omega

/-! ## Node Removal -/

/-- Adjusted index into eraseIdx maps back to the original element. -/
theorem eraseIdx_getElem_adjust {l : List α} {i : Nat}
    {e : Nat} (he : e < l.length) (hne : e ≠ i)
    (h : (if e < i then e else e - 1) < (l.eraseIdx i).length) :
    (l.eraseIdx i)[if e < i then e else e - 1] = l[e] := by
  by_cases hlt : e < i
  · simp only [if_pos hlt] at h ⊢
    exact List.getElem_eraseIdx_of_lt h hlt
  · simp only [if_neg hlt] at h ⊢
    rw [List.getElem_eraseIdx_of_ge h (by omega)]
    have : (e - 1) + 1 = e := by omega
    simp only [this]

/-- Remove a node from the graph, re-indexing edges. -/
def removeNode (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) : CubeGraph where
  cubes := G.cubes.eraseIdx i
  edges :=
    G.edges.filterMap (fun e =>
      if h1 : e.1 = i then none
      else if h2 : e.2 = i then none
      else
        have hlen_eq : (G.cubes.eraseIdx i).length = G.cubes.length - 1 := by
          rw [List.length_eraseIdx]; simp [i.isLt]
        let j : Fin (G.cubes.eraseIdx i).length :=
          ⟨if e.1.val < i.val then e.1.val else e.1.val - 1,
           by rw [hlen_eq]; have := e.1.isLt; have : e.1.val ≠ i.val := fun h => h1 (Fin.ext h)
              split <;> omega⟩
        let k : Fin (G.cubes.eraseIdx i).length :=
          ⟨if e.2.val < i.val then e.2.val else e.2.val - 1,
           by rw [hlen_eq]; have := e.2.isLt; have : e.2.val ≠ i.val := fun h => h2 (Fin.ext h)
              split <;> omega⟩
        some (j, k))
  edges_valid := by
    intro ⟨a, b⟩ hmem
    simp only [List.mem_filterMap] at hmem
    obtain ⟨⟨e1, e2⟩, he_mem, h_fm⟩ := hmem
    split at h_fm
    · next h1 => simp at h_fm
    · next h1 =>
      split at h_fm
      · next h2 => simp at h_fm
      · next h2 =>
        simp at h_fm
        have h_valid := G.edges_valid ⟨e1, e2⟩ he_mem
        obtain ⟨ha, hb⟩ := h_fm
        subst ha; subst hb
        simp only [Fin.getElem_fin]
        rw [eraseIdx_getElem_adjust e1.isLt (fun h => h1 (Fin.ext h)),
            eraseIdx_getElem_adjust e2.isLt (fun h => h2 (Fin.ext h))]
        exact h_valid
  edges_complete := by
    intro i' j' hij' hlw'
    have hlen_eq : (G.cubes.eraseIdx i.val).length = G.cubes.length - 1 := by
      rw [List.length_eraseIdx]; simp [i.isLt]
    -- Embed erased index → original: if < i then same, else +1
    let ei : Fin G.cubes.length :=
      ⟨if i'.val < i.val then i'.val else i'.val + 1,
       by have := i'.isLt; have := hlen_eq; split <;> omega⟩
    let ej : Fin G.cubes.length :=
      ⟨if j'.val < i.val then j'.val else j'.val + 1,
       by have := j'.isLt; have := hlen_eq; split <;> omega⟩
    -- Extract .val equations for omega
    have hei_val : ei.val = if i'.val < i.val then i'.val else i'.val + 1 := by
      simp [ei]
    have hej_val : ej.val = if j'.val < i.val then j'.val else j'.val + 1 := by
      simp [ej]
    -- cubes[embed(j')] = cubes_erased[j']
    have hci : G.cubes[ei] = (G.cubes.eraseIdx i.val)[i'] := by
      simp only [ei, Fin.getElem_fin]
      split
      · exact (List.getElem_eraseIdx_of_lt i'.isLt ‹_›).symm
      · exact (List.getElem_eraseIdx_of_ge i'.isLt (by omega)).symm
    have hcj : G.cubes[ej] = (G.cubes.eraseIdx i.val)[j'] := by
      simp only [ej, Fin.getElem_fin]
      split
      · exact (List.getElem_eraseIdx_of_lt j'.isLt ‹_›).symm
      · exact (List.getElem_eraseIdx_of_ge j'.isLt (by omega)).symm
    -- linkWeight preserved
    have hlw_orig : Cube.linkWeight G.cubes[ei] G.cubes[ej] > 0 := by
      rw [hci, hcj]; exact hlw'
    -- embed(i') ≠ embed(j')
    have hij_orig : ei ≠ ej := by
      intro h
      have hv : ei.val = ej.val := congrArg Fin.val h
      rw [hei_val, hej_val] at hv
      apply hij'; ext
      have := i'.isLt; have := j'.isLt; have := hlen_eq
      split at hv <;> split at hv <;> omega
    -- embed(j') ≠ i (removed node)
    have hei_ne : ei ≠ i := by
      intro h
      have hv : ei.val = i.val := congrArg Fin.val h
      rw [hei_val] at hv
      have := i'.isLt; have := hlen_eq; split at hv <;> omega
    have hej_ne : ej ≠ i := by
      intro h
      have hv : ej.val = i.val := congrArg Fin.val h
      rw [hej_val] at hv
      have := j'.isLt; have := hlen_eq; split at hv <;> omega
    -- Helper: shrink(embed(x)) = x (inline version of removeNodeShrink_embed)
    have shrink_embed (x : Fin (G.cubes.eraseIdx i.val).length) :
        (if (if x.val < i.val then x.val else x.val + 1) < i.val
          then (if x.val < i.val then x.val else x.val + 1)
          else (if x.val < i.val then x.val else x.val + 1) - 1) = x.val := by
      by_cases h : x.val < i.val
      · simp [h]
      · simp only [if_neg h, show ¬(x.val + 1 < i.val) from by omega, ite_false]
        omega
    -- Apply G.edges_complete
    rcases G.edges_complete ei ej hij_orig hlw_orig with hedge | hedge
    · left; rw [List.mem_filterMap]
      refine ⟨(ei, ej), hedge, ?_⟩
      simp only [dif_neg hei_ne, dif_neg hej_ne]
      congr 1; congr 1 <;> ext
      · show (if ei.val < i.val then ei.val else ei.val - 1) = i'.val
        rw [hei_val]; exact shrink_embed i'
      · show (if ej.val < i.val then ej.val else ej.val - 1) = j'.val
        rw [hej_val]; exact shrink_embed j'
    · right; rw [List.mem_filterMap]
      refine ⟨(ej, ei), hedge, ?_⟩
      simp only [dif_neg hej_ne, dif_neg hei_ne]
      congr 1; congr 1 <;> ext
      · show (if ej.val < i.val then ej.val else ej.val - 1) = j'.val
        rw [hej_val]; exact shrink_embed j'
      · show (if ei.val < i.val then ei.val else ei.val - 1) = i'.val
        rw [hei_val]; exact shrink_embed i'

/-! ## Leaf Removal Preserves Node Count -/

/-- Removing a node reduces the cube count by 1. -/
theorem removeNode_cubes_length (G : CubeGraph) (i : Fin G.cubes.length)
    (h_len : G.cubes.length ≥ 2) :
    (G.removeNode i h_len).cubes.length = G.cubes.length - 1 := by
  simp [removeNode, List.length_eraseIdx, i.isLt]

/-! ## Connectivity -/

/-- Depth (number of steps) in a GraphPath, for well-founded recursion. -/
def pathDepth : GraphPath G a b → Nat
  | .trivial => 0
  | .step _ sub => pathDepth sub + 1

/-- Result of decomposing a non-trivial path into its first step.
    A structure in Type (not Prop) so we can extract the GraphPath sub-path. -/
structure GraphPathStep (G : CubeGraph) (x b : Fin G.cubes.length)
    (h : GraphPath G x b) where
  next : Fin G.cubes.length
  edge : (x, next) ∈ G.edges ∨ (next, x) ∈ G.edges
  sub : GraphPath G next b
  depth_bound : pathDepth sub + 1 ≤ pathDepth h

/-- A non-trivial path (x ≠ b) can be decomposed into a first step.
    Returns a Type-valued structure to avoid Prop elimination restrictions. -/
def graphPath_step_of_ne {G : CubeGraph} {x b : Fin G.cubes.length}
    (h : GraphPath G x b) (hne : x ≠ b) : GraphPathStep G x b h :=
  match h with
  | .trivial => absurd rfl hne
  | .step edge sub => ⟨_, edge, sub, Nat.le.refl⟩

/-- A CubeGraph is connected if every pair of nodes has a structural path. -/
def isConnected (G : CubeGraph) : Prop :=
  ∀ i j : Fin G.cubes.length, Nonempty (GraphPath G i j)

/-- If there's an edge between a and i (in either direction), a is a neighbor of i. -/
theorem mem_neighbors_of_edge (G : CubeGraph) (i a : Fin G.cubes.length)
    (h : (a, i) ∈ G.edges ∨ (i, a) ∈ G.edges) :
    a ∈ G.neighbors i := by
  simp only [neighbors, List.mem_filterMap]
  rcases h with h | h
  · -- (a, i) ∈ G.edges → a ∈ neighbors i
    refine ⟨(a, i), (mem_incidentEdges_iff ..).mpr ⟨h, .inr rfl⟩, ?_⟩
    -- filterMap on (a, i): if a = i then some i else some a
    simp only
    by_cases hai : a = i
    · simp [hai]
    · simp [hai]
  · -- (i, a) ∈ G.edges → a ∈ neighbors i
    refine ⟨(i, a), (mem_incidentEdges_iff ..).mpr ⟨h, .inl rfl⟩, ?_⟩
    simp

/-- If j ∈ neighbors(i), then there exists an edge between i and j. -/
theorem edge_of_mem_neighbors (G : CubeGraph) (i j : Fin G.cubes.length)
    (h : j ∈ G.neighbors i) :
    (i, j) ∈ G.edges ∨ (j, i) ∈ G.edges := by
  simp only [neighbors, List.mem_filterMap] at h
  obtain ⟨e, he_inc, he_j⟩ := h
  have ⟨he_mem, he_touch⟩ := (mem_incidentEdges_iff ..).mp he_inc
  -- The filterMap function: if e.1 = i → some e.2, elif e.2 = i → some e.1, else none
  -- he_j says the result is some j
  by_cases h1 : e.1 = i
  · -- e.1 = i: filterMap gives some e.2
    have : (if e.1 = i then some e.2 else if e.2 = i then some e.1 else none) = some e.2 :=
      by simp [h1]
    rw [this] at he_j
    have hj_eq := Option.some.inj he_j
    rw [← hj_eq, ← h1]; exact .inl he_mem
  · -- e.1 ≠ i: need e.2 = i (from he_touch)
    have h2 : e.2 = i := by
      rcases he_touch with h | h
      · exact absurd h h1
      · exact h
    rw [if_neg h1, if_pos h2] at he_j
    have hj_eq := Option.some.inj he_j
    rw [← hj_eq, ← h2]; exact .inr he_mem

/-- In a connected graph with ≥ 2 nodes, every node has degree ≥ 1 (no isolated nodes). -/
theorem connected_degree_pos (G : CubeGraph) (h_conn : G.isConnected)
    (h_len : G.cubes.length ≥ 2) (i : Fin G.cubes.length) :
    G.degree i ≥ 1 := by
  -- Pick a node k ≠ i
  have hlt : G.cubes.length > 0 := by omega
  obtain ⟨k, hk⟩ : ∃ k : Fin G.cubes.length, k ≠ i := by
    by_cases hi : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by have hv := congrArg Fin.val h; simp at hv; omega⟩
    · exact ⟨⟨0, hlt⟩, fun h => by have hv := congrArg Fin.val h; simp at hv; omega⟩
  -- Path from i to k is non-trivial since i ≠ k
  have hpath : GraphPath G i k := Classical.choice (h_conn i k)
  cases hpath with
  | trivial => exact absurd rfl hk
  | step edge _ =>
    -- edge gives an incident edge to i → degree ≥ 1
    rw [degree_eq_incidentEdges]
    rcases edge with h | h
    · exact List.length_pos_of_mem ((mem_incidentEdges_iff ..).mpr ⟨h, .inl rfl⟩)
    · exact List.length_pos_of_mem ((mem_incidentEdges_iff ..).mpr ⟨h, .inr rfl⟩)

/-! ## Forest (Leaf-Peelable Acyclicity) -/

/-- A CubeGraph is a forest if it can be fully decomposed by leaf removal.
    This is the correct acyclicity notion for the SAT theorem:
    - `isAcyclic = |E| < |V|` is necessary but NOT sufficient (fails on disconnected graphs)
    - `IsForest` gives exactly the induction structure we need (peel leaves one by one)

    Constructors:
    - leaf_free: no edges → trivially a forest
    - peel: remove a degree-1 node → if remainder is forest → whole graph is forest -/
inductive IsForest : CubeGraph → Prop where
  | leaf_free {G : CubeGraph} : G.edges = [] → IsForest G
  | peel {G : CubeGraph} (i : Fin G.cubes.length) (h_len : G.cubes.length ≥ 2) :
      G.degree i = 1 → IsForest (G.removeNode i h_len) → IsForest G

end CubeGraph
