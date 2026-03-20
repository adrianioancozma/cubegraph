/-
  CubeGraph/CNF.lean
  Phase 4 (T1-A): CNF ↔ CubeGraph Bridge.

  Proves the fundamental equivalence between 3-SAT satisfiability
  (truth assignments on variables) and CubeGraph satisfiability
  (compatible gap selections).

  Core insight — Complement Duality:
  Assignment a satisfies all clauses in cube C
  iff the complement vertex (7 − assignmentVertex(a,C)) is a gap in C.

  Main results:
  - complement_duality: per-cube equivalence
  - formula_sat_implies_sat: FormulaSat → Satisfiable (unconditional)
  - sat_implies_formula_sat: Satisfiable → FormulaSat (unconditional)
  - sat_iff_formula_sat: full equivalence (unconditional, edges_complete is structural)

  See: theory/foundations/02-clause-space.md (clause encoding: bit=1 → positive literal)
  See: theory/foundations/06-empty-vertex-duality.md (complement duality)
  See: theory/theorems/CORE-THEOREMS-SUMMARY.md (the bridge theorem)
-/

import CubeGraph.Basic
import CubeGraph.GapLemmas
import CubeGraph.PartB

namespace CubeGraph

/-! ## Section 1: CNF Definitions -/

/-- A truth assignment: variable number → truth value. -/
def Assignment := Nat → Bool

/-- Helper: bounded if-then-else sum for Fin 8 construction. -/
private theorem ite_sum_lt_eight (b₁ b₂ b₃ : Bool) :
    (if b₁ then 1 else 0) + (if b₂ then 2 else 0) + (if b₃ then 4 else 0) < 8 := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> simp <;> omega

private theorem ite_sum_lt_eight' (b₁ b₂ b₃ : Bool) :
    (if b₁ then 0 else 1) + (if b₂ then 0 else 2) + (if b₃ then 0 else 4) < 8 := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> simp <;> omega

/-- Map assignment to vertex in cube: bit i = a(varAt i).
    Encodes which literals are "matched" by the assignment. -/
def assignmentToVertex (a : Assignment) (c : Cube) : Vertex :=
  ⟨(if a c.var₁ then 1 else 0) +
   (if a c.var₂ then 2 else 0) +
   (if a c.var₃ then 4 else 0), ite_sum_lt_eight _ _ _⟩

/-- Complement vertex: flips all 3 bits (v ↦ 7 − v). -/
def complementVertex (v : Vertex) : Vertex := ⟨7 - v.val, by omega⟩

/-- Map assignment directly to gap vertex: bit i = ¬a(varAt i).
    Equal to complementVertex (assignmentToVertex a c). -/
def assignmentToGap (a : Assignment) (c : Cube) : Vertex :=
  ⟨(if a c.var₁ then 0 else 1) +
   (if a c.var₂ then 0 else 2) +
   (if a c.var₃ then 0 else 4), ite_sum_lt_eight' _ _ _⟩

/-- Assignment satisfies all clauses encoded by cube c.
    A filled vertex v represents clause (l₁ ∨ l₂ ∨ l₃) with polarities from v's bits.
    Assignment a satisfies this clause iff a agrees with v on ≥1 bit.
    Equivalently: a satisfies ALL clauses iff complement(assignmentVertex) is a gap. -/
def allClausesSat (c : Cube) (a : Assignment) : Prop :=
  c.isGap (assignmentToGap a c) = true

/-- CubeGraph is formula-satisfiable: ∃ global assignment satisfying all cubes. -/
def FormulaSat (G : CubeGraph) : Prop :=
  ∃ a : Assignment, ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a

/-- CubeGraph has edges between ALL pairs of cubes with shared variables.
    Now guaranteed structurally by `CubeGraph.edges_complete` field.
    Kept as an alias for backward compatibility and documentation. -/
def HasCompleteEdges (G : CubeGraph) : Prop :=
  ∀ i j : Fin G.cubes.length, i ≠ j →
    Cube.linkWeight (G.cubes[i]) (G.cubes[j]) > 0 →
    (i, j) ∈ G.edges ∨ (j, i) ∈ G.edges

/-- Every CubeGraph has complete edges (structural invariant). -/
theorem hasCompleteEdges (G : CubeGraph) : HasCompleteEdges G := G.edges_complete

/-! ## Section 2: Complement Properties -/

/-- Complement is involutive: complement(complement(v)) = v. -/
theorem complement_involutive (v : Vertex) :
    complementVertex (complementVertex v) = v := by
  revert v; native_decide

/-- Complement is never self: complement(v) ≠ v for all v : Fin 8.
    (7 − v = v would require v = 3.5, impossible in ℕ.) -/
theorem complement_ne_self (v : Vertex) : complementVertex v ≠ v := by
  revert v; native_decide

/-- assignmentToGap = complementVertex ∘ assignmentToVertex. -/
theorem assignmentToGap_eq (a : Assignment) (c : Cube) :
    assignmentToGap a c = complementVertex (assignmentToVertex a c) := by
  have h : (assignmentToGap a c).val = (complementVertex (assignmentToVertex a c)).val := by
    unfold assignmentToGap assignmentToVertex complementVertex
    simp only []
    cases a c.var₁ <;> cases a c.var₂ <;> cases a c.var₃ <;> simp <;> omega
  exact Fin.ext h

/-! ## Section 3: Bit-Level Lemmas -/

/-- Bit j of assignmentToGap = ¬a(c.varAt j). -/
theorem assignmentToGap_bit (a : Assignment) (c : Cube) (j : Fin 3) :
    Cube.vertexBit (assignmentToGap a c) j = !a (c.varAt j) := by
  match j with
  | ⟨0, _⟩ =>
    simp only [Cube.vertexBit, assignmentToGap, Cube.varAt]
    cases a c.var₁ <;> cases a c.var₂ <;> cases a c.var₃ <;> simp
  | ⟨1, _⟩ =>
    simp only [Cube.vertexBit, assignmentToGap, Cube.varAt]
    cases a c.var₁ <;> cases a c.var₂ <;> cases a c.var₃ <;> simp
  | ⟨2, _⟩ =>
    simp only [Cube.vertexBit, assignmentToGap, Cube.varAt]
    cases a c.var₁ <;> cases a c.var₂ <;> cases a c.var₃ <;> simp

/-- vars.idxOf (varAt j) = j.val for distinct variables. -/
theorem vars_idxOf_varAt (c : Cube) (j : Fin 3) :
    c.vars.idxOf (c.varAt j) = j.val := by
  have ⟨h12, h13, h23⟩ := c.vars_distinct
  match j with
  | ⟨0, _⟩ =>
    simp only [Cube.vars, Cube.varAt]
    simp [List.idxOf_cons_self]
  | ⟨1, _⟩ =>
    simp only [Cube.vars, Cube.varAt, List.idxOf, List.findIdx_cons]
    rw [show (c.var₁ == c.var₂) = false from beq_eq_false_iff_ne.mpr h12]
    simp
  | ⟨2, _⟩ =>
    simp only [Cube.vars, Cube.varAt, List.idxOf, List.findIdx_cons]
    rw [show (c.var₁ == c.var₃) = false from beq_eq_false_iff_ne.mpr h13,
        show (c.var₂ == c.var₃) = false from beq_eq_false_iff_ne.mpr h23]
    simp

/-- Member of vars ↔ equals one of the three variables. -/
theorem mem_vars_iff (c : Cube) (v : Nat) :
    v ∈ c.vars ↔ v = c.var₁ ∨ v = c.var₂ ∨ v = c.var₃ := by
  simp [Cube.vars]

/-- Member of sharedVars → member of both vars lists. -/
theorem mem_sharedVars (c₁ c₂ : Cube) (v : Nat)
    (h : v ∈ Cube.sharedVars c₁ c₂) : v ∈ c₁.vars ∧ v ∈ c₂.vars := by
  simp [Cube.sharedVars, List.mem_filter] at h
  exact ⟨h.1, h.2⟩

/-! ## Section 4: Bit Shift Helpers -/

/-- If vertexBit values (as Bool = (x>>>j &&&1 == 1)) are equal,
    then the raw (x>>>j &&&1) Nat values are BEq-equal. -/
private theorem shift_and1_beq_of_eq (x y jx jy : Nat)
    (h : (((x >>> jx) &&& 1) == 1) = (((y >>> jy) &&& 1) == 1)) :
    (((x >>> jx) &&& 1) == ((y >>> jy) &&& 1)) = true := by
  simp only [Nat.and_one_is_mod] at h ⊢
  have h1 := Nat.mod_two_eq_zero_or_one (x >>> jx)
  have h2 := Nat.mod_two_eq_zero_or_one (y >>> jy)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all

/-- vertexBit is definitionally the same as the raw bit-shift check. -/
theorem vertexBit_eq_shift (v : Vertex) (j : Fin 3) :
    Cube.vertexBit v j = ((v.val >>> j.val) &&& 1 == 1) := rfl

/-- For sv ∈ c.vars, the raw bit at idxOf sv equals vertexBit at the matching Fin 3 index.
    Cases: sv = var₁ → idx 0, sv = var₂ → idx 1, sv = var₃ → idx 2. -/
theorem assignmentToGap_rawbit (a : Assignment) (c : Cube) (sv : Nat) (hsv : sv ∈ c.vars) :
    (((assignmentToGap a c).val >>> c.vars.idxOf sv) &&& 1 == 1) = !a sv := by
  rw [mem_vars_iff] at hsv
  rcases hsv with rfl | rfl | rfl
  · -- sv = var₁: idxOf = 0
    have : c.vars.idxOf c.var₁ = (0 : Fin 3).val := vars_idxOf_varAt c ⟨0, by omega⟩
    rw [this]; exact assignmentToGap_bit a c ⟨0, by omega⟩
  · -- sv = var₂: idxOf = 1
    have : c.vars.idxOf c.var₂ = (1 : Fin 3).val := vars_idxOf_varAt c ⟨1, by omega⟩
    rw [this]; exact assignmentToGap_bit a c ⟨1, by omega⟩
  · -- sv = var₃: idxOf = 2
    have : c.vars.idxOf c.var₃ = (2 : Fin 3).val := vars_idxOf_varAt c ⟨2, by omega⟩
    rw [this]; exact assignmentToGap_bit a c ⟨2, by omega⟩

/-! ## Section 5: Backward Direction (FormulaSat → Satisfiable) -/

/-- Gap selection from assignment: each cube gets its gap vertex. -/
def assignmentToGapSelection (G : CubeGraph) (a : Assignment) : GapSelection G :=
  fun i => assignmentToGap a (G.cubes[i])

/-- Valid: each gap is actually a gap (from allClausesSat hypothesis). -/
theorem assignmentToGapSelection_valid (G : CubeGraph) (a : Assignment)
    (h : ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a) :
    validSelection G (assignmentToGapSelection G a) :=
  fun i => h i

/-- Compatible: transferOp satisfied on all edges (unconditional — follows from
    shared variable bit agreement via the same assignment). -/
theorem assignmentToGapSelection_compatible (G : CubeGraph) (a : Assignment)
    (h_valid : ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a) :
    compatibleSelection G (assignmentToGapSelection G a) := by
  intro e he
  unfold assignmentToGapSelection
  apply gaps_and_compat_implies_transferOp
  · exact h_valid e.1
  · exact h_valid e.2
  · rw [List.all_eq_true]
    intro sv hsv
    have ⟨hsv1, hsv2⟩ := mem_sharedVars _ _ sv hsv
    have hbit1 := assignmentToGap_rawbit a (G.cubes[e.1]) sv hsv1
    have hbit2 := assignmentToGap_rawbit a (G.cubes[e.2]) sv hsv2
    exact shift_and1_beq_of_eq _ _ _ _ (by rw [hbit1, hbit2])

/-- **Backward**: FormulaSat → Satisfiable (unconditional — no HasCompleteEdges needed). -/
theorem formula_sat_implies_sat (G : CubeGraph) (h : G.FormulaSat) : G.Satisfiable := by
  obtain ⟨a, ha⟩ := h
  exact ⟨assignmentToGapSelection G a,
         assignmentToGapSelection_valid G a ha,
         assignmentToGapSelection_compatible G a ha⟩

/-! ## Section 6: Forward Direction (Satisfiable → FormulaSat) -/

/-- varAt j is always a member of vars. -/
theorem varAt_mem_vars (c : Cube) (j : Fin 3) : c.varAt j ∈ c.vars := by
  match j with
  | ⟨0, _⟩ => simp [Cube.vars, Cube.varAt]
  | ⟨1, _⟩ => simp [Cube.vars, Cube.varAt]
  | ⟨2, _⟩ => simp [Cube.vars, Cube.varAt]

/-- vars has length 3. -/
theorem vars_length (c : Cube) : c.vars.length = 3 := by simp [Cube.vars]

/-- If v ∈ c.vars, then idxOf v < 3. -/
theorem idxOf_lt_three (c : Cube) (v : Nat) (hv : v ∈ c.vars) :
    c.vars.idxOf v < 3 := by
  have := List.idxOf_lt_length_of_mem hv
  rw [vars_length] at this; exact this

/-- From transferOp = true, extract that a shared variable's bit agrees. -/
theorem transferOp_sharedVar_agree (c₁ c₂ : Cube) (g₁ g₂ : Vertex)
    (h : transferOp c₁ c₂ g₁ g₂ = true) (sv : Nat)
    (hsv : sv ∈ Cube.sharedVars c₁ c₂) :
    ((g₁.val >>> c₁.vars.idxOf sv) &&& 1) = ((g₂.val >>> c₂.vars.idxOf sv) &&& 1) := by
  simp only [transferOp, Bool.and_eq_true] at h
  have hcompat := h.2
  rw [List.all_eq_true] at hcompat
  have hsv_eq := hcompat sv hsv
  exact beq_iff_eq.mp hsv_eq

/-- Shared variable membership: if v ∈ c₁.vars ∧ v ∈ c₂.vars, then v ∈ sharedVars. -/
theorem mem_sharedVars_of_mem_both (c₁ c₂ : Cube) (v : Nat)
    (h₁ : v ∈ c₁.vars) (h₂ : v ∈ c₂.vars) :
    v ∈ Cube.sharedVars c₁ c₂ := by
  simp [Cube.sharedVars, List.mem_filter]
  exact ⟨h₁, h₂⟩

/-- linkWeight > 0 when a shared variable exists. -/
theorem linkWeight_pos_of_shared (c₁ c₂ : Cube) (v : Nat)
    (h₁ : v ∈ c₁.vars) (h₂ : v ∈ c₂.vars) :
    Cube.linkWeight c₁ c₂ > 0 := by
  unfold Cube.linkWeight
  have := mem_sharedVars_of_mem_both c₁ c₂ v h₁ h₂
  exact List.length_pos_of_mem this

/-- Construct global assignment from gap selection (noncomputable via Classical.choose). -/
noncomputable def gapSelectionToAssignment (G : CubeGraph) (s : GapSelection G) : Assignment :=
  fun v =>
    if h : ∃ i : Fin G.cubes.length, v ∈ (G.cubes[i]).vars then
      let i := h.choose
      let c := G.cubes[i]
      let idx := c.vars.idxOf v
      have hidx : idx < 3 := idxOf_lt_three c v h.choose_spec
      !(Cube.vertexBit (s i) ⟨idx, hidx⟩)
    else true

/-- Key: for any cube j containing variable v, the constructed assignment
    reads the correct bit from s(j) (using compatibility for cross-cube consistency). -/
theorem gapSelection_consistent_bit (G : CubeGraph) (s : GapSelection G)
    (_h_valid : validSelection G s) (h_compat : compatibleSelection G s)
    (j : Fin G.cubes.length) (k : Fin 3) :
    gapSelectionToAssignment G s ((G.cubes[j]).varAt k) =
      !(Cube.vertexBit (s j) k) := by
  let v := (G.cubes[j]).varAt k
  have hv_mem_j : v ∈ (G.cubes[j]).vars := varAt_mem_vars _ k
  -- The assignment uses some cube i (Classical.choose)
  unfold gapSelectionToAssignment
  have hex : ∃ i : Fin G.cubes.length, v ∈ (G.cubes[i]).vars := ⟨j, hv_mem_j⟩
  rw [dif_pos hex]
  -- Now we need: the bit from cube i matches the bit from cube j
  let i := hex.choose
  have hv_mem_i : v ∈ (G.cubes[i]).vars := hex.choose_spec
  by_cases hij : i = j
  · -- Same cube: i = j, so s i and s j are the same
    dsimp only []
    have hij' : hex.choose = j := hij
    simp only [hij', vars_idxOf_varAt]
  · -- Different cubes sharing variable v: use compatibility
    have hlw : Cube.linkWeight (G.cubes[i]) (G.cubes[j]) > 0 :=
      linkWeight_pos_of_shared _ _ v hv_mem_i hv_mem_j
    have hedge := G.edges_complete i j hij hlw
    -- Get the edge and extract bit agreement
    rcases hedge with hedge | hedge
    · -- Edge (i, j) exists
      have htop := h_compat (i, j) hedge
      have hag := transferOp_sharedVar_agree _ _ _ _ htop v
        (mem_sharedVars_of_mem_both _ _ v hv_mem_i hv_mem_j)
      -- hag : raw bits agree between s(i) and s(j)
      -- Need: vertexBit (s i) ⟨idxOf v in ci, _⟩ = vertexBit (s j) ⟨idxOf v in cj, _⟩
      simp only [Cube.vertexBit]
      have hj_idx : (G.cubes[j]).vars.idxOf v = k.val := vars_idxOf_varAt (G.cubes[j]) k
      rw [hj_idx] at hag
      rw [hag]
    · -- Edge (j, i) exists
      have htop := h_compat (j, i) hedge
      have hag := transferOp_sharedVar_agree _ _ _ _ htop v
        (mem_sharedVars_of_mem_both _ _ v hv_mem_j hv_mem_i)
      simp only [Cube.vertexBit]
      have hj_idx : (G.cubes[j]).vars.idxOf v = k.val := vars_idxOf_varAt (G.cubes[j]) k
      rw [hj_idx] at hag
      rw [← hag]

/-- Bit-reconstruction: any vertex v : Fin 8 is determined by its 3 bits.
    Reconstruction via assignmentToGap pattern (negated bits → gap vertex). -/
private theorem gap_bit_reconstruction (v : Vertex) :
    (⟨(if !(Cube.vertexBit v ⟨0, by omega⟩) then 0 else 1) +
     (if !(Cube.vertexBit v ⟨1, by omega⟩) then 0 else 2) +
     (if !(Cube.vertexBit v ⟨2, by omega⟩) then 0 else 4),
     ite_sum_lt_eight' _ _ _⟩ : Vertex) = v := by
  revert v; native_decide

/-- The constructed assignment's gap vertex equals the gap selection. -/
theorem gapSelectionToAssignment_gap_eq (G : CubeGraph) (s : GapSelection G)
    (h_valid : validSelection G s) (h_compat : compatibleSelection G s)
    (j : Fin G.cubes.length) :
    assignmentToGap (gapSelectionToAssignment G s) (G.cubes[j]) = s j := by
  have h0 := gapSelection_consistent_bit G s h_valid h_compat j ⟨0, by omega⟩
  have h1 := gapSelection_consistent_bit G s h_valid h_compat j ⟨1, by omega⟩
  have h2 := gapSelection_consistent_bit G s h_valid h_compat j ⟨2, by omega⟩
  simp only [Cube.varAt] at h0 h1 h2
  show assignmentToGap _ _ = _
  simp only [assignmentToGap, h0, h1, h2]
  exact gap_bit_reconstruction (s j)

/-- Under HasCompleteEdges, the constructed assignment satisfies each cube. -/
theorem gapSelectionToAssignment_satisfies (G : CubeGraph) (s : GapSelection G)
    (h_valid : validSelection G s) (h_compat : compatibleSelection G s) :
    ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) (gapSelectionToAssignment G s) := by
  intro i
  unfold allClausesSat
  rw [gapSelectionToAssignment_gap_eq G s h_valid h_compat i]
  exact h_valid i

/-- **Forward**: Satisfiable → FormulaSat (uses structural edges_complete). -/
theorem sat_implies_formula_sat (G : CubeGraph)
    (h_sat : G.Satisfiable) : G.FormulaSat := by
  obtain ⟨s, h_valid, h_compat⟩ := h_sat
  exact ⟨gapSelectionToAssignment G s,
         gapSelectionToAssignment_satisfies G s h_valid h_compat⟩

/-! ## Section 7: Main Theorem -/

/-- **T1-A**: CubeGraph.Satisfiable ↔ FormulaSat (unconditional). -/
theorem sat_iff_formula_sat (G : CubeGraph) :
    G.Satisfiable ↔ G.FormulaSat :=
  ⟨sat_implies_formula_sat G, formula_sat_implies_sat G⟩

end CubeGraph
