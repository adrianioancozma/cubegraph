/-
  CubeGraph/Theorems.lean
  Core theorems of the 3-CUBES framework.

  Proven:
    - rank_zero_unsat: zero transfer operator ⟹ UNSAT
    - locality: constraints decompose into local (per-edge) checks
    - cycle_trace_iff_satisfiable: cycle satisfiability ↔ trace of composed operator
    - transferOp_transpose: σ(c₁,c₂) = σ(c₂,c₁)ᵀ
    - chain_semantics: chainOperator entry ↔ PathExists
    - seven_gaps_structure: 7-gap cube has unique non-gap vertex
    - sat_implies_no_dead: satisfiable ⟹ no dead cubes

  See: theory/theorems/THEOREM-A-HIERARCHY.md (hierarchy context)
  See: theory/theorems/CORE-THEOREMS-SUMMARY.md (full theorem inventory)
-/

import CubeGraph.Basic

namespace CubeGraph

/-! ## Theorem 1: Zero operator implies UNSAT -/

/-- If the transfer operator on any edge is the zero matrix,
    no gap selection can satisfy that edge ⟹ graph is unsatisfiable.

    This is the ONLY universal UNSAT marker across all topologies
    (verified empirically on 7 topologies, see SPECTRAL-FINGERPRINT-FINDINGS.md). -/
theorem rank_zero_unsat (G : CubeGraph)
    (i j : Fin G.cubes.length)
    (edge_exists : (i, j) ∈ G.edges)
    (h_zero : ∀ g₁ g₂ : Vertex, transferOp (G.cubes[i]) (G.cubes[j]) g₁ g₂ = false) :
    ¬ G.Satisfiable := by
  intro ⟨s, _, hcompat⟩
  have h_edge := hcompat (i, j) edge_exists
  have h_false := h_zero (s i) (s j)
  rw [h_false] at h_edge
  exact Bool.false_ne_true h_edge

/-! ## Theorem 2: Locality (Markov property) -/

/-- The constraints on node i decompose into:
    (a) s(i) ∈ gaps(i)
    (b) ∀ neighbor j: transferOp(i,j)(s(i), s(j)) = true
    No constraint involves nodes at distance > 1 from i. -/
theorem locality (G : CubeGraph) (s : GapSelection G)
    (i : Fin G.cubes.length) :
    (G.cubes[i]).isGap (s i) = true ∧
    (∀ e ∈ G.edges, e.1 = i → transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true) ∧
    (∀ e ∈ G.edges, e.2 = i → transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true)
    ↔
    (G.cubes[i]).isGap (s i) = true ∧
    (∀ e ∈ G.edges, e.1 = i ∨ e.2 = i →
      transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true) := by
  constructor
  · intro ⟨hgap, hfwd, hbwd⟩
    exact ⟨hgap, fun e he hor => hor.elim (fun h => hfwd e he h) (fun h => hbwd e he h)⟩
  · intro ⟨hgap, hedge⟩
    exact ⟨hgap,
      fun e he h => hedge e he (Or.inl h),
      fun e he h => hedge e he (Or.inr h)⟩

/-! ## Theorem 3: Compose operators along a path -/

/-- Compose transfer operators along a chain of cubes.
    This is the core algebraic operation: chains of cubes
    reduce to a single 8×8 operator via boolean matrix multiplication. -/
def chainOperator (cubes : List Cube) : BoolMat 8 :=
  match cubes with
  | [] => BoolMat.one
  | [_] => BoolMat.one
  | c₁ :: c₂ :: rest =>
    BoolMat.mul (transferOp c₁ c₂) (chainOperator (c₂ :: rest))

/-- Key algebraic property: chains with the same operator are functionally equivalent.
    Two chains P₁, P₂ connecting the same endpoints with chainOperator P₁ = chainOperator P₂
    can be substituted without affecting satisfiability. -/
theorem chain_substitution (c_start c_end : Cube)
    (chain₁ chain₂ : List Cube)
    (h_eq : chainOperator (c_start :: chain₁ ++ [c_end]) = chainOperator (c_start :: chain₂ ++ [c_end])) :
    -- For any gap assignment at the endpoints,
    -- chain₁ admits a compatible internal assignment ↔ chain₂ does
    ∀ g_s g_e : Vertex,
      chainOperator (c_start :: chain₁ ++ [c_end]) g_s g_e =
      chainOperator (c_start :: chain₂ ++ [c_end]) g_s g_e := by
  intro g_s g_e
  rw [h_eq]

/-! ## Theorem 4: Cycle trace -/

/-- The cycle operator: compose operators around a cycle and check the diagonal.
    For a cycle [c₁, c₂, ..., cₖ]:
      cycleOp = transferOp(c₁,c₂) ⊗ transferOp(c₂,c₃) ⊗ ... ⊗ transferOp(cₖ,c₁) -/
def cycleOp (cycle : List Cube) (h : cycle.length ≥ 2) : BoolMat 8 :=
  match cycle with
  | c₁ :: rest =>
    match rest.getLast? with
    | some cₖ => BoolMat.mul (chainOperator (c₁ :: rest)) (transferOp cₖ c₁)
    | none => BoolMat.one  -- unreachable given h
  | [] => BoolMat.one  -- unreachable given h

/-- Path semantics: a sequence of gaps through a chain of cubes, respecting constraints. -/
def PathExists : List Cube → Vertex → Vertex → Prop
  | [], g_s, g_e => g_s = g_e  -- Empty path: must be same vertex
  | [_], g_s, g_e => g_s = g_e  -- Single cube: must be same vertex
  | c₁ :: c₂ :: rest, g_s, g_e =>
    ∃ g_mid : Vertex, transferOp c₁ c₂ g_s g_mid = true ∧
      PathExists (c₂ :: rest) g_mid g_e

/-- Cycle satisfiability: path exists around the cycle closing at same gap. -/
def CycleSatisfiable : List Cube → Prop
  | [] => False
  | [_] => False  -- Single cube cannot form a cycle (need ≥ 2)
  | c₁ :: rest =>
    match rest.getLast? with
    | some cₖ => ∃ g g_last : Vertex,
        PathExists (c₁ :: rest) g g_last ∧
        transferOp cₖ c₁ g_last g = true  -- Close the cycle
    | none => False

/-- Key lemma: chainOperator semantics via PathExists -/
theorem chain_semantics (cubes : List Cube) (g_s g_e : Vertex) :
    chainOperator cubes g_s g_e = true ↔ PathExists cubes g_s g_e := by
  induction cubes generalizing g_s g_e with
  | nil =>
    simp [chainOperator, PathExists, BoolMat.one_apply_true]
  | cons c₁ rest ih =>
    cases rest with
    | nil =>
      simp [chainOperator, PathExists, BoolMat.one_apply_true]
    | cons c₂ rest' =>
      simp only [chainOperator, PathExists]
      rw [BoolMat.mul_apply_true]
      constructor
      · intro ⟨g_mid, h1, h2⟩
        exact ⟨g_mid, h1, (ih g_mid g_e).mp h2⟩
      · intro ⟨g_mid, h1, h2⟩
        exact ⟨g_mid, h1, (ih g_mid g_e).mpr h2⟩

/-- **Theorem (Cycle Trace Semantics)**:
    A cycle in the CubeGraph is satisfiable (admits a compatible gap selection
    for all cubes on the cycle) if and only if the trace of the cycle operator is true.

    trace(cycleOp) = ∨_g cycleOp[g,g]
                   = "can some gap come back to itself after traversing the cycle?"

    This is the algebraic foundation for the cycle-based analysis of satisfiability.

    Proof structure (Template 3 — match elimination + semantic chain):
      (1) Eliminate impossible match arms: since h : cycle.length ≥ 2, cycle must be
          c₁ :: c₂ :: rest'. The [] and [_] arms are dead.
      (2) With rest = c₂ :: rest' nonempty, rest.getLast? = some cₖ deterministically.
          Both cycleOp and CycleSatisfiable reduce to the same cₖ.
      (3) Unfold trace via trace_true: ∃ g, M g g = true.
      (4) Unfold matrix product via mul_apply_true: ∃ g_last, chain g g_last ∧ back g_last g.
      (5) Convert chain to path via chain_semantics.
      (6) The resulting iff is exactly CycleSatisfiable (c₁ :: rest). -/
theorem cycle_trace_iff_satisfiable (cycle : List Cube) (h : cycle.length ≥ 2) :
    BoolMat.trace (cycleOp cycle h) = true ↔ CycleSatisfiable cycle := by
  -- Step 1: since cycle.length ≥ 2, eliminate the [] and [_] arms
  match cycle, h with
  | c₁ :: c₂ :: rest', _ =>
    -- Now cycle = c₁ :: c₂ :: rest'; let rest = c₂ :: rest' (nonempty)
    have hne : (c₂ :: rest') ≠ [] := List.cons_ne_nil _ _
    -- Step 2: both cycleOp and CycleSatisfiable reduce via the same getLast?
    -- Rewrite getLast? as some (getLast rest hne) so the match arms collapse
    simp only [cycleOp, CycleSatisfiable, List.getLast?_eq_some_getLast hne]
    -- After unfolding: LHS = trace (mul (chainOperator cycle) (transferOp cₖ c₁)) = true
    --                  RHS = ∃ g g_last, PathExists cycle g g_last ∧ transferOp cₖ c₁ g_last g = true
    -- Step 3: unfold trace
    rw [BoolMat.trace_true]
    -- Goal: (∃ g, (mul (chainOperator …) (transferOp cₖ c₁)) g g = true) ↔ ∃ g g_last, …
    constructor
    · -- Forward: diagonal entry true → CycleSatisfiable
      intro ⟨g, hg⟩
      -- Step 4: unfold the product entry
      rw [BoolMat.mul_apply_true] at hg
      obtain ⟨g_last, h_chain, h_back⟩ := hg
      -- Step 5: convert chain operator entry to PathExists
      rw [chain_semantics] at h_chain
      exact ⟨g, g_last, h_chain, h_back⟩
    · -- Backward: CycleSatisfiable → diagonal entry true
      intro ⟨g, g_last, h_path, h_back⟩
      refine ⟨g, ?_⟩
      rw [BoolMat.mul_apply_true]
      exact ⟨g_last, (chain_semantics _ _ _).mpr h_path, h_back⟩

/-! ## Theorem 5: Transfer operator symmetry -/

/-- Helper: shared variables are symmetric as sets.
    If sv ∈ sharedVars c₁ c₂ then sv ∈ sharedVars c₂ c₁. -/
private theorem sharedVars_mem_comm (c₁ c₂ : Cube) (sv : Nat) :
    sv ∈ Cube.sharedVars c₁ c₂ ↔ sv ∈ Cube.sharedVars c₂ c₁ := by
  simp [Cube.sharedVars, Cube.vars, List.mem_filter, List.mem_cons]
  constructor
  · intro ⟨hc2, hc1⟩; exact ⟨hc1, hc2⟩
  · intro ⟨hc1, hc2⟩; exact ⟨hc2, hc1⟩

/-- Helper: bit compatibility is symmetric.
    The comparison ((g₁.val >>> idx₁) &&& 1) == ((g₂.val >>> idx₂) &&& 1)
    is symmetric: swapping g₁↔g₂ and idx₁↔idx₂ gives the same value. -/
private theorem bitCompat_comm (g₁ g₂ : Vertex) (idx₁ idx₂ : Nat) :
    (((g₁.val >>> idx₁) &&& 1) == ((g₂.val >>> idx₂) &&& 1)) =
    (((g₂.val >>> idx₂) &&& 1) == ((g₁.val >>> idx₁) &&& 1)) := by
  -- (a == b) = (b == a) by symmetry of decidable equality
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact eq_comm

/-- Helper: the all-check over sharedVars c₁ c₂ equals the all-check over sharedVars c₂ c₁
    when the predicate is bit-equality (which is symmetric). -/
private theorem sharedVars_all_comm (c₁ c₂ : Cube) (g₁ g₂ : Vertex) :
    (Cube.sharedVars c₁ c₂).all (fun sv =>
      let idx₁ := c₁.vars.idxOf sv
      let idx₂ := c₂.vars.idxOf sv
      ((g₁.val >>> idx₁) &&& 1) == ((g₂.val >>> idx₂) &&& 1)) =
    (Cube.sharedVars c₂ c₁).all (fun sv =>
      let idx₁ := c₂.vars.idxOf sv
      let idx₂ := c₁.vars.idxOf sv
      ((g₂.val >>> idx₁) &&& 1) == ((g₁.val >>> idx₂) &&& 1)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro h sv hmem
    rw [sharedVars_mem_comm] at hmem
    have := h sv hmem
    simp only at this ⊢
    rw [bitCompat_comm]
    exact this
  · intro h sv hmem
    have hmem' : sv ∈ Cube.sharedVars c₂ c₁ := (sharedVars_mem_comm c₁ c₂ sv).mp hmem
    have := h sv hmem'
    simp only at this ⊢
    rw [bitCompat_comm]
    exact this

/-- **Theorem**: Transfer operators are symmetric under transpose.
    transferOp c₁ c₂ = (transferOp c₂ c₁)ᵀ

    This holds because:
    - M[g₁,g₂] = c₁.isGap g₁ ∧ c₂.isGap g₂ ∧ shared vars compatible
    - Mᵀ[g₁,g₂] = M[g₂,g₁] = c₂.isGap g₂ ∧ c₁.isGap g₁ ∧ same compatibility
    Both are equal (AND is commutative, bit-equality is symmetric). -/
theorem transferOp_transpose (c₁ c₂ : Cube) :
    transferOp c₁ c₂ = (transferOp c₂ c₁).transpose := by
  funext g₁ g₂
  simp only [BoolMat.transpose_apply, transferOp]
  -- LHS: c₁.isGap g₁ && c₂.isGap g₂ && all(sharedVars c₁ c₂, compat g₁ g₂)
  -- RHS: c₂.isGap g₂ && c₁.isGap g₁ && all(sharedVars c₂ c₁, compat g₂ g₁)
  -- Rewrite as iff on Bool, then split into three conjuncts
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  constructor
  · intro ⟨⟨hg1, hg2⟩, hall⟩
    refine ⟨⟨hg2, hg1⟩, ?_⟩
    rwa [← sharedVars_all_comm]
  · intro ⟨⟨hg2, hg1⟩, hall⟩
    refine ⟨⟨hg1, hg2⟩, ?_⟩
    rwa [sharedVars_all_comm]

/-! ## Counting helpers -/

/-- Complement counting: p-count + not-p-count = length -/
theorem countP_complement (p : α → Bool) (l : List α) :
    l.countP p + l.countP (fun x => !p x) = l.length := by
  induction l with
  | nil => simp [List.countP_nil]
  | cons x xs ih =>
    cases hpx : p x
    · rw [List.countP_cons_of_neg (by simp [hpx]),
          List.countP_cons_of_pos (by simp [hpx]),
          List.length_cons]; omega
    · rw [List.countP_cons_of_pos hpx,
          List.countP_cons_of_neg (by simp [hpx]),
          List.length_cons]; omega

/-- Two distinct witnesses imply countP ≥ 2 -/
theorem countP_ge_two [DecidableEq α] (p : α → Bool) {l : List α} {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) (hpa : p a = true) (hpb : p b = true) :
    2 ≤ l.countP p := by
  induction l with
  | nil => exact absurd ha List.not_mem_nil
  | cons x xs ih =>
    cases hpx : p x
    · rw [List.countP_cons_of_neg (by simp [hpx])]
      exact ih
        (by rcases List.mem_cons.mp ha with h | h
            · rw [h] at hpa; exact absurd (hpa.symm.trans hpx) (by decide)
            · exact h)
        (by rcases List.mem_cons.mp hb with h | h
            · rw [h] at hpb; exact absurd (hpb.symm.trans hpx) (by decide)
            · exact h)
    · rw [List.countP_cons_of_pos hpx]
      by_cases hax : a = x
      · have hb_xs : b ∈ xs := by
          rcases List.mem_cons.mp hb with h | h
          · exfalso; exact hab (hax.trans h.symm)
          · exact h
        have := List.countP_pos_iff.mpr ⟨b, hb_xs, hpb⟩; omega
      · have ha_xs : a ∈ xs := by
          rcases List.mem_cons.mp ha with h | h
          · exact absurd h hax
          · exact h
        have := List.countP_pos_iff.mpr ⟨a, ha_xs, hpa⟩; omega

/-! ## Theorem 5: Gap count invariants -/

/-- A cube with 7 gaps (1 filled vertex) has exactly one non-gap vertex.
    The gap tensor T ∈ {0,1}^{2×2×2} is the all-ones tensor minus one basis element.
    This forces rank-2 on every matricization axis. -/
theorem seven_gaps_structure (c : Cube) (h : c.gapCount = 7) :
    ∃ v : Vertex, c.isGap v = false ∧ ∀ w : Vertex, c.isGap w = false → w = v := by
  -- Step 1: complement counting
  simp only [Cube.gapCount] at h
  have hcomp := countP_complement (fun v => c.isGap v) (List.finRange 8)
  have hlen : (List.finRange 8).length = 8 := List.length_finRange
  rw [hlen] at hcomp
  -- hcomp : countP (isGap c) + countP (fun x => !isGap c x) = 8
  -- h : countP (isGap c) = 7
  -- Need: countP (fun v => !isGap c v) = 1
  -- The complement in hcomp uses (fun x => ...) which is alpha-eq to (fun v => ...)
  have h_neg : (List.finRange 8).countP (fun v => !c.isGap v) = 1 := by omega
  -- Step 2: existence from countP = 1 > 0
  have h_pos : 0 < (List.finRange 8).countP (fun v => !c.isGap v) := by omega
  obtain ⟨v, _, hv_neg⟩ := List.countP_pos_iff.mp h_pos
  have hv_gap : c.isGap v = false := by
    cases hg : c.isGap v
    · rfl
    · exact absurd hv_neg (by simp [hg])
  -- Step 3: uniqueness via counting contradiction
  refine ⟨v, hv_gap, fun w hw => ?_⟩
  by_cases heq : w = v
  · exact heq
  · exfalso
    have h_ge2 := countP_ge_two (fun x => !c.isGap x)
      (BoolMat.mem_finRange v) (BoolMat.mem_finRange w) (Ne.symm heq)
      (by simp [hv_gap]) (by simp [hw])
    omega

/-! ## Corollary: satisfiable implies no dead cubes -/

/-- If a CubeGraph is satisfiable, every cube must have at least one gap. -/
theorem sat_implies_no_dead (G : CubeGraph) (h : G.Satisfiable) :
    ∀ i : Fin G.cubes.length, (G.cubes[i]).gapCount > 0 := by
  intro i
  obtain ⟨s, hvalid, _⟩ := h
  have hgap := hvalid i
  exact List.countP_pos_iff.mpr ⟨s i, BoolMat.mem_finRange _, hgap⟩

end CubeGraph
