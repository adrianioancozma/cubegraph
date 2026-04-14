/-
  CubeGraph/PigeonholeSelfLoop.lean
  PIGEONHOLE SELF-LOOP THEOREM: Rich cubes force transfer operator self-loops.

  Core argument (three-level pigeonhole):
  1. Two subsets of Fin 8 with combined size > 8 must intersect (basic pigeonhole).
  2. A gap g in both cubes contributes a self-loop M[g,g] = true only if the shared
     variable's bits at positions p₁ (in c₁) and p₂ (in c₂) agree: g.bit(p₁) = g.bit(p₂).
  3. For vertices in Fin 8, the set where bit(p₁) = bit(p₂) has size:
     - 8 if p₁ = p₂ (trivially all agree)
     - 4 if p₁ ≠ p₂ (half agree, half disagree)
     So the self-loop-eligible set has 4 or 8 elements.
  4. At ρ_c (~7/8 gaps): each cube contributes ≥ 3 gaps to the eligible set
     (only 4 slots outside, and 7 gaps total). 3 + 3 = 6 > 4 → intersection → self-loop.
  5. H² witness (2 gaps each): 2 + 2 = 4 ≤ 8 → no pigeonhole → self-loop avoidable.

  Key theorems:
  - pigeonhole_fin8:              |P| + |Q| > 8 → P ∩ Q ≠ ∅
  - gap_intersection_of_rich:     gapCount c₁ + gapCount c₂ > 8 → ∃ common gap
  - selfloop_same_position:       same-position + ≥ 5 gaps → self-loop
  - critical_density_selfloop:    7 gaps + any positions → self-loop
  - critical_density_idempotent:  7 gaps + rank-1 → M² = M
  - h2_below_threshold:           H² has 2+2 = 4 ≤ 8 (escapes pigeonhole)
  - pigeonhole_dichotomy:         above threshold → self-loop; below → can avoid
  - selfloop_persists_composition: self-loops compose

  See: MisalignedComposition.lean (gap coverage → rank-1)
  See: BoolMat.lean (fixedPoint_mul: self-loops persist under composition)
  See: Rank1Algebra.lean (rank1_idempotent: trace + rank-1 → M² = M)
-/

import CubeGraph.MisalignedComposition

namespace CubeGraph

open BoolMat

/-! ## Part 1: Counting Infrastructure

  Helper lemmas for Bool predicates on Fin n, building the pigeonhole argument
  from countP properties available in the codebase.

  NOTE: Lean 4.29's omega tactic creates distinct integer variables for
  syntactically different but alpha-equivalent lambda expressions in countP.
  We work around this using `generalize ... at *` to name countP values. -/

/-- Disjoint predicates: countP(P) + countP(Q) ≤ length when P and Q have no common true.
    Core of the pigeonhole argument. -/
private theorem countP_disjoint_le {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x, x ∈ l → ¬(p x = true ∧ q x = true)) :
    l.countP p + l.countP q ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons, List.length_cons]
    have ih' := ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    have ha := h a (List.mem_cons.mpr (Or.inl rfl))
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

/-- Conjunction lower bound: countP(P ∧ Q) + length ≥ countP(P) + countP(Q).
    Equivalently: countP(P ∧ Q) ≥ countP(P) + countP(Q) - length.
    Stated additively to avoid subtraction on Nat. -/
private theorem countP_conj_lb (P Q : Fin 8 → Bool) :
    (List.finRange 8).countP (fun v => P v && Q v) + 8 ≥
    (List.finRange 8).countP (fun v => P v) + (List.finRange 8).countP (fun v => Q v) := by
  suffices h1 : (List.finRange 8).countP (fun v => P v && Q v) +
                (List.finRange 8).countP (fun v => !(Q v)) ≥
                (List.finRange 8).countP (fun v => P v) by
    have h2 : (List.finRange 8).countP (fun v => Q v) +
              (List.finRange 8).countP (fun v => !(Q v)) = 8 := by
      have := countP_complement (fun v => Q v) (List.finRange 8)
      rw [List.length_finRange] at this; exact this
    omega
  generalize (List.finRange 8) = l
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    cases hp : P a <;> cases hq : Q a <;> simp_all <;> omega

/-! ## Part 2: Pigeonhole on Fin 8

  The core combinatorial fact: two Bool predicates on Fin 8 with
  combined true-counts exceeding 8 must share a common true element. -/

/-- **Pigeonhole on Fin 8**: if two Bool predicates on Fin 8 have combined
    true-counts exceeding 8, there exists an element where both are true.

    Proof: contrapositive. If no common element, the predicates are disjoint
    on the 8-element universe, so their counts sum to at most 8. -/
theorem pigeonhole_fin8 (P Q : Fin 8 → Bool)
    (h : (List.finRange 8).countP (fun v => P v) +
         (List.finRange 8).countP (fun v => Q v) > 8) :
    ∃ i : Fin 8, P i = true ∧ Q i = true := by
  exact Classical.byContradiction fun h_neg => by
    have h_forall : ∀ i : Fin 8, ¬(P i = true ∧ Q i = true) := by
      intro i ⟨hp, hq⟩; exact h_neg ⟨i, hp, hq⟩
    have h_le := countP_disjoint_le (List.finRange 8) P Q (fun x _ => h_forall x)
    rw [List.length_finRange] at h_le
    generalize (List.finRange 8).countP (fun v => P v) = np at *
    generalize (List.finRange 8).countP (fun v => Q v) = nq at *
    omega

/-! ## Part 3: Gap Set Intersection

  If two cubes have enough gaps (combined count > 8), their gap sets
  must intersect: there exists a vertex that is a gap in both cubes. -/

/-- **Gap intersection**: if the combined gap count of two cubes exceeds 8,
    there exists a vertex that is a gap in both.
    Threshold: gapCount c₁ + gapCount c₂ > 8. -/
theorem gap_intersection_of_rich (c₁ c₂ : Cube)
    (h : c₁.gapCount + c₂.gapCount > 8) :
    ∃ g : Vertex, c₁.isGap g = true ∧ c₂.isGap g = true := by
  unfold Cube.gapCount at h
  exact pigeonhole_fin8 c₁.isGap c₂.isGap h

/-- Both cubes with ≥ 5 gaps guarantees intersection (5 + 5 = 10 > 8). -/
theorem gap_intersection_of_five (c₁ c₂ : Cube)
    (h₁ : c₁.gapCount ≥ 5) (h₂ : c₂.gapCount ≥ 5) :
    ∃ g : Vertex, c₁.isGap g = true ∧ c₂.isGap g = true :=
  gap_intersection_of_rich c₁ c₂ (by omega)

/-! ## Part 4: Self-Loop from Common Gap

  When a vertex g is a gap in both cubes, the transfer operator's diagonal
  entry M[g,g] depends on whether the shared variable's bits agree at the
  respective positions.

  Key subtlety: transferOp c₁ c₂ g g checks that for each shared variable sv,
  g.bit(idxOf sv in c₁) = g.bit(idxOf sv in c₂). When the shared variable
  is at DIFFERENT positions in the two cubes, this is NOT trivially true. -/

/-- Self-loop for common gap with compatible bits. -/
theorem selfloop_of_compatible_gap (c₁ c₂ : Cube) (g : Vertex)
    (hg₁ : c₁.isGap g = true) (hg₂ : c₂.isGap g = true)
    (hcompat : (Cube.sharedVars c₁ c₂).all (fun sv =>
      ((g.val >>> c₁.vars.idxOf sv) &&& 1) ==
      ((g.val >>> c₂.vars.idxOf sv) &&& 1)) = true) :
    transferOp c₁ c₂ g g = true :=
  gaps_and_compat_implies_transferOp c₁ c₂ g g hg₁ hg₂ hcompat

/-- Self-loop implies trace is true. -/
theorem trace_of_selfloop (c₁ c₂ : Cube) (g : Vertex)
    (h : transferOp c₁ c₂ g g = true) :
    (transferOp c₁ c₂).trace = true :=
  (trace_true _).mpr ⟨g, h⟩

/-! ## Part 5: Eligible Vertices for Self-Loop

  For a shared variable at positions p₁ and p₂, the "eligible" vertices
  for self-loops are those where bit(p₁) = bit(p₂). -/

/-- A vertex is eligible for self-loop: bit(p₁) = bit(p₂). -/
private def isEligible (p₁ p₂ : Fin 3) (v : Vertex) : Bool :=
  ((v.val >>> p₁.val) &&& 1) == ((v.val >>> p₂.val) &&& 1)

/-- When p₁ = p₂, all 8 vertices are eligible. -/
theorem all_eligible_same_pos (p : Fin 3) (v : Vertex) :
    isEligible p p v = true := by
  revert p v; native_decide

/-- When p₁ ≠ p₂, exactly 4 vertices are eligible. -/
private theorem eligible_count_diff_pos (p₁ p₂ : Fin 3) (hne : p₁ ≠ p₂) :
    (List.finRange 8).countP (fun v => isEligible p₁ p₂ v) = 4 := by
  revert hne p₁ p₂; native_decide

/-- Eligible count is always ≥ 4 (regardless of whether positions match). -/
private theorem eligible_count_ge_4 (p₁ p₂ : Fin 3) :
    (List.finRange 8).countP (fun v => isEligible p₁ p₂ v) ≥ 4 := by
  rcases Classical.em (p₁ = p₂) with rfl | hne
  · -- Same position: all 8 eligible
    have : ∀ v : Fin 8, v ∈ List.finRange 8 → isEligible p₁ p₁ v = true := by
      intro v _; revert v p₁; native_decide
    have h := List.countP_eq_length.mpr this
    rw [List.length_finRange] at h
    generalize (List.finRange 8).countP (fun v => isEligible p₁ p₁ v) = n at *
    omega
  · -- Different positions: exactly 4
    have := eligible_count_diff_pos p₁ p₂ hne
    generalize (List.finRange 8).countP (fun v => isEligible p₁ p₂ v) = n at *
    omega

/-- Eligible gap gives self-loop when cubes share exactly one variable. -/
theorem selfloop_from_eligible_gap (c₁ c₂ : Cube) (v_shared : Nat)
    (p₁ : Fin 3) (p₂ : Fin 3)
    (hsv : SingleSharedVar c₁ c₂ v_shared)
    (hp₁ : c₁.vars.idxOf v_shared = p₁.val)
    (hp₂ : c₂.vars.idxOf v_shared = p₂.val)
    (g : Vertex) (hg₁ : c₁.isGap g = true) (hg₂ : c₂.isGap g = true)
    (helig : isEligible p₁ p₂ g = true) :
    transferOp c₁ c₂ g g = true := by
  apply gaps_and_compat_implies_transferOp c₁ c₂ g g hg₁ hg₂
  rw [hsv]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [hp₁, hp₂]
  exact helig

/-! ## Part 6: Same-Position Self-Loop (Threshold k ≥ 5)

  When the shared variable is at the SAME position in both cubes,
  every common gap gives a self-loop. -/

/-- **Self-loop (same position)**: shared variable at same position + ≥ 5 gaps each
    guarantees a self-loop (bit(p) = bit(p) always holds). -/
theorem selfloop_same_position (c₁ c₂ : Cube) (v_shared : Nat) (p : Fin 3)
    (hsv : SingleSharedVar c₁ c₂ v_shared)
    (hp₁ : c₁.vars.idxOf v_shared = p.val)
    (hp₂ : c₂.vars.idxOf v_shared = p.val)
    (hk₁ : c₁.gapCount ≥ 5) (hk₂ : c₂.gapCount ≥ 5) :
    ∃ g : Vertex, transferOp c₁ c₂ g g = true := by
  obtain ⟨g, hg₁, hg₂⟩ := gap_intersection_of_five c₁ c₂ hk₁ hk₂
  exact ⟨g, selfloop_from_eligible_gap c₁ c₂ v_shared p p hsv hp₁ hp₂ g hg₁ hg₂
    (all_eligible_same_pos p g)⟩

/-! ## Part 7: Critical Density Self-Loop (Threshold k ≥ 7)

  The main theorem: with 7 gaps each and any shared variable positions,
  a self-loop is guaranteed.

  Counting chain (two-step inclusion-exclusion):
  1. |gap₁ ∩ gap₂| ≥ k₁ + k₂ - 8 = 7 + 7 - 8 = 6
  2. |gap₁ ∩ gap₂ ∩ eligible| ≥ 6 + 4 - 8 = 2 > 0 -/

/-- **Critical density self-loop**: with 7 gaps each and any shared variable
    positions, a self-loop is guaranteed. At ρ_c cubes have ~7/8 gaps. -/
theorem critical_density_selfloop (c₁ c₂ : Cube) (v_shared : Nat)
    (p₁ p₂ : Fin 3)
    (hsv : SingleSharedVar c₁ c₂ v_shared)
    (hp₁ : c₁.vars.idxOf v_shared = p₁.val)
    (hp₂ : c₂.vars.idxOf v_shared = p₂.val)
    (hk₁ : c₁.gapCount ≥ 7) (hk₂ : c₂.gapCount ≥ 7) :
    ∃ g : Vertex, transferOp c₁ c₂ g g = true := by
  unfold Cube.gapCount at hk₁ hk₂
  -- Suffices: prove countP > 0, then extract witness
  suffices h_pos : 0 < (List.finRange 8).countP
      (fun v => c₁.isGap v && c₂.isGap v && isEligible p₁ p₂ v) by
    obtain ⟨g, _, hg⟩ := List.countP_pos_iff.mp h_pos
    simp only [Bool.and_eq_true] at hg
    obtain ⟨⟨hg₁, hg₂⟩, hgE⟩ := hg
    exact ⟨g, selfloop_from_eligible_gap c₁ c₂ v_shared p₁ p₂ hsv hp₁ hp₂ g hg₁ hg₂ hgE⟩
  -- Prove countP > 0 via two-step inclusion-exclusion
  have h_step1 := countP_conj_lb c₁.isGap c₂.isGap
  have h_step2 := countP_conj_lb (fun v => c₁.isGap v && c₂.isGap v) (isEligible p₁ p₂)
  have h_elig := eligible_count_ge_4 p₁ p₂
  -- Generalize all countP values to fix omega's variable confusion
  generalize (List.finRange 8).countP
    (fun v => c₁.isGap v && c₂.isGap v && isEligible p₁ p₂ v) = n_triple at *
  generalize (List.finRange 8).countP
    (fun v => c₁.isGap v && c₂.isGap v) = n_pq at *
  generalize (List.finRange 8).countP
    (fun v => isEligible p₁ p₂ v) = n_e at *
  generalize (List.finRange 8).countP
    (fun v => c₁.isGap v) = n_p at *
  generalize (List.finRange 8).countP
    (fun v => c₂.isGap v) = n_q at *
  omega

/-- Trace is true at critical density for any shared variable positions. -/
theorem critical_density_trace (c₁ c₂ : Cube) (v_shared : Nat)
    (p₁ p₂ : Fin 3)
    (hsv : SingleSharedVar c₁ c₂ v_shared)
    (hp₁ : c₁.vars.idxOf v_shared = p₁.val)
    (hp₂ : c₂.vars.idxOf v_shared = p₂.val)
    (hk₁ : c₁.gapCount ≥ 7) (hk₂ : c₂.gapCount ≥ 7) :
    (transferOp c₁ c₂).trace = true := by
  obtain ⟨g, hg⟩ := critical_density_selfloop c₁ c₂ v_shared p₁ p₂ hsv hp₁ hp₂ hk₁ hk₂
  exact trace_of_selfloop c₁ c₂ g hg

/-! ## Part 8: Trace and Idempotence Consequences -/

/-- Same-position rich cubes have positive trace. -/
theorem rich_cubes_have_trace (c₁ c₂ : Cube) (v_shared : Nat) (p : Fin 3)
    (hsv : SingleSharedVar c₁ c₂ v_shared)
    (hp₁ : c₁.vars.idxOf v_shared = p.val)
    (hp₂ : c₂.vars.idxOf v_shared = p.val)
    (hk₁ : c₁.gapCount ≥ 5) (hk₂ : c₂.gapCount ≥ 5) :
    (transferOp c₁ c₂).trace = true := by
  obtain ⟨g, hg⟩ := selfloop_same_position c₁ c₂ v_shared p hsv hp₁ hp₂ hk₁ hk₂
  exact trace_of_selfloop c₁ c₂ g hg

/-- **Idempotence (same position)**: rank-1 + ≥ 5 gaps + same position → M² = M. -/
theorem rich_cubes_idempotent (c₁ c₂ : Cube) (v_shared : Nat) (p : Fin 3)
    (hsv : SingleSharedVar c₁ c₂ v_shared)
    (hp₁ : c₁.vars.idxOf v_shared = p.val)
    (hp₂ : c₂.vars.idxOf v_shared = p.val)
    (hk₁ : c₁.gapCount ≥ 5) (hk₂ : c₂.gapCount ≥ 5)
    (hrank : (transferOp c₁ c₂).IsRankOne) :
    mul (transferOp c₁ c₂) (transferOp c₁ c₂) = transferOp c₁ c₂ :=
  rank1_idempotent hrank
    (rich_cubes_have_trace c₁ c₂ v_shared p hsv hp₁ hp₂ hk₁ hk₂)

/-- **Idempotence (any position)**: rank-1 + ≥ 7 gaps → M² = M. -/
theorem critical_density_idempotent (c₁ c₂ : Cube) (v_shared : Nat)
    (p₁ p₂ : Fin 3)
    (hsv : SingleSharedVar c₁ c₂ v_shared)
    (hp₁ : c₁.vars.idxOf v_shared = p₁.val)
    (hp₂ : c₂.vars.idxOf v_shared = p₂.val)
    (hk₁ : c₁.gapCount ≥ 7) (hk₂ : c₂.gapCount ≥ 7)
    (hrank : (transferOp c₁ c₂).IsRankOne) :
    mul (transferOp c₁ c₂) (transferOp c₁ c₂) = transferOp c₁ c₂ :=
  rank1_idempotent hrank
    (critical_density_trace c₁ c₂ v_shared p₁ p₂ hsv hp₁ hp₂ hk₁ hk₂)

/-! ## Part 9: H² Witness Escapes Pigeonhole

  The H² witness cubes have only 2 gaps each (2+2 = 4 ≤ 8), so the
  pigeonhole argument does NOT apply. Sparse gap sets can be arranged to
  avoid self-loops, enabling anti-diagonal operators that create UNSAT. -/

/-- H² cube A has exactly 2 gaps. -/
theorem h2CubeA_gapCount : h2CubeA.gapCount = 2 := by native_decide

/-- H² cube B has exactly 2 gaps. -/
theorem h2CubeB_gapCount : h2CubeB.gapCount = 2 := by native_decide

/-- H² cube C has exactly 2 gaps. -/
theorem h2CubeC_gapCount : h2CubeC.gapCount = 2 := by native_decide

/-- H² witness is below the pigeonhole threshold: 2 + 2 = 4 ≤ 8. -/
theorem h2_below_threshold :
    h2CubeA.gapCount + h2CubeB.gapCount ≤ 8 ∧
    h2CubeB.gapCount + h2CubeC.gapCount ≤ 8 ∧
    h2CubeA.gapCount + h2CubeC.gapCount ≤ 8 := by
  simp only [h2CubeA_gapCount, h2CubeB_gapCount, h2CubeC_gapCount]; omega

/-- H² A→B has NO self-loop (trace = false): anti-diagonal structure. -/
theorem h2_AB_no_selfloop : (transferOp h2CubeA h2CubeB).trace = false := by
  native_decide

/-- H² B→C has NO self-loop. -/
theorem h2_BC_no_selfloop : (transferOp h2CubeB h2CubeC).trace = false := by
  native_decide

/-- H² edges A→B and B→C are trace-free.
    Note: C→A DOES have self-loops (cubes share gaps {0,3} and variable 2 at
    position 0 in both). The cycle is UNSAT because the intermediate edges lack them. -/
theorem h2_critical_edges_trace_free :
    (transferOp h2CubeA h2CubeB).trace = false ∧
    (transferOp h2CubeB h2CubeC).trace = false :=
  ⟨h2_AB_no_selfloop, h2_BC_no_selfloop⟩

/-- C→A DOES have self-loops (cubes A and C share gap set {0,3}). -/
theorem h2_CA_has_selfloop : (transferOp h2CubeC h2CubeA).trace = true := by
  native_decide

/-! ## Part 10: Rank-1 H² Witness -/

/-- Rank-1 cube A has 2 gaps. -/
theorem r1CubeA_gapCount : r1CubeA.gapCount = 2 := by native_decide

/-- Rank-1 cube B has 4 gaps. -/
theorem r1CubeB_gapCount : r1CubeB.gapCount = 4 := by native_decide

/-- Rank-1 cube C has 2 gaps. -/
theorem r1CubeC_gapCount : r1CubeC.gapCount = 2 := by native_decide

/-- Rank-1 A→B has no self-loop (despite B having 4 gaps). -/
theorem r1_AB_no_selfloop : (transferOp r1CubeA r1CubeB).trace = false := by
  native_decide

/-- Rank-1 B→C has no self-loop. -/
theorem r1_BC_no_selfloop : (transferOp r1CubeB r1CubeC).trace = false := by
  native_decide

/-- Rank-1 C→A has self-loops (cubes share gap set {0,4}). -/
theorem r1_CA_has_selfloop : (transferOp r1CubeC r1CubeA).trace = true := by
  native_decide

/-! ## Part 11: Rich Cubes — Concrete Witnesses -/

/-- Rich cube 1: vars (1,2,3), 7 gaps (all except vertex 7). -/
def richCube1 : Cube where
  var₁ := 1
  var₂ := 2
  var₃ := 3
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨127, by omega⟩
  gaps_nonempty := by decide

/-- Rich cube 2: vars (1,4,5), 7 gaps. Same position for shared variable 1. -/
def richCube2 : Cube where
  var₁ := 1
  var₂ := 4
  var₃ := 5
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨127, by omega⟩
  gaps_nonempty := by decide

theorem richCube1_gapCount : richCube1.gapCount = 7 := by native_decide
theorem richCube2_gapCount : richCube2.gapCount = 7 := by native_decide
theorem rich_shared_vars : Cube.sharedVars richCube1 richCube2 = [1] := by native_decide

/-- Concrete witness: rich cubes have trace = true. -/
theorem rich_cubes_concrete_trace :
    (transferOp richCube1 richCube2).trace = true := by native_decide

/-- Same-position case: 7 self-loops out of 8 diagonal entries. -/
theorem rich_cubes_selfloop_count :
    (List.finRange 8).countP (fun g =>
      transferOp richCube1 richCube2 g g) = 7 := by native_decide

/-! ## Part 12: Different-Position Concrete Witness -/

/-- Rich cube 3: vars (4,1,5), 7 gaps. Variable 1 at position 1 (not 0). -/
def richCube3 : Cube where
  var₁ := 4
  var₂ := 1
  var₃ := 5
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨127, by omega⟩
  gaps_nonempty := by decide

theorem richCube3_gapCount : richCube3.gapCount = 7 := by native_decide

/-- Shared variable 1 at position 0 in richCube1, position 1 in richCube3. -/
theorem rich_diff_positions :
    Cube.sharedVars richCube1 richCube3 = [1] ∧
    richCube1.vars.idxOf 1 = 0 ∧
    richCube3.vars.idxOf 1 = 1 := by native_decide

/-- Different-position case still has self-loops (pigeonhole forces it). -/
theorem rich_diff_pos_trace :
    (transferOp richCube1 richCube3).trace = true := by native_decide

/-- Different positions: 3 self-loops (fewer than 7 — eligible set has only 4 vertices). -/
theorem rich_diff_pos_selfloop_count :
    (List.finRange 8).countP (fun g =>
      transferOp richCube1 richCube3 g g) = 3 := by native_decide

/-! ## Part 13: The Dichotomy

  - **Rich cubes (ρ_c)**: ≥ 7 gaps → pigeonhole forces self-loops →
    trace = true → rank-1 operators are idempotent (M² = M) →
    information is absorbed, SAT and UNSAT look identical locally.

  - **Sparse cubes (H²)**: 2 gaps → below threshold → self-loops avoidable →
    trace = false → anti-diagonal operators → UNSAT detectable. -/

/-- **The Pigeonhole Dichotomy**: above threshold → self-loop guaranteed;
    below threshold → self-loop avoidable (H² witness). -/
theorem pigeonhole_dichotomy :
    -- Part 1: same position, k ≥ 5 → self-loop
    (∀ c₁ c₂ : Cube, ∀ v : Nat, ∀ p : Fin 3,
      SingleSharedVar c₁ c₂ v → c₁.vars.idxOf v = p.val → c₂.vars.idxOf v = p.val →
      c₁.gapCount ≥ 5 → c₂.gapCount ≥ 5 →
      ∃ g, transferOp c₁ c₂ g g = true) ∧
    -- Part 2: any position, k ≥ 7 → self-loop
    (∀ c₁ c₂ : Cube, ∀ v : Nat, ∀ p₁ p₂ : Fin 3,
      SingleSharedVar c₁ c₂ v → c₁.vars.idxOf v = p₁.val → c₂.vars.idxOf v = p₂.val →
      c₁.gapCount ≥ 7 → c₂.gapCount ≥ 7 →
      ∃ g, transferOp c₁ c₂ g g = true) ∧
    -- Part 3: below threshold → self-loop avoidable
    (∃ c₁ c₂ : Cube, c₁.gapCount = 2 ∧ c₂.gapCount = 2 ∧
      (transferOp c₁ c₂).trace = false) :=
  ⟨fun c₁ c₂ v p hsv hp₁ hp₂ hk₁ hk₂ =>
    selfloop_same_position c₁ c₂ v p hsv hp₁ hp₂ hk₁ hk₂,
   fun c₁ c₂ v p₁ p₂ hsv hp₁ hp₂ hk₁ hk₂ =>
    critical_density_selfloop c₁ c₂ v p₁ p₂ hsv hp₁ hp₂ hk₁ hk₂,
   ⟨h2CubeA, h2CubeB, h2CubeA_gapCount, h2CubeB_gapCount, h2_AB_no_selfloop⟩⟩

/-- **Self-loop persistence**: self-loops compose. -/
theorem selfloop_persists_composition (c₁ c₂ c₃ c₄ : Cube) (g : Vertex)
    (h₁ : transferOp c₁ c₂ g g = true)
    (h₂ : transferOp c₃ c₄ g g = true) :
    (mul (transferOp c₁ c₂) (transferOp c₃ c₄)) g g = true :=
  fixedPoint_mul (transferOp c₁ c₂) (transferOp c₃ c₄) g h₁ h₂

end CubeGraph
