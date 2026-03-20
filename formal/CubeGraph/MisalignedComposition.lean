/-
  CubeGraph/MisalignedComposition.lean
  T4: Misaligned composition → rank-1.

  When edge(A,B) shares exactly one variable v₁ and edge(B,C) shares exactly
  one variable v₂ with v₁ ≠ v₂, the composed operator mul(transferOp A B)(transferOp B C)
  is rank-1 — provided cube B has "gap coverage" (all 4 bit-combinations on
  the positions of v₁ and v₂ appear among B's gaps).

  Root cause: the two operators constrain DIFFERENT bit positions in B. Any active
  source gap in A can reach any active target gap in C through some intermediate
  gap in B that satisfies both constraints independently.

  This formalizes T4 from the research plan (non-transitivity → rank-1).

  NOTE: The H² witness (h2CubeA/B/C) does NOT satisfy gap coverage — cube B
  has only 2 gaps ({1,2}), missing 2 of 4 bit combos on positions (0,1).
  Consequently the composed operator is rank-2 (anti-diagonal), not rank-1.
  T4 applies when B has ≥ 4 gaps covering all combos — the typical case at
  critical density where cubes have ~7/8 gaps.

  See: FullSupportComposition.lean (abstract mechanism: mul_full_support_rankOne)
  See: NonTransitivity.lean (concrete witness: compatibility_not_transitive)
  See: experiments-ml/019_.../brainstorm/PLAN-T4-NonTransitivity.md (plan)
-/

import CubeGraph.FullSupportComposition
import CubeGraph.NonTransitivity

namespace CubeGraph

open BoolMat

/-! ## Section 1: Definitions -/

/-- Two edges A→B and B→C have "disjoint shared variables": no variable is
    shared by both edges. This means the information transmitted through B
    on the first edge is independent of what the second edge checks.
    Formulated as: sharedVars(A,B) and sharedVars(B,C) have no common element. -/
def DisjointSharedVars (cA cB cC : Cube) : Prop :=
  ∀ v, v ∈ Cube.sharedVars cA cB → v ∉ Cube.sharedVars cB cC

/-- Single-variable edge: two cubes share exactly one variable.
    This is the w=1 (weak link) case, the generic situation at critical density. -/
def SingleSharedVar (c₁ c₂ : Cube) (v : Nat) : Prop :=
  Cube.sharedVars c₁ c₂ = [v]

/-- Gap coverage on two bit positions in a cube: for every combination (a,b) ∈ {0,1}²,
    there exists a gap g in the cube with bit p = a and bit q = b.
    This ensures that the cube can "route" any source constraint to any target
    constraint when the two edges constrain different positions.

    Positions p, q are indices into the cube's 3 variables (0, 1, or 2).
    Uses Cube.vertexBit for bit extraction.

    Requires ≥ 4 gaps to cover all 4 combinations. At critical density ρ_c ≈ 4.27,
    cubes typically have ~7/8 gaps (7 gaps out of 8 vertices), so coverage holds
    for all position pairs. -/
def HasGapCoverage (c : Cube) (p q : Fin 3) : Prop :=
  p ≠ q ∧
  ∀ (a b : Bool),
    ∃ g : Vertex, c.isGap g = true ∧
      Cube.vertexBit g p = a ∧
      Cube.vertexBit g q = b

/-- The full-support connectivity condition specialized to transfer operators:
    every active source gap in A can reach every active target gap in C
    through some intermediate gap in B.
    This is exactly the hypothesis of mul_full_support / mul_full_support_rankOne. -/
def HasFullSupport (cA cB cC : Cube) : Prop :=
  ∀ i j,
    (transferOp cA cB).rowSup i = true →
    (transferOp cB cC).colSup j = true →
    ∃ k, transferOp cA cB i k = true ∧ transferOp cB cC k j = true

/-! ## Section 2: Bridge Lemma (gap coverage → full-support) -/

/-- Bit extraction from Vertex (Fin 8) at position (Fin 3) gives 0 or 1. -/
private theorem vertex_bit_zero_or_one (v : Vertex) (p : Fin 3) :
    (v.val >>> p.val) &&& 1 = 0 ∨ (v.val >>> p.val) &&& 1 = 1 := by
  revert p v; native_decide

/-- If two vertices have the same vertexBit at position p, their raw bit
    extractions are equal as Nat values. -/
private theorem vertexBit_eq_raw (g₁ g₂ : Vertex) (p : Fin 3)
    (h : Cube.vertexBit g₁ p = Cube.vertexBit g₂ p) :
    (g₁.val >>> p.val) &&& 1 = (g₂.val >>> p.val) &&& 1 := by
  simp only [Cube.vertexBit] at h
  have h1 := vertex_bit_zero_or_one g₁ p
  have h2 := vertex_bit_zero_or_one g₂ p
  rcases h1 with h1v | h1v <;> rcases h2 with h2v | h2v <;> simp_all

/-- Right substitution: when sharedVars(c₁,c₂) = [v] (w=1 link) and two
    right-side vertices agree on the bit at position p (= idxOf v in c₂),
    transferOp is preserved. This captures: "transferOp(A,B) depends only
    on one bit position in B when there's one shared variable." -/
private theorem transferOp_subst_right (c₁ c₂ : Cube) (v : Nat) (p : Fin 3)
    (hsv : SingleSharedVar c₁ c₂ v) (hp : c₂.vars.idxOf v = p.val)
    (g₁ k k' : Vertex) (hk'_gap : c₂.isGap k' = true)
    (hbit : Cube.vertexBit k' p = Cube.vertexBit k p)
    (h : transferOp c₁ c₂ g₁ k = true) :
    transferOp c₁ c₂ g₁ k' = true := by
  have ⟨hg₁_gap, _⟩ := transferOp_implies_gaps c₁ c₂ g₁ k h
  apply gaps_and_compat_implies_transferOp c₁ c₂ g₁ k' hg₁_gap hk'_gap
  -- Goal: (sharedVars c₁ c₂).all (...) = true
  simp only [transferOp, Bool.and_eq_true] at h
  obtain ⟨⟨_, _⟩, h_compat⟩ := h
  -- h_compat: (sharedVars c₁ c₂).all (...with k...) = true
  -- Rewrite sharedVars to [v] in both goal and h_compat
  rw [hsv] at h_compat ⊢
  simp only [List.all_cons, List.all_nil, Bool.and_true] at h_compat ⊢
  -- h_compat: bit check passes for (g₁, k) at variable v
  -- Goal: bit check passes for (g₁, k') at variable v
  -- Bridge: k' and k have same bit at position p = idxOf v in c₂
  have hraw := vertexBit_eq_raw k' k p hbit
  rw [← hp] at hraw
  -- hraw: (k'.val >>> c₂.vars.idxOf v) &&& 1 = (k.val >>> c₂.vars.idxOf v) &&& 1
  rw [hraw]
  exact h_compat

/-- Left substitution: when sharedVars(c₁,c₂) = [v] and two left-side
    vertices agree on the bit at position q (= idxOf v in c₁), transferOp
    is preserved. Symmetric to transferOp_subst_right. -/
private theorem transferOp_subst_left (c₁ c₂ : Cube) (v : Nat) (q : Fin 3)
    (hsv : SingleSharedVar c₁ c₂ v) (hq : c₁.vars.idxOf v = q.val)
    (k k' : Vertex) (g₂ : Vertex) (hk'_gap : c₁.isGap k' = true)
    (hbit : Cube.vertexBit k' q = Cube.vertexBit k q)
    (h : transferOp c₁ c₂ k g₂ = true) :
    transferOp c₁ c₂ k' g₂ = true := by
  have ⟨_, hg₂_gap⟩ := transferOp_implies_gaps c₁ c₂ k g₂ h
  apply gaps_and_compat_implies_transferOp c₁ c₂ k' g₂ hk'_gap hg₂_gap
  simp only [transferOp, Bool.and_eq_true] at h
  obtain ⟨⟨_, _⟩, h_compat⟩ := h
  rw [hsv] at h_compat ⊢
  simp only [List.all_cons, List.all_nil, Bool.and_true] at h_compat ⊢
  have hraw := vertexBit_eq_raw k' k q hbit
  rw [← hq] at hraw
  rw [hraw]
  exact h_compat

/-- **T4 Bridge Lemma**: single shared var + gap coverage → full-support.
    When A→B shares exactly v₁ (at position p in B), B→C shares exactly v₂
    (at position q in B), and B has gap coverage on (p,q), then HasFullSupport
    holds: every active source gap in A reaches every active target gap in C
    through some intermediate gap in B.

    This is the core mechanism of rank-1 convergence on misaligned paths:
    the two edges constrain DIFFERENT bit positions in B, so constraints
    are independent and any active-to-active routing is possible. -/
theorem gap_coverage_implies_full_support
    (cA cB cC : Cube) (v₁ v₂ : Nat) (p q : Fin 3)
    (hsv_AB : SingleSharedVar cA cB v₁)
    (hsv_BC : SingleSharedVar cB cC v₂)
    (hp : cB.vars.idxOf v₁ = p.val)
    (hq : cB.vars.idxOf v₂ = q.val)
    (hcov : HasGapCoverage cB p q) :
    HasFullSupport cA cB cC := by
  intro i j hi hj
  -- Step 1: Extract witnesses from rowSup / colSup
  obtain ⟨k₁, hk₁⟩ := mem_rowSup_iff.mp hi
  obtain ⟨k₂, hk₂⟩ := mem_colSup_iff.mp hj
  -- Step 2: Extract gap membership
  have hk₁_gap := (transferOp_implies_gaps cA cB i k₁ hk₁).2
  have hk₂_gap := (transferOp_implies_gaps cB cC k₂ j hk₂).2
  -- Step 3: Get k from gap coverage matching both bit positions
  obtain ⟨_, hcov_all⟩ := hcov
  obtain ⟨k, hk_gap, hk_p, hk_q⟩ := hcov_all (Cube.vertexBit k₁ p) (Cube.vertexBit k₂ q)
  -- Step 4: Route through k — both transferOps hold by bit substitution
  exact ⟨k,
    transferOp_subst_right cA cB v₁ p hsv_AB hp i k₁ k hk_gap hk_p hk₁,
    transferOp_subst_left cB cC v₂ q hsv_BC hq k₂ k j hk_gap hk_q hk₂⟩

/-! ## Section 3: Single-variable transferOp characterization -/

/-- When two cubes share exactly one variable v (w=1 link), transferOp on
    gaps reduces to matching a single bit: the bit at position `idxOf v`
    in each cube's variable ordering.

    Forward: transferOp = true → the shared-variable bits match.
    Backward: gaps + bit match → transferOp = true.

    This is the iff characterization underlying S2's substitution lemmas.
    It isolates the bit-level mechanism: with a single shared variable,
    the entire compatibility check collapses to one bit comparison. -/
theorem transferOp_single_shared (c₁ c₂ : Cube) (v : Nat)
    (hsv : SingleSharedVar c₁ c₂ v) (g₁ g₂ : Vertex)
    (hg₁ : c₁.isGap g₁ = true) (hg₂ : c₂.isGap g₂ = true) :
    transferOp c₁ c₂ g₁ g₂ = true ↔
      (((g₁.val >>> c₁.vars.idxOf v) &&& 1) ==
       ((g₂.val >>> c₂.vars.idxOf v) &&& 1)) = true := by
  constructor
  · -- Forward: extract the compatibility check from transferOp
    intro h
    simp only [transferOp, Bool.and_eq_true] at h
    obtain ⟨⟨_, _⟩, hcompat⟩ := h
    rw [hsv] at hcompat
    simp only [List.all_cons, List.all_nil, Bool.and_true] at hcompat
    exact hcompat
  · -- Backward: reconstruct transferOp from gaps + bit match
    intro h
    apply gaps_and_compat_implies_transferOp c₁ c₂ g₁ g₂ hg₁ hg₂
    rw [hsv]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    exact h

/-! ## Section 4: Main theorem (T4) -/

/-- **T4: Misaligned composition is rank-1.**
    When A→B shares exactly one variable v₁ (w=1 link), B→C shares exactly one
    variable v₂ (w=1 link), and cube B has gap coverage on the positions of v₁ and v₂,
    then the composed operator `mul (transferOp A B) (transferOp B C)` is rank-1.

    This is the formal statement of why information is lost on misaligned paths:
    A→B transmits v₁, B→C transmits v₂, but these are independent dimensions in B.
    Any active source gap in A can reach any active target gap in C through some
    intermediate gap in B — the full-support condition holds, forcing rank-1.

    Hypotheses:
    - `hsv_AB`: edge A→B shares exactly variable v₁
    - `hsv_BC`: edge B→C shares exactly variable v₂
    - `hp`, `hq`: positions of v₁, v₂ in B's variable list
    - `hcov`: B has gap coverage on (p,q) — all 4 bit combos present
    - `hRA`: A→B has at least one active row (non-degenerate)
    - `hCB`: B→C has at least one active column (non-degenerate)

    At critical density ρ_c ≈ 4.27, most cubes have ~7/8 gaps, so gap coverage
    holds for all position pairs. Non-degeneracy holds whenever both edges are
    non-zero (which is guaranteed by arc-consistency / H¹ check). -/
theorem misaligned_composition_rankOne (cA cB cC : Cube)
    (v₁ v₂ : Nat) (p q : Fin 3)
    (hsv_AB : SingleSharedVar cA cB v₁)
    (hsv_BC : SingleSharedVar cB cC v₂)
    (hp : cB.vars.idxOf v₁ = p.val)
    (hq : cB.vars.idxOf v₂ = q.val)
    (hcov : HasGapCoverage cB p q)
    (hRA : IndNonempty (transferOp cA cB).rowSup)
    (hCB : IndNonempty (transferOp cB cC).colSup) :
    IsRankOne (mul (transferOp cA cB) (transferOp cB cC)) :=
  mul_full_support_rankOne _ _ hRA hCB
    (gap_coverage_implies_full_support cA cB cC v₁ v₂ p q hsv_AB hsv_BC hp hq hcov)

/-! ## Concrete Validation -/

/-- The H² witness edges have disjoint shared variables:
    sharedVars(A,B) = [1] and sharedVars(B,C) = [4], which are disjoint. -/
theorem h2_disjoint_shared_vars : DisjointSharedVars h2CubeA h2CubeB h2CubeC := by
  intro v hv_ab hv_bc
  have ⟨hab, hbc, _⟩ := different_shared_vars
  rw [hab] at hv_ab
  rw [hbc] at hv_bc
  simp [List.mem_cons] at hv_ab hv_bc
  omega

/-- Edge A→B shares exactly variable 1. -/
theorem h2_single_AB : SingleSharedVar h2CubeA h2CubeB 1 :=
  different_shared_vars.1

/-- Edge B→C shares exactly variable 4. -/
theorem h2_single_BC : SingleSharedVar h2CubeB h2CubeC 4 :=
  different_shared_vars.2.1

/-- The H² witness does NOT have full-support connectivity.
    Cube B has only 2 gaps, so gap coverage fails — the composed
    operator is rank-2 (anti-diagonal), not rank-1.
    This shows that gap coverage is an essential hypothesis of T4. -/
theorem h2_not_full_support : ¬ HasFullSupport h2CubeA h2CubeB h2CubeC := by
  unfold HasFullSupport
  native_decide

/-- The H² composed operator is rank-2 (not rank-1).
    Witness: entries (0,3) and (3,0) are both true — these cannot be expressed
    as an outer product R ⊗ C (would need R[0]∧C[3] and R[3]∧C[0], but
    then R[0]∧C[0] and R[3]∧C[3] would also be true, which they aren't). -/
theorem h2_composed_not_rankOne :
    ¬ IsRankOne (mul (transferOp h2CubeA h2CubeB) (transferOp h2CubeB h2CubeC)) := by
  intro ⟨R, C, _, _, hRC⟩
  have h03 := (hRC ⟨0, by omega⟩ ⟨3, by omega⟩).mp (by native_decide)
  have h30 := (hRC ⟨3, by omega⟩ ⟨0, by omega⟩).mp (by native_decide)
  have h00 := (hRC ⟨0, by omega⟩ ⟨0, by omega⟩).mpr ⟨h03.1, h30.2⟩
  exact absurd h00 (by native_decide)

end CubeGraph
