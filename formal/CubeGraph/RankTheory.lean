/-
  CubeGraph/RankTheory.lean
  Rank-1 properties, transferOp↔gap structure, arc consistency↔support,
  and RankAtMost definition.

  Phase 3b (T1-E) — connects algebraic rank to geometric gap structure.

  KEY CONNECTIONS:
  - Section 3: arcConsistentDir ↔ colSup covers target gaps (algebra↔constraint propagation)
  - Section 5: RankAtMost = vocabulary for Phase 6 (rank-2 cycle DP)
  - removeNode_preserves_arcConsistent is in TreeSAT.lean Section 8

  See: theory/foundations/04-links-weights.md (link weights and transfer operators)
  See: theory/theorems/CORE-THEOREMS-SUMMARY.md (rank theory in the framework)
-/

import CubeGraph.ChannelAlignment
import CubeGraph.TreeSAT
import CubeGraph.PartB

/-! ## Section 1: Rank-1 Basic Properties -/

namespace BoolMat

variable {n : Nat}

/-- R1: A rank-1 matrix has at least one true entry. -/
theorem rankOne_nonzero {M : BoolMat n} (h : M.IsRankOne) :
    ∃ i j : Fin n, M i j = true := by
  obtain ⟨R, C, ⟨r, hr⟩, ⟨c, hc⟩, hRC⟩ := h
  exact ⟨r, c, (hRC r c).mpr ⟨hr, hc⟩⟩

/-- R2: A rank-1 matrix is not the zero matrix. -/
theorem rankOne_not_isZero {M : BoolMat n} (h : M.IsRankOne) : ¬ M.isZero := by
  intro hz
  obtain ⟨i, j, hij⟩ := rankOne_nonzero h
  rw [hz i j] at hij
  exact Bool.false_ne_true hij

/-- R3: The zero matrix is not rank-1 (contrapositive of R2). -/
theorem isZero_not_rankOne {M : BoolMat n} (h : M.isZero) : ¬ M.IsRankOne :=
  fun hr => rankOne_not_isZero hr h

/-! ## Section 5: RankAtMost Definition (placed here to keep BoolMat namespace together)

  Boolean rank: minimum number of rank-1 boolean matrices whose boolean OR equals M.
  RankAtMost k: M can be decomposed into at most k rank-1 components.

  Vocabulary for Phase 6 (rank-2 cycle DP) and Phase 8 (hierarchy).
  Rank-0 = isZero, Rank-1 = IsRankOne, Rank ≥ 2 = the "hard" case. -/

/-- D1: A boolean matrix has rank at most k if it can be written as the
    boolean OR of at most k rank-1 boolean matrices.
    This is the "boolean rank" or "rectangle cover number". -/
def RankAtMost (M : BoolMat n) (k : Nat) : Prop :=
  ∃ (components : List (BoolMat n)),
    components.length ≤ k ∧
    (∀ C ∈ components, C.IsRankOne) ∧
    (∀ i j, M i j = true ↔ ∃ C ∈ components, C i j = true)

/-- R9: Rank at most 0 ↔ the matrix is zero (no rank-1 components). -/
theorem rankAtMost_zero_iff_isZero (M : BoolMat n) :
    RankAtMost M 0 ↔ M.isZero := by
  constructor
  · intro ⟨comps, hlen, _, hM⟩
    have hempty : comps = [] := List.eq_nil_of_length_eq_zero (by omega)
    intro i j
    cases h : M i j with
    | false => rfl
    | true =>
      obtain ⟨C, hC, _⟩ := (hM i j).mp h
      subst hempty; simp at hC
  · intro h
    refine ⟨[], by simp, fun _ hC => by simp at hC, fun i j => ?_⟩
    constructor
    · intro hij; rw [h i j] at hij; exact absurd hij Bool.false_ne_true
    · intro ⟨_, hC, _⟩; simp at hC

/-- R10: A rank-1 matrix has rank at most 1. -/
theorem rankOne_rankAtMost_one {M : BoolMat n} (h : M.IsRankOne) :
    RankAtMost M 1 := by
  refine ⟨[M], by simp, fun C hC => ?_, fun i j => ?_⟩
  · simp at hC; rwa [hC]
  · constructor
    · intro hij; exact ⟨M, by simp, hij⟩
    · intro ⟨C, hC, hCij⟩; simp at hC; rwa [← hC]

/-- R11: The zero matrix has rank at most k for any k. -/
theorem isZero_rankAtMost {M : BoolMat n} (h : M.isZero) (k : Nat) :
    RankAtMost M k := by
  refine ⟨[], by simp, fun _ hC => by simp at hC, fun i j => ?_⟩
  constructor
  · intro hij; rw [h i j] at hij; exact absurd hij Bool.false_ne_true
  · intro ⟨_, hC, _⟩; simp at hC

/-- R12: Rank bound is monotone: if M has rank ≤ k₁ and k₁ ≤ k₂, then rank ≤ k₂. -/
theorem rankAtMost_mono {M : BoolMat n} {k₁ k₂ : Nat}
    (h : RankAtMost M k₁) (hle : k₁ ≤ k₂) : RankAtMost M k₂ := by
  obtain ⟨comps, hlen, hr1, hM⟩ := h
  exact ⟨comps, by omega, hr1, hM⟩

end BoolMat

/-! ## Sections 2-4: TransferOp and Arc Consistency -/

namespace CubeGraph

open BoolMat

/-! ## Section 2: TransferOp Support ⊆ Gaps -/

/-- R4: If vertex i is in rowSup of transferOp, then i is a gap of c₁.
    Geometrically: only gap vertices can "send" through a transfer operator. -/
theorem transferOp_rowSup_gap (c₁ c₂ : Cube) (i : Vertex)
    (h : (transferOp c₁ c₂).rowSup i = true) : c₁.isGap i = true := by
  obtain ⟨j, hj⟩ := mem_rowSup_iff.mp h
  exact (transferOp_implies_gaps c₁ c₂ i j hj).1

/-- R5: If vertex j is in colSup of transferOp, then j is a gap of c₂.
    Geometrically: only gap vertices can "receive" through a transfer operator. -/
theorem transferOp_colSup_gap (c₁ c₂ : Cube) (j : Vertex)
    (h : (transferOp c₁ c₂).colSup j = true) : c₂.isGap j = true := by
  obtain ⟨i, hi⟩ := mem_colSup_iff.mp h
  exact (transferOp_implies_gaps c₁ c₂ i j hi).2

/-! ## Section 3: Arc Consistency ↔ Column/Row Support

  Key insight: arc consistency from c₁ to c₂ is equivalent to
  colSup(σ(c₁,c₂)) covering all gaps of c₂.

  Combined with R4-R5: arc consistency ↔ support = gaps.
  Without arc consistency: support ⊊ gaps (some gaps unreachable).

  Bidirectional arc consistency:
  - arcConsistentDir c₁ c₂ ↔ colSup(σ) covers gaps of c₂
  - arcConsistentDir c₂ c₁ ↔ rowSup(σ) covers gaps of c₁
  (via transferOp_transpose: σ(c₁,c₂) = σ(c₂,c₁)ᵀ) -/

/-- R6: Arc consistency from c₁ to c₂ ↔ colSup covers all target gaps.
    This bridges constraint propagation (arc consistency) with
    linear algebra (column support). -/
theorem arcConsistentDir_iff_colSup (c₁ c₂ : Cube) :
    arcConsistentDir c₁ c₂ ↔
    ∀ g₂ : Vertex, c₂.isGap g₂ = true → (transferOp c₁ c₂).colSup g₂ = true := by
  constructor
  · intro h g₂ hg₂
    obtain ⟨g₁, hg₁⟩ := h g₂ hg₂
    exact mem_colSup_iff.mpr ⟨g₁, hg₁⟩
  · intro h g₂ hg₂
    obtain ⟨g₁, hg₁⟩ := mem_colSup_iff.mp (h g₂ hg₂)
    exact ⟨g₁, hg₁⟩

/-- R6b: Element-level transpose for transferOp.
    Public for Phase 5 (reverse-direction edge compatibility). -/
theorem transferOp_transpose_elem (c₁ c₂ : Cube) (g₁ g₂ : Vertex) :
    transferOp c₁ c₂ g₁ g₂ = transferOp c₂ c₁ g₂ g₁ := by
  have := congrFun (congrFun (transferOp_transpose c₁ c₂) g₁) g₂
  simp only [BoolMat.transpose_apply] at this
  exact this

/-- R7: Arc consistency from c₂ to c₁ ↔ rowSup(σ(c₁,c₂)) covers all source gaps.
    Uses transferOp_transpose: σ(c₂,c₁)[g₂,g₁] = σ(c₁,c₂)[g₁,g₂]. -/
theorem arcConsistentDir_reverse_iff_rowSup (c₁ c₂ : Cube) :
    arcConsistentDir c₂ c₁ ↔
    ∀ g₁ : Vertex, c₁.isGap g₁ = true → (transferOp c₁ c₂).rowSup g₁ = true := by
  constructor
  · intro h g₁ hg₁
    obtain ⟨g₂, hg₂⟩ := h g₁ hg₁
    -- hg₂ : transferOp c₂ c₁ g₂ g₁ = true
    -- By transpose: σ(c₁,c₂)(g₁,g₂) = σ(c₂,c₁)(g₂,g₁) = true
    apply mem_rowSup_iff.mpr
    exact ⟨g₂, by rw [transferOp_transpose_elem]; exact hg₂⟩
  · intro h g₁ hg₁
    obtain ⟨g₂, hg₂⟩ := mem_rowSup_iff.mp (h g₁ hg₁)
    -- hg₂ : transferOp c₁ c₂ g₁ g₂ = true
    -- By transpose: σ(c₂,c₁)(g₂,g₁) = σ(c₁,c₂)(g₁,g₂) = true
    exact ⟨g₂, by rw [← transferOp_transpose_elem]; exact hg₂⟩

/-! ## Section 4: Arc Consistency Preservation under removeNode

  Already proven in TreeSAT.lean Section 8 as `removeNode_preserves_arcConsistent`.
  CRITICAL for Phase 5 (acyclic + arc-consistent → SAT) induction step. -/

/-- R8: Given arc consistency from c₁ to c₂ and a gap g₂ in c₂,
    there exists a gap g₁ in c₁ compatible via transferOp.
    CRITICAL for Phase 5: choosing the leaf node's gap in the peel step. -/
theorem leaf_has_compatible_gap (c₁ c₂ : Cube) (g₂ : Vertex)
    (h_ac : arcConsistentDir c₁ c₂) (hg₂ : c₂.isGap g₂ = true) :
    ∃ g₁ : Vertex, c₁.isGap g₁ = true ∧ transferOp c₁ c₂ g₁ g₂ = true := by
  obtain ⟨g₁, hg₁⟩ := h_ac g₂ hg₂
  exact ⟨g₁, (transferOp_implies_gaps c₁ c₂ g₁ g₂ hg₁).1, hg₁⟩

end CubeGraph
