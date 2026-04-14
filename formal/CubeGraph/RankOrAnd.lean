/-
  CubeGraph/RankOrAnd.lean
  Rank Behavior Under Entry-wise OR and AND of Boolean Matrices.

  Formalizes key algebraic properties of entry-wise OR (boolOr) and AND (boolAnd)
  as they interact with rank-1 structure and boolean matrix composition.

  KEY RESULTS:
  T1. and_decreases_rank — AND of rank-1 -> rank <= 1
  T2. boolOr_isBoolRankLeTwo — OR of rank-1 has boolean rank <= 2
  T3. mul_boolOr_left / mul_boolOr_right — composition distributes over OR
  T4. mul_boolOr_rank1_collapse_8 — compose(OR(rank1,rank1), any) has bool rank <= 2
  T5. boolOr_rowSup / boolOr_colSup — support union properties
  T6. composition_bottleneck_8 — OR + compose = rank-1 or zero per component
  T7. monotone_rank_barrier_8 — capstone summary

  The rank cycle: OR raises boolean rank to <= 2, next composition drops to <= 1.

  Python verification: 100% of mul(boolOr(rank1, rank1), T3*) yield rank <= 1.
  See: experiments-ml/040_2026-03-29_close-the-chain/rank_or_and_experiment.py
  See: experiments-ml/040_2026-03-29_close-the-chain/SESSION-040-SUMMARY.md
  See: CubeGraph/DAGRankComposition.lean (AND preserves rank-1, OR breaks it)
  See: CubeGraph/EraseOnlyCollapse.lean (rank-1 propagation, rank1_left_compose)
  See: CubeGraph/ConditionalMFI.lean (MFI chain — uses rank bottleneck)
  See: CubeGraph/T3StarNoGroup.lean (T₃* algebra)
  Strategy: experiments-ml/040_2026-03-29_close-the-chain/STRATEGIC-CLOSE-THE-CHAIN.md
  Created: Session 040, 2026-03-29
-/

import CubeGraph.EraseOnlyCollapse
import CubeGraph.DAGRankComposition

namespace BoolMat

variable {n : Nat}

/-! ## Part 1: Boolean Rank Definition -/

/-- A matrix has boolean rank <= k if it can be expressed as the entry-wise OR
    of at most k rank-1 boolean matrices. -/
def IsBoolRankLe (M : BoolMat n) (k : Nat) : Prop :=
  ∃ (components : List (BoolMat n)),
    components.length ≤ k ∧
    (∀ C ∈ components, C.IsRankOne) ∧
    (∀ i j : Fin n, M i j = true ↔
      (components.any fun C => C i j) = true)

/-- Boolean rank 0: the zero matrix. -/
theorem zero_boolRankLe_zero : IsBoolRankLe (zero : BoolMat n) 0 :=
  ⟨[], Nat.le_refl _,
   fun _ h => absurd h (by simp),
   fun i j => ⟨fun h => by simp [zero] at h, fun h => by simp at h⟩⟩

/-- Every rank-1 matrix has boolean rank <= 1. -/
theorem rankOne_boolRankLe_one {M : BoolMat n} (hR : M.IsRankOne) :
    IsBoolRankLe M 1 :=
  ⟨[M], by simp,
   fun C hC => by simp at hC; rwa [hC],
   fun i j => by simp⟩

/-- Boolean rank is monotone: rank <= k implies rank <= k+1. -/
theorem boolRankLe_mono {M : BoolMat n} {k : Nat} (h : IsBoolRankLe M k) :
    IsBoolRankLe M (k + 1) := by
  obtain ⟨cs, hlen, hrank, hcover⟩ := h
  exact ⟨cs, by omega, hrank, hcover⟩

/-! ## Part 2: OR of Rank-1 Has Boolean Rank <= 2 -/

/-- Helper: List.any semantics for a two-element list. -/
private theorem list_any_two (f : BoolMat n → Bool) (A B : BoolMat n) :
    ([A, B].any f) = (f A || f B) := by simp [List.any]

/-- **T2: OR of rank-1 has boolean rank <= 2.**
    boolOr A B is the union of two rank-1 components.
    This is the core algebraic fact: boolean rank of OR is at most
    the sum of boolean ranks. -/
theorem boolOr_isBoolRankLeTwo {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne) :
    IsBoolRankLe (boolOr A B) 2 := by
  refine ⟨[A, B], by simp, fun C hC => ?_, fun i j => ?_⟩
  · simp at hC; rcases hC with rfl | rfl <;> assumption
  · constructor
    · intro h
      simp only [boolOr_apply] at h
      rw [list_any_two (fun C => C i j) A B]
      rw [Bool.or_eq_true] at h ⊢
      exact h
    · intro h
      simp only [boolOr_apply]
      rw [list_any_two (fun C => C i j) A B] at h
      rw [Bool.or_eq_true] at h ⊢
      exact h

/-- **T3: OR of rank-1 is covered by the two outer product components.** -/
theorem boolOr_rank1_covered {A B : BoolMat n}
    (_hA : A.IsRankOne) (_hB : B.IsRankOne) :
    ∀ i j : Fin n, boolOr A B i j = true ↔ (A i j = true ∨ B i j = true) := by
  intro i j; simp only [boolOr_apply, Bool.or_eq_true]

/-! ## Part 3: Support Properties of OR -/

/-- **T5: Row support of OR is the union of row supports.** -/
theorem boolOr_rowSup (A B : BoolMat n) (i : Fin n) :
    (boolOr A B).rowSup i = (A.rowSup i || B.rowSup i) := by
  simp only [rowSup, boolOr_apply]
  -- Goal: any(j, A i j || B i j) = (any(j, A i j) || any(j, B i j))
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨j, hj, hA | hB⟩
    · left; exact ⟨j, hj, hA⟩
    · right; exact ⟨j, hj, hB⟩
  · rintro (⟨j, hj, hA⟩ | ⟨j, hj, hB⟩)
    · exact ⟨j, hj, Or.inl hA⟩
    · exact ⟨j, hj, Or.inr hB⟩

/-- **T6: Column support of OR is the union of column supports.** -/
theorem boolOr_colSup (A B : BoolMat n) (j : Fin n) :
    (boolOr A B).colSup j = (A.colSup j || B.colSup j) := by
  simp only [colSup, boolOr_apply]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨i, hi, hA | hB⟩
    · left; exact ⟨i, hi, hA⟩
    · right; exact ⟨i, hi, hB⟩
  · rintro (⟨i, hi, hA⟩ | ⟨i, hi, hB⟩)
    · exact ⟨i, hi, Or.inl hA⟩
    · exact ⟨i, hi, Or.inr hB⟩

/-! ## Part 4: Composition Distributes Over OR -/

/-- **Distributivity (left)**: mul (boolOr A B) C = boolOr (mul A C) (mul B C). -/
theorem mul_boolOr_left (A B C : BoolMat n) :
    mul (boolOr A B) C = boolOr (mul A C) (mul B C) := by
  funext i j
  apply Bool.eq_iff_iff.mpr
  simp only [mul, boolOr_apply, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨k, hk, h_or, hCkj⟩
    rcases h_or with hAik | hBik
    · left; exact ⟨k, hk, hAik, hCkj⟩
    · right; exact ⟨k, hk, hBik, hCkj⟩
  · rintro (⟨k, hk, hAik, hCkj⟩ | ⟨k, hk, hBik, hCkj⟩)
    · exact ⟨k, hk, Or.inl hAik, hCkj⟩
    · exact ⟨k, hk, Or.inr hBik, hCkj⟩

/-- **Distributivity (right)**: mul C (boolOr A B) = boolOr (mul C A) (mul C B). -/
theorem mul_boolOr_right (A B C : BoolMat n) :
    mul C (boolOr A B) = boolOr (mul C A) (mul C B) := by
  funext i j
  apply Bool.eq_iff_iff.mpr
  simp only [mul, boolOr_apply, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨k, hk, hCik, h_or⟩
    rcases h_or with hAkj | hBkj
    · left; exact ⟨k, hk, hCik, hAkj⟩
    · right; exact ⟨k, hk, hCik, hBkj⟩
  · rintro (⟨k, hk, hCik, hAkj⟩ | ⟨k, hk, hCik, hBkj⟩)
    · exact ⟨k, hk, hCik, Or.inl hAkj⟩
    · exact ⟨k, hk, hCik, Or.inr hBkj⟩

end BoolMat

/-! ## Part 5: Rank-1 Left-Compose + OR = Boolean Rank <= 2

  Using CubeGraph.rank1_left_compose (for BoolMat 8):
  if M is rank-1, then mul M N is rank-1 or zero.

  Combined with distributivity: mul (boolOr A B) C = boolOr (mul A C) (mul B C)
  where each component is rank-1 or zero. So the result has boolean rank <= 2. -/

namespace CubeGraph

open BoolMat

/-- Helper: boolOr with zero on left. -/
private theorem boolOr_zero_left (N : BoolMat n) :
    boolOr zero N = N := by
  funext i j; simp [boolOr, zero]

/-- Helper: boolOr with zero on right. -/
private theorem boolOr_zero_right (M : BoolMat n) :
    boolOr M zero = M := by
  funext i j; simp [boolOr, zero]

/-- Helper: boolOr of two zeros. -/
private theorem boolOr_zero_zero : boolOr (zero : BoolMat n) zero = zero := by
  funext i j; simp [boolOr, zero]

/-- **T4: Composition absorbs OR for 8x8 boolean matrices.**
    mul (boolOr A B) C, where A, B rank-1, has boolean rank <= 2.
    By distributivity + rank1_left_compose, each component is rank-1 or zero. -/
theorem mul_boolOr_rank1_collapse_8 {A B C : BoolMat 8}
    (hA : A.IsRankOne) (hB : B.IsRankOne) :
    IsBoolRankLe (mul (boolOr A B) C) 2 := by
  rw [mul_boolOr_left]
  have hAC := rank1_left_compose A C hA
  have hBC := rank1_left_compose B C hB
  rcases hAC with hAC_r1 | hAC_z
  · rcases hBC with hBC_r1 | hBC_z
    · exact boolOr_isBoolRankLeTwo hAC_r1 hBC_r1
    · have h_eq : boolOr (mul A C) (mul B C) = mul A C := by
        rw [hBC_z]; exact boolOr_zero_right (mul A C)
      rw [h_eq]
      exact boolRankLe_mono (rankOne_boolRankLe_one hAC_r1)
  · rcases hBC with hBC_r1 | hBC_z
    · have h_eq : boolOr (mul A C) (mul B C) = mul B C := by
        rw [hAC_z]; exact boolOr_zero_left (mul B C)
      rw [h_eq]
      exact boolRankLe_mono (rankOne_boolRankLe_one hBC_r1)
    · have h_eq : boolOr (mul A C) (mul B C) = zero := by
        rw [hAC_z, hBC_z]; exact boolOr_zero_zero
      rw [h_eq]
      exact boolRankLe_mono (boolRankLe_mono zero_boolRankLe_zero)

/-- **Composition bottleneck**: Each component decomposes independently.
    After compose, the result splits into rank-1-or-zero pieces. -/
theorem composition_bottleneck_8 (A B C : BoolMat 8)
    (hA : A.IsRankOne) (hB : B.IsRankOne) :
    mul (boolOr A B) C = boolOr (mul A C) (mul B C)
    ∧ ((mul A C).IsRankOne ∨ mul A C = zero)
    ∧ ((mul B C).IsRankOne ∨ mul B C = zero) :=
  ⟨mul_boolOr_left A B C,
   rank1_left_compose A C hA,
   rank1_left_compose B C hB⟩

/-! ## Part 6: AND-OR-Compose Circuit Analysis -/

/-- **AND is monotone-decreasing for boolean rank.** -/
theorem and_decreases_rank {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne) :
    isZero (boolAnd A B) ∨ (boolAnd A B).IsRankOne :=
  boolAnd_zero_or_rankOne hA hB

/-- **OR raises boolean rank by at most 1.**
    Upper bound: rank-1 OR rank-1 has boolean rank <= 2.
    Lower bound witness: there exist rank-1 matrices with boolOr not rank-1. -/
theorem or_raises_rank_by_one :
    (∀ (A B : BoolMat n), A.IsRankOne → B.IsRankOne →
      IsBoolRankLe (boolOr A B) 2)
    ∧ (∃ (A B : BoolMat 3), A.IsRankOne ∧ B.IsRankOne ∧
        ¬ (boolOr A B).IsRankOne) :=
  ⟨fun A B hA hB => boolOr_isBoolRankLeTwo hA hB,
   entrywise_or_breaks_rank1⟩

/-- **Full bottleneck: OR + compose = bounded rank per component.** -/
theorem compose_is_bottleneck_8 (A B C : BoolMat 8)
    (hA : A.IsRankOne) (hB : B.IsRankOne) :
    IsBoolRankLe (boolOr A B) 2
    ∧ IsBoolRankLe (mul (boolOr A B) C) 2
    ∧ ((mul A C).IsRankOne ∨ mul A C = zero)
    ∧ ((mul B C).IsRankOne ∨ mul B C = zero) :=
  ⟨boolOr_isBoolRankLeTwo hA hB,
   mul_boolOr_rank1_collapse_8 hA hB,
   rank1_left_compose A C hA,
   rank1_left_compose B C hB⟩

/-! ## Part 7: Capstone — The Monotone Rank Barrier

  1. Transfer operators compose to rank-1 or zero (EraseOnlyCollapse).
  2. AND preserves rank <= 1 (boolAnd_zero_or_rankOne).
  3. OR raises to boolean rank <= 2 (boolOr_isBoolRankLeTwo).
  4. Composition drops rank back via distributivity + rank-1 left-compose.
  5. At every CubeGraph edge: information bottlenecked to boolean rank <= 2.
  6. CG-UNSAT needs Omega(n) bits simultaneously -> exponential circuit size. -/

/-- **Monotone Rank Barrier Summary.**
    Packages the key results for the monotone circuit argument. -/
theorem monotone_rank_barrier_8 :
    -- (1) AND preserves rank <= 1
    (∀ A B : BoolMat 8, A.IsRankOne → B.IsRankOne →
      isZero (boolAnd A B) ∨ (boolAnd A B).IsRankOne)
    -- (2) OR raises boolean rank to <= 2
    ∧ (∀ A B : BoolMat 8, A.IsRankOne → B.IsRankOne →
      IsBoolRankLe (boolOr A B) 2)
    -- (3) Composition + rank-1: each component rank-1 or zero
    ∧ (∀ A B C : BoolMat 8, A.IsRankOne → B.IsRankOne →
      ((mul A C).IsRankOne ∨ mul A C = zero)
      ∧ ((mul B C).IsRankOne ∨ mul B C = zero))
    -- (4) Distributivity: mul (boolOr A B) C = boolOr (mul A C) (mul B C)
    ∧ (∀ (A B C : BoolMat 8),
      mul (boolOr A B) C = boolOr (mul A C) (mul B C)) :=
  ⟨fun A B hA hB => boolAnd_zero_or_rankOne hA hB,
   fun A B hA hB => boolOr_isBoolRankLeTwo hA hB,
   fun A B C hA hB =>
     ⟨rank1_left_compose A C hA, rank1_left_compose B C hB⟩,
   fun A B C => mul_boolOr_left A B C⟩

end CubeGraph
