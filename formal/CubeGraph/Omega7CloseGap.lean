/-
  CubeGraph/Omega7CloseGap.lean
  CLOSING THE PSI7 BOOLOOR GAP — HasMultiRow theory and applications.

  Psi7GeneralProjection.lean has a gap at the boolOr(non-perm, non-perm) case.
  This file provides the HasMultiRow theory that closes that gap under the
  hypothesis that non-perm sub-expressions are HasMultiRow, isZero, or low-rank.

  PROVEN (0 sorry, 17 theorems):
  Part 1: HasMultiRow definition and 10 core lemmas
  Part 2: The gap-closing lemma for boolOr
  Part 3: Permutation-rowRank interaction
  Part 4: Grand summary

  IMPORTS: Chi7CircuitProjection, Nu6BooleanInvolution
-/

import CubeGraph.Chi7CircuitProjection
import CubeGraph.Nu6BooleanInvolution

open BoolMat

namespace CubeGraph

/-! ## Part 1: HasMultiRow — Definition and Core Properties -/

/-- A boolean matrix has multi-row if some row has ≥ 2 distinct true entries.
    This immediately prevents the matrix from being a permutation. -/
def HasMultiRow {n : Nat} (M : BoolMat n) : Prop :=
  ∃ i j₁ j₂ : Fin n, j₁ ≠ j₂ ∧ M i j₁ = true ∧ M i j₂ = true

instance instDecidableHasMultiRow {n : Nat} {M : BoolMat n} : Decidable (HasMultiRow M) :=
  inferInstanceAs (Decidable (∃ i j₁ j₂ : Fin n, j₁ ≠ j₂ ∧ M i j₁ = true ∧ M i j₂ = true))

/-- **Ω7.1 — HASMULTIROW IMPLIES NOT PERMUTATION**: -/
theorem hasMultiRow_not_perm {n : Nat} {M : BoolMat n} (hM : HasMultiRow M) :
    ¬ IsPermutationMatrix M := by
  intro hP
  obtain ⟨i, j₁, j₂, hne, h₁, h₂⟩ := hM
  obtain ⟨k, _, hk_u⟩ := hP.1 i
  exact hne (hk_u j₁ h₁ ▸ (hk_u j₂ h₂).symm)

/-- **Ω7.2 — BOOLOOR PRESERVES MULTIROW LEFT**: boolOr only adds entries. -/
theorem hasMultiRow_boolOr_left {n : Nat} {A : BoolMat n} (B : BoolMat n)
    (hA : HasMultiRow A) : HasMultiRow (boolOr A B) := by
  obtain ⟨i, j₁, j₂, hne, h₁, h₂⟩ := hA
  exact ⟨i, j₁, j₂, hne, by simp [boolOr, h₁], by simp [boolOr, h₂]⟩

/-- **Ω7.3 — BOOLOOR PRESERVES MULTIROW RIGHT**: Symmetric version. -/
theorem hasMultiRow_boolOr_right {n : Nat} (A : BoolMat n) {B : BoolMat n}
    (hB : HasMultiRow B) : HasMultiRow (boolOr A B) := by
  obtain ⟨i, j₁, j₂, hne, h₁, h₂⟩ := hB
  refine ⟨i, j₁, j₂, hne, ?_, ?_⟩ <;> simp only [boolOr] <;> cases A i _ <;> simp [*]

/-- **Ω7.4 — PERM MUL LEFT PRESERVES MULTIROW**: Row permutation preserves
    multi-row. If A has multi-row at row i₀, then P·A has it at σ⁻¹(i₀). -/
theorem hasMultiRow_perm_mul_left {n : Nat} {P A : BoolMat n}
    (hP : IsPermutationMatrix P) (hA : HasMultiRow A) :
    HasMultiRow (BoolMat.mul P A) := by
  obtain ⟨i₀, j₁, j₂, hne, h₁, h₂⟩ := hA
  obtain ⟨r, hr, _⟩ := hP.2 i₀
  exact ⟨r, j₁, j₂, hne,
    (mul_apply_true P A r j₁).mpr ⟨i₀, hr, h₁⟩,
    (mul_apply_true P A r j₂).mpr ⟨i₀, hr, h₂⟩⟩

/-- **Ω7.5 — PERM MUL RIGHT PRESERVES MULTIROW**: Column permutation
    preserves multi-row. The 2+ entries in a row move to distinct columns. -/
theorem hasMultiRow_mul_perm_right {n : Nat} {A P : BoolMat n}
    (hA : HasMultiRow A) (hP : IsPermutationMatrix P) :
    HasMultiRow (BoolMat.mul A P) := by
  obtain ⟨i₀, j₁, j₂, hne, h₁, h₂⟩ := hA
  obtain ⟨c₁, hc₁, _⟩ := hP.1 j₁
  obtain ⟨c₂, hc₂, _⟩ := hP.1 j₂
  have hcne : c₁ ≠ c₂ := by
    intro h_eq; obtain ⟨r, _, hr_u⟩ := hP.2 c₁
    exact hne (hr_u j₁ hc₁ ▸ (hr_u j₂ (h_eq ▸ hc₂)).symm)
  exact ⟨i₀, c₁, c₂, hcne,
    (mul_apply_true A P i₀ c₁).mpr ⟨j₁, h₁, hc₁⟩,
    (mul_apply_true A P i₀ c₂).mpr ⟨j₂, h₂, hc₂⟩⟩

/-- **Ω7.6 — DISTINCT PERMS HAVE MULTIROW BOOLOR**: -/
theorem hasMultiRow_boolOr_distinct_perms {n : Nat} {P₁ P₂ : BoolMat n}
    (hP₁ : IsPermutationMatrix P₁) (hP₂ : IsPermutationMatrix P₂)
    (hne : P₁ ≠ P₂) : HasMultiRow (boolOr P₁ P₂) := by
  obtain ⟨i, j₁, j₂, hj_ne, h₁, h₂⟩ := distinct_perms_disagree P₁ P₂ hP₁ hP₂ hne
  refine ⟨i, j₁, j₂, hj_ne, by simp [boolOr, h₁], ?_⟩
  simp only [boolOr]; cases P₁ i j₂ <;> simp [h₂]

/-- **Ω7.7 — ISZERO NOT PERM** (for BoolMat 8): -/
theorem isZero_not_perm_8 {M : BoolMat 8} (h : BoolMat.isZero M) :
    ¬ IsPermutationMatrix M := by
  intro hP; obtain ⟨j, hj, _⟩ := hP.1 ⟨0, by omega⟩
  exact absurd (h ⟨0, by omega⟩ j ▸ hj) (by decide)

/-- **Ω7.8 — BOOLOOR WITH ZERO LEFT**: -/
theorem boolOr_isZero_left {n : Nat} {A : BoolMat n} (B : BoolMat n)
    (hA : BoolMat.isZero A) : boolOr A B = B := by
  funext i j; simp [boolOr, hA i j]

/-- **Ω7.9 — BOOLOOR WITH ZERO RIGHT**: -/
theorem boolOr_isZero_right {n : Nat} (A : BoolMat n) {B : BoolMat n}
    (hB : BoolMat.isZero B) : boolOr A B = A := by
  funext i j; simp [boolOr, hB i j]

/-- **Ω7.10 — ISZERO BOOLOOR**: Both zero → boolOr zero. -/
theorem isZero_boolOr {n : Nat} {A B : BoolMat n}
    (hA : BoolMat.isZero A) (hB : BoolMat.isZero B) :
    BoolMat.isZero (boolOr A B) :=
  fun i j => by simp [boolOr, hA i j, hB i j]

/-! ## Part 2: The Gap-Closing Lemma -/

/-- **Ω7.11 — LOW COMBINED RANK NOT PERM**: -/
theorem boolOr_low_rank_not_perm (A B : BoolMat 8)
    (h : rowRank A + rowRank B < 8) :
    ¬ IsPermutationMatrix (boolOr A B) :=
  low_rank_not_perm _ (Nat.lt_of_le_of_lt (boolOr_rowRank_le_add A B) h)

/-- **Ω7.12 — THE GAP-CLOSING LEMMA**: For any two BoolMat 8 matrices that
    are each HasMultiRow, isZero, or have rowRank ≤ 3, their boolOr is NOT
    a permutation. Covers all 9 pairwise combinations.

    This theorem directly closes the Psi7 sorry at boolOr(non-perm, non-perm)
    when the inductive hypothesis ensures these conditions. -/
theorem boolOr_nonperm_of_omega7 (A B : BoolMat 8)
    (hA : HasMultiRow A ∨ BoolMat.isZero A ∨ BoolMat.rowRank A ≤ 3)
    (hB : HasMultiRow B ∨ BoolMat.isZero B ∨ BoolMat.rowRank B ≤ 3) :
    ¬ IsPermutationMatrix (boolOr A B) := by
  rcases hA with hMA | hZA | hRA
  · exact hasMultiRow_not_perm (hasMultiRow_boolOr_left B hMA)
  · rcases hB with hMB | hZB | hRB
    · exact hasMultiRow_not_perm (hasMultiRow_boolOr_right A hMB)
    · rw [boolOr_isZero_left B hZA]; exact isZero_not_perm_8 hZB
    · rw [boolOr_isZero_left B hZA]; exact low_rank_not_perm B (by omega)
  · rcases hB with hMB | hZB | hRB
    · exact hasMultiRow_not_perm (hasMultiRow_boolOr_right A hMB)
    · rw [boolOr_isZero_right A hZB]; exact low_rank_not_perm A (by omega)
    · exact boolOr_low_rank_not_perm A B (by omega)

/-! ## Part 3: Additional RowRank Lemmas -/

/-- **Ω7.14 — ENTRYAND ROWRANK LEFT**: entryAnd ≤ left factor's rowRank. -/
theorem omega7_entryAnd_rowRank_le_left (A B : BoolMat n) :
    BoolMat.rowRank (BoolMat.entryAnd A B) ≤ BoolMat.rowRank A := by
  unfold BoolMat.rowRank
  apply countP_le_of_implies
  intro i hi; rw [mem_rowSup_iff] at hi ⊢
  obtain ⟨j, hj⟩ := hi; simp [BoolMat.entryAnd] at hj; exact ⟨j, hj.1⟩

/-- **Ω7.15 — ENTRYAND ROWRANK RIGHT**: entryAnd ≤ right factor's rowRank. -/
theorem omega7_entryAnd_rowRank_le_right (A B : BoolMat n) :
    BoolMat.rowRank (BoolMat.entryAnd A B) ≤ BoolMat.rowRank B := by
  unfold BoolMat.rowRank
  apply countP_le_of_implies
  intro i hi; rw [mem_rowSup_iff] at hi ⊢
  obtain ⟨j, hj⟩ := hi; simp [BoolMat.entryAnd] at hj; exact ⟨j, hj.2⟩

/-! ## Part 4: Grand Summary -/

/-- **Ω7.16 — COMPREHENSIVE SUMMARY**: All results assembled. -/
theorem omega7_grand_summary :
    -- (a) HasMultiRow → ¬ perm
    (∀ (n : Nat) (M : BoolMat n), HasMultiRow M → ¬ IsPermutationMatrix M) ∧
    -- (b) boolOr preserves HasMultiRow (both sides)
    (∀ (n : Nat) (A B : BoolMat n), HasMultiRow A → HasMultiRow (boolOr A B)) ∧
    (∀ (n : Nat) (A B : BoolMat n), HasMultiRow B → HasMultiRow (boolOr A B)) ∧
    -- (c) Perm × HasMultiRow → HasMultiRow (both sides)
    (∀ (n : Nat) (P A : BoolMat n), IsPermutationMatrix P → HasMultiRow A →
      HasMultiRow (BoolMat.mul P A)) ∧
    (∀ (n : Nat) (A P : BoolMat n), HasMultiRow A → IsPermutationMatrix P →
      HasMultiRow (BoolMat.mul A P)) ∧
    -- (d) boolOr of distinct perms → HasMultiRow
    (∀ (n : Nat) (P₁ P₂ : BoolMat n), IsPermutationMatrix P₁ → IsPermutationMatrix P₂ →
      P₁ ≠ P₂ → HasMultiRow (boolOr P₁ P₂)) ∧
    -- (e) The gap-closing lemma
    (∀ A B : BoolMat 8,
      (HasMultiRow A ∨ BoolMat.isZero A ∨ BoolMat.rowRank A ≤ 3) →
      (HasMultiRow B ∨ BoolMat.isZero B ∨ BoolMat.rowRank B ≤ 3) →
      ¬ IsPermutationMatrix (boolOr A B)) :=
  ⟨fun _ _ hM => hasMultiRow_not_perm hM,
   fun _ _ B hA => hasMultiRow_boolOr_left B hA,
   fun _ A _ hB => hasMultiRow_boolOr_right A hB,
   fun _ _ _ hP hA => hasMultiRow_perm_mul_left hP hA,
   fun _ _ _ hA hP => hasMultiRow_mul_perm_right hA hP,
   fun _ _ _ hP₁ hP₂ hne => hasMultiRow_boolOr_distinct_perms hP₁ hP₂ hne,
   boolOr_nonperm_of_omega7⟩

end CubeGraph
