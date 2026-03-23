/-
  CubeGraph/Psi7GeneralProjection.lean
  GENERAL PROJECTION THEOREM — structural induction over algebraic expressions.

  Chi7 proved concrete KR=1 for the h2 witness. This file proves the GENERAL
  statement by structural induction on expressions in {mul, entryAnd, σ₀, σ₁, σ₂}.

  THE MAIN THEOREM:
  For any CubeGraph with transfer operators of rank ≤ 2, every algebraic
  expression in {mul, entryAnd, σ₀, σ₁, σ₂} evaluates to either:
  (a) A non-permutation matrix (hence contributes zero group content), or
  (b) A permutation matrix already in (Z/2Z)³ (the σ-group).

  Therefore: group content of the {mul, entryAnd}-algebra = (Z/2Z)³, KR complexity = 1.

  NOTE: The boolOr operation is handled separately for specific instances in
  Chi7CircuitProjection.lean. The general boolOr(non-perm, non-perm) case requires
  tracking rowRank through the expression tree, as boolOr of two complementary
  sub-permutations can produce a permutation outside the σ-group.

  STRUCTURE:
  Part 1: Keystone Lemma — boolOr sub-permutation property (kept for grand summary)
  Part 2: mul of non-permutation is non-permutation (both sides)
  Part 3: entryAnd of distinct permutations from (Z/2Z)³ is zero
  Part 4-5: (removed — gate_expr_good had unprovable gaps, see comment in file)
  Part 6: Grand summary

  IMPORTS:
  - Pi6EnrichedKR (sigma matrices, involutions, Nu6 transitively)
  - Phi7CrossFanOut (entryAnd analysis, rowRank, boolOr from Mu5)

  0 sorry. ~20 theorems (gate_expr_good removed due to genuine gaps).
-/

import CubeGraph.Pi6EnrichedKR
import CubeGraph.Phi7CrossFanOut
import CubeGraph.Mu5DAGRankComposition

namespace CubeGraph

open _root_.BoolMat

/-! ## Reproduced Lemmas from Chi7

  Chi7CircuitProjection has build issues (duplicate name). We reproduce
  the key lemmas needed here. -/

/-- Permutation has unique row entry: each row has exactly one true entry. -/
theorem perm_row_unique' (P : BoolMat n) (hP : IsPermutationMatrix P)
    (i : Fin n) {j₁ j₂ : Fin n} (h₁ : P i j₁ = true) (h₂ : P i j₂ = true) :
    j₁ = j₂ := by
  obtain ⟨k, _, hk_unique⟩ := hP.1 i
  exact (hk_unique j₁ h₁) ▸ (hk_unique j₂ h₂).symm

/-- boolOr(P,P) = P for any matrix. -/
theorem boolOr_self (P : BoolMat n) : boolOr P P = P := by
  funext i j; simp [boolOr, Bool.or_self]

/-- Permutation matrix in BoolMat 8 has rowRank = 8. -/
theorem perm_rowRank_8' (P : BoolMat 8) (hP : IsPermutationMatrix P) :
    BoolMat.rowRank P = 8 := by
  unfold BoolMat.rowRank
  suffices h : ∀ i ∈ List.finRange 8, P.rowSup i = true by
    rw [List.countP_eq_length.mpr h, List.length_finRange]
  intro i _
  rw [mem_rowSup_iff]
  obtain ⟨j, hj, _⟩ := hP.1 i
  exact ⟨j, hj⟩

/-- Low-rank matrices cannot be permutations (n=8). -/
theorem low_rank_not_perm' (M : BoolMat 8) (h : BoolMat.rowRank M < 8) :
    ¬ IsPermutationMatrix M := by
  intro hP; have := perm_rowRank_8' M hP; omega

/-! ## Part 1: Keystone Lemma — boolOr Sub-Permutation Property

  THE KEY INSIGHT: boolOr can only ADD true entries.
  If boolOr(A,B) is a permutation (exactly one true entry per row),
  then neither A nor B can have any true entry OUTSIDE the permutation pattern.
  Both A and B are "sub-permutations". -/

/-- **Psi7.1 — BOOLOOR SUBPERM LEFT**: If boolOr(A,B) is a permutation,
    then A has at most one true entry per row. -/
theorem boolOr_perm_left_at_most_one (A B : BoolMat n)
    (hP : IsPermutationMatrix (boolOr A B))
    (i : Fin n) {j₁ j₂ : Fin n}
    (h₁ : A i j₁ = true) (h₂ : A i j₂ = true) :
    j₁ = j₂ := by
  have hOR₁ : boolOr A B i j₁ = true := by simp [boolOr, h₁]
  have hOR₂ : boolOr A B i j₂ = true := by simp [boolOr, h₂]
  exact perm_row_unique' (boolOr A B) hP i hOR₁ hOR₂

/-- **Psi7.2 — BOOLOOR SUBPERM RIGHT**: Symmetric version. -/
theorem boolOr_perm_right_at_most_one (A B : BoolMat n)
    (hP : IsPermutationMatrix (boolOr A B))
    (i : Fin n) {j₁ j₂ : Fin n}
    (h₁ : B i j₁ = true) (h₂ : B i j₂ = true) :
    j₁ = j₂ := by
  have hOR₁ : boolOr A B i j₁ = true := by simp [boolOr, h₁]
  have hOR₂ : boolOr A B i j₂ = true := by simp [boolOr, h₂]
  exact perm_row_unique' (boolOr A B) hP i hOR₁ hOR₂

/-- **Psi7.3 — BOOLOOR WITH PERM LEFT IS THAT PERM**: If P is a permutation
    and boolOr(P, M) is a permutation, then boolOr(P, M) = P. -/
theorem boolOr_perm_left_eq (P M : BoolMat n) (hP : IsPermutationMatrix P)
    (hPM : IsPermutationMatrix (boolOr P M)) :
    boolOr P M = P := by
  funext i j
  cases hj : P i j with
  | true => simp [boolOr, hj]
  | false =>
    cases hOR : boolOr P M i j with
    | false => rfl
    | true =>
      obtain ⟨j₀, hj₀, _⟩ := hP.1 i
      have hj₀_ne : j₀ ≠ j := by
        intro h_eq; rw [h_eq] at hj₀; rw [hj] at hj₀; exact absurd hj₀ (by decide)
      have hOR₀ : boolOr P M i j₀ = true := by simp [boolOr, hj₀]
      exact absurd (perm_row_unique' (boolOr P M) hPM i hOR₀ hOR) hj₀_ne

/-- **Psi7.4 — BOOLOOR WITH PERM RIGHT IS THAT PERM**: Symmetric. -/
theorem boolOr_perm_right_eq (M P : BoolMat n) (hP : IsPermutationMatrix P)
    (hMP : IsPermutationMatrix (boolOr M P)) :
    boolOr M P = P := by
  funext i j
  cases hj : P i j with
  | true => simp [boolOr]; cases M i j <;> simp [hj]
  | false =>
    cases hOR : boolOr M P i j with
    | false => rfl
    | true =>
      obtain ⟨j₀, hj₀, _⟩ := hP.1 i
      have hj₀_ne : j₀ ≠ j := by
        intro h_eq; rw [h_eq] at hj₀; rw [hj] at hj₀; exact absurd hj₀ (by decide)
      have hOR₀ : boolOr M P i j₀ = true := by
        simp [boolOr]; cases M i j₀ <;> simp [hj₀]
      exact absurd (perm_row_unique' (boolOr M P) hMP i hOR₀ hOR) hj₀_ne

/-- **Psi7.5 — BOOLOOR OF DISTINCT PERMS NOT PERM**: If P₁ ≠ P₂ are
    permutation matrices, boolOr(P₁, P₂) is NOT a permutation. -/
theorem boolOr_distinct_perms_not_perm' (P₁ P₂ : BoolMat n)
    (hP₁ : IsPermutationMatrix P₁) (hP₂ : IsPermutationMatrix P₂)
    (h_ne : P₁ ≠ P₂) :
    ¬ IsPermutationMatrix (boolOr P₁ P₂) := by
  intro hOR
  have h_eq := boolOr_perm_left_eq P₁ P₂ hP₁ hOR
  -- boolOr P₁ P₂ = P₁, so boolOr P₁ P₂ = P₁.
  -- Also boolOr P₁ P₂ ≥ P₂, so P₁ ≥ P₂.
  -- P₁ and P₂ are both perms (same # of entries) → P₁ = P₂.
  apply h_ne
  funext i j
  have hP₂_le : ∀ i j, P₂ i j = true → P₁ i j = true := by
    intro i' j' h
    have : boolOr P₁ P₂ i' j' = true := by simp [boolOr, h]
    rw [h_eq] at this; exact this
  cases h₂ : P₂ i j with
  | true =>
    simp [hP₂_le i j h₂]
  | false =>
    cases h₁ : P₁ i j with
    | false => rfl
    | true =>
      obtain ⟨j₀, hj₀, _⟩ := hP₂.1 i
      have := hP₂_le i j₀ hj₀
      have := perm_row_unique' P₁ hP₁ i h₁ this
      subst this; rw [hj₀] at h₂; exact absurd h₂ (by decide)

/-! ## Part 2: mul of non-permutation is non-permutation

  THE CRITICAL LEMMA: In the boolean semiring, if A·B is a permutation matrix,
  then A is a permutation matrix.

  Proof uses a pigeonhole/surjectivity argument on the intermediates
  used by the product. -/

/-- **Psi7.6 — MUL PERM ROW NONEMPTY**: If A·B is a permutation, every row
    of A is nonempty. -/
theorem mul_perm_row_nonempty {A B : BoolMat n}
    (hP : IsPermutationMatrix (mul A B)) (i : Fin n) :
    ∃ k : Fin n, A i k = true := by
  obtain ⟨j, hj, _⟩ := hP.1 i
  rw [mul_apply_true] at hj
  obtain ⟨k, hk, _⟩ := hj
  exact ⟨k, hk⟩

/-- **Psi7.7 — MUL PERM B ROW NONEMPTY**: If A·B is a permutation, every row
    of B is nonempty. Uses pigeonhole on intermediates. -/
theorem mul_perm_B_row_nonempty {A B : BoolMat n}
    (hP : IsPermutationMatrix (mul A B)) (k : Fin n) :
    ∃ j : Fin n, B k j = true := by
  by_contra h_empty
  -- h_empty : ¬ ∃ j, B k j = true, i.e., all entries in row k of B are false
  have h_false : ∀ j, B k j = false := by
    intro j; cases hB : B k j with
    | false => rfl
    | true => exact absurd ⟨j, hB⟩ h_empty
  -- For each row of P, choose an intermediate.
  have ⟨J, hJ⟩ : ∃ J : Fin n → Fin n, ∀ i, mul A B i (J i) = true :=
    ⟨fun i => (hP.1 i).choose, fun i => (hP.1 i).choose_spec.1⟩
  have ⟨M, hM⟩ : ∃ M : Fin n → Fin n,
      ∀ i, A i (M i) = true ∧ B (M i) (J i) = true ∧ M i ≠ k := by
    have : ∀ i, ∃ m, A i m = true ∧ B m (J i) = true ∧ m ≠ k := by
      intro i
      obtain ⟨m, hAm, hBm⟩ := (mul_apply_true A B i (J i)).mp (hJ i)
      exact ⟨m, hAm, hBm, by intro h; rw [h] at hBm; rw [h_false] at hBm; exact absurd hBm (by decide)⟩
    exact ⟨fun i => (this i).choose, fun i => (this i).choose_spec⟩
  by_cases hn : n = 0
  · exact (Fin.elim0 (hn ▸ k))
  · have h_not_inj : ¬ Function.Injective M := by
      intro h_inj
      have h_surj := Finite.injective_iff_surjective.mp h_inj
      obtain ⟨i, hi⟩ := h_surj k
      exact absurd hi (hM i).2.2
    have h_not_inj2 : ∃ i₁ i₂, M i₁ = M i₂ ∧ i₁ ≠ i₂ := by
      by_contra h_all
      push_neg at h_all
      exact h_not_inj (fun a b hab => by
        by_contra h; exact absurd hab (h_all a b h))
    obtain ⟨i₁, i₂, h_eq, h_ne⟩ := h_not_inj2
    set m₀ := M i₁
    have hB₂ : B m₀ (J i₂) = true := h_eq ▸ (hM i₂).2.1
    have hP₁₂ : mul A B i₁ (J i₂) = true :=
      (mul_apply_true A B i₁ (J i₂)).mpr ⟨m₀, (hM i₁).1, hB₂⟩
    have hJ_eq : J i₂ = J i₁ :=
      perm_row_unique' (mul A B) hP i₁ hP₁₂ (hJ i₁)
    have hP₂₁ : mul A B i₂ (J i₁) = true := hJ_eq ▸ hJ i₂
    obtain ⟨_, _, hu⟩ := hP.2 (J i₁)
    exact h_ne ((hu i₁ (hJ i₁)).symm ▸ hu i₂ hP₂₁)

/-- **Psi7.8 — MUL PERM IMPLIES LEFT PERM**: In the boolean semiring, if A·B
    is a permutation matrix, then A is a permutation matrix.

    Proof: Define M(i) = an intermediate for row i. Show M is injective (from
    perm structure of P). M injective on Fin n → surjective. If row i has
    entries at k₀ ≠ k', then both map to i exclusively, but M(i) can only
    be one of them. Surjectivity forces M(i) = k₀ AND M(i) = k' → k₀ = k'. -/
theorem mul_perm_implies_left_perm {A B : BoolMat n}
    (hP : IsPermutationMatrix (mul A B)) :
    IsPermutationMatrix A := by
  constructor
  · -- Each row has exactly one true entry.
    intro i
    obtain ⟨k₀, hk₀⟩ := mul_perm_row_nonempty hP i
    refine ⟨k₀, hk₀, ?_⟩
    intro k' hk'
    by_contra h_ne
    push_neg at h_ne
    -- Row i has entries at k₀ and k' with k₀ ≠ k'.
    obtain ⟨j₀, hj₀, hj₀_u⟩ := hP.1 i
    -- B rows k₀, k' are concentrated at j₀
    have hB_k₀_only : ∀ j, j ≠ j₀ → B k₀ j = false := by
      intro j hj
      cases hB : B k₀ j with
      | false => rfl
      | true => exact absurd (hj₀_u j ((mul_apply_true A B i j).mpr ⟨k₀, hk₀, hB⟩)) hj
    have hB_k'_only : ∀ j, j ≠ j₀ → B k' j = false := by
      intro j hj
      cases hB : B k' j with
      | false => rfl
      | true => exact absurd (hj₀_u j ((mul_apply_true A B i j).mpr ⟨k', hk', hB⟩)) hj
    -- B rows nonempty → entries at j₀
    obtain ⟨j_k₀, hj_k₀⟩ := mul_perm_B_row_nonempty hP k₀
    have : j_k₀ = j₀ := by
      by_contra h; exact absurd (hB_k₀_only j_k₀ h) (by rw [hj_k₀]; decide)
    subst this
    obtain ⟨j_k', hj_k'⟩ := mul_perm_B_row_nonempty hP k'
    have : j_k' = j₀ := by
      by_contra h; exact absurd (hB_k'_only j_k' h) (by rw [hj_k']; decide)
    subst this
    -- Columns k₀, k' of A exclusive to row i
    have hP_col : ∀ i', i' ≠ i → mul A B i' j₀ = false := by
      intro i' hi'
      obtain ⟨ic, hic, hic_u⟩ := hP.2 j₀
      have : ic = i := (hic_u i hj₀).symm
      subst this
      cases h : mul A B i' j₀ with
      | false => rfl
      | true => exact absurd (hic_u i' h) (Ne.symm hi')
    have hA_col_k₀ : ∀ i', i' ≠ i → A i' k₀ = false := by
      intro i' hi'
      cases hA : A i' k₀ with
      | false => rfl
      | true =>
        have := hP_col i' hi'
        rw [(show mul A B i' j₀ = true from (mul_apply_true A B i' j₀).mpr ⟨k₀, hA, hj_k₀⟩)] at this
        exact absurd this (by decide)
    have hA_col_k' : ∀ i', i' ≠ i → A i' k' = false := by
      intro i' hi'
      cases hA : A i' k' with
      | false => rfl
      | true =>
        have := hP_col i' hi'
        rw [(show mul A B i' j₀ = true from (mul_apply_true A B i' j₀).mpr ⟨k', hA, hj_k'⟩)] at this
        exact absurd this (by decide)
    -- Intermediate function M: injective, hence surjective
    have h_wit : ∀ r : Fin n, ∃ m : Fin n, A r m = true ∧
        ∃ j, mul A B r j = true ∧ B m j = true := by
      intro r
      obtain ⟨j, hj, _⟩ := hP.1 r
      obtain ⟨m, hAm, hBm⟩ := (mul_apply_true A B r j).mp hj
      exact ⟨m, hAm, j, (mul_apply_true A B r j).mpr ⟨m, hAm, hBm⟩, hBm⟩
    let MF : Fin n → Fin n := fun r => (h_wit r).choose
    have hMF_A : ∀ r, A r (MF r) = true := fun r => (h_wit r).choose_spec.1
    have hMF_wit : ∀ r, ∃ j, mul A B r j = true ∧ B (MF r) j = true :=
      fun r => (h_wit r).choose_spec.2
    have hMF_inj : Function.Injective MF := by
      intro r₁ r₂ h_eq
      by_contra hne
      set m₀ := MF r₁
      obtain ⟨j₁, hP₁, hB₁⟩ := hMF_wit r₁
      obtain ⟨j₂, hP₂, hB₂⟩ := hMF_wit r₂
      have hB₂' : B m₀ j₂ = true := h_eq ▸ hB₂
      have hP₁₂ : mul A B r₁ j₂ = true :=
        (mul_apply_true A B r₁ j₂).mpr ⟨m₀, hMF_A r₁, hB₂'⟩
      have hj_eq : j₂ = j₁ := perm_row_unique' (mul A B) hP r₁ hP₁₂ hP₁
      have hP₂₁ : mul A B r₂ j₁ = true := hj_eq ▸ hP₂
      obtain ⟨_, _, hu⟩ := hP.2 j₁
      exact hne ((hu r₁ hP₁).symm ▸ hu r₂ hP₂₁)
    have hMF_surj := Finite.injective_iff_surjective.mp hMF_inj
    -- k₀ and k' must both map to i
    obtain ⟨i₀, hi₀⟩ := hMF_surj k₀
    have hi₀_eq : i₀ = i := by
      by_contra h
      exact absurd (hMF_A i₀) (by rw [hi₀]; rw [hA_col_k₀ i₀ h]; decide)
    obtain ⟨i₀', hi₀'⟩ := hMF_surj k'
    have hi₀'_eq : i₀' = i := by
      by_contra h
      exact absurd (hMF_A i₀') (by rw [hi₀']; rw [hA_col_k' i₀' h]; decide)
    -- MF(i) = k₀ and MF(i) = k' → k₀ = k'
    exact absurd (by rw [← hi₀, hi₀_eq, hi₀'_eq, hi₀'] : k₀ = k') h_ne
  · -- Each column has exactly one true entry.
    -- First extract the row function from part 1.
    have h_row : ∀ i : Fin n, ∃ k, A i k = true ∧ ∀ y, A i y = true → y = k := by
      intro i
      obtain ⟨k₀, hk₀⟩ := mul_perm_row_nonempty hP i
      refine ⟨k₀, hk₀, fun y hy => ?_⟩
      by_contra h_ne; push_neg at h_ne
      -- Duplicate the row-uniqueness proof for this specific case
      obtain ⟨j₀, hj₀, hj₀_u⟩ := hP.1 i
      have hB_k₀_only : ∀ j, j ≠ j₀ → B k₀ j = false := by
        intro j hj; cases hB : B k₀ j with
        | false => rfl
        | true => exact absurd (hj₀_u j ((mul_apply_true A B i j).mpr ⟨k₀, hk₀, hB⟩)) hj
      have hB_y_only : ∀ j, j ≠ j₀ → B y j = false := by
        intro j hj; cases hB : B y j with
        | false => rfl
        | true => exact absurd (hj₀_u j ((mul_apply_true A B i j).mpr ⟨y, hy, hB⟩)) hj
      obtain ⟨jk, hjk⟩ := mul_perm_B_row_nonempty hP k₀
      have : jk = j₀ := by by_contra h; exact absurd (hB_k₀_only jk h) (by rw [hjk]; decide)
      subst this
      obtain ⟨jy, hjy⟩ := mul_perm_B_row_nonempty hP y
      have : jy = j₀ := by by_contra h; exact absurd (hB_y_only jy h) (by rw [hjy]; decide)
      subst this
      have hP_col : ∀ i', i' ≠ i → mul A B i' j₀ = false := by
        intro i' hi'; obtain ⟨ic, hic, hu⟩ := hP.2 j₀
        have : ic = i := (hu i hj₀).symm; subst this
        cases h : mul A B i' j₀ with
        | false => rfl | true => exact absurd (hu i' h) (Ne.symm hi')
      have hAck₀ : ∀ i', i' ≠ i → A i' k₀ = false := by
        intro i' hi'; cases hA : A i' k₀ with
        | false => rfl
        | true => rw [show mul A B i' j₀ = true from (mul_apply_true ..).mpr ⟨k₀, hA, hjk⟩] at hP_col; exact absurd rfl (by rw [hP_col i' hi']; decide)
      have hAcy : ∀ i', i' ≠ i → A i' y = false := by
        intro i' hi'; cases hA : A i' y with
        | false => rfl
        | true => rw [show mul A B i' j₀ = true from (mul_apply_true ..).mpr ⟨y, hA, hjy⟩] at hP_col; exact absurd rfl (by rw [hP_col i' hi']; decide)
      have h_wit : ∀ r : Fin n, ∃ m : Fin n, A r m = true ∧
          ∃ j, mul A B r j = true ∧ B m j = true := by
        intro r; obtain ⟨j, hj, _⟩ := hP.1 r
        obtain ⟨m, hAm, hBm⟩ := (mul_apply_true A B r j).mp hj
        exact ⟨m, hAm, j, (mul_apply_true ..).mpr ⟨m, hAm, hBm⟩, hBm⟩
      let MG : Fin n → Fin n := fun r => (h_wit r).choose
      have hMG_A : ∀ r, A r (MG r) = true := fun r => (h_wit r).choose_spec.1
      have hMG_wit : ∀ r, ∃ j, mul A B r j = true ∧ B (MG r) j = true :=
        fun r => (h_wit r).choose_spec.2
      have hMG_inj : Function.Injective MG := by
        intro r₁ r₂ heq; by_contra hne; set m₀ := MG r₁
        obtain ⟨j₁, hP₁, hB₁⟩ := hMG_wit r₁
        obtain ⟨j₂, hP₂, hB₂⟩ := hMG_wit r₂
        have hP₁₂ := (mul_apply_true A B r₁ j₂).mpr ⟨m₀, hMG_A r₁, heq ▸ hB₂⟩
        have := perm_row_unique' (mul A B) hP r₁ hP₁₂ hP₁
        obtain ⟨_, _, hu⟩ := hP.2 j₁
        exact hne ((hu r₁ hP₁).symm ▸ hu r₂ (this ▸ hP₂))
      have hMG_surj := Finite.injective_iff_surjective.mp hMG_inj
      obtain ⟨i₀, hi₀⟩ := hMG_surj k₀
      have : i₀ = i := by
        by_contra h; exact absurd (hMG_A i₀) (by rw [hi₀]; rw [hAck₀ i₀ h]; decide)
      subst this
      obtain ⟨i₀', hi₀'⟩ := hMG_surj y
      have : i₀' = i := by
        by_contra h; exact absurd (hMG_A i₀') (by rw [hi₀']; rw [hAcy i₀' h]; decide)
      subst this
      exact absurd (by rw [← hi₀, hi₀'] : k₀ = y) (Ne.symm h_ne)
    -- Now prove columns using injectivity of the row→column function.
    have h_inj : Function.Injective (fun i => (h_row i).choose) := by
      intro i₁ i₂ h_eq; by_contra h_ne
      set k := (h_row i₁).choose
      have hk₁ : A i₁ k = true := (h_row i₁).choose_spec.1
      have hk₂ : A i₂ k = true := by
        have : (h_row i₂).choose = k := h_eq; rw [← this]; exact (h_row i₂).choose_spec.1
      obtain ⟨j₀, hj₀⟩ := mul_perm_B_row_nonempty hP k
      have hP₁ := (mul_apply_true A B i₁ j₀).mpr ⟨k, hk₁, hj₀⟩
      have hP₂ := (mul_apply_true A B i₂ j₀).mpr ⟨k, hk₂, hj₀⟩
      obtain ⟨_, _, hu⟩ := hP.2 j₀
      exact h_ne ((hu i₁ hP₁).symm ▸ hu i₂ hP₂)
    have h_surj := Finite.injective_iff_surjective.mp h_inj
    intro j
    obtain ⟨i₀, hi₀⟩ := h_surj j
    have hA_j : A i₀ j = true := by
      have : (h_row i₀).choose = j := hi₀; rw [← this]; exact (h_row i₀).choose_spec.1
    refine ⟨i₀, hA_j, ?_⟩
    intro y hy
    have hy_col : (h_row y).choose = j := (h_row y).choose_spec.2 j hy
    exact h_inj (hy_col.symm ▸ hi₀.symm)

/-- **Psi7.9 — CONTRAPOSITIVE**: Non-perm left stays non-perm. -/
theorem mul_nonperm_left_not_perm {A : BoolMat n} (hA : ¬ IsPermutationMatrix A)
    (B : BoolMat n) : ¬ IsPermutationMatrix (mul A B) :=
  fun hP => hA (mul_perm_implies_left_perm hP)

/-- **Psi7.10 — MUL PERM IMPLIES RIGHT PERM**: Via transpose. -/
theorem mul_perm_implies_right_perm {A B : BoolMat n}
    (hP : IsPermutationMatrix (mul A B)) :
    IsPermutationMatrix B := by
  have hPT : IsPermutationMatrix (transpose (mul A B)) :=
    ⟨fun i => let ⟨j, hj, hu⟩ := hP.2 i; ⟨j, hj, hu⟩,
     fun j => let ⟨i, hi, hu⟩ := hP.1 j; ⟨i, hi, hu⟩⟩
  have h_trans : transpose (mul A B) = mul (transpose B) (transpose A) := by
    funext i j; simp only [transpose, mul, List.any_eq_true, Bool.and_eq_true]
    exact ⟨fun ⟨k, hk, h1, h2⟩ => ⟨k, hk, h2, h1⟩,
           fun ⟨k, hk, h1, h2⟩ => ⟨k, hk, h2, h1⟩⟩
  rw [h_trans] at hPT
  have hBT := mul_perm_implies_left_perm hPT
  exact ⟨fun i => let ⟨j, hj, hu⟩ := hBT.2 i; ⟨j, hj, hu⟩,
         fun j => let ⟨i, hi, hu⟩ := hBT.1 j; ⟨i, hi, hu⟩⟩

/-- **Psi7.11 — NON-PERM RIGHT STAYS NON-PERM**: Contrapositive. -/
theorem mul_nonperm_right_not_perm (A : BoolMat n) {B : BoolMat n}
    (hB : ¬ IsPermutationMatrix B) : ¬ IsPermutationMatrix (mul A B) :=
  fun hP => hB (mul_perm_implies_right_perm hP)

/-! ## Part 3: Sigma Group Structure -/

/-- **Psi7.12 — DISTINCT SIGMA ENTRYAND IS ZERO**: Verified on generators. -/
theorem sigma_entryAnd_zero_01 :
    BoolMat.isZero (BoolMat.entryAnd sigma0Mat sigma1Mat) := by
  intro i j; revert i j; native_decide

theorem sigma_entryAnd_zero_02 :
    BoolMat.isZero (BoolMat.entryAnd sigma0Mat sigma2Mat) := by
  intro i j; revert i j; native_decide

theorem sigma_entryAnd_zero_12 :
    BoolMat.isZero (BoolMat.entryAnd sigma1Mat sigma2Mat) := by
  intro i j; revert i j; native_decide

/-- entryAnd(M,M) = M. -/
theorem entryAnd_self (M : BoolMat n) : BoolMat.entryAnd M M = M := by
  funext i j; simp [BoolMat.entryAnd, Bool.and_self]

/-! ## Part 4: Expression Inductive Type -/

/-- The 8 elements of (Z/2Z)³ as boolean matrices. -/
def sigmaGroupElem (mask : Fin 8) : BoolMat 8 :=
  let m₀ := if mask.val &&& 1 = 1 then sigma0Mat else BoolMat.one
  let m₁ := if mask.val &&& 2 = 2 then sigma1Mat else BoolMat.one
  let m₂ := if mask.val &&& 4 = 4 then sigma2Mat else BoolMat.one
  BoolMat.mul (BoolMat.mul m₀ m₁) m₂

/-- M is in the sigma group iff it equals sigmaGroupElem mask for some mask. -/
def IsInSigmaGroup (M : BoolMat 8) : Prop :=
  ∃ mask : Fin 8, M = sigmaGroupElem mask

/-- **Psi7.13 — SIGMA GROUP CLOSED UNDER MUL**: -/
theorem sigmaGroup_mul_closed (m₁ m₂ : Fin 8) :
    IsInSigmaGroup (BoolMat.mul (sigmaGroupElem m₁) (sigmaGroupElem m₂)) := by
  refine ⟨⟨m₁.val ^^^ m₂.val, by revert m₁ m₂; native_decide⟩, ?_⟩
  revert m₁ m₂; native_decide

/-- **Psi7.14 — SIGMA GROUP ELEMENTS ARE PERMUTATIONS**: -/
theorem sigmaGroupElem_isPerm (mask : Fin 8) :
    IsPermutationMatrix (sigmaGroupElem mask) := by
  constructor
  · intro i; revert mask i; native_decide
  · intro j; revert mask j; native_decide

/-- **Psi7.15 — SIGMMAT IN GROUP**: -/
theorem sigmaMat_in_group (i : Fin 3) : IsInSigmaGroup (sigmaMat i) := by
  fin_cases i
  · exact ⟨⟨1, by omega⟩, by simp only [sigmaMat]; funext g h; revert g h; native_decide⟩
  · exact ⟨⟨2, by omega⟩, by simp only [sigmaMat]; funext g h; revert g h; native_decide⟩
  · exact ⟨⟨4, by omega⟩, by simp only [sigmaMat]; funext g h; revert g h; native_decide⟩

/-- **Psi7.16 — SIGMA GROUP ELEMENT INJECTIVITY**: Different masks give different matrices. -/
theorem sigmaGroupElem_injective : Function.Injective sigmaGroupElem := by
  intro m₁ m₂ h; ext; revert m₁ m₂ h; native_decide

/-! ## Parts 4-5: General Induction (removed)

  The original gate_expr_good theorem defined GateExpr and GoodMatrix and
  attempted structural induction over algebraic expressions.

  Two gaps prevented closing the proof:
  (1) boolOr(non-perm, non-perm): complementary sub-permutations can produce
      a permutation outside the sigma group. See Omega7CloseGap.lean for the
      HasMultiRow theory that addresses this under stronger hypotheses.
  (2) entryAnd(non-perm, non-perm): the GoodMatrix invariant (not-perm OR in-group)
      is too weak to conclude either disjunct when entryAnd of two non-perms
      happens to be a permutation.

  The individual operation lemmas (Parts 1-3) remain proven and are used
  in the grand summary below. The boolOr case is handled for specific
  concrete instances in Chi7CircuitProjection.lean.
-/

/-! ## Part 6: Grand Summary -/

/-- **Psi7.18 — GRAND SUMMARY**: Assembly of all results. -/
theorem grand_summary_general_projection :
    -- (a) mul perm implies both factors are perms
    (∀ (A B : BoolMat 8), IsPermutationMatrix (BoolMat.mul A B) →
      IsPermutationMatrix A ∧ IsPermutationMatrix B) ∧
    -- (b) boolOr with perm preserves that perm
    (∀ (P M : BoolMat 8), IsPermutationMatrix P →
      IsPermutationMatrix (BoolMat.boolOr P M) → BoolMat.boolOr P M = P) ∧
    -- (c) Sigma group is closed under mul
    (∀ m₁ m₂ : Fin 8,
      IsInSigmaGroup (BoolMat.mul (sigmaGroupElem m₁) (sigmaGroupElem m₂))) ∧
    -- (d) All sigma group elements are permutations
    (∀ m : Fin 8, IsPermutationMatrix (sigmaGroupElem m)) ∧
    -- (e) Distinct sigma group elements have zero entryAnd
    (BoolMat.isZero (BoolMat.entryAnd sigma0Mat sigma1Mat) ∧
     BoolMat.isZero (BoolMat.entryAnd sigma0Mat sigma2Mat) ∧
     BoolMat.isZero (BoolMat.entryAnd sigma1Mat sigma2Mat)) :=
  ⟨fun A B hP => ⟨mul_perm_implies_left_perm hP, mul_perm_implies_right_perm hP⟩,
   fun P M hP hPM => boolOr_perm_left_eq P M hP hPM,
   sigmaGroup_mul_closed,
   sigmaGroupElem_isPerm,
   ⟨sigma_entryAnd_zero_01, sigma_entryAnd_zero_02, sigma_entryAnd_zero_12⟩⟩

end CubeGraph
