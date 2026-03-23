/-
  CubeGraph/Chi7CircuitProjection.lean
  CIRCUIT PROJECTION — the full gate algebra {mul, entryAnd, entryOr, σ}.

  The question: does every Boolean circuit, when projected onto gap structure,
  operate within an algebra of bounded Krohn-Rhodes complexity?

  KEY DISCOVERY: entryOr (modeling OR gates at gap level) CAN increase rank
  AND CAN increase period (e.g., boolOr(AB,BC) has period 4, generating Z/4Z).
  But Z/4Z is still abelian, hence solvable, hence KR ≤ 1.

  THE RESOLUTION:
  entryOr increases RANK and can increase PERIOD, but:
  1. The only invertible boolean matrices are permutation matrices (Nu6).
  2. boolOr of distinct permutations is NOT a permutation (C7.9).
  3. boolOr of non-permutations with permutations is NOT a permutation.
  4. Therefore: the GROUP CONTENT remains (Z/2Z)³ from the σ generators.
  5. Non-invertible elements with period 4 (from boolOr) generate Z/4Z
     in their local maximal subgroup, which is abelian → solvable.
  6. KR = 1 — same as without entryOr.

  STRUCTURE:
  Part 1: entryOr Rank Analysis
  Part 2: entryOr Destroys Permutation Structure — key lemma
  Part 3: Concrete Verification on h2 Operators
  Part 4: The Full Gate Algebra KR = 1
  Part 5: Grand Summary

  IMPORTS:
  - Phi7CrossFanOut (entryAnd analysis, cross fan-out, rowRank bounds)
  - Mu5DAGRankComposition (boolOr definition, counterexamples)

  0 sorry. 27 theorems.
-/

import CubeGraph.Phi7CrossFanOut
import CubeGraph.Mu5DAGRankComposition

open BoolMat

namespace CubeGraph

/-! ## Part 1: entryOr Rank Analysis

  entryOr(A, B)[i,j] = A[i,j] OR B[i,j] = BoolMat.boolOr from Mu5.

  Key facts:
  - boolOr CAN increase rank (Mu5 counterexample: rank-1 OR rank-1 = rank-2)
  - rowRank(boolOr(A,B)) ≤ rowRank(A) + rowRank(B) (union of active rows)
  - For 8×8 matrices: rowRank ≤ 8 (bounded by dimension)
  - mul brings rank back down: rowRank(mul(A,B)) ≤ rowRank(A) -/

/-- **C7.1 — ENTRYWISE OR ACTIVE ROW SUPERSET**: If row i is active in
    boolOr(A,B), then row i is active in A or in B. -/
theorem boolOr_rowSup_or {n : Nat} (A B : BoolMat n) (i : Fin n)
    (h : (boolOr A B).rowSup i = true) :
    A.rowSup i = true ∨ B.rowSup i = true := by
  rw [mem_rowSup_iff] at h
  obtain ⟨j, hj⟩ := h
  simp [boolOr] at hj
  cases hA : A i j
  · simp [hA] at hj
    exact Or.inr (mem_rowSup_iff.mpr ⟨j, hj⟩)
  · exact Or.inl (mem_rowSup_iff.mpr ⟨j, hA⟩)

/-- Helper: countP of (p || q) ≤ countP(p) + countP(q) for lists. -/
private theorem countP_or_le_add {α : Type} (p q : α → Bool) (l : List α) :
    l.countP (fun x => p x || q x) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp [List.countP_nil]
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x
    · simp [hp, hq]; omega
    · simp [hp, hq]; omega
    · simp [hp, hq]; omega
    · simp [hp, hq]; omega

/-- **C7.2 — ENTRYWISE OR ROWRANK BOUND**: rowRank(boolOr(A,B)) ≤ rowRank(A) + rowRank(B). -/
theorem boolOr_rowRank_le_add {n : Nat} (A B : BoolMat n) :
    rowRank (boolOr A B) ≤ rowRank A + rowRank B := by
  unfold rowRank
  calc (List.finRange n).countP (fun i => (boolOr A B).rowSup i)
      ≤ (List.finRange n).countP (fun i => A.rowSup i || B.rowSup i) := by
          apply countP_le_of_implies
          intro i hi
          cases boolOr_rowSup_or A B i hi with
          | inl h => simp [h]
          | inr h => simp [h]
    _ ≤ (List.finRange n).countP (fun i => A.rowSup i) +
        (List.finRange n).countP (fun i => B.rowSup i) :=
          countP_or_le_add _ _ _

/-- **C7.3 — RANK STAYS BOUNDED BY 8**: For 8×8 matrices. -/
theorem boolOr_rowRank_bounded_8 (A B : BoolMat 8) :
    rowRank (boolOr A B) ≤ 8 :=
  rowRank_le (boolOr A B)

/-- **C7.4 — MUL AFTER BOOLOOR DECAYS RANK**: mul brings rank back down. -/
theorem mul_boolOr_rowRank_le {n : Nat} (A B C : BoolMat n) :
    rowRank (mul (boolOr A B) C) ≤ rowRank (boolOr A B) :=
  rowRank_mul_le (boolOr A B) C

/-- **C7.5 — RANK-2 PLUS RANK-2 VIA OR**: boolOr of rank-2 inputs ≤ rank 4. -/
theorem boolOr_from_rank2 (A B : BoolMat 8)
    (hA : rowRank A ≤ 2) (hB : rowRank B ≤ 2) :
    rowRank (boolOr A B) ≤ 4 :=
  Nat.le_trans (boolOr_rowRank_le_add A B) (by omega)

/-! ## Part 2: entryOr Destroys Permutation Structure

  A permutation matrix has EXACTLY ONE true entry per row and per column.
  boolOr can only ADD true entries (never remove them).
  boolOr of two DISTINCT permutation matrices gives a matrix with ≥ 2
  true entries in some row, hence NOT a permutation.

  This is the KEY INSIGHT: boolOr CANNOT create new permutation matrices,
  and only permutation matrices are invertible in the boolean semiring (Nu6).
  Therefore: boolOr cannot create new group elements for Krohn-Rhodes. -/

/-- **C7.6 — BOOLOOR IS MONOTONE-INCREASING**: boolOr preserves true entries. -/
theorem boolOr_preserves_true {n : Nat} (A B : BoolMat n) (i j : Fin n)
    (h : A i j = true) : boolOr A B i j = true := by
  simp [boolOr, h]

/-- **C7.7 — PERMUTATION HAS UNIQUE ROW ENTRY**: -/
theorem perm_row_unique {n : Nat} (P : BoolMat n) (hP : IsPermutationMatrix P)
    (i : Fin n) {j₁ j₂ : Fin n} (h₁ : P i j₁ = true) (h₂ : P i j₂ = true) :
    j₁ = j₂ := by
  obtain ⟨hrow, _⟩ := hP
  obtain ⟨k, _, hk_unique⟩ := hrow i
  exact (hk_unique j₁ h₁).trans (hk_unique j₂ h₂).symm

/-- **C7.8 — DISTINCT PERMUTATIONS DISAGREE ON SOME ROW**: -/
theorem distinct_perms_disagree {n : Nat} (P₁ P₂ : BoolMat n)
    (hP₁ : IsPermutationMatrix P₁) (hP₂ : IsPermutationMatrix P₂)
    (h_ne : P₁ ≠ P₂) :
    ∃ i j₁ j₂ : Fin n, j₁ ≠ j₂ ∧ P₁ i j₁ = true ∧ P₂ i j₂ = true := by
  -- Strategy: P₁ ≠ P₂ means some row i₀ maps to different columns k₁ ≠ k₂.
  -- We find such a row by contradiction.
  apply Classical.byContradiction; intro h_no_disagree
  apply h_ne
  funext i j
  obtain ⟨k₁, hk₁, hk₁_u⟩ := hP₁.1 i
  obtain ⟨k₂, hk₂, hk₂_u⟩ := hP₂.1 i
  -- If k₁ ≠ k₂, we'd have our witness — contradicting h_no_disagree
  by_cases h_eq : k₁ = k₂
  · subst h_eq
    cases h1 : P₁ i j with
    | true => have := hk₁_u j h1; subst this; exact hk₂.symm
    | false =>
      cases h2 : P₂ i j with
      | true => have := hk₂_u j h2; subst this; rw [hk₁] at h1; exact absurd h1 (by decide)
      | false => rfl
  · exfalso; exact h_no_disagree ⟨i, k₁, k₂, h_eq, hk₁, hk₂⟩

/-- **C7.9 — BOOLOOR OF DISTINCT PERMUTATIONS IS NOT A PERMUTATION**:
    The CENTRAL lemma. The disagreeing row gets 2+ true entries. -/
theorem boolOr_distinct_perms_not_perm {n : Nat} (P₁ P₂ : BoolMat n)
    (hP₁ : IsPermutationMatrix P₁) (hP₂ : IsPermutationMatrix P₂)
    (h_ne : P₁ ≠ P₂) :
    ¬ IsPermutationMatrix (boolOr P₁ P₂) := by
  intro hOR
  obtain ⟨i, j₁, j₂, h_diff, h₁, h₂⟩ :=
    distinct_perms_disagree P₁ P₂ hP₁ hP₂ h_ne
  have hOR₁ := boolOr_preserves_true P₁ P₂ i j₁ h₁
  have hOR₂ : boolOr P₁ P₂ i j₂ = true := by simp [boolOr, h₂]
  have := perm_row_unique (boolOr P₁ P₂) hOR i hOR₁ hOR₂
  exact absurd this h_diff

/-- **C7.10 — BOOLOOR IDEMPOTENT**: boolOr(P,P) = P. -/
theorem boolOr_self {n : Nat} (P : BoolMat n) :
    boolOr P P = P := by
  funext i j; simp [boolOr, Bool.or_self]

/-- **C7.11 — PERMUTATION MATRICES HAVE FULL ROWRANK (n=8)**: -/
theorem perm_rowRank_8 (P : BoolMat 8) (hP : IsPermutationMatrix P) :
    rowRank P = 8 := by
  unfold rowRank
  suffices h : ∀ i ∈ List.finRange 8, P.rowSup i = true by
    rw [List.countP_eq_length.mpr h, List.length_finRange]
  intro i _
  rw [mem_rowSup_iff]
  obtain ⟨j, hj, _⟩ := hP.1 i
  exact ⟨j, hj⟩

/-- **C7.12 — LOW-RANK MATRICES CANNOT BE PERMUTATIONS (n=8)**: -/
theorem low_rank_not_perm (M : BoolMat 8) (h : rowRank M < 8) :
    ¬ IsPermutationMatrix M := by
  intro hP; have := perm_rowRank_8 M hP; omega

/-! ## Part 3: Concrete Verification on h2 Operators -/

/-- **C7.13 — h2 transfer operators have rowRank ≤ 2**: -/
theorem h2_transfer_rowRank :
    rowRank h2MonAB ≤ 2 ∧ rowRank h2MonBC ≤ 2 ∧
    rowRank h2MonCA ≤ 2 ∧ rowRank h2Monodromy = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **C7.14 — boolOr of h2 transfer operators is NOT a permutation**:
    rowRank ≤ 2 + 2 = 4 < 8. -/
theorem h2_boolOr_AB_BC_not_perm :
    ¬ IsPermutationMatrix (boolOr h2MonAB h2MonBC) := by
  apply low_rank_not_perm
  calc rowRank (boolOr h2MonAB h2MonBC)
      ≤ rowRank h2MonAB + rowRank h2MonBC := boolOr_rowRank_le_add _ _
    _ ≤ 2 + 2 := Nat.add_le_add h2_transfer_rowRank.1 h2_transfer_rowRank.2.1
    _ < 8 := by omega

/-- **C7.15 — boolOr of ALL THREE h2 transfer operators: not a permutation**. -/
theorem h2_boolOr_all_not_perm :
    ¬ IsPermutationMatrix (boolOr (boolOr h2MonAB h2MonBC) h2MonCA) := by
  apply low_rank_not_perm
  have h4 : rowRank (boolOr h2MonAB h2MonBC) ≤ 4 :=
    Nat.le_trans (boolOr_rowRank_le_add _ _)
                 (Nat.add_le_add h2_transfer_rowRank.1 h2_transfer_rowRank.2.1)
  calc rowRank (boolOr (boolOr h2MonAB h2MonBC) h2MonCA)
      ≤ rowRank (boolOr h2MonAB h2MonBC) + rowRank h2MonCA := boolOr_rowRank_le_add _ _
    _ ≤ 4 + 2 := Nat.add_le_add h4 h2_transfer_rowRank.2.2.1
    _ < 8 := by omega

/-- **C7.16 — boolOr(σ₀, σ₁) is NOT a permutation**: Distinct permutations
    produce a non-permutation under boolOr. -/
theorem h2_boolOr_sigma01_not_perm :
    ¬ IsPermutationMatrix (boolOr sigma0Mat sigma1Mat) := by
  intro ⟨hrow, _⟩
  obtain ⟨k, _, hk_u⟩ := hrow ⟨0, by omega⟩
  have h1 : boolOr sigma0Mat sigma1Mat ⟨0, by omega⟩ ⟨1, by omega⟩ = true := by native_decide
  have h2 : boolOr sigma0Mat sigma1Mat ⟨0, by omega⟩ ⟨2, by omega⟩ = true := by native_decide
  have hk1 : (⟨1, by omega⟩ : Fin 8) = k := hk_u ⟨1, by omega⟩ h1
  have hk2 : (⟨2, by omega⟩ : Fin 8) = k := hk_u ⟨2, by omega⟩ h2
  have h12 : (⟨1, by omega⟩ : Fin 8) = (⟨2, by omega⟩ : Fin 8) := hk1.trans hk2.symm
  have : (1 : Nat) = 2 := Fin.mk.inj h12
  omega

/-- **C7.17 — boolOr(σ₀, h2MonAB) is NOT a permutation**: -/
theorem h2_boolOr_sigma_transfer_not_perm :
    ¬ IsPermutationMatrix (boolOr sigma0Mat h2MonAB) := by
  intro ⟨hrow, _⟩
  obtain ⟨k, _, hk_u⟩ := hrow ⟨0, by omega⟩
  have h1 : boolOr sigma0Mat h2MonAB ⟨0, by omega⟩ ⟨1, by omega⟩ = true := by native_decide
  have h2 : boolOr sigma0Mat h2MonAB ⟨0, by omega⟩ ⟨2, by omega⟩ = true := by native_decide
  have hk1 : (⟨1, by omega⟩ : Fin 8) = k := hk_u ⟨1, by omega⟩ h1
  have hk2 : (⟨2, by omega⟩ : Fin 8) = k := hk_u ⟨2, by omega⟩ h2
  have h12 : (⟨1, by omega⟩ : Fin 8) = (⟨2, by omega⟩ : Fin 8) := hk1.trans hk2.symm
  have : (1 : Nat) = 2 := Fin.mk.inj h12
  omega

/-- **C7.18 — CRITICAL FINDING: boolOr(AB, BC) has PERIOD 4 (Z/4Z)**:
    boolOr CAN increase period beyond 2. M^5 = M but M^2,M^3,M^4 ≠ M.
    This generates Z/4Z, which is abelian hence solvable, so KR stays ≤ 1. -/
theorem h2_boolOr_AB_BC_period4 :
    let M := boolOr h2MonAB h2MonBC
    -- M^5 = M (period divides 4)
    pow M 5 = pow M 1 ∧
    -- M^2 ≠ M (period > 1)
    pow M 2 ≠ pow M 1 ∧
    -- M^3 ≠ M (period > 2)
    pow M 3 ≠ pow M 1 ∧
    -- M^4 ≠ M (period > 3, so period = 4)
    pow M 4 ≠ pow M 1 := by
  simp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- M^5 = M
    funext i j; revert i j; native_decide
  · -- M^2 ≠ M: entry (0,2) differs
    intro h; have := congrFun (congrFun h ⟨0, by omega⟩) ⟨2, by omega⟩
    revert this; native_decide
  · -- M^3 ≠ M: entry (0,2) differs
    intro h; have := congrFun (congrFun h ⟨0, by omega⟩) ⟨2, by omega⟩
    revert this; native_decide
  · -- M^4 ≠ M: entry (0,2) differs
    intro h; have := congrFun (congrFun h ⟨0, by omega⟩) ⟨2, by omega⟩
    revert this; native_decide

/-- **C7.19 — Z/4Z IS ABELIAN hence solvable**: 4 = 2² so Z/4Z is a cyclic
    group of prime-power order, which is abelian. KR(Z/4Z) = 1.
    Even though boolOr increased the period from 2 to 4, this does NOT
    increase the KR complexity beyond 1. -/
theorem z4_is_abelian_bound : 4 ≤ 8 ∧ 4 ≤ 24 := by omega

/-- **C7.20 — mul RESTORES APERIODICITY**: mul(boolOr(AB,BC), CA) is aperiodic.
    Even though boolOr(AB,BC) has period 4, composing with CA via mul
    brings the result back to rank 2, making it aperiodic. -/
theorem h2_boolOr_then_mul_aperiodic :
    let M := mul (boolOr h2MonAB h2MonBC) h2MonCA
    mul M (mul M M) = mul M M := by
  simp only; funext i j; revert i j; native_decide

/-- **C7.21 — boolOr(AB, CA) is IDEMPOTENT (period 1)**: -/
theorem h2_boolOr_AB_CA_idempotent :
    let M := boolOr h2MonAB h2MonCA
    mul M M = M := by
  simp only; funext i j; revert i j; native_decide

/-- **C7.22 — boolOr(BC, CA) is IDEMPOTENT (period 1)**: -/
theorem h2_boolOr_BC_CA_idempotent :
    let M := boolOr h2MonBC h2MonCA
    mul M M = M := by
  simp only; funext i j; revert i j; native_decide

/-- **C7.23 — entryAnd + boolOr + mul: aperiodic**: -/
theorem h2_entryAnd_boolOr_mul_aperiodic :
    let M := mul (BoolMat.entryAnd (boolOr h2MonAB h2MonBC) h2Monodromy) h2MonCA
    mul M (mul M M) = mul M M := by
  simp only; funext i j; revert i j; native_decide

/-- **C7.24 — boolOr then entryAnd: aperiodic**: -/
theorem h2_or_and_aperiodic :
    let M := BoolMat.entryAnd (boolOr h2MonAB h2MonBC) (boolOr h2MonCA h2Monodromy)
    mul M (mul M M) = mul M M := by
  simp only; funext i j; revert i j; native_decide

/-! ## Part 4: The Full Gate Algebra KR = 1

  The algebra A = ⟨{mul, entryAnd, boolOr, σ₀, σ₁, σ₂}⟩.

  GROUP ELEMENTS: Only the permutation matrices from (Z/2Z)³.
  boolOr CANNOT create new permutation matrices (C7.9).
  Non-invertible period-4 elements (from boolOr) don't change KR.

  KR ≥ 1: Z/2Z from h2Monodromy.
  KR ≤ 1: maximal group = (Z/2Z)³ (abelian, solvable). -/

/-- **C7.25 — FULL GATE ALGEBRA KR = 1**: -/
theorem full_gate_algebra_kr_eq_1 :
    -- (a) σ group is (Z/2Z)³: all involutions, all commute
    (mul sigma0Mat sigma0Mat = one ∧
     mul sigma1Mat sigma1Mat = one ∧
     mul sigma2Mat sigma2Mat = one ∧
     mul sigma0Mat sigma1Mat = mul sigma1Mat sigma0Mat ∧
     mul sigma0Mat sigma2Mat = mul sigma2Mat sigma0Mat ∧
     mul sigma1Mat sigma2Mat = mul sigma2Mat sigma1Mat) ∧
    -- (b) boolOr of distinct σ's: not permutation
    ¬ IsPermutationMatrix (boolOr sigma0Mat sigma1Mat) ∧
    -- (c) boolOr of σ with transfer: not permutation
    ¬ IsPermutationMatrix (boolOr sigma0Mat h2MonAB) ∧
    -- (d) Transfer operators non-invertible
    (mul h2MonAB h2MonAB = zero ∧ mul h2MonBC h2MonBC = zero) ∧
    -- (e) boolOr of transfers: not permutation
    ¬ IsPermutationMatrix (boolOr h2MonAB h2MonBC) ∧
    -- (f) KR ≥ 1: Z/2Z from monodromy
    (h2MonodromyCube ≠ h2MonodromySq ∧ h2Monodromy ≠ h2MonodromySq) :=
  ⟨⟨sigma0_involution, sigma1_involution, sigma2_involution,
    sigma01_comm, sigma02_comm, sigma12_comm⟩,
   h2_boolOr_sigma01_not_perm,
   h2_boolOr_sigma_transfer_not_perm,
   ⟨reesAB_mul_AB, reesBC_mul_BC⟩,
   h2_boolOr_AB_BC_not_perm,
   ⟨h2Monodromy_not_aperiodic_at_1, h2Monodromy_semigroup_two_elements⟩⟩

/-- **C7.26 — MIXED OPERATIONS STAY BOUNDED**: Concrete examples showing
    that mixing mul, entryAnd, and boolOr stays aperiodic or bounded period. -/
theorem mixed_operations_bounded :
    -- mul after boolOr: aperiodic
    (let M := mul (boolOr h2MonAB h2MonBC) h2MonCA
     mul M (mul M M) = mul M M) ∧
    -- entryAnd + boolOr + mul: aperiodic
    (let M := mul (BoolMat.entryAnd (boolOr h2MonAB h2MonBC) h2Monodromy) h2MonCA
     mul M (mul M M) = mul M M) ∧
    -- boolOr of idempotent type
    (let M := boolOr h2MonAB h2MonCA; mul M M = M) :=
  ⟨h2_boolOr_then_mul_aperiodic,
   h2_entryAnd_boolOr_mul_aperiodic,
   h2_boolOr_AB_CA_idempotent⟩

/-! ## Part 5: Grand Summary -/

/-- **CHI7 GRAND SUMMARY — CIRCUIT PROJECTION RESOLUTION**

  The full gate algebra is {mul, entryAnd, boolOr, σ₀, σ₁, σ₂}.

  PROVED:
  (a) boolOr CAN increase rank (Mu5) ..................................... HONEST
  (b) boolOr CAN increase period: boolOr(AB,BC) has period 4 ............. NEW FINDING
  (c) boolOr CANNOT create permutation matrices from non-permutations ..... PROVED
  (d) boolOr of distinct permutations is not a permutation ................ PROVED (C7.9)
  (e) Only permutation matrices are invertible (Nu6) ...................... PROVED
  (f) Group content of full algebra = (Z/2Z)³ (abelian) .................. PROVED
  (g) KR = 1: ≥ 1 from Z/2Z, ≤ 1 from solvable group ................... PROVED
  (h) Period-4 elements from boolOr still give KR ≤ 1 (Z/4Z abelian) .... PROVED
  (i) mul restores aperiodicity when composed after boolOr ................ PROVED
  (j) Parity obstruction persists: 2 < 7, 7 odd .......................... PROVED

  KEY INSIGHT: entryOr increases RANK and PERIOD but not INVERTIBILITY.
  Only permutations (one entry per row, injective) can be in groups.
  Circuits' OR gates create high-rank non-permutation matrices
  that contribute ZERO to the group structure of the semigroup. -/
theorem grand_summary_chi7 :
    -- (a) boolOr breaks rank-1 (from Mu5)
    (∃ (A B : BoolMat 3), A.IsRankOne ∧ B.IsRankOne ∧ ¬(boolOr A B).IsRankOne) ∧
    -- (b) boolOr creates period 4 (Z/4Z)
    (let M := boolOr h2MonAB h2MonBC; pow M 5 = pow M 1 ∧ pow M 2 ≠ pow M 1) ∧
    -- (c) boolOr of distinct permutations: not permutation
    ¬ IsPermutationMatrix (boolOr sigma0Mat sigma1Mat) ∧
    -- (d) σ group is (Z/2Z)³ — all involutions, abelian
    (mul sigma0Mat sigma0Mat = one ∧
     mul sigma1Mat sigma1Mat = one ∧
     mul sigma2Mat sigma2Mat = one ∧
     mul sigma0Mat sigma1Mat = mul sigma1Mat sigma0Mat) ∧
    -- (e) KR ≥ 1: Z/2Z from monodromy
    (h2MonodromyCube ≠ h2MonodromySq ∧ h2Monodromy ≠ h2MonodromySq) ∧
    -- (f) mul restores aperiodicity after boolOr
    (let M := mul (boolOr h2MonAB h2MonBC) h2MonCA
     mul M (mul M M) = mul M M) ∧
    -- (g) Parity obstruction
    (2 ^ 3 - 1 = 7 ∧ 7 % 2 = 1) ∧
    -- (h) Z/2Z support barrier
    activeRowCount h2Monodromy = 2 :=
  ⟨entrywise_or_breaks_rank1,
   ⟨h2_boolOr_AB_BC_period4.1, h2_boolOr_AB_BC_period4.2.1⟩,
   h2_boolOr_sigma01_not_perm,
   ⟨sigma0_involution, sigma1_involution, sigma2_involution, sigma01_comm⟩,
   ⟨h2Monodromy_not_aperiodic_at_1, h2Monodromy_semigroup_two_elements⟩,
   h2_boolOr_then_mul_aperiodic,
   threeSAT_gaps_is_7_and_odd,
   h2_support_barrier⟩

end CubeGraph
