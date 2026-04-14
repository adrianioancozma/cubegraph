/-
  CubeGraph/BooleanInvolution.lean
  BOOLEAN INVOLUTION CONJECTURE — PROVED.

  THEOREM: Every boolean matrix M with M² = I (in the OR/AND semiring)
  is a permutation matrix (exactly one 1 per row and per column),
  and the corresponding permutation is an involution (σ² = id).

  PROOF SKETCH:
  M² = I means:
    Diagonal: ∀ i, ∃ k, M[i,k] ∧ M[k,i]         (self-return path exists)
    Off-diag: ∀ i≠j, ∀ k, ¬(M[i,k] ∧ M[k,j])    (no length-2 path between distinct)

  Step 1: If M[i,k]=true, then row k has M[k,j]=false for all j≠i.
  Step 2: So if M[i,k]=true, row k has at most one true entry (at position i).
          The diagonal condition forces exactly one: M[k,i]=true.
  Step 3: Row i has at most one true entry.
  Step 4: Each row has EXACTLY one true entry → permutation matrix → involution.

  See: SyntacticMonoid.lean (IsInvolution definition)
  See: SyntacticConsequences.lean (permMatrix definition)
-/

import CubeGraph.SyntacticConsequences

namespace BoolMat

variable {n : Nat}

/-! ## Part 1: Core Definitions -/

/-- A boolean matrix is a permutation matrix iff each row has exactly one true entry
    and each column has exactly one true entry. -/
def IsPermutationMatrix (M : BoolMat n) : Prop :=
  (∀ i : Fin n, ∃ j : Fin n, M i j = true ∧ ∀ y : Fin n, M i y = true → y = j) ∧
  (∀ j : Fin n, ∃ i : Fin n, M i j = true ∧ ∀ y : Fin n, M y j = true → y = i)

/-! ## Part 2: The Row Exclusivity Lemma -/

/-- If M²=I then off-diagonal entries of M² are false. -/
theorem involution_off_diag {M : BoolMat n} (h_inv : IsInvolution M)
    {i j : Fin n} (h_ne : i ≠ j) :
    mul M M i j = false := by
  have : mul M M = one := h_inv
  rw [this]; simp [one, h_ne]

/-- If M²=I then diagonal entries of M² are true. -/
theorem involution_diag {M : BoolMat n} (h_inv : IsInvolution M)
    (i : Fin n) :
    mul M M i i = true := by
  have : mul M M = one := h_inv
  rw [this]; simp [one]

/-- If M²=I and M[i,k]=true, then M[k,j]=false for all j≠i.
    This is the fundamental constraint: a true entry M[i,k] forces
    row k to be "exclusive" to column i. -/
theorem involution_row_exclusive {M : BoolMat n} (h_inv : IsInvolution M)
    {i k : Fin n} (h_ik : M i k = true) (j : Fin n) (h_ne : j ≠ i) :
    M k j = false := by
  cases h : M k j with
  | false => rfl
  | true =>
    have h_sq : mul M M i j = true :=
      (mul_apply_true M M i j).mpr ⟨k, h_ik, h⟩
    have h_off := involution_off_diag h_inv (Ne.symm h_ne)
    rw [h_off] at h_sq
    exact absurd h_sq (by decide)

/-- If M²=I and M[i,k]=true, then M[k,i]=true. -/
theorem involution_entry_reflects {M : BoolMat n} (h_inv : IsInvolution M)
    {i k : Fin n} (h_ik : M i k = true) :
    M k i = true := by
  obtain ⟨p, hp1, _⟩ := (mul_apply_true M M k k).mp (involution_diag h_inv k)
  by_cases h_eq : p = i
  · rw [h_eq] at hp1; exact hp1
  · exact absurd hp1 (by rw [involution_row_exclusive h_inv h_ik p h_eq]; decide)

/-! ## Part 3: Each Row Has Exactly One True Entry -/

/-- If M²=I, row i has at least one true entry. -/
theorem involution_row_nonempty {M : BoolMat n} (h_inv : IsInvolution M)
    (i : Fin n) : ∃ k : Fin n, M i k = true := by
  obtain ⟨k, hk, _⟩ := (mul_apply_true M M i i).mp (involution_diag h_inv i)
  exact ⟨k, hk⟩

/-- If M²=I, row i has at most one true entry. -/
theorem involution_row_unique {M : BoolMat n} (h_inv : IsInvolution M)
    (i : Fin n) {k₁ k₂ : Fin n} (h1 : M i k₁ = true) (h2 : M i k₂ = true) :
    k₁ = k₂ := by
  by_cases h_eq : k₁ = k₂
  · exact h_eq
  · have hk1i := involution_entry_reflects h_inv h1
    have h_sq : mul M M k₁ k₂ = true :=
      (mul_apply_true M M k₁ k₂).mpr ⟨i, hk1i, h2⟩
    exact absurd h_sq (by rw [involution_off_diag h_inv h_eq]; decide)

/-! ## Part 4: Each Column Has Exactly One True Entry -/

/-- If M²=I, column j has at least one true entry. -/
theorem involution_col_nonempty {M : BoolMat n} (h_inv : IsInvolution M)
    (j : Fin n) : ∃ i : Fin n, M i j = true := by
  obtain ⟨k, hk⟩ := involution_row_nonempty h_inv j
  exact ⟨k, involution_entry_reflects h_inv hk⟩

/-- If M²=I, column j has at most one true entry. -/
theorem involution_col_unique {M : BoolMat n} (h_inv : IsInvolution M)
    (j : Fin n) {i₁ i₂ : Fin n} (h1 : M i₁ j = true) (h2 : M i₂ j = true) :
    i₁ = i₂ :=
  involution_row_unique h_inv j (involution_entry_reflects h_inv h1)
    (involution_entry_reflects h_inv h2)

/-! ## Part 5: Boolean Involution Is A Permutation Matrix -/

/-- **BOOLEAN INVOLUTION THEOREM**: Every boolean matrix M with M²=I
    is a permutation matrix. -/
theorem boolean_involution_is_permutation {M : BoolMat n}
    (h_inv : IsInvolution M) : IsPermutationMatrix M := by
  refine ⟨fun i => ?_, fun j => ?_⟩
  · obtain ⟨k, hk⟩ := involution_row_nonempty h_inv i
    exact ⟨k, hk, fun y hy => involution_row_unique h_inv i hy hk⟩
  · obtain ⟨i, hi⟩ := involution_col_nonempty h_inv j
    exact ⟨i, hi, fun y hy => involution_col_unique h_inv j hy hi⟩

/-! ## Part 6: Extract the Permutation Function -/

/-- From a boolean involution, extract the permutation function σ. -/
noncomputable def involutionPerm {M : BoolMat n} (h_inv : IsInvolution M) :
    Fin n → Fin n :=
  fun i => Classical.choose (involution_row_nonempty h_inv i)

/-- The extracted permutation satisfies M[i,σ(i)] = true. -/
theorem involutionPerm_spec {M : BoolMat n} (h_inv : IsInvolution M)
    (i : Fin n) : M i (involutionPerm h_inv i) = true :=
  Classical.choose_spec (involution_row_nonempty h_inv i)

/-- M[i,j] = true iff σ(i) = j. -/
theorem involutionPerm_iff {M : BoolMat n} (h_inv : IsInvolution M)
    (i j : Fin n) : M i j = true ↔ involutionPerm h_inv i = j :=
  ⟨fun h => involution_row_unique h_inv i (involutionPerm_spec h_inv i) h,
   fun h => h ▸ involutionPerm_spec h_inv i⟩

/-- M[i,j] = true implies σ(i) = j. -/
theorem involutionPerm_eq {M : BoolMat n} (h_inv : IsInvolution M)
    {i j : Fin n} (h : M i j = true) : involutionPerm h_inv i = j :=
  (involutionPerm_iff h_inv i j).mp h

/-- The extracted permutation is injective. -/
theorem involutionPerm_injective {M : BoolMat n} (h_inv : IsInvolution M) :
    Function.Injective (involutionPerm h_inv) := by
  intro a b h_eq
  have ha := involutionPerm_spec h_inv a
  have hb := involutionPerm_spec h_inv b
  rw [h_eq] at ha
  exact involution_col_unique h_inv _ ha hb

/-- The extracted permutation is surjective. -/
theorem involutionPerm_surjective {M : BoolMat n} (h_inv : IsInvolution M) :
    Function.Surjective (involutionPerm h_inv) := by
  intro j
  obtain ⟨i, hi⟩ := involution_col_nonempty h_inv j
  exact ⟨i, involutionPerm_eq h_inv hi⟩

/-! ## Part 7: The Permutation Is An Involution (σ² = id) -/

/-- The extracted permutation is an involution: σ(σ(i)) = i. -/
theorem involutionPerm_involutive {M : BoolMat n} (h_inv : IsInvolution M)
    (i : Fin n) : involutionPerm h_inv (involutionPerm h_inv i) = i := by
  have h1 := involutionPerm_spec h_inv i
  have h2 := involution_entry_reflects h_inv h1
  exact involutionPerm_eq h_inv h2

/-- M equals permMatrix σ where σ is the extracted permutation. -/
theorem involution_eq_permMatrix {M : BoolMat n} (h_inv : IsInvolution M) :
    M = permMatrix (involutionPerm h_inv) := by
  funext i j
  simp only [permMatrix]
  -- Goal: M i j = decide (involutionPerm h_inv i = j)
  cases h : M i j with
  | false =>
    -- Goal: false = decide (involutionPerm h_inv i = j)
    have h_ne : involutionPerm h_inv i ≠ j :=
      fun h_eq => absurd (h_eq ▸ involutionPerm_spec h_inv i) (by rw [h]; decide)
    exact (decide_eq_false_iff_not.mpr h_ne).symm
  | true =>
    -- Goal: true = decide (involutionPerm h_inv i = j)
    exact (decide_eq_true_eq.mpr (involutionPerm_eq h_inv h)).symm

/-! ## Part 8: Converse -/

/-- Converse: a permutation matrix from an involutive injection satisfies M²=I. -/
theorem permMatrix_of_involution_is_involution {σ : Fin n → Fin n}
    (h_inj : Function.Injective σ) (h_inv : ∀ i, σ (σ i) = i) :
    IsInvolution (permMatrix σ) :=
  permMatrix_involution h_inv h_inj

/-! ## Part 9: The Complete Characterization -/

/-- **BOOLEAN INVOLUTION CHARACTERIZATION**: M²=I in the boolean semiring
    iff M = permMatrix σ for some involutive injection σ. -/
theorem boolean_involution_iff_involutive_perm (M : BoolMat n) :
    IsInvolution M ↔
    ∃ σ : Fin n → Fin n, Function.Injective σ ∧
      (∀ i, σ (σ i) = i) ∧ M = permMatrix σ :=
  ⟨fun h_inv => ⟨involutionPerm h_inv,
                  involutionPerm_injective h_inv,
                  involutionPerm_involutive h_inv,
                  involution_eq_permMatrix h_inv⟩,
   fun ⟨_, h_inj, h_σ_inv, h_eq⟩ =>
     h_eq ▸ permMatrix_of_involution_is_involution h_inj h_σ_inv⟩

/-! ## Part 10: Small Cases -/

/-- At n=1, the only boolean involution is the identity. -/
theorem involution_n1_is_id (M : BoolMat 1) (h : IsInvolution M) :
    M = one := by
  have hperm := boolean_involution_is_permutation h
  funext ⟨i, hi⟩ ⟨j, hj⟩
  have : i = 0 := by omega
  have : j = 0 := by omega
  subst ‹i = 0›; subst ‹j = 0›
  obtain ⟨k, hk, _⟩ := hperm.1 ⟨0, by omega⟩
  have : k = ⟨0, by omega⟩ := by ext; omega
  rw [this] at hk; simp [one]; exact hk

/-- At n=2, boolean involutions are exactly {identity, anti-diagonal}. -/
theorem involution_n2_classification (M : BoolMat 2) (h : IsInvolution M) :
    M = one ∨ M = antiDiag2 := by
  by_cases h00 : M 0 0 = true
  · -- M[0,0]=true → identity
    left
    have h01 : M 0 1 = false := involution_row_exclusive h h00 1 (by decide)
    have h10 : M 1 0 = false := by
      cases hm : M 1 0 with
      | false => rfl
      | true => exact absurd (involution_col_unique h 0 hm h00) (by decide)
    have h11 : M 1 1 = true := by
      obtain ⟨k, hk⟩ := involution_row_nonempty h (1 : Fin 2)
      have hk_bound : k.val = 0 ∨ k.val = 1 := by omega
      rcases hk_bound with hv | hv
      · have hk0 : k = (0 : Fin 2) := by ext; exact hv
        rw [hk0] at hk; rw [h10] at hk; exact absurd hk (by decide)
      · have hk1 : k = (1 : Fin 2) := by ext; exact hv
        rw [hk1] at hk; exact hk
    funext ⟨i, hi⟩ ⟨j, hj⟩
    have : i = 0 ∨ i = 1 := by omega
    have : j = 0 ∨ j = 1 := by omega
    rcases ‹i = 0 ∨ i = 1› with rfl | rfl <;> rcases ‹j = 0 ∨ j = 1› with rfl | rfl <;>
      simp [one, h00, h01, h10, h11]
  · -- M[0,0]=false → M[0,1]=true → anti-diagonal
    right
    have h00f : M 0 0 = false := by
      cases hm : M 0 0 with | false => rfl | true => exact absurd hm h00
    have h01 : M 0 1 = true := by
      obtain ⟨k, hk⟩ := involution_row_nonempty h (0 : Fin 2)
      have hk_bound : k.val = 0 ∨ k.val = 1 := by omega
      rcases hk_bound with hv | hv
      · have hk0 : k = (0 : Fin 2) := by ext; exact hv
        rw [hk0] at hk; rw [h00f] at hk; exact absurd hk (by decide)
      · have hk1 : k = (1 : Fin 2) := by ext; exact hv
        rw [hk1] at hk; exact hk
    have h10 : M 1 0 = true := involution_entry_reflects h h01
    have h11 : M 1 1 = false := involution_row_exclusive h h01 1 (by decide)
    funext ⟨i, hi⟩ ⟨j, hj⟩
    have : i = 0 ∨ i = 1 := by omega
    have : j = 0 ∨ j = 1 := by omega
    rcases ‹i = 0 ∨ i = 1› with rfl | rfl <;> rcases ‹j = 0 ∨ j = 1› with rfl | rfl <;>
      simp [antiDiag2, h00f, h01, h10, h11]

/-! ## Part 11: Consequences for CubeGraph Transfer Operators -/

/-- A rank-1 boolean involution has only diagonal entries true.
    Proof: rank-1 means all nonzero rows have the same column pattern.
    An off-diagonal entry forces a self-loop, contradicting row uniqueness. -/
theorem rank1_involution_trivial {M : BoolMat n} (h_inv : IsInvolution M)
    (h_r1 : M.IsRankOne) : ∀ i j : Fin n, M i j = true ↔ i = j := by
  intro i j
  obtain ⟨R, C, _, _, hRC⟩ := h_r1
  constructor
  · intro h
    by_cases h_eq : i = j
    · exact h_eq
    · -- M[i,j]=true and M[j,i]=true (reflects), with i≠j
      have hji := involution_entry_reflects h_inv h
      have hRi : R i = true := ((hRC i j).mp h).1
      have hCi : C i = true := ((hRC j i).mp hji).2
      have hii : M i i = true := (hRC i i).mpr ⟨hRi, hCi⟩
      -- (M²)[i,j] has witness k=i: M[i,i]∧M[i,j] = true
      have h_sq : mul M M i j = true := (mul_apply_true M M i j).mpr ⟨i, hii, h⟩
      exact absurd h_sq (by rw [involution_off_diag h_inv h_eq]; decide)
  · intro h; subst h
    obtain ⟨k, hk⟩ := involution_row_nonempty h_inv i
    by_cases h_eq : k = i
    · exact h_eq ▸ hk
    · exfalso
      have hki := involution_entry_reflects h_inv hk
      have hRi := ((hRC i k).mp hk).1
      have hCi := ((hRC k i).mp hki).2
      have hii : M i i = true := (hRC i i).mpr ⟨hRi, hCi⟩
      exact h_eq (involution_row_unique h_inv i hk hii)

/-- The identity matrix is the ONLY rank-1 boolean involution. -/
theorem rank1_involution_is_identity {M : BoolMat n}
    (h_inv : IsInvolution M) (h_r1 : M.IsRankOne) :
    M = one := by
  funext i j
  simp only [one]
  by_cases h_eq : i = j
  · subst h_eq; simp; exact (rank1_involution_trivial h_inv h_r1 i i).mpr rfl
  · simp [h_eq]
    cases h : M i j with
    | false => rfl
    | true => exact absurd ((rank1_involution_trivial h_inv h_r1 i j).mp h) h_eq

/-! ## Part 12: Structural Consequences -/

/-- Non-fixed-points of a boolean involution come in pairs (transpositions). -/
theorem involution_support_bound {M : BoolMat n} (h_inv : IsInvolution M) :
    ∀ i : Fin n, involutionPerm h_inv i ≠ i →
    involutionPerm h_inv (involutionPerm h_inv i) = i :=
  fun i _ => involutionPerm_involutive h_inv i

/-- Fixed points: M[i,i]=true iff σ(i)=i. -/
theorem involution_fixed_point_iff {M : BoolMat n} (h_inv : IsInvolution M)
    (i : Fin n) : M i i = true ↔ involutionPerm h_inv i = i := by
  constructor
  · exact fun h => involutionPerm_eq h_inv h
  · intro h
    have := involutionPerm_spec h_inv i
    rw [h] at this
    exact this

/-- Decomposition into fixed points and transpositions. -/
theorem involution_transposition_structure {M : BoolMat n} (h_inv : IsInvolution M)
    {i : Fin n} (h_not_fixed : involutionPerm h_inv i ≠ i) :
    involutionPerm h_inv (involutionPerm h_inv i) = i ∧
    involutionPerm h_inv i ≠ i :=
  ⟨involutionPerm_involutive h_inv i, h_not_fixed⟩

/-- Trace = true iff σ has a fixed point. -/
theorem involution_trace_iff_fixed_point {M : BoolMat n} (h_inv : IsInvolution M) :
    M.trace = true ↔ ∃ i : Fin n, involutionPerm h_inv i = i := by
  rw [trace_true]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, (involution_fixed_point_iff h_inv i).mp hi⟩,
         fun ⟨i, hi⟩ => ⟨i, (involution_fixed_point_iff h_inv i).mpr hi⟩⟩

/-- An involution with trace = false is a fixed-point-free involution. -/
theorem involution_traceless_derangement {M : BoolMat n} (h_inv : IsInvolution M)
    (h_trace : M.trace = false) :
    ∀ i : Fin n, involutionPerm h_inv i ≠ i := by
  intro i h_fix
  have h_diag : M i i = true := (involution_fixed_point_iff h_inv i).mpr h_fix
  have h_trace_true : M.trace = true := (trace_true M).mpr ⟨i, h_diag⟩
  rw [h_trace] at h_trace_true
  exact absurd h_trace_true (by decide)

/-- Every 2-cycle in an involution: M[i,k]=true ∧ M[k,i]=true ∧ k≠i ∧ σ(k)=i. -/
theorem involution_two_cycle {M : BoolMat n} (h_inv : IsInvolution M)
    {i : Fin n} (h_nf : involutionPerm h_inv i ≠ i) :
    let k := involutionPerm h_inv i
    M i k = true ∧ M k i = true ∧ k ≠ i ∧ involutionPerm h_inv k = i :=
  ⟨involutionPerm_spec h_inv i,
   involution_entry_reflects h_inv (involutionPerm_spec h_inv i),
   h_nf,
   involutionPerm_involutive h_inv i⟩

end BoolMat
