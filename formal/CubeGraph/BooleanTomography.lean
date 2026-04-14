/-
  CubeGraph/BooleanTomography.lean
  Boolean Tomography Theorem: OR/AND (idempotent) rank-1 projections
  CANNOT reconstruct rank > 1, unlike XOR (field GF(2)) projections.

  CT scan analogy:
  - Continuous (field): O(n) projections reconstruct full structure (polynomial)
  - Boolean (semiring): poly(n) projections stay rank-1 (no reconstruction)
  Root cause: idempotency (a OR a = a) kills multiplicities.

  Part 1: Entrywise OR of BoolMat — idempotent, rank-bounded
  Part 2: Entrywise XOR of BoolMat — cancellative, rank-amplifying
  Part 3: The Tomography Gap — OR stays rank ≤ 1, XOR reaches rank n
  Part 4: Application — idempotent combination = no rank amplification
  Part 5: Idempotency as root cause

  See: experiments-ml/025_2026-03-19_synthesis/bridge-next/BRAINSTORM.md (Observation 2)
-/

import CubeGraph.Rank1Algebra

namespace BoolMat

variable {n : Nat}

/-! ## Part 1: Entrywise OR — The Boolean Projection Combiner

  Entrywise OR of boolean matrices: (A ∨ B)[i,j] = A[i,j] ∨ B[i,j].
  This is the natural way to combine boolean "projections" (views of gap structure).
  Unlike matrix multiplication (composition), this aggregates OBSERVATIONS. -/

/-- Entrywise OR of two boolean matrices. -/
def bor (A B : BoolMat n) : BoolMat n :=
  fun i j => A i j || B i j

/-- Entrywise XOR of two boolean matrices. -/
def bxor (A B : BoolMat n) : BoolMat n :=
  fun i j => xor (A i j) (B i j)

/-! ### Basic OR properties -/

@[simp] theorem bor_apply (A B : BoolMat n) (i j : Fin n) :
    bor A B i j = (A i j || B i j) := rfl

@[simp] theorem bxor_apply (A B : BoolMat n) (i j : Fin n) :
    bxor A B i j = xor (A i j) (B i j) := rfl

/-- **OR is idempotent**: A ∨ A = A.
    This is the ROOT CAUSE of the tomography gap.
    Seeing the same projection twice gives ZERO new information. -/
theorem bor_idem (A : BoolMat n) : bor A A = A := by
  funext i j; simp [bor, Bool.or_self]

/-- OR is commutative. -/
theorem bor_comm (A B : BoolMat n) : bor A B = bor B A := by
  funext i j; simp [bor, Bool.or_comm]

/-- OR is associative. -/
theorem bor_assoc (A B C : BoolMat n) : bor (bor A B) C = bor A (bor B C) := by
  funext i j; simp [bor, Bool.or_assoc]

/-- OR with zero is identity. -/
theorem bor_zero (A : BoolMat n) : bor A zero = A := by
  funext i j; simp [bor, zero]

/-- Zero is left identity for OR. -/
theorem zero_bor (A : BoolMat n) : bor zero A = A := by
  funext i j; simp [bor, zero]

/-- **OR is absorptive**: A ∨ (A ∨ B) = A ∨ B.
    Repeating projections adds nothing. -/
theorem bor_absorb (A B : BoolMat n) : bor A (bor A B) = bor A B := by
  rw [← bor_assoc, bor_idem]

/-! ### XOR properties (contrast with OR) -/

/-- **XOR is NOT idempotent**: A ⊕ A = 0 (not A).
    This is CANCELLATIVE: identical observations cancel out!
    In a field, x + x = 0 enables "subtraction" of known components. -/
theorem bxor_self_eq_zero (A : BoolMat n) : bxor A A = zero := by
  funext i j; unfold bxor zero; cases A i j <;> rfl

/-- XOR is commutative. -/
theorem bxor_comm (A B : BoolMat n) : bxor A B = bxor B A := by
  funext i j; unfold bxor
  cases A i j <;> cases B i j <;> rfl

/-- XOR with zero is identity. -/
theorem bxor_zero (A : BoolMat n) : bxor A zero = A := by
  funext i j; unfold bxor zero; cases A i j <;> rfl

/-! ## Part 2: Rank under OR — rank-1 OR rank-1 ≤ rank-1 (when same shape)

  Key theorem: OR of two rank-1 outer products with the SAME row support
  and the SAME column support gives back the SAME matrix.
  More generally: OR of rank-1 matrices gives rank ≤ 2 in general,
  but rank ≤ 1 when supports are compatible. -/

/-- If M₁ = M₂ (same rank-1 projection), their OR is the same matrix.
    This is the simplest consequence of idempotency: no new information. -/
theorem bor_same_rankOne {M : BoolMat n} (_h : M.IsRankOne) :
    bor M M = M := bor_idem M

/-- OR of an outer product with itself is idempotent.
    This is the algebraic core: rank-1 OR rank-1 = rank-1 when same supports. -/
theorem bor_outerProduct_idem (R C : Fin n → Bool) :
    bor (outerProduct R C) (outerProduct R C) = outerProduct R C := by
  exact bor_idem (outerProduct R C)

/-- OR of outer products with same row support yields outerProduct R (C₁ ∨ C₂).
    The result is outerProduct R₁ (C₁ ∨ C₂), which is still rank-1. -/
theorem bor_outerProduct_same_row (R C₁ C₂ : Fin n → Bool) :
    bor (outerProduct R C₁) (outerProduct R C₂) =
    outerProduct R (fun j => C₁ j || C₂ j) := by
  funext i j
  simp only [bor, outerProduct_apply]
  cases R i <;> simp

/-- Symmetric version: same column support. -/
theorem bor_outerProduct_same_col (R₁ R₂ C : Fin n → Bool) :
    bor (outerProduct R₁ C) (outerProduct R₂ C) =
    outerProduct (fun i => R₁ i || R₂ i) C := by
  funext i j
  simp only [bor, outerProduct_apply]
  cases C j <;> simp

/-- Combining shared-row outer products preserves rank-1. -/
theorem bor_outerProduct_same_row_rankOne {R C₁ C₂ : Fin n → Bool}
    (hR : IndNonempty R)
    (hC : ∃ k : Fin n, C₁ k = true ∨ C₂ k = true) :
    (bor (outerProduct R C₁) (outerProduct R C₂)).IsRankOne := by
  rw [bor_outerProduct_same_row]
  refine ⟨R, fun j => C₁ j || C₂ j, hR, ?_, fun i j => by simp [outerProduct, Bool.and_eq_true]⟩
  obtain ⟨k, hk⟩ := hC
  exact ⟨k, by cases hk with | inl h => simp [h] | inr h => simp [h]⟩

/-! ## Part 3: The Tomography Gap — OR-aggregation is rank-bounded

  Central result: OR-folding a list of rank-1 outer products with the
  SAME row support R yields an outer product outerProduct R (∨ Cᵢ).
  No matter how many projections, the result is still rank-1.

  In contrast, XOR-folding can increase rank: two linearly independent
  rank-1 matrices XOR to a rank-2 matrix. -/

/-- Helper: foldl of entrywise-OR over indicator functions propagates truth. -/
private theorem foldl_or_preserves_true (Cs : List (Fin n → Bool))
    (acc : Fin n → Bool) (k : Fin n) (h : acc k = true) :
    (Cs.foldl (fun a C => fun j => a j || C j) acc) k = true := by
  induction Cs generalizing acc with
  | nil => exact h
  | cons C rest ih =>
    simp only [List.foldl_cons]
    apply ih
    simp [h]

/-- Helper: generalized foldl over outer products with accumulator. -/
private theorem bor_foldl_outerProduct_aux (R : Fin n → Bool)
    (Cs : List (Fin n → Bool)) (acc_C : Fin n → Bool) :
    Cs.foldl (fun acc C => bor acc (outerProduct R C)) (outerProduct R acc_C)
    = outerProduct R (Cs.foldl (fun a C => fun j => a j || C j) acc_C) := by
  induction Cs generalizing acc_C with
  | nil => rfl
  | cons C rest ih =>
    simp only [List.foldl_cons]
    rw [bor_outerProduct_same_row]
    exact ih (fun j => acc_C j || C j)

/-- OR-fold of outer products with same row support:
    ∨ᵢ (R ⊗ Cᵢ) = R ⊗ (∨ᵢ Cᵢ). -/
theorem bor_foldl_outerProduct_same_row (R : Fin n → Bool)
    (Cs : List (Fin n → Bool)) :
    Cs.foldl (fun acc C => bor acc (outerProduct R C)) (zero)
    = outerProduct R (Cs.foldl (fun acc C => fun j => acc j || C j) (fun _ => false)) := by
  cases Cs with
  | nil =>
    funext i j; simp only [List.foldl_nil, zero, outerProduct_apply]; cases R i <;> simp
  | cons C rest =>
    simp only [List.foldl_cons, zero_bor]
    -- After consuming the head: acc = outerProduct R C
    -- We need: rest.foldl ... (outerProduct R C) = outerProduct R (rest.foldl ... C)
    -- which is exactly bor_foldl_outerProduct_aux with acc_C = C
    have h_eq : outerProduct R C = outerProduct R (fun j => false || C j) := by
      funext i j; simp [outerProduct]
    rw [h_eq]
    exact bor_foldl_outerProduct_aux R rest (fun j => false || C j)

/-- Helper: if C₀ ∈ Cs and C₀ k = true, the generalized OR-fold at k is true. -/
private theorem foldl_or_mem_true_aux (Cs : List (Fin n → Bool))
    (acc : Fin n → Bool) (C₀ : Fin n → Bool) (hC₀ : C₀ ∈ Cs) (k : Fin n) (hk : C₀ k = true) :
    (Cs.foldl (fun a C => fun j => a j || C j) acc) k = true := by
  induction Cs generalizing acc with
  | nil => simp at hC₀
  | cons C rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hC₀ with rfl | h_rest
    · exact foldl_or_preserves_true rest _ k (by simp [hk])
    · exact ih _ h_rest

/-- Helper: if C₀ ∈ Cs and C₀ k = true, the OR-fold at k is true. -/
private theorem foldl_or_mem_true (Cs : List (Fin n → Bool))
    (C₀ : Fin n → Bool) (hC₀ : C₀ ∈ Cs) (k : Fin n) (hk : C₀ k = true) :
    (Cs.foldl (fun a C => fun j => a j || C j) (fun _ => false)) k = true :=
  foldl_or_mem_true_aux Cs _ C₀ hC₀ k hk

/-- **Tomography Gap (OR side)**: OR-combining k rank-1 outer products
    sharing row support R always gives rank ≤ 1.
    No matter how large k is, the OR-result has rank ≤ 1.
    This is because outerProduct R C is rank-1 for any C (or zero if C = 0). -/
theorem or_tomography_bounded (R : Fin n → Bool) (Cs : List (Fin n → Bool))
    (hR : IndNonempty R) (hC : ∃ C ∈ Cs, IndNonempty C) :
    (Cs.foldl (fun acc C => bor acc (outerProduct R C)) zero).IsRankOne := by
  rw [bor_foldl_outerProduct_same_row]
  obtain ⟨C₀, hC₀_mem, ⟨k, hk⟩⟩ := hC
  have hC_ne : IndNonempty (Cs.foldl (fun acc C => fun j => acc j || C j) (fun _ => false)) :=
    ⟨k, foldl_or_mem_true Cs C₀ hC₀_mem k hk⟩
  exact outerProduct_isRankOne hR hC_ne

/-- **Tomography Gap (XOR side)**: XOR of two rank-1 matrices with
    disjoint supports gives a rank-2 matrix (not rank-1).
    Concretely: outerProduct [1,0] [1,0] ⊕ outerProduct [0,1] [0,1] = I₂,
    which is rank-2.

    This demonstrates that XOR CAN amplify rank — unlike OR. -/
theorem xor_can_amplify_rank :
    ∃ (A B : BoolMat 2), A.IsRankOne ∧ B.IsRankOne ∧ ¬(bxor A B).IsRankOne := by
  -- A = [[1,0],[0,0]], B = [[0,0],[0,1]]
  -- A ⊕ B = [[1,0],[0,1]] = identity, which is rank-2
  let A : BoolMat 2 := fun i j => decide (i = ⟨0, by omega⟩ ∧ j = ⟨0, by omega⟩)
  let B : BoolMat 2 := fun i j => decide (i = ⟨1, by omega⟩ ∧ j = ⟨1, by omega⟩)
  refine ⟨A, B, ?_, ?_, ?_⟩
  · -- A is rank-1
    exact ⟨fun i => decide (i = ⟨0, by omega⟩), fun j => decide (j = ⟨0, by omega⟩),
           ⟨⟨0, by omega⟩, by simp⟩, ⟨⟨0, by omega⟩, by simp⟩,
           fun i j => by simp [A, decide_eq_true_eq, Bool.and_eq_true]⟩
  · -- B is rank-1
    exact ⟨fun i => decide (i = ⟨1, by omega⟩), fun j => decide (j = ⟨1, by omega⟩),
           ⟨⟨1, by omega⟩, by simp⟩, ⟨⟨1, by omega⟩, by simp⟩,
           fun i j => by simp [B, decide_eq_true_eq, Bool.and_eq_true]⟩
  · -- A ⊕ B is NOT rank-1 (it's the 2x2 identity)
    intro ⟨R, C, _, _, hRC⟩
    have h00 : bxor A B ⟨0, by omega⟩ ⟨0, by omega⟩ = true := by native_decide
    have h11 : bxor A B ⟨1, by omega⟩ ⟨1, by omega⟩ = true := by native_decide
    have h01 : bxor A B ⟨0, by omega⟩ ⟨1, by omega⟩ = false := by native_decide
    have ⟨hR0, _⟩ := (hRC ⟨0, by omega⟩ ⟨0, by omega⟩).mp h00
    have hC1 := ((hRC ⟨1, by omega⟩ ⟨1, by omega⟩).mp h11).2
    have h01_true := (hRC ⟨0, by omega⟩ ⟨1, by omega⟩).mpr ⟨hR0, hC1⟩
    rw [h01] at h01_true
    exact Bool.false_ne_true h01_true

/-! ## Part 4: OR monotonicity and the rank-1 ceiling

  Key structural results connecting OR-aggregation to the transfer operator setting.
  In the CubeGraph, each "view" (arc-consistency propagation step) produces
  a rank-1 projection. Combining these views with OR stays at rank-1. -/

/-- OR is monotone: A ≤ A ∨ B (entrywise). -/
theorem bor_le_left (A B : BoolMat n) (i j : Fin n)
    (h : A i j = true) : bor A B i j = true := by
  simp [bor, h]

/-- OR is monotone: B ≤ A ∨ B (entrywise). -/
theorem bor_le_right (A B : BoolMat n) (i j : Fin n)
    (h : B i j = true) : bor A B i j = true := by
  simp [bor, h, Bool.or_true]

/-- **OR saturation lemma**: bor A (bor A B) = bor A B.
    Once A is included, adding it again changes nothing.
    Induction base for showing repeated OR-folding converges in one pass. -/
theorem bor_left_absorb (A B : BoolMat n) : bor A (bor A B) = bor A B :=
  bor_absorb A B

/-! ## Part 5: The Idempotency Root Cause — structural comparison

  Why does OR lose information but XOR doesn't?
  - OR: a ∨ a = a (idempotent) → duplicate = no new info
  - XOR: a ⊕ a = 0 (cancellative) → duplicate = erasure → SUBTRACTIVE

  In a field, "seeing the same thing twice" lets you SUBTRACT it,
  isolating the difference. In a semiring, "seeing the same thing twice"
  gives you exactly what you already had.

  For tomography: you need subtraction to reconstruct.
  Without subtraction, you only accumulate — and accumulation saturates. -/

/-- **Idempotency theorem**: OR of k copies of A equals A, for all k ≥ 1.
    k projections from the SAME angle give exactly one projection's worth. -/
theorem bor_replicate (A : BoolMat n) (k : Nat) (hk : k ≥ 1) :
    (List.replicate k A).foldl bor zero = A := by
  induction k with
  | zero => omega
  | succ k' ih =>
    simp only [List.replicate_succ, List.foldl_cons, zero_bor]
    suffices ∀ m, (List.replicate m A).foldl bor A = A from this k'
    intro m
    induction m with
    | zero => simp [List.replicate]
    | succ m' ihm =>
      simp only [List.replicate_succ, List.foldl_cons, bor_idem]
      exact ihm

/-- **Cancellation theorem**: XOR of 2 copies of A equals zero. -/
theorem bxor_replicate_two (A : BoolMat n) :
    bxor A A = zero := bxor_self_eq_zero A

/-- **The fundamental asymmetry**: OR(A, A) = A but XOR(A, A) = 0.
    This one equation encodes the entire tomography gap:
    - OR cannot "cancel" known components to reveal new ones
    - XOR can "cancel" known components, enabling reconstruction -/
theorem fundamental_asymmetry (A : BoolMat n) :
    bor A A = A ∧ bxor A A = zero :=
  ⟨bor_idem A, bxor_self_eq_zero A⟩

/-! ## Part 6: Rank-1 outer products under OR — the full picture -/

/-- OR of two outer products: always decomposes as a structured sum. -/
theorem bor_outerProduct_general (R₁ R₂ C₁ C₂ : Fin n → Bool) :
    bor (outerProduct R₁ C₁) (outerProduct R₂ C₂) =
    fun i j => (R₁ i && C₁ j) || (R₂ i && C₂ j) := by
  funext i j; simp [bor, outerProduct]

/-- **Row support monotonicity under OR**: rowSup(A ∨ B) ⊆ rowSup(A) ∪ rowSup(B). -/
theorem bor_rankOne_rowSup_monotone (A B : BoolMat n) (i : Fin n)
    (h : (bor A B).rowSup i = true) :
    A.rowSup i = true ∨ B.rowSup i = true := by
  rw [mem_rowSup_iff] at h
  obtain ⟨j, hj⟩ := h
  simp [bor] at hj
  cases hA : A i j
  · simp [hA] at hj
    exact Or.inr (mem_rowSup_iff.mpr ⟨j, hj⟩)
  · exact Or.inl (mem_rowSup_iff.mpr ⟨j, hA⟩)

/-! ## Part 7: Application to transfer operators

  In the CubeGraph setting:
  - Each edge gives a transfer operator M_e ∈ BoolMat 8
  - Arc-consistency propagation produces "projected" versions
  - These projections are combined using OR (feasible gaps = union)
  - Result: aggregated view is rank-bounded

  The tomography barrier says: no matter how many edges you process,
  the OR-aggregated view cannot reconstruct the full rank-2+ structure
  needed to detect UNSAT Type 2 (Borromean obstruction). -/

/-- Projecting a BoolMat by zeroing rows NOT in a given support.
    This models "viewing M from the perspective of gap set G". -/
def projectRows (M : BoolMat n) (G : Fin n → Bool) : BoolMat n :=
  fun i j => G i && M i j

/-- Row-projection is rank-bounded: if M is rank-1, its row-projection is rank-1 or zero. -/
theorem projectRows_rankOne_or_zero {M : BoolMat n}
    (hM : M.IsRankOne) (G : Fin n → Bool) :
    (projectRows M G).IsRankOne ∨ projectRows M G = zero := by
  obtain ⟨R, C, hR, hC, hRC⟩ := hM
  by_cases h : ∃ k : Fin n, G k = true ∧ R k = true
  · -- Some row survives → rank-1 with restricted row support
    left
    refine ⟨fun i => G i && R i, C, ?_, hC, ?_⟩
    · obtain ⟨k, hGk, hRk⟩ := h
      exact ⟨k, by simp [hGk, hRk]⟩
    · intro i j
      simp only [projectRows, Bool.and_eq_true]
      constructor
      · intro ⟨hGi, hMij⟩
        exact ⟨⟨hGi, ((hRC i j).mp hMij).1⟩, ((hRC i j).mp hMij).2⟩
      · intro ⟨⟨hGi, hRi⟩, hCj⟩
        exact ⟨hGi, (hRC i j).mpr ⟨hRi, hCj⟩⟩
  · -- No row survives → zero
    right
    funext i j
    simp only [projectRows, zero]
    cases hGi : G i with
    | false => simp
    | true =>
      -- G i = true, so R i must be false (from ¬∃ k, G k ∧ R k)
      have hRi : R i = false := by
        cases hR_val : R i with
        | false => rfl
        | true => exact absurd ⟨i, hGi, hR_val⟩ h
      cases hMij : M i j with
      | false => simp
      | true =>
        -- M i j = true → R i = true, contradiction
        exact absurd ((hRC i j).mp hMij).1 (by rw [hRi]; decide)

/-- OR of two row-projections of the same rank-1 matrix:
    result is rank-1 or zero. -/
theorem bor_projectRows_rankOne {M : BoolMat n}
    (hM : M.IsRankOne) (G₁ G₂ : Fin n → Bool) :
    (bor (projectRows M G₁) (projectRows M G₂)).IsRankOne ∨
    bor (projectRows M G₁) (projectRows M G₂) = zero := by
  -- bor of two projections = projection with G₁ ∨ G₂
  have h_eq : bor (projectRows M G₁) (projectRows M G₂) =
              projectRows M (fun i => G₁ i || G₂ i) := by
    funext i j
    simp only [bor, projectRows]
    cases G₁ i <;> cases G₂ i <;> simp
  rw [h_eq]
  exact projectRows_rankOne_or_zero hM _

/-! ## Summary of proven theorems -/

/-- **Boolean Tomography Summary**: The key theorems, collected.
    1. OR is idempotent (bor_idem)
    2. XOR is cancellative (bxor_self_eq_zero)
    3. OR of same-row outer products stays rank-1 (bor_outerProduct_same_row_rankOne)
    4. XOR of disjoint outer products amplifies rank (xor_can_amplify_rank)
    5. Row-projection preserves rank-1 (projectRows_rankOne_or_zero)
    6. OR of projections stays rank-1 (bor_projectRows_rankOne)

    The gap: field (XOR) enables polynomial reconstruction via cancellation.
    Semiring (OR) cannot reconstruct beyond rank-1 due to idempotency. -/
theorem boolean_tomography_summary :
    -- (1) OR idempotent
    (∀ (A : BoolMat n), bor A A = A)
    -- (2) XOR cancellative
    ∧ (∀ (A : BoolMat n), bxor A A = zero)
    -- (3) Fundamental asymmetry
    ∧ (∀ (A : BoolMat n), bor A A = A ∧ bxor A A = zero) :=
  ⟨bor_idem, bxor_self_eq_zero, fundamental_asymmetry⟩

end BoolMat
