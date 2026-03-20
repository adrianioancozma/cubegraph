/-
  CubeGraph/RankMonotonicity.lean
  T5: Rank Left-Monotonicity Generalized

  Extends RowRank.lean with:
  1. foldl composition: rank of composed chain ≤ rank of first factor
  2. Concrete cycle rotation bounds (3-element cycles)
  3. Rank-1 absorbing: if any factor is rank ≤ 1, some rotation has rank ≤ 1
  4. Chain monotonicity: adding factors can only decrease rank
  5. Rank-0 propagation: zero is absorbing

  Base lemma (already proven in RowRank.lean):
    rowRank_mul_le : rowRank(A · B) ≤ rowRank(A)

  Key NON-theorem (FALSE over 𝔹):
    rowRank(A · B) ≤ min(rowRank A, rowRank B)  -- 5508 counterexamples
    rowRank(A · B) ≤ rowRank(B)  -- counterexample in RowRank.lean:13-15

  See: RowRank.lean (base: rowRank_mul_le, rowSup_mul_of_rowSup)
  See: BandSemigroup.lean (rank1_idempotent, rank1_aperiodic)
  See: FlatBundleFailure.lean (T4: monodromy rank ≥ 2, consistent with cycle rotation bound)
  See: experiments-ml/021_.../T1-RESULTS.md (rank-1 absorbing: λ ≈ 0.87/step, 0% rank-0)
  See: experiments-ml/021_.../T5-PLAN.md (plan)
  See: experiments-ml/021_.../MICRO-MACRO-BRIDGE.md (rank monotonicity = funnel = lossy bridge)
-/

import CubeGraph.RowRank

namespace BoolMat

variable {n : Nat}

/-! ## Section 1: Foldl Composition -/

/-- Row rank of a left-fold: composing a list of matrices onto A
    cannot increase row rank beyond A's. -/
theorem rowRank_foldl_le (A : BoolMat n) (ms : List (BoolMat n)) :
    rowRank (ms.foldl mul A) ≤ rowRank A := by
  induction ms generalizing A with
  | nil => simp [List.foldl]
  | cons M rest ih =>
    simp only [List.foldl]
    calc rowRank (rest.foldl mul (mul A M))
        ≤ rowRank (mul A M) := ih (mul A M)
      _ ≤ rowRank A := rowRank_mul_le A M

/-- Row rank of foldl starting from identity: bounded by rank of first matrix. -/
theorem rowRank_foldl_one_le (M : BoolMat n) (rest : List (BoolMat n)) :
    rowRank ((M :: rest).foldl mul (one : BoolMat n)) ≤ rowRank M := by
  simp only [List.foldl]
  calc rowRank (rest.foldl mul (mul one M))
      = rowRank (rest.foldl mul M) := by rw [one_mul]
    _ ≤ rowRank M := rowRank_foldl_le M rest

/-! ## Section 2: Chain Monotonicity -/

/-- Adding more factors to a chain can only decrease rank. -/
theorem rowRank_foldl_prefix_ge (A : BoolMat n) (ms₁ ms₂ : List (BoolMat n)) :
    rowRank ((ms₁ ++ ms₂).foldl mul A) ≤ rowRank (ms₁.foldl mul A) := by
  rw [List.foldl_append]
  exact rowRank_foldl_le (ms₁.foldl mul A) ms₂

/-- Appending one more factor can only decrease rank. -/
theorem rowRank_snoc_le (A : BoolMat n) (ms : List (BoolMat n)) (M : BoolMat n) :
    rowRank ((ms ++ [M]).foldl mul A) ≤ rowRank (ms.foldl mul A) :=
  rowRank_foldl_prefix_ge A ms [M]

/-! ## Section 3: Cycle Rotation Bounds (concrete) -/

/-- Each rotation of a 3-cycle is bounded by the first element of that rotation. -/
theorem rowRank_cycle3_rotate (A B C : BoolMat n) :
    rowRank (mul (mul A B) C) ≤ rowRank A ∧
    rowRank (mul (mul B C) A) ≤ rowRank B ∧
    rowRank (mul (mul C A) B) ≤ rowRank C :=
  ⟨rowRank_mul_mul_le A B C,
   rowRank_mul_mul_le B C A,
   rowRank_mul_mul_le C A B⟩

/-- Each rotation of a 4-cycle is bounded by the first element. -/
theorem rowRank_cycle4_rotate (A B C D : BoolMat n) :
    rowRank (mul (mul (mul A B) C) D) ≤ rowRank A ∧
    rowRank (mul (mul (mul B C) D) A) ≤ rowRank B ∧
    rowRank (mul (mul (mul C D) A) B) ≤ rowRank C ∧
    rowRank (mul (mul (mul D A) B) C) ≤ rowRank D :=
  ⟨Nat.le_trans (rowRank_mul_le _ D) (rowRank_mul_mul_le A B C),
   Nat.le_trans (rowRank_mul_le _ A) (rowRank_mul_mul_le B C D),
   Nat.le_trans (rowRank_mul_le _ B) (rowRank_mul_mul_le C D A),
   Nat.le_trans (rowRank_mul_le _ C) (rowRank_mul_mul_le D A B)⟩

/-! ## Section 4: Rank-1 Absorbing -/

/-- If A has rowRank ≤ 1, then A·B has rowRank ≤ 1. -/
theorem rowRank_mul_le_one (A B : BoolMat n) (h : rowRank A ≤ 1) :
    rowRank (mul A B) ≤ 1 :=
  Nat.le_trans (rowRank_mul_le A B) h

/-- Rank ≤ 1 is absorbing under composition: once rank drops to ≤ 1,
    it stays ≤ 1 forever. This formalizes the T1 empirical observation
    that boolean rank converges to 1 and never returns to 2+. -/
theorem rowRank_foldl_le_one (A : BoolMat n) (ms : List (BoolMat n))
    (h : rowRank A ≤ 1) :
    rowRank (ms.foldl mul A) ≤ 1 :=
  Nat.le_trans (rowRank_foldl_le A ms) h

/-- In a 3-cycle, if any factor has rank ≤ 1, some rotation has rank ≤ 1.
    This is the cycle version of "rank-1 is absorbing." -/
theorem rowRank_cycle3_absorbing (A B C : BoolMat n)
    (h : rowRank A ≤ 1 ∨ rowRank B ≤ 1 ∨ rowRank C ≤ 1) :
    rowRank (mul (mul A B) C) ≤ 1 ∨
    rowRank (mul (mul B C) A) ≤ 1 ∨
    rowRank (mul (mul C A) B) ≤ 1 := by
  rcases h with hA | hB | hC
  · exact .inl (Nat.le_trans (rowRank_mul_mul_le A B C) hA)
  · exact .inr (.inl (Nat.le_trans (rowRank_mul_mul_le B C A) hB))
  · exact .inr (.inr (Nat.le_trans (rowRank_mul_mul_le C A B) hC))

/-- Generalized: if any matrix in a list has rank ≤ k,
    then composing from that point has rank ≤ k. -/
theorem rowRank_foldl_le_of_head_le (A : BoolMat n) (ms : List (BoolMat n))
    (k : Nat) (h : rowRank A ≤ k) :
    rowRank (ms.foldl mul A) ≤ k :=
  Nat.le_trans (rowRank_foldl_le A ms) h

/-! ## Section 5: Rank-0 Propagation -/

/-- Rank 0 (zero matrix) is absorbing: zero · anything = zero. -/
theorem rowRank_foldl_zero (ms : List (BoolMat n)) :
    rowRank (ms.foldl mul (zero : BoolMat n)) = 0 := by
  induction ms with
  | nil => simp [List.foldl]; exact rowRank_zero
  | cons M rest ih =>
    simp only [List.foldl, zero_mul]
    exact ih

/-- If any prefix product hits rank 0, the full product is rank 0. -/
theorem rowRank_zero_of_prefix_zero (A : BoolMat n) (ms₁ ms₂ : List (BoolMat n))
    (h : rowRank (ms₁.foldl mul A) = 0) :
    rowRank ((ms₁ ++ ms₂).foldl mul A) = 0 := by
  rw [List.foldl_append]
  have hle := rowRank_foldl_le (ms₁.foldl mul A) ms₂
  omega

/-! ## Section 6: Rank Hierarchy Summary -/

/-- Rank 0 ≤ rank 1 ≤ rank 2 ... and each level is absorbing from the left.
    Once you enter level k, you never leave (under left-multiplication).
    This is the "funnel" property of boolean matrix composition. -/
theorem rowRank_funnel (A : BoolMat n) (B : BoolMat n) (k : Nat)
    (h : rowRank A ≤ k) : rowRank (mul A B) ≤ k :=
  Nat.le_trans (rowRank_mul_le A B) h

end BoolMat
