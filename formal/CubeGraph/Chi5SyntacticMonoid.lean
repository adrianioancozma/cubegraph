/-
  CubeGraph/Chi5SyntacticMonoid.lean
  The SYNTACTIC MONOID of the trace language over the boolean matrix monoid.

  KEY IDEA (from CLAUDE-OWN-IDEAS.md, Idea 2):
  Individual transfer operators are APERIODIC (M³ = M², KR = 0).
  But the LANGUAGE L = {w ∈ (BoolMat n)* : trace(product(w)) = true}
  might have a NON-APERIODIC syntactic monoid — meaning the language
  requires GROUP computation even though each individual element is simple.

  See: BandSemigroup.lean (rank1_aperiodic — M³ = M²)
  See: BarringtonConnection.lean (Barrington — AC⁰ connection)
  See: BorromeanAC0.lean (AC⁰ lower bound via Braverman)
  See: Z3Composition.lean (h2Graph monodromy has trace = false)
-/

import CubeGraph.BandSemigroup

namespace BoolMat

variable {n : Nat}

/-! ## Part 1: Words and Products -/

/-- The product of a word (list of boolean matrices) via left-fold. -/
def wordProduct (w : List (BoolMat n)) : BoolMat n :=
  w.foldl mul one

/-- Empty word product is the identity. -/
theorem wordProduct_nil : wordProduct ([] : List (BoolMat n)) = one := rfl

/-- Singleton word product is the matrix itself. -/
theorem wordProduct_singleton (M : BoolMat n) : wordProduct [M] = M := by
  simp [wordProduct, one_mul]

/-- Helper: foldl mul acc = acc * foldl mul one. -/
private theorem foldl_mul_eq (ys : List (BoolMat n)) (acc : BoolMat n) :
    ys.foldl mul acc = mul acc (ys.foldl mul one) := by
  induction ys generalizing acc with
  | nil => simp [mul_one]
  | cons y rest ih =>
    simp only [List.foldl_cons]
    rw [ih (mul acc y), ih (mul one y), one_mul, mul_assoc]

/-- Product of concatenation = product of products. -/
theorem wordProduct_append (x y : List (BoolMat n)) :
    wordProduct (x ++ y) = mul (wordProduct x) (wordProduct y) := by
  simp only [wordProduct, List.foldl_append]
  exact foldl_mul_eq y (x.foldl mul one)

/-- The trace language: a word is in L iff its product has trace = true. -/
def inTraceLanguage (w : List (BoolMat n)) : Prop :=
  trace (wordProduct w) = true

/-- The trace language is decidable. -/
instance : DecidablePred (inTraceLanguage (n := n)) :=
  fun w => inferInstanceAs (Decidable (trace (wordProduct w) = true))

/-- Empty word is in the trace language (for n >= 1). -/
theorem nil_in_traceLanguage (h : n >= 1) : inTraceLanguage ([] : List (BoolMat n)) := by
  simp only [inTraceLanguage, wordProduct_nil, trace_true]
  exact ⟨⟨0, h⟩, by simp [one]⟩

/-! ## Part 2: The Syntactic Congruence -/

/-- Syntactic equivalence: u ~_L v iff for all contexts x, y,
    xuy in L iff xvy in L. -/
def SyntacticEquiv (u v : List (BoolMat n)) : Prop :=
  ∀ (x y : List (BoolMat n)),
    inTraceLanguage (x ++ u ++ y) ↔ inTraceLanguage (x ++ v ++ y)

/-- Syntactic equivalence is reflexive. -/
theorem syntacticEquiv_refl (u : List (BoolMat n)) : SyntacticEquiv u u :=
  fun _ _ => Iff.rfl

/-- Syntactic equivalence is symmetric. -/
theorem syntacticEquiv_symm {u v : List (BoolMat n)} (h : SyntacticEquiv u v) :
    SyntacticEquiv v u :=
  fun x y => (h x y).symm

/-- Syntactic equivalence is transitive. -/
theorem syntacticEquiv_trans {u v w : List (BoolMat n)}
    (h1 : SyntacticEquiv u v) (h2 : SyntacticEquiv v w) :
    SyntacticEquiv u w :=
  fun x y => Iff.trans (h1 x y) (h2 x y)

/-- Two words with the same product are syntactically equivalent. -/
theorem same_product_syntacticEquiv {u v : List (BoolMat n)}
    (h : wordProduct u = wordProduct v) : SyntacticEquiv u v := by
  intro x y
  simp only [inTraceLanguage, wordProduct_append, h]

/-- Context characterization: if all matrix contexts agree, words are equivalent. -/
theorem syntacticEquiv_of_matrix_contexts {u v : List (BoolMat n)}
    (h : ∀ (A B : BoolMat n), trace (mul (mul A (wordProduct u)) B) =
                               trace (mul (mul A (wordProduct v)) B)) :
    SyntacticEquiv u v := by
  intro x y
  simp only [inTraceLanguage, wordProduct_append]
  constructor
  · intro h_tr
    have heq := h (wordProduct x) (wordProduct y)
    rw [heq] at h_tr; exact h_tr
  · intro h_tr
    have heq := h (wordProduct x) (wordProduct y)
    rw [← heq] at h_tr; exact h_tr

/-! ## Part 3: Aperiodicity Definitions -/

/-- Repeat a word k times. -/
def wordPow (w : List (BoolMat n)) : Nat → List (BoolMat n)
  | 0 => []
  | k + 1 => w ++ wordPow w k

/-- Product of repeated word = matrix power. -/
theorem wordProduct_pow (w : List (BoolMat n)) (k : Nat) :
    wordProduct (wordPow w k) = BoolMat.pow (wordProduct w) k := by
  induction k with
  | zero => simp [wordPow, wordProduct_nil, BoolMat.pow]
  | succ k ih => simp only [wordPow, BoolMat.pow]; rw [wordProduct_append, ih]

/-- A word is syntactically aperiodic if w^{k+1} ~_L w^k for some k. -/
def SyntacticallyAperiodic (w : List (BoolMat n)) : Prop :=
  ∃ k : Nat, SyntacticEquiv (wordPow w (k + 1)) (wordPow w k)

/-- The trace language is aperiodic if every word is syntactically aperiodic. -/
def TraceLanguageAperiodic : Prop :=
  ∀ (w : List (BoolMat n)), SyntacticallyAperiodic w

/-- Rank-1 words ARE syntactically aperiodic (from rank1_aperiodic: M³ = M²). -/
theorem rank1_syntactically_aperiodic {M : BoolMat n} (h : M.IsRankOne) :
    SyntacticallyAperiodic [M] := by
  refine ⟨2, same_product_syntacticEquiv ?_⟩
  rw [wordProduct_pow, wordProduct_pow, wordProduct_singleton]
  simp only [BoolMat.pow, mul_one]
  exact rank1_aperiodic h

/-! ## Part 4: Zero Matrix Absorber -/

/-- Zero product words are all syntactically equivalent. -/
theorem zero_product_equiv {u v : List (BoolMat n)}
    (hu : wordProduct u = zero) (hv : wordProduct v = zero) :
    SyntacticEquiv u v := by
  intro x y; simp only [inTraceLanguage, wordProduct_append, hu, hv]

/-- A zero-product word is NOT in the trace language. -/
theorem zero_product_not_in_language {w : List (BoolMat n)}
    (h : wordProduct w = zero) : ¬ inTraceLanguage w := by
  simp only [inTraceLanguage, h, trace_zero]; exact Bool.false_ne_true

/-! ## Part 5: Syntactic Non-Triviality -/

/-- A traceless matrix is in a different syntactic class than identity. -/
theorem traceless_not_equiv_id {M : BoolMat n}
    (h_trace : trace M = false) (h_n : n >= 1) :
    ¬ SyntacticEquiv [M] [] := by
  intro h_eq
  have h_ctx := h_eq [] []
  simp only [inTraceLanguage, List.nil_append, List.append_nil,
             wordProduct_singleton, wordProduct_nil] at h_ctx
  have h_one : trace (one : BoolMat n) = true :=
    (trace_true _).mpr ⟨⟨0, h_n⟩, by simp [one]⟩
  exact Bool.false_ne_true (h_trace ▸ h_ctx.mpr h_one)

/-- A nonzero matrix is in a different syntactic class than zero. -/
theorem nonzero_not_equiv_zero {M : BoolMat n}
    (h_nonzero : ¬ isZero M) :
    ¬ SyntacticEquiv [M] [zero] := by
  intro h_eq
  apply h_nonzero
  intro i j
  cases hij : M i j with
  | false => rfl
  | true =>
    exfalso
    let A : BoolMat n := fun _ c => decide (c = i)
    let B : BoolMat n := fun r c => decide (r = j ∧ c = i)
    have h_ctx := h_eq [A] [B]
    simp only [inTraceLanguage] at h_ctx
    have h_pm : wordProduct ([A] ++ [M] ++ [B]) = mul (mul A M) B := by
      show List.foldl mul one [A, M, B] = mul (mul A M) B
      simp only [List.foldl, one_mul]
    have h_pz : wordProduct ([A] ++ [zero] ++ [B]) = mul (mul A zero) B := by
      show List.foldl mul one [A, zero, B] = mul (mul A zero) B
      simp only [List.foldl, one_mul]
    rw [h_pm, h_pz] at h_ctx
    have h_amb : trace (mul (mul A M) B) = true := by
      rw [trace_true]
      exact ⟨i, (mul_apply_true _ _ _ _).mpr ⟨j,
        (mul_apply_true _ _ _ _).mpr ⟨i, by simp [A], hij⟩,
        by simp [B]⟩⟩
    have h_azb : trace (mul (mul A zero) B) = false := by
      simp only [trace, mul, zero]
      simp
    rw [h_azb] at h_ctx
    exact Bool.false_ne_true (h_ctx.mp h_amb)

/-- Identity is not syntactically equivalent to zero. -/
theorem id_not_equiv_zero (h_n : n >= 1) :
    ¬ SyntacticEquiv ([] : List (BoolMat n)) [zero] := by
  intro h_eq
  have h_ctx := h_eq [] []
  simp only [inTraceLanguage, List.nil_append, List.append_nil,
             wordProduct_nil, wordProduct_singleton] at h_ctx
  have h_one : trace (one : BoolMat n) = true :=
    (trace_true _).mpr ⟨⟨0, h_n⟩, by simp [one]⟩
  exact Bool.false_ne_true (trace_zero ▸ (h_ctx.mp h_one))

/-- The syntactic monoid has at least 3 distinct classes. -/
theorem syntactic_monoid_at_least_3_classes {M : BoolMat n}
    (h_trace : trace M = false) (h_nonzero : ¬ isZero M) (h_n : n >= 1) :
    ¬ SyntacticEquiv [M] [] ∧
    ¬ SyntacticEquiv [M] [zero] ∧
    ¬ SyntacticEquiv ([] : List (BoolMat n)) [zero] :=
  ⟨traceless_not_equiv_id h_trace h_n,
   nonzero_not_equiv_zero h_nonzero,
   id_not_equiv_zero h_n⟩

/-! ## Part 6: Involutions and Periodicity -/

/-- A matrix is an involution: S² = I. -/
def IsInvolution (S : BoolMat n) : Prop :=
  mul S S = one

/-- An involution is nonzero (for n >= 1). -/
theorem involution_nonzero {S : BoolMat n} (h_inv : IsInvolution S) (h_n : n >= 1) :
    ¬ isZero S := by
  intro h_zero
  have h_ss_zero : isZero (mul S S) := by
    intro i j
    cases h : mul S S i j with
    | false => rfl
    | true =>
      obtain ⟨k, hk1, _⟩ := (mul_apply_true S S i j).mp h
      exact absurd (h_zero i k ▸ hk1) Bool.false_ne_true
  have h_diag : (one : BoolMat n) ⟨0, h_n⟩ ⟨0, h_n⟩ = true := by simp [one]
  rw [← h_inv] at h_diag
  exact absurd (h_ss_zero ⟨0, h_n⟩ ⟨0, h_n⟩ ▸ h_diag) Bool.false_ne_true

/-- Power of an involution alternates: even -> one, odd -> S. -/
theorem involution_pow_parity {S : BoolMat n} (h_inv : IsInvolution S) (m : Nat) :
    BoolMat.pow S m = if m % 2 = 0 then one else S := by
  induction m with
  | zero => simp [BoolMat.pow]
  | succ m ih =>
    simp only [BoolMat.pow, ih]
    split
    · rename_i h_even
      rw [mul_one]
      have : (m + 1) % 2 ≠ 0 := by omega
      simp [this]
    · rename_i h_odd
      show mul S S = if (m + 1) % 2 = 0 then one else S
      rw [h_inv]
      have : (m + 1) % 2 = 0 := by omega
      simp [this]

/-- An involution with trace = false creates a 2-periodic element in Syn(L). -/
theorem involution_creates_period {S : BoolMat n}
    (h_inv : IsInvolution S) (h_trace : trace S = false) (h_n : n >= 1) :
    ¬ SyntacticEquiv [S] [] ∧
    SyntacticEquiv (wordPow [S] 2) [] := by
  refine ⟨traceless_not_equiv_id h_trace h_n, ?_⟩
  apply same_product_syntacticEquiv
  rw [wordProduct_pow, wordProduct_nil, wordProduct_singleton]
  simp only [BoolMat.pow, mul_one]
  exact h_inv

/-! ## Part 7: The Anti-Diagonal Witness -/

/-- The 2x2 anti-diagonal matrix: swaps coordinates. -/
def antiDiag2 : BoolMat 2 :=
  fun i j => decide (i.val + j.val = 1)

/-- antiDiag2 has trace = false. -/
theorem antiDiag2_trace : trace antiDiag2 = false := by native_decide

/-- antiDiag2 is an involution: S² = I. -/
theorem antiDiag2_involution : IsInvolution antiDiag2 := by
  show mul antiDiag2 antiDiag2 = one
  funext i j; revert i j; native_decide

/-- antiDiag2 is nonzero. -/
theorem antiDiag2_nonzero : ¬ isZero antiDiag2 :=
  involution_nonzero antiDiag2_involution (by omega)

/-- The 2x2 anti-diagonal creates period 2 in Syn(L). -/
theorem antiDiag2_period_2 :
    ¬ SyntacticEquiv [antiDiag2] [] ∧
    SyntacticEquiv (wordPow [antiDiag2] 2) ([] : List (BoolMat 2)) :=
  involution_creates_period antiDiag2_involution antiDiag2_trace (by omega)

/-! ## Part 8: Trace Language Non-Aperiodicity -/

/-- The syntactic monoid of the trace language on BoolMat 2 is NOT aperiodic. -/
theorem traceLanguage_not_aperiodic_2 : ¬ @TraceLanguageAperiodic 2 := by
  intro h_aper
  obtain ⟨k, hk⟩ := h_aper [antiDiag2]
  have h_ctx := hk [] []
  simp only [inTraceLanguage, List.nil_append, List.append_nil] at h_ctx
  rw [wordProduct_pow, wordProduct_pow, wordProduct_singleton] at h_ctx
  rw [involution_pow_parity antiDiag2_involution (k + 1),
      involution_pow_parity antiDiag2_involution k] at h_ctx
  by_cases h_even : k % 2 = 0
  · have h_k1 : (k + 1) % 2 ≠ 0 := by omega
    simp only [h_even, h_k1, ite_true, ite_false] at h_ctx
    exact Bool.false_ne_true (antiDiag2_trace ▸ h_ctx.mpr (by native_decide))
  · have h_k1 : (k + 1) % 2 = 0 := by omega
    simp only [h_even, h_k1, ite_true, ite_false] at h_ctx
    exact Bool.false_ne_true (antiDiag2_trace ▸ h_ctx.mp (by native_decide))

/-! ## Part 9: The Element-vs-Language Gap -/

/-- The trace language on BoolMat 2 is NOT star-free. -/
theorem non_aperiodic_not_star_free :
    ¬ @TraceLanguageAperiodic 2 :=
  traceLanguage_not_aperiodic_2

/-- The gap between element aperiodicity and language aperiodicity. -/
theorem element_vs_language_gap :
    (∀ (M : BoolMat 2), M.IsRankOne → SyntacticallyAperiodic [M]) ∧
    ¬ @TraceLanguageAperiodic 2 :=
  ⟨fun _ hM => rank1_syntactically_aperiodic hM,
   traceLanguage_not_aperiodic_2⟩

/-! ## Part 10: Trace Commutativity and Order Sensitivity -/

/-- Trace of a product is commutative: trace(AB) = trace(BA). -/
theorem trace_mul_commutative (A B : BoolMat n) :
    trace (mul A B) = trace (mul B A) := by
  apply Bool.eq_iff_iff.mpr
  simp only [trace_true, mul_apply_true]
  constructor
  · rintro ⟨i, k, h1, h2⟩; exact ⟨k, i, h2, h1⟩
  · rintro ⟨i, k, h1, h2⟩; exact ⟨k, i, h2, h1⟩

/-- Three-word composition is order-sensitive for trace. -/
theorem three_word_order_matters :
    ∃ (A B C : BoolMat 2),
      trace (mul (mul A B) C) ≠ trace (mul (mul A C) B) := by
  let A : BoolMat 2 := fun i j => decide (i.val = 0 ∧ j.val = 0)
  let B : BoolMat 2 := fun i j => decide (i.val = 0 ∧ j.val = 1)
  let C : BoolMat 2 := fun i j => decide (i.val = 1 ∧ j.val = 0)
  exact ⟨A, B, C, by native_decide⟩

/-! ## Part 11: Syntactic Congruence is a Congruence -/

/-- Syntactic equivalence is a right congruence. -/
theorem syntacticEquiv_append_right {u v : List (BoolMat n)}
    (h : SyntacticEquiv u v) (w : List (BoolMat n)) :
    SyntacticEquiv (u ++ w) (v ++ w) := by
  intro x y
  have := h x (w ++ y)
  simp only [List.append_assoc] at this ⊢
  exact this

/-- Syntactic equivalence is a left congruence. -/
theorem syntacticEquiv_append_left {u v : List (BoolMat n)}
    (h : SyntacticEquiv u v) (w : List (BoolMat n)) :
    SyntacticEquiv (w ++ u) (w ++ v) := by
  intro x y
  have := h (x ++ w) y
  simp only [List.append_assoc] at this ⊢
  exact this

/-- Syntactic equivalence is a congruence. -/
theorem syntacticEquiv_congr {u u' v v' : List (BoolMat n)}
    (hu : SyntacticEquiv u u') (hv : SyntacticEquiv v v') :
    SyntacticEquiv (u ++ v) (u' ++ v') :=
  syntacticEquiv_trans (syntacticEquiv_append_right hu v)
    (syntacticEquiv_append_left hv u')

/-! ## Part 12: Summary -/

/-- **Syntactic Monoid Theorem**: Complete characterization. -/
theorem syntactic_monoid_summary :
    (∀ (M : BoolMat 2), M.IsRankOne → SyntacticallyAperiodic [M])
    ∧ ¬ @TraceLanguageAperiodic 2
    ∧ ¬ SyntacticEquiv [antiDiag2] ([] : List (BoolMat 2))
    ∧ ¬ SyntacticEquiv [antiDiag2] ([zero] : List (BoolMat 2))
    ∧ ¬ SyntacticEquiv ([] : List (BoolMat 2)) [zero]
    ∧ SyntacticEquiv (wordPow [antiDiag2] 2) ([] : List (BoolMat 2))
    ∧ ∃ (A B C : BoolMat 2),
        trace (mul (mul A B) C) ≠ trace (mul (mul A C) B) := by
  refine ⟨fun _ hM => rank1_syntactically_aperiodic hM,
          traceLanguage_not_aperiodic_2,
          ?_, ?_, ?_,
          antiDiag2_period_2.2,
          three_word_order_matters⟩
  · exact (syntactic_monoid_at_least_3_classes antiDiag2_trace
      antiDiag2_nonzero (by omega)).1
  · exact (syntactic_monoid_at_least_3_classes antiDiag2_trace
      antiDiag2_nonzero (by omega)).2.1
  · exact (syntactic_monoid_at_least_3_classes antiDiag2_trace
      antiDiag2_nonzero (by omega)).2.2

end BoolMat
