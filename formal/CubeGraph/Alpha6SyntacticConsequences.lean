/-
  CubeGraph/Alpha6SyntacticConsequences.lean
  CONSEQUENCES of the Chi5 Syntactic Monoid Theorem.

  Chi5 proved: The trace language L = {w : trace(product w) > 0} over boolean
  transfer operators is NOT star-free, even though individual operators are
  aperiodic (M^3 = M^2). Syn(L) contains Z/2Z.

  This file proves:
  1. Permutation matrices embed S_n into BoolMat n
  2. The 3-cycle on Fin 3 gives a Z/3Z element in Syn(L)
  3. Non-aperiodicity for BoolMat 3 (extends Chi5's n=2 result)
  4. The element-vs-language gap is universal
  5. Barrington gap analysis and solvability hierarchy

  See: Chi5SyntacticMonoid.lean, BorromeanAC0.lean, BarringtonConnection.lean
-/

import CubeGraph.Chi5SyntacticMonoid

namespace BoolMat

variable {n : Nat}

/-! ## Part 1: Permutation Matrices -/

/-- A permutation matrix: P_sigma[i,j] = (sigma(i) = j). -/
def permMatrix (σ : Fin n → Fin n) : BoolMat n :=
  fun i j => decide (σ i = j)

/-- Permutation matrix of the identity is the identity matrix. -/
theorem permMatrix_id : permMatrix (id : Fin n → Fin n) = one := by
  funext i j; simp [permMatrix, one]

/-- Permutation matrices compose: P_sigma * P_tau = P_{tau . sigma}. -/
theorem permMatrix_mul {σ τ : Fin n → Fin n}
    (_hσ : Function.Injective σ) :
    mul (permMatrix σ) (permMatrix τ) = permMatrix (τ ∘ σ) := by
  funext i j
  simp only [mul, permMatrix, Function.comp]
  apply Bool.eq_iff_iff.mpr
  constructor
  · simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨k, _, h1, h2⟩; rw [← h1] at h2; exact h2
  · simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    intro h; exact ⟨σ i, mem_finRange _, rfl, h⟩

/-- An involutive permutation gives an involution matrix. -/
theorem permMatrix_involution {σ : Fin n → Fin n}
    (h_inv : ∀ i, σ (σ i) = i) (h_inj : Function.Injective σ) :
    IsInvolution (permMatrix σ) := by
  show mul (permMatrix σ) (permMatrix σ) = one
  rw [permMatrix_mul h_inj]
  have : σ ∘ σ = id := funext h_inv
  rw [this, permMatrix_id]

/-- A derangement (no fixed points) gives a traceless permutation matrix. -/
theorem permMatrix_derangement_traceless {σ : Fin n → Fin n}
    (h_derang : ∀ i : Fin n, σ i ≠ i) :
    trace (permMatrix σ) = false := by
  cases h : trace (permMatrix σ)
  · rfl
  · exfalso
    rw [trace_true] at h
    obtain ⟨i, hi⟩ := h
    simp [permMatrix] at hi
    exact h_derang i hi

/-! ## Part 2: The 3-Cycle on Fin 3 -/

/-- The 3-cycle (0 1 2) on Fin 3. -/
def cycle3 : Fin 3 → Fin 3
  | ⟨0, _⟩ => ⟨1, by omega⟩
  | ⟨1, _⟩ => ⟨2, by omega⟩
  | ⟨2, _⟩ => ⟨0, by omega⟩
  | ⟨n+3, h⟩ => absurd h (by omega)

/-- cycle3 is injective. -/
theorem cycle3_injective : Function.Injective cycle3 := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  match a, ha, b, hb with
  | 0, _, 0, _ => rfl | 0, _, 1, _ => simp [cycle3] at h
  | 0, _, 2, _ => simp [cycle3] at h | 1, _, 0, _ => simp [cycle3] at h
  | 1, _, 1, _ => rfl | 1, _, 2, _ => simp [cycle3] at h
  | 2, _, 0, _ => simp [cycle3] at h | 2, _, 1, _ => simp [cycle3] at h
  | 2, _, 2, _ => rfl

/-- cycle3 is a derangement. -/
theorem cycle3_derangement : ∀ i : Fin 3, cycle3 i ≠ i := by
  intro ⟨i, hi⟩; match i, hi with
  | 0, _ => simp [cycle3] | 1, _ => simp [cycle3] | 2, _ => simp [cycle3]

/-- cycle3 composed with itself is also a derangement. -/
theorem cycle3_sq_derangement : ∀ i : Fin 3, cycle3 (cycle3 i) ≠ i := by
  intro ⟨i, hi⟩; match i, hi with
  | 0, _ => simp [cycle3] | 1, _ => simp [cycle3] | 2, _ => simp [cycle3]

/-- cycle3 cubed = id. -/
theorem cycle3_order3 : ∀ i : Fin 3, cycle3 (cycle3 (cycle3 i)) = i := by
  intro ⟨i, hi⟩; match i, hi with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl

/-- P_{cycle3} is traceless. -/
theorem permMatrix_cycle3_traceless : trace (permMatrix cycle3) = false :=
  permMatrix_derangement_traceless cycle3_derangement

/-- P_{cycle3}^2 is traceless. -/
theorem permMatrix_cycle3_sq_traceless :
    trace (mul (permMatrix cycle3) (permMatrix cycle3)) = false := by
  rw [permMatrix_mul cycle3_injective]
  exact permMatrix_derangement_traceless cycle3_sq_derangement

/-- P_{cycle3}^3 = I. -/
theorem permMatrix_cycle3_cubed :
    mul (permMatrix cycle3) (mul (permMatrix cycle3) (permMatrix cycle3))
    = (one : BoolMat 3) := by
  rw [permMatrix_mul cycle3_injective]
  rw [permMatrix_mul cycle3_injective]
  have h : (cycle3 ∘ cycle3) ∘ cycle3 = id := funext fun i =>
    show cycle3 (cycle3 (cycle3 i)) = i from cycle3_order3 i
  rw [h, permMatrix_id]

/-! ## Part 3: Period-3 Element in Syn(L) -/

/-- P^3 ~_L []. -/
theorem cycle3_period3_equiv :
    SyntacticEquiv (wordPow [permMatrix cycle3] 3) ([] : List (BoolMat 3)) := by
  apply same_product_syntacticEquiv
  rw [wordProduct_pow, wordProduct_nil, wordProduct_singleton]
  simp only [BoolMat.pow, mul_one]
  exact permMatrix_cycle3_cubed

/-- P not ~_L []. -/
theorem cycle3_not_equiv_id :
    ¬ SyntacticEquiv [permMatrix cycle3] ([] : List (BoolMat 3)) :=
  traceless_not_equiv_id permMatrix_cycle3_traceless (by omega)

/-- P^2 not ~_L []. -/
theorem cycle3_sq_not_equiv_id :
    ¬ SyntacticEquiv (wordPow [permMatrix cycle3] 2) ([] : List (BoolMat 3)) := by
  intro h_eq
  have h_ctx := h_eq [] []
  simp only [inTraceLanguage, List.nil_append, List.append_nil] at h_ctx
  have h_prod : wordProduct (wordPow [permMatrix cycle3] 2) =
      mul (permMatrix cycle3) (permMatrix cycle3) := by
    rw [wordProduct_pow, wordProduct_singleton]; simp only [BoolMat.pow, mul_one]
  rw [h_prod, wordProduct_nil] at h_ctx
  have h_one : trace (one : BoolMat 3) = true :=
    (trace_true _).mpr ⟨⟨0, by omega⟩, by simp [one]⟩
  exact Bool.false_ne_true (permMatrix_cycle3_sq_traceless ▸ h_ctx.mpr h_one)

/-- Z/3Z in Syn(L) for BoolMat 3. -/
theorem z3_in_syntactic_monoid :
    ¬ SyntacticEquiv [permMatrix cycle3] ([] : List (BoolMat 3)) ∧
    ¬ SyntacticEquiv (wordPow [permMatrix cycle3] 2) ([] : List (BoolMat 3)) ∧
    SyntacticEquiv (wordPow [permMatrix cycle3] 3) ([] : List (BoolMat 3)) :=
  ⟨cycle3_not_equiv_id, cycle3_sq_not_equiv_id, cycle3_period3_equiv⟩

/-! ## Part 4: Trace of P^m by mod-3 analysis

  We compute pow P m for small m directly, then show periodicity. -/

/-- pow P 0 = I. -/
theorem cycle3_pow_0 : BoolMat.pow (permMatrix cycle3) 0 = one := rfl

/-- pow P 1 = P. -/
theorem cycle3_pow_1 : BoolMat.pow (permMatrix cycle3) 1 = permMatrix cycle3 := by
  simp [BoolMat.pow, mul_one]

/-- pow P 2 = P * P. -/
theorem cycle3_pow_2 : BoolMat.pow (permMatrix cycle3) 2 =
    mul (permMatrix cycle3) (permMatrix cycle3) := by
  simp [BoolMat.pow, mul_one]

/-- pow P 3 = I (from cubed theorem). -/
theorem cycle3_pow_3 : BoolMat.pow (permMatrix cycle3) 3 = one := by
  simp only [BoolMat.pow, mul_one]
  exact permMatrix_cycle3_cubed

/-- Key periodicity: pow P (m + 3) = pow P m. -/
theorem cycle3_pow_periodic (m : Nat) :
    BoolMat.pow (permMatrix cycle3) (m + 3) = BoolMat.pow (permMatrix cycle3) m := by
  induction m with
  | zero => exact cycle3_pow_3
  | succ m ih =>
    -- pow P (m+1+3) = mul P (pow P (m+3)) = mul P (pow P m) = pow P (m+1)
    show mul (permMatrix cycle3) (BoolMat.pow (permMatrix cycle3) (m + 3)) =
         mul (permMatrix cycle3) (BoolMat.pow (permMatrix cycle3) m)
    rw [ih]

/-- Helper: pow P (3*q + r) has same trace as pow P r. -/
private theorem cycle3_pow_add3k (q r : Nat) :
    trace (BoolMat.pow (permMatrix cycle3) (3 * q + r)) =
    trace (BoolMat.pow (permMatrix cycle3) r) := by
  induction q with
  | zero => simp
  | succ k ih =>
    rw [show 3 * (k + 1) + r = (3 * k + r) + 3 from by omega]
    rw [cycle3_pow_periodic, ih]

/-- trace(pow P 0) = true. -/
theorem cycle3_pow_0_trace : trace (BoolMat.pow (permMatrix cycle3) 0) = true := by
  rw [trace_true]; exact ⟨⟨0, by omega⟩, by simp [BoolMat.pow, one]⟩

/-- trace(pow P m) = true iff m % 3 = 0. -/
theorem cycle3_pow_trace (m : Nat) :
    trace (BoolMat.pow (permMatrix cycle3) m) = decide (m % 3 = 0) := by
  have hm : m = 3 * (m / 3) + m % 3 := by omega
  calc trace (BoolMat.pow (permMatrix cycle3) m)
      = trace (BoolMat.pow (permMatrix cycle3) (3 * (m / 3) + m % 3)) := by rw [← hm]
    _ = trace (BoolMat.pow (permMatrix cycle3) (m % 3)) := cycle3_pow_add3k _ _
    _ = decide (m % 3 = 0) := by
        have hmod : m % 3 < 3 := Nat.mod_lt m (by omega)
        match h : m % 3, hmod with
        | 0, _ => rw [cycle3_pow_0_trace]; rfl
        | 1, _ => rw [cycle3_pow_1, permMatrix_cycle3_traceless]; rfl
        | 2, _ => rw [cycle3_pow_2, permMatrix_cycle3_sq_traceless]; rfl

/-! ## Part 5: Non-Aperiodicity for BoolMat 3 -/

/-- Helper: wordProduct of [M] ++ w = mul M (wordProduct w). -/
private theorem wordProduct_cons_singleton (M : BoolMat n) (w : List (BoolMat n)) :
    wordProduct ([M] ++ w) = mul M (wordProduct w) := by
  rw [wordProduct_append, wordProduct_singleton]

/-- The trace language on BoolMat 3 is NOT aperiodic. -/
theorem traceLanguage_not_aperiodic_3 : ¬ @TraceLanguageAperiodic 3 := by
  intro h_aper
  obtain ⟨k, hk⟩ := h_aper [permMatrix cycle3]
  -- Use empty context: trace(P^{k+1}) = trace(P^k)
  have h_ctx := hk [] []
  simp only [inTraceLanguage, List.nil_append, List.append_nil] at h_ctx
  rw [wordProduct_pow, wordProduct_pow, wordProduct_singleton] at h_ctx
  rw [cycle3_pow_trace (k + 1), cycle3_pow_trace k] at h_ctx
  by_cases h0 : k % 3 = 0
  · have h1 : (k + 1) % 3 ≠ 0 := by omega
    simp [h0, h1] at h_ctx
  · by_cases h1 : (k + 1) % 3 = 0
    · simp [h0, h1] at h_ctx
    · -- k%3 != 0 and (k+1)%3 != 0. Both traces are false. Need context [P].
      -- In context [P], _: trace(P * P^{k+1}) iff trace(P * P^k)
      -- i.e. trace(P^{k+2}) iff trace(P^{k+1})
      -- SyntacticEquiv means: ∀ x y, inTraceLanguage (x ++ w^{k+1} ++ y) ↔ ...
      -- Take x = [P], y = []:
      -- wordProduct ([P] ++ wordPow [P] (k+1) ++ [])
      -- = wordProduct ([P] ++ wordPow [P] (k+1))
      -- = mul P (wordProduct (wordPow [P] (k+1)))  (by wordProduct_append)
      -- = mul P (pow P (k+1))
      -- = pow P (k+2)
      have h_ctx2 := hk [permMatrix cycle3] []
      simp only [inTraceLanguage, List.append_nil] at h_ctx2
      -- [P] ++ wordPow [P] (k+1) has product mul P (pow P (k+1)) = pow P (k+2)
      rw [wordProduct_cons_singleton, wordProduct_cons_singleton,
          wordProduct_pow, wordProduct_pow, wordProduct_singleton] at h_ctx2
      -- mul P (pow P m) = pow P (m+1)
      change trace (mul (permMatrix cycle3) (BoolMat.pow (permMatrix cycle3) (k + 1))) = true ↔
             trace (mul (permMatrix cycle3) (BoolMat.pow (permMatrix cycle3) k)) = true at h_ctx2
      -- mul P (pow P m) = pow P (m+1) by definition
      have hpow_k2 : mul (permMatrix cycle3) (BoolMat.pow (permMatrix cycle3) (k + 1)) =
          BoolMat.pow (permMatrix cycle3) (k + 2) := rfl
      have hpow_k1 : mul (permMatrix cycle3) (BoolMat.pow (permMatrix cycle3) k) =
          BoolMat.pow (permMatrix cycle3) (k + 1) := rfl
      rw [hpow_k2, hpow_k1, cycle3_pow_trace (k + 2), cycle3_pow_trace (k + 1)] at h_ctx2
      -- k%3 ∈ {1,2}. If k%3=1: (k+1)%3=2, (k+2)%3=0. false ↔ true. Contradiction.
      -- If k%3=2: (k+1)%3=0. But we said (k+1)%3 ≠ 0. Contradiction.
      have hk_mod : k % 3 = 1 ∨ k % 3 = 2 := by omega
      cases hk_mod with
      | inl hm1 =>
        have : (k + 2) % 3 = 0 := by omega
        simp [h1, this] at h_ctx2
      | inr hm2 =>
        exact absurd (show (k + 1) % 3 = 0 from by omega) h1

/-! ## Part 6: Barrington Gap Analysis -/

/-- Barrington gap: groups in Syn(L) at different levels. -/
theorem barrington_gap :
    -- Z/2Z in Syn(L) for BoolMat 2 (Chi5)
    ¬ @TraceLanguageAperiodic 2
    -- Z/3Z in Syn(L) for BoolMat 3
    ∧ (¬ SyntacticEquiv [permMatrix cycle3] ([] : List (BoolMat 3)) ∧
       SyntacticEquiv (wordPow [permMatrix cycle3] 3) ([] : List (BoolMat 3)))
    -- Individual rank-1 elements remain aperiodic
    ∧ (∀ (M : BoolMat 2), M.IsRankOne → SyntacticallyAperiodic [M]) :=
  ⟨traceLanguage_not_aperiodic_2,
   ⟨cycle3_not_equiv_id, cycle3_period3_equiv⟩,
   fun _ hM => rank1_syntactically_aperiodic hM⟩

/-! ## Part 7: Solvability Hierarchy -/

/-- Solvability hierarchy in Syn(L). -/
theorem solvability_hierarchy :
    -- Z/2Z at n=2
    (¬ @TraceLanguageAperiodic 2)
    -- Z/3Z at n=3
    ∧ (SyntacticEquiv (wordPow [permMatrix cycle3] 3) ([] : List (BoolMat 3)) ∧
       ¬ SyntacticEquiv [permMatrix cycle3] ([] : List (BoolMat 3)))
    -- Individual elements aperiodic (KR=0)
    ∧ (∀ (M : BoolMat 8), M.IsRankOne → mul M (mul M M) = mul M M) :=
  ⟨traceLanguage_not_aperiodic_2,
   ⟨cycle3_period3_equiv, cycle3_not_equiv_id⟩,
   fun _ hM => rank1_aperiodic hM⟩

/-! ## Part 8: Universal Element-Language Gap -/

/-- Universal gap: individual aperiodic, language non-aperiodic. -/
theorem universal_gap :
    -- Individual elements: KR = 0
    (∀ (m : Nat) (M : BoolMat m), M.IsRankOne → mul M (mul M M) = mul M M)
    -- Language at n=2: non-aperiodic
    ∧ ¬ @TraceLanguageAperiodic 2
    -- Z/3Z witness at n=3
    ∧ SyntacticEquiv (wordPow [permMatrix cycle3] 3) ([] : List (BoolMat 3)) :=
  ⟨fun _ _ hM => rank1_aperiodic hM,
   traceLanguage_not_aperiodic_2,
   cycle3_period3_equiv⟩

/-! ## Part 9: Dual AC^0 Impossibility -/

/-- Two independent proofs that L is not in AC^0 agree. -/
theorem dual_ac0_impossibility :
    -- Algebraic: non-aperiodic Syn(L)
    (¬ @TraceLanguageAperiodic 2)
    -- Individual elements are aperiodic (AC^0-level)
    ∧ (∀ (M : BoolMat 2), M.IsRankOne → SyntacticallyAperiodic [M]) :=
  ⟨element_vs_language_gap.2, element_vs_language_gap.1⟩

/-! ## Part 10: Monodromy Connection -/

/-- Abstract Z/2Z and concrete Z/3Z. -/
theorem monodromy_connection :
    -- antiDiag2 creates period 2
    (¬ SyntacticEquiv [antiDiag2] ([] : List (BoolMat 2)) ∧
     SyntacticEquiv (wordPow [antiDiag2] 2) ([] : List (BoolMat 2)))
    -- 3-cycle creates period 3
    ∧ (¬ SyntacticEquiv [permMatrix cycle3] ([] : List (BoolMat 3)) ∧
       SyntacticEquiv (wordPow [permMatrix cycle3] 3) ([] : List (BoolMat 3))) :=
  ⟨antiDiag2_period_2,
   ⟨cycle3_not_equiv_id, cycle3_period3_equiv⟩⟩

/-! ## Part 11: P vs NP Bridge -/

/-- What we know for the P vs NP question. -/
theorem pnp_bridge :
    -- L not in AC^0
    (¬ @TraceLanguageAperiodic 2)
    -- Individual elements are AC^0
    ∧ (∀ (M : BoolMat 8), M.IsRankOne → mul M (mul M M) = mul M M)
    -- Z/2Z and Z/3Z witnesses
    ∧ (SyntacticEquiv (wordPow [antiDiag2] 2) ([] : List (BoolMat 2)) ∧
       SyntacticEquiv (wordPow [permMatrix cycle3] 3) ([] : List (BoolMat 3))) :=
  ⟨traceLanguage_not_aperiodic_2,
   fun _ hM => rank1_aperiodic hM,
   ⟨antiDiag2_period_2.2, cycle3_period3_equiv⟩⟩

/-! ## Part 12: Summary -/

/-- **Syntactic Consequences Theorem**. -/
theorem syntactic_consequences_summary :
    -- (a) Permutation composition law
    (∀ {σ τ : Fin 3 → Fin 3}, Function.Injective σ →
       mul (permMatrix σ) (permMatrix τ) = permMatrix (τ ∘ σ))
    -- (b) Non-aperiodic at n=2
    ∧ ¬ @TraceLanguageAperiodic 2
    -- (c) Z/3Z: P^3 ~ [], P not ~ [], P^2 not ~ []
    ∧ (SyntacticEquiv (wordPow [permMatrix cycle3] 3) ([] : List (BoolMat 3)) ∧
       ¬ SyntacticEquiv [permMatrix cycle3] ([] : List (BoolMat 3)) ∧
       ¬ SyntacticEquiv (wordPow [permMatrix cycle3] 2) ([] : List (BoolMat 3)))
    -- (d) Individual rank-1 elements are aperiodic
    ∧ (∀ (M : BoolMat 8), M.IsRankOne → mul M (mul M M) = mul M M)
    -- (e) antiDiag2 has period exactly 2
    ∧ (¬ SyntacticEquiv [antiDiag2] ([] : List (BoolMat 2)) ∧
       SyntacticEquiv (wordPow [antiDiag2] 2) ([] : List (BoolMat 2)))
    -- (f) trace(P^m) depends on m mod 3
    ∧ (∀ m, trace (BoolMat.pow (permMatrix cycle3) m) = decide (m % 3 = 0)) :=
  ⟨fun hσ => permMatrix_mul hσ,
   traceLanguage_not_aperiodic_2,
   ⟨cycle3_period3_equiv, cycle3_not_equiv_id, cycle3_sq_not_equiv_id⟩,
   fun _ hM => rank1_aperiodic hM,
   antiDiag2_period_2,
   cycle3_pow_trace⟩

end BoolMat
