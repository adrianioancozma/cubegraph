/-
  CubeGraph/Tau2Backward.lean — Backward Reasoning: Assume P=NP, Derive Constraints

  Agent-Tau2, Generation 13.

  ════════════════════════════════════════════════════════════════════════════
  THE ANTI-PATTERN: BACKWARD REASONING
  ════════════════════════════════════════════════════════════════════════════

  All previous agents used FORWARD reasoning: CubeGraph → barriers → bounds.
  This file tries BACKWARD: assume Frege proof size is polynomial → derive
  constraints → identify where contradiction would need to come from.

  THE CHAIN:
  1. If P = NP, then by Cook-Reckhow (1979), every UNSAT formula has
     poly-size Frege proofs: S = O(n^k) for some fixed k.
  2. frege_near_quadratic (PROVEN): c₂·S · (c₃·(|G| + c₂·S) + 1) ≥ (n/c₁)²
  3. With |G| ≤ C·n and S ≤ B (constant): O(B·n) ≥ Ω(n²). CONTRADICTION.
  4. With S = O(n): O(n²) ≥ Ω(n²). SATISFIABLE.
  5. So backward reasoning gives S unbounded but NOT super-polynomial.

  0 sorry. 1 new axiom (schoenebeck_linear_tight).

  See: FregeLowerBound.lean, PhiBSWRevived.lean, Epsilon2Final.lean.
  References: Cook-Reckhow (1979), BSW (2001), Schoenebeck (2008).
-/

import CubeGraph.FregeLowerBound

namespace CubeGraph

open BoolMat

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 1: STRENGTHENED SCHOENEBECK
    ═══════════════════════════════════════════════════════════════════════════ -/

/-- **Strengthened Schoenebeck**: UNSAT CubeGraphs from random 3-SAT at ρ_c
    have both |cubes| ≥ n AND |cubes| ≤ C·n.
    This is implicit in Schoenebeck (2008). -/
axiom schoenebeck_linear_tight :
    ∃ c_lo c_hi : Nat, c_lo ≥ 2 ∧ c_hi ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph,
        G.cubes.length ≥ n ∧
        G.cubes.length ≤ c_hi * n ∧
        KConsistent G (n / c_lo) ∧
        ¬ G.Satisfiable

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 2: TIGHT FREGE BOUND
    ═══════════════════════════════════════════════════════════════════════════ -/

/-- **Tight Frege bound**: frege_near_quadratic with |G| ≤ C·n. -/
theorem frege_near_quadratic_tight :
    ∃ c₁ c₂ c₃ c₄ : Nat, c₁ ≥ 2 ∧ c₂ ≥ 1 ∧ c₃ ≥ 1 ∧ c₄ ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ G.cubes.length ≤ c₄ * n ∧
        ¬ G.Satisfiable ∧
        c₂ * minFregeSize G * (c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1) ≥
        (n / c₁) * (n / c₁) := by
  obtain ⟨c_lo, c_hi, hlo, hhi, h_sch⟩ := schoenebeck_linear_tight
  obtain ⟨c₂, hc₂, h_sim⟩ := frege_simulation
  obtain ⟨c₃, hc₃, h_bsw⟩ := bsw_with_formula_size
  refine ⟨c_lo, c₂, c₃, c_hi, hlo, hc₂, hc₃, hhi, fun n hn => ?_⟩
  obtain ⟨G, hsize_lo, hsize_hi, hkc, hunsat⟩ := h_sch n hn
  refine ⟨G, hsize_lo, hsize_hi, hunsat, ?_⟩
  obtain ⟨ext, hext_size, hext_sparse, hext_agg, hext_res⟩ := h_sim G hunsat
  have hkc_ext := er_kconsistent_from_aggregate G (n / c_lo) ext hext_sparse hext_agg hkc
  have h_bsw_ext := h_bsw ext.extended (n / c_lo) hkc_ext ext.still_unsat
  have h_rhs : c₃ * ext.extended.cubes.length + 1 ≤
               c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left c₃ hext_size) 1
  have step1 := Nat.mul_le_mul_left (minResolutionSize ext.extended) h_rhs
  have step2 := Nat.mul_le_mul_right
    (c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1) hext_res
  exact Nat.le_trans (Nat.le_trans h_bsw_ext step1) step2

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 3: FREGE SIZE IS UNBOUNDED
    ═══════════════════════════════════════════════════════════════════════════ -/

/-- For large enough m, m * m > a * m + b. -/
private theorem quad_beats_linear (a b : Nat) :
    ∃ m₀ : Nat, m₀ ≥ 1 ∧ ∀ m ≥ m₀, m * m > a * m + b := by
  refine ⟨a + b + 2, by omega, fun m hm => ?_⟩
  have hm_big : m ≥ a + 2 := by omega
  have h1 : m * m ≥ m * (a + 2) := Nat.mul_le_mul_left m hm_big
  have h2 : m * (a + 2) = m * a + m * 2 := Nat.mul_add m a 2
  have h3 : m * a = a * m := Nat.mul_comm m a
  -- m * m ≥ m * (a+2) = a*m + 2*m, and 2*m ≥ 2*(a+b+2) > b
  omega

/-- Products of Nat are commutative and associative — helper for reordering. -/
private theorem mul_reorder_5 (a b c d e : Nat) :
    a * b * c * (d * (e * (m₀ + 1))) = e * a * c * d * b * (m₀ + 1) := by
  simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]

private theorem mul_reorder_4 (a b c d : Nat) :
    a * b * c * (d * e) = d * a * c * b * e := by
  simp [Nat.mul_comm, Nat.mul_left_comm]

/-- a * (b * (c + d) + 1) = a*b*c + a*b*d + a for Nat. -/
private theorem distrib_expand (a b c d : Nat) :
    a * (b * (c + d) + 1) = a * b * c + a * b * d + a := by
  simp [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]

/-- **Frege size is unbounded**: for any B, ∃ UNSAT G with minFregeSize G > B. -/
theorem frege_unbounded :
    ∀ B : Nat, ∃ G : CubeGraph, ¬ G.Satisfiable ∧ minFregeSize G > B := by
  obtain ⟨c₁, c₂, c₃, c₄, hc₁, hc₂, hc₃, hc₄, hfnq⟩ := frege_near_quadratic_tight
  intro B
  obtain ⟨m₀, _, hm₀⟩ := quad_beats_linear
    (c₁ * c₂ * c₃ * c₄ * B) (c₂ * c₂ * c₃ * B * B + c₂ * B)
  have hc₁_pos : 0 < c₁ := by omega
  have hn : c₁ * (m₀ + 1) ≥ 1 :=
    Nat.le_trans (by omega : 1 ≤ 1 * 1) (Nat.mul_le_mul (by omega : 1 ≤ c₁) (by omega : 1 ≤ m₀ + 1))
  obtain ⟨G, _, hsize_hi, hunsat, hineq⟩ := hfnq (c₁ * (m₀ + 1)) hn
  refine ⟨G, hunsat, ?_⟩
  -- Use Nat.lt_or_ge to case split: either S > B (done) or S ≤ B (contradiction).
  rcases Nat.lt_or_ge B (minFregeSize G) with h_gt | h_le
  · -- S > B. Convert from B < S to S > B.
    exact h_gt
  · -- S ≤ B → contradiction.
    exfalso
    have h_div : c₁ * (m₀ + 1) / c₁ = m₀ + 1 :=
      Nat.mul_div_cancel_left (m₀ + 1) hc₁_pos
    rw [h_div] at hineq
    -- Upper bound LHS: S ≤ B and |G| ≤ c₄ * (c₁ * (m₀+1))
    have h_upper : c₂ * minFregeSize G * (c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1) ≤
                   c₂ * B * (c₃ * (c₄ * (c₁ * (m₀ + 1)) + c₂ * B) + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left c₂ h_le)
        (Nat.add_le_add_right (Nat.mul_le_mul_left c₃
          (Nat.add_le_add hsize_hi (Nat.mul_le_mul_left c₂ h_le))) 1)
    have h_combined := Nat.le_trans hineq h_upper
    -- Expand RHS using distributivity
    have h_exp := distrib_expand (c₂ * B) c₃ (c₄ * (c₁ * (m₀ + 1))) (c₂ * B)
    -- h_exp : c₂*B*(c₃*(c₄*(c₁*(m₀+1)) + c₂*B) + 1)
    --       = c₂*B*c₃*(c₄*(c₁*(m₀+1))) + c₂*B*c₃*(c₂*B) + c₂*B
    -- Reorder factors in each term:
    -- Term 1: c₂*B*c₃*(c₄*(c₁*(m₀+1))) = c₁*c₂*c₃*c₄*B*(m₀+1)
    have ht1 : c₂ * B * c₃ * (c₄ * (c₁ * (m₀ + 1))) =
               c₁ * c₂ * c₃ * c₄ * B * (m₀ + 1) := by
      simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    -- Term 2: c₂*B*c₃*(c₂*B) = c₂*c₂*c₃*B*B
    have ht2 : c₂ * B * c₃ * (c₂ * B) = c₂ * c₂ * c₃ * B * B := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    rw [h_exp, ht1, ht2] at h_combined
    -- h_combined : (m₀+1)*(m₀+1) ≤ c₁*c₂*c₃*c₄*B*(m₀+1) + c₂*c₂*c₃*B*B + c₂*B
    -- hm₀ : ∀ m ≥ m₀, m*m > c₁*c₂*c₃*c₄*B*m + (c₂*c₂*c₃*B*B + c₂*B)
    have h_gt := hm₀ (m₀ + 1) (by omega)
    omega

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 4: BACKWARD k=1 IS CONSISTENT
    ═══════════════════════════════════════════════════════════════════════════ -/

/-- **Backward k=1 is consistent**: S = C·n satisfies the inequality. -/
theorem backward_k1_consistent :
    ∀ c₁ c₂ c₃ c₄ : Nat, c₁ ≥ 2 → c₂ ≥ 1 → c₃ ≥ 1 → c₄ ≥ 1 →
      ∃ C : Nat, C ≥ 1 ∧ ∀ n : Nat,
        c₂ * (C * n) * (c₃ * (c₄ * n + c₂ * (C * n)) + 1) ≥
        (n / c₁) * (n / c₁) := by
  intro c₁ c₂ c₃ c₄ hc₁ hc₂ hc₃ hc₄
  -- Choose C = c₁ * c₁.
  have hC : c₁ * c₁ ≥ 1 := by
    have : c₁ ≥ 1 := by omega
    exact Nat.le_trans (by omega : 1 ≤ 1 * 1) (Nat.mul_le_mul this this)
  refine ⟨c₁ * c₁, hC, fun n => ?_⟩
  -- (n/c₁)² ≤ n² (since n/c₁ ≤ n)
  have h_div_le : n / c₁ ≤ n := Nat.div_le_self n c₁
  have h_rhs_le : (n / c₁) * (n / c₁) ≤ n * n :=
    Nat.mul_le_mul h_div_le h_div_le
  -- Show LHS ≥ n * n. Split into two factors, each ≥ n.
  -- factor1 = c₂ * (c₁ * c₁ * n) = c₂ * c₁² * n
  -- factor2 = c₃ * (c₄ * n + c₂ * (c₁ * c₁ * n)) + 1
  -- factor1 ≥ n: since c₂ * c₁² ≥ 1 * 4 = 4 ≥ 1
  -- factor2 ≥ n: since c₃ * (c₄ + c₂*c₁²) ≥ 1 and +1 handles n=0
  suffices h : c₂ * (c₁ * c₁ * n) * (c₃ * (c₄ * n + c₂ * (c₁ * c₁ * n)) + 1) ≥ n * n from
    Nat.le_trans h_rhs_le h
  -- factor1 ≥ n
  have hf1 : c₂ * (c₁ * c₁ * n) ≥ n := by
    have hmul_ge : c₂ * (c₁ * c₁) ≥ 1 :=
      Nat.le_trans (by omega : 1 ≤ 1 * 1) (Nat.mul_le_mul (by omega : 1 ≤ c₂)
        (Nat.mul_le_mul (by omega : 1 ≤ c₁) (by omega : 1 ≤ c₁)))
    have : c₂ * (c₁ * c₁ * n) = c₂ * (c₁ * c₁) * n :=
      (Nat.mul_assoc c₂ (c₁ * c₁) n).symm
    rw [this]
    exact Nat.le_trans (Nat.le_refl n) (Nat.le_mul_of_pos_left n (by omega))
  -- factor2 ≥ n
  have hf2 : c₃ * (c₄ * n + c₂ * (c₁ * c₁ * n)) + 1 ≥ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · omega
    · -- n ≥ 1. c₄*n ≥ n, so inner ≥ n, so c₃ * inner ≥ n, so c₃*inner+1 > n ≥ n
      have h_inner : c₄ * n + c₂ * (c₁ * c₁ * n) ≥ n :=
        Nat.le_trans (Nat.le_trans (Nat.le_refl n) (Nat.le_mul_of_pos_left n (by omega))) (Nat.le_add_right _ _)
      have : c₃ * (c₄ * n + c₂ * (c₁ * c₁ * n)) ≥ n :=
        Nat.le_trans h_inner (Nat.le_mul_of_pos_left _ (by omega))
      omega
  exact Nat.mul_le_mul hf1 hf2

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 5: SUMMARY
    ═══════════════════════════════════════════════════════════════════════════ -/

/-- The BSW barrier: re-export of frege_near_quadratic. -/
theorem bsw_barrier_documented :
    ∃ c₁ c₂ c₃ : Nat, c₁ ≥ 2 ∧ c₂ ≥ 1 ∧ c₃ ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        c₂ * minFregeSize G * (c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1) ≥
        (n / c₁) * (n / c₁) :=
  frege_near_quadratic

/-- Forward and backward give the same bounds. -/
theorem backward_equals_forward :
    (∃ c₁ c₂ c₃ : Nat, c₁ ≥ 2 ∧ c₂ ≥ 1 ∧ c₃ ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        c₂ * minFregeSize G * (c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1) ≥
        (n / c₁) * (n / c₁))
    ∧ (∀ B : Nat, ∃ G : CubeGraph, ¬ G.Satisfiable ∧ minFregeSize G > B) :=
  ⟨frege_near_quadratic, frege_unbounded⟩

/-! ═══════════════════════════════════════════════════════════════════════════
    HONEST ACCOUNTING
    ═══════════════════════════════════════════════════════════════════════════

    WHAT THIS FILE PROVES (0 sorry, 1 new axiom):

    New axiom (1):
    - schoenebeck_linear_tight: |G| ≤ C·n (implicit in Schoenebeck 2008)

    New theorems (5):
    1. frege_near_quadratic_tight: with |G| ≤ C·n
    2. frege_unbounded: ∀ B, ∃ UNSAT G with S > B
    3. backward_k1_consistent: S = O(n) is consistent (barrier)
    4. bsw_barrier_documented: re-export
    5. backward_equals_forward: same bound

    WHAT THIS DOES NOT PROVE:
    - P ≠ NP
    - Super-polynomial Frege lower bounds
    - Any advantage of backward over forward reasoning

    THE FINDING:
    Backward reasoning gives IDENTICAL bounds to forward.
    BSW denominator absorbs polynomial proof-size growth.
    Super-polynomial requires TransferConstrained or new techniques.
    ════════════════════════════════════════════════════════════════════════ -/

end CubeGraph
