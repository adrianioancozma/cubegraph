/-
  CubeGraph/BackwardLowerBound.lean — Backward Reasoning: Assume P=NP, Derive Constraints

  Agent-Tau2, Generation 13.

  CLEANUP (2026-03-24): Removed all theorems that depended on the unsound
  `frege_simulation` axiom (via `frege_near_quadratic`):
  - frege_near_quadratic_tight (used frege_simulation directly)
  - frege_unbounded (used frege_near_quadratic_tight)
  - bsw_barrier_documented (re-export of frege_near_quadratic)
  - backward_equals_forward (used frege_near_quadratic + frege_unbounded)

  Retained:
  - schoenebeck_linear_tight (axiom, independent of frege_simulation)
  - backward_k1_consistent (pure math, no axiom dependencies)
  - Helper lemmas (quad_beats_linear, mul_reorder_*, distrib_expand)

  See: FregeLowerBound.lean (frege_simulation removal)
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

/- REMOVED (2026-03-24): `frege_near_quadratic_tight` depended on `frege_simulation`
   (via direct use of the axiom in its proof). Removed because frege_simulation is unsound. -/

/- REMOVED (2026-03-24): `frege_unbounded` depended on `frege_near_quadratic_tight`. -/

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 2: BACKWARD k=1 IS CONSISTENT
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

/- REMOVED (2026-03-24): `bsw_barrier_documented` was a re-export of frege_near_quadratic. -/

/- REMOVED (2026-03-24): `backward_equals_forward` depended on frege_near_quadratic
   and frege_unbounded. -/

/-! ═══════════════════════════════════════════════════════════════════════════
    HONEST ACCOUNTING (updated 2026-03-24)
    ═══════════════════════════════════════════════════════════════════════════

    WHAT THIS FILE RETAINS (1 axiom, 2 theorems):

    Axiom (1):
    - schoenebeck_linear_tight: |G| ≤ C·n (implicit in Schoenebeck 2008)

    Theorems (2):
    1. quad_beats_linear: pure math helper
    2. backward_k1_consistent: S = O(n) is consistent (barrier)

    WHAT WAS REMOVED (4 theorems, all depended on unsound frege_simulation):
    1. frege_near_quadratic_tight
    2. frege_unbounded
    3. bsw_barrier_documented
    4. backward_equals_forward
    ════════════════════════════════════════════════════════════════════════ -/

end CubeGraph
