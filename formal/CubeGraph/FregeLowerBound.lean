/-
  CubeGraph/FregeLowerBound.lean — Frege Lower Bound (CONDITIONAL)

  ⚠️ WARNING: The `frege_simulation` axiom is NOT faithful to the literature.
  The standard Tseitin/Cook transformation does NOT satisfy the h_sparse and
  h_aggregate conditions required by `er_kconsistent_from_aggregate`:
  - h_sparse (gapCount ≥ 7): Tseitin 2-literal clauses padded to 3-SAT produce
    cubes with only 6 gaps (2 filled vertices in the same quadrant)
  - h_aggregate (fresh variable per cube): Tseitin extension variables appear in
    at least 2 cubes (definition + usage as input to parent gate)

  See: experiments-ml/026_2026-03-24_audit/Q3-FREGE-SIMULATION.md (detailed analysis)
  See: experiments-ml/026_2026-03-24_audit/Q3b-TSEITIN-6GAP.md (impossibility proof)

  CONSEQUENCE: `frege_superlinear` and `frege_near_quadratic` are FORMALLY VALID
  (0 sorry, correct deduction from axioms) but NOT SOUND (the axiom
  `frege_simulation` does not hold for the standard Tseitin transformation).
  The claimed Ω(n²/log n) Frege lower bound is NOT established.

  The deductive chain IS correct:
  1. schoenebeck_linear: KConsistent G (n/c₁) on UNSAT G      [correct axiom]
  2. frege_simulation: Frege(S) → ER extension                 [INCORRECT axiom]
  3. er_kconsistent_from_aggregate: KConsistent preserved       [proven, 0 sorry]
  4. bsw_with_formula_size_log: BSW in log form                [correct axiom]
  5. Combine: log₂(c·S) · (c·(n + c·S) + 1) ≥ n²/c'          [valid deduction]

  The file is kept for:
  - Documenting the approach and why it fails
  - The BSW log-form axiom and helper lemmas (useful elsewhere)
  - Backward compatibility (bsw_with_formula_size as theorem)

  To make this sound, one would need a NON-STANDARD Frege→ER simulation
  producing cubes with ≥ 7 gaps and fresh variables. No such simulation is known.

  References:
  - Ben-Sasson, Wigderson. JACM 48(2), 2001, Corollary 3.6.
  - Atserias, Bulatov, Dalmau. ICALP 2007.
  - Tseitin. "On the complexity of derivation in propositional calculus." 1968.
  - Cook. "Feasibly constructive proofs..." 1975.
-/

import CubeGraph.ERKConsistentInduction
import CubeGraph.ERLowerBound

namespace CubeGraph

open BoolMat

/-! ## Section 1: Frege proof size (axiom-specified) -/

/-- Minimum Frege proof size (total symbols) for an UNSAT CubeGraph.
    Frege uses propositional logic rules (modus ponens, conjunction intro, etc.)
    on formulas of arbitrary depth. Strictly stronger than Resolution/ER/PC/CP.

    We do not model Frege proofs directly. Properties from published results. -/
axiom minFregeSize (G : CubeGraph) : Nat

/-! ## Section 2: Frege → Resolution simulation via Tseitin -/

/-- ⚠️ UNSOUND AXIOM — h_sparse and h_aggregate NOT satisfied by standard Tseitin.

    Claims Frege(S) → ER extension with h_sparse (≥7 gaps) + h_aggregate (fresh var).
    Standard Tseitin produces cubes with 6 gaps (from 2-literal clause padding)
    and extension variables in ≥2 cubes (definition + parent gate).

    See Q3-FREGE-SIMULATION.md and Q3b-TSEITIN-6GAP.md for detailed analysis.
    The obstruction is structural: h_aggregate and h_diff_quadrant are mutually
    exclusive for Tseitin padded 2-literal clause cubes.

    Kept as axiom for: (1) documenting the approach, (2) showing what WOULD
    be needed (a non-standard simulation), (3) backward compatibility.

    Original references: Tseitin (1968), Cook (1975) — but the h_sparse/h_aggregate
    claims go BEYOND what these papers establish. -/
axiom frege_simulation :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      ∃ ext : ERExtension G,
        ext.extended.cubes.length ≤ G.cubes.length + c * minFregeSize G ∧
        (∀ i : Fin ext.extended.cubes.length,
          i.val ≥ G.cubes.length → (ext.extended.cubes[i]).gapCount ≥ 7) ∧
        (∀ i : Fin ext.extended.cubes.length,
          i.val ≥ G.cubes.length →
            ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length, i ≠ j →
              (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars) ∧
        minResolutionSize ext.extended ≤ c * minFregeSize G

/-! ## Section 3: BSW with explicit formula size (LOG FORM)

  BSW Corollary 3.6 (Ben-Sasson, Wigderson, JACM 2001):
    For a CNF formula F on n variables with initial clause width w₀,
    any Resolution refutation of size S has width w satisfying:

        w >= w(F |- bot) - O(sqrt(n * log S))

    where w(F |- bot) is the minimum refutation width. Equivalently:

        S >= 2^{(w - w₀)^2 / n}

    For 3-SAT (w₀ = 3): S >= 2^{(w-3)^2 / n}.

  Combined with ABD+AD (2007/2008): KConsistent G k => refutation width > k.

  Together: KConsistent G k /\ UNSAT => S >= 2^{(k-3)^2 / n} >= 2^{k^2/(c*n)}.

  In LOG form: log₂(S) * (c * n + 1) >= k * k.

  Here n = G.cubes.length (number of cubes = CSP variables in CubeGraph).

  NOTE: The previous version of this axiom used a POLYNOMIAL form:
    S * (c * N + 1) >= k^2
  which is strictly weaker (loses the exponential). That form only yielded
  S >= Omega(n) (linear). The log form yields S >= Omega(n^2 / log n)
  (genuinely super-linear) via the self-referential Frege argument.

  References: BSW (2001) Cor. 3.6, ABD+AD (2007/2008). -/
axiom bsw_with_formula_size_log :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph) (k : Nat),
      KConsistent G k → ¬ G.Satisfiable →
      Nat.log2 (minResolutionSize G) * (c * G.cubes.length + 1) ≥ k * k

/- OLD AXIOM (polynomial form — strictly weaker, kept for reference):

  axiom bsw_with_formula_size :
      ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph) (k : Nat),
        KConsistent G k → ¬ G.Satisfiable →
        minResolutionSize G * (c * G.cubes.length + 1) ≥ k * k

  This followed from BSW but lost the exponential by stating size directly
  instead of log₂(size). The consequence was only S >= Omega(n) (linear),
  as the Q1 audit confirmed: S = O(n) satisfies size * (c*N+1) >= k^2.
-/

/-! ## Section 3a: Helper lemmas for Nat.log2 -/

/-- log₂(n) ≤ n for all natural numbers. -/
private theorem log2_le_self (n : Nat) : Nat.log2 n ≤ n := by
  rcases n with _ | n
  · native_decide
  · have h : n + 1 ≠ 0 := by omega
    suffices Nat.log2 (n + 1) < n + 2 by omega
    rw [Nat.log2_lt h]
    calc n + 1 < 2 ^ (n + 1) := @Nat.lt_two_pow_self (n + 1)
      _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by omega) (by omega)

/-- log₂ is monotone: a ≤ b → log₂(a) ≤ log₂(b). -/
private theorem log2_mono {a b : Nat} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact Nat.zero_le _
  · rcases Nat.eq_zero_or_pos b with rfl | _
    · omega
    · rcases Nat.lt_or_ge (Nat.log2 b) (Nat.log2 a) with h_lt | h_ge
      · have hb_ne : b ≠ 0 := by omega
        have ha_ne : a ≠ 0 := by omega
        rw [Nat.log2_lt hb_ne] at h_lt
        have h_self := Nat.log2_self_le ha_ne
        omega
      · exact h_ge

/-! ## Section 3b: Backward compatibility — derive polynomial form from log form -/

/-- **BSW polynomial form** (derived from log form).
    Since log₂(size) ≤ size, the log-form axiom implies the polynomial form.
    This is strictly weaker but preserved for backward compatibility with
    downstream files (Tau2Backward.lean, Epsilon3CubeBSW.lean, etc.). -/
theorem bsw_with_formula_size :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph) (k : Nat),
      KConsistent G k → ¬ G.Satisfiable →
      minResolutionSize G * (c * G.cubes.length + 1) ≥ k * k := by
  obtain ⟨c, hc, h_log⟩ := bsw_with_formula_size_log
  exact ⟨c, hc, fun G k hkc hunsat => by
    have h := h_log G k hkc hunsat
    -- log₂(minRes) * (c * N + 1) ≥ k²
    -- log₂(minRes) ≤ minRes
    -- So: minRes * (c * N + 1) ≥ log₂(minRes) * (c * N + 1) ≥ k²
    exact Nat.le_trans h (Nat.mul_le_mul_right _ (log2_le_self _))⟩

/-! ## Section 4: Main theorem — self-referential bound (LOG FORM) -/

/-- ⚠️ CONDITIONAL on unsound `frege_simulation` axiom — see file header.

    Self-referential inequality: log₂(c₂·S) · (c₃·(|G| + c₂·S) + 1) ≥ (n/c₁)²

    IF `frege_simulation` were correct, this would imply S = Ω(n²/log n):
    - S = C·n → log₂(C·n)·(n+C·n) = O(n log n) < Ω(n²). Contradiction.
    - Therefore S = ω(n), more precisely S = Ω(n²/log n).

    However, `frege_simulation` is NOT faithful to Tseitin/Cook (see Q3 audit).
    The deduction is formally valid but the conclusion is NOT established. -/
theorem frege_superlinear :
    ∃ c₁ c₂ c₃ : Nat, c₁ ≥ 2 ∧ c₂ ≥ 1 ∧ c₃ ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        -- Log-form self-referential bound:
        -- log₂(c₂·S) · (c₃·(|G| + c₂·S) + 1) ≥ (n/c₁)²
        -- Consequence: S = Omega(n²/log n)
        Nat.log2 (c₂ * minFregeSize G) *
          (c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1) ≥
        (n / c₁) * (n / c₁) := by
  obtain ⟨c₁, hc₁, h_sch⟩ := schoenebeck_linear
  obtain ⟨c₂, hc₂, h_sim⟩ := frege_simulation
  obtain ⟨c₃, hc₃, h_bsw⟩ := bsw_with_formula_size_log
  refine ⟨c₁, c₂, c₃, hc₁, hc₂, hc₃, fun n hn => ?_⟩
  obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch n hn
  refine ⟨G, hsize, hunsat, ?_⟩
  -- Get the Tseitin extension from Frege simulation
  obtain ⟨ext, hext_size, hext_sparse, hext_agg, hext_res⟩ := h_sim G hunsat
  -- KConsistent preserved on extension
  have hkc_ext := er_kconsistent_from_aggregate G (n / c₁) ext hext_sparse hext_agg hkc
  -- BSW log form on extension:
  -- log₂(minRes_ext) * (c₃ · ext.cubes + 1) ≥ (n/c₁)²
  have h_bsw_ext := h_bsw ext.extended (n / c₁) hkc_ext ext.still_unsat
  -- From simulation: minRes_ext ≤ c₂ · S
  have h_res_le : minResolutionSize ext.extended ≤ c₂ * minFregeSize G := hext_res
  -- From size bound: ext.cubes ≤ |G| + c₂ · S
  have h_cubes_le : ext.extended.cubes.length ≤ G.cubes.length + c₂ * minFregeSize G :=
    hext_size
  -- log₂ is monotone: minRes_ext ≤ c₂·S → log₂(minRes_ext) ≤ log₂(c₂·S)
  have h_log_le : Nat.log2 (minResolutionSize ext.extended) ≤
                  Nat.log2 (c₂ * minFregeSize G) :=
    log2_mono h_res_le
  -- Second factor monotone: c₃ · ext.cubes + 1 ≤ c₃ · (|G| + c₂·S) + 1
  have h_rhs : c₃ * ext.extended.cubes.length + 1 ≤
               c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left c₃ h_cubes_le) 1
  -- Step 1: log₂(minRes) * (c₃·ext+1) ≤ log₂(minRes) * (c₃·(|G|+c₂S)+1)
  have step1 : Nat.log2 (minResolutionSize ext.extended) *
                 (c₃ * ext.extended.cubes.length + 1) ≤
               Nat.log2 (minResolutionSize ext.extended) *
                 (c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1) :=
    Nat.mul_le_mul_left _ h_rhs
  -- Step 2: log₂(minRes) * (...) ≤ log₂(c₂·S) * (...)
  have step2 : Nat.log2 (minResolutionSize ext.extended) *
                 (c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1) ≤
               Nat.log2 (c₂ * minFregeSize G) *
                 (c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1) :=
    Nat.mul_le_mul_right _ h_log_le
  -- Combine: (n/c₁)² ≤ log₂(minRes)*(c₃·ext+1)
  --          ≤ log₂(minRes)*(c₃·(|G|+c₂S)+1) ≤ log₂(c₂S)*(c₃·(|G|+c₂S)+1)
  exact Nat.le_trans (Nat.le_trans h_bsw_ext step1) step2

/-! ## Section 4a: Backward-compatible weak form -/

/-- **Frege bound (polynomial form)**: backward-compatible version using
    the polynomial BSW. This is the OLD `frege_near_quadratic` statement.
    Only implies S >= Omega(n) (linear), NOT super-linear.
    Kept for downstream compatibility.

    For the genuinely super-linear bound, use `frege_superlinear`. -/
theorem frege_near_quadratic :
    ∃ c₁ c₂ c₃ : Nat, c₁ ≥ 2 ∧ c₂ ≥ 1 ∧ c₃ ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        c₂ * minFregeSize G * (c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1) ≥
        (n / c₁) * (n / c₁) := by
  obtain ⟨c₁, hc₁, h_sch⟩ := schoenebeck_linear
  obtain ⟨c₂, hc₂, h_sim⟩ := frege_simulation
  obtain ⟨c₃, hc₃, h_bsw⟩ := bsw_with_formula_size
  refine ⟨c₁, c₂, c₃, hc₁, hc₂, hc₃, fun n hn => ?_⟩
  obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch n hn
  refine ⟨G, hsize, hunsat, ?_⟩
  obtain ⟨ext, hext_size, hext_sparse, hext_agg, hext_res⟩ := h_sim G hunsat
  have hkc_ext := er_kconsistent_from_aggregate G (n / c₁) ext hext_sparse hext_agg hkc
  have h_bsw_ext := h_bsw ext.extended (n / c₁) hkc_ext ext.still_unsat
  have h_res_le : minResolutionSize ext.extended ≤ c₂ * minFregeSize G := hext_res
  have h_cubes_le : ext.extended.cubes.length ≤ G.cubes.length + c₂ * minFregeSize G :=
    hext_size
  have h_rhs : c₃ * ext.extended.cubes.length + 1 ≤
               c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left c₃ h_cubes_le) 1
  have step1 : minResolutionSize ext.extended * (c₃ * ext.extended.cubes.length + 1) ≤
               minResolutionSize ext.extended * (c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1) :=
    Nat.mul_le_mul_left _ h_rhs
  have step2 : minResolutionSize ext.extended * (c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1) ≤
               c₂ * minFregeSize G * (c₃ * (G.cubes.length + c₂ * minFregeSize G) + 1) :=
    Nat.mul_le_mul_right _ h_res_le
  exact Nat.le_trans (Nat.le_trans h_bsw_ext step1) step2

/-! ## HONEST ACCOUNTING (post-audit 2026-03-23)

    STATUS: frege_superlinear and frege_near_quadratic are FORMALLY VALID
    (correct deduction from axioms, 0 sorry) but NOT SOUND because
    `frege_simulation` is not faithful to the Tseitin/Cook literature.

    The `frege_simulation` axiom claims h_sparse (≥7 gaps) and h_aggregate
    (fresh variable), but standard Tseitin produces:
    - 6 gaps (not 7) for padded 2-literal clause cubes
    - Extension variables in ≥2 cubes (not fresh)
    See: Q3-FREGE-SIMULATION.md, Q3b-TSEITIN-6GAP.md

    What IS sound in this file:
    - bsw_with_formula_size_log (correct BSW Cor. 3.6 encoding)
    - bsw_with_formula_size (derived theorem, backward compatible)
    - log2_le_self, log2_mono (pure math lemmas)

    What is NOT sound:
    - frege_superlinear (depends on unsound frege_simulation)
    - frege_near_quadratic (same dependency)

    To fix: need a non-standard Frege→ER simulation satisfying h_sparse + h_aggregate.
    This is an open research problem in proof complexity. -/

end CubeGraph
