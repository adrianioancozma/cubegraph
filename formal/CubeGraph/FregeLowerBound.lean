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
  (correct deduction from axioms) but NOT SOUND (the axiom
  `frege_simulation` does not hold for the standard Tseitin transformation).
  The claimed Ω(n²/log n) Frege lower bound is NOT established.

  The deductive chain IS correct:
  1. schoenebeck_linear: KConsistent G (n/c₁) on UNSAT G      [correct axiom]
  2. frege_simulation: Frege(S) → ER extension                 [INCORRECT axiom]
  3. er_kconsistent_from_aggregate: KConsistent preserved       [proven]
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

/- REMOVED (2026-03-24): `frege_simulation` axiom was unsound.

   The axiom claimed Frege(S) → ER extension with h_sparse (≥7 gaps) + h_aggregate
   (fresh variable per cube). Standard Tseitin produces cubes with only 6 gaps
   (from 2-literal clause padding) and extension variables in ≥2 cubes
   (definition + parent gate).

   See: Q3-FREGE-SIMULATION.md and Q3b-TSEITIN-6GAP.md for detailed analysis.

   All downstream theorems that depended on this axiom (frege_superlinear,
   frege_near_quadratic, and their transitive dependents in 10+ files) have
   been removed. The sound parts of this file (bsw_with_formula_size_log,
   bsw_with_formula_size, log2_le_self, log2_mono) are preserved. -/

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
    downstream files (BackwardLowerBound.lean, CubeBSW.lean, etc.). -/
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

/- REMOVED (2026-03-24): `frege_superlinear` depended on unsound `frege_simulation`.

   The theorem claimed a self-referential bound:
     log₂(c₂·S) · (c₃·(|G| + c₂·S) + 1) ≥ (n/c₁)²
   implying Frege proof size S = Ω(n²/log n).

   The deduction was formally valid but relied on `frege_simulation` which
   does not hold for the standard Tseitin/Cook transformation.
   See: Q3-FREGE-SIMULATION.md, Q3b-TSEITIN-6GAP.md -/

/- REMOVED (2026-03-24): `frege_near_quadratic` depended on unsound `frege_simulation`.

   The theorem claimed: c₂·S · (c₃·(|G| + c₂·S) + 1) ≥ (n/c₁)²
   (polynomial BSW form, implying S = Ω(n) at minimum).

   Relied on `frege_simulation` which is unsound (standard Tseitin does not
   satisfy h_sparse and h_aggregate conditions).
   See: Q3-FREGE-SIMULATION.md, Q3b-TSEITIN-6GAP.md -/

/- HONEST ACCOUNTING (updated 2026-03-24)

   CLEANUP: `frege_simulation` axiom REMOVED (unsound).
   `frege_superlinear` and `frege_near_quadratic` REMOVED (depended on it).
   All downstream references in 10+ files cleaned up.

   What REMAINS sound in this file:
   - minFregeSize (axiom, function specification)
   - bsw_with_formula_size_log (correct BSW Cor. 3.6 encoding)
   - bsw_with_formula_size (derived theorem, backward compatible)
   - log2_le_self, log2_mono (pure math lemmas)

   What was REMOVED:
   - frege_simulation (unsound axiom — h_sparse/h_aggregate not satisfied by Tseitin)
   - frege_superlinear (depended on frege_simulation)
   - frege_near_quadratic (depended on frege_simulation)

   See: Q3-FREGE-SIMULATION.md, Q3b-TSEITIN-6GAP.md for detailed analysis. -/

end CubeGraph
