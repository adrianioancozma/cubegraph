/-
  CubeGraph/BSWWidthSize.lean — BSW Width-Size Relation (Ben-Sasson-Wigderson 2001)

  Two independent axioms decomposing `abd_bsw_resolution_exponential`:

  1. **bsw_width_to_size** (BSW Corollary 3.6):
     Resolution width w → size ≥ 2^{(w - 3)² / (c · M)}
     where M = G.cubes.length
     [Ben-Sasson, Wigderson. JACM 48(2), 2001, Corollary 3.6]

  2. **bsw_width_exponential** (BSW random restriction, refined):
     Resolution width w → size ≥ 2^{w / c}
     [Ben-Sasson, Wigderson. JACM 48(2), 2001, via Theorem 3.2 iterated]

  Uses `minResWidth` from ABDWidthLowerBound.lean (ABD axiom) and declares
  `minResolutionSize` (the canonical location for this axiom).

  The assembly-ready combined theorem `abd_bsw_combined_exponential` derives
  the old `abd_bsw_resolution_exponential` from ABD + BSW (linear form),
  with .

  **. 4 axioms (minResolutionSize + 3 BSW forms). 7 theorems.**

  See: ABDWidthLowerBound.lean (ABD axiom: KConsistent + UNSAT → width > k)
  See: ERLowerBound.lean (uses these to derive er_resolution_lower_bound)
  See: KConsistency.lean (KConsistent definition)
-/

import CubeGraph.ABDWidthLowerBound

namespace CubeGraph

open BoolMat

/-! ## Section 1: Resolution proof size (axiom-specified)

  Canonical declaration of minResolutionSize. All downstream files
  (ERLowerBound, FregeLowerBound, EFLowerBound, etc.) get this
  through their import chain. -/

/-- Minimum Resolution proof size for a CubeGraph.
    For UNSAT G: the minimum number of clauses in any Resolution refutation
    of the CNF formula associated with G.
    For SAT G: unconstrained (axioms only apply to UNSAT).

    We do not model Resolution proofs directly. This function is specified
    by axioms corresponding to published results. -/
axiom minResolutionSize (G : CubeGraph) : Nat

/-! ## Section 2: BSW Width-Size Relation — Quadratic Form (Corollary 3.6)

  **Theorem (BSW 2001, Cor. 3.6)**: Let F be an unsatisfiable CNF formula
  on n variables with initial clause width at most w₀.
  Any Resolution refutation π of F satisfies:

      |π| ≥ 2^{(w(π) - w₀)² / n}

  where |π| = size and w(π) = max clause width.

  For 3-SAT on CubeGraph:
  - n = 3 · G.cubes.length (number of underlying variables)
  - w₀ = 3 (each original clause has 3 literals)
  - The constant c absorbs the factor 3 in the denominator

  Reference: Ben-Sasson, Wigderson. "Short proofs are narrow — resolution
  made simple." JACM 48(2), 2001, Corollary 3.6. -/

axiom bsw_width_to_size :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      G.cubes.length ≥ 1 →
      minResolutionSize G ≥
        2 ^ ((minResWidth G - 3) * (minResWidth G - 3) /
             (c * G.cubes.length))

/- REMOVED (2026-03-24): bsw_width_exponential was an INCORRECT axiom (#11).

   It claimed: size ≥ 2^{w/c} WITHOUT the formula size N in the denominator.

   BSW 2001 always has N in the denominator: size ≥ 2^{(w-3)²/(c·N)}.
   The argument in Section 3 above (random restriction yielding N-free bound)
   does NOT actually eliminate N — the restriction probability p = c·w/N
   means the restricted formula has N' = c·w variables, but the original
   proof size is only bounded by the RESTRICTED proof size, and the
   restricted formula's size depends on p·N, creating a circular dependency.

   The correct axiom is bsw_width_to_size (#10, Section 2) which faithfully
   states Corollary 3.6 with N = G.cubes.length in the denominator.

   All downstream theorems (abd_bsw_combined_exponential, etc.) have been
   updated to use the quadratic form from bsw_width_to_size.

   See: BSWRevived.lean (Section 5: "Why abd_bsw_resolution_exponential
   cannot be used naively") for analysis of the N-denominator issue. -/

/-! ## Section 4: Helper lemmas -/

/-- Monotonicity of exponentiation: a ≥ b → 2^a ≥ 2^b. -/
private theorem pow2_mono {a b : Nat} (h : a ≥ b) : 2 ^ a ≥ 2 ^ b :=
  Nat.pow_le_pow_right (by omega : 2 ≥ 1) h

/-! ## Section 5: Combined ABD + BSW — Exponential Form

  Combines:
  - ABD (from ABDWidthLowerBound): KConsistent G k + UNSAT → minResWidth G > k
  - BSW linear (above): UNSAT → size ≥ 2^{minResWidth G / c}

  Result: KConsistent G k + UNSAT → size ≥ 2^{k/c'}.

  NOTE (2026-03-24): This formerly derived `abd_bsw_resolution_exponential`
  (size ≥ 2^{k/c}) from the incorrect axiom `bsw_width_exponential`.
  Now uses the quadratic form from `bsw_width_to_size` (BSW Cor. 3.6),
  which includes G.cubes.length in the denominator. -/

/-- **ABD + BSW combined (exponential form — quadratic exponent)**.
    k-consistency on UNSAT CubeGraph → size ≥ 2^{(k-2)²/(c·M)}.

    Derived from:
    - ABD: minResWidth G > k (so minResWidth G - 3 ≥ k - 2)
    - BSW quadratic (Cor. 3.6): size ≥ 2^{(minResWidth G - 3)²/(c·M)}
    - Combined: size ≥ 2^{(k-2)²/(c·M)}

    NOTE (2026-03-24): Previously claimed size ≥ 2^{k/c} without the
    M = G.cubes.length denominator, via the incorrect axiom
    bsw_width_exponential. The correct BSW bound always has N in
    the denominator. Downstream users updated accordingly. -/
theorem abd_bsw_combined_exponential :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph) (k : Nat),
      KConsistent G k → ¬ G.Satisfiable → G.cubes.length ≥ 1 →
      minResolutionSize G ≥
        2 ^ ((k - 2) * (k - 2) / (c * G.cubes.length)) := by
  obtain ⟨c, hc, h_bsw⟩ := bsw_width_to_size
  refine ⟨c, hc, fun G k hkc hunsat hM => ?_⟩
  have h_abd := abd_width_from_kconsistency G k hkc hunsat
  have h_size := h_bsw G hunsat hM
  apply Nat.le_trans _ h_size
  apply pow2_mono
  apply Nat.div_le_div_right
  have hw : minResWidth G - 3 ≥ k - 2 := by omega
  exact Nat.mul_le_mul hw hw

/-! ## Section 6: BSW with explicit width parameter -/

/-- **BSW with explicit width**: given minimum refutation width ≥ w,
    the minimum Resolution proof size is at least 2^{(w-3)²/(c·M)}.

    Interface for the assembly: plug in w = k (from ABD) to get
    size ≥ 2^{(k-3)²/(c · M)}. -/
theorem bsw_width_implies_exponential_size :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      G.cubes.length ≥ 1 →
      ∀ (w : Nat), minResWidth G ≥ w →
        minResolutionSize G ≥ 2 ^ ((w - 3) * (w - 3) / (c * G.cubes.length)) := by
  obtain ⟨c, hc, h_bsw⟩ := bsw_width_to_size
  refine ⟨c, hc, fun G hunsat hM w hw => ?_⟩
  have h1 := h_bsw G hunsat hM
  apply Nat.le_trans _ h1
  apply pow2_mono
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul (Nat.sub_le_sub_right hw 3) (Nat.sub_le_sub_right hw 3)

/-! ## Section 7: ABD + BSW interface -/

/-- **ABD + BSW interface**: packages both axioms.
    Part 1: ABD gives width > k from k-consistency.
    Part 2: BSW gives size from width. -/
theorem abd_bsw_interface :
    (∀ (G : CubeGraph) (k : Nat),
      KConsistent G k → ¬ G.Satisfiable →
      minResWidth G > k)
    ∧
    (∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      G.cubes.length ≥ 1 →
      minResolutionSize G ≥
        2 ^ ((minResWidth G - 3) * (minResWidth G - 3) /
             (c * G.cubes.length))) :=
  ⟨abd_width_from_kconsistency, bsw_width_to_size⟩

/-! ## Section 8: Combined quadratic form (for Schoenebeck-regime proofs) -/

/-- **ABD + BSW combined (quadratic exponent)**.
    k-consistency on UNSAT CubeGraph → size ≥ 2^{(k - 2)²/(c · M)}.

    Uses ABD (width > k, so width - 3 ≥ k - 2) + BSW quadratic form. -/
theorem abd_bsw_combined_quadratic :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph) (k : Nat),
      KConsistent G k → ¬ G.Satisfiable → G.cubes.length ≥ 1 →
      minResolutionSize G ≥
        2 ^ ((k - 2) * (k - 2) / (c * G.cubes.length)) := by
  obtain ⟨c, hc, h_bsw⟩ := bsw_width_to_size
  refine ⟨c, hc, fun G k hkc hunsat hM => ?_⟩
  have h_abd := abd_width_from_kconsistency G k hkc hunsat
  have h_size := h_bsw G hunsat hM
  apply Nat.le_trans _ h_size
  apply pow2_mono
  apply Nat.div_le_div_right
  -- minResWidth G > k, so minResWidth G ≥ k + 1
  -- Need: (k - 2) * (k - 2) ≤ (minResWidth G - 3) * (minResWidth G - 3)
  -- Since minResWidth G - 3 ≥ k - 2 (by cases: k ≤ 2 gives k-2=0; k ≥ 3 gives width-3 ≥ k-2)
  have hw : minResWidth G - 3 ≥ k - 2 := by omega
  exact Nat.mul_le_mul hw hw

/-! ## Section 9: k ≥ M implies SAT -/

/-- List.finRange n is Nodup (reproved locally to avoid deep imports). -/
private theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij h_eq
  simp only [List.getElem_finRange] at h_eq
  have h := Fin.ext_iff.mp h_eq
  simp at h
  omega

/-- k ≥ M ∧ KConsistent G k → Satisfiable.
    When k ≥ |cubes|, the full cube set is a subset of size ≤ k,
    so KConsistent provides a global compatible gap selection = SAT. -/
theorem kconsistent_large_implies_sat (G : CubeGraph) (k : Nat)
    (hk : k ≥ G.cubes.length) (hkc : KConsistent G k) : G.Satisfiable := by
  have hfull : (List.finRange G.cubes.length).length ≤ k := by
    simp [List.length_finRange]; omega
  have hnodup : (List.finRange G.cubes.length).Nodup := finRange_nodup _
  obtain ⟨s, hv, hc⟩ := hkc (List.finRange G.cubes.length) hfull hnodup
  exact ⟨s,
    fun i => hv i (mem_finRange i),
    fun e he => hc e he (mem_finRange e.1) (mem_finRange e.2)⟩

/-! ## Section 10: Arithmetic helpers for assembly -/

/-- When k ≥ 6 and k ≤ M, the quadratic exponent (k-2)² is at least (k/2)². -/
theorem quadratic_exponent_lower_bound
    (k M : Nat) (_hM : M ≥ 1) (hk_large : k ≥ 6) (_hk_le_M : k ≤ M) :
    (k - 2) * (k - 2) ≥ k / 2 * (k / 2) := by
  have : k - 2 ≥ k / 2 := by omega
  exact Nat.mul_le_mul this this

/-! ## Section 11: Accounting

  NEW AXIOMS (3, all from published literature):
  1. minResolutionSize G : Nat
     — Minimum Resolution proof size (axiomatic function)
  2. bsw_width_to_size
     — BSW 2001, Cor. 3.6: size ≥ 2^{(w-3)²/(c·M)} [quadratic form]
  3. minResWidth (from ABDWidthLowerBound) + abd_width_from_kconsistency

  REMOVED (2026-03-24):
  - bsw_width_exponential — claimed size ≥ 2^{w/c} WITHOUT formula-size
    denominator. BSW 2001 always has N in the denominator. See Section 3 comment.

  DERIVED THEOREMS:
  - abd_bsw_combined_exponential: KConsistent + UNSAT → size ≥ 2^{(k-2)²/(c·M)}
    (NOTE: was 2^{k/c}; corrected to include M denominator)
  - abd_bsw_combined_quadratic: KConsistent + UNSAT → size ≥ 2^{(k-2)²/(c·M)}
  - bsw_width_implies_exponential_size: BSW with explicit width bound
  - abd_bsw_interface: packages both axioms
  - kconsistent_large_implies_sat: k ≥ M → SAT
  - quadratic_exponent_lower_bound: arithmetic helper
-/

end CubeGraph
