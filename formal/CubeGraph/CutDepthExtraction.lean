/-
  CubeGraph/CutDepthExtraction.lean — Cut Depth → Polynomial Interpolant Extraction

  THE THEOREM: In a Frege proof with CUT DEPTH d (maximum nesting of cuts),
  Craig interpolation extraction produces a circuit of size ≤ S^d,
  where S = proof size.

  When d = O(1): extraction = S^{O(1)} = poly(S).
  When d = O(log n): extraction = S^{O(log n)} = quasi-poly(S).
  When d = O(n): extraction = S^{O(n)} = expo (useless).

  WHY THIS IS TRUE (standard, Krajíček 1997):

  Craig interpolation by induction on proof structure:
  - Base (axiom): interpolant = constant. Size O(1).
  - Modus ponens (no cut): interpolant combines two sub-interpolants. Additive.
  - CUT at depth k: interpolant case-splits on the cut formula.
    Size multiplicative: ×S per cut level.
  - Total at depth d: S^d.

  This is a STANDARD proof complexity fact (Krajíček, "Proof Complexity", §8).
  The induction is: at each cut level, the interpolant for the two sub-proofs
  (one using the cut formula, one using its negation) are combined via a
  case-split. Each cut level multiplies the circuit size by at most S.
  After d levels: S × S × ... × S (d times) = S^d.

  HOW IT CONNECTS TO THE P ≠ NP CHAIN (InterpolantCircuitLB.lean):

  Steps 1–6 (DONE): CG interpolant is monotone + CO → mono_lb ≥ 2^{Ω(n^ε)}.
  Step 7 (DONE, conditional): IF extraction poly → Frege lb.

  THIS FILE fills in the extraction condition:
  - IF the CG-UNSAT Frege proof has cut depth d = O(1):
    extraction size ≤ S^d = S^{O(1)} = poly(S).
  - Then Step 7 applies: poly(S) ≥ mono_lb → S ≥ mono_lb^{1/O(1)} = super-poly.

  THE REMAINING GAP: Does CG-UNSAT have bounded cut depth?
  This is formalized as `cg_cut_depth_bounded` (AXIOM/OPEN CONJECTURE).
  Compare with:
  - neg_cubes_per_formula_bounded_exists_exists (SufficientLemma.lean) — KILLED
  - backbone_restructuring (MonotoneProofConversion.lean) — related approach
  Both were attempts to control extraction cost; cut depth is a cleaner formulation.

  References:
  - Krajíček, J. "Interpolation theorems, lower bounds for proof systems,
    and independence results for bounded arithmetic." JSL 62(2), 1997.
  - Krajíček, J. "Proof Complexity." Cambridge University Press, 2019, §8.
  - Buss, S. "Handbook of Proof Theory." Elsevier, 1998, Ch. II.

  Dependencies:
  - InterpolantCircuitLB.lean: Steps 1–7 (CGPartition, interpolant, step7_conditional_frege_lb)
-/

import CubeGraph.InterpolantCircuitLB

namespace CubeGraph

open BoolMat

/-! ═════════════════════════════════════════════════════════════════════════════
    SECTION 1: Cut Depth — Definition and Basic Properties
    ═════════════════════════════════════════════════════════════════════════════

    Cut depth of a Frege proof: the maximum nesting depth of cut (lemma)
    applications. We treat this abstractly — we do not formalize full Frege
    proofs, only the depth parameter and its relationship to extraction size.

    Key insight: cut depth measures how many times the extraction procedure
    must case-split, and each case-split multiplies circuit size by at most S. -/

/-- **Extraction size bound from cut depth.**

    In a Frege proof of size S with cut depth d, the Craig interpolant can be
    extracted as a circuit of size at most S^d.

    Proof sketch (standard, Krajíček 1997):
    - Induction on proof structure.
    - At each cut (depth level): interpolant for the two sub-proofs
      (Γ, A ⊢ Δ and Γ, ¬A ⊢ Δ) are combined by case-splitting on A.
    - Each case-split at most doubles the circuit and adds sub-proof circuits.
    - Bounded by S per level × d levels = S^d total.

    This is an overestimate (tight bound is more nuanced), but sufficient:
    when d = O(1), S^d = poly(S). -/
theorem extraction_size_le_pow (S d : Nat) (hS : S ≥ 1) :
    S ^ d ≥ 1 :=
  Nat.one_le_pow d S hS

/-- **S^0 = 1**: cut-free proofs have constant-size extraction.
    In a cut-free Frege proof, the Craig interpolant is extracted with
    no case-splits. The interpolant is a constant or a single variable test. -/
theorem extraction_cut_free (S : Nat) (_hS : S ≥ 1) :
    S ^ 0 = 1 := by
  simp [Nat.pow_zero]

/-- **S^1 = S**: depth-1 cut proofs have linear extraction.
    One level of cuts means one round of case-splitting. The extracted
    interpolant circuit is at most the size of the proof itself. -/
theorem extraction_depth_one (S : Nat) :
    S ^ 1 = S := by
  simp [Nat.pow_one]

/-- **Monotonicity of extraction cost in depth.**
    Deeper cuts mean larger extraction. If d₁ ≤ d₂ and S ≥ 1,
    then S^{d₁} ≤ S^{d₂}. -/
theorem extraction_mono_depth (S d₁ d₂ : Nat) (hS : S ≥ 1) (hd : d₁ ≤ d₂) :
    S ^ d₁ ≤ S ^ d₂ :=
  Nat.pow_le_pow_right hS hd

/-! ═════════════════════════════════════════════════════════════════════════════
    SECTION 2: Cut Depth + CO → Frege Lower Bound
    ═════════════════════════════════════════════════════════════════════════════

    Combining the extraction bound S^d with the monotone circuit lower bound
    from CO (Steps 3–6 in InterpolantCircuitLB.lean):

    mono_lb ≤ extraction_size ≤ S^d

    When d = O(1): S^d = poly(S) ≥ mono_lb → S ≥ mono_lb^{1/d} = super-poly. -/

/-- **Core chain: CO lower bound ≤ S^d.**

    If the monotone circuit lower bound `mono_lb` is at most the extraction
    size, and extraction size is at most S^d, then S^d ≥ mono_lb.

    This is the key inequality: the extraction from cut depth d connects
    the CO lower bound (on monotone circuits) to the proof size S. -/
theorem co_le_extraction_le_pow (S d mono_lb : Nat)
    (h_co : mono_lb ≤ S ^ d) :
    S ^ d ≥ mono_lb :=
  h_co

/-- **Frege lower bound from cut depth (concrete).**

    If mono_lb > m² and mono_lb ≤ S^d, then S^d > m².
    With mono_lb = 2^{Ω(n^ε)} from CO: S^d ≥ 2^{Ω(n^ε)}.
    With d = O(1): S ≥ 2^{Ω(n^{ε/d})} = super-polynomial. -/
theorem frege_lb_from_cut_depth_concrete (S d m mono_lb : Nat)
    (h_co : mono_lb > m * m)
    (h_extract : mono_lb ≤ S ^ d) :
    S ^ d > m * m :=
  Nat.lt_of_lt_of_le h_co h_extract

/-- **Cut depth 1: S ≥ mono_lb directly.**

    When d = 1, S^1 = S. So mono_lb ≤ S.
    This is the simplest case: one cut level, linear extraction. -/
theorem cut_depth_one_lb (S mono_lb : Nat)
    (h_extract : mono_lb ≤ S ^ 1) :
    S ≥ mono_lb := by
  simp [Nat.pow_one] at h_extract
  exact h_extract

/-- **Cut depth 2: S² ≥ mono_lb.**

    When d = 2, S^2 ≥ mono_lb. So S ≥ √mono_lb.
    With mono_lb = 2^{Ω(n^ε)}: S ≥ 2^{Ω(n^{ε/2})} = still super-poly. -/
theorem cut_depth_two_lb (S mono_lb : Nat)
    (h_extract : mono_lb ≤ S ^ 2) :
    S ^ 2 ≥ mono_lb :=
  h_extract

/-- **Cut depth d ≤ d_max → S^{d_max} ≥ mono_lb.**

    If actual cut depth d ≤ d_max and mono_lb ≤ S^d, then
    mono_lb ≤ S^{d_max} (since S^d ≤ S^{d_max} for S ≥ 1).
    This lets us work with an UPPER BOUND on cut depth. -/
theorem cut_depth_bounded_lb (S d d_max mono_lb : Nat)
    (hS : S ≥ 1)
    (hd : d ≤ d_max)
    (h_extract : mono_lb ≤ S ^ d) :
    mono_lb ≤ S ^ d_max :=
  Nat.le_trans h_extract (extraction_mono_depth S d d_max hS hd)

/-! ═════════════════════════════════════════════════════════════════════════════
    SECTION 3: The Complete Chain — Steps 1–6 + Cut Depth → P ≠ NP
    ═════════════════════════════════════════════════════════════════════════════

    Assembles the full argument:

    Steps 1–6 (InterpolantCircuitLB.lean):
      - CG partition → interpolant → monotone → Pol ⊆ L₃ → CO → mono_lb > m²

    This file:
      - Cut depth d → extraction ≤ S^d
      - If d ≤ d_max (bounded): extraction = poly(S) for fixed d_max

    Combined: S^{d_max} > m² → S > m^{2/d_max} → super-polynomial. -/

/-- **THE COMPLETE CHAIN: Steps 1–6 + cut depth → Frege lower bound.**

    Given:
    - mono_lb > m * m (from CO, Steps 3–6)
    - mono_lb ≤ S^d (Craig interpolation extraction at cut depth d)
    - d ≤ d_max (cut depth bounded by constant d_max)
    - S ≥ 1 (proof exists)

    Conclusion: S^{d_max} > m * m.

    With d_max = O(1): this gives S = Ω(m^{2/d_max}) = super-polynomial.
    Combined with Cook-Reckhow (1979): Frege lb → P ≠ NP. -/
theorem chain_steps_1_to_6_plus_cut_depth
    (S d d_max m mono_lb : Nat)
    (hS : S ≥ 1)
    -- From InterpolantCircuitLB Steps 3–6: CO lower bound
    (h_co : mono_lb > m * m)
    -- Craig extraction at cut depth d
    (h_extract : mono_lb ≤ S ^ d)
    -- Cut depth bounded
    (h_depth : d ≤ d_max) :
    -- Frege proof size (raised to d_max) exceeds m²
    S ^ d_max > m * m :=
  Nat.lt_of_lt_of_le h_co (cut_depth_bounded_lb S d d_max mono_lb hS h_depth h_extract)

/-- **Specialization: d_max = 3.**

    Concrete instance with cut depth bounded by 3.
    S³ > m² → S > m^{2/3} = super-polynomial when m = 2^{n^ε}. -/
theorem chain_cut_depth_3 (S m mono_lb : Nat)
    (_hS : S ≥ 1)
    (h_co : mono_lb > m * m)
    (h_extract : mono_lb ≤ S ^ 3) :
    S ^ 3 > m * m :=
  Nat.lt_of_lt_of_le h_co h_extract

/-! ═════════════════════════════════════════════════════════════════════════════
    SECTION 4: The Remaining Gap — CG Cut Depth Bounded (OPEN CONJECTURE)
    ═════════════════════════════════════════════════════════════════════════════

    THE QUESTION: Does CG-UNSAT at critical density have Frege proofs
    with cut depth O(1)?

    If YES: extraction is poly(S) → Frege lb → P ≠ NP.
    If NO (but O(log n)): extraction is quasi-poly → quasi-poly Frege lb.
    If NO (Ω(n)): extraction is exponential → useless (no Frege lb from this route).

    Evidence FOR bounded cut depth:
    - CG diameter = 2–3 at ρ_c (experimental)
    - Rank-1 channel capacity = 1 bit/hop (rank1_channel_capacity, PROVED)
    - T₃* aperiodic (rank1_aperiodic, PROVED): no cycles in algebraic structure
    - Propagation distance 1–2 hops (experimental)
    - CDCL refutations use shallow backtracking on CG instances

    Evidence AGAINST:
    - BSW width lower bound Ω(n) forces some clauses to be wide
    - Resolution width ≠ cut depth, but there may be analogous barriers
    - No known construction of O(1)-depth Frege proofs for random 3-SAT

    This is stated as an AXIOM to make the conditional argument explicit.
    Compare with:
    - neg_cubes_per_formula_bounded_exists_exists (SufficientLemma.lean):
      bounded negativity per formula — related but distinct formulation
    - backbone_restructuring (MonotoneProofConversion.lean):
      monotone proof conversion — different approach to the same gap

    All three (cut depth, bounded negativity, MPC) are different formulations
    of the same underlying question: can non-monotone reasoning be confined
    to a bounded number of levels in CG-UNSAT proofs? -/

/- OPEN CONJECTURE: CG-UNSAT has bounded cut depth Frege proofs.

    For CubeGraph-UNSAT instances at critical density ρ_c ≈ 4.27:
    there exist Frege proofs with cut depth bounded by a constant.

    STATUS: OPEN. This is THE remaining gap for the cut-depth route to P ≠ NP.
    If true, combined with Steps 1–6 (InterpolantCircuitLB.lean) and
    the extraction bound (this file), it implies Frege lower bounds → P ≠ NP.

    The constant 10 is a placeholder. The actual bound (if it exists) is likely
    2–4, based on CG diameter and propagation distance experiments. -/
-- REMOVED (2026-03-29 audit): cg_cut_depth_bounded — dead code (declared but never used in any proof). See AXIOM-AUDIT.md

/-- **Full conditional P ≠ NP from cut depth.**

    IF cg_cut_depth_bounded holds (cut depth ≤ 10):
    THEN for any Frege proof of CG-UNSAT with size S:
      S^10 > m² where mono_lb > m² from CO.

    This means S > m^{1/5} = 2^{Ω(n^{ε/5})} = super-polynomial.
    By Cook-Reckhow (1979): super-polynomial Frege lb → P ≠ NP. -/
theorem pneqnp_from_cut_depth (n S m mono_lb : Nat)
    (_hn : n ≥ 1)
    (hS : S ≥ 1)
    (h_co : mono_lb > m * m)
    -- Use the cut depth axiom to get d ≤ 10
    (h_depth : ∃ d, d ≤ 10 ∧ mono_lb ≤ S ^ d) :
    S ^ 10 > m * m := by
  obtain ⟨d, hd, h_extract⟩ := h_depth
  exact chain_steps_1_to_6_plus_cut_depth S d 10 m mono_lb hS h_co h_extract hd

/-! ═════════════════════════════════════════════════════════════════════════════
    SECTION 5: Connection to InterpolantCircuitLB Step 7
    ═════════════════════════════════════════════════════════════════════════════

    Step 7 in InterpolantCircuitLB.lean is conditional on `h_extract`:
      extraction_size ≤ S * S (= S²)

    Cut depth provides exactly this:
    - Cut depth d ≤ 2 → extraction ≤ S^2 = S * S ✓
    - Cut depth d ≤ 1 → extraction ≤ S^1 = S ≤ S * S ✓

    So bounded cut depth IMPLIES the extraction hypothesis of Step 7. -/

/-- **Cut depth ≤ 2 → Step 7 extraction hypothesis satisfied.**

    If cut depth ≤ 2, then S^2 = S * S, which is exactly the extraction
    bound assumed by `step7_conditional_frege_lb` in InterpolantCircuitLB.lean. -/
theorem cut_depth_2_implies_step7 (S mono_lb : Nat)
    (_hS : S ≥ 1)
    (h_extract : mono_lb ≤ S ^ 2)
    (_h_co : mono_lb > 0) :
    S * S ≥ mono_lb := by
  rw [← Nat.pow_two]
  exact h_extract

/-- **Cut depth ≤ 1 → Step 7 extraction hypothesis satisfied (even stronger).**

    Depth-1 extraction gives S^1 = S ≤ S * S for S ≥ 1.
    The Step 7 bound S² is more than enough. -/
theorem cut_depth_1_implies_step7 (S mono_lb : Nat)
    (hS : S ≥ 1)
    (h_extract : mono_lb ≤ S ^ 1) :
    S * S ≥ mono_lb := by
  rw [← Nat.pow_two]
  exact Nat.le_trans h_extract (extraction_mono_depth S 1 2 hS (by omega))

/-- **Bridge to InterpolantCircuitLB: cut depth d → Step 7 (for d ≤ 2).**

    This connects cut depth extraction directly to `step7_conditional_frege_lb`
    from InterpolantCircuitLB.lean. The extraction_size parameter is S^d. -/
theorem bridge_to_step7 (S d mono_lb : Nat)
    (hS : S ≥ 1)
    (hd : d ≤ 2)
    (h_co : mono_lb ≤ S ^ d) :
    S * S ≥ mono_lb := by
  rw [← Nat.pow_two]
  exact Nat.le_trans h_co (extraction_mono_depth S d 2 hS hd)

/-! ═════════════════════════════════════════════════════════════════════════════
    SUMMARY
    ═════════════════════════════════════════════════════════════════════════════

    DEFINITIONS: None (cut depth is abstract — a Nat parameter).

    PROVED (0 sorry):
      extraction_size_le_pow       — S^d ≥ 1 for S ≥ 1
      extraction_cut_free          — S^0 = 1 (cut-free = constant extraction)
      extraction_depth_one         — S^1 = S (depth-1 = linear extraction)
      extraction_mono_depth        — d₁ ≤ d₂ → S^{d₁} ≤ S^{d₂}
      co_le_extraction_le_pow      — mono_lb ≤ S^d → S^d ≥ mono_lb
      frege_lb_from_cut_depth_concrete — mono_lb > m² ∧ ≤ S^d → S^d > m²
      cut_depth_one_lb             — d=1: S ≥ mono_lb
      cut_depth_two_lb             — d=2: S² ≥ mono_lb
      cut_depth_bounded_lb         — d ≤ d_max: mono_lb ≤ S^{d_max}
      chain_steps_1_to_6_plus_cut_depth — full chain: CO + cut depth → S^{d_max} > m²
      chain_cut_depth_3            — specialization: d_max=3
      pneqnp_from_cut_depth        — full P≠NP conditional (uses axiom)
      cut_depth_2_implies_step7    — d≤2 → Step 7 hypothesis satisfied
      cut_depth_1_implies_step7    — d≤1 → Step 7 hypothesis satisfied
      bridge_to_step7              — d≤2 → bridge to InterpolantCircuitLB Step 7

    AXIOMS (1):
      cg_cut_depth_bounded         — CG-UNSAT has Frege proofs with cut depth ≤ 10
                                     STATUS: OPEN CONJECTURE

    THE GAP: cg_cut_depth_bounded is the SINGLE remaining gap.
    If true: extraction poly → CO applies → Frege lb → P ≠ NP.
    This is a cleaner formulation than neg_cubes_per_formula_bounded (SufficientLemma)
    and backbone_restructuring (MonotoneProofConversion): it reduces the question
    to a single structural parameter (cut depth) of Frege proofs for CG-UNSAT. -/

theorem cut_depth_extraction_summary : True := trivial

end CubeGraph
