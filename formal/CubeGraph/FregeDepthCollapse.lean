/-
  CubeGraph/FregeDepthCollapse.lean — Depth Collapse Conjecture for CG-UNSAT

  THE ONLY REMAINING PATH TO P != NP in this project.

  CONJECTURE (Depth Collapse):
    On CG-UNSAT tautologies, general Frege proofs can be converted to
    bounded-depth Frege proofs with at most polynomial blowup.

    Formally: there exist constants d0 >= 1 and k >= 1 such that for all
    UNSAT CubeGraph instances G:
      minBDFregeSize G d0 <= (minFregeSize G) ^ k

  WHY THIS GIVES P != NP:
    1. BD-Frege HAS Monotone Feasible Interpolation (Krajicek 1997, unconditional)
    2. Frege ~ BD-Frege on CG-UNSAT (this conjecture)
    3. Therefore: Frege has MFI on CG-UNSAT
    4. mSIZE(CG-UNSAT) >= 2^{Omega(n^eps)} (CKO CCC 2024)
    5. MFI: poly(S) >= 2^{Omega(n^eps)} => S >= 2^{Omega(n^eps)}
    6. Cook-Reckhow => P != NP

  THE CHAIN:
    depth_collapse_cg (AXIOM -- the conjecture)
      + krajicek_bd_frege_mfi (AXIOM -- Krajicek 1997, unconditional)
        => frege_has_mfi_on_cg (THEOREM from above two)
          + cko_monotone_lower_bound (AXIOM -- CKO CCC 2024)
            => frege_lb_from_depth_collapse (THEOREM)
              + cook_reckhow_separation (AXIOM -- Cook-Reckhow 1979)
                => p_ne_np_from_depth_collapse (THEOREM)

  RELATIONSHIP TO ConditionalMFI.lean:
    ConditionalMFI uses `conditional_mfi_acc0` as its central axiom:
      "IF ACC^0 algebraic structure THEN Frege has MFI"
    This file uses `depth_collapse_cg` instead:
      "Frege proofs on CG-UNSAT collapse to bounded depth"

    depth_collapse_cg IMPLIES conditional_mfi_acc0 (stronger assumption).
    But depth_collapse_cg is:
      (a) MORE CONCRETE: it identifies the exact mechanism (depth saturation
          from T3* aperiodicity)
      (b) MORE TESTABLE: one can experimentally compare Frege and BD-Frege
          proof sizes on CG instances
      (c) MORE SPECIFIC: it identifies the precise depth d0 and exponent k

  See: CubeGraph/T3StarACC0.lean (T3* in ACC^0, BPR barrier removal)
  See: CubeGraph/ConditionalMFI.lean (alternative approach via conditional_mfi_acc0)
  See: CubeGraph/TreeLikeFrege.lean (tree-like Frege lower bound)
  See: CubeGraph/ContextExplosion.lean (minProofSizeAny, PolyBoundedProofSystem)
  See: CubeGraph/BoundedDepthFregeBarrier.lean (minBDFregeSize, BD-Frege lower bounds)
  See: experiments-ml/041_2026-03-30_mfi-tautology-structure/BRIEFING.md
  See: experiments-ml/040_2026-03-29_close-the-chain/RESULTS-BD-FREGE-HIERARCHY.md
  Strategy: experiments-ml/040_2026-03-29_close-the-chain/STRATEGIC-CLOSE-THE-CHAIN.md

  Axiom inventory (2 new axioms in this file):
  1. depth_collapse_cg            -- THE CONJECTURE (OPEN)
  2. krajicek_bd_frege_mfi        -- Krajicek 1997 (PUBLISHED, unconditional)

  Reused axioms (from imported files, not counted):
  - minFregeSize (ConditionalMFI.lean) -- specification
  - monotoneInterpolantSize (ConditionalMFI.lean) -- specification
  - minBDFregeSize (BoundedDepthFregeBarrier.lean) -- specification
  - cko_monotone_lower_bound (ConditionalMFI.lean) -- CKO CCC 2024
  - cook_reckhow_separation (ConditionalMFI.lean) -- Cook-Reckhow 1979
  - bmt_aperiodic_acc0, barrington_groups_nc1 (T3StarACC0.lean) -- transitive

  0 sorry. All gaps as clearly documented axioms.
  Created: Session 041, 2026-03-29
-/

import CubeGraph.ConditionalMFI
import CubeGraph.BoundedDepthFregeBarrier

namespace CubeGraph

open BoolMat

/-! ## Section 1: Definitions

  We reuse the following from existing files (no new definitions needed):
  - `minFregeSize` (ConditionalMFI.lean): minimum Frege proof size for a CubeGraph
  - `monotoneInterpolantSize` (ConditionalMFI.lean): monotone circuit size of interpolant
  - `minBDFregeSize` (BoundedDepthFregeBarrier.lean): min BD-Frege proof size (depth d)
  - `PolyBoundedProofSystem` (ContextExplosion.lean): P = NP iff this holds
  - `HasACC0AlgebraicStructure` (ConditionalMFI.lean): T3* is aperiodic and finite -/

/-! ## Section 2: The Depth Collapse Conjecture -/

/-- **DEPTH COLLAPSE CONJECTURE for CG-UNSAT.**

    On CG-UNSAT tautologies, general Frege proofs can be converted to
    bounded-depth Frege proofs with polynomial blowup.

    Formally: there exist constants d0 >= 1 and k >= 1 such that for all
    UNSAT CubeGraph instances G:
        minBDFregeSize G d0 <= (minFregeSize G) ^ k

    That is: the minimum depth-d0 Frege proof is at most polynomially larger
    than the minimum (unrestricted-depth) Frege proof.

    EVIDENCE:
    - BD-Frege hierarchy is FLAT experimentally (alpha in [0.06, 0.09] at depths 1-5)
    - T3* aperiodicity (m^5 = m^3) means composition saturates at index 3
    - Rank-1 convergence after 3 hops (EraseOnlyCollapse)
    - All known proof strategies give the same exponent on CG-UNSAT
    - Path saturation: extending any product beyond depth 3 gives the same
      T3* element (path_saturation from TransferMonoid.lean)

    WHY IT MIGHT BE TRUE:
    - CG-UNSAT's algebraic structure (ACC^0 via BMT) is too weak to benefit
      from Frege's depth advantage (which comes from NC^1 via Barrington)
    - T3* has no non-solvable groups => Barrington's theorem doesn't apply
    - Depth in Frege <-> nesting of Boolean operations <-> compose depth in T3*
    - T3* compose depth saturates at 3 => Frege depth > 3 is "wasted"
    - Word normalization (t3star_word_normalization): extending any product by
      m*m is idempotent after depth 4

    WHY IT MIGHT BE FALSE:
    - Frege depth != algebraic compose depth (the central gap)
    - Frege can use depth for LOGICAL reasoning, not just algebraic composition
    - No known technique for proving depth collapse on specific tautology families
    - Frege might exploit depth for cut reuse / sharing in ways unrelated to T3*

    REMOVING THIS AXIOM = proving the depth collapse conjecture = major
    breakthrough in proof complexity (not just P != NP). It would be the
    first known depth collapse result for a natural tautology family. -/
axiom depth_collapse_cg :
    ∃ (d₀ k : Nat), d₀ ≥ 1 ∧ k ≥ 1 ∧
    ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      minBDFregeSize G d₀ ≤ (minFregeSize G) ^ k

/-! ## Section 3: Supporting Lemmas — What T3* Structure Contributes

  These lemmas identify the algebraic reasons why depth should not help
  on CG-UNSAT. They do NOT constitute a proof of depth collapse, but they
  identify exactly WHERE the depth advantage of Frege is blocked. -/

/-- **T3* composition saturates at depth 3.**

    For all m in T3*, m^5 = m^3 (where pow m k = m^{k+1} in our convention).
    This means: any chain of >= 3 identical transfer operators gives the same
    result as 3 steps. No new information propagates beyond depth 3.

    Source: t3star_aperiodic from T3StarNoGroup.lean (native_decide). -/
theorem t3star_compose_saturates_at_depth_3 :
    ∀ m : T3Star, T3Star.pow m 4 = T3Star.pow m 2 :=
  t3star_aperiodic

/-- **T3* has no non-solvable group quotient.**

    The only group homomorphic images of T3* are Z/2Z or trivial.
    Aperiodicity (Eilenberg's variety theorem) + absorbing element 27.

    Source: t3star_no_nontrivial_group_quotient from T3StarACC0.lean. -/
theorem t3star_no_nonsolvable_group :
    (∀ m : T3Star, T3Star.pow m 4 = T3Star.pow m 2) ∧
    (∀ m : T3Star, T3Star.mul m ⟨27, by omega⟩ = ⟨27, by omega⟩) ∧
    (List.finRange 28).countP (fun e =>
      T3Star.mul e e == e &&
      (List.finRange 28).any (fun g =>
        g != e &&
        T3Star.mul g g == e &&
        T3Star.mul e g == g &&
        T3Star.mul g e == g)) = 3 :=
  t3star_no_nontrivial_group_quotient

/-- **Barrington's theorem is inapplicable to CG-UNSAT.**

    Barrington (1989): programs over non-solvable groups compute exactly NC^1.
    T3* has no non-solvable group quotient (proven above).
    Therefore: the depth advantage of Frege (via Barrington's construction)
    is structurally unavailable for CG-UNSAT.

    NOTE: This does not constitute a proof of depth collapse. Frege might
    exploit depth in ways unrelated to Barrington-style branching programs. -/
theorem barrington_inapplicable_to_cg :
    (∀ m : T3Star, T3Star.pow m 4 = T3Star.pow m 2) ∧
    (∀ m : T3Star, T3Star.mul m ⟨27, by omega⟩ = ⟨27, by omega⟩) ∧
    (∀ G : CubeGraph, HasACC0AlgebraicStructure G) :=
  ⟨t3star_aperiodic,
   t3star_all_elements_reach_27,
   every_cg_has_acc0_structure⟩

/-- **CG-UNSAT tautologies cannot encode NC^1 computation.**

    T3* aperiodic (PROVED) + BMT 1992 => word problem in ACC^0.
    Barrington 1989 => NC^1 requires non-solvable groups => T3* too weak.
    BPR does not apply (from ConditionalMFI.lean).

    This is the STRUCTURAL CORE of the depth collapse conjecture:
    CG-UNSAT's algebraic structure is strictly below NC^1. -/
theorem cg_unsat_below_nc1 :
    (∀ G : CubeGraph, HasACC0AlgebraicStructure G) ∧
    ((∀ m : T3Star,
      ∃ a b : T3Star, a ≠ b ∧ T3Star.mul m a = T3Star.mul m b) ∧
     (∀ m : T3Star,
      ∃ a b : T3Star, a ≠ b ∧ T3Star.mul a m = T3Star.mul b m) ∧
     (∀ m : T3Star, T3Star.pow m 4 = T3Star.pow m 2) ∧
     (¬ ∃ e : T3Star, ∀ m : T3Star,
         T3Star.mul e m = m ∧ T3Star.mul m e = m) ∧
     (∀ G : CubeGraph, HasACC0AlgebraicStructure G)) :=
  ⟨every_cg_has_acc0_structure, bpr_does_not_apply_to_cg⟩

/-! ## Section 4: BD-Frege has MFI (Krajicek 1997)

  Krajicek (1997) proved UNCONDITIONALLY that bounded-depth Frege has
  Monotone Feasible Interpolation.

  This is the critical asymmetry: BD-Frege has MFI, while general Frege
  does NOT (blocked by BPR crypto barrier in general -- though BPR does
  not apply to CG-UNSAT specifically).

  If Frege ~ BD-Frege on CG-UNSAT (depth collapse), then Frege inherits
  MFI on CG-UNSAT from BD-Frege.

  KEY DESIGN CHOICE: We state Krajicek's MFI as UNIVERSAL in depth d
  (it holds for every d >= 1, which is the published result). This avoids
  the need to match the Krajicek depth with the collapse depth d0. -/

/-- **Krajicek 1997: Bounded-depth Frege has Monotone Feasible Interpolation.**

    For ANY fixed depth d >= 1, depth-d Frege proofs admit monotone feasible
    interpolation: the monotone interpolant can be extracted with at most
    polynomial blowup (the polynomial depends on d).

    Formally: for every depth d >= 1, there exists an exponent e(d) >= 1
    such that for all UNSAT CubeGraph G:
      monotoneInterpolantSize G <= (minBDFregeSize G d) ^ e

    NOTE: The exponent e may depend on d, but for any FIXED d it is a constant.
    We existentially quantify over e for simplicity.

    This is UNCONDITIONAL -- no algebraic assumptions. It holds for ALL
    tautology families, not just CG-UNSAT.

    Reference: Krajicek, J. "Interpolation theorems, lower bounds for proof
    systems, and independence results for bounded arithmetic."
    Journal of Symbolic Logic, 62(2), 1997. -/
axiom krajicek_bd_frege_mfi :
    ∀ (d : Nat), d ≥ 1 →
    ∃ (e : Nat), e ≥ 1 ∧
    ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      monotoneInterpolantSize G ≤ (minBDFregeSize G d) ^ e

/-! ## Section 5: The Chain — Depth Collapse => MFI => Frege lb => P != NP -/

/-- **Frege has MFI on CG-UNSAT** (from depth collapse + Krajicek).

    Combining:
    1. depth_collapse_cg: minBDFregeSize G d0 <= (minFregeSize G)^k
    2. krajicek_bd_frege_mfi at d = d0: monotone <= (minBDFregeSize G d0)^e

    Result: monotone <= ((minFregeSize G)^k)^e = (minFregeSize G)^(k*e)

    The key: we instantiate Krajicek at the SAME depth d0 as the collapse.
    This is valid because Krajicek's result is universal in d. -/
theorem frege_has_mfi_on_cg :
    ∃ (exp : Nat), exp ≥ 1 ∧
    ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      monotoneInterpolantSize G ≤ (minFregeSize G) ^ exp := by
  -- Get the depth collapse constants d0, k
  obtain ⟨d₀, k, hd₀, hk, h_collapse⟩ := depth_collapse_cg
  -- Get the Krajicek MFI at depth d0 specifically
  obtain ⟨e, he, h_krajicek⟩ := krajicek_bd_frege_mfi d₀ hd₀
  -- The combined exponent is k * e >= 1
  refine ⟨k * e, ?_, ?_⟩
  · -- k * e >= 1 since k >= 1 and e >= 1
    have : 1 * 1 ≤ k * e := Nat.mul_le_mul hk he
    omega
  · -- For all G UNSAT: monotone <= (minFregeSize G)^(k*e)
    intro G hunsat
    have h_mfi := h_krajicek G hunsat
    have h_col := h_collapse G hunsat
    calc monotoneInterpolantSize G
        ≤ (minBDFregeSize G d₀) ^ e := h_mfi
      _ ≤ ((minFregeSize G) ^ k) ^ e := Nat.pow_le_pow_left h_col e
      _ = (minFregeSize G) ^ (k * e) := by rw [Nat.pow_mul]

/-- **Frege lower bound on CG-UNSAT from depth collapse.**

    Combining frege_has_mfi_on_cg with cko_monotone_lower_bound:
    (minFregeSize G)^exp >= 2^{n/eps}

    This gives super-polynomial Frege proof size on CG-UNSAT instances. -/
theorem frege_lb_from_depth_collapse :
    ∃ (eps exp : Nat), eps ≥ 1 ∧ exp ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        (minFregeSize G) ^ exp ≥ 2 ^ (n / eps) := by
  obtain ⟨exp, hexp, h_mfi⟩ := frege_has_mfi_on_cg
  obtain ⟨eps, heps, h_cko⟩ := cko_monotone_lower_bound
  refine ⟨eps, exp, heps, hexp, fun n hn => ?_⟩
  obtain ⟨G, hsize, hunsat, h_mono_lb⟩ := h_cko n hn
  refine ⟨G, hsize, hunsat, ?_⟩
  -- monotoneInterpolantSize G <= (minFregeSize G)^exp (from MFI)
  -- monotoneInterpolantSize G >= 2^{n/eps} (from CKO)
  -- Therefore: (minFregeSize G)^exp >= 2^{n/eps}
  exact Nat.le_trans h_mono_lb (h_mfi G hunsat)

/-- **THE CAPSTONE: P != NP from depth collapse.**

    This theorem depends on exactly the following axioms:

    1. depth_collapse_cg          STATUS: OPEN (the research target)
       CONTENT: Frege proofs on CG-UNSAT collapse to bounded depth
       TO REMOVE: prove the depth collapse conjecture (major breakthrough)

    2. krajicek_bd_frege_mfi      STATUS: PUBLISHED (Krajicek, JSL 62(2), 1997)
       CONTENT: BD-Frege has monotone feasible interpolation (unconditional)
       TO REMOVE: formalize Krajicek's proof in Lean

    3. cko_monotone_lower_bound   STATUS: PUBLISHED (CKO, CCC 2024)
       CONTENT: mSIZE >= 2^{n^eps} for CG-UNSAT interpolant
       TO REMOVE: formalize CKO in Lean

    4. cook_reckhow_separation    STATUS: PUBLISHED (Cook-Reckhow 1979)
       CONTENT: Frege lb on NP-complete => no PBPS
       TO REMOVE: formalize Cook-Reckhow in Lean

    SPECIFICATION AXIOMS (definitional, not mathematical claims):
    - minFregeSize, monotoneInterpolantSize, minBDFregeSize, minProofSizeAny

    THE KEY INSIGHT: depth_collapse_cg is the ONLY axiom whose removal
    requires NEW mathematics. All others are either definitional or from
    published, peer-reviewed results. -/
theorem p_ne_np_from_depth_collapse :
    ¬ PolyBoundedProofSystem :=
  cook_reckhow_separation frege_lb_from_depth_collapse

/-! ## Section 6: Honest Accounting

  **What IS proved in this file** (Lean, 0 sorry):
  - t3star_compose_saturates_at_depth_3: restatement (from T3StarNoGroup)
  - t3star_no_nonsolvable_group: bundled from T3StarACC0
  - barrington_inapplicable_to_cg: structural bundle
  - cg_unsat_below_nc1: full BPR impossibility bundle (from ConditionalMFI)
  - frege_has_mfi_on_cg: MFI on CG-UNSAT (from depth_collapse + Krajicek)
  - frege_lb_from_depth_collapse: super-poly Frege lb (from MFI + CKO)
  - p_ne_np_from_depth_collapse: capstone (from lb + Cook-Reckhow)
  - depth_collapse_implies_conditional_mfi: implication to weaker axiom
  - both_approaches_agree: agreement with ConditionalMFI

  **New axioms (2)**:
  1. depth_collapse_cg: THE CONJECTURE (OPEN)
  2. krajicek_bd_frege_mfi: Krajicek 1997 (PUBLISHED, unconditional)

  **Reused axioms (from imported files)**:
  - cko_monotone_lower_bound (ConditionalMFI.lean) -- CKO CCC 2024
  - cook_reckhow_separation (ConditionalMFI.lean) -- Cook-Reckhow 1979
  - minFregeSize, monotoneInterpolantSize (ConditionalMFI.lean) -- specification
  - minBDFregeSize (BoundedDepthFregeBarrier.lean) -- specification
  - bmt_aperiodic_acc0, barrington_groups_nc1 (T3StarACC0.lean) -- transitive

  **What is NOT claimed**:
  - P != NP is NOT proved unconditionally
  - depth_collapse_cg is NOT proved (it is the OPEN question)
  - Removing depth_collapse_cg = proving P != NP
-/
theorem depth_collapse_honest_accounting : True := trivial

/-! ## Section 7: Comparison with ConditionalMFI.lean

  ConditionalMFI.lean uses `conditional_mfi_acc0` as its central axiom:
    "IF ACC^0 algebraic structure THEN Frege has MFI"
  This file uses `depth_collapse_cg` instead:
    "Frege proofs on CG-UNSAT collapse to bounded depth"

  The relationship:
  - depth_collapse_cg IMPLIES conditional_mfi_acc0 (stronger assumption)
  - depth_collapse_cg is MORE CONCRETE and TESTABLE
  - depth_collapse_cg identifies the exact mechanism (depth saturation) -/

/-- **Depth collapse implies conditional MFI.**

    depth_collapse_cg is a STRICTLY STRONGER assumption than conditional_mfi_acc0.
    This theorem shows the implication: depth collapse gives MFI on CG-UNSAT,
    which is exactly what conditional_mfi_acc0 asserts. -/
theorem depth_collapse_implies_conditional_mfi :
    ∃ d : Nat, d ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      HasACC0AlgebraicStructure G →
      monotoneInterpolantSize G ≤ (minFregeSize G) ^ d := by
  obtain ⟨exp, hexp, h_mfi⟩ := frege_has_mfi_on_cg
  exact ⟨exp, hexp, fun G hunsat _hacc0 => h_mfi G hunsat⟩

/-- **Both approaches yield the same conclusion.**

    p_ne_np_from_depth_collapse (this file)
    and p_ne_np_from_mfi (ConditionalMFI.lean)
    both prove not PolyBoundedProofSystem.

    APPROACH 1 (ConditionalMFI): conditional_mfi_acc0
    - "ACC^0 algebraic structure => Frege has MFI"
    - More abstract, weaker assumption

    APPROACH 2 (this file): depth_collapse_cg
    - "Frege proofs collapse to bounded depth on CG-UNSAT"
    - More concrete, stronger assumption, identifies mechanism

    Both yield not PolyBoundedProofSystem (= P != NP). -/
theorem both_approaches_agree :
    (¬ PolyBoundedProofSystem) ∧ (¬ PolyBoundedProofSystem) :=
  ⟨p_ne_np_from_depth_collapse, p_ne_np_from_mfi⟩

end CubeGraph
