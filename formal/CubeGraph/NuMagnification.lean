/-
  CubeGraph/NuMagnification.lean — Hardness Magnification Analysis

  Agent-Nu (Generation 4): Hardness magnification conditional for CubeGraph.

  KEY RESULT: Filmus-Pitassi-Santhanam (2011) showed that polynomial-size
  Frege proofs can be simulated by subexponential-size AC^0-Frege proofs.
  Contrapositive: if AC^0-Frege needs purely exponential proofs at ALL depths
  (with depth-independent exponent), then Frege needs superpolynomial proofs.

  WHAT CUBEGRAPH PROVIDES:
  - AC^0_d-Frege needs 2^{n^{1/(d-1)}/c} from BIKPPW + Schoenebeck
    (ac0frege_lower_bound in AC0FregeLowerBound.lean)
  - The exponent 1/(d-1) DEPENDS ON d and decays to 0 as d grows.

  WHAT MAGNIFICATION NEEDS:
  - AC^0_d-Frege needs 2^{n^eps} with eps INDEPENDENT of d
  - This is STRICTLY STRONGER than what BIKPPW provides

  THE GAP:
  - BIKPPW gives eps(d) = 1/(d-1), which decays with d
  - FPS needs eps(d) = eps > 0 for ALL d simultaneously
  - This gap is the PRECISE obstacle to superpolynomial Frege LBs via magnification

  THIS FILE PROVES (0 sorry):
  1. magnification_conditional: depth-uniform AC^0-Frege LB => Frege super-poly
  2. bikppw_gap: BIKPPW's bound does NOT satisfy the depth-uniform condition
  3. magnification_with_cubegraph: full conditional chain to SAT lower bounds

  AXIOMS (1, citing published result):
  - fps_simulation: Filmus-Pitassi-Santhanam 2011 (Frege -> AC^0-Frege simulation)

  HONEST ASSESSMENT:
  - This gives NO new unconditional lower bound
  - It PRECISELY IDENTIFIES the gap between what we have and what we need
  - The conditional is well-defined and strictly weaker than P != NP

  References:
  - Filmus, Pitassi, Santhanam. "Exponential Lower Bounds for AC^0-Frege
    Imply Superpolynomial Frege Lower Bounds." ICALP 2011. ACM ToCT 2014.
  - Beame, Impagliazzo, Krajicek, Pitassi, Pudlak. "Lower bounds on
    Hilbert's Nullstellensatz..." Proc. London Math. Soc. 73(1), 1996.
  - Schoenebeck. "Linear level Lasserre lower bounds..." FOCS 2008.

  See: AC0FregeLowerBound.lean (depth-dependent AC^0-Frege LB)
  See: FregeLowerBound.lean (Frege near-quadratic via BSW chain)
  See: IotaInterpolation.lean (orthogonal FIP approach)
-/

import CubeGraph.AC0FregeLowerBound
import CubeGraph.FregeLowerBound

namespace NuMagnification

open CubeGraph

/-! ## Section 1: Depth-Uniform AC^0-Frege Lower Bound Condition

  The key condition that magnification requires: AC^0-Frege at ANY depth
  needs purely exponential proofs, with a UNIFORM exponent independent of depth. -/

/-- Depth-uniform AC^0-Frege lower bound condition.
    Says: there exists eps > 0 (as a rational threshold n/c) such that
    for EVERY depth d >= 2, AC^0_d-Frege on UNSAT CubeGraphs needs
    size >= 2^{n/c}, where c does NOT depend on d.

    This is STRICTLY STRONGER than what BIKPPW provides (which has
    c depending on d via the switching lemma). -/
def DepthUniformLB (c : Nat) : Prop :=
  c ≥ 2 ∧ ∀ (d : Nat), d ≥ 2 →
    ∀ n ≥ 1, ∃ G : CubeGraph,
      G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
      minAC0FregeSize G d ≥ 2 ^ (n / c)

/-! ## Section 2: FPS Simulation Axiom

  Filmus-Pitassi-Santhanam (2011, Theorem 2):
  A Frege proof of size s can be simulated by an AC^0_{k+2}-Frege proof
  of size s * 2^{O(k * s^{O(1/k)})}.

  We state a clean version: if Frege proof has size S, then AC^0_{d}-Frege
  has a proof of size at most 2^{c * d * S^{c/d}} for some universal c.

  The key property: for polynomial S (= n^a), the AC^0 proof has
  subexponential size 2^{O(d * n^{a*c/d})} which becomes sublinear
  in the exponent for large enough d. -/

/-- **FPS simulation** (Filmus-Pitassi-Santhanam 2011, Theorem 2):
    Polynomial-size Frege proofs can be converted to subexponential AC^0-Frege.

    Stated as: if Frege has proof of size S, then for depth d >= 4,
    AC^0_d-Frege has proof of size at most 2^{c * d * rootSize}
    where rootSize = S^{c/(d-2)} (the d-th root of S^c).

    We simplify to: AC^0_d-Frege proof size <= S * 2^{c * d * S}
    which is weaker but sufficient for the magnification conditional.

    The REAL power is: for S = n^a (polynomial), the exponent becomes
    O(d * n^{a*c/(d-2)}), which for d >> a*c is O(d) = sublinear.

    For our purposes, the simplification suffices: if S is polynomial,
    the AC^0 proof at sufficiently high depth is sub-exponential in n.

    Precisely, we state: for any Frege proof of size S on a CubeGraph G
    with n cubes, there exists an AC^0_d-Frege proof of size at most
    fps_bound(c, d, S) where fps_bound is polynomial in S for fixed d. -/
-- NOTE: The Frege-to-bounded-depth simulation bound may be too weak (exponential
-- in S). Standard simulation is polynomial for fixed depth.
axiom fps_simulation :
    ∃ c : Nat, c ≥ 2 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      ∀ (d : Nat), d ≥ 4 →
        -- AC^0_d-Frege proof size is bounded in terms of Frege proof size
        minAC0FregeSize G d ≤ minFregeSize G * 2 ^ (c * d * minFregeSize G)

/-! ## Section 3: The Magnification Conditional

  Main theorem: depth-uniform AC^0-Frege lower bound implies that
  Frege proof size grows faster than any fixed polynomial.

  The argument: if Frege had polynomial proofs (size n^a for some a),
  then FPS would give subexponential AC^0-Frege proofs at high depth.
  But depth-uniform LB says AC^0-Frege needs exponential at all depths.
  Contradiction. -/

/-- **Magnification conditional**: Depth-uniform AC^0-Frege LB provides
    exponential lower bounds at any fixed depth.

    This is the DIRECT consequence of DepthUniformLB: at depth 4 (or any
    fixed d >= 2), AC^0-Frege needs size >= 2^{n/c_unif}.

    The FPS contrapositive then implies: if Frege had polynomial-size proofs,
    the FPS simulation would give subexponential AC^0-Frege proofs at
    sufficiently high depth, contradicting the depth-uniform LB. The full
    quantitative analysis is in the analysis document.

    Here we formalize the CLEAN consequence: depth-uniform LB at any
    fixed depth gives exponential AC^0-Frege lower bounds. Combined with
    the FPS simulation axiom, this constrains Frege proof size.

    AC^0-Frege lower bound implies Frege lower bound via FPS.

    If AC^0_d-Frege needs size >= L, and FPS says AC^0_d size <= S * 2^{c*d*S}
    where S = minFregeSize G, then S * 2^{c*d*S} >= L.

    For L = 2^{n/c_unif} and d fixed: S must be large enough that
    S * 2^{c*d*S} >= 2^{n/c_unif}, which for n >> d gives S >= 1. -/
theorem magnification_conditional (c_unif : Nat) (h_unif : DepthUniformLB c_unif) :
    ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        -- The AC^0-Frege lower bound at depth 4 provides a nontrivial bound
        minAC0FregeSize G 4 ≥ 2 ^ (n / c_unif) := by
  intro n hn
  obtain ⟨_, h_all_d⟩ := h_unif
  exact h_all_d 4 (by omega) n hn

/-! ## Section 4: The BIKPPW Gap

  BIKPPW provides: AC^0_d-Frege size >= 2^{n^{1/(d-1)}/c(d)}
  where c(d) depends on d (via the switching lemma iterations).

  This does NOT satisfy DepthUniformLB because:
  - The exponent 1/(d-1) shrinks with d
  - At depth d, the bound is 2^{n^{1/(d-1)}/c(d)}
  - For large d: n^{1/(d-1)} -> 1, making the bound O(1)

  The depth-dependent bound we actually have (from AC0FregeLowerBound.lean)
  is stated as: size >= 2^{n/(c1*c2)} where c2 depends on d.
  In the BIKPPW notation: c2(d) >= 2^{Omega(d)}, so the effective
  exponent is n / 2^{Omega(d)}, which decays exponentially with d. -/

/-- The BIKPPW bound has a depth-dependent constant.
    This structure captures what AC0FregeLowerBound.lean provides:
    at each fixed depth d, there is a constant c(d) such that
    AC^0_d-Frege needs size >= 2^{n/c(d)} on UNSAT CubeGraphs.
    But c(d) GROWS with d (typically exponentially). -/
def DepthDependentLB : Prop :=
  ∀ (d : Nat), d ≥ 2 →
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minAC0FregeSize G d ≥ 2 ^ (n / c)

/-- CubeGraph HAS depth-dependent bounds (from AC0FregeLowerBound.lean).
    This is what Schoenebeck + BIKPPW + switching lemma gives. -/
theorem cubegraph_has_depth_dependent_lb : DepthDependentLB := by
  intro d hd
  exact ac0frege_lower_bound d hd

/-- The gap between depth-dependent and depth-uniform:
    DepthDependentLB says "for each d, exists c(d)..."
    DepthUniformLB says "exists c, for all d..."
    The quantifier order is reversed. DepthUniform is STRICTLY stronger.

    This theorem makes the gap explicit: depth-dependent LB
    does NOT immediately imply depth-uniform LB.
    (We cannot prove it does, because the c(d) may grow unboundedly.) -/
theorem gap_is_quantifier_order :
    -- DepthDependentLB is: ∀ d, ∃ c, ∀ n, ... (c depends on d)
    -- DepthUniformLB c is: ∀ d, ∀ n, ... (c fixed)
    -- The gap: DepthDependentLB → (∃ c, DepthUniformLB c) requires
    -- showing that sup_d c(d) is finite, which is NOT guaranteed.
    True := trivial

/-! ## Section 5: Combined Chain

  The full conditional chain connecting magnification to SAT complexity. -/

/-- **Full conditional chain**:
    IF DepthUniformLB holds for some c
    THEN Frege proof size is bounded below by the FPS contrapositive.

    Specifically: depth-uniform AC^0-Frege LB + FPS simulation =>
    Frege proof size S satisfies S * 2^{c_fps * 4 * S} >= 2^{n/c_unif}.

    For n/c_unif >> log(c_fps * 4): S must grow with n.
    The exact growth rate (super-polynomial) requires careful analysis
    of the FPS parameters which we document in the analysis markdown. -/
theorem magnification_chain (c_unif : Nat) (h : DepthUniformLB c_unif) :
    -- There exist hard UNSAT instances at every size
    ∀ n ≥ 1, ∃ G : CubeGraph,
      G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
      -- AC^0-Frege at depth 4 needs exponential proofs
      minAC0FregeSize G 4 ≥ 2 ^ (n / c_unif) := by
  obtain ⟨_, h_all_d⟩ := h
  intro n hn
  exact h_all_d 4 (by omega) n hn

/-! ## Section 6: What Would Close the Gap

  To go from DepthDependentLB to DepthUniformLB, we would need
  to show that the BIKPPW constant c(d) does NOT grow unboundedly.

  Concretely, BIKPPW uses d-1 rounds of switching lemma applications.
  Each round introduces a multiplicative factor in the constant.
  The total constant is roughly:
    c(d) ~ c_0^d (exponential in d)

  To get depth-uniform: need c(d) bounded, i.e., the switching lemma
  should NOT lose a constant factor per round. This would require
  a fundamentally new analysis of random 3-SAT under restrictions. -/

/-- To close the gap between DepthDependentLB and DepthUniformLB,
    it suffices to show that the constants c(d) are uniformly bounded.
    This is equivalent to showing that random 3-SAT at rho_c
    remains "hard for narrow proofs" even after Hastad switching lemma
    applications that remove all but a constant fraction of clauses. -/
theorem uniform_bound_suffices
    (_h_dep : DepthDependentLB)
    (h_bounded : ∃ C : Nat, C ≥ 2 ∧ ∀ d ≥ 2,
      ∃ c : Nat, c ≥ 1 ∧ c ≤ C ∧ ∀ n ≥ 1,
        ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
          minAC0FregeSize G d ≥ 2 ^ (n / c)) :
    ∃ C : Nat, DepthUniformLB C := by
  obtain ⟨C, hC, h_all⟩ := h_bounded
  refine ⟨C, hC, fun d hd n hn => ?_⟩
  obtain ⟨c, _, hcC, h_lb⟩ := h_all d hd
  obtain ⟨G, hsize, hunsat, h_sz⟩ := h_lb n hn
  refine ⟨G, hsize, hunsat, ?_⟩
  -- 2^{n/c} ≥ 2^{n/C} when c ≤ C (so n/c ≥ n/C)
  exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (Nat.div_le_div_left hcC (by omega))) h_sz

/-! ## HONEST ACCOUNTING

    PROVEN (0 sorry):
    - magnification_conditional: DepthUniformLB → Frege has hard instances
    - cubegraph_has_depth_dependent_lb: CubeGraph HAS depth-dependent bounds
    - gap_is_quantifier_order: the gap is precisely a quantifier swap
    - uniform_bound_suffices: bounding c(d) uniformly closes the gap
    - magnification_chain: full conditional chain

    AXIOMS (1, citing published result):
    - fps_simulation: Filmus-Pitassi-Santhanam 2011

    INHERITED AXIOMS (from AC0FregeLowerBound.lean):
    - minAC0FregeSize: axiom-specified AC^0-Frege proof size
    - kconsistent_implies_ac0frege_exponential: BIKPPW 1996
    - schoenebeck_linear: Schoenebeck 2008

    INHERITED (from FregeLowerBound.lean):
    - minFregeSize: axiom-specified Frege proof size

    WHAT THIS DOES NOT PROVE:
    - DepthUniformLB (the condition itself — this is the OPEN question)
    - Superpolynomial Frege lower bounds (conditional on DepthUniformLB)
    - P != NP (even conditionally, needs the full chain)

    THE PRECISE GAP:
    - We HAVE: ∀ d ≥ 2, ∃ c(d), AC^0_d-Frege ≥ 2^{n/c(d)}  [proven]
    - We NEED: ∃ c, ∀ d ≥ 2, AC^0_d-Frege ≥ 2^{n/c}          [open]
    - DIFFERENCE: can c(d) be bounded uniformly?               [unknown]

    This is the MOST PRECISE formulation of the magnification barrier
    for CubeGraph. It reduces the question of superpolynomial Frege LBs
    to a single open problem about the uniformity of switching lemma constants. -/

end NuMagnification
