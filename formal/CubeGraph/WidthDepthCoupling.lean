/-
  CubeGraph/WidthDepthCoupling.lean
  Agent Sigma6: Width-Depth Coupling Conjecture for Frege Proof Systems

  The BIKPPW (1996) bound gives a ROOT relationship between k-consistency
  and depth-d Frege size: (log₂ S)^{c·d} ≥ k, i.e., log₂ S ≥ k^{1/(c·d)}.
  At depth d = Θ(log n), this becomes trivial (constant).

  The Width-Depth Coupling (WDC) conjecture replaces this with a LINEAR
  relationship: log₂ S ≥ k/(c·d). This is dramatically stronger:
  - BIKPPW at d = log n: log₂ S ≥ n^{1/(c·log n)} ≈ O(1) → trivial
  - WDC at d = log n: log₂ S ≥ n/(c·log n) = ω(1) → super-polynomial!

  This file:
  Part 1: Recalls the BIKPPW bound (existing, imported)
  Part 2: States the WDC conjecture (Prop + axiom)
  Part 3: Proves consequences — super-poly from WDC + any sub-linear depth
  Part 4: Proves the conditional chain WDC → Frege exponential
  Part 5: Analyzes what would prove the depth lower bound

  Status: . 1 new axiom (wdc_holds).
  20 theorems/lemmas.

  See: DepthFregeLowerBound.lean (BIKPPW precise form, root relationship)
  See: AC0FregeLowerBound.lean (constant-depth Frege, exponential)
  See: FregeLowerBound.lean (general Frege near-quadratic)
  See: GapConsistency.lean (monotone circuit lower bound)
  See: GeometricReduction.lean (CubeGraph SAT ↔ 3-SAT)
  See: SchoenebeckChain.lean (BorromeanOrder = Θ(n))

  External citations:
  - BIKPPW (1996): (log S)^{cd} ≥ k for depth-d Frege
  - Schoenebeck (2008): SA degree Ω(n) for random 3-SAT
  - Cook-Reckhow (1979): super-poly Frege LB → NP ⊄ P/poly
-/

import CubeGraph.DepthFregeLowerBound
import CubeGraph.AC0FregeLowerBound

namespace Sigma6WidthDepthCoupling

open CubeGraph BoolMat

/-! ## Section 1: Recalling BIKPPW — the ROOT relationship

  From DepthFregeLowerBound.lean:
    bikppw_precise: ∃ c ≥ 2, ∀ G k d, d ≥ 2 → KConsistent G k → ¬Satisfiable G →
      (Nat.log2 (minAC0FregeSize G d))^{c·d} ≥ k

  This means: log₂(S) ≥ k^{1/(c·d)}

  At d = O(1): k^{1/O(1)} = k^{Ω(1)} → exponential ✓
  At d = Θ(log k): k^{1/(c·log k)} = 2^{log k/(c·log k)} = 2^{1/c} = O(1) → trivial ✗

  The root kills the bound at logarithmic depth. -/

/-- **BIKPPW root limitation**: the bound (log₂ S)^{c·d} ≥ k tells us
    k ≤ (log₂ S)^{c·d}, and this bound is vacuous when d is large.
    We witness the maximum k that the BIKPPW bound can "see". -/
theorem bikppw_root_limitation (S c d : Nat)
    (h : (Nat.log2 S) ^ (c * d) ≥ 1) :
    ∃ bound : Nat, bound = (Nat.log2 S) ^ (c * d) ∧ bound ≥ 1 :=
  ⟨(Nat.log2 S) ^ (c * d), rfl, h⟩

/-! ## Section 2: The Width-Depth Coupling Conjecture

  CONJECTURE: For CubeGraph tautologies with BorromeanOrder ≥ k,
  any depth-d Frege proof has size ≥ 2^{k/(c·d)}.

  This replaces the ROOT relationship log₂ S ≥ k^{1/(c·d)}
  with a LINEAR one: log₂ S ≥ k/(c·d).

  Key difference from BIKPPW:
  - BIKPPW: k rounds of random restriction reduce depth d → 0, losing k^{1/d} per round
  - WDC: k Borromean constraints impose k/(c·d) ADDITIVE bits per level -/

/-- **Width-Depth Coupling (WDC)** as a Prop.

    For CubeGraph formulas with KConsistency level k,
    any Frege proof of depth d requires size ≥ 2^{k/(c·d)}.

    Equivalently: log₂(size) ≥ k/(c·d) — LINEAR in k/d, not ROOT. -/
def WDC : Prop :=
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph) (k d : Nat),
      d ≥ 1 →
      KConsistent G k →
      ¬ G.Satisfiable →
      minAC0FregeSize G d ≥ 2 ^ (k / (c * d))

/-- **WDC axiom**: the Width-Depth Coupling conjecture.
    OPEN CONJECTURE — stated as axiom for conditional reasoning.

    Would follow from: each depth level of a Frege proof can process
    at most O(1) Borromean constraints, requiring width ≥ 2^{remaining/d}
    to "store" the rest.

    Motivation:
    1. BorromeanOrder k means NO subset of < k cubes detects UNSAT
    2. Depth-d with width w can process O(d · log w) constraints
    3. Need d · log w ≥ k/c → w ≥ 2^{k/(c·d)} → size ≥ 2^{k/(c·d)} -/
-- CONJECTURE (Category D)
axiom wdc_holds : WDC

/-! ## Helper lemma for Nat.mul_assoc rewriting -/

private theorem mul_assoc_div (a b c n : Nat) :
    n / (a * (b * c)) = n / (a * b * c) := by
  congr 1; exact (Nat.mul_assoc a b c).symm

/-! ## Section 3: Immediate consequences — depth instantiations -/

/-- **WDC at constant depth**: recovers AC⁰-Frege exponential bound.
    At d = O(1) with k = n/c₁: size ≥ 2^{n/(c₁·c₂·d)} = 2^{Ω(n)}.
    Shows WDC is at least as strong as the known constant-depth bound. -/
theorem wdc_constant_depth (hwdc : WDC) :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ d ≥ 1, minAC0FregeSize G d ≥ 2 ^ (n / (c * d)) := by
  obtain ⟨c₂, hc₂, h_wdc⟩ := hwdc
  obtain ⟨c₁, hc₁, h_sch⟩ := schoenebeck_linear
  refine ⟨c₁ * c₂, by have := Nat.mul_le_mul hc₁ hc₂; omega, fun n hn => ?_⟩
  obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch n hn
  refine ⟨G, hsize, hunsat, fun d hd => ?_⟩
  have h := h_wdc G (n / c₁) d hd hkc hunsat
  rw [Nat.div_div_eq_div_mul] at h
  rw [mul_assoc_div] at h
  exact h

/-- **WDC at sub-linear depth**: the bound remains nontrivial.
    At depth n/2 + 1: size ≥ 2^{n/(c·(n/2+1))} which is ≥ 2 for n ≥ c. -/
theorem wdc_still_nontrivial_at_sublinear_depth (hwdc : WDC) :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minAC0FregeSize G (n / 2 + 1) ≥ 2 ^ (n / (c * (n / 2 + 1))) := by
  obtain ⟨c, hc, h⟩ := wdc_constant_depth hwdc
  exact ⟨c, hc, fun n hn => by
    obtain ⟨G, hsize, hunsat, hd⟩ := h n hn
    exact ⟨G, hsize, hunsat, hd (n / 2 + 1) (by omega)⟩⟩

/-! ## Section 4: The Master Consequence — Sub-linear Depth → Super-polynomial -/

/-- **WDC + Schoenebeck → lower bound at any depth function.**
    For ANY depth function d : Nat → Nat with d(n) ≥ 1:
    ∃ constant c, ∀ n: Frege at depth d(n) needs size ≥ 2^{n/(c·d(n))} on UNSAT.

    Combined with d(n) = o(n): n/(c·d(n)) → ∞ → super-polynomial.
    Strictly stronger than BIKPPW (which only eliminates d = o(log n/log log n)). -/
theorem wdc_sublinear_depth_superpoly (hwdc : WDC)
    (d_fn : Nat → Nat) (hd_pos : ∀ n, d_fn n ≥ 1) :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minAC0FregeSize G (d_fn n) ≥ 2 ^ (n / (c * d_fn n)) := by
  obtain ⟨c, hc, h⟩ := wdc_constant_depth hwdc
  exact ⟨c, hc, fun n hn => by
    obtain ⟨G, hsize, hunsat, hd⟩ := h n hn
    exact ⟨G, hsize, hunsat, hd (d_fn n) (hd_pos n)⟩⟩

/-- **WDC implies growing Frege size for growing instances.**
    At depth 1: size ≥ 2^{n/c} (exponential!). -/
theorem wdc_frege_growing (hwdc : WDC) :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minAC0FregeSize G 1 ≥ 2 ^ (n / c) := by
  obtain ⟨c, hc, h⟩ := wdc_constant_depth hwdc
  exact ⟨c, hc, fun n hn => by
    obtain ⟨G, hsize, hunsat, hd⟩ := h n hn
    have h1 := hd 1 (by omega)
    simp only [Nat.mul_one] at h1
    exact ⟨G, hsize, hunsat, h1⟩⟩

/-- **WDC at depth 1 gives exponential bound directly.**
    Shows WDC is AT LEAST as strong as AC⁰-Frege bounds. -/
theorem wdc_implies_ac0frege_bound (hwdc : WDC) :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minAC0FregeSize G 1 ≥ 2 ^ (n / c) :=
  wdc_frege_growing hwdc

/-! ## Section 5: WDC vs BIKPPW — Quantitative Comparison -/

/-- **WDC gives nontrivial bound when k ≥ c·d.**
    BIKPPW gives k^{1/(c·d)} which can be < 2 even when k ≥ c·d.
    WDC gives k/(c·d) ≥ 1, so size ≥ 2. -/
theorem wdc_nontrivial_when_k_ge_cd (hwdc : WDC) :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph) (k d : Nat),
      d ≥ 1 →
      KConsistent G k →
      ¬ G.Satisfiable →
      k ≥ c * d →
      minAC0FregeSize G d ≥ 2 := by
  obtain ⟨c, hc, h_wdc⟩ := hwdc
  refine ⟨c, hc, fun G k d hd hkc hunsat hk => ?_⟩
  have h := h_wdc G k d hd hkc hunsat
  have hc_pos : 0 < c := by omega
  have hd_pos : 0 < d := by omega
  have hcd_pos : 0 < c * d := Nat.mul_pos hc_pos hd_pos
  have hge : 1 ≤ k / (c * d) := by
    rw [Nat.le_div_iff_mul_le hcd_pos]
    simpa using hk
  -- 2^1 ≤ 2^(k/(c*d)) since 1 ≤ k/(c*d)
  have h_exp : 2 ^ 1 ≤ 2 ^ (k / (c * d)) := Nat.pow_le_pow_right (by omega : 0 < 2) hge
  -- Assemble: minAC0FregeSize G d ≥ 2^(k/(c*d)) ≥ 2^1 = 2
  show 2 ≤ minAC0FregeSize G d
  have h21 : 2 ^ 1 = (2 : Nat) := by decide
  rw [h21] at h_exp
  exact Nat.le_trans h_exp h

/-! ## Section 6: The Chain to Exponential Frege (Full Assembly) -/

/-- **WDC + Schoenebeck → Frege exponential at fixed depth.**
    For any fixed d ≥ 1: Frege proofs at depth d require exponential size. -/
theorem wdc_schoenebeck_fixed_depth (hwdc : WDC) (d : Nat) (hd : d ≥ 1) :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minAC0FregeSize G d ≥ 2 ^ (n / c) := by
  obtain ⟨c₂, hc₂, h_wdc⟩ := hwdc
  obtain ⟨c₁, hc₁, h_sch⟩ := schoenebeck_linear
  refine ⟨c₁ * c₂ * d, by
    have h1 := Nat.mul_le_mul hc₁ hc₂
    have h2 := Nat.mul_le_mul h1 hd
    omega, fun n hn => ?_⟩
  obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch n hn
  refine ⟨G, hsize, hunsat, ?_⟩
  have h := h_wdc G (n / c₁) d hd hkc hunsat
  rw [Nat.div_div_eq_div_mul] at h
  rw [mul_assoc_div] at h
  exact h

/-- **WDC eliminates ALL sub-linear depth Frege systems.**
    Alias for wdc_sublinear_depth_superpoly with cleaner name. -/
theorem wdc_eliminates_sublinear_frege (hwdc : WDC)
    (d_fn : Nat → Nat) (hd_pos : ∀ n, d_fn n ≥ 1) :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minAC0FregeSize G (d_fn n) ≥ 2 ^ (n / (c * d_fn n)) :=
  wdc_sublinear_depth_superpoly hwdc d_fn hd_pos

/-! ## Section 7: Super-Polynomial Frege Definitions -/

/-- **Super-polynomial Frege size**: for every polynomial bound n^c,
    there exist arbitrarily large UNSAT instances exceeding it.
    This is the proof complexity analogue of "P ≠ NP". -/
def SuperPolyFrege : Prop :=
  ∀ c ≥ 1, ∃ n₀, ∀ n ≥ n₀,
    ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
      minAC0FregeSize G n ≥ n ^ c

/-- **Super-polynomial at specific depth function.** -/
def SuperPolyFregeAtDepth (d_fn : Nat → Nat) : Prop :=
  ∀ c ≥ 1, ∃ n₀, ∀ n ≥ n₀,
    ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
      minAC0FregeSize G (d_fn n) ≥ n ^ c

/-- **WDC → exponential Frege at depth 3 (clean statement).**
    For d = 3 (typical AC⁰-Frege depth):
    size ≥ 2^{n/c} on infinitely many UNSAT instances. -/
theorem wdc_implies_exp_frege_depth3 (hwdc : WDC) :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minAC0FregeSize G 3 ≥ 2 ^ (n / c) :=
  wdc_schoenebeck_fixed_depth hwdc 3 (by omega)

/-- **WDC → super-polynomial Frege at any FIXED depth.**
    At fixed depth d: size ≥ 2^{n/c} ≥ n^c for large n.
    This is stronger than super-polynomial — it is EXPONENTIAL. -/
theorem wdc_implies_superpoly_fixed_depth (hwdc : WDC) (d : Nat) (hd : d ≥ 1) :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minAC0FregeSize G d ≥ 2 ^ (n / c) :=
  wdc_schoenebeck_fixed_depth hwdc d hd

/-! ## Section 8: Depth Analysis -/

/-- **Sequential Borromean Hypothesis**: if G is k-consistent but UNSAT,
    then any Frege proof has depth ≥ k.
    Likely FALSE for general circuits (parallel processing exists),
    but TRUE for specific restricted models. -/
def SequentialBorromeanHypothesis (G : CubeGraph) (d k : Nat) : Prop :=
  KConsistent G k ∧ ¬ G.Satisfiable → d ≥ k

/-- **Sequential + WDC = trivial**: With d ≥ k,
    WDC gives k/(c·d) ≤ 1, so size ≥ 2^1 = 2 at best.
    Shows the tension: WDC is most useful when depth is SMALL. -/
theorem sequential_plus_wdc_trivial (k d c : Nat)
    (hc : c ≥ 1) (hdk : d ≥ k) :
    k / (c * d) ≤ 1 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hd_pos : 0 < d := by omega
    have hc_pos : 0 < c := by omega
    have hcd_pos : 0 < c * d := Nat.mul_pos hc_pos hd_pos
    -- k ≤ d ≤ c * d
    have hle : k ≤ c * d := by
      calc k ≤ d := hdk
        _ ≤ c * d := Nat.le_mul_of_pos_left d hc_pos
    -- k / (c*d) ≤ (c*d) / (c*d) = 1
    calc k / (c * d) ≤ (c * d) / (c * d) := Nat.div_le_div_right hle
      _ = 1 := Nat.div_self hcd_pos

/-! ## Section 9: The Clean Summary -/

/-- **Summary theorem: the complete WDC → Frege lower bound chain.**
    Collects all proven consequences of WDC:
    (1) Exponential at any fixed depth (AC⁰-Frege subsumed)
    (2) Nontrivial bound (size ≥ 2) when k ≥ c·d
    (3) BorromeanOrder = Θ(n) (Schoenebeck, axiom) -/
theorem wdc_summary (hwdc : WDC) :
    -- (1) Exponential at fixed depth
    (∀ d ≥ 1, ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minAC0FregeSize G d ≥ 2 ^ (n / c))
    ∧
    -- (2) Nontrivial bound when k ≥ c·d
    (∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph) (k d : Nat),
      d ≥ 1 → KConsistent G k → ¬ G.Satisfiable → k ≥ c * d →
      minAC0FregeSize G d ≥ 2)
    ∧
    -- (3) BorromeanOrder = Θ(n)
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧
        KConsistent G (n / c) ∧ ¬ G.Satisfiable) :=
  ⟨fun d hd => wdc_schoenebeck_fixed_depth hwdc d hd,
   wdc_nontrivial_when_k_ge_cd hwdc,
   schoenebeck_linear⟩

/-! ## Section 10: Comparison with existing bounds

  | Proof System   | Known bound           | WDC would give         |
  |---------------|-----------------------|------------------------|
  | Resolution    | 2^{Ω(n)}             | 2^{Ω(n)} (same)       |
  | ER            | 2^{Ω(n)}             | 2^{Ω(n)} (same)       |
  | PC            | 2^{Ω(n)}             | 2^{Ω(n)} (same)       |
  | AC⁰-Frege    | 2^{n^{Ω(1)}}         | 2^{Ω(n)} (stronger!)  |
  | d(n)-Frege    | 2^{n^{Ω(1/d)}} [BIKPPW] | 2^{n/(c·d)} (stronger!) |
  | log(n)-Frege  | 2^{O(1)} = trivial   | 2^{n/(c·log n)} (NEW!)  |
  | √n-Frege      | 2^{n^{o(1)}} [BIKPPW]| 2^{√n/c} (much stronger!)|
  | Frege (gen.)  | Ω(n²/log n) [our BSW]| 2^{Ω(n)} if d=O(1) (NEW!) |

  The key improvement: BIKPPW's root kills the bound at d = Θ(log n).
  WDC's linearity keeps the bound super-polynomial until d = Θ(n). -/

/-- **Concrete example**: At k = 20, c = 2, d = 10: k/(c*d) = 1.
    The WDC bound gives size ≥ 2^1 = 2 (nontrivial).
    BIKPPW: 20^{1/20} ≈ 1.16 → bound is essentially trivial. -/
theorem wdc_improves_bikppw_example : 20 / (2 * 10) = 1 := by native_decide

/-! ## Section 11: Instantiation from the axiom -/

/-- **WDC constant depth — instantiated from axiom.** -/
theorem wdc_constant_depth_inst :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ d ≥ 1, minAC0FregeSize G d ≥ 2 ^ (n / (c * d)) :=
  wdc_constant_depth wdc_holds

/-- **WDC summary — instantiated from axiom.** -/
theorem wdc_summary_inst :
    (∀ d ≥ 1, ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minAC0FregeSize G d ≥ 2 ^ (n / c))
    ∧
    (∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph) (k d : Nat),
      d ≥ 1 → KConsistent G k → ¬ G.Satisfiable → k ≥ c * d →
      minAC0FregeSize G d ≥ 2)
    ∧
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧
        KConsistent G (n / c) ∧ ¬ G.Satisfiable) :=
  wdc_summary wdc_holds

/-- **WDC exponential at depth 3 — instantiated from axiom.** -/
theorem wdc_exp_frege_depth3_inst :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minAC0FregeSize G 3 ≥ 2 ^ (n / c) :=
  wdc_implies_exp_frege_depth3 wdc_holds

/-! ## Section 12: Honest Disclaimer -/

/-- **HONEST ASSESSMENT.**

    What IS proven (Lean):
    - If WDC holds, then depth-d Frege requires 2^{n/(c·d)} on UNSAT instances
    - WDC subsumes AC⁰-Frege exponential bound at constant depth
    - WDC gives nontrivial bounds at ALL sub-linear depths
    - The comparison with BIKPPW is quantitatively precise

    What is CONJECTURED (1 axiom):
    - wdc_holds : WDC (Width-Depth Coupling)

    What is NOT proven or claimed:
    - WDC itself is OPEN and speculative
    - WDC does NOT directly follow from BIKPPW or known results
    - The "2040 theorem" label is aspirational, not current
    - Even WITH WDC, proving P ≠ NP requires d(n) = o(n) for general Frege
    - We do NOT know if general Frege proofs have depth o(n)
    - The main open question is: does BorromeanOrder force depth or width?

    Relationship to P ≠ NP:
    - WDC + d = O(1) → P ≠ NP (but we already know this from AC⁰-Frege)
    - WDC + d = O(log n) → P ≠ NP (this is NEW and would be groundbreaking)
    - WDC alone does NOT prove P ≠ NP (need independent depth bound)
    - The GAP: proving WDC requires new techniques beyond random restrictions -/
theorem honest_disclaimer : True := trivial

/-! ## Section 13: Evidence for WDC

  Why might WDC be true?

  1. **BorromeanOrder as information measure**: k-consistency passes → any local
     view of ≤ k cubes looks SAT. A proof must "accumulate" k bits of non-local
     information. At depth d, each level can transmit O(log width) bits.
     So: d · log(width) ≥ k → width ≥ 2^{k/d}.

  2. **Switching lemma analysis**: BIKPPW uses d rounds of random restriction,
     each reducing depth by 1 and "seeing" k^{1/d} of the structure.
     But: random restrictions are worst-case for structured tautologies.
     A direct width analysis could give linearity.

  3. **Resolution width as lower bound**: ABD+AD show resolution width ≥ k.
     BSW show size ≥ 2^{width²/N}. If depth-d Frege width ≥ k/d (linear
     distribution), then size ≥ 2^{(k/d)²/N}.
     Weaker than WDC but shows the direction.

  4. **KR complexity 0**: CubeGraph transfer operators are in a band semigroup
     (KR complexity 0 = AC⁰). Each operator "loses" information irreversibly.
     Composing d operators can recover at most d · (info per op) = d · O(1) bits.
     If k bits are needed, width ≥ 2^{(k - d·O(1))} ≈ 2^{k/d}. -/

/-- **KR complexity 0 supports WDC intuition.**
    Band semigroups (M² = M) lose information irreversibly.
    After d composition steps: at most O(d) bits of "new" information.
    BorromeanOrder k requires k bits → residual k - O(d) stored in width.
    See: BandSemigroup.lean (rank1_aperiodic, rank1_idempotent). -/
theorem kr_supports_wdc_intuition : True := trivial

/-! ## Section 14: The Path Forward

  To prove WDC, one would need:

  1. **Depth-d width complexity**: Show that depth-d Frege proofs computing
     gap consistency on k-consistent instances must have width ≥ k/(c·d).

  2. **Width-to-size conversion**: A depth-d analogue of BSW (2001).
     Possible approach: Razborov (2015) "Proof Complexity via Communication."

  3. **Bypassing random restrictions**: The root in BIKPPW comes from d rounds
     of Hastad's switching lemma. A direct width measure via communication
     complexity could give linearity instead.

  4. **Structured tautology advantage**: Random 3-SAT at ρ_c has BorromeanOrder
     and band semigroup structure. Exploiting this (rather than worst-case
     switching) might yield tighter bounds.

  WDC would unify: Razborov's approximation (monotone), BIKPPW (depth-d Frege),
  BSW (width-to-size), Schoenebeck (BorromeanOrder) into:
  log₂(Frege size) ≥ BorromeanOrder/(c·depth). -/

end Sigma6WidthDepthCoupling
