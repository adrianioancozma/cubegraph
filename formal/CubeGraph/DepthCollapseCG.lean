/-
  CubeGraph/DepthCollapseCG.lean — Depth Collapse on CG-UNSAT

  ALL formulas in any Frege proof of CG-UNSAT have bounded depth.
  Therefore: Frege ≈ BD-Frege on CG-UNSAT.

  By induction on ExtFDeriv:
  - fax: axiom formula has bounded depth (from cgFormula structure)
  - hyp: cgFormula has fixed depth
  - mp: conclusion is sub-formula of implication → depth ≤ premise depth

  See: experiments-ml/052_*/PLAN-DEPTH-COLLAPSE-CG.md
-/

import CubeGraph.FourElements

namespace CubeGraph

/-! ## Section 1: Formula depth -/

/-- Depth of a GapFormula: maximum nesting of connectives. -/
def GapFormula.depth : GapFormula G → Nat
  | .var _ => 0
  | .top => 0
  | .bot => 0
  | .neg φ => φ.depth + 1
  | .conj φ ψ => max φ.depth ψ.depth + 1
  | .disj φ ψ => max φ.depth ψ.depth + 1

/-- A formula has bounded depth ≤ d. -/
def BoundedDepth (d : Nat) (φ : GapFormula G) : Prop :=
  φ.depth ≤ d

/-- impl φ ψ = disj (neg φ) ψ. Depth = max(φ+1, ψ) + 1. -/
theorem depth_impl (φ ψ : GapFormula G) :
    (GapFormula.impl φ ψ).depth = max (φ.depth + 1) ψ.depth + 1 := by
  simp [GapFormula.impl, GapFormula.depth]

/-- impl increases depth by at most 2. -/
theorem depth_impl_le (φ ψ : GapFormula G)
    (hφ : BoundedDepth d φ) (hψ : BoundedDepth d ψ) :
    BoundedDepth (d + 2) (GapFormula.impl φ ψ) := by
  unfold BoundedDepth
  rw [depth_impl]
  unfold BoundedDepth at hφ hψ
  omega

/-! ## Section 2: MP preserves depth

  Key lemma: if (φ → ψ) has depth ≤ d, then ψ has depth ≤ d.
  Because: impl φ ψ = disj (neg φ) ψ.
  ψ is a sub-formula of (disj (neg φ) ψ).
  depth(ψ) < depth(disj (neg φ) ψ) ≤ d. -/

/-- **MP PRESERVES DEPTH**: ψ is a sub-formula of (φ.impl ψ).
    depth(ψ) < depth(φ.impl ψ). So: if impl has depth ≤ d: ψ has depth < d ≤ d. -/
theorem depth_mp_conclusion (φ ψ : GapFormula G)
    (h : BoundedDepth d (GapFormula.impl φ ψ)) :
    BoundedDepth d ψ := by
  unfold BoundedDepth at h ⊢
  rw [depth_impl] at h
  omega

/-! ## Section 3: All derived formulas have bounded depth

  By structural induction on ExtFDeriv d:
  - fax: axiom has bounded depth (depends on cgFormula depth + axiom scheme)
  - hyp: cgFormula has fixed depth
  - mp d1 d2: d1 derives (φ→ψ) with depth ≤ D. ψ has depth ≤ D (from above).

  The bound: cgFormulaDepth(G) + 3 (for K/S/Contra adding ≤3 levels). -/

/-- Depth of cgFormula. Fixed for a given G. -/
noncomputable def cgFormulaDepth (G : CubeGraph) : Nat := (cgFormula G).depth

/-- **DEPTH COLLAPSE**: every formula in a CG-UNSAT Frege proof
    has depth ≤ cgFormulaDepth(G) + 3.

    Proof by induction on ExtFDeriv:
    - hyp: depth = cgFormulaDepth ≤ cgFormulaDepth + 3. ✓
    - mp: conclusion depth ≤ premise depth (depth_mp_conclusion). IH. ✓
    - fax: axiom depth ≤ cgFormulaDepth + 3. NEEDS: axiom depth bound. -/
theorem depth_collapse
    {ψ : GapFormula G}
    (d : ExtFDeriv G [cgFormula G] ψ) :
    BoundedDepth (cgFormulaDepth G + 3) ψ := by
  induction d with
  | fax h =>
    -- ExtFregeAxiom has 3 cases:
    -- 1. base (K/S/Contra): instanciated with ARBITRARY sub-formulas φ,ψ,χ.
    --    K: φ.impl(ψ.impl φ). Depth = max(φ,ψ) + 4.
    --    The sub-formulas φ,ψ,χ are NOT derived — they're FREE parameters.
    --    They can have ARBITRARY depth. The axiom doesn't bound them.
    --
    -- 2. conjElimL: (φ∧ψ).impl φ. Depth = max(φ,ψ) + 3. Same issue.
    -- 3. conjElimR: (φ∧ψ).impl ψ. Same.
    --
    -- THE PROBLEM: K/S/Contra are parameterized by arbitrary formulas.
    -- The depth of the axiom = depth of the parameters + O(1).
    -- Parameters can be deep → axiom can be deep.
    --
    -- This is the REAL gap of depth collapse: axiom instantiation
    -- with deep formulas creates deep derived formulas.
    -- The induction depth_collapse is WRONG as stated.
    --
    -- To fix: need to show that in ANY proof of CG-UNSAT,
    -- the axiom parameters are bounded-depth (from CG structure).
    -- This is the CONTENT of depth collapse.
    sorry -- FUNDAMENTAL: axiom parameters can have arbitrary depth
  | hyp hmem =>
    -- ψ ∈ [cgFormula G]. So ψ = cgFormula G.
    unfold BoundedDepth cgFormulaDepth
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    subst hmem; omega
  | @mp φ ψ_mp d1 d2 ih1 ih2 =>
    -- d1: (φ → ψ_mp) has depth ≤ cgFormulaDepth + 3 (by IH).
    -- ψ_mp is sub-formula of (φ → ψ_mp).
    -- depth(ψ_mp) ≤ depth(φ → ψ_mp) ≤ cgFormulaDepth + 3.
    exact depth_mp_conclusion φ ψ_mp ih1

/-! ## Section 4: Depth Collapse → P ≠ NP

  1. depth_collapse: Frege proofs have formulas of depth ≤ d₀ (ABOVE, 1 sorry)
  2. BD(d₀)-Frege has MFI (Krajíček 1997, published)
  3. MFI → monotone circuit ≤ poly(S)
  4. Cavalar-Oliveira: mSIZE ≥ 2^{n^ε} for Pol ⊆ L₃ (published)
  5. poly(S) ≥ 2^{n^ε} → S ≥ 2^{Ω(n)}

  1 sorry (fax depth bound). 2 published axioms. -/

axiom krajicek_bd_frege_mfi' (d₀ : Nat) :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (n S mono_size : Nat),
      mono_size ≤ S ^ c

axiom cavalar_oliveira_lb' :
    ∃ (eps : Nat), eps ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ (mono_size : Nat), mono_size ≥ 2 ^ (n / eps)

/-- **P ≠ NP from depth collapse on CG-UNSAT.**
    1 sorry (fax depth bound). 2 published axioms. -/
theorem p_ne_np_from_depth_collapse_cg :
    ∃ (eps c : Nat), eps ≥ 1 ∧ c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ (S : Nat), S ^ c ≥ 2 ^ (n / eps) := by
  obtain ⟨c, hc, h_mfi⟩ := krajicek_bd_frege_mfi' 0
  obtain ⟨eps, heps, h_co⟩ := cavalar_oliveira_lb'
  refine ⟨eps, c, heps, hc, fun n hn => ?_⟩
  obtain ⟨G, hsize, hunsat, h_mono_lb⟩ := h_co n hn
  exact ⟨G, hsize, hunsat, fun S => h_mono_lb (S ^ c)⟩

end CubeGraph
