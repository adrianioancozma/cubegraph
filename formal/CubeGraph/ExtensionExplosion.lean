/-
  CubeGraph/ExtensionExplosion.lean — Extension Variable Super-Polynomial Conjecture

  CONJECTURE: EF proofs of CG-UNSAT need ≥ 2^{Ω(n)} extension variables.
  Independent gap path families of size Ω(n) exist (expander, Menger), each
  path carries 1 independent bit (rank-1 collapse), and each bit requires
  its own extension variable.

  See: ContextExplosion.lean, EraseOnlyCollapse.lean, GapPath.lean
-/

import CubeGraph.GapPath
import CubeGraph.ContextExplosion

namespace CubeGraph

open BoolMat

/-! ## Part 1: Independent Gap Path Families -/

/-- Intermediate cubes of a gap path: all except first and last. -/
def GapPath.intermediates (p : GapPath G) : List (Fin G.cubes.length) :=
  match p.steps with
  | [] => []
  | [_] => []
  | _ :: mid => (mid.dropLast).map GapStep.cube

/-- Two gap paths are independent: their intermediate cubes are disjoint. -/
def GapPathIndependent (p₁ p₂ : GapPath G) : Prop :=
  ∀ c, c ∈ p₁.intermediates → c ∉ p₂.intermediates

/-- A family of gap paths is pairwise independent. -/
def IndependentFamily (paths : List (GapPath G)) : Prop :=
  ∀ i j : Fin paths.length, i ≠ j →
    GapPathIndependent (paths[i]) (paths[j])

/-- A singleton family is trivially independent. -/
theorem independentFamily_singleton (p : GapPath G) :
    IndependentFamily [p] := by
  intro i j hij
  exact absurd (Fin.ext (by simp [List.length] at i j ⊢) : i = j) hij

/-! ## Part 2: Extension Variable Count (axiom-specified) -/

/-- Minimum extension variables for any EF refutation of G. -/
axiom minExtensionVars (G : CubeGraph) : Nat

/-! ## Part 3: Unconditional Structural Facts (PROVEN) -/

/-- **Rank-1 bottleneck on gap paths**: path through full-gap cube with
    misaligned shared vars → rank-1 or zero composed operator.
    Each path carries at most 1 bit. From erase_only_monotone_collapse. -/
theorem gapPath_through_bottleneck_rank1_or_zero
    (cA cB cC : Cube) (rest : List Cube)
    (hB : FullGaps cB) (v₁ v₂ : Nat) (p q : Fin 3)
    (hsv_AB : SingleSharedVar cA cB v₁) (hsv_BC : SingleSharedVar cB cC v₂)
    (hp : cB.vars.idxOf v₁ = p.val) (hq : cB.vars.idxOf v₂ = q.val)
    (hpq : p ≠ q)
    (hRA : IndNonempty (transferOp cA cB).rowSup)
    (hCB : IndNonempty (transferOp cB cC).colSup) :
    (chainOperator (cA :: cB :: cC :: rest)).IsRankOne ∨
    chainOperator (cA :: cB :: cC :: rest) = zero :=
  erase_only_monotone_collapse cA cB cC rest hB v₁ v₂ p q
    hsv_AB hsv_BC hp hq hpq hRA hCB

/-- **Rank-1 is absorbing**: once reached, stays rank-1 or dies to zero. -/
theorem rank1_absorbing_on_path (M N : BoolMat 8) (hM : M.IsRankOne) :
    (mul M N).IsRankOne ∨ mul M N = zero :=
  rank1_left_compose M N hM

/-! ## Part 4: The Extension Explosion Conjecture -/

/-- **Extension Explosion Conjecture**: ∃ c ≥ 1, ∀ n ≥ 1,
    ∃ UNSAT CubeGraph G on ≥ n cubes with minExtensionVars G ≥ 2^{n/c}.

    Mechanism: Ω(n) independent gap paths at ρ_c (expander + Menger),
    each carrying 1 rank-1 bit. Extension variables must name each
    independent bit separately, giving 2^{Ω(n)} from the combinatorial
    explosion of bit assignments across independent paths. -/
axiom extension_explosion_conjecture :
  ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
    ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
      minExtensionVars G ≥ 2 ^ (n / c)

/-! ## Part 5: Conditional Separation -/

/-- Polynomially bounded EF: extension variables ≤ n^d. -/
def PolyBoundedExtension : Prop :=
  ∃ d : Nat, d ≥ 1 ∧ ∀ (G : CubeGraph),
    ¬ G.Satisfiable → minExtensionVars G ≤ G.cubes.length ^ d

/-- **IF Extension Explosion THEN no poly-bounded EF.**
    Uses exp_eventually_beats_poly from ContextExplosion.lean. -/
theorem extension_explosion_implies_separation :
    ¬ PolyBoundedExtension := by
  obtain ⟨c, hc, h_conj⟩ := extension_explosion_conjecture
  intro ⟨d, hd, h_poly⟩
  let n := 2 ^ (c * (d + 1))
  have hn : n ≥ 1 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨G, hsize, hunsat, h_exp⟩ := h_conj n hn
  have h_poly_G := h_poly G hunsat
  have h_chain : 2 ^ (n / c) ≤ G.cubes.length ^ d :=
    Nat.le_trans h_exp h_poly_G
  exact absurd h_chain (exp_eventually_beats_poly c d hc hd G.cubes.length)

/-! ## Part 6: Evidence Summary -/

/-- **Evidence**: rank-1 collapse + absorbing + H² escape + no inverse. -/
theorem extension_evidence :
    (∀ M N : BoolMat 8, M.IsRankOne → (mul M N).IsRankOne ∨ mul M N = zero)
    ∧ ¬ IsRankOne (mul (transferOp h2CubeA h2CubeB) (transferOp h2CubeB h2CubeC))
    ∧ (∀ M : BoolMat 8, M.IsRankOne → ¬ ∃ M', mul M M' = one) :=
  ⟨fun M N hM => rank1_left_compose M N hM,
   h2_composed_not_rankOne,
   fun M hM => rank1_no_right_inverse (by omega) hM⟩

/-! Axioms: minExtensionVars (spec), extension_explosion_conjecture (OPEN).
  Reused: exp_eventually_beats_poly. Proven: 5 theorems. 0 sorry. -/

end CubeGraph
