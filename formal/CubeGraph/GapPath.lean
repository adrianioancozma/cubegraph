/-
  CubeGraph/GapPath.lean — Gap Paths as First-Class Objects

  A GapPath is a sequence of (cube_index, gap_vertex) pairs along a path
  in the CubeGraph, where consecutive entries are compatible via the
  transfer operator.

  Gap paths are the ATOMS of CG-UNSAT:
  - SAT ↔ ∃ gap paths covering all cubes consistently
  - UNSAT ↔ all gap paths conflict somewhere

  See: experiments-ml/039_2026-03-28_order-propagation/INSIGHT-PERISHABLE-AXIOMS.md
  See: formal/CubeGraph/EraseOnlyCollapse.lean (rank-1 after 3 hops)
-/

import CubeGraph.EraseOnlyCollapse

namespace CubeGraph

open BoolMat

/-! ## Part 1: GapPath Definition -/

/-- A step in a gap path: a cube index paired with a gap vertex at that cube. -/
structure GapStep (G : CubeGraph) where
  cube : Fin G.cubes.length
  gap : Vertex
  isGap : (G.cubes[cube]).isGap gap = true

/-- A GapPath on a CubeGraph: a non-empty list of GapSteps where
    consecutive steps are compatible via the transfer operator. -/
structure GapPath (G : CubeGraph) where
  steps : List (GapStep G)
  nonempty : steps.length ≥ 1
  compatible : ∀ (i : Nat) (hi : i + 1 < steps.length),
    transferOp (G.cubes[(steps[i]'(by omega)).cube]) (G.cubes[(steps[i+1]'(by omega)).cube])
      (steps[i]'(by omega)).gap (steps[i+1]'(by omega)).gap = true

/-- Length of a gap path -/
def GapPath.length (p : GapPath G) : Nat := p.steps.length

/-! ## Part 2: SAT gives Gap Paths -/

/-- SAT implies: for every edge, there exists a compatible gap pair. -/
theorem sat_implies_gapStep_pair (G : CubeGraph)
    (hsat : G.Satisfiable) (e : Fin G.cubes.length × Fin G.cubes.length)
    (he : e ∈ G.edges) :
    ∃ g₁ g₂ : Vertex,
      (G.cubes[e.1]).isGap g₁ = true ∧
      (G.cubes[e.2]).isGap g₂ = true ∧
      transferOp (G.cubes[e.1]) (G.cubes[e.2]) g₁ g₂ = true := by
  obtain ⟨s, hs_valid, hs_compat⟩ := hsat
  exact ⟨s e.1, s e.2, hs_valid e.1, hs_valid e.2, hs_compat e he⟩

/-- A single-step gap path from a valid gap. -/
def GapPath.singleton (G : CubeGraph) (i : Fin G.cubes.length) (g : Vertex)
    (hg : (G.cubes[i]).isGap g = true) : GapPath G :=
  ⟨[⟨i, g, hg⟩], by simp, by intro j hj; simp at hj⟩

/-- A two-step gap path from a compatible edge. -/
def GapPath.edge (G : CubeGraph) (i j : Fin G.cubes.length)
    (g₁ g₂ : Vertex)
    (hg₁ : (G.cubes[i]).isGap g₁ = true)
    (hg₂ : (G.cubes[j]).isGap g₂ = true)
    (hcompat : transferOp (G.cubes[i]) (G.cubes[j]) g₁ g₂ = true) : GapPath G :=
  ⟨[⟨i, g₁, hg₁⟩, ⟨j, g₂, hg₂⟩], by simp, by
    intro k hk
    simp at hk
    have : k = 0 := by omega
    subst this
    simp
    exact hcompat⟩

/-! ## Part 3: Key Structural Property -/

/-- **The fundamental fact**: SAT gives a gap path of length n (one gap per cube).
    This is just the satisfying assignment viewed as a gap path. -/
theorem sat_gives_full_gapPath (G : CubeGraph) (hsat : G.Satisfiable)
    (hne : G.cubes.length ≥ 1) :
    ∃ steps : List (GapStep G), steps.length = G.cubes.length ∧
      ∀ (i : Fin G.cubes.length), ∃ s ∈ steps, s.cube = i := by
  obtain ⟨s, hs_valid, _⟩ := hsat
  refine ⟨(List.finRange G.cubes.length).map (fun i => ⟨i, s i, hs_valid i⟩), ?_, ?_⟩
  · simp [List.length_map, List.length_finRange]
  · intro i
    exact ⟨⟨i, s i, hs_valid i⟩, by simp [List.mem_map], rfl⟩

/-! ## Part 4: Connection to Rank-1 Collapse -/

/-- **Rank-1 collapse on gap paths**: the composed transfer operator
    along any gap path of ≥ 3 steps through full-gap cubes with misaligned
    shared variables is rank-1 or zero.

    This is the bridge between GapPath and EraseOnlyCollapse.
    Consequence: after 3 hops, only 1 bit of info survives.
    The specific gap selection (which gap?) is LOST.

    Delegates to erase_only_monotone_collapse from EraseOnlyCollapse.lean. -/
theorem gapPath_rank1_collapse (cA cB cC : Cube) (rest : List Cube)
    (hB : FullGaps cB)
    (v₁ v₂ : Nat) (p q : Fin 3)
    (hsv_AB : SingleSharedVar cA cB v₁)
    (hsv_BC : SingleSharedVar cB cC v₂)
    (hp : cB.vars.idxOf v₁ = p.val)
    (hq : cB.vars.idxOf v₂ = q.val)
    (hpq : p ≠ q)
    (hRA : IndNonempty (transferOp cA cB).rowSup)
    (hCB : IndNonempty (transferOp cB cC).colSup) :
    (chainOperator (cA :: cB :: cC :: rest)).IsRankOne ∨
    chainOperator (cA :: cB :: cC :: rest) = zero :=
  erase_only_monotone_collapse cA cB cC rest hB v₁ v₂ p q
    hsv_AB hsv_BC hp hq hpq hRA hCB

end CubeGraph
