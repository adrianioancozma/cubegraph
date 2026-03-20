/-
  CubeGraph/Rank1AC.lean
  Rank-1 + Arc Consistency → SAT on ANY topology.

  The unifying theorem: rank-1 transfer operators make topology irrelevant.
  When all edges are rank-1 and arc-consistent, ALL gap pairs on each edge
  are compatible, so any gap selection is a valid global section.

  Key insight: rank-1 M factors as M[i,j] = R[i] ∧ C[j].
  Bidirectional AC forces R[g₁] = true for all source gaps,
  C[g₂] = true for all target gaps. Therefore M[g₁,g₂] = true
  for ALL gap pairs — not just some.

  This subsumes forest_arc_consistent_sat on rank-1 domains:
  - forest_ac_sat: any rank, trees only (~200 lines, induction)
  - rank1_ac_sat: rank-1 only, any topology (~50 lines, direct)

  Part of the 5-Barriers program: five independent tractability mechanisms
  for Boolean SAT, exhaustive by Schaefer's dichotomy (1978).
  Barrier 4 has NO Schaefer analog — genuinely new.

  See: experiments-ml/012_2026-03-05_fiber-algebra-topology/RESULTS.md (§2, Barrier 4)
  See: experiments-ml/011_2026-03-05_polynomial-barriers/PLAN-L1-RANK1-AC-SAT.md
  See: experiments-ml/010_2026-03-05/RANK-TOPOLOGY-DICHOTOMY.md (§3, §9)
  See: theory/theorems/THEOREM-A-HIERARCHY.md
  See: formal/CubeGraph/InvertibilityBarrier.lean (Barrier 1: XOR invertibility)
  See: formal/CubeGraph/HornBarrier.lean (Barrier 2: Horn OR-closed gaps)
  See: formal/CubeGraph/DualHornBarrier.lean (Barrier 2b: Dual-Horn AND-closed gaps)
  See: formal/CubeGraph/TrivialSection.lean (Barrier 3: trivial section)
  See: formal/CubeGraph/FunctionalTransfer.lean (Barrier 5: functional composition)
  See: formal/CubeGraph/BarrierSummary.lean (Meta: witness failing all 5 barriers)
  See: formal/CubeGraph/FiberDichotomy.lean (complementary: fiber size explains 2-SAT vs 3-SAT)
-/

import CubeGraph.RankTheory
import CubeGraph.LeafTrimming

namespace CubeGraph

/-! ## Section 1: AllRankOne Predicate -/

/-- All edges in a CubeGraph have rank-1 transfer operators. -/
def AllRankOne (G : CubeGraph) : Prop :=
  ∀ e ∈ G.edges, (transferOp (G.cubes[e.1]) (G.cubes[e.2])).IsRankOne

/-! ## Section 2: Key Lemma — Rank-1 + AC → All Gap Pairs Compatible

  This is the core insight. For a rank-1 matrix M[i,j] = R[i] ∧ C[j]:
  - AC forward ensures C[g₂] = true for all target gaps
  - AC backward ensures R[g₁] = true for all source gaps
  - Therefore M[g₁,g₂] = true for ALL gap pairs -/

/-- If a transfer operator is rank-1 and arc-consistent in both directions,
    then ALL pairs of source/target gaps are compatible. -/
theorem rank1_ac_all_compatible (c₁ c₂ : Cube)
    (hR1 : (transferOp c₁ c₂).IsRankOne)
    (hAC_fwd : arcConsistentDir c₁ c₂)
    (hAC_bwd : arcConsistentDir c₂ c₁) :
    ∀ g₁ g₂ : Vertex,
      c₁.isGap g₁ = true → c₂.isGap g₂ = true →
      transferOp c₁ c₂ g₁ g₂ = true := by
  obtain ⟨R, C, _, _, hRC⟩ := hR1
  intro g₁ g₂ hg₁ hg₂
  -- AC backward → R[g₁] = true
  have hR : R g₁ = true := by
    have hrow := (arcConsistentDir_reverse_iff_rowSup c₁ c₂).mp hAC_bwd g₁ hg₁
    obtain ⟨j, hj⟩ := BoolMat.mem_rowSup_iff.mp hrow
    exact ((hRC g₁ j).mp hj).1
  -- AC forward → C[g₂] = true
  have hC : C g₂ = true := by
    have hcol := (arcConsistentDir_iff_colSup c₁ c₂).mp hAC_fwd g₂ hg₂
    obtain ⟨i, hi⟩ := BoolMat.mem_colSup_iff.mp hcol
    exact ((hRC i g₂).mp hi).2
  -- Combine: M[g₁,g₂] ↔ R[g₁] ∧ C[g₂] = true
  exact (hRC g₁ g₂).mpr ⟨hR, hC⟩

/-! ## Section 3: Main Theorem — Rank-1 + AC → SAT -/

/-- **Rank-1 AC SAT**: If all edges are rank-1 and the graph is
    arc-consistent, then the graph is satisfiable.
    Works on ANY topology — trees, cycles, general graphs.
    Rank-1 makes topology irrelevant: all gap pairs are compatible. -/
theorem rank1_ac_sat (G : CubeGraph)
    (hR1 : AllRankOne G)
    (hAC : AllArcConsistent G) :
    G.Satisfiable := by
  -- Pick any gap per cube (every cube has ≥ 1 gap by gaps_nonempty)
  have hgaps : ∀ i : Fin G.cubes.length, ∃ v : Vertex, (G.cubes[i]).isGap v = true := by
    intro i
    obtain ⟨v, _, hv⟩ := (Cube.gapCount_pos_iff (G.cubes[i])).mp
      (by have := Cube.gapCount_pos (G.cubes[i]); omega)
    exact ⟨v, hv⟩
  refine ⟨fun i => (hgaps i).choose,
         fun i => (hgaps i).choose_spec,
         fun e he => ?_⟩
  -- For any edge: rank-1 + AC → all gap pairs compatible
  exact rank1_ac_all_compatible (G.cubes[e.1]) (G.cubes[e.2])
    (hR1 e he) (hAC e he).1 (hAC e he).2 _ _
    (hgaps e.1).choose_spec (hgaps e.2).choose_spec

/-! ## Section 4: Corollary — Subsumption -/

/-- rank1_ac_sat subsumes forest_ac_sat on rank-1 graphs.
    forest_ac_sat: needs acyclicity, works on any rank.
    rank1_ac_sat: needs rank-1, works on any topology. -/
theorem rank1_subsumes_forest (G : CubeGraph)
    (_h_forest : IsForest G)
    (hR1 : AllRankOne G)
    (hAC : AllArcConsistent G) :
    G.Satisfiable :=
  rank1_ac_sat G hR1 hAC

end CubeGraph
