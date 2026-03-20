/-
  CubeGraph/FunctionalTransfer.lean
  Barrier 5: Functional Transfer (Bijunctive / 2-SAT)

  A transfer operator is "functional on gaps" when each source gap maps to
  at most one target gap. This captures Schaefer's bijunctive (2-SAT) class:
  fiber size 1 means constraints are functions, not relations.

  Key theorem: composition of functional transfers is functional.
  This is why 2-SAT is in P: the constraint graph stays deterministic
  under composition — no exponential branching.

  Part of the 5-Barriers program: five independent tractability mechanisms
  for Boolean SAT, exhaustive by Schaefer's dichotomy (1978).

  See: experiments-ml/012_2026-03-05_fiber-algebra-topology/RESULTS.md (§2, Barrier 5)
  See: experiments-ml/012_2026-03-05_fiber-algebra-topology/PLAN-FunctionalTransfer.md
  See: formal/CubeGraph/InvertibilityBarrier.lean (Barrier 1: XOR invertibility)
  See: formal/CubeGraph/HornBarrier.lean (Barrier 2: Horn OR-closed gaps)
  See: formal/CubeGraph/DualHornBarrier.lean (Barrier 2b: Dual-Horn AND-closed gaps)
  See: formal/CubeGraph/TrivialSection.lean (Barrier 3: trivial section)
  See: formal/CubeGraph/Rank1AC.lean (Barrier 4: rank-1 + AC → SAT)
  See: formal/CubeGraph/FiberDichotomy.lean (complementary: fiber size explains 2-SAT vs 3-SAT)
  See: formal/CubeGraph/BarrierSummary.lean (Meta: witness failing all 5 barriers)
-/

import CubeGraph.PartB

namespace CubeGraph

/-! ## Section 1: IsFunctionalOnGaps Definition -/

/-- A transfer operator is functional on gaps: each source gap that has
    at least one compatible target gap has EXACTLY one.
    Captures Schaefer's bijunctive (2-SAT): constraints are functions.
    Expanded form of ∃! (ExistsUnique not available without Mathlib). -/
def IsFunctionalOnGaps (c1 c2 : Cube) : Prop :=
  ∀ g1 : Vertex, c1.isGap g1 = true →
    (∃ g2 : Vertex, c2.isGap g2 = true ∧ transferOp c1 c2 g1 g2 = true) →
    ∃ g2 : Vertex, (c2.isGap g2 = true ∧ transferOp c1 c2 g1 g2 = true) ∧
      ∀ g2' : Vertex, (c2.isGap g2' = true ∧ transferOp c1 c2 g1 g2' = true) → g2' = g2

/-! ## Section 2: Composition Theorem -/

/-- **Barrier 5**: Composition of functional transfers is functional.
    If c1→c2 and c2→c3 are both functional on gaps, then the composed
    transfer (via BoolMat.mul) is also functional on gaps.

    This is why 2-SAT chains stay deterministic: each gap maps to exactly
    one gap at every step, so path-following is O(n). -/
theorem functional_comp (c1 c2 c3 : Cube)
    (h12 : IsFunctionalOnGaps c1 c2)
    (h23 : IsFunctionalOnGaps c2 c3) :
    ∀ g1 : Vertex, c1.isGap g1 = true →
      (∃ g3 : Vertex, c3.isGap g3 = true ∧
        (BoolMat.mul (transferOp c1 c2) (transferOp c2 c3)) g1 g3 = true) →
      ∃ g3 : Vertex, (c3.isGap g3 = true ∧
        (BoolMat.mul (transferOp c1 c2) (transferOp c2 c3)) g1 g3 = true) ∧
        ∀ g3' : Vertex, (c3.isGap g3' = true ∧
          (BoolMat.mul (transferOp c1 c2) (transferOp c2 c3)) g1 g3' = true) → g3' = g3 := by
  intro g1 hg1 ⟨g3_wit, hg3_wit_gap, hg3_wit_mul⟩
  -- Step 1: Extract intermediate k from matrix product
  obtain ⟨k, hk12, hk23⟩ := (BoolMat.mul_apply_true _ _ g1 g3_wit).mp hg3_wit_mul
  -- Step 2: k is a gap in c2
  have hk_gap : c2.isGap k = true := (transferOp_implies_gaps c1 c2 g1 k hk12).2
  -- Step 3: h12 gives uniqueness of k
  obtain ⟨k_u, ⟨_, hku12⟩, hk_uniq⟩ := h12 g1 hg1 ⟨k, hk_gap, hk12⟩
  -- Step 4: h23 gives uniqueness of g3 through k
  obtain ⟨g3_u, ⟨_, hg3u23⟩, hg3_uniq⟩ := h23 k hk_gap ⟨g3_wit, hg3_wit_gap, hk23⟩
  -- Step 5: Build the existential with witness g3_wit
  refine ⟨g3_wit, ⟨hg3_wit_gap, hg3_wit_mul⟩, ?_⟩
  -- Step 6: Prove uniqueness
  intro g3b ⟨hg3b_gap, hg3b_mul⟩
  obtain ⟨kb, hkb12, hkb23⟩ := (BoolMat.mul_apply_true _ _ g1 g3b).mp hg3b_mul
  have hkb_gap : c2.isGap kb = true := (transferOp_implies_gaps c1 c2 g1 kb hkb12).2
  -- kb = k: both equal to k_u
  have hkbk : kb = k :=
    (hk_uniq kb ⟨hkb_gap, hkb12⟩).trans (hk_uniq k ⟨hk_gap, hk12⟩).symm
  -- g3b = g3_wit: both equal to g3_u (after substituting kb → k)
  rw [hkbk] at hkb23
  exact (hg3_uniq g3b ⟨hg3b_gap, hkb23⟩).trans (hg3_uniq g3_wit ⟨hg3_wit_gap, hk23⟩).symm

end CubeGraph
