/-
  CubeGraph/HornBarrier.lean
  Barrier 2: Monotonicity (Horn-SAT, OR-closed gaps)

  A Horn cube has only clauses with at most 1 positive literal.
  In CubeGraph encoding (bit=1 = positive literal), Horn vertices
  have Hamming weight ≤ 1: {0, 1, 2, 4}.

  Key theorem: Horn cubes have OR-closed gap sets.
  This captures the algebraic reason Horn-SAT is in P:
  unit propagation computes the least fixpoint (Knaster-Tarski).

  Part of the 5-Barriers program: five independent tractability mechanisms
  for Boolean SAT, exhaustive by Schaefer's dichotomy (1978).

  See: experiments-ml/012_2026-03-05_fiber-algebra-topology/RESULTS.md (§2, Barrier 2)
  See: experiments-ml/012_2026-03-05_fiber-algebra-topology/G7-A.md (File 2, implementation plan)
  See: experiments-ml/012_2026-03-05_fiber-algebra-topology/PLAN-HornBarrier.md
  See: formal/CubeGraph/DualHornBarrier.lean (Barrier 2b: Dual-Horn AND-closed — mirror)
  See: formal/CubeGraph/TrivialSection.lean (Barrier 3: trivial section)
  See: formal/CubeGraph/InvertibilityBarrier.lean (Barrier 1: XOR invertibility)
  See: formal/CubeGraph/Rank1AC.lean (Barrier 4: rank-1 + AC → SAT)
  See: formal/CubeGraph/FunctionalTransfer.lean (Barrier 5: functional composition)
  See: formal/CubeGraph/BarrierSummary.lean (Meta: witness failing all 5 barriers)
-/

import CubeGraph.Basic

namespace CubeGraph

/-- A vertex is a Horn vertex: at most 1 positive literal.
    In CubeGraph encoding (bit=1 = positive), Hamming weight ≤ 1.
    Horn vertices: {0 (000), 1 (001), 2 (010), 4 (100)}. -/
def IsHornVertex (v : Vertex) : Bool :=
  v.val == 0 || v.val == 1 || v.val == 2 || v.val == 4

/-- A cube is Horn if every filled vertex is a Horn vertex.
    Equivalently: non-Horn vertices {3, 5, 6, 7} are all gaps. -/
def IsHornCube (c : Cube) : Prop :=
  ∀ v : Vertex, c.isGap v = false → IsHornVertex v = true

/-- A gap set is OR-closed: the bitwise OR of any two gaps is a gap. -/
def IsORClosed (c : Cube) : Prop :=
  ∀ v1 v2 : Vertex,
    c.isGap v1 = true → c.isGap v2 = true →
    c.isGap (Fin.mk ((v1.val ||| v2.val) % 8) (by omega)) = true

/-- Auxiliary: for any gapMask whose filled vertices are all Horn,
    the gaps are OR-closed.

    Quantifies over all 256 possible gapMasks (Fin 256).
    Each mask checked in O(72) operations → total ~18K evaluations.
    (Precedent: TaylorBarrier.lean handles 114.8M evaluations.) -/
private theorem horn_or_closed_aux :
    ∀ (mask : Fin 256),
      (∀ v : Fin 8, ((mask.val >>> v.val) &&& 1 == 1) = false → IsHornVertex v = true) →
      ∀ v1 v2 : Fin 8,
        ((mask.val >>> v1.val) &&& 1 == 1) = true →
        ((mask.val >>> v2.val) &&& 1 == 1) = true →
        ((mask.val >>> ((v1.val ||| v2.val) % 8)) &&& 1 == 1) = true := by
  native_decide

/-- **Barrier 2**: Horn cubes have OR-closed gap sets.
    Bridge: c.isGap v is definitionally (c.gapMask.val >>> v.val) &&& 1 == 1,
    so horn_or_closed_aux applies directly with mask = c.gapMask. -/
theorem horn_gaps_or_closed (c : Cube) (h : IsHornCube c) : IsORClosed c := by
  intro v1 v2 hv1 hv2
  exact horn_or_closed_aux c.gapMask h v1 v2 hv1 hv2

end CubeGraph
