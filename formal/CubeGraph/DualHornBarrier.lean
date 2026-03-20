/-
  CubeGraph/DualHornBarrier.lean
  Barrier 2b: Dual Monotonicity (Dual-Horn, AND-closed gaps)

  A Dual-Horn cube has only clauses with at most 1 negative literal.
  In CubeGraph encoding (bit=1 = positive literal), Dual-Horn vertices
  have Hamming weight ≥ 2: {3, 5, 6, 7}.

  Key theorem: Dual-Horn cubes have AND-closed gap sets.
  Dual of HornBarrier.lean: solutions OR-closed ↔ gaps AND-closed
  (via complement: solution = 7 XOR gap).

  Part of the 5-Barriers program: five independent tractability mechanisms
  for Boolean SAT, exhaustive by Schaefer's dichotomy (1978).

  See: experiments-ml/012_2026-03-05_fiber-algebra-topology/RESULTS.md (§2, Barrier 2b)
  See: experiments-ml/012_2026-03-05_fiber-algebra-topology/G7-A.md (File 3, implementation plan)
  See: experiments-ml/012_2026-03-05_fiber-algebra-topology/PLAN-DualHornBarrier.md
  See: formal/CubeGraph/HornBarrier.lean (Barrier 2: Horn OR-closed gaps — mirror)
  See: formal/CubeGraph/TrivialSection.lean (Barrier 3: trivial section)
  See: formal/CubeGraph/InvertibilityBarrier.lean (Barrier 1: XOR invertibility)
  See: formal/CubeGraph/Rank1AC.lean (Barrier 4: rank-1 + AC → SAT)
  See: formal/CubeGraph/FunctionalTransfer.lean (Barrier 5: functional composition)
  See: formal/CubeGraph/BarrierSummary.lean (Meta: witness failing all 5 barriers)
-/

import CubeGraph.Basic

namespace CubeGraph

/-- A vertex is a Dual-Horn vertex: at most 1 negative literal.
    In CubeGraph encoding (bit=1 = positive), Hamming weight ≥ 2.
    Dual-Horn vertices: {3 (011), 5 (101), 6 (110), 7 (111)}. -/
def IsDualHornVertex (v : Vertex) : Bool :=
  v.val == 3 || v.val == 5 || v.val == 6 || v.val == 7

/-- A cube is Dual-Horn if every filled vertex is a Dual-Horn vertex.
    Equivalently: non-Dual-Horn vertices {0, 1, 2, 4} are all gaps. -/
def IsDualHornCube (c : Cube) : Prop :=
  ∀ v : Vertex, c.isGap v = false → IsDualHornVertex v = true

/-- A gap set is AND-closed: the bitwise AND of any two gaps is a gap. -/
def IsANDClosed (c : Cube) : Prop :=
  ∀ v1 v2 : Vertex,
    c.isGap v1 = true → c.isGap v2 = true →
    c.isGap (Fin.mk ((v1.val &&& v2.val) % 8) (by omega)) = true

/-- Auxiliary: for any gapMask whose filled vertices are all Dual-Horn,
    the gaps are AND-closed.

    Mirror of horn_or_closed_aux with &&& replacing |||.
    Same cost: 256 × 72 ≈ 18K evaluations. -/
private theorem dualhorn_and_closed_aux :
    ∀ (mask : Fin 256),
      (∀ v : Fin 8, ((mask.val >>> v.val) &&& 1 == 1) = false → IsDualHornVertex v = true) →
      ∀ v1 v2 : Fin 8,
        ((mask.val >>> v1.val) &&& 1 == 1) = true →
        ((mask.val >>> v2.val) &&& 1 == 1) = true →
        ((mask.val >>> ((v1.val &&& v2.val) % 8)) &&& 1 == 1) = true := by
  native_decide

/-- **Barrier 2b**: Dual-Horn cubes have AND-closed gap sets.
    Bridge: c.isGap v is definitionally (c.gapMask.val >>> v.val) &&& 1 == 1,
    so dualhorn_and_closed_aux applies directly with mask = c.gapMask. -/
theorem dualhorn_gaps_and_closed (c : Cube) (h : IsDualHornCube c) : IsANDClosed c := by
  intro v1 v2 hv1 hv2
  exact dualhorn_and_closed_aux c.gapMask h v1 v2 hv1 hv2

end CubeGraph
