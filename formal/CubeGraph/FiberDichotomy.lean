/-
  CubeGraph/FiberDichotomy.lean
  Fiber Size Dichotomy: why 3-SAT cubes produce relational transfers.

  Main results:
  - Cube.fiberGaps: gaps filtered by bit value at a variable position
  - fiber_forced_three: single-filled 3-cube → forced fiber = 3 gaps
  - fiber_free_four: single-filled 3-cube → free fiber = 4 gaps
  - single_filled_gapCount: single-filled 3-cube → gapCount = 7

  The key insight: for k=3, the "forced" fiber has 2^(k-1) - 1 = 3 gaps,
  making the transfer a 3-element RELATION, not a function.
  For k=2 (2-SAT), fiber = 1, giving a FUNCTION → group → P.
  This is the P/NP threshold in CubeGraph terms.

  See: experiments-ml/011_2026-03-05_polynomial-barriers/BRAINSTORM-OR-FIBER-DICHOTOMY.md
  See: experiments-ml/011_2026-03-05_polynomial-barriers/PLAN-L2b-FIBER-DICHOTOMY.md
  See: formal/CubeGraph/InvertibilityBarrier.lean (OR non-invertible)
  See: formal/CubeGraph/Rank1AC.lean (rank-1 + AC → SAT)
  See: formal/CubeGraph/FunctionalTransfer.lean (Barrier 5: fiber=1 → functional)
  See: formal/CubeGraph/BarrierSummary.lean (Meta: witness failing all 5 barriers)
  See: formal/CubeGraph/TaylorBarrier.lean (no WNU3 on Fin 3 — CSP Dichotomy angle)
-/

import CubeGraph.GapLemmas

namespace CubeGraph

open Cube

/-! ## Section 1: Fiber Definition -/

/-- The fiber of a cube's gap set at bit position `idx` with value `val`:
    all gaps whose variable at position `idx` matches `val`.
    Partitions the gap set into two subsets by one variable's value. -/
def Cube.fiberGaps (c : Cube) (idx : Fin 3) (val : Bool) : List Vertex :=
  (List.finRange 8).filter fun v =>
    c.isGap v && (vertexBit v idx == val)

/-! ## Section 2: Core Combinatorics (cube-independent)

  Strategy: factor out the cube dependency. For a single-filled cube,
  `isGap v = (v ≠ filled)`. The remaining computation is purely about
  Fin 8 × Fin 3, verified exhaustively by native_decide (24 cases). -/

/-- 3 of 8 vertices differ from `filled` and share its bit at `idx`.
    This is the fiber size: 2^(3-1) - 1 = 3. -/
private theorem fiber_forced_aux :
    ∀ (filled : Fin 8) (idx : Fin 3),
      ((List.finRange 8).filter fun v : Fin 8 =>
        (if v = filled then false else true) &&
        (vertexBit v idx == vertexBit filled idx)).length = 3 := by
  native_decide

/-- 4 of 8 vertices differ from `filled` and have opposite bit at `idx`.
    This is 2^(3-1) = 4. -/
private theorem fiber_free_aux :
    ∀ (filled : Fin 8) (idx : Fin 3),
      ((List.finRange 8).filter fun v : Fin 8 =>
        (if v = filled then false else true) &&
        (vertexBit v idx == !vertexBit filled idx)).length = 4 := by
  native_decide

/-- 7 of 8 vertices differ from any given vertex. -/
private theorem gapCount_aux :
    ∀ (filled : Fin 8),
      (List.finRange 8).countP (fun v : Fin 8 =>
        if v = filled then false else true) = 7 := by
  native_decide

/-! ## Section 3: Predicate Factorization -/

/-- For a single-filled cube, `isGap v ↔ v ≠ filled` (as Bool equality). -/
private theorem isGap_eq_ne_filled (c : Cube) (filled : Vertex)
    (h_filled : c.isGap filled = false)
    (h_others : ∀ v : Vertex, v ≠ filled → c.isGap v = true) :
    ∀ v : Vertex,
      c.isGap v = if v = filled then false else true := by
  intro v
  by_cases hv : v = filled
  · subst hv; rw [h_filled, if_pos rfl]
  · rw [h_others v hv, if_neg hv]

/-! ## Section 4: Fiber Size Theorems -/

/-- **T1 (k=3)**: For a 3-cube with exactly 1 filled vertex, the fiber on
    the "forced" side (bit matching the filled vertex) has exactly **3** gaps.

    This is `2^(k-1) - 1 = 2^2 - 1 = 3` for `k = 3`.

    The P/NP threshold:
    - k=2 (2-SAT): fiber = 2^1 - 1 = **1** → function → group → **P**
    - k=3 (3-SAT): fiber = 2^2 - 1 = **3** → relation → monoid → **NP** -/
theorem fiber_forced_three (c : Cube) (filled : Vertex)
    (h_filled : c.isGap filled = false)
    (h_others : ∀ v : Vertex, v ≠ filled → c.isGap v = true)
    (idx : Fin 3) :
    (Cube.fiberGaps c idx (vertexBit filled idx)).length = 3 := by
  unfold Cube.fiberGaps
  simp only [isGap_eq_ne_filled c filled h_filled h_others]
  exact fiber_forced_aux filled idx

/-- The "free" fiber (opposite bit value from the filled vertex) has **4** gaps.
    This is `2^(k-1) = 2^2 = 4` for `k = 3`. -/
theorem fiber_free_four (c : Cube) (filled : Vertex)
    (h_filled : c.isGap filled = false)
    (h_others : ∀ v : Vertex, v ≠ filled → c.isGap v = true)
    (idx : Fin 3) :
    (Cube.fiberGaps c idx (!vertexBit filled idx)).length = 4 := by
  unfold Cube.fiberGaps
  simp only [isGap_eq_ne_filled c filled h_filled h_others]
  exact fiber_free_aux filled idx

/-! ## Section 5: Gap Count -/

/-- A single-filled 3-cube has exactly 7 gaps (8 vertices minus 1 filled). -/
theorem single_filled_gapCount (c : Cube) (filled : Vertex)
    (h_filled : c.isGap filled = false)
    (h_others : ∀ v : Vertex, v ≠ filled → c.isGap v = true) :
    c.gapCount = 7 := by
  unfold Cube.gapCount
  simp only [isGap_eq_ne_filled c filled h_filled h_others]
  exact gapCount_aux filled

/-! ## Section 6: Connection to P vs NP

  The fiber size determines the algebraic structure of transfer composition:

  | k | Fiber (forced) | Structure | Composition | Complexity |
  |---|----------------|-----------|-------------|------------|
  | 2 | 1              | Function  | Group       | **P**      |
  | 3 | 3              | Relation  | Monoid      | **NP**     |

  For k=2 (2-SAT): fiber=1 means each gap on the forced side maps to
  exactly one compatible gap. The transfer is a FUNCTION. Composition of
  functions is a function. Monodromy is a PERMUTATION on {0,1}.
  SAT ↔ fixed point exists. Decision: O(1) per cycle, O(V+E) total
  (Tarjan SCC algorithm for 2-SAT).

  For k=3 (3-SAT): fiber=3 means each gap can be compatible with MULTIPLE
  gaps. The transfer is a RELATION. Composition via OR (boolean matrix
  multiplication) is non-invertible (see InvertibilityBarrier.lean).
  Monodromy is a BOOLEAN MATRIX. SAT ↔ trace ≠ 0. Decision: NP-hard.

  SURPRISE: 2-SAT transfer operators are rank-2 (NOT rank-1).
  Rank alone does NOT explain the P/NP boundary.
  Fiber size does: fiber=1 → functional → invertible composition → P.

  FUTURE WORK (needs Cube2 infrastructure — not in current formalization):
  - T2: fiber=1 → transfer is bijection on fibers
  - T3: bijective monodromy = permutation on Fin 2
  - T4: permutation SAT iff fixed point exists

  See: BRAINSTORM-OR-FIBER-DICHOTOMY.md for the full analysis.
  See: InvertibilityBarrier.lean for the algebraic barrier.
  See: Rank1AC.lean for rank-1 tractability. -/

end CubeGraph
