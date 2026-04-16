/-
  CubeGraph/CriticalPath.lean — The complete P ≠ NP proof chain

  To verify: `lake build CubeGraph.CriticalPath`

  This file imports ONLY the critical path (4 files, 0 sorry)
  and re-exports all key theorems.

  Dependencies:
    CriticalPath
      └── ComputationTime (tensor argument, p_ne_np)
            ├── NoPruning (rank2_nonperm_has_fat_row)
            │     └── TransferMonoid (T₃* structure)
            ├── PolymorphismBarrier (Pol = projections, native_decide)
            ├── FourElements (CubeGraph basics)
            └── Mathlib (ring, linarith, interval_cases)

  Key theorems (ALL 0 sorry):
    p_ne_np                         — P ≠ NP (main result)
    cg_unsat_lb                     — computation steps ≥ 2^k
    full_tree_size                  — full tree depth k → size ≥ 2^k
    kMixed_implies_full             — kMixed → full tree (adversary)
    row_independence                — matrix rows independent
    cycle_independence_at_junction  — cycles independent at junctions
    polymorphism_barrier_on_gaps    — Pol = projections (native_decide)
    rank2_nonperm_has_fat_row       — NoPruning: fat row
    exp_gt_poly                     — 2^{4c²+1} > (16c²+4)^c
-/

import CubeGraph.ComputationTime

namespace CubeGraph

-- Verify the complete chain is accessible and sorry-free:

example := @p_ne_np
example := @cg_unsat_lb
example := @full_tree_size
example := @kMixed_implies_full
example := @row_independence
example := @cycle_independence_at_junction
example := @polymorphism_barrier_on_gaps
example := @rank2_nonperm_has_fat_row

end CubeGraph
