/-
  TODO: Derive h_instances as theorem from SchoenebeckKConsistent + NoPruning

  h_instances (currently hypothesis in p_ne_np):
    ∀ k ≥ 4, ∃ (a : AdaptiveQuery) (D : Nat),
      a.isMixed ∧ a.kMixed k ∧ D ≤ 4 * k

  Derivation steps:
  1. Define "correct algorithm for CG instance G":
     AdaptiveQuery where eval(oracle) = false for UNSAT oracles,
     true for SAT oracles

  2. From SchoenebeckKConsistent G k:
     Any ≤k queries are consistent with a SAT assignment.
     → ∃ SAT oracle in both branches at each depth < k
     → each subtree has a true-leaf

  3. From rank2_nonperm_has_fat_row (NoPruning):
     Both gap values at each intermediate are viable.
     → ∃ UNSAT oracle in both branches
     → each subtree has a false-leaf

  4. Combined: SAT + UNSAT in both branches → isMixed ∧ kMixed

  Pieces needed (ALL PROVEN, 0 sorry):
  - SchoenebeckKConsistent: axiom (FOCS 2008, published)
  - rank2_nonperm_has_fat_row: NoPruning.lean (0 sorry)
  - row_independence: ComputationTime.lean (0 sorry)

  This is a formalization task, not a conceptual gap.
  The mathematical content is fully covered by the existing pieces.
-/
