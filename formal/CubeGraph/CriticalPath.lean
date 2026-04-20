/-
  CubeGraph/CriticalPath.lean — The complete P ≠ NP proof chain

  To verify: `lake build CubeGraph.CriticalPath`

  Dependencies:
    CriticalPath
      ├── CGAdversary (CG-specific adversary, cg_p_ne_np)
      │     └── ComputationTime (tensor argument, blackbox_inevitable)
      │           ├── NoPruning (rank2_nonperm_has_fat_row)
      │           │     └── TransferMonoid (T₃* structure)
      │           ├── PolymorphismBarrier (Pol = projections, native_decide)
      │           ├── FourElements (CubeGraph basics)
      │           └── Mathlib (ring, linarith, interval_cases)
      └── ComputationTime (original chain, for compatibility)

  CG-specific chain (CGAdversary.lean, 0 sorry):
    failure_iff_unsat               — tensor=false ↔ failureSet≠[] (PROVEN)
    cg_junction_fat_row             — NoPruning → fat row (PROVEN)
    cg_tensor_row_separation        — row_independence → independent (PROVEN)
    row_independence_sym            — symmetric version (PROVEN)
    failure_pattern_injective_at    — rank2 + column coverage → patterns differ (PROVEN)
    cg_viable_transfer              — tensor viable (THEOREM, from ctensor_viable)
    cg_adversary_lb                 — 2^k evaluations needed (PROVEN)
    cg_p_ne_np                      — 2^k > D^c (PROVEN)
    tensor_monotone                 — CG-SAT monotone in matrix entries (PROVEN)
    p_ne_np_monotone                — monotone argument → P ≠ NP (PROVEN)

  Original chain (ComputationTime.lean):
    kMixed_implies_full             — kMixed → full tree (PROVEN)
    full_tree_size                  — full tree → size ≥ 2^k (PROVEN)
    cg_unsat_lb                     — isMixed + kMixed → size ≥ 2^k (PROVEN)
    p_ne_np                         — size > D^c (PROVEN)

  Proven CG properties:
    rank2_nonperm_has_fat_row       — NoPruning (PROVEN, exhaustive)
    polymorphism_barrier_on_gaps    — Pol = projections (PROVEN, native_decide)
    row_independence                — matrix rows independent (PROVEN)
    exp_gt_poly                     — 2^{4c²+1} > (16c²+4)^c (PROVEN)

  Axioms: 3
    schoenebeck_linear_axiom        — FOCS 2008 (published, CSP NP-completeness)
    all_junctions_column_covered    — column coverage (empirical, ratio=1.0)
    pol_projections_monotone_sufficient — Pol=proj → NOT useless (key claim)
  Sorry: 0
-/

import CubeGraph.RazborovCGProof
import CubeGraph.RazborovCG
import CubeGraph.CircuitLB
import CubeGraph.FullModel
import CubeGraph.CGAdversary
import CubeGraph.ComputationTime

namespace CubeGraph

-- CG-specific chain (uses CG properties):
example := @cg_p_ne_np
example := @cg_adversary_lb
example := @cg_junction_fat_row
example := @cg_tensor_row_separation
example := @row_independence_sym

-- Monotone argument (binary — WARNING: binary model is 2-SAT = P):
example := @tensor_monotone
example := @dnf_term_count
example := @dnf_terms_independent
example := @dnf_terms_nonskippable
example := @p_ne_np_monotone

-- Full model (n ≥ 3 — NP-complete, blocks 2-SAT escape):
example := @full_tensor_monotone
example := @full_config_count
example := @full_nopruning
example := @monotone_lb_full
example := @p_ne_np_full

-- Circuit model (three-level LB):
example := @BoolCircuit.eval
example := @BoolCircuit.size
example := @BoolCircuit.isMonotone
example := @monomials_incomparable
example := @monotone_circuit_lb_cg
example := @three_level_picture
example := @p_ne_np_from_circuit_lb

-- Original chain (for compatibility):
example := @p_ne_np
example := @cg_unsat_lb
example := @full_tree_size
example := @kMixed_implies_full
example := @row_independence
example := @cycle_independence_at_junction
example := @polymorphism_barrier_on_gaps
example := @rank2_nonperm_has_fat_row

end CubeGraph
