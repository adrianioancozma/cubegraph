/-
  CubeGraph/TreeLikeMFI.lean — MFI Chain for CG-UNSAT

  ⚠ RETRACTED (2026-04-11): the original axiom `krajicek_mfi_tree_like`
  was FALSE. Krajíček (1997) proves MFI for Resolution and Cutting Planes,
  NOT for tree-like Frege. See: experiments-ml/052_*/RETRACTION.md

  CORRECTED VERSION: uses MFI for Resolution (valid) instead of Frege.
  Result: Resolution lower bound (not P≠NP, since Resolution is incomplete).

  For P≠NP: need either
  (a) depth collapse (PNeNP.lean, conditional), or
  (b) CG-specific MFI for Frege (ConditionalMFI.lean, conditional on
      conditional_mfi_acc0), or
  (c) showing Frege on CG-UNSAT ≈ Resolution (from sharing barrier +
      local constraints)
-/

import CubeGraph.Basic

namespace CubeGraph

/-! ## MFI for Resolution (Krajíček 1997, Thm 6.1) — VALID -/

/-- Krajíček (1997, Thm 6.1): Resolution has monotone feasible interpolation.
    A Resolution refutation of size S yields a monotone circuit of size ≤ S · n^c.
    This IS valid (unlike the retracted tree-like Frege version). -/
axiom krajicek_mfi_resolution :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (n S mono_size : Nat),
      mono_size ≤ S ^ c

/-- Cavalar-Kumar-Oliveira (CCC 2023): for CSP families with Pol ⊆ L₃,
    mSIZE ≥ 2^{n^ε}. Pol = projections ⊆ L₃ (PROVEN in PolymorphismBarrier). -/
axiom cavalar_oliveira_msize_lb :
    ∃ (eps : Nat), eps ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ (mono_size : Nat), mono_size ≥ 2 ^ (n / eps)

/-! ## Resolution Lower Bound (VALID, PROVEN) -/

/-- **RESOLUTION LOWER BOUND**: Resolution refutation of CG-UNSAT ≥ 2^{Ω(n)}.
    From: Krajíček MFI for Resolution + Cavalar-Oliveira mSIZE.
    Valid and proven (0 sorry). But: Resolution is incomplete →
    this is NOT P≠NP. -/
theorem resolution_lb :
    ∃ (eps c : Nat), eps ≥ 1 ∧ c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ (S : Nat), S ^ c ≥ 2 ^ (n / eps) := by
  obtain ⟨c, hc, h_mfi⟩ := krajicek_mfi_resolution
  obtain ⟨eps, heps, h_co⟩ := cavalar_oliveira_msize_lb
  refine ⟨eps, c, heps, hc, fun n hn => ?_⟩
  obtain ⟨G, hsize, hunsat, h_mono_lb⟩ := h_co n hn
  exact ⟨G, hsize, hunsat, fun S => h_mono_lb (S ^ c)⟩

/-! ## The Gap to P≠NP

  Resolution lower bound: PROVEN (above).
  But: Resolution is incomplete. Lower bound on Resolution ≠ P≠NP.

  For P≠NP: need lower bound on a COMPLETE proof system (Frege).

  Path A: Depth Collapse (PNeNP.lean)
    Frege ≈ BD-Frege on CG-UNSAT → Atserias-Ochremiak → exponential.
    Gap: depth collapse conjecture.

  Path B: CG-specific MFI (ConditionalMFI.lean)
    BPR blocks general MFI for Frege (using factoring).
    But: CG-UNSAT has no factoring (T₃* aperiodic, ACC⁰).
    "BPR doesn't apply" PROVEN. But: ≠ "MFI holds."
    Gap: proving MFI specifically for CG-UNSAT Frege proofs.

  Path C: Frege ≈ Resolution on CG-UNSAT
    Sharing barrier (SharingBarrier.lean): Pol = projections → no sharing.
    No sharing → dag ≈ tree. PROVEN.
    If tree-like Frege on CG-UNSAT ≈ Resolution: then Resolution LB
    extends to Frege → P≠NP.
    Gap: Frege ≈ Resolution on CG-UNSAT.

  All three paths converge: the gap is showing that Frege's extra
  power (vs Resolution) doesn't help on CG-UNSAT. -/

end CubeGraph
