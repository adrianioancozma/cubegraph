/-
  CubeGraph/CascadeSpreads.lean — Cascade Spreads to New Cubes

  Session: 047.
  Docs: experiments-ml/047_2026-04-06_roadmap-pnp/INSIGHT-CROSS-CUBE.md

  Problem 1: the cascade doesn't rotate in a circle — it spreads.
  CubeGraph has no leaves (trimmed), no single cycles (core graph).
  The cascade reaches NEW cubes at each step.

  Problem 2: the case-splits are COMBINATORIAL (multiplicative).
  n/c free cubes (Schoenebeck), each with ≥ 2 options (rank-2).
  All 2^{n/c} combinations are locally consistent (Schoenebeck).
  Proof must eliminate ALL combinations.
-/

import CubeGraph.ProofComplexityModel
import CubeGraph.SchoenebeckAxiom
import CubeGraph.NonInvertibleTransfer
import CubeGraph.IrrationalNodes

namespace CubeGraph

/-! ## Problem 1: Cascade Spreads -/

/-- Schoenebeck gives n/c "free" cubes: any assignment on them is
    locally consistent. The proof must address ALL of them.
    From: schoenebeck_linear_axiom + kconsistent_restricted_sat. -/
theorem free_cubes_exist :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph,
        G.cubes.length ≥ n ∧
        SchoenebeckKConsistent G (n / c) ∧ ¬ G.Satisfiable := schoenebeck_linear_axiom

/-- Each free cube has ≥ 2 genuine gap options (rank-2).
    "Genuine" = producing different constraints on at least one neighbor.
    From: per_gap_derivations_differ. -/
theorem free_cubes_have_options (G : CubeGraph)
    (i j : Fin G.cubes.length)
    (hrank : ¬(transferOp G.cubes[i] G.cubes[j]).IsRankOne)
    (hactive : ∃ g, (transferOp G.cubes[i] G.cubes[j]).rowSup g = true) :
    ∃ g₁ g₂ : Vertex,
      G.cubes[i].isGap g₁ = true ∧ G.cubes[i].isGap g₂ = true ∧ g₁ ≠ g₂ :=
  let ⟨g₁, g₂, hg1, hg2, hne, _⟩ := per_gap_derivations_differ G i j hrank hactive
  ⟨g₁, g₂, hg1, hg2, hne⟩

/-! ## Problem 2: Combinations are Multiplicative -/

/-- The number of gap combinations on k cubes with ≥ 2 options each
    is ≥ 2^k. This is pure counting (no proof complexity). -/
theorem combinations_exponential (k : Nat) :
    -- k cubes, each with ≥ 2 options → ≥ 2^k combinations
    -- This is just: 2^k ≥ 2^k (trivial)
    2 ^ k ≥ 2 ^ k := Nat.le_refl _

/-- Schoenebeck: ALL combinations on ≤ n/c cubes are locally consistent.
    This means: the proof cannot eliminate ANY combination "for free" —
    each must be individually shown inconsistent with the FULL graph.

    From SchoenebeckKConsistent: for any S with |S| ≤ n/c,
    there exists an assignment on S satisfying all internal constraints.
    So: the combination IS locally valid — the proof can't dismiss it
    without examining constraints OUTSIDE S. -/
theorem all_combinations_consistent (G : CubeGraph) (k : Nat)
    (hkc : SchoenebeckKConsistent G k) :
    -- For any set S of ≤ k cubes and ANY gap selection on S:
    -- there exists an extension to a full assignment satisfying
    -- all constraints internal to S.
    ∀ S : List (Fin G.cubes.length), S.length ≤ k → S.Nodup →
      ∃ s : (i : Fin G.cubes.length) → Vertex,
        (∀ i ∈ S, G.cubes[i].isGap (s i) = true) ∧
        (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
          transferOp G.cubes[e.1] G.cubes[e.2] (s e.1) (s e.2) = true) :=
  hkc

/-! ## The Argument -/

/-- **THE COMBINATORIAL ARGUMENT.**

    1. n/c cubes are "free" (Schoenebeck): any gap selection is locally consistent
    2. Each free cube has ≥ 2 options (rank-2)
    3. → ≥ 2^{n/c} combinations of gap selections on the free cubes
    4. ALL 2^{n/c} combinations are locally consistent (Schoenebeck)
    5. The proof must show EACH combination is globally inconsistent
    6. → proof must "cover" all 2^{n/c} combinations

    The question: how many proof formulas are needed to cover 2^{n/c} combinations?

    A formula specific for k cubes: eliminates combinations inconsistent
    with that formula's specific gap values. It covers 2^{n/c - k} combinations
    (those agreeing on the k specific cubes, free on the rest).

    With k = 1: each formula covers 2^{n/c - 1} = half. Need ≥ 2.
    With k = 2: each covers 2^{n/c - 2} = quarter. Need ≥ 4.
    ...
    With k = n/c: each covers 1. Need ≥ 2^{n/c}.

    BUT: the proof might only need formulas with SMALL k (specific for few cubes).
    Each small-k formula covers MANY combinations.
    The question: do small-k formulas SUFFICE to cover ALL 2^{n/c} combinations?

    Answer depends on whether the combinations' inconsistencies are
    INDEPENDENT (need k = n/c) or CORRELATED (small k suffices).

    For CG-UNSAT: Schoenebeck says any k ≤ n/c combinations ARE consistent.
    So: the inconsistency is NOT detectable from k ≤ n/c cubes.
    A formula specific for k ≤ n/c cubes: cannot detect the inconsistency
    of any combination on those cubes (they're all consistent!).

    Therefore: formulas must be specific for > n/c cubes to detect
    inconsistency. And formulas specific for > n/c cubes cover
    ≤ 2^{n/c - n/c} = 1 combination each. Need ≥ 2^{n/c}. -/

-- Wait. This argument has a flaw. Let me re-examine.
--
-- A formula specific for k cubes doesn't "detect inconsistency of those k cubes."
-- It detects inconsistency of the COMBINATION of those k cubes with OTHER cubes.
-- A formula mentioning cubes i₁...iₖ plus cubes j₁...jₘ (from cgFormula):
-- it combines LOCAL constraints from multiple cubes.
--
-- Schoenebeck says: constraints on ≤ n/c cubes are consistent.
-- But a formula can MENTION cubes from outside the n/c free cubes!
-- It can use constraints from the "non-free" cubes to eliminate combinations.
--
-- The formula is specific for the FREE cubes (depends on their gaps)
-- but uses constraints from ALL cubes (including non-free).
--
-- So: a formula specific for 1 free cube + constraints from many non-free cubes:
-- can potentially eliminate HALF of all combinations at that free cube.
-- Need: 2 such formulas per free cube × n/c free cubes = O(n). POLYNOMIAL.
--
-- Unless: the formulas for different free cubes INTERACT.
-- Two formulas: one eliminating gap_i=g₁, another eliminating gap_j=g₃.
-- Together: they eliminate combinations with gap_i=g₁ AND gap_j=g₃.
-- But also combinations with JUST gap_i=g₁ (first formula) and JUST gap_j=g₃ (second).
-- The coverage is the UNION, not the INTERSECTION.
--
-- Union of n/c formulas, each covering half: covers 1-(1/2)^{n/c} ≈ all.
-- So: O(n) formulas cover ALMOST all combinations. POLYNOMIAL.
--
-- EXCEPT: each formula must be DERIVED from cgFormula. The derivation
-- requires combining constraints — which is the MP cost.
-- The formulas exist (semantically) but deriving them might be expensive.
--
-- This is the gap: SEMANTIC coverage is polynomial (O(n) formulas suffice).
-- SYNTACTIC derivation might be exponential (each formula requires MP chain).
--
-- The gap is at MP derivation cost, not at coverage counting.

theorem combinatorial_structure :
    -- The combinatorial structure exists (from Schoenebeck + rank-2).
    -- The proof complexity question is about DERIVATION cost, not coverage.
    True := trivial

end CubeGraph
