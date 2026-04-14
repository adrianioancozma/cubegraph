/-
  CubeGraph/DistinctCompositions.lean — Distinct Compositions Grow on Non-Abelian Expander

  On CubeGraph with non-abelian transfer operators (T₃*):
  the number of DISTINCT composed operators along k-hop paths
  grows exponentially with k.

  Experimentally verified:
    k=1: ~500 distinct operators
    k=2: ~4000 distinct (×8)
    k=3: ~14000 distinct (×3.5)
    Growth factor: ~5× per hop

  This means: formulas derived from different paths are about DIFFERENT
  compositions. Reuse of derived formulas is BOUNDED.

  Connection to proof complexity:
  - Bounded reuse → tree-like proof ≈ DAG proof (constant factor)
  - Resolution lb on tree-like (2^{Ω(n)}) transfers to DAG
  - Experimental: reuse_ratio ≈ 2x constant on CG (experiment 035)

  See: experiments-ml/035_2026-03-26_frege-vs-resolution/RESULTS.md
  See: experiments-ml/035_2026-03-26_frege-vs-resolution/BRAINSTORM-NUCLEAR.md
  See: experiments-ml/034_2026-03-26_lifting/ANALYSIS-CUT-REUSE.md
  See: experiments-ml/035_2026-03-26_frege-vs-resolution/SYNTHESIS-5-AGENTS.md

  STATUS (2026-03-27): Distinct compositions → bounded reuse is a CATEGORY ERROR.
  PHP has rank-1 constraints (unique compositions per path) yet exponential tree/DAG.
  The algebraic growth of distinct compositions does NOT control proof-level reuse.
  The bounded_reuse_tree_le_dag theorem below is TRIVIALLY true (just h_bound).
-/

import CubeGraph.CutReuse

namespace CubeGraph

open BoolMat

/-! ## Section 1: Distinct Compositions — Experimental Evidence

  On CubeGraph with ~42 cubes (n=10), the number of distinct
  composed transfer operators grows rapidly with path length:

    k=1: 523 distinct operators (individual edges)
    k=2: 3844 distinct (composed pairs)
    k=3: 11175 distinct (composed triples)

  Growth factor ≈ 5× per hop. Non-abelian composition generates
  MANY distinct results from the 28 elements of T₃*.

  At k hops: approximately c^k distinct compositions (c ≈ 5).
  This means: different k-hop paths give DIFFERENT operators. -/

-- REMOVED (2026-03-29 audit): distinct_compositions_grow was vacuous (body = True).
-- Direction KILLED: algebraic non-commutativity ≠ propositional non-reusability.
-- See: AXIOM-AUDIT.md

/-! ## Section 2: Distinct Compositions → Bounded Reuse

  If different paths give different compositions, then a formula
  derived from one path is IRRELEVANT for another path.

  "Relevance" = the formula appears as a premise in a derivation
  about the other path.

  Bounded distinct compositions → bounded reuse:
  - At distance k: c^k distinct compositions exist
  - A formula about ONE composition is relevant to at most
    (total paths) / c^k ≈ 1 of the c^k distinct paths
  - Reuse per formula ≈ 1 (constant)

  Experimental verification (experiment 035):
  - reuse_ratio ≈ 2.08 (constant across n=5..20)
  - slope(log(ratio) vs n) ≈ 0.01 (approximately zero)
  - 335 UNSAT instances tested -/

/-- Bounded reuse from distinct compositions.
    If reuse of any clause in a Resolution proof is bounded by R:
    then tree-like proof size ≤ R × DAG proof size.

    This is a general proof theory fact (not CG-specific). -/
theorem bounded_reuse_tree_le_dag
    (dag_size tree_size : Nat) (R : Nat)
    (h_bound : tree_size ≤ R * dag_size) :
    tree_size ≤ R * dag_size :=
  h_bound

/-! ## Section 3: Transfer from Tree-like to DAG

  If reuse ≤ R (constant) on CG:
  - tree_size ≤ R × dag_size
  - tree_size ≥ 2^{Ω(n)} (Resolution lower bound, ERLowerBound.lean)
  - → dag_size ≥ tree_size / R = 2^{Ω(n)} / R = 2^{Ω(n)}

  A constant factor R doesn't affect the exponential lower bound.

  Experimental R ≈ 2. So: dag_size ≥ 2^{Ω(n)} / 2 = 2^{Ω(n)}. -/

/-- Transfer: if tree_size ≥ lb and tree_size ≤ R × dag_size:
    then dag_size ≥ lb / R. -/
theorem tree_lb_transfers_to_dag
    (dag_size tree_size lb R : Nat)
    (h_tree_lb : tree_size ≥ lb)
    (h_reuse : tree_size ≤ R * dag_size)
    (hR : R ≥ 1) :
    dag_size * R ≥ lb :=
  Nat.le_trans h_tree_lb (Nat.mul_comm R dag_size ▸ h_reuse)

/-! ## Section 4: The Full Chain (Conditional on Bounded Reuse)

  IF reuse is bounded on CG (supported by experiment, not proven):
  1. Resolution tree-like lb ≥ 2^{Ω(n)} (ERLowerBound.lean, PROVEN)
  2. Reuse ≤ R ≈ 2 on CG (experimental, CONJECTURED)
  3. Resolution DAG lb ≥ 2^{Ω(n)} / R (from 1+2)
  4. Frege ≥ Resolution DAG (Frege simulates Resolution)

  Wait — step 4 is wrong. Frege INCLUDES Resolution.
  Frege lb ≤ Resolution lb (Frege can be faster).

  The correct step 4: IF Frege ≈ Resolution on CG (reuse constant):
  4'. Frege size ≈ Resolution DAG size (on CG specifically)
  5. → Frege ≥ 2^{Ω(n)} / R = 2^{Ω(n)}

  The "≈" in step 4' is the CONJECTURE (NOTHELPS on CG).
  Experimental evidence: reuse_ratio ≈ 2 (constant). -/

end CubeGraph
