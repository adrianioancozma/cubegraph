/-
  CubeGraph/CutReuse.lean — Cut Formula Reuse on Non-Abelian CubeGraph

  The gap Frege > Resolution comes from CUT: intermediate formulas
  derived once, reused many times. On abelian CSPs (Z/2Z): uniform
  formulas → max reuse → Frege poly. On non-abelian CSPs (T₃*):
  non-uniform formulas → bounded reuse → Frege ≈ Resolution.

  This file formalizes:
  - The concept of "region-specific" formulas (depend on local composition)
  - Non-abelianity limits cross-region reuse
  - Connection: bounded reuse + Resolution lb → Frege lb

  See: experiments-ml/034_2026-03-26_lifting/BRAINSTORM-NOTHELPS-NUCLEAR.md
  See: experiments-ml/034_2026-03-26_lifting/ANALYSIS-CUT-REUSE.md
  See: experiments-ml/035_2026-03-26_frege-vs-resolution/SYNTHESIS-5-AGENTS.md

  STATUS (2026-03-27): Path D (cut-reuse from non-commutativity) has FATAL FLAW.
  Algebraic non-commutativity ≠ propositional non-reusability.
  PHP counterexample: rank-1 constraints but exponential tree/DAG ratio.
  The NOTHELPS conjecture (Section 4) remains the strongest formulation.
-/

import CubeGraph.Basic
import CubeGraph.MonotoneAxioms
import CubeGraph.ComputationalNoether

namespace CubeGraph

open BoolMat

/-! ## Section 1: Composition is Non-Commutative

  Different orderings of transfer operators give different results.
  This means: formulas derived from region A are DIFFERENT from
  formulas needed in region B (because paths differ). -/

/-- Two transfer operator compositions in different order give different results.
    This is the "non-abelian witness" — the foundation of limited reuse. -/
theorem composition_order_matters :
    ∃ (M₁ M₂ : BoolMat 8), mul M₁ M₂ ≠ mul M₂ M₁ := by
  -- From ComputationalNoether.lean: third component of summary
  obtain ⟨_, _, h_nc, _, _, _⟩ := computational_noether_summary
  exact h_nc

/-! ## Section 2: Path-Dependent Composition

  The composition of transfer operators along a path depends on:
  1. Which edges are in the path (determined by graph structure)
  2. The ORDER of edges (determined by path direction)

  On a non-abelian monoid: changing the order changes the result.
  Different paths between the same endpoints give different compositions. -/

/-- A path in a CubeGraph is a sequence of adjacent cube indices. -/
def CubePath (G : CubeGraph) := List (Fin G.cubes.length)

/-- The composed transfer operator along a path of length ≥ 2. -/
def pathComposition (G : CubeGraph) : CubePath G → BoolMat 8
  | [] => one  -- identity for empty path
  | [_] => one  -- single cube, no composition
  | (c₁ :: c₂ :: rest) =>
    mul (transferOp (G.cubes[c₁]) (G.cubes[c₂])) (pathComposition G (c₂ :: rest))

/-! ## Section 3: Region Specificity (Conceptual)

  A "region" of a CubeGraph is a connected subgraph.
  Formulas derived from region A are about the SPECIFIC compositions
  in that region. On a non-abelian monoid: these compositions are
  DIFFERENT from compositions in region B.

  Consequence: a cut formula derived from region A has LIMITED REUSE
  in other regions (the compositions don't match).

  The FORMAL bound on reuse requires:
  1. Defining "relevance" of a formula to a region
  2. Showing: non-abelian → cross-region relevance is bounded
  3. Bounding total reuse from bounded cross-region relevance

  Steps 2-3 are conjectural (= the NOTHELPS conjecture restricted
  to proof systems on non-abelian CSPs). -/

-- REMOVED (2026-03-29 audit): expander_paths_distinct_compositions was vacuous (body = True).
-- Direction KILLED: algebraic distinctness ≠ propositional non-reusability.
-- See: AXIOM-AUDIT.md

/-! ## Section 4: The NOTHELPS Proof System Conjecture

  CONJECTURE (restricted to proof systems):
  On CubeGraph with Pol = projections and T₃* aperiodic:
    Frege proof size ≤ poly(n) × Resolution proof size

  Equivalently: cuts save at most polynomial work on CG-UNSAT.

  If true: Resolution lb 2^{Ω(n)} (ERLowerBound.lean)
  → Frege lb ≥ 2^{Ω(n)} / poly(n) = 2^{Ω(n)}
  → P ≠ NP

  Evidence:
  - Non-abelianity limits cut-reuse (this file)
  - No inverse structure for NOT to exploit (BandSemigroup.lean)
  - Erase-only axioms → monotone effect (MonotoneAxioms.lean)
  - All known Frege > Resolution gaps use abelian/group structure (Tseitin = Z/2Z) -/

end CubeGraph
