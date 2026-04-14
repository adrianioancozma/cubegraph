/-
  CubeGraph/FregeExponential.lean — Conditional Frege Lower Bound

  Session: 047.
  Docs: experiments-ml/047_2026-04-06_roadmap-pnp/ARGUMENT.md

  STATUS: CONDITIONAL. Depends on UNPROVEN conjecture (depth_collapse).

  What IS proven here:
  - rank2_forces_different_formulas (from per_gap_derivations_differ)

  What is CONJECTURED (not proven, marked clearly):
  - branching_multiplies (CONJECTURE — equivalent to P≠NP on CG-UNSAT)
  - frege_exponential (CONJECTURE — IS P≠NP on CG-UNSAT)

  These conjectures are here for REFERENCE only. They are NOT axioms.
  They are NOT used to "prove" anything.
  The real conditional result is in DepthCollapse.lean.
-/

import CubeGraph.ProofComplexityModel
import CubeGraph.SchoenebeckAxiom
import CubeGraph.NonInvertibleTransfer
import CubeGraph.IrrationalNodes

namespace CubeGraph

/-- Rank-2 implies different gap choices produce different truth conditions.
    PROVEN from per_gap_derivations_differ. -/
theorem rank2_forces_different_formulas (G : CubeGraph)
    (i j : Fin G.cubes.length)
    (hrank : ¬(transferOp G.cubes[i] G.cubes[j]).IsRankOne)
    (hactive : ∃ g, (transferOp G.cubes[i] G.cubes[j]).rowSup g = true) :
    ∃ (g₁ g₂ : Vertex),
      G.cubes[i].isGap g₁ = true ∧ G.cubes[i].isGap g₂ = true ∧ g₁ ≠ g₂ ∧
      ∃ g : Vertex,
        transferOp G.cubes[i] G.cubes[j] g₁ g ≠
        transferOp G.cubes[i] G.cubes[j] g₂ g :=
  per_gap_derivations_differ G i j hrank hactive

/-! ## Conjectures (NOT proven, for reference only) -/

-- CONJECTURE: branching_multiplies
-- On CG-UNSAT with rank-2 on all edges, any Frege proof of ⊥ from
-- cgFormula has ≥ 2^{n/c} distinct formulas.
-- STATUS: UNPROVEN. Equivalent to P≠NP on CG-UNSAT.
-- Every attempt to prove this has been circular (see session 047 analysis).

-- CONJECTURE: frege_exponential
-- Frege proofs of CG-UNSAT are exponential.
-- STATUS: UNPROVEN. IS P≠NP.
-- Conditional version: see DepthCollapse.lean (frege_exponential_IF_depth_collapse).

end CubeGraph
