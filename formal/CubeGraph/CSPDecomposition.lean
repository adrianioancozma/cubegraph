/-
  CubeGraph/CSPDecomposition.lean

  CSP Decomposition: CubeGraph SAT = f(gap_masks) on fixed topology.

  Topology (variable triples, edges) is FIXED.
  Gap masks (which vertices are gaps) VARY — they are the "truth tables."

  Key: Cube.withMask replaces gap mask preserving variables/topology.
  satWithMasks defines SAT as explicit function of masks on fixed topology.

  See: Basic.lean (Cube, CubeGraph, Satisfiable)
  See: QueryLowerBound.lean (DT ≥ Ω(n))
  See: experiments-ml/024/PAS3C2-PLAN-CSP-DECOMPOSITION.md
-/

import CubeGraph.QueryLowerBound

-- ═════════════════════════════════════════════════════════════════════
-- Cube-level definitions (ROOT namespace — needed for dot notation)
-- ═════════════════════════════════════════════════════════════════════

/-- Replace the gap mask of a cube, keeping variable triples. -/
def Cube.withMask (c : Cube) (mask : Fin 256) (h : mask.val > 0) : Cube where
  var₁ := c.var₁; var₂ := c.var₂; var₃ := c.var₃
  var₁_pos := c.var₁_pos; var₂_pos := c.var₂_pos; var₃_pos := c.var₃_pos
  vars_distinct := c.vars_distinct
  gapMask := mask; gaps_nonempty := h

/-- Variables unchanged by withMask. -/
theorem Cube.vars_withMask (c : Cube) (mask : Fin 256) (h : mask.val > 0) :
    (c.withMask mask h).vars = c.vars := by
  rfl

/-- Shared variables unchanged by withMask (topology preserved). -/
theorem Cube.sharedVars_withMask (c₁ c₂ : Cube) (m₁ m₂ : Fin 256) (h₁ h₂) :
    Cube.sharedVars (c₁.withMask m₁ h₁) (c₂.withMask m₂ h₂) =
    Cube.sharedVars c₁ c₂ := by
  simp [Cube.sharedVars, Cube.vars_withMask]

/-- Link weight unchanged by withMask. Edge structure is preserved. -/
theorem Cube.linkWeight_withMask (c₁ c₂ : Cube) (m₁ m₂ : Fin 256) (h₁ h₂) :
    Cube.linkWeight (c₁.withMask m₁ h₁) (c₂.withMask m₂ h₂) =
    Cube.linkWeight c₁ c₂ := by
  simp [Cube.linkWeight, Cube.sharedVars_withMask]

/-- isGap with original mask is unchanged. -/
theorem Cube.isGap_withMask_self (c : Cube) (v : Vertex) :
    (c.withMask c.gapMask c.gaps_nonempty).isGap v = c.isGap v := by
  rfl

/-- transferOp with original masks is unchanged. -/
theorem CubeGraph.transferOp_withMask_self (c₁ c₂ : Cube) :
    CubeGraph.transferOp (c₁.withMask c₁.gapMask c₁.gaps_nonempty)
               (c₂.withMask c₂.gapMask c₂.gaps_nonempty) =
    CubeGraph.transferOp c₁ c₂ := by
  funext g₁ g₂
  simp [CubeGraph.transferOp, Cube.isGap_withMask_self,
        Cube.sharedVars_withMask, Cube.vars_withMask]

-- ═════════════════════════════════════════════════════════════════════
-- CubeGraph-level definitions
-- ═════════════════════════════════════════════════════════════════════

namespace CubeGraph

/-! ## Section 1: SAT as function of masks on fixed topology -/

/-- **SAT with replaced gap masks**: Satisfiability where gap masks are
    parameters but topology (variable triples, edges) is from G.

    This is the "outer function f" in the lifting decomposition:
    f(masks) = SAT on topology(G) with given gap masks.

    Input space has PRODUCT STRUCTURE: one Fin 256 per cube. -/
def satWithMasks (G : CubeGraph) (masks : Fin G.cubes.length → Fin 256)
    (hmasks : ∀ i, (masks i).val > 0) : Prop :=
  ∃ s : Fin G.cubes.length → Vertex,
    (∀ i, (Cube.withMask (G.cubes[i]) (masks i) (hmasks i)).isGap (s i) = true) ∧
    (∀ e ∈ G.edges,
      transferOp (Cube.withMask (G.cubes[e.1]) (masks e.1) (hmasks e.1))
                 (Cube.withMask (G.cubes[e.2]) (masks e.2) (hmasks e.2))
                 (s e.1) (s e.2) = true)

/-! ## Section 2: Equivalence with Satisfiable -/

/-- **Decomposition faithful**: satWithMasks with original masks = Satisfiable. -/
theorem satWithMasks_original (G : CubeGraph) :
    satWithMasks G (fun i => (G.cubes[i]).gapMask)
                   (fun i => (G.cubes[i]).gaps_nonempty)
    ↔ G.Satisfiable := by
  simp only [satWithMasks, Satisfiable, validSelection, compatibleSelection]
  constructor
  · rintro ⟨s, hv, hc⟩
    refine ⟨s, fun i => ?_, fun e he => ?_⟩
    · rw [← Cube.isGap_withMask_self]; exact hv i
    · rw [← transferOp_withMask_self]; exact hc e he
  · rintro ⟨s, hv, hc⟩
    refine ⟨s, fun i => ?_, fun e he => ?_⟩
    · rw [Cube.isGap_withMask_self]; exact hv i
    · rw [transferOp_withMask_self]; exact hc e he

/-! ## Section 3: CSP Decomposition Summary -/

/-- **CSP Decomposition**: CubeGraph SAT decomposes as:

    1. **Topology** (fixed): variable triples + edge structure
       - Preserved under mask changes (linkWeight_withMask)
    2. **Truth tables** (variable): gap masks (one Fin 256 per cube)
       - satWithMasks parameterizes SAT by masks
    3. **Product structure**: each cube = one coordinate (Fin 256)
    4. **DT ≥ Ω(n)**: from QueryLowerBound.decision_tree_depth_scaling
    5. **Lifting-ready**: f = satWithMasks, DT(f) ≥ Ω(n),
       product structure → GPW applies (Step 3)

    Zero new axioms. -/
theorem csp_decomposition :
    -- (1) Topology preserved under withMask
    (∀ (c₁ c₂ : Cube) (m₁ m₂ : Fin 256) (h₁ : m₁.val > 0) (h₂ : m₂.val > 0),
      Cube.linkWeight (c₁.withMask m₁ h₁) (c₂.withMask m₂ h₂) = Cube.linkWeight c₁ c₂)
    -- (2) Decomposition faithful
    ∧ (∀ G : CubeGraph,
        satWithMasks G (fun i => (G.cubes[i]).gapMask) (fun i => (G.cubes[i]).gaps_nonempty)
        ↔ G.Satisfiable)
    -- (3) DT ≥ Ω(n) applies
    ∧ (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
        ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
          ∀ (S : List (Fin G.cubes.length)), S.Nodup → S.length < n / c →
            ∃ s : (i : Fin G.cubes.length) → Vertex,
              (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
              (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
                transferOp (G.cubes[e.1]) (G.cubes[e.2])
                  (s e.1) (s e.2) = true)) :=
  ⟨Cube.linkWeight_withMask,
   satWithMasks_original,
   decision_tree_depth_scaling⟩

end CubeGraph
