/-
  CubeGraph/CycleIntersection.lean
  Cycle-feasible gaps and the SAT → feasible nonempty theorem.

  MAIN RESULT (sat_implies_feasible_nonempty):
    If a CubeGraph is satisfiable, then for any cycle in the graph and any
    position in that cycle, there exists a cycle-feasible gap at that position.

    Informally: SAT → ∀ cycle C in G, ∀ position i in C: I(v) ≠ ∅
    where I(v) = {g : g is cycle-feasible at position v}.

    This is the formal counterpart of Experiment 007 Phase 1, which showed
    computationally that single-node cycle intersection never empties.

  PROOF STRATEGY:
    Direct extraction from the global gap selection. No cycleOp, no trace,
    no list rotation. The satisfying gap selection restricted to cycle
    positions gives a feasible gap at every position.

  See: theory/research/TRUE-EMERGENCE.md (true emergence framework)
  See: experiments-ml/007_2026-03-04_topology-of-hardness/RESULTS-PHASE1.md
  See: CubeGraph/Holonomy.lean (uses CycleInGraph, CycleFeasibleAt for common fixed point)
-/

import CubeGraph.Theorems

namespace CubeGraph

/-! ## Section 1: Cycle-in-Graph Predicate -/

/-- Next index in a cycle (wrapping around). -/
def nextIdx (len : Nat) (h_pos : len > 0) (j : Fin len) : Fin len :=
  ⟨(j.val + 1) % len, Nat.mod_lt _ h_pos⟩

/-- A cycle `[c₁, ..., cₖ]` is "in" a CubeGraph `G` if:
    (1) It has length ≥ 2
    (2) Each cube in the cycle is a cube in G (with explicit index mapping)
    (3) Each consecutive pair (including the closing edge cₖ → c₁) has an edge in G

    The explicit index mapping `idxs` avoids ambiguity when the same cube
    appears at multiple positions in G.cubes. -/
structure CycleInGraph (G : CubeGraph) (cycle : List Cube) where
  /-- Map each cycle position to its index in G.cubes -/
  idxs : Fin cycle.length → Fin G.cubes.length
  /-- Cycle has at least 2 cubes -/
  length_ge : cycle.length ≥ 2
  /-- Each mapped cube matches the cycle cube -/
  cubes_match : ∀ j : Fin cycle.length, G.cubes[idxs j] = cycle[j]
  /-- Consecutive pairs (including closing edge) have edges in G -/
  edges_exist : ∀ j : Fin cycle.length,
    (idxs j, idxs (nextIdx cycle.length (by omega) j)) ∈ G.edges

/-! ## Section 2: Cycle-Feasible Gap -/

/-- A gap `g` is **cycle-feasible** at position `i` in a cycle if there exist
    compatible gaps at ALL other positions such that `g` sits at position `i`.

    Formally: ∃ gaps : Fin k → Vertex, such that:
    - gaps i = g
    - Each gaps j is a valid gap in cycle[j]
    - Each consecutive pair is compatible via transferOp

    This is exactly what Experiment 007 computes:
    F_C(v) = {g : g is cycle-feasible at v} = diagonal of the rotated cycleOp. -/
def CycleFeasibleAt (cycle : List Cube) (h_len : cycle.length ≥ 2)
    (i : Fin cycle.length) (g : Vertex) : Prop :=
  ∃ (gaps : Fin cycle.length → Vertex),
    gaps i = g ∧
    (∀ j : Fin cycle.length, (cycle[j]).isGap (gaps j) = true) ∧
    (∀ j : Fin cycle.length,
      transferOp (cycle[j]) (cycle[nextIdx cycle.length (by omega) j])
                 (gaps j) (gaps (nextIdx cycle.length (by omega) j)) = true)

/-! ## Section 3: Main Theorem -/

/-- **SAT implies cycle-feasible gaps are nonempty**.

    If G is satisfiable, then for any cycle in G and any position in that cycle,
    there exists at least one cycle-feasible gap.

    Proof: The satisfying gap selection `s`, restricted to the cycle positions
    via the index mapping, gives compatible gaps at every position. The gap
    `s(idxs i)` at position `i` is therefore cycle-feasible.

    This is the formal version of the Phase 1 observation that I(v) ≠ ∅
    for SAT instances. The contrapositive gives: if I(v) = ∅ at any position
    of any cycle, the formula is UNSAT. -/
theorem sat_implies_feasible_nonempty (G : CubeGraph) (h_sat : G.Satisfiable)
    (cycle : List Cube) (h_cyc : CycleInGraph G cycle)
    (i : Fin cycle.length) :
    ∃ g : Vertex, CycleFeasibleAt cycle h_cyc.length_ge i g := by
  -- Step 1: Extract gap selection from SAT witness
  obtain ⟨s, h_valid, h_compat⟩ := h_sat
  -- Step 2: Build gap assignment for the cycle from the global selection
  let gaps : Fin cycle.length → Vertex := fun j => s (h_cyc.idxs j)
  -- Step 3: The gap at position i is our witness
  refine ⟨gaps i, gaps, rfl, ?valid, ?compat⟩
  -- Sub-goal: validity — each gap is actually a gap in its cube
  case valid =>
    intro j
    -- G.cubes[idxs j] = cycle[j], and s(idxs j) is a valid gap in G.cubes[idxs j]
    rw [← h_cyc.cubes_match j]
    exact h_valid (h_cyc.idxs j)
  -- Sub-goal: compatibility — consecutive gaps satisfy the transfer operator
  case compat =>
    intro j
    -- Rewrite cycle[j] → G.cubes[idxs j] in the goal
    simp only [← h_cyc.cubes_match]
    -- The edge (idxs j, idxs j') is in G.edges; apply compatibility
    exact h_compat _ (h_cyc.edges_exist j)

/-- **Contrapositive**: if no gap is cycle-feasible at some position, the graph is UNSAT. -/
theorem empty_feasible_implies_unsat (G : CubeGraph)
    (cycle : List Cube) (h_cyc : CycleInGraph G cycle)
    (i : Fin cycle.length)
    (h_empty : ∀ g : Vertex, ¬ CycleFeasibleAt cycle h_cyc.length_ge i g) :
    ¬ G.Satisfiable := by
  intro h_sat
  obtain ⟨g, hg⟩ := sat_implies_feasible_nonempty G h_sat cycle h_cyc i
  exact h_empty g hg

end CubeGraph
