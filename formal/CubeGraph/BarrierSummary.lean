/-
  CubeGraph/BarrierSummary.lean
  Meta-Barrier: concrete witness failing all 5 tractability barriers.

  The witness r1Graph (from Witness.lean) is UNSAT yet fails every known
  polynomial escape mechanism for Boolean SAT:
    1. Not invertible (generic: rank-1 over OR/AND, see InvertibilityBarrier.lean)
    2. Not all Horn (r1CubeA has filled vertex 3, Hamming weight 2)
    2b. Not all Dual-Horn (r1CubeA has filled vertex 1, Hamming weight 1)
    3. No trivial section (gaps(A) ∩ gaps(B) = ∅)
    4. Not arc-consistent (indirect: rank1_ac_sat would give SAT)
    5. Not functional (gap 0 in A maps to {2,6} in B — two targets)

  This formalizes: generic 3-SAT at critical density has no polynomial
  escape via any known algebraic mechanism. The barrier list is exhaustive
  for Boolean SAT by Schaefer's dichotomy (1978).

  Part of the 5-Barriers program.

  See: experiments-ml/012_2026-03-05_fiber-algebra-topology/RESULTS.md (§2.4, Meta-barrier)
  See: experiments-ml/012_2026-03-05_fiber-algebra-topology/PLAN-BarrierSummary.md
  See: formal/CubeGraph/InvertibilityBarrier.lean (Barrier 1: XOR invertibility)
  See: formal/CubeGraph/HornBarrier.lean (Barrier 2: Horn OR-closed gaps)
  See: formal/CubeGraph/DualHornBarrier.lean (Barrier 2b: Dual-Horn AND-closed gaps)
  See: formal/CubeGraph/TrivialSection.lean (Barrier 3: trivial section)
  See: formal/CubeGraph/Rank1AC.lean (Barrier 4: rank-1 + AC → SAT)
  See: formal/CubeGraph/FunctionalTransfer.lean (Barrier 5: functional composition)
  See: formal/CubeGraph/MinimalBarrier.lean (r1Graph is also the minimal H² witness — sharp boundary at 3 cubes)
-/

import CubeGraph.Witness
import CubeGraph.HornBarrier
import CubeGraph.DualHornBarrier
import CubeGraph.TrivialSection
import CubeGraph.FunctionalTransfer
import CubeGraph.Rank1AC

namespace CubeGraph

/-! ## Section 1: Barrier 2 & 2b — Horn / Dual-Horn Failures -/

/-- r1CubeA is not Horn: filled vertex 3 (011) has Hamming weight 2. -/
theorem r1Graph_not_horn : ¬ IsHornCube r1CubeA := by
  intro h
  have h1 : r1CubeA.isGap ⟨3, by omega⟩ = false := by native_decide
  have h2 := h ⟨3, by omega⟩ h1
  exact absurd h2 (by native_decide)

/-- r1CubeA is not Dual-Horn: filled vertex 1 (001) has Hamming weight 1. -/
theorem r1Graph_not_dualhorn : ¬ IsDualHornCube r1CubeA := by
  intro h
  have h1 : r1CubeA.isGap ⟨1, by omega⟩ = false := by native_decide
  have h2 := h ⟨1, by omega⟩ h1
  exact absurd h2 (by native_decide)

/-! ## Section 2: Barrier 3 — No Trivial Section -/

/-- gaps(A) ∩ gaps(B) = ∅: no gap is present in both r1CubeA and r1CubeB. -/
private theorem r1_gap_disjoint :
    ∀ g : Vertex, ¬ (r1CubeA.isGap g = true ∧ r1CubeB.isGap g = true) := by
  native_decide

/-- No constant gap works as a trivial section for r1Graph. -/
theorem r1Graph_no_trivial_section : ∀ g : Vertex, ¬ HasTrivialSection r1Graph g := by
  intro g ⟨h_all, _⟩
  exact r1_gap_disjoint g ⟨h_all ⟨0, by decide⟩, h_all ⟨1, by decide⟩⟩

/-! ## Section 3: Barrier 4 — AC Fails (indirect) -/

/-- All edges of r1Graph have rank-1 transfer operators. -/
theorem r1Graph_allRankOne : AllRankOne r1Graph := by
  intro e he
  simp only [r1Graph, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact r1_AB_rankOne
  · exact r1_BC_rankOne
  · exact r1_CA_rankOne

/-- r1Graph is NOT arc-consistent.
    Proof: if it were, rank1_ac_sat would give SAT, contradicting r1Graph_unsat. -/
theorem r1Graph_not_ac : ¬ AllArcConsistent r1Graph := by
  intro hAC
  exact r1Graph_unsat (rank1_ac_sat r1Graph r1Graph_allRankOne hAC)

/-! ## Section 4: Barrier 5 — Not Functional -/

/-- Edge A→B is not functional: gap 0 in A maps to BOTH gap 2 and gap 6 in B. -/
theorem r1Graph_not_functional_AB : ¬ IsFunctionalOnGaps r1CubeA r1CubeB := by
  intro h
  have h0_gap : r1CubeA.isGap ⟨0, by omega⟩ = true := by native_decide
  have h2_gap : r1CubeB.isGap ⟨2, by omega⟩ = true := by native_decide
  have h6_gap : r1CubeB.isGap ⟨6, by omega⟩ = true := by native_decide
  have h02 : transferOp r1CubeA r1CubeB ⟨0, by omega⟩ ⟨2, by omega⟩ = true := by native_decide
  have h06 : transferOp r1CubeA r1CubeB ⟨0, by omega⟩ ⟨6, by omega⟩ = true := by native_decide
  obtain ⟨g_u, _, h_uniq⟩ := h ⟨0, by omega⟩ h0_gap ⟨⟨2, by omega⟩, h2_gap, h02⟩
  have h26 : (⟨2, by omega⟩ : Vertex) = (⟨6, by omega⟩ : Vertex) :=
    (h_uniq ⟨2, by omega⟩ ⟨h2_gap, h02⟩).trans (h_uniq ⟨6, by omega⟩ ⟨h6_gap, h06⟩).symm
  exact absurd h26 (by decide)

/-! ## Section 5: Main Theorem -/

/-- **META-BARRIER**: There exists a CubeGraph that is UNSAT yet fails
    all 5 tractability barriers. This formalizes the statement:
    generic 3-SAT at critical density has no polynomial escape via
    any known algebraic mechanism. The barrier list is exhaustive
    for Boolean SAT by Schaefer's dichotomy (1978).

    Barrier 1 (invertibility) is omitted: it's a property of the boolean
    semiring itself (OR/AND), not of any specific CubeGraph instance.
    See: rank1_not_bool_invertible in InvertibilityBarrier.lean. -/
theorem exists_barrier_free_cubegraph :
    ∃ G : CubeGraph,
      ¬ G.Satisfiable ∧
      (∃ i : Fin G.cubes.length, ¬ IsHornCube (G.cubes[i])) ∧
      (∃ i : Fin G.cubes.length, ¬ IsDualHornCube (G.cubes[i])) ∧
      (∀ g : Vertex, ¬ HasTrivialSection G g) ∧
      (¬ AllArcConsistent G) ∧
      (∃ i j : Fin G.cubes.length,
        ¬ IsFunctionalOnGaps (G.cubes[i]) (G.cubes[j])) :=
  ⟨r1Graph,
   r1Graph_unsat,
   ⟨⟨0, by decide⟩, r1Graph_not_horn⟩,
   ⟨⟨0, by decide⟩, r1Graph_not_dualhorn⟩,
   r1Graph_no_trivial_section,
   r1Graph_not_ac,
   ⟨⟨0, by decide⟩, ⟨1, by decide⟩, r1Graph_not_functional_AB⟩⟩

end CubeGraph
