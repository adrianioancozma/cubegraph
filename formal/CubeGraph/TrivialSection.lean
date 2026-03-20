/-
  CubeGraph/TrivialSection.lean
  Barrier 3: Trivial Section (0-valid / 1-valid)

  A CubeGraph with a constant global section of the gap sheaf is satisfiable.
  Captures Schaefer's 0-valid (g=7) and 1-valid (g=0) tractable classes.

  Part of the 5-Barriers program: five independent tractability mechanisms
  for Boolean SAT, exhaustive by Schaefer's dichotomy (1978).

  See: experiments-ml/012_2026-03-05_fiber-algebra-topology/RESULTS.md (§2, Barrier 3)
  See: experiments-ml/012_2026-03-05_fiber-algebra-topology/G7-A.md (File 1, implementation plan)
  See: experiments-ml/012_2026-03-05_fiber-algebra-topology/PLAN-TrivialSection.md
  See: theory/foundations/06-empty-vertex-duality.md (gap = satisfying assignment)
  See: formal/CubeGraph/InvertibilityBarrier.lean (Barrier 1: XOR invertibility)
  See: formal/CubeGraph/HornBarrier.lean (Barrier 2: Horn OR-closed gaps)
  See: formal/CubeGraph/DualHornBarrier.lean (Barrier 2b: Dual-Horn AND-closed gaps)
  See: formal/CubeGraph/Rank1AC.lean (Barrier 4: rank-1 + AC → SAT)
  See: formal/CubeGraph/FunctionalTransfer.lean (Barrier 5: functional composition)
  See: formal/CubeGraph/BarrierSummary.lean (Meta: witness failing all 5 barriers)
-/

import CubeGraph.Basic

namespace CubeGraph

/-- A CubeGraph has a trivial section at gap g if g is a gap in every cube
    and self-compatible across every edge. Sheaf-theoretic: a constant
    global section of the gap sheaf. -/
def HasTrivialSection (G : CubeGraph) (g : Vertex) : Prop :=
  (∀ i : Fin G.cubes.length, (G.cubes[i]).isGap g = true) ∧
  (∀ e, e ∈ G.edges → transferOp (G.cubes[e.1]) (G.cubes[e.2]) g g = true)

/-- **Barrier 3**: A CubeGraph with a trivial section is satisfiable.
    Proof: the constant function `fun _ => g` is a valid compatible gap selection. -/
theorem trivial_section_sat (G : CubeGraph) (g : Vertex)
    (h : HasTrivialSection G g) : G.Satisfiable :=
  ⟨fun _ => g, h.1, fun e he => h.2 e he⟩

end CubeGraph
