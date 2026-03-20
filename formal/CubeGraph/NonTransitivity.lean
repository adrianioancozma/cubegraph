/-
  CubeGraph/NonTransitivity.lean
  Gap compatibility is NOT transitive: A compatible with B, B compatible with C,
  does NOT imply A compatible with C.

  Root cause: different edges transmit different variables. The "channel"
  A→B transmits var 1, B→C transmits var 4, but A→C checks var 2 —
  which was never transmitted through B.

  This is the concrete manifestation of the information bottleneck (T3).
  See: Witness.lean (same cubes used as H² witness)
  See: FullSupportComposition.lean (algebraic consequence: rank collapse)
-/
import CubeGraph.Witness

namespace CubeGraph

open BoolMat

/-- N1: Gap compatibility is NOT transitive.
    Concrete witness: g₁=0 in A compatible with g₂=2 in B (var 1 matches),
    g₂=2 in B compatible with g₃=3 in C (var 4 matches),
    but g₁=0 in A INCOMPATIBLE with g₃=3 in C (var 2 mismatches). -/
theorem compatibility_not_transitive :
    ∃ (A B C : Cube) (g₁ g₂ g₃ : Vertex),
      transferOp A B g₁ g₂ = true ∧
      transferOp B C g₂ g₃ = true ∧
      transferOp A C g₁ g₃ = false :=
  ⟨h2CubeA, h2CubeB, h2CubeC,
   ⟨0, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
   by native_decide, by native_decide, by native_decide⟩

/-- N2: Matrix composition "invents" compatibilities that the direct edge rejects.
    The composed operator A→B→C has a true entry where the direct operator A→C
    has a false entry. This happens because composition through B loses information
    about var 2, which the direct A→C edge checks. -/
theorem composition_exceeds_direct :
    ∃ (g₁ g₃ : Vertex),
      (mul (transferOp h2CubeA h2CubeB) (transferOp h2CubeB h2CubeC)) g₁ g₃ = true ∧
      transferOp h2CubeA h2CubeC g₁ g₃ = false :=
  ⟨⟨0, by omega⟩, ⟨3, by omega⟩, by native_decide, by native_decide⟩

/-- N3: The three edges of the H² witness triangle each transmit a DIFFERENT variable.
    This is the mechanism behind non-transitivity: no single variable is shared
    across all three edges, so information is lost at each hop. -/
theorem different_shared_vars :
    Cube.sharedVars h2CubeA h2CubeB = [1] ∧
    Cube.sharedVars h2CubeB h2CubeC = [4] ∧
    Cube.sharedVars h2CubeA h2CubeC = [2] := by
  native_decide

end CubeGraph
