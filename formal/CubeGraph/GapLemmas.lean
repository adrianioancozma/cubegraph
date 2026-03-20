/-
  CubeGraph/GapLemmas.lean
  Foundation lemmas for gap counting and satisfiability extraction.

  These lemmas are reused across multiple formalization candidates:
  - gapCount_pos_iff: T1-B, T1-C, T1-D, T2-A, T2-B (5 candidates)
  - validSelection_at: T1-B, T1-C, T1-D, T2-A (4 candidates)
  - compatibleSelection_at: T1-B, T1-C, T1-D, T2-A (4 candidates)

  See: theory/foundations/06-empty-vertex-duality.md (gap = complement of clause)
  See also: CubeGraph/FiberDichotomy.lean (fiber size dichotomy: uses gapCount, isGap)
-/

import CubeGraph.Theorems

/-! ## Gap Counting Lemmas -/

namespace Cube

/-- Gap count is bounded by the number of vertices (8). -/
theorem gapCount_le_eight (c : Cube) : c.gapCount ≤ 8 := by
  simp only [gapCount]
  calc (List.finRange 8).countP (fun v => c.isGap v)
      ≤ (List.finRange 8).length := List.countP_le_length
    _ = 8 := List.length_finRange

/-- Zero gaps means no vertex is a gap. -/
theorem gapCount_eq_zero_iff (c : Cube) :
    c.gapCount = 0 ↔ ∀ v : Vertex, c.isGap v = false := by
  simp only [gapCount]
  constructor
  · -- mp: countP = 0 → all false
    intro h v
    cases hv : c.isGap v with
    | false => rfl
    | true =>
      have : 0 < (List.finRange 8).countP (fun v => c.isGap v) :=
        List.countP_pos_iff.mpr ⟨v, BoolMat.mem_finRange v, hv⟩
      omega
  · -- mpr: all false → countP = 0
    intro h
    apply List.countP_eq_zero.mpr
    intro x _
    simp only [h x]
    exact Bool.false_ne_true

/-- Positive gap count iff there exists a gap. -/
theorem gapCount_pos_iff (c : Cube) :
    c.gapCount > 0 ↔ ∃ v : Vertex, v ∈ List.finRange 8 ∧ c.isGap v = true := by
  simp only [gapCount]
  exact List.countP_pos_iff

/-- Check if any of the 8 bits is set. -/
private def hasGapBit (n : Nat) : Bool :=
  ((n >>> 0) &&& 1 == 1) || ((n >>> 1) &&& 1 == 1) ||
  ((n >>> 2) &&& 1 == 1) || ((n >>> 3) &&& 1 == 1) ||
  ((n >>> 4) &&& 1 == 1) || ((n >>> 5) &&& 1 == 1) ||
  ((n >>> 6) &&& 1 == 1) || ((n >>> 7) &&& 1 == 1)

/-- All positive values below 256 have at least one bit set (pure Bool check). -/
private theorem all_pos_have_gap_bit :
    (List.finRange 256).all (fun (m : Fin 256) =>
      if m.val > 0 then hasGapBit m.val else true) = true := by native_decide

/-- If hasGapBit n = true, there exists a Fin 8 witness for isGap. -/
private theorem hasGapBit_implies_exists (n : Nat) (h : hasGapBit n = true) :
    ∃ v : Fin 8, ((n >>> v.val) &&& 1 == 1) = true := by
  simp only [hasGapBit] at h
  by_cases h0 : ((n >>> 0) &&& 1 == 1) = true
  · exact ⟨⟨0, by omega⟩, h0⟩
  · by_cases h1 : ((n >>> 1) &&& 1 == 1) = true
    · exact ⟨⟨1, by omega⟩, h1⟩
    · by_cases h2 : ((n >>> 2) &&& 1 == 1) = true
      · exact ⟨⟨2, by omega⟩, h2⟩
      · by_cases h3 : ((n >>> 3) &&& 1 == 1) = true
        · exact ⟨⟨3, by omega⟩, h3⟩
        · by_cases h4 : ((n >>> 4) &&& 1 == 1) = true
          · exact ⟨⟨4, by omega⟩, h4⟩
          · by_cases h5 : ((n >>> 5) &&& 1 == 1) = true
            · exact ⟨⟨5, by omega⟩, h5⟩
            · by_cases h6 : ((n >>> 6) &&& 1 == 1) = true
              · exact ⟨⟨6, by omega⟩, h6⟩
              · -- Must be bit 7
                have h7 : ((n >>> 7) &&& 1 == 1) = true := by
                  simp only [] at h0 h1 h2 h3 h4 h5 h6
                  simp only [h0, h1, h2, h3, h4, h5, h6, Bool.false_or] at h
                  exact h
                exact ⟨⟨7, by omega⟩, h7⟩

/-- Every well-formed cube has at least one gap (from gaps_nonempty invariant). -/
theorem gapCount_pos (c : Cube) : c.gapCount ≥ 1 := by
  suffices h : c.gapCount > 0 by omega
  rw [gapCount_pos_iff]
  -- Extract hasGapBit from all_pos_have_gap_bit for our specific gapMask
  have hmask : hasGapBit c.gapMask.val = true := by
    have hall := all_pos_have_gap_bit
    rw [List.all_eq_true] at hall
    have := hall ⟨c.gapMask.val, c.gapMask.isLt⟩ (BoolMat.mem_finRange _)
    simp only [c.gaps_nonempty, ↓reduceIte] at this
    exact this
  obtain ⟨v, hv⟩ := hasGapBit_implies_exists c.gapMask.val hmask
  exact ⟨v, BoolMat.mem_finRange v, by simp only [isGap]; exact hv⟩

/-- Complement counting: filled vertices + gaps = 8. -/
theorem filled_plus_gap (c : Cube) :
    (List.finRange 8).countP (fun v => !c.isGap v) + c.gapCount = 8 := by
  simp only [gapCount]
  have h := CubeGraph.countP_complement (fun v => c.isGap v) (List.finRange 8)
  simp only [List.length_finRange] at h
  omega

end Cube

/-! ## Satisfiability Extraction Lemmas -/

namespace CubeGraph

/-- Extract gap validity for a specific cube from a valid selection. -/
theorem validSelection_at (G : CubeGraph) (s : GapSelection G)
    (h : validSelection G s) (i : Fin G.cubes.length) :
    (G.cubes[i]).isGap (s i) = true :=
  h i

/-- Extract edge compatibility from a compatible selection. -/
theorem compatibleSelection_at (G : CubeGraph) (s : GapSelection G)
    (h : compatibleSelection G s)
    (e : Fin G.cubes.length × Fin G.cubes.length) (he : e ∈ G.edges) :
    transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true :=
  h e he

/-- Satisfiability implies compatible gaps exist on every edge. -/
theorem sat_decompose_edge (G : CubeGraph) (h : G.Satisfiable)
    (e : Fin G.cubes.length × Fin G.cubes.length) (he : e ∈ G.edges) :
    ∃ g₁ g₂ : Vertex,
      (G.cubes[e.1]).isGap g₁ = true ∧
      (G.cubes[e.2]).isGap g₂ = true ∧
      transferOp (G.cubes[e.1]) (G.cubes[e.2]) g₁ g₂ = true := by
  obtain ⟨s, hvalid, hcompat⟩ := h
  exact ⟨s e.1, s e.2, hvalid e.1, hvalid e.2, hcompat e he⟩

/-! ## T1-B: Complete Cube → UNSAT -/

/-- T1-B: A cube with zero gaps makes the entire CubeGraph unsatisfiable.
    This is the contrapositive of sat_implies_no_dead.
    Note: vacuously true in current formalization since Cube.gaps_nonempty
    prevents construction of zero-gap cubes, but conceptually important
    and serves as the H⁰ case in the UNSAT hierarchy (T2-B). -/
theorem complete_cube_unsat (G : CubeGraph) (i : Fin G.cubes.length)
    (h_complete : (G.cubes[i]).gapCount = 0) : ¬ G.Satisfiable := by
  intro hsat
  have := sat_implies_no_dead G hsat i
  omega

/-- Every cube in a well-formed CubeGraph has at least one gap.
    Direct consequence of the Cube.gaps_nonempty invariant.
    This makes complete_cube_unsat vacuously true but confirms
    that H⁰ UNSAT is impossible for valid CubeGraphs. -/
theorem no_dead_cubes (G : CubeGraph) :
    ∀ i : Fin G.cubes.length, (G.cubes[i]).gapCount ≥ 1 := by
  intro i
  exact Cube.gapCount_pos (G.cubes[i])

end CubeGraph
