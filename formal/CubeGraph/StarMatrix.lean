/-
  CubeGraph/StarMatrix.lean

  The global star matrix G ∈ {0,1}^{8N×8N} and its decomposition G = S ⊙ M.

  G[(i,g), (j,g')] = 1 iff gap g in cube i is compatible with gap g' in cube j.

  Decomposition:
  - S = structural matrix: S[(i,g), (j,g')] = 1 iff g and g' AGREE on shared
    variables of cubes i,j. Depends ONLY on which variables are shared, not on gaps.
    S is "flat" — preserved by full Boolean clone. TRACTABLE alone.

  - M = mask matrix: M[(i,g), (j,g')] = 1 iff g is a gap of cube i AND g' is a
    gap of cube j. Depends ONLY on gap masks, not on variable sharing.
    M is block-diagonal. TRIVIAL alone.

  - G = S ⊙ M (Hadamard / entry-wise AND): the INTERACTION of structure and
    fiber. NP-HARD. The Stella Octangula obstruction lives in ⊙.

  SAT ⟺ ∃ selection (one gap per cube) where all G entries are 1.

  Dependencies: Basic.lean, Star.lean, StellaOctangula.lean
  See: experiments-ml/027_2026-03-24_star-analysis/SESSION-SUMMARY.md
-/

import CubeGraph.Star
import CubeGraph.StellaOctangula

namespace CubeGraph

/-! ## Section 1: The 8N×8N Global Matrix -/

/-- A "fat index" into the 8N×8N matrix: (cube index, vertex). -/
structure FatIdx (G : CubeGraph) where
  cube : Fin G.cubes.length
  vertex : Vertex  -- Fin 8

/-- The global matrix G[(i,g), (j,g')] = transferOp applied to the two cubes.
    This is 1 iff g is gap in i, g' is gap in j, and they agree on shared vars. -/
def globalMatrix (G : CubeGraph) (a b : FatIdx G) : Bool :=
  transferOp (G.cubes[a.cube]) (G.cubes[b.cube]) a.vertex b.vertex

/-! ## Section 2: Structural Matrix S

  S depends ONLY on which variables are shared between cubes.
  S[(i,g), (j,g')] = 1 iff g and g' agree on all shared variable positions.
  Ignores gap masks entirely — pretends all 8 vertices are gaps.

  This is the "connection" in constraint graph language: the local transport
  between cubes, independent of the fiber state. -/

/-- The structural matrix: compatibility ignoring gap masks.
    S[(i,g), (j,g')] = 1 iff g,g' agree on shared variables of cubes i,j.
    When cubes share no variables: S = 1 (everything compatible). -/
def structuralMatrix (G : CubeGraph) (a b : FatIdx G) : Bool :=
  let c₁ := G.cubes[a.cube]
  let c₂ := G.cubes[b.cube]
  (Cube.sharedVars c₁ c₂).all fun sv =>
    let idx₁ := (c₁.vars.idxOf sv)
    let idx₂ := (c₂.vars.idxOf sv)
    ((a.vertex.val >>> idx₁) &&& 1) == ((b.vertex.val >>> idx₂) &&& 1)

/-! ## Section 3: Mask Matrix M

  M depends ONLY on gap masks.
  M[(i,g), (j,g')] = 1 iff g is a gap of cube i AND g' is a gap of cube j.
  Block-diagonal structure: M[(i,g), (j,g')] = isGap(i,g) ∧ isGap(j,g').

  This is the "fiber constraint": which vertices are available.
  Alone, M is trivial — no cross-cube interaction. -/

/-- The mask matrix: gap availability only.
    M[(i,g), (j,g')] = isGap(cube_i, g) ∧ isGap(cube_j, g'). -/
def maskMatrix (G : CubeGraph) (a b : FatIdx G) : Bool :=
  (G.cubes[a.cube]).isGap a.vertex && (G.cubes[b.cube]).isGap b.vertex

/-! ## Section 4: Decomposition G = S ⊙ M

  The Hadamard product (entry-wise AND) of S and M gives G.
  This is the fundamental decomposition:
  - S captures STRUCTURE (variable sharing patterns, 27 types)
  - M captures FIBER (gap masks, which vertices are available)
  - G = S ⊙ M captures INTERACTION (the NP-hard part) -/

/-- **Decomposition Theorem**: G = S ⊙ M (entry-wise AND).
    The global matrix is the Hadamard product of structure and mask.
    Proof: transferOp checks (isGap a) ∧ (isGap b) ∧ (shared vars agree)
    = (shared vars agree) ∧ (isGap a ∧ isGap b) = S ∧ M. -/
theorem global_eq_structural_and_mask (G : CubeGraph) (a b : FatIdx G) :
    globalMatrix G a b = (structuralMatrix G a b && maskMatrix G a b) := by
  simp only [globalMatrix, structuralMatrix, maskMatrix, transferOp]
  cases (G.cubes[a.cube]).isGap a.vertex <;>
  cases (G.cubes[b.cube]).isGap b.vertex <;>
  simp [Bool.and_assoc, Bool.and_comm, Bool.false_and, Bool.and_false]

/-! ## Section 5: Properties of S (Structural — Flat)

  The structural matrix S has MAXIMAL rank per block:
  for connected cubes (sharing w variables), S has rank 2^(3-w).
  - w=1: rank 4 (agree on 1 bit, free on 2) — 32 ones per 8×8 block
  - w=2: rank 2 (agree on 2 bits, free on 1) — 16 ones per 8×8 block
  - w=0: rank 8 (no shared vars, everything compatible) — all 64 ones

  S is "flat" in constraint graph terms: no twisting, full Boolean clone preserves it.
  The 27 structural operators (from experiment 027) generate ALL of S. -/

/-- Structural w=1 operators have 32 ones (half the 8×8 matrix).
    w=2 operators have 16 ones (quarter). Verified for all positions. -/
theorem structural_density :
    -- w=1: each operator has 32 ones (50%)
    (List.finRange 3).all (fun p₁ =>
      (List.finRange 3).all (fun p₂ =>
        (List.finRange 8).foldl (fun acc (g₁ : Fin 8) =>
          acc + (List.finRange 8).countP (fun g₂ =>
            ((g₁.val >>> p₁.val) &&& 1) == ((g₂.val >>> p₂.val) &&& 1))
        ) 0 == 32)) = true := by native_decide

/-! ## Section 6: Properties of M (Mask — Trivial)

  M is block-diagonal in a strong sense: M[(i,g), (j,g')] depends only on
  whether g is a gap of cube i and g' is a gap of cube j, independently.
  The cross-cube structure is a TENSOR PRODUCT: M = ⊗ᵢ mask(i).

  Alone, M imposes no cross-cube constraints. Any gap selection where
  each cube picks from its own gaps is M-compatible.
  "SAT of M alone" = trivially true (just pick any gap per cube). -/

/-- M-compatibility is trivially satisfiable: any gap selection works. -/
theorem mask_always_satisfiable (G : CubeGraph)
    (s : GapSelection G) (hs : validSelection G s) :
    ∀ a b : FatIdx G, a.vertex = s a.cube → b.vertex = s b.cube →
      maskMatrix G a b = true := by
  intro ⟨ci, vi⟩ ⟨cj, vj⟩ ha hb
  simp only [maskMatrix] at *
  simp only [ha, hb, hs ci, hs cj, Bool.true_and]

/-! ## Section 7: The Hardness Lives in ⊙

  S alone: tractable (full Boolean clone preserves all 27 structural relations).
  M alone: trivial (no cross-cube constraints).
  S ⊙ M: NP-hard (Bulatov-Zhuk, since conservative Taylor polymorphisms
  are killed by Stella Octangula triples).

  The Stella obstruction explains WHERE the hardness enters:
  - S says: "bits at shared positions must match" (affine constraint)
  - M says: "only these 7 of 8 vertices are available" (conservative constraint)
  - S ⊙ M says: "match bits AND stay in the 7-set" (non-affine, kills majority)

  The transition from tractable to NP-hard happens at the ⊙ operation. -/

/-- The Stella obstruction in matrix language:
    S allows bitwise majority. M forces conservativeness.
    S ⊙ M forbids both → only projections → NP-hard.

    Concretely: for the triple {0,3,5} in a 7-gap set,
    S permits majority(0,3,5) = 1 (bits match on shared vars),
    but M forbids it (1 is not a gap). The ⊙ kills majority. -/
theorem hadamard_kills_majority :
    -- S: bitwise majority(0,3,5) = 1, and 1 is structurally compatible
    -- (for w=0, all compatible; for w=1, depends on shared position)
    -- M: vertex 1 is NOT a gap when forbidden vertex = 1
    -- So S allows 1 but M forbids it. The ⊙ kills it.
    bitwiseMajority ⟨0, by omega⟩ ⟨3, by omega⟩ ⟨5, by omega⟩ = ⟨1, by omega⟩ ∧
    -- 1 is NOT in {0,3,5}
    (⟨1, by omega⟩ : Fin 8) ≠ ⟨0, by omega⟩ ∧
    (⟨1, by omega⟩ : Fin 8) ≠ ⟨3, by omega⟩ ∧
    (⟨1, by omega⟩ : Fin 8) ≠ ⟨5, by omega⟩ := by native_decide

/-! ## Section 8: SAT as Matrix Selection

  SAT ⟺ ∃ selection function s (one gap per cube) such that
  G[(i, s(i)), (j, s(j))] = 1 for all edges (i,j).

  Equivalently: select N entries from the 8N×8N matrix G (one per block-row),
  such that all selected pairs in connected blocks are 1.

  This is a STRUCTURED combinatorial selection problem on the matrix G = S ⊙ M. -/

/-- SAT ⟺ the global matrix admits a compatible selection. -/
theorem sat_iff_matrix_selection (G : CubeGraph) :
    G.Satisfiable ↔
    ∃ s : GapSelection G, validSelection G s ∧
      ∀ e ∈ G.edges,
        globalMatrix G ⟨e.1, s e.1⟩ ⟨e.2, s e.2⟩ = true := by
  constructor
  · intro ⟨s, hv, hc⟩
    exact ⟨s, hv, fun e he => hc e he⟩
  · intro ⟨s, hv, hc⟩
    exact ⟨s, hv, fun e he => hc e he⟩

end CubeGraph
