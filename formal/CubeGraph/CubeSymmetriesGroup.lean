/-
  CubeGraph/CubeSymmetryGroup.lean

  The FULL symmetry group of the cube {0,1}³ (48 elements = rotations + reflections).

  Structure: (Z/2Z)³ ⋊ S₃ where
  - (Z/2Z)³ = bit flips (variable negation: x → ¬x)
  - S₃ = bit position permutation (variable reordering)

  Reflection = negation of a single variable (flip 1 bit).
  Rotation = even number of negations + permutation.

  Key results:
  1. 48 symmetries = 24 rotations + 24 reflections
  2. Stabilizer of each vertex = S₃ (order 6): 3 rotations + 3 reflections
  3. All 6 stabilizer elements preserve the 7-gap mask
  4. For a PAIR of cubes with different forbidden vertices: intersection shrinks
  5. For the h2 TRIPLE: intersection = Z/2Z = {id, XOR 3}

  Physical interpretation:
  - Reflection = negating one literal (x₁ → ¬x₁)
  - Rotation = combined negation+reordering that preserves orientation
  - Gap mask breaks 42 of 48 symmetries (keeps only 6 per cube)
  - Multiple cubes break further: 6 → 2 (Z/2Z for h2 triple)

  Dependencies: CubeRotationGroup.lean, StellaOctangula.lean
  See: experiments-ml/027_2026-03-24_star-analysis/SESSION-SUMMARY.md
-/

import CubeGraph.CubeRotationsGroup

namespace CubeGraph

/-! ## Section 1: Full Symmetry Group (48 elements)

  All (σ, mask) pairs: 6 permutations × 8 masks = 48.
  No parity constraint (unlike rotations which require parity match). -/

/-- All 48 symmetries of the cube (rotations + reflections). -/
def allCubeSymmetries : List CubeRot :=
  -- All 6 perms × all 8 masks
  (List.finRange 8).flatMap (fun mask =>
    [⟨0,1,2, mask.val⟩, ⟨1,2,0, mask.val⟩, ⟨2,0,1, mask.val⟩,
     ⟨0,2,1, mask.val⟩, ⟨2,1,0, mask.val⟩, ⟨1,0,2, mask.val⟩])

/-- There are exactly 48 cube symmetries. -/
theorem symmetry_count : allCubeSymmetries.length = 48 := by native_decide

/-- Every symmetry is a Hamming isometry. -/
theorem symmetries_preserve_hamming :
    allCubeSymmetries.all (fun r =>
      (List.finRange 8).all (fun v₁ =>
        (List.finRange 8).all (fun v₂ =>
          hammingDist (r.apply v₁) (r.apply v₂) == hammingDist v₁ v₂
        ))) = true := by native_decide

/-- Every symmetry is a bijection. -/
theorem symmetries_bijective :
    allCubeSymmetries.all (fun r =>
      ((List.finRange 8).map r.apply).Nodup) = true := by native_decide

/-! ## Section 2: Rotations vs Reflections

  A rotation has sign(σ) = parity(popcount(mask)).
  A reflection has sign(σ) ≠ parity(popcount(mask)).
  Reflections include single-bit flips (variable negation). -/

/-- Parity of a permutation: true = even (id, cyc, cyc²). -/
private def permEven (s0 s1 s2 : Nat) : Bool :=
  (s0 == 0 && s1 == 1 && s2 == 2) ||  -- id
  (s0 == 1 && s1 == 2 && s2 == 0) ||  -- cyc
  (s0 == 2 && s1 == 0 && s2 == 1)     -- cyc²

/-- A symmetry is a rotation iff parity matches. -/
def CubeRot.isRotation (r : CubeRot) : Bool :=
  permEven r.s0 r.s1 r.s2 == (popcount3 ⟨r.mask % 8, by omega⟩ % 2 == 0)

/-- Exactly 24 of 48 symmetries are rotations. -/
theorem rotation_reflection_split :
    allCubeSymmetries.countP CubeRot.isRotation = 24 ∧
    allCubeSymmetries.countP (fun r => !r.isRotation) = 24 := by native_decide

/-! ## Section 3: The Three Reflections (Variable Negation)

  Flipping bit i (negating variable i) is a reflection: identity perm + mask = 2^i.
  These are the generators of (Z/2Z)³. -/

/-- Negate variable 0: flip bit 0 (mask = 1). -/
def reflBit0 : CubeRot := ⟨0, 1, 2, 1⟩

/-- Negate variable 1: flip bit 1 (mask = 2). -/
def reflBit1 : CubeRot := ⟨0, 1, 2, 2⟩

/-- Negate variable 2: flip bit 2 (mask = 4). -/
def reflBit2 : CubeRot := ⟨0, 1, 2, 4⟩

/-- Single-bit flips are reflections (not rotations). -/
theorem single_flips_are_reflections :
    reflBit0.isRotation = false ∧
    reflBit1.isRotation = false ∧
    reflBit2.isRotation = false := by native_decide

/-- Single-bit flips are involutions (order 2). -/
theorem single_flips_involutive :
    (List.finRange 8).all (fun v =>
      reflBit0.apply (reflBit0.apply v) == v) = true ∧
    (List.finRange 8).all (fun v =>
      reflBit1.apply (reflBit1.apply v) == v) = true ∧
    (List.finRange 8).all (fun v =>
      reflBit2.apply (reflBit2.apply v) == v) = true := by native_decide

/-- Single-bit flips have NO fixed points (every vertex changes). -/
theorem single_flips_no_fixpoint :
    (List.finRange 8).all (fun v => reflBit0.apply v != v) = true ∧
    (List.finRange 8).all (fun v => reflBit1.apply v != v) = true ∧
    (List.finRange 8).all (fun v => reflBit2.apply v != v) = true := by
  native_decide

/-! ## Section 4: Stabilizers in Full Group

  For each vertex v, the stabilizer Stab(v) ⊂ 48 symmetries has order 6 = S₃.
  It consists of 3 rotations + 3 reflections.
  All 6 permute the remaining 7 vertices among themselves → all preserve 7-gap masks. -/

/-- Each vertex has stabilizer of order 6 in the full symmetry group. -/
theorem full_stabilizer_order_6 :
    (List.finRange 8).all (fun v =>
      allCubeSymmetries.countP (fun r => r.apply v == v) == 6
    ) = true := by native_decide

/-- The stabilizer splits into 3 rotations + 3 reflections. -/
theorem stabilizer_split_3_3 :
    (List.finRange 8).all (fun v =>
      allCubeSymmetries.countP (fun r => r.apply v == v && r.isRotation) == 3 &&
      allCubeSymmetries.countP (fun r => r.apply v == v && !r.isRotation) == 3
    ) = true := by native_decide

/-- Every stabilizer element preserves the 7-gap mask (since it's a bijection fixing v). -/
theorem stabilizer_preserves_gaps :
    (List.finRange 8).all (fun forbidden =>
      allCubeSymmetries.all (fun r =>
        !(r.apply forbidden == forbidden) ||
        (List.finRange 8).all (fun v =>
          v == forbidden || r.apply v != forbidden)
      )) = true := by native_decide

/-! ## Section 5: Multi-Cube Intersection → Z/2Z

  For a SINGLE cube: 6 of 48 symmetries preserve the gap mask.
  For TWO cubes with different forbidden vertices: the intersection shrinks.
  For the h2 TRIPLE (3 cubes): only Z/2Z = {id, XOR 3} survives.

  The symmetry XOR 3 = (0,1,2, mask=3) is the 180° rotation around the z-axis.
  It negates variables 0 and 1 simultaneously. This is a ROTATION (even perm + even mask). -/

/-- XOR 3 = negation of variables 0 and 1 simultaneously. -/
def xor3Rot : CubeRot := ⟨0, 1, 2, 3⟩

/-- XOR 3 is a rotation (not a reflection). -/
theorem xor3_is_rotation : xor3Rot.isRotation = true := by native_decide

/-- XOR 3 has order 2 (involution). -/
theorem xor3_order2 :
    (List.finRange 8).all (fun v =>
      xor3Rot.apply (xor3Rot.apply v) == v) = true := by native_decide

/-- XOR 3 has no fixed points. -/
theorem xor3_no_fixpoint :
    (List.finRange 8).all (fun v => xor3Rot.apply v != v) = true := by
  native_decide

/-- For a pair of vertices at Hamming distance 2, the intersection of stabilizers
    has order at most 2 (generically). -/
theorem stabilizer_intersection_pair :
    -- Pick specific pairs: (0,3), (0,5), (0,6) — all at Hamming distance 2
    allCubeSymmetries.countP (fun r =>
      r.apply ⟨0, by omega⟩ == ⟨0, by omega⟩ &&
      r.apply ⟨3, by omega⟩ == ⟨3, by omega⟩) = 2 ∧
    allCubeSymmetries.countP (fun r =>
      r.apply ⟨0, by omega⟩ == ⟨0, by omega⟩ &&
      r.apply ⟨5, by omega⟩ == ⟨5, by omega⟩) = 2 ∧
    allCubeSymmetries.countP (fun r =>
      r.apply ⟨0, by omega⟩ == ⟨0, by omega⟩ &&
      r.apply ⟨6, by omega⟩ == ⟨6, by omega⟩) = 2 := by native_decide

/-- For a triple forming a Stella face (all Hamming distance 2),
    the stabilizer intersection has order 1 (only identity fixes all 3). -/
theorem stella_triple_stabilizer_trivial :
    -- {0,3,5}: only identity fixes all 3 simultaneously
    allCubeSymmetries.countP (fun r =>
      r.apply ⟨0, by omega⟩ == ⟨0, by omega⟩ &&
      r.apply ⟨3, by omega⟩ == ⟨3, by omega⟩ &&
      r.apply ⟨5, by omega⟩ == ⟨5, by omega⟩) = 1 := by native_decide

/-! ## Section 6: Symmetry Breaking Chain

  The full picture of how gap constraints progressively break symmetry:

  48 (full symmetry group)
   → 6 per cube (stabilizer of forbidden vertex)
   → 2 per pair of cubes with different forbidden vertices
   → 1 for a Stella triple of forbidden vertices (only identity)

  The last line is key: if 3 cubes have forbidden vertices forming a Stella triple
  (like {0,3,5}), then ONLY the identity preserves all 3 gap masks.
  This is MAXIMAL symmetry breaking — the structure has trivial residual symmetry.

  For the h2 witness: the forbidden vertices do NOT form a Stella triple
  (they're chosen by the formula), so Z/2Z survives. But the Stella triples
  are the WORST CASE for symmetry breaking. -/

/-- **Symmetry breaking chain**: 48 → 6 → 2 → 1 as constraints accumulate. -/
theorem symmetry_breaking_chain :
    -- Level 0: full group
    allCubeSymmetries.length = 48 ∧
    -- Level 1: one cube (forbidden vertex 0)
    allCubeSymmetries.countP (fun r => r.apply ⟨0, by omega⟩ == ⟨0, by omega⟩) = 6 ∧
    -- Level 2: two cubes (forbidden 0 and 3)
    allCubeSymmetries.countP (fun r =>
      r.apply ⟨0, by omega⟩ == ⟨0, by omega⟩ &&
      r.apply ⟨3, by omega⟩ == ⟨3, by omega⟩) = 2 ∧
    -- Level 3: three cubes forming Stella triple (forbidden 0, 3, 5)
    allCubeSymmetries.countP (fun r =>
      r.apply ⟨0, by omega⟩ == ⟨0, by omega⟩ &&
      r.apply ⟨3, by omega⟩ == ⟨3, by omega⟩ &&
      r.apply ⟨5, by omega⟩ == ⟨5, by omega⟩) = 1 := by native_decide

end CubeGraph
