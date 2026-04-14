/-
  CubeGraph/CubeRotationGroup.lean

  The rotation group of the cube {0,1}³ and its interaction with gap sets.

  The cube has 24 orientation-preserving rotations (≅ S₄).
  Each rotation = permute 3 bit positions + XOR flip mask,
  with parity constraint: sign(σ) = parity(popcount(mask)).

  Key results:
  1. 24 rotations, all Hamming isometries and bijections
  2. Rotations act transitively on 8 vertices (one orbit)
  3. Each vertex has stabilizer of order 3 (identity + 2 diagonal rotations)
  4. Each Stella triple is an ORBIT of a 120° diagonal rotation
  5. The Stella obstruction = the diagonal rotation maps a gap to the
     forbidden vertex, breaking the gap mask

  Connection to GapPreservingSubgroup.lean:
  - The Z/2Z gap-preserving subgroup ({id, XOR 3}) is for SPECIFIC h2 cubes
  - Here we show: per INDIVIDUAL cube, stabilizer has order 3
  - The Z/2Z comes from intersecting stabilizers across multiple cubes

  Dependencies: StellaOctangula.lean
  See: experiments-ml/027_2026-03-24_star-analysis/SESSION-SUMMARY.md
-/

import CubeGraph.StellaOctangula

namespace CubeGraph

/-! ## Section 1: Cube Rotation Action -/

/-- Permute bits of a vertex: output bit i comes from input bit s_i. -/
private def permuteBitsVal (s0 s1 s2 : Nat) (v : Nat) : Nat :=
  ((v >>> s0) &&& 1) |||
  (((v >>> s1) &&& 1) <<< 1) |||
  (((v >>> s2) &&& 1) <<< 2)

/-- A cube rotation descriptor: bit permutation + flip mask. -/
structure CubeRot where
  s0 : Nat
  s1 : Nat
  s2 : Nat
  mask : Nat
  deriving DecidableEq, Repr

/-- Apply a cube rotation to a vertex. -/
def CubeRot.apply (r : CubeRot) (v : Fin 8) : Fin 8 :=
  ⟨(permuteBitsVal r.s0 r.s1 r.s2 v.val ^^^ r.mask) % 8,
   Nat.mod_lt _ (by omega)⟩

/-- The 24 orientation-preserving rotations of the cube.
    Even permutations × even-popcount masks (12)
    + odd permutations × odd-popcount masks (12). -/
def allCubeRotations : List CubeRot :=
  -- Even perms: id=(0,1,2), cyc=(1,2,0), cyc²=(2,0,1)
  -- × even masks: 0, 3, 5, 6 (popcount 0 or 2)
  [ ⟨0,1,2, 0⟩, ⟨0,1,2, 3⟩, ⟨0,1,2, 5⟩, ⟨0,1,2, 6⟩,
    ⟨1,2,0, 0⟩, ⟨1,2,0, 3⟩, ⟨1,2,0, 5⟩, ⟨1,2,0, 6⟩,
    ⟨2,0,1, 0⟩, ⟨2,0,1, 3⟩, ⟨2,0,1, 5⟩, ⟨2,0,1, 6⟩,
  -- Odd perms: (0,2,1), (2,1,0), (1,0,2)
  -- × odd masks: 1, 2, 4, 7 (popcount 1 or 3)
    ⟨0,2,1, 1⟩, ⟨0,2,1, 2⟩, ⟨0,2,1, 4⟩, ⟨0,2,1, 7⟩,
    ⟨2,1,0, 1⟩, ⟨2,1,0, 2⟩, ⟨2,1,0, 4⟩, ⟨2,1,0, 7⟩,
    ⟨1,0,2, 1⟩, ⟨1,0,2, 2⟩, ⟨1,0,2, 4⟩, ⟨1,0,2, 7⟩ ]

/-- There are exactly 24 cube rotations. -/
theorem rotation_count : allCubeRotations.length = 24 := by native_decide

/-! ## Section 2: Basic Properties -/

/-- Every rotation preserves Hamming distance. -/
theorem rotations_preserve_hamming :
    allCubeRotations.all (fun r =>
      (List.finRange 8).all (fun v₁ =>
        (List.finRange 8).all (fun v₂ =>
          hammingDist (r.apply v₁) (r.apply v₂) == hammingDist v₁ v₂
        ))) = true := by native_decide

/-- Every rotation is a bijection on Fin 8. -/
theorem rotations_bijective :
    allCubeRotations.all (fun r =>
      ((List.finRange 8).map r.apply).Nodup) = true := by native_decide

/-- The identity rotation. -/
def identityRot : CubeRot := ⟨0, 1, 2, 0⟩

/-- Identity acts trivially. -/
theorem identity_apply :
    (List.finRange 8).all (fun v => identityRot.apply v == v) = true := by
  native_decide

/-! ## Section 3: Transitive Action and Stabilizers

  The rotation group acts TRANSITIVELY on all 8 vertices.
  By orbit-stabilizer: |Stab(v)| = 24/8 = 3 for each vertex. -/

/-- Rotations act transitively: for any u, v there exists a rotation mapping u to v. -/
theorem rotations_transitive :
    (List.finRange 8).all (fun u =>
      (List.finRange 8).all (fun v =>
        allCubeRotations.any (fun r => r.apply u == v)
      )) = true := by native_decide

/-- Each vertex is fixed by exactly 3 of the 24 rotations. -/
theorem stabilizer_order_3 :
    (List.finRange 8).all (fun v =>
      allCubeRotations.countP (fun r => r.apply v == v) == 3
    ) = true := by native_decide

/-! ## Section 4: Body Diagonal Rotations (Order 3)

  4 body diagonals, each giving 2 rotations (120° and 240°).
  The axis endpoints are fixed; the other 6 vertices form 2 orbits of size 3.
  These orbits are Stella Octangula triples. -/

/-- 120° rotation around diagonal 0↔7 (axis 000↔111). -/
def diagRot07 : CubeRot := ⟨2, 0, 1, 0⟩

/-- 120° rotation around diagonal 1↔6 (axis 001↔110). -/
def diagRot16 : CubeRot := ⟨2, 0, 1, 3⟩

/-- 120° rotation around diagonal 3↔4 (axis 011↔100). -/
def diagRot34 : CubeRot := ⟨2, 0, 1, 5⟩

/-- 120° rotation around diagonal 2↔5 (axis 010↔101). -/
def diagRot25 : CubeRot := ⟨2, 0, 1, 6⟩

/-- Diagonal rotations have order 3. -/
theorem diagRots_order3 :
    [diagRot07, diagRot16, diagRot25, diagRot34].all (fun r =>
      (List.finRange 8).all (fun v =>
        r.apply (r.apply (r.apply v)) == v)) = true := by native_decide

/-- Each diagonal rotation fixes exactly 2 vertices (the axis endpoints). -/
theorem diagRots_fix_two :
    [diagRot07, diagRot16, diagRot25, diagRot34].all (fun r =>
      (List.finRange 8).countP (fun v => r.apply v == v) == 2
    ) = true := by native_decide

/-- The 4 diagonal 120° rotations fix these specific vertex pairs:
    diagRot07 fixes {0,7}, diagRot16 fixes {1,6},
    diagRot25 fixes {2,5}, diagRot34 fixes {3,4}. -/
theorem diagRot_fixed_vertices :
    diagRot07.apply ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧
    diagRot07.apply ⟨7, by omega⟩ = ⟨7, by omega⟩ ∧
    diagRot16.apply ⟨1, by omega⟩ = ⟨1, by omega⟩ ∧
    diagRot16.apply ⟨6, by omega⟩ = ⟨6, by omega⟩ ∧
    diagRot25.apply ⟨2, by omega⟩ = ⟨2, by omega⟩ ∧
    diagRot25.apply ⟨5, by omega⟩ = ⟨5, by omega⟩ ∧
    diagRot34.apply ⟨3, by omega⟩ = ⟨3, by omega⟩ ∧
    diagRot34.apply ⟨4, by omega⟩ = ⟨4, by omega⟩ := by native_decide

/-! ## Section 5: Stella Triples = Rotation Orbits -/

/-- {0,3,5} is the orbit of 0 under diagRot16 (axis 1↔6). -/
theorem orbit_035 :
    diagRot16.apply ⟨0, by omega⟩ = ⟨3, by omega⟩ ∧
    diagRot16.apply ⟨3, by omega⟩ = ⟨5, by omega⟩ ∧
    diagRot16.apply ⟨5, by omega⟩ = ⟨0, by omega⟩ := by native_decide

/-- {3,5,6} is the orbit of 3 under diagRot07 (axis 0↔7). -/
theorem orbit_356 :
    diagRot07.apply ⟨3, by omega⟩ = ⟨6, by omega⟩ ∧
    diagRot07.apply ⟨6, by omega⟩ = ⟨5, by omega⟩ ∧
    diagRot07.apply ⟨5, by omega⟩ = ⟨3, by omega⟩ := by native_decide

/-- {1,2,4} is the orbit of 1 under diagRot07 (axis 0↔7). -/
theorem orbit_124 :
    diagRot07.apply ⟨1, by omega⟩ = ⟨2, by omega⟩ ∧
    diagRot07.apply ⟨2, by omega⟩ = ⟨4, by omega⟩ ∧
    diagRot07.apply ⟨4, by omega⟩ = ⟨1, by omega⟩ := by native_decide

/-- Every Stella triple is the orbit of some diagonal rotation. -/
theorem stella_triples_are_orbits :
    stellaTriples.all (fun t =>
      [diagRot07, diagRot16, diagRot25, diagRot34].any (fun r =>
        (r.apply t.a == t.b && r.apply t.b == t.c && r.apply t.c == t.a) ||
        (r.apply t.a == t.c && r.apply t.c == t.b && r.apply t.b == t.a)
      )) = true := by native_decide

/-! ## Section 6: Gap Masks and Rotational Symmetry Breaking

  A 7-gap mask (one forbidden vertex) is preserved by a rotation iff
  the rotation FIXES the forbidden vertex (since rotations are bijections).
  Each vertex has stabilizer of order 3, so 3 rotations preserve each mask.

  But the gap-preserving subgroup for the h2 witness (3 cubes simultaneously)
  is Z/2Z = {id, XOR 3} — smaller than any individual stabilizer.
  This is because XOR 3 is a 180° face rotation (order 2) that happens to
  preserve the specific gap structure of all 3 h2 cubes, while the order-3
  diagonal rotations do NOT preserve all 3 simultaneously. -/

/-- A rotation preserves a 7-gap mask iff it fixes the forbidden vertex. -/
def rotFixesVertex (r : CubeRot) (v : Fin 8) : Bool := r.apply v == v

/-- Stabilizer of each vertex = 3 rotations (= identity + 2 diagonal). -/
theorem gap_preserving_per_vertex :
    (List.finRange 8).all (fun v =>
      allCubeRotations.countP (fun r => rotFixesVertex r v) == 3
    ) = true := by native_decide

/-- The stabilizer of vertex 0 consists of: identity, diagRot07, diagRot07². -/
theorem stabilizer_vertex0 :
    rotFixesVertex identityRot ⟨0, by omega⟩ = true ∧
    rotFixesVertex diagRot07 ⟨0, by omega⟩ = true ∧
    rotFixesVertex (⟨1, 2, 0, 0⟩ : CubeRot) ⟨0, by omega⟩ = true := by
  native_decide

/-! ## Section 7: The Geometric Mechanism

  WHY does a diagonal rotation break 7-gap masks?

  Rotation R around diagonal a↔(7-a) has orbits {b,c,d} and {b',c',d'}.
  These are Stella triples. The rotation cyclically permutes each orbit.

  If the forbidden vertex is in orbit {b,c,d}, say forbidden=b, then:
  - R maps c → d (gap to gap ✓)
  - R maps d → b = forbidden! (gap to forbidden ✗)

  So R maps some gap to the forbidden vertex, breaking the mask.
  This is EXACTLY the Stella obstruction from StellaOctangula.lean,
  seen from the rotation perspective instead of the majority perspective. -/

/-- For each non-axis vertex v, the diagonal rotation through v's complement
    maps some other non-axis vertex to v (breaking any gap mask with v forbidden). -/
theorem rotation_breaks_gap :
    -- diagRot07 maps some non-{0,7} vertex to each non-{0,7} target
    (List.finRange 8).all (fun v =>
      v == ⟨0, by omega⟩ || v == ⟨7, by omega⟩ ||
      (List.finRange 8).any (fun u =>
        u != v && diagRot07.apply u == v)
    ) = true := by native_decide

/-! ## Section 8: Capstone -/

/-- **Capstone**: the complete rotation-theoretic picture.
    (1) 24 rotations, Hamming isometries, bijections
    (2) Transitive action on 8 vertices
    (3) Stabilizer order 3 per vertex
    (4) Stella triples = orbits of order-3 diagonal rotations
    (5) Diagonal rotations have order 3 and fix exactly 2 vertices -/
theorem cube_rotation_group :
    allCubeRotations.length = 24
    ∧ (List.finRange 8).all (fun u =>
        (List.finRange 8).all (fun v =>
          allCubeRotations.any (fun r => r.apply u == v))) = true
    ∧ (List.finRange 8).all (fun v =>
        allCubeRotations.countP (fun r => r.apply v == v) == 3) = true
    ∧ stellaTriples.all (fun t =>
        [diagRot07, diagRot16, diagRot25, diagRot34].any (fun r =>
          (r.apply t.a == t.b && r.apply t.b == t.c && r.apply t.c == t.a) ||
          (r.apply t.a == t.c && r.apply t.c == t.b && r.apply t.b == t.a)
        )) = true
    ∧ [diagRot07, diagRot16, diagRot25, diagRot34].all (fun r =>
        (List.finRange 8).all (fun v =>
          r.apply (r.apply (r.apply v)) == v)) = true := by
  exact ⟨rotation_count, rotations_transitive, stabilizer_order_3,
         stella_triples_are_orbits, diagRots_order3⟩

end CubeGraph
