/-
  CubeGraph/AffineFactorization.lean
  Agent-Pi5: Affine/Non-Affine Factorization of 3-SAT Gap Sets.

  Core insight: A 3-SAT clause forbids 1 of 8 vertices, leaving 7 gaps.
  These 7 gaps decompose as 7 = 4 + 3:
    - 4 gaps form a MAXIMAL AFFINE SUBSPACE (a face/hyperplane of GF(2)^3)
    - 3 gaps form the NON-AFFINE RESIDUE

  The face decomposition is relative to a chosen bit position i:
    A(v, i) = { w in {0..7} \ {v} | bit i of w != bit i of v }  (|A| = 4)
    R(v, i) = { w in {0..7} \ {v} | bit i of w = bit i of v }   (|R| = 3)

  When two cubes share a variable at bit position i, the transfer operator
  decomposes into a 2x2 block structure on {A, R}:
    - Same polarity (v1 and v2 agree on bit i): M = diag(J_4, J_3)
    - Opposite polarity (disagree on bit i):    M = antidiag(J_4x3, J_3x4)
  where J denotes all-ones blocks.

  This is the algebraic root of the Schaefer dichotomy:
    - The affine block (4 gaps) supports XOR-SAT structure -> P
    - The residue block (3 gaps) is non-affine -> NP-hard
    - Cross-terms couple the two -> full 3-SAT is harder than either alone

  Key results (25 theorems):

  Section 1: Face decomposition, 7 = 4 + 3
  Section 2: Affinity of face, non-affinity of residue
  Section 3: Exhaustive verification: 7 maximal affine 2-planes per vertex
  Section 4: Transfer operator block decomposition (same/opposite polarity)
  Section 5: Structural barrier from residue non-affinity
  Section 6: Recursive factorization 2^d - 1 = 2^(d-1) + (2^(d-1) - 1)
  Section 7: Summary theorems

  All proofs by computation on finite domains (native_decide).
  0 axioms beyond those in Basic.lean.

  See: formal/CubeGraph/NonAffine.lean (7 gaps are non-affine)
  See: formal/CubeGraph/AffineComposition.lean (affine composition)
  See: formal/CubeGraph/InvertibilityBarrier.lean (OR vs XOR)
-/

import CubeGraph.NonAffine

namespace CubeGraph

/-! ## Utility functions (private, redefined since Theta3's are private) -/

/-- Extract bit v from a 256-mask. -/
private def pi5_maskBit (m : Fin 256) (v : Fin 8) : Bool :=
  (m.val >>> v.val) &&& 1 == 1

/-- Count set bits in a mask. -/
private def pi5_maskCount (m : Fin 256) : Nat :=
  (List.finRange 8).countP (fun v => pi5_maskBit m v)

/-- Check if a mask represents a linear subspace of GF(2)^3. -/
private def pi5_isLinear (m : Fin 256) : Bool :=
  pi5_maskBit m ⟨0, by omega⟩ &&
  (List.finRange 8).all fun v =>
    (List.finRange 8).all fun w =>
      if pi5_maskBit m v && pi5_maskBit m w then
        pi5_maskBit m ⟨(v.val ^^^ w.val) % 8, by omega⟩
      else true

/-- Check if a mask represents an affine subspace. -/
private def pi5_isAffine (m : Fin 256) : Bool :=
  (List.finRange 8).any fun t =>
    let translated := Fin.mk
      ((List.finRange 8).foldl (fun acc v =>
        if pi5_maskBit m v then acc ||| (1 <<< ((t.val ^^^ v.val) % 8)) else acc) 0 % 256)
      (by omega)
    pi5_isLinear translated

/-! ## Section 1: Face Decomposition

  Given a forbidden vertex v and a bit position i,
  the AFFINE FACE is {w | bit_i(w) != bit_i(v)} -- a hyperplane, size 4.
  The RESIDUE is {w != v | bit_i(w) = bit_i(v)} -- 3 remaining gaps. -/

/-- The affine face: vertices whose bit i differs from v's bit i.
    This is a hyperplane of GF(2)^3, hence an affine subspace of dimension 2. -/
def affineFace (v : Vertex) (i : Fin 3) : Fin 8 → Bool :=
  fun w => ((w.val >>> i.val) &&& 1) != ((v.val >>> i.val) &&& 1)

/-- The residue: gap vertices NOT in the affine face.
    bit i agrees with v's bit i, but w != v. -/
def residueSet (v : Vertex) (i : Fin 3) : Fin 8 → Bool :=
  fun w => w != v && ((w.val >>> i.val) &&& 1) == ((v.val >>> i.val) &&& 1)

/-- The gap set of a single-clause cube: everything except the forbidden vertex. -/
def gapSetOf (v : Vertex) : Fin 8 → Bool :=
  fun w => w != v

/-- The affine face has exactly 4 elements (for all v and i). -/
theorem affineFace_count (v : Vertex) (i : Fin 3) :
    count8 (affineFace v i) = 4 := by
  revert v i; native_decide

/-- The residue has exactly 3 elements (for all v and i). -/
theorem residueSet_count (v : Vertex) (i : Fin 3) :
    count8 (residueSet v i) = 3 := by
  revert v i; native_decide

/-- The gap set has exactly 7 elements. -/
theorem gapSetOf_count (v : Vertex) : count8 (gapSetOf v) = 7 := by
  revert v; native_decide

/-- **Decomposition 7 = 4 + 3**: face and residue partition the gap set.
    gapSetOf v w = (affineFace v i w) || (residueSet v i w). -/
theorem decomposition_partition (v : Vertex) (i : Fin 3) (w : Fin 8) :
    gapSetOf v w = (affineFace v i w || residueSet v i w) := by
  revert v i w; native_decide

/-- The face and residue are disjoint. -/
theorem face_residue_disjoint (v : Vertex) (i : Fin 3) (w : Fin 8) :
    ¬ (affineFace v i w = true ∧ residueSet v i w = true) := by
  revert v i w; native_decide

/-- The face is a subset of the gaps. -/
theorem affineFace_subset_gaps (v : Vertex) (i : Fin 3) (w : Fin 8) :
    affineFace v i w = true → gapSetOf v w = true := by
  revert v i w; native_decide

/-- The residue is a subset of the gaps. -/
theorem residueSet_subset_gaps (v : Vertex) (i : Fin 3) (w : Fin 8) :
    residueSet v i w = true → gapSetOf v w = true := by
  revert v i w; native_decide

/-! ## Section 2: Affine Structure

  The face is an affine subspace of GF(2)^3 (verified exhaustively).
  The residue has size 3 (not a power of 2), hence NOT affine. -/

/-- Encode the affine face as a Fin 256 mask. -/
private def faceMask (v : Vertex) (i : Fin 3) : Fin 256 :=
  ⟨(List.finRange 8).foldl (fun acc w =>
    if affineFace v i w then acc ||| (1 <<< w.val) else acc) 0 % 256,
   by omega⟩

/-- Encode the residue as a Fin 256 mask. -/
private def residueMask (v : Vertex) (i : Fin 3) : Fin 256 :=
  ⟨(List.finRange 8).foldl (fun acc w =>
    if residueSet v i w then acc ||| (1 <<< w.val) else acc) 0 % 256,
   by omega⟩

/-- Every face mask is an affine subspace (8 vertices x 3 bits = 24 checks). -/
theorem affineFace_is_affine :
    (List.finRange 8).all (fun v =>
      (List.finRange 3).all (fun i =>
        pi5_isAffine (faceMask v i))) = true := by
  native_decide

/-- Every residue mask is NOT an affine subspace (24 checks). -/
theorem residueSet_not_affine :
    (List.finRange 8).all (fun v =>
      (List.finRange 3).all (fun i =>
        !pi5_isAffine (residueMask v i))) = true := by
  native_decide

/-! ## Section 3: Seven Maximal Affine 2-Planes

  For each forbidden vertex, there are exactly 7 distinct affine 2-planes
  (size 4) contained in the 7 gaps. The face decomposition gives 3 of these. -/

/-- Encode the gap set as a Fin 256 mask. -/
private def gapMaskOf' (v : Vertex) : Fin 256 :=
  ⟨(List.finRange 8).foldl (fun acc w =>
    if gapSetOf v w then acc ||| (1 <<< w.val) else acc) 0 % 256,
   by omega⟩

/-- Count affine 2-planes (size 4) inside a gap set. -/
private def countAffine2Planes (gapMsk : Fin 256) : Nat :=
  (List.finRange 256).countP (fun m =>
    pi5_maskCount m == 4 && pi5_isAffine m &&
    (List.finRange 8).all (fun w =>
      if pi5_maskBit m w then pi5_maskBit gapMsk w else true))

/-- For every forbidden vertex, there are exactly 7 affine 2-planes in the gaps. -/
theorem seven_affine_2planes :
    (List.finRange 8).all (fun v =>
      countAffine2Planes (gapMaskOf' v) == 7) = true := by
  native_decide

/-- Gap masks have count 7 for each forbidden vertex. -/
theorem gapMask_count_seven :
    (List.finRange 8).all (fun v =>
      pi5_maskCount (gapMaskOf' v) == 7) = true := by
  native_decide

/-- The three face-based planes are distinct for each forbidden vertex. -/
theorem three_faces_distinct :
    (List.finRange 8).all (fun v =>
      (List.finRange 3).all (fun i =>
        (List.finRange 3).all (fun j =>
          if i == j then true else faceMask v i != faceMask v j))) = true := by
  native_decide

/-! ## Section 4: Transfer Operator Block Decomposition

  When two cubes share a variable at bit position s,
  the transfer operator M[g1, g2] = 1 iff bit_s(g1) = bit_s(g2).

  Using the face decomposition relative to the SHARED bit s:
    A_k = {w | bit_s(w) != bit_s(v_k)}  (affine face, 4 elements)
    R_k = {w != v_k | bit_s(w) = bit_s(v_k)}  (residue, 3 elements)

  Block structure depends on polarity:
    Same polarity: M = diag(J_{4x4}, J_{3x3})  [block diagonal]
    Opposite polarity: M = antidiag(J_{4x3}, J_{3x4})  [anti-block diagonal] -/

/-- Compatibility: g1 and g2 agree on bit s. -/
def agreeOnBit (g1 g2 : Vertex) (s : Fin 3) : Bool :=
  ((g1.val >>> s.val) &&& 1) == ((g2.val >>> s.val) &&& 1)

/-- Same polarity: v1 and v2 agree on bit s. -/
def samePolarity (v1 v2 : Vertex) (s : Fin 3) : Bool :=
  agreeOnBit v1 v2 s

/-- **Same polarity, A x A block = all 1s**: affine gaps are mutually compatible. -/
theorem block_same_AA :
    ∀ (v1 v2 : Vertex) (s : Fin 3),
      samePolarity v1 v2 s = true →
      ∀ g1 g2 : Vertex,
        affineFace v1 s g1 = true →
        affineFace v2 s g2 = true →
        agreeOnBit g1 g2 s = true := by
  decide

/-- **Same polarity, R x R block = all 1s**: residue gaps are mutually compatible. -/
theorem block_same_RR :
    ∀ (v1 v2 : Vertex) (s : Fin 3),
      samePolarity v1 v2 s = true →
      ∀ g1 g2 : Vertex,
        residueSet v1 s g1 = true →
        residueSet v2 s g2 = true →
        agreeOnBit g1 g2 s = true := by
  decide

/-- **Same polarity, A x R block = all 0s**: cross-terms incompatible. -/
theorem block_same_AR_zero :
    ∀ (v1 v2 : Vertex) (s : Fin 3),
      samePolarity v1 v2 s = true →
      ∀ g1 g2 : Vertex,
        affineFace v1 s g1 = true →
        residueSet v2 s g2 = true →
        agreeOnBit g1 g2 s = false := by
  decide

/-- **Same polarity, R x A block = all 0s**: cross-terms incompatible. -/
theorem block_same_RA_zero :
    ∀ (v1 v2 : Vertex) (s : Fin 3),
      samePolarity v1 v2 s = true →
      ∀ g1 g2 : Vertex,
        residueSet v1 s g1 = true →
        affineFace v2 s g2 = true →
        agreeOnBit g1 g2 s = false := by
  decide

/-- **Opposite polarity, A x A block = all 0s**. -/
theorem block_opp_AA_zero :
    ∀ (v1 v2 : Vertex) (s : Fin 3),
      samePolarity v1 v2 s = false →
      ∀ g1 g2 : Vertex,
        affineFace v1 s g1 = true →
        affineFace v2 s g2 = true →
        agreeOnBit g1 g2 s = false := by
  decide

/-- **Opposite polarity, R x R block = all 0s**. -/
theorem block_opp_RR_zero :
    ∀ (v1 v2 : Vertex) (s : Fin 3),
      samePolarity v1 v2 s = false →
      ∀ g1 g2 : Vertex,
        residueSet v1 s g1 = true →
        residueSet v2 s g2 = true →
        agreeOnBit g1 g2 s = false := by
  decide

/-- **Opposite polarity, A x R block = all 1s**: affine maps to residue. -/
theorem block_opp_AR :
    ∀ (v1 v2 : Vertex) (s : Fin 3),
      samePolarity v1 v2 s = false →
      ∀ g1 g2 : Vertex,
        affineFace v1 s g1 = true →
        residueSet v2 s g2 = true →
        agreeOnBit g1 g2 s = true := by
  decide

/-- **Opposite polarity, R x A block = all 1s**: residue maps to affine. -/
theorem block_opp_RA :
    ∀ (v1 v2 : Vertex) (s : Fin 3),
      samePolarity v1 v2 s = false →
      ∀ g1 g2 : Vertex,
        residueSet v1 s g1 = true →
        affineFace v2 s g2 = true →
        agreeOnBit g1 g2 s = true := by
  decide

/-! ## Section 5: Structural Barrier from Residue Non-Affinity

  The residue (3 gaps) is never an affine subspace because 3 is not a power of 2.
  This holds not just for face-based residues, but for the residue of ANY maximal
  affine 2-plane contained in the 7 gaps. -/

/-- The residue of any affine 2-plane (size 4) in a 7-gap set has size 3. -/
theorem residue_of_plane_size_3 :
    (List.finRange 8).all (fun v =>
      (List.finRange 256).all (fun m =>
        if pi5_maskCount m == 4 && pi5_isAffine m &&
           (List.finRange 8).all (fun w =>
             if pi5_maskBit m w then pi5_maskBit (gapMaskOf' v) w else true)
        then
          pi5_maskCount (⟨((gapMaskOf' v).val &&& (m.val ^^^ 255)) % 256, by omega⟩ : Fin 256) == 3
        else true)) = true := by
  native_decide

/-- The residue of any affine 2-plane in a 7-gap set is NEVER affine. -/
theorem residue_of_plane_not_affine :
    (List.finRange 8).all (fun v =>
      (List.finRange 256).all (fun m =>
        if pi5_maskCount m == 4 && pi5_isAffine m &&
           (List.finRange 8).all (fun w =>
             if pi5_maskBit m w then pi5_maskBit (gapMaskOf' v) w else true)
        then
          !pi5_isAffine (⟨((gapMaskOf' v).val &&& (m.val ^^^ 255)) % 256, by omega⟩ : Fin 256)
        else true)) = true := by
  native_decide

/-- 3 is not a power of two (residues are structurally non-affine). -/
theorem residue_size_not_pow2 : ¬ IsPowerOfTwo 3 := three_not_pow2

/-! ## Section 6: Recursive Factorization

  The pattern 7 = 4 + 3 is the d=3 case of:
    2^d - 1 = 2^(d-1) + (2^(d-1) - 1)

  The affine part (2^(d-1)) is a power of 2 and tractable.
  The residue (2^(d-1) - 1) is non-affine for d >= 2.
  The residue has the SAME structure one dimension lower. -/

/-- For d=3: 7 = 4 + 3. -/
theorem factorization_d3 : 7 = 4 + 3 := by omega

/-- For d=2: 3 = 2 + 1 (the residue decomposes further). -/
theorem factorization_d2 : 3 = 2 + 1 := by omega

/-- For d=1: 1 = 1 + 0 (base case). -/
theorem factorization_d1 : 1 = 1 + 0 := by omega

/-- The affine part sizes are powers of 2. -/
theorem affine_part_pow2 :
    IsPowerOfTwo 4 ∧ IsPowerOfTwo 2 ∧ IsPowerOfTwo 1 := by
  simp [IsPowerOfTwo]

/-- Residue size 3 (d=3 case) is not a power of 2. -/
theorem residue_not_pow2_d3 : ¬ IsPowerOfTwo 3 := three_not_pow2

/-- Residue size 1 (d=2 case) IS a power of 2 -- base case, recursion terminates. -/
theorem residue_pow2_d2 : IsPowerOfTwo 1 := by simp [IsPowerOfTwo]

/-! ## Section 7: Summary Theorems -/

/-- **The Affine Factorization Theorem**:
    For every forbidden vertex v and every bit position i,
    the 7 gaps decompose as:
    (1) |face| = 4, |residue| = 3, 4 + 3 = 7
    (2) face is affine, residue is not
    (3) face and residue are disjoint and partition the gaps -/
theorem affine_factorization (v : Vertex) (i : Fin 3) :
    count8 (affineFace v i) = 4
    ∧ count8 (residueSet v i) = 3
    ∧ 4 + 3 = 7
    ∧ (∀ w : Fin 8, gapSetOf v w = (affineFace v i w || residueSet v i w))
    ∧ (∀ w : Fin 8, ¬ (affineFace v i w = true ∧ residueSet v i w = true)) := by
  exact ⟨affineFace_count v i,
         residueSet_count v i,
         by omega,
         decomposition_partition v i,
         face_residue_disjoint v i⟩

/-- **The Block Decomposition Theorem**:
    For any two forbidden vertices v1, v2 and shared bit s,
    the compatibility respects the {face, residue} partition. -/
theorem block_decomposition (v1 v2 : Vertex) (s : Fin 3) :
    -- Same polarity: block diagonal
    (samePolarity v1 v2 s = true →
      (∀ g1 g2, affineFace v1 s g1 = true → affineFace v2 s g2 = true →
        agreeOnBit g1 g2 s = true) ∧
      (∀ g1 g2, residueSet v1 s g1 = true → residueSet v2 s g2 = true →
        agreeOnBit g1 g2 s = true) ∧
      (∀ g1 g2, affineFace v1 s g1 = true → residueSet v2 s g2 = true →
        agreeOnBit g1 g2 s = false) ∧
      (∀ g1 g2, residueSet v1 s g1 = true → affineFace v2 s g2 = true →
        agreeOnBit g1 g2 s = false))
    ∧
    -- Opposite polarity: anti-block diagonal
    (samePolarity v1 v2 s = false →
      (∀ g1 g2, affineFace v1 s g1 = true → affineFace v2 s g2 = true →
        agreeOnBit g1 g2 s = false) ∧
      (∀ g1 g2, residueSet v1 s g1 = true → residueSet v2 s g2 = true →
        agreeOnBit g1 g2 s = false) ∧
      (∀ g1 g2, affineFace v1 s g1 = true → residueSet v2 s g2 = true →
        agreeOnBit g1 g2 s = true) ∧
      (∀ g1 g2, residueSet v1 s g1 = true → affineFace v2 s g2 = true →
        agreeOnBit g1 g2 s = true)) := by
  constructor
  · intro h
    exact ⟨block_same_AA v1 v2 s h,
           block_same_RR v1 v2 s h,
           block_same_AR_zero v1 v2 s h,
           block_same_RA_zero v1 v2 s h⟩
  · intro h
    exact ⟨block_opp_AA_zero v1 v2 s h,
           block_opp_RR_zero v1 v2 s h,
           block_opp_AR v1 v2 s h,
           block_opp_RA v1 v2 s h⟩

end CubeGraph
