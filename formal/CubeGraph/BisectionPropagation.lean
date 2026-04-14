/-
  CubeGraph/BisectionPropagation.lean
  Agent-Lambda4: Non-affine bisection propagation for 3-SAT gap sets.

  THE KEY STRUCTURAL RESULT:

  For any S ⊆ Fin 8 with |S| = 7 (a 3-SAT gap set — one vertex forbidden):
  Bisecting along any variable x_i (i = 0, 1, 2) yields two parts:
    S₀ = {v ∈ S : bit i of v = 0}  — vertices where variable i is false
    S₁ = {v ∈ S : bit i of v = 1}  — vertices where variable i is true

  Proven properties:

  § Section 2 — Size split: {|S₀|, |S₁|} = {3, 4}

  § Section 3 — Size-3 part is ALWAYS non-affine (3 ∉ {1, 2, 4, 8})

  § Section 4 — Size-4 part = complete cube face = ALWAYS affine

  § Section 5 — Unilateral propagation: EXACTLY one part is non-affine

  § Section 6 — Cross-axis rank decay: T(b₁,b₁)·T(b₂,b₂) collapses to rank 1
                 Same-axis: rank 2 preserved

  § Section 7 — Gap count 6: all 28 masks have SOME axis with both parts non-affine

  § Section 8 — Size 7 always produces a size-3 part (non-pow2)

  § Section 9 — Ternary XOR closure parallels: size-3 never closed, size-4 always closed

  § Section 10 — XOR-SAT contrast: nonempty bisection parts are always affine

  § Section 11 — Coverage rate: XOR-SAT preserves rank 2, 3-SAT collapses to rank 1

  Mathematical significance:
    Non-affinity is UNILATERALLY HEREDITARY for 7-gap sets. The forbidden vertex
    damages one face of the cube, creating an indelible size-3 defect. Cross-axis
    composition through this defect causes rank collapse — the algebraic barrier
    that separates 3-SAT from XOR-SAT.

  All proofs by native_decide on finite domains. 0 axioms.

  See: CubeGraph/NonAffine.lean (3-SAT gap sets are non-affine)
  See: CubeGraph/FiveViews.lean (five views of the P/NP dichotomy)
  See: CubeGraph/AffineComposition.lean (affine structure under composition)
-/

import CubeGraph.NonAffine

namespace CubeGraph

/-! ## Section 1: Bisection Definitions

  Bisecting a subset of Fin 8 along bit i: partition into vertices where
  bit i = 0 and bit i = 1.

  We work at the mask level (Fin 256) for native_decide compatibility. -/

/-- Extract bit v from a 256-mask. -/
private def bBit (m : Fin 256) (v : Fin 8) : Bool :=
  (m.val >>> v.val) &&& 1 == 1

/-- Count set bits in a mask. -/
private def bCount (m : Fin 256) : Nat :=
  (List.finRange 8).countP (fun v => bBit m v)

/-- Check if count is a power of 2 (in {1,2,4,8}). -/
private def bIsPow2 (m : Fin 256) : Bool :=
  let c := bCount m
  c == 1 || c == 2 || c == 4 || c == 8

/-- Check if a mask represents a linear subspace (contains 0, XOR-closed). -/
private def bIsLinear (m : Fin 256) : Bool :=
  bBit m ⟨0, by omega⟩ &&
  (List.finRange 8).all fun v =>
    (List.finRange 8).all fun w =>
      if bBit m v && bBit m w then
        bBit m ⟨(v.val ^^^ w.val) % 8, by omega⟩
      else true

/-- Check if a mask represents an affine subspace. -/
private def bIsAffine (m : Fin 256) : Bool :=
  (List.finRange 8).any fun t =>
    let translated := Fin.mk
      ((List.finRange 8).foldl (fun acc v =>
        if bBit m v then acc ||| (1 <<< ((t.val ^^^ v.val) % 8)) else acc) 0 % 256)
      (by omega)
    bIsLinear translated

/-- Bisect a mask along bit i: keep only vertices where bit i = b. -/
private def bisect (m : Fin 256) (i : Fin 3) (b : Bool) : Fin 256 :=
  ⟨(List.finRange 8).foldl (fun acc v =>
    if bBit m v && (((v.val >>> i.val) &&& 1 == 1) == b) then
      acc ||| (1 <<< v.val)
    else acc) 0 % 256, by omega⟩

/-- The "false" side of a bisection: vertices where bit i = 0. -/
private def bisect0 (m : Fin 256) (i : Fin 3) : Fin 256 := bisect m i false

/-- The "true" side of a bisection: vertices where bit i = 1. -/
private def bisect1 (m : Fin 256) (i : Fin 3) : Fin 256 := bisect m i true

/-- A mask has exactly 7 bits set (single-clause 3-SAT gap set). -/
private def is7gap (m : Fin 256) : Bool := bCount m == 7

/-- A mask has exactly 6 bits set (two-clause 3-SAT gap set). -/
private def is6gap (m : Fin 256) : Bool := bCount m == 6

/-! ## Section 2: Size Split = {3, 4}

  The 8 vertices split 4/4 along any bit. Removing one vertex from one side
  yields {3, 4}. -/

/-- For every 7-gap mask and every axis i:
    the bisection sizes are {3, 4} (in some order). -/
theorem bisection_sizes_3_4 :
    (List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun i =>
          let s0 := bCount (bisect0 m i)
          let s1 := bCount (bisect1 m i)
          (s0 + s1 == 7) &&
          ((s0 == 3 && s1 == 4) || (s0 == 4 && s1 == 3)))
      else true) = true := by
  native_decide

/-- The two sides partition the original set: sizes sum to 7. -/
theorem bisection_partition :
    (List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun i =>
          bCount (bisect0 m i) + bCount (bisect1 m i) == 7)
      else true) = true := by
  native_decide

/-! ## Section 3: Size-3 Part is ALWAYS Non-Affine

  3 ∉ {1, 2, 4, 8} → any size-3 subset cannot be affine. -/

/-- No size-3 subset of Fin 8 is affine. (56 subsets, 0 affine.) -/
theorem size3_never_affine :
    (List.finRange 256).all (fun m =>
      if bCount m == 3 then !bIsAffine m else true) = true := by
  native_decide

/-- Corollary: for every 7-gap mask, the size-3 bisection part is non-affine. -/
theorem bisection_size3_nonaffine :
    (List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun i =>
          (if bCount (bisect0 m i) == 3 then !bIsAffine (bisect0 m i) else true) &&
          (if bCount (bisect1 m i) == 3 then !bIsAffine (bisect1 m i) else true))
      else true) = true := by
  native_decide

/-! ## Section 4: Size-4 Part = Complete Face = ALWAYS Affine

  The size-4 part is the COMPLETE face opposite the forbidden vertex.
  A face {v : bit_i(v) = b} is a coset of a 2-dimensional subspace of GF(2)^3. -/

/-- For every 7-gap mask and axis: the size-4 part IS affine. -/
theorem bisection_size4_always_affine :
    (List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun i =>
          (if bCount (bisect0 m i) == 4 then bIsAffine (bisect0 m i) else true) &&
          (if bCount (bisect1 m i) == 4 then bIsAffine (bisect1 m i) else true))
      else true) = true := by
  native_decide

/-- The size-4 part is a COMPLETE face: all 4 vertices with that bit value present. -/
theorem size4_is_complete_face :
    (List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun i =>
          let s0 := bisect0 m i
          let s1 := bisect1 m i
          if bCount s0 == 4 then
            (List.finRange 8).all (fun v =>
              if ((v.val >>> i.val) &&& 1 == 0) then bBit s0 v else true)
          else
            (List.finRange 8).all (fun v =>
              if ((v.val >>> i.val) &&& 1 == 1) then bBit s1 v else true))
      else true) = true := by
  native_decide

/-! ## Section 5: Unilateral Propagation Theorem

  For 7-gap masks: bisection produces EXACTLY one non-affine part (size 3)
  and one affine part (size 4 = complete face). -/

/-- **Unilateral propagation**: at least one part is non-affine for every bisection. -/
theorem bisection_at_least_one_nonaffine :
    (List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun i =>
          !bIsAffine (bisect0 m i) || !bIsAffine (bisect1 m i))
      else true) = true := by
  native_decide

/-- **Exactly one**: for every (mask, axis), exactly one part is non-affine.
    The non-affine part is always the size-3 side (the one with the forbidden vertex). -/
theorem bisection_exactly_one_nonaffine :
    (List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun i =>
          (!bIsAffine (bisect0 m i)) != (!bIsAffine (bisect1 m i)))
      else true) = true := by
  native_decide

/-- The non-affine part is ALWAYS the side with count 3 (containing the forbidden vertex).
    Size 3 ↔ non-affine, size 4 ↔ affine. -/
theorem nonaffine_on_forbidden_side :
    (List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun i =>
          let s0 := bisect0 m i
          let s1 := bisect1 m i
          ((bCount s0 == 3) == (!bIsAffine s0)) &&
          ((bCount s1 == 3) == (!bIsAffine s1)))
      else true) = true := by
  native_decide

/-! ## Section 6: Cross-Axis Rank Decay

  Composing transfer operators along DIFFERENT axes always yields rank 1.
  Composing along the SAME axis preserves rank 2.

  This is the algebraic manifestation of non-affine bisection:
  - Same axis: both steps project onto the same face → structure preserved
  - Different axes: steps project onto orthogonal faces → cross the non-affine
    defect → rank collapses -/

/-- Transfer operator between gap masks sharing 1 variable on axis b. -/
private def bTransfer (m1 m2 : Fin 256) (b1 b2 : Fin 3) : BoolMat 8 :=
  fun g1 g2 =>
    bBit m1 g1 && bBit m2 g2 &&
    (Cube.vertexBit g1 b1 == Cube.vertexBit g2 b2)

/-- Check if a BoolMat 8 has boolean rank 1. -/
private def bIsRank1 (M : BoolMat 8) : Bool :=
  let firstRow := (List.finRange 8).find? fun i =>
    (List.finRange 8).any fun j => M i j
  match firstRow with
  | none => false
  | some r0 =>
    (List.finRange 8).all fun i =>
      if (List.finRange 8).any fun j => M i j then
        (List.finRange 8).all fun j => M i j == M r0 j
      else true

/-- Check if a BoolMat 8 is the zero matrix. -/
private def bIsZero (M : BoolMat 8) : Bool :=
  (List.finRange 8).all fun i =>
    (List.finRange 8).all fun j =>
      !M i j

/-- Boolean rank: 0 if zero, 1 if rank-1, 2 otherwise. -/
private def bRank (M : BoolMat 8) : Nat :=
  if bIsZero M then 0
  else if bIsRank1 M then 1
  else 2

/-- **Cross-axis rank collapse**: T(b₁,b₁)·T(b₂,b₂) for different axes → rank 1.
    Verified for ALL 8 single-clause masks. -/
theorem cross_axis_rank1 :
    (List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun b1 =>
          (List.finRange 3).all (fun b2 =>
            if b1 == b2 then true
            else bIsRank1 (BoolMat.mul
              (bTransfer m m b1 b1)
              (bTransfer m m b2 b2))))
      else true) = true := by
  native_decide

/-- **Same-axis rank preservation**: T(b,b)·T(b,b) has rank 2 for all 7-gap masks. -/
theorem same_axis_rank2 :
    (List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun b =>
          bRank (BoolMat.mul
            (bTransfer m m b b)
            (bTransfer m m b b)) == 2)
      else true) = true := by
  native_decide

/-- **Axis contrast**: same axis → rank 2; different axes → rank 1.
    The geometric explanation: same axis stays on one face (affine, rank preserved);
    different axes cross faces, hitting the non-affine defect (rank collapses). -/
theorem axis_rank_contrast :
    (List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun b1 =>
          (List.finRange 3).all (fun b2 =>
            let composed := BoolMat.mul (bTransfer m m b1 b1) (bTransfer m m b2 b2)
            if b1 == b2 then
              bRank composed == 2
            else
              bRank composed == 1))
      else true) = true := by
  native_decide

/-! ## Section 7: Gap Count 6 — Both Parts Non-Affine

  For cubes with 2 forbidden vertices (6 gaps), the bisection is richer.
  All 28 six-gap masks have at least one axis where BOTH parts are non-affine.
  This happens when both forbidden vertices are on the same face → {3, 3} split. -/

/-- For 6-gap masks: ALL 28 masks have some axis with both parts non-affine. -/
theorem gap6_all_have_both_nonaffine :
    (List.finRange 256).all (fun m =>
      if is6gap m then
        (List.finRange 3).any (fun i =>
          !bIsAffine (bisect0 m i) && !bIsAffine (bisect1 m i))
      else true) = true := by
  native_decide

/-- Count: all 28 six-gap masks exhibit this property. -/
theorem gap6_count_28 :
    (List.finRange 256).countP (fun m =>
      is6gap m) = 28 := by
  native_decide

/-! ## Section 8: Size 7 Always Produces Size 3

  Bisecting a 7-element set always produces a 3-element part.
  Since 3 ∉ {1,2,4,8}, this non-pow2 count persists through bisection. -/

/-- Size 7: at least one part has size 3 (which is non-pow2). -/
theorem size7_produces_size3 :
    (List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun i =>
          bCount (bisect0 m i) == 3 || bCount (bisect1 m i) == 3)
      else true) = true := by
  native_decide

/-- Size 3 splits into parts summing to 3.
    Note: {1,2} are both pow2. Non-affinity terminates at depth 2. -/
theorem size3_splits :
    (List.finRange 256).all (fun m =>
      if bCount m == 3 then
        (List.finRange 3).all (fun i =>
          let s0 := bCount (bisect0 m i)
          let s1 := bCount (bisect1 m i)
          s0 + s1 == 3)
      else true) = true := by
  native_decide

/-! ## Section 9: Ternary XOR Closure Under Bisection

  Non-affine ↔ not ternary-XOR-closed (by Nu3 V2↔V3).
  The size-3 part is never ternary-closed; the size-4 part always is. -/

/-- Check if a mask is ternary-XOR-closed. -/
private def bIsTernary (m : Fin 256) : Bool :=
  (List.finRange 8).all fun a =>
    (List.finRange 8).all fun b =>
      (List.finRange 8).all fun c =>
        if bBit m a && bBit m b && bBit m c then
          bBit m ⟨(a.val ^^^ b.val ^^^ c.val) % 8, by omega⟩
        else true

/-- No size-3 subset of Fin 8 is ternary-XOR-closed. -/
theorem size3_not_ternary :
    (List.finRange 256).all (fun m =>
      if bCount m == 3 then !bIsTernary m else true) = true := by
  native_decide

/-- For 7-gap bisections: size-3 part is never ternary-closed. -/
theorem bisection_ternary_fails :
    (List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun i =>
          (if bCount (bisect0 m i) == 3 then !bIsTernary (bisect0 m i) else true) &&
          (if bCount (bisect1 m i) == 3 then !bIsTernary (bisect1 m i) else true))
      else true) = true := by
  native_decide

/-- For 7-gap bisections: size-4 part IS ternary-closed. -/
theorem bisection_size4_ternary :
    (List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun i =>
          (if bCount (bisect0 m i) == 4 then bIsTernary (bisect0 m i) else true) &&
          (if bCount (bisect1 m i) == 4 then bIsTernary (bisect1 m i) else true))
      else true) = true := by
  native_decide

/-! ## Section 10: XOR-SAT Contrast — Affine Bisection Preserves Affinity

  For XOR-SAT constraints (affine gap sets, 4 gaps):
  every NONEMPTY bisection part is affine.

  Some affine 4-gap masks bisect as {4,0} along certain axes (the mask IS a face).
  The empty set is not affine by our definition. But the nonempty parts are always
  affine. For parity masks (even/odd XOR constraints) the split is always {2,2}. -/

/-- XOR-SAT: every nonempty bisection part of an affine 4-gap mask is affine. -/
theorem xorsat_bisection_nonempty_affine :
    (List.finRange 256).all (fun m =>
      if bIsAffine m && bCount m == 4 then
        (List.finRange 3).all (fun i =>
          (if bCount (bisect0 m i) > 0 then bIsAffine (bisect0 m i) else true) &&
          (if bCount (bisect1 m i) > 0 then bIsAffine (bisect1 m i) else true))
      else true) = true := by
  native_decide

/-- XOR parity masks (even parity 153, odd parity 102): bisection is always {2,2}. -/
theorem parity_bisection_2_2 :
    (List.finRange 3).all (fun i =>
      bCount (bisect0 ⟨153, by omega⟩ i) == 2 &&
      bCount (bisect1 ⟨153, by omega⟩ i) == 2 &&
      bIsAffine (bisect0 ⟨153, by omega⟩ i) &&
      bIsAffine (bisect1 ⟨153, by omega⟩ i) &&
      bCount (bisect0 ⟨102, by omega⟩ i) == 2 &&
      bCount (bisect1 ⟨102, by omega⟩ i) == 2 &&
      bIsAffine (bisect0 ⟨102, by omega⟩ i) &&
      bIsAffine (bisect1 ⟨102, by omega⟩ i)) = true := by
  native_decide

/-- **Dichotomy contrast**:
    XOR-SAT: nonempty bisection parts are always affine.
    3-SAT: exactly one part is non-affine.

    This is the geometric root of the tractability separation:
    XOR-SAT → recursive bisection preserves structure → Gaussian elimination → P.
    3-SAT → every bisection produces a non-affine defect → no clean decomposition. -/
theorem bisection_dichotomy :
    -- XOR-SAT: nonempty parts stay affine
    ((List.finRange 256).all (fun m =>
      if bIsAffine m && bCount m == 4 then
        (List.finRange 3).all (fun i =>
          (if bCount (bisect0 m i) > 0 then bIsAffine (bisect0 m i) else true) &&
          (if bCount (bisect1 m i) > 0 then bIsAffine (bisect1 m i) else true))
      else true) = true) ∧
    -- 3-SAT: exactly one part non-affine
    ((List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun i =>
          (!bIsAffine (bisect0 m i)) != (!bIsAffine (bisect1 m i)))
      else true) = true) := by
  exact ⟨xorsat_bisection_nonempty_affine, bisection_exactly_one_nonaffine⟩

/-! ## Section 11: Coverage Rate Contrast

  XOR-SAT: rank 2 after 2 cross-axis steps → information preserved → rate = 2 → P.
  3-SAT: rank 1 after 2 cross-axis steps → information lost → rate < 2 → NP barrier. -/

/-- **Coverage rate contrast**: XOR-SAT rank 2, 3-SAT rank 1. -/
theorem coverage_rate_contrast :
    -- XOR-SAT (mask 153): rank 2 after cross-axis composition
    (bRank (BoolMat.mul
      (bTransfer ⟨153, by omega⟩ ⟨153, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩)
      (bTransfer ⟨153, by omega⟩ ⟨153, by omega⟩ ⟨1, by omega⟩ ⟨1, by omega⟩)) = 2) ∧
    -- 3-SAT (mask 254): rank 1 after cross-axis composition
    (bRank (BoolMat.mul
      (bTransfer ⟨254, by omega⟩ ⟨254, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩)
      (bTransfer ⟨254, by omega⟩ ⟨254, by omega⟩ ⟨1, by omega⟩ ⟨1, by omega⟩)) = 1) := by
  native_decide

/-! ## Section 12: Main Theorem — Non-Affine Bisection Propagation -/

/-- **MAIN THEOREM: Non-Affine Bisection Propagation**

  For S ⊆ Fin 8 with |S| = 7 (3-SAT gap set):

  (P1) Every bisection yields a {3, 4} split.
  (P2) The size-3 part is ALWAYS non-affine.
  (P3) The size-4 part is ALWAYS affine (complete face of GF(2)^3).
  (P4) Exactly one part is non-affine per bisection (unilateral propagation).
  (P5) Cross-axis composition collapses to rank 1; same-axis preserves rank 2.
  (P6) XOR-SAT: nonempty bisection parts stay affine; 3-SAT: one part defective.

  Consequence: the forbidden vertex creates an INDELIBLE non-affine defect.
  Every bisection propagates this defect to exactly one branch.
  Cross-axis composition through the defect causes rank collapse —
  the algebraic mechanism by which 3-SAT resists the methods that solve XOR-SAT. -/
theorem nonaffine_bisection_propagation :
    -- (P1) Bisection sizes = {3, 4}
    ((List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun i =>
          let s0 := bCount (bisect0 m i)
          let s1 := bCount (bisect1 m i)
          (s0 + s1 == 7) &&
          ((s0 == 3 && s1 == 4) || (s0 == 4 && s1 == 3)))
      else true) = true) ∧
    -- (P2) Size-3 subsets are never affine
    ((List.finRange 256).all (fun m =>
      if bCount m == 3 then !bIsAffine m else true) = true) ∧
    -- (P3) The size-4 bisection part is always affine
    ((List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun i =>
          (if bCount (bisect0 m i) == 4 then bIsAffine (bisect0 m i) else true) &&
          (if bCount (bisect1 m i) == 4 then bIsAffine (bisect1 m i) else true))
      else true) = true) ∧
    -- (P4) Exactly one part is non-affine (unilateral)
    ((List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun i =>
          (!bIsAffine (bisect0 m i)) != (!bIsAffine (bisect1 m i)))
      else true) = true) ∧
    -- (P5) Cross-axis rank collapse to rank 1
    ((List.finRange 256).all (fun m =>
      if is7gap m then
        (List.finRange 3).all (fun b1 =>
          (List.finRange 3).all (fun b2 =>
            if b1 == b2 then true
            else bIsRank1 (BoolMat.mul
              (bTransfer m m b1 b1)
              (bTransfer m m b2 b2))))
      else true) = true) ∧
    -- (P6) XOR-SAT: nonempty bisection parts stay affine
    ((List.finRange 256).all (fun m =>
      if bIsAffine m && bCount m == 4 then
        (List.finRange 3).all (fun i =>
          (if bCount (bisect0 m i) > 0 then bIsAffine (bisect0 m i) else true) &&
          (if bCount (bisect1 m i) > 0 then bIsAffine (bisect1 m i) else true))
      else true) = true) := by
  exact ⟨bisection_sizes_3_4,
         size3_never_affine,
         bisection_size4_always_affine,
         bisection_exactly_one_nonaffine,
         cross_axis_rank1,
         xorsat_bisection_nonempty_affine⟩

end CubeGraph
