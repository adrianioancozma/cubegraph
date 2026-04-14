/-
  CubeGraph/FiveViews.lean
  Agent-Nu3: Five Views of the P/NP Dichotomy on 3-Variable Constraint Gap Sets.

  The 5 views:
    (V1) Arithmetic:   |S| ∈ {1, 2, 4, 8}  (power of 2)
    (V2) Geometric:    S is an affine subspace of GF(2)^3
    (V3) Symmetric:    S is closed under ternary XOR: ∀ a b c ∈ S, a ⊕ b ⊕ c ∈ S
    (V4) Algebraic:    boolean rank does not decay to 1 under 2-step composition
    (V5) Computational: falls within a Schaefer tractable class

  Proven equivalences (all on Fin 8 subsets, exhaustive native_decide):

  § (V2) ↔ (V3):  PROVEN. Affine ⟺ ternary XOR-closed (for nonempty sets).
                   This IS an iff — verified on all 256 subsets.

  § (V2) → (V1):  PROVEN. Affine ⟹ pow2 size (Lagrange for GF(2)^3).

  § (V1) ↛ (V2):  PROVEN. pow2 does NOT imply affine.
                   Counterexample: {0,1,2,4} (size 4, not affine).
                   Only 14 of 70 size-4 subsets are affine.

  § (V4) witness:  PROVEN (concrete). 3-SAT 2-step composition IS rank-1;
                   XOR-SAT 2-step composition is NOT rank-1.
                   This is the information-theoretic gap.
                   (V4 is NOT a universal iff with V2 — some affine masks also
                   decay to rank-1, and some non-affine don't.)

  § 3-SAT:        7 gaps → ¬V1 ∧ ¬V2 ∧ ¬V3 (all structural views fail).

  Total: .
-/

import CubeGraph.Basic

namespace CubeGraph

/-! ## Mask-Level Helpers (self-contained)

  Subsets of Fin 8 = {0..7} encoded as Fin 256 bitmasks.
  Independent of private defs in NonAffine.lean. -/

/-- Extract bit v from a 256-mask. -/
private def fvBit (m : Fin 256) (v : Fin 8) : Bool :=
  (m.val >>> v.val) &&& 1 == 1

/-- Count set bits. -/
private def fvCount (m : Fin 256) : Nat :=
  (List.finRange 8).countP (fun v => fvBit m v)

/-- Check if count is in {1,2,4,8}. -/
private def fvIsPow2 (m : Fin 256) : Bool :=
  let c := fvCount m
  c == 1 || c == 2 || c == 4 || c == 8

/-- Check if mask is a linear subspace (contains 0, XOR-closed). -/
private def fvIsLinear (m : Fin 256) : Bool :=
  fvBit m ⟨0, by omega⟩ &&
  (List.finRange 8).all fun v =>
    (List.finRange 8).all fun w =>
      if fvBit m v && fvBit m w then
        fvBit m ⟨(v.val ^^^ w.val) % 8, by omega⟩
      else true

/-- Check if mask is an affine subspace (∃ translation making it linear). -/
private def fvIsAffine (m : Fin 256) : Bool :=
  (List.finRange 8).any fun t =>
    let translated := Fin.mk
      ((List.finRange 8).foldl (fun acc v =>
        if fvBit m v then acc ||| (1 <<< ((t.val ^^^ v.val) % 8)) else acc) 0 % 256)
      (by omega)
    fvIsLinear translated

/-- Check if mask is ternary-XOR-closed: ∀ a b c ∈ S, a⊕b⊕c ∈ S. -/
private def fvIsTernary (m : Fin 256) : Bool :=
  (List.finRange 8).all fun a =>
    (List.finRange 8).all fun b =>
      (List.finRange 8).all fun c =>
        if fvBit m a && fvBit m b && fvBit m c then
          fvBit m ⟨(a.val ^^^ b.val ^^^ c.val) % 8, by omega⟩
        else true

/-! ## Section 1: (V2) ↔ (V3) — Affine ⟺ Ternary XOR-Closed

  THE central equivalence. A nonempty S ⊆ GF(2)^3 is an affine subspace iff
  it is closed under the ternary operation a ⊕ b ⊕ c.

  Over GF(2), a ⊕ b ⊕ c is the unique "affine combination" a − b + c.
  Closure under this operation is the defining property of affine subspaces
  in any vector space over a field of characteristic 2.
-/

/-- **(V2 ↔ V3)**: For nonempty subsets of GF(2)^3:
    affine subspace ⟺ ternary XOR-closed.
    Verified exhaustively on all 256 subsets. -/
theorem v2_iff_v3 :
    (List.finRange 256).all (fun m =>
      if decide (fvCount m > 0) then
        (fvIsAffine m) == (fvIsTernary m)
      else true) = true := by
  native_decide

/-- (V2 → V3): Every affine mask is ternary-closed. -/
theorem v2_implies_v3 :
    (List.finRange 256).all (fun m =>
      if fvIsAffine m then fvIsTernary m else true) = true := by
  native_decide

/-- (V3 → V2): Every nonempty ternary-closed mask is affine. -/
theorem v3_implies_v2 :
    (List.finRange 256).all (fun m =>
      if fvIsTernary m && decide (fvCount m > 0)
      then fvIsAffine m else true) = true := by
  native_decide

/-- Edge case: the empty set is vacuously ternary-closed but NOT affine. -/
theorem empty_ternary_not_affine :
    fvIsTernary ⟨0, by omega⟩ = true ∧
    fvIsAffine ⟨0, by omega⟩ = false := by
  native_decide

/-! ## Section 2: (V2) → (V1) — Affine ⟹ Power-of-2 Size

  Lagrange's theorem: |coset of V| = |V| = 2^dim(V) ∈ {1, 2, 4, 8}.
-/

/-- (V2 → V1): Affine → power-of-2 count. -/
theorem v2_implies_v1 :
    (List.finRange 256).all (fun m =>
      if fvIsAffine m then fvIsPow2 m else true) = true := by
  native_decide

/-! ## Section 3: (V1) ↛ (V2) — Power-of-2 Does NOT Imply Affine

  Counterexample: {0,1,2,4} (mask 23) has |S| = 4 = 2² but is NOT affine.
  Reason: 0⊕1⊕2 = 3 ∉ {0,1,2,4} → NOT ternary closed → NOT affine.

  Quantitatively: size 1,2,8 → 100% affine; size 4 → only 20% (14/70).
-/

/-- Counterexample: {0,1,2,4} (mask 23) has 4 elements, is pow2, but NOT affine. -/
theorem v1_not_implies_v2 :
    fvCount ⟨23, by omega⟩ = 4 ∧
    fvIsPow2 ⟨23, by omega⟩ = true ∧
    fvIsAffine ⟨23, by omega⟩ = false ∧
    fvIsTernary ⟨23, by omega⟩ = false := by
  native_decide

/-- Full classification: affine fraction by size.
    The gap between V1 and V2 exists ONLY at size 4. -/
theorem affine_fraction_by_size :
    -- Size 1: 8/8 = 100%
    (List.finRange 256).countP (fun m => fvCount m == 1 && fvIsAffine m) = 8 ∧
    (List.finRange 256).countP (fun m => fvCount m == 1) = 8 ∧
    -- Size 2: 28/28 = 100%
    (List.finRange 256).countP (fun m => fvCount m == 2 && fvIsAffine m) = 28 ∧
    (List.finRange 256).countP (fun m => fvCount m == 2) = 28 ∧
    -- Size 4: 14/70 = 20% (THIS is where V1 ≠ V2)
    (List.finRange 256).countP (fun m => fvCount m == 4 && fvIsAffine m) = 14 ∧
    (List.finRange 256).countP (fun m => fvCount m == 4) = 70 ∧
    -- Size 8: 1/1 = 100%
    (List.finRange 256).countP (fun m => fvCount m == 8 && fvIsAffine m) = 1 ∧
    (List.finRange 256).countP (fun m => fvCount m == 8) = 1 ∧
    -- Non-pow2 sizes: 0% (impossible by Lagrange)
    (List.finRange 256).countP (fun m => fvCount m == 3 && fvIsAffine m) = 0 ∧
    (List.finRange 256).countP (fun m => fvCount m == 5 && fvIsAffine m) = 0 ∧
    (List.finRange 256).countP (fun m => fvCount m == 6 && fvIsAffine m) = 0 ∧
    (List.finRange 256).countP (fun m => fvCount m == 7 && fvIsAffine m) = 0 := by
  native_decide

/-! ## Section 4: (V4) Rank Contrast — Algebraic Dichotomy Witness

  Boolean (OR/AND) composition of transfer operators:
  - 3-SAT (7 gaps): 2-step composition IS rank-1 → information irreversibly lost
  - XOR-SAT (4 gaps, affine): 2-step composition NOT rank-1 → structure preserved

  This is NOT a universal iff (some affine masks decay, some non-affine don't),
  but it IS the precise algebraic mechanism separating tractable from hard:
  rank-1 composition means all active rows become identical, so the operator
  can no longer distinguish between different gap choices.

  Reuses BoolMat from Basic.lean.
-/

/-- Transfer operator for masks sharing 1 variable on axis b. -/
private def fvTransferOp (m1 m2 : Fin 256) (b1 b2 : Fin 3) : BoolMat 8 :=
  fun g1 g2 =>
    fvBit m1 g1 && fvBit m2 g2 &&
    (Cube.vertexBit g1 b1 == Cube.vertexBit g2 b2)

/-- Check if a BoolMat 8 is rank-1 (all active rows identical). -/
private def isRk1 (M : BoolMat 8) : Bool :=
  let firstRow := (List.finRange 8).find? fun i =>
    (List.finRange 8).any fun j => M i j
  match firstRow with
  | none => false
  | some r0 =>
    (List.finRange 8).all fun i =>
      if (List.finRange 8).any fun j => M i j then
        (List.finRange 8).all fun j => M i j == M r0 j
      else true

/-- **3-SAT rank collapse**: 2-step composition IS rank-1.
    Mask 254 (vertex 0 forbidden, 7 gaps), sharing bit 0 then bit 1.
    After 2 steps: all active rows identical → information lost. -/
theorem sat3_2step_rank1 :
    isRk1 (BoolMat.mul
      (fvTransferOp ⟨254, by omega⟩ ⟨254, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩)
      (fvTransferOp ⟨254, by omega⟩ ⟨254, by omega⟩ ⟨1, by omega⟩ ⟨1, by omega⟩)) = true := by
  native_decide

/-- **XOR-SAT rank preservation**: 2-step composition is NOT rank-1.
    Mask 153 (even parity, 4 gaps), sharing bit 0 then bit 1.
    After 2 steps: rows still have 2 distinct patterns → structure preserved. -/
theorem xorsat_2step_not_rank1 :
    isRk1 (BoolMat.mul
      (fvTransferOp ⟨153, by omega⟩ ⟨153, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩)
      (fvTransferOp ⟨153, by omega⟩ ⟨153, by omega⟩ ⟨1, by omega⟩ ⟨1, by omega⟩)) = false := by
  native_decide

/-- **Rank contrast**: at 2 composition steps, 3-SAT is rank-1 but XOR-SAT is not.
    This is the information-theoretic gap: 3-SAT loses all gap-selection
    information, while XOR-SAT retains structure for Gaussian elimination. -/
theorem v4_rank_contrast :
    -- 3-SAT: 2-step = rank-1
    (isRk1 (BoolMat.mul
      (fvTransferOp ⟨254, by omega⟩ ⟨254, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩)
      (fvTransferOp ⟨254, by omega⟩ ⟨254, by omega⟩ ⟨1, by omega⟩ ⟨1, by omega⟩)) = true) ∧
    -- XOR-SAT: 2-step ≠ rank-1
    (isRk1 (BoolMat.mul
      (fvTransferOp ⟨153, by omega⟩ ⟨153, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩)
      (fvTransferOp ⟨153, by omega⟩ ⟨153, by omega⟩ ⟨1, by omega⟩ ⟨1, by omega⟩)) = false) := by
  exact ⟨sat3_2step_rank1, xorsat_2step_not_rank1⟩

/-- Rank contrast holds for ALL 8 forbidden vertices (all 7-gap masks). -/
theorem sat3_2step_rank1_all :
    (List.finRange 256).all (fun m =>
      if fvCount m == 7 then
        isRk1 (BoolMat.mul
          (fvTransferOp m m ⟨0, by omega⟩ ⟨0, by omega⟩)
          (fvTransferOp m m ⟨1, by omega⟩ ⟨1, by omega⟩))
      else true) = true := by
  native_decide

/-- Both 1-step transfers are NOT rank-1 (for both 3-SAT and XOR-SAT). -/
theorem both_1step_not_rank1 :
    -- 3-SAT single-step: not rank-1
    isRk1 (fvTransferOp ⟨254, by omega⟩ ⟨254, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩) = false ∧
    -- XOR-SAT single-step: not rank-1
    isRk1 (fvTransferOp ⟨153, by omega⟩ ⟨153, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩) = false := by
  native_decide

/-! ## Section 5: 3-SAT — All Structural Views Fail Simultaneously

  A 3-SAT clause: 1 forbidden vertex, 7 gaps.
  7 ∉ {1,2,4,8}: V1 fails → V2 fails (by V2→V1) → V3 fails (by V2↔V3).
  V4: rank collapses at 2 steps (Section 4).
  V5: outside ALL Schaefer tractable classes (see BarrierSummary.lean).
-/

/-- All 8 single-clause masks (7 gaps) fail V1, V2, V3. -/
theorem sat3_all_views_fail :
    (List.finRange 256).all (fun m =>
      if fvCount m == 7 then
        !fvIsPow2 m && !fvIsAffine m && !fvIsTernary m
      else true) = true := by
  native_decide

/-- All 8 single-clause masks have rank-1 at 2-step composition (V4 fails). -/
theorem sat3_v4_fails_all :
    (List.finRange 256).all (fun m =>
      if fvCount m == 7 then
        isRk1 (BoolMat.mul
          (fvTransferOp m m ⟨0, by omega⟩ ⟨0, by omega⟩)
          (fvTransferOp m m ⟨1, by omega⟩ ⟨1, by omega⟩))
      else true) = true := by
  native_decide

/-! ## Section 6: Quantitative Structure of GF(2)^3

  The lattice of affine subspaces:
  - 16 linear subspaces (all dim 0..3)
  - 51 affine subspaces (all nonempty; empty set is NOT affine)
  - 7 dim-2 linear, 14 dim-2 affine
  - Affine size-4 sets come in 7 complementary pairs
-/

/-- 16 linear subspaces, 51 affine subspaces of GF(2)^3. -/
theorem subspace_counts :
    (List.finRange 256).countP (fun m => fvIsLinear m) = 16 ∧
    (List.finRange 256).countP (fun m => fvIsAffine m) = 51 := by
  native_decide

/-- 7 dim-2 linear subspaces, 14 dim-2 affine subspaces. -/
theorem dim2_counts :
    (List.finRange 256).countP (fun m =>
      fvIsLinear m && (fvCount m == 4)) = 7 ∧
    (List.finRange 256).countP (fun m =>
      fvIsAffine m && (fvCount m == 4)) = 14 := by
  native_decide

/-- Affine size-4 sets pair with their complements (both affine). -/
theorem affine_complement_stable :
    (List.finRange 256).all (fun m =>
      if fvIsAffine m && (fvCount m == 4) then
        fvIsAffine ⟨(255 - m.val) % 256, by omega⟩
      else true) = true := by
  native_decide

/-- Linear vs affine by dimension:
    dim 0 (size 1): 1 linear ({0}), 8 affine
    dim 1 (size 2): 7 linear, 28 affine
    dim 2 (size 4): 7 linear, 14 affine
    dim 3 (size 8): 1 linear = 1 affine (full space) -/
theorem dim_distribution :
    (List.finRange 256).countP (fun m => fvIsLinear m && (fvCount m == 1)) = 1 ∧
    (List.finRange 256).countP (fun m => fvIsAffine m && (fvCount m == 1)) = 8 ∧
    (List.finRange 256).countP (fun m => fvIsLinear m && (fvCount m == 2)) = 7 ∧
    (List.finRange 256).countP (fun m => fvIsAffine m && (fvCount m == 2)) = 28 ∧
    (List.finRange 256).countP (fun m => fvIsLinear m && (fvCount m == 4)) = 7 ∧
    (List.finRange 256).countP (fun m => fvIsAffine m && (fvCount m == 4)) = 14 ∧
    (List.finRange 256).countP (fun m => fvIsLinear m && (fvCount m == 8)) = 1 ∧
    (List.finRange 256).countP (fun m => fvIsAffine m && (fvCount m == 8)) = 1 := by
  native_decide

/-! ## Section 7: Positive Example — XOR-SAT

  When gaps ARE affine, all structural views hold simultaneously.
  This confirms the dichotomy.
-/

/-- Even-parity mask 153 = {0,3,5,6}: V1∧V2∧V3 all hold. -/
theorem xorsat_positive :
    fvCount ⟨153, by omega⟩ = 4 ∧
    fvIsPow2 ⟨153, by omega⟩ = true ∧
    fvIsAffine ⟨153, by omega⟩ = true ∧
    fvIsTernary ⟨153, by omega⟩ = true := by
  native_decide

/-- Odd-parity mask 102 = {1,2,4,7}: also affine (coset of same subspace). -/
theorem xorsat_odd_positive :
    fvCount ⟨102, by omega⟩ = 4 ∧
    fvIsAffine ⟨102, by omega⟩ = true ∧
    fvIsTernary ⟨102, by omega⟩ = true := by
  native_decide

/-- Even and odd parity are complements, both affine. -/
theorem parity_complement :
    (153 + 102 = 255) ∧
    fvIsAffine ⟨153, by omega⟩ = true ∧
    fvIsAffine ⟨102, by omega⟩ = true := by
  native_decide

/-! ## Section 8: Main Theorem — Five Views Summary

  The honest summary of all relationships between the 5 views.
-/

/-- **Main Theorem**: Complete relationship map between the five views.

  For nonempty S ⊆ GF(2)^3:
    (V2) ↔ (V3): affine ⟺ ternary XOR-closed                [v2_iff_v3]
    (V2) → (V1): affine ⟹ pow2 count                         [v2_implies_v1]
    (V1) ↛ (V2): pow2 ↛ affine (counterexample at size 4)     [v1_not_implies_v2]
    (V4):        3-SAT 2-step rank-1, XOR-SAT 2-step not      [v4_rank_contrast]
    3-SAT (7g):  ¬V1 ∧ ¬V2 ∧ ¬V3 ∧ 2-step-rank-1             [sat3_all_views_fail]

  True equivalence class: {V2, V3} (two-way iff, exhaustive on 256 subsets).
  V1 is strictly weaker (necessary but not sufficient).
  V4 is a concrete witness of the algebraic mechanism (rank decay).
  V5 is external (Schaefer's theorem, not mechanized here). -/
theorem five_views_summary :
    -- (V2 ↔ V3)
    ((List.finRange 256).all (fun m =>
      if decide (fvCount m > 0) then
        (fvIsAffine m) == (fvIsTernary m)
      else true) = true) ∧
    -- (V2 → V1)
    ((List.finRange 256).all (fun m =>
      if fvIsAffine m then fvIsPow2 m else true) = true) ∧
    -- ¬(V1 → V2)
    (fvIsPow2 ⟨23, by omega⟩ = true ∧ fvIsAffine ⟨23, by omega⟩ = false) ∧
    -- (V4) rank contrast
    (isRk1 (BoolMat.mul
      (fvTransferOp ⟨254, by omega⟩ ⟨254, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩)
      (fvTransferOp ⟨254, by omega⟩ ⟨254, by omega⟩ ⟨1, by omega⟩ ⟨1, by omega⟩)) = true ∧
    isRk1 (BoolMat.mul
      (fvTransferOp ⟨153, by omega⟩ ⟨153, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩)
      (fvTransferOp ⟨153, by omega⟩ ⟨153, by omega⟩ ⟨1, by omega⟩ ⟨1, by omega⟩)) = false) ∧
    -- 3-SAT: all views fail
    ((List.finRange 256).all (fun m =>
      if fvCount m == 7 then
        !fvIsPow2 m && !fvIsAffine m && !fvIsTernary m
      else true) = true) := by
  exact ⟨v2_iff_v3, v2_implies_v1,
         ⟨by native_decide, by native_decide⟩,
         v4_rank_contrast, sat3_all_views_fail⟩

/-! ## Section 9: Prop-Level Definitions -/

/-- Ternary XOR on vertices. -/
def ternaryXor (a b c : Vertex) : Vertex :=
  ⟨(a.val ^^^ b.val ^^^ c.val) % 8, by omega⟩

/-- A gap set is ternary-affine-closed (Prop-level). -/
def IsTernaryAffineClosed (S : Fin 8 → Bool) : Prop :=
  ∀ a b c : Fin 8, S a = true → S b = true → S c = true →
    S (ternaryXor a b c) = true

/-- Ternary XOR is commutative in first two args. -/
theorem ternaryXor_comm12 (a b c : Vertex) :
    ternaryXor a b c = ternaryXor b a c := by
  revert a b c; native_decide

/-- Ternary XOR self-cancellation: (a ⊕ b ⊕ a) = b. -/
theorem ternaryXor_cancel (a b : Vertex) :
    ternaryXor a b a = b := by
  revert a b; native_decide

/-- Ternary XOR left-cancellation: (a ⊕ a ⊕ c) = c. -/
theorem ternaryXor_cancel_left (a c : Vertex) :
    ternaryXor a a c = c := by
  revert a c; native_decide

end CubeGraph
