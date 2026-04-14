/-
  CubeGraph/PhantomGates.lean
  Agent-Upsilon4: XOR vs OR composition — phantom solutions are IMPOSSIBLE.

  THE EXACT QUESTION: Does XOR composition on non-affine gap sets produce
  phantom solutions (valid under XOR but invalid under OR)?

  ANSWER: NO. Phantoms cannot exist. OR DOMINATES XOR:
    boolMul[i,j] = false  →  xorMul[i,j] = false

  Proof: boolMul = OR_k (A[i,k] ∧ B[k,j]). If this is false, then
  A[i,k] ∧ B[k,j] = false for ALL k. Hence XOR_k (A[i,k] ∧ B[k,j]) = false
  (XOR of all-false is false).

  The REVERSE phenomenon exists: ANTI-PHANTOMS.
  For non-affine (7-gap) transfer operators, there exist entries where
  OR = true but XOR = false (even number of witnesses cancel in GF(2)).

  All proofs by computation (native_decide) or short deductions.
  0 axioms.

  See: formal/CubeGraph/NonAffine.lean (3-SAT gap sets are non-affine)
  See: formal/CubeGraph/AffineComposition.lean (XOR preserves structure on affine)
  See: formal/CubeGraph/IrreversibleDecay.lean (OR is irreversible)
  See: formal/CubeGraph/InvertibilityBarrier.lean (XorMat.mul definition)
-/

import CubeGraph.IrreversibleDecay

namespace CubeGraph

open BoolMat

/-! ## Section 1: Definitions -/

/-- A phantom at entry (i,j): XOR says true but OR says false. -/
def IsPhantomEntry (A B : BoolMat 8) (i j : Fin 8) : Prop :=
  XorMat.mul A B i j = true ∧ BoolMat.mul A B i j = false

/-- A matrix pair has a phantom: exists entry where XOR=true but OR=false. -/
def HasPhantom (A B : BoolMat 8) : Prop :=
  ∃ i j, IsPhantomEntry A B i j

/-- An anti-phantom at entry (i,j): OR says true but XOR says false. -/
def IsAntiPhantomEntry (A B : BoolMat 8) (i j : Fin 8) : Prop :=
  BoolMat.mul A B i j = true ∧ XorMat.mul A B i j = false

/-- A matrix pair has an anti-phantom: exists entry where OR=true but XOR=false. -/
def HasAntiPhantom (A B : BoolMat 8) : Prop :=
  ∃ i j, IsAntiPhantomEntry A B i j

/-! ## Section 2: The Core Lemma — OR Dominates XOR

  Algebraic fact: XOR-fold of all-false entries stays false. -/

/-- XOR-fold over a list stays false when the function always returns false. -/
private theorem xor_foldl_false {α : Type} (l : List α) (f : α → Bool)
    (h : ∀ a ∈ l, f a = false) :
    l.foldl (fun acc a => Bool.xor acc (f a)) false = false := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [h x (List.mem_cons.mpr (Or.inl rfl)), Bool.false_xor]
    exact ih (fun a ha => h a (List.mem_cons.mpr (Or.inr ha)))

/-- If boolMul A B i j = false, then every term A[i,k] AND B[k,j] = false. -/
private theorem all_terms_false_of_or_false (A B : BoolMat n) (i j : Fin n)
    (h_or : BoolMat.mul A B i j = false) :
    ∀ k : Fin n, (A i k && B k j) = false := by
  intro k
  -- Suppose A i k && B k j = true. Then mul must be true. Contradiction.
  cases hak : A i k <;> cases hbk : B k j <;> simp
  -- Only case: A i k = true, B k j = true
  exfalso
  have hmul : BoolMat.mul A B i j = true :=
    (BoolMat.mul_apply_true A B i j).mpr ⟨k, hak, hbk⟩
  rw [hmul] at h_or; exact Bool.noConfusion h_or

/-- OR-false implies XOR-false (size 8). -/
theorem or_false_implies_xor_false (A B : BoolMat 8) (i j : Fin 8)
    (h_or : BoolMat.mul A B i j = false) :
    XorMat.mul A B i j = false := by
  have h_terms := all_terms_false_of_or_false A B i j h_or
  show (List.finRange 8).foldl (fun acc k => Bool.xor acc (A i k && B k j)) false = false
  exact xor_foldl_false (List.finRange 8) (fun k => A i k && B k j)
    (fun k _ => h_terms k)

/-- **OR dominates XOR (8x8)**: XOR=true implies OR=true. -/
theorem xor_true_implies_or_true (A B : BoolMat 8) (i j : Fin 8) :
    XorMat.mul A B i j = true → BoolMat.mul A B i j = true := by
  intro hxor
  cases h : BoolMat.mul A B i j with
  | true => rfl
  | false =>
    have := or_false_implies_xor_false A B i j h
    rw [this] at hxor; exact absurd hxor (by decide)

/-! ## Section 3: No Phantoms — Main Theorem -/

/-- **No Phantoms Theorem**: For ANY boolean matrices A, B of size 8x8,
    there are no phantom entries. Phantoms are mathematically IMPOSSIBLE. -/
theorem no_phantoms (A B : BoolMat 8) : ¬ HasPhantom A B := by
  intro ⟨i, j, hxor_true, hor_false⟩
  have := xor_true_implies_or_true A B i j hxor_true
  rw [hor_false] at this; exact absurd this (by decide)

/-! ## Section 4: OR Dominates XOR — General Size -/

/-- XOR matrix multiplication for general size n. -/
def xorMatMul (A B : BoolMat n) : BoolMat n :=
  fun i j => (List.finRange n).foldl (fun acc k => Bool.xor acc (A i k && B k j)) false

/-- OR-false implies XOR-false: general size. -/
theorem or_false_implies_xor_false_general {n : Nat} (A B : BoolMat n) (i j : Fin n)
    (h_or : BoolMat.mul A B i j = false) :
    xorMatMul A B i j = false := by
  have h_terms := all_terms_false_of_or_false A B i j h_or
  show (List.finRange n).foldl (fun acc k => Bool.xor acc (A i k && B k j)) false = false
  exact xor_foldl_false (List.finRange n) (fun k => A i k && B k j)
    (fun k _ => h_terms k)

/-- OR dominates XOR: general size version. -/
theorem or_dominates_xor {n : Nat} (A B : BoolMat n) (i j : Fin n) :
    xorMatMul A B i j = true → BoolMat.mul A B i j = true := by
  intro hxor
  cases h : BoolMat.mul A B i j with
  | true => rfl
  | false =>
    have := or_false_implies_xor_false_general A B i j h
    rw [this] at hxor; exact absurd hxor (by decide)

/-! ## Section 5: Anti-Phantoms EXIST for Non-Affine Gap Sets -/

/-- Transfer operator for mask m, sharing bit b between source and target. -/
private def mkTransfer (m1 m2 : Fin 256) (b : Fin 3) : BoolMat 8 :=
  fun g1 g2 =>
    let bit1 := (m1.val >>> g1.val) &&& 1 == 1
    let bit2 := (m2.val >>> g2.val) &&& 1 == 1
    bit1 && bit2 && (Cube.vertexBit g1 b == Cube.vertexBit g2 b)

/-- **Anti-phantom witness**: For 3-SAT cubes (mask 254 = 7 gaps),
    exists (i,j) where BoolMat.mul = true but XorMat.mul = false. -/
theorem anti_phantom_exists_3sat :
    let T := mkTransfer ⟨254, by omega⟩ ⟨254, by omega⟩ ⟨0, by omega⟩
    ∃ i j : Fin 8,
      BoolMat.mul T T i j = true ∧
      XorMat.mul T T i j = false := by
  native_decide

/-- Anti-phantoms for mask 127 (vertex 7 forbidden, 7 gaps). -/
theorem anti_phantom_exists_mask127 :
    let T := mkTransfer ⟨127, by omega⟩ ⟨127, by omega⟩ ⟨0, by omega⟩
    ∃ i j : Fin 8,
      BoolMat.mul T T i j = true ∧
      XorMat.mul T T i j = false := by
  native_decide

/-- Anti-phantoms for 5-gap mask (mask 251, vertex 2 forbidden). -/
theorem anti_phantom_exists_5gaps :
    let T := mkTransfer ⟨251, by omega⟩ ⟨251, by omega⟩ ⟨0, by omega⟩
    ∃ i j : Fin 8,
      BoolMat.mul T T i j = true ∧
      XorMat.mul T T i j = false := by
  native_decide

/-! ## Section 6: Counting Anti-Phantoms vs Phantoms -/

/-- Count phantom entries (XOR=true, OR=false) for self-composition. -/
private def phantomCount (m : Fin 256) (b : Fin 3) : Nat :=
  let T := mkTransfer m m b
  let Tbool := BoolMat.mul T T
  let Txor := XorMat.mul T T
  (List.finRange 8).foldl (fun acc i =>
    acc + (List.finRange 8).foldl (fun acc2 j =>
      if Txor i j && !Tbool i j then acc2 + 1 else acc2) 0) 0

/-- Count anti-phantom entries (OR=true, XOR=false) for self-composition. -/
private def antiPhantomCount (m : Fin 256) (b : Fin 3) : Nat :=
  let T := mkTransfer m m b
  let Tbool := BoolMat.mul T T
  let Txor := XorMat.mul T T
  (List.finRange 8).foldl (fun acc i =>
    acc + (List.finRange 8).foldl (fun acc2 j =>
      if Tbool i j && !Txor i j then acc2 + 1 else acc2) 0) 0

/-- Zero phantoms for mask 254 (7-gap, 3-SAT). -/
theorem zero_phantoms_254 :
    phantomCount ⟨254, by omega⟩ ⟨0, by omega⟩ = 0 ∧
    phantomCount ⟨254, by omega⟩ ⟨1, by omega⟩ = 0 ∧
    phantomCount ⟨254, by omega⟩ ⟨2, by omega⟩ = 0 := by
  native_decide

/-- Zero phantoms for mask 127 (vertex 7 forbidden, 7-gap). -/
theorem zero_phantoms_127 :
    phantomCount ⟨127, by omega⟩ ⟨0, by omega⟩ = 0 ∧
    phantomCount ⟨127, by omega⟩ ⟨1, by omega⟩ = 0 ∧
    phantomCount ⟨127, by omega⟩ ⟨2, by omega⟩ = 0 := by
  native_decide

/-- Anti-phantom count is positive for mask 254 (7 gaps). -/
theorem anti_phantom_count_positive_254 :
    antiPhantomCount ⟨254, by omega⟩ ⟨0, by omega⟩ > 0 := by
  native_decide

/-! ## Section 7: Exhaustive No-Phantom Verification -/

/-- No phantoms for ALL 8 single-clause masks, all 3 shared bits.
    24 independent verifications: 8 masks x 3 bits. -/
theorem no_phantoms_all_single_clause :
    phantomCount ⟨254, by omega⟩ ⟨0, by omega⟩ = 0 ∧
    phantomCount ⟨254, by omega⟩ ⟨1, by omega⟩ = 0 ∧
    phantomCount ⟨254, by omega⟩ ⟨2, by omega⟩ = 0 ∧
    phantomCount ⟨253, by omega⟩ ⟨0, by omega⟩ = 0 ∧
    phantomCount ⟨253, by omega⟩ ⟨1, by omega⟩ = 0 ∧
    phantomCount ⟨253, by omega⟩ ⟨2, by omega⟩ = 0 ∧
    phantomCount ⟨251, by omega⟩ ⟨0, by omega⟩ = 0 ∧
    phantomCount ⟨251, by omega⟩ ⟨1, by omega⟩ = 0 ∧
    phantomCount ⟨251, by omega⟩ ⟨2, by omega⟩ = 0 ∧
    phantomCount ⟨247, by omega⟩ ⟨0, by omega⟩ = 0 ∧
    phantomCount ⟨247, by omega⟩ ⟨1, by omega⟩ = 0 ∧
    phantomCount ⟨247, by omega⟩ ⟨2, by omega⟩ = 0 ∧
    phantomCount ⟨239, by omega⟩ ⟨0, by omega⟩ = 0 ∧
    phantomCount ⟨239, by omega⟩ ⟨1, by omega⟩ = 0 ∧
    phantomCount ⟨239, by omega⟩ ⟨2, by omega⟩ = 0 ∧
    phantomCount ⟨223, by omega⟩ ⟨0, by omega⟩ = 0 ∧
    phantomCount ⟨223, by omega⟩ ⟨1, by omega⟩ = 0 ∧
    phantomCount ⟨223, by omega⟩ ⟨2, by omega⟩ = 0 ∧
    phantomCount ⟨191, by omega⟩ ⟨0, by omega⟩ = 0 ∧
    phantomCount ⟨191, by omega⟩ ⟨1, by omega⟩ = 0 ∧
    phantomCount ⟨191, by omega⟩ ⟨2, by omega⟩ = 0 ∧
    phantomCount ⟨127, by omega⟩ ⟨0, by omega⟩ = 0 ∧
    phantomCount ⟨127, by omega⟩ ⟨1, by omega⟩ = 0 ∧
    phantomCount ⟨127, by omega⟩ ⟨2, by omega⟩ = 0 := by
  native_decide

/-! ## Section 8: OR and XOR Compositions Differ on 3-SAT -/

/-- OR and XOR self-compositions of the 7-gap transfer operator DIFFER. -/
theorem or_neq_xor_composition_254 :
    let T := mkTransfer ⟨254, by omega⟩ ⟨254, by omega⟩ ⟨0, by omega⟩
    BoolMat.mul T T ≠ XorMat.mul T T := by
  simp only
  intro h
  have ⟨i, j, h_or, h_xor⟩ := anti_phantom_exists_3sat
  -- h : BoolMat.mul T T = XorMat.mul T T
  -- So BoolMat.mul T T i j = XorMat.mul T T i j
  rw [h] at h_or
  -- Now h_or : XorMat.mul T T i j = true, h_xor : XorMat.mul T T i j = false
  rw [h_or] at h_xor
  exact absurd h_xor (by decide)

/-! ## Section 9: The Grand Synthesis -/

/-- **Grand Synthesis**: The complete XOR impossibility for 3-SAT.

    (1) No phantoms: XOR never overpromises (OR dominates XOR)
    (2) Anti-phantoms exist: XOR underpromises on 3-SAT
    (3) OR and XOR differ on 7-gap operators
    (4) Non-affine: 7 gaps is not a power of 2
    (5) OR irreversible: rank-1 aperiodicity M^3 = M^2 -/
theorem grand_synthesis_xor_impossible :
    -- (1) No phantoms ever
    (∀ A B : BoolMat 8, ¬ HasPhantom A B) ∧
    -- (2) Anti-phantoms exist for 3-SAT
    (let T := mkTransfer ⟨254, by omega⟩ ⟨254, by omega⟩ ⟨0, by omega⟩
     ∃ i j : Fin 8, BoolMat.mul T T i j = true ∧ XorMat.mul T T i j = false) ∧
    -- (3) OR neq XOR on 3-SAT operators
    (let T := mkTransfer ⟨254, by omega⟩ ⟨254, by omega⟩ ⟨0, by omega⟩
     BoolMat.mul T T ≠ XorMat.mul T T) ∧
    -- (4) Non-affine gap structure
    ¬ IsPowerOfTwo 7 ∧
    -- (5) OR composition is irreversible
    (∀ (m : Nat) (M : BoolMat m), M.IsRankOne →
      BoolMat.mul M (BoolMat.mul M M) = BoolMat.mul M M) := by
  exact ⟨
    no_phantoms,
    anti_phantom_exists_3sat,
    or_neq_xor_composition_254,
    seven_not_pow2,
    fun m M h => BoolMat.rank1_aperiodic h
  ⟩

end CubeGraph
