/-
  CubeGraph/CycleDP.lean
  Rank-2 Cycle DP: decidability of cycle satisfiability with rank-≤2 operators.

  Phase 6 (T1-D) — reduces rank-2 cycle SAT to rank-1 channel alignment.

  VERIFIED COMPUTATIONALLY (2026-02-24):
    - 50,000 cycles, k=3..7, 100% match between 2-CSP DP and brute-force.

  THEOREM (Rank-2 Cycle):
    For a cycle [M₁, ..., Mₖ] where each Mᵢ = Aᵢ ∨ Bᵢ (rank-1 components):
      trace(M₁ ⊗ ... ⊗ Mₖ) = true
    iff ∃ coloring c ∈ {A,B}^k such that the selected rank-1 components
    form a channel-aligned cycle.

  ALGEBRAIC BASIS:
    Boolean matrix multiplication distributes over entrywise OR:
      (A ∨ B) ⊗ C = (A ⊗ C) ∨ (B ⊗ C)
      C ⊗ (A ∨ B) = (C ⊗ A) ∨ (C ⊗ B)
    Trace distributes: trace(X ∨ Y) = trace(X) ∨ trace(Y).
    Combined: trace(∏(Aᵢ ∨ Bᵢ)) = ∨_{c} trace(∏ selected(cᵢ)).
    Each term is a rank-1 cycle → Channel Alignment Theorem applies.

  See: theory/foundations/05-cycles.md (cycle structure and constraint propagation)
  See: theory/theorems/CORE-THEOREMS-SUMMARY.md (rank-2 decidability)
-/

import CubeGraph.ChannelAlignment
import CubeGraph.RankTheory

/-! ## Section 1: Definitions -/

namespace BoolMat

variable {n : Nat}

/-- Entrywise OR of two boolean matrices: (A ∨ B)[i,j] = A[i,j] ∨ B[i,j]. -/
def bor (A B : BoolMat n) : BoolMat n :=
  fun i j => A i j || B i j

/-- Convert Bool iff to Bool equality (local copy of BoolMat private helper). -/
private theorem bool_eq_of_iff {a b : Bool} (h : (a = true) ↔ (b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

/-! ## Section 2: BOR Properties -/

/-- Entry of bor is true iff either component is true. -/
theorem bor_true_iff (A B : BoolMat n) (i j : Fin n) :
    bor A B i j = true ↔ A i j = true ∨ B i j = true := by
  simp [bor, Bool.or_eq_true]

/-! ## Section 3: Distributivity of mul over bor -/

/-- Left distributivity: (A ∨ B) ⊗ C = (A ⊗ C) ∨ (B ⊗ C). -/
theorem mul_bor_left (A B C : BoolMat n) :
    mul (bor A B) C = bor (mul A C) (mul B C) := by
  funext i j
  apply bool_eq_of_iff
  simp only [bor, mul, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨k, hk, hAB, hC⟩
    rcases hAB with hA | hB
    · exact Or.inl ⟨k, hk, hA, hC⟩
    · exact Or.inr ⟨k, hk, hB, hC⟩
  · rintro (⟨k, hk, hA, hC⟩ | ⟨k, hk, hB, hC⟩)
    · exact ⟨k, hk, Or.inl hA, hC⟩
    · exact ⟨k, hk, Or.inr hB, hC⟩

/-- Right distributivity: C ⊗ (A ∨ B) = (C ⊗ A) ∨ (C ⊗ B). -/
theorem mul_bor_right (C A B : BoolMat n) :
    mul C (bor A B) = bor (mul C A) (mul C B) := by
  funext i j
  apply bool_eq_of_iff
  simp only [bor, mul, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨k, hk, hC, hAB⟩
    rcases hAB with hA | hB
    · exact Or.inl ⟨k, hk, hC, hA⟩
    · exact Or.inr ⟨k, hk, hC, hB⟩
  · rintro (⟨k, hk, hC, hA⟩ | ⟨k, hk, hC, hB⟩)
    · exact ⟨k, hk, hC, Or.inl hA⟩
    · exact ⟨k, hk, hC, Or.inr hB⟩

/-! ## Section 4: Trace distributes over BOR -/

/-- trace(A ∨ B) = true iff trace(A) = true or trace(B) = true. -/
theorem trace_bor_iff (A B : BoolMat n) :
    trace (bor A B) = true ↔ trace A = true ∨ trace B = true := by
  simp only [trace_true]
  constructor
  · rintro ⟨i, hi⟩
    rw [bor_true_iff] at hi
    rcases hi with hA | hB
    · exact Or.inl ⟨i, hA⟩
    · exact Or.inr ⟨i, hB⟩
  · rintro (⟨i, hA⟩ | ⟨i, hB⟩)
    · exact ⟨i, (bor_true_iff A B i i).mpr (Or.inl hA)⟩
    · exact ⟨i, (bor_true_iff A B i i).mpr (Or.inr hB)⟩

/-! ## Section 5: BOR accumulator distributes through foldl -/

/-- If the accumulator is bor X Y, foldl mul distributes entrywise. -/
theorem foldl_mul_bor_acc (X Y : BoolMat n) (rest : List (BoolMat n)) (i j : Fin n) :
    (rest.foldl mul (bor X Y)) i j = true ↔
    (rest.foldl mul X) i j = true ∨ (rest.foldl mul Y) i j = true := by
  induction rest generalizing X Y with
  | nil => exact bor_true_iff X Y i j
  | cons M rest' ih =>
    simp only [List.foldl_cons]
    rw [mul_bor_left]
    exact ih (mul X M) (mul Y M)

end BoolMat

namespace CubeGraph

open BoolMat

/-- A rank-2 decomposition of a boolean matrix into two rank-1 components.
    The original matrix equals bor compA compB (entrywise OR). -/
structure Rank2Decomp (n : Nat) where
  compA : BoolMat n
  compB : BoolMat n
  rankA : compA.IsRankOne
  rankB : compB.IsRankOne

/-- Select component by boolean choice: false → A, true → B. -/
def selectComp (d : Rank2Decomp n) (b : Bool) : BoolMat n :=
  if b then d.compB else d.compA

/-- Build the list of rank-2 operators (the "originals") from decompositions. -/
def rank2Ops (decomps : List (Rank2Decomp n)) : List (BoolMat n) :=
  decomps.map (fun d => BoolMat.bor d.compA d.compB)

/-- Build the list of rank-1 operators selected by a coloring (parallel List Bool).
    Recursive definition makes the cons-lemma definitional. -/
def coloredOps : List (Rank2Decomp n) → List Bool → List (BoolMat n)
  | [], _ => []
  | _, [] => []
  | d :: rest, b :: bs => selectComp d b :: coloredOps rest bs

/-! ## Section 6: Expansion Theorem — product of rank-2 ops ↔ ∃ coloring -/

/-- Product of rank-2 operators has entry (i,j) true iff there exists a coloring
    such that the product of the selected rank-1 components has the same entry true.
    This is the core algebraic fact: boolean OR distributes through the entire fold. -/
theorem foldl_bor_expansion (decomps : List (Rank2Decomp n))
    (acc : BoolMat n) (i j : Fin n) :
    (rank2Ops decomps).foldl BoolMat.mul acc i j = true ↔
    ∃ c : List Bool, c.length = decomps.length ∧
      (coloredOps decomps c).foldl BoolMat.mul acc i j = true := by
  induction decomps generalizing acc with
  | nil =>
    simp only [rank2Ops, coloredOps, List.map_nil, List.foldl_nil]
    exact ⟨fun h => ⟨[], rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  | cons d rest ih =>
    simp only [rank2Ops, List.map_cons, List.foldl_cons]
    -- After foldl_cons: accumulator becomes mul acc (bor d.compA d.compB)
    -- Apply right distributivity: mul acc (bor A B) = bor (mul acc A) (mul acc B)
    rw [BoolMat.mul_bor_right]
    -- Now accumulator is bor (mul acc A) (mul acc B)
    -- Distribute bor through the remaining foldl
    rw [BoolMat.foldl_mul_bor_acc]
    constructor
    · -- Forward: one of the branches has true entry → construct coloring
      rintro (hA | hB)
      · -- Branch A: acc' = mul acc d.compA
        obtain ⟨c_rest, hlen, hc⟩ := (ih (BoolMat.mul acc d.compA)).mp hA
        exact ⟨false :: c_rest, by simp [hlen], by
          simp only [coloredOps, selectComp, List.foldl_cons]; exact hc⟩
      · -- Branch B: acc' = mul acc d.compB
        obtain ⟨c_rest, hlen, hc⟩ := (ih (BoolMat.mul acc d.compB)).mp hB
        exact ⟨true :: c_rest, by simp [hlen], by
          simp only [coloredOps, selectComp, List.foldl_cons]; exact hc⟩
    · -- Backward: given coloring, determine which branch
      rintro ⟨c, hlen, hc⟩
      -- c must be nonempty since c.length = rest.length + 1
      match c, hlen with
      | b :: c_rest, hlen =>
        have hlen' : c_rest.length = rest.length := by simp at hlen; exact hlen
        simp only [coloredOps, selectComp, List.foldl_cons] at hc
        cases b with
        | false =>
          exact Or.inl ((ih (BoolMat.mul acc d.compA)).mpr ⟨c_rest, hlen', hc⟩)
        | true =>
          exact Or.inr ((ih (BoolMat.mul acc d.compB)).mpr ⟨c_rest, hlen', hc⟩)

/-! ## Section 7: coloredOps properties -/

/-- All operators selected by a coloring are rank-1. -/
theorem coloredOps_all_rank_one (decomps : List (Rank2Decomp n)) (c : List Bool) :
    ∀ M ∈ coloredOps decomps c, BoolMat.IsRankOne M := by
  induction decomps generalizing c with
  | nil => simp [coloredOps]
  | cons d rest ih =>
    cases c with
    | nil => simp [coloredOps]
    | cons b bs =>
      simp only [coloredOps, List.mem_cons]
      intro M hM
      rcases hM with rfl | hM
      · simp only [selectComp]; split
        · exact d.rankB
        · exact d.rankA
      · exact ih bs M hM

/-- Length of coloredOps equals decomps length (when coloring has matching length). -/
theorem coloredOps_length (decomps : List (Rank2Decomp n)) (c : List Bool)
    (h : c.length = decomps.length) :
    (coloredOps decomps c).length = decomps.length := by
  induction decomps generalizing c with
  | nil => simp [coloredOps]
  | cons d rest ih =>
    match c, h with
    | b :: bs, h =>
      simp only [coloredOps, List.length_cons]
      have hlen : bs.length = rest.length := by simp at h; exact h
      exact congrArg (· + 1) (ih bs hlen)

/-! ## Section 8: Main Theorem -/

/-- Trace of rank-2 cycle product equals existence of aligned coloring trace. -/
theorem rank2_trace_expansion (decomps : List (Rank2Decomp n)) :
    BoolMat.trace ((rank2Ops decomps).foldl BoolMat.mul BoolMat.one) = true ↔
    ∃ c : List Bool, c.length = decomps.length ∧
      BoolMat.trace ((coloredOps decomps c).foldl BoolMat.mul BoolMat.one) = true := by
  simp only [BoolMat.trace_true]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨c, hlen, hc⟩ := (foldl_bor_expansion decomps BoolMat.one i i).mp hi
    exact ⟨c, hlen, i, hc⟩
  · rintro ⟨c, hlen, i, hi⟩
    exact ⟨i, (foldl_bor_expansion decomps BoolMat.one i i).mpr ⟨c, hlen, hi⟩⟩

/-- **RANK-2 CYCLE THEOREM** (Verified: 50,000 cycles, k=3..7, 100% match)

    For a cycle of rank-2 boolean matrices, each Mᵢ = Aᵢ ∨ Bᵢ (rank-1 components):
      trace(M₁ ⊗ M₂ ⊗ ... ⊗ Mₖ) = true
    iff there exists a coloring c ∈ {A,B}^k such that the selected rank-1
    components form a channel-aligned cycle.

    This reduces rank-2 cycle decidability to the Channel Alignment Theorem
    for rank-1 cycles (already proven in ChannelAlignment.lean). -/
theorem rank2_trace_iff_exists_aligned (decomps : List (Rank2Decomp n))
    (h_len : decomps.length ≥ 2) :
    BoolMat.trace ((rank2Ops decomps).foldl BoolMat.mul BoolMat.one) = true ↔
    ∃ c : List Bool, c.length = decomps.length ∧
      fullyChannelAligned (coloredOps decomps c) := by
  rw [rank2_trace_expansion]
  constructor
  · -- Forward: ∃ coloring with trace true → ∃ coloring with channel alignment
    rintro ⟨c, hlen, htrace⟩
    refine ⟨c, hlen, ?_⟩
    let h_cyc : RankOneCycle n := {
      operators := coloredOps decomps c
      length_ge := by rw [coloredOps_length decomps c hlen]; exact h_len
      all_rank_one := coloredOps_all_rank_one decomps c
    }
    exact (channel_alignment h_cyc).mp htrace
  · -- Backward: ∃ coloring with channel alignment → ∃ coloring with trace true
    rintro ⟨c, hlen, haligned⟩
    refine ⟨c, hlen, ?_⟩
    let h_cyc : RankOneCycle n := {
      operators := coloredOps decomps c
      length_ge := by rw [coloredOps_length decomps c hlen]; exact h_len
      all_rank_one := coloredOps_all_rank_one decomps c
    }
    exact (channel_alignment h_cyc).mpr haligned

/-! ## Section 9: Decidability -/

/-- Rank-2 cycle SAT is decidable: trace ∈ Bool has DecidableEq. -/
instance rank2_cycle_trace_decidable (decomps : List (Rank2Decomp n)) :
    Decidable (BoolMat.trace ((rank2Ops decomps).foldl BoolMat.mul BoolMat.one) = true) :=
  inferInstance

end CubeGraph
