/-
  CubeGraph/ChannelAlignment.lean
  Channel Alignment Theorem for Rank-1 Boolean Cycles.

  VERIFIED COMPUTATIONALLY (2026-02-24):
    - 344,736 / 344,736 cycles at k=3 (100.0% match)
    - 100,000 / 100,000 cycles at k=4 (100.0% match)
    - 100,000 / 100,000 cycles at k=5 (100.0% match)
    Zero mismatches. Zero false positives/negatives.

  THEOREM (Channel Alignment):
    For a cycle of cubes where every edge transfer operator is rank-1
    (as a boolean matrix over ℝ), the cycle is satisfiable iff at every
    cube the "incoming" compatible gaps overlap the "outgoing" compatible gaps.

  ALGEBRAIC BASIS:
    A rank-1 boolean 8×8 matrix M has all nonzero rows identical:
      M[i,j] = 1 iff rowSup(M)(i) ∧ colSup(M)(j)
    i.e., M = 1_{R} · 1_{C}ᵀ (outer product of indicator vectors).

    For composition: (A ⊗ B)[i,j] = ∨_k (A[i,k] ∧ B[k,j])
    If A = 1_R_A · 1_C_A^T and B = 1_R_B · 1_C_B^T, then:
      A ⊗ B = 0          if C_A ∩ R_B = ∅
      A ⊗ B = 1_R_A · 1_C_B^T   otherwise (still rank-1)

  INTERDISCIPLINARY CONNECTIONS:
    - Percolation theory: each cube = site, transmits iff incoming ∩ outgoing ≠ ∅
    - Tropical algebra: rank-1 composition = tropical singularity detection
    - Shannon theory: channel capacity = 0 when alphabets disjoint
    - Matroid theory: alignment = non-empty flat intersection

  See: theory/foundations/05-cycles.md (cycle structure in CubeGraph)
  See: theory/theorems/THEOREM-A-HIERARCHY.md (H¹ detection via blocked edges)
-/

import CubeGraph.Basic

/-! ## BoolMat: Support and Rank-1 Definitions

  We extend the BoolMat namespace with support and rank-1 concepts.
  Supports are represented as indicator functions (Fin n → Bool). -/

namespace BoolMat

variable {n : Nat}

/-- Row support: indicator function for rows with at least one true entry. -/
def rowSup (M : BoolMat n) : Fin n → Bool :=
  fun i => (List.finRange n).any fun j => M i j

/-- Column support: indicator function for columns with at least one true entry. -/
def colSup (M : BoolMat n) : Fin n → Bool :=
  fun j => (List.finRange n).any fun i => M i j

/-- Two indicator functions are disjoint: no index is true in both. -/
def IndDisjoint (R S : Fin n → Bool) : Prop :=
  ∀ k : Fin n, ¬(R k = true ∧ S k = true)

/-- An indicator function is nonempty: some index is true. -/
def IndNonempty (R : Fin n → Bool) : Prop :=
  ∃ k : Fin n, R k = true

/-- A boolean matrix is rank-1 iff it factors as an outer product.
    Equivalently: ∃ R C : Fin n → Bool nonempty s.t. M i j = true ↔ R i ∧ C j. -/
def IsRankOne (M : BoolMat n) : Prop :=
  ∃ (R C : Fin n → Bool),
    IndNonempty R ∧ IndNonempty C ∧
    ∀ i j, M i j = true ↔ (R i = true ∧ C j = true)

/-! ### Helper Lemmas: rowSup and colSup membership -/

theorem mem_rowSup_iff {M : BoolMat n} {i : Fin n} :
    M.rowSup i = true ↔ ∃ j : Fin n, M i j = true := by
  simp only [rowSup, List.any_eq_true]
  constructor
  · rintro ⟨j, _, hj⟩; exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩; exact ⟨j, mem_finRange j, hj⟩

theorem mem_colSup_iff {M : BoolMat n} {j : Fin n} :
    M.colSup j = true ↔ ∃ i : Fin n, M i j = true := by
  simp only [colSup, List.any_eq_true]
  constructor
  · rintro ⟨i, _, hi⟩; exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩; exact ⟨i, mem_finRange i, hi⟩

/-! ## Theorem 1: Rank-1 outer product form -/

/-- If M is rank-1, the witnesses can be taken to be rowSup M and colSup M. -/
theorem rankOne_outer_product {M : BoolMat n}
    (h : M.IsRankOne) :
    ∃ (R C : Fin n → Bool),
      R = M.rowSup ∧ C = M.colSup ∧
      ∀ i j, M i j = true ↔ (R i = true ∧ C j = true) := by
  obtain ⟨R, C, hR, hC, hRC⟩ := h
  -- Use rowSup M and colSup M as the canonical witnesses
  refine ⟨M.rowSup, M.colSup, rfl, rfl, ?_⟩
  intro i j
  constructor
  · -- M i j = true → rowSup i ∧ colSup j
    intro hij
    exact ⟨mem_rowSup_iff.mpr ⟨j, hij⟩, mem_colSup_iff.mpr ⟨i, hij⟩⟩
  · -- rowSup i = true ∧ colSup j = true → M i j = true
    intro ⟨hi_row, hj_col⟩
    -- From rowSup i: ∃ j', M i j' = true → i ∈ R
    obtain ⟨j', hj'⟩ := mem_rowSup_iff.mp hi_row
    have hi_R : R i = true := ((hRC i j').mp hj').1
    -- From colSup j: ∃ i', M i' j = true → j ∈ C
    obtain ⟨i', hi'⟩ := mem_colSup_iff.mp hj_col
    have hj_C : C j = true := ((hRC i' j).mp hi').2
    exact (hRC i j).mpr ⟨hi_R, hj_C⟩

/-! ## Theorem 2: Rank-1 composition -/

/-- Zero iff disjoint: A ⊗ B = 0 iff colSup(A) ∩ rowSup(B) = ∅. -/
theorem rankOne_mul_zero_iff {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne) :
    BoolMat.isZero (BoolMat.mul A B) ↔
    IndDisjoint A.colSup B.rowSup := by
  obtain ⟨RA, CA, _hRA, _hCA, hA_char⟩ := hA
  obtain ⟨RB, CB, _hRB, _hCB, hB_char⟩ := hB
  simp only [isZero, IndDisjoint]
  constructor
  · -- isZero → IndDisjoint
    intro h_zero k ⟨hk_colA, hk_rowB⟩
    obtain ⟨i, hiA⟩ := mem_colSup_iff.mp hk_colA
    obtain ⟨j, hjB⟩ := mem_rowSup_iff.mp hk_rowB
    have hmul : mul A B i j = true := mul_apply_true A B i j |>.mpr ⟨k, hiA, hjB⟩
    rw [h_zero i j] at hmul
    exact Bool.false_ne_true hmul
  · -- IndDisjoint → isZero
    intro h_disj i j
    -- Suppose mul A B i j = true for contradiction
    cases h : mul A B i j with
    | true =>
      obtain ⟨k, hAik, hBkj⟩ := (mul_apply_true A B i j).mp h
      have hk_colA : A.colSup k = true := mem_colSup_iff.mpr ⟨i, hAik⟩
      have hk_rowB : B.rowSup k = true := mem_rowSup_iff.mpr ⟨j, hBkj⟩
      exact absurd ⟨hk_colA, hk_rowB⟩ (h_disj k)
    | false => rfl

/-- Rank-1 mul rank-1 = rank-1 (when supports connect). -/
theorem rankOne_mul_rankOne {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne)
    (h_connect : ¬ IndDisjoint A.colSup B.rowSup) :
    (BoolMat.mul A B).IsRankOne := by
  obtain ⟨RA, CA, hRA, hCA, hA_char⟩ := hA
  obtain ⟨RB, CB, hRB, hCB, hB_char⟩ := hB
  -- Extract shared element from ¬ IndDisjoint
  -- h_connect : ¬ (∀ k, ¬(A.colSup k = true ∧ B.rowSup k = true))
  -- We need: ∃ k, A.colSup k = true ∧ B.rowSup k = true
  have h_ex : ∃ k : Fin n, A.colSup k = true ∧ B.rowSup k = true :=
    Classical.byContradiction (fun h_none => h_connect (fun k hk => h_none ⟨k, hk⟩))
  obtain ⟨k, hk_colA, hk_rowB⟩ := h_ex
  -- Map k back to the witness sets CA and RB
  have hk_in_CA : CA k = true := by
    obtain ⟨i', hi'⟩ := mem_colSup_iff.mp hk_colA
    exact ((hA_char i' k).mp hi').2
  have hk_in_RB : RB k = true := by
    obtain ⟨j', hj'⟩ := mem_rowSup_iff.mp hk_rowB
    exact ((hB_char k j').mp hj').1
  -- mul A B is rank-1 with witnesses RA and CB
  refine ⟨RA, CB, hRA, hCB, ?_⟩
  intro i j
  constructor
  · -- mul A B i j = true → i ∈ RA ∧ j ∈ CB
    intro hmul
    obtain ⟨m, hAim, hBmj⟩ := (mul_apply_true A B i j).mp hmul
    exact ⟨((hA_char i m).mp hAim).1, ((hB_char m j).mp hBmj).2⟩
  · -- i ∈ RA ∧ j ∈ CB → mul A B i j = true
    intro ⟨hi_RA, hj_CB⟩
    exact (mul_apply_true A B i j).mpr
      ⟨k, (hA_char i k).mpr ⟨hi_RA, hk_in_CA⟩,
           (hB_char k j).mpr ⟨hk_in_RB, hj_CB⟩⟩

/-! ## Helper lemmas for Channel Alignment proof -/

/-- IndDisjoint is symmetric (since ∧ is commutative). -/
theorem IndDisjoint_comm (R S : Fin n → Bool) :
    IndDisjoint R S ↔ IndDisjoint S R := by
  simp only [IndDisjoint]
  constructor <;> (intro h k hk; exact h k ⟨hk.2, hk.1⟩)

/-- Negation of IndDisjoint: there exists a shared element. -/
theorem not_IndDisjoint_iff (R S : Fin n → Bool) :
    ¬ IndDisjoint R S ↔ ∃ k : Fin n, R k = true ∧ S k = true := by
  constructor
  · intro h
    exact Classical.byContradiction fun h_neg =>
      h fun k hk => h_neg ⟨k, hk⟩
  · intro ⟨k, hk⟩ h_disj
    exact h_disj k hk

/-- Trace of a rank-1 matrix: true iff rowSup and colSup share an element. -/
theorem trace_rankOne_iff {M : BoolMat n} (h : M.IsRankOne) :
    M.trace = true ↔ ¬ IndDisjoint M.rowSup M.colSup := by
  obtain ⟨R, C, hR_ne, hC_ne, hRC⟩ := h
  rw [trace_true, not_IndDisjoint_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, mem_rowSup_iff.mpr ⟨g, hg⟩, mem_colSup_iff.mpr ⟨g, hg⟩⟩
  · rintro ⟨g, hrow, hcol⟩
    obtain ⟨j, hj⟩ := mem_rowSup_iff.mp hrow
    obtain ⟨i, hi⟩ := mem_colSup_iff.mp hcol
    -- g is in rowSup → R g; g is in colSup → C g
    have hRg : R g = true := ((hRC g j).mp hj).1
    have hCg : C g = true := ((hRC i g).mp hi).2
    exact ⟨g, (hRC g g).mpr ⟨hRg, hCg⟩⟩

/-- If the accumulator is zero, foldl stays zero. -/
theorem isZero_foldl_mul (acc : BoolMat n) (rest : List (BoolMat n))
    (h : isZero acc) : isZero (rest.foldl mul acc) := by
  induction rest generalizing acc with
  | nil => exact h
  | cons M rest' ih =>
    simp only [List.foldl_cons]
    apply ih
    intro i j
    cases hmul : mul acc M i j with
    | false => rfl
    | true =>
      obtain ⟨k, hk1, _⟩ := (mul_apply_true acc M i j).mp hmul
      rw [h i k] at hk1; exact absurd hk1 (by decide)

/-- Rank-1 product characterization: rowSup of product = rowSup of A. -/
theorem rankOne_mul_rowSup {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne)
    (h_conn : ¬ IndDisjoint A.colSup B.rowSup) :
    (mul A B).rowSup = A.rowSup := by
  obtain ⟨RA, CA, _hRA_ne, _hCA_ne, hA_char⟩ := hA
  obtain ⟨RB, CB, _hRB_ne, hCB_ne, hB_char⟩ := hB
  funext i; apply Bool.eq_iff_iff.mpr; rw [mem_rowSup_iff, mem_rowSup_iff]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨_, (mul_apply_true A B i j).mp hj |>.choose_spec.1⟩
  · rintro ⟨j, hij⟩
    have hRA_i := ((hA_char i j).mp hij).1
    obtain ⟨m, hm_colA, hm_rowB⟩ := (not_IndDisjoint_iff _ _).mp h_conn
    obtain ⟨i', hi'⟩ := mem_colSup_iff.mp hm_colA
    obtain ⟨j', hj'⟩ := mem_rowSup_iff.mp hm_rowB
    obtain ⟨p, hCB_p⟩ := hCB_ne
    exact ⟨p, (mul_apply_true A B i p).mpr
      ⟨m, (hA_char i m).mpr ⟨hRA_i, ((hA_char i' m).mp hi').2⟩,
          (hB_char m p).mpr ⟨((hB_char m j').mp hj').1, hCB_p⟩⟩⟩

/-- Rank-1 product characterization: colSup of product = colSup of B. -/
theorem rankOne_mul_colSup {A B : BoolMat n}
    (hA : A.IsRankOne) (hB : B.IsRankOne)
    (h_conn : ¬ IndDisjoint A.colSup B.rowSup) :
    (mul A B).colSup = B.colSup := by
  obtain ⟨RA, CA, hRA_ne, _hCA_ne, hA_char⟩ := hA
  obtain ⟨RB, CB, _hRB_ne, _hCB_ne, hB_char⟩ := hB
  funext j; apply Bool.eq_iff_iff.mpr; rw [mem_colSup_iff, mem_colSup_iff]
  constructor
  · rintro ⟨i, hij⟩
    exact ⟨_, (mul_apply_true A B i j).mp hij |>.choose_spec.2⟩
  · rintro ⟨i, hij⟩
    have hCB_j := ((hB_char i j).mp hij).2
    obtain ⟨m, hm_colA, hm_rowB⟩ := (not_IndDisjoint_iff _ _).mp h_conn
    obtain ⟨i', hi'⟩ := mem_colSup_iff.mp hm_colA
    obtain ⟨j', hj'⟩ := mem_rowSup_iff.mp hm_rowB
    obtain ⟨r, hRA_r⟩ := hRA_ne
    exact ⟨r, (mul_apply_true A B r j).mpr
      ⟨m, (hA_char r m).mpr ⟨hRA_r, ((hA_char i' m).mp hi').2⟩,
          (hB_char m j).mpr ⟨((hB_char m j').mp hj').1, hCB_j⟩⟩⟩

end BoolMat

/-! ## Channel Alignment for Cycles -/

namespace CubeGraph

/-- A cycle of transfer operators, each rank-1, represented as a list of matrices. -/
structure RankOneCycle (n : Nat) where
  /-- The transfer operators around the cycle -/
  operators : List (BoolMat n)
  /-- Cycle has length ≥ 2 -/
  length_ge : operators.length ≥ 2
  /-- Every operator is rank-1 -/
  all_rank_one : ∀ M ∈ operators, BoolMat.IsRankOne M

/-- Channel alignment at position i: colSup of previous edge overlaps rowSup of next.
    Geometrically: cube i can "pass the signal" from predecessor to successor. -/
def channelAlignedAt (ops : List (BoolMat n)) (i : Fin ops.length) : Prop :=
  -- ops is nonempty since i : Fin ops.length
  have h_pos : 0 < ops.length := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let prev := ops.get ⟨(i.val + ops.length - 1) % ops.length, Nat.mod_lt _ h_pos⟩
  let next := ops.get i
  ¬ BoolMat.IndDisjoint prev.colSup next.rowSup

/-- A cycle is fully channel-aligned iff every position is aligned. -/
def fullyChannelAligned (ops : List (BoolMat n)) : Prop :=
  ∀ i : Fin ops.length, channelAlignedAt ops i

/-- All consecutive pairs in a chain are aligned (supports overlap). -/
def chainConnected : List (BoolMat n) → Prop
  | [] | [_] => True
  | A :: B :: rest => ¬BoolMat.IndDisjoint A.colSup B.rowSup ∧ chainConnected (B :: rest)

/-- If chainConnected, foldl of rank-1 matrices is rank-1 with preserved supports. -/
private theorem foldl_rankOne_of_connected (M : BoolMat n) :
    ∀ (rest : List (BoolMat n)),
    M.IsRankOne → (∀ N ∈ rest, BoolMat.IsRankOne N) →
    chainConnected (M :: rest) →
    (rest.foldl BoolMat.mul M).IsRankOne ∧
    (rest.foldl BoolMat.mul M).rowSup = M.rowSup ∧
    (∀ L, rest.getLast? = some L →
      (rest.foldl BoolMat.mul M).colSup = L.colSup) ∧
    (rest = [] → (rest.foldl BoolMat.mul M).colSup = M.colSup) := by
  intro rest
  induction rest generalizing M with
  | nil =>
    intro hM _ _
    exact ⟨hM, rfl, fun _ h => by simp at h, fun _ => rfl⟩
  | cons N rest' ih =>
    intro hM hrest hconn
    simp only [List.foldl_cons]
    have hN : N.IsRankOne := hrest N (List.mem_cons_self)
    have hrest' : ∀ P ∈ rest', BoolMat.IsRankOne P :=
      fun P hp => hrest P (List.mem_cons_of_mem _ hp)
    have hconn_pair : ¬BoolMat.IndDisjoint M.colSup N.rowSup := hconn.1
    have hconn_rest : chainConnected (N :: rest') := hconn.2
    have hMN_r1 := BoolMat.rankOne_mul_rankOne hM hN hconn_pair
    have hMN_row := BoolMat.rankOne_mul_rowSup hM hN hconn_pair
    have hMN_col := BoolMat.rankOne_mul_colSup hM hN hconn_pair
    have hconn_acc : chainConnected (BoolMat.mul M N :: rest') := by
      cases rest' with
      | nil => trivial
      | cons P _ =>
        exact ⟨hMN_col ▸ hconn_rest.1, hconn_rest.2⟩
    obtain ⟨hr1, hrow, hlast, hempty⟩ := ih (BoolMat.mul M N) hMN_r1 hrest' hconn_acc
    refine ⟨hr1, hrow.trans hMN_row, ?_, fun h => by simp at h⟩
    intro L hL
    cases rest' with
    | nil =>
      simp [List.getLast?] at hL
      subst hL
      exact (hempty rfl).trans hMN_col
    | cons P rest'' =>
      simp only [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at hL ⊢
      exact hlast L hL

/-- If some consecutive pair is disjoint, foldl produces zero. -/
private theorem foldl_rankOne_zero_of_disconnected (M : BoolMat n) :
    ∀ (rest : List (BoolMat n)),
    M.IsRankOne → (∀ N ∈ rest, BoolMat.IsRankOne N) →
    ¬ chainConnected (M :: rest) →
    BoolMat.isZero (rest.foldl BoolMat.mul M) := by
  intro rest
  induction rest generalizing M with
  | nil =>
    intro _ _ hconn
    exact absurd trivial hconn
  | cons N rest' ih =>
    intro hM hrest hconn
    simp only [List.foldl_cons]
    have hN : N.IsRankOne := hrest N (List.mem_cons_self)
    have hrest' : ∀ P ∈ rest', BoolMat.IsRankOne P :=
      fun P hp => hrest P (List.mem_cons_of_mem _ hp)
    -- Either M,N pair is disjoint, or the rest is disconnected
    by_cases h_pair : BoolMat.IndDisjoint M.colSup N.rowSup
    · -- Product M ⊗ N is zero, so foldl stays zero
      have h_zero := (BoolMat.rankOne_mul_zero_iff hM hN).mpr h_pair
      exact BoolMat.isZero_foldl_mul _ _ h_zero
    · -- Pair connects, but rest must be disconnected
      have hMN_col := BoolMat.rankOne_mul_colSup hM hN h_pair
      have hconn_acc : ¬ chainConnected (BoolMat.mul M N :: rest') := by
        intro h_conn_acc
        cases rest' with
        | nil => exact hconn ⟨h_pair, trivial⟩
        | cons P _ =>
          exact hconn ⟨h_pair, ⟨hMN_col ▸ h_conn_acc.1, h_conn_acc.2⟩⟩
      exact ih (BoolMat.mul M N)
        (BoolMat.rankOne_mul_rankOne hM hN h_pair) hrest' hconn_acc

/-- Modular index helper: (i+1 + k-1) % k = i when i+1 < k -/
private theorem mod_prev_succ (i k : Nat) (hi : i + 1 < k) :
    (i + 1 + k - 1) % k = i := by
  have hk : k ≥ 1 := by omega
  have : i + 1 + k - 1 = i + k := by omega
  rw [this, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- Extract consecutive pair alignment from fullyChannelAligned -/
private theorem aligned_consecutive (ops : List (BoolMat n))
    (h : fullyChannelAligned ops) (i : Nat) (hi : i + 1 < ops.length) :
    ¬BoolMat.IndDisjoint
      (ops.get ⟨i, by omega⟩).colSup
      (ops.get ⟨i + 1, hi⟩).rowSup := by
  have h_at := h ⟨i + 1, hi⟩
  simp only [channelAlignedAt] at h_at
  have h_mod := mod_prev_succ i ops.length hi
  have h_idx : (⟨(i + 1 + ops.length - 1) % ops.length,
    Nat.mod_lt _ (by omega)⟩ : Fin ops.length) = ⟨i, by omega⟩ := by
    ext; exact h_mod
  rw [h_idx] at h_at
  exact h_at

/-- Extract closing condition from fullyChannelAligned -/
private theorem aligned_closing (ops : List (BoolMat n))
    (h : fullyChannelAligned ops) (h_len : ops.length ≥ 2) :
    ¬BoolMat.IndDisjoint
      (ops.get ⟨ops.length - 1, by omega⟩).colSup
      (ops.get ⟨0, by omega⟩).rowSup := by
  have h_at := h ⟨0, by omega⟩
  simp only [channelAlignedAt] at h_at
  have h_mod : (0 + ops.length - 1) % ops.length = ops.length - 1 := by
    simp only [Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  have h_idx : (⟨(0 + ops.length - 1) % ops.length,
    Nat.mod_lt _ (by omega)⟩ : Fin ops.length) = ⟨ops.length - 1, by omega⟩ := by
    ext; exact h_mod
  rw [h_idx] at h_at
  exact h_at

/-- If all consecutive pairs are non-disjoint, the chain is connected. -/
private theorem chainConnected_of_consecutive (ops : List (BoolMat n))
    (h : ∀ (i : Nat) (hi : i + 1 < ops.length),
      ¬BoolMat.IndDisjoint (ops.get ⟨i, by omega⟩).colSup
        (ops.get ⟨i + 1, hi⟩).rowSup) :
    chainConnected ops := by
  induction ops with
  | nil => trivial
  | cons A tail ih =>
    cases tail with
    | nil => trivial
    | cons B rest =>
      refine ⟨h 0 (by simp), ?_⟩
      apply ih
      intro i hi
      exact h (i + 1) (by simp only [List.length] at hi ⊢; omega)

/-- Build chainConnected from fullyChannelAligned via aligned_consecutive -/
private theorem chainConnected_of_aligned (ops : List (BoolMat n))
    (h : fullyChannelAligned ops) : chainConnected ops :=
  chainConnected_of_consecutive ops fun i hi => aligned_consecutive ops h i hi

/-- Converse: chainConnected implies all consecutive pairs are non-disjoint. -/
private theorem consecutive_of_chainConnected (ops : List (BoolMat n))
    (h : chainConnected ops) (i : Nat) (hi : i + 1 < ops.length) :
    ¬BoolMat.IndDisjoint (ops.get ⟨i, by omega⟩).colSup
      (ops.get ⟨i + 1, hi⟩).rowSup := by
  induction ops generalizing i with
  | nil => simp at hi
  | cons A tail ih =>
    cases tail with
    | nil => simp at hi
    | cons B rest =>
      cases i with
      | zero => exact h.1
      | succ j => exact ih h.2 j (by simp only [List.length] at hi ⊢; omega)

/-- Last element: (hd :: tl).get ⟨tl.length⟩ = tl.getLast -/
private theorem cons_get_last (hd : α) (tl : List α) (h : tl ≠ []) :
    (hd :: tl).get ⟨tl.length, by simp⟩ = tl.getLast h := by
  induction tl generalizing hd with
  | nil => exact absurd rfl h
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      simp only [List.getLast_cons (List.cons_ne_nil _ _)]
      exact ih a (List.cons_ne_nil _ _)

/-- The closing condition extracted from fullyChannelAligned in usable form. -/
private theorem closing_of_aligned (hd : BoolMat n) (tl : List (BoolMat n))
    (h_tl : tl ≠ [])
    (h_aligned : fullyChannelAligned (hd :: tl)) :
    ¬BoolMat.IndDisjoint (tl.getLast h_tl).colSup hd.rowSup := by
  have h_len : (hd :: tl).length ≥ 2 := by
    cases tl with | nil => exact absurd rfl h_tl | cons _ _ => simp [List.length]
  have h_close := aligned_closing (hd :: tl) h_aligned h_len
  have h_fin_eq : (⟨(hd :: tl).length - 1, (by omega)⟩ : Fin (hd :: tl).length) =
    ⟨tl.length, by simp⟩ := by ext; simp
  rw [h_fin_eq, cons_get_last hd tl h_tl] at h_close
  exact h_close

/-- channelAlignedAt at j+1 follows from consecutive pair non-disjointness.
    (Reverse of aligned_consecutive — same index arithmetic, reversed direction.) -/
private theorem channelAlignedAt_of_consecutive (ops : List (BoolMat n))
    (h_consec : ∀ (i : Nat) (hi : i + 1 < ops.length),
      ¬BoolMat.IndDisjoint (ops.get ⟨i, by omega⟩).colSup
        (ops.get ⟨i + 1, hi⟩).rowSup)
    (j : Nat) (hj : j + 1 < ops.length) :
    channelAlignedAt ops ⟨j + 1, hj⟩ := by
  -- Same index arithmetic as aligned_consecutive, reversed direction
  simp only [channelAlignedAt]
  have h_mod := mod_prev_succ j ops.length hj
  have h_idx : (⟨(j + 1 + ops.length - 1) % ops.length,
    Nat.mod_lt _ (by omega)⟩ : Fin ops.length) = ⟨j, by omega⟩ := by
    ext; exact h_mod
  rw [h_idx]
  exact h_consec j hj

/-- channelAlignedAt at 0 follows from the closing condition. -/
private theorem channelAlignedAt_zero_of_closing (hd : BoolMat n) (tl : List (BoolMat n))
    (h_tl : tl ≠ [])
    (h_close : ¬BoolMat.IndDisjoint (tl.getLast h_tl).colSup hd.rowSup) :
    channelAlignedAt (hd :: tl) ⟨0, by simp⟩ := by
  simp only [channelAlignedAt]
  have h_mod : (0 + (hd :: tl).length - 1) % (hd :: tl).length = tl.length := by
    simp only [List.length, Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
  have h_idx : (⟨(0 + (hd :: tl).length - 1) % (hd :: tl).length,
    Nat.mod_lt _ (by simp [List.length])⟩ : Fin (hd :: tl).length) =
    ⟨tl.length, by simp⟩ := by ext; exact h_mod
  rw [h_idx, cons_get_last hd tl h_tl]
  exact h_close

/-- Backward: fullyChannelAligned → trace = true -/
private theorem channel_alignment_backward (ops : List (BoolMat n))
    (h_len : ops.length ≥ 2)
    (h_r1 : ∀ M ∈ ops, BoolMat.IsRankOne M)
    (h_aligned : fullyChannelAligned ops) :
    BoolMat.trace (ops.foldl BoolMat.mul BoolMat.one) = true := by
  obtain ⟨hd, tl, rfl⟩ : ∃ hd tl, ops = hd :: tl := by
    cases ops with | nil => simp at h_len | cons h t => exact ⟨h, t, rfl⟩
  have h_tl_ne : tl ≠ [] := by intro h; subst h; simp at h_len
  change BoolMat.trace (List.foldl BoolMat.mul (BoolMat.mul BoolMat.one hd) tl) = true
  rw [BoolMat.one_mul]
  have hd_r1 : hd.IsRankOne := h_r1 hd (List.mem_cons_self)
  have tl_r1 : ∀ M ∈ tl, M.IsRankOne := fun M hM => h_r1 M (List.mem_cons_of_mem _ hM)
  have h_chain := chainConnected_of_aligned (hd :: tl) h_aligned
  obtain ⟨h_r1p, h_rowp, h_lastp, _⟩ := foldl_rankOne_of_connected hd tl hd_r1 tl_r1 h_chain
  have h_colp := h_lastp (tl.getLast h_tl_ne) (List.getLast?_eq_some_getLast h_tl_ne)
  rw [BoolMat.trace_rankOne_iff h_r1p, h_rowp, h_colp, BoolMat.IndDisjoint_comm]
  exact closing_of_aligned hd tl h_tl_ne h_aligned

/-- Forward: trace = true → fullyChannelAligned -/
private theorem channel_alignment_forward (ops : List (BoolMat n))
    (h_len : ops.length ≥ 2)
    (h_r1 : ∀ M ∈ ops, BoolMat.IsRankOne M)
    (h_trace : BoolMat.trace (ops.foldl BoolMat.mul BoolMat.one) = true) :
    fullyChannelAligned ops := by
  obtain ⟨hd, tl, rfl⟩ : ∃ hd tl, ops = hd :: tl := by
    cases ops with | nil => simp at h_len | cons h t => exact ⟨h, t, rfl⟩
  have h_tl_ne : tl ≠ [] := by intro h; subst h; simp at h_len
  change BoolMat.trace (List.foldl BoolMat.mul (BoolMat.mul BoolMat.one hd) tl) = true at h_trace
  rw [BoolMat.one_mul] at h_trace
  have hd_r1 : hd.IsRankOne := h_r1 hd (List.mem_cons_self)
  have tl_r1 : ∀ M ∈ tl, M.IsRankOne := fun M hM => h_r1 M (List.mem_cons_of_mem _ hM)
  -- Product is not zero (since trace = true)
  have h_not_zero : ¬BoolMat.isZero (tl.foldl BoolMat.mul hd) := by
    intro h_zero
    have h_eq := BoolMat.trace_of_isZero h_zero
    rw [h_eq] at h_trace
    exact Bool.false_ne_true h_trace
  -- Chain is connected (contrapositive of zero_of_disconnected)
  have h_chain : chainConnected (hd :: tl) := by
    apply Classical.byContradiction; intro h_not
    exact h_not_zero (foldl_rankOne_zero_of_disconnected hd tl hd_r1 tl_r1 h_not)
  -- Product properties
  obtain ⟨h_r1p, h_rowp, h_lastp, _⟩ := foldl_rankOne_of_connected hd tl hd_r1 tl_r1 h_chain
  have h_colp := h_lastp (tl.getLast h_tl_ne) (List.getLast?_eq_some_getLast h_tl_ne)
  -- Extract closing condition from trace
  have h_close : ¬BoolMat.IndDisjoint (tl.getLast h_tl_ne).colSup hd.rowSup := by
    rw [BoolMat.trace_rankOne_iff h_r1p, h_rowp, h_colp, BoolMat.IndDisjoint_comm] at h_trace
    exact h_trace
  -- Consecutive pairs from chainConnected
  have h_consec := consecutive_of_chainConnected (hd :: tl) h_chain
  -- Build fullyChannelAligned
  intro ⟨i, hi⟩
  cases i with
  | zero => exact channelAlignedAt_zero_of_closing hd tl h_tl_ne h_close
  | succ j => exact channelAlignedAt_of_consecutive (hd :: tl) h_consec j hi

/-- **CHANNEL ALIGNMENT THEOREM** (Verified computationally: 544,736 / 544,736 cycles)

    For a cycle [M₁, M₂, ..., Mₖ] of rank-1 boolean matrices:
      trace(M₁ ⊗ M₂ ⊗ ... ⊗ Mₖ) > 0
    iff at every position i: colSup(M_{i-1}) ∩ rowSup(M_i) ≠ ∅. -/
theorem channel_alignment (cyc : RankOneCycle n) :
    BoolMat.trace (cyc.operators.foldl BoolMat.mul BoolMat.one) = true ↔
    fullyChannelAligned cyc.operators :=
  ⟨channel_alignment_forward cyc.operators cyc.length_ge cyc.all_rank_one,
   channel_alignment_backward cyc.operators cyc.length_ge cyc.all_rank_one⟩

/-- In UNSAT rank-1 cycles, there exists at least one "blocked" cube. -/
theorem unsat_rank1_cycle_has_blocked_cube (cyc : RankOneCycle n)
    (h_unsat : BoolMat.trace (cyc.operators.foldl BoolMat.mul BoolMat.one) = false) :
    ∃ i : Fin cyc.operators.length,
      ¬ channelAlignedAt cyc.operators i := by
  -- Contrapositive of channel_alignment
  apply Classical.byContradiction
  intro h
  have h_all : fullyChannelAligned cyc.operators := fun i =>
    Classical.byContradiction fun h_neg => h ⟨i, h_neg⟩
  have h_true := (channel_alignment cyc).mpr h_all
  rw [h_unsat] at h_true
  exact Bool.false_ne_true h_true

/-! ## Empirical observation (NOT YET A THEOREM):
    At k=3, every UNSAT rank-1 cycle has EXACTLY 1 blocked cube.
    Distribution: uniform across positions (33.3% each).
    This suggests the blocking condition is "generic" (not position-dependent). -/

end CubeGraph
