/-
  CubeGraph/MonodromyCycleOp.lean
  Connection between monodromy (left-fold via cycleChainFrom)
  and cycleOp (right-fold via chainOperator).

  MAIN RESULTS:
    chainOperator_snoc: chainOperator(xs ++ [c]) = chainOperator(xs) * T(last, c)
    cycleChainFrom_zero_eq_chainOperator: cycleChainFrom at start=0 = chainOperator of take
    monodromy_zero_eq_cycleOp: monodromy at position 0 = cycleOp
    trace_mul_comm: trace(AB) = trace(BA)
    trace_monodromy_independent: trace(M_i) = trace(M_j) for any positions i, j

  See: Monodromy.lean (left-fold: cycleChainFrom, monodromy)
  See: Theorems.lean (right-fold: chainOperator, cycleOp)
  See: theory/research/CECH-COHOMOLOGY-SAT.md (holonomy = monodromy connection)
  See: experiments-ml/007_2026-03-04_topology-of-hardness/PLAN-E-MONODROMYCYCLEOP.md (plan)
  See: paper/HOUSEKEEPING.md §5 (Cycle Analysis — paper placement)
  See: logs/STATUS-LOG-2026-03-04.md (Snapshot 005 — this file)
-/

import CubeGraph.Monodromy

namespace CubeGraph

/-! ## Section 1: chainOperator_snoc — appending to a chain -/

/-- Appending one cube to a chain extends the composed operator.
    chainOperator(xs ++ [c]) = chainOperator(xs) * T(last(xs), c) -/
theorem chainOperator_snoc (cubes : List Cube) (c : Cube) (h : cubes ≠ []) :
    chainOperator (cubes ++ [c]) =
      BoolMat.mul (chainOperator cubes) (transferOp (cubes.getLast h) c) := by
  induction cubes with
  | nil => exact absurd rfl h
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [List.singleton_append, chainOperator, List.getLast_singleton]
      rw [BoolMat.mul_one, BoolMat.one_mul]
    | cons b rest' =>
      show chainOperator (a :: b :: (rest' ++ [c])) =
        BoolMat.mul (chainOperator (a :: b :: rest'))
          (transferOp ((a :: b :: rest').getLast h) c)
      simp only [chainOperator]
      simp only [List.getLast_cons (List.cons_ne_nil _ _)]
      show BoolMat.mul (transferOp a b) (chainOperator ((b :: rest') ++ [c])) =
        BoolMat.mul (BoolMat.mul (transferOp a b) (chainOperator (b :: rest')))
          (transferOp ((b :: rest').getLast (List.cons_ne_nil b rest')) c)
      rw [ih (List.cons_ne_nil b rest')]
      exact (BoolMat.mul_assoc _ _ _).symm

/-! ## Section 2: cycleChainFrom at start=0 = chainOperator of take -/

/-- One step of cycleChainFrom at start=0 with simplified indices. -/
private theorem cycleChainFrom_zero_step (cycle : List Cube) (h_pos : cycle.length > 0)
    (n : Nat) (h_n_lt : n < cycle.length) (h_n1_lt : n + 1 < cycle.length) :
    cycleChainFrom cycle h_pos ⟨0, h_pos⟩ (n + 1) =
      BoolMat.mul (cycleChainFrom cycle h_pos ⟨0, h_pos⟩ n)
        (transferOp cycle[n] cycle[n + 1]) := by
  simp only [cycleChainFrom, nextIdx, Nat.zero_add,
             Nat.mod_eq_of_lt h_n_lt, Nat.mod_eq_of_lt h_n1_lt, Fin.getElem_fin]

/-- One step of cycleChainFrom at start=0 for the CLOSING edge (wrapping around). -/
private theorem cycleChainFrom_zero_close (cycle : List Cube) (h_pos : cycle.length > 0)
    (h_len2 : cycle.length ≥ 2) :
    cycleChainFrom cycle h_pos ⟨0, h_pos⟩ cycle.length =
      BoolMat.mul (cycleChainFrom cycle h_pos ⟨0, h_pos⟩ (cycle.length - 1))
        (transferOp cycle[cycle.length - 1] cycle[0]) := by
  rw [show cycleChainFrom cycle h_pos ⟨0, h_pos⟩ cycle.length =
    cycleChainFrom cycle h_pos ⟨0, h_pos⟩ ((cycle.length - 1) + 1) from
    congrArg (cycleChainFrom cycle h_pos ⟨0, h_pos⟩) (by omega)]
  have h_wrap : (cycle.length - 1 + 1) % cycle.length = 0 := by
    rw [show cycle.length - 1 + 1 = cycle.length from by omega]; exact Nat.mod_self _
  simp only [cycleChainFrom, nextIdx, Nat.zero_add,
             Nat.mod_eq_of_lt (show cycle.length - 1 < cycle.length from by omega),
             h_wrap, Fin.getElem_fin]

/-- cycleChainFrom at start position 0 equals chainOperator of the corresponding prefix. -/
theorem cycleChainFrom_zero_eq_chainOperator
    (cycle : List Cube) (h_pos : cycle.length > 0) (n : Nat)
    (h_le : n + 1 ≤ cycle.length) :
    cycleChainFrom cycle h_pos ⟨0, h_pos⟩ n =
      chainOperator (cycle.take (n + 1)) := by
  induction n with
  | zero =>
    simp only [cycleChainFrom]
    match cycle, h_pos with
    | a :: _, _ =>
      simp only [List.take_succ_cons, List.take_zero, chainOperator]
  | succ n ih =>
    have h_n_lt : n < cycle.length := by omega
    have h_n1_lt : n + 1 < cycle.length := by omega
    rw [cycleChainFrom_zero_step cycle h_pos n h_n_lt h_n1_lt]
    rw [ih (by omega)]
    -- Goal: chainOperator(take(n+1)) * T(cycle[n], cycle[n+1]) = chainOperator(take(n+2))
    rw [show n + 1 + 1 = (n + 1) + 1 from by omega]
    rw [List.take_succ_eq_append_getElem h_n1_lt]
    rw [chainOperator_snoc _ _ (by
      intro h_empty; cases cycle with
      | nil => simp at h_pos
      | cons a _ => simp at h_empty)]
    -- getLast(take(n+1)) = cycle[n]
    congr 1
    simp [List.getLast_eq_getElem, List.length_take, List.getElem_take,
          Nat.min_eq_left (by omega : n + 1 ≤ cycle.length)]

/-! ## Section 3: monodromy at position 0 = cycleOp -/

/-- **Monodromy at position 0 equals cycleOp**. -/
theorem monodromy_zero_eq_cycleOp (cycle : List Cube) (h_len : cycle.length ≥ 2) :
    monodromy cycle h_len ⟨0, by omega⟩ = cycleOp cycle h_len := by
  match cycle, h_len with
  | c₁ :: c₂ :: rest', h =>
    simp only [monodromy]
    -- cycleChainFrom ... k = cycleChainFrom ... (k-1) * T(cycle[k-1], cycle[0])
    rw [cycleChainFrom_zero_close _ _ h]
    -- cycleChainFrom ... (k-1) = chainOperator cycle
    rw [cycleChainFrom_zero_eq_chainOperator _ _ _ (by omega)]
    rw [show (c₁ :: c₂ :: rest').length - 1 + 1 = (c₁ :: c₂ :: rest').length from by omega]
    rw [List.take_length]
    -- Unfold cycleOp
    have hne : (c₂ :: rest') ≠ [] := List.cons_ne_nil _ _
    simp only [cycleOp, List.getLast?_eq_some_getLast hne]
    -- Both sides: chainOperator(cycle) * T(getLast, c₁)
    congr 1
    simp only [List.getLast_eq_getElem, List.length_cons]
    rfl

/-! ## Section 4: trace(AB) = trace(BA) -/

/-- **Trace commutativity for boolean matrices**. -/
theorem trace_mul_comm {n : Nat} (A B : BoolMat n) :
    BoolMat.trace (BoolMat.mul A B) = BoolMat.trace (BoolMat.mul B A) := by
  apply Bool.eq_iff_iff.mpr
  simp only [BoolMat.trace_true, BoolMat.mul_apply_true]
  constructor
  · rintro ⟨i, k, h1, h2⟩; exact ⟨k, i, h2, h1⟩
  · rintro ⟨k, i, h1, h2⟩; exact ⟨i, k, h2, h1⟩

/-! ## Section 5: Trace is position-independent -/

/-- **Trace of monodromy is independent of the starting position**. -/
theorem trace_monodromy_independent (cycle : List Cube) (h_len : cycle.length ≥ 2)
    (i j : Fin cycle.length) :
    BoolMat.trace (monodromy cycle h_len i) =
    BoolMat.trace (monodromy cycle h_len j) := by
  apply Bool.eq_iff_iff.mpr
  simp only [BoolMat.trace_true]
  constructor
  · intro ⟨g, hg⟩
    obtain ⟨gaps, _, hvalid, hcompat⟩ :=
      (monodromy_diag_iff_feasible cycle h_len i g).mp hg
    exact ⟨gaps j, (monodromy_diag_iff_feasible cycle h_len j (gaps j)).mpr
      ⟨gaps, rfl, hvalid, hcompat⟩⟩
  · intro ⟨g, hg⟩
    obtain ⟨gaps, _, hvalid, hcompat⟩ :=
      (monodromy_diag_iff_feasible cycle h_len j g).mp hg
    exact ⟨gaps i, (monodromy_diag_iff_feasible cycle h_len i (gaps i)).mpr
      ⟨gaps, rfl, hvalid, hcompat⟩⟩

/-- Corollary: trace of monodromy at any position equals trace of cycleOp. -/
theorem trace_monodromy_eq_trace_cycleOp (cycle : List Cube) (h_len : cycle.length ≥ 2)
    (i : Fin cycle.length) :
    BoolMat.trace (monodromy cycle h_len i) =
    BoolMat.trace (cycleOp cycle h_len) := by
  rw [trace_monodromy_independent cycle h_len i ⟨0, by omega⟩]
  rw [monodromy_zero_eq_cycleOp]

end CubeGraph
