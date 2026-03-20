/-
  CubeGraph/Monodromy.lean
  Monodromy operator at an arbitrary cycle position.

  The monodromy operator M_i is the composition of all transfer operators
  around a cycle, starting and ending at position i:
    M_i = T(c_i, c_{i+1}) * T(c_{i+1}, c_{i+2}) * ... * T(c_{i-1}, c_i)

  The diagonal M_i[g,g] = true iff gap g can "survive" a full traversal
  of the cycle from position i. This connects the semantic notion of
  cycle-feasible gaps (CycleIntersection.lean) with the algebraic notion
  of boolean matrix trace.

  MAIN RESULTS:
    feasible_implies_monodromy: CycleFeasibleAt → M_i[g,g] = true
    monodromy_implies_feasible: M_i[g,g] = true → CycleFeasibleAt
    monodromy_diag_iff_feasible: M_i[g,g] = true ↔ CycleFeasibleAt
    sat_monodromy_fixed: SAT → ∃ g, M_i[g,g] = true
    sat_monodromy_trace: SAT → trace(M_i) = true

  See: CycleIntersection.lean (semantic version: sat_implies_feasible_nonempty)
  See: theory/research/TRUE-EMERGENCE.md (true emergence framework)
  See: theory/research/GAP-SHEAF-FORMALIZATION.md (gap sheaf = monodromy context)
  See: theory/research/PROOF-CHAIN.md (complete Lean proof chain narrative)
  See: paper/HOUSEKEEPING.md §5 (cycle analysis in the paper)
  See: experiments-ml/007_2026-03-04_topology-of-hardness/ (computational validation)
  See: CubeGraph/Holonomy.lean (holonomy monoid + common fixed point theorem)
-/

import CubeGraph.CycleIntersection

namespace CubeGraph

/-! ## Section 1: Definitions -/

/-- Compose `n` transfer operators starting from position `start` in a cycle.
    After n steps: T(c_start, c_{start+1}) * ... * T(c_{start+n-1}, c_{start+n})
    where indices wrap around mod cycle.length. -/
def cycleChainFrom (cycle : List Cube) (h_pos : cycle.length > 0)
    (start : Fin cycle.length) : Nat → BoolMat 8
  | 0 => BoolMat.one
  | n + 1 =>
    let j : Fin cycle.length := ⟨(start.val + n) % cycle.length, Nat.mod_lt _ h_pos⟩
    BoolMat.mul (cycleChainFrom cycle h_pos start n)
               (transferOp cycle[j] cycle[nextIdx cycle.length h_pos j])

/-- The monodromy operator at position `i`: compose all k transfer operators
    around the cycle, starting and ending at position i.
    M_i = T(c_i, c_{i+1}) * T(c_{i+1}, c_{i+2}) * ... * T(c_{i-1}, c_i) -/
def monodromy (cycle : List Cube) (h_len : cycle.length ≥ 2)
    (i : Fin cycle.length) : BoolMat 8 :=
  cycleChainFrom cycle (by omega) i cycle.length

/-! ## Section 2: Modular arithmetic helpers -/

private theorem mod_succ (a n : Nat) (h : n > 0) :
    (a % n + 1) % n = (a + 1) % n := by
  have h1 := Nat.add_mod a 1 n
  have h2 := Nat.add_mod (a % n) 1 n
  rw [Nat.mod_eq_of_lt (Nat.mod_lt a h)] at h2
  exact h2.trans h1.symm

private theorem mod_add_self (a n : Nat) (h : n > 0) :
    (a + n) % n = a % n := by
  rw [Nat.add_mod, Nat.mod_self, Nat.add_zero]
  exact Nat.mod_eq_of_lt (Nat.mod_lt a h)

/-! ## Section 3: Chain semantics (backward direction) -/

/-- If all cycle edges are compatible via `gaps`, then the chain from position `start`
    maps gaps[start] to gaps[start + n] (mod cycle.length).

    This is the key algebraic lemma: a compatible gap assignment "threads through"
    the composed transfer operators. -/
theorem cycleChainFrom_apply (cycle : List Cube) (h_pos : cycle.length > 0)
    (start : Fin cycle.length) (n : Nat)
    (gaps : Fin cycle.length → Vertex)
    (h_compat : ∀ j : Fin cycle.length,
      transferOp cycle[j] cycle[nextIdx cycle.length h_pos j]
                 (gaps j) (gaps (nextIdx cycle.length h_pos j)) = true) :
    cycleChainFrom cycle h_pos start n
      (gaps start)
      (gaps ⟨(start.val + n) % cycle.length, Nat.mod_lt _ h_pos⟩) = true := by
  induction n with
  | zero =>
    simp only [cycleChainFrom, Nat.add_zero]
    rw [BoolMat.one_apply_true]
    congr 1; exact Fin.ext (Nat.mod_eq_of_lt start.isLt).symm
  | succ n ih =>
    simp only [cycleChainFrom]
    rw [BoolMat.mul_apply_true]
    refine ⟨gaps ⟨(start.val + n) % cycle.length, Nat.mod_lt _ h_pos⟩, ih, ?_⟩
    -- Show: nextIdx of position (start+n)%k equals position (start+n+1)%k
    have h_next : (⟨(start.val + (n + 1)) % cycle.length,
                    Nat.mod_lt _ h_pos⟩ : Fin cycle.length) =
                  nextIdx cycle.length h_pos
                    ⟨(start.val + n) % cycle.length, Nat.mod_lt _ h_pos⟩ := by
      apply Fin.ext; simp only [nextIdx, Fin.val_mk]
      rw [show start.val + (n + 1) = start.val + n + 1 from by omega]
      exact (mod_succ (start.val + n) cycle.length h_pos).symm
    rw [h_next]
    exact h_compat ⟨(start.val + n) % cycle.length, Nat.mod_lt _ h_pos⟩

/-- Full cycle: maps gaps[start] back to gaps[start]. -/
theorem cycleChainFrom_full_cycle (cycle : List Cube) (h_pos : cycle.length > 0)
    (start : Fin cycle.length)
    (gaps : Fin cycle.length → Vertex)
    (h_compat : ∀ j : Fin cycle.length,
      transferOp cycle[j] cycle[nextIdx cycle.length h_pos j]
                 (gaps j) (gaps (nextIdx cycle.length h_pos j)) = true) :
    cycleChainFrom cycle h_pos start cycle.length (gaps start) (gaps start) = true := by
  have h := cycleChainFrom_apply cycle h_pos start cycle.length gaps h_compat
  have h_wrap : (⟨(start.val + cycle.length) % cycle.length,
                  Nat.mod_lt _ h_pos⟩ : Fin cycle.length) = start := by
    have h_eq : (start.val + cycle.length) % cycle.length = start.val := by
      rw [mod_add_self _ _ h_pos]; exact Nat.mod_eq_of_lt start.isLt
    exact Fin.ext h_eq
  rwa [h_wrap] at h

/-! ## Section 4: CycleFeasibleAt → monodromy diagonal -/

/-- **CycleFeasibleAt implies monodromy diagonal entry**.
    If g is cycle-feasible at position i, then M_i[g,g] = true. -/
theorem feasible_implies_monodromy (cycle : List Cube) (h_len : cycle.length ≥ 2)
    (i : Fin cycle.length) (g : Vertex)
    (h : CycleFeasibleAt cycle h_len i g) :
    monodromy cycle h_len i g g = true := by
  obtain ⟨gaps, h_gi, _, h_compat⟩ := h
  subst h_gi
  exact cycleChainFrom_full_cycle cycle (by omega) i gaps h_compat

/-! ## Section 5: Main results -/

/-- **SAT → monodromy has a fixed point at every cycle position**.
    If G is satisfiable, then for any cycle and any position i,
    there exists a gap g such that M_i[g,g] = true. -/
theorem sat_monodromy_fixed (G : CubeGraph) (h_sat : G.Satisfiable)
    (cycle : List Cube) (h_cyc : CycleInGraph G cycle)
    (i : Fin cycle.length) :
    ∃ g : Vertex, monodromy cycle h_cyc.length_ge i g g = true := by
  obtain ⟨g, hg⟩ := sat_implies_feasible_nonempty G h_sat cycle h_cyc i
  exact ⟨g, feasible_implies_monodromy cycle h_cyc.length_ge i g hg⟩

/-- **SAT → monodromy trace is nonzero at every cycle position**.
    trace(M_i) = true means some gap can traverse the entire cycle
    starting from position i and return to itself. -/
theorem sat_monodromy_trace (G : CubeGraph) (h_sat : G.Satisfiable)
    (cycle : List Cube) (h_cyc : CycleInGraph G cycle)
    (i : Fin cycle.length) :
    BoolMat.trace (monodromy cycle h_cyc.length_ge i) = true := by
  rw [BoolMat.trace_true]
  exact sat_monodromy_fixed G h_sat cycle h_cyc i

/-! ## Section 6: Forward direction — monodromy diagonal → CycleFeasibleAt -/

/-- Helper: extract isGap from transferOp. -/
private theorem transferOp_isGap_fst (c₁ c₂ : Cube) (g₁ g₂ : Vertex)
    (h : transferOp c₁ c₂ g₁ g₂ = true) : c₁.isGap g₁ = true := by
  simp only [transferOp, Bool.and_eq_true] at h; exact h.1.1

/-- Extract a gap path from a cycleChainFrom entry. -/
theorem cycleChainFrom_extract (cycle : List Cube) (h_pos : cycle.length > 0)
    (start : Fin cycle.length) :
    ∀ (n : Nat) (g_s g_e : Vertex),
    cycleChainFrom cycle h_pos start n g_s g_e = true →
    ∃ (path : Fin (n + 1) → Vertex),
      path ⟨0, by omega⟩ = g_s ∧
      path ⟨n, by omega⟩ = g_e ∧
      ∀ (s : Fin n),
        let pos : Fin cycle.length :=
          ⟨(start.val + s.val) % cycle.length, Nat.mod_lt _ h_pos⟩
        transferOp cycle[pos] cycle[nextIdx cycle.length h_pos pos]
          (path ⟨s.val, by omega⟩) (path ⟨s.val + 1, by omega⟩) = true := by
  intro n
  induction n with
  | zero =>
    intro g_s g_e h
    simp only [cycleChainFrom] at h
    rw [BoolMat.one_apply_true] at h
    exact ⟨fun _ => g_s, rfl, h, fun s => Fin.elim0 s⟩
  | succ n ih =>
    intro g_s g_e h
    simp only [cycleChainFrom] at h
    rw [BoolMat.mul_apply_true] at h
    obtain ⟨g_mid, h_chain, h_transfer⟩ := h
    obtain ⟨old_path, h_start, h_end, h_old_compat⟩ := ih g_s g_mid h_chain
    -- Extend path: keep old_path for indices ≤ n, add g_e at index n+1
    refine ⟨fun idx => if hle : idx.val ≤ n then old_path ⟨idx.val, by omega⟩ else g_e,
            ?_, ?_, ?_⟩
    · -- path 0 = g_s: 0 ≤ n is true, so dite reduces to old_path branch
      dsimp only
      rw [dif_pos (show (0 : Nat) ≤ n from Nat.zero_le n)]
      exact h_start
    · -- path (n+1) = g_e: ¬(n+1 ≤ n), so dite reduces to g_e
      dsimp only
      rw [dif_neg (show ¬(n + 1 ≤ n) from by omega)]
    · -- compatibility at each step
      intro s
      simp only []
      by_cases hs : s.val < n
      · -- Old step: both s.val and s.val+1 are ≤ n
        rw [dif_pos (show s.val ≤ n from by omega),
            dif_pos (show s.val + 1 ≤ n from by omega)]
        exact h_old_compat ⟨s.val, hs⟩
      · -- New step (s.val = n): path[n] from old_path, path[n+1] = g_e
        have hs_eq : s.val = n := by omega
        rw [dif_pos (show s.val ≤ n from by omega),
            dif_neg (show ¬(s.val + 1 ≤ n) from by omega)]
        simp only [hs_eq]; rw [h_end]; exact h_transfer

/-- Round-trip: (i + (j + k - i) % k) % k = j, for i, j < k. -/
private theorem round_trip (i j k : Nat) (hi : i < k) (hj : j < k) (hk : k > 0) :
    (i + (j + k - i) % k) % k = j := by
  by_cases hij : j ≥ i
  · have h1 : j + k - i = j - i + k := by omega
    rw [h1, mod_add_self _ _ hk, Nat.mod_eq_of_lt (show j - i < k by omega)]
    have : i + (j - i) = j := by omega
    rw [this]; exact Nat.mod_eq_of_lt hj
  · rw [Nat.mod_eq_of_lt (show j + k - i < k by omega)]
    have : i + (j + k - i) = j + k := by omega
    rw [this, mod_add_self _ _ hk]; exact Nat.mod_eq_of_lt hj

/-- Step-successor: when step(j) + 1 < k, the next index maps correctly. -/
private theorem step_next (i j k : Nat) (hi : i < k) (hj : j < k) (hk : k > 0)
    (h_lt : (j + k - i) % k + 1 < k) :
    ((j + 1) % k + k - i) % k = (j + k - i) % k + 1 := by
  by_cases hij : j ≥ i
  · have hs : (j + k - i) % k = j - i := by
      rw [show j + k - i = j - i + k from by omega, mod_add_self _ _ hk]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hs] at h_lt ⊢
    by_cases hj1 : j + 1 < k
    · rw [Nat.mod_eq_of_lt hj1,
          show j + 1 + k - i = j - i + 1 + k from by omega, mod_add_self _ _ hk]
      exact Nat.mod_eq_of_lt h_lt
    · have : j + 1 = k := by omega
      rw [this, Nat.mod_self, show 0 + k - i = k - i from by omega,
          Nat.mod_eq_of_lt (show k - i < k by omega)]
      omega
  · have hs : (j + k - i) % k = j + k - i := Nat.mod_eq_of_lt (by omega)
    rw [hs] at h_lt ⊢
    rw [Nat.mod_eq_of_lt (show j + 1 < k by omega),
        Nat.mod_eq_of_lt (show j + 1 + k - i < k by omega)]
    omega

/-- **Monodromy diagonal entry implies CycleFeasibleAt**.
    If M_i[g,g] = true, then g is cycle-feasible at position i. -/
theorem monodromy_implies_feasible (cycle : List Cube) (h_len : cycle.length ≥ 2)
    (i : Fin cycle.length) (g : Vertex)
    (h : monodromy cycle h_len i g g = true) :
    CycleFeasibleAt cycle h_len i g := by
  -- Extract gap path from monodromy
  have hlen : cycle.length > 0 := by omega
  obtain ⟨path, h_start, h_end, h_path_compat⟩ :=
    cycleChainFrom_extract cycle (by omega) i cycle.length g g h
  -- Define gaps by reindexing: gaps[j] = path[step that visits position j]
  -- Step for position j: (j + cycle.length - i) % cycle.length
  refine ⟨fun j => path ⟨(j.val + cycle.length - i.val) % cycle.length,
    Nat.lt_succ_of_lt (Nat.mod_lt _ hlen)⟩, ?gi, ?valid, ?compat⟩
  case gi =>
    -- gaps i = path[(i + len - i) % len] = path[0] = g
    have h0 : (i.val + cycle.length - i.val) % cycle.length = 0 := by
      rw [show i.val + cycle.length - i.val = cycle.length from by omega]
      exact Nat.mod_self cycle.length
    show path ⟨(i.val + cycle.length - i.val) % cycle.length, _⟩ = g
    simp only [h0]; exact h_start
  case valid =>
    intro j
    -- The step for j is s = (j + len - i) % len
    -- h_path_compat at step s: transferOp at position (i+s)%len
    -- By round_trip: (i+s)%len = j
    have hs_lt : (j.val + cycle.length - i.val) % cycle.length < cycle.length :=
      Nat.mod_lt _ hlen
    have h_step := h_path_compat ⟨(j.val + cycle.length - i.val) % cycle.length, hs_lt⟩
    simp only [] at h_step
    -- The cube position in h_step is (i + s) % len = j
    have h_rt := round_trip i.val j.val cycle.length i.isLt j.isLt hlen
    have h_cube_eq : (⟨(i.val + (j.val + cycle.length - i.val) % cycle.length) % cycle.length,
        Nat.mod_lt _ hlen⟩ : Fin cycle.length) = j := Fin.ext h_rt
    simp only [h_cube_eq] at h_step
    exact transferOp_isGap_fst _ _ _ _ h_step
  case compat =>
    intro j
    have hs_lt : (j.val + cycle.length - i.val) % cycle.length < cycle.length :=
      Nat.mod_lt _ hlen
    have h_step := h_path_compat ⟨(j.val + cycle.length - i.val) % cycle.length, hs_lt⟩
    simp only [] at h_step
    have h_rt := round_trip i.val j.val cycle.length i.isLt j.isLt hlen
    have h_cube_eq : (⟨(i.val + (j.val + cycle.length - i.val) % cycle.length) % cycle.length,
        Nat.mod_lt _ hlen⟩ : Fin cycle.length) = j := Fin.ext h_rt
    simp only [h_cube_eq] at h_step
    -- h_step: transferOp cycle[j] cycle[nextIdx j] (path ⟨s,_⟩) (path ⟨s+1,_⟩) = true
    -- where s = (j + len - i) % len
    -- Goal: transferOp cycle[j] cycle[nextIdx j] (gaps j) (gaps (nextIdx j)) = true
    -- gaps j = path ⟨s,_⟩ (definitional) ✓
    -- Need: gaps (nextIdx j) matches path ⟨s+1,_⟩
    by_cases hs1 : (j.val + cycle.length - i.val) % cycle.length + 1 < cycle.length
    · -- s + 1 < len: step_next gives matching index
      have h_sn := step_next i.val j.val cycle.length i.isLt j.isLt hlen hs1
      -- gaps (nextIdx j) = path ⟨((nextIdx j).val + len - i) % len, _⟩
      -- = path ⟨s + 1, _⟩ by h_sn
      suffices h_eq : path ⟨((nextIdx cycle.length hlen j).val + cycle.length - i.val) %
          cycle.length, _⟩ = path ⟨(j.val + cycle.length - i.val) % cycle.length + 1, _⟩ by
        dsimp only; rw [h_eq]; exact h_step
      congr 1; apply Fin.ext; simp only [nextIdx]; exact h_sn
    · -- s + 1 = len: the cycle closes
      have hs_eq : (j.val + cycle.length - i.val) % cycle.length + 1 = cycle.length := by omega
      -- path ⟨s+1, _⟩ = path ⟨len, _⟩ = g
      have h_pk : path ⟨(j.val + cycle.length - i.val) % cycle.length + 1, by omega⟩ = g := by
        have : (⟨(j.val + cycle.length - i.val) % cycle.length + 1,
            (by omega : _ + 1 < cycle.length + 1)⟩ : Fin (cycle.length + 1)) =
               ⟨cycle.length, by omega⟩ := Fin.ext hs_eq
        rw [this]; exact h_end
      -- gaps (nextIdx j) = path ⟨((nextIdx j) + len - i) % len, _⟩ = path ⟨0, _⟩ = g
      suffices h_gap0 : ((nextIdx cycle.length hlen j).val + cycle.length - i.val) %
          cycle.length = 0 by
        dsimp only
        have h4 : path ⟨((nextIdx cycle.length hlen j).val + cycle.length - i.val) %
            cycle.length, Nat.lt_succ_of_lt (Nat.mod_lt _ hlen)⟩ = g := by
          have : (⟨((nextIdx cycle.length hlen j).val + cycle.length - i.val) % cycle.length,
              Nat.lt_succ_of_lt (Nat.mod_lt _ hlen)⟩ : Fin (cycle.length + 1)) = ⟨0, by omega⟩ :=
            Fin.ext h_gap0
          rw [this]; exact h_start
        rw [h4, ← h_pk]; exact h_step
      simp only [nextIdx]
      by_cases hij : j.val ≥ i.val
      · have h_sv : (j.val + cycle.length - i.val) % cycle.length = j.val - i.val := by
          rw [show j.val + cycle.length - i.val = j.val - i.val + cycle.length from by omega,
              mod_add_self _ _ hlen]
          exact Nat.mod_eq_of_lt (by omega)
        have hj_eq : j.val = i.val + cycle.length - 1 := by omega
        rw [show (j.val + 1) % cycle.length = i.val from by
          rw [hj_eq, show i.val + cycle.length - 1 + 1 = i.val + cycle.length from by omega,
              mod_add_self _ _ hlen]
          exact Nat.mod_eq_of_lt i.isLt]
        rw [show i.val + cycle.length - i.val = cycle.length from by omega]
        exact Nat.mod_self cycle.length
      · have h_sv : (j.val + cycle.length - i.val) % cycle.length = j.val + cycle.length - i.val :=
          Nat.mod_eq_of_lt (by omega)
        have hj_eq : j.val = i.val - 1 := by omega
        rw [show (j.val + 1) % cycle.length = i.val from by
          rw [hj_eq, show i.val - 1 + 1 = i.val from by omega]
          exact Nat.mod_eq_of_lt i.isLt]
        rw [show i.val + cycle.length - i.val = cycle.length from by omega]
        exact Nat.mod_self cycle.length

/-! ## Section 7: The iff -/

/-- **Monodromy diagonal ↔ CycleFeasibleAt**.
    M_i[g,g] = true if and only if g is cycle-feasible at position i. -/
theorem monodromy_diag_iff_feasible (cycle : List Cube) (h_len : cycle.length ≥ 2)
    (i : Fin cycle.length) (g : Vertex) :
    monodromy cycle h_len i g g = true ↔ CycleFeasibleAt cycle h_len i g :=
  ⟨monodromy_implies_feasible cycle h_len i g,
   feasible_implies_monodromy cycle h_len i g⟩

end CubeGraph
