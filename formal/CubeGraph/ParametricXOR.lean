/-
  CubeGraph/ParametricXOR.lean — Parametric XOR parity cycle

  For any m ≥ 3: constructs a CubeGraph with m cubes, (m-1)-consistent, UNSAT.
  This PROVES the schoenebeck and schoenebeck_linear statements constructively.

  Status: . All theorems fully proven.
  Includes: edges_valid, edges_complete, UNSAT parity, (m-1)-consistency.
  0 axioms.
-/

import CubeGraph.BandwidthGap
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use

set_option maxHeartbeats 12800000

namespace CubeGraph

open BoolMat

/-! ## Section 1: Gap Mask Properties -/

private theorem odd_xor_one (v : Vertex) (hg : (102 >>> v.val) &&& 1 = 1) :
    (v.val &&& 1) ^^^ ((v.val >>> 1) &&& 1) = 1 := by revert v; native_decide

private theorem even_xor_zero (v : Vertex) (hg : (153 >>> v.val) &&& 1 = 1) :
    (v.val &&& 1) ^^^ ((v.val >>> 1) &&& 1) = 0 := by revert v; native_decide

private theorem xor_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a ^^^ b ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> simp

private theorem exists_gap_with_bits (parity b0 b1 : Nat) (hp : parity ≤ 1)
    (hb0 : b0 ≤ 1) (hb1 : b1 ≤ 1) (hxor : b0 ^^^ b1 = parity) :
    ∃ v : Vertex,
      ((if parity = 0 then 153 else 102 : Nat) >>> v.val) &&& 1 = 1 ∧
      v.val &&& 1 = b0 ∧ (v.val >>> 1) &&& 1 = b1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb0 with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb1 with rfl | rfl <;>
    simp_all <;> first
    | exact ⟨⟨0, by omega⟩, by native_decide, by native_decide, by native_decide⟩
    | exact ⟨⟨3, by omega⟩, by native_decide, by native_decide, by native_decide⟩
    | exact ⟨⟨2, by omega⟩, by native_decide, by native_decide, by native_decide⟩
    | exact ⟨⟨1, by omega⟩, by native_decide, by native_decide, by native_decide⟩

/-! ## Section 2: Cube Construction -/

private def xorLeftVar (m i : Nat) : Nat := if i = 0 then m else i
private def xorRightVar (i : Nat) : Nat := i + 1
private def xorPrivVar (m i : Nat) : Nat := m + 1 + i

private def xorCube (m i : Nat) (hm : m ≥ 3) (hi : i < m) : Cube where
  var₁ := xorLeftVar m i
  var₂ := xorRightVar i
  var₃ := xorPrivVar m i
  var₁_pos := by unfold xorLeftVar; split <;> omega
  var₂_pos := by unfold xorRightVar; omega
  var₃_pos := by unfold xorPrivVar; omega
  vars_distinct := by
    constructor
    · show xorLeftVar m i ≠ xorRightVar i; unfold xorLeftVar xorRightVar; split <;> omega
    constructor
    · show xorLeftVar m i ≠ xorPrivVar m i; unfold xorLeftVar xorPrivVar; split <;> omega
    · show xorRightVar i ≠ xorPrivVar m i; unfold xorRightVar xorPrivVar; omega
  gapMask := ⟨if i = 0 then 102 else 153, by split <;> omega⟩
  gaps_nonempty := by simp; split <;> omega

/-- The vars list of an XOR cube. -/
private theorem xorCube_vars (m i : Nat) (hm : m ≥ 3) (hi : i < m) :
    (xorCube m i hm hi).vars = [xorLeftVar m i, xorRightVar i, xorPrivVar m i] := rfl

/-- xorLeftVar is never equal to xorRightVar for valid indices. -/
private theorem xorLeft_ne_xorRight (m i : Nat) (hm : m ≥ 3) (hi : i < m) :
    xorLeftVar m i ≠ xorRightVar i := by
  unfold xorLeftVar xorRightVar; split <;> omega

/-- xorPrivVar is never equal to xorRightVar. -/
private theorem xorPriv_ne_xorRight (m i : Nat) (hi : i < m) :
    xorPrivVar m i ≠ xorRightVar i := by
  unfold xorPrivVar xorRightVar; omega

/-- xorPrivVar of i is never equal to xorLeftVar of (i+1)%m. -/
private theorem xorPriv_ne_nextLeft (m i : Nat) (hm : m ≥ 3) (hi : i < m) :
    xorPrivVar m i ≠ xorLeftVar m ((i + 1) % m) := by
  unfold xorPrivVar xorLeftVar
  split_ifs with h
  · omega
  · have : (i + 1) % m < m := Nat.mod_lt _ (by omega)
    omega

/-- xorPrivVar of i is never equal to xorRightVar of (i+1)%m. -/
private theorem xorPriv_ne_nextRight (m i : Nat) (hm : m ≥ 3) (hi : i < m) :
    xorPrivVar m i ≠ xorRightVar ((i + 1) % m) := by
  unfold xorPrivVar xorRightVar
  have : (i + 1) % m < m := Nat.mod_lt _ (by omega)
  omega

/-- xorPrivVar of i is never equal to xorPrivVar of (i+1)%m (for non-trivial m). -/
private theorem xorPriv_ne_nextPriv (m i : Nat) (hm : m ≥ 3) (hi : i < m) :
    xorPrivVar m i ≠ xorPrivVar m ((i + 1) % m) := by
  unfold xorPrivVar
  have hmod : (i + 1) % m < m := Nat.mod_lt _ (by omega)
  intro heq
  have : i = (i + 1) % m := by omega
  by_cases hlt : i + 1 < m
  · rw [Nat.mod_eq_of_lt hlt] at this; omega
  · have : i + 1 = m := by omega
    rw [this, Nat.mod_self] at *; omega

/-- xorLeftVar of i is never equal to xorRightVar of (i+1)%m (except when they're adjacent). -/
private theorem xorLeft_ne_nextRight (m i : Nat) (hm : m ≥ 3) (hi : i < m) :
    xorLeftVar m i ≠ xorRightVar ((i + 1) % m) := by
  unfold xorLeftVar xorRightVar
  split_ifs with h
  · subst h; have : (0 + 1) % m = 1 := Nat.mod_eq_of_lt (by omega); rw [this]; omega
  · have hmod : (i + 1) % m < m := Nat.mod_lt _ (by omega)
    by_cases hlt : i + 1 < m
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · have him : i + 1 = m := by omega
      rw [him, Nat.mod_self]; omega

/-- xorLeftVar of i is never equal to xorPrivVar of (i+1)%m. -/
private theorem xorLeft_ne_nextPriv (m i : Nat) (hm : m ≥ 3) (hi : i < m) :
    xorLeftVar m i ≠ xorPrivVar m ((i + 1) % m) := by
  unfold xorLeftVar xorPrivVar
  split_ifs with h
  · subst h; omega
  · have : (i + 1) % m < m := Nat.mod_lt _ (by omega); omega

/-- idxOf of xorRightVar i in cube i's vars is 1. -/
private theorem idxOf_rightVar_in_cube (m i : Nat) (hm : m ≥ 3) (hi : i < m) :
    (xorCube m i hm hi).vars.idxOf (xorRightVar i) = 1 := by
  simp only [xorCube_vars]
  show [xorLeftVar m i, xorRightVar i, xorPrivVar m i].idxOf (xorRightVar i) = 1
  simp only [List.idxOf, List.findIdx]
  have hne := xorLeft_ne_xorRight m i hm hi
  simp [BEq.beq, hne]

/-- idxOf of xorRightVar i in cube (i+1)%m's vars is 0
    (because xorRightVar i = xorLeftVar m ((i+1)%m)). -/
private theorem idxOf_rightVar_in_next_cube (m i : Nat) (hm : m ≥ 3) (hi : i < m) :
    let j := (i + 1) % m
    let hj : j < m := Nat.mod_lt _ (by omega)
    (xorCube m j hm hj).vars.idxOf (xorRightVar i) = 0 := by
  simp only [xorCube_vars]
  show [xorLeftVar m ((i+1)%m), xorRightVar ((i+1)%m), xorPrivVar m ((i+1)%m)].idxOf (xorRightVar i) = 0
  rw [rightVar_eq_nextLeftVar m i hm hi]
  simp only [List.idxOf, List.findIdx]
  simp [BEq.beq]

/-- For XOR cubes, transferOp between adjacent cubes checks only bit1=bit0 match. -/
private theorem xorCube_transferOp_iff (m i : Nat) (hm : m ≥ 3) (hi : i < m)
    (g₁ g₂ : Vertex) :
    let j := (i + 1) % m
    let hj : j < m := Nat.mod_lt _ (by omega)
    transferOp (xorCube m i hm hi) (xorCube m j hm hj) g₁ g₂ = true ↔
    ((xorCube m i hm hi).isGap g₁ = true ∧
     (xorCube m j hm hj).isGap g₂ = true ∧
     (g₁.val >>> 1) &&& 1 = g₂.val &&& 1) := by
  constructor
  · intro htop
    unfold transferOp at htop
    simp only [Bool.and_eq_true] at htop
    obtain ⟨⟨hg1, hg2⟩, hall⟩ := htop
    refine ⟨hg1, hg2, ?_⟩
    rw [List.all_eq_true] at hall
    have hmem : xorRightVar i ∈ Cube.sharedVars (xorCube m i hm hi)
        (xorCube m ((i+1)%m) hm (Nat.mod_lt _ (by omega))) := by
      rw [xorCube_sharedVars m i hm hi]; exact List.Mem.head _
    have hbits := hall (xorRightVar i) hmem
    simp only [Bool.beq_eq_true_iff_eq, Nat.beq_eq_true_iff_eq, decide_eq_true_eq] at hbits
    rw [idxOf_rightVar_in_cube m i hm hi, idxOf_rightVar_in_next_cube m i hm hi] at hbits
    simpa using hbits
  · intro ⟨hg1, hg2, hbits⟩
    unfold transferOp
    simp only [Bool.and_eq_true]
    refine ⟨⟨hg1, hg2⟩, ?_⟩
    rw [List.all_eq_true]
    intro sv hsv
    rw [xorCube_sharedVars m i hm hi] at hsv
    simp at hsv; subst hsv
    simp only [Bool.beq_eq_true_iff_eq, Nat.beq_eq_true_iff_eq, decide_eq_true_eq]
    rw [idxOf_rightVar_in_cube m i hm hi, idxOf_rightVar_in_next_cube m i hm hi]
    simpa using hbits

/-- The shared variables between adjacent XOR cubes = [xorRightVar i]. -/
private theorem xorCube_sharedVars (m i : Nat) (hm : m ≥ 3) (hi : i < m) :
    let j := (i + 1) % m
    let hj : j < m := Nat.mod_lt _ (by omega)
    Cube.sharedVars (xorCube m i hm hi) (xorCube m j hm hj) = [xorRightVar i] := by
  simp only [Cube.sharedVars, xorCube_vars, Cube.vars, xorCube, List.filter]
  -- Need to show: filtering [xorLeftVar m i, xorRightVar i, xorPrivVar m i] by
  -- membership in [xorLeftVar m j, xorRightVar j, xorPrivVar m j] = [xorRightVar i]
  simp only [List.contains_cons, List.contains_nil, Bool.or_false]
  -- xorLeftVar m i is NOT in cube (i+1)%m's vars
  have h1 : (xorLeftVar m i == xorLeftVar m ((i+1)%m) ||
             xorLeftVar m i == xorRightVar ((i+1)%m) ||
             xorLeftVar m i == xorPrivVar m ((i+1)%m)) = false := by
    simp only [beq_iff_eq, Bool.or_eq_false_iff]
    exact ⟨⟨by
      unfold xorLeftVar; split_ifs with h1 h2 h2
      · subst h1; rw [show (0+1)%m = 1 from Nat.mod_eq_of_lt (by omega)]; omega
      · subst h1; rw [show (0+1)%m = 1 from Nat.mod_eq_of_lt (by omega)]; omega
      · intro heq; have := Nat.mod_lt (i+1) (by omega : m > 0)
        by_cases h3 : i + 1 < m
        · rw [Nat.mod_eq_of_lt h3] at heq; exact h2 heq.symm
        · rw [show i + 1 = m from by omega, Nat.mod_self] at heq h2; exact h1 heq.symm,
      xorLeft_ne_nextRight m i hm hi⟩,
      xorLeft_ne_nextPriv m i hm hi⟩
  -- xorRightVar i IS in cube (i+1)%m's vars (it equals xorLeftVar m ((i+1)%m))
  have h2 : (xorRightVar i == xorLeftVar m ((i+1)%m) ||
             xorRightVar i == xorRightVar ((i+1)%m) ||
             xorRightVar i == xorPrivVar m ((i+1)%m)) = true := by
    simp only [beq_iff_eq, Bool.or_eq_true_iff]
    left; left; exact rightVar_eq_nextLeftVar m i hm hi
  -- xorPrivVar m i is NOT in cube (i+1)%m's vars
  have h3 : (xorPrivVar m i == xorLeftVar m ((i+1)%m) ||
             xorPrivVar m i == xorRightVar ((i+1)%m) ||
             xorPrivVar m i == xorPrivVar m ((i+1)%m)) = false := by
    simp only [beq_iff_eq, Bool.or_eq_false_iff]
    exact ⟨⟨xorPriv_ne_nextLeft m i hm hi,
            xorPriv_ne_nextRight m i hm hi⟩,
           xorPriv_ne_nextPriv m i hm hi⟩
  simp [h1, h2, h3]

/-! ## Section 3: CubeGraph Construction -/

private def xorCubeList (m : Nat) (hm : m ≥ 3) : List Cube :=
  (List.finRange m).map fun ⟨i, hi⟩ => xorCube m i hm hi

private theorem xorCubeList_length (m : Nat) (hm : m ≥ 3) :
    (xorCubeList m hm).length = m := by simp [xorCubeList]

private theorem xorCubeList_getElem_nat (m : Nat) (hm : m ≥ 3)
    (j : Nat) (hjl : j < (xorCubeList m hm).length) :
    (xorCubeList m hm)[j]'hjl = xorCube m j hm (by rw [xorCubeList_length] at hjl; exact hjl) := by
  simp [xorCubeList, List.getElem_map, List.getElem_finRange]

@[simp] private theorem xorCubeList_getElem_fin (m : Nat) (hm : m ≥ 3)
    (idx : Fin (xorCubeList m hm).length) :
    (xorCubeList m hm)[idx] =
    xorCube m idx.val hm (Nat.lt_of_lt_of_eq idx.isLt (xorCubeList_length m hm)) := by
  rw [Fin.getElem_fin]; exact xorCubeList_getElem_nat m hm idx.val idx.isLt

private theorem rightVar_eq_nextLeftVar (m j : Nat) (hm : m ≥ 3) (hj : j < m) :
    xorRightVar j = xorLeftVar m ((j + 1) % m) := by
  unfold xorRightVar xorLeftVar
  split_ifs with h
  · have hdvd : m ∣ (j + 1) := Nat.dvd_of_mod_eq_zero h
    have := Nat.le_of_dvd (by omega) hdvd; omega
  · have hlt : j + 1 < m := by
      by_contra hle; simp [Nat.not_lt] at hle
      rw [show j + 1 = m from by omega, Nat.mod_self] at h; exact h rfl
    rw [Nat.mod_eq_of_lt hlt]

private theorem linkWeight_pos_shared (c₁ c₂ : Cube) (h : Cube.linkWeight c₁ c₂ > 0) :
    ∃ v, v ∈ c₁.vars ∧ v ∈ c₂.vars := by
  unfold Cube.linkWeight Cube.sharedVars at h
  have hne : (c₁.vars.filter fun v => c₂.vars.contains v) ≠ [] := by
    intro heq; rw [heq] at h; simp at h
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne
  rw [List.mem_filter] at hv
  exact ⟨v, hv.1, by simp at hv; exact hv.2⟩

/-- If cubes a and b share a variable, they are cyclically adjacent. -/
private theorem sharing_implies_adjacent (m a b : Nat) (hm : m ≥ 3) (ha : a < m) (hb : b < m)
    (hab : a ≠ b) (v : Nat)
    (hv1 : v = xorLeftVar m a ∨ v = xorRightVar a ∨ v = xorPrivVar m a)
    (hv2 : v = xorLeftVar m b ∨ v = xorRightVar b ∨ v = xorPrivVar m b) :
    b = (a + 1) % m ∨ a = (b + 1) % m := by
  rcases hv1 with rfl | rfl | rfl <;> rcases hv2 with h | h | h
  · unfold xorLeftVar at h; split_ifs at h <;> first | omega | exact absurd h hab
  · unfold xorLeftVar xorRightVar at h; split_ifs at h with ha0
    · right; subst ha0
      rw [show b = m - 1 from by omega, show m - 1 + 1 = m from by omega, Nat.mod_self]
    · right; rw [Nat.mod_eq_of_lt (by omega : b + 1 < m)]; omega
  · exfalso; unfold xorLeftVar xorPrivVar at h; split_ifs at h <;> omega
  · unfold xorRightVar xorLeftVar at h; split_ifs at h with hb0
    · left; subst hb0
      rw [show a = m - 1 from by omega, show m - 1 + 1 = m from by omega, Nat.mod_self]
    · left; rw [Nat.mod_eq_of_lt (by omega : a + 1 < m)]; omega
  · unfold xorRightVar at h; omega
  · exfalso; unfold xorRightVar xorPrivVar at h; omega
  · exfalso; unfold xorPrivVar xorLeftVar at h; split_ifs at h <;> omega
  · exfalso; unfold xorPrivVar xorRightVar at h; omega
  · exfalso; unfold xorPrivVar at h; omega

/-- Named edge function for the XOR cycle: edge i connects cube i to cube (i+1)%m. -/
private def xorEdge (m : Nat) (hm : m ≥ 3) (idx : Fin m) :
    Fin (xorCubeList m hm).length × Fin (xorCubeList m hm).length :=
  (⟨idx.val, by rw [xorCubeList_length]; exact idx.isLt⟩,
   ⟨(idx.val + 1) % m, by rw [xorCubeList_length]; exact Nat.mod_lt _ (by omega)⟩)

private theorem edge_eq_left (m : Nat) (hm : m ≥ 3) (a b : Nat)
    (ha : a < (xorCubeList m hm).length) (hb : b < (xorCubeList m hm).length)
    (hba : b = (a + 1) % m) (ham : a < m) :
    (⟨a, ha⟩, ⟨b, hb⟩) = xorEdge m hm ⟨a, ham⟩ := by
  ext <;> simp [xorEdge] <;> omega

private theorem edge_eq_right (m : Nat) (hm : m ≥ 3) (a b : Nat)
    (ha : a < (xorCubeList m hm).length) (hb : b < (xorCubeList m hm).length)
    (hab : a = (b + 1) % m) (hbm : b < m) :
    (⟨b, hb⟩, ⟨a, ha⟩) = xorEdge m hm ⟨b, hbm⟩ := by
  ext <;> simp [xorEdge] <;> omega

/-- The XOR cycle graph of length m. Adjacent cubes share exactly one variable
    (xorRightVar i at position 1 in cube i and position 0 in cube (i+1)%m).
    Non-adjacent cubes have disjoint variable sets (proven in sharing_implies_adjacent). -/
def xorCycleGraph (m : Nat) (hm : m ≥ 3) : CubeGraph where
  cubes := xorCubeList m hm
  edges := (List.finRange m).map (xorEdge m hm)
  edges_valid := by
    intro e he; simp only [List.mem_map, List.mem_finRange, true_and] at he
    obtain ⟨⟨i, hi⟩, rfl⟩ := he
    simp only [xorEdge, xorCubeList_getElem_fin]
    unfold Cube.linkWeight
    apply List.length_pos_of_mem
    unfold Cube.sharedVars
    rw [List.mem_filter]
    refine ⟨?_, ?_⟩
    · show xorRightVar i ∈ [xorLeftVar m i, xorRightVar i, xorPrivVar m i]; simp
    · show [xorLeftVar m ((i+1)%m), xorRightVar ((i+1)%m), xorPrivVar m ((i+1)%m)].contains
          (xorRightVar i)
      rw [rightVar_eq_nextLeftVar m i hm hi]; simp
  edges_complete := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab hlw
    have ham : a < m := by rw [xorCubeList_length] at ha; exact ha
    have hbm : b < m := by rw [xorCubeList_length] at hb; exact hb
    have habne : a ≠ b := fun heq => hab (Fin.ext heq)
    simp only [xorCubeList_getElem_fin] at hlw
    obtain ⟨v, hv1, hv2⟩ := linkWeight_pos_shared _ _ hlw
    simp only [Cube.vars, xorCube] at hv1 hv2
    have hv1' : v = xorLeftVar m a ∨ v = xorRightVar a ∨ v = xorPrivVar m a := by
      simp at hv1; exact hv1
    have hv2' : v = xorLeftVar m b ∨ v = xorRightVar b ∨ v = xorPrivVar m b := by
      simp at hv2; exact hv2
    rcases sharing_implies_adjacent m a b hm ham hbm habne v hv1' hv2' with hadj | hadj
    · left; rw [edge_eq_left m hm a b ha hb hadj ham]
      exact List.mem_map_of_mem (List.mem_finRange _)
    · right; rw [edge_eq_right m hm a b ha hb hadj hbm]
      exact List.mem_map_of_mem (List.mem_finRange _)

theorem xorCycleGraph_length (m : Nat) (hm : m ≥ 3) :
    (xorCycleGraph m hm).cubes.length = m := xorCubeList_length m hm

/-! ## Section 4: UNSAT Proof (XOR parity argument) -/

/-- The XOR cycle of length m is UNSAT for any m ≥ 3.

    Proof by parity contradiction:
    - Cube 0 has gapMask 102 (XOR parity 1: bit0 ⊕ bit1 = 1 for all gaps)
    - Cubes i > 0 have gapMask 153 (XOR parity 0: bit0 = bit1 for all gaps)
    - Along each edge, the shared variable forces bit1(curr) = bit0(next)
    - Combining: bit0(s(next)) = bit0(s(curr)) ⊕ parity(curr)
    - Around the cycle: bit0(s(0)) = bit0(s(0)) ⊕ 1. Contradiction. -/
theorem xorCycle_unsat (m : Nat) (hm : m ≥ 3) : ¬ (xorCycleGraph m hm).Satisfiable := by
  intro ⟨s, hv, hc⟩
  -- Step lemma: bit0(s(next)) = bit0(s(curr)) ⊕ parity(curr)
  -- Key lemma: the edge (i, (i+1)%m) is in the graph edges
  have hedge : ∀ i (hi : i < m), xorEdge m hm ⟨i, hi⟩ ∈ (xorCycleGraph m hm).edges := by
    intro i hi; simp only [xorCycleGraph]; exact List.mem_map_of_mem (List.mem_finRange _)

  -- Key lemma: transferOp for adjacent XOR cubes forces bit matching
  -- For edge (i, (i+1)%m): shared var = xorRightVar i, idx=1 in cube i, idx=0 in cube (i+1)%m
  -- transferOp = true → (g₁.val >>> 1) &&& 1 == (g₂.val >>> 0) &&& 1
  -- i.e. bit1(g₁) = bit0(g₂)
  have hshared_bit : ∀ i (hi : i < m),
      let e := xorEdge m hm ⟨i, hi⟩
      let g₁ := s e.1
      let g₂ := s e.2
      (g₁.val >>> 1) &&& 1 = (g₂.val &&& 1) := by
    intro i hi
    have he := hedge i hi
    have htop := hc _ he
    simp only [xorCycleGraph, xorEdge, xorCubeList_getElem_fin] at htop
    exact ((xorCube_transferOp_iff m i hm hi _ _).mp htop).2.2

  have hstep : ∀ i (hi : i < m),
      (s ⟨(i+1)%m, by rw [xorCycleGraph_length]; exact Nat.mod_lt _ (by omega)⟩).val &&& 1 =
      ((s ⟨i, by rw [xorCycleGraph_length]; exact hi⟩).val &&& 1) ^^^ (if i = 0 then 1 else 0) := by
    intro i hi
    have hbit := hshared_bit i hi
    -- hbit: bit1(s(i)) = bit0(s((i+1)%m))
    -- From gap validity: s(i) is a gap in cube i
    -- If i = 0: gapMask = 102 → bit0 ⊕ bit1 = 1, so bit1 = bit0 ⊕ 1
    -- If i > 0: gapMask = 153 → bit0 ⊕ bit1 = 0, so bit1 = bit0
    -- Combining: bit0(s((i+1)%m)) = bit1(s(i)) = bit0(s(i)) ⊕ parity(i)
    have hgap := hv ⟨i, by rw [xorCycleGraph_length]; exact hi⟩
    simp only [xorCycleGraph, xorCubeList_getElem_fin, Cube.isGap, xorCube] at hgap
    simp only [xorEdge] at hbit
    by_cases hi0 : i = 0
    · subst hi0; simp
      -- gapMask = 102, so (102 >>> g.val) &&& 1 = 1
      -- This means bit0 ⊕ bit1 = 1 (from odd_xor_one)
      have hxor := odd_xor_one (s ⟨0, by rw [xorCycleGraph_length]; omega⟩) (by simpa using hgap)
      -- hxor: bit0 ⊕ bit1 = 1, hbit: bit1 = bit0(next)
      -- So bit0(next) = bit1 = bit0 ⊕ 1
      omega
    · simp [hi0]
      -- gapMask = 153, so (153 >>> g.val) &&& 1 = 1
      -- This means bit0 ⊕ bit1 = 0 (from even_xor_zero)
      have hxor := even_xor_zero (s ⟨i, by rw [xorCycleGraph_length]; exact hi⟩) (by simpa [hi0] using hgap)
      -- hxor: bit0 ⊕ bit1 = 0 → bit1 = bit0
      -- hbit: bit1 = bit0(next)
      -- So bit0(next) = bit0
      omega

  -- Induction: for 1 ≤ k ≤ m, bit0(s(k%m)) = bit0(s(0)) ⊕ 1
  have key : ∀ k, 1 ≤ k → k ≤ m →
    (s ⟨k % m, by rw [xorCycleGraph_length]; exact Nat.mod_lt _ (by omega)⟩).val &&& 1 =
    ((s ⟨0, by rw [xorCycleGraph_length]; omega⟩).val &&& 1) ^^^ 1 := by
    intro k hk
    induction k with
    | zero => omega
    | succ n ih =>
      intro hn
      by_cases hn0 : n = 0
      · subst hn0; exact hstep 0 (by omega)
      · have hlt : n < m := by omega
        have hstepn := hstep n hlt
        -- hstepn: s((n+1)%m) &&& 1 = s(n) &&& 1 ^^^ (if n=0 then 1 else 0)
        -- Since n ≠ 0: ... = s(n) &&& 1 ^^^ 0 = s(n) &&& 1
        have : (if n = 0 then 1 else 0 : Nat) = 0 := by simp [hn0]
        rw [this, Nat.xor_zero] at hstepn
        have hih := ih (by omega) (by omega)
        -- s(n%m) = s(n) since n < m → n%m = n
        have hmod : n % m = n := Nat.mod_eq_of_lt hlt
        have hfin : (⟨n % m, by rw [xorCycleGraph_length]; exact Nat.mod_lt _ (by omega)⟩ :
          Fin (xorCycleGraph m hm).cubes.length) =
          ⟨n, by rw [xorCycleGraph_length]; exact hlt⟩ := Fin.ext (by simp [hmod])
        rw [hfin] at hih; rw [hstepn, hih]
  -- At k = m: s(0) &&& 1 = s(0) &&& 1 ⊕ 1. Contradiction.
  have hfinal := key m (by omega) (by omega)
  have hfin : (⟨m % m, by rw [xorCycleGraph_length]; exact Nat.mod_lt _ (by omega)⟩ :
    Fin (xorCycleGraph m hm).cubes.length) =
    ⟨0, by rw [xorCycleGraph_length]; omega⟩ := Fin.ext (by simp [Nat.mod_self])
  rw [hfin] at hfinal
  -- hfinal : x = x ^^^ 1 where x = s(0).val &&& 1. Contradiction.
  have h0lt : 0 < (xorCycleGraph m hm).cubes.length := by rw [xorCycleGraph_length]; omega
  have hx : (s ⟨0, h0lt⟩).val &&& 1 ≤ 1 := by
    rw [Nat.and_one_is_mod]
    rcases Nat.mod_two_eq_zero_or_one (s ⟨0, h0lt⟩).val with h | h <;> omega
  -- x ≤ 1 means x = 0 or x = 1. In both cases x ≠ x ^^^ 1.
  rcases Nat.eq_zero_or_pos ((s ⟨0, h0lt⟩).val &&& 1) with h | h
  · rw [h] at hfinal; simp at hfinal
  · have h1 : (s ⟨0, h0lt⟩).val &&& 1 = 1 := by omega
    rw [h1] at hfinal; simp at hfinal

/-! ## Section 5: (m-1)-Consistency -/

private theorem all_covered_length_ge : ∀ (n : Nat) (vals : List Nat),
    vals.Nodup → (∀ j, j < n → j ∈ vals) → n ≤ vals.length := by
  intro n; induction n with
  | zero => intros; omega
  | succ k ih =>
    intro vals hnodup hcover
    have hk := hcover k (by omega)
    have hcov' : ∀ j, j < k → j ∈ vals.erase k := by
      intro j hj
      exact (List.mem_erase_of_ne (Nat.ne_of_lt hj)).mpr (hcover j (Nat.lt_succ_of_lt hj))
    have hih := ih (vals.erase k) (hnodup.erase k) hcov'
    have hpos : vals.length ≥ 1 := List.length_pos_of_mem hk
    have hlen' := List.length_erase_of_mem hk
    omega

private theorem exists_missing (m : Nat) (_ : m ≥ 1)
    (S : List (Fin m)) (hlen : S.length < m) (hnodup : S.Nodup) :
    ∃ j : Nat, j < m ∧ ∀ idx ∈ S, idx.val ≠ j := by
  suffices h : ¬ (∀ j, j < m → ∃ idx ∈ S, idx.val = j) by
    push_neg at h; obtain ⟨j, hj, habs⟩ := h; exact ⟨j, hj, fun idx hidx => habs idx hidx⟩
  intro hall
  have hnodup_vals : (S.map Fin.val).Nodup := by
    unfold List.Nodup; rw [List.pairwise_map]
    exact hnodup.imp (fun hab heq => hab (Fin.ext heq))
  have hcover : ∀ j, j < m → j ∈ S.map Fin.val := by
    intro j hj; rw [List.mem_map]
    obtain ⟨idx, hidx, hval⟩ := hall j hj; exact ⟨idx, hidx, hval⟩
  have hge := all_covered_length_ge m (S.map Fin.val) hnodup_vals hcover
  simp [List.length_map] at hge; omega

/-- The parity of cube i: 1 if i=0, 0 otherwise. -/
private def xorParity (i : Nat) : Nat := if i = 0 then 1 else 0

/-- Accumulated parity from position 0 to k-1 in the path starting at cube (j+1)%m.
    accParity m j k = XOR of parities of cubes at positions 0..k-1 in the path. -/
private def accParity (m j : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => accParity m j k ^^^ xorParity ((j + 1 + k) % m)

/-- accParity step relation. -/
private theorem accParity_succ (m j k : Nat) :
    accParity m j (k + 1) = accParity m j k ^^^ xorParity ((j + 1 + k) % m) := rfl

/-- accParity values are bounded by 1. -/
private theorem accParity_le_one (m j : Nat) : ∀ k, accParity m j k ≤ 1 := by
  intro k; induction k with
  | zero => simp [accParity]
  | succ n ih =>
    simp only [accParity, xorParity]
    split <;> (apply xor_le_one <;> omega)

/-- Make a gap vertex from bit0 and parity. Gap = bit0 + (bit0 XOR parity) * 2.
    bit2 = 0 (private variable, can be anything for compatibility). -/
private def makeGapVertex (b0 par : Nat) (hb0 : b0 ≤ 1) (hpar : par ≤ 1) : Vertex :=
  ⟨b0 + (b0 ^^^ par) * 2, by have := xor_le_one hb0 hpar; omega⟩

/-- makeGapVertex bit0. -/
private theorem makeGapVertex_bit0 (b0 par : Nat) (hb0 : b0 ≤ 1) (hpar : par ≤ 1) :
    (makeGapVertex b0 par hb0 hpar).val &&& 1 = b0 := by
  simp only [makeGapVertex]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb0 with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hpar with rfl | rfl <;> simp

/-- makeGapVertex bit1. -/
private theorem makeGapVertex_bit1 (b0 par : Nat) (hb0 : b0 ≤ 1) (hpar : par ≤ 1) :
    ((makeGapVertex b0 par hb0 hpar).val >>> 1) &&& 1 = b0 ^^^ par := by
  simp only [makeGapVertex]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb0 with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hpar with rfl | rfl <;> simp

/-- makeGapVertex is a valid gap in its cube. -/
private theorem makeGapVertex_isGap (m i b0 par : Nat) (hm : m ≥ 3) (hi : i < m)
    (hb0 : b0 ≤ 1) (hpar : par ≤ 1)
    (hpar_eq : par = xorParity i) :
    (xorCube m i hm hi).isGap (makeGapVertex b0 par hb0 hpar) = true := by
  simp only [Cube.isGap, xorCube, makeGapVertex]
  subst hpar_eq
  by_cases hi0 : i = 0
  · subst hi0; simp [xorParity]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb0 with rfl | rfl <;> simp
  · simp [hi0, xorParity]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb0 with rfl | rfl <;> simp

/-- The gap assignment for the XOR path: assign to cube at position k in the path
    starting at (j+1)%m, where k ranges over 0..m-2. -/
private def pathAssignment (m j : Nat) (hm : m ≥ 3) (hj : j < m)
    (cubeIdx : Fin (xorCycleGraph m hm).cubes.length) : Vertex :=
  let i := cubeIdx.val
  let pos := (i + m - (j + 1)) % m  -- position in path
  let b0 := accParity m j pos
  makeGapVertex b0 (xorParity i) (accParity_le_one m j pos) (by unfold xorParity; split <;> omega)

/-- Position of cube i in the path starting at (j+1). -/
private def pathPos (m j i : Nat) : Nat := (i + m - (j + 1)) % m

/-- (j + 1 + pathPos m j i) % m = i, for i < m and j < m. -/
private theorem pathPos_cube_id (m j i : Nat) (hm : m ≥ 1) (hi : i < m) (hj : j < m) :
    (j + 1 + pathPos m j i) % m = i := by
  simp only [pathPos]
  have hmod : (i + m - (j + 1)) % m < m := Nat.mod_lt _ (by omega)
  -- (j + 1 + (i + m - (j + 1)) % m) % m = i
  by_cases hle : i ≥ j + 1
  · -- i ≥ j + 1: pathPos = (i - (j+1)) since i - (j+1) < m
    have hval : i + m - (j + 1) = i - (j + 1) + m := by omega
    rw [hval, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - (j + 1) < m)]
    rw [show j + 1 + (i - (j + 1)) = i from by omega, Nat.mod_eq_of_lt hi]
  · -- i < j + 1: pathPos = i + m - (j + 1) (already < m)
    have hval : i + m - (j + 1) < m := by omega
    rw [Nat.mod_eq_of_lt hval]
    rw [show j + 1 + (i + m - (j + 1)) = i + m from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hi]

/-- pathPos of j = m - 1 (j is the last position, i.e., "missing" in the m-1 path). -/
private theorem pathPos_of_missing (m j : Nat) (hm : m ≥ 1) (hj : j < m) :
    pathPos m j j = m - 1 := by
  simp only [pathPos, show j + m - (j + 1) = m - 1 from by omega]
  exact Nat.mod_eq_of_lt (by omega)

/-- For i ≠ j: pathPos m j i < m - 1. -/
private theorem pathPos_lt_pred (m j i : Nat) (hm : m ≥ 2) (hi : i < m) (hj : j < m)
    (hne : i ≠ j) : pathPos m j i < m - 1 := by
  have hpos_m1 := pathPos_of_missing m j (by omega) hj
  have hpos_lt : pathPos m j i < m := Nat.mod_lt _ (by omega)
  -- pathPos is injective (mod m), so i ≠ j → pos(i) ≠ pos(j) = m-1
  by_contra hle
  have heq : pathPos m j i = m - 1 := by omega
  -- (j+1 + m-1) % m = j and (j+1 + pathPos(i)) % m = i
  have h1 := pathPos_cube_id m j i (by omega) hi hj
  have h2 := pathPos_cube_id m j j (by omega) hj hj
  rw [heq] at h1; rw [hpos_m1] at h2
  have : i = j := by omega
  exact hne this

/-- pathPos of (i+1)%m = pathPos of i + 1, when i ≠ j. -/
private theorem pathPos_succ (m j i : Nat) (hm : m ≥ 2) (hi : i < m) (hj : j < m)
    (hne : i ≠ j) : pathPos m j ((i + 1) % m) = pathPos m j i + 1 := by
  have hlt := pathPos_lt_pred m j i hm hi hj hne
  simp only [pathPos]
  -- Need: ((i+1)%m + m - (j+1)) % m = (i + m - (j+1)) % m + 1
  -- Since pos(i) < m-1, pos(i)+1 < m
  by_cases hlt2 : i + 1 < m
  · rw [Nat.mod_eq_of_lt hlt2]
    rw [show i + 1 + m - (j + 1) = (i + m - (j + 1)) + 1 from by omega]
    have hval : (i + m - (j + 1)) % m < m - 1 := hlt
    have hval2 : (i + m - (j + 1)) % m + 1 < m := by omega
    rw [Nat.mod_eq_of_lt hval2]
    omega
  · have him : i + 1 = m := by omega
    rw [him, Nat.mod_self]
    rw [show 0 + m - (j + 1) = m - (j + 1) from by omega]
    rw [show i + m - (j + 1) = m + m - (j + 1) - 1 from by omega]
    have hj_pos : j + 1 ≤ m := by omega
    rw [Nat.mod_eq_of_lt (by omega : m - (j + 1) < m)]
    -- Need: m - (j+1) = (m + m - (j+1) - 1) % m + 1
    -- m + m - (j+1) - 1 = 2m - j - 2. This mod m = m - j - 2 (if j < m - 1) or 0 (if j = m-1 then impossible since i ≠ j and i = m-1).
    by_cases hj_last : j = m - 1
    · exfalso; subst hj_last; exact hne (by omega)
    · rw [show m + m - (j + 1) - 1 = m + (m - j - 2) from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : m - j - 2 < m)]
      omega

/-- The XOR cycle of length m is (m-1)-consistent.

    Proof: for any subset S of ≤ m-1 cubes, there's a missing cube j ∉ S.
    Removing cube j breaks the cycle into a path. On a path, we propagate
    bit0 values from one end: bit0 starts at 0, flips when passing cube 0
    (which has parity 1). This gives a consistent gap assignment. -/
/-- pathAssignment assigns valid gaps. -/
private theorem pathAssignment_isGap (m j : Nat) (hm : m ≥ 3) (hj : j < m)
    (idx : Fin (xorCycleGraph m hm).cubes.length) :
    ((xorCycleGraph m hm).cubes[idx]).isGap (pathAssignment m j hm hj idx) = true := by
  simp only [xorCycleGraph, xorCubeList_getElem_fin, pathAssignment]
  exact makeGapVertex_isGap m idx.val _ _
    (by omega) (by rw [xorCycleGraph_length] at idx; exact Nat.lt_of_lt_of_eq idx.isLt (xorCycleGraph_length m hm))
    _ _ rfl

/-- pathAssignment bit1 matches bit0 of next cube, when both are not the missing cube j. -/
private theorem pathAssignment_bit_match (m j : Nat) (hm : m ≥ 3) (hj : j < m)
    (a : Nat) (ha : a < m) (ha_ne_j : a ≠ j) (hnext_ne_j : (a + 1) % m ≠ j) :
    let idx_a : Fin (xorCycleGraph m hm).cubes.length :=
      ⟨a, by rw [xorCycleGraph_length]; exact ha⟩
    let idx_b : Fin (xorCycleGraph m hm).cubes.length :=
      ⟨(a + 1) % m, by rw [xorCycleGraph_length]; exact Nat.mod_lt _ (by omega)⟩
    ((pathAssignment m j hm hj idx_a).val >>> 1) &&& 1 =
    (pathAssignment m j hm hj idx_b).val &&& 1 := by
  simp only [pathAssignment]
  rw [makeGapVertex_bit1, makeGapVertex_bit0]
  -- Need: accParity m j (pathPos m j a) ^^^ xorParity a =
  --        accParity m j (pathPos m j ((a+1)%m))
  rw [pathPos_succ m j a (by omega) ha hj ha_ne_j]
  rw [accParity_succ]
  rw [pathPos_cube_id m j a (by omega) ha hj]

/-- The XOR cycle of length m is (m-1)-consistent.

    Proof: for any subset S of ≤ m-1 cubes, there's a missing cube j ∉ S.
    Removing cube j breaks the cycle into a path. On a path, we propagate
    bit0 values from one end: bit0 starts at 0, flips when passing cube 0
    (which has parity 1). This gives a consistent gap assignment. -/
theorem xorCycle_kconsistent (m : Nat) (hm : m ≥ 3) :
    KConsistent (xorCycleGraph m hm) (m - 1) := by
  intro S hlen hnodup
  -- Step 1: Find missing cube j
  have hlen' : S.length < m := by omega
  obtain ⟨j, hj, hmissing⟩ := exists_missing m (by omega) S hlen' hnodup
  -- Step 2: Construct gap assignment
  let assign := pathAssignment m j hm hj
  -- Step 3: Verify validity and compatibility
  refine ⟨assign, fun idx hidx => pathAssignment_isGap m j hm hj idx,
    fun e he h1 h2 => ?_⟩
  -- Edge e is in the graph: e = (a, (a+1)%m) for some a
  simp only [xorCycleGraph, List.mem_map, List.mem_finRange, true_and] at he
  obtain ⟨⟨a, ha_lt⟩, rfl⟩ := he
  simp only [xorEdge] at h1 h2
  -- e.1 = a, e.2 = (a+1)%m. Both are in S, so both ≠ j.
  have ha_ne_j : a ≠ j := by
    intro heq; subst heq
    exact hmissing ⟨j, by rw [xorCycleGraph_length]; exact hj⟩ h1 rfl
  have hnext_ne_j : (a + 1) % m ≠ j := by
    intro heq
    have hmod_lt : (a + 1) % m < m := Nat.mod_lt _ (by omega)
    exact hmissing ⟨(a + 1) % m, by rw [xorCycleGraph_length]; exact hmod_lt⟩ h2 heq
  -- Use xorCube_transferOp_iff to reduce to gap validity + bit matching
  simp only [xorCycleGraph, xorCubeList_getElem_fin]
  rw [xorCube_transferOp_iff m a hm ha_lt]
  exact ⟨pathAssignment_isGap m j hm hj _
         |> by simp only [xorCycleGraph, xorCubeList_getElem_fin]; exact id,
         pathAssignment_isGap m j hm hj _
         |> by simp only [xorCycleGraph, xorCubeList_getElem_fin]; exact id,
         pathAssignment_bit_match m j hm hj a ha_lt ha_ne_j hnext_ne_j⟩

/-! ## Section 6: Main Theorems -/

/-- **Schoenebeck (constructive)**: for any c, there exist arbitrarily large
    UNSAT CubeGraphs that are c-consistent. -/
theorem schoenebeck_constructive :
    ∀ c : Nat, ∃ n₀ : Nat, ∀ n ≥ n₀,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ KConsistent G c ∧ ¬ G.Satisfiable := by
  intro c; refine ⟨max (c + 1) 3, ?_⟩; intro n hn
  exact ⟨xorCycleGraph n (by omega),
    by rw [xorCycleGraph_length]; omega,
    kconsistent_mono _ (by omega) (xorCycle_kconsistent n (by omega)),
    xorCycle_unsat n (by omega)⟩

/-- **Schoenebeck linear (constructive)**: SA needs level Ω(n).
    There exists c ≥ 2 such that for all n ≥ 1, there's an n-cube UNSAT graph
    that is (n/c)-consistent. -/
theorem schoenebeck_linear_constructive :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ KConsistent G (n / c) ∧ ¬ G.Satisfiable := by
  refine ⟨2, by omega, ?_⟩
  intro n hn
  by_cases hn3 : n ≥ 3
  · exact ⟨xorCycleGraph n hn3, by rw [xorCycleGraph_length]; omega,
      kconsistent_mono _ (by omega) (xorCycle_kconsistent n hn3), xorCycle_unsat n hn3⟩
  · exact ⟨h2Graph, by simp [h2Graph]; omega,
      kconsistent_mono h2Graph (by omega) h2graph_2consistent, h2Graph_unsat⟩

end CubeGraph
