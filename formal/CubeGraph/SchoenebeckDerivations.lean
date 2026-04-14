/-
  CubeGraph/SchoenebeckDerivations.lean — 4-cube XOR cycle: 3-consistent AND UNSAT

  . 0 axioms.
-/

import CubeGraph.BandwidthGap

set_option maxHeartbeats 1600000

namespace CubeGraph

open BoolMat

private def xc4_c0 : Cube :=
  { var₁ := 4, var₂ := 1, var₃ := 5,
    var₁_pos := by omega, var₂_pos := by omega, var₃_pos := by omega,
    vars_distinct := by decide, gapMask := ⟨102, by omega⟩, gaps_nonempty := by decide }

private def xc4_c1 : Cube :=
  { var₁ := 1, var₂ := 2, var₃ := 6,
    var₁_pos := by omega, var₂_pos := by omega, var₃_pos := by omega,
    vars_distinct := by decide, gapMask := ⟨153, by omega⟩, gaps_nonempty := by decide }

private def xc4_c2 : Cube :=
  { var₁ := 2, var₂ := 3, var₃ := 7,
    var₁_pos := by omega, var₂_pos := by omega, var₃_pos := by omega,
    vars_distinct := by decide, gapMask := ⟨153, by omega⟩, gaps_nonempty := by decide }

private def xc4_c3 : Cube :=
  { var₁ := 3, var₂ := 4, var₃ := 8,
    var₁_pos := by omega, var₂_pos := by omega, var₃_pos := by omega,
    vars_distinct := by decide, gapMask := ⟨153, by omega⟩, gaps_nonempty := by decide }

def xc4Graph : CubeGraph where
  cubes := [xc4_c0, xc4_c1, xc4_c2, xc4_c3]
  edges := [(⟨0, by decide⟩, ⟨1, by decide⟩), (⟨1, by decide⟩, ⟨2, by decide⟩),
            (⟨2, by decide⟩, ⟨3, by decide⟩), (⟨3, by decide⟩, ⟨0, by decide⟩)]
  edges_valid := by native_decide
  edges_complete := by native_decide

/-! ## UNSAT -/

private def xc4SatCheck : Bool :=
  (List.finRange 8).any fun g0 => (List.finRange 8).any fun g1 =>
  (List.finRange 8).any fun g2 => (List.finRange 8).any fun g3 =>
    xc4_c0.isGap g0 && xc4_c1.isGap g1 && xc4_c2.isGap g2 && xc4_c3.isGap g3 &&
    transferOp xc4_c0 xc4_c1 g0 g1 && transferOp xc4_c1 xc4_c2 g1 g2 &&
    transferOp xc4_c2 xc4_c3 g2 g3 && transferOp xc4_c3 xc4_c0 g3 g0

private theorem xc4SatCheck_false : xc4SatCheck = false := by native_decide

private theorem sat_implies_xc4Check (h : xc4Graph.Satisfiable) : xc4SatCheck = true := by
  obtain ⟨s, hv, hc⟩ := h; unfold xc4SatCheck
  rw [List.any_eq_true]; refine ⟨s ⟨0, by decide⟩, mem_finRange _, ?_⟩
  rw [List.any_eq_true]; refine ⟨s ⟨1, by decide⟩, mem_finRange _, ?_⟩
  rw [List.any_eq_true]; refine ⟨s ⟨2, by decide⟩, mem_finRange _, ?_⟩
  rw [List.any_eq_true]; refine ⟨s ⟨3, by decide⟩, mem_finRange _, ?_⟩
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨hv ⟨0, by decide⟩, hv ⟨1, by decide⟩⟩, hv ⟨2, by decide⟩⟩, hv ⟨3, by decide⟩⟩,
    hc _ (.head _)⟩, hc _ (.tail _ (.head _))⟩,
    hc _ (.tail _ (.tail _ (.head _)))⟩,
    hc _ (.tail _ (.tail _ (.tail _ (.head _))))⟩

theorem xc4_unsat : ¬ xc4Graph.Satisfiable := by
  intro h; exact Bool.false_ne_true (xc4SatCheck_false ▸ sat_implies_xc4Check h)

/-! ## 3-Consistent -/

-- Use a different approach: define witnesses directly using Fin xc4Graph.cubes.length.
-- Avoid the Fin 4 ↔ Fin xc4Graph.cubes.length conversion problem entirely.

/-- Gap witness for each possible "missing cube index" (as Nat). -/
private def xc4GapAt (missing : Nat) (cube : Nat) : Vertex :=
  if missing == 0 then
    match cube with | 0 => ⟨1,by omega⟩ | 1 => ⟨0,by omega⟩ | 2 => ⟨0,by omega⟩ | _ => ⟨0,by omega⟩
  else if missing == 1 then
    match cube with | 0 => ⟨1,by omega⟩ | 2 => ⟨3,by omega⟩ | 3 => ⟨3,by omega⟩ | _ => ⟨0,by omega⟩
  else if missing == 2 then
    match cube with | 0 => ⟨1,by omega⟩ | 1 => ⟨0,by omega⟩ | 3 => ⟨3,by omega⟩ | _ => ⟨0,by omega⟩
  else  -- missing == 3
    match cube with | 0 => ⟨1,by omega⟩ | 1 => ⟨0,by omega⟩ | 2 => ⟨0,by omega⟩ | _ => ⟨0,by omega⟩

/-- The 4 cubes as a function of Nat index. -/
private def xc4CubeAt (i : Nat) : Cube :=
  match i with | 0 => xc4_c0 | 1 => xc4_c1 | 2 => xc4_c2 | _ => xc4_c3

/-- xc4CubeAt matches the graph's cube list. -/
private theorem xc4CubeAt_eq (i : Fin xc4Graph.cubes.length) :
    xc4CubeAt i.val = xc4Graph.cubes[i] := by
  have hi := i.isLt; simp [xc4Graph] at hi
  match i with
  | ⟨0,_⟩ => rfl | ⟨1,_⟩ => rfl | ⟨2,_⟩ => rfl | ⟨3,_⟩ => rfl

/-- Validity check: for each missing/cube pair, gap is valid. -/
private theorem xc4GapAt_valid : ∀ m : Fin 4, ∀ c : Fin 4, c ≠ m →
    (xc4CubeAt c.val).isGap (xc4GapAt m.val c.val) = true := by native_decide

/-- Compatibility check: for each missing index and each edge (a,b) not touching missing,
    the transfer operator is true. -/
private theorem xc4GapAt_compat : ∀ m : Fin 4, ∀ a b : Fin 4,
    -- The edge (a,b) is in the edge list (checked via Nat values)
    ((a.val == 0 && b.val == 1) || (a.val == 1 && b.val == 2) ||
     (a.val == 2 && b.val == 3) || (a.val == 3 && b.val == 0)) = true →
    a ≠ m → b ≠ m →
    transferOp (xc4CubeAt a.val) (xc4CubeAt b.val) (xc4GapAt m.val a.val) (xc4GapAt m.val b.val) = true := by
  native_decide

/-- The edge membership condition as Nat equality matches the actual edge list. -/
private theorem xc4_edge_nat (e : Fin xc4Graph.cubes.length × Fin xc4Graph.cubes.length)
    (he : e ∈ xc4Graph.edges) :
    ((e.1.val == 0 && e.2.val == 1) || (e.1.val == 1 && e.2.val == 2) ||
     (e.1.val == 2 && e.2.val == 3) || (e.1.val == 3 && e.2.val == 0)) = true := by
  let f := fun (p : Fin xc4Graph.cubes.length × Fin xc4Graph.cubes.length) => (p.1.val, p.2.val)
  have hemap : xc4Graph.edges.map f = [(0,1), (1,2), (2,3), (3,0)] := by native_decide
  have hmem : f e ∈ xc4Graph.edges.map f := List.mem_map.mpr ⟨e, he, rfl⟩
  rw [hemap] at hmem
  simp only [f, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all

theorem xc4_3consistent : KConsistent xc4Graph 3 := by
  intro S hlen hnodup
  -- Find missing cube.
  have hlen4 : xc4Graph.cubes.length = 4 := by simp [xc4Graph]
  -- Every i : Fin xc4Graph.cubes.length has i.val < 4.
  have hbound : ∀ i : Fin xc4Graph.cubes.length, i.val < 4 := fun i => hlen4 ▸ i.isLt
  -- Pigeonhole: |S| ≤ 3 < 4 = |cubes|, so some index is not in S.
  have hmissing : ∃ j : Nat, j < 4 ∧ ∀ i ∈ S, i.val ≠ j := by
    -- Check each index 0,1,2,3.
    rcases Classical.em (∀ i ∈ S, i.val ≠ 0) with h0 | h0
    · exact ⟨0, by omega, h0⟩
    · rcases Classical.em (∀ i ∈ S, i.val ≠ 1) with h1 | h1
      · exact ⟨1, by omega, h1⟩
      · rcases Classical.em (∀ i ∈ S, i.val ≠ 2) with h2 | h2
        · exact ⟨2, by omega, h2⟩
        · -- 0, 1, 2 all appear in S. Show 3 doesn't.
          -- From ¬(∀ i ∈ S, i.val ≠ k), we get ∃ i ∈ S, i.val = k.
          have get : ∀ {k : Nat}, ¬(∀ i ∈ S, i.val ≠ k) → ∃ i ∈ S, i.val = k := by
            intro k hk; apply Classical.byContradiction; intro h
            apply hk; intro i hi heq
            exact h ⟨i, hi, heq⟩
          obtain ⟨i0, hi0, hv0⟩ := get h0
          obtain ⟨i1, hi1, hv1⟩ := get h1
          obtain ⟨i2, hi2, hv2⟩ := get h2
          refine ⟨3, by omega, fun i hi heq => ?_⟩
          have hne01 : i0 ≠ i1 := fun h => by rw [congrArg Fin.val h] at hv0; omega
          have hne02 : i0 ≠ i2 := fun h => by rw [congrArg Fin.val h] at hv0; omega
          have hne12 : i1 ≠ i2 := fun h => by rw [congrArg Fin.val h] at hv1; omega
          have hne0i : i0 ≠ i := fun h => by rw [congrArg Fin.val h] at hv0; omega
          have hne1i : i1 ≠ i := fun h => by rw [congrArg Fin.val h] at hv1; omega
          have hne2i : i2 ≠ i := fun h => by rw [congrArg Fin.val h] at hv2; omega
          have := List.length_erase_of_mem hi0
          have := List.length_erase_of_mem ((List.mem_erase_of_ne hne01.symm).mpr hi1)
          have := List.length_erase_of_mem
            ((List.mem_erase_of_ne hne12.symm).mpr ((List.mem_erase_of_ne hne02.symm).mpr hi2))
          have := List.length_pos_of_mem
            ((List.mem_erase_of_ne hne2i.symm).mpr
              ((List.mem_erase_of_ne hne1i.symm).mpr
                ((List.mem_erase_of_ne hne0i.symm).mpr hi)))
          omega
  obtain ⟨mval, hmlt, hmiss⟩ := hmissing
  -- Use the gap witness for this missing index.
  refine ⟨fun i => xc4GapAt mval i.val, fun i hi => ?_, fun e he h1 h2 => ?_⟩
  · -- Valid gap.
    rw [← xc4CubeAt_eq]
    exact xc4GapAt_valid ⟨mval, hmlt⟩ ⟨i.val, hbound i⟩
      (fun heq => hmiss i hi (by have := Fin.val_eq_of_eq heq; simp_all))
  · -- Compatible on edges.
    rw [← xc4CubeAt_eq, ← xc4CubeAt_eq]
    exact xc4GapAt_compat ⟨mval, hmlt⟩ ⟨e.1.val, hbound e.1⟩ ⟨e.2.val, hbound e.2⟩
      (xc4_edge_nat e he)
      (fun heq => hmiss e.1 h1 (by have := Fin.val_eq_of_eq heq; simp_all))
      (fun heq => hmiss e.2 h2 (by have := Fin.val_eq_of_eq heq; simp_all))

/-! ## NOT 4-consistent -/

theorem xc4_not_4consistent : ¬ KConsistent xc4Graph 4 := by
  intro h4; apply xc4_unsat
  let S : List (Fin xc4Graph.cubes.length) :=
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]
  obtain ⟨s, hv, hc⟩ := h4 S (by decide) (by decide)
  refine ⟨s, fun i => ?_, fun e he => ?_⟩
  · have : i ∈ S := by
      have := i.isLt; simp [xc4Graph] at this
      match i with
      | ⟨0,_⟩ => exact .head _ | ⟨1,_⟩ => exact .tail _ (.head _)
      | ⟨2,_⟩ => exact .tail _ (.tail _ (.head _))
      | ⟨3,_⟩ => exact .tail _ (.tail _ (.tail _ (.head _)))
    exact hv i this
  · have he1 : e.1 ∈ S := by
      match e.1 with
      | ⟨0,_⟩ => exact .head _ | ⟨1,_⟩ => exact .tail _ (.head _)
      | ⟨2,_⟩ => exact .tail _ (.tail _ (.head _))
      | ⟨3,_⟩ => exact .tail _ (.tail _ (.tail _ (.head _)))
    have he2 : e.2 ∈ S := by
      match e.2 with
      | ⟨0,_⟩ => exact .head _ | ⟨1,_⟩ => exact .tail _ (.head _)
      | ⟨2,_⟩ => exact .tail _ (.tail _ (.head _))
      | ⟨3,_⟩ => exact .tail _ (.tail _ (.tail _ (.head _)))
    exact hc e he he1 he2

/-! ## Main Theorems -/

theorem xc4_bandwidth_gap : BandwidthGap xc4Graph 3 4 :=
  ⟨xc4_3consistent, xc4_not_4consistent, by omega⟩

theorem consistency_gap_3 :
    ∃ G : CubeGraph, KConsistent G 3 ∧ ¬ G.Satisfiable :=
  ⟨xc4Graph, xc4_3consistent, xc4_unsat⟩

theorem bandwidth_gap_hierarchy :
    (∃ G : CubeGraph, BandwidthGap G 2 3) ∧ (∃ G : CubeGraph, BandwidthGap G 3 4) :=
  ⟨⟨h2Graph, h2_bandwidth_gap⟩, ⟨xc4Graph, xc4_bandwidth_gap⟩⟩

theorem consistency_gap_le3 (c : Nat) (hc : c ≤ 3) :
    ∃ G : CubeGraph, KConsistent G c ∧ ¬ G.Satisfiable := by
  by_cases h : c ≤ 2
  · exact ⟨h2Graph, kconsistent_mono h2Graph h h2graph_2consistent, h2Graph_unsat⟩
  · exact ⟨xc4Graph, kconsistent_mono xc4Graph (by omega) xc4_3consistent, xc4_unsat⟩

end CubeGraph
