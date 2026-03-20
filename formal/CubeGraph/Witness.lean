/-
  CubeGraph/Witness.lean
  Concrete H² witness: a CubeGraph that is UNSAT with no blocked edges.

  This closes AUDIT.md Gap 2: UNSATType2 was previously unconstructible in Lean.
  The witness is a 3-cube cycle (triangle) with channel misalignment:
  - Each edge has compatible gap pairs (non-zero transfer operator)
  - But no global consistent gap selection exists
  - Rank-2 cycle UNSAT: each operator has anti-diagonal pattern (rank-2),
    both traversal paths return to the wrong gap

  Construction:
    Cube A: vars (1,2,3), gaps {0,3} — assignments (0,0,0) and (1,1,0)
    Cube B: vars (1,4,5), gaps {1,2} — assignments (1,0,0) and (0,1,0)
    Cube C: vars (2,4,6), gaps {0,3} — assignments (0,0,0) and (1,1,0)

  Edge (A,B) shared var 1: pairs (0,2) and (3,1) compatible
  Edge (B,C) shared var 4: pairs (2,3) and (1,0) compatible
  Edge (C,A) shared var 2: pairs (3,3) and (0,0) compatible

  UNSAT: picking gap 0 in A forces gap 2 in B forces gap 3 in C,
         which needs gap 3 in A (var2=1) — but we picked gap 0 (var2=0). ✗
         The other path: gap 3 → gap 1 → gap 0 → needs gap 0 (var2=0),
         but we picked gap 3 (var2=1). ✗

  See: theory/foundations/05-cycles.md (cycle contradictions)
  See: theory/theorems/THEOREM-A-HIERARCHY.md (H² = global incoherence)
  See: formal/CubeGraph/BarrierSummary.lean (r1Graph used as barrier-free witness)
  See: formal/CubeGraph/MinimalBarrier.lean (h2_minimal_three_cubes: r1Graph is the sharp H² boundary)
-/

import CubeGraph.Hierarchy
import CubeGraph.CNF
import CubeGraph.ChannelAlignment

namespace CubeGraph

open BoolMat

/-! ## Section 1: Concrete Cubes -/

/-- Cube A: variables (1,2,3), gapMask = 9 = 0b00001001, gaps at vertices 0 and 3. -/
def h2CubeA : Cube where
  var₁ := 1; var₂ := 2; var₃ := 3
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨9, by omega⟩
  gaps_nonempty := by decide

/-- Cube B: variables (1,4,5), gapMask = 6 = 0b00000110, gaps at vertices 1 and 2. -/
def h2CubeB : Cube where
  var₁ := 1; var₂ := 4; var₃ := 5
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨6, by omega⟩
  gaps_nonempty := by decide

/-- Cube C: variables (2,4,6), gapMask = 9 = 0b00001001, gaps at vertices 0 and 3. -/
def h2CubeC : Cube where
  var₁ := 2; var₂ := 4; var₃ := 6
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨9, by omega⟩
  gaps_nonempty := by decide

/-! ## Section 2: Concrete Graph -/

/-- The H² witness graph: 3 cubes forming a cycle.
    Each pair shares exactly one variable (weight-1 edges). -/
def h2Graph : CubeGraph where
  cubes := [h2CubeA, h2CubeB, h2CubeC]
  edges := [(⟨0, by decide⟩, ⟨1, by decide⟩),
            (⟨1, by decide⟩, ⟨2, by decide⟩),
            (⟨2, by decide⟩, ⟨0, by decide⟩)]
  edges_valid := by native_decide
  edges_complete := by native_decide

/-! ## Section 3: Exhaustive SAT Check -/

/-- Boolean check: does h2Graph have any valid compatible gap selection?
    Enumerates all 8³ = 512 possible (g0, g1, g2) triples. -/
private def h2SatCheck : Bool :=
  (List.finRange 8).any fun g0 =>
  (List.finRange 8).any fun g1 =>
  (List.finRange 8).any fun g2 =>
    h2CubeA.isGap g0 && h2CubeB.isGap g1 && h2CubeC.isGap g2 &&
    transferOp h2CubeA h2CubeB g0 g1 &&
    transferOp h2CubeB h2CubeC g1 g2 &&
    transferOp h2CubeC h2CubeA g2 g0

/-- The exhaustive check returns false: no valid compatible selection exists. -/
private theorem h2SatCheck_false : h2SatCheck = false := by native_decide

/-! ## Section 4: Connecting Boolean Check to Satisfiable -/

/-- If h2Graph is satisfiable, the boolean check would return true.
    This is the soundness direction: any valid selection witnesses a true entry. -/
private theorem sat_implies_h2Check (h : h2Graph.Satisfiable) : h2SatCheck = true := by
  obtain ⟨s, hv, hc⟩ := h
  unfold h2SatCheck
  rw [List.any_eq_true]
  refine ⟨s ⟨0, by decide⟩, mem_finRange _, ?_⟩
  rw [List.any_eq_true]
  refine ⟨s ⟨1, by decide⟩, mem_finRange _, ?_⟩
  rw [List.any_eq_true]
  refine ⟨s ⟨2, by decide⟩, mem_finRange _, ?_⟩
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨hv ⟨0, by decide⟩, hv ⟨1, by decide⟩⟩, hv ⟨2, by decide⟩⟩,
    hc _ (List.Mem.head _)⟩,
    hc _ (List.Mem.tail _ (List.Mem.head _))⟩,
    hc _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))⟩

/-! ## Section 5: Main Theorems -/

/-- The h2Graph is UNSAT: no valid compatible gap selection exists. -/
theorem h2Graph_unsat : ¬ h2Graph.Satisfiable := by
  intro h
  have := sat_implies_h2Check h
  rw [h2SatCheck_false] at this
  exact Bool.false_ne_true this

/-- The h2Graph has no blocked edges: every edge has a compatible gap pair. -/
theorem h2Graph_no_blocked : ¬ HasBlockedEdge h2Graph := by
  intro ⟨e, he, hb⟩
  simp only [h2Graph, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact absurd hb (by native_decide)
  · exact absurd hb (by native_decide)
  · exact absurd hb (by native_decide)

/-- **H² WITNESS**: h2Graph is UNSATType2 — the first concrete H² instance in Lean.
    This makes the H² type non-vacuous: global incoherence really exists. -/
theorem h2_witness : UNSATType2 h2Graph :=
  ⟨h2Graph_unsat, H0_impossible h2Graph, h2Graph_no_blocked⟩

/-! ## Section 6: CNF Bridge -/

/-- Full CNF bridge for h2Graph: CubeGraph satisfiability equals formula satisfiability. -/
theorem h2Graph_bridge : h2Graph.Satisfiable ↔ h2Graph.FormulaSat :=
  sat_iff_formula_sat h2Graph

/-! ## Section 7: SAT Witness -/

/-- A cube with 7 gaps (only vertex 7 is filled). -/
def satCube : Cube where
  var₁ := 1; var₂ := 2; var₃ := 3
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨127, by omega⟩
  gaps_nonempty := by decide

/-- A trivially satisfiable CubeGraph: one cube, no edges. -/
def satGraph : CubeGraph where
  cubes := [satCube]
  edges := []
  edges_valid := by intro e he; simp at he
  edges_complete := by
    intro i j hij
    have hi := i.isLt; have hj := j.isLt
    simp only [List.length] at hi hj
    exact absurd (Fin.ext (by omega)) hij

/-- satGraph is satisfiable: pick gap 0, no edges to violate. -/
theorem satGraph_satisfiable : satGraph.Satisfiable :=
  ⟨fun _ => ⟨0, by omega⟩,
   fun i => by revert i; native_decide,
   fun e he => by simp [satGraph] at he⟩

/-! ## Section 8: H¹ Witness -/

/-- Cube D: vars (1,2,3), single gap at vertex 0 (var1=0). -/
def h1CubeD : Cube where
  var₁ := 1; var₂ := 2; var₃ := 3
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨1, by omega⟩
  gaps_nonempty := by decide

/-- Cube E: vars (1,4,5), single gap at vertex 1 (var1=1). -/
def h1CubeE : Cube where
  var₁ := 1; var₂ := 4; var₃ := 5
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨2, by omega⟩
  gaps_nonempty := by decide

/-- H¹ witness graph: 2 cubes sharing var 1 with incompatible gaps.
    Cube D has gap 0 (var1=0), Cube E has gap 1 (var1=1).
    The only gap pair disagrees on var 1 → blocked edge. -/
def h1Graph : CubeGraph where
  cubes := [h1CubeD, h1CubeE]
  edges := [(⟨0, by decide⟩, ⟨1, by decide⟩)]
  edges_valid := by native_decide
  edges_complete := by native_decide

/-- h1Graph has a blocked edge: transferOp is zero on the single edge. -/
theorem h1Graph_has_blocked : HasBlockedEdge h1Graph :=
  ⟨_, List.Mem.head _, by native_decide⟩

/-- h1Graph is UNSAT (from blocked edge). -/
theorem h1Graph_unsat : ¬ h1Graph.Satisfiable :=
  hasBlockedEdge_implies_unsat h1Graph h1Graph_has_blocked

/-- **H¹ WITNESS**: h1Graph is UNSATType1 — blocked edge causes UNSAT. -/
theorem h1_witness : UNSATType1 h1Graph :=
  ⟨h1Graph_unsat, H0_impossible h1Graph, h1Graph_has_blocked⟩

/-! ## Section 9: Hierarchy Completeness -/

/-- The UNSAT hierarchy is fully concrete and non-vacuous:
    - H⁰ is impossible for all CubeGraphs (Cube.gaps_nonempty invariant)
    - H¹ exists (h1Graph: blocked edge)
    - H² exists (h2Graph: global incoherence)
    - SAT exists (satGraph: trivially satisfiable)
    This makes every branch of the classification constructive. -/
theorem hierarchy_complete :
    (∀ G : CubeGraph, ¬ UNSATType0 G) ∧
    (∃ G : CubeGraph, UNSATType1 G) ∧
    (∃ G : CubeGraph, UNSATType2 G) ∧
    (∃ G : CubeGraph, G.Satisfiable) :=
  ⟨UNSATType0_impossible, ⟨_, h1_witness⟩, ⟨_, h2_witness⟩, ⟨_, satGraph_satisfiable⟩⟩

/-! ## Section 10: Rank-1 H² Witness

  A rank-1 H² witness: 3 cubes forming a cycle where ALL transfer operators
  are rank-1 (factor as R ⊗ C), yet the cycle is UNSAT due to channel misalignment.
  This directly connects to the Channel Alignment Theorem (ChannelAlignment.lean).

  Construction:
    Cube rA: vars (1,2,3), gaps {0,4} — var₁ varies, var₂=var₃=0 fixed
    Cube rB: vars (1,4,5), gaps {1,2,5,6} — var₁=0 ↦ {2,6}, var₄=0 ↦ {1,5}
    Cube rC: vars (2,4,6), gaps {0,4} — var₂ varies, var₄=var₆=0 fixed

  Channel alignment at cube B FAILS:
    colSup(M_AB) = {2,6} (B-gaps reachable from A)
    rowSup(M_BC) = {1,5} (B-gaps that can reach C)
    {2,6} ∩ {1,5} = ∅ → misalignment → UNSAT
-/

/-- Rank-1 cube A: vars (1,2,3), gapMask = 17 = 0b00010001, gaps at 0 and 4. -/
def r1CubeA : Cube where
  var₁ := 1; var₂ := 2; var₃ := 3
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨17, by omega⟩
  gaps_nonempty := by decide

/-- Rank-1 cube B: vars (1,4,5), gapMask = 102 = 0b01100110, gaps at 1,2,5,6. -/
def r1CubeB : Cube where
  var₁ := 1; var₂ := 4; var₃ := 5
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨102, by omega⟩
  gaps_nonempty := by decide

/-- Rank-1 cube C: vars (2,4,6), gapMask = 17 = 0b00010001, gaps at 0 and 4. -/
def r1CubeC : Cube where
  var₁ := 2; var₂ := 4; var₃ := 6
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨17, by omega⟩
  gaps_nonempty := by decide

/-! ## Section 11: Rank-1 Graph + Operators -/

/-- The rank-1 H² witness graph: 3 cubes forming a cycle. -/
def r1Graph : CubeGraph where
  cubes := [r1CubeA, r1CubeB, r1CubeC]
  edges := [(⟨0, by decide⟩, ⟨1, by decide⟩),
            (⟨1, by decide⟩, ⟨2, by decide⟩),
            (⟨2, by decide⟩, ⟨0, by decide⟩)]
  edges_valid := by native_decide
  edges_complete := by native_decide

/-- The 3 transfer operators forming the cycle A→B→C→A. -/
def r1Ops : List (BoolMat 8) :=
  [transferOp r1CubeA r1CubeB,
   transferOp r1CubeB r1CubeC,
   transferOp r1CubeC r1CubeA]

/-! ## Section 12: Rank-1 Proofs -/

private def r1_R_AB : Fin 8 → Bool := fun i => i == 0 || i == 4
private def r1_C_AB : Fin 8 → Bool := fun j => j == 2 || j == 6

private def r1_R_BC : Fin 8 → Bool := fun i => i == 1 || i == 5
private def r1_C_BC : Fin 8 → Bool := fun j => j == 0 || j == 4

private def r1_R_CA : Fin 8 → Bool := fun i => i == 0 || i == 4
private def r1_C_CA : Fin 8 → Bool := fun j => j == 0 || j == 4

theorem r1_AB_rankOne : (transferOp r1CubeA r1CubeB).IsRankOne :=
  ⟨r1_R_AB, r1_C_AB, ⟨⟨0, by omega⟩, by decide⟩, ⟨⟨2, by omega⟩, by decide⟩, by native_decide⟩

theorem r1_BC_rankOne : (transferOp r1CubeB r1CubeC).IsRankOne :=
  ⟨r1_R_BC, r1_C_BC, ⟨⟨1, by omega⟩, by decide⟩, ⟨⟨0, by omega⟩, by decide⟩, by native_decide⟩

theorem r1_CA_rankOne : (transferOp r1CubeC r1CubeA).IsRankOne :=
  ⟨r1_R_CA, r1_C_CA, ⟨⟨0, by omega⟩, by decide⟩, ⟨⟨0, by omega⟩, by decide⟩, by native_decide⟩

/-! ## Section 13: Channel Alignment Connection -/

/-- The rank-1 cycle built from r1Ops. -/
def r1Cycle : RankOneCycle 8 where
  operators := r1Ops
  length_ge := by simp [r1Ops]
  all_rank_one := by
    intro M hM; simp [r1Ops] at hM
    rcases hM with rfl | rfl | rfl
    · exact r1_AB_rankOne
    · exact r1_BC_rankOne
    · exact r1_CA_rankOne

/-- The composed operator has trace false: no gap can traverse the cycle and return. -/
theorem r1_trace_false :
    BoolMat.trace (r1Cycle.operators.foldl BoolMat.mul BoolMat.one) = false :=
  by native_decide

/-- **Channel alignment correctly predicts UNSAT**: the rank-1 cycle is not
    fully channel-aligned (misalignment at cube B). -/
theorem r1_channel_misaligned : ¬ fullyChannelAligned r1Ops := by
  intro h
  have := (channel_alignment r1Cycle).mpr h
  rw [r1_trace_false] at this
  exact Bool.false_ne_true this

/-! ## Section 14: UNSAT and H² for Rank-1 Witness -/

/-- Exhaustive SAT check for r1Graph (512 triples). -/
private def r1SatCheck : Bool :=
  (List.finRange 8).any fun g0 =>
  (List.finRange 8).any fun g1 =>
  (List.finRange 8).any fun g2 =>
    r1CubeA.isGap g0 && r1CubeB.isGap g1 && r1CubeC.isGap g2 &&
    transferOp r1CubeA r1CubeB g0 g1 &&
    transferOp r1CubeB r1CubeC g1 g2 &&
    transferOp r1CubeC r1CubeA g2 g0

private theorem r1SatCheck_false : r1SatCheck = false := by native_decide

private theorem sat_implies_r1Check (h : r1Graph.Satisfiable) : r1SatCheck = true := by
  obtain ⟨s, hv, hc⟩ := h
  unfold r1SatCheck
  rw [List.any_eq_true]
  refine ⟨s ⟨0, by decide⟩, mem_finRange _, ?_⟩
  rw [List.any_eq_true]
  refine ⟨s ⟨1, by decide⟩, mem_finRange _, ?_⟩
  rw [List.any_eq_true]
  refine ⟨s ⟨2, by decide⟩, mem_finRange _, ?_⟩
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨hv ⟨0, by decide⟩, hv ⟨1, by decide⟩⟩, hv ⟨2, by decide⟩⟩,
    hc _ (List.Mem.head _)⟩,
    hc _ (List.Mem.tail _ (List.Mem.head _))⟩,
    hc _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))⟩

/-- r1Graph is UNSAT. -/
theorem r1Graph_unsat : ¬ r1Graph.Satisfiable := by
  intro h
  have := sat_implies_r1Check h
  rw [r1SatCheck_false] at this
  exact Bool.false_ne_true this

/-- r1Graph has no blocked edges. -/
theorem r1Graph_no_blocked : ¬ HasBlockedEdge r1Graph := by
  intro ⟨e, he, hb⟩
  simp only [r1Graph, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact absurd hb (by native_decide)
  · exact absurd hb (by native_decide)
  · exact absurd hb (by native_decide)

/-- r1Graph is UNSATType2 — a rank-1 H² instance. -/
theorem r1_h2_witness : UNSATType2 r1Graph :=
  ⟨r1Graph_unsat, H0_impossible r1Graph, r1Graph_no_blocked⟩

/-! ## Section 15: Channel Alignment Characterizes H² -/

/-- **THE CONNECTION**: Channel alignment correctly characterizes this H² witness.
    The rank-1 cycle is not channel-aligned, and the graph is UNSATType2.
    This links the concrete witness to the main algebraic theorem. -/
theorem r1_alignment_characterizes_h2 :
    ¬ fullyChannelAligned r1Ops ∧ UNSATType2 r1Graph :=
  ⟨r1_channel_misaligned, r1_h2_witness⟩

/-! ## Section 16: H¹·⁵ Backward Witness

  A CubeGraph that is:
  - Acyclic (path of 3 cubes)
  - No blocked edges (every edge has at least one compatible gap pair)
  - UNSAT (no globally consistent gap selection)

  This is a counterexample to the false theorem "acyclic + non-blocked → SAT".
  The correct theorem requires arc-consistency, not just non-blocked edges.

  Construction:
    Cube bw1: vars (1,2,3), gapMask = 1,  gaps = {0}     → var1=0
    Cube bw2: vars (1,4,5), gapMask = 9,  gaps = {0, 3}  → var1=0 or var1=1,var4=1
    Cube bw3: vars (4,6,7), gapMask = 2,  gaps = {1}     → var4=1

  Edge (bw1, bw2) shared var 1: pair (0,0) compatible (var1=0 in both)
  Edge (bw2, bw3) shared var 4: pair (3,1) compatible (var4=1 in both)
  No edge (bw1, bw3): no shared variables

  UNSAT: bw1 forces bw2=gap0 (var1=0), bw3 forces bw2=gap3 (var4=1).
         But gap0 has var4=0, contradicting bw3. And gap3 has var1=1, contradicting bw1.
         bw2 can't satisfy both neighbors simultaneously.

  Level H¹·⁵: between H¹ (blocked edge) and H² (global cycle incoherence).
  Detectable in P by arc-consistency (AC-3).

  See: experiments-ml/008_2026-03-04_why-h2-hard/DISCOVERY-CHAIN-2026-03-04.md §2
  See: experiments-ml/008_2026-03-04_why-h2-hard/PLAN-FAZA2-LEAN-FIXPOINT-MONOTONICITY.md (plan)
-/

/-- Backward cube 1: vars (1,2,3), single gap at vertex 0 (var1=0, var2=0, var3=0). -/
def bwCube1 : Cube where
  var₁ := 1; var₂ := 2; var₃ := 3
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨1, by omega⟩
  gaps_nonempty := by decide

/-- Backward cube 2: vars (1,4,5), gaps at vertices 0 and 3. -/
def bwCube2 : Cube where
  var₁ := 1; var₂ := 4; var₃ := 5
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨9, by omega⟩
  gaps_nonempty := by decide

/-- Backward cube 3: vars (4,6,7), single gap at vertex 1 (var4=1, var6=0, var7=0). -/
def bwCube3 : Cube where
  var₁ := 4; var₂ := 6; var₃ := 7
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨2, by omega⟩
  gaps_nonempty := by decide

/-- H¹·⁵ witness graph: path bw1-bw2-bw3.
    bw1 and bw2 share var 1, bw2 and bw3 share var 4, bw1 and bw3 share nothing. -/
def bwGraph : CubeGraph where
  cubes := [bwCube1, bwCube2, bwCube3]
  edges := [(⟨0, by decide⟩, ⟨1, by decide⟩),
            (⟨1, by decide⟩, ⟨2, by decide⟩)]
  edges_valid := by native_decide
  edges_complete := by native_decide

/-! ## Section 17: H¹·⁵ Proofs -/

/-- Exhaustive SAT check for bwGraph. -/
private def bwSatCheck : Bool :=
  (List.finRange 8).any fun g0 =>
  (List.finRange 8).any fun g1 =>
  (List.finRange 8).any fun g2 =>
    bwCube1.isGap g0 && bwCube2.isGap g1 && bwCube3.isGap g2 &&
    transferOp bwCube1 bwCube2 g0 g1 &&
    transferOp bwCube2 bwCube3 g1 g2

private theorem bwSatCheck_false : bwSatCheck = false := by native_decide

private theorem sat_implies_bwCheck (h : bwGraph.Satisfiable) : bwSatCheck = true := by
  obtain ⟨s, hv, hc⟩ := h
  unfold bwSatCheck
  rw [List.any_eq_true]
  refine ⟨s ⟨0, by decide⟩, mem_finRange _, ?_⟩
  rw [List.any_eq_true]
  refine ⟨s ⟨1, by decide⟩, mem_finRange _, ?_⟩
  rw [List.any_eq_true]
  refine ⟨s ⟨2, by decide⟩, mem_finRange _, ?_⟩
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨hv ⟨0, by decide⟩, hv ⟨1, by decide⟩⟩, hv ⟨2, by decide⟩⟩,
    hc _ (List.Mem.head _)⟩,
    hc _ (List.Mem.tail _ (List.Mem.head _))⟩

/-- bwGraph is UNSAT: arc-inconsistency on acyclic path. -/
theorem bwGraph_unsat : ¬ bwGraph.Satisfiable := by
  intro h
  have := sat_implies_bwCheck h
  rw [bwSatCheck_false] at this
  exact Bool.false_ne_true this

/-- bwGraph has no blocked edges: each edge has at least one compatible pair. -/
theorem bwGraph_no_blocked : ¬ HasBlockedEdge bwGraph := by
  intro ⟨e, he, hb⟩
  simp only [bwGraph, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact absurd hb (by native_decide)
  · exact absurd hb (by native_decide)

/-- **H¹·⁵ WITNESS**: acyclic path, no blocked edges, but UNSAT.
    Counterexample to "acyclic + non-blocked → SAT".
    The correct theorem requires arc-consistency (detectable in P via AC-3). -/
theorem bw_h15_witness : ¬ bwGraph.Satisfiable ∧ ¬ HasBlockedEdge bwGraph :=
  ⟨bwGraph_unsat, bwGraph_no_blocked⟩

end CubeGraph
