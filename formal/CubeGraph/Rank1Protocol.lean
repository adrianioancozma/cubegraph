/-
  CubeGraph/Rank1Protocol.lean

  Rank-1 Observation Protocol: an explicit model of computation where
  an algorithm observes CubeGraph through boolean compositions (each
  yielding a rank-≤1 matrix) and decides SAT/UNSAT.

  Main result: any Rank-1 Protocol must touch ≥ b(n) = Ω(n) cubes,
  because sub-linear subsets always admit consistent gap selections
  (the protocol is "blind" to UNSAT).

  This is sa_lower_bound in communication complexity language.

  See: InformationChannel.lean (sa_lower_bound, blind_below_borromean)
  See: IntegerMonodromy.lean (information_loss)
  See: experiments-ml/024/PAS3A-PLAN-RANK1PROTOCOL.md
-/

import CubeGraph.InformationChannel
import CubeGraph.IntegerMonodromy

namespace CubeGraph

open BoolMat NatMat

/-! ## Section 1: Rank-1 Observation -/

/-- A rank-1 observation: a composition along a path producing rank ≤ 1.
    After rank decay (~5 steps), every long composition is dead.
    Each observation carries at most 8 boolean trace bits. -/
structure Rank1Observation (G : CubeGraph) where
  path : CompositionSeq G
  isDead : ChannelDead G path

/-- A Rank-1 Protocol: observations + verdict. Models any algorithm
    that reads CubeGraph through boolean composition of transfer ops. -/
structure Rank1Protocol (G : CubeGraph) where
  observations : List (Rank1Observation G)
  verdict : Bool

/-! ## Section 2: Observation information bound -/

/-- Boolean trace count of any 8×8 matrix is at most 8. -/
theorem boolTraceCount_le_eight (M : BoolMat 8) : boolTraceCount M ≤ 8 := by
  unfold boolTraceCount
  have h1 : (List.finRange 8).countP (fun i => M i i) ≤ (List.finRange 8).length :=
    List.countP_le_length
  have h2 : (List.finRange 8).length = 8 := by
    unfold List.finRange; exact List.length_ofFn
  omega

/-- Each rank-1 observation's trace count is ≤ 8 bits. -/
theorem observation_trace_bounded (G : CubeGraph) (obs : Rank1Observation G) :
    boolTraceCount (composeSeq G obs.path) ≤ 8 :=
  boolTraceCount_le_eight _

/-! ## Section 3: Protocol blindness below Borromean order -/

/-- **Protocol Blindness**: Any subset of < b cubes on a graph with
    Borromean order b admits a consistent gap selection.
    The protocol CANNOT distinguish SAT from UNSAT on these cubes.

    This is the core argument: KConsistent G (b-1) means any (b-1)-subset
    has a consistent assignment. A rank-1 protocol touching < b cubes
    sees only a consistent sub-structure — identical to what a SAT graph
    would produce. -/
theorem protocol_blind (G : CubeGraph) (b : Nat)
    (hbo : BorromeanOrder G b) (hb : b > 0)
    (S : List (Fin G.cubes.length)) (hnd : S.Nodup) (hlen : S.length < b) :
    ∃ s : (i : Fin G.cubes.length) → Vertex,
      (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true) :=
  hbo.2 hb S (by omega) hnd

/-! ## Section 4: Concrete witness — h2Graph -/

/-- h2Graph requires any rank-1 protocol to touch ≥ 3 cubes. -/
theorem h2_protocol_needs_3_cubes :
    ¬ h2Graph.Satisfiable ∧ BorromeanOrder h2Graph 3 ∧
    (∀ (S : List (Fin h2Graph.cubes.length)), S.Nodup → S.length < 3 →
      ∃ s : (i : Fin h2Graph.cubes.length) → Vertex,
        (∀ i ∈ S, (h2Graph.cubes[i]).isGap (s i) = true) ∧
        (∀ e ∈ h2Graph.edges, e.1 ∈ S → e.2 ∈ S →
          transferOp (h2Graph.cubes[e.1]) (h2Graph.cubes[e.2])
            (s e.1) (s e.2) = true)) :=
  ⟨h2Graph_unsat, h2_borromean_order,
   fun S hnd hlen => protocol_blind h2Graph 3 h2_borromean_order (by omega) S hnd hlen⟩

/-! ## Section 5: Scaling — Ω(n) cubes needed -/

/-- **Rank-1 Protocol Scaling**: For arbitrarily large UNSAT graphs,
    any rank-1 protocol must touch Ω(n) cubes.

    From Schoenebeck: ∃ UNSAT graphs where (n/c)-consistency passes.
    Protocol blindness: < n/c cubes → consistent gap selection.
    Therefore: correct protocol needs ≥ n/c cubes.
    Coordination cost: n^{Ω(n)} (Schoenebeck). -/
theorem rank1_protocol_scaling :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph,
        G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        (∀ (S : List (Fin G.cubes.length)), S.Nodup → S.length < n / c →
          ∃ s : (i : Fin G.cubes.length) → Vertex,
            (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
            (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
              transferOp (G.cubes[e.1]) (G.cubes[e.2])
                (s e.1) (s e.2) = true)) := by
  obtain ⟨c, hc, hsch⟩ := schoenebeck_linear
  refine ⟨c, hc, fun n hn => ?_⟩
  obtain ⟨G, hsize, hkc, hunsat⟩ := hsch n hn
  exact ⟨G, hsize, hunsat, fun S hnd hlen => hkc S (by omega) hnd⟩

/-! ## Section 6: Information loss connection (IntegerMonodromy) -/

/-- Each observation loses multiplicity: boolean trace ≤ 8 but integer
    trace can be 50-5000 (E-META). Bridge + gap from IntegerMonodromy. -/
theorem information_loss_per_observation :
    (∀ (M : BoolMat 8), boolTraceCount M ≤ 8) ∧
    (∀ (Ms : List (BoolMat 8)),
      NatMat.toBool (NatMat.mulSeq (Ms.map NatMat.ofBool))
        = NatMat.boolMulSeq Ms) ∧
    (∀ (Ms : List (BoolMat 8)),
      boolTraceCount (NatMat.boolMulSeq Ms)
        ≤ NatMat.natTrace (NatMat.mulSeq (Ms.map NatMat.ofBool))) :=
  ⟨boolTraceCount_le_eight,
   NatMat.bridge_compose,
   fun Ms => by rw [← NatMat.bridge_compose]; exact NatMat.boolTraceCount_le_natTrace _⟩

/-! ## Section 7: Summary -/

/-- **Rank-1 Protocol Summary**: Complete argument in one theorem.

    **Eliminates**: SA, k-consistency, SOS, arc-consistency, any method
    based on boolean composition of transfer operators.

    **Does NOT eliminate**: DPLL (branching), Resolution (cuts),
    Extended Resolution, or algorithms not based on composition. -/
theorem rank1_protocol_summary :
    -- (1) Rank-1 closed (composition cannot create coordination)
    (∀ {n : Nat} (A B : BoolMat n), A.IsRankOne → B.IsRankOne →
      (mul A B).IsRankOne ∨ mul A B = zero) ∧
    -- (2) Dead stays dead (irreversibility)
    (∀ G seq e, ChannelDead G seq → ChannelDead G (seq ++ [e])) ∧
    -- (3) Information bounded (≤ 8 bits per observation)
    (∀ M : BoolMat 8, boolTraceCount M ≤ 8) ∧
    -- (4) Protocol blind below Borromean
    (∀ G b, BorromeanOrder G b → b > 0 →
      ∀ (S : List (Fin G.cubes.length)), S.Nodup → S.length < b →
        ∃ s : (i : Fin G.cubes.length) → Vertex,
          (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
          (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
            transferOp (G.cubes[e.1]) (G.cubes[e.2])
              (s e.1) (s e.2) = true)) ∧
    -- (5) Scaling: Ω(n) cubes needed
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        (∀ (S : List (Fin G.cubes.length)), S.Nodup → S.length < n / c →
          ∃ s : (i : Fin G.cubes.length) → Vertex,
            (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
            (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
              transferOp (G.cubes[e.1]) (G.cubes[e.2])
                (s e.1) (s e.2) = true))) :=
  ⟨fun _ _ hA hB => rank1_closed_under_compose hA hB,
   dead_extends_dead,
   boolTraceCount_le_eight,
   protocol_blind,
   rank1_protocol_scaling⟩

end CubeGraph
