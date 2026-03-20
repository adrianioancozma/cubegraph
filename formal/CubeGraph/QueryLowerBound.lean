/-
  CubeGraph/QueryLowerBound.lean

  Query complexity lower bound for CubeGraph SAT.

  An adaptive query algorithm inspects cubes (learning gap masks).
  To decide SAT/UNSAT, it must inspect ≥ b(n) = Ω(n) cubes.

  This is the "f" side of GPW lifting: DT(CubeGraphSAT) = Ω(n).

  See: Rank1Protocol.lean (protocol_blind, rank1_protocol_scaling)
  See: InformationChannel.lean (BorromeanOrder, blind_below_borromean)
  See: experiments-ml/024/PAS3C-PLAN-LIFTING.md
-/

import CubeGraph.QuantitativeGap

namespace CubeGraph

/-! ## Section 1: Query blindness -/

/-- **Query Blindness**: An algorithm inspecting fewer than b cubes
    on a graph with Borromean order b cannot distinguish SAT from UNSAT.

    The inspected cubes always admit a consistent gap selection
    (from KConsistent G (b-1)). This is protocol_blind in query language.

    DT(CubeGraphSAT) ≥ b(n). -/
theorem query_blind (G : CubeGraph) (b : Nat)
    (hbo : BorromeanOrder G b) (hb : b > 0)
    (S : List (Fin G.cubes.length)) (hnd : S.Nodup) (hlen : S.length < b) :
    ∃ s : (i : Fin G.cubes.length) → Vertex,
      (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true) :=
  protocol_blind G b hbo hb S hnd hlen

/-! ## Section 2: Concrete witness -/

/-- h2Graph: any query algorithm must inspect ≥ 3 cubes. -/
theorem h2_query_depth_ge_3 :
    ¬ h2Graph.Satisfiable ∧ BorromeanOrder h2Graph 3 ∧
    (∀ (S : List (Fin h2Graph.cubes.length)), S.Nodup → S.length < 3 →
      ∃ s : (i : Fin h2Graph.cubes.length) → Vertex,
        (∀ i ∈ S, (h2Graph.cubes[i]).isGap (s i) = true) ∧
        (∀ e ∈ h2Graph.edges, e.1 ∈ S → e.2 ∈ S →
          transferOp (h2Graph.cubes[e.1]) (h2Graph.cubes[e.2])
            (s e.1) (s e.2) = true)) :=
  h2_protocol_needs_3_cubes

/-! ## Section 3: Decision tree depth scaling -/

/-- **DT(CubeGraphSAT) ≥ Ω(n)**: For arbitrarily large UNSAT graphs,
    any correct query algorithm must inspect Ω(n) cubes.

    This is the input for GPW lifting:
    DT(f) = Ω(n) → CC(f ∘ g^n) = Ω(n log n) → monotone depth Ω(n/log n). -/
theorem decision_tree_depth_scaling :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph,
        G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        (∀ (S : List (Fin G.cubes.length)), S.Nodup → S.length < n / c →
          ∃ s : (i : Fin G.cubes.length) → Vertex,
            (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
            (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
              transferOp (G.cubes[e.1]) (G.cubes[e.2])
                (s e.1) (s e.2) = true)) :=
  rank1_protocol_scaling

/-! ## Section 4: Information per query + summary -/

/-- **Query Lower Bound Summary**: Unifies DT scaling + information bounds.

    (1) DT ≥ Ω(n): must inspect Ω(n) cubes
    (2) Each inspection: ≤ 8 bits (gap mask)
    (3) Rank-1 closed: composition cannot coordinate
    (4) Dead stays dead: information loss is permanent
    (5) Boolean ≤ Integer: multiplicities lost per composition

    **Eliminates**: Any adaptive gap-query algorithm with sub-linear queries.
    **Provides DT(f) for lifting**: CC(f ∘ g^n) ≥ Ω(n log n) [GPW axiom]. -/
theorem query_lower_bound_summary :
    -- (1) DT ≥ Ω(n)
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ (S : List (Fin G.cubes.length)), S.Nodup → S.length < n / c →
          ∃ s : (i : Fin G.cubes.length) → Vertex,
            (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
            (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
              transferOp (G.cubes[e.1]) (G.cubes[e.2])
                (s e.1) (s e.2) = true))
    -- (2) Per query: ≤ 8 bits
    ∧ (∀ M : BoolMat 8, NatMat.boolTraceCount M ≤ 8)
    -- (3) Rank-1 closed
    ∧ (∀ {n : Nat} (A B : BoolMat n), A.IsRankOne → B.IsRankOne →
        (BoolMat.mul A B).IsRankOne ∨ BoolMat.mul A B = BoolMat.zero)
    -- (4) Dead stays dead
    ∧ (∀ G seq e, ChannelDead G seq → ChannelDead G (seq ++ [e]))
    -- (5) Boolean ≤ Integer per composition
    ∧ (∀ Ms : List (BoolMat 8),
        NatMat.boolTraceCount (NatMat.boolMulSeq Ms)
          ≤ NatMat.natTrace (NatMat.mulSeq (Ms.map NatMat.ofBool))) :=
  ⟨rank1_protocol_scaling,
   boolTraceCount_le_eight,
   fun _ _ hA hB => rank1_closed_under_compose hA hB,
   dead_extends_dead,
   fun Ms => by rw [← NatMat.bridge_compose]; exact NatMat.boolTraceCount_le_natTrace _⟩

end CubeGraph
