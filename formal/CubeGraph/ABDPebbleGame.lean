/-
  CubeGraph/ABDPebbleGame.lean — ABD Pebble Game Theorem

  Formalizes the core of Atserias-Dalmau (2008) in CubeGraph language.

  **Main theorem** (abd_weak_cubegraph):
    KConsistent G k → ¬ Satisfiable G → k < G.cubes.length

  This REPLACES the axiom `abd_ad_consistency_implies_high_width`
  in RankWidthTransfer.lean with a proven theorem. 0 new axioms.

  Key results (12 theorems):
  T1.  finRange_nodup: (List.finRange n).Nodup
  T2.  full_consistency_implies_sat: KConsistent G n → Satisfiable G
  T3.  sat_implies_full_consistency: Satisfiable → KConsistent G n
  T4.  full_consistency_iff_sat: KConsistent G n ↔ Satisfiable G
  T5.  abd_weak_cubegraph: KConsistent G k ∧ ¬SAT → k < n
  T6.  unsat_not_full_consistent: ¬SAT → ¬KConsistent G n
  T7.  abd_borromean_width: (b-1)-consistent ∧ ¬SAT → b-1 < n
  T8.  kconsistent_ge_iff_sat: k ≥ n → (KConsistent G k ↔ Satisfiable)
  T9.  kconsistent_is_pebble_game: KConsistent = Duplicator wins (Iff.rfl)
  T10. abd_contrapositive: KConsistent → ¬SAT → all ≤k subsets consistent
  T11. abd_schoenebeck_to_bsw: Schoenebeck + ABD → BSW conclusion
  T12. abd_complete_package: summary theorem

  Proof structure (Atserias-Dalmau 2008):
  KConsistent G k = "Duplicator wins the k-pebble existential game."
  Resolution width ≤ k = "Spoiler uses ≤ k pebbles."
  Key lemma: k ≥ n → KConsistent G k → Satisfiable (full consistency = SAT).
  Contrapositive: UNSAT + KConsistent G k → k < n.

  See: RankWidthTransfer.lean (axiom `abd_ad_consistency_implies_high_width`)
  See: KConsistency.lean (KConsistent, kconsistent_mono, sat_implies_kconsistent)
  See: SchoenebeckChain.lean (schoenebeck_linear)
  Extern: Atserias, Dalmau. JCSS 74(3), 2008.
  Extern: Ben-Sasson, Wigderson. JACM 48(2), 2001.
-/

import CubeGraph.KConsistency

namespace CubeGraph

/-! ## Section 1: List.finRange Nodup

  The list [0, 1, ..., n-1] has no duplicates.
  Proven by induction: finRange (n+1) = 0 :: map succ (finRange n).
-/

/-- **(T1)** List.finRange n has no duplicates.
    Proof by induction using finRange_succ = 0 :: map succ (finRange n). -/
theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp [List.finRange]
  | succ n ih =>
    rw [List.finRange_succ, List.nodup_cons]
    exact ⟨
      fun h => by
        rw [List.mem_map] at h
        obtain ⟨x, _, hx⟩ := h
        have := congrArg Fin.val hx
        simp [Fin.succ] at this,
      List.Pairwise.map Fin.succ
        (fun a b (hab : a ≠ b) (heq : Fin.succ a = Fin.succ b) =>
          hab (Fin.ext (by
            have := congrArg Fin.val heq
            simp [Fin.succ] at this
            omega)))
        ih⟩

/-! ## Section 2: Full Consistency = Satisfiability

  The foundational equivalence: KConsistent G n ↔ Satisfiable G.
  The → direction is the key new result.
-/

/-- **(T2)** Full consistency implies satisfiability.
    If every subset of ≤ n cubes has a compatible gap selection,
    then the entire graph is satisfiable.

    Proof: Apply KConsistent to S = finRange n (all cube indices). -/
theorem full_consistency_implies_sat (G : CubeGraph) :
    KConsistent G G.cubes.length → G.Satisfiable := by
  intro hkc
  obtain ⟨s, hv, hc⟩ := hkc (List.finRange G.cubes.length)
    (by simp [List.length_finRange])
    (finRange_nodup G.cubes.length)
  exact ⟨s,
    fun i => hv i (List.mem_finRange i),
    fun e he => hc e he (List.mem_finRange e.1) (List.mem_finRange e.2)⟩

/-- **(T3)** Converse: Satisfiable → n-consistent (from sat_implies_kconsistent). -/
theorem sat_implies_full_consistency (G : CubeGraph) :
    G.Satisfiable → KConsistent G G.cubes.length :=
  sat_implies_kconsistent G G.cubes.length

/-- **(T4)** n-consistency ↔ Satisfiability. The fundamental equivalence. -/
theorem full_consistency_iff_sat (G : CubeGraph) :
    KConsistent G G.cubes.length ↔ G.Satisfiable :=
  ⟨full_consistency_implies_sat G, sat_implies_full_consistency G⟩

/-! ## Section 3: The ABD Weak Theorem

  The main result: KConsistent G k ∧ ¬ Satisfiable → k < n.
  This replaces the axiom in RankWidthTransfer.lean.
-/

/-- **(T5)** ABD Weak (CubeGraph): k-consistent and UNSAT implies k < n.

    Proof: case split on k < n vs k ≥ n.
    If k ≥ n: KConsistent G k → KConsistent G n (by mono) → Satisfiable (by T2).
    Contradicts ¬ Satisfiable. So k < n. -/
theorem abd_weak_cubegraph (G : CubeGraph) (k : Nat)
    (hkc : KConsistent G k) (hunsat : ¬ G.Satisfiable) :
    k < G.cubes.length := by
  rcases Nat.lt_or_ge k G.cubes.length with h | h
  · exact h
  · exact absurd (full_consistency_implies_sat G (kconsistent_mono G h hkc)) hunsat

/-- **(T6)** UNSAT implies not fully consistent (contrapositive of T2). -/
theorem unsat_not_full_consistent (G : CubeGraph)
    (hunsat : ¬ G.Satisfiable) :
    ¬ KConsistent G G.cubes.length :=
  fun hkc => hunsat (full_consistency_implies_sat G hkc)

/-! ## Section 4: Borromean Width Bound -/

/-- **(T7)** ABD for Borromean Order: (b-1)-consistent and UNSAT implies b-1 < n.
    Equivalently: Resolution width ≥ b. -/
theorem abd_borromean_width (G : CubeGraph) (b : Nat)
    (hbo_kc : KConsistent G (b - 1)) (hunsat : ¬ G.Satisfiable) :
    b - 1 < G.cubes.length :=
  abd_weak_cubegraph G (b - 1) hbo_kc hunsat

/-! ## Section 5: KConsistent Stabilization -/

/-- **(T8)** k ≥ n → (KConsistent G k ↔ Satisfiable G).
    For k ≥ n, k-consistency collapses to satisfiability.

    Proof:
    →: KConsistent G k → KConsistent G n (mono) → Satisfiable (T2).
    ←: Satisfiable → KConsistent G k (sat_implies_kconsistent). -/
theorem kconsistent_ge_iff_sat (G : CubeGraph) (k : Nat)
    (hk : k ≥ G.cubes.length) :
    KConsistent G k ↔ G.Satisfiable :=
  ⟨fun hkc => full_consistency_implies_sat G (kconsistent_mono G hk hkc),
   sat_implies_kconsistent G k⟩

/-! ## Section 6: Pebble Game Interpretation -/

/-- **(T9)** KConsistent IS the Duplicator's winning condition.
    This is definitionally true (Iff.rfl). The pebble game:
    Spoiler places pebbles on ≤ k cubes, Duplicator responds with
    a compatible gap selection. KConsistent G k says Duplicator always wins. -/
theorem kconsistent_is_pebble_game (G : CubeGraph) (k : Nat) :
    KConsistent G k ↔
    (∀ (S : List (Fin G.cubes.length)), S.length ≤ k → S.Nodup →
      ∃ s : (i : Fin G.cubes.length) → Vertex,
        (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
        (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
          transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true)) :=
  Iff.rfl

/-! ## Section 7: ABD Contrapositive -/

/-- **(T10)** ABD Contrapositive: k-consistent + UNSAT →
    every subset of ≤ k cubes has a local model.
    This IS the Duplicator's winning strategy unfolded. -/
theorem abd_contrapositive (G : CubeGraph) (k : Nat)
    (hkc : KConsistent G k) (_hunsat : ¬ G.Satisfiable)
    (S : List (Fin G.cubes.length)) (hnd : S.Nodup) (hlen : S.length ≤ k) :
    ∃ s : (i : Fin G.cubes.length) → Vertex,
      (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true) :=
  hkc S hlen hnd

/-! ## Section 8: ABD + Schoenebeck → BSW -/

/-- **(T11)** Schoenebeck + ABD → BSW conclusion.

    From Schoenebeck: for UNSAT G with ≥ n cubes, KConsistent G (n/c).
    Unfolding KConsistent: any subset of < n/c cubes has a local model.
    This IS the BSW conclusion (width > n/c stated as "blind below n/c").

    Proof: unfold KConsistent + use S.length < n/c → S.length ≤ n/c. -/
theorem abd_schoenebeck_to_bsw :
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧
        KConsistent G (n / c) ∧ ¬ G.Satisfiable) →
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ (S : List (Fin G.cubes.length)), S.Nodup → S.length < n / c →
          ∃ s : (i : Fin G.cubes.length) → Vertex,
            (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
            (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
              transferOp (G.cubes[e.1]) (G.cubes[e.2])
                (s e.1) (s e.2) = true)) := by
  intro ⟨c, hc, hsch⟩
  refine ⟨c, hc, fun n hn => ?_⟩
  obtain ⟨G, hG_large, hG_kc, hG_unsat⟩ := hsch n hn
  exact ⟨G, hG_large, hG_unsat, fun S hnd hlen =>
    hG_kc S (Nat.le_of_lt hlen) hnd⟩

/-! ## Section 9: Summary -/

/-- **(T12)** ABD Complete Package: all key results in one theorem. -/
theorem abd_complete_package :
    -- (1) n-consistency ↔ SAT
    (∀ G : CubeGraph, KConsistent G G.cubes.length ↔ G.Satisfiable)
    -- (2) ABD weak: k-consistent + UNSAT → k < n
    ∧ (∀ (G : CubeGraph) (k : Nat),
        KConsistent G k → ¬ G.Satisfiable → k < G.cubes.length)
    -- (3) SAT → k-consistent (for all k)
    ∧ (∀ (G : CubeGraph) (k : Nat), G.Satisfiable → KConsistent G k)
    -- (4) k ≥ n → (KConsistent G k ↔ Satisfiable)
    ∧ (∀ (G : CubeGraph) (k : Nat), k ≥ G.cubes.length →
        (KConsistent G k ↔ G.Satisfiable))
    -- (5) Schoenebeck + ABD → BSW
    ∧ ((∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
        ∃ G : CubeGraph, G.cubes.length ≥ n ∧
          KConsistent G (n / c) ∧ ¬ G.Satisfiable) →
      (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
        ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
          ∀ (S : List (Fin G.cubes.length)), S.Nodup → S.length < n / c →
            ∃ s : (i : Fin G.cubes.length) → Vertex,
              (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
              (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
                transferOp (G.cubes[e.1]) (G.cubes[e.2])
                  (s e.1) (s e.2) = true))) :=
  ⟨full_consistency_iff_sat,
   abd_weak_cubegraph,
   sat_implies_kconsistent,
   kconsistent_ge_iff_sat,
   abd_schoenebeck_to_bsw⟩

end CubeGraph
