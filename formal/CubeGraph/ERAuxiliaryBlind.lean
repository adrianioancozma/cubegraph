/-
  CubeGraph/ERAuxiliaryBlind.lean — F1.3

  Extended Resolution auxiliary variables are individually blind.

  6 theorems showing that ER auxiliary variables, taken individually or in
  pairs or chains, cannot extract information about SAT/UNSAT:

  T1: er_variable_blind     — 1 auxiliary variable is blind (1 cube < b)
  T2: er_pair_blind          — any pair is blind (2 cubes < b, needs b ≥ 3)
  T3: er_sublinear_blind     — any sublinear set of ORIGINAL cubes is blind under ER
  T4: or_correlation_rank1   — pairwise OR/AND correlation is rank-1
  T5: er_chain_blind         — chain of k rank-1 operators → rank-1 or zero
  T6: er_not_invertible      — OR + rank-1 + transfer are non-invertible

  WHAT THIS DOES NOT PROVE: that a COLLECTION of poly(n) auxiliary variables
  is blind. Collections might contain information through CORRELATIONS,
  even though individuals are blind. This is the gap (Phase 3).

  EXPLICIT LIMIT: T5 covers CHAINS (sequential composition) but NOT
  NETWORKS (graphs with cycles). Networks with cycles can create rank-0
  (UNSAT) — exactly the original problem at the meta-level.
  See: FIXED-POINT-ARGUMENT.md

  0 sorry. 0 new axioms.

  See: experiments-ml/025_2026-03-19_synthesis/bridge/F1.3-PLAN-ER-AUXILIARY.md
  See: experiments-ml/025_2026-03-19_synthesis/bridge/AUXILIARY-VARIABLES-CANNOT-HELP.md
  See: experiments-ml/025_2026-03-19_synthesis/bridge/FIXED-POINT-ARGUMENT.md
-/

import CubeGraph.SublinearER
import CubeGraph.InformationChannel
import CubeGraph.InvertibilityBarrier
import CubeGraph.Rank1Bubbles

namespace CubeGraph

open BoolMat

/-! ## Section 1: Individual Blindness -/

/-- **ER Variable Blind**: in a CubeGraph with Borromean order b ≥ 2,
    any subset of ≤ 1 cube is consistent (blind to SAT/UNSAT).

    Interpretation: one ER auxiliary variable affects at most 1 new cube.
    Examining 1 cube < b does not distinguish SAT from UNSAT. -/
theorem er_variable_blind (G : CubeGraph) (b : Nat)
    (hbo : BorromeanOrder G b) (hb : b ≥ 2)
    (S : List (Fin G.cubes.length)) (hlen : S.length ≤ 1) (hnd : S.Nodup) :
    ∃ s : (i : Fin G.cubes.length) → Vertex,
      (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true) :=
  blind_below_borromean G b hbo (by omega) S (by omega) hnd

/-- **ER Pair Blind**: in a CubeGraph with Borromean order b ≥ 3,
    any subset of ≤ 2 cubes is consistent (blind).

    On h2Graph: b = 3, so any 2 cubes are blind. The third cube is
    where the twist lives — but you can't see it from 2 cubes. -/
theorem er_pair_blind (G : CubeGraph) (b : Nat)
    (hbo : BorromeanOrder G b) (hb : b ≥ 3)
    (S : List (Fin G.cubes.length)) (hlen : S.length ≤ 2) (hnd : S.Nodup) :
    ∃ s : (i : Fin G.cubes.length) → Vertex,
      (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true) :=
  blind_below_borromean G b hbo (by omega) S (by omega) hnd

/-! ## Section 2: Sublinear Blindness on Originals under ER -/

/-- **ER Sublinear Blind**: after ER extension, any sublinear subset
    of ORIGINAL cubes remains blind.

    Chain: Schoenebeck (UNSAT with (n/c)-consistency passing) +
    er_kconsistent_on_originals (ER preserves consistency on originals)
    → sublinear subsets of originals are blind under any ER extension.

    This does NOT say that NEW cubes (with auxiliary variables) are blind.
    That is the gap — see Phase 3 in PLAN.md. -/
theorem er_sublinear_blind :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ (ext : ERExtension G),
          ∀ (S : List (Fin G.cubes.length)), S.length ≤ n / c → S.Nodup →
            ∃ s : (i : Fin G.cubes.length) → Vertex,
              (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
              (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
                transferOp (G.cubes[e.1]) (G.cubes[e.2])
                  (s e.1) (s e.2) = true) := by
  obtain ⟨c, hc, hsch⟩ := schoenebeck_linear
  exact ⟨c, hc, fun n hn => by
    obtain ⟨G, hsize, hkc, hunsat⟩ := hsch n hn
    exact ⟨G, hsize, hunsat, fun ext S hlen hnd =>
      er_kconsistent_on_originals G ext (n / c) hkc S hlen hnd⟩⟩

/-! ## Section 3: Pairwise Correlation and Chain Composition -/

/-- **OR Correlation Rank-1**: composing two rank-1 operators through
    OR/AND yields rank-1 or zero. Pairwise correlation through boolean
    composition cannot create rank ≥ 2 (coordination).

    Renamed `rank1_closed_under_compose` for the ER context. -/
theorem or_correlation_rank1 {n : Nat} (A B : BoolMat n)
    (hA : A.IsRankOne) (hB : B.IsRankOne) :
    (BoolMat.mul A B).IsRankOne ∨ BoolMat.mul A B = BoolMat.zero :=
  rank1_closed_under_compose hA hB

/-- **ER Chain Blind**: a chain of k rank-1 operators composed
    sequentially yields rank-1 or zero. Never rank ≥ 2.

    CRITICAL LIMIT: this covers CHAINS (sequential composition on paths)
    but NOT NETWORKS (graphs with cycles and junctions).
    On networks with cycles, rank-1 × rank-1 × ... CAN produce rank-0
    (UNSAT) — this is experiment 001. Networks recreate the original
    SAT problem at meta-level. See FIXED-POINT-ARGUMENT.md. -/
theorem er_chain_blind {n : Nat} (Ms : List (BoolMat n)) (acc : BoolMat n)
    (hacc : acc.IsRankOne ∨ acc = BoolMat.zero)
    (hMs : ∀ M ∈ Ms, M.IsRankOne) :
    (Ms.foldl BoolMat.mul acc).IsRankOne ∨
      Ms.foldl BoolMat.mul acc = BoolMat.zero :=
  rank1_foldl_preserves Ms acc hacc hMs

/-! ## Section 4: Non-Invertibility -/

/-- **ER Not Invertible**: OR has no inverse, rank-1 boolean matrices
    have no inverse, transfer operators rank-1 have no inverse.

    Consequence: ER auxiliary variables defined through OR/AND cannot
    "undo" the effect of existing clauses. Information lost through
    OR (1||x = 1) cannot be recovered.

    Contrast with XOR: on Tseitin, carry bits (XOR) ARE invertible,
    so ER is polynomial. On 3-SAT (OR), non-invertibility forbids
    carry bits → ER exponential (conjectured). -/
theorem er_not_invertible :
    -- (1) OR has no inverse
    (¬ ∃ x : Bool, (true || x) = false)
    -- (2) Rank-1 boolean matrices non-invertible (n ≥ 2)
    ∧ (∀ (M : BoolMat 8), M.IsRankOne →
        ¬ ∃ M' : BoolMat 8, BoolMat.mul M M' = BoolMat.one)
    -- (3) Transfer operators rank-1 non-invertible
    ∧ (∀ (c₁ c₂ : Cube), (transferOp c₁ c₂).IsRankOne →
        ¬ ∃ M' : BoolMat 8, BoolMat.mul (transferOp c₁ c₂) M' = BoolMat.one) :=
  ⟨or_no_inverse,
   fun M hM => rank1_not_bool_invertible (by omega) M hM,
   transferOp_rank1_not_invertible⟩

/-! ## Section 5: Summary -/

/-- **ER Auxiliary Summary**: all 6 properties combined.

    WHAT IS PROVEN:
    (1-2) Individual/pair auxiliary variables are blind (Borromean)
    (3) Sublinear sets of original cubes blind under ER (Schoenebeck + ER)
    (4) Pairwise correlation rank-1 (composition closed)
    (5) Chain composition rank-1 (sequential = rank-1 or zero)
    (6) Non-invertible (OR, rank-1, transfer operators)

    WHAT IS NOT PROVEN (= the gap):
    - A COLLECTION of poly(n) auxiliary variables might contain info
      through correlations, even if each is individually blind.
    - Network (cyclic) composition CAN create rank-0 from rank-1.
    - This is EXACTLY the original problem at the meta-level.
    - See FIXED-POINT-ARGUMENT.md for the structural fixed point analysis. -/
theorem er_auxiliary_summary :
    -- (1) Single variable blind (b ≥ 2)
    (∀ G b, BorromeanOrder G b → b ≥ 2 →
      ∀ S : List (Fin G.cubes.length), S.length ≤ 1 → S.Nodup →
        ∃ s : (i : Fin G.cubes.length) → Vertex,
          (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
          (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
            transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true))
    -- (2) Pair blind (b ≥ 3)
    ∧ (∀ G b, BorromeanOrder G b → b ≥ 3 →
        ∀ S : List (Fin G.cubes.length), S.length ≤ 2 → S.Nodup →
          ∃ s : (i : Fin G.cubes.length) → Vertex,
            (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
            (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
              transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true))
    -- (3) Pairwise correlation rank-1
    ∧ (∀ {n : Nat} (A B : BoolMat n), A.IsRankOne → B.IsRankOne →
        (BoolMat.mul A B).IsRankOne ∨ BoolMat.mul A B = BoolMat.zero)
    -- (4) Chain rank-1 or zero
    ∧ (∀ {n : Nat} (Ms : List (BoolMat n)) (acc : BoolMat n),
        (acc.IsRankOne ∨ acc = BoolMat.zero) →
        (∀ M ∈ Ms, M.IsRankOne) →
        (Ms.foldl BoolMat.mul acc).IsRankOne ∨
          Ms.foldl BoolMat.mul acc = BoolMat.zero)
    -- (5) Non-invertible
    ∧ ((¬ ∃ x : Bool, (true || x) = false) ∧
       (∀ M : BoolMat 8, M.IsRankOne →
         ¬ ∃ M' : BoolMat 8, BoolMat.mul M M' = BoolMat.one) ∧
       (∀ c₁ c₂ : Cube, (transferOp c₁ c₂).IsRankOne →
         ¬ ∃ M' : BoolMat 8, BoolMat.mul (transferOp c₁ c₂) M' = BoolMat.one)) :=
  ⟨er_variable_blind,
   er_pair_blind,
   fun _ _ hA hB => or_correlation_rank1 _ _ hA hB,
   fun Ms acc hacc hMs => er_chain_blind Ms acc hacc hMs,
   er_not_invertible⟩

end CubeGraph
