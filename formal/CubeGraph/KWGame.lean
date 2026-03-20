/-
  CubeGraph/KWGame.lean

  Karchmer-Wigderson game and False Clause Search for CubeGraph SAT.

  See: LiftingTheorem.lean (lifting chain, depth Ω(n/log n))
  See: QueryLowerBound.lean (DT ≥ Ω(n))
  See: experiments-ml/024/PAS3D-PLAN-KW-GAME.md
  Extern: Karchmer-Wigderson (1990), Ben-Sasson-Wigderson (2001)
-/

import CubeGraph.LiftingTheorem

namespace CubeGraph

/-! ## Section 1: Helper — extracting witness from negated universal on list -/

/-- If not all elements satisfy p, some element doesn't. -/
private theorem exists_not_of_not_forall_mem {α : Type} {p : α → Prop}
    [inst : DecidablePred p] {l : List α}
    (h : ¬ ∀ x ∈ l, p x) : ∃ x ∈ l, ¬ p x := by
  induction l with
  | nil => exact absurd (fun _ hx => nomatch hx) h
  | cons a t ih =>
    by_cases ha : p a
    · have ht : ¬ ∀ x ∈ t, p x := by
        intro hall
        exact h fun x hx => by
          cases hx with
          | head => exact ha
          | tail _ hxt => exact hall x hxt
      obtain ⟨x, hx, hpx⟩ := ih ht
      exact ⟨x, .tail a hx, hpx⟩
    · exact ⟨a, .head t, ha⟩

/-! ## Section 2: False Clause Search -/

/-- **False Clause Search**: an edge where the assignment is incompatible. -/
def HasViolation (G : CubeGraph) (σ : GapSelection G) : Prop :=
  ∃ e ∈ G.edges, transferOp (G.cubes[e.1]) (G.cubes[e.2]) (σ e.1) (σ e.2) = false

/-- On UNSAT graphs, every valid gap assignment has a violation. -/
theorem unsat_valid_implies_violation (G : CubeGraph) (hunsat : ¬ G.Satisfiable)
    (σ : GapSelection G) (hv : validSelection G σ) :
    HasViolation G σ := by
  by_cases hc : compatibleSelection G σ
  · exact absurd ⟨σ, hv, hc⟩ hunsat
  · -- ¬compatible → ∃ violated edge
    unfold compatibleSelection at hc
    have ⟨e, he, hne⟩ := exists_not_of_not_forall_mem hc
    refine ⟨e, he, ?_⟩
    cases htf : transferOp (G.cubes[e.1]) (G.cubes[e.2]) (σ e.1) (σ e.2)
    · rfl
    · exact absurd htf (by simp_all)

/-- Every assignment on UNSAT is either invalid or has violation. -/
theorem unsat_implies_search (G : CubeGraph) (hunsat : ¬ G.Satisfiable)
    (σ : GapSelection G) :
    ¬ validSelection G σ ∨ HasViolation G σ := by
  by_cases hv : validSelection G σ
  · exact Or.inr (unsat_valid_implies_violation G hunsat σ hv)
  · exact Or.inl hv

/-! ## Section 3: KW Pair -/

/-- **KW Pair**: Alice (UNSAT) vs Bob (SAT). -/
structure KWPair where
  alice : CubeGraph
  bob : CubeGraph
  alice_unsat : ¬ alice.Satisfiable
  bob_sat : bob.Satisfiable

/-- KW asymmetry: Alice always has violations, Bob has none. -/
theorem kw_asymmetry (kw : KWPair) :
    (∀ σ : GapSelection kw.alice, validSelection kw.alice σ →
      HasViolation kw.alice σ)
    ∧ (∃ σ : GapSelection kw.bob, validSelection kw.bob σ ∧
        compatibleSelection kw.bob σ) := by
  exact ⟨fun σ hv => unsat_valid_implies_violation kw.alice kw.alice_unsat σ hv,
         kw.bob_sat⟩

/-! ## Section 4: Search blindness below Borromean -/

/-- **Search Blindness**: On UNSAT with Borromean order b,
    any < b cubes have consistent gap selection (no local violation).
    Search query complexity ≥ b(n) = Ω(n). -/
theorem search_blind (G : CubeGraph) (b : Nat)
    (hbo : BorromeanOrder G b) (hb : b > 0)
    (S : List (Fin G.cubes.length)) (hnd : S.Nodup) (hlen : S.length < b) :
    ∃ s : (i : Fin G.cubes.length) → Vertex,
      (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true) :=
  protocol_blind G b hbo hb S hnd hlen

/-! ## Section 5: Complete summary -/

/-- **KW Game Summary**: Search + Blind + DT + CSP + Info gap. -/
theorem kw_game_summary :
    -- (1) Search: UNSAT + valid → violation
    (∀ G : CubeGraph, ¬ G.Satisfiable →
      ∀ σ : GapSelection G, validSelection G σ → HasViolation G σ)
    -- (2) Blind: sub-Borromean → consistent
    ∧ (∀ G b, BorromeanOrder G b → b > 0 →
        ∀ (S : List (Fin G.cubes.length)), S.Nodup → S.length < b →
          ∃ s : (i : Fin G.cubes.length) → Vertex,
            (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
            (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
              transferOp (G.cubes[e.1]) (G.cubes[e.2])
                (s e.1) (s e.2) = true))
    -- (3) DT ≥ Ω(n)
    ∧ (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
        ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
          ∀ (S : List (Fin G.cubes.length)), S.Nodup → S.length < n / c →
            ∃ s : (i : Fin G.cubes.length) → Vertex,
              (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
              (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
                transferOp (G.cubes[e.1]) (G.cubes[e.2])
                  (s e.1) (s e.2) = true))
    -- (4) CSP decomposition
    ∧ (∀ G : CubeGraph,
        satWithMasks G (fun i => (G.cubes[i]).gapMask) (fun i => (G.cubes[i]).gaps_nonempty)
        ↔ G.Satisfiable) :=
  ⟨unsat_valid_implies_violation,
   protocol_blind,
   decision_tree_depth_scaling,
   satWithMasks_original⟩

end CubeGraph
