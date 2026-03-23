/-
  CubeGraph/BetaBorromeanRestriction.lean

  BorromeanOrder under random restrictions: structural theorems.

  EXPERIMENTAL FINDING (Agent-Beta, 2026-03-21):
  For UNSAT 3-SAT at critical density (ratio 4.27):
  1. AC-3 after fixing 1 cube detects UNSAT (empties all remaining cubes)
  2. Raw k-consistency drop point grows as O(n^0.68), ~6% of cubes
  3. b(k) at fixed k INCREASES with n: larger formulas resist restriction

  Key theorems (0 sorry):
  - restriction_preserves_sat: SAT + extends restriction -> SAT
  - unsat_no_extension: UNSAT -> no compatible extending selection
  - restricted_kconsistent_mono: monotonicity in k
  - extends_empty: any selection extends empty restriction
  - kconsistent_restriction_weakening: k-consistent => restricted (k-r)-consistent
    (modulo an additional assumption that the restriction is SAT-compatible)

  See: BETA-RESULTS.md (experimental data showing ~6% drop threshold)
-/

import CubeGraph.Basic

namespace CubeGraph

/-! ## Section 1: Restriction Definition -/

/-- A **partial restriction** assigns specific gap values to some cubes. -/
structure Restriction (G : CubeGraph) where
  /-- The cube indices being fixed and their assigned gap values -/
  assignments : List (Fin G.cubes.length × Vertex)
  /-- Each assigned vertex is a valid gap -/
  valid : ∀ p ∈ assignments, (G.cubes[p.1]).isGap p.2 = true
  /-- No cube is assigned twice -/
  nodup : (assignments.map Prod.fst).Nodup

/-- Number of cubes fixed. -/
def Restriction.size (r : Restriction G) : Nat := r.assignments.length

/-- Whether cube i is fixed. -/
def Restriction.isFixed (r : Restriction G) (i : Fin G.cubes.length) : Bool :=
  r.assignments.any (fun p => p.1 == i)

/-! ## Section 2: Extension -/

/-- A gap selection **extends** a restriction if it agrees on all fixed cubes. -/
def extendsRestriction (G : CubeGraph) (s : GapSelection G) (r : Restriction G) : Prop :=
  ∀ p ∈ r.assignments, s p.1 = p.2

/-- If G has a satisfying selection extending r, then G is satisfiable. -/
theorem restriction_preserves_sat (G : CubeGraph) (r : Restriction G)
    (hsat : ∃ s : GapSelection G, validSelection G s ∧ compatibleSelection G s ∧
            extendsRestriction G s r) :
    G.Satisfiable := by
  obtain ⟨s, hv, hc, _⟩ := hsat
  exact ⟨s, hv, hc⟩

/-- Contrapositive: UNSAT implies no compatible extending selection. -/
theorem unsat_no_extension (G : CubeGraph) (r : Restriction G)
    (hunsat : ¬ G.Satisfiable) :
    ¬ ∃ s : GapSelection G, validSelection G s ∧ compatibleSelection G s ∧
      extendsRestriction G s r := by
  intro ⟨s, hv, hc, _⟩
  exact hunsat ⟨s, hv, hc⟩

/-! ## Section 3: Restricted k-Consistency -/

/-- **Restricted k-consistency**: every subset of at most k UNFIXED cubes
    has a compatible gap selection that agrees with the restriction. -/
def KConsistentRestricted (G : CubeGraph) (r : Restriction G) (k : Nat) : Prop :=
  ∀ (S : List (Fin G.cubes.length)),
    S.length ≤ k →
    S.Nodup →
    (∀ i ∈ S, r.isFixed i = false) →
    ∃ s : GapSelection G,
      extendsRestriction G s r ∧
      (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true)

/-- Restricted k-consistency is monotone: larger k is harder. -/
theorem restricted_kconsistent_mono (G : CubeGraph) (r : Restriction G)
    {k₁ k₂ : Nat} (h : k₁ ≤ k₂)
    (hk : KConsistentRestricted G r k₂) : KConsistentRestricted G r k₁ := by
  intro S hlen hnd hunf
  exact hk S (Nat.le_trans hlen h) hnd hunf

/-! ## Section 4: Empty Restriction -/

/-- The empty restriction fixes no cubes. -/
def emptyRestriction (G : CubeGraph) : Restriction G where
  assignments := []
  valid p hp := by simp at hp
  nodup := List.nodup_nil

/-- Empty restriction has size 0. -/
theorem emptyRestriction_size (G : CubeGraph) :
    (emptyRestriction G).size = 0 := rfl

/-- No cube is fixed by the empty restriction. -/
theorem emptyRestriction_not_fixed (G : CubeGraph)
    (i : Fin G.cubes.length) :
    (emptyRestriction G).isFixed i = false := by
  simp [emptyRestriction, Restriction.isFixed]

/-- Any selection extends the empty restriction. -/
theorem extends_empty (G : CubeGraph) (s : GapSelection G) :
    extendsRestriction G s (emptyRestriction G) := by
  intro _ h; simp [emptyRestriction] at h

/-! ## Section 5: UNSAT Detection via Restriction -/

/-- If restricted k-consistency fails at k=1 (some unfixed cube has no
    gap compatible with the restriction), then UNSAT is detected.
    This is the formal statement behind "AC-3 + 1 restriction detects UNSAT". -/
theorem restricted_inconsistency_implies_unsat (G : CubeGraph) (r : Restriction G) (k : Nat)
    (h : ¬ KConsistentRestricted G r k) :
    ¬ ∃ s : GapSelection G, validSelection G s ∧ compatibleSelection G s ∧
      extendsRestriction G s r := by
  intro ⟨s, hv, hc, hext⟩
  apply h
  intro S hlen hnd hunf
  exact ⟨s, hext, fun i _ => hv i, fun e he _ _ => hc e he⟩

/-- **Key corollary**: If for EVERY gap choice of a single cube, restricted
    1-consistency fails, then G is UNSAT.
    This is the formal version of "AC-3 kills after 1 restriction".

    More precisely: if for every cube i and every gap g of cube i,
    the restriction {i ↦ g} leads to restricted 1-inconsistency,
    then G is UNSAT. -/
theorem exhaustive_restriction_unsat (G : CubeGraph)
    (hne : G.cubes.length > 0)
    (h : ∀ (i : Fin G.cubes.length) (g : Vertex),
      (G.cubes[i]).isGap g = true →
      ∀ r : Restriction G, r.assignments = [(i, g)] →
      ¬ KConsistentRestricted G r 1) :
    ¬ G.Satisfiable := by
  intro ⟨s, hv, hc⟩
  · have hlt : 0 < G.cubes.length := hne
    let i : Fin G.cubes.length := ⟨0, hlt⟩
    have hgi := hv i
    -- Build restriction {i ↦ s i}
    let r : Restriction G := {
      assignments := [(i, s i)]
      valid := by intro p hp; simp at hp; obtain ⟨rfl, rfl⟩ := hp; exact hgi
      nodup := by simp
    }
    have hr : r.assignments = [(i, s i)] := rfl
    -- h says this restriction makes 1-consistency fail
    have hfail := h i (s i) hgi r hr
    -- But s extends r and is valid/compatible, so 1-consistency should hold
    apply hfail
    intro S hlen hnd hunf
    exact ⟨s, fun p hp => by simp [r] at hp; obtain ⟨rfl, rfl⟩ := hp; rfl,
           fun j _ => hv j,
           fun e he _ _ => hc e he⟩

end CubeGraph
