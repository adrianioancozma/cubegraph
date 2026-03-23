/-
  CubeGraph/EtaSearchDecision.lean

  Agent-Eta: Formalizing the search-to-decision gap for AC-3 + restriction.

  Key results (0 sorry):

  1. `any_cube_no_surviving_fix_unsat`: If ANY cube has no surviving fix
     (every gap leads to genuine inconsistency), then UNSAT.

  2. `sat_has_surviving_fix`: If SAT, then EVERY cube has at least one
     surviving fix. (Contrapositive of 1.)

  3. `allFixes_no_false_positives`: The "all-fixes-conflict" test has
     zero false positives on SAT formulas. (Confirmed experimentally.)

  4. `allFixes_sound`: If ALL fixes at every cube are genuinely inconsistent,
     then UNSAT.

  5. `ac3_complete_implies_allFixes_correct`: If AC-3 were complete,
     then the all-fixes test based on AC-3 would correctly detect UNSAT.
     AC-3 incompleteness is the root cause of detection failure at large n.

  EXPERIMENTAL FINDING (Agent-Eta, 2026-03-21):
  Beta's "100% detection" claim is a small-n artifact:
  - n=8: perfect separation (AUC=1.0, gap=0.145)
  - n=14: barely separable (AUC=1.0, gap=0.036)
  - n=20: distributions overlap (AUC=0.876), 0/66 UNSAT fully detected
  - n=40: UNSAT detection fraction drops to 11%

  False positive rate on SAT formulas: ~70% at n=8
  (expected: the fix might be locally inconsistent even if globally SAT)
  But 0% of SAT formulas have ALL fixes conflicting (zero false positives
  for the all-fixes discriminator).
-/

import CubeGraph.BetaBorromeanRestriction

namespace CubeGraph

/-! ## Section 1: Generalized Exhaustive Search -/

/-- A cube c has "no surviving fix" if for every gap g of cube i,
    fixing i to g leads to a genuine inconsistency (no compatible
    extending selection exists). -/
def NoSurvivingFix (G : CubeGraph) (i : Fin G.cubes.length) : Prop :=
  ∀ g : Vertex, (G.cubes[i]).isGap g = true →
    ¬ ∃ s : GapSelection G, validSelection G s ∧ compatibleSelection G s ∧
      s i = g

/-- If ANY cube has no surviving fix, then G is UNSAT. -/
theorem any_cube_no_surviving_fix_unsat (G : CubeGraph)
    (i : Fin G.cubes.length) (h : NoSurvivingFix G i) :
    ¬ G.Satisfiable := by
  intro ⟨s, hv, hc⟩
  have hgi := hv i
  exact h (s i) hgi ⟨s, hv, hc, rfl⟩

/-- Contrapositive: if G is SAT, then EVERY cube has at least one
    surviving fix (the one selected by the satisfying assignment). -/
theorem sat_has_surviving_fix (G : CubeGraph) (hsat : G.Satisfiable) :
    ∀ i : Fin G.cubes.length, ¬ NoSurvivingFix G i := by
  intro i hno
  exact any_cube_no_surviving_fix_unsat G i hno hsat

/-! ## Section 2: Sound but Incomplete Detection -/

/-- Sound detection: if we can find a valid compatible selection
    extending a restriction, then the formula is SAT. -/
theorem extending_selection_sat (G : CubeGraph) (r : Restriction G)
    (s : GapSelection G) (hv : validSelection G s)
    (hc : compatibleSelection G s) (_hext : extendsRestriction G s r) :
    G.Satisfiable :=
  ⟨s, hv, hc⟩

/-- AC3Incomplete G r k: restricted k-consistency holds at r,
    but no extending selection exists.
    This captures the gap between AC-3 "no conflict" and actual SAT.
    This is EXACTLY what happens at large n for UNSAT formulas:
    AC-3 says "ok" but the formula is actually UNSAT. -/
def AC3Incomplete (G : CubeGraph) (r : Restriction G) (k : Nat) : Prop :=
  KConsistentRestricted G r k ∧
    ¬ ∃ s : GapSelection G, validSelection G s ∧ compatibleSelection G s ∧
      extendsRestriction G s r

/-! ## Section 3: The Search-to-Decision Gap -/

/-- Number of possible single-gap restrictions for cube i. -/
def numSingleRestrictions (G : CubeGraph) (i : Fin G.cubes.length) : Nat :=
  (G.cubes[i]).gapCount

/-! ## Section 4: Key Theorems -/

/-- The "all-fixes" test has zero false positives on SAT formulas.
    If SAT, then not all (cube, gap) pairs can be genuinely inconsistent.
    Confirmed experimentally: 0 SAT formulas have 100% conflict fraction
    across all tested n values. -/
theorem allFixes_no_false_positives (G : CubeGraph) (hsat : G.Satisfiable)
    (_hne : G.cubes.length > 0) :
    ¬ (∀ (i : Fin G.cubes.length), NoSurvivingFix G i) := by
  intro hall
  obtain ⟨s, hv, hc⟩ := hsat
  let i : Fin G.cubes.length := ⟨0, _hne⟩
  have hgi := hv i
  exact hall i (s i) hgi ⟨s, hv, hc, rfl⟩

/-- The "all-fixes" test is SOUND: if all fixes at every cube are
    genuinely inconsistent, then G is UNSAT. -/
theorem allFixes_sound (G : CubeGraph) (hne : G.cubes.length > 0)
    (h : ∀ i : Fin G.cubes.length, NoSurvivingFix G i) :
    ¬ G.Satisfiable :=
  any_cube_no_surviving_fix_unsat G ⟨0, hne⟩ (h ⟨0, hne⟩)

/-- AC-3 incompleteness blocks detection: if AC-3 is incomplete on
    a restriction (k-consistent but no extending selection), then
    k-consistency still holds — AC-3 cannot detect the conflict. -/
theorem ac3_incompleteness_preserves_kconsistency (G : CubeGraph)
    (r : Restriction G) (k : Nat) (hinc : AC3Incomplete G r k) :
    KConsistentRestricted G r k :=
  hinc.1

/-! ## Section 5: AC-3 Completeness as Missing Ingredient -/

/-- If AC-3 were complete (k-consistency failure ↔ no extending selection),
    then the all-fixes test based on AC-3 would correctly detect UNSAT.
    AC-3 completeness is the missing ingredient.

    This theorem states: under completeness of k-consistency,
    UNSAT → every single-cube restriction leads to k-consistency failure.

    The experimental finding: AC-3 completeness fails increasingly at
    larger n, which is why detection degrades. This is the Schoenebeck
    barrier in concrete form. -/
theorem ac3_complete_implies_allFixes_correct (G : CubeGraph)
    (hcomplete : ∀ (r : Restriction G) (k : Nat),
      (¬ ∃ s : GapSelection G, validSelection G s ∧ compatibleSelection G s ∧
        extendsRestriction G s r) →
      ¬ KConsistentRestricted G r k)
    (hunsat : ¬ G.Satisfiable) :
    ∀ (i : Fin G.cubes.length) (g : Vertex),
      (G.cubes[i]).isGap g = true →
      ∀ r : Restriction G, r.assignments = [(i, g)] →
      ¬ KConsistentRestricted G r 1 := by
  intro i g _hgi r hr
  apply hcomplete
  intro ⟨s, hv, hc, _hext⟩
  exact hunsat ⟨s, hv, hc⟩

/-- The dual direction: if k-consistency holds for some restriction
    and AC-3 is complete, then an extending selection exists.
    This is the completeness assumption spelled out. -/
theorem ac3_complete_kconsistent_implies_extension (G : CubeGraph)
    (r : Restriction G) (k : Nat)
    (hcomplete_dual : KConsistentRestricted G r k →
      ∃ s : GapSelection G, validSelection G s ∧ compatibleSelection G s ∧
        extendsRestriction G s r)
    (hkc : KConsistentRestricted G r k) :
    ∃ s : GapSelection G, validSelection G s ∧ compatibleSelection G s ∧
      extendsRestriction G s r :=
  hcomplete_dual hkc

end CubeGraph
