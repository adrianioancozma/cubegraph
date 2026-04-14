/-
  CubeGraph/KConsistentProjection.lean — Projection via k-Consistent Equivalence

  Session: 047.
  Docs: experiments-ml/047_2026-04-06_roadmap-pnp/PLAN-ORTHOGONALITY-AND-PROJECTION.md

  What IS proven: ~_k is a congruence (equivalence + preserves boolean ops).
  What REMAINS: each class has depth-O(1) representative (Barrington gap).
  NO axioms from thin air. Gap is clearly marked.
-/

import CubeGraph.ProofComplexityModel
import CubeGraph.SchoenebeckAxiom
import CubeGraph.NonInvertibleTransfer
import CubeGraph.BDFregeLowerBound

namespace CubeGraph

/-! ## Section 1: k-Consistent Equivalence -/

/-- Two formulas are k-consistently equivalent if they agree on ALL
    k-consistent assignments (from SchoenebeckKConsistent). -/
def kConsistentEquiv (G : CubeGraph) (k : Nat) (φ ψ : GapFormula G) : Prop :=
  ∀ (σ : GapAssignment G),
    -- σ is k-consistent: satisfies constraints on any k cubes
    (∀ S : List (Fin G.cubes.length), S.length ≤ k → S.Nodup →
      (cgFormulaRestricted G S).eval σ = true) →
    φ.eval σ = ψ.eval σ

/-! ## Section 2: ~_k is an Equivalence Relation -/

theorem kEquiv_refl (G : CubeGraph) (k : Nat) (φ : GapFormula G) :
    kConsistentEquiv G k φ φ :=
  fun _ _ => rfl

theorem kEquiv_symm {G : CubeGraph} {k : Nat} {φ ψ : GapFormula G}
    (h : kConsistentEquiv G k φ ψ) : kConsistentEquiv G k ψ φ :=
  fun σ hσ => (h σ hσ).symm

theorem kEquiv_trans {G : CubeGraph} {k : Nat} {φ ψ χ : GapFormula G}
    (h1 : kConsistentEquiv G k φ ψ) (h2 : kConsistentEquiv G k ψ χ) :
    kConsistentEquiv G k φ χ :=
  fun σ hσ => (h1 σ hσ).trans (h2 σ hσ)

/-! ## Section 3: ~_k is a CONGRUENCE -/

/-- ~_k preserves negation. -/
theorem kEquiv_neg {G : CubeGraph} {k : Nat} {φ ψ : GapFormula G}
    (h : kConsistentEquiv G k φ ψ) :
    kConsistentEquiv G k (.neg φ) (.neg ψ) :=
  fun σ hσ => by simp only [GapFormula.eval]; rw [h σ hσ]

/-- ~_k preserves conjunction. -/
theorem kEquiv_conj {G : CubeGraph} {k : Nat} {φ₁ ψ₁ φ₂ ψ₂ : GapFormula G}
    (h1 : kConsistentEquiv G k φ₁ ψ₁) (h2 : kConsistentEquiv G k φ₂ ψ₂) :
    kConsistentEquiv G k (.conj φ₁ φ₂) (.conj ψ₁ ψ₂) :=
  fun σ hσ => by simp only [GapFormula.eval]; rw [h1 σ hσ, h2 σ hσ]

/-- ~_k preserves disjunction. -/
theorem kEquiv_disj {G : CubeGraph} {k : Nat} {φ₁ ψ₁ φ₂ ψ₂ : GapFormula G}
    (h1 : kConsistentEquiv G k φ₁ ψ₁) (h2 : kConsistentEquiv G k φ₂ ψ₂) :
    kConsistentEquiv G k (.disj φ₁ φ₂) (.disj ψ₁ ψ₂) :=
  fun σ hσ => by simp only [GapFormula.eval]; rw [h1 σ hσ, h2 σ hσ]

/-- ~_k preserves implication (impl = disj ∘ neg). -/
theorem kEquiv_impl {G : CubeGraph} {k : Nat} {φ₁ ψ₁ φ₂ ψ₂ : GapFormula G}
    (h1 : kConsistentEquiv G k φ₁ ψ₁) (h2 : kConsistentEquiv G k φ₂ ψ₂) :
    kConsistentEquiv G k (φ₁.impl φ₂) (ψ₁.impl ψ₂) :=
  kEquiv_disj (kEquiv_neg h1) h2

/-! ## Section 4: Consequences -/

/-- ⊥ is invariant under ~_k (it's false on all assignments). -/
theorem kEquiv_bot_self (G : CubeGraph) (k : Nat) :
    kConsistentEquiv G k .bot .bot :=
  kEquiv_refl G k .bot

/-- ⊤ is invariant under ~_k. -/
theorem kEquiv_top_self (G : CubeGraph) (k : Nat) :
    kConsistentEquiv G k .top .top :=
  kEquiv_refl G k .top

/-- Frege axioms are tautologies → ~_k equivalent to ⊤.
    Proven via frege_sound: axioms evaluate to true under any σ. -/
theorem kEquiv_axiom_top {G : CubeGraph} {k : Nat} {φ : GapFormula G}
    (hax : FregeAxiom G φ) : kConsistentEquiv G k φ .top := by
  intro σ _
  simp only [GapFormula.eval]
  exact frege_sound G [] φ (fun _ h => by simp at h) (.fax hax) σ

/-! ## Section 5: What This Gives Us -/

-- PROVEN above: ~_k is a congruence on GapFormula.
-- This means: the quotient GapFormula/~_k is a boolean algebra.
-- MP in the quotient: if [φ→ψ] and [φ], then [ψ]. (From kEquiv_impl.)
-- Axioms map to [⊤]. ⊥ maps to [⊥].
--
-- THE GAP (not proven, not axiomatized, clearly marked):
--   Each equivalence class [φ]_{~_k} contains a formula of depth O(1).
--   This would follow from Barrington-Thérien IF we can show:
--   "the function of φ, restricted to k-consistent assignments,
--    is recognized by an aperiodic monoid (T₃* or a product of T₃*)."
--
-- IF this gap is closed:
--   → Every formula in the proof can be replaced by depth-O(1) equivalent
--   → The proof becomes BD-Frege at depth O(1)
--   → Atserias-Ochremiak: BD-Frege is exponential on CG-UNSAT
--   → P ≠ NP
--
-- PRECISE GAP (from IDEA-LOCAL-GLOBAL-DICHOTOMY.md):
-- At MP: from [φ→ψ] (AC⁰ class) and [φ] (AC⁰ class), is [ψ] in AC⁰ class?
-- On {φ=true}: ψ = (φ→ψ) restricted → AC⁰. ✓
-- On {φ=false}: ψ undetermined by MP. This is the gap.
-- Why it should close: proof doesn't USE ψ on {φ=false} (tree-like 99%).

/-! ## AC⁰ Closure Under Boolean Operations -/

/-- If [φ] has depth-c₀ representative, [¬φ] has depth-(c₀+1) representative. -/
theorem ac0_closure_neg {G : CubeGraph} {k c₀ : Nat} {φ : GapFormula G}
    (h : ∃ φ', kConsistentEquiv G k φ φ' ∧ φ'.depth ≤ c₀) :
    ∃ ψ, kConsistentEquiv G k (.neg φ) ψ ∧ ψ.depth ≤ c₀ + 1 := by
  obtain ⟨φ', heq, hd⟩ := h
  exact ⟨.neg φ', kEquiv_neg heq, by simp [GapFormula.depth]; omega⟩

/-- If [φ] and [ψ] have depth-c₀ reps, [φ∧ψ] has depth-(c₀+1) rep. -/
theorem ac0_closure_conj {G : CubeGraph} {k c₀ : Nat} {φ ψ : GapFormula G}
    (h1 : ∃ φ', kConsistentEquiv G k φ φ' ∧ φ'.depth ≤ c₀)
    (h2 : ∃ ψ', kConsistentEquiv G k ψ ψ' ∧ ψ'.depth ≤ c₀) :
    ∃ χ, kConsistentEquiv G k (.conj φ ψ) χ ∧ χ.depth ≤ c₀ + 1 := by
  obtain ⟨φ', h1, hd1⟩ := h1; obtain ⟨ψ', h2, hd2⟩ := h2
  exact ⟨.conj φ' ψ', kEquiv_conj h1 h2, by simp [GapFormula.depth]; omega⟩

/-- If [φ] and [ψ] have depth-c₀ reps, [φ∨ψ] has depth-(c₀+1) rep. -/
theorem ac0_closure_disj {G : CubeGraph} {k c₀ : Nat} {φ ψ : GapFormula G}
    (h1 : ∃ φ', kConsistentEquiv G k φ φ' ∧ φ'.depth ≤ c₀)
    (h2 : ∃ ψ', kConsistentEquiv G k ψ ψ' ∧ ψ'.depth ≤ c₀) :
    ∃ χ, kConsistentEquiv G k (.disj φ ψ) χ ∧ χ.depth ≤ c₀ + 1 := by
  obtain ⟨φ', h1, hd1⟩ := h1; obtain ⟨ψ', h2, hd2⟩ := h2
  exact ⟨.disj φ' ψ', kEquiv_disj h1 h2, by simp [GapFormula.depth]; omega⟩

/-- If [φ] and [ψ] have depth-c₀ reps, [φ→ψ] has depth-(c₀+2) rep. -/
theorem ac0_closure_impl {G : CubeGraph} {k c₀ : Nat} {φ ψ : GapFormula G}
    (h1 : ∃ φ', kConsistentEquiv G k φ φ' ∧ φ'.depth ≤ c₀)
    (h2 : ∃ ψ', kConsistentEquiv G k ψ ψ' ∧ ψ'.depth ≤ c₀) :
    ∃ χ, kConsistentEquiv G k (φ.impl ψ) χ ∧ χ.depth ≤ c₀ + 2 := by
  obtain ⟨φ', h1, hd1⟩ := h1; obtain ⟨ψ', h2, hd2⟩ := h2
  exact ⟨φ'.impl ψ', kEquiv_impl h1 h2, by
    simp [GapFormula.impl, GapFormula.depth]; omega⟩

end CubeGraph
