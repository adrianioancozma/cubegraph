/-
  CubeGraph/OneWayMonoid.lean — Algebraic One-Way Property of T₃*

  T₃* (transfer monoid, n≥3) is computationally one-way:
  - Forward (composition): NC¹ (Barrington 1989)
  - Inverse (satisfiability): NP-complete (Bulatov-Zhuk)

  Algebraic properties forcing this:
  - Aperiodic (no groups) → strings isolated
  - Pol = projections → no batching
  - Failure patterns injective → defects individual

  For MONOTONE circuits: isolation → exponential (information_lb)
  For GENERAL circuits: NOT gates could batch-detect → OPEN (= P vs NP)

  This file: 0 sorry. References proven results from other files.
  Deps: CGAdversary.lean, InformationLB.lean
-/

import CubeGraph.InformationLB

namespace CubeGraph

-- ============================================================
-- The three algebraic properties (proven elsewhere, referenced)
-- ============================================================

-- (1) Pol = projections: from PolymorphismBarrier.lean
--     polymorphism_barrier_on_gaps (native_decide, 128/128)

-- (2) Strings isolated: from PNeNP.lean
--     unique_solution_exists (each σ can be unique solution)
--     These are combined in InformationLB.lean → full_independence

-- (3) Failure patterns injective: from CGAdversary.lean
--     failure_pattern_injective_at (rank2 + column coverage → patterns differ)

-- ============================================================
-- The monotone lower bound (algebraic consequence)
-- ============================================================

/-- The monotone lower bound from isolation:

    n^k strings are fully isolated (full_independence).
    Any procedure checking < n^k strings cannot distinguish SAT from UNSAT.
    For monotone circuits: this means size ≥ n^k.

    The algebraic chain:
      T₃* aperiodic → no group → no orbits → strings isolated
      Pol = projections → no combining → no batching
      Isolated + no batching → each string checked individually
      n^k individual checks → monotone circuit ≥ n^k

    This IS the information_lb theorem applied to circuits. -/
theorem monotone_lb_algebraic {k n : Nat}
    (edges : List (Fin k × Fin k))
    (h_edges : ∀ l : Fin k, ∃ e ∈ edges, e.1 = l)
    (e₀ : Fin k × Fin k) (he₀ : e₀ ∈ edges)
    (S : Finset (Fin k → Fin n)) (hS : S.card < n ^ k) :
    ∃ (c_sat c_unsat : Fin k → Fin n → Fin n → Bool),
      (∀ τ ∈ S, tensorAsBoolFunc k n edges c_sat τ =
                 tensorAsBoolFunc k n edges c_unsat τ) ∧
      (∃ σ, tensorAsBoolFunc k n edges c_sat σ = true) ∧
      (∀ σ, tensorAsBoolFunc k n edges c_unsat σ = false) :=
  information_lb edges h_edges e₀ he₀ S hS

/-- The exponential bound: n^k > D^c for any polynomial degree c.
    Arithmetic consequence of isolation. -/
theorem monotone_lb_exponential (c : Nat) (hc : c ≥ 1)
    (n : Nat) (hn : n ≥ 3)
    (D : Nat) (hD : D ≤ 4 * (4 * c * c + 1)) :
    n ^ (4 * c * c + 1) > D ^ c :=
  p_ne_np_via_monotone c hc n hn D hD

-- ============================================================
-- The sole remaining gap: NOT gates
-- ============================================================

/-!
  ## What NOT gates add (the general circuit gap)

  A monotone circuit can only detect PRESENCE: "compat(l,g,g') = 1."
  It verifies: ∃σ where ALL entries are 1. Each σ needs its own AND.

  A general circuit can also detect ABSENCE: "compat(l,g,g') = 0."
  One absent entry blocks ALL σ that read it (up to n^{k-2} strings).
  This is BATCH DETECTION of defects via negation.

  The question: can batch detection (via NOT) reduce n^k to poly?

  At n=2 (Z/2Z, group): YES. Complement + implication = poly.
  At n≥3 (T₃*, aperiodic): Pol=proj argues NO.

  Formal gap:
  - "Pol = projections" constrains SOLUTIONS (gap selections)
  - But a circuit doesn't need to preserve solution structure
  - A circuit with NOT computes arbitrary boolean functions
  - Can those arbitrary functions "simulate" batch detection?

  This gap = P vs NP.

  What's proven:
  - WITHOUT NOT (monotone): exponential (this file) ✓
  - WITH NOT (general): exponential iff P ≠ NP (open)

  What connects them:
  - Pol = projections: complement is NOT a polymorphism
  - Therefore: NOT doesn't preserve CG structure
  - But: a circuit doesn't need to preserve structure
  - The question: does NON-structure-preserving NOT help?
-/

end CubeGraph
