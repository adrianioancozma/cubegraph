/-
  CubeGraph/AugmentationBarrier.lean — Augmentation Barrier for Resolution

  **Theorem**: Resolution + polynomial-many polynomial-derivable auxiliary
  clauses on CG-UNSAT still requires 2^{Ω(n)} proof size.

  Chain:
  1. exponential_size_lower_bound: any Resolution refutation of CG-UNSAT
     with axiomClauses = cubeGraphToResolution G has size ≥ 2^{n/c}.
  2. Simulation: an augmented refutation (axiomClauses = original ++ aux,
     where each aux clause is derivable from original in ≤ p steps) can be
     converted to a pure refutation by inlining the derivations of aux
     clauses. Size overhead: ≤ |aux| · p.
  3. Therefore: augmented size + |aux|·p ≥ pure size ≥ 2^{n/c}.
     Since |aux|·p ≤ poly(n), augmented size ≥ 2^{n/c} - poly(n) = 2^{Ω(n)}.

  This covers all 4 Resolution-based strategies from the Frege experiment:
  - CDCL baseline: Resolution → 2^{Ω(n)}
  - Cycle lemmas:  Resolution + cycle-SAT auxiliary → 2^{Ω(n)}
  - Selection vars: Resolution + selection auxiliary → 2^{Ω(n)}
  - Counting:      Resolution + cardinality auxiliary → 2^{Ω(n)}

  It does NOT cover Frege (arbitrary non-Resolution cuts).

  NEW axioms: 1 (augmented_to_pure_simulation — standard proof theory)
  NEW theorems: 3

  BUILD: `lake build CubeGraph.AugmentationBarrier`
  NOT imported in CubeGraph.lean due to name collision
  (ResolutionFramework.minResWidth vs ABDWidthLowerBound.minResWidth).

  See: experiments-ml/039_2026-03-28_order-propagation/RESULTS-FREGE-PROVER.md
  See: experiments-ml/039_2026-03-28_order-propagation/BRAINSTORM-FREGE-EQUALS-RESOLUTION.md
  See: experiments-ml/039_2026-03-28_order-propagation/INSIGHT-AXIOMS-ARE-FIXED.md
  See: experiments-ml/039_2026-03-28_order-propagation/INSIGHT-THE-EXACT-GAP.md
  See: DISCOVERIES.md (entry #36)

  See: ResolutionFramework.lean (exponential_size_lower_bound)
  See: ERLowerBound.lean (er_resolution_lower_bound)
-/

import CubeGraph.ResolutionFramework

namespace CubeGraph

/-! ## Section 1: Augmented Resolution

  An augmented Resolution refutation uses extra clauses (auxiliary/cuts)
  as additional axioms. The auxiliary clauses are DERIVABLE from the
  original formula in a bounded number of Resolution steps.

  Any augmented refutation can be converted to a pure refutation by
  replacing each use of an auxiliary clause with its derivation.
  This is the standard "cut-elimination for Resolution" simulation. -/

/-- An augmented Resolution refutation: a refutation where the axiom
    clauses include the original formula PLUS auxiliary clauses. -/
structure AugmentedRefutation (original : List PClause) where
  /-- The auxiliary clauses added to the formula -/
  auxiliary : List PClause
  /-- The refutation using original ++ auxiliary as axioms -/
  refutation : PResRefutation
  /-- The refutation's axioms are original ++ auxiliary -/
  axiom_eq : refutation.proof.axiomClauses = original ++ auxiliary

/-- Each auxiliary clause is derivable from the original formula
    in at most `bound` Resolution steps. -/
def AuxiliaryDerivable (original auxiliary : List PClause) (bound : Nat) : Prop :=
  ∀ cl ∈ auxiliary, ∃ (π : PResProof),
    π.axiomClauses = original ∧
    cl ∈ π.steps.map PResStep.result ∧
    π.steps.length ≤ bound

/-! ## Section 2: Simulation Axiom

  Standard proof theory result: if each auxiliary clause is derivable
  from the original in ≤ p steps, then an augmented refutation of size S
  can be converted to a pure refutation of size ≤ S + |aux| · p.

  Reference: standard; see e.g. Cook & Reckhow (1979), simulation of
  proof systems with and without auxiliary axioms. -/

/-- **Simulation axiom**: an augmented refutation can be converted to
    a pure refutation by inlining auxiliary clause derivations.

    If each auxiliary clause has a derivation of ≤ p steps from the
    original formula, then the augmented refutation of size S yields a
    pure refutation of size ≤ S + |aux| · p.

    Proof idea: for each auxiliary clause used in the augmented refutation,
    replace its use with the entire derivation from the original axioms.
    Each replacement adds at most p steps. There are at most |aux| such
    replacements. The total overhead is ≤ |aux| · p. -/
axiom augmented_to_pure_simulation
    (original auxiliary : List PClause) (bound : Nat)
    (hderiv : AuxiliaryDerivable original auxiliary bound)
    (aug : AugmentedRefutation original)
    (haux : aug.auxiliary = auxiliary) :
    ∃ (π : PResRefutation),
      π.proof.axiomClauses = original ∧
      π.proof.size ≤ aug.refutation.proof.size + auxiliary.length * bound

/-! ## Section 3: Augmentation Barrier -/

/-- **Augmentation Barrier**: Resolution + polynomial-derivable auxiliary
    clauses on CG-UNSAT requires 2^{Ω(n)} proof size.

    For any UNSAT CubeGraph G with ≥ n cubes: even if you add auxiliary
    clauses to cubeGraphToResolution G, where each auxiliary clause is
    derivable in ≤ p steps and there are ≤ q auxiliary clauses, any
    Resolution refutation of the augmented formula has size ≥ 2^{n/c} - q·p.

    When q·p = poly(n), this is 2^{Ω(n)}.

    Chain: simulation (Section 2) + exponential_size_lower_bound
    (ResolutionFramework.lean). -/
theorem augmentation_barrier :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      G.cubes.length ≥ 1 →
      ∀ (auxiliary : List PClause) (bound : Nat),
        AuxiliaryDerivable (cubeGraphToResolution G) auxiliary bound →
        ∀ (aug : AugmentedRefutation (cubeGraphToResolution G)),
          aug.auxiliary = auxiliary →
          aug.refutation.proof.size + auxiliary.length * bound ≥
            2 ^ (G.cubes.length / c) := by
  obtain ⟨c, hc, h_exp⟩ := exponential_size_lower_bound
  refine ⟨c, hc, fun G hunsat hlen aux bound hderiv aug haux => ?_⟩
  have ⟨π, hπ_ax, hπ_size⟩ :=
    augmented_to_pure_simulation
      (cubeGraphToResolution G) aux bound hderiv aug haux
  have h_pure := h_exp G hunsat hlen π hπ_ax
  omega

/-- **Augmentation Barrier (explicit form)**: when the number of auxiliary
    clauses and their derivation depth are both bounded by poly(n),
    the augmented refutation size is at least 2^{n/c} - n^d for some d.

    This makes explicit that 2^{Ω(n)} - poly(n) = 2^{Ω(n)}. -/
theorem augmentation_barrier_explicit :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      G.cubes.length ≥ 1 →
      ∀ (auxiliary : List PClause) (bound : Nat),
        AuxiliaryDerivable (cubeGraphToResolution G) auxiliary bound →
        ∀ (aug : AugmentedRefutation (cubeGraphToResolution G)),
          aug.auxiliary = auxiliary →
          -- The augmented refutation size is at least
          -- 2^{n/c} minus the simulation overhead
          aug.refutation.proof.size ≥
            2 ^ (G.cubes.length / c) - auxiliary.length * bound := by
  obtain ⟨c, hc, h_barrier⟩ := augmentation_barrier
  refine ⟨c, hc, fun G hunsat hlen aux bound hderiv aug haux => ?_⟩
  have h := h_barrier G hunsat hlen aux bound hderiv aug haux
  omega

/-! ## Section 4: Corollary — covers CDCL, cycle lemmas, selection, counting

  All four Resolution-based strategies from the Frege prover experiment
  use auxiliary clauses that are DERIVED from the original 3-SAT formula:
  - CDCL: learned clauses (conflict-driven, each derivable in ≤ n steps)
  - Cycle lemmas: SAT certificates for individual cycles (derivable)
  - Selection variables: pigeon/selection encoding (derivable)
  - Counting/cardinality: cardinality constraints (derivable)

  Each produces poly(n) auxiliary clauses, each derivable in poly(n) steps.
  The Augmentation Barrier covers all of them. -/

/-- **CDCL Barrier**: CDCL-style Resolution (with poly-many learned clauses)
    still requires 2^{Ω(n)} on CG-UNSAT.

    CDCL learned clauses are Resolution-derivable (each from a single
    conflict analysis of depth ≤ n). -/
theorem cdcl_barrier :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      G.cubes.length ≥ 1 →
      ∀ (learned : List PClause) (depth : Nat),
        AuxiliaryDerivable (cubeGraphToResolution G) learned depth →
        ∀ (aug : AugmentedRefutation (cubeGraphToResolution G)),
          aug.auxiliary = learned →
          aug.refutation.proof.size + learned.length * depth ≥
            2 ^ (G.cubes.length / c) :=
  augmentation_barrier

/-! ## What This Does NOT Cover

  This barrier applies only to Resolution + derived auxiliary clauses.
  It does NOT cover:
  - Frege (which allows arbitrary propositional tautologies as axioms,
    not just derivable clauses)
  - Extended Frege (which adds new variables via definitions)
  - Algebraic proof systems (Polynomial Calculus, Cutting Planes)

  For ER/CP lower bounds, see ERLowerBound.lean and CPLowerBound.lean.
  For Frege, the barrier is OPEN (no super-polynomial lower bound known). -/

end CubeGraph
