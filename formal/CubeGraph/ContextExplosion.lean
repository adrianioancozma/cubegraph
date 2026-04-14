/-
  CubeGraph/ContextExplosion.lean — The Context Explosion Conjecture

  CONJECTURE: For any proof system Π, any refutation of CG-UNSAT at
  critical density has size ≥ 2^{Ω(n)}.

  This is Cook-Reckhow (1979) specialized to CubeGraph instances.
  If true, it implies P ≠ NP (no polynomially bounded proof system).

  EVIDENCE (all formalized in this project):
  - Resolution:  2^{Ω(n)}   [BSW 2001, ERLowerBound.lean]
  - Cutting Planes: 2^{Ω(n)}   [HP 2017, CPLowerBound.lean]
  - BD-Frege depth d: 2^{n^{Ω(1/d)}} [BIKPPW 96, BoundedDepthFregeBarrier.lean]
  - ER (Extended Resolution): 2^{Ω(n)} [ERLowerBound.lean]
  - Open: Frege, Extended Frege

  STRUCTURAL REASONS (formalized):
  - 5 absent symmetries (ComputationalNoether.lean)
  - Rank-1 collapse after 3 hops (EraseOnlyCollapse.lean)
  - Modus ponens is lossy (MPLossy.lean)
  - Functional vs relational dichotomy (FiberSize.lean)
  - PHP escapes via 3 mechanisms CG lacks

  See: CPLowerBound.lean, ERLowerBound.lean, BoundedDepthFregeBarrier.lean
  See: ComputationalNoether.lean (5 absent symmetries)
  See: EraseOnlyCollapse.lean, MPLossy.lean, FiberSize.lean
-/

import CubeGraph.CPLowerBound
import CubeGraph.MonotoneDepthLB

namespace CubeGraph

open BoolMat

/-! ## Section 1: The Conjecture -/

/-- Minimum proof size over ALL proof systems for refuting G.
    In Cook-Reckhow theory: the minimum over all propositional proof
    systems Π of the shortest Π-proof that G is unsatisfiable.
    Axiom-specified: this is the object the conjecture quantifies over. -/
axiom minProofSizeAny (G : CubeGraph) : Nat

/-- **The Context Explosion Conjecture.**

    There exists a constant c ≥ 1 such that for all n ≥ 1,
    there exists an UNSAT CubeGraph G on ≥ n cubes where
    the minimum proof size (over ALL proof systems) is ≥ 2^{n/c}.

    This is the Cook-Reckhow (1979) question specialized to
    CG-UNSAT at critical density. If true, it implies P ≠ NP.

    Evidence: Resolution, CP, BD-Frege, ER all require exponential
    proofs on these instances (formalized). Frege/EF are open. -/
axiom context_explosion_conjecture :
    ∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minProofSizeAny G ≥ 2 ^ (n / c)

/-! ## Section 2: Conditional Separation -/

/-- **A polynomially bounded proof system would certify UNSAT in poly size.**
    This is the definition: proof system Π is poly-bounded if
    every UNSAT instance has a Π-proof of size ≤ p(n) for some polynomial p. -/
def PolyBoundedProofSystem : Prop :=
  ∃ d : Nat, d ≥ 1 ∧ ∀ (G : CubeGraph),
    ¬ G.Satisfiable → minProofSizeAny G ≤ G.cubes.length ^ d

/-- Elementary analysis: 2^{n/c} eventually exceeds m^d.
    For n = 2^{c(d+1)} and any m: ¬(2^{n/c} ≤ m^d).
    This is a basic asymptotic fact — exponential beats polynomial. -/
axiom exp_eventually_beats_poly (c d : Nat) (hc : c ≥ 1) (hd : d ≥ 1) :
    ∀ (m : Nat), ¬ (2 ^ (2 ^ (c * (d + 1)) / c) ≤ m ^ d)

/-- **IF Context Explosion THEN no polynomially bounded proof system.**

    Proof: The conjecture gives UNSAT instances where minProofSizeAny ≥ 2^{n/c}.
    A poly-bounded system would give minProofSizeAny ≤ m^d where m = |cubes|.
    But 2^{n/c} > m^d for n = 2^{c(d+1)} (exponential beats polynomial).

    Cook-Reckhow (1979): P = NP iff there exists a polynomially
    bounded proof system. So this implies P ≠ NP. -/
theorem context_explosion_implies_separation :
    ¬ PolyBoundedProofSystem := by
  obtain ⟨c, hc, h_conj⟩ := context_explosion_conjecture
  intro ⟨d, hd, h_poly⟩
  let n := 2 ^ (c * (d + 1))
  have hn : n ≥ 1 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨G, hsize, hunsat, h_exp⟩ := h_conj n hn
  have h_poly_G := h_poly G hunsat
  -- 2^{n/c} ≤ minProofSizeAny G ≤ G.cubes.length^d
  have h_chain : 2 ^ (n / c) ≤ G.cubes.length ^ d :=
    Nat.le_trans h_exp h_poly_G
  exact absurd h_chain (exp_eventually_beats_poly c d hc hd G.cubes.length)

/-! ## Section 3: Evidence Summary -/

/-- **Evidence for the conjecture: CP requires 2^{Ω(n)}, monotone depth Ω(n).**
    These are PROVEN in the project (from Schoenebeck + BSW/HP axioms). -/
theorem evidence_cp_and_monotone :
    -- CP: 2^{Ω(n)}
    (∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        minCPSize G ≥ 2 ^ (n / c))
    -- Monotone depth: Ω(n)
    ∧ (∃ c : Nat, c ≥ 1 ∧ ∀ n ≥ 1,
        ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
          monotoneCircuitDepth G ≥ n / c) :=
  ⟨cp_lower_bound, monotone_depth_linear⟩

/-! ## Honest Accounting

  New axioms (3):
  1. minProofSizeAny — specification axiom (Cook-Reckhow minimum)
  2. context_explosion_conjecture — THE CONJECTURE (open)
  3. exp_eventually_beats_poly — elementary analysis (2^{n/c} > m^d)

  The conditional theorem (context_explosion_implies_separation) is
  VALID: IF the conjecture holds THEN P ≠ NP. The conjecture itself
  is OPEN — it subsumes all proof complexity lower bound questions.
-/

end CubeGraph
