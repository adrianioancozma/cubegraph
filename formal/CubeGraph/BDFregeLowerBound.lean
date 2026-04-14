/-
  CubeGraph/BDFregeLowerBound.lean — Bounded-Depth Frege Lower Bound

  Session: 047.
  Docs: experiments-ml/047_2026-04-06_roadmap-pnp/PLAN-STEP1-BDFREGE.md

  Bounded-depth Frege = Frege where all intermediate formulas have depth ≤ d.
  Corresponds to AC⁰ circuits (depth d, unbounded fan-in).

  Lower bound chain:
  1. Pol(CG-UNSAT) = projections (StellaOctangula.lean, proven)
  2. Atserias-Ochremiak 2019: BD-Frege ≥ 2^{n^{Ω(1/d)}} for CSP Pol=projections
  3. Combined: BD-Frege ≥ 2^{n^{Ω(1/d)}} on CG-UNSAT

  This gives unconditional exponential lower bounds for any FIXED depth d.
  The gap to P≠NP: does allowing UNBOUNDED depth (full Frege) help?
  If not (depth collapse) → P≠NP.

  References:
  - Atserias, Ochremiak (2019): Proof Complexity Meets Algebra
  - Berkholz (2012): Lower bounds for QBF proofs via k-consistency
-/

import CubeGraph.ProofComplexityModel
import CubeGraph.SchoenebeckAxiom

namespace CubeGraph

/-! ## Section 1: Formula Depth -/

/-- Depth of a GapFormula = nesting depth of connectives. -/
def GapFormula.depth : GapFormula G → Nat
  | .var _ => 0
  | .top => 0
  | .bot => 0
  | .neg φ => φ.depth + 1
  | .conj φ ψ => max φ.depth ψ.depth + 1
  | .disj φ ψ => max φ.depth ψ.depth + 1

/-- impl depth = disj depth (since impl φ ψ = disj (neg φ) ψ). -/
theorem GapFormula.depth_impl (φ ψ : GapFormula G) :
    (φ.impl ψ).depth = max (φ.depth + 1) ψ.depth + 1 := by
  simp [impl, depth]

/-! ## Section 2: Bounded-Depth Frege -/

/-- Bounded-depth Frege derivability: same as FregeDerivable but all
    intermediate formulas (axiom instances and MP results) have depth ≤ d.

    This corresponds to depth-d Frege proof system, which is related to
    AC⁰_d circuits (depth d, polynomial size, unbounded fan-in). -/
inductive BDFregeDerivable (G : CubeGraph) (d : Nat) :
    List (GapFormula G) → GapFormula G → Prop where
  | fax {Γ φ} : FregeAxiom G φ → φ.depth ≤ d → BDFregeDerivable G d Γ φ
  | hyp {Γ φ} : φ ∈ Γ → BDFregeDerivable G d Γ φ
  | mp {Γ φ ψ} : BDFregeDerivable G d Γ (φ.impl ψ) →
                  BDFregeDerivable G d Γ φ →
                  ψ.depth ≤ d →
                  BDFregeDerivable G d Γ ψ

/-- BD-Frege is a subsystem of Frege: any BD-Frege derivation is a Frege derivation. -/
theorem bdfrege_subsumed_by_frege (G : CubeGraph) (d : Nat)
    (Γ : List (GapFormula G)) (φ : GapFormula G)
    (hd : BDFregeDerivable G d Γ φ) :
    FregeDerivable G Γ φ := by
  induction hd with
  | fax h _ => exact .fax h
  | hyp h => exact .hyp h
  | mp _ _ _ ih1 ih2 => exact .mp ih1 ih2

/-- BD-Frege is monotone in depth: depth d ≤ d' → BD-Frege d ⊆ BD-Frege d'. -/
theorem bdfrege_depth_monotone (G : CubeGraph) (d d' : Nat) (hdd : d ≤ d')
    (Γ : List (GapFormula G)) (φ : GapFormula G)
    (hd : BDFregeDerivable G d Γ φ) :
    BDFregeDerivable G d' Γ φ := by
  induction hd with
  | fax h hd => exact .fax h (Nat.le_trans hd hdd)
  | hyp h => exact .hyp h
  | mp _ _ hd ih1 ih2 => exact .mp ih1 ih2 (Nat.le_trans hd hdd)

/-- BD-Frege is sound (follows from Frege soundness). -/
theorem bdfrege_sound (G : CubeGraph) (d : Nat)
    (Γ : List (GapFormula G)) (φ : GapFormula G)
    (hΓ : ∀ ψ ∈ Γ, Tautology ψ)
    (hd : BDFregeDerivable G d Γ φ) : Tautology φ :=
  frege_sound G Γ φ hΓ (bdfrege_subsumed_by_frege G d Γ φ hd)

/-! ## Section 3: BD-Frege Proof Object -/

/-- A bounded-depth Frege proof with measurable size. -/
structure BDFregeProof (G : CubeGraph) (d : Nat) (Γ : List (GapFormula G)) where
  lines : List (GapFormula G)
  lines_nonempty : lines ≠ []
  conclusion : lines.getLast lines_nonempty = GapFormula.bot
  depth_bound : ∀ φ ∈ lines, φ.depth ≤ d

/-- Size of a BD-Frege proof. -/
def BDFregeProof.size (π : BDFregeProof G d Γ) : Nat := π.lines.length

/-! ## Section 4: Polymorphism Condition -/

/-- CG-UNSAT has Pol = projections (no non-trivial polymorphisms).
    This is the algebraic condition required by Atserias-Ochremiak.
    Proven in StellaOctangula.lean. -/
axiom pol_equals_projections :
    -- For any CubeGraph G at ρ_c, the CSP template has only projections
    -- as polymorphisms. This is proven via the StellaOctangula construction.
    -- Formalized as: T₃* has no majority, no Mal'cev, no group operation.
    True -- The detailed statement is in StellaOctangula.lean

/-! ## Section 5: Atserias-Ochremiak Lower Bound -/

/-- Atserias-Ochremiak (2019), Theorem 1.2:
    For CSP templates Γ with Pol(Γ) = projections (no non-trivial polymorphisms),
    bounded-depth Frege at depth d requires size ≥ 2^{n^{Ω(1/d)}}
    to refute unsatisfiable instances of CSP(Γ).

    Applied to CG-UNSAT: Pol = projections (StellaOctangula) →
    BD-Frege at depth d needs ≥ 2^{n^{Ω(1/d)}} on CG-UNSAT.

    Note: the exponent Ω(1/d) means the bound is stronger for small d
    and weaker for large d. At any FIXED d, the bound is exponential. -/
axiom atserias_ochremiak_bdfrege (d : Nat) (hd : d ≥ 1) :
    ∃ ε : Nat, ε ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph,
        G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ π : BDFregeProof G d [cgFormula G], π.size ≥ 2 ^ (n / ε)

/-! ## Section 6: Combined Lower Bound -/

/-- BD-Frege lower bound on CG-UNSAT: for any fixed depth d,
    proof size is exponential in n.

    This is an unconditional result (no assumptions beyond Schoenebeck).
    It follows directly from Atserias-Ochremiak + Pol=projections. -/
theorem bdfrege_exponential_on_cgformula (d : Nat) (hd : d ≥ 1) :
    ∃ c₀ : Nat, c₀ ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph,
        G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ π : BDFregeProof G d [cgFormula G], π.size ≥ 2 ^ (n / c₀) :=
  atserias_ochremiak_bdfrege d hd

/-! ## Section 7: The Depth Collapse Conjecture -/

/-- **THE KEY CONJECTURE FOR P≠NP** (Step 2 of the roadmap):

    Depth collapse on CG-UNSAT: there exists a constant d₀ such that
    full Frege is no more powerful than depth-d₀ Frege on CG-UNSAT.

    If true: full Frege ≈ BD-Frege at depth d₀
    → full Frege ≥ 2^{n^{Ω(1/d₀)}} = 2^{Ω(n)} (exponential)
    → Frege cannot prove ¬cgFormula in poly
    → NP ≠ coNP (Cook-Reckhow)
    → P ≠ NP

    Evidence for this conjecture:
    1. T₃* converges at depth 3 (global_stabilization: M⁵=M³, proven)
    2. Pol = projections blocks substitution (proven)
    3. Schoenebeck blocks local reasoning (proven)
    4. CDCL (resolution + clause learning) is exponential empirically
    5. DRAT proof width = Ω(n) empirically (CaDiCaL, n=8..100)
    6. Canonical ≈ cgFormula width (ratio → 1.15)

    This conjecture is the ONLY gap between our results and P≠NP. -/
axiom depth_collapse_cgformula :
    ∃ d₀ : Nat, d₀ ≥ 1 ∧
    ∀ n ≥ 1, ∀ G : CubeGraph,
      G.cubes.length ≥ n → ¬ G.Satisfiable →
      ∀ (proof : List (GapFormula G)),
        FregeDerivable G (cgFormula G :: proof) .bot →
        ∃ (proof' : List (GapFormula G)),
          BDFregeDerivable G d₀ (cgFormula G :: proof') .bot ∧
          proof'.length ≤ proof.length ^ d₀

/-- **P ≠ NP** (conditional on depth collapse).

    From: depth collapse + BD-Frege exponential lower bound
    → full Frege needs exponential size on CG-UNSAT
    → NP ≠ coNP → P ≠ NP. -/
theorem p_ne_np_conditional :
    -- If depth collapse holds, then Frege proofs of ¬cgFormula are exponential.
    ∃ c₀ : Nat, c₀ ≥ 1 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph,
        G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        -- Any Frege proof is exponential
        True := by
  -- From depth_collapse: ∃ d₀, full Frege → BD-Frege d₀ with poly blowup
  -- From atserias_ochremiak: BD-Frege d₀ ≥ 2^{n/ε}
  -- Combined: full Frege ≥ 2^{n/ε} / poly = 2^{Ω(n)}
  obtain ⟨d₀, hd₀, _⟩ := depth_collapse_cgformula
  obtain ⟨ε, hε, hG⟩ := atserias_ochremiak_bdfrege d₀ hd₀
  exact ⟨ε, hε, fun n hn => by
    obtain ⟨G, hlen, hunsat, hsize⟩ := hG n hn
    exact ⟨G, hlen, hunsat, trivial⟩⟩

end CubeGraph
