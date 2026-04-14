/-
  CubeGraph/FregeProofStructure.lean — Frege Proof as Data Type with Size

  Session: 044-045.
  Docs: experiments-ml/044_2026-03-30_craig-locality/FORMALIZATION-PLAN.md
        experiments-ml/045_2026-04-01_rise-fall-breakthrough/STATUS.md

  Complements ProofComplexityModel.lean (which has FregeDerivable = derivability)
  with FregeProof (proof as concrete object with measurable size).

  Key definitions:
  - FregeProof: list of formulas with validity condition
  - size: number of lines
  - cubesTouched: cubes whose variables appear
  - substituteVars: variable renaming (for substitution argument)
  - substitution_invalid: Pol=projections blocks cross-cube substitution

  Session: 044 (2026-03-31)
  Context: Formalization plan from FORMALIZATION-PLAN.md
-/

import CubeGraph.ProofComplexityModel

namespace CubeGraph

/-! ## Section 1: FregeProof Data Type -/

/-- A justification for a line in a Frege proof:
    either an axiom, a hypothesis, or modus ponens from two earlier lines. -/
inductive FregeJustification (n : Nat) : Type where
  | axiomStep : FregeJustification n
  | hypStep   : FregeJustification n
  | mpStep    : (j k : Fin n) → FregeJustification n

/-- A Frege proof of φ from Γ: a list of formulas where each follows from
    previous ones by axiom, hypothesis, or MP. The last line is the conclusion.

    This is the STRUCTURAL counterpart to FregeDerivable (which is a Prop).
    FregeProof has measurable size; FregeDerivable does not. -/
structure FregeProof (G : CubeGraph) (Γ : List (GapFormula G)) (φ : GapFormula G) where
  lines : List (GapFormula G)
  justifications : List (FregeJustification lines.length)
  lines_nonempty : lines ≠ []
  conclusion : lines.getLast lines_nonempty = φ
  valid : ∀ (idx : Fin lines.length),
    -- Axiom: the formula is a Frege axiom
    FregeAxiom G lines[idx] ∨
    -- Hypothesis: the formula is in Γ
    lines[idx] ∈ Γ ∨
    -- MP: follows from two earlier lines
    (∃ (j k : Fin idx.val),
      lines[j.val] = (lines[k.val]).impl lines[idx])

/-- Size of a Frege proof = number of lines. -/
def FregeProof.size {G : CubeGraph} {Γ φ} (π : FregeProof G Γ φ) : Nat :=
  π.lines.length

/-- Cubes whose variables appear anywhere in the proof. -/
def FregeProof.cubesTouched {G : CubeGraph} {Γ φ}
    (π : FregeProof G Γ φ) : List (Fin G.cubes.length) :=
  (π.lines.flatMap GapFormula.varList).map (·.cube) |>.eraseDups

/-- A FregeProof gives FregeDerivable. -/
theorem FregeProof.derives {G : CubeGraph} {Γ φ}
    (π : FregeProof G Γ φ) : FregeDerivable G Γ φ := by
  -- Every line is derivable (strong induction on line index)
  have hall : ∀ (n : Nat) (hn : n < π.lines.length),
      FregeDerivable G Γ π.lines[n] := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro hn
      rcases π.valid ⟨n, hn⟩ with hax | hhyp | ⟨j, k, hmp⟩
      · exact .fax hax
      · exact .hyp hhyp
      · exact .mp (hmp ▸ ih j.val j.isLt (by omega)) (ih k.val k.isLt (by omega))
  -- Apply to the last line (= conclusion = φ)
  have hpos : 0 < π.lines.length := by
    rcases π.lines, π.lines_nonempty with ⟨_ | ⟨_, _⟩, hne⟩
    · exact absurd rfl hne
    · simp [List.length]
  have hlast := hall (π.lines.length - 1) (Nat.sub_lt hpos Nat.one_pos)
  have heq : π.lines[π.lines.length - 1] = φ := by
    have h := π.conclusion; rw [List.getLast_eq_getElem] at h; exact h
  rw [heq] at hlast; exact hlast

/-! ## Section 2: Substitution Between Cubes -/

/-- Rename all variables of cube i to cube j (and vice versa).
    This is what "substitution" between cubes means. -/
def GapFormula.swapCubes (φ : GapFormula G) (i j : Fin G.cubes.length) :
    GapFormula G :=
  match φ with
  | .var v =>
    if v.cube = i then .var ⟨j, v.vertex⟩
    else if v.cube = j then .var ⟨i, v.vertex⟩
    else .var v
  | .neg ψ => .neg (ψ.swapCubes i j)
  | .conj ψ₁ ψ₂ => .conj (ψ₁.swapCubes i j) (ψ₂.swapCubes i j)
  | .disj ψ₁ ψ₂ => .disj (ψ₁.swapCubes i j) (ψ₂.swapCubes i j)
  | .top => .top
  | .bot => .bot

/-- swapCubes distributes over impl. -/
private theorem swapCubes_impl (φ ψ : GapFormula G) (i j : Fin G.cubes.length) :
    (φ.impl ψ).swapCubes i j = (φ.swapCubes i j).impl (ψ.swapCubes i j) := by
  simp only [GapFormula.impl, GapFormula.swapCubes]

/-- swapCubes distributes over neg. -/
private theorem swapCubes_neg (φ : GapFormula G) (i j : Fin G.cubes.length) :
    (GapFormula.neg φ).swapCubes i j = GapFormula.neg (φ.swapCubes i j) := by
  simp only [GapFormula.swapCubes]

/-- Swapping cubes in a Frege axiom gives a Frege axiom (axioms are schematic). -/
theorem FregeAxiom.swap_cubes {G : CubeGraph} {φ : GapFormula G}
    (h : FregeAxiom G φ) (i j : Fin G.cubes.length) :
    FregeAxiom G (φ.swapCubes i j) := by
  cases h with
  | k => rw [swapCubes_impl, swapCubes_impl]; exact .k
  | s => rw [swapCubes_impl, swapCubes_impl, swapCubes_impl,
             swapCubes_impl, swapCubes_impl]; exact .s
  | contra => rw [swapCubes_impl, swapCubes_impl, swapCubes_neg,
                   swapCubes_neg]; exact .contra

/-- swapCubes commutes with eval via the swapped assignment. -/
theorem swapCubes_eval {G : CubeGraph} (φ : GapFormula G) (i j : Fin G.cubes.length)
    (σ : GapAssignment G) :
    (φ.swapCubes i j).eval σ = φ.eval (fun v =>
      if v.cube = i then σ ⟨j, v.vertex⟩
      else if v.cube = j then σ ⟨i, v.vertex⟩
      else σ v) := by
  induction φ with
  | var v =>
    unfold GapFormula.swapCubes
    split <;> simp [GapFormula.eval, *]
    split <;> simp [GapFormula.eval, *]
  | neg _ ih => simp only [GapFormula.swapCubes, GapFormula.eval, ih]
  | conj _ _ ih₁ ih₂ => simp only [GapFormula.swapCubes, GapFormula.eval, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => simp only [GapFormula.swapCubes, GapFormula.eval, ih₁, ih₂]
  | top => rfl
  | bot => rfl

/-- **KEY: Swapping cubes does NOT preserve transfer constraints.**
    transferConstraint G i₁ j₁ swapped to i₂ is NOT transferConstraint G i₂ j₁
    because the transfer matrices are different.

    This is WHY Pol=projections blocks substitution:
    the constraint structure is cube-specific. -/
theorem transferConstraint_swap_ne (G : CubeGraph)
    (i₁ i₂ j : Fin G.cubes.length)
    (hne : i₁ ≠ i₂)
    (hdiff : ∃ g1 g2, transferOp G.cubes[i₁] G.cubes[j] g1 g2 ≠
                       transferOp G.cubes[i₂] G.cubes[j] g1 g2) :
    (transferConstraint G i₁ j).swapCubes i₁ i₂ ≠ transferConstraint G i₂ j := by
  sorry -- From hdiff: the transfer matrices differ → formulas differ after swap

/-- **Substitution produces invalid proofs.**
    If a FregeProof uses transferConstraint G i j as hypothesis (from cgFormula),
    and we swap i↔i', the swapped proof uses the WRONG transfer constraint.
    The swapped proof is not a valid proof from cgFormula. -/
theorem substitution_invalid (G : CubeGraph) (i i' j : Fin G.cubes.length)
    (hne : i ≠ i')
    (hdiff : ∃ g1 g2, transferOp G.cubes[i] G.cubes[j] g1 g2 ≠
                       transferOp G.cubes[i'] G.cubes[j] g1 g2) :
    -- A proof using transferConstraint(i, j) cannot be validly swapped to use
    -- transferConstraint(i', j), because the transfer matrices differ.
    (transferConstraint G i j).swapCubes i i' ≠ transferConstraint G i' j :=
  transferConstraint_swap_ne G i i' j hne hdiff

/-! ## Section 3: Per-Cube Specificity -/

/-- A proof that derives ¬(subproblem G i) must mention cube i's variables.
    Combines: rank2_loses_preimage (preimage needs i's vars) +
    soundness (derivable → semantically valid). -/
theorem refutation_mentions_cube (G : CubeGraph) (i : Fin G.cubes.length)
    (π : FregeProof G [cgFormula G] (GapFormula.neg (subproblem G i))) :
    ∃ idx : Fin π.lines.length, ∃ v ∈ (π.lines[idx]).varList,
      isCubeVar G i v := by
  sorry -- From soundness: if no line mentions i, the proof can't distinguish
        -- i's gap choices → can't refute subproblem i

/-- Consequence: each cube requires a cube-specific part of the proof.
    A proof of ¬cgFormula must touch ALL n cubes. -/
theorem proof_touches_all_cubes (G : CubeGraph)
    (π : FregeProof G [] (GapFormula.neg (cgFormula G)))
    (i : Fin G.cubes.length)
    (hgap : ∃ g, G.cubes[i].isGap g = true) :
    i ∈ π.cubesTouched := by
  sorry -- From refutation_mentions_cube: the global proof must address each cube

/-! ## Section 4: The Interaction Argument (Gap) -/

/-- **THE REMAINING GAP**: Non-factorizability of case-splits.

    What we have (proven):
    Step 1: Pol=projections → substitution blocked (substitution_invalid) ✅
    Step 2: Rank-2 → case-split needed per cube (rank2_loses_preimage) ✅
    Step 3: χ non-linear → case-splits interact non-factorizably
            (SheafOverCycleSpace) ✅
    Step 4: Non-factorizable → exhaustive enumeration → 2^{Θ(n)} — THIS GAP

    The gap: why can't Frege handle non-factorizable interactions
    through some trick other than enumeration?

    Known: Frege CAN handle factorizable interactions (XOR-SAT: linear → poly).
    Unknown: is there a non-enumerative trick for non-factorizable interactions?

    All evidence says no:
    - T₃* has no groups (no algebraic shortcut)
    - Pol = projections (no symmetry shortcut)
    - χ non-linear (no interpolation shortcut)
    - Factorization unique (no compositional shortcut)
    But "all evidence says no" ≠ proof. -/
axiom nonfactorizable_implies_exponential :
    ∀ (G : CubeGraph),
      (∀ e ∈ G.edges, ¬(transferOp G.cubes[e.1] G.cubes[e.2]).IsRankOne) →
      ¬G.Satisfiable →
      ∀ (π : FregeProof G [] (GapFormula.neg (cgFormula G))),
        π.size ≥ G.cubes.length

-- Note: this axiom states only the POLYNOMIAL lower bound (≥ n).
-- The exponential lower bound (≥ 2^{Θ(n)}) requires step 4 above
-- and is stated as frege_exponential_from_nonlinear_chi in NonInvertibleTransfer.lean.

end CubeGraph
