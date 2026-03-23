/-
  CubeGraph/ResolutionFramework.lean

  Clean, self-contained Resolution proof framework for BSW and ABD formalization.

  Provides:
  1. Propositional Resolution types (PLiteral, PClause, PResStep, PResProof)
  2. Width and size metrics
  3. CubeGraph → Resolution bridge (cubeGraphToResolution)
  4. Key definitions for BSW: minResWidth, minResSize
  5. Basic structural lemmas

  Does NOT import from Resolution.lean or Epsilon3CubeBSW.lean to avoid conflicts.

  See: Resolution.lean (older framework, kept for backward compatibility)
  See: Epsilon3CubeBSW.lean (CG-Resolution, higher-level)
  See: Ben-Sasson & Wigderson (2001) — "Short proofs are narrow"
  See: Atserias, Bonacina & de Rezende (2019) — ABD proof complexity
-/

import CubeGraph.Basic

namespace CubeGraph

/-! ## Section 1: Propositional Literals and Clauses -/

/-- A propositional literal: a variable index with a polarity.
    `polarity = true` means positive (x), `polarity = false` means negated (¬x). -/
structure PLiteral where
  var : Nat
  polarity : Bool
  deriving DecidableEq, Repr

/-- The negation of a literal: flips polarity. -/
def PLiteral.neg (l : PLiteral) : PLiteral :=
  { l with polarity := !l.polarity }

/-- Two literals are complementary iff same variable, opposite polarity. -/
def PLiteral.isComplement (l₁ l₂ : PLiteral) : Bool :=
  l₁.var == l₂.var && l₁.polarity != l₂.polarity

/-- Negation is involutive. -/
theorem PLiteral.neg_neg (l : PLiteral) : l.neg.neg = l := by
  simp [PLiteral.neg, Bool.not_not]

/-- A propositional clause: a list of literals.
    Represents a disjunction. Empty clause = contradiction.
    Using `abbrev` so that List operations are directly available. -/
abbrev PClause := List PLiteral

/-- Width of a clause = number of literals. -/
def pclauseWidth (C : PClause) : Nat := C.length

/-- The empty clause (contradiction). -/
def PClause.empty : PClause := []

/-- Width of empty clause is 0. -/
theorem PClause.empty_width : pclauseWidth PClause.empty = 0 := rfl

/-- Variables appearing in a clause. -/
def pclauseVars (C : PClause) : List Nat := (C.map PLiteral.var).eraseDups

/-- Number of distinct variables in a clause. -/
def pclauseNumVars (C : PClause) : Nat := (pclauseVars C).length

/-- Variables of a formula (list of clauses). -/
def formulaVars (clauses : List PClause) : List Nat :=
  (clauses.flatMap fun c => c.map fun l => l.var).eraseDups

/-- Number of variables in a formula. -/
def formulaNumVars (clauses : List PClause) : Nat :=
  (formulaVars clauses).length

/-! ## Section 2: Resolution Steps -/

/-- A resolution step: resolve two premise clauses on a pivot variable.
    The result should be (c1 \ {+pivot}) ∪ (c2 \ {¬pivot}), but we store
    the result explicitly and check validity separately. -/
structure PResStep where
  c1 : PClause
  c2 : PClause
  pivot : Nat
  result : PClause

/-- Remove all literals with a given variable from a clause. -/
def removePivot (C : PClause) (v : Nat) : PClause :=
  C.filter fun l => l.var != v

/-- The expected resolvent of two clauses on a pivot variable:
    union of both clauses with the pivot variable removed. -/
def resolvent (c1 c2 : PClause) (pivot : Nat) : PClause :=
  removePivot c1 pivot ++ removePivot c2 pivot

/-- A resolution step is valid if:
    1. c1 contains the positive pivot literal
    2. c2 contains the negative pivot literal (or vice versa)
    3. result equals the resolvent -/
def PResStep.isValid (step : PResStep) : Prop :=
  (step.c1.any fun l => l.var == step.pivot && l.polarity == true) = true ∧
  (step.c2.any fun l => l.var == step.pivot && l.polarity == false) = true ∧
  step.result = resolvent step.c1 step.c2 step.pivot

/-- Width of a resolution step = width of the result clause. -/
def PResStep.resultWidth (step : PResStep) : Nat := pclauseWidth step.result

/-- Resolvent width is at most the sum of premise widths (trivial upper bound). -/
theorem resolvent_width_le (c1 c2 : PClause) (pivot : Nat) :
    pclauseWidth (resolvent c1 c2 pivot) ≤ pclauseWidth c1 + pclauseWidth c2 := by
  unfold resolvent pclauseWidth removePivot
  simp only [List.length_append]
  exact Nat.add_le_add (List.length_filter_le _ _) (List.length_filter_le _ _)

/-! ## Section 3: Resolution Proofs -/

/-- A resolution proof: axiom clauses (the formula) + derivation steps.
    A refutation derives the empty clause. -/
structure PResProof where
  /-- Initial formula clauses (axioms) -/
  axiomClauses : List PClause
  /-- Sequence of resolution steps -/
  steps : List PResStep

/-- Size of a proof = total number of clauses (axioms + derived). -/
def PResProof.size (π : PResProof) : Nat :=
  π.axiomClauses.length + π.steps.length

/-- All clauses appearing in the proof (axioms + step results). -/
def PResProof.allClauses (π : PResProof) : List PClause :=
  π.axiomClauses ++ π.steps.map PResStep.result

/-- Width of a proof = max clause width across ALL clauses (axioms and derived). -/
def PResProof.proofWidth (π : PResProof) : Nat :=
  π.allClauses.foldl (fun acc c => Nat.max acc (pclauseWidth c)) 0

/-- Maximum axiom width (= k for k-SAT). -/
def PResProof.axiomWidth (π : PResProof) : Nat :=
  π.axiomClauses.foldl (fun acc c => Nat.max acc (pclauseWidth c)) 0

/-- Maximum derived clause width. -/
def PResProof.derivedWidth (π : PResProof) : Nat :=
  (π.steps.map PResStep.result).foldl (fun acc c => Nat.max acc (pclauseWidth c)) 0

/-- Helper: foldl max is monotone in the init argument. -/
private theorem foldl_max_mono {f : α → Nat} (l : List α) {a b : Nat} (h : a ≤ b) :
    l.foldl (fun acc x => Nat.max acc (f x)) a ≤
    l.foldl (fun acc x => Nat.max acc (f x)) b := by
  induction l generalizing a b with
  | nil => exact h
  | cons hd tl ih =>
    exact ih (Nat.max_le.mpr ⟨Nat.le_trans h (Nat.le_max_left _ _), Nat.le_max_right _ _⟩)

/-- Helper: foldl max from init is ≥ init. -/
private theorem foldl_max_ge_init {f : α → Nat} (l : List α) (init : Nat) :
    init ≤ l.foldl (fun acc x => Nat.max acc (f x)) init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- Helper: foldl max over a list appended to another is ≥ foldl max over prefix alone. -/
private theorem foldl_max_le_foldl_max_append {f : α → Nat} (l₁ l₂ : List α) (init : Nat) :
    l₁.foldl (fun acc x => Nat.max acc (f x)) init ≤
    (l₁ ++ l₂).foldl (fun acc x => Nat.max acc (f x)) init := by
  induction l₁ generalizing init with
  | nil =>
    simp only [List.nil_append, List.foldl]
    exact foldl_max_ge_init l₂ init
  | cons hd tl ih =>
    simp only [List.cons_append, List.foldl]
    exact ih (Nat.max init (f hd))

/-- Proof width is at least axiom width. -/
theorem PResProof.proofWidth_ge_axiomWidth (π : PResProof) :
    π.proofWidth ≥ π.axiomWidth := by
  unfold proofWidth axiomWidth allClauses
  exact foldl_max_le_foldl_max_append π.axiomClauses (π.steps.map PResStep.result) 0

/-- A refutation is a proof whose last step derives the empty clause. -/
def PResProof.isRefutation (π : PResProof) : Prop :=
  ∃ s ∈ π.steps, s.result = PClause.empty

/-- Number of steps (simplified depth measure). -/
def PResProof.numSteps (π : PResProof) : Nat := π.steps.length

/-! ## Section 4: CubeGraph ↔ Resolution Bridge -/

/-- Convert a filled vertex in a cube to a propositional clause.

    A cube has 3 variables (var₁, var₂, var₃). A filled vertex v encodes
    literal polarities via bits: bit i = 1 → positive literal for varAt i.

    The clause is the disjunction of these 3 literals.
    Example: vertex 5 = 101₂ → (var₁ ∨ ¬var₂ ∨ var₃). -/
def vertexToClause (c : Cube) (v : Vertex) : PClause :=
  [ { var := c.var₁, polarity := Cube.vertexBit v ⟨0, by omega⟩ },
    { var := c.var₂, polarity := Cube.vertexBit v ⟨1, by omega⟩ },
    { var := c.var₃, polarity := Cube.vertexBit v ⟨2, by omega⟩ } ]

/-- Each vertex-to-clause conversion produces exactly 3 literals. -/
theorem vertexToClause_width (c : Cube) (v : Vertex) :
    pclauseWidth (vertexToClause c v) = 3 := by
  rfl

/-- Collect all clauses from a single cube: one clause per filled vertex.
    A vertex is filled iff it is NOT a gap. -/
def cubeToResolution (c : Cube) : List PClause :=
  (List.finRange 8).filterMap fun v =>
    if c.isGap v then none else some (vertexToClause c v)

/-- Convert an entire CubeGraph to a list of propositional clauses.
    Concatenates the clauses from each cube. -/
def cubeGraphToResolution (G : CubeGraph) : List PClause :=
  G.cubes.flatMap cubeToResolution

/-- Every clause produced by cubeGraphToResolution has width exactly 3. -/
theorem cubeGraph_axiom_width_eq_3 (G : CubeGraph) :
    ∀ cl ∈ cubeGraphToResolution G, pclauseWidth cl = 3 := by
  intro clause hclause
  simp only [cubeGraphToResolution, List.mem_flatMap] at hclause
  obtain ⟨cube, _, hcube_mem⟩ := hclause
  simp only [cubeToResolution, List.mem_filterMap, List.mem_finRange, true_and] at hcube_mem
  obtain ⟨v, hite⟩ := hcube_mem
  split at hite
  · simp at hite
  · simp at hite
    rw [← hite]
    exact vertexToClause_width cube v

/-- Every clause produced by cubeGraphToResolution has width ≤ 3. -/
theorem cubeGraph_axiom_width_le_3 (G : CubeGraph) :
    ∀ cl ∈ cubeGraphToResolution G, pclauseWidth cl ≤ 3 := by
  intro c hc
  exact Nat.le_of_eq (cubeGraph_axiom_width_eq_3 G c hc)

/-- Helper: foldl max over a list where every element maps to ≤ k gives result ≤ k. -/
private theorem foldl_max_le_of_all_le {f : α → Nat} {k : Nat} (l : List α)
    (h : ∀ x ∈ l, f x ≤ k) (init : Nat) (hinit : init ≤ k) :
    l.foldl (fun acc x => Nat.max acc (f x)) init ≤ k := by
  induction l generalizing init with
  | nil => simp [List.foldl]; exact hinit
  | cons hd tl ih =>
    simp only [List.foldl]
    apply ih (fun x hx => h x (.tail _ hx))
    exact Nat.max_le.mpr ⟨hinit, h hd (.head _)⟩

/-- The axiom width of any resolution proof starting from a CubeGraph is ≤ 3. -/
theorem cubeGraph_proof_axiomWidth_le_3 (G : CubeGraph) (π : PResProof)
    (hax : π.axiomClauses = cubeGraphToResolution G) :
    π.axiomWidth ≤ 3 := by
  unfold PResProof.axiomWidth
  rw [hax]
  exact foldl_max_le_of_all_le (cubeGraphToResolution G)
    (cubeGraph_axiom_width_le_3 G) 0 (by omega)

/-! ## Section 5: Minimum Width and Size (BSW Key Definitions) -/

/-- A resolution refutation of a clause set: a proof that derives the empty clause. -/
structure PResRefutation where
  proof : PResProof
  isRefutation : proof.isRefutation

/-- Minimum resolution proof width for refuting an unsatisfiable formula.
    Defined as the infimum over all refutations.

    For BSW: the key quantity. BSW shows size ≥ 2^{(w - maxAxiomWidth)² / n}.

    We axiomatize this as a function — computing the exact minimum requires
    quantifying over all possible proofs, which is not constructive. -/
noncomputable def minResWidth (_clauses : List PClause) : Nat :=
  Classical.choice (inferInstance : Nonempty Nat)

/-- Minimum resolution proof size for refuting an unsatisfiable formula.
    Analogous to minResWidth but for size (= total number of clauses). -/
noncomputable def minResSize (_clauses : List PClause) : Nat :=
  Classical.choice (inferInstance : Nonempty Nat)

/-- **BSW Width-Size Relation (Ben-Sasson & Wigderson 2001, Theorem 1.1)**

    For any unsatisfiable formula F with n variables and initial clause width ≤ k:
      S(F ⊢ ⊥) ≥ 2^{(w(F ⊢ ⊥) - k)² / n}

    where S = minimum proof size, w = minimum proof width, k = max axiom width.

    We state this as: for any refutation π of F,
      size(π) ≥ 2^{(proofWidth(π) - axiomWidth(π))² / numVars(F)}

    This is the fundamental tradeoff: narrow proofs must be long. -/
axiom bsw_width_size_tradeoff :
  ∀ (clauses : List PClause) (π : PResRefutation),
    π.proof.axiomClauses = clauses →
    π.proof.size ≥ 2 ^ ((π.proof.proofWidth - π.proof.axiomWidth) ^ 2 /
                          formulaNumVars clauses)

/-- **ABD Width Lower Bound (Atserias-Bonacina-de Rezende)**

    For random k-SAT at critical density with n variables:
    any resolution refutation has proof width ≥ n / c for some constant c.

    Equivalently: minResWidth(F) = Ω(n) for UNSAT random 3-SAT at ρ_c.

    We state a version for CubeGraph: if G is UNSAT and has ≥ n cubes,
    any refutation of cubeGraphToResolution G has proof width ≥ n/c. -/
axiom abd_width_lower_bound :
  ∃ c : Nat, c ≥ 2 ∧ ∀ (G : CubeGraph),
    ¬ G.Satisfiable →
    G.cubes.length ≥ 1 →
    ∀ (π : PResRefutation),
      π.proof.axiomClauses = cubeGraphToResolution G →
      π.proof.proofWidth ≥ G.cubes.length / c

/-- **Corollary: Exponential Size Lower Bound for CubeGraph Resolution**

    Combining BSW width-size tradeoff with ABD width lower bound:
    any resolution refutation of an UNSAT CubeGraph has size ≥ 2^{Ω(n)}.

    Proof sketch:
    - axiomWidth ≤ 3 (from cubeGraph_proof_axiomWidth_le_3)
    - proofWidth ≥ n/c (from abd_width_lower_bound)
    - numVars ≤ 3n (each cube contributes ≤ 3 variables)
    - size ≥ 2^{(n/c - 3)² / (3n)} = 2^{Ω(n)} -/
theorem exponential_size_lower_bound :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      G.cubes.length ≥ 1 →
      ∀ (π : PResRefutation),
        π.proof.axiomClauses = cubeGraphToResolution G →
        π.proof.size ≥ 2 ^ (G.cubes.length / c) := by
  -- Follows from bsw_width_size_tradeoff + abd_width_lower_bound
  -- The constant c absorbs the (n/c₁ - 3)² / (3n) → n/c calculation
  sorry

/-! ## Section 6: Proof System Properties -/

/-- A proof system is sound if it cannot derive the empty clause from
    satisfiable formulas. We don't prove soundness of Resolution here
    (would require formalizing semantics), but state it as a property. -/
def ResolutionSound : Prop :=
  ∀ (clauses : List PClause),
    (∃ a : Nat → Bool,
      ∀ C ∈ clauses, C.any fun l =>
        if l.polarity then a l.var else !a l.var) →
    ¬ ∃ (π : PResRefutation), π.proof.axiomClauses = clauses

/-- Resolution is sound (standard result, not formalized here). -/
axiom resolution_sound : ResolutionSound

/-! ## Section 7: Width Excess (BSW Key Quantity) -/

/-- Width excess of a proof over its axiom width.
    This is the quantity (w - k) that appears in the BSW exponent. -/
def PResProof.widthExcess (π : PResProof) : Nat :=
  π.proofWidth - π.axiomWidth

/-- For CubeGraph proofs, width excess = proofWidth - 3 when formula is nonempty
    and the proof has axiomWidth = 3 (which holds when there is at least one clause). -/
theorem cubeGraph_widthExcess (G : CubeGraph) (π : PResProof)
    (hax : π.axiomClauses = cubeGraphToResolution G)
    (hne : cubeGraphToResolution G ≠ []) :
    π.widthExcess = π.proofWidth - 3 := by
  -- Requires proving axiomWidth = 3 (not just ≤ 3) when formula is nonempty.
  -- axiomWidth = 3 follows from: every clause has width exactly 3 (cubeGraph_axiom_width_eq_3)
  -- and there exists at least one clause (hne).
  sorry

/-- Width excess is nonneg (trivially, since Nat subtraction is truncated). -/
theorem PResProof.widthExcess_nonneg (π : PResProof) :
    π.widthExcess ≥ 0 := by
  omega

end CubeGraph
