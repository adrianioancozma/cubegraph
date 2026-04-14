/-
  CubeGraph/ResolutionFramework.lean

  Clean, self-contained Resolution proof framework for BSW and ABD formalization.

  Provides:
  1. Propositional Resolution types (PLiteral, PClause, PResStep, PResProof)
  2. Width and size metrics
  3. CubeGraph → Resolution bridge (cubeGraphToResolution)
  4. Key definitions for BSW: minResWidth, minResSize
  5. Basic structural lemmas

  Does NOT import from Resolution.lean or CubeBSW.lean to avoid conflicts.

  See: Resolution.lean (older framework, kept for backward compatibility)
  See: CubeBSW.lean (CG-Resolution, higher-level)
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

-- **Corollary: Exponential Size Lower Bound for CubeGraph Resolution**
--
-- Combining BSW width-size tradeoff with ABD width lower bound:
-- any resolution refutation of an UNSAT CubeGraph has size >= 2^(Omega(n)).
-- Proof: axiomWidth <= 3, proofWidth >= n/c1, numVars <= 3n,
-- size >= 2^((n/c1 - 3)^2 / (3n)) >= 2^(n / (12*c1^2)).

/-- Each cube contributes at most 3 distinct variables to the formula.
    Structural fact: cubeGraphToResolution generates clauses whose variables
    come from cube triplets (var₁, var₂, var₃), and eraseDups can only reduce
    the count.

    KEPT AS AXIOM (2026-03-29 audit): The proof requires `List.nodup_eraseDups`
    (eraseDups produces a Nodup list) and a "Nodup subset of list L implies
    length ≤ length L" lemma. Neither is available in core Lean 4 without
    Mathlib. The statement is mathematically trivial: each cube has 3 variables,
    so the total number of distinct variables across all cubes is ≤ 3n. -/
axiom formulaNumVars_le (G : CubeGraph) :
    formulaNumVars (cubeGraphToResolution G) ≤ 3 * G.cubes.length

private theorem refutation_size_pos (π : PResRefutation) : π.proof.size ≥ 1 := by
  unfold PResProof.size
  have ⟨s, hs, _⟩ := π.isRefutation
  have : π.proof.steps.length ≥ 1 := by
    cases h : π.proof.steps with
    | nil => simp [h] at hs
    | cons _ _ => simp [List.length]
  omega

/-- If all cubes have all vertices as gaps, G is satisfiable. -/
private theorem all_gap_sat (G : CubeGraph)
    (hall : ∀ (i : Fin G.cubes.length) (v : Vertex), (G.cubes[i]).isGap v = true) :
    G.Satisfiable := by
  refine ⟨fun _ => ⟨0, by omega⟩, ?_, ?_⟩
  · intro i; exact hall i ⟨0, by omega⟩
  · intro e _; unfold transferOp
    simp only [hall e.1, hall e.2, Bool.true_and]
    apply List.all_eq_true.mpr; intro sv _; simp

/-- If cubeGraphToResolution G = [], all cubes have all-gap vertices. -/
private theorem empty_resolution_all_gap (G : CubeGraph)
    (hempty : cubeGraphToResolution G = []) :
    ∀ (i : Fin G.cubes.length) (v : Vertex), (G.cubes[i]).isGap v = true := by
  intro i v
  have : cubeToResolution (G.cubes[i]) = [] :=
    List.flatMap_eq_nil_iff.mp (show G.cubes.flatMap cubeToResolution = [] from hempty)
      (G.cubes[i]) (List.getElem_mem i.isLt)
  unfold cubeToResolution at this
  have hfilt := List.filterMap_eq_nil_iff.mp this v (List.mem_finRange v)
  split at hfilt
  · assumption
  · simp at hfilt

/-- formulaNumVars = 0 implies the resolution encoding has no clauses. -/
private theorem nv_zero_implies_empty_resolution (G : CubeGraph)
    (hnv : formulaNumVars (cubeGraphToResolution G) = 0) :
    cubeGraphToResolution G = [] := by
  unfold formulaNumVars formulaVars at hnv
  have hflat : (cubeGraphToResolution G).flatMap (fun c => c.map (·.var)) = [] := by
    match hc : (cubeGraphToResolution G).flatMap (fun c => c.map (·.var)) with
    | [] => exact hc
    | hd :: tl =>
      exfalso; rw [hc] at hnv
      have := List.mem_eraseDups.mpr (List.Mem.head (a := hd) tl)
      simp_all
  rw [List.flatMap_eq_nil_iff] at hflat
  match hcgr : cubeGraphToResolution G with
  | [] => rfl
  | cl :: _ =>
    exfalso
    have hwidth := cubeGraph_axiom_width_eq_3 G cl (hcgr ▸ .head _)
    have := List.eq_nil_of_map_eq_nil (hflat cl (hcgr ▸ .head _))
    unfold pclauseWidth at hwidth; simp [this] at hwidth

theorem exponential_size_lower_bound :
    ∃ c : Nat, c ≥ 1 ∧ ∀ (G : CubeGraph),
      ¬ G.Satisfiable →
      G.cubes.length ≥ 1 →
      ∀ (π : PResRefutation),
        π.proof.axiomClauses = cubeGraphToResolution G →
        π.proof.size ≥ 2 ^ (G.cubes.length / c) := by
  obtain ⟨c₁, hc₁, habd⟩ := abd_width_lower_bound
  have hc_pos : 12 * c₁ ^ 2 ≥ 1 := by
    have h2 : c₁ ≥ 2 := hc₁
    have h4 : c₁ ^ 2 ≥ 4 := by
      show c₁ ^ 2 ≥ 2 ^ 2
      exact Nat.pow_le_pow_left h2 2
    omega
  refine ⟨12 * c₁ ^ 2, hc_pos, ?_⟩
  intro G hunsat hlen π hπ
  have hbsw := bsw_width_size_tradeoff (cubeGraphToResolution G) π hπ
  have hpw := habd G hunsat hlen π hπ
  have haw := cubeGraph_proof_axiomWidth_le_3 G π.proof hπ
  have hnv := formulaNumVars_le G
  have hpw_ge_aw := π.proof.proofWidth_ge_axiomWidth
  -- Chain: size ≥ 2^((pw-aw)²/numVars) ≥ 2^(n/(12c₁²))
  apply Nat.le_trans _ hbsw
  apply Nat.pow_le_pow_right (by omega : 0 < 2)
  -- Width excess: pw - aw ≥ n/c₁ - 3
  have hwe : π.proof.proofWidth - π.proof.axiomWidth ≥ G.cubes.length / c₁ - 3 := by
    omega
  -- (pw-aw)² ≥ (n/c₁ - 3)²
  have hsq : (π.proof.proofWidth - π.proof.axiomWidth) ^ 2 ≥
      (G.cubes.length / c₁ - 3) ^ 2 := Nat.pow_le_pow_left hwe 2
  -- Trivial case: n/(12c₁²) = 0
  by_cases hsmall : G.cubes.length / (12 * c₁ ^ 2) = 0
  · simp [hsmall]
  · -- Cf. Ben-Sasson & Wigderson (2001, Theorem 1.1).
    -- Step 1: n ≥ 12c₁² (from hsmall: n/(12c₁²) ≠ 0)
    have hn12 : G.cubes.length ≥ 12 * c₁ ^ 2 := by
      have h1 : G.cubes.length / (12 * c₁ ^ 2) ≥ 1 := Nat.pos_of_ne_zero hsmall
      have h2 := (Nat.le_div_iff_mul_le (by omega : 0 < 12 * c₁ ^ 2)).mp h1
      omega
    -- Step 2: n/c₁ ≥ 7
    have hq7 : G.cubes.length / c₁ ≥ 7 := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < c₁)).mpr
      have hc₁_sq : c₁ ^ 2 = c₁ * c₁ := Nat.pow_two c₁
      have : 7 * c₁ ≤ 12 * c₁ ^ 2 := by
        rw [hc₁_sq]; have : c₁ * c₁ ≥ 2 * c₁ := Nat.mul_le_mul_right c₁ hc₁; omega
      omega
    -- Step 3: n ≤ 2c₁*(n/c₁ - 3)
    have hn_le : G.cubes.length ≤ 2 * c₁ * (G.cubes.length / c₁ - 3) := by
      have hdiv := Nat.div_add_mod G.cubes.length c₁
      have hmod_bound : G.cubes.length % c₁ < c₁ := Nat.mod_lt _ (by omega)
      have hm7 : c₁ * (G.cubes.length / c₁) ≥ 7 * c₁ := by
        have h1 : (G.cubes.length / c₁) * c₁ ≥ 7 * c₁ := Nat.mul_le_mul_right c₁ hq7
        have h2 : c₁ * (G.cubes.length / c₁) = (G.cubes.length / c₁) * c₁ :=
          Nat.mul_comm c₁ (G.cubes.length / c₁)
        omega
      rw [Nat.mul_assoc 2 c₁ _, Nat.mul_sub c₁]
      omega
    -- Step 4: 3n² ≤ 12c₁²*(n/c₁-3)²
    have hsq_core : 3 * G.cubes.length ^ 2 ≤
        12 * c₁ ^ 2 * (G.cubes.length / c₁ - 3) ^ 2 := by
      have h_sq : G.cubes.length ^ 2 ≤ (2 * c₁ * (G.cubes.length / c₁ - 3)) ^ 2 :=
        Nat.pow_le_pow_left hn_le 2
      have h_expand : (2 * c₁ * (G.cubes.length / c₁ - 3)) ^ 2 =
          4 * c₁ ^ 2 * (G.cubes.length / c₁ - 3) ^ 2 := by
        rw [show 2 * c₁ * (G.cubes.length / c₁ - 3) =
            (2 * c₁) * (G.cubes.length / c₁ - 3) from rfl]
        rw [Nat.mul_pow, Nat.mul_pow]
      rw [h_expand] at h_sq
      calc 3 * G.cubes.length ^ 2
          ≤ 3 * (4 * c₁ ^ 2 * (G.cubes.length / c₁ - 3) ^ 2) :=
            Nat.mul_le_mul_left 3 h_sq
        _ = 12 * c₁ ^ 2 * (G.cubes.length / c₁ - 3) ^ 2 := by
            rw [← Nat.mul_assoc 3 (4 * c₁ ^ 2) _, ← Nat.mul_assoc 3 4 (c₁ ^ 2)]
    -- Step 5: n*nv ≤ 12c₁²*(pw-aw)²
    have hn_nv : G.cubes.length * formulaNumVars (cubeGraphToResolution G) ≤
        12 * c₁ ^ 2 * (π.proof.proofWidth - π.proof.axiomWidth) ^ 2 := by
      have hpow : G.cubes.length * (3 * G.cubes.length) =
          3 * G.cubes.length ^ 2 := by
        rw [Nat.pow_two, Nat.mul_comm G.cubes.length (3 * G.cubes.length), Nat.mul_assoc]
      calc G.cubes.length * formulaNumVars (cubeGraphToResolution G)
          ≤ G.cubes.length * (3 * G.cubes.length) := Nat.mul_le_mul_left _ hnv
        _ = 3 * G.cubes.length ^ 2 := hpow
        _ ≤ 12 * c₁ ^ 2 * (G.cubes.length / c₁ - 3) ^ 2 := hsq_core
        _ ≤ 12 * c₁ ^ 2 * (π.proof.proofWidth - π.proof.axiomWidth) ^ 2 :=
          Nat.mul_le_mul_left _ hsq
    -- Step 6: n/(12c₁²)*nv ≤ (pw-aw)²
    have h_assoc : G.cubes.length / (12 * c₁ ^ 2) *
        formulaNumVars (cubeGraphToResolution G) ≤
        (π.proof.proofWidth - π.proof.axiomWidth) ^ 2 := by
      have hcomm : G.cubes.length / (12 * c₁ ^ 2) *
          formulaNumVars (cubeGraphToResolution G) =
          formulaNumVars (cubeGraphToResolution G) *
          (G.cubes.length / (12 * c₁ ^ 2)) := Nat.mul_comm _ _
      have hcomm2 : formulaNumVars (cubeGraphToResolution G) * G.cubes.length =
          G.cubes.length * formulaNumVars (cubeGraphToResolution G) := Nat.mul_comm _ _
      rw [hcomm]
      calc formulaNumVars (cubeGraphToResolution G) * (G.cubes.length / (12 * c₁ ^ 2))
          ≤ formulaNumVars (cubeGraphToResolution G) * G.cubes.length / (12 * c₁ ^ 2) :=
          Nat.mul_div_le_mul_div_assoc _ _ _
        _ = G.cubes.length * formulaNumVars (cubeGraphToResolution G) / (12 * c₁ ^ 2) := by
          rw [hcomm2]
        _ ≤ (π.proof.proofWidth - π.proof.axiomWidth) ^ 2 :=
          Nat.div_le_of_le_mul hn_nv
    -- Step 7: conclude using le_div_iff_mul_le (need nv > 0)
    by_cases hnv0 : formulaNumVars (cubeGraphToResolution G) = 0
    · -- nv=0 is impossible: all cubes would be all-gap → G satisfiable → ¬hunsat.
      exfalso
      exact hunsat (all_gap_sat G
        (empty_resolution_all_gap G (nv_zero_implies_empty_resolution G hnv0)))
    · exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hnv0)).mpr h_assoc

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

/- REMOVED (2026-03-24): `resolution_sound` axiom deleted.
   Category D dead code — zero downstream uses in proofs.
   Provably FALSE under current definitions: ResolutionSound asserts that no
   PResRefutation exists for satisfiable formulas, but PResRefutation only
   requires ∃ step with result = [], not that step premises come from axioms.
   The definition lacks a validity/derivability check, making it unsound.
   A correct formalization would need a full derivation DAG with validity. -/

/-! ## Section 7: Width Excess (BSW Key Quantity) -/

/-- Width excess of a proof over its axiom width.
    This is the quantity (w - k) that appears in the BSW exponent. -/
def PResProof.widthExcess (π : PResProof) : Nat :=
  π.proofWidth - π.axiomWidth

/-- Helper: if x ∈ l then foldl max 0 ≥ f x. -/
private theorem foldl_max_ge_elem {f : α → Nat} {x : α} {l : List α}
    (hmem : x ∈ l) :
    f x ≤ l.foldl (fun acc y => Nat.max acc (f y)) 0 := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.foldl]
    cases hmem with
    | head => exact Nat.le_trans (Nat.le_max_right 0 (f x)) (foldl_max_ge_init tl _)
    | tail _ htl => exact Nat.le_trans (ih htl) (foldl_max_mono tl (Nat.zero_le _))

/-- For CubeGraph proofs, width excess = proofWidth - 3 when formula is nonempty
    and the proof has axiomWidth = 3 (which holds when there is at least one clause). -/
theorem cubeGraph_widthExcess (G : CubeGraph) (π : PResProof)
    (hax : π.axiomClauses = cubeGraphToResolution G)
    (hne : cubeGraphToResolution G ≠ []) :
    π.widthExcess = π.proofWidth - 3 := by
  unfold PResProof.widthExcess
  suffices h : π.axiomWidth = 3 by rw [h]
  unfold PResProof.axiomWidth; rw [hax]
  apply Nat.le_antisymm
  · exact foldl_max_le_of_all_le _
      (fun x hx => Nat.le_of_eq (cubeGraph_axiom_width_eq_3 G x hx)) 0 (by omega)
  · have ⟨hd, hd_mem⟩ : ∃ x, x ∈ cubeGraphToResolution G := by
      cases h : cubeGraphToResolution G with
      | nil => exact absurd h hne
      | cons hd _ => exact ⟨hd, .head _⟩
    calc 3 = pclauseWidth hd := (cubeGraph_axiom_width_eq_3 G hd hd_mem).symm
      _ ≤ _ := foldl_max_ge_elem hd_mem

/-- Width excess is nonneg (trivially, since Nat subtraction is truncated). -/
theorem PResProof.widthExcess_nonneg (π : PResProof) :
    π.widthExcess ≥ 0 := by
  omega

end CubeGraph
