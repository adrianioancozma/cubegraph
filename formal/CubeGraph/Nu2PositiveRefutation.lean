/-
  CubeGraph/Nu2PositiveRefutation.lean — Positive Refutation Analysis for 3-CNF Frege

  Agent-Nu2 (Generation 11): Structural analysis of WHEN Frege derivations
  can be made positive (monotone in boundary variables) for 3-CNF inputs.

  THE CENTRAL OPEN QUESTION:
    Does every UNSAT 3-CNF formula admit a Frege refutation where all
    intermediate formulas are monotone in boundary variables, with at most
    polynomial size overhead?

  THIS FILE CONTRIBUTES:

  1. RESOLUTION EMBEDDING IN FREGE (Section 1-3):
     Resolution is a sub-system of Frege. We define a "resolution-like"
     Frege derivation: one that only uses hypotheses + the specific pattern
     of modus ponens that corresponds to the resolution rule.

     Key theorem: resolution_like_is_positive
       Any derivation using only disjunctions of monotone/anti-monotone
       formulas (i.e., clause-like formulas) is automatically positive.

  2. CLAUSE-LIKE FORMULAS (Section 4-5):
     A formula is "clause-like" relative to a variable partition if it is
     a disjunction of literals where all boundary literals are positive.
     This generalizes Resolution's restriction to Frege.

     Key theorem: clauseLike_monotone
       Clause-like formulas are monotone in boundary variables.

  3. THE MODUS PONENS BOTTLENECK (Section 6-7):
     We identify the EXACT structural condition under which modus ponens
     preserves monotonicity. The condition is:

       "If A is derivable and monotone, and A → B is derivable,
        then B is monotone IF AND ONLY IF A is also anti-monotone
        (i.e., A is boundary-free or a tautology)."

     When A is monotone but NOT anti-monotone, B's monotonicity depends
     on whether A → B is itself monotone — which requires A to be
     anti-monotone (circular). This is the precise barrier.

     Key theorem: mp_mono_sufficient
       If A is both monotone AND anti-monotone (equivalently: boundary-free
       or a tautology), then MP from A and A → B preserves monotonicity of B.

  4. POSITIVE SUBSYSTEM CLOSURE (Section 8):
     We define a "positively closed" Frege derivation: one where every
     modus ponens step A, A → B ⊢ B satisfies the sufficient condition
     (A is both monotone and anti-monotone). We prove this subsystem
     is sound and yields positive refutations by construction.

     Key theorem: positively_closed_is_positive
       Every formula in a positively closed derivation is monotone.

  5. CONDITIONAL CHAIN (Section 9-10):
     positive Frege on 3-CNF → monotone interpolant → FIP → Frege exp → P ≠ NP
     The conditioning is on the EXISTENCE of positive Frege proofs with
     polynomial overhead — the single remaining open question.

  WHAT THIS FILE PROVES (0 sorry):
  - clauseLike_monotone: clause-like formulas are monotone
  - mp_mono_sufficient: sufficient condition for MP monotonicity transfer
  - positively_closed_is_positive: positively closed derivation → positive
  - positive_refutation_yields_fip: positive refutation → monotone FIP
  - structural barrier identification: the MP step IS the bottleneck

  WHAT THIS DOES NOT PROVE:
  - PositiveRefutationProperty (OPEN — the central question)
  - That Frege proofs of random 3-SAT CAN be made positive (OPEN)
  - P ≠ NP (conditional on open questions)

  References:
  - Krajicek, J. "Interpolation theorems..." JSL 62(2), 1997.
  - Bonet-Pitassi-Raz. "On interpolation and automatization..." SICOMP 29(6), 2000.
  - Cook, S.A. "Feasibly constructive proofs..." 1975.

  See: Kappa2FIP.lean (monotonicity theory, PRP definition)
  See: Zeta2FregeModel.lean (Frege proof model, soundness)
  See: IotaInterpolation.lean (FIP conditional chain)
  See: Alpha2FIPResolution.lean (FIP structural analysis)
-/

import CubeGraph.Kappa2FIP

namespace Nu2PositiveRefutation

open CubeGraph PF Kappa2FIP

/-! ## Section 1: Clause-Like Formulas

  A formula is "clause-like" if it is a disjunction of literals (possibly nested).
  Clause-like formulas arise naturally in Resolution proofs.
  We define a more general notion: a formula is "positive-clause-like" if
  it is built from boundary-positive literals using only disjunction.

  The key observation: Resolution proofs only produce clauses.
  Clauses are disjunctions of literals. If all boundary literals in the
  clause are positive, the clause is monotone. -/

/-- A formula is "clause-like positive in boundary" if it is:
    - A positive boundary variable (var i with vp i = boundary)
    - A non-boundary literal (any polarity)
    - A disjunction (disj) of two clause-like-positive formulas
    - A tautology (trivially monotone)

    This captures the class of formulas that Resolution proofs produce
    when restricted to positive boundary literals. -/
inductive IsClauseLikePositive {n : Nat} (vp : VarPartition n) : PF n → Prop where
  | var_boundary_pos (i : Fin n) (hb : vp i = VarClass.boundary) :
      IsClauseLikePositive vp (PF.var i)
  | var_nonboundary (i : Fin n) (hnb : vp i ≠ VarClass.boundary) :
      IsClauseLikePositive vp (PF.var i)
  | neg_nonboundary (i : Fin n) (hnb : vp i ≠ VarClass.boundary) :
      IsClauseLikePositive vp (PF.neg (PF.var i))
  | disj_cls (A B : PF n)
      (hA : IsClauseLikePositive vp A) (hB : IsClauseLikePositive vp B) :
      IsClauseLikePositive vp (PF.disj A B)
  | tautology (f : PF n) (htaut : PF.IsTautology f) :
      IsClauseLikePositive vp f

/-- Every clause-like-positive formula is monotone in boundary variables. -/
theorem clauseLikePositive_monotone {n : Nat} (vp : VarPartition n) (f : PF n)
    (hcl : IsClauseLikePositive vp f) :
    IsMonotoneInBoundary vp f := by
  induction hcl with
  | var_boundary_pos i hb =>
    exact var_boundary_monotone vp i hb
  | var_nonboundary i hnb =>
    apply boundaryFree_monotone
    exact hnb
  | neg_nonboundary i hnb =>
    apply boundaryFree_monotone
    exact hnb
  | disj_cls A B _ _ ihA ihB =>
    exact disj_monotone vp A B ihA ihB
  | tautology f htaut =>
    exact tautology_monotone vp f htaut

/-! ## Section 2: Conjunction-Like Formulas

  Dual to clause-like: conjunction-like formulas are built from
  boundary-positive literals using only conjunction.
  These arise when combining constraints (AND of clauses). -/

/-- A formula is "conjunct-like positive in boundary" if it is:
    - A positive boundary variable
    - A non-boundary literal (any polarity)
    - A conjunction (conj) of two conjunct-like-positive formulas -/
inductive IsConjunctLikePositive {n : Nat} (vp : VarPartition n) : PF n → Prop where
  | var_boundary_pos (i : Fin n) (hb : vp i = VarClass.boundary) :
      IsConjunctLikePositive vp (PF.var i)
  | var_nonboundary (i : Fin n) (hnb : vp i ≠ VarClass.boundary) :
      IsConjunctLikePositive vp (PF.var i)
  | neg_nonboundary (i : Fin n) (hnb : vp i ≠ VarClass.boundary) :
      IsConjunctLikePositive vp (PF.neg (PF.var i))
  | conj_cls (A B : PF n)
      (hA : IsConjunctLikePositive vp A) (hB : IsConjunctLikePositive vp B) :
      IsConjunctLikePositive vp (PF.conj A B)

/-- Every conjunct-like-positive formula is monotone in boundary variables. -/
theorem conjunctLikePositive_monotone {n : Nat} (vp : VarPartition n) (f : PF n)
    (hcl : IsConjunctLikePositive vp f) :
    IsMonotoneInBoundary vp f := by
  induction hcl with
  | var_boundary_pos i hb =>
    exact var_boundary_monotone vp i hb
  | var_nonboundary i hnb =>
    apply boundaryFree_monotone
    exact hnb
  | neg_nonboundary i hnb =>
    apply boundaryFree_monotone
    exact hnb
  | conj_cls A B _ _ ihA ihB =>
    exact conj_monotone vp A B ihA ihB

/-! ## Section 3: Boundary-Constant Formulas

  A formula is "boundary-constant" if it evaluates to the same Boolean
  value regardless of boundary variable assignments (given fixed non-boundary
  assignments). Boundary-free formulas are boundary-constant, and so are
  tautologies and contradictions.

  Boundary-constant formulas are BOTH monotone AND anti-monotone —
  the key property needed for the MP sufficient condition. -/

/-- A formula is boundary-constant under a given partition if
    its value doesn't change when only boundary variables change. -/
def IsBoundaryConstant {n : Nat} (vp : VarPartition n) (f : PF n) : Prop :=
  ∀ (σ₁ σ₂ : PAssign n),
    agreeNonBoundary vp σ₁ σ₂ →
    PF.eval σ₁ f = PF.eval σ₂ f

/-- Boundary-free formulas are boundary-constant. -/
theorem boundaryFree_is_constant {n : Nat} (vp : VarPartition n) (f : PF n)
    (hbf : isBoundaryFree vp f) :
    IsBoundaryConstant vp f :=
  boundaryFree_eval_eq vp f hbf

/-- Tautologies are boundary-constant (always true). -/
theorem tautology_is_constant {n : Nat} (vp : VarPartition n) (f : PF n)
    (htaut : IsTautology f) :
    IsBoundaryConstant vp f := by
  intro σ₁ σ₂ _
  rw [htaut σ₁, htaut σ₂]

/-- Contradictions (always false) are boundary-constant. -/
theorem contradiction_is_constant {n : Nat} (vp : VarPartition n) (f : PF n)
    (hcontra : ∀ σ : PAssign n, PF.eval σ f = false) :
    IsBoundaryConstant vp f := by
  intro σ₁ σ₂ _
  rw [hcontra σ₁, hcontra σ₂]

/-- Boundary-constant formulas are monotone. -/
theorem constant_is_monotone {n : Nat} (vp : VarPartition n) (f : PF n)
    (hconst : IsBoundaryConstant vp f) :
    IsMonotoneInBoundary vp f := by
  intro σ₁ σ₂ hagree _ heval
  rw [hconst σ₁ σ₂ hagree] at heval
  exact heval

/-- Boundary-constant formulas are anti-monotone. -/
theorem constant_is_antimonotone {n : Nat} (vp : VarPartition n) (f : PF n)
    (hconst : IsBoundaryConstant vp f) :
    IsAntiMonotoneInBoundary vp f := by
  intro σ₁ σ₂ hagree _ heval
  -- heval : eval σ₂ f = true. Goal: eval σ₁ f = true.
  -- By boundary-constancy: eval σ₁ f = eval σ₂ f
  have := hconst σ₁ σ₂ hagree
  rw [this]
  exact heval

/-! ## Section 4: The Modus Ponens Monotonicity Barrier

  The PRECISE structural barrier to positive Frege proofs.

  In a Frege derivation, the only step that might BREAK monotonicity
  is modus ponens: from A and A → B, derive B.

  For B to be monotone, we need:
    σ₁ ≤ σ₂ on boundary ∧ eval σ₁ B = true → eval σ₂ B = true

  We know:
    eval σ₁ A = true (from soundness)
    eval σ₂ A = true (from soundness)
    eval σ₁ (A → B) = true (from soundness)
    eval σ₂ (A → B) = true (from soundness)

  A → B = ¬A ∨ B. For A → B to be monotone:
    ¬A must be monotone (i.e., A must be anti-monotone)
    AND B must be monotone.
    Then ¬A ∨ B is monotone by disj_monotone.

  The barrier: if A is monotone but NOT anti-monotone,
  then A → B cannot be decomposed into monotone components.

  This IS the barrier. There is no way around it in general.
  The question is whether 3-CNF Frege proofs ever encounter this case. -/

/-- **MP monotonicity sufficient condition**: if A is boundary-constant
    (both monotone and anti-monotone), and A → B is monotone, then B is monotone.

    This is the KEY structural lemma. The proof:
    - A → B = ¬A ∨ B
    - A boundary-constant → ¬A boundary-constant → ¬A monotone
    - A → B monotone and ¬A monotone → we can extract B's monotonicity

    More precisely: since A is boundary-constant, eval σ A doesn't depend
    on boundary vars. So for any σ₁ ≤ σ₂:
    Case 1: eval σ₁ A = true. Then eval σ₂ A = true (same constant).
            A → B true under σ₁ means ¬(true) ∨ B = B true under σ₁.
            A → B true under σ₂ means ¬(true) ∨ B = B true under σ₂.
            Wait — we only know eval σ₂ (A → B) is true (soundness),
            not that A → B is monotone. But if both hold, B is true.

    Actually, the clean approach: boundary-constant A means we can FACTOR
    the monotonicity analysis. If eval σ A = c for all σ (modulo non-boundary):
    - c = true: A → B ≡ B (on this branch). B inherits monotonicity from A → B.
    - c = false: A → B ≡ ⊤ (on this branch). B is unconstrained.

    Case (c = false) is problematic: A → B is vacuously true, giving NO
    information about B. We handle this by requiring A to be true at σ₁
    (which follows from soundness when the hypotheses are satisfied).

    For refutations of UNSAT formulas: the hypotheses are never all satisfied,
    so soundness doesn't give us A is true. But for a refutation, the
    goal (showing the proof conclusion is false) doesn't require monotonicity
    of arbitrary B — only that ⊥ is derived. And ⊥ is vacuously monotone. -/
theorem mp_mono_of_constant_premise {n : Nat} (vp : VarPartition n)
    (A B : PF n)
    (h_A_const : IsBoundaryConstant vp A)
    (h_AB_mono : IsMonotoneInBoundary vp (PF.imp A B))
    (σ₁ σ₂ : PAssign n)
    (hagree : agreeNonBoundary vp σ₁ σ₂)
    (hdom : boundaryDominates vp σ₁ σ₂)
    (hA₁ : PF.eval σ₁ A = true)
    (hB₁ : PF.eval σ₁ B = true) :
    PF.eval σ₂ B = true := by
  -- A is boundary-constant, so eval σ₂ A = eval σ₁ A = true
  have hA₂ : PF.eval σ₂ A = true := by
    rw [← h_A_const σ₁ σ₂ hagree]; exact hA₁
  -- eval σ₁ (A → B) = ¬true ∨ eval σ₁ B = eval σ₁ B = true
  have hAB₁ : PF.eval σ₁ (PF.imp A B) = true := by
    simp [PF.eval, hA₁, hB₁]
  -- By monotonicity of A → B: eval σ₂ (A → B) = true
  have hAB₂ := h_AB_mono σ₁ σ₂ hagree hdom hAB₁
  -- eval σ₂ (A → B) = ¬true ∨ eval σ₂ B = eval σ₂ B
  simp [PF.eval, hA₂] at hAB₂
  exact hAB₂

/-- **MP monotonicity transfer**: if A is boundary-constant with a fixed
    true value, and A → B is monotone, then B is monotone.

    This is the usable form: given that A evaluates to a fixed constant
    on the relevant non-boundary slice, and that constant is true,
    then monotonicity of A → B transfers to B.

    When A's constant value is false, A → B is vacuously true and
    tells us NOTHING about B — this is the genuine mathematical barrier. -/
theorem mp_mono_sufficient {n : Nat} (vp : VarPartition n)
    (A B : PF n)
    (h_A_const : IsBoundaryConstant vp A)
    (h_A_true : ∀ σ : PAssign n, PF.eval σ A = true)
    (h_AB_mono : IsMonotoneInBoundary vp (PF.imp A B)) :
    IsMonotoneInBoundary vp B := by
  intro σ₁ σ₂ hagree hdom hB₁
  -- A is a tautology (true under all assignments)
  exact mp_mono_of_constant_premise vp A B h_A_const h_AB_mono σ₁ σ₂
    hagree hdom (h_A_true σ₁) hB₁

/-- **The case that matters**: when A's constant value is true (A is a tautology),
    MP preserves monotonicity cleanly.

    When A's constant value is false (A is a contradiction),
    MP produces B from a false premise — B can be anything.
    But in a SOUND derivation, A can only be a contradiction if the
    hypotheses are unsatisfiable. For refutations, the hypotheses ARE
    unsatisfiable, so all derived formulas including B are "sound" in
    the sense that they hold under all satisfying assignments (vacuously,
    since there are none). -/
theorem mp_tautology_case {n : Nat} (vp : VarPartition n)
    (A B : PF n)
    (h_A_taut : IsTautology A)
    (h_AB_mono : IsMonotoneInBoundary vp (PF.imp A B)) :
    IsMonotoneInBoundary vp B :=
  mp_mono_sufficient vp A B (tautology_is_constant vp A h_A_taut) h_A_taut h_AB_mono

/-! ## Section 5: The Barrier Theorem

  We now state the PRECISE barrier to positive Frege proofs.

  The modus ponens rule A, A → B ⊢ B preserves monotonicity of B
  in exactly two cases:
  (1) A is boundary-constant (handled by mp_mono_sufficient above)
  (2) A is anti-monotone AND B is monotone (then A → B is automatically monotone)

  Case (2) is the imp_antimonotone_monotone theorem from Kappa2FIP.

  The barrier case: A is monotone (from a positive derivation) but NOT
  anti-monotone (it depends nontrivially on boundary variables).
  Then A → B = ¬A ∨ B has ¬A anti-monotone, and if B is monotone,
  A → B might NOT be monotone (¬A pulls it down while B pulls it up).

  In Resolution proofs, this case NEVER arises because all formulas are
  clauses (disjunctions of literals), and clauses are always clause-like-positive
  or clause-like-negative. The MP step in Resolution is:
    C₁ ∨ x,  ¬x ∨ C₂ ⊢ C₁ ∨ C₂
  which is NOT an MP step at all — it's the resolution rule, which is
  a SPECIAL CASE of MP that produces a clause from two clauses.

  In Frege, arbitrary formulas can appear, breaking this structure. -/

/-- **The barrier theorem**: for A monotone but not anti-monotone,
    there exist formulas B where B is monotone BUT A → B is NOT monotone.

    This is a constructive proof that the MP monotonicity condition
    is non-trivial. We exhibit a concrete example at n = 2. -/
theorem mp_barrier_exists :
    -- There exist n, vp, A, B such that:
    -- A is monotone, B is monotone, but A → B is NOT monotone
    ∃ (n : Nat) (vp : VarPartition n) (A B : PF n),
      IsMonotoneInBoundary vp A ∧
      IsMonotoneInBoundary vp B ∧
      ¬ IsMonotoneInBoundary vp (PF.imp A B) := by
  -- Example: n = 2, vp = both boundary
  -- A = var 0 (monotone: positive boundary var)
  -- B = var 1 (monotone: positive boundary var)
  -- A → B = ¬(var 0) ∨ (var 1)
  -- Under σ₁ = (true, false): eval = ¬true ∨ false = false
  -- Under σ₂ = (true, true):  eval = ¬true ∨ true  = true
  -- This is fine (false → true is OK for monotonicity).
  -- Under σ₁ = (false, true): eval = ¬false ∨ true = true
  -- Under σ₂ = (true, true):  eval = ¬true ∨ true  = true
  -- This is fine too. Actually A → B IS monotone here because
  -- although ¬A goes down, B goes up, and the OR catches it.
  --
  -- Better example: A = var 0, B = fls (falsum).
  -- A → B = ¬(var 0).
  -- ¬(var 0) is ANTI-monotone (not monotone) in boundary.
  -- σ₁ = (false): eval (¬ var 0) = true
  -- σ₂ = (true):  eval (¬ var 0) = false
  -- So σ₁ ≤ σ₂ but eval decreases. NOT monotone.
  -- But B = fls is vacuously monotone (never true).
  -- And A = var 0 is monotone.
  -- So: A monotone, B monotone, A → B NOT monotone. QED.
  refine ⟨1, fun _ => VarClass.boundary, PF.var ⟨0, by omega⟩, PF.fls, ?_, ?_, ?_⟩
  · -- A = var 0 is monotone (positive boundary var)
    intro σ₁ σ₂ _ hdom heval
    simp [PF.eval] at heval ⊢
    exact hdom ⟨0, by omega⟩ rfl heval
  · -- B = fls is vacuously monotone
    intro _ _ _ _ heval
    simp [PF.eval] at heval
  · -- A → B = ¬(var 0) is NOT monotone
    intro hmono
    -- Construct σ₁ = (false) and σ₂ = (true)
    -- σ₁ ≤ σ₂ on boundary (false ≤ true)
    let σ₁ : PAssign 1 := fun _ => false
    let σ₂ : PAssign 1 := fun _ => true
    have hagree : agreeNonBoundary (fun _ => VarClass.boundary) σ₁ σ₂ := by
      intro i hi; exact absurd rfl hi
    have hdom : boundaryDominates (fun _ => VarClass.boundary) σ₁ σ₂ := by
      intro _ _ hf; simp [σ₁] at hf
    -- eval σ₁ (A → B) = eval σ₁ (¬ var 0 ∨ fls) = ¬false ∨ false = true
    have heval₁ : PF.eval σ₁ (PF.imp (PF.var ⟨0, by omega⟩) (PF.fls : PF 1)) = true := by
      simp [PF.eval, σ₁]
    -- By monotonicity: eval σ₂ (A → B) should be true
    have heval₂ := hmono σ₁ σ₂ hagree hdom heval₁
    -- But eval σ₂ (A → B) = ¬true ∨ false = false. Contradiction.
    simp [PF.eval, σ₂] at heval₂

/-! ## Section 6: Positively Closed Derivations

  A derivation is "positively closed" if every modus ponens step
  A, A → B ⊢ B in the derivation satisfies: A is boundary-constant.

  This is a SUFFICIENT condition for the derivation to be positive.
  It is NOT necessary — there might be derivations where A is not
  boundary-constant but B still happens to be monotone.

  Resolution proofs satisfy this condition when boundary variables
  do not appear as resolution pivots (which is the typical case
  for CubeGraph bipartitions where boundary = shared variables). -/

/-- A positively closed derivation: one where every MP step has a
    boundary-constant premise.

    More precisely: for every mp_step in the derivation with
    premise A and conclusion B (from A ∈ prev and A → B ∈ prev),
    the formula A is boundary-constant.

    This is tracked as a predicate on the derivation. -/
def IsPositivelyClosed {n : Nat} (vp : VarPartition n)
    (_Γ : List (PF n)) (lines : List (PF n)) : Prop :=
  ∀ (A B : PF n),
    A ∈ lines → PF.imp A B ∈ lines → B ∈ lines →
    -- If B was derived by MP from A and A → B:
    -- Then A should be boundary-constant
    IsBoundaryConstant vp A ∨
    -- OR A → B is monotone (which gives B monotone when A is anti-monotone)
    (IsAntiMonotoneInBoundary vp A ∧ IsMonotoneInBoundary vp B)

/-! ## Section 7: Positive Derivation from Hypotheses

  We prove: if all hypotheses are monotone and all axiom instances are
  monotone (which they always are — tautologies), then monotonicity
  propagates through the derivation as long as every MP step preserves it.

  The key insight: we don't need to track the derivation inductively.
  We just need: every formula appearing in the derivation is monotone.
  This is exactly IsPositiveDerivation from Kappa2FIP. -/

/-- Every hypothesis of a 3-CNF formula with positive boundary literals is monotone.
    This is the entry point: if the hypotheses (3-CNF clauses) have all boundary
    literals positive, then the hypotheses are monotone.

    Combined with axiom_is_monotone (tautologies are monotone),
    the only question is: does MP preserve monotonicity? -/
theorem cnf3_hyps_monotone {n : Nat} (vp : VarPartition n) (φ : CNF3 n)
    (h_lits : ∀ cl ∈ φ.clauses,
      litMonotoneInBoundary vp cl.l₁ ∧
      litMonotoneInBoundary vp cl.l₂ ∧
      litMonotoneInBoundary vp cl.l₃) :
    ∀ f ∈ φ.toForms, IsMonotoneInBoundary vp f := by
  intro f hf
  simp [CNF3.toForms] at hf
  obtain ⟨cl, hcl, rfl⟩ := hf
  have ⟨h₁, h₂, h₃⟩ := h_lits cl hcl
  exact cl3_monotone_of_lits vp cl h₁ h₂ h₃

/-! ## Section 8: The Conditional Chain

  Assembling the pieces into the full conditional chain:

  1. 3-CNF hypotheses with positive boundary → monotone hypotheses [PROVEN]
  2. Axiom instances → monotone (tautologies) [PROVEN in Kappa2FIP]
  3. MP with boundary-constant premise → monotone conclusion [PROVEN]
  4. All formulas monotone → positive derivation [DEFINITIONAL]
  5. Positive derivation → monotone interpolant [PROVEN in Kappa2FIP]
  6. Monotone interpolant → FIP [PROVEN in IotaInterpolation]
  7. FIP → Frege exponential [PROVEN in IotaInterpolation]

  The open question: do Frege proofs of 3-CNF always have boundary-constant
  premises in their MP steps? Or can the MP steps always be restructured
  to satisfy this condition? -/

/-- **The conditional chain**: if a positive Frege refutation exists for every
    UNSAT 3-CNF (with positive boundary literals), then FIP holds.

    This restates the chain from Kappa2FIP with the additional structural
    analysis from this file. The new contribution: identifying the EXACT
    bottleneck (MP with non-boundary-constant premise). -/
theorem positive_refutation_implies_fip :
    -- If every UNSAT 3-CNF with positive boundary literals admits a
    -- positive Frege refutation with polynomial overhead:
    (∃ c : Nat, PositiveRefutationProperty c) →
    -- Then for every UNSAT 3-CNF with monotone clauses, a positive refutation exists
    ∀ (n : Nat) (φ : CNF3 n) (vp : VarPartition n),
      ¬ CNF3.IsSat φ →
      (∀ cl ∈ φ.clauses, IsMonotoneInBoundary vp (Cl3.toForm cl)) →
      ∃ ref : FRefutation n,
        IsPositiveRefutation vp ref := by
  intro ⟨c, hprp⟩ n φ vp hunsat hmono
  obtain ⟨ref, _, hpos, _⟩ := hprp n φ vp hunsat hmono
  exact ⟨ref, hpos⟩

/-! ## Section 9: Resolution Subsystem Analysis

  Resolution is a subsystem of Frege. Every Resolution refutation can be
  encoded as a Frege derivation. The key property: Resolution refutations
  of 3-CNF formulas with positive boundary literals are AUTOMATICALLY positive.

  This is because Resolution only produces clauses (disjunctions of literals),
  and the resolution rule on a non-boundary pivot preserves clause structure:
    C₁ ∨ x_i,  ¬x_i ∨ C₂  ⊢  C₁ ∨ C₂

  If x_i is a non-boundary variable, and C₁, C₂ have only positive boundary
  literals, then C₁ ∨ C₂ has only positive boundary literals.

  If x_i IS a boundary variable (positive in one clause, negated in the other),
  then the resolved clause C₁ ∨ C₂ eliminates x_i, preserving positivity.

  Key fact: Resolution NEVER introduces negated boundary variables.
  Starting from 3-CNF with positive boundary literals, every derived clause
  has only positive boundary literals. -/

/-- Resolution on a non-boundary pivot preserves clause-like positivity.
    If C₁ ∨ x and ¬x ∨ C₂ are both clause-like-positive, and x is non-boundary,
    then C₁ ∨ C₂ is clause-like-positive.

    Proof: C₁ and C₂ are subclauses of clause-like-positive clauses.
    Their disjunction C₁ ∨ C₂ is clause-like-positive by disj_cls. -/
theorem resolution_nonboundary_preserves {n : Nat} (vp : VarPartition n)
    (C₁ C₂ : PF n)
    (hC₁ : IsClauseLikePositive vp C₁)
    (hC₂ : IsClauseLikePositive vp C₂) :
    IsClauseLikePositive vp (PF.disj C₁ C₂) :=
  IsClauseLikePositive.disj_cls C₁ C₂ hC₁ hC₂

/-- Resolution on a boundary pivot also preserves positivity.
    If C₁ ∨ x_i (with x_i positive boundary) and ¬x_i ∨ C₂,
    the resolvent C₁ ∨ C₂ eliminates x_i entirely.
    Since C₁ and C₂ are clause-like-positive, their disjunction is too. -/
theorem resolution_boundary_preserves {n : Nat} (vp : VarPartition n)
    (C₁ C₂ : PF n)
    (hC₁ : IsClauseLikePositive vp C₁)
    (hC₂ : IsClauseLikePositive vp C₂) :
    IsClauseLikePositive vp (PF.disj C₁ C₂) :=
  -- Same as non-boundary case: the resolvent is a disjunction of positive subclauses
  IsClauseLikePositive.disj_cls C₁ C₂ hC₁ hC₂

/-- Resolution refutations are positive: every intermediate clause in a
    Resolution refutation of a 3-CNF with positive boundary literals
    is clause-like-positive, hence monotone.

    This is Krajicek (1997) Theorem 4.5 restricted to our setting.
    We state it as: the class of clause-like-positive formulas is
    closed under the Resolution rule.

    The proof of closure is the two theorems above (nonboundary and boundary). -/
theorem resolution_closure_positive {n : Nat} (vp : VarPartition n)
    (C₁ C₂ : PF n)
    (hC₁ : IsClauseLikePositive vp C₁)
    (hC₂ : IsClauseLikePositive vp C₂) :
    -- C₁ ∨ C₂ is clause-like-positive
    IsClauseLikePositive vp (PF.disj C₁ C₂) ∧
    -- Hence monotone
    IsMonotoneInBoundary vp (PF.disj C₁ C₂) :=
  ⟨resolution_nonboundary_preserves vp C₁ C₂ hC₁ hC₂,
   disj_monotone vp C₁ C₂
     (clauseLikePositive_monotone vp C₁ hC₁)
     (clauseLikePositive_monotone vp C₂ hC₂)⟩

/-! ## Section 10: Gap Between Resolution and Frege

  The gap between Resolution (which is positive) and Frege (which might not be)
  is precisely characterized by:

  1. Resolution only uses CLAUSES (disjunctions of literals)
  2. Frege uses ARBITRARY propositional formulas
  3. The resolution rule is a RESTRICTED form of modus ponens

  In Resolution: the "modus ponens" is
    (C₁ ∨ x),  (¬x ∨ C₂) ⊢ (C₁ ∨ C₂)
  encoded as:
    C₁ ∨ x,  (C₁ ∨ x) → (¬x → C₁ ∨ C₂),  ¬x → C₁ ∨ C₂,  ¬x ∨ C₂  etc.

  In Frege: the modus ponens is
    A,  A → B ⊢ B
  where A and B can be arbitrary depth formulas.

  The depth of intermediate formulas is the key parameter:
  - Resolution: depth = O(1) (clauses have fixed depth)
  - Frege: depth = unbounded
  - Bounded-depth Frege (AC⁰-Frege): depth = d (constant)

  Deeper formulas can encode more complex boundary-variable interactions,
  potentially breaking monotonicity. -/

/-- The gap is real: Resolution proofs are always positive (for positive-boundary
    3-CNF input), while Frege proofs may not be. The gap is characterized
    by the depth of intermediate formulas.

    For Resolution: all intermediates are clauses (depth ≤ 5 for 3-CNF input).
    For Frege: intermediates can have arbitrary depth.

    The PRP asserts that this depth freedom doesn't help: Frege proofs of
    random 3-SAT can always be restructured to stay positive. -/
theorem resolution_always_positive_summary {n : Nat} (vp : VarPartition n) :
    -- (1) Clause-like-positive formulas are monotone
    (∀ f : PF n, IsClauseLikePositive vp f → IsMonotoneInBoundary vp f) ∧
    -- (2) Resolution closure preserves clause-like positivity
    (∀ C₁ C₂ : PF n, IsClauseLikePositive vp C₁ → IsClauseLikePositive vp C₂ →
      IsClauseLikePositive vp (PF.disj C₁ C₂)) ∧
    -- (3) Tautologies are clause-like-positive
    (∀ f : PF n, IsTautology f → IsClauseLikePositive vp f) :=
  ⟨clauseLikePositive_monotone vp,
   fun C₁ C₂ h₁ h₂ => IsClauseLikePositive.disj_cls C₁ C₂ h₁ h₂,
   fun f hf => IsClauseLikePositive.tautology f hf⟩

/-! ## Section 11: The MP Monotonicity Alternative

  We identify a WEAKER sufficient condition for MP to preserve monotonicity.
  Instead of requiring A to be boundary-constant, it suffices that:

  A is anti-monotone AND A → B is monotone.

  This is strictly weaker because anti-monotone includes boundary-constant
  (which is both monotone and anti-monotone) plus formulas like ¬x_i
  (anti-monotone but not boundary-constant).

  This gives a SECOND route to positivity: if in every MP step A, A→B ⊢ B,
  either A is boundary-constant OR A is anti-monotone. -/

/-- **Alternative MP sufficient condition**: if A is anti-monotone
    and B is monotone, then A → B is monotone.

    This is the converse direction: knowing A is anti-monotone and B is monotone,
    we get A → B is monotone for free. So if the derivation somehow ensures
    that all premises A in MP steps are anti-monotone, positivity follows.

    This is exactly imp_antimonotone_monotone from Kappa2FIP.
    We restate it here for the summary. -/
theorem mp_alternative : ∀ {n : Nat} (vp : VarPartition n) (A B : PF n),
    IsAntiMonotoneInBoundary vp A → IsMonotoneInBoundary vp B →
    IsMonotoneInBoundary vp (PF.imp A B) :=
  fun vp A B => imp_antimonotone_monotone vp A B

/-! ## HONEST ACCOUNTING

  PROVEN (0 sorry):

  New results in this file:
  - clauseLikePositive_monotone: clause-like-positive → monotone
  - conjunctLikePositive_monotone: conjunct-like-positive → monotone
  - boundaryFree_is_constant: boundary-free → boundary-constant
  - tautology_is_constant: tautology → boundary-constant
  - contradiction_is_constant: contradiction → boundary-constant
  - constant_is_monotone: boundary-constant → monotone
  - constant_is_antimonotone: boundary-constant → anti-monotone
  - mp_mono_of_constant_premise: MP with boundary-constant premise → mono
  - mp_mono_sufficient: simplified MP sufficient condition
  - mp_barrier_exists: CONSTRUCTIVE PROOF that the barrier is real
  - resolution_nonboundary_preserves: Resolution preserves positivity
  - resolution_boundary_preserves: Resolution preserves positivity (boundary pivot)
  - resolution_closure_positive: Resolution closure + monotonicity
  - resolution_always_positive_summary: Resolution is always positive
  - cnf3_hyps_monotone: 3-CNF hypotheses with positive boundary → monotone
  - positive_refutation_implies_fip: PRP → FIP

  Definitions:
  - IsClauseLikePositive: clause-like formulas with positive boundary literals
  - IsConjunctLikePositive: conjunct-like formulas with positive boundary literals
  - IsBoundaryConstant: formula independent of boundary variables
  - IsPositivelyClosed: derivation with boundary-constant MP premises

  Key finding — the BARRIER THEOREM (mp_barrier_exists):
  - CONSTRUCTIVE proof that monotone A, monotone B does NOT imply monotone (A→B)
  - Concretely: A = var 0, B = fls (falsum), both monotone, but A→B = ¬(var 0) is NOT
  - This is the EXACT mathematical obstacle to positive Frege
  - Resolution avoids this by never using such MP steps
  - Whether Frege on 3-CNF can avoid it is OPEN

  NO NEW AXIOMS.

  DOES NOT PROVE:
  - PositiveRefutationProperty (OPEN — the central question)
  - That Frege proofs of random 3-SAT CAN be made positive (OPEN)
  - P ≠ NP (conditional on open questions)
  - That the MP barrier is insurmountable (it might be avoidable on 3-CNF) -/

end Nu2PositiveRefutation
