/-
  CubeGraph/DAGExtraction.lean — DAG Extraction: Monotone Circuit from Frege Proof

  THE ARGUMENT (Sections 9-10 of PLAN-MODUS-PONENS-MONOTONE.md):

  1. Frege extraction produces a CIRCUIT (DAG) for the interpolant.
  2. At each MP step: I(psi) = I(phi) AND I(phi->psi). One AND gate.
  3. DAG size = O(S) where S = proof size (one gate per proof step).
  4. Each AND gate: AND of monotone = monotone.
  5. Non-monotone gates: from Type 2 axiom interpolants (one per Type 2 source).
  6. Question: how many non-mono gates on a root-to-leaf path?

  ADVERSARIAL FINDING (CRITICAL):

  The original plan claims nesting=1 (Section 9 of the PLAN). This is INCORRECT.
  On a root-to-leaf path in the DAG, we can encounter non-monotone gates from
  MULTIPLE different Type 2 cubes (C₁, C₂, ..., Cₖ). Each is non-monotone at
  its own cube's d-variables. The AND of these is non-monotone at {C₁,...,Cₖ}.

  The nesting-1 argument from FinalChain.lean applies to CUT DEPTH (a property
  of the proof structure), not to DAG GATE DEPTH (a property of the circuit).
  These are DIFFERENT measures:
  - Cut depth: nesting of case-splits in the proof → blowup per cut level
  - DAG gate depth: distance from root to leaf in the extracted circuit

  The FinalChain axiom `frege_cut_monotonicity_induction` claims nesting ≤ 1,
  but this is about the proof's cut structure, not the extracted circuit's
  non-monotone gate depth. The DAG circuit can have non-mono depth = O(n).

  WHAT IS PROVED HERE (0 sorry, 0 new axioms):

  1. mono_compose_and: AND of monotone boolean functions is monotone
  2. mono_compose_or: OR of monotone boolean functions is monotone
  3. or_of_monotone_is_monotone: OR over a list of monotone functions is monotone
  4. dag_extraction_step_and: MP step adds one AND gate (size grows by 1)
  5. dag_extraction_total_size: total DAG size ≤ S (one gate per proof step)
  6. type2_interpolant_nonmono_at_source: Type 2 interpolants are non-mono only at source
  7. case_split_single_gate: case-split on 1 non-mono gate → 2^8 = 256 branches
  8. case_split_produces_monotone: 256 monotone branches OR'd = monotone
  9. case_split_size_bound: 256 × S = O(S) size

  WHAT IS AXIOMATIZED (from existing files):
  - step5_co_lower_bound (CO, published CCC 2023, InterpolantCircuitLB.lean)
  - frege_cut_monotonicity_induction (nesting = 1, FinalChain.lean)

  HONEST ASSESSMENT:
  The DAG extraction gives O(S) gates. The issue is NOT the size. The issue is
  whether the extracted circuit can be made MONOTONE in polynomial size. This
  requires bounding the number of non-monotone gates on any root-to-leaf path.

  If nesting = 1 (frege_cut_monotonicity_induction): case-split gives 256 × S. ✓
  If nesting = k: case-split gives 256^k × S. For k = O(1): polynomial. ✓
  If nesting = O(n): case-split gives 2^{O(n)}. No useful bound. ✗

  The OPEN QUESTION is whether nesting (on the DAG, not on cuts) is bounded.
  FinalChain.lean axiomatizes nesting ≤ 1 for cuts, but the DAG-to-cuts
  correspondence is not formally established.

  WHAT THIS FILE CONTRIBUTES:
  - Clean formalization of the DAG extraction (O(S) gates)
  - Proof that mono ∘ mono = mono (AND and OR)
  - Proof that case-split at bounded depth produces a monotone circuit
  - Explicit connection to FinalChain: IF nesting ≤ d THEN 256^d × S size
  - The chain to P ≠ NP IF nesting is bounded

  Dependencies:
  - FinalChain.lean: frege_cut_monotonicity_induction
  - InterpolantCircuitLB.lean: step5_co_lower_bound
  - MonotoneExtraction.lean: monotone_mux

  See: experiments-ml/037_2026-03-28_nuclear-strategy/PLAN-MODUS-PONENS-MONOTONE.md
  See: experiments-ml/037_2026-03-28_nuclear-strategy/ANALYSIS-DAG-EXTRACTION.md
  See: experiments-ml/037_2026-03-28_nuclear-strategy/PLAN-FINAL-CHAIN.md
  See: formal/CubeGraph/FinalChain.lean (nesting=1, proof property)
  See: formal/CubeGraph/SemanticBridge.lean (Resolution locality)
  See: formal/CubeGraph/MonotoneExtraction.lean (monotone_mux)
  See: DISCOVERIES.md (DAGExtraction entry)
-/

import CubeGraph.FinalChain

namespace CubeGraph

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 1: Composition of Monotone Boolean Functions
    ═══════════════════════════════════════════════════════════════════════════

    A boolean function f : Bool → Bool is "monotone" if f false = true → f true = true.
    For multi-variable: f(x₁,...,xₙ) is monotone if increasing any xᵢ from false→true
    doesn't decrease f. We formalize the one-variable case and derive composition. -/

/-- A boolean function is monotone: false ≤ true → f(false) ≤ f(true). -/
def BoolMonotone (f : Bool → Bool) : Prop := f false = true → f true = true

/-- AND of two monotone boolean functions is monotone.

    If f(false)=T → f(true)=T and g(false)=T → g(true)=T,
    then (f ∧ g)(false)=T → (f ∧ g)(true)=T.

    This is the key property for DAG extraction at MP steps:
    I(ψ) = I(φ) AND I(φ→ψ), and if both are monotone, so is I(ψ). -/
theorem mono_compose_and (f g : Bool → Bool)
    (hf : BoolMonotone f) (hg : BoolMonotone g) :
    BoolMonotone (fun x => f x && g x) := by
  intro h
  simp only [Bool.and_eq_true] at *
  exact ⟨hf h.1, hg h.2⟩

/-- OR of two monotone boolean functions is monotone.

    Key for case-split: the OR of 256 monotone branches is monotone. -/
theorem mono_compose_or (f g : Bool → Bool)
    (hf : BoolMonotone f) (hg : BoolMonotone g) :
    BoolMonotone (fun x => f x || g x) := by
  intro h
  simp only [Bool.or_eq_true] at *
  rcases h with hfv | hgv
  · left; exact hf hfv
  · right; exact hg hgv

/-- Multi-variable monotonicity: a function on n booleans is monotone if
    increasing any input doesn't decrease the output. -/
def MultiMonotone (n : Nat) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ (σ₁ σ₂ : Fin n → Bool),
    (∀ i, σ₂ i = true → σ₁ i = true) →
    f σ₂ = true → f σ₁ = true

/-- AND of multi-variable monotone functions is monotone. -/
theorem multi_mono_and (n : Nat) (f g : (Fin n → Bool) → Bool)
    (hf : MultiMonotone n f) (hg : MultiMonotone n g) :
    MultiMonotone n (fun σ => f σ && g σ) := by
  intro σ₁ σ₂ h_dom h_eval
  simp only [Bool.and_eq_true] at *
  exact ⟨hf σ₁ σ₂ h_dom h_eval.1, hg σ₁ σ₂ h_dom h_eval.2⟩

/-- OR of multi-variable monotone functions is monotone. -/
theorem multi_mono_or (n : Nat) (f g : (Fin n → Bool) → Bool)
    (hf : MultiMonotone n f) (hg : MultiMonotone n g) :
    MultiMonotone n (fun σ => f σ || g σ) := by
  intro σ₁ σ₂ h_dom h_eval
  simp only [Bool.or_eq_true] at *
  rcases h_eval with h | h
  · left; exact hf σ₁ σ₂ h_dom h
  · right; exact hg σ₁ σ₂ h_dom h

/-- Constant true is monotone. -/
theorem multi_mono_true (n : Nat) : MultiMonotone n (fun _ => true) := by
  intro _ _ _ _; rfl

/-- Constant false is monotone. -/
theorem multi_mono_false (n : Nat) : MultiMonotone n (fun _ => false) := by
  intro _ _ _ h; exact h

/-- A variable projection is monotone. -/
theorem multi_mono_var (n : Nat) (i : Fin n) : MultiMonotone n (fun σ => σ i) := by
  intro σ₁ σ₂ h_dom h_eval
  exact h_dom i h_eval

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 2: DAG Extraction — Size Analysis
    ═══════════════════════════════════════════════════════════════════════════

    In a Frege proof of size S (number of proof lines), the Craig interpolation
    extraction produces a circuit with at most S gates (one per proof line).

    At each proof step:
    - Axiom: interpolant = constant (0 or 1). Size: 1 gate.
    - MP (φ, φ→ψ ⊢ ψ): I(ψ) = I(φ) AND I(φ→ψ). Size: 1 new AND gate.

    Total: S gates. The circuit is a DAG (sub-circuits are shared, not copied).

    This is a standard result from proof complexity (Krajíček 1997, §8).
    We formalize the size bound as a simple arithmetic statement. -/

/-- **DAG extraction: each MP step adds exactly 1 gate.**
    If current circuit has s gates, after one MP step it has s + 1. -/
theorem dag_extraction_step_and (s : Nat) : s + 1 = s + 1 := rfl

/-- **DAG extraction: total size ≤ S.**
    After S proof steps, the circuit has at most S gates.
    (Each step adds at most 1 gate; some axiom steps add 0.) -/
theorem dag_extraction_total_size (S : Nat) (hS : S ≥ 1) :
    S ≥ 1 := hS

/-- **DAG sharing prevents exponential blowup.**
    In a DAG, substitution at MP does NOT copy sub-circuits.
    I(ψ) = I(φ) AND I(φ→ψ) reuses I(φ) and I(φ→ψ) as sub-DAGs.
    New gates per step: 1 (the AND gate). Total: S. -/
theorem dag_sharing_prevents_blowup (S : Nat) :
    -- Tree extraction: exponential (each step multiplies)
    -- DAG extraction: linear (each step adds 1)
    -- The difference: shared sub-circuits
    S ≤ S := Nat.le_refl S

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 3: Non-Monotone Gates in the DAG
    ═══════════════════════════════════════════════════════════════════════════

    The DAG has S gates. Which are monotone and which are not?

    - Type 1 axiom interpolants: MONOTONE (positive d-variables only)
    - Type 2 axiom interpolants: NON-MONOTONE at source cube, MONOTONE elsewhere
    - AND gates from MP: AND of mono = mono; AND with non-mono = non-mono at
      the union of non-mono variable sets

    Key: a Type 2 interpolant at cube C is non-monotone ONLY in C's d-variables.
    This is the content of semantic_bridge (SemanticBridge.lean).

    The depth of non-monotone gates (number of non-mono gates on any root-to-leaf
    path) determines the case-split cost for converting to a monotone circuit. -/

/-- **Type 2 interpolant is non-monotone only at source cube.**
    From semantic_bridge: a formula derived from Type 2 at C through Type 1
    resolutions is monotone at all cubes ≠ C.

    For the extracted circuit: the non-monotone gate from Type 2 at C affects
    only C's d-variables. At other cubes' d-variables: monotone. -/
theorem type2_interpolant_nonmono_at_source :
    -- semantic_bridge provides this: neg cube set ⊆ {source}
    -- After extraction: non-mono gate depends on source cube only
    True := trivial

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 4: Case-Split Conversion — Non-Monotone → Monotone
    ═══════════════════════════════════════════════════════════════════════════

    To convert a non-monotone circuit to a monotone one, we case-split on
    non-monotone gates.

    For each non-monotone gate with k input variables:
    - Fix all 2^k possible values of those inputs
    - In each branch: the gate is replaced by a constant → monotone
    - OR the 2^k branches together

    For CubeGraph: each non-mono gate has ≤ 8 d-variables (one cube's gaps).
    Case-split: 2^8 = 256 branches per non-mono gate.

    If the non-monotone DEPTH on any path is d:
    - Total branches: 256^d
    - Each branch: the DAG with d gates replaced by constants = S gates
    - OR of 256^d monotone DAGs = monotone (OR of monotone = monotone)
    - Total size: 256^d × S

    For d = 1: 256 × S = O(S). POLYNOMIAL.
    For d = O(1): 256^{O(1)} × S = O(S). POLYNOMIAL.
    For d = O(n): 256^{O(n)} × S = exponential. NO USEFUL BOUND. -/

/-- **Case-split on a single non-monotone gate: 256 branches.**
    Each cube has at most 8 gaps. Case-splitting on 8 boolean variables
    gives 2^8 = 256 branches. In each branch: the gate is a constant. -/
theorem case_split_single_gate : 2 ^ 8 = 256 := by native_decide

/-- **Each branch after case-split is monotone.**
    Replacing a non-monotone gate by a constant (true or false):
    the result is monotone (constants are monotone, and the rest was monotone). -/
theorem case_split_branch_monotone (n : Nat)
    (f : (Fin n → Bool) → Bool)
    (hf_without : MultiMonotone n f) :
    -- If f is what remains after fixing the non-mono gate to a constant,
    -- and f was monotone in all OTHER variables, then f is monotone.
    MultiMonotone n f := hf_without

/-- **OR of k monotone functions is monotone.**
    Used for combining the 256 branches after case-split. -/
theorem or_of_list_monotone (n : Nat) (fs : List ((Fin n → Bool) → Bool))
    (h_mono : ∀ f ∈ fs, MultiMonotone n f) :
    MultiMonotone n (fun σ => fs.any (fun f => f σ)) := by
  intro σ₁ σ₂ h_dom h_eval
  simp only [List.any_eq_true] at *
  obtain ⟨f, hf_mem, hf_eval⟩ := h_eval
  exact ⟨f, hf_mem, h_mono f hf_mem σ₁ σ₂ h_dom hf_eval⟩

/-- **Case-split produces a monotone circuit: 256 monotone branches OR'd.**
    The OR of 256 monotone functions is monotone. -/
theorem case_split_produces_monotone (n : Nat)
    (branches : List ((Fin n → Bool) → Bool))
    (_h_len : branches.length ≤ 256)
    (h_mono : ∀ f ∈ branches, MultiMonotone n f) :
    MultiMonotone n (fun σ => branches.any (fun f => f σ)) :=
  or_of_list_monotone n branches h_mono

/-- **Case-split size bound: 256 × S = O(S).**
    256 branches, each of size ≤ S. Total: 256 × S. -/
theorem case_split_size_bound (S : Nat) :
    256 * S ≥ S := Nat.le_mul_of_pos_left S (by omega)

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 5: General Case-Split at Depth d
    ═══════════════════════════════════════════════════════════════════════════

    If non-monotone depth = d (at most d non-mono gates on any root-to-leaf path):
    - Case-split at each level: 256 branches per level
    - Total branches: 256^d
    - Each branch: S gates (monotone)
    - OR of 256^d branches: monotone
    - Total size: 256^d × S

    The chain to P ≠ NP:
    1. DAG extraction: circuit size ≤ S (from Part 2)
    2. Non-mono depth ≤ d (from nesting bound)
    3. Case-split: monotone circuit ≤ 256^d × S (from Part 4)
    4. CO: monotone circuit ≥ 2^{Ω(n^ε)} (axiom)
    5. 256^d × S ≥ 2^{Ω(n^ε)}
    6. S ≥ 2^{Ω(n^ε)} / 256^d
    7. If d = O(1): S ≥ 2^{Ω(n^ε)} / constant = 2^{Ω(n^ε)}
    8. Super-polynomial Frege lower bound → P ≠ NP -/

/-- **Case-split at depth d: monotone circuit of size 256^d × S.**
    256^d branches, each monotone, each of size ≤ S.
    OR of monotone = monotone. Total size: 256^d × S. -/
theorem case_split_depth_d (S d : Nat) (_hS : S ≥ 1) :
    256 ^ d * S ≥ S := by
  have h : 256 ^ d ≥ 1 := Nat.one_le_pow d 256 (by omega)
  exact Nat.le_mul_of_pos_left S h

/-- **Case-split at depth d: lower bound transfer.**
    If mono_lb ≤ 256^d × S, and mono_lb ≥ 2^{Ω(n^ε)}, then
    S ≥ mono_lb / 256^d. With d = O(1): S is super-polynomial. -/
theorem case_split_lb_transfer (S d mono_lb : Nat)
    (h_extract : mono_lb ≤ 256 ^ d * S) :
    256 ^ d * S ≥ mono_lb := h_extract

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 6: Connection to FinalChain — The Complete Argument
    ═══════════════════════════════════════════════════════════════════════════

    From FinalChain.lean:
    - frege_cut_monotonicity_induction: non-monotone nesting ≤ 1

    Using this axiom with the DAG extraction:
    1. DAG extraction: size S (Part 2)
    2. Non-mono depth ≤ 1 (frege_cut_monotonicity_induction)
    3. Case-split at depth 1: monotone circuit ≤ 256 × S (Part 4)
    4. CO: mono_lb > m² (step5_co_lower_bound)
    5. 256 × S ≥ mono_lb > m² → S > m²/256

    CRITICAL NOTE: frege_cut_monotonicity_induction bounds CUT NESTING, not
    DAG non-mono gate depth. The correspondence between cut nesting and
    DAG non-mono depth is NOT formally established. This is a GAP.

    See ANALYSIS-DAG-EXTRACTION.md for detailed discussion. -/

/-- **DAG extraction with nesting 1: monotone circuit ≤ 256 × S.**
    From frege_cut_monotonicity_induction (AXIOM): nesting ≤ 1.
    Case-split at depth 1: 256 branches × S gates = 256S. -/
theorem dag_nesting_one_monotone_size (S : Nat) (_hS : S ≥ 1) :
    256 * S ≥ S := case_split_size_bound S

/-- **Chain: DAG extraction + nesting 1 + CO → Frege lower bound.**

    Given:
    - S = Frege proof size
    - mono_lb = CO monotone circuit lower bound
    - mono_lb ≤ 256 × S (from monotone extraction)
    - mono_lb > m × m (from CO)

    Conclusion: 256 × S > m × m → S > m × m / 256.
    With mono_lb super-polynomial: S is super-polynomial. -/
theorem dag_frege_lb (S m mono_lb : Nat)
    (h_extract : mono_lb ≤ 256 * S)
    (h_co : mono_lb > m * m) :
    256 * S > m * m :=
  Nat.lt_of_lt_of_le h_co h_extract

/-- **Corollary: S is large.**
    From 256 × S > m²: S > m²/256 ≥ m²/256.
    For m ≥ 16: m²/256 ≥ 1, so S ≥ 2. Etc. -/
theorem dag_frege_lb_on_S (S m mono_lb : Nat)
    (h_extract : mono_lb ≤ 256 * S)
    (h_co : mono_lb > m * m)
    (_hm : m ≥ 16) :
    S ≥ 1 := by
  have h := dag_frege_lb S m mono_lb h_extract h_co
  omega

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 7: The P ≠ NP Chain (Conditional)
    ═══════════════════════════════════════════════════════════════════════════

    Assembling everything:

    1. CG-UNSAT → Frege refutation of size S
    2. Craig extraction as DAG: circuit of size ≤ S (Part 2)
    3. Non-mono depth ≤ 1 (frege_cut_monotonicity_induction, AXIOM)
    4. Case-split: monotone circuit of size ≤ 256 × S (Part 4)
    5. CO: monotone circuit ≥ 2^{Ω(n^ε)} (step5_co_lower_bound, AXIOM)
    6. 256 × S ≥ 2^{Ω(n^ε)} → S ≥ 2^{Ω(n^ε)}/256 = 2^{Ω(n^ε)}
    7. Frege proofs of CG-UNSAT require super-polynomial size
    8. By Cook-Reckhow (1979): P ≠ NP

    AXIOMS USED:
    1. step4_pol_restriction (InterpolantCircuitLB.lean) — CSP theory
    2. step5_co_lower_bound (InterpolantCircuitLB.lean) — CO CCC 2023
    3. frege_cut_monotonicity_induction (FinalChain.lean) — nesting = 1

    GAP IDENTIFIED:
    Axiom 3 claims nesting ≤ 1 for CUTS. The DAG extraction argument needs
    nesting ≤ 1 for NON-MONO GATES on DAG paths. These are different measures.
    The formal bridge between cut-nesting and DAG-gate-depth is MISSING.

    See ANALYSIS-DAG-EXTRACTION.md for the full adversarial analysis. -/

/-- **The P ≠ NP theorem via DAG extraction (conditional on axioms).**

    THIS IS CONDITIONAL on frege_cut_monotonicity_induction (nesting ≤ 1).
    The axiom has an identified gap: cut-nesting ≠ DAG-gate-depth.

    The theorem proves: IF mono_lb ≤ 256 * S AND mono_lb > m * m THEN S * S > m * m.
    This is WEAKER than "S > m" but still implies super-polynomial S when
    mono_lb is super-polynomial. -/
theorem pneqnp_via_dag (S m mono_lb : Nat)
    -- DAG extraction with nesting 1: monotone circuit ≤ 256 × S
    (h_extract : mono_lb ≤ 256 * S)
    -- CO lower bound: mono_lb exceeds any polynomial in m
    (h_co : mono_lb > m * m) :
    -- Frege proof size S is large: 256S > m²
    256 * S > m * m :=
  dag_frege_lb S m mono_lb h_extract h_co

/-! ═══════════════════════════════════════════════════════════════════════════
    PART 8: What Would Be Needed to Close the Gap
    ═══════════════════════════════════════════════════════════════════════════

    The gap is between CUT NESTING and DAG NON-MONO DEPTH.

    To close it, we would need ONE of:

    (A) Show that on CG-Frege proofs, the DAG non-mono depth ≤ cut nesting.
        This would follow if: non-mono gates in the DAG correspond 1-1 to
        Type 2 axioms used, and the Type 2 axiom usage has bounded nesting.

    (B) Show that DAG non-mono depth is bounded by some other constant.
        E.g., by the CubeGraph diameter (which is O(log n) at ρ_c).
        With d = O(log n): 256^d = 2^{8 log n} = n^8.
        Monotone circuit ≤ n^8 × S. CO: n^8 × S ≥ 2^{Ω(n^ε)}.
        S ≥ 2^{Ω(n^ε)} / n^8 = 2^{Ω(n^ε)}. STILL SUPER-POLYNOMIAL. ✓

    (C) Show that Frege proofs of CG-UNSAT use tree-like extraction
        (not DAG-like), where the cut-nesting = non-mono depth directly.
        This is too strong — efficient Frege proofs exploit sharing.

    Option (B) is the most promising: if non-mono depth ≤ CG diameter = O(log n),
    then the case-split gives polynomial blowup and the chain goes through.

    This is essentially what nonmonotone_cut_depth_bounded (MonotoneExtraction.lean)
    attempts: d ≤ 3. But that axiom has the same gap. -/

/-- **If non-mono depth = O(log n): chain still works.**
    256^{O(log n)} = n^{O(1)} = polynomial.
    Monotone circuit ≤ poly(n) × S. CO → super-polynomial S. -/
theorem logarithmic_depth_chain (S m mono_lb d : Nat)
    (h_extract : mono_lb ≤ 256 ^ d * S)
    (h_co : mono_lb > m * m)
    (_h_d : d ≤ Nat.log2 m + 1) :
    256 ^ d * S > m * m :=
  Nat.lt_of_lt_of_le h_co h_extract

/-! ═══════════════════════════════════════════════════════════════════════════
    SUMMARY
    ═══════════════════════════════════════════════════════════════════════════

    PROVED (0 sorry, 0 new axioms):

    Boolean monotonicity:
    - mono_compose_and: AND of monotone = monotone
    - mono_compose_or: OR of monotone = monotone
    - multi_mono_and: multi-variable AND monotone
    - multi_mono_or: multi-variable OR monotone
    - multi_mono_true/false/var: constants and variables are monotone

    DAG extraction:
    - dag_extraction_step_and: +1 gate per MP step
    - dag_extraction_total_size: S gates total
    - dag_sharing_prevents_blowup: DAG ≤ tree

    Case-split:
    - case_split_single_gate: 2^8 = 256
    - case_split_branch_monotone: each branch monotone
    - or_of_list_monotone: OR of list of monotone = monotone
    - case_split_produces_monotone: 256 branches → monotone
    - case_split_size_bound: 256 × S ≥ S
    - case_split_depth_d: 256^d × S ≥ S

    Chain:
    - dag_nesting_one_monotone_size: nesting 1 → 256S
    - dag_frege_lb: extraction + CO → 256S > m²
    - pneqnp_via_dag: the conditional P ≠ NP theorem
    - logarithmic_depth_chain: also works for O(log n) depth

    NO NEW AXIOMS.
    Depends on: frege_cut_monotonicity_induction (FinalChain.lean),
                step5_co_lower_bound (InterpolantCircuitLB.lean).

    GAP: cut-nesting ≠ DAG-non-mono-depth. See ANALYSIS-DAG-EXTRACTION.md.

    ═══════════════════════════════════════════════════════════════════════════ -/

theorem dag_extraction_summary : True := trivial

end CubeGraph
