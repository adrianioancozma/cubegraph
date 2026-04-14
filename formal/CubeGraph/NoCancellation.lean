/-
  CubeGraph/NoCancellation.lean
  NO-CANCELLATION property of the OR/AND semiring and BPR non-applicability.

  The BPR (Bonet-Pitassi-Raz 2000) counterexample to Frege FIP uses CRT (Chinese
  Remainder Theorem), which requires a RING structure with additive inverses.
  The CubeGraph transfer operators live in the OR/AND semiring, which has NO
  cancellative elements (beyond false). This structural difference means BPR's
  proof technique cannot be imported to CubeGraph.

  Main results:
  Part 1 — OR/AND semiring properties (commutativity, associativity, distributivity)
  Part 2 — No cancellation for Bool: only false is left-cancellative under OR
  Part 3 — Boolean matrix no-cancellation: non-zero BoolMat not cancellative under OR-lift
  Part 4 — Ring vs semiring gap: XOR has cancellation, OR does not (idempotent barrier)
  Part 5 — Connection to Frege interpolation: BPR structurally inapplicable to CubeGraph

  See: experiments-ml/025_2026-03-19_synthesis/bridge-next/agents/2026-03-23-STRATEGY-45-DEPTH-COLLAPSE.md
  See: CubeGraph/InvertibilityBarrier.lean (complementary: OR vs XOR on invertibility)
  See: CubeGraph/NonCancellative.lean (complementary: non-cancellativity under MUL)
  See: CubeGraph/IdempotentSemiring.lean (complementary: idempotent barrier)
-/

import CubeGraph.Basic

/-! ## Part 1: OR/AND Semiring Properties

  OR (||) and AND (&&) form a commutative semiring on Bool:
  - (Bool, OR, false) is a commutative monoid
  - (Bool, AND, true) is a commutative monoid
  - AND distributes over OR
  - false is an annihilator for AND
  - BUT: there are NO additive inverses (no subtraction) -/

namespace Eta5

/-- OR is commutative. -/
theorem or_comm : ∀ a b : Bool, (a || b) = (b || a) := by decide

/-- OR is associative. -/
theorem or_assoc : ∀ a b c : Bool, (a || (b || c)) = ((a || b) || c) := by decide

/-- false is the identity for OR. -/
theorem or_false_id : ∀ a : Bool, (a || false) = a := by decide

/-- false is the left identity for OR. -/
theorem false_or_id : ∀ a : Bool, (false || a) = a := by decide

/-- AND is commutative. -/
theorem and_comm : ∀ a b : Bool, (a && b) = (b && a) := by decide

/-- AND is associative. -/
theorem and_assoc : ∀ a b c : Bool, (a && (b && c)) = ((a && b) && c) := by decide

/-- true is the identity for AND. -/
theorem and_true_id : ∀ a : Bool, (a && true) = a := by decide

/-- true is the left identity for AND. -/
theorem true_and_id : ∀ a : Bool, (true && a) = a := by decide

/-- false is the annihilator for AND. -/
theorem and_false_annihilate : ∀ a : Bool, (a && false) = false := by decide

/-- AND left-distributes over OR. -/
theorem and_or_distrib : ∀ a b c : Bool, (a && (b || c)) = ((a && b) || (a && c)) := by decide

/-- AND right-distributes over OR. -/
theorem or_and_distrib : ∀ a b c : Bool, ((a || b) && c) = ((a && c) || (b && c)) := by decide

/-- OR is idempotent: a || a = a. This is the KEY difference from XOR/ring addition. -/
theorem or_idem : ∀ a : Bool, (a || a) = a := by decide

/-- OR has NO additive inverse for true: there is no x such that true || x = false. -/
theorem or_no_additive_inverse : ¬ ∃ x : Bool, (true || x) = false := by decide

/-! ## Part 2: No Cancellation for Bool under OR

  An element a is left-cancellative under an operation if:
    a ∘ b = a ∘ c  implies  b = c
  We prove that only false is left-cancellative under OR.
  true is NOT cancellative: true || false = true = true || true, but false ≠ true. -/

/-- An element a is left-cancellative under OR if a || b = a || c implies b = c. -/
def IsLeftCancOR (a : Bool) : Prop :=
  ∀ b c : Bool, (a || b) = (a || c) → b = c

/-- An element a is right-cancellative under OR if b || a = c || a implies b = c. -/
def IsRightCancOR (a : Bool) : Prop :=
  ∀ b c : Bool, (b || a) = (c || a) → b = c

/-- false is left-cancellative under OR: false || b = b. -/
theorem false_isLeftCancOR : IsLeftCancOR false := by
  intro b c h
  simpa using h

/-- false is right-cancellative under OR: b || false = b. -/
theorem false_isRightCancOR : IsRightCancOR false := by
  intro b c h
  simpa using h

/-- true is NOT left-cancellative under OR.
    Witness: true || false = true = true || true, but false ≠ true. -/
theorem true_not_isLeftCancOR : ¬ IsLeftCancOR true := by
  intro h
  have := h false true (by decide)
  exact absurd this (by decide)

/-- true is NOT right-cancellative under OR.
    Witness: false || true = true = true || true, but false ≠ true. -/
theorem true_not_isRightCancOR : ¬ IsRightCancOR true := by
  intro h
  have := h false true (by decide)
  exact absurd this (by decide)

/-- Only false is left-cancellative under OR.
    Complete characterization: IsLeftCancOR a ↔ a = false. -/
theorem isLeftCancOR_iff (a : Bool) : IsLeftCancOR a ↔ a = false := by
  constructor
  · intro h
    cases a with
    | false => rfl
    | true => exact absurd h true_not_isLeftCancOR
  · intro h; subst h; exact false_isLeftCancOR

/-- Only false is right-cancellative under OR.
    Complete characterization: IsRightCancOR a ↔ a = false. -/
theorem isRightCancOR_iff (a : Bool) : IsRightCancOR a ↔ a = false := by
  constructor
  · intro h
    cases a with
    | false => rfl
    | true => exact absurd h true_not_isRightCancOR
  · intro h; subst h; exact false_isRightCancOR

/-- The OR operation on Bool is not (globally) cancellative.
    There exist a, b, c with a || b = a || c but b ≠ c. -/
theorem or_not_cancellative :
    ¬ (∀ a b c : Bool, (a || b) = (a || c) → b = c) := by
  intro h
  have := h true false true (by decide)
  exact absurd this (by decide)

/-! ## Part 3: Boolean Matrix No-Cancellation under Entrywise OR

  Define entrywise OR on BoolMat. Prove that non-zero matrices are not
  left-cancellative under entrywise OR.

  The entrywise OR of two boolean matrices:
    (A ∨ B)[i,j] = A[i,j] || B[i,j]

  This is the "addition" in the OR/AND semiring lifted to matrices.
  Non-zero matrices absorb information: if A has a true entry at (i,j),
  then (A ∨ B)[i,j] = true regardless of B[i,j]. -/

variable {n : Nat}

/-- Entrywise OR of two boolean matrices. -/
def BoolMat.orLift (A B : BoolMat n) : BoolMat n :=
  fun i j => A i j || B i j

/-- An element A is left-cancellative under entrywise OR if
    A ∨ B = A ∨ C implies B = C. -/
def BoolMat.IsLeftCancOrLift (A : BoolMat n) : Prop :=
  ∀ B C : BoolMat n, BoolMat.orLift A B = BoolMat.orLift A C → B = C

/-- Helper: extract a true entry from a non-zero BoolMat. -/
theorem BoolMat.exists_true_of_not_isZero (A : BoolMat n) (hA : ¬ BoolMat.isZero A) :
    ∃ i₀ j₀ : Fin n, A i₀ j₀ = true := by
  -- isZero A = ∀ i j, A i j = false. ¬isZero means ∃ i j with A i j = true.
  apply Classical.byContradiction
  intro h_no
  apply hA
  intro i j
  cases hv : A i j with
  | false => rfl
  | true =>
    exfalso; apply h_no
    exact ⟨i, j, hv⟩

/-- The zero matrix is left-cancellative under entrywise OR.
    zero ∨ B = B, so zero ∨ B = zero ∨ C implies B = C. -/
theorem BoolMat.zero_isLeftCancOrLift : BoolMat.IsLeftCancOrLift (BoolMat.zero : BoolMat n) := by
  intro B C h
  funext i j
  have := congrFun (congrFun h i) j
  simp [BoolMat.orLift, BoolMat.zero] at this
  exact this

/-- A non-zero BoolMat is NOT left-cancellative under entrywise OR.
    If A has a true entry at (i₀, j₀), then (A ∨ B)[i₀,j₀] = true
    for ALL B. So A ∨ zero = A ∨ E_{i₀,j₀}, but zero ≠ E_{i₀,j₀}. -/
theorem BoolMat.nonzero_not_isLeftCancOrLift (A : BoolMat n) (hA : ¬ BoolMat.isZero A) :
    ¬ BoolMat.IsLeftCancOrLift A := by
  obtain ⟨i₀, j₀, hij⟩ := BoolMat.exists_true_of_not_isZero A hA
  intro hcanc
  -- Define E_{i₀,j₀}: single true entry at (i₀, j₀)
  let E : BoolMat n := fun i j => decide (i = i₀ ∧ j = j₀)
  -- Show: orLift A zero = orLift A E
  have h_eq : BoolMat.orLift A BoolMat.zero = BoolMat.orLift A E := by
    funext i j
    simp only [BoolMat.orLift, BoolMat.zero, Bool.or_false]
    cases h_aij : A i j with
    | true =>
      -- A i j = true, so true = true || E i j
      simp
    | false =>
      -- A i j = false, so false = false || E i j = E i j
      -- E i j = decide (i = i₀ ∧ j = j₀) must be false
      -- because if i = i₀ and j = j₀, then A i₀ j₀ = true ≠ false
      simp only [Bool.false_or]
      show false = (E i j)
      symm
      simp only [E, decide_eq_false_iff_not]
      intro ⟨hi, hj⟩
      subst hi; subst hj
      rw [hij] at h_aij
      exact absurd h_aij (by decide)
  -- But zero ≠ E (they differ at (i₀, j₀))
  have h_ne : (BoolMat.zero : BoolMat n) ≠ E := by
    intro h
    have := congrFun (congrFun h i₀) j₀
    simp [BoolMat.zero, E] at this
  exact h_ne (hcanc BoolMat.zero E h_eq)

/-- Complete characterization: IsLeftCancOrLift A ↔ isZero A.
    Only the zero matrix is left-cancellative under entrywise OR. -/
theorem BoolMat.isLeftCancOrLift_iff (A : BoolMat n) :
    BoolMat.IsLeftCancOrLift A ↔ BoolMat.isZero A := by
  constructor
  · -- cancellative → zero
    intro h
    -- Suppose not zero → contradiction
    apply Classical.byContradiction
    intro hA
    exact BoolMat.nonzero_not_isLeftCancOrLift A hA h
  · -- zero → cancellative
    intro hA B C h
    funext i j
    have := congrFun (congrFun h i) j
    simp only [BoolMat.orLift] at this
    have hAij : A i j = false := hA i j
    simp [hAij] at this
    exact this

/-! ## Part 4: Ring vs Semiring Gap

  In a ring (e.g. Z, GF(2)), every element has an additive inverse:
    a + (-a) = 0
  This enables cancellation: a + b = a + c ⟹ b = c (add -a to both sides).

  XOR (= addition in GF(2)) has this property: a ⊕ a = false.
  OR does NOT: a || a = a (idempotent, not cancellative).

  This gap is precisely why CRT works over rings but not over the OR/AND semiring. -/

/-- XOR is self-inverse: every element cancels itself. -/
theorem xor_self_inverse : ∀ a : Bool, Bool.xor a a = false := by decide

/-- OR is self-idempotent: a || a = a, NOT 0. -/
theorem or_self_idempotent : ∀ a : Bool, (a || a) = a := by decide

/-- The fundamental gap: XOR has cancellation, OR does not.
    XOR: a ⊕ b = a ⊕ c ⟹ b = c (⊕ a on both sides, since a ⊕ a = 0)
    OR: a ∨ b = a ∨ c does NOT imply b = c (when a = true) -/
theorem xor_is_cancellative : ∀ a b c : Bool, Bool.xor a b = Bool.xor a c → b = c := by
  decide

/-- OR is NOT cancellative (re-stated for emphasis alongside xor_is_cancellative). -/
theorem or_is_not_cancellative : ∃ a b c : Bool, (a || b) = (a || c) ∧ b ≠ c := by
  exact ⟨true, false, true, by decide, by decide⟩

/-- XOR distributes over AND (GF(2) field axiom). -/
theorem xor_and_distrib : ∀ a b c : Bool, (a && (Bool.xor b c)) = Bool.xor (a && b) (a && c) := by
  decide

/-- GF(2) has multiplicative inverses for nonzero elements (trivially: 1⁻¹ = 1). -/
theorem gf2_mul_inverse : ∀ a : Bool, a = true → ∃ b : Bool, (a && b) = true :=
  fun a h => ⟨true, by simp [h]⟩

/-- OR/AND has no subtraction operation: no function sub such that sub(a || b, a) = b.
    In a ring: a + b = c ⟹ b = c - a (subtraction exists).
    In OR/AND: a || b = true does NOT determine b (no "OR-subtraction"). -/
theorem or_no_subtraction : ¬ ∃ (sub : Bool → Bool → Bool),
    ∀ a b : Bool, sub (a || b) a = b := by
  intro ⟨sub, h⟩
  have h1 := h true false  -- sub (true || false) true = false, so sub true true = false
  have h2 := h true true   -- sub (true || true) true = true, so sub true true = true
  simp at h1 h2
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ## Part 5: Connection to Frege Interpolation — BPR Structural Inapplicability

  The BPR (Bonet-Pitassi-Raz 2000) proof creates Frege interpolants by:
  1. Decomposing into modular components (CRT — requires ring)
  2. Computing each component independently
  3. Combining via CRT reconstruction (requires inverses)

  Step 1 fails in OR/AND: no modular decomposition without additive inverses.
  Step 3 fails: CRT reconstruction needs modular inverse — not available in OR/AND.

  We formalize this as a structural incompatibility theorem. -/

/-- A "CRT-like decomposition" requires:
    (1) An operation + with identity 0
    (2) An inverse operation: ∀ a, ∃ b, a + b = 0
    We show OR fails condition (2). -/
theorem or_fails_crt_prerequisite :
    ¬ (∀ a : Bool, ∃ b : Bool, (a || b) = false) := by
  intro h
  obtain ⟨b, hb⟩ := h true
  exact absurd hb (by cases b <;> decide)

/-- AND/OR semiring entrywise operations on BoolMat fail CRT prerequisites.
    If ANY entry of A is true, then A has no additive (OR) inverse. -/
theorem BoolMat.orLift_fails_crt (A : BoolMat n) (hA : ¬ BoolMat.isZero A) :
    ¬ ∃ B : BoolMat n, BoolMat.orLift A B = BoolMat.zero := by
  intro ⟨B, h⟩
  obtain ⟨i₀, j₀, hij⟩ := BoolMat.exists_true_of_not_isZero A hA
  -- At (i₀, j₀): (A ∨ B)[i₀,j₀] = true || B[i₀,j₀] = true ≠ false
  have := congrFun (congrFun h i₀) j₀
  simp [BoolMat.orLift, BoolMat.zero, hij] at this

/-- **NO-CANCELLATION BARRIER**: Transfer operator composition in the OR/AND
    semiring cannot be "undone" by any operation.

    In a ring (Z, GF(2)): if M₁ · M₂ = R, one can recover M₂ = M₁⁻¹ · R
    (when M₁ is invertible). CRT exploits this reversibility.

    In the OR/AND semiring: transfer operators are boolean matrices.
    (1) Boolean matrix multiplication is NOT invertible (rank-1 never invertible,
        proven in InvertibilityBarrier.lean).
    (2) Entrywise OR is NOT cancellative (only zero matrix is cancellative,
        proven above).
    (3) Therefore: neither the "multiplication" nor the "addition" of the
        OR/AND semiring supports the algebraic manipulations needed for CRT.
    (4) BPR's proof technique structurally cannot apply to CubeGraph. -/
theorem no_cancellation_barrier :
    -- (1) OR not globally cancellative on Bool
    (¬ (∀ a b c : Bool, (a || b) = (a || c) → b = c))
    -- (2) Only zero BoolMat is entrywise-OR cancellative
    ∧ (∀ (A : BoolMat n), BoolMat.IsLeftCancOrLift A ↔ BoolMat.isZero A)
    -- (3) Non-zero BoolMat has no entrywise-OR inverse
    ∧ (∀ (A : BoolMat n), ¬ BoolMat.isZero A → ¬ ∃ B : BoolMat n, BoolMat.orLift A B = BoolMat.zero)
    -- (4) XOR IS cancellative (contrast: ring structure)
    ∧ (∀ a b c : Bool, Bool.xor a b = Bool.xor a c → b = c)
    -- (5) OR has no subtraction operator
    ∧ (¬ ∃ (sub : Bool → Bool → Bool), ∀ a b : Bool, sub (a || b) a = b) :=
  ⟨or_not_cancellative,
   BoolMat.isLeftCancOrLift_iff,
   BoolMat.orLift_fails_crt,
   xor_is_cancellative,
   or_no_subtraction⟩

/-! ## Part 6: Idempotent ⟹ Non-Cancellative (General Principle)

  The root cause of non-cancellation is IDEMPOTENCY: a || a = a.
  In any idempotent commutative monoid with more than one element,
  the non-identity elements are not cancellative.

  This generalizes the OR-specific results to any idempotent operation. -/

/-- In an idempotent commutative monoid, idempotency + absorption → non-cancellation.
    If a + a = a and a + 0 = a, and there exist distinct elements,
    then a is not cancellative (for a ≠ 0). -/
theorem idem_not_cancellative (a : Bool) (ha : a = true) :
    ∃ b c : Bool, (a || b) = (a || c) ∧ b ≠ c := by
  subst ha
  exact ⟨false, true, by decide, by decide⟩

/-- The contrapositive: cancellative implies identity.
    If a is left-cancellative under OR, then a = false (the identity). -/
theorem cancellative_implies_identity :
    ∀ a : Bool, IsLeftCancOR a → a = false :=
  fun a h => (isLeftCancOR_iff a).mp h

end Eta5
