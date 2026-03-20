/-
  CubeGraph/Absorption.lean
  Absorption theory: zero is an absorbing state in the boolean matrix monoid.

  Main theorems:
  - foldl_mul_zero: folding mul from zero always yields zero
  - listProd_zero_of_take: prefix product zero → full product zero
  - absorption_chain: once zero, always zero (for all j ≥ k)
  - trace_nonzero_no_prefix_zero: contrapositive — nonzero trace ⇒ no prefix was zero

  These formalize the Absorption Theorem from D2 Step 1:
  random products in T₃* converge to zero exponentially (λ = 0.947).
  The algebraic reason: zero is an absorbing state, and each multiplication step
  has probability ~5.3% of reaching zero, creating exponential decay.

  Connection to SAT:
  - sat_monodromy_trace (Monodromy.lean): SAT → trace(monodromy) = true
  - Contrapositive: trace = false → UNSAT
  - absorption_chain: if any prefix product is zero, full product is zero
    → trace false → UNSAT

  Depends on: CubeGraph/BoolMat.lean (mul, one, zero, zero_mul, trace_zero)

  See: experiments-ml/018_2026-03-11_negation-complexity/D2-STEP1-RESULTS.md §3
  See: experiments-ml/018_2026-03-11_negation-complexity/D2-LEAN-PLAN.md (L5)
  See: experiments-ml/018_2026-03-11_negation-complexity/L5-PLAN.md (implementation plan)
-/

import CubeGraph.BoolMat

namespace BoolMat

variable {n : Nat}

/-! ## Definitions -/

/-- Product of a list of boolean matrices via left fold.
    listProd [M₁, M₂, M₃] = ((I ⊗ M₁) ⊗ M₂) ⊗ M₃ = M₁ ⊗ M₂ ⊗ M₃ -/
def listProd (Ms : List (BoolMat n)) : BoolMat n :=
  Ms.foldl mul one

/-! ## Basic properties -/

/-- Product of empty list is the identity. -/
@[simp] theorem listProd_nil : listProd ([] : List (BoolMat n)) = one := rfl

/-- Product of a singleton list is the matrix itself. -/
theorem listProd_singleton (M : BoolMat n) : listProd [M] = M := by
  simp [listProd, one_mul]

/-! ## Core absorption: zero is absorbing under foldl -/

/-- Left-folding mul from zero always yields zero.
    This is the algebraic core: zero is a left-absorbing element,
    so 0 ⊗ M = 0 for all M, and by induction, folding from 0 stays at 0.

    Proof: induction on the list. At each step, zero_mul rewrites
    mul zero M to zero, and the IH finishes. -/
theorem foldl_mul_zero (Ms : List (BoolMat n)) :
    Ms.foldl mul zero = zero := by
  induction Ms with
  | nil => rfl
  | cons M rest ih =>
    simp only [List.foldl_cons, zero_mul]
    exact ih

/-! ## List product over append -/

/-- List product distributes over append. -/
theorem listProd_append (xs ys : List (BoolMat n)) :
    listProd (xs ++ ys) = ys.foldl mul (listProd xs) := by
  simp [listProd, List.foldl_append]

/-- If a prefix product is zero, appending more matrices keeps it zero. -/
theorem listProd_append_of_zero (xs ys : List (BoolMat n))
    (h : listProd xs = zero) :
    listProd (xs ++ ys) = zero := by
  rw [listProd_append, h]
  exact foldl_mul_zero ys

/-! ## Main absorption theorems -/

/-- If a prefix product is zero, the full product is zero.
    Proof: split the list at position k via take_append_drop,
    then apply listProd_append_of_zero. -/
theorem listProd_zero_of_take (Ms : List (BoolMat n)) (k : Nat) (_hk : k ≤ Ms.length)
    (h : listProd (Ms.take k) = zero) :
    listProd Ms = zero := by
  unfold listProd at h ⊢
  rw [← List.take_append_drop k Ms, List.foldl_append, h]
  exact foldl_mul_zero _

/-- **L5: Absorption Chain Theorem**.
    Once a partial product becomes zero, ALL longer partial products are zero.
    If listProd(Ms.take k) = zero, then listProd(Ms.take j) = zero for all j ≥ k.

    This formalizes the central mechanism of the Absorption Theorem from D2 Step 1:
    the zero matrix is an absorbing state in T₃*, so random products converge
    to zero exponentially (λ = 0.947, half-life = 12.8 steps).

    Proof: (Ms.take j).take k = Ms.take (min k j) = Ms.take k (since k ≤ j),
    then apply listProd_zero_of_take to Ms.take j.

    See: experiments-ml/018_2026-03-11_negation-complexity/D2-STEP1-RESULTS.md §3
    See: experiments-ml/018_2026-03-11_negation-complexity/D2-LEAN-PLAN.md (L5) -/
theorem absorption_chain (Ms : List (BoolMat n)) (k : Nat) (_hk : k ≤ Ms.length)
    (h : listProd (Ms.take k) = zero) :
    ∀ j, k ≤ j → j ≤ Ms.length → listProd (Ms.take j) = zero := by
  intro j hkj hjlen
  have hjlen' : (Ms.take j).length = j := by
    rw [List.length_take, Nat.min_eq_left hjlen]
  apply listProd_zero_of_take (Ms.take j) k (by omega)
  rwa [List.take_take, Nat.min_eq_left hkj]

/-! ## Connections to trace and SAT -/

/-- Zero product means zero trace.
    Combined with sat_monodromy_trace (Monodromy.lean, contrapositive):
    zero monodromy product → trace = false → cycle UNSAT. -/
theorem listProd_zero_trace (Ms : List (BoolMat n))
    (h : listProd Ms = zero) :
    trace (listProd Ms) = false := by
  rw [h]; exact trace_zero

/-- Contrapositive of absorption: if the full product has nonzero trace,
    then no prefix product is zero. This is useful for proving satisfiability:
    if we can show trace(product) = true (via sat_monodromy_trace),
    then no intermediate product collapsed to zero. -/
theorem trace_nonzero_no_prefix_zero (Ms : List (BoolMat n))
    (h : trace (listProd Ms) = true) (k : Nat) (hk : k ≤ Ms.length) :
    listProd (Ms.take k) ≠ zero := by
  intro h_zero
  have := listProd_zero_of_take Ms k hk h_zero
  rw [this, trace_zero] at h
  exact absurd h (by decide)

end BoolMat
