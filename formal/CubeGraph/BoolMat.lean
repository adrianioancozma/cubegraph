/-
  CubeGraph/BoolMat.lean
  Boolean matrices over Fin n × Fin n, forming a monoid under Boolean matrix multiplication.
  This is the algebraic foundation: the monoid (Bₙ, ⊗, I) where
    (A ⊗ B)[i,j] = ∨_{k} (A[i,k] ∧ B[k,j])

  The transfer operator monoid T₃* is a sub-monoid of B₈.

  See: theory/foundations/04-links-weights.md (transfer operators between cubes)
  See: theory/theorems/CORE-THEOREMS-SUMMARY.md (role in the framework)
-/

/-- A boolean matrix of size n × n. -/
def BoolMat (n : Nat) := Fin n → Fin n → Bool

namespace BoolMat

variable {n : Nat}

/-- Boolean matrix multiplication: (A ⊗ B)[i,j] = ∨_k (A[i,k] ∧ B[k,j]) -/
def mul (A B : BoolMat n) : BoolMat n :=
  fun i j => (List.finRange n).any fun k => A i k && B k j

/-- The identity matrix: I[i,j] = (i == j) -/
def one : BoolMat n :=
  fun i j => decide (i = j)

/-- The zero matrix -/
def zero : BoolMat n :=
  fun _ _ => false

/-- The trace of a boolean matrix: ∨_i M[i,i] -/
def trace (M : BoolMat n) : Bool :=
  (List.finRange n).any fun i => M i i

/-- A matrix is zero iff all entries are false -/
def isZero (M : BoolMat n) : Prop :=
  ∀ i j, M i j = false

instance {M : BoolMat n} : Decidable (isZero M) :=
  inferInstanceAs (Decidable (∀ i j, M i j = false))

/-- Every Fin n is a member of List.finRange n -/
theorem mem_finRange (i : Fin n) : i ∈ List.finRange n := by
  unfold List.finRange
  rw [List.mem_iff_getElem]
  exact ⟨i.val, by rw [List.length_ofFn]; exact i.isLt, by simp [List.getElem_ofFn]⟩

/-- Convert Bool iff to Bool equality -/
private theorem bool_eq_of_iff {a b : Bool} (h : (a = true) ↔ (b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

/-- zero matrix mul anything = zero -/
theorem zero_mul (A : BoolMat n) : mul zero A = zero := by
  funext i j
  simp [mul, zero]

/-- anything mul zero = zero -/
theorem mul_zero (A : BoolMat n) : mul A zero = zero := by
  funext i j
  simp [mul, zero]

/-- mul is associative -/
theorem mul_assoc (A B C : BoolMat n) : mul (mul A B) C = mul A (mul B C) := by
  funext i j
  apply bool_eq_of_iff
  simp only [mul, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨k, hk, ⟨m, hm, h1, h2⟩, h3⟩
    exact ⟨m, hm, h1, k, hk, h2, h3⟩
  · rintro ⟨m, hm, h1, k, hk, h2, h3⟩
    exact ⟨k, hk, ⟨m, hm, h1, h2⟩, h3⟩

/-- one is left identity -/
theorem one_mul (A : BoolMat n) : mul one A = A := by
  funext i j
  apply bool_eq_of_iff
  simp only [mul, one, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨_, _, rfl, h⟩ => h, fun h => ⟨i, mem_finRange _, rfl, h⟩⟩

/-- one is right identity -/
theorem mul_one (A : BoolMat n) : mul A one = A := by
  funext i j
  apply bool_eq_of_iff
  simp only [mul, one, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨_, _, h, rfl⟩ => h, fun h => ⟨j, mem_finRange _, h, rfl⟩⟩

/-- Power of a boolean matrix (iterated multiplication) -/
def pow (M : BoolMat n) : Nat → BoolMat n
  | 0 => one
  | k + 1 => mul M (pow M k)

/-- A matrix is nilpotent if some power is zero -/
def IsNilpotent (M : BoolMat n) : Prop :=
  ∃ k : Nat, k > 0 ∧ isZero (pow M k)

/-- Trace of zero is false -/
theorem trace_zero : trace (zero (n := n)) = false := by
  simp [trace, zero]

/-- If isZero M, then trace M = false -/
theorem trace_of_isZero {M : BoolMat n} (h : isZero M) : trace M = false := by
  simp [trace]
  intro i
  exact h i i

/-- Semantics of matrix multiplication: entry is true iff ∃ intermediate -/
theorem mul_apply_true (A B : BoolMat n) (i j : Fin n) :
    mul A B i j = true ↔ ∃ k : Fin n, A i k = true ∧ B k j = true := by
  simp only [mul, List.any_eq_true, Bool.and_eq_true]
  exact ⟨fun ⟨k, _, h1, h2⟩ => ⟨k, h1, h2⟩,
         fun ⟨k, h1, h2⟩ => ⟨k, mem_finRange k, h1, h2⟩⟩

/-- Semantics of identity matrix -/
theorem one_apply_true (i j : Fin n) :
    (one : BoolMat n) i j = true ↔ i = j := by
  simp [one, decide_eq_true_eq]

/-- Semantics of trace: true iff some diagonal entry is true -/
theorem trace_true (M : BoolMat n) :
    trace M = true ↔ ∃ i : Fin n, M i i = true := by
  simp only [trace, List.any_eq_true]
  exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩,
         fun ⟨i, h⟩ => ⟨i, mem_finRange i, h⟩⟩

/-! ## Fixed-Point Monotonicity

  The diagonal of a boolean matrix product preserves fixed points:
  if g is a fixed point of both M₁ and M₂, it is a fixed point of M₁ ⊗ M₂.
  This is the algebraic foundation of the holonomy monoid theory:
  generators suffice for computing ∩Fix(Hol).

  See: experiments-ml/008_2026-03-04_why-h2-hard/DISCOVERY-CHAIN-2026-03-04.md §1
  See: experiments-ml/008_2026-03-04_why-h2-hard/PLAN-FAZA2-LEAN-FIXPOINT-MONOTONICITY.md (plan)
-/

/-- **Fixed-Point Monotonicity**: Fix(M₁·M₂) ⊇ Fix(M₁) ∩ Fix(M₂).
    If g is a fixed point of both M₁ and M₂, then g is a fixed point of M₁⊗M₂.
    Proof: (M₁⊗M₂)[g,g] = ∨_k(M₁[g,k] ∧ M₂[k,g]) ≥ M₁[g,g] ∧ M₂[g,g] = 1. -/
theorem fixedPoint_mul (M₁ M₂ : BoolMat n) (g : Fin n)
    (h₁ : M₁ g g = true) (h₂ : M₂ g g = true) :
    (mul M₁ M₂) g g = true := by
  rw [mul_apply_true]; exact ⟨g, h₁, h₂⟩

/-- Helper: foldl mul preserves fixed points with any accumulator. -/
private theorem fixedPoint_foldl_aux (l : List (BoolMat n)) (A : BoolMat n) (g : Fin n)
    (hA : A g g = true) (hl : ∀ M ∈ l, M g g = true) :
    (l.foldl mul A) g g = true := by
  induction l generalizing A with
  | nil => simpa
  | cons M rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact fixedPoint_mul A M g hA (hl M (by simp))
    · intro M' hM'
      exact hl M' (by simp [hM'])

/-- Fixed point is preserved under iterated multiplication (foldl).
    If g is a fixed point of every matrix in a list,
    then g is a fixed point of their left-fold product.
    Corollary: generators suffice — ∩Fix(monoid) = ∩Fix(generators). -/
theorem fixedPoint_foldl (ms : List (BoolMat n)) (g : Fin n)
    (h : ∀ M ∈ ms, M g g = true) :
    (ms.foldl mul one) g g = true :=
  fixedPoint_foldl_aux ms one g (by simp [one]) h

/-- Transpose of a boolean matrix: (Aᵀ)[i,j] = A[j,i] -/
def transpose (M : BoolMat n) : BoolMat n :=
  fun i j => M j i

/-- Semantics of transpose: entry (i,j) of Aᵀ equals entry (j,i) of A -/
theorem transpose_apply (M : BoolMat n) (i j : Fin n) :
    M.transpose i j = M j i := rfl

end BoolMat
