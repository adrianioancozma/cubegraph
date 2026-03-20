/-
  CubeGraph/TraceKernel.lean
  Trace equivalence on boolean matrices: A ~_tr B iff forall L R, trace(L*A*R) = trace(L*B*R).

  Establishes:
  1. traceEquiv is an equivalence relation (refl, symm, trans)
  2. traceEquiv is a congruence (compatible with multiplication: left and right)
  3. |Q_8| >= 3 (zero, singleEntry, one are pairwise non-equivalent)

  Depends on: CubeGraph/BoolMat.lean (mul_assoc, trace_zero, one_mul, mul_one)

  Task: experiments-ml/014_2026-03-06_synthesis-foundations/TODO.md (T1.3)
  Plan: experiments-ml/014_2026-03-06_synthesis-foundations/PLAN-T1.3-TraceKernel.md
  Design source: round_01/RESULTS.md Section 12
  Validated by:
  - T1.1: trace_kernel.py — |Q_8| >= 220 computationally (>> 3 proven here)
  - Results: experiments-ml/014_.../results/trace_kernel.json
-/

import CubeGraph.BoolMat

namespace BoolMat

variable {n : Nat}

/-! ## Trace Equivalence -/

/-- Trace equivalence: A ~_tr B iff trace(L*A*R) = trace(L*B*R) for all contexts (L, R).
    This is the finest congruence on the boolean matrix monoid that factors through trace. -/
def traceEquiv (n : Nat) (A B : BoolMat n) : Prop :=
  ∀ (L R : BoolMat n), trace (mul (mul L A) R) = trace (mul (mul L B) R)

/-! ## Equivalence Properties -/

/-- traceEquiv is reflexive. -/
theorem traceEquiv_refl (A : BoolMat n) : traceEquiv n A A :=
  fun _ _ => rfl

/-- traceEquiv is symmetric. -/
theorem traceEquiv_symm {A B : BoolMat n} (h : traceEquiv n A B) :
    traceEquiv n B A :=
  fun L R => (h L R).symm

/-- traceEquiv is transitive. -/
theorem traceEquiv_trans {A B C : BoolMat n}
    (h1 : traceEquiv n A B) (h2 : traceEquiv n B C) :
    traceEquiv n A C :=
  fun L R => (h1 L R).trans (h2 L R)

/-! ## Congruence Properties -/

/-- Left congruence: A ~_tr B implies M*A ~_tr M*B.
    Proof: trace(L*(M*A)*R) = trace((L*M)*A*R) = trace((L*M)*B*R) = trace(L*(M*B)*R). -/
theorem traceEquiv_mul_left {A B : BoolMat n} (h : traceEquiv n A B) (M : BoolMat n) :
    traceEquiv n (mul M A) (mul M B) := by
  intro L R
  have := h (mul L M) R
  simp only [mul_assoc] at this ⊢
  exact this

/-- Right congruence: A ~_tr B implies A*M ~_tr B*M.
    Proof: trace(L*(A*M)*R) = trace(L*A*(M*R)) = trace(L*B*(M*R)) = trace(L*(B*M)*R). -/
theorem traceEquiv_mul_right {A B : BoolMat n} (h : traceEquiv n A B) (M : BoolMat n) :
    traceEquiv n (mul A M) (mul B M) := by
  intro L R
  have := h L (mul M R)
  simp only [mul_assoc] at this ⊢
  exact this

/-! ## Concrete Distinctions on B_8 -/

/-- The single-entry matrix E_{ij}: has true at (i,j) and false elsewhere. -/
def singleEntry (i j : Fin n) : BoolMat n :=
  fun r c => (r == i) && (c == j)

/-- zero and one are not trace-equivalent (n=8).
    Witness: L=I, R=I gives trace(zero) = false != true = trace(one). -/
theorem zero_not_traceEquiv_one_8 : ¬ traceEquiv 8 zero one := by
  intro h
  have heq := h one one
  simp only [one_mul, mul_one] at heq
  rw [trace_zero] at heq
  have hone : trace (one : BoolMat 8) = true := by native_decide
  rw [hone] at heq
  exact absurd heq (by decide)

/-- zero and singleEntry 0 0 are not trace-equivalent (n=8).
    Witness: L=I, R=I gives trace(zero) = false != true = trace(E_{00}). -/
theorem zero_not_traceEquiv_singleEntry_8 :
    ¬ traceEquiv 8 zero (singleEntry (⟨0, by omega⟩ : Fin 8) ⟨0, by omega⟩) := by
  intro h
  have heq := h one one
  simp only [one_mul, mul_one] at heq
  rw [trace_zero] at heq
  have hse : trace (singleEntry (⟨0, by omega⟩ : Fin 8) ⟨0, by omega⟩) = true := by native_decide
  rw [hse] at heq
  exact absurd heq (by decide)

/-- singleEntry 0 0 and one are not trace-equivalent (n=8).
    Witness: L=E_{11}, R=I gives trace(E_{11}*E_{00}) = false != true = trace(E_{11}*I). -/
theorem singleEntry_not_traceEquiv_one_8 :
    ¬ traceEquiv 8 (singleEntry (⟨0, by omega⟩ : Fin 8) ⟨0, by omega⟩) one := by
  intro h
  have heq := h (singleEntry ⟨1, by omega⟩ ⟨1, by omega⟩) one
  simp only [mul_one] at heq
  -- heq : false = trace (singleEntry 1 1)  (simp already evaluated LHS)
  have htr : trace (singleEntry (⟨1, by omega⟩ : Fin 8) ⟨1, by omega⟩) = true := by native_decide
  rw [htr] at heq
  exact absurd heq (by decide)

/-- The trace kernel Q_8 has at least 3 equivalence classes:
    [zero], [E_{00}], and [I] are pairwise distinct. -/
theorem Q8_at_least_3_classes : ∃ (A B C : BoolMat 8),
    ¬ traceEquiv 8 A B ∧ ¬ traceEquiv 8 B C ∧ ¬ traceEquiv 8 A C :=
  ⟨zero, singleEntry ⟨0, by omega⟩ ⟨0, by omega⟩, one,
   zero_not_traceEquiv_singleEntry_8,
   singleEntry_not_traceEquiv_one_8,
   zero_not_traceEquiv_one_8⟩

end BoolMat
