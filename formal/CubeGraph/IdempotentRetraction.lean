/-
  CubeGraph/IdempotentRetraction.lean
  Idempotent retractions on boolean matrices — definitions and basic lemmas.

  A retraction R is an idempotent (R² = R) that is not the identity.
  The 5 known barriers (XOR, Horn, Trivial Section, Rank-1+AC, Fiber=1)
  each correspond to a type of idempotent retraction on the gap space.

  The main theorem (T4.2: r1Graph_no_proper_retraction_on_gaps) is deferred.

  Depends on: CubeGraph/BoolMat.lean (mul, one, zero, mul_one, zero_mul)

  Task: experiments-ml/014_2026-03-06_synthesis-foundations/TODO.md (T2.4)
  Plan: experiments-ml/014_2026-03-06_synthesis-foundations/PLAN-T2.4-IdempotentRetraction.md
  Design source: round_01/G7-C.md (Idea G7C-2: "Generic = Absence of All Idempotent Retractions")

  D2 extension (018): idempotent_pow_all (L4) — M²=M → M^k=M ∀k≥1
  See: experiments-ml/018_2026-03-11_negation-complexity/D2-LEAN-PLAN.md (L4)
  See: experiments-ml/018_2026-03-11_negation-complexity/D2-STEP1-RESULTS.md §5 (24 resistant elements)
-/

import CubeGraph.BoolMat

namespace BoolMat

variable {n : Nat}

/-- M is idempotent: M² = M -/
def IsIdempotent (M : BoolMat n) : Prop := mul M M = M

/-- M is a proper retraction: idempotent and not identity -/
def IsRetraction (M : BoolMat n) : Prop := IsIdempotent M ∧ M ≠ one

/-- A retraction at a junction is coherent if it is "invisible" to composed operators:
    for each pair (T_in, T_out), inserting R does not change the product.
    T_out ⊗ R ⊗ T_in = T_out ⊗ T_in -/
def IsCoherentRetraction (R : BoolMat n) (edges_in edges_out : List (BoolMat n)) : Prop :=
  IsRetraction R ∧
  ∀ T_in, T_in ∈ edges_in → ∀ T_out, T_out ∈ edges_out →
    mul (mul T_out R) T_in = mul T_out T_in

/-- A system of junctions has coherent retractions if there exists a single
    proper retraction compatible with all junction operator pairs. -/
def HasCoherentRetractions (junctions : List (List (BoolMat n) × List (BoolMat n))) : Prop :=
  ∃ R : BoolMat n, ∀ j, j ∈ junctions →
    IsCoherentRetraction R j.1 j.2

-- ============================================================
--  Basic lemmas (all trivial)
-- ============================================================

/-- The identity matrix is idempotent: I² = I -/
theorem one_is_idempotent : IsIdempotent (one : BoolMat n) := by
  unfold IsIdempotent
  exact one_mul one

/-- The zero matrix is idempotent: 0² = 0 -/
theorem zero_is_idempotent : IsIdempotent (zero : BoolMat n) := by
  unfold IsIdempotent
  exact zero_mul zero

/-- A retraction is idempotent (first projection) -/
theorem retraction_idempotent {M : BoolMat n} (h : IsRetraction M) : IsIdempotent M :=
  h.1

/-- A retraction is not the identity (second projection) -/
theorem retraction_not_identity {M : BoolMat n} (h : IsRetraction M) : M ≠ one :=
  h.2

/-- The identity is not a retraction -/
theorem one_not_retraction : ¬ IsRetraction (one : BoolMat n) := by
  intro ⟨_, hne⟩
  exact hne rfl

/-- The zero matrix is a retraction when n > 0 (since 0 ≠ I) -/
theorem zero_is_retraction (hn : n > 0) : IsRetraction (zero : BoolMat n) := by
  constructor
  · exact zero_is_idempotent
  · intro h
    have : (zero : BoolMat n) ⟨0, hn⟩ ⟨0, hn⟩ = (one : BoolMat n) ⟨0, hn⟩ ⟨0, hn⟩ := by
      rw [h]
    simp [zero, one] at this

/-- Idempotent matrices are fixed points of squaring -/
theorem idempotent_pow_two {M : BoolMat n} (h : IsIdempotent M) :
    pow M 2 = M := by
  simp [pow, IsIdempotent] at *
  rw [mul_one]
  exact h

/-- **L4: Idempotent Fixpoint Theorem** (D2 Step 4).
    If M is idempotent (M² = M), then M^k = M for all k ≥ 1.
    This explains the "24 resistant elements" from D2 mixing experiments:
    idempotent matrices are absorbing fixpoints of random walks in T₃*.

    Proof: by induction. Base: M¹ = M·I = M. Step: M^(k+2) = M·M^(k+1) = M·M = M.

    See: experiments-ml/018_2026-03-11_negation-complexity/D2-STEP1-RESULTS.md §5
    See: experiments-ml/018_2026-03-11_negation-complexity/D2-LEAN-PLAN.md (L4) -/
theorem idempotent_pow_all {M : BoolMat n} (h : IsIdempotent M) :
    ∀ k : Nat, k ≥ 1 → pow M k = M := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      -- pow M 1 = mul M (pow M 0) = mul M one = M
      simp [pow, mul_one]
    | succ k =>
      -- Goal: mul M (mul M (pow M k)) = M
      -- Use associativity: mul (mul M M) (pow M k) = mul M (pow M k) = pow M (k+1) = M
      simp only [pow]
      rw [← mul_assoc]
      have : mul M M = M := h
      rw [this]
      -- Now goal: mul M (pow M k) = M, i.e., pow M (k+1) = M
      exact ih (by omega)

/-- If R is a coherent retraction, then R is a retraction -/
theorem coherent_retraction_is_retraction {R : BoolMat n}
    {ei eo : List (BoolMat n)} (h : IsCoherentRetraction R ei eo) :
    IsRetraction R :=
  h.1

/-- Coherent retraction absorbs into composed operators -/
theorem coherent_retraction_absorbs {R : BoolMat n}
    {ei eo : List (BoolMat n)} (h : IsCoherentRetraction R ei eo)
    {T_in T_out : BoolMat n} (hin : T_in ∈ ei) (hout : T_out ∈ eo) :
    mul (mul T_out R) T_in = mul T_out T_in :=
  h.2 T_in hin T_out hout

end BoolMat
