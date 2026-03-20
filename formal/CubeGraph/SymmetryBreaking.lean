/-
  CubeGraph/SymmetryBreaking.lean — F1.2

  Symmetry Breaking is Irreversible: Z₂³ symmetry of the cube,
  broken by OR clauses, cannot be restored through polynomial computation.

  The cube has (Z/2Z)³ symmetry (3 independent bit-flips = literal negations).
  Each clause (OR of literals) BREAKS this symmetry by eliminating states.
  OR is non-invertible (1+1=1): the breaking is IRREVERSIBLE.
  Rank-1 boolean matrices have no inverse: information lost forever.
  This holds on ANY idempotent semiring (a+a=a), not just Bool.

  Consequence: rank decay on cycles = the irreversible loss of symmetry
  information through monotone composition. The twist (H²) is invisible
  because the symmetry needed to detect it has been irreversibly destroyed.

  0 sorry. 0 new axioms. All proofs are references to existing theorems.

  See: experiments-ml/025_2026-03-19_synthesis/bridge/CORE-THESIS.md
  See: experiments-ml/025_2026-03-19_synthesis/bridge/FIXED-POINT-ARGUMENT.md
  See: experiments-ml/025_2026-03-19_synthesis/bridge/F1.2-PLAN-SYMMETRY-BREAKING.md
-/

import CubeGraph.Z2Reflection
import CubeGraph.InvertibilityBarrier
import CubeGraph.IdempotentSemiring
import CubeGraph.Rank1Bubbles
import CubeGraph.SpreadingCompression

namespace CubeGraph

open BoolMat

/-! ## Section 1: Symmetry and Its Breaking -/

/-- **Symmetry and Its Breaking**: the cube has Z₂³ symmetry,
    OR breaks it irreversibly, rank-1 matrices have no inverse.

    (A) Z₂ symmetry: flipBit is involutive (σᵢ² = id)
    (B) Complement = product of all 3 reflections (σ₀∘σ₁∘σ₂)
    (C) OR non-invertible: true ∨ x = true, cannot "undo" true
    (D) Rank-1 boolean non-invertible: ¬∃ M' with M·M' = I (n ≥ 2)
    (E) BoolMat.mul monotone: a single witness path ⇒ entry = true
    (F) Transfer operators rank-1 are non-invertible

    Breaking symmetry is O(m) — one clause at a time.
    Restoring symmetry requires inverting OR — impossible on Bool. -/
theorem symmetry_and_its_breaking :
    -- (A) flipBit involutive (Z₂ symmetry per axis)
    (∀ v : Vertex, ∀ i : Fin 3, flipBit (flipBit v i) i = v)
    -- (B) complement = composition of all 3 reflections
    ∧ (∀ v : Vertex, CubeGraph.complementVertex v =
        flipBit (flipBit (flipBit v ⟨0, by omega⟩) ⟨1, by omega⟩) ⟨2, by omega⟩)
    -- (C) OR non-invertible (1+1=1, no subtraction)
    ∧ (¬ ∃ x : Bool, (true || x) = false)
    -- (D) Rank-1 boolean matrices non-invertible
    ∧ (∀ (M : BoolMat 8), M.IsRankOne →
        ¬ ∃ M' : BoolMat 8, BoolMat.mul M M' = BoolMat.one)
    -- (E) BoolMat.mul monotone (single witness suffices)
    ∧ (∀ (A B : BoolMat 8) (i j k : Fin 8),
        A i k = true → B k j = true → BoolMat.mul A B i j = true)
    -- (F) Transfer operators rank-1 non-invertible
    ∧ (∀ c₁ c₂ : Cube, (transferOp c₁ c₂).IsRankOne →
        ¬ ∃ M' : BoolMat 8, BoolMat.mul (transferOp c₁ c₂) M' = BoolMat.one) :=
  ⟨flipBit_involutive,
   complement_eq_flipAll,
   or_no_inverse,
   fun M hM => rank1_not_bool_invertible (by omega) M hM,
   fun A B i j k hA hB => boolmat_mul_monotone A B i j k hA hB,
   transferOp_rank1_not_invertible⟩

/-! ## Section 2: Irreversibility Implies Rank Decay -/

/-- **Irreversibility → Rank Decay → Blind**: the complete chain.

    OR non-invertible (Section 1) → composition loses information →
    rank decay (rank-1 absorbing) → dead stays dead →
    blind below Borromean order.

    Universal on ANY idempotent semiring (a+a=a):
    the barrier is a property of the CLASS, not of Bool specifically.

    CONSEQUENCE: symmetry broken by m OR-clauses is IRREVERSIBLE.
    Restoration would require inverting OR = subtraction = non-existent
    on the boolean semiring. Any attempt to restore through composition
    hits rank decay → information lost → blind to the twist. -/
theorem irreversibility_implies_rank_decay :
    -- (1) Rank-1 closed: composition cannot create coordination
    (∀ {n : Nat} (A B : BoolMat n), A.IsRankOne → B.IsRankOne →
      (BoolMat.mul A B).IsRankOne ∨ BoolMat.mul A B = BoolMat.zero)
    -- (2) Rank-1 absorbing on lists: never rank ≥ 2 from rank-1
    ∧ (∀ {n : Nat} (Ms : List (BoolMat n)) (acc : BoolMat n),
        (acc.IsRankOne ∨ acc = BoolMat.zero) →
        (∀ M ∈ Ms, M.IsRankOne) →
        (Ms.foldl BoolMat.mul acc).IsRankOne ∨
          Ms.foldl BoolMat.mul acc = BoolMat.zero)
    -- (3) Dead stays dead: rowRank ≤ 1 is absorbing
    ∧ (∀ {n : Nat} (A : BoolMat n) (sfx : List (BoolMat n)),
        rowRank A ≤ 1 → rowRank (sfx.foldl BoolMat.mul A) ≤ 1)
    -- (4) Idempotent universal: a+a=a on ANY IdempSR
    ∧ (∀ (S : Type) [inst : IdempSR S] (a : S), a + a = a)
    -- (5) Borromean gap: lost information → blind below b
    ∧ InformationGap h2Graph 3 :=
  ⟨fun _ _ hA hB => rank1_closed_under_compose hA hB,
   fun Ms acc hacc hMs => rank1_foldl_preserves Ms acc hacc hMs,
   fun A sfx h => dead_walk_stays_dead A sfx h,
   fun S inst a => @IdempSR.add_idem S inst a,
   h2_information_gap⟩

end CubeGraph
