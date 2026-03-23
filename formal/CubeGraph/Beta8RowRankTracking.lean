/-
  CubeGraph/Beta8RowRankTracking.lean
  ROWRANK TRACKING — Analysis and Resolution of the Psi7 boolOr Gap

  THIS FILE proves:
  (1) gate_expr_good IS FALSE: counterexample via native_decide
  (2) The counterexample perm has order 4 (solvable), KR = 1 safe
  (3) OmegaSafe closes boolOr gap for direct transfer children
  (4) h2 transfers and sigma products are OmegaSafe
  (5) Structural rank tracking lemmas

  IMPORTS: Omega7CloseGap

  0 sorry. 20 theorems.
-/

import CubeGraph.Omega7CloseGap

namespace CubeGraph

open _root_.BoolMat

/-! ## Local Definitions -/

/-- The 8 elements of (Z/2Z)^3 as boolean matrices. -/
@[reducible] private def sigmaGroupElem' (mask : Fin 8) : BoolMat 8 :=
  BoolMat.mul (BoolMat.mul
    (if mask.val &&& 1 = 1 then sigma0Mat else BoolMat.one)
    (if mask.val &&& 2 = 2 then sigma1Mat else BoolMat.one))
    (if mask.val &&& 4 = 4 then sigma2Mat else BoolMat.one)

/-- M is in the sigma group. -/
private def IsInSigmaGroup' (M : BoolMat 8) : Prop :=
  ∃ mask : Fin 8, M = sigmaGroupElem' mask

/-! ## Part 1: The Counterexample -/

private def s2ABs2 : BoolMat 8 :=
  BoolMat.mul (BoolMat.mul sigma2Mat h2MonAB) sigma2Mat

private def s2BCs2 : BoolMat 8 :=
  BoolMat.mul (BoolMat.mul sigma2Mat h2MonBC) sigma2Mat

private def piPerm : BoolMat 8 :=
  BoolMat.boolOr
    (BoolMat.boolOr h2MonAB s2ABs2)
    (BoolMat.boolOr h2MonBC s2BCs2)

/-- **B8.1**: Sigma2 conjugates preserve rank 2. -/
theorem conjugate_rank2 :
    BoolMat.rowRank s2ABs2 ≤ 2 ∧ BoolMat.rowRank s2BCs2 ≤ 2 := by
  constructor <;> native_decide

/-- **B8.2**: piPerm is a permutation matrix. -/
theorem piPerm_is_perm : IsPermutationMatrix piPerm := by
  constructor
  · intro i; revert i; native_decide
  · intro j; revert j; native_decide

/-- **B8.3**: piPerm is NOT in (Z/2Z)^3. piPerm(0) = 2, so mask would
    need to be 2 (XOR 2). But sigmaGroupElem'(2)(1) = 3, while piPerm(1) = 0. -/
theorem piPerm_not_sigma : ¬ IsInSigmaGroup' piPerm := by
  intro ⟨mask, h_eq⟩
  -- piPerm at entry (0, 0) is false
  have h00 : piPerm (0 : Fin 8) (0 : Fin 8) = false := by native_decide
  -- piPerm at entry (0, 2) is true
  have h02 : piPerm (0 : Fin 8) (2 : Fin 8) = true := by native_decide
  -- Rewrite using h_eq
  rw [h_eq] at h00 h02
  -- For each mask, check contradiction
  have : mask.val < 8 := mask.isLt
  -- sigmaGroupElem' mask (0, 0) = (decide (0 XOR mask = 0)) ... complicated.
  -- Let's do case analysis on mask.val
  -- Exhaustive case check: for any mask, one of h00 or h02 gives contradiction
  -- Use the fact that sigmaGroupElem' is @[reducible]
  -- Try direct native_decide on the combined condition
  -- piPerm(0,0) = false AND piPerm(0,2) = true
  -- For any mask: sigmaGroupElem'(mask)(0,0) = true iff 0 XOR mask = 0 iff mask &&& 7 = 0 (complicated)
  -- Simpler: just check piPerm ≠ sigmaGroupElem'(mask) for each specific mask
  -- For each mask value 0..7, check that the entry constraint fails
  -- Use simp to substitute mask value and native_decide
  have hlt := mask.isLt
  -- The key: h00 says sigmaGroupElem' mask 0 0 = false
  -- But for mask with bit 1 set (mask ∈ {2,3,6,7}): sigmaGroupElem' maps 0 → 0 XOR mask,
  -- and entry (0, 0 XOR mask) is true. If mask &&& 7 ≠ 0: (0, 0) is false only if
  -- 0 XOR mask ≠ 0, i.e. mask ≠ 0. So h00 rules out mask with (0 XOR mask) = 0, i.e. mask = 0.
  -- Actually let's just do 8 separate proofs using Fin.ext + native_decide.
  -- Approach: show piPerm ≠ sigmaGroupElem' m for each m : Fin 8.
  -- piPerm at (0,2) = true. Check sigmaGroupElem' m (0,2) for each m.
  -- If false: contradiction with h02. If true: check (1,0).
  -- piPerm at (1,0) = true. Check sigmaGroupElem' m (1,0).
  have h10 : piPerm (1 : Fin 8) (0 : Fin 8) = true := by native_decide
  rw [h_eq] at h10
  -- Now we have: sigmaGroupElem' mask 0 0 = false, 0 2 = true, 1 0 = true
  -- Case split on mask.val using omega on Fin
  -- We have h00, h02, h10 about sigmaGroupElem' mask at specific entries.
  -- For each mask 0..7, at least one of these is a contradiction.
  -- We case-split on mask.val and use native_decide on the specific Bool equation.
  -- Manually check each of the 8 possible mask values.
  -- We substitute the mask value and check a specific entry.
  have hlt := mask.isLt
  -- For mask = 0: sigmaGroupElem' ⟨0, by omega⟩ (0:Fin 8) (2:Fin 8) = false
  -- Contradicts h02 = ... = true. Similarly for other masks.
  -- Use Fin.ext to check mask = ⟨k, _⟩ for each k
  have : mask = (0 : Fin 8) ∨ mask = (1 : Fin 8) ∨ mask = (2 : Fin 8) ∨
         mask = (3 : Fin 8) ∨ mask = (4 : Fin 8) ∨ mask = (5 : Fin 8) ∨
         mask = (6 : Fin 8) ∨ mask = (7 : Fin 8) := by
    have h := mask.isLt
    have : mask.val = 0 ∨ mask.val = 1 ∨ mask.val = 2 ∨ mask.val = 3 ∨
           mask.val = 4 ∨ mask.val = 5 ∨ mask.val = 6 ∨ mask.val = 7 := by omega
    rcases this with h | h | h | h | h | h | h | h <;>
      (try (left; exact Fin.ext h)) <;>
      (try (right; left; exact Fin.ext h)) <;>
      (try (right; right; left; exact Fin.ext h)) <;>
      (try (right; right; right; left; exact Fin.ext h)) <;>
      (try (right; right; right; right; left; exact Fin.ext h)) <;>
      (try (right; right; right; right; right; left; exact Fin.ext h)) <;>
      (try (right; right; right; right; right; right; left; exact Fin.ext h)) <;>
      (try (right; right; right; right; right; right; right; exact Fin.ext h))
  -- Use simp to normalize h00, h02, h10 after mask substitution
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (first
    | exact absurd h02 (by native_decide)
    | exact absurd h10 (by native_decide)
    | exact absurd h00 (by native_decide))

/-- **B8.4**: gate_expr_good is false: rank-2 transfers + sigma produce
    a non-sigma permutation. -/
theorem gate_expr_good_refuted :
    ∃ (P : BoolMat 8), IsPermutationMatrix P ∧ ¬ IsInSigmaGroup' P ∧
    BoolMat.rowRank h2MonAB ≤ 2 ∧ BoolMat.rowRank h2MonBC ≤ 2 :=
  ⟨piPerm, piPerm_is_perm, piPerm_not_sigma, by native_decide, by native_decide⟩

/-- **B8.5**: piPerm has order 4 (pi^4 = I). -/
theorem piPerm_order_4 :
    BoolMat.mul piPerm (BoolMat.mul piPerm
      (BoolMat.mul piPerm piPerm)) = BoolMat.one := by
  funext i j; revert i j; native_decide

/-- **B8.6**: pi^2 is in sigma group (= XOR 3). -/
theorem piPerm_sq_in_sigma :
    IsInSigmaGroup' (BoolMat.mul piPerm piPerm) :=
  ⟨⟨3, by omega⟩, by funext i j; revert i j; native_decide⟩

/-- **B8.7**: pi^2 is NOT identity (order exactly 4, not 2 or 1). -/
theorem piPerm_order_not_2 :
    BoolMat.mul piPerm piPerm ≠ BoolMat.one := by
  intro h
  -- pi^2(0, 0) should be false (pi^2 maps 0 -> 3), but one(0,0) = true
  have : BoolMat.mul piPerm piPerm (0 : Fin 8) (0 : Fin 8) = false := by native_decide
  rw [h] at this
  revert this; native_decide

/-! ## Part 2: OmegaSafe Closes boolOr -/

/-- `OmegaSafe M`: HasMultiRow or isZero or rowRank <= 3. -/
def OmegaSafe (M : BoolMat 8) : Prop :=
  HasMultiRow M ∨ BoolMat.isZero M ∨ BoolMat.rowRank M ≤ 3

/-- **B8.8**: Rank <= 2 implies OmegaSafe. -/
theorem rank2_omegaSafe (M : BoolMat 8) (h : BoolMat.rowRank M ≤ 2) :
    OmegaSafe M := Or.inr (Or.inr (by omega))

/-- **B8.9**: Two OmegaSafe matrices have non-perm boolOr. -/
theorem boolOr_omegaSafe_nonPerm' (A B : BoolMat 8)
    (hA : OmegaSafe A) (hB : OmegaSafe B) :
    ¬ IsPermutationMatrix (BoolMat.boolOr A B) :=
  boolOr_nonperm_of_omega7 A B hA hB

/-- **B8.10**: Every OmegaSafe matrix is non-perm. -/
theorem omegaSafe_nonPerm (M : BoolMat 8) (h : OmegaSafe M) :
    ¬ IsPermutationMatrix M := by
  rcases h with hM | hZ | hR
  · exact hasMultiRow_not_perm hM
  · exact @isZero_not_perm_8 M hZ
  · exact low_rank_not_perm M (by omega)

/-! ## Part 3: h2 Verification -/

/-- **B8.11**: h2 transfers are OmegaSafe. -/
theorem h2_transfers_omegaSafe :
    OmegaSafe h2MonAB ∧ OmegaSafe h2MonBC ∧ OmegaSafe h2MonCA := by
  exact ⟨Or.inr (Or.inr (by native_decide)),
         Or.inr (Or.inr (by native_decide)),
         Or.inr (Or.inr (by native_decide))⟩

/-- **B8.12**: h2 monodromy is OmegaSafe. -/
theorem h2_monodromy_omegaSafe' : OmegaSafe h2Monodromy :=
  Or.inr (Or.inr (by native_decide))

/-- **B8.13**: h2 sigma-transfer products are OmegaSafe. -/
theorem h2_sigma_products_omegaSafe :
    OmegaSafe (BoolMat.mul sigma0Mat h2MonAB) ∧
    OmegaSafe (BoolMat.mul sigma1Mat h2MonBC) ∧
    OmegaSafe (BoolMat.mul sigma2Mat h2MonCA) ∧
    OmegaSafe s2ABs2 ∧ OmegaSafe s2BCs2 := by
  exact ⟨Or.inr (Or.inr (by native_decide)),
         Or.inr (Or.inr (by native_decide)),
         Or.inr (Or.inr (by native_decide)),
         Or.inr (Or.inr (by native_decide)),
         Or.inr (Or.inr (by native_decide))⟩

/-- **B8.14**: boolOr(AB, CA) has HasMultiRow (shared row 0). -/
theorem h2_boolOr_AB_CA_multirow :
    HasMultiRow (BoolMat.boolOr h2MonAB h2MonCA) := by
  refine ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨2, by omega⟩, ?_, ?_, ?_⟩
  · decide
  · native_decide
  · native_decide

/-- **B8.15**: boolOr(AB, BC) has rank 4, no multi-row. -/
theorem h2_boolOr_AB_BC_rank4 :
    BoolMat.rowRank (BoolMat.boolOr h2MonAB h2MonBC) = 4 ∧
    ¬ HasMultiRow (BoolMat.boolOr h2MonAB h2MonBC) := by
  constructor
  · native_decide
  · intro ⟨i, j₁, j₂, hne, h₁, h₂⟩; revert i j₁ j₂ hne h₁ h₂; native_decide

/-! ## Part 4: Structural Rank Tracking -/

/-- **B8.16**: mul(rank <= 3, anything) has rank <= 3 hence OmegaSafe. -/
theorem mul_left_omegaSafe (A B : BoolMat 8)
    (h : BoolMat.rowRank A ≤ 3) : OmegaSafe (BoolMat.mul A B) :=
  Or.inr (Or.inr (Nat.le_trans (BoolMat.rowRank_mul_le A B) h))

/-- **B8.17**: entryAnd(rank <= 3, anything) has rank <= 3 hence OmegaSafe. -/
theorem entryAnd_left_omegaSafe (A B : BoolMat 8)
    (h : BoolMat.rowRank A ≤ 3) : OmegaSafe (BoolMat.entryAnd A B) :=
  Or.inr (Or.inr (Nat.le_trans (entryAnd_rowRank_le_left A B) h))

/-- **B8.18**: perm * HasMultiRow has HasMultiRow hence OmegaSafe. -/
theorem perm_mul_multirow_omegaSafe (P M : BoolMat 8)
    (hP : IsPermutationMatrix P) (hM : HasMultiRow M) :
    OmegaSafe (BoolMat.mul P M) :=
  Or.inl (hasMultiRow_perm_mul_left hP hM)

/-- **B8.19**: HasMultiRow * perm has HasMultiRow hence OmegaSafe. -/
theorem mul_perm_multirow_omegaSafe (M P : BoolMat 8)
    (hM : HasMultiRow M) (hP : IsPermutationMatrix P) :
    OmegaSafe (BoolMat.mul M P) :=
  Or.inl (hasMultiRow_mul_perm_right hM hP)

/-! ## Part 5: Summary -/

/-- **B8.20**: Complete summary. -/
theorem beta8_summary :
    -- (a) Counterexample exists
    (∃ P : BoolMat 8, IsPermutationMatrix P ∧ ¬ IsInSigmaGroup' P) ∧
    -- (b) Counterexample has order 4
    BoolMat.mul piPerm (BoolMat.mul piPerm
      (BoolMat.mul piPerm piPerm)) = BoolMat.one ∧
    -- (c) pi^2 in sigma group
    IsInSigmaGroup' (BoolMat.mul piPerm piPerm) ∧
    -- (d) OmegaSafe closes boolOr
    (∀ A B : BoolMat 8, OmegaSafe A → OmegaSafe B →
      ¬ IsPermutationMatrix (BoolMat.boolOr A B)) ∧
    -- (e) Rank-2 implies OmegaSafe
    (∀ M : BoolMat 8, BoolMat.rowRank M ≤ 2 → OmegaSafe M) ∧
    -- (f) h2 transfers OmegaSafe
    (OmegaSafe h2MonAB ∧ OmegaSafe h2MonBC ∧ OmegaSafe h2MonCA) :=
  ⟨⟨piPerm, piPerm_is_perm, piPerm_not_sigma⟩,
   piPerm_order_4, piPerm_sq_in_sigma,
   boolOr_omegaSafe_nonPerm', rank2_omegaSafe,
   h2_transfers_omegaSafe⟩

end CubeGraph
