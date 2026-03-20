/-
  CubeGraph/TaylorBarrier.lean
  Taylor polymorphism barrier: ≠ on Fin 3 has no WNU3 polymorphism.

  The CSP Dichotomy Theorem (Bulatov 2017, Zhuk 2020):
    CSP(Γ) ∈ P iff Γ admits a Taylor polymorphism (equivalently, a WNU).

  We prove:
  - POSITIVE: majority on Fin 2 is a WNU3 that preserves ≠ → 2-coloring ∈ P
  - NEGATIVE: no WNU3 on Fin 3 preserves ≠ → 3-coloring NP-complete (Bool + Prop levels)

  Connection to CubeGraph: transfer operators at critical density generate
  constraint relations containing ≠ on shared-variable projections
  (computationally verified: check_wnu_junction.py, check_taylor_kmm.py).
  Hence no Taylor polymorphism for the full CubeGraph constraint language.

  See: formal/CubeGraph/InvertibilityBarrier.lean (Barrier 1: XOR invertibility)
  See: formal/CubeGraph/HornBarrier.lean (Barrier 2: Horn OR-closed gaps)
  See: formal/CubeGraph/DualHornBarrier.lean (Barrier 2b: Dual-Horn AND-closed gaps)
  See: formal/CubeGraph/TrivialSection.lean (Barrier 3: trivial section)
  See: formal/CubeGraph/Rank1AC.lean (Barrier 4: rank-1 + AC → SAT)
  See: formal/CubeGraph/FunctionalTransfer.lean (Barrier 5: functional composition)
  See: formal/CubeGraph/BarrierSummary.lean (Meta: witness failing all 5 barriers)
  See: formal/CubeGraph/FiberDichotomy.lean (fiber=3 → relational → NP boundary)
  See: experiments-ml/008_2026-03-04_why-h2-hard/CSP-DICHOTOMY.md
  See: experiments-ml/011_2026-03-05_polynomial-barriers/TRACKING.md (W4)
  See: experiments-ml/011_2026-03-05_polynomial-barriers/PLAN-SEMANTIC-BRIDGE.md (Section 6 plan)
-/

import CubeGraph.Basic

namespace CubeGraph

/-! ## Section 1: WNU Definitions -/

/-- Weak Near-Unanimity of arity 3: idempotent + symmetric on two-equal inputs.
    f(x,x,x) = x and f(y,x,x) = f(x,y,x) = f(x,x,y) for all x,y.
    Taylor polymorphism ⟺ WNU ⟺ Siggers on finite domains. -/
def IsWNU3 (n : Nat) (f : Fin n → Fin n → Fin n → Fin n) : Prop :=
  (∀ x : Fin n, f x x x = x) ∧
  (∀ x y : Fin n, f x y y = f y x y ∧ f y x y = f y y x)

/-- A ternary operation preserves a binary relation R:
    R(a₁,b₁) ∧ R(a₂,b₂) ∧ R(a₃,b₃) → R(f(a₁,a₂,a₃), f(b₁,b₂,b₃)). -/
def PreservesRel (n : Nat) (f : Fin n → Fin n → Fin n → Fin n)
    (R : Fin n → Fin n → Bool) : Prop :=
  ∀ a₁ b₁ a₂ b₂ a₃ b₃ : Fin n,
    R a₁ b₁ = true → R a₂ b₂ = true → R a₃ b₃ = true →
    R (f a₁ a₂ a₃) (f b₁ b₂ b₃) = true

/-! ## Section 2: Positive Example — Majority on Fin 2

  The majority function is a WNU3 that preserves ≠ on Fin 2.
  This is why 2-SAT (and 2-coloring) are in P: the constraint
  language admits a Taylor polymorphism. -/

/-- Majority vote on Fin 2: returns the value appearing ≥ 2 times. -/
def majority2 (a b c : Fin 2) : Fin 2 :=
  if a == b then a else c

/-- ≠ on Fin 2 (the constraint of 2-coloring / 2-SAT implication). -/
def neq2 (a b : Fin 2) : Bool := a != b

/-- Majority is a WNU3 on Fin 2. -/
theorem majority2_wnu : IsWNU3 2 majority2 := by
  constructor
  · intro x; revert x; native_decide
  · intro x y; revert y; revert x; native_decide

/-- Majority preserves ≠ on Fin 2: the algebraic reason 2-coloring is in P. -/
theorem majority2_preserves_neq : PreservesRel 2 majority2 neq2 := by
  intro a₁ b₁ a₂ b₂ a₃ b₃
  revert a₁ b₁ a₂ b₂ a₃ b₃; native_decide

/-! ## Section 3: WNU3 Construction on Fin 3

  A WNU3 on Fin 3 is determined by 12 free parameters:
  - 6 values for "two-equal" inputs (WNU symmetry equates 3 inputs per group)
  - 6 values for "all-different" inputs (no WNU constraint)
  Total: 3¹² = 531,441 candidates.

  Encoding: input (a,b,c) → idx = a·9 + b·3 + c ∈ [0..26]
  - All-same: {0, 13, 26} → fixed (idempotent)
  - Two-equal: 6 groups of 3 indices → 6 free parameters
  - All-different: 6 single indices → 6 free parameters -/

/-- ≠ on Fin 3 (the constraint of graph 3-coloring). -/
def neq3 (a b : Fin 3) : Bool := a != b

/-- Build a WNU3 function on Fin 3 from 12 free parameters.
    Idempotent and WNU-symmetric by construction.

    Parameters m01..m21: values for two-equal inputs
      m01 = f(0,0,1) = f(0,1,0) = f(1,0,0)  (two 0's, one 1)
      m02 = f(0,0,2) = f(0,2,0) = f(2,0,0)  (two 0's, one 2)
      m10 = f(0,1,1) = f(1,0,1) = f(1,1,0)  (two 1's, one 0)
      m12 = f(1,1,2) = f(1,2,1) = f(2,1,1)  (two 1's, one 2)
      m20 = f(0,2,2) = f(2,0,2) = f(2,2,0)  (two 2's, one 0)
      m21 = f(1,2,2) = f(2,1,2) = f(2,2,1)  (two 2's, one 1)
    Parameters d012..d210: values for all-different inputs -/
def mkWNU3Direct (m01 m02 m10 m12 m20 m21
    d012 d021 d102 d120 d201 d210 : Fin 3)
    (a b c : Fin 3) : Fin 3 :=
  let idx := a.val * 9 + b.val * 3 + c.val
  -- Idempotent: f(x,x,x) = x
  if idx == 0 then 0 else if idx == 13 then 1 else if idx == 26 then 2
  -- Two-equal (WNU: all permutations of "two x's, one y" give same value)
  else if idx == 1 || idx == 3 || idx == 9 then m01      -- (0,0,1),(0,1,0),(1,0,0)
  else if idx == 2 || idx == 6 || idx == 18 then m02     -- (0,0,2),(0,2,0),(2,0,0)
  else if idx == 4 || idx == 10 || idx == 12 then m10    -- (0,1,1),(1,0,1),(1,1,0)
  else if idx == 14 || idx == 16 || idx == 22 then m12   -- (1,1,2),(1,2,1),(2,1,1)
  else if idx == 8 || idx == 20 || idx == 24 then m20    -- (0,2,2),(2,0,2),(2,2,0)
  else if idx == 17 || idx == 23 || idx == 25 then m21   -- (1,2,2),(2,1,2),(2,2,1)
  -- All-different (unconstrained by WNU)
  else if idx == 5 then d012      -- (0,1,2)
  else if idx == 7 then d021      -- (0,2,1)
  else if idx == 11 then d102     -- (1,0,2)
  else if idx == 15 then d120     -- (1,2,0)
  else if idx == 19 then d201     -- (2,0,1)
  else d210                       -- (2,1,0) [idx == 21]

/-- Check if a ternary operation on Fin 3 preserves ≠ (decidable Bool version).
    Tests all 6³ = 216 triples of ≠-pairs. Short-circuits on first violation. -/
def checkPreservesNeq3 (f : Fin 3 → Fin 3 → Fin 3 → Fin 3) : Bool :=
  let pairs : List (Fin 3 × Fin 3) := [(0,1), (0,2), (1,0), (1,2), (2,0), (2,1)]
  pairs.all fun (a₁, b₁) =>
  pairs.all fun (a₂, b₂) =>
  pairs.all fun (a₃, b₃) =>
    f a₁ a₂ a₃ != f b₁ b₂ b₃

/-! ## Section 4: Exhaustive Verification -/

/-- Exhaustive check: no WNU3 on Fin 3 preserves ≠.
    Iterates over all 3¹² = 531,441 WNU3 candidates via 12 nested loops. -/
def noWNU3PreservesNeq3 : Bool :=
  (List.finRange 3).all fun m01 =>
  (List.finRange 3).all fun m02 =>
  (List.finRange 3).all fun m10 =>
  (List.finRange 3).all fun m12 =>
  (List.finRange 3).all fun m20 =>
  (List.finRange 3).all fun m21 =>
  (List.finRange 3).all fun d012 =>
  (List.finRange 3).all fun d021 =>
  (List.finRange 3).all fun d102 =>
  (List.finRange 3).all fun d120 =>
  (List.finRange 3).all fun d201 =>
  (List.finRange 3).all fun d210 =>
    !(checkPreservesNeq3 (mkWNU3Direct m01 m02 m10 m12 m20 m21
                           d012 d021 d102 d120 d201 d210))

/-- **No WNU3 on Fin 3 preserves ≠** (verified exhaustively, 531,441 candidates).

    This is the algebraic reason 3-coloring is NP-complete:
    the CSP Dichotomy Theorem says CSP(Γ) ∈ P iff Γ admits a Taylor
    polymorphism (equiv. WNU), and ≠ on Fin 3 has none.

    For CubeGraph: since Γ_cube ⊇ ≠ at critical density (computationally
    verified), no Taylor polymorphism exists for 3-SAT's CubeGraph. -/
theorem noWNU3PreservesNeq3_verified : noWNU3PreservesNeq3 = true := by
  native_decide

/-! ## Section 5: The WNU Dichotomy

  | Domain | WNU3 preserving ≠ | CSP(≠)  | Complexity |
  |--------|-------------------|---------|------------|
  | Fin 2  | majority2 ✓       | 2-COL   | **P**      |
  | Fin 3  | NONE ✗             | 3-COL   | **NP-c**   |

  Three complementary barriers explain the same P/NP threshold:
  1. **TaylorBarrier** (this file): ≠ on Fin 3 has no WNU → CSP NP-hard
  2. **InvertibilityBarrier**: OR absorbs → boolean matrix composition non-invertible
  3. **FiberDichotomy**: fiber=3 → relational transfer → monoid (not group)

  All three say: k=3 crosses the algebraic boundary from tractable to intractable.

  CubeGraph contribution: these abstract algebraic facts become CONCRETE
  at critical density ρ ≈ 4.27, where 100% of UNSAT is H² (global incoherence)
  with no local witness. The absence of Taylor polymorphism explains WHY
  no polynomial-time algorithm can detect H² in general. -/

/-! ## Section 6: Semantic Bridge (Bool → Prop)

  The exhaustive check `noWNU3PreservesNeq3_verified` operates at the Bool level.
  This section lifts it to Prop: ∀ f, IsWNU3 3 f → ¬PreservesRel 3 f neq3.

  Strategy:
  1. Coverage: any WNU3 on Fin 3 ≡ mkWNU3Direct with its own values
  2. Bridge: PreservesRel → checkPreservesNeq3 = true
  3. Contradiction with exhaustive Bool check -/

/-- Any WNU3 on Fin 3 is extensionally equal to `mkWNU3Direct` instantiated
    with its own output values as parameters.
    Reduces from 3^27 possible functions to 3^12 WNU3 candidates. -/
theorem wnu3_coverage (f : Fin 3 → Fin 3 → Fin 3 → Fin 3) (hf : IsWNU3 3 f)
    (a b c : Fin 3) :
    f a b c = mkWNU3Direct (f 0 0 1) (f 0 0 2) (f 0 1 1) (f 1 1 2)
              (f 0 2 2) (f 1 2 2) (f 0 1 2) (f 0 2 1) (f 1 0 2)
              (f 1 2 0) (f 2 0 1) (f 2 1 0) a b c := by
  obtain ⟨hi, hw⟩ := hf
  match a, b, c with
  | 0, 0, 0 => exact hi 0
  | 0, 0, 1 => rfl
  | 0, 0, 2 => rfl
  | 0, 1, 0 => exact (hw 1 0).2
  | 0, 1, 1 => rfl
  | 0, 1, 2 => rfl
  | 0, 2, 0 => exact (hw 2 0).2
  | 0, 2, 1 => rfl
  | 0, 2, 2 => rfl
  | 1, 0, 0 => exact (hw 1 0).1.trans (hw 1 0).2
  | 1, 0, 1 => exact (hw 0 1).1.symm
  | 1, 0, 2 => rfl
  | 1, 1, 0 => exact ((hw 0 1).1.trans (hw 0 1).2).symm
  | 1, 1, 1 => exact hi 1
  | 1, 1, 2 => rfl
  | 1, 2, 0 => rfl
  | 1, 2, 1 => exact (hw 2 1).2
  | 1, 2, 2 => rfl
  | 2, 0, 0 => exact (hw 2 0).1.trans (hw 2 0).2
  | 2, 0, 1 => rfl
  | 2, 0, 2 => exact (hw 0 2).1.symm
  | 2, 1, 0 => rfl
  | 2, 1, 1 => exact (hw 2 1).1.trans (hw 2 1).2
  | 2, 1, 2 => exact (hw 1 2).1.symm
  | 2, 2, 0 => exact ((hw 0 2).1.trans (hw 0 2).2).symm
  | 2, 2, 1 => exact ((hw 1 2).1.trans (hw 1 2).2).symm
  | 2, 2, 2 => exact hi 2

/-- All pairs in checkPreservesNeq3's test list satisfy neq3. -/
private theorem mem_pairs_neq3 (a b : Fin 3)
    (h : (a, b) ∈ ([(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)] : List (Fin 3 × Fin 3))) :
    neq3 a b = true := by
  revert h a b; native_decide

/-- Bridge: PreservesRel 3 f neq3 implies the Bool check passes. -/
theorem preservesRel_implies_check (f : Fin 3 → Fin 3 → Fin 3 → Fin 3)
    (h : PreservesRel 3 f neq3) : checkPreservesNeq3 f = true := by
  simp only [checkPreservesNeq3]
  apply List.all_eq_true.mpr; intro ⟨a₁, b₁⟩ h₁
  apply List.all_eq_true.mpr; intro ⟨a₂, b₂⟩ h₂
  apply List.all_eq_true.mpr; intro ⟨a₃, b₃⟩ h₃
  exact h a₁ b₁ a₂ b₂ a₃ b₃
    (mem_pairs_neq3 a₁ b₁ h₁) (mem_pairs_neq3 a₂ b₂ h₂) (mem_pairs_neq3 a₃ b₃ h₃)

/-- All mkWNU3Direct instances fail the neq3 check (exhaustive, 3^12 = 531K candidates). -/
private theorem all_check_false :
    ∀ (m01 m02 m10 m12 m20 m21 d012 d021 d102 d120 d201 d210 : Fin 3),
    checkPreservesNeq3 (mkWNU3Direct m01 m02 m10 m12 m20 m21
                        d012 d021 d102 d120 d201 d210) = false := by
  native_decide

/-- **No WNU3 on Fin 3 preserves ≠** (semantic Prop-level theorem).
    Lifts `noWNU3PreservesNeq3_verified` from Bool to Prop.

    Combined with CSP Dichotomy (Bulatov 2017, Zhuk 2020): any CSP whose constraint
    language contains ≠ on a 3-element domain is NP-complete. This includes
    CubeGraph's Γ_cube at critical density, where transfer operators generate ≠
    on shared-variable projections (verified: check_taylor_kmm.py).

    See: experiments-ml/008_2026-03-04_why-h2-hard/CSP-DICHOTOMY.md -/
theorem no_wnu3_preserves_neq3 :
    ∀ f : Fin 3 → Fin 3 → Fin 3 → Fin 3,
    IsWNU3 3 f → ¬PreservesRel 3 f neq3 := by
  intro f hf hpres
  -- Step 1: Coverage — f ≡ mkWNU3Direct with f's own output values
  have hcov := wnu3_coverage f hf
  -- Step 2: Transfer PreservesRel from f to its mkWNU3Direct representation
  have hg : PreservesRel 3
      (mkWNU3Direct (f 0 0 1) (f 0 0 2) (f 0 1 1) (f 1 1 2) (f 0 2 2) (f 1 2 2)
                    (f 0 1 2) (f 0 2 1) (f 1 0 2) (f 1 2 0) (f 2 0 1) (f 2 1 0))
      neq3 := by
    intro a₁ b₁ a₂ b₂ a₃ b₃ h₁ h₂ h₃
    rw [← hcov a₁ a₂ a₃, ← hcov b₁ b₂ b₃]
    exact hpres a₁ b₁ a₂ b₂ a₃ b₃ h₁ h₂ h₃
  -- Step 3: Bridge to Bool — PreservesRel implies check = true
  have htrue := preservesRel_implies_check _ hg
  -- Step 4: But exhaustive check says check = false for ALL mkWNU3Direct instances
  have hfalse := all_check_false (f 0 0 1) (f 0 0 2) (f 0 1 1) (f 1 1 2)
    (f 0 2 2) (f 1 2 2) (f 0 1 2) (f 0 2 1) (f 1 0 2) (f 1 2 0) (f 2 0 1) (f 2 1 0)
  -- Contradiction: true = false
  exact absurd (htrue.symm.trans hfalse) (by decide)

end CubeGraph
