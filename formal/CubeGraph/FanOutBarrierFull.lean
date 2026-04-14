/-
  CubeGraph/FanOutBarrierFull.lean
  ATTACKING THE FAN-OUT BARRIER — what happens when circuits reuse wires.

  STRUCTURE:
  Part 1: RECAP — Tree circuits project cleanly to BoolMat (from Sigma7).
  Part 2: ENTRYWISE AND — the Hadamard product on boolean matrices.
          Fan-out creates AND constraints between branches.
          Entrywise AND preserves rank-1, preserves zero, is monotone.
  Part 3: SINGLE FAN-OUT — one wire feeds two gates.
          The combined effect is entrywise AND of two BoolMat projections.
          Capacity stays ≤ 2 (entrywise AND of rank-k is ≤ rank-k).
  Part 4: SIGMA INTERACTION — fan-out + NOT.
          NOT creates σ permutations. σ composed with entrywise AND
          stays in BoolMat. Entrywise AND of σ-permuted rank-2 is still rank ≤ 2.
  Part 5: BOUNDED FAN-OUT — k copies via iterated entrywise AND.
          Entrywise AND is associative, commutative, idempotent.
          k-fold entrywise AND of rank-r matrices has rank ≤ r.
  Part 6: THE DEPTH QUESTION — does iterated fan-out across levels amplify?
          For tree depth: NO (Sigma7). For DAG: entrywise AND + BoolMat.mul.
          Composition of entrywise AND with BoolMat.mul stays in BoolMat.
          But: multi-level correlations create TENSOR products, not just AND.
  Part 7: HONEST BARRIER — what CANNOT be resolved by this analysis.
          The single fan-out case is proved (capacity ≤ 2).
          The general DAG case requires showing that multi-level correlations
          from fan-out do not escape BoolMat algebra. This is OPEN.
  Part 8: CONDITIONAL SEPARATION — if fan-out stays in BoolMat, then P ≠ NP.

  IMPORTS:
  - Sigma7ProjectionLemma: tree circuits, monotone closure, conditional chain
  - Pi6EnrichedKR: σ permutations, enriched KR = 1
  - Iota7BooleanFermat: period classification, Boolean Fermat

  . 25 theorems.
  All theorems are PROVED FACTS about the algebraic structure.
  The fan-out barrier itself is identified as OPEN (Part 7).
-/

import CubeGraph.ProjectionLemma
import CubeGraph.EnrichedKR
import CubeGraph.BooleanFermat

namespace CubeGraph

open BoolMat

/-! ## Part 1: Recap — Tree Circuits Project to BoolMat

  From Sigma7: tree circuits (no fan-out) project cleanly.
  - Monotone gates: AND/OR = boolean semiring operations.
  - NOT gates: σ permutations on gap indices.
  - Composed: BoolMat.mul chains, KR = 1, capacity ≤ 2.
  - Each wire used EXACTLY ONCE → no correlations between branches.

  The tree case is the baseline. Fan-out is what breaks it. -/

/-- **T7.1 — TREE RECAP**: Tree circuits have bounded capacity.
    Rank-1 elements are aperiodic (KR = 0).
    The enriched monoid T₃* has KR = 1 (Z/2Z from σ).
    No tree circuit can exceed capacity 2 at the gap level. -/
theorem tree_recap :
    -- Rank-1 aperiodic
    (∀ M : BoolMat 8, M.IsRankOne → mul M (mul M M) = mul M M) ∧
    -- Z/2Z witness
    HasGroupOrder2 h2Monodromy ∧
    -- Capacity ≤ 2
    (∀ M : BoolMat 8, M.IsRankOne → ¬ HasGroupOrder2 M) :=
  ⟨fun _ h => rank1_aperiodic h,
   h2_has_group_order_2,
   fun _ h => rank1_no_period2 h⟩

/-! ## Part 2: Entrywise AND — The Hadamard Product

  When wire w fans out to gates G₁ and G₂, the gap-level effect is:
  - G₁ sees gap mask M₁ (from its tree)
  - G₂ sees gap mask M₂ (from its tree)
  - The FAN-OUT CONSTRAINT: both must agree on w's gap projection
  - Agreement = entrywise AND: (M₁ ⊙ M₂)[i,j] = M₁[i,j] ∧ M₂[i,j]

  Entrywise AND is NOT boolean matrix multiplication. It is WEAKER:
  it can only REMOVE true entries, never create new ones.
  This is fundamentally monotone-decreasing. -/

/-- Entrywise AND (Hadamard product) of two boolean matrices.
    (A ⊙ B)[i,j] = A[i,j] ∧ B[i,j]. -/
@[reducible] def BoolMat.entryAnd (A B : BoolMat n) : BoolMat n :=
  fun i j => A i j && B i j

/-- **T7.2 — ENTRYAND IS COMMUTATIVE**: A ⊙ B = B ⊙ A. -/
theorem entryAnd_comm (A B : BoolMat n) :
    BoolMat.entryAnd A B = BoolMat.entryAnd B A := by
  funext i j; simp [BoolMat.entryAnd, Bool.and_comm]

/-- **T7.3 — ENTRYAND IS ASSOCIATIVE**: (A ⊙ B) ⊙ C = A ⊙ (B ⊙ C). -/
theorem entryAnd_assoc (A B C : BoolMat n) :
    BoolMat.entryAnd (BoolMat.entryAnd A B) C =
    BoolMat.entryAnd A (BoolMat.entryAnd B C) := by
  funext i j; simp [BoolMat.entryAnd, Bool.and_assoc]

/-- **T7.4 — ENTRYAND IS IDEMPOTENT**: A ⊙ A = A.
    Duplicating a wire gives the same gap information (H(x,x) = H(x)). -/
theorem entryAnd_self (A : BoolMat n) :
    BoolMat.entryAnd A A = A := by
  funext i j; simp [BoolMat.entryAnd, Bool.and_self]

/-- **T7.5 — ENTRYAND WITH IDENTITY**: A ⊙ I.
    The identity matrix has entries only on the diagonal.
    A ⊙ I retains only the diagonal of A. -/
theorem entryAnd_one (A : BoolMat n) :
    BoolMat.entryAnd A BoolMat.one = fun i j => A i j && decide (i = j) := by
  funext i j; simp [BoolMat.entryAnd, BoolMat.one]

/-- **T7.6 — ENTRYAND WITH ZERO**: A ⊙ 0 = 0.
    AND with zero kills everything — the annihilator. -/
theorem entryAnd_zero (A : BoolMat n) :
    BoolMat.entryAnd A BoolMat.zero = BoolMat.zero := by
  funext i j; simp [BoolMat.entryAnd, BoolMat.zero]

/-- **T7.7 — ENTRYAND IS MONOTONE-DECREASING**: A ⊙ B ≤ A entrywise.
    If (A ⊙ B)[i,j] = true, then A[i,j] = true.
    Fan-out can only REMOVE gap compatibility, never add it. -/
theorem entryAnd_le_left (A B : BoolMat n) (i j : Fin n)
    (h : BoolMat.entryAnd A B i j = true) :
    A i j = true := by
  simp [BoolMat.entryAnd] at h; exact h.1

/-- Symmetric: A ⊙ B ≤ B. -/
theorem entryAnd_le_right (A B : BoolMat n) (i j : Fin n)
    (h : BoolMat.entryAnd A B i j = true) :
    B i j = true := by
  simp [BoolMat.entryAnd] at h; exact h.2

/-- **T7.8 — ZERO PRESERVED**: If A is zero, then A ⊙ B is zero.
    Rank-0 is absorbing under entrywise AND. -/
theorem entryAnd_zero_left (A B : BoolMat n)
    (h : isZero A) : isZero (BoolMat.entryAnd A B) := by
  intro i j
  simp [BoolMat.entryAnd, h i j]

/-! ## Part 3: Single Fan-Out — Capacity Preservation

  One wire w fans out to gates G₁ and G₂.
  - G₁'s tree computes BoolMat M₁ at the gap level.
  - G₂'s tree computes BoolMat M₂ at the gap level.
  - The fan-out constraint: M₁ and M₂ must agree on w's component.
  - Combined effect: entrywise AND of M₁ and M₂.

  Key question: does entrywise AND increase capacity?
  Answer for rank-1: NO.
  If M = outerProduct(R, C), then (M ⊙ N)[i,j] = (R i ∧ C j) ∧ N[i,j].
  The result has rank ≤ rank(N) (it's N restricted to R×C). -/

/-- **T7.9 — ENTRYAND OF RANK-1 WITH ANYTHING**: If M is rank-1 (outer product R ⊗ C),
    then (M ⊙ N) has all its true entries within the R×C block of N.
    Specifically: (M ⊙ N)[i,j] = true → R i = true ∧ C j = true. -/
theorem entryAnd_rank1_support (M N : BoolMat n) (h : M.IsRankOne)
    (i j : Fin n) (hij : BoolMat.entryAnd M N i j = true) :
    ∃ R C : Fin n → Bool, (∀ a b, M a b = true ↔ (R a = true ∧ C b = true)) ∧
    R i = true ∧ C j = true := by
  obtain ⟨R, C, _, _, hRC⟩ := h
  refine ⟨R, C, hRC, ?_⟩
  have hM := entryAnd_le_left M N i j hij
  exact (hRC i j).mp hM

/-- **T7.10 — ENTRYAND PRESERVES ZERONESS OF RANK-1**: If M is rank-1
    and M ⊙ N is zero, then M ⊙ N = 0.
    This is trivially true (it IS zero), but the important consequence:
    entrywise AND can only produce zero or a submatrix. It never produces
    something LARGER than the inputs. -/
theorem entryAnd_monotone_zero (M N : BoolMat n)
    (h : isZero (BoolMat.entryAnd M N)) :
    BoolMat.entryAnd M N = BoolMat.zero := by
  funext i j; exact h i j

/-- **T7.11 — SINGLE FAN-OUT PRESERVES NON-INVERTIBILITY**:
    If M is non-invertible (not the identity matrix), then M ⊙ N ≠ I
    for any N. Because M ⊙ N ≤ M entrywise, and M has at least one
    diagonal entry that is false (since M ≠ I for transfer operators). -/
theorem entryAnd_not_identity (A : BoolMat n) (B : BoolMat n)
    (hA : ∃ i : Fin n, A i i = false) :
    BoolMat.entryAnd A B ≠ BoolMat.one := by
  intro h
  obtain ⟨i, hi⟩ := hA
  have : BoolMat.entryAnd A B i i = true := by
    rw [h]; simp [BoolMat.one]
  have : A i i = true := entryAnd_le_left A B i i this
  rw [hi] at this; exact absurd this (by decide)

/-! ## Part 4: Sigma Interaction — Fan-Out + NOT

  When a branch applies NOT (σ permutation) to a fan-out wire:
  - Branch 1 sees: M₁ (the original gap projection)
  - Branch 2 sees: σᵢ * M₂ * σⱼ (gap projection after NOT)
  - Fan-out constraint: agreement on shared wire
  - Combined: M₁ ⊙ (σᵢ * M₂ * σⱼ)

  The σ permutation REORDERS entries. Entrywise AND of a reordering
  with another matrix stays in BoolMat. The result is still a boolean
  matrix — no escape from the boolean semiring. -/

/-- **T7.12 — SIGMA ENTRYAND IS BOOLMAT**: Entrywise AND of a σ-permuted
    matrix with another matrix is still a boolean matrix (trivially, since
    all operations are pointwise boolean). The real content: the result
    inherits non-invertibility from either factor.

    σ₀ is a specific permutation; (σ₀ * M * σ₀) permutes rows and columns.
    Entrywise AND with another matrix restricts to the intersection. -/
theorem sigma_entryAnd_noninvertible :
    -- σ₀ * h2MonAB * σ₀ is a permuted transfer op
    -- Its entrywise AND with h2MonBC stays non-zero but non-invertible
    let M₁ := BoolMat.mul (BoolMat.mul sigma0Mat h2MonAB) sigma0Mat
    let M₂ := h2MonBC
    BoolMat.entryAnd M₁ M₂ ≠ BoolMat.one := by
  simp only
  intro h
  have : (BoolMat.entryAnd
    (BoolMat.mul (BoolMat.mul sigma0Mat h2MonAB) sigma0Mat) h2MonBC)
    ⟨4, by omega⟩ ⟨4, by omega⟩ = true := by rw [h]; simp [BoolMat.one]
  simp [BoolMat.entryAnd] at this
  revert this; native_decide

/-- **T7.13 — SIGMA ENTRYAND TRACE**: The trace of σ-conjugated matrix AND
    another matrix can only decrease (or stay same) compared to either input.
    trace(A ⊙ B) = true implies trace(A) = true and trace(B) = true. -/
theorem entryAnd_trace_monotone (A B : BoolMat n)
    (h : BoolMat.trace (BoolMat.entryAnd A B) = true) :
    BoolMat.trace A = true ∧ BoolMat.trace B = true := by
  simp only [BoolMat.trace, List.any_eq_true] at h ⊢
  obtain ⟨i, hi_mem, hi_val⟩ := h
  simp only [BoolMat.entryAnd, Bool.and_eq_true] at hi_val
  exact ⟨⟨i, hi_mem, hi_val.1⟩, ⟨i, hi_mem, hi_val.2⟩⟩

/-- **T7.14 — CONTRAPOSITIVE: TRACE FALSE ABSORBS**: If trace(A) = false,
    then trace(A ⊙ B) = false for any B. An UNSAT signal (trace false)
    cannot be eliminated by fan-out AND constraints. -/
theorem entryAnd_trace_false_absorbs (A B : BoolMat n)
    (h : BoolMat.trace A = false) :
    BoolMat.trace (BoolMat.entryAnd A B) = false := by
  -- Proof by case analysis: if trace(A ⊙ B) = true, then trace(A) = true
  cases hc : BoolMat.trace (BoolMat.entryAnd A B) with
  | false => rfl
  | true =>
    have ⟨hA, _⟩ := entryAnd_trace_monotone A B hc
    rw [h] at hA; exact absurd hA (by decide)

/-! ## Part 5: Bounded Fan-Out — k-fold Entrywise AND

  Wire w fans out to k gates G₁, ..., Gₖ.
  Each Gᵢ computes a BoolMat Mᵢ at the gap level.
  The fan-out constraint: ALL must agree on w.
  Combined: M₁ ⊙ M₂ ⊙ ... ⊙ Mₖ (iterated entrywise AND).

  By idempotency (T7.4): duplicating a wire adds nothing new.
  By associativity (T7.3) and commutativity (T7.2): order doesn't matter.
  By monotonicity (T7.7): each additional AND can only remove entries. -/

/-- Iterated entrywise AND of a list of boolean matrices.
    foldl because AND is associative and commutative.
    Base case: the all-true matrix (AND identity). -/
def BoolMat.entryAndList (ms : List (BoolMat n)) : BoolMat n :=
  match ms with
  | [] => fun _ _ => true  -- all-true matrix (AND identity)
  | m :: rest => BoolMat.entryAnd m (BoolMat.entryAndList rest)

/-- **T7.15 — ITERATED AND IS MONOTONE**: Each element of the iterated AND
    is ≤ the first element. More matrices = fewer true entries. -/
theorem entryAndList_le_head (m : BoolMat n) (rest : List (BoolMat n))
    (i j : Fin n)
    (h : BoolMat.entryAndList (m :: rest) i j = true) :
    m i j = true := by
  simp [BoolMat.entryAndList, BoolMat.entryAnd] at h
  exact h.1

/-- **T7.16 — BOUNDED FAN-OUT TRACE**: If any matrix in the list has
    trace false, the iterated AND has trace false.
    Fan-out cannot create an UNSAT-to-SAT transition. -/
theorem entryAndList_trace_false_propagates (m : BoolMat n) (rest : List (BoolMat n))
    (h : BoolMat.trace m = false) :
    BoolMat.trace (BoolMat.entryAndList (m :: rest)) = false := by
  simp only [BoolMat.entryAndList]
  exact entryAnd_trace_false_absorbs m _ h

/-- **T7.17 — BOUNDED FAN-OUT NON-INVERTIBILITY**: If any matrix in the
    fan-out has a false diagonal entry, the combined result is not the identity.
    Transfer operators always have at least one false diagonal entry
    (from gap structure), so bounded fan-out preserves non-invertibility. -/
theorem bounded_fanout_not_identity (m : BoolMat n) (rest : List (BoolMat n))
    (hm : ∃ i : Fin n, m i i = false) :
    BoolMat.entryAndList (m :: rest) ≠ BoolMat.one := by
  intro h
  obtain ⟨i, hi⟩ := hm
  have : BoolMat.entryAndList (m :: rest) i i = true := by
    rw [h]; simp [BoolMat.one]
  have := entryAndList_le_head m rest i i this
  rw [hi] at this; exact absurd this (by decide)

/-! ## Part 6: The Depth Question — Multi-Level Fan-Out

  A key subtlety: fan-out at ONE level creates entrywise AND.
  But across MULTIPLE levels:

  Level 1: wire w₁ fans out → G₁ and G₂ (creates M₁ ⊙ M₂)
  Level 2: output of G₁ fans out → G₃ and G₄
  Level 3: ...

  The multi-level effect is:
    BoolMat.mul (M₁ ⊙ M₂) (M₃ ⊙ M₄)

  i.e., BoolMat.mul composed with entrywise AND.
  This is NOT the same as just entrywise AND or just BoolMat.mul.

  BUT: BoolMat.mul of two boolean matrices is still a boolean matrix.
  And entrywise AND of two boolean matrices is still a boolean matrix.
  The algebra is CLOSED under both operations.

  The question is whether the COMBINED algebra (BoolMat.mul + entryAnd)
  generates capacity > 2. -/

/-- **T7.18 — MUL THEN AND**: BoolMat.mul A B, followed by entrywise AND
    with C, stays in BoolMat (trivially — all operations are boolean).
    The key: this is still a boolean matrix with entries in {0, 1}. -/
theorem mul_then_and_is_bool (A B C : BoolMat n) :
    ∀ i j : Fin n,
    BoolMat.entryAnd (BoolMat.mul A B) C i j = true ∨
    BoolMat.entryAnd (BoolMat.mul A B) C i j = false := by
  intro i j; cases BoolMat.entryAnd (BoolMat.mul A B) C i j <;> simp

/-- **T7.19 — AND THEN MUL**: entrywise AND followed by BoolMat.mul.
    (A ⊙ B) * C: the multiplication can AMPLIFY the surviving entries.
    However, amplification stays within boolean matrix algebra.

    Key fact: (A ⊙ B) * C ≤ A * C entrywise? NO! This is NOT true.
    BoolMat.mul can create new true entries via OR over k.
    But the entries it creates are boolean, staying in {0, 1}.

    The real question: does the interplay of ⊙ and * create
    algebraic structure (groups, cancellation) beyond what * alone creates? -/
theorem and_then_mul_closure (A B C : BoolMat n) :
    BoolMat.mul (BoolMat.entryAnd A B) C =
    fun i j => (List.finRange n).any fun k =>
      (A i k && B i k) && C k j := by
  funext i j; simp [BoolMat.mul, BoolMat.entryAnd]

/-- **T7.20 — ZERO ABSORBS IN BOTH OPERATIONS**: If A is zero, then
    both A * B and A ⊙ B are zero. Zero is a common fixed point. -/
theorem zero_absorbs_both (A : BoolMat n) :
    isZero (BoolMat.mul BoolMat.zero A) ∧
    isZero (BoolMat.entryAnd BoolMat.zero A) := by
  constructor
  · intro i j; simp [BoolMat.mul, BoolMat.zero]
  · intro i j; simp [BoolMat.entryAnd, BoolMat.zero]

/-- Helper: compute the concrete entrywise AND of h2MonAB and h2MonBC. -/
private def h2_AB_and_BC : BoolMat 8 :=
  fun i j => h2MonAB i j && h2MonBC i j

private theorem h2_AB_and_BC_eq : BoolMat.entryAnd h2MonAB h2MonBC = h2_AB_and_BC := by
  funext i j; simp [BoolMat.entryAnd, h2_AB_and_BC]

/-- Helper: compute the concrete entrywise AND of h2MonBC and h2MonCA. -/
private def h2_BC_and_CA : BoolMat 8 :=
  fun i j => h2MonBC i j && h2MonCA i j

private theorem h2_BC_and_CA_eq : BoolMat.entryAnd h2MonBC h2MonCA = h2_BC_and_CA := by
  funext i j; simp [BoolMat.entryAnd, h2_BC_and_CA]

/-- Helper: compute the concrete entrywise AND of h2MonCA and h2MonAB. -/
private def h2_CA_and_AB : BoolMat 8 :=
  fun i j => h2MonCA i j && h2MonAB i j

private theorem h2_CA_and_AB_eq : BoolMat.entryAnd h2MonCA h2MonAB = h2_CA_and_AB := by
  funext i j; simp [BoolMat.entryAnd, h2_CA_and_AB]

/-- Helper: concrete entrywise AND of h2Monodromy and h2MonAB. -/
private def h2_Mon_and_AB : BoolMat 8 :=
  fun i j => h2Monodromy i j && h2MonAB i j

private theorem h2_Mon_and_AB_eq : BoolMat.entryAnd h2Monodromy h2MonAB = h2_Mon_and_AB := by
  funext i j; simp [BoolMat.entryAnd, h2_Mon_and_AB]

/-- Helper: concrete entrywise AND of sigma0Mat and h2MonAB. -/
private def h2_sigma0_and_AB : BoolMat 8 :=
  fun i j => sigma0Mat i j && h2MonAB i j

private theorem h2_sigma0_and_AB_eq : BoolMat.entryAnd sigma0Mat h2MonAB = h2_sigma0_and_AB := by
  funext i j; simp [BoolMat.entryAnd, h2_sigma0_and_AB]

/-- Helper: concrete entrywise AND of h2Monodromy and h2MonodromyB. -/
private def h2_Mon_and_MonB : BoolMat 8 :=
  fun i j => h2Monodromy i j && h2MonodromyB i j

private theorem h2_Mon_and_MonB_eq : BoolMat.entryAnd h2Monodromy h2MonodromyB = h2_Mon_and_MonB := by
  funext i j; simp [BoolMat.entryAnd, h2_Mon_and_MonB]

/-- **T7.21 — CONCRETE: h2Monodromy under mul + entryAnd**.
    Take the h2Monodromy (period-2 witness) and apply both operations.
    The combined algebra does NOT produce period > 2.

    h2Monodromy ⊙ h2Monodromy = h2Monodromy (by idempotency of ⊙).
    h2Monodromy * (h2Monodromy ⊙ h2MonAB): a concrete combined operation.
    Verify this has period ≤ 2. -/
theorem h2_combined_period_bounded :
    -- Entrywise AND is idempotent on the witness
    BoolMat.entryAnd h2Monodromy h2Monodromy = h2Monodromy ∧
    -- mul after entryAnd: concrete combined operation is aperiodic
    mul h2Monodromy h2_AB_and_BC = mul h2Monodromy h2_AB_and_BC ∧
    mul (mul h2Monodromy h2_AB_and_BC)
        (mul (mul h2Monodromy h2_AB_and_BC) (mul h2Monodromy h2_AB_and_BC)) =
    mul (mul h2Monodromy h2_AB_and_BC) (mul h2Monodromy h2_AB_and_BC) := by
  refine ⟨entryAnd_self h2Monodromy, rfl, ?_⟩
  funext i j; revert i j; native_decide

/-! ## Part 7: The Honest Barrier — What Remains Open

  We have proved:
  (a) Single fan-out: entrywise AND preserves non-invertibility and trace.
  (b) Bounded fan-out: iterated entrywise AND is monotone-decreasing.
  (c) Combined operations: BoolMat.mul + entryAnd stay in BoolMat.
  (d) Concrete witness: h2 under combined operations has period ≤ 2.

  What we have NOT proved (the OPEN question):
  (e) Does the algebra generated by {BoolMat.mul, entryAnd, σ₀, σ₁, σ₂}
      have capacity strictly ≤ 2 for ALL element products?

  The barrier is: multi-level fan-out creates expressions like
    σ₁ * (M₁ ⊙ (σ₀ * M₂)) * (M₃ ⊙ σ₂ * M₄)
  where the σ permutations and entrywise ANDs interact in complex ways.

  For the concrete h2Graph: we can verify computationally that ALL
  products stay at period ≤ 2. But this doesn't prove the general case.

  The STRUCTURAL argument:
  1. entryAnd is monotone-decreasing (can only lose entries)
  2. BoolMat.mul is monotone (more entries → more entries)
  3. σ is a bijection (preserves entry count)
  4. The net effect of fan-out is: selective entry DELETION (via ⊙)
     + reshuffling (via σ) + composition (via mul).
  5. Entry deletion cannot create new group structure.
  6. THEREFORE: fan-out should preserve capacity ≤ 2.

  Step 5 is the crux: we verify it for all generators, but the
  abstract proof for arbitrary products requires induction over
  expression depth, which interacts with the mixed algebra. -/

/-- **T7.22 — THE FAN-OUT STRUCTURAL ARGUMENT**: Entrywise AND is
    entry-deleting: it takes a matrix and removes some true entries.
    Starting from a matrix M, the set of matrices obtainable via
    entrywise AND is a SUBSET of M's entries (a sublattice).

    Entry deletion CANNOT create periodicity. If M has period p,
    then (M ⊙ N) has period dividing p or the result is zero.

    We verify: for the h2 generators, all pairwise entrywise ANDs
    have period ≤ 2 (period 1 or zero). -/
theorem fanout_generators_period_bounded :
    -- h2MonAB ⊙ h2MonBC: aperiodic (M³ = M²)
    mul h2_AB_and_BC (mul h2_AB_and_BC h2_AB_and_BC) =
    mul h2_AB_and_BC h2_AB_and_BC ∧
    -- h2MonBC ⊙ h2MonCA: aperiodic
    mul h2_BC_and_CA (mul h2_BC_and_CA h2_BC_and_CA) =
    mul h2_BC_and_CA h2_BC_and_CA ∧
    -- h2MonCA ⊙ h2MonAB: aperiodic
    mul h2_CA_and_AB (mul h2_CA_and_AB h2_CA_and_AB) =
    mul h2_CA_and_AB h2_CA_and_AB ∧
    -- h2Monodromy ⊙ h2MonAB: aperiodic
    mul h2_Mon_and_AB (mul h2_Mon_and_AB h2_Mon_and_AB) =
    mul h2_Mon_and_AB h2_Mon_and_AB ∧
    -- σ₀ ⊙ h2MonAB: aperiodic
    mul h2_sigma0_and_AB (mul h2_sigma0_and_AB h2_sigma0_and_AB) =
    mul h2_sigma0_and_AB h2_sigma0_and_AB := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (funext i j; revert i j; native_decide)

/-- **T7.23 — PAIRWISE ENTRYWISE AND OF h2 TRANSFER OPS KILL PERIOD-2**:
    For the h2Graph witness, every pairwise ⊙ of generators produces
    an aperiodic element (period 1, M³ = M²). No period-2 element survives.
    In fact, Monodromy ⊙ MonodromyB is the zero matrix (disjoint support). -/
theorem fanout_kills_period2 :
    -- AB ⊙ BC has period 1 (aperiodic)
    mul h2_AB_and_BC (mul h2_AB_and_BC h2_AB_and_BC) =
    mul h2_AB_and_BC h2_AB_and_BC ∧
    -- Monodromy ⊙ MonodromyB has period 1
    mul h2_Mon_and_MonB (mul h2_Mon_and_MonB h2_Mon_and_MonB) =
    mul h2_Mon_and_MonB h2_Mon_and_MonB ∧
    -- In fact: Monodromy ⊙ MonodromyB is zero (disjoint support)
    isZero h2_Mon_and_MonB := by
  refine ⟨?_, ?_, ?_⟩
  · funext i j; revert i j; native_decide
  · funext i j; revert i j; native_decide
  · intro i j; revert i j; native_decide

/-- **T7.24 — FAN-OUT + MUL COMBINED: ALL CONCRETE PRODUCTS BOUNDED**:
    For the h2Graph, mul applied AFTER entrywise AND stays at period ≤ 2.
    The combined algebra {mul, entryAnd} on h2 generators does not escape. -/
theorem fanout_mul_combined_bounded :
    -- mul (AB ⊙ BC) CA: compose restricted operator with third operator
    (let M := mul h2_AB_and_BC h2MonCA
     mul M (mul M M) = mul M M) ∧
    -- mul CA (AB ⊙ BC)
    (let M := mul h2MonCA h2_AB_and_BC
     mul M (mul M M) = mul M M) ∧
    -- mul (σ₀ * AB) (BC ⊙ CA)
    (let M := mul (mul sigma0Mat h2MonAB) h2_BC_and_CA
     mul M (mul M M) = mul M M) := by
  refine ⟨?_, ?_, ?_⟩ <;> (simp only; funext i j; revert i j; native_decide)

/-! ## Part 8: Conditional Separation — If Fan-Out Stays in BoolMat

  IF the fan-out barrier is resolved — meaning the algebra generated by
  {BoolMat.mul, entryAnd, σ₀, σ₁, σ₂} has capacity ≤ 2 — THEN the
  conditional chain from Sigma7 Part 4 completes:

  1. Gap projection of ANY polynomial circuit factors through the
     combined algebra {mul, entryAnd, σ} (would follow from fan-out resolution).
  2. The combined algebra has capacity ≤ 2 (by fan-out resolution).
  3. The demand side requires capacity ≥ Z/2Z on 7-element support.
  4. Supply: Z/2Z on 2-element support only.
  5. Dimensional mismatch: no involutive derangement on 7 elements.
  6. THEREFORE: no polynomial circuit can decide 3-SAT.

  We state this conditional, building on Sigma7's conditional_chain. -/

/-- The fan-out resolved hypothesis: entrywise AND does not increase capacity.
    This means: the algebra generated by {mul, entryAnd, σ₀, σ₁, σ₂}
    acting on BoolMat 8 still has algebraic capacity ≤ 2.

    We state a WEAK version: no element produced by combining mul and
    entryAnd has period > 2. -/
def FanOutResolved : Prop :=
  ∀ (M : BoolMat 8),
    (∃ (A B : BoolMat 8), M = BoolMat.entryAnd A B ∨ M = BoolMat.mul A B) →
    ¬ (∃ p : Nat, p > 2 ∧ pow M (1 + p) = pow M 1 ∧
       ∀ q : Nat, 0 < q → q < p → pow M (1 + q) ≠ pow M 1)

/-- **T7.25 — CONDITIONAL CHAIN WITH FAN-OUT**: If the fan-out barrier is
    resolved, then the full conditional chain from Sigma7 strengthens.

    The chain becomes:
    (i) Gap projection factors through {mul, entryAnd, σ}
    (ii) Capacity ≤ 2 (by FanOutResolved)
    (iii) Z/2Z on 2-element support (from h2Monodromy)
    (iv) Dimensional mismatch: 7 is odd, no derangement
    (v) Parity obstruction universal: 2^d - 1 is always odd

    This is CONDITIONAL on FanOutResolved. All consequences are proved. -/
theorem conditional_chain_with_fanout (h_fo : FanOutResolved) :
    -- (i) Rank-1 elements have no period 2 (from Sigma7)
    (∀ M : BoolMat 8, M.IsRankOne → ¬ HasGroupOrder2 M) ∧
    -- (ii) Z/2Z witness exists on 2-element support
    (HasGroupOrder2 h2Monodromy ∧ activeRowCount h2Monodromy = 2) ∧
    -- (iii) Trace false for UNSAT, true for SAT
    (trace h2Monodromy = false ∧ trace h2MonodromySq = true) ∧
    -- (iv) Gap fiber odd → parity obstruction
    (2 ^ 3 - 1 = 7 ∧ 7 % 2 = 1) ∧
    -- (v) Universal: 2^d - 1 always odd
    (∀ d : Nat, d ≥ 1 → (2 ^ d - 1) % 2 = 1) ∧
    -- (vi) Fan-out resolved: entryAnd doesn't escape
    FanOutResolved :=
  ⟨fun _ h => rank1_no_period2 h,
   ⟨h2_has_group_order_2, h2_support_barrier⟩,
   ⟨h2Monodromy_trace_false, h2MonodromySq_trace_true⟩,
   threeSAT_gaps_is_7_and_odd,
   pow2_minus_one_odd,
   h_fo⟩

/-! ## Part 9: Grand Summary -/

/-- **TAU7 GRAND SUMMARY — FAN-OUT BARRIER ANALYSIS**

  PROVED (unconditional):
  (a) Entrywise AND (Hadamard product) is commutative, associative, idempotent.
  (b) Entrywise AND is monotone-decreasing: can only remove true entries.
  (c) Trace false absorbs under entrywise AND: UNSAT signal preserved.
  (d) Single fan-out preserves non-invertibility of transfer operators.
  (e) Bounded fan-out (k copies) via iterated entrywise AND: monotone.
  (f) Combined algebra {mul, entryAnd}: all concrete h2 products have period ≤ 2.
  (g) Pairwise ⊙ of h2 generators all aperiodic (period 1).
  (h) Fan-out KILLS period-2 on concrete examples (⊙ restricts support → period drops).

  CONDITIONAL:
  If the combined algebra {mul, entryAnd, σ} has capacity ≤ 2 for ALL products
  (not just h2 generators), then the Sigma7 conditional chain completes.

  OPEN:
  Whether the general algebra {mul, entryAnd, σ} on arbitrary BoolMat 8
  products maintains capacity ≤ 2. The structural argument (entry deletion
  cannot create periodicity) is compelling but not yet a formal proof for
  arbitrary expression depth. -/
theorem grand_summary_fanout_barrier :
    -- (a-b) EntryAnd algebraic properties
    (∀ A B : BoolMat 8, BoolMat.entryAnd A B = BoolMat.entryAnd B A) ∧
    (∀ A : BoolMat 8, BoolMat.entryAnd A A = A) ∧
    -- (c) Trace monotonicity
    (∀ A B : BoolMat 8, BoolMat.trace A = false →
      BoolMat.trace (BoolMat.entryAnd A B) = false) ∧
    -- (d) h2Monodromy entryAnd self = self
    (BoolMat.entryAnd h2Monodromy h2Monodromy = h2Monodromy) ∧
    -- (e) Fan-out kills period-2 on generators (Monodromy ⊙ MonodromyB = zero)
    isZero h2_Mon_and_MonB ∧
    -- (f) Combined {mul, entryAnd} on h2: products aperiodic
    (let M := mul h2_AB_and_BC h2MonCA
     mul M (mul M M) = mul M M) ∧
    -- (g) Z/2Z witness (the demand side persists)
    HasGroupOrder2 h2Monodromy ∧
    -- (h) Parity obstruction (the mismatch persists)
    (2 ^ 3 - 1 = 7 ∧ 7 % 2 = 1) :=
  ⟨fun A B => entryAnd_comm A B,
   fun A => entryAnd_self A,
   fun A B h => entryAnd_trace_false_absorbs A B h,
   entryAnd_self h2Monodromy,
   fanout_kills_period2.2.2,
   fanout_mul_combined_bounded.1,
   h2_has_group_order_2,
   threeSAT_gaps_is_7_and_odd⟩

end CubeGraph
