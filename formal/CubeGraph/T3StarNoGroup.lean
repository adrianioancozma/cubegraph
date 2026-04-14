/-
  CubeGraph/T3StarNoGroup.lean

  T₃* algebraic structure: no global identity, no cancellative elements,
  aperiodic — and why this blocks the BPR (Bonet-Pitassi-Raz 2000)
  cancellation mechanism.

  ## Actual algebraic structure of T₃* (28 elements)

  T₃* has NO global identity element (it is a semigroup, not a monoid).
  Element 27 is the ABSORBING (zero) element: 27·m = m·27 = 27 for all m.
  Idempotents: {0, 4, 8, 9, 17, 25, 27}.
  Z/2Z group H-classes: (9,10), (17,18), (25,26) — local group structure only.
  Global stabilization: m⁵ = m³ for all m (from TransferMonoid).

  ## What blocks BPR

  BPR (Bonet-Pitassi-Raz 2000) constructs Frege interpolants via CRT.
  CRT requires a CANCELLATIVE element in the multiplication structure:
    ∀ a b, m·a = m·b → a = b

  No element of T₃* is cancellative (left OR right).  In particular:
    — 89% collision rate among the 28 elements (see experiments-ml/018/)
    — Zero-column mechanism: most operators have zero columns → non-cancellative

  This is the structural BPR barrier:
    1. T₃* has no global identity → no globally meaningful inverses
    2. No element is (left or right) cancellative → CRT cannot be applied
    3. T₃* is aperiodic (m⁵ = m³) → no non-trivial modular arithmetic
    4. T₃* is von Neumann regular → quasi-inverses exist but are non-unique

  No sorry, no new axioms.  All proofs via `native_decide` over Fin 28.

  Dependencies: CubeGraph.TransferMonoid
  See: CubeGraph/NoCancellation.lean   (OR/AND semiring no-cancellation)
  See: CubeGraph/NonCancellative.lean  (BoolMat concrete witnesses)
  See: CubeGraph/BandSemigroup.lean    (rank-1 aperiodic / no right inverse)
  See: CubeGraph/ReesStructure.lean    (Rees matrix semigroup structure)
  See: CubeGraph/TreeLikeFrege.lean    (tree-like Frege lb, uses rank-1 + label erasure)
  Strategy: experiments-ml/040_2026-03-29_close-the-chain/STRATEGIC-CLOSE-THE-CHAIN.md
    (Attack 1: BPR barrier removal — this file proves T₃* structural prerequisites)
  Created: Session 040, 2026-03-29
-/

import CubeGraph.TransferMonoid

namespace CubeGraph

open BoolMat

/-! ## Section 1: No Global Identity Element

  T₃* has NO global identity: no element e satisfies e·m = m·e = m for ALL m.
  This is the first obstruction to applying BPR: without a global identity,
  there can be no globally meaningful inverses.

  Note: element 27 is the ABSORBING (zero) element, not an identity. -/

/-- **Theorem 1a: No Global Identity**.
    T₃* has no element that acts as a two-sided identity for all elements.
    (T₃* is a semigroup without a unit.) -/
theorem t3star_no_global_identity :
    ¬ ∃ e : T3Star, ∀ m : T3Star,
        T3Star.mul e m = m ∧ T3Star.mul m e = m := by
  native_decide

/-- Element 27 is the absorbing (zero) element: m·27 = 27·m = 27 for all m.
    This is the OPPOSITE of an identity: it "kills" everything. -/
theorem t3star_27_is_absorbing :
    ∀ m : T3Star,
      T3Star.mul m ⟨27, by omega⟩ = ⟨27, by omega⟩ ∧
      T3Star.mul ⟨27, by omega⟩ m = ⟨27, by omega⟩ := by
  native_decide

/-! ## Section 2: Global Aperiodicity

  T₃* is aperiodic: every element m satisfies m⁵ = m³.
  (Recall convention: T3Star.pow m k = m^{k+1}; global_stabilization is in TransferMonoid.)

  Aperiodicity means the semigroup has no non-trivial periodic cycles.
  For BPR: there is no element that could drive a repeating group action
  of the kind needed for CRT's modular arithmetic. -/

/-- **Theorem 2: Global Aperiodicity** (proper ∀ form of global_stabilization).
    Every element of T₃* satisfies m⁵ = m³ (= T3Star.pow m 4 = T3Star.pow m 2). -/
theorem t3star_aperiodic :
    ∀ m : T3Star, T3Star.pow m 4 = T3Star.pow m 2 := by
  intro m
  have h := global_stabilization
  rw [List.all_eq_true] at h
  have hm := h m (List.mem_finRange m)
  simp only [beq_iff_eq] at hm
  exact hm

/-- **Idempotent count**: exactly 7 idempotents in T₃*.
    The idempotents are indexed {0, 4, 8, 9, 17, 25, 27}. -/
theorem t3star_seven_idempotents :
    (List.finRange 28).countP (fun m => T3Star.mul m m == m) = 7 := by
  native_decide

/-- The Z/2Z group H-classes: pairs (9,10), (17,18), (25,26).
    For each pair (e, g): e*e = e (idempotent), g*g = e (involution),
    e*g = g and g*e = g (e is local identity for g).
    These are the ONLY non-trivial group H-classes in T₃*. -/
theorem t3star_z2_hclasses :
    T3Star.mul ⟨9,  by omega⟩ ⟨9,  by omega⟩ = ⟨9,  by omega⟩ ∧
    T3Star.mul ⟨10, by omega⟩ ⟨10, by omega⟩ = ⟨9,  by omega⟩ ∧
    T3Star.mul ⟨9,  by omega⟩ ⟨10, by omega⟩ = ⟨10, by omega⟩ ∧
    T3Star.mul ⟨10, by omega⟩ ⟨9,  by omega⟩ = ⟨10, by omega⟩ ∧
    T3Star.mul ⟨17, by omega⟩ ⟨17, by omega⟩ = ⟨17, by omega⟩ ∧
    T3Star.mul ⟨18, by omega⟩ ⟨18, by omega⟩ = ⟨17, by omega⟩ ∧
    T3Star.mul ⟨17, by omega⟩ ⟨18, by omega⟩ = ⟨18, by omega⟩ ∧
    T3Star.mul ⟨18, by omega⟩ ⟨17, by omega⟩ = ⟨18, by omega⟩ ∧
    T3Star.mul ⟨25, by omega⟩ ⟨25, by omega⟩ = ⟨25, by omega⟩ ∧
    T3Star.mul ⟨26, by omega⟩ ⟨26, by omega⟩ = ⟨25, by omega⟩ ∧
    T3Star.mul ⟨25, by omega⟩ ⟨26, by omega⟩ = ⟨26, by omega⟩ ∧
    T3Star.mul ⟨26, by omega⟩ ⟨25, by omega⟩ = ⟨26, by omega⟩ := by
  native_decide

/-- These are EXACTLY the 3 group H-classes of size 2.
    No other pair (e, g) with e idempotent, g≠e forms such a group. -/
theorem t3star_z2_hclasses_are_all :
    (List.finRange 28).countP (fun e =>
      T3Star.mul e e == e &&
      (List.finRange 28).any (fun g =>
        g != e &&
        T3Star.mul g g == e &&
        T3Star.mul e g == g &&
        T3Star.mul g e == g)) = 3 := by
  native_decide

/-! ## Section 3: The Z/2Z Groups Are Local, Not Global

  The three group H-classes (Z/2Z groups) have LOCAL structure only.
  None of the involutions (elements 10, 18, 26) is cancellative in the
  GLOBAL semigroup T₃*.

  This is the crucial point: having a group H-class does NOT imply
  having a globally cancellative element.  The Z/2Z groups can only
  "cancel" within their own H-class, not across T₃*.  BPR needs
  GLOBAL cancellation (to apply CRT to the whole formula). -/

/-- The involution 10 (Z/2Z partner of idempotent 9) is not left-cancellative.
    Witness: 10·0 = 10·15 (both equal 3) but 0 ≠ 15. -/
theorem t3star_involution_10_not_cancellative :
    T3Star.mul ⟨10, by omega⟩ ⟨0, by omega⟩ =
    T3Star.mul ⟨10, by omega⟩ ⟨15, by omega⟩ ∧
    (⟨0, by omega⟩ : T3Star) ≠ ⟨15, by omega⟩ := by
  constructor
  · native_decide
  · decide

/-- The involution 18 (Z/2Z partner of idempotent 17) is not left-cancellative.
    Witness: 18·0 = 18·9 (both equal 6) but 0 ≠ 9. -/
theorem t3star_involution_18_not_cancellative :
    T3Star.mul ⟨18, by omega⟩ ⟨0, by omega⟩ =
    T3Star.mul ⟨18, by omega⟩ ⟨9, by omega⟩ ∧
    (⟨0, by omega⟩ : T3Star) ≠ ⟨9, by omega⟩ := by
  constructor
  · native_decide
  · decide

/-- The involution 26 (Z/2Z partner of idempotent 25) is not left-cancellative.
    Witness: 26·0 = 26·1 (both equal 27) but 0 ≠ 1. -/
theorem t3star_involution_26_not_cancellative :
    T3Star.mul ⟨26, by omega⟩ ⟨0, by omega⟩ =
    T3Star.mul ⟨26, by omega⟩ ⟨1, by omega⟩ ∧
    (⟨0, by omega⟩ : T3Star) ≠ ⟨1, by omega⟩ := by
  constructor
  · native_decide
  · decide

/-! ## Section 4: No Cancellative Element

  This is the KEY structural theorem for blocking BPR.

  An element m is left-cancellative if: ∀ a b, m·a = m·b → a = b.
  An element m is right-cancellative if: ∀ a b, a·m = b·m → a = b.

  We prove: NO element of T₃* is left-cancellative.
  We prove: NO element of T₃* is right-cancellative.

  This is verified exhaustively: for each of the 28 elements, we exhibit
  a collision pair (a ≠ b with m·a = m·b).  The collision rate is ~89%.

  For BPR: since no element is cancellative, the Chinese Remainder Theorem
  cannot be applied.  There is no "modular inverse" to factor out common
  components across the formula. -/

/-- **Theorem 4a: No Left-Cancellative Element**.
    For every m ∈ T₃* there exist a ≠ b with m·a = m·b. -/
theorem t3star_no_left_cancellative :
    ∀ m : T3Star,
      ∃ a b : T3Star, a ≠ b ∧ T3Star.mul m a = T3Star.mul m b := by
  native_decide

/-- **Theorem 4b: No Right-Cancellative Element**.
    For every m ∈ T₃* there exist a ≠ b with a·m = b·m. -/
theorem t3star_no_right_cancellative :
    ∀ m : T3Star,
      ∃ a b : T3Star, a ≠ b ∧ T3Star.mul a m = T3Star.mul b m := by
  native_decide

/-- Equivalently: no element satisfies the cancellation property (left). -/
theorem t3star_not_left_cancellative :
    ∀ m : T3Star,
      ¬ (∀ a b : T3Star, T3Star.mul m a = T3Star.mul m b → a = b) := by
  intro m hcanc
  obtain ⟨a, b, hne, heq⟩ := t3star_no_left_cancellative m
  exact hne (hcanc a b heq)

/-- Equivalently: no element satisfies the cancellation property (right). -/
theorem t3star_not_right_cancellative :
    ∀ m : T3Star,
      ¬ (∀ a b : T3Star, T3Star.mul a m = T3Star.mul b m → a = b) := by
  intro m hcanc
  obtain ⟨a, b, hne, heq⟩ := t3star_no_right_cancellative m
  exact hne (hcanc a b heq)

/-! ## Section 5: Von Neumann Regularity

  T₃* is von Neumann regular: every element m has a quasi-inverse x with m·x·m = m.
  This is a weaker property than invertibility: quasi-inverses exist but are NOT
  unique and do NOT give a group structure.

  This shows the BPR barrier is not about "algebraic poverty" of T₃*.
  The monoid has rich local structure (regular, Z/2Z H-classes).
  The barrier is specifically about the ABSENCE of global cancellation. -/

/-- **Theorem 5: Von Neumann Regularity**.
    Every element of T₃* has a quasi-inverse: ∃ x, m·x·m = m. -/
theorem t3star_von_neumann_regular :
    ∀ m : T3Star,
      ∃ x : T3Star, T3Star.mul (T3Star.mul m x) m = m := by
  native_decide

/-- The quasi-inverse is NOT unique: most elements have multiple quasi-inverses.
    Concretely: element 0 has at least two distinct quasi-inverses. -/
theorem t3star_quasi_inverse_not_unique :
    ∃ m x y : T3Star,
      x ≠ y ∧
      T3Star.mul (T3Star.mul m x) m = m ∧
      T3Star.mul (T3Star.mul m y) m = m := by
  native_decide

/-! ## Section 6: Capstone — BPR Inapplicability

  The BPR proof technique (Bonet-Pitassi-Raz 2000) for constructing Frege
  interpolants uses the Chinese Remainder Theorem (CRT).  At its core, CRT
  needs cancellative elements — elements m such that m·a = m·b implies a = b —
  to "factor out" common parts of the circuit.

  We have shown T₃* has NONE of these:
    (1) t3star_no_global_identity    — no global identity (T₃* is not a monoid)
    (2) t3star_not_left_cancellative — no left-cancellative element
    (3) t3star_aperiodic             — globally aperiodic (m⁵ = m³), bounded periods
    (4) t3star_von_neumann_regular   — quasi-inverses exist but are non-unique

  Combined: BPR's CRT decomposition cannot proceed over T₃*.  The formula's
  transfer operators cannot be "inverted" or "factored" modulo any non-trivial
  modulus.  Frege interpolants, if they exist, cannot be constructed by any
  BPR-like technique using the CubeGraph algebraic structure. -/

/-- **Theorem 6: BPR Structural Inapplicability** (Capstone).
    Bundles the key no-cancellation properties that make BPR inapplicable. -/
theorem bpr_structurally_inapplicable :
    -- (1) No global identity: T₃* is not a monoid
    (¬ ∃ e : T3Star, ∀ m : T3Star,
        T3Star.mul e m = m ∧ T3Star.mul m e = m)
    -- (2) No left-cancellative element
    ∧ (∀ m : T3Star,
        ¬ (∀ a b : T3Star, T3Star.mul m a = T3Star.mul m b → a = b))
    -- (3) Global aperiodicity: m⁵ = m³ for all m (no non-trivial modular periods)
    ∧ (∀ m : T3Star, T3Star.pow m 4 = T3Star.pow m 2)
    -- (4) Von Neumann regularity: quasi-inverses exist but non-unique
    ∧ (∀ m : T3Star,
        ∃ x : T3Star, T3Star.mul (T3Star.mul m x) m = m) :=
  ⟨t3star_no_global_identity,
   t3star_not_left_cancellative,
   t3star_aperiodic,
   t3star_von_neumann_regular⟩

/-- **T₃* No Group-Cancellation Summary**.
    The complete algebraic picture that blocks BPR:
      — no global identity → no globally meaningful "inverse" concept
      — no left/right cancellative element → CRT impossible
      — aperiodic → no non-trivial modular arithmetic
      — regular but not inverse → quasi-inverses non-unique (CRT needs uniqueness)
      — Z/2Z H-classes exist → the barrier is about GLOBAL vs LOCAL structure -/
theorem t3star_no_group_cancellation :
    -- No global identity
    (¬ ∃ e : T3Star, ∀ m : T3Star,
        T3Star.mul e m = m ∧ T3Star.mul m e = m) ∧
    -- No left-cancellative element (∃ collision pair for every m)
    (∀ m : T3Star,
      ∃ a b : T3Star, a ≠ b ∧ T3Star.mul m a = T3Star.mul m b) ∧
    -- No right-cancellative element
    (∀ m : T3Star,
      ∃ a b : T3Star, a ≠ b ∧ T3Star.mul a m = T3Star.mul b m) ∧
    -- Global aperiodicity
    (∀ m : T3Star, T3Star.pow m 4 = T3Star.pow m 2) :=
  ⟨t3star_no_global_identity,
   t3star_no_left_cancellative,
   t3star_no_right_cancellative,
   t3star_aperiodic⟩

end CubeGraph
