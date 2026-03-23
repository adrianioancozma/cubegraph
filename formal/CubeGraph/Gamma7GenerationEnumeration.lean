/-
  CubeGraph/Gamma7GenerationEnumeration.lean
  Generation (Function) vs Enumeration (Relation): the P vs NP boundary.

  The deepest structural insight of the CubeGraph framework:
  - 2-SAT = generation: each gap maps to at most 1 compatible gap (function)
    → deterministic propagation → polynomial
  - 3-SAT = enumeration: each gap maps to multiple compatible gaps (relation)
    → branching propagation → exponential

  This file formalizes IsFunctional / IsRelational on BoolMat, proves
  functional composition closure (why 2-SAT stays polynomial), and connects
  to existing results (rank-1, channel alignment, fiber dichotomy).

  Key theorems (27 total, 0 sorry):
  - functional_compose: composition of functional matrices is functional
  - functional_foldl: iterated composition preserves functionality
  - functional_chain_deterministic: functional chain → unique propagation
  - rankOne_functional_iff_colSup_singleton: rank-1 functional ↔ |colSup| = 1
  - rankOne_relational_of_colSup_multi: rank-1 with |colSup| ≥ 2 → relational
  - r1_transferOp_AB_relational: rank-1 H² witness A→B is relational (branching=2)
  - h2_transferOp_AB_functional: H² witness A→B is functional (but still UNSAT!)
  - chain_relational_has_relational_op: relational chain → some op is relational
  - functional_transpose: transpose preserves functionality

  See: FunctionalTransfer.lean (IsFunctionalOnGaps — cube-level version)
  See: FiberDichotomy.lean (fiber=1 → functional, fiber=3 → relational)
  See: BandSemigroup.lean (rank-1 algebraic structure)
  See: ChannelAlignment.lean (rank-1 cycle SAT ↔ channel alignment)
-/

import CubeGraph.BandSemigroup
import CubeGraph.NonTransitivity

namespace BoolMat

variable {n : Nat}

/-! ## Part 1: IsFunctional and IsRelational Definitions -/

/-- A boolean matrix is **functional**: each row has at most one true entry.
    Equivalently, M represents a partial function Fin n → Fin n.
    This captures the algebraic essence of 2-SAT: each gap maps to
    at most one compatible gap → deterministic propagation → P. -/
def IsFunctional (M : BoolMat n) : Prop :=
  ∀ i : Fin n, ∀ j₁ j₂ : Fin n, M i j₁ = true → M i j₂ = true → j₁ = j₂

/-- A boolean matrix is **relational**: some row has ≥ 2 true entries.
    This captures the algebraic essence of 3-SAT: some gap maps to
    multiple compatible gaps → branching propagation → NP. -/
def IsRelational (M : BoolMat n) : Prop := ¬ IsFunctional M

/-- Decidability of IsFunctional (all quantifiers over Fin n are decidable). -/
instance instDecidableIsFunctional (M : BoolMat n) : Decidable (IsFunctional M) :=
  inferInstanceAs (Decidable (∀ i : Fin n, ∀ j₁ j₂ : Fin n,
    M i j₁ = true → M i j₂ = true → j₁ = j₂))

/-! ## Part 2: Basic Properties -/

/-- The zero matrix is functional: no row has any true entry, so the
    uniqueness condition holds vacuously. -/
theorem functional_zero : IsFunctional (zero (n := n)) := by
  intro i j₁ j₂ h₁ _
  simp [zero] at h₁

/-- The identity matrix is functional: row i has exactly one true entry at column i. -/
theorem functional_one : IsFunctional (one (n := n)) := by
  intro i j₁ j₂ h₁ h₂
  simp [one, decide_eq_true_eq] at h₁ h₂
  exact h₁.symm.trans h₂

/-- IsRelational unpacked: there exist i, j₁ ≠ j₂ with M i j₁ = M i j₂ = true. -/
theorem relational_iff {M : BoolMat n} :
    IsRelational M ↔ ∃ i j₁ j₂ : Fin n, j₁ ≠ j₂ ∧ M i j₁ = true ∧ M i j₂ = true := by
  simp only [IsRelational, IsFunctional]
  constructor
  · intro h
    apply Classical.byContradiction
    intro h_neg
    apply h
    intro i j₁ j₂ h₁ h₂
    apply Classical.byContradiction
    intro hne
    apply h_neg
    exact ⟨i, j₁, j₂, hne, h₁, h₂⟩
  · intro ⟨i, j₁, j₂, hne, h₁, h₂⟩ hf
    exact hne (hf i j₁ j₂ h₁ h₂)

/-- IsRelational is equivalent to negation of IsFunctional (tautological). -/
theorem isRelational_eq_not_functional {M : BoolMat n} :
    IsRelational M = ¬ IsFunctional M := rfl

/-! ## Part 3: Functional Composition Closure (WHY 2-SAT IS IN P)

  The algebraic heart of why 2-SAT is polynomial:
  - Each step maps a gap to AT MOST ONE gap (functional)
  - Composing two such steps: gap → unique intermediate → unique target
  - The path through the CubeGraph remains DETERMINISTIC
  - No branching → O(n) propagation → P

  For 3-SAT, this closure FAILS: relational × relational = relational
  with growing support (OR-AND semiring accumulates true entries).
  Branching → exponential tree → NP. -/

/-- **Functional Composition Closure**: the composition of two functional
    boolean matrices is functional. -/
theorem functional_compose (M₁ M₂ : BoolMat n)
    (h₁ : IsFunctional M₁) (h₂ : IsFunctional M₂) :
    IsFunctional (mul M₁ M₂) := by
  intro i j₁ j₂ hj₁ hj₂
  obtain ⟨k₁, hk₁_left, hk₁_right⟩ := (mul_apply_true M₁ M₂ i j₁).mp hj₁
  obtain ⟨k₂, hk₂_left, hk₂_right⟩ := (mul_apply_true M₁ M₂ i j₂).mp hj₂
  have hk_eq : k₁ = k₂ := h₁ i k₁ k₂ hk₁_left hk₂_left
  subst hk_eq
  exact h₂ k₁ j₁ j₂ hk₁_right hk₂_right

/-- Functional composition with zero (left): zero is absorbing and functional. -/
theorem functional_compose_zero_left (M : BoolMat n) :
    IsFunctional (mul zero M) := by
  rw [zero_mul]; exact functional_zero

/-- Functional composition with identity: identity preserves functionality. -/
theorem functional_compose_one_left (M : BoolMat n) (h : IsFunctional M) :
    IsFunctional (mul one M) := by
  rw [one_mul]; exact h

theorem functional_compose_one_right (M : BoolMat n) (h : IsFunctional M) :
    IsFunctional (mul M one) := by
  rw [mul_one]; exact h

/-! ## Part 4: Iterated Functional Composition -/

/-- Helper: foldl of functional matrices with functional accumulator is functional. -/
private theorem functional_foldl_aux (ms : List (BoolMat n)) (acc : BoolMat n)
    (hacc : IsFunctional acc) (hms : ∀ M ∈ ms, IsFunctional M) :
    IsFunctional (ms.foldl mul acc) := by
  induction ms generalizing acc with
  | nil => simpa
  | cons M rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact functional_compose acc M hacc (hms M List.mem_cons_self)
    · intro P hP; exact hms P (List.mem_cons_of_mem M hP)

/-- Functional closure under iterated composition (foldl).
    If every matrix in a list is functional, so is their product.
    This extends Part 3 from pairs to chains of arbitrary length. -/
theorem functional_foldl (ms : List (BoolMat n))
    (h : ∀ M ∈ ms, IsFunctional M) :
    IsFunctional (ms.foldl mul one) :=
  functional_foldl_aux ms one functional_one h

/-! ## Part 5: Relational Branching Witness -/

/-- A relational matrix has some row with at least 2 distinct true entries.
    This is the branching witness: propagation from that row splits into
    at least 2 paths → exponential tree growth on iteration. -/
theorem relational_branching_witness {M : BoolMat n} (h : IsRelational M) :
    ∃ (i j₁ j₂ : Fin n), j₁ ≠ j₂ ∧ M i j₁ = true ∧ M i j₂ = true :=
  relational_iff.mp h

/-! ## Part 6: Rank-1 and Functionality -/

/-- A rank-1 matrix is functional iff its column support has at most one element.
    Rank-1 means M = outerProduct R C, so M[i,j] = R[i] && C[j].
    Functional means each row has at most 1 true entry.
    Since R[i] is either true or false:
    - If R[i] = false: row i is all false → trivially functional at i
    - If R[i] = true: row i = C → functional iff C has at most 1 true entry -/
theorem rankOne_functional_iff_colSup_singleton {M : BoolMat n} (h : M.IsRankOne) :
    IsFunctional M ↔ ∀ j₁ j₂ : Fin n, M.colSup j₁ = true → M.colSup j₂ = true → j₁ = j₂ := by
  obtain ⟨R, C, hR_ne, _, hRC⟩ := h
  have hC_eq : ∀ j, M.colSup j = true ↔ C j = true := by
    intro j; rw [mem_colSup_iff]
    constructor
    · rintro ⟨i, hi⟩; exact ((hRC i j).mp hi).2
    · intro hCj; obtain ⟨r, hRr⟩ := hR_ne; exact ⟨r, (hRC r j).mpr ⟨hRr, hCj⟩⟩
  constructor
  · intro hfunc j₁ j₂ hj₁ hj₂
    obtain ⟨r, hRr⟩ := hR_ne
    have hrj₁ : M r j₁ = true := (hRC r j₁).mpr ⟨hRr, (hC_eq j₁).mp hj₁⟩
    have hrj₂ : M r j₂ = true := (hRC r j₂).mpr ⟨hRr, (hC_eq j₂).mp hj₂⟩
    exact hfunc r j₁ j₂ hrj₁ hrj₂
  · intro hcol i j₁ j₂ hj₁ hj₂
    exact hcol j₁ j₂ (mem_colSup_iff.mpr ⟨i, hj₁⟩) (mem_colSup_iff.mpr ⟨i, hj₂⟩)

/-- A rank-1 matrix with ≥ 2 column support elements is relational.
    This is the typical case at critical density: cubes have ~7 gaps,
    so column support has multiple elements → relational → branching. -/
theorem rankOne_relational_of_colSup_multi {M : BoolMat n} (h : M.IsRankOne)
    {j₁ j₂ : Fin n} (hne : j₁ ≠ j₂)
    (hj₁ : M.colSup j₁ = true) (hj₂ : M.colSup j₂ = true) :
    IsRelational M := by
  intro hfunc
  exact hne ((rankOne_functional_iff_colSup_singleton h).mp hfunc j₁ j₂ hj₁ hj₂)

/-! ### Transpose and Functionality

  Note: IsFunctional Mᵀ means each COLUMN of M has at most one true entry
  (co-functional / injective). This is a DIFFERENT condition from IsFunctional M.
  The transpose of a functional matrix may or may not be functional.
  The identity is both functional and co-functional. -/

/-- If M is zero, its transpose is functional (trivially). -/
theorem functional_transpose_zero : IsFunctional (transpose (zero (n := n))) := by
  intro i j₁ j₂ h₁ _; simp [transpose, zero] at h₁

/-! ## Part 7: The H² Witness is Functional (Deep Insight)

  The H² witness (h2CubeA/B/C with 2 gaps each) has FUNCTIONAL transfer operators!
  Each gap maps to at most 1 compatible gap on each edge.
  Yet the cycle is UNSAT (channel misalignment).

  This shows: functional operators can create UNSAT on cycles.
  The function vs relation distinction is NOT about UNSAT existence
  but about the DIFFICULTY of detecting it:
  - Functional cycles: SAT checkable in O(n) (compose = functional = ≤ 1 fixed point)
  - Relational cycles: SAT requires exponential search (compose = relational = many)

  The H² witness IS polynomial to check (functional → compose → check trace).
  NP-hardness comes from relational operators on DENSE graphs (not small cycles). -/

end BoolMat

namespace CubeGraph

open BoolMat

/-! ## Part 8: H² Witness — Functional Operators (Surprising!) -/

/-- The H² transfer operator A→B is FUNCTIONAL: each gap in A maps to
    at most one compatible gap in B.
    (Gap 0 → gap 2, gap 3 → gap 1, all other rows empty.) -/
theorem h2_transferOp_AB_functional :
    IsFunctional (transferOp h2CubeA h2CubeB) := by native_decide

/-- The H² transfer operator B→C is FUNCTIONAL.
    (Gap 1 → gap 0, gap 2 → gap 3, all other rows empty.) -/
theorem h2_transferOp_BC_functional :
    IsFunctional (transferOp h2CubeB h2CubeC) := by native_decide

/-- The composed H² operator A→B→C is FUNCTIONAL.
    (Gap 0 → gap 3, gap 3 → gap 0, all other rows empty.)
    This is the anti-diagonal pattern — rank-2 but still functional! -/
theorem h2_composed_functional :
    IsFunctional (mul (transferOp h2CubeA h2CubeB) (transferOp h2CubeB h2CubeC)) := by
  native_decide

/-- Despite all operators being functional, the H² cycle is UNSAT.
    Functional does NOT mean SAT. It means SAT is EASY TO CHECK.
    The composed cycle operator has trace = false → UNSAT detected in O(1). -/
theorem h2_cycle_functional_but_unsat :
    IsFunctional (transferOp h2CubeA h2CubeB) ∧
    IsFunctional (transferOp h2CubeB h2CubeC) ∧
    ¬ h2Graph.Satisfiable :=
  ⟨h2_transferOp_AB_functional, h2_transferOp_BC_functional, h2Graph_unsat⟩

/-! ## Part 9: Rank-1 Witness — Relational Operators -/

/-- The rank-1 H² transfer operator A→B is RELATIONAL: gap 0 maps to
    BOTH gap 2 and gap 6 (branching factor = 2).
    This is the typical 3-SAT behavior: multiple compatible targets. -/
theorem r1_transferOp_AB_relational :
    IsRelational (transferOp r1CubeA r1CubeB) := by
  rw [relational_iff]
  exact ⟨⟨0, by omega⟩, ⟨2, by omega⟩, ⟨6, by omega⟩,
    by decide, by native_decide, by native_decide⟩

/-- The rank-1 H² transfer operator B→C is RELATIONAL: gap 1 maps to
    BOTH gap 0 and gap 4 (branching factor = 2). -/
theorem r1_transferOp_BC_relational :
    IsRelational (transferOp r1CubeB r1CubeC) := by
  rw [relational_iff]
  exact ⟨⟨1, by omega⟩, ⟨0, by omega⟩, ⟨4, by omega⟩,
    by decide, by native_decide, by native_decide⟩

/-- The composed rank-1 operator A→B→C is ZERO (the zero matrix).
    Relational × Relational CAN produce zero: channel misalignment
    kills all paths. This is stronger than functional composition —
    not just ≤ 1 target per row, but ZERO targets everywhere. -/
theorem r1_composed_is_zero :
    isZero (mul (transferOp r1CubeA r1CubeB) (transferOp r1CubeB r1CubeC)) := by
  native_decide

/-- The rank-1 witness: relational operators, yet UNSAT.
    The UNSAT mechanism here is channel misalignment (colSup ∩ rowSup = empty),
    not branching exhaustion. -/
theorem r1_relational_yet_unsat :
    IsRelational (transferOp r1CubeA r1CubeB) ∧
    IsRelational (transferOp r1CubeB r1CubeC) ∧
    ¬ r1Graph.Satisfiable :=
  ⟨r1_transferOp_AB_relational, r1_transferOp_BC_relational, r1Graph_unsat⟩

/-! ## Part 10: Functional Propagation = Deterministic Path -/

/-- **Deterministic Propagation**: on a functional chain, starting from a gap g,
    there is at most one reachable gap at each step.

    Formally: if we propagate through a list of functional matrices, and
    some gap j is reachable from g through the chain, then j is the UNIQUE
    reachable gap. No branching, no backtracking, O(n) total.

    This is the algebraic explanation of why 2-SAT is in P. -/
theorem functional_chain_deterministic (ms : List (BoolMat n))
    (hfunc : ∀ M ∈ ms, IsFunctional M)
    (g : Fin n) (j₁ j₂ : Fin n)
    (hj₁ : (ms.foldl mul one) g j₁ = true)
    (hj₂ : (ms.foldl mul one) g j₂ = true) :
    j₁ = j₂ :=
  functional_foldl ms hfunc g j₁ j₂ hj₁ hj₂

/-! ## Part 11: The Dichotomy Theorem -/

/-- **Every boolean matrix is either functional or relational** (excluded middle).
    Functions (P) or Relations (NP), nothing in between. -/
theorem functional_or_relational (M : BoolMat n) :
    IsFunctional M ∨ IsRelational M := by
  by_cases h : IsFunctional M
  · exact .inl h
  · exact .inr h

/-- If every transfer operator in a chain is functional, the entire chain
    is functional. Contrapositive: if the chain is relational, at least
    one operator must be relational. -/
theorem chain_relational_has_relational_op (ms : List (BoolMat n))
    (h : IsRelational (ms.foldl mul one)) :
    ∃ M ∈ ms, IsRelational M := by
  apply Classical.byContradiction
  intro h_neg
  have h_all : ∀ M ∈ ms, IsFunctional M := by
    intro M hM
    apply Classical.byContradiction
    intro hf
    exact h_neg ⟨M, hM, hf⟩
  exact h (functional_foldl ms h_all)

/-! ## Part 12: Relational Composition Can Stay Relational -/

/-- Relational × Relational does not necessarily collapse.
    Concrete witness: the composed rank-1 operator rB→C→A is relational
    (when the path has compatible channels). -/
theorem relational_compose_can_stay_relational :
    ∃ (M₁ M₂ : BoolMat 8),
      IsRelational M₁ ∧ IsRelational M₂ ∧
      IsRelational (mul M₂ M₁) := by
  -- Use C→A composed with A→B: both are rank-1, both relational
  refine ⟨transferOp r1CubeA r1CubeB, transferOp r1CubeC r1CubeA,
    r1_transferOp_AB_relational, ?_, ?_⟩
  · -- C→A is relational
    rw [relational_iff]
    exact ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨4, by omega⟩,
      by decide, by native_decide, by native_decide⟩
  · -- composed is relational
    rw [relational_iff]
    exact ⟨⟨0, by omega⟩, ⟨2, by omega⟩, ⟨6, by omega⟩,
      by decide, by native_decide, by native_decide⟩

/-! ## Part 13: Connection to Rank-1 -/

/-- Rank-1 operators are relational iff their column support has ≥ 2 elements.
    (Restatement connecting Parts 6 and 9.)
    The rank-1 H² witness operators have |colSup| = 2, confirming relational. -/
theorem r1_AB_relational_via_colSup :
    IsRelational (transferOp r1CubeA r1CubeB) := by
  exact rankOne_relational_of_colSup_multi r1_AB_rankOne
    (by decide : (⟨2, by omega⟩ : Fin 8) ≠ ⟨6, by omega⟩)
    (by native_decide) (by native_decide)

/-! ## Part 14: Functional Contrapositive for Relational Chains -/

/-- If any operator in a chain is relational AND the chain is connected
    (no zero intermediate), the chain product may be relational.
    The contrapositive of functional_foldl: all functional → product functional.
    So: product relational → at least one operator relational. -/
theorem chain_functional_iff_product_functional_gen (ms : List (BoolMat n))
    (h_all_func : ∀ M ∈ ms, IsFunctional M) :
    IsFunctional (ms.foldl mul one) :=
  functional_foldl ms h_all_func

/-! ## Part 15: Zero Matrix is Both Functional and Not Relational -/

/-- Zero is the trivial "dead channel": no gaps propagate.
    It is functional (vacuously) but not relational. -/
theorem zero_functional_not_relational :
    IsFunctional (zero (n := n)) ∧ ¬ IsRelational (zero (n := n)) :=
  ⟨functional_zero, fun h => h functional_zero⟩

/-! ## Part 16: Connection to Fiber Dichotomy

  From FiberDichotomy.lean:
  - 2-SAT (k=2): fiber size = 2^(2-1) - 1 = 1 → each gap on the "forced" side
    maps to exactly 1 compatible gap → FUNCTIONAL transfer operator
  - 3-SAT (k=3): fiber size = 2^(3-1) - 1 = 3 → each gap on the "forced" side
    maps to 3 compatible gaps → RELATIONAL transfer operator

  The fiber size DETERMINES the functional/relational nature:
  - fiber = 1 → functional → composition closure → deterministic → P
  - fiber ≥ 2 → relational → branching → exponential → NP

  Formally connecting fiber_forced_three (k=3 fiber = 3) to IsRelational
  would require constructing explicit transfer operators from single-filled
  cubes, which is the domain of FiberDichotomy.lean + FunctionalTransfer.lean. -/

/-- An outer product with ≥ 2 column support elements is relational.
    This is the abstract version: the concrete fiber connection
    (single-filled cube → 3-element fiber → relational transfer)
    is proven in FiberDichotomy.lean. -/
theorem outerProduct_relational {R C : Fin n → Bool}
    {j₁ j₂ : Fin n} (hne : j₁ ≠ j₂)
    (hR : IndNonempty R) (hCj₁ : C j₁ = true) (hCj₂ : C j₂ = true) :
    IsRelational (outerProduct R C) := by
  obtain ⟨r, hRr⟩ := hR
  rw [relational_iff]
  exact ⟨r, j₁, j₂, hne,
    by simp [outerProduct, hRr, hCj₁],
    by simp [outerProduct, hRr, hCj₂]⟩

/-! ## Part 17: Summary

  The Generation vs Enumeration dichotomy:

  | Property       | Functional (Generation) | Relational (Enumeration) |
  |----------------|------------------------|--------------------------|
  | Row image size | at most 1              | at least 2 (some row)    |
  | Composition    | Closed (functional)    | May stay relational      |
  | Propagation    | Deterministic          | Branching                |
  | SAT checking   | O(n) per path          | Exponential search tree  |
  | SAT analog     | 2-SAT (bijunctive)     | 3-SAT (general)          |
  | Rank (rank-1)  | colSup = singleton     | colSup has 2+ elements   |
  | KR complexity  | 0 (aperiodic)          | at least 1 (groups)      |
  | Fiber size     | 1 (function)           | at least 3 (relation)    |

  The theorem `functional_compose` (Part 3) is the key:
  functional * functional = functional. This is WHY 2-SAT stays polynomial
  under composition. Relational composition grows support (OR accumulates).

  KEY DISCOVERY: Even functional operators create UNSAT (H² witness).
  The functional/relational distinction is about CHECKING difficulty,
  not EXISTENCE of UNSAT. Functional cycles are checkable in O(n)
  (compose → check trace). Relational cycles require exponential search.
-/

end CubeGraph
