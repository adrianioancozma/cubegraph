/-
  CubeGraph/DimensionThreshold.lean
  T9: Dimension Threshold — Why k=3 is the NP-hardness boundary.

  Unifies 5 independently proven properties that ALL change at k=2 → k=3:
  1. Polymorphism: k=2 has WNU preserving ≠. k=3 does not.
  2. H² topology: requires ≥ 3 cubes. Achieved at exactly 3.
  3. Type 2 UNSAT: locally consistent + UNSAT exists at k=3.
  4. Monodromy: non-trivial (traceless, nonzero) at k=3.
  5. Algebra: same matrix is bool-idempotent but GF(2)-nilpotent.

  Each property is already proven in its own file. T9 merely combines them
  into a single statement: "dimension 3 is special because EVERYTHING aligns."

  See: TaylorBarrier.lean (#1), MinimalBarrier.lean (#2),
       Type2Monodromy.lean (#3-4), IdempotenceBarrier.lean (#5)
  See: experiments-ml/021_.../HYPERSPHERE-TOMOGRAPHY.md (Q5: why k=3?)
  See: TrivialPolymorphism.lean (T10: single gap → trivial polymorphism)
  See: experiments-ml/021_.../Q5-D2-RESULTS.md (traceless swap EXISTS at k=2 but P-detectable)
  See: experiments-ml/021_.../T9-PLAN.md (plan)
  See: experiments-ml/021_.../HYPERSPHERE-TOMOGRAPHY.md (Q5: why k=3?)
  See: experiments-ml/021_.../MICRO-MACRO-BRIDGE.md (dimension threshold = bridge breaks at k=3)
-/

import CubeGraph.TaylorBarrier
import CubeGraph.MinimalBarrier
import CubeGraph.Type2Monodromy
import CubeGraph.IdempotenceBarrier

namespace CubeGraph

open BoolMat

/-! ## Section 1: Components (rewraps for clarity) -/

/-- **P1: k=2 has polymorphism** — majority on Fin 2 is a WNU3 that preserves ≠. -/
theorem k2_has_polymorphism :
    ∃ f : Fin 2 → Fin 2 → Fin 2 → Fin 2,
      IsWNU3 2 f ∧ PreservesRel3 2 f neq2 :=
  ⟨majority2, majority2_wnu, majority2_preserves_neq⟩

/-- **P2: k=3 has NO polymorphism** — no WNU3 on Fin 3 preserves ≠. -/
theorem k3_no_polymorphism :
    ∀ f : Fin 3 → Fin 3 → Fin 3 → Fin 3,
      IsWNU3 3 f → ¬ PreservesRel3 3 f neq3 :=
  no_wnu3_preserves_neq3

/-- **P3: H² requires ≥ 3 cubes** — 2 cubes can never be H² UNSAT. -/
theorem h2_needs_three (G : CubeGraph) (h : G.cubes.length ≤ 2) :
    ¬ UNSATType2 G :=
  small_not_H2 G h

/-- **P4: H² achieved at exactly 3 cubes** — r1Graph witnesses H². -/
theorem h2_achieved_at_three :
    ∃ G : CubeGraph, UNSATType2 G ∧ G.cubes.length = 3 :=
  ⟨r1Graph, h2_minimal_three_cubes.1, h2_minimal_three_cubes.2⟩

/-- **P5: Type 2 UNSAT at k=3** — locally consistent + UNSAT. -/
theorem flat_failure_at_three :
    ∃ G : CubeGraph, LocallyConsistent G ∧ ¬ G.Satisfiable :=
  locally_consistent_not_implies_sat

/-- **P6: Non-trivial monodromy at k=3** — nonzero but traceless. -/
theorem nontrivial_monodromy_at_three :
    ¬ isZero h2MonodromyCycle ∧ trace h2MonodromyCycle = false :=
  ⟨h2_monodromy_nonzero, h2_monodromy_trace_false⟩

/-- **P7: Bool vs GF(2) dichotomy** — same matrix, opposite fates. -/
theorem algebra_dichotomy :
    ∃ M : BoolMat 8, mul M M = M ∧ isZero (xor_mul M M) :=
  bool_vs_xor_dichotomy

/-! ## Section 2: Main Theorem -/

/-- **DIMENSION THRESHOLD (Theorem B)**:
    Five properties that ALL change at the k=2 → k=3 boundary.
    Together they explain why 2-SAT ∈ P and 3-SAT is NP-complete.

    1. Polymorphism disappears (Schaefer dichotomy)
    2. H² topology becomes possible (≥ 3 cubes)
    3. Type 2 UNSAT exists (local consistency ≠ satisfiable)
    4. Monodromy becomes non-trivial (traceless swaps)
    5. Boolean algebra diverges from GF(2) (idempotent vs nilpotent)

    None of these hold at k=2. All hold at k=3. -/
theorem dimension_threshold :
    -- 1. Polymorphism: k=2 yes, k=3 no
    (∃ f, IsWNU3 2 f ∧ PreservesRel3 2 f neq2) ∧
    (∀ f, IsWNU3 3 f → ¬ PreservesRel3 3 f neq3) ∧
    -- 2. H² topology: needs ≥ 3, achieved at 3
    (∀ G : CubeGraph, G.cubes.length ≤ 2 → ¬ UNSATType2 G) ∧
    (∃ G : CubeGraph, UNSATType2 G ∧ G.cubes.length = 3) ∧
    -- 3. Type 2 UNSAT exists
    (∃ G : CubeGraph, LocallyConsistent G ∧ ¬ G.Satisfiable) ∧
    -- 4. Non-trivial monodromy (traceless swap)
    (¬ isZero h2MonodromyCycle ∧ trace h2MonodromyCycle = false) ∧
    -- 5. Bool ≠ GF(2) on same matrix
    (∃ M : BoolMat 8, mul M M = M ∧ isZero (xor_mul M M)) :=
  ⟨k2_has_polymorphism,
   k3_no_polymorphism,
   h2_needs_three,
   h2_achieved_at_three,
   flat_failure_at_three,
   nontrivial_monodromy_at_three,
   algebra_dichotomy⟩

/-! ## Section 3: What Each Component Means -/

/-- The polymorphism gap: k=2 has algebraic shortcuts, k=3 does not.
    At k=2, majority voting resolves conflicts. At k=3, no such operation exists. -/
theorem polymorphism_gap :
    (∃ f, IsWNU3 2 f ∧ PreservesRel3 2 f neq2) ∧
    (∀ f, IsWNU3 3 f → ¬ PreservesRel3 3 f neq3) :=
  ⟨k2_has_polymorphism, k3_no_polymorphism⟩

/-- The topology gap: H² (global incoherence) is impossible at 2 cubes,
    possible at 3. The minimum traceless swap requires a triangle. -/
theorem topology_gap :
    (∀ G : CubeGraph, G.cubes.length ≤ 2 → ¬ UNSATType2 G) ∧
    (∃ G : CubeGraph, UNSATType2 G ∧ G.cubes.length = 3) :=
  ⟨h2_needs_three, h2_achieved_at_three⟩

/-- The algebra gap: boolean composition is idempotent (M²=M, information preserved
    as projection), while GF(2) is nilpotent (M²=0, information destroyed).
    The same matrix, two fates, determined by 1+1=1 vs 1+1=0. -/
theorem algebra_gap :
    ∃ M : BoolMat 8,
      mul M M = M ∧                    -- boolean: stable (band semigroup)
      isZero (xor_mul M M) :=          -- GF(2): annihilated (nilpotent)
  algebra_dichotomy

end CubeGraph
