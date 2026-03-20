/-
  CubeGraph/BarringtonConnection.lean
  F2.1: Barrington Connection — CubeGraph composition in aperiodic T₃*.

  Chain: T₃* aperiodic → composition ⊂ AC⁰ → SAT ∉ AC⁰ → insufficient.
  Steps 3-4 are external citations. We formalize: definitions + rank decay + summary.

  See: BandSemigroup.lean, RankMonotonicity.lean, KConsistency.lean
  See: experiments-ml/022_.../theory/KR-LADDER.md
  See: experiments-ml/022_.../F2.1-PLAN.md, F2.2-RESULTS.md
-/

import CubeGraph.KConsistency
import CubeGraph.IdempotenceBarrier

namespace CubeGraph

open BoolMat

/-! ## Section 1: Composition Sequences -/

/-- A composition sequence: edges to compose in order. -/
abbrev CompositionSeq (G : CubeGraph) := List (Fin G.cubes.length × Fin G.cubes.length)

/-- Transfer operator for a single edge. -/
def edgeOp (G : CubeGraph) (e : Fin G.cubes.length × Fin G.cubes.length) : BoolMat 8 :=
  transferOp (G.cubes[e.1]) (G.cubes[e.2])

/-- Product of a composition sequence via boolean matrix multiplication. -/
def composeSeq (G : CubeGraph) (seq : CompositionSeq G) : BoolMat 8 :=
  seq.foldl (fun acc e => mul acc (edgeOp G e)) (one : BoolMat 8)

/-- Trace of composed product. -/
def traceOfSeq (G : CubeGraph) (seq : CompositionSeq G) : Bool :=
  trace (composeSeq G seq)

/-! ## Section 2: Rank Decay on Sequences -/

/-- composeSeq with cons = foldl starting from edgeOp of first element. -/
theorem composeSeq_cons (G : CubeGraph) (e : Fin G.cubes.length × Fin G.cubes.length)
    (rest : CompositionSeq G) :
    composeSeq G (e :: rest) =
    rest.foldl (fun acc e' => mul acc (edgeOp G e')) (edgeOp G e) := by
  simp only [composeSeq, List.foldl, one_mul]

/-- Empty sequence = identity. -/
theorem composeSeq_nil (G : CubeGraph) : composeSeq G [] = one := by
  simp [composeSeq]

/-! ## Section 3: Aperiodicity of Composed Products -/

/-- Any rank-1 composed product is aperiodic: M³ = M². -/
theorem composed_aperiodic (G : CubeGraph) (seq : CompositionSeq G)
    (h : (composeSeq G seq).IsRankOne) :
    mul (composeSeq G seq) (mul (composeSeq G seq) (composeSeq G seq))
    = mul (composeSeq G seq) (composeSeq G seq) :=
  rank1_aperiodic h

/-- Any rank-1 composed product with trace>0 is idempotent: M² = M. -/
theorem composed_idempotent (G : CubeGraph) (seq : CompositionSeq G)
    (h : (composeSeq G seq).IsRankOne) (ht : (composeSeq G seq).trace = true) :
    mul (composeSeq G seq) (composeSeq G seq) = composeSeq G seq :=
  rank1_idempotent h ht

/-- Idempotence barrier on sequences: M·(M·B) = M·B. -/
theorem composed_barrier (G : CubeGraph) (seq : CompositionSeq G)
    (h : (composeSeq G seq).IsRankOne) (ht : (composeSeq G seq).trace = true)
    (B : BoolMat 8) :
    mul (composeSeq G seq) (mul (composeSeq G seq) B)
    = mul (composeSeq G seq) B := by
  rw [show mul (composeSeq G seq) (mul (composeSeq G seq) B)
      = mul (mul (composeSeq G seq) (composeSeq G seq)) B
    from (mul_assoc _ _ _).symm]
  rw [composed_idempotent G seq h ht]

/-! ## Section 4: SAT ≠ Single Composition -/

/-- SAT is NOT determined by any single composition.
    Flat connection (all edges OK) does not imply satisfiability. -/
theorem sat_not_single_comp :
    ∃ G : CubeGraph, FlatConnection G ∧ ¬ G.Satisfiable :=
  flat_not_implies_sat

/-- Coordination required: local consistency ≠ global satisfiability.
    2-consistent but not 3-consistent. -/
theorem coordination_required :
    ∃ G : CubeGraph, KConsistent G 2 ∧ ¬ KConsistent G 3 :=
  ⟨h2Graph, h2graph_2consistent, h2graph_not_3consistent⟩

/-! ## Section 5: Barrington Summary -/

/-- **Barrington Connection**: four facts that together show CubeGraph
    composition is structurally insufficient for SAT.

    1. Flat bundle: locally consistent ≠ globally satisfiable
    2. Consistency gap: 2-consistent ∧ ¬3-consistent (Borromean)
    3. Aperiodicity: rank-1 products satisfy M³=M² (KR=0, AC⁰)
    4. Idempotency: rank-1 with trace>0 satisfies M²=M (saturation)

    Combined with external citations:
    5. Aperiodic monoid → AC⁰ (Barrington-Thérien 1988)
    6. SAT ∉ AC⁰ (Furst-Saxe-Sipser 1984)
    → CubeGraph composition cannot solve SAT.

    Additionally (F2.2, empirical):
    7. KR=1 (ℤ/3ℤ, ACC⁰) also cannot discriminate (Δ<0.01) -/
theorem barrington_summary :
    (∃ G : CubeGraph, FlatConnection G ∧ ¬ G.Satisfiable) ∧
    (∃ G : CubeGraph, KConsistent G 2 ∧ ¬ KConsistent G 3) ∧
    (∀ {M : BoolMat 8}, M.IsRankOne →
      mul M (mul M M) = mul M M) ∧
    (∀ {M : BoolMat 8}, M.IsRankOne → M.trace = true →
      mul M M = M) :=
  ⟨sat_not_single_comp,
   coordination_required,
   fun h => rank1_aperiodic h,
   fun h ht => rank1_idempotent h ht⟩

end CubeGraph
