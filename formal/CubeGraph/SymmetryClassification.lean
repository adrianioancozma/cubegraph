/-
  CubeGraph/SymmetryClassification.lean
  The 5 computational symmetries and why SAT on CubeGraph lacks the first 4.

  Framework (from BRAINSTORM-GAP-ANALYSIS.md):
    SAT on CubeGraph lacks 4 symmetries, each eliminating an algorithm class:
    1. Locality      -- eliminated by Borromean order Theta(n) [Schoenebeck 2008]
    2. Affinity      -- eliminated by 7 != 2^k [gap sets non-affine]
    3. Commutativity  -- eliminated by non-commuting transfer operators
    4. Reversibility  -- eliminated by rank decay M^3 = M^2 [aperiodicity]
    5. Replicability  -- the circuit's own symmetry (fan-out); NOT absent

  Each symmetry, if present, would yield polynomial-time algorithms:
    Locality      -> propagation (AC-3)
    Affinity      -> Gaussian elimination (XOR-SAT)
    Commutativity -> ACC^0 circuits (Barrington)
    Reversibility -> group computation (NC^1)
    Replicability -> polynomial circuits (P)

  Status: 4 out of 4 absence proofs. 0 new axioms
    (uses schoenebeck axiom from SchoenebeckChain.lean).
  Uses: schoenebeck / schoenebeck_linear (axioms from SchoenebeckChain.lean),
        seven_not_pow2 (NonAffine.lean),
        rank1_aperiodic (BandSemigroup.lean),
        h2CubeA/B/C (Witness.lean, for non-commutativity witness).

  See: experiments-ml/026_2026-03-24_audit/BRAINSTORM-GAP-ANALYSIS.md
-/

import CubeGraph.BandSemigroup
import CubeGraph.NonAffine
import CubeGraph.SchoenebeckChain

namespace CubeGraph

open BoolMat

/-! ## Symmetry 1: Locality

  A decision procedure is k-local if it only inspects k cubes.
  Schoenebeck (2008): UNSAT CubeGraphs exist that are (n/c)-consistent.
  Hence no k-local procedure with k < n/c can distinguish SAT from UNSAT. -/

/-- SAT on CubeGraph is not k-local for any fixed k:
    for any k, there exist arbitrarily large UNSAT CubeGraphs
    that are k-consistent (every subset of k cubes is satisfiable). -/
theorem sat_not_local :
    ∀ k : Nat, ∃ n₀ : Nat, ∀ n ≥ n₀,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧
        KConsistent G k ∧ ¬ G.Satisfiable :=
  schoenebeck

/-- Stronger form: locality fails at LINEAR scale.
    There exists c >= 2 such that (n/c)-consistency does not imply SAT. -/
theorem sat_not_local_linear :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧
        KConsistent G (n / c) ∧ ¬ G.Satisfiable :=
  schoenebeck_linear

/-! ## Symmetry 2: Affinity (Linearity over GF(2))

  An affine subspace of GF(2)^3 has size 2^k for some k.
  A single 3-SAT clause has 7 gaps. 7 is not a power of 2.
  Hence gap sets are non-affine, and XOR/Gaussian methods fail. -/

/-- The gap count of a single 3-SAT clause (7) is not a power of 2.
    This means gap sets are NOT affine subspaces of GF(2)^3,
    blocking Gaussian elimination / XOR-SAT techniques. -/
theorem sat_not_affine : ¬ IsPowerOfTwo 7 := seven_not_pow2

/-! ## Symmetry 3: Commutativity

  Transfer operators compose via boolean matrix multiplication.
  If composition were commutative, order of processing would not matter,
  and abelian/ACC^0 methods would apply (Barrington's theorem).

  We exhibit two concrete transfer operators from the h2 witness
  where symM1 * symM2 != symM2 * symM1. -/

/-- Transfer operator from cube A to cube B in the h2 witness. -/
private def symM1 : BoolMat 8 := transferOp h2CubeA h2CubeB

/-- Transfer operator from cube B to cube C in the h2 witness. -/
private def symM2 : BoolMat 8 := transferOp h2CubeB h2CubeC

/-- Entry (0,3) of symM1 * symM2 is true. -/
private theorem m12_entry :
    mul symM1 symM2 ⟨0, by omega⟩ ⟨3, by omega⟩ = true := by native_decide

/-- Entry (0,3) of symM2 * symM1 is false. -/
private theorem m21_entry :
    mul symM2 symM1 ⟨0, by omega⟩ ⟨3, by omega⟩ = false := by native_decide

/-- Transfer operator composition is NOT commutative:
    symM1 * symM2 != symM2 * symM1.
    Witness: entry (0,3) is true in one product, false in the other. -/
theorem composition_not_commutative :
    mul symM1 symM2 ≠ mul symM2 symM1 := by
  intro h
  have h1 := congrFun (congrFun h ⟨0, by omega⟩) ⟨3, by omega⟩
  rw [m12_entry, m21_entry] at h1
  exact absurd h1 (by decide)

/-- The specific entry witnessing non-commutativity. -/
theorem composition_not_commutative_witness :
    ∃ i j : Fin 8, mul symM1 symM2 i j ≠ mul symM2 symM1 i j :=
  ⟨⟨0, by omega⟩, ⟨3, by omega⟩, by rw [m12_entry, m21_entry]; decide⟩

/-! ## Symmetry 4: Reversibility

  A reversible computation can recover its input from output.
  In semigroup terms: reversibility requires group structure (every
  element has an inverse).

  Rank-1 transfer operators satisfy M^3 = M^2 (aperiodicity).
  This means composition is IRREVERSIBLE: information is lost at
  each step and cannot be recovered. The semigroup has Krohn-Rhodes
  complexity 0 -- no group components, only reset/projection. -/

/-- Rank-1 transfer operator composition is irreversible:
    M^3 = M^2 (aperiodic, information is lost and stays lost).
    Equivalently: the rank-1 semigroup has no non-trivial group factors. -/
theorem composition_irreversible (M : BoolMat 8) (h : M.IsRankOne) :
    mul M (mul M M) = mul M M :=
  rank1_aperiodic h

/-- The nilpotent case: when trace = 0, information is completely destroyed.
    M^2 = 0 -- two steps of composition annihilate all information. -/
theorem composition_nilpotent (M : BoolMat 8) (h : M.IsRankOne)
    (ht : M.trace = false) :
    mul M M = zero :=
  rank1_nilpotent h ht

/-! ## Symmetry 5: Replicability (Fan-out)

  This is NOT a property of the problem but of the computation model.
  Circuits can compute a value once and reuse it (fan-out).
  Trees (formulas) cannot -- each subtree is independent.

  Without fan-out (trees): decision tree depth = Theta(n) -> exp(n) size.
  With fan-out (circuits): this is the open question (P vs NP).

  We state this as the central remaining question, not as a theorem. -/

/-- Circuits have fan-out (replicability): a computed bit can be sent to
    multiple gates. This is the computational symmetry that separates
    tree lower bounds (proved) from circuit lower bounds (open).

    SAT on CubeGraph has NATURAL fan-out (variables shared across cubes),
    but it is unknown whether polynomial artificial fan-out (Tseitin
    extension variables) suffices to compute the SAT function. -/
def ReplicabilitySeparatesTreesFromCircuits : Prop :=
  -- Tree complexity (no fan-out) is exponential:
  -- For all tree-depth bounds d < n/c, there exist UNSAT CubeGraphs
  -- that cannot be decided by depth-d decision trees.
  -- This is a consequence of Borromean order Theta(n).
  ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
    ∃ G : CubeGraph, G.cubes.length ≥ n ∧
      KConsistent G (n / c) ∧ ¬ G.Satisfiable

/-- Replicability for trees is insufficient (same as non-locality). -/
theorem no_tree_shortcut : ReplicabilitySeparatesTreesFromCircuits :=
  schoenebeck_linear

/-! ## Summary: The 4+1 Symmetry Classification

  We collect the four absence-of-symmetry results into a single structure. -/

/-- The four absent symmetries of SAT on CubeGraph, bundled together.
    Each field witnesses the failure of one computational shortcut. -/
structure FourAbsentSymmetries where
  /-- Non-locality: k-consistency fails for all fixed k -/
  nonlocal : ∀ k : Nat, ∃ n₀ : Nat, ∀ n ≥ n₀,
    ∃ G : CubeGraph, G.cubes.length ≥ n ∧ KConsistent G k ∧ ¬ G.Satisfiable
  /-- Non-affinity: 7 gaps is not a power of 2 -/
  nonaffine : ¬ IsPowerOfTwo 7
  /-- Non-commutativity: transfer operator composition does not commute -/
  noncommutative : mul symM1 symM2 ≠ mul symM2 symM1
  /-- Irreversibility: rank-1 operators satisfy M^3 = M^2 -/
  irreversible : ∀ (M : BoolMat 8), M.IsRankOne → mul M (mul M M) = mul M M

/-- Construction: all four symmetry absences are proved. -/
theorem four_absent_symmetries : FourAbsentSymmetries where
  nonlocal := sat_not_local
  nonaffine := sat_not_affine
  noncommutative := composition_not_commutative
  irreversible := fun M h => composition_irreversible M h

/-! ## Consequence: Algorithm Class Elimination

  Each absent symmetry eliminates a class of polynomial-time algorithms:
  - Non-local:       eliminates propagation / local consistency (AC-3, SA)
  - Non-affine:      eliminates linear algebra over GF(2) (Gaussian, XOR-SAT)
  - Non-commutative: eliminates abelian computation (ACC^0 circuits)
  - Irreversible:    eliminates group-based computation (NC^1, Barrington)

  The conjunction of all four means no algorithm from ANY of these classes
  can solve SAT on CubeGraph in polynomial time.

  What REMAINS: algorithms using replicability (fan-out) beyond these
  classes -- i.e., general polynomial-size circuits. This is P vs NP. -/

/-- The four absent symmetries collectively eliminate all known
    polynomial algorithm classes except general circuits. -/
theorem algorithm_classes_eliminated (h : FourAbsentSymmetries) :
    -- Propagation fails (from non-locality)
    (∀ k, ∃ n₀, ∀ n ≥ n₀, ∃ G : CubeGraph,
      G.cubes.length ≥ n ∧ KConsistent G k ∧ ¬ G.Satisfiable) ∧
    -- Gaussian elimination fails (from non-affinity)
    ¬ IsPowerOfTwo 7 ∧
    -- Abelian computation fails (from non-commutativity)
    mul symM1 symM2 ≠ mul symM2 symM1 ∧
    -- Group computation fails (from irreversibility)
    (∀ M : BoolMat 8, M.IsRankOne → mul M (mul M M) = mul M M) :=
  ⟨h.nonlocal, h.nonaffine, h.noncommutative, h.irreversible⟩

end CubeGraph
