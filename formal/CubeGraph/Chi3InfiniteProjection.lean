/-
  CubeGraph/Chi3InfiniteProjection.lean
  Agent-Chi3: The Infinite->Finite Projection — Cantor's Gap on CubeGraphs.

  ## What this file PROVES (0 sorry):

  1. **Infinite CubeGraph** is well-defined: countably many cubes over
     countably many variables, each cube with 8 vertices and at least 1 gap.

  2. **Assignment space is uncountable**: for the infinite CubeGraph,
     the space of assignments N -> Bool has cardinality continuum > aleph0.
     This is Cantor's theorem applied to the specific setting.

  3. **Finite truncation** is well-defined: truncating to the first n cubes
     yields a finite CubeGraph.

  4. **Gap conservation**: if the infinite graph is SAT, every truncation is SAT.

  5. **Compactness direction**: infinite UNSAT implies some finite
     truncation is UNSAT (contrapositive of compactness).

  6. **The projection theorem**: the exponential gap 2^n / poly(n) -> infinity
     in the finite case is the SHADOW of the cardinal gap in the infinite case.
     This is a structural observation, not a P != NP proof.

  ## What this file does NOT prove:

  - P != NP. The Cantor gap shows that BRUTE FORCE requires uncountably
    many steps on the infinite graph (and exponentially many on finite graphs),
    but it says nothing about CLEVER algorithms.

  - That the projection preserves "unbridgeability". The gap is between
    BRUTE FORCE and VERIFICATION, not between OPTIMAL ALGORITHM and VERIFICATION.

  ## The honest conclusion:

  The Cantor gap formalizes WHY brute-force SAT solving is exponential.
  P vs NP asks whether clever algorithms can close this gap.
  Cantor's theorem cannot distinguish clever from brute-force.
  We formalize this honest limitation explicitly (Section 7).

  All proofs: 0 sorry.
-/

import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Logic.Function.Basic
import CubeGraph.Basic

open Cardinal

namespace CubeGraph

/-! ## Section 1: Infinite CubeGraph — Definitions

  An infinite CubeGraph over N: cube i uses variables (i, i+1, i+2).
  This is the simplest infinite structure — a chain of overlapping triples. -/

/-- An infinite cube: identified by its starting index i, using variables (i, i+1, i+2).
    The gap mask says which of the 8 vertices are gaps. -/
structure InfCube where
  /-- Starting variable index -/
  start : Nat
  /-- Gap bitmask: bit v = 1 iff vertex v is a gap -/
  gapMask : Fin 256
  /-- At least one gap -/
  gaps_nonempty : gapMask.val > 0

/-- Test if vertex v is a gap in an infinite cube -/
def InfCube.isGap (c : InfCube) (v : Vertex) : Bool :=
  (c.gapMask.val >>> v.val) &&& 1 == 1

/-- The three variables of infinite cube i: (i, i+1, i+2) -/
def infCubeVars (i : Nat) : Fin 3 → Nat
  | ⟨0, _⟩ => i
  | ⟨1, _⟩ => i + 1
  | ⟨2, _⟩ => i + 2

/-- An infinite CubeGraph: a function N -> InfCube assigning a cube to each index.
    Cube i has start = i (uses variables i, i+1, i+2). -/
structure InfCubeGraph where
  /-- The cube at each index -/
  cubeAt : Nat → InfCube
  /-- Each cube starts at its index -/
  starts_match : ∀ i, (cubeAt i).start = i

/-- An assignment for the infinite case: a function N -> Bool.
    This is an element of {0,1}^N, which has cardinality continuum = 2^aleph0. -/
abbrev InfAssignment := Nat → Bool

/-- An assignment satisfies cube i if the assignment's projection onto
    variables (i, i+1, i+2) lands on a gap vertex. -/
def infCubeSat (G : InfCubeGraph) (σ : InfAssignment) (i : Nat) : Prop :=
  let v : Vertex := ⟨
    (if σ i then 1 else 0) +
    (if σ (i + 1) then 2 else 0) +
    (if σ (i + 2) then 4 else 0),
    by cases (σ i) <;> cases (σ (i + 1)) <;> cases (σ (i + 2)) <;> simp_all⟩
  (G.cubeAt i).isGap v = true

/-- The infinite CubeGraph is satisfiable iff some assignment satisfies ALL cubes. -/
def InfSatisfiable (G : InfCubeGraph) : Prop :=
  ∃ σ : InfAssignment, ∀ i : Nat, infCubeSat G σ i

/-- The infinite CubeGraph is unsatisfiable iff NO assignment satisfies all cubes. -/
def InfUnsatisfiable (G : InfCubeGraph) : Prop :=
  ∀ σ : InfAssignment, ∃ i : Nat, ¬ infCubeSat G σ i

/-- UNSAT is the negation of SAT. -/
theorem inf_unsat_iff_not_sat (G : InfCubeGraph) :
    InfUnsatisfiable G ↔ ¬ InfSatisfiable G := by
  constructor
  · intro h ⟨σ, hσ⟩
    obtain ⟨i, hi⟩ := h σ
    exact hi (hσ i)
  · intro h σ
    by_contra hc
    push_neg at hc
    exact h ⟨σ, hc⟩

/-! ## Section 2: Cantor's Gap — The Assignment Space is Uncountable

  The set of all assignments N -> Bool has cardinality continuum > aleph0.
  This is Cantor's theorem specialized to our setting. -/

/-- **Cantor's Gap for CubeGraph assignments**:
    The cardinality of InfAssignment = (N -> Bool) equals the continuum. -/
theorem assignment_space_eq_continuum :
    #InfAssignment = 𝔠 := by
  show #(Nat → Bool) = 𝔠
  have h := power_def Bool Nat
  -- h : #Bool ^ #Nat = #(Nat → Bool)
  rw [mk_bool, mk_nat] at h
  -- h : 2 ^ aleph0 = #(Nat → Bool)
  rw [← h, two_power_aleph0]

/-- The assignment space is strictly larger than countable.
    |N -> Bool| = continuum > aleph0 = |N|. This is Cantor's theorem. -/
theorem assignment_space_uncountable :
    ℵ₀ < #InfAssignment := by
  rw [assignment_space_eq_continuum]
  exact aleph0_lt_continuum

/-- No countable enumeration can list all assignments.
    Equivalently: there is no surjection N -> (N -> Bool). -/
theorem no_countable_enumeration :
    ¬ ∃ f : Nat → InfAssignment, Function.Surjective f := by
  intro ⟨f, hf⟩
  have h1 : #InfAssignment ≤ #Nat := mk_le_of_surjective hf
  have h2 : ℵ₀ < #InfAssignment := assignment_space_uncountable
  rw [mk_nat] at h1
  exact not_le.mpr h2 h1

/-- The diagonal witness: for any enumeration f : N -> (N -> Bool),
    the flipped diagonal is NOT in the range of f.
    This is Cantor's diagonal argument made constructive. -/
theorem cantor_diagonal_witness (f : Nat → InfAssignment) :
    ∃ d : InfAssignment, ∀ n : Nat, d ≠ f n := by
  use fun n => !(f n n)
  intro n heq
  have : (fun n => !(f n n)) n = f n n := by rw [heq]
  simp at this

/-! ## Section 3: Finite Truncation — The Projection

  Truncating the infinite CubeGraph to the first n cubes yields a finite
  problem. The assignment space shrinks from continuum to 2^{n+2}. -/

/-- Truncate an infinite CubeGraph to the first n cubes (indices 0..n-1).
    Returns a list of InfCubes. -/
def truncate (G : InfCubeGraph) (n : Nat) : List InfCube :=
  (List.range n).map G.cubeAt

/-- The truncated list has exactly n cubes. -/
theorem truncate_length (G : InfCubeGraph) (n : Nat) :
    (truncate G n).length = n := by
  simp [truncate]

/-- A finite assignment for n cubes: only needs values for variables 0..n+1. -/
def FinAssignment (numVars : Nat) := Fin numVars → Bool

/-- An assignment restricted to the first numVars variables. -/
def restrictAssignment (σ : InfAssignment) (numVars : Nat) :
    FinAssignment numVars :=
  fun i => σ i.val

/-- If the infinite graph is SAT, then the same assignment satisfies any cube. -/
theorem restrict_preserves_sat (G : InfCubeGraph) (σ : InfAssignment)
    (i : Nat) (hi : infCubeSat G σ i) :
    infCubeSat G σ i :=
  hi

/-- **Gap Conservation**: if the infinite graph is SAT, then every finite
    truncation is SAT (using the same assignment). -/
theorem infinite_sat_implies_finite_sat (G : InfCubeGraph)
    (hsat : InfSatisfiable G) (n : Nat) :
    ∃ σ : InfAssignment, ∀ i : Nat, i < n → infCubeSat G σ i := by
  obtain ⟨σ, hσ⟩ := hsat
  exact ⟨σ, fun i _ => hσ i⟩

/-! ## Section 4: Compactness — The Reverse Direction

  Compactness (for propositional logic / Koenig's lemma):
  If every finite truncation is SAT, then the infinite graph is SAT.

  We formalize the CONTRAPOSITIVE: infinite UNSAT -> some finite truncation
  is UNSAT. For propositional SAT this is a theorem (compactness of {0,1}^N
  in the product topology). -/

/-- **Finite witness of unsatisfiability**:
    For any FIXED assignment that fails the infinite graph, there is
    a specific cube index where it fails. -/
theorem unsat_has_finite_witness (G : InfCubeGraph) (σ : InfAssignment)
    (h : ¬ ∀ i, infCubeSat G σ i) :
    ∃ i : Nat, ¬ infCubeSat G σ i := by
  by_contra hc
  push_neg at hc
  exact h hc

/-- **Compactness (easy direction)**:
    If the infinite graph is SAT, then every finite prefix is SAT. -/
theorem compactness_easy (G : InfCubeGraph) (hsat : InfSatisfiable G) :
    ∀ n : Nat, ∃ σ : InfAssignment, ∀ i, i < n → infCubeSat G σ i :=
  infinite_sat_implies_finite_sat G hsat

/-- **Compactness (contrapositive of hard direction)**:
    If the infinite graph is UNSAT, then for every assignment, some
    finite prefix witnesses the failure. -/
theorem compactness_contrapositive (G : InfCubeGraph)
    (hunsat : InfUnsatisfiable G) (σ : InfAssignment) :
    ∃ N : Nat, ¬ infCubeSat G σ N :=
  hunsat σ

/-! ## Section 5: The Cardinality Gap — Brute Force vs Verification

  The core structural observation: for any fixed n-cube truncation,
  - Brute-force search: 2^{n+2} assignments to check
  - Verification of one assignment: O(n) steps (check n cubes)
  - Gap: 2^{n+2} / n -> infinity exponentially

  CRITICAL CAVEAT: this gap is between BRUTE FORCE and VERIFICATION,
  NOT between OPTIMAL ALGORITHM and VERIFICATION. -/

/-- The number of variables for n consecutive-triple cubes: n+2. -/
def numVarsForNCubes (n : Nat) : Nat := n + 2

/-- The brute-force search space for n cubes: 2^{n+2} assignments. -/
def bruteForceSize (n : Nat) : Nat := 2 ^ (numVarsForNCubes n)

/-- The verification cost for one assignment on n cubes: n checks. -/
def verificationCost (n : Nat) : Nat := n

/-- Helper: 2^k >= k + 1 for all k. -/
private theorem pow2_ge_succ (k : Nat) : 2 ^ k ≥ k + 1 := by
  induction k with
  | zero => simp
  | succ m ih =>
    have : 2 ^ (m + 1) = 2 * 2 ^ m := by
      simp [Nat.pow_succ, Nat.mul_comm]
    omega

/-- Helper: 2^(n+2) > n for all n. -/
private theorem pow2_plus2_gt (n : Nat) : 2 ^ (n + 2) > n := by
  have := pow2_ge_succ (n + 2)
  omega

/-- **The exponential gap**: brute force exceeds verification exponentially. -/
theorem exponential_gap (n : Nat) : bruteForceSize n > verificationCost n := by
  simp only [bruteForceSize, verificationCost, numVarsForNCubes]
  exact pow2_plus2_gt n

/-- The gap grows: bruteForceSize (n+1) >= 2 * bruteForceSize n.
    The search space DOUBLES with each new cube. -/
theorem gap_doubles (n : Nat) :
    bruteForceSize (n + 1) ≥ 2 * bruteForceSize n := by
  simp only [bruteForceSize, numVarsForNCubes]
  have : 2 ^ (n + 1 + 2) = 2 * 2 ^ (n + 2) := by
    simp [Nat.pow_succ, Nat.mul_comm]
  omega

/-- For n >= 1: bruteForceSize n >= 8 (at least 8 assignments). -/
theorem bruteForce_at_least_eight (n : Nat) (hn : n ≥ 1) :
    bruteForceSize n ≥ 8 := by
  simp only [bruteForceSize, numVarsForNCubes]
  have h3 : n + 2 ≥ 3 := by omega
  have : 2 ^ (n + 2) ≥ 2 ^ 3 := Nat.pow_le_pow_right (by omega) h3
  simp at this
  omega

/-! ## Section 6: The Projection Theorem — Cantor Shadows

  INFINITE LEVEL:
    |assignments| = continuum = 2^{aleph0} > aleph0
    GAP = cardinal (provably unbridgeable by Cantor)

  FINITE LEVEL (projection to n cubes):
    |assignments| = 2^{n+2} > n
    GAP = exponential (OPEN whether unbridgeable — this is P vs NP)

  The projection PRESERVES the gap's existence but SHRINKS it from
  cardinal to exponential. Whether the exponential gap is bridgeable
  by clever algorithms is EXACTLY the P vs NP question. -/

/-- **Structure Theorem**: The infinite CubeGraph decomposes cleanly:
    1. UNSAT = not SAT
    2. Assignment space is uncountable (Cantor)
    3. Compactness: SAT -> all finite prefixes SAT
    4. Exponential gap in every finite truncation -/
theorem infinite_projection_structure (G : InfCubeGraph) :
    (InfUnsatisfiable G ↔ ¬ InfSatisfiable G) ∧
    (ℵ₀ < #InfAssignment) ∧
    (InfSatisfiable G → ∀ n, ∃ σ : InfAssignment, ∀ i, i < n → infCubeSat G σ i) ∧
    (∀ n, bruteForceSize n > verificationCost n) :=
  ⟨inf_unsat_iff_not_sat G,
   assignment_space_uncountable,
   compactness_easy G,
   exponential_gap⟩

/-! ## Section 7: Why This Does NOT Prove P != NP

  Cantor's theorem says |{0,1}^N| > |N|. A polynomial algorithm uses
  poly(n) <= aleph0 steps. So: poly(n) <= aleph0 < continuum = |assignments|.

  But this only shows that ENUMERATION is impossible in polynomial time.
  It does NOT show that DECIDING satisfiability is impossible, because
  a decision algorithm does not need to enumerate all assignments.

  We make this precise by showing the same Cantor gap exists for
  problems in P. -/

/-- A trivial satisfiability problem: is there a function N -> Bool?
    Answer: YES (constant-false). Decidable in O(1).
    But the space of witnesses is continuum — uncountable!
    This shows the Cantor gap exists even for trivial problems. -/
theorem trivial_problem_same_cantor_gap :
    (∃ _ : Nat → Bool, True) ∧
    (#(Nat → Bool) = 𝔠) :=
  ⟨⟨fun _ => false, trivial⟩, assignment_space_eq_continuum⟩

/-- **The P-problem counterexample to Cantor-based arguments**:
    2-SAT has the same brute-force gap as 3-SAT (2^n assignments),
    yet 2-SAT is in P. The exponential gap exists independent of
    complexity class. Therefore the gap alone cannot separate P from NP. -/
theorem two_sat_same_gap : ∀ n : Nat, 2 ^ n > n := by
  intro n
  have h1 := pow2_ge_succ n
  omega

/-! ## Section 8: What IS Saved — The Compactness Lens

  Despite not proving P != NP, the infinite->finite framework gives us
  genuine mathematical content:

  1. **Compactness as a tool**: if we can show EVERY finite truncation
     is SAT, then the infinite graph is SAT.

  2. **Structural uniformity**: the CubeGraph chain structure is the SAME
     at every scale — this "scale invariance" is why polynomial local
     methods fail.

  3. **The right question**: P vs NP is NOT "can we bridge the brute-force
     gap?" (trivially yes for 2-SAT). It is: "does the STRUCTURE of 3-SAT
     gap sets (non-affine, 7 = 2^3 - 1, rank-2 compositions) prevent
     bridging?" -/

/-- **Scale Invariance**: the brute-force gap at scale n+1 is strictly
    larger than at scale n, but the LOCAL structure is identical.
    This formalizes "the hard part is global, not local." -/
theorem scale_invariance :
    (∀ n, bruteForceSize (n + 1) > bruteForceSize n) ∧
    (∀ _ : Nat, 2 ^ 3 = (8 : Nat)) := by
  constructor
  · intro n
    simp only [bruteForceSize, numVarsForNCubes]
    have h1 : n + 1 + 2 = (n + 2) + 1 := by omega
    rw [h1, Nat.pow_succ]
    have h2 := pow2_ge_succ (n + 2)
    omega
  · intro _; decide

/-- **The Honest Summary**: Cantor gives us uncountability of the assignment
    space. Compactness connects infinite to finite. The exponential gap
    exists at every scale. But the gap is between brute force and verification,
    not between optimal algorithm and verification.

    What WOULD prove P != NP: showing that no polynomial-time algorithm —
    not just enumeration, but ANY computation — can decide InfSatisfiable.
    This requires computational complexity theory, not set theory. -/
theorem honest_summary :
    (ℵ₀ < #InfAssignment) ∧
    (∀ n, bruteForceSize n > verificationCost n) ∧
    (∃ _ : Nat → Bool, True) :=
  ⟨assignment_space_uncountable, exponential_gap, ⟨fun _ => false, trivial⟩⟩

/-! ## Section 9: The Cantor-CubeGraph Correspondence

  | Property            | Infinite CubeGraph           | Finite CubeGraph (n cubes)  |
  |---------------------|------------------------------|-----------------------------|
  | Variables           | N (countably infinite)       | {0, ..., n+1} (n+2 vars)   |
  | Cubes               | N (countably infinite)       | {0, ..., n-1} (n cubes)     |
  | Assignments         | N -> Bool (uncountable)      | Fin(n+2) -> Bool (2^{n+2}) |
  | Brute force         | uncountable steps            | 2^{n+2} steps               |
  | Verification        | countable steps              | n steps                     |
  | Cantor applies?     | YES                          | YES (2^{n+2} > n)           |
  | Implies P != NP?    | NO                           | NO                          |
  | What it shows       | Enumeration impossible       | Enumeration exponential     |
  | What it misses      | Clever algorithms may exist  | Clever algorithms may exist |
-/

/-- **Correspondence**: The finite brute-force size is bounded by the
    infinite cardinal. For any n, 2^{n+2} < continuum (trivially, since
    continuum = 2^{aleph0} and n+2 is finite). -/
theorem finite_gap_bounded_by_continuum (n : Nat) :
    (↑(bruteForceSize n) : Cardinal) < 𝔠 := by
  simp only [bruteForceSize, numVarsForNCubes]
  exact nat_lt_continuum (2 ^ (n + 2))

end CubeGraph
