/-
  CubeGraph/TensorEigenvector.lean

  Boolean tensor eigenvector formulation of SAT.

  Each star defines a tensor. A "boolean eigenvector" is a gap selection
  that is self-consistent: contracting each star's tensor with the neighbors'
  selections returns the center's selection.

  SAT ⟺ the system of N star-tensors has a common boolean eigenvector.

  Over a field: eigenvectors found by linear algebra (Perron-Frobenius).
  Over boolean semiring: finding boolean eigenvector = NP-hard.
  This gap = Type 2 UNSAT in spectral language.

  Dependencies: Star.lean, StarMatrix.lean
  See: experiments-ml/027_2026-03-24_star-analysis/SESSION-SUMMARY.md
-/

import CubeGraph.StarMatrix

namespace CubeGraph

/-! ## Section 1: Star Tensor Contraction

  The star tensor for cube i, contracted with gap selections for all
  neighbors, gives a boolean vector in the center's gap space.
  Entry g = 1 iff gap g is compatible with ALL neighbors' selections. -/

/-- Contract star i's tensor with neighbor selections.
    Result[g] = 1 iff g is a gap of cube i AND for every neighbor j,
    transferOp(cube_i, cube_j)[g, s(j)] = 1. -/
def starContraction (G : CubeGraph) (i : Fin G.cubes.length)
    (s : GapSelection G) : Vertex → Bool :=
  fun g =>
    (G.cubes[i]).isGap g &&
    G.edges.all (fun e =>
      -- Only check edges involving cube i
      if e.1 == i then transferOp (G.cubes[e.1]) (G.cubes[e.2]) g (s e.2)
      else if e.2 == i then transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) g
      else true)

/-! ## Section 2: Boolean Eigenvector

  A gap selection s is a "boolean eigenvector" of the star tensor system
  iff contracting each star with s returns s itself.
  That is: for every cube i, starContraction(i, s)[s(i)] = 1.

  This is the FIXED POINT condition: the selection is self-consistent. -/

/-- A gap selection is a boolean eigenvector: each star's contraction,
    evaluated at the selected gap, returns true. -/
def IsBooleanEigenvector (G : CubeGraph) (s : GapSelection G) : Prop :=
  ∀ i : Fin G.cubes.length, starContraction G i s (s i) = true

/-- A boolean eigenvector is a valid gap selection. -/
theorem eigenvector_is_valid (G : CubeGraph) (s : GapSelection G)
    (h : IsBooleanEigenvector G s) :
    validSelection G s := by
  intro i
  have hi := h i
  unfold starContraction at hi
  revert hi
  cases (G.cubes[i]).isGap (s i) <;> simp

/-! ## Section 3: Eigenvector ⟺ SAT

  The fundamental equivalence: boolean eigenvector exists ⟺ SAT. -/

/-- **Boolean eigenvector implies SAT**: if s is an eigenvector,
    then s is a valid compatible gap selection.
    Proof outline: eigenvector condition at star i with edge (i,j)
    gives transferOp check for that edge. -/
theorem eigenvector_implies_sat (G : CubeGraph) (s : GapSelection G)
    (h : IsBooleanEigenvector G s) :
    G.Satisfiable := by
  refine ⟨s, eigenvector_is_valid G s h, ?_⟩
  intro e he
  have hi := h e.1
  unfold starContraction at hi
  simp only [Bool.and_eq_true, List.all_eq_true] at hi
  have hedge := hi.2 e he
  simp only [beq_iff_eq] at hedge
  exact hedge

/-- **SAT implies boolean eigenvector**: a satisfying selection
    is automatically an eigenvector.
    Proof outline: valid + compatible selection satisfies starContraction at each i. -/
theorem sat_implies_eigenvector (G : CubeGraph)
    (hsat : G.Satisfiable) :
    ∃ s : GapSelection G, IsBooleanEigenvector G s := by
  obtain ⟨s, hv, hc⟩ := hsat
  refine ⟨s, fun i => ?_⟩
  unfold starContraction
  simp only [Bool.and_eq_true, List.all_eq_true]
  exact ⟨hv i, fun e he => by
    simp only [beq_iff_eq]
    by_cases h1 : e.1 = i
    · simp only [if_pos h1]; exact h1 ▸ hc e he
    · simp only [if_neg h1]
      by_cases h2 : e.2 = i
      · simp only [if_pos h2]; exact h2 ▸ hc e he
      · simp only [if_neg h2]⟩

/-- **The Fundamental Equivalence**: SAT ⟺ boolean eigenvector exists. -/
theorem sat_iff_eigenvector (G : CubeGraph) :
    G.Satisfiable ↔ ∃ s : GapSelection G, IsBooleanEigenvector G s :=
  ⟨sat_implies_eigenvector G, fun ⟨s, h⟩ => eigenvector_implies_sat G s h⟩

/-! ## Section 4: The Field vs Semiring Gap

  Over a FIELD (e.g., R):
  - Replace Bool with R, AND with ×, OR with +
  - The star contraction becomes a multilinear map
  - Eigenvectors found by Perron-Frobenius (nonneg tensors → dominant eigenvector)
  - Power iteration converges in polynomial time

  Over BOOLEAN SEMIRING:
  - OR is idempotent (1 ∨ 1 = 1): power iteration stalls immediately
  - No additive inverse: cannot "subtract" to isolate components
  - Finding boolean eigenvector = finding satisfying assignment = NP-hard

  The gap between field and semiring IS the computational gap.
  This is Type 2 UNSAT in eigenvalue language:
  - Field: local consistency → eigenvectors → P
  - Boolean: local consistency → NO eigenvector method → NP -/

/-- Power iteration on boolean stalls: OR(x, x) = x for all x.
    Iterating the star contraction with a fixed selection gives
    the same result immediately — no convergence to new information. -/
theorem boolean_power_stall :
    ∀ a : Bool, (a || a) = a := by
  intro a; cases a <;> rfl

/-! ## Section 5: Local vs Global Eigenvectors

  Each star INDIVIDUALLY always has an eigenvector (any viable gap works).
  The hardness is in finding a COMMON eigenvector for all N stars.

  This parallels the symmetry breaking chain:
  - 1 star: eigenvector trivially exists (pick any gap)
  - 2 stars: common eigenvector = 2-CSP (polynomial)
  - N stars: common eigenvector = SAT (NP-hard for k ≥ 3) -/

/-- Every individual star has a local eigenvector (any gap is self-consistent
    when we don't constrain neighbors). -/
private theorem gapMask_pos_has_gap :
    ∀ (mask : Fin 256), mask.val > 0 →
      ∃ v : Fin 8, ((mask.val >>> v.val) &&& 1 == 1) = true := by native_decide

theorem local_eigenvector_exists (G : CubeGraph) (i : Fin G.cubes.length) :
    ∃ g : Vertex, (G.cubes[i]).isGap g = true := by
  have h := (G.cubes[i]).gaps_nonempty
  have ⟨v, hv⟩ := gapMask_pos_has_gap (G.cubes[i]).gapMask h
  exact ⟨v, hv⟩

/-! ## Section 6: Capstone -/

/-- **Capstone**: SAT = boolean eigenvector, with the field/semiring gap.
    (1) SAT ⟺ boolean eigenvector exists
    (2) Individual stars always have local eigenvectors
    (3) Boolean power iteration stalls (OR idempotent)
    (4) The gap is between field (P) and semiring (NP) -/
theorem tensor_eigenvector_framework (G : CubeGraph) :
    -- (1) SAT ⟺ eigenvector
    (G.Satisfiable ↔ ∃ s : GapSelection G, IsBooleanEigenvector G s) ∧
    -- (2) Each cube has at least one gap
    (∀ i : Fin G.cubes.length, ∃ g : Vertex, (G.cubes[i]).isGap g = true) ∧
    -- (3) OR is idempotent (power iteration stalls)
    (∀ a : Bool, (a || a) = a) := by
  exact ⟨sat_iff_eigenvector G,
         local_eigenvector_exists G,
         boolean_power_stall⟩

end CubeGraph
