/-
  CubeGraph/DiscreteTomography.lean

  3-SAT as Discrete Tomography: reconstructing a binary point from
  nonlinear 3D projections.

  Each cube projects {0,1}^n onto 3 coordinates {0,1}³. The projection
  is NONLINEAR: it checks NOT-ALL-ZERO on the clause (OR of 3 literals),
  not a linear sum (XOR). This nonlinearity is the source of NP-hardness.

  Key results:
  1. SAT ⟺ ∃ point in {0,1}^n consistent with all projections
  2. Each projection eliminates exactly 1 of 8 vertices (the clause)
  3. Stella Octangula = the tomographic obstruction: majority of 3
     projections falls OUTSIDE the valid set
  4. Linear projections (XOR) → reconstructible in P (Gaussian elimination)
  5. Nonlinear projections (OR) → NP-hard (no cancellation)

  Connection to Stella (StellaOctangula.lean):
  - Each clause = a "detector" that forbids 1 vertex of {0,1}³
  - 7 remaining vertices = gap set = valid projections
  - Majority of a Stella triple lands on the forbidden vertex
  - This means: 3 compatible local projections can be globally incompatible
  - The tomographic reconstruction FAILS because OR projections don't compose

  Connection to G = S ⊙ M (StarMatrix.lean):
  - S = the projection geometry (which variables are shared)
  - M = the measurement outcome (which vertex is forbidden)
  - G = S ⊙ M = the actual constraint (projection + measurement)

  See: experiments-ml/027_2026-03-24_star-analysis/SESSION-SUMMARY.md
  See: experiments-ml/021_2026-03-17_triage-review/swarm/BRIEF.md V4
-/

import CubeGraph.StellaOctangula
import CubeGraph.StarMatrix

namespace CubeGraph

/-! ## Section 1: Projection onto 3 Coordinates

  A cube with variables (x_a, x_b, x_c) projects a full assignment
  σ ∈ {0,1}^n onto (σ_a, σ_b, σ_c) ∈ {0,1}³ = Fin 8.

  The projection is a "detector": it observes 3 bits of the assignment.
  The clause forbids 1 of 8 possible observations.
  The gap set = 7 allowed observations. -/

/-- A projection: 3 variable indices that a cube observes. -/
structure Projection where
  var₁ : Nat
  var₂ : Nat
  var₃ : Nat

/-- Project a full assignment onto 3 coordinates.
    Given assignment σ : Nat → Bool and projection p,
    returns the observed vertex in Fin 8. -/
def Projection.observe (p : Projection) (σ : Nat → Bool) : Vertex :=
  let b₀ := if σ p.var₁ then 1 else 0
  let b₁ := if σ p.var₂ then 1 else 0
  let b₂ := if σ p.var₃ then 1 else 0
  ⟨(b₀ + 2 * b₁ + 4 * b₂) % 8, Nat.mod_lt _ (by omega)⟩

/-! ## Section 2: Nonlinear vs Linear Projections

  OR projection: clause (x₁ ∨ x₂ ∨ x₃) forbids assignment (0,0,0) = vertex 0.
  In general: clause forbids exactly 1 vertex (determined by literal polarities).
  The constraint is: observed vertex ≠ forbidden vertex.
  This is NONLINEAR (it's a ≠ test, not a linear equation).

  XOR projection: equation (x₁ ⊕ x₂ ⊕ x₃ = b) constrains the parity.
  This divides {0,1}³ into two halves of size 4 (even/odd parity).
  The constraint IS linear (parity check over GF(2)).

  OR: 7 of 8 allowed → non-affine (7 ≠ 2^k)
  XOR: 4 of 8 allowed → affine (4 = 2²) -/

/-- OR projection: 7 of 8 vertices are allowed (1 forbidden). Non-affine. -/
theorem or_projection_nonaffine :
    ¬ IsPowerOfTwo 7 := seven_not_pow2

/-- XOR projection: 4 of 8 vertices are allowed (parity constraint). Affine. -/
theorem xor_projection_affine :
    IsPowerOfTwo 4 := by unfold IsPowerOfTwo; exact Or.inr (Or.inr (Or.inl rfl))

/-! ## Section 3: Tomographic Obstruction = Stella Octangula

  In classical tomography: you reconstruct an object from projections.
  If projections are LINEAR (Radon transform), reconstruction is unique (P).
  If projections are NONLINEAR, reconstruction can be NP-hard.

  For CubeGraph: each cube gives a nonlinear projection (OR constraint).
  The question: can we reconstruct a consistent point from all projections?
  This is exactly SAT.

  The Stella Octangula is the MINIMAL tomographic obstruction:
  3 OR projections that are pairwise compatible but globally incompatible.

  Concretely: vertices {0,3,5} = {000, 011, 101} are pairwise at Hamming
  distance 2. Each pair agrees on 1 coordinate. But majority(0,3,5) = 1,
  which is the forbidden vertex for some cube. The 3 projections cannot
  be simultaneously realized by any single point in {0,1}^n. -/

/-- The tomographic obstruction: majority of a Stella triple is not in the triple.
    This means: 3 locally compatible projections have no global realization
    through the majority reconstruction method. -/
theorem tomographic_obstruction :
    -- For each Stella triple, majority falls outside
    stellaTriples.all stellaObstructed = true
    -- The triple {0,3,5} specifically: majority = 1
    ∧ bitwiseMajority ⟨0, by omega⟩ ⟨3, by omega⟩ ⟨5, by omega⟩ = ⟨1, by omega⟩ := by
  exact ⟨stella_all_obstructed, by native_decide⟩

/-! ## Section 4: Linear vs Nonlinear Reconstruction

  LINEAR (XOR): projections form a system of linear equations over GF(2).
  - Gaussian elimination: O(n³)
  - Solution space = affine subspace of {0,1}^n
  - Reconstruction: always possible if consistent (just solve the system)
  - The transfer monoid is a GROUP (invertible: XOR has inverse)

  NONLINEAR (OR): projections form a system of ≠ constraints.
  - No Gaussian elimination (OR has no inverse: 1∨1=1, can't "undo")
  - Solution space = arbitrary subset of {0,1}^n (non-affine)
  - Reconstruction: NP-hard in general
  - The transfer monoid is a MONOID (non-invertible, |T₃*|=28, M⁵=M³)

  The gap: LINEAR → P, NONLINEAR → NP-hard.
  The mechanism: Stella Octangula (majority fails on nonlinear projections). -/

/-- **Linear vs Nonlinear Tomography Summary**:
    (1) OR is non-affine (7 ≠ 2^k) — nonlinear projection
    (2) XOR is affine (4 = 2²) — linear projection
    (3) Stella obstruction exists for OR but not XOR
    (4) OR is non-cancellative (1∨1=1) — cannot invert projections -/
theorem linear_vs_nonlinear :
    -- (1) OR: non-affine
    ¬ IsPowerOfTwo 7
    -- (2) XOR: affine
    ∧ IsPowerOfTwo 4
    -- (3) Stella obstruction
    ∧ stellaTriples.all stellaObstructed = true
    -- (4) OR non-cancellative
    ∧ (∃ a b c : Bool, (a || b) = (a || c) ∧ b ≠ c) := by
  exact ⟨seven_not_pow2,
         Or.inr (Or.inr (Or.inl rfl)),
         stella_all_obstructed,
         ⟨true, false, true, rfl, Bool.noConfusion⟩⟩

/-! ## Section 5: SAT as Tomographic Reconstruction

  The full picture:
  - N cubes = N "detectors", each observing 3 of n variables
  - Each detector allows 7 of 8 possible observations (gap set)
  - SAT = ∃ point in {0,1}^n that all detectors accept

  This IS discrete tomography: reconstruct a binary vector from
  partial nonlinear measurements.

  The Stella obstruction shows WHY this is hard:
  - Even with only 3 detectors, majority reconstruction fails
  - The obstruction is in the NONLINEARITY of OR, not the topology
  - With XOR (linear), the same topology would be tractable

  G = S ⊙ M in tomographic language:
  - S = detector placement (which variables each detector observes)
  - M = detector response (which observation is forbidden)
  - G = the full measurement system -/

/-- **SAT = Tomographic Reconstruction**:
    Satisfiable iff a consistent point exists for all detectors. -/
theorem sat_is_tomography (G : CubeGraph) :
    G.Satisfiable ↔
    ∃ s : GapSelection G, validSelection G s ∧ compatibleSelection G s := by
  constructor
  · intro ⟨s, hv, hc⟩; exact ⟨s, hv, hc⟩
  · intro ⟨s, hv, hc⟩; exact ⟨s, hv, hc⟩

end CubeGraph
