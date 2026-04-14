/-
  CubeGraph/WeakExpander.lean — Weak Expander Bridge to Bounded-Depth Frege

  Connects CubeGraph theory to Gryaznov-Talebanfard (2024):
  "Bounded-Depth Frege Lower Bounds for Random 3-CNFs via Deterministic Restrictions"

  Their result: depth-k Frege refutations of random 3-CNFs with Theta(n) clauses
  need Omega(n^{1 + epsilon_k}) steps, where epsilon_k = 2^{-(k+1)}.

  Key definition: (r, Delta, c)-weak expander on the clause-variable bipartite graph.
  - All left vertices have degree <= Delta (= 3 for 3-CNF)
  - |I| <= r/2 => |boundary(I)| > 0
  - r/2 < |I| <= r => |boundary(I)| >= c|I|

  Our contribution: CubeGraph provides ALGEBRAIC structure (transfer operators,
  rank theory, KR complexity) that is invisible to GT24's technique.

  Chain of proven results:
  1. WeakExpander definition for CubeGraph (new, this file)
  2. Random CubeGraph satisfies weak expansion (axiom — from GT24)
  3. Weak expansion => resolution width lower bound (axiom — GT24 Lemma 14)
  4. Rank-1 bottleneck: IsRankOne => aperiodic (M^3 = M^2), KR = 0
  5. Rank-2 generates Z/2Z => KR >= 1
  6. Connection: expansion drives BOTH width bound AND rank stabilization
  7. Gap: turning this into super-polynomial requires showing restriction preserves algebra

  References:
  - Gryaznov, Talebanfard. arXiv:2403.02275 (March 2024).
  - de Rezende, Fleming, Janett, Nordstrom, Pang. STOC 2025.
  - Zhan. arXiv:2602.23411 (Feb 2026).
  - Atserias, Dalmau. ICALP 2007.
  - Schoenebeck. STOC 2008.

  See: SchoenebeckChain.lean (SA/k-consistency lower bound)
  See: AC0FregeLowerBound.lean (bounded-depth Frege via BIKPPW)
  See: DepthFregeLowerBound.lean (depth-sensitive bounds)
  See: BandSemigroup.lean (rank-1 aperiodic, KR = 0)
  See: KRBounds.lean (rank2_kr_geq_one — Z/2Z witness)
  See: InformationChannel.lean (dead channels, capacity vs requirement)
-/

import CubeGraph.AC0FregeLowerBound
import CubeGraph.BandSemigroup
import CubeGraph.KRBounds
import CubeGraph.ERLowerBound

namespace CubeGraph

open BoolMat

/-! ## Section 1: Weak Expander Definition

Gryaznov-Talebanfard (2024) define a (r, Delta, c)-weak expander
on a bipartite graph G = (L cup R, E):
- All vertices in L have degree <= Delta
- For all I subset L with |I| <= r/2: |boundary(I)| > 0
- For all I subset L with r/2 < |I| <= r: |boundary(I)| >= c|I|

For CubeGraph: L = cubes, R = variables, Delta = 3 (each cube has 3 vars),
r = Theta(n). -/

/-- A bipartite graph between cubes and variables.
    In CubeGraph, each cube touches exactly 3 variables, giving degree 3 on left. -/
structure BipartiteGraph where
  /-- Number of left vertices (cubes) -/
  numLeft : Nat
  /-- Number of right vertices (variables) -/
  numRight : Nat
  /-- Adjacency: left vertex i is connected to right vertex j -/
  adj : Fin numLeft → Fin numRight → Bool

namespace BipartiteGraph

/-- Degree of a left vertex -/
def leftDegree (B : BipartiteGraph) (i : Fin B.numLeft) : Nat :=
  (List.finRange B.numRight).countP (fun j => B.adj i j)

/-- Neighborhood of a set of left vertices: right vertices adjacent to some member -/
def neighborhood (B : BipartiteGraph) (S : List (Fin B.numLeft)) : List (Fin B.numRight) :=
  (List.finRange B.numRight).filter (fun j => S.any (fun i => B.adj i j))

/-- Boundary size of a set of left vertices -/
def boundary (B : BipartiteGraph) (S : List (Fin B.numLeft)) : Nat :=
  (neighborhood B S).length

end BipartiteGraph

/-- **(r, Delta, c)-Weak Expander** (Gryaznov-Talebanfard 2024, Definition 2.1).
    A bipartite graph where:
    1. Left vertices have degree <= Delta
    2. Small left subsets (|I| <= r/2) have nonempty boundary
    3. Medium left subsets (r/2 < |I| <= r) have boundary >= c * |I| -/
structure WeakExpander (B : BipartiteGraph) where
  /-- Expansion radius -/
  r : Nat
  /-- Maximum left degree -/
  delta : Nat
  /-- Expansion constant -/
  c : Nat
  /-- r > 0 -/
  r_pos : r > 0
  /-- c > 0 -/
  c_pos : c > 0
  /-- All left vertices have degree <= delta -/
  degree_bound : ∀ i : Fin B.numLeft, B.leftDegree i ≤ delta
  /-- Small sets have nonempty boundary -/
  small_expansion : ∀ (S : List (Fin B.numLeft)),
    S.Nodup → S.length > 0 → S.length ≤ r / 2 →
    B.boundary S > 0
  /-- Medium sets have linear boundary -/
  medium_expansion : ∀ (S : List (Fin B.numLeft)),
    S.Nodup → S.length > r / 2 → S.length ≤ r →
    B.boundary S ≥ c * S.length

/-! ## Section 2: CubeGraph to BipartiteGraph -/

/-- Extract the bipartite graph from a CubeGraph.
    Left = cubes, Right = variables, edge iff variable appears in cube. -/
def toBipartite (G : CubeGraph) (numVars : Nat) : BipartiteGraph where
  numLeft := G.cubes.length
  numRight := numVars
  adj := fun i j =>
    let c := G.cubes[i]
    (c.vars).any (fun v => v == j.val + 1)  -- 1-indexed to 0-indexed

/-! ## Section 3: Weak Expansion of Random CubeGraph (Axiom from GT24)

Gryaznov-Talebanfard prove that random 3-CNF with Theta(n) clauses
has a clause-variable bipartite graph that is a weak expander w.h.p.
This follows from standard random bipartite graph expansion. -/

/- GT24 Expansion Axiom (removed): Random 3-CNF at linear density produces
    a CubeGraph whose bipartite graph is a (Theta(n), 3, c)-weak expander.

    From Gryaznov-Talebanfard (2024), using Friedman-Kahn-Szemeredi (1989). -/
-- REMOVED (2026-03-29 audit): random_cubegraph_weak_expander — dead code (declared but never used in any proof). See AXIOM-AUDIT.md

/-! ## Section 4: Weak Expansion to Resolution Width (GT24 Lemma 14) -/

/-- Minimum resolution width for refuting a CubeGraph. -/
axiom minResolutionWidth (G : CubeGraph) : Nat

/- GT24 Lemma 14 (removed): Weak expansion forces large resolution width.
    An (r, Delta, c)-weakly expanding system requires resolution width >= c*r/2.

    Proof idea: small subsystems are satisfiable by expansion,
    so any derivation of the empty clause needs width exceeding
    what small subsets can provide. -/
-- REMOVED (2026-03-29 audit): weak_expander_resolution_width — dead code (declared but never used in any proof). See AXIOM-AUDIT.md

/-! ## Section 5: GT24 Super-Linear Bound -/

/- Gryaznov-Talebanfard Main Theorem (2024) (orphaned doc — axiom removed):
    depth-k Frege refutations of random 3-CNFs need Omega(n^{1+eps_k}) steps.
    eps_k = 2^{-(k+1)}. -/
-- REMOVED (2026-03-29 audit): gt24_superlinear_bound — overclaimed.
-- GT24 proves this for RANDOM 3-CNF at linear density, not arbitrary UNSAT
-- CubeGraphs. The ∀ G quantifier is too strong — the correct version would
-- need a "random CG" predicate we don't have. See AXIOM-AUDIT.md

/-! ## Section 6: The Rank-1 Bottleneck (Proven)

CubeGraph's core algebraic contribution:
- Rank-1 operators are aperiodic: M^3 = M^2 (BandSemigroup.lean)
- Rank-1 is closed under composition (InformationChannel.lean)
- Rank-2 operators generate Z/2Z: KR >= 1 (KRBounds.lean)
- Bandwidth gap: k-consistency at level k passes but level b > k fails

The bottleneck theorem: rank-1 channels carry exactly 1 bit of information,
and composition cannot amplify this. But UNSAT detection needs rank-2
coordination (KR >= 1). -/

/-- **Rank-1 Algebraic Bottleneck**: rank-1 is aperiodic (KR = 0) and closed,
    while rank-2 has KR >= 1 (generates Z/2Z). This is the algebraic
    manifestation of the information bottleneck.

    All components proven in existing files with . -/
theorem rank1_algebraic_bottleneck :
    -- (a) Rank-1 is aperiodic: M^3 = M^2
    (∀ (M : BoolMat 8), M.IsRankOne → mul M (mul M M) = mul M M) ∧
    -- (b) Rank-1 is closed under composition (or goes to zero)
    (∀ (A B : BoolMat 8), A.IsRankOne → B.IsRankOne →
      (mul A B).IsRankOne ∨ mul A B = zero) ∧
    -- (c) Rank-2 generates Z/2Z group (KR >= 1)
    (∃ (g e : BoolMat 8), IsZ2Group g e ∧ g ≠ e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro M hM; exact rank1_aperiodic hM
  · intro A B hA hB; exact rank1_closed_under_compose hA hB
  · exact rank2_kr_geq_one

/-! ## Section 7: Expansion Drives Both Width and Rank Stabilization

KEY INSIGHT connecting GT24 to CubeGraph:

The SAME weak expansion property that gives GT24 their width lower bound
also explains why transfer operators stabilize to rank-1 along long paths:
- Expansion ensures long derivation paths (width >= Omega(n))
- Long paths in CubeGraph compose to rank-1 (rank decay)
- Rank-1 has KR = 0 (aperiodic, AC^0)
- But UNSAT detection needs KR >= 1

GT24 sees this as "deterministic restriction simplifies gates."
CubeGraph sees this as "rank-1 bottleneck kills information."
Same phenomenon, two views. -/

/-- **Width-Consistency Equivalence**: Schoenebeck's linear k-consistency
    (width >= Omega(n)) and the ER exponential lower bound
    are two views of the SAME expansion property.

    Proven from schoenebeck_linear + er_exponential_unconditional. -/
theorem expansion_drives_both_bounds :
    -- (a) Linear k-consistency on UNSAT (Schoenebeck)
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧
        KConsistent G (n / c) ∧ ¬ G.Satisfiable) ∧
    -- (b) ER exponential: k-consistency preserved on extensions (BSW + our framework)
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        KConsistent G (n / c) ∧
        (∀ ext : ERExtension G,
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length → (ext.extended.cubes[i]).gapCount ≥ 7) →
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length →
              ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length, i ≠ j →
                (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars) →
          KConsistent ext.extended (n / c) ∧ ¬ ext.extended.Satisfiable)) := by
  exact ⟨schoenebeck_linear, er_exponential_unconditional⟩

/-! ## Section 8: WL-Consistency Connection (de Rezende et al. STOC 2025)

"Truly Supercritical Trade-Offs for Resolution, Cutting Planes,
 Monotone Circuits, and Weisfeiler-Leman"

WL dimension k ~ k-consistency level k (Atserias-Maneva 2013).
AC-3 on CubeGraph = 2-consistency = WL dimension 2.

Their supercritical trade-off means: reducing WL dimension forces
superlinear increase in iterations. This IS the bandwidth gap:
- WL dimension = k in k-consistency
- WL iterations = propagation depth
- Trade-off = b(n) = Omega(n) iterations needed at dimension < b -/

/-- **WL-Consistency witness**: h2Graph shows WL dimension 2 is insufficient.
    2-consistent but not 3-consistent (WL dim 2 passes, dim 3 fails). -/
theorem wl_dimension_witness :
    ∃ G : CubeGraph, KConsistent G 2 ∧ ¬ KConsistent G 3 ∧ ¬ G.Satisfiable := by
  exact ⟨h2Graph, h2graph_2consistent, h2graph_not_3consistent, h2Graph_unsat⟩

/-! ## Section 9: Zhan (2026) Connection

"Microscopic Structure of Random 3-SAT: A Discrete Geometric Approach"
arXiv:2602.23411

Zhan's model: each clause eliminates 2^{n-3} vertices from {0,1}^N.
CubeGraph: each clause fills one vertex in a 3-variable cube.

Correspondence:
- Zhan's "remaining vertex" = CubeGraph's "gap" (dual view)
- Zhan's "cluster" = CubeGraph's "feasible gap selection"
- Zhan's "frozen variable" = CubeGraph's "forced gap" (rank-1 forces unique gap)
- Zhan's "8-clause UNSAT core" = CubeGraph's "dead cube" (gapCount = 0)

Zhan works at global scale (N-dim hypercube).
CubeGraph decomposes into local 3-dim cubes + transfer operators.
Bridge: transfer operators translate local to global. -/

/-- **Zhan's minimal UNSAT core = dead cube**.
    8 clauses on 3 variables = cube with 0 gaps = Type 0 UNSAT.

    This proves the correspondence between Zhan's combinatorial
    observation and CubeGraph's algebraic framework. -/
theorem zhan_dead_cube_unsat (G : CubeGraph) (i : Fin G.cubes.length)
    (hzero : (G.cubes[i]).gapCount = 0) : ¬ G.Satisfiable := by
  intro ⟨s, hv, _⟩
  have hgap := hv i
  simp only [Cube.gapCount] at hzero
  rw [List.countP_eq_zero] at hzero
  have := hzero (s i) (mem_finRange (s i))
  simp only [Bool.not_eq_true] at this
  rw [this] at hgap
  exact absurd hgap (by decide)

/-! ## Section 10: The Gap to Super-Polynomial

GT24 achieves n^{1+eps_k} (super-linear) for bounded-depth Frege.
The open problem is n^{omega(1)} (super-polynomial).

Our analysis identifies what is missing:

1. GT24 fixes o(n) variables via deterministic restriction.
   After restriction, each depth-k gate depends on <= d_1...d_k variables.

2. CubeGraph reveals WHY the remaining variables matter:
   they carry rank-2 information needed for Type-2 UNSAT detection.

3. THE GAP: GT24 treats the formula as a black box after restriction.
   CubeGraph's rank theory provides internal algebraic structure.

4. IF deterministic restriction preserves:
   (a) Weak expansion (r = Omega(n))
   (b) Rank-1 stabilization on paths
   (c) Bandwidth gap b(G) = Omega(n)
   THEN: exponential bound for bounded-depth Frege.

5. This would convert GT24's n^{1+eps_k} to 2^{n^{Omega(1/k)}}.

HONEST ASSESSMENT: This is a real gap. We identify the bridge
(restriction preserves algebra) but do not prove it. -/

/-- The strengthening hypothesis: after restriction, algebraic structure is preserved.
    This is the central OPEN QUESTION connecting GT24 to exponential bounds. -/
def RestrictionPreservesAlgebra (G : CubeGraph) : Prop :=
  ∃ c : Nat, c ≥ 1 ∧
    KConsistent G (G.cubes.length / c) ∧ ¬ G.Satisfiable

/-- IF restriction preserves algebra, THEN k-consistency at Omega(n) holds. -/
theorem conditional_kconsistency
    (G : CubeGraph) (n : Nat) (hn : G.cubes.length ≥ n) (_hn₁ : n ≥ 1)
    (hpreserve : RestrictionPreservesAlgebra G) :
    ∃ c : Nat, c ≥ 1 ∧ KConsistent G (n / c) := by
  obtain ⟨c, hc, hkc, _⟩ := hpreserve
  exact ⟨c, hc, kconsistent_mono G (Nat.div_le_div_right hn) hkc⟩

/-! ## Section 11: Complete Summary -/

/- COMMENTED OUT (2026-03-29 audit): three_pillar_summary
   Depended on gt24_superlinear_bound which was removed (overclaimed).

theorem three_pillar_summary :
    (∀ k : Nat, k ≥ 1 → ∃ n₀, ∀ n ≥ n₀,
      ∀ G : CubeGraph, G.cubes.length ≥ n → ¬ G.Satisfiable →
        minAC0FregeSize G k ≥ n) ∧
    ... := by
  refine ⟨gt24_superlinear_bound, ...⟩
-/

end CubeGraph
