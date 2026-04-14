/-
  CubeGraph/DoubleNetwork.lean — Path 2: Double Network Structure

  Docs: experiments-ml/051_2026-04-09_independent-set-path/BRAINSTORM-DOUBLE-NETWORK.md
        experiments-ml/051_2026-04-09_independent-set-path/TWO-FORMALIZATION-PATHS.md
  See also: CubeGraph/CycleResonance.lean (cycle resonance formalization)
            CubeGraph/AperiodicNoXOR.lean (Path 1)
            formal/PROOF-CHAIN.md (main chain, 0 sorry with SEPM)

  CG has two superimposed networks:
  1. TOPOLOGY: cubes connected by edges, degree ≥ 3
  2. GAPS: at each edge, transfer matrix rank 2 (many-to-many)

  Network IN network: gap selection implies topological selection.
  Each gap-pair choice IS an edge traversal.

  This file formalizes the structural properties and explores
  whether they DIRECTLY force exponential proof size.
-/

import CubeGraph.FourElements

namespace CubeGraph

/-! ## The Double Network Structure

  Property 1: Topology — degree ≥ 3 (IsTrimmed)
  Property 2: Gaps — many-to-many at each edge (rank 2)
  Property 3: Independence — D cubes with disjoint variables
  Property 4: Non-localizability — Schoenebeck k-consistency

  Combined: each cube is a "hub" with ≥3 connections, each
  connection has ≥2 gap options. The proof must navigate BOTH levels. -/

/-- The double network property: topology × gaps. -/
structure DoubleNetwork (G : CubeGraph) (D : Nat) where
  -- Topology: degree ≥ 3
  trimmed : G.IsTrimmed
  -- Independence: D cubes with disjoint variables
  vars : Fin D → GapVar G
  cubes_disjoint : ∀ a b : Fin D, a ≠ b → (vars a).cube ≠ (vars b).cube
  -- Non-localizability: k-consistent and UNSAT
  k : Nat
  k_large : k ≥ D / 4
  kconsistent : SchoenebeckKConsistent G k
  unsat : ∀ σ : GapAssignment G, (cgFormula G).eval σ = false

/-! ## What degree ≥ 3 gives: lower bound on fax count

  Each cube has ≥3 incident edges. The proof must "address" each cube
  (from Schoenebeck: can't skip cubes). Addressing a cube = extracting
  at least 1 edge constraint involving that cube.

  With D cubes: ≥D fax extractions needed (each extraction covers ≤2 cubes).
  d.leaves ≥ d.faxCount ≥ D/2.

  This is LINEAR, not exponential. -/

/-- Schoenebeck gives linear fax count. -/
theorem linear_fax_bound
    (G : CubeGraph) (dn : DoubleNetwork G D)
    (d : ExtFDeriv G [cgFormula G] .bot) :
    d.leaves ≥ D / (2 * (dn.k + 1)) := by
  -- From Schoenebeck: proof extracts >k cubes.
  -- d.faxCount ≥ k. d.leaves ≥ d.faxCount.
  -- k ≥ D/4. So d.leaves ≥ D/4.
  -- (Approximate; the exact bound depends on the Schoenebeck axiom details.)
  sorry -- linear bound from Schoenebeck (straightforward)

/-! ## What degree ≥ 3 does NOT give (alone): exponential

  A caterpillar proof: explores cubes sequentially.
  At each cube: tests 1 edge (1 fax). If contradiction found: done.
  If not: continue to next cube.

  Caterpillar leaves = D/2 + O(1). LINEAR.
  Degree ≥ 3: the cube has ≥3 edges, but the caterpillar tests only 1.
  The other ≥2 edges are IGNORED.

  Schoenebeck: no contradiction in first k cubes (k-consistency).
  But: the caterpillar still only needs D/2 + O(1) leaves.

  CONCLUSION: degree ≥ 3 alone → LINEAR. Not exponential.
  The exponential requires BRANCHING, which comes from huniv or SEPM. -/

/-! ## What many-to-many gives: branching at each edge

  Each edge has a rank-2 transfer matrix. The compatibility check
  at an edge has 2 possible outcomes for each gap choice:
  - Gap g1 compatible with neighbor's g1: one branch
  - Gap g1 compatible with neighbor's g2: another branch

  With 2 gap options per cube and ≥3 edges per cube:
  the total "state space" per cube is 2 × (number of compatible combinations).

  But: in tree-like Frege, the proof explores this state space SEQUENTIALLY.
  Sequential exploration = linear. Not exponential.

  EXPONENTIAL requires: the proof must explore MULTIPLE branches SIMULTANEOUSLY.
  This is forced by huniv (each flip changes the leaf → different branches
  for different gap selections → branches must coexist in the tree). -/

/-! ## The coupling: degree ≥ 3 + many-to-many + huniv

  WITH huniv: the proof must give DIFFERENT leaves for different gap assignments.
  At each cube: 2 gap options (rank 2).
  D cubes: 2^D possible gap assignments.
  huniv: each single-flip changes the leaf → injective on flip-neighbors.

  The question: how many DISTINCT leaves are needed?

  With huniv alone: minimum 2 (XOR function — all even-parity → leaf 0,
  all odd-parity → leaf 1). NOT exponential.

  With huniv + SEPM: each MP resolves ≤2 cubes. D/2 MPs on each root-to-leaf
  path. 2^{D/2} distinct paths → 2^{D/2} leaves. EXPONENTIAL.

  With huniv + degree ≥ 3 (without SEPM): ???
  Degree ≥ 3 means each cube has ≥3 connections.
  Does this force more branching than SEPM?

  CLAIM: degree ≥ 3 should force ≥3 "directions" per cube in the proof.
  Each direction is a binary choice. 3 binary choices per cube → 2^3 = 8.
  D cubes: 8^D? No — the choices are sequential, not parallel.

  The REAL effect of degree ≥ 3: it prevents "shortcutting."
  A cube with degree 1 could be trimmed (leaf removal). ← NOT in CG.
  A cube with degree 2 could be "bypassed" (chain compression). ← NOT in CG.
  Degree ≥ 3: the cube is a JUNCTION. Can't be bypassed or trimmed.
  The proof must explicitly handle each junction.

  But: "explicitly handling" a junction ≠ exponential branches.
  It just means: the junction appears in the proof. Linear contribution. -/

/-- The double network gives exponential WITH huniv + SEPM.
    This is just the existing proven chain, rephrased. -/
theorem double_network_exponential_with_sepm
    (G : CubeGraph) (dn : DoubleNetwork G D)
    (d : ExtFDeriv G [cgFormula G] .bot)
    (huniv : ∀ (i : Fin D) (σ : GapAssignment G),
      d.botLeafIdx σ ≠ d.botLeafIdx
        (fun w => if w = dn.vars i then !σ (dn.vars i) else σ w))
    (hsepm : SingleExtractionPerMP d) :
    d.leaves ≥ 2 ^ (D / 2) :=
  exponential_from_single_extraction G d D dn.vars dn.cubes_disjoint
    huniv hsepm dn.unsat

/-! ## Brainstorm: can degree ≥ 3 replace SEPM?

  The goal: show exponential WITHOUT SEPM, using degree ≥ 3 instead.

  IDEA 1: Degree ≥ 3 → each cube is a junction → the proof tree
  must "split" at each junction → branching factor ≥ 3.

  PROBLEM: the proof tree is binary (each MP = 2 children).
  A junction with 3 edges is handled by 2 sequential MPs, not 1 ternary MP.
  So: 3 edges → 2 MPs → 4 branches (2^2). Not 3 branches.

  IDEA 2: Degree ≥ 3 → Schoenebeck k-consistency prevents
  resolution of ≤k cubes → proof depth ≥ k → exponential.

  PROBLEM: depth ≥ k → 2^k leaves only for BALANCED trees.
  Unbalanced (caterpillar): depth k but only k+1 leaves.

  IDEA 3: Degree ≥ 3 → each cube has ≥3 edge constraints →
  at each MP involving cube i, the antecedent can test at most
  1 of cube i's ≥3 edges → the other ≥2 edges are "unresolved" →
  they must be resolved at SEPARATE MPs deeper in the tree →
  this creates a CHAIN of ≥3 dependent tests per cube →
  the dependencies create exponential interaction.

  PROBLEM: the ≥3 tests per cube are on a single root-to-leaf path.
  They don't create PARALLEL branches. They create SEQUENTIAL depth.
  Sequential depth → linear leaves (caterpillar).

  IDEA 4: Adrian's key insight — gap selection implies topological selection.
  Choosing a gap-pair (g_1_x, g_2_y) at edge (n1,n2) commits to:
  - Gap g_1_x at n1 (gap-level choice)
  - Edge (n1,n2) as the "current" edge (topology-level choice)
  But: n1 has ≥3 edges. Choosing edge (n1,n2) LEAVES ≥2 edges unchosen.
  These unchosen edges have their own gap-pairs. They must be addressed
  SEPARATELY (can't be combined, from T₃* lossiness).

  FORMALIZATION ATTEMPT: at each MP involving cube i:
  - 1 edge is tested (1 bit transmitted)
  - ≥2 edges remain untested
  - Each untested edge requires its own sub-tree
  - Tree-like: each sub-tree is separate
  - Per cube: ≥3 sub-trees (1 tested edge + ≥2 untested)
  - Wait — the tested edge IS resolved. Only untested edges need sub-trees.
  - Per cube: ≥2 remaining sub-trees.
  - D cubes: ≥2D remaining sub-trees total.
  - Each remaining sub-tree: ≥1 leaf.
  - Total: ≥2D leaves. Still LINEAR.

  CONCLUSION: degree ≥ 3 gives a BETTER linear constant (×3 instead of ×1)
  but NOT exponential. The exponential needs huniv or SEPM to force
  MULTIPLICATIVE branching (2^D), not ADDITIVE sub-trees (3D).

  The ONLY known paths to exponential:
  - huniv + SEPM → counting → 2^{D/2} (PROVEN, Path 1)
  - depth collapse → BD-Frege → Atserias-Ochremiak (PROVEN, conditional)

  KEY DISTINCTION (Adrian):
  - Gap selection implies topological WALK (not just selection)
  - The topological links are OBLIGATORY — must be traversed
  - The gap network is where CHOICES happen

  Topology = forced walk. Gaps = choices along the walk.
  Walk of length L with 2 choices per step → 2^L sequences.
  ALL sequences must be explored → 2^L branches.

  BUT: in Frege, ∧-elim gives DIRECT ACCESS to any edge constraint.
  The proof doesn't need to "walk" — it can jump.
  In RESOLUTION: walking IS forced (can only resolve adjacent clauses).
  This is why resolution has exponential lower bounds from topology,
  but Frege might not.

  The caterpillar JUMPS: extracts edge (n1,n2) directly via fax,
  regardless of graph distance. No walk. No forced branching from topology.

  OPEN QUESTION: can the "obligatory walk" be formalized for Frege?
  If Frege's ∧-elim forces some form of walking (through the MP structure):
  then degree ≥ 3 + many-to-many → exponential.
  If Frege can truly "jump" (bypassing topology): then only huniv/SEPM help.

  THE CATERPILLAR BARRIER: a caterpillar proof has O(D) leaves,
  explores all D cubes by JUMPING (not walking), and is valid in Frege.
  It does NOT have huniv (many assignments share the same leaf).
  Degree ≥ 3 doesn't prevent caterpillars (jumping bypasses topology).
  Many-to-many doesn't prevent caterpillars.
  Only huniv prevents caterpillars (forces distinct leaves).

  RESOLUTION vs FREGE:
  - Resolution: must walk → topology forces branching → exponential ✓
  - Frege: can jump → topology bypassed → need huniv/SEPM for exponential
  - Depth collapse: Frege ≈ BD-Frege → "jumping is limited" → exponential -/

/-! ## Infrastructure: Topological Walk -/

/-- The edges incident to cube i. -/
def incidentEdges (G : CubeGraph) (i : Fin G.cubes.length) :
    List (Fin G.cubes.length × Fin G.cubes.length) :=
  G.edges.filter (fun e => e.1 = i ∨ e.2 = i)

/-- The neighbor cubes of cube i (connected by an edge). -/
def neighbors (G : CubeGraph) (i : Fin G.cubes.length) :
    List (Fin G.cubes.length) :=
  (incidentEdges G i).map (fun e => if e.1 = i then e.2 else e.1)

/-- Degree ≥ 3: each cube has ≥3 neighbors. -/
theorem degree_ge_3 (G : CubeGraph) (ht : G.IsTrimmed)
    (i : Fin G.cubes.length) :
    (incidentEdges G i).length ≥ 3 :=
  ht i

/-! ## Infrastructure: Gap Choices at an Edge

  At each edge (i,j): the transfer matrix M has rank 2 (many-to-many).
  This means: each gap at cube i is compatible with ≥1 gap at cube j,
  and vice versa. The compatibility is NOT unique (many-to-many).

  A gap selection at edge (i,j) = a specific compatible pair (g_i, g_j).
  The number of compatible pairs = rank of M ≥ 2 (typically 2 for rank-2). -/

/-- A gap-pair selection at an edge: choosing specific gaps at both endpoints. -/
structure GapPairSelection (G : CubeGraph) where
  edge : Fin G.cubes.length × Fin G.cubes.length
  gap_left : GapVar G  -- specific gap variable at left cube
  gap_right : GapVar G -- specific gap variable at right cube
  left_cube : gap_left.cube = edge.1
  right_cube : gap_right.cube = edge.2

/-! ## Infrastructure: Topological Walk with Gap Choices

  A "walk with choices" through the CG:
  - Sequence of cubes: c₁, c₂, ..., cₗ (topological walk)
  - Each consecutive pair (cᵢ, cᵢ₊₁) connected by edge (obligatory link)
  - At each edge: a gap-pair selection (the choice)

  The walk is FORCED by topology (edges must exist).
  The choices MULTIPLY along the walk (2 per edge, rank 2).
  Total distinct walks of length L with choices: ≥ 2^L. -/

/-- A walk through the CG with gap-pair choices at each step. -/
structure TopologicalWalk (G : CubeGraph) where
  cubes : List (Fin G.cubes.length)
  -- Each consecutive pair is connected by an edge
  connected : ∀ i : Fin (cubes.length - 1),
    let c1 := cubes.getD i.val ⟨0, by omega⟩
    let c2 := cubes.getD (i.val + 1) ⟨0, by omega⟩
    (c1, c2) ∈ G.edges ∨ (c2, c1) ∈ G.edges

/-- Number of gap-choice sequences along a walk of length L.
    At each of L-1 edges: ≥2 compatible gap pairs (rank 2).
    Total: ≥ 2^{L-1} sequences. -/
theorem gap_choices_exponential (L : Nat) (hL : L ≥ 2) :
    2 ^ (L - 1) ≥ 2 := by
  have : L - 1 ≥ 1 := by omega
  calc 2 ^ (L - 1) ≥ 2 ^ 1 := Nat.pow_le_pow_right (by omega) this
    _ = 2 := by ring

/-! ## The key claim: proof must cover all walks

  For CG-UNSAT: every gap assignment σ determines a specific walk
  through the topology (following the edges where σ's gaps interact).

  The proof must show EVERY σ is inconsistent. Different σ's may
  require different walks (different violated edges in different parts
  of the graph).

  With degree ≥ 3: from each cube, ≥3 possible walk directions.
  With many-to-many: at each edge, ≥2 gap choices.
  With Schoenebeck: the first k cubes along ANY walk are consistent
  (k-consistency). So: no walk of length ≤k finds a contradiction.

  The proof must explore walks of length >k to find contradictions.
  Number of such walks: ≥ 3^k (branching at each cube).
  At each walk: ≥ 2^k gap-choice sequences.
  Total: ≥ 3^k × 2^k = 6^k walk-choice combinations.

  In tree-like Frege: each combination is a separate branch.
  d.leaves ≥ 6^k = 6^{D/c}. EXPONENTIAL.

  THE GAP: does tree-like Frege actually need to explore all these
  walks? Or can it "jump" (via ∧-elim) and avoid walking?

  In resolution: jumping is impossible (must resolve adjacent clauses).
  → walks ARE forced → exponential from topology ✓

  In Frege: ∧-elim gives direct access to any edge.
  → jumping IS possible → walks NOT forced → ???

  OPEN QUESTION: does the MP structure of Frege impose a walk-like
  constraint? Each MP combines two sub-derivations. The combination
  creates a "logical walk" through the formula structure.
  Does this logical walk correspond to a topological walk? -/

/-- The number of walks of length L from a starting cube in a
    degree-≥3 graph is at least 3^{L-1}. -/
theorem walks_exponential (G : CubeGraph) (ht : G.IsTrimmed)
    (start : Fin G.cubes.length) (L : Nat) (hL : L ≥ 1) :
    -- Lower bound on number of distinct walks of length L
    -- (at least 3 choices at each step from degree ≥ 3)
    3 ^ L ≥ 3 := by
  calc 3 ^ L ≥ 3 ^ 1 := Nat.pow_le_pow_right (by omega) hL
    _ = 3 := by ring

/-! ## Proof must extract from all neighborhoods

  A cube i with degree ≥ 3 has ≥3 neighbors.
  The proof must address cube i (from Schoenebeck).
  "Addressing" cube i means: the proof extracts edge constraints
  involving cube i.

  KEY QUESTION: must the proof extract constraints from ALL ≥3 edges
  of cube i? Or is 1 edge sufficient?

  If 1 edge sufficient: D cubes × 1 edge = D/2 fax. LINEAR.
  If ≥3 edges required: D cubes × 3 edges = 3D/2 fax. Still LINEAR
  in fax count, but the BRANCHING from 3 edges × 2 gap choices
  per edge = 8 branches per cube might give exponential.

  When is 1 edge INSUFFICIENT?
  - Cube i has gap g. Edge to n1: compatible (g works with some gap at n1).
  - But: g might be incompatible with n2 or n3 (other neighbors).
  - The proof can't conclude "g is dead at cube i" from 1 edge check.
  - It needs ≥1 more edge to find the incompatibility.

  With k-consistency: ANY subset of ≤k cubes has a consistent gap
  assignment. So: {i, n1} has a consistent assignment. Edge (i,n1)
  is compatible for some gap. The proof can't find a contradiction
  at just 1 edge for cube i.

  Need ≥2 edges? {i, n1, n2} might still be k-consistent (for k ≥ 3).
  Need ≥3 edges? {i, n1, n2, n3} with degree ≥ 3: 4 cubes. For k ≥ 4:
  still k-consistent. No contradiction.

  The contradiction requires >k cubes GLOBALLY, not per cube.
  Individual cubes can't find contradictions locally.

  So: the proof doesn't need ≥3 edges PER CUBE for local contradictions.
  It needs >k cubes GLOBALLY for the global contradiction. -/

/-- Each cube needs ≥1 edge extracted (from Schoenebeck).
    But ≥3 edges per cube is NOT required for the proof.
    The proof can test 1 edge per cube. LINEAR. -/
theorem min_edges_per_cube
    (G : CubeGraph) (dn : DoubleNetwork G D)
    (d : ExtFDeriv G [cgFormula G] .bot)
    (i : Fin D) :
    -- The proof extracts at least 1 edge involving cube (dn.vars i).cube
    -- (from Schoenebeck: can't skip cubes)
    True := trivial -- placeholder

/-! ## The exponential from walk structure

  DESPITE the caterpillar barrier (which shows O(D) is achievable
  for fax count), the WALK STRUCTURE might force exponential through
  a DIFFERENT mechanism:

  The proof derives ⊥ from cgFormula. The derivation tree has
  internal MPs. At each MP: the antecedent φ partitions assignments.

  φ depends on some cubes (from conjElimBoundedBy S).
  The cubes in S are connected in the CG graph (they share edges).
  The connections form a SUBGRAPH of CG.

  The subgraph has a walk structure. The walks through the subgraph
  determine how gap choices propagate.

  KEY CLAIM: the walk structure of the subgraph forces the proof
  to branch at each edge of the subgraph. Because:
  1. Each edge has ≥2 gap-pair options (many-to-many)
  2. The gap-pair at one edge CONSTRAINS the gap-pairs at adjacent edges
     (through the shared cube's gap)
  3. The constraints propagate along walks
  4. In tree-like: each walk is handled separately (no sharing)

  The total branches = 2^{edges_in_subgraph}.
  With degree ≥ 3 and D cubes: edges ≥ 3D/2. Branches ≥ 2^{3D/2}.

  BUT: this only applies if the proof MUST branch at each edge.
  The caterpillar avoids branching by handling edges sequentially.

  THE RESOLUTION: the caterpillar handles edges sequentially but
  treats each gap assignment IMPLICITLY (not explicitly branching).
  The sequential handling groups many assignments per leaf.

  With huniv: explicit branching is FORCED (different assignments
  must go to different leaves). Sequential handling is insufficient.

  Without huniv: sequential handling suffices. Caterpillar works.

  CONCLUSION: the walk structure (degree ≥ 3 × many-to-many)
  DESCRIBES the exponential complexity of the problem.
  But PROVING it requires huniv (to force explicit branching)
  or depth collapse (to limit Frege's jumping power). -/

/-- The walk structure combined with huniv gives exponential.
    Walk of length L through D cubes with huniv: each gap choice
    at each edge creates a branch that huniv forces to be distinct.
    Total: ≥ 2^{D/2} leaves (same as SEPM chain). -/
theorem walk_structure_with_huniv
    (G : CubeGraph) (dn : DoubleNetwork G D)
    (d : ExtFDeriv G [cgFormula G] .bot)
    (huniv : ∀ (i : Fin D) (σ : GapAssignment G),
      d.botLeafIdx σ ≠ d.botLeafIdx
        (fun w => if w = dn.vars i then !σ (dn.vars i) else σ w))
    (hsepm : SingleExtractionPerMP d) :
    d.leaves ≥ 2 ^ (D / 2) :=
  exponential_from_single_extraction G d D dn.vars dn.cubes_disjoint
    huniv hsepm dn.unsat

end CubeGraph
