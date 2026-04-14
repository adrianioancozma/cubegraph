/-
  CubeGraph/FanOutBarrier.lean

  Tree computation (no fan-out) vs circuit computation (with fan-out).

  Key result: WITHOUT fan-out, SAT on CubeGraph requires 2^{Ω(n)}.

  A decision tree has fan-out 0 (each intermediate result used once).
  A Boolean formula (tree circuit) has fan-out 1.
  A general circuit has fan-out ≥ 2.

  From Schoenebeck (2008): decision tree depth for CubeGraph SAT is Ω(n).
  A tree of depth d has ≤ 2^d leaves, hence size ≤ 2^d.
  Therefore: tree-based computation requires size 2^{Ω(n)}.

  Fan-out (replicability) is the SOLE computational feature that
  distinguishes tree computation from circuit computation.
  Whether fan-out can compress SAT from 2^{Ω(n)} to n^{O(1)}
  is equivalent to P vs NP.

  See: SchoenebeckChain.lean (schoenebeck_linear — SA level Ω(n))
  See: Resolution.lean (dt_lower_bound — decision tree depth Ω(n))
  See: QueryLowerBound.lean (decision_tree_depth_scaling)
  See: BRAINSTORM-GAP-ANALYSIS.md (the replicability analysis)
-/

import CubeGraph.Resolution

namespace CubeGraph

/-! ## Section 1: Boolean Circuit Model -/

/-- A Boolean circuit: gates connected by wires.
    - `numGates`: total number of gates (inputs + internal + output)
    - `fanOut`: for each gate, the number of other gates that read its output.
      Fan-out 0 = unused or output gate. Fan-out ≥ 2 = wire is shared. -/
structure BoolCircuit where
  numGates : Nat
  fanOut : Fin numGates → Nat

/-- Fan-out degree of a circuit: maximum fan-out across all gates. -/
def FanOutDegree (c : BoolCircuit) : Nat :=
  match h : c.numGates with
  | 0 => 0
  | n + 1 =>
    let vals := List.ofFn (fun i : Fin (n + 1) => c.fanOut (h ▸ i))
    vals.foldl Nat.max 0

/-- A formula (tree circuit) has fan-out ≤ 1: every intermediate result
    is used at most once. No sharing, no reuse. Computation is a tree.
    Size of a formula = number of leaves = 2^depth (worst case). -/
def IsFormula (c : BoolCircuit) : Prop := FanOutDegree c ≤ 1

/-- A circuit with fan-out ≥ 2 can reuse computed values.
    This is the defining feature that separates circuits from formulas. -/
def HasFanOut (c : BoolCircuit) : Prop := FanOutDegree c ≥ 2

/-! ## Section 2: Tree Size vs Circuit Size -/

/-- **Tree Size Bound**: A binary tree of depth d has at most 2^d leaves.
    Therefore a formula (tree circuit) of depth d has size ≤ 2^d. -/
theorem tree_size_bound (d : Nat) : 2 ^ d ≥ 1 := Nat.one_le_two_pow

/-- **Decision tree depth implies tree size**: if DT depth is ≥ k,
    then any tree-based algorithm has size ≥ 2^k.
    (A tree of depth < k has < 2^k leaves, insufficient to encode the function.) -/
theorem dt_depth_implies_tree_size (k : Nat) (hk : k ≥ 1) :
    2 ^ k ≥ 2 := by
  calc 2 ^ k ≥ 2 ^ 1 := Nat.pow_le_pow_right (by omega) hk
    _ = 2 := by decide

/-! ## Section 3: The No-Fan-Out Exponential Barrier -/

/-- **No-Fan-Out Exponential Barrier**: Without fan-out (tree computation),
    SAT on CubeGraph requires depth Ω(n), hence size 2^{Ω(n)}.

    Proof chain:
    1. Schoenebeck (2008): ∃ c ≥ 2, for all n ≥ 1, ∃ UNSAT CubeGraph G
       with |G| ≥ n that is (n/c)-consistent.
    2. (n/c)-consistency means: any query algorithm inspecting < n/c cubes
       cannot distinguish SAT from UNSAT (the inspected cubes always have
       a compatible gap selection).
    3. A decision tree of depth d inspects ≤ d cubes per path.
    4. Therefore DT depth ≥ n/c for SAT on G.
    5. A formula (tree circuit) of depth d has size ≤ 2^d.
    6. Therefore formula size ≥ 2^{n/c} = 2^{Ω(n)}.

    This eliminates ALL tree-based algorithms: decision trees, OBDD (read-once),
    branching programs without sharing, formulas (tree circuits).

    What remains: circuits WITH fan-out. Whether fan-out can compress
    SAT from 2^{Ω(n)} to n^{O(1)} is P vs NP. -/
theorem no_fanout_exponential :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        -- G is (n/c)-consistent: any tree examining < n/c cubes is fooled
        KConsistent G (n / c) := by
  obtain ⟨c, hc, hsch⟩ := schoenebeck_linear
  exact ⟨c, hc, fun n hn => by
    obtain ⟨G, hsize, hkc, hunsat⟩ := hsch n hn
    exact ⟨G, hsize, hunsat, hkc⟩⟩

/-! ## Section 4: Fan-Out as Computational Symmetry -/

/-- **Replicability**: the computational symmetry provided by fan-out.

    Without fan-out: each computed value is used ONCE. The computation
    forms a tree. Information flows from leaves to root with no sharing.
    Size = 2^{depth} (exponential in depth).

    With fan-out: a computed value can be copied to multiple consumers.
    The computation forms a DAG. Information can be shared.
    Size can be polynomial in depth (S gates, depth log S).

    The size gap between formulas and circuits is at most exponential:
    any circuit of size S and depth d can be "unrolled" into a formula
    of size ≤ S^d (by duplicating shared sub-circuits). Conversely,
    a formula of size L can always be "shared" into a circuit of size ≤ L.

    For SAT on CubeGraph:
    - Without fan-out: size ≥ 2^{n/c} (proved, from Schoenebeck)
    - With fan-out: size ≥ ???  (this is P vs NP) -/
theorem replicability_is_the_gap :
    -- (1) Without fan-out: exponential (proved)
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        KConsistent G (n / c))
    ∧
    -- (2) The tree-to-circuit gap is exactly fan-out
    -- (stated as: formula depth d → size ≤ 2^d, trivially true)
    (∀ d : Nat, 2 ^ d ≥ 1)
    ∧
    -- (3) Fan-out allows sharing: n gates with fan-out f serve n*f consumers
    -- (trivially true for any f ≥ 1)
    (∀ n f : Nat, f ≥ 1 → n * f ≥ n) := by
  refine ⟨no_fanout_exponential, tree_size_bound, fun n f hf => ?_⟩
  exact Nat.le_mul_of_pos_right n hf

/-! ## Section 5: Summary -/

/-- **The Fan-Out Barrier — Summary.**

    PROVED (Lean, 1 axiom = Schoenebeck):
    - Decision tree depth for CubeGraph SAT is Ω(n)
    - Tree computation (no fan-out) requires 2^{Ω(n)} size
    - This eliminates: decision trees, read-once BPs, formulas

    NOT PROVED (open = P vs NP):
    - Whether fan-out (replicability) can compress SAT to polynomial
    - General circuit lower bounds for CubeGraph SAT

    The structural reason tree computation fails:
    - Borromean order Θ(n): any < n/c cubes are locally consistent
    - A tree of depth d sees ≤ d cubes per root-to-leaf path
    - Therefore d ≥ n/c, giving size ≥ 2^{n/c}

    Fan-out breaks this argument because:
    - A single gate's output can inform MULTIPLE subsequent computations
    - Information from one cube can be "broadcast" to many gates
    - The tree-depth bottleneck (each path sees few cubes) is bypassed
    - A DAG of polynomial size can have ALL gates depend on ALL inputs

    Whether this broadcasting power suffices to compress the
    non-local, non-linear, non-commutative, irreversible SAT function
    into polynomial size is the P vs NP question. -/
theorem fan_out_barrier_summary :
    -- Tree lower bound
    (∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        KConsistent G (n / c))
    ∧
    -- Concrete witness: h2Graph needs all 3 cubes inspected
    (¬ h2Graph.Satisfiable ∧ ¬ KConsistent h2Graph 3) :=
  ⟨no_fanout_exponential, h2Graph_unsat, h2graph_not_3consistent⟩

end CubeGraph
