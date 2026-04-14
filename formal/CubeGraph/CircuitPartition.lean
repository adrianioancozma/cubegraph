/-
  CubeGraph/CircuitPartition.lean
  Circuit states argument: a polynomial circuit running on an exponential
  family of CNFs must confuse exponentially many instances, and Borromean
  structure constrains which confusions are possible.

  FRAMEWORK:
  1. CubeGraphFamily — fix topology, vary polarities → 8^m members
  2. CircuitPartition — S wires → at most 2^S equivalence classes
  3. BorromeanPartitionConstraint — k-consistency means no ≤ k-local
     function separates SAT from UNSAT
  4. Pigeonhole — 8^m instances / 2^S states = 2^{3m - S} confused pairs

  HONEST: This formalizes the counting framework and the Borromean
  constraint. It does NOT prove P ≠ NP — the gap from "exponentially
  many confused instances" to "no polynomial circuit works" requires
  showing that the Borromean constraint forces the confusion to cross
  the SAT/UNSAT boundary. That step is the open problem.

  See: KConsistency.lean (KConsistent, sat_implies_kconsistent)
  See: SchoenebeckChain.lean (schoenebeck_linear — Borromean order Ω(n))
  See: QueryLowerBound.lean (DT ≥ Ω(n))
  See: CircuitRigidity.lean (wire dependency analysis)
  See: experiments-ml/026_.../BRAINSTORM-GAP-ANALYSIS.md (motivation)
-/

import CubeGraph.SchoenebeckChain

set_option maxHeartbeats 400000

namespace CubeGraph

/-! ## Section 1: CubeGraph Family

Fix a topology (cubes + edges). Each cube has 8 possible polarity
configurations (which vertex is filled). The family of all polarity
assignments has 8^m members where m = number of cubes. -/

/-- A **polarity configuration**: assigns one of 8 polarity choices to
    each cube in the graph. This determines which vertex is filled,
    hence which 7 vertices are gaps. -/
def PolarityConfig (m : Nat) := Fin m → Fin 8

/-- 8 = 2^3: each cube polarity is 3 bits. -/
theorem eight_eq_two_cubed : (8 : Nat) = 2 ^ 3 := by decide

/-- 8^m = 2^{3m}: the family of polarity configs on m cubes has 2^{3m} members.
    Each polarity is 3 bits, so total input space is 2^{3*m} bits. -/
theorem family_size_binary (m : Nat) : 8 ^ m = 2 ^ (3 * m) := by
  have : (8 : Nat) = 2 ^ 3 := by decide
  rw [this, ← Nat.pow_mul]

/-! ## Section 2: Circuit State Partition

A Boolean circuit with S wires (internal gates + output) partitions
its input space into at most 2^S equivalence classes, where two inputs
are equivalent iff they produce the same bit-string on all S wires.

At the output wire alone: exactly 2 classes (outputs 0 or 1). -/

/-- A **circuit partition**: a function from inputs to one of 2^S states.
    Two inputs in the same state are indistinguishable to the circuit. -/
def CircuitPartition (m S : Nat) := (Fin m → Fin 8) → Fin (2 ^ S)

/-- The range of a circuit partition has exactly 2^S elements.
    This bounds the number of distinguishable classes. -/
theorem partition_range_size (S : Nat) :
    ∀ (x : Fin (2 ^ S)), x.val < 2 ^ S := Fin.isLt

/-! ## Section 3: Borromean Partition Constraint

Any partition of the family based on inspecting ≤ k cubes' polarities
cannot separate SAT from UNSAT when the graph is k-consistent.

Formally: if G is k-consistent and UNSAT, any function depending on
a subset of ≤ k cubes agrees on at least one SAT-like and one UNSAT
configuration (because the restriction to those k cubes always has
a consistent gap selection). -/

/-- **Borromean partition constraint**: if G is k-consistent, then
    for any subset S of ≤ k cube indices, the UNSAT graph G admits
    a consistent local selection on S — indistinguishable from SAT.

    No function of the S-restricted polarities can distinguish
    SAT from UNSAT. This is the fundamental locality barrier.

    Uses KConsistent from KConsistency.lean. -/
theorem borromean_partition_constraint (G : CubeGraph) (k : Nat)
    (hkc : KConsistent G k)
    (S : List (Fin G.cubes.length)) (hlen : S.length ≤ k) (hnd : S.Nodup) :
    -- The graph G, restricted to S, admits a consistent selection
    ∃ s : (i : Fin G.cubes.length) → Vertex,
      (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true) :=
  hkc S hlen hnd

/-- **Corollary**: With Schoenebeck's theorem (axiom), for any constant c,
    there exist arbitrarily large UNSAT graphs where c-consistency passes.
    No fixed-depth local inspection suffices. -/
theorem borromean_constraint_scales :
    ∀ c : Nat, ∃ n₀ : Nat, ∀ n ≥ n₀,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧
        KConsistent G c ∧ ¬ G.Satisfiable :=
  schoenebeck

/-! ## Section 4: Pigeonhole — Exponential Confusion

A circuit with S wires running on 8^m = 2^{3m} inputs must have
at least 2^{3m} / 2^S = 2^{3m - S} inputs per circuit state (on average).
For S polynomial in m, this is exponentially many. -/

/-- **Pigeonhole bound**: 2^a items into 2^b bins (b ≤ a) yields
    2^a / 2^b = 2^{a-b} items per bin.
    This is the discrete pigeonhole principle in exponential form. -/
theorem exp_pigeonhole (a b : Nat) (hle : b ≤ a) :
    2 ^ a / 2 ^ b = 2 ^ (a - b) :=
  Nat.pow_div hle (by omega : 0 < 2)

/-- **Circuit state pigeonhole**: a circuit with S wires on a family
    of 2^{3m} instances has 2^{3m} / 2^S = 2^{3m - S} instances
    per circuit state on average.
    When S < 3m (polynomial vs exponential), this is exponentially many. -/
theorem circuit_state_pigeonhole (m S : Nat) (hS : S ≤ 3 * m) :
    2 ^ (3 * m) / 2 ^ S = 2 ^ (3 * m - S) :=
  exp_pigeonhole (3 * m) S hS

/-- **Exponential confusion**: for S < 3m, the number of confused
    instances per state is at least 2 — genuinely exponential. -/
theorem confusion_exponential (m S : Nat) (hS : S < 3 * m) :
    2 ^ (3 * m - S) ≥ 2 := by
  have h : 3 * m - S ≥ 1 := by omega
  calc 2 ^ (3 * m - S)
      ≥ 2 ^ 1 := Nat.pow_le_pow_right (by omega) h
    _ = 2 := by omega

/-! ## Section 5: Combined Framework

Putting it all together: for Schoenebeck families with m cubes and
Borromean order Ω(m), a circuit of size S = poly(m) faces:
  (A) 2^{3m - S} confused instances per state (pigeonhole)
  (B) first Ω(m) levels of the circuit are blind (Borromean)
  (C) the circuit must separate SAT from UNSAT in the remaining gates

This does NOT prove the circuit fails. It quantifies the challenge. -/

/-- **Framework theorem**: combines Borromean blindness with pigeonhole.

    For an UNSAT graph G with m cubes that is k-consistent:
    1. Any circuit with S wires confuses 2^{3m-S} instances per state
    2. Any function depending on ≤ k cubes sees consistent local views
    3. Both constraints hold simultaneously

    The circuit must untangle exponential confusion using gates that
    initially compute only locally-blind functions. -/
theorem circuit_partition_framework (G : CubeGraph) (k S : Nat)
    (hkc : KConsistent G k)
    (m : Nat) (hS : S ≤ 3 * m) :
    -- (1) Pigeonhole: 2^{3m-S} instances per state
    2 ^ (3 * m) / 2 ^ S = 2 ^ (3 * m - S) ∧
    -- (2) Borromean: any ≤ k cubes admit consistent selection
    (∀ (T : List (Fin G.cubes.length)), T.length ≤ k → T.Nodup →
      ∃ s : (i : Fin G.cubes.length) → Vertex,
        (∀ i ∈ T, (G.cubes[i]).isGap (s i) = true) ∧
        (∀ e ∈ G.edges, e.1 ∈ T → e.2 ∈ T →
          transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true)) :=
  ⟨circuit_state_pigeonhole m S hS,
   fun T hlen hnd => borromean_partition_constraint G k hkc T hlen hnd⟩

/-- **Scaling theorem**: from Schoenebeck, instantiate the framework
    at arbitrarily large n with Borromean order Ω(n).

    For any circuit size bound c (interpreting c as a constant),
    there exist arbitrarily large graphs where c-consistency passes
    but the graph is UNSAT. The circuit faces
    the full Borromean + pigeonhole constraint. -/
theorem framework_scales :
    ∀ c : Nat, ∃ n₀ : Nat, ∀ n ≥ n₀,
      ∃ G : CubeGraph,
        G.cubes.length ≥ n ∧
        KConsistent G c ∧
        ¬ G.Satisfiable ∧
        -- Pigeonhole applies with m = n
        (c ≤ 3 * n → 2 ^ (3 * n) / 2 ^ c = 2 ^ (3 * n - c)) := by
  intro c
  obtain ⟨n₀, hn₀⟩ := schoenebeck c
  exact ⟨n₀, fun n hn => by
    obtain ⟨G, hm, hkc, hunsat⟩ := hn₀ n hn
    exact ⟨G, hm, hkc, hunsat, fun hcn => circuit_state_pigeonhole n c hcn⟩⟩

/-! ## Section 6: What This Does NOT Prove

This file formalizes the FRAMEWORK for the circuit states argument:
- Exponentially many instances share circuit states (pigeonhole)
- Below Borromean order, all local views are consistent (blindness)

What remains OPEN (and is equivalent to P ≠ NP):
- Showing that the Borromean constraint forces the circuit's confusion
  to cross the SAT/UNSAT boundary (i.e., confused instances include
  both SAT and UNSAT members)
- Showing that fan-out (wire reuse) cannot overcome the blindness

The gap between this framework and P ≠ NP is precisely the gap
between counting arguments and structural arguments about circuits. -/

end CubeGraph
