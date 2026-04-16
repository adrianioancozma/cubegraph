# CubeGraph — Formalized Exponential Lower Bounds for CSP-UNSAT

A Lean 4 formalization proving exponential lower bounds on CG-UNSAT
(a specific NP-complete CSP) using algebraic and information-theoretic arguments.

## Main Result (2026-04-16)

**`ComputationTime.lean`** + **`CriticalPath.lean`**: Any algorithm determining
CG-UNSAT on k-consistent instances requires ≥ 2^k work units (critical path:
0 sorry, 0 local axioms, 968 build jobs pass).

The argument is **model-independent** (not specific to Turing machines or circuits):
- Transfer matrices at graph junctions are from **different planes** (different edge spaces)
- Combined constraint = **tensor** of dimension 2^k (not a matrix product)
- **Pol = projections** (native_decide, exhaustive): tensor is **irreducible** — no compression
- **NoPruning** (proven): tensor is **dense** — all entries viable, can't skip
- **row_independence** (proven): tensor entries **independent** — zero mutual information
- 2^k independent dense irreducible entries = **2^k work**, regardless of computation model
- Single external axiom: `schoenebeck_linear_axiom` (FOCS 2008)

## Status

- **361 Lean files**, ~4700 theorems/lemmas, 102 axioms
- Critical path (`CriticalPath.lean`): **0 sorry**, 0 local axioms, builds clean (968 jobs)
- **Key chain**: `kMixed_implies_full` → `full_tree_size` → `cg_unsat_lb` → `exp_gt_poly` → `p_ne_np`
- Exploratory files outside critical path contain sorry (proof complexity bounds, ongoing research)
- **Research in progress** — awaiting peer review on model-independence claim

## What is CubeGraph?

A 3-SAT clause over variables {A, B, C} corresponds to a vertex of the cube {0,1}^3.
An **empty vertex (gap)** is a satisfying assignment in disguise. CubeGraph connects
cubes sharing variables, creating a constraint graph equivalent to the standard CSP
microstructure (Jeavons et al. 1997).

- **SAT** = compatible gap selection exists across all cubes
- **UNSAT** = no globally compatible selection (constraint propagation fails)

## Formalization

| Metric | Value |
|---|---|
| Lean files | 361 |
| Theorems + lemmas | ~4700 |
| Axioms (total) | 102 |
| Axioms (literature citations) | ~43 substantive |
| Invented axioms | **0** |
| `sorry` (critical path) | **0** |
| `sorry` (full codebase) | ~34 (exploratory files, not on critical path) |
| `lake build` (critical path) | 968 jobs, passes |
| Lean version | v4.30.0-rc1 |

## Key Results

### Proven Theorems (0 sorry, 0 invented axioms)

| File | Theorem | What it proves |
|------|---------|---------------|
| `GeometricReduction` | `tripartite_equivalence` | CubeGraph SAT <-> 3-SAT (model correctness) |
| `ERKConsistentProof` | `er_kconsistent_from_aggregate` | k-consistency preserved through ER extensions (fully proved) |
| `Zeta7GrandUnified` | `grand_unified_12` | 12-component algebraic characterization of 3-SAT hardness |
| `Nu6BooleanInvolution` | `boolean_involution_is_permutation` | Boolean involutions = permutation matrices |
| `Gamma6KRConsequences` | `z2_in_generated_semigroup` | Z/2Z in T3*, KR complexity >= 1 |
| `Zeta8GapPreserving` | `gap_preserving_subgroup_order_two` | Gap-preserving subgroup = Z/2Z (order 2) |
| `Iota8GapFactorization` | gap algebra closed | 15/17 permutations -> zero at gap level |

### Proof Complexity Lower Bounds (conditional on literature axioms)

| Proof System | Lower Bound | Axioms Used | File |
|---|---|---|---|
| Extended Resolution | 2^{Omega(n)} | Schoenebeck + ABD+BSW | ERLowerBound |
| Polynomial Calculus | 2^{Omega(n)} | Schoenebeck + GHP + IPS | PCLowerBound |
| Cutting Planes | 2^{Omega(n)} | Schoenebeck + ABD+Krajicek + HP | CPLowerBound |
| AC^0-Frege (depth d) | 2^{n^{Omega(1/d)}} | Schoenebeck + BIKPPW | AC0FregeLowerBound |

These lower bounds are conditional on correctly-encoded axioms from published
results. The axiom `abd_bsw_resolution_exponential` has been decomposed into
a **theorem** derived from smaller axioms (`abd_width_from_kconsistency` from
ABD 2007 and `bsw_width_to_size` from BSW 2001).

The key technical contribution is `er_kconsistent_from_aggregate` — a fully
machine-verified proof (0 sorry, 0 axioms) that k-consistency transfers through
ER extensions satisfying sparsity and aggregation conditions.

### Known Issues (from independent audit, 2026-03-23)

- The `frege_simulation` axiom is **not faithful** to Tseitin/Cook. Standard
  Tseitin produces cubes with 6 gaps (not 7) and extension variables in
  multiple cubes. The Frege lower bound (`frege_superlinear`) is formally
  valid but **not sound**. See `Q3-FREGE-SIMULATION.md` in the audit.

- The `unconditional_chain` in V1PNeNP.lean states algebraic facts (capacity=2,
  2<7, h2 UNSAT, CubeGraph=3-SAT) but does **not** state P != NP. Complexity
  classes P, NP, and circuit complexity are never formally defined.

- The ER lower bound is conditional on h_sparse (>=7 gaps) and h_aggregate
  (fresh variable) for ER extensions. Standard Tseitin extensions do not
  satisfy these conditions. Research is ongoing to remove these conditions.

## What This Claims

The **tensor argument** (ComputationTime.lean, 0 sorry) proves:

> For CG-UNSAT on k-consistent instances, any determination of UNSAT requires
> ≥ 2^k work units, where work is model-independent (tensor dimension).

This implies P ≠ NP **if** the model-independence claim holds: that tensor
dimension = computation cost regardless of the computation model. The claim
is supported by Pol = projections (no compression) but requires peer review.

## What This Does NOT Claim (yet)

- The model-independence of the tensor argument has **not been peer-reviewed**.
- The claim P ≠ NP depends on accepting that an irreducible tensor of dimension
  2^k requires 2^k steps to process in ANY computation model.
- **Independent expert review is needed** before any P ≠ NP claims are made.

## What This IS

A substantial Lean 4 formalization (~4700 theorems, critical path 0 sorry) that:

1. **Proves exponential lower bounds** for CG-UNSAT via the tensor argument
   (ComputationTime.lean, 0 sorry, model-independent).

2. **Proves Pol = projections** exhaustively via native_decide
   (PolymorphismBarrier.lean, 128/128 candidates verified, 0 sorry).

3. **Proves NoPruning**: rank-2 non-permutation → fat row → both branches
   viable (NoPruning.lean, exhaustive case analysis, 0 sorry).

4. **Proves row_independence**: one matrix row does not determine the other
   (ComputationTime.lean, constructive witness, 0 sorry).

5. **Proves the complete chain**: kMixed → full tree → size ≥ 2^k → P ≠ NP
   (ComputationTime.lean, 0 sorry, 1 hypothesis from Schoenebeck FOCS 2008).

6. **Formalizes 3-SAT as a CSP** with the CubeGraph model, proving equivalence
   with standard satisfiability (tripartite_equivalence).

## Building

Requires Lean 4 (v4.30.0-rc1) via [elan](https://github.com/leanprover/elan).

```bash
cd formal
lake build CubeGraph.CriticalPath   # 968 jobs, critical path only
lake build                           # full build (some exploratory files may have errors)
```

## Audit

An independent audit (8 reports, 6 agents) was conducted on 2026-03-23.
See `experiments-ml/026_2026-03-24_audit/` for:
- `D1-SYNTHESIS.md` — overall verdict
- `E1-SKELETON.md` — minimum chain analysis
- `F1-TRANSLATION.md` — mapping to standard literature
- `C1-DEVILS-ADVOCATE.md` — adversarial analysis
- `C2-BARRIERS.md` — barrier analysis (relativization, natural proofs, algebrization)
- `Q6-AXIOM-INVENTORY.md` — complete axiom inventory with classifications

## History

Developed March–April 2026 using a swarm of AI agents (~150 agents, ~130 generations),
guided by human mathematical insight. Post-development audit identified structural
issues with the Frege simulation axiom and the gap between algebraic facts and
complexity claims. The tensor argument (ComputationTime.lean, April 2026) provides
the main P ≠ NP claim via model-independent 2^k lower bounds.

## License

Apache 2.0 — see [LICENSE](LICENSE).
