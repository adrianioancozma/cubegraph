# CubeGraph — A Lean 4 Formalization of 3-SAT Proof Complexity

A Lean 4 formalization of the CubeGraph model for analyzing 3-SAT structure,
with conditional proof complexity lower bounds for Resolution, Extended Resolution,
Polynomial Calculus, Cutting Planes, and bounded-depth Frege.

## Status

- **249 Lean files**, ~3800 theorems, **0 sorry**, 0 errors
- `lake build` passes (216 jobs)
- **91 axioms** (all citing published results; 22 function specs, remainder are
  standard literature citations from Schoenebeck 2008, BSW 2001, ABD 2007, etc.)
- **Research in progress** — awaiting independent expert review

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
| Lean files | 249 |
| Theorems + lemmas | ~3800 |
| Axioms (total) | 91 |
| Axioms (literature citations) | ~43 substantive |
| Axioms (function specs) | 22 |
| Axioms (duplicates) | 10 |
| Invented axioms | **0** |
| `sorry` | **0** |
| `lake build` | 216 jobs, passes |

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

## What This Does NOT Claim

- This is **not** a proof of P != NP.
- This is **not** a verified super-linear Frege lower bound (the axiom is unsound).
- The algebraic chain (capacity < fiber) is a collection of true algebraic facts
  that do not imply a complexity separation without additional formalization.
- The `SimpleGate` / `CircuitGapProjection` bridge is a **placeholder** (returns
  BoolMat.zero). The gap between algebraic structure and circuit complexity is
  not formalized.
- **Independent expert review is needed** before any claims are made.

## What This IS

A substantial Lean 4 formalization (~3800 theorems, 0 sorry) that:

1. **Formalizes 3-SAT as a CSP** with the CubeGraph model, proving equivalence
   with standard satisfiability (tripartite_equivalence).

2. **Analyzes the algebraic structure** of boolean transfer operators (Krohn-Rhodes
   complexity, boolean collapse, gap-preserving subgroup analysis).

3. **Proves conditional proof complexity lower bounds** for ER, PC, CP, and
   AC^0-Frege, using literature axioms that cite specific published results.

4. **Fully proves k-consistency transfer** through ER extensions
   (er_kconsistent_from_aggregate, 0 sorry, 0 axioms).

5. **Identifies precisely** where the gap lies between algebraic structure and
   circuit/proof complexity, including a detailed analysis of why the Tseitin
   simulation fails to satisfy the sparsity conditions.

## Building

Requires Lean 4 (v4.29.0-rc6) via [elan](https://github.com/leanprover/elan).

```bash
cd formal
lake build     # 216 jobs, ~5 min
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

Developed March 2026 using a swarm of AI agents (~150 agents, ~130 generations),
guided by human mathematical insight. Post-development audit identified structural
issues with the Frege simulation axiom and the gap between algebraic facts and
complexity claims. Axiom cleanup reduced count from 105 to 91 (17 tautological
axioms converted to theorems, 3 dead-code axioms deleted, 1 monolithic axiom
decomposed into focused sub-axioms).

## License

Apache 2.0 — see [LICENSE](LICENSE).
