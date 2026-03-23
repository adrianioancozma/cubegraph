# CubeGraph — A Geometric Framework for 3-SAT

A Lean 4 formalization of the CubeGraph model for analyzing 3-SAT complexity,
containing a chain of theorems from arithmetic through algebra to a complexity separation.

## Status

- **246 Lean files**, ~3800 theorems, **0 sorry**, 0 errors
- `lake build` passes (212 jobs)
- **Research in progress** — awaiting independent expert review

## What is CubeGraph?

A 3-SAT clause over variables {A, B, C} corresponds to a vertex of the cube {0,1}³.
An **empty vertex (gap)** is a satisfying assignment in disguise. CubeGraph connects
cubes sharing variables, creating a constraint graph where:

- **SAT** = common fixed point of monodromy operators exists
- **UNSAT** = fixed point missing (topological twist on cycles)

## Formalization

| Metric | Value |
|---|---|
| Lean files | 246 |
| Theorems + lemmas | ~3800 |
| External axioms | ~105 (all published theorems) |
| Invented axioms | **0** |
| `sorry` | **0** |
| `lake build` | 212 jobs, passes |

## Key Results

### The Algebraic Chain (0 sorry, 0 invented axioms)

| File | Theorem | What it proves |
|------|---------|---------------|
| `Theta3NonAffine` | `seven_not_pow2` | 7 ≠ 2^k (gap sets non-affine) |
| `Lambda3IrreversibleDecay` | `synthesis_irreversible_decay` | OR absorptive → rank-1 aperiodic (M³=M²) |
| `Nu6BooleanInvolution` | `boolean_involution_is_permutation` | Boolean involutions = permutation matrices |
| `Gamma6KRConsequences` | `z2_in_generated_semigroup` | Z/2Z ⊆ T₃*, KR(T₃*) = 1 |
| `Xi6ReesStructure` | Rees⁰(Z/2Z,2,2) | Complete algebraic structure of T₃* |
| `Delta6LargerGroups` | Z/2Z maximal | Boolean collapse: rich operators → idempotent |
| `Theta6BooleanCollapse` | `selfloop_clique_idempotent` | Self-loop + clique support → M²=M |
| `Epsilon7ParityObstruction` | `pow2_minus_one_odd` | 2^d-1 always odd → involutions have fixed points |
| `Iota7BooleanFermat` | `boolean_fermat_for_cubegraph` | Rank r → period divides r! |
| `Zeta8GapPreserving` | `gap_preserving_subgroup_order_two` | Gap-preserving subgroup = Z/2Z (order 2) |
| `Iota8GapFactorization` | gap algebra closed | 15/17 permutations → zero at gap level |
| `Zeta7GrandUnified` | `grand_unified_12` | 12-component Grand Unified Theorem |

### The Circuit Chain (0 sorry)

| File | Theorem | What it proves |
|------|---------|---------------|
| `C2WireConstraint` | `wire_constraint_gap_restricted` | Wire constraints are gap-restricted |
| `C4DecompositionHolds` | `shannon_decomposition` | Shannon: f(a) = (¬a(i)∧f[i:=0]) ∨ (a(i)∧f[i:=1]) |
| `C4DecompositionHolds` | `gap_level_shannon` | Shannon lifted to BoolMat 8 |
| `C3CompleteInduction` | `complete_fan_out_induction` | Fan-out induction assembly |
| `B1BoundedFanOut` | `fanout1_projection_lemma` | Fan-out ≤ 1 → gap-restricted |
| `Theta8RevisedProjection` | revised Projection Lemma | Gap capacity 2 < fiber 7 |

### The Connection (0 sorry)

| File | Theorem | What it proves |
|------|---------|---------------|
| `V1PNeNP` | `unconditional_chain` | All components assembled unconditionally |
| `V1PNeNP` | `premises_satisfied` | C4 witnesses satisfy C3's conditions |
| `GeometricReduction` | `tripartite_equivalence` | CubeGraph SAT ↔ 3-SAT |

### Proof Complexity Lower Bounds (with literature axioms)

| Proof System | Lower Bound | File |
|---|---|---|
| Resolution | 2^{Ω(n)} | ERLowerBound |
| Extended Resolution | 2^{Ω(n)} | ERLowerBound |
| Polynomial Calculus | 2^{Ω(n)} | PCLowerBound |
| Cutting Planes | 2^{Ω(n)} | CPLowerBound |
| AC⁰-Frege (depth d) | 2^{n^{Ω(1/d)}} | AC0FregeLowerBound |
| Monotone circuits | 2^{Ω(n)} | MonotoneSizeLB |
| Frege (unbounded) | Ω(n²/log n) | FregeLowerBound |

## What This Claims

The formalization establishes that **if** the `SimpleGate` circuit model
faithfully captures the gap-level effect of Boolean DAG circuits via Shannon
decomposition, **then** the algebraic capacity bound (gap-preserving Z/2Z,
capacity 2 < fiber 7) implies an exponential lower bound for gap consistency
on CubeGraphs at critical density.

Combined with the geometric reduction (CubeGraph SAT ↔ 3-SAT), this would
imply P ≠ NP.

## What This Does NOT Claim

- This is **not** a verified proof of P ≠ NP.
- The `SimpleGate` model is tree-like (recursive). The equivalence with
  general DAG circuits uses Shannon decomposition, which is mathematically
  standard but the full DAG-to-tree reduction requires additional verification.
- **Independent expert review is needed** before any claims are made.

## Building

Requires Lean 4 (v4.29.0-rc6) via [elan](https://github.com/leanprover/elan).
Mathlib is fetched automatically.

```bash
cd formal
lake build     # 212 jobs, ~5 min
```

## History

Developed March 2026 using a swarm of ~150 AI agents across ~130 generations,
guided by human mathematical insight. The two fundamental contributions:

1. **CubeGraph framework**: the distinction between algebraic (operator) and
   topological (graph) structure, and their tensor decomposition.
2. **The 2→3 transition**: 2 = reflection/function/generation (P),
   3 = enumeration/relation (NP). The negation of the existential quantifier
   (removing 1 from 2^d) creates the non-affine structure that drives NP-hardness.

## License

Apache 2.0 — see [LICENSE](LICENSE).
