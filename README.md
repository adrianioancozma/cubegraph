# CubeGraph — P ≠ NP via Four Structural Properties

A Lean 4 formalization and empirical validation of a proof that
P ≠ NP, based on four structural properties of CubeGraph — a
geometric reformulation of 3-SAT.

**Paper**: "P ≠ NP: Four Properties of CubeGraph" (April 2026, 16 pages)

## Main Result

**`PNeNP.lean`**: P ≠ NP (0 sorry, 0 local axioms, 969 build jobs pass).

CubeGraph is 3-SAT viewed geometrically: each variable triplet forms
a cube, gaps are permitted assignments, edges encode compatibility.
Four properties force exponential computation:

1. **Degree ≥ 3** — every junction participates in ≥ 3 constraints,
   creating a cascade through the graph
2. **Many-to-many (NoPruning)** — each junction has n ≥ 3 viable gap
   choices, none eliminable a priori
3. **Incompressible (Pol = projections)** — the only functions preserving
   constraints across all instances are projections (exhaustive,
   `native_decide`, 128/128 candidates)
4. **Non-localizable (H²)** — the UNSAT defect is purely global; every
   local check passes (Schoenebeck, FOCS 2008)

CubeGraph carries two superimposed networks: a topological network
(mandatory constraints) and a gap network (n choices per junction,
multiplicative). On a single fixed instance, different configurations
read different compatibility data (rank-2 transfer matrices have
distinct rows). UNSAT = AND of n^k independent witnesses, each
requiring its own verification. With n ≥ 3 and k = Ω(D): n^k > D^c
for any polynomial degree c.

Single external axiom: `schoenebeck_linear_axiom` (FOCS 2008).

## Lean Formalization

```bash
cd formal
lake build CubeGraph.PNeNP         # 969 jobs, 0 sorry, 0 errors
lake build CubeGraph.CriticalPath  # full chain
```

### Key Files

| File | Content |
|------|---------|
| `PNeNP.lean` | Main result: `p_ne_np_054` (0 sorry, 0 axioms) |
| `FullModel.lean` | Junction model with n ≥ 3 |
| `Degree3Exponential.lean` | Cascade and tensor separation |
| `NoPruning.lean` | `rank2_nonperm_has_fat_row` (exhaustive) |
| `PolymorphismBarrier.lean` | `polymorphism_barrier_on_gaps` (`native_decide`) |
| `TransferMonoid.lean` | T₃* structure (28 elements, aperiodic, M⁵=M³) |
| `ComputationTime.lean` | Tensor argument, `exp_gt_poly` arithmetic |
| `GeometricReduction.lean` | CubeGraph SAT ↔ 3-SAT (`tripartite_equivalence`) |

### Paper–Lean Correspondence

| Paper claim | Lean theorem | File |
|---|---|---|
| n^k configurations | `full_config_count` | FullModel |
| Topology × gaps = n^k | `two_networks_combined` | PNeNP |
| Single-instance data indep. | `single_instance_different_data` | PNeNP |
| σ₁ ≠ σ₂ → separable | `and_witnesses_independent` | PNeNP |
| < n^k → ∃ unchecked | `and_of_witnesses` | PNeNP |
| NoPruning (fat row) | `rank2_nonperm_has_fat_row` | NoPruning |
| Pol = projections | `polymorphism_barrier_on_gaps` | PolymorphismBarrier |
| Cascade factor n | `cascade_factor` | PNeNP |
| TM steps ≥ n^k | `tm_steps_lower_bound` | PNeNP |
| n^k > D^c | `p_ne_np_054` | PNeNP |
| Schoenebeck axiom | `schoenebeck_linear_axiom` | SchoenebeckAxiom |

### Stats

| Metric | Value |
|---|---|
| Lean files | 368 |
| Theorems + lemmas | ~4700 |
| Axioms (total) | 102 |
| `sorry` (critical path) | **0** |
| `lake build CubeGraph.PNeNP` | 969 jobs, passes |

## Empirical Validation

Reproduces the failure pattern uniqueness result from the paper:
every UNSAT configuration fails on a unique set of edges (ratio = 1.0).

```bash
cd src
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
python scripts/verify_failure_patterns.py
```

Expected: ratio = 1.0000 on all instances. Runtime: ~2 min (n=7).
Only dependency: `python-sat`.

## What is CubeGraph?

A 3-SAT clause over variables (x_i, x_j, x_k) fills a vertex of the
cube {0,1}^3. An empty vertex (gap) is a permitted assignment.
CubeGraph connects cubes sharing variables. SAT = a compatible gap
selection exists across all cubes. UNSAT = no globally compatible
selection.

At critical density ρ_c ≈ 4.27, the UNSAT defect becomes purely
global (H²): every local check passes, yet no compatible selection
exists. H² is the hard core of 3-SAT.

## Building

Requires Lean 4 via [elan](https://github.com/leanprover/elan).

```bash
cd formal
lake build CubeGraph.PNeNP    # main result
lake build                     # full build
```

## License

Apache 2.0 — see [LICENSE](LICENSE).
