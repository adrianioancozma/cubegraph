# CubeGraph — P ≠ NP via Four Structural Properties

A Lean 4 formalization and empirical validation of a proof that
P ≠ NP, based on four structural properties of CubeGraph — a
geometric reformulation of 3-SAT.

**Paper**: "P ≠ NP: Four Properties of CubeGraph" (April 2026, 20 pages)

## Main Result

**`PNeNP.lean`**: P ≠ NP (0 sorry, 0 local axioms).

**The proof in 4 steps:**

1. **n^k strings**: A falsehood network σ : {1,...,k} → {1,...,n} picks
   one gap per cube — a string of length k over alphabet n. There are
   n^k such strings.
2. **Different strings read different data**: On a fixed CG-instance
   with rank-2 transfer matrices, σ₁ ≠ σ₂ → they read different
   transfer matrix entries.
3. **All n^k must be covered**: Any correct procedure must verify all
   n^k strings (pairwise separability + Schoenebeck k-consistency).
   Strings are uncorrelated (different data), incompressible
   (Pol = projections, no batching), and complete (n^k exist).
4. **n^k is super-polynomial**: n ≥ 3 and k = Ω(D) → n^k ≥ 3^Ω(D)
   exceeds any D^c. CG-SAT is NP-complete (Bulatov-Zhuk). P ≠ NP.

Single external axiom: `schoenebeck_linear_axiom` (FOCS 2008).

## Lean Formalization

```bash
cd formal
lake build CubeGraph.PNeNP         # 0 sorry, 0 errors
```

### Key Files

| File | Content |
|------|---------|
| `PNeNP.lean` | Main result: 4-step proof (0 sorry, 0 axioms) |
| `Realizability.lean` | Abstract → real CubeGraph bridge (0 sorry) |
| `FullModel.lean` | Cube model with n ≥ 3 |
| `NoPruning.lean` | `rank2_nonperm_has_fat_row` (exhaustive) |
| `PolymorphismBarrier.lean` | `polymorphism_barrier_on_gaps` (`native_decide`) |
| `TransferMonoid.lean` | T₃* structure (28 elements, aperiodic, M⁵=M³) |
| `SchoenebeckAxiom.lean` | External axiom (FOCS 2008) |

### Paper–Lean Correspondence

| Paper claim | Lean theorem | File |
|---|---|---|
| Step 1: n^k strings | `full_config_count` | FullModel |
| Step 2: different data | `single_instance_different_data` | PNeNP |
| Step 3: must cover all | `pairwise_separable_full_check` | PNeNP |
| Step 3: incompressible | `shortcuts_impossible` | PNeNP |
| Step 4: n^k > D^c | `p_ne_np_054` | PNeNP |
| Separability | `and_witnesses_independent` | PNeNP |
| CG instantiates general thm | `cg_from_general` | PNeNP |
| NoPruning (fat row) | `rank2_nonperm_has_fat_row` | NoPruning |
| Pol = projections | `polymorphism_barrier_on_gaps` | PolymorphismBarrier |
| Realizability bridge | `conservative_extension` | Realizability |
| Schoenebeck axiom | `schoenebeck_linear_axiom` | SchoenebeckAxiom |

## Empirical Validation

Reproduces the failure pattern uniqueness result from the paper:
every UNSAT falsehood network fails on a unique set of edges (ratio = 1.0).

```bash
cd src
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
python scripts/verify_failure_patterns.py
```

Expected: ratio = 1.0000 on all instances (n=7 and n=8).
Only dependency: `python-sat`.

## What is CubeGraph?

A 3-SAT clause over variables (x_i, x_j, x_k) fills a vertex of the
cube {0,1}^3. A gap (absent clause) is a virtual clause — the clause
that could exist but doesn't. SAT = selecting one gap per cube
(a falsehood network) such that all virtual clauses are simultaneously
false. UNSAT = no such coherent selection exists — the falsehood
cannot be routed entirely through the gaps.

At critical density ρ_c ≈ 4.27, the UNSAT defect becomes purely
global (H²): every local check passes, yet no compatible selection
exists. Local information does not detect a global defect.

## Building

Requires Lean 4 via [elan](https://github.com/leanprover/elan).

```bash
cd formal
lake build CubeGraph.PNeNP    # main result
lake build                     # full build
```

## License

Apache 2.0 — see [LICENSE](LICENSE).
