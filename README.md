# CubeGraph — A Geometric Framework for 3-SAT

A Lean 4 formalization of the CubeGraph model for analyzing 3-SAT complexity.

## What is CubeGraph?

A 3-SAT clause over variables {A, B, C} corresponds to a vertex of the cube {0,1}³. An **empty vertex (gap)** is a satisfying assignment in disguise. CubeGraph connects cubes sharing variables, creating a constraint graph where:

- **SAT** = common fixed point of monodromy operators exists
- **UNSAT** = fixed point missing (topological twist on cycles)

## Formalization

| Metric | Value |
|---|---|
| Lean files | 82 |
| Theorems + lemmas | ~604 |
| Definitions | ~230 |
| External axioms | 11 (all published theorems) |
| `sorry` | **0** |
| Lines of code | ~15,500 |

### Key Results (all 0 sorry)

- `geometric_reduction` — CubeGraph SAT ↔ 3-SAT ↔ GeoSAT (tripartite equivalence)
- `cycle_trace_iff_satisfiable` — SAT on cycle ↔ trace of monodromy operator
- `channel_alignment` — rank-1 cycle SAT ↔ channel alignment at every node
- `information_bottleneck` — 11-component capstone: rank decay + Borromean + information gap
- `fixed_point_gap_summary` — P = Knaster-Tarski on trees, NP = fixed point missing on cycles
- `symmetry_and_its_breaking` — Z₂³ symmetry broken irreversibly by OR (1+1=1)
- `monotone_size_exponential` — monotone circuit SIZE ≥ n^{Ω(n)}
- `borromean_not_ac0` — Borromean detection ∉ AC⁰ (two independent proofs)
- `no_wnu3_preserves_neq3` — no Taylor polymorphism (CSP NP-completeness)
- `er_auxiliary_summary` — ER auxiliary variables individually blind

### Eliminated Algorithm Classes (formally proven)

1. **AC⁰** — rank-1 = aperiodic = KR complexity 0
2. **ACC⁰** — ℤ/3ℤ has no fixed point on H² witness
3. **SA / k-consistency / SOS** — Schoenebeck barrier (exponential)
4. **Monotone circuits** — SIZE ≥ n^{Ω(n)} (BSW + GGKS)
5. **C_local** — boolean composition barrier (6 components)
6. **Rank-1 protocols** — blind below Borromean order Θ(n)

### External Axioms (11 total)

All are published theorems from the complexity theory literature:

| Axiom | Source |
|---|---|
| `schoenebeck` | Schoenebeck 2008 — SOS degree lower bounds |
| `schoenebeck_linear` | Schoenebeck 2008 — linear form |
| `braverman_polylog_fools_ac0` | Braverman 2010 — polylog fools AC⁰ |
| `gpw_lifting` | Göös-Pitassi-Watson 2018 — CC → circuit depth |
| `kw_cc_equals_depth` | Karchmer-Wigderson 1990 |
| `bsw_resolution_width` | Ben-Sasson-Wigderson 2001 |
| `ggks_width_to_monotone_size` | Garg-Göös-Kamath-Sousa 2020 |
| `abd_ad_consistency_implies_high_width` | Atserias-Bulatov-Dalmau 2007 |
| `petke_jeavons_consistency_eq_hyperres` | Petke-Jeavons 2011 |
| `berkholz_propagation_depth` | Berkholz 2012 |
| `bsw_on_cubegraph` | Ben-Sasson-Wigderson on CubeGraph |

## Building

Requires [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.28.0) via [elan](https://github.com/leanprover/elan).

```bash
cd formal
lake build
```

## Structure

```
formal/
├── CubeGraph/           — 82 theorem files
│   ├── Basic.lean        — Core definitions (Cube, CubeGraph, transferOp, Satisfiable)
│   ├── BoolMat.lean      — Boolean matrix algebra (OR/AND semiring)
│   ├── Monodromy.lean    — SAT ↔ fixed point of monodromy
│   ├── TreeSAT.lean      — Acyclic + AC → SAT (Knaster-Tarski)
│   ├── FlatBundleFailure.lean  — H² twist on cycles
│   ├── InformationBottleneckComplete.lean  — Capstone theorem
│   └── ...
├── CubeGraph.lean        — Module root
├── lakefile.toml         — Lake build configuration
└── lean-toolchain        — Lean version
```

## License

Apache 2.0 — see [LICENSE](LICENSE).
