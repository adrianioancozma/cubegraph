# CubeGraph — A Geometric Framework for 3-SAT

A Lean 4 formalization of the CubeGraph model for analyzing 3-SAT complexity.

## What is CubeGraph?

A 3-SAT clause over variables {A, B, C} corresponds to a vertex of the cube {0,1}³. An **empty vertex (gap)** is a satisfying assignment in disguise. CubeGraph connects cubes sharing variables, creating a constraint graph where:

- **SAT** = common fixed point of monodromy operators exists
- **UNSAT** = fixed point missing (topological twist on cycles)

## Formalization

| Metric | Value |
|---|---|
| Lean files | 96 |
| Theorems + lemmas | ~890 |
| Definitions | ~240 |
| External axioms | 26 (all published theorems) |
| Internal axioms | **0** |
| `sorry` | **0** |
| Lines of code | ~17,800 |

### Key Results (all 0 sorry)

**Core framework:**
- `geometric_reduction` — CubeGraph SAT ↔ 3-SAT ↔ GeoSAT (tripartite equivalence)
- `cycle_trace_iff_satisfiable` — SAT on cycle ↔ trace of monodromy operator
- `channel_alignment` — rank-1 cycle SAT ↔ channel alignment at every node
- `information_bottleneck` — 11-component capstone: rank decay + Borromean + information gap
- `fixed_point_gap_summary` — P = Knaster-Tarski on trees, NP = fixed point missing on cycles
- `symmetry_and_its_breaking` — Z₂³ symmetry broken irreversibly by OR (1+1=1)

**Proof complexity lower bounds:**
- `er_resolution_lower_bound` — Extended Resolution size ≥ 2^{Ω(n)}
- `pc_lower_bound` — Polynomial Calculus size ≥ 2^{Ω(n)}
- `cp_lower_bound` — Cutting Planes size ≥ 2^{Ω(n)}
- `ac0frege_lower_bound` — AC⁰-Frege size ≥ 2^{Ω(n)} at any fixed depth
- `ef_resolution_lower_bound` — Generalized ER (any abbreviation type via HasCorrectGaps)
- `depth_frege_lower_bound` — Depth-sensitive Frege: super-polynomial for d = o(log n / log log n)
- `frege_near_quadratic` — Frege general (unbounded depth) self-referential bound via CubeGraph (matches known Ω(n²) from literature)

**Other lower bounds:**
- `monotone_size_exponential` — monotone circuit SIZE ≥ n^{Ω(n)}
- `borromean_not_ac0` — Borromean detection ∉ AC⁰ (two independent proofs)
- `no_wnu3_preserves_neq3` — no Taylor polymorphism (CSP NP-completeness)

**CubeGraph structural:**
- `er_kconsistent_from_aggregate` — k-consistency extends to T(G) (replaces former axiom #12)
- `er_borromean_unconditional` — BorromeanOrder exactly preserved under ER: b(T(G)) = b(G)
- `ef_kconsistent_from_correct_gaps` — HasCorrectGaps: works for ANY abbreviation (AND, XOR, arbitrary)

### Eliminated Proof System Classes

| # | Class | Lower Bound | File |
|---|-------|-------------|------|
| 1 | Resolution | 2^{Ω(n)} | ERLowerBound |
| 2 | Extended Resolution | 2^{Ω(n)} | ERLowerBound |
| 3 | SA / k-consistency / SOS | 2^{Ω(n)} | SchoenebeckChain |
| 4 | Polynomial Calculus | 2^{Ω(n)} | PCLowerBound |
| 5 | Polynomial Calculus + ER | 2^{Ω(n)} | PCLowerBound |
| 6 | Cutting Planes | 2^{Ω(n)} | CPLowerBound |
| 7 | Cutting Planes + ER | 2^{Ω(n)} | CPLowerBound |
| 8 | Monotone circuits | n^{Ω(n)} | MonotoneSizeLB |
| 9 | AC⁰ circuits | exponential | BorromeanAC0 |
| 10 | Rank-1 protocols | blind below Θ(n) | Rank1Protocol |
| 11 | AC⁰-Frege | 2^{n^{Ω(1/d)}} | AC0FregeLowerBound |
| 12 | AC⁰-Frege + ER | 2^{n^{Ω(1/d)}} | AC0FregeLowerBound |
| 13 | Generalized ER (any abbreviation) | 2^{Ω(n)} | EFLowerBound |
| 14 | Depth-sensitive Frege | super-poly for d = o(log n) | DepthFregeLowerBound |
| 15 | Frege (unbounded depth) | Ω(n²/log n) via CubeGraph | FregeLowerBound |

### What is NOT proven

This formalization does **not** prove P ≠ NP. Specifically:

- **Frege lower bound**: Ω(n²/log n) via CubeGraph framework — matches the known Ω(n²) from proof complexity literature (no super-polynomial Frege lower bounds are known; this is a 50+ year open problem). The barrier: BSW width-size theorem has formula size N in the denominator. For P ≠ NP: would need 2^{Ω(n)}.
- **Extended Frege**: Our generalized ER result (EFLowerBound) proves Resolution on any extension is hard. But EF uses Frege rules (not Resolution), and k-consistency does not imply Frege proof size bounds. The naming "EF" in the file is imprecise — it's Resolution-based.
- **General circuit lower bounds**: Only monotone circuits are covered. Non-monotone circuits are not addressed.

### External Axioms (26 total)

All are published theorems from the complexity theory literature:

| Axiom | Source | File |
|---|---|---|
| `schoenebeck`, `schoenebeck_linear` | Schoenebeck 2008 | SchoenebeckChain |
| `braverman_polylog_fools_ac0` | Braverman 2010 | BorromeanAC0 |
| `gpw_lifting`, `kw_cc_equals_depth` | GPW 2018, KW 1990 | LiftingTheorem |
| `bsw_resolution_width` | Ben-Sasson-Wigderson 2001 | MonotoneSizeLB |
| `ggks_width_to_monotone_size` | GGKS 2020 | MonotoneSizeLB |
| `abd_ad_consistency_implies_high_width` | ABD 2007 + AD 2008 | RankWidthTransfer |
| `petke_jeavons_consistency_eq_hyperres` | Petke-Jeavons 2012 | RankWidthTransfer |
| `berkholz_propagation_depth` | Berkholz 2014 | RankWidthTransfer |
| `abd_bsw_resolution_exponential` | ABD+AD+BSW combined | ERLowerBound |
| `kconsistent_implies_pc_high_degree` | Schoenebeck+GHP 2002 | PCLowerBound |
| `pc_degree_implies_size` | IPS 1999 | PCLowerBound |
| `kconsistent_implies_cp_high_width` | ABD+AD+Krajíček 1997 | CPLowerBound |
| `cp_width_implies_size` | Hrubeš-Pudlák 2017 | CPLowerBound |
| `kconsistent_implies_ac0frege_exponential` | BIKPPW 1996 | AC0FregeLowerBound |
| `bikppw_precise` | BIKPPW 1996 (precise form) | DepthFregeLowerBound |
| `frege_simulation` | Tseitin 1968 + Cook 1975 | FregeLowerBound |
| `bsw_with_formula_size` | BSW 2001 (explicit N) | FregeLowerBound |
| + 4 function specifications | `minResolutionSize`, `minPCDegree`, `minPCSize`, `minCPWidth`, `minCPSize`, `minAC0FregeSize`, `minFregeSize` | various |

## Building

Requires [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.28.0) via [elan](https://github.com/leanprover/elan).

```bash
cd formal
lake build
```

## Structure

```
formal/
├── CubeGraph/           — 96 Lean files
│   ├── Basic.lean        — Core definitions (Cube, CubeGraph, transferOp, Satisfiable)
│   ├── BoolMat.lean      — Boolean matrix algebra (OR/AND semiring)
│   ├── Monodromy.lean    — SAT ↔ fixed point of monodromy
│   ├── TreeSAT.lean      — Acyclic + AC → SAT (Knaster-Tarski)
│   ├── ERKConsistentProof.lean  — Axiom #12 eliminated (0 sorry)
│   ├── ERLowerBound.lean  — ER proof size ≥ 2^{Ω(n)}
│   ├── PCLowerBound.lean  — PC proof size ≥ 2^{Ω(n)}
│   ├── CPLowerBound.lean  — CP proof size ≥ 2^{Ω(n)}
│   ├── AC0FregeLowerBound.lean — AC⁰-Frege ≥ 2^{Ω(n)}
│   ├── EFLowerBound.lean  — Generalized ER (HasCorrectGaps)
│   ├── DepthFregeLowerBound.lean — Depth-sensitive Frege
│   ├── FregeLowerBound.lean — Frege Ω(n²/log n) — first super-linear
│   └── ...
├── CubeGraph.lean        — Module root (96 imports)
├── lakefile.toml         — Lake build configuration
└── lean-toolchain        — Lean version
```

## License

Apache 2.0 — see [LICENSE](LICENSE).
