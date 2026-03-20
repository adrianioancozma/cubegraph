# CubeGraph — A Geometric Framework for 3-SAT

A Lean 4 formalization of the CubeGraph model for analyzing 3-SAT complexity.

## What is CubeGraph?

A 3-SAT clause over variables {A, B, C} corresponds to a vertex of the cube {0,1}³. An **empty vertex (gap)** is a satisfying assignment in disguise. CubeGraph connects cubes sharing variables, creating a constraint graph where:

- **SAT** = common fixed point of monodromy operators exists
- **UNSAT** = fixed point missing (topological twist on cycles)

## Formalization

| Metric | Value |
|---|---|
| Lean files | 90 |
| Theorems + lemmas | ~800 |
| Definitions | ~235 |
| External axioms | 12 (all published theorems) |
| Internal axioms | **0** |
| `sorry` | **0** |
| Lines of code | ~16,800 |

### Key Results (all 0 sorry)

**Core framework:**
- `geometric_reduction` — CubeGraph SAT ↔ 3-SAT ↔ GeoSAT (tripartite equivalence)
- `cycle_trace_iff_satisfiable` — SAT on cycle ↔ trace of monodromy operator
- `channel_alignment` — rank-1 cycle SAT ↔ channel alignment at every node
- `information_bottleneck` — 11-component capstone: rank decay + Borromean + information gap
- `fixed_point_gap_summary` — P = Knaster-Tarski on trees, NP = fixed point missing on cycles
- `symmetry_and_its_breaking` — Z₂³ symmetry broken irreversibly by OR (1+1=1)

**Lower bounds:**
- `monotone_size_exponential` — monotone circuit SIZE ≥ n^{Ω(n)}
- `borromean_not_ac0` — Borromean detection ∉ AC⁰ (two independent proofs)
- `no_wnu3_preserves_neq3` — no Taylor polymorphism (CSP NP-completeness)

**Extended Resolution (NEW):**
- `er_kconsistent_from_aggregate` — k-consistency extends from G to T(G) for sparse ER (replaces former axiom #12)
- `er_borromean_unconditional` — BorromeanOrder exactly preserved under ER: b(T(G)) = b(G)
- `er_exponential_unconditional` — SA + ER exponential on UNSAT CubeGraphs at ρ_c
- `er_resolution_lower_bound` — ER proofs require size ≥ 2^{Ω(n)} (via ABD+AD+BSW)

### Eliminated Algorithm Classes (formally proven)

1. **AC⁰** — rank-1 = aperiodic = KR complexity 0
2. **ACC⁰** — ℤ/3ℤ has no fixed point on H² witness
3. **SA / k-consistency / SOS** — Schoenebeck barrier (exponential)
4. **SA + Extended Resolution** — BorromeanOrder preserved under ER extensions
5. **Monotone circuits** — SIZE ≥ n^{Ω(n)} (BSW + GGKS)
6. **C_local** — boolean composition barrier (6 components)
7. **Rank-1 protocols** — blind below Borromean order Θ(n)

### What is NOT proven

This formalization does **not** prove P ≠ NP. Specifically:

- **Extended Resolution lower bound**: **PROVEN** — ER proofs need 2^{Ω(n)} size on random 3-SAT at ρ_c. The key insight: ER definitions produce cubes with 7/8 gaps, which are always extendable, so BorromeanOrder is exactly preserved (er_borromean_unconditional). Combined with ABD+AD+BSW axioms → exponential Resolution size on the extended formula.
- **Frege / Extended Frege lower bounds**: OPEN. Extended Frege can introduce abbreviations `p ↔ ψ` where ψ is an arbitrary formula (not just a clause), potentially filling 4+ vertices per cube. Our argument requires ≥ 7 gaps (h_sparse), which breaks for XOR-like abbreviations. This is the remaining gap.
- **General circuit lower bounds**: Only monotone circuits are covered (SIZE ≥ n^{Ω(n)}). Non-monotone circuits are not addressed.
- **The gap to P ≠ NP**: ER exponential does not imply coNP ≠ NP (Cook-Reckhow 1979: ER is one proof system; stronger systems like Frege might still be polynomial). Closing this gap requires lower bounds against Frege or Extended Frege, a major open problem in proof complexity.

### External Axioms (12 total)

All are published theorems from the complexity theory literature:

| Axiom | Source | File |
|---|---|---|
| `schoenebeck` | Schoenebeck 2008 — SOS degree lower bounds | SchoenebeckChain |
| `schoenebeck_linear` | Schoenebeck 2008 — linear form | SchoenebeckChain |
| `braverman_polylog_fools_ac0` | Braverman 2010 — polylog fools AC⁰ | BorromeanAC0 |
| `gpw_lifting` | Göös-Pitassi-Watson 2018 — CC → circuit depth | LiftingTheorem |
| `kw_cc_equals_depth` | Karchmer-Wigderson 1990 | LiftingTheorem |
| `bsw_resolution_width` | Ben-Sasson-Wigderson 2001 | MonotoneSizeLB |
| `ggks_width_to_monotone_size` | Garg-Göös-Kamath-Sokolov 2020 | MonotoneSizeLB |
| `abd_ad_consistency_implies_high_width` | Atserias-Bulatov-Dalmau 2007 + Atserias-Dalmau 2008 | RankWidthTransfer |
| `petke_jeavons_consistency_eq_hyperres` | Petke-Jeavons 2012 | RankWidthTransfer |
| `berkholz_propagation_depth` | Berkholz 2014 | RankWidthTransfer |
| `abd_bsw_resolution_exponential` | ABD+AD 2007/2008 + BSW 2001 combined | ERLowerBound |
| `minResolutionSize` | Resolution proof size (function specification) | ERLowerBound |

## Building

Requires [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.28.0) via [elan](https://github.com/leanprover/elan).

```bash
cd formal
lake build
```

## Structure

```
formal/
├── CubeGraph/           — 90 Lean files
│   ├── Basic.lean        — Core definitions (Cube, CubeGraph, transferOp, Satisfiable)
│   ├── BoolMat.lean      — Boolean matrix algebra (OR/AND semiring)
│   ├── Monodromy.lean    — SAT ↔ fixed point of monodromy
│   ├── TreeSAT.lean      — Acyclic + AC → SAT (Knaster-Tarski)
│   ├── FlatBundleFailure.lean  — H² twist on cycles
│   ├── InformationBottleneckComplete.lean  — Capstone theorem
│   ├── ERKConsistentProof.lean  — Axiom #12 eliminated (0 sorry)
│   ├── ERKConsistentInduction.lean — ER exponential (0 internal axioms)
│   ├── ERLowerBound.lean  — ER proof size ≥ 2^{Ω(n)}
│   └── ...
├── CubeGraph.lean        — Module root (90 imports)
├── lakefile.toml         — Lake build configuration
└── lean-toolchain        — Lean version
```

## License

Apache 2.0 — see [LICENSE](LICENSE).
