# Lanțul Demonstrativ P≠NP — Formalizare Lean 4

## Rezultat

**Teoremă (p_ne_np_on_CG_UNSAT)**: Sub 3 ipoteze, orice demonstrație
tree-like Frege a CG-UNSAT are ≥ 2^{n/8} frunze.

```
∃ c ≥ 2, ∀ n ≥ 1, ∃ G : CubeGraph,
  |G.cubes| ≥ n ∧ Element3_Explosion G c
```

**Status**: PROVEN, 0 sorry, 0 axiome locale.

## Fișiere Lean — Lanțul Principal (0 sorry)

| Fișier | Conținut | Sorry |
|--------|----------|-------|
| [FourElements.lean](CubeGraph/FourElements.lean) | Lanțul principal: counting_k2, AMTRO, SEPM, p_ne_np_on_CG_UNSAT | **0** |
| [SensitivityForcing.lean](CubeGraph/SensitivityForcing.lean) | derived_insensitive_to_non_S, substF chain, flipVar, falseLeafIdx helpers | **0** |
| [ExponentialBound.lean](CubeGraph/ExponentialBound.lean) | Infrastructură: ExtFDeriv, falseLeafIdx, botLeafIdx, conjElimBoundedBy | **0** |
| [TransferMonoid.lean](CubeGraph/TransferMonoid.lean) | T₃* definiții, Cayley table, M⁵=M³, native_decide | **0** |
| [PNeNP.lean](CubeGraph/PNeNP.lean) | Lanțul depth collapse (alternativ) | **0** |

## Fișiere Lean — Explorare (cu sorry)

| Fișier | Conținut | Sorry | Docs |
|--------|----------|-------|------|
| [AperiodicNoXOR.lean](CubeGraph/AperiodicNoXOR.lean) | Path 1: direct_exponential_gen, T₃* algebră | 1 | [GAP-ANALYSIS.md](../experiments-ml/051_2026-04-09_independent-set-path/GAP-ANALYSIS.md) |
| [CycleResonance.lean](CubeGraph/CycleResonance.lean) | Path 2: cicluri ca rezonatoare → 2^{D/2} | 5 | [INSIGHT-CYCLES-RESONANCE.md](../experiments-ml/051_2026-04-09_independent-set-path/INSIGHT-CYCLES-RESONANCE.md) |
| [DoubleNetwork.lean](CubeGraph/DoubleNetwork.lean) | Infrastructură rețea dublă, brainstorm | 1 | [BRAINSTORM-DOUBLE-NETWORK.md](../experiments-ml/051_2026-04-09_independent-set-path/BRAINSTORM-DOUBLE-NETWORK.md) |
| [OnlyXOR.lean](CubeGraph/OnlyXOR.lean) | "Only XOR universally sensitive" | 2 | [PLAN-APERIODIC-NO-XOR.md](../experiments-ml/051_2026-04-09_independent-set-path/PLAN-APERIODIC-NO-XOR.md) |
| [XORCounterexample.lean](CubeGraph/XORCounterexample.lean) | Contraexemplu XOR (documentare, circular) | 2 | [GAP-ANALYSIS.md](../experiments-ml/051_2026-04-09_independent-set-path/GAP-ANALYSIS.md) |
| [HunivFromDefect.lean](CubeGraph/HunivFromDefect.lean) | Analiză huniv ca ipoteză | 0 | [ANALYSIS-HUNIV.md](../experiments-ml/051_2026-04-09_independent-set-path/ANALYSIS-HUNIV.md) |

## Cele 3 Ipoteze

### H1: Schoenebeck (axiom publicat — FOCS 2008)
→ Lean: `h_schoenebeck` în [FourElements.lean](CubeGraph/FourElements.lean)

### H2: huniv (sensibilitate universală)
→ Lean: `h_huniv` în [FourElements.lean](CubeGraph/FourElements.lean)
→ Analiză: [ANALYSIS-HUNIV.md](../experiments-ml/051_2026-04-09_independent-set-path/ANALYSIS-HUNIV.md), [HunivFromDefect.lean](CubeGraph/HunivFromDefect.lean)

### H3: SEPM — SingleExtractionPerMP
→ Lean: `h_sepm` în [FourElements.lean](CubeGraph/FourElements.lean)
→ Analiză: [GAP-ANALYSIS.md](../experiments-ml/051_2026-04-09_independent-set-path/GAP-ANALYSIS.md)
→ Tentative de eliminare: [AperiodicNoXOR.lean](CubeGraph/AperiodicNoXOR.lean), [CycleResonance.lean](CubeGraph/CycleResonance.lean)

## Lanțul Demonstrat (0 sorry)

```
p_ne_np_on_CG_UNSAT                     [FourElements.lean]
  → topology_and_choices_imply_explosion [FourElements.lean]
    → exponential_from_single_extraction [FourElements.lean]
      → counting_k2                     [FourElements.lean]
      → derived_insensitive_to_non_S    [SensitivityForcing.lean]
  → nonlocal_makes_explosion_necessary  [FourElements.lean]
```

## Două Căi de Eliminare SEPM

### Calea 1 (Path 1): Var deletion + "only XOR"
→ Lean: [AperiodicNoXOR.lean](CubeGraph/AperiodicNoXOR.lean)
→ Docs: [GAP-ANALYSIS.md](../experiments-ml/051_2026-04-09_independent-set-path/GAP-ANALYSIS.md), [TWO-FORMALIZATION-PATHS.md](../experiments-ml/051_2026-04-09_independent-set-path/TWO-FORMALIZATION-PATHS.md)
→ Status: 1 sorry (K_partial vars nu recuperează huniv)

### Calea 2 (Path 2): Cicluri ca rezonatoare
→ Lean: [CycleResonance.lean](CubeGraph/CycleResonance.lean), [DoubleNetwork.lean](CubeGraph/DoubleNetwork.lean)
→ Docs: [INSIGHT-CYCLES-RESONANCE.md](../experiments-ml/051_2026-04-09_independent-set-path/INSIGHT-CYCLES-RESONANCE.md), [BRAINSTORM-DOUBLE-NETWORK.md](../experiments-ml/051_2026-04-09_independent-set-path/BRAINSTORM-DOUBLE-NETWORK.md)
→ Status: 5 sorry (cycle rank, Schoenebeck → cycles, case split × independent)
→ **Nu depinde de huniv sau SEPM** — pur structural

### Insight cheie: P vs NP = rețea fixă vs rețea suprapusă
→ Docs: [TWO-FORMALIZATION-PATHS.md](../experiments-ml/051_2026-04-09_independent-set-path/TWO-FORMALIZATION-PATHS.md)

## Fapte T₃* (toate PROVEN via native_decide)

→ Lean: [AperiodicNoXOR.lean](CubeGraph/AperiodicNoXOR.lean), [TransferMonoid.lean](CubeGraph/TransferMonoid.lean)

| Teoremă | Fișier |
|---------|--------|
| t3star_no_product_identity | AperiodicNoXOR.lean |
| t3star_square_not_identity | AperiodicNoXOR.lean |
| t3star_composition_irreversible | AperiodicNoXOR.lean |
| t3star_no_identity | TransferMonoid.lean |
| global_stabilization (M⁵=M³) | TransferMonoid.lean |
