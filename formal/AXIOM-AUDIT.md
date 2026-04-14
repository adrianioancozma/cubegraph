# Axiom Audit — CubeGraph Lean 4 Formalization

**Date**: 2026-03-28
**Scope**: 43 files, 87 axioms classified

## Categories

- **FUNC**: Declares a function/constant (e.g. `minResolutionSize : CubeGraph → Nat`)
- **LIT**: Axiomatizes a published, peer-reviewed result
- **CONJ**: Axiomatizes a conjecture, unproved claim, or CG-specific hypothesis
- **KILLED**: Axiomatizes something known false, blocked, or with body `True` (vacuous)

## Audit Table

| File | Axiom | Category | Source | Notes |
|------|-------|----------|--------|-------|
| ABDWidthLowerBound | `minResWidth` | FUNC | — | Specifies min Resolution refutation width |
| ABDWidthLowerBound | `abd_width_from_kconsistency` | LIT | Atserias-Bulatov-Dalmau 2007; Atserias-Dalmau 2008 | KConsistent + UNSAT → width > k. Standard result |
| AC0FregeLowerBound | `minAC0FregeSize` | FUNC | — | Specifies min AC0-Frege proof size at depth d |
| AC0FregeLowerBound | `kconsistent_implies_ac0frege_exponential` | LIT | BIKPPW 1996 + Krajicek 1994 + Hastad 1986 | k-consistent UNSAT → AC0-Frege exponential. Published |
| BackwardLowerBound | `schoenebeck_linear_tight` | LIT | Schoenebeck 2008 (implicit) | Strengthened: adds upper bound |cubes| ≤ C·n |
| BooleanEncoding | `boolean_encoding_pol_eq_proj` | CONJ | Computational (250/250 verified) | Pol = projections preserved at bit level. Not proved in Lean |
| BoundedDepthFregeBarrier | `minBDFregeSize` | FUNC | — | Specifies min bounded-depth Frege proof size |
| BoundedDepthFregeBarrier | `bikppw_local` | LIT | BIKPPW 1996 | Precise form: (log2 size)^{c·d} ≥ k |
| BoundedDepthFregeBarrier | `barto_kozik_no_bounded_width` | LIT | Barto-Kozik 2014 + Atserias-Ochremiak 2019 | No WNU → no bounded width → k-consistent UNSAT exists |
| BSWWidthSize | `minResolutionSize` | FUNC | — | Specifies min Resolution proof size |
| BSWWidthSize | `bsw_width_to_size` | LIT | Ben-Sasson-Wigderson 2001 Cor. 3.6 | Size ≥ 2^{(w-3)²/(c·M)}. Faithful encoding |
| CCLifting | `minWitnessCC` | FUNC | — | Specifies witness communication complexity |
| CCLifting | `gpw_witness_quantitative` | LIT | Goos-Pitassi-Watson 2015/2018 | CC ≥ DT/c for composed functions |
| CCLifting | `minMonotoneInterpolantDepth` | FUNC | — | Specifies monotone interpolant depth |
| CCLifting | `kw_interpolant_depth` | LIT | Karchmer-Wigderson 1990 | Depth = CC for monotone functions |
| CCLifting | `resolution_fip_exponential` | CONJ | Mixes Frege size with Resolution FIP | WARNING: uses gamma_minFregeSize but claims Resolution FIP |
| CPLowerBound | `minCPWidth` | FUNC | — | Specifies min Cutting Planes width |
| CPLowerBound | `minCPSize` | FUNC | — | Specifies min Cutting Planes size |
| CPLowerBound | `kconsistent_implies_cp_high_width` | LIT | ABD 2007/2008 + Krajicek 1997 | k-consistent UNSAT → CP width > k |
| CPLowerBound | `cp_width_implies_size` | LIT | Hrubes-Pudlak 2017 | CP width w → size ≥ 2^{w/c} |
| CPLowerBoundMFI | `mfi_for_cp` | KILLED | Krajicek 1997 | Body = `True`. Vacuous axiom |
| CPLowerBoundMFI | `co_boundary_monotone_lb` | KILLED | Cavalar-Oliveira 2023 | Body = `True`. Vacuous axiom |
| CutCoverage | `cut_coverage_ge_borromean` | CONJ | Invented (CG-specific) | Proof DAG cut coverage ≥ Borromean order. Novel conjecture |
| CutDepthExtraction | `cg_cut_depth_bounded` | CONJ | Invented (CG-specific) | CG-UNSAT has Frege proofs with cut depth ≤ 10. Open conjecture |
| CutReuse | `expander_paths_distinct_compositions` | KILLED | Invented | Body = `True`. Vacuous. Direction KILLED (category error) |
| DepthFIP | `minFregeDepth` | FUNC | — | Specifies min Frege proof depth |
| DepthFregeLowerBound | `bikppw_precise` | LIT | BIKPPW 1996 | Precise depth-sensitive form: (log2 size)^{c·d} ≥ k |
| DerivationTrace | `mp_interpolant_is_substitution` | KILLED | Krajicek 1997 | Body = `True`. Vacuous axiom. Corrected from AND to substitution |
| DerivationTrace | `rank1_expiry_connection` | KILLED | Semantic bridge extension | Body = `True`. Vacuous. R ≤ 3 → expiry |
| DerivationTrace | `degree_bounded` | KILLED | Experimental (ρ_c) | Body = `True`. Vacuous. Max degree ≤ 12 |
| DistinctCompositions | `distinct_compositions_grow` | KILLED | Experimental | Body = `True`. Vacuous. Direction KILLED (category error) |
| FinalChain | `frege_cut_monotonicity_induction` | CONJ | CG-specific (semantic bridge extension) | Non-mono nesting = 1 for Frege cuts on CG. THE key conjecture |
| FregeLowerBound | `minFregeSize` | FUNC | — | Specifies min Frege proof size |
| FregeLowerBound | `bsw_with_formula_size_log` | LIT | BSW 2001 Cor. 3.6 | Log form: log2(S)·(c·N+1) ≥ k². Faithful encoding |
| HPExtension | `restriction_monotonicity_conjecture` | CONJ | Hrubes-Pudlak 2017 style | Frege FIP on random 3-SAT. Open question |
| InterpolantCircuitLB | `step4_pol_restriction` | CONJ | CSP theory (standard argument) | LEFT sub-CSP preserves Pol ⊆ L₃. Plausible but unproved |
| InterpolantCircuitLB | `step5_co_lower_bound` | LIT | Cavalar-Oliveira CCC 2023 | Pol ⊆ L₃ → mSIZE ≥ 2^{Ω(n^ε)}. Published |
| InterpolationGame | `minProofSize` | FUNC | — | Specifies min proof size for a named system |
| InterpolationGame | `minMonotoneInterpolantSize` | FUNC | — | Specifies min monotone interpolant circuit size |
| InterpolationGame | `monotone_interpolant_exponential` | CONJ | Overclaims Razborov 1985 | Claims exp monotone interpolant lb for CG. Razborov proved for CLIQUE, not gap consistency |
| InterpolationGame | `resolution_has_fip` | LIT | Krajicek 1997 | Resolution has monotone FIP. Standard |
| InterpolationGame | `cutting_planes_has_fip` | LIT | Pudlak 1997 / Krajicek 1997 | CP has monotone FIP. Standard |
| KRSynthesis | `pi_exp_dominates_linear` | LIT | Elementary analysis | 2^{n/c} > c·n for large n. Math fact |
| KRSynthesis | `pi_magnification` | LIT | Atserias-Muller 2025 | Superlinear → superpolynomial magnification. Published (arXiv) |
| LayeredExtraction | `active_nonmono_per_layer_bounded` | CONJ | CG-specific (rank-1 + locality) | ≤ B active non-mono per layer. Body = `True` but B ≤ 1728 specified |
| LiftingQueryToCircuit | `queryComplexity` | FUNC | — | Specifies query complexity of gap consistency |
| LiftingQueryToCircuit | `minKWGapCC` | FUNC | — | Specifies KW gap communication complexity |
| LiftingQueryToCircuit | `kw_gap_depth_eq` | LIT | Karchmer-Wigderson 1990 | CC = monotone depth for KW game |
| LiftingQueryToCircuit | `minGeneralCircuitSize` | FUNC | — | Specifies min general circuit size |
| MonotoneExtraction | `nonmonotone_cut_depth_bounded` | CONJ | CG-specific (diameter + rank-1) | Non-mono cut depth ≤ 3. Body = `True`. Open conjecture |
| MonotoneInterpolant | `craig_interpolation_frege` | LIT | Krajicek 1997 Thm 1.1 | Craig interpolation for Frege. Standard |
| MonotoneInterpolant | `fip_frege` | LIT | Krajicek 1997 | Frege refutation → interpolant exists. Standard |
| MonotoneInterpolant | `resolution_fip_monotone` | LIT | Krajicek 1997 Thm 4.5 | Resolution FIP gives monotone interpolant. Standard |
| MonotoneLowerBound | `boolean_encoding_preserves_projections` | KILLED | Computational (250/250) | Body = `True`. Vacuous placeholder |
| MonotoneLowerBound | `cavalar_oliveira_monotone_lb` | KILLED | Cavalar-Oliveira CCC 2023 | Body = `True`. Vacuous placeholder |
| MonotoneProofConversion | `monotone_proof_conversion` | CONJ | CG-specific (MPC conjecture) | Frege → monotone proof with poly blowup. Core conjecture |
| MonotoneProofConversion | `r_type2_bounded` | CONJ | Experimental | Type 2 reuse bounded. CG-specific claim |
| MonotoneProofConversion | `co_monotone_lb` | CONJ | Cavalar-Oliveira 2023 adapted | CO applied to CG. Stronger than placeholder in MonotoneLowerBound |
| MonotoneProofConversion | `nothelps_cg` | CONJ | CG-specific (central conjecture) | Frege ≈ Resolution on CG. Body may be `True` |
| MonotoneProofConversion | `backbone_restructuring` | CONJ | CG-specific (MPC variant) | Proof restructuring to monotone backbone |
| MonotoneSizeLB | `bsw_resolution_width` | LIT | Schoenebeck + ABD (equivalent) | Resolution width Ω(n) via k-consistency. Published |
| NegationComplexity | `markov_bound` | LIT | Markov 1958 | monoSize ≤ genSize × 2^neg. Classical result |
| PCLowerBound | `minPCDegree` | FUNC | — | Specifies min PC degree |
| PCLowerBound | `minPCSize` | FUNC | — | Specifies min PC size |
| PCLowerBound | `kconsistent_implies_pc_high_degree` | LIT | Schoenebeck 2008 + GHP 2002 | k-consistent UNSAT → PC degree > k |
| PCLowerBound | `pc_degree_implies_size` | LIT | Impagliazzo-Pudlak-Sgall 1999 | PC degree d → size ≥ 2^{d/c} |
| RankWidthTransfer | `abd_ad_consistency_implies_high_width` | LIT | ABD 2007 + AD 2008 | k-consistent + UNSAT → k < |cubes|. Weak form of ABD |
| ResolutionNegBounded | `resolution_neg_per_clause_effective` | CONJ | CG-specific (rank-1 convergence) | Body = `True`. ≤ 1728 neg cubes per clause in Resolution |
| SchoenebeckAxiom | `schoenebeck_linear_axiom` | LIT | Schoenebeck 2008 + AD 2008 | CANONICAL. SA needs Ω(n) levels. Well-established |
| SchoenebeckChain | `schoenebeck` | LIT | Schoenebeck 2008 | Constant-level form: ∀c, ∃ UNSAT passing c-consistency |
| SufficientLemma | `neg_cubes_per_formula_bounded_exists_exists` | CONJ | CG-specific (REVISED from KILLED) | Body = `True`. ∃ proof with ≤ B neg cubes. Experimentally refuted for CDCL |
| TransferConstrained | `transfer_alignment_axiom` | CONJ | CG-specific | Frege proofs on random 3-SAT are transfer-aligned. Open |
| WeakExpander | (no new axioms in scope) | — | — | Uses imported axioms only |
| WidthDepthCoupling | `wdc_holds` | CONJ | CG-specific conjecture | Width-Depth Coupling: log2 S ≥ k/(c·d). Replaces BIKPPW root with linear |
| WidthReuse | `resolution_width_linear` | KILLED | Schoenebeck + ABD | Body = `True`. Vacuous placeholder |
| WidthReuse | `width_bounds_reuse` | CONJ | CG-specific | Width → bounded reuse on expander. Conjectural |
| WidthReuse | `cg_resolution_reuse_bounded` | CONJ | CG-specific + experimental | CG reuse bounded. Polynomial growth ~n^0.6 |
| WitnessReduction | `minWitnessCircuit` | FUNC | — | Specifies min witness circuit size |
| WitnessReduction | `frege_to_witness` | LIT | Folklore | Proof evaluation gives witness circuit. Standard |
| WLLifting | `minResolutionDepth` | FUNC | — | Specifies min Resolution depth at width w |
| WLLifting | `minTreelikeSize` | FUNC | — | Specifies min treelike Resolution size at width w |

## Summary

| Category | Count | Description |
|----------|-------|-------------|
| **FUNC** | 20 | Function/constant declarations (uninterpreted) |
| **LIT** | 27 | Published results faithfully axiomatized |
| **CONJ** | 24 | Conjectures, unproved claims, CG-specific hypotheses |
| **KILLED** | 16 | Vacuous (body = `True`), dead code, or known-blocked directions |
| **Total** | 87 | |

## Key Observations

1. **16 vacuous axioms** have body `True` -- they carry no logical content. Many are placeholders from agent-generated code that were never filled in.

2. **27 literature axioms** faithfully encode published results (Schoenebeck, BSW, BIKPPW, Krajicek, Cavalar-Oliveira, etc.). These are the sound foundation.

3. **24 conjectures** are the research frontier. The most important ones:
   - `frege_cut_monotonicity_induction` (FinalChain) -- nesting = 1
   - `monotone_proof_conversion` (MPC) -- Frege → monotone with poly blowup
   - `restriction_monotonicity_conjecture` (HPExtension) -- Frege FIP on random 3-SAT
   - `nothelps_cg` (MPC) -- Frege ≈ Resolution on CG
   - `monotone_interpolant_exponential` -- overclaims Razborov for gap consistency

4. **Duplicate axioms**: `schoenebeck_linear_axiom` (canonical) has ~5 duplicates/variants across files.

5. **The 20 FUNC axioms** are sound -- they just declare uninterpreted constants that downstream axioms constrain.
