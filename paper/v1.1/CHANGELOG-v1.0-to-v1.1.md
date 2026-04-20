# Changelog: v1.0 → v1.1

**Date**: 2026-04-20

---

## Summary

Step 3 strengthened: verbal "correctness argument" replaced with formal
theorem chain (all proven in Lean 4, 0 sorry, 0 new axioms).
No change to structure, claims, or other steps.

---

## Changes in detail

### 1. Title page

- Added "Version 1.1" below date

### 2. Abstract

- GitHub tag reference: `v1.0-arxiv` → `v1.1`

### 3. §4.3 Step 3 (main change)

**REMOVED** (v1.0):
- Verbal correctness argument ("The procedure's code is fixed... suppose it has covered a set S...")
- Bullet list: Uncorrelated, Incompressible, Complete (informal)
- Reference to `pairwise_separable_full_check` as main theorem

**ADDED** (v1.1):
- **Theorem 4.X (Full Independence)**: For any subset S with σ ∉ S, ∃ two instances identical on S but differing on σ. (Lean: `full_independence`, 0 sorry, 0 axioms.)
- **Theorem 4.Y (Information Lower Bound)**: < n^k verifications → can't distinguish SAT from UNSAT. (Lean: `information_lb`, 0 sorry, 0 axioms.)
- **Theorem 4.Z (No Shortcuts)**: No Bool²→Bool derives T(σ₃) from T(σ₁), T(σ₂). (Lean: `shortcuts_impossible`, 0 sorry.)
- **Combining paragraph**: Three theorems close Step 3 without gap: (1) n^k necessary, (2) independent, (3) sequential machine → 1 step each → time ≥ n^k.
- **Remark (Why n=2 escapes)**: Z/2Z provides non-trivial polymorphism → implication graph batches 2^k into O(k). At n≥3: Pol=projections blocks grouping.
- **Supporting result**: Transfer matrices non-invertible → backward propagation blocked. (Lean: `rank2_nonperm_not_invertible`, 0 sorry.)

### 4. §8 Lean table

**REMOVED** rows:
- `pairwise_separable_full_check` (PNeNP)
- `and_witnesses_independent` (PNeNP)
- `and_of_witnesses` (PNeNP)

**ADDED** rows:
- `full_independence` (InformationLB) — n^k entries fully independent
- `information_lb` (InformationLB) ��� < n^k → undecidable
- `shortcuts_impossible` (PNeNP) — no shortcuts
- `rank2_nonperm_not_invertible` (PruningImpossible) — non-invertible
- `step3_complete` (Step3Closed) — complete chain
- `unique_solution_exists` (PNeNP) — each σ unique solution
- `must_observe_all` (InformationLB) — must observe all

### 5. §8 GitHub tag

- `v1.0-arxiv` → `v1.1`

### 6. Bibliography

**ADDED**:
- [cavalar2023] B. P. Cavalar and I. C. Oliveira. "Constant-depth circuits vs. monotone circuits." Proc. 38th CCC, LIPIcs vol. 264, pages 29:1–29:37, 2023.

---

## What did NOT change

- Paper title
- Author
- Overall structure (4-step proof, §1–§8)
- Steps 1, 2, 4 (unchanged)
- The main claim: P ≠ NP
- Barriers section (§5)
- Schoenebeck axiom (FOCS 2008, only external dependency)
- All other theorems and propositions
- Figures (all 7 unchanged)

---

## Lean formalization status

| | v1.0 | v1.1 |
|---|---|---|
| Sorry on critical path | 0 | 0 |
| External axioms | 1 (Schoenebeck) | 1 (same) |
| Lean files on critical path | 4 | 8 |
| Step 3 gap | Acknowledged ("argued") | Closed (formal chain) |
| New theorems | — | full_independence, information_lb, rank2_nonperm_not_invertible |
| GitHub tag | v1.0-arxiv | v1.1 |

---

## Files

- `CubeGraph_Cozma_2026.pdf` — compiled paper (20 pages)
- `CubeGraph_Cozma_2026.pdf.ots` — OpenTimestamps blockchain proof
- `main.tex` — LaTeX source
- `fig-*.pdf` — figures (unchanged from v1.0)
