# Axiom #12 Eliminated — 2026-03-20

## Summary

`axiom er_sparse_kconsistent_extends` replaced by `theorem er_kconsistent_from_aggregate` with full proof (0 sorry).

This was the last internal axiom. The remaining axioms are all external literature results (Schoenebeck, GPW lifting, BSW, GGKS, etc.).

## Files Modified

### `ERKConsistentProof.lean` — 3 fixes

1. **Line 274**: `bit_consistency'` → `bit_consistency` (typo in identifier name)

2. **Lines 272-277**: Factored out `hex : ∃ j ∈ S_orig, sv' ∈ (G.cubes[j]).vars` so that `Classical.choose hex` / `Classical.choose_spec hex` have inferable types (previously `⟨proj_i, hmem, hsv'_g⟩` inline failed)

3. **Lines 296-304**: Fixed `Classical.choose` corruption from `rw [varAt_of_idxOf_eq] at hb`

   **Problem**: `rw [varAt_of_idxOf_eq _ sv' _ hsv' hp] at hb` rewrites ALL occurrences of `varAt pos` in `hb`, including inside `Classical.choose (multi_compatible_gap ... (varBit (varAt pos) == 1) ...)`. This creates a different `Classical.choose` instance, causing a type mismatch that LOOKS identical when printed (differences hidden behind `⋯`).

   **Fix**: Rewrite the GOAL instead of the hypothesis:
   ```lean
   have hva := varAt_of_idxOf_eq (ext.extended.cubes[i]) sv' (other_positions w).1 hsv' hp
   rw [← hva]  -- changes goal's `varBit sv'` → `varBit (varAt ...)`
   exact bit_val_eq _ _ (by rw [hva]; exact hvb) hb  -- hb untouched
   ```

### `ERKConsistentInduction.lean` — axiom removed

- Import: `ERKConsistentBridge` → `ERKConsistentProof`
- Deleted `axiom er_sparse_kconsistent_extends` (+ 15-line docstring)
- `er_borromean_unconditional`: `h_fresh` (linkWeight ≤ 2) → `h_aggregate` (∃ fresh variable)
- `er_exponential_unconditional`: same hypothesis change
- Both now call `er_kconsistent_from_aggregate`

## Hypothesis Change

**Old** (axiom): `∀ i j, linkWeight (cubes[i]) (cubes[j]) ≤ 2` — each new cube shares at most 2 vars with any other

**New** (theorem): `∀ i, ∃ w_pos : Fin 3, ∀ j, i ≠ j → cubes[i].varAt w_pos ∉ cubes[j].vars` — each new cube has a fresh variable not in any other cube

The new hypothesis is stronger (fresh variable implies linkWeight ≤ 2, but not vice versa) but matches the actual ER construction.

## Verification

```bash
cd formal && lake build  # 160 jobs, 0 errors, 0 sorry
grep -rn 'sorry' CubeGraph/ --include='*.lean'  # only in comments
grep -rn '^axiom ' CubeGraph/ --include='*.lean'  # only external literature axioms
```

## Remaining Axioms (all external)

| Axiom | Source | File |
|-------|--------|------|
| `schoenebeck` | Schoenebeck 2008 | SchoenebeckChain.lean |
| `schoenebeck_linear` | Schoenebeck 2008 | SchoenebeckChain.lean |
| `gpw_lifting` | GPW 2010 | LiftingTheorem.lean |
| `kw_cc_equals_depth` | Kolaitis-Vardi | LiftingTheorem.lean |
| `bsw_resolution_width` | BSW 2001 | MonotoneSizeLB.lean |
| `ggks_width_to_monotone_size` | GGKS 2012 | MonotoneSizeLB.lean |
| `braverman_polylog_fools_ac0` | Braverman 2010 | BorromeanAC0.lean |
| `abd_ad_consistency_implies_high_width` | ABD 2007 | RankWidthTransfer.lean |
| `petke_jeavons_consistency_eq_hyperres` | Petke-Jeavons 2012 | RankWidthTransfer.lean |
| `berkholz_propagation_depth` | Berkholz 2012 | RankWidthTransfer.lean |
