# Mathlib Quality Audit — HeckeRIngs

Generated: 2026-03-23 | Branch: `hecke-ring`

## Stage 1: Variable cleanup + easy fixes (eliminates ~140 `omit` lines + dead code)

- [x] **1a.** AbstractHeckeRing: Remove `[IsDomain Z]` from `variable` in Module.lean ✅
- [x] **1b.** AbstractHeckeRing: Remove unused variables from `variable` blocks ✅
- [x] **1c.** GLn: Remove `[NeZero n]` from file-level `variable` (~130 omit lines removed) ✅
- [x] **1d.** Fix `decompQuot_T_one_eq_bot` → `decompQuot_T_one_eq_top` ✅
- [x] **1e.** Remove `T_ad'` alias ✅
- [x] **1f.** Remove `T_ad_self_eq_T_ad` dead code ✅
- [x] **1g.** Remove `diagMul_pos` deprecated alias ✅
- [x] **1h.** Consolidate `divChain_dvd`/`divChain_div_pos` in DiagonalCosets.lean ✅
- [x] **1i.** Remove duplicate `smulOrbit_map_injective` in Degree.lean ✅
- [x] **1j.** Remove `one_eq_T_single` duplicate ✅
- [x] **1k.** Remove unused `Γₙ` / `Δₙ` notations ✅

## Stage 2: Rename `thm324_*` + fix public/private visibility

- [x] **2a.** `thm324_2` → `T_ad_one_ppow_eq` ✅
- [x] **2b.** `thm324_3` → `T_sum_mul` ✅
- [x] **2c.** `thm324_4` → `T_sum_ppow_mul` ✅
- [x] **2d.** `thm324_5` → `T_sum_prime_mul_T_ad` ✅
- [x] **2e.** `thm324_6` → `deg_T_diag_ppow`, `thm324_6_scalar` → `deg_T_diag_scalar` ✅
- [x] **2f.** `thm324_7` → `deg_T_sum` ✅
- [x] **2g.** Make `T_sum_nat`, `T_sum_nat_eq` public ✅
- [x] **2h.** Make `T_sum_one` public ✅
- [x] **2i.** Make `T_ad_mul_of_coprime` public ✅
- [x] **2j.** Make `gcd_factor_prime_pow`, `gcd_pow_pow_of_le`, `mul_injOn_coprime_divisors` public ✅
- [x] **2k.** Make `matrix_isolate_middle` public ✅
- [ ] **2l.** Make `deg_fun` private — SKIPPED (used cross-file)
- [x] **2m.** Make `M_ext_set` public with `@[ext]` ✅
- [x] **2n.** Remove scoped notations `T⦃⦄`, `◇`, `Diag()` ✅
- [x] **2o.** Make `SLnZ_to_GLnQ_det/val` public ✅

## Stage 3: Add docstrings

- [x] **3a.** Module docstrings: all files have `/-! -/` headers ✅
- [x] **3b.** AbstractHeckeRing: ~50 docstrings added across 7 files ✅
- [x] **3c.** GLn: ~18 docstrings added across 9 files ✅
- [x] **3d.** GL2: ~15 docstrings added across 4 files ✅
- [x] **3e.** Key theorems all documented ✅

## Stage 4: Naming pass (coordinate across all files)

- [x] **4a.** Structure fields: `T'.set` → `T'.carrier`, `T'.eql` → `T'.doubleCoset_eq`, `M.set` → `M.carrier`, `M.eql` → `M.leftCoset_eq` (~400 references updated across 14 files) ✅
- [x] **4b.** `T_mk` → `T'.mk'`, `M_mk` → `M.mk'`, `T_one` → `T'.one`, `M_one` → `M.one` (14 files updated) ✅
- [x] **4c.** Lemma names: 9 `𝕋_*` renames to `*_𝕋` ✅
- [ ] **4d.** GLn names: `SLnZ_subgroup`, `posDetInt_submonoid`, etc. (deferred — needs mathlib naming discussion)
- [ ] **4e.** GL2 names: `T_ad`, `T_pp`, `T_sum` (deferred — these are standard Hecke ring notation)
- [ ] **4f.** Fix `D1/D2` → `D₁/D₂` subscripts (deferred — cosmetic)
- [x] **4g.** Fix `m'_T_one`/`m'_one_T` → `m'_mul_one`/`m'_one_mul` (6 renames) ✅
- [x] **4h.** Fix `left_coset_exist` → `leftCoset_exists` ✅

## Stage 5: Split large files

- [x] **5a.** Extract SL_n transvection generation → `GLn/SLnTransvection.lean` (566 lines, CoprimeMul reduced to 1031) ✅
- [ ] **5b.** Extract CRT decomposition → `CRTDecomposition.lean` (deferred)
- [x] **5c.** Move `CongruenceIndex.lean` from GLn/ to GL2/ ✅
- [ ] **5d.** Split MultiplicationTable.lean degree formulas (deferred)
- [ ] **5e.** Further MultiplicationTable splits (deferred)

## Stage 6: Add missing `@[simp]` + replace mathlib-duplicate code

- [x] **6a.** Add `@[simp]`: `T_ad_one_one`, `heckeSlash_zero`, `diagMat_mul`, `diagMat_scalar_eq` ✅
- [x] **6b.** `det_intMat_cast` — already minimal (Int.cast vs RingHom mismatch prevents one-liner) ✅
- [x] **6c.** `intMat_map_mul` — already minimal, private, used 2x ✅
- [ ] **6d.** Replace generic Finsupp lemmas in Module.lean (deferred — needs mathlib contribution)
- [x] **6e.** Changed `@[reducible] def UpperTriRep` to `abbrev` ✅
- [x] **6f.** Added junk-value documentation to `diagMat` docstring ✅

## Stage 7: Architectural improvements

- [x] **7a.** Added TODO comment for RingHom packaging of heckeOperator ✅
- [x] **7b.** No maxHeartbeats annotations found (previously removed or never present) ✅
- [x] **7c.** Replaced `open Classical` → `open scoped Classical` (3 occurrences) ✅
- [ ] **7d.** Fill the 2 sorries in PolynomialRing.lean (Shimura Thm 3.20) — hard, separate task

## Notes

- Stages 1-3 are safe mechanical changes that don't affect proof logic
- Stage 4 is a large rename that should be done in one pass to avoid intermediate breakage
- Stage 5 is file reorganization — do after renames to avoid merge conflicts
- Stages 6-7 require deeper understanding and may affect proof structure
