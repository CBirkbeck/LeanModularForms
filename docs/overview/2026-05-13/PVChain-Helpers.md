# PVChain/Helpers.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ValenceFormula/PVChain/Helpers.lean` (528 lines)

Section: `noncomputable section`, with `Classical.propDecidable` as local instance and section variables `{k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)`.

### `def pvIntegrand`
- **Type**: `{k : ℤ} (f : ModularForm (Gamma 1) k) (γ : ℝ → ℂ) (S₀ : Finset ℂ) (ε : ℝ) (t : ℝ) → ℂ`
- **What**: The ε-truncated integrand for the principal-value integral of `f'/f` along `γ`, zero when `γ(t)` is within `ε` of any `s ∈ S₀`.
- **How**: Direct definition via `cauchyPrincipalValueIntegrandOn S₀ (logDeriv (modularFormCompOfComplex f)) γ ε t`.
- **Hypotheses**: None.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `modularFormCompOfComplex`
- **Used by**: External downstream (PV chain).
- **Visibility**: public
- **Lines**: 41-43
- **Notes**: None.

### `def sArcOfS`
- **Type**: `(S : Finset UpperHalfPlane) → Finset ℂ`
- **What**: Arc singular set: unit-circle zeros in `S` (image), their `S`-transforms `-1/z`, plus the elliptic points `ρ`, `ρ + 1`.
- **How**: `(S.filter ‖·‖=1).image (↑·) ∪ (S.filter ‖·‖=1).image (-1/·) ∪ {ρ, ρ+1}`.
- **Hypotheses**: None.
- **Uses from project**: `ellipticPointRho`, `ellipticPointRhoPlusOne`, `UpperHalfPlane`
- **Used by**: `onCurvePVProvider`, `fdBoundary_H_onCurvePVProvider`, `sArcOfS_rho_in`, `sArcOfS_rho_plus_one_in`, `sArcOfS_unit`, `sArcOfS_closed`, `sArcOfS_im_pos`, `fdBox_of_on_curve`
- **Visibility**: public
- **Lines**: 46-49
- **Notes**: None.

### `def sVertOfS`
- **Type**: `(S : Finset UpperHalfPlane) → Finset ℂ`
- **What**: Vertical singular set: points with `re = ±1/2` and `‖z‖ > 1`, together with their `T`-shifts `±1`.
- **How**: Four-fold union of `S.filter (re = ±1/2 ∧ ‖·‖ > 1).image (...)` over `(↑·)`, `(↑· - 1)`, and `(↑· + 1)`.
- **Hypotheses**: None.
- **Uses from project**: `UpperHalfPlane`
- **Used by**: `onCurvePVProvider`, `fdBoundary_H_onCurvePVProvider`, `sVertOfS_re`, `sVertOfS_pair_left`, `sVertOfS_pair_right`, `sVertOfS_im_lt_height_bound`, `sVertOfS_im_pos`, `sVertOfS_re_bound`, `sVertOfS_im_gt_sqrt3_half`, `fdBox_of_on_curve`
- **Visibility**: public
- **Lines**: 52-60
- **Notes**: None.

### `def onCurvePVProvider`
- **Type**: `(S : Finset UpperHalfPlane) → Prop`
- **What**: Predicate: CPV exists at every on-curve singular point `s ∈ sArcOfS S ∪ sVertOfS S` for the boundary `fdBoundary_H H` when `H > √3/2`.
- **How**: ∀ H, ∀ s, on-curve condition `∃ t ∈ Icc 0 5, fdBoundary_H H t = s` implies `CauchyPrincipalValueExists' ((·-s)⁻¹) (fdBoundary_H H) 0 5 s`.
- **Hypotheses**: None.
- **Uses from project**: `sArcOfS`, `sVertOfS`, `CauchyPrincipalValueExists'`, `fdBoundary_H`, `UpperHalfPlane`
- **Used by**: `fdBoundary_H_onCurvePVProvider`
- **Visibility**: public
- **Lines**: 63-66
- **Notes**: None.

### `theorem fdBoundary_H_onCurvePVProvider`
- **Type**: `(S : Finset UpperHalfPlane) → onCurvePVProvider S`
- **What**: CPV exists at every on-curve singular point of `fdBoundary_H H`.
- **How**: `exact fdBoundary_H_cpv_exists_of_onCurve H hH s h_on`.
- **Hypotheses**: None.
- **Uses from project**: `onCurvePVProvider`, `fdBoundary_H`, `fdBoundary_H_cpv_exists_of_onCurve`, `UpperHalfPlane`
- **Used by**: External downstream (PV chain).
- **Visibility**: public
- **Lines**: 70-73
- **Notes**: `omit f hf in`.

### `lemma sArcOfS_rho_in`
- **Type**: `(S : Finset UpperHalfPlane) → ellipticPointRho ∈ sArcOfS S`
- **What**: `ρ ∈ sArcOfS S` (it's in the literal `{ρ, ρ+1}` summand).
- **How**: `simp [sArcOfS]`.
- **Hypotheses**: None.
- **Uses from project**: `sArcOfS`, `ellipticPointRho`, `UpperHalfPlane`
- **Used by**: External downstream.
- **Visibility**: public
- **Lines**: 76-78
- **Notes**: `omit f hf in`.

### `lemma sArcOfS_rho_plus_one_in`
- **Type**: `(S : Finset UpperHalfPlane) → ellipticPointRhoPlusOne ∈ sArcOfS S`
- **What**: `ρ + 1 ∈ sArcOfS S`.
- **How**: `simp [sArcOfS]`.
- **Hypotheses**: None.
- **Uses from project**: `sArcOfS`, `ellipticPointRhoPlusOne`, `UpperHalfPlane`
- **Used by**: External downstream.
- **Visibility**: public
- **Lines**: 81-83
- **Notes**: `omit f hf in`.

### `lemma sArcOfS_unit`
- **Type**: `(S : Finset UpperHalfPlane) → ∀ s ∈ sArcOfS S, ‖s‖ = 1`
- **What**: Every point of `sArcOfS S` lies on the unit circle.
- **How**: Destructure into three cases (image, -1/image, elliptic): images use `hp_norm`; `-1/p`: `norm_div`, `norm_neg`, `hp_norm`, `div_one`; elliptic: `ellipticPointRho_norm`, `ellipticPointRhoPlusOne_norm`.
- **Hypotheses**: None.
- **Uses from project**: `sArcOfS`, `ellipticPointRho_norm`, `ellipticPointRhoPlusOne_norm`, `UpperHalfPlane`
- **Used by**: `fdBox_of_on_curve`
- **Visibility**: public
- **Lines**: 86-96
- **Notes**: `omit f hf in`. >10 lines (11 lines).

### `private lemma neg_inv_rho_eq_rho_plus_one`
- **Type**: `-(1 : ℂ) / ellipticPointRho = ellipticPointRhoPlusOne`
- **What**: The S-transform of `ρ` is `ρ + 1`.
- **How**: Compute `re` and `im` of both sides using `ellipticPointRho/RhoPlusOne'` definitions; compute `normSq ρ = (-1/2)² + (√3/2)² = 1`; apply `Complex.ext` and `ring`.
- **Hypotheses**: None.
- **Uses from project**: `ellipticPointRho`, `ellipticPointRho'`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`
- **Used by**: `sArcOfS_closed`
- **Visibility**: private
- **Lines**: 99-120
- **Notes**: `omit f hf in`. >10 lines (22 lines).

### `private lemma neg_inv_rho_plus_one_eq_rho`
- **Type**: `-(1 : ℂ) / ellipticPointRhoPlusOne = ellipticPointRho`
- **What**: The S-transform of `ρ + 1` is `ρ`.
- **How**: Mirror of `neg_inv_rho_eq_rho_plus_one`: compute `re/im` of both points, `normSq = (1/2)² + (√3/2)² = 1`, `Complex.ext` + `ring`.
- **Hypotheses**: None.
- **Uses from project**: `ellipticPointRho`, `ellipticPointRho'`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`
- **Used by**: `sArcOfS_closed`
- **Visibility**: private
- **Lines**: 123-143
- **Notes**: `omit f hf in`. >10 lines (21 lines).

### `lemma sArcOfS_closed`
- **Type**: `(S : Finset UpperHalfPlane) → ∀ s ∈ sArcOfS S, -(1 : ℂ) / s ∈ sArcOfS S`
- **What**: `sArcOfS S` is closed under the S-transform `s ↦ -1/s`.
- **How**: Case on `s`: image branch maps to S-transform image; S-transform branch: from `hp.2 = norm = 1`, deduce `↑p ≠ 0` (else norm zero), then `-1/(-1/p) = p` via `field_simp`; elliptic: use `neg_inv_rho_eq_rho_plus_one` / `neg_inv_rho_plus_one_eq_rho`.
- **Hypotheses**: None.
- **Uses from project**: `sArcOfS`, `neg_inv_rho_eq_rho_plus_one`, `neg_inv_rho_plus_one_eq_rho`, `UpperHalfPlane`
- **Used by**: External downstream (PV chain).
- **Visibility**: public
- **Lines**: 146-169
- **Notes**: `omit f hf in`. >10 lines (24 lines).

### `lemma sVertOfS_re`
- **Type**: `(S : Finset UpperHalfPlane) → ∀ s ∈ sVertOfS S, s.re = 1/2 ∨ s.re = -1/2`
- **What**: Every vertical singular point has real part `±1/2`.
- **How**: Case on which of the 4 image branches; for each, extract `re = ±1/2` from filter and adjust via `sub_re`/`add_re` for the shifted branches.
- **Hypotheses**: None.
- **Uses from project**: `sVertOfS`, `UpperHalfPlane`
- **Used by**: External downstream.
- **Visibility**: public
- **Lines**: 172-192
- **Notes**: `omit f hf in`. >10 lines (21 lines).

### `lemma sVertOfS_pair_left`
- **Type**: `(S : Finset UpperHalfPlane) → ∀ s ∈ sVertOfS S, s.re = 1/2 → s - 1 ∈ sVertOfS S`
- **What**: The `T`-pair of any `s ∈ sVertOfS S` with `re = 1/2` is `s - 1` ∈ `sVertOfS S`.
- **How**: Case on the 4 branches of `s`'s membership; for the matching branch (re = 1/2), apply the shift-image branch (re = 1/2 - 1 = -1/2 already in set); for non-matching branches derive contradictions on `re` (e.g., branch B has `(↑p - 1).re = -1/2`, branch C has `re = -1/2`).
- **Hypotheses**: None.
- **Uses from project**: `sVertOfS`, `UpperHalfPlane`
- **Used by**: External downstream.
- **Visibility**: public
- **Lines**: 195-226
- **Notes**: `omit f hf in`. >10 lines (32 lines).

### `lemma sVertOfS_pair_right`
- **Type**: `(S : Finset UpperHalfPlane) → ∀ s ∈ sVertOfS S, s.re = -1/2 → s + 1 ∈ sVertOfS S`
- **What**: The `T`-pair of any `s ∈ sVertOfS S` with `re = -1/2` is `s + 1` ∈ `sVertOfS S`.
- **How**: Mirror of `sVertOfS_pair_left`: case on the 4 branches, route the matching one to the shift-image branch, derive contradictions otherwise.
- **Hypotheses**: None.
- **Uses from project**: `sVertOfS`, `UpperHalfPlane`
- **Used by**: External downstream.
- **Visibility**: public
- **Lines**: 229-258
- **Notes**: `omit f hf in`. >10 lines (30 lines).

### `private theorem modularFormCompOfComplex_periodic`
- **Type**: `Function.Periodic (modularFormCompOfComplex f) (1 : ℂ)`
- **What**: `modularFormCompOfComplex f` is periodic with period 1 (T-invariance).
- **How**: `SlashInvariantFormClass.periodic_comp_ofComplex f ModularFormClass.one_mem_strictPeriods_SL2Z`.
- **Hypotheses**: None (uses section `f : ModularForm (Gamma 1) k`).
- **Uses from project**: `modularFormCompOfComplex`, `ModularFormClass.one_mem_strictPeriods_SL2Z`
- **Used by**: unused in file (private but referenced downstream)
- **Visibility**: private
- **Lines**: 262-264
- **Notes**: `omit hf in`.

### `theorem exists_height_bound_S`
- **Type**: `(S : Finset UpperHalfPlane) → ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧ 1 < H₁ ∧ ∀ s ∈ S, (s : ℂ).im < H₁`
- **What**: A height above `√3/2` (and 1) strictly exceeding all `im` of points in `S`.
- **How**: Empty case: use `H₁ = 2` (`√3/2 < 2`, `1 < 2`). Non-empty case: `M := S.sup' h_ne (im)`, show `M > 0` via any `s.2`, set `H₁ := max 2 (M + 1)`; bounds verified by `nlinarith` with `Real.sq_sqrt`.
- **Hypotheses**: None.
- **Uses from project**: `UpperHalfPlane`
- **Used by**: External downstream.
- **Visibility**: public
- **Lines**: 269-285
- **Notes**: `omit f hf in`. >10 lines (17 lines).

### `lemma sVertOfS_im_lt_height_bound`
- **Type**: `(S : Finset UpperHalfPlane) → (s : ℂ) → s ∈ sVertOfS S → (∀ p ∈ S, (p : ℂ).im < H₁) → s.im < H₁`
- **What**: All elements of `sVertOfS S` have `im < H₁` when all elements of `S` do.
- **How**: Case on 4 branches: image branch directly uses `h_bound`; sub-1 and add-1 branches use `sub_im`/`add_im` with `one_im = 0`.
- **Hypotheses**: All elements of `S` have `im < H₁`.
- **Uses from project**: `sVertOfS`, `UpperHalfPlane`
- **Used by**: `fdBox_of_on_curve`
- **Visibility**: public
- **Lines**: 289-305
- **Notes**: `omit f hf in`. >10 lines (17 lines).

### `private theorem zeros_complete_of_hS_complete`
- **Type**: `(S : Finset UpperHalfPlane) → (∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) → ∀ s, s ∈ 𝒟 → f s = 0 → s ∈ S.filter (fun p => f p = 0)`
- **What**: Zeros in `S` are complete: every zero of `f` in the fundamental domain `𝒟` lies in `S.filter zero`.
- **How**: `Finset.mem_filter.mpr` from `hS_complete` and `orderOfVanishingAt'_ne_zero_of_eq_zeroFM f hf s hs_zero`.
- **Hypotheses**: `f ≠ 0`, `S` completes zeros in `𝒟`.
- **Uses from project**: `𝒟` (fundamental domain), `orderOfVanishingAt'`, `orderOfVanishingAt'_ne_zero_of_eq_zeroFM`, `UpperHalfPlane`
- **Used by**: External downstream.
- **Visibility**: private
- **Lines**: 309-314
- **Notes**: `include hf in`.

### `theorem sum_gWN_ord_eq_filter_zeros`
- **Type**: `(S : Finset UpperHalfPlane) (g : ℂ → ℂ) → ∑ s ∈ S, g s · ord(f, s) = ∑ s ∈ S.filter (f = 0), g s · ord(f, s)`
- **What**: Summing `gWN · ord` over all of `S` equals summing over just the zero subset (other terms have `ord = 0`).
- **How**: `Finset.sum_filter` then `Finset.sum_congr rfl`; for non-zero `f p`, `orderOfVanishingAt'_eq_zero_of_ne_zero'` gives `ord = 0`, killing the term.
- **Hypotheses**: None.
- **Uses from project**: `orderOfVanishingAt'`, `orderOfVanishingAt'_eq_zero_of_ne_zero'`, `UpperHalfPlane`
- **Used by**: External downstream.
- **Visibility**: public
- **Lines**: 318-327
- **Notes**: `omit hf in`. >10 lines (10 lines).

### `lemma sArcOfS_im_pos`
- **Type**: `(S : Finset UpperHalfPlane) → (s : ℂ) → s ∈ sArcOfS S → 0 < s.im`
- **What**: Every point of `sArcOfS S` has positive imaginary part.
- **How**: Case on 3 branches: image branch uses `p.2`; S-transform branch: rewrite `-1/p = (-p)⁻¹`, then `Complex.inv_im` reduces to `-im/normSq`; numerator and denominator positive via `Complex.normSq_pos`. Elliptic branch: explicit `Im = √3/2 > 0` for ρ, ρ+1.
- **Hypotheses**: None.
- **Uses from project**: `sArcOfS`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, `UpperHalfPlane`
- **Used by**: `fdBox_of_on_curve`
- **Visibility**: public
- **Lines**: 331-348
- **Notes**: `omit f hf in`. >10 lines (18 lines).

### `lemma sVertOfS_im_pos`
- **Type**: `(S : Finset UpperHalfPlane) → (s : ℂ) → s ∈ sVertOfS S → 0 < s.im`
- **What**: Every point of `sVertOfS S` has positive imaginary part.
- **How**: Case on 4 branches: each uses `p.2` (UpperHalfPlane `im > 0`); `sub_im`/`add_im` for shifted branches.
- **Hypotheses**: None.
- **Uses from project**: `sVertOfS`, `UpperHalfPlane`
- **Used by**: External downstream.
- **Visibility**: public
- **Lines**: 352-366
- **Notes**: `omit f hf in`. >10 lines (15 lines).

### `private lemma sVertOfS_re_bound`
- **Type**: `(S : Finset UpperHalfPlane) → (s : ℂ) → s ∈ sVertOfS S → |s.re| ≤ 1/2`
- **What**: Every vertical singular point has `|re| ≤ 1/2`.
- **How**: Case on 4 branches: extract `re = ±1/2` from filter; for shifted branches adjust by `sub_re`/`add_re` then `norm_num`.
- **Hypotheses**: None.
- **Uses from project**: `sVertOfS`, `UpperHalfPlane`
- **Used by**: `fdBox_of_on_curve`
- **Visibility**: private
- **Lines**: 369-388
- **Notes**: `omit f hf in`. >10 lines (20 lines).

### `private lemma im_gt_sqrt3_half_of_re_half_and_norm_gt_one`
- **Type**: `(p : ℍ) → (↑p : ℂ).re = 1/2 ∨ (↑p : ℂ).re = -1/2 → ‖(↑p : ℂ)‖ > 1 → (↑p : ℂ).im > Real.sqrt 3 / 2`
- **What**: For `p ∈ ℍ` with `re = ±1/2` and `‖p‖ > 1`, the imaginary part exceeds `√3/2`.
- **How**: From `‖p‖² > 1` derive `re² + im² > 1`; with `re² = 1/4`, get `im² > 3/4`; sqrt monotonicity (`Real.sqrt_lt_sqrt`) and `Real.sqrt_sq` give `im > √3/2`.
- **Hypotheses**: `re = ±1/2`, `‖p‖ > 1`.
- **Uses from project**: `UpperHalfPlane`
- **Used by**: `sVertOfS_im_gt_sqrt3_half`
- **Visibility**: private
- **Lines**: 391-410
- **Notes**: `omit f hf in`. >10 lines (20 lines).

### `private lemma sVertOfS_im_gt_sqrt3_half`
- **Type**: `(S : Finset UpperHalfPlane) → (s : ℂ) → s ∈ sVertOfS S → s.im > Real.sqrt 3 / 2`
- **What**: Every vertical singular point has `im > √3/2`.
- **How**: Case on 4 branches: apply `im_gt_sqrt3_half_of_re_half_and_norm_gt_one` with appropriate `Or.inl/Or.inr` and filter data; `sub_im`/`add_im` for shifted branches.
- **Hypotheses**: None.
- **Uses from project**: `sVertOfS`, `im_gt_sqrt3_half_of_re_half_and_norm_gt_one`, `UpperHalfPlane`
- **Used by**: `fdBox_of_on_curve`
- **Visibility**: private
- **Lines**: 413-432
- **Notes**: `omit f hf in`. >10 lines (20 lines).

### `private lemma im_ge_sqrt3_half_of_re_half_and_norm_eq_one`
- **Type**: `(p : ℍ) → |(↑p : ℂ).re| ≤ 1/2 → ‖(↑p : ℂ)‖ = 1 → (↑p : ℂ).im ≥ Real.sqrt 3 / 2`
- **What**: For `p ∈ ℍ` with `|re| ≤ 1/2` and `‖p‖ = 1`, the imaginary part is `≥ √3/2`.
- **How**: From `‖p‖² = 1` and `re² ≤ 1/4` get `im² ≥ 3/4`; case on equality vs strict, both yield `im ≥ √3/2` via `Real.sqrt_sq` and `Real.sqrt_lt_sqrt`.
- **Hypotheses**: `|re| ≤ 1/2`, `‖p‖ = 1`.
- **Uses from project**: `UpperHalfPlane`
- **Used by**: `fdBox_of_on_curve`
- **Visibility**: private
- **Lines**: 435-461
- **Notes**: `omit f hf in`. >10 lines (27 lines).

### `lemma fdBox_of_on_curve`
- **Type**: `(S : Finset UpperHalfPlane) → (∀ p ∈ S, p ∈ 𝒟) → {H M : ℝ} → Real.sqrt 3 / 2 < H → H < M → 1 ≤ H → (∀ s ∈ S, (s : ℂ).im < H) → (s : ℂ) → s ∈ sArcOfS S ∪ sVertOfS S → s ∈ fdBox M`
- **What**: On-curve singular points (arc or vert) lie inside `fdBox M` when the boundary height `H` satisfies `√3/2 < H < M`, `1 ≤ H`, and `S ⊆ 𝒟` with all heights bounded.
- **How**: Case `s ∈ sArcOfS`: derive `‖s‖ = 1` (`sArcOfS_unit`), `0 < s.im` (`sArcOfS_im_pos`), so `re² + im² = 1`, `re² < 1`, `im ≤ 1`. For `im ≥ √3/2`: depends on branch: image uses `im_ge_sqrt3_half_of_re_half_and_norm_eq_one (hS p).2 hp_norm`; S-transform branch shows `Im(-1/p) = Im p` (via `Complex.inv_im`, `normSq_neg`, normSq = 1), then same lemma; elliptic branch direct. Bound `re ∈ (-1, 1)`, `im ∈ [√3/2, 1]`. Case `s ∈ sVertOfS`: use `sVertOfS_re_bound` (`|re| ≤ 1/2`), `sVertOfS_im_gt_sqrt3_half`, `sVertOfS_im_lt_height_bound`. In both cases pack into `fdBox` constructor with `√3 > 1` proved via `Real.sqrt_one.symm` and `Real.sqrt_lt_sqrt`.
- **Hypotheses**: `S ⊆ 𝒟`, `√3/2 < H < M`, `1 ≤ H`, all `S.im < H`.
- **Uses from project**: `sArcOfS`, `sVertOfS`, `sArcOfS_unit`, `sArcOfS_im_pos`, `sVertOfS_re_bound`, `sVertOfS_im_gt_sqrt3_half`, `sVertOfS_im_lt_height_bound`, `im_ge_sqrt3_half_of_re_half_and_norm_eq_one`, `fdBox`, `𝒟`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, `UpperHalfPlane`
- **Used by**: External downstream (PV chain).
- **Visibility**: public
- **Lines**: 465-527
- **Notes**: `omit f hf in`. >10 lines (63 lines).

## File Summary

This file defines the singular-set bookkeeping for the principal-value formulation of the valence formula on `Gamma 1`. It introduces `sArcOfS S` (arc singularities: unit-circle zeros and their S-transforms `-1/z` plus `ρ`, `ρ+1`) and `sVertOfS S` (vertical singularities: zeros with `re = ±1/2`, `‖·‖ > 1`, and their T-shifts `±1`). The headline structural lemmas establish: (1) S-closure of arc set (`sArcOfS_closed`) via two computational identities `-1/ρ = ρ+1` and `-1/(ρ+1) = ρ`; (2) T-closure of vert set (`sVertOfS_pair_left/right`); (3) geometric containment in `fdBox M` (`fdBox_of_on_curve`) for any boundary height `H ∈ (√3/2, M)`. Also: `pvIntegrand` (the ε-truncated CPV integrand for `f'/f`), `onCurvePVProvider` (CPV existence predicate, witnessed via `fdBoundary_H_cpv_exists_of_onCurve`), `exists_height_bound_S` (height above all `S.im`), `sum_gWN_ord_eq_filter_zeros` (restrict sum to zero-filter). Total: 3 definitions + 22 lemmas/theorems. No `sorry`, no axioms, no `set_option`. Uses `omit f hf` extensively for the structural set-membership lemmas.
