# SingularAnnulus.lean Inventory

File: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/PVInfrastructure/SingularAnnulus.lean
Lines: 765

### `private instance : NormSMulClass ℝ ℂ`
- **Type**: `NormSMulClass ℝ ℂ`
- **What**: Local instance enabling `‖r • z‖ = ‖r‖ · ‖z‖` for `r : ℝ`, `z : ℂ`.
- **How**: Forward `NormedSpace.toNormSMulClass`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: implicit (typeclass).
- **Visibility**: private instance.
- **Lines**: 25-25.
- **Notes**: short.

### `lemma norm_annulus_condition_iff`
- **Type**: `(hL_pos : 0 < ‖L‖) (t : ℝ) : (ε₂ < ‖L‖ * |t − t₀| ∧ ‖L‖ * |t − t₀| ≤ ε₁) ↔ (ε₂/‖L‖ < |t − t₀| ∧ |t − t₀| ≤ ε₁/‖L‖)`
- **What**: Rescaling the annulus condition from `‖L‖·|t−t₀|` to `|t−t₀|` directly.
- **How**: Forward and backward rewriting using `div_lt_iff₀`, `le_div_iff₀`, and `mul_comm`.
- **Hypotheses**: `0 < ‖L‖`.
- **Uses from project**: [].
- **Used by**: `singular_annulus_lin_integral_zero`.
- **Visibility**: public.
- **Lines**: 33-42.
- **Notes**: short.

### `lemma intervalIntegral_eq_zero_of_ae_eq_zero`
- **Type**: `(_hI : IntervalIntegrable φ volume a b) (h_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → φ t = 0) : ∫ t in a..b, φ t = 0`
- **What**: An a.e.-zero integrand has zero interval integral.
- **How**: Rewrite the integral as `∫ a..b, 0` via `intervalIntegral.integral_congr_ae` + `filter_upwards`, then `intervalIntegral.integral_zero`.
- **Hypotheses**: `IntervalIntegrable φ volume a b`, a.e. zero on `uIoc a b`.
- **Uses from project**: [].
- **Used by**: `lin_indicator_zero_left`, `lin_indicator_zero_right`.
- **Visibility**: public.
- **Lines**: 45-53.
- **Notes**: short.

### `lemma integral_split_five`
- **Type**: From five `IntervalIntegrable` hypotheses on consecutive pieces, splits `∫ a..b φ` into five sub-integrals at four intermediate points.
- **What**: Five-way split of an interval integral at ordered intermediate points.
- **How**: Apply `intervalIntegral.integral_add_adjacent_intervals` four times (sequentially), combining integrabilities with `IntervalIntegrable.trans`.
- **Hypotheses**: five `IntervalIntegrable` hypotheses on `a..p₁`, `p₁..p₂`, ..., `p₄..b`.
- **Uses from project**: [].
- **Used by**: `singular_annulus_lin_integral_zero`.
- **Visibility**: public.
- **Lines**: 56-82.
- **Notes**: 27 lines.

### `lemma singular_tAnnLin_inside_interval`
- **Type**: For `t₀ ∈ Ioo a b`, `0 < ‖L‖`, `ε₁ < ‖L‖ · min (t₀ − a) (b − t₀)`, and `‖L‖ · |t − t₀| ≤ ε₁`: `t ∈ Icc a b`.
- **What**: If the rescaled distance `‖L‖·|t−t₀|` is bounded by `ε₁` (less than the distance to the endpoints), then `t` stays inside `[a, b]`.
- **How**: From `‖L‖ · |t − t₀| ≤ ε₁ < ‖L‖ · min(t₀ − a, b − t₀)`, divide by `‖L‖ > 0` to get `|t − t₀| < min(...)`, then `abs_lt` and `linarith`.
- **Hypotheses**: `hat₀`, `hL_pos`, `hε₁_small`, `ht_bound`.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 86-104.
- **Notes**: 19 lines. Likely intended for downstream callers.

### `lemma singular_tAnnLin_cancel`
- **Type**: For `0 < ‖L‖`, `0 < ε₂ ≤ ε₁`: with `c₁ := ε₂/‖L‖`, `c₂ := ε₁/‖L‖`, `∫_{t₀ − c₂}^{t₀ − c₁} (t−t₀)⁻¹ + ∫_{t₀ + c₁}^{t₀ + c₂} (t−t₀)⁻¹ = 0`.
- **What**: The linearized annular integrand `(t − t₀)⁻¹` cancels symmetrically across left/right wings.
- **How**: Direct application of `integral_inv_symm` (from `AnnulusBounds`) with positivity of `c₁, c₂` and `c₁ ≤ c₂` from `hε₂_pos`, `hε₂_le`.
- **Hypotheses**: `hL_pos`, `hε₂_pos`, `hε₂_le`.
- **Uses from project**: `integral_inv_symm` (from `AnnulusBounds`).
- **Used by**: `singular_annulus_lin_integral_zero`.
- **Visibility**: public.
- **Lines**: 106-119.
- **Notes**: short.

### `lemma singular_symmDiff_sup_bound`
- **Type**: For `0 < c` and `c ≤ |t − t₀|`: `‖((t − t₀ : ℝ) : ℂ)⁻¹‖ ≤ 1/c`.
- **What**: Norm bound `1/c` for the inverse complex coordinate when `|t − t₀| ≥ c`.
- **How**: `norm_inv`, `Complex.norm_real`, `Real.norm_eq_abs`, `one_div`, then `inv_anti₀ hc_pos ht_lower`.
- **Hypotheses**: `0 < c`, `c ≤ |t − t₀|`.
- **Uses from project**: [].
- **Used by**: `singular_annulus_f_lin_bound`, `singular_annulus_diff_pointwise_bound`.
- **Visibility**: public.
- **Lines**: 121-128.
- **Notes**: short.

### `private lemma singular_annulus_f_lin_measurable`
- **Type**: Measurability of `t ↦ if ε₂ < ‖L‖·|t−t₀| ∧ ‖L‖·|t−t₀| ≤ ε₁ then (t−t₀ : ℂ)⁻¹ else 0`.
- **What**: Measurability of the linearized annular indicator.
- **How**: `Measurable.ite` on the intersection of two measurable sets (an open `<` set and a closed `≤` set), with the inner function from `Complex.measurable_ofReal.comp ... .inv`.
- **Hypotheses**: implicit.
- **Uses from project**: [].
- **Used by**: `singular_annulus_f_lin_intervalIntegrable`, `singular_annulus_bound_explicit`.
- **Visibility**: private.
- **Lines**: 132-144.
- **Notes**: 13 lines.

### `private lemma singular_annulus_f_lin_bound`
- **Type**: `(hL_pos : 0 < ‖L‖) (hε₂_pos : 0 < ε₂) (t : ℝ) : ‖indicator t‖ ≤ 2·‖L‖/ε₂`.
- **What**: Uniform pointwise bound `2·‖L‖/ε₂` on the linearized annular indicator.
- **How**: Case split on the condition. In the `pos` branch: show `ε₂/(2·‖L‖) < |t − t₀|` from `ε₂/(2‖L‖) < ε₂/‖L‖ ≤ |t − t₀|`, then `singular_symmDiff_sup_bound` and `one_div, inv_div`. In the `neg` branch: zero, then `positivity`.
- **Hypotheses**: `hL_pos`, `hε₂_pos`.
- **Uses from project**: `singular_symmDiff_sup_bound`.
- **Used by**: `singular_annulus_f_lin_intervalIntegrable`, `singular_annulus_bound_explicit`.
- **Visibility**: private.
- **Lines**: 146-163.
- **Notes**: short (18 lines).

### `lemma singular_annulus_f_lin_intervalIntegrable`
- **Type**: `(hL_pos : 0 < ‖L‖) (hε₂_pos : 0 < ε₂) (u v : ℝ) : IntervalIntegrable (linearized annular indicator) volume u v`.
- **What**: The linearized annular indicator is integrable on any interval.
- **How**: `intervalIntegrable_iff`, then `MeasureTheory.IntegrableOn.of_bound` on the finite-volume `Ioc` using the measurability and uniform bound from the previous two lemmas.
- **Hypotheses**: `hL_pos`, `hε₂_pos`.
- **Uses from project**: `singular_annulus_f_lin_measurable`, `singular_annulus_f_lin_bound`.
- **Used by**: `singular_annulus_lin_integral_zero`.
- **Visibility**: public.
- **Lines**: 166-176.
- **Notes**: short.

### `private lemma lin_indicator_zero_left`
- **Type**: For `a < t₀ − c₂`, `φ` integrable on `[a, t₀ − c₂]`, `φ t = 0` when `¬(c₁ < |t − t₀| ∧ |t − t₀| ≤ c₂)`: `∫ a..(t₀ − c₂) φ = 0`.
- **What**: Left part of `(a, t₀ − c₂)` lies outside the annulus, so `φ` is a.e. zero.
- **How**: `intervalIntegral_eq_zero_of_ae_eq_zero` with an a.e.-zero hypothesis built via `filter_upwards` on the cocountable `{t₀ − c₂}ᶜ`; on `uIoc`, `t − t₀ ≤ 0`, so `|t − t₀| = −(t − t₀) > c₂`, contradicting the indicator's upper bound.
- **Hypotheses**: `_hc₂_nonneg`, `ha_lt_mc₂`, `hI`, `hφ_zero`.
- **Uses from project**: `intervalIntegral_eq_zero_of_ae_eq_zero`.
- **Used by**: `singular_annulus_lin_integral_zero`.
- **Visibility**: private.
- **Lines**: 181-195.
- **Notes**: 15 lines.

### `private lemma lin_indicator_zero_right`
- **Type**: Right wing analogue: `t ∈ (t₀ + c₂, b)` gives `|t − t₀| > c₂`, so `φ = 0`.
- **What**: Right part of `(t₀ + c₂, b)` is outside the annulus.
- **How**: Same scaffolding as `lin_indicator_zero_left` but with `t − t₀ ≥ 0`.
- **Hypotheses**: `_hc₂_nonneg`, `hpc₂_lt_b`, `hI`, `hφ_zero`.
- **Uses from project**: `intervalIntegral_eq_zero_of_ae_eq_zero`.
- **Used by**: `singular_annulus_lin_integral_zero`.
- **Visibility**: private.
- **Lines**: 198-208.
- **Notes**: 11 lines.

### `private lemma lin_indicator_zero_middle`
- **Type**: For `t ∈ (t₀ − c₁, t₀ + c₁)`: `|t − t₀| < c₁`, so the indicator is zero throughout.
- **What**: Middle part is fully inside the inner disk → indicator is zero everywhere.
- **How**: Replace the integrand by `0` pointwise on `uIcc` via `intervalIntegral.integral_congr` and `abs_le.mpr`; then `intervalIntegral.integral_zero`.
- **Hypotheses**: `hmc₁_le_pc₁`, `hφ_zero`.
- **Uses from project**: [].
- **Used by**: `singular_annulus_lin_integral_zero`.
- **Visibility**: private.
- **Lines**: 211-222.
- **Notes**: 12 lines.

### `private lemma lin_indicator_eq_inv_left`
- **Type**: On `(t₀ − c₂, t₀ − c₁)`: `φ t = (t − t₀ : ℂ)⁻¹`.
- **What**: Left annular wing: indicator equals the bare `(t − t₀)⁻¹`.
- **How**: `intervalIntegral.integral_congr_ae` plus `filter_upwards` on a cocountable `{t₀ − c₁}ᶜ`; verify `c₁ < |t − t₀| ≤ c₂` using `t − t₀ ≤ 0` and `abs_of_nonpos`.
- **Hypotheses**: `_hc₁_nonneg`, `hmc₂_le_mc₁`, `hφ_val`.
- **Uses from project**: [].
- **Used by**: `singular_annulus_lin_integral_zero`.
- **Visibility**: private.
- **Lines**: 225-241.
- **Notes**: 17 lines.

### `private lemma lin_indicator_eq_inv_right`
- **Type**: On `(t₀ + c₁, t₀ + c₂)`: `φ t = (t − t₀ : ℂ)⁻¹`.
- **What**: Right annular wing: indicator equals `(t − t₀)⁻¹`.
- **How**: Mirror of `lin_indicator_eq_inv_left` with `t − t₀ ≥ 0` and `abs_of_nonneg`.
- **Hypotheses**: `_hc₁_nonneg`, `hpc₁_le_pc₂`, `hφ_val`.
- **Uses from project**: [].
- **Used by**: `singular_annulus_lin_integral_zero`.
- **Visibility**: private.
- **Lines**: 244-255.
- **Notes**: 12 lines.

### `private lemma singular_annulus_lin_integral_zero`
- **Type**: For `hL_pos`, `0 < ε₂ ≤ ε₁`, `ε₁ < ‖L‖ · min(t₀ − a, b − t₀)`, `t₀ ∈ Ioo a b`: `∫ a..b, (linearized indicator) = 0`.
- **What**: Linearized annular integral vanishes by symmetric cancellation across the five-way split.
- **How**: KEY: `integral_split_five` decomposes the integral at `a < t₀ − c₂ < t₀ − c₁ < t₀ + c₁ < t₀ + c₂ < b`. Outer wings vanish via `lin_indicator_zero_left/right` (outside the annulus), middle vanishes via `lin_indicator_zero_middle` (inside the inner disk), and the two annular wings combine via `lin_indicator_eq_inv_left/right` + `singular_tAnnLin_cancel`. Uses `norm_annulus_condition_iff` to translate between `‖L‖·|t − t₀|` and `|t − t₀|/‖L‖` formulations.
- **Hypotheses**: `hL_pos`, `_hε₁_pos`, `hε₂_pos`, `hε₂_le`, `hε₁_lt_Ldist`, `_hat₀`.
- **Uses from project**: `norm_annulus_condition_iff`, `singular_annulus_f_lin_intervalIntegrable`, `integral_split_five`, `lin_indicator_zero_left`, `lin_indicator_zero_right`, `lin_indicator_zero_middle`, `lin_indicator_eq_inv_left`, `lin_indicator_eq_inv_right`, `singular_tAnnLin_cancel`.
- **Used by**: `singular_annulus_bound_explicit`.
- **Visibility**: private.
- **Lines**: 257-297.
- **Notes**: 41 lines.

### `private lemma singular_annulus_diff_pointwise_bound`
- **Type**: For curve indicator `‖γ−γ₀‖`-form vs linear `‖L‖·|t−t₀|`-form: pointwise norm of the difference is `≤ 2·‖L‖/ε₂`.
- **What**: Pointwise bound on the difference between the two annular indicators.
- **How**: Four-way case split on whether the curve condition and the linear condition hold. (a) both true: difference is `0`. (b) curve true, linear false: bound via `h_upper` (curve-vs-line upper bound) giving `ε₂/(2‖L‖) ≤ |t − t₀|`, then `singular_symmDiff_sup_bound`. (c) curve false, linear true: directly `ε₂/(2‖L‖) ≤ |t − t₀|` from the linear inequality, then `singular_symmDiff_sup_bound`. (d) both false: difference is `0`.
- **Hypotheses**: `hL_pos`, `hε₂_pos`, `h_localize`, `hδ₁_le_δ_up`, `h_upper`, `t ∈ Icc a b`.
- **Uses from project**: `singular_symmDiff_sup_bound`.
- **Used by**: `singular_annulus_bound_explicit`.
- **Visibility**: private.
- **Lines**: 301-355.
- **Notes**: 55 lines (long).

### `private lemma symmDiff_ae_version_null`
- **Type**: If `h' =ᵐ ‖γ − γ₀‖` on `Icc a b`, the symmetric difference of the corresponding sets has measure zero.
- **What**: AE-version equivalence: replacing `‖γ − γ₀‖` with an a.e.-equal `h'` doesn't change set measure (modulo null sets).
- **How**: Cover the symmetric difference by `{t | t ∈ Icc a b ∧ h' t ≠ ‖γ − γ₀‖ t}`; rewrite this as `{¬(‖γ−γ₀‖ = h')} ∩ Icc a b`, which by `MeasureTheory.Measure.restrict_apply'` and `ae_iff` has measure zero.
- **Hypotheses**: `hh'_ae`.
- **Uses from project**: [].
- **Used by**: `singular_annulus_symmDiff_vol_via_ae`.
- **Visibility**: private.
- **Lines**: 361-384.
- **Notes**: 24 lines.

### `private lemma singular_annulus_symmDiff_vol_via_ae`
- **Type**: Promotes the volume bound from `‖γ − γ₀‖`-annulus → `‖L‖·|t−t₀|`-annulus to the `h'`-annulus → `‖L‖·|t−t₀|`-annulus, using a.e. equality.
- **What**: Triangle inequality for `volume(symmDiff)` to swap `‖γ − γ₀‖` with an a.e.-equal `h'`.
- **How**: `MeasureTheory.measure_symmDiff_le` (triangle inequality on symm-diff measures), then `symmDiff_ae_version_null` for the first term, and the supplied bound `h_meas` for the second.
- **Hypotheses**: `hε₂_pos`, `hε₂_le`, `hε₁_lt_δ_meas`, `h_meas`, `hh'_ae`.
- **Uses from project**: `symmDiff_ae_version_null`.
- **Used by**: `singular_annulus_bound_explicit`.
- **Visibility**: private.
- **Lines**: 386-422.
- **Notes**: 37 lines.

### `lemma singular_annulus_bound_explicit`
- **Type**: For `a < b`, `t₀ ∈ Ioo a b`, `γ` `C^2` at `t₀` with `deriv γ t₀ = L ≠ 0`, continuous on `Icc a b`, locally injective at `t₀`: there exist `Csing > 0` and `δ > 0` such that for all `ε₁, ε₂` with `0 < ε₂ ≤ ε₁ ≤ 2·ε₂ < δ`, the singular annular integral has norm `≤ Csing · ε₁`.
- **What**: Epsilon-independent (up to factor `Csing`) bound on the singular annular integral in the curve-PV setting.
- **How**: KEY: Combines several auxiliary bounds: (1) `annulus_symmDiff_measure_bound` (from `AnnulusBounds`) gives a volume bound on the symmetric difference between `γ`-annulus and linearized annulus. (2) `gamma_lower_bound_of_hasDerivAt` and `gamma_upper_bound_of_hasDerivAt` give two-sided bounds for `‖γ − γ₀‖` vs `‖L‖·|t − t₀|`. (3) `no_return_of_inj_continuous` (localization radius) keeps `|t − t₀| < δ₁` whenever `‖γ − γ₀‖ ≤ ε₁`. (4) Set `Csing := 4·Kmeas/‖L‖²`, define `f_γ`, `f_lin`, `d := f_γ − f_lin`. (5) Show `f_γ = d + f_lin`; the `f_lin` integral vanishes by `singular_annulus_lin_integral_zero`. (6) Bound `∫ d` via `MeasureTheory.norm_integral_le_of_norm_le` applied to `g_comp := S'.indicator (fun _ => bound)`, where `S'` is the symmetric difference. (7) Replace `f_γ` with a strongly-measurable version `f_γ'` using `h_norm_aesm.mk` and `h_norm_aesm.ae_eq_mk`. (8) `singular_annulus_symmDiff_vol_via_ae` gives `volume S' ≤ ENNReal.ofReal (Kmeas·ε₁²/‖L‖³)`. (9) Final arithmetic: `Kmeas·ε₁²/‖L‖³ · (2·‖L‖/ε₂) ≤ 4·Kmeas/‖L‖² · ε₁` using `ε₁ ≤ 2ε₂`, closed by `nlinarith`.
- **Hypotheses**: `hab`, `hat₀`, `hγ_C2`, `hγ_deriv`, `hL`, `hγ_cont`, `h_inj`.
- **Uses from project**: `annulus_symmDiff_measure_bound`, `gamma_lower_bound_of_hasDerivAt`, `gamma_upper_bound_of_hasDerivAt`, `no_return_of_inj_continuous` (all from `AnnulusBounds`), `singular_annulus_f_lin_measurable`, `singular_annulus_f_lin_bound`, `singular_annulus_lin_integral_zero`, `singular_annulus_diff_pointwise_bound`, `singular_annulus_symmDiff_vol_via_ae`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 424-762.
- **Notes**: 339 lines (very long, single proof block). The headline theorem of the file.

## File Summary

- **Total declarations**: 19 (1 private instance, 18 lemmas: 7 public + 11 private).
- **Key API**: `singular_tAnnLin_cancel`, `singular_annulus_lin_integral_zero` (private), `singular_annulus_bound_explicit` (headline). Public reusable helpers: `norm_annulus_condition_iff`, `intervalIntegral_eq_zero_of_ae_eq_zero`, `integral_split_five`, `singular_tAnnLin_inside_interval`, `singular_symmDiff_sup_bound`, `singular_annulus_f_lin_intervalIntegrable`.
- **Unused in file**: `singular_tAnnLin_inside_interval`, `singular_annulus_bound_explicit` (these are the file's outward-facing reusable lemmas — used downstream in the dyadic PV convergence proof).
- **Sorries**: 0.
- **`set_option` lines**: 0.
- **Long proofs (>30 lines)**: `singular_annulus_lin_integral_zero` (41), `singular_annulus_diff_pointwise_bound` (55), `symmDiff_ae_version_null` (24, just under), `singular_annulus_symmDiff_vol_via_ae` (37), `singular_annulus_bound_explicit` (339).
- **Purpose**: Provides the singular-annulus bounds used in the dyadic principal-value (PV) convergence proof for `(t − t₀)⁻¹`-type integrands. The headline lemma `singular_annulus_bound_explicit` bounds the curve-PV-style integral `∫_a^b (annulus indicator) · (t − t₀)⁻¹ dt` by `Csing · ε₁`, with `Csing` and `δ` depending only on the curve `γ`'s `C²`-data and local injectivity (not on `ε₁, ε₂`). The proof strategy is: subtract a linearized model (whose integral vanishes by exact symmetric cancellation `singular_tAnnLin_cancel`), then bound the difference between the curve annulus and the linearized annulus by a measure-theoretic symmetric-difference estimate (`annulus_symmDiff_measure_bound`, supplied from `AnnulusBounds`). All ε-uniform bounds and a.e. measurability gymnastics are kept private; the file exposes a clean explicit-bound API.
