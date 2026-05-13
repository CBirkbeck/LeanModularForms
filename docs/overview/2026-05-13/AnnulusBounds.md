# AnnulusBounds.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/PVInfrastructure/AnnulusBounds.lean` (554 lines)

### `instance : NormSMulClass ℝ ℂ`
- **Type**: `NormSMulClass ℝ ℂ`
- **What**: Provides the `NormSMulClass` instance for real scaling of complex numbers (norm of `r • z` equals `|r| * ‖z‖`).
- **How**: Delegates to `NormedSpace.toNormSMulClass`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: Used implicitly by downstream lemmas needing `‖r • L‖ = |r| * ‖L‖`.
- **Visibility**: private
- **Lines**: 30
- **Notes**: Instance declaration.

### `lemma annulus_t_measure_bound`
- **Type**: `{γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ} {ε₁ ε₂ δ₁ : ℝ} → L ≠ 0 → 0 < ε₁ → (∀ t, 0 < |t - t₀| → |t - t₀| < δ₁ → ‖γ t - γ t₀‖ ≥ (‖L‖/2) * |t - t₀|) → (∀ t ∈ [a,b], ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₁ δ₁) → (t : ℝ) → t ∈ [a,b] → t ≠ t₀ → ε₂ < ‖γ t - γ t₀‖ → ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| ≤ 2*ε₁/‖L‖`
- **What**: Points in the gamma-annulus `{ε₂ < ‖γ t - γ t₀‖ ≤ ε₁}` lie within `t`-distance `2ε₁/‖L‖` of `t₀`.
- **How**: Localizes `|t - t₀| < δ₁`, uses `abs_pos.mpr` for positivity, applies `t_bound_from_gamma_annulus`.
- **Hypotheses**: `L ≠ 0`, lower linear approximation `‖γ t - γ t₀‖ ≥ ‖L‖/2 |t - t₀|`, localization estimate, `ε₁ > 0`.
- **Uses from project**: `t_bound_from_gamma_annulus`
- **Used by**: `remainder_annulus_zero_of_far`
- **Visibility**: public
- **Lines**: 34-44
- **Notes**: None.

### `private lemma remainder_annulus_zero_of_far`
- **Type**: `{γ : ℝ → ℂ} {a b t₀ : ℝ} {δ₁ ε₁ ε₂ : ℝ} {L : ℂ} → L ≠ 0 → 0 < ε₁ → 0 < ε₂ → (lower-bound hyp) → (localize hyp) → a < b → {r : ℝ → ℂ} (t : ℝ) → t ∈ Ι a b → 2*ε₁/‖L‖ < |t - t₀| → (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0) = 0`
- **What**: The indicator integrand is zero far from `t₀` (outside the radius `2ε₁/‖L‖`).
- **How**: Case on whether `t` is in the annulus; if so, derive contradiction with `annulus_t_measure_bound` by showing `|t - t₀|` is too small to be `> 2ε₁/‖L‖`. Handles boundary `t = t₀` via `hε₂_pos`.
- **Hypotheses**: `L ≠ 0`, `ε₁, ε₂ > 0`, lower-bound, localization, `a < b`.
- **Uses from project**: `annulus_t_measure_bound`
- **Used by**: `remainder_integral_bound_on_annulus`
- **Visibility**: private
- **Lines**: 48-70
- **Notes**: >10 lines (23 lines).

### `private lemma remainder_annulus_pw_bound`
- **Type**: `{γ : ℝ → ℂ} {a b t₀ : ℝ} {C δ₀ δ₁ ε₁ ε₂ : ℝ} → 0 < ε₂ → (∀ t, 0 < |t - t₀| → |t - t₀| < δ₀ → ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ C) → (∀ t ∈ [a,b], ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₀ δ₁) → a < b → (t : ℝ) → t ∈ Ι a b → ‖if … then … else 0‖ ≤ max 0 C`
- **What**: Pointwise bound on the indicator integrand by `max 0 C` on the integration interval.
- **How**: Case on annulus membership; outside it the integrand is 0 (use `le_max_right`); inside, use `hr_bounded` after localizing to `|t - t₀| < δ₀`.
- **Hypotheses**: `ε₂ > 0`, remainder pointwise bound on punctured neighborhood, localization, `a < b`.
- **Uses from project**: []
- **Used by**: `remainder_integral_bound_on_annulus`
- **Visibility**: private
- **Lines**: 73-96
- **Notes**: >10 lines (24 lines).

### `lemma remainder_integral_bound_on_annulus`
- **Type**: `{γ : ℝ → ℂ} {a b t₀ : ℝ} {C δ₀ δ₁ ε₁ ε₂ : ℝ} {L : ℂ} → L ≠ 0 → 0 < ε₁ → 0 < ε₂ → (rem-bound) → (lower-bound) → (localize) → t₀ ∈ Ioo a b → ‖∫_a^b (if … then r t else 0)‖ ≤ max 0 C * (4*ε₁/‖L‖)`
- **What**: The integral of the indicator remainder over `[a, b]` is `O(ε₁)`, specifically `≤ (max 0 C) · (4ε₁/‖L‖)`.
- **How**: Builds an `Icc`-indicator dominator `g_comp`, applies `intervalIntegral.norm_integral_le_of_norm_le` with the pointwise bound from `remainder_annulus_pw_bound` and zero-far bound from `remainder_annulus_zero_of_far`; computes `volume Icc = 2 * (2ε₁/‖L‖)`.
- **Hypotheses**: `L ≠ 0`, `ε₁, ε₂ > 0`, remainder bound on punctured neighborhood, linear lower bound on gamma, localization, `t₀ ∈ (a, b)`.
- **Uses from project**: `remainder_annulus_pw_bound`, `remainder_annulus_zero_of_far`
- **Used by**: Headline result; used by downstream PV convergence.
- **Visibility**: public
- **Lines**: 98-161
- **Notes**: >10 lines (64 lines).

### `lemma norm_linear_approx_bound`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {K₀ δ₀ : ℝ} → (∀ t, |t - t₀| < δ₀ → ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ K₀ * |t - t₀|^2) → |t - t₀| < δ₀ → abs(‖γ t - γ t₀‖ - ‖L‖ * |t - t₀|) ≤ K₀ * |t - t₀|^2`
- **What**: Quadratic remainder bound: the difference between `‖γ(t) - γ(t₀)‖` and the linear model `‖L‖·|t - t₀|` is `O(|t - t₀|²)`.
- **How**: Applies `abs_norm_sub_norm_le` (reverse triangle inequality) and `norm_smul`, then transitivity.
- **Hypotheses**: Quadratic remainder hypothesis for `γ`.
- **Uses from project**: []
- **Used by**: `annulus_symmDiff_measure_bound`
- **Visibility**: public
- **Lines**: 163-172
- **Notes**: None.

### `lemma volume_shell_le`
- **Type**: `{t₀ r₁ r₂ : ℝ} → r₁ ≤ r₂ → volume {t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} ≤ ENNReal.ofReal (2 * (r₂ - r₁))`
- **What**: The measure of the annular shell `{r₁ < |t - t₀| ≤ r₂}` is at most `2(r₂ - r₁)`.
- **How**: Splits the shell into two intervals `Ico (t₀ - r₂) (t₀ - r₁) ∪ Ioc (t₀ + r₁) (t₀ + r₂)` via sign cases on `t - t₀`, applies `measure_union_le` and `Real.volume_Ico/Ioc`.
- **Hypotheses**: `r₁ ≤ r₂`.
- **Uses from project**: []
- **Used by**: `shell_vol_le_of_large_eps`
- **Visibility**: public
- **Lines**: 174-199
- **Notes**: >10 lines (26 lines).

### `lemma symmDiff_subset_boundaryLayers`
- **Type**: `{g x e ε₁ ε₂ : ℝ} → |g - x| ≤ e → Xor' (ε₂ < g ∧ g ≤ ε₁) (ε₂ < x ∧ x ≤ ε₁) → |x - ε₂| ≤ e ∨ |x - ε₁| ≤ e`
- **What**: If `g` and `x` differ by ≤ e and they disagree on annulus membership, then `x` is within `e` of one of the threshold values `ε₁, ε₂`.
- **How**: Case split on Xor and on which side `x` falls; in each case bound `|x - εᵢ|` via the chain `x - εᵢ ≤ g - x ≤ |g - x| ≤ e` (or symmetric form).
- **Hypotheses**: Linear approximation bound and exclusive-or annulus condition.
- **Uses from project**: []
- **Used by**: `annulus_symmDiff_measure_bound`
- **Visibility**: public
- **Lines**: 201-260
- **Notes**: >10 lines (60 lines).

### `lemma tAnnLin_implies_r_le`
- **Type**: `{L_norm r ε₁ : ℝ} → 0 < L_norm → L_norm * r ≤ ε₁ → r ≤ ε₁ / L_norm`
- **What**: Standard division-bound: from `L·r ≤ ε₁` and `L > 0`, conclude `r ≤ ε₁/L`.
- **How**: Apply `le_div_iff₀ hL_pos` after `mul_comm`.
- **Hypotheses**: `L_norm > 0`, `L_norm * r ≤ ε₁`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 262-267
- **Notes**: None.

### `lemma near_threshold_implies_r_in_shell`
- **Type**: `{L_norm r ε K₀ R_max : ℝ} → 0 < L_norm → 0 ≤ K₀ → 0 ≤ R_max → r ≤ R_max → 0 ≤ r → |L_norm * r - ε| ≤ K₀ * r^2 → (ε - K₀*R_max^2)/L_norm ≤ r ∧ r ≤ (ε + K₀*R_max^2)/L_norm`
- **What**: If `r ∈ [0, R_max]` and `L·r ≈ ε` with quadratic error `K₀ r²`, then `r` is in an annular shell around `ε/L`.
- **How**: From `abs_le.mp h_near` derive two-sided bound `ε - K₀ r² ≤ L r ≤ ε + K₀ r²`, then upgrade with `r² ≤ R_max²` via `mul_le_mul_of_nonneg_left`.
- **Hypotheses**: `L_norm > 0`, `K₀, R_max, r ≥ 0`, `r ≤ R_max`, near-threshold quadratic bound.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 269-288
- **Notes**: >10 lines (20 lines).

### `private lemma shell_vol_le_of_small_eps`
- **Type**: `{t₀ ε Δ L_norm : ℝ} → 0 < L_norm → 0 ≤ Δ → ε ≤ Δ → volume {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ≤ ENNReal.ofReal (4Δ/L_norm)`
- **What**: When `ε ≤ Δ`, the shell `{|L·|t - t₀| - ε| ≤ Δ}` is contained in a ball of radius `(ε+Δ)/L`, so its measure is `≤ 4Δ/L`.
- **How**: Build subset to `{|t - t₀| ≤ (ε+Δ)/L}` by dividing by `L_norm`, identify with closed interval, compute `Real.volume_Icc`, then bound `2(ε+Δ) ≤ 4Δ`.
- **Hypotheses**: `L_norm > 0`, `Δ ≥ 0`, `ε ≤ Δ`.
- **Uses from project**: []
- **Used by**: `shell_vol_le`
- **Visibility**: private
- **Lines**: 290-317
- **Notes**: >10 lines (28 lines).

### `private lemma volume_abs_eq_null`
- **Type**: `{t₀ r₁ : ℝ} → 0 < r₁ → volume {t : ℝ | |t - t₀| = r₁} = 0`
- **What**: The level set `{|t - t₀| = r₁}` for `r₁ > 0` has measure zero (it consists of at most 2 points `{t₀ ± r₁}`).
- **How**: Subset into `{t₀ - r₁, t₀ + r₁}` via `abs_eq`, then `Set.toFinite _).measure_zero`.
- **Hypotheses**: `r₁ > 0`.
- **Uses from project**: []
- **Used by**: `shell_vol_le_of_large_eps`
- **Visibility**: private
- **Lines**: 319-333
- **Notes**: >10 lines (15 lines).

### `private lemma shell_vol_le_of_large_eps`
- **Type**: `{t₀ ε Δ L_norm : ℝ} → 0 < L_norm → 0 ≤ Δ → Δ < ε → volume {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ≤ ENNReal.ofReal (4Δ/L_norm)`
- **What**: When `Δ < ε`, the shell is an annulus with width `2Δ/L`, measure `≤ 4Δ/L`.
- **How**: Build subset chain: shell ⊆ `{r₁ ≤ |t - t₀| ≤ r₂}` ⊆ `{r₁ < … ≤ r₂} ∪ {|t - t₀| = r₁}`; apply `volume_shell_le` and `volume_abs_eq_null`.
- **Hypotheses**: `L_norm > 0`, `Δ ≥ 0`, `Δ < ε`.
- **Uses from project**: `volume_shell_le`, `volume_abs_eq_null`
- **Used by**: `shell_vol_le`
- **Visibility**: private
- **Lines**: 336-375
- **Notes**: >10 lines (40 lines).

### `lemma shell_vol_le`
- **Type**: `{t₀ ε Δ L_norm : ℝ} → 0 < L_norm → 0 ≤ Δ → 0 < ε → volume {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ≤ ENNReal.ofReal (4Δ/L_norm)`
- **What**: Unified shell-volume bound `≤ 4Δ/L` regardless of relative magnitudes of `ε` and `Δ`.
- **How**: Case split on `ε ≤ Δ` (small) vs `Δ < ε` (large), delegate to private helpers.
- **Hypotheses**: `L_norm > 0`, `Δ ≥ 0`, `ε > 0`.
- **Uses from project**: `shell_vol_le_of_small_eps`, `shell_vol_le_of_large_eps`
- **Used by**: `annulus_symmDiff_measure_bound`
- **Visibility**: public
- **Lines**: 377-382
- **Notes**: None.

### `lemma annulus_symmDiff_measure_bound`
- **Type**: `{γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ} → a < b → t₀ ∈ Ioo a b → ContDiffAt ℝ 2 γ t₀ → deriv γ t₀ = L → L ≠ 0 → ∃ K > 0, ∃ δ₀' > 0, ∃ δ > 0, ∀ ε₁ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ ε₁ → ε₁ < δ → volume (symmDiff γAnn tAnnLin) ≤ ENNReal.ofReal (K * ε₁^2 / ‖L‖^3)`
- **What**: The symmetric difference between the true gamma-annulus and the linear-model annulus has measure `O(ε₁²/‖L‖³)`.
- **How**: Uses `quadratic_approx_of_contDiffAt_two` to extract `K₀` and `δ₀`. Chooses scale `δ₁ := min δ₀ (‖L‖/(4 K₀))`. For each `t` in the symmetric difference, applies `norm_linear_approx_bound` to bound `|‖γ(t) - γ(t₀)‖ - ‖L‖·|t - t₀||`, then `symmDiff_subset_boundaryLayers` to conclude `t` lies in one of two shell layers around `ε₁` or `ε₂`. Both shells have measure `≤ 4Δ/‖L‖` by `shell_vol_le`, with `Δ = K₀ · (2ε₁/‖L‖)²`.
- **Hypotheses**: `a < b`, `t₀ ∈ (a, b)`, `ContDiffAt ℝ 2 γ t₀`, `deriv γ t₀ = L`, `L ≠ 0`.
- **Uses from project**: `quadratic_approx_of_contDiffAt_two`, `norm_linear_approx_bound`, `symmDiff_subset_boundaryLayers`, `shell_vol_le`
- **Used by**: Headline result for downstream PV convergence; used externally.
- **Visibility**: public
- **Lines**: 384-551
- **Notes**: >10 lines (168 lines). Heavy proof.

## File Summary

This file establishes measure-theoretic and analytic estimates on annular regions around a crossing point `t₀` of a `C²` curve `γ : ℝ → ℂ`, central to dyadic principal-value convergence. Headline results: `annulus_t_measure_bound` (linear lower bound implies `|t - t₀| ≤ 2ε/‖L‖`), `remainder_integral_bound_on_annulus` (annulus integral is `O(ε)`), `shell_vol_le` (unified shell volume `≤ 4Δ/L`), and `annulus_symmDiff_measure_bound` (curved vs. linear annulus symmetric difference is `O(ε²/‖L‖³)`). The file uses three private helper lemmas (`remainder_annulus_zero_of_far`, `remainder_annulus_pw_bound`, `volume_abs_eq_null`, `shell_vol_le_of_small/large_eps`) for clean main statements. Total: 14 declarations + 1 instance. No `sorry`, no axioms, no `set_option`.
