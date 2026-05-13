# HW-ExitTimeExcision.md

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HungerbuhlerWasem/ExitTimeExcision.lean` (423 lines)

Namespace: `HungerbuhlerWasem`

### `theorem cpvIntegrandOn_singleton_eq_contour_of_far`
- **Type**: `(γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε : ℝ} {t : ℝ} (h_far : ε < ‖γ.toPath.extend t - s‖) : cpvIntegrandOn {s} f γ.toPath.extend ε t = f (γ.toPath.extend t) * deriv γ.toPath.extend t`
- **What**: When γ(t) is more than ε away from singleton pole s, the CPV integrand equals the bare contour integrand `f(γ t)·γ'(t)`.
- **How**: Direct application of `cpvIntegrandOn_of_forall_gt`, peeling singleton membership via `Finset.mem_singleton.mp`.
- **Hypotheses**: ε strictly less than `‖γ(t) - s‖`.
- **Uses from project**: `PiecewiseC1Path`, `cpvIntegrandOn`, `cpvIntegrandOn_of_forall_gt`.
- **Used by**: `cpvIntegrandOn_singleton_eq_indicator`, `integral_cpvIntegrandOn_singleton_eq_contour_left`, `integral_cpvIntegrandOn_singleton_eq_contour_right`.
- **Visibility**: public
- **Lines**: 63-70
- **Notes**: none

### `theorem cpvIntegrandOn_singleton_eq_zero_of_close`
- **Type**: `(γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε : ℝ} {t : ℝ} (h_close : ‖γ.toPath.extend t - s‖ ≤ ε) : cpvIntegrandOn {s} f γ.toPath.extend ε t = 0`
- **What**: When γ(t) is within ε of singleton pole s, the CPV integrand is 0.
- **How**: Direct application of `cpvIntegrandOn_of_exists_le` with witness `s ∈ {s}`.
- **Hypotheses**: `‖γ(t) - s‖ ≤ ε`.
- **Uses from project**: `PiecewiseC1Path`, `cpvIntegrandOn`, `cpvIntegrandOn_of_exists_le`.
- **Used by**: `cpvIntegrandOn_singleton_eq_indicator`, `integral_cpvIntegrandOn_singleton_eq_zero_middle`.
- **Visibility**: public
- **Lines**: 73-77
- **Notes**: none

### `theorem cpvIntegrandOn_singleton_eq_indicator`
- **Type**: `(γ : PiecewiseC1Path x x) (s : ℂ) (f : ℂ → ℂ) (ε : ℝ) (t : ℝ) : cpvIntegrandOn {s} f γ.toPath.extend ε t = ({t | ε < ‖γ.toPath.extend t - s‖}.indicator (fun t => f (γ.toPath.extend t) * deriv γ.toPath.extend t)) t`
- **What**: Pointwise, the CPV integrand for a singleton equals the "far from s" indicator times the contour integrand.
- **How**: Case split on `ε < ‖γ(t) - s‖`; far case uses `indicator_of_mem` + `cpvIntegrandOn_singleton_eq_contour_of_far`, close case uses `indicator_of_notMem` + `cpvIntegrandOn_singleton_eq_zero_of_close`.
- **Hypotheses**: none.
- **Uses from project**: `PiecewiseC1Path`, `cpvIntegrandOn`, `cpvIntegrandOn_singleton_eq_contour_of_far`, `cpvIntegrandOn_singleton_eq_zero_of_close`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 82-92
- **Notes**: none

### `theorem integral_cpvIntegrandOn_singleton_eq_contour_left`
- **Type**: `(γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε α : ℝ} (hα : 0 ≤ α) (h_outside : ∀ t ∈ Ioo (0 : ℝ) α, ε < ‖γ.toPath.extend t - s‖) : ∫ t in (0 : ℝ)..α, cpvIntegrandOn {s} f γ.toPath.extend ε t = ∫ t in (0 : ℝ)..α, f (γ.toPath.extend t) * deriv γ.toPath.extend t`
- **What**: Over `[0, α]` where γ stays ε-far from s on `(0, α)`, the CPV-integrand integral equals the contour-integrand integral.
- **How**: Reduce both sides to `Ioo` via `integral_Ioc_eq_integral_Ioo`, then `setIntegral_congr_fun` using `cpvIntegrandOn_singleton_eq_contour_of_far`.
- **Hypotheses**: `0 ≤ α`; far condition on open `(0, α)`.
- **Uses from project**: `PiecewiseC1Path`, `cpvIntegrandOn`, `cpvIntegrandOn_singleton_eq_contour_of_far`.
- **Used by**: `cpvIntegrandOn_singleton_integral_eq_excision`.
- **Visibility**: public
- **Lines**: 99-108
- **Notes**: none

### `theorem integral_cpvIntegrandOn_singleton_eq_contour_right`
- **Type**: `(γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε β : ℝ} (hβ : β ≤ 1) (h_outside : ∀ t ∈ Ioo β (1 : ℝ), ε < ‖γ.toPath.extend t - s‖) : ∫ t in β..(1 : ℝ), cpvIntegrandOn {s} f γ.toPath.extend ε t = ∫ t in β..(1 : ℝ), f (γ.toPath.extend t) * deriv γ.toPath.extend t`
- **What**: Mirror of left version: on `[β, 1]` with γ ε-far on `(β, 1)`, CPV integrand integral equals contour integrand integral.
- **How**: Same as left: `Ioc → Ioo` conversion and `setIntegral_congr_fun` with `cpvIntegrandOn_singleton_eq_contour_of_far`.
- **Hypotheses**: `β ≤ 1`; far condition on open `(β, 1)`.
- **Uses from project**: `PiecewiseC1Path`, `cpvIntegrandOn`, `cpvIntegrandOn_singleton_eq_contour_of_far`.
- **Used by**: `cpvIntegrandOn_singleton_integral_eq_excision`.
- **Visibility**: public
- **Lines**: 112-120
- **Notes**: none

### `theorem integral_cpvIntegrandOn_singleton_eq_zero_middle`
- **Type**: `(γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε α β : ℝ} (h_le : α ≤ β) (h_inside : ∀ t ∈ Ioo α β, ‖γ.toPath.extend t - s‖ ≤ ε) : ∫ t in α..β, cpvIntegrandOn {s} f γ.toPath.extend ε t = 0`
- **What**: On `[α, β]` where γ stays within ε of s on `(α, β)`, the CPV-integrand integral is 0.
- **How**: `Ioc → Ioo` reduction, then `setIntegral_congr_fun` rewriting integrand to 0 via `cpvIntegrandOn_singleton_eq_zero_of_close`; finish with `simp`.
- **Hypotheses**: `α ≤ β`; close condition on open `(α, β)`.
- **Uses from project**: `PiecewiseC1Path`, `cpvIntegrandOn`, `cpvIntegrandOn_singleton_eq_zero_of_close`.
- **Used by**: `cpvIntegrandOn_singleton_integral_eq_excision`.
- **Visibility**: public
- **Lines**: 124-132
- **Notes**: none

### `theorem cpvIntegrandOn_singleton_integral_eq_excision`
- **Type**: `(γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε : ℝ} {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) (h_le : α ≤ β) (h_outside_left : ∀ t ∈ Ioo (0 : ℝ) α, ε < ‖γ.toPath.extend t - s‖) (h_outside_right : ∀ t ∈ Ioo β (1 : ℝ), ε < ‖γ.toPath.extend t - s‖) (h_inside : ∀ t ∈ Ioo α β, ‖γ.toPath.extend t - s‖ ≤ ε) (h_int_full : IntervalIntegrable (fun t => cpvIntegrandOn {s} f γ.toPath.extend ε t) volume 0 1) : ∫ t in (0:ℝ)..1, cpvIntegrandOn {s} f γ.toPath.extend ε t = (∫ t in (0:ℝ)..α, f (γ.toPath.extend t) * deriv γ.toPath.extend t) + ∫ t in β..(1:ℝ), f (γ.toPath.extend t) * deriv γ.toPath.extend t`
- **What**: Under the standard shape hypothesis (γ far on `(0,α) ∪ (β,1)`, close on `(α,β)`), the CPV integrand integral on `[0,1]` equals the symmetric-excision contour integral on `[0,α] ∪ [β,1]`.
- **How**: Splits the full integral into three adjacent pieces using `integral_add_adjacent_intervals` (twice), each piece via `IntervalIntegrable.mono_set` with `Icc_subset_Icc`; then applies the three earlier "left/middle/right" lemmas. Key lemma: `intervalIntegral.integral_add_adjacent_intervals`.
- **Hypotheses**: 0 ≤ α ≤ β ≤ 1; outside-left/right and inside conditions; full integrability.
- **Uses from project**: `PiecewiseC1Path`, `cpvIntegrandOn`, `integral_cpvIntegrandOn_singleton_eq_contour_left`, `integral_cpvIntegrandOn_singleton_eq_zero_middle`, `integral_cpvIntegrandOn_singleton_eq_contour_right`.
- **Used by**: `hasCauchyPVOn_singleton_of_excision_tendsto`.
- **Visibility**: public
- **Lines**: 136-176
- **Notes**: >30 lines.

### `theorem hasCauchyPVOn_singleton_of_excision_tendsto`
- **Type**: `(γ : PiecewiseC1Path x x) (s : ℂ) (f : ℂ → ℂ) (α β : ℝ → ℝ) (h_shape : ∀ᶠ ε in 𝓝[>] 0, 0 ≤ α ε ∧ β ε ≤ 1 ∧ α ε ≤ β ε ∧ … shape conditions) (h_int_full : ∀ᶠ ε, IntervalIntegrable …) (h_excision : Tendsto (excision integral) (𝓝[>] 0) (𝓝 0)) : HasCauchyPVOn {s} f γ 0`
- **What**: Bridge from parametric symmetric-excision PV to `HasCauchyPVOn {s} f γ 0`: if the excision integral tends to 0 and the shape holds eventually, then γ has CPV 0.
- **How**: Uses `h_excision.congr'` to rewrite the limit of CPV integrals as the (negated) excision form via `cpvIntegrandOn_singleton_integral_eq_excision` applied under the `filter_upwards` for shape and integrability.
- **Hypotheses**: parametric shape eventually; CPV integrand interval-integrable eventually; excision integral → 0.
- **Uses from project**: `PiecewiseC1Path`, `HasCauchyPVOn`, `cpvIntegrandOn`, `cpvIntegrandOn_singleton_integral_eq_excision`.
- **Used by**: `hasCauchyPVOn_singleton_of_exitTime_excision`.
- **Visibility**: public
- **Lines**: 191-209
- **Notes**: none

### `theorem hasCauchyPVOn_singleton_of_exitTime_excision`
- **Type**: `(γ : PiecewiseC1Path x x) (s : ℂ) (f : ℂ → ℂ) {t₀ δMinus δPlus : ℝ} (h_shape) (h_int_full) (h_excision) : HasCauchyPVOn {s} f γ 0` where the exit times are `firstExitTimeLeft` and `firstExitTimeRight`.
- **What**: Specialization of `hasCauchyPVOn_singleton_of_excision_tendsto` using the canonical exit-time functions α = `firstExitTimeLeft` and β = `firstExitTimeRight`.
- **How**: Direct invocation of `hasCauchyPVOn_singleton_of_excision_tendsto` with α, β set to the named exit-time functions.
- **Hypotheses**: same as `hasCauchyPVOn_singleton_of_excision_tendsto` but α and β are specialized to `firstExitTimeLeft`/`firstExitTimeRight`.
- **Uses from project**: `PiecewiseC1Path`, `HasCauchyPVOn`, `cpvIntegrandOn`, `LeanModularForms.firstExitTimeLeft`, `LeanModularForms.firstExitTimeRight`, `hasCauchyPVOn_singleton_of_excision_tendsto`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 215-249
- **Notes**: >30 lines (>34 lines of signature).

### `theorem shape_left_of_strictAntiOn`
- **Type**: `{γ : ℝ → ℂ} {s : ℂ} {t₀ δMinus : ℝ} (h_t₀_minus_pos : 0 ≤ t₀ - δMinus) (hδMinus : 0 < δMinus) (hγ_cont : ContinuousOn γ (Icc (t₀-δMinus) t₀)) (hγ_anti : StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀-δMinus) t₀)) {δ_avoid : ℝ} (h_avoid : …) {ε : ℝ} (hε_lt_avoid : ε < δ_avoid) (hε_le_max : ε ≤ ‖γ (t₀-δMinus) - s‖) : 0 ≤ firstExitTimeLeft γ t₀ δMinus s ε ∧ ∀ t ∈ Ioo 0 (firstExitTimeLeft …), ε < ‖γ t - s‖`
- **What**: Left-side shape from strict anti-monotonicity: with γ continuous + `‖γ - s‖` strict-anti on `[t₀-δMinus, t₀]` and avoidance margin on `[0, t₀-δMinus]`, the left exit time is ≥ 0 and the curve stays ε-far on `(0, exitTime)`.
- **How**: Use `firstExitTimeLeft_mem_Icc` to bound exit time in `[t₀-δMinus, t₀]`; for `t < exitTime`, case-split on `t ≤ t₀-δMinus` (use avoidance) vs interior (use strict anti and `ε_le_norm_at_firstExitTimeLeft`).
- **Hypotheses**: positivity/continuity/strict-anti of `‖γ-s‖`; avoidance margin and ε bounds.
- **Uses from project**: `LeanModularForms.firstExitTimeLeft`, `LeanModularForms.firstExitTimeLeft_mem_Icc`, `LeanModularForms.ε_le_norm_at_firstExitTimeLeft`.
- **Used by**: `shape_left_eventually`.
- **Visibility**: public
- **Lines**: 258-278
- **Notes**: none

### `theorem shape_right_of_strictMonoOn`
- **Type**: `{γ : ℝ → ℂ} {s : ℂ} {t₀ δPlus : ℝ} (h_t₀_plus_le : t₀ + δPlus ≤ 1) (hδPlus : 0 < δPlus) (hγ_cont : ContinuousOn γ (Icc t₀ (t₀+δPlus))) (hγ_mono : StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀+δPlus))) {δ_avoid : ℝ} (h_avoid : …) {ε : ℝ} (hε_lt_avoid : ε < δ_avoid) (hε_le_max : …) : firstExitTimeRight γ t₀ δPlus s ε ≤ 1 ∧ ∀ t ∈ Ioo (firstExitTimeRight …) 1, ε < ‖γ t - s‖`
- **What**: Mirror of `shape_left_of_strictAntiOn` on the right side, using strict mono of `‖γ - s‖`.
- **How**: Use `firstExitTimeRight_mem_Icc`, then case-split `t₀+δPlus ≤ t` (avoidance) vs interior (strict-mono + `ε_le_norm_at_firstExitTimeRight`).
- **Hypotheses**: positivity/continuity/strict-mono on right side; avoidance margin.
- **Uses from project**: `LeanModularForms.firstExitTimeRight`, `LeanModularForms.firstExitTimeRight_mem_Icc`, `LeanModularForms.ε_le_norm_at_firstExitTimeRight`.
- **Used by**: `shape_right_eventually`.
- **Visibility**: public
- **Lines**: 283-303
- **Notes**: none

### `theorem shape_right_eventually`
- **Type**: `{γ : ℝ → ℂ} {s : ℂ} {t₀ δPlus : ℝ} (h_t₀_plus_le) (hδPlus) (hγ_cont) (hγ_mono) (_ : γ t₀ = s) {δ_avoid : ℝ} (h_avoid_pos : 0 < δ_avoid) (h_avoid : …) : ∀ᶠ ε in 𝓝[>] 0, firstExitTimeRight γ t₀ δPlus s ε ≤ 1 ∧ ∀ t ∈ Ioo (firstExitTimeRight …) 1, ε < ‖γ t - s‖`
- **What**: Eventual right-side shape: for all ε sufficiently small (in the right-neighborhood of 0), the right-side shape conclusion of `shape_right_of_strictMonoOn` holds.
- **How**: Filter argument: choose `Ioo` containing 0 with upper bound `min …`, then `filter_upwards` and apply `shape_right_of_strictMonoOn` with the small ε.
- **Hypotheses**: same as `shape_right_of_strictMonoOn` plus positivity of δ_avoid and `γ t₀ = s`.
- **Uses from project**: `LeanModularForms.firstExitTimeRight`, `shape_right_of_strictMonoOn`.
- **Used by**: `shape_eventually_of_strict_mono`.
- **Visibility**: public
- **Lines**: 308-324
- **Notes**: none

### `theorem shape_left_eventually`
- **Type**: `{γ : ℝ → ℂ} {s : ℂ} {t₀ δMinus : ℝ} (h_t₀_minus_pos) (hδMinus) (hγ_cont) (hγ_anti) (_ : γ t₀ = s) {δ_avoid : ℝ} (h_avoid_pos) (h_avoid) : ∀ᶠ ε in 𝓝[>] 0, 0 ≤ firstExitTimeLeft γ t₀ δMinus s ε ∧ ∀ t ∈ Ioo 0 (firstExitTimeLeft …), ε < ‖γ t - s‖`
- **What**: Eventual left-side shape, mirror of `shape_right_eventually`.
- **How**: Same filter argument as `shape_right_eventually`, calling `shape_left_of_strictAntiOn`.
- **Hypotheses**: same as `shape_left_of_strictAntiOn` plus positivity of δ_avoid and `γ t₀ = s`.
- **Uses from project**: `LeanModularForms.firstExitTimeLeft`, `shape_left_of_strictAntiOn`.
- **Used by**: `shape_eventually_of_strict_mono`.
- **Visibility**: public
- **Lines**: 328-344
- **Notes**: none

### `theorem shape_eventually_of_strict_mono`
- **Type**: `{γ : ℝ → ℂ} {s : ℂ} {t₀ δMinus δPlus : ℝ} (h_t₀_minus_pos) (h_t₀_plus_le) (hδMinus) (hδPlus) (hγ_cont_left) (hγ_cont_right) (hγ_anti) (hγ_mono) (h_s : γ t₀ = s) {δ_avoid_left δ_avoid_right : ℝ} (h_avoid_left_pos) (h_avoid_right_pos) (h_avoid_left) (h_avoid_right) : ∀ᶠ ε in 𝓝[>] 0, 0 ≤ firstExitTimeLeft … ∧ firstExitTimeRight … ≤ 1 ∧ firstExitTimeLeft … ≤ firstExitTimeRight … ∧ (left far) ∧ (right far) ∧ (middle close)`
- **What**: Combined eventual shape (left, right, plus the natural `α ε ≤ β ε` and the middle `‖γ - s‖ ≤ ε`), packaged into the exact form expected by `hasCauchyPVOn_singleton_of_exitTime_excision`.
- **How**: Combines `shape_left_eventually` and `shape_right_eventually`; separate filter-upwards proves middle facts using `csSup`/`csInf` bounds (`firstExitTimeLeft_set_ub`, `firstExitTimeRight_set_lb`) plus `firstExitTimeLeft_mem_Icc`/`firstExitTimeRight_mem_Icc`. Key lemma: `firstExitTimeLeft_set_ub` and `firstExitTimeRight_set_lb` (used in `le_csSup`/`csInf_le` for the bracketed bound).
- **Hypotheses**: positivity/continuity/strict-mono/anti; γ(t₀)=s; both avoidance margins positive.
- **Uses from project**: `LeanModularForms.firstExitTimeLeft`, `LeanModularForms.firstExitTimeRight`, `LeanModularForms.firstExitTimeLeft_mem_Icc`, `LeanModularForms.firstExitTimeRight_mem_Icc`, `LeanModularForms.firstExitTimeLeft_set_ub`, `LeanModularForms.firstExitTimeRight_set_lb`, `shape_left_eventually`, `shape_right_eventually`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 351-419
- **Notes**: >30 lines (~68 lines).

## File Summary

`ExitTimeExcision.lean` (T-SC-00b in the HungerbuhlerWasem program) restores the excision-based bridge from a parametric symmetric-excision CPV to the canonical `HasCauchyPVOn` form, used by the sector-cancellation argument in T-SC-01.

The file is organised in four blocks:
1. Pointwise CPV-integrand identification: `cpvIntegrandOn_singleton_eq_contour_of_far`, `cpvIntegrandOn_singleton_eq_zero_of_close`, `cpvIntegrandOn_singleton_eq_indicator` (3 theorems).
2. Integral splitting: `integral_cpvIntegrandOn_singleton_eq_contour_left/right`, `integral_cpvIntegrandOn_singleton_eq_zero_middle`, `cpvIntegrandOn_singleton_integral_eq_excision` (4 theorems).
3. Bridge: `hasCauchyPVOn_singleton_of_excision_tendsto` + specialization `hasCauchyPVOn_singleton_of_exitTime_excision` to `firstExitTimeLeft/Right` (2 theorems).
4. Shape lemmas: pointwise (`shape_left_of_strictAntiOn`, `shape_right_of_strictMonoOn`) and eventual (`shape_left_eventually`, `shape_right_eventually`, combined `shape_eventually_of_strict_mono`) (5 theorems).

Total: 14 public theorems, all in namespace `HungerbuhlerWasem`. No sorries, no axioms, no `set_option`. The file is fully self-contained on top of imports from `ExitTime`, `CauchyPrincipalValue`, `MultipointPV`. Out-of-file dependencies are exit-time API functions in `LeanModularForms` and CPV definitions in mathlib.
