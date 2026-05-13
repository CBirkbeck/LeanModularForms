# Inventory — MultiCrossingCPV.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HungerbuhlerWasem/MultiCrossingCPV.lean`
Lines: 5133. Namespace: `HungerbuhlerWasem`. Imports `LeanModularForms.ForMathlib.HungerbuhlerWasem.Crossing`. Whole file is `noncomputable section`.

---

### `private theorem exists_per_crossing_radius`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo 0 1) (h_at : γ.toPath.extend t₀ = s) : ∃ r L_R L_L, 0 < r ∧ L_R ≠ 0 ∧ L_L ≠ 0 ∧ HasDerivWithinAt … L_R (Ioi t₀) t₀ ∧ HasDerivWithinAt … L_L (Iio t₀) t₀ ∧ [four slit-plane / chord-quotient conditions on `[t₀ - r, t₀ + r]`]`
- **What**: Bundles the per-crossing one-sided derivative limits `L_R`, `L_L` with a single radius `r > 0` such that four slit-plane chord-quotient and endpoint conditions all hold uniformly on `[t₀ - r, t₀ + r]`.
- **How**: Calls `oneSided_deriv_setup γ ht₀` to obtain `L_R, L_L`, then four separate radius existence lemmas (`exists_chord_slitPlane_radius_right/left`, `exists_chord_div_endpoint_slitPlane_right/left`). Takes `r := min (min r_R₁ r_L₁) (min r_R₂ r_L₂)` and dispatches each conjunct.
- **Hypotheses**: Closed pw-C¹ immersion γ; t₀ interior of [0,1]; γ(t₀) = s.
- **Uses from project**: `oneSided_deriv_setup`, `exists_chord_slitPlane_radius_right`, `exists_chord_slitPlane_radius_left`, `exists_chord_div_endpoint_slitPlane_right`, `exists_chord_div_endpoint_slitPlane_left` (from Crossing.lean).
- **Used by**: `hasCauchyPV_inv_sub_multiCrossing`, `hasCauchyPV_inv_sub_multiCrossing_corner`, `hasCauchyPVOn_multiCrossing_higherOrder`.
- **Visibility**: private
- **Lines**: 65–117
- **Notes**: None.

---

### `private theorem cpv_tendsto_along_sorted`
- **Type**: Inductive over sorted lists `sorted : List ℝ`. For sorted crossings in `(a,1)` pairwise far apart by `2r`, each contributing per-window convergence to some `λ_i`, with a uniform smooth bound outside the windows, the cutoff integral `∫_a^1 cpvIntegrand((·-s)⁻¹) γ s ε t dt` converges to some `L : ℂ`.
- **What**: Inductive convergence of the cutoff CPV integrand over `[a, 1]` along a sorted list of crossings, for the simple-pole `(z-s)⁻¹` case (smooth-only crossings).
- **How**: Induction on `sorted`. Base case (nil): integrand is `(γ-s)⁻¹·γ'` since `‖γ-s‖ ≥ m > ε` everywhere on `[a,1]`; uses `cpvIntegrand_of_gt`, `intervalIntegral.integral_congr`, `Tendsto.congr'`, `tendsto_const_nhds`. Step case (`t :: rest`): splits `∫_a^1 = ∫_a^{t-r} (const) + ∫_{t-r}^{t+r} (window, converges to λ_t) + ∫_{t+r}^1 (IH)` using `intervalIntegral.integral_add_adjacent_intervals`, bounding cpvIntegrand via `‖cpvIntegrand‖ ≤ (1/ε)·‖γ'‖` and `IntervalIntegrable.mono_fun'`.
- **Hypotheses**: Sorted strictly-increasing list; windows pairwise far apart; per-window convergence; uniform smooth bound off windows.
- **Uses from project**: `cpvIntegrand_of_gt`, `cpvIntegrand` (Crossing.lean), `inv_sub_mul_deriv_intervalIntegrable`, `ClosedPwC1Curve.deriv_extend_intervalIntegrable`.
- **Used by**: `hasCauchyPV_inv_sub_multiCrossing`.
- **Visibility**: private
- **Lines**: 135–449 (proof: ~314 lines)
- **Notes**: Proof >30 lines (≈314 lines); large recursive induction.

---

### `private theorem cpv_tendsto_along_sorted_corner`
- **Type**: Same as `cpv_tendsto_along_sorted` but drops the `h_t_off` (off-partition) hypothesis per crossing.
- **What**: Corner-friendly twin of `cpv_tendsto_along_sorted` (T-BR-Y11c): same convergence statement without requiring crossings to avoid the partition.
- **How**: Identical induction structure to `cpv_tendsto_along_sorted`. The off-partition hypothesis was only propagated, never consumed. Reuses `cpvIntegrand_of_gt`, `inv_sub_mul_deriv_intervalIntegrable`, `intervalIntegral.integral_add_adjacent_intervals`, and the same `(1/ε)·‖γ'‖` bound.
- **Hypotheses**: Sorted list; pairwise separation; per-window convergence; uniform far-bound; γ at crossings = s; crossings in Ioo. Crucially, no off-partition condition.
- **Uses from project**: `cpvIntegrand_of_gt`, `cpvIntegrand`, `inv_sub_mul_deriv_intervalIntegrable`, `ClosedPwC1Curve.deriv_extend_intervalIntegrable`.
- **Used by**: `hasCauchyPV_inv_sub_multiCrossing_corner`.
- **Visibility**: private
- **Lines**: 463–725 (proof: ~262 lines)
- **Notes**: Proof >30 lines (≈262 lines).

---

### `theorem hasCauchyPV_inv_sub_multiCrossing`
- **Type**: `{γ : ClosedPwC1Immersion x} {s : ℂ} (D : MultiPoleCrossData γ s) (_h_flat_at_each : ∀ t₀ ∈ D.crossings, IsFlatOfOrder … 1) : ∃ L : ℂ, HasCauchyPV (fun z => (z - s)⁻¹) γ.toPiecewiseC1Path s L`
- **What**: Multi-crossing simple-pole CPV existence (T-BR-Y9d) for arbitrary card ≥ 0.
- **How**: Case-splits on `D.crossings = ∅` (γ avoids s; uses compactness via `IsCompact.exists_isMinOn`, then `hasCauchyPV_of_avoids`). Non-empty case: extracts per-crossing radii via `exists_per_crossing_radius`, takes a common minimum `r_chord` (via `Finset.exists_min_image` on the attach), combines with geometric radius `r_geom` from `multi_pole_common_radius`, takes `r := min r_chord (r_geom / 2)`, derives smooth-complement bound `multi_pole_smooth_complement_far_bound`, per-window convergence via `perCrossing_window_integral_tendsto_exact`, then applies `cpv_tendsto_along_sorted` on `D.crossings.sort`.
- **Hypotheses**: Closed pw-C¹ immersion γ; multi-pole crossing data D; per-crossing flatness of order 1.
- **Uses from project**: `exists_per_crossing_radius`, `cpv_tendsto_along_sorted`, `multi_pole_common_radius`, `multi_pole_smooth_complement_far_bound`, `multi_pole_local_uniqueness`, `perCrossing_window_integral_tendsto_exact`, `hasCauchyPV_of_avoids`, `MultiPoleCrossData.avoids_of_crossings_empty`, `MultiPoleCrossData.h_Ioo`, `D.h_off`, `D.h_at`, `D.h_complete`, `Finset.sortedLT_sort`.
- **Used by**: `cpv_polarPart_at_multiCrossed_pole`, `cpv_polarPart_at_multiCrossed_pole_under_condB`.
- **Visibility**: public
- **Lines**: 734–938 (proof: ~204 lines)
- **Notes**: Proof >30 lines (≈204 lines).

---

### `private theorem multi_pole_common_radius_corner_simple`
- **Type**: `{crossings partition : Finset ℝ} (h_nonempty : crossings.Nonempty) (h_Ioo : ∀ t ∈ crossings, t ∈ Ioo 0 1) : ∃ r > 0, (endpts) ∧ (pairwise) ∧ (∀ t ∈ crossings, ∀ p ∈ partition, p ∉ crossings → r < |t - p|)`
- **What**: Corner-friendly common local-uniqueness radius (duplicate of `multi_pole_common_radius_corner`, placed earlier for use by the corner-friendly simple-pole CPV theorem).
- **How**: Replaces the `partition` argument by `partition \ crossings` and delegates to `multi_pole_common_radius`.
- **Hypotheses**: Nonempty crossings inside Ioo 0 1.
- **Uses from project**: `multi_pole_common_radius`.
- **Used by**: `hasCauchyPV_inv_sub_multiCrossing_corner`.
- **Visibility**: private
- **Lines**: 964–987
- **Notes**: Duplicate of `multi_pole_common_radius_corner` (line 3390); kept here to avoid forward reference.

---

### `theorem hasCauchyPV_inv_sub_multiCrossing_corner`
- **Type**: `{γ : ClosedPwC1Immersion x} {s : ℂ} {crossings : Finset ℝ} (h_Ioo h_at h_complete _h_flat : …) : ∃ L : ℂ, HasCauchyPV ((·-s)⁻¹) γ.toPiecewiseC1Path s L`
- **What**: Corner-friendly multi-crossing simple-pole CPV existence (T-BR-Y11c). Same statement as `hasCauchyPV_inv_sub_multiCrossing` but does NOT require crossings to be off the partition.
- **How**: Empty crossings: same min-on-compact argument as smooth form using `hasCauchyPV_of_avoids`. Non-empty: extracts per-crossing radii via `exists_per_crossing_radius`, takes common `r_chord` minimum, uses corner-friendly `multi_pole_common_radius_corner_simple` for the geometric radius, derives smooth bound via `multi_pole_smooth_complement_far_bound`, and applies the corner-friendly aggregator `cpv_tendsto_along_sorted_corner`.
- **Hypotheses**: γ closed pw-C¹; crossings ⊂ Ioo 0 1 hitting s; completeness; per-crossing flatness of order 1.
- **Uses from project**: `exists_per_crossing_radius`, `cpv_tendsto_along_sorted_corner`, `multi_pole_common_radius_corner_simple`, `multi_pole_smooth_complement_far_bound`, `multi_pole_local_uniqueness`, `perCrossing_window_integral_tendsto_exact`, `hasCauchyPV_of_avoids`, `Finset.sortedLT_sort`.
- **Used by**: `residueTheorem_crossing_paper_faithful_clean`.
- **Visibility**: public
- **Lines**: 1001–1195 (proof: ~194 lines)
- **Notes**: Proof >30 lines (≈194 lines).

---

### `private theorem pow_inv_mul_deriv_intervalIntegrable`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {a b : ℝ} (c : ℂ) (k : ℕ) (hab : a ≤ b) (h_in_Icc : Icc a b ⊆ Icc 0 1) (h_ne : ∀ t ∈ Icc a b, γ.extend t ≠ s) : IntervalIntegrable (fun t => c * deriv γ.extend t / (γ.extend t - s)^k) volume a b`
- **What**: Integrability of `c · γ' / (γ - s)^k` on a subinterval `[a,b] ⊆ [0,1]` avoiding `s`.
- **How**: Uses `γ.toClosedPwC1Curve.deriv_extend_intervalIntegrable` and `mono_set` to get integrability of `deriv γ` on `[a,b]`. Multiplies by the continuous function `c / (γ-s)^k` via `IntervalIntegrable.mul_continuousOn`, then rewrites the product to the desired form via `congr` + `ring`.
- **Hypotheses**: γ closed pw-C¹; `a ≤ b`; `[a,b] ⊆ [0,1]`; γ avoids s on `[a,b]`.
- **Uses from project**: `ClosedPwC1Curve.deriv_extend_intervalIntegrable`, `PiecewiseC1Path.toPath.continuous_extend`.
- **Used by**: `perCrossing_higherOrder_window_integral_tendsto`, `cpv_higherOrder_tendsto_along_sorted`, `perCrossing_higherOrder_window_integral_tendsto_corner`, `cpv_higherOrder_tendsto_along_sorted_corner`, `hasCauchyPVOn_multiCrossing_higherOrder`, `hasCauchyPVOn_multiCrossing_higherOrder_corner`.
- **Visibility**: private
- **Lines**: 1204–1236
- **Notes**: None.

---

### `private theorem cpvIntegrand_higherOrder_intervalIntegrable`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {a b : ℝ} (c : ℂ) (k : ℕ) (hk_pos : 1 ≤ k) {ε : ℝ} (hε_pos : 0 < ε) (hab : a ≤ b) (h_in_Icc : Icc a b ⊆ Icc 0 1) : IntervalIntegrable (fun t => cpvIntegrand (·c/(z-s)^k) γ.extend s ε t) volume a b`
- **What**: Integrability of the cutoff integrand for `c/(z-s)^k`, bounded by `‖c‖/ε^k · ‖γ'‖`, on a subinterval of `[0,1]`.
- **How**: Builds `AEStronglyMeasurable` via `Measurable.ite` on the measurable predicate `{u | ε < ‖γf u - s‖}`. Bounds `‖cpvIntegrand‖ ≤ M · ‖γ'‖` (M = `‖c‖/ε^k`) via `div_le_div_of_nonneg_left` and `pow_le_pow_left₀`. Uses `IntervalIntegrable.mono_fun'` with dominating function `M·‖γ'‖`.
- **Hypotheses**: γ closed pw-C¹; `k ≥ 1`; `ε > 0`; `[a,b] ⊆ [0,1]`.
- **Uses from project**: `cpvIntegrand`, `ClosedPwC1Curve.deriv_extend_intervalIntegrable`.
- **Used by**: `perCrossing_higherOrder_window_integral_tendsto`, `cpv_higherOrder_tendsto_along_sorted`, `perCrossing_higherOrder_window_integral_tendsto_corner`, `cpv_higherOrder_tendsto_along_sorted_corner`.
- **Visibility**: private
- **Lines**: 1239–1298
- **Notes**: None.

---

### `private noncomputable def antiderivPow`
- **Type**: `(s : ℂ) (k : ℕ) (z : ℂ) : ℂ := -(↑(k-1))⁻¹ * ((z - s) ^ (k-1))⁻¹`
- **What**: Antiderivative `F(z) = -(k-1)⁻¹ · (z-s)^{-(k-1)}` for `k ≥ 2`. Satisfies `F'(z) = 1/(z-s)^k` (off `s`).
- **How**: Direct definition.
- **Hypotheses**: None (definition).
- **Uses from project**: [].
- **Used by**: `perCrossing_higherOrder_window_integral_tendsto`, `cpv_higherOrder_tendsto_along_sorted`, `hasCauchyPVOn_multiCrossing_higherOrder`, `perCrossing_higherOrder_window_integral_tendsto_corner`, `cpv_higherOrder_tendsto_along_sorted_corner`, `hasCauchyPVOn_multiCrossing_higherOrder_corner`.
- **Visibility**: private
- **Lines**: 1308–1309
- **Notes**: None.

---

### `private theorem perCrossing_higherOrder_window_integral_tendsto`
- **Type**: For a single smooth crossing `t_i` of γ at s (off-partition), with flatness of order `n ≥ k` (`k ≥ 2`), the angle relation `(k-1)π ∈ 2π·ℤ`, and local uniqueness on `[t_i - r, t_i + r]`, the per-window cutoff integral `∫_{t_i-r}^{t_i+r} cpvIntegrand(c/(z-s)^k) γ s ε u du` tends as `ε → 0⁺` to `c·(antiderivPow s k (γ(t_i+r)) − antiderivPow s k (γ(t_i-r)))`.
- **What**: Per-crossing higher-order window convergence under condition (B), smooth-crossing version.
- **How**: Extracts `L = deriv γ t_i` via `deriv_limit_eq_at_off_partition`. Builds strict mono/anti radii `r_R, r_L` from `norm_sub_strictMonoOn_right/left`. Sets `r_mono := min r (min r_R r_L) / 2`. Builds `HasDerivWithinAt` via `hasDerivWithinAt_Ioi_of_tendsto / Iio`. Derives smooth `h_B` from `h_B_of_angle_compat_smooth`. Splits the window integral into three pieces using firstExitTime±, with the middle piece vanishing a.e. (norm ≤ ε), and applies FTC `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le` with chain rule using `hasDerivAt_antiderivative_pow_inv_complex`. F-curve difference at `t_eps_minus, t_eps_plus` vanishes by `F_curve_diff_tendsto_zero_under_conditionB`.
- **Hypotheses**: t_i ∈ Ioo 0 1; γ(t_i) = s; r > 0 with `[t_i±r] ⊆ [0,1]`; t_i ∉ partition; local uniqueness; flatness of order `n ≥ k`; `k ≥ 2`; smooth angle condition.
- **Uses from project**: `deriv_limit_eq_at_off_partition`, `norm_sub_strictMonoOn_right`, `norm_sub_strictAntiOn_left`, `eventually_differentiable_right`, `eventually_differentiable_left`, `hasDerivWithinAt_Ioi_of_tendsto`, `hasDerivWithinAt_Iio_of_tendsto`, `h_B_of_angle_compat_smooth`, `LeanModularForms.firstExitTimeRight`, `LeanModularForms.firstExitTimeLeft`, `LeanModularForms.firstExitTimeRight_tendsto_t₀`, `LeanModularForms.firstExitTimeLeft_tendsto_t₀`, `LeanModularForms.firstExitTimeRight_radius_eventually`, `LeanModularForms.firstExitTimeLeft_radius_eventually`, `F_curve_diff_tendsto_zero_under_conditionB`, `multi_pole_local_far_bound`, `hasDerivAt_antiderivative_pow_inv_complex`, `antiderivPow`, `cpvIntegrand`, `cpvIntegrand_higherOrder_intervalIntegrable`, `pow_inv_mul_deriv_intervalIntegrable`, `PiecewiseC1Path.differentiable_off`.
- **Used by**: `hasCauchyPVOn_multiCrossing_higherOrder`.
- **Visibility**: private
- **Lines**: 1320–1856 (proof: ~536 lines)
- **Notes**: Proof >30 lines (≈536 lines); large window-FTC argument.

---

### `private theorem cpv_higherOrder_tendsto_along_sorted`
- **Type**: Inductive over sorted lists; given per-crossing convergence to `c·(antiderivPow(γ(t+r)) − antiderivPow(γ(t-r)))` and a smooth bound, `∫_a^1 cpvIntegrand(c/(z-s)^k) γ s ε t` tends to `c·(antiderivPow(γ(1)) − antiderivPow(γ(a)))` as `ε → 0⁺`.
- **What**: Higher-order analogue of `cpv_tendsto_along_sorted`: aggregated convergence over a sorted list of crossings with telescoping FTC cancellation between the smooth and window pieces.
- **How**: Induction on the sorted list. Base case (nil): integrand equals `c·γ'/(γ-s)^k` everywhere, FTC `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le` yields the antiderivative difference. Step case: splits `[a,1]` into smooth left, window middle (per-crossing convergence to telescoping `F(γ(t+r))-F(γ(t-r))`), recursive right. Sums via `Tendsto.add`; uses `Finset.sum / ring` to collapse the telescoping sum to `c·(F(γ(1)) - F(γ(a)))`.
- **Hypotheses**: γ closed pw-C¹; sorted list of crossings in Ioo, pairwise far apart, off partition, hitting s, with local uniqueness and per-window convergence.
- **Uses from project**: `cpvIntegrand`, `cpvIntegrand_higherOrder_intervalIntegrable`, `pow_inv_mul_deriv_intervalIntegrable`, `antiderivPow`, `hasDerivAt_antiderivative_pow_inv_complex`, `PiecewiseC1Path.differentiable_off`.
- **Used by**: `hasCauchyPVOn_multiCrossing_higherOrder`.
- **Visibility**: private
- **Lines**: 1864–2229 (proof: ~365 lines)
- **Notes**: Proof >30 lines (≈365 lines).

---

### `theorem hasCauchyPVOn_multiCrossing_higherOrder`
- **Type**: `{γ : ClosedPwC1Immersion x} {s : ℂ} (D : MultiPoleCrossData γ s) {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n) (h_flat : …) (h_angle : ∀ _ ∈ D.crossings, ∃ m, ((k-1):ℕ)·π = m·2π) (c : ℂ) : HasCauchyPVOn {s} (·c/(z-s)^k) γ.toPiecewiseC1Path 0`
- **What**: Multi-crossing higher-order CPV vanishing (T-BR-Y9e): for `k ≥ 2`, each crossing flat of order `n ≥ k` with the angle condition `(k-1)π ∈ 2π·ℤ`, the CPV vanishes.
- **How**: Empty crossings: closed-contour FTC gives the integral = 0 (uses `closed_immersion_extend_zero_eq_one`), then `hasCauchyPVOn_of_avoids` plus contour-integral identification. Non-empty: per-crossing radii via `exists_per_crossing_radius`, common radius via `multi_pole_common_radius`, smooth bound via `multi_pole_smooth_complement_far_bound`, per-window convergence via `perCrossing_higherOrder_window_integral_tendsto`, aggregation via `cpv_higherOrder_tendsto_along_sorted`; closed-contour identity collapses target to 0. Converts to `HasCauchyPVOn` via `cpvIntegrand_eq_cpvIntegrandOn_singleton`.
- **Hypotheses**: D crossings; `2 ≤ k ≤ n`; `n ≥ 1`; flatness of order `n` at each crossing; smooth angle condition `(k-1)π ∈ 2π·ℤ`.
- **Uses from project**: `MultiPoleCrossData.avoids_of_crossings_empty`, `closed_immersion_extend_zero_eq_one`, `hasCauchyPVOn_of_avoids`, `pow_inv_mul_deriv_intervalIntegrable`, `antiderivPow`, `hasDerivAt_antiderivative_pow_inv_complex`, `exists_per_crossing_radius`, `multi_pole_common_radius`, `multi_pole_smooth_complement_far_bound`, `multi_pole_local_uniqueness`, `perCrossing_higherOrder_window_integral_tendsto`, `cpv_higherOrder_tendsto_along_sorted`, `cpvIntegrand`, `cpvIntegrand_eq_cpvIntegrandOn_singleton`, `Finset.sortedLT_sort`, `PiecewiseC1Path.differentiable_off`.
- **Used by**: `cpv_polarPart_at_multiCrossed_pole`, `cpv_polarPart_at_multiCrossed_pole_under_condB`.
- **Visibility**: public
- **Lines**: 2237–2507 (proof: ~270 lines)
- **Notes**: Proof >30 lines (≈270 lines).

---

### `private theorem cpv_higherOrder_tendsto_along_sorted_corner`
- **Type**: Same as `cpv_higherOrder_tendsto_along_sorted` but drops the off-partition hypothesis per crossing.
- **What**: Corner-friendly variant of `cpv_higherOrder_tendsto_along_sorted` (T-BR-Y11b): drops `h_t_off` (only propagated, never consumed).
- **How**: Identical induction to the smooth form. Reuses `cpvIntegrand_higherOrder_intervalIntegrable`, `pow_inv_mul_deriv_intervalIntegrable`, `antiderivPow`, FTC via `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`. The countable-exception set in the FTC tolerates corners.
- **Hypotheses**: Sorted crossings in Ioo, pairwise far apart, hitting s, with local uniqueness and per-window convergence. No off-partition condition.
- **Uses from project**: `cpvIntegrand`, `cpvIntegrand_higherOrder_intervalIntegrable`, `pow_inv_mul_deriv_intervalIntegrable`, `antiderivPow`, `hasDerivAt_antiderivative_pow_inv_complex`, `PiecewiseC1Path.differentiable_off`.
- **Used by**: `hasCauchyPVOn_multiCrossing_higherOrder_corner`.
- **Visibility**: private
- **Lines**: 2518–2859 (proof: ~341 lines)
- **Notes**: Proof >30 lines (≈341 lines).

---

### `private theorem perCrossing_higherOrder_window_integral_tendsto_corner`
- **Type**: Per-crossing higher-order window convergence with separate one-sided limits `L_+`, `L_-` (both ≠ 0) and corner-form `h_B : (L_+/‖L_+‖)^(k-1) = ((-L_-)/‖L_-‖)^(k-1)`.
- **What**: Corner-friendly twin of `perCrossing_higherOrder_window_integral_tendsto`. Generalises by accepting separate left/right derivative limits and the general-angle `h_B`.
- **How**: Same architecture as the smooth version: build strict mono/anti radii via `norm_sub_strictMonoOn_right/left` (with separate `L_+`, `L_-`), set `r_mono`, build `HasDerivWithinAt` via `hasDerivWithinAt_Ioi_of_tendsto`/`Iio_of_tendsto`, split the integral via firstExitTime±, middle piece vanishes a.e., left/right by FTC `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le` with chain rule. F-curve cancellation by `F_curve_diff_tendsto_zero_under_conditionB`.
- **Hypotheses**: t_i ∈ Ioo 0 1; γ(t_i) = s; r > 0 with `[t_i±r] ⊆ [0,1]`; local uniqueness; `L_+, L_- ≠ 0` with one-sided derivative tendsto; flatness of order `n ≥ k ≥ 2`; corner-form `h_B`. No off-partition.
- **Uses from project**: `norm_sub_strictMonoOn_right`, `norm_sub_strictAntiOn_left`, `eventually_differentiable_right`, `eventually_differentiable_left`, `hasDerivWithinAt_Ioi_of_tendsto`, `hasDerivWithinAt_Iio_of_tendsto`, `LeanModularForms.firstExitTimeRight`, `LeanModularForms.firstExitTimeLeft`, `LeanModularForms.firstExitTimeRight_tendsto_t₀`, `LeanModularForms.firstExitTimeLeft_tendsto_t₀`, `LeanModularForms.firstExitTimeRight_radius_eventually`, `LeanModularForms.firstExitTimeLeft_radius_eventually`, `F_curve_diff_tendsto_zero_under_conditionB`, `multi_pole_local_far_bound`, `hasDerivAt_antiderivative_pow_inv_complex`, `antiderivPow`, `cpvIntegrand`, `cpvIntegrand_higherOrder_intervalIntegrable`, `pow_inv_mul_deriv_intervalIntegrable`, `PiecewiseC1Path.differentiable_off`.
- **Used by**: `hasCauchyPVOn_multiCrossing_higherOrder_corner`.
- **Visibility**: private
- **Lines**: 2890–3375 (proof: ~485 lines)
- **Notes**: Proof >30 lines (≈485 lines).

---

### `private theorem multi_pole_common_radius_corner`
- **Type**: `{crossings partition : Finset ℝ} (h_nonempty : crossings.Nonempty) (h_Ioo : ∀ t ∈ crossings, t ∈ Ioo 0 1) : ∃ r > 0, (endpts) ∧ (pairwise) ∧ (∀ t ∈ crossings, ∀ p ∈ partition, p ∉ crossings → r < |t - p|)`
- **What**: Corner-friendly common local-uniqueness radius (allows partition points to coincide with crossing parameters).
- **How**: Replaces `partition` with `partition \ crossings` and delegates to `multi_pole_common_radius`.
- **Hypotheses**: Nonempty crossings inside Ioo 0 1.
- **Uses from project**: `multi_pole_common_radius`.
- **Used by**: `hasCauchyPVOn_multiCrossing_higherOrder_corner`.
- **Visibility**: private
- **Lines**: 3390–3413
- **Notes**: Duplicate of `multi_pole_common_radius_corner_simple` (line 964).

---

### `theorem hasCauchyPVOn_multiCrossing_higherOrder_corner`
- **Type**: Corner-friendly multi-crossing higher-order CPV vanishing (T-BR-Y11b). Takes user-supplied per-crossing `L_+`, `L_-` and corner-form `h_B`.
- **What**: Generalises `hasCauchyPVOn_multiCrossing_higherOrder` to admit corner crossings.
- **How**: Empty crossings: closed-contour FTC = 0 (uses `closed_immersion_extend_zero_eq_one`). Non-empty: extracts per-crossing strict mono/anti radii via `norm_sub_strictMonoOn_right/left`, takes common minimum, combines with corner-friendly common radius `multi_pole_common_radius_corner`, derives smooth bound via `multi_pole_smooth_complement_far_bound`. Per-window convergence via `perCrossing_higherOrder_window_integral_tendsto_corner` (using user-supplied `L_+, L_-, h_B`). Aggregation via `cpv_higherOrder_tendsto_along_sorted_corner`. Closed contour collapses target to 0. Converts via `cpvIntegrand_eq_cpvIntegrandOn_singleton`.
- **Hypotheses**: γ closed pw-C¹; crossings ⊂ Ioo 0 1; completeness; `2 ≤ k ≤ n`, `n ≥ 1`; flatness; per-crossing one-sided limits and corner-form angle compatibility.
- **Uses from project**: `closed_immersion_extend_zero_eq_one`, `hasCauchyPVOn_of_avoids`, `pow_inv_mul_deriv_intervalIntegrable`, `antiderivPow`, `hasDerivAt_antiderivative_pow_inv_complex`, `norm_sub_strictMonoOn_right`, `norm_sub_strictAntiOn_left`, `eventually_differentiable_right/left`, `multi_pole_common_radius_corner`, `multi_pole_smooth_complement_far_bound`, `multi_pole_local_uniqueness`, `perCrossing_higherOrder_window_integral_tendsto_corner`, `cpv_higherOrder_tendsto_along_sorted_corner`, `cpvIntegrand`, `cpvIntegrand_eq_cpvIntegrandOn_singleton`, `Finset.sortedLT_sort`, `PiecewiseC1Path.differentiable_off`.
- **Used by**: `cpv_polarPart_at_multiCrossed_pole_under_condB_corner`.
- **Visibility**: public
- **Lines**: 3429–3720 (proof: ~291 lines)
- **Notes**: Proof >30 lines (≈291 lines).

---

### `theorem cpv_polarPart_at_multiCrossed_pole`
- **Type**: `{γ : ClosedPwC1Immersion x} {s : ℂ} {S : Finset ℂ} (hs : s ∈ S) {f : ℂ → ℂ} {U : Set ℂ} (decomp : PolarPartDecomposition f S U) (D : MultiPoleCrossData γ s) (h_flat_at_each : ∀ t₀ ∈ D.crossings, IsFlatOfOrder … (decomp.order s)) (h_angle_at_each : ∀ k : Fin (decomp.order s), k.val ≥ 1 → ∀ t₀ ∈ D.crossings, ∃ m, k.val·π = m·2π) : HasCauchyPVOn {s} (decomp.polarPart s) γ.toPiecewiseC1Path (2πi·w·residue f s)` where `w := generalizedWindingNumber γ s`.
- **What**: Per-pole polar-part CPV for multi-crossings (T-BR-Y9f): the CPV of the polar part equals `2πi·w·residue f s`.
- **How**: Decomposes `polarPart s = ∑_{k:Fin N} a k / (z-s)^(k.val+1)`. For `k.val = 0` (simple pole), uses `hasCauchyPV_inv_sub_multiCrossing` + `hasGeneralizedWindingNumber_of_hasCauchyPV` to identify `L_inv = 2πi·w`, then scales by `a 0` via `HungerbuhlerWasem.hasCauchyPV_simplePole_of_inv`. For `k.val ≥ 1` (higher order), applies `hasCauchyPVOn_multiCrossing_higherOrder` to get CPV = 0. Aggregates via `HasCauchyPV.finset_sum`, then `Finset.sum_eq_single` isolates the k=0 term as `2πi·w·a₀ = 2πi·w·residue f s` (via `decomp.residue_eq`). Rewrites the sum to `decomp.polarPart s` off `s` via `HasCauchyPV.congr_pointwise` and `decomp.polarPart_eq`. Converts via `HasCauchyPV.to_singletonOn`.
- **Hypotheses**: decomp from PolarPartDecomposition; D crossings; per-crossing flatness of `decomp.order s`; per-`k ≥ 1` angle condition.
- **Uses from project**: `PolarPartDecomposition` (`.order`, `.coeff`, `.residue_eq`, `.polarPart_eq`), `HungerbuhlerWasem.cpvIntegrandOn_singleMonomial_intervalIntegrable`, `cpvIntegrand`, `cpvIntegrand_eq_cpvIntegrandOn_singleton`, `cpvIntegrandOn`, `hasCauchyPV_inv_sub_multiCrossing`, `hasGeneralizedWindingNumber_of_hasCauchyPV`, `HungerbuhlerWasem.hasCauchyPV_simplePole_of_inv`, `hasCauchyPVOn_multiCrossing_higherOrder`, `hasCauchyPV_of_hasCauchyPVOn_singleton`, `HasCauchyPV.finset_sum`, `HasCauchyPV.congr_pointwise`, `HasCauchyPV.to_singletonOn`, `IsFlatOfOrder.of_le`, `generalizedWindingNumber`, `residue`, `Complex.two_pi_I_ne_zero`.
- **Used by**: unused in file (consumed externally; this is a façade replaced by the conditional-angle variant for HW3.3 callers).
- **Visibility**: public
- **Lines**: 3739–3878 (proof: ~139 lines)
- **Notes**: Proof >30 lines (≈139 lines).

---

### `theorem cpv_polarPart_at_multiCrossed_pole_under_condB`
- **Type**: As `cpv_polarPart_at_multiCrossed_pole` but with the angle hypothesis weakened to a conditional `(coeff s k ≠ 0 → angle relation)`.
- **What**: Conditional-angle variant (T-BR-Y9g) matching the output of `SatisfiesConditionB.laurent_compatible`.
- **How**: Same architecture; for the higher-order case, additionally splits on `decomp.coeff s k = 0` (then the monomial vanishes identically, CPV = 0 via `HasCauchyPVOn.zero_fun`) vs `≠ 0` (where condition (B) supplies the angle).
- **Hypotheses**: decomp; D crossings; per-crossing flatness; conditional angle `coeff ≠ 0 → ∃ m, kπ = m·2π` for `k ≥ 1`.
- **Uses from project**: `PolarPartDecomposition` (`.order`, `.coeff`, `.residue_eq`, `.polarPart_eq`), `HungerbuhlerWasem.cpvIntegrandOn_singleMonomial_intervalIntegrable`, `cpvIntegrand`, `cpvIntegrand_eq_cpvIntegrandOn_singleton`, `hasCauchyPV_inv_sub_multiCrossing`, `hasGeneralizedWindingNumber_of_hasCauchyPV`, `HungerbuhlerWasem.hasCauchyPV_simplePole_of_inv`, `hasCauchyPVOn_multiCrossing_higherOrder`, `hasCauchyPV_of_hasCauchyPVOn_singleton`, `HasCauchyPV.finset_sum`, `HasCauchyPV.congr_pointwise`, `HasCauchyPV.to_singletonOn`, `HasCauchyPVOn.zero_fun`, `IsFlatOfOrder.of_le`, `Complex.two_pi_I_ne_zero`.
- **Used by**: `residueTheorem_crossing_full_spec`.
- **Visibility**: public
- **Lines**: 3890–4029 (proof: ~139 lines)
- **Notes**: Proof >30 lines (≈139 lines).

---

### `theorem cpv_polarPart_at_multiCrossed_pole_under_condB_corner`
- **Type**: Corner-friendly version of `cpv_polarPart_at_multiCrossed_pole_under_condB` (T-BR-Y11b). Caller supplies per-crossing `L_+, L_-` with corner-form `h_B` and `h_simple_cpv` (existence of simple-pole CPV witness).
- **What**: Per-pole polar-part multi-crossing CPV with corner support.
- **How**: Same architecture as the smooth conditional form; for simple-pole case (`k.val = 0`), uses the supplied `h_simple_cpv` directly (rather than building it internally) and identifies `L_inv = 2πi·w`. For higher-order case (`k.val ≥ 1`), splits on `a k = 0` (vanishing monomial) vs `≠ 0` (apply `hasCauchyPVOn_multiCrossing_higherOrder_corner` with corner-form `h_B`). Aggregates via `HasCauchyPV.finset_sum`.
- **Hypotheses**: decomp; crossings + completeness; per-crossing flatness; user-supplied `L_+, L_-`; conditional corner-form `h_B`; simple-pole CPV existence.
- **Uses from project**: `PolarPartDecomposition`, `HungerbuhlerWasem.cpvIntegrandOn_singleMonomial_intervalIntegrable`, `cpvIntegrand`, `cpvIntegrand_eq_cpvIntegrandOn_singleton`, `hasGeneralizedWindingNumber_of_hasCauchyPV`, `HungerbuhlerWasem.hasCauchyPV_simplePole_of_inv`, `hasCauchyPVOn_multiCrossing_higherOrder_corner`, `hasCauchyPV_of_hasCauchyPVOn_singleton`, `HasCauchyPV.finset_sum`, `HasCauchyPV.congr_pointwise`, `HasCauchyPV.to_singletonOn`, `HasCauchyPVOn.zero_fun`, `Complex.two_pi_I_ne_zero`.
- **Used by**: `residueTheorem_crossing_paper_faithful_clean`.
- **Visibility**: public
- **Lines**: 4049–4201 (proof: ~152 lines)
- **Notes**: Proof >30 lines (≈152 lines).

---

### `theorem residueTheorem_crossing_full_spec`
- **Type**: HW3.3 full-spec form (T-BR-Y9g). Eight spec hypotheses (paper-faithful HW3.3) plus `hx_notin_S` and `h_no_corner_crossings`; concludes `HasCauchyPVOn S f γ … (∑_s 2πi·w·residue f s)`.
- **What**: Eliminates `h_multi_cpv_polar_part` oracle from `_no_basepoint_no_unique_constraint` by discharging the per-pole multi-crossing CPV via `cpv_polarPart_at_multiCrossed_pole_under_condB`.
- **How**: Wraps `residueTheorem_crossing_no_basepoint_no_unique_constraint` (external) and supplies the per-pole oracle internally: constructs `MultiPoleCrossScenario.ofImmersion` and per-pole `data`, derives `h_flat_at_each` from `hCondA`, derives `h_angle_cond` from `hCondB` via `angle_compat_of_condB`, applies `cpv_polarPart_at_multiCrossed_pole_under_condB`, lifts via `hasCauchyPV_of_hasCauchyPVOn_singleton`.
- **Hypotheses**: U open, S ⊂ U, f differentiable on U\S, γ closed pw-C¹, null-homologous, meromorphic at each pole, conditions A'/B, x ∉ S, no corner crossings.
- **Uses from project**: `residueTheorem_crossing_no_basepoint_no_unique_constraint`, `PolarPartDecomposition.ofMeromorphicWithCondB`, `MultiPoleCrossScenario.ofImmersion`, `MultiPoleCrossScenario.data`, `MultiPoleCrossData` (`.h_at`, `.h_off`, `.h_Ioo`, `.crossings`), `SatisfiesConditionA'`, `SatisfiesConditionB`, `IsNullHomologous`, `angle_compat_of_condB`, `cpv_polarPart_at_multiCrossed_pole_under_condB`, `hasCauchyPV_of_hasCauchyPVOn_singleton`, `IsFlatOfOrder`.
- **Used by**: `residueTheorem_crossing_full_spec_reparam`, `residueTheorem_crossing_full_spec_general`, `residueTheorem_crossing_paper_faithful`.
- **Visibility**: public
- **Lines**: 4229–4297 (proof: ~68 lines)
- **Notes**: Proof >30 lines (≈68 lines).

---

### `theorem residueTheorem_crossing_full_spec_reparam`
- **Type**: Drops `hx_notin_S` by exposing the reparametrization-lift hypothesis explicitly.
- **What**: Reparametrization-shim form (T-BR-Y9g-continue).
- **How**: Refines using the user-supplied `h_reparam_lift`, with the body delegating to `residueTheorem_crossing_full_spec` for any `γ'` satisfying the lifted spec.
- **Hypotheses**: Same as `_full_spec` minus `hx_notin_S`, plus `h_reparam_lift`.
- **Uses from project**: `residueTheorem_crossing_full_spec`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 4343–4384
- **Notes**: None.

---

### `theorem residueTheorem_crossing_full_spec_general`
- **Type**: Drops `hx_notin_S` by case-splitting on `x ∈ S`, with the genuine reparametrization case packaged as `h_reparam_lift_at_pole_basepoint`.
- **What**: General no-basepoint form (T-BR-Y9g-continue).
- **How**: `by_cases hx : x ∈ S`: if yes, apply user-supplied lift; if no, direct dispatch to `residueTheorem_crossing_full_spec`.
- **Hypotheses**: Same as `_full_spec` minus `hx_notin_S`, plus conditional cyclic-shift lift.
- **Uses from project**: `residueTheorem_crossing_full_spec`.
- **Used by**: `residueTheorem_crossing_full_spec_basepoint_off`.
- **Visibility**: public
- **Lines**: 4414–4464
- **Notes**: None.

---

### `theorem residueTheorem_crossing_full_spec_basepoint_off`
- **Type**: HW3.3 full-spec form for `x ∉ S` (auto-discharges the cyclic-shift lift).
- **What**: Convenience corollary of `_general` for `x ∉ S` (T-BR-Y9g-continue).
- **How**: Apply `_general` with the lift hypothesis trivialised by `absurd hx hx_notin_S`.
- **Hypotheses**: As `_full_spec`.
- **Uses from project**: `residueTheorem_crossing_full_spec_general`.
- **Used by**: `residueTheorem_crossing_full_spec_no_basepoint`.
- **Visibility**: public
- **Lines**: 4478–4499
- **Notes**: None.

---

### `theorem residueTheorem_crossing_full_spec_no_basepoint`
- **Type**: Drops `hx_notin_S` from `_basepoint_off` by accepting cyclic-shift pole-basepoint data (CPV witness for shifted path).
- **What**: No-basepoint form (T-BR-Y9h-C).
- **How**: `by_cases hx`: if yes, obtain shift `τ` and CPV witness `h_cpv'` for shifted path, transport back via `ClosedPwC1Immersion.hasCauchyPVOn_cyclicShift` and `ClosedPwC1Immersion.generalizedWindingNumber_cyclicShift` (winding numbers preserved under cyclic shift). If no, direct dispatch to `_basepoint_off`.
- **Hypotheses**: As `_basepoint_off` minus `hx_notin_S`, plus conditional pole-basepoint data.
- **Uses from project**: `residueTheorem_crossing_full_spec_basepoint_off`, `ClosedPwC1Immersion.generalizedWindingNumber_cyclicShift`, `ClosedPwC1Immersion.hasCauchyPVOn_cyclicShift`, `ClosedPwC1Immersion.cyclicShift`.
- **Used by**: `residueTheorem_crossing_full_spec_no_basepoint_with_transports`, `residueTheorem_crossing_full_spec_no_basepoint_basepoint_off`.
- **Visibility**: public
- **Lines**: 4551–4615 (proof: ~64 lines)
- **Notes**: Proof >30 lines (≈64 lines).

---

### `theorem residueTheorem_crossing_full_spec_no_basepoint_with_transports`
- **Type**: Variant of `_no_basepoint` invoking the cyclic-shift transports for null-homology / A' / B internally.
- **What**: Internally applies `isNullHomologous_cyclicShift`, `satisfiesConditionA'_cyclicShift`, `satisfiesConditionB_cyclicShift` to lift the spec hypotheses.
- **How**: Calls `_no_basepoint` with a tailored `h_pole_basepoint_data` that, given the breakpoint witnesses (ord, angle, Laurent), uses `ClosedPwC1Immersion.isNullHomologous_cyclicShift`, `ClosedPwC1Immersion.satisfiesConditionA'_cyclicShift`, `ClosedPwC1Immersion.satisfiesConditionB_cyclicShift` to lift the spec hypotheses, then dispatches via the caller-supplied final CPV witness.
- **Hypotheses**: Same as `_no_basepoint` plus expanded basepoint-specific witnesses (ord, angle, Laurent at the breakpoint).
- **Uses from project**: `residueTheorem_crossing_full_spec_no_basepoint`, `ClosedPwC1Immersion.isNullHomologous_cyclicShift`, `ClosedPwC1Immersion.satisfiesConditionA'_cyclicShift`, `ClosedPwC1Immersion.satisfiesConditionB_cyclicShift`, `PolarPartDecomposition.ofMeromorphicWithCondB`, `angleAtCrossing`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 4637–4708 (proof: ~71 lines)
- **Notes**: Proof >30 lines (≈71 lines).

---

### `theorem residueTheorem_crossing_full_spec_no_basepoint_basepoint_off`
- **Type**: Specialisation of `_no_basepoint` for `x ∉ S` (auto-discharges the pole-basepoint data).
- **What**: Convenience corollary matching the signature of `_basepoint_off` (T-BR-Y9h-C).
- **How**: Apply `_no_basepoint` with `(fun hx => absurd hx hx_notin_S)` to trivialise the basepoint data.
- **Hypotheses**: As `_full_spec`.
- **Uses from project**: `residueTheorem_crossing_full_spec_no_basepoint`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 4716–4737
- **Notes**: None.

---

### `theorem residueTheorem_crossing_paper_faithful`
- **Type**: Paper-faithful HW3.3 spec form (T-BR-Y11) with eight spec hypotheses plus a single structural disjunction `h_geom_residual` (smooth branch `(x ∉ S, no_corner_crossings)` ∨ corner branch `unique_cross`).
- **What**: Headline HW3.3 form combining smooth multi-crossings branch and corner single-crossing branch under one disjunction.
- **How**: `rcases h_geom_residual` and dispatches: smooth branch → `residueTheorem_crossing_full_spec`; corner branch → `residueTheorem_crossing_truly_full_spec` (external).
- **Hypotheses**: 8 paper-faithful spec hypotheses (U open, nonempty, S in U, f differentiable on U\S, γ closed, null-homologous, meromorphic, A', B) + `h_geom_residual` disjunction.
- **Uses from project**: `residueTheorem_crossing_full_spec`, `residueTheorem_crossing_truly_full_spec`.
- **Used by**: `residueTheorem_crossing_paper_faithful_smooth`, `residueTheorem_crossing_paper_faithful_unique`.
- **Visibility**: public
- **Lines**: 4796–4828 (proof: ~32 lines)
- **Notes**: Proof >30 lines (≈32 lines).

---

### `theorem residueTheorem_crossing_paper_faithful_smooth`
- **Type**: Specialisation of `_paper_faithful` to the smooth branch (`hx_notin_S, h_no_corner_crossings`).
- **What**: Convenience corollary for `ContDiff`-style contours.
- **How**: Calls `_paper_faithful` with `Or.inl ⟨hx_notin_S, h_no_corner_crossings⟩`.
- **Hypotheses**: As `_full_spec`.
- **Uses from project**: `residueTheorem_crossing_paper_faithful`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 4843–4863
- **Notes**: None.

---

### `theorem residueTheorem_crossing_paper_faithful_unique`
- **Type**: Specialisation of `_paper_faithful` to the corner branch (single-crossing).
- **What**: Convenience corollary for polygonal / single-crossing contours.
- **How**: Calls `_paper_faithful` with `Or.inr h_unique_cross`.
- **Hypotheses**: As `_paper_faithful` but with `h_unique_cross` directly.
- **Uses from project**: `residueTheorem_crossing_paper_faithful`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 4869–4890
- **Notes**: None.

---

### `theorem residueTheorem_crossing_paper_faithful_clean`
- **Type**: Eight-spec-hypothesis corner-friendly clean form (T-BR-Y11c) with only `hx_notin_S` as the geometric residual.
- **What**: Final headline form admitting both multi-crossings AND corner crossings, with all per-pole simple-pole CPV existence auto-discharged.
- **How**: Wraps `residueTheorem_crossing_compositional` (external) and discharges the per-pole oracle: split on uncrossed (`cpv_polarPart_at_uncrossed_pole`) vs crossed. Crossed case: builds `crossings` via `PwC1Immersion.crossingSet_finite` (needing `γ(0) ≠ s` and `γ(1) ≠ s`, both auto-derived from `hx_notin_S` and basepoint identities). Defines `L_plus`, `L_minus` via case-split on partition membership: corner uses `right_deriv_limit`/`left_deriv_limit` (via `Classical.choose`); smooth uses `deriv γ`. Builds `h_B'` via `corner_angle_compat_to_h_B` for corners and `h_B_of_angle_compat_smooth` for smooth (with `angle_compat_of_condB_anywhere` / `angle_compat_of_condB`). Auto-discharges `h_simple_cpv` via `hasCauchyPV_inv_sub_multiCrossing_corner`. Applies `cpv_polarPart_at_multiCrossed_pole_under_condB_corner`, then routes via `hasCauchyPV_of_hasCauchyPVOn_singleton` + `MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole`.
- **Hypotheses**: Eight paper-faithful HW3.3 hypotheses plus `hx_notin_S`.
- **Uses from project**: `residueTheorem_crossing_compositional`, `PolarPartDecomposition.ofMeromorphicWithCondB`, `cpv_polarPart_at_uncrossed_pole`, `PwC1Immersion.crossingSet_finite`, `Path.extend_zero`, `Path.extend_one`, `PiecewiseC1Path.right_deriv_limit`, `PiecewiseC1Path.left_deriv_limit`, `deriv_limit_eq_at_off_partition`, `corner_angle_compat_to_h_B`, `h_B_of_angle_compat_smooth`, `angle_compat_of_condB`, `angle_compat_of_condB_anywhere`, `isFlatOfOrder_one`, `hasCauchyPV_inv_sub_multiCrossing_corner`, `cpv_polarPart_at_multiCrossed_pole_under_condB_corner`, `hasCauchyPV_of_hasCauchyPVOn_singleton`, `MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole`, `angleAtCrossing`.
- **Used by**: unused in file (final headline form for downstream consumers).
- **Visibility**: public
- **Lines**: 4910–5129 (proof: ~220 lines)
- **Notes**: `set_option maxHeartbeats 1600000 in` before the theorem; proof >30 lines (≈220 lines).

---

### File Summary

- **Total declarations**: 30 (1 def, 29 theorems).
  - 12 private theorems (helpers, recursive aggregators, per-window machinery).
  - 17 public theorems (multi-crossing CPV main results and HW3.3 spec forms).
  - 1 private noncomputable def (`antiderivPow`).

- **Key API (used by 3+ others in this file)**:
  - `exists_per_crossing_radius` (used by 3 theorems)
  - `antiderivPow` (used by 6 theorems)
  - `pow_inv_mul_deriv_intervalIntegrable` (used by 6 theorems)
  - `cpvIntegrand_higherOrder_intervalIntegrable` (used by 4 theorems)
  - `residueTheorem_crossing_full_spec` (used by 3 theorems)

- **Unused in this file (likely consumed externally)**:
  - `cpv_polarPart_at_multiCrossed_pole` (façade; superseded by conditional-angle variant)
  - `residueTheorem_crossing_full_spec_reparam`
  - `residueTheorem_crossing_full_spec_no_basepoint_with_transports`
  - `residueTheorem_crossing_full_spec_no_basepoint_basepoint_off`
  - `residueTheorem_crossing_paper_faithful_smooth`
  - `residueTheorem_crossing_paper_faithful_unique`
  - `residueTheorem_crossing_paper_faithful_clean` (the final headline result)

- **Declarations with `sorry`**: none.

- **Declarations with `set_option`**: `residueTheorem_crossing_paper_faithful_clean` (`maxHeartbeats 1600000`).

- **Proofs >30 lines**:
  - `cpv_tendsto_along_sorted` (≈314 lines)
  - `cpv_tendsto_along_sorted_corner` (≈262 lines)
  - `hasCauchyPV_inv_sub_multiCrossing` (≈204 lines)
  - `hasCauchyPV_inv_sub_multiCrossing_corner` (≈194 lines)
  - `perCrossing_higherOrder_window_integral_tendsto` (≈536 lines)
  - `cpv_higherOrder_tendsto_along_sorted` (≈365 lines)
  - `hasCauchyPVOn_multiCrossing_higherOrder` (≈270 lines)
  - `cpv_higherOrder_tendsto_along_sorted_corner` (≈341 lines)
  - `perCrossing_higherOrder_window_integral_tendsto_corner` (≈485 lines)
  - `hasCauchyPVOn_multiCrossing_higherOrder_corner` (≈291 lines)
  - `cpv_polarPart_at_multiCrossed_pole` (≈139 lines)
  - `cpv_polarPart_at_multiCrossed_pole_under_condB` (≈139 lines)
  - `cpv_polarPart_at_multiCrossed_pole_under_condB_corner` (≈152 lines)
  - `residueTheorem_crossing_full_spec` (≈68 lines)
  - `residueTheorem_crossing_full_spec_no_basepoint` (≈64 lines)
  - `residueTheorem_crossing_full_spec_no_basepoint_with_transports` (≈71 lines)
  - `residueTheorem_crossing_paper_faithful` (≈32 lines)
  - `residueTheorem_crossing_paper_faithful_clean` (≈220 lines)

- **File purpose (one paragraph)**: This file delivers the multi-crossing Cauchy Principal Value (CPV) theory underpinning Hungerbühler–Wasem Theorem 3.3 for closed piecewise-`C¹` immersions. It proves (i) `hasCauchyPV_inv_sub_multiCrossing` (T-BR-Y9d), the simple-pole CPV existence `∃ L, HasCauchyPV ((z-s)⁻¹) γ s L` for arbitrary cardinality of crossings of γ at a pole `s`; (ii) `hasCauchyPVOn_multiCrossing_higherOrder` (T-BR-Y9e), the higher-order CPV vanishing for `c/(z-s)^k` (k ≥ 2) under condition (B) smooth angle compatibility; and (iii) their corner-friendly twins (T-BR-Y11b, T-BR-Y11c) admitting crossings at piecewise-`C¹` partition (corner) points by accepting separate one-sided derivative limits and a corner-form `h_B`. These per-monomial results are composed into per-pole polar-part CPVs (`cpv_polarPart_at_multiCrossed_pole_under_condB[_corner]`) yielding `2πi · winding · residue` per pole, and aggregated into a tower of HW3.3 residue-theorem spec forms culminating in the headline `residueTheorem_crossing_paper_faithful_clean` (T-BR-Y11c). The proofs follow a uniform pattern: per-crossing flatness/angle conditions are combined with smooth-complement far-bounds and `intervalIntegral.integral_add_adjacent_intervals` to split the cutoff integral into smooth + window pieces; window pieces are evaluated via FTC `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le` with `antiderivPow s k` as the antiderivative, while smooth pieces are constant in ε; recursive aggregation over a sorted list of crossings (`Finset.sortedLT_sort`) yields the global limit.
