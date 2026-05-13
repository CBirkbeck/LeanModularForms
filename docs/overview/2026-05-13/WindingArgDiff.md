# Inventory: WindingArgDiff.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/WindingArgDiff.lean`
Lines: 394

### `theorem Complex.contourIntegral_inv_eq_sum_log_segRatio`
- **Type**: `(γ : PiecewiseC1Path x y) {w : ℂ} {N : ℕ} (_hN : 0 < N) {s : ℕ → ℝ} (hs_zero : s 0 = 0) (hs_N : s N = 1) (hs_mono : Monotone s) (hs_in : ∀ j ≤ N, s j ∈ Icc 0 1) (h_avoid : ∀ j ≤ N, γ.toPath.extend (s j) - w ≠ 0) (h_slit : ∀ j, j < N → ∀ t ∈ Icc (s j) (s (j+1)), (γ.toPath.extend t - w) / (γ.toPath.extend (s j) - w) ∈ slitPlane) (h_int : IntervalIntegrable (deriv γ.toPath.extend / (γ.toPath.extend t - w)) volume 0 1) : γ.contourIntegral (fun z => (z - w)⁻¹) = ∑ j ∈ Finset.range N, Complex.log ((γ.toPath.extend (s (j+1)) - w) / (γ.toPath.extend (s j) - w))`
- **What**: For a fine-enough partition `s_0=0, …, s_N=1` ensuring each segment ratio lies in `Complex.slitPlane`, the contour integral of `(z - w)⁻¹` along γ equals the sum of complex logs of consecutive segment ratios.
- **How**: (1) Rewrite contour integral as `∫_0^1 γ'(t)/(γ(t) - w) dt` via `intervalIntegral.integral_congr` and `div_eq_mul_inv` + `mul_comm`. (2) Split into adjacent intervals using `intervalIntegral.sum_integral_adjacent_intervals` with segment integrability via `h_int.mono_set`. (3) On each `[s_j, s_{j+1}]` apply `segment_log_FTC` (continuity of γ, differentiability off the partition, slitPlane membership, non-vanishing at left endpoint).
- **Hypotheses**: monotone partition `s` with `s 0 = 0, s N = 1`, all `γ(s j) ≠ w`, slitPlane membership per segment, interval-integrability of the integrand.
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.contourIntegral`, `PiecewiseC1Path.partition`, `PiecewiseC1Path.differentiable_off`, `segment_log_FTC`.
- **Used by**: `contourIntegral_inv_decomp`.
- **Visibility**: public
- **Lines**: 45-102
- **Notes**: ~58 line proof

### `theorem Complex.contourIntegral_inv_decomp`
- **Type**: Same fine-partition hypotheses as `contourIntegral_inv_eq_sum_log_segRatio` (and same `h_int`), conclusion `γ.contourIntegral (fun z => (z - w)⁻¹) = ((Real.log ‖γ 1 - w‖ - Real.log ‖γ 0 - w‖ : ℝ) : ℂ) + I * ((∑_{j < N} (Complex.log ((γ(s(j+1)) - w) / (γ(s j) - w))).im : ℝ) : ℂ)`.
- **What**: Real/imaginary decomposition of the contour integral — the real part telescopes through `Real.log` of curve norms; the imaginary part is the sum of imaginary parts of consecutive segment logs (multiplied by I).
- **How**: Apply `contourIntegral_inv_eq_sum_log_segRatio` to rewrite as a finite sum of logs; use `Complex.ext`; for the real part, use `Complex.re_sum` + `Complex.log_re` + `norm_div` + `Real.log_div` (consuming non-vanishing of γ(s_j) - w) + `Finset.sum_range_sub` (telescoping); for imaginary, `Complex.im_sum`.
- **Hypotheses**: same as `contourIntegral_inv_eq_sum_log_segRatio`.
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.contourIntegral`, `contourIntegral_inv_eq_sum_log_segRatio`.
- **Used by**: `hasGeneralizedWindingNumber_eq_arg_diff_W1_closed`.
- **Visibility**: public
- **Lines**: 107-147
- **Notes**: ~41 line proof; uses `calc` for the real-part telescoping

### `theorem Complex.hasGeneralizedWindingNumber_eq_arg_diff_W1_closed`
- **Type**: `(γ : PiecewiseC1Path x x) {w : ℂ} (hδ : ∃ δ > 0, ∀ t ∈ Icc 0 1, δ ≤ ‖γ.toPath.extend t - w‖) (h_int : IntervalIntegrable (deriv γ.toPath.extend / (γ.toPath.extend t - w)) volume 0 1) : ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 1) ∧ (∀ t ∈ Icc 0 1, γ.toPath.extend t - w = (‖γ.toPath.extend t - w‖ : ℂ) * Complex.exp (I * (θ t : ℂ))) ∧ HasGeneralizedWindingNumber γ w (((θ 1 - θ 0 : ℝ) : ℂ) / (2 * Real.pi))`
- **What**: **W-2.** For a closed PwC1 path avoiding w with positive distance, there exists a continuous arg lift `θ` of `γ - w` such that the generalized winding number equals `(θ(1) - θ(0)) / (2π)`.
- **How**: Use `Complex.exists_continuous_arg_lift_with_partition` to build `θ` and a fine partition `s` with `s_j` avoiding 0 and segment ratios in slitPlane. Explicit θ via `Complex.arg (γ(0) - w) + ∑_j Im(log(segRatio …))`. Compute θ(0) using `segRatio_eq_one_of_le` (segRatio equals 1 at the left endpoint) so all summands have zero imaginary part. Compute θ(1) using `segRatio_eq_full`. For closed γ, `γ(1) - w = γ(0) - w`, so the real part of the contour integral vanishes (Real.log ‖γ(1) - w‖ - Real.log ‖γ(0) - w‖ = 0). Apply `contourIntegral_inv_decomp` and `hasGeneralizedWindingNumber_of_avoids`; finish by `field_simp` to rewrite `(θ 1 - θ 0)/(2π)` in the required form.
- **Hypotheses**: closed PwC1 path γ; γ stays at positive distance δ from w; interval-integrability of `γ'(t)/(γ(t) - w)`.
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.toPath`, `HasGeneralizedWindingNumber`, `Complex.exists_continuous_arg_lift_with_partition`, `Complex.segRatio`, `Complex.segRatio_eq_one_of_le`, `Complex.segRatio_eq_full`, `contourIntegral_inv_decomp`, `hasGeneralizedWindingNumber_of_avoids`.
- **Used by**: `hasGeneralizedWindingNumber_integer_of_closed`.
- **Visibility**: public
- **Lines**: 154-240
- **Notes**: ~87 line proof; central W-2 theorem

### `theorem Complex.hasGeneralizedWindingNumber_integer_of_closed`
- **Type**: `(γ : PiecewiseC1Path x x) {w : ℂ} (hδ : ∃ δ > 0, ∀ t ∈ Icc 0 1, δ ≤ ‖γ.toPath.extend t - w‖) (h_int : IntervalIntegrable ... volume 0 1) : ∃ n : ℤ, HasGeneralizedWindingNumber γ w (n : ℂ)`
- **What**: **W-3.** For a closed PwC1 path avoiding w with positive distance, the generalized winding number is an integer.
- **How**: Obtain `θ` from `hasGeneralizedWindingNumber_eq_arg_diff_W1_closed`. From closedness `γ(1) = γ(0)` and the lift identity `γ(t) - w = ‖γ(t) - w‖ · exp(I · θ(t))`, cancel the (non-zero) norm factor via `mul_left_cancel₀` to get `exp(I · θ(0)) = exp(I · θ(1))`. Hence `exp(I · (θ(1) - θ(0))) = 1` (via `Complex.exp_sub` + `div_self`). Apply `Complex.exp_eq_one_iff` to extract an integer `n` with `I · (θ(1) - θ(0)) = I · n · 2π`; cancel `I` (`I_ne_zero`) and `2π` (`Real.pi_ne_zero`) via `field_simp` to get `(θ(1) - θ(0))/(2π) = n`.
- **Hypotheses**: closed PwC1 path; positive distance bound; interval-integrability.
- **Uses from project**: `PiecewiseC1Path`, `HasGeneralizedWindingNumber`, `hasGeneralizedWindingNumber_eq_arg_diff_W1_closed`.
- **Used by**: `generalizedWindingNumber_locally_const_of_closed`.
- **Visibility**: public
- **Lines**: 246-302
- **Notes**: ~57 line proof; integer-valued winding from W-2

### `theorem intervalIntegrable_div_lipschitz`
- **Type**: `(γ : PiecewiseC1Path x y) {w : ℂ} {δ : ℝ} (_hδ_pos : 0 < δ) (h_dist_lb : ∀ t ∈ Icc 0 1, δ ≤ ‖γ.toPath.extend t - w‖) {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) : IntervalIntegrable (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - w)) volume 0 1`
- **What**: For Lipschitz γ at positive distance δ from w, the integrand `γ'(t) / (γ(t) - w)` is interval-integrable on `[0,1]`.
- **How**: Use `stronglyMeasurable_deriv` for measurability; bound `‖γ'(t)‖ ≤ K` via `norm_deriv_le_of_lipschitz`; conclude integrability of γ' via `Measure.integrableOn_of_bounded` on `Ioc`. Show `(γ(t) - w)⁻¹` is continuous on `[0,1]` via `(continuous_extend.sub continuousOn_const).inv₀` (using `h_avoid`); combine via `IntervalIntegrable.mul_continuousOn` after rewriting `div = mul ∘ inv`.
- **Hypotheses**: γ Lipschitz; γ at positive distance δ from w on `[0,1]`.
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.toPath`, `norm_deriv_le_of_lipschitz`.
- **Used by**: `generalizedWindingNumber_locally_const_of_closed`.
- **Visibility**: public
- **Lines**: 308-336

### `theorem Complex.generalizedWindingNumber_locally_const_of_closed`
- **Type**: `(γ : PiecewiseC1Path x x) {w : ℂ} (h_avoid : ∀ t ∈ Icc 0 1, γ.toPath.extend t ≠ w) {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) : ∃ ε > 0, ∀ w' ∈ Metric.ball w ε, generalizedWindingNumber γ w' = generalizedWindingNumber γ w`
- **What**: **W-4.** For a closed Lipschitz PwC1 path avoiding w, the generalized winding number is constant on a neighborhood of w.
- **How**: From `ball_dist_to_curve_lb` get ε₀ > 0 with γ at distance ≥ ε₀/2 from every w' in `B(w, ε₀)`. From `generalizedWindingNumber_continuousAt_of_avoids` get ε > 0 with `|w(γ, w') - w(γ, w)| < 1/2` for w' in `B(w, ε)`. Take `min ε ε₀`. By W-3 (`hasGeneralizedWindingNumber_integer_of_closed`) both `w(γ, w')` and `w(γ, w)` are integers; their distance < 1/2 implies they are equal (since `|n - m| ≥ 1` whenever `n ≠ m`, via `Int.one_le_abs` + `Complex.norm_intCast`). Discharge integrability via `intervalIntegrable_div_lipschitz`.
- **Hypotheses**: closed PwC1 path γ; γ avoids w on `[0,1]`; γ Lipschitz.
- **Uses from project**: `PiecewiseC1Path`, `ball_dist_to_curve_lb`, `generalizedWindingNumber`, `generalizedWindingNumber_continuousAt_of_avoids`, `HasGeneralizedWindingNumber`, `hasGeneralizedWindingNumber_integer_of_closed`, `intervalIntegrable_div_lipschitz`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 342-390
- **Notes**: ~49 line proof; central W-4 theorem

## File Summary

Six theorems (one structure-free) building the **W-1 through W-4** chain for the generalized winding number of closed piecewise C¹ paths:
- **W-1/W-2** (`contourIntegral_inv_eq_sum_log_segRatio` + `contourIntegral_inv_decomp` + `hasGeneralizedWindingNumber_eq_arg_diff_W1_closed`): contour integral telescopes through complex logs, decomposes into real (log-norm) + imaginary (arg-difference) parts, and the winding number equals `(θ(1) - θ(0)) / (2π)` for a continuous arg lift `θ`.
- **W-3** (`hasGeneralizedWindingNumber_integer_of_closed`): closedness forces `exp(I(θ(1) - θ(0))) = 1`, hence the winding number is an integer.
- **W-4** (`generalizedWindingNumber_locally_const_of_closed`): integer-valued + continuous implies locally constant, with `intervalIntegrable_div_lipschitz` as a discharge helper.

No `sorry`/`axiom`/heartbeat overrides. All six declarations are public.
