# DixonDiff.lean Inventory

File: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/DixonDiff.lean
Lines: 802

### `private lemma curveImage_compact`
- **Type**: `(γ : PiecewiseC1Path x x) : IsCompact (γ.toPath.extend '' Icc (0 : ℝ) 1)`
- **What**: The image of a piecewise-C¹ path on the parameter interval `[0,1]` is compact.
- **How**: One-liner: image of compact `Icc 0 1` under continuous `γ.toPath.extend` is compact (`isCompact_Icc.image`).
- **Hypotheses**: `γ : PiecewiseC1Path x x`.
- **Uses from project**: `PiecewiseC1Path`.
- **Used by**: `curveImage_infDist_pos`.
- **Visibility**: private.
- **Lines**: 40-42.
- **Notes**: short.

### `private lemma curveImage_nonempty`
- **Type**: `(γ : PiecewiseC1Path x x) : (γ.toPath.extend '' Icc (0 : ℝ) 1).Nonempty`
- **What**: The image of `[0,1]` under `γ` is nonempty.
- **How**: Witness is `γ.toPath.extend 0`, which is in the image via `mem_image_of_mem` with `left_mem_Icc`.
- **Hypotheses**: `γ : PiecewiseC1Path x x`.
- **Uses from project**: `PiecewiseC1Path`.
- **Used by**: `curveImage_infDist_pos`.
- **Visibility**: private.
- **Lines**: 44-46.
- **Notes**: short.

### `private lemma curveImage_infDist_pos`
- **Type**: `(γ : PiecewiseC1Path x x) (w : ℂ) (hoff : ∀ t ∈ Icc 0 1, γ t ≠ w) : 0 < Metric.infDist w (γ.toPath.extend '' Icc 0 1)`
- **How**: Uses `IsCompact.isClosed.notMem_iff_infDist_pos` with `curveImage_compact` and `curveImage_nonempty`; the `notMem` is unpacked into the contrapositive of `hoff`.
- **What**: Positive infimum distance from a point `w` off a compact path image.
- **Hypotheses**: `hoff : γ avoids w on Icc 0 1`.
- **Uses from project**: `curveImage_compact`, `curveImage_nonempty`, `PiecewiseC1Path`.
- **Used by**: `dixonH2_differentiableAt`, `dixonH2_differentiableAt_of_regular`, `dixonFunction_differentiable`.
- **Visibility**: private.
- **Lines**: 48-52.
- **Notes**: short.

### `private lemma ball_avoids_curve`
- **Type**: `(γ : PiecewiseC1Path x x) (w : ℂ) {ε : ℝ} (hε : 0 < ε) (hε_le : 2 * ε ≤ Metric.infDist w (γ.image)) : ∀ w' ∈ Metric.ball w ε, ∀ t ∈ Icc 0 1, γ t ≠ w'`
- **What**: If `2ε` is below the infDist from `w` to the curve, then every `w'` in the open ball `B(w, ε)` is avoided by the curve.
- **How**: Triangle inequality: `infDist w (image) ≤ dist w (γ t) = dist w w'` (if `γ t = w'`), but `dist w w' < ε`, contradicting `2ε ≤ infDist`.
- **Hypotheses**: `0 < ε`, `2ε ≤ infDist w (image)`.
- **Uses from project**: `PiecewiseC1Path`.
- **Used by**: `dixonH2_differentiableAt`, `dixonH2_differentiableAt_of_regular`, `dixonFunction_differentiable`.
- **Visibility**: private.
- **Lines**: 54-63.
- **Notes**: short.

### `private lemma ball_dist_lower_bound`
- **Type**: `(γ : PiecewiseC1Path x x) (w : ℂ) {ε : ℝ} (hε_le : 2 * ε ≤ Metric.infDist w (γ.image)) : ∀ w' ∈ Metric.ball w ε, ∀ t ∈ Icc 0 1, ε ≤ ‖γ t - w'‖`
- **What**: Distance lower bound `‖γ t − w'‖ ≥ ε` on a `B(w, ε)` ball under the `2ε ≤ infDist` premise.
- **How**: Triangle inequality `‖γt − w'‖ ≥ ‖γt − w‖ − ‖w − w'‖ ≥ 2ε − ε = ε`; uses `norm_sub_norm_le` and `norm_sub_rev`.
- **Hypotheses**: `2ε ≤ infDist w (image)`.
- **Uses from project**: `PiecewiseC1Path`.
- **Used by**: `dixonH2_differentiableAt`, `dixonH2_differentiableAt_of_regular`.
- **Visibility**: private.
- **Lines**: 65-79.
- **Notes**: short (15 lines).

### `private lemma h2_pointwise_hasDerivAt`
- **Type**: `(fz c z w : ℂ) (hne : z - w ≠ 0) : HasDerivAt (fun w' => fz * (z - w')⁻¹ * c) (fz * (z - w)⁻¹ ^ 2 * c) w`
- **What**: The function `w' ↦ fz·(z−w')⁻¹·c` has complex derivative `fz·(z−w)⁻²·c` at `w` when `z ≠ w`.
- **How**: Chain rule: `(z − w')` has derivative `−1`, hence `(z − w')⁻¹` has derivative `−(−1)·(z − w)⁻²` via `HasDerivAt.inv`; then multiply by constants and `congr_deriv`/`ring`.
- **Hypotheses**: `z - w ≠ 0`.
- **Uses from project**: [].
- **Used by**: `dixonH2_differentiableAt`.
- **Visibility**: private.
- **Lines**: 83-93.
- **Notes**: short.

### `private lemma h2_integrand_norm_bound`
- **Type**: gives `‖f(γt) * (γt − w')⁻² * deriv γ t‖ ≤ M · ε⁻² · D` when `‖f∘γ‖ ≤ M`, `‖γ'‖ ≤ D`, and the curve stays at distance `≥ ε` from the ball.
- **What**: Pointwise majorant for the h2-derivative integrand on a tube of radius ε about `w`.
- **How**: Decompose `norm_mul`, `norm_pow`, `norm_inv`, then chain `mul_le_mul` with `pow_le_pow_left₀` and `inv_anti₀` on the distance bound.
- **Hypotheses**: `0 ≤ M`, `0 < ε`, `hM`, `hD`, `h_dist_lb`, `t ∈ Ioc 0 1`, `w' ∈ Metric.ball w ε`.
- **Uses from project**: `PiecewiseC1Path`.
- **Used by**: `dixonH2_differentiableAt`.
- **Visibility**: private.
- **Lines**: 95-112.
- **Notes**: short (16 lines).

### `theorem dixonH2_differentiableAt`
- **Type**: Conditions (curve avoids `w`, integrability, bounded `f∘γ`, bounded `γ'`, measurability of integrand and its derivative variant) → `DifferentiableAt ℂ (dixonH2 f γ) w`.
- **What**: Dixon's `h2` integral function is holomorphic at every point off the curve, given external regularity oracles.
- **How**: KEY: invoke `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` (parametric Leibniz rule) with the F/F'/bound triple; pointwise derivative comes from `h2_pointwise_hasDerivAt`, bound from `h2_integrand_norm_bound`, and ε halves the infimum distance.
- **Hypotheses**: 6 oracle hypotheses: `hoff`, `h_int`, `h_fγ_bound`, `h_deriv_bound`, `h_meas`, `h_F'_meas`.
- **Uses from project**: `PiecewiseC1Path`, `dixonH2`, `curveImage_infDist_pos`, `ball_avoids_curve`, `ball_dist_lower_bound`, `h2_pointwise_hasDerivAt`, `h2_integrand_norm_bound`.
- **Used by**: `dixonH2_differentiableAt_of_regular`.
- **Visibility**: public (theorem).
- **Lines**: 119-163.
- **Notes**: 45 lines.

### `private lemma dixonH2_integrand_stronglyMeasurable`
- **Type**: gives `AEStronglyMeasurable (t ↦ f(γt)·(γt − w')⁻¹·γ'(t))` on the restricted measure space.
- **What**: Strong-measurability of the h2 integrand.
- **How**: Factor as continuous `f∘γ` times continuous `(γ − w')⁻¹` (using `ContinuousOn.inv₀` and the `hoff` non-vanishing), times the (a.e. strongly measurable) `stronglyMeasurable_deriv`.
- **Hypotheses**: `hf_cont`, `hoff`.
- **Uses from project**: `PiecewiseC1Path`.
- **Used by**: `dixonH2_differentiableAt_of_regular`.
- **Visibility**: private.
- **Lines**: 169-186.
- **Notes**: short (18 lines).

### `private lemma dixonH2_deriv_integrand_stronglyMeasurable`
- **Type**: same as above but with `(γ − w)⁻¹^2` (second-order).
- **What**: Strong-measurability of the differentiated h2 integrand (the F' for the Leibniz rule).
- **How**: As `dixonH2_integrand_stronglyMeasurable` but with `.pow 2` on the inverse continuity factor.
- **Hypotheses**: `hf_cont`, `hoff`.
- **Uses from project**: `PiecewiseC1Path`.
- **Used by**: `dixonH2_differentiableAt_of_regular`.
- **Visibility**: private.
- **Lines**: 189-206.
- **Notes**: short.

### `theorem dixonH2_differentiableAt_of_regular`
- **Type**: From `hoff`, `f` continuous on `γ.image`, and `γ.extend` `K`-Lipschitz → `DifferentiableAt ℂ (dixonH2 f γ) w`.
- **What**: B-3 bundle: discharges all six oracles of `dixonH2_differentiableAt` from minimal regularity.
- **How**: KEY: lemma `dixonH2_differentiableAt` is called after building all six prerequisites — `h_deriv_bound` via `norm_deriv_le_of_lipschitz`, `h_fγ_bound` via `IsCompact.bddAbove_image` on `f∘γ`, measurability via `dixonH2_(deriv_)integrand_stronglyMeasurable`, integrability built from a bounded a.e.-strongly-measurable integrand on `Ioc 0 1`.
- **Hypotheses**: `hoff`, `hf_cont`, `hLip`.
- **Uses from project**: `PiecewiseC1Path`, `dixonH2`, `curveImage_infDist_pos`, `ball_avoids_curve`, `ball_dist_lower_bound`, `dixonH2_integrand_stronglyMeasurable`, `dixonH2_deriv_integrand_stronglyMeasurable`, `dixonH2_differentiableAt`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 215-274.
- **Notes**: 60 lines.

### `private lemma dslope_comm`
- **Type**: `(f : ℂ → ℂ) (a b : ℂ) : dslope f a b = dslope f b a`
- **What**: `dslope` (divided difference) is symmetric in its two arguments.
- **How**: Case split on `b = a`; equal case is `rfl`-like after rewrite, distinct case uses `dslope_of_ne` and `slope_comm`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `dslope_hasDerivAt_first_arg`, `dslope_fixed_continuousOn`.
- **Visibility**: private.
- **Lines**: 280-283.
- **Notes**: short.

### `private lemma dslope_hasDerivAt_first_arg`
- **Type**: For open `U`, `f` differentiable on `U`, `c, w ∈ U`: `HasDerivAt (fun w' => dslope f w' c) (deriv (dslope f c) w) w`.
- **What**: Differentiability in the first argument of `dslope` reduces to the second-argument case via symmetry.
- **How**: Use `Complex.differentiableOn_dslope` (second-arg version) to get `DifferentiableAt`, then `hasDerivAt`, then `congr_of_eventuallyEq` with `dslope_comm`.
- **Hypotheses**: `IsOpen U`, `DifferentiableOn ℂ f U`, `c ∈ U`, `w ∈ U`.
- **Uses from project**: `dslope_comm`.
- **Used by**: `dixonH1_differentiableOn_of_regular`.
- **Visibility**: private.
- **Lines**: 288-294.
- **Notes**: short.

### `private lemma dslope_fixed_continuousOn`
- **Type**: For `U` open, `f` differentiable on `U`, `γ` mapping into `U`, `w ∈ U`: `ContinuousOn (fun t => dslope f w (γ t)) (Icc 0 1)`.
- **What**: With `w` fixed in `U`, the composition `t ↦ dslope f w (γt)` is continuous on the unit interval.
- **How**: `(Complex.differentiableOn_dslope).mpr.continuousOn` for `dslope f w : U → ℂ`, then compose with continuous `γ.extend`.
- **Hypotheses**: `IsOpen U`, `DifferentiableOn ℂ f U`, `γ image in U`, `w ∈ U`.
- **Uses from project**: `PiecewiseC1Path`.
- **Used by**: `dixonH1_integrand_stronglyMeasurable`, `dixonH1_differentiableOn_of_regular`.
- **Visibility**: private.
- **Lines**: 299-306.
- **Notes**: short.

### `private lemma min3_ball_subsets`
- **Type**: Given three positive radii, the ball of radius `min·all/2` is contained in each of the three balls of the original radii.
- **What**: Triple-min ball-subset combinator.
- **How**: `Metric.ball_subset_ball` with arithmetic comparison via `min_le_left/right` and `linarith`.
- **Hypotheses**: positivity of `ε_m`, `ε_d`, `δ_C`.
- **Uses from project**: [].
- **Used by**: `dixonH1_differentiableOn`.
- **Visibility**: private.
- **Lines**: 309-319.
- **Notes**: short.

### `private lemma dslope_deriv_product_bound`
- **Type**: ae bound `‖deriv (dslope f (γ t)) w · γ'(t)‖ ≤ C·D` on `Set.uIoc 0 1`.
- **What**: Combines a uniform bound `C` for `deriv (dslope f (γt)) w` on a ball with a uniform bound `D` for `γ'`.
- **How**: `filter_upwards`, `Set.uIoc_of_le zero_le_one`, then `norm_mul` and `mul_le_mul`.
- **Hypotheses**: `h_deriv_bd`, `hD`, `hball_sub`.
- **Uses from project**: `PiecewiseC1Path` (implicit `w₀`, `δ_C`, `f`, `ε` are section-implicit names without binders here).
- **Used by**: `dixonH1_differentiableOn`.
- **Visibility**: private.
- **Lines**: 322-335.
- **Notes**: short. Free variables `w₀ δ_C f ε` are auto-bound section variables in this `private` lemma.

### `theorem dixonH1_differentiableOn`
- **Type**: With 7 oracle hypotheses on integrability, measurability, `dslope` derivatives, and bounds → `DifferentiableOn ℂ (dixonH1 f γ.toPiecewiseC1Path) U`.
- **What**: Dixon's `h1` is holomorphic on `U`.
- **How**: KEY: `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` again, with the dominated bound being the product of two bounds (`dslope_deriv_product_bound`) and the pointwise derivative oracle `h_dslope_hasDerivAt` plugged in.
- **Hypotheses**: many: `_hU`, `_hf`, `_hγ`, `h_int`, `h_meas`, `h_deriv_bound`, `h_dslope_hasDerivAt`, `h_F'_meas`, `h_dslope_deriv_bound`.
- **Uses from project**: `PwC1Immersion`, `PiecewiseC1Path`, `dixonH1`, `min3_ball_subsets`, `dslope_deriv_product_bound`.
- **Used by**: `dixonH1_differentiableOn_of_regular`.
- **Visibility**: public.
- **Lines**: 340-388.
- **Notes**: 49 lines.

### `private lemma dixonH1_integrand_stronglyMeasurable`
- **Type**: gives `AEStronglyMeasurable (t ↦ dslope f w (γt) · γ'(t))` on `Set.uIoc 0 1`.
- **What**: Strong-measurability of the dixonH1 integrand.
- **How**: Use `dslope_fixed_continuousOn` to get continuity of `t ↦ dslope f w (γt)` on `Icc 0 1`, restrict to `Ioc 0 1`, take a.e. strong measurability, multiply by `stronglyMeasurable_deriv`.
- **Hypotheses**: `hU`, `hf`, `hγ`, `hw`.
- **Uses from project**: `dslope_fixed_continuousOn`, `PiecewiseC1Path`.
- **Used by**: `dixonH1_differentiableOn_of_regular`.
- **Visibility**: private.
- **Lines**: 394-406.
- **Notes**: short.

### `theorem dixonH1_differentiableOn_of_regular`
- **Type**: With `f` differentiable on `U`, `γ` Lipschitz `PwC1Immersion` into `U`, and two oracles `h_F'_meas` & `h_dslope_deriv_bound` → `DifferentiableOn ℂ (dixonH1 f γ) U`.
- **What**: B-2 partial bundle: discharges 5 of the 7 oracles of `dixonH1_differentiableOn`.
- **How**: KEY: lemma `dixonH1_differentiableOn` invoked after building (a) integrability from bounded continuous integrand on finite-measure `Ioc`, (b) local measurability from `dixonH1_integrand_stronglyMeasurable`, (c) `h_dslope_hasDerivAt` from `dslope_hasDerivAt_first_arg`, (d) `h_deriv_bound` from `norm_deriv_le_of_lipschitz`.
- **Hypotheses**: `hU`, `hf`, `hγ`, `hLip`, `h_F'_meas`, `h_dslope_deriv_bound`.
- **Uses from project**: `PwC1Immersion`, `dixonH1`, `dixonH1_integrand_stronglyMeasurable`, `dslope_fixed_continuousOn`, `dslope_hasDerivAt_first_arg`, `dixonH1_differentiableOn`.
- **Used by**: `dixonH1_differentiableOn_of_regular_convex`, `dixonH1_differentiableOn_of_regular_open`.
- **Visibility**: public.
- **Lines**: 421-480.
- **Notes**: 60 lines.

### `theorem dixonH1_differentiableOn_of_regular_convex`
- **Type**: Same as above but auto-discharges `h_dslope_deriv_bound` via D-1c for convex `U`.
- **What**: B-2 bundle with auto-discharge of dslope-derivative bound for convex domains.
- **How**: Build `h_dslope_deriv_bound` via `Complex.deriv_dslope_bounded_on_compact` on the compact `γ` image, then apply `dixonH1_differentiableOn_of_regular`.
- **Hypotheses**: `hU_convex`, `hU`, `hf`, `hγ`, `hLip`, `h_F'_meas`.
- **Uses from project**: `PwC1Immersion`, `dixonH1`, `dixonH1_differentiableOn_of_regular`.
- **Used by**: `dixonH1_differentiableOn_of_regular_convex_full`.
- **Visibility**: public.
- **Lines**: 486-508.
- **Notes**: 23 lines.

### `theorem dixonH1_differentiableOn_of_regular_open`
- **Type**: As `..._convex` but uses the open (non-convex) variant `Complex.deriv_dslope_bounded_on_compact_open`.
- **What**: B-2 bundle dropping the convexity requirement.
- **How**: Identical structure to `..._convex` using the open analogue of D-1c.
- **Hypotheses**: `hU`, `hf`, `hγ`, `hLip`, `h_F'_meas`.
- **Uses from project**: `PwC1Immersion`, `dixonH1`, `dixonH1_differentiableOn_of_regular`.
- **Used by**: `dixonH1_differentiableOn_of_regular_open_full`.
- **Visibility**: public.
- **Lines**: 514-536.
- **Notes**: 23 lines.

### `theorem dixonH1_differentiableOn_of_regular_convex_full`
- **Type**: For convex open `U`, differentiable `f`, Lipschitz `PwC1Immersion γ` into `U` → `DifferentiableOn ℂ (dixonH1 f γ) U`.
- **What**: B-2 fully closed (convex): auto-discharges every oracle, including `h_F'_meas`.
- **How**: KEY: builds `h_F'_meas` via a sequential a.e. limit — `q n t := (dslope f (γt) (w₀ + h_n) − dslope f (γt) w₀)/h_n · γ'(t)` is shown a.e. strongly measurable (via `Complex.continuousOn_dslope_first_arg`), then `aestronglyMeasurable_of_tendsto_ae` with `tendsto_slope` (the slope tends to `deriv (dslope f (γt)) w₀`).
- **Hypotheses**: `hU_convex`, `hU`, `hf`, `hγ`, `hLip`.
- **Uses from project**: `PwC1Immersion`, `dixonH1`, `dixonH1_differentiableOn_of_regular_convex`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 541-640.
- **Notes**: 100 lines (long). Sequential a.e. measurability argument is the heavy lifting.

### `theorem dixonH1_differentiableOn_of_regular_open_full`
- **Type**: Same as `..._convex_full` without convexity.
- **What**: B-2 fully closed (open): auto-discharges every oracle using the open variant of `continuousOn_dslope_first_arg`.
- **How**: Identical structure to `..._convex_full`, but invokes `Complex.continuousOn_dslope_first_arg_open` instead and chains to `dixonH1_differentiableOn_of_regular_open`.
- **Hypotheses**: `hU`, `hf`, `hγ`, `hLip`.
- **Uses from project**: `PwC1Immersion`, `dixonH1`, `dixonH1_differentiableOn_of_regular_open`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 644-738.
- **Notes**: 95 lines (long). Mirror of the convex full bundle.

### `theorem dixonFunction_differentiable`
- **Type**: For open `U`, `f` differentiable on `U`, null-homologous `γ`, with `h1`/`h2`-differentiability and the fundamental identity → `Differentiable ℂ (dixonFunction f U γ.toPiecewiseC1Path)`.
- **What**: The Dixon function is entire (the central conclusion of Dixon's proof of Cauchy's theorem).
- **How**: KEY: Case split on `w ∈ U`. On `U`: `dixonFunction = dixonH1` near `w` (`dixonFunction_eq_dixonH1`) — apply `h1_diff` via `congr_of_eventuallyEq`. Off `U`: curve lies in `U` (from null-homology), so `w` is off the curve; winding number is zero on a small ball (from `h_winding_zero_near`), and the identity collapses `h1 = h2`, then `h2_diff` carries us through.
- **Hypotheses**: `hU`, `_hf`, `γ`, `h_null`, `h1_diff`, `h2_diff`, `h_identity`, `h_winding_zero_near`.
- **Uses from project**: `PwC1Immersion`, `dixonH1`, `dixonH2`, `dixonFunction`, `dixonFunction_eq_dixonH1`, `IsNullHomologous`, `generalizedWindingNumber`, `curveImage_infDist_pos`, `ball_avoids_curve`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 749-800.
- **Notes**: 52 lines.

## File Summary

- **Total declarations**: 23 (8 public theorems, 15 private lemmas).
- **Key API**: `dixonH2_differentiableAt`, `dixonH2_differentiableAt_of_regular`, `dixonH1_differentiableOn`, `dixonH1_differentiableOn_of_regular`, `dixonH1_differentiableOn_of_regular_convex`, `dixonH1_differentiableOn_of_regular_open`, `dixonH1_differentiableOn_of_regular_convex_full`, `dixonH1_differentiableOn_of_regular_open_full`, `dixonFunction_differentiable`.
- **Unused in file**: `dixonH2_differentiableAt_of_regular`, `dixonH1_differentiableOn_of_regular_convex_full`, `dixonH1_differentiableOn_of_regular_open_full`, `dixonFunction_differentiable` (these are the public endpoints — used downstream).
- **Sorries**: 0.
- **`set_option` lines**: 0.
- **Long proofs (>30 lines)**: `dixonH2_differentiableAt` (45), `dixonH2_differentiableAt_of_regular` (60), `dixonH1_differentiableOn` (49), `dixonH1_differentiableOn_of_regular` (60), `dixonH1_differentiableOn_of_regular_convex_full` (100), `dixonH1_differentiableOn_of_regular_open_full` (95), `dixonFunction_differentiable` (52).
- **Purpose**: Establishes that the three functions arising in Dixon's proof of Cauchy's integral theorem are holomorphic: the parametric Cauchy-kernel integral `dixonH2` is holomorphic off the curve, the "averaged" function `dixonH1` is holomorphic on `U`, and the patched `dixonFunction` is entire on `ℂ`. The proof uses the parametric Leibniz rule (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) with carefully verified dominated bounds, plus the null-homology / winding-number identity to glue `h1` and `h2` across the boundary of `U`. The file builds a tower of progressively higher-level "regular" bundles (`_of_regular`, `_of_regular_convex`, `_of_regular_open`, `..._full`) so that downstream applications only need standard regularity hypotheses (Lipschitz curve, continuous `f`).
