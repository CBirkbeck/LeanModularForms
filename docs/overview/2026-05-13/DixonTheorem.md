# DixonTheorem.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/DixonTheorem.lean` (888 lines)

Imports: `LeanModularForms.ForMathlib.DixonDiff`, `Mathlib.Analysis.Complex.Liouville`.

Opens: `Complex Set Filter Topology MeasureTheory`; scoped `Classical Real Interval`.

### `private lemma curve_dist_lower_bound`
- **Type**: `{γ : PiecewiseC1Path x x} {R : ℝ} {w : ℂ} (hR : ∀ t ∈ Icc 0 1, ‖γ t‖ ≤ R) {t} (ht : t ∈ Icc 0 1) : ‖w‖ - R ≤ ‖γ t - w‖`
- **What**: Reverse triangle inequality: if `‖γ t‖ ≤ R`, the distance from `w` to a curve point is at least `‖w‖ - R`.
- **How**: `norm_sub_norm_le w (γ t)` plus `norm_sub_rev` and `linarith`.
- **Hypotheses**: Curve `γ : PiecewiseC1Path x x`, uniform bound `‖γ t‖ ≤ R` on `[0,1]`.
- **Uses from project**: `PiecewiseC1Path` (its `CoeFun` to `ℝ → ℂ`).
- **Used by**: `dixonH2_norm_le`.
- **Visibility**: private.
- **Lines**: 58–63.
- **Notes**: 5 lines.

### `private lemma norm_gt_mem_cocompact`
- **Type**: `(R : ℝ) : {w : ℂ | R < ‖w‖} ∈ Filter.cocompact ℂ`
- **What**: The set `{w : ‖w‖ > R}` lies in the cocompact filter of `ℂ`.
- **How**: Witness with `Metric.closedBall 0 R` which is compact via `isCompact_closedBall`.
- **Hypotheses**: none beyond `R : ℝ`.
- **Uses from project**: [].
- **Used by**: `dixonH2_tendsto_zero`.
- **Visibility**: private.
- **Lines**: 66–72.
- **Notes**: 6 lines.

### `theorem dixonH2_norm_le`
- **Type**: `{f γ} {R M_f M_d} (hM_f_nn : 0 ≤ M_f) (hR : ∀ t ∈ Icc 0 1, ‖γ t‖ ≤ R) (hM_f hM_d) {w} (hw : R < ‖w‖) : ‖dixonH2 f γ w‖ ≤ M_f * M_d / (‖w‖ - R)`
- **What**: Norm bound for the Cauchy-type integral `dixonH2 f γ w = ∫₀¹ f(γ t)/(γ t - w)·γ'(t) dt`, controlled by `M_f·M_d/(‖w‖-R)` when `‖w‖>R≥sup‖γ‖`.
- **How**: Pointwise: `‖f(γt)/(γt-w)·γ'(t)‖ ≤ M_f/(‖w‖-R)·M_d` via `curve_dist_lower_bound` plus `div_le_div_of_nonneg_left`; integral bound via `intervalIntegral.norm_integral_le_of_norm_le_const`.
- **Hypotheses**: `0 ≤ M_f`, `‖γt‖≤R`, `‖f(γt)‖≤M_f`, `‖γ'(t)‖≤M_d`, `R<‖w‖`.
- **Uses from project**: `dixonH2` (from `DixonDiff`), `curve_dist_lower_bound`, `PiecewiseC1Path`.
- **Used by**: `dixonH2_tendsto_zero`.
- **Visibility**: public.
- **Lines**: 79–107.
- **Notes**: 28 lines.

### `theorem dixonH2_tendsto_zero`
- **Type**: `{f γ R M_f M_d} (hM_f_nn hR hM_f hM_d) : Tendsto (dixonH2 f γ) (cocompact ℂ) (nhds 0)`
- **What**: `dixonH2 f γ w → 0` as `‖w‖ → ∞` along `cocompact ℂ`.
- **How**: For each `ε>0`, restrict to `‖w‖ > max R (R + M_f·M_d/ε)`; then `dixonH2_norm_le` gives `≤ M_f·M_d/(‖w‖-R) < ε` via `div_lt_iff₀` and `linarith`.
- **Hypotheses**: same uniform bounds as `dixonH2_norm_le`.
- **Uses from project**: `dixonH2`, `dixonH2_norm_le`, `norm_gt_mem_cocompact`.
- **Used by**: `dixonFunction_tendsto_zero`.
- **Visibility**: public.
- **Lines**: 114–133.
- **Notes**: 19 lines.

### `theorem dixonFunction_tendsto_zero`
- **Type**: `{f U γ} (h_evt : ∀ᶠ w in cocompact ℂ, dixonFunction f U γ w = dixonH2 f γ w) (hM_f_nn hR hM_f hM_d) : Tendsto (dixonFunction f U γ) (cocompact ℂ) (nhds 0)`
- **What**: The Dixon function tends to 0 at infinity, given eventual agreement with `dixonH2`.
- **How**: `congr'` of `dixonH2_tendsto_zero` along the eventual-equality filter.
- **Hypotheses**: eventual equality + uniform curve/value/derivative bounds.
- **Uses from project**: `dixonFunction`, `dixonH2`, `dixonH2_tendsto_zero`.
- **Used by**: `dixonFunction_eq_zero_of_bounds`.
- **Visibility**: public.
- **Lines**: 143–153.
- **Notes**: none.

### `theorem dixonFunction_eq_zero`
- **Type**: `{f U γ} (h_entire : Differentiable ℂ (dixonFunction f U γ)) (h_tendsto : Tendsto ... cocompact (nhds 0)) : ∀ w, dixonFunction f U γ w = 0`
- **What**: Liouville: an entire function that vanishes at infinity is identically zero.
- **How**: Direct application of `Differentiable.apply_eq_of_tendsto_cocompact`.
- **Hypotheses**: `dixonFunction` is entire and tends to 0 along `cocompact ℂ`.
- **Uses from project**: `dixonFunction`.
- **Used by**: `dixonFunction_eq_zero_of_bounds`.
- **Visibility**: public.
- **Lines**: 161–166.
- **Notes**: none.

### `theorem dixonFunction_eq_zero_of_bounds`
- **Type**: `{f U γ} (h_entire) (h_evt) (hM_f_nn hR hM_f hM_d) : ∀ w, dixonFunction f U γ w = 0`
- **What**: Assembled Dixon-vanishing theorem: entire + eventual `=h2` + curve bounds ⟹ identically zero.
- **How**: Compose `dixonFunction_tendsto_zero` with `dixonFunction_eq_zero` (Liouville).
- **Hypotheses**: as above.
- **Uses from project**: `dixonFunction`, `dixonH2`, `dixonFunction_tendsto_zero`, `dixonFunction_eq_zero`.
- **Used by**: `dixonFunction_eq_zero_of_nullHomologous`.
- **Visibility**: public.
- **Lines**: 170–181.
- **Notes**: none.

### `theorem dixonFunction_eventually_eq_dixonH2`
- **Type**: `{f U} (γ : PwC1Immersion x x) (h_identity h_winding_evt) : ∀ᶠ w in cocompact ℂ, dixonFunction f U γ.toPiecewiseC1Path w = dixonH2 f γ.toPiecewiseC1Path w`
- **What**: Eventual equality of Dixon function with `dixonH2`: off-`U` it holds definitionally, in-`U` it follows from `h1 = h2 - 2πi·n·f` with `n=0`.
- **How**: `h_winding_evt.mono` then split on `w ∈ U`: in-`U` rewrite `h_identity` and `hwn:n=0` and `ring`; out-of-`U` is definitional.
- **Hypotheses**: identity `dixonH1 = dixonH2 - 2πi·n·f` off-curve and eventual `winding = 0` off-curve in cocompact.
- **Uses from project**: `dixonFunction`, `dixonH1`, `dixonH2`, `generalizedWindingNumber`, `PwC1Immersion`.
- **Used by**: `dixonFunction_eventually_eq_dixonH2_of_nullHomologous`, `dixonFunction_eq_zero_of_nullHomologous`.
- **Visibility**: public.
- **Lines**: 191–209.
- **Notes**: none.

### `theorem dixonFunction_eventually_eq_dixonH2_of_nullHomologous`
- **Type**: `{f U} (γ h_null hU_bounded h_identity) : ∀ᶠ w in cocompact ℂ, dixonFunction f U γ.toPiecewiseC1Path w = dixonH2 f γ.toPiecewiseC1Path w`
- **What**: B-4 bundle: discharge the eventual-winding hypothesis automatically using boundedness and null-homology.
- **How**: Invokes `dixonFunction_eventually_eq_dixonH2` with `h_null.winding_eventually_zero_cocompact_of_bounded hU_bounded`.
- **Hypotheses**: null-homologous γ in U, U bounded, integrability identity.
- **Uses from project**: `dixonFunction`, `dixonH1`, `dixonH2`, `generalizedWindingNumber`, `IsNullHomologous` and its `winding_eventually_zero_cocompact_of_bounded`, `PwC1Immersion`, `dixonFunction_eventually_eq_dixonH2`.
- **Used by**: unused in file (downstream callers only).
- **Visibility**: public.
- **Lines**: 218–230.
- **Notes**: none.

### `theorem cauchyIntegralFormula_nullHomologous`
- **Type**: `{f U γ} (h_zero : ∀ w, dixonFunction f U γ w = 0) (w) (hw : w ∈ U) (hoff h_cauchy_int h_base_int) : dixonH2 f γ w = 2*π*I·n(γ,w)·f(w)`
- **What**: Cauchy integral formula for null-homologous closed paths: `∮ f(z)/(z-w)·γ'(t)dt = 2πi·n(γ,w)·f(w)` for `w ∈ U` off curve.
- **How**: `dixonFunction_eq_dixonH1 hw` reduces `dixonFunction(w)=0` to `dixonH1(w)=0`; then `dixonH1_eq_dixonH2_sub_winding_f` gives `h2 = 2πi·n·f`.
- **Hypotheses**: Dixon-zero globally, integrability of `f∘γ/(γ-w)·γ'` and `1/(γ-w)·γ'`.
- **Uses from project**: `dixonFunction`, `dixonH2`, `dixonFunction_eq_dixonH1`, `dixonH1_eq_dixonH2_sub_winding_f`, `generalizedWindingNumber`.
- **Used by**: `cauchyIntegralFormula_contourIntegral`.
- **Visibility**: public.
- **Lines**: 244–259.
- **Notes**: none.

### `theorem cauchyIntegralFormula_nullHomologous_at`
- **Type**: `{f U γ w} (h_zero_at : dixonFunction f U γ w = 0) (hw hoff h_cauchy_int h_base_int) : dixonH2 f γ w = 2*π*I·n(γ,w)·f(w)`
- **What**: Pointwise variant of `cauchyIntegralFormula_nullHomologous`: needs Dixon-zero only at `w` (not globally).
- **How**: Same as `cauchyIntegralFormula_nullHomologous` but with a single-point `h_zero_at` hypothesis.
- **Hypotheses**: Dixon-zero at `w`, `w ∈ U`, off-curve, integrability.
- **Uses from project**: `dixonFunction`, `dixonH2`, `dixonFunction_eq_dixonH1`, `dixonH1_eq_dixonH2_sub_winding_f`, `generalizedWindingNumber`.
- **Used by**: `contourIntegral_eq_zero_of_nullHomologous_at`.
- **Visibility**: public.
- **Lines**: 264–277.
- **Notes**: none.

### `theorem dixonH1_eq_zero_of_dixonFunction_eq_zero`
- **Type**: `{f U γ} (h_zero) (w) (hw : w ∈ U) : dixonH1 f γ w = 0`
- **What**: When the Dixon function is identically zero and `w ∈ U`, `dixonH1 f γ w = 0`.
- **How**: `simp [← dixonFunction_eq_dixonH1 hw, h_zero w]`.
- **Hypotheses**: global Dixon-zero, `w ∈ U`.
- **Uses from project**: `dixonFunction`, `dixonH1`, `dixonFunction_eq_dixonH1`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 280–285.
- **Notes**: none.

### `theorem dixonH2_eq_zero_of_dixonFunction_eq_zero`
- **Type**: `{f U γ} (h_zero) (w) (hw : w ∉ U) : dixonH2 f γ w = 0`
- **What**: Off `U`, `dixonH2` matches `dixonFunction`, which is zero by hypothesis.
- **How**: `simp [← dixonFunction_eq_dixonH2 hw, h_zero w]`.
- **Hypotheses**: global Dixon-zero, `w ∉ U`.
- **Uses from project**: `dixonFunction`, `dixonH2`, `dixonFunction_eq_dixonH2`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 288–293.
- **Notes**: none.

### `theorem cauchyIntegralFormula_contourIntegral`
- **Type**: `{f U γ} (h_zero) (w) (hw hoff h_cauchy_int h_base_int) : ∫₀¹ f(γ t)/(γ t - w)·γ'(t)dt = 2*π*I·n(γ,w)·f(w)`
- **What**: Contour-integral statement of CIF for null-homologous curves.
- **How**: Direct application of `cauchyIntegralFormula_nullHomologous` (definitionally `dixonH2` is this integral).
- **Hypotheses**: global Dixon-zero, `w ∈ U`, off-curve, integrability.
- **Uses from project**: `dixonFunction`, `generalizedWindingNumber`, `cauchyIntegralFormula_nullHomologous`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 299–310.
- **Notes**: none.

### `theorem contourIntegral_eq_zero_of_nullHomologous_at`
- **Type**: `{f U γ} (w₀ hw₀_in_U hw₀_off) (h_zero_at : dixonFunction (fun z => (z-w₀)·f z) U γ w₀ = 0) (h_cauchy_int h_base_int) : γ.contourIntegral f = 0`
- **What**: Cauchy's theorem (∮f=0) pointwise version: apply CIF to `g(z)=(z-w₀)f(z)` which vanishes at `w₀`, yielding `∮ g/(z-w₀) = 0 = ∮ f`.
- **How**: Let `g(z)=(z-w₀)f(z)`. Apply `cauchyIntegralFormula_nullHomologous_at` with `g`; since `g(w₀)=0`, RHS is 0. Then `dixonH2 g γ w₀ = γ.contourIntegral f` via `intervalIntegral.integral_congr` and `field_simp` (cancel `(γ t - w₀)` factor since γ avoids `w₀`).
- **Hypotheses**: `w₀ ∈ U`, off-curve, pointwise Dixon-zero of twisted function at `w₀`, integrability.
- **Uses from project**: `dixonFunction`, `dixonH2`, `cauchyIntegralFormula_nullHomologous_at`, `PiecewiseC1Path.contourIntegral`.
- **Used by**: `contourIntegral_eq_zero_of_nullHomologous`.
- **Visibility**: public.
- **Lines**: 324–349.
- **Notes**: 25 lines.

### `theorem contourIntegral_eq_zero_of_nullHomologous`
- **Type**: `{f U γ} (w₀ hw₀_in_U hw₀_off) (h_zero : ∀ w, dixonFunction (fun z => (z-w₀)·f z) U γ w = 0) (h_cauchy_int h_base_int) : γ.contourIntegral f = 0`
- **What**: Global-Dixon-zero version of Cauchy's theorem for null-homologous curves.
- **How**: Delegates to `contourIntegral_eq_zero_of_nullHomologous_at` by specializing `h_zero` at `w₀`.
- **Hypotheses**: as above with global Dixon-zero.
- **Uses from project**: `dixonFunction`, `PiecewiseC1Path.contourIntegral`, `contourIntegral_eq_zero_of_nullHomologous_at`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 351–363.
- **Notes**: none.

### `theorem dixonFunction_eq_zero_of_nullHomologous`
- **Type**: `{f U} (hU hf γ h_null h1_diff h2_diff h_cauchy_int h_base_int h_winding_zero_near h_winding_evt) (hM_f_nn hR hM_f hM_d) : ∀ w, dixonFunction f U γ.toPiecewiseC1Path w = 0`
- **What**: B-5 aggregator: bundles all oracles to prove the Dixon function is identically zero for null-homologous γ.
- **How**: Constructs `h_id : ∀ w off-curve, dixonH1 = dixonH2 - 2πi·n·f` via `dixonH1_eq_dixonH2_sub_winding_f`; calls `dixonFunction_eq_zero_of_bounds` with `dixonFunction_differentiable` (entireness) and `dixonFunction_eventually_eq_dixonH2 γ h_id h_winding_evt`.
- **Hypotheses**: hU open, hf differentiable on U, γ null-hom, h1/h2 differentiability oracles, integrability identity, local off-U winding-zero, eventual winding-zero in cocompact, uniform bounds.
- **Uses from project**: `dixonFunction`, `dixonH1`, `dixonH2`, `dixonH1_eq_dixonH2_sub_winding_f`, `dixonFunction_eq_zero_of_bounds`, `dixonFunction_differentiable`, `dixonFunction_eventually_eq_dixonH2`, `IsNullHomologous`, `PwC1Immersion`, `generalizedWindingNumber`.
- **Used by**: `dixonFunction_eq_zero_of_nullHomologous_bounded`, `dixonFunction_eq_zero_of_nullHomologous_unbounded`.
- **Visibility**: public.
- **Lines**: 381–418.
- **Notes**: many-hypothesis API.

### `theorem dixonFunction_eq_zero_of_nullHomologous_bounded`
- **Type**: same shape as above + `hU_bounded` and drops `h_winding_evt`.
- **What**: B-5 specialized to bounded `U`: cocompact winding-zero is auto-discharged.
- **How**: Forwards to `dixonFunction_eq_zero_of_nullHomologous` with `h_null.winding_eventually_zero_cocompact_of_bounded hU_bounded`.
- **Hypotheses**: as before plus `hU_bounded`.
- **Uses from project**: `dixonFunction_eq_zero_of_nullHomologous`, `IsNullHomologous`, `PwC1Immersion`.
- **Used by**: `dixonFunction_eq_zero_of_nullHomologous_autoH2`.
- **Visibility**: public.
- **Lines**: 423–450.
- **Notes**: none.

### `theorem dixonFunction_eq_zero_of_nullHomologous_unbounded`
- **Type**: B-5 with `hLip : LipschitzWith K γ` replacing `hU_bounded`, drops `h_winding_evt`.
- **What**: Same conclusion as `_bounded` but for unbounded U with Lipschitz γ; cocompact winding-zero from γ Lipschitz.
- **How**: Forwards to `dixonFunction_eq_zero_of_nullHomologous` with `winding_eventually_zero_cocompact_of_lipschitz hLip`.
- **Hypotheses**: γ Lipschitz, otherwise as before.
- **Uses from project**: `dixonFunction_eq_zero_of_nullHomologous`, `winding_eventually_zero_cocompact_of_lipschitz`, `PwC1Immersion`, `IsNullHomologous`.
- **Used by**: `dixonFunction_eq_zero_of_nullHomologous_autoH2_unbounded`.
- **Visibility**: public.
- **Lines**: 463–491.
- **Notes**: none.

### `theorem dixonFunction_eq_zero_of_nullHomologous_autoH2`
- **Type**: B-5 bounded variant that auto-discharges `h2_diff` via `dixonH2_differentiableAt_of_regular`.
- **What**: Closes one oracle (B-3) when f is continuous on the curve image (via Lipschitz γ).
- **How**: Construct `h2_diff` from `dixonH2_differentiableAt_of_regular hoff hf_cont hLip`; forward to `dixonFunction_eq_zero_of_nullHomologous_bounded`.
- **Hypotheses**: bounded U + γ Lipschitz + remaining oracles.
- **Uses from project**: `dixonFunction`, `dixonH2_differentiableAt_of_regular`, `dixonFunction_eq_zero_of_nullHomologous_bounded`, `PwC1Immersion`, `IsNullHomologous`.
- **Used by**: `dixonFunction_eq_zero_of_nullHomologous_autoBounds`.
- **Visibility**: public.
- **Lines**: 496–528.
- **Notes**: 32 lines (signature heavy; body short).

### `theorem dixonFunction_eq_zero_of_nullHomologous_autoBounds`
- **Type**: B-5 bounded variant that further auto-discharges the uniform `‖γ‖`, `‖f∘γ‖`, `‖γ'‖`, and integrability bounds, leaving only `h1_diff` + `h_winding_zero_near`.
- **What**: Reduces the public surface to the two deep oracles (B-2 and the local off-U winding-zero).
- **How**: Compactness of `Icc 0 1` + continuity of `γ`, `f∘γ` give `R`, `M_f`; Lipschitz gives `‖γ'‖ ≤ K`; cauchy/base integrabilities via continuity + Lipschitz + `Integrable.of_bound`. Then `dixonFunction_eq_zero_of_nullHomologous_autoH2`.
- **Hypotheses**: hU bounded open, hf differentiable on U, γ null-hom Lipschitz, h1_diff, h_winding_zero_near.
- **Uses from project**: `dixonFunction`, `dixonFunction_eq_zero_of_nullHomologous_autoH2`, `norm_deriv_le_of_lipschitz`, `PwC1Immersion`, `IsNullHomologous`, `generalizedWindingNumber`.
- **Used by**: `dixonFunction_eq_zero_of_nullHomologous_autoH1`, `dixonFunction_eq_zero_of_nullHomologous_convex`, `dixonFunction_eq_zero_of_nullHomologous_convex_full`, `dixonFunction_eq_zero_of_nullHomologous_open_full`.
- **Visibility**: public.
- **Lines**: 536–638.
- **Notes**: 102 lines (key lemma: `Integrable.of_bound` + compactness of curve image).

### `theorem dixonFunction_eq_zero_of_nullHomologous_autoH1`
- **Type**: B-5 variant discharging `h1_diff` via B-2 `dixonH1_differentiableOn_of_regular`.
- **What**: Reduces further; only `h_F'_meas`, `h_dslope_deriv_bound`, and `h_winding_zero_near` remain.
- **How**: Forward to `dixonFunction_eq_zero_of_nullHomologous_autoBounds` with `dixonH1_differentiableOn_of_regular hU hf γ h_null.image_subset hLip h_F'_meas h_dslope_deriv_bound`.
- **Hypotheses**: as above; `h_F'_meas` and `h_dslope_deriv_bound` provide the second-order structure of `dslope`.
- **Uses from project**: `dixonFunction`, `dixonH1_differentiableOn_of_regular`, `dslope`, `dixonFunction_eq_zero_of_nullHomologous_autoBounds`, `PwC1Immersion`, `IsNullHomologous`, `generalizedWindingNumber`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 645–664.
- **Notes**: none.

### `theorem dixonFunction_eq_zero_of_nullHomologous_convex`
- **Type**: Variant for convex bounded `U`; auto-discharges `h_dslope_deriv_bound` via D-1c.
- **What**: For convex bounded `U`, only `h_F'_meas` and `h_winding_zero_near` remain.
- **How**: Calls `dixonFunction_eq_zero_of_nullHomologous_autoBounds` with `dixonH1_differentiableOn_of_regular_convex hU_convex hU hf γ h_null.image_subset hLip h_F'_meas`.
- **Hypotheses**: hU_convex, hU, hU_bounded, hf, γ Lipschitz null-hom, h_F'_meas, h_winding_zero_near.
- **Uses from project**: `dixonFunction`, `dixonH1_differentiableOn_of_regular_convex`, `dslope`, `dixonFunction_eq_zero_of_nullHomologous_autoBounds`, `PwC1Immersion`, `IsNullHomologous`, `generalizedWindingNumber`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 670–687.
- **Notes**: none.

### `theorem dixonFunction_eq_zero_of_nullHomologous_convex_full`
- **Type**: B-5 fully auto for convex bounded `U`: only `h_winding_zero_near` remains.
- **What**: All B-2 sub-oracles (D-1a/b/c/d) plus B-3, B-4 are discharged automatically.
- **How**: Uses `dixonH1_differentiableOn_of_regular_convex_full`.
- **Hypotheses**: hU_convex, hU, hU_bounded, hf, γ Lipschitz null-hom, h_winding_zero_near.
- **Uses from project**: `dixonFunction`, `dixonH1_differentiableOn_of_regular_convex_full`, `dixonFunction_eq_zero_of_nullHomologous_autoBounds`, `PwC1Immersion`, `IsNullHomologous`, `generalizedWindingNumber`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 697–710.
- **Notes**: none.

### `theorem dixonFunction_eq_zero_of_nullHomologous_open_full`
- **Type**: B-5 fully closed for general open bounded `U` (no convexity).
- **What**: Same as `_convex_full` but works for any open bounded U.
- **How**: Uses `dixonH1_differentiableOn_of_regular_open_full`.
- **Hypotheses**: hU, hU_bounded, hf, γ Lipschitz null-hom, h_winding_zero_near.
- **Uses from project**: `dixonFunction`, `dixonH1_differentiableOn_of_regular_open_full`, `dixonFunction_eq_zero_of_nullHomologous_autoBounds`, `PwC1Immersion`, `IsNullHomologous`, `generalizedWindingNumber`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 715–728.
- **Notes**: none.

### `theorem dixonFunction_eq_zero_of_nullHomologous_autoH2_unbounded`
- **Type**: B-5 autoH2 for unbounded U with Lipschitz γ.
- **What**: Unbounded analog of `_autoH2`.
- **How**: Constructs `h2_diff` via `dixonH2_differentiableAt_of_regular`; forwards to `dixonFunction_eq_zero_of_nullHomologous_unbounded`.
- **Hypotheses**: hU open, hf differentiable on U, γ Lipschitz null-hom, h1_diff, integrabilities, h_winding_zero_near, uniform bounds.
- **Uses from project**: `dixonFunction`, `dixonH2_differentiableAt_of_regular`, `dixonFunction_eq_zero_of_nullHomologous_unbounded`, `PwC1Immersion`, `IsNullHomologous`.
- **Used by**: `dixonFunction_eq_zero_of_nullHomologous_autoBounds_unbounded`.
- **Visibility**: public.
- **Lines**: 733–765.
- **Notes**: none.

### `theorem dixonFunction_eq_zero_of_nullHomologous_autoBounds_unbounded`
- **Type**: B-5 autoBounds for unbounded `U` (no bound). Body packages the same uniform-bound machinery as `_autoBounds` (bounded case).
- **What**: Auto-discharges all uniform bounds and integrabilities for the unbounded chain; only `h1_diff` and `h_winding_zero_near` remain.
- **How**: Same compactness + Lipschitz + `Integrable.of_bound` strategy as bounded autoBounds; then `dixonFunction_eq_zero_of_nullHomologous_autoH2_unbounded`.
- **Hypotheses**: hU open, hf, γ Lipschitz null-hom, h1_diff, h_winding_zero_near.
- **Uses from project**: `dixonFunction`, `dixonFunction_eq_zero_of_nullHomologous_autoH2_unbounded`, `norm_deriv_le_of_lipschitz`, `PwC1Immersion`, `IsNullHomologous`, `generalizedWindingNumber`.
- **Used by**: `dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded`.
- **Visibility**: public.
- **Lines**: 768–870.
- **Notes**: 102 lines (mirrors `_autoBounds`).

### `theorem dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded`
- **Type**: B-5 fully closed for unbounded open `U` with Lipschitz γ.
- **What**: Unbounded analog of `_open_full`: only `h_winding_zero_near` (B-1 full) remains.
- **How**: Uses `dixonH1_differentiableOn_of_regular_open_full`; forwards to `dixonFunction_eq_zero_of_nullHomologous_autoBounds_unbounded`.
- **Hypotheses**: hU open, hf, γ Lipschitz null-hom, h_winding_zero_near.
- **Uses from project**: `dixonFunction`, `dixonH1_differentiableOn_of_regular_open_full`, `dixonFunction_eq_zero_of_nullHomologous_autoBounds_unbounded`, `PwC1Immersion`, `IsNullHomologous`, `generalizedWindingNumber`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 874–886.
- **Notes**: none.

## File Summary

- **Total declarations**: 22 (2 private lemmas + 20 public theorems).
- **Key API**: `dixonH2_norm_le`, `dixonH2_tendsto_zero`, `dixonFunction_eq_zero`, `cauchyIntegralFormula_nullHomologous`, `cauchyIntegralFormula_contourIntegral`, `contourIntegral_eq_zero_of_nullHomologous`, and the family `dixonFunction_eq_zero_of_nullHomologous_{,bounded,unbounded,autoH2,autoBounds,autoH1,convex,convex_full,open_full,autoH2_unbounded,autoBounds_unbounded,open_full_unbounded}`. The progressive auto-discharge ladder is the centerpiece (B-5 → B-5 convex full → B-5 open full).
- **Unused in file**: 8 theorems exported only — `dixonFunction_eventually_eq_dixonH2_of_nullHomologous`, `dixonH1_eq_zero_of_dixonFunction_eq_zero`, `dixonH2_eq_zero_of_dixonFunction_eq_zero`, `cauchyIntegralFormula_contourIntegral`, `contourIntegral_eq_zero_of_nullHomologous`, `dixonFunction_eq_zero_of_nullHomologous_autoH1`, `dixonFunction_eq_zero_of_nullHomologous_convex`, `dixonFunction_eq_zero_of_nullHomologous_convex_full`, `dixonFunction_eq_zero_of_nullHomologous_open_full`, `dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded`.
- **Sorries**: 0.
- **set_options**: none.
- **Long proofs (>30 lines)**: `dixonFunction_eq_zero_of_nullHomologous_autoH2` (32 lines), `dixonFunction_eq_zero_of_nullHomologous_autoBounds` (~102 lines), `dixonFunction_eq_zero_of_nullHomologous_autoBounds_unbounded` (~102 lines).
- **Purpose**: Proves the Dixon theorem in Lean 4 — the Dixon function is identically zero for null-homologous curves — and deduces the Cauchy integral formula and Cauchy's theorem (∮f=0) as corollaries. The file packages many specialization variants (bounded vs unbounded U, convex vs general U, Lipschitz γ vs uniform bounds) so downstream users only need to discharge a minimal set of oracles (typically just `h_winding_zero_near` for the convex/open-full versions). The proof strategy: entireness of the Dixon function + decay at infinity via the Cauchy-type integral bound → identically zero via Liouville. From this CIF and Cauchy's theorem follow by classical tricks (twisting by `(z-w₀)·f(z)`).
