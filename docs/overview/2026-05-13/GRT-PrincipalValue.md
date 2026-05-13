# PrincipalValue.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/PrincipalValue.lean`
Lines: 329

## Imports
- `LeanModularForms.ForMathlib.ClassicalCPV`

---

### `theorem cauchyPrincipalValueIntegrand_bounded`
- **Type**: `(f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (ε : ℝ) (_hε : 0 < ε) (hf_cont : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε)) (hγ_cont : ContinuousOn γ (Icc a b)) (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) → ∃ M : ℝ, ∀ t ∈ Icc a b, ‖cauchyPrincipalValueIntegrand' f γ z₀ ε t‖ ≤ M`
- **What**: The PV cutoff integrand `f(γ t)·γ'(t)·𝟙[ε < ‖γ t - z₀‖]` is uniformly bounded on `[a,b]` by `Mf·Mγ + 1`.
- **How**: Case-split on whether `γ '' Icc a b \ Metric.ball z₀ ε` is nonempty. If so, take compact bounds `Mf` on `f.norm` (via `IsCompact.exists_bound_of_continuousOn`) and `Mγ` on `‖γ'‖`; bound by `Mf * Mγ + 1`. If empty, the cutoff is uniformly zero (the absurd branch leads to contradiction).
- **Hypotheses**: `f` continuous off `Metric.ball z₀ ε`, `γ` and `γ'` continuous on `[a,b]`.
- **Uses from project**: `cauchyPrincipalValueIntegrand'` (from `ClassicalCPV`).
- **Used by**: `cauchyPrincipalValueIntegrand_integrable`.
- **Visibility**: public
- **Lines**: 20-54
- **Notes**: >10 lines; key lemma `IsCompact.exists_bound_of_continuousOn`.

### `lemma measurableSet_pv_support`
- **Type**: `(γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (ε : ℝ) (hγ_cont : ContinuousOn γ (Icc a b)) → MeasurableSet ({t | ε < ‖γ t - z₀‖} ∩ Icc a b)`
- **What**: The PV cutoff support `{t : ε < ‖γ t - z₀‖} ∩ [a,b]` is measurable.
- **How**: `(γ - z₀).norm` is continuous, so its preimage of `Ioi ε` is open on the subtype `Icc a b`; pull back via `isOpen_induced_iff` to a global open `U` and rewrite the intersection.
- **Hypotheses**: `γ` continuous on `Icc a b`.
- **Uses from project**: none.
- **Used by**: `aEStronglyMeasurable_pv_integrand`, `pv_piecewise_measurable`.
- **Visibility**: public
- **Lines**: 56-74
- **Notes**: >10 lines.

### `lemma continuousOn_pv_base`
- **Type**: `(f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (ε : ℝ) (hf_cont ...) (hγ_cont ...) (hγ'_cont ...) → ContinuousOn (fun t => f (γ t) * deriv γ t) ({t | ε < ‖γ t - z₀‖} ∩ Icc a b)`
- **What**: The base integrand `t ↦ f(γ t)·γ'(t)` is continuous on the PV support intersected with `[a,b]`.
- **How**: Composes `hf_cont` along `γ` (using `MapsTo` into `γ '' Icc a b \ Metric.ball z₀ ε`) for `f∘γ`, then multiplies by `γ'`.
- **Hypotheses**: `f` continuous off the open ball, `γ`, `γ'` continuous on `Icc`.
- **Uses from project**: none.
- **Used by**: `aEStronglyMeasurable_pv_integrand`.
- **Visibility**: public
- **Lines**: 76-92
- **Notes**: >10 lines.

### `private theorem aEStronglyMeasurable_pv_integrand`
- **Type**: `{f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {ε : ℝ} (hf ...) (hγ ...) (hγ' ...) → AEStronglyMeasurable (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0) (volume.restrict (Icc a b))`
- **What**: The indicator-shaped PV integrand is `AEStronglyMeasurable` on `volume.restrict (Icc a b)`.
- **How**: Builds AEStronglyMeasurable on the support `S ∩ [a,b]` from `continuousOn_pv_base`, then uses `AEStronglyMeasurable.piecewise` with constant `0` on the complement and an a.e. equality `filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet]`.
- **Hypotheses**: same as `continuousOn_pv_base`.
- **Uses from project**: `measurableSet_pv_support`, `continuousOn_pv_base`.
- **Used by**: `cauchyPrincipalValueIntegrand_integrable`, `cauchyPrincipalValueExists_of_continuous`.
- **Visibility**: private
- **Lines**: 94-118
- **Notes**: >10 lines; uses `Measure.restrict_le_self`.

### `theorem cauchyPrincipalValueIntegrand_integrable`
- **Type**: `(f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (ε : ℝ) (hε : 0 < ε) (hab : a < b) (hf_cont ...) (hγ_cont ...) (hγ'_cont ...) → IntervalIntegrable (cauchyPrincipalValueIntegrand' f γ z₀ ε) volume a b`
- **What**: For each fixed `ε > 0`, the PV cutoff integrand is interval-integrable on `[a,b]`.
- **How**: Use the bound `M` from `cauchyPrincipalValueIntegrand_bounded`, rewrite `cauchyPrincipalValueIntegrand'` as an `if`, apply `intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le`, then `IntegrableOn.of_bound` with bound `max M 0` and AE measurability from `aEStronglyMeasurable_pv_integrand`.
- **Hypotheses**: `0 < ε`, `a < b`, continuity hypotheses.
- **Uses from project**: `cauchyPrincipalValueIntegrand_bounded`, `aEStronglyMeasurable_pv_integrand`, `cauchyPrincipalValueIntegrand'`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 120-139
- **Notes**: >10 lines.

### `theorem cauchyPrincipalValue_of_dominated`
- **Type**: `(f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b) (M : ℝ) (_hM : 0 < M) (h_bound : ∀ ε > 0, ∀ t ∈ Icc a b, ‖cauchyPrincipalValueIntegrand' f γ z₀ ε t‖ ≤ M) (h_ae_limit : ∀ᵐ t ∂volume.restrict (Icc a b), ∃ L, Tendsto (fun ε => cauchyPrincipalValueIntegrand' f γ z₀ ε t) (𝓝[>] 0) (𝓝 L)) (hF_meas : ∀ᶠ ε in 𝓝[>] 0, AEStronglyMeasurable ...) → CauchyPrincipalValueExists' f γ a b z₀`
- **What**: Dominated convergence for PV: under a uniform pointwise bound `M`, a.e. existence of pointwise limits, and eventual AE strong measurability, the PV limit exists.
- **How**: Casts hypotheses to `uIoc` form, picks the a.e. limit function `g t := limUnder (𝓝[>] 0) (...)`, shows `Tendsto ... (𝓝 (g t))` a.e., then invokes `intervalIntegral.tendsto_integral_filter_of_dominated_convergence` with constant dominator `M`.
- **Hypotheses**: `a < b`, uniform bound, a.e. pointwise convergence, eventual measurability.
- **Uses from project**: `cauchyPrincipalValueIntegrand'`, `CauchyPrincipalValueExists'`.
- **Used by**: `cauchyPrincipalValueExists_of_continuous`.
- **Visibility**: public
- **Lines**: 142-171
- **Notes**: >10 lines; key lemma `intervalIntegral.tendsto_integral_filter_of_dominated_convergence`.

### `private theorem pv_uniform_bound_of_continuous_aux`
- **Type**: `(g : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b) (hg ...) (hγ ...) (hγ' ...) → ∃ M > 0, ∀ ε > 0, ∀ t ∈ Icc a b, ‖cauchyPrincipalValueIntegrand' g γ z₀ ε t‖ ≤ M`
- **What**: For continuous `g` on the image of `γ`, the PV cutoff integrand is uniformly bounded by a constant `Mg·Mγ' + 1`.
- **How**: Compact bounds `Mg` on `g.norm` and `Mγ'` on `‖γ'‖` from `IsCompact.exists_bound_of_continuousOn`; uniform bound from `mul_le_mul`.
- **Hypotheses**: `a < b`, continuity hypotheses.
- **Uses from project**: `cauchyPrincipalValueIntegrand'`.
- **Used by**: `cauchyPrincipalValueExists_of_continuous`.
- **Visibility**: private
- **Lines**: 173-196
- **Notes**: >10 lines.

### `theorem cauchyPrincipalValueExists_of_continuous`
- **Type**: `(g : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b) (hg : ContinuousOn g (γ '' Icc a b)) (hγ : ContinuousOn γ (Icc a b)) (hγ' : ContinuousOn (deriv γ) (Icc a b)) → CauchyPrincipalValueExists' g γ a b z₀`
- **What**: When `g` is continuous on the entire image (no singularity), the PV exists trivially.
- **How**: Invokes `cauchyPrincipalValue_of_dominated` with the bound from `pv_uniform_bound_of_continuous_aux`. Splits the pointwise limit on `γ t = z₀` (limit is `0`) vs `γ t ≠ z₀` (cutoff is eventually 1 in `𝓝[>] 0`; limit is `g(γ t)·γ'(t)`). Provides AE measurability via `aEStronglyMeasurable_pv_integrand` with `hg.mono diff_subset`.
- **Hypotheses**: `a < b`, continuity of `g`, `γ`, `γ'`.
- **Uses from project**: `cauchyPrincipalValue_of_dominated`, `pv_uniform_bound_of_continuous_aux`, `aEStronglyMeasurable_pv_integrand`, `cauchyPrincipalValueIntegrand'`, `CauchyPrincipalValueExists'`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 199-222
- **Notes**: >10 lines.

### `theorem cauchyPrincipalValueExists_of_singular_inv`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (h_crossing_cauchy : (∃ t ∈ Icc γ.a γ.b, γ.toFun t = z₀) → Cauchy (Filter.map (fun ε => ∫ t in γ.a..γ.b, if ε < ‖γ.toFun t - z₀‖ then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0) (𝓝[>] 0))) → CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun γ.a γ.b z₀`
- **What**: PV exists for the singular `1/(z - z₀)` integrand on a piecewise-C1 immersion, given Cauchy-criterion for crossing case (and trivially otherwise).
- **How**: Case-split on whether `γ` crosses `z₀`. If yes, conclude via `CompleteSpace.complete (h_crossing_cauchy ...)`. If no, take `t₀` minimizing `‖γ t - z₀‖` on the compact `Icc γ.a γ.b` (`IsCompact.exists_isMinOn`), set `δ = ‖γ t₀ - z₀‖ > 0`; then for small `ε ∈ Ioo 0 δ` the cutoff is identically `1` on `Icc γ.a γ.b`, so the cutoff integral is constant and the limit equals the full integral.
- **Hypotheses**: crossing Cauchy criterion if `γ` hits `z₀`.
- **Uses from project**: `PiecewiseC1Immersion`, `PiecewiseC1Immersion.toFun`, `PiecewiseC1Immersion.continuous_toFun`, `PiecewiseC1Immersion.hab`, `CauchyPrincipalValueExists'`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 225-248
- **Notes**: >10 lines; uses `push Not at h_cross`.

### `theorem uniform_avoidance_on_compact`
- **Type**: `(γ : ℝ → ℂ) (K : Set ℝ) (z₀ : ℂ) (hK_compact : IsCompact K) (hK_nonempty : K.Nonempty) (hγ_cont : ContinuousOn γ K) (h_avoid : ∀ t ∈ K, γ t ≠ z₀) → ∃ δ > 0, ∀ t ∈ K, δ ≤ ‖γ t - z₀‖`
- **What**: If `γ` is continuous on compact `K` and avoids `z₀`, there's a uniform positive lower bound on `‖γ t - z₀‖`.
- **How**: `IsCompact.exists_isMinOn` on `(γ - z₀).norm`, the minimum is positive by `h_avoid`, the bound from `eventually_principal`.
- **Hypotheses**: compactness, nonemptiness, continuity, pointwise avoidance.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 251-257
- **Notes**: none.

### `private theorem pv_piecewise_measurable`
- **Type**: `(g : ℂ → ℂ) (γ : PiecewiseC1Curve) (z₀ : ℂ) (h_integrable : IntervalIntegrable (fun t => g (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b) → ∀ᶠ ε in 𝓝[>] 0, AEStronglyMeasurable (fun t => if ε < ‖γ.toFun t - z₀‖ then g (γ.toFun t) * deriv γ.toFun t else 0) (volume.restrict (Ι γ.a γ.b))`
- **What**: For each small `ε > 0`, the indicator-shaped integrand on a piecewise-C1 curve is `AEStronglyMeasurable`.
- **How**: From integrability get base AE measurability; apply `AEStronglyMeasurable.indicator` with `measurableSet_pv_support`; transfer via `congr` and `ae_restrict_mem measurableSet_Ioc`.
- **Hypotheses**: integrability of the base integrand.
- **Uses from project**: `PiecewiseC1Curve`, `PiecewiseC1Curve.toFun`, `PiecewiseC1Curve.continuous_toFun`, `PiecewiseC1Curve.hab`, `measurableSet_pv_support`.
- **Used by**: unused in file.
- **Visibility**: private
- **Lines**: 259-273
- **Notes**: >10 lines.

### `private theorem pv_piecewise_bound`
- **Type**: `(γ : PiecewiseC1Curve) (z₀ : ℂ) (g : ℂ → ℂ) → ∀ᶠ ε in 𝓝[>] 0, ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b → ‖(if ε < ‖γ.toFun t - z₀‖ then g (γ.toFun t) * deriv γ.toFun t else 0)‖ ≤ ‖g (γ.toFun t) * deriv γ.toFun t‖`
- **What**: The indicator-cut integrand is pointwise bounded by the uncut integrand (cutoff kills, leaves zero on `else` branch).
- **How**: `filter_upwards [self_mem_nhdsWithin]`, then `split_ifs` (one case `le_refl`, the other `‖0‖ = 0 ≤ ‖_‖`).
- **Hypotheses**: none.
- **Uses from project**: `PiecewiseC1Curve`, `PiecewiseC1Curve.toFun`, `PiecewiseC1Curve.a`, `PiecewiseC1Curve.b`.
- **Used by**: unused in file.
- **Visibility**: private
- **Lines**: 275-284
- **Notes**: none.

### `private theorem pv_piecewise_pointwise`
- **Type**: `(γ : PiecewiseC1Curve) (z₀ : ℂ) (g : ℂ → ℂ) (h_finite_preimage : Set.Finite {t ∈ Icc γ.a γ.b | γ.toFun t = z₀}) → ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b → Tendsto (fun ε => if ε < ‖γ.toFun t - z₀‖ then g (γ.toFun t) * deriv γ.toFun t else 0) (𝓝[>] 0) (𝓝 (g (γ.toFun t) * deriv γ.toFun t))`
- **What**: A.e., the cutoff integrand pointwise converges to the uncut integrand as `ε → 0⁺` (since the cutoff fails only on a finite set).
- **How**: `filter_upwards [h_finite_preimage.countable.ae_notMem _]` to exclude `γ t = z₀`; then for `ε ∈ Ioo 0 ‖γ t - z₀‖`, the cutoff is `true`, so the value equals `g(γ t)·γ'(t)`.
- **Hypotheses**: finite preimage of `z₀` under `γ`.
- **Uses from project**: `PiecewiseC1Curve`, `PiecewiseC1Curve.toFun`, `PiecewiseC1Curve.a`, `PiecewiseC1Curve.b`, `PiecewiseC1Curve.hab`.
- **Used by**: unused in file.
- **Visibility**: private
- **Lines**: 286-297
- **Notes**: none.

### `private theorem pv_simple_pole_integrand_split`
- **Type**: `(γ_fun : ℝ → ℂ) (z₀ c : ℂ) (g : ℂ → ℂ) (ε : ℝ) (t : ℝ) → (if ε < ‖γ_fun t - z₀‖ then (c / (γ_fun t - z₀) + g (γ_fun t)) * deriv γ_fun t else 0) = (if ε < ‖γ_fun t - z₀‖ then c / (γ_fun t - z₀) * deriv γ_fun t else 0) + (if ε < ‖γ_fun t - z₀‖ then g (γ_fun t) * deriv γ_fun t else 0)`
- **What**: Pointwise additive split: the cutoff integrand for a simple-pole + regular sum splits into two cutoff integrands.
- **How**: `split_ifs <;> ring`.
- **Hypotheses**: none.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: private
- **Lines**: 299-304
- **Notes**: none.

### `private theorem pv_simple_pole_tendsto`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ c : ℂ) (g : ℂ → ℂ) (Ls Lg : ℂ) (hLs : Tendsto (fun ε => ∫_a^b 𝟙·c/(γ-z₀)·γ') (𝓝[>] 0) (𝓝 Ls)) (hLg : Tendsto (fun ε => ∫_a^b 𝟙·g(γ)·γ') (𝓝[>] 0) (𝓝 Lg)) (h_int : ∀ ε > 0, IntervalIntegrable (...) ... ∧ IntervalIntegrable (...) ...) → Tendsto (fun ε => ∫_a^b (𝟙·c/(γ-z₀)·γ' + 𝟙·g(γ)·γ')) (𝓝[>] 0) (𝓝 (Ls + Lg))`
- **What**: Sum of PV limits: if `Ls` and `Lg` are PV limits of the singular and regular parts and both are interval-integrable, the sum-cutoff integral tends to `Ls + Lg`.
- **How**: `Tendsto.congr'` on `Tendsto.add hLs hLg`; `filter_upwards [self_mem_nhdsWithin]` and apply `intervalIntegral.integral_add` to combine the two integrals.
- **Hypotheses**: individual PV limits and per-ε integrability of both pieces.
- **Uses from project**: `PiecewiseC1Immersion`, `PiecewiseC1Immersion.toFun`, `PiecewiseC1Immersion.a`, `PiecewiseC1Immersion.b`.
- **Used by**: unused in file.
- **Visibility**: private
- **Lines**: 306-327
- **Notes**: >10 lines; key lemma `intervalIntegral.integral_add`.

---

## File Summary
`PrincipalValue.lean` (329 lines, 0 sorries, 0 axioms) develops Cauchy-principal-value theory for piecewise-C1 contour integrals, building on `cauchyPrincipalValueIntegrand'` and `CauchyPrincipalValueExists'` from `ClassicalCPV`. Public results include: uniform boundedness (`cauchyPrincipalValueIntegrand_bounded`), measurability of the PV support (`measurableSet_pv_support`), interval-integrability of each cutoff (`cauchyPrincipalValueIntegrand_integrable`), a dominated-convergence theorem for PVs (`cauchyPrincipalValue_of_dominated`), and existence for continuous integrands (`cauchyPrincipalValueExists_of_continuous`) and for the singular `1/(z-z₀)` case on immersions (`cauchyPrincipalValueExists_of_singular_inv`). A utility `uniform_avoidance_on_compact` provides a uniform separation bound. Five private helpers (`pv_piecewise_measurable/_bound/_pointwise/_integrand_split/_tendsto`) plus `aEStronglyMeasurable_pv_integrand` and `pv_uniform_bound_of_continuous_aux` round out the file. Many private helpers appear unused in the file (they're API for downstream callers).
