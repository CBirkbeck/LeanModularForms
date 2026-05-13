# Inventory: `SectorCurveLemma.lean`

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean` (924 lines)

### `theorem sectorCurve_differentiableAt_off_knots`
- **Type**: `(r : ℝ) (α : ℝ) (t : ℝ) (_ht : t ∈ Ioo (0 : ℝ) 3) (ht_not : t ∉ ({1, 2} : Set ℝ)) : DifferentiableAt ℝ (sectorCurve r α) t`
- **What**: The sector curve `γ(t)` (three-piece: radial-out, arc, radial-in) is differentiable at any `t ∈ (0, 3)` not equal to the knot points 1 or 2.
- **How**: Case-split into `t < 1`, `1 < t < 2`, `2 < t` using `lt_or_gt_of_ne`. On each open sub-interval, `sectorCurve` agrees with an explicit smooth formula (`sectorCurve_seg1/2/3` rewrites), and we apply `DifferentiableAt.const_mul`, `cexp`, `ofReal_comp` chains.
- **Hypotheses**: `t ∈ (0,3) \ {1,2}`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg2`
- **Used by**: `pv_sector_higher_power`, `integral_analytic_sectorCurve_eq_zero`, `zpow_primitive_hasDerivAt`
- **Visibility**: private
- **Lines**: 30-60
- **Notes**: >10 lines (31)

### `theorem pow_integrableOn_01`
- **Type**: `(r α : ℝ) (n : ℕ) : IntervalIntegrable (fun t => (sectorCurve r α t) ^ (n - 1) * deriv (sectorCurve r α) t) volume 0 1`
- **What**: The integrand `γ(t)^(n-1) · γ'(t)` is interval-integrable on the radial-out segment `[0,1]`.
- **How**: Continuous polynomial-times-constant on `Icc` upgraded via `intervalIntegrable`, then `.congr_ae` using `sectorCurve_seg1` + `deriv_sectorCurve_seg1`.
- **Hypotheses**: none.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg1`, `deriv_sectorCurve_seg1`
- **Used by**: `pv_sector_higher_power`
- **Visibility**: private
- **Lines**: 62-72
- **Notes**: >10 lines (11)

### `theorem pow_integrableOn_12`
- **Type**: `(r α : ℝ) (n : ℕ) : IntervalIntegrable (fun t => (sectorCurve r α t) ^ (n - 1) * deriv (sectorCurve r α) t) volume 1 2`
- **What**: Integrability on the arc segment `[1,2]`.
- **How**: Continuous-on `Icc 1 2` of `(r·exp(I(t-1)α))^(n-1) · r·(Iα)·exp(...)`; `.congr_ae` via `sectorCurve_seg2` + `deriv_sectorCurve_seg2`.
- **Hypotheses**: none.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg2`, `deriv_sectorCurve_seg2`
- **Used by**: `pv_sector_higher_power`
- **Visibility**: private
- **Lines**: 74-85
- **Notes**: >10 lines (12)

### `theorem pow_integrableOn_23`
- **Type**: `(r α : ℝ) (n : ℕ) : IntervalIntegrable (fun t => (sectorCurve r α t) ^ (n - 1) * deriv (sectorCurve r α) t) volume 2 3`
- **What**: Integrability on the radial-in segment `[2,3]`.
- **How**: Continuous-on of `((3-t)·r·exp(Iα))^(n-1) · (-r·exp(Iα))`; `.congr_ae` via `sectorCurve_seg3` + `deriv_sectorCurve_seg3`.
- **Hypotheses**: none.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg3`, `deriv_sectorCurve_seg3`
- **Used by**: `pv_sector_higher_power`
- **Visibility**: private
- **Lines**: 87-98
- **Notes**: >10 lines (12)

### `theorem pv_sector_higher_power`
- **Type**: `(r : ℝ) (_hr : 0 < r) (α : ℝ) (_hα_nonneg : 0 ≤ α) (_hα_le : α ≤ 2π) (n : ℕ) (hn : 1 ≤ n) (_h_angle : ∃ k : ℤ, n * α = k * (2π)) : ∫ t in (0:ℝ)..3, (sectorCurve r α t) ^ (n - 1) * deriv (sectorCurve r α) t = 0`
- **What**: For `n ≥ 1`, the contour integral of `z^(n-1) dz` along the sector curve vanishes when `nα` is a multiple of `2π` (this is `pv_sector_higher_power`; the closing-angle case).
- **How**: Primitive `F(t) = γ(t)^n / n`, with `HasDerivAt` off `{1,2}` (via `sectorCurve_differentiableAt_off_knots`); apply `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`; evaluate at endpoints `sectorCurve_zero = 0 = sectorCurve_three`.
- **Hypotheses**: `0 < r`, `0 ≤ α ≤ 2π`, `1 ≤ n`, angle-closure condition.
- **Uses from project**: `sectorCurve`, `sectorCurve_continuousOn`, `sectorCurve_differentiableAt_off_knots`, `sectorCurve_zero`, `sectorCurve_three`, `pow_integrableOn_01`, `pow_integrableOn_12`, `pow_integrableOn_23`
- **Used by**: unused in file
- **Visibility**: public (theorem)
- **Lines**: 100-131
- **Notes**: >10 lines (32)

### `theorem sectorCurve_mem_ball`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) : ∀ t ∈ Icc 0 3, sectorCurve r α t ∈ Metric.ball (0 : ℂ) (↑r + 1)`
- **What**: The sector curve image lies inside the open ball `B(0, r+1)`.
- **How**: Case-split into segments using `sectorCurve_seg1/2/3` and bound `|γ(t)| ≤ r < r+1` via `Complex.norm_exp_ofReal_mul_I = 1`.
- **Hypotheses**: `0 < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg1`, `sectorCurve_seg2`, `sectorCurve_seg3`
- **Used by**: `φ_sectorCurve_integrableOn_01`, `φ_sectorCurve_integrableOn_12`, `φ_sectorCurve_integrableOn_23`, `integral_analytic_sectorCurve_eq_zero`
- **Visibility**: private
- **Lines**: 133-154
- **Notes**: >10 lines (22)

### `theorem φ_sectorCurve_integrableOn_01`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) : IntervalIntegrable (fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t) volume 0 1`
- **What**: For analytic `g` on the enclosing ball, `g(γ(t)) · γ'(t)` is interval-integrable on `[0,1]`.
- **How**: Use `hg.continuousOn.comp` on the parametric form `g((tr:ℂ))`; combine with constant `r`; convert via `intervalIntegrable_of_Icc` + `.congr_ae` rewriting through `sectorCurve_seg1` and `deriv_sectorCurve_seg1`.
- **Hypotheses**: `0 < r`, `g` analytic on `B(0, r+1)`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg1`, `deriv_sectorCurve_seg1`, `sectorCurve_mem_ball`
- **Used by**: `φ_sectorCurve_intervalIntegrable`
- **Visibility**: private
- **Lines**: 156-174
- **Notes**: >10 lines (19)

### `theorem φ_sectorCurve_integrableOn_12`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) : IntervalIntegrable (fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t) volume 1 2`
- **What**: Same integrability on the arc segment.
- **How**: Continuous composition via `hg.continuousOn.comp` with `r·exp(I(t-1)α)`; `.congr_ae` via `sectorCurve_seg2` + `deriv_sectorCurve_seg2`.
- **Hypotheses**: `0 < r`, `g` analytic on enclosing ball.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg2`, `deriv_sectorCurve_seg2`, `sectorCurve_mem_ball`
- **Used by**: `φ_sectorCurve_intervalIntegrable`
- **Visibility**: private
- **Lines**: 176-199
- **Notes**: >10 lines (24)

### `theorem φ_sectorCurve_integrableOn_23`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) : IntervalIntegrable (fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t) volume 2 3`
- **What**: Same integrability on the radial-in segment.
- **How**: Continuous composition via `hg.continuousOn.comp` with `((3-t)·r·exp(Iα))`; `.congr_ae` via `sectorCurve_seg3` + `deriv_sectorCurve_seg3`.
- **Hypotheses**: `0 < r`, `g` analytic on enclosing ball.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg3`, `deriv_sectorCurve_seg3`, `sectorCurve_mem_ball`
- **Used by**: `φ_sectorCurve_intervalIntegrable`
- **Visibility**: private
- **Lines**: 201-221
- **Notes**: >10 lines (21)

### `theorem φ_sectorCurve_intervalIntegrable`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) : IntervalIntegrable (fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t) volume 0 3`
- **What**: Combined integrability of `g(γ(t)) γ'(t)` on `[0,3]`.
- **How**: Chain `φ_sectorCurve_integrableOn_01`, `_12`, `_23` via `.trans`.
- **Hypotheses**: `0 < r`, `g` analytic.
- **Uses from project**: `sectorCurve`, `φ_sectorCurve_integrableOn_01`, `φ_sectorCurve_integrableOn_12`, `φ_sectorCurve_integrableOn_23`
- **Used by**: `integral_analytic_sectorCurve_eq_zero`, `cauchyPV_g_intervalIntegrable`, `cauchyPV_g_tendsto_zero`
- **Visibility**: private
- **Lines**: 223-229
- **Notes**: none

### `theorem integral_analytic_sectorCurve_eq_zero`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) : ∫ t in (0:ℝ)..3, g (sectorCurve r α t) * deriv (sectorCurve r α) t = 0`
- **What**: The integral of any analytic `g` along the closed sector curve is zero (loop closes at 0).
- **How**: Existence of primitive `F` via `holomorphic_convex_primitive` on the convex open ball; `HasDerivAt (F ∘ γ)` off `{1,2}` via chain rule with `sectorCurve_differentiableAt_off_knots`; `integral_eq_of_hasDerivAt_off_countable_of_le` reduces to `F(γ(3)) - F(γ(0)) = 0` since `γ(0) = γ(3) = 0`.
- **Hypotheses**: `0 < r`, `g` analytic on enclosing ball.
- **Uses from project**: `sectorCurve`, `sectorCurve_continuousOn`, `sectorCurve_mem_ball`, `sectorCurve_differentiableAt_off_knots`, `sectorCurve_zero`, `sectorCurve_three`, `φ_sectorCurve_intervalIntegrable`, `holomorphic_convex_primitive`
- **Used by**: `cauchyPV_g_tendsto_zero`
- **Visibility**: private
- **Lines**: 234-255
- **Notes**: >10 lines (22)

### `theorem cauchyPV_g_aestronglyMeasurable`
- **Type**: `(r : ℝ) (α : ℝ) (g : ℂ → ℂ) (ε : ℝ) (h_int_g : IntervalIntegrable ... 0 3) : AEStronglyMeasurable (cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε) (volume.restrict (Ioc 0 3))`
- **What**: The cutoff integrand (indicator of `‖γ(t)‖ > ε` times `g(γ)γ'`) is a.e. strongly measurable.
- **How**: `h_int_g.aestronglyMeasurable.indicator` against the support set, then `.congr` via case-split on the cutoff predicate.
- **Hypotheses**: integrability of `g(γ) γ'` on `[0,3]`.
- **Uses from project**: `sectorCurve`, `sectorCurve_continuousOn`, `cauchyPrincipalValueIntegrand'`, `measurableSet_pv_support`
- **Used by**: `cauchyPV_g_intervalIntegrable`, `cauchyPV_g_tendsto_zero`
- **Visibility**: private
- **Lines**: 257-273
- **Notes**: >10 lines (17)

### `theorem cauchyPV_g_norm_le`
- **Type**: `(r : ℝ) (α : ℝ) (g : ℂ → ℂ) (ε : ℝ) (t : ℝ) : ‖cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε t‖ ≤ ‖g (sectorCurve r α t) * deriv (sectorCurve r α) t‖`
- **What**: The cutoff integrand is pointwise bounded in norm by the un-cut integrand.
- **How**: `split_ifs`: equality in cutoff case; trivially `0 ≤ ‖·‖` in zero branch.
- **Hypotheses**: none.
- **Uses from project**: `sectorCurve`, `cauchyPrincipalValueIntegrand'`
- **Used by**: `cauchyPV_g_intervalIntegrable`, `cauchyPV_g_tendsto_zero`
- **Visibility**: private
- **Lines**: 275-283
- **Notes**: none

### `theorem sectorCurve_zero_set_finite`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) : Set.Finite ({t ∈ Icc 0 3 | sectorCurve r α t = 0})`
- **What**: The zero-set of γ in `[0,3]` is finite (in fact ⊆ {0, 3}).
- **How**: `Set.Finite.subset` of `{0, 3}`; case-split on segments using `sectorCurve_seg1/2/3`, `Complex.ofReal_eq_zero`, and `Complex.exp_ne_zero` to rule out non-endpoint zeros.
- **Hypotheses**: `0 < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg1`, `sectorCurve_seg2`, `sectorCurve_seg3`
- **Used by**: `cauchyPV_g_tendsto_zero`
- **Visibility**: private
- **Lines**: 285-303
- **Notes**: >10 lines (19)

### `theorem cauchyPV_g_intervalIntegrable`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) (ε : ℝ) : IntervalIntegrable (cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε) volume 0 3`
- **What**: The cutoff integrand is interval-integrable on `[0,3]`.
- **How**: Dominated by `h_int_g` via `.mono_fun` using `cauchyPV_g_aestronglyMeasurable` and `cauchyPV_g_norm_le`.
- **Hypotheses**: `0 < r`, `g` analytic.
- **Uses from project**: `sectorCurve`, `cauchyPrincipalValueIntegrand'`, `φ_sectorCurve_intervalIntegrable`, `cauchyPV_g_aestronglyMeasurable`, `cauchyPV_g_norm_le`
- **Used by**: `cauchyPV_simplePole_integral_split`
- **Visibility**: private
- **Lines**: 305-314
- **Notes**: >10 lines (10)

### `theorem cauchyPV_inv_integrableOn_0δ`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) : IntervalIntegrable (cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε) volume 0 (ε / r)`
- **What**: On `[0, ε/r]` the cutoff integrand for `z⁻¹` is integrable — it equals 0 because `‖γ(t)‖ = t·r ≤ ε`.
- **How**: Equality with constant 0 via `intervalIntegrable_const.congr`: `‖sectorCurve_seg1‖ = t·r ≤ ε` rules out the cutoff condition.
- **Hypotheses**: `0 < ε < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_norm_seg1`, `cauchyPrincipalValueIntegrand'`
- **Used by**: `cauchyPV_inv_intervalIntegrable`
- **Visibility**: private
- **Lines**: 316-327
- **Notes**: >10 lines (12)

### `theorem cauchyPV_inv_integrableOn_3δ3`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) : IntervalIntegrable (...) volume (3 - ε / r) 3`
- **What**: Symmetric integrability near `t = 3`: zero integrand because `‖γ‖ = (3-t)r ≤ ε`.
- **How**: `intervalIntegrable_const.congr` using `sectorCurve_norm_seg3'`.
- **Hypotheses**: `0 < ε < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_norm_seg3'`, `cauchyPrincipalValueIntegrand'`
- **Used by**: `cauchyPV_inv_intervalIntegrable`
- **Visibility**: private
- **Lines**: 329-342
- **Notes**: >10 lines (14)

### `theorem cauchyPV_inv_integrableOn_δ1`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) : IntervalIntegrable (...) volume (ε / r) 1`
- **What**: On `[ε/r, 1]` the cutoff integrand equals `↑(t⁻¹)` and is integrable.
- **How**: `pv_integrand_seg1` gives explicit form `↑(t⁻¹)`; cutoff is satisfied by `t·r > ε`. Identify a.e. via `Integrable.congr` against `(↑t⁻¹ : ℂ)`.
- **Hypotheses**: `0 < ε < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_norm_seg1`, `cauchyPrincipalValueIntegrand'`, `pv_integrand_seg1`
- **Used by**: `cauchyPV_inv_intervalIntegrable`
- **Visibility**: private
- **Lines**: 344-375
- **Notes**: >10 lines (32)

### `theorem cauchyPV_inv_integrableOn_12`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ) (hε_lt_r : ε < r) : IntervalIntegrable (...) volume 1 2`
- **What**: On the arc segment `[1,2]`, cutoff integrand for `z⁻¹` equals constant `Iα` (and is integrable).
- **How**: `pv_integrand_seg2` gives constant `Iα`; cutoff holds because `‖γ‖ = r > ε`. `Integrable.congr` against `integrableOn_const`.
- **Hypotheses**: `0 < r`, `ε < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg2`, `cauchyPrincipalValueIntegrand'`, `pv_integrand_seg2`
- **Used by**: `cauchyPV_inv_intervalIntegrable`
- **Visibility**: private
- **Lines**: 377-397
- **Notes**: >10 lines (21)

### `theorem cauchyPV_inv_integrableOn_2_3δ`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) : IntervalIntegrable (...) volume 2 (3 - ε / r)`
- **What**: On `[2, 3 - ε/r]`, the cutoff integrand equals `-(↑(3-t)⁻¹)` (and is integrable).
- **How**: Explicit form from `sectorCurve_seg3` + `deriv_sectorCurve_seg3` followed by `field_simp`; cutoff holds since `(3-t)r > ε`.
- **Hypotheses**: `0 < ε < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg3`, `deriv_sectorCurve_seg3`, `sectorCurve_norm_seg3'`, `cauchyPrincipalValueIntegrand'`
- **Used by**: `cauchyPV_inv_intervalIntegrable`
- **Visibility**: private
- **Lines**: 399-441
- **Notes**: >10 lines (43)

### `theorem cauchyPV_inv_intervalIntegrable`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) : IntervalIntegrable (cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε) volume 0 3`
- **What**: Combined integrability of the `z⁻¹` cutoff integrand on `[0,3]`.
- **How**: Chain the five sub-intervals via `.trans`.
- **Hypotheses**: `0 < ε < r`.
- **Uses from project**: `sectorCurve`, `cauchyPrincipalValueIntegrand'`, `cauchyPV_inv_integrableOn_0δ`, `cauchyPV_inv_integrableOn_δ1`, `cauchyPV_inv_integrableOn_12`, `cauchyPV_inv_integrableOn_2_3δ`, `cauchyPV_inv_integrableOn_3δ3`
- **Used by**: `cauchyPV_simplePole_integral_split`
- **Visibility**: private
- **Lines**: 443-451
- **Notes**: none

### `theorem cauchyPV_g_tendsto_zero`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) : Tendsto (fun ε => ∫ t in (0:ℝ)..3, cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε t) (𝓝[>] 0) (𝓝 0)`
- **What**: As ε → 0+, the cutoff integral of an analytic `g` along the sector tends to 0 (using closed-loop primitive existence).
- **How**: Dominated convergence (`intervalIntegral.tendsto_integral_filter_of_dominated_convergence`) with bound `‖g(γ)γ'‖` and pointwise limit (away from γ-zero-set, ε → 0 forces cutoff to be on); identifies limit with `integral_analytic_sectorCurve_eq_zero`.
- **Hypotheses**: `0 < r`, `g` analytic on enclosing ball.
- **Uses from project**: `sectorCurve`, `cauchyPrincipalValueIntegrand'`, `φ_sectorCurve_intervalIntegrable`, `integral_analytic_sectorCurve_eq_zero`, `cauchyPV_g_aestronglyMeasurable`, `cauchyPV_g_norm_le`, `sectorCurve_zero_set_finite`
- **Used by**: `cauchyPV_sectorCurve_simplePole`
- **Visibility**: private
- **Lines**: 453-481
- **Notes**: >10 lines (29)

### `theorem cauchyPV_simplePole_integral_split`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (c : ℂ) (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) : ∀ᶠ ε in 𝓝[>] 0, (∫ ... (c/z + g z) ...) = c · (∫ ... z⁻¹ ...) + (∫ ... g ...)`
- **What**: Eventually (for ε < r), the cutoff integral splits linearly: `(c/z + g)` decomposes into `c · z⁻¹ + g`.
- **How**: Pointwise equality of the integrand (after `split_ifs` and `ring`); `intervalIntegral.integral_congr`, `intervalIntegral.integral_const_mul`, `intervalIntegral.integral_add` using both `cauchyPV_inv_intervalIntegrable` and `cauchyPV_g_intervalIntegrable`.
- **Hypotheses**: `0 < r`, `g` analytic.
- **Uses from project**: `sectorCurve`, `cauchyPrincipalValueIntegrand'`, `cauchyPV_inv_intervalIntegrable`, `cauchyPV_g_intervalIntegrable`
- **Used by**: `cauchyPV_sectorCurve_simplePole`
- **Visibility**: private
- **Lines**: 483-515
- **Notes**: >10 lines (33)

### `theorem cauchyPV_sectorCurve_simplePole`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (hα_nonneg : 0 ≤ α) (hα_le : α ≤ 2π) (c : ℂ) (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) : CauchyPrincipalValueExists' (fun z => c / z + g z) (sectorCurve r α) 0 3 0 ∧ cauchyPrincipalValue' (...) = I * ↑α * c`
- **What**: **Lemma 3.1 (Simple pole)**: For `f(z) = c/z + g(z)` with `g` analytic on `B(0, r+1)`, the principal value of `∫ f dz` along the sector equals `I · α · c`.
- **How**: Tendsto-product: combine `pv_sector_dz_over_z` (giving `L_inv = Iα` for `∫ dz/z`) with `cauchyPV_g_tendsto_zero`; split via `cauchyPV_simplePole_integral_split`. Conclude `tendsto → CauchyPrincipalValueExists' ∧ value = Iα · c`.
- **Hypotheses**: `0 < r`, `0 ≤ α ≤ 2π`, `g` analytic.
- **Uses from project**: `sectorCurve`, `CauchyPrincipalValueExists'`, `cauchyPrincipalValueIntegrand'`, `cauchyPrincipalValue'`, `pv_sector_dz_over_z`, `cauchyPV_g_tendsto_zero`, `cauchyPV_simplePole_integral_split`
- **Used by**: `cauchyPV_sectorCurve_eq_mul_residueSimplePole`
- **Visibility**: public (theorem)
- **Lines**: 523-539
- **Notes**: >10 lines (17)

### `theorem cauchyPV_sectorCurve_eq_mul_residueSimplePole`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (hα_nonneg : 0 ≤ α) (hα_le : α ≤ 2π) (f : ℂ → ℂ) (c : ℂ) (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) (hf_eq : ∀ z, z ≠ 0 → f z = c / z + g z) (hc : c = residueSimplePole f 0) : CauchyPrincipalValueExists' f (sectorCurve r α) 0 3 0 ∧ cauchyPrincipalValue' f (sectorCurve r α) 0 3 0 = I * ↑α * residueSimplePole f 0`
- **What**: Variant of Lemma 3.1 stated for arbitrary `f` agreeing with `c/z + g` away from 0, with `c = residueSimplePole f 0`.
- **How**: Show eventually the cutoff integrands of `f` and `c/z+g` coincide (away from γ=0 by the cutoff condition); use `hf_eq` and `cauchyPV_sectorCurve_simplePole`. Transport `Tendsto.congr'` to identify PV existence and value.
- **Hypotheses**: `0 < r`, `0 ≤ α ≤ 2π`, `g` analytic, `f = c/z + g` off 0, `c = residueSimplePole f 0`.
- **Uses from project**: `sectorCurve`, `CauchyPrincipalValueExists'`, `cauchyPrincipalValueIntegrand'`, `cauchyPrincipalValue'`, `residueSimplePole`, `cauchyPV_sectorCurve_simplePole`
- **Used by**: unused in file
- **Visibility**: public (theorem)
- **Lines**: 543-582
- **Notes**: >10 lines (40)

### `theorem sectorCurve_ne_zero_of_Icc_δ`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (δ : ℝ) (hδ_pos : 0 < δ) (_hδ_lt_1 : δ < 1) : ∀ t ∈ Icc δ (3 - δ), sectorCurve r α t ≠ 0`
- **What**: On the trimmed interval `[δ, 3-δ]`, the sector curve is non-zero.
- **How**: Case-split by segment; in each, the only zero would force `t = 0` or `t = 3` (excluded) or `r = 0` (contradiction).
- **Hypotheses**: `0 < δ < 1`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg1`, `sectorCurve_seg2`, `sectorCurve_seg3`
- **Used by**: `zpow_primitive_hasDerivAt`, `pv_sector_negative_power`
- **Visibility**: private
- **Lines**: 584-605
- **Notes**: >10 lines (22)

### `theorem sectorCurve_norm_le_near_zero`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (δ : ℝ) (_hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) (ε : ℝ) (hδr_eq : δ · r = ε) : ∀ t ∈ Icc 0 δ, ‖sectorCurve r α t‖ ≤ ε`
- **What**: Near `t = 0`, the sector norm is at most ε (where ε = δr).
- **How**: `sectorCurve_norm_seg1` then `mul_le_mul_of_nonneg_right`.
- **Hypotheses**: `0 < r`, `0 < δ < 1`, `δr = ε`.
- **Uses from project**: `sectorCurve`, `sectorCurve_norm_seg1`
- **Used by**: `pv_cutoff_integral_eq_mid`
- **Visibility**: private
- **Lines**: 607-613
- **Notes**: none

### `theorem sectorCurve_norm_le_near_three`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (δ : ℝ) (hδ_lt_1 : δ < 1) (ε : ℝ) (hδr_eq : δ · r = ε) : ∀ t ∈ Icc (3 - δ) 3, ‖sectorCurve r α t‖ ≤ ε`
- **What**: Symmetric bound near `t = 3`.
- **How**: `sectorCurve_norm_seg3'` then `mul_le_mul_of_nonneg_right`.
- **Hypotheses**: `0 < r`, `δ < 1`, `δr = ε`.
- **Uses from project**: `sectorCurve`, `sectorCurve_norm_seg3'`
- **Used by**: `pv_cutoff_integral_eq_mid`
- **Visibility**: private
- **Lines**: 615-623
- **Notes**: none

### `theorem sectorCurve_norm_gt_mid`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (δ : ℝ) (hδ_pos : 0 < δ) (_hδ_lt_1 : δ < 1) (ε : ℝ) (hε_lt_r : ε < r) (hδr_eq : δ · r = ε) : ∀ t ∈ Ioo δ (3 - δ), ε < ‖sectorCurve r α t‖`
- **What**: On the trimmed open interval, the norm exceeds ε.
- **How**: Segment-split: on `seg1`, `t·r > δ·r = ε`; on `seg2`, `‖γ‖ = r > ε`; on `seg3`, `(3-t)·r > ε`.
- **Hypotheses**: `0 < r`, `0 < δ < 1`, `ε < r`, `δr = ε`.
- **Uses from project**: `sectorCurve`, `sectorCurve_norm_seg1`, `sectorCurve_norm_on_arc`, `sectorCurve_norm_seg3'`
- **Used by**: `pv_cutoff_integral_eq_mid`
- **Visibility**: private
- **Lines**: 625-643
- **Notes**: >10 lines (19)

### `theorem zpow_integrableOn_δ1`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) : IntervalIntegrable (fun t => (sectorCurve r α t) ^ (-(↑n : ℤ)) * deriv (sectorCurve r α) t) volume δ 1`
- **What**: Integrability of `γ^{-n} · γ'` on `[δ, 1]` (trimmed near 0).
- **How**: `ContinuousOn.zpow₀` applied to `(t·r:ℂ)^{-n}`; non-vanishing follows from `δ < t`; combine with constant; `.congr_ae` via segment formula.
- **Hypotheses**: `0 < r`, `0 < δ < 1`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg1`, `deriv_sectorCurve_seg1`
- **Used by**: `pv_cutoff_integral_eq_mid`, `pv_sector_negative_power`
- **Visibility**: private
- **Lines**: 645-662
- **Notes**: >10 lines (18)

### `theorem zpow_integrableOn_12`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ) : IntervalIntegrable (...) volume 1 2`
- **What**: Integrability of `γ^{-n} · γ'` on the arc.
- **How**: `ContinuousOn.zpow₀` of `r·exp(I(t-1)α)` (non-vanishing via `mul_ne_zero` and `exp_ne_zero`); `.congr_ae` via `sectorCurve_seg2`.
- **Hypotheses**: `0 < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg2`, `deriv_sectorCurve_seg2`
- **Used by**: `pv_cutoff_integral_eq_mid`, `pv_sector_negative_power`
- **Visibility**: private
- **Lines**: 664-681
- **Notes**: >10 lines (18)

### `theorem zpow_integrableOn_23δ`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) : IntervalIntegrable (...) volume 2 (3 - δ)`
- **What**: Integrability on `[2, 3-δ]`.
- **How**: `ContinuousOn.zpow₀` of `(3-t)·r·exp(Iα)` (non-vanishing for `t < 3-δ < 3`); `.congr_ae` via `sectorCurve_seg3`.
- **Hypotheses**: `0 < r`, `0 < δ < 1`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg3`, `deriv_sectorCurve_seg3`
- **Used by**: `pv_cutoff_integral_eq_mid`, `pv_sector_negative_power`
- **Visibility**: private
- **Lines**: 683-703
- **Notes**: >10 lines (21)

### `theorem zpow_primitive_hasDerivAt`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ) (hn : 2 ≤ n) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) : ∀ t ∈ Ioo δ (3 - δ) \ ({1, 2} ∩ Ioo δ (3 - δ)), HasDerivAt F (f t) t`
- **What**: Off the two knot points, `F(t) = γ(t)^{1-n}/(1-n)` has derivative `γ(t)^{-n} γ'(t)`.
- **How**: `hasDerivAt_zpow` for `m = 1 - n` (which is `≤ -1`, so non-zero base needed: `sectorCurve_ne_zero_of_Icc_δ`); compose with `sectorCurve_differentiableAt_off_knots`; `.div_const`; `mul_div_cancel_left₀`.
- **Hypotheses**: `0 < r`, `2 ≤ n`, `0 < δ < 1`.
- **Uses from project**: `sectorCurve`, `sectorCurve_ne_zero_of_Icc_δ`, `sectorCurve_differentiableAt_off_knots`
- **Used by**: `pv_sector_negative_power`
- **Visibility**: private
- **Lines**: 705-730
- **Notes**: >10 lines (26)

### `theorem zpow_ftc_vanishes`
- **Type**: `(r : ℝ) (_hr : 0 < r) (α : ℝ) (n : ℕ) (_hn : 2 ≤ n) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) (h_exp_one : exp (I * ↑((1 - ↑n) * α)) = 1) : F (3 - δ) - F δ = 0`
- **What**: When the angle-closure holds (`exp(I(1-n)α) = 1`), the primitive `F = γ^{1-n}/(1-n)` agrees at `δ` and `3 - δ`.
- **How**: `sectorCurve_seg1` at `δ` gives `γ(δ) = (δ·r)` and `sectorCurve_seg3` at `3-δ` gives `γ(3-δ) = (δ·r)·exp(Iα)`; `mul_zpow` then `Complex.exp_int_mul` followed by `h_exp_one` collapses the angle factor to 1.
- **Hypotheses**: `0 < r`, `2 ≤ n`, `0 < δ < 1`, `exp(I(1-n)α) = 1`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg1`, `sectorCurve_seg3`
- **Used by**: `pv_sector_negative_power`
- **Visibility**: private
- **Lines**: 732-752
- **Notes**: >10 lines (21)

### `theorem angle_condition_exp_eq_one`
- **Type**: `(n : ℕ) (hn : 2 ≤ n) (α : ℝ) (k : ℤ) (hk : (↑(n-1) : ℤ) * α = k * (2π)) : exp (I * ↑((1 - ↑n) * α)) = 1`
- **What**: Translates the angle condition `(n-1)α = 2πk` into `exp(I(1-n)α) = 1`.
- **How**: Construct `j = -k` so that `I(1-n)α = j · 2πI`; apply `Complex.exp_int_mul_two_pi_mul_I`.
- **Hypotheses**: `2 ≤ n`, integer `k` realising `(n-1)α = 2πk`.
- **Uses from project**: []
- **Used by**: `pv_sector_negative_power`
- **Visibility**: private
- **Lines**: 754-768
- **Notes**: >10 lines (15)

### `theorem pv_cutoff_integral_eq_mid`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) : ∫ t in (0:ℝ)..3, (if ‖γ t‖ > ε then γ(t)^{-n} γ'(t) else 0) = ∫ t in δ..(3-δ), γ(t)^{-n} γ'(t)`
- **What**: The cutoff integral collapses to the middle interval `[δ, 3-δ]`, where `δ = ε/r`.
- **How**: Near `0` and `3`, cutoff is off (`if_neg`) so integrals vanish (via `intervalIntegral.integral_zero_ae`). On the middle, cutoff is on (`if_pos`) and the integrand matches `f`. Splice via `intervalIntegral.integral_add_adjacent_intervals` (with explicit `IntervalIntegrable` witnesses).
- **Hypotheses**: `0 < r`, `0 < ε < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_norm_le_near_zero`, `sectorCurve_norm_le_near_three`, `sectorCurve_norm_gt_mid`, `zpow_integrableOn_δ1`, `zpow_integrableOn_12`, `zpow_integrableOn_23δ`
- **Used by**: `pv_sector_negative_power`
- **Visibility**: private
- **Lines**: 770-856
- **Notes**: >10 lines (87)

### `theorem pv_sector_negative_power`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (_hα_nonneg : 0 ≤ α) (_hα_le : α ≤ 2π) (n : ℕ) (hn : 2 ≤ n) (h_angle : ∃ k : ℤ, (↑(n-1) : ℤ) * α = k * (2π)) : CauchyPrincipalValueExists' (fun z => z ^ (-(↑n : ℤ))) (sectorCurve r α) 0 3 0 ∧ cauchyPrincipalValue' (...) = 0`
- **What**: **Equation (3.4)**: For `n ≥ 2`, the principal value of `∫ z^{-n} dz` along the sector vanishes when `(n-1)α` is a multiple of `2π`.
- **How**: Cutoff integral equals zero eventually: combine `pv_cutoff_integral_eq_mid` with FTC `integral_eq_of_hasDerivAt_off_countable_of_le` using primitive from `zpow_primitive_hasDerivAt`; conclude via `zpow_ftc_vanishes` + `angle_condition_exp_eq_one`. Then `Tendsto` to 0 gives existence + value.
- **Hypotheses**: `0 < r`, `2 ≤ n`, angle condition.
- **Uses from project**: `sectorCurve`, `sectorCurve_continuousOn`, `CauchyPrincipalValueExists'`, `cauchyPrincipalValue'`, `sectorCurve_ne_zero_of_Icc_δ`, `zpow_integrableOn_δ1`, `zpow_integrableOn_12`, `zpow_integrableOn_23δ`, `pv_cutoff_integral_eq_mid`, `zpow_primitive_hasDerivAt`, `zpow_ftc_vanishes`, `angle_condition_exp_eq_one`
- **Used by**: unused in file
- **Visibility**: public (theorem)
- **Lines**: 862-909
- **Notes**: >10 lines (48)

### `theorem generalizedWindingNumber_sectorCurve`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (hα_nonneg : 0 ≤ α) (hα_le : α ≤ 2π) (_hPV : CauchyPrincipalValueExists' (fun z => z⁻¹) (sectorCurve r α) 0 3 0) : generalizedWindingNumber' (sectorCurve r α) 0 3 0 = ↑α / (2 * ↑π)`
- **What**: The generalized winding number of the sector curve around 0 equals `α / (2π)`.
- **How**: Unfold `generalizedWindingNumber'`; the inverse-PV equals `Iα` by `pv_sector_dz_over_z`; divide by `2πI` to get `α/(2π)` via `field_simp`.
- **Hypotheses**: `0 < r`, `0 ≤ α ≤ 2π`, PV exists.
- **Uses from project**: `sectorCurve`, `CauchyPrincipalValueExists'`, `generalizedWindingNumber'`, `pv_sector_dz_over_z`
- **Used by**: unused in file
- **Visibility**: public (theorem)
- **Lines**: 913-922
- **Notes**: none

---

## File Summary

- **Total declarations**: 33 (all `theorem`; no `def`)
- **Public API**: `pv_sector_higher_power`, `cauchyPV_sectorCurve_simplePole`, `cauchyPV_sectorCurve_eq_mul_residueSimplePole`, `pv_sector_negative_power`, `generalizedWindingNumber_sectorCurve`
- **Unused in file**: the five public-API theorems above (consumed externally); `pv_sector_higher_power` has no in-file consumer
- **Sorries**: 0
- **set_options**: none
- **Attribute**: `attribute [local instance] Classical.propDecidable` at the file top
- **Long proofs (>10 lines)**: 24 theorems; the largest are `pv_cutoff_integral_eq_mid` ~87 lines, `pv_sector_negative_power` ~48 lines, `cauchyPV_inv_integrableOn_2_3δ` ~43 lines, `cauchyPV_sectorCurve_eq_mul_residueSimplePole` ~40 lines, `cauchyPV_simplePole_integral_split` ~33 lines, `cauchyPV_inv_integrableOn_δ1` ~32 lines, `pv_sector_higher_power` ~32 lines, `sectorCurve_differentiableAt_off_knots` ~31 lines, `cauchyPV_g_tendsto_zero` ~29 lines, `zpow_primitive_hasDerivAt` ~26 lines
- **Purpose**: This file establishes the higher-order principal-value identities for the model sector curve `γ_{r,α}` (three-piece: radial out to `r`, arc of angle α, radial back to 0) used in Lemma 3.1 of the generalised residue theory. It proves: (1) `∫ z^{n-1} dz = 0` for `n ≥ 1` under the closing-angle condition, (2) for `f = c/z + g` with `g` analytic on an enclosing ball, the principal value equals `I·α·c` (simple-pole formula), (3) variant referring directly to `residueSimplePole f 0`, (4) `PV ∫ z^{-n} dz = 0` for `n ≥ 2` when `(n-1)α` is a multiple of `2π`, and (5) the generalized winding number around 0 equals `α/(2π)`. The proof apparatus consists of segment-wise integrability lemmas, cutoff-integral reduction to a trimmed middle interval, primitives via convex-domain analyticity (`holomorphic_convex_primitive`) for the analytic part, and explicit FTC for `z^{-n}`.
