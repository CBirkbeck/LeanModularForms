# SectorCurve.lean — Inventory

### `def sectorCurve`
- **Type**: `(r α t : ℝ) : ℂ`
- **What**: Model sector curve on `[0, 3]`: radial segment `[0, 1]`, arc segment `[1, 2]` of radius `r` from angle `0` to `α`, returning radial segment `[2, 3]`.
- **How**: Piecewise `if t ≤ 1 then ↑(t·r) else if t ≤ 2 then ↑r · exp(I·↑((t-1)·α)) else ↑((3-t)·r) · exp(I·↑α)`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `sectorCurve_zero`, `sectorCurve_three`, `sectorCurve_closed`, `sectorCurve_one`, `sectorCurve_two`, `sectorCurve_seg1`, `sectorCurve_seg2`, `sectorCurve_seg3`, `sectorCurve_continuousOn`, `sectorCurve_passes_through_origin`, `sectorCurve_norm_on_arc`, `deriv_sectorCurve_seg1`, `deriv_sectorCurve_seg2`, `deriv_sectorCurve_seg3`, `pv_integrand_seg1`, `pv_integrand_seg2`, `pv_integrand_seg3`, `sectorCurve_norm_seg1`, `sectorCurve_norm_seg3'`, all `pv_cutoff_F_integrable_*`, `pv_sector_cutoff_base_integrabilities`, `pv_sector_cutoff_composed_integrabilities`, `pv_cutoff_integral_seg1_eq_inv`, `pv_cutoff_integral_seg2_eq_Ialpha`, `pv_cutoff_integral_seg3_eq_neg_inv`, `pv_sector_cutoff_eq`, `pv_sector_dz_over_z`
- **Visibility**: public
- **Lines**: 58–64
- **Notes**: noncomputable.

### `theorem sectorCurve_zero`
- **Type**: `(r α : ℝ) : sectorCurve r α 0 = 0`
- **What**: The sector curve starts at `0`.
- **How**: `simp [sectorCurve]` (the `t ≤ 1` branch with `t = 0` gives `0 · r = 0`).
- **Hypotheses**: None.
- **Uses from project**: `sectorCurve`
- **Used by**: `sectorCurve_closed`, `sectorCurve_passes_through_origin`
- **Visibility**: public
- **Lines**: 69–71

### `theorem sectorCurve_three`
- **Type**: `(r α : ℝ) : sectorCurve r α 3 = 0`
- **What**: The sector curve ends at `0`.
- **How**: `simp only` with `¬3 ≤ 1`, `¬3 ≤ 2`, reducing to `(3 - 3)·r · exp(I·α) = 0`.
- **Hypotheses**: None.
- **Uses from project**: `sectorCurve`
- **Used by**: `sectorCurve_closed`, `sectorCurve_passes_through_origin`
- **Visibility**: public
- **Lines**: 74–78

### `theorem sectorCurve_closed`
- **Type**: `(r α : ℝ) : sectorCurve r α 0 = sectorCurve r α 3`
- **What**: The sector curve is closed.
- **How**: Both endpoints are `0` via `sectorCurve_zero` and `sectorCurve_three`.
- **Hypotheses**: None.
- **Uses from project**: `sectorCurve`, `sectorCurve_zero`, `sectorCurve_three`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 81–83

### `theorem sectorCurve_one`
- **Type**: `(r α : ℝ) : sectorCurve r α 1 = ↑r`
- **What**: At `t = 1`, the sector curve is `r` (radial-arc junction).
- **How**: `simp [sectorCurve]`.
- **Hypotheses**: None.
- **Uses from project**: `sectorCurve`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 86–88

### `theorem sectorCurve_two`
- **Type**: `(r α : ℝ) : sectorCurve r α 2 = ↑r * exp (I * ↑α)`
- **What**: At `t = 2`, the sector curve is `r · exp(iα)` (end of arc).
- **How**: `simp only` with `¬2 ≤ 1`, `2 ≤ 2`; `congr 1; congr 1; push_cast; ring`.
- **Hypotheses**: None.
- **Uses from project**: `sectorCurve`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 91–98

### `theorem sectorCurve_seg1`
- **Type**: `(r α : ℝ) (t : ℝ) (ht : t ∈ Icc 0 1) : sectorCurve r α t = ↑(t * r)`
- **What**: On `[0, 1]`, the curve is `t·r`.
- **How**: `simp [sectorCurve, ht.2]`.
- **Hypotheses**: `t ∈ Icc 0 1`.
- **Uses from project**: `sectorCurve`
- **Used by**: `sectorCurve_continuousOn`, `pv_integrand_seg1`, `sectorCurve_norm_seg1`, `pv_cutoff_integral_seg1_eq_inv`
- **Visibility**: public
- **Lines**: 101–103

### `theorem sectorCurve_seg2`
- **Type**: `(r α : ℝ) (t : ℝ) (ht : t ∈ Icc 1 2) : sectorCurve r α t = ↑r * exp (I * ↑((t - 1) * α))`
- **What**: On `[1, 2]`, the curve is the arc `r · exp(i·(t-1)·α)`.
- **How**: Case-split on `t = 1` (boundary, via `exp_zero`) vs `t > 1` (use `if_neg` on `t ≤ 1`).
- **Hypotheses**: `t ∈ Icc 1 2`.
- **Uses from project**: `sectorCurve`
- **Used by**: `sectorCurve_continuousOn`, `sectorCurve_norm_on_arc`, `deriv_sectorCurve_seg2`, `pv_integrand_seg2`, `pv_cutoff_F_integrable_1_2`, `pv_cutoff_integral_seg2_eq_Ialpha`
- **Visibility**: public
- **Lines**: 106–110

### `theorem sectorCurve_seg3`
- **Type**: `(r α : ℝ) (t : ℝ) (ht : t ∈ Icc 2 3) : sectorCurve r α t = ↑((3 - t) * r) * exp (I * ↑α)`
- **What**: On `[2, 3]`, the curve is `(3 - t)·r · exp(iα)` (returning ray).
- **How**: Case-split on `t = 2` (use `if_neg` for `¬2 ≤ 1`, `if_pos` for `2 ≤ 2`, then `push_cast`, `ring_nf`) vs `t > 2` (use `if_neg` for both).
- **Hypotheses**: `t ∈ Icc 2 3`.
- **Uses from project**: `sectorCurve`
- **Used by**: `sectorCurve_continuousOn`, `deriv_sectorCurve_seg3`, `pv_integrand_seg3`, `sectorCurve_norm_seg3'`, `pv_cutoff_F_integrable_2_3delta`, `pv_cutoff_integral_seg3_eq_neg_inv`
- **Visibility**: public
- **Lines**: 113–121

### `theorem sectorCurve_continuousOn`
- **Type**: `(r α : ℝ) : ContinuousOn (sectorCurve r α) (Icc 0 3)`
- **What**: The sector curve is continuous on `[0, 3]`.
- **How**: Split `Icc 0 3 = Icc 0 1 ∪ Icc 1 2 ∪ Icc 2 3` (via `ext` + `by_cases`); show continuity on each part by congruence with the closed-form segment expression (`sectorCurve_seg1/2/3`); glue with `ContinuousOn.union_of_isClosed` twice.
- **Hypotheses**: None.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg1`, `sectorCurve_seg2`, `sectorCurve_seg3`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 124–163
- **Notes**: >10 lines; key step `ContinuousOn.union_of_isClosed`.

### `theorem sectorCurve_passes_through_origin`
- **Type**: `(r α : ℝ) : sectorCurve r α 0 = 0 ∧ sectorCurve r α 3 = 0`
- **What**: The curve passes through `0` at both endpoints.
- **How**: `⟨sectorCurve_zero, sectorCurve_three⟩`.
- **Hypotheses**: None.
- **Uses from project**: `sectorCurve`, `sectorCurve_zero`, `sectorCurve_three`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 166–168

### `theorem sectorCurve_norm_on_arc`
- **Type**: `(r : ℝ) (hr : 0 < r) (α t : ℝ) (ht : t ∈ Icc 1 2) : ‖sectorCurve r α t‖ = r`
- **What**: On the arc segment, the curve has constant modulus `r`.
- **How**: Use `sectorCurve_seg2`; simplify `‖r · exp(I·(t-1)·α)‖ = r · 1` via `Complex.norm_exp_I_mul_ofReal`; apply `Complex.norm_of_nonneg (le_of_lt hr)`.
- **Hypotheses**: `0 < r`, `t ∈ Icc 1 2`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg2`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 171–176

### `theorem deriv_sectorCurve_seg1`
- **Type**: `(r α t : ℝ) (ht : t ∈ Ioo 0 1) : deriv (sectorCurve r α) t = ↑r`
- **What**: On `(0, 1)`, the derivative is the constant `r`.
- **How**: Show `sectorCurve =ᶠ[𝓝 t] fun s => ↑(s · r)` via `filter_upwards [Iio_mem_nhds ht.2]`; apply `EventuallyEq.deriv_eq` and `HasDerivAt`-build for `s ↦ s·r` then `.ofReal_comp`.
- **Hypotheses**: `t ∈ Ioo 0 1`.
- **Uses from project**: `sectorCurve`
- **Used by**: `pv_integrand_seg1`, `pv_cutoff_integral_seg1_eq_inv`
- **Visibility**: public
- **Lines**: 181–193

### `theorem deriv_sectorCurve_seg2`
- **Type**: `(r α t : ℝ) (ht : t ∈ Ioo 1 2) : deriv (sectorCurve r α) t = ↑r * (I * ↑α) * exp (I * ↑((t - 1) * α))`
- **What**: On `(1, 2)`, the derivative is `r · iα · exp(i·(t-1)·α)`.
- **How**: `EventuallyEq` to `s ↦ ↑r · exp(I · ↑((s-1)·α))` on `Ioo 1 2` (via `isOpen_Ioo.mem_nhds`); chain rule: real `s ↦ (s-1)·α` has deriv `α`, then `.ofReal_comp`, then `hasDerivAt_exp ... .comp` with `.mul`; multiply with the constant `r`; `convert ... using 1; ring`.
- **Hypotheses**: `t ∈ Ioo 1 2`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg2`
- **Used by**: `pv_integrand_seg2`, `pv_cutoff_F_integrable_1_2`, `pv_cutoff_integral_seg2_eq_Ialpha`
- **Visibility**: public
- **Lines**: 197–222
- **Notes**: >10 lines; key step `hasDerivAt_exp _ .comp t`.

### `theorem deriv_sectorCurve_seg3`
- **Type**: `(r α t : ℝ) (ht : t ∈ Ioo 2 3) : deriv (sectorCurve r α) t = -(↑r) * exp (I * ↑α)`
- **What**: On `(2, 3)`, the derivative is `-r · exp(iα)`.
- **How**: `EventuallyEq` to `s ↦ ↑((3-s)·r) · exp(I·↑α)` on `Ioi 2`; real derivative of `s ↦ (3-s)·r` is `-r` (via `hasDerivAt_const.sub hasDerivAt_id`); `.ofReal_comp`; `mul_const`; `.deriv`; `push_cast; ring`.
- **Hypotheses**: `t ∈ Ioo 2 3`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg3`
- **Used by**: `pv_integrand_seg3`, `pv_cutoff_F_integrable_2_3delta`, `pv_cutoff_integral_seg3_eq_neg_inv`
- **Visibility**: public
- **Lines**: 226–246
- **Notes**: >10 lines; uses `filter_upwards [Ioi_mem_nhds ht.1]`.

### `theorem pv_integrand_seg1`
- **Type**: `(r : ℝ) (hr : 0 < r) (α t : ℝ) (ht : t ∈ Ioo 0 1) : (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = ↑(t⁻¹)`
- **What**: On seg1, the PV integrand `(σ)⁻¹ · σ'` simplifies to `1/t`.
- **How**: Rewrite `sectorCurve = t·r` and `deriv = r`; `field_simp` after asserting `t, r ≠ 0`.
- **Hypotheses**: `0 < r`, `t ∈ Ioo 0 1`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg1`, `deriv_sectorCurve_seg1`
- **Used by**: `pv_cutoff_F_integrable_delta_1`
- **Visibility**: public
- **Lines**: 252–259

### `theorem pv_integrand_seg2`
- **Type**: `(r : ℝ) (hr : 0 < r) (α t : ℝ) (ht : t ∈ Ioo 1 2) : (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = I * ↑α`
- **What**: On seg2 (arc), the PV integrand simplifies to `i·α`.
- **How**: Rewrite curve as arc and derivative; both `r ≠ 0` and `exp(I·(t-1)·α) ≠ 0`; `field_simp`.
- **Hypotheses**: `0 < r`, `t ∈ Ioo 1 2`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg2`, `deriv_sectorCurve_seg2`
- **Used by**: unused in file (subsumed by per-segment integral evaluations)
- **Visibility**: public
- **Lines**: 262–268

### `theorem pv_integrand_seg3`
- **Type**: `(r : ℝ) (hr : 0 < r) (α t : ℝ) (ht : t ∈ Ioo 2 3) : (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = -↑((3 - t)⁻¹)`
- **What**: On seg3, the PV integrand simplifies to `-1/(3 - t)`.
- **How**: Substitute curve and derivative; `r, exp(I·α), (3 - t) ≠ 0`; `push_cast; field_simp`.
- **Hypotheses**: `0 < r`, `t ∈ Ioo 2 3`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg3`, `deriv_sectorCurve_seg3`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 271–280

### `theorem integral_seg1_eq_neg_log`
- **Type**: `(ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) : ∫ t in ε..1, (t : ℝ)⁻¹ = -Real.log ε`
- **What**: `∫_ε^1 1/t = -log ε`.
- **How**: `integral_inv_of_pos hε one_pos`, `Real.log_div`, `Real.log_one`, `zero_sub`.
- **Hypotheses**: `0 < ε < 1`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 285–288

### `theorem integral_seg3_eq_log`
- **Type**: `(ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) : ∫ t in 2..(3 - ε), -((3 - t)⁻¹) = Real.log ε`
- **What**: `∫_2^{3-ε} -1/(3 - t) = log ε`.
- **How**: Negate; substitute `u := 3 - t` via `intervalIntegral.integral_comp_sub_left`; reduce to `∫_ε^1 u⁻¹`.
- **Hypotheses**: `0 < ε < 1`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 291–301

### `theorem sectorCurve_norm_seg1`
- **Type**: `(r : ℝ) (hr : 0 < r) (α t : ℝ) (ht : t ∈ Icc 0 1) : ‖sectorCurve r α t‖ = t * r`
- **What**: On seg1, `‖σ(t)‖ = t·r`.
- **How**: `sectorCurve_seg1`; `Complex.norm_of_nonneg` with `mul_nonneg ht.1 hr.le`.
- **Hypotheses**: `0 < r`, `t ∈ Icc 0 1`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg1`
- **Used by**: `pv_cutoff_F_integrable_0_delta`, `pv_cutoff_F_integrable_delta_1`, `pv_cutoff_integral_seg1_eq_inv`, `pv_sector_cutoff_eq`
- **Visibility**: public
- **Lines**: 304–307

### `theorem sectorCurve_norm_seg3'`
- **Type**: `(r : ℝ) (hr : 0 < r) (α t : ℝ) (ht : t ∈ Icc 2 3) : ‖sectorCurve r α t‖ = (3 - t) * r`
- **What**: On seg3, `‖σ(t)‖ = (3 - t)·r`.
- **How**: `sectorCurve_seg3`; norm of product is product of norms; `Complex.norm_exp_I_mul_ofReal = 1`; `Complex.norm_of_nonneg`.
- **Hypotheses**: `0 < r`, `t ∈ Icc 2 3`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg3`
- **Used by**: `pv_cutoff_F_integrable_3delta_3`, `pv_cutoff_F_integrable_2_3delta`, `pv_cutoff_integral_seg3_eq_neg_inv`, `pv_sector_cutoff_eq`
- **Visibility**: public
- **Lines**: 310–313

### `theorem log_cancellation`
- **Type**: `(r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) (hεr : ε < r) : (∫ t in (ε/r)..1, ↑(t⁻¹)) + (∫ t in 2..(3 - ε/r), -(↑((3 - t)⁻¹))) = 0`
- **What**: The logarithmic divergences from seg1 and seg3 cancel after rescaling `ε ↦ ε/r`.
- **How**: Compute each real integral as ±`log(ε/r)` via `integral_inv_of_pos` (with substitution `u := 3 - t` for seg3); lift via `intervalIntegral.integral_ofReal`; combine `↑(-log(ε/r)) + ↑(log(ε/r)) = ↑0 = 0`.
- **Hypotheses**: `0 < ε < r`.
- **Uses from project**: []
- **Used by**: `pv_sector_cutoff_eq`
- **Visibility**: public
- **Lines**: 316–343
- **Notes**: >10 lines; key step `intervalIntegral.integral_comp_sub_left` to relate seg3 to seg1.

### `private theorem pv_cutoff_F_integrable_0_delta`
- **Type**: `(r : ℝ) (hr : 0 < r) (α ε : ℝ) (hε : 0 < ε) (hεr : ε < r) : let F := ...; IntervalIntegrable F volume 0 (ε / r)`
- **What**: The cutoff integrand `F` is interval integrable on `[0, ε/r]` (where it is identically `0`).
- **How**: Compare with `intervalIntegrable_const 0` via `.congr`; show on `uIoc 0 δ`, `F = 0` because `‖σ‖ = t·r ≤ δ·r = ε`, so the `if`-condition is false (use `not_lt.mpr`, `mul_le_mul_of_nonneg_right ht.2 hr.le`, `field_simp`).
- **Hypotheses**: `0 < r`, `0 < ε < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_norm_seg1`
- **Used by**: `pv_sector_cutoff_base_integrabilities`
- **Visibility**: private
- **Lines**: 345–364

### `private theorem pv_cutoff_F_integrable_3delta_3`
- **Type**: `(r : ℝ) (hr : 0 < r) (α ε : ℝ) (hε : 0 < ε) (hεr : ε < r) : let F := ...; IntervalIntegrable F volume (3 - ε / r) 3`
- **What**: `F` is integrable on `[3 - ε/r, 3]` (where it is identically `0`).
- **How**: Mirror of `pv_cutoff_F_integrable_0_delta` using `sectorCurve_norm_seg3'`; `(3 - t) · r ≤ δ · r = ε`.
- **Hypotheses**: `0 < r`, `0 < ε < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_norm_seg3'`
- **Used by**: `pv_sector_cutoff_base_integrabilities`
- **Visibility**: private
- **Lines**: 366–388

### `private theorem pv_cutoff_F_integrable_delta_1`
- **Type**: `(r : ℝ) (hr : 0 < r) (α ε : ℝ) (hε : 0 < ε) (hεr : ε < r) : let F := ...; IntervalIntegrable F volume (ε / r) 1`
- **What**: `F` is integrable on `[ε/r, 1]` (where it equals `↑(t⁻¹)`).
- **How**: On `Ioo δ 1`, prove `F = ↑(t⁻¹)` via `pv_integrand_seg1` (after verifying the `if` condition via `sectorCurve_norm_seg1`). Integrability of `↑(t⁻¹)` follows from `ContinuousOn`-continuity. Lift to interval integrable via `Measure.restrict_congr_set Ioo_ae_eq_Ioc`.
- **Hypotheses**: `0 < r`, `0 < ε < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_norm_seg1`, `pv_integrand_seg1`
- **Used by**: `pv_sector_cutoff_base_integrabilities`
- **Visibility**: private
- **Lines**: 390–425
- **Notes**: >10 lines; key step `Integrable.congr` of a measurable function equal a.e. to `↑(t⁻¹)`.

### `private theorem pv_cutoff_F_integrable_1_2`
- **Type**: `(r : ℝ) (hr : 0 < r) (α ε : ℝ) (_hε : 0 < ε) (hεr : ε < r) : let F := ...; IntervalIntegrable F volume 1 2`
- **What**: `F` is integrable on `[1, 2]` (where it equals `I · α`).
- **How**: On `Ioo 1 2`, `F = I·α` (compute curve and deriv via `sectorCurve_seg2`, `deriv_sectorCurve_seg2`; `field_simp`); use `intervalIntegrable_const` for `I·α`; `Integrable.congr` and `Measure.restrict_congr_set Ioo_ae_eq_Ioc`.
- **Hypotheses**: `0 < r`, `ε < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg2`, `deriv_sectorCurve_seg2`
- **Used by**: `pv_sector_cutoff_base_integrabilities`
- **Visibility**: private
- **Lines**: 427–458
- **Notes**: >10 lines.

### `private theorem pv_cutoff_F_integrable_2_3delta`
- **Type**: `(r : ℝ) (hr : 0 < r) (α ε : ℝ) (hε : 0 < ε) (hεr : ε < r) : let F := ...; IntervalIntegrable F volume 2 (3 - ε / r)`
- **What**: `F` is integrable on `[2, 3 - ε/r]` (where it equals `-↑((3 - t)⁻¹)`).
- **How**: On `Ioo 2 (3 - δ)`, compute `F = -↑((3 - t)⁻¹)` via `sectorCurve_seg3`, `deriv_sectorCurve_seg3` and `field_simp`; continuity of `-↑((3 - t)⁻¹)` via `ContinuousAt.continuousWithinAt`; lift to `IntervalIntegrable`.
- **Hypotheses**: `0 < r`, `0 < ε < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg3`, `deriv_sectorCurve_seg3`, `sectorCurve_norm_seg3'`
- **Used by**: `pv_sector_cutoff_base_integrabilities`
- **Visibility**: private
- **Lines**: 460–508
- **Notes**: >10 lines (~50 lines); key step `Integrable.congr` of the explicit continuous function on `Ioo`.

### `private theorem pv_sector_cutoff_base_integrabilities`
- **Type**: `(r : ℝ) (hr : 0 < r) (α ε : ℝ) (hε : 0 < ε) (hεr : ε < r) : (5 IntervalIntegrable assertions on adjacent base intervals)`
- **What**: Bundles the five base interval-integrability results for `F` on `[0, δ], [3-δ, 3], [δ, 1], [1, 2], [2, 3-δ]`.
- **How**: Combine the five preceding private lemmas as a single tuple.
- **Hypotheses**: `0 < r`, `0 < ε < r`.
- **Uses from project**: `sectorCurve`, `pv_cutoff_F_integrable_0_delta`, `pv_cutoff_F_integrable_3delta_3`, `pv_cutoff_F_integrable_delta_1`, `pv_cutoff_F_integrable_1_2`, `pv_cutoff_F_integrable_2_3delta`
- **Used by**: `pv_sector_cutoff_composed_integrabilities`, `pv_sector_cutoff_eq`
- **Visibility**: private
- **Lines**: 510–525

### `private lemma intervalIntegrable_union_adjacent`
- **Type**: `{f : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (h1 : IntervalIntegrable f volume a b) (h2 : IntervalIntegrable f volume b c) : IntervalIntegrable f volume a c`
- **What**: Glue adjacent interval integrabilities `[a, b]` and `[b, c]` into `[a, c]`.
- **How**: Unfold `intervalIntegrable_iff`; use `uIoc_of_le` on each; cover `uIoc a c` by union of the two via case split on `t ≤ b`.
- **Hypotheses**: `a ≤ b ≤ c`, integrability on both pieces.
- **Uses from project**: []
- **Used by**: `pv_sector_cutoff_composed_integrabilities`
- **Visibility**: private
- **Lines**: 527–539

### `private theorem pv_sector_cutoff_composed_integrabilities`
- **Type**: `(r : ℝ) (hr : 0 < r) (α ε : ℝ) (hε : 0 < ε) (hεr : ε < r) : (IntervalIntegrable F vol 0 1 ∧ ... 0 2 ∧ ... 0 (3 - δ))`
- **What**: Chains adjacent base integrabilities into integrability on `[0, 1]`, `[0, 2]`, `[0, 3 - δ]`.
- **How**: Three applications of `intervalIntegrable_union_adjacent` starting from `pv_sector_cutoff_base_integrabilities`.
- **Hypotheses**: `0 < r`, `0 < ε < r`.
- **Uses from project**: `sectorCurve`, `pv_sector_cutoff_base_integrabilities`, `intervalIntegrable_union_adjacent`
- **Used by**: `pv_sector_cutoff_eq`
- **Visibility**: private
- **Lines**: 541–560

### `private theorem pv_cutoff_integral_seg1_eq_inv`
- **Type**: `(r : ℝ) (hr : 0 < r) (α ε : ℝ) (hε : 0 < ε) (hεr : ε < r) : let F := ...; ∫ t in (ε/r)..1, F t = ∫ t in (ε/r)..1, ↑(t⁻¹)`
- **What**: The cutoff integral on `[δ, 1]` equals the elementary integral of `1/t`.
- **How**: A.e. on `Ioo δ 1`, `F = ↑(t⁻¹)` (use `sectorCurve_seg1`, `deriv_sectorCurve_seg1`, `sectorCurve_norm_seg1` to verify cutoff `if`-condition); `intervalIntegral.integral_congr_ae` via `Ioo_ae_eq_Ioc`.
- **Hypotheses**: `0 < r`, `0 < ε < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg1`, `deriv_sectorCurve_seg1`, `sectorCurve_norm_seg1`
- **Used by**: `pv_sector_cutoff_eq`
- **Visibility**: private
- **Lines**: 562–591
- **Notes**: >10 lines.

### `private theorem pv_cutoff_integral_seg2_eq_Ialpha`
- **Type**: `(r : ℝ) (hr : 0 < r) (α ε : ℝ) (_hε : 0 < ε) (hεr : ε < r) : let F := ...; ∫ t in 1..2, F t = I * ↑α`
- **What**: The cutoff integral on `[1, 2]` is exactly `I · α`.
- **How**: A.e. on `Ioo 1 2`, `F = I·α` (verify cutoff using `sectorCurve_seg2`); `intervalIntegral.integral_congr_ae` + `intervalIntegral.integral_const`; `norm_num` for `(2 - 1) · (I·α) = I·α`.
- **Hypotheses**: `0 < r`, `ε < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg2`, `deriv_sectorCurve_seg2`
- **Used by**: `pv_sector_cutoff_eq`
- **Visibility**: private
- **Lines**: 593–620
- **Notes**: >10 lines; uses `Ioo_ae_eq_Ioc`.

### `private theorem pv_cutoff_integral_seg3_eq_neg_inv`
- **Type**: `(r : ℝ) (hr : 0 < r) (α ε : ℝ) (hε : 0 < ε) (hεr : ε < r) : let F := ...; ∫ t in 2..(3 - ε/r), F t = ∫ t in 2..(3 - ε/r), -(↑((3 - t)⁻¹))`
- **What**: The cutoff integral on `[2, 3 - δ]` equals the elementary integral of `-1/(3 - t)`.
- **How**: A.e. on `Ioo 2 (3 - δ)`, `F = -↑((3 - t)⁻¹)` (use `sectorCurve_seg3`, `deriv_sectorCurve_seg3`, `sectorCurve_norm_seg3'`); `intervalIntegral.integral_congr_ae` via `Ioo_ae_eq_Ioc`.
- **Hypotheses**: `0 < r`, `0 < ε < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_seg3`, `deriv_sectorCurve_seg3`, `sectorCurve_norm_seg3'`
- **Used by**: `pv_sector_cutoff_eq`
- **Visibility**: private
- **Lines**: 622–657
- **Notes**: >10 lines.

### `theorem pv_sector_cutoff_eq`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ) (hε : 0 < ε) (hεr : ε < r) : ∫ t in 0..3, (if ‖σ - 0‖ > ε then σ⁻¹ · σ' else 0) = I · α`
- **What**: For `0 < ε < r`, the cutoff `dz/z`-integral along the sector curve equals `I · α`.
- **How**: Obtain all base + composed integrabilities. Show the trimmed pieces on `[0, δ]` and `[3 - δ, 3]` vanish (constant zero inside the disk via `sectorCurve_norm_seg1/3'`). Compute the three middle pieces with `pv_cutoff_integral_seg1_eq_inv`, `pv_cutoff_integral_seg2_eq_Ialpha`, `pv_cutoff_integral_seg3_eq_neg_inv`. Split the total integral into the five pieces via three `intervalIntegral.integral_add_adjacent_intervals` applications; close via `log_cancellation` and `linear_combination`.
- **Hypotheses**: `0 < r`, `0 < ε < r`.
- **Uses from project**: `sectorCurve`, `sectorCurve_norm_seg1`, `sectorCurve_norm_seg3'`, `pv_sector_cutoff_base_integrabilities`, `pv_sector_cutoff_composed_integrabilities`, `pv_cutoff_integral_seg1_eq_inv`, `pv_cutoff_integral_seg2_eq_Ialpha`, `pv_cutoff_integral_seg3_eq_neg_inv`, `log_cancellation`
- **Used by**: `pv_sector_dz_over_z`
- **Visibility**: public
- **Lines**: 661–716
- **Notes**: >10 lines (~55 lines); key step the `intervalIntegral.integral_add_adjacent_intervals` chain.

### `theorem pv_sector_dz_over_z`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (_hα_nonneg : 0 ≤ α) (_hα_le : α ≤ 2π) : CauchyPrincipalValueExists' (fun z => z⁻¹) (sectorCurve r α) 0 3 0 ∧ cauchyPrincipalValue' (fun z => z⁻¹) (sectorCurve r α) 0 3 0 = I * ↑α`
- **What**: HW Lemma 3.1 (`dz/z` part): the principal value along the sector curve exists and equals `I · α`.
- **How**: For `ε ∈ (0, r)`, `pv_sector_cutoff_eq` gives the cutoff integral is `I·α`; lift to `Tendsto ... (𝓝 (I·α))` via `tendsto_const_nhds.congr'` with `eventually_nhdsWithin_iff` + `Iio_mem_nhds hr`; existence is `⟨I·α, h_tendsto⟩`; value is `h_tendsto.limUnder_eq`.
- **Hypotheses**: `0 < r`, `0 ≤ α ≤ 2π` (auxiliary, not used in proof).
- **Uses from project**: `sectorCurve`, `CauchyPrincipalValueExists'`, `cauchyPrincipalValue'`, `pv_sector_cutoff_eq`
- **Used by**: unused in file (final API endpoint)
- **Visibility**: public
- **Lines**: 722–744
- **Notes**: >10 lines.

---

## File Summary
- **Totals**: 33 declarations (1 def + 32 theorems/lemmas).
- **Key API**: `sectorCurve` (the model curve); `pv_sector_dz_over_z` (HW Lemma 3.1 `dz/z`-part); the structural lemmas `sectorCurve_seg1/2/3`, `sectorCurve_continuousOn`, `deriv_sectorCurve_seg1/2/3`, `pv_integrand_seg1/2/3`, `log_cancellation`, and `pv_sector_cutoff_eq`.
- **Unused in file**: `sectorCurve_closed`, `sectorCurve_one`, `sectorCurve_two`, `sectorCurve_continuousOn`, `sectorCurve_passes_through_origin`, `sectorCurve_norm_on_arc`, `pv_integrand_seg2`, `pv_integrand_seg3`, `integral_seg1_eq_neg_log`, `integral_seg3_eq_log`, `pv_sector_dz_over_z` (these are external/structural API endpoints).
- **Sorries**: none.
- **`set_option`s**: none.
- **Long proofs (>10 lines)**: `sectorCurve_continuousOn`, `deriv_sectorCurve_seg2`, `deriv_sectorCurve_seg3`, `log_cancellation`, `pv_cutoff_F_integrable_delta_1`, `pv_cutoff_F_integrable_1_2`, `pv_cutoff_F_integrable_2_3delta`, `pv_cutoff_integral_seg1_eq_inv`, `pv_cutoff_integral_seg2_eq_Ialpha`, `pv_cutoff_integral_seg3_eq_neg_inv`, `pv_sector_cutoff_eq` (~55 lines), `pv_sector_dz_over_z`.
- **Purpose**: Builds the model sector-curve `σ_{r,α}` (radial-out, circular arc of angle `α` at radius `r`, radial-back) on `[0, 3]` and proves Hungerbuhler-Wasem Lemma 3.1 (the `dz/z`-part): the Cauchy principal value of `1/z` along the sector curve equals `I · α`. The proof structure: explicit closed forms on the three segments and their derivatives; PV cutoff integrand simplifies to `1/t`, `i·α`, `-1/(3-t)` on the three open segments. The two logarithmic divergences from the radial segments cancel exactly after rescaling `ε ↦ ε/r` (`log_cancellation`), leaving the arc contribution `∫_0^α i dθ = i·α`. A scaffolding of five interval integrability lemmas (the `pv_cutoff_F_integrable_*` family) plus an adjacent-union helper lets the final telescoping (`pv_sector_cutoff_eq`) split the integral into the five base pieces. The final `pv_sector_dz_over_z` packages the result as a `CauchyPrincipalValueExists'` + value statement for downstream consumption.
