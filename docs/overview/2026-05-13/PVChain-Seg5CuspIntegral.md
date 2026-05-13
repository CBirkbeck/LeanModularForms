# Inventory: PVChain/Seg5CuspIntegral.lean

### `private lemma eball_one_eq_ball`
- **Type**: `{F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F (Metric.eball 0 1)) : AnalyticOnNhd ℂ F (Metric.ball 0 1)`
- **What**: Convert analyticity on the extended `eball 0 1` to the metric `ball 0 1`.
- **How**: `hF.mono` with `Metric.mem_eball/mem_ball` and `ENNReal.coe_lt_one_iff` (`exact_mod_cast`).
- **Hypotheses**: `F` analytic on the extended-ball.
- **Uses from project**: []
- **Used by**: `qExpFMS_ne_zero`, `cuspFunction_factored`
- **Visibility**: private
- **Lines**: 49–54

### `private lemma qExpFMS_ne_zero`
- **Type**: `(hf : f ≠ 0) : ModularFormClass.qExpansionFormalMultilinearSeries 1 f ≠ 0`
- **What**: For nonzero modular form `f`, the FMS of the q-expansion is nonzero.
- **How**: By contradiction. If FMS = 0, `ModularFormClass.hasFPowerSeries_cuspFunction` becomes a zero power series, so `cuspFunction` is `EqOn 0` on `Metric.ball 0 1` (analytic continuation: `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` on `convex_ball 0 1`). Then `SlashInvariantFormClass.eq_cuspFunction` + `τ.norm_qParam_lt_one 1` give `f τ = 0` for all `τ`, contradicting `hf` via `ModularForm.ext`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `ModularFormClass.qExpansionFormalMultilinearSeries`, `ModularFormClass.hasFPowerSeries_cuspFunction`, `ModularFormClass.one_mem_strictPeriods_SL2Z`, `SlashInvariantFormClass.cuspFunction`, `SlashInvariantFormClass.eq_cuspFunction`, `eball_one_eq_ball`, `UpperHalfPlane.norm_qParam_lt_one`
- **Used by**: `qExpFMS_order_eq`, `cuspFunction_factored`
- **Visibility**: private
- **Lines**: 56–76
- **Notes**: 21 lines.

### `private lemma qExpFMS_order_eq`
- **Type**: `(hf : f ≠ 0) : (ModularFormClass.qExpansionFormalMultilinearSeries 1 f).order = (orderAtCusp' f).toNat`
- **What**: The FMS order matches `(orderAtCusp' f).toNat`.
- **How**: Set `p := qExpansionFormalMultilinearSeries 1 f`, `ps := qExpansion 1 f`. Establish bijection `p n = 0 ↔ ps.coeff n = 0` via `ModularFormClass.qExpansionFormalMultilinearSeries_apply_norm` and `norm_eq_zero`. Show `ps ≠ 0` (using `qExpFMS_ne_zero` and `FormalMultilinearSeries.ext`). Convert `ps.order` to `(ps.order.toNat : ℕ∞)` via `ENat.coe_toNat_eq_self.mpr (PowerSeries.order_eq_top.not.mpr hps_ne)`. Use `PowerSeries.order_eq_nat` to get `ps.coeff m ≠ 0` and `∀ i < m, ps.coeff i = 0`. Conclude `p.order = m` via `le_antisymm`: `Nat.sInf_le` for `m ∈ {n | p n ≠ 0}`, and `by_contra; Nat.sInf_mem` for the reverse.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `ModularFormClass.qExpansionFormalMultilinearSeries`, `ModularFormClass.qExpansion`, `ModularFormClass.qExpansionFormalMultilinearSeries_apply_norm`, `orderAtCusp'`, `qExpFMS_ne_zero`
- **Used by**: `cuspFunction_factored`
- **Visibility**: private
- **Lines**: 79–116
- **Notes**: 38 lines.

### `private lemma cuspFunction_factored`
- **Type**: `(hf : f ≠ 0) : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball 0 1) ∧ g 0 ≠ 0 ∧ ∀ q ∈ Metric.ball 0 1, SlashInvariantFormClass.cuspFunction 1 f q = q ^ (orderAtCusp' f).toNat * g q`
- **What**: Factorization `cuspFunction = q^m · g` on `ball 0 1` with `g` differentiable and `g(0) ≠ 0`.
- **How**: Set `F := cuspFunction 1 f`, `p := FMS`, `g₀ := (Function.swap dslope 0)^[p.order] F`. `hp.iterate_dslope_fslope_ne_zero hp_ne` gives `g₀ 0 ≠ 0`. `hp.eq_pow_order_mul_iterate_dslope` gives `F z = (z - 0)^p.order • g₀ z` eventually near 0. Show `g₀ differentiableOn ball 0 1` by induction on `k`, using `Complex.differentiableOn_dslope hball_nhds` for the successor step. Lift the local equality to the whole ball via `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` on `Convex.isPreconnected (convex_ball 0 1)`. Refine with `simp only [sub_zero, smul_eq_mul]; rw [this, hp_order]`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `SlashInvariantFormClass.cuspFunction`, `ModularFormClass.qExpansionFormalMultilinearSeries`, `ModularFormClass.hasFPowerSeries_cuspFunction`, `ModularFormClass.one_mem_strictPeriods_SL2Z`, `qExpFMS_ne_zero`, `qExpFMS_order_eq`, `eball_one_eq_ball`, `orderAtCusp'`
- **Used by**: `circleIntegral_logDeriv_cuspFunction_of_radius`
- **Visibility**: private
- **Lines**: 120–166
- **Notes**: 47 lines.

### `private lemma circleIntegral_const_mul_inv`
- **Type**: `(m : ℂ) {R : ℝ} (hR : R ≠ 0) : (∮ q in C(0, R), m * q⁻¹) = m * (2 * ↑Real.pi * I)`
- **What**: Circle integral of `m/q` around 0 of nonzero radius equals `2πim`.
- **How**: `circleIntegral.integral_const_mul`, rewrite `q⁻¹ = (q - 0)⁻¹`, apply `circleIntegral.integral_sub_center_inv 0 hR`.
- **Hypotheses**: `R ≠ 0`.
- **Uses from project**: []
- **Used by**: `circleIntegral_logDeriv_cuspFunction_of_radius`
- **Visibility**: private, `omit f hf`
- **Lines**: 171–179

### `private lemma circleIntegral_logDeriv_regular_zero`
- **Type**: `(g : ℂ → ℂ) {R : ℝ} (hR_pos : 0 < R) (hR_lt : R < 1) (hg_diff : DifferentiableOn ℂ g (Metric.ball 0 1)) (hg_nonvan : ∀ q ∈ Metric.closedBall 0 R, g q ≠ 0) : (∮ q in C(0, R), logDeriv g q) = 0`
- **What**: Circle integral of `logDeriv g = g'/g` around 0 is zero when `g` is differentiable and non-vanishing on `closedBall 0 R`.
- **How**: `ContinuousOn (logDeriv g)` on `closedBall 0 R` via `ContinuousOn.div` of `deriv g` (from `hg_diff.contDiffOn.continuousOn_deriv_of_isOpen`) and `g` (from `hg_diff.continuousOn`), divided by `hg_nonvan`. Differentiability at every `z ∈ ball 0 R` similarly. Apply `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR_le Set.countable_empty hg_cont`.
- **Hypotheses**: `0 < R < 1`, `g` differentiable on `ball 0 1`, `g` non-vanishing on `closedBall 0 R`.
- **Uses from project**: []
- **Used by**: `circleIntegral_logDeriv_cuspFunction_of_radius`
- **Visibility**: private, `omit f hf`
- **Lines**: 185–210
- **Notes**: 26 lines.

### `lemma seg5_q_radius_H_pos`
- **Type**: `(H : ℝ) : 0 < seg5_q_radius_H H`
- **What**: q-radius along seg5 is always positive.
- **How**: `Real.exp_pos _` (since `seg5_q_radius_H H = exp(...)`).
- **Hypotheses**: none.
- **Uses from project**: `seg5_q_radius_H`
- **Used by**: `seg5_logDeriv_integral_eq_H`
- **Visibility**: public, `omit f hf`
- **Lines**: 216–217

### `private lemma seg5_q_radius_H_lt_one'`
- **Type**: `{H : ℝ} (hH : 0 < H) : seg5_q_radius_H H < 1`
- **What**: q-radius along seg5 is `< 1` for `H > 0`.
- **How**: `Real.exp_lt_one_iff.mpr (nlinarith [Real.pi_pos])` (since `seg5_q_radius_H H = exp(-2πH) < 1` for `H > 0`).
- **Hypotheses**: `0 < H`.
- **Uses from project**: `seg5_q_radius_H`
- **Used by**: `seg5_logDeriv_integral_eq_H`
- **Visibility**: private, `omit f hf`
- **Lines**: 221–222

### `lemma circleIntegral_logDeriv_cuspFunction_of_radius`
- **Type**: `(hf : f ≠ 0) {R : ℝ} (hR_pos : 0 < R) (hR_lt : R < 1) (hcusp_nonvan : ∀ q ∈ Metric.closedBall 0 R, q ≠ 0 → cuspFunction 1 f q ≠ 0) : (∮ q in C(0, R), logDeriv (cuspFunction 1 f) q) = 2 * ↑Real.pi * I * ↑(orderAtCusp' f)`
- **What**: Circle integral of `logDeriv(cuspFunction)` at any radius `0 < R < 1` equals `2πi · orderAtCusp' f`.
- **How**: Use `cuspFunction_factored` to write `F = q^m · g` with `g` differentiable and non-vanishing on `closedBall 0 R` (`hcusp_nonvan` + `right_ne_zero_of_mul`). For each `q` on the sphere of radius `R`, derive `logDeriv F q = m/q + logDeriv g q`: from `F =ᶠ[𝓝 q] z ↦ z^m · g z` (via `Metric.isOpen_ball.eventually_mem`), then `(hasDerivAt_pow m q).mul ((hg_diff.differentiableAt ...).hasDerivAt).deriv` gives the explicit derivative; `field_simp` + `rcases m` + `Nat.succ_sub_one` and `ring`. `CircleIntegrable` of `m · q⁻¹` and `logDeriv g` separately, then `intervalIntegral.integral_congr` + `circleIntegral.integral_add hci_inv hci_logDeriv` + `circleIntegral_const_mul_inv (↑m) (ne_of_gt hR_pos)` + `circleIntegral_logDeriv_regular_zero g hR_pos hR_lt hg_diff hg_nonvan` + `add_zero`. Finally `(↑m : ℂ) = ↑(orderAtCusp' f)` via `push_cast [Int.toNat_natCast]`.
- **Hypotheses**: `f ≠ 0`, `0 < R < 1`, `cuspFunction` non-vanishing on `closedBall 0 R` except at 0.
- **Uses from project**: `SlashInvariantFormClass.cuspFunction`, `orderAtCusp'`, `cuspFunction_factored`, `circleIntegral_const_mul_inv`, `circleIntegral_logDeriv_regular_zero`
- **Used by**: `seg5_logDeriv_integral_eq_H`
- **Visibility**: public
- **Lines**: 230–311
- **Notes**: 82 lines.

### `private lemma qParam_seg5_H_eq_circleMap`
- **Type**: `(H : ℝ) (t : ℝ) : Function.Periodic.qParam (1 : ℝ) (fdBoundary_seg5_H H t) = circleMap 0 (seg5_q_radius_H H) (2 * Real.pi * (t - 9 / 2))`
- **What**: The q-parameter along seg5 at height `H` equals a circleMap value.
- **How**: `simp only` unfolds `qParam`, `fdBoundary_seg5_H`, `seg5_q_radius_H`, `circleMap_zero`. Rewrite the exponent algebraically using `linear_combination` against `I_sq` (`I^2 = -1`), then `Complex.exp_add` + `Complex.ofReal_exp`.
- **Hypotheses**: none.
- **Uses from project**: `Function.Periodic.qParam`, `fdBoundary_seg5_H`, `seg5_q_radius_H`
- **Used by**: `seg5_integral_eq_circleIntegral_H`
- **Visibility**: private, `omit f hf`
- **Lines**: 318–328

### `private lemma im_fdBoundary_seg5_H_pos`
- **Type**: `{H : ℝ} (hH : 0 < H) (t : ℝ) : 0 < (fdBoundary_seg5_H H t).im`
- **What**: The seg5 height has positive imaginary part when `H > 0`.
- **How**: `change` to expose `(t - 9/2 + H·I).im`, `simp [add_im, mul_im, ...]`, `linarith`.
- **Hypotheses**: `0 < H`.
- **Uses from project**: `fdBoundary_seg5_H`
- **Used by**: `logDeriv_modularForm_eq_logDeriv_cuspFn_mul_qderiv_H`
- **Visibility**: private, `omit f hf`
- **Lines**: 331–335

### `private lemma logDeriv_modularForm_eq_logDeriv_cuspFn_mul_qderiv_H`
- **Type**: `{H : ℝ} (hH : 0 < H) (t : ℝ) : logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5_H H t) = logDeriv (cuspFunction 1 f) (Function.Periodic.qParam 1 (fdBoundary_seg5_H H t)) * (2 * ↑Real.pi * I * Function.Periodic.qParam 1 (fdBoundary_seg5_H H t))`
- **What**: Chain rule for `logDeriv` along seg5: `logDeriv(f∘ofC)(z) = logDeriv(cuspFn)(q(z)) · 2πi·q(z)`.
- **How**: Set `z := fdBoundary_seg5_H H t`, `F := cuspFunction 1 f`, `q_fn := Periodic.qParam 1`. Show `modularFormCompOfComplex f = F ∘ q_fn` eventually near `z` by combining `UpperHalfPlane.ofComplex_apply_of_im_pos` with `SlashInvariantFormClass.eq_cuspFunction`. `‖q_fn z‖ < 1` via `Function.Periodic.norm_qParam` + `Real.exp_lt_one_iff` + `im_fdBoundary_seg5_H_pos`. `F` differentiable at `q_fn z` via `ModularFormClass.differentiableAt_cuspFunction`. Apply `logDeriv_comp hF_diff hq_diff` then compute `deriv q_fn z` directly: rewrite `q_fn = fun z => cexp(2πi·z)`, `HasDerivAt.cexp.deriv`, `ring`.
- **Hypotheses**: `0 < H`.
- **Uses from project**: `modularFormCompOfComplex`, `Function.Periodic.qParam`, `Function.Periodic.norm_qParam`, `Function.Periodic.differentiable_qParam`, `SlashInvariantFormClass.cuspFunction`, `SlashInvariantFormClass.eq_cuspFunction`, `ModularFormClass.differentiableAt_cuspFunction`, `ModularFormClass.one_mem_strictPeriods_SL2Z`, `UpperHalfPlane.ofComplex_apply_of_im_pos`, `UpperHalfPlane.isOpen_upperHalfPlaneSet`, `fdBoundary_seg5_H`, `im_fdBoundary_seg5_H_pos`
- **Used by**: `seg5_integral_eq_circleIntegral_H`
- **Visibility**: private, `omit hf`
- **Lines**: 340–387
- **Notes**: 48 lines.

### `lemma seg5_integral_eq_circleIntegral_H`
- **Type**: `{H : ℝ} (hH : 0 < H) : ∫ t in (4:ℝ)..5, logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5_H H t) = ∮ q in C(0, seg5_q_radius_H H), logDeriv (cuspFunction 1 f) q`
- **What**: **Stage 1**: change of variables from the seg5 parametric logDeriv integral to a circle integral in the q-plane.
- **How**: `simp_rw [logDeriv_modularForm_eq_logDeriv_cuspFn_mul_qderiv_H f hH]` and `simp_rw [qParam_seg5_H_eq_circleMap H]` rewrite the integrand on the right. Set `g θ := deriv (circleMap 0 R) θ • logDeriv F (circleMap 0 R θ)`. Show `integrand = (2π : ℝ) • g(2π(t - 9/2))` via `erw [deriv_circleMap]`, `Complex.real_smul`, `push_cast; ring`. Then `intervalIntegral.integral_smul` + `intervalIntegral.integral_comp_mul_add` (with `hpi_ne := positivity`), shifting the limits to `[-π, π]`. Use `Function.Periodic.intervalIntegral_add_eq` (`g` has period `2π` via `periodic_circleMap`) to shift `[-π, 0]` to `[π, 2π]`, yielding `[0, 2π]`-type integrand, which unfolds to `circleIntegral` definitionally (`rfl`).
- **Hypotheses**: `0 < H`.
- **Uses from project**: `modularFormCompOfComplex`, `SlashInvariantFormClass.cuspFunction`, `fdBoundary_seg5_H`, `seg5_q_radius_H`, `logDeriv_modularForm_eq_logDeriv_cuspFn_mul_qderiv_H`, `qParam_seg5_H_eq_circleMap`
- **Used by**: `seg5_logDeriv_integral_eq_H`
- **Visibility**: public, `omit hf`
- **Lines**: 392–434
- **Notes**: 43 lines.

### `lemma seg5_logDeriv_integral_eq_H`
- **Type**: `(hf : f ≠ 0) {H : ℝ} (hH : 0 < H) (hcusp_nonvan : ∀ q ∈ Metric.closedBall 0 (seg5_q_radius_H H), q ≠ 0 → cuspFunction 1 f q ≠ 0) : ∫ t in (4:ℝ)..5, logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5_H H t) = 2 * ↑Real.pi * I * ↑(orderAtCusp' f)`
- **What**: Combination of Stages 1 + 2 at height `H`: seg5 logDeriv integral = `2πi · orderAtCusp' f`.
- **How**: `seg5_integral_eq_circleIntegral_H f hH` + `circleIntegral_logDeriv_cuspFunction_of_radius f hf (seg5_q_radius_H_pos H) (seg5_q_radius_H_lt_one' hH) hcusp_nonvan`.
- **Hypotheses**: `f ≠ 0`, `0 < H`, `cuspFunction` non-vanishing on `closedBall 0 R` except at 0.
- **Uses from project**: `seg5_integral_eq_circleIntegral_H`, `circleIntegral_logDeriv_cuspFunction_of_radius`, `seg5_q_radius_H_pos`, `seg5_q_radius_H_lt_one'`, `modularFormCompOfComplex`, `SlashInvariantFormClass.cuspFunction`, `fdBoundary_seg5_H`, `seg5_q_radius_H`, `orderAtCusp'`
- **Used by**: `seg5_logDeriv_integral_value_bridge`
- **Visibility**: public
- **Lines**: 438–446

### `theorem seg5_logDeriv_integral_value_bridge`
- **Type**: `{H : ℝ} (hH : Real.sqrt 3 / 2 < H) (hcusp_nonvan : ∀ q ∈ Metric.closedBall 0 (seg5_q_radius_H H), q ≠ 0 → cuspFunction 1 f q ≠ 0) : ∫ t in (4:ℝ)..5, logDeriv (modularFormCompOfComplex f) (fdBoundary_H H t) * deriv (fdBoundary_H H) t = 2 * ↑Real.pi * I * (orderAtCusp' f : ℂ)`
- **What**: **Bridge to `PVChain.Assembly`**: seg5 integral with `· deriv (fdBoundary_H H) t` matches `2πi · orderAtCusp' f`.
- **How**: Use `Real.sqrt 3 / 2 < H` ⟹ `0 < H`. Establish `h_eq_ae` (AE-equality of integrands on `uIoc 4 5`): for `4 < t`, `fdBoundary_H H t = fdBoundary_seg5_H H t` (`fdBoundary_H_eq_seg5_H`) and `deriv (fdBoundary_H H) t = 1` (`fdBoundary_H_hasDerivAt_seg5 H ht4).deriv`, then `mul_one`). `calc` step: `intervalIntegral.integral_congr_ae h_eq_ae` then `seg5_logDeriv_integral_eq_H f hf hH_pos hcusp_nonvan`.
- **Hypotheses**: `f ≠ 0` (from outer `include hf`), `Real.sqrt 3 / 2 < H`, `cuspFunction` non-vanishing on `closedBall 0 (seg5_q_radius_H H)` except at 0.
- **Uses from project**: `seg5_logDeriv_integral_eq_H`, `modularFormCompOfComplex`, `SlashInvariantFormClass.cuspFunction`, `fdBoundary_H`, `fdBoundary_H_eq_seg5_H`, `fdBoundary_H_hasDerivAt_seg5`, `seg5_q_radius_H`, `orderAtCusp'`
- **Used by**: unused in file
- **Visibility**: public, `include hf`
- **Lines**: 459–487
- **Notes**: 29 lines.

## File Summary
Cusp-function machinery for seg5 of the valence formula contour. Two-stage strategy: (Stage 1) `seg5_integral_eq_circleIntegral_H` change-of-variables to a `q`-plane circle integral via `qParam_seg5_H_eq_circleMap`, chain-rule `logDeriv_modularForm_eq_logDeriv_cuspFn_mul_qderiv_H`, periodicity of circleMap, and integral-substitution to align bounds `(-π, π)`; (Stage 2) `circleIntegral_logDeriv_cuspFunction_of_radius` factors `cuspFunction = q^m · g` via `cuspFunction_factored` (using `iterate_dslope_fslope_ne_zero` + `eq_pow_order_mul_iterate_dslope`), and the integral reduces to `m · 2πi + 0` via `circleIntegral_const_mul_inv` + `circleIntegral_logDeriv_regular_zero` (Cauchy-Goursat). Combined `seg5_logDeriv_integral_eq_H` and bridge `seg5_logDeriv_integral_value_bridge` for use in `PVChain.Assembly`. Uses `attribute [local instance] Classical.propDecidable`. 0 sorry, no `set_option`, no axioms.
