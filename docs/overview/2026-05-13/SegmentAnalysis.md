# Inventory: SegmentAnalysis.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/SegmentAnalysis.lean`
Lines: 466

### `private lemma gamma_eventuallyEq`
- **Type**: `{H} {γ : PiecewiseC1Path (fdStart H) (fdStart H)} (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) {t} (ht : t ∈ Ioo 0 1) : γ.toPath.extend =ᶠ[𝓝 t] fdBoundaryFun H`
- **What**: On `(0,1)`, `γ.toPath.extend` and `fdBoundaryFun H` agree in a neighborhood of any interior `t`
- **How**: `Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2)` with the pointwise hypothesis `hγ` restricted from `Icc` to `Ioo`
- **Hypotheses**: agreement on `Icc 0 1`; `t ∈ Ioo 0 1`
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`
- **Used by**: `transfer_integrability`, `transfer_integral`
- **Visibility**: private
- **Lines**: 61-67

### `theorem transfer_integrability`
- **Type**: `{H} (z : ℂ) {a b} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1) (γ, hγ, hint : IntervalIntegrable on fdBoundaryFun-based integrand) : IntervalIntegrable on γ-based integrand`
- **What**: Transfers `IntervalIntegrable` from the `fdBoundaryFun H`-based log-derivative integrand to the `γ.toPath.extend`-based one
- **How**: `hint.congr_ae`; off the measure-zero singleton `{b}`, every `t ∈ uIoc a b` lies in `Ioo 0 1`, and `gamma_eventuallyEq` plus `EventuallyEq.deriv_eq` rewrite both `f t` and `f' t`
- **Hypotheses**: `0 ≤ a ≤ b ≤ 1`; pointwise agreement on `Icc 0 1`
- **Uses from project**: `gamma_eventuallyEq`, `fdBoundaryFun`, `PiecewiseC1Path`, `fdStart`
- **Used by**: `gamma_integrable_left_of_I`, `gamma_integrable_right_of_I`
- **Visibility**: public
- **Lines**: 70-87

### `theorem transfer_integral`
- **Type**: `{H} (z : ℂ) {a b} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1) (γ, hγ) : ∫ t in a..b, (γ.extend t - z)⁻¹ · γ.extend' t = ∫ t in a..b, (fdBoundaryFun H t - z)⁻¹ · fdBoundaryFun H' t`
- **What**: Transfers integral equality between `γ.toPath.extend`-based and `fdBoundaryFun H`-based log-derivative integrands
- **How**: `intervalIntegral.integral_congr_ae`; off the measure-zero singleton `{b}`, every `t ∈ uIoc a b` lies in `Ioo 0 1`, then `gamma_eventuallyEq.deriv_eq` and pointwise equality from `hγ`
- **Hypotheses**: `0 ≤ a ≤ b ≤ 1`; pointwise agreement on `Icc 0 1`
- **Uses from project**: `gamma_eventuallyEq`, `fdBoundaryFun`, `PiecewiseC1Path`, `fdStart`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 90-102

### `private def ref_seg1_I`
- **Type**: `(H t : ℝ) : ℂ`
- **What**: Smooth reference function on segment 1 (right vertical, `Re = 1/2`) equal to `fdBoundaryFun H t - I` for `t ≤ 1/5`
- **How**: definition `1/2 + (H - 1 - 5 t (H - √3/2)) I`
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `ref_seg1_I_contDiff`, `ref_seg1_I_slitPlane`, `fdBoundary_sub_I_eq_ref_seg1`, `fdBoundary_sub_I_eventuallyEq_ref_seg1`, `seg1_ftc_I`
- **Visibility**: private
- **Lines**: 108-109

### `private lemma ref_seg1_I_contDiff`
- **Type**: `(H : ℝ) : ContDiff ℝ ⊤ (ref_seg1_I H)`
- **What**: `ref_seg1_I H` is smooth (`C^∞`)
- **How**: built from `contDiff_const`, `contDiff_const.mul Complex.ofRealCLM.contDiff`, `.add`, `.sub`, `.mul`
- **Hypotheses**: none
- **Uses from project**: `ref_seg1_I`
- **Used by**: `seg1_ftc_I`
- **Visibility**: private
- **Lines**: 111-116

### `private lemma ref_seg1_I_slitPlane`
- **Type**: `(H : ℝ) (t : ℝ) : ref_seg1_I H t ∈ Complex.slitPlane`
- **What**: `ref_seg1_I H t` lies in the slit plane (`Re > 0` since real part is `1/2`)
- **How**: `Complex.mem_slitPlane_iff.left`; simplifies real part and `norm_num`
- **Hypotheses**: none
- **Uses from project**: `ref_seg1_I`
- **Used by**: `seg1_ftc_I`
- **Visibility**: private
- **Lines**: 118-124

### `private lemma fdBoundary_sub_I_eq_ref_seg1`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ≤ 1/5) : fdBoundaryFun H t - I = ref_seg1_I H t`
- **What**: Pointwise equality of `fdBoundaryFun H t - I` with `ref_seg1_I H t` on segment 1
- **How**: `simp [fdBoundaryFun, ht, ite_true, ref_seg1_I]` then `ring`
- **Hypotheses**: `t ≤ 1/5`
- **Uses from project**: `fdBoundaryFun`, `ref_seg1_I`
- **Used by**: `fdBoundary_sub_I_eventuallyEq_ref_seg1`, `seg1_ftc_I`
- **Visibility**: private
- **Lines**: 126-129

### `private lemma fdBoundary_sub_I_eventuallyEq_ref_seg1`
- **Type**: `(H : ℝ) {t : ℝ} (ht : t < 1/5) : (fun s => fdBoundaryFun H s - I) =ᶠ[𝓝 t] ref_seg1_I H`
- **What**: Neighborhood-eventual equality near `t < 1/5`
- **How**: `Filter.eventually_of_mem (Iio_mem_nhds ht)` plus the pointwise equality
- **Hypotheses**: `t < 1/5`
- **Uses from project**: `fdBoundaryFun`, `ref_seg1_I`, `fdBoundary_sub_I_eq_ref_seg1`
- **Used by**: `seg1_ftc_I`
- **Visibility**: private
- **Lines**: 131-134

### `private def ref_seg4_I`
- **Type**: `(H t : ℝ) : ℂ`
- **What**: Smooth reference function on segment 4 (left vertical, `Re = -1/2`)
- **How**: definition `-1/2 + (√3/2 - 1 + (5t - 3)(H - √3/2)) I`
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `ref_seg4_I_contDiff`, `ref_seg4_I_ne_zero`, `ref_seg4_I_neg_slitPlane`, `fdBoundary_sub_I_eventuallyEq_ref_seg4`, `seg4_full_intervalIntegrable_I`
- **Visibility**: private
- **Lines**: 138-139

### `private lemma ref_seg4_I_contDiff`
- **Type**: `(H : ℝ) : ContDiff ℝ ⊤ (ref_seg4_I H)`
- **What**: `ref_seg4_I H` is smooth
- **How**: combines `contDiff_const`, `Complex.ofRealCLM.contDiff`, `.add/.sub/.mul`
- **Hypotheses**: none
- **Uses from project**: `ref_seg4_I`
- **Used by**: `seg4_full_intervalIntegrable_I`
- **Visibility**: private
- **Lines**: 141-146

### `private lemma ref_seg4_I_ne_zero`
- **Type**: `(H t : ℝ) : ref_seg4_I H t ≠ 0`
- **What**: `ref_seg4_I H t` is never zero (real part is `-1/2 ≠ 0`)
- **How**: assumes `= 0`, computes `re = -1/2`, derives `0 = -1/2` via `linarith`
- **Hypotheses**: none
- **Uses from project**: `ref_seg4_I`
- **Used by**: `seg4_full_intervalIntegrable_I`
- **Visibility**: private
- **Lines**: 148-157

### `private lemma ref_seg4_I_neg_slitPlane`
- **Type**: `(H t : ℝ) : -(ref_seg4_I H t) ∈ Complex.slitPlane`
- **What**: `-(ref_seg4_I H t)` lies in the slit plane (its real part is `1/2 > 0`)
- **How**: `Complex.mem_slitPlane_iff.left`; simp + `norm_num`
- **Hypotheses**: none
- **Uses from project**: `ref_seg4_I`
- **Used by**: unused in file
- **Visibility**: private
- **Lines**: 159-165

### `private lemma fdBoundary_sub_I_eventuallyEq_ref_seg4`
- **Type**: `(H : ℝ) {t : ℝ} (ht3 : 3/5 < t) (ht4 : t < 4/5) : (fun s => fdBoundaryFun H s - I) =ᶠ[𝓝 t] ref_seg4_I H`
- **What**: Neighborhood-eventual equality near segment 4 interior
- **How**: `Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht3) (Iio_mem_nhds ht4))`; in the `simp` step branches all `≤` predicates of `fdBoundaryFun` and applies `ring`
- **Hypotheses**: `3/5 < t < 4/5`
- **Uses from project**: `fdBoundaryFun`, `ref_seg4_I`
- **Used by**: `seg4_full_intervalIntegrable_I`
- **Visibility**: private
- **Lines**: 167-178

### `private def ref_seg5_I`
- **Type**: `(H t : ℝ) : ℂ`
- **What**: Smooth reference function on segment 5 (horizontal, `Im = H`)
- **How**: definition `(5t - 9/2) + (H - 1) I`
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `ref_seg5_I_contDiff`, `ref_seg5_I_slitPlane`, `ref_seg5_I_ne_zero`, `fdBoundary_sub_I_eq_ref_seg5`, `fdBoundary_sub_I_eventuallyEq_ref_seg5`, `seg5_ftc_I`, `seg5_full_intervalIntegrable_I`
- **Visibility**: private
- **Lines**: 182

### `private lemma ref_seg5_I_contDiff`
- **Type**: `(H : ℝ) : ContDiff ℝ ⊤ (ref_seg5_I H)`
- **What**: `ref_seg5_I H` is smooth
- **How**: chain of `contDiff_const`, `Complex.ofRealCLM.contDiff`, `.mul/.sub/.add`
- **Hypotheses**: none
- **Uses from project**: `ref_seg5_I`
- **Used by**: `seg5_ftc_I`, `seg5_full_intervalIntegrable_I`
- **Visibility**: private
- **Lines**: 184-186

### `private lemma ref_seg5_I_slitPlane`
- **Type**: `(H : ℝ) (hH : 1 < H) (t : ℝ) : ref_seg5_I H t ∈ Complex.slitPlane`
- **What**: `ref_seg5_I H t` is in the slit plane (`Im = H - 1 > 0`)
- **How**: `Complex.mem_slitPlane_iff.right`; `norm_num` and `linarith` using `1 < H`
- **Hypotheses**: `1 < H`
- **Uses from project**: `ref_seg5_I`
- **Used by**: `ref_seg5_I_ne_zero`, `seg5_ftc_I`
- **Visibility**: private
- **Lines**: 188-197

### `private lemma ref_seg5_I_ne_zero`
- **Type**: `(H : ℝ) (hH : 1 < H) (t : ℝ) : ref_seg5_I H t ≠ 0`
- **What**: `ref_seg5_I H t ≠ 0` for `1 < H`
- **How**: `Complex.slitPlane_ne_zero (ref_seg5_I_slitPlane H hH t)`
- **Hypotheses**: `1 < H`
- **Uses from project**: `ref_seg5_I_slitPlane`
- **Used by**: `seg5_full_intervalIntegrable_I`
- **Visibility**: private
- **Lines**: 199-200

### `private lemma fdBoundary_sub_I_eq_ref_seg5`
- **Type**: `(H : ℝ) (t : ℝ) (ht : 4/5 < t) : fdBoundaryFun H t - I = ref_seg5_I H t`
- **What**: Pointwise equality of `fdBoundaryFun H t - I` with `ref_seg5_I H t` on segment 5
- **How**: `simp [fdBoundaryFun, ...]` discharging all four negated `≤`s by `linarith`, then `ring`
- **Hypotheses**: `4/5 < t`
- **Uses from project**: `fdBoundaryFun`, `ref_seg5_I`
- **Used by**: `fdBoundary_sub_I_eventuallyEq_ref_seg5`, `seg5_ftc_I`, `seg5_full_intervalIntegrable_I`
- **Visibility**: private
- **Lines**: 202-207

### `private lemma fdBoundary_sub_I_eventuallyEq_ref_seg5`
- **Type**: `(H : ℝ) {t : ℝ} (ht : 4/5 < t) : (fun s => fdBoundaryFun H s - I) =ᶠ[𝓝 t] ref_seg5_I H`
- **What**: Neighborhood-eventual equality near segment 5 interior
- **How**: `Filter.eventually_of_mem (Ioi_mem_nhds ht)` plus `fdBoundary_sub_I_eq_ref_seg5`
- **Hypotheses**: `4/5 < t`
- **Uses from project**: `fdBoundaryFun`, `ref_seg5_I`, `fdBoundary_sub_I_eq_ref_seg5`
- **Used by**: `seg5_ftc_I`, `seg5_full_intervalIntegrable_I`
- **Visibility**: private
- **Lines**: 209-212

### `private lemma arc_exp_continuous`
- **Type**: `Continuous (fun t => exp (↑(fdArcAngle t) * I))`
- **What**: The arc parametrization `t ↦ exp(i · fdArcAngle(t))` is continuous
- **How**: `Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp fdArcAngle_continuous).mul continuous_const)`
- **Hypotheses**: none
- **Uses from project**: `fdArcAngle`, `fdArcAngle_continuous`
- **Used by**: `seg2_intervalIntegrable_I`, `seg3_intervalIntegrable_I`
- **Visibility**: private
- **Lines**: 216-219

### `private lemma arc_sub_I_ne_zero_seg2`
- **Type**: `{t : ℝ} (ht1 : 1/5 ≤ t) (ht2 : t < 2/5) : exp (↑(fdArcAngle t) * I) - I ≠ 0`
- **What**: On segment 2, `exp(i · fdArcAngle(t)) ≠ I`
- **How**: assumes equality, takes real parts; uses `Real.cos_pos_of_mem_Ioo` with `fdArcAngle t ∈ (0, π/2)` derived via `nlinarith` from the bounds and `Real.pi_pos`
- **Hypotheses**: `1/5 ≤ t < 2/5`
- **Uses from project**: `fdArcAngle`
- **Used by**: `seg2_intervalIntegrable_I`
- **Visibility**: private
- **Lines**: 221-230

### `private lemma arc_sub_I_ne_zero_seg3`
- **Type**: `(H : ℝ) {t : ℝ} (ht1 : 2/5 < t) (ht2 : t ≤ 3/5) : exp (↑(fdArcAngle t) * I) - I ≠ 0`
- **What**: On segment 3, `exp(i · fdArcAngle(t)) ≠ I`
- **How**: rewrites `exp` to `fdBoundaryFun H t` via `fdBoundaryFun_arc_eq_exp` and invokes `fdBoundaryFun_sub_i_ne_zero_seg3`
- **Hypotheses**: `2/5 < t ≤ 3/5`
- **Uses from project**: `fdBoundaryFun_arc_eq_exp`, `fdBoundaryFun_sub_i_ne_zero_seg3`
- **Used by**: `seg3_intervalIntegrable_I`
- **Visibility**: private
- **Lines**: 232-236

### `private def arcIntegrand_I`
- **Type**: `(t : ℝ) : ℂ`
- **What**: The continuous arc-form of the log-derivative integrand: `(exp(i α(t)) - I)⁻¹ · (i · 5π/6) · exp(i α(t))` where `α = fdArcAngle`
- **How**: definitional
- **Hypotheses**: none
- **Uses from project**: `fdArcAngle`
- **Used by**: `seg2_intervalIntegrable_I`, `seg3_intervalIntegrable_I`
- **Visibility**: private
- **Lines**: 238-240

### `private lemma fdBoundary_eventuallyEq_arc`
- **Type**: `(H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t < 3/5) : fdBoundaryFun H =ᶠ[𝓝 t] fun s => exp (↑(fdArcAngle s) * I)`
- **What**: `fdBoundaryFun H` agrees with the arc parametrization near each `t ∈ (1/5, 3/5)`
- **How**: `Filter.eventually_of_mem (inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht2))` plus `fdBoundaryFun_arc_eq_exp`
- **Hypotheses**: `1/5 < t < 3/5`
- **Uses from project**: `fdBoundaryFun`, `fdArcAngle`, `fdBoundaryFun_arc_eq_exp`
- **Used by**: `seg2_intervalIntegrable_I`, `seg3_intervalIntegrable_I`
- **Visibility**: private
- **Lines**: 243-251

### `private lemma integrand_form_eq`
- **Type**: `(f : ℝ → ℂ) (z : ℂ) (t : ℝ) : (f t - z)⁻¹ * deriv f t = deriv (fun s => f s - z) t / (f t - z)`
- **What**: Equivalence of two pointwise forms of the log-derivative integrand
- **How**: rewrites `f - z = f + (-z)`, applies `deriv_add_const`, then `div_eq_mul_inv` and `mul_comm`
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `fdBoundary_seg1_intervalIntegrable_I`
- **Visibility**: private
- **Lines**: 256-259

### `theorem seg1_ftc_I`
- **Type**: `(H : ℝ) {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/5) : IntervalIntegrable (...) ∧ ∫ = log (γ(a)-I) - log (γ(0)-I)`
- **What**: Integrability + FTC for the log-derivative integrand on segment 1 `[0, a]` (shifted by `I`)
- **How**: applies `LogDerivFTC.ftc_log_pieceFM` with the smoothness, derivative, slit-plane, and pointwise/eventually-equality hypotheses for `ref_seg1_I` (proof >10 lines)
- **Hypotheses**: `0 ≤ a ≤ 1/5`
- **Uses from project**: `LogDerivFTC.ftc_log_pieceFM`, `ref_seg1_I_contDiff`, `ref_seg1_I_slitPlane`, `fdBoundary_sub_I_eq_ref_seg1`, `fdBoundary_sub_I_eventuallyEq_ref_seg1`, `fdBoundaryFun`
- **Used by**: `fdBoundary_seg1_intervalIntegrable_I`, `fdBoundary_integrable_left_of_I`
- **Visibility**: public
- **Lines**: 264-278
- **Notes**: >10 lines

### `theorem seg5_ftc_I`
- **Type**: `(H : ℝ) (hH : 1 < H) {b : ℝ} (hb : 4/5 < b) (hb1 : b ≤ 1) : IntervalIntegrable (...) ∧ ∫ = log (γ(1)-I) - log (γ(b)-I)`
- **What**: Integrability + FTC on segment 5 `[b, 1]` (shifted by `I`)
- **How**: applies `LogDerivFTC.ftc_log_pieceFM` with the `ref_seg5_I` smoothness/slit-plane/equality hypotheses (proof >10 lines)
- **Hypotheses**: `1 < H`; `4/5 < b ≤ 1`
- **Uses from project**: `LogDerivFTC.ftc_log_pieceFM`, `ref_seg5_I_contDiff`, `ref_seg5_I_slitPlane`, `fdBoundary_sub_I_eq_ref_seg5`, `fdBoundary_sub_I_eventuallyEq_ref_seg5`, `fdBoundaryFun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 281-295
- **Notes**: >10 lines

### `theorem fdBoundary_seg1_intervalIntegrable_I`
- **Type**: `(H : ℝ) {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/5) : IntervalIntegrable (fun t => (fdBoundaryFun H t - I)⁻¹ * deriv (fdBoundaryFun H) t) volume 0 a`
- **What**: Integrability of the standard log-derivative form on segment 1
- **How**: `(seg1_ftc_I H ha ha').1.congr` with `integrand_form_eq`
- **Hypotheses**: `0 ≤ a ≤ 1/5`
- **Uses from project**: `seg1_ftc_I`, `integrand_form_eq`, `fdBoundaryFun`
- **Used by**: `fdBoundary_integrable_left_of_I`
- **Visibility**: public
- **Lines**: 298-302

### `theorem seg2_intervalIntegrable_I`
- **Type**: `(H : ℝ) {a : ℝ} (ha : 1/5 ≤ a) (ha' : a < 2/5) : IntervalIntegrable (... fdBoundaryFun H ... - I) volume (1/5) a`
- **What**: Integrability on segment 2 `[1/5, a]`
- **How**: shows `arcIntegrand_I` is continuous on `Icc 1/5 a` (uses `arc_exp_continuous`, `arc_sub_I_ne_zero_seg2`, `continuousOn.inv₀`); transfers to the log-derivative form via `congr_ae` off `{a}`, using `fdBoundaryFun_arc_eq_exp` and `fdBoundary_eventuallyEq_arc.deriv_eq` and `fdBoundary_arc_deriv_eq` (proof >10 lines)
- **Hypotheses**: `1/5 ≤ a < 2/5`
- **Uses from project**: `arcIntegrand_I`, `arc_exp_continuous`, `arc_sub_I_ne_zero_seg2`, `fdBoundaryFun_arc_eq_exp`, `fdBoundary_eventuallyEq_arc`, `fdBoundary_arc_deriv_eq`, `fdBoundaryFun`
- **Used by**: `fdBoundary_integrable_left_of_I`
- **Visibility**: public
- **Lines**: 308-329
- **Notes**: `set_option maxHeartbeats 400000`; >10 lines

### `theorem seg3_intervalIntegrable_I`
- **Type**: `(H : ℝ) {a : ℝ} (ha : 2/5 < a) (ha' : a ≤ 3/5) : IntervalIntegrable (... fdBoundaryFun H ... - I) volume a (3/5)`
- **What**: Integrability on segment 3 `[a, 3/5]`
- **How**: same arc-based pattern as seg2: continuity of `arcIntegrand_I` (via `arc_sub_I_ne_zero_seg3`); transfer to log-derivative form using `fdBoundaryFun_arc_eq_exp`, `fdBoundary_eventuallyEq_arc.deriv_eq`, `fdBoundary_arc_deriv_eq` (proof >10 lines)
- **Hypotheses**: `2/5 < a ≤ 3/5`
- **Uses from project**: `arcIntegrand_I`, `arc_exp_continuous`, `arc_sub_I_ne_zero_seg3`, `fdBoundaryFun_arc_eq_exp`, `fdBoundary_eventuallyEq_arc`, `fdBoundary_arc_deriv_eq`, `fdBoundaryFun`
- **Used by**: `fdBoundary_integrable_right_of_I`
- **Visibility**: public
- **Lines**: 335-356
- **Notes**: `set_option maxHeartbeats 400000`; >10 lines

### `theorem seg4_full_intervalIntegrable_I`
- **Type**: `(H : ℝ) : IntervalIntegrable (... fdBoundaryFun H ... - I) volume (3/5) (4/5)`
- **What**: Full integrability on segment 4 `[3/5, 4/5]`
- **How**: `ref_seg4_I` is continuously differentiable and globally nonvanishing (`ref_seg4_I_ne_zero`) so `(ref_seg4_I)⁻¹ · deriv` is continuous and `IntervalIntegrable`; transfer to `fdBoundaryFun` form via `congr_ae` off `{4/5}` with pointwise equality and `deriv_sub_const` (proof >10 lines)
- **Hypotheses**: none
- **Uses from project**: `ref_seg4_I`, `ref_seg4_I_contDiff`, `ref_seg4_I_ne_zero`, `fdBoundary_sub_I_eventuallyEq_ref_seg4`, `fdBoundaryFun`
- **Used by**: `fdBoundary_integrable_right_of_I`
- **Visibility**: public
- **Lines**: 363-388
- **Notes**: `set_option maxHeartbeats 400000`; >10 lines

### `theorem seg5_full_intervalIntegrable_I`
- **Type**: `(H : ℝ) (hH : 1 < H) : IntervalIntegrable (... fdBoundaryFun H ... - I) volume (4/5) 1`
- **What**: Full integrability on segment 5 `[4/5, 1]`
- **How**: `ref_seg5_I` is smooth and nonvanishing for `1 < H` (via slit plane); integrand `(ref_seg5_I)⁻¹ · deriv` is continuous → `IntervalIntegrable`; transfer to `fdBoundaryFun` form via `congr_ae` off `{1}` with `fdBoundary_sub_I_eq_ref_seg5`, `_eventuallyEq_ref_seg5.deriv_eq`, `deriv_sub_const` (proof >10 lines)
- **Hypotheses**: `1 < H`
- **Uses from project**: `ref_seg5_I`, `ref_seg5_I_contDiff`, `ref_seg5_I_ne_zero`, `fdBoundary_sub_I_eq_ref_seg5`, `fdBoundary_sub_I_eventuallyEq_ref_seg5`, `fdBoundaryFun`
- **Used by**: `fdBoundary_integrable_right_of_I`
- **Visibility**: public
- **Lines**: 395-416
- **Notes**: `set_option maxHeartbeats 400000`; >10 lines

### `theorem fdBoundary_integrable_left_of_I`
- **Type**: `(H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) : IntervalIntegrable (... fdBoundaryFun H ... - I) volume 0 (2/5 - δ)`
- **What**: Combined integrability on `[0, 2/5 - δ]` for the crossing at `i`
- **How**: `IntervalIntegrable.trans` of `fdBoundary_seg1_intervalIntegrable_I` (at `a = 1/5`) and `seg2_intervalIntegrable_I` (at `a = 2/5 - δ`); inequalities via `linarith`
- **Hypotheses**: `0 < δ < 1/5`
- **Uses from project**: `fdBoundary_seg1_intervalIntegrable_I`, `seg2_intervalIntegrable_I`, `fdBoundaryFun`
- **Used by**: `gamma_integrable_left_of_I`
- **Visibility**: public
- **Lines**: 422-427

### `theorem fdBoundary_integrable_right_of_I`
- **Type**: `(H : ℝ) (hH : 1 < H) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) : IntervalIntegrable (... fdBoundaryFun H ... - I) volume (2/5 + δ) 1`
- **What**: Combined integrability on `[2/5 + δ, 1]` for the crossing at `i`
- **How**: `IntervalIntegrable.trans` chain of `seg3_intervalIntegrable_I` (at `a = 2/5 + δ`), `seg4_full_intervalIntegrable_I`, and `seg5_full_intervalIntegrable_I`; inequalities by `linarith`
- **Hypotheses**: `1 < H`; `0 < δ < 1/5`
- **Uses from project**: `seg3_intervalIntegrable_I`, `seg4_full_intervalIntegrable_I`, `seg5_full_intervalIntegrable_I`, `fdBoundaryFun`
- **Used by**: `gamma_integrable_right_of_I`
- **Visibility**: public
- **Lines**: 431-438

### `theorem gamma_integrable_left_of_I`
- **Type**: `{H} (_hH : 1 < H) {γ : PiecewiseC1Path (fdStart H) (fdStart H)} (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) {δ} (hδ : 0 < δ) (hδ' : δ < 1/5) : IntervalIntegrable (γ-based form) volume 0 (2/5 - δ)`
- **What**: `γ`-based integrability on `[0, 2/5 - δ]`, supplying the `hint_left` field of `ArcFTCHyp`
- **How**: `transfer_integrability I` from `fdBoundary_integrable_left_of_I`; uses `linarith` for `a ≤ b` and explicit `le_refl` for `0 ≤ 0`
- **Hypotheses**: `1 < H`; `γ` agrees with `fdBoundaryFun H`; `0 < δ < 1/5`
- **Uses from project**: `transfer_integrability`, `fdBoundary_integrable_left_of_I`, `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 445-453

### `theorem gamma_integrable_right_of_I`
- **Type**: `{H} (hH : 1 < H) {γ : PiecewiseC1Path (fdStart H) (fdStart H)} (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) {δ} (hδ : 0 < δ) (hδ' : δ < 1/5) : IntervalIntegrable (γ-based form) volume (2/5 + δ) 1`
- **What**: `γ`-based integrability on `[2/5 + δ, 1]`, supplying the `hint_right` field of `ArcFTCHyp`
- **How**: `transfer_integrability I` from `fdBoundary_integrable_right_of_I`; `linarith` for `a ≤ b` and `le_refl 1`
- **Hypotheses**: `1 < H`; `γ` agrees with `fdBoundaryFun H`; `0 < δ < 1/5`
- **Uses from project**: `transfer_integrability`, `fdBoundary_integrable_right_of_I`, `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 456-464

## File Summary

SegmentAnalysis.lean proves interval integrability and the FTC for the log-derivative integrand `(γ(t) - i)⁻¹ · γ'(t)` along the five segments of the modular fundamental domain boundary (parametrized by `fdBoundaryFun H` on `[0,1]`). The strategy is uniform: for each segment, introduce a smooth `ref_segN_I` function equal to `fdBoundaryFun H · − i` on that segment, prove it is `C^∞` and avoids zero (typically by real/imag-part inspection placing it in the slit plane), then transfer integrability and integrals via `congr_ae`. Segments 1 and 5 (right and left horizontals) also give FTC results in terms of `Complex.log` via the helper `LogDerivFTC.ftc_log_pieceFM`. Segments 2 and 3 are the arc, where `fdBoundaryFun H` matches `exp(i · fdArcAngle)`; integrability uses `arcIntegrand_I` and arc-specific nonvanishing lemmas (`arc_sub_I_ne_zero_seg2/3`). Segment 4 is the left vertical (`Re = -1/2`). The combined results `fdBoundary_integrable_left_of_I` (for `[0, 2/5 - δ]`) and `fdBoundary_integrable_right_of_I` (for `[2/5 + δ, 1]`) glue the pieces by `IntervalIntegrable.trans`; finally `transfer_integrability` lifts everything from `fdBoundaryFun H` to a generic `γ : PiecewiseC1Path (fdStart H) (fdStart H)` that pointwise matches `fdBoundaryFun H`, yielding `gamma_integrable_{left,right}_of_I` (the `hint_left/right` data of `ArcFTCHyp` at `i`). Three theorems set `maxHeartbeats 400000`. No sorries; depends on `FDBoundaryPath`, `ArcFTCLimit`, `SegmentFTC`, and Mathlib.
