# Inventory: `ArcGenericFTCProvider.lean`

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ArcGenericFTCProvider.lean` (941 lines)

### `def arc_h₀`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ`
- **What**: Reference linear function for seg1 (right vertical): models `fdBoundaryFun H t - z₀` on `[0, 1/5]` as `(1/2 - z₀.re) + (H - 5t·(H - √3/2) - z₀.im)·I`.
- **How**: Direct ℂ-valued algebraic definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `fdBoundary_sub_eq_arc_h₀`, `arc_h₀_continuous`, `hasDerivAt_arc_h₀`, `deriv_arc_h₀`, `arc_h₀_slitPlane`, `arc_seg1_ftc`, `arc_junction_15`, `arc_closed`, `arc_ae_eq_h₀`, `fdBoundary_ftc_telescope_arc_aux`
- **Visibility**: private
- **Lines**: 43-45
- **Notes**: none

### `lemma fdBoundary_sub_eq_arc_h₀`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) (ht : t ≤ 1/5) : fdBoundaryFun H t - z₀ = arc_h₀ H z₀ t`
- **What**: On seg1, the shifted boundary function equals the reference seg1 model.
- **How**: `Complex.ext` then simp with `fdBoundaryFun` unfolded under `ht_true` branch.
- **Hypotheses**: `t ≤ 1/5`.
- **Uses from project**: `arc_h₀`, `fdBoundaryFun`
- **Used by**: `arc_ae_eq_h₀`
- **Visibility**: private
- **Lines**: 47-54
- **Notes**: none

### `lemma arc_h₀_continuous`
- **Type**: `(H : ℝ) (z₀ : ℂ) : Continuous (arc_h₀ H z₀)`
- **What**: The reference seg1 model is a continuous function `ℝ → ℂ`.
- **How**: `Continuous.add` plus `Complex.continuous_ofReal.comp` with `fun_prop`.
- **Hypotheses**: none.
- **Uses from project**: `arc_h₀`
- **Used by**: `arc_seg1_ftc`
- **Visibility**: private
- **Lines**: 56-60
- **Notes**: none

### `lemma hasDerivAt_arc_h₀`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : HasDerivAt (arc_h₀ H z₀) (-(seg1Speed H : ℂ) * I) t`
- **What**: Derivative of the seg1 reference function equals `-seg1Speed(H) · I`.
- **How**: Compose `hasDerivAt_id.const_mul.mul_const.congr_deriv` then `ofReal_comp` and `mul_const I`.
- **Hypotheses**: none.
- **Uses from project**: `arc_h₀`, `seg1Speed`
- **Used by**: `deriv_arc_h₀`, `arc_seg1_ftc`
- **Visibility**: private
- **Lines**: 62-76
- **Notes**: none

### `lemma deriv_arc_h₀`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : deriv (arc_h₀ H z₀) t = -(seg1Speed H : ℂ) * I`
- **What**: Closed-form `deriv` of the seg1 reference.
- **How**: `.deriv` of `hasDerivAt_arc_h₀`.
- **Hypotheses**: none.
- **Uses from project**: `arc_h₀`, `hasDerivAt_arc_h₀`, `seg1Speed`
- **Used by**: `arc_seg1_ftc`
- **Visibility**: private
- **Lines**: 78-80
- **Notes**: none

### `lemma arc_h₀_slitPlane`
- **Type**: `{H : ℝ} {θ₀ : ℝ} (h_lo : π/3 < θ₀) (h_hi : θ₀ < 2π/3) (t : ℝ) : arc_h₀ H (exp (↑θ₀ * I)) t ∈ Complex.slitPlane`
- **What**: For `θ₀ ∈ (π/3, 2π/3)`, the seg1 reference at arc-z₀ has positive real part `1/2 - cos θ₀ > 0`.
- **How**: Reduce to `cos θ₀ < 1/2` via `Real.strictAntiOn_cos` and `Real.cos_pi_div_three`.
- **Hypotheses**: `π/3 < θ₀ < 2π/3`.
- **Uses from project**: `arc_h₀`, `arcZ₀_re_eq`
- **Used by**: `arc_seg1_ftc`
- **Visibility**: private
- **Lines**: 83-96
- **Notes**: none

### `def arc_h₅`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ`
- **What**: Reference linear function for seg5 (top horizontal): `(5t - 9/2 - z₀.re) + (H - z₀.im)·I`.
- **How**: Direct algebraic definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `fdBoundary_sub_eq_arc_h₅`, `arc_h₅_continuous`, `hasDerivAt_arc_h₅`, `deriv_arc_h₅`, `arc_h₅_slitPlane`, `arc_seg5_ftc`, `arc_junction_45`, `arc_closed`, `arc_branch_correction_45`, `arc_ae_eq_h₅`, `fdBoundary_ftc_telescope_arc_aux`
- **Visibility**: private
- **Lines**: 100-101
- **Notes**: none

### `lemma fdBoundary_sub_eq_arc_h₅`
- **Type**: `(H : ℝ) (z₀ : ℂ) {t : ℝ} (ht : 4/5 < t) : fdBoundaryFun H t - z₀ = arc_h₅ H z₀ t`
- **What**: On seg5 (t > 4/5), the shifted boundary equals the seg5 model.
- **How**: simp `fdBoundaryFun` with all four `ite` negative branches, then `Complex.ext`.
- **Hypotheses**: `4/5 < t`.
- **Uses from project**: `arc_h₅`, `fdBoundaryFun`
- **Used by**: `arc_ae_eq_h₅`
- **Visibility**: private
- **Lines**: 103-112
- **Notes**: none

### `lemma arc_h₅_continuous`
- **Type**: `(H : ℝ) (z₀ : ℂ) : Continuous (arc_h₅ H z₀)`
- **What**: Seg5 reference is continuous.
- **How**: `Continuous.add` and `Complex.continuous_ofReal.comp`.
- **Hypotheses**: none.
- **Uses from project**: `arc_h₅`
- **Used by**: `arc_seg5_ftc`
- **Visibility**: private
- **Lines**: 114-117
- **Notes**: none

### `lemma hasDerivAt_arc_h₅`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : HasDerivAt (arc_h₅ H z₀) (5 : ℂ) t`
- **What**: Derivative of the seg5 reference equals `5`.
- **How**: Chain of `hasDerivAt_id.const_mul.sub_const.sub_const` and `ofReal_comp`.
- **Hypotheses**: none.
- **Uses from project**: `arc_h₅`
- **Used by**: `deriv_arc_h₅`, `arc_seg5_ftc`
- **Visibility**: private
- **Lines**: 119-125
- **Notes**: none

### `lemma deriv_arc_h₅`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : deriv (arc_h₅ H z₀) t = 5`
- **What**: Closed-form derivative for seg5 reference.
- **How**: `.deriv` of `hasDerivAt_arc_h₅`.
- **Hypotheses**: none.
- **Uses from project**: `arc_h₅`, `hasDerivAt_arc_h₅`
- **Used by**: `arc_seg5_ftc`
- **Visibility**: private
- **Lines**: 127-129
- **Notes**: none

### `lemma arc_h₅_slitPlane`
- **Type**: `{H : ℝ} (hH : 1 < H) {θ₀ : ℝ} (t : ℝ) : arc_h₅ H (exp (↑θ₀ * I)) t ∈ Complex.slitPlane`
- **What**: For `H > 1`, seg5 reference has positive imaginary part `H - sin θ₀ > 0`.
- **How**: `right`-branch of slitPlane via `Real.sin_le_one`.
- **Hypotheses**: `1 < H`.
- **Uses from project**: `arc_h₅`, `arcZ₀_im_eq`
- **Used by**: `arc_seg5_ftc`
- **Visibility**: private
- **Lines**: 132-140
- **Notes**: none

### `def arc_h₃`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ`
- **What**: Reference linear function for seg4 (left vertical): `(-1/2 - z₀.re) + (√3/2 + (5t-3)·(H-√3/2) - z₀.im)·I`.
- **How**: Direct algebraic definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `fdBoundary_sub_eq_arc_h₃`, `arc_h₃_continuous`, `hasDerivAt_arc_h₃`, `deriv_arc_h₃`, `neg_arc_h₃_slitPlane`, `arc_seg4_ftc`, `arc_junction_35`, `arc_junction_45`, `arc_branch_correction_45`, `arc_ae_eq_h₃`, `fdBoundary_ftc_telescope_arc_aux`
- **Visibility**: private
- **Lines**: 144-146
- **Notes**: none

### `lemma fdBoundary_sub_eq_arc_h₃`
- **Type**: `(H : ℝ) (z₀ : ℂ) {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) : fdBoundaryFun H t - z₀ = arc_h₃ H z₀ t`
- **What**: On seg4 (3/5 < t ≤ 4/5), shifted boundary equals seg4 model.
- **How**: simp `fdBoundaryFun` with appropriate `ite` branches, then `Complex.ext`.
- **Hypotheses**: `3/5 < t ≤ 4/5`.
- **Uses from project**: `arc_h₃`, `fdBoundaryFun`
- **Used by**: `arc_ae_eq_h₃`
- **Visibility**: private
- **Lines**: 148-158
- **Notes**: none

### `lemma arc_h₃_continuous`
- **Type**: `(H : ℝ) (z₀ : ℂ) : Continuous (arc_h₃ H z₀)`
- **What**: Seg4 reference is continuous.
- **How**: `Continuous.add`, `Continuous.mul`, `Complex.continuous_ofReal.comp`.
- **Hypotheses**: none.
- **Uses from project**: `arc_h₃`
- **Used by**: `arc_seg4_ftc`
- **Visibility**: private
- **Lines**: 160-164
- **Notes**: none

### `lemma hasDerivAt_arc_h₃`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : HasDerivAt (arc_h₃ H z₀) ((seg1Speed H : ℂ) * I) t`
- **What**: Derivative of seg4 reference equals `seg1Speed(H) · I`.
- **How**: Chain of `hasDerivAt_id.const_mul.sub_const`, `mul_const`, `const_add`, `sub_const`, `ofReal_comp`, `mul_const I`.
- **Hypotheses**: none.
- **Uses from project**: `arc_h₃`, `seg1Speed`
- **Used by**: `deriv_arc_h₃`, `arc_seg4_ftc`
- **Visibility**: private
- **Lines**: 166-180
- **Notes**: none

### `lemma deriv_arc_h₃`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : deriv (arc_h₃ H z₀) t = (seg1Speed H : ℂ) * I`
- **What**: Closed-form derivative for seg4 reference.
- **How**: `.deriv` of `hasDerivAt_arc_h₃`.
- **Hypotheses**: none.
- **Uses from project**: `arc_h₃`, `hasDerivAt_arc_h₃`, `seg1Speed`
- **Used by**: `arc_seg4_ftc`
- **Visibility**: private
- **Lines**: 182-184
- **Notes**: none

### `lemma neg_arc_h₃_slitPlane`
- **Type**: `{H : ℝ} {θ₀ : ℝ} (h_lo : π/3 < θ₀) (h_hi : θ₀ < 2π/3) (t : ℝ) : -(arc_h₃ H (exp (↑θ₀ * I)) t) ∈ Complex.slitPlane`
- **What**: For `θ₀ ∈ (π/3, 2π/3)`, the negated seg4 reference has positive real part `1/2 + cos θ₀ > 0`.
- **How**: Uses `Real.cos_pi_sub` to compute `cos(2π/3) = -1/2`, then `Real.strictAntiOn_cos`.
- **Hypotheses**: `π/3 < θ₀ < 2π/3`.
- **Uses from project**: `arc_h₃`, `arcZ₀_re_eq`
- **Used by**: `arc_seg4_ftc`
- **Visibility**: private
- **Lines**: 187-202
- **Notes**: none

### `def arc_h_arc`
- **Type**: `(z₀ : ℂ) (t : ℝ) : ℂ`
- **What**: Reference arc function on segments 2-3: `exp(i · fdArcAngle(t)) - z₀`.
- **How**: Direct definition.
- **Hypotheses**: none.
- **Uses from project**: `fdArcAngle`
- **Used by**: `fdBoundary_sub_eq_arc_h_arc`, `arc_h_arc_continuous`, `hasDerivAt_arc_h_arc`, `deriv_arc_h_arc`, `arc_h_arc_left_slitPlane`, `neg_arc_h_arc_right_slitPlane`, `arc_arc_left_ftc`, `arc_arc_right_ftc`, `arc_junction_15`, `arc_junction_35`, `arc_h_arc_ratio_eq`, `arc_log_diff_tendsto`, `arc_ae_eq_h_arc`, `arc_E`, `arc_E_tendsto`, `fdBoundary_ftc_telescope_arc_aux`
- **Visibility**: private
- **Lines**: 206-207
- **Notes**: none

### `lemma fdBoundary_sub_eq_arc_h_arc`
- **Type**: `{H : ℝ} (z₀ : ℂ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) : fdBoundaryFun H t - z₀ = arc_h_arc z₀ t`
- **What**: On the arc segments, shifted boundary equals the arc reference.
- **How**: Unfold `arc_h_arc` and apply `fdBoundaryFun_arc_eq_exp`.
- **Hypotheses**: `1/5 < t ≤ 3/5`.
- **Uses from project**: `arc_h_arc`, `fdBoundaryFun`, `fdBoundaryFun_arc_eq_exp`
- **Used by**: `arc_ae_eq_h_arc`
- **Visibility**: private
- **Lines**: 209-212
- **Notes**: none

### `lemma arc_h_arc_continuous`
- **Type**: `(z₀ : ℂ) : Continuous (arc_h_arc z₀)`
- **What**: Arc reference is continuous.
- **How**: `Continuous.sub` composed with `Complex.continuous_exp`, `continuous_ofReal`, `fdArcAngle_continuous`.
- **Hypotheses**: none.
- **Uses from project**: `arc_h_arc`, `fdArcAngle_continuous`
- **Used by**: `arc_arc_left_ftc`, `arc_arc_right_ftc`
- **Visibility**: private
- **Lines**: 214-218
- **Notes**: none

### `lemma hasDerivAt_arc_h_arc`
- **Type**: `(z₀ : ℂ) (t : ℝ) : HasDerivAt (arc_h_arc z₀) (↑(5π/6) * I * exp (↑(fdArcAngle t) * I)) t`
- **What**: Derivative of arc reference is `(5π/6) I · exp(i·fdArcAngle(t))`.
- **How**: Chain rule: `fdArcAngle` has derivative `5π/6`, then `.ofReal_comp.mul_const I`, then `.cexp.sub_const`.
- **Hypotheses**: none.
- **Uses from project**: `arc_h_arc`, `fdArcAngle`
- **Used by**: `deriv_arc_h_arc`, `arc_arc_left_ftc`, `arc_arc_right_ftc`
- **Visibility**: private
- **Lines**: 220-231
- **Notes**: none

### `lemma deriv_arc_h_arc`
- **Type**: `(z₀ : ℂ) (t : ℝ) : deriv (arc_h_arc z₀) t = ↑(5π/6) * I * exp (↑(fdArcAngle t) * I)`
- **What**: Closed-form derivative of the arc reference.
- **How**: `.deriv` of `hasDerivAt_arc_h_arc`.
- **Hypotheses**: none.
- **Uses from project**: `arc_h_arc`, `hasDerivAt_arc_h_arc`, `fdArcAngle`
- **Used by**: `arc_arc_left_ftc`, `arc_arc_right_ftc`
- **Visibility**: private
- **Lines**: 233-235
- **Notes**: none

### `lemma arc_h_arc_left_slitPlane`
- **Type**: `{θ₀ : ℝ} (h_lo : π/3 < θ₀) (h_hi : θ₀ < 2π/3) {t : ℝ} (ht1 : 1/5 ≤ t) (ht_lt : t < arcT₀ θ₀) : arc_h_arc (exp (↑θ₀ * I)) t ∈ Complex.slitPlane`
- **What**: On the left arc (t < t₀), `arc_h_arc z₀ t` has positive real part because the angle `fdArcAngle(t) < θ₀`.
- **How**: `Real.strictAntiOn_cos` applied to `fdArcAngle(t) < θ₀` (derived from `fdArcAngle_arcT₀`).
- **Hypotheses**: `π/3 < θ₀ < 2π/3`, `1/5 ≤ t < arcT₀ θ₀`.
- **Uses from project**: `arc_h_arc`, `fdArcAngle`, `arcT₀`, `fdArcAngle_arcT₀`
- **Used by**: `arc_arc_left_ftc`
- **Visibility**: private
- **Lines**: 239-258
- **Notes**: >10 lines (20)

### `lemma neg_arc_h_arc_right_slitPlane`
- **Type**: `{θ₀ : ℝ} (h_lo : π/3 < θ₀) (h_hi : θ₀ < 2π/3) {t : ℝ} (ht_gt : arcT₀ θ₀ < t) (ht3 : t ≤ 3/5) : -(arc_h_arc (exp (↑θ₀ * I)) t) ∈ Complex.slitPlane`
- **What**: On the right arc (t > t₀), the negated reference has positive real part since `fdArcAngle(t) > θ₀`.
- **How**: `Real.strictAntiOn_cos` applied to `θ₀ < fdArcAngle(t)`, similar to left case.
- **Hypotheses**: `π/3 < θ₀ < 2π/3`, `arcT₀ θ₀ < t ≤ 3/5`.
- **Uses from project**: `arc_h_arc`, `fdArcAngle`, `arcT₀`, `fdArcAngle_arcT₀`
- **Used by**: `arc_arc_right_ftc`
- **Visibility**: private
- **Lines**: 261-281
- **Notes**: >10 lines (21)

### `lemma arc_seg1_ftc`
- **Type**: `(H : ℝ) {θ₀ : ℝ} (h_lo : π/3 < θ₀) (h_hi : θ₀ < 2π/3) : IntervalIntegrable ... ∧ ∫... = log(arc_h₀(1/5)) - log(arc_h₀(0))`
- **What**: FTC for `log` on seg1: integrating `deriv h / h` yields the difference of logs at endpoints.
- **How**: Apply `LogDerivFTC.ftc_log_on_segment` with continuity, differentiability, slitPlane-membership via `arc_h₀_slitPlane`.
- **Hypotheses**: `π/3 < θ₀ < 2π/3`.
- **Uses from project**: `arc_h₀`, `arc_h₀_continuous`, `hasDerivAt_arc_h₀`, `deriv_arc_h₀`, `arc_h₀_slitPlane`, `LogDerivFTC.ftc_log_on_segment`, `seg1Speed`
- **Used by**: `fdBoundary_ftc_telescope_arc_aux`, `arc_hint_left_helper`
- **Visibility**: private
- **Lines**: 285-302
- **Notes**: >10 lines (18)

### `lemma arc_arc_left_ftc`
- **Type**: `{θ₀ : ℝ} (h_lo : π/3 < θ₀) (h_hi : θ₀ < 2π/3) {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < arcT₀ θ₀ - 1/5) : ... = log(arc_h_arc(t₀-δ)) - log(arc_h_arc(1/5))`
- **What**: FTC for `log` on the left arc segment `[1/5, t₀-δ]`.
- **How**: `LogDerivFTC.ftc_log_on_segment` with `arc_h_arc_left_slitPlane` for membership.
- **Hypotheses**: `π/3 < θ₀ < 2π/3`, `0 < δ < arcT₀ θ₀ - 1/5`.
- **Uses from project**: `arc_h_arc`, `arc_h_arc_continuous`, `hasDerivAt_arc_h_arc`, `deriv_arc_h_arc`, `arc_h_arc_left_slitPlane`, `LogDerivFTC.ftc_log_on_segment`, `fdArcAngle_continuous`, `arcT₀`
- **Used by**: `fdBoundary_ftc_telescope_arc_aux`, `arc_hint_left_helper`
- **Visibility**: private
- **Lines**: 304-324
- **Notes**: >10 lines (21)

### `lemma arc_arc_right_ftc`
- **Type**: `{θ₀ : ℝ} (h_lo : π/3 < θ₀) (h_hi : θ₀ < 2π/3) {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 3/5 - arcT₀ θ₀) : ... = log(-arc_h_arc(3/5)) - log(-arc_h_arc(t₀+δ))`
- **What**: FTC for `log(-·)` on the right arc segment `[t₀+δ, 3/5]`.
- **How**: `LogDerivFTC.ftc_log_neg_on_segment` with `neg_arc_h_arc_right_slitPlane`.
- **Hypotheses**: `π/3 < θ₀ < 2π/3`, `0 < δ < 3/5 - arcT₀ θ₀`.
- **Uses from project**: `arc_h_arc`, `arc_h_arc_continuous`, `hasDerivAt_arc_h_arc`, `deriv_arc_h_arc`, `neg_arc_h_arc_right_slitPlane`, `LogDerivFTC.ftc_log_neg_on_segment`, `fdArcAngle_continuous`, `arcT₀`
- **Used by**: `fdBoundary_ftc_telescope_arc_aux`, `arc_hint_right_helper`
- **Visibility**: private
- **Lines**: 326-346
- **Notes**: >10 lines (21)

### `lemma arc_seg4_ftc`
- **Type**: `(H : ℝ) {θ₀ : ℝ} (h_lo : π/3 < θ₀) (h_hi : θ₀ < 2π/3) : ... = log(-arc_h₃(4/5)) - log(-arc_h₃(3/5))`
- **What**: FTC for `log(-·)` on seg4.
- **How**: `LogDerivFTC.ftc_log_neg_on_segment` with `neg_arc_h₃_slitPlane`.
- **Hypotheses**: `π/3 < θ₀ < 2π/3`.
- **Uses from project**: `arc_h₃`, `arc_h₃_continuous`, `hasDerivAt_arc_h₃`, `deriv_arc_h₃`, `neg_arc_h₃_slitPlane`, `LogDerivFTC.ftc_log_neg_on_segment`, `seg1Speed`
- **Used by**: `fdBoundary_ftc_telescope_arc_aux`, `arc_hint_right_helper`
- **Visibility**: private
- **Lines**: 348-365
- **Notes**: >10 lines (18)

### `lemma arc_seg5_ftc`
- **Type**: `{H : ℝ} (hH : 1 < H) {θ₀ : ℝ} : ... = log(arc_h₅(1)) - log(arc_h₅(4/5))`
- **What**: FTC for `log` on seg5.
- **How**: `LogDerivFTC.ftc_log_on_segment` with `arc_h₅_slitPlane`.
- **Hypotheses**: `1 < H`.
- **Uses from project**: `arc_h₅`, `arc_h₅_continuous`, `hasDerivAt_arc_h₅`, `deriv_arc_h₅`, `arc_h₅_slitPlane`, `LogDerivFTC.ftc_log_on_segment`
- **Used by**: `fdBoundary_ftc_telescope_arc_aux`, `arc_hint_right_helper`
- **Visibility**: private
- **Lines**: 367-382
- **Notes**: >10 lines (16)

### `lemma arc_junction_15`
- **Type**: `(H : ℝ) (z₀ : ℂ) : arc_h₀ H z₀ (1/5) = arc_h_arc z₀ (1/5)`
- **What**: At `t = 1/5`, the seg1 and arc references agree.
- **How**: Unfold and compute `fdArcAngle(1/5) = π/3`, use `cos_pi_div_three`, `sin_pi_div_three`, then `Complex.ext`.
- **Hypotheses**: none.
- **Uses from project**: `arc_h₀`, `arc_h_arc`, `fdArcAngle`
- **Used by**: `fdBoundary_ftc_telescope_arc_aux`
- **Visibility**: private
- **Lines**: 386-397
- **Notes**: >10 lines (12)

### `lemma arc_junction_35`
- **Type**: `(H : ℝ) (z₀ : ℂ) : arc_h_arc z₀ (3/5) = arc_h₃ H z₀ (3/5)`
- **What**: At `t = 3/5`, arc and seg4 references agree.
- **How**: Compute `fdArcAngle(3/5) = 2π/3`, then `cos(π - π/3)`, `sin(π - π/3)` simplifications, finishing with `Complex.ext`.
- **Hypotheses**: none.
- **Uses from project**: `arc_h_arc`, `arc_h₃`, `fdArcAngle`
- **Used by**: `fdBoundary_ftc_telescope_arc_aux`
- **Visibility**: private
- **Lines**: 399-412
- **Notes**: >10 lines (14)

### `lemma arc_junction_45`
- **Type**: `(H : ℝ) (z₀ : ℂ) : arc_h₃ H z₀ (4/5) = arc_h₅ H z₀ (4/5)`
- **What**: At `t = 4/5`, seg4 and seg5 references agree.
- **How**: Unfold and `Complex.ext` reduces to pure algebraic identities (ring).
- **Hypotheses**: none.
- **Uses from project**: `arc_h₃`, `arc_h₅`
- **Used by**: `arc_branch_correction_45`, `fdBoundary_ftc_telescope_arc_aux`
- **Visibility**: private
- **Lines**: 414-423
- **Notes**: none

### `lemma arc_closed`
- **Type**: `(H : ℝ) (z₀ : ℂ) : arc_h₀ H z₀ 0 = arc_h₅ H z₀ 1`
- **What**: The seg1 reference at `t=0` and seg5 reference at `t=1` agree, expressing closedness of the loop.
- **How**: Unfold + `Complex.ext` + ring.
- **Hypotheses**: none.
- **Uses from project**: `arc_h₀`, `arc_h₅`
- **Used by**: `fdBoundary_ftc_telescope_arc_aux`
- **Visibility**: private
- **Lines**: 425-434
- **Notes**: none

### `lemma arc_branch_correction_45`
- **Type**: `{H : ℝ} (hH : 1 < H) (θ₀ : ℝ) : log(-(arc_h₃ H (exp (↑θ₀ * I)) (4/5))) - log(arc_h₅ H (exp (↑θ₀ * I)) (4/5)) = -(↑π * I)`
- **What**: At the 4/5 junction the log-branch jumps by `-π·I`: value lies in upper-left quadrant (re<0, im>0), so `log(-w) = log(w) - π·I`.
- **How**: Use `Complex.arg_neg_eq_arg_sub_pi_of_im_pos` combined with `Real.sin_le_one` to establish `im > 0` for `H > 1`.
- **Hypotheses**: `1 < H`.
- **Uses from project**: `arc_h₃`, `arc_h₅`, `arcZ₀_re_eq`, `arcZ₀_im_eq`, `arc_junction_45`
- **Used by**: `fdBoundary_ftc_telescope_arc_aux`
- **Visibility**: private
- **Lines**: 441-463
- **Notes**: >10 lines (23)

### `lemma arc_ae_eq_h₀`
- **Type**: `(H : ℝ) (z₀ : ℂ) : ∀ᵐ t, t ∈ uIoc 0 (1/5) → (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t = deriv (arc_h₀ H z₀) t / arc_h₀ H z₀ t`
- **What**: Off a measure-zero set, the boundary log-derivative integrand equals the reference's log-derivative on seg1.
- **How**: Filter-upwards on `{1/5}ᶜ`; use `fdBoundary_sub_eq_arc_h₀` and `EventuallyEq.deriv_eq`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `arc_h₀`, `fdBoundary_sub_eq_arc_h₀`
- **Used by**: `fdBoundary_ftc_telescope_arc_aux`, `arc_hint_left_helper`
- **Visibility**: private
- **Lines**: 467-479
- **Notes**: >10 lines (13)

### `lemma arc_ae_eq_h_arc`
- **Type**: `(H : ℝ) (z₀ : ℂ) {a b : ℝ} (hab : a ≤ b) (ha_ge : 1/5 ≤ a) (hb_le : b ≤ 3/5) : ∀ᵐ t, t ∈ uIoc a b → ... = deriv (arc_h_arc z₀) t / arc_h_arc z₀ t`
- **What**: Off measure-zero, boundary log-derivative integrand equals arc reference's log-derivative on a sub-arc `[a,b] ⊂ [1/5,3/5]`.
- **How**: Filter-upwards on `{a,b}ᶜ`; uses `fdBoundary_sub_eq_arc_h_arc`.
- **Hypotheses**: `a ≤ b`, `1/5 ≤ a`, `b ≤ 3/5`.
- **Uses from project**: `fdBoundaryFun`, `arc_h_arc`, `fdBoundary_sub_eq_arc_h_arc`
- **Used by**: `fdBoundary_ftc_telescope_arc_aux`, `arc_hint_left_helper`, `arc_hint_right_helper`
- **Visibility**: private
- **Lines**: 481-498
- **Notes**: >10 lines (18)

### `lemma arc_ae_eq_h₃`
- **Type**: `(H : ℝ) (z₀ : ℂ) : ∀ᵐ t, t ∈ uIoc (3/5) (4/5) → ... = deriv (arc_h₃ H z₀) t / arc_h₃ H z₀ t`
- **What**: Same a.e. identification for seg4.
- **How**: Filter-upwards on `{4/5}ᶜ`; uses `fdBoundary_sub_eq_arc_h₃`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `arc_h₃`, `fdBoundary_sub_eq_arc_h₃`
- **Used by**: `fdBoundary_ftc_telescope_arc_aux`, `arc_hint_right_helper`
- **Visibility**: private
- **Lines**: 500-513
- **Notes**: >10 lines (14)

### `lemma arc_ae_eq_h₅`
- **Type**: `(H : ℝ) (z₀ : ℂ) : ∀ᵐ t, t ∈ uIoc (4/5) 1 → ... = deriv (arc_h₅ H z₀) t / arc_h₅ H z₀ t`
- **What**: Same a.e. identification for seg5 (without further exclusion).
- **How**: `ae_of_all`, using `fdBoundary_sub_eq_arc_h₅`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `arc_h₅`, `fdBoundary_sub_eq_arc_h₅`
- **Used by**: `fdBoundary_ftc_telescope_arc_aux`, `arc_hint_right_helper`
- **Visibility**: private
- **Lines**: 515-525
- **Notes**: >10 lines (11)

### `theorem fdBoundary_ftc_telescope_arc_aux`
- **Type**: `{H : ℝ} (hH : 1 < H) {θ₀ : ℝ} (h_lo : π/3 < θ₀) (h_hi : θ₀ < 2π/3) {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_lo : δ < arcT₀ θ₀ - 1/5) (hδ_lt_hi : δ < 3/5 - arcT₀ θ₀) : sum_of_two_integrals = log(arc_h_arc(t₀-δ)) - log(-arc_h_arc(t₀+δ)) + (-π·I)`
- **What**: The "trimmed" pole-avoiding boundary integral around an arc pole `z₀ = exp(iθ₀)`, with crossing window excised by δ, equals the log-crossing term plus the `-π·I` branch correction.
- **How**: Splits the integral into 5 pieces (seg1, left arc, right arc, seg4, seg5), applies the per-segment FTCs, junction equalities, and `arc_branch_correction_45`. Key lemma: `intervalIntegral.integral_add_adjacent_intervals` for telescoping.
- **Hypotheses**: `1 < H`, `π/3 < θ₀ < 2π/3`, `0 < δ` strictly below both gap bounds.
- **Uses from project**: `fdBoundaryFun`, `arcT₀`, `arcT₀_gt_one_fifth`, `arcT₀_lt_three_fifths`, `arc_seg1_ftc`, `arc_arc_left_ftc`, `arc_arc_right_ftc`, `arc_seg4_ftc`, `arc_seg5_ftc`, `arc_ae_eq_h₀`, `arc_ae_eq_h_arc`, `arc_ae_eq_h₃`, `arc_ae_eq_h₅`, `arc_h₀`, `arc_h₅`, `arc_h₃`, `arc_h_arc`, `arc_junction_15`, `arc_junction_35`, `arc_junction_45`, `arc_closed`, `arc_branch_correction_45`
- **Used by**: `arc_h_ftc_helper`
- **Visibility**: public (theorem)
- **Lines**: 533-638
- **Notes**: >10 lines (106); central telescoping lemma

### `lemma log_div_of_re_pos`
- **Type**: `{a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) : Complex.log (a / b) = Complex.log a - Complex.log b`
- **What**: Standard `log` algebra: positive-real-part numerator and denominator force the arguments to lie in `(-π/2, π/2)`, where `log` is additive over multiplication.
- **How**: `Complex.abs_arg_lt_pi_div_two_iff` for both `a, b`; then `Complex.log_mul` + `Complex.log_inv` after rewriting `a/b = a * b⁻¹`.
- **Hypotheses**: `0 < a.re ∧ 0 < b.re`.
- **Uses from project**: []
- **Used by**: `arc_log_diff_tendsto`
- **Visibility**: private
- **Lines**: 642-658
- **Notes**: >10 lines (17)

### `lemma arc_h_arc_ratio_eq`
- **Type**: `{θ₀ : ℝ} {δ : ℝ} (hδ_pos : 0 < δ) (hδ_small : δ * (5π/6) < π) : arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - δ) / (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + δ))) = exp (↑(-(5π/6 · δ)) * I)`
- **What**: Closed-form ratio: both numerator and `-`-denominator factor as `exp(iθ₀)·(exp(∓i 5πδ/6) - 1)`, with ratio simplifying to `exp(-i 5πδ/6)`.
- **How**: Compute `fdArcAngle(t₀±δ) = θ₀ ± 5πδ/6` via `fdArcAngle_arcT₀`; use `Complex.exp_sub/add/neg`. Key: `Real.sin_pos_of_pos_of_lt_pi` to show `w ≠ 1`. Concluded via `field_simp; ring`.
- **Hypotheses**: `0 < δ`, `δ · 5π/6 < π`.
- **Uses from project**: `arc_h_arc`, `arcT₀`, `fdArcAngle`, `fdArcAngle_arcT₀`
- **Used by**: `arc_log_diff_tendsto`
- **Visibility**: private
- **Lines**: 666-709
- **Notes**: >10 lines (44)

### `lemma arc_log_diff_tendsto`
- **Type**: `{θ₀ : ℝ} (h_lo : π/3 < θ₀) (h_hi : θ₀ < 2π/3) : Tendsto (fun δ => log(arc_h_arc(t₀-δ)) - log(-arc_h_arc(t₀+δ))) (𝓝[>] 0) (𝓝 0)`
- **What**: The log-crossing contribution at the arc pole vanishes as δ → 0+.
- **How**: Rewrite log-diff as `log(ratio)` via `log_div_of_re_pos` (requires positive real parts proven via `Real.strictAntiOn_cos`); compose with `arc_h_arc_ratio_eq`; use continuity of `log(exp(...))` at 0.
- **Hypotheses**: `π/3 < θ₀ < 2π/3`.
- **Uses from project**: `arc_h_arc`, `arcT₀`, `arcT₀_gt_one_fifth`, `arcT₀_lt_three_fifths`, `fdArcAngle`, `fdArcAngle_arcT₀`, `arc_h_arc_ratio_eq`, `log_div_of_re_pos`
- **Used by**: `arc_E_tendsto`
- **Visibility**: private
- **Lines**: 714-792
- **Notes**: >10 lines (79); large positive-real-part bookkeeping for both endpoints

### `lemma arc_arcsinDelta_tendsto`
- **Type**: `Tendsto arcsinDelta (𝓝[>] 0) (𝓝[>] 0)`
- **What**: The shrinkage function `arcsinDelta` (`12/(5π) · arcsin(ε/2)`) tends to 0+ as ε → 0+.
- **How**: Continuity at 0 of `arcsin` composed with division by 2; positivity from `arcsinDelta_pos`.
- **Hypotheses**: none.
- **Uses from project**: `arcsinDelta`, `arcsinDelta_pos`
- **Used by**: `arc_E_tendsto`
- **Visibility**: private
- **Lines**: 796-808
- **Notes**: none

### `def arc_E`
- **Type**: `(θ₀ : ℝ) (ε : ℝ) : ℂ`
- **What**: The trimmed boundary integral as a function of ε: `log(arc_h_arc(t₀-arcsinDelta(ε))) - log(-arc_h_arc(t₀+arcsinDelta(ε))) + (-π·I)`.
- **How**: Direct definition.
- **Hypotheses**: none.
- **Uses from project**: `arc_h_arc`, `arcT₀`, `arcsinDelta`
- **Used by**: `arc_E_tendsto`, `arc_h_ftc_helper`, `arcFTCHyp_arc_generic`
- **Visibility**: private
- **Lines**: 812-815
- **Notes**: none

### `lemma arc_E_tendsto`
- **Type**: `{θ₀ : ℝ} (h_lo : π/3 < θ₀) (h_hi : θ₀ < 2π/3) : Tendsto (arc_E θ₀) (𝓝[>] 0) (𝓝 (-(↑π * I)))`
- **What**: As ε → 0+, the trimmed `arc_E θ₀ ε` approaches `-π·I`.
- **How**: Compose `arc_log_diff_tendsto` with `arc_arcsinDelta_tendsto`, then add the constant `-π·I`.
- **Hypotheses**: `π/3 < θ₀ < 2π/3`.
- **Uses from project**: `arc_E`, `arc_h_arc`, `arcT₀`, `arcsinDelta`, `arc_log_diff_tendsto`, `arc_arcsinDelta_tendsto`
- **Used by**: `arcFTCHyp_arc_generic`
- **Visibility**: private
- **Lines**: 817-826
- **Notes**: none

### `lemma arc_h_ftc_helper`
- **Type**: `{H : ℝ} (hH : 1 < H) (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) {θ₀ : ℝ} (h_lo : π/3 < θ₀) (h_hi : θ₀ < 2π/3) (ε : ℝ) (hε : 0 < ε) (hε_thr : ε < arcThreshold H θ₀) : (∫ ... left) + (∫ ... right) = arc_E θ₀ ε`
- **What**: Packages the telescoping into the `ArcFTCHyp.h_ftc` field: for a path γ that coincides with `fdBoundaryFun`, the trimmed integral equals `arc_E θ₀ ε`.
- **How**: Transfer integrals from γ to `fdBoundaryFun` via `transfer_integral`, then invoke `fdBoundary_ftc_telescope_arc_aux`. Gap bounds derived via `arcsinDelta_lt_arcGap`, `min_le_left/right`.
- **Hypotheses**: `1 < H`, `γ` agrees on `Icc 0 1`, `π/3 < θ₀ < 2π/3`, `0 < ε < arcThreshold H θ₀`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `arcsinDelta`, `arcsinDelta_pos`, `arcsinDelta_lt_arcGap`, `arcGap`, `arcT₀`, `arcT₀_gt_one_fifth`, `arcT₀_lt_three_fifths`, `arcThreshold`, `transfer_integral`, `arc_E`, `fdBoundary_ftc_telescope_arc_aux`
- **Used by**: `arcFTCHyp_arc_generic`
- **Visibility**: private
- **Lines**: 832-854
- **Notes**: >10 lines (23)

### `lemma arc_hint_left_helper`
- **Type**: `{H : ℝ} (_hH : 1 < H) (γ ...) (hγ ...) {θ₀ : ℝ} (h_lo : π/3 < θ₀) (h_hi : θ₀ < 2π/3) (ε : ℝ) (hε : 0 < ε) (hε_thr : ε < arcThreshold H θ₀) : IntervalIntegrable ... volume 0 (arcT₀ θ₀ - arcsinDelta ε)`
- **What**: The left-trimmed integrand is integrable on `[0, t₀ - arcsinDelta(ε)]`.
- **How**: `transfer_integrability` from γ to `fdBoundaryFun`; chain seg1 + left-arc `IntervalIntegrable`s via `arc_ae_eq_h₀.mono` and `arc_ae_eq_h_arc.mono`, then `.trans`.
- **Hypotheses**: `1 < H`, `γ` agrees, `π/3 < θ₀ < 2π/3`, `0 < ε < arcThreshold H θ₀`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `arcsinDelta`, `arcsinDelta_pos`, `arcsinDelta_lt_arcGap`, `arcGap`, `arcT₀`, `arcT₀_gt_one_fifth`, `arcT₀_lt_three_fifths`, `arcThreshold`, `transfer_integrability`, `arc_seg1_ftc`, `arc_arc_left_ftc`, `arc_ae_eq_h₀`, `arc_ae_eq_h_arc`
- **Used by**: `arcFTCHyp_arc_generic`
- **Visibility**: private
- **Lines**: 856-886
- **Notes**: >10 lines (31); `set_option maxHeartbeats 4000000`

### `lemma arc_hint_right_helper`
- **Type**: `{H : ℝ} (hH : 1 < H) (γ ...) (hγ ...) {θ₀ : ℝ} (h_lo : π/3 < θ₀) (h_hi : θ₀ < 2π/3) (ε : ℝ) (hε : 0 < ε) (hε_thr : ε < arcThreshold H θ₀) : IntervalIntegrable ... volume (arcT₀ θ₀ + arcsinDelta ε) 1`
- **What**: The right-trimmed integrand is integrable on `[t₀ + arcsinDelta(ε), 1]`.
- **How**: `transfer_integrability` + chain `arc_arc_right_ftc`, `arc_seg4_ftc`, `arc_seg5_ftc` (each upgraded via `.congr_ae` against `arc_ae_eq_*`), composed by `.trans`.
- **Hypotheses**: `1 < H`, `γ` agrees, `π/3 < θ₀ < 2π/3`, `0 < ε < arcThreshold H θ₀`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `arcsinDelta`, `arcsinDelta_pos`, `arcsinDelta_lt_arcGap`, `arcGap`, `arcT₀`, `arcT₀_gt_one_fifth`, `arcT₀_lt_three_fifths`, `arcThreshold`, `transfer_integrability`, `arc_arc_right_ftc`, `arc_seg4_ftc`, `arc_seg5_ftc`, `arc_ae_eq_h_arc`, `arc_ae_eq_h₃`, `arc_ae_eq_h₅`
- **Used by**: `arcFTCHyp_arc_generic`
- **Visibility**: private
- **Lines**: 888-924
- **Notes**: >10 lines (37); `set_option maxHeartbeats 8000000`

### `def arcFTCHyp_arc_generic`
- **Type**: `{H : ℝ} (hH : 1 < H) (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) {θ₀ : ℝ} (h_lo : π/3 < θ₀) (h_hi : θ₀ < 2π/3) : ArcFTCHyp γ (exp (↑θ₀ * I)) (arcT₀ θ₀) arcsinDelta (arcThreshold H θ₀) (-(↑π * I))`
- **What**: The main public API: the `ArcFTCHyp` structure at any smooth arc point `z₀ = exp(iθ₀)`, packaging `arc_E`, the integral identity, both integrability witnesses, and the limit `-π·I`.
- **How**: Structure-construction combining `arc_h_ftc_helper`, `arc_hint_left_helper`, `arc_hint_right_helper`, `arc_E_tendsto`.
- **Hypotheses**: `1 < H`, γ agrees with `fdBoundaryFun`, `π/3 < θ₀ < 2π/3`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `arcT₀`, `arcsinDelta`, `arcThreshold`, `ArcFTCHyp`, `arc_E`, `arc_h_ftc_helper`, `arc_hint_left_helper`, `arc_hint_right_helper`, `arc_E_tendsto`
- **Used by**: unused in file
- **Visibility**: public (def)
- **Lines**: 928-938
- **Notes**: none

---

## File Summary

- **Total declarations**: 41 (5 `def`, 36 `lemma`/`theorem`)
- **Public API**: `fdBoundary_ftc_telescope_arc_aux` (intermediate, exposed as theorem), `arcFTCHyp_arc_generic` (main entry point)
- **Unused in file**: `arcFTCHyp_arc_generic` is the terminal export (no consumers in this file)
- **Sorries**: 0
- **set_options**: `maxHeartbeats 4000000` on `arc_hint_left_helper`, `maxHeartbeats 8000000` on `arc_hint_right_helper`
- **Long proofs (>10 lines)**: 21 lemmas (notably `fdBoundary_ftc_telescope_arc_aux` ~106 lines, `arc_log_diff_tendsto` ~79 lines, `arc_h_arc_ratio_eq` ~44 lines, `arc_hint_right_helper` ~37 lines)
- **Purpose**: This file constructs the analytic FTC-hypothesis bundle `ArcFTCHyp` for the unit-circle arc portion of the fundamental-domain boundary at a generic non-elliptic, non-`i` arc point `z₀ = exp(iθ₀)` with `θ₀ ∈ (π/3, 2π/3) \ {π/2}`. The construction defines a slit-plane-valued reference function on each of the five fundamental-domain boundary segments (seg1, left arc, right arc, seg4, seg5), proves per-segment FTC and a.e. identifications with the boundary log-derivative, computes the junction equalities and the single `-π·I` branch-jump at the 4/5 corner, and shows that the crossing log-difference vanishes as the crossing window δ → 0. The terminal `arcFTCHyp_arc_generic` packages all of this into an `ArcFTCHyp` structure with limit `-π·I`, axiom-clean.
