# Seg1FTCProvider.lean — Inventory

### `private def seg1_h₀`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ`
- **What**: Seg1 reference function: `((H - 5t(H - √3/2) - z₀.im) : ℝ)·I + ((1/2 - z₀.re) : ℝ)`; matches `fdBoundaryFun H t - z₀` on seg1.
- **How**: Literal construction.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `seg1_h₀_eq_pure_im`, `fdBoundary_sub_eq_seg1_h₀`, `seg1_h₀_contDiff`, `hasDerivAt_seg1_h₀`, `seg1_h₀_continuous`, `deriv_seg1_h₀`, `neg_seg1_h₀_left_slitPlane`, `neg_seg1_h₀_right_slitPlane`, `seg1_left_ftc`, `seg1_right_ftc`, `seg1_junction_15`, `seg1_closed`, `seg1_log_diff_eq_neg_pi_I`, `ae_eq_seg1_h₀`, `fdBoundary_ftc_telescope_seg1`, `arcFTCHyp_seg1`
- **Visibility**: private
- **Lines**: 50–51
- **Notes**: noncomputable section.

### `private lemma seg1_h₀_eq_pure_im`
- **Type**: `{H : ℝ} {z₀ : ℂ} (hz_re : z₀.re = 1/2) (t : ℝ) : seg1_h₀ H z₀ t = ((H - 5t(H - √3/2) - z₀.im) : ℝ) * I`
- **What**: When `z₀.re = 1/2`, the seg1 reference reduces to a pure-imaginary multiple of `I`.
- **How**: Unfold; rewrite `1/2 - z₀.re = 0` (using `hz_re`); `simp`.
- **Hypotheses**: `z₀.re = 1/2`.
- **Uses from project**: `seg1_h₀`
- **Used by**: `neg_seg1_h₀_left_slitPlane`, `neg_seg1_h₀_right_slitPlane`, `seg1_log_diff_eq_neg_pi_I`
- **Visibility**: private
- **Lines**: 54–58

### `private lemma fdBoundary_sub_eq_seg1_h₀`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) (ht : t ≤ 1/5) : fdBoundaryFun H t - z₀ = seg1_h₀ H z₀ t`
- **What**: On seg1 (`t ≤ 1/5`), `fdBoundaryFun H t - z₀ = seg1_h₀ H z₀ t`.
- **How**: `simp` with `fdBoundaryFun`, `ite_true` (via `ht`), `seg1_h₀`, then `Complex.ext` + `simp`.
- **Hypotheses**: `t ≤ 1/5`.
- **Uses from project**: `seg1_h₀`, `fdBoundaryFun`
- **Used by**: `ae_eq_seg1_h₀`
- **Visibility**: private
- **Lines**: 61–64

### `private lemma seg1_h₀_contDiff`
- **Type**: `(H : ℝ) (z₀ : ℂ) : ContDiff ℝ ⊤ (seg1_h₀ H z₀)`
- **What**: `seg1_h₀ H z₀` is smooth.
- **How**: Real piece smooth (`fun_prop`); complexify via `Complex.ofRealCLM.contDiff.comp`; product with `I` and add constant.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h₀`
- **Used by**: `seg1_h₀_continuous`
- **Visibility**: private
- **Lines**: 66–73

### `private lemma hasDerivAt_seg1_h₀`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : HasDerivAt (seg1_h₀ H z₀) (-(seg1Speed H : ℂ) * I) t`
- **What**: The derivative of `seg1_h₀ H z₀` is `-seg1Speed H · I`.
- **How**: Build `HasDerivAt` on the real linear inner function (chain `hasDerivAt_id.const_mul` + `mul_const` + `sub_const`); `ofReal_comp`; multiply by `I`; add constant; `congr_deriv`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h₀`, `seg1Speed`
- **Used by**: `deriv_seg1_h₀`, `seg1_left_ftc`, `seg1_right_ftc`
- **Visibility**: private
- **Lines**: 75–89

### `private lemma seg1_h₀_continuous`
- **Type**: `(H : ℝ) (z₀ : ℂ) : Continuous (seg1_h₀ H z₀)`
- **What**: `seg1_h₀ H z₀` is continuous.
- **How**: `seg1_h₀_contDiff.continuous`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h₀`, `seg1_h₀_contDiff`
- **Used by**: `seg1_left_ftc`, `seg1_right_ftc`
- **Visibility**: private
- **Lines**: 91–92

### `private lemma deriv_seg1_h₀`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : deriv (seg1_h₀ H z₀) t = -(seg1Speed H : ℂ) * I`
- **What**: The pointwise derivative of `seg1_h₀ H z₀`.
- **How**: `hasDerivAt_seg1_h₀.deriv`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h₀`, `seg1Speed`, `hasDerivAt_seg1_h₀`
- **Used by**: `seg1_left_ftc`, `seg1_right_ftc`
- **Visibility**: private
- **Lines**: 94–96

### `private lemma neg_seg1_h₀_left_slitPlane`
- **Type**: `{H : ℝ} (hH : √3/2 < H) {z₀ : ℂ} (hz_re : z₀.re = 1/2) {δ : ℝ} (hδ_pos : 0 < δ) {t : ℝ} (htd : t ≤ seg1T₀ H z₀.im - δ) : -(seg1_h₀ H z₀ t) ∈ Complex.slitPlane`
- **What**: For `t` strictly left of the crossing on seg1, `-(γ - z₀)` is in `slitPlane` (nonzero imaginary part).
- **How**: Right-branch of `mem_slitPlane_iff`; reduce to `im ≠ 0` via `seg1_h₀_eq_pure_im`; if equal, use `seg1Speed_mul_t₀` and `seg1Speed_pos` to derive `t = seg1T₀`, contradicting `t ≤ t₀ - δ` with `linarith`.
- **Hypotheses**: `H > √3/2`, `z₀.re = 1/2`, `δ > 0`, `t ≤ t₀ - δ`.
- **Uses from project**: `seg1_h₀`, `seg1_h₀_eq_pure_im`, `seg1T₀`, `seg1Speed`, `seg1Speed_pos`, `seg1Speed_mul_t₀`
- **Used by**: `seg1_left_ftc`
- **Visibility**: private
- **Lines**: 102–118

### `private lemma neg_seg1_h₀_right_slitPlane`
- **Type**: `{H : ℝ} (hH : √3/2 < H) {z₀ : ℂ} (hz_re : z₀.re = 1/2) {δ : ℝ} (hδ_pos : 0 < δ) {t : ℝ} (htd : seg1T₀ H z₀.im + δ ≤ t) : -(seg1_h₀ H z₀ t) ∈ Complex.slitPlane`
- **What**: For `t` strictly right of the crossing on seg1, `-(γ - z₀)` is in `slitPlane`.
- **How**: Mirror of left case: `seg1_h₀_eq_pure_im`; equality leads to `t = seg1T₀` via `seg1Speed_mul_t₀`, contradicting `t₀ + δ ≤ t`.
- **Hypotheses**: same as left, with `t₀ + δ ≤ t`.
- **Uses from project**: `seg1_h₀`, `seg1_h₀_eq_pure_im`, `seg1T₀`, `seg1Speed`, `seg1Speed_pos`, `seg1Speed_mul_t₀`
- **Used by**: `seg1_right_ftc`
- **Visibility**: private
- **Lines**: 122–137

### `private def seg1_h_arc`
- **Type**: `(z₀ : ℂ) (t : ℝ) : ℂ`
- **What**: Arc reference: `exp(i · fdArcAngle t) - z₀`.
- **How**: Literal `exp (↑(fdArcAngle t) * I) - z₀`.
- **Hypotheses**: None.
- **Uses from project**: `fdArcAngle`
- **Used by**: `fdBoundary_sub_eq_seg1_h_arc`, `seg1_h_arc_continuous`, `hasDerivAt_seg1_h_arc`, `deriv_seg1_h_arc`, `neg_seg1_h_arc_slitPlane`, `seg1_arc_ftc`, `seg1_junction_15`, `seg1_junction_35`, `ae_eq_seg1_h_arc`, `fdBoundary_ftc_telescope_seg1`, `arcFTCHyp_seg1`
- **Visibility**: private
- **Lines**: 142–143

### `private lemma fdBoundary_sub_eq_seg1_h_arc`
- **Type**: `{H : ℝ} (z₀ : ℂ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) : fdBoundaryFun H t - z₀ = seg1_h_arc z₀ t`
- **What**: On the arc (`1/5 < t ≤ 3/5`), `fdBoundaryFun H t - z₀ = seg1_h_arc z₀ t`.
- **How**: Unfold; apply `fdBoundaryFun_arc_eq_exp`.
- **Hypotheses**: `1/5 < t ≤ 3/5`.
- **Uses from project**: `seg1_h_arc`, `fdBoundaryFun`, `fdBoundaryFun_arc_eq_exp`
- **Used by**: `ae_eq_seg1_h_arc`
- **Visibility**: private
- **Lines**: 145–149

### `private lemma seg1_h_arc_continuous`
- **Type**: `(z₀ : ℂ) : Continuous (seg1_h_arc z₀)`
- **What**: The arc reference is continuous.
- **How**: Compose `Complex.continuous_exp`, `Complex.continuous_ofReal`, `fdArcAngle_continuous`, `continuous_const`, and `.sub continuous_const`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h_arc`, `fdArcAngle`, `fdArcAngle_continuous`
- **Used by**: `seg1_arc_ftc`
- **Visibility**: private
- **Lines**: 151–155

### `private lemma hasDerivAt_seg1_h_arc`
- **Type**: `(z₀ : ℂ) (t : ℝ) : HasDerivAt (seg1_h_arc z₀) (↑(5π/6) * I * exp (↑(fdArcAngle t) * I)) t`
- **What**: Derivative of the arc reference: `(5π/6) · I · exp(i · fdArcAngle t)`.
- **How**: Compute `HasDerivAt fdArcAngle (5π/6)` by `hasDerivAt_id.const_mul.sub_const` chain (after unfolding `fdArcAngle`); complexify via `ofReal_comp`; multiply by `I`; compose with `exp`; subtract `z₀`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h_arc`, `fdArcAngle`
- **Used by**: `deriv_seg1_h_arc`, `seg1_arc_ftc`
- **Visibility**: private
- **Lines**: 157–177
- **Notes**: >10 lines; key step `hasDerivAt_exp _ .comp t`.

### `private lemma deriv_seg1_h_arc`
- **Type**: `(z₀ : ℂ) (t : ℝ) : deriv (seg1_h_arc z₀) t = ↑(5π/6) * I * exp (↑(fdArcAngle t) * I)`
- **What**: Pointwise derivative formula.
- **How**: `hasDerivAt_seg1_h_arc.deriv`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h_arc`, `fdArcAngle`, `hasDerivAt_seg1_h_arc`
- **Used by**: `seg1_arc_ftc`
- **Visibility**: private
- **Lines**: 179–181

### `private lemma neg_seg1_h_arc_slitPlane`
- **Type**: `{z₀ : ℂ} (hz_re : z₀.re = 1/2) (hc_lo : √3/2 < z₀.im) {t : ℝ} (ht1 : 1/5 ≤ t) (ht3 : t ≤ 3/5) : -(seg1_h_arc z₀ t) ∈ Complex.slitPlane`
- **What**: On the arc (with `z₀ = 1/2 + c·I`, `c > √3/2`), `-(γ - z₀)` is in `slitPlane`.
- **How**: Case split on `t = 1/5` (then `γ = ρ+1`: positive imaginary part `z₀.im - √3/2 > 0`) vs `t > 1/5` (use `Real.strictAntiOn_cos` on `[0, π]` with `π/3 < fdArcAngle t` to get `cos(fdArcAngle t) < 1/2`, hence `re < 0`).
- **Hypotheses**: `z₀.re = 1/2`, `√3/2 < z₀.im`, `1/5 ≤ t ≤ 3/5`.
- **Uses from project**: `seg1_h_arc`, `fdArcAngle`
- **Used by**: `seg1_arc_ftc`
- **Visibility**: private
- **Lines**: 186–219
- **Notes**: >10 lines; uses `exp_mul_I`, `Real.cos_pi_div_three`, `Real.sin_pi_div_three`, `Real.strictAntiOn_cos`.

### `private def seg1_h₃`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ`
- **What**: Seg4 reference: `(-1/2 - z₀.re) + ((√3/2 + (5t - 3)(H - √3/2) - z₀.im)) · I`.
- **How**: Direct construction.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `fdBoundary_sub_eq_seg1_h₃`, `seg1_h₃_continuous`, `hasDerivAt_seg1_h₃`, `deriv_seg1_h₃`, `neg_seg1_h₃_slitPlane`, `seg1_seg4_ftc`, `seg1_junction_35`, `seg1_junction_45`, `ae_eq_seg1_h₃`, `fdBoundary_ftc_telescope_seg1`, `arcFTCHyp_seg1`
- **Visibility**: private
- **Lines**: 224–226

### `private lemma fdBoundary_sub_eq_seg1_h₃`
- **Type**: `(H : ℝ) (z₀ : ℂ) {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) : fdBoundaryFun H t - z₀ = seg1_h₃ H z₀ t`
- **What**: On seg4, `fdBoundaryFun H t - z₀ = seg1_h₃ H z₀ t`.
- **How**: Unfold `fdBoundaryFun`, discharge all `¬t ≤ 1/5`, `¬t ≤ 2/5`, `¬t ≤ 3/5` by `linarith`; close with `Complex.ext` + `simp`.
- **Hypotheses**: `3/5 < t ≤ 4/5`.
- **Uses from project**: `seg1_h₃`, `fdBoundaryFun`
- **Used by**: `ae_eq_seg1_h₃`
- **Visibility**: private
- **Lines**: 228–234

### `private lemma seg1_h₃_continuous`
- **Type**: `(H : ℝ) (z₀ : ℂ) : Continuous (seg1_h₃ H z₀)`
- **What**: Continuity of the seg4 reference.
- **How**: `Continuous.add continuous_const ((continuous_ofReal.comp fun_prop).mul continuous_const)`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h₃`
- **Used by**: `seg1_seg4_ftc`
- **Visibility**: private
- **Lines**: 236–240

### `private lemma hasDerivAt_seg1_h₃`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : HasDerivAt (seg1_h₃ H z₀) ((seg1Speed H : ℂ) * I) t`
- **What**: Derivative of `seg1_h₃ H z₀` is `seg1Speed H · I`.
- **How**: Build `HasDerivAt` on real `5s - 3`; multiply by `(H - √3/2)`; add `√3/2`; subtract `z₀.im`; `ofReal_comp`; multiply by `I`; add `((-1/2 - z₀.re) : ℂ)`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h₃`, `seg1Speed`
- **Used by**: `deriv_seg1_h₃`, `seg1_seg4_ftc`
- **Visibility**: private
- **Lines**: 242–257
- **Notes**: >10 lines.

### `private lemma deriv_seg1_h₃`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : deriv (seg1_h₃ H z₀) t = (seg1Speed H : ℂ) * I`
- **What**: Pointwise derivative formula.
- **How**: `.deriv` of `hasDerivAt_seg1_h₃`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h₃`, `seg1Speed`, `hasDerivAt_seg1_h₃`
- **Used by**: `seg1_seg4_ftc`
- **Visibility**: private
- **Lines**: 259–261

### `private lemma neg_seg1_h₃_slitPlane`
- **Type**: `{H : ℝ} {z₀ : ℂ} (hz_re : z₀.re = 1/2) (t : ℝ) : -(seg1_h₃ H z₀ t) ∈ Complex.slitPlane`
- **What**: For `z₀.re = 1/2`, `-(seg4 - z₀)` has `re = 1 > 0`, so in `slitPlane`.
- **How**: Left branch of `mem_slitPlane_iff`; unfold and simplify `re`; substitute `hz_re`; `norm_num`.
- **Hypotheses**: `z₀.re = 1/2`.
- **Uses from project**: `seg1_h₃`
- **Used by**: `seg1_seg4_ftc`
- **Visibility**: private
- **Lines**: 264–272

### `private def seg1_h₅`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ`
- **What**: Seg5 reference: `((5t - 9/2 - z₀.re) : ℝ) + ((H - z₀.im) : ℝ) · I`.
- **How**: Direct construction.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `fdBoundary_sub_eq_seg1_h₅`, `seg1_h₅_continuous`, `hasDerivAt_seg1_h₅`, `deriv_seg1_h₅`, `neg_seg1_h₅_slitPlane`, `seg1_seg5_ftc`, `seg1_junction_45`, `seg1_closed`, `ae_eq_seg1_h₅`, `fdBoundary_ftc_telescope_seg1`, `arcFTCHyp_seg1`
- **Visibility**: private
- **Lines**: 277–278

### `private lemma fdBoundary_sub_eq_seg1_h₅`
- **Type**: `(H : ℝ) (z₀ : ℂ) {t : ℝ} (ht : 4/5 < t) : fdBoundaryFun H t - z₀ = seg1_h₅ H z₀ t`
- **What**: On seg5 (`t > 4/5`), `fdBoundaryFun H t - z₀ = seg1_h₅ H z₀ t`.
- **How**: Unfold `fdBoundaryFun`, discharge `¬t ≤ 1/5`, `¬t ≤ 2/5`, `¬t ≤ 3/5`, `¬t ≤ 4/5` by `linarith`; `Complex.ext` + `simp`.
- **Hypotheses**: `t > 4/5`.
- **Uses from project**: `seg1_h₅`, `fdBoundaryFun`
- **Used by**: `ae_eq_seg1_h₅`
- **Visibility**: private
- **Lines**: 280–285

### `private lemma seg1_h₅_continuous`
- **Type**: `(H : ℝ) (z₀ : ℂ) : Continuous (seg1_h₅ H z₀)`
- **What**: Continuity of seg5 reference.
- **How**: `Continuous.add (continuous_ofReal.comp fun_prop) continuous_const`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h₅`
- **Used by**: `seg1_seg5_ftc`
- **Visibility**: private
- **Lines**: 287–290

### `private lemma hasDerivAt_seg1_h₅`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : HasDerivAt (seg1_h₅ H z₀) (5 : ℂ) t`
- **What**: Derivative of `seg1_h₅ H z₀` is `5`.
- **How**: Build real `HasDerivAt (5s - 9/2 - z₀.re) 5`; `ofReal_comp`; add constant.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h₅`
- **Used by**: `deriv_seg1_h₅`, `seg1_seg5_ftc`
- **Visibility**: private
- **Lines**: 292–298

### `private lemma deriv_seg1_h₅`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : deriv (seg1_h₅ H z₀) t = 5`
- **What**: Pointwise derivative formula.
- **How**: `.deriv` of `hasDerivAt_seg1_h₅`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h₅`, `hasDerivAt_seg1_h₅`
- **Used by**: `seg1_seg5_ftc`
- **Visibility**: private
- **Lines**: 300–302

### `private lemma neg_seg1_h₅_slitPlane`
- **Type**: `{H : ℝ} {z₀ : ℂ} (hc_hi : z₀.im < H) (t : ℝ) : -(seg1_h₅ H z₀ t) ∈ Complex.slitPlane`
- **What**: For `z₀.im < H`, `-(seg5 - z₀)` has negative imaginary part, in `slitPlane`.
- **How**: Right branch of `mem_slitPlane_iff`; simplify `im` of `seg1_h₅`; `linarith`.
- **Hypotheses**: `z₀.im < H`.
- **Uses from project**: `seg1_h₅`
- **Used by**: `seg1_seg5_ftc`
- **Visibility**: private
- **Lines**: 305–313

### `private lemma seg1_left_ftc`
- **Type**: `{H : ℝ} (hH : √3/2 < H) {z₀ : ℂ} (hz_re : z₀.re = 1/2) {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_t₀ : δ < seg1T₀ H z₀.im) : IntervalIntegrable (deriv (seg1_h₀ H z₀) / seg1_h₀ H z₀) volume 0 (seg1T₀ H z₀.im - δ) ∧ ∫ t ... = Complex.log (-(seg1_h₀ H z₀ (t₀ - δ))) - Complex.log (-(seg1_h₀ H z₀ 0))`
- **What**: FTC for the seg1 left half `[0, t₀ - δ]`, giving log of negation at endpoints.
- **How**: Apply `LogDerivFTC.ftc_log_neg_on_segment` with: continuity (`seg1_h₀_continuous`), differentiability (`hasDerivAt_seg1_h₀ ... .differentiableAt`), continuous deriv (`deriv_seg1_h₀` + `continuousOn_const`); slitPlane via `neg_seg1_h₀_left_slitPlane`.
- **Hypotheses**: `H > √3/2`, `z₀.re = 1/2`, `0 < δ < seg1T₀`.
- **Uses from project**: `seg1_h₀`, `seg1T₀`, `LogDerivFTC.ftc_log_neg_on_segment`, `seg1_h₀_continuous`, `hasDerivAt_seg1_h₀`, `deriv_seg1_h₀`, `neg_seg1_h₀_left_slitPlane`
- **Used by**: `fdBoundary_ftc_telescope_seg1`, `arcFTCHyp_seg1`
- **Visibility**: private
- **Lines**: 318–332

### `private lemma seg1_right_ftc`
- **Type**: `{H : ℝ} (hH : √3/2 < H) {z₀ : ℂ} (hz_re : z₀.re = 1/2) {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 1/5 - seg1T₀ H z₀.im) : IntervalIntegrable ... ∧ ∫ t ... = Complex.log (-(seg1_h₀ H z₀ (1/5))) - Complex.log (-(seg1_h₀ H z₀ (t₀ + δ)))`
- **What**: FTC for the seg1 right half `[t₀ + δ, 1/5]`.
- **How**: Mirror of `seg1_left_ftc`: apply `LogDerivFTC.ftc_log_neg_on_segment` with `neg_seg1_h₀_right_slitPlane`.
- **Hypotheses**: `H > √3/2`, `z₀.re = 1/2`, `0 < δ < 1/5 - seg1T₀`.
- **Uses from project**: `seg1_h₀`, `seg1T₀`, `LogDerivFTC.ftc_log_neg_on_segment`, `seg1_h₀_continuous`, `hasDerivAt_seg1_h₀`, `deriv_seg1_h₀`, `neg_seg1_h₀_right_slitPlane`
- **Used by**: `fdBoundary_ftc_telescope_seg1`, `arcFTCHyp_seg1`
- **Visibility**: private
- **Lines**: 335–349

### `private lemma seg1_arc_ftc`
- **Type**: `{z₀ : ℂ} (hz_re : z₀.re = 1/2) (hc_lo : √3/2 < z₀.im) : IntervalIntegrable (deriv (seg1_h_arc z₀) / seg1_h_arc z₀) volume (1/5) (3/5) ∧ ∫ t ... = log(-(seg1_h_arc z₀ (3/5))) - log(-(seg1_h_arc z₀ (1/5)))`
- **What**: FTC for the arc `[1/5, 3/5]`.
- **How**: `LogDerivFTC.ftc_log_neg_on_segment` with `seg1_h_arc_continuous`, `hasDerivAt_seg1_h_arc`, `deriv_seg1_h_arc`; continuous deriv via composition of `continuous_exp` with `fdArcAngle_continuous`; slitPlane via `neg_seg1_h_arc_slitPlane`.
- **Hypotheses**: `z₀.re = 1/2`, `z₀.im > √3/2`.
- **Uses from project**: `seg1_h_arc`, `LogDerivFTC.ftc_log_neg_on_segment`, `seg1_h_arc_continuous`, `hasDerivAt_seg1_h_arc`, `deriv_seg1_h_arc`, `fdArcAngle_continuous`, `neg_seg1_h_arc_slitPlane`
- **Used by**: `fdBoundary_ftc_telescope_seg1`, `arcFTCHyp_seg1`
- **Visibility**: private
- **Lines**: 352–368

### `private lemma seg1_seg4_ftc`
- **Type**: `(H : ℝ) {z₀ : ℂ} (hz_re : z₀.re = 1/2) : IntervalIntegrable ... volume (3/5) (4/5) ∧ ∫ ... = log(-(seg1_h₃ H z₀ (4/5))) - log(-(seg1_h₃ H z₀ (3/5)))`
- **What**: FTC for seg4 `[3/5, 4/5]`.
- **How**: `LogDerivFTC.ftc_log_neg_on_segment` with `seg1_h₃_continuous`, `hasDerivAt_seg1_h₃`, `deriv_seg1_h₃`; slitPlane via `neg_seg1_h₃_slitPlane`.
- **Hypotheses**: `z₀.re = 1/2`.
- **Uses from project**: `seg1_h₃`, `LogDerivFTC.ftc_log_neg_on_segment`, `seg1_h₃_continuous`, `hasDerivAt_seg1_h₃`, `deriv_seg1_h₃`, `neg_seg1_h₃_slitPlane`
- **Used by**: `fdBoundary_ftc_telescope_seg1`, `arcFTCHyp_seg1`
- **Visibility**: private
- **Lines**: 371–383

### `private lemma seg1_seg5_ftc`
- **Type**: `(H : ℝ) {z₀ : ℂ} (hc_hi : z₀.im < H) : IntervalIntegrable ... volume (4/5) 1 ∧ ∫ ... = log(-(seg1_h₅ H z₀ 1)) - log(-(seg1_h₅ H z₀ (4/5)))`
- **What**: FTC for seg5 `[4/5, 1]`.
- **How**: `LogDerivFTC.ftc_log_neg_on_segment` with `seg1_h₅_continuous`, `hasDerivAt_seg1_h₅`, `deriv_seg1_h₅`; slitPlane via `neg_seg1_h₅_slitPlane`.
- **Hypotheses**: `z₀.im < H`.
- **Uses from project**: `seg1_h₅`, `LogDerivFTC.ftc_log_neg_on_segment`, `seg1_h₅_continuous`, `hasDerivAt_seg1_h₅`, `deriv_seg1_h₅`, `neg_seg1_h₅_slitPlane`
- **Used by**: `fdBoundary_ftc_telescope_seg1`, `arcFTCHyp_seg1`
- **Visibility**: private
- **Lines**: 386–398

### `private lemma seg1_junction_15`
- **Type**: `(H : ℝ) (z₀ : ℂ) : seg1_h₀ H z₀ (1/5) = seg1_h_arc z₀ (1/5)`
- **What**: Continuity at the seg1-arc junction `t = 1/5`.
- **How**: Unfold; `fdArcAngle (1/5) = π/3`; expand `exp_mul_I` via `cos_pi_div_three`, `sin_pi_div_three`; `Complex.ext` + `simp`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h₀`, `seg1_h_arc`, `fdArcAngle`
- **Used by**: `fdBoundary_ftc_telescope_seg1`
- **Visibility**: private
- **Lines**: 403–408

### `private lemma seg1_junction_35`
- **Type**: `(H : ℝ) (z₀ : ℂ) : seg1_h_arc z₀ (3/5) = seg1_h₃ H z₀ (3/5)`
- **What**: Continuity at the arc-seg4 junction `t = 3/5`.
- **How**: `fdArcAngle (3/5) = 2π/3`; rewrite `cos(π - π/3)`, `sin(π - π/3)`; `Complex.ext` + `simp` + `ring` on both components.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h_arc`, `seg1_h₃`, `fdArcAngle`
- **Used by**: `fdBoundary_ftc_telescope_seg1`
- **Visibility**: private
- **Lines**: 411–424
- **Notes**: >10 lines; uses `Real.cos_pi_sub`, `Real.sin_pi_sub`.

### `private lemma seg1_junction_45`
- **Type**: `(H : ℝ) (z₀ : ℂ) : seg1_h₃ H z₀ (4/5) = seg1_h₅ H z₀ (4/5)`
- **What**: Continuity at the seg4-seg5 junction `t = 4/5`.
- **How**: Unfold; `Complex.ext` + `simp` + `ring`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h₃`, `seg1_h₅`
- **Used by**: `fdBoundary_ftc_telescope_seg1`
- **Visibility**: private
- **Lines**: 427–430

### `private lemma seg1_closed`
- **Type**: `(H : ℝ) (z₀ : ℂ) : seg1_h₀ H z₀ 0 = seg1_h₅ H z₀ 1`
- **What**: Closed-curve identity at `t = 0` and `t = 1`.
- **How**: Unfold; `Complex.ext` + `simp` + `ring`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h₀`, `seg1_h₅`
- **Used by**: `fdBoundary_ftc_telescope_seg1`
- **Visibility**: private
- **Lines**: 433–437

### `private lemma seg1_log_diff_eq_neg_pi_I`
- **Type**: `{H : ℝ} (hH : √3/2 < H) {z₀ : ℂ} (hz_re : z₀.re = 1/2) {δ : ℝ} (hδ_pos : 0 < δ) : Complex.log(-(seg1_h₀ H z₀ (t₀ - δ))) - Complex.log(-(seg1_h₀ H z₀ (t₀ + δ))) = -(π · I)`
- **What**: Sum of log differences around the crossing telescopes to `-π·I`.
- **How**: Compute `seg1_h₀(t₀ ± δ) = ±Kδ · I` using `seg1Speed_mul_t₀`; rewrite negations to factor `I`/`-I`; apply `Complex.log_ofReal_mul` with positive `Kδ`; use `Complex.log_I` and `Complex.log_neg_I`; close with `ring`.
- **Hypotheses**: `H > √3/2`, `z₀.re = 1/2`, `δ > 0`.
- **Uses from project**: `seg1_h₀`, `seg1_h₀_eq_pure_im`, `seg1T₀`, `seg1Speed`, `seg1Speed_pos`, `seg1Speed_mul_t₀`
- **Used by**: `fdBoundary_ftc_telescope_seg1`
- **Visibility**: private
- **Lines**: 442–471
- **Notes**: >10 lines; key step `Complex.log_ofReal_mul`.

### `private lemma ae_eq_seg1_h₀`
- **Type**: `(H : ℝ) (z₀ : ℂ) {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 1/5) : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t = deriv (seg1_h₀ H z₀) t / seg1_h₀ H z₀ t`
- **What**: A.e. equality between the inverse-shifted PV integrand and the seg1 log derivative on `(a, b]` (`b ≤ 1/5`).
- **How**: Exclude the endpoint `b` via `compl_mem_ae_iff.mpr (measure_singleton b)`; for `t ≠ b` in `(a, b]`, get `t < 1/5`; use `fdBoundary_sub_eq_seg1_h₀ H z₀ t ht_lt.le` plus `EventuallyEq.deriv_eq` to identify derivatives; convert via `div_eq_mul_inv` + `mul_comm`.
- **Hypotheses**: `a ≤ b ≤ 1/5`.
- **Uses from project**: `seg1_h₀`, `fdBoundaryFun`, `fdBoundary_sub_eq_seg1_h₀`
- **Used by**: `fdBoundary_ftc_telescope_seg1`, `arcFTCHyp_seg1`
- **Visibility**: private
- **Lines**: 477–489

### `private lemma ae_eq_seg1_h_arc`
- **Type**: `(H : ℝ) (z₀ : ℂ) : ∀ᵐ t ∂volume, t ∈ Set.uIoc (1/5) (3/5) → (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t = deriv (seg1_h_arc z₀) t / seg1_h_arc z₀ t`
- **What**: Same a.e. identity, on the arc `(1/5, 3/5)`.
- **How**: Exclude endpoint `3/5`; for `t ∈ (1/5, 3/5)` use `fdBoundary_sub_eq_seg1_h_arc` and `EventuallyEq.deriv_eq` on `Ioo`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h_arc`, `fdBoundaryFun`, `fdBoundary_sub_eq_seg1_h_arc`
- **Used by**: `fdBoundary_ftc_telescope_seg1`, `arcFTCHyp_seg1`
- **Visibility**: private
- **Lines**: 492–505

### `private lemma ae_eq_seg1_h₃`
- **Type**: `(H : ℝ) (z₀ : ℂ) : ∀ᵐ t ∂volume, t ∈ Set.uIoc (3/5) (4/5) → ...`
- **What**: A.e. identity on seg4 `(3/5, 4/5)`.
- **How**: Mirror of arc case, with `fdBoundary_sub_eq_seg1_h₃`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h₃`, `fdBoundaryFun`, `fdBoundary_sub_eq_seg1_h₃`
- **Used by**: `fdBoundary_ftc_telescope_seg1`, `arcFTCHyp_seg1`
- **Visibility**: private
- **Lines**: 508–521

### `private lemma ae_eq_seg1_h₅`
- **Type**: `(H : ℝ) (z₀ : ℂ) : ∀ᵐ t ∂volume, t ∈ Set.uIoc (4/5) 1 → ...`
- **What**: A.e. identity on seg5 `(4/5, 1)`.
- **How**: No endpoint exclusion needed (covered everywhere on `(4/5, 1]`); use `fdBoundary_sub_eq_seg1_h₅`.
- **Hypotheses**: None.
- **Uses from project**: `seg1_h₅`, `fdBoundaryFun`, `fdBoundary_sub_eq_seg1_h₅`
- **Used by**: `fdBoundary_ftc_telescope_seg1`, `arcFTCHyp_seg1`
- **Visibility**: private
- **Lines**: 524–534

### `theorem fdBoundary_ftc_telescope_seg1`
- **Type**: `{H : ℝ} (hH : √3/2 < H) {z₀ : ℂ} (hz_re : z₀.re = 1/2) (hc_lo : √3/2 < z₀.im) (hc_hi : z₀.im < H) {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_t₀ : δ < seg1T₀ H z₀.im) (hδ_lt_one_fifth_sub : δ < 1/5 - seg1T₀ H z₀.im) : (∫ t in 0..(seg1T₀ - δ), (fdBoundary - z₀)⁻¹ · γ') + (∫ t in (seg1T₀ + δ)..1, ...) = -(π · I)`
- **What**: Full FTC telescope: the trimmed integral around the seg1 crossing equals `-π · I` (independent of `δ`).
- **How**: Aggregate `seg1_left_ftc`, `seg1_right_ftc`, `seg1_arc_ftc`, `seg1_seg4_ftc`, `seg1_seg5_ftc`; convert each to PV integrand via `intervalIntegral.integral_congr_ae` and the four `ae_eq_seg1_h*` lemmas; build integrability for adjacent splits; chain `intervalIntegral.integral_add_adjacent_intervals` three times to get `∫_{t₀+δ}^1 = ∫_{t₀+δ}^{1/5} + ∫_{1/5}^{3/5} + ∫_{3/5}^{4/5} + ∫_{4/5}^1`; rewrite junction equalities (`seg1_junction_15`, `seg1_junction_35`, `seg1_junction_45`, `seg1_closed`); cancel via algebraic `ring`; finish with `seg1_log_diff_eq_neg_pi_I`.
- **Hypotheses**: `H > √3/2`, `z₀.re = 1/2`, `√3/2 < z₀.im < H`, `0 < δ` strictly inside the safety window on both sides.
- **Uses from project**: `seg1_h₀`, `seg1_h_arc`, `seg1_h₃`, `seg1_h₅`, `seg1T₀`, `seg1T₀_pos`, `seg1T₀_lt_one_fifth`, `seg1_left_ftc`, `seg1_right_ftc`, `seg1_arc_ftc`, `seg1_seg4_ftc`, `seg1_seg5_ftc`, `ae_eq_seg1_h₀`, `ae_eq_seg1_h_arc`, `ae_eq_seg1_h₃`, `ae_eq_seg1_h₅`, `seg1_junction_15`, `seg1_junction_35`, `seg1_junction_45`, `seg1_closed`, `seg1_log_diff_eq_neg_pi_I`
- **Used by**: `arcFTCHyp_seg1`
- **Visibility**: public
- **Lines**: 539–637
- **Notes**: >10 lines (~100 lines); key step the `linear_combination` over three `integral_add_adjacent_intervals` results.

### `def arcFTCHyp_seg1`
- **Type**: `{H : ℝ} (hH : √3/2 < H) (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) {z₀ : ℂ} (hz_re : z₀.re = 1/2) (hc_lo : √3/2 < z₀.im) (hc_hi : z₀.im < H) : ArcFTCHyp γ z₀ (seg1T₀ H z₀.im) (linDelta (seg1Speed H)) (seg1Threshold H z₀) (-(π · I))`
- **What**: The full `ArcFTCHyp` structure at any seg1 interior crossing point, with limit `-π · I`.
- **How**: Provide structure fields:
  - `E := fun _ => -(π · I)` (constant).
  - `h_ftc`: convert `ε`-threshold info to `linDelta < seg1T₀` / `linDelta < 1/5 - seg1T₀` via `linDelta`, `seg1Speed_mul_t₀`, `seg1Speed_mul_one_fifth_sub_t₀`, `norm_sub_one_le_im_sub_sqrt3`; use `transfer_integral` (twice) to move between `γ` and `fdBoundaryFun`; apply `fdBoundary_ftc_telescope_seg1`.
  - `hint_left`: same ε bookkeeping then `transfer_integrability` + `seg1_left_ftc.1` converted via `ae_eq_seg1_h₀`.
  - `hint_right`: combine `seg1_right_ftc`, `seg1_arc_ftc`, `seg1_seg4_ftc`, `seg1_seg5_ftc` (via per-segment `ae_eq`s) and chain three `.trans` calls.
  - `h_limit := tendsto_const_nhds` (`E` is constant).
- **Hypotheses**: `H > √3/2`, `γ` is the FD-boundary path with `γ.toPath.extend = fdBoundaryFun H` on `[0,1]`, `z₀.re = 1/2`, `√3/2 < z₀.im < H`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `ArcFTCHyp`, `seg1T₀`, `seg1T₀_pos`, `seg1T₀_lt_one_fifth`, `linDelta`, `linDelta_pos`, `seg1Speed`, `seg1Speed_pos`, `seg1Speed_mul_t₀`, `seg1Speed_mul_one_fifth_sub_t₀`, `seg1Threshold`, `norm_sub_one_le_im_sub_sqrt3`, `transfer_integral`, `transfer_integrability`, `fdBoundary_ftc_telescope_seg1`, `seg1_left_ftc`, `seg1_right_ftc`, `seg1_arc_ftc`, `seg1_seg4_ftc`, `seg1_seg5_ftc`, `ae_eq_seg1_h₀`, `ae_eq_seg1_h_arc`, `ae_eq_seg1_h₃`, `ae_eq_seg1_h₅`
- **Used by**: unused in file (provides the structure for external use)
- **Visibility**: public
- **Lines**: 642–745
- **Notes**: >10 lines (~100 lines); structure body. Key external dependencies: `transfer_integral`, `transfer_integrability`, `norm_sub_one_le_im_sub_sqrt3` and the threshold/speed lemmas imported from `BoundaryWindingSeg1Proof` / `WindingWeightProofs`.

---

## File Summary
- **Totals**: 41 declarations (5 defs incl. `arcFTCHyp_seg1`, 36 lemmas/theorems).
- **Key API**: `fdBoundary_ftc_telescope_seg1` (the `-π · I` log-telescope identity around any seg1 crossing) and `arcFTCHyp_seg1` (the full `ArcFTCHyp` structure consumed downstream). Private machinery: per-segment reference functions (`seg1_h₀`, `seg1_h_arc`, `seg1_h₃`, `seg1_h₅`), their derivatives, slitPlane lemmas, FTC pieces (`seg1_left/right/arc/seg4/seg5_ftc`), junctions, and a.e. equalities (`ae_eq_seg1_h*`).
- **Unused in file**: `arcFTCHyp_seg1` (final API, consumed downstream); all other publics (`fdBoundary_ftc_telescope_seg1`) are used internally to construct `arcFTCHyp_seg1`.
- **Sorries**: none.
- **`set_option`s**: none.
- **Long proofs (>10 lines)**: `hasDerivAt_seg1_h_arc`, `neg_seg1_h_arc_slitPlane`, `hasDerivAt_seg1_h₃`, `seg1_junction_35`, `seg1_log_diff_eq_neg_pi_I`, `fdBoundary_ftc_telescope_seg1` (~100 lines), `arcFTCHyp_seg1` (~100 lines).
- **Purpose**: Builds the `ArcFTCHyp` data at any interior point of the right vertical edge (seg1) of the fundamental-domain boundary, using a linear-cutoff `δ`. The strategy: replace `fdBoundaryFun H t - z₀` by per-segment reference functions (`seg1_h₀, seg1_h_arc, seg1_h₃, seg1_h₅`) whose negations lie in `slitPlane`, then telescope `∫ deriv h / h = log(-h(b)) - log(-h(a))` via `LogDerivFTC.ftc_log_neg_on_segment` across all five pieces; junction values cancel by direct computation, leaving the seg1 left/right log difference, which equals `-π · I` independently of `δ`. The closing `arcFTCHyp_seg1` packages the FTC identity and per-side integrability with a linear `linDelta` cutoff, enabling the generic-seg1-point arc-FTC machinery used by the boundary winding/PV chain.
