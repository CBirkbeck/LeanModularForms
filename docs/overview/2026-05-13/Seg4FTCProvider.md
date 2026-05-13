# Seg4FTCProvider.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/Seg4FTCProvider.lean` (831 lines)

Imports: `LeanModularForms.ForMathlib.BoundaryWindingSeg4Proof`, `SegmentAnalysis`, `SegmentFTC`, `WindingWeightProofs`.

Opens: `Complex MeasureTheory Set Filter Topology`; scoped `Real Interval`.

### `private def seg4_h₀`
- **Type**: `(H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ`
- **What**: The reference function for seg1 piece `[0, 1/5]` shifted by `-z₀`: it sends `t ↦ (1/2 - z₀.re) + (H - 5t(H - √3/2) - z₀.im)·I`.
- **How**: Inline definition.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `fdBoundary_sub_eq_seg4_h₀`, `seg4_h₀_continuous`, `hasDerivAt_seg4_h₀`, `deriv_seg4_h₀`, `seg4_h₀_slitPlane`, `seg4_seg1_ftc`, `seg4_junction_15`, `seg4_closed`, `seg4_ae_eq_h₀`, `fdBoundary_ftc_telescope_seg4`.
- **Visibility**: private.
- **Lines**: 32–34.
- **Notes**: definition.

### `private lemma fdBoundary_sub_eq_seg4_h₀`
- **Type**: `(H z₀ t) (ht : t ≤ 1/5) : fdBoundaryFun H t - z₀ = seg4_h₀ H z₀ t`
- **What**: On `[0, 1/5]`, the shifted boundary `fdBoundary - z₀` equals the reference `seg4_h₀`.
- **How**: Unfold `fdBoundaryFun` and `seg4_h₀`, apply `Complex.ext`, simp the re/im components.
- **Hypotheses**: `t ≤ 1/5`.
- **Uses from project**: `fdBoundaryFun`, `seg4_h₀`.
- **Used by**: `seg4_ae_eq_h₀`.
- **Visibility**: private.
- **Lines**: 36–43.
- **Notes**: none.

### `private lemma seg4_h₀_continuous`
- **Type**: `(H z₀) : Continuous (seg4_h₀ H z₀)`
- **What**: `seg4_h₀ H z₀` is continuous.
- **How**: `Continuous.add` of const and product; `Complex.continuous_ofReal.comp` + `fun_prop`.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h₀`.
- **Used by**: `seg4_seg1_ftc`.
- **Visibility**: private.
- **Lines**: 45–49.
- **Notes**: none.

### `private lemma hasDerivAt_seg4_h₀`
- **Type**: `(H z₀ t) : HasDerivAt (seg4_h₀ H z₀) (-(seg1Speed H : ℂ) * I) t`
- **What**: The derivative of `seg4_h₀` is the constant `-seg1Speed(H)·I` (negative imaginary direction, matching seg1 going DOWN).
- **How**: Differentiate the real part `H - 5t(H - √3/2) - z₀.im` to get `-seg1Speed H`; lift to ℂ via `ofReal_comp`; tack on `*I`; `congr_deriv` to absorb const part of `(1/2 - z₀.re) + ...`.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h₀`, `seg1Speed`.
- **Used by**: `deriv_seg4_h₀`, `seg4_seg1_ftc`.
- **Visibility**: private.
- **Lines**: 51–66.
- **Notes**: 16 lines.

### `private lemma deriv_seg4_h₀`
- **Type**: `(H z₀ t) : deriv (seg4_h₀ H z₀) t = -(seg1Speed H : ℂ) * I`
- **What**: Derivative of `seg4_h₀` (functional form).
- **How**: `.deriv` projection of `hasDerivAt_seg4_h₀`.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h₀`, `seg1Speed`, `hasDerivAt_seg4_h₀`.
- **Used by**: `seg4_seg1_ftc`.
- **Visibility**: private.
- **Lines**: 68–70.
- **Notes**: none.

### `private def seg4_h_arc`
- **Type**: `(z₀ : ℂ) (t : ℝ) : ℂ`
- **What**: Arc reference function: `exp(↑fdArcAngle(t)·I) - z₀` — same as the seg1 case.
- **How**: Inline definition.
- **Hypotheses**: none.
- **Uses from project**: `fdArcAngle`.
- **Used by**: `fdBoundary_sub_eq_seg4_h_arc`, `seg4_h_arc_continuous`, `hasDerivAt_seg4_h_arc`, `deriv_seg4_h_arc`, `seg4_h_arc_slitPlane`, `seg4_arc_ftc`, `seg4_junction_15`, `seg4_junction_35`, `seg4_ae_eq_h_arc`, `fdBoundary_ftc_telescope_seg4`.
- **Visibility**: private.
- **Lines**: 73–74.
- **Notes**: none.

### `private lemma fdBoundary_sub_eq_seg4_h_arc`
- **Type**: `{H z₀} {t} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) : fdBoundaryFun H t - z₀ = seg4_h_arc z₀ t`
- **What**: On `(1/5, 3/5]`, `fdBoundaryFun H t - z₀ = exp(↑fdArcAngle t · I) - z₀`.
- **How**: Unfold `seg4_h_arc`; rewrite using `fdBoundaryFun_arc_eq_exp`.
- **Hypotheses**: `1/5 < t ≤ 3/5`.
- **Uses from project**: `fdBoundaryFun`, `seg4_h_arc`, `fdBoundaryFun_arc_eq_exp`.
- **Used by**: `seg4_ae_eq_h_arc`.
- **Visibility**: private.
- **Lines**: 76–80.
- **Notes**: none.

### `private lemma seg4_h_arc_continuous`
- **Type**: `(z₀) : Continuous (seg4_h_arc z₀)`
- **What**: `seg4_h_arc z₀` is continuous.
- **How**: Compose `Complex.continuous_exp`, `Complex.continuous_ofReal`, `fdArcAngle_continuous`, and constants.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h_arc`, `fdArcAngle_continuous`.
- **Used by**: `seg4_arc_ftc`.
- **Visibility**: private.
- **Lines**: 82–86.
- **Notes**: none.

### `private lemma hasDerivAt_seg4_h_arc`
- **Type**: `(z₀ t) : HasDerivAt (seg4_h_arc z₀) (↑(5π/6) · I · exp(↑fdArcAngle(t)·I)) t`
- **What**: Derivative of `seg4_h_arc` at t: chain rule gives `(5π/6)·I·exp(iθ(t))`.
- **How**: Compute `HasDerivAt fdArcAngle (5π/6)` (linear in t), then complex-lift and `.cexp.congr_deriv`.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h_arc`, `fdArcAngle`.
- **Used by**: `deriv_seg4_h_arc`, `seg4_arc_ftc`.
- **Visibility**: private.
- **Lines**: 88–103.
- **Notes**: 16 lines.

### `private lemma deriv_seg4_h_arc`
- **Type**: `(z₀ t) : deriv (seg4_h_arc z₀) t = ↑(5π/6) · I · exp(↑fdArcAngle(t)·I)`
- **What**: Functional `.deriv` of `hasDerivAt_seg4_h_arc`.
- **How**: `.deriv` projection.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h_arc`, `fdArcAngle`, `hasDerivAt_seg4_h_arc`.
- **Used by**: `seg4_arc_ftc`.
- **Visibility**: private.
- **Lines**: 105–107.
- **Notes**: none.

### `private lemma seg4_h_arc_slitPlane`
- **Type**: `{z₀} (hz_re : z₀.re = -1/2) (hc_lo : √3/2 < z₀.im) {t} (ht1 : 1/5 ≤ t) (ht3 : t ≤ 3/5) : seg4_h_arc z₀ t ∈ Complex.slitPlane`
- **What**: For z₀ on left vertical edge above √3/2, the arc reference `exp(iθ(t)) - z₀` stays in the slit plane for t in `[1/5, 3/5]` — needed so `Complex.log` is holomorphic on the image.
- **How**: Case-split on t=3/5 (where γ=ρ, then imaginary part is `sin(2π/3)-z₀.im = √3/2 - z₀.im < 0`, falls into `slitPlane` via `re=0, im<0`) vs t<3/5 (real part: `cos(θ) + 1/2 > 0` via strict cosine monotonicity on `[π/3, 2π/3)`).
- **Hypotheses**: `z₀.re=-1/2`, `√3/2 < z₀.im`, `1/5 ≤ t ≤ 3/5`.
- **Uses from project**: `seg4_h_arc`, `fdArcAngle`.
- **Used by**: `seg4_arc_ftc`.
- **Visibility**: private.
- **Lines**: 111–154.
- **Notes**: 44 lines.

### `private lemma seg4_h₀_slitPlane`
- **Type**: `{H z₀} (hz_re : z₀.re = -1/2) (t) : seg4_h₀ H z₀ t ∈ Complex.slitPlane`
- **What**: For z₀ on left vertical edge, `seg4_h₀ H z₀ t` has `re = 1/2 - z₀.re = 1 > 0`, so in slit plane.
- **How**: `mem_slitPlane_iff` + compute `re = (1/2 - z₀.re) = 1 > 0`.
- **Hypotheses**: `z₀.re=-1/2`.
- **Uses from project**: `seg4_h₀`.
- **Used by**: `seg4_seg1_ftc`.
- **Visibility**: private.
- **Lines**: 158–166.
- **Notes**: none.

### `private def seg4_h₃`
- **Type**: `(H z₀ t) : ℂ`
- **What**: Seg4 (left vertical edge) reference function: `(-1/2 - z₀.re) + (√3/2 + (5t-3)(H-√3/2) - z₀.im)·I`. This is the crossing segment containing `z₀`.
- **How**: Inline definition.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `seg4_h₃_eq_pure_im`, `fdBoundary_sub_eq_seg4_h₃`, `seg4_h₃_continuous`, `hasDerivAt_seg4_h₃`, `deriv_seg4_h₃`, `seg4_h₃_left_slitPlane`, `seg4_h₃_right_slitPlane`, `seg4_left_ftc`, `seg4_right_ftc`, `seg4_junction_35`, `seg4_junction_45`, `seg4_log_diff_eq_neg_pi_I`, `seg4_ae_eq_h₃`, `fdBoundary_ftc_telescope_seg4`.
- **Visibility**: private.
- **Lines**: 169–171.
- **Notes**: none.

### `private lemma seg4_h₃_eq_pure_im`
- **Type**: `{H z₀} (hz_re : z₀.re = -1/2) (t) : seg4_h₃ H z₀ t = ↑(√3/2 + (5t-3)(H-√3/2) - z₀.im)·I`
- **What**: When z₀ is on the left edge (re=-1/2), the real part of `seg4_h₃` vanishes, so it's purely imaginary.
- **How**: Substitute `-1/2 - z₀.re = 0` (from `hz_re`) and simp.
- **Hypotheses**: `z₀.re=-1/2`.
- **Uses from project**: `seg4_h₃`.
- **Used by**: `seg4_h₃_left_slitPlane`, `seg4_h₃_right_slitPlane`, `seg4_log_diff_eq_neg_pi_I`.
- **Visibility**: private.
- **Lines**: 174–179.
- **Notes**: none.

### `private lemma fdBoundary_sub_eq_seg4_h₃`
- **Type**: `(H z₀) {t} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) : fdBoundaryFun H t - z₀ = seg4_h₃ H z₀ t`
- **What**: On `(3/5, 4/5]`, the seg4 ref equals `fdBoundaryFun - z₀`.
- **How**: Unfold `fdBoundaryFun` and `seg4_h₃`; choose the right `ite` branch via the inequalities; `Complex.ext` and componentwise simp.
- **Hypotheses**: `3/5 < t ≤ 4/5`.
- **Uses from project**: `fdBoundaryFun`, `seg4_h₃`.
- **Used by**: `seg4_ae_eq_h₃`.
- **Visibility**: private.
- **Lines**: 181–191.
- **Notes**: 11 lines.

### `private lemma seg4_h₃_continuous`
- **Type**: `(H z₀) : Continuous (seg4_h₃ H z₀)`
- **What**: `seg4_h₃ H z₀` is continuous.
- **How**: As for `seg4_h₀_continuous`.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h₃`.
- **Used by**: `seg4_left_ftc`, `seg4_right_ftc`.
- **Visibility**: private.
- **Lines**: 193–197.
- **Notes**: none.

### `private lemma hasDerivAt_seg4_h₃`
- **Type**: `(H z₀ t) : HasDerivAt (seg4_h₃ H z₀) ((seg1Speed H : ℂ)·I) t`
- **What**: Derivative of `seg4_h₃` is `seg1Speed(H)·I` (positive imaginary direction, matching seg4 going UP).
- **How**: Differentiate `√3/2 + (5t-3)(H-√3/2) - z₀.im` w.r.t. t → real derivative `5(H-√3/2) = seg1Speed H`; ofReal-lift; multiply by I.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h₃`, `seg1Speed`.
- **Used by**: `deriv_seg4_h₃`, `seg4_left_ftc`, `seg4_right_ftc`.
- **Visibility**: private.
- **Lines**: 199–214.
- **Notes**: 16 lines.

### `private lemma deriv_seg4_h₃`
- **Type**: `(H z₀ t) : deriv (seg4_h₃ H z₀) t = (seg1Speed H : ℂ)·I`
- **What**: Functional `.deriv` of `hasDerivAt_seg4_h₃`.
- **How**: `.deriv` projection.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h₃`, `seg1Speed`, `hasDerivAt_seg4_h₃`.
- **Used by**: `seg4_left_ftc`, `seg4_right_ftc`.
- **Visibility**: private.
- **Lines**: 216–218.
- **Notes**: none.

### `private lemma seg4_h₃_left_slitPlane`
- **Type**: `{H} (hH : √3/2 < H) {z₀} (hz_re : z₀.re = -1/2) {δ} (hδ_pos : 0 < δ) {t} (htd : t ≤ seg4T₀ H z₀.im - δ) : seg4_h₃ H z₀ t ∈ slitPlane`
- **What**: To the LEFT of the crossing point (`t ≤ t₀ - δ`), `seg4_h₃` is purely imaginary with NEGATIVE im — in the slit plane.
- **How**: From `seg4_h₃_eq_pure_im`, just need `im ≠ 0`. Suppose `im = 0`; then `seg1Speed H · (t - 3/5) = z₀.im - √3/2`; combine with the definition `seg1Speed H · (seg4T₀ H z₀.im - 3/5) = z₀.im - √3/2` (`hK_eq_seg4`) using `mul_left_cancel₀` to get `t = seg4T₀ H z₀.im`, contradicting `t ≤ t₀ - δ` and `δ > 0`.
- **Hypotheses**: `√3/2 < H`, `z₀.re=-1/2`, `δ > 0`, `t ≤ t₀ - δ`.
- **Uses from project**: `seg4_h₃`, `seg4_h₃_eq_pure_im`, `seg4T₀`, `seg1Speed`, `seg1Speed_pos`.
- **Used by**: `seg4_left_ftc`.
- **Visibility**: private.
- **Lines**: 221–244.
- **Notes**: 24 lines.

### `private lemma seg4_h₃_right_slitPlane`
- **Type**: symmetric: `t ≥ seg4T₀ H z₀.im + δ` ⟹ `seg4_h₃ ∈ slitPlane`.
- **What**: RIGHT of crossing, purely imaginary with POSITIVE im (still ≠ 0).
- **How**: Same as `seg4_h₃_left_slitPlane` but with the opposite inequality.
- **Hypotheses**: `√3/2 < H`, `z₀.re=-1/2`, `δ > 0`, `seg4T₀ + δ ≤ t`.
- **Uses from project**: `seg4_h₃`, `seg4_h₃_eq_pure_im`, `seg4T₀`, `seg1Speed`, `seg1Speed_pos`.
- **Used by**: `seg4_right_ftc`.
- **Visibility**: private.
- **Lines**: 247–270.
- **Notes**: 24 lines.

### `private def seg4_h₅`
- **Type**: `(H z₀ t) : ℂ`
- **What**: Seg5 (horizontal edge) reference: `(5t - 9/2 - z₀.re) + (H - z₀.im)·I`.
- **How**: Inline definition.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `fdBoundary_sub_eq_seg4_h₅`, `seg4_h₅_continuous`, `hasDerivAt_seg4_h₅`, `deriv_seg4_h₅`, `seg4_h₅_slitPlane`, `seg4_seg5_ftc`, `seg4_junction_45`, `seg4_closed`, `seg4_ae_eq_h₅`, `fdBoundary_ftc_telescope_seg4`.
- **Visibility**: private.
- **Lines**: 273–274.
- **Notes**: none.

### `private lemma fdBoundary_sub_eq_seg4_h₅`
- **Type**: `(H z₀) {t} (ht : 4/5 < t) : fdBoundaryFun H t - z₀ = seg4_h₅ H z₀ t`
- **What**: On `(4/5, 1]`, the boundary minus z₀ equals `seg4_h₅`.
- **How**: As for the other `fdBoundary_sub_eq_*`: pick the right `ite` branch and component-simp.
- **Hypotheses**: `4/5 < t`.
- **Uses from project**: `fdBoundaryFun`, `seg4_h₅`.
- **Used by**: `seg4_ae_eq_h₅`.
- **Visibility**: private.
- **Lines**: 276–285.
- **Notes**: none.

### `private lemma seg4_h₅_continuous`
- **Type**: `(H z₀) : Continuous (seg4_h₅ H z₀)`
- **What**: `seg4_h₅` is continuous.
- **How**: As for other `seg4_h*_continuous`.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h₅`.
- **Used by**: `seg4_seg5_ftc`.
- **Visibility**: private.
- **Lines**: 287–290.
- **Notes**: none.

### `private lemma hasDerivAt_seg4_h₅`
- **Type**: `(H z₀ t) : HasDerivAt (seg4_h₅ H z₀) (5 : ℂ) t`
- **What**: Derivative of `seg4_h₅` is the constant `5` (the seg5 parametrization runs at speed 5).
- **How**: Differentiate `5t - 9/2 - z₀.re` to get 5; ofReal-lift; `.add_const`.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h₅`.
- **Used by**: `deriv_seg4_h₅`, `seg4_seg5_ftc`.
- **Visibility**: private.
- **Lines**: 292–298.
- **Notes**: none.

### `private lemma deriv_seg4_h₅`
- **Type**: `(H z₀ t) : deriv (seg4_h₅ H z₀) t = 5`
- **What**: Functional `.deriv` of `hasDerivAt_seg4_h₅`.
- **How**: `.deriv` projection.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h₅`, `hasDerivAt_seg4_h₅`.
- **Used by**: `seg4_seg5_ftc`.
- **Visibility**: private.
- **Lines**: 300–302.
- **Notes**: none.

### `private lemma seg4_h₅_slitPlane`
- **Type**: `{H z₀} (hc_hi : z₀.im < H) (t) : seg4_h₅ H z₀ t ∈ slitPlane`
- **What**: When z₀ is below height H, `seg4_h₅` has `im = H - z₀.im > 0` — in slit plane.
- **How**: Compute `im = H - z₀.im > 0`, satisfies `mem_slitPlane_iff` (positive im).
- **Hypotheses**: `z₀.im < H`.
- **Uses from project**: `seg4_h₅`.
- **Used by**: `seg4_seg5_ftc`.
- **Visibility**: private.
- **Lines**: 305–313.
- **Notes**: none.

### `private lemma seg4_seg1_ftc`
- **Type**: `(H) {z₀} (hz_re : z₀.re = -1/2) : IntervalIntegrable ... ∧ ∫₀^{1/5} ... = log(seg4_h₀ H z₀ 1/5) - log(seg4_h₀ H z₀ 0)`
- **What**: FTC on `[0, 1/5]` for `deriv h₀ / h₀` using `seg4_h₀_slitPlane`. Same shape as seg1's standard FTC.
- **How**: Apply `LogDerivFTC.ftc_log_on_segment` with the continuity, differentiability, and `seg4_h₀_slitPlane` hypotheses (constant derivative).
- **Hypotheses**: `z₀.re=-1/2`.
- **Uses from project**: `seg4_h₀`, `seg4_h₀_continuous`, `hasDerivAt_seg4_h₀`, `deriv_seg4_h₀`, `seg4_h₀_slitPlane`, `seg1Speed`, `LogDerivFTC.ftc_log_on_segment`.
- **Used by**: `fdBoundary_ftc_telescope_seg4`, `arcFTCHyp_seg4`.
- **Visibility**: private.
- **Lines**: 318–332.
- **Notes**: 15 lines.

### `private lemma seg4_arc_ftc`
- **Type**: `{z₀} (hz_re hc_lo) : IntervalIntegrable ... ∧ ∫_{1/5}^{3/5} ... = log(seg4_h_arc z₀ 3/5) - log(seg4_h_arc z₀ 1/5)`
- **What**: FTC on the arc piece using `seg4_h_arc_slitPlane`.
- **How**: `LogDerivFTC.ftc_log_on_segment` with continuity of `5π/6·I·exp(iθ)` derivative, and `seg4_h_arc_slitPlane`.
- **Hypotheses**: `z₀.re=-1/2`, `√3/2 < z₀.im`.
- **Uses from project**: `seg4_h_arc`, `seg4_h_arc_continuous`, `hasDerivAt_seg4_h_arc`, `seg4_h_arc_slitPlane`, `fdArcAngle`, `fdArcAngle_continuous`, `LogDerivFTC.ftc_log_on_segment`.
- **Used by**: `fdBoundary_ftc_telescope_seg4`, `arcFTCHyp_seg4`.
- **Visibility**: private.
- **Lines**: 335–356.
- **Notes**: 22 lines.

### `private lemma seg4_left_ftc`
- **Type**: `{H} (hH) {z₀} (hz_re) {δ} (hδ_pos hδ_lt) : IntervalIntegrable on [3/5, t₀-δ] ∧ ∫ = log(seg4_h₃ ... t₀-δ) - log(seg4_h₃ ... 3/5)`
- **What**: FTC for `seg4_h₃` on the LEFT half `[3/5, t₀ - δ]` of seg4 (before the crossing point at t₀).
- **How**: `LogDerivFTC.ftc_log_on_segment` with `seg4_h₃_continuous`, `hasDerivAt_seg4_h₃`, `deriv_seg4_h₃` (constant), and `seg4_h₃_left_slitPlane`.
- **Hypotheses**: H>√3/2, `z₀.re=-1/2`, `0 < δ`, `δ < t₀ - 3/5`.
- **Uses from project**: `seg4_h₃`, `seg4_h₃_continuous`, `hasDerivAt_seg4_h₃`, `deriv_seg4_h₃`, `seg4_h₃_left_slitPlane`, `seg1Speed`, `seg4T₀`, `LogDerivFTC.ftc_log_on_segment`.
- **Used by**: `fdBoundary_ftc_telescope_seg4`, `arcFTCHyp_seg4`.
- **Visibility**: private.
- **Lines**: 359–376.
- **Notes**: 18 lines.

### `private lemma seg4_right_ftc`
- **Type**: same shape as `seg4_left_ftc` but on `[t₀+δ, 4/5]`.
- **What**: FTC for `seg4_h₃` on the RIGHT half after the crossing.
- **How**: `LogDerivFTC.ftc_log_on_segment` with `seg4_h₃_right_slitPlane`.
- **Hypotheses**: H>√3/2, `z₀.re=-1/2`, `0 < δ`, `δ < 4/5 - t₀`.
- **Uses from project**: `seg4_h₃`, `seg4_h₃_continuous`, `hasDerivAt_seg4_h₃`, `deriv_seg4_h₃`, `seg4_h₃_right_slitPlane`, `seg1Speed`, `seg4T₀`, `LogDerivFTC.ftc_log_on_segment`.
- **Used by**: `fdBoundary_ftc_telescope_seg4`, `arcFTCHyp_seg4`.
- **Visibility**: private.
- **Lines**: 379–396.
- **Notes**: 18 lines.

### `private lemma seg4_seg5_ftc`
- **Type**: `(H) {z₀} (hc_hi : z₀.im < H) : IntervalIntegrable on [4/5, 1] ∧ ∫ = log(seg4_h₅ ... 1) - log(seg4_h₅ ... 4/5)`
- **What**: FTC on `[4/5, 1]` for the seg5 reference.
- **How**: `LogDerivFTC.ftc_log_on_segment` with `seg4_h₅_slitPlane`.
- **Hypotheses**: `z₀.im < H`.
- **Uses from project**: `seg4_h₅`, `seg4_h₅_continuous`, `hasDerivAt_seg4_h₅`, `deriv_seg4_h₅`, `seg4_h₅_slitPlane`, `LogDerivFTC.ftc_log_on_segment`.
- **Used by**: `fdBoundary_ftc_telescope_seg4`, `arcFTCHyp_seg4`.
- **Visibility**: private.
- **Lines**: 399–413.
- **Notes**: 15 lines.

### `private lemma seg4_junction_15`
- **Type**: `(H z₀) : seg4_h₀ H z₀ (1/5) = seg4_h_arc z₀ (1/5)`
- **What**: Junction equality at t=1/5: the seg1 ref meets the arc ref.
- **How**: Unfold definitions; substitute `fdArcAngle(1/5)=π/3`; compute `cos(π/3)=1/2`, `sin(π/3)=√3/2`; `Complex.ext` componentwise.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h₀`, `seg4_h_arc`, `fdArcAngle`.
- **Used by**: `fdBoundary_ftc_telescope_seg4`.
- **Visibility**: private.
- **Lines**: 417–428.
- **Notes**: 12 lines.

### `private lemma seg4_junction_35`
- **Type**: `(H z₀) : seg4_h_arc z₀ (3/5) = seg4_h₃ H z₀ (3/5)`
- **What**: Junction at t=3/5: arc ref meets seg4 ref.
- **How**: Unfold; `fdArcAngle(3/5) = 2π/3`; compute `cos(2π/3) = -1/2`, `sin(2π/3) = √3/2`; `Complex.ext`.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h_arc`, `seg4_h₃`, `fdArcAngle`.
- **Used by**: `fdBoundary_ftc_telescope_seg4`.
- **Visibility**: private.
- **Lines**: 430–443.
- **Notes**: 14 lines.

### `private lemma seg4_junction_45`
- **Type**: `(H z₀) : seg4_h₃ H z₀ (4/5) = seg4_h₅ H z₀ (4/5)`
- **What**: Junction at t=4/5: seg4 ref meets seg5 ref.
- **How**: `Complex.ext`; component-simp on definitions.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h₃`, `seg4_h₅`.
- **Used by**: `fdBoundary_ftc_telescope_seg4`.
- **Visibility**: private.
- **Lines**: 445–454.
- **Notes**: none.

### `private lemma seg4_closed`
- **Type**: `(H z₀) : seg4_h₀ H z₀ 0 = seg4_h₅ H z₀ 1`
- **What**: The boundary path closes: `seg4_h₀(0) = seg4_h₅(1)` (i.e. `fdBoundaryFun(0) - z₀ = fdBoundaryFun(1) - z₀`).
- **How**: `Complex.ext` + componentwise simp.
- **Hypotheses**: none.
- **Uses from project**: `seg4_h₀`, `seg4_h₅`.
- **Used by**: `fdBoundary_ftc_telescope_seg4`.
- **Visibility**: private.
- **Lines**: 456–465.
- **Notes**: 10 lines.

### `private lemma seg4_log_diff_eq_neg_pi_I`
- **Type**: `{H} (hH) {z₀} (hz_re) {δ} (hδ_pos) : log(seg4_h₃ H z₀ (t₀-δ)) - log(seg4_h₃ H z₀ (t₀+δ)) = -(π·I)`
- **What**: Across the crossing point t₀, the log of `seg4_h₃` jumps by `-π·I` (going from negative-imaginary to positive-imaginary).
- **How**: Compute `seg4_h₃(t₀-δ) = -(seg1Speed H · δ) · I` and `seg4_h₃(t₀+δ) = (seg1Speed H · δ) · I` (both purely imaginary, opposite signs), using `seg4_h₃_eq_pure_im` and the identity `seg1Speed H · (t₀ - 3/5) = z₀.im - √3/2`. Then `Complex.log` of `(c·(-I))` minus `log(c·I)` = `log_neg_I - log_I = -π/2·I - π/2·I = -π·I` via `Complex.log_ofReal_mul`, `Complex.log_neg_I`, `Complex.log_I`.
- **Hypotheses**: H>√3/2, `z₀.re=-1/2`, `0 < δ`.
- **Uses from project**: `seg4_h₃`, `seg4_h₃_eq_pure_im`, `seg1Speed`, `seg1Speed_pos`, `seg4T₀`.
- **Used by**: `fdBoundary_ftc_telescope_seg4`.
- **Visibility**: private.
- **Lines**: 470–515.
- **Notes**: 46 lines.

### `private lemma seg4_ae_eq_h₀`
- **Type**: `(H z₀) : ∀ᵐ t ∂volume, t ∈ uIoc 0 (1/5) → (fdBoundaryFun H t - z₀)⁻¹ · deriv (fdBoundaryFun H) t = deriv (seg4_h₀ H z₀) t / seg4_h₀ H z₀ t`
- **What**: Almost-everywhere agreement of the "boundary winding integrand" with `deriv h₀ / h₀` on `uIoc 0 (1/5)`, excluding measure-zero endpoint.
- **How**: Exclude `{1/5}` (measure zero); for `t < 1/5` use `fdBoundary_sub_eq_seg4_h₀` plus `EventuallyEq.deriv_eq` (from `Iio_mem_nhds`) + `deriv_sub_const` to commute deriv and subtraction.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `seg4_h₀`, `fdBoundary_sub_eq_seg4_h₀`.
- **Used by**: `fdBoundary_ftc_telescope_seg4`, `arcFTCHyp_seg4`.
- **Visibility**: private.
- **Lines**: 519–538.
- **Notes**: 20 lines.

### `private lemma seg4_ae_eq_h_arc`
- **Type**: same shape on `uIoc (1/5) (3/5)`.
- **What**: A.e. agreement on the arc piece.
- **How**: Same approach with `Iio_mem_nhds`+`Ioi_mem_nhds` and `fdBoundary_sub_eq_seg4_h_arc`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `seg4_h_arc`, `fdBoundary_sub_eq_seg4_h_arc`.
- **Used by**: `fdBoundary_ftc_telescope_seg4`, `arcFTCHyp_seg4`.
- **Visibility**: private.
- **Lines**: 540–560.
- **Notes**: 21 lines.

### `private lemma seg4_ae_eq_h₃`
- **Type**: `(H z₀) {a b} (hab : a ≤ b) (ha_ge : 3/5 ≤ a) (hb_le : b ≤ 4/5) : ∀ᵐ t ∂volume, t ∈ uIoc a b → ... = deriv (seg4_h₃ H z₀) t / seg4_h₃ H z₀ t`
- **What**: A.e. agreement on any subinterval of `[3/5, 4/5]` (seg4 reference window).
- **How**: Exclude `{a, b}` (finite); use `fdBoundary_sub_eq_seg4_h₃` and `EventuallyEq.deriv_eq` with `Ioi_mem_nhds`+`Iio_mem_nhds`.
- **Hypotheses**: `a ≤ b`, `3/5 ≤ a`, `b ≤ 4/5`.
- **Uses from project**: `fdBoundaryFun`, `seg4_h₃`, `fdBoundary_sub_eq_seg4_h₃`.
- **Used by**: `fdBoundary_ftc_telescope_seg4`, `arcFTCHyp_seg4`.
- **Visibility**: private.
- **Lines**: 562–586.
- **Notes**: 25 lines.

### `private lemma seg4_ae_eq_h₅`
- **Type**: same shape on `uIoc (4/5) 1`.
- **What**: A.e. agreement on the seg5 piece.
- **How**: `ae_of_all` (no exclusion needed); use `fdBoundary_sub_eq_seg4_h₅` and `Ioi_mem_nhds`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `seg4_h₅`, `fdBoundary_sub_eq_seg4_h₅`.
- **Used by**: `fdBoundary_ftc_telescope_seg4`, `arcFTCHyp_seg4`.
- **Visibility**: private.
- **Lines**: 588–604.
- **Notes**: 17 lines.

### `theorem fdBoundary_ftc_telescope_seg4`
- **Type**: `{H} (hH) {z₀} (hz_re hc_lo hc_hi) {δ} (hδ_pos hδ_lt_lo hδ_lt_hi) : (∫₀^(t₀-δ)) + (∫_(t₀+δ)^1) = -(π·I)` where t₀ = seg4T₀ H z₀.im.
- **What**: **Main FTC telescope theorem for seg4 crossing**: the (deleted-neighborhood) integral around the seg4 crossing point t₀ contributes `-π·I` — exactly half of `-2π·I·winding`, contributing a winding number of 1/2 to the boundary integral.
- **How**: Five per-segment FTC pieces ([0,1/5], [1/5,3/5], [3/5,t₀-δ], [t₀+δ,4/5], [4/5,1]) via `seg4_seg1_ftc`, `seg4_arc_ftc`, `seg4_left_ftc`, `seg4_right_ftc`, `seg4_seg5_ftc`. Convert each via `intervalIntegral.integral_congr_ae` using the a.e. equalities `seg4_ae_eq_*`. Establish integrability on each piece via `IntervalIntegrable.congr_ae`. Split the LHS (0, t₀-δ) via `intervalIntegral.integral_add_adjacent_intervals` through 1/5 and 3/5 (uses `linear_combination -h1 - h2`). Split (t₀+δ, 1) through 4/5. Combine all logs; junction equalities `seg4_junction_15/35/45/closed` cancel most terms, leaving `log(seg4_h₃(t₀-δ)) - log(seg4_h₃(t₀+δ))` = `-π·I` by `seg4_log_diff_eq_neg_pi_I`.
- **Hypotheses**: H>√3/2, z₀ on left edge above √3/2 and below H, 0 < δ < min(t₀-3/5, 4/5-t₀).
- **Uses from project**: `fdBoundaryFun`, `seg4T₀`, `seg4T₀_gt_three_fifths`, `seg4T₀_lt_four_fifths`, `seg4_seg1_ftc`, `seg4_arc_ftc`, `seg4_left_ftc`, `seg4_right_ftc`, `seg4_seg5_ftc`, `seg4_ae_eq_h₀`, `seg4_ae_eq_h_arc`, `seg4_ae_eq_h₃`, `seg4_ae_eq_h₅`, `seg4_h₀`, `seg4_h_arc`, `seg4_h₃`, `seg4_h₅`, `seg4_junction_15`, `seg4_junction_35`, `seg4_junction_45`, `seg4_closed`, `seg4_log_diff_eq_neg_pi_I`.
- **Used by**: `arcFTCHyp_seg4`.
- **Visibility**: public.
- **Lines**: 609–720.
- **Notes**: 112 lines.

### `def arcFTCHyp_seg4`
- **Type**: `{H} (hH) (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : extend agreement with fdBoundaryFun) {z₀} (hz_re hc_lo hc_hi) : ArcFTCHyp γ z₀ (seg4T₀ H z₀.im) (linDelta (seg1Speed H)) (seg4Threshold H z₀) (-(π·I))`
- **What**: **Final assembly**: the full `ArcFTCHyp` structure (FTC limit, left integrability, right integrability, limit-tendsto) at any interior point of seg4, providing data needed by the generalized winding number framework with limit `-π·I`.
- **How**: Constructs the four fields `E`, `h_ftc`, `hint_left`, `hint_right`, `h_limit`. `E := fun _ => -(π·I)`. For `h_ftc`: derive `ε < min(H-z₀.im, ‖z₀‖-1)` (then `< z₀.im - √3/2` via `norm_sub_one_le_im_sub_sqrt3_seg4`); `linDelta(seg1Speed H) ε < min(t₀-3/5, 4/5-t₀)` (via `seg1Speed_mul_t₀_sub_three_fifths` and `seg1Speed_mul_four_fifths_sub_t₀`); apply `transfer_integral` and `fdBoundary_ftc_telescope_seg4`. For `hint_left/right`: combine the same per-piece integrabilities via `IntervalIntegrable.trans`. `h_limit := tendsto_const_nhds`.
- **Hypotheses**: H>√3/2; γ closed path matching `fdBoundaryFun` on `Icc 0 1`; z₀ on left edge between √3/2 and H.
- **Uses from project**: `ArcFTCHyp`, `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `seg1Speed`, `seg1Speed_pos`, `linDelta`, `linDelta_pos`, `seg4T₀`, `seg4T₀_gt_three_fifths`, `seg4T₀_lt_four_fifths`, `seg4Threshold`, `seg1Speed_mul_t₀_sub_three_fifths`, `seg1Speed_mul_four_fifths_sub_t₀`, `norm_sub_one_le_im_sub_sqrt3_seg4`, `transfer_integral`, `transfer_integrability`, `fdBoundary_ftc_telescope_seg4`, `seg4_seg1_ftc`, `seg4_arc_ftc`, `seg4_left_ftc`, `seg4_right_ftc`, `seg4_seg5_ftc`, `seg4_ae_eq_h₀`, `seg4_ae_eq_h_arc`, `seg4_ae_eq_h₃`, `seg4_ae_eq_h₅`.
- **Used by**: unused in file (exported).
- **Visibility**: public.
- **Lines**: 725–826.
- **Notes**: 102 lines; final structure with three big tactic blocks.

## File Summary

- **Total declarations**: 35 (5 private `def`s + 28 private `lemma`s + 2 public theorems/defs).
- **Key API**: 
  - Public exports: `fdBoundary_ftc_telescope_seg4` (main FTC) and `arcFTCHyp_seg4` (final `ArcFTCHyp` structure).
  - Five reference-function families (`seg4_h₀`, `seg4_h_arc`, `seg4_h₃`, `seg4_h₅`) each with companion continuity, `HasDerivAt`, derivative-formula, slit-plane, and FTC lemmas.
- **Unused in file**: `arcFTCHyp_seg4` (the main public export, consumed downstream).
- **Sorries**: 0.
- **set_options**: none.
- **Long proofs (>30 lines)**: `fdBoundary_ftc_telescope_seg4` (112), `arcFTCHyp_seg4` (102), `seg4_log_diff_eq_neg_pi_I` (46), `seg4_h_arc_slitPlane` (44).
- **Purpose**: Provides the FTC-based ε-deleted-neighborhood log-derivative integral for the LEFT vertical edge (seg4) crossing of the modular fundamental-domain boundary. Symmetric to seg1 but with reversed orientation (UP not DOWN). Produces the `ArcFTCHyp` structure at any generic seg4 interior point `z₀` (with `re=-1/2`, `√3/2 < im < H`), recording that the deleted-neighborhood integral contributes `-π·I` to the boundary winding. This is one of two "edge providers" supplying half-integer winding contributions in the valence-formula contour integral. Strategy: piecewise reference functions per segment ([0,1/5] seg1, [1/5,3/5] arc, [3/5,4/5] seg4 with left/right halves around the crossing, [4/5,1] seg5), each in `slitPlane` so `Complex.log` is holomorphic; junction equalities glue the logs together; only the `seg4_h₃` jump survives, contributing `log(neg-imag) - log(pos-imag) = -π·I`.
