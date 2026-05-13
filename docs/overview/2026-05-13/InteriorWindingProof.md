# InteriorWindingProof.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/InteriorWindingProof.lean`
Imports: `InteriorWinding`, `FDBoundaryPath`, `SegmentFTC`

### `theorem Complex.log_eq_log_norm_add_arg_mul_I`
- **Type**: `(w : ℂ) → Complex.log w = ↑(Real.log ‖w‖) + ↑(Complex.arg w) * I`
- **What**: The complex logarithm decomposes into its real part `log‖w‖` and imaginary part `arg(w)·I`.
- **How**: `Complex.ext` splitting real and imaginary parts, then `simp [Complex.log_re]` and `simp [Complex.log_im]`.
- **Hypotheses**: None beyond `w : ℂ`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 49-53
- **Notes**: none

### `theorem fdBoundary_seg1_in_slitPlane`
- **Type**: `{z : ℂ} {H : ℝ} (hz_re : z.re < 1/2) (t : ℝ) (ht : t ≤ 1/5) → fdBoundaryFun H t - z ∈ Complex.slitPlane`
- **What**: On segment 1 (right vertical) with `re = 1/2`, the shifted point `γ(t) - z` lies in the slit plane provided `z.re < 1/2`.
- **How**: Use `Complex.mem_slitPlane_iff`, choose `left` branch; compute real part via `fdBoundaryFun_seg1_re`, conclude by `linarith`.
- **Hypotheses**: `z.re < 1/2`; `t ≤ 1/5`.
- **Uses from project**: `fdBoundaryFun_seg1_re`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 62-69
- **Notes**: none

### `theorem fdBoundary_seg5_in_slitPlane`
- **Type**: `{z : ℂ} {H : ℝ} (hz_im : z.im < H) (t : ℝ) (ht : 4/5 < t) → fdBoundaryFun H t - z ∈ Complex.slitPlane`
- **What**: On segment 5 (horizontal at `im = H`), `γ(t) - z` is in the slit plane when `z.im < H`.
- **How**: Choose `right` branch of `mem_slitPlane_iff`; imaginary part computed by `fdBoundaryFun_seg5_im`; `linarith`.
- **Hypotheses**: `z.im < H`; `4/5 < t`.
- **Uses from project**: `fdBoundaryFun_seg5_im`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 73-80
- **Notes**: none

### `theorem fdBoundary_seg4_in_slitPlane_of_im_ne`
- **Type**: `{z : ℂ} {H : ℝ} (t : ℝ) (_ht3 : 3/5 < t) (_ht4 : t ≤ 4/5) (him_ne : (fdBoundaryFun H t - z).im ≠ 0) → fdBoundaryFun H t - z ∈ Complex.slitPlane`
- **What**: On segment 4 (left vertical), `γ(t) - z` is in the slit plane whenever its imaginary part is nonzero.
- **How**: Use `Complex.mem_slitPlane_iff`, choose `right`, return hypothesis directly.
- **Hypotheses**: `(fdBoundaryFun H t - z).im ≠ 0`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 84-90
- **Notes**: none

### `lemma segment_integrability`
- **Type**: `{f : ℝ → ℂ} (hint : IntervalIntegrable f volume 0 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) → IntervalIntegrable f volume a b`
- **What**: Extracts integrability on a sub-interval `[a,b] ⊆ [0,1]` from full-interval integrability.
- **How**: `IntervalIntegrable.mono_set` via `Set.uIcc_subset_uIcc`.
- **Hypotheses**: `0 ≤ a`, `a ≤ b`, `b ≤ 1`; `f` integrable on `[0,1]`.
- **Uses from project**: []
- **Used by**: `fdBoundary_contourIntegral_split`
- **Visibility**: private
- **Lines**: 98-102
- **Notes**: none

### `theorem fdBoundary_contourIntegral_split`
- **Type**: `{z : ℂ} {H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hint : IntervalIntegrable (fun t => (γ t - z)⁻¹ * deriv γ.toPath.extend t) volume 0 1) → γ.contourIntegral (fun w => (w - z)⁻¹) = (∫... 0..1/5) + (∫... 1/5..2/5) + (∫... 2/5..3/5) + (∫... 3/5..4/5) + (∫... 4/5..1)`
- **What**: Decomposes the contour integral of `(w-z)⁻¹` along the FD boundary into five segment integrals at partition points `1/5, 2/5, 3/5, 4/5`.
- **How**: Unfold `PiecewiseC1Path.contourIntegral`; derive five `segment_integrability` instances; iteratively apply `intervalIntegral.integral_add_adjacent_intervals` to subdivide `[0,1]`; close with `ring`.
- **Hypotheses**: Integrability of the integrand on `[0,1]`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `PiecewiseC1Path.contourIntegral`, `segment_integrability`
- **Used by**: `fdBoundary_contourIntegral_inv_sub_eq_of_ftc`
- **Visibility**: public
- **Lines**: 106-146
- **Notes**: >30 lines

### `theorem fdBoundary_contourIntegral_inv_sub_eq_of_ftc`
- **Type**: `{z : ℂ} {H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hint : IntervalIntegrable ...) (h_seg1..h_seg5 : segment FTC identities) (h_total : sum of log differences = -(2πI)) → γ.contourIntegral (fun w => (w - z)⁻¹) = -(2πI)`
- **What**: Given five segment FTC log-difference identities and their algebraic sum equal to `-2πi`, the contour integral equals `-2πi`.
- **How**: Apply `fdBoundary_contourIntegral_split`; rewrite each segment with its FTC hypothesis then with `h_total`.
- **Hypotheses**: Integrability; five segment integral=log difference equalities; total log telescoping equality.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `PiecewiseC1Path.contourIntegral`, `fdBoundary_contourIntegral_split`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 155-177
- **Notes**: none

### `theorem log_telescope_five`
- **Type**: `{a b c d e f : ℂ} → (b - a) + (c - b) + (d - c) + (e - d) + (f - e) = f - a`
- **What**: Five-term telescoping identity for differences.
- **How**: `ring`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `closed_path_log_telescope_five`
- **Visibility**: public
- **Lines**: 180-181
- **Notes**: none

### `theorem closed_path_sub_eq`
- **Type**: `{z : ℂ} {H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) → γ 1 - z = γ 0 - z`
- **What**: For a path agreeing with `fdBoundaryFun` (closed at endpoints), `γ(1) - z = γ(0) - z`.
- **How**: Identify `γ 0` and `γ 1` via `hγ` to `fdBoundaryFun H 0/1`, then apply `fdBoundaryFun_closed`.
- **Hypotheses**: `γ` agrees with `fdBoundaryFun H` on `[0,1]`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `fdBoundaryFun_closed`
- **Used by**: `closed_path_log_telescope_eq_zero`
- **Visibility**: public
- **Lines**: 186-196
- **Notes**: none

### `theorem closed_path_log_telescope_eq_zero`
- **Type**: `{z : ℂ} {H : ℝ} (γ : ...) (hγ : ...) → Complex.log (γ 1 - z) - Complex.log (γ 0 - z) = 0`
- **What**: For a closed path, the log difference at endpoints vanishes.
- **How**: Rewrite using `closed_path_sub_eq`, then `sub_self`.
- **Hypotheses**: `γ` agrees with `fdBoundaryFun H`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `closed_path_sub_eq`
- **Used by**: `closed_path_log_telescope_five`
- **Visibility**: public
- **Lines**: 199-203
- **Notes**: none

### `theorem closed_path_log_telescope_five`
- **Type**: `{z : ℂ} {H : ℝ} (γ : ...) (hγ : ...) → five log-differences sum = 0`
- **What**: For a closed path the five standard-branch log differences telescope to zero — so any `-2πi` correction must come from branch-switching on at least one segment.
- **How**: Combine `log_telescope_five` (specialized to log values at `0,1/5,2/5,3/5,4/5,1`) with `closed_path_log_telescope_eq_zero`.
- **Hypotheses**: `γ` agrees with `fdBoundaryFun H`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `log_telescope_five`, `closed_path_log_telescope_eq_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 208-223
- **Notes**: none

### `theorem fdBoundary_interior_winding_neg_one`
- **Type**: `{H : ℝ} (hH : H > Real.sqrt 3 / 2) {z : ℂ} (hz : FDStrictInterior z H) (h_integral : (fdBoundaryPC1Path H hH).contourIntegral (fun w => (w - z)⁻¹) = -(2πI)) → HasGeneralizedWindingNumber (fdBoundaryPC1Path H hH) z (-1)`
- **What**: For a strict interior point with the contour integral identity, the generalized winding number equals `-1`.
- **How**: Apply `hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral` to `fdBoundaryPC1Path H hH` with path equality `fdBoundaryPC1Path_eq` and the four strict-interior properties from `hz`.
- **Hypotheses**: `H > √3/2`; strict interior; contour integral = `-2πi`.
- **Uses from project**: `fdBoundaryPC1Path`, `FDStrictInterior`, `HasGeneralizedWindingNumber`, `hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral`, `fdBoundaryPC1Path_eq`, `FDStrictInterior.norm_gt/re_abs_lt/im_pos/im_lt`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 229-238
- **Notes**: none

### `theorem circle_integral_inv_sub_eq_two_pi_I`
- **Type**: `{c z : ℂ} {R : ℝ} (hz : z ∈ Metric.ball c R) → ∮ w in C(c, R), (w - z)⁻¹ = 2 * ↑Real.pi * I`
- **What**: Counterclockwise circle integral of `(w - z)⁻¹` around a ball containing `z` equals `2πi`.
- **How**: Direct alias of `circleIntegral.integral_sub_inv_of_mem_ball`.
- **Hypotheses**: `z ∈ Metric.ball c R`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 243-246
- **Notes**: none

### `theorem contourIntegral_inv_sub_of_winding_neg_one`
- **Type**: `{x : ℂ} (γ : PiecewiseC1Path x x) {z : ℂ} (h_val : ∃ n : ℤ, γ.contourIntegral ... = n * (2πI)) (hn : ∀ n, ... = n * (2πI) → n = -1) → γ.contourIntegral (fun w => (w - z)⁻¹) = -(2πI)`
- **What**: If the contour integral is an integer multiple of `2πi` and the unique such integer is `-1`, the integral equals `-2πi`.
- **How**: Extract `n` from `h_val`, apply `hn`, push casts and `ring`.
- **Hypotheses**: Integer-multiple representation; integer determined to be `-1`.
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.contourIntegral`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 252-262
- **Notes**: none

### `theorem fdBoundary_seg1_ftc`
- **Type**: `{z : ℂ} {H : ℝ} (_hz_re : z.re < 1/2) (γ : ...) (_hγ : ...) (h_int : IntervalIntegrable ... 0 (1/5)) (hFγ_cont : ContinuousOn ... (Icc 0 (1/5))) (hFγ_deriv : ∀ t ∈ Ioo 0 (1/5), HasDerivAt ...) → ∫ t in 0..1/5, ... = log(γ(1/5) - z) - log(γ 0 - z)`
- **What**: FTC on segment 1: integral equals log difference, given primitive continuity and derivative.
- **How**: Direct application of `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`.
- **Hypotheses**: Integrability; primitive continuous on `[0,1/5]` with correct derivative on `(0,1/5)`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 275-292
- **Notes**: none

### `theorem fdBoundary_seg5_ftc`
- **Type**: `{z : ℂ} {H : ℝ} (_hz_im : z.im < H) (γ : ...) (_hγ : ...) (h_int : IntervalIntegrable ... 4/5 1) (hFγ_cont : ContinuousOn ... (Icc (4/5) 1)) (hFγ_deriv : ∀ t ∈ Ioo (4/5) 1, HasDerivAt ...) → ∫ t in 4/5..1, ... = log(γ 1 - z) - log(γ(4/5) - z)`
- **What**: FTC on segment 5: integral equals log difference under the analogous hypotheses.
- **How**: Direct application of `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`.
- **Hypotheses**: Analogous to seg1, on `[4/5, 1]`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 296-310
- **Notes**: none

### `def fdWindingData_of_interior_integral`
- **Type**: `{H : ℝ} (hH : H > √3/2) (h_int : ∀ z ∈ strict interior, contour integral = -(2πI)) (D_i, D_rho, D_rho1 : SingleCrossingData ...) (hL_*) → FDWindingData H`
- **What**: Builds `FDWindingData H` from the interior contour integral identity and three elliptic single-crossing data.
- **How**: Delegates to `FDWindingData.mk_of_interior_contourIntegral` with `fdBoundaryPC1Path` and `fdBoundaryPC1Path_eq`.
- **Hypotheses**: `H > √3/2`; per-point integral identity; `SingleCrossingData` at `I, ρ, ρ+1` with prescribed CPV limits.
- **Uses from project**: `fdBoundaryPC1Path`, `fdBoundaryPC1Path_eq`, `SingleCrossingData`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, `FDWindingData`, `FDWindingData.mk_of_interior_contourIntegral`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 318-333
- **Notes**: none

### `theorem ftc_inv_sub_on_slitPlane`
- **Type**: `{x z : ℂ} (γ : PiecewiseC1Path x x) {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ Icc 0 1) (hγ_slit : ∀ t ∈ Icc a b, γ t - z ∈ Complex.slitPlane) (h_no_part : ∀ p ∈ γ.partition, p ∉ Ioo a b) (h_int : IntervalIntegrable ...) → ∫ t in a..b, ... = log(γ b - z) - log(γ a - z)`
- **What**: FTC for `(w-z)⁻¹` on a sub-interval `[a,b]` of a piecewise C¹ path when `γ(t)-z` stays in the slit plane and no partition points lie in `(a,b)`.
- **How**: Define `F(t) = log(γ.extend(t) - z)`. Show `ContinuousOn` via `ContinuousOn.clog` on `(γ-z)`. Show `HasDerivAt` pointwise on `Ioo a b` using `γ.differentiable_off`, `hasDerivAt.sub (hasDerivAt_const)`, then `HasDerivAt.clog_real` (chain rule), and `Complex.slitPlane_ne_zero`. Conclude with `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`.
- **Hypotheses**: `a ≤ b ⊆ [0,1]`; slit-plane membership of `γ-z`; no partition point in `(a,b)`; integrability.
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.partition`, `PiecewiseC1Path.differentiable_off`, `PiecewiseC1Path.extendedPath`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 344-383
- **Notes**: >30 lines

## File Summary
- Total declarations: 16 (1 lemma `segment_integrability` private; 14 public theorems; 1 public def `fdWindingData_of_interior_integral`).
- Theme: Decomposition of the contour integral of `(w-z)⁻¹` along the 5-segment FD boundary into log differences via FTC, plus reduction of "interior winding = -1" to a single contour integral identity and a clean `FDWindingData` constructor.
- Key external dependencies: `InteriorWinding` (predicate `FDStrictInterior`, reduction lemmas, `FDWindingData.mk_of_interior_contourIntegral`), `FDBoundaryPath` (`fdBoundaryFun`, `fdBoundaryPC1Path`, segment re/im lemmas, closure), `SegmentFTC` (likely supplies FTC scaffolding referenced indirectly).
- No `sorry`, no `axiom`, no `set_option` directives, no `native_decide`.
- 2 declarations exceed 30 lines (`fdBoundary_contourIntegral_split`, `ftc_inv_sub_on_slitPlane`).
