# Inventory: ArcFTCAtI.lean

File: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ArcFTCAtI.lean
Lines: 488

### `def arcRef_I`
- **Type**: `(t : ℝ) : ℂ`
- **What**: Reference arc parametrization `exp(i·fdArcAngle(t)) - I` used on segment 2 and 3 of the FD boundary.
- **How**: Direct definition combining `Complex.exp`, `fdArcAngle`, and `I`.
- **Hypotheses**: none
- **Uses from project**: `fdArcAngle`
- **Used by**: `arcRef_I_contDiff`, `arcRef_I_eq`, `arcRef_I_eq_at_15`, `arcRef_I_eventuallyEq`, `arcRef_I_slitPlane_seg2`, `arcRef_I_neg_slitPlane_seg3`, `seg2_ftc_I`, `seg3_ftc_neg_I`
- **Visibility**: private
- **Lines**: 45
- **Notes**: none

### `lemma fdArcAngle_contDiff`
- **Type**: `ContDiff ℝ ⊤ fdArcAngle`
- **What**: The fundamental-domain arc angle parametrization is smooth.
- **How**: `unfold fdArcAngle` then `fun_prop`.
- **Hypotheses**: none
- **Uses from project**: `fdArcAngle`
- **Used by**: `arcRef_I_contDiff`
- **Visibility**: private
- **Lines**: 47-49
- **Notes**: none

### `lemma arcRef_I_contDiff`
- **Type**: `ContDiff ℝ ⊤ arcRef_I`
- **What**: The reference arc function `arcRef_I` is smooth.
- **How**: `Complex.contDiff_exp.comp (ofRealCLM.contDiff.comp fdArcAngle_contDiff).mul const).sub const`.
- **Hypotheses**: none
- **Uses from project**: `arcRef_I`, `fdArcAngle_contDiff`
- **Used by**: `seg2_ftc_I`, `seg3_ftc_neg_I`
- **Visibility**: private
- **Lines**: 51-55
- **Notes**: none

### `lemma arcRef_I_eq`
- **Type**: `(H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) : fdBoundaryFun H t - I = arcRef_I t`
- **What**: On the arc piece `(1/5, 3/5]`, the FD boundary minus `i` agrees with `arcRef_I`.
- **How**: Apply `fdBoundaryFun_arc_eq_exp`.
- **Hypotheses**: `1/5 < t`, `t ≤ 3/5`
- **Uses from project**: `arcRef_I`, `fdBoundaryFun`, `fdBoundaryFun_arc_eq_exp`
- **Used by**: `arcRef_I_eventuallyEq`, `seg2_ftc_I`, `seg3_ftc_neg_I`
- **Visibility**: private
- **Lines**: 57-60
- **Notes**: none

### `lemma arcRef_I_eq_at_15`
- **Type**: `(H : ℝ) : fdBoundaryFun H (1/5) - I = arcRef_I (1/5)`
- **What**: Endpoint identity for `arcRef_I` at `t = 1/5` (which is `ρ+1`).
- **How**: Rewrite using `fdArcAngle_at_one_fifth` and `fdBoundaryFun_at_one_fifth`, then `cos π/3 = 1/2`, `sin π/3 = √3/2`.
- **Hypotheses**: none
- **Uses from project**: `arcRef_I`, `fdBoundaryFun`, `fdArcAngle_at_one_fifth`, `fdBoundaryFun_at_one_fifth`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`
- **Used by**: `seg2_ftc_I`
- **Visibility**: private
- **Lines**: 62-69
- **Notes**: none

### `lemma arcRef_I_eventuallyEq`
- **Type**: `(H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t < 3/5) : (fun s => fdBoundaryFun H s - I) =ᶠ[𝓝 t] arcRef_I`
- **What**: `fdBoundaryFun - I` agrees with `arcRef_I` in a nhd of `t ∈ (1/5, 3/5)`.
- **How**: `Filter.eventually_of_mem` on `Ioi 1/5 ∩ Iio 3/5` plus `arcRef_I_eq`.
- **Hypotheses**: `1/5 < t`, `t < 3/5`
- **Uses from project**: `fdBoundaryFun`, `arcRef_I`, `arcRef_I_eq`
- **Used by**: `seg2_ftc_I`, `seg3_ftc_neg_I`
- **Visibility**: private
- **Lines**: 71-77
- **Notes**: none

### `lemma arcRef_I_slitPlane_seg2`
- **Type**: `{t : ℝ} (ht1 : 1/5 ≤ t) (ht2 : t < 2/5) : arcRef_I t ∈ Complex.slitPlane`
- **What**: On `[1/5, 2/5)`, `arcRef_I t` has positive real part (in slit plane).
- **How**: `Real.cos_pos_of_mem_Ioo` on `fdArcAngle t ∈ (−π/2, π/2)` via `nlinarith`.
- **Hypotheses**: `1/5 ≤ t`, `t < 2/5`
- **Uses from project**: `arcRef_I`, `fdArcAngle`
- **Used by**: `seg2_ftc_I`
- **Visibility**: private
- **Lines**: 79-89
- **Notes**: none

### `lemma arcRef_I_neg_slitPlane_seg3`
- **Type**: `{t : ℝ} (ht2 : 2/5 < t) (ht3 : t ≤ 3/5) : -(arcRef_I t) ∈ Complex.slitPlane`
- **What**: On `(2/5, 3/5]`, `-arcRef_I t` is in the slit plane (i.e. `arcRef_I` has negative real part).
- **How**: `Real.cos_neg_of_pi_div_two_lt_of_lt` on `fdArcAngle t ∈ (π/2, π + π/2)`.
- **Hypotheses**: `2/5 < t`, `t ≤ 3/5`
- **Uses from project**: `arcRef_I`, `fdArcAngle`
- **Used by**: `seg3_ftc_neg_I`
- **Visibility**: private
- **Lines**: 91-105
- **Notes**: none

### `lemma integrand_form_eq`
- **Type**: `(f : ℝ → ℂ) (z : ℂ) (t : ℝ) : (f t - z)⁻¹ * deriv f t = deriv (fun s => f s - z) t / (f t - z)`
- **What**: Rewrite of logarithmic-derivative integrand from product form to derivative-of-shift form.
- **How**: `deriv_add_const` after rewriting `f s - z = f s + (-z)`, then `div_eq_mul_inv`, `mul_comm`.
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `fdBoundary_ftc_telescope_I`
- **Visibility**: private
- **Lines**: 109-112
- **Notes**: none

### `theorem seg2_ftc_I`
- **Type**: `(H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) : IntervalIntegrable ... ∧ ∫ ... = log(...) - log(...)`
- **What**: FTC for the log-derivative integrand on the seg2 sub-interval `[1/5, 2/5 - δ]`, with closed form via `Complex.log`.
- **How**: `LogDerivFTC.ftc_log_pieceFM` applied with `arcRef_I_contDiff` (continuity + differentiability + deriv continuity), slit-plane hypothesis `arcRef_I_slitPlane_seg2`, and pointwise/derivative agreement via `arcRef_I_eq`/`arcRef_I_eventuallyEq` plus endpoint identity `arcRef_I_eq_at_15`.
- **Hypotheses**: `0 < δ`, `δ < 1/5`
- **Uses from project**: `LogDerivFTC.ftc_log_pieceFM`, `fdBoundaryFun`, `arcRef_I_contDiff`, `arcRef_I_slitPlane_seg2`, `arcRef_I_eq`, `arcRef_I_eventuallyEq`, `arcRef_I_eq_at_15`
- **Used by**: `fdBoundary_ftc_telescope_I`
- **Visibility**: private
- **Lines**: 115-130
- **Notes**: >10 lines

### `theorem seg3_ftc_neg_I`
- **Type**: `(H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) : IntervalIntegrable ... ∧ ∫ ... = log(-...) - log(-...)`
- **What**: FTC for the log-derivative integrand on seg3 sub-interval `[2/5+δ, 3/5]`, using negated reference (because real part is negative).
- **How**: `LogDerivFTC.ftc_log_neg_on_segment` + ae-congruence (excluding the right endpoint via `compl_mem_ae_iff.mpr (measure_singleton (3/5))`) bridges the actual integrand with the reference integrand. >10 lines.
- **Hypotheses**: `0 < δ`, `δ < 1/5`
- **Uses from project**: `LogDerivFTC.ftc_log_neg_on_segment`, `fdBoundaryFun`, `arcRef_I_contDiff`, `arcRef_I_neg_slitPlane_seg3`, `arcRef_I_eq`, `arcRef_I_eventuallyEq`
- **Used by**: `fdBoundary_ftc_telescope_I`
- **Visibility**: private
- **Lines**: 133-159
- **Notes**: >10 lines

### `def seg4Ref_I`
- **Type**: `(H : ℝ) (t : ℝ) : ℂ`
- **What**: Reference parametrization for seg4 (left vertical edge), `-1/2 + i·(linear in t)`.
- **How**: Direct linear expression.
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `seg4Ref_I_contDiff`, `seg4Ref_I_neg_slitPlane`, `seg4Ref_I_eq`, `seg4Ref_I_eq_35`, `seg4Ref_I_eq_45`, `seg4Ref_I_eventuallyEq`, `seg4_ftc_neg_I`
- **Visibility**: private
- **Lines**: 163-164
- **Notes**: none

### `lemma seg4Ref_I_contDiff`
- **Type**: `(H : ℝ) : ContDiff ℝ ⊤ (seg4Ref_I H)`
- **What**: seg4 reference is smooth.
- **How**: `ContDiff.add contDiff_const` with `ofRealCLM.contDiff.comp ... .mul contDiff_const`.
- **Hypotheses**: none
- **Uses from project**: `seg4Ref_I`
- **Used by**: `seg4_ftc_neg_I`
- **Visibility**: private
- **Lines**: 166-171
- **Notes**: none

### `lemma seg4Ref_I_neg_slitPlane`
- **Type**: `(H : ℝ) (t : ℝ) : -(seg4Ref_I H t) ∈ Complex.slitPlane`
- **What**: `-seg4Ref_I` is in slit plane (real part of `seg4Ref_I` is `-1/2 < 0`).
- **How**: `Complex.mem_slitPlane_iff` then `norm_num` after computing real part.
- **Hypotheses**: none
- **Uses from project**: `seg4Ref_I`
- **Used by**: `seg4_ftc_neg_I`
- **Visibility**: private
- **Lines**: 173-179
- **Notes**: none

### `lemma seg4Ref_I_eq_35`
- **Type**: `(H : ℝ) : fdBoundaryFun H (3/5) - I = seg4Ref_I H (3/5)`
- **What**: Endpoint identity at `t = 3/5`.
- **How**: Rewrite `fdBoundaryFun_at_three_fifths`, unfold `seg4Ref_I`, `push_cast`, `ring`.
- **Hypotheses**: none
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_three_fifths`, `seg4Ref_I`, `ellipticPointRho`, `ellipticPointRho'`
- **Used by**: `seg4_ftc_neg_I`
- **Visibility**: private
- **Lines**: 181-186
- **Notes**: none

### `lemma seg4Ref_I_eq_45`
- **Type**: `(H : ℝ) : fdBoundaryFun H (4/5) - I = seg4Ref_I H (4/5)`
- **What**: Endpoint identity at `t = 4/5`.
- **How**: Rewrite `fdBoundaryFun_at_four_fifths`, unfold, `push_cast`, `ring`.
- **Hypotheses**: none
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_four_fifths`, `seg4Ref_I`
- **Used by**: `seg4_ftc_neg_I`
- **Visibility**: private
- **Lines**: 188-193
- **Notes**: none

### `lemma seg4Ref_I_eq`
- **Type**: `(H : ℝ) {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) : fdBoundaryFun H t - I = seg4Ref_I H t`
- **What**: Interior identity on `(3/5, 4/5]`.
- **How**: `simp` the `fdBoundaryFun` if-cases away, then `push_cast`, `ring`.
- **Hypotheses**: `3/5 < t`, `t ≤ 4/5`
- **Uses from project**: `fdBoundaryFun`, `seg4Ref_I`
- **Used by**: `seg4Ref_I_eventuallyEq`, `seg4_ftc_neg_I`
- **Visibility**: private
- **Lines**: 195-201
- **Notes**: none

### `lemma seg4Ref_I_eventuallyEq`
- **Type**: `(H : ℝ) {t : ℝ} (ht3 : 3/5 < t) (ht4 : t < 4/5) : (fun s => fdBoundaryFun H s - I) =ᶠ[𝓝 t] seg4Ref_I H`
- **What**: Local agreement of `fdBoundaryFun - I` with `seg4Ref_I` on `(3/5, 4/5)`.
- **How**: `Filter.eventually_of_mem` on `Ioi 3/5 ∩ Iio 4/5`, applying `seg4Ref_I_eq`.
- **Hypotheses**: `3/5 < t`, `t < 4/5`
- **Uses from project**: `fdBoundaryFun`, `seg4Ref_I`, `seg4Ref_I_eq`
- **Used by**: `seg4_ftc_neg_I`
- **Visibility**: private
- **Lines**: 203-209
- **Notes**: none

### `theorem seg4_ftc_neg_I`
- **Type**: `(H : ℝ) : IntervalIntegrable ... ∧ ∫ ... = log(-...) - log(-...)`
- **What**: FTC on seg4 `[3/5, 4/5]` using negated reference.
- **How**: `LogDerivFTC.ftc_log_neg_on_segment` + ae-congruence excluding right endpoint (`measure_singleton (4/5)`). Bridges actual integrand to reference via `seg4Ref_I_eq`/`seg4Ref_I_eventuallyEq` and endpoints via `seg4Ref_I_eq_35`/`seg4Ref_I_eq_45`. >10 lines.
- **Hypotheses**: none
- **Uses from project**: `LogDerivFTC.ftc_log_neg_on_segment`, `fdBoundaryFun`, `seg4Ref_I_contDiff`, `seg4Ref_I_neg_slitPlane`, `seg4Ref_I_eq`, `seg4Ref_I_eventuallyEq`, `seg4Ref_I_eq_35`, `seg4Ref_I_eq_45`
- **Used by**: `fdBoundary_ftc_telescope_I`
- **Visibility**: private
- **Lines**: 212-236
- **Notes**: >10 lines

### `def seg5Ref_I`
- **Type**: `(H : ℝ) (t : ℝ) : ℂ`
- **What**: Reference parametrization for seg5 (top horizontal), `(5t - 9/2) + (H-1)·I`.
- **How**: Direct affine expression.
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `seg5Ref_I_contDiff`, `seg5Ref_I_slitPlane`, `seg5Ref_I_eq`, `seg5Ref_I_eventuallyEq`, `seg5Ref_I_eq_45`, `seg5Ref_I_eq_1`, `seg5_ftc_full_I`
- **Visibility**: private
- **Lines**: 240
- **Notes**: none

### `lemma seg5Ref_I_contDiff`
- **Type**: `(H : ℝ) : ContDiff ℝ ⊤ (seg5Ref_I H)`
- **What**: seg5 reference is smooth.
- **How**: `contDiff_const.mul Complex.ofRealCLM.contDiff` composed with `.sub`/`.add`.
- **Hypotheses**: none
- **Uses from project**: `seg5Ref_I`
- **Used by**: `seg5_ftc_full_I`
- **Visibility**: private
- **Lines**: 242-244
- **Notes**: none

### `lemma seg5Ref_I_slitPlane`
- **Type**: `(H : ℝ) (hH : 1 < H) (t : ℝ) : seg5Ref_I H t ∈ Complex.slitPlane`
- **What**: seg5 reference has positive imaginary part `H-1 > 0`, hence in slit plane.
- **How**: `Complex.mem_slitPlane_iff` right branch (im ≠ 0), compute `im = H - 1 > 0`.
- **Hypotheses**: `1 < H`
- **Uses from project**: `seg5Ref_I`
- **Used by**: `seg5_ftc_full_I`
- **Visibility**: private
- **Lines**: 246-257
- **Notes**: none

### `lemma seg5Ref_I_eq`
- **Type**: `(H : ℝ) {t : ℝ} (ht : 4/5 < t) : fdBoundaryFun H t - I = seg5Ref_I H t`
- **What**: Interior identity on `(4/5, ?]`.
- **How**: Simp on `fdBoundaryFun` if-cases, then `ring`.
- **Hypotheses**: `4/5 < t`
- **Uses from project**: `fdBoundaryFun`, `seg5Ref_I`
- **Used by**: `seg5Ref_I_eventuallyEq`, `seg5_ftc_full_I`
- **Visibility**: private
- **Lines**: 259-264
- **Notes**: none

### `lemma seg5Ref_I_eventuallyEq`
- **Type**: `(H : ℝ) {t : ℝ} (ht : 4/5 < t) : (fun s => fdBoundaryFun H s - I) =ᶠ[𝓝 t] seg5Ref_I H`
- **What**: Local agreement on `(4/5, ∞)`.
- **How**: `Filter.eventually_of_mem (Ioi_mem_nhds ht)` + `seg5Ref_I_eq`.
- **Hypotheses**: `4/5 < t`
- **Uses from project**: `fdBoundaryFun`, `seg5Ref_I`, `seg5Ref_I_eq`
- **Used by**: `seg5_ftc_full_I`
- **Visibility**: private
- **Lines**: 266-268
- **Notes**: none

### `lemma seg5Ref_I_eq_45`
- **Type**: `(H : ℝ) : fdBoundaryFun H (4/5) - I = seg5Ref_I H (4/5)`
- **What**: Endpoint identity at `t = 4/5`.
- **How**: Rewrite `fdBoundaryFun_at_four_fifths`, then `push_cast`/`ring`.
- **Hypotheses**: none
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_four_fifths`, `seg5Ref_I`
- **Used by**: `seg5_ftc_full_I`
- **Visibility**: private
- **Lines**: 270-275
- **Notes**: none

### `lemma seg5Ref_I_eq_1`
- **Type**: `(H : ℝ) : fdBoundaryFun H 1 - I = seg5Ref_I H 1`
- **What**: Endpoint identity at `t = 1` (right end of contour).
- **How**: Rewrite `fdBoundaryFun_at_one`, unfold `fdStart`/`seg5Ref_I`, `push_cast`/`ring`.
- **Hypotheses**: none
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_one`, `seg5Ref_I`, `fdStart`
- **Used by**: `seg5_ftc_full_I`
- **Visibility**: private
- **Lines**: 277-282
- **Notes**: none

### `theorem seg5_ftc_full_I`
- **Type**: `(H : ℝ) (hH : 1 < H) : IntervalIntegrable ... ∧ ∫ ... = log(...) - log(...)`
- **What**: FTC on seg5 `[4/5, 1]`.
- **How**: `LogDerivFTC.ftc_log_pieceFM` with seg5 reference smoothness/slit-plane hypothesis + endpoint identities.
- **Hypotheses**: `1 < H`
- **Uses from project**: `LogDerivFTC.ftc_log_pieceFM`, `fdBoundaryFun`, `seg5Ref_I_contDiff`, `seg5Ref_I_slitPlane`, `seg5Ref_I_eq`, `seg5Ref_I_eventuallyEq`, `seg5Ref_I_eq_45`, `seg5Ref_I_eq_1`
- **Used by**: `fdBoundary_ftc_telescope_I`
- **Visibility**: private
- **Lines**: 285-300
- **Notes**: none

### `lemma log_neg_eq_add_pi_IFM`
- **Type**: `{z : ℂ} (_hz_ne : z ≠ 0) (hz_im : z.im < 0) : Complex.log (-z) = Complex.log z + ↑Real.pi * I`
- **What**: Branch correction for `log(-z)` when `z` is in lower half-plane.
- **How**: `Complex.arg_neg_eq_arg_add_pi_of_im_neg` on the `arg`, `norm_neg` for the modulus.
- **Hypotheses**: `z ≠ 0`, `z.im < 0`
- **Uses from project**: none
- **Used by**: `right_integral_34_branch_corrected`
- **Visibility**: private
- **Lines**: 304-310
- **Notes**: `_hz_ne` is unused (underscore).

### `lemma log_neg_eq_sub_pi_I`
- **Type**: `{z : ℂ} (_hz_ne : z ≠ 0) (hz_im : 0 < z.im) : Complex.log (-z) = Complex.log z - ↑Real.pi * I`
- **What**: Branch correction for `log(-z)` when `z` is in upper half-plane.
- **How**: `Complex.arg_neg_eq_arg_sub_pi_of_im_pos`, `norm_neg`.
- **Hypotheses**: `z ≠ 0`, `0 < z.im`
- **Uses from project**: none
- **Used by**: `right_integral_34_branch_corrected`
- **Visibility**: private
- **Lines**: 312-318
- **Notes**: `_hz_ne` is unused.

### `lemma fdBoundary_sub_I_at_35_im_neg`
- **Type**: `(H : ℝ) : (fdBoundaryFun H (3/5) - I).im < 0`
- **What**: At `t = 3/5` (which is `ρ`), `fdBoundaryFun - I` has negative imaginary part.
- **How**: Rewrite at `3/5` to `ρ`, then `nlinarith` using `√3 ≤ 2` (i.e. `(√3-2)² ≥ 0`).
- **Hypotheses**: none
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_three_fifths`, `ellipticPointRho`, `ellipticPointRho'`
- **Used by**: unused in file
- **Visibility**: private
- **Lines**: 322-329
- **Notes**: Declared but apparently not used in the file (used via the branch correction path only by the 2p_im_neg lemma).

### `lemma fdBoundary_sub_I_at_45_im_pos`
- **Type**: `(H : ℝ) (hH : 1 < H) : 0 < (fdBoundaryFun H (4/5) - I).im`
- **What**: At `t = 4/5`, `fdBoundaryFun - I` has positive imaginary part.
- **How**: Rewrite at `4/5` (top of left edge), compute `im = H - 1 > 0`.
- **Hypotheses**: `1 < H`
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_four_fifths`
- **Used by**: `right_integral_34_branch_corrected`
- **Visibility**: private
- **Lines**: 331-336
- **Notes**: none

### `lemma fdBoundary_sub_I_at_2p_im_neg`
- **Type**: `(H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) : (fdBoundaryFun H (2/5 + δ) - I).im < 0`
- **What**: Just past the crossing `t = 2/5` (where `arcRef_I = 0`), the imaginary part is negative.
- **How**: `fdBoundaryFun_arc_eq_exp` → `sin(fdArcAngle(2/5+δ)) < 1` via `Real.sin_pi_sub` and `Real.sin_lt_sin_of_lt_of_le_pi_div_two`.
- **Hypotheses**: `0 < δ`, `δ < 1/5`
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_arc_eq_exp`, `fdArcAngle`
- **Used by**: `right_integral_34_branch_corrected`
- **Visibility**: private
- **Lines**: 338-356
- **Notes**: >10 lines

### `lemma right_integral_34_branch_corrected`
- **Type**: `(H : ℝ) (hH : 1 < H) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) (hright34 : ∫ ... = log(-...) - log(-...)) : ∫ ... = log(...) - log(...) - 2 * π * I`
- **What**: Branch correction on `[2/5+δ, 4/5]`: combining the two `log(-z)` terms from seg3+seg4 into `log(z)` terms produces a `-2πI` offset.
- **How**: Apply `log_neg_eq_add_pi_IFM` at `t = 2/5+δ` (im < 0) and `log_neg_eq_sub_pi_I` at `t = 4/5` (im > 0); the sign discrepancy gives `-2πI`. Then `ring`.
- **Hypotheses**: `1 < H`, `0 < δ`, `δ < 1/5`, hypothesis that the integral equals the negated log form.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_sub_i_ne_zero_seg3`, `log_neg_eq_add_pi_IFM`, `log_neg_eq_sub_pi_I`, `fdBoundary_sub_I_at_2p_im_neg`, `fdBoundary_sub_I_at_45_im_pos`
- **Used by**: `fdBoundary_ftc_telescope_I`
- **Visibility**: private
- **Lines**: 363-386
- **Notes**: >10 lines

### `theorem fdBoundary_ftc_telescope_I`
- **Type**: `(H : ℝ) (hH : 1 < H) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) : (∫ ...) + (∫ ...) = log(...) - log(...) - 2*π*I`
- **What**: Full FTC telescope for the crossing at `i`: integral over `[0, 2/5-δ] ∪ [2/5+δ, 1]` equals the log difference plus the `-2πI` branch correction.
- **How**: Combine `seg1_ftc_I` (from CrossingAtI), `seg2_ftc_I`, `seg3_ftc_neg_I`, `seg4_ftc_neg_I`, `seg5_ftc_full_I` via `intervalIntegral.integral_add_adjacent_intervals`; apply `right_integral_34_branch_corrected`. Then rewrite via `integrand_form_eq` and `fdBoundaryFun_closed`. >10 lines.
- **Hypotheses**: `1 < H`, `0 < δ`, `δ < 1/5`
- **Uses from project**: `fdBoundaryFun`, `seg1_ftc_I`, `seg2_ftc_I`, `seg3_ftc_neg_I`, `seg4_ftc_neg_I`, `seg5_ftc_full_I`, `right_integral_34_branch_corrected`, `integrand_form_eq`, `fdBoundaryFun_closed`
- **Used by**: `arcFTCHyp_atI`
- **Visibility**: public (no `private`)
- **Lines**: 389-422
- **Notes**: >10 lines

### `def E_atI`
- **Type**: `(H : ℝ) (ε : ℝ) : ℂ`
- **What**: The error function used in `ArcFTCHyp`: the log difference at the two crossing points minus `2πI`.
- **How**: Direct definition `log(f(2/5-δ)-I) - log(f(2/5+δ)-I) - 2πI`, with `δ = arcsinDelta ε`.
- **Hypotheses**: none
- **Uses from project**: `fdBoundaryFun`, `arcsinDelta`
- **Used by**: `E_atI_tendsto`, `arcFTCHyp_atI`
- **Visibility**: private
- **Lines**: 426-428
- **Notes**: none

### `lemma arcsinDelta_tendsto_nhdsWithin`
- **Type**: `Tendsto arcsinDelta (𝓝[>] 0) (𝓝[>] 0)`
- **What**: `arcsinDelta` (a rescaled `arcsin`) is continuous and positive on the right at 0, hence sends `𝓝[>]0` to `𝓝[>]0`.
- **How**: Continuity from `Real.continuous_arcsin.continuousAt.comp` and `Real.arcsin_zero`; eventual positivity from `arcsinDelta_pos` for `ε < 1`.
- **Hypotheses**: none
- **Uses from project**: `arcsinDelta`, `arcsinDelta_pos`
- **Used by**: `E_atI_tendsto`
- **Visibility**: private
- **Lines**: 430-441
- **Notes**: none

### `theorem E_atI_tendsto`
- **Type**: `(H : ℝ) : Tendsto (E_atI H) (𝓝[>] 0) (𝓝 (-(↑Real.pi * I)))`
- **What**: As `ε → 0⁺`, `E_atI H ε → -πI`.
- **How**: Compose `fdBoundaryFun_log_diff_core_tendsto` (limit of log difference → `πI`) with `arcsinDelta_tendsto_nhdsWithin`, then subtract `2πI` constant to get `πI - 2πI = -πI`.
- **Hypotheses**: none
- **Uses from project**: `E_atI`, `fdBoundaryFun_log_diff_core_tendsto`, `arcsinDelta_tendsto_nhdsWithin`
- **Used by**: `arcFTCHyp_atI`
- **Visibility**: private
- **Lines**: 443-459
- **Notes**: >10 lines

### `def arcFTCHyp_atI`
- **Type**: `{H : ℝ} (hH : 1 < H) {γ : PiecewiseC1Path (fdStart H) (fdStart H)} (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) : ArcFTCHyp γ I (2/5) arcsinDelta (min (1/3) (H-1)) (-(↑Real.pi * I))`
- **What**: Bundles the full `ArcFTCHyp` instance at the crossing `i`: with `E = E_atI`, `δ = arcsinDelta`, `threshold = min(1/3, H-1)`, limit `L = -πI`.
- **How**: Provides `E := E_atI H`, `h_ftc` via `transfer_integral` + `fdBoundary_ftc_telescope_I`, `hint_left`/`hint_right` via `gamma_integrable_left_of_I`/`gamma_integrable_right_of_I`, `h_limit := E_atI_tendsto`.
- **Hypotheses**: `1 < H`, `γ` agrees with `fdBoundaryFun H` on `[0,1]`
- **Uses from project**: `ArcFTCHyp`, `E_atI`, `arcsinDelta`, `arcsinDelta_pos`, `arcsinDelta_lt_one_fifth`, `transfer_integral`, `fdBoundary_ftc_telescope_I`, `gamma_integrable_left_of_I`, `gamma_integrable_right_of_I`, `E_atI_tendsto`, `fdStart`, `fdBoundaryFun`, `PiecewiseC1Path`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 464-486
- **Notes**: >10 lines (struct constructor with multiple field proofs)

## File Summary

ArcFTCAtI.lean: 488 lines. Assembles a concrete `ArcFTCHyp` instance at the crossing `i` (parameter `t₀ = 2/5`) on the FD boundary. The file proceeds in seven parts: (1) reference function `arcRef_I` (the arc piece `exp(iφ(t)) - I`); (2) per-segment FTC for the five segments of the boundary (`seg2_ftc_I`, `seg3_ftc_neg_I`, `seg4_ftc_neg_I`, `seg5_ftc_full_I`, the seg1 piece imported from CrossingAtI); (3) branch correction lemmas `log(-z) = log(z) ± πI` depending on `im z`'s sign; (4) imaginary-part sign lemmas at the corners `3/5`, `4/5`, `2/5+δ`; (5) the full FTC telescope `fdBoundary_ftc_telescope_I` combining the five pieces and yielding `log(...) - log(...) - 2πI`; (6) the error function `E_atI` and its `ε → 0⁺` limit `→ -πI`; (7) assembly of `arcFTCHyp_atI`. The single public-facing definition is `arcFTCHyp_atI`; `fdBoundary_ftc_telescope_I` is technically non-private but used internally. No sorries, no axioms, no `set_option`s, no TODOs.
