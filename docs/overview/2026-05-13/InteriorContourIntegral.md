# InteriorContourIntegral.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/InteriorContourIntegral.lean` (531 lines)

### `private lemma abs_lt_of_sq_lt`
- **Type**: `{a b : ℝ} → a^2 < b^2 → |a| < |b|`
- **What**: Strict monotonicity of `abs` for squared real values.
- **How**: `nlinarith` with hints `sq_abs a, sq_abs b, sq_nonneg (|a| - |b|), abs_nonneg a, abs_nonneg b`.
- **Hypotheses**: `a^2 < b^2`.
- **Uses from project**: []
- **Used by**: `arcRef_slit_nonpos`, `arcRef_neg_slit_pos`
- **Visibility**: private
- **Lines**: 37-39
- **Notes**: None.

### `theorem im_gt_sqrt3_div_two_of_interior`
- **Type**: `{z : ℂ} → 1 < ‖z‖ → |z.re| < 1/2 → 0 < z.im → Real.sqrt 3 / 2 < z.im`
- **What**: For `z` in the strict interior of the fundamental domain (norm > 1, |Re| < 1/2, Im > 0), the imaginary part exceeds `√3/2`.
- **How**: From `one_lt_normSq_iff` derive `re² + im² > 1`; bound `re² < 1/4` via `nlinarith` and `sq_abs`; conclude `im² > 3/4`, then `im > √3/2` via `nlinarith` with `sq_nonneg (im - √3/2)`.
- **Hypotheses**: `‖z‖ > 1`, `|z.re| < 1/2`, `z.im > 0`.
- **Uses from project**: []
- **Used by**: `arcEndpoint_im_neg`, `bc35`
- **Visibility**: public
- **Lines**: 41-54
- **Notes**: >10 lines (14 lines).

### `private def ref1`
- **Type**: `(z : ℂ) (H : ℝ) (t : ℝ) → ℂ`
- **What**: Reference smooth path for segment 1 (left vertical edge): linear interpolation in `Im` from `H` down to `√3/2` at `Re = 1/2 - z.re`, used to express `fdBoundary(t) - z` as a smooth `(real, imag)` pair.
- **How**: `(1/2 - z.re) + (H - 5t(H - √3/2) - z.im) i`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `ref1_cd`, `ref1_eq`, `ref1_slit`, `seg1F`, `ftc_full`
- **Visibility**: private
- **Lines**: 58-59
- **Notes**: None.

### `private lemma ref1_cd`
- **Type**: `(z : ℂ) (H : ℝ) → ContDiff ℝ ⊤ (ref1 z H)`
- **What**: Smoothness of `ref1`.
- **How**: Decomposes via `ContDiff.add`, `Complex.ofRealCLM.contDiff.comp`, polynomial decomposition.
- **Hypotheses**: None.
- **Uses from project**: `ref1`
- **Used by**: `seg1F`
- **Visibility**: private
- **Lines**: 61-66
- **Notes**: None.

### `private lemma ref1_eq`
- **Type**: `(z : ℂ) (H : ℝ) {t : ℝ} → t ≤ 1/5 → fdBoundaryFun H t - z = ref1 z H t`
- **What**: `fdBoundaryFun(t) - z` equals `ref1(t)` on segment 1 (`t ≤ 1/5`).
- **How**: `simp` with `fdBoundaryFun` definition (selects seg1 branch), `Complex.ext`, then `push_cast` and component simp lemmas.
- **Hypotheses**: `t ≤ 1/5`.
- **Uses from project**: `fdBoundaryFun`, `ref1`
- **Used by**: `seg1F`
- **Visibility**: private
- **Lines**: 68-72
- **Notes**: None.

### `private lemma ref1_slit`
- **Type**: `(z : ℂ) (H : ℝ) → z.re < 1/2 → (t : ℝ) → ref1 z H t ∈ slitPlane`
- **What**: `ref1(t)` avoids the negative real axis (in slit plane), since its real part `1/2 - z.re > 0`.
- **How**: `mem_slitPlane_iff` left branch (positive real part), `linarith`.
- **Hypotheses**: `z.re < 1/2`.
- **Uses from project**: `ref1`
- **Used by**: `seg1F`
- **Visibility**: private
- **Lines**: 74-80
- **Notes**: None.

### `private def ref5`
- **Type**: `(z : ℂ) (H : ℝ) (t : ℝ) → ℂ`
- **What**: Reference smooth path for segment 5 (top horizontal edge): linear in Re from `1/2 - z.re` to `-1/2 - z.re`, constant imaginary `H - z.im`.
- **How**: `(5t - 9/2 - z.re) + (H - z.im) i`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `ref5_cd`, `ref5_eq`, `ref5_slit`, `seg5F`
- **Visibility**: private
- **Lines**: 82-83
- **Notes**: None.

### `private lemma ref5_cd`
- **Type**: `(z : ℂ) (H : ℝ) → ContDiff ℝ ⊤ (ref5 z H)`
- **What**: Smoothness of `ref5`.
- **How**: ContDiff composition via `Complex.ofRealCLM.contDiff.comp` and arithmetic.
- **Hypotheses**: None.
- **Uses from project**: `ref5`
- **Used by**: `seg5F`
- **Visibility**: private
- **Lines**: 84-88
- **Notes**: None.

### `private lemma ref5_eq`
- **Type**: `(z : ℂ) (H : ℝ) {t : ℝ} → 4/5 < t → fdBoundaryFun H t - z = ref5 z H t`
- **What**: `fdBoundaryFun(t) - z = ref5(t)` for strict interior of segment 5 (`4/5 < t`).
- **How**: `simp` with `fdBoundaryFun` selecting the seg5 branch (all four prior conditions false), `Complex.ext`, `push_cast`.
- **Hypotheses**: `4/5 < t`.
- **Uses from project**: `fdBoundaryFun`, `ref5`
- **Used by**: `seg5F`
- **Visibility**: private
- **Lines**: 90-95
- **Notes**: None.

### `private lemma ref5_slit`
- **Type**: `(z : ℂ) (H : ℝ) → z.im < H → (t : ℝ) → ref5 z H t ∈ slitPlane`
- **What**: `ref5(t)` avoids negative real axis when `z.im < H` (its imaginary part `H - z.im > 0`).
- **How**: `mem_slitPlane_iff` right branch (nonzero imaginary part), `linarith`.
- **Hypotheses**: `z.im < H`.
- **Uses from project**: `ref5`
- **Used by**: `seg5F`
- **Visibility**: private
- **Lines**: 97-104
- **Notes**: None.

### `private def ref4n`
- **Type**: `(z : ℂ) (H : ℝ) (t : ℝ) → ℂ`
- **What**: Negated reference path for segment 4 (right vertical edge, descending): `(z.re + 1/2) + (z.im - √3/2 - (5t-3)(H-√3/2)) i`. Represents `-(fdBoundary(t) - z)`.
- **How**: Direct definition.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `ref4n_cd`, `ref4n_eq`, `ref4n_slit`, `seg4F`
- **Visibility**: private
- **Lines**: 106-108
- **Notes**: None.

### `private lemma ref4n_cd`
- **Type**: `(z : ℂ) (H : ℝ) → ContDiff ℝ ⊤ (ref4n z H)`
- **What**: Smoothness of `ref4n`.
- **How**: ContDiff composition.
- **Hypotheses**: None.
- **Uses from project**: `ref4n`
- **Used by**: `seg4F`
- **Visibility**: private
- **Lines**: 110-115
- **Notes**: None.

### `private lemma ref4n_eq`
- **Type**: `(z : ℂ) (H : ℝ) {t : ℝ} → 3/5 < t → t ≤ 4/5 → -(fdBoundaryFun H t - z) = ref4n z H t`
- **What**: `-(fdBoundaryFun(t) - z) = ref4n(t)` on segment 4 (`3/5 < t ≤ 4/5`).
- **How**: `simp` with `fdBoundaryFun` branch selection, `Complex.ext`, `push_cast`, `ring`.
- **Hypotheses**: `3/5 < t`, `t ≤ 4/5`.
- **Uses from project**: `fdBoundaryFun`, `ref4n`
- **Used by**: `seg4F`
- **Visibility**: private
- **Lines**: 117-122
- **Notes**: None.

### `private lemma ref4n_slit`
- **Type**: `(z : ℂ) (H : ℝ) → -1/2 < z.re → (t : ℝ) → ref4n z H t ∈ slitPlane`
- **What**: `ref4n(t)` lies in slit plane when `-1/2 < z.re` (positive real part `z.re + 1/2`).
- **How**: `mem_slitPlane_iff` left branch, `linarith`.
- **Hypotheses**: `-1/2 < z.re`.
- **Uses from project**: `ref4n`
- **Used by**: `seg4F`
- **Visibility**: private
- **Lines**: 124-129
- **Notes**: None.

### `private theorem seg1F`
- **Type**: `(z : ℂ) (H : ℝ) → z.re < 1/2 → IntervalIntegrable … 0 (1/5) ∧ ∫_0^(1/5) deriv(γ - z)/(γ - z) = Complex.log(γ(1/5) - z) - Complex.log(γ(0) - z)` (with `γ = fdBoundaryFun H`)
- **What**: FTC on segment 1: the logarithmic-derivative integral telescopes to the log difference.
- **How**: Applies `LogDerivFTC.ftc_log_pieceFM` with smoothness from `ref1_cd`, slit-plane membership `ref1_slit`, and pointwise equality `ref1_eq`; provides `Filter.EventuallyEq.deriv_eq` for the derivative match.
- **Hypotheses**: `z.re < 1/2`.
- **Uses from project**: `LogDerivFTC.ftc_log_pieceFM`, `fdBoundaryFun`, `ref1_cd`, `ref1_slit`, `ref1_eq`
- **Used by**: `ftc_full`
- **Visibility**: private
- **Lines**: 133-147
- **Notes**: >10 lines (15 lines).

### `private theorem seg5F`
- **Type**: `(z : ℂ) (H : ℝ) → z.im < H → IntervalIntegrable … (4/5) 1 ∧ ∫_(4/5)^1 deriv(γ-z)/(γ-z) = Complex.log(γ(1) - z) - Complex.log(γ(4/5) - z)`
- **What**: FTC on segment 5 (top edge).
- **How**: `LogDerivFTC.ftc_log_pieceFM` with `ref5`; at endpoint `t = 4/5` cannot use `ref5_eq` (strict ineq), computes directly via `fdBoundaryFun_at_four_fifths` and `Complex.ext`.
- **Hypotheses**: `z.im < H`.
- **Uses from project**: `LogDerivFTC.ftc_log_pieceFM`, `fdBoundaryFun`, `fdBoundaryFun_at_four_fifths`, `ref5_cd`, `ref5_slit`, `ref5_eq`
- **Used by**: `ftc_full`
- **Visibility**: private
- **Lines**: 149-172
- **Notes**: >10 lines (24 lines).

### `private theorem seg4F`
- **Type**: `(z : ℂ) (H : ℝ) → -1/2 < z.re → IntervalIntegrable … (3/5) (4/5) ∧ ∫_(3/5)^(4/5) deriv(γ-z)/(γ-z) = Complex.log(-(γ(4/5) - z)) - Complex.log(-(γ(3/5) - z))`
- **What**: FTC on segment 4, integrating `-(γ - z)` (via `ref4n`).
- **How**: Establishes a.e. equality `deriv(γ - z)/(γ - z) = deriv(ref4n)/ref4n` via the negation identity (using `deriv.neg` and `neg_div_neg_eq`). Then applies `ftc_log_pieceFM` for `ref4n`, telescopes log difference, and matches endpoints using `ref4n_eq` (at `t = 4/5`) and explicit computation at `t = 3/5` via `fdBoundaryFun_at_three_fifths`.
- **Hypotheses**: `-1/2 < z.re`.
- **Uses from project**: `LogDerivFTC.ftc_log_pieceFM`, `fdBoundaryFun`, `fdBoundaryFun_at_three_fifths`, `ref4n`, `ref4n_cd`, `ref4n_eq`, `ref4n_slit`, `ellipticPointRho`, `ellipticPointRho'`
- **Used by**: `ftc_full`
- **Visibility**: private
- **Lines**: 174-222
- **Notes**: `set_option maxHeartbeats 400000`. >10 lines (49 lines).

### `private lemma fdArcAngle_contDiff'`
- **Type**: `ContDiff ℝ ⊤ fdArcAngle`
- **What**: Smoothness of the arc-angle parameterization function `fdArcAngle`.
- **How**: `unfold` then `fun_prop`.
- **Hypotheses**: None.
- **Uses from project**: `fdArcAngle`
- **Used by**: `arcRef_cd`
- **Visibility**: private
- **Lines**: 226-228
- **Notes**: None.

### `private def arcRef`
- **Type**: `(z : ℂ) (t : ℝ) → ℂ`
- **What**: Reference smooth curve for the arc (segments 2 and 3): `exp(i·fdArcAngle(t)) - z`.
- **How**: Direct definition.
- **Hypotheses**: None.
- **Uses from project**: `fdArcAngle`
- **Used by**: `arcRef_cd`, `arcRef_eq`, `arcRef_eq15`, `arcRef_eq35`, `arcRef_ee`, `arcRef_slit_nonpos`, `arcRef_neg_slit_pos`, `arcF_standard`, `arcF_negated`
- **Visibility**: private
- **Lines**: 230
- **Notes**: None.

### `private lemma arcRef_cd`
- **Type**: `(z : ℂ) → ContDiff ℝ ⊤ (arcRef z)`
- **What**: Smoothness of `arcRef`.
- **How**: `ContDiff.comp` with `Complex.contDiff_exp`, `ofRealCLM`, and `fdArcAngle_contDiff'`.
- **Hypotheses**: None.
- **Uses from project**: `arcRef`, `fdArcAngle_contDiff'`
- **Used by**: `arcF_standard`, `arcF_negated`
- **Visibility**: private
- **Lines**: 232-236
- **Notes**: None.

### `private lemma arcRef_eq`
- **Type**: `(z : ℂ) (H : ℝ) {t : ℝ} → 1/5 < t → t ≤ 3/5 → fdBoundaryFun H t - z = arcRef z t`
- **What**: `fdBoundaryFun(t) - z = arcRef(t)` on the arc (`1/5 < t ≤ 3/5`).
- **How**: `unfold arcRef`, then `fdBoundaryFun_arc_eq_exp`.
- **Hypotheses**: `1/5 < t`, `t ≤ 3/5`.
- **Uses from project**: `fdBoundaryFun`, `arcRef`, `fdBoundaryFun_arc_eq_exp`
- **Used by**: `arcRef_ee`, `arcF_standard`, `arcF_negated`
- **Visibility**: private
- **Lines**: 238-241
- **Notes**: None.

### `private lemma arcRef_eq15`
- **Type**: `(z : ℂ) (H : ℝ) → fdBoundaryFun H (1/5) - z = arcRef z (1/5)`
- **What**: Endpoint identity at `t = 1/5` (corner ρ+1).
- **How**: Computes via `fdArcAngle_at_one_fifth`, `fdBoundaryFun_at_one_fifth`, `exp_mul_I`, `cos_pi_div_three`, `sin_pi_div_three`, `push_cast`, `ring`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundaryFun`, `arcRef`, `fdArcAngle_at_one_fifth`, `fdBoundaryFun_at_one_fifth`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`
- **Used by**: `arcF_standard`, `arcF_negated`, `ftc_full`
- **Visibility**: private
- **Lines**: 243-250
- **Notes**: None.

### `private lemma arcRef_eq35`
- **Type**: `(z : ℂ) (H : ℝ) → fdBoundaryFun H (3/5) - z = arcRef z (3/5)`
- **What**: Endpoint identity at `t = 3/5` (corner ρ).
- **How**: Direct computation: `fdBoundaryFun_at_three_fifths`, set `fdArcAngle(3/5) = 2π/3 = π - π/3`, use `exp_mul_I`, `cos_pi_sub`, `sin_pi_sub`, `cos_pi_div_three`, `sin_pi_div_three`, `push_cast`, `ring`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundaryFun`, `arcRef`, `fdBoundaryFun_at_three_fifths`, `fdArcAngle`, `ellipticPointRho`, `ellipticPointRho'`
- **Used by**: `arcF_standard`, `arcF_negated`, `ftc_full`
- **Visibility**: private
- **Lines**: 252-264
- **Notes**: >10 lines (13 lines).

### `private lemma arcRef_ee`
- **Type**: `(z : ℂ) (H : ℝ) {t : ℝ} → 1/5 < t → t < 3/5 → (fun s => fdBoundaryFun H s - z) =ᶠ[𝓝 t] arcRef z`
- **What**: Local (eventual) equality of `fdBoundary - z` and `arcRef` in a neighborhood, used to transfer derivatives.
- **How**: `Filter.eventually_of_mem` over `Ioi 1/5 ∩ Iio 3/5`, apply `arcRef_eq` pointwise.
- **Hypotheses**: `1/5 < t`, `t < 3/5`.
- **Uses from project**: `fdBoundaryFun`, `arcRef`, `arcRef_eq`
- **Used by**: `arcF_standard`, `arcF_negated`
- **Visibility**: private
- **Lines**: 266-269
- **Notes**: None.

### `private lemma arcRef_slit_nonpos`
- **Type**: `{z : ℂ} → 1 < ‖z‖ → z.re ≤ 0 → 0 < z.im → {t : ℝ} → 1/5 ≤ t → t ≤ 3/5 → arcRef z t ∈ slitPlane`
- **What**: Arc reference lies in slit plane when `z.re ≤ 0` (standard branch case).
- **How**: Case on whether `sin(fdArcAngle t) = z.im`; if equal, derive `cos² = 1 - z.im² < z.re²` (using `‖z‖ > 1`), then `|cos| < -z.re` via `abs_lt_of_sq_lt`, conclude `cos - z.re > 0`. Otherwise, the imaginary part is non-zero (right branch of slit).
- **Hypotheses**: `‖z‖ > 1`, `z.re ≤ 0`, `z.im > 0`.
- **Uses from project**: `arcRef`, `fdArcAngle`, `abs_lt_of_sq_lt`
- **Used by**: `arcF_standard`
- **Visibility**: private
- **Lines**: 271-293
- **Notes**: `set_option maxHeartbeats 800000`. >10 lines (23 lines).

### `private lemma arcRef_neg_slit_pos`
- **Type**: `{z : ℂ} → 1 < ‖z‖ → 0 < z.re → 0 < z.im → {t : ℝ} → 1/5 ≤ t → t ≤ 3/5 → -(arcRef z t) ∈ slitPlane`
- **What**: Negated arc reference lies in slit plane when `z.re > 0` (negated branch case).
- **How**: Mirror of `arcRef_slit_nonpos`: case on `sin = z.im`; if so, `|cos| < z.re`; else, imaginary part non-zero.
- **Hypotheses**: `‖z‖ > 1`, `z.re > 0`, `z.im > 0`.
- **Uses from project**: `arcRef`, `fdArcAngle`, `abs_lt_of_sq_lt`
- **Used by**: `arcF_negated`
- **Visibility**: private
- **Lines**: 295-317
- **Notes**: `set_option maxHeartbeats 800000`. >10 lines (23 lines).

### `private theorem arcF_standard`
- **Type**: `{z : ℂ} → 1 < ‖z‖ → |z.re| < 1/2 → z.re ≤ 0 → 0 < z.im → (H : ℝ) → IntervalIntegrable … (1/5) (3/5) ∧ ∫_(1/5)^(3/5) deriv(γ-z)/(γ-z) = log(γ(3/5)-z) - log(γ(1/5)-z)`
- **What**: Arc FTC for `z.re ≤ 0` (standard slit-plane log).
- **How**: `LogDerivFTC.ftc_log_pieceFM` with `arcRef`, slit membership `arcRef_slit_nonpos`, pointwise equality `arcRef_eq`, eventual-equality derivative match `arcRef_ee.deriv_eq`, endpoint matches `arcRef_eq15`, `arcRef_eq35`.
- **Hypotheses**: `‖z‖ > 1`, `|z.re| < 1/2`, `z.re ≤ 0`, `z.im > 0`.
- **Uses from project**: `LogDerivFTC.ftc_log_pieceFM`, `fdBoundaryFun`, `arcRef_cd`, `arcRef_slit_nonpos`, `arcRef_eq`, `arcRef_ee`, `arcRef_eq15`, `arcRef_eq35`
- **Used by**: `arcF`
- **Visibility**: private
- **Lines**: 321-335
- **Notes**: >10 lines (15 lines).

### `private lemma log_neg_add_pi_of_im_neg`
- **Type**: `{w : ℂ} → w.im < 0 → Complex.log (-w) = Complex.log w + ↑Real.pi * I`
- **What**: Branch correction: `log(-w) = log(w) + iπ` when `Im w < 0`.
- **How**: Expand via `Real.log ‖·‖ + arg·I`; uses `norm_neg` and `arg_neg_eq_arg_add_pi_of_im_neg`.
- **Hypotheses**: `w.im < 0`.
- **Uses from project**: []
- **Used by**: `arcF_negated`
- **Visibility**: private
- **Lines**: 338-345
- **Notes**: None.

### `private lemma arcEndpoint_im_neg`
- **Type**: `{z : ℂ} → 1 < ‖z‖ → |z.re| < 1/2 → 0 < z.im → (H : ℝ) → (p : ℝ) → p ∈ {1/5, 3/5} → (fdBoundaryFun H p - z).im < 0`
- **What**: At the arc endpoints `p = 1/5` (ρ+1) and `p = 3/5` (ρ), the imaginary part of `γ(p) - z` is negative since `Im γ(p) = √3/2 < z.im`.
- **How**: Case split on `p ∈ {1/5, 3/5}`; compute `Im γ(p) = √3/2` via `fdBoundaryFun_at_one_fifth/three_fifths` and `ellipticPointRho/RhoPlusOne` simps; apply `im_gt_sqrt3_div_two_of_interior`.
- **Hypotheses**: `‖z‖ > 1`, `|z.re| < 1/2`, `z.im > 0`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_one_fifth`, `fdBoundaryFun_at_three_fifths`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`, `ellipticPointRho`, `ellipticPointRho'`, `im_gt_sqrt3_div_two_of_interior`
- **Used by**: `arcF_negated`
- **Visibility**: private
- **Lines**: 349-365
- **Notes**: >10 lines (17 lines).

### `private theorem arcF_negated`
- **Type**: `{z : ℂ} → 1 < ‖z‖ → |z.re| < 1/2 → 0 < z.re → 0 < z.im → (H : ℝ) → IntervalIntegrable … (1/5) (3/5) ∧ ∫_(1/5)^(3/5) deriv(γ-z)/(γ-z) = log(γ(3/5)-z) - log(γ(1/5)-z)`
- **What**: Arc FTC for `z.re > 0`, identical conclusion to `arcF_standard` but via negated branch (then branch-corrected back).
- **How**: Apply `LogDerivFTC.ftc_log_neg_on_segment` to `arcRef` (with `-arcRef ∈ slitPlane` from `arcRef_neg_slit_pos`). The result gives `log(-arcRef) - log(-arcRef)`; convert to `log(arcRef)` using `log_neg_add_pi_of_im_neg` at each endpoint (`arcEndpoint_im_neg`). The two `+ iπ` corrections cancel.
- **Hypotheses**: `‖z‖ > 1`, `|z.re| < 1/2`, `z.re > 0`, `z.im > 0`.
- **Uses from project**: `LogDerivFTC.ftc_log_neg_on_segment`, `fdBoundaryFun`, `arcRef_cd`, `arcRef_neg_slit_pos`, `arcRef_eq`, `arcRef_ee`, `arcRef_eq15`, `arcRef_eq35`, `arcEndpoint_im_neg`, `log_neg_add_pi_of_im_neg`
- **Used by**: `arcF`
- **Visibility**: private
- **Lines**: 367-396
- **Notes**: `set_option maxHeartbeats 800000`. >10 lines (30 lines).

### `private theorem arcF`
- **Type**: `{z : ℂ} → 1 < ‖z‖ → |z.re| < 1/2 → 0 < z.im → (H : ℝ) → IntervalIntegrable … (1/5) (3/5) ∧ ∫_(1/5)^(3/5) deriv(γ-z)/(γ-z) = log(γ(3/5)-z) - log(γ(1/5)-z)`
- **What**: Unified arc FTC, no sign restriction on `z.re`.
- **How**: `rcases le_or_gt z.re 0`; dispatch to `arcF_standard` or `arcF_negated`.
- **Hypotheses**: `‖z‖ > 1`, `|z.re| < 1/2`, `z.im > 0`.
- **Uses from project**: `fdBoundaryFun`, `arcF_standard`, `arcF_negated`
- **Used by**: `ftc_full`
- **Visibility**: private
- **Lines**: 398-408
- **Notes**: None.

### `private lemma bc35`
- **Type**: `{z : ℂ} {H : ℝ} → 1 < ‖z‖ → |z.re| < 1/2 → 0 < z.im → Complex.log (-(fdBoundaryFun H (3/5) - z)) = Complex.log (fdBoundaryFun H (3/5) - z) + ↑Real.pi * I`
- **What**: Branch correction at `t = 3/5` (`Im γ - z < 0`, so `log(-w) = log w + iπ`).
- **How**: Establish `Im γ(3/5) = √3/2 < z.im`, so `Im(γ - z) < 0`; expand log via `norm_neg`, `arg_neg_eq_arg_add_pi_of_im_neg`.
- **Hypotheses**: `‖z‖ > 1`, `|z.re| < 1/2`, `z.im > 0`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_three_fifths`, `ellipticPointRho`, `ellipticPointRho'`, `im_gt_sqrt3_div_two_of_interior`
- **Used by**: `ftc_full`
- **Visibility**: private
- **Lines**: 412-428
- **Notes**: >10 lines (17 lines).

### `private lemma bc45`
- **Type**: `{z : ℂ} {H : ℝ} → z.im < H → Complex.log (-(fdBoundaryFun H (4/5) - z)) = Complex.log (fdBoundaryFun H (4/5) - z) - ↑Real.pi * I`
- **What**: Branch correction at `t = 4/5` (`Im γ - z > 0`, so `log(-w) = log w - iπ`).
- **How**: `Im γ(4/5) = H > z.im` gives `Im(γ - z) > 0`; use `arg_neg_eq_arg_sub_pi_of_im_pos`.
- **Hypotheses**: `z.im < H`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_four_fifths`
- **Used by**: `ftc_full`
- **Visibility**: private
- **Lines**: 430-444
- **Notes**: >10 lines (15 lines).

### `private theorem ftc_full`
- **Type**: `{z : ℂ} {H : ℝ} → 1 < ‖z‖ → |z.re| < 1/2 → 0 < z.im → z.im < H → ∫_0^1 (fdBoundaryFun H t - z)⁻¹ * deriv (fdBoundaryFun H) t = -(2 * ↑Real.pi * I)`
- **What**: Full FTC: the contour integral of `(w - z)⁻¹` over the entire fundamental-domain boundary equals `-2πi` for interior `z`.
- **How**: Rewrite integrand via `deriv_add_const` to `deriv(γ - z) / (γ - z)`. Telescope on segments (`seg1F`, `arcF`, `seg4F`, `seg5F`); compute partial integrals: `h13 = ∫_0^(3/5) = log γ(3/5) - log γ(0)`, `h4 = ∫_(3/5)^(4/5) = log γ(4/5) - log γ(3/5) - 2πi` (using `bc35`, `bc45`). Combine via `intervalIntegral.integral_add_adjacent_intervals` and `fdBoundaryFun_closed`. Final `ring` cancels logs to yield `-2πi`.
- **Hypotheses**: `‖z‖ > 1`, `|z.re| < 1/2`, `0 < z.im < H`.
- **Uses from project**: `fdBoundaryFun`, `seg1F`, `arcF`, `seg4F`, `seg5F`, `bc35`, `bc45`, `fdBoundaryFun_closed`
- **Used by**: `fdBoundary_contourIntegral_interior_eq`
- **Visibility**: private
- **Lines**: 449-484
- **Notes**: `set_option maxHeartbeats 1600000`. >10 lines (36 lines).

### `private theorem xfer`
- **Type**: `{z : ℂ} {H : ℝ} → {γ : PiecewiseC1Path (fdStart H) (fdStart H)} → (∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) → γ.contourIntegral (fun w => (w - z)⁻¹) = ∫_0^1 (fdBoundaryFun H t - z)⁻¹ * deriv (fdBoundaryFun H) t`
- **What**: Transfers from a generic piecewise-`C¹` path `γ` (extension equal to `fdBoundaryFun` on `[0,1]`) to the explicit `fdBoundaryFun` integral.
- **How**: Unfold `PiecewiseC1Path.contourIntegral`; show a.e. equality of integrands on `(0, 1)` via `Ioo_mem_nhds`; transfer derivative via `Filter.EventuallyEq.deriv_eq`.
- **Hypotheses**: Pathwise equality of `γ.extend` and `fdBoundaryFun` on `[0,1]`.
- **Uses from project**: `PiecewiseC1Path.contourIntegral`, `fdBoundaryFun`, `fdStart`
- **Used by**: `fdBoundary_contourIntegral_interior_eq`
- **Visibility**: private
- **Lines**: 486-503
- **Notes**: >10 lines (18 lines).

### `theorem fdBoundary_contourIntegral_interior_eq`
- **Type**: `{H : ℝ} → H > Real.sqrt 3 / 2 → {z : ℂ} → FDStrictInterior z H → {γ : PiecewiseC1Path (fdStart H) (fdStart H)} → (∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) → γ.contourIntegral (fun w => (w - z)⁻¹) = -(2 * ↑Real.pi * I)`
- **What**: **Headline**: Interior contour integral of `(w - z)⁻¹` around FD boundary equals `-2πi`.
- **How**: Combine `xfer` to switch from generic `γ` to `fdBoundaryFun`, then apply `ftc_full` with hypotheses extracted from `FDStrictInterior`.
- **Hypotheses**: `H > √3/2`, `z ∈ FDStrictInterior H`, path matches `fdBoundaryFun`.
- **Uses from project**: `xfer`, `ftc_full`, `FDStrictInterior`, `fdStart`, `fdBoundaryFun`
- **Used by**: `fdBoundaryPC1Path_contourIntegral_interior_eq`, `fdBoundary_interior_winding_complete`
- **Visibility**: public
- **Lines**: 506-512
- **Notes**: None.

### `theorem fdBoundaryPC1Path_contourIntegral_interior_eq`
- **Type**: `{H : ℝ} → H > Real.sqrt 3 / 2 → {z : ℂ} → FDStrictInterior z H → (fdBoundaryPC1Path H hH).contourIntegral (fun w => (w - z)⁻¹) = -(2 * ↑Real.pi * I)`
- **What**: Specialization of the headline to the canonical `fdBoundaryPC1Path`.
- **How**: Apply `fdBoundary_contourIntegral_interior_eq` with `fdBoundaryPC1Path_eq` as the path-equality witness.
- **Hypotheses**: `H > √3/2`, `z ∈ FDStrictInterior H`.
- **Uses from project**: `fdBoundary_contourIntegral_interior_eq`, `fdBoundaryPC1Path`, `fdBoundaryPC1Path_eq`, `FDStrictInterior`
- **Used by**: External downstream code; not used in file.
- **Visibility**: public
- **Lines**: 515-519
- **Notes**: None.

### `theorem fdBoundary_interior_winding_complete`
- **Type**: `{H : ℝ} → H > Real.sqrt 3 / 2 → {z : ℂ} → FDStrictInterior z H → {γ : PiecewiseC1Path (fdStart H) (fdStart H)} → (∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) → HasGeneralizedWindingNumber γ z (-1)`
- **What**: **Interior winding number = -1**.
- **How**: Apply `hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral` with the contour integral identity from `fdBoundary_contourIntegral_interior_eq` and hypotheses extracted from `FDStrictInterior`.
- **Hypotheses**: `H > √3/2`, `z ∈ FDStrictInterior H`, path matches.
- **Uses from project**: `hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral`, `fdBoundary_contourIntegral_interior_eq`, `FDStrictInterior`, `fdStart`, `fdBoundaryFun`, `HasGeneralizedWindingNumber`
- **Used by**: External downstream code.
- **Visibility**: public
- **Lines**: 522-529
- **Notes**: None.

## File Summary

This file proves that for any `z` in the strict interior of the modular fundamental domain (`‖z‖ > 1`, `|Re z| < 1/2`, `0 < Im z < H`), the contour integral of `(w - z)⁻¹` around the boundary of `fdBox H` equals `-2πi`, equivalently the generalized winding number equals `-1`. Strategy: split the boundary into five pieces (two vertical segments, two arc halves, one horizontal segment), build reference smooth functions `ref1`, `ref5`, `ref4n`, `arcRef` that match `fdBoundary - z` on each piece, prove each reference avoids the slit plane's branch cut, apply `LogDerivFTC.ftc_log_pieceFM` to telescope each segment's integral into a `log(end) - log(start)` difference. Two branch corrections (`bc35`, `bc45`) absorb the `±iπ` from the negated segment 4 and arc-when-`z.re > 0` case. The total telescoping `log` terms vanish; only `-2πi` remains. Headline theorems: `fdBoundary_contourIntegral_interior_eq` (contour integral form), `fdBoundary_interior_winding_complete` (winding number form). Total: 31 declarations (mostly private), 4 `set_option maxHeartbeats` (400k, 800k×2, 1.6M), no `sorry`.
