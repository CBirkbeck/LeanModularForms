# Inventory: ValenceFormula/WindingWeights/Common.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ValenceFormula/WindingWeights/Common.lean` (312 lines)

Purpose: Shared infrastructure for the winding-weight proofs at the elliptic points `ρ`, `ρ+1`, and `i`. Provides:
1. Pointwise formulas for the height-`H` fundamental-domain boundary `fdBoundary_H` at the canonical breakpoints and along each of its five segments.
2. Continuity of `Complex.arg` and `Complex.log` on the closed upper half-plane minus 0.
3. FTC-for-log helpers on segments where `h` stays in `slitPlane`, in the closed upper half-plane (`im ≥ 0`), or in the closed lower half-plane (`im ≤ 0`).
4. HasDerivAt and continuity lemmas for the arc parameterization `t ↦ exp(i π (1+t)/6) − s`.
5. Three "nhds-equality from interval-agreement" helpers.

Imports: `LeanModularForms.ForMathlib.ValenceFormula.Boundary.Smooth`, `LeanModularForms.ForMathlib.SegmentFTC`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds`, `LeanModularForms.ForMathlib.TrigLemmas`.

Top-level: `attribute [local instance] Classical.propDecidable`; `noncomputable section`. Closes with `end` at line 312.

---

### `noncomputable instance instNormSMulClassRealComplex'`
- **Type**: `NormSMulClass ℝ ℂ`
- **What**: Work around mathlib 4.29-rc8 instance synthesis bug for ℝ-scalar-on-ℂ.
- **How**: `@NormedSpace.toNormSMulClass ℝ ℂ _ _ _` (delegating to the typeclass producer).
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: implicitly used by instance synthesis in the file.
- **Visibility**: public instance
- **Lines**: 25–26

### `theorem fdBoundary_H_at_one_eq_rho_plus_one`
- **Type**: `(H : ℝ) : fdBoundary_H H 1 = ellipticPointRhoPlusOne`
- **What**: At parameter `t = 1`, the FD boundary equals `ρ+1`.
- **How**: Unfold `fdBoundary_H`; both branches of the `if t ≤ 1` are equal at `t = 1`; rewrite `ellipticPointRhoPlusOne'` via `UpperHalfPlane.coe_mk`, `ofReal_one`; close with `ring`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_H`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`.
- **Used by**: unused in file (used by downstream WindingWeights modules).
- **Visibility**: public
- **Lines**: 30–36

### `theorem fdBoundary_H_at_two_eq_I`
- **Type**: `(H : ℝ) : fdBoundary_H H 2 = I`
- **What**: At parameter `t = 2`, the FD boundary equals the elliptic point `i`.
- **How**: `fdBoundary_H` reduces to `exp((π/3 + (2−1)(π/2 − π/3)) · I) = exp((π/2) · I)`; simplify angle via `push_cast; ring`; conclude via `exp_real_angle_I`, `Real.cos_pi_div_two`, `Real.sin_pi_div_two`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_H`, `exp_real_angle_I`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 38–49
- **Notes**: >10 lines.

### `theorem fdBoundary_H_at_three_eq_rho`
- **Type**: `(H : ℝ) : fdBoundary_H H 3 = ellipticPointRho`
- **What**: At parameter `t = 3`, the FD boundary equals `ρ`.
- **How**: `fdBoundary_H` becomes `exp((π/2 + (3-2)(2π/3 − π/2)) · I) = exp((2π/3) · I)`; simplify with `push_cast; ring`; conclude via `exp_real_angle_I` + `cos_two_pi_div_three` + `sin_two_pi_div_three` + `ring`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_H`, `exp_real_angle_I`, `cos_two_pi_div_three`, `sin_two_pi_div_three`, `ellipticPointRho`, `ellipticPointRho'`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 51–64
- **Notes**: >10 lines.

### `theorem fdBoundary_H_seg0`
- **Type**: `(H : ℝ) {t : ℝ} (ht : t ≤ 1) : fdBoundary_H H t = 1/2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I`
- **What**: Explicit formula for the FD boundary on segment 0 (the right vertical edge above `ρ+1`).
- **How**: `simp only [fdBoundary_H, ht, ↓reduceIte]`.
- **Hypotheses**: `t ≤ 1`.
- **Uses from project**: `fdBoundary_H`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 66–68

### `theorem fdBoundary_H_seg1`
- **Type**: `(H : ℝ) {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : t ≤ 2) : fdBoundary_H H t = exp ((↑(Real.pi : ℝ) / 3 + (↑t - 1) * (↑(Real.pi : ℝ) / 2 - ↑(Real.pi : ℝ) / 3)) * I)`
- **What**: Explicit formula for segment 1 (right half of the unit-circle arc from `ρ+1` to `i`).
- **How**: `simp only` with the segment-selectors.
- **Hypotheses**: `¬(t ≤ 1)`, `t ≤ 2`.
- **Uses from project**: `fdBoundary_H`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 70–73

### `theorem fdBoundary_H_seg2`
- **Type**: `(H : ℝ) {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : ¬(t ≤ 2)) (ht3 : t ≤ 3) : fdBoundary_H H t = exp ((↑(Real.pi : ℝ) / 2 + (↑t - 2) * (2 * ↑(Real.pi : ℝ) / 3 - ↑(Real.pi : ℝ) / 2)) * I)`
- **What**: Explicit formula for segment 2 (left half of the unit-circle arc from `i` to `ρ`).
- **How**: `simp only` with selectors.
- **Hypotheses**: `¬(t ≤ 1)`, `¬(t ≤ 2)`, `t ≤ 3`.
- **Uses from project**: `fdBoundary_H`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 75–79

### `theorem fdBoundary_H_seg3`
- **Type**: `(H : ℝ) {t : ℝ}` with `¬(t ≤ 1), ¬(t ≤ 2), ¬(t ≤ 3), t ≤ 4`; `fdBoundary_H H t = -1/2 + (↑(Real.sqrt 3) / 2 + (↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I`
- **What**: Explicit formula for segment 3 (left vertical edge above `ρ`).
- **How**: `simp only` with selectors.
- **Hypotheses**: `¬(t ≤ 1), ¬(t ≤ 2), ¬(t ≤ 3), t ≤ 4`.
- **Uses from project**: `fdBoundary_H`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 81–85

### `theorem fdBoundary_H_seg4`
- **Type**: `(H : ℝ) {t : ℝ}` with `¬(t ≤ 1), ¬(t ≤ 2), ¬(t ≤ 3), ¬(t ≤ 4)`; `fdBoundary_H H t = (↑t - 9/2) + ↑H * I`
- **What**: Explicit formula for segment 4 (top horizontal edge at height `H`).
- **How**: `simp only` with selectors.
- **Hypotheses**: `¬(t ≤ 1), ¬(t ≤ 2), ¬(t ≤ 3), ¬(t ≤ 4)`.
- **Uses from project**: `fdBoundary_H`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 87–90

### `theorem fdBoundary_H_eq_arc`
- **Type**: `{H : ℝ} {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) : fdBoundary_H H t = Complex.exp (↑(Real.pi * (1 + t) / 6) * I)`
- **What**: For `t ∈ (1, 3)`, the FD boundary equals the unit-circle arc point `exp(iπ(1+t)/6)`.
- **How**: First reduce `¬(t ≤ 1)`; case-split `t ≤ 2`; on each, `congr 1; push_cast; ring` to align the angle parameter.
- **Hypotheses**: `1 < t`, `t < 3`.
- **Uses from project**: `fdBoundary_H`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 92–103
- **Notes**: >10 lines.

### `lemma ftc_log_pieceFM`
- **Type**: `{g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hh_cont : ContinuousOn h (Icc a b)) (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t) (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b)) (hh_slit : ∀ t ∈ Icc a b, h t ∈ slitPlane) (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t) (heq_a : g a = h a) (heq_b : g b = h b) : IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧ ∫ t in a..b, deriv g t / g t = log (g b) - log (g a)`
- **What**: Thin wrapper: re-exports `LogDerivFTC.ftc_log_pieceFM` (FTC piece for `g` agreeing with a `slitPlane`-valued reference `h`).
- **How**: Direct application of `LogDerivFTC.ftc_log_pieceFM`.
- **Hypotheses**: same as `LogDerivFTC.ftc_log_pieceFM`.
- **Uses from project**: `LogDerivFTC.ftc_log_pieceFM`.
- **Used by**: `ftc_piece_of_hasDerivAt`.
- **Visibility**: public
- **Lines**: 105–113

### `lemma continuousOn_arg_im_nonneg`
- **Type**: `ContinuousOn Complex.arg {z : ℂ | 0 ≤ z.im ∧ z ≠ 0}`
- **What**: `Complex.arg` is continuous on the closed upper half-plane minus 0.
- **How**: On this set, `arg z = arccos (re/‖z‖)` (via `Complex.arg_of_im_nonneg_of_ne_zero`); apply `Continuous.div` + `Continuous.arccos`; `ContinuousWithinAt.congr` to swap to `arg`.
- **Hypotheses**: none beyond signature.
- **Uses from project**: [].
- **Used by**: `continuousOn_clog_im_nonneg`.
- **Visibility**: public
- **Lines**: 115–122

### `lemma continuousOn_clog_im_nonneg`
- **Type**: `ContinuousOn Complex.log {z : ℂ | 0 ≤ z.im ∧ z ≠ 0}`
- **What**: `Complex.log` is continuous on the closed upper half-plane minus 0.
- **How**: Rewrite `log = (fun w => ↑(Real.log ‖w‖) + ↑(arg w) * I)`; continuity of the real-log composed with `‖·‖`; continuity of `arg` from `continuousOn_arg_im_nonneg`; combine with `ContinuousWithinAt.add` and `.mul`.
- **Hypotheses**: none beyond signature.
- **Uses from project**: `continuousOn_arg_im_nonneg`.
- **Used by**: `ftc_log_piece_upper`, `ftc_log_piece_lower`.
- **Visibility**: public
- **Lines**: 124–135
- **Notes**: >10 lines.

### `lemma ftc_log_piece_upper`
- **Type**: `{g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hh_cont : ContinuousOn h (Icc a b)) (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t) (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b)) (hh_im_nn : ∀ t ∈ Icc a b, 0 ≤ (h t).im) (hh_ne : ∀ t ∈ Icc a b, h t ≠ 0) (hh_slit_interior : ∀ t ∈ Ioo a b, h t ∈ slitPlane) (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t) (heq_a : g a = h a) (heq_b : g b = h b) : IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧ ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a)`
- **What**: FTC for log-derivative when `h` stays in the closed upper half-plane minus 0 (only requiring `slitPlane` membership on the open interior), with `g` agreeing with `h` on `Ioo a b` and the endpoints.
- **How**: Compose `continuousOn_clog_im_nonneg` with `hh_cont` to get continuity of `log ∘ h` on `Icc`; integrability of `h'/h` via `ContinuousOn.div`; a.e. agreement of `g'/g = h'/h` modulo `{b}ᶜ`; assemble FTC via `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` using `clog_real` for the open-interior `slitPlane`-derivative; the empty `Ioc b a` case via `integrableOn_empty`.
- **Hypotheses**: `a ≤ b`; `h` continuous on `Icc`; differentiable on `Ioo`; deriv continuous on `Icc`; `0 ≤ (h t).im` on `Icc`; `h t ≠ 0` on `Icc`; `h t ∈ slitPlane` on `Ioo`; pointwise agreement `g = h` on `Ioo` and endpoints.
- **Uses from project**: `continuousOn_clog_im_nonneg`.
- **Used by**: `ftc_piece_upper_of_hasDerivAt`.
- **Visibility**: public
- **Lines**: 137–178
- **Notes**: >30 lines (42 lines); follows the same skeleton as `LogDerivFTC.ftc_log_pieceFM` but with the weakened slit-plane hypothesis.

### `lemma ftc_log_piece_lower`
- **Type**: `{g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hh_cont : ContinuousOn h (Icc a b)) (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t) (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b)) (hh_im_np : ∀ t ∈ Icc a b, (h t).im ≤ 0) (hh_ne : ∀ t ∈ Icc a b, h t ≠ 0) (hh_im_neg_interior : ∀ t ∈ Ioo a b, (h t).im < 0) (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t) (heq_a : g a = h a) (heq_b : g b = h b) : IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧ ∫ t in a..b, deriv g t / g t = Complex.log (-(g b)) - Complex.log (-(g a))`
- **What**: FTC for log-derivative when `h` stays in the closed lower half-plane minus 0 (with strictly negative imaginary part on the interior); primitive is `log ∘ (−h)`.
- **How**: Continuity of `log(−h)` on `Icc` via `continuousOn_clog_im_nonneg` after `.neg` (using `Complex.neg_im` + `Left.nonneg_neg_iff`); `(−h)` lies in `slitPlane` on `Ioo` via `mem_slitPlane_iff` taking the right disjunct; key derivative identity `−deriv h / −h = deriv h / h` via `neg_div_neg_eq`; `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` finishes; the empty `Ioc b a` case via `integrableOn_empty`.
- **Hypotheses**: `a ≤ b`; `h` continuous/diff/`deriv` continuous as before; `h t ≤ 0` (`im`) on `Icc`; `h t ≠ 0` on `Icc`; `h t .im < 0` on `Ioo`; pointwise agreement.
- **Uses from project**: `continuousOn_clog_im_nonneg`.
- **Used by**: unused in file (used by lower-half-plane segment proofs downstream).
- **Visibility**: public
- **Lines**: 180–234
- **Notes**: >30 lines (55 lines).

### `lemma ftc_piece_of_hasDerivAt`
- **Type**: `{g h : ℝ → ℂ} {a b : ℝ} {d : ℝ → ℂ} (hab : a ≤ b) (hd : ∀ t : ℝ, HasDerivAt h (d t) t) (hd_cont : Continuous d) (hg_eq : ∀ t, a ≤ t → t ≤ b → g t = h t) (hg_eq_nhds : ∀ t ∈ Ioo a b, g =ᶠ[𝓝 t] h) (hh_slit : ∀ t ∈ Icc a b, h t ∈ slitPlane) : IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧ ∫ t in a..b, deriv g t / g t = log (g b) - log (g a)`
- **What**: User-friendly FTC: given a derivative function `d` for `h` and `g = h` on `[a,b]` (with `g =ᶠ h` in nhds for interior points), conclude integrability and FTC for `g`.
- **How**: Reduce to `ftc_log_pieceFM` by extracting continuity-at and differentiability from `HasDerivAt`; rewrite `deriv h = d` via `funext (hd t).deriv` to obtain continuity of `deriv h`; the `eq` argument follows by `EventuallyEq.deriv_eq` and pointwise.
- **Hypotheses**: `a ≤ b`; pointwise HasDerivAt; continuity of the derivative; pointwise + nhds agreement; `slitPlane` on `Icc`.
- **Uses from project**: `ftc_log_pieceFM` (which calls `LogDerivFTC.ftc_log_pieceFM`).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 238–251
- **Notes**: >10 lines.

### `lemma ftc_piece_upper_of_hasDerivAt`
- **Type**: `{g h : ℝ → ℂ} {a b : ℝ} {d : ℝ → ℂ} (hab : a ≤ b) (hd : ∀ t : ℝ, HasDerivAt h (d t) t) (hd_cont : Continuous d) (hg_eq : ∀ t, a ≤ t → t ≤ b → g t = h t) (hg_eq_nhds : ∀ t ∈ Ioo a b, g =ᶠ[𝓝 t] h) (hh_im_nn : ∀ t ∈ Icc a b, 0 ≤ (h t).im) (hh_ne : ∀ t ∈ Icc a b, h t ≠ 0) (hh_slit_int : ∀ t ∈ Ioo a b, h t ∈ slitPlane) : IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧ ∫ t in a..b, deriv g t / g t = log (g b) - log (g a)`
- **What**: Variant of `ftc_piece_of_hasDerivAt` requiring `slitPlane` only on the open interior, with closed upper-half-plane membership on `Icc`.
- **How**: Reduce to `ftc_log_piece_upper` analogously to the previous lemma.
- **Hypotheses**: HasDerivAt + continuity of `d`; agreement; `h` non-zero on `Icc`; `im ≥ 0` on `Icc`; `slitPlane` on `Ioo`.
- **Uses from project**: `ftc_log_piece_upper`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 254–270
- **Notes**: >10 lines.

### `lemma hasDerivAt_arc`
- **Type**: `(s : ℂ) : ∀ t : ℝ, HasDerivAt (fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - s) (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t`
- **What**: `t ↦ exp(i π (1+t)/6) − s` has derivative `(π/6) · i · exp(i π (1+t)/6)`.
- **How**: Compute derivative of `Real.pi * (1+t)/6` (via `hasDerivAt_id.add_const.const_mul.congr_of_eventuallyEq`), then `.ofReal_comp.mul_const I`, then `.cexp.sub (hasDerivAt_const t s)`, then `.congr_deriv` with `simp [sub_zero]; ring`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: unused in file (used by downstream arc-specific winding-weight proofs).
- **Visibility**: public
- **Lines**: 273–287
- **Notes**: >10 lines.

### `lemma continuous_arc_deriv`
- **Type**: `(_ : ℂ) : Continuous (fun t : ℝ => ↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I))`
- **What**: Continuity of the arc derivative (s is an unused argument for API symmetry).
- **How**: `Continuous.mul continuous_const (Continuous.cexp (Continuous.mul (continuous_ofReal.comp …) continuous_const))` using `fun_prop` on the polynomial in `t`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 290–294

### `lemma eventuallyEq_of_Ioo_subset`
- **Type**: `{g h : ℝ → ℂ} {a b : ℝ} (hg_eq : ∀ t, a < t → t < b → g t = h t) (t : ℝ) (ht : t ∈ Ioo a b) : g =ᶠ[𝓝 t] h`
- **What**: Pointwise agreement on `Ioo a b` upgrades to nhds-agreement at each interior point.
- **How**: `Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2)`.
- **Hypotheses**: `t ∈ Ioo a b`; pointwise agreement.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 297–300

### `lemma eventuallyEq_of_Iio`
- **Type**: `{g h : ℝ → ℂ} {b : ℝ} (hg_eq : ∀ t, t < b → g t = h t) (t : ℝ) (ht : t < b) : g =ᶠ[𝓝 t] h`
- **What**: Pointwise agreement on `Iio b` upgrades to nhds-agreement.
- **How**: `Filter.eventually_of_mem (Iio_mem_nhds ht)`.
- **Hypotheses**: `t < b`.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 303–305

### `lemma eventuallyEq_of_Ioi`
- **Type**: `{g h : ℝ → ℂ} {a : ℝ} (hg_eq : ∀ t, a < t → g t = h t) (t : ℝ) (ht : a < t) : g =ᶠ[𝓝 t] h`
- **What**: Pointwise agreement on `Ioi a` upgrades to nhds-agreement.
- **How**: `Filter.eventually_of_mem (Ioi_mem_nhds ht)`.
- **Hypotheses**: `a < t`.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 308–310

---

## File Summary

- **Declarations**: 21 named declarations: 1 instance, 9 `fdBoundary_H` evaluation/segment lemmas (`_at_one`, `_at_two`, `_at_three`, `_seg0`–`_seg4`, `_eq_arc`), 1 thin re-export `ftc_log_pieceFM`, 2 continuity lemmas (`continuousOn_arg_im_nonneg`, `continuousOn_clog_im_nonneg`), 2 long FTC piece lemmas (`ftc_log_piece_upper`, `ftc_log_piece_lower`), 2 `HasDerivAt`-based FTC wrappers (`ftc_piece_of_hasDerivAt`, `ftc_piece_upper_of_hasDerivAt`), 2 arc lemmas (`hasDerivAt_arc`, `continuous_arc_deriv`), 3 nhds-equality helpers (`eventuallyEq_of_Ioo_subset`, `eventuallyEq_of_Iio`, `eventuallyEq_of_Ioi`).
- **Theme**: One-stop shop of pointwise/segment formulas for `fdBoundary_H`, continuity of `Complex.log`/`Complex.arg` on the upper half-plane minus 0, FTC-for-log lemmas tuned to upper- and lower-half-plane segments, and arc parameter derivatives. Used by the ρ, ρ+1, and i winding-weight proofs downstream.
- **Internal call graph**: `continuousOn_clog_im_nonneg` (built on `continuousOn_arg_im_nonneg`) underpins `ftc_log_piece_upper` and `ftc_log_piece_lower`. `ftc_log_pieceFM` (thin wrapper around `LogDerivFTC.ftc_log_pieceFM`) underpins `ftc_piece_of_hasDerivAt`, and `ftc_log_piece_upper` underpins `ftc_piece_upper_of_hasDerivAt`. The remaining lemmas are standalone.
- **Imports**: `LeanModularForms.ForMathlib.ValenceFormula.Boundary.Smooth` (provides `fdBoundary_H`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, etc.); `LeanModularForms.ForMathlib.SegmentFTC` (`LogDerivFTC.ftc_log_pieceFM`); `LeanModularForms.ForMathlib.TrigLemmas` (`exp_real_angle_I`, `cos_two_pi_div_three`, `sin_two_pi_div_three`); plus Mathlib `Trigonometric.Bounds`.
- **Notes**: No `set_option`, no `sorry`, no `axiom`, no `TODO`. Contains a workaround `noncomputable instance` for a mathlib 4.29-rc8 instance-synthesis issue. Several FTC lemmas exceed 30 lines.
