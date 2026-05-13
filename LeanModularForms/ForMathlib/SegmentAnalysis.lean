/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDBoundaryPath
import LeanModularForms.ForMathlib.ArcFTCLimit
import LeanModularForms.ForMathlib.SegmentFTC

/-!
# Segment FTC and Integrability for FD Boundary Segments

This file proves integrability and FTC for the log-derivative integrand
`(γ(t) - z₀)⁻¹ * γ'(t)` along each of the 5 segments of the fundamental domain
boundary, for the crossing point `z₀ = i`.

## Strategy

For each segment, we define a smooth reference function that equals
`fdBoundaryFun H t - I` on the segment. Since each reference is `ContDiff ℝ ⊤`
and nonvanishing (checked via the real or imaginary part), the log-derivative
integrand is continuous and hence integrable. These are combined across segments
via `IntervalIntegrable.trans` and transferred to the `PiecewiseC1Path` via
ae-equality.

## Main results

### Per-segment integrability

* `fdBoundary_seg1_intervalIntegrable_I` — seg1 `[0, a]` for `a ≤ 1/5`
* `seg2_intervalIntegrable_I` — seg2 `[1/5, a]` for `a < 2/5`
* `seg3_intervalIntegrable_I` — seg3 `[a, 3/5]` for `2/5 < a`
* `seg4_full_intervalIntegrable_I` — seg4 `[3/5, 4/5]`
* `seg5_full_intervalIntegrable_I` — seg5 `[4/5, 1]`

### Combined integrability (fills `hint_left`/`hint_right` in `ArcFTCHyp`)

* `fdBoundary_integrable_left_of_I` — integrability on `[0, 2/5 - δ]`
* `fdBoundary_integrable_right_of_I` — integrability on `[2/5 + δ, 1]`

### FTC

* `seg1_ftc_I` — FTC on seg1 (slitPlane)
* `seg5_ftc_I` — FTC on seg5 (slitPlane)

### Transfer and assembly

* `transfer_integrability` — from `fdBoundaryFun` to `γ.toPath.extend`
* `transfer_integral` — integral equality transfer
* `arcFTCHyp_atI` — complete `ArcFTCHyp` at `i`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ## Part 1: Transfer infrastructure -/

/-- On `(0, 1)`, `γ.toPath.extend` agrees with `fdBoundaryFun H` in a neighborhood. -/
private lemma gamma_eventuallyEq {H : ℝ}
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    γ.toPath.extend =ᶠ[𝓝 t] fdBoundaryFun H :=
  eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs =>
    hγ s (Ioo_subset_Icc_self hs)

/-- Transfer integrability from `fdBoundaryFun`-based to `γ`-based integrand. -/
theorem transfer_integrability {H : ℝ} (z : ℂ) {a b : ℝ}
    (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (hint : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z)⁻¹ * deriv (fdBoundaryFun H) t) volume a b) :
    IntervalIntegrable
      (fun t => (γ.toPath.extend t - z)⁻¹ * deriv γ.toPath.extend t) volume a b := by
  apply hint.congr_ae
  rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton b)] with t ht_ne_b ht_mem
  rw [uIoc_of_le hab] at ht_mem
  have htb : t < b := ht_mem.2.lt_of_ne fun h => ht_ne_b (mem_singleton_iff.mpr h)
  have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht_mem.1], by linarith⟩
  change (fdBoundaryFun H t - z)⁻¹ * deriv (fdBoundaryFun H) t =
    (γ.toPath.extend t - z)⁻¹ * deriv γ.toPath.extend t
  rw [← hγ t (Ioo_subset_Icc_self ht01), ← (gamma_eventuallyEq hγ ht01).deriv_eq]

/-- Transfer integral equality from `fdBoundaryFun`-based to `γ`-based integrand. -/
theorem transfer_integral {H : ℝ} (z : ℂ) {a b : ℝ}
    (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t) :
    ∫ t in a..b, (γ.toPath.extend t - z)⁻¹ * deriv γ.toPath.extend t =
    ∫ t in a..b, (fdBoundaryFun H t - z)⁻¹ * deriv (fdBoundaryFun H) t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton b)] with t ht_ne_b ht_mem
  rw [uIoc_of_le hab] at ht_mem
  have htb : t < b := ht_mem.2.lt_of_ne fun h => ht_ne_b (mem_singleton_iff.mpr h)
  have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht_mem.1], by linarith⟩
  rw [← hγ t (Ioo_subset_Icc_self ht01), ← (gamma_eventuallyEq hγ ht01).deriv_eq]

/-! ## Part 2: Smooth reference functions -/

/-! ### Segment 1: Right vertical, `Re = 1/2` -/

private def ref_seg1_I (H : ℝ) (t : ℝ) : ℂ :=
  1/2 + (↑H - 1 - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I

private lemma ref_seg1_I_contDiff (H : ℝ) : ContDiff ℝ ⊤ (ref_seg1_I H) := by
  unfold ref_seg1_I
  exact contDiff_const.add
    ((contDiff_const.sub
      ((contDiff_const.mul ofRealCLM.contDiff).mul contDiff_const)).mul
      contDiff_const)

private lemma ref_seg1_I_slitPlane (H : ℝ) (t : ℝ) :
    ref_seg1_I H t ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  simp only [ref_seg1_I, add_re, ofReal_re, mul_re, sub_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, div_ofNat]
  norm_num

private lemma fdBoundary_sub_I_eq_ref_seg1 (H : ℝ) (t : ℝ) (ht : t ≤ 1/5) :
    fdBoundaryFun H t - I = ref_seg1_I H t := by
  simp only [fdBoundaryFun, ht, ite_true, ref_seg1_I]
  ring

private lemma fdBoundary_sub_I_eventuallyEq_ref_seg1 (H : ℝ) {t : ℝ} (ht : t < 1/5) :
    (fun s => fdBoundaryFun H s - I) =ᶠ[𝓝 t] ref_seg1_I H :=
  eventually_of_mem (Iio_mem_nhds ht) fun s (hs : s < 1/5) =>
    fdBoundary_sub_I_eq_ref_seg1 H s hs.le

/-! ### Segment 4: Left vertical, `Re = -1/2` -/

private def ref_seg4_I (H : ℝ) (t : ℝ) : ℂ :=
  -1/2 + (↑(Real.sqrt 3) / 2 - 1 + (5 * ↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I

private lemma ref_seg4_I_contDiff (H : ℝ) : ContDiff ℝ ⊤ (ref_seg4_I H) := by
  unfold ref_seg4_I
  exact contDiff_const.add
    ((contDiff_const.add
      (((contDiff_const.mul ofRealCLM.contDiff).sub contDiff_const).mul
        contDiff_const)).mul contDiff_const)

private lemma ref_seg4_I_ne_zero (H : ℝ) (t : ℝ) : ref_seg4_I H t ≠ 0 := by
  intro h
  have hre : (ref_seg4_I H t).re = -1/2 := by
    unfold ref_seg4_I
    simp only [add_re, mul_re, sub_re, ofReal_re, ofReal_im, I_re, I_im, neg_re, one_re, div_ofNat]
    norm_num
  rw [h] at hre
  simp only [zero_re] at hre
  linarith

private lemma fdBoundary_sub_I_eventuallyEq_ref_seg4 (H : ℝ) {t : ℝ}
    (ht3 : 3/5 < t) (ht4 : t < 4/5) :
    (fun s => fdBoundaryFun H s - I) =ᶠ[𝓝 t] ref_seg4_I H :=
  eventually_of_mem
    (inter_mem (Ioi_mem_nhds ht3) (Iio_mem_nhds ht4))
    fun s ⟨hs3, hs4⟩ => by
      rw [mem_Ioi] at hs3
      rw [mem_Iio] at hs4
      simp only [fdBoundaryFun, show ¬s ≤ 1/5 from by linarith,
        show ¬s ≤ 2/5 from by linarith, show ¬s ≤ 3/5 from by linarith,
        show s ≤ 4/5 from by linarith, ite_true, ite_false, ref_seg4_I]
      ring

/-! ### Segment 5: Horizontal, `Im = H` -/

private def ref_seg5_I (H : ℝ) (t : ℝ) : ℂ := (5 * ↑t - 9/2) + (↑H - 1) * I

private lemma ref_seg5_I_contDiff (H : ℝ) : ContDiff ℝ ⊤ (ref_seg5_I H) := by
  unfold ref_seg5_I
  exact ((contDiff_const.mul ofRealCLM.contDiff).sub contDiff_const).add contDiff_const

private lemma ref_seg5_I_slitPlane (H : ℝ) (hH : 1 < H) (t : ℝ) :
    ref_seg5_I H t ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  -- Goal: (ref_seg5_I H t).im ≠ 0
  unfold ref_seg5_I
  simp only [add_im, mul_im, sub_im, ofReal_re, ofReal_im, I_re, I_im]
  norm_num
  linarith

private lemma ref_seg5_I_ne_zero (H : ℝ) (hH : 1 < H) (t : ℝ) : ref_seg5_I H t ≠ 0 :=
  slitPlane_ne_zero (ref_seg5_I_slitPlane H hH t)

private lemma fdBoundary_sub_I_eq_ref_seg5 (H : ℝ) (t : ℝ) (ht : 4/5 < t) :
    fdBoundaryFun H t - I = ref_seg5_I H t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    show ¬t ≤ 4/5 from by linarith, ite_false, ref_seg5_I]
  ring

private lemma fdBoundary_sub_I_eventuallyEq_ref_seg5 (H : ℝ) {t : ℝ} (ht : 4/5 < t) :
    (fun s => fdBoundaryFun H s - I) =ᶠ[𝓝 t] ref_seg5_I H :=
  eventually_of_mem (Ioi_mem_nhds ht) fun s (hs : 4/5 < s) =>
    fdBoundary_sub_I_eq_ref_seg5 H s hs

/-! ## Part 3: Arc segment infrastructure -/

private lemma arc_exp_continuous :
    Continuous (fun t => exp (↑(fdArcAngle t) * I)) :=
  continuous_exp.comp
    ((continuous_ofReal.comp fdArcAngle_continuous).mul continuous_const)

private lemma arc_sub_I_ne_zero_seg2 {t : ℝ} (ht1 : 1/5 ≤ t) (ht2 : t < 2/5) :
    exp (↑(fdArcAngle t) * I) - I ≠ 0 := by
  intro h
  have hre := congr_arg re h
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin] at hre
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, sub_re, zero_re] at hre
  linarith [Real.cos_pos_of_mem_Ioo
    ⟨by unfold fdArcAngle; nlinarith [Real.pi_pos],
     show fdArcAngle t < Real.pi / 2 from by unfold fdArcAngle; nlinarith [Real.pi_pos]⟩]

private lemma arc_sub_I_ne_zero_seg3 (H : ℝ) {t : ℝ}
    (ht1 : 2/5 < t) (ht2 : t ≤ 3/5) :
    exp (↑(fdArcAngle t) * I) - I ≠ 0 := by
  rw [← fdBoundaryFun_arc_eq_exp H t (by linarith) ht2]
  exact fdBoundaryFun_sub_i_ne_zero_seg3 H t ht1 ht2

private def arcIntegrand_I (t : ℝ) : ℂ :=
  (exp (↑(fdArcAngle t) * I) - I)⁻¹ *
    (↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I))

/-- `fdBoundaryFun H` agrees with `exp(i·fdArcAngle)` near each `t ∈ (1/5, 3/5)`. -/
private lemma fdBoundary_eventuallyEq_arc (H : ℝ) {t : ℝ}
    (ht1 : 1/5 < t) (ht2 : t < 3/5) :
    fdBoundaryFun H =ᶠ[𝓝 t] fun s => exp (↑(fdArcAngle s) * I) :=
  eventually_of_mem
    (inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht2))
    fun s ⟨hs1, hs2⟩ => by
      rw [mem_Ioi] at hs1
      rw [mem_Iio] at hs2
      exact fdBoundaryFun_arc_eq_exp H s hs1 hs2.le

/-! ## Part 4: Per-segment integrability and FTC -/

/-- Pointwise equality: `(f(t) - z)⁻¹ * f'(t) = deriv(f - z)(t) / (f(t) - z)`. -/
private lemma integrand_form_eq (f : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    (f t - z)⁻¹ * deriv f t = deriv (fun s => f s - z) t / (f t - z) := by
  rw [show (fun s => f s - z) = (fun s => f s + (-z)) from by ext; ring,
    deriv_add_const, div_eq_mul_inv, mul_comm]

/-! ### Segment 1: FTC via `ftc_log_pieceFM` -/

/-- Integrability + FTC on seg1 `[0, a]` for `a ≤ 1/5`, shifted by `I`. -/
theorem seg1_ftc_I (H : ℝ) {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/5) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - I) t /
      (fdBoundaryFun H t - I)) volume 0 a ∧
    ∫ t in (0 : ℝ)..a, deriv (fun s => fdBoundaryFun H s - I) t /
      (fdBoundaryFun H t - I) =
      Complex.log (fdBoundaryFun H a - I) - Complex.log (fdBoundaryFun H 0 - I) :=
  LogDerivFTC.ftc_log_pieceFM ha
    (ref_seg1_I_contDiff H).continuous.continuousOn
    (fun t _ => ((ref_seg1_I_contDiff H).differentiable (by norm_num)).differentiableAt)
    ((ref_seg1_I_contDiff H).continuous_deriv le_top).continuousOn
    (fun t _ => ref_seg1_I_slitPlane H t)
    (fun t ht => ⟨fdBoundary_sub_I_eq_ref_seg1 H t (by linarith [ht.2]),
      (fdBoundary_sub_I_eventuallyEq_ref_seg1 H (by linarith [ht.2])).deriv_eq⟩)
    (fdBoundary_sub_I_eq_ref_seg1 H 0 (by norm_num))
    (fdBoundary_sub_I_eq_ref_seg1 H a ha')

/-- Integrability + FTC on seg5 `[b, 1]` for `4/5 < b`, shifted by `I`. -/
theorem seg5_ftc_I (H : ℝ) (hH : 1 < H) {b : ℝ} (hb : 4/5 < b) (hb1 : b ≤ 1) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - I) t /
      (fdBoundaryFun H t - I)) volume b 1 ∧
    ∫ t in b..1, deriv (fun s => fdBoundaryFun H s - I) t /
      (fdBoundaryFun H t - I) =
      Complex.log (fdBoundaryFun H 1 - I) - Complex.log (fdBoundaryFun H b - I) :=
  LogDerivFTC.ftc_log_pieceFM hb1
    (ref_seg5_I_contDiff H).continuous.continuousOn
    (fun t _ => ((ref_seg5_I_contDiff H).differentiable (by norm_num)).differentiableAt)
    ((ref_seg5_I_contDiff H).continuous_deriv le_top).continuousOn
    (fun t _ => ref_seg5_I_slitPlane H hH t)
    (fun t ht => ⟨fdBoundary_sub_I_eq_ref_seg5 H t (by linarith [ht.1]),
      (fdBoundary_sub_I_eventuallyEq_ref_seg5 H (by linarith [ht.1])).deriv_eq⟩)
    (fdBoundary_sub_I_eq_ref_seg5 H b hb)
    (fdBoundary_sub_I_eq_ref_seg5 H 1 (by norm_num))

/-- Integrability in the standard form on seg1. -/
theorem fdBoundary_seg1_intervalIntegrable_I (H : ℝ) {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1/5) :
    IntervalIntegrable
      (fun t => (fdBoundaryFun H t - I)⁻¹ * deriv (fdBoundaryFun H) t) volume 0 a :=
  (seg1_ftc_I H ha ha').1.congr fun t _ => (integrand_form_eq (fdBoundaryFun H) I t).symm

/-! ### Segment 2: Arc integrability via continuity -/

/-- Integrability on seg2 `[1/5, a]` for `a < 2/5`, shifted by `I`. -/
theorem seg2_intervalIntegrable_I (H : ℝ) {a : ℝ} (ha : 1/5 ≤ a) (ha' : a < 2/5) :
    IntervalIntegrable
      (fun t => (fdBoundaryFun H t - I)⁻¹ * deriv (fdBoundaryFun H) t) volume (1/5) a := by
  have hint_arc : IntervalIntegrable arcIntegrand_I volume (1/5) a := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ha]
    unfold arcIntegrand_I
    exact (((arc_exp_continuous.sub continuous_const).continuousOn.inv₀
      (fun t ht => arc_sub_I_ne_zero_seg2 ht.1 (by linarith [ht.2]))).mul
      (continuous_const.mul arc_exp_continuous).continuousOn)
  apply hint_arc.congr_ae
  rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton a)] with t ht_ne ht_mem
  rw [uIoc_of_le ha] at ht_mem
  have ht1 : 1/5 < t := ht_mem.1
  have hta : t < a := ht_mem.2.lt_of_ne fun h => ht_ne (mem_singleton_iff.mpr h)
  change arcIntegrand_I t = (fdBoundaryFun H t - I)⁻¹ * deriv (fdBoundaryFun H) t
  unfold arcIntegrand_I
  rw [fdBoundaryFun_arc_eq_exp H t ht1 (by linarith)]
  congr 1
  rw [(fdBoundary_eventuallyEq_arc H ht1 (by linarith)).deriv_eq, fdBoundary_arc_deriv_eq]

/-! ### Segment 3: Arc integrability via continuity -/

/-- Integrability on seg3 `[a, 3/5]` for `2/5 < a`, shifted by `I`. -/
theorem seg3_intervalIntegrable_I (H : ℝ) {a : ℝ} (ha : 2/5 < a) (ha' : a ≤ 3/5) :
    IntervalIntegrable
      (fun t => (fdBoundaryFun H t - I)⁻¹ * deriv (fdBoundaryFun H) t) volume a (3/5) := by
  have hint_arc : IntervalIntegrable arcIntegrand_I volume a (3/5) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ha']
    unfold arcIntegrand_I
    exact (((arc_exp_continuous.sub continuous_const).continuousOn.inv₀
      (fun t ht => arc_sub_I_ne_zero_seg3 H (by linarith [ht.1]) ht.2)).mul
      (continuous_const.mul arc_exp_continuous).continuousOn)
  apply hint_arc.congr_ae
  rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (3/5 : ℝ))] with t ht_ne ht_mem
  rw [uIoc_of_le ha'] at ht_mem
  have ht1 : 2/5 < t := by linarith [ht_mem.1]
  have ht2 : t < 3/5 := ht_mem.2.lt_of_ne fun h => ht_ne (mem_singleton_iff.mpr h)
  change arcIntegrand_I t = (fdBoundaryFun H t - I)⁻¹ * deriv (fdBoundaryFun H) t
  unfold arcIntegrand_I
  rw [fdBoundaryFun_arc_eq_exp H t (by linarith) (by linarith)]
  congr 1
  rw [(fdBoundary_eventuallyEq_arc H (by linarith) ht2).deriv_eq, fdBoundary_arc_deriv_eq]

/-! ### Segment 4: Full integrability via continuous reference -/

/-- Integrability on seg4 `[3/5, 4/5]`, shifted by `I`.
Uses the globally nonvanishing reference `ref_seg4_I` (Re = -1/2 ≠ 0). -/
theorem seg4_full_intervalIntegrable_I (H : ℝ) :
    IntervalIntegrable
      (fun t => (fdBoundaryFun H t - I)⁻¹ * deriv (fdBoundaryFun H) t) volume (3/5) (4/5) := by
  have hint_ref : IntervalIntegrable
      (fun t => (ref_seg4_I H t)⁻¹ * deriv (ref_seg4_I H) t) volume (3/5) (4/5) :=
    ((((ref_seg4_I_contDiff H).continuous).inv₀ (ref_seg4_I_ne_zero H)).mul
      ((ref_seg4_I_contDiff H).continuous_deriv le_top)).continuousOn.intervalIntegrable
  apply hint_ref.congr_ae
  rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (4/5 : ℝ))] with t ht_ne ht_mem
  rw [uIoc_of_le (by norm_num : (3:ℝ)/5 ≤ 4/5)] at ht_mem
  have ht3 : 3/5 < t := ht_mem.1
  have ht4 : t < 4/5 := ht_mem.2.lt_of_ne fun h => ht_ne (mem_singleton_iff.mpr h)
  change (ref_seg4_I H t)⁻¹ * deriv (ref_seg4_I H) t =
    (fdBoundaryFun H t - I)⁻¹ * deriv (fdBoundaryFun H) t
  have h_val : fdBoundaryFun H t - I = ref_seg4_I H t := by
    simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
      show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
      show t ≤ 4/5 from by linarith, ite_true, ite_false, ref_seg4_I]
    ring
  rw [h_val, ← (fdBoundary_sub_I_eventuallyEq_ref_seg4 H ht3 ht4).deriv_eq]
  congr 1
  change deriv (fun s => fdBoundaryFun H s - I) t = deriv (fdBoundaryFun H) t
  simp only [deriv_sub_const]

/-! ### Segment 5: Full integrability via continuous reference -/

/-- Integrability on seg5 `[4/5, 1]`, shifted by `I`.
Uses the globally nonvanishing reference `ref_seg5_I` (Im = H-1 > 0). -/
theorem seg5_full_intervalIntegrable_I (H : ℝ) (hH : 1 < H) :
    IntervalIntegrable
      (fun t => (fdBoundaryFun H t - I)⁻¹ * deriv (fdBoundaryFun H) t) volume (4/5) 1 := by
  have hint_ref : IntervalIntegrable
      (fun t => (ref_seg5_I H t)⁻¹ * deriv (ref_seg5_I H) t) volume (4/5) 1 :=
    ((((ref_seg5_I_contDiff H).continuous).inv₀ (ref_seg5_I_ne_zero H hH)).mul
      ((ref_seg5_I_contDiff H).continuous_deriv le_top)).continuousOn.intervalIntegrable
  apply hint_ref.congr_ae
  rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ))] with t ht_ne ht_mem
  rw [uIoc_of_le (by norm_num : (4:ℝ)/5 ≤ 1)] at ht_mem
  have ht4 : 4/5 < t := ht_mem.1
  have ht1 : t < 1 := ht_mem.2.lt_of_ne fun h => ht_ne (mem_singleton_iff.mpr h)
  change (ref_seg5_I H t)⁻¹ * deriv (ref_seg5_I H) t =
    (fdBoundaryFun H t - I)⁻¹ * deriv (fdBoundaryFun H) t
  have h_val : fdBoundaryFun H t - I = ref_seg5_I H t :=
    fdBoundary_sub_I_eq_ref_seg5 H t ht4
  rw [h_val, ← (fdBoundary_sub_I_eventuallyEq_ref_seg5 H ht4).deriv_eq]
  congr 1
  simp [deriv_sub_const]

/-! ## Part 5: Combined integrability across segments -/

/-- Integrability on `[0, 2/5 - δ]` for the crossing at `I`.
Combines seg1 `[0, 1/5]` and seg2 `[1/5, 2/5 - δ]`. -/
theorem fdBoundary_integrable_left_of_I (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) :
    IntervalIntegrable
      (fun t => (fdBoundaryFun H t - I)⁻¹ * deriv (fdBoundaryFun H) t)
      volume 0 (2/5 - δ) :=
  (fdBoundary_seg1_intervalIntegrable_I (a := 1/5) H (by norm_num) le_rfl).trans
    (seg2_intervalIntegrable_I H (by linarith) (by linarith))

/-- Integrability on `[2/5 + δ, 1]` for the crossing at `I`.
Combines seg3 `[2/5 + δ, 3/5]`, seg4 `[3/5, 4/5]`, and seg5 `[4/5, 1]`. -/
theorem fdBoundary_integrable_right_of_I (H : ℝ) (hH : 1 < H)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) :
    IntervalIntegrable
      (fun t => (fdBoundaryFun H t - I)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (2/5 + δ) 1 :=
  ((seg3_intervalIntegrable_I H (by linarith) (by linarith)).trans
    (seg4_full_intervalIntegrable_I H)).trans
    (seg5_full_intervalIntegrable_I H hH)

/-! ## Part 6: Gamma-based integrability (for ArcFTCHyp)

These provide the `hint_left` and `hint_right` fields of `ArcFTCHyp` at `i`. -/

/-- Integrability of the `γ`-based integrand on `[0, 2/5 - δ]`. -/
theorem gamma_integrable_left_of_I {H : ℝ} (_hH : 1 < H)
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) :
    IntervalIntegrable
      (fun t => (γ.toPath.extend t - I)⁻¹ * deriv γ.toPath.extend t)
      volume 0 (2/5 - δ) :=
  transfer_integrability I (by linarith) (le_refl 0) (by linarith) hγ
    (fdBoundary_integrable_left_of_I H hδ hδ')

/-- Integrability of the `γ`-based integrand on `[2/5 + δ, 1]`. -/
theorem gamma_integrable_right_of_I {H : ℝ} (hH : 1 < H)
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) :
    IntervalIntegrable
      (fun t => (γ.toPath.extend t - I)⁻¹ * deriv γ.toPath.extend t)
      volume (2/5 + δ) 1 :=
  transfer_integrability I (by linarith) (by linarith) (le_refl 1) hγ
    (fdBoundary_integrable_right_of_I H hH hδ hδ')

end
