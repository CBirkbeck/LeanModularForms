/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.CrossingAtI
import LeanModularForms.ForMathlib.SegmentAnalysis

/-!
# ArcFTCHyp at i — Full FTC Telescope + Limit

Constructs a concrete `ArcFTCHyp` instance for the crossing at `i` (`t₀ = 2/5`)
on the FD boundary, with `δ = arcsinDelta`, `threshold = min(1/3, H-1)`,
and limit target `L = -(π·I)`.

## Strategy

The E function is defined as the sum of the two far-segment integrals (making
`h_ftc` definitional). Then `h_limit` is proved by:

1. FTC telescoping on the 5 segments shows the sum equals
   `log(γ(2/5-δ) - I) - log(γ(2/5+δ) - I) - 2πI`
2. `fdBoundaryFun_log_diff_core_tendsto` from ArcFTCLimit gives the log difference → πI
3. Therefore E(ε) → πI - 2πI = -πI ✓

The `-2πI` branch correction arises from segments 3 and 4, where `γ(t) - I` has
negative real part and crosses through the slit.

## Main results

* `arcFTCHyp_atI` — the full `ArcFTCHyp` at `i`

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ## Part 1: Arc reference function -/

private def arcRef_I (t : ℝ) : ℂ := exp (↑(fdArcAngle t) * I) - I

private lemma fdArcAngle_contDiff : ContDiff ℝ ⊤ fdArcAngle := by
  unfold fdArcAngle; fun_prop

private lemma arcRef_I_contDiff : ContDiff ℝ ⊤ arcRef_I := by
  unfold arcRef_I
  exact (Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp fdArcAngle_contDiff).mul
      contDiff_const)).sub contDiff_const

private lemma arcRef_I_eq (H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t - I = arcRef_I t := by
  unfold arcRef_I; rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2]

private lemma arcRef_I_eq_at_15 (H : ℝ) :
    fdBoundaryFun H (1/5) - I = arcRef_I (1/5) := by
  unfold arcRef_I; rw [fdArcAngle_at_one_fifth]
  rw [fdBoundaryFun_at_one_fifth]
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring

private lemma arcRef_I_eventuallyEq (H : ℝ) {t : ℝ}
    (ht1 : 1/5 < t) (ht2 : t < 3/5) :
    (fun s => fdBoundaryFun H s - I) =ᶠ[𝓝 t] arcRef_I :=
  Filter.eventually_of_mem
    (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht2))
    fun s ⟨hs1, hs2⟩ => by
      rw [mem_Ioi] at hs1; rw [mem_Iio] at hs2
      exact arcRef_I_eq H hs1 (le_of_lt hs2)

private lemma arcRef_I_slitPlane_seg2 {t : ℝ} (ht1 : 1/5 ≤ t) (ht2 : t < 2/5) :
    arcRef_I t ∈ Complex.slitPlane := by
  unfold arcRef_I
  rw [Complex.mem_slitPlane_iff]; left
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [add_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, add_zero, mul_one]
  exact Real.cos_pos_of_mem_Ioo ⟨by unfold fdArcAngle; nlinarith [Real.pi_pos],
    by unfold fdArcAngle; nlinarith [Real.pi_pos]⟩

private lemma arcRef_I_neg_slitPlane_seg3 {t : ℝ} (ht2 : 2/5 < t) (ht3 : t ≤ 3/5) :
    -(arcRef_I t) ∈ Complex.slitPlane := by
  unfold arcRef_I
  rw [Complex.mem_slitPlane_iff]; left
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [neg_sub, sub_re, I_re, add_re, ofReal_re, mul_re, ofReal_im, I_im,
    mul_zero, sub_zero, add_zero, mul_one]
  have hgt : Real.pi / 2 < fdArcAngle t := by
    unfold fdArcAngle; nlinarith [Real.pi_pos]
  have hlt : fdArcAngle t < Real.pi + Real.pi / 2 := by
    unfold fdArcAngle; nlinarith [Real.pi_pos]
  linarith [Real.cos_neg_of_pi_div_two_lt_of_lt hgt hlt]

/-! ## Part 2: Per-segment FTC -/

private lemma integrand_form_eq (f : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    (f t - z)⁻¹ * deriv f t =
    deriv (fun s => f s - z) t / (f t - z) := by
  rw [show (fun s => f s - z) = (fun s => f s + (-z)) from by ext; ring,
    deriv_add_const, div_eq_mul_inv, mul_comm]

/-- FTC on seg2 `[1/5, 2/5-δ]`. -/
private theorem seg2_ftc_I (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - I) t /
      (fdBoundaryFun H t - I)) volume (1/5) (2/5 - δ) ∧
    ∫ t in (1/5 : ℝ)..(2/5 - δ), deriv (fun s => fdBoundaryFun H s - I) t /
      (fdBoundaryFun H t - I) =
      Complex.log (fdBoundaryFun H (2/5 - δ) - I) -
      Complex.log (fdBoundaryFun H (1/5) - I) :=
  LogDerivFTC.ftc_log_piece (by linarith)
    arcRef_I_contDiff.continuous.continuousOn
    (fun t _ => arcRef_I_contDiff.differentiable (by norm_num) |>.differentiableAt)
    (arcRef_I_contDiff.continuous_deriv le_top).continuousOn
    (fun t ht => arcRef_I_slitPlane_seg2 (by linarith [ht.1]) (by linarith [ht.2, hδ]))
    (fun t ht => ⟨arcRef_I_eq H (by linarith [ht.1]) (by linarith [ht.2]),
      (arcRef_I_eventuallyEq H (by linarith [ht.1]) (by linarith [ht.2, hδ])).deriv_eq⟩)
    (arcRef_I_eq_at_15 H)
    (arcRef_I_eq H (by linarith) (by linarith))

/-- FTC on seg3 `[2/5+δ, 3/5]` using negated reference. -/
private theorem seg3_ftc_neg_I (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - I) t /
      (fdBoundaryFun H t - I)) volume (2/5 + δ) (3/5) ∧
    ∫ t in (2/5 + δ)..(3/5 : ℝ), deriv (fun s => fdBoundaryFun H s - I) t /
      (fdBoundaryFun H t - I) =
      Complex.log (-(fdBoundaryFun H (3/5) - I)) -
      Complex.log (-(fdBoundaryFun H (2/5 + δ) - I)) := by
  have hab : (2/5 + δ) ≤ (3/5 : ℝ) := by linarith
  have h_piece := @LogDerivFTC.ftc_log_neg_on_segment arcRef_I (2/5 + δ) (3/5) hab
    arcRef_I_contDiff.continuous.continuousOn
    (fun t _ => arcRef_I_contDiff.differentiable (by norm_num) |>.differentiableAt)
    (arcRef_I_contDiff.continuous_deriv le_top).continuousOn
    (fun t ht => arcRef_I_neg_slitPlane_seg3 (by linarith [ht.1]) ht.2)
  have h_ae : ∀ᵐ t ∂volume, t ∈ Ι (2/5 + δ) (3/5 : ℝ) →
      deriv (fun s => fdBoundaryFun H s - I) t / (fdBoundaryFun H t - I) =
      deriv arcRef_I t / arcRef_I t := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (3/5 : ℝ))] with t ht_ne ht_mem
    rw [uIoc_of_le (by linarith : (2/5 + δ) ≤ 3/5)] at ht_mem
    have ht_lt : t < 3/5 := lt_of_le_of_ne ht_mem.2
      (fun h => ht_ne (mem_singleton_iff.mpr h))
    have ht_gt : 1/5 < t := by linarith [ht_mem.1]
    rw [arcRef_I_eq H ht_gt (le_of_lt ht_lt),
      (arcRef_I_eventuallyEq H ht_gt ht_lt).deriv_eq]
  exact ⟨h_piece.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae.mono fun t ht hm => (ht hm).symm)),
    by rw [intervalIntegral.integral_congr_ae h_ae, h_piece.2,
      arcRef_I_eq H (by linarith) le_rfl,
      arcRef_I_eq H (by linarith) (by linarith)]⟩

/-! ### Seg4: left vertical -/

private def seg4Ref_I (H : ℝ) (t : ℝ) : ℂ := (-1/2 : ℂ) +
  (↑(Real.sqrt 3 / 2 - 1 + (5 * t - 3) * (H - Real.sqrt 3 / 2))) * I

private lemma seg4Ref_I_contDiff (H : ℝ) : ContDiff ℝ ⊤ (seg4Ref_I H) := by
  unfold seg4Ref_I
  apply ContDiff.add contDiff_const
  exact (Complex.ofRealCLM.contDiff.comp (by fun_prop :
    ContDiff ℝ ⊤ fun x : ℝ => Real.sqrt 3 / 2 - 1 +
      (5 * x - 3) * (H - Real.sqrt 3 / 2))).mul contDiff_const

private lemma seg4Ref_I_neg_slitPlane (H : ℝ) (t : ℝ) :
    -(seg4Ref_I H t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  simp only [seg4Ref_I, neg_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, div_ofNat, neg_add_rev]; norm_num

private lemma seg4Ref_I_eq_35 (H : ℝ) :
    fdBoundaryFun H (3/5) - I = seg4Ref_I H (3/5) := by
  rw [fdBoundaryFun_at_three_fifths]
  simp only [seg4Ref_I, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  push_cast; ring

private lemma seg4Ref_I_eq_45 (H : ℝ) :
    fdBoundaryFun H (4/5) - I = seg4Ref_I H (4/5) := by
  rw [fdBoundaryFun_at_four_fifths]
  simp only [seg4Ref_I]; push_cast; ring

private lemma seg4Ref_I_eq (H : ℝ) {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    fdBoundaryFun H t - I = seg4Ref_I H t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    ht4, ite_true, ite_false, seg4Ref_I]
  push_cast; ring

private lemma seg4Ref_I_eventuallyEq (H : ℝ) {t : ℝ}
    (ht3 : 3/5 < t) (ht4 : t < 4/5) :
    (fun s => fdBoundaryFun H s - I) =ᶠ[𝓝 t] seg4Ref_I H :=
  Filter.eventually_of_mem
    (Filter.inter_mem (Ioi_mem_nhds ht3) (Iio_mem_nhds ht4))
    fun s ⟨hs3, hs4⟩ =>
      seg4Ref_I_eq H (by rwa [mem_Ioi] at hs3) (by rw [mem_Iio] at hs4; linarith)

/-- FTC on seg4 `[3/5, 4/5]` using negated reference. -/
private theorem seg4_ftc_neg_I (H : ℝ) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - I) t /
      (fdBoundaryFun H t - I)) volume (3/5) (4/5) ∧
    ∫ t in (3/5 : ℝ)..(4/5), deriv (fun s => fdBoundaryFun H s - I) t /
      (fdBoundaryFun H t - I) =
      Complex.log (-(fdBoundaryFun H (4/5) - I)) -
      Complex.log (-(fdBoundaryFun H (3/5) - I)) := by
  have h_piece := LogDerivFTC.ftc_log_neg_on_segment (by norm_num : (3/5 : ℝ) ≤ 4/5)
    (seg4Ref_I_contDiff H).continuous.continuousOn
    (fun t _ => (seg4Ref_I_contDiff H).differentiable (by norm_num) |>.differentiableAt)
    ((seg4Ref_I_contDiff H).continuous_deriv le_top).continuousOn
    (fun t _ => seg4Ref_I_neg_slitPlane H t)
  have h_ae : ∀ᵐ t ∂volume, t ∈ Ι (3/5 : ℝ) (4/5) →
      deriv (fun s => fdBoundaryFun H s - I) t / (fdBoundaryFun H t - I) =
      deriv (seg4Ref_I H) t / seg4Ref_I H t := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (4/5 : ℝ))] with t ht_ne ht_mem
    rw [uIoc_of_le (by norm_num : (3/5 : ℝ) ≤ 4/5)] at ht_mem
    have ht_lt : t < 4/5 := lt_of_le_of_ne ht_mem.2
      (fun h => ht_ne (mem_singleton_iff.mpr h))
    rw [seg4Ref_I_eq H (by linarith [ht_mem.1]) (le_of_lt ht_lt),
      (seg4Ref_I_eventuallyEq H (by linarith [ht_mem.1]) ht_lt).deriv_eq]
  exact ⟨h_piece.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae.mono fun t ht hm => (ht hm).symm)),
    by rw [intervalIntegral.integral_congr_ae h_ae, h_piece.2,
      seg4Ref_I_eq_35 H, seg4Ref_I_eq_45 H]⟩

/-! ### Seg5: horizontal -/

private def seg5Ref_I (H : ℝ) (t : ℝ) : ℂ := (5 * ↑t - 9/2) + (↑H - 1) * I

private lemma seg5Ref_I_contDiff (H : ℝ) : ContDiff ℝ ⊤ (seg5Ref_I H) := by
  unfold seg5Ref_I
  exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).add contDiff_const

private lemma seg5Ref_I_slitPlane (H : ℝ) (hH : 1 < H) (t : ℝ) :
    seg5Ref_I H t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  show (seg5Ref_I H t).im ≠ 0
  have : (seg5Ref_I H t).im = H - 1 := by
    unfold seg5Ref_I
    simp only [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      zero_add, add_zero]; norm_num
  rw [this]; linarith

private lemma seg5Ref_I_eq (H : ℝ) {t : ℝ} (ht : 4/5 < t) :
    fdBoundaryFun H t - I = seg5Ref_I H t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    show ¬t ≤ 4/5 from by linarith, ite_false, seg5Ref_I]; ring

private lemma seg5Ref_I_eventuallyEq (H : ℝ) {t : ℝ} (ht : 4/5 < t) :
    (fun s => fdBoundaryFun H s - I) =ᶠ[𝓝 t] seg5Ref_I H :=
  Filter.eventually_of_mem (Ioi_mem_nhds ht) fun _ hs => seg5Ref_I_eq H hs

private lemma seg5Ref_I_eq_45 (H : ℝ) :
    fdBoundaryFun H (4/5) - I = seg5Ref_I H (4/5) := by
  rw [fdBoundaryFun_at_four_fifths]; simp only [seg5Ref_I]; push_cast; ring

private lemma seg5Ref_I_eq_1 (H : ℝ) :
    fdBoundaryFun H 1 - I = seg5Ref_I H 1 := by
  rw [fdBoundaryFun_at_one]; simp only [seg5Ref_I, fdStart]; push_cast; ring

/-- FTC on seg5 `[4/5, 1]`. -/
private theorem seg5_ftc_full_I (H : ℝ) (hH : 1 < H) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - I) t /
      (fdBoundaryFun H t - I)) volume (4/5) 1 ∧
    ∫ t in (4/5 : ℝ)..1, deriv (fun s => fdBoundaryFun H s - I) t /
      (fdBoundaryFun H t - I) =
      Complex.log (fdBoundaryFun H 1 - I) -
      Complex.log (fdBoundaryFun H (4/5) - I) :=
  LogDerivFTC.ftc_log_piece (by norm_num)
    (seg5Ref_I_contDiff H).continuous.continuousOn
    (fun t _ => (seg5Ref_I_contDiff H).differentiable (by norm_num) |>.differentiableAt)
    ((seg5Ref_I_contDiff H).continuous_deriv le_top).continuousOn
    (fun t _ => seg5Ref_I_slitPlane H hH t)
    (fun t ht => ⟨seg5Ref_I_eq H (by linarith [ht.1]),
      (seg5Ref_I_eventuallyEq H (by linarith [ht.1])).deriv_eq⟩)
    (seg5Ref_I_eq_45 H)
    (seg5Ref_I_eq_1 H)

/-! ## Part 3: Branch correction lemmas -/

private lemma log_neg_eq_add_pi_I {z : ℂ} (_hz_ne : z ≠ 0) (hz_im : z.im < 0) :
    Complex.log (-z) = Complex.log z + ↑Real.pi * I := by
  show ↑(Real.log ‖-z‖) + ↑((-z).arg) * I =
    ↑(Real.log ‖z‖) + ↑z.arg * I + ↑Real.pi * I
  simp only [norm_neg]
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hz_im]
  push_cast; ring

private lemma log_neg_eq_sub_pi_I {z : ℂ} (_hz_ne : z ≠ 0) (hz_im : 0 < z.im) :
    Complex.log (-z) = Complex.log z - ↑Real.pi * I := by
  show ↑(Real.log ‖-z‖) + ↑((-z).arg) * I =
    ↑(Real.log ‖z‖) + ↑z.arg * I - ↑Real.pi * I
  simp only [norm_neg]
  rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz_im]
  push_cast; ring

/-! ## Part 4: Branch point imaginary parts -/

private lemma fdBoundary_sub_I_at_35_im_neg (H : ℝ) :
    (fdBoundaryFun H (3/5) - I).im < 0 := by
  rw [fdBoundaryFun_at_three_fifths]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
    sub_im, add_im, neg_im, ofReal_im, one_im, div_ofNat, mul_im,
    ofReal_re, I_re, I_im, mul_zero, mul_one, add_zero]
  nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
    sq_nonneg (Real.sqrt 3 - 2)]

private lemma fdBoundary_sub_I_at_45_im_pos (H : ℝ) (hH : 1 < H) :
    0 < (fdBoundaryFun H (4/5) - I).im := by
  rw [fdBoundaryFun_at_four_fifths]
  simp only [sub_im, add_im, neg_im, ofReal_im, one_im, div_ofNat, mul_im,
    ofReal_re, I_re, I_im, mul_zero, mul_one, add_zero]; linarith

private lemma fdBoundary_sub_I_at_2p_im_neg (H : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1/5) :
    (fdBoundaryFun H (2/5 + δ) - I).im < 0 := by
  rw [fdBoundaryFun_arc_eq_exp H _ (by linarith) (by linarith),
    exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [add_im, sub_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
    mul_zero, add_zero, mul_one, zero_add]
  have hgt : Real.pi / 2 < fdArcAngle (2/5 + δ) := by
    unfold fdArcAngle; nlinarith [Real.pi_pos]
  have hlt : fdArcAngle (2/5 + δ) < Real.pi := by
    unfold fdArcAngle; nlinarith [Real.pi_pos]
  have h1 : Real.sin (fdArcAngle (2/5 + δ)) =
      Real.sin (Real.pi - fdArcAngle (2/5 + δ)) := by rw [Real.sin_pi_sub]
  have h2 : Real.pi - fdArcAngle (2/5 + δ) < Real.pi / 2 := by linarith
  have h3 : Real.sin (Real.pi - fdArcAngle (2/5 + δ)) < Real.sin (Real.pi / 2) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) le_rfl h2
  rw [Real.sin_pi_div_two] at h3; linarith [h1]

/-! ## Part 5: Full FTC telescope -/

/-- Branch correction: the integral over `[2/5+delta, 4/5]` equals
`log(f(4/5)-I) - log(f(2/5+delta)-I) - 2*pi*I` after resolving the two log-of-neg
branch cuts. -/
private lemma right_integral_34_branch_corrected (H : ℝ) (hH : 1 < H) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1/5)
    (p3 : IntervalIntegrable _ _ (2/5 + δ) (3/5) ∧ _)
    (p4 : IntervalIntegrable _ _ (3/5) (4/5) ∧ _)
    (hright34 : ∫ t in (2/5 + δ)..(4/5 : ℝ),
        deriv (fun s => fdBoundaryFun H s - I) t / (fdBoundaryFun H t - I) =
        Complex.log (-(fdBoundaryFun H (4/5) - I)) -
        Complex.log (-(fdBoundaryFun H (2/5 + δ) - I))) :
    ∫ t in (2/5 + δ)..(4/5 : ℝ),
      deriv (fun s => fdBoundaryFun H s - I) t / (fdBoundaryFun H t - I) =
      Complex.log (fdBoundaryFun H (4/5) - I) -
      Complex.log (fdBoundaryFun H (2/5 + δ) - I) - 2 * ↑Real.pi * I := by
  have h_branch_2pδ : Complex.log (-(fdBoundaryFun H (2/5 + δ) - I)) =
      Complex.log (fdBoundaryFun H (2/5 + δ) - I) + ↑Real.pi * I :=
    log_neg_eq_add_pi_I (fdBoundaryFun_sub_i_ne_zero_seg3 H _ (by linarith) (by linarith))
      (fdBoundary_sub_I_at_2p_im_neg H hδ hδ')
  have h45_ne : fdBoundaryFun H (4/5) - I ≠ 0 := by
    intro h; have := fdBoundary_sub_I_at_45_im_pos H hH
    rw [h] at this; simp only [zero_im, lt_irrefl] at this
  have h_branch_45 : Complex.log (-(fdBoundaryFun H (4/5) - I)) =
      Complex.log (fdBoundaryFun H (4/5) - I) - ↑Real.pi * I :=
    log_neg_eq_sub_pi_I h45_ne (fdBoundary_sub_I_at_45_im_pos H hH)
  rw [hright34, h_branch_45, h_branch_2pδ]; ring

/-- Full FTC telescope for the crossing at `i`. -/
theorem fdBoundary_ftc_telescope_I (H : ℝ) (hH : 1 < H) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1/5) :
    (∫ t in (0 : ℝ)..(2/5 - δ),
        (fdBoundaryFun H t - I)⁻¹ * deriv (fdBoundaryFun H) t) +
    (∫ t in (2/5 + δ)..(1 : ℝ),
        (fdBoundaryFun H t - I)⁻¹ * deriv (fdBoundaryFun H) t) =
    Complex.log (fdBoundaryFun H (2/5 - δ) - I) -
    Complex.log (fdBoundaryFun H (2/5 + δ) - I) - 2 * ↑Real.pi * I := by
  have h_form : ∀ t, (fdBoundaryFun H t - I)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (fun s => fdBoundaryFun H s - I) t / (fdBoundaryFun H t - I) :=
    fun t => integrand_form_eq (fdBoundaryFun H) I t
  simp_rw [h_form]
  have p1 := seg1_ftc_I H (by norm_num) (le_refl (1/5 : ℝ))
  have p2 := seg2_ftc_I H hδ hδ'
  have p3 := seg3_ftc_neg_I H hδ hδ'
  have p4 := seg4_ftc_neg_I H
  have p5 := seg5_ftc_full_I H hH
  have hleft : ∫ t in (0 : ℝ)..(2/5 - δ),
      deriv (fun s => fdBoundaryFun H s - I) t / (fdBoundaryFun H t - I) =
      Complex.log (fdBoundaryFun H (2/5 - δ) - I) -
      Complex.log (fdBoundaryFun H 0 - I) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals p1.1 p2.1, p1.2, p2.2]; ring
  have hright34' := right_integral_34_branch_corrected H hH hδ hδ' p3 p4 (by
    rw [← intervalIntegral.integral_add_adjacent_intervals p3.1 p4.1, p3.2, p4.2]; ring)
  have hright : ∫ t in (2/5 + δ)..(1 : ℝ),
      deriv (fun s => fdBoundaryFun H s - I) t / (fdBoundaryFun H t - I) =
      Complex.log (fdBoundaryFun H 1 - I) -
      Complex.log (fdBoundaryFun H (2/5 + δ) - I) - 2 * ↑Real.pi * I := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (p3.1.trans p4.1) p5.1,
      hright34', p5.2]; ring
  rw [hleft, hright, fdBoundaryFun_closed H]; ring

/-! ## Part 6: E function and limit -/

private def E_atI (H : ℝ) (ε : ℝ) : ℂ :=
  Complex.log (fdBoundaryFun H (2/5 - arcsinDelta ε) - I) -
  Complex.log (fdBoundaryFun H (2/5 + arcsinDelta ε) - I) - 2 * ↑Real.pi * I

private lemma arcsinDelta_tendsto_nhdsWithin :
    Tendsto arcsinDelta (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have : arcsinDelta = fun ε => 12 / (5 * Real.pi) * Real.arcsin (ε / 2) := rfl
    rw [this]
    have hcont : ContinuousAt (fun ε : ℝ =>
        12 / (5 * Real.pi) * Real.arcsin (ε / 2)) 0 := by
      exact continuousAt_const.mul
        (Real.continuous_arcsin.continuousAt.comp (continuousAt_id.div_const 2))
    convert hcont.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp only [Real.arcsin_zero, mul_zero, zero_div]
  · rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0:ℝ) < 1 from by norm_num)] with ε _ hε
    exact mem_Ioi.mpr (arcsinDelta_pos (by rwa [mem_Ioi] at hε))

private theorem E_atI_tendsto (H : ℝ) :
    Tendsto (E_atI H) (𝓝[>] 0) (𝓝 (-(↑Real.pi * I))) := by
  unfold E_atI
  have hcore := fdBoundaryFun_log_diff_core_tendsto H
  have h1 : Tendsto (fun ε =>
      Complex.log (fdBoundaryFun H (2/5 - arcsinDelta ε) - I) -
      Complex.log (fdBoundaryFun H (2/5 + arcsinDelta ε) - I))
      (𝓝[>] 0) (𝓝 (↑Real.pi * I)) :=
    hcore.comp arcsinDelta_tendsto_nhdsWithin
  have h2 : Tendsto (fun ε =>
      Complex.log (fdBoundaryFun H (2/5 - arcsinDelta ε) - I) -
      Complex.log (fdBoundaryFun H (2/5 + arcsinDelta ε) - I) -
      2 * ↑Real.pi * I)
      (𝓝[>] 0) (𝓝 (↑Real.pi * I - 2 * ↑Real.pi * I)) :=
    h1.sub tendsto_const_nhds
  convert h2 using 1; ring

/-! ## Part 7: Assembly -/

/-- The complete `ArcFTCHyp` at `i` for the FD boundary. -/
def arcFTCHyp_atI {H : ℝ} (hH : 1 < H)
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t) :
    ArcFTCHyp γ I (2/5) arcsinDelta (min (1/3) (H - 1)) (-(↑Real.pi * I)) where
  E := E_atI H
  h_ftc := by
    intro ε hε hεt
    have hε_lt : ε < 1/3 := lt_of_lt_of_le hεt (min_le_left _ _)
    have hδ := arcsinDelta_pos hε
    have hδ' := arcsinDelta_lt_one_fifth hε hε_lt
    rw [transfer_integral I (by linarith) (le_refl 0) (by linarith) hγ,
      transfer_integral I (by linarith) (by linarith) (le_refl 1) hγ]
    exact fdBoundary_ftc_telescope_I H hH hδ hδ'
  hint_left := by
    intro ε hε hεt
    have hε_lt : ε < 1/3 := lt_of_lt_of_le hεt (min_le_left _ _)
    exact gamma_integrable_left_of_I hH hγ (arcsinDelta_pos hε)
      (arcsinDelta_lt_one_fifth hε hε_lt)
  hint_right := by
    intro ε hε hεt
    have hε_lt : ε < 1/3 := lt_of_lt_of_le hεt (min_le_left _ _)
    exact gamma_integrable_right_of_I hH hγ (arcsinDelta_pos hε)
      (arcsinDelta_lt_one_fifth hε hε_lt)
  h_limit := E_atI_tendsto H

end
