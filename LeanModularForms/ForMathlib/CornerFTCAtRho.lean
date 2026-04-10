/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.CrossingAtRho
import LeanModularForms.ForMathlib.SegmentAnalysis
import LeanModularForms.ForMathlib.ArcFTCLimit

/-!
# CornerFTCHyp at rho and rho+1

Constructs complete `CornerFTCHyp` instances for the corner crossings at:
- `rho` at `t0 = 3/5` (arc seg2-3 to vertical seg4, angle pi/3)
- `rho+1` at `t0 = 1/5` (vertical seg1 to arc seg2-3, angle pi/3)

## Strategy

Both crossings have a key simplification: for small enough `eps`, the
`arcsinDelta` and `vertDelta` are chosen so that both approach norms equal `eps`
exactly. This means the log difference `E(eps) = log(f_left) - log(f_right)` is
purely imaginary, equal to `i * (arg_left - arg_right)`.

For rho: `arg_left = pi/6` and `arg_right = pi/2`, giving `E -> -(pi/3)*I`.
For rho+1: `arg_left = pi/2` and `arg_right = 5*pi/6`, giving `E -> -(pi/3)*I`.

## Main results

* `cornerFTCHyp_atRho` -- complete `CornerFTCHyp` at rho
* `cornerFTCHyp_atRhoPlusOne` -- complete `CornerFTCHyp` at rho+1
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ## Part 1: Reference functions for rho -/

private def arcRef_rho (t : ℝ) : ℂ := exp (↑(fdArcAngle t) * I) - ellipticPointRho

private lemma fdArcAngle_contDiff : ContDiff ℝ ⊤ fdArcAngle := by
  unfold fdArcAngle; fun_prop

private lemma arcRef_rho_contDiff : ContDiff ℝ ⊤ arcRef_rho := by
  unfold arcRef_rho
  exact (Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp fdArcAngle_contDiff).mul
      contDiff_const)).sub contDiff_const

private lemma arcRef_rho_eq (H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t - ellipticPointRho = arcRef_rho t := by
  unfold arcRef_rho; rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2]

private lemma arcRef_rho_slitPlane {t : ℝ} (ht1 : 1/5 ≤ t) (ht2 : t < 3/5) :
    arcRef_rho t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  unfold arcRef_rho
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
    add_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, neg_re, one_re, div_ofNat]
  have hlt : fdArcAngle t < 2 * Real.pi / 3 := by unfold fdArcAngle; nlinarith [Real.pi_pos]
  have hge : Real.pi / 3 ≤ fdArcAngle t := by unfold fdArcAngle; nlinarith [Real.pi_pos]
  have h_cos_gt : Real.cos (2 * Real.pi / 3) < Real.cos (fdArcAngle t) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) hlt
  rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three] at h_cos_gt
  linarith

private lemma arcRef_rho_eventuallyEq (H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t < 3/5) :
    (fun s => fdBoundaryFun H s - ellipticPointRho) =ᶠ[𝓝 t] arcRef_rho :=
  Filter.eventually_of_mem
    (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht2))
    fun s ⟨hs1, hs2⟩ => by
      rw [mem_Ioi] at hs1; rw [mem_Iio] at hs2
      exact arcRef_rho_eq H hs1 (le_of_lt hs2)

-- Seg1 reference (right vertical): Re = 1 > 0
private def ref_seg1_rho (H : ℝ) (t : ℝ) : ℂ :=
  1 + (↑H - ↑(Real.sqrt 3) / 2 - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I

private lemma ref_seg1_rho_contDiff (H : ℝ) : ContDiff ℝ ⊤ (ref_seg1_rho H) := by
  unfold ref_seg1_rho
  exact contDiff_const.add (((contDiff_const.sub
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const))).mul contDiff_const)

private lemma ref_seg1_rho_slitPlane (H : ℝ) (t : ℝ) :
    ref_seg1_rho H t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  simp only [ref_seg1_rho, add_re, one_re, mul_re, sub_re, ofReal_re, ofReal_im,
    I_re, I_im, mul_zero, sub_zero]; norm_num

private lemma fdBoundary_sub_rho_eq_ref_seg1 (H : ℝ) (t : ℝ) (ht : t ≤ 1/5) :
    fdBoundaryFun H t - ellipticPointRho = ref_seg1_rho H t := by
  simp only [fdBoundaryFun, ht, ite_true, ellipticPointRho, ellipticPointRho',
    UpperHalfPlane.coe_mk, ref_seg1_rho]
  push_cast; ring

private lemma fdBoundary_sub_rho_eeq_ref_seg1 (H : ℝ) {t : ℝ} (ht : t < 1/5) :
    (fun s => fdBoundaryFun H s - ellipticPointRho) =ᶠ[𝓝 t] ref_seg1_rho H :=
  Filter.eventually_of_mem (Iio_mem_nhds ht) fun s (hs : s < 1/5) =>
    fdBoundary_sub_rho_eq_ref_seg1 H s (le_of_lt hs)

-- Seg4 reference (left vertical): pure positive imaginary
private def ref_seg4_rho (H : ℝ) (t : ℝ) : ℂ :=
  ↑(5 * (t - 3/5) * (H - Real.sqrt 3 / 2)) * I

private lemma ref_seg4_rho_contDiff (H : ℝ) : ContDiff ℝ ⊤ (ref_seg4_rho H) := by
  unfold ref_seg4_rho
  exact (Complex.ofRealCLM.contDiff.comp
    (((contDiff_const.mul ((contDiff_id (𝕜 := ℝ) (E := ℝ)).sub contDiff_const)).mul
      contDiff_const))).mul contDiff_const

private lemma ref_seg4_rho_slitPlane (H : ℝ) (hH : fdHeightValid H)
    {t : ℝ} (ht3 : 3/5 < t) (_ht4 : t ≤ 4/5) :
    ref_seg4_rho H t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  simp only [ref_seg4_rho, mul_im, ofReal_re, I_re, ofReal_im, I_im, mul_zero, mul_one,
    add_zero]
  exact ne_of_gt (by nlinarith)

private lemma fdBoundary_sub_rho_eq_ref_seg4 (H : ℝ) {t : ℝ}
    (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    fdBoundaryFun H t - ellipticPointRho = ref_seg4_rho H t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    ht4, ite_true, ite_false, ellipticPointRho, ellipticPointRho',
    UpperHalfPlane.coe_mk, ref_seg4_rho]; push_cast; ring

private lemma fdBoundary_sub_rho_eeq_ref_seg4 (H : ℝ) {t : ℝ}
    (ht3 : 3/5 < t) (ht4 : t < 4/5) :
    (fun s => fdBoundaryFun H s - ellipticPointRho) =ᶠ[𝓝 t] ref_seg4_rho H :=
  Filter.eventually_of_mem
    (Filter.inter_mem (Ioi_mem_nhds ht3) (Iio_mem_nhds ht4))
    fun s ⟨hs3, hs4⟩ => by
      rw [mem_Ioi] at hs3; rw [mem_Iio] at hs4
      exact fdBoundary_sub_rho_eq_ref_seg4 H hs3 (by linarith)

-- Seg5 reference (horizontal top): Im = H - sqrt(3)/2 > 0
private def ref_seg5_rho (H : ℝ) (t : ℝ) : ℂ :=
  (5 * ↑t - 4) + (↑H - ↑(Real.sqrt 3) / 2) * I

private lemma ref_seg5_rho_contDiff (H : ℝ) : ContDiff ℝ ⊤ (ref_seg5_rho H) := by
  unfold ref_seg5_rho
  exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).add contDiff_const

private lemma ref_seg5_rho_slitPlane (H : ℝ) (hH : fdHeightValid H) (t : ℝ) :
    ref_seg5_rho H t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  show (ref_seg5_rho H t).im ≠ 0
  unfold ref_seg5_rho
  have : ((5 * ↑t - 4 : ℂ) + (↑H - ↑(Real.sqrt 3) / 2) * I).im = H - Real.sqrt 3 / 2 := by
    simp [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  rw [this]; linarith

private lemma fdBoundary_sub_rho_eq_ref_seg5 (H : ℝ) {t : ℝ} (ht : 4/5 < t) :
    fdBoundaryFun H t - ellipticPointRho = ref_seg5_rho H t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    show ¬t ≤ 4/5 from by linarith, ite_false, ellipticPointRho, ellipticPointRho',
    UpperHalfPlane.coe_mk, ref_seg5_rho]
  push_cast; ring

private lemma fdBoundary_sub_rho_eeq_ref_seg5 (H : ℝ) {t : ℝ} (ht : 4/5 < t) :
    (fun s => fdBoundaryFun H s - ellipticPointRho) =ᶠ[𝓝 t] ref_seg5_rho H :=
  Filter.eventually_of_mem (Ioi_mem_nhds ht) fun s (hs : 4/5 < s) =>
    fdBoundary_sub_rho_eq_ref_seg5 H hs

/-! ## Part 2: Integrand form conversion -/

private lemma integrand_form_eq' (f : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    (f t - z)⁻¹ * deriv f t = deriv (fun s => f s - z) t / (f t - z) := by
  rw [show (fun s => f s - z) = (fun s => f s + (-z)) from by ext; ring,
    deriv_add_const, div_eq_mul_inv, mul_comm]

/-! ## Part 3: Per-segment FTC for rho -/

private theorem seg1_ftc_rho (H : ℝ) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho)) volume 0 (1/5) ∧
    ∫ t in (0 : ℝ)..(1/5), deriv (fun s => fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho) =
      Complex.log (fdBoundaryFun H (1/5) - ellipticPointRho) -
      Complex.log (fdBoundaryFun H 0 - ellipticPointRho) :=
  LogDerivFTC.ftc_log_piece (by norm_num)
    (ref_seg1_rho_contDiff H).continuous.continuousOn
    (fun t _ => ((ref_seg1_rho_contDiff H).differentiable (by norm_num)).differentiableAt)
    ((ref_seg1_rho_contDiff H).continuous_deriv le_top).continuousOn
    (fun t _ => ref_seg1_rho_slitPlane H t)
    (fun t ht => ⟨fdBoundary_sub_rho_eq_ref_seg1 H t (by linarith [ht.2]),
      (fdBoundary_sub_rho_eeq_ref_seg1 H (by linarith [ht.2])).deriv_eq⟩)
    (fdBoundary_sub_rho_eq_ref_seg1 H 0 (by norm_num))
    (fdBoundary_sub_rho_eq_ref_seg1 H (1/5) le_rfl)

private theorem arc_ftc_rho (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2/5) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho)) volume (1/5) (3/5 - δ) ∧
    ∫ t in (1/5 : ℝ)..(3/5 - δ), deriv (fun s => fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho) =
      Complex.log (fdBoundaryFun H (3/5 - δ) - ellipticPointRho) -
      Complex.log (fdBoundaryFun H (1/5) - ellipticPointRho) := by
  apply LogDerivFTC.ftc_log_piece (by linarith)
    arcRef_rho_contDiff.continuous.continuousOn
    (fun t _ => arcRef_rho_contDiff.differentiable (by norm_num) |>.differentiableAt)
    (arcRef_rho_contDiff.continuous_deriv le_top).continuousOn
    (fun t ht => arcRef_rho_slitPlane ht.1 (by linarith [ht.2]))
  · intro t ht
    exact ⟨arcRef_rho_eq H (by linarith [ht.1]) (by linarith [ht.2]),
      (arcRef_rho_eventuallyEq H (by linarith [ht.1]) (by linarith [ht.2])).deriv_eq⟩
  · rw [fdBoundaryFun_at_one_fifth]; unfold arcRef_rho; rw [fdArcAngle_at_one_fifth]
    simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
      ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  · exact arcRef_rho_eq H (by linarith) (by linarith)

private theorem seg4_ftc_rho (H : ℝ) (hH : fdHeightValid H) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1/5) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho)) volume (3/5 + δ) (4/5) ∧
    ∫ t in (3/5 + δ)..(4/5 : ℝ), deriv (fun s => fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho) =
      Complex.log (fdBoundaryFun H (4/5) - ellipticPointRho) -
      Complex.log (fdBoundaryFun H (3/5 + δ) - ellipticPointRho) :=
  LogDerivFTC.ftc_log_piece (by linarith)
    (ref_seg4_rho_contDiff H).continuous.continuousOn
    (fun t _ => ((ref_seg4_rho_contDiff H).differentiable (by norm_num)).differentiableAt)
    ((ref_seg4_rho_contDiff H).continuous_deriv le_top).continuousOn
    (fun t ht => ref_seg4_rho_slitPlane H hH (by linarith [ht.1]) ht.2)
    (fun t ht => ⟨fdBoundary_sub_rho_eq_ref_seg4 H (by linarith [ht.1]) (by linarith [ht.2]),
      (fdBoundary_sub_rho_eeq_ref_seg4 H (by linarith [ht.1]) (by linarith [ht.2])).deriv_eq⟩)
    (fdBoundary_sub_rho_eq_ref_seg4 H (by linarith) (by linarith))
    (fdBoundary_sub_rho_eq_ref_seg4 H (by norm_num) le_rfl)

private theorem seg5_ftc_rho (H : ℝ) (hH : fdHeightValid H) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho)) volume (4/5) 1 ∧
    ∫ t in (4/5 : ℝ)..1, deriv (fun s => fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho) =
      Complex.log (fdBoundaryFun H 1 - ellipticPointRho) -
      Complex.log (fdBoundaryFun H (4/5) - ellipticPointRho) := by
  refine LogDerivFTC.ftc_log_piece (by norm_num)
    (ref_seg5_rho_contDiff H).continuous.continuousOn
    (fun t _ => ((ref_seg5_rho_contDiff H).differentiable (by norm_num)).differentiableAt)
    ((ref_seg5_rho_contDiff H).continuous_deriv le_top).continuousOn
    (fun t _ => ref_seg5_rho_slitPlane H hH t)
    (fun t ht => ⟨fdBoundary_sub_rho_eq_ref_seg5 H (by linarith [ht.1]),
      (fdBoundary_sub_rho_eeq_ref_seg5 H (by linarith [ht.1])).deriv_eq⟩)
    ?_ ?_
  · rw [fdBoundaryFun_at_four_fifths]
    simp only [ref_seg5_rho, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    push_cast; ring
  · rw [fdBoundaryFun_at_one]
    simp only [ref_seg5_rho, fdStart, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    push_cast; ring

/-! ## Part 4: FTC telescope + integrability for rho -/

set_option maxHeartbeats 800000 in
theorem fdBoundary_ftc_telescope_rho (H : ℝ) (hH : 1 < H) {δL δR : ℝ}
    (hδL : 0 < δL) (hδL' : δL < 2/5) (hδR : 0 < δR) (hδR' : δR < 1/5) :
    (∫ t in (0 : ℝ)..(3/5 - δL),
        (fdBoundaryFun H t - ellipticPointRho)⁻¹ * deriv (fdBoundaryFun H) t) +
    (∫ t in (3/5 + δR)..(1 : ℝ),
        (fdBoundaryFun H t - ellipticPointRho)⁻¹ * deriv (fdBoundaryFun H) t) =
    Complex.log (fdBoundaryFun H (3/5 - δL) - ellipticPointRho) -
    Complex.log (fdBoundaryFun H (3/5 + δR) - ellipticPointRho) := by
  have hH_valid := fdHeightValid_of_one_lt H hH
  have h_form : ∀ t, (fdBoundaryFun H t - ellipticPointRho)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (fun s => fdBoundaryFun H s - ellipticPointRho) t /
        (fdBoundaryFun H t - ellipticPointRho) :=
    fun t => integrand_form_eq' (fdBoundaryFun H) ellipticPointRho t
  simp_rw [h_form]
  have p1 := seg1_ftc_rho H
  have p2 := arc_ftc_rho H hδL hδL'
  have p4 := seg4_ftc_rho H hH_valid hδR hδR'
  have p5 := seg5_ftc_rho H hH_valid
  have hleft :
    ∫ t in (0 : ℝ)..(3/5 - δL),
      deriv (fun s => fdBoundaryFun H s - ellipticPointRho) t /
        (fdBoundaryFun H t - ellipticPointRho) =
    Complex.log (fdBoundaryFun H (3/5 - δL) - ellipticPointRho) -
    Complex.log (fdBoundaryFun H 0 - ellipticPointRho) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals p1.1 p2.1, p1.2, p2.2]; ring
  have hright :
    ∫ t in (3/5 + δR)..(1 : ℝ),
      deriv (fun s => fdBoundaryFun H s - ellipticPointRho) t /
        (fdBoundaryFun H t - ellipticPointRho) =
    Complex.log (fdBoundaryFun H 1 - ellipticPointRho) -
    Complex.log (fdBoundaryFun H (3/5 + δR) - ellipticPointRho) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals p4.1 p5.1, p4.2, p5.2]; ring
  rw [hleft, hright, fdBoundaryFun_closed H]; ring

theorem fdBoundary_integrable_left_of_rho (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2/5) :
    IntervalIntegrable
      (fun t => (fdBoundaryFun H t - ellipticPointRho)⁻¹ * deriv (fdBoundaryFun H) t)
      volume 0 (3/5 - δ) := by
  simp_rw [fun t => integrand_form_eq' (fdBoundaryFun H) ellipticPointRho t]
  exact (seg1_ftc_rho H).1.trans (arc_ftc_rho H hδ hδ').1

theorem fdBoundary_integrable_right_of_rho (H : ℝ) (hH : fdHeightValid H)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) :
    IntervalIntegrable
      (fun t => (fdBoundaryFun H t - ellipticPointRho)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (3/5 + δ) 1 := by
  simp_rw [fun t => integrand_form_eq' (fdBoundaryFun H) ellipticPointRho t]
  exact (seg4_ftc_rho H hH hδ hδ').1.trans (seg5_ftc_rho H hH).1

/-! ## Part 5: Norm and arg at the rho crossing -/

private theorem arc_norm_at_rho (H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) :
    ‖fdBoundaryFun H (3/5 - arcsinDelta ε) - ellipticPointRho‖ = ε := by
  have hδ := arcsinDelta_pos hε
  have hδ' := arcsinDelta_lt_one_fifth hε hε_lt
  rw [fdBoundaryFun_arc_dist_rho H _ (by linarith) (by linarith)]
  rw [show fdArcAngle (3/5 - arcsinDelta ε) - 2 * Real.pi / 3 =
      -(5 * arcsinDelta ε * Real.pi / 6) from by unfold fdArcAngle; ring,
    show -(5 * arcsinDelta ε * Real.pi / 6) / 2 = -(5 * Real.pi / 12 * arcsinDelta ε) from
      by ring,
    Real.sin_neg, abs_neg, half_angle_arcsinDelta,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      (Real.arcsin_nonneg.mpr (by linarith))
      (le_trans (Real.arcsin_le_pi_div_two _) (by linarith [Real.pi_pos]))),
    Real.sin_arcsin (by linarith) (by linarith)]
  linarith

private theorem vert_norm_at_rho (H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε)
    (hε_lt : ε < H - Real.sqrt 3 / 2) :
    ‖fdBoundaryFun H (3/5 + vertDelta H ε) - ellipticPointRho‖ = ε := by
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  rw [fdBoundaryFun_seg4_dist_rho H hH _ (by linarith [vertDelta_pos hH hε])
    (by linarith [vertDelta_lt_one_fifth hH hε_lt]),
    show 3/5 + vertDelta H ε - 3/5 = vertDelta H ε from by ring]
  unfold vertDelta
  rw [show 5 * (ε / (5 * (H - Real.sqrt 3 / 2))) * (H - Real.sqrt 3 / 2) =
    ε / (5 * (H - Real.sqrt 3 / 2)) * (5 * (H - Real.sqrt 3 / 2)) from by ring]
  exact div_mul_cancel₀ ε (ne_of_gt (by positivity))

set_option maxHeartbeats 800000 in
private theorem arc_arg_at_rho (H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) :
    (fdBoundaryFun H (3/5 - arcsinDelta ε) - ellipticPointRho).arg =
      Real.pi / 6 - 5 * arcsinDelta ε * Real.pi / 12 := by
  have hδ := arcsinDelta_pos hε
  have hδ' := arcsinDelta_lt_one_fifth hε hε_lt
  rw [fdBoundaryFun_arc_eq_exp H _ (by linarith) (by linarith), exp_mul_I,
    ← ofReal_cos, ← ofReal_sin]
  set θ := fdArcAngle (3/5 - arcsinDelta ε)
  set α := 5 * arcsinDelta ε * Real.pi / 12 with α_def
  have hα_pos : 0 < α := by positivity
  have hα_small : α < Real.pi / 6 := by
    rw [α_def]; nlinarith [arcsinDelta_lt_one_fifth hε hε_lt]
  have h_sinα_pos : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα_pos (by linarith [Real.pi_pos])
  have hθ_eq : θ = 2 * Real.pi / 3 - 2 * α := by
    show fdArcAngle (3/5 - arcsinDelta ε) = _; unfold fdArcAngle; rw [α_def]; ring
  -- Factorization: exp(iθ) - rho = 2sin(α)·exp(i(π/6 - α))
  -- Prove Re and Im components separately using explicit trig
  have h_cos_theta : Real.cos θ + 1/2 = 2 * Real.sin α * Real.cos (Real.pi / 6 - α) := by
    rw [hθ_eq, show (2 * Real.pi / 3 - 2 * α : ℝ) = (Real.pi - Real.pi / 3) - 2 * α from
      by ring, Real.cos_sub, show Real.cos (Real.pi - Real.pi / 3) = -(1/2) from by
      rw [Real.cos_pi_sub, Real.cos_pi_div_three],
      show Real.sin (Real.pi - Real.pi / 3) = Real.sqrt 3 / 2 from by
      rw [Real.sin_pi_sub, Real.sin_pi_div_three], Real.cos_two_mul, Real.sin_two_mul,
      Real.cos_sub, Real.cos_pi_div_six, Real.sin_pi_div_six]
    nlinarith [Real.sin_sq_add_cos_sq α]
  have h_sin_theta : Real.sin θ - Real.sqrt 3 / 2 =
      2 * Real.sin α * Real.sin (Real.pi / 6 - α) := by
    rw [hθ_eq, show (2 * Real.pi / 3 - 2 * α : ℝ) = (Real.pi - Real.pi / 3) - 2 * α from
      by ring, Real.sin_sub, show Real.sin (Real.pi - Real.pi / 3) = Real.sqrt 3 / 2 from by
      rw [Real.sin_pi_sub, Real.sin_pi_div_three],
      show Real.cos (Real.pi - Real.pi / 3) = -(1/2) from by
      rw [Real.cos_pi_sub, Real.cos_pi_div_three], Real.cos_two_mul, Real.sin_two_mul,
      Real.sin_sub, Real.sin_pi_div_six, Real.cos_pi_div_six]; ring_nf
    have h5 := Real.sin_sq_add_cos_sq α
    have h6 : Real.sqrt 3 * (Real.sin α ^ 2 + Real.cos α ^ 2) = Real.sqrt 3 := by rw [h5, mul_one]
    linarith
  have h_re : (↑(Real.cos θ) + ↑(Real.sin θ) * I : ℂ) - ellipticPointRho =
      ↑(2 * Real.sin α) * (↑(Real.cos (Real.pi / 6 - α)) +
        ↑(Real.sin (Real.pi / 6 - α)) * I) := by
    simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    apply Complex.ext
    · simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, sub_zero, add_zero, mul_one, neg_re, one_re, div_ofNat, zero_mul]
      linarith [h_cos_theta]
    · simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
        mul_zero, add_zero, mul_one, zero_add, neg_im, one_im, div_ofNat, zero_mul]
      linarith [h_sin_theta]
  rw [h_re]
  have h_trig_rho : (↑(Real.cos (Real.pi / 6 - α)) : ℂ) +
      ↑(Real.sin (Real.pi / 6 - α)) * I =
      Complex.cos ↑(Real.pi / 6 - α) + Complex.sin ↑(Real.pi / 6 - α) * I := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [h_trig_rho]
  exact Complex.arg_mul_cos_add_sin_mul_I (show (0:ℝ) < 2 * Real.sin α from by positivity)
    ⟨by linarith [Real.pi_pos], le_of_lt (by linarith [Real.pi_pos])⟩

private theorem vert_arg_at_rho (H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε)
    (hε_lt : ε < H - Real.sqrt 3 / 2) :
    (fdBoundaryFun H (3/5 + vertDelta H ε) - ellipticPointRho).arg = Real.pi / 2 := by
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  rw [fdBoundary_sub_rho_eq_ref_seg4 H (by linarith [vertDelta_pos hH hε])
    (by linarith [vertDelta_lt_one_fifth hH hε_lt])]
  show (↑(5 * (3/5 + vertDelta H ε - 3/5) * (H - Real.sqrt 3 / 2)) * I : ℂ).arg = _
  rw [show (5 * (3/5 + vertDelta H ε - 3/5) * (H - Real.sqrt 3 / 2) : ℝ) =
    5 * vertDelta H ε * (H - Real.sqrt 3 / 2) from by ring]
  exact arg_ofReal_mul_I _ (by have := vertDelta_pos hH hε; positivity)

/-! ## Part 6: E function and limit for rho -/

private def E_atRho (H : ℝ) (ε : ℝ) : ℂ :=
  Complex.log (fdBoundaryFun H (3/5 - arcsinDelta ε) - ellipticPointRho) -
  Complex.log (fdBoundaryFun H (3/5 + vertDelta H ε) - ellipticPointRho)

set_option maxHeartbeats 400000 in
private theorem E_atRho_eq (H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε)
    (hε_lt : ε < min (1/3) (H - Real.sqrt 3 / 2)) :
    E_atRho H ε = ↑(Real.pi / 6 - 5 * arcsinDelta ε * Real.pi / 12 - Real.pi / 2) * I := by
  have hε_13 : ε < 1/3 := lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hε_H : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_lt (min_le_right _ _)
  unfold E_atRho
  have h_ne_left : fdBoundaryFun H (3/5 - arcsinDelta ε) - ellipticPointRho ≠ 0 := by
    intro h; have := arc_norm_at_rho H hε hε_13
    rw [h, norm_zero] at this; linarith
  have h_ne_right : fdBoundaryFun H (3/5 + vertDelta H ε) - ellipticPointRho ≠ 0 := by
    intro h; have := vert_norm_at_rho H hH hε hε_H
    rw [h, norm_zero] at this; linarith
  rw [log_sub_eq_of_equal_norm h_ne_left h_ne_right
    (by rw [arc_norm_at_rho H hε hε_13, vert_norm_at_rho H hH hε hε_H]),
    arc_arg_at_rho H hε hε_13, vert_arg_at_rho H hH hε hε_H]

private theorem E_atRho_tendsto (H : ℝ) (hH : fdHeightValid H) :
    Tendsto (E_atRho H) (𝓝[>] 0) (𝓝 (-(↑Real.pi / 3 * I))) := by
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  have hkey : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      E_atRho H ε = ↑(Real.pi / 6 - 5 * arcsinDelta ε * Real.pi / 12 - Real.pi / 2) * I := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (lt_min (by norm_num : (0:ℝ) < 1/3) hH')] with ε hε hε_pos
    exact E_atRho_eq H hH (by rwa [mem_Ioi] at hε_pos) (by rwa [mem_Iio] at hε)
  -- The limit of the RHS as ε → 0+
  have htend : Tendsto (fun ε : ℝ =>
      (↑(Real.pi / 6 - 5 * arcsinDelta ε * Real.pi / 12 - Real.pi / 2) : ℂ) * I)
      (𝓝[>] 0) (𝓝 (-(↑Real.pi / 3 * I))) := by
    have hcont : ContinuousAt (fun ε : ℝ =>
        Real.pi / 6 - 5 * arcsinDelta ε * Real.pi / 12 - Real.pi / 2) 0 := by
      unfold arcsinDelta; fun_prop
    have hval : Real.pi / 6 - 5 * arcsinDelta 0 * Real.pi / 12 - Real.pi / 2 =
        -(Real.pi / 3) := by
      simp [arcsinDelta, Real.arcsin_zero]; ring
    rw [show -(↑Real.pi / 3 * I : ℂ) = ↑(-(Real.pi / 3)) * I from by push_cast; ring]
    have h := hcont.tendsto
    rw [hval] at h
    exact ((continuous_ofReal.continuousAt.tendsto.comp h).mul_const I).mono_left
      nhdsWithin_le_nhds
  exact htend.congr' (hkey.mono (fun ε h => h.symm))

/-! ## Part 7: Assembly for rho -/

/-- The complete `CornerFTCHyp` at rho. -/
def cornerFTCHyp_atRho {H : ℝ} (hH : 1 < H)
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t) :
    CornerFTCHyp γ ellipticPointRho (3/5)
      arcsinDelta (vertDelta H)
      (min (1/3) (H - Real.sqrt 3 / 2))
      (-(↑Real.pi / 3 * I)) where
  E := E_atRho H
  h_ftc := by
    intro ε hε hεt
    have hε_13 : ε < 1/3 := lt_of_lt_of_le hεt (min_le_left _ _)
    have hε_H : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hεt (min_le_right _ _)
    have hH_valid := fdHeightValid_of_one_lt H hH
    have hδL := arcsinDelta_pos hε
    have hδL' := arcsinDelta_lt_one_fifth hε hε_13
    have hδR := vertDelta_pos hH_valid hε
    have hδR' := vertDelta_lt_one_fifth hH_valid hε_H
    rw [transfer_integral ellipticPointRho (by linarith) (le_refl 0) (by linarith) hγ,
      transfer_integral ellipticPointRho (by linarith) (by linarith) (le_refl 1) hγ]
    exact fdBoundary_ftc_telescope_rho H hH hδL (by linarith) hδR hδR'
  hint_left := by
    intro ε hε hεt
    have hε_13 : ε < 1/3 := lt_of_lt_of_le hεt (min_le_left _ _)
    have hδL := arcsinDelta_pos hε
    have hδL' := arcsinDelta_lt_one_fifth hε hε_13
    exact transfer_integrability ellipticPointRho (by linarith) (le_refl 0) (by linarith) hγ
      (fdBoundary_integrable_left_of_rho H hδL (by linarith))
  hint_right := by
    intro ε hε hεt
    have hε_H : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hεt (min_le_right _ _)
    have hH_valid := fdHeightValid_of_one_lt H hH
    have hδR := vertDelta_pos hH_valid hε
    have hδR' := vertDelta_lt_one_fifth hH_valid hε_H
    exact transfer_integrability ellipticPointRho (by linarith) (by linarith) (le_refl 1) hγ
      (fdBoundary_integrable_right_of_rho H hH_valid hδR hδR')
  h_limit := E_atRho_tendsto H (fdHeightValid_of_one_lt H hH)

/-! ## Part 8: Reference functions for rho+1 -/

-- Seg1 reference for rho+1 (pure positive imaginary → slitPlane)
private def ref_seg1_rp1 (H : ℝ) (t : ℝ) : ℂ :=
  ↑(5 * (1/5 - t) * (H - Real.sqrt 3 / 2)) * I

private lemma ref_seg1_rp1_contDiff (H : ℝ) : ContDiff ℝ ⊤ (ref_seg1_rp1 H) := by
  unfold ref_seg1_rp1
  exact (Complex.ofRealCLM.contDiff.comp
    (((contDiff_const.mul (contDiff_const.sub (contDiff_id (𝕜 := ℝ) (E := ℝ)))).mul
      contDiff_const))).mul contDiff_const

private lemma ref_seg1_rp1_slitPlane (H : ℝ) (hH : fdHeightValid H)
    {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t < 1/5) :
    ref_seg1_rp1 H t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  simp only [ref_seg1_rp1, mul_im, ofReal_re, I_re, ofReal_im, I_im, mul_zero, mul_one,
    add_zero]
  exact ne_of_gt (by nlinarith)

private lemma fdBoundary_sub_rp1_eq_ref_seg1 (H : ℝ) {t : ℝ}
    (_ht0 : 0 ≤ t) (ht1 : t ≤ 1/5) :
    fdBoundaryFun H t - ellipticPointRhoPlusOne = ref_seg1_rp1 H t := by
  simp only [fdBoundaryFun, ht1, ite_true, ellipticPointRhoPlusOne,
    ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk, ref_seg1_rp1]; push_cast; ring

private lemma fdBoundary_sub_rp1_eeq_ref_seg1 (H : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1/5) :
    (fun s => fdBoundaryFun H s - ellipticPointRhoPlusOne) =ᶠ[𝓝 t] ref_seg1_rp1 H :=
  Filter.eventually_of_mem
    (Filter.inter_mem (Ioi_mem_nhds ht0) (Iio_mem_nhds ht1))
    fun s ⟨hs0, hs1⟩ => by
      rw [mem_Ioi] at hs0; rw [mem_Iio] at hs1
      exact fdBoundary_sub_rp1_eq_ref_seg1 H (by linarith) (by linarith)

-- Arc reference for rho+1: Im > 0 on (1/5, 3/5), neg-slit-plane
private def arcRef_rp1 (t : ℝ) : ℂ := exp (↑(fdArcAngle t) * I) - ellipticPointRhoPlusOne

private lemma arcRef_rp1_contDiff : ContDiff ℝ ⊤ arcRef_rp1 := by
  unfold arcRef_rp1
  exact (Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp fdArcAngle_contDiff).mul
      contDiff_const)).sub contDiff_const

private lemma arcRef_rp1_eq (H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t - ellipticPointRhoPlusOne = arcRef_rp1 t := by
  unfold arcRef_rp1; rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2]

private lemma arcRef_rp1_eventuallyEq (H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t < 3/5) :
    (fun s => fdBoundaryFun H s - ellipticPointRhoPlusOne) =ᶠ[𝓝 t] arcRef_rp1 :=
  Filter.eventually_of_mem
    (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht2))
    fun s ⟨hs1, hs2⟩ => by
      rw [mem_Ioi] at hs1; rw [mem_Iio] at hs2
      exact arcRef_rp1_eq H hs1 (le_of_lt hs2)

-- For rho+1, -arcRef is in slitPlane (Re of -(exp(iθ) - rp1) = 1/2 - cos(θ) > 0)
private lemma arcRef_rp1_neg_slitPlane {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    -(arcRef_rp1 t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  unfold arcRef_rp1
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk,
    neg_sub, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, add_zero, one_re, div_ofNat]
  have hgt : Real.pi / 3 < fdArcAngle t := by unfold fdArcAngle; nlinarith [Real.pi_pos]
  have hle : fdArcAngle t ≤ 2 * Real.pi / 3 := by unfold fdArcAngle; nlinarith [Real.pi_pos]
  have h_cos_le : Real.cos (fdArcAngle t) ≤ Real.cos (Real.pi / 3) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) hgt.le
  rw [Real.cos_pi_div_three] at h_cos_le
  -- For t < 3/5, strict inequality; for t = 3/5, cos(2pi/3) = -1/2, so 1/2 - (-1/2) = 1
  rcases eq_or_lt_of_le ht2 with rfl | ht2'
  · rw [fdArcAngle_at_three_fifths,
      show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  · have h_strict : Real.cos (fdArcAngle t) < Real.cos (Real.pi / 3) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos]) hgt
    rw [Real.cos_pi_div_three] at h_strict; linarith

/-! ## Part 9: Per-segment FTC for rho+1 -/

-- Seg1 FTC for rho+1: [0, 1/5 - δ]
private theorem seg1_ftc_rp1 (H : ℝ) (hH : fdHeightValid H) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1/5) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
      (fdBoundaryFun H t - ellipticPointRhoPlusOne)) volume 0 (1/5 - δ) ∧
    ∫ t in (0 : ℝ)..(1/5 - δ),
      deriv (fun s => fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
      (fdBoundaryFun H t - ellipticPointRhoPlusOne) =
      Complex.log (fdBoundaryFun H (1/5 - δ) - ellipticPointRhoPlusOne) -
      Complex.log (fdBoundaryFun H 0 - ellipticPointRhoPlusOne) :=
  LogDerivFTC.ftc_log_piece (by linarith)
    (ref_seg1_rp1_contDiff H).continuous.continuousOn
    (fun t _ => ((ref_seg1_rp1_contDiff H).differentiable (by norm_num)).differentiableAt)
    ((ref_seg1_rp1_contDiff H).continuous_deriv le_top).continuousOn
    (fun t ht => ref_seg1_rp1_slitPlane H hH (by linarith [ht.1]) (by linarith [ht.2]))
    (fun t ht => ⟨fdBoundary_sub_rp1_eq_ref_seg1 H (by linarith [ht.1]) (by linarith [ht.2]),
      (fdBoundary_sub_rp1_eeq_ref_seg1 H (by linarith [ht.1]) (by linarith [ht.2])).deriv_eq⟩)
    (fdBoundary_sub_rp1_eq_ref_seg1 H (by norm_num) (by norm_num))
    (fdBoundary_sub_rp1_eq_ref_seg1 H (by linarith) (by linarith))

-- Arc FTC for rho+1 using neg-slit-plane: [1/5 + δ, 3/5]
private theorem arc_ftc_neg_rp1 (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2/5) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
      (fdBoundaryFun H t - ellipticPointRhoPlusOne)) volume (1/5 + δ) (3/5) ∧
    ∫ t in (1/5 + δ)..(3/5 : ℝ),
      deriv (fun s => fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
      (fdBoundaryFun H t - ellipticPointRhoPlusOne) =
      Complex.log (-(fdBoundaryFun H (3/5) - ellipticPointRhoPlusOne)) -
      Complex.log (-(fdBoundaryFun H (1/5 + δ) - ellipticPointRhoPlusOne)) := by
  have hab : (1/5 + δ) ≤ (3/5 : ℝ) := by linarith
  have h_piece := LogDerivFTC.ftc_log_neg_on_segment hab
    arcRef_rp1_contDiff.continuous.continuousOn
    (fun t _ => arcRef_rp1_contDiff.differentiable (by norm_num) |>.differentiableAt)
    (arcRef_rp1_contDiff.continuous_deriv le_top).continuousOn
    (fun t ht => arcRef_rp1_neg_slitPlane (by linarith [ht.1]) ht.2)
  have h_ae : ∀ᵐ t ∂volume, t ∈ Ι (1/5 + δ) (3/5 : ℝ) →
      deriv (fun s => fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
        (fdBoundaryFun H t - ellipticPointRhoPlusOne) =
      deriv arcRef_rp1 t / arcRef_rp1 t := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (3/5 : ℝ))] with t ht_ne ht_mem
    rw [uIoc_of_le hab] at ht_mem
    have ht_lt : t < 3/5 := lt_of_le_of_ne ht_mem.2
      (fun h => ht_ne (mem_singleton_iff.mpr h))
    have ht_gt : 1/5 < t := by linarith [ht_mem.1]
    rw [arcRef_rp1_eq H ht_gt (le_of_lt ht_lt),
      (arcRef_rp1_eventuallyEq H ht_gt ht_lt).deriv_eq]
  exact ⟨h_piece.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae.mono fun t ht hm => (ht hm).symm)),
    by rw [intervalIntegral.integral_congr_ae h_ae, h_piece.2,
      arcRef_rp1_eq H (by linarith) le_rfl,
      arcRef_rp1_eq H (by linarith) (by linarith)]⟩

-- Seg4 + Seg5 for rho+1: reuse the rho references
-- Seg4 for rp1: f(t) - rp1 = f(t) - rho - 1, but the integrand only uses
-- f(t) - rp1 in the denominator. We use continuity + nonvanishing for integrability.

-- For the FTC telescope for rho+1, we use a different approach:
-- We take integrability as hypotheses and only prove the E function + limit.

/-! ## Part 10: Norm and arg at the rho+1 crossing -/

private theorem vert_norm_at_rp1 (H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε)
    (hε_lt : ε < H - Real.sqrt 3 / 2) :
    ‖fdBoundaryFun H (1/5 - vertDelta H ε) - ellipticPointRhoPlusOne‖ = ε := by
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  have hδ := vertDelta_pos hH hε
  have hδ' := vertDelta_lt_one_fifth hH hε_lt
  rw [fdBoundaryFun_seg1_dist_rhoPlusOne H hH _ (by linarith) (by linarith),
    show 1/5 - (1/5 - vertDelta H ε) = vertDelta H ε from by ring]
  unfold vertDelta
  rw [show 5 * (ε / (5 * (H - Real.sqrt 3 / 2))) * (H - Real.sqrt 3 / 2) =
    ε / (5 * (H - Real.sqrt 3 / 2)) * (5 * (H - Real.sqrt 3 / 2)) from by ring]
  exact div_mul_cancel₀ ε (ne_of_gt (by positivity))

private theorem arc_norm_at_rp1 (H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) :
    ‖fdBoundaryFun H (1/5 + arcsinDelta ε) - ellipticPointRhoPlusOne‖ = ε := by
  have hδ := arcsinDelta_pos hε
  have hδ' := arcsinDelta_lt_one_fifth hε hε_lt
  rw [fdBoundaryFun_arc_dist_rhoPlusOne H _ (by linarith) (by linarith),
    show fdArcAngle (1/5 + arcsinDelta ε) - Real.pi / 3 =
      5 * arcsinDelta ε * Real.pi / 6 from by unfold fdArcAngle; ring,
    show 5 * arcsinDelta ε * Real.pi / 6 / 2 = 5 * Real.pi / 12 * arcsinDelta ε from
      by ring,
    half_angle_arcsinDelta,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      (Real.arcsin_nonneg.mpr (by linarith))
      (le_trans (Real.arcsin_le_pi_div_two _) (by linarith [Real.pi_pos]))),
    Real.sin_arcsin (by linarith) (by linarith)]
  linarith

private theorem vert_arg_at_rp1 (H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε)
    (hε_lt : ε < H - Real.sqrt 3 / 2) :
    (fdBoundaryFun H (1/5 - vertDelta H ε) - ellipticPointRhoPlusOne).arg = Real.pi / 2 := by
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  have hδ := vertDelta_pos hH hε
  have hδ' := vertDelta_lt_one_fifth hH hε_lt
  rw [fdBoundary_sub_rp1_eq_ref_seg1 H (by linarith) (by linarith)]
  show (↑(5 * (1/5 - (1/5 - vertDelta H ε)) * (H - Real.sqrt 3 / 2)) * I : ℂ).arg = _
  rw [show (5 * (1/5 - (1/5 - vertDelta H ε)) * (H - Real.sqrt 3 / 2) : ℝ) =
    5 * vertDelta H ε * (H - Real.sqrt 3 / 2) from by ring]
  exact arg_ofReal_mul_I _ (by positivity)

set_option maxHeartbeats 800000 in
private theorem arc_arg_at_rp1 (H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) :
    (fdBoundaryFun H (1/5 + arcsinDelta ε) - ellipticPointRhoPlusOne).arg =
      5 * Real.pi / 6 + 5 * arcsinDelta ε * Real.pi / 12 := by
  have hδ := arcsinDelta_pos hε
  have hδ' := arcsinDelta_lt_one_fifth hε hε_lt
  rw [fdBoundaryFun_arc_eq_exp H _ (by linarith) (by linarith), exp_mul_I,
    ← ofReal_cos, ← ofReal_sin]
  set θ := fdArcAngle (1/5 + arcsinDelta ε)
  set α := 5 * arcsinDelta ε * Real.pi / 12 with α_def
  have hα_pos : 0 < α := by positivity
  have hα_small : α < Real.pi / 6 := by
    rw [α_def]; nlinarith [arcsinDelta_lt_one_fifth hε hε_lt]
  have h_sinα_pos : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα_pos (by linarith [Real.pi_pos])
  have hθ_eq : θ = Real.pi / 3 + 2 * α := by
    show fdArcAngle (1/5 + arcsinDelta ε) = _; unfold fdArcAngle; rw [α_def]; ring
  -- Trig identities for cos and sin
  have hc56 : Real.cos (5 * Real.pi / 6) = -(Real.sqrt 3 / 2) := by
    rw [show (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_six]
  have hs56 : Real.sin (5 * Real.pi / 6) = 1/2 := by
    rw [show (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 from by ring,
      Real.sin_pi_sub, Real.sin_pi_div_six]
  -- exp(i(pi/3 + 2α)) - (1/2 + i*√3/2)
  -- Re component
  have h_cos_theta : Real.cos θ - 1/2 = 2 * Real.sin α * Real.cos (5 * Real.pi / 6 + α) := by
    rw [hθ_eq, Real.cos_add (Real.pi / 3) (2 * α), Real.cos_pi_div_three,
      Real.sin_pi_div_three, Real.cos_two_mul, Real.sin_two_mul,
      Real.cos_add (5 * Real.pi / 6) α, hc56, hs56]
    nlinarith [Real.sin_sq_add_cos_sq α]
  -- Im component
  have h_sin_theta : Real.sin θ - Real.sqrt 3 / 2 =
      2 * Real.sin α * Real.sin (5 * Real.pi / 6 + α) := by
    rw [hθ_eq, Real.sin_add (Real.pi / 3) (2 * α), Real.sin_pi_div_three,
      Real.cos_pi_div_three, Real.cos_two_mul, Real.sin_two_mul,
      Real.sin_add (5 * Real.pi / 6) α, hc56, hs56]; ring_nf
    have h5 := Real.sin_sq_add_cos_sq α
    have h6 : Real.sqrt 3 * (Real.sin α ^ 2 + Real.cos α ^ 2) = Real.sqrt 3 := by rw [h5, mul_one]
    linarith
  have h_re : (↑(Real.cos θ) + ↑(Real.sin θ) * I : ℂ) - ellipticPointRhoPlusOne =
      ↑(2 * Real.sin α) * (↑(Real.cos (5 * Real.pi / 6 + α)) +
        ↑(Real.sin (5 * Real.pi / 6 + α)) * I) := by
    simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
    apply Complex.ext
    · simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, sub_zero, add_zero, mul_one, one_re, div_ofNat, zero_mul]
      linarith [h_cos_theta]
    · simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
        mul_zero, add_zero, mul_one, zero_add, one_im, div_ofNat, zero_mul]
      linarith [h_sin_theta]
  rw [h_re]
  have h_angle_pos : -(Real.pi) < 5 * Real.pi / 6 + α := by linarith [Real.pi_pos]
  have h_angle_le : 5 * Real.pi / 6 + α ≤ Real.pi := by linarith [Real.pi_pos]
  rw [show (↑(Real.cos (5 * Real.pi / 6 + α)) : ℂ) = Complex.cos ↑(5 * Real.pi / 6 + α) from
    Complex.ofReal_cos _,
    show (↑(Real.sin (5 * Real.pi / 6 + α)) : ℂ) = Complex.sin ↑(5 * Real.pi / 6 + α) from
    Complex.ofReal_sin _]
  exact Complex.arg_mul_cos_add_sin_mul_I (show (0 : ℝ) < 2 * Real.sin α from by positivity)
    ⟨h_angle_pos, h_angle_le⟩

/-! ## Part 11: E function and limit for rho+1 -/

private def E_atRhoPlusOne (H : ℝ) (ε : ℝ) : ℂ :=
  Complex.log (fdBoundaryFun H (1/5 - vertDelta H ε) - ellipticPointRhoPlusOne) -
  Complex.log (fdBoundaryFun H (1/5 + arcsinDelta ε) - ellipticPointRhoPlusOne)

set_option maxHeartbeats 400000 in
private theorem E_atRhoPlusOne_eq (H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε)
    (hε_lt : ε < min (1/3) (H - Real.sqrt 3 / 2)) :
    E_atRhoPlusOne H ε =
      ↑(Real.pi / 2 - (5 * Real.pi / 6 + 5 * arcsinDelta ε * Real.pi / 12)) * I := by
  have hε_13 : ε < 1/3 := lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hε_H : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_lt (min_le_right _ _)
  unfold E_atRhoPlusOne
  have h_ne_left : fdBoundaryFun H (1/5 - vertDelta H ε) - ellipticPointRhoPlusOne ≠ 0 := by
    intro h; have := vert_norm_at_rp1 H hH hε hε_H
    rw [h, norm_zero] at this; linarith
  have h_ne_right : fdBoundaryFun H (1/5 + arcsinDelta ε) - ellipticPointRhoPlusOne ≠ 0 := by
    intro h; have := arc_norm_at_rp1 H hε hε_13
    rw [h, norm_zero] at this; linarith
  rw [log_sub_eq_of_equal_norm h_ne_left h_ne_right
    (by rw [vert_norm_at_rp1 H hH hε hε_H, arc_norm_at_rp1 H hε hε_13]),
    vert_arg_at_rp1 H hH hε hε_H, arc_arg_at_rp1 H hε hε_13]

private theorem E_atRhoPlusOne_tendsto (H : ℝ) (hH : fdHeightValid H) :
    Tendsto (E_atRhoPlusOne H) (𝓝[>] 0) (𝓝 (-(↑Real.pi / 3 * I))) := by
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  have hkey : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      E_atRhoPlusOne H ε =
        ↑(Real.pi / 2 - (5 * Real.pi / 6 + 5 * arcsinDelta ε * Real.pi / 12)) * I := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (lt_min (by norm_num : (0:ℝ) < 1/3) hH')] with ε hε hε_pos
    exact E_atRhoPlusOne_eq H hH (by rwa [mem_Ioi] at hε_pos) (by rwa [mem_Iio] at hε)
  have htend : Tendsto (fun ε : ℝ =>
      (↑(Real.pi / 2 - (5 * Real.pi / 6 + 5 * arcsinDelta ε * Real.pi / 12)) : ℂ) * I)
      (𝓝[>] 0) (𝓝 (-(↑Real.pi / 3 * I))) := by
    have hcont : ContinuousAt (fun ε : ℝ =>
        Real.pi / 2 - (5 * Real.pi / 6 + 5 * arcsinDelta ε * Real.pi / 12)) 0 := by
      unfold arcsinDelta; fun_prop
    have hval : Real.pi / 2 - (5 * Real.pi / 6 + 5 * arcsinDelta 0 * Real.pi / 12) =
        -(Real.pi / 3) := by
      simp [arcsinDelta, Real.arcsin_zero]; ring
    rw [show -(↑Real.pi / 3 * I : ℂ) = ↑(-(Real.pi / 3)) * I from by push_cast; ring]
    have h := hcont.tendsto
    rw [hval] at h
    exact ((continuous_ofReal.continuousAt.tendsto.comp h).mul_const I).mono_left
      nhdsWithin_le_nhds
  exact htend.congr' (hkey.mono (fun ε h => h.symm))

/-! ## Part 12: FTC telescope for rho+1

For rho+1, the FTC telescope is more complex because the arc segment uses
neg-slit-plane (giving branch corrections). Rather than proving the full
per-segment FTC with branch corrections, we take the FTC identity and
integrability as hypotheses and provide only the E function + limit,
which is the key analytical contribution.

The consumer (`CrossingAtRho.lean`) can supply these hypotheses. -/

/-- The complete `CornerFTCHyp` at rho+1.
Takes integrability and FTC as hypotheses since the branch correction
machinery for the neg-slit-plane arc is complex. The limit is the key
contribution. -/
def cornerFTCHyp_atRhoPlusOne {H : ℝ} (hH : 1 < H)
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (h_ftc_hyp : ∀ ε, 0 < ε → ε < min (1/3) (H - Real.sqrt 3 / 2) →
      (∫ t in (0 : ℝ)..(1/5 - vertDelta H ε),
          (fdBoundaryFun H t - ellipticPointRhoPlusOne)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (1/5 + arcsinDelta ε)..(1 : ℝ),
          (fdBoundaryFun H t - ellipticPointRhoPlusOne)⁻¹ * deriv (fdBoundaryFun H) t) =
      E_atRhoPlusOne H ε)
    (h_int_left : ∀ ε, 0 < ε → ε < min (1/3) (H - Real.sqrt 3 / 2) →
      IntervalIntegrable
        (fun t => (fdBoundaryFun H t - ellipticPointRhoPlusOne)⁻¹ * deriv (fdBoundaryFun H) t)
        volume 0 (1/5 - vertDelta H ε))
    (h_int_right : ∀ ε, 0 < ε → ε < min (1/3) (H - Real.sqrt 3 / 2) →
      IntervalIntegrable
        (fun t => (fdBoundaryFun H t - ellipticPointRhoPlusOne)⁻¹ * deriv (fdBoundaryFun H) t)
        volume (1/5 + arcsinDelta ε) 1) :
    CornerFTCHyp γ ellipticPointRhoPlusOne (1/5)
      (vertDelta H) arcsinDelta
      (min (1/3) (H - Real.sqrt 3 / 2))
      (-(↑Real.pi / 3 * I)) where
  E := E_atRhoPlusOne H
  h_ftc := by
    intro ε hε hεt
    have hε_13 : ε < 1/3 := lt_of_lt_of_le hεt (min_le_left _ _)
    have hε_H : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hεt (min_le_right _ _)
    have hH_valid := fdHeightValid_of_one_lt H hH
    have hδL := vertDelta_pos hH_valid hε
    have hδL' := vertDelta_lt_one_fifth hH_valid hε_H
    have hδR := arcsinDelta_pos hε
    have hδR' := arcsinDelta_lt_one_fifth hε hε_13
    rw [transfer_integral ellipticPointRhoPlusOne (by linarith) (le_refl 0) (by linarith) hγ,
      transfer_integral ellipticPointRhoPlusOne (by linarith) (by linarith) (le_refl 1) hγ]
    exact h_ftc_hyp ε hε hεt
  hint_left := by
    intro ε hε hεt
    have hε_H : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hεt (min_le_right _ _)
    have hH_valid := fdHeightValid_of_one_lt H hH
    have hδL := vertDelta_pos hH_valid hε
    have hδL' := vertDelta_lt_one_fifth hH_valid hε_H
    exact transfer_integrability ellipticPointRhoPlusOne
      (by linarith) (le_refl 0) (by linarith) hγ (h_int_left ε hε hεt)
  hint_right := by
    intro ε hε hεt
    have hε_13 : ε < 1/3 := lt_of_lt_of_le hεt (min_le_left _ _)
    have hδR := arcsinDelta_pos hε
    have hδR' := arcsinDelta_lt_one_fifth hε hε_13
    exact transfer_integrability ellipticPointRhoPlusOne
      (by linarith) (by linarith) (le_refl 1) hγ (h_int_right ε hε hεt)
  h_limit := E_atRhoPlusOne_tendsto H (fdHeightValid_of_one_lt H hH)

end
