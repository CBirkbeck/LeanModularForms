/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ValenceFormula.WindingWeights.Common

/-!
# Winding Number Weight at i

PV integral computation and generalized winding number of `fdBoundary_H`
around the point i.

## Main Results

* `pv_integral_at_i_tendsto` — PV integral converges to -iπ
* `gWN_fdBoundary_H_at_i` — gWN = -1/2 at i
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

private lemma arg_approach_i_left (hδ : 0 < δ) (hδ_small : δ < 1) :
    (fdBoundary_H H (2 - δ) - I).arg = -(δ * Real.pi / 12) := by
  have h1 : 1 < 2 - δ := by linarith
  have h3 : 2 - δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3]
  set θ := Real.pi / 2 - δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 - δ)) / 6 = θ from by simp only [hθ_def]; ring]
  rw [show (↑θ : ℂ) * I = ↑θ * I from rfl, exp_real_angle_I]
  have h_cos : Real.cos θ = Real.sin (δ * Real.pi / 6) := by
    rw [hθ_def, Real.cos_pi_div_two_sub]
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by
    rw [hθ_def, Real.sin_pi_div_two_sub]
  have h_re_factor : Real.sin (δ * Real.pi / 6) =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (δ * Real.pi / 12) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.sin_two_mul]
  have h_im_factor : Real.cos (δ * Real.pi / 6) - 1 =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.sin (δ * Real.pi / 12)) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (δ * Real.pi / 12)]
  have h_sin_pos : 0 < Real.sin (δ * Real.pi / 12) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      ↑(2 * Real.sin (δ * Real.pi / 12)) *
        (↑(Real.cos (δ * Real.pi / 12)) + ↑(-(Real.sin (δ * Real.pi / 12))) * I) := by
    rw [h_cos, h_sin]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]; linarith [h_re_factor]
    · simp only [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, add_zero, mul_one, zero_add]; linarith [h_im_factor]
  rw [h_eq]
  have h_trig : (↑(Real.cos (δ * Real.pi / 12)) : ℂ) +
      ↑(-(Real.sin (δ * Real.pi / 12))) * I =
      Complex.cos ↑(-(δ * Real.pi / 12)) + Complex.sin ↑(-(δ * Real.pi / 12)) * I := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, ofReal_neg]
  rw [h_trig]
  exact Complex.arg_mul_cos_add_sin_mul_I
    (mul_pos (by norm_num : (0:ℝ) < 2) h_sin_pos)
    ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩

private lemma arg_approach_i_right (hδ : 0 < δ) (hδ_small : δ < 1) :
    (fdBoundary_H H (2 + δ) - I).arg = δ * Real.pi / 12 - Real.pi := by
  have h1 : 1 < 2 + δ := by linarith
  have h3 : 2 + δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3]
  set θ := Real.pi / 2 + δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 + δ)) / 6 = θ from by simp only [hθ_def]; ring]
  rw [show (↑θ : ℂ) * I = ↑θ * I from rfl, exp_real_angle_I]
  have h_cos : Real.cos θ = -Real.sin (δ * Real.pi / 6) := by
    rw [hθ_def, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by
    rw [hθ_def, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  have h_re_factor : -Real.sin (δ * Real.pi / 6) =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.cos (δ * Real.pi / 12)) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.sin_two_mul]
  have h_im_factor : Real.cos (δ * Real.pi / 6) - 1 =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.sin (δ * Real.pi / 12)) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (δ * Real.pi / 12)]
  have h_sin_pos : 0 < Real.sin (δ * Real.pi / 12) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  set w := (↑(Real.cos (δ * Real.pi / 12)) : ℂ) +
    ↑(Real.sin (δ * Real.pi / 12)) * I with hw_def
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      -(↑(2 * Real.sin (δ * Real.pi / 12)) * w) := by
    rw [h_cos, h_sin]
    apply Complex.ext
    · simp only [hw_def, add_re, sub_re, neg_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]; linarith [h_re_factor]
    · simp only [hw_def, add_im, sub_im, neg_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, add_zero, mul_one, zero_add]; linarith [h_im_factor]
  rw [h_eq]
  have hw_im_pos : 0 < w.im := by
    simp only [hw_def, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      mul_zero, add_zero, mul_one]
    linarith
  have hw_arg : w.arg = δ * Real.pi / 12 := by
    have hw_eq : w = ↑(1:ℝ) * (Complex.cos ↑(δ * Real.pi / 12) +
        Complex.sin ↑(δ * Real.pi / 12) * I) := by
      simp only [hw_def, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Complex.ofReal_one, one_mul]
    rw [hw_eq]
    exact Complex.arg_mul_cos_add_sin_mul_I (by norm_num : (0:ℝ) < 1)
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hrw_im_pos : 0 < (↑(2 * Real.sin (δ * Real.pi / 12)) * w).im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    simp only [zero_mul, add_zero]
    exact mul_pos (mul_pos (by norm_num) h_sin_pos) hw_im_pos
  rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hrw_im_pos,
      Complex.arg_real_mul w (mul_pos (by norm_num : (0:ℝ) < 2) h_sin_pos),
      hw_arg]

private lemma g_i_norm_left {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ‖fdBoundary_H H (2 - δ) - I‖ = 2 * Real.sin (δ * Real.pi / 12) := by
  have h1 : 1 < 2 - δ := by linarith
  have h3 : 2 - δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3, exp_real_angle_I]
  set θ := Real.pi / 2 - δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 - δ)) / 6 = θ from by simp only [hθ_def]; ring]
  have h_cos : Real.cos θ = Real.sin (δ * Real.pi / 6) := by
    rw [hθ_def, Real.cos_pi_div_two_sub]
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by
    rw [hθ_def, Real.sin_pi_div_two_sub]
  have h_re_factor : Real.sin (δ * Real.pi / 6) =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (δ * Real.pi / 12) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.sin_two_mul]
  have h_im_factor : Real.cos (δ * Real.pi / 6) - 1 =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.sin (δ * Real.pi / 12)) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (δ * Real.pi / 12)]
  have h_sin_pos : 0 < Real.sin (δ * Real.pi / 12) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      (2 * Real.sin (δ * Real.pi / 12)) • Complex.exp (↑(-(δ * Real.pi / 12)) * I) := by
    rw [Complex.real_smul, exp_real_angle_I, Real.cos_neg, Real.sin_neg, h_cos, h_sin]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]; linarith [h_re_factor]
    · simp only [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, add_zero, mul_one, zero_add]; linarith [h_im_factor]
  rw [h_eq, norm_smul, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_of_nonneg (by linarith)]

private lemma g_i_norm_right {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ‖fdBoundary_H H (2 + δ) - I‖ = 2 * Real.sin (δ * Real.pi / 12) := by
  have h1 : 1 < 2 + δ := by linarith
  have h3 : 2 + δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3, exp_real_angle_I]
  set θ := Real.pi / 2 + δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 + δ)) / 6 = θ from by simp only [hθ_def]; ring]
  have h_cos : Real.cos θ = -Real.sin (δ * Real.pi / 6) := by
    rw [hθ_def, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by
    rw [hθ_def, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  have h_re_factor : -Real.sin (δ * Real.pi / 6) =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.cos (δ * Real.pi / 12)) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.sin_two_mul]
  have h_im_factor : Real.cos (δ * Real.pi / 6) - 1 =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.sin (δ * Real.pi / 12)) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (δ * Real.pi / 12)]
  have h_sin_pos : 0 < Real.sin (δ * Real.pi / 12) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      (-(2 * Real.sin (δ * Real.pi / 12))) • Complex.exp (↑(δ * Real.pi / 12) * I) := by
    rw [Complex.real_smul, exp_real_angle_I, h_cos, h_sin]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]; linarith [h_re_factor]
    · simp only [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, add_zero, mul_one, zero_add]; linarith [h_im_factor]
  rw [h_eq, norm_smul, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by linarith)]

private lemma g_i_norm_ge_seg0 {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 / 2 ≤ ‖fdBoundary_H H t - I‖ := by
  have hre : (fdBoundary_H H t - I).re = 1 / 2 := by
    rw [fdBoundary_H_seg0 H ht1]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.div_ofNat_re,
      mul_zero, sub_zero, zero_mul, mul_one]
    norm_num
  calc (1 : ℝ) / 2 = |1 / 2| := (abs_of_pos (by norm_num)).symm
    _ = |(fdBoundary_H H t - I).re| := by rw [hre]
    _ ≤ ‖fdBoundary_H H t - I‖ := Complex.abs_re_le_norm _

private lemma g_i_norm_ge_seg4 (H : ℝ) (hH : 1 < H)
    {t : ℝ} (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    H - 1 ≤ ‖fdBoundary_H H t - I‖ := by
  have him : (fdBoundary_H H t - I).im = H - 1 := by
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · rw [fdBoundary_H_at_four H]
      simp only [Complex.neg_im, Complex.div_ofNat_im, Complex.one_im, Complex.add_im,
        Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_im,
        Complex.ofReal_re]
      ring
    · rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) (by linarith)]
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.div_ofNat_im, Complex.im_ofNat]
      ring
  calc H - 1 = |H - 1| := (abs_of_pos (by linarith)).symm
    _ = |(fdBoundary_H H t - I).im| := by rw [him]
    _ ≤ ‖fdBoundary_H H t - I‖ := Complex.abs_im_le_norm _

private lemma g_i_slitPlane_left {t : ℝ} (_ht0 : 0 ≤ t) (ht2 : t < 2) :
    fdBoundary_H H t - I ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  rcases le_or_gt t 1 with ht1 | ht1
  · rw [fdBoundary_H_seg0 H ht1]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.div_ofNat_re,
      mul_zero, sub_zero, zero_mul, mul_one]
    norm_num
  · rw [fdBoundary_H_seg1 H (by linarith) (by linarith)]
    set θ := Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3) with hθ_def
    rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      (↑θ : ℂ) * I from by simp only [hθ_def]; push_cast; ring, exp_real_angle_I]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero,
      mul_one]
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · simp only [hθ_def]; nlinarith [Real.pi_pos]
    · simp only [hθ_def]; nlinarith [Real.pi_pos]

private lemma g_i_seg3_value {t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) :
    fdBoundary_H H t - I =
      -1/2 + ↑(Real.sqrt 3 / 2 - 1 + (t - 3) * (H - Real.sqrt 3 / 2)) * I := by
  rw [fdBoundary_H_seg3 H (by linarith) (by linarith) (by linarith) ht4]
  push_cast; ring

private lemma g_i_seg4_value {t : ℝ} (ht4 : 4 < t) :
    fdBoundary_H H t - I = ↑(t - 9/2) + ↑(H - 1) * I := by
  rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) (by linarith)]
  push_cast; ring

private lemma g_i_norm_ge_seg3 {t : ℝ} (ht3 : 3 ≤ t) (ht4 : t ≤ 4) :
    1 / 2 ≤ ‖fdBoundary_H H t - I‖ := by
  have hre : (fdBoundary_H H t - I).re = -1 / 2 := by
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · rw [fdBoundary_H_at_three_eq_rho]
      simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk_subtype,
        Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.div_ofNat_re,
        Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero]
      norm_num
    · rw [g_i_seg3_value ht3' ht4]
      simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, add_zero, zero_mul]
  calc 1 / 2 = |(-1:ℝ) / 2| := by norm_num
    _ = |(fdBoundary_H H t - I).re| := by rw [hre]
    _ ≤ ‖fdBoundary_H H t - I‖ := Complex.abs_re_le_norm _

private lemma g_i_slitPlane_arc_right {t : ℝ} (ht2 : 2 < t) (ht3 : t ≤ 3) :
    fdBoundary_H H t - I ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  rcases eq_or_lt_of_le ht3 with rfl | ht3'
  · rw [fdBoundary_H_at_three_eq_rho]
    simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk_subtype,
      Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.div_ofNat_im, Complex.div_ofNat_re,
      Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_div]
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num), sq_nonneg (2 - Real.sqrt 3)]
  · rw [fdBoundary_H_eq_arc (by linarith) ht3', exp_real_angle_I]
    simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_add]
    have hθ_bound : Real.pi / 2 < Real.pi * (1 + t) / 6 := by nlinarith [Real.pi_pos]
    have hθ_bound2 : Real.pi * (1 + t) / 6 < Real.pi + Real.pi / 2 := by nlinarith [Real.pi_pos]
    have h_cos_neg := Real.cos_neg_of_pi_div_two_lt_of_lt hθ_bound hθ_bound2
    have h_sin_lt : Real.sin (Real.pi * (1 + t) / 6) < 1 := by
      by_contra h_ge; push_neg at h_ge
      have h_eq := le_antisymm (Real.sin_le_one _) h_ge
      have : Real.cos (Real.pi * (1 + t) / 6) = 0 := by
        nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t) / 6)]
      linarith
    linarith

private lemma g_i_norm_arc_right {t : ℝ} (ht2 : 2 < t) (ht3 : t < 3) :
    ‖fdBoundary_H H t - I‖ = 2 * Real.sin ((t - 2) * Real.pi / 12) := by
  have h := g_i_norm_right (H := H) (δ := t - 2) (by linarith) (by linarith)
  rwa [show 2 + (t - 2) = t from by ring] at h

private lemma g_i_norm_arc_left {t : ℝ} (ht1 : 1 < t) (ht2 : t < 2) :
    ‖fdBoundary_H H t - I‖ = 2 * Real.sin ((2 - t) * Real.pi / 12) := by
  have h := g_i_norm_left (H := H) (δ := 2 - t) (by linarith) (by linarith)
  rwa [show 2 - (2 - t) = t from by ring] at h

private noncomputable def t₀_i (H : ℝ) : ℝ :=
  3 + (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2)

private lemma t₀_i_gt_three (hH : 1 < H) : 3 < t₀_i H := by
  unfold t₀_i
  have h_num_pos : 0 < 1 - Real.sqrt 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
              sq_nonneg (2 - Real.sqrt 3)]
  have h_den_pos : 0 < H - Real.sqrt 3 / 2 := by nlinarith
  linarith [div_pos h_num_pos h_den_pos]

private lemma t₀_i_lt_four (hH : 1 < H) : t₀_i H < 4 := by
  unfold t₀_i
  have h_den_pos : 0 < H - Real.sqrt 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
              sq_nonneg (2 - Real.sqrt 3)]
  rw [show (4:ℝ) = 3 + 1 from by ring]
  have : (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) < 1 := by
    rw [div_lt_one h_den_pos]; linarith
  linarith

private lemma g_i_at_t₀ (hH : 1 < H) :
    fdBoundary_H H (t₀_i H) - I = -1/2 := by
  have ht₀3 := t₀_i_gt_three hH
  have ht₀4 := t₀_i_lt_four hH
  rw [g_i_seg3_value (by linarith) (by linarith)]
  have h_den_pos : 0 < H - Real.sqrt 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
              sq_nonneg (2 - Real.sqrt 3)]
  have h_im_zero : Real.sqrt 3 / 2 - 1 + (t₀_i H - 3) * (H - Real.sqrt 3 / 2) = 0 := by
    unfold t₀_i
    rw [show 3 + (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) - 3 =
      (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) from by ring]
    rw [div_mul_cancel₀ _ (ne_of_gt h_den_pos)]; ring
  rw [h_im_zero]; simp

private lemma g_i_seg3_im_neg {t : ℝ} (ht3 : 3 < t) (ht_t0 : t < t₀_i H)
    (hH : 1 < H) : (fdBoundary_H H t - I).im < 0 := by
  rw [g_i_seg3_value ht3 (by linarith [t₀_i_lt_four hH])]
  simp only [Complex.add_im, Complex.neg_im, Complex.div_ofNat_im, Complex.one_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, add_zero, mul_one]
  norm_num
  have h_den_pos : 0 < H - Real.sqrt 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
              sq_nonneg (2 - Real.sqrt 3)]
  have h_eq_zero : Real.sqrt 3 / 2 - 1 + (t₀_i H - 3) * (H - Real.sqrt 3 / 2) = 0 := by
    unfold t₀_i
    rw [show 3 + (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) - 3 =
      (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) from by ring]
    rw [div_mul_cancel₀ _ (ne_of_gt h_den_pos)]; ring
  nlinarith

private lemma g_i_seg3_im_pos {t : ℝ} (ht_t0 : t₀_i H < t) (ht4 : t ≤ 4)
    (hH : 1 < H) : 0 < (fdBoundary_H H t - I).im := by
  rw [g_i_seg3_value (by linarith [t₀_i_gt_three hH]) ht4]
  simp only [Complex.add_im, Complex.neg_im, Complex.div_ofNat_im, Complex.one_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, add_zero, mul_one]
  norm_num
  have h_den_pos : 0 < H - Real.sqrt 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
              sq_nonneg (2 - Real.sqrt 3)]
  have h_eq_zero : Real.sqrt 3 / 2 - 1 + (t₀_i H - 3) * (H - Real.sqrt 3 / 2) = 0 := by
    unfold t₀_i
    rw [show 3 + (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) - 3 =
      (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) from by ring]
    rw [div_mul_cancel₀ _ (ne_of_gt h_den_pos)]; ring
  nlinarith

private lemma g_i_ne_zero_seg3 {t : ℝ} (ht3 : 3 ≤ t) (ht4 : t ≤ 4) :
    fdBoundary_H H t - I ≠ 0 := by
  intro h; have := congr_arg Complex.re h
  simp only [Complex.zero_re] at this
  rcases eq_or_lt_of_le ht3 with rfl | ht3'
  · rw [fdBoundary_H_at_three_eq_rho] at this
    simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk_subtype,
      Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.div_ofNat_re,
      Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero] at this
    norm_num at this
  · rw [g_i_seg3_value ht3' ht4] at this
    simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, add_zero, zero_mul] at this
    norm_num at this

private lemma log_neg_eq_add_pi_I {z : ℂ} (_hz_ne : z ≠ 0) (hz_im : z.im < 0) :
    Complex.log (-z) = Complex.log z + ↑Real.pi * I := by
  show ↑(Real.log ‖-z‖) + ↑((-z).arg) * I =
    ↑(Real.log ‖z‖) + ↑z.arg * I + ↑Real.pi * I
  simp only [norm_neg]
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hz_im]
  push_cast; ring

set_option maxHeartbeats 16000000 in
private lemma ftc_logDeriv_telescope_i (H : ℝ) (hH : 1 < H)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let g := fun t => fdBoundary_H H t - I
    IntervalIntegrable (fun t => deriv g t / g t) volume 0 (2 - δ) ∧
    IntervalIntegrable (fun t => deriv g t / g t) volume (2 + δ) 5 ∧
    ((∫ t in (0:ℝ)..(2 - δ), deriv g t / g t) +
    (∫ t in (2 + δ)..(5:ℝ), deriv g t / g t) =
    Complex.log (g (2 - δ)) - Complex.log (g (2 + δ)) - 2 * ↑Real.pi * I) := by
  intro g
  have hH_sqrt : Real.sqrt 3 / 2 < H := by
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
              sq_nonneg (2 - Real.sqrt 3)]
  set t₀ := t₀_i H with ht₀_def
  have ht₀3 := t₀_i_gt_three hH
  have ht₀4 := t₀_i_lt_four hH
  set h₀ : ℝ → ℂ := fun t => 1/2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2) - 1) * I
  set h₁ : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - I
  set h₂ : ℝ → ℂ :=
    fun t => -1/2 + ↑(Real.sqrt 3 / 2 - 1 + (t - 3) * (H - Real.sqrt 3 / 2)) * I
  set h₃ : ℝ → ℂ := fun t => ↑(t - 9/2) + ↑(H - 1) * I
  have hg_eq_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := by
    intro t ht; show fdBoundary_H H t - I = h₀ t
    rw [fdBoundary_H_seg0 H ht]; simp only [h₀]; ring
  have hg_eq_h₁ : ∀ t, 1 < t → t < 3 → g t = h₁ t := by
    intro t ht1 ht3; show fdBoundary_H H t - I = h₁ t
    rw [fdBoundary_H_eq_arc ht1 ht3]
  have hg_eq_h₂ : ∀ t, 3 < t → t ≤ 4 → g t = h₂ t := by
    intro t ht3 ht4; exact g_i_seg3_value ht3 ht4
  have hg_eq_h₃ : ∀ t, 4 < t → g t = h₃ t := by
    intro t ht4; exact g_i_seg4_value ht4
  have hg0 : g 0 = h₀ 0 := hg_eq_h₀ 0 (by norm_num)
  have hg1_0 : g 1 = h₀ 1 := hg_eq_h₀ 1 (le_refl 1)
  have hg1_1 : g 1 = h₁ 1 := by
    show fdBoundary_H H 1 - I = h₁ 1
    rw [fdBoundary_H_at_one_eq_rho_plus_one]
    simp only [h₁, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      UpperHalfPlane.coe_mk_subtype]
    rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
        show (↑(Real.pi / 3) : ℂ) * I = ↑(Real.pi / 3) * I from rfl,
        exp_real_angle_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  have hg2mδ : g (2 - δ) = h₁ (2 - δ) := hg_eq_h₁ (2 - δ) (by linarith) (by linarith)
  have hg2pδ : g (2 + δ) = h₁ (2 + δ) := hg_eq_h₁ (2 + δ) (by linarith) (by linarith)
  have hg3_1 : g 3 = h₁ 3 := by
    show fdBoundary_H H 3 - I = h₁ 3
    rw [fdBoundary_H_at_three_eq_rho]
    simp only [h₁, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk_subtype]
    rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 from by ring]
    rw [show (↑(2 * Real.pi / 3) : ℂ) * I = ↑(2 * Real.pi / 3) * I from rfl,
        exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
    push_cast; ring
  have hg3_2 : g 3 = h₂ 3 := by
    show fdBoundary_H H 3 - I = h₂ 3
    rw [fdBoundary_H_at_three_eq_rho]
    simp only [h₂, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk_subtype]
    push_cast; ring
  have hgt₀_2 : g t₀ = h₂ t₀ := hg_eq_h₂ t₀ ht₀3 (le_of_lt ht₀4)
  have hgt₀_val : g t₀ = (-1 : ℂ) / 2 := g_i_at_t₀ hH
  have hg4_2 : g 4 = h₂ 4 := hg_eq_h₂ 4 (by linarith) (le_refl 4)
  have hg4_3 : g 4 = h₃ 4 := by
    show fdBoundary_H H 4 - I = h₃ 4
    rw [fdBoundary_H_at_four H]; simp only [h₃]; push_cast; ring
  have hg5 : g 5 = h₃ 5 := hg_eq_h₃ 5 (by norm_num)
  have hd_h₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
    intro t; simp only [h₀]
    have ht := (hasDerivAt_id t).ofReal_comp.mul_const (↑H - ↑(Real.sqrt 3) / 2 : ℂ)
    have hinner := ((hasDerivAt_const t (↑H : ℂ)).sub ht).sub (hasDerivAt_const t (1:ℂ))
    exact ((hasDerivAt_const t ((1:ℂ)/2)).add (hinner.mul_const I)).congr_deriv
      (by push_cast; ring)
  have hd_h₁ : ∀ t : ℝ, HasDerivAt h₁
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t := by
    intro t
    have hf : HasDerivAt (fun s : ℝ => Real.pi * (1 + s) / 6) (Real.pi / 6) t :=
      ((hasDerivAt_id t).add_const (1:ℝ) |>.const_mul (Real.pi / 6)).congr_of_eventuallyEq
        (Eventually.of_forall fun s => show _ from by simp [id]; ring)
        |>.congr_deriv (by ring)
    have hci : HasDerivAt (fun s : ℝ => (↑(Real.pi * (1 + s) / 6) : ℂ) * I)
        ((↑(Real.pi / 6) : ℂ) * I) t :=
      (hf.ofReal_comp.mul_const I).congr_deriv (by norm_num [smul_eq_mul])
    exact (hci.cexp.sub (hasDerivAt_const t I)).congr_deriv (by simp only [sub_zero]; ring)
  have hd_h₂ : ∀ t : ℝ, HasDerivAt h₂ ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
    intro t; simp only [h₂]
    have hf : HasDerivAt (fun s : ℝ => Real.sqrt 3 / 2 - 1 + (s - 3) * (H - Real.sqrt 3 / 2))
        (H - Real.sqrt 3 / 2) t :=
      ((hasDerivAt_id t).sub_const (3:ℝ) |>.mul_const (H - Real.sqrt 3 / 2)
        |>.add_const (Real.sqrt 3 / 2 - 1)).congr_of_eventuallyEq
        (Eventually.of_forall fun s => show _ from by simp [id]; ring)
        |>.congr_deriv (by ring)
    exact ((hasDerivAt_const t ((-1:ℂ)/2)).add
      (hf.ofReal_comp.mul_const I)).congr_deriv (by push_cast; ring)
  have hd_h₃ : ∀ t : ℝ, HasDerivAt h₃ 1 t := by
    intro t
    show HasDerivAt (fun s => ↑(s - 9/2) + ↑(H - 1) * I) (1 : ℂ) t
    have h1 : HasDerivAt (fun s : ℝ => s - 9/2) (1 : ℝ) t := by
      have := (hasDerivAt_id t).sub (hasDerivAt_const t (9/2:ℝ))
      convert this using 1
      ring
    have h2 := h1.ofReal_comp.add (hasDerivAt_const t (↑(H - 1) * I))
    exact h2.congr_deriv (by simp)
  have heq_01 : ∀ t ∈ Ioo (0:ℝ) 1, g t = h₀ t ∧ deriv g t = deriv h₀ t := by
    intro t ⟨_, ht1⟩
    refine ⟨hg_eq_h₀ t (le_of_lt ht1), ?_⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Iio_mem_nhds ht1)
      (fun s hs => hg_eq_h₀ s (le_of_lt hs)))
  have heq_1_2mδ : ∀ t ∈ Ioo (1:ℝ) (2 - δ), g t = h₁ t ∧ deriv g t = deriv h₁ t := by
    intro t ⟨ht1, ht2⟩
    refine ⟨hg_eq_h₁ t ht1 (by linarith), ?_⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds ht1 (show t < 3 by linarith))
      (fun s hs => hg_eq_h₁ s hs.1 hs.2))
  have heq_2pδ_3 : ∀ t ∈ Ioo (2 + δ) (3:ℝ), g t = h₁ t ∧ deriv g t = deriv h₁ t := by
    intro t ⟨ht2, ht3⟩
    refine ⟨hg_eq_h₁ t (by linarith) ht3, ?_⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds (show 1 < t by linarith) ht3)
      (fun s hs => hg_eq_h₁ s hs.1 hs.2))
  have heq_3_t₀ : ∀ t ∈ Ioo (3:ℝ) t₀, g t = h₂ t ∧ deriv g t = deriv h₂ t := by
    intro t ⟨ht3, ht_t0⟩
    refine ⟨hg_eq_h₂ t ht3 (by linarith), ?_⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds ht3 (show t < 4 by linarith))
      (fun s hs => hg_eq_h₂ s hs.1 (le_of_lt hs.2)))
  have heq_t₀_4 : ∀ t ∈ Ioo t₀ (4:ℝ), g t = h₂ t ∧ deriv g t = deriv h₂ t := by
    intro t ⟨ht_t0, ht4⟩
    refine ⟨hg_eq_h₂ t (by linarith) (le_of_lt ht4), ?_⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds (show 3 < t by linarith) ht4)
      (fun s hs => hg_eq_h₂ s hs.1 (le_of_lt hs.2)))
  have heq_45 : ∀ t ∈ Ioo (4:ℝ) 5, g t = h₃ t ∧ deriv g t = deriv h₃ t := by
    intro t ⟨ht4, _⟩
    refine ⟨hg_eq_h₃ t ht4, ?_⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioi_mem_nhds ht4) (fun s hs => hg_eq_h₃ s hs))
  have hh₀_cont : ContinuousOn h₀ (Icc 0 1) :=
    fun t _ => (hd_h₀ t).continuousAt.continuousWithinAt
  have hh₁_cont_12 : ContinuousOn h₁ (Icc 1 (2 - δ)) :=
    fun t _ => (hd_h₁ t).continuousAt.continuousWithinAt
  have hh₁_cont_23 : ContinuousOn h₁ (Icc (2 + δ) 3) :=
    fun t _ => (hd_h₁ t).continuousAt.continuousWithinAt
  have hh₂_cont_3t₀ : ContinuousOn h₂ (Icc 3 t₀) :=
    fun t _ => (hd_h₂ t).continuousAt.continuousWithinAt
  have hh₂_cont_t₀4 : ContinuousOn h₂ (Icc t₀ 4) :=
    fun t _ => (hd_h₂ t).continuousAt.continuousWithinAt
  have hh₃_cont : ContinuousOn h₃ (Icc 4 5) :=
    fun t _ => (hd_h₃ t).continuousAt.continuousWithinAt
  have hh₀_diff : ∀ t ∈ Ioo (0:ℝ) 1, DifferentiableAt ℝ h₀ t :=
    fun t _ => (hd_h₀ t).differentiableAt
  have hh₁_diff_12 : ∀ t ∈ Ioo (1:ℝ) (2 - δ), DifferentiableAt ℝ h₁ t :=
    fun t _ => (hd_h₁ t).differentiableAt
  have hh₁_diff_23 : ∀ t ∈ Ioo (2 + δ) (3:ℝ), DifferentiableAt ℝ h₁ t :=
    fun t _ => (hd_h₁ t).differentiableAt
  have hh₂_diff_3t₀ : ∀ t ∈ Ioo (3:ℝ) t₀, DifferentiableAt ℝ h₂ t :=
    fun t _ => (hd_h₂ t).differentiableAt
  have hh₂_diff_t₀4 : ∀ t ∈ Ioo t₀ (4:ℝ), DifferentiableAt ℝ h₂ t :=
    fun t _ => (hd_h₂ t).differentiableAt
  have hh₃_diff : ∀ t ∈ Ioo (4:ℝ) 5, DifferentiableAt ℝ h₃ t :=
    fun t _ => (hd_h₃ t).differentiableAt
  have hh₀_deriv_cont : ContinuousOn (deriv h₀) (Icc 0 1) := by
    rw [show deriv h₀ = fun _ => -(↑(H - Real.sqrt 3 / 2) : ℂ) * I from
      funext fun t => (hd_h₀ t).deriv]; exact continuousOn_const
  have hh₁_deriv_cont : ∀ (a b : ℝ), ContinuousOn (deriv h₁) (Icc a b) := by
    intro a b
    rw [show deriv h₁ = fun t => ↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I) from
      funext fun t => (hd_h₁ t).deriv]
    exact (Continuous.mul continuous_const (Continuous.cexp (Continuous.mul
      (continuous_ofReal.comp (by fun_prop : Continuous fun s => Real.pi * (1 + s) / 6))
      continuous_const))).continuousOn
  have hh₂_deriv_cont : ∀ (a b : ℝ), ContinuousOn (deriv h₂) (Icc a b) := by
    intro a b
    rw [show deriv h₂ = fun _ => (↑(H - Real.sqrt 3 / 2) : ℂ) * I from
      funext fun t => (hd_h₂ t).deriv]; exact continuousOn_const
  have hh₃_deriv_cont : ContinuousOn (deriv h₃) (Icc 4 5) := by
    rw [show deriv h₃ = fun _ => (1 : ℂ) from
      funext fun t => (hd_h₃ t).deriv]; exact continuousOn_const
  have hh₀_slit : ∀ t ∈ Icc (0:ℝ) 1, h₀ t ∈ slitPlane := by
    intro t ⟨ht0, ht1⟩; rw [← hg_eq_h₀ t ht1]
    exact g_i_slitPlane_left ht0 (by linarith)
  have piece₀ := ftc_log_piece (by norm_num : (0:ℝ) ≤ 1) hh₀_cont hh₀_diff
    hh₀_deriv_cont hh₀_slit heq_01 hg0 hg1_0
  have hh₁_slit_12 : ∀ t ∈ Icc (1:ℝ) (2 - δ), h₁ t ∈ slitPlane := by
    intro t ⟨ht1, ht2⟩
    rcases eq_or_lt_of_le ht1 with rfl | ht1'
    · rw [← hg1_1]; exact g_i_slitPlane_left (by norm_num) (by linarith)
    · rw [← hg_eq_h₁ t ht1' (by linarith)]
      exact g_i_slitPlane_left (by linarith) (by linarith)
  have piece₁ := ftc_log_piece (by linarith : (1:ℝ) ≤ 2 - δ) hh₁_cont_12 hh₁_diff_12
    (hh₁_deriv_cont 1 (2-δ)) hh₁_slit_12 heq_1_2mδ hg1_1 hg2mδ
  have hh₁_slit_23 : ∀ t ∈ Icc (2 + δ) (3:ℝ), h₁ t ∈ slitPlane := by
    intro t ⟨ht2, ht3⟩
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · rw [← hg3_1]; exact g_i_slitPlane_arc_right (by linarith) (le_refl 3)
    · rw [← hg_eq_h₁ t (by linarith) ht3']
      exact g_i_slitPlane_arc_right (by linarith) (le_of_lt ht3')
  have piece₂ := ftc_log_piece (by linarith : (2 + δ) ≤ 3) hh₁_cont_23 hh₁_diff_23
    (hh₁_deriv_cont (2+δ) 3) hh₁_slit_23 heq_2pδ_3 hg2pδ hg3_1
  have hh₂_im_np_3t₀ : ∀ t ∈ Icc (3:ℝ) t₀, (h₂ t).im ≤ 0 := by
    intro t ⟨ht3, ht_t0⟩
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · show (h₂ 3).im ≤ 0
      simp only [h₂, Complex.add_im, Complex.neg_im, Complex.div_ofNat_im,
        Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one]
      nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
                sq_nonneg (2 - Real.sqrt 3)]
    · rcases eq_or_lt_of_le ht_t0 with rfl | ht_t0'
      · show (h₂ t₀).im ≤ 0
        rw [← hg_eq_h₂ t₀ (by linarith [t₀_i_gt_three hH])
              (by linarith [t₀_i_lt_four hH]),
          hgt₀_val]
        simp
      · show (h₂ t).im ≤ 0
        rw [← hg_eq_h₂ t ht3' (by linarith)]
        exact le_of_lt (g_i_seg3_im_neg ht3' ht_t0' hH)
  have hh₂_ne_3t₀ : ∀ t ∈ Icc (3:ℝ) t₀, h₂ t ≠ 0 := by
    intro t ⟨ht3, ht_t0⟩
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · rw [← hg3_2]; exact g_i_ne_zero_seg3 (le_refl 3) (by linarith)
    · rw [← hg_eq_h₂ t ht3' (by linarith)]
      exact g_i_ne_zero_seg3 (by linarith) (by linarith)
  have hh₂_im_neg_int_3t₀ : ∀ t ∈ Ioo (3:ℝ) t₀, (h₂ t).im < 0 := by
    intro t ⟨ht3, ht_t0⟩
    rw [← hg_eq_h₂ t ht3 (by linarith)]
    exact g_i_seg3_im_neg ht3 ht_t0 hH
  have piece₃ := ftc_log_piece_lower (by linarith : (3:ℝ) ≤ t₀)
    hh₂_cont_3t₀ hh₂_diff_3t₀ (hh₂_deriv_cont 3 t₀) hh₂_im_np_3t₀ hh₂_ne_3t₀
    hh₂_im_neg_int_3t₀ heq_3_t₀ hg3_2 hgt₀_2
  have hh₂_im_nn_t₀4 : ∀ t ∈ Icc t₀ (4:ℝ), 0 ≤ (h₂ t).im := by
    intro t ⟨ht_t0, ht4⟩
    rcases eq_or_lt_of_le ht_t0 with rfl | ht_t0'
    · rw [← hgt₀_2, hgt₀_val]; simp
    · rw [← hg_eq_h₂ t (by linarith) ht4]
      exact le_of_lt (g_i_seg3_im_pos ht_t0' ht4 hH)
  have hh₂_ne_t₀4 : ∀ t ∈ Icc t₀ (4:ℝ), h₂ t ≠ 0 := by
    intro t ⟨ht_t0, ht4⟩
    rcases eq_or_lt_of_le ht_t0 with rfl | ht_t0'
    · rw [← hgt₀_2]; exact g_i_ne_zero_seg3 (by linarith) (by linarith)
    · rw [← hg_eq_h₂ t (by linarith) ht4]
      exact g_i_ne_zero_seg3 (by linarith) ht4
  have hh₂_slit_int_t₀4 : ∀ t ∈ Ioo t₀ (4:ℝ), h₂ t ∈ slitPlane := by
    intro t ⟨ht_t0, ht4⟩
    rw [← hg_eq_h₂ t (by linarith) (le_of_lt ht4)]
    rw [Complex.mem_slitPlane_iff]; right
    exact ne_of_gt (g_i_seg3_im_pos ht_t0 (le_of_lt ht4) hH)
  have piece₄ := ftc_log_piece_upper (by linarith : t₀ ≤ 4)
    hh₂_cont_t₀4 hh₂_diff_t₀4 (hh₂_deriv_cont t₀ 4)
    hh₂_im_nn_t₀4 hh₂_ne_t₀4 hh₂_slit_int_t₀4 heq_t₀_4 hgt₀_2 hg4_2
  have hh₃_slit : ∀ t ∈ Icc (4:ℝ) 5, h₃ t ∈ slitPlane := by
    intro t ⟨ht4, ht5⟩
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · rw [Complex.mem_slitPlane_iff]; right
      simp only [h₃, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
      linarith
    · rw [show h₃ t = g t from (hg_eq_h₃ t ht4').symm, Complex.mem_slitPlane_iff]; right
      show (g t).im ≠ 0
      simp only [show g t = h₃ t from hg_eq_h₃ t ht4', h₃, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
      linarith
  have piece₅ := ftc_log_piece (by norm_num : (4:ℝ) ≤ 5) hh₃_cont hh₃_diff
    hh₃_deriv_cont hh₃_slit heq_45 hg4_3 hg5
  have hint_left : IntervalIntegrable (fun t => deriv g t / g t) volume 0 (2 - δ) :=
    piece₀.1.trans piece₁.1
  have hint_right : IntervalIntegrable (fun t => deriv g t / g t) volume (2 + δ) 5 :=
    piece₂.1.trans (piece₃.1.trans (piece₄.1.trans piece₅.1))
  refine ⟨hint_left, hint_right, ?_⟩
  rw [(intervalIntegral.integral_add_adjacent_intervals piece₀.1 piece₁.1).symm,
    (intervalIntegral.integral_add_adjacent_intervals piece₂.1
      (piece₃.1.trans (piece₄.1.trans piece₅.1))).symm,
    (intervalIntegral.integral_add_adjacent_intervals piece₃.1
      (piece₄.1.trans piece₅.1)).symm,
    (intervalIntegral.integral_add_adjacent_intervals piece₄.1 piece₅.1).symm,
    piece₀.2, piece₁.2, piece₂.2, piece₃.2, piece₄.2, piece₅.2]
  have hg3_im_neg : (g 3).im < 0 := by
    rw [hg3_2]; simp only [h₂, Complex.add_im, Complex.neg_im, Complex.div_ofNat_im,
      Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one]
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
              sq_nonneg (2 - Real.sqrt 3)]
  have hg3_ne : g 3 ≠ 0 := g_i_ne_zero_seg3 (le_refl 3) (by norm_num)
  have h_branch_3 : Complex.log (-(g 3)) = Complex.log (g 3) + ↑Real.pi * I :=
    log_neg_eq_add_pi_I hg3_ne hg3_im_neg
  have h_branch_t₀ : Complex.log (-(g t₀)) - Complex.log (g t₀) = -(↑Real.pi * I) := by
    rw [hgt₀_val]
    have h1 : -(-1 / 2 : ℂ) = (1 / 2 : ℂ) := by ring
    rw [h1]
    have hm : (-1:ℂ) / 2 = ↑((1:ℝ)/2) * (-1:ℂ) := by push_cast; ring
    rw [hm, Complex.log_ofReal_mul (by norm_num : (0:ℝ) < 1/2) (by norm_num : (-1:ℂ) ≠ 0),
        Complex.log_neg_one]
    rw [show (1:ℂ)/2 = ↑((1:ℝ)/2) from by push_cast; ring,
        ← Complex.ofReal_log (show (0:ℝ) ≤ 1/2 from by norm_num)]
    ring
  have hg_closed : g 0 = g 5 := by
    show fdBoundary_H H 0 - I = fdBoundary_H H 5 - I; rw [fdBoundary_H_closed H]
  have h_branch_t₀' : Complex.log (-(g t₀)) = Complex.log (g t₀) - ↑Real.pi * I := by
    linear_combination h_branch_t₀
  rw [hg_closed, h_branch_3, h_branch_t₀']; ring

set_option maxHeartbeats 16000000 in
/-- The PV integral of `(γ-I)⁻¹ γ'` over `[0,5]` with ε-ball cutoff tends to `-iπ`. -/
theorem pv_integral_at_i_tendsto (H : ℝ) (hH : 1 < H) :
    Tendsto (fun ε => ∫ t in (0:ℝ)..5, if ‖fdBoundary_H H t - I‖ > ε
      then (fdBoundary_H H t - I)⁻¹ *
           deriv (fun s => fdBoundary_H H s - I) t
      else 0)
      (𝓝[>] 0) (𝓝 (-(I * ↑Real.pi))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro r hr
  set ε₀ := min (min (min (1/2) (H - 1)) (2 * Real.sin (Real.pi / 12))) (r / 2) with hε₀_def
  have hH1_pos : 0 < H - 1 := by linarith
  have hsin_pos : 0 < Real.sin (Real.pi / 12) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have h2sin_pos : 0 < 2 * Real.sin (Real.pi / 12) := by positivity
  have hε₀_pos : 0 < ε₀ := by positivity
  refine ⟨ε₀, hε₀_pos, ?_⟩
  intro ε hε_mem hε_dist
  simp only [Set.mem_Ioi] at hε_mem
  rw [Real.dist_eq, sub_zero, abs_of_pos hε_mem] at hε_dist
  have hε_pos : 0 < ε := hε_mem
  have hε_lt_half : ε < 1 / 2 := lt_of_lt_of_le hε_dist
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hε_lt_gap : ε < H - 1 := lt_of_lt_of_le hε_dist
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := lt_of_lt_of_le hε_dist
    (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε_lt_r2 : ε < r / 2 := lt_of_lt_of_le hε_dist (min_le_right _ _)
  set δ := 12 / Real.pi * Real.arcsin (ε / 2) with hδ_def
  have hε_half_pos : 0 < ε / 2 := by linarith
  have hε_half_le : ε / 2 ≤ 1 := by linarith
  have hε_half_neg : -1 ≤ ε / 2 := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have harcsin_pos : 0 < Real.arcsin (ε / 2) := Real.arcsin_pos.mpr hε_half_pos
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  have hδ_lt_one : δ < 1 := by
    rw [hδ_def]
    have hε_lt_sin : ε / 2 < Real.sin (Real.pi / 12) := by linarith
    have harcsin_lt : Real.arcsin (ε / 2) < Real.pi / 12 := by
      calc Real.arcsin (ε / 2) < Real.arcsin (Real.sin (Real.pi / 12)) :=
            Real.arcsin_lt_arcsin hε_half_neg hε_lt_sin (Real.sin_le_one _)
        _ = Real.pi / 12 :=
            Real.arcsin_sin (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    calc 12 / Real.pi * Real.arcsin (ε / 2)
        < 12 / Real.pi * (Real.pi / 12) :=
          mul_lt_mul_of_pos_left harcsin_lt (div_pos (by norm_num) hpi_pos)
      _ = 1 := by field_simp
  have hδ_angle : δ * Real.pi / 12 = Real.arcsin (ε / 2) := by rw [hδ_def]; field_simp
  have h_norm_L : ‖fdBoundary_H H (2 - δ) - I‖ = ε := by
    rw [g_i_norm_left hδ_pos hδ_lt_one, hδ_angle,
        Real.sin_arcsin hε_half_neg hε_half_le]; linarith
  have h_norm_R : ‖fdBoundary_H H (2 + δ) - I‖ = ε := by
    rw [g_i_norm_right hδ_pos hδ_lt_one, hδ_angle,
        Real.sin_arcsin hε_half_neg hε_half_le]; linarith
  set g := fun t => fdBoundary_H H t - I with hg_def
  have h_ftc := ftc_logDeriv_telescope_i H hH hδ_pos hδ_lt_one
  obtain ⟨hint_L, hint_R, h_telescope⟩ := h_ftc
  have h_norm_gt_left : ∀ t ∈ Ioo (0 : ℝ) (2 - δ), ‖g t‖ > ε := by
    intro t ⟨ht0, ht2⟩
    rcases le_or_gt t 1 with ht1 | ht1
    · calc ε < 1 / 2 := hε_lt_half
        _ ≤ ‖g t‖ := g_i_norm_ge_seg0 (le_of_lt ht0) ht1
    · rw [show g t = fdBoundary_H H t - I from rfl, g_i_norm_arc_left ht1 (by linarith)]
      rw [← h_norm_L, g_i_norm_left hδ_pos hδ_lt_one]
      apply mul_lt_mul_of_pos_left _ (by norm_num : (0:ℝ) < 2)
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
  have h_norm_gt_right : ∀ t ∈ Ioo (2 + δ) (5 : ℝ), ‖g t‖ > ε := by
    intro t ⟨ht2, ht5⟩
    rcases le_or_gt t 3 with ht3 | ht3
    · rcases eq_or_lt_of_le ht3 with rfl | ht3'
      · calc ε < 1 / 2 := hε_lt_half
          _ ≤ ‖g 3‖ := g_i_norm_ge_seg3 (le_refl 3) (by norm_num)
      · rw [show g t = fdBoundary_H H t - I from rfl, g_i_norm_arc_right (by linarith) ht3']
        rw [← h_norm_R, g_i_norm_right hδ_pos hδ_lt_one]
        apply mul_lt_mul_of_pos_left _ (by norm_num : (0:ℝ) < 2)
        exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])
    · rcases le_or_gt t 4 with ht4 | ht4
      · calc ε < 1 / 2 := hε_lt_half
          _ ≤ ‖g t‖ := g_i_norm_ge_seg3 (le_of_lt ht3) ht4
      · calc ε < H - 1 := hε_lt_gap
          _ ≤ ‖g t‖ := g_i_norm_ge_seg4 H hH (le_of_lt ht4) (le_of_lt ht5)
  have h_norm_le_middle : ∀ t, 2 - δ ≤ t → t ≤ 2 + δ → ¬(‖g t‖ > ε) := by
    intro t ht_lo ht_hi; push_neg
    rcases le_or_gt t 2 with ht2 | ht2
    · rcases eq_or_lt_of_le ht2 with rfl | ht2'
      · rw [show g 2 = fdBoundary_H H 2 - I from rfl, fdBoundary_H_at_two_eq_I,
          sub_self, norm_zero]; exact le_of_lt hε_pos
      · have ht1 : 1 < t := by linarith
        rw [show g t = fdBoundary_H H t - I from rfl, g_i_norm_arc_left ht1 ht2']
        rw [← h_norm_L, g_i_norm_left hδ_pos hδ_lt_one]
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
        exact Real.sin_le_sin_of_le_of_le_pi_div_two
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])
    · rw [show g t = fdBoundary_H H t - I from rfl, g_i_norm_arc_right ht2 (by linarith)]
      rw [← h_norm_R, g_i_norm_right hδ_pos hδ_lt_one]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
      exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
  set F := fun t => if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else (0 : ℂ) with hF_def
  have hF_when_gt (t : ℝ) (h_gt : ‖g t‖ > ε) : F t = deriv g t / g t := by
    simp only [hF_def, if_pos h_gt, mul_comm (g t)⁻¹, div_eq_mul_inv]
  have hF_when_le (t : ℝ) (h_le : ¬(‖g t‖ > ε)) : F t = 0 := by
    simp only [hF_def, if_neg h_le]
  have hF_eq_left_ae :
      ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (2 - δ) → F t = deriv g t / g t := by
    have : ({2 - δ} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton _)
    filter_upwards [this] with t ht_ne ht_mem
    rw [uIoc_of_le (by linarith : (0:ℝ) ≤ 2 - δ)] at ht_mem
    exact hF_when_gt t (h_norm_gt_left t
      ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (mem_singleton_iff.mpr h))⟩)
  have hF_int_left : IntervalIntegrable F volume 0 (2 - δ) :=
    hint_L.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_eq_left_ae.mono (fun t ht hm => (ht hm).symm)))
  have hF_eq_right_ae :
      ∀ᵐ t ∂volume, t ∈ Ι (2 + δ) (5 : ℝ) → F t = deriv g t / g t := by
    have : ({5} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton _)
    filter_upwards [this] with t ht_ne ht_mem
    rw [uIoc_of_le (by linarith : 2 + δ ≤ 5)] at ht_mem
    exact hF_when_gt t (h_norm_gt_right t
      ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (mem_singleton_iff.mpr h))⟩)
  have hF_int_right : IntervalIntegrable F volume (2 + δ) 5 :=
    hint_R.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_eq_right_ae.mono (fun t ht hm => (ht hm).symm)))
  have hF_eq_mid : ∀ t ∈ Ι (2 - δ) (2 + δ), F t = 0 := by
    intro t ht; rw [uIoc_of_le (by linarith : 2 - δ ≤ 2 + δ)] at ht
    exact hF_when_le t (h_norm_le_middle t (le_of_lt ht.1) ht.2)
  have hF_int_mid : IntervalIntegrable F volume (2 - δ) (2 + δ) :=
    (IntervalIntegrable.zero (μ := volume) (a := 2 - δ) (b := 2 + δ)).congr
      (fun t ht => (hF_eq_mid t ht).symm)
  have h_split : ∫ t in (0:ℝ)..5, F t =
      (∫ t in (0:ℝ)..(2 - δ), F t) + (∫ t in (2 - δ)..(2 + δ), F t) +
      (∫ t in (2 + δ)..(5:ℝ), F t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hF_int_left.trans hF_int_mid) hF_int_right,
        ← intervalIntegral.integral_add_adjacent_intervals hF_int_left hF_int_mid]
  have h_mid_zero : ∫ t in (2 - δ)..(2 + δ), F t = 0 := by
    rw [intervalIntegral.integral_congr_ae (ae_of_all _ (fun t ht => hF_eq_mid t ht))]
    simp [intervalIntegral.integral_zero]
  have h_int_eq : (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) =
      (∫ t in (0:ℝ)..(2 - δ), deriv g t / g t) +
      (∫ t in (2 + δ)..(5:ℝ), deriv g t / g t) := by
    calc (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0)
        = ∫ t in (0:ℝ)..5, F t := rfl
      _ = _ + _ + _ := h_split
      _ = _ + 0 + _ := by rw [h_mid_zero]
      _ = _ := by
          rw [add_zero, intervalIntegral.integral_congr_ae hF_eq_left_ae,
              intervalIntegral.integral_congr_ae hF_eq_right_ae]
  rw [show dist (∫ t in (0:ℝ)..5,
      if ‖fdBoundary_H H t - I‖ > ε
      then (fdBoundary_H H t - I)⁻¹ *
           deriv (fun s => fdBoundary_H H s - I) t
      else 0)
    (-(I * ↑Real.pi)) =
    ‖(∫ t in (0:ℝ)..5,
      if ‖fdBoundary_H H t - I‖ > ε
      then (fdBoundary_H H t - I)⁻¹ *
           deriv (fun s => fdBoundary_H H s - I) t
      else 0) - (-(I * ↑Real.pi))‖ from Complex.dist_eq _ _]
  rw [h_int_eq, h_telescope]
  set zL := fdBoundary_H H (2 - δ) - I
  set zR := fdBoundary_H H (2 + δ) - I
  rw [← Complex.re_add_im (Complex.log zL), ← Complex.re_add_im (Complex.log zR),
    Complex.log_re, Complex.log_re, Complex.log_im, Complex.log_im]
  change ‖zL‖ = ε at h_norm_L; change ‖zR‖ = ε at h_norm_R
  rw [h_norm_L, h_norm_R,
    show zL.arg = (fdBoundary_H H (2 - δ) - I).arg from rfl,
    arg_approach_i_left hδ_pos hδ_lt_one,
    show zR.arg = (fdBoundary_H H (2 + δ) - I).arg from rfl,
    arg_approach_i_right hδ_pos hδ_lt_one]
  have h_simp : ↑(Real.log ε) + ↑(-(δ * Real.pi / 12)) * I -
      (↑(Real.log ε) + ↑(δ * Real.pi / 12 - Real.pi) * I) -
      2 * ↑Real.pi * I - -(I * ↑Real.pi) =
      ↑(-(δ * Real.pi / 6)) * I := by push_cast; ring
  rw [h_simp, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  set x := δ * Real.pi / 12 with hx_def
  have hx_pos : 0 < x := by positivity
  have hx_le_one : x ≤ 1 := by nlinarith [Real.pi_le_four]
  have h_sin_lb := Real.sin_gt_sub_cube hx_pos hx_le_one
  have h_lb : x - x ^ 3 / 4 > x / 2 := by nlinarith [sq_nonneg x, sq_nonneg (1 - x)]
  have h_norm_is_2sin : 2 * Real.sin x = ε := by
    rw [hx_def, show δ * Real.pi / 12 = δ * Real.pi / 12 from rfl]
    linarith [h_norm_L, g_i_norm_left (H := H) hδ_pos hδ_lt_one]
  have hx_lt_ε : x < ε := by linarith
  linarith

/-- `generalizedWindingNumber' (fdBoundary_H H) 0 5 I = -1/2`.

Note: requires `1 < H` (not just `√3/2 < H`) because for `H > 1`, the point `I` is
strictly inside the contour and the branch cut correction on seg 3 contributes `-2πi`.
For `√3/2 < H < 1`, `I` would be outside the contour and the result would be `+1/2`. -/
theorem gWN_fdBoundary_H_at_i (H : ℝ) (hH : 1 < H) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 I = -1/2 := by
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  dsimp only []
  simp only [sub_zero]
  have h_tendsto := pv_integral_at_i_tendsto H hH
  rw [h_tendsto.limUnder_eq]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [Real.pi_ne_zero, I_ne_zero]

end
