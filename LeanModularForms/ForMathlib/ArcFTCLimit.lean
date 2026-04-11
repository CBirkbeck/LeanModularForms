/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.ArcFTC
import LeanModularForms.ForMathlib.SegmentFTC
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Arc FTC Limit at i — Slit Plane Membership and Log-Arg Computation

This file proves that `γ(t) - i` stays in the slit plane away from `t = 2/5` on
the segments where it does, computes the equal-norm property at `2/5 ± δ`, and
establishes the log difference formula and limit `E(δ) → -πi`.

## Main results

* `fdBoundaryFun_sub_i_slitPlane_seg1` — slit plane on right vertical
* `fdBoundaryFun_sub_i_slitPlane_seg2` — slit plane on arc before `i`
* `fdBoundaryFun_sub_i_neg_slitPlane_seg3` — neg-slit-plane on arc after `i`
* `fdBoundaryFun_sub_i_slitPlane_seg5` — slit plane on horizontal
* `fdBoundaryFun_sub_i_norm_symm` — equal norms at `2/5 ± δ`
* `log_sub_eq_of_equal_norm` — log difference = arg difference when norms equal
* `fdBoundaryFun_arg_left` — `arg(γ(2/5-δ) - i) = -5δπ/12`
* `fdBoundaryFun_arg_right` — `arg(γ(2/5+δ) - i) = 5δπ/12 - π`
* `fdBoundaryFun_log_diff_core_tendsto` — `log(γ(2/5-δ)-i) - log(γ(2/5+δ)-i) → πi`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ## Part 1: Slit plane membership per segment -/

/-- On segment 1 (right vertical, `Re = 1/2`), `γ(t) - i ∈ slitPlane`. -/
theorem fdBoundaryFun_sub_i_slitPlane_seg1 (H : ℝ) (t : ℝ) (ht : t ≤ 1/5) :
    fdBoundaryFun H t - I ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  simp only [sub_re, fdBoundaryFun_seg1_re H t ht, I_re]; norm_num

/-- On segment 2 (arc before `i`, angle `< π/2`), `γ(t) - i ∈ slitPlane`. -/
theorem fdBoundaryFun_sub_i_slitPlane_seg2 (H : ℝ) (t : ℝ)
    (ht1 : 1/5 < t) (ht2 : t < 2/5) :
    fdBoundaryFun H t - I ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  rw [fdBoundaryFun_arc_eq_exp H t (by linarith) (by linarith),
    exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [add_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, add_zero, mul_one]
  exact Real.cos_pos_of_mem_Ioo ⟨by unfold fdArcAngle; nlinarith [Real.pi_pos],
    by unfold fdArcAngle; nlinarith [Real.pi_pos]⟩

/-- On segment 3 (arc after `i`), `γ(t) - i ≠ 0` (cos is strictly negative). -/
theorem fdBoundaryFun_sub_i_ne_zero_seg3 (H : ℝ) (t : ℝ)
    (ht2 : 2/5 < t) (ht3 : t ≤ 3/5) :
    fdBoundaryFun H t - I ≠ 0 := by
  rw [fdBoundaryFun_arc_eq_exp H t (by linarith) ht3,
    exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  intro h
  have hre := congr_arg Complex.re h
  simp only [add_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, add_zero, zero_re, mul_one] at hre
  have hgt : Real.pi / 2 < fdArcAngle t := by
    unfold fdArcAngle; nlinarith [Real.pi_pos]
  have hlt : fdArcAngle t < Real.pi + Real.pi / 2 := by
    unfold fdArcAngle; nlinarith [Real.pi_pos]
  linarith [Real.cos_neg_of_pi_div_two_lt_of_lt hgt hlt]

/-- On segment 3 (arc after `i`), `-(γ(t) - i) ∈ slitPlane`. -/
theorem fdBoundaryFun_sub_i_neg_slitPlane_seg3 (H : ℝ) (t : ℝ)
    (ht2 : 2/5 < t) (ht3 : t ≤ 3/5) :
    -(fdBoundaryFun H t - I) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  rw [fdBoundaryFun_arc_eq_exp H t (by linarith) ht3,
    exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [neg_sub, sub_re, I_re, add_re, ofReal_re, mul_re, ofReal_im, I_im,
    mul_zero, sub_zero, add_zero, mul_one]
  have hgt : Real.pi / 2 < fdArcAngle t := by
    unfold fdArcAngle; nlinarith [Real.pi_pos]
  have hlt : fdArcAngle t < Real.pi + Real.pi / 2 := by
    unfold fdArcAngle; nlinarith [Real.pi_pos]
  linarith [Real.cos_neg_of_pi_div_two_lt_of_lt hgt hlt]

/-- On segment 5 (horizontal at height `H`), `γ(t) - i ∈ slitPlane` when `H > 1`. -/
theorem fdBoundaryFun_sub_i_slitPlane_seg5 (H : ℝ) (hH : 1 < H)
    (t : ℝ) (ht : 4/5 < t) :
    fdBoundaryFun H t - I ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  simp only [sub_im, fdBoundaryFun_seg5_im H t ht, I_im]; linarith

/-! ## Part 2: Arc norm symmetry -/

/-- Norm of `γ(2/5 - δ) - i` equals `2|sin(5δπ/12)|`. -/
theorem fdBoundaryFun_sub_i_norm_left (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) :
    ‖fdBoundaryFun H (2/5 - δ) - I‖ = 2 * |Real.sin (5 * δ * Real.pi / 12)| := by
  rw [fdBoundaryFun_arc_dist_I H (2/5 - δ) (by linarith) (by linarith)]
  congr 1
  rw [show fdArcAngle (2/5 - δ) - Real.pi / 2 = -(5 * δ * Real.pi / 6) from by
    unfold fdArcAngle; ring]
  rw [show -(5 * δ * Real.pi / 6) / 2 = -(5 * δ * Real.pi / 12) from by ring,
    Real.sin_neg, abs_neg]

/-- Norm of `γ(2/5 + δ) - i` equals `2|sin(5δπ/12)|`. -/
theorem fdBoundaryFun_sub_i_norm_right (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) :
    ‖fdBoundaryFun H (2/5 + δ) - I‖ = 2 * |Real.sin (5 * δ * Real.pi / 12)| := by
  rw [fdBoundaryFun_arc_dist_I H (2/5 + δ) (by linarith) (by linarith)]
  congr 1
  rw [show fdArcAngle (2/5 + δ) - Real.pi / 2 = 5 * δ * Real.pi / 6 from by
    unfold fdArcAngle; ring]
  rw [show 5 * δ * Real.pi / 6 / 2 = 5 * δ * Real.pi / 12 from by ring]

/-- The norms are equal: `‖γ(2/5-δ) - i‖ = ‖γ(2/5+δ) - i‖`. -/
theorem fdBoundaryFun_sub_i_norm_symm (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) :
    ‖fdBoundaryFun H (2/5 - δ) - I‖ = ‖fdBoundaryFun H (2/5 + δ) - I‖ := by
  rw [fdBoundaryFun_sub_i_norm_left H hδ hδs,
    fdBoundaryFun_sub_i_norm_right H hδ hδs]

/-! ## Part 3: Log difference when norms are equal -/

/-- When two nonzero complex numbers have equal norms, their log difference
equals `↑(arg z - arg w) * I`. -/
theorem log_sub_eq_of_equal_norm {z w : ℂ} (_hz : z ≠ 0) (_hw : w ≠ 0)
    (hnorm : ‖z‖ = ‖w‖) :
    Complex.log z - Complex.log w = ↑(z.arg - w.arg) * I := by
  apply Complex.ext
  · simp only [sub_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, mul_zero,
      Complex.log_re, hnorm, sub_self]; ring
  · simp only [sub_im, mul_im, ofReal_re, I_re, ofReal_im, I_im, mul_zero, add_zero,
      mul_one, Complex.log_im]

/-! ## Part 4: Arg computation at approach points -/

/-- Arg of the left approach: `arg(γ(2/5-δ) - i) = -(5δπ/12)` for `0 < δ < 1/5`.

The half-angle factorization gives `γ(2/5-δ) - i = 2sin(α) · exp(-iα)` where
`α = 5δπ/12 ∈ (0, π/12)`, hence `arg = -α`. -/
theorem fdBoundaryFun_arg_left (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) :
    (fdBoundaryFun H (2/5 - δ) - I).arg = -(5 * δ * Real.pi / 12) := by
  rw [fdBoundaryFun_arc_eq_exp H _ (by linarith) (by linarith),
    exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  set α := 5 * δ * Real.pi / 12
  have hα_pos : 0 < α := by positivity
  have hα_small : α < Real.pi := by
    change 5 * δ * Real.pi / 12 < Real.pi; nlinarith [Real.pi_pos]
  have h_sinα_pos : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα_pos hα_small
  have h_cosθ : Real.cos (fdArcAngle (2/5 - δ)) = Real.sin (5 * δ * Real.pi / 6) := by
    rw [show fdArcAngle (2/5 - δ) = Real.pi / 2 - 5 * δ * Real.pi / 6 from by
      unfold fdArcAngle; ring]
    exact Real.cos_pi_div_two_sub _
  have h_sinθ : Real.sin (fdArcAngle (2/5 - δ)) = Real.cos (5 * δ * Real.pi / 6) := by
    rw [show fdArcAngle (2/5 - δ) = Real.pi / 2 - 5 * δ * Real.pi / 6 from by
      unfold fdArcAngle; ring]
    exact Real.sin_pi_div_two_sub _
  have h2α : (5 * δ * Real.pi / 6 : ℝ) = 2 * α := by ring
  have h_sin_double : Real.sin (5 * δ * Real.pi / 6) =
      2 * Real.sin α * Real.cos α := by rw [h2α, Real.sin_two_mul]
  have h_cos_double : Real.cos (5 * δ * Real.pi / 6) - 1 =
      -(2 * Real.sin α ^ 2) := by
    rw [h2α, Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq α]
  have h_eq : ↑(Real.cos (fdArcAngle (2/5 - δ))) +
      ↑(Real.sin (fdArcAngle (2/5 - δ))) * I - I =
      ↑(2 * Real.sin α) * (↑(Real.cos α) + ↑(-(Real.sin α)) * I) := by
    apply Complex.ext
    · simp only [add_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, sub_zero, add_zero, mul_one]
      rw [h_cosθ]; linarith [h_sin_double]
    · simp only [add_im, sub_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
        mul_zero, add_zero, mul_one, zero_add]
      rw [h_sinθ]; nlinarith [h_cos_double]
  rw [h_eq]
  have h_trig : (↑(Real.cos α) : ℂ) + ↑(-(Real.sin α)) * I =
      Complex.cos ↑(-α) + Complex.sin ↑(-α) * I := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, ofReal_neg]
  rw [h_trig]
  exact Complex.arg_mul_cos_add_sin_mul_I (by positivity)
    ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩

/-- Arg of the right approach: `arg(γ(2/5+δ) - i) = 5δπ/12 - π` for `0 < δ < 1/5`.

The half-angle factorization gives `γ(2/5+δ) - i = -2sin(α) · exp(iα)` where
`α = 5δπ/12`, so `arg = α - π` (negative since `im < 0`). -/
theorem fdBoundaryFun_arg_right (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) :
    (fdBoundaryFun H (2/5 + δ) - I).arg = 5 * δ * Real.pi / 12 - Real.pi := by
  rw [fdBoundaryFun_arc_eq_exp H _ (by linarith) (by linarith),
    exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  set α := 5 * δ * Real.pi / 12
  have hα_pos : 0 < α := by positivity
  have hα_small : α < Real.pi := by
    change 5 * δ * Real.pi / 12 < Real.pi; nlinarith [Real.pi_pos]
  have h_sinα_pos : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα_pos hα_small
  have h_cosθ : Real.cos (fdArcAngle (2/5 + δ)) = -(Real.sin (5 * δ * Real.pi / 6)) := by
    rw [show fdArcAngle (2/5 + δ) = Real.pi / 2 + 5 * δ * Real.pi / 6 from by
      unfold fdArcAngle; ring, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have h_sinθ : Real.sin (fdArcAngle (2/5 + δ)) = Real.cos (5 * δ * Real.pi / 6) := by
    rw [show fdArcAngle (2/5 + δ) = Real.pi / 2 + 5 * δ * Real.pi / 6 from by
      unfold fdArcAngle; ring, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  have h2α : (5 * δ * Real.pi / 6 : ℝ) = 2 * α := by ring
  have h_sin_double : Real.sin (5 * δ * Real.pi / 6) =
      2 * Real.sin α * Real.cos α := by rw [h2α, Real.sin_two_mul]
  have h_cos_double : Real.cos (5 * δ * Real.pi / 6) - 1 =
      -(2 * Real.sin α ^ 2) := by
    rw [h2α, Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq α]
  have h_eq : ↑(Real.cos (fdArcAngle (2/5 + δ))) +
      ↑(Real.sin (fdArcAngle (2/5 + δ))) * I - I =
      -(↑(2 * Real.sin α) * (↑(Real.cos α) + ↑(Real.sin α) * I)) := by
    apply Complex.ext
    · simp only [add_re, sub_re, neg_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, sub_zero, add_zero, mul_one]
      rw [h_cosθ]; linarith [h_sin_double]
    · simp only [add_im, sub_im, neg_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
        mul_zero, add_zero, mul_one, zero_add]
      rw [h_sinθ]; nlinarith [h_cos_double]
  rw [h_eq]
  have h_trig : (↑(Real.cos α) : ℂ) + ↑(Real.sin α) * I =
      Complex.cos ↑α + Complex.sin ↑α * I := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [h_trig]
  have hw_arg := Complex.arg_mul_cos_add_sin_mul_I (show (0:ℝ) < 2 * Real.sin α by positivity)
    (show α ∈ Ioc (-Real.pi) Real.pi from ⟨by nlinarith [Real.pi_pos], by linarith⟩)
  have hrw_im_pos : 0 < (↑(2 * Real.sin α) *
      (Complex.cos ↑α + Complex.sin ↑α * I)).im := by
    rw [mul_im, ofReal_re, ofReal_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [ofReal_re, ofReal_im, add_re, mul_re, I_re, I_im, mul_zero, sub_zero,
      add_im, mul_im, zero_mul, add_zero, mul_one]
    nlinarith [Real.sin_pos_of_pos_of_lt_pi hα_pos hα_small]
  rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hrw_im_pos, hw_arg]

/-- The arg difference: `arg(left) - arg(right) = π - 5δπ/6`. -/
theorem fdBoundaryFun_arg_diff (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) :
    (fdBoundaryFun H (2/5 - δ) - I).arg -
    (fdBoundaryFun H (2/5 + δ) - I).arg = Real.pi - 5 * δ * Real.pi / 6 := by
  rw [fdBoundaryFun_arg_left H hδ hδs, fdBoundaryFun_arg_right H hδ hδs]; ring

/-! ## Part 5: The limit -/

/-- The "core" log difference tends to `πi` as `δ → 0⁺`.
`log(γ(2/5-δ) - i) - log(γ(2/5+δ) - i) → πi`. -/
theorem fdBoundaryFun_log_diff_core_tendsto (H : ℝ) :
    Tendsto (fun δ => Complex.log (fdBoundaryFun H (2/5 - δ) - I) -
      Complex.log (fdBoundaryFun H (2/5 + δ) - I))
      (𝓝[>] 0) (𝓝 (↑Real.pi * I)) := by
  have hkey : ∀ᶠ δ in 𝓝[>] (0:ℝ),
      Complex.log (fdBoundaryFun H (2/5 - δ) - I) -
      Complex.log (fdBoundaryFun H (2/5 + δ) - I) =
      ↑(Real.pi - 5 * δ * Real.pi / 6) * I := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0:ℝ) < 1/5 from by norm_num)] with δ hδ hδ_pos
    rw [mem_Ioi] at hδ_pos; rw [mem_Iio] at hδ
    rw [log_sub_eq_of_equal_norm
      (sub_ne_zero.mpr (by
        rw [fdBoundaryFun_arc_eq_exp H _ (by linarith) (by linarith),
          exp_mul_I, ← ofReal_cos, ← ofReal_sin]
        intro heq; have := congr_arg Complex.re heq
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero] at this
        linarith [Real.cos_pos_of_mem_Ioo
          (show fdArcAngle (2/5 - δ) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
            ⟨by unfold fdArcAngle; nlinarith [Real.pi_pos],
             by unfold fdArcAngle; nlinarith [Real.pi_pos]⟩)]))
      (fdBoundaryFun_sub_i_ne_zero_seg3 H _ (by linarith) (by linarith))
      (fdBoundaryFun_sub_i_norm_symm H hδ_pos hδ),
      fdBoundaryFun_arg_diff H hδ_pos hδ]
  have htend : Tendsto (fun δ : ℝ => (↑(Real.pi - 5 * δ * Real.pi / 6) : ℂ) * I)
      (𝓝[>] 0) (𝓝 (↑Real.pi * I)) := by
    apply Filter.Tendsto.mul_const
    apply Filter.Tendsto.ofReal
    have key : ContinuousAt (fun δ : ℝ => Real.pi - 5 * δ * Real.pi / 6) 0 :=
      continuousAt_const.sub
        ((continuousAt_const.mul continuousAt_id).mul continuousAt_const |>.div_const _)
    have h := key.tendsto
    simp only [mul_zero, zero_mul, zero_div, sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact htend.congr' (hkey.mono fun _ h => h.symm)

end
