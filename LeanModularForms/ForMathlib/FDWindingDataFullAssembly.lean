/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.BoundaryWindingSeg1Proof
import LeanModularForms.ForMathlib.BoundaryWindingSeg4Proof
import LeanModularForms.ForMathlib.BoundaryWindingArcProof

/-!
# Assembly: `FDWindingDataFull` from per-segment FTC providers

Given:
1. A base `FDWindingData H` (interior + three elliptic corner winding numbers)
2. Per-segment `ArcFTCHyp` providers for seg1, seg4, and the arc

this file assembles `FDWindingDataFull H` unconditionally.

## Main results

* `mkFDWindingDataFull_of_ftcProviders` -- the main assembler
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ### Converting between arc angle and complex point -/

/-- For `z` on the unit circle in the upper half-plane with `|z.re| < 1/2`,
the argument `arg z` lies in `(π/3, 2π/3)`. -/
theorem arg_mem_arc_range {z : ℂ} (hz_norm : ‖z‖ = 1) (hz_im : 0 < z.im)
    (hz_re : |z.re| < 1/2) :
    Real.pi / 3 < z.arg ∧ z.arg < 2 * Real.pi / 3 := by
  have hz_ne : z ≠ 0 := by
    intro h; rw [h] at hz_im; simp at hz_im
  have h_cos : Real.cos z.arg = z.re := by
    rw [Complex.cos_arg hz_ne, hz_norm, div_one]
  have h_sin : Real.sin z.arg = z.im := by
    rw [Complex.sin_arg, hz_norm, div_one]
  have h_arg_pos : 0 < z.arg := by
    rcases lt_or_eq_of_le (Complex.arg_nonneg_iff.mpr hz_im.le) with h | h
    · exact h
    · exfalso; rw [← h] at h_sin
      rw [Real.sin_zero] at h_sin
      linarith
  have h_arg_lt_pi : z.arg < Real.pi := by
    rcases lt_or_eq_of_le (Complex.arg_le_pi z) with h | h
    · exact h
    · exfalso
      have : Real.sin z.arg = 0 := by rw [h, Real.sin_pi]
      rw [h_sin] at this
      linarith
  have hpi := Real.pi_pos
  have hπ3_Icc : (Real.pi / 3) ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have h2π3_Icc : (2 * Real.pi / 3) ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have h_arg_Icc : z.arg ∈ Icc (0 : ℝ) Real.pi := ⟨h_arg_pos.le, h_arg_lt_pi.le⟩
  -- |cos z.arg| < 1/2 means cos z.arg ∈ (-1/2, 1/2), and cos is strictly
  -- decreasing on [0, π], so z.arg ∈ (π/3, 2π/3).
  have h_cos_abs : |Real.cos z.arg| < 1/2 := by rw [h_cos]; exact hz_re
  have h_cos_lo : Real.cos z.arg > -1/2 := by
    rcases abs_lt.mp h_cos_abs with ⟨h1, _⟩; linarith
  have h_cos_hi : Real.cos z.arg < 1/2 := by
    rcases abs_lt.mp h_cos_abs with ⟨_, h2⟩; linarith
  have h_cos_pi3 : Real.cos (Real.pi / 3) = 1/2 := Real.cos_pi_div_three
  have h_cos_2pi3 : Real.cos (2 * Real.pi / 3) = -1/2 := by
    rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  refine ⟨?_, ?_⟩
  · by_contra h_not
    push Not at h_not
    have h_cos_ge : Real.cos z.arg ≥ Real.cos (Real.pi / 3) :=
      Real.cos_le_cos_of_nonneg_of_le_pi h_arg_pos.le (by linarith) h_not
    rw [h_cos_pi3] at h_cos_ge
    linarith
  · by_contra h_not
    push Not at h_not
    have h_cos_le : Real.cos z.arg ≤ Real.cos (2 * Real.pi / 3) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) h_arg_lt_pi.le h_not
    rw [h_cos_2pi3] at h_cos_le
    linarith

/-- For `z` on the unit circle, `z = exp(i * arg z)`. -/
theorem eq_exp_arg_mul_I {z : ℂ} (hz_norm : ‖z‖ = 1) :
    z = exp (↑z.arg * I) := by
  have hz_ne : z ≠ 0 := by
    intro h; rw [h] at hz_norm; simp at hz_norm
  have h_cos : Real.cos z.arg = z.re := by
    rw [Complex.cos_arg hz_ne, hz_norm, div_one]
  have h_sin : Real.sin z.arg = z.im := by
    rw [Complex.sin_arg, hz_norm, div_one]
  rw [exp_mul_I]
  rw [← ofReal_cos, ← ofReal_sin, h_cos, h_sin]
  apply Complex.ext <;> simp

/-! ### Main assembler -/

/-- Given `FDWindingData H` and FTC providers for seg1, seg4, and the arc,
construct `FDWindingDataFull H` unconditionally. -/
def mkFDWindingDataFull_of_ftcProviders {H : ℝ} (hH : 1 < H)
    (D : FDWindingData H)
    (ftc_seg1 : ∀ z₀ : ℂ, z₀.re = 1/2 →
      Real.sqrt 3 / 2 < z₀.im → z₀.im < H →
      ArcFTCHyp D.boundary z₀ (seg1T₀ H z₀.im) (linDelta (seg1Speed H))
        (seg1Threshold H z₀) (-(↑Real.pi * I)))
    (ftc_seg4 : ∀ z₀ : ℂ, z₀.re = -1/2 →
      Real.sqrt 3 / 2 < z₀.im → z₀.im < H →
      ArcFTCHyp D.boundary z₀ (seg4T₀ H z₀.im) (linDelta (seg1Speed H))
        (seg4Threshold H z₀) (-(↑Real.pi * I)))
    (ftc_arc : ∀ θ₀ : ℝ, Real.pi / 3 < θ₀ → θ₀ < 2 * Real.pi / 3 →
      ArcFTCHyp D.boundary (exp (↑θ₀ * I)) (arcT₀ θ₀) arcsinDelta
        (arcThreshold H θ₀) (-(↑Real.pi * I))) :
    FDWindingDataFull H := by
  have hH_sqrt3 : Real.sqrt 3 / 2 < H := by
    have h_sqrt3_lt : Real.sqrt 3 < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_nonneg 3]
    linarith
  refine mkFDWindingDataFull D ?_
  intro z hz_im_pos hz_im_lt hz_ne_I hz_ne_rho hz_ne_rho1 hz_not_int hz_nsq hz_re
  have h_class := smooth_boundary_classification z hz_im_pos hz_ne_I
    hz_ne_rho hz_ne_rho1 hz_not_int hz_nsq hz_re
  rcases h_class with ⟨h_re_half, h_norm_gt⟩ | ⟨h_norm, h_re_ne, h_re_half_ne⟩
  · -- Vertical case: z.re = ±1/2
    -- Derive z.im > √3/2 from ‖z‖ > 1 and z.re² = 1/4
    have h_im_gt : Real.sqrt 3 / 2 < z.im := by
      have h_nsq : Complex.normSq z > 1 := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [h_norm_gt, sq_nonneg (‖z‖ - 1), norm_nonneg z]
      rw [Complex.normSq_apply] at h_nsq
      have h_re_sq : z.re * z.re = 1/4 := by
        rcases abs_eq (show (1 : ℝ)/2 ≥ 0 by norm_num) |>.mp h_re_half with
          h | h <;> nlinarith
      have h_im_sq_gt : z.im * z.im > 3/4 := by linarith
      have h_im_nonneg : 0 ≤ z.im := hz_im_pos.le
      have h_sqrt3_nn : 0 ≤ Real.sqrt 3 / 2 := by positivity
      have h_sq_sqrt3 : (Real.sqrt 3 / 2) * (Real.sqrt 3 / 2) = 3/4 := by
        rw [show Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = (Real.sqrt 3 / 2) ^ 2 from by ring,
            div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]
        norm_num
      nlinarith [sq_nonneg (z.im - Real.sqrt 3 / 2)]
    -- Case on sign of z.re
    rcases abs_eq (show (1 : ℝ)/2 ≥ 0 by norm_num) |>.mp h_re_half with h_pos | h_neg
    · -- z.re = 1/2: seg1
      have hSBD :=
        smoothBoundaryData_seg1_of_ftcHyp hH_sqrt3 D.boundary D.boundary_eq
          h_pos h_im_gt hz_im_lt (ftc_seg1 z h_pos h_im_gt hz_im_lt)
      exact hSBD.hasWindingNumber
    · -- z.re = -1/2: seg4
      have h_neg' : z.re = -1/2 := by linarith
      have hSBD :=
        smoothBoundaryData_seg4_of_ftcHyp hH_sqrt3 D.boundary D.boundary_eq
          h_neg' h_im_gt hz_im_lt (ftc_seg4 z h_neg' h_im_gt hz_im_lt)
      exact hSBD.hasWindingNumber
  · -- Arc case: ‖z‖ = 1
    have h_re_lt : |z.re| < 1/2 := lt_of_le_of_ne hz_re h_re_half_ne
    obtain ⟨h_arg_lo, h_arg_hi⟩ := arg_mem_arc_range h_norm hz_im_pos h_re_lt
    have h_z_eq : z = exp (↑z.arg * I) := eq_exp_arg_mul_I h_norm
    rw [h_z_eq]
    have hSBD := smoothBoundaryData_arc_of_ftcHyp hH D.boundary D.boundary_eq
      h_arg_lo h_arg_hi (ftc_arc z.arg h_arg_lo h_arg_hi)
    exact hSBD.hasWindingNumber

end
