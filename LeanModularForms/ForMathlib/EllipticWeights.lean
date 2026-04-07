/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDBoundary
import LeanModularForms.ForMathlib.SingleCrossing

/-!
# Elliptic Point Winding Weights

Geometric infrastructure for computing the generalized winding number of the
fundamental domain boundary contour `fdBoundary H hH` at the three
elliptic/boundary-crossing points `I`, `ρ = -1/2 + (√3/2)i`, and
`ρ + 1 = 1/2 + (√3/2)i`.

## Overview

The FD boundary crosses each elliptic point at exactly one parameter value:
- `I` at `t₀ = 2/5` (junction of arc segments 2 and 3)
- `ρ + 1` at `t₀ = 1/5` (junction of segment 1 and arc segment 2)
- `ρ` at `t₀ = 3/5` (junction of arc segment 3 and segment 4)

## Main results

### Crossing-point values
* `fdBoundaryFun_two_fifths_eq_I` -- `fdBoundaryFun H (2/5) = I`
* `fdBoundaryFun_one_fifth_eq_rhoPlusOne` -- `fdBoundaryFun H (1/5) = ρ + 1`
* `fdBoundaryFun_three_fifths_eq_rho` -- `fdBoundaryFun H (3/5) = ρ`

### Unit circle norm on arc segments
* `norm_fdBoundaryFun_seg2` -- `‖fdBoundaryFun H t‖ = 1` for `t ∈ (1/5, 2/5]`
* `norm_fdBoundaryFun_seg3` -- `‖fdBoundaryFun H t‖ = 1` for `t ∈ (2/5, 3/5]`

### Key trigonometric distance identity
* `norm_exp_I_sub` -- `‖exp(iα) - exp(iβ)‖ = 2|sin((α-β)/2)|`

### Distance formulas on arc segments
* `norm_fdBoundaryFun_sub_I_seg2` -- distance from I on segment 2
* `norm_fdBoundaryFun_sub_I_seg3` -- distance from I on segment 3
* `norm_fdBoundaryFun_sub_rhoPlusOne_seg2` -- distance from ρ+1 on segment 2
* `norm_fdBoundaryFun_sub_rho_seg3` -- distance from ρ on segment 3

### Segment avoidance and distance bounds
* `fdBoundaryFun_ne_I_of_seg1` -- segment 1 avoids I
* `fdBoundaryFun_ne_I_of_seg4` -- segment 4 avoids I
* `fdBoundaryFun_ne_I_of_seg5` -- segment 5 avoids I (when H > 1)
* `norm_fdBoundaryFun_sub_I_ge_seg1` -- distance from I on segment 1 ≥ 1/2
* `norm_fdBoundaryFun_sub_I_ge_seg4` -- distance from I on segment 4 ≥ 1/2

### Algebraic winding number values
* `neg_pi_I_div_two_pi_I` -- `-πi / (2πi) = -1/2`
* `neg_pi_third_I_div_two_pi_I` -- `(-π/3 · i) / (2πi) = -1/6`

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

noncomputable section

/-! ### Elliptic point definitions -/

/-- The elliptic point `ρ = -1/2 + (√3/2)i`. -/
def rho : ℂ := -1 / 2 + ↑(Real.sqrt 3) / 2 * I

/-- The elliptic point `ρ + 1 = 1/2 + (√3/2)i`. -/
def rhoPlusOne : ℂ := 1 / 2 + ↑(Real.sqrt 3) / 2 * I

theorem rho_add_one : rho + 1 = rhoPlusOne := by
  simp only [rho, rhoPlusOne]; ring

theorem rhoPlusOne_sub_one : rhoPlusOne - 1 = rho := by
  simp only [rho, rhoPlusOne]; ring

theorem rho_re : rho.re = -1 / 2 := by
  simp [rho, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]

theorem rho_im : rho.im = Real.sqrt 3 / 2 := by
  simp [rho, add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re]

theorem rhoPlusOne_re : rhoPlusOne.re = 1 / 2 := by
  simp [rhoPlusOne, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]

theorem rhoPlusOne_im : rhoPlusOne.im = Real.sqrt 3 / 2 := by
  simp [rhoPlusOne, add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re]

/-! ### Crossing-point values -/

/-- The FD boundary passes through `I` at parameter `t = 2/5`. -/
theorem fdBoundaryFun_two_fifths_eq_I (H : ℝ) :
    fdBoundaryFun H (2 / 5) = I :=
  fdBoundaryFun_at_two_fifths H

/-- The FD boundary passes through `ρ + 1` at parameter `t = 1/5`. -/
theorem fdBoundaryFun_one_fifth_eq_rhoPlusOne (H : ℝ) :
    fdBoundaryFun H (1 / 5) = rhoPlusOne := by
  rw [fdBoundaryFun_at_one_fifth, rhoPlusOne]

/-- The FD boundary passes through `ρ` at parameter `t = 3/5`. -/
theorem fdBoundaryFun_three_fifths_eq_rho (H : ℝ) :
    fdBoundaryFun H (3 / 5) = rho := by
  rw [fdBoundaryFun_at_three_fifths, rho]

/-! ### Angle parameterization on arc segments

On segment 2 (`t ∈ [1/5, 2/5]`), the angle is `π/3 + 5(t - 1/5)(π/6)`,
ranging from `π/3` to `π/2`.

On segment 3 (`t ∈ [2/5, 3/5]`), the angle is `π/2 + 5(t - 2/5)(π/6)`,
ranging from `π/2` to `2π/3`. -/

/-- The angle parameter for segment 2. -/
def seg2Angle (t : ℝ) : ℝ :=
  Real.pi / 3 + 5 * (t - 1 / 5) * (Real.pi / 2 - Real.pi / 3)

/-- The angle parameter for segment 3. -/
def seg3Angle (t : ℝ) : ℝ :=
  Real.pi / 2 + 5 * (t - 2 / 5) * (2 * Real.pi / 3 - Real.pi / 2)

theorem seg2Angle_at_one_fifth : seg2Angle (1 / 5) = Real.pi / 3 := by
  simp [seg2Angle]

theorem seg2Angle_at_two_fifths : seg2Angle (2 / 5) = Real.pi / 2 := by
  simp [seg2Angle]; ring

theorem seg3Angle_at_two_fifths : seg3Angle (2 / 5) = Real.pi / 2 := by
  simp [seg3Angle]

theorem seg3Angle_at_three_fifths : seg3Angle (3 / 5) = 2 * Real.pi / 3 := by
  simp [seg3Angle]; ring

/-- On segment 2, `fdBoundaryFun` equals `exp(i * seg2Angle(t))`. -/
theorem fdBoundaryFun_seg2_eq {H : ℝ} {t : ℝ} (h1 : 1 / 5 < t) (h2 : t ≤ 2 / 5) :
    fdBoundaryFun H t = exp (↑(seg2Angle t) * I) := by
  simp only [fdBoundaryFun, show ¬t ≤ 1 / 5 from not_le.mpr h1, h2, ite_true, ite_false]
  congr 1
  simp only [seg2Angle]; push_cast; ring

/-- On segment 3, `fdBoundaryFun` equals `exp(i * seg3Angle(t))`. -/
theorem fdBoundaryFun_seg3_eq {H : ℝ} {t : ℝ} (h1 : 2 / 5 < t) (h2 : t ≤ 3 / 5) :
    fdBoundaryFun H t = exp (↑(seg3Angle t) * I) := by
  simp only [fdBoundaryFun,
    show ¬t ≤ 1 / 5 from not_le.mpr (lt_trans (by norm_num : (1 : ℝ) / 5 < 2 / 5) h1),
    show ¬t ≤ 2 / 5 from not_le.mpr h1, h2, ite_true, ite_false]
  congr 1
  simp only [seg3Angle]; push_cast; ring

/-! ### Unit circle norm on arc segments -/

/-- On segment 2, the boundary lies on the unit circle. -/
theorem norm_fdBoundaryFun_seg2 {H : ℝ} {t : ℝ}
    (h1 : 1 / 5 < t) (h2 : t ≤ 2 / 5) :
    ‖fdBoundaryFun H t‖ = 1 := by
  rw [fdBoundaryFun_seg2_eq h1 h2, norm_exp_ofReal_mul_I]

/-- On segment 3, the boundary lies on the unit circle. -/
theorem norm_fdBoundaryFun_seg3 {H : ℝ} {t : ℝ}
    (h1 : 2 / 5 < t) (h2 : t ≤ 3 / 5) :
    ‖fdBoundaryFun H t‖ = 1 := by
  rw [fdBoundaryFun_seg3_eq h1 h2, norm_exp_ofReal_mul_I]

/-! ### The key trigonometric identity for distances on the unit circle

For points on the unit circle, `‖exp(iα) - exp(iβ)‖ = 2|sin((α - β)/2)|`. -/

theorem norm_exp_I_sub {α β : ℝ} :
    ‖exp (↑α * I) - exp (↑β * I)‖ = 2 * |Real.sin ((α - β) / 2)| := by
  rw [show (↑α : ℂ) * I = ↑((α + β) / 2 + (α - β) / 2) * I from by push_cast; ring,
      show (↑β : ℂ) * I = ↑((α + β) / 2 - (α - β) / 2) * I from by push_cast; ring]
  set m := (α + β) / 2
  set d := (α - β) / 2
  rw [show (↑(m + d) : ℂ) * I = ↑m * I + ↑d * I from by push_cast; ring,
      show (↑(m - d) : ℂ) * I = ↑m * I + -(↑d * I) from by push_cast; ring,
      exp_add, exp_add,
      show exp (↑m * I) * exp (↑d * I) - exp (↑m * I) * exp (-(↑d * I)) =
        exp (↑m * I) * (exp (↑d * I) - exp (-(↑d * I))) from by ring,
      Complex.norm_mul, norm_exp_ofReal_mul_I, one_mul]
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin,
      show -(↑d * I) = ↑(-d) * I from by push_cast; ring,
      exp_mul_I, ← ofReal_cos, ← ofReal_sin,
      Real.cos_neg, Real.sin_neg]
  rw [show (↑(Real.cos d) : ℂ) + ↑(Real.sin d) * I -
      (↑(Real.cos d) + ↑(-Real.sin d) * I) = ↑(2 * Real.sin d) * I from by push_cast; ring,
      Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_mul, show |(2 : ℝ)| = 2 from abs_of_pos (by norm_num)]

/-! ### ρ as exponential -/

theorem rhoPlusOne_eq_exp : rhoPlusOne = exp (↑(Real.pi / 3) * I) := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
  simp only [rhoPlusOne]; push_cast; ring

theorem rho_eq_exp : rho = exp (↑(2 * Real.pi / 3) * I) := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  simp only [rho]; push_cast; ring

theorem I_eq_exp_pi_half : (I : ℂ) = exp (↑(Real.pi / 2) * I) := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]; simp

/-! ### Distance from I on arc segments -/

/-- Distance from `I` on segment 2 of the FD boundary. -/
theorem norm_fdBoundaryFun_sub_I_seg2 {H : ℝ} {t : ℝ}
    (h1 : 1 / 5 < t) (h2 : t ≤ 2 / 5) :
    ‖fdBoundaryFun H t - I‖ =
      2 * |Real.sin (5 * (t - 2 / 5) * Real.pi / 12)| := by
  suffices h : ‖exp (↑(seg2Angle t) * I) - exp (↑(Real.pi / 2) * I)‖ =
      2 * |Real.sin (5 * (t - 2 / 5) * Real.pi / 12)| by
    rw [fdBoundaryFun_seg2_eq h1 h2]; convert h using 3; exact I_eq_exp_pi_half
  rw [norm_exp_I_sub]
  congr 1; simp only [seg2Angle]; ring_nf

/-- Distance from `I` on segment 3 of the FD boundary. -/
theorem norm_fdBoundaryFun_sub_I_seg3 {H : ℝ} {t : ℝ}
    (h1 : 2 / 5 < t) (h2 : t ≤ 3 / 5) :
    ‖fdBoundaryFun H t - I‖ =
      2 * |Real.sin (5 * (t - 2 / 5) * Real.pi / 12)| := by
  suffices h : ‖exp (↑(seg3Angle t) * I) - exp (↑(Real.pi / 2) * I)‖ =
      2 * |Real.sin (5 * (t - 2 / 5) * Real.pi / 12)| by
    rw [fdBoundaryFun_seg3_eq h1 h2]; convert h using 3; exact I_eq_exp_pi_half
  rw [norm_exp_I_sub]
  congr 1; simp only [seg3Angle]; ring_nf

/-! ### Distance from ρ+1 on segment 2 -/

/-- Distance from `ρ+1` on segment 2 of the FD boundary. -/
theorem norm_fdBoundaryFun_sub_rhoPlusOne_seg2 {H : ℝ} {t : ℝ}
    (h1 : 1 / 5 < t) (h2 : t ≤ 2 / 5) :
    ‖fdBoundaryFun H t - rhoPlusOne‖ =
      2 * |Real.sin (5 * (t - 1 / 5) * Real.pi / 12)| := by
  suffices h : ‖exp (↑(seg2Angle t) * I) - exp (↑(Real.pi / 3) * I)‖ =
      2 * |Real.sin (5 * (t - 1 / 5) * Real.pi / 12)| by
    rw [fdBoundaryFun_seg2_eq h1 h2, rhoPlusOne_eq_exp]; exact h
  rw [norm_exp_I_sub]
  congr 1; simp only [seg2Angle]; ring_nf

/-! ### Distance from ρ on segment 3 -/

/-- Distance from `ρ` on segment 3 of the FD boundary. -/
theorem norm_fdBoundaryFun_sub_rho_seg3 {H : ℝ} {t : ℝ}
    (h1 : 2 / 5 < t) (h2 : t ≤ 3 / 5) :
    ‖fdBoundaryFun H t - rho‖ =
      2 * |Real.sin (5 * (t - 3 / 5) * Real.pi / 12)| := by
  suffices h : ‖exp (↑(seg3Angle t) * I) - exp (↑(2 * Real.pi / 3) * I)‖ =
      2 * |Real.sin (5 * (t - 3 / 5) * Real.pi / 12)| by
    rw [fdBoundaryFun_seg3_eq h1 h2, rho_eq_exp]; exact h
  rw [norm_exp_I_sub]
  congr 1; simp only [seg3Angle]; ring_nf

/-! ### Segment avoidance for I -/

/-- Segment 1 (right vertical, re = 1/2) avoids `I` (re = 0). -/
theorem fdBoundaryFun_ne_I_of_seg1 {H : ℝ} {t : ℝ} (ht : t ≤ 1 / 5) :
    fdBoundaryFun H t ≠ I := by
  simp only [fdBoundaryFun, ht, ite_true]
  intro heq
  have hre := congr_arg re heq
  simp [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im] at hre

/-- Segment 4 (left vertical, re = -1/2) avoids `I` (re = 0). -/
theorem fdBoundaryFun_ne_I_of_seg4 {H : ℝ} {t : ℝ}
    (h1 : 3 / 5 < t) (h2 : t ≤ 4 / 5) :
    fdBoundaryFun H t ≠ I := by
  simp only [fdBoundaryFun, show ¬t ≤ 1 / 5 from not_le.mpr (by linarith),
    show ¬t ≤ 2 / 5 from not_le.mpr (by linarith),
    show ¬t ≤ 3 / 5 from not_le.mpr h1, h2, ite_true, ite_false]
  intro heq
  have hre := congr_arg re heq
  simp [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, sub_re] at hre

/-- Segment 5 (horizontal, im = H) avoids `I` (im = 1) when `H > 1`. -/
theorem fdBoundaryFun_ne_I_of_seg5 {H : ℝ} (hH : H > 1) {t : ℝ}
    (h1 : 4 / 5 < t) :
    fdBoundaryFun H t ≠ I := by
  simp only [fdBoundaryFun, show ¬t ≤ 1 / 5 from not_le.mpr (by linarith),
    show ¬t ≤ 2 / 5 from not_le.mpr (by linarith),
    show ¬t ≤ 3 / 5 from not_le.mpr (by linarith),
    show ¬t ≤ 4 / 5 from not_le.mpr h1, ite_false]
  intro heq
  have lhs_im : (-1 / 2 + 5 * (↑t - 4 / 5) + ↑H * I : ℂ).im = H := by
    simp [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, sub_im]
  have him := congr_arg im heq
  rw [lhs_im] at him; simp only [I_im] at him; linarith

/-! ### Positive distance from I on non-arc segments -/

/-- On segment 1, the real part is 1/2, so distance from `I` is at least 1/2. -/
theorem norm_fdBoundaryFun_sub_I_ge_seg1 {H : ℝ} {t : ℝ} (ht : t ≤ 1 / 5) :
    1 / 2 ≤ ‖fdBoundaryFun H t - I‖ := by
  have hre : (fdBoundaryFun H t - I).re = 1 / 2 := by
    simp only [fdBoundaryFun, ht, ite_true]
    simp [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
  calc (1 : ℝ) / 2 = |(fdBoundaryFun H t - I).re| := by rw [hre, abs_of_pos (by norm_num)]
    _ ≤ ‖fdBoundaryFun H t - I‖ := Complex.abs_re_le_norm _

/-- On segment 4, the real part is -1/2, so distance from `I` is at least 1/2. -/
theorem norm_fdBoundaryFun_sub_I_ge_seg4 {H : ℝ} {t : ℝ}
    (h1 : 3 / 5 < t) (h2 : t ≤ 4 / 5) :
    1 / 2 ≤ ‖fdBoundaryFun H t - I‖ := by
  have hre : (fdBoundaryFun H t - I).re = -1 / 2 := by
    simp only [fdBoundaryFun, show ¬t ≤ 1 / 5 from not_le.mpr (by linarith),
      show ¬t ≤ 2 / 5 from not_le.mpr (by linarith),
      show ¬t ≤ 3 / 5 from not_le.mpr h1, h2, ite_true, ite_false]
    simp [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
  calc (1 : ℝ) / 2 = |(fdBoundaryFun H t - I).re| := by
        rw [hre]; norm_num
    _ ≤ ‖fdBoundaryFun H t - I‖ := Complex.abs_re_le_norm _

/-! ### Norm of ρ and ρ+1 -/

theorem norm_rho : ‖rho‖ = 1 := by
  rw [Complex.norm_def, normSq_apply, rho]
  simp [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
        add_im, mul_im, ofReal_re, I_re, I_im, ofReal_im]
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith

theorem norm_rhoPlusOne : ‖rhoPlusOne‖ = 1 := by
  rw [Complex.norm_def, normSq_apply, rhoPlusOne]
  simp [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
        add_im, mul_im, ofReal_re, I_re, I_im, ofReal_im]
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith

/-! ### Segment 1 avoids ρ+1 except at endpoint -/

theorem fdBoundaryFun_ne_rhoPlusOne_seg1 {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    {t : ℝ} (_ : 0 ≤ t) (ht2 : t < 1 / 5) :
    fdBoundaryFun H t ≠ rhoPlusOne := by
  simp only [fdBoundaryFun, show t ≤ 1 / 5 from le_of_lt ht2, ite_true, rhoPlusOne]
  intro heq
  have lhs_im : (1 / 2 + (↑H - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I : ℂ).im =
      H - 5 * t * (H - Real.sqrt 3 / 2) := by
    simp [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, sub_re, sub_im, mul_re, mul_im]
  have rhs_im : (1 / 2 + ↑(Real.sqrt 3) / 2 * I : ℂ).im = Real.sqrt 3 / 2 := by
    simp [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im]
  have him := congr_arg im heq
  rw [lhs_im, rhs_im] at him
  nlinarith [mul_pos (show 0 < 1 - 5 * t from by linarith)
    (show 0 < H - Real.sqrt 3 / 2 from by linarith)]

/-! ### Segment 4 avoids ρ except at endpoint -/

theorem fdBoundaryFun_ne_rho_seg4 {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    {t : ℝ} (h1 : 3 / 5 < t) (h2 : t ≤ 4 / 5) :
    fdBoundaryFun H t ≠ rho := by
  simp only [fdBoundaryFun, show ¬t ≤ 1 / 5 from not_le.mpr (by linarith),
    show ¬t ≤ 2 / 5 from not_le.mpr (by linarith),
    show ¬t ≤ 3 / 5 from not_le.mpr h1, h2, ite_true, ite_false, rho]
  intro heq
  have lhs_im : (-1 / 2 + (↑(Real.sqrt 3) / 2 + 5 * (↑t - 3 / 5) *
      (↑H - ↑(Real.sqrt 3) / 2)) * I : ℂ).im =
      Real.sqrt 3 / 2 + 5 * (t - 3 / 5) * (H - Real.sqrt 3 / 2) := by
    simp [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, sub_re, sub_im, mul_re, mul_im,
      add_re]
  have rhs_im : (-1 / 2 + ↑(Real.sqrt 3) / 2 * I : ℂ).im = Real.sqrt 3 / 2 := by
    simp [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im]
  have him := congr_arg im heq
  rw [lhs_im, rhs_im] at him
  nlinarith [mul_pos (show 0 < 5 * (t - 3 / 5) from by linarith)
    (show 0 < H - Real.sqrt 3 / 2 from by linarith)]

/-! ### Positive distance from ρ+1 / ρ on segments 1 / 4 -/

theorem norm_fdBoundaryFun_sub_rhoPlusOne_pos_seg1 {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    {t : ℝ} (ht1 : 0 ≤ t) (ht2 : t < 1 / 5) :
    0 < ‖fdBoundaryFun H t - rhoPlusOne‖ := by
  rw [norm_pos_iff]
  exact sub_ne_zero.mpr (fdBoundaryFun_ne_rhoPlusOne_seg1 hH ht1 ht2)

theorem norm_fdBoundaryFun_sub_rho_pos_seg4 {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    {t : ℝ} (h1 : 3 / 5 < t) (h2 : t ≤ 4 / 5) :
    0 < ‖fdBoundaryFun H t - rho‖ := by
  rw [norm_pos_iff]
  exact sub_ne_zero.mpr (fdBoundaryFun_ne_rho_seg4 hH h1 h2)

/-! ### sqrt 3 / 2 bounds -/

theorem sqrt3_div2_pos : (0 : ℝ) < Real.sqrt 3 / 2 :=
  div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)

theorem one_lt_sqrt3 : (1 : ℝ) < Real.sqrt 3 := by
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-! ### The FD boundary `extend` agrees with `fdBoundaryFun` at Icc points -/

theorem fdBoundaryPath_extend_eq {H : ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fdBoundaryPath H).extend t = fdBoundaryFun H t := by
  simp only [Path.extend, Set.IccExtend, fdBoundaryPath, ContinuousMap.coe_mk, Function.comp_def]
  show fdBoundaryFun H (Set.projIcc 0 1 zero_le_one t : ℝ) = fdBoundaryFun H t
  congr 1
  exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ht)

theorem fdBoundary_extend_eq {H : ℝ} {hH : H > Real.sqrt 3 / 2} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (fdBoundary H hH).toPath.extend t = fdBoundaryFun H t :=
  fdBoundaryPath_extend_eq ht

/-! ### The three elliptic point crossing values via extend -/

theorem fdBoundary_at_two_fifths {H : ℝ} {hH : H > Real.sqrt 3 / 2} :
    (fdBoundary H hH).toPath.extend (2 / 5) = I := by
  rw [fdBoundary_extend_eq (by constructor <;> norm_num : (2 : ℝ) / 5 ∈ Icc 0 1)]
  exact fdBoundaryFun_two_fifths_eq_I H

theorem fdBoundary_at_one_fifth {H : ℝ} {hH : H > Real.sqrt 3 / 2} :
    (fdBoundary H hH).toPath.extend (1 / 5) = rhoPlusOne := by
  rw [fdBoundary_extend_eq (by constructor <;> norm_num : (1 : ℝ) / 5 ∈ Icc 0 1)]
  exact fdBoundaryFun_one_fifth_eq_rhoPlusOne H

theorem fdBoundary_at_three_fifths {H : ℝ} {hH : H > Real.sqrt 3 / 2} :
    (fdBoundary H hH).toPath.extend (3 / 5) = rho := by
  rw [fdBoundary_extend_eq (by constructor <;> norm_num : (3 : ℝ) / 5 ∈ Icc 0 1)]
  exact fdBoundaryFun_three_fifths_eq_rho H

/-! ### Segment 2/3 angle ranges -/

theorem seg2Angle_mem_Icc {t : ℝ} (h1 : 1 / 5 ≤ t) (h2 : t ≤ 2 / 5) :
    seg2Angle t ∈ Icc (Real.pi / 3) (Real.pi / 2) := by
  simp only [seg2Angle]
  constructor <;> nlinarith [Real.pi_pos]

theorem seg3Angle_mem_Icc {t : ℝ} (h1 : 2 / 5 ≤ t) (h2 : t ≤ 3 / 5) :
    seg3Angle t ∈ Icc (Real.pi / 2) (2 * Real.pi / 3) := by
  simp only [seg3Angle]
  constructor <;> nlinarith [Real.pi_pos]

/-! ### Algebraic winding number values

These record the algebraic facts that reduce PV limits to winding numbers. -/

/-- `-πi / (2πi) = -1/2`, giving the winding number at `I`. -/
theorem neg_pi_I_div_two_pi_I :
    -(↑Real.pi * I) / (2 * ↑Real.pi * I) = -1 / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- `(-π/3 · i) / (2πi) = -1/6`, giving the winding number at `ρ` and `ρ+1`. -/
theorem neg_pi_third_I_div_two_pi_I :
    -(↑Real.pi / 3 * I) / (2 * ↑Real.pi * I) = -1 / 6 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp; ring

end
