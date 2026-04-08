/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.WindingWeightProofs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Arc FTC — Crossing Angles and Winding Numbers for FD Boundary

This file computes the crossing angles at the three on-curve points of the
fundamental domain boundary (`i`, `ρ`, `ρ+1`) and provides geometric lemmas
for the `ArcFTCHyp` construction.

## Mathematical content

The FD boundary crosses three special points:
- `i` at `t₀ = 2/5` (smooth crossing on the unit circle arc)
- `ρ` at `t₀ = 3/5` (corner: arc meets left vertical)
- `ρ+1` at `t₀ = 1/5` (corner: right vertical meets arc)

At each crossing, the **FTC limit** `L` satisfies `L/(2πi) = -α/(2π)`:
- At `i`: `L = -πi`, giving winding number `-1/2`
- At `ρ`, `ρ+1`: `L = -πi/3`, giving winding number `-1/6`

## Strategy

1. Compute tangent directions on each segment of the FD boundary
2. Compute the arg of each tangent at the crossing points
3. Derive the crossing angle `α = arg(L_right) - arg(-L_left)`
4. Verify consistency of FTC limits with winding numbers

## Main results

### Auxiliary
* `sin_abs_le_abs` — `|sin x| ≤ |x|` when `|x| ≤ π`
* `arg_exp_mul_I` — `arg(exp(iθ)) = θ` for `θ ∈ (-π, π]`
* `arg_ofReal_mul_I` — `arg(r·I) = π/2` for `r > 0`

### Tangent directions
* `fdBoundary_arc_deriv_eq` — derivative of arc parametrization
* `fdBoundary_arc_deriv_at_two_fifths` — arc tangent at `i`
* `fdBoundary_seg1_deriv` — right vertical tangent
* `fdBoundary_seg4_deriv` — left vertical tangent

### Crossing angles
* `fdBoundary_crossing_angle_at_rhoPlusOne` — angle at `ρ+1` is `π/3`
* `fdBoundary_crossing_angle_at_rho` — angle at `ρ` is `π/3`
* `fdBoundary_angle_at_I_partition` — angle at `i` is `π`

### Limit targets
* `arcFTC_limit_target_I` — `-(πi)/(2πi) = -1/2`
* `arcFTC_limit_target_rho` — `-(πi/3)/(2πi) = -1/6`

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ## Part 1: Auxiliary lemmas -/

/-- `|sin x| ≤ |x|` when `|x| ≤ π`. Uses monotonicity of sin on `[0, π]`. -/
theorem sin_abs_le_abs (x : ℝ) (hx : |x| ≤ Real.pi) : |Real.sin x| ≤ |x| := by
  rcases le_or_gt 0 x with hx_nn | hx_neg
  · rw [abs_of_nonneg hx_nn]
    rcases eq_or_lt_of_le hx_nn with rfl | hx_pos
    · simp
    · have : 0 ≤ Real.sin x :=
        Real.sin_nonneg_of_nonneg_of_le_pi hx_nn (by rwa [abs_of_nonneg hx_nn] at hx)
      rw [abs_of_nonneg this]
      exact (Real.sin_lt hx_pos).le
  · rw [abs_of_neg hx_neg]
    have hx' : 0 < -x := neg_pos.mpr hx_neg
    have : Real.sin x ≤ 0 := by
      rw [← neg_nonneg, ← Real.sin_neg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi hx'.le (by rwa [abs_of_neg hx_neg] at hx)
    rw [abs_of_nonpos this, ← Real.sin_neg]
    exact (Real.sin_lt hx').le

/-- The argument of `exp(iθ)` is `θ` for `θ ∈ (-π, π]`. -/
theorem arg_exp_mul_I (θ : ℝ) (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    arg (exp (↑θ * I)) = θ := by
  rw [exp_mul_I]; exact Complex.arg_cos_add_sin_mul_I hθ

/-- The argument of `r * I` is `π/2` for `r > 0`. -/
theorem arg_ofReal_mul_I (r : ℝ) (hr : 0 < r) :
    arg (↑r * I) = Real.pi / 2 := by
  have h : ↑r * I = exp (↑(Real.pi / 2) * I) * ↑r := by
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast; ring
  rw [h, Complex.arg_mul_real hr]
  exact arg_exp_mul_I _ ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- The argument of a negative real number is `π`. -/
theorem arg_neg_ofReal (r : ℝ) (hr : 0 < r) :
    arg (-(↑r : ℂ)) = Real.pi := by
  rw [Complex.arg_eq_pi_iff]; constructor <;> simp <;> linarith

/-- The argument of a positive real number is `0`. -/
theorem arg_pos_ofReal (r : ℝ) (hr : 0 < r) :
    arg (↑r : ℂ) = 0 := by
  simp [Complex.arg, ofReal_re, ofReal_im, hr.le]

/-! ## Part 2: Arc tangent directions -/

/-- The derivative of the arc parametrization.
`d/dt exp(i·θ(t)) = (5π/6) · i · exp(i·θ(t))`. -/
theorem fdBoundary_arc_deriv_eq (t : ℝ) :
    deriv (fun s => exp (↑(fdArcAngle s) * I)) t =
      ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I) := by
  have h1 : (fun s => exp (↑(fdArcAngle s) * I)) =
      (fun s => exp (↑(Real.pi / 3 + (5 * s - 1) * (Real.pi / 6)) * I)) := by
    ext s; simp only [fdArcAngle]
  rw [h1]
  have hd : HasDerivAt (fun s : ℝ =>
      Real.pi / 3 + (5 * s - 1) * (Real.pi / 6)) (5 * Real.pi / 6) t := by
    have := ((hasDerivAt_id t).const_mul 5).sub_const 1 |>.mul_const (Real.pi / 6)
      |>.const_add (Real.pi / 3)
    convert this using 1; ring
  rw [(hd.ofReal_comp.mul_const I).cexp.deriv]
  simp only [fdArcAngle]; push_cast; ring

/-- Arc tangent at `t = 2/5`: `γ'(2/5) = -(5π/6)` (leftward at `i`). -/
theorem fdBoundary_arc_deriv_at_two_fifths :
    deriv (fun s => exp (↑(fdArcAngle s) * I)) (2/5 : ℝ) =
      -(↑(5 * Real.pi / 6) : ℂ) := by
  rw [fdBoundary_arc_deriv_eq, fdArcAngle_at_two_fifths,
    exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp only [ofReal_zero, ofReal_one, zero_add, one_mul, mul_assoc, I_mul_I]
  push_cast; ring

/-- Arc tangent at `t = 1/5` (right tangent at `ρ+1`). -/
theorem fdBoundary_arc_deriv_at_one_fifth :
    deriv (fun s => exp (↑(fdArcAngle s) * I)) (1/5 : ℝ) =
      ↑(5 * Real.pi / 6) * I * exp (↑(Real.pi / 3) * I) := by
  rw [fdBoundary_arc_deriv_eq, fdArcAngle_at_one_fifth]

/-- Arc tangent at `t = 3/5` (left tangent at `ρ`). -/
theorem fdBoundary_arc_deriv_at_three_fifths :
    deriv (fun s => exp (↑(fdArcAngle s) * I)) (3/5 : ℝ) =
      ↑(5 * Real.pi / 6) * I * exp (↑(2 * Real.pi / 3) * I) := by
  rw [fdBoundary_arc_deriv_eq, fdArcAngle_at_three_fifths]

/-! ### Vertical segment tangent directions -/

/-- Right vertical (segment 1) tangent: downward. -/
theorem fdBoundary_seg1_deriv (H t : ℝ) :
    deriv (fun s => (1 : ℂ) / 2 +
      (↑H - 5 * ↑s * (↑H - ↑(Real.sqrt 3) / 2)) * I) t =
      -(5 * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (H : ℂ) - 5 * ↑s * (↑H - ↑(Real.sqrt 3) / 2))
      (-(5 * (↑H - ↑(Real.sqrt 3) / 2))) t := by
    have hd := h1.const_mul ((5 : ℂ) * (↑H - ↑(Real.sqrt 3) / 2))
    have := hd.const_sub (H : ℂ)
    convert this using 1
    · funext s; push_cast; ring
    · push_cast; ring
  exact ((hasDerivAt_const t ((1 : ℂ) / 2)).add (h2.mul_const I)).deriv.trans (by ring)

/-- Left vertical (segment 4) tangent: upward. -/
theorem fdBoundary_seg4_deriv (H t : ℝ) :
    deriv (fun s => (-1 : ℂ) / 2 +
      (↑(Real.sqrt 3) / 2 + (5 * ↑s - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I) t =
      5 * (↑H - ↑(Real.sqrt 3) / 2) * I := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ =>
      (↑(Real.sqrt 3) / 2 : ℂ) + (5 * ↑s - 3) * (↑H - ↑(Real.sqrt 3) / 2))
      (5 * (↑H - ↑(Real.sqrt 3) / 2)) t := by
    have hd := ((h1.const_mul (5 : ℂ)).sub_const (3 : ℂ)).mul_const (↑H - ↑(Real.sqrt 3) / 2)
      |>.const_add (↑(Real.sqrt 3) / 2 : ℂ)
    convert hd using 1 <;> first | (funext s; push_cast; ring) | ring
  exact ((hasDerivAt_const t ((-1 : ℂ) / 2)).add (h2.mul_const I)).deriv.trans (by ring)

/-! ## Part 3: Crossing angle computations -/

/-- `i · exp(iπ/3) = exp(i·5π/6)`. -/
theorem I_mul_exp_pi_third :
    I * exp (↑(Real.pi / 3) * I) = exp (↑(5 * Real.pi / 6) * I) := by
  rw [show (5 * Real.pi / 6 : ℝ) = Real.pi / 2 + Real.pi / 3 from by ring,
    ofReal_add, add_mul, exp_add]
  congr 1
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

/-- The arg of the right tangent at `ρ+1`: `5π/6`. -/
theorem arg_right_tangent_rhoPlusOne :
    arg (I * exp (↑(Real.pi / 3) * I)) = 5 * Real.pi / 6 := by
  rw [I_mul_exp_pi_third]
  exact arg_exp_mul_I _ ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- The arg of the negated left tangent at `ρ+1` is `π/2`. -/
theorem arg_neg_left_tangent_rhoPlusOne (H : ℝ) (hH : fdHeightValid H) :
    arg (5 * (↑H - ↑(Real.sqrt 3) / 2) * I) = Real.pi / 2 := by
  have hH' : (0 : ℝ) < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  rw [show (5 * (↑H - ↑(Real.sqrt 3) / 2) * I : ℂ) =
      ↑(5 * (H - Real.sqrt 3 / 2)) * I from by push_cast; ring]
  exact arg_ofReal_mul_I _ (by positivity)

/-- The crossing angle at `ρ+1` is `π/3`. -/
theorem fdBoundary_crossing_angle_at_rhoPlusOne (H : ℝ) (hH : fdHeightValid H) :
    arg (I * exp (↑(Real.pi / 3) * I)) -
      arg (5 * (↑H - ↑(Real.sqrt 3) / 2) * I) = Real.pi / 3 := by
  rw [arg_right_tangent_rhoPlusOne, arg_neg_left_tangent_rhoPlusOne H hH]; ring

/-- `i · exp(i·2π/3) = exp(i·(-5π/6))`. -/
theorem I_mul_exp_two_pi_third :
    I * exp (↑(2 * Real.pi / 3) * I) = exp (↑(-5 * Real.pi / 6) * I) := by
  rw [exp_mul_I, exp_mul_I]
  simp only [← ofReal_cos, ← ofReal_sin]
  rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [show (-5 * Real.pi / 6 : ℝ) = -(Real.pi - Real.pi / 6) from by ring,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_six, Real.sin_pi_div_six]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, ofReal_re, ofReal_im]

/-- The arg of the left tangent at `ρ`: `-5π/6`. -/
theorem arg_left_tangent_rho :
    arg (I * exp (↑(2 * Real.pi / 3) * I)) = -5 * Real.pi / 6 := by
  rw [I_mul_exp_two_pi_third]
  exact arg_exp_mul_I _ ⟨by nlinarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- The arg of `-(i · exp(i·2π/3))`: `π/6`.
Since `im(i · exp(i·2π/3)) < 0`, we have `arg(-z) = arg(z) + π`. -/
theorem arg_neg_left_tangent_rho :
    arg (-(I * exp (↑(2 * Real.pi / 3) * I))) = Real.pi / 6 := by
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg]
  · rw [arg_left_tangent_rho]; ring
  · rw [I_mul_exp_two_pi_third, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]
    rw [show (-5 * Real.pi / 6 : ℝ) = -(Real.pi - Real.pi / 6) from by ring, Real.sin_neg]
    have : 0 < Real.sin (Real.pi - Real.pi / 6) := by
      rw [Real.sin_pi_sub]
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    linarith

/-- The arg of the right tangent at `ρ` (upward vertical): `π/2`. -/
theorem arg_right_tangent_rho (H : ℝ) (hH : fdHeightValid H) :
    arg (5 * (↑H - ↑(Real.sqrt 3) / 2) * I) = Real.pi / 2 :=
  arg_neg_left_tangent_rhoPlusOne H hH

/-- The crossing angle at `ρ` is `π/3`. -/
theorem fdBoundary_crossing_angle_at_rho (H : ℝ) (hH : fdHeightValid H) :
    arg (5 * (↑H - ↑(Real.sqrt 3) / 2) * I) -
      arg (-(I * exp (↑(2 * Real.pi / 3) * I))) = Real.pi / 3 := by
  rw [arg_right_tangent_rho H hH, arg_neg_left_tangent_rho]; ring

/-- The crossing angle at `i` (partition point) is `π`.
Both tangent directions are `-(5π/6)` (leftward), so
`arg(-(5π/6)) - arg(5π/6) = π - 0 = π`. -/
theorem fdBoundary_angle_at_I_partition :
    arg (-(↑(5 * Real.pi / 6) : ℂ)) -
      arg (-(-(↑(5 * Real.pi / 6) : ℂ))) = Real.pi := by
  have hpi : (0 : ℝ) < 5 * Real.pi / 6 := by positivity
  rw [neg_neg, arg_neg_ofReal _ hpi, arg_pos_ofReal _ hpi]; ring

/-! ## Part 4: ArcFTCHyp limit target values -/

/-- `-(πi)/(2πi) = -1/2`. -/
theorem arcFTC_limit_target_I :
    -(↑Real.pi * I) / (2 * ↑Real.pi * I) = (-1 / 2 : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- `-(πi/3)/(2πi) = -1/6`. -/
theorem arcFTC_limit_target_rho :
    -(↑Real.pi / 3 * I) / (2 * ↑Real.pi * I) = (-1 / 6 : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp; ring

/-- `2πi · (-1/2) = -πi`. -/
theorem arcFTC_pv_target_I :
    2 * ↑Real.pi * I * (-1 / 2 : ℂ) = -(↑Real.pi * I) := by ring

/-- `2πi · (-1/6) = -πi/3`. -/
theorem arcFTC_pv_target_rho :
    2 * ↑Real.pi * I * (-1 / 6 : ℂ) = -(↑Real.pi / 3 * I) := by ring

/-! ## Part 5: Verified membership proofs -/

/-- `2/5 ∈ (0, 1)`. -/
theorem two_fifths_mem_Ioo : (2 : ℝ)/5 ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num

/-- `1/5 ∈ (0, 1)`. -/
theorem one_fifth_mem_Ioo : (1 : ℝ)/5 ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num

/-- `3/5 ∈ (0, 1)`. -/
theorem three_fifths_mem_Ioo : (3 : ℝ)/5 ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num

end
