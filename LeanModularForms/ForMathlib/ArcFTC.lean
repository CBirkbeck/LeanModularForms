/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.WindingWeightProofs

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

open Complex Set

noncomputable section

/-- The argument of `exp(iθ)` is `θ` for `θ ∈ (-π, π]`. -/
theorem arg_exp_mul_I (θ : ℝ) (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    arg (exp (↑θ * I)) = θ := by
  simpa [exp_mul_I] using Complex.arg_cos_add_sin_mul_I hθ

/-- The argument of `r * I` is `π/2` for `r > 0`. -/
theorem arg_ofReal_mul_I (r : ℝ) (hr : 0 < r) :
    arg (↑r * I) = Real.pi / 2 := by
  rw [Complex.arg_real_mul _ hr, Complex.arg_I]

/-- The derivative of the arc parametrization.
`d/dt exp(i·θ(t)) = (5π/6) · i · exp(i·θ(t))`. -/
theorem fdBoundary_arc_deriv_eq (t : ℝ) :
    deriv (fun s => exp (↑(fdArcAngle s) * I)) t =
      ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I) := by
  simp only [fdArcAngle]
  have hd : HasDerivAt (fun s : ℝ =>
      Real.pi / 3 + (5 * s - 1) * (Real.pi / 6)) (5 * Real.pi / 6) t := by
    convert (((hasDerivAt_id t).const_mul 5).sub_const 1).mul_const (Real.pi / 6)
      |>.const_add (Real.pi / 3) using 1
    ring
  rw [(hd.ofReal_comp.mul_const I).cexp.deriv]; push_cast; ring

/-- Arc tangent at `t = 2/5`: `γ'(2/5) = -(5π/6)` (leftward at `i`). -/
theorem fdBoundary_arc_deriv_at_two_fifths :
    deriv (fun s => exp (↑(fdArcAngle s) * I)) (2/5 : ℝ) =
      -(↑(5 * Real.pi / 6) : ℂ) := by
  rw [fdBoundary_arc_deriv_eq, fdArcAngle_at_two_fifths, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp [mul_assoc]

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

/-- Right vertical (segment 1) tangent: downward. -/
theorem fdBoundary_seg1_deriv (H t : ℝ) :
    deriv (fun s => (1 : ℂ) / 2 +
      (↑H - 5 * ↑s * (↑H - ↑(Real.sqrt 3) / 2)) * I) t =
      -(5 * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (H : ℂ) - 5 * ↑s * (↑H - ↑(Real.sqrt 3) / 2))
      (-(5 * (↑H - ↑(Real.sqrt 3) / 2))) t := by
    convert (h1.const_mul ((5 : ℂ) * (↑H - ↑(Real.sqrt 3) / 2))).const_sub (H : ℂ) using 1
    · funext s; ring
    · ring
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
    convert ((h1.const_mul (5 : ℂ)).sub_const (3 : ℂ)).mul_const (↑H - ↑(Real.sqrt 3) / 2)
      |>.const_add (↑(Real.sqrt 3) / 2 : ℂ) using 1
    ring
  exact ((hasDerivAt_const t ((-1 : ℂ) / 2)).add (h2.mul_const I)).deriv.trans (by ring)

/-- `i · exp(iπ/3) = exp(i·5π/6)`. -/
theorem I_mul_exp_pi_third :
    I * exp (↑(Real.pi / 3) * I) = exp (↑(5 * Real.pi / 6) * I) := by
  rw [show ((5 * Real.pi / 6 : ℝ) : ℂ) * I = ↑Real.pi / 2 * I + ↑(Real.pi / 3) * I
      from by push_cast; ring, exp_add, Complex.exp_pi_div_two_mul_I]

/-- The arg of the right tangent at `ρ+1`: `5π/6`. -/
theorem arg_right_tangent_rhoPlusOne :
    arg (I * exp (↑(Real.pi / 3) * I)) = 5 * Real.pi / 6 := by
  rw [I_mul_exp_pi_third]
  exact arg_exp_mul_I _ ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- The arg of the negated left tangent at `ρ+1` is `π/2`. -/
theorem arg_neg_left_tangent_rhoPlusOne (H : ℝ) (hH : fdHeightValid H) :
    arg (5 * (↑H - ↑(Real.sqrt 3) / 2) * I) = Real.pi / 2 := by
  unfold fdHeightValid at hH
  rw [show (5 * (↑H - ↑(Real.sqrt 3) / 2) * I : ℂ) =
      ↑(5 * (H - Real.sqrt 3 / 2)) * I from by push_cast; ring]
  exact arg_ofReal_mul_I _ (by linarith)

/-- The crossing angle at `ρ+1` is `π/3`. -/
theorem fdBoundary_crossing_angle_at_rhoPlusOne (H : ℝ) (hH : fdHeightValid H) :
    arg (I * exp (↑(Real.pi / 3) * I)) -
      arg (5 * (↑H - ↑(Real.sqrt 3) / 2) * I) = Real.pi / 3 := by
  rw [arg_right_tangent_rhoPlusOne, arg_neg_left_tangent_rhoPlusOne H hH]; ring

/-- `i · exp(i·2π/3) = exp(i·(-5π/6))`. -/
theorem I_mul_exp_two_pi_third :
    I * exp (↑(2 * Real.pi / 3) * I) = exp (↑(-5 * Real.pi / 6) * I) := by
  rw [show (↑(-5 * Real.pi / 6) * I : ℂ) = ↑Real.pi / 2 * I + ↑(2 * Real.pi / 3) * I -
      2 * Real.pi * I from by push_cast; ring,
    exp_sub, exp_add, Complex.exp_two_pi_mul_I, div_one, Complex.exp_pi_div_two_mul_I]

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
    rw [show (-5 * Real.pi / 6 : ℝ) = -(Real.pi - Real.pi / 6) from by ring, Real.sin_neg,
      Real.sin_pi_sub]
    linarith [Real.sin_pos_of_pos_of_lt_pi (show (0:ℝ) < Real.pi / 6 by linarith [Real.pi_pos])
      (show Real.pi / 6 < Real.pi by linarith [Real.pi_pos])]

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
  rw [neg_neg, ← ofReal_neg, Complex.arg_ofReal_of_neg (by linarith [Real.pi_pos]),
    Complex.arg_ofReal_of_nonneg (by positivity)]; ring

/-- `-(πi)/(2πi) = -1/2`. -/
theorem arcFTC_limit_target_I :
    -(↑Real.pi * I) / (2 * ↑Real.pi * I) = (-1 / 2 : ℂ) := by
  field_simp

/-- `-(πi/3)/(2πi) = -1/6`. -/
theorem arcFTC_limit_target_rho :
    -(↑Real.pi / 3 * I) / (2 * ↑Real.pi * I) = (-1 / 6 : ℂ) := by
  field_simp; ring

/-- `2πi · (-1/2) = -πi`. -/
theorem arcFTC_pv_target_I :
    2 * ↑Real.pi * I * (-1 / 2 : ℂ) = -(↑Real.pi * I) := by ring

/-- `2πi · (-1/6) = -πi/3`. -/
theorem arcFTC_pv_target_rho :
    2 * ↑Real.pi * I * (-1 / 6 : ℂ) = -(↑Real.pi / 3 * I) := by ring

/-- `2/5 ∈ (0, 1)`. -/
theorem two_fifths_mem_Ioo : (2 : ℝ)/5 ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num

/-- `1/5 ∈ (0, 1)`. -/
theorem one_fifth_mem_Ioo : (1 : ℝ)/5 ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num

/-- `3/5 ∈ (0, 1)`. -/
theorem three_fifths_mem_Ioo : (3 : ℝ)/5 ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num

end
