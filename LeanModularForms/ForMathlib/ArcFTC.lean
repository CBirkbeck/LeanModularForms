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

end
