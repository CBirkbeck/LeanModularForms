/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.ArcFTCLimit
import LeanModularForms.ForMathlib.WindingWeightProofs
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Unconditional Winding Weights Assembly

This file assembles the geometric infrastructure for computing generalized winding
numbers at the three on-curve points of the FD boundary (`i`, `ρ`, `ρ+1`).

The geometric bounds (cutoff functions, arc distance formulas, segment lower bounds)
are all proved in `WindingWeightProofs.lean` and `ArcFTC.lean`. The analytic
hypothesis (`ArcFTCHyp`) provides the FTC telescoping, integrability, and limit.

## Main results

* `hasWindingNumber_atI_of_scd` — winding number at `i` is `-1/2`
* `hasWindingNumber_atRho_of_scd` — winding number at `ρ` is `-1/6`
* `hasWindingNumber_atRhoPlusOne_of_scd` — winding number at `ρ+1` is `-1/6`
* `fdWindingData_of_singleCrossingData` — full `FDWindingData` assembly
* `arcDelta` — cutoff function `6ε/(5π)` for the `i` crossing
* `arc_near_core` — near bound via `|sin x| ≤ |x|`
* `fdBoundaryFun_log_diff_core_tendsto` — (imported) the FTC core limit at `i`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ## Part 1: Cutoff function for smooth crossing at `i` -/

/-- Arc cutoff: `δ(ε) = 6ε/(5π)`. Inverts the half-angle formula
`‖γ(t) - i‖ = 2|sin(5(t-2/5)π/12)|` via `|sin x| ≤ |x|`.

This is the appropriate delta for the near bound (upper bound on distance).
For the far bound, the exact delta should be `12·arcsin(ε/2)/(5π)`, which is
slightly larger. The near bound via `arcDelta` is used in the `ArcFTCHyp`
construction. -/
def arcDelta (ε : ℝ) : ℝ := 6 * ε / (5 * Real.pi)

theorem arcDelta_pos {ε : ℝ} (hε : 0 < ε) : 0 < arcDelta ε := by
  unfold arcDelta; positivity

theorem arcDelta_lt_one_fifth {ε : ℝ} (hε_lt : ε < 1/2) :
    arcDelta ε < 1/5 := by
  unfold arcDelta
  have hpi := Real.pi_gt_three
  rw [show (1 : ℝ)/5 = Real.pi / (5 * Real.pi) from by field_simp]
  exact div_lt_div_of_pos_right (by nlinarith) (by positivity)

theorem half_angle_factor (ε : ℝ) :
    5 * Real.pi / 12 * arcDelta ε = ε / 2 := by
  unfold arcDelta; field_simp; ring

/-! ## Part 2: Arc near bound for `i` -/

/-- On the unit circle arc, when `|t - 2/5| ≤ arcDelta ε`, the distance to `i`
is at most `ε`. Uses `|sin x| ≤ |x|` and the half-angle distance formula. -/
theorem arc_near_at_I (H : ℝ) {ε : ℝ} (hε_lt : ε < 1/2)
    {t : ℝ} (ht : |t - 2/5| ≤ arcDelta ε) :
    ‖fdBoundaryFun H t - I‖ ≤ ε := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hδ := arcDelta_lt_one_fifth hε_lt
  have hle := abs_le.mp (le_trans ht hδ.le)
  have hle' := abs_le.mp ht
  rw [fdBoundaryFun_arc_dist_I H t (by nlinarith [hle'.1, hδ]) (by linarith [hle.2]),
    show (fdArcAngle t - Real.pi / 2) / 2 = 5 * (t - 2/5) * Real.pi / 12 from by
      simp only [fdArcAngle]; ring]
  set α := 5 * (t - 2/5) * Real.pi / 12
  have hα_abs : |α| = 5 * Real.pi / 12 * |t - 2/5| := by
    rw [show α = 5 * Real.pi / 12 * (t - 2/5) from by ring, abs_mul, abs_of_pos (by positivity)]
  have hα_bound : |α| ≤ ε / 2 := by
    rw [hα_abs]
    calc 5 * Real.pi / 12 * |t - 2/5| ≤ 5 * Real.pi / 12 * arcDelta ε := by gcongr
      _ = ε / 2 := half_angle_factor ε
  calc 2 * |Real.sin α|
      ≤ 2 * |α| := by
        apply mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ ≤ 2 * (ε / 2) := by linarith
    _ = ε := by ring

/-! ## Part 3: Winding number from SingleCrossingData -/

/-- Winding number at `i` is `-1/2` from `SingleCrossingData` with limit `-(πi)`. -/
theorem hasWindingNumber_atI_of_scd
    {γ : PiecewiseC1Path x y} (D : SingleCrossingData γ I)
    (hL : D.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber γ I (-1/2) := by
  convert D.hasWindingNumber using 1
  rw [hL]; field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- Winding number at `ρ` is `-1/6` from `SingleCrossingData` with limit `-(πi/3)`. -/
theorem hasWindingNumber_atRho_of_scd
    {γ : PiecewiseC1Path x y} (D : SingleCrossingData γ ellipticPointRho)
    (hL : D.L = -(↑Real.pi / 3 * I)) :
    HasGeneralizedWindingNumber γ ellipticPointRho (-1/6) := by
  convert D.hasWindingNumber using 1
  rw [hL]; field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]; ring

/-- Winding number at `ρ+1` is `-1/6` from `SingleCrossingData` with limit `-(πi/3)`. -/
theorem hasWindingNumber_atRhoPlusOne_of_scd
    {γ : PiecewiseC1Path x y} (D : SingleCrossingData γ ellipticPointRhoPlusOne)
    (hL : D.L = -(↑Real.pi / 3 * I)) :
    HasGeneralizedWindingNumber γ ellipticPointRhoPlusOne (-1/6) := by
  convert D.hasWindingNumber using 1
  rw [hL]; field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]; ring

/-! ## Part 4: Full FDWindingData assembly -/

/-- Full `FDWindingData` from `SingleCrossingData` at each crossing point and
interior winding. This is the top-level assembler.

The three `SingleCrossingData` instances bundle all geometric and analytic
ingredients (cutoff functions, far/near bounds, FTC, integrability, and limits).
The winding weights `-1/2` and `-1/6` follow from the limit values. -/
def fdWindingData_of_singleCrossingData {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (h_int : ∀ z : ℂ, ‖z‖ > 1 → |z.re| < 1/2 → z.im > 0 → z.im < H →
      HasGeneralizedWindingNumber γ z (-1))
    (D_i : SingleCrossingData γ I)
    (hL_i : D_i.L = -(↑Real.pi * I))
    (D_rho : SingleCrossingData γ ellipticPointRho)
    (hL_rho : D_rho.L = -(↑Real.pi / 3 * I))
    (D_rho1 : SingleCrossingData γ ellipticPointRhoPlusOne)
    (hL_rho1 : D_rho1.L = -(↑Real.pi / 3 * I)) :
    FDWindingData H where
  boundary := γ
  boundary_eq := hγ
  interior_winding := h_int
  winding_at_i := hasWindingNumber_atI_of_scd D_i hL_i
  winding_at_rho := hasWindingNumber_atRho_of_scd D_rho hL_rho
  winding_at_rho_plus_one := hasWindingNumber_atRhoPlusOne_of_scd D_rho1 hL_rho1

end
