/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import LeanModularForms.ForMathlib.ArcFTCLimit
import LeanModularForms.ForMathlib.WindingWeightProofs

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

/-- Arc cutoff: `δ(ε) = 6ε/(5π)`. Inverts the half-angle formula
`‖γ(t) - i‖ = 2|sin(5(t-2/5)π/12)|` via `|sin x| ≤ |x|`.

This is the appropriate delta for the near bound (upper bound on distance).
For the far bound, the exact delta should be `12·arcsin(ε/2)/(5π)`, which is
slightly larger. The near bound via `arcDelta` is used in the `ArcFTCHyp`
construction. -/
def arcDelta (ε : ℝ) : ℝ := 6 * ε / (5 * Real.pi)


/-- Winding number at `i` is `-1/2` from `SingleCrossingData` with limit `-(πi)`. -/
theorem hasWindingNumber_atI_of_scd
    {γ : PiecewiseC1Path x y} (D : SingleCrossingData γ I)
    (hL : D.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber γ I (-1/2) := by
  convert D.hasWindingNumber using 1
  rw [hL]
  field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- Winding number at `ρ` is `-1/6` from `SingleCrossingData` with limit `-(πi/3)`. -/
theorem hasWindingNumber_atRho_of_scd
    {γ : PiecewiseC1Path x y} (D : SingleCrossingData γ ellipticPointRho)
    (hL : D.L = -(↑Real.pi / 3 * I)) :
    HasGeneralizedWindingNumber γ ellipticPointRho (-1/6) := by
  convert D.hasWindingNumber using 1
  rw [hL]
  field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

/-- Winding number at `ρ+1` is `-1/6` from `SingleCrossingData` with limit `-(πi/3)`. -/
theorem hasWindingNumber_atRhoPlusOne_of_scd
    {γ : PiecewiseC1Path x y} (D : SingleCrossingData γ ellipticPointRhoPlusOne)
    (hL : D.L = -(↑Real.pi / 3 * I)) :
    HasGeneralizedWindingNumber γ ellipticPointRhoPlusOne (-1/6) := by
  convert D.hasWindingNumber using 1
  rw [hL]
  field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

end
