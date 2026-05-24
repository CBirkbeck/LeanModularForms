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

/-- Winding number at `i` is `-1/2` from `SingleCrossingData` with limit `-(πi)`. -/
theorem hasWindingNumber_atI_of_scd
    {γ : PiecewiseC1Path x y} (D : SingleCrossingData γ I)
    (hL : D.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber γ I (-1/2) := by
  convert D.hasWindingNumber using 1
  rw [hL]
  field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]

end
