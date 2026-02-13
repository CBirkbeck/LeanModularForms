/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_ModularSide
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_Boundary_Param

/-!
# Parameterized Modular Side

Height-parameterized wrappers for the modular-side identity, bridging
the parameterized q-radius `seg5_q_radius_H` to the fixed `seg5_q_radius`.

## Main Results

* `seg5_q_radius_H_eq` — bridge: `seg5_q_radius_H H_height = seg5_q_radius`
* `modular_side_of_smaller_height` — modular-side identity for any `H ≤ H_height`
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-! ## q-Radius Bridge -/

/-- The parameterized q-radius at canonical height equals the fixed q-radius. -/
theorem seg5_q_radius_H_eq : seg5_q_radius_H H_height = seg5_q_radius := rfl

/-! ## Modular Side at Smaller Height -/

/-- Modular-side identity for height `H ≤ H_height`.

When `H ≤ H_height`, the ball `closedBall(0, seg5_q_radius_H H)` is at least as large
as `closedBall(0, seg5_q_radius)`, so nonvanishing on the larger ball suffices. -/
theorem modular_side_of_smaller_height (hf : f ≠ 0)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {H : ℝ} (hH : H ≤ H_height)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    pv_integral f fdBoundary 0 5 =
        -(2 * Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) :=
  modular_side_of_larger_radius f hf hint
    (by rw [← seg5_q_radius_H_eq]; exact seg5_q_radius_H_anti hH) hcusp_nonvan

end
