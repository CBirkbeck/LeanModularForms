/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_ModularSide
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_Boundary_Param
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_CuspHeight

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

/-! ## Modular Side at Arbitrary Height -/

/-- Modular-side identity at arbitrary height `H > 0`, using `fdBoundary_H H`.

Forwards to `pv_integral_eq_modular_transformation_H` from `ValenceFormula_PV.lean`.
Unlike `modular_side_of_smaller_height`, this operates on the *parameterized* boundary
curve `fdBoundary_H H`, not the fixed `fdBoundary`. -/
theorem modular_side_of_height (hf : f ≠ 0)
    {H : ℝ} (hH : 0 < H)
    (hint_H : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    pv_integral f (fdBoundary_H H) 0 5 =
        -(2 * Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) :=
  pv_integral_eq_modular_transformation_H f hf hH hint_H hcusp_nonvan

/-! ## Modular Side from Nonvanishing -/

/-- Modular-side identity at arbitrary height `H > 0`, deriving integrability from nonvanishing.

This wraps `modular_side_of_height` by deriving the `IntervalIntegrable` hypothesis from
the nonvanishing condition `h_nv` via `intervalIntegrable_logDeriv_fdBoundary_H_of_nonvanishing`. -/
theorem modular_side_of_height_of_nonvanishing (hf : f ≠ 0)
    {H : ℝ} (hH : 0 < H)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    pv_integral f (fdBoundary_H H) 0 5 =
        -(2 * Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) :=
  modular_side_of_height f hf hH
    (intervalIntegrable_logDeriv_fdBoundary_H_of_nonvanishing f hH h_nv) hcusp_nonvan

/-! ## Modular Side with Auto-Cusp Nonvanishing -/

/-- Modular-side identity with automatic cusp nonvanishing derived from `hf`.

From `hf : f ≠ 0`, the cusp function has isolated zeros near 0, giving
`∃ H₀ > √3/2, cusp_nonvan(H₀)`. For any `H ≥ H₀`, cusp nonvanishing transfers
by monotonicity (`cusp_nonvanishing_seg5_q_radius_H_mono`). The caller supplies
only `h_nv` (boundary nonvanishing), not `hcusp_nonvan`. -/
theorem modular_side_auto_cusp (hf : f ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral f (fdBoundary_H H) 0 5 =
          -(2 * Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) := by
  obtain ⟨H₀, hH₀_gt, hH₀_nonvan⟩ := exists_height_cusp_nonvanishing f hf
  refine ⟨H₀, hH₀_gt, fun {H} hH h_nv => ?_⟩
  have hH_pos : 0 < H := by
    have : (0 : ℝ) < Real.sqrt 3 / 2 := by positivity
    linarith
  exact modular_side_of_height_of_nonvanishing f hf hH_pos h_nv
    (cusp_nonvanishing_seg5_q_radius_H_mono f hH hH₀_nonvan)

/-! ## Modular Side with Auto-Cusp and Integrability -/

/-- Modular-side identity with automatic cusp nonvanishing, taking integrability instead of `h_nv`.

Combines `modular_side_auto_cusp` with `hint_H_iff_nonvanishing_fdBoundary_H`:
from `IntervalIntegrable` at height `H ≥ H₀ > √3/2`, derive boundary nonvanishing
via the iff characterization, then apply the auto-cusp route. -/
theorem modular_side_auto_cusp_of_integrable (hf : f ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
          (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5 →
        pv_integral f (fdBoundary_H H) 0 5 =
          -(2 * Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ := modular_side_auto_cusp f hf
  refine ⟨H₀, hH₀_gt, fun {H} hH hint => ?_⟩
  have hH_gt : Real.sqrt 3 / 2 < H := lt_of_lt_of_le hH₀_gt hH
  exact h_auto hH ((hint_H_iff_nonvanishing_fdBoundary_H f hf hH_gt).mp hint)

end
