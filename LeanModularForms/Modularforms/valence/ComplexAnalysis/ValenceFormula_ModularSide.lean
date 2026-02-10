/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormulaDefinitions
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_Boundary
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_PV
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Modular Side of the Valence Formula

This file assembles the **modular side** of the valence formula, which computes
the PV integral using modular transformation properties.

## Main Result

* `modular_side_mult_form`: The modular transformation gives
  PV ∮_{CW ∂𝒟} f'/f dz = -(2πi · (k/12 - ord_∞(f)))

This is a thin wrapper around `pv_integral_eq_modular_transformation` from the PV file.

## References

See `VALENCE_AI_PLAN_CORE.md` for the detailed proof strategy.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-! ## Order at Cusp -/

/-- The order at the cusp (order of vanishing in the q-expansion).
This is an alias for `orderAtCusp` from `ValenceFormula_PV`. -/
def orderAtCusp' (f : ModularForm (Gamma 1) k) : ℤ := orderAtCusp f

/-- `orderAtCusp'` equals `orderAtCusp`. -/
theorem orderAtCusp'_eq : orderAtCusp' f = orderAtCusp f := rfl

/-- The order at cusp is non-negative for modular forms. -/
theorem orderAtCusp_nonneg : 0 ≤ orderAtCusp' f := by
  unfold orderAtCusp' orderAtCusp
  exact Int.natCast_nonneg _

/-! ## Modular Transformation Contribution -/

/-- The S-transformation contribution is -k/12 (CW orientation).

Divides `arc_contribution_is_k_div_12` by 2πi. -/
theorem s_transformation_contribution
    (h_arc_seg2_gne : ∀ t ∈ Set.uIcc 1 2,
      modularFormCompOfComplex f (fdBoundary_seg2 t) ≠ 0)
    (h_arc_seg3_gne : ∀ t ∈ Set.uIcc 2 3,
      modularFormCompOfComplex f (fdBoundary_seg3 t) ≠ 0) :
    (1 / (2 * Real.pi * I)) * (pv_integral f fdBoundary_seg2 1 2 +
        pv_integral f fdBoundary_seg3 2 3) = -((k : ℂ) / 12) := by
  rw [arc_contribution_is_k_div_12 f h_arc_seg2_gne h_arc_seg3_gne]
  have hpi : (2 : ℂ) * ↑Real.pi * I ≠ 0 := by
    simp [ne_eq, mul_eq_zero, ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero]
  field_simp

/-! ## Cusp Contribution -/

/-- The q-expansion contribution is +ord_∞(f).

Divides `seg5_integral_eq_cusp_order` by 2πi. -/
theorem cusp_contribution (hf : f ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (1 / (2 * Real.pi * I)) * pv_integral f fdBoundary_seg5 4 5 =
        (orderAtCusp' f : ℂ) := by
  rw [orderAtCusp'_eq, seg5_integral_eq_cusp_order f hf hcusp_nonvan]
  have hpi : (2 : ℂ) * ↑Real.pi * I ≠ 0 := by
    simp [ne_eq, mul_eq_zero, ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero]
  field_simp

/-! ## Main Modular Side Result -/

/-- The modular side in multiplicative form (CW orientation).

Thin wrapper around `pv_integral_eq_modular_transformation`. -/
theorem modular_side_mult_form (hf : f ≠ 0)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    pv_integral f fdBoundary 0 5 =
        -(2 * Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) := by
  rw [orderAtCusp'_eq]
  exact pv_integral_eq_modular_transformation f hf hint hcusp_nonvan

/-- **Main Result**: (1/(2πi)) · ∮ = ord_∞ - k/12.

Divides `modular_side_mult_form` by 2πi. -/
theorem modular_side_equals_pv_integral (hf : f ≠ 0)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (1 / (2 * Real.pi * I)) * pv_integral f fdBoundary 0 5 =
      (orderAtCusp' f : ℂ) - (k : ℂ) / 12 := by
  rw [modular_side_mult_form f hf hint hcusp_nonvan]
  have hpi : (2 : ℂ) * ↑Real.pi * I ≠ 0 := by
    simp [ne_eq, mul_eq_zero, ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero]
  field_simp
  ring

end
