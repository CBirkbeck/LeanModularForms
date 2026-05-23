/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Homotopy.Integrality

/-!
# Homotopy Invariance of Winding Numbers

The classical winding number formula for curves avoiding a point.

## Main Results

* `generalizedWindingNumber_eq_classical_away` — PV winding number
    equals classical integral when curve avoids z₀
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- When γ avoids z₀, the PV winding number equals the classical contour integral. -/
theorem generalizedWindingNumber_eq_classical_away
    (γ : PiecewiseC1Curve) (z₀ : ℂ) (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) :
    generalizedWindingNumber' γ.toFun γ.a γ.b z₀ =
    (2 * Real.pi * I)⁻¹ * ∫ t in γ.a..γ.b, (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t := by
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  have hδ : 0 < Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b) :=
    ((isCompact_Icc.image_of_continuousOn γ.continuous_toFun).isClosed.notMem_iff_infDist_pos
      (Set.image_nonempty.mpr (Set.nonempty_Icc.mpr γ.hab.le))).mp
      (fun ⟨t, ht, htw⟩ => hoff t ht htw)
  congr 1
  apply limUnder_eventually_eq_const
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t ht
  simp only [sub_zero]
  rw [Set.uIoc_of_le γ.hab.le] at ht
  have ht' : t ∈ Icc γ.a γ.b := Ioc_subset_Icc_self ht
  have hbound : ε < ‖γ.toFun t - z₀‖ := by
    calc ε < Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b) := (mem_Ioo.mp hε).2
      _ ≤ dist z₀ (γ.toFun t) :=
            Metric.infDist_le_dist_of_mem (mem_image_of_mem γ.toFun ht')
      _ = ‖γ.toFun t - z₀‖ := by rw [Complex.dist_eq, norm_sub_rev]
  simp only [hbound, ↓reduceIte, deriv_sub_const]

end
