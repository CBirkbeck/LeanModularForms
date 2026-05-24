/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ClassicalCPV

/-!
# Cauchy Principal Value Theory

Theory of Cauchy principal value integrals for piecewise C¹ contour integration.
The principal value approach allows contours to pass through singularities.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- The principal value support set `{t | ε < ‖γ t - z₀‖} ∩ Icc a b` is measurable. -/
lemma measurableSet_pv_support (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (ε : ℝ)
    (hγ_cont : ContinuousOn γ (Icc a b)) :
    MeasurableSet ({t | ε < ‖γ t - z₀‖} ∩ Icc a b) := by
  have h_norm_cont : ContinuousOn (fun t => ‖γ t - z₀‖) (Icc a b) :=
    (hγ_cont.sub continuousOn_const).norm
  obtain ⟨U, hU_open, hU_eq⟩ := continuousOn_iff'.mp h_norm_cont (Ioi ε) isOpen_Ioi
  rw [show {t | ε < ‖γ t - z₀‖} ∩ Icc a b = U ∩ Icc a b from hU_eq]
  exact hU_open.measurableSet.inter isClosed_Icc.measurableSet

end
