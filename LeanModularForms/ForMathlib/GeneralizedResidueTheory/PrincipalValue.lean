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

/-- The integrand `f ∘ γ * γ'` is continuous on the principal-value support set. -/
lemma continuousOn_pv_base (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (ε : ℝ)
    (hf_cont : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ_cont : ContinuousOn γ (Icc a b)) (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    ContinuousOn (fun t => f (γ t) * deriv γ t) ({t | ε < ‖γ t - z₀‖} ∩ Icc a b) := by
  have h_maps : MapsTo γ ({t | ε < ‖γ t - z₀‖} ∩ Icc a b)
      (γ '' Icc a b \ Metric.ball z₀ ε) := fun s ⟨hs_far, hs_Icc⟩ =>
    ⟨mem_image_of_mem γ hs_Icc, by
      simp only [Metric.mem_ball, not_lt, dist_eq_norm]; exact hs_far.le⟩
  intro t ht
  refine (ContinuousWithinAt.comp (hf_cont _ (h_maps ht))
    ((hγ_cont t ht.2).mono inter_subset_right) h_maps).mul ?_
  exact (hγ'_cont t ht.2).mono inter_subset_right

end
