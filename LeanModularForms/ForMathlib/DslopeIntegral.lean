/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# `dslope` as a parameter integral

For `f : ℂ → ℂ` differentiable on an open convex set `U` and `c, w ∈ U`, we have
the integral representation:

  `dslope f c w = ∫₀¹ deriv f (c + t • (w - c)) ∂t`

This is the fundamental theorem of calculus applied to `f` on the segment `[c, w] ⊆ U`.
The representation unifies the two cases in `dslope` (`c = w` giving `deriv f c`, and
`c ≠ w` giving the usual slope formula).

From this integral representation we deduce:

* Joint continuity of `(c, w) ↦ dslope f c w` on convex open sets

## Main results

* `dslope_eq_integral_deriv` — `dslope f c w = ∫₀¹ deriv f (c + t•(w-c))` on convex `U`
-/

open Set MeasureTheory Filter Topology intervalIntegral

noncomputable section

namespace Complex

variable {f : ℂ → ℂ}

set_option backward.isDefEq.respectTransparency false in
/-- The `dslope` integral representation on a convex open set: when `f` is
differentiable on `U` and both `c, w ∈ U` (so the segment `[c, w] ⊆ U`), then
`dslope f c w` equals the integral of the derivative of `f` along the segment. -/
theorem dslope_eq_integral_deriv {U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c w : ℂ} (hc : c ∈ U) (hw : w ∈ U) :
    dslope f c w = ∫ t in (0 : ℝ)..1, deriv f (c + t • (w - c)) := by
  have h_seg : ∀ t ∈ Icc (0 : ℝ) 1, c + t • (w - c) ∈ U := by
    intro t ht
    have h_eq : c + t • (w - c) = (1 - t) • c + t • w := by module
    rw [h_eq]
    exact hU hc hw (by linarith [ht.2]) ht.1 (by linarith)
  have h_deriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt f (deriv f (c + t • (w - c))) (c + t • (w - c)) := fun t ht =>
    ((hf (c + t • (w - c)) (h_seg t ht)).differentiableAt
      (hU_open.mem_nhds (h_seg t ht))).hasDerivAt
  have h_cont : ContinuousOn (fun t : ℝ => deriv f (c + t • (w - c))) (Icc (0 : ℝ) 1) := by
    have h1 : Continuous (fun t : ℝ => c + t • (w - c)) := by continuity
    have h2 : ContinuousOn (deriv f) U :=
      (hf.analyticOnNhd hU_open).deriv.continuousOn
    exact h2.comp h1.continuousOn h_seg
  have h_int := integral_unitInterval_deriv_eq_sub h_cont h_deriv
  have heq : c + (w - c) = w := by ring
  rw [heq] at h_int
  by_cases hwc : w = c
  · have h_const : ∀ t : ℝ, c + t • (w - c) = c := by
      intro t; rw [hwc]; simp
    simp_rw [h_const]
    rw [hwc, dslope_same, intervalIntegral.integral_const, sub_zero, one_smul]
  · have hne : w - c ≠ 0 := sub_ne_zero.mpr hwc
    have h_mul : (w - c) * ∫ t in (0 : ℝ)..1, deriv f (c + t • (w - c)) = f w - f c := by
      rw [← smul_eq_mul]; exact h_int
    rw [dslope_of_ne f hwc, slope_def_module, smul_eq_mul]
    rw [show (w - c)⁻¹ * (f w - f c) = ∫ t in (0 : ℝ)..1, deriv f (c + t • (w - c)) from ?_]
    rw [← h_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-! ### Continuity from the integral representation -/

/-- Auxiliary: for `c₀, w₀ ∈ U` open convex, there is a compact subset `K ⊆ U`
and `ε > 0` such that the segment `[c, w₀]` lies in `K` for all `c ∈ ball c₀ ε`.
Uses the continuous image `(c, t) ↦ (1-t)c + tw₀` on `closedBall c₀ ε × [0,1]`. -/
private lemma exists_compact_tube {U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U)
    {c₀ w₀ : ℂ} (hc₀ : c₀ ∈ U) (hw₀ : w₀ ∈ U) :
    ∃ ε > 0, ∃ K ⊆ U, IsCompact K ∧
      ∀ c ∈ Metric.ball c₀ ε, ∀ t ∈ Icc (0 : ℝ) 1, c + t • (w₀ - c) ∈ K := by
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.isOpen_iff.mp hU_open c₀ hc₀
  refine ⟨ρ / 2, by linarith,
    (fun p : ℂ × ℝ => (1 - p.2) • p.1 + p.2 • w₀) ''
      (Metric.closedBall c₀ (ρ / 2) ×ˢ Icc (0 : ℝ) 1), ?_, ?_, ?_⟩
  · rintro z ⟨⟨c, t⟩, ⟨hc, ht⟩, rfl⟩
    have hc_U : c ∈ U := hρ_sub (by
      rw [Metric.mem_closedBall] at hc
      rw [Metric.mem_ball]
      linarith)
    exact hU hc_U hw₀ (by linarith [ht.2]) ht.1 (by linarith)
  · refine IsCompact.image_of_continuousOn
      ((isCompact_closedBall _ _).prod isCompact_Icc) ?_
    have : Continuous (fun p : ℂ × ℝ => (1 - p.2) • p.1 + p.2 • w₀) := by continuity
    exact this.continuousOn
  · intro c hc t ht
    refine ⟨(c, t), ⟨?_, ht⟩, ?_⟩
    · rw [Metric.mem_closedBall, Complex.dist_eq] at *
      rw [Metric.mem_ball, Complex.dist_eq] at hc
      linarith
    · show (1 - t) • c + t • w₀ = c + t • (w₀ - c)
      module

/-- Continuity of `c ↦ dslope f c w₀` on a convex open set `U` for `f` differentiable
on `U` and any fixed `w₀ ∈ U`. Uses `dslope_eq_integral_deriv` +
`intervalIntegral.continuousAt_of_dominated_interval` on a compact tube. -/
theorem continuousOn_dslope_first_arg {U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {w₀ : ℂ} (hw₀ : w₀ ∈ U) :
    ContinuousOn (fun c => dslope f c w₀) U := by
  intro c₀ hc₀
  obtain ⟨ε, hε_pos, K, hK_sub, hK_compact, hK_tube⟩ :=
    exists_compact_tube hU hU_open hc₀ hw₀
  have h_deriv_contU : ContinuousOn (deriv f) U :=
    (hf.analyticOnNhd hU_open).deriv.continuousOn
  obtain ⟨M, hM⟩ := hK_compact.bddAbove_image (h_deriv_contU.norm.mono hK_sub)
  have h_eq_nbhd : (fun c => dslope f c w₀) =ᶠ[nhds c₀]
      fun c => ∫ t in (0 : ℝ)..1, deriv f (c + t • (w₀ - c)) := by
    filter_upwards [hU_open.mem_nhds hc₀] with c hc
    exact dslope_eq_integral_deriv hU hU_open hf hc hw₀
  refine (ContinuousAt.congr ?_ h_eq_nbhd.symm).continuousWithinAt
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => max M 0) ?_ ?_ intervalIntegral.intervalIntegrable_const ?_
  · filter_upwards [Metric.ball_mem_nhds c₀ hε_pos] with c hc
    rw [uIoc_of_le (zero_le_one' ℝ)]
    have h_cont : ContinuousOn (fun t : ℝ => deriv f (c + t • (w₀ - c))) (Icc (0 : ℝ) 1) := by
      have h1 : Continuous (fun t : ℝ => c + t • (w₀ - c)) := by continuity
      exact h_deriv_contU.comp h1.continuousOn fun t ht => hK_sub (hK_tube c hc t ht)
    exact (h_cont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [Metric.ball_mem_nhds c₀ hε_pos] with c hc
    filter_upwards with t ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht_Icc := Ioc_subset_Icc_self ht
    exact le_max_of_le_left (hM ⟨c + t • (w₀ - c), hK_tube c hc t ht_Icc, rfl⟩)
  · filter_upwards with t ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht_Icc := Ioc_subset_Icc_self ht
    have hmem : c₀ + t • (w₀ - c₀) ∈ U :=
      hK_sub (hK_tube c₀ (Metric.mem_ball_self hε_pos) t ht_Icc)
    have h1 : ContinuousAt (fun c : ℂ => c + t • (w₀ - c)) c₀ := by
      have : Continuous (fun c : ℂ => c + t • (w₀ - c)) := by continuity
      exact this.continuousAt
    have h2 : ContinuousAt (deriv f) (c₀ + t • (w₀ - c₀)) :=
      h_deriv_contU.continuousAt (hU_open.mem_nhds hmem)
    exact h2.comp_of_eq h1 rfl

end Complex

end
