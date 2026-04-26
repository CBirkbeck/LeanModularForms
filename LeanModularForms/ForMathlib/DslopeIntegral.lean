/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Liouville
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

/-! ### Joint continuity -/

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary: for `c₀, w₀ ∈ U` open convex, there is a compact subset `K ⊆ U` and
`ε > 0` such that for all `c ∈ ball c₀ ε` and `w ∈ ball w₀ ε`, the segment
`[c, w]` lies in `K`. -/
private lemma exists_compact_tube_prod {U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U)
    {c₀ w₀ : ℂ} (hc₀ : c₀ ∈ U) (hw₀ : w₀ ∈ U) :
    ∃ ε > 0, ∃ K ⊆ U, IsCompact K ∧
      ∀ c ∈ Metric.ball c₀ ε, ∀ w ∈ Metric.ball w₀ ε,
        ∀ t ∈ Icc (0 : ℝ) 1, c + t • (w - c) ∈ K := by
  obtain ⟨ρ_c, hρ_c_pos, hρ_c_sub⟩ := Metric.isOpen_iff.mp hU_open c₀ hc₀
  obtain ⟨ρ_w, hρ_w_pos, hρ_w_sub⟩ := Metric.isOpen_iff.mp hU_open w₀ hw₀
  set ρ := min ρ_c ρ_w / 2
  have hρ_pos : 0 < ρ := by simp only [ρ]; positivity
  refine ⟨ρ, hρ_pos,
    (fun p : ℂ × ℂ × ℝ => (1 - p.2.2) • p.1 + p.2.2 • p.2.1) ''
      (Metric.closedBall c₀ ρ ×ˢ Metric.closedBall w₀ ρ ×ˢ Icc (0 : ℝ) 1),
    ?_, ?_, ?_⟩
  · rintro z ⟨⟨c, w, t⟩, ⟨hc, hw, ht⟩, rfl⟩
    have hc_U : c ∈ U := hρ_c_sub (by
      rw [Metric.mem_closedBall] at hc
      rw [Metric.mem_ball]
      simp only [ρ] at hc
      linarith [min_le_left ρ_c ρ_w])
    have hw_U : w ∈ U := hρ_w_sub (by
      rw [Metric.mem_closedBall] at hw
      rw [Metric.mem_ball]
      simp only [ρ] at hw
      linarith [min_le_right ρ_c ρ_w])
    exact hU hc_U hw_U (by linarith [ht.2]) ht.1 (by linarith)
  · refine IsCompact.image_of_continuousOn
      ((isCompact_closedBall _ _).prod
        ((isCompact_closedBall _ _).prod isCompact_Icc)) ?_
    have h_cont : Continuous (fun p : ℂ × ℂ × ℝ => (1 - p.2.2) • p.1 + p.2.2 • p.2.1) := by
      refine Continuous.add ?_ ?_
      · exact (continuous_const.sub continuous_snd.snd).smul continuous_fst
      · exact continuous_snd.snd.smul continuous_snd.fst
    exact h_cont.continuousOn
  · intro c hc w hw t ht
    refine ⟨(c, w, t), ⟨?_, ?_, ht⟩, ?_⟩
    · rw [Metric.mem_closedBall]; rw [Metric.mem_ball] at hc; linarith
    · rw [Metric.mem_closedBall]; rw [Metric.mem_ball] at hw; linarith
    · show (1 - t) • c + t • w = c + t • (w - c)
      module

/-- Joint continuity of `(c, w) ↦ dslope f c w` on `U × U` for `f` differentiable
on open convex `U`. -/
theorem continuousOn_dslope_prod {U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U)
    (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fun p : ℂ × ℂ => dslope f p.1 p.2) (U ×ˢ U) := by
  rintro ⟨c₀, w₀⟩ ⟨hc₀, hw₀⟩
  obtain ⟨ε, hε_pos, K, hK_sub, hK_compact, hK_tube⟩ :=
    exists_compact_tube_prod hU hU_open hc₀ hw₀
  have h_deriv_contU : ContinuousOn (deriv f) U :=
    (hf.analyticOnNhd hU_open).deriv.continuousOn
  obtain ⟨M, hM⟩ := hK_compact.bddAbove_image (h_deriv_contU.norm.mono hK_sub)
  have h_eq_nbhd : (fun p : ℂ × ℂ => dslope f p.1 p.2) =ᶠ[nhds (c₀, w₀)]
      fun p => ∫ t in (0 : ℝ)..1, deriv f (p.1 + t • (p.2 - p.1)) := by
    filter_upwards [(hU_open.prod hU_open).mem_nhds (by exact ⟨hc₀, hw₀⟩ : (c₀, w₀) ∈ U ×ˢ U)]
      with p hp
    exact dslope_eq_integral_deriv hU hU_open hf hp.1 hp.2
  refine (ContinuousAt.congr ?_ h_eq_nbhd.symm).continuousWithinAt
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => max M 0) ?_ ?_ intervalIntegral.intervalIntegrable_const ?_
  · filter_upwards [Metric.ball_mem_nhds (c₀, w₀) hε_pos] with p hp
    rw [uIoc_of_le (zero_le_one' ℝ)]
    have hp_c : p.1 ∈ Metric.ball c₀ ε := by
      rw [Metric.mem_ball] at hp ⊢
      refine lt_of_le_of_lt ?_ hp
      rw [Prod.dist_eq]; exact le_max_left _ _
    have hp_w : p.2 ∈ Metric.ball w₀ ε := by
      rw [Metric.mem_ball] at hp ⊢
      refine lt_of_le_of_lt ?_ hp
      rw [Prod.dist_eq]; exact le_max_right _ _
    have h_cont : ContinuousOn (fun t : ℝ => deriv f (p.1 + t • (p.2 - p.1)))
        (Icc (0 : ℝ) 1) := by
      have h1 : Continuous (fun t : ℝ => p.1 + t • (p.2 - p.1)) := by continuity
      exact h_deriv_contU.comp h1.continuousOn fun t ht =>
        hK_sub (hK_tube p.1 hp_c p.2 hp_w t ht)
    exact (h_cont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [Metric.ball_mem_nhds (c₀, w₀) hε_pos] with p hp
    filter_upwards with t ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht_Icc := Ioc_subset_Icc_self ht
    have hp_c : p.1 ∈ Metric.ball c₀ ε := by
      rw [Metric.mem_ball] at hp ⊢
      refine lt_of_le_of_lt ?_ hp
      rw [Prod.dist_eq]; exact le_max_left _ _
    have hp_w : p.2 ∈ Metric.ball w₀ ε := by
      rw [Metric.mem_ball] at hp ⊢
      refine lt_of_le_of_lt ?_ hp
      rw [Prod.dist_eq]; exact le_max_right _ _
    exact le_max_of_le_left
      (hM ⟨p.1 + t • (p.2 - p.1), hK_tube p.1 hp_c p.2 hp_w t ht_Icc, rfl⟩)
  · filter_upwards with t ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht_Icc := Ioc_subset_Icc_self ht
    have hmem : c₀ + t • (w₀ - c₀) ∈ U :=
      hK_sub (hK_tube c₀ (Metric.mem_ball_self hε_pos) w₀
        (Metric.mem_ball_self hε_pos) t ht_Icc)
    have h1 : ContinuousAt (fun p : ℂ × ℂ => p.1 + t • (p.2 - p.1)) (c₀, w₀) := by
      have : Continuous (fun p : ℂ × ℂ => p.1 + t • (p.2 - p.1)) := by continuity
      exact this.continuousAt
    have h2 : ContinuousAt (deriv f) (c₀ + t • (w₀ - c₀)) :=
      h_deriv_contU.continuousAt (hU_open.mem_nhds hmem)
    exact h2.comp_of_eq h1 rfl

/-! ### Cauchy estimates for the derivative of `dslope` -/

/-- Uniform bound on `deriv (dslope f c) w` for `(c, w)` in a compact product neighborhood
of `(c₀, w₀)`, via Cauchy's estimate applied to `dslope f c` (analytic on `U` by
`Complex.differentiableOn_dslope`).

The bound is `2M/ρ` where `M = sup_{(c, z) ∈ closedBall c₀ ρ × closedBall w₀ (3ρ/2)} ‖dslope f c z‖`
(finite by joint continuity D-1b on a compact set) and `ρ` is chosen so
`closedBall c₀ (2ρ), closedBall w₀ (2ρ) ⊆ U`. -/
theorem deriv_dslope_bounded_locally {U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c₀ w₀ : ℂ} (hc₀ : c₀ ∈ U) (hw₀ : w₀ ∈ U) :
    ∃ C > 0, ∃ δ > 0, ∀ c ∈ Metric.ball c₀ δ, ∀ w ∈ Metric.ball w₀ δ,
      ‖deriv (dslope f c) w‖ ≤ C := by
  obtain ⟨ρ_c, hρ_c_pos, hρ_c_sub⟩ := Metric.isOpen_iff.mp hU_open c₀ hc₀
  obtain ⟨ρ_w, hρ_w_pos, hρ_w_sub⟩ := Metric.isOpen_iff.mp hU_open w₀ hw₀
  set ρ := min ρ_c ρ_w / 4
  have hρ_pos : 0 < ρ := by simp only [ρ]; positivity
  -- Compact K = closedBall c₀ ρ × closedBall w₀ (3ρ/2) ⊆ U × U
  have h_cB_w_sub : Metric.closedBall w₀ (3 * ρ / 2) ⊆ U := fun z hz =>
    hρ_w_sub (by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      simp only [ρ] at hz ⊢
      linarith [min_le_right ρ_c ρ_w])
  have h_cB_c_sub : Metric.closedBall c₀ ρ ⊆ U := fun z hz =>
    hρ_c_sub (by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      simp only [ρ] at hz ⊢
      linarith [min_le_left ρ_c ρ_w])
  have hK_sub : Metric.closedBall c₀ ρ ×ˢ Metric.closedBall w₀ (3 * ρ / 2) ⊆ U ×ˢ U :=
    fun ⟨c, z⟩ ⟨hc, hz⟩ => ⟨h_cB_c_sub hc, h_cB_w_sub hz⟩
  have hK_compact : IsCompact
      (Metric.closedBall c₀ ρ ×ˢ Metric.closedBall w₀ (3 * ρ / 2)) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have h_cont := continuousOn_dslope_prod hU hU_open hf
  obtain ⟨M, hM⟩ := hK_compact.bddAbove_image (h_cont.mono hK_sub).norm
  refine ⟨max M 0 / (ρ / 2) + 1, by positivity, ρ / 2, by positivity, ?_⟩
  intro c hc w hw
  rw [Metric.mem_ball] at hc hw
  have hc_cB : c ∈ Metric.closedBall c₀ ρ := by
    rw [Metric.mem_closedBall]; linarith
  have hc_U : c ∈ U := h_cB_c_sub hc_cB
  have h_ds_diff_U : DifferentiableOn ℂ (dslope f c) U :=
    (Complex.differentiableOn_dslope (hU_open.mem_nhds hc_U)).mpr hf
  -- Cauchy estimate on ball w (ρ/2)
  have hρ2_pos : 0 < ρ / 2 := by positivity
  have h_cB_w_w0 : Metric.closedBall w (ρ / 2) ⊆ Metric.closedBall w₀ (3 * ρ / 2) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    calc dist z w₀ ≤ dist z w + dist w w₀ := dist_triangle _ _ _
      _ ≤ ρ / 2 + ρ / 2 := by linarith
      _ ≤ 3 * ρ / 2 := by linarith
  have h_diff_ball : DifferentiableOn ℂ (dslope f c) (Metric.ball w (ρ / 2)) :=
    h_ds_diff_U.mono fun z hz =>
      h_cB_w_sub (h_cB_w_w0 (Metric.ball_subset_closedBall hz))
  have h_DC : DiffContOnCl ℂ (dslope f c) (Metric.ball w (ρ / 2)) :=
    ⟨h_diff_ball,
     (h_ds_diff_U.mono fun z hz =>
       h_cB_w_sub (h_cB_w_w0 (Metric.closure_ball_subset_closedBall hz))).continuousOn⟩
  have h_sphere_bound : ∀ z ∈ Metric.sphere w (ρ / 2), ‖dslope f c z‖ ≤ max M 0 := by
    intro z hz
    have hz_cB : z ∈ Metric.closedBall w₀ (3 * ρ / 2) :=
      h_cB_w_w0 (Metric.sphere_subset_closedBall hz)
    exact le_max_of_le_left (hM ⟨(c, z), ⟨hc_cB, hz_cB⟩, rfl⟩)
  have h_est := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ2_pos h_DC
    h_sphere_bound
  linarith

/-- Uniform bound on `deriv (dslope f c) w` for `c` in a compact subset of `U` and `w`
in a ball around `w₀ ∈ U`. Generalization of `deriv_dslope_bounded_locally` to allow
the first argument to range over a compact set rather than just a ball. -/
theorem deriv_dslope_bounded_on_compact {U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {K_c : Set ℂ} (hK_compact : IsCompact K_c)
    (hK_sub : K_c ⊆ U) {w₀ : ℂ} (hw₀ : w₀ ∈ U) :
    ∃ C > 0, ∃ δ > 0, ∀ c ∈ K_c, ∀ w ∈ Metric.ball w₀ δ,
      ‖deriv (dslope f c) w‖ ≤ C := by
  obtain ⟨ρ_w, hρ_w_pos, hρ_w_sub⟩ := Metric.isOpen_iff.mp hU_open w₀ hw₀
  set ρ := ρ_w / 4
  have hρ_pos : 0 < ρ := by simp only [ρ]; positivity
  have h_cB_w_sub : Metric.closedBall w₀ (3 * ρ / 2) ⊆ U := fun z hz =>
    hρ_w_sub (by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      simp only [ρ] at hz ⊢; linarith)
  have hK_sub_prod : K_c ×ˢ Metric.closedBall w₀ (3 * ρ / 2) ⊆ U ×ˢ U :=
    fun ⟨c, z⟩ ⟨hc, hz⟩ => ⟨hK_sub hc, h_cB_w_sub hz⟩
  have hKprod_compact : IsCompact (K_c ×ˢ Metric.closedBall w₀ (3 * ρ / 2)) :=
    hK_compact.prod (isCompact_closedBall _ _)
  have h_cont := continuousOn_dslope_prod hU hU_open hf
  obtain ⟨M, hM⟩ := hKprod_compact.bddAbove_image (h_cont.mono hK_sub_prod).norm
  refine ⟨max M 0 / (ρ / 2) + 1, by positivity, ρ / 2, by positivity, ?_⟩
  intro c hc w hw
  rw [Metric.mem_ball] at hw
  have hc_U : c ∈ U := hK_sub hc
  have h_ds_diff_U : DifferentiableOn ℂ (dslope f c) U :=
    (Complex.differentiableOn_dslope (hU_open.mem_nhds hc_U)).mpr hf
  have hρ2_pos : 0 < ρ / 2 := by positivity
  have h_cB_w_w0 : Metric.closedBall w (ρ / 2) ⊆ Metric.closedBall w₀ (3 * ρ / 2) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    calc dist z w₀ ≤ dist z w + dist w w₀ := dist_triangle _ _ _
      _ ≤ ρ / 2 + ρ / 2 := by linarith
      _ ≤ 3 * ρ / 2 := by linarith
  have h_diff_ball : DifferentiableOn ℂ (dslope f c) (Metric.ball w (ρ / 2)) :=
    h_ds_diff_U.mono fun z hz =>
      h_cB_w_sub (h_cB_w_w0 (Metric.ball_subset_closedBall hz))
  have h_DC : DiffContOnCl ℂ (dslope f c) (Metric.ball w (ρ / 2)) :=
    ⟨h_diff_ball,
     (h_ds_diff_U.mono fun z hz =>
       h_cB_w_sub (h_cB_w_w0 (Metric.closure_ball_subset_closedBall hz))).continuousOn⟩
  have h_sphere_bound : ∀ z ∈ Metric.sphere w (ρ / 2), ‖dslope f c z‖ ≤ max M 0 := by
    intro z hz
    have hz_cB : z ∈ Metric.closedBall w₀ (3 * ρ / 2) :=
      h_cB_w_w0 (Metric.sphere_subset_closedBall hz)
    exact le_max_of_le_left (hM ⟨(c, z), ⟨hc, hz_cB⟩, rfl⟩)
  have h_est := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ2_pos h_DC
    h_sphere_bound
  linarith

/-! ### Measurability via pointwise limit -/

/-- For `f` differentiable on convex open `U` and `w₀ ∈ U`, the function
`c ↦ deriv (dslope f c) w₀` is AE strongly measurable on the restriction of any
measure to `U`. Proof: pointwise limit of continuous difference quotients
(each continuous by D-1a) using a scaled sequence `h_n = (ρ/2)/(n+1)` chosen
so that `w₀ + h_n ∈ U` for all `n`. -/
theorem aestronglyMeasurable_deriv_dslope {U : Set ℂ} (hU : Convex ℝ U)
    (hU_open : IsOpen U) (hf : DifferentiableOn ℂ f U) {w₀ : ℂ} (hw₀ : w₀ ∈ U)
    (μ : Measure ℂ) :
    AEStronglyMeasurable (fun c => deriv (dslope f c) w₀) (μ.restrict U) := by
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.isOpen_iff.mp hU_open w₀ hw₀
  -- Sequence `h_n = ((ρ/2) / ((n:ℝ)+1) : ℂ)` — always small, nonzero
  set h_seq : ℕ → ℂ := fun n => ((ρ / 2 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have h_seq_real_pos : ∀ n : ℕ, 0 < ρ / 2 / ((n : ℝ) + 1) := fun n => by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    positivity
  have h_seq_ne : ∀ n : ℕ, h_seq n ≠ 0 := fun n => by
    simp only [h_seq, ne_eq, Complex.ofReal_eq_zero]
    exact (h_seq_real_pos n).ne'
  have h_seq_norm_lt : ∀ n : ℕ, ‖h_seq n‖ < ρ := fun n => by
    simp only [h_seq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (h_seq_real_pos n)]
    have hge1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have : ρ / 2 / ((n : ℝ) + 1) ≤ ρ / 2 := by
      apply div_le_self (by linarith) hge1
    linarith
  have h_in_U : ∀ n : ℕ, w₀ + h_seq n ∈ U := fun n => hρ_sub <| by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact h_seq_norm_lt n
  -- h_seq tends to 0
  have h_seq_tendsto : Tendsto h_seq atTop (𝓝 0) := by
    have h_real : Tendsto (fun n : ℕ => ρ / 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have h_inv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).inv_tendsto_atTop
      have := h_inv.const_mul (ρ / 2)
      simpa [div_eq_mul_inv] using this
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from rfl]
    exact (Complex.continuous_ofReal.tendsto _).comp h_real
  -- Approximating sequence
  set q : ℕ → ℂ → ℂ := fun n c => (dslope f c (w₀ + h_seq n) - dslope f c w₀) / h_seq n
  -- Each q n is continuous on U
  have h_q_aemeas : ∀ n : ℕ, AEStronglyMeasurable (q n) (μ.restrict U) := fun n =>
    (((continuousOn_dslope_first_arg hU hU_open hf (h_in_U n)).sub
      (continuousOn_dslope_first_arg hU hU_open hf hw₀)).div_const _).aestronglyMeasurable
      hU_open.measurableSet
  -- Pointwise limit: q n c → deriv (dslope f c) w₀ for c ∈ U
  refine aestronglyMeasurable_of_tendsto_ae atTop h_q_aemeas ?_
  filter_upwards [ae_restrict_mem hU_open.measurableSet] with c hc
  -- For c ∈ U, dslope f c is differentiable at w₀
  have h_diff : DifferentiableAt ℂ (dslope f c) w₀ :=
    ((Complex.differentiableOn_dslope (hU_open.mem_nhds hc)).mpr hf w₀ hw₀).differentiableAt
      (hU_open.mem_nhds hw₀)
  -- Use HasDerivAt.tendsto_slope at w₀, parameterized by y → w₀
  have h_slope_tendsto :
      Tendsto (slope (dslope f c) w₀) (𝓝[≠] w₀) (𝓝 (deriv (dslope f c) w₀)) :=
    h_diff.hasDerivAt.tendsto_slope
  -- y_n = w₀ + h_seq n → w₀, y_n ≠ w₀
  have hy_tendsto : Tendsto (fun n => w₀ + h_seq n) atTop (𝓝 w₀) := by
    simpa using h_seq_tendsto.const_add w₀
  have hy_ne : ∀ n, w₀ + h_seq n ≠ w₀ := fun n h => h_seq_ne n (by
    have := add_left_cancel (a := w₀) (h.trans (add_zero w₀).symm)
    exact this)
  have hy_in_compl : ∀ᶠ n : ℕ in atTop, w₀ + h_seq n ∈ ({w₀}ᶜ : Set ℂ) :=
    Eventually.of_forall fun n => hy_ne n
  have hy_within : Tendsto (fun n => w₀ + h_seq n) atTop (𝓝[≠] w₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hy_tendsto, hy_in_compl⟩
  have h_comp := h_slope_tendsto.comp hy_within
  convert h_comp using 1
  ext n
  simp only [slope_def_field, Function.comp_apply, q]
  rw [show w₀ + h_seq n - w₀ = h_seq n from by ring, div_eq_inv_mul, mul_comm]

end Complex

end
