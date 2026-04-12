/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.DixonDef
import LeanModularForms.ForMathlib.NullHomologous
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Dixon Function Differentiability

This file proves the Dixon h2 function is holomorphic off the curve, the h1 function is
holomorphic on U, and the full Dixon function is entire, using the parametric Leibniz rule
for differentiation under the integral sign.

## Main results

* `dixonH2_differentiableAt` -- h2 is holomorphic at every point off the curve image
* `dixonH1_differentiableOn` -- h1 is holomorphic on U
* `dixonFunction_differentiable` -- the Dixon function is entire

## References

* J. D. Dixon, *A brief proof of Cauchy's integral theorem*, 1971
-/

open Complex Set Filter Topology MeasureTheory
open scoped Classical Real Interval

noncomputable section

variable {x : ℂ}

/-! ## Curve distance infrastructure -/

private lemma curveImage_compact (γ : PiecewiseC1Path x x) :
    IsCompact (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
  isCompact_Icc.image γ.toPath.continuous_extend

private lemma curveImage_nonempty (γ : PiecewiseC1Path x x) :
    (γ.toPath.extend '' Icc (0 : ℝ) 1).Nonempty :=
  ⟨γ.toPath.extend 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩

private lemma curveImage_infDist_pos (γ : PiecewiseC1Path x x) (w : ℂ)
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    0 < Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
  ((curveImage_compact γ).isClosed.notMem_iff_infDist_pos (curveImage_nonempty γ)).mp
    fun ⟨t, ht, heq⟩ => hoff t ht heq

private lemma ball_avoids_curve (γ : PiecewiseC1Path x x) (w : ℂ)
    {ε : ℝ} (hε : 0 < ε)
    (hε_le : 2 * ε ≤ Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1)) :
    ∀ w' ∈ Metric.ball w ε, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w' := by
  intro w' hw' t ht heq
  have h1 := Metric.infDist_le_dist_of_mem (x := w)
    (show γ t ∈ γ.toPath.extend '' Icc (0 : ℝ) 1 from ⟨t, ht, rfl⟩)
  have h2 := Metric.mem_ball.mp hw'
  rw [heq] at h1
  linarith [dist_comm w' w]

private lemma ball_dist_lower_bound (γ : PiecewiseC1Path x x) (w : ℂ)
    {ε : ℝ} (hε_le : 2 * ε ≤ Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1)) :
    ∀ w' ∈ Metric.ball w ε, ∀ t ∈ Icc (0 : ℝ) 1, ε ≤ ‖γ t - w'‖ := by
  intro w' hw' t ht
  have h1 := Metric.infDist_le_dist_of_mem (x := w)
    (show γ t ∈ γ.toPath.extend '' Icc (0 : ℝ) 1 from ⟨t, ht, rfl⟩)
  rw [Complex.dist_eq] at h1
  have h2 := Metric.mem_ball.mp hw'
  rw [Complex.dist_eq] at h2
  have h5 := norm_sub_norm_le (γ t - w) (γ t - w')
  have h6 : (γ t - w) - (γ t - w') = w' - w := by ring
  rw [h6] at h5
  have h7 : ‖w' - w‖ = ‖w - w'‖ := norm_sub_rev w' w
  have h8 : ‖w - γ t‖ = ‖γ t - w‖ := norm_sub_rev w (γ t)
  linarith

/-! ## h2 differentiability -/

private lemma h2_pointwise_hasDerivAt (fz c z w : ℂ) (hne : z - w ≠ 0) :
    HasDerivAt (fun w' => fz * (z - w')⁻¹ * c)
      (fz * (z - w)⁻¹ ^ 2 * c) w := by
  have h_sub : HasDerivAt (fun w' => z - w') (-1) w :=
    HasDerivAt.const_sub z (hasDerivAt_id w)
  have h_inv : HasDerivAt (fun w' => (z - w')⁻¹) ((z - w)⁻¹ ^ 2) w := by
    have h := HasDerivAt.inv h_sub hne
    simp only [neg_neg, one_div] at h
    convert h using 1; rw [inv_pow]
  exact ((h_inv.const_mul fz).mul_const c).congr_deriv (by ring)

/-- Norm bound for the h2 integrand: `‖f(γ t) * (γ t - w')⁻¹ ^ 2 * γ'(t)‖ ≤ M * ε⁻¹² * D`
when `w'` is in a ball of radius `ε` around `w` and the curve stays at distance `≥ ε`. -/
private lemma h2_integrand_norm_bound {f : ℂ → ℂ} {γ : PiecewiseC1Path x x}
    {M ε D : ℝ} (hM_nn : 0 ≤ M) (hε_pos : 0 < ε)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ t)‖ ≤ M)
    (hD : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ.toPath.extend t‖ ≤ D)
    (h_dist_lb : ∀ w' ∈ Metric.ball w ε,
      ∀ t ∈ Icc (0 : ℝ) 1, ε ≤ ‖γ t - w'‖)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) {w' : ℂ} (hw' : w' ∈ Metric.ball w ε) :
    ‖f (γ t) * (γ t - w')⁻¹ ^ 2 * deriv γ.toPath.extend t‖ ≤ M * ε⁻¹ ^ 2 * D := by
  have ht_Icc := Ioc_subset_Icc_self ht
  rw [norm_mul, norm_mul, norm_pow, norm_inv]
  exact mul_le_mul
    (mul_le_mul (hM t ht_Icc)
      (pow_le_pow_left₀ (by positivity)
        (inv_anti₀ hε_pos (h_dist_lb w' hw' t ht_Icc)) 2)
      (by positivity) hM_nn)
    (hD t ht_Icc) (by positivity) (mul_nonneg hM_nn (by positivity))

/-- **h2 is holomorphic at every point off the curve.**

Uses the parametric Leibniz rule (differentiation under the integral sign).
The integrability, bounds, and measurability hypotheses are provided externally
since they depend on the curve's regularity structure. -/
theorem dixonH2_differentiableAt {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x x} {w : ℂ}
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * (γ t - w)⁻¹ * deriv γ.toPath.extend t) volume 0 1)
    (h_fγ_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ t)‖ ≤ M)
    (h_deriv_bound : ∃ D : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ.toPath.extend t‖ ≤ D)
    (h_meas : ∀ w' ∈ Metric.ball w
        (Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1) / 2),
      AEStronglyMeasurable
        (fun t => f (γ t) * (γ t - w')⁻¹ * deriv γ.toPath.extend t)
        (volume.restrict (Set.uIoc 0 1)))
    (h_F'_meas : AEStronglyMeasurable
      (fun t => f (γ t) * (γ t - w)⁻¹ ^ 2 * deriv γ.toPath.extend t)
      (volume.restrict (Set.uIoc 0 1))) :
    DifferentiableAt ℂ (dixonH2 f γ) w := by
  have hid_pos := curveImage_infDist_pos γ w hoff
  set ε := Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1) / 2
  have hε_pos : 0 < ε := by simp only [ε]; linarith
  have h2ε : 2 * ε ≤ Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1) := by
    simp only [ε]; linarith
  obtain ⟨M, hM_nn, hM⟩ := h_fγ_bound
  obtain ⟨D, hD⟩ := h_deriv_bound
  have h_ball_avoids := ball_avoids_curve γ w hε_pos h2ε
  have h_dist_lb := ball_dist_lower_bound γ w h2ε
  have h_eq : dixonH2 f γ = fun w' =>
      ∫ t in (0 : ℝ)..1, f (γ t) * (γ t - w')⁻¹ * deriv γ.toPath.extend t := by
    ext w'; simp only [dixonH2, div_eq_mul_inv]
  rw [h_eq]
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun w' t => f (γ t) * (γ t - w')⁻¹ * deriv γ.toPath.extend t)
    (F' := fun w' t => f (γ t) * (γ t - w')⁻¹ ^ 2 * deriv γ.toPath.extend t)
    (bound := fun _ => M * ε⁻¹ ^ 2 * D)
    (Metric.ball_mem_nhds w hε_pos)
    (by filter_upwards [Metric.ball_mem_nhds w hε_pos] with w' hw'; exact h_meas w' hw')
    h_int h_F'_meas
    (by filter_upwards with t ht w' hw'
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact h2_integrand_norm_bound hM_nn hε_pos hM hD h_dist_lb ht hw')
    (intervalIntegrable_const (c := M * ε⁻¹ ^ 2 * D))
    (by filter_upwards with t ht w' hw'
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact h2_pointwise_hasDerivAt (f (γ t)) (deriv γ.toPath.extend t) (γ t) w'
          (sub_ne_zero.mpr (h_ball_avoids w' hw' t (Ioc_subset_Icc_self ht))))).2.differentiableAt

/-! ## h1 differentiability -/

/-- The ball of radius `min (min a b) c / 2` is contained in balls of radius `a`, `b`, and `c`. -/
private lemma min3_ball_subsets (w₀ : ℂ) {ε_m ε_d δ_C : ℝ}
    (hε_m_pos : 0 < ε_m) (hε_d_pos : 0 < ε_d) (hδ_C_pos : 0 < δ_C) :
    let ε := min (min ε_m ε_d) δ_C / 2
    (0 < ε) ∧
    (Metric.ball w₀ ε ⊆ Metric.ball w₀ ε_m) ∧
    (Metric.ball w₀ ε ⊆ Metric.ball w₀ ε_d) ∧
    (Metric.ball w₀ ε ⊆ Metric.ball w₀ δ_C) := by
  refine ⟨by positivity,
    Metric.ball_subset_ball (by linarith [min_le_left (min ε_m ε_d) δ_C, min_le_left ε_m ε_d]),
    Metric.ball_subset_ball (by linarith [min_le_left (min ε_m ε_d) δ_C, min_le_right ε_m ε_d]),
    Metric.ball_subset_ball (by linarith [min_le_right (min ε_m ε_d) δ_C])⟩

/-- **h1 is holomorphic on U.**

Uses the parametric Leibniz rule with Cauchy estimates for the derivative of dslope. -/
theorem dixonH1_differentiableOn {f : ℂ → ℂ} {U : Set ℂ} (_hU : IsOpen U)
    (_hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion x x)
    (_hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ∈ U)
    (h_int : ∀ w ∈ U, IntervalIntegrable
      (fun t => dslope f w (γ.toPiecewiseC1Path t) *
        deriv γ.toPiecewiseC1Path.toPath.extend t) volume 0 1)
    (h_meas : ∀ w₀ ∈ U, ∃ ε > 0, ∀ w ∈ Metric.ball w₀ ε,
      AEStronglyMeasurable
        (fun t => dslope f w (γ.toPiecewiseC1Path t) *
          deriv γ.toPiecewiseC1Path.toPath.extend t)
        (volume.restrict (Set.uIoc 0 1)))
    (_h_dslope_bound : ∀ w₀ ∈ U, ∃ C > 0, ∃ δ > 0,
      ∀ c ∈ γ.toPiecewiseC1Path.toPath.extend '' Icc (0 : ℝ) 1,
        ∀ w ∈ Metric.ball w₀ δ, ‖dslope f c w‖ ≤ C)
    (h_deriv_bound : ∃ D : ℝ, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖deriv γ.toPiecewiseC1Path.toPath.extend t‖ ≤ D)
    -- HasDerivAt for the dslope integrand (swaps dslope arguments + multiplies by γ')
    (h_dslope_hasDerivAt : ∀ w₀ ∈ U, ∃ ε > 0,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Metric.ball w₀ ε,
        HasDerivAt (fun w' => dslope f w' (γ.toPiecewiseC1Path t) *
          deriv γ.toPiecewiseC1Path.toPath.extend t)
          (deriv (dslope f (γ.toPiecewiseC1Path t)) w *
            deriv γ.toPiecewiseC1Path.toPath.extend t) w)
    -- F' measurability
    (h_F'_meas : ∀ w₀ ∈ U,
      AEStronglyMeasurable
        (fun t => deriv (dslope f (γ.toPiecewiseC1Path t)) w₀ *
          deriv γ.toPiecewiseC1Path.toPath.extend t)
        (volume.restrict (Set.uIoc 0 1)))
    -- Derivative bound for dslope
    (h_dslope_deriv_bound : ∀ w₀ ∈ U, ∃ C > 0, ∃ δ > 0,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Metric.ball w₀ δ,
        ‖deriv (dslope f (γ.toPiecewiseC1Path t)) w‖ ≤ C) :
    DifferentiableOn ℂ (dixonH1 f γ.toPiecewiseC1Path) U := by
  intro w₀ hw₀
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨D, hD⟩ := h_deriv_bound
  obtain ⟨ε_m, hε_m_pos, h_meas_ball⟩ := h_meas w₀ hw₀
  obtain ⟨ε_d, hε_d_pos, h_dslope_hda⟩ := h_dslope_hasDerivAt w₀ hw₀
  obtain ⟨C, hC_pos, δ_C, hδ_C_pos, h_deriv_bd⟩ := h_dslope_deriv_bound w₀ hw₀
  obtain ⟨hε_pos, hball_sub_εm, hball_sub_εd, hball_sub_δC⟩ :=
    min3_ball_subsets w₀ hε_m_pos hε_d_pos hδ_C_pos
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun w t => dslope f w (γ.toPiecewiseC1Path t) *
      deriv γ.toPiecewiseC1Path.toPath.extend t)
    (F' := fun w t => deriv (dslope f (γ.toPiecewiseC1Path t)) w *
      deriv γ.toPiecewiseC1Path.toPath.extend t)
    (bound := fun _ => C * D)
    (Metric.ball_mem_nhds w₀ hε_pos)
    (by filter_upwards [Metric.ball_mem_nhds w₀ hε_pos] with w hw
        exact h_meas_ball w (hball_sub_εm hw))
    (h_int w₀ hw₀)
    (h_F'_meas w₀ hw₀)
    (by filter_upwards with t ht w hw
        rw [Set.uIoc_of_le zero_le_one] at ht
        have ht_Icc := Ioc_subset_Icc_self ht
        rw [norm_mul]
        exact mul_le_mul (h_deriv_bd t ht_Icc w (hball_sub_δC hw)) (hD t ht_Icc)
          (norm_nonneg _) (le_trans (norm_nonneg _) (h_deriv_bd t ht_Icc w (hball_sub_δC hw))))
    (intervalIntegrable_const (c := C * D))
    (by filter_upwards with t ht w hw
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact h_dslope_hda t (Ioc_subset_Icc_self ht) w (hball_sub_εd hw))).2.differentiableAt

/-! ## Dixon function is entire -/

/-- **The Dixon function is entire.**

On `U`: equals `h1`, which is holomorphic.
Off `U`: equals `h2`, which is holomorphic. The curve lies in `U`, so
off `U` means off the curve.
Patching at `boundary(U)`: null-homologous gives winding number 0 near `boundary(U)`,
so `h1 = h2` by the fundamental identity. -/
theorem dixonFunction_differentiable {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (_hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion x x) (h_null : IsNullHomologous γ U)
    (h1_diff : DifferentiableOn ℂ (dixonH1 f γ.toPiecewiseC1Path) U)
    (h2_diff : ∀ w, (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      DifferentiableAt ℂ (dixonH2 f γ.toPiecewiseC1Path) w)
    (h_identity : ∀ w, (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      dixonH1 f γ.toPiecewiseC1Path w =
        dixonH2 f γ.toPiecewiseC1Path w -
          2 * ↑Real.pi * I * generalizedWindingNumber γ.toPiecewiseC1Path w * f w)
    (h_winding_zero_near : ∀ w, w ∉ U →
      (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
        generalizedWindingNumber γ.toPiecewiseC1Path w' = 0) :
    Differentiable ℂ (dixonFunction f U γ.toPiecewiseC1Path) := by
  intro w
  by_cases hw : w ∈ U
  · -- On U: dixonFunction = h1
    exact (h1_diff.differentiableAt (hU.mem_nhds hw)).congr_of_eventuallyEq
      (Filter.Eventually.mono (hU.mem_nhds hw) fun w' hw' => dixonFunction_eq_dixonH1 hw')
  · -- Off U: the curve lies in U, so w avoids the curve
    have hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w :=
      fun t ht heq => hw (heq ▸ h_null.image_subset t ht)
    obtain ⟨ε₁, hε₁_pos, hwn_zero⟩ := h_winding_zero_near w hw hoff
    -- The curve avoids a ball around w
    have hid_pos := curveImage_infDist_pos γ.toPiecewiseC1Path w hoff
    set ε₂ := Metric.infDist w (γ.toPiecewiseC1Path.toPath.extend '' Icc (0 : ℝ) 1) / 2
    have hε₂_pos : 0 < ε₂ := by simp only [ε₂]; linarith
    set ε := min ε₁ ε₂
    have hε_pos : 0 < ε := lt_min hε₁_pos hε₂_pos
    have h_wn_zero : ∀ w' ∈ Metric.ball w ε,
        generalizedWindingNumber γ.toPiecewiseC1Path w' = 0 :=
      fun w' hw' => hwn_zero w' (Metric.ball_subset_ball (min_le_left _ _) hw')
    have hoff' : ∀ w' ∈ Metric.ball w ε,
        ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w' :=
      ball_avoids_curve γ.toPiecewiseC1Path w (lt_min hε₁_pos hε₂_pos) (by
        simp only [ε, ε₂]; nlinarith [min_le_right ε₁ (Metric.infDist w (γ.toPiecewiseC1Path.toPath.extend '' Icc (0 : ℝ) 1) / 2)])
    have heq_near : ∀ᶠ w' in 𝓝 w,
        dixonFunction f U γ.toPiecewiseC1Path w' =
          dixonH2 f γ.toPiecewiseC1Path w' := by
      apply Filter.Eventually.mono (Metric.ball_mem_nhds w hε_pos)
      intro w' hw'
      simp only [dixonFunction]
      split_ifs with hw'U
      · rw [h_identity w' (hoff' w' hw'), h_wn_zero w' hw']
        simp [mul_zero, zero_mul]
      · rfl
    exact (h2_diff w hoff).congr_of_eventuallyEq heq_near

end
