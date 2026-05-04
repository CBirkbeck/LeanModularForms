/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Local strict monotonicity of `‖γ - s‖` near a transverse crossing

For a curve `γ : ℝ → ℂ` with `γ(t₀) = s`, `γ'(t₀) = L ≠ 0` (one-sided
derivative on the right), the function `‖γ(t) - s‖` is strictly increasing
in a small right-neighborhood of `t₀`. Symmetrically on the left.

This closes the shape-hypothesis derivation needed for the bridge in
`HW33Bridge.lean` (`shape_left_of_strictAntiOn` / `shape_right_of_strictMonoOn`).

## Strategy

We show `f(t) := ‖γ(t) - s‖²` is strictly monotone:

* `HasDerivAt.norm_sq` gives `f'(t) = 2 ⟨γ(t) - s, γ'(t)⟩_ℝ`.
* `slope γ t₀ t = (γ(t) - s) / (t - t₀) → L` as `t → t₀⁺`
  (`HasDerivWithinAt`).
* `γ'(t) → L` as `t → t₀⁺` (`Tendsto (deriv γ) ...`).
* By continuity of inner product, `⟨slope γ t₀ t, γ'(t)⟩ → ‖L‖² > 0`.
* Hence `f'(t) = 2 (t - t₀) · ⟨slope γ t₀ t, γ'(t)⟩ > 0` for `t` slightly
  above `t₀`.
* `strictMonoOn_of_hasDerivWithinAt_pos` ⇒ `f` is strictly monotone.
* Strict mono of `f = ‖·‖²` ⇒ strict mono of `‖·‖` (since `‖·‖ ≥ 0` and
  `· ↦ ·²` is strictly monotone on `[0, ∞)`).
-/

open Filter Topology Set Complex InnerProductSpace

noncomputable section

namespace LeanModularForms

/-! ## Strict monotonicity from transverse data -/

/-- **Strict monotonicity of `‖γ - s‖²` to the right of `t₀`.** -/
theorem exists_strictMonoOn_normSq_right_of_transverse
    {γ : ℝ → ℂ} {s : ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (h_s : γ t₀ = s)
    (h_deriv_right : HasDerivWithinAt γ L (Ici t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (h_smooth : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t)
    (hγ_cont : ContinuousAt γ t₀) :
    ∃ δ > (0 : ℝ),
      StrictMonoOn (fun t => ‖γ t - s‖ ^ 2) (Icc t₀ (t₀ + δ)) := by
  -- ‖L‖² > 0 since L ≠ 0
  have hL_normSq_pos : (0 : ℝ) < ‖L‖ ^ 2 := pow_pos (norm_pos_iff.mpr hL) 2
  -- slope γ t₀ → L on 𝓝[>] t₀ and ⟨slope·, deriv·⟩ → ‖L‖²
  have h_inner_tendsto :
      Tendsto (fun t => @inner ℝ ℂ _ (slope γ t₀ t) (deriv γ t))
        (𝓝[>] t₀) (𝓝 (‖L‖ ^ 2)) := by
    have h_slope : Tendsto (slope γ t₀) (𝓝[>] t₀) (𝓝 L) := by
      have h := hasDerivWithinAt_iff_tendsto_slope.mp h_deriv_right
      rwa [Ici_diff_left] at h
    have := ((continuous_inner (𝕜 := ℝ) (E := ℂ)).tendsto (L, L)).comp
      (h_slope.prodMk_nhds hL_right)
    rwa [show @inner ℝ ℂ _ L L = ‖L‖ ^ 2 from real_inner_self_eq_norm_sq L] at this
  -- Combine eventually-pos with smoothness, both on 𝓝[>] t₀
  have h_combined :
      ∀ᶠ t in 𝓝[>] t₀,
        DifferentiableAt ℝ γ t ∧
        ‖L‖ ^ 2 / 2 < @inner ℝ ℂ _ (slope γ t₀ t) (deriv γ t) :=
    h_smooth.and (h_inner_tendsto.eventually (eventually_gt_nhds (by linarith)))
  -- Extract a uniform δ > 0
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h_combined
  obtain ⟨δ, hδ_pos, h_uniform⟩ := h_combined
  refine ⟨δ / 2, by linarith, ?_⟩
  -- Apply strictMonoOn_of_hasDerivWithinAt_pos
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    (f' := fun t => 2 * @inner ℝ ℂ _ (γ t - s) (deriv γ t))
  · -- ContinuousOn (‖γ - s‖²) (Icc t₀ (t₀ + δ/2))
    apply ContinuousOn.pow
    apply ContinuousOn.norm
    refine ContinuousOn.sub ?_ continuousOn_const
    intro t ht
    rcases eq_or_lt_of_le ht.1 with ht_eq | ht_lt
    · rw [← ht_eq]; exact hγ_cont.continuousWithinAt
    · have ht_in_ball : dist t t₀ < δ := by
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht_lt)]
        linarith [ht.2]
      exact (h_uniform ht_in_ball ht_lt).1.continuousAt.continuousWithinAt
  · -- HasDerivWithinAt at each t in interior(Icc) = Ioo
    intro t ht
    rw [interior_Icc] at ht
    have ht_in_ball : dist t t₀ < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)]
      linarith [ht.2]
    exact ((h_uniform ht_in_ball ht.1).1.hasDerivAt.sub_const s).norm_sq.hasDerivWithinAt
  · -- Positivity of derivative on interior
    intro t ht
    rw [interior_Icc] at ht
    have ht_in_ball : dist t t₀ < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)]
      linarith [ht.2]
    have h_inner_gt := (h_uniform ht_in_ball ht.1).2
    -- Convert: 2 * inner (γ t - s) (deriv γ t) = 2(t - t₀) * inner (slope) (deriv γ)
    have ht_pos : (0 : ℝ) < t - t₀ := sub_pos.mpr ht.1
    simp only [slope_def_module, h_s] at h_inner_gt
    rw [real_inner_smul_left (γ t - s) (deriv γ t) (t - t₀)⁻¹] at h_inner_gt
    -- h_inner_gt : ‖L‖² / 2 < (t - t₀)⁻¹ * ⟪γ t - s, deriv γ t⟫
    have h_pos : 0 < @inner ℝ ℂ _ (γ t - s) (deriv γ t) := by
      have h := mul_lt_mul_of_pos_left h_inner_gt ht_pos
      rw [← mul_assoc, mul_inv_cancel₀ ht_pos.ne', one_mul] at h
      have : 0 < (t - t₀) * (‖L‖ ^ 2 / 2) := by positivity
      linarith
    linarith

/-- **Strict monotonicity of `‖γ - s‖` to the right of `t₀`** (from `‖γ - s‖²`).
Since `‖γ - s‖ ≥ 0` and `· ↦ ·²` is strictly monotone on `[0, ∞)`, strict
monotonicity of `‖γ - s‖²` implies strict monotonicity of `‖γ - s‖`. -/
theorem exists_strictMonoOn_norm_right_of_transverse
    {γ : ℝ → ℂ} {s : ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (h_s : γ t₀ = s)
    (h_deriv_right : HasDerivWithinAt γ L (Ici t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (h_smooth : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t)
    (hγ_cont : ContinuousAt γ t₀) :
    ∃ δ > (0 : ℝ),
      StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + δ)) := by
  obtain ⟨δ, hδ_pos, h_mono_sq⟩ := exists_strictMonoOn_normSq_right_of_transverse
    hL h_s h_deriv_right hL_right h_smooth hγ_cont
  refine ⟨δ, hδ_pos, ?_⟩
  intro a ha b hb hab
  have ha_sq : ‖γ a - s‖ ^ 2 < ‖γ b - s‖ ^ 2 := h_mono_sq ha hb hab
  nlinarith [ha_sq, norm_nonneg (γ a - s), norm_nonneg (γ b - s),
             sq_nonneg (‖γ a - s‖ - ‖γ b - s‖),
             sq_nonneg (‖γ a - s‖ + ‖γ b - s‖)]

/-! ## Symmetric left-side versions -/

/-- **Strict anti-monotonicity of `‖γ - s‖²` to the left of `t₀`** (symmetric of
`exists_strictMonoOn_normSq_right_of_transverse`). -/
theorem exists_strictAntiOn_normSq_left_of_transverse
    {γ : ℝ → ℂ} {s : ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (h_s : γ t₀ = s)
    (h_deriv_left : HasDerivWithinAt γ L (Iic t₀) t₀)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (h_smooth : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t)
    (hγ_cont : ContinuousAt γ t₀) :
    ∃ δ > (0 : ℝ),
      StrictAntiOn (fun t => ‖γ t - s‖ ^ 2) (Icc (t₀ - δ) t₀) := by
  -- ‖L‖² > 0 since L ≠ 0
  have hL_normSq_pos : (0 : ℝ) < ‖L‖ ^ 2 := pow_pos (norm_pos_iff.mpr hL) 2
  -- slope γ t₀ → L on 𝓝[<] t₀ and ⟨slope·, deriv·⟩ → ‖L‖²
  have h_inner_tendsto :
      Tendsto (fun t => @inner ℝ ℂ _ (slope γ t₀ t) (deriv γ t))
        (𝓝[<] t₀) (𝓝 (‖L‖ ^ 2)) := by
    have h_slope : Tendsto (slope γ t₀) (𝓝[<] t₀) (𝓝 L) := by
      have h := hasDerivWithinAt_iff_tendsto_slope.mp h_deriv_left
      rwa [Iic_diff_right] at h
    have := ((continuous_inner (𝕜 := ℝ) (E := ℂ)).tendsto (L, L)).comp
      (h_slope.prodMk_nhds hL_left)
    rwa [show @inner ℝ ℂ _ L L = ‖L‖ ^ 2 from real_inner_self_eq_norm_sq L] at this
  have h_combined :
      ∀ᶠ t in 𝓝[<] t₀,
        DifferentiableAt ℝ γ t ∧
        ‖L‖ ^ 2 / 2 < @inner ℝ ℂ _ (slope γ t₀ t) (deriv γ t) :=
    h_smooth.and (h_inner_tendsto.eventually (eventually_gt_nhds (by linarith)))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h_combined
  obtain ⟨δ, hδ_pos, h_uniform⟩ := h_combined
  refine ⟨δ / 2, by linarith, ?_⟩
  -- Apply strictAntiOn_of_hasDerivWithinAt_neg
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
    (f' := fun t => 2 * @inner ℝ ℂ _ (γ t - s) (deriv γ t))
  · -- ContinuousOn (‖γ - s‖²) (Icc (t₀ - δ/2) t₀)
    apply ContinuousOn.pow
    apply ContinuousOn.norm
    refine ContinuousOn.sub ?_ continuousOn_const
    intro t ht
    rcases eq_or_lt_of_le ht.2 with ht_eq | ht_lt
    · rw [ht_eq]; exact hγ_cont.continuousWithinAt
    · have ht_in_ball : dist t t₀ < δ := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr ht_lt)]
        linarith [ht.1]
      exact (h_uniform ht_in_ball ht_lt).1.continuousAt.continuousWithinAt
  · -- HasDerivWithinAt at each t in interior
    intro t ht
    rw [interior_Icc] at ht
    have ht_in_ball : dist t t₀ < δ := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr ht.2)]
      linarith [ht.1]
    exact ((h_uniform ht_in_ball ht.2).1.hasDerivAt.sub_const s).norm_sq.hasDerivWithinAt
  · -- Negativity of derivative on interior
    intro t ht
    rw [interior_Icc] at ht
    have ht_in_ball : dist t t₀ < δ := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr ht.2)]
      linarith [ht.1]
    have h_inner_gt := (h_uniform ht_in_ball ht.2).2
    have ht_neg : t - t₀ < 0 := sub_neg.mpr ht.2
    simp only [slope_def_module, h_s] at h_inner_gt
    rw [real_inner_smul_left (γ t - s) (deriv γ t) (t - t₀)⁻¹] at h_inner_gt
    -- For (t - t₀) < 0: multiply by (t - t₀), flip inequality
    -- (t - t₀) · ‖L‖²/2 > ⟪γ t - s, deriv γ t⟫
    -- LHS < 0, so ⟪γ t - s, deriv γ t⟫ < 0
    have h_neg_inner : @inner ℝ ℂ _ (γ t - s) (deriv γ t) < 0 := by
      have h := mul_lt_mul_of_neg_left h_inner_gt ht_neg
      rw [← mul_assoc, mul_inv_cancel₀ ht_neg.ne, one_mul] at h
      have h_lhs_neg : (t - t₀) * (‖L‖ ^ 2 / 2) < 0 := by
        have : ‖L‖ ^ 2 / 2 > 0 := by linarith
        nlinarith
      linarith
    linarith

/-- **Strict anti-monotonicity of `‖γ - s‖` to the left of `t₀`** (from
`‖γ - s‖²`). -/
theorem exists_strictAntiOn_norm_left_of_transverse
    {γ : ℝ → ℂ} {s : ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (h_s : γ t₀ = s)
    (h_deriv_left : HasDerivWithinAt γ L (Iic t₀) t₀)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (h_smooth : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t)
    (hγ_cont : ContinuousAt γ t₀) :
    ∃ δ > (0 : ℝ),
      StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - δ) t₀) := by
  obtain ⟨δ, hδ_pos, h_anti_sq⟩ := exists_strictAntiOn_normSq_left_of_transverse
    hL h_s h_deriv_left hL_left h_smooth hγ_cont
  refine ⟨δ, hδ_pos, ?_⟩
  intro a ha b hb hab
  have ha_sq : ‖γ b - s‖ ^ 2 < ‖γ a - s‖ ^ 2 := h_anti_sq ha hb hab
  nlinarith [ha_sq, norm_nonneg (γ a - s), norm_nonneg (γ b - s),
             sq_nonneg (‖γ a - s‖ - ‖γ b - s‖),
             sq_nonneg (‖γ a - s‖ + ‖γ b - s‖)]

end LeanModularForms

end
