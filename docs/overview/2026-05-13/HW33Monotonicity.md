# HW33Monotonicity.lean

**Path**: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HW33Monotonicity.lean
**Lines**: 210
**Imports**: `Mathlib.Analysis.InnerProductSpace.Calculus`, `Mathlib.Analysis.Calculus.Deriv.MeanValue`, `Mathlib.Analysis.Calculus.Deriv.Slope`, `Mathlib.Analysis.SpecialFunctions.Complex.Analytic`
**Namespace**: `LeanModularForms`

---

## theorem `exists_strictMonoOn_normSq_right_of_transverse`
- **Type**: `{γ : ℝ → ℂ} {s : ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0) (h_s : γ t₀ = s) (h_deriv_right : HasDerivWithinAt γ L (Ici t₀) t₀) (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)) (h_smooth : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t) (hγ_cont : ContinuousAt γ t₀) : ∃ δ > 0, StrictMonoOn (fun t => ‖γ t - s‖ ^ 2) (Icc t₀ (t₀ + δ))`
- **What**: For a transverse crossing γ(t₀) = s with right derivative L ≠ 0, `‖γ - s‖²` is strictly increasing on a right neighbourhood.
- **How** (>10 lines): Show `Tendsto (⟨slope γ t₀ t, deriv γ t⟩_ℝ) (𝓝[>] t₀) (𝓝 ‖L‖²)` by combining `hasDerivWithinAt_iff_tendsto_slope` (rewriting `Ici_diff_left`) with `hL_right` via `continuous_inner.tendsto.comp (h_slope.prodMk_nhds hL_right)` and `real_inner_self_eq_norm_sq`; combine with `h_smooth` via `.and (h_inner_tendsto.eventually (eventually_gt_nhds ...))` to get a δ-ball with uniform positivity of the inner product greater than `‖L‖²/2`; apply `strictMonoOn_of_hasDerivWithinAt_pos` with derivative `2 * ⟨γ t - s, deriv γ t⟩`, using `HasDerivAt.sub_const s` and `HasDerivAt.norm_sq` for differentiability and `real_inner_smul_left` to convert the slope-form inner product back to `⟨γ t - s, deriv γ t⟩`; continuity at the endpoint uses `hγ_cont.continuousWithinAt`.
- **Hypotheses**: nonzero one-sided derivative `L`, point-value `γ t₀ = s`, right HasDerivWithinAt, tendsto of derivative from the right, eventual differentiability from the right, continuity at t₀.
- **Uses-from-project**: none (mathlib-only proof).
- **Used by**: `exists_strictMonoOn_norm_right_of_transverse`.
- **Visibility**: public (in namespace).
- **Lines**: 45-105.
- **Notes**: Core right-side `‖·‖²` monotonicity, the foundation of the transverse-crossing shape lemma.

## theorem `exists_strictMonoOn_norm_right_of_transverse`
- **Type**: same hypotheses as the `_sq` version `: ∃ δ > 0, StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + δ))`
- **What**: Right-side strict monotonicity of `‖γ - s‖` (no square) for a transverse crossing.
- **How**: Obtain `δ, h_mono_sq` from `exists_strictMonoOn_normSq_right_of_transverse`; for `a < b` in `[t₀, t₀+δ]` apply `(sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp` to `h_mono_sq ha hb hab`.
- **Hypotheses**: same as the `_sq` version.
- **Uses-from-project**: `exists_strictMonoOn_normSq_right_of_transverse`.
- **Used by**: external (`HW33Bridge.lean`'s `shape_right_of_strictMonoOn`).
- **Visibility**: public.
- **Lines**: 110-122.
- **Notes**: Plain-norm corollary via square-root monotonicity.

## theorem `exists_strictAntiOn_normSq_left_of_transverse`
- **Type**: `{γ : ℝ → ℂ} {s : ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0) (h_s : γ t₀ = s) (h_deriv_left : HasDerivWithinAt γ L (Iic t₀) t₀) (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L)) (h_smooth : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t) (hγ_cont : ContinuousAt γ t₀) : ∃ δ > 0, StrictAntiOn (fun t => ‖γ t - s‖ ^ 2) (Icc (t₀ - δ) t₀)`
- **What**: Symmetric left-side version: `‖γ - s‖²` is strictly decreasing on `[t₀ - δ, t₀]` for a transverse crossing.
- **How** (>10 lines): Same structure as the right-side proof but with `𝓝[<] t₀`, `Iic_diff_right`, `abs_of_neg (sub_neg.mpr ...)`, `mul_lt_mul_of_neg_left`, and `strictAntiOn_of_hasDerivWithinAt_neg`. Concludes negativity of `⟨γ t - s, deriv γ t⟩` using `t - t₀ < 0` and `‖L‖²/2 > 0`.
- **Hypotheses**: nonzero one-sided derivative `L`, `γ t₀ = s`, left HasDerivWithinAt, tendsto of derivative from the left, eventual differentiability from the left, continuity at t₀.
- **Uses-from-project**: none.
- **Used by**: `exists_strictAntiOn_norm_left_of_transverse`.
- **Visibility**: public.
- **Lines**: 128-190.
- **Notes**: Left-side mirror of the main monotonicity theorem.

## theorem `exists_strictAntiOn_norm_left_of_transverse`
- **Type**: same hypotheses as the `_sq` version `: ∃ δ > 0, StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - δ) t₀)`
- **What**: Left-side strict anti-monotonicity of `‖γ - s‖` (no square).
- **How**: Obtain `δ, h_anti_sq` from `exists_strictAntiOn_normSq_left_of_transverse`; for `a < b` apply `(sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h_anti_sq ha hb hab)`.
- **Hypotheses**: same as `_sq` left version.
- **Uses-from-project**: `exists_strictAntiOn_normSq_left_of_transverse`.
- **Used by**: external (`HW33Bridge.lean`'s `shape_left_of_strictAntiOn`).
- **Visibility**: public.
- **Lines**: 194-206.
- **Notes**: Plain-norm corollary.

---

## File Summary

Strict monotonicity of `‖γ - s‖` (and its square) in a one-sided neighbourhood of a transverse crossing `γ(t₀) = s, γ'(t₀) = L ≠ 0`. Right-side (`exists_strictMonoOn_norm{Sq}_right_of_transverse`) and left-side (`exists_strictAntiOn_norm{Sq}_left_of_transverse`) versions are proved symmetrically. The strategy: `HasDerivAt.norm_sq` gives `f'(t) = 2 ⟨γ(t) - s, γ'(t)⟩`; combining the slope-tendsto from `HasDerivWithinAt` with the derivative-tendsto from the right/left and continuity of inner product yields `⟨slope γ t₀ t, deriv γ t⟩ → ‖L‖² > 0` (or via sign flip on the left), so for `t` near `t₀` the inner product is strictly positive (negative), and `strictMonoOn_of_hasDerivWithinAt_pos` (`strictAntiOn_of_hasDerivWithinAt_neg`) closes the square version. The plain-norm versions follow from `sq_lt_sq₀` and `norm_nonneg`. This file discharges the shape-hypothesis derivation used by `HW33Bridge.lean`.
