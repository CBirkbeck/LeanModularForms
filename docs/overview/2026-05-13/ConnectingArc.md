# ConnectingArc.lean

## theorem/norm_deriv_circleMap
- **Type**: `(c : ℂ) (R : ℝ) (θ : ℝ) → ‖deriv (circleMap c R) θ‖ = |R|`
- **What**: Norm of the circle-map derivative equals `|R|`.
- **How**: `rw [deriv_circleMap]; simp [mul_one]`.
- **Hypotheses**: none.
- **Uses-from-project**: [].
- **Used by**: `norm_subarc_integral_le` (same file).
- **Visibility**: public.
- **Lines**: ~39-42.
- **Notes**: Mathlib-style auxiliary; pure Mathlib usage.

## theorem/norm_subarc_integral_le
- **Type**: `{f : ℂ → ℂ} {c : ℂ} {R : ℝ} {θ₁ θ₂ : ℝ} {C : ℝ} (hf : ∀ θ ∈ uIcc θ₁ θ₂, ‖f (circleMap c R θ)‖ ≤ C) → ‖∫ θ in θ₁..θ₂, f (circleMap c R θ) * deriv (circleMap c R) θ‖ ≤ |R| * C * |θ₂ - θ₁|`
- **What**: Partial-arc integral bound for `f : ℂ → ℂ` with `‖f‖ ≤ C` on the arc — generalizes `circleIntegral.norm_integral_le_of_norm_le_const` from `[0, 2π]` to sub-arcs.
- **How**: Build pointwise `h_bound` via `norm_mul`, `norm_deriv_circleMap`, `gcongr`; conclude with `intervalIntegral.norm_integral_le_of_norm_le_const`.
- **Hypotheses**: `‖f‖ ≤ C` on `uIcc θ₁ θ₂`.
- **Uses-from-project**: `norm_deriv_circleMap`.
- **Used by**: HW Theorem 3.3 higher-order proofs (connecting-arc bounds at radius ε); Phase 3 sector model comparison.
- **Visibility**: public.
- **Lines**: ~50-62.
- **Notes**: Provides analytic mechanism behind HW eq. (3.4) bound; foundational for matching sector-model to true flat curve.

### File Summary
Two mathlib-style theorems providing the partial-arc integral bound on circles. Mathlib pure (no project deps); foundation for HW Theorem 3.3 Phase 3 connecting-arc analysis.
