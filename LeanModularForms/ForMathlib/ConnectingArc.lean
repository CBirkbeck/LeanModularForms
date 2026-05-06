/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Connecting arcs on circles

For HW Theorem 3.3 higher-order proof, when comparing the actual flat curve to
the sector model, we need to bound integrals over short arcs on the boundary
`{|z - s| = ε}`. This file provides the **partial-arc integral bound**:

  `‖∫_{θ₁}^{θ₂} f(circleMap c R θ) · circleMap'(c, R, θ) dθ‖ ≤ R · C · |θ₂ - θ₁|`

when `‖f‖ ≤ C` on the relevant arc.

This generalizes `circleIntegral.norm_integral_le_of_norm_le_const` (which is
only stated for the full `[0, 2π]` arc) to sub-arcs.

## Phase 3 context

In HW's argument:
- The connecting arcs at radius ε have `|θ₂ - θ₁| = o(ε^{n-1})` (by flatness +
  geometric arc-length-vs-chord bound at small angles).
- The integrand `1/(z-s)^k` has `‖f‖ ≤ 1/ε^k` on the arc.
- Combined: `‖integral over arc‖ ≤ ε · (1/ε^k) · o(ε^{n-1}) = o(ε^{n-k}) → 0`
  for `n ≥ k`.

This is the analytic mechanism behind HW's eq. (3.4) bound.
-/

open Complex Set Filter Topology MeasureTheory Real

noncomputable section

/-- **Norm of the circle-map derivative.** `‖d/dθ (circleMap c R θ)‖ = |R|`. -/
theorem norm_deriv_circleMap (c : ℂ) (R : ℝ) (θ : ℝ) :
    ‖deriv (circleMap c R) θ‖ = |R| := by
  rw [deriv_circleMap]
  simp [mul_one]

/-- **Partial-arc integral bound.** For `f : ℂ → ℂ` with `‖f(z)‖ ≤ C` on the arc
`circleMap c R '' uIcc θ₁ θ₂`, the partial-arc integral
`∫_{θ₁}^{θ₂} f(circleMap c R θ) · circleMap'(c, R, θ) dθ` has norm at most
`|R| · C · |θ₂ - θ₁|`.

This is the building block for Phase 3 connecting-arc bounds. -/
theorem norm_subarc_integral_le {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {θ₁ θ₂ : ℝ} {C : ℝ}
    (hf : ∀ θ ∈ uIcc θ₁ θ₂, ‖f (circleMap c R θ)‖ ≤ C) :
    ‖∫ θ in θ₁..θ₂, f (circleMap c R θ) * deriv (circleMap c R) θ‖ ≤
      |R| * C * |θ₂ - θ₁| := by
  have h_bound : ∀ θ ∈ Set.uIoc θ₁ θ₂,
      ‖f (circleMap c R θ) * deriv (circleMap c R) θ‖ ≤ |R| * C := by
    intro θ hθ
    rw [norm_mul, norm_deriv_circleMap]
    calc ‖f (circleMap c R θ)‖ * |R| ≤ C * |R| := by gcongr; exact hf θ (uIoc_subset_uIcc hθ)
      _ = |R| * C := by ring
  calc ‖∫ θ in θ₁..θ₂, f (circleMap c R θ) * deriv (circleMap c R) θ‖
      ≤ |R| * C * |θ₂ - θ₁| :=
        intervalIntegral.norm_integral_le_of_norm_le_const h_bound

end
