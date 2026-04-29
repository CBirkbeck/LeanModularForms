/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.FlatnessConditions

/-!
# Chord-to-tangent bounds from flatness

For a curve `γ` flat of order `n` at `t₀` with `γ(t₀) = s` and one-sided
derivative `L ≠ 0`, this file derives bounds on the chord from `γ(t)` to the
"natural" tangent point on the radius-ε circle at distance `ε = ‖γ(t) - s‖`.

The natural tangent point is `s + (ε/‖L‖) • L`, i.e., the unique point on the
ray `s + ℝ₊ · L` at distance `ε`. The chord
`‖γ(t) - s - (ε/‖L‖) • L‖`
decomposes via Pythagoras into:
- An orthogonal piece (= `tangentDeviation (γ(t)-s) L`), of size `o(ε^n)` by
  flatness.
- A parallel correction (deviation of the parallel projection from `ε/‖L‖`),
  of size `o(ε^{2n-1})` by Pythagoras + sqrt asymptotic.

Both are dominated by `o(ε^n)` for `n ≥ 1`, giving `chord = o(ε^n)`.

## Phase 3 context

This is Phase 3.3 of the HW Theorem 3.3 higher-order proof (Sub-phase 3 in the
plan). It bridges the parameter-based flatness condition (`IsFlatOfOrder`) to
the radius-based bound needed for the connecting-arc analysis.

For now we provide the **orthogonal deviation bound** directly from the
definition, which is the cleanest extraction. The full chord bound (orthogonal
plus parallel correction) is left as a documented sub-task: it requires
Pythagoras + sqrt asymptotic.
-/

open Set Filter Topology Asymptotics

namespace LeanModularForms

/-- **Orthogonal deviation at exit-radius (right side).** Restatement of
`IsFlatOfOrder.right_flat` substituting `γ(t₀) = s`: the orthogonal deviation
of `γ(t) - s` from the tangent direction `L` is
`o(‖γ(t) - s‖^n)` as `t → t₀⁺`.

This is the bound used in Phase 3.3 chord analysis. -/
theorem orthogonal_deviation_at_radius_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n)
    (hL : L ≠ 0)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (h_s : γ t₀ = s) :
    (fun t : ℝ => ‖tangentDeviation (γ t - s) L‖) =o[𝓝[>] t₀]
      (fun t => ‖γ t - s‖ ^ n) := by
  have h := h_flat.right_flat L hL hL_right
  have h_eq : ∀ t, γ t - γ t₀ = γ t - s := by
    intro t; rw [h_s]
  simp only [h_eq] at h
  exact h

/-- **Orthogonal deviation at exit-radius (left side).** Symmetric version. -/
theorem orthogonal_deviation_at_radius_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n)
    (hL : L ≠ 0)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ t₀ = s) :
    (fun t : ℝ => ‖tangentDeviation (γ t - s) L‖) =o[𝓝[<] t₀]
      (fun t => ‖γ t - s‖ ^ n) := by
  have h := h_flat.left_flat L hL hL_left
  have h_eq : ∀ t, γ t - γ t₀ = γ t - s := by
    intro t; rw [h_s]
  simp only [h_eq] at h
  exact h

end LeanModularForms
