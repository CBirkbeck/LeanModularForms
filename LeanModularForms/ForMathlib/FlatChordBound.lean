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

/-! ### Pythagoras for the orthogonal decomposition -/

/-- **Pythagoras for `orthogonalProjectionComplex` and `tangentDeviation`.**
The squared norm of `w` decomposes into the squared norms of its parallel
projection on `L` and its orthogonal complement: this is the standard
orthogonal-decomposition identity in ℝ² (viewing ℂ as ℝ²). -/
theorem orthogonal_pythagoras (w L : ℂ) :
    ‖orthogonalProjectionComplex w L‖^2 + ‖tangentDeviation w L‖^2 = ‖w‖^2 := by
  rcases eq_or_ne L 0 with rfl | hL
  · simp [orthogonalProjectionComplex, tangentDeviation]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  unfold tangentDeviation orthogonalProjectionComplex
  simp only [Complex.real_smul]
  have hL_sq : Complex.normSq L ≠ 0 := (Complex.normSq_pos.mpr hL).ne'
  set u := (w * starRingEnd ℂ L).re with hu
  set N := Complex.normSq L with hN
  have h1 : Complex.normSq ((↑(u / N) : ℂ) * L) = (u / N) ^ 2 * N := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]; ring
  have h2 : (w * starRingEnd ℂ ((↑(u / N) : ℂ) * L)).re = (u / N) * u := by
    rw [map_mul, Complex.conj_ofReal]
    rw [show w * ((↑(u / N) : ℂ) * starRingEnd ℂ L) =
      (↑(u / N) : ℂ) * (w * starRingEnd ℂ L) from by ring]
    rw [Complex.mul_re]
    simp [hu]
  rw [Complex.normSq_sub, h1, h2]
  field_simp
  ring

/-- **Norm of the parallel projection.** From Pythagoras:
`‖orthogonalProjection w L‖² = ‖w‖² − ‖tangentDeviation w L‖²`. -/
theorem norm_sq_orthogonalProjection (w L : ℂ) :
    ‖orthogonalProjectionComplex w L‖ ^ 2 = ‖w‖ ^ 2 - ‖tangentDeviation w L‖ ^ 2 := by
  have := orthogonal_pythagoras w L
  linarith

/-! ### sqrt asymptotic: `ε − √(ε² − δ²) ≤ δ²/ε`

This is the key arithmetic estimate behind the parallel-projection-to-target
distance bound: when γ(t) is at radius ε from s with orthogonal deviation δ,
the parallel-component magnitude is `√(ε² − δ²)`, which is close to ε. The
shortfall `ε − √(ε² − δ²)` is bounded by `δ²/ε` (rationalization). -/

/-- **Sqrt shortfall bound.** For `0 ≤ δ ≤ ε` with `ε > 0`:
`ε − √(ε² − δ²) ≤ δ²/ε`.

Proof: rationalize `ε − √(ε² − δ²) = δ² / (ε + √(ε² − δ²)) ≤ δ²/ε` since
`√(ε² − δ²) ≥ 0`. -/
theorem real_sqrt_shortfall_le {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hle : δ ≤ ε) :
    ε - Real.sqrt (ε ^ 2 - δ ^ 2) ≤ δ ^ 2 / ε := by
  have h_sq_nonneg : 0 ≤ ε ^ 2 - δ ^ 2 := by nlinarith
  have h_sqrt_nonneg : 0 ≤ Real.sqrt (ε ^ 2 - δ ^ 2) := Real.sqrt_nonneg _
  have h_sqrt_sq : Real.sqrt (ε ^ 2 - δ ^ 2) ^ 2 = ε ^ 2 - δ ^ 2 :=
    Real.sq_sqrt h_sq_nonneg
  have h_eq :
      (ε - Real.sqrt (ε ^ 2 - δ ^ 2)) * (ε + Real.sqrt (ε ^ 2 - δ ^ 2)) = δ ^ 2 := by
    have : ε ^ 2 - Real.sqrt (ε ^ 2 - δ ^ 2) ^ 2 = δ ^ 2 := by
      rw [h_sqrt_sq]; ring
    linarith [this, sq_nonneg ε, sq_nonneg (Real.sqrt (ε ^ 2 - δ ^ 2))]
  have h_pos : 0 < ε + Real.sqrt (ε ^ 2 - δ ^ 2) := by linarith
  have h_diff_eq :
      ε - Real.sqrt (ε ^ 2 - δ ^ 2) = δ ^ 2 / (ε + Real.sqrt (ε ^ 2 - δ ^ 2)) := by
    field_simp
    linarith [h_eq]
  rw [h_diff_eq]
  apply div_le_div_of_nonneg_left (by positivity) hε (by linarith)

/-- **Norm shortfall from Pythagoras.** When `‖w‖ > 0`, the norm of the
parallel projection `‖orthogonalProj w L‖` is at most `‖w‖`, with shortfall
bounded by `‖tangentDev‖² / ‖w‖`:

`‖w‖ − ‖orthogonalProj w L‖ ≤ ‖tangentDev w L‖² / ‖w‖`.

Proof: From Pythagoras, `‖proj‖² = ‖w‖² − ‖tangentDev‖²`, so
`‖proj‖ = √(‖w‖² − ‖tangentDev‖²)`. Apply `real_sqrt_shortfall_le`. -/
theorem norm_orthogonalProjection_shortfall_le {w : ℂ} (L : ℂ) (hw : 0 < ‖w‖) :
    ‖w‖ - ‖orthogonalProjectionComplex w L‖ ≤ ‖tangentDeviation w L‖ ^ 2 / ‖w‖ := by
  have h_pyth := orthogonal_pythagoras w L
  have h_proj_sq :
      ‖orthogonalProjectionComplex w L‖ ^ 2 = ‖w‖ ^ 2 - ‖tangentDeviation w L‖ ^ 2 := by
    linarith
  have h_proj_nonneg : 0 ≤ ‖orthogonalProjectionComplex w L‖ := norm_nonneg _
  have h_dev_nonneg : 0 ≤ ‖tangentDeviation w L‖ := norm_nonneg _
  have h_sq_diff_nonneg : 0 ≤ ‖w‖ ^ 2 - ‖tangentDeviation w L‖ ^ 2 :=
    h_proj_sq ▸ sq_nonneg _
  have h_dev_le : ‖tangentDeviation w L‖ ≤ ‖w‖ := by
    nlinarith [h_sq_diff_nonneg, sq_nonneg ‖w‖]
  have h_sqrt := real_sqrt_shortfall_le hw h_dev_nonneg h_dev_le
  have h_sqrt_eq :
      Real.sqrt (‖w‖ ^ 2 - ‖tangentDeviation w L‖ ^ 2) =
        ‖orthogonalProjectionComplex w L‖ := by
    rw [← h_proj_sq]; exact Real.sqrt_sq h_proj_nonneg
  rw [h_sqrt_eq] at h_sqrt
  exact h_sqrt

end LeanModularForms
