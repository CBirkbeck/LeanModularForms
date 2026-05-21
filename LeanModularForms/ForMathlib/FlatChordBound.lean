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
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n : ℕ} (h_flat : IsFlatOfOrder γ t₀ n)
    (hL : L ≠ 0) (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)) (h_s : γ t₀ = s) :
    (fun t : ℝ => ‖tangentDeviation (γ t - s) L‖) =o[𝓝[>] t₀]
      (fun t => ‖γ t - s‖ ^ n) := by
  subst h_s
  exact h_flat.right_flat L hL hL_right

/-- **Orthogonal deviation at exit-radius (left side).** Symmetric version. -/
theorem orthogonal_deviation_at_radius_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n : ℕ} (h_flat : IsFlatOfOrder γ t₀ n)
    (hL : L ≠ 0) (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L)) (h_s : γ t₀ = s) :
    (fun t : ℝ => ‖tangentDeviation (γ t - s) L‖) =o[𝓝[<] t₀]
      (fun t => ‖γ t - s‖ ^ n) := by
  subst h_s
  exact h_flat.left_flat L hL hL_left

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
  set u := (w * starRingEnd ℂ L).re with hu
  set N := Complex.normSq L
  have hN_ne : N ≠ 0 := (Complex.normSq_pos.mpr hL).ne'
  have h1 : Complex.normSq ((↑(u / N) : ℂ) * L) = (u / N) ^ 2 * N := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  have h2 : (w * starRingEnd ℂ ((↑(u / N) : ℂ) * L)).re = (u / N) * u := by
    rw [map_mul, Complex.conj_ofReal,
      show w * ((↑(u / N) : ℂ) * starRingEnd ℂ L) =
        (↑(u / N) : ℂ) * (w * starRingEnd ℂ L) by ring,
      Complex.mul_re]
    simp [hu]
  rw [Complex.normSq_sub, h1, h2]
  field_simp
  ring

/-- **Norm of the parallel projection.** From Pythagoras:
`‖orthogonalProjection w L‖² = ‖w‖² − ‖tangentDeviation w L‖²`. -/
theorem norm_sq_orthogonalProjection (w L : ℂ) :
    ‖orthogonalProjectionComplex w L‖ ^ 2 = ‖w‖ ^ 2 - ‖tangentDeviation w L‖ ^ 2 := by
  linarith [orthogonal_pythagoras w L]

/-- **Sqrt shortfall bound.** For `0 ≤ δ ≤ ε` with `ε > 0`:
`ε − √(ε² − δ²) ≤ δ²/ε`.

Proof: rationalize `ε − √(ε² − δ²) = δ² / (ε + √(ε² − δ²)) ≤ δ²/ε` since
`√(ε² − δ²) ≥ 0`. -/
theorem real_sqrt_shortfall_le {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hle : δ ≤ ε) :
    ε - Real.sqrt (ε ^ 2 - δ ^ 2) ≤ δ ^ 2 / ε := by
  have h_sqrt_sq : Real.sqrt (ε ^ 2 - δ ^ 2) ^ 2 = ε ^ 2 - δ ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have h_sqrt_nn : 0 ≤ Real.sqrt (ε ^ 2 - δ ^ 2) := Real.sqrt_nonneg _
  rw [show ε - Real.sqrt (ε ^ 2 - δ ^ 2) =
      δ ^ 2 / (ε + Real.sqrt (ε ^ 2 - δ ^ 2)) by
    field_simp; nlinarith [h_sqrt_sq]]
  exact div_le_div_of_nonneg_left (by positivity) hε (by linarith)

/-- **Norm shortfall from Pythagoras.** When `‖w‖ > 0`, the norm of the
parallel projection `‖orthogonalProj w L‖` is at most `‖w‖`, with shortfall
bounded by `‖tangentDev‖² / ‖w‖`:

`‖w‖ − ‖orthogonalProj w L‖ ≤ ‖tangentDev w L‖² / ‖w‖`.

Proof: From Pythagoras, `‖proj‖² = ‖w‖² − ‖tangentDev‖²`, so
`‖proj‖ = √(‖w‖² − ‖tangentDev‖²)`. Apply `real_sqrt_shortfall_le`. -/
theorem norm_orthogonalProjection_shortfall_le {w : ℂ} (L : ℂ) (hw : 0 < ‖w‖) :
    ‖w‖ - ‖orthogonalProjectionComplex w L‖ ≤ ‖tangentDeviation w L‖ ^ 2 / ‖w‖ := by
  have h_proj_sq : ‖orthogonalProjectionComplex w L‖ ^ 2 =
      ‖w‖ ^ 2 - ‖tangentDeviation w L‖ ^ 2 := by linarith [orthogonal_pythagoras w L]
  have h_dev_le : ‖tangentDeviation w L‖ ≤ ‖w‖ := by
    nlinarith [h_proj_sq ▸ sq_nonneg (‖orthogonalProjectionComplex w L‖), sq_nonneg ‖w‖]
  have h_sqrt_eq : Real.sqrt (‖w‖ ^ 2 - ‖tangentDeviation w L‖ ^ 2) =
      ‖orthogonalProjectionComplex w L‖ := by
    rw [← h_proj_sq]; exact Real.sqrt_sq (norm_nonneg _)
  rw [← h_sqrt_eq]
  exact real_sqrt_shortfall_le hw (norm_nonneg _) h_dev_le

/-- **Same-direction shortfall.** If `Re(w · conj L) ≥ 0`, then the parallel
projection's distance to the same-magnitude target on the +L ray equals the
difference in magnitudes:

`‖orthogonalProj w L − (‖w‖/‖L‖) • L‖ = ‖w‖ − ‖orthogonalProj w L‖`. -/
theorem norm_orthogonalProjection_minus_target_eq {w L : ℂ} (hL : L ≠ 0)
    (h_pos : 0 ≤ (w * starRingEnd ℂ L).re) :
    ‖orthogonalProjectionComplex w L - (‖w‖ / ‖L‖ : ℝ) • L‖ =
      ‖w‖ - ‖orthogonalProjectionComplex w L‖ := by
  set c := (w * starRingEnd ℂ L).re / Complex.normSq L
  have hc_nonneg : 0 ≤ c := div_nonneg h_pos (Complex.normSq_pos.mpr hL).le
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have h_proj_norm : ‖orthogonalProjectionComplex w L‖ = c * ‖L‖ := by
    change ‖(c : ℝ) • L‖ = c * ‖L‖
    rw [norm_smul]
    simp [abs_of_nonneg hc_nonneg]
  have h_proj_le_w : ‖orthogonalProjectionComplex w L‖ ≤ ‖w‖ := by
    have h_sq : ‖orthogonalProjectionComplex w L‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      linarith [orthogonal_pythagoras w L, sq_nonneg ‖tangentDeviation w L‖]
    exact (abs_le_of_sq_le_sq' h_sq (norm_nonneg w)).2
  have h_c_le_div : c ≤ ‖w‖ / ‖L‖ := by
    rw [le_div_iff₀ hL_norm_pos, ← h_proj_norm]; exact h_proj_le_w
  change ‖(c : ℝ) • L - (‖w‖ / ‖L‖ : ℝ) • L‖ = ‖w‖ - ‖orthogonalProjectionComplex w L‖
  rw [show (c : ℝ) • L - (‖w‖ / ‖L‖ : ℝ) • L = (c - ‖w‖ / ‖L‖ : ℝ) • L by module,
    norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr h_c_le_div), h_proj_norm]
  field_simp
  ring

/-- **Chord-to-tangent bound.** When `w` is in the `+L` hemisphere
(`Re(w · conj L) ≥ 0`) and `‖w‖ > 0`, the chord from `w` to the
"natural" tangent target `(‖w‖/‖L‖) • L` is bounded by

  `‖tangentDev w L‖ + ‖tangentDev w L‖² / ‖w‖`

via the triangle inequality combined with `norm_orthogonalProjection_shortfall_le`
and `norm_orthogonalProjection_minus_target_eq`. -/
theorem norm_chord_to_tangent_target_le {w L : ℂ} (hL : L ≠ 0) (hw : 0 < ‖w‖)
    (h_pos : 0 ≤ (w * starRingEnd ℂ L).re) :
    ‖w - (‖w‖ / ‖L‖ : ℝ) • L‖ ≤
      ‖tangentDeviation w L‖ + ‖tangentDeviation w L‖ ^ 2 / ‖w‖ := by
  rw [show w - (‖w‖ / ‖L‖ : ℝ) • L =
      (orthogonalProjectionComplex w L - (‖w‖ / ‖L‖ : ℝ) • L) +
        tangentDeviation w L by unfold tangentDeviation; ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_orthogonalProjection_minus_target_eq hL h_pos]
  linarith [norm_orthogonalProjection_shortfall_le L hw]

end LeanModularForms
