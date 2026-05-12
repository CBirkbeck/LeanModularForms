/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CrossingDataBuilder
import LeanModularForms.ForMathlib.WindingInteger

/-!
# Chord-to-tangent quotient limits (T-BR-Y3d Phase 1)

For a curve `γ : ℝ → ℂ` with one-sided derivative `L ≠ 0` at `t₀` and
`γ(t₀) = s`, the chord ratio `(γ(t) - s) / (t - t₀)` tends to `L` as `t → t₀`.

These limits are the analytic content used in the eventual CPV existence proof
at a transverse crossing: they govern the boundary behaviour of
`Complex.log(γ(t₀ ± δ(ε)) - s)` as `ε → 0⁺`.

## Main results

* `chord_div_t_tendsto_right` — `(γ(t) - s) / (t - t₀) → L_+` as `t → t₀⁺`.
* `chord_div_t_tendsto_left` — `(γ(t) - s) / (t - t₀) → L_-` as `t → t₀⁻`.

## Extended results (T-BR-Y3e: log convergence at exit time)

Given a positive cutoff function `δ_right : ℝ → ℝ` with `δ_right(ε) → 0⁺`
(typically the exit-time inversion `δ_right(ε) = strict_mono_inverse(...) ε`),
the **exit-point chord ratio** `(γ(t₀ + δ_right(ε)) - s) / δ_right(ε)` tends
to `L_+` as `ε → 0⁺`.

* `exit_chord_tendsto_right` — `(γ(t₀ + δ_right(ε)) - s) / δ_right(ε) → L_+`.
* `exit_chord_tendsto_left`  — analogous on the left.

These imply (via continuity of `Complex.arg` on `Complex.slitPlane`):

* `exit_arg_tendsto_right` — `arg(γ(t₀ + δ_right(ε)) - s) → arg L_+`
  modulo branch cut (assuming `L_+ ∈ Complex.slitPlane`).
* `exit_arg_tendsto_left` — analogous on the left.

Combining with the exit-time norm equation `‖γ(t₀ ± δ_•(ε)) - s‖ = ε`:

* `exit_log_tendsto_right` — `log(γ(t₀ + δ_right(ε)) - s) - log ε → arg L_+ · I`.
* `exit_log_tendsto_left` — analogous on the left, limit `arg(-L_-) · I`.
* `exit_log_diff_tendsto` — the **key cancellation**: the difference
  `log(γ(t₀+δ_right(ε)) - s) - log(γ(t₀-δ_left(ε)) - s)` is bounded and
  convergent as `ε → 0⁺`. The `log ε` divergent parts cancel symmetrically.

This convergence is the analytic core of the asymmetric CPV existence proof
at a transverse single crossing: it shows that the FTC-evaluated outer
integrals have a finite limit, paving the way for full CPV existence via the
forthcoming `segment_log_FTC` invocation on the smooth outer pieces.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

/-- **Right-side chord-to-tangent quotient limit.** Given `γ : ℝ → ℂ` with
`HasDerivWithinAt γ L (Ioi t₀) t₀` and `γ(t₀) = s`, the chord quotient
`(γ(t) - s) / (t - t₀)` tends to `L` as `t → t₀⁺`. -/
theorem chord_div_t_tendsto_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) :
    Tendsto (fun t : ℝ => (γ t - s) / ((t - t₀ : ℝ) : ℂ)) (𝓝[>] t₀) (𝓝 L) := by
  have hr := hasDerivWithinAt_iff_isLittleO.mp h_deriv
  -- Step 1: remainder `r(t) := γ(t) - γ(t₀) - (t - t₀) • L` satisfies
  -- `r(t) / (↑(t - t₀)) → 0` as `t → t₀⁺`.
  have h_rem_tendsto :
      Tendsto (fun t : ℝ => (γ t - γ t₀ - (t - t₀) • L) / ((t - t₀ : ℝ) : ℂ))
        (𝓝[>] t₀) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ_pos
    have h_pos_half : (0 : ℝ) < δ / 2 := by linarith
    filter_upwards [hr.def h_pos_half, self_mem_nhdsWithin] with t hb ht
    have h_pos : 0 < t - t₀ := sub_pos.mpr ht
    have h_norm_eq : ‖(t - t₀ : ℝ)‖ = t - t₀ := by
      rw [Real.norm_eq_abs, abs_of_pos h_pos]
    rw [dist_zero_right, norm_div, Complex.norm_real, h_norm_eq]
    rw [h_norm_eq] at hb
    rw [div_lt_iff₀ h_pos]
    have h_le : ‖γ t - γ t₀ - ((t - t₀) : ℝ) • L‖ ≤ δ / 2 * (t - t₀) := hb
    have h_lt : δ / 2 * (t - t₀) < δ * (t - t₀) := by
      have : 0 < δ * (t - t₀) := mul_pos hδ_pos h_pos
      nlinarith
    linarith
  -- Step 2: write `(γ(t) - s) / (↑(t - t₀)) = L + r(t) / (↑(t - t₀))`.
  have h_rewrite : ∀ᶠ t in 𝓝[>] t₀,
      (γ t - s) / ((t - t₀ : ℝ) : ℂ) =
        L + (γ t - γ t₀ - (t - t₀) • L) / ((t - t₀ : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h_pos : 0 < t - t₀ := sub_pos.mpr ht
    have h_ne_complex : ((t - t₀ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by linarith : t - t₀ ≠ 0)
    rw [h_at, Complex.real_smul]
    field_simp
    ring
  have h_add :
      Tendsto (fun t : ℝ => L + (γ t - γ t₀ - (t - t₀) • L) / ((t - t₀ : ℝ) : ℂ))
        (𝓝[>] t₀) (𝓝 L) := by
    have h_const : Tendsto (fun _ : ℝ => L) (𝓝[>] t₀) (𝓝 L) := tendsto_const_nhds
    simpa using h_const.add h_rem_tendsto
  exact h_add.congr' (h_rewrite.mono (fun _ h => h.symm))

/-- **Left-side chord-to-tangent quotient limit.** Given `γ : ℝ → ℂ` with
`HasDerivWithinAt γ L (Iio t₀) t₀` and `γ(t₀) = s`, the chord quotient
`(γ(t) - s) / (t - t₀)` tends to `L` as `t → t₀⁻`. -/
theorem chord_div_t_tendsto_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) :
    Tendsto (fun t : ℝ => (γ t - s) / ((t - t₀ : ℝ) : ℂ)) (𝓝[<] t₀) (𝓝 L) := by
  have hr := hasDerivWithinAt_iff_isLittleO.mp h_deriv
  have h_rem_tendsto :
      Tendsto (fun t : ℝ => (γ t - γ t₀ - (t - t₀) • L) / ((t - t₀ : ℝ) : ℂ))
        (𝓝[<] t₀) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ_pos
    have h_pos_half : (0 : ℝ) < δ / 2 := by linarith
    filter_upwards [hr.def h_pos_half, self_mem_nhdsWithin] with t hb ht
    have h_neg : t - t₀ < 0 := sub_neg_of_lt ht
    have h_pos : 0 < t₀ - t := sub_pos.mpr ht
    have h_norm_eq : ‖(t - t₀ : ℝ)‖ = t₀ - t := by
      rw [Real.norm_eq_abs, abs_of_neg h_neg]; ring
    rw [dist_zero_right, norm_div, Complex.norm_real, h_norm_eq]
    rw [h_norm_eq] at hb
    rw [div_lt_iff₀ h_pos]
    have h_le : ‖γ t - γ t₀ - ((t - t₀) : ℝ) • L‖ ≤ δ / 2 * (t₀ - t) := hb
    have h_lt : δ / 2 * (t₀ - t) < δ * (t₀ - t) := by nlinarith
    linarith
  have h_rewrite : ∀ᶠ t in 𝓝[<] t₀,
      (γ t - s) / ((t - t₀ : ℝ) : ℂ) =
        L + (γ t - γ t₀ - (t - t₀) • L) / ((t - t₀ : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h_neg : t - t₀ < 0 := sub_neg_of_lt ht
    have h_ne_complex : ((t - t₀ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by linarith : t - t₀ ≠ 0)
    rw [h_at, Complex.real_smul]
    field_simp
    ring
  have h_add :
      Tendsto (fun t : ℝ => L + (γ t - γ t₀ - (t - t₀) • L) / ((t - t₀ : ℝ) : ℂ))
        (𝓝[<] t₀) (𝓝 L) := by
    have h_const : Tendsto (fun _ : ℝ => L) (𝓝[<] t₀) (𝓝 L) := tendsto_const_nhds
    simpa using h_const.add h_rem_tendsto
  exact h_add.congr' (h_rewrite.mono (fun _ h => h.symm))

/-! ### Exit-point chord ratio convergence (T-BR-Y3e Step 2) -/

/-- **Right-side exit-point chord ratio convergence.** Given a positive cutoff
function `δ_right : ℝ → ℝ⁺` with `δ_right(ε) → 0⁺` as `ε → 0⁺`, the chord ratio
`(γ(t₀ + δ_right(ε)) - s) / δ_right(ε)` tends to `L_+` as `ε → 0⁺`.

This is a composition: `chord_div_t_tendsto_right` gives the limit
`(γ(t) - s)/(t - t₀) → L_+` as `t → t₀⁺`, and the map
`ε ↦ t₀ + δ_right(ε)` carries `𝓝[>] 0` to `𝓝[>] t₀` (since `δ_right > 0`
and `δ_right → 0⁺`). -/
theorem exit_chord_tendsto_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s)
    {δ_right : ℝ → ℝ}
    (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_right ε)
    (hδ_to_zero : Tendsto δ_right (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ))) :
    Tendsto (fun ε : ℝ => (γ (t₀ + δ_right ε) - s) / ((δ_right ε : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  -- Compose: ε ↦ t₀ + δ_right(ε) sends 𝓝[>] 0 to 𝓝[>] t₀.
  have h_compose : Tendsto (fun ε : ℝ => t₀ + δ_right ε)
      (𝓝[>] (0 : ℝ)) (𝓝[>] t₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · -- t₀ + δ_right(ε) → t₀ as ε → 0⁺, since δ_right(ε) → 0.
      have h_to_zero : Tendsto δ_right (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        hδ_to_zero.mono_right nhdsWithin_le_nhds
      have h_const : Tendsto (fun _ : ℝ => t₀) (𝓝[>] (0 : ℝ)) (𝓝 t₀) :=
        tendsto_const_nhds
      simpa using h_const.add h_to_zero
    · filter_upwards [hδ_pos] with ε hε using by
        change t₀ < t₀ + δ_right ε
        linarith
  -- Apply chord_div_t_tendsto_right to the composition.
  have h_chord := chord_div_t_tendsto_right h_deriv h_at
  have h_comp := h_chord.comp h_compose
  -- Rewrite the composition expression.
  refine h_comp.congr' ?_
  filter_upwards [hδ_pos] with ε hε
  simp only [Function.comp_apply]
  congr 1
  · -- (γ(t₀ + δ_right ε) - s) / (↑(t₀ + δ_right ε - t₀)) =
    --   (γ(t₀ + δ_right ε) - s) / (↑(δ_right ε))
    congr 2
    ring

/-- **Left-side exit-point chord ratio convergence.** Symmetric to
`exit_chord_tendsto_right`: with `δ_left → 0⁺`, the chord ratio
`(γ(t₀ - δ_left(ε)) - s) / (-δ_left(ε)) → L_-` as `ε → 0⁺`.

(Note the sign: `t - t₀ = -δ_left(ε) < 0`, so dividing by `t - t₀` gives the
right limit `L_-`. Equivalently, `(γ(t₀ - δ_left(ε)) - s) / δ_left(ε) → -L_-`.) -/
theorem exit_chord_tendsto_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s)
    {δ_left : ℝ → ℝ}
    (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_left ε)
    (hδ_to_zero : Tendsto δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ))) :
    Tendsto (fun ε : ℝ => (γ (t₀ - δ_left ε) - s) / ((-(δ_left ε) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  -- Compose: ε ↦ t₀ - δ_left(ε) sends 𝓝[>] 0 to 𝓝[<] t₀.
  have h_compose : Tendsto (fun ε : ℝ => t₀ - δ_left ε)
      (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h_to_zero : Tendsto δ_left (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        hδ_to_zero.mono_right nhdsWithin_le_nhds
      have h_const : Tendsto (fun _ : ℝ => t₀) (𝓝[>] (0 : ℝ)) (𝓝 t₀) :=
        tendsto_const_nhds
      simpa using h_const.sub h_to_zero
    · filter_upwards [hδ_pos] with ε hε using by
        change t₀ - δ_left ε < t₀
        linarith
  -- Apply chord_div_t_tendsto_left to the composition.
  have h_chord := chord_div_t_tendsto_left h_deriv h_at
  have h_comp := h_chord.comp h_compose
  -- Rewrite the composition expression.
  refine h_comp.congr' ?_
  filter_upwards [hδ_pos] with ε hε
  simp only [Function.comp_apply]
  congr 1
  · -- (γ(t₀ - δ_left ε) - s) / (↑(t₀ - δ_left ε - t₀)) =
    --   (γ(t₀ - δ_left ε) - s) / (↑(-(δ_left ε)))
    congr 2
    ring

/-! ### Arg convergence at exit times -/

/-- **Right-side exit-point arg convergence.** If `L_+ ∈ Complex.slitPlane`
(i.e. is not a non-positive real), then
`arg(γ(t₀ + δ_right(ε)) - s) → arg L_+` as `ε → 0⁺`.

This follows from `exit_chord_tendsto_right` (giving directional convergence
to `L_+`) and continuity of `Complex.arg` on the slit plane. Importantly, the
arg is unchanged under positive real scaling, so the limit of the unit-direction
`(γ(t₀ + δ_right(ε)) - s) / δ_right(ε)` and the original `γ(t₀ + δ_right(ε)) - s`
have the same arg. -/
theorem exit_arg_tendsto_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s)
    (hL_slit : L ∈ Complex.slitPlane)
    {δ_right : ℝ → ℝ}
    (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_right ε)
    (hδ_to_zero : Tendsto δ_right (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ))) :
    Tendsto (fun ε : ℝ => Complex.arg (γ (t₀ + δ_right ε) - s))
      (𝓝[>] (0 : ℝ)) (𝓝 L.arg) := by
  -- Apply Complex.continuousAt_arg at L (which is in slitPlane).
  have h_arg_cont : ContinuousAt Complex.arg L := Complex.continuousAt_arg hL_slit
  -- Quotient `(γ - s) / δ_right ε → L`.
  have h_quot := exit_chord_tendsto_right h_deriv h_at hδ_pos hδ_to_zero
  -- arg is invariant under positive real scaling:
  -- arg(z) = arg(z / r) for r > 0 real.
  have h_arg_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Complex.arg ((γ (t₀ + δ_right ε) - s) / ((δ_right ε : ℝ) : ℂ)) =
        Complex.arg (γ (t₀ + δ_right ε) - s) := by
    filter_upwards [hδ_pos] with ε hε
    have hε_inv_pos : (0 : ℝ) < (δ_right ε)⁻¹ := inv_pos.mpr hε
    have h_rewrite : (γ (t₀ + δ_right ε) - s) / ((δ_right ε : ℝ) : ℂ) =
        (((δ_right ε)⁻¹ : ℝ) : ℂ) * (γ (t₀ + δ_right ε) - s) := by
      push_cast
      rw [div_eq_inv_mul]
    rw [h_rewrite]
    exact Complex.arg_real_mul _ hε_inv_pos
  -- Apply continuity of arg to the convergent quotient, then transfer via h_arg_eq.
  have h_comp : Tendsto (fun ε : ℝ =>
      Complex.arg ((γ (t₀ + δ_right ε) - s) / ((δ_right ε : ℝ) : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 L.arg) := h_arg_cont.tendsto.comp h_quot
  exact h_comp.congr' h_arg_eq

/-- **Left-side exit-point arg convergence.** If `-L_- ∈ Complex.slitPlane`, then
`arg(γ(t₀ - δ_left(ε)) - s) → arg(-L_-)` as `ε → 0⁺`.

(For the LEFT, `t - t₀ = -δ_left(ε) < 0`, so the chord-to-tangent gives
`(γ(t₀ - δ_left(ε)) - s) ≈ -δ_left(ε) · L_- = δ_left(ε) · (-L_-)`. Hence the arg
limit is `arg(-L_-)`.) -/
theorem exit_arg_tendsto_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s)
    (hnegL_slit : -L ∈ Complex.slitPlane)
    {δ_left : ℝ → ℝ}
    (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_left ε)
    (hδ_to_zero : Tendsto δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ))) :
    Tendsto (fun ε : ℝ => Complex.arg (γ (t₀ - δ_left ε) - s))
      (𝓝[>] (0 : ℝ)) (𝓝 (-L).arg) := by
  -- Apply Complex.continuousAt_arg at -L (which is in slitPlane).
  have h_arg_cont : ContinuousAt Complex.arg (-L) := Complex.continuousAt_arg hnegL_slit
  -- Quotient `(γ - s) / (-(δ_left ε)) → L`, hence `(γ - s) / δ_left ε → -L`.
  have h_quot := exit_chord_tendsto_left h_deriv h_at hδ_pos hδ_to_zero
  -- Build the positive-denominator version `(γ - s) / δ_left ε → -L`.
  -- Strategy: negate the function in h_quot using Tendsto.neg, then rewrite
  -- `-(γ - s)/(-δ_left ε) = (γ - s)/(δ_left ε)`.
  have h_neg : Tendsto (fun ε : ℝ => -((γ (t₀ - δ_left ε) - s) /
      ((-(δ_left ε) : ℝ) : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 (-L)) := h_quot.neg
  have h_quot' :
      Tendsto (fun ε : ℝ => (γ (t₀ - δ_left ε) - s) / ((δ_left ε : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (-L)) := by
    refine h_neg.congr' ?_
    filter_upwards [hδ_pos] with ε hε
    have hε_ne : ((δ_left ε : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hε)
    have h_cast : ((-(δ_left ε) : ℝ) : ℂ) = -((δ_left ε : ℝ) : ℂ) := by push_cast; ring
    rw [h_cast, div_neg, neg_neg]
  -- arg is invariant under positive real scaling.
  have h_arg_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Complex.arg ((γ (t₀ - δ_left ε) - s) / ((δ_left ε : ℝ) : ℂ)) =
        Complex.arg (γ (t₀ - δ_left ε) - s) := by
    filter_upwards [hδ_pos] with ε hε
    have hε_inv_pos : (0 : ℝ) < (δ_left ε)⁻¹ := inv_pos.mpr hε
    have h_rewrite : (γ (t₀ - δ_left ε) - s) / ((δ_left ε : ℝ) : ℂ) =
        (((δ_left ε)⁻¹ : ℝ) : ℂ) * (γ (t₀ - δ_left ε) - s) := by
      push_cast
      rw [div_eq_inv_mul]
    rw [h_rewrite]
    exact Complex.arg_real_mul _ hε_inv_pos
  have h_comp : Tendsto (fun ε : ℝ =>
      Complex.arg ((γ (t₀ - δ_left ε) - s) / ((δ_left ε : ℝ) : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (-L).arg) := h_arg_cont.tendsto.comp h_quot'
  exact h_comp.congr' h_arg_eq

/-! ### Log convergence at exit times (combining norm and arg) -/

/-- **Log convergence on the right at the exit time.** If `‖γ(t₀ + δ_right(ε)) - s‖ = ε`
(exit-time property) and `L_+ ∈ Complex.slitPlane`, then
`Complex.log(γ(t₀ + δ_right(ε)) - s) - Real.log ε → (Complex.I * L_+.arg)` as `ε → 0⁺`.

Decompose `Complex.log z = Real.log ‖z‖ + I·arg(z)`. The norm term equals
`Real.log ε` (using the exit-time property), so it cancels. The arg term tends
to `arg L_+` by `exit_arg_tendsto_right`. -/
theorem exit_log_tendsto_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s)
    (hL_slit : L ∈ Complex.slitPlane)
    {δ_right : ℝ → ℝ}
    (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_right ε)
    (hδ_to_zero : Tendsto δ_right (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)))
    (h_exit : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖γ (t₀ + δ_right ε) - s‖ = ε) :
    Tendsto (fun ε : ℝ =>
      Complex.log (γ (t₀ + δ_right ε) - s) - ((Real.log ε : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (L.arg * Complex.I)) := by
  -- Express log z = Real.log ‖z‖ + arg z * I.
  -- Then log(γ(...)-s) - Real.log ε = Real.log ‖γ(...)-s‖ - Real.log ε + arg(...) * I
  --                                = 0 + arg(...) * I
  -- which tends to arg L * I.
  have h_arg := exit_arg_tendsto_right h_deriv h_at hL_slit hδ_pos hδ_to_zero
  -- Function we want to compute: log(γ-s) - Real.log ε.
  have h_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Complex.log (γ (t₀ + δ_right ε) - s) - ((Real.log ε : ℝ) : ℂ) =
        ((γ (t₀ + δ_right ε) - s).arg : ℂ) * Complex.I := by
    filter_upwards [h_exit, hδ_pos] with ε h_exit_ε _hδ_pos_ε
    -- log(γ-s) = Real.log ‖γ-s‖ + arg(γ-s) * I, and ‖γ-s‖ = ε.
    have h_log_decomp :
        Complex.log (γ (t₀ + δ_right ε) - s) =
          ((Real.log ‖γ (t₀ + δ_right ε) - s‖ : ℝ) : ℂ) +
            ((γ (t₀ + δ_right ε) - s).arg : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [Complex.log_re]
      · simp [Complex.log_im]
    rw [h_log_decomp, h_exit_ε]
    ring
  -- Now apply h_arg via continuity of (· * I) at L.arg.
  have h_mul_I : Tendsto (fun ε : ℝ =>
      ((γ (t₀ + δ_right ε) - s).arg : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝 (L.arg * Complex.I)) := by
    have h_cast : Tendsto (fun ε : ℝ => ((γ (t₀ + δ_right ε) - s).arg : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (L.arg : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp h_arg
    have h_const : Tendsto (fun _ : ℝ => Complex.I) (𝓝[>] (0 : ℝ)) (𝓝 Complex.I) :=
      tendsto_const_nhds
    exact h_cast.mul h_const
  exact h_mul_I.congr' (h_eq.mono (fun _ h => h.symm))

/-- **Log convergence on the left at the exit time.** Symmetric to the right side. -/
theorem exit_log_tendsto_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s)
    (hnegL_slit : -L ∈ Complex.slitPlane)
    {δ_left : ℝ → ℝ}
    (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_left ε)
    (hδ_to_zero : Tendsto δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)))
    (h_exit : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖γ (t₀ - δ_left ε) - s‖ = ε) :
    Tendsto (fun ε : ℝ =>
      Complex.log (γ (t₀ - δ_left ε) - s) - ((Real.log ε : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L).arg * Complex.I)) := by
  have h_arg := exit_arg_tendsto_left h_deriv h_at hnegL_slit hδ_pos hδ_to_zero
  have h_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Complex.log (γ (t₀ - δ_left ε) - s) - ((Real.log ε : ℝ) : ℂ) =
        ((γ (t₀ - δ_left ε) - s).arg : ℂ) * Complex.I := by
    filter_upwards [h_exit, hδ_pos] with ε h_exit_ε _hδ_pos_ε
    have h_log_decomp :
        Complex.log (γ (t₀ - δ_left ε) - s) =
          ((Real.log ‖γ (t₀ - δ_left ε) - s‖ : ℝ) : ℂ) +
            ((γ (t₀ - δ_left ε) - s).arg : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [Complex.log_re]
      · simp [Complex.log_im]
    rw [h_log_decomp, h_exit_ε]
    ring
  have h_mul_I : Tendsto (fun ε : ℝ =>
      ((γ (t₀ - δ_left ε) - s).arg : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L).arg * Complex.I)) := by
    have h_cast : Tendsto (fun ε : ℝ => ((γ (t₀ - δ_left ε) - s).arg : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 ((-L).arg : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp h_arg
    have h_const : Tendsto (fun _ : ℝ => Complex.I) (𝓝[>] (0 : ℝ)) (𝓝 Complex.I) :=
      tendsto_const_nhds
    exact h_cast.mul h_const
  exact h_mul_I.congr' (h_eq.mono (fun _ h => h.symm))

/-- **Symmetric log difference at exit times.** This is the central
T-BR-Y3e quantity:
`Complex.log(γ(t₀ + δ_right(ε)) - s) - Complex.log(γ(t₀ - δ_left(ε)) - s)`
tends to `(arg L_+ - arg(-L_-)) * I` as `ε → 0⁺`.

The divergent `Real.log ε` terms cancel between the two sides. Only the arg
parts contribute. This is the analytic core of the CPV existence proof: it
shows that the boundary log values at the two exit points are bounded and
convergent as `ε → 0⁺`. -/
theorem exit_log_diff_tendsto
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L_right L_left : ℂ}
    (h_deriv_right : HasDerivWithinAt γ L_right (Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ L_left (Iio t₀) t₀)
    (h_at : γ t₀ = s)
    (hL_right_slit : L_right ∈ Complex.slitPlane)
    (hnegL_left_slit : -L_left ∈ Complex.slitPlane)
    {δ_left δ_right : ℝ → ℝ}
    (hδ_left_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_left ε)
    (hδ_right_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_right ε)
    (hδ_left_to_zero : Tendsto δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)))
    (hδ_right_to_zero : Tendsto δ_right (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)))
    (h_exit_left : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖γ (t₀ - δ_left ε) - s‖ = ε)
    (h_exit_right : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖γ (t₀ + δ_right ε) - s‖ = ε) :
    Tendsto (fun ε : ℝ =>
      Complex.log (γ (t₀ + δ_right ε) - s) -
        Complex.log (γ (t₀ - δ_left ε) - s))
      (𝓝[>] (0 : ℝ)) (𝓝 (L_right.arg * Complex.I - (-L_left).arg * Complex.I)) := by
  -- Use exit_log_tendsto_right and exit_log_tendsto_left, then subtract.
  -- (log(R) - log ε) - (log(L) - log ε) = log(R) - log(L).
  have h_right := exit_log_tendsto_right h_deriv_right h_at hL_right_slit
    hδ_right_pos hδ_right_to_zero h_exit_right
  have h_left := exit_log_tendsto_left h_deriv_left h_at hnegL_left_slit
    hδ_left_pos hδ_left_to_zero h_exit_left
  -- Difference: (log(R) - log ε) - (log(L) - log ε) = log(R) - log(L).
  have h_diff := h_right.sub h_left
  refine h_diff.congr' ?_
  refine Eventually.of_forall fun ε => ?_
  ring

/-! ### Slit-plane on small one-sided intervals (T-BR-Y3f Step 3)

For an immersion `γ` with right derivative `L ≠ 0` at `t₀`, the normalized
chord `(γ(t) - s) / (L * (t - t₀))` is close to `1` for `t` near `t₀⁺`. This
gives slit-plane conditions on quotients `(γ(b) - s) / (γ(a) - s)` for `a, b`
both near `t₀⁺` (and similarly on the left). These slit-plane conditions are
the analytic input for the FTC on small annular pieces, which together with
the log-difference cancellation (T-BR-Y3e) yield CPV existence. -/

/-- **Normalized chord close to 1 (right side).** For any `ρ > 0`, eventually
on `𝓝[>] t₀`, `‖(γ(t) - s) / (L · (t - t₀)) - 1‖ ≤ ρ`.

This is the key chord-to-tangent estimate in normalized form. -/
theorem normalized_chord_close_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∀ᶠ t in 𝓝[>] t₀,
      ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  -- chord_div_t_tendsto_right gives (γ t - s) / (t - t₀) → L.
  -- Divide by L: (γ t - s) / (L · (t - t₀)) → 1.
  have h_chord := chord_div_t_tendsto_right h_deriv h_at
  -- Tendsto.div_const by L (which is nonzero).
  have h_div : Tendsto
      (fun t : ℝ => (γ t - s) / ((t - t₀ : ℝ) : ℂ) / L)
      (𝓝[>] t₀) (𝓝 (L / L)) :=
    h_chord.div_const _
  have hLL : L / L = 1 := div_self hL
  rw [hLL] at h_div
  -- Convert (γ t - s) / (t - t₀) / L = (γ t - s) / (L · (t - t₀)).
  have h_eq : ∀ᶠ t in 𝓝[>] t₀,
      (γ t - s) / ((t - t₀ : ℝ) : ℂ) / L =
        (γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h_pos : 0 < t - t₀ := sub_pos.mpr ht
    have h_ne : ((t - t₀ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt h_pos)
    field_simp
  have h_tendsto_one : Tendsto
      (fun t : ℝ => (γ t - s) / (L * ((t - t₀ : ℝ) : ℂ))) (𝓝[>] t₀) (𝓝 1) := by
    exact h_div.congr' h_eq
  -- Extract eventually-close from tendsto.
  rw [Metric.tendsto_nhds] at h_tendsto_one
  have h_eventually := h_tendsto_one ρ hρ_pos
  filter_upwards [h_eventually] with t ht
  rw [dist_eq_norm] at ht
  exact ht.le

/-- **Normalized chord close to 1 (left side).** Note the sign: on the left, the
relevant tangent is `-L_-` and `t - t₀ < 0`, so we work with `(t₀ - t) > 0`. -/
theorem normalized_chord_close_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∀ᶠ t in 𝓝[<] t₀,
      ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  have h_chord := chord_div_t_tendsto_left h_deriv h_at
  have h_div : Tendsto
      (fun t : ℝ => (γ t - s) / ((t - t₀ : ℝ) : ℂ) / L)
      (𝓝[<] t₀) (𝓝 (L / L)) :=
    h_chord.div_const _
  have hLL : L / L = 1 := div_self hL
  rw [hLL] at h_div
  have h_eq : ∀ᶠ t in 𝓝[<] t₀,
      (γ t - s) / ((t - t₀ : ℝ) : ℂ) / L =
        (γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h_neg : t - t₀ < 0 := sub_neg_of_lt ht
    have h_ne : ((t - t₀ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_lt h_neg)
    field_simp
  have h_tendsto_one : Tendsto
      (fun t : ℝ => (γ t - s) / (L * ((t - t₀ : ℝ) : ℂ))) (𝓝[<] t₀) (𝓝 1) := by
    exact h_div.congr' h_eq
  rw [Metric.tendsto_nhds] at h_tendsto_one
  have h_eventually := h_tendsto_one ρ hρ_pos
  filter_upwards [h_eventually] with t ht
  rw [dist_eq_norm] at ht
  exact ht.le

/-- **Fixed-radius normalized chord bound (right side).** From the eventual
bound, extract a positive radius `r > 0` such that the bound holds uniformly
on `(t₀, t₀ + r]`. -/
theorem exists_normalized_chord_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∃ r > 0, ∀ t ∈ Ioc t₀ (t₀ + r),
      ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  have h_ev := normalized_chord_close_right h_deriv h_at hL hρ_pos
  rw [Filter.eventually_iff_exists_mem] at h_ev
  obtain ⟨U, hU_mem, hU_prop⟩ := h_ev
  rw [mem_nhdsWithin] at hU_mem
  obtain ⟨V, hV_open, ht₀_in_V, hV_sub⟩ := hU_mem
  rw [Metric.isOpen_iff] at hV_open
  obtain ⟨r, hr_pos, hr_ball⟩ := hV_open t₀ ht₀_in_V
  refine ⟨r / 2, by linarith, fun t ht_in => ?_⟩
  have h_gt : t₀ < t := ht_in.1
  have h_le : t ≤ t₀ + r / 2 := ht_in.2
  have h_in_V : t ∈ V := by
    apply hr_ball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < t - t₀)]
    linarith
  exact hU_prop t (hV_sub ⟨h_in_V, mem_Ioi.mpr h_gt⟩)

/-- **Fixed-radius normalized chord bound (left side).** -/
theorem exists_normalized_chord_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∃ r > 0, ∀ t ∈ Ico (t₀ - r) t₀,
      ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  have h_ev := normalized_chord_close_left h_deriv h_at hL hρ_pos
  rw [Filter.eventually_iff_exists_mem] at h_ev
  obtain ⟨U, hU_mem, hU_prop⟩ := h_ev
  rw [mem_nhdsWithin] at hU_mem
  obtain ⟨V, hV_open, ht₀_in_V, hV_sub⟩ := hU_mem
  rw [Metric.isOpen_iff] at hV_open
  obtain ⟨r, hr_pos, hr_ball⟩ := hV_open t₀ ht₀_in_V
  refine ⟨r / 2, by linarith, fun t ht_in => ?_⟩
  have h_ge : t₀ - r / 2 ≤ t := ht_in.1
  have h_lt : t < t₀ := ht_in.2
  have h_in_V : t ∈ V := by
    apply hr_ball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith : t - t₀ < 0)]
    linarith
  exact hU_prop t (hV_sub ⟨h_in_V, mem_Iio.mpr h_lt⟩)

/-! ### Slit-plane condition for chord quotients -/

/-- **Slit-plane condition for chord quotients.** If `‖z - 1‖ ≤ 1/4` and
`‖w - 1‖ ≤ 1/4`, then `z / w ∈ slitPlane` (specifically `Re(z/w) > 0`).

The proof uses `‖z/w - 1‖ = ‖z-w‖/‖w‖ ≤ (1/2)/(3/4) = 2/3 < 1`, giving
`Re(z/w) > 0` via `|Re(z/w) - 1| ≤ |z/w - 1| < 1`. -/
theorem div_mem_slitPlane_of_close_to_one {z w : ℂ}
    (hz : ‖z - 1‖ ≤ 1 / 4) (hw : ‖w - 1‖ ≤ 1 / 4) :
    z / w ∈ Complex.slitPlane := by
  have hw_ne : w ≠ 0 := by
    intro hw_eq
    rw [hw_eq, zero_sub, norm_neg, norm_one] at hw
    linarith
  have h_zw : ‖z - w‖ ≤ 1 / 2 := by
    calc ‖z - w‖ = ‖(z - 1) - (w - 1)‖ := by congr 1; ring
      _ ≤ ‖z - 1‖ + ‖w - 1‖ := norm_sub_le _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add hz hw
      _ = 1 / 2 := by ring
  have hw_norm_ge : (3 : ℝ) / 4 ≤ ‖w‖ := by
    have h_sub_nn := norm_sub_norm_le (1 : ℂ) w
    have h1 : (1 : ℝ) - ‖w‖ ≤ ‖w - 1‖ := by
      rw [show ((1 : ℂ) - w) = -(w - 1) from by ring, norm_neg, norm_one] at h_sub_nn
      exact h_sub_nn
    linarith
  have hw_pos : 0 < ‖w‖ := by linarith
  have h_diff : z / w - 1 = (z - w) / w := by field_simp
  have h_diff_norm : ‖z / w - 1‖ < 1 := by
    rw [h_diff, norm_div]
    -- ‖z-w‖ / ‖w‖ ≤ (1/2) / (3/4) = 2/3 < 1.
    have h_quot : ‖z - w‖ / ‖w‖ ≤ 2 / 3 := by
      rw [div_le_iff₀ hw_pos]
      have h1 : ‖z - w‖ ≤ 2 / 3 * (3 / 4) := by linarith
      have h2 : 2 / 3 * (3 / 4) ≤ 2 / 3 * ‖w‖ :=
        mul_le_mul_of_nonneg_left hw_norm_ge (by norm_num : (0 : ℝ) ≤ 2 / 3)
      linarith
    linarith
  -- Re(z/w) > 0 from |z/w - 1| < 1.
  rw [Complex.mem_slitPlane_iff]
  left
  have h_re : |(z / w - 1).re| < 1 := by
    have := Complex.abs_re_le_norm (z / w - 1)
    linarith
  have h_re_eq : (z / w - 1).re = (z / w).re - 1 := by simp
  rw [h_re_eq] at h_re
  rw [abs_sub_lt_iff] at h_re
  linarith

/-- **Slit-plane on small right interval.** There exists `r > 0` such that for
all `a, b` with `t₀ < a ≤ b ≤ t₀ + r`, the chord quotient
`(γ(b) - s) / (γ(a) - s) ∈ Complex.slitPlane`.

This follows from chord-to-tangent: the normalized quantities
`(γ(b)-s)/(L·(b-t₀))` and `(γ(a)-s)/(L·(a-t₀))` are both close to `1` for
`a, b` near `t₀⁺`, and their ratio (times positive real `(b-t₀)/(a-t₀)`) is
in slitPlane. -/
theorem exists_slitPlane_chord_quotient_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_right h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun a b ha_gt hab hb_le => ?_⟩
  have ha_le : a ≤ t₀ + r := le_trans hab hb_le
  have hb_gt : t₀ < b := lt_of_lt_of_le ha_gt hab
  -- Set up
  have ha_in : a ∈ Ioc t₀ (t₀ + r) := ⟨ha_gt, ha_le⟩
  have hb_in : b ∈ Ioc t₀ (t₀ + r) := ⟨hb_gt, hb_le⟩
  have ha_pos : 0 < a - t₀ := sub_pos.mpr ha_gt
  have hb_pos : 0 < b - t₀ := sub_pos.mpr hb_gt
  have ha_pos_C : ((a - t₀ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt ha_pos)
  have hb_pos_C : ((b - t₀ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hb_pos)
  -- Apply the chord bounds
  have hb_bound := hr_close b hb_in
  have ha_bound := hr_close a ha_in
  -- ‖(γ a - s) / (L * (a - t₀)) - 1‖ ≤ 1/3 says (γ a - s)/(L*(a-t₀)) is close to 1.
  -- So `(γ a - s)/(L*(a-t₀)) ≠ 0`, in particular `γ a - s ≠ 0`.
  have ha_chord_ne : (γ a - s) / (L * ((a - t₀ : ℝ) : ℂ)) ≠ 0 := by
    intro h_eq
    rw [h_eq, zero_sub, norm_neg, norm_one] at ha_bound
    linarith
  have h_La_ne : L * ((a - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL ha_pos_C
  have ha_ne : γ a - s ≠ 0 := by
    intro h_eq
    rw [h_eq, zero_div] at ha_chord_ne
    exact ha_chord_ne rfl
  -- Set z := (γ b - s)/(L*(b-t₀)), w := (γ a - s)/(L*(a-t₀))
  -- z/w = ((γ b - s)/(L*(b-t₀))) / ((γ a - s)/(L*(a-t₀)))
  --     = ((γ b - s) / (γ a - s)) * ((a - t₀)/(b - t₀))
  -- Since (a-t₀)/(b-t₀) > 0 real, slit-plane is preserved by multiplying by positive real.
  set z := (γ b - s) / (L * ((b - t₀ : ℝ) : ℂ))
  set w := (γ a - s) / (L * ((a - t₀ : ℝ) : ℂ))
  have h_zw : z / w ∈ Complex.slitPlane :=
    div_mem_slitPlane_of_close_to_one hb_bound ha_bound
  -- Rewrite (γ b - s) / (γ a - s) = (z/w) * ((b - t₀)/(a - t₀))
  have h_ratio : (γ b - s) / (γ a - s) =
      (((b - t₀) / (a - t₀) : ℝ) : ℂ) * (z / w) := by
    have hL_ab : L * ((b - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL hb_pos_C
    have hL_aa : L * ((a - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL ha_pos_C
    rw [show (γ b - s) / (γ a - s) =
        (z * (L * ((b - t₀ : ℝ) : ℂ))) / (w * (L * ((a - t₀ : ℝ) : ℂ))) from by
      congr 1
      · simp only [z]; exact (div_mul_cancel₀ _ hL_ab).symm
      · simp only [w]; exact (div_mul_cancel₀ _ hL_aa).symm]
    push_cast
    field_simp
  rw [h_ratio]
  -- Positive real scaling preserves slit-plane.
  have h_pos_ratio : 0 < (b - t₀) / (a - t₀) := div_pos hb_pos ha_pos
  rw [show (((b - t₀) / (a - t₀) : ℝ) : ℂ) * (z / w) =
        (((b - t₀) / (a - t₀) : ℝ) : ℂ) * (z / w) from rfl]
  -- Use: positive real · slitPlane ⊆ slitPlane.
  rw [Complex.mem_slitPlane_iff] at h_zw ⊢
  rcases h_zw with h_re | h_im
  · left
    have : (((b - t₀) / (a - t₀) : ℝ) : ℂ).re = (b - t₀) / (a - t₀) :=
      Complex.ofReal_re _
    simp only [Complex.mul_re, this, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos h_pos_ratio h_re
  · right
    have h_re_pos : (((b - t₀) / (a - t₀) : ℝ) : ℂ).re = (b - t₀) / (a - t₀) :=
      Complex.ofReal_re _
    have h_im_zero : (((b - t₀) / (a - t₀) : ℝ) : ℂ).im = 0 := Complex.ofReal_im _
    simp only [Complex.mul_im, h_re_pos, h_im_zero, zero_mul, add_zero]
    exact mul_ne_zero (ne_of_gt h_pos_ratio) h_im

/-- **Slit-plane on small left interval (forward direction).** There exists
`r > 0` such that for all `a, b` with `t₀ - r ≤ a ≤ b < t₀`, the chord quotient
`(γ(b) - s) / (γ(a) - s) ∈ Complex.slitPlane`.

This is the FTC-relevant form: the FTC `segment_log_FTC` requires
`(γ(t) - s) / (γ(a) - s) ∈ slitPlane` for `t ∈ [a, b]` (where `a` is the left
endpoint). Here `b` is closer to `t₀`, so `γ(b) - s` is smaller in magnitude. -/
theorem exists_slitPlane_chord_quotient_left_forward
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_left h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun a b ha_ge hab hb_lt => ?_⟩
  have ha_lt : a < t₀ := lt_of_le_of_lt hab hb_lt
  have hb_ge : t₀ - r ≤ b := le_trans ha_ge hab
  have ha_in : a ∈ Ico (t₀ - r) t₀ := ⟨ha_ge, ha_lt⟩
  have hb_in : b ∈ Ico (t₀ - r) t₀ := ⟨hb_ge, hb_lt⟩
  have ha_neg : a - t₀ < 0 := sub_neg_of_lt ha_lt
  have hb_neg : b - t₀ < 0 := sub_neg_of_lt hb_lt
  have ha_neg_C : ((a - t₀ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_lt ha_neg)
  have hb_neg_C : ((b - t₀ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_lt hb_neg)
  have hb_bound := hr_close b hb_in
  have ha_bound := hr_close a ha_in
  have ha_chord_ne : (γ a - s) / (L * ((a - t₀ : ℝ) : ℂ)) ≠ 0 := by
    intro h_eq
    rw [h_eq, zero_sub, norm_neg, norm_one] at ha_bound
    linarith
  have h_La_ne : L * ((a - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL ha_neg_C
  have ha_ne : γ a - s ≠ 0 := by
    intro h_eq
    rw [h_eq, zero_div] at ha_chord_ne
    exact ha_chord_ne rfl
  -- We want (γ b - s)/(γ a - s). Here a is farther from t₀, b closer.
  -- Set z := (γ b - s)/(L*(b - t₀)), w := (γ a - s)/(L*(a - t₀)).
  -- Both close to 1 (ρ = 1/4). So z/w ∈ slitPlane.
  -- (γ b - s)/(γ a - s) = (z/w) * ((b - t₀)/(a - t₀)).
  set z := (γ b - s) / (L * ((b - t₀ : ℝ) : ℂ))
  set w := (γ a - s) / (L * ((a - t₀ : ℝ) : ℂ))
  have h_zw : z / w ∈ Complex.slitPlane :=
    div_mem_slitPlane_of_close_to_one hb_bound ha_bound
  have h_ratio : (γ b - s) / (γ a - s) =
      (((b - t₀) / (a - t₀) : ℝ) : ℂ) * (z / w) := by
    have hL_aa : L * ((a - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL ha_neg_C
    have hL_bb : L * ((b - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL hb_neg_C
    rw [show (γ b - s) / (γ a - s) =
        (z * (L * ((b - t₀ : ℝ) : ℂ))) / (w * (L * ((a - t₀ : ℝ) : ℂ))) from by
      congr 1
      · simp only [z]; exact (div_mul_cancel₀ _ hL_bb).symm
      · simp only [w]; exact (div_mul_cancel₀ _ hL_aa).symm]
    push_cast
    field_simp
  rw [h_ratio]
  have h_pos_ratio : 0 < (b - t₀) / (a - t₀) := div_pos_of_neg_of_neg hb_neg ha_neg
  rw [Complex.mem_slitPlane_iff] at h_zw ⊢
  rcases h_zw with h_re | h_im
  · left
    have : (((b - t₀) / (a - t₀) : ℝ) : ℂ).re = (b - t₀) / (a - t₀) :=
      Complex.ofReal_re _
    simp only [Complex.mul_re, this, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos h_pos_ratio h_re
  · right
    have h_re_pos : (((b - t₀) / (a - t₀) : ℝ) : ℂ).re = (b - t₀) / (a - t₀) :=
      Complex.ofReal_re _
    have h_im_zero : (((b - t₀) / (a - t₀) : ℝ) : ℂ).im = 0 := Complex.ofReal_im _
    simp only [Complex.mul_im, h_re_pos, h_im_zero, zero_mul, add_zero]
    exact mul_ne_zero (ne_of_gt h_pos_ratio) h_im

/-- **Slit-plane on small left interval (backward direction).** There exists
`r > 0` such that for all `a, b` with `t₀ - r ≤ a ≤ b < t₀`, the chord quotient
`(γ(a) - s) / (γ(b) - s) ∈ Complex.slitPlane`.

(Note the ORDER: on the left, the FTC-relevant quotient is "later relative to
the curve direction" over "earlier", i.e., closer to `t₀` over further.) -/
theorem exists_slitPlane_chord_quotient_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ a - s) / (γ b - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_left h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun a b ha_ge hab hb_lt => ?_⟩
  have ha_lt : a < t₀ := lt_of_le_of_lt hab hb_lt
  have hb_ge : t₀ - r ≤ b := le_trans ha_ge hab
  have ha_in : a ∈ Ico (t₀ - r) t₀ := ⟨ha_ge, ha_lt⟩
  have hb_in : b ∈ Ico (t₀ - r) t₀ := ⟨hb_ge, hb_lt⟩
  have ha_neg : a - t₀ < 0 := sub_neg_of_lt ha_lt
  have hb_neg : b - t₀ < 0 := sub_neg_of_lt hb_lt
  have ha_neg_C : ((a - t₀ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_lt ha_neg)
  have hb_neg_C : ((b - t₀ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_lt hb_neg)
  have hb_bound := hr_close b hb_in
  have ha_bound := hr_close a ha_in
  have hb_chord_ne : (γ b - s) / (L * ((b - t₀ : ℝ) : ℂ)) ≠ 0 := by
    intro h_eq
    rw [h_eq, zero_sub, norm_neg, norm_one] at hb_bound
    linarith
  have h_Lb_ne : L * ((b - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL hb_neg_C
  have hb_ne : γ b - s ≠ 0 := by
    intro h_eq
    rw [h_eq, zero_div] at hb_chord_ne
    exact hb_chord_ne rfl
  set z := (γ a - s) / (L * ((a - t₀ : ℝ) : ℂ))
  set w := (γ b - s) / (L * ((b - t₀ : ℝ) : ℂ))
  have h_zw : z / w ∈ Complex.slitPlane :=
    div_mem_slitPlane_of_close_to_one ha_bound hb_bound
  -- Rewrite (γ a - s) / (γ b - s) = (z/w) * ((a - t₀)/(b - t₀))
  -- where (a - t₀)/(b - t₀) > 0 (both negative).
  have h_ratio : (γ a - s) / (γ b - s) =
      (((a - t₀) / (b - t₀) : ℝ) : ℂ) * (z / w) := by
    have hL_aa : L * ((a - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL ha_neg_C
    have hL_bb : L * ((b - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL hb_neg_C
    rw [show (γ a - s) / (γ b - s) =
        (z * (L * ((a - t₀ : ℝ) : ℂ))) / (w * (L * ((b - t₀ : ℝ) : ℂ))) from by
      congr 1
      · simp only [z]; exact (div_mul_cancel₀ _ hL_aa).symm
      · simp only [w]; exact (div_mul_cancel₀ _ hL_bb).symm]
    push_cast
    field_simp
  rw [h_ratio]
  have h_pos_ratio : 0 < (a - t₀) / (b - t₀) := div_pos_of_neg_of_neg ha_neg hb_neg
  rw [Complex.mem_slitPlane_iff] at h_zw ⊢
  rcases h_zw with h_re | h_im
  · left
    have : (((a - t₀) / (b - t₀) : ℝ) : ℂ).re = (a - t₀) / (b - t₀) :=
      Complex.ofReal_re _
    simp only [Complex.mul_re, this, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos h_pos_ratio h_re
  · right
    have h_re_pos : (((a - t₀) / (b - t₀) : ℝ) : ℂ).re = (a - t₀) / (b - t₀) :=
      Complex.ofReal_re _
    have h_im_zero : (((a - t₀) / (b - t₀) : ℝ) : ℂ).im = 0 := Complex.ofReal_im _
    simp only [Complex.mul_im, h_re_pos, h_im_zero, zero_mul, add_zero]
    exact mul_ne_zero (ne_of_gt h_pos_ratio) h_im

/-! ### FTC on small annular pieces

For a curve `γ` smooth on `(t₀, t₀+r]` (resp. `[t₀-r, t₀)`) avoiding `s`, with
slit-plane condition `(γ(b) - s) / (γ(a) - s) ∈ slitPlane` for `a, b` in the
interval, the integral `∫_a^b γ'/(γ-s) dt = log((γ(b)-s)/(γ(a)-s))` by the FTC
of `segment_log_FTC`. -/

/-- **FTC on right annular piece via slit-plane.** Given `a, b` with
`t₀ < a ≤ b ≤ t₀+r` such that the chord quotients are in slit-plane, and the
curve is integrable on `[a,b]`, the integral equals the log difference. -/
theorem annulus_FTC_right
    {γ : ℝ → ℂ} {s : ℂ} {a b : ℝ}
    (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    {P : Set ℝ} (hP_count : P.Countable)
    (hγ_diff : ∀ t ∈ Ioo a b \ P, HasDerivAt γ (deriv γ t) t)
    (h_ne : γ a - s ≠ 0)
    (h_slit : ∀ t ∈ Icc a b, (γ t - s) / (γ a - s) ∈ Complex.slitPlane)
    (h_int : IntervalIntegrable
      (fun t => deriv γ t / (γ t - s)) MeasureTheory.volume a b) :
    ∫ t in a..b, deriv γ t / (γ t - s) =
      Complex.log ((γ b - s) / (γ a - s)) := by
  exact segment_log_FTC hab hP_count hγ_cont hγ_diff h_ne h_slit h_int

/-! ### CPV existence on the level of immersion data

The next theorem packages the chord-to-tangent slit-plane condition + FTC
machinery into a full `HasCauchyPV` existence result. The strategy:

1. Pick a fixed radius `r > 0` smaller than both the slit-plane radii and the
   threshold.
2. Split the outer integral at radius `r` from `t₀`: outer = `[0, t₀-r] ∪
   [t₀+r, 1]` (fixed) + `[t₀-r, t₀-δL(ε)] ∪ [t₀+δR(ε), t₀+r]` (shrinking
   annuli).
3. By FTC, the shrinking annuli contribute
   `[log(γ(t₀-δL(ε))-s) - log(γ(t₀-r)-s)] +
    [log(γ(t₀+r)-s) - log(γ(t₀+δR(ε))-s)]`.
4. By T-BR-Y3e (`exit_log_diff_tendsto`), the difference
   `log(γ(t₀+δR(ε))-s) - log(γ(t₀-δL(ε))-s)` converges as `ε → 0⁺`.
5. Combine: `I(ε) = constant + log(γ(t₀+r)-s) - log(γ(t₀-r)-s) -
   [log(γ(t₀+δR(ε))-s) - log(γ(t₀-δL(ε))-s)] → finite limit`.

This is the analytic core of the CPV existence proof.

### Implementation

We assemble the CPV existence theorem using the building blocks above. -/

/-- **FTC on a right annular piece via the explicit chord-quotient slit-plane
condition.** For `t₀ < a ≤ b`, with curve `γ` admitting derivative `L` from
the right at `t₀`, suitable continuity/differentiability, and slit-plane
condition on quotients, the integral equals the log difference. -/
theorem right_annulus_log_FTC
    (γ : ℝ → ℂ) {s : ℂ} {t₀ a b : ℝ}
    (_ht₀_lt_a : t₀ < a) (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    {P : Set ℝ} (hP_count : P.Countable)
    (hγ_diff : ∀ t ∈ Ioo a b \ P, HasDerivAt γ (deriv γ t) t)
    (h_ne_a : γ a - s ≠ 0)
    (h_slit : ∀ t ∈ Icc a b, (γ t - s) / (γ a - s) ∈ Complex.slitPlane)
    (h_int : IntervalIntegrable
      (fun t => deriv γ t / (γ t - s)) MeasureTheory.volume a b) :
    ∫ t in a..b, deriv γ t / (γ t - s) =
      Complex.log ((γ b - s) / (γ a - s)) :=
  segment_log_FTC hab hP_count hγ_cont hγ_diff h_ne_a h_slit h_int

/-! ### CPV existence via FTC + log-difference cancellation

We now combine all building blocks into the CPV existence theorem. The
strategy follows the plan above:

1. The cutoff integral splits via `cutoff_integral_eq_outer_sum`.
2. The outer-sum further splits at radius `r` (chosen smaller than slit-plane
   radii and the threshold).
3. The fixed parts `[0, t₀-r] ∪ [t₀+r, 1]` give a constant.
4. The annular parts apply `segment_log_FTC` to express as log differences.
5. The log-divergence at the exit times cancels via T-BR-Y3e.

The full assembly is intricate. We expose the key intermediate result —
the annular log-difference — as a separate theorem so that downstream callers
can assemble the convergence directly. -/

/-- **Right annular log-difference via FTC.** For `γ` with right derivative
`L_right ≠ 0` at `t₀` (in slit-plane), and for `0 < δ_R < r` such that
the slit-plane radius `r_R` and the integrability conditions hold, the
integral on `[t₀ + δ_R, t₀ + r]` equals
`log((γ(t₀ + r) - s) / (γ(t₀ + δ_R) - s))`.

This is a direct application of `segment_log_FTC` on the right annular
piece, using the slit-plane condition from
`exists_slitPlane_chord_quotient_right`. -/
theorem right_annular_log_diff
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    {L_right : ℂ} (_hL_right_ne : L_right ≠ 0)
    (_h_deriv_right : HasDerivWithinAt
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_right (Ioi t₀) t₀)
    (_h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    {r δ_R : ℝ} (hδ_R_pos : 0 < δ_R) (hδ_R_lt : δ_R < r) (_hr_pos : 0 < r)
    (hr_le_one_sub : t₀ + r ≤ 1)
    (h_slit_R : ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
        Complex.slitPlane)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (ht₀_pos : 0 < t₀) :
    ∫ t in (t₀ + δ_R)..(t₀ + r),
      deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s) =
    Complex.log
      ((γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + r) - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + δ_R) - s)) := by
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  set a : ℝ := t₀ + δ_R
  set b : ℝ := t₀ + r
  have hab : a ≤ b := by simp only [a, b]; linarith
  have ha_gt : t₀ < a := by simp only [a]; linarith
  have hb_le : b ≤ t₀ + r := by simp only [b]; linarith
  -- Slit-plane on [a, b]: (γ t - s)/(γ a - s) ∈ slitPlane for t ∈ [a, b].
  have h_slit_ab : ∀ t ∈ Icc a b, (γf t - s) / (γf a - s) ∈ Complex.slitPlane := by
    intro t ht_in
    apply h_slit_R a t ha_gt ht_in.1 (le_trans ht_in.2 hb_le)
  -- γ a - s ≠ 0 since t₀ < a and h_unique says only t₀ maps to s.
  have ha_ne : γf a - s ≠ 0 := by
    intro h_eq
    have h_in_01 : a ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith, by linarith⟩
    have : a = t₀ := h_unique a h_in_01 (sub_eq_zero.mp h_eq)
    linarith
  -- Continuity of γf on [a, b].
  have hγ_cont : ContinuousOn γf (Icc a b) :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousOn
  -- Differentiability off partition: P := γ.partition, countable (finite).
  set P : Set ℝ := ↑γ.toPwC1Immersion.toPiecewiseC1Path.partition with hP_def
  have hP_count : P.Countable :=
    γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.countable
  have hγ_diff : ∀ t ∈ Ioo a b \ P, HasDerivAt γf (deriv γf t) t := by
    intro t ht
    have ht_in_Ioo : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨by linarith [ht.1.1, ht₀_pos, hδ_R_pos], by linarith [ht.1.2, hr_le_one_sub]⟩
    have h_diff_at : DifferentiableAt ℝ γf t :=
      γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off t ht_in_Ioo ht.2
    exact h_diff_at.hasDerivAt
  -- Integrability of γ'/(γ-s) on [a, b].
  have h_int : IntervalIntegrable
      (fun t => deriv γf t / (γf t - s)) MeasureTheory.volume a b := by
    -- We have inv_sub_mul_deriv_intervalIntegrable_right but that's for `(γ-s)⁻¹ * γ'`.
    -- Adapt via congr.
    have h1 := inv_sub_mul_deriv_intervalIntegrable_right γ
      (by exact ⟨ht₀_pos, by linarith [hr_le_one_sub, hδ_R_pos, hδ_R_lt]⟩ :
        t₀ ∈ Ioo (0 : ℝ) 1) (δ_right_ε := δ_R) hδ_R_pos
      (by linarith [hb_le, hr_le_one_sub] : δ_R < 1 - t₀) h_unique
    refine h1.mono_set ?_ |>.congr (fun t _ => ?_)
    · simp only [a, b, Set.uIcc_of_le hab,
        Set.uIcc_of_le (by linarith [hb_le, hr_le_one_sub] : t₀ + δ_R ≤ 1)]
      exact Set.Icc_subset_Icc le_rfl (by linarith [hr_le_one_sub])
    · simp only [hγf_def]
      ring
  exact segment_log_FTC hab hP_count hγ_cont hγ_diff ha_ne h_slit_ab h_int

/-! ### Exit-time equality (T-BR-Y3f auxiliary)

From the public `h_near_right` and `h_far_right` bounds in `DerivedAsymmetricCutoffs`,
we derive `‖γ(t₀ + δ_right ε) - s‖ = ε` via squeezing and continuity. -/

/-- **Right exit-time equality.** `‖γ(t₀ + δ_right ε) - s‖ = ε`. -/
theorem exit_time_eq_right
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (D : DerivedAsymmetricCutoffs γ s t₀)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold) :
    ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + D.δ_right ε) - s‖ = ε := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ)
  have hδR_pos := D.hδ_right_pos ε hε_pos hε_lt
  have hδR_small := D.hδ_right_small ε hε_pos hε_lt
  have h_le : ‖γf (t₀ + D.δ_right ε) - s‖ ≤ ε :=
    D.h_near_right ε hε_pos hε_lt (t₀ + D.δ_right ε) (by linarith) (by linarith)
  have hγ_cont : Continuous γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  -- Build continuity of norm of shifted path.
  have h_g_cont : Continuous (fun η : ℝ => ‖γf (t₀ + D.δ_right ε + η) - s‖) := by
    refine Continuous.norm ?_
    refine Continuous.sub ?_ continuous_const
    exact hγ_cont.comp (continuous_const.add continuous_id)
  have h_lim_ge : ε ≤ ‖γf (t₀ + D.δ_right ε) - s‖ := by
    have h_tendsto : Tendsto
        (fun η : ℝ => ‖γf (t₀ + D.δ_right ε + η) - s‖)
        (𝓝[>] 0) (𝓝 ‖γf (t₀ + D.δ_right ε) - s‖) := by
      have h1 := h_g_cont.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))
      simp only [add_zero] at h1
      exact h1
    refine ge_of_tendsto h_tendsto ?_
    have h_max_η : (0 : ℝ) < 1 - t₀ - D.δ_right ε := by linarith
    filter_upwards [Ioo_mem_nhdsGT h_max_η] with η hη
    have hη_pos : 0 < η := hη.1
    have hη_lt : η < 1 - t₀ - D.δ_right ε := hη.2
    have h_t_in : t₀ + D.δ_right ε + η ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [ht₀.1], by linarith⟩
    have h_t₀_le : t₀ ≤ t₀ + D.δ_right ε + η := by linarith
    have h_gap : D.δ_right ε < t₀ + D.δ_right ε + η - t₀ := by linarith
    exact le_of_lt (D.h_far_right ε hε_pos hε_lt
      (t₀ + D.δ_right ε + η) h_t_in h_t₀_le h_gap)
  exact le_antisymm h_le h_lim_ge

/-- **Left exit-time equality.** `‖γ(t₀ - δ_left ε) - s‖ = ε`. -/
theorem exit_time_eq_left
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (D : DerivedAsymmetricCutoffs γ s t₀)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold) :
    ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - D.δ_left ε) - s‖ = ε := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ)
  have hδL_pos := D.hδ_left_pos ε hε_pos hε_lt
  have hδL_small := D.hδ_left_small ε hε_pos hε_lt
  have h_le : ‖γf (t₀ - D.δ_left ε) - s‖ ≤ ε :=
    D.h_near_left ε hε_pos hε_lt (t₀ - D.δ_left ε) (by linarith) (by linarith)
  have hγ_cont : Continuous γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  have h_g_cont : Continuous (fun η : ℝ => ‖γf (t₀ - D.δ_left ε - η) - s‖) := by
    refine Continuous.norm ?_
    refine Continuous.sub ?_ continuous_const
    exact hγ_cont.comp (continuous_const.sub continuous_id)
  have h_lim_ge : ε ≤ ‖γf (t₀ - D.δ_left ε) - s‖ := by
    have h_tendsto : Tendsto
        (fun η : ℝ => ‖γf (t₀ - D.δ_left ε - η) - s‖)
        (𝓝[>] 0) (𝓝 ‖γf (t₀ - D.δ_left ε) - s‖) := by
      have h1 := h_g_cont.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))
      simp only [sub_zero] at h1
      exact h1
    refine ge_of_tendsto h_tendsto ?_
    have h_max_η : (0 : ℝ) < t₀ - D.δ_left ε := by linarith
    filter_upwards [Ioo_mem_nhdsGT h_max_η] with η hη
    have hη_pos : 0 < η := hη.1
    have hη_lt : η < t₀ - D.δ_left ε := hη.2
    have h_t_in : t₀ - D.δ_left ε - η ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith, by linarith [ht₀.2]⟩
    have h_t_le : t₀ - D.δ_left ε - η ≤ t₀ := by linarith
    have h_gap : D.δ_left ε < t₀ - (t₀ - D.δ_left ε - η) := by linarith
    exact le_of_lt (D.h_far_left ε hε_pos hε_lt
      (t₀ - D.δ_left ε - η) h_t_in h_t_le h_gap)
  exact le_antisymm h_le h_lim_ge

/-- **Left annular log-difference via FTC.** Symmetric to
`right_annular_log_diff`. Integral on `[t₀ - r, t₀ - δ_L]` equals
`log((γ(t₀ - δ_L) - s) / (γ(t₀ - r) - s))`. -/
theorem left_annular_log_diff
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    {L_left : ℂ} (_hL_left_ne : L_left ≠ 0)
    (_h_deriv_left : HasDerivWithinAt
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_left (Iio t₀) t₀)
    (_h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    {r δ_L : ℝ} (hδ_L_pos : 0 < δ_L) (hδ_L_lt : δ_L < r) (_hr_pos : 0 < r)
    (hr_le_t₀ : 0 ≤ t₀ - r)
    (h_slit_L : ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
        Complex.slitPlane)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (ht₀_lt_one : t₀ < 1) :
    ∫ t in (t₀ - r)..(t₀ - δ_L),
      deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s) =
    Complex.log
      ((γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - δ_L) - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - r) - s)) := by
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  set a : ℝ := t₀ - r
  set b : ℝ := t₀ - δ_L
  have hab : a ≤ b := by simp only [a, b]; linarith
  have ha_ge : t₀ - r ≤ a := le_refl _
  have hb_lt : b < t₀ := by simp only [b]; linarith
  -- Slit-plane on [a, b]: (γ t - s)/(γ a - s) ∈ slitPlane for t ∈ [a, b].
  have h_slit_ab : ∀ t ∈ Icc a b, (γf t - s) / (γf a - s) ∈ Complex.slitPlane := by
    intro t ht_in
    apply h_slit_L a t ha_ge ht_in.1 (lt_of_le_of_lt ht_in.2 hb_lt)
  -- γ a - s ≠ 0 since a < t₀ and h_unique says only t₀ maps to s.
  have ha_ne : γf a - s ≠ 0 := by
    intro h_eq
    have h_in_01 : a ∈ Icc (0 : ℝ) 1 :=
      ⟨hr_le_t₀, by linarith⟩
    have : a = t₀ := h_unique a h_in_01 (sub_eq_zero.mp h_eq)
    simp only [a] at this
    linarith
  -- Continuity of γf on [a, b].
  have hγ_cont : ContinuousOn γf (Icc a b) :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousOn
  -- Differentiability off partition.
  set P : Set ℝ := ↑γ.toPwC1Immersion.toPiecewiseC1Path.partition with hP_def
  have hP_count : P.Countable :=
    γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.countable
  have hγ_diff : ∀ t ∈ Ioo a b \ P, HasDerivAt γf (deriv γf t) t := by
    intro t ht
    have ht_in_Ioo : t ∈ Ioo (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · linarith [ht.1.1, hr_le_t₀]
      · linarith [ht.1.2, hb_lt]
    have h_diff_at : DifferentiableAt ℝ γf t :=
      γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off t ht_in_Ioo ht.2
    exact h_diff_at.hasDerivAt
  -- Integrability of γ'/(γ-s) on [a, b].
  have h_int : IntervalIntegrable
      (fun t => deriv γf t / (γf t - s)) MeasureTheory.volume a b := by
    have ht₀_in : t₀ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hr_le_t₀, hδ_L_pos, hδ_L_lt],
      ht₀_lt_one⟩
    -- δ_L < t₀: need this. r ≤ t₀, δ_L < r, so δ_L < t₀.
    have hδL_lt_t₀ : δ_L < t₀ := lt_of_lt_of_le hδ_L_lt (by linarith [hr_le_t₀])
    have h1 := inv_sub_mul_deriv_intervalIntegrable_left γ ht₀_in
      (δ_left_ε := δ_L) hδ_L_pos hδL_lt_t₀ h_unique
    refine h1.mono_set ?_ |>.congr (fun t _ => ?_)
    · simp only [a, b, Set.uIcc_of_le hab,
        Set.uIcc_of_le (by linarith [hδL_lt_t₀] : (0 : ℝ) ≤ t₀ - δ_L)]
      exact Set.Icc_subset_Icc hr_le_t₀ le_rfl
    · simp only [hγf_def]
      ring
  exact segment_log_FTC hab hP_count hγ_cont hγ_diff ha_ne h_slit_ab h_int

/-! ### Arg convergence of the annular quotient (T-BR-Y3g auxiliary)

For a fixed `r > 0` such that the chord `γ(t₀ + r) - s` lies in a generic
direction (specifically, `(γ(t₀+r)-s) / L_+ ∈ slitPlane`), the argument
`arg((γ(t₀+r)-s) / (γ(t₀ + δ_right ε) - s))` converges as `ε → 0⁺`. -/

/-- **Right annular quotient arg convergence.** -/
theorem arg_right_annular_tendsto
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {δ_right : ℝ → ℝ} {r : ℝ}
    (h_γr_div_L : (γ (t₀ + r) - s) / L ∈ Complex.slitPlane)
    (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_right ε)
    (hδ_to_zero : Tendsto δ_right (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ))) :
    Tendsto (fun ε : ℝ =>
      Complex.arg ((γ (t₀ + r) - s) / (γ (t₀ + δ_right ε) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((γ (t₀ + r) - s) / L).arg) := by
  -- exit_chord_tendsto_right: (γ(t₀+δR ε) - s)/(δR ε) → L.
  have h_chord := exit_chord_tendsto_right h_deriv h_at hδ_pos hδ_to_zero
  -- The reciprocal: (δR ε / (γ(t₀+δR ε)-s)) → 1/L.
  have hL_ne_C : L ≠ 0 := hL
  have h_recip : Tendsto (fun ε : ℝ => ((δ_right ε : ℝ) : ℂ) / (γ (t₀ + δ_right ε) - s))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / L)) := by
    -- 1/((γ-s)/δR) → 1/L.
    have h1 : Tendsto (fun ε : ℝ =>
        ((γ (t₀ + δ_right ε) - s) / ((δ_right ε : ℝ) : ℂ))⁻¹)
        (𝓝[>] (0 : ℝ)) (𝓝 L⁻¹) := h_chord.inv₀ hL_ne_C
    have h_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ((γ (t₀ + δ_right ε) - s) / ((δ_right ε : ℝ) : ℂ))⁻¹ =
          ((δ_right ε : ℝ) : ℂ) / (γ (t₀ + δ_right ε) - s) := by
      filter_upwards with ε
      rw [inv_div]
    rw [show ((1 : ℂ) / L) = L⁻¹ from one_div L]
    exact h1.congr' h_eq
  -- Quotient · δR ε = (γ(t₀+r)-s) · δR ε / (γ(t₀+δR ε)-s) → (γ(t₀+r)-s)/L.
  have h_quot_delta : Tendsto (fun ε : ℝ =>
      (γ (t₀ + r) - s) * (((δ_right ε : ℝ) : ℂ) / (γ (t₀ + δ_right ε) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((γ (t₀ + r) - s) * (1 / L))) :=
    tendsto_const_nhds.mul h_recip
  have h_simp : (γ (t₀ + r) - s) * (1 / L) = (γ (t₀ + r) - s) / L := by
    rw [mul_one_div]
  rw [h_simp] at h_quot_delta
  -- arg is continuous at (γ(t₀+r)-s)/L (in slit plane).
  have h_arg_cont : ContinuousAt Complex.arg ((γ (t₀ + r) - s) / L) :=
    Complex.continuousAt_arg h_γr_div_L
  -- Compose.
  have h_arg_lim : Tendsto (fun ε : ℝ =>
      Complex.arg ((γ (t₀ + r) - s) * (((δ_right ε : ℝ) : ℂ) / (γ (t₀ + δ_right ε) - s))))
      (𝓝[>] (0 : ℝ)) (𝓝 ((γ (t₀ + r) - s) / L).arg) :=
    h_arg_cont.tendsto.comp h_quot_delta
  -- Need to identify arg((γ(t₀+r)-s) · (δR ε)/(γ(t₀+δR ε)-s)) =
  --   arg((γ(t₀+r)-s)/(γ(t₀+δR ε)-s)).
  -- Use: multiplying by positive real preserves arg.
  refine h_arg_lim.congr' ?_
  filter_upwards [hδ_pos] with ε hε
  -- Manipulate: (γ(t₀+r)-s) · δR ε/(γ(t₀+δR ε)-s) = δR ε · ((γ(t₀+r)-s)/(γ(t₀+δR ε)-s))
  -- arg of (real_pos · z) = arg z.
  have h_rw : (γ (t₀ + r) - s) * (((δ_right ε : ℝ) : ℂ) / (γ (t₀ + δ_right ε) - s)) =
      ((δ_right ε : ℝ) : ℂ) * ((γ (t₀ + r) - s) / (γ (t₀ + δ_right ε) - s)) := by
    ring
  rw [h_rw]
  exact Complex.arg_real_mul _ hε

/-- **Left annular quotient arg convergence.** -/
theorem arg_left_annular_tendsto
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {δ_left : ℝ → ℝ} {r : ℝ}
    (h_γnegr_div_L : (-L) / (γ (t₀ - r) - s) ∈ Complex.slitPlane)
    (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_left ε)
    (hδ_to_zero : Tendsto δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ))) :
    Tendsto (fun ε : ℝ =>
      Complex.arg ((γ (t₀ - δ_left ε) - s) / (γ (t₀ - r) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L) / (γ (t₀ - r) - s)).arg) := by
  -- exit_chord_tendsto_left: (γ(t₀ - δL ε) - s)/(-(δL ε)) → L, so
  -- (γ(t₀-δL ε)-s) / δL ε → -L (via the negation argument inside).
  have h_chord_neg := exit_chord_tendsto_left h_deriv h_at hδ_pos hδ_to_zero
  -- Build h_quot' : (γ(t₀-δL ε)-s)/δL ε → -L.
  have h_neg_func : Tendsto (fun ε : ℝ => -((γ (t₀ - δ_left ε) - s) /
      ((-(δ_left ε) : ℝ) : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 (-L)) := h_chord_neg.neg
  have h_quot' : Tendsto (fun ε : ℝ =>
      (γ (t₀ - δ_left ε) - s) / ((δ_left ε : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (-L)) := by
    refine h_neg_func.congr' ?_
    filter_upwards [hδ_pos] with ε hε
    have h_cast : ((-(δ_left ε) : ℝ) : ℂ) = -((δ_left ε : ℝ) : ℂ) := by push_cast; ring
    rw [h_cast, div_neg, neg_neg]
  -- Quotient: (γ(t₀-δL ε)-s)/(γ(t₀-r)-s) · 1/δL ε → -L/(γ(t₀-r)-s).
  -- Equivalently: ((γ(t₀-δL ε)-s)/δL ε) / (γ(t₀-r)-s) → -L/(γ(t₀-r)-s).
  -- Then arg is invariant under positive real scaling (multiplying by 1/δL ε).
  have h_quot_div : Tendsto (fun ε : ℝ =>
      (γ (t₀ - δ_left ε) - s) / ((δ_left ε : ℝ) : ℂ) / (γ (t₀ - r) - s))
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L) / (γ (t₀ - r) - s))) :=
    h_quot'.div_const _
  have h_arg_cont : ContinuousAt Complex.arg ((-L) / (γ (t₀ - r) - s)) :=
    Complex.continuousAt_arg h_γnegr_div_L
  have h_arg_lim : Tendsto (fun ε : ℝ =>
      Complex.arg ((γ (t₀ - δ_left ε) - s) / ((δ_left ε : ℝ) : ℂ) / (γ (t₀ - r) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L) / (γ (t₀ - r) - s)).arg) :=
    h_arg_cont.tendsto.comp h_quot_div
  refine h_arg_lim.congr' ?_
  filter_upwards [hδ_pos] with ε hε
  -- Show arg((γ(t₀-δL ε)-s)/δL ε / (γ(t₀-r)-s)) = arg((γ(t₀-δL ε)-s)/(γ(t₀-r)-s))
  -- via arg invariance under positive real scaling.
  have hε_inv_pos : (0 : ℝ) < (δ_left ε)⁻¹ := inv_pos.mpr hε
  have h_rw : (γ (t₀ - δ_left ε) - s) / ((δ_left ε : ℝ) : ℂ) / (γ (t₀ - r) - s) =
      (((δ_left ε)⁻¹ : ℝ) : ℂ) * ((γ (t₀ - δ_left ε) - s) / (γ (t₀ - r) - s)) := by
    push_cast
    field_simp
  rw [h_rw]
  exact Complex.arg_real_mul _ hε_inv_pos

/-! ### Cutoff functions tend to `0⁺` (T-BR-Y3g auxiliary)

From the geometric scaffolding bundle, both cutoffs `D.δ_right` and `D.δ_left`
tend to `0⁺` as `ε → 0⁺`. The proof uses the contrapositive of `h_near_right`
(resp. `h_near_left`): for any `δ_0 > 0`, picking `m := ‖γ(t₀ + δ_0) - s‖ > 0`
(positive by uniqueness), for all `ε < min(m, threshold)`, we have
`‖γ(t₀ + δ_0) - s‖ > ε`, which by contrapositive of `h_near_right` gives
`δ_right ε < δ_0`. -/

/-- **Right cutoff tends to `0⁺` as `ε → 0⁺`.** -/
theorem DerivedAsymmetricCutoffs.δ_right_tendsto_zero
    {γ : ClosedPwC1Immersion x} {s : ℂ} {t₀ : ℝ}
    (ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (D : DerivedAsymmetricCutoffs γ s t₀) :
    Tendsto D.δ_right (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · -- δ_right ε → 0 in 𝓝 (absolute).
    rw [Metric.tendsto_nhds]
    intro δ₀ hδ₀_pos
    -- Choose δ₀' := min δ₀ ((1 - t₀)/2), so t₀ + δ₀' ∈ Ioo 0 1.
    set δ₀' : ℝ := min δ₀ ((1 - t₀) / 2) with hδ₀'_def
    have hδ₀'_pos : 0 < δ₀' := lt_min hδ₀_pos (by linarith [ht₀_Ioo.2])
    have hδ₀'_le : δ₀' ≤ δ₀ := min_le_left _ _
    have hδ₀'_le_half : δ₀' ≤ (1 - t₀) / 2 := min_le_right _ _
    have h_in_01 : t₀ + δ₀' ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [ht₀_Ioo.1], by linarith [ht₀_Ioo.2]⟩
    -- m := ‖γ(t₀ + δ₀') - s‖ > 0 by uniqueness.
    set m : ℝ := ‖γf (t₀ + δ₀') - s‖ with hm_def
    have hm_pos : 0 < m := by
      rw [hm_def]
      refine norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
      intro h_eq
      have ht_eq : t₀ + δ₀' = t₀ := h_unique _ h_in_01 h_eq
      linarith
    -- ε_star := min m D.threshold.
    set ε_star : ℝ := min m D.threshold with hε_star_def
    have hε_star_pos : 0 < ε_star := lt_min hm_pos D.hthresh
    have hε_star_le_m : ε_star ≤ m := min_le_left _ _
    have hε_star_le_thresh : ε_star ≤ D.threshold := min_le_right _ _
    -- Filter: Ioo 0 ε_star ∈ 𝓝[>] 0.
    have hmem : Ioo (0 : ℝ) ε_star ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hε_star_pos
    filter_upwards [hmem] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt_thresh : ε < D.threshold := lt_of_lt_of_le hε.2 hε_star_le_thresh
    have hε_lt_m : ε < m := lt_of_lt_of_le hε.2 hε_star_le_m
    have hδR_pos := D.hδ_right_pos ε hε_pos hε_lt_thresh
    -- Contrapositive of h_near_right at t = t₀ + δ₀':
    -- If t₀ + δ₀' - t₀ ≤ δ_right ε, then ‖γ(t₀ + δ₀') - s‖ ≤ ε. But ε < m, contradiction.
    by_contra h_ge
    push Not at h_ge
    -- h_ge : δ₀ ≤ dist (δ_right ε) 0 = δ_right ε (since δ_right ε > 0).
    rw [Real.dist_eq, sub_zero, abs_of_pos hδR_pos] at h_ge
    -- δ_right ε ≥ δ₀ ≥ δ₀'.
    have h_δ_ge_δ₀' : δ₀' ≤ D.δ_right ε := hδ₀'_le.trans h_ge
    -- Apply h_near_right.
    have h_t_in : t₀ + δ₀' - t₀ ≤ D.δ_right ε := by linarith
    have h_norm_le := D.h_near_right ε hε_pos hε_lt_thresh (t₀ + δ₀') (by linarith) h_t_in
    -- h_norm_le : ‖γ(t₀ + δ₀') - s‖ ≤ ε. But ε < m = ‖γ(t₀ + δ₀') - s‖. Contradiction.
    linarith
  · -- positivity: D.δ_right ε > 0 eventually.
    have hmem : Ioo (0 : ℝ) D.threshold ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT D.hthresh
    filter_upwards [hmem] with ε hε
    exact D.hδ_right_pos ε hε.1 hε.2

/-- **Left cutoff tends to `0⁺` as `ε → 0⁺`.** -/
theorem DerivedAsymmetricCutoffs.δ_left_tendsto_zero
    {γ : ClosedPwC1Immersion x} {s : ℂ} {t₀ : ℝ}
    (ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (D : DerivedAsymmetricCutoffs γ s t₀) :
    Tendsto D.δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro δ₀ hδ₀_pos
    set δ₀' : ℝ := min δ₀ (t₀ / 2) with hδ₀'_def
    have hδ₀'_pos : 0 < δ₀' := lt_min hδ₀_pos (by linarith [ht₀_Ioo.1])
    have hδ₀'_le : δ₀' ≤ δ₀ := min_le_left _ _
    have hδ₀'_le_half : δ₀' ≤ t₀ / 2 := min_le_right _ _
    have h_in_01 : t₀ - δ₀' ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [ht₀_Ioo.1], by linarith [ht₀_Ioo.2]⟩
    set m : ℝ := ‖γf (t₀ - δ₀') - s‖ with hm_def
    have hm_pos : 0 < m := by
      rw [hm_def]
      refine norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
      intro h_eq
      have ht_eq : t₀ - δ₀' = t₀ := h_unique _ h_in_01 h_eq
      linarith
    set ε_star : ℝ := min m D.threshold with hε_star_def
    have hε_star_pos : 0 < ε_star := lt_min hm_pos D.hthresh
    have hmem : Ioo (0 : ℝ) ε_star ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hε_star_pos
    filter_upwards [hmem] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt_thresh : ε < D.threshold := lt_of_lt_of_le hε.2 (min_le_right _ _)
    have hε_lt_m : ε < m := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hδL_pos := D.hδ_left_pos ε hε_pos hε_lt_thresh
    by_contra h_ge
    push Not at h_ge
    rw [Real.dist_eq, sub_zero, abs_of_pos hδL_pos] at h_ge
    have h_δ_ge_δ₀' : δ₀' ≤ D.δ_left ε := hδ₀'_le.trans h_ge
    have h_t_in : t₀ - (t₀ - δ₀') ≤ D.δ_left ε := by linarith
    have h_norm_le := D.h_near_left ε hε_pos hε_lt_thresh (t₀ - δ₀') (by linarith) h_t_in
    linarith
  · have hmem : Ioo (0 : ℝ) D.threshold ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT D.hthresh
    filter_upwards [hmem] with ε hε
    exact D.hδ_left_pos ε hε.1 hε.2

/-! ### Setup helpers for full CPV existence (T-BR-Y3g)

This section bundles the geometric setup (derivative limits, slit-plane
preconditions on the chord-vs-tangent quotient at a fixed radius `r > 0`) used
by the eventual full CPV existence theorem.

The full theorem assembly is intricate; this section captures the geometric
setup as a reusable internal helper. The remaining analytic content
(`Real.log ε` cancellation + arg convergence) is in the helper
`arg_right_annular_tendsto`, `arg_left_annular_tendsto`,
`DerivedAsymmetricCutoffs.δ_right_tendsto_zero`,
`DerivedAsymmetricCutoffs.δ_left_tendsto_zero` above. -/

/-- **Geometric setup for full CPV existence**: derives the slit-plane
preconditions `(γ(t₀+r)-s)/L_R ∈ slitPlane` and `-L_L/(γ(t₀-r)-s) ∈ slitPlane`
for sufficiently small `r > 0`, plus the supporting derivative-limit data.
This is the setup phase used by `hasCauchyPV_inv_sub_of_flat_one_full`. -/
private theorem cpvFullSetup
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∃ (L_R L_L : ℂ) (r : ℝ),
      L_R ≠ 0 ∧ L_L ≠ 0 ∧ 0 < r ∧ r ≤ t₀ ∧ r ≤ 1 - t₀ ∧
      HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_R
        (Ioi t₀) t₀ ∧
      HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_L
        (Iio t₀) t₀ ∧
      (∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
          (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
            Complex.slitPlane) ∧
      (∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
          (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
            Complex.slitPlane) ∧
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + r) - s) / L_R ∈
        Complex.slitPlane ∧
      (-L_L) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - r) - s) ∈
        Complex.slitPlane := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  -- Step 2: derivative limits.
  obtain ⟨L_R, hL_R_ne, hL_R_tendsto⟩ := exists_right_deriv_limit γ ht₀
  obtain ⟨L_L, hL_L_ne, hL_L_tendsto⟩ := exists_left_deriv_limit γ ht₀
  have hγf_cont : ContinuousAt γf t₀ :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousAt
  have hγf_cont_all : Continuous γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  have hγf_diff_right : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γf t :=
    eventually_differentiable_right γ ht₀
  have hγf_diff_left : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γf t :=
    eventually_differentiable_left γ ht₀
  obtain ⟨S_R, hS_R_mem, hS_R_diff⟩ := hγf_diff_right.exists_mem
  obtain ⟨S_L, hS_L_mem, hS_L_diff⟩ := hγf_diff_left.exists_mem
  have h_deriv_right : HasDerivWithinAt γf L_R (Ioi t₀) t₀ :=
    hasDerivWithinAt_Ioi_iff_Ici.mpr
      (hasDerivWithinAt_Ici_of_tendsto_deriv
        (fun t ht => (hS_R_diff t ht).differentiableWithinAt)
        hγf_cont.continuousWithinAt hS_R_mem hL_R_tendsto)
  have h_deriv_left : HasDerivWithinAt γf L_L (Iio t₀) t₀ :=
    hasDerivWithinAt_Iio_iff_Iic.mpr
      (hasDerivWithinAt_Iic_of_tendsto_deriv
        (fun t ht => (hS_L_diff t ht).differentiableWithinAt)
        hγf_cont.continuousWithinAt hS_L_mem hL_L_tendsto)
  -- Step 3: choose r small enough.
  -- exists_slitPlane_chord_quotient_right, exists_slitPlane_chord_quotient_left_forward,
  -- exists_normalized_chord_right, exists_normalized_chord_left.
  obtain ⟨r_R₁, hr_R₁_pos, hr_R₁_slit⟩ :=
    exists_slitPlane_chord_quotient_right h_deriv_right h_at hL_R_ne
  obtain ⟨r_L₁, hr_L₁_pos, hr_L₁_slit⟩ :=
    exists_slitPlane_chord_quotient_left_forward h_deriv_left h_at hL_L_ne
  obtain ⟨r_R₂, hr_R₂_pos, hr_R₂_close⟩ :=
    exists_normalized_chord_right h_deriv_right h_at hL_R_ne
      (ρ := 1 / 4) (by norm_num)
  obtain ⟨r_L₂, hr_L₂_pos, hr_L₂_close⟩ :=
    exists_normalized_chord_left h_deriv_left h_at hL_L_ne
      (ρ := 1 / 4) (by norm_num)
  set r : ℝ := min (min r_R₁ r_L₁) (min (min r_R₂ r_L₂) (min (t₀ / 2) ((1 - t₀) / 2))) with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    refine lt_min (lt_min hr_R₁_pos hr_L₁_pos)
      (lt_min (lt_min hr_R₂_pos hr_L₂_pos) (lt_min ?_ ?_))
    · linarith [ht₀.1]
    · linarith [ht₀.2]
  have hr_le_R₁ : r ≤ r_R₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hr_le_L₁ : r ≤ r_L₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hr_le_R₂ : r ≤ r_R₂ :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hr_le_L₂ : r ≤ r_L₂ :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hr_le_t₀_half : r ≤ t₀ / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hr_le_one_sub_half : r ≤ (1 - t₀) / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hr_le_t₀ : r ≤ t₀ := by linarith
  have hr_le_one_sub : r ≤ 1 - t₀ := by linarith
  have hr_lt_one_sub : r < 1 - t₀ := by linarith
  have hr_lt_t₀ : r < t₀ := by linarith
  -- Verify slit-plane preconditions for arg_*_annular_tendsto:
  -- (γ(t₀+r)-s)/L_R ∈ slitPlane.
  have h_γPlus_div_LR : (γf (t₀ + r) - s) / L_R ∈ Complex.slitPlane := by
    have h_close_orig : ‖(γf (t₀ + r) - s) / (L_R * (((t₀ + r) - t₀ : ℝ) : ℂ)) - 1‖ ≤ 1/4 := by
      apply hr_R₂_close (t₀ + r)
      refine ⟨by linarith, by linarith⟩
    have h_simp : (((t₀ + r) - t₀ : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
      push_cast; ring
    have h_close : ‖(γf (t₀ + r) - s) / (L_R * ((r : ℝ) : ℂ)) - 1‖ ≤ 1/4 := by
      rw [← h_simp]; exact h_close_orig
    -- (γ(t₀+r)-s)/(L_R · r) - 1 has norm ≤ 1/4, so Re ≥ 3/4 > 0.
    have h_re_chord_close : (3/4 : ℝ) ≤ ((γf (t₀ + r) - s) / (L_R * ((r : ℝ) : ℂ))).re := by
      have h_abs_le : |((γf (t₀ + r) - s) / (L_R * ((r : ℝ) : ℂ)) - 1).re| ≤ 1/4 :=
        le_trans (Complex.abs_re_le_norm _) h_close
      have h_re_eq : ((γf (t₀ + r) - s) / (L_R * ((r : ℝ) : ℂ)) - 1).re =
          ((γf (t₀ + r) - s) / (L_R * ((r : ℝ) : ℂ))).re - 1 := by simp
      rw [h_re_eq] at h_abs_le
      have h_abs : |((γf (t₀ + r) - s) / (L_R * ((r : ℝ) : ℂ))).re - 1| ≤ 1/4 := h_abs_le
      have := abs_le.mp h_abs
      linarith
    -- Re((γ(t₀+r)-s)/L_R) = Re((γ(t₀+r)-s)/(L_R·r)) · r since r is a positive real.
    have hr_C_ne : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr_pos)
    have hLR_C_ne : L_R * ((r : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL_R_ne hr_C_ne
    have h_div_eq : (γf (t₀ + r) - s) / L_R =
        ((r : ℝ) : ℂ) * ((γf (t₀ + r) - s) / (L_R * ((r : ℝ) : ℂ))) := by
      field_simp
    rw [h_div_eq]
    rw [Complex.mem_slitPlane_iff]
    left
    have h_re_calc : (((r : ℝ) : ℂ) * ((γf (t₀ + r) - s) / (L_R * ((r : ℝ) : ℂ)))).re =
        r * ((γf (t₀ + r) - s) / (L_R * ((r : ℝ) : ℂ))).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [h_re_calc]
    have : 0 < r * (3/4 : ℝ) := by positivity
    have : 0 < r * ((γf (t₀ + r) - s) / (L_R * ((r : ℝ) : ℂ))).re :=
      lt_of_lt_of_le this (mul_le_mul_of_nonneg_left h_re_chord_close hr_pos.le)
    exact this
  -- Similarly for left side: -L_L / (γ(t₀-r)-s) ∈ slitPlane.
  -- We have ‖(γ(t₀-r)-s)/(L_L·(t₀-r-t₀)) - 1‖ = ‖(γ(t₀-r)-s)/(L_L·(-r)) - 1‖ ≤ 1/4.
  have h_LL_neg_div_γMinus : (-L_L) / (γf (t₀ - r) - s) ∈ Complex.slitPlane := by
    have h_close_orig : ‖(γf (t₀ - r) - s) / (L_L * (((t₀ - r) - t₀ : ℝ) : ℂ)) - 1‖ ≤ 1/4 := by
      apply hr_L₂_close (t₀ - r)
      refine ⟨by linarith, by linarith⟩
    -- t₀ - r - t₀ = -r, real negative.
    have h_simp_in : (((t₀ - r) - t₀ : ℝ) : ℂ) = -((r : ℝ) : ℂ) := by push_cast; ring
    have h_close : ‖(γf (t₀ - r) - s) / (L_L * -((r : ℝ) : ℂ)) - 1‖ ≤ 1/4 := by
      rw [← h_simp_in]; exact h_close_orig
    -- ‖(γ(t₀-r)-s)/(L_L · (-r)) - 1‖ ≤ 1/4.
    -- We want: (-L_L)/(γ(t₀-r)-s) ∈ slitPlane.
    -- (γ(t₀-r)-s)/(L_L·(-r)) ≈ 1, so (-L_L)·r/(γ(t₀-r)-s) ≈ 1.
    -- Reciprocal: (γ(t₀-r)-s) / ((-L_L)·r) ≈ 1, hence Re ≥ 3/4.
    -- Then (-L_L)·r/(γ(t₀-r)-s) is the reciprocal.
    -- Alternative: just work with (γ(t₀-r)-s)/(L_L·(-r)) directly.
    -- (γ(t₀-r)-s)/(L_L·(-r)) = -(γ(t₀-r)-s)/(L_L·r).
    -- So -((γ(t₀-r)-s)/(L_L·r)) - 1 has norm ≤ 1/4.
    -- Hence (γ(t₀-r)-s)/(L_L·r) has Re close to -1, NOT close to 1!
    -- So actually we have: (γ(t₀-r)-s)/(L_L·r) ≈ -1.
    -- Reciprocal: (L_L·r)/(γ(t₀-r)-s) ≈ -1.
    -- So (-L_L·r)/(γ(t₀-r)-s) ≈ 1, hence Re ≥ 3/4.
    -- So (-L_L)/(γ(t₀-r)-s) has Re ≥ 3/4 · 1/r = 3/(4r) > 0. In slitPlane.
    have hr_C_ne : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr_pos)
    have h_γMinus_ne : γf (t₀ - r) - s ≠ 0 := by
      intro h_eq
      have h_in_01 : t₀ - r ∈ Icc (0 : ℝ) 1 :=
        ⟨by linarith, by linarith [ht₀.2]⟩
      have h_eq_t₀ := h_unique _ h_in_01 (sub_eq_zero.mp h_eq)
      linarith
    have hLL_C_ne : L_L * ((r : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL_L_ne hr_C_ne
    -- Express (-L_L·r)/(γ(t₀-r)-s) - 1 = 1/((γ(t₀-r)-s)/(-L_L·r)) - 1 = ...
    -- For now, just show Re((-L_L·r)/(γ(t₀-r)-s) - 1) ≤ 1/4? Too hard.
    -- Direct: (-L_L)/(γ(t₀-r)-s) is the reciprocal of -(γ(t₀-r)-s)/L_L. Its arg differs by π from
    -- arg((γ(t₀-r)-s)/L_L). Hmm getting complex.
    -- Easier path: compute (γ(t₀-r)-s)/(L_L·(-r)) ≈ 1 means (γ(t₀-r)-s) ≈ -L_L·r.
    -- So (γ(t₀-r)-s)/(-L_L·r) ≈ 1. So (-L_L·r)/(γ(t₀-r)-s) ≈ 1.
    -- Take Re: Re((-L_L·r)/(γ(t₀-r)-s)) ≥ 3/4 (via reciprocal close to 1 in norm).
    -- That's also complicated. Let me use the convergence directly:
    -- |(γ(t₀-r)-s)/(-L_L·r) - 1| ≤ 1/4 means
    --   the chord quotient is at distance ≤ 1/4 from 1.
    -- So in particular its modulus is in [3/4, 5/4], hence ≠ 0.
    -- Its reciprocal (-L_L·r)/(γ(t₀-r)-s) is therefore at modulus in [4/5, 4/3],
    --   and close to 1 (by 1/q identity).
    -- |1/q - 1| = |1 - q|/|q|. With |q-1| ≤ 1/4 and |q| ≥ 3/4: |1/q - 1| ≤ (1/4)/(3/4) = 1/3.
    -- So Re(1/q) ≥ 1 - 1/3 = 2/3 > 0. In slitPlane.
    set q : ℂ := (γf (t₀ - r) - s) / (L_L * ((r : ℝ) : ℂ))
      with hq_def
    have hq_close : ‖-q - 1‖ ≤ 1/4 := by
      have : (γf (t₀ - r) - s) / (L_L * -((r : ℝ) : ℂ)) = -q := by
        rw [hq_def, mul_neg, div_neg]
      rw [this] at h_close
      exact h_close
    -- Want: (-L_L)/(γf (t₀ - r) - s) ∈ slitPlane.
    -- (-L_L)/(γf (t₀ - r) - s) = (-L_L)/(γf (t₀ - r) - s). Let r' := -L_L · r/(γ(t₀-r)-s) = -(1/q)... actually:
    -- 1/q = L_L·r/(γ(t₀-r)-s). -1/q = -L_L·r/(γ(t₀-r)-s).
    -- And -L_L/(γ(t₀-r)-s) = (-1/q)/r ... wait:
    -- (-L_L)/(γ(t₀-r)-s) = (-L_L·r)/((γ(t₀-r)-s)·r) = (-L_L·r/(γ(t₀-r)-s)) / r = (-(1/q))/r? No.
    -- Hmm. (-L_L)/(γ(t₀-r)-s) = -L_L · (1/(γ(t₀-r)-s)).
    -- And -1/q = -L_L · r / (γ(t₀-r)-s).
    -- So (-L_L)/(γ(t₀-r)-s) = -1/q · 1/r = (-1/q)·(1/r) = (-1/q)·(1/r).
    -- Since 1/r > 0 real, (-L_L)/(γ(t₀-r)-s) has same arg as -1/q.
    -- Re((-L_L)/(γ(t₀-r)-s)) = (1/r) · Re(-1/q).
    -- We need Re(-1/q) > 0.
    -- -1/q is close to 1 (within 1/3 in norm).
    -- Let me check: hq_close : ‖-q - 1‖ ≤ 1/4, i.e. q is close to -1.
    -- 1/q is close to 1/(-1) = -1. -1/q is close to 1.
    -- Bound: ‖-1/q - 1‖ = ‖-(1+q)/q‖ = ‖1+q‖/‖q‖ ≤ (1/4)/(3/4) = 1/3 (since ‖q‖ ≥ 3/4).
    -- So Re(-1/q) ≥ 1 - 1/3 = 2/3 > 0.
    have hq_norm : 3/4 ≤ ‖q‖ := by
      -- ‖q‖ ≥ 1 - ‖q+1‖ via reverse triangle inequality: ‖-1‖ - ‖q‖ ≤ ‖-1 - q‖.
      have h1 : ‖q + 1‖ = ‖-q - 1‖ := by
        rw [show q + 1 = -(- q - 1) from by ring, norm_neg]
      have h2 : ‖q + 1‖ ≤ 1/4 := h1.trans_le hq_close
      have h3 : (1 : ℝ) - ‖q + 1‖ ≤ ‖q‖ := by
        have h_rev : ‖(-1 : ℂ)‖ - ‖q‖ ≤ ‖-1 - q‖ := norm_sub_norm_le _ _
        rw [norm_neg, norm_one] at h_rev
        have h_eq : (-1 : ℂ) - q = -(q + 1) := by ring
        rw [h_eq, norm_neg] at h_rev
        linarith
      linarith
    have hq_ne : q ≠ 0 := by
      intro h_eq
      rw [h_eq, norm_zero] at hq_norm
      linarith
    have h_neg_inv_q_close : ‖(-1 / q) - 1‖ ≤ 1/3 := by
      -- ‖-1/q - 1‖ = ‖(-1 - q)/q‖ = ‖-(1+q)‖/‖q‖ = ‖1+q‖/‖q‖.
      have h_eq : ((-1 : ℂ) / q) - 1 = -((1 + q) / q) := by
        field_simp
        ring
      rw [h_eq, norm_neg, norm_div]
      have h_one_plus_q : ‖(1 : ℂ) + q‖ = ‖-q - 1‖ := by
        have : (1 : ℂ) + q = -(-q - 1) := by ring
        rw [this, norm_neg]
      rw [h_one_plus_q]
      have hq_norm_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq_ne
      rw [div_le_iff₀ hq_norm_pos]
      calc ‖-q - 1‖ ≤ 1/4 := hq_close
        _ ≤ (1/3) * (3/4) := by norm_num
        _ ≤ (1/3) * ‖q‖ := mul_le_mul_of_nonneg_left hq_norm (by norm_num)
    -- (-L_L)/(γf (t₀ - r) - s) = (-1/q) · (1/r) (since q = (γ-s)/(L_L·r), -1/q = -L_L·r/(γ-s), divide by r).
    have h_eq_target : (-L_L) / (γf (t₀ - r) - s) =
        (((1/r) : ℝ) : ℂ) * (-1 / q) := by
      rw [hq_def]
      push_cast
      field_simp
    rw [h_eq_target]
    rw [Complex.mem_slitPlane_iff]
    left
    have h_re_calc : ((((1/r) : ℝ) : ℂ) * (-1 / q)).re = (1/r) * (-1 / q).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [h_re_calc]
    -- Show Re(-1/q) ≥ 2/3 > 0.
    have h_abs_re_le : |(-1 / q - 1).re| ≤ 1/3 :=
      le_trans (Complex.abs_re_le_norm _) h_neg_inv_q_close
    have h_re_eq : (-1 / q - 1).re = (-1 / q).re - 1 := by simp
    rw [h_re_eq] at h_abs_re_le
    have h_lb_re := (abs_le.mp h_abs_re_le).1
    have h_re_ge : (2/3 : ℝ) ≤ (-1 / q).re := by linarith
    have h_inv_r_pos : 0 < 1/r := by positivity
    have : 0 < (1/r) * (2/3 : ℝ) := by positivity
    linarith [mul_le_mul_of_nonneg_left h_re_ge h_inv_r_pos.le]
  -- Final assembly: return the tuple.
  refine ⟨L_R, L_L, r, hL_R_ne, hL_L_ne, hr_pos, hr_le_t₀, hr_le_one_sub,
    h_deriv_right, h_deriv_left, ?_, ?_, h_γPlus_div_LR, h_LL_neg_div_γMinus⟩
  · intro a b ha_gt hab hb_le
    exact hr_R₁_slit a b ha_gt hab (le_trans hb_le (by linarith [hr_le_R₁]))
  · intro a b ha_ge hab hb_lt
    exact hr_L₁_slit a b (le_trans (by linarith [hr_le_L₁]) ha_ge) hab hb_lt

/-! ### Full CPV existence at a transverse crossing (T-BR-Y3g main theorem) -/

/-- **Full CPV existence at a transverse crossing.** For a closed piecewise-`C¹`
immersion `γ` crossing the pole `s` uniquely at `t₀ ∈ Ioo 0 1`, off-partition,
and `IsFlatOfOrder _ _ 1` (automatic for `C¹` curves), there exists `L : ℂ`
such that `HasCauchyPV (fun z => (z - s)⁻¹) γ.toPiecewiseC1Path s L`.

This is the eventual elimination of the `h_geometry_cpv` oracle in
`residueTheorem_crossing_asymmetric_cpv`. -/
theorem hasCauchyPV_inv_sub_of_flat_one_full
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (_h_flat : IsFlatOfOrder
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ 1) :
    ∃ L : ℂ, HasCauchyPV (fun z => (z - s)⁻¹)
      γ.toPwC1Immersion.toPiecewiseC1Path s L := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  -- Setup phase.
  obtain ⟨L_R, L_L, r, hL_R_ne, hL_L_ne, hr_pos, hr_le_t₀, hr_le_one_sub,
    h_deriv_right, h_deriv_left, h_slit_R, h_slit_L, h_γPlus_div_LR,
    h_LL_neg_div_γMinus⟩ := cpvFullSetup γ ht₀ h_at h_unique
  set D : DerivedAsymmetricCutoffs γ s t₀ :=
    deriveAsymmetricCutoffs_anywhere γ ht₀ h_at h_unique with hD_def
  have hδR_tendsto : Tendsto D.δ_right (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    DerivedAsymmetricCutoffs.δ_right_tendsto_zero ht₀ h_unique D
  have hδL_tendsto : Tendsto D.δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    DerivedAsymmetricCutoffs.δ_left_tendsto_zero ht₀ h_unique D
  -- Eventually δ_R(ε) < r and δ_L(ε) < r.
  have hδR_lt_r : ∀ᶠ ε in 𝓝[>] (0 : ℝ), D.δ_right ε < r := by
    have h_abs := (hδR_tendsto.mono_right nhdsWithin_le_nhds).eventually
      (Metric.ball_mem_nhds (0 : ℝ) hr_pos)
    filter_upwards [h_abs] with ε hε
    rw [Real.dist_eq, sub_zero] at hε
    have h_le_abs : D.δ_right ε ≤ |D.δ_right ε| := le_abs_self _
    linarith
  have hδL_lt_r : ∀ᶠ ε in 𝓝[>] (0 : ℝ), D.δ_left ε < r := by
    have h_abs := (hδL_tendsto.mono_right nhdsWithin_le_nhds).eventually
      (Metric.ball_mem_nhds (0 : ℝ) hr_pos)
    filter_upwards [h_abs] with ε hε
    rw [Real.dist_eq, sub_zero] at hε
    have h_le_abs : D.δ_left ε ≤ |D.δ_left ε| := le_abs_self _
    linarith
  -- The "fixed integrals" C₁ + C₂.
  set C₁ : ℂ := ∫ t in (0 : ℝ)..(t₀ - r),
    (γf t - s)⁻¹ * deriv γf t with hC₁_def
  set C₂ : ℂ := ∫ t in (t₀ + r)..1,
    (γf t - s)⁻¹ * deriv γf t with hC₂_def
  -- Annular log-diff functions.
  set Λ_R : ℝ → ℂ := fun ε =>
    Complex.log ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)) with hΛR_def
  set Λ_L : ℝ → ℂ := fun ε =>
    Complex.log ((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)) with hΛL_def
  -- Step A: Λ_R, Λ_L have a definite imaginary-part limit.
  -- Re Λ_R(ε) = Real.log(‖γ(t₀+r)-s‖/ε), Re Λ_L(ε) = Real.log(ε/‖γ(t₀-r)-s‖).
  -- Sum: Real.log(‖γ(t₀+r)-s‖) - Real.log(‖γ(t₀-r)-s‖) (Real.log ε cancels).
  -- Im Λ_R(ε) → arg((γ(t₀+r)-s)/L_R), Im Λ_L(ε) → arg(-L_L/(γ(t₀-r)-s)).
  -- Provide explicit positivity (eventually):
  have hδR_pos_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < D.δ_right ε := by
    have hmem : Ioo (0 : ℝ) D.threshold ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT D.hthresh
    filter_upwards [hmem] with ε hε
    exact D.hδ_right_pos ε hε.1 hε.2
  have hδL_pos_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < D.δ_left ε := by
    have hmem : Ioo (0 : ℝ) D.threshold ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT D.hthresh
    filter_upwards [hmem] with ε hε
    exact D.hδ_left_pos ε hε.1 hε.2
  have h_arg_R_clean : Tendsto (fun ε : ℝ =>
      Complex.arg ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((γf (t₀ + r) - s) / L_R).arg) :=
    arg_right_annular_tendsto h_deriv_right h_at hL_R_ne h_γPlus_div_LR
      hδR_pos_ev hδR_tendsto
  have h_arg_L_clean : Tendsto (fun ε : ℝ =>
      Complex.arg ((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L_L) / (γf (t₀ - r) - s)).arg) :=
    arg_left_annular_tendsto h_deriv_left h_at hL_L_ne h_LL_neg_div_γMinus
      hδL_pos_ev hδL_tendsto
  -- Step B: Re of each Λ. Im of Λ via continuity of arg-to-ofReal.
  -- We'll show Λ_R + Λ_L converges to a definite limit.
  -- Notation: argR_lim := ((γf (t₀ + r) - s) / L_R).arg
  -- argL_lim := ((-L_L) / (γf (t₀ - r) - s)).arg
  set argR_lim : ℝ := ((γf (t₀ + r) - s) / L_R).arg with hargR_def
  set argL_lim : ℝ := ((-L_L) / (γf (t₀ - r) - s)).arg with hargL_def
  -- The constant real part of Λ_R + Λ_L:
  set logNorm_diff : ℝ :=
    Real.log ‖γf (t₀ + r) - s‖ - Real.log ‖γf (t₀ - r) - s‖ with hlogND_def
  -- Define L := C₁ + C₂ + logNorm_diff + (argR_lim + argL_lim)·I.
  set L : ℂ := C₁ + C₂ + ((logNorm_diff : ℝ) : ℂ) +
    (((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I) with hL_def
  refine ⟨L, ?_⟩
  -- HasCauchyPV unfolds to Tendsto cutoff_integral (𝓝[>] 0) (𝓝 L).
  unfold HasCauchyPV
  -- Show: Tendsto (fun ε => ∫_0^1 cpvIntegrand ... ε) → L.
  -- Use cutoff_integral_eq_outer_sum to identify with E_outer(ε).
  -- Then E_outer(ε) = C₁ + Λ_L(ε) + Λ_R(ε) + C₂.
  -- Then Λ_L(ε) + Λ_R(ε) → logNorm_diff + (argR_lim + argL_lim)·I.
  have h_eventually_eq :
      (fun ε => ∫ t in (0 : ℝ)..1,
          cpvIntegrand (fun z => (z - s)⁻¹) γf s ε t) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε => C₁ + Λ_L ε + Λ_R ε + C₂) := by
    filter_upwards [Ioo_mem_nhdsGT D.hthresh, hδR_lt_r, hδL_lt_r,
        hδR_pos_ev, hδL_pos_ev] with ε hε_thresh hδR_r hδL_r hδR_pos hδL_pos
    have hε_pos : 0 < ε := hε_thresh.1
    have hε_lt_thresh : ε < D.threshold := hε_thresh.2
    -- Express outer sum via cutoff_integral_eq_outer_sum.
    rw [cutoff_integral_eq_outer_sum γ ht₀ D h_unique hε_pos hε_lt_thresh]
    -- Now we have ∫₀^{t₀-δL} + ∫_{t₀+δR}^1. Need to split each at r.
    -- ∫₀^{t₀-δL} = ∫₀^{t₀-r} + ∫_{t₀-r}^{t₀-δL} = C₁ + Λ_L(ε)
    -- ∫_{t₀+δR}^1 = ∫_{t₀+δR}^{t₀+r} + ∫_{t₀+r}^1 = Λ_R(ε) + C₂
    have hδR_pos' := D.hδ_right_pos ε hε_pos hε_lt_thresh
    have hδL_pos' := D.hδ_left_pos ε hε_pos hε_lt_thresh
    -- Establish integrability for splitting.
    have h_int_left : IntervalIntegrable
        (fun t => (γf t - s)⁻¹ * deriv γf t) MeasureTheory.volume 0 (t₀ - D.δ_left ε) :=
      inv_sub_mul_deriv_intervalIntegrable_left γ ht₀ hδL_pos'
        (D.hδ_left_small ε hε_pos hε_lt_thresh) h_unique
    have h_int_right : IntervalIntegrable
        (fun t => (γf t - s)⁻¹ * deriv γf t) MeasureTheory.volume (t₀ + D.δ_right ε) 1 :=
      inv_sub_mul_deriv_intervalIntegrable_right γ ht₀ hδR_pos'
        (D.hδ_right_small ε hε_pos hε_lt_thresh) h_unique
    -- Subdivide.
    have h_left_split :
        ∫ t in (0 : ℝ)..(t₀ - D.δ_left ε), (γf t - s)⁻¹ * deriv γf t =
          C₁ + Λ_L ε := by
      have hr_le : (0 : ℝ) ≤ t₀ - r := by linarith
      have h_int_C₁ : IntervalIntegrable (fun t => (γf t - s)⁻¹ * deriv γf t)
          MeasureTheory.volume 0 (t₀ - r) :=
        h_int_left.mono_set (by
          rw [Set.uIcc_of_le hr_le, Set.uIcc_of_le (by linarith)]
          exact Set.Icc_subset_Icc le_rfl (by linarith))
      have h_int_ann : IntervalIntegrable (fun t => (γf t - s)⁻¹ * deriv γf t)
          MeasureTheory.volume (t₀ - r) (t₀ - D.δ_left ε) :=
        h_int_left.mono_set (by
          rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
          exact Set.Icc_subset_Icc hr_le le_rfl)
      rw [← intervalIntegral.integral_add_adjacent_intervals h_int_C₁ h_int_ann]
      congr 1
      -- The second integral equals Λ_L(ε) via left_annular_log_diff.
      have h_LL := left_annular_log_diff γ hL_L_ne h_deriv_left h_at
        hδL_pos' hδL_r hr_pos hr_le h_slit_L h_unique ht₀.2
      -- left_annular_log_diff gives ∫ deriv γ/(γ - s), but we have (γ-s)⁻¹ · γ'.
      have h_congr : ∫ t in (t₀ - r)..(t₀ - D.δ_left ε),
          (γf t - s)⁻¹ * deriv γf t =
          ∫ t in (t₀ - r)..(t₀ - D.δ_left ε),
          deriv γf t / (γf t - s) := by
        apply intervalIntegral.integral_congr
        intro t _
        show (γf t - s)⁻¹ * deriv γf t = deriv γf t / (γf t - s)
        rw [div_eq_mul_inv, mul_comm]
      rw [h_congr, h_LL]
    have h_right_split :
        ∫ t in (t₀ + D.δ_right ε)..(1 : ℝ), (γf t - s)⁻¹ * deriv γf t =
          Λ_R ε + C₂ := by
      have hr_le : t₀ + r ≤ 1 := by linarith
      have h_int_C₂ : IntervalIntegrable (fun t => (γf t - s)⁻¹ * deriv γf t)
          MeasureTheory.volume (t₀ + r) 1 :=
        h_int_right.mono_set (by
          rw [Set.uIcc_of_le hr_le, Set.uIcc_of_le (by linarith)]
          exact Set.Icc_subset_Icc (by linarith) le_rfl)
      have h_int_ann : IntervalIntegrable (fun t => (γf t - s)⁻¹ * deriv γf t)
          MeasureTheory.volume (t₀ + D.δ_right ε) (t₀ + r) :=
        h_int_right.mono_set (by
          rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
          exact Set.Icc_subset_Icc le_rfl hr_le)
      rw [← intervalIntegral.integral_add_adjacent_intervals h_int_ann h_int_C₂]
      congr 1
      have h_RR := right_annular_log_diff γ hL_R_ne h_deriv_right h_at
        hδR_pos' hδR_r hr_pos hr_le h_slit_R h_unique ht₀.1
      have h_congr : ∫ t in (t₀ + D.δ_right ε)..(t₀ + r),
          (γf t - s)⁻¹ * deriv γf t =
          ∫ t in (t₀ + D.δ_right ε)..(t₀ + r),
          deriv γf t / (γf t - s) := by
        apply intervalIntegral.integral_congr
        intro t _
        show (γf t - s)⁻¹ * deriv γf t = deriv γf t / (γf t - s)
        rw [div_eq_mul_inv, mul_comm]
      rw [h_congr, h_RR]
    rw [h_left_split, h_right_split]
    ring
  refine Tendsto.congr' h_eventually_eq.symm ?_
  -- Now show: (fun ε => C₁ + Λ_L ε + Λ_R ε + C₂) → L.
  -- L = C₁ + C₂ + logNorm_diff + (argR_lim + argL_lim)·I.
  -- So Λ_L ε + Λ_R ε → logNorm_diff + (argR_lim + argL_lim)·I.
  have h_sum_tendsto : Tendsto (fun ε : ℝ => Λ_L ε + Λ_R ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (((logNorm_diff : ℝ) : ℂ) +
        ((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I)) := by
    -- Decompose into Re + Im parts.
    -- Λ_R(ε) = log z = Real.log ‖z‖ + arg z · I  (where z = (γ(t₀+r)-s)/(γ(t₀+δR ε)-s))
    -- For ε > 0 small: ‖z‖ = ‖γ(t₀+r)-s‖/ε (by exit_time_eq_right), arg z = arg_R(ε)
    -- Re Λ_R(ε) = Real.log ‖γ(t₀+r)-s‖ - Real.log ε.
    -- Similarly Re Λ_L(ε) = Real.log ε - Real.log ‖γ(t₀-r)-s‖. Sum: logNorm_diff.
    -- Im Λ_R(ε) + Im Λ_L(ε) → argR_lim + argL_lim.
    have h_decomp : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        Λ_L ε + Λ_R ε = ((logNorm_diff : ℝ) : ℂ) +
          ((((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg +
            ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg : ℝ) : ℂ) * Complex.I := by
      filter_upwards [Ioo_mem_nhdsGT D.hthresh, hδR_lt_r, hδL_lt_r,
          hδR_pos_ev, hδL_pos_ev] with ε hε_thresh hδR_r hδL_r hδR_pos hδL_pos
      have hε_pos : 0 < ε := hε_thresh.1
      have hε_lt_thresh : ε < D.threshold := hε_thresh.2
      -- Exit-time equalities.
      have h_eq_R := exit_time_eq_right γ D ht₀ hε_pos hε_lt_thresh
      have h_eq_L := exit_time_eq_left γ D ht₀ hε_pos hε_lt_thresh
      -- Compute Re Λ_R, Re Λ_L.
      have h_γPlus_ne : γf (t₀ + r) - s ≠ 0 := by
        intro h_eq
        have : t₀ + r ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht₀.1], by linarith⟩
        have ht_eq := h_unique _ this (sub_eq_zero.mp h_eq)
        linarith
      have h_γMinus_ne : γf (t₀ - r) - s ≠ 0 := by
        intro h_eq
        have : t₀ - r ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht₀.2]⟩
        have ht_eq := h_unique _ this (sub_eq_zero.mp h_eq)
        linarith
      have h_γR_ne : γf (t₀ + D.δ_right ε) - s ≠ 0 := by
        rw [← norm_pos_iff, h_eq_R]; exact hε_pos
      have h_γL_ne : γf (t₀ - D.δ_left ε) - s ≠ 0 := by
        rw [← norm_pos_iff, h_eq_L]; exact hε_pos
      -- Decompose log via Real.log ‖·‖ + arg(·) · I.
      have h_log_R_decomp : Λ_R ε =
          ((Real.log ‖γf (t₀ + r) - s‖ - Real.log ‖γf (t₀ + D.δ_right ε) - s‖ : ℝ) : ℂ) +
          (((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg : ℂ) * Complex.I := by
        rw [hΛR_def]
        apply Complex.ext
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.I_im, mul_zero, mul_one, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
          rw [Complex.log_re, norm_div]
          rw [Real.log_div (norm_ne_zero_iff.mpr h_γPlus_ne) (norm_ne_zero_iff.mpr h_γR_ne)]
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, zero_mul, mul_one, Complex.ofReal_re, zero_add]
          rw [Complex.log_im]
          ring
      have h_log_L_decomp : Λ_L ε =
          ((Real.log ‖γf (t₀ - D.δ_left ε) - s‖ - Real.log ‖γf (t₀ - r) - s‖ : ℝ) : ℂ) +
          (((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg : ℂ) * Complex.I := by
        rw [hΛL_def]
        apply Complex.ext
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.I_im, mul_zero, mul_one, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
          rw [Complex.log_re, norm_div]
          rw [Real.log_div (norm_ne_zero_iff.mpr h_γL_ne) (norm_ne_zero_iff.mpr h_γMinus_ne)]
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, zero_mul, mul_one, Complex.ofReal_re, zero_add]
          rw [Complex.log_im]
          ring
      rw [h_log_L_decomp, h_log_R_decomp, h_eq_R, h_eq_L]
      simp only [hlogND_def]
      push_cast
      ring
    -- Now the function Λ_L + Λ_R equals (fixed real const) + (arg_L + arg_R) * I eventually.
    -- arg_R and arg_L converge to argR_lim and argL_lim respectively.
    have h_decomp' : (fun ε : ℝ => ((logNorm_diff : ℝ) : ℂ) +
        ((((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg +
          ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg : ℝ) : ℂ) *
            Complex.I) =ᶠ[𝓝[>] (0 : ℝ)] (fun ε => Λ_L ε + Λ_R ε) := by
      filter_upwards [h_decomp] with ε hε
      exact hε.symm
    refine Tendsto.congr' h_decomp' ?_
    -- Show (fun ε => logNorm_diff + (arg_L + arg_R) · I) → logNorm_diff + (argR_lim + argL_lim) · I.
    refine tendsto_const_nhds.add ?_
    -- (arg_L + arg_R) → argL_lim + argR_lim as functions, then cast and multiply by I.
    have h_arg_sum : Tendsto (fun ε : ℝ =>
        ((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg +
          ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg)
        (𝓝[>] (0 : ℝ)) (𝓝 (argL_lim + argR_lim)) := by
      simpa [hargL_def, hargR_def, add_comm] using h_arg_L_clean.add h_arg_R_clean
    have h_cast : Tendsto (fun ε : ℝ =>
        ((((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg +
            ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 ((argL_lim + argR_lim : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp h_arg_sum
    have h_mul_I : Tendsto (fun ε : ℝ =>
        ((((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg +
            ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg : ℝ) : ℂ) * Complex.I)
        (𝓝[>] (0 : ℝ)) (𝓝 (((argL_lim + argR_lim : ℝ) : ℂ) * Complex.I)) :=
      h_cast.mul tendsto_const_nhds
    have h_target_eq : ((argL_lim + argR_lim : ℝ) : ℂ) * Complex.I =
        ((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [← h_target_eq]
    exact h_mul_I
  -- Now combine: cutoff integral → C₁ + C₂ + (logNorm_diff + (argR_lim + argL_lim)·I) = L.
  -- Compose: (Λ_L + Λ_R) tends to logNorm_diff + arg·I, plus constants C₁, C₂.
  have h_full : Tendsto (fun ε : ℝ => C₁ + (Λ_L ε + Λ_R ε) + C₂)
      (𝓝[>] (0 : ℝ)) (𝓝 (C₁ + (((logNorm_diff : ℝ) : ℂ) +
        ((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I) + C₂)) :=
    (tendsto_const_nhds.add h_sum_tendsto).add tendsto_const_nhds
  have h_target_eq : C₁ + (((logNorm_diff : ℝ) : ℂ) +
      ((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I) + C₂ = L := by
    rw [hL_def]; ring
  rw [← h_target_eq]
  refine h_full.congr' ?_
  filter_upwards with ε
  ring

/-- **Corner-friendly alias** for `hasCauchyPV_inv_sub_of_flat_one_full`
(T-BR-Y10b). Since `hasCauchyPV_inv_sub_of_flat_one_full` no longer requires
`h_part_off` (the only internal use was the now-unused parameter to
`deriveAsymmetricCutoffs`, which is replaced by
`deriveAsymmetricCutoffs_anywhere`), this is a definitional alias retained
for clarity at callers wanting the explicit "anywhere" naming. -/
theorem hasCauchyPV_inv_sub_of_flat_one_full_anywhere
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (h_flat : IsFlatOfOrder
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ 1) :
    ∃ L : ℂ, HasCauchyPV (fun z => (z - s)⁻¹)
      γ.toPwC1Immersion.toPiecewiseC1Path s L :=
  hasCauchyPV_inv_sub_of_flat_one_full γ ht₀ h_at h_unique h_flat

end HungerbuhlerWasem

end
