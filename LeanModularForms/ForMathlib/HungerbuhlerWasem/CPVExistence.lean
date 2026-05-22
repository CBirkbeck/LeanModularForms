/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CrossingDataBuilder
import LeanModularForms.ForMathlib.WindingInteger

/-!
# Cauchy principal-value existence at a transverse crossing

For a closed piecewise-`C¹` immersion `γ : ℝ → ℂ` crossing a pole `s` uniquely at
`t₀ ∈ Ioo 0 1` with non-vanishing one-sided derivatives, the Cauchy principal
value `lim_{ε → 0⁺} ∫_{|γ-s| ≥ ε} (γ - s)⁻¹ · γ'` exists. This file develops the
analytic machinery — chord-to-tangent limits, slit-plane chord-quotient
estimates, FTC on annular pieces, and exit-time cancellations — culminating in
the full CPV existence theorem.

## Main results

* `chord_div_t_tendsto_right` / `chord_div_t_tendsto_left`: chord-to-tangent
  limits `(γ(t) - s) / (t - t₀) → L_±` as `t → t₀^±`.
* `exit_chord_tendsto_right` / `exit_chord_tendsto_left`: exit-time variants
  evaluated along a positive cutoff `δ(ε) → 0⁺`.
* `exit_arg_tendsto_right` / `exit_arg_tendsto_left`: convergence of
  `arg(γ(t₀ ± δ(ε)) - s)` under a slit-plane hypothesis on `L_±`.
* `exit_log_tendsto_right` / `exit_log_tendsto_left`: convergence of
  `Complex.log(γ(t₀ ± δ(ε)) - s) - Real.log ε` to `(arg L_±) · I`.
* `exit_log_diff_tendsto`: the divergent `Real.log ε` parts cancel between the
  two sides, leaving a finite log-difference limit.
* `exists_slitPlane_chord_quotient_right` / `_left_forward` / `_left`:
  slit-plane chord-quotient estimates on small one-sided intervals.
* `right_annular_log_diff` / `left_annular_log_diff`: FTC on shrinking annular
  pieces expresses the integral as a log difference.
* `hasCauchyPV_inv_sub_of_flat_one_full`: the headline CPV existence theorem.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

/-- Decomposition of `Complex.log` as real-log-of-norm plus `arg · I`. -/
private lemma complex_log_eq (z : ℂ) :
    Complex.log z = ((Real.log ‖z‖ : ℝ) : ℂ) + (z.arg : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im]

/-- Rewriting `(γ - s)⁻¹ * deriv γ` as `deriv γ / (γ - s)` inside an integral. -/
private lemma integral_inv_sub_mul_eq_div {γ : ℝ → ℂ} {s : ℂ} (a b : ℝ) :
    ∫ t in a..b, (γ t - s)⁻¹ * deriv γ t = ∫ t in a..b, deriv γ t / (γ t - s) :=
  intervalIntegral.integral_congr fun _ _ => by rw [div_eq_mul_inv, mul_comm]

/-- **Right-side chord-to-tangent quotient limit.** Given `γ : ℝ → ℂ` with
`HasDerivWithinAt γ L (Ioi t₀) t₀` and `γ(t₀) = s`, the chord quotient
`(γ(t) - s) / (t - t₀)` tends to `L` as `t → t₀⁺`. -/
theorem chord_div_t_tendsto_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) :
    Tendsto (fun t : ℝ => (γ t - s) / ((t - t₀ : ℝ) : ℂ)) (𝓝[>] t₀) (𝓝 L) := by
  have hr := hasDerivWithinAt_iff_isLittleO.mp h_deriv
  have h_rem_tendsto :
      Tendsto (fun t : ℝ => (γ t - γ t₀ - (t - t₀) • L) / ((t - t₀ : ℝ) : ℂ))
        (𝓝[>] t₀) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ_pos
    filter_upwards [hr.def (by linarith : (0 : ℝ) < δ / 2), self_mem_nhdsWithin] with t hb ht
    have h_pos : 0 < t - t₀ := sub_pos.mpr ht
    have h_norm_eq : ‖(t - t₀ : ℝ)‖ = t - t₀ := by
      rw [Real.norm_eq_abs, abs_of_pos h_pos]
    rw [dist_zero_right, norm_div, Complex.norm_real, h_norm_eq, div_lt_iff₀ h_pos]
    rw [h_norm_eq] at hb
    have h_le : ‖γ t - γ t₀ - ((t - t₀) : ℝ) • L‖ ≤ δ / 2 * (t - t₀) := hb
    have h_lt : δ / 2 * (t - t₀) < δ * (t - t₀) := by nlinarith
    linarith
  have h_rewrite : ∀ᶠ t in 𝓝[>] t₀,
      (γ t - s) / ((t - t₀ : ℝ) : ℂ) =
        L + (γ t - γ t₀ - (t - t₀) • L) / ((t - t₀ : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h_ne_complex : ((t - t₀ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt ht))
    rw [h_at, Complex.real_smul]; field_simp; ring
  refine (?_ : Tendsto _ _ _).congr' (h_rewrite.mono (fun _ h => h.symm))
  simpa using tendsto_const_nhds.add h_rem_tendsto

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
    filter_upwards [hr.def (by linarith : (0 : ℝ) < δ / 2), self_mem_nhdsWithin] with t hb ht
    have h_pos : 0 < t₀ - t := sub_pos.mpr ht
    have h_norm_eq : ‖(t - t₀ : ℝ)‖ = t₀ - t := by
      rw [Real.norm_eq_abs, abs_of_neg (sub_neg_of_lt ht)]; ring
    rw [dist_zero_right, norm_div, Complex.norm_real, h_norm_eq, div_lt_iff₀ h_pos]
    rw [h_norm_eq] at hb
    have h_le : ‖γ t - γ t₀ - ((t - t₀) : ℝ) • L‖ ≤ δ / 2 * (t₀ - t) := hb
    have h_lt : δ / 2 * (t₀ - t) < δ * (t₀ - t) := by nlinarith
    linarith
  have h_rewrite : ∀ᶠ t in 𝓝[<] t₀,
      (γ t - s) / ((t - t₀ : ℝ) : ℂ) =
        L + (γ t - γ t₀ - (t - t₀) • L) / ((t - t₀ : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h_ne_complex : ((t - t₀ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_lt ht))
    rw [h_at, Complex.real_smul]; field_simp; ring
  refine (?_ : Tendsto _ _ _).congr' (h_rewrite.mono (fun _ h => h.symm))
  simpa using tendsto_const_nhds.add h_rem_tendsto

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
  have h_compose : Tendsto (fun ε : ℝ => t₀ + δ_right ε)
      (𝓝[>] (0 : ℝ)) (𝓝[>] t₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using tendsto_const_nhds.add
        (hδ_to_zero.mono_right nhdsWithin_le_nhds : Tendsto δ_right (𝓝[>] (0 : ℝ)) (𝓝 0))
    · filter_upwards [hδ_pos] with ε hε using show t₀ < t₀ + δ_right ε by linarith
  refine ((chord_div_t_tendsto_right h_deriv h_at).comp h_compose).congr' ?_
  filter_upwards [hδ_pos] with ε _
  simp [Function.comp_apply, add_sub_cancel_left]

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
  have h_compose : Tendsto (fun ε : ℝ => t₀ - δ_left ε)
      (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using tendsto_const_nhds.sub
        (hδ_to_zero.mono_right nhdsWithin_le_nhds : Tendsto δ_left (𝓝[>] (0 : ℝ)) (𝓝 0))
    · filter_upwards [hδ_pos] with ε hε using show t₀ - δ_left ε < t₀ by linarith
  refine ((chord_div_t_tendsto_left h_deriv h_at).comp h_compose).congr' ?_
  filter_upwards [hδ_pos] with ε _
  simp only [Function.comp_apply, show t₀ - δ_left ε - t₀ = -δ_left ε from by ring]

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
  have h_arg_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Complex.arg ((γ (t₀ + δ_right ε) - s) / ((δ_right ε : ℝ) : ℂ)) =
        Complex.arg (γ (t₀ + δ_right ε) - s) := by
    filter_upwards [hδ_pos] with ε hε
    rw [div_eq_inv_mul, ← Complex.ofReal_inv]
    exact Complex.arg_real_mul _ (inv_pos.mpr hε)
  exact ((Complex.continuousAt_arg hL_slit).tendsto.comp
    (exit_chord_tendsto_right h_deriv h_at hδ_pos hδ_to_zero)).congr' h_arg_eq

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
  have h_quot' :
      Tendsto (fun ε : ℝ => (γ (t₀ - δ_left ε) - s) / ((δ_left ε : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (-L)) := by
    refine (exit_chord_tendsto_left h_deriv h_at hδ_pos hδ_to_zero).neg.congr' ?_
    filter_upwards [hδ_pos] with ε hε
    have h_cast : ((-(δ_left ε) : ℝ) : ℂ) = -((δ_left ε : ℝ) : ℂ) := by push_cast; ring
    rw [h_cast, div_neg, neg_neg]
  have h_arg_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Complex.arg ((γ (t₀ - δ_left ε) - s) / ((δ_left ε : ℝ) : ℂ)) =
        Complex.arg (γ (t₀ - δ_left ε) - s) := by
    filter_upwards [hδ_pos] with ε hε
    rw [div_eq_inv_mul, ← Complex.ofReal_inv]
    exact Complex.arg_real_mul _ (inv_pos.mpr hε)
  exact ((Complex.continuousAt_arg hnegL_slit).tendsto.comp h_quot').congr' h_arg_eq

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
  have h_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Complex.log (γ (t₀ + δ_right ε) - s) - ((Real.log ε : ℝ) : ℂ) =
        ((γ (t₀ + δ_right ε) - s).arg : ℂ) * Complex.I := by
    filter_upwards [h_exit] with ε h_exit_ε
    rw [complex_log_eq, h_exit_ε]; ring
  have h_arg := exit_arg_tendsto_right h_deriv h_at hL_slit hδ_pos hδ_to_zero
  have h_mul_I : Tendsto (fun ε : ℝ =>
      ((γ (t₀ + δ_right ε) - s).arg : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝 (L.arg * Complex.I)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto.comp h_arg).mul tendsto_const_nhds
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
  have h_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Complex.log (γ (t₀ - δ_left ε) - s) - ((Real.log ε : ℝ) : ℂ) =
        ((γ (t₀ - δ_left ε) - s).arg : ℂ) * Complex.I := by
    filter_upwards [h_exit] with ε h_exit_ε
    rw [complex_log_eq, h_exit_ε]; ring
  have h_arg := exit_arg_tendsto_left h_deriv h_at hnegL_slit hδ_pos hδ_to_zero
  have h_mul_I : Tendsto (fun ε : ℝ =>
      ((γ (t₀ - δ_left ε) - s).arg : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L).arg * Complex.I)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto.comp h_arg).mul tendsto_const_nhds
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
  have h_right := exit_log_tendsto_right h_deriv_right h_at hL_right_slit
    hδ_right_pos hδ_right_to_zero h_exit_right
  have h_left := exit_log_tendsto_left h_deriv_left h_at hnegL_left_slit
    hδ_left_pos hδ_left_to_zero h_exit_left
  refine (h_right.sub h_left).congr' (Eventually.of_forall fun ε => ?_)
  ring

/-- **Normalized chord close to 1 (right side).** For any `ρ > 0`, eventually
on `𝓝[>] t₀`, `‖(γ(t) - s) / (L · (t - t₀)) - 1‖ ≤ ρ`.

This is the key chord-to-tangent estimate in normalized form. -/
theorem normalized_chord_close_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∀ᶠ t in 𝓝[>] t₀,
      ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  have h_div := ((chord_div_t_tendsto_right h_deriv h_at).div_const L)
  rw [div_self hL] at h_div
  have h_tendsto_one : Tendsto
      (fun t : ℝ => (γ t - s) / (L * ((t - t₀ : ℝ) : ℂ))) (𝓝[>] t₀) (𝓝 1) := by
    refine h_div.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h_ne : ((t - t₀ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr ht))
    field_simp
  rw [Metric.tendsto_nhds] at h_tendsto_one
  filter_upwards [h_tendsto_one ρ hρ_pos] with t ht
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
  have h_div := ((chord_div_t_tendsto_left h_deriv h_at).div_const L)
  rw [div_self hL] at h_div
  have h_tendsto_one : Tendsto
      (fun t : ℝ => (γ t - s) / (L * ((t - t₀ : ℝ) : ℂ))) (𝓝[<] t₀) (𝓝 1) := by
    refine h_div.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h_ne : ((t - t₀ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_lt (sub_neg_of_lt ht))
    field_simp
  rw [Metric.tendsto_nhds] at h_tendsto_one
  filter_upwards [h_tendsto_one ρ hρ_pos] with t ht
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
  refine ⟨r / 2, by linarith, fun t ht_in => hU_prop t (hV_sub ⟨?_, ht_in.1⟩)⟩
  apply hr_ball
  rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith [ht_in.1] : 0 < t - t₀)]
  linarith [ht_in.2]

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
  refine ⟨r / 2, by linarith, fun t ht_in => hU_prop t (hV_sub ⟨?_, ht_in.2⟩)⟩
  apply hr_ball
  rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith [ht_in.2] : t - t₀ < 0)]
  linarith [ht_in.1]

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
    rw [show ((1 : ℂ) - w) = -(w - 1) from by ring, norm_neg, norm_one] at h_sub_nn
    linarith
  have hw_pos : 0 < ‖w‖ := by linarith
  have h_diff : z / w - 1 = (z - w) / w := by field_simp
  have h_diff_norm : ‖z / w - 1‖ < 1 := by
    rw [h_diff, norm_div, div_lt_iff₀ hw_pos]
    nlinarith
  rw [Complex.mem_slitPlane_iff]
  refine .inl ?_
  have h_re : |(z / w).re - 1| < 1 := by
    have h1 := Complex.abs_re_le_norm (z / w - 1)
    simp at h1
    linarith
  rw [abs_sub_lt_iff] at h_re
  linarith

/-- Multiplication by a positive real preserves membership in `Complex.slitPlane`. -/
private lemma ofReal_pos_mul_mem_slitPlane {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) : ((c : ℝ) : ℂ) * z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hz ⊢
  rcases hz with h_re | h_im
  · left
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos hc h_re
  · right
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_ne_zero hc.ne' h_im

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
  have ha_in : a ∈ Ioc t₀ (t₀ + r) := ⟨ha_gt, ha_le⟩
  have hb_in : b ∈ Ioc t₀ (t₀ + r) := ⟨hb_gt, hb_le⟩
  have ha_pos : 0 < a - t₀ := sub_pos.mpr ha_gt
  have hb_pos : 0 < b - t₀ := sub_pos.mpr hb_gt
  have ha_pos_C : ((a - t₀ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt ha_pos)
  have hb_pos_C : ((b - t₀ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hb_pos)
  set z := (γ b - s) / (L * ((b - t₀ : ℝ) : ℂ))
  set w := (γ a - s) / (L * ((a - t₀ : ℝ) : ℂ))
  have h_zw : z / w ∈ Complex.slitPlane :=
    div_mem_slitPlane_of_close_to_one (hr_close b hb_in) (hr_close a ha_in)
  have h_ratio : (γ b - s) / (γ a - s) =
      (((b - t₀) / (a - t₀) : ℝ) : ℂ) * (z / w) := by
    have hL_ab : L * ((b - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL hb_pos_C
    have hL_aa : L * ((a - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL ha_pos_C
    rw [show (γ b - s) / (γ a - s) =
        (z * (L * ((b - t₀ : ℝ) : ℂ))) / (w * (L * ((a - t₀ : ℝ) : ℂ))) from by
      congr 1
      · simp only [z]; exact (div_mul_cancel₀ _ hL_ab).symm
      · simp only [w]; exact (div_mul_cancel₀ _ hL_aa).symm]
    push_cast; field_simp
  rw [h_ratio]
  exact ofReal_pos_mul_mem_slitPlane (div_pos hb_pos ha_pos) h_zw

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
  set z := (γ b - s) / (L * ((b - t₀ : ℝ) : ℂ))
  set w := (γ a - s) / (L * ((a - t₀ : ℝ) : ℂ))
  have h_zw : z / w ∈ Complex.slitPlane :=
    div_mem_slitPlane_of_close_to_one (hr_close b hb_in) (hr_close a ha_in)
  have h_ratio : (γ b - s) / (γ a - s) =
      (((b - t₀) / (a - t₀) : ℝ) : ℂ) * (z / w) := by
    have hL_aa : L * ((a - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL ha_neg_C
    have hL_bb : L * ((b - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL hb_neg_C
    rw [show (γ b - s) / (γ a - s) =
        (z * (L * ((b - t₀ : ℝ) : ℂ))) / (w * (L * ((a - t₀ : ℝ) : ℂ))) from by
      congr 1
      · simp only [z]; exact (div_mul_cancel₀ _ hL_bb).symm
      · simp only [w]; exact (div_mul_cancel₀ _ hL_aa).symm]
    push_cast; field_simp
  rw [h_ratio]
  exact ofReal_pos_mul_mem_slitPlane (div_pos_of_neg_of_neg hb_neg ha_neg) h_zw

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
  set z := (γ a - s) / (L * ((a - t₀ : ℝ) : ℂ))
  set w := (γ b - s) / (L * ((b - t₀ : ℝ) : ℂ))
  have h_zw : z / w ∈ Complex.slitPlane :=
    div_mem_slitPlane_of_close_to_one (hr_close a ha_in) (hr_close b hb_in)
  have h_ratio : (γ a - s) / (γ b - s) =
      (((a - t₀) / (b - t₀) : ℝ) : ℂ) * (z / w) := by
    have hL_aa : L * ((a - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL ha_neg_C
    have hL_bb : L * ((b - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL hb_neg_C
    rw [show (γ a - s) / (γ b - s) =
        (z * (L * ((a - t₀ : ℝ) : ℂ))) / (w * (L * ((b - t₀ : ℝ) : ℂ))) from by
      congr 1
      · simp only [z]; exact (div_mul_cancel₀ _ hL_aa).symm
      · simp only [w]; exact (div_mul_cancel₀ _ hL_bb).symm]
    push_cast; field_simp
  rw [h_ratio]
  exact ofReal_pos_mul_mem_slitPlane (div_pos_of_neg_of_neg ha_neg hb_neg) h_zw

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
  have hab : t₀ + δ_R ≤ t₀ + r := by linarith
  have h_slit_ab : ∀ t ∈ Icc (t₀ + δ_R) (t₀ + r),
      (γf t - s) / (γf (t₀ + δ_R) - s) ∈ Complex.slitPlane :=
    fun t ht_in => h_slit_R (t₀ + δ_R) t (by linarith) ht_in.1 ht_in.2
  have ha_ne : γf (t₀ + δ_R) - s ≠ 0 := by
    intro h_eq
    have h_in_01 : t₀ + δ_R ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    linarith [h_unique _ h_in_01 (sub_eq_zero.mp h_eq)]
  have hγ_cont : ContinuousOn γf (Icc (t₀ + δ_R) (t₀ + r)) :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousOn
  have hP_count : (↑γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ).Countable :=
    γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.countable
  have hγ_diff : ∀ t ∈ Ioo (t₀ + δ_R) (t₀ + r) \
      (↑γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ),
      HasDerivAt γf (deriv γf t) t := fun t ht =>
    (γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off_extend t
      ⟨by linarith [ht.1.1, ht₀_pos, hδ_R_pos], by linarith [ht.1.2, hr_le_one_sub]⟩
      ht.2).hasDerivAt
  have h_int : IntervalIntegrable
      (fun t => deriv γf t / (γf t - s)) MeasureTheory.volume (t₀ + δ_R) (t₀ + r) := by
    have h1 := inv_sub_mul_deriv_intervalIntegrable_right γ
      (⟨ht₀_pos, by linarith [hr_le_one_sub, hδ_R_pos, hδ_R_lt]⟩ :
        t₀ ∈ Ioo (0 : ℝ) 1) (δ_right_ε := δ_R) hδ_R_pos
      (by linarith [hr_le_one_sub] : δ_R < 1 - t₀) h_unique
    refine h1.mono_set ?_ |>.congr fun t _ => by simp only [hγf_def]; ring
    rw [Set.uIcc_of_le hab,
      Set.uIcc_of_le (by linarith [hr_le_one_sub] : t₀ + δ_R ≤ 1)]
    exact Set.Icc_subset_Icc le_rfl (by linarith [hr_le_one_sub])
  exact segment_log_FTC hab hP_count hγ_cont hγ_diff ha_ne h_slit_ab h_int

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
  refine le_antisymm h_le ?_
  have h_g_cont : Continuous (fun η : ℝ => ‖γf (t₀ + D.δ_right ε + η) - s‖) :=
    ((γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.comp
      (continuous_const.add continuous_id)).sub continuous_const).norm
  have h_tendsto : Tendsto
      (fun η : ℝ => ‖γf (t₀ + D.δ_right ε + η) - s‖)
      (𝓝[>] 0) (𝓝 ‖γf (t₀ + D.δ_right ε) - s‖) := by
    have h1 := h_g_cont.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))
    simpa using h1
  refine ge_of_tendsto h_tendsto ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1 - t₀ - D.δ_right ε)] with η hη
  exact (D.h_far_right ε hε_pos hε_lt (t₀ + D.δ_right ε + η)
    ⟨by linarith [ht₀.1, hη.1], by linarith [hη.2]⟩ (by linarith [hη.1])
    (by linarith [hη.1])).le

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
  refine le_antisymm h_le ?_
  have h_g_cont : Continuous (fun η : ℝ => ‖γf (t₀ - D.δ_left ε - η) - s‖) :=
    ((γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.comp
      (continuous_const.sub continuous_id)).sub continuous_const).norm
  have h_tendsto : Tendsto
      (fun η : ℝ => ‖γf (t₀ - D.δ_left ε - η) - s‖)
      (𝓝[>] 0) (𝓝 ‖γf (t₀ - D.δ_left ε) - s‖) := by
    have h1 := h_g_cont.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))
    simpa using h1
  refine ge_of_tendsto h_tendsto ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < t₀ - D.δ_left ε)] with η hη
  exact (D.h_far_left ε hε_pos hε_lt (t₀ - D.δ_left ε - η)
    ⟨by linarith [hη.2], by linarith [ht₀.2, hη.1]⟩ (by linarith [hη.1])
    (by linarith [hη.1])).le

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
  have hab : t₀ - r ≤ t₀ - δ_L := by linarith
  have h_slit_ab : ∀ t ∈ Icc (t₀ - r) (t₀ - δ_L),
      (γf t - s) / (γf (t₀ - r) - s) ∈ Complex.slitPlane :=
    fun t ht_in => h_slit_L (t₀ - r) t le_rfl ht_in.1 (lt_of_le_of_lt ht_in.2 (by linarith))
  have ha_ne : γf (t₀ - r) - s ≠ 0 := by
    intro h_eq
    have h_in_01 : t₀ - r ∈ Icc (0 : ℝ) 1 := ⟨hr_le_t₀, by linarith⟩
    have : t₀ - r = t₀ := h_unique _ h_in_01 (sub_eq_zero.mp h_eq)
    linarith
  have hγ_cont : ContinuousOn γf (Icc (t₀ - r) (t₀ - δ_L)) :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousOn
  have hP_count : (↑γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ).Countable :=
    γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.countable
  have hγ_diff : ∀ t ∈ Ioo (t₀ - r) (t₀ - δ_L) \
      (↑γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ),
      HasDerivAt γf (deriv γf t) t := fun t ht =>
    (γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off_extend t
      ⟨by linarith [ht.1.1, hr_le_t₀], by linarith [ht.1.2, hδ_L_pos]⟩
      ht.2).hasDerivAt
  have h_int : IntervalIntegrable
      (fun t => deriv γf t / (γf t - s)) MeasureTheory.volume (t₀ - r) (t₀ - δ_L) := by
    have ht₀_in : t₀ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hr_le_t₀, hδ_L_pos, hδ_L_lt],
      ht₀_lt_one⟩
    have hδL_lt_t₀ : δ_L < t₀ := lt_of_lt_of_le hδ_L_lt (by linarith [hr_le_t₀])
    have h1 := inv_sub_mul_deriv_intervalIntegrable_left γ ht₀_in
      (δ_left_ε := δ_L) hδ_L_pos hδL_lt_t₀ h_unique
    refine h1.mono_set ?_ |>.congr fun t _ => by simp only [hγf_def]; ring
    rw [Set.uIcc_of_le hab,
      Set.uIcc_of_le (by linarith [hδL_lt_t₀] : (0 : ℝ) ≤ t₀ - δ_L)]
    exact Set.Icc_subset_Icc hr_le_t₀ le_rfl
  exact segment_log_FTC hab hP_count hγ_cont hγ_diff ha_ne h_slit_ab h_int

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
  have h_recip : Tendsto (fun ε : ℝ => ((δ_right ε : ℝ) : ℂ) / (γ (t₀ + δ_right ε) - s))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / L)) := by
    rw [one_div]
    refine ((exit_chord_tendsto_right h_deriv h_at hδ_pos hδ_to_zero).inv₀ hL).congr' ?_
    filter_upwards with ε using by rw [inv_div]
  have h_quot_delta : Tendsto (fun ε : ℝ =>
      (γ (t₀ + r) - s) * (((δ_right ε : ℝ) : ℂ) / (γ (t₀ + δ_right ε) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((γ (t₀ + r) - s) / L)) := by
    have h1 := tendsto_const_nhds (x := γ (t₀ + r) - s) |>.mul h_recip
    rwa [mul_one_div] at h1
  refine ((Complex.continuousAt_arg h_γr_div_L).tendsto.comp h_quot_delta).congr' ?_
  filter_upwards [hδ_pos] with ε hε
  rw [Function.comp_apply, show (γ (t₀ + r) - s) * (((δ_right ε : ℝ) : ℂ) /
      (γ (t₀ + δ_right ε) - s)) =
      ((δ_right ε : ℝ) : ℂ) * ((γ (t₀ + r) - s) / (γ (t₀ + δ_right ε) - s)) from by ring]
  exact Complex.arg_real_mul _ hε

/-- **Left annular quotient arg convergence.** -/
theorem arg_left_annular_tendsto
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (_hL : L ≠ 0)
    {δ_left : ℝ → ℝ} {r : ℝ}
    (h_γnegr_div_L : (-L) / (γ (t₀ - r) - s) ∈ Complex.slitPlane)
    (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_left ε)
    (hδ_to_zero : Tendsto δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ))) :
    Tendsto (fun ε : ℝ =>
      Complex.arg ((γ (t₀ - δ_left ε) - s) / (γ (t₀ - r) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L) / (γ (t₀ - r) - s)).arg) := by
  have h_quot' : Tendsto (fun ε : ℝ =>
      (γ (t₀ - δ_left ε) - s) / ((δ_left ε : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (-L)) := by
    refine (exit_chord_tendsto_left h_deriv h_at hδ_pos hδ_to_zero).neg.congr' ?_
    filter_upwards with ε using by push_cast; rw [div_neg, neg_neg]
  refine ((Complex.continuousAt_arg h_γnegr_div_L).tendsto.comp
    (h_quot'.div_const (γ (t₀ - r) - s))).congr' ?_
  filter_upwards [hδ_pos] with ε hε
  rw [Function.comp_apply, show (γ (t₀ - δ_left ε) - s) / ((δ_left ε : ℝ) : ℂ) /
      (γ (t₀ - r) - s) =
      (((δ_left ε)⁻¹ : ℝ) : ℂ) * ((γ (t₀ - δ_left ε) - s) / (γ (t₀ - r) - s)) from by
    push_cast; field_simp]
  exact Complex.arg_real_mul _ (inv_pos.mpr hε)

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
  · rw [Metric.tendsto_nhds]
    intro δ₀ hδ₀_pos
    set δ₀' : ℝ := min δ₀ ((1 - t₀) / 2) with hδ₀'_def
    have hδ₀'_pos : 0 < δ₀' := lt_min hδ₀_pos (by linarith [ht₀_Ioo.2])
    have hδ₀'_le : δ₀' ≤ δ₀ := min_le_left _ _
    have hδ₀'_le_half : δ₀' ≤ (1 - t₀) / 2 := min_le_right _ _
    have h_in_01 : t₀ + δ₀' ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [ht₀_Ioo.1], by linarith [ht₀_Ioo.2]⟩
    have hm_pos : 0 < ‖γf (t₀ + δ₀') - s‖ := by
      refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h_eq => ?_)
      linarith [h_unique _ h_in_01 h_eq]
    filter_upwards [Ioo_mem_nhdsGT (lt_min hm_pos D.hthresh)] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt_thresh : ε < D.threshold := lt_of_lt_of_le hε.2 (min_le_right _ _)
    have hε_lt_m : ε < ‖γf (t₀ + δ₀') - s‖ := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hδR_pos := D.hδ_right_pos ε hε_pos hε_lt_thresh
    by_contra h_ge
    push Not at h_ge
    rw [Real.dist_eq, sub_zero, abs_of_pos hδR_pos] at h_ge
    have h_t_in : t₀ + δ₀' - t₀ ≤ D.δ_right ε := by linarith [hδ₀'_le.trans h_ge]
    linarith [D.h_near_right ε hε_pos hε_lt_thresh (t₀ + δ₀') (by linarith) h_t_in]
  · filter_upwards [Ioo_mem_nhdsGT D.hthresh] with ε hε
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
    have hm_pos : 0 < ‖γf (t₀ - δ₀') - s‖ := by
      refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h_eq => ?_)
      linarith [h_unique _ h_in_01 h_eq]
    filter_upwards [Ioo_mem_nhdsGT (lt_min hm_pos D.hthresh)] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt_thresh : ε < D.threshold := lt_of_lt_of_le hε.2 (min_le_right _ _)
    have hε_lt_m : ε < ‖γf (t₀ - δ₀') - s‖ := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hδL_pos := D.hδ_left_pos ε hε_pos hε_lt_thresh
    by_contra h_ge
    push Not at h_ge
    rw [Real.dist_eq, sub_zero, abs_of_pos hδL_pos] at h_ge
    have h_t_in : t₀ - (t₀ - δ₀') ≤ D.δ_left ε := by linarith [hδ₀'_le.trans h_ge]
    linarith [D.h_near_left ε hε_pos hε_lt_thresh (t₀ - δ₀') (by linarith) h_t_in]
  · filter_upwards [Ioo_mem_nhdsGT D.hthresh] with ε hε
    exact D.hδ_left_pos ε hε.1 hε.2

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
  obtain ⟨L_R, hL_R_ne, hL_R_tendsto⟩ := exists_right_deriv_limit γ ht₀
  obtain ⟨L_L, hL_L_ne, hL_L_tendsto⟩ := exists_left_deriv_limit γ ht₀
  have hγf_cont : ContinuousAt γf t₀ :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousAt
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
  have hr_le_R₁ : r ≤ r_R₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hr_le_L₁ : r ≤ r_L₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hr_le_R₂ : r ≤ r_R₂ :=
    (min_le_right _ _).trans <| (min_le_left _ _).trans (min_le_left _ _)
  have hr_le_L₂ : r ≤ r_L₂ :=
    (min_le_right _ _).trans <| (min_le_left _ _).trans (min_le_right _ _)
  have hr_le_t₀_half : r ≤ t₀ / 2 :=
    (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)
  have hr_le_one_sub_half : r ≤ (1 - t₀) / 2 :=
    (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_right _ _)
  have hr_le_t₀ : r ≤ t₀ := by linarith
  have hr_le_one_sub : r ≤ 1 - t₀ := by linarith
  have hr_lt_one_sub : r < 1 - t₀ := by linarith
  have hr_lt_t₀ : r < t₀ := by linarith
  have hr_C_ne : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr_pos)
  have h_γPlus_div_LR : (γf (t₀ + r) - s) / L_R ∈ Complex.slitPlane := by
    have h_close : ‖(γf (t₀ + r) - s) / (L_R * ((r : ℝ) : ℂ)) - 1‖ ≤ 1/4 := by
      have h_orig := hr_R₂_close (t₀ + r) ⟨by linarith, by linarith⟩
      rwa [show (((t₀ + r) - t₀ : ℝ) : ℂ) = ((r : ℝ) : ℂ) from by push_cast; ring] at h_orig
    have hLR_C_ne : L_R * ((r : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL_R_ne hr_C_ne
    rw [show (γf (t₀ + r) - s) / L_R =
        ((r : ℝ) : ℂ) * ((γf (t₀ + r) - s) / (L_R * ((r : ℝ) : ℂ))) from by field_simp]
    refine ofReal_pos_mul_mem_slitPlane hr_pos ?_
    rw [Complex.mem_slitPlane_iff]
    refine .inl ?_
    have h1 := Complex.abs_re_le_norm ((γf (t₀ + r) - s) / (L_R * ((r : ℝ) : ℂ)) - 1)
    simp at h1
    linarith [(abs_le.mp (h1.trans h_close)).1]
  have h_LL_neg_div_γMinus : (-L_L) / (γf (t₀ - r) - s) ∈ Complex.slitPlane := by
    have h_γMinus_ne : γf (t₀ - r) - s ≠ 0 := by
      intro h_eq
      have h_in_01 : t₀ - r ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht₀.2]⟩
      linarith [h_unique _ h_in_01 (sub_eq_zero.mp h_eq)]
    have hLL_C_ne : L_L * ((r : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL_L_ne hr_C_ne
    set q : ℂ := (γf (t₀ - r) - s) / (L_L * ((r : ℝ) : ℂ)) with hq_def
    have hq_close : ‖-q - 1‖ ≤ 1/4 := by
      have h_orig := hr_L₂_close (t₀ - r) ⟨by linarith, by linarith⟩
      rwa [show (((t₀ - r) - t₀ : ℝ) : ℂ) = -((r : ℝ) : ℂ) from by push_cast; ring,
        mul_neg, div_neg, ← hq_def] at h_orig
    have hq_norm : 3/4 ≤ ‖q‖ := by
      have h_rev : ‖(-1 : ℂ)‖ - ‖q‖ ≤ ‖-1 - q‖ := norm_sub_norm_le _ _
      rw [norm_neg, norm_one, show ((-1 : ℂ) - q) = -(q + 1) from by ring, norm_neg,
        show q + 1 = -(-q - 1) from by ring, norm_neg] at h_rev
      linarith
    have hq_ne : q ≠ 0 := by
      intro h_eq
      rw [h_eq, norm_zero] at hq_norm
      linarith
    have h_neg_inv_q_close : ‖(-1 / q) - 1‖ ≤ 1/3 := by
      rw [show ((-1 : ℂ) / q) - 1 = -((1 + q) / q) from by field_simp; ring, norm_neg,
        norm_div, show (1 : ℂ) + q = -(-q - 1) from by ring, norm_neg,
        div_le_iff₀ (norm_pos_iff.mpr hq_ne)]
      nlinarith [hq_close, hq_norm]
    have h_eq_target : (-L_L) / (γf (t₀ - r) - s) =
        (((1/r) : ℝ) : ℂ) * (-1 / q) := by
      rw [hq_def]; push_cast; field_simp
    rw [h_eq_target]
    refine ofReal_pos_mul_mem_slitPlane (by positivity) ?_
    rw [Complex.mem_slitPlane_iff]
    refine .inl ?_
    have h_abs_re_le : |(-1 / q).re - 1| ≤ 1/3 := by
      have h1 := Complex.abs_re_le_norm (-1 / q - 1)
      simp at h1
      linarith [h_neg_inv_q_close]
    linarith [(abs_le.mp h_abs_re_le).1]
  refine ⟨L_R, L_L, r, hL_R_ne, hL_L_ne, hr_pos, hr_le_t₀, hr_le_one_sub,
    h_deriv_right, h_deriv_left, ?_, ?_, h_γPlus_div_LR, h_LL_neg_div_γMinus⟩
  · intro a b ha_gt hab hb_le
    exact hr_R₁_slit a b ha_gt hab (le_trans hb_le (by linarith [hr_le_R₁]))
  · intro a b ha_ge hab hb_lt
    exact hr_L₁_slit a b (le_trans (by linarith [hr_le_L₁]) ha_ge) hab hb_lt

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
  obtain ⟨L_R, L_L, r, hL_R_ne, hL_L_ne, hr_pos, hr_le_t₀, hr_le_one_sub,
    h_deriv_right, h_deriv_left, h_slit_R, h_slit_L, h_γPlus_div_LR,
    h_LL_neg_div_γMinus⟩ := cpvFullSetup γ ht₀ h_at h_unique
  set D : DerivedAsymmetricCutoffs γ s t₀ :=
    deriveAsymmetricCutoffs_anywhere γ ht₀ h_at h_unique with hD_def
  have hδR_tendsto : Tendsto D.δ_right (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    DerivedAsymmetricCutoffs.δ_right_tendsto_zero ht₀ h_unique D
  have hδL_tendsto : Tendsto D.δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    DerivedAsymmetricCutoffs.δ_left_tendsto_zero ht₀ h_unique D
  have hδR_lt_r : ∀ᶠ ε in 𝓝[>] (0 : ℝ), D.δ_right ε < r := by
    filter_upwards [(hδR_tendsto.mono_right nhdsWithin_le_nhds).eventually
      (Metric.ball_mem_nhds (0 : ℝ) hr_pos)] with ε hε
    rw [Real.dist_eq, sub_zero] at hε
    linarith [le_abs_self (D.δ_right ε)]
  have hδL_lt_r : ∀ᶠ ε in 𝓝[>] (0 : ℝ), D.δ_left ε < r := by
    filter_upwards [(hδL_tendsto.mono_right nhdsWithin_le_nhds).eventually
      (Metric.ball_mem_nhds (0 : ℝ) hr_pos)] with ε hε
    rw [Real.dist_eq, sub_zero] at hε
    linarith [le_abs_self (D.δ_left ε)]
  set C₁ : ℂ := ∫ t in (0 : ℝ)..(t₀ - r),
    (γf t - s)⁻¹ * deriv γf t with hC₁_def
  set C₂ : ℂ := ∫ t in (t₀ + r)..1,
    (γf t - s)⁻¹ * deriv γf t with hC₂_def
  set Λ_R : ℝ → ℂ := fun ε =>
    Complex.log ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)) with hΛR_def
  set Λ_L : ℝ → ℂ := fun ε =>
    Complex.log ((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)) with hΛL_def
  have hδR_pos_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < D.δ_right ε := by
    filter_upwards [Ioo_mem_nhdsGT D.hthresh] with ε hε
    exact D.hδ_right_pos ε hε.1 hε.2
  have hδL_pos_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < D.δ_left ε := by
    filter_upwards [Ioo_mem_nhdsGT D.hthresh] with ε hε
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
  set argR_lim : ℝ := ((γf (t₀ + r) - s) / L_R).arg with hargR_def
  set argL_lim : ℝ := ((-L_L) / (γf (t₀ - r) - s)).arg with hargL_def
  set logNorm_diff : ℝ :=
    Real.log ‖γf (t₀ + r) - s‖ - Real.log ‖γf (t₀ - r) - s‖ with hlogND_def
  set L : ℂ := C₁ + C₂ + ((logNorm_diff : ℝ) : ℂ) +
    (((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I) with hL_def
  refine ⟨L, ?_⟩
  unfold HasCauchyPV
  have h_eventually_eq :
      (fun ε => ∫ t in (0 : ℝ)..1,
          cpvIntegrand (fun z => (z - s)⁻¹) γf s ε t) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε => C₁ + Λ_L ε + Λ_R ε + C₂) := by
    filter_upwards [Ioo_mem_nhdsGT D.hthresh, hδR_lt_r, hδL_lt_r,
        hδR_pos_ev, hδL_pos_ev] with ε hε_thresh hδR_r hδL_r hδR_pos hδL_pos
    have hε_pos : 0 < ε := hε_thresh.1
    have hε_lt_thresh : ε < D.threshold := hε_thresh.2
    rw [cutoff_integral_eq_outer_sum γ ht₀ D h_unique hε_pos hε_lt_thresh]
    have hδR_pos' := D.hδ_right_pos ε hε_pos hε_lt_thresh
    have hδL_pos' := D.hδ_left_pos ε hε_pos hε_lt_thresh
    have h_int_left : IntervalIntegrable
        (fun t => (γf t - s)⁻¹ * deriv γf t) MeasureTheory.volume 0 (t₀ - D.δ_left ε) :=
      inv_sub_mul_deriv_intervalIntegrable_left γ ht₀ hδL_pos'
        (D.hδ_left_small ε hε_pos hε_lt_thresh) h_unique
    have h_int_right : IntervalIntegrable
        (fun t => (γf t - s)⁻¹ * deriv γf t) MeasureTheory.volume (t₀ + D.δ_right ε) 1 :=
      inv_sub_mul_deriv_intervalIntegrable_right γ ht₀ hδR_pos'
        (D.hδ_right_small ε hε_pos hε_lt_thresh) h_unique
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
      rw [integral_inv_sub_mul_eq_div,
        left_annular_log_diff γ hL_L_ne h_deriv_left h_at hδL_pos' hδL_r hr_pos hr_le
          h_slit_L h_unique ht₀.2]
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
      rw [integral_inv_sub_mul_eq_div,
        right_annular_log_diff γ hL_R_ne h_deriv_right h_at hδR_pos' hδR_r hr_pos hr_le
          h_slit_R h_unique ht₀.1]
    rw [h_left_split, h_right_split]
    ring
  refine Tendsto.congr' h_eventually_eq.symm ?_
  have h_sum_tendsto : Tendsto (fun ε : ℝ => Λ_L ε + Λ_R ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (((logNorm_diff : ℝ) : ℂ) +
        ((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I)) := by
    have h_decomp : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        Λ_L ε + Λ_R ε = ((logNorm_diff : ℝ) : ℂ) +
          ((((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg +
            ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg : ℝ) : ℂ) * Complex.I := by
      filter_upwards [Ioo_mem_nhdsGT D.hthresh, hδR_lt_r, hδL_lt_r,
          hδR_pos_ev, hδL_pos_ev] with ε hε_thresh hδR_r hδL_r hδR_pos hδL_pos
      have hε_pos : 0 < ε := hε_thresh.1
      have hε_lt_thresh : ε < D.threshold := hε_thresh.2
      have h_eq_R := exit_time_eq_right γ D ht₀ hε_pos hε_lt_thresh
      have h_eq_L := exit_time_eq_left γ D ht₀ hε_pos hε_lt_thresh
      have h_γPlus_ne : γf (t₀ + r) - s ≠ 0 := fun h_eq => by
        have : t₀ + r ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht₀.1], by linarith⟩
        linarith [h_unique _ this (sub_eq_zero.mp h_eq)]
      have h_γMinus_ne : γf (t₀ - r) - s ≠ 0 := fun h_eq => by
        have : t₀ - r ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht₀.2]⟩
        linarith [h_unique _ this (sub_eq_zero.mp h_eq)]
      have h_γR_ne : γf (t₀ + D.δ_right ε) - s ≠ 0 := norm_pos_iff.mp (h_eq_R.symm ▸ hε_pos)
      have h_γL_ne : γf (t₀ - D.δ_left ε) - s ≠ 0 := norm_pos_iff.mp (h_eq_L.symm ▸ hε_pos)
      have h_log_R_decomp : Λ_R ε =
          ((Real.log ‖γf (t₀ + r) - s‖ - Real.log ‖γf (t₀ + D.δ_right ε) - s‖ : ℝ) : ℂ) +
          (((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg : ℂ) * Complex.I := by
        simp only [hΛR_def]
        rw [complex_log_eq, norm_div,
          Real.log_div (norm_ne_zero_iff.mpr h_γPlus_ne) (norm_ne_zero_iff.mpr h_γR_ne)]
      have h_log_L_decomp : Λ_L ε =
          ((Real.log ‖γf (t₀ - D.δ_left ε) - s‖ - Real.log ‖γf (t₀ - r) - s‖ : ℝ) : ℂ) +
          (((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg : ℂ) * Complex.I := by
        simp only [hΛL_def]
        rw [complex_log_eq, norm_div,
          Real.log_div (norm_ne_zero_iff.mpr h_γL_ne) (norm_ne_zero_iff.mpr h_γMinus_ne)]
      rw [h_log_L_decomp, h_log_R_decomp, h_eq_R, h_eq_L]
      simp only [hlogND_def]
      push_cast
      ring
    refine Tendsto.congr' (h_decomp.mono fun _ h => h.symm) ?_
    refine tendsto_const_nhds.add ?_
    have h_arg_sum : Tendsto (fun ε : ℝ =>
        ((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg +
          ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg)
        (𝓝[>] (0 : ℝ)) (𝓝 (argL_lim + argR_lim)) := by
      simpa [hargL_def, hargR_def, add_comm] using h_arg_L_clean.add h_arg_R_clean
    rw [show ((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I =
        ((argL_lim + argR_lim : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    exact ((Complex.continuous_ofReal.tendsto _).comp h_arg_sum).mul tendsto_const_nhds
  have h_full : Tendsto (fun ε : ℝ => C₁ + (Λ_L ε + Λ_R ε) + C₂)
      (𝓝[>] (0 : ℝ)) (𝓝 (C₁ + (((logNorm_diff : ℝ) : ℂ) +
        ((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I) + C₂)) :=
    (tendsto_const_nhds.add h_sum_tendsto).add tendsto_const_nhds
  rw [show L = C₁ + (((logNorm_diff : ℝ) : ℂ) +
      ((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I) + C₂ from by rw [hL_def]; ring]
  refine h_full.congr' ?_
  filter_upwards with ε using by ring

end HungerbuhlerWasem

end
