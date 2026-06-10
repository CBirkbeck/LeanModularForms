/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import LeanModularForms.ForMathlib.HungerbuhlerWasem.CrossingDataBuilder
public import LeanModularForms.ForMathlib.WindingInteger

/-!
# Chord-to-tangent asymptotics at a transverse crossing

For a curve `γ : ℝ → ℂ` passing through a pole `s` at time `t₀` with
non-vanishing one-sided derivatives, this file develops the chord-to-tangent
estimates feeding the CPV existence argument: the chord quotient
`(γ(t) - s) / (t - t₀)` tends to the one-sided tangent, the normalized chord
`(γ(t) - s) / (L · (t - t₀))` is close to `1` on small one-sided intervals,
chord quotients there lie in the slit plane, and the annular quotient
arguments converge as the excision window shrinks.

Where the two sides share a proof, the statement is parametrised over the
within-set `u` (`Ioi t₀` on the right, `Iio t₀` on the left).

## Main results

* `chord_div_t_tendsto`: the chord-to-tangent limit
  `(γ(t) - s) / (t - t₀) → L` along `𝓝[u] t₀` for `t₀ ∉ u`.
* `normalized_chord_close`: eventually `‖(γ(t) - s) / (L · (t - t₀)) - 1‖ ≤ ρ`.
* `exists_normalized_chord_right` / `exists_normalized_chord_left`: the same
  bound on a fixed interval `Ioc t₀ (t₀ + r)` resp. `Ico (t₀ - r) t₀`.
* `exists_slitPlane_chord_quotient_right` / `_left_forward`: chord quotients
  `(γ(b) - s) / (γ(a) - s)` on small one-sided intervals lie in the slit plane.
* `arg_right_annular_tendsto` / `arg_left_annular_tendsto`: convergence of the
  annular quotient arguments along a positive cutoff `δ(ε) → 0⁺`.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Real Interval

@[expose] public section

noncomputable section

namespace HungerbuhlerWasem

variable {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}

/-- **Chord-to-tangent quotient limit.** Given `HasDerivWithinAt γ L u t₀` with
`t₀ ∉ u` and `γ(t₀) = s`, the chord quotient `(γ(t) - s) / (t - t₀)` tends to
`L` along `𝓝[u] t₀`. Specialises to the one-sided limits at `u = Ioi t₀`
(right) and `u = Iio t₀` (left). -/
theorem chord_div_t_tendsto {u : Set ℝ} (hu : t₀ ∉ u)
    (h_deriv : HasDerivWithinAt γ L u t₀) (h_at : γ t₀ = s) :
    Tendsto (fun t : ℝ => (γ t - s) / ((t - t₀ : ℝ) : ℂ)) (𝓝[u] t₀) (𝓝 L) := by
  refine ((hasDerivWithinAt_iff_tendsto_slope' hu).mp h_deriv).congr fun t => ?_
  rw [slope_def_module, h_at, Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div]

/-- **Normalized chord close to 1.** For any `ρ > 0`, eventually along
`𝓝[u] t₀`, `‖(γ(t) - s) / (L · (t - t₀)) - 1‖ ≤ ρ`. This is the key
chord-to-tangent estimate in normalized form. -/
theorem normalized_chord_close {u : Set ℝ} (hu : t₀ ∉ u)
    (h_deriv : HasDerivWithinAt γ L u t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∀ᶠ t in 𝓝[u] t₀, ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  have h_div := (chord_div_t_tendsto hu h_deriv h_at).div_const L
  rw [div_self hL] at h_div
  have h_one : Tendsto (fun t : ℝ => (γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)))
      (𝓝[u] t₀) (𝓝 1) := h_div.congr fun t => by rw [div_div, mul_comm]
  filter_upwards [Metric.tendsto_nhds.mp h_one ρ hρ_pos] with t ht
  rw [dist_eq_norm] at ht
  exact ht.le

/-- **Fixed-radius normalized chord bound (right side).** From the eventual
bound, extract a positive radius `r > 0` such that the bound holds uniformly
on `(t₀, t₀ + r]`. -/
theorem exists_normalized_chord_right
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∃ r > 0, ∀ t ∈ Ioc t₀ (t₀ + r),
      ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  obtain ⟨c, hc, h⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (normalized_chord_close self_notMem_Ioi h_deriv h_at hL hρ_pos)
  exact ⟨c - t₀, sub_pos.mpr hc, fun t ht => h ⟨ht.1, by linarith [ht.2]⟩⟩

/-- **Fixed-radius normalized chord bound (left side).** -/
theorem exists_normalized_chord_left
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∃ r > 0, ∀ t ∈ Ico (t₀ - r) t₀,
      ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  obtain ⟨c, hc, h⟩ := mem_nhdsLT_iff_exists_Ico_subset.mp
    (normalized_chord_close self_notMem_Iio h_deriv h_at hL hρ_pos)
  exact ⟨t₀ - c, sub_pos.mpr hc, fun t ht => h ⟨by linarith [ht.1], ht.2⟩⟩

/-- **Slit-plane condition for chord quotients.** If `‖z - 1‖ ≤ 1/4` and
`‖w - 1‖ ≤ 1/4`, then `z / w ∈ slitPlane` (specifically `Re(z/w) > 0`).

The proof uses `‖z/w - 1‖ = ‖z-w‖/‖w‖ ≤ (1/2)/(3/4) = 2/3 < 1`, giving
`Re(z/w) > 0` via `|Re(z/w) - 1| ≤ |z/w - 1| < 1`. -/
theorem div_mem_slitPlane_of_close_to_one {z w : ℂ}
    (hz : ‖z - 1‖ ≤ 1 / 4) (hw : ‖w - 1‖ ≤ 1 / 4) :
    z / w ∈ Complex.slitPlane := by
  have hw_ne : w ≠ 0 := fun hw_eq => by
    rw [hw_eq, zero_sub, norm_neg, norm_one] at hw; linarith
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
  · exact Or.inl <| by simpa using mul_pos hc h_re
  · exact Or.inr <| by simpa using mul_ne_zero hc.ne' h_im

/-- **Chord quotient in the slit plane (algebraic core).** If the normalized
chords at `a` and `b` are `1/4`-close to `1` and `a`, `b` lie on a common side
of `t₀` (so that `(b - t₀) / (a - t₀) > 0`), then
`(γ(b) - s) / (γ(a) - s) ∈ Complex.slitPlane`. -/
theorem chord_quotient_mem_slitPlane (hL : L ≠ 0) {a b : ℝ}
    (ha : ‖(γ a - s) / (L * ((a - t₀ : ℝ) : ℂ)) - 1‖ ≤ 1 / 4)
    (hb : ‖(γ b - s) / (L * ((b - t₀ : ℝ) : ℂ)) - 1‖ ≤ 1 / 4)
    (hab : 0 < (b - t₀) / (a - t₀)) :
    (γ b - s) / (γ a - s) ∈ Complex.slitPlane := by
  have ha_ne : (a - t₀ : ℝ) ≠ 0 := fun h => by simp [h] at hab
  have hb_ne : (b - t₀ : ℝ) ≠ 0 := fun h => by simp [h] at hab
  have hL_a : L * ((a - t₀ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hL (Complex.ofReal_ne_zero.mpr ha_ne)
  have hL_b : L * ((b - t₀ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hL (Complex.ofReal_ne_zero.mpr hb_ne)
  set z := (γ b - s) / (L * ((b - t₀ : ℝ) : ℂ)) with hz
  set w := (γ a - s) / (L * ((a - t₀ : ℝ) : ℂ)) with hw
  have h_ratio : (γ b - s) / (γ a - s) =
      (((b - t₀) / (a - t₀) : ℝ) : ℂ) * (z / w) := by
    rw [show (γ b - s) / (γ a - s) =
        (z * (L * ((b - t₀ : ℝ) : ℂ))) / (w * (L * ((a - t₀ : ℝ) : ℂ))) from by
      congr 1
      · simp only [z]; exact (div_mul_cancel₀ _ hL_b).symm
      · simp only [w]; exact (div_mul_cancel₀ _ hL_a).symm]
    push_cast; field_simp
  rw [h_ratio]
  exact ofReal_pos_mul_mem_slitPlane hab (div_mem_slitPlane_of_close_to_one hb ha)

/-- **Slit-plane on small right interval.** There exists `r > 0` such that for
all `a, b` with `t₀ < a ≤ b ≤ t₀ + r`, the chord quotient
`(γ(b) - s) / (γ(a) - s) ∈ Complex.slitPlane`. -/
theorem exists_slitPlane_chord_quotient_right
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_right h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun a b ha hab hb => ?_⟩
  exact chord_quotient_mem_slitPlane hL (hr_close a ⟨ha, by linarith⟩)
    (hr_close b ⟨by linarith, hb⟩) (div_pos (by linarith) (by linarith))

/-- **Slit-plane on small left interval (forward direction).** There exists
`r > 0` such that for all `a, b` with `t₀ - r ≤ a ≤ b < t₀`, the chord quotient
`(γ(b) - s) / (γ(a) - s) ∈ Complex.slitPlane`.

This is the FTC-relevant form: the FTC `segment_log_FTC` requires
`(γ(t) - s) / (γ(a) - s) ∈ slitPlane` for `t ∈ [a, b]` (where `a` is the left
endpoint). Here `b` is closer to `t₀`, so `γ(b) - s` is smaller in magnitude. -/
theorem exists_slitPlane_chord_quotient_left_forward
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_left h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun a b ha hab hb => ?_⟩
  exact chord_quotient_mem_slitPlane hL (hr_close a ⟨ha, by linarith⟩)
    (hr_close b ⟨by linarith, hb⟩)
    (div_pos_of_neg_of_neg (by linarith) (by linarith))

/-- **Positive real scaling does not move the argument**: if `Q ∈ slitPlane`,
`c ε > 0` eventually, and `(c ε : ℂ) * f ε → Q`, then `arg (f ε) → arg Q`. -/
theorem tendsto_arg_of_pos_smul_tendsto {l : Filter ℝ} {c : ℝ → ℝ} {f : ℝ → ℂ}
    {Q : ℂ} (hQ : Q ∈ Complex.slitPlane) (hc : ∀ᶠ ε in l, 0 < c ε)
    (h : Tendsto (fun ε => ((c ε : ℝ) : ℂ) * f ε) l (𝓝 Q)) :
    Tendsto (fun ε => (f ε).arg) l (𝓝 Q.arg) := by
  refine ((Complex.continuousAt_arg hQ).tendsto.comp h).congr' ?_
  filter_upwards [hc] with ε hε
  exact Complex.arg_real_mul _ hε

/-- **Right annular quotient arg convergence.** -/
theorem arg_right_annular_tendsto
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {δ_right : ℝ → ℝ} {r : ℝ}
    (h_γr_div_L : (γ (t₀ + r) - s) / L ∈ Complex.slitPlane)
    (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_right ε)
    (hδ_to_zero : Tendsto δ_right (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ))) :
    Tendsto (fun ε : ℝ =>
      Complex.arg ((γ (t₀ + r) - s) / (γ (t₀ + δ_right ε) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((γ (t₀ + r) - s) / L).arg) := by
  have h_compose : Tendsto (fun ε : ℝ => t₀ + δ_right ε)
      (𝓝[>] (0 : ℝ)) (𝓝[>] t₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, hδ_pos.mono fun ε hε => by simpa using hε⟩
    simpa using tendsto_const_nhds.add
      (hδ_to_zero.mono_right nhdsWithin_le_nhds : Tendsto δ_right (𝓝[>] (0 : ℝ)) (𝓝 0))
  have h_chord : Tendsto
      (fun ε : ℝ => (γ (t₀ + δ_right ε) - s) / ((δ_right ε : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    ((chord_div_t_tendsto self_notMem_Ioi h_deriv h_at).comp h_compose).congr
      fun ε => by simp [Function.comp_apply, add_sub_cancel_left]
  refine tendsto_arg_of_pos_smul_tendsto h_γr_div_L hδ_pos ?_
  have h_recip := (h_chord.inv₀ hL).const_mul (γ (t₀ + r) - s)
  rw [← div_eq_mul_inv] at h_recip
  exact h_recip.congr fun ε => by rw [inv_div]; ring

/-- **Left annular quotient arg convergence.** -/
theorem arg_left_annular_tendsto
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (_hL : L ≠ 0)
    {δ_left : ℝ → ℝ} {r : ℝ}
    (h_γnegr_div_L : (-L) / (γ (t₀ - r) - s) ∈ Complex.slitPlane)
    (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_left ε)
    (hδ_to_zero : Tendsto δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ))) :
    Tendsto (fun ε : ℝ =>
      Complex.arg ((γ (t₀ - δ_left ε) - s) / (γ (t₀ - r) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L) / (γ (t₀ - r) - s)).arg) := by
  have h_compose : Tendsto (fun ε : ℝ => t₀ - δ_left ε)
      (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, hδ_pos.mono fun ε hε => by simpa using hε⟩
    simpa using tendsto_const_nhds.sub
      (hδ_to_zero.mono_right nhdsWithin_le_nhds : Tendsto δ_left (𝓝[>] (0 : ℝ)) (𝓝 0))
  have h_chord : Tendsto
      (fun ε : ℝ => (γ (t₀ - δ_left ε) - s) / ((δ_left ε : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (-L)) :=
    ((chord_div_t_tendsto self_notMem_Iio h_deriv h_at).comp h_compose).neg.congr
      fun ε => by
        simp only [Function.comp_apply]
        rw [show t₀ - δ_left ε - t₀ = -δ_left ε from by ring, Complex.ofReal_neg,
          div_neg, neg_neg]
  refine tendsto_arg_of_pos_smul_tendsto h_γnegr_div_L
    (hδ_pos.mono fun ε hε => inv_pos.mpr hε) ?_
  refine (h_chord.div_const (γ (t₀ - r) - s)).congr fun ε => ?_
  push_cast
  ring

end HungerbuhlerWasem

end

end
