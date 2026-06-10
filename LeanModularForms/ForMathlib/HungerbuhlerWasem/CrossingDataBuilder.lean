/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import LeanModularForms.ForMathlib.PaperPwC1Immersion
public import LeanModularForms.ForMathlib.HungerbuhlerWasem.HigherOrderAsymptotics

/-!
# Local geometry of a `ClosedPwC1Immersion` near an interior parameter

This file provides the local geometric ingredients used to analyse a closed
piecewise-`C¹` immersion `γ` near a transverse crossing of a point `s` at a
parameter `t₀ ∈ Ioo 0 1`.

## Main results

1. **One-sided derivative limits** (`exists_left_deriv_limit`,
   `exists_right_deriv_limit`): at any interior `t₀`, the immersion has nonzero
   one-sided derivative limits.

2. **Eventual differentiability on each side** (`eventually_differentiable_left`,
   `eventually_differentiable_right`): `γ` is differentiable on a punctured
   one-sided neighbourhood of any interior `t₀`.

3. **Strict monotonicity of the distance to the crossed point**:

   * `norm_sub_strictMonoOn_right` — `‖γ(t) - s‖` is strictly increasing on
     `[t₀, t₀ + r]` for some `r > 0`;
   * `norm_sub_strictAntiOn_left` — `‖γ(t) - s‖` is strictly decreasing on
     `[t₀ - r, t₀]` for some `r > 0`.

   These follow from `HasDerivAt.norm_sq` and a chord-to-tangent positivity
   argument: `(d/dt)‖γ(t) - s‖² = 2 · ⟪γ(t) - s, γ'(t)⟫_ℝ`, whose leading term
   `(t - t₀) · ‖L‖²` dominates the `o(t - t₀)` corrections.

4. **Integrability away from the singularity**
   (`inv_sub_mul_deriv_intervalIntegrable`): if `γ(t) ≠ s` on `[a, b] ⊆ [0, 1]`,
   then `(γ(t) - s)⁻¹ * γ'(t)` is interval-integrable on `[a, b]`.

The strict-monotonicity lemmas let callers build excision cutoffs via IVT
inversion when they have additional symmetry information about the curve.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Real Interval

@[expose] public section

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

/-- At any `t₀ ∈ Ioo 0 1`, the right derivative limit `L_+` exists and is nonzero. -/
theorem exists_right_deriv_limit
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[>] t₀) (𝓝 L) := by
  by_cases h_part : t₀ ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
  · exact γ.toPwC1Immersion.right_deriv_limit t₀ h_part
  · refine ⟨deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀,
      γ.toPwC1Immersion.deriv_ne_zero t₀ ht₀ h_part,
      (γ.toPwC1Immersion.toPiecewiseC1Path.deriv_continuous_off_extend t₀ ht₀
        h_part).tendsto.mono_left nhdsWithin_le_nhds⟩

/-- At any `t₀ ∈ Ioo 0 1`, the left derivative limit `L_-` exists and is nonzero. -/
theorem exists_left_deriv_limit
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[<] t₀) (𝓝 L) := by
  by_cases h_part : t₀ ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
  · exact γ.toPwC1Immersion.left_deriv_limit t₀ h_part
  · refine ⟨deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀,
      γ.toPwC1Immersion.deriv_ne_zero t₀ ht₀ h_part,
      (γ.toPwC1Immersion.toPiecewiseC1Path.deriv_continuous_off_extend t₀ ht₀
        h_part).tendsto.mono_left nhdsWithin_le_nhds⟩

/-- Differentiability is eventual on `𝓝[u] t₀` (for any `u ∌ t₀`) for an
immersion at interior `t₀`. -/
theorem eventually_differentiable
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    {u : Set ℝ} (hu : t₀ ∉ u) :
    ∀ᶠ t in 𝓝[u] t₀,
      DifferentiableAt ℝ γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t := by
  have hcl : IsClosed
      ((↑γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ) \ {t₀}) :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.subset
      diff_subset).isClosed
  filter_upwards [
    nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (mem_compl fun h => h.2 rfl)),
    nhdsWithin_le_nhds (Ioo_mem_nhds ht₀.1 ht₀.2),
    self_mem_nhdsWithin] with t ht₁ ht₂ ht₃
  exact γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off_extend t ht₂
    fun hm => ht₁ ⟨hm, fun h => hu (h ▸ ht₃)⟩

/-- Differentiability is eventual on `𝓝[>] t₀` for an immersion at interior `t₀`. -/
theorem eventually_differentiable_right
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ t in 𝓝[>] t₀,
      DifferentiableAt ℝ γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t :=
  eventually_differentiable γ ht₀ self_notMem_Ioi

/-- Differentiability is eventual on `𝓝[<] t₀` for an immersion at interior `t₀`. -/
theorem eventually_differentiable_left
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ t in 𝓝[<] t₀,
      DifferentiableAt ℝ γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t :=
  eventually_differentiable γ ht₀ self_notMem_Iio

/-- **Two-sided inner-product expansion bound.** Near a one-sided derivative
limit `L`, the derivative of `‖γ(t) - s‖²` (up to the factor `2`) deviates from
its leading term `(t - t₀)·‖L‖²` by at most `|t - t₀|·‖L‖²/2`. Both one-sided
strict-monotonicity statements read off their sign from this single bound. -/
private theorem abs_inner_chord_deriv_sub_le
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s)
    {L : ℂ} (hL : L ≠ 0) {u : Set ℝ}
    (h_deriv : HasDerivWithinAt γ L u t₀)
    (hL_tendsto : Tendsto (deriv γ) (𝓝[u] t₀) (𝓝 L)) :
    ∀ᶠ t in 𝓝[u] t₀,
      |inner ℝ (γ t - s) (deriv γ t) - (t - t₀) * ‖L‖ ^ 2| ≤
        |t - t₀| * ‖L‖ ^ 2 / 2 := by
  have hr := hasDerivWithinAt_iff_isLittleO.mp h_deriv
  set η : ℝ := ‖L‖ / 8 with hη_def
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hη_pos : 0 < η := by rw [hη_def]; positivity
  have h_deriv_close : ∀ᶠ t in 𝓝[u] t₀, ‖deriv γ t - L‖ < η := by
    filter_upwards [(Metric.tendsto_nhds.mp hL_tendsto) η hη_pos] with t ht
    rwa [dist_eq_norm] at ht
  filter_upwards [hr.def hη_pos, h_deriv_close] with t h_chord_t h_dclose_t
  set R : ℂ := γ t - γ t₀ - (t - t₀) • L with hR_def
  set D : ℂ := deriv γ t - L with hD_def
  have hR_norm : ‖R‖ ≤ η * |t - t₀| := by rwa [Real.norm_eq_abs] at h_chord_t
  have hD_norm : ‖D‖ ≤ η := le_of_lt h_dclose_t
  have h_err_LD : |inner ℝ L D| ≤ ‖L‖ * η :=
    (abs_real_inner_le_norm L D).trans
      (mul_le_mul_of_nonneg_left hD_norm (norm_nonneg _))
  have h_err_RL : |inner ℝ R L| ≤ η * |t - t₀| * ‖L‖ :=
    (abs_real_inner_le_norm R L).trans
      (mul_le_mul_of_nonneg_right hR_norm (norm_nonneg _))
  have h_err_RD : |inner ℝ R D| ≤ η * |t - t₀| * η :=
    (abs_real_inner_le_norm R D).trans
      (mul_le_mul hR_norm hD_norm (norm_nonneg _) (by positivity))
  have h_err_tLD : |(t - t₀) * inner ℝ L D| ≤ |t - t₀| * (‖L‖ * η) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h_err_LD (abs_nonneg _)
  have h_expand : inner ℝ (γ t - s) (deriv γ t) - (t - t₀) * ‖L‖ ^ 2 =
      (t - t₀) * inner ℝ L D + inner ℝ R L + inner ℝ R D := by
    rw [show γ t - s = (t - t₀) • L + R by rw [hR_def, h_at]; ring,
      show deriv γ t = L + D by rw [hD_def]; ring,
      inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have h_eta_bound : 2 * η * ‖L‖ + η ^ 2 ≤ ‖L‖ ^ 2 / 2 := by
    rw [hη_def]; nlinarith [hL_pos]
  rw [h_expand]
  calc |(t - t₀) * inner ℝ L D + inner ℝ R L + inner ℝ R D|
      ≤ |(t - t₀) * inner ℝ L D| + |inner ℝ R L| + |inner ℝ R D| :=
        abs_add_three _ _ _
    _ ≤ |t - t₀| * (‖L‖ * η) + η * |t - t₀| * ‖L‖ + η * |t - t₀| * η := by
        gcongr
    _ ≤ |t - t₀| * ‖L‖ ^ 2 / 2 := by
        nlinarith [mul_le_mul_of_nonneg_left h_eta_bound (abs_nonneg (t - t₀))]

/-- **Strict monotonicity right side**: for some `r > 0`, the function
`t ↦ ‖γ(t) - s‖` is strictly monotone-increasing on `[t₀, t₀+r]`.

This is the key one-sided strict-monotonicity property used to define the
exit-time cutoff `δ(ε)` via IVT. -/
theorem norm_sub_strictMonoOn_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s)
    {L : ℂ} (hL : L ≠ 0)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t) :
    ∃ r > 0, StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + r)) := by
  have h_combined : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t ∧
      (t - t₀) * ‖L‖ ^ 2 / 2 ≤ inner ℝ (γ t - s) (deriv γ t) := by
    filter_upwards [hγ_diff,
      abs_inner_chord_deriv_sub_le h_at hL
        (hasDerivWithinAt_Ioi_of_tendsto hγ_cont hγ_diff hL_right) hL_right,
      self_mem_nhdsWithin] with t h_diff h_abs ht
    rw [abs_of_pos (show (0 : ℝ) < t - t₀ from sub_pos.mpr ht)] at h_abs
    exact ⟨h_diff, by linarith [(abs_le.mp h_abs).1]⟩
  obtain ⟨c, hc, hr_data⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp h_combined
  refine ⟨c - t₀, sub_pos.mpr hc, ?_⟩
  rw [show t₀ + (c - t₀) = c from by ring]
  set f : ℝ → ℝ := fun t => ‖γ t - s‖ ^ 2
  have h_γ_continuousOn : ContinuousOn γ (Icc t₀ c) := fun t ht => by
    rcases eq_or_lt_of_le ht.1 with h_eq | h_gt
    · rw [← h_eq]; exact hγ_cont.continuousWithinAt
    · exact (hr_data ⟨h_gt, ht.2⟩).1.continuousAt.continuousWithinAt
  have h_f_cont : ContinuousOn f (Icc t₀ c) := fun t ht =>
    (((h_γ_continuousOn t ht).sub continuousWithinAt_const).norm).pow 2
  have h_f_strictMono : StrictMonoOn f (Icc t₀ c) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (f' := fun t => 2 * inner ℝ (γ t - s) (deriv γ t)) h_f_cont
    · intro t ht
      rw [interior_Icc] at ht
      exact (((hr_data ⟨ht.1, ht.2.le⟩).1.hasDerivAt.sub_const
        s).norm_sq).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hL_sq_pos : 0 < ‖L‖ ^ 2 := by positivity
      linarith [(hr_data ⟨ht.1, ht.2.le⟩).2,
        mul_pos (sub_pos.mpr ht.1) hL_sq_pos]
  exact fun a ha b hb hab =>
    lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (h_f_strictMono ha hb hab)

/-- **Strict ANTI-monotonicity left side**: for some `r > 0`, the function
`t ↦ ‖γ(t) - s‖` is strictly anti-monotone (decreasing) on `[t₀ - r, t₀]`.

Symmetric to `norm_sub_strictMonoOn_right`. -/
theorem norm_sub_strictAntiOn_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s)
    {L : ℂ} (hL : L ≠ 0)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t) :
    ∃ r > 0, StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - r) t₀) := by
  have h_combined : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t ∧
      inner ℝ (γ t - s) (deriv γ t) ≤ (t - t₀) * ‖L‖ ^ 2 / 2 := by
    filter_upwards [hγ_diff,
      abs_inner_chord_deriv_sub_le h_at hL
        (hasDerivWithinAt_Iio_of_tendsto hγ_cont hγ_diff hL_left) hL_left,
      self_mem_nhdsWithin] with t h_diff h_abs ht
    rw [abs_of_neg (show t - t₀ < (0 : ℝ) from sub_neg.mpr ht)] at h_abs
    exact ⟨h_diff, by linarith [(abs_le.mp h_abs).2]⟩
  obtain ⟨c, hc, hr_data⟩ := mem_nhdsLT_iff_exists_Ico_subset.mp h_combined
  refine ⟨t₀ - c, sub_pos.mpr hc, ?_⟩
  rw [show t₀ - (t₀ - c) = c from by ring]
  set f : ℝ → ℝ := fun t => ‖γ t - s‖ ^ 2
  have h_γ_continuousOn : ContinuousOn γ (Icc c t₀) := fun t ht => by
    rcases eq_or_lt_of_le ht.2 with h_eq | h_lt
    · rw [h_eq]; exact hγ_cont.continuousWithinAt
    · exact (hr_data ⟨ht.1, h_lt⟩).1.continuousAt.continuousWithinAt
  have h_f_cont : ContinuousOn f (Icc c t₀) := fun t ht =>
    (((h_γ_continuousOn t ht).sub continuousWithinAt_const).norm).pow 2
  have h_f_strictAnti : StrictAntiOn f (Icc c t₀) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
      (f' := fun t => 2 * inner ℝ (γ t - s) (deriv γ t)) h_f_cont
    · intro t ht
      rw [interior_Icc] at ht
      exact (((hr_data ⟨ht.1.le, ht.2⟩).1.hasDerivAt.sub_const
        s).norm_sq).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hL_sq_pos : 0 < ‖L‖ ^ 2 := by positivity
      have h_neg_inner : (t - t₀) * ‖L‖ ^ 2 / 2 < 0 := by
        nlinarith [sub_neg_of_lt ht.2, hL_sq_pos]
      linarith [(hr_data ⟨ht.1.le, ht.2⟩).2]
  exact fun a ha b hb hab =>
    lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (h_f_strictAnti ha hb hab)

/-- **Integrability of `(γ - s)⁻¹ * γ'` on segments away from the
singularity**. If `γ(t) ≠ s` on the closed interval `[a, b] ⊆ [0, 1]`, then
the integrand `(γ(t) - s)⁻¹ * γ'(t)` is interval-integrable on `[a, b]`.

The proof: `γ'` is interval-integrable on `[0, 1]` (hence on `[a, b]` by
restriction), and `(γ - s)⁻¹` is continuous on `[a, b]` (since `γ - s ≠ 0`
on the compact interval). Their product is interval-integrable. -/
theorem inv_sub_mul_deriv_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {s : ℂ} {a b : ℝ}
    (hab : a ≤ b) (h_in_Icc : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1)
    (h_ne : ∀ t ∈ Set.Icc a b,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t ≠ s) :
    IntervalIntegrable
      (fun t => (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s)⁻¹ *
        deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t)
      MeasureTheory.volume a b := by
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
  have hγ_int : IntervalIntegrable (deriv γf) MeasureTheory.volume a b :=
    γ.toClosedPwC1Curve.deriv_extend_intervalIntegrable.mono_set <| by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le zero_le_one]; exact h_in_Icc
  have h_cont : ContinuousOn (fun t => (γf t - s)⁻¹) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    refine (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousOn.sub
      continuousOn_const).inv₀ fun t ht h_eq => h_ne t ht ?_
    linear_combination h_eq
  exact (hγ_int.mul_continuousOn h_cont).congr (fun t _ => by ring)

end HungerbuhlerWasem

end

end
