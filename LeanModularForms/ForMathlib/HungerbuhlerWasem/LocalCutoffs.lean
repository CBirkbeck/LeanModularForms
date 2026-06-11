/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import LeanModularForms.ForMathlib.HungerbuhlerWasem.CPVExistenceMulti
public import LeanModularForms.ForMathlib.ExitTime

/-!
# Localized per-crossing window infrastructure for multi-crossing CPV

This file provides the per-crossing local machinery used by the multi-crossing
CPV theorems in `MultiCrossingCPV.lean`: slit-plane radii at the window
boundary, one-sided derivative setup, annular log-differences, and the
**shared window-splitting core** `perCrossing_window_splitting`.

## Setup

Throughout, `γ` is a closed piecewise-`C¹` immersion (with range avoidance
`x : ℂ`) crossing the pole `s : ℂ` at an interior parameter `t₀ ∈ (0, 1)`
which is the unique crossing on the window `[t₀ - r, t₀ + r] ⊆ [0, 1]`.
The local-uniqueness assumption comes from `multi_pole_local_uniqueness` in
`CPVExistenceMulti.lean` (applied with the common radius from
`multi_pole_common_radius`).

## Main results

* `perCrossing_window_splitting` — the shared split-annihilate skeleton: for
  any integrand `g` with integrable `ε`-cutoff, the cutoff integral over the
  window eventually equals the sum of the two *smooth* side integrals up to
  the exit times `firstExitTimeLeft/Right` (`ExitTime.lean`); the middle
  piece is annihilated by strict monotonicity of the distance profile near
  `t₀` and the side cutoffs are removed by the far bounds.
* `perCrossing_window_integral_tendsto_exact` — simple-pole per-window CPV
  convergence (T-BR-Y9c), via the log primitive; an instantiation of the
  core. (The higher-order instantiation is
  `perCrossing_higherOrder_window_integral_tendsto_corner` in
  `MultiCrossingCPV.lean`.)
* `multi_pole_smooth_complement_far_bound` — positive lower bound for
  `‖γ - s‖` on the complement of the crossing windows.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2 §3.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Real Interval

@[expose] public section

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

/-- **Right boundary slit-plane radius existence**: given a right one-sided
derivative limit `L ≠ 0`, there exists `r > 0` such that for every
`0 < r' ≤ r`, the boundary chord-to-tangent quotient
`(γ(t₀ + r') - s) / L ∈ Complex.slitPlane`.

The proof uses the normalized chord bound
`‖(γ(t₀ + r') - s) / (L · r') - 1‖ ≤ 1/4`, which yields
`Re((γ(t₀ + r') - s) / (L · r')) ≥ 3/4`. Multiplying by the positive real
`r'` (which preserves slit-plane membership) gives the desired result. -/
theorem exists_chord_div_endpoint_slitPlane_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Set.Ioi t₀) t₀)
    (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      (γ (t₀ + r') - s) / L ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_right h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun r' hr'_pos hr'_le => ?_⟩
  have h_in : (t₀ + r') ∈ Set.Ioc t₀ (t₀ + r) := ⟨by linarith, by linarith⟩
  have h_simp : (((t₀ + r') - t₀ : ℝ) : ℂ) = ((r' : ℝ) : ℂ) := by push_cast; ring
  have h_close : ‖(γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)) - 1‖ ≤ 1 / 4 := by
    rw [← h_simp]; exact hr_close (t₀ + r') h_in
  have h_re_close : (3 / 4 : ℝ) ≤
      ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))).re := by
    have h_abs_le :
        |((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)) - 1).re| ≤ 1 / 4 :=
      (Complex.abs_re_le_norm _).trans h_close
    have h_re_eq : ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)) - 1).re =
        ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))).re - 1 := by simp
    rw [h_re_eq] at h_abs_le
    linarith [(abs_le.mp h_abs_le).1]
  have hr'_C_ne : ((r' : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hr'_pos.ne'
  have h_div_eq : (γ (t₀ + r') - s) / L =
      ((r' : ℝ) : ℂ) * ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))) := by
    field_simp
  rw [h_div_eq, Complex.mem_slitPlane_iff]
  left
  have h_re_calc :
      (((r' : ℝ) : ℂ) * ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)))).re =
        r' * ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  rw [h_re_calc]
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < r' * (3 / 4))
    (mul_le_mul_of_nonneg_left h_re_close hr'_pos.le)

/-- **Left boundary slit-plane radius existence**: given a left one-sided
derivative limit `L ≠ 0`, there exists `r > 0` such that for every
`0 < r' ≤ r` with `γ(t₀ - r') ≠ s`, the negated boundary quotient
`-L / (γ(t₀ - r') - s) ∈ Complex.slitPlane`.

The `γ(t₀ - r') ≠ s` hypothesis is supplied by the caller (typically via
local uniqueness on the window). The proof uses `‖−q − 1‖ ≤ 1/4` where
`q = (γ(t₀ - r') - s) / (L · r')`, then deduces `‖q‖ ≥ 3/4`, then
`‖−1/q − 1‖ ≤ 1/3`, then `Re(−1/q) ≥ 2/3`, and finally multiplies by `1/r' > 0`. -/
theorem exists_chord_div_endpoint_slitPlane_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Set.Iio t₀) t₀)
    (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r → γ (t₀ - r') ≠ s →
      (-L) / (γ (t₀ - r') - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_left h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun r' hr'_pos hr'_le h_γ_ne => ?_⟩
  have h_in : (t₀ - r') ∈ Set.Ico (t₀ - r) t₀ :=
    ⟨by linarith, by linarith⟩
  have h_simp_in : (((t₀ - r') - t₀ : ℝ) : ℂ) = -((r' : ℝ) : ℂ) := by
    push_cast; ring
  have h_close : ‖(γ (t₀ - r') - s) / (L * -((r' : ℝ) : ℂ)) - 1‖ ≤ 1 / 4 := by
    rw [← h_simp_in]; exact hr_close (t₀ - r') h_in
  have hr'_C_ne : ((r' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr'_pos.ne'
  have h_γMinus_ne : γ (t₀ - r') - s ≠ 0 := sub_ne_zero.mpr h_γ_ne
  set q : ℂ := (γ (t₀ - r') - s) / (L * ((r' : ℝ) : ℂ)) with hq_def
  have hq_close : ‖-q - 1‖ ≤ 1 / 4 := by
    have h_eq : (γ (t₀ - r') - s) / (L * -((r' : ℝ) : ℂ)) = -q := by
      rw [hq_def, mul_neg, div_neg]
    rwa [h_eq] at h_close
  have hq_norm : 3 / 4 ≤ ‖q‖ := by
    have h_rev : ‖(-1 : ℂ)‖ - ‖q‖ ≤ ‖-1 - q‖ := norm_sub_norm_le _ _
    rw [norm_neg, norm_one, show (-1 : ℂ) - q = -(q + 1) from by ring,
      norm_neg, show q + 1 = -(-q - 1) from by ring, norm_neg] at h_rev
    linarith
  have hq_ne : q ≠ 0 := fun h_eq => by
    rw [h_eq, norm_zero] at hq_norm; linarith
  have h_neg_inv_q_close : ‖(-1 / q) - 1‖ ≤ 1 / 3 := by
    have h_eq : ((-1 : ℂ) / q) - 1 = -((1 + q) / q) := by field_simp; ring
    rw [h_eq, norm_neg, norm_div,
      show ‖(1 : ℂ) + q‖ = ‖-q - 1‖ from by
        rw [show (1 : ℂ) + q = -(-q - 1) from by ring, norm_neg],
      div_le_iff₀ (norm_pos_iff.mpr hq_ne)]
    calc ‖-q - 1‖ ≤ 1 / 4 := hq_close
      _ ≤ (1 / 3) * (3 / 4) := by norm_num
      _ ≤ (1 / 3) * ‖q‖ := mul_le_mul_of_nonneg_left hq_norm (by norm_num)
  have h_eq_target : (-L) / (γ (t₀ - r') - s) =
      (((1 / r' : ℝ)) : ℂ) * (-1 / q) := by
    rw [hq_def]; push_cast; field_simp
  rw [h_eq_target, Complex.mem_slitPlane_iff]
  left
  have h_re_calc :
      ((((1 / r' : ℝ)) : ℂ) * (-1 / q)).re = (1 / r') * (-1 / q).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  rw [h_re_calc]
  have h_abs_re_le : |(-1 / q - 1).re| ≤ 1 / 3 :=
    (Complex.abs_re_le_norm _).trans h_neg_inv_q_close
  have h_re_eq : (-1 / q - 1).re = (-1 / q).re - 1 := by simp
  rw [h_re_eq] at h_abs_re_le
  have h_inv_r_pos : 0 < 1 / r' := by positivity
  linarith [mul_le_mul_of_nonneg_left
    (show (2 / 3 : ℝ) ≤ (-1 / q).re by linarith [(abs_le.mp h_abs_re_le).1])
    h_inv_r_pos.le,
    show 0 < (1 / r') * (2 / 3 : ℝ) by positivity]

/-- **One-sided derivative limit setup at an interior crossing.** Extracts the
nonzero one-sided derivatives `L_R, L_L` and the corresponding
`HasDerivWithinAt` witnesses on `Ioi t₀, Iio t₀` from the immersion
infrastructure. This is the radius-independent substrate of the per-crossing
slit-plane radii. -/
theorem oneSided_deriv_setup
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ (L_R L_L : ℂ),
      L_R ≠ 0 ∧ L_L ≠ 0 ∧
      HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_R
        (Set.Ioi t₀) t₀ ∧
      HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_L
        (Set.Iio t₀) t₀ := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ)
  obtain ⟨L_R, hL_R_ne, hL_R_tendsto⟩ := exists_right_deriv_limit γ ht₀
  obtain ⟨L_L, hL_L_ne, hL_L_tendsto⟩ := exists_left_deriv_limit γ ht₀
  have hγf_cont : ContinuousAt γf t₀ :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousAt
  exact ⟨L_R, L_L, hL_R_ne, hL_L_ne,
    hasDerivWithinAt_Ioi_of_tendsto hγf_cont
      (eventually_differentiable_right γ ht₀) hL_R_tendsto,
    hasDerivWithinAt_Iio_of_tendsto hγf_cont
      (eventually_differentiable_left γ ht₀) hL_L_tendsto⟩

/-- **Annular log-difference on a crossing-free subinterval.** The directionless
core shared by `right_annular_log_diff_local` and `left_annular_log_diff_local`:
on any `[a, b] ⊆ [0, 1]` avoiding the pole (`γ ≠ s` throughout) and satisfying
the slit-plane chord condition, the integral of `(γ-s)⁻¹·γ'` equals the log of
the chord quotient. Both callers supply `a`, `b` and discharge `γ ≠ s` from
local uniqueness. -/
private theorem annular_log_diff_of_window
    (γ : ClosedPwC1Immersion x) {s : ℂ} {a b : ℝ} (hab : a ≤ b)
    (h_ab_in_unit : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1)
    (h_ne : ∀ t ∈ Set.Icc a b,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t ≠ s)
    (h_slit : ∀ t ∈ Set.Icc a b,
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈ Complex.slitPlane) :
    ∫ t in a..b,
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s)⁻¹ *
        deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t =
    Complex.log
      ((γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s)) := by
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  have ha_in_01 : a ∈ Set.Icc (0 : ℝ) 1 := h_ab_in_unit ⟨le_rfl, hab⟩
  have hb_in_01 : b ∈ Set.Icc (0 : ℝ) 1 := h_ab_in_unit ⟨hab, le_rfl⟩
  have ha_ne : γf a - s ≠ 0 := sub_ne_zero.mpr (h_ne a ⟨le_rfl, hab⟩)
  have hγ_cont : ContinuousOn γf (Set.Icc a b) :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousOn
  have hP_count : (↑γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ).Countable :=
    γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.countable
  have hγ_diff : ∀ t ∈ Set.Ioo a b \ ↑γ.toPwC1Immersion.toPiecewiseC1Path.partition,
      HasDerivAt γf (deriv γf t) t := fun t ht =>
    (γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off_extend t
      ⟨lt_of_le_of_lt ha_in_01.1 ht.1.1, lt_of_lt_of_le ht.1.2 hb_in_01.2⟩ ht.2).hasDerivAt
  have h_int : IntervalIntegrable
      (fun t => deriv γf t / (γf t - s)) MeasureTheory.volume a b :=
    ((inv_sub_mul_deriv_intervalIntegrable γ hab h_ab_in_unit h_ne).congr
      (fun t _ => by simp only [hγf_def]; ring))
  calc ∫ t in a..b, (γf t - s)⁻¹ * deriv γf t
      = ∫ t in a..b, deriv γf t / (γf t - s) :=
        intervalIntegral.integral_congr fun t _ => by rw [div_eq_mul_inv, mul_comm]
    _ = _ := segment_log_FTC hab hP_count hγ_cont hγ_diff ha_ne h_slit h_int

/-- **Local right annular log-difference**: for `t₀ < a ≤ t₀ + r`, the integral
on `[a, t₀ + r]` of `(γ-s)⁻¹·γ'` equals the log of the chord quotient.
Local-uniqueness version of `right_annular_log_diff`, stated at an arbitrary
inner endpoint `a` (in practice the right exit time). -/
private theorem right_annular_log_diff_local
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ r a : ℝ}
    (ha_gt : t₀ < a) (ha_le : a ≤ t₀ + r)
    (h_window_in_unit : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_slit_R : ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
        Complex.slitPlane)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∫ t in a..(t₀ + r),
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s)⁻¹ *
        deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t =
    Complex.log
      ((γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + r) - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s)) := by
  have hr_pos : 0 < r := by linarith
  have hwin_lo : 0 ≤ t₀ - r := (h_window_in_unit (Set.left_mem_Icc.mpr (by linarith))).1
  have hwin_hi : t₀ + r ≤ 1 := (h_window_in_unit (Set.right_mem_Icc.mpr (by linarith))).2
  refine annular_log_diff_of_window γ ha_le
    (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩) (fun t ht h_eq => ?_)
    (fun t ht => h_slit_R a t ha_gt ht.1 ht.2)
  have : t = t₀ := h_local_unique t ⟨by linarith [ht.1], by linarith [ht.2]⟩ h_eq
  linarith [ht.1]

/-- **Local left annular log-difference**: for `t₀ - r ≤ b < t₀`, the integral
on `[t₀ - r, b]` of `(γ-s)⁻¹·γ'` equals the log of the chord quotient.
Local-uniqueness version of `left_annular_log_diff`, stated at an arbitrary
inner endpoint `b` (in practice the left exit time). -/
private theorem left_annular_log_diff_local
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ r b : ℝ}
    (hb_ge : t₀ - r ≤ b) (hb_lt : b < t₀)
    (h_window_in_unit : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_slit_L : ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
        Complex.slitPlane)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∫ t in (t₀ - r)..b,
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s)⁻¹ *
        deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t =
    Complex.log
      ((γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - r) - s)) := by
  have hr_pos : 0 < r := by linarith
  have hwin_lo : 0 ≤ t₀ - r := (h_window_in_unit (Set.left_mem_Icc.mpr (by linarith))).1
  have hwin_hi : t₀ + r ≤ 1 := (h_window_in_unit (Set.right_mem_Icc.mpr (by linarith))).2
  refine annular_log_diff_of_window γ hb_ge
    (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩) (fun t ht h_eq => ?_)
    (fun t ht => h_slit_L (t₀ - r) t le_rfl ht.1 (by linarith [ht.2]))
  have : t = t₀ := h_local_unique t ⟨by linarith [ht.1], by linarith [ht.2]⟩ h_eq
  linarith [ht.2]

/-- **Simple-pole cutoff integrand bounded by `(1/ε) · ‖γ'‖`**, integrable on
`[a, b]`. -/
theorem cpvIntegrand_inv_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {s : ℂ} {a b : ℝ}
    {ε : ℝ} (hε_pos : 0 < ε)
    (hab : a ≤ b) (h_in_Icc : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable
      (fun t => cpvIntegrand (fun z => (z - s)⁻¹)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε t)
      MeasureTheory.volume a b := by
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
  have hγ_int : IntervalIntegrable (deriv γf) MeasureTheory.volume a b := by
    refine γ.toClosedPwC1Curve.deriv_extend_intervalIntegrable.mono_set ?_
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le zero_le_one]; exact h_in_Icc
  have h_sm_γf : Measurable γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.measurable
  have h_sm : Measurable
      (fun u => cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u) := by
    unfold cpvIntegrand
    exact Measurable.ite ((h_sm_γf.sub measurable_const).norm measurableSet_Ioi)
      ((h_sm_γf.sub measurable_const).inv.mul (measurable_deriv γf)) measurable_const
  have h_bd : ∀ u, ‖cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u‖ ≤
      (1 / ε) * ‖deriv γf u‖ := fun u => by
    simp only [cpvIntegrand]
    split_ifs with h_gt
    · rw [norm_mul, norm_inv, inv_eq_one_div]
      exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hε_pos h_gt.le)
        (norm_nonneg _)
    · simp only [norm_zero]; positivity
  exact IntervalIntegrable.mono_fun' ((hγ_int.norm).const_mul (1 / ε))
    h_sm.aestronglyMeasurable (Filter.Eventually.of_forall h_bd)

/-- **Shared window-splitting core.** For a closed pw-`C¹` immersion `γ`
crossing `s` at an interior parameter `t₀` (smooth or corner), with local
uniqueness on the window `[t₀ - r, t₀ + r] ⊆ [0, 1]`, there are exit-time
functions `τL, τR` (built from `firstExitTimeLeft/Right` at a
strict-monotonicity radius of the distance profile) with `τL ε → t₀⁻`,
`τR ε → t₀⁺` and exit radius exactly `ε`, such that — for every integrand `g`
whose `ε`-cutoff `cpvIntegrand g γ s ε` is interval-integrable — the window
cutoff integral eventually splits into the two *smooth* side integrals: the
middle piece `[τL ε, τR ε]` is annihilated by the near-bound (monotonicity up
to the exit radius), and on the side pieces the cutoff is the plain integrand
by the far-bounds (monotonicity inside the monotone radius,
`multi_pole_local_far_bound` beyond it).

Both `perCrossing_window_integral_tendsto_exact` (simple pole, log primitive)
and `perCrossing_higherOrder_window_integral_tendsto_corner` (order-`k` pole,
`antiderivPow` primitive, in `MultiCrossingCPV.lean`) instantiate this core
and add only the per-side FTC evaluation plus the limit of the coupled
exit-time term. -/
theorem perCrossing_window_splitting
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    {r : ℝ} (hr_pos : 0 < r)
    (h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (g : ℂ → ℂ)
    (h_int : ∀ ε : ℝ, 0 < ε → ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1 →
      IntervalIntegrable
        (cpvIntegrand g γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε)
        MeasureTheory.volume a b) :
    ∃ τL τR : ℝ → ℝ,
      Tendsto τL (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) ∧
      Tendsto τR (𝓝[>] (0 : ℝ)) (𝓝[>] t₀) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (τL ε) - s‖ = ε) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (τR ε) - s‖ = ε) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), τL ε ∈ Set.Ioo (t₀ - r) t₀) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), τR ε ∈ Set.Ioo t₀ (t₀ + r)) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∫ u in (t₀ - r)..(t₀ + r),
          cpvIntegrand g γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε u =
        (∫ u in (t₀ - r)..(τL ε),
          g (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend u) *
            deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend u) +
        (∫ u in (τR ε)..(t₀ + r),
          g (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend u) *
            deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend u)) := by
  classical
  set f : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hf_def
  have hf_cont : Continuous f :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  obtain ⟨L_R, hL_R_ne, hL_right⟩ := exists_right_deriv_limit γ ht₀
  obtain ⟨L_L, hL_L_ne, hL_left⟩ := exists_left_deriv_limit γ ht₀
  obtain ⟨r_R, hr_R_pos, hmono_raw⟩ :=
    norm_sub_strictMonoOn_right h_at hL_R_ne hL_right hf_cont.continuousAt
      (eventually_differentiable_right γ ht₀)
  obtain ⟨r_L, hr_L_pos, hanti_raw⟩ :=
    norm_sub_strictAntiOn_left h_at hL_L_ne hL_left hf_cont.continuousAt
      (eventually_differentiable_left γ ht₀)
  set ρ : ℝ := min r (min r_R r_L) / 2 with hρ_def
  have hρ_pos : 0 < ρ := half_pos (lt_min hr_pos (lt_min hr_R_pos hr_L_pos))
  have hρ_le : ρ ≤ min r (min r_R r_L) :=
    half_le_self (lt_min hr_pos (lt_min hr_R_pos hr_L_pos)).le
  have hρ_le_r : ρ ≤ r := hρ_le.trans (min_le_left _ _)
  have hmono : StrictMonoOn (fun t => ‖f t - s‖) (Set.Icc t₀ (t₀ + ρ)) :=
    hmono_raw.mono (Set.Icc_subset_Icc le_rfl
      (by linarith [hρ_le.trans ((min_le_right r _).trans (min_le_left r_R r_L))]))
  have hanti : StrictAntiOn (fun t => ‖f t - s‖) (Set.Icc (t₀ - ρ) t₀) :=
    hanti_raw.mono (Set.Icc_subset_Icc
      (by linarith [hρ_le.trans ((min_le_right r _).trans (min_le_right r_R r_L))]) le_rfl)
  have h_leave_right : ∀ t ∈ Set.Ioc t₀ (t₀ + ρ), f t ≠ s := fun t ht heq => by
    have h_strict : ‖f t₀ - s‖ < ‖f t - s‖ :=
      hmono ⟨le_rfl, by linarith⟩ ⟨ht.1.le, ht.2⟩ ht.1
    rw [h_at, heq] at h_strict; simp at h_strict
  have h_leave_left : ∀ t ∈ Set.Ico (t₀ - ρ) t₀, f t ≠ s := fun t ht heq => by
    have h_strict : ‖f t₀ - s‖ < ‖f t - s‖ :=
      hanti ⟨ht.1, ht.2.le⟩ ⟨by linarith, le_rfl⟩ ht.2
    rw [h_at, heq] at h_strict; simp at h_strict
  set τL : ℝ → ℝ := LeanModularForms.firstExitTimeLeft f t₀ ρ s with hτL_def
  set τR : ℝ → ℝ := LeanModularForms.firstExitTimeRight f t₀ ρ s with hτR_def
  have h_τL_to : Tendsto τL (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) :=
    LeanModularForms.firstExitTimeLeft_tendsto_t₀ hρ_pos hf_cont.continuousOn
      h_at h_leave_left
  have h_τR_to : Tendsto τR (𝓝[>] (0 : ℝ)) (𝓝[>] t₀) :=
    LeanModularForms.firstExitTimeRight_tendsto_t₀ hρ_pos hf_cont.continuousOn
      h_at h_leave_right
  have h_τL_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖f (τL ε) - s‖ = ε :=
    LeanModularForms.firstExitTimeLeft_radius_eventually hρ_pos hf_cont.continuousOn
      h_at h_leave_left
  have h_τR_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖f (τR ε) - s‖ = ε :=
    LeanModularForms.firstExitTimeRight_radius_eventually hρ_pos hf_cont.continuousOn
      h_at h_leave_right
  have h_τL_mem : ∀ᶠ ε in 𝓝[>] (0 : ℝ), τL ε ∈ Set.Ioo (t₀ - ρ) t₀ :=
    h_τL_to (Ioo_mem_nhdsLT (by linarith))
  have h_τR_mem : ∀ᶠ ε in 𝓝[>] (0 : ℝ), τR ε ∈ Set.Ioo t₀ (t₀ + ρ) :=
    h_τR_to (Ioo_mem_nhdsGT (by linarith))
  obtain ⟨m, hm_pos, h_far_left, h_far_right⟩ :=
    multi_pole_local_far_bound γ hr_pos h_local_unique hρ_pos hρ_le_r
  refine ⟨τL, τR, h_τL_to, h_τR_to, h_τL_radius, h_τR_radius,
    h_τL_mem.mono fun ε hε => ⟨by linarith [hε.1], hε.2⟩,
    h_τR_mem.mono fun ε hε => ⟨hε.1, by linarith [hε.2]⟩, ?_⟩
  filter_upwards [h_τL_radius, h_τR_radius, h_τL_mem, h_τR_mem,
    Ioo_mem_nhdsGT hm_pos] with ε hεL hεR hτL hτR hεm
  have hε_pos : 0 < ε := hεm.1
  have h_lb : t₀ - r ≤ τL ε := by linarith [hτL.1]
  have h_mid_le : τL ε ≤ τR ε := by linarith [hτL.2, hτR.1]
  have h_ub : τR ε ≤ t₀ + r := by linarith [hτR.2]
  have h_sub : ∀ {a b : ℝ}, t₀ - r ≤ a → b ≤ t₀ + r →
      Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1 := fun ha hb u hu =>
    h_window_Icc ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h_int_left := h_int ε hε_pos (t₀ - r) (τL ε) h_lb
    (h_sub le_rfl (by linarith [hτL.2]))
  have h_int_mid := h_int ε hε_pos (τL ε) (τR ε) h_mid_le (h_sub h_lb h_ub)
  have h_int_right := h_int ε hε_pos (τR ε) (t₀ + r) h_ub
    (h_sub (h_lb.trans h_mid_le) le_rfl)
  have h_mid_zero : ∫ u in (τL ε)..(τR ε), cpvIntegrand g f s ε u = 0 := by
    have h_norm_le : ∀ u ∈ Set.Ioo (τL ε) (τR ε), ‖f u - s‖ ≤ ε := fun u hu => by
      rcases lt_trichotomy u t₀ with h_lt | h_eq | h_gt
      · have h_bd : ‖f u - s‖ < ‖f (τL ε) - s‖ :=
          hanti ⟨hτL.1.le, hτL.2.le⟩ ⟨by linarith [hτL.1, hu.1], h_lt.le⟩ hu.1
        rw [hεL] at h_bd; exact h_bd.le
      · rw [h_eq, h_at, sub_self, norm_zero]; exact hε_pos.le
      · have h_bd : ‖f u - s‖ < ‖f (τR ε) - s‖ :=
          hmono ⟨h_gt.le, by linarith [hτR.2, hu.2]⟩ ⟨hτR.1.le, hτR.2.le⟩ hu.2
        rw [hεR] at h_bd; exact h_bd.le
    have h_eq0 : (fun u => cpvIntegrand g f s ε u) =ᶠ[MeasureTheory.ae
        (MeasureTheory.volume.restrict (Set.uIoc (τL ε) (τR ε)))] (fun _ => 0) := by
      rw [Set.uIoc_of_le h_mid_le]
      have h_compl : ({τR ε}ᶜ : Set ℝ) ∈ MeasureTheory.ae
          (MeasureTheory.volume.restrict (Set.Ioc (τL ε) (τR ε))) := by
        refine MeasureTheory.compl_mem_ae_iff.mpr ?_
        rw [MeasureTheory.Measure.restrict_apply (measurableSet_singleton _)]
        exact MeasureTheory.measure_mono_null Set.inter_subset_left
          (MeasureTheory.measure_singleton _)
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc, h_compl]
        with u hu hu_ne
      simp only [cpvIntegrand,
        if_neg (h_norm_le u ⟨hu.1, lt_of_le_of_ne hu.2 hu_ne⟩).not_gt]
    simpa using intervalIntegral.integral_congr_ae_restrict h_eq0
  have h_left_eq : ∫ u in (t₀ - r)..(τL ε), cpvIntegrand g f s ε u =
      ∫ u in (t₀ - r)..(τL ε), g (f u) * deriv f u := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le h_lb]
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
      (MeasureTheory.measure_singleton (τL ε))] with u hu_ne hu
    have h_u_lt : u < τL ε := lt_of_le_of_ne hu.2 hu_ne
    refine cpvIntegrand_of_gt ?_
    rcases lt_or_ge u (t₀ - ρ) with h_lt | h_ge
    · exact lt_of_lt_of_le hεm.2 (h_far_left u ⟨hu.1.le, h_lt.le⟩)
    · have h_bd : ‖f (τL ε) - s‖ < ‖f u - s‖ :=
        hanti ⟨h_ge, by linarith [hτL.2, h_u_lt]⟩ ⟨hτL.1.le, hτL.2.le⟩ h_u_lt
      rwa [hεL] at h_bd
  have h_right_eq : ∫ u in (τR ε)..(t₀ + r), cpvIntegrand g f s ε u =
      ∫ u in (τR ε)..(t₀ + r), g (f u) * deriv f u := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le h_ub]
    filter_upwards with u hu
    refine cpvIntegrand_of_gt ?_
    rcases le_or_gt u (t₀ + ρ) with h_le | h_gt
    · have h_bd : ‖f (τR ε) - s‖ < ‖f u - s‖ :=
        hmono ⟨hτR.1.le, hτR.2.le⟩ ⟨by linarith [hτR.1, hu.1], h_le⟩ hu.1
      rwa [hεR] at h_bd
    · exact lt_of_lt_of_le hεm.2 (h_far_right u ⟨h_gt.le, hu.2⟩)
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (h_int_left.trans h_int_mid) h_int_right,
    ← intervalIntegral.integral_add_adjacent_intervals h_int_left h_int_mid,
    h_mid_zero, add_zero, h_left_eq, h_right_eq]

/-- **Real/imaginary decomposition of `Complex.log (a / b)`** for nonzero `a`, `b`:
the real part is `log ‖a‖ - log ‖b‖` and the imaginary part is `arg (a / b)`. -/
private lemma log_div_re_im_decomp {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Complex.log (a / b) =
      ((Real.log ‖a‖ - Real.log ‖b‖ : ℝ) : ℂ) + ((a / b).arg : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, Complex.ofReal_im, sub_zero, add_zero]
    rw [Complex.log_re, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb)]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_one, Complex.ofReal_re, zero_add]
    rw [Complex.log_im]; ring

/-- **Per-window cutoff integral converges, exact-radius form** (T-BR-Y9c).

Takes the window radius `r` and all slit-plane chord-quotient/boundary data as
INPUTS rather than deriving them internally (which would shrink `r`). This
unblocks multi-crossing aggregation: each crossing supplies its threshold
radius `r_i`, the caller takes `r = min_i r_i`, and every crossing's window
uses the SAME fixed radius `r`.

The caller is responsible for ensuring the slit-plane bounds hold at the
chosen `r`. The companion theorems
`exists_slitPlane_chord_quotient_right/_left_forward` and
`exists_chord_div_endpoint_slitPlane_right/left` produce per-crossing
threshold radii.

Instantiates `perCrossing_window_splitting` with the simple-pole integrand:
the side integrals are log chord quotients (`*_annular_log_diff_local`),
whose `log ε` real parts cancel across the two sides while the argument
parts converge by `arg_right/left_annular_tendsto`. -/
theorem perCrossing_window_integral_tendsto_exact
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    {r : ℝ} (hr_pos : 0 < r)
    (h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_local_unique_r : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    {L_R L_L : ℂ} (hL_R_ne : L_R ≠ 0) (hL_L_ne : L_L ≠ 0)
    (h_deriv_right : HasDerivWithinAt
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_R (Set.Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_L (Set.Iio t₀) t₀)
    (h_slit_R : ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
          Complex.slitPlane)
    (h_slit_L : ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
          Complex.slitPlane)
    (h_γPlus_div_LR :
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + r) - s) / L_R ∈
        Complex.slitPlane)
    (h_LL_neg_div_γMinus :
      (-L_L) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - r) - s) ∈
        Complex.slitPlane) :
    ∃ L_i : ℂ,
      Tendsto (fun ε : ℝ =>
        ∫ t in (t₀ - r)..(t₀ + r),
          cpvIntegrand (fun z => (z - s)⁻¹)
            γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε t)
        (𝓝[>] (0 : ℝ)) (𝓝 L_i) := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  obtain ⟨τL, τR, h_τL_to, h_τR_to, h_τL_radius, h_τR_radius, h_τL_mem, h_τR_mem,
      h_split⟩ :=
    perCrossing_window_splitting γ ht₀ h_at hr_pos h_window_Icc h_local_unique_r
      (fun z => (z - s)⁻¹)
      (fun ε hε_pos a b hab h_in =>
        cpvIntegrand_inv_intervalIntegrable γ hε_pos hab h_in)
  have hδR_pos_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < τR ε - t₀ :=
    h_τR_mem.mono fun ε hε => by linarith [hε.1]
  have hδL_pos_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t₀ - τL ε :=
    h_τL_mem.mono fun ε hε => by linarith [hε.2]
  have hδR_to : Tendsto (fun ε => τR ε - t₀) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using (h_τR_to.mono_right nhdsWithin_le_nhds).sub_const t₀,
      hδR_pos_ev.mono fun ε hε => Set.mem_Ioi.mpr hε⟩
  have hδL_to : Tendsto (fun ε => t₀ - τL ε) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using (h_τL_to.mono_right nhdsWithin_le_nhds).const_sub t₀,
      hδL_pos_ev.mono fun ε hε => Set.mem_Ioi.mpr hε⟩
  have h_arg_R_clean : Tendsto (fun ε : ℝ =>
      Complex.arg ((γf (t₀ + r) - s) / (γf (τR ε) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((γf (t₀ + r) - s) / L_R).arg) :=
    (arg_right_annular_tendsto h_deriv_right h_at hL_R_ne h_γPlus_div_LR
      hδR_pos_ev hδR_to).congr fun ε => by
        rw [show t₀ + (τR ε - t₀) = τR ε by ring]
  have h_arg_L_clean : Tendsto (fun ε : ℝ =>
      Complex.arg ((γf (τL ε) - s) / (γf (t₀ - r) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L_L) / (γf (t₀ - r) - s)).arg) :=
    (arg_left_annular_tendsto h_deriv_left h_at hL_L_ne h_LL_neg_div_γMinus
      hδL_pos_ev hδL_to).congr fun ε => by
        rw [show t₀ - (t₀ - τL ε) = τL ε by ring]
  set argR_lim : ℝ := ((γf (t₀ + r) - s) / L_R).arg with hargR_def
  set argL_lim : ℝ := ((-L_L) / (γf (t₀ - r) - s)).arg with hargL_def
  set logNorm_diff : ℝ :=
    Real.log ‖γf (t₀ + r) - s‖ - Real.log ‖γf (t₀ - r) - s‖ with hlogND_def
  set Λ_L : ℝ → ℂ := fun ε =>
    Complex.log ((γf (τL ε) - s) / (γf (t₀ - r) - s)) with hΛL_def
  set Λ_R : ℝ → ℂ := fun ε =>
    Complex.log ((γf (t₀ + r) - s) / (γf (τR ε) - s)) with hΛR_def
  refine ⟨((logNorm_diff : ℝ) : ℂ) +
    (((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I), ?_⟩
  have h_eventually_eq : (fun ε : ℝ => ∫ t in (t₀ - r)..(t₀ + r),
      cpvIntegrand (fun z => (z - s)⁻¹) γf s ε t) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => Λ_L ε + Λ_R ε) := by
    filter_upwards [h_split, h_τL_mem, h_τR_mem] with ε hsplit hτL hτR
    rw [hsplit,
      left_annular_log_diff_local γ hτL.1.le hτL.2 h_window_Icc h_slit_L
        h_local_unique_r,
      right_annular_log_diff_local γ hτR.1 hτR.2.le h_window_Icc h_slit_R
        h_local_unique_r]
  refine Tendsto.congr' h_eventually_eq.symm ?_
  have h_decomp : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Λ_L ε + Λ_R ε = ((logNorm_diff : ℝ) : ℂ) +
        ((((γf (τL ε) - s) / (γf (t₀ - r) - s)).arg +
          ((γf (t₀ + r) - s) / (γf (τR ε) - s)).arg : ℝ) : ℂ) * Complex.I := by
    filter_upwards [h_τL_radius, h_τR_radius, self_mem_nhdsWithin]
      with ε h_eq_L h_eq_R hε_mem
    have hε_pos : 0 < ε := hε_mem
    have h_γPlus_ne : γf (t₀ + r) - s ≠ 0 := fun h_eq =>
      absurd (h_local_unique_r _ (Set.right_mem_Icc.mpr (by linarith))
        (sub_eq_zero.mp h_eq)) (by linarith)
    have h_γMinus_ne : γf (t₀ - r) - s ≠ 0 := fun h_eq =>
      absurd (h_local_unique_r _ (Set.left_mem_Icc.mpr (by linarith))
        (sub_eq_zero.mp h_eq)) (by linarith)
    have h_γR_ne : γf (τR ε) - s ≠ 0 := by
      rw [← norm_pos_iff, h_eq_R]; exact hε_pos
    have h_γL_ne : γf (τL ε) - s ≠ 0 := by
      rw [← norm_pos_iff, h_eq_L]; exact hε_pos
    have h_log_R_decomp : Λ_R ε =
        ((Real.log ‖γf (t₀ + r) - s‖ - Real.log ‖γf (τR ε) - s‖ : ℝ) : ℂ) +
        (((γf (t₀ + r) - s) / (γf (τR ε) - s)).arg : ℂ) * Complex.I :=
      log_div_re_im_decomp h_γPlus_ne h_γR_ne
    have h_log_L_decomp : Λ_L ε =
        ((Real.log ‖γf (τL ε) - s‖ - Real.log ‖γf (t₀ - r) - s‖ : ℝ) : ℂ) +
        (((γf (τL ε) - s) / (γf (t₀ - r) - s)).arg : ℂ) * Complex.I :=
      log_div_re_im_decomp h_γL_ne h_γMinus_ne
    rw [h_log_L_decomp, h_log_R_decomp, h_eq_R, h_eq_L]
    simp only [hlogND_def]; push_cast; ring
  have h_decomp' : (fun ε : ℝ => ((logNorm_diff : ℝ) : ℂ) +
      ((((γf (τL ε) - s) / (γf (t₀ - r) - s)).arg +
        ((γf (t₀ + r) - s) / (γf (τR ε) - s)).arg : ℝ) : ℂ) *
          Complex.I) =ᶠ[𝓝[>] (0 : ℝ)] (fun ε => Λ_L ε + Λ_R ε) :=
    h_decomp.mono fun ε hε => hε.symm
  refine Tendsto.congr' h_decomp' (tendsto_const_nhds.add ?_)
  have h_arg_sum : Tendsto (fun ε : ℝ =>
      ((γf (τL ε) - s) / (γf (t₀ - r) - s)).arg +
        ((γf (t₀ + r) - s) / (γf (τR ε) - s)).arg)
      (𝓝[>] (0 : ℝ)) (𝓝 (argL_lim + argR_lim)) := by
    simpa [hargL_def, hargR_def] using h_arg_L_clean.add h_arg_R_clean
  have h_target_eq : ((argL_lim + argR_lim : ℝ) : ℂ) * Complex.I =
      ((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [← h_target_eq]
  exact ((Complex.continuous_ofReal.tendsto _).comp h_arg_sum).mul tendsto_const_nhds

/-- **Smooth complement positive bound** for a multi-crossing setup.

Given a finite set of crossings `crossings : Finset ℝ` (each in `Icc 0 1`,
with `γ(t) = s` only when `t ∈ crossings`), and a common radius function
`r_at : crossings → ℝ` with each `r_at t_i > 0`, the function `t ↦ ‖γ(t) - s‖`
has a positive minimum on the **closed complement** `[0, 1] \ ⋃_i (t_i - r_at t_i,
t_i + r_at t_i)`. -/
theorem multi_pole_smooth_complement_far_bound
    (γ : ClosedPwC1Immersion x) {s : ℂ}
    {crossings : Finset ℝ}
    (h_complete : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t ∈ crossings)
    (r_at : ℝ → ℝ) (hr_at_pos : ∀ t ∈ crossings, 0 < r_at t) :
    ∃ m : ℝ, 0 < m ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (∀ t_i ∈ crossings, t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)) →
        m ≤ ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ := by
  classical
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
  have hγ_cont : Continuous γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  set C : Set ℝ := {t ∈ Set.Icc (0 : ℝ) 1 |
    ∀ t_i ∈ crossings, t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)} with hC_def
  have hC_subset : C ⊆ Set.Icc (0 : ℝ) 1 := fun t ht => ht.1
  have hC_closed : IsClosed C := by
    have h2 : IsClosed ({t : ℝ | ∀ t_i ∈ crossings,
        t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)}) := by
      have h_eq : {t : ℝ | ∀ t_i ∈ crossings,
            t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)} =
          ⋂ t_i ∈ crossings, (Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i))ᶜ := by
        ext t; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
      rw [h_eq]
      exact isClosed_biInter fun _ _ => isOpen_Ioo.isClosed_compl
    have hC_eq : C = Set.Icc (0 : ℝ) 1 ∩
        {t : ℝ | ∀ t_i ∈ crossings,
          t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)} := by
      ext t; simp only [hC_def, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [hC_eq]
    exact isClosed_Icc.inter h2
  have hC_compact : IsCompact C :=
    isCompact_Icc.of_isClosed_subset hC_closed hC_subset
  by_cases hC_empty : C = ∅
  · exact ⟨1, one_pos, fun t ht h_avoid => by
      have : t ∈ C := ⟨ht, h_avoid⟩
      rw [hC_empty] at this; exact absurd this (Set.notMem_empty t)⟩
  · have h_norm_cont : ContinuousOn (fun t => ‖γf t - s‖) C :=
      (hγ_cont.continuousOn.sub continuousOn_const).norm
    obtain ⟨t_min, ht_min_mem, ht_min⟩ := hC_compact.exists_isMinOn
      (Set.nonempty_iff_ne_empty.mpr hC_empty) h_norm_cont
    refine ⟨‖γf t_min - s‖, ?_, fun t ht h_avoid => ht_min ⟨ht, h_avoid⟩⟩
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h_eq => ?_)
    have h_t_min_in_crossings : t_min ∈ crossings :=
      h_complete t_min (hC_subset ht_min_mem) h_eq
    exact ht_min_mem.2 t_min h_t_min_in_crossings
      ⟨by linarith [hr_at_pos t_min h_t_min_in_crossings],
       by linarith [hr_at_pos t_min h_t_min_in_crossings]⟩

end HungerbuhlerWasem

end

end
