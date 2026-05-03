/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HW33ExitTimeWrapper

/-!
# Bridge: parametric symmetric-excision PV ↔ `HasCauchyPVOn`

This file provides infrastructure for bridging between the parametric
symmetric-excision PV form (used by `hw_theorem_3_3_odd_transverse_parametric`)
and the `HasCauchyPVOn` form used in the rest of the residue-theorem framework.

## Strategy

The single-pole `cpvIntegrandOn {s} f γ ε t` is `0` if `‖γ(t) - s‖ ≤ ε`,
else `f(γ(t)) · γ'(t)`. If for fixed `ε`, the set
`{t ∈ [0, 1] : ‖γ(t) - s‖ ≤ ε}` equals `[α, β]` (with
`0 ≤ α ≤ β ≤ 1`), then the cpvIntegrandOn integral on `[0, 1]`
equals `∫_0^α + ∫_β^1` (the symmetric-excision form).

Combined with the parametric Tendsto for the excision integral, this gives
`HasCauchyPVOn {s} f γ 0`.

This file provides the **pointwise step** of the bridge: identifying when
`cpvIntegrandOn {s}` equals the contour integrand or zero based on γ's
distance from `s`.

## Main results

* `cpvIntegrandOn_singleton_eq_contour_of_far`: `cpvIntegrandOn {s} f γ ε t`
  equals the contour integrand when `ε < ‖γ(t) - s‖`.

* `cpvIntegrandOn_singleton_eq_zero_of_close`: `cpvIntegrandOn {s} f γ ε t = 0`
  when `‖γ(t) - s‖ ≤ ε`.

* `cpvIntegrandOn_singleton_eq_indicator`: `cpvIntegrandOn {s} f γ ε t` equals
  `Set.indicator {t | ε < ‖γ(t) - s‖} (contourIntegrand f γ) t`.

These give the pointwise/measurable identification needed to bridge to
`HasCauchyPVOn`. The full integral splitting under a "shape" hypothesis
(set-equals-bracket form) builds on these.
-/

open Filter Topology MeasureTheory Set Complex
open scoped Classical Real Interval

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-- **CPV integrand for a singleton equals the contour integrand when γ is far
from `s`.** -/
theorem cpvIntegrandOn_singleton_eq_contour_of_far
    (γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε : ℝ}
    {t : ℝ} (h_far : ε < ‖γ.toPath.extend t - s‖) :
    cpvIntegrandOn {s} f γ.toPath.extend ε t =
      f (γ.toPath.extend t) * deriv γ.toPath.extend t := by
  apply cpvIntegrandOn_of_forall_gt
  intro s' hs'
  rw [Finset.mem_singleton] at hs'
  rw [hs']
  exact h_far

/-- **CPV integrand for a singleton is zero when γ is close to `s`.** -/
theorem cpvIntegrandOn_singleton_eq_zero_of_close
    (γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε : ℝ}
    {t : ℝ} (h_close : ‖γ.toPath.extend t - s‖ ≤ ε) :
    cpvIntegrandOn {s} f γ.toPath.extend ε t = 0 :=
  cpvIntegrandOn_of_exists_le ⟨s, Finset.mem_singleton_self s, h_close⟩

/-- **CPV integrand for a singleton as indicator.** Pointwise:

  `cpvIntegrandOn {s} f γ ε t = (Set.indicator A) (f(γ t) · γ'(t)) t`

where `A = {t | ε < ‖γ(t) - s‖}` is the "far from s" set. -/
theorem cpvIntegrandOn_singleton_eq_indicator
    (γ : PiecewiseC1Path x x) (s : ℂ) (f : ℂ → ℂ) (ε : ℝ) (t : ℝ) :
    cpvIntegrandOn {s} f γ.toPath.extend ε t =
      ({t | ε < ‖γ.toPath.extend t - s‖}.indicator
        (fun t => f (γ.toPath.extend t) * deriv γ.toPath.extend t)) t := by
  by_cases h : ε < ‖γ.toPath.extend t - s‖
  · have h_mem : t ∈ {t | ε < ‖γ.toPath.extend t - s‖} := h
    rw [Set.indicator_of_mem h_mem]
    exact cpvIntegrandOn_singleton_eq_contour_of_far γ h
  · have h_notmem : t ∉ {t | ε < ‖γ.toPath.extend t - s‖} := h
    rw [Set.indicator_of_notMem h_notmem]
    push Not at h
    exact cpvIntegrandOn_singleton_eq_zero_of_close γ h

/-! ## Integral splitting under the shape hypothesis -/

/-- **CPV integrand integral on `[0, α]` equals contour integrand integral**
when `ε < ‖γ(t) - s‖` on `(0, α)`. Boundary points are measure-zero, so the
equality is via Ioc → Ioo conversion. -/
theorem integral_cpvIntegrandOn_singleton_eq_contour_left
    (γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε α : ℝ}
    (hα : 0 ≤ α)
    (h_outside : ∀ t ∈ Ioo (0 : ℝ) α, ε < ‖γ.toPath.extend t - s‖) :
    ∫ t in (0 : ℝ)..α, cpvIntegrandOn {s} f γ.toPath.extend ε t =
      ∫ t in (0 : ℝ)..α, f (γ.toPath.extend t) * deriv γ.toPath.extend t := by
  rw [intervalIntegral.integral_of_le hα, intervalIntegral.integral_of_le hα,
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  exact cpvIntegrandOn_singleton_eq_contour_of_far γ (h_outside t ht)

/-- **CPV integrand integral on `[β, 1]` equals contour integrand integral**
when `ε < ‖γ(t) - s‖` on `(β, 1)`. -/
theorem integral_cpvIntegrandOn_singleton_eq_contour_right
    (γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε β : ℝ}
    (hβ : β ≤ 1)
    (h_outside : ∀ t ∈ Ioo β (1 : ℝ), ε < ‖γ.toPath.extend t - s‖) :
    ∫ t in β..(1 : ℝ), cpvIntegrandOn {s} f γ.toPath.extend ε t =
      ∫ t in β..(1 : ℝ), f (γ.toPath.extend t) * deriv γ.toPath.extend t := by
  rw [intervalIntegral.integral_of_le hβ, intervalIntegral.integral_of_le hβ,
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  exact cpvIntegrandOn_singleton_eq_contour_of_far γ (h_outside t ht)

/-- **CPV integrand integral on `[α, β]` is zero** when `‖γ(t) - s‖ ≤ ε` on
`(α, β)`. -/
theorem integral_cpvIntegrandOn_singleton_eq_zero_middle
    (γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε α β : ℝ}
    (h_le : α ≤ β)
    (h_inside : ∀ t ∈ Ioo α β, ‖γ.toPath.extend t - s‖ ≤ ε) :
    ∫ t in α..β, cpvIntegrandOn {s} f γ.toPath.extend ε t = 0 := by
  rw [intervalIntegral.integral_of_le h_le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [show (∫ t in Ioo α β, cpvIntegrandOn {s} f γ.toPath.extend ε t ∂volume) =
    ∫ t in Ioo α β, (0 : ℂ) ∂volume from by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
    exact fun t ht => cpvIntegrandOn_singleton_eq_zero_of_close γ (h_inside t ht)]
  simp

/-- **Full integral splitting (excision form).** Under the shape hypothesis on
`(0, α) ∪ (α, β) ∪ (β, 1)`, the cpvIntegrandOn integral on `[0, 1]` equals the
symmetric-excision integral. -/
theorem cpvIntegrandOn_singleton_integral_eq_excision
    (γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε : ℝ}
    {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) (h_le : α ≤ β)
    (h_outside_left : ∀ t ∈ Ioo (0 : ℝ) α, ε < ‖γ.toPath.extend t - s‖)
    (h_outside_right : ∀ t ∈ Ioo β (1 : ℝ), ε < ‖γ.toPath.extend t - s‖)
    (h_inside : ∀ t ∈ Ioo α β, ‖γ.toPath.extend t - s‖ ≤ ε)
    (h_int_full : IntervalIntegrable
      (fun t => cpvIntegrandOn {s} f γ.toPath.extend ε t) volume 0 1) :
    ∫ t in (0 : ℝ)..1, cpvIntegrandOn {s} f γ.toPath.extend ε t =
      (∫ t in (0 : ℝ)..α, f (γ.toPath.extend t) * deriv γ.toPath.extend t) +
      ∫ t in β..(1 : ℝ), f (γ.toPath.extend t) * deriv γ.toPath.extend t := by
  have h_split :
      ∫ t in (0 : ℝ)..1, cpvIntegrandOn {s} f γ.toPath.extend ε t =
      (∫ t in (0 : ℝ)..α, cpvIntegrandOn {s} f γ.toPath.extend ε t) +
      (∫ t in α..β, cpvIntegrandOn {s} f γ.toPath.extend ε t) +
      ∫ t in β..(1 : ℝ), cpvIntegrandOn {s} f γ.toPath.extend ε t := by
    have hα1 : α ≤ 1 := h_le.trans hβ
    have h0β : (0 : ℝ) ≤ β := hα.trans h_le
    have h_int_α : IntervalIntegrable
        (fun t => cpvIntegrandOn {s} f γ.toPath.extend ε t) volume 0 α := by
      apply h_int_full.mono_set
      rw [Set.uIcc_of_le hα, Set.uIcc_of_le (zero_le_one' ℝ)]
      exact Set.Icc_subset_Icc le_rfl hα1
    have h_int_β : IntervalIntegrable
        (fun t => cpvIntegrandOn {s} f γ.toPath.extend ε t) volume α β := by
      apply h_int_full.mono_set
      rw [Set.uIcc_of_le h_le, Set.uIcc_of_le (zero_le_one' ℝ)]
      exact Set.Icc_subset_Icc hα hβ
    have h_int_1 : IntervalIntegrable
        (fun t => cpvIntegrandOn {s} f γ.toPath.extend ε t) volume β 1 := by
      apply h_int_full.mono_set
      rw [Set.uIcc_of_le hβ, Set.uIcc_of_le (zero_le_one' ℝ)]
      exact Set.Icc_subset_Icc h0β le_rfl
    have h_int_αβ : IntervalIntegrable
        (fun t => cpvIntegrandOn {s} f γ.toPath.extend ε t) volume 0 β :=
      h_int_α.trans h_int_β
    rw [← intervalIntegral.integral_add_adjacent_intervals h_int_αβ h_int_1,
        ← intervalIntegral.integral_add_adjacent_intervals h_int_α h_int_β]
  rw [h_split,
      integral_cpvIntegrandOn_singleton_eq_contour_left γ hα h_outside_left,
      integral_cpvIntegrandOn_singleton_eq_zero_middle γ h_le h_inside,
      integral_cpvIntegrandOn_singleton_eq_contour_right γ hβ h_outside_right,
      add_zero]

/-! ## Bridge to `HasCauchyPVOn` -/

/-- **Bridge from parametric symmetric-excision PV to `HasCauchyPVOn`.**
Given functions `α, β : ℝ → ℝ` (the exit-time functions, e.g.,
`firstExitTimeLeft` and `firstExitTimeRight`) such that:

* `α ε ∈ [0, 1]`, `β ε ∈ [0, 1]`, `α ε ≤ β ε` for small `ε > 0`,
* on `(0, α ε)` and `(β ε, 1)`, γ is far from s (`ε < ‖γ - s‖`),
* on `(α ε, β ε)`, γ is close to s (`‖γ - s‖ ≤ ε`),
* the CPV integrand is interval-integrable for each ε,
* the symmetric-excision integral tends to `0`,

then `HasCauchyPVOn {s} f γ 0`. -/
theorem hasCauchyPVOn_singleton_of_excision_tendsto
    (γ : PiecewiseC1Path x x) (s : ℂ) (f : ℂ → ℂ)
    (α β : ℝ → ℝ)
    (h_shape : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ α ε ∧ β ε ≤ 1 ∧ α ε ≤ β ε ∧
      (∀ t ∈ Ioo (0 : ℝ) (α ε), ε < ‖γ.toPath.extend t - s‖) ∧
      (∀ t ∈ Ioo (β ε) (1 : ℝ), ε < ‖γ.toPath.extend t - s‖) ∧
      (∀ t ∈ Ioo (α ε) (β ε), ‖γ.toPath.extend t - s‖ ≤ ε))
    (h_int_full : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => cpvIntegrandOn {s} f γ.toPath.extend ε t) volume 0 1)
    (h_excision : Tendsto (fun ε =>
      (∫ t in (0 : ℝ)..(α ε), f (γ.toPath.extend t) * deriv γ.toPath.extend t) +
      ∫ t in (β ε)..(1 : ℝ), f (γ.toPath.extend t) * deriv γ.toPath.extend t)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    HasCauchyPVOn {s} f γ 0 := by
  refine h_excision.congr' ?_
  filter_upwards [h_shape, h_int_full] with ε ⟨ha, hb, hc, hd, he, hf⟩ h_int
  exact (cpvIntegrandOn_singleton_integral_eq_excision γ
    ha hb hc hd he hf h_int).symm

/-! ## Specialization to firstExitTimeLeft / firstExitTimeRight -/

/-- **Bridge using the canonical exit times.** Specializes
`hasCauchyPVOn_singleton_of_excision_tendsto` to `α = firstExitTimeLeft` and
`β = firstExitTimeRight`. -/
theorem hasCauchyPVOn_singleton_of_exitTime_excision
    (γ : PiecewiseC1Path x x) (s : ℂ) (f : ℂ → ℂ)
    {t₀ δMinus δPlus : ℝ}
    (h_shape : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε ∧
      firstExitTimeRight γ.toPath.extend t₀ δPlus s ε ≤ 1 ∧
      firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε ≤
        firstExitTimeRight γ.toPath.extend t₀ δPlus s ε ∧
      (∀ t ∈ Ioo (0 : ℝ) (firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε),
        ε < ‖γ.toPath.extend t - s‖) ∧
      (∀ t ∈ Ioo (firstExitTimeRight γ.toPath.extend t₀ δPlus s ε) (1 : ℝ),
        ε < ‖γ.toPath.extend t - s‖) ∧
      (∀ t ∈ Ioo (firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε)
        (firstExitTimeRight γ.toPath.extend t₀ δPlus s ε),
        ‖γ.toPath.extend t - s‖ ≤ ε))
    (h_int_full : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => cpvIntegrandOn {s} f γ.toPath.extend ε t) volume 0 1)
    (h_excision : Tendsto (fun ε =>
      (∫ t in (0 : ℝ)..(firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε),
        f (γ.toPath.extend t) * deriv γ.toPath.extend t) +
      ∫ t in (firstExitTimeRight γ.toPath.extend t₀ δPlus s ε)..(1 : ℝ),
        f (γ.toPath.extend t) * deriv γ.toPath.extend t)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    HasCauchyPVOn {s} f γ 0 :=
  hasCauchyPVOn_singleton_of_excision_tendsto γ s f
    (firstExitTimeLeft γ.toPath.extend t₀ δMinus s)
    (firstExitTimeRight γ.toPath.extend t₀ δPlus s)
    h_shape h_int_full h_excision

/-! ## Shape hypothesis from local strict monotonicity -/

/-- **Left-side shape from strict anti-monotonicity (γ continuous).** If γ is
continuous on `[t₀ - δMinus, t₀]` with `‖γ - s‖` strictly anti-monotone there,
and γ avoids `s` on `[0, t₀ - δMinus]` with margin `δ_avoid > 0`, then for
sufficiently small `ε > 0`:

* `0 ≤ firstExitTimeLeft γ t₀ δMinus s ε`,
* For `t ∈ Ioo 0 (firstExitTimeLeft γ t₀ δMinus s ε)`, `ε < ‖γ(t) - s‖`. -/
theorem shape_left_of_strictAntiOn
    {γ : ℝ → ℂ} {s : ℂ} {t₀ δMinus : ℝ}
    (h_t₀_minus_pos : 0 ≤ t₀ - δMinus)
    (hδMinus : 0 < δMinus)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - δMinus) t₀))
    (hγ_anti : StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - δMinus) t₀))
    {δ_avoid : ℝ} (h_avoid : ∀ t ∈ Icc (0 : ℝ) (t₀ - δMinus), δ_avoid ≤ ‖γ t - s‖)
    {ε : ℝ} (hε_lt_avoid : ε < δ_avoid)
    (hε_le_max : ε ≤ ‖γ (t₀ - δMinus) - s‖) :
    0 ≤ firstExitTimeLeft γ t₀ δMinus s ε ∧
    ∀ t ∈ Ioo (0 : ℝ) (firstExitTimeLeft γ t₀ δMinus s ε),
      ε < ‖γ t - s‖ := by
  have h_inIcc := firstExitTimeLeft_mem_Icc hδMinus.le hε_le_max
  refine ⟨h_t₀_minus_pos.trans h_inIcc.1, ?_⟩
  intro t ⟨ht_pos, ht_lt⟩
  by_cases h_outer : t ≤ t₀ - δMinus
  · calc ε < δ_avoid := hε_lt_avoid
      _ ≤ ‖γ t - s‖ := h_avoid t ⟨le_of_lt ht_pos, h_outer⟩
  · push Not at h_outer
    have ht_in_Icc : t ∈ Icc (t₀ - δMinus) t₀ :=
      ⟨le_of_lt h_outer, le_of_lt (lt_of_lt_of_le ht_lt h_inIcc.2)⟩
    have h_strict : ‖γ (firstExitTimeLeft γ t₀ δMinus s ε) - s‖ < ‖γ t - s‖ :=
      hγ_anti ht_in_Icc h_inIcc ht_lt
    linarith [ε_le_norm_at_firstExitTimeLeft hδMinus hγ_cont hε_le_max]

/-- **Right-side shape from strict monotonicity (γ continuous).** Symmetric of
`shape_left_of_strictAntiOn`: γ continuous on `[t₀, t₀ + δPlus]` with
`‖γ - s‖` strictly monotone there, plus avoidance margin on `[t₀ + δPlus, 1]`,
gives the right-side shape. -/
theorem shape_right_of_strictMonoOn
    {γ : ℝ → ℂ} {s : ℂ} {t₀ δPlus : ℝ}
    (h_t₀_plus_le : t₀ + δPlus ≤ 1)
    (hδPlus : 0 < δPlus)
    (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δPlus)))
    (hγ_mono : StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + δPlus)))
    {δ_avoid : ℝ} (h_avoid : ∀ t ∈ Icc (t₀ + δPlus) (1 : ℝ), δ_avoid ≤ ‖γ t - s‖)
    {ε : ℝ} (hε_lt_avoid : ε < δ_avoid)
    (hε_le_max : ε ≤ ‖γ (t₀ + δPlus) - s‖) :
    firstExitTimeRight γ t₀ δPlus s ε ≤ 1 ∧
    ∀ t ∈ Ioo (firstExitTimeRight γ t₀ δPlus s ε) (1 : ℝ),
      ε < ‖γ t - s‖ := by
  have h_inIcc := firstExitTimeRight_mem_Icc hδPlus.le hε_le_max
  refine ⟨h_inIcc.2.trans h_t₀_plus_le, ?_⟩
  intro t ⟨ht_lt, ht_lt_one⟩
  by_cases h_outer : t₀ + δPlus ≤ t
  · calc ε < δ_avoid := hε_lt_avoid
      _ ≤ ‖γ t - s‖ := h_avoid t ⟨h_outer, le_of_lt ht_lt_one⟩
  · push Not at h_outer
    have ht_in_Icc : t ∈ Icc t₀ (t₀ + δPlus) :=
      ⟨le_of_lt (lt_of_le_of_lt h_inIcc.1 ht_lt), le_of_lt h_outer⟩
    have h_strict : ‖γ (firstExitTimeRight γ t₀ δPlus s ε) - s‖ < ‖γ t - s‖ :=
      hγ_mono h_inIcc ht_in_Icc ht_lt
    linarith [ε_le_norm_at_firstExitTimeRight hδPlus hγ_cont hε_le_max]

end LeanModularForms

end
