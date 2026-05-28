/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.ExitTime
import LeanModularForms.ForMathlib.CauchyPrincipalValue
import LeanModularForms.ForMathlib.MultipointPV

/-!
# Excision / bridge chain (T-SC-00b)

This file restores the shape lemmas and the excision-based bridge from the
parametric symmetric-excision PV form to the `HasCauchyPVOn` form, used by
the sector cancellation argument in T-SC-01.

The deleted sources are:
* `HW33Bridge.lean` (305 lines at git ref `07809ad^`) — bridge from parametric
  excision to `HasCauchyPVOn` plus shape lemmas.
* `HW33Final.lean` (lines 35-170 at git ref `07809ad^`) — eventual-shape forms
  ready for the bridge. The fully assembled theorem
  `hasCauchyPVOn_singleton_pow_of_transverse_assembled` is intentionally
  *not* restored here — it lives in T-SC-01.

## Strategy

The single-pole `cpvIntegrandOn {s} f γ ε t` is `0` if `‖γ(t) - s‖ ≤ ε`,
else `f(γ(t)) · γ'(t)`. If for fixed `ε`, the set
`{t ∈ [0, 1] : ‖γ(t) - s‖ ≤ ε}` equals `[α, β]` (with
`0 ≤ α ≤ β ≤ 1`), then the cpvIntegrandOn integral on `[0, 1]`
equals `∫_0^α + ∫_β^1` (the symmetric-excision form).

Combined with the parametric Tendsto for the excision integral, this gives
`HasCauchyPVOn {s} f γ 0`.

## Headline theorems

* `shape_right_of_strictMonoOn` — for γ strictly monotone on `(t₀, b)`, the
  curve image is in one half-plane.
* `shape_left_of_strictAntiOn` — mirror form on the left.
* `shape_right_eventually` — eventual right-side shape from strict mono.
* `shape_left_eventually` — eventual left-side shape.
* `shape_eventually_of_strict_mono` — combines the previous two.
* `hasCauchyPVOn_singleton_of_excision_tendsto` — CPV equals the limit of
  excised integrals.
* `hasCauchyPVOn_singleton_of_exitTime_excision` — CPV via exit-time excision.
* `cpvIntegrandOn_singleton_integral_eq_excision` — the `cpvIntegrandOn`-
  singleton integral equals the excised line integral.
-/

open Filter Topology Set Complex MeasureTheory
open scoped Classical Real Interval

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

/-! ## Pointwise CPV-integrand identification -/

/-- The CPV integrand for a singleton equals the contour integrand when `γ` is far
from `s`. -/
theorem cpvIntegrandOn_singleton_eq_contour_of_far
    (γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε : ℝ}
    {t : ℝ} (h_far : ε < ‖γ.toPath.extend t - s‖) :
    cpvIntegrandOn {s} f γ.toPath.extend ε t =
      f (γ.toPath.extend t) * deriv γ.toPath.extend t :=
  cpvIntegrandOn_of_forall_gt fun s' hs' ↦ by
    rw [Finset.mem_singleton.mp hs']
    exact h_far

/-- The CPV integrand for a singleton is zero when `γ` is close to `s`. -/
theorem cpvIntegrandOn_singleton_eq_zero_of_close
    (γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε : ℝ}
    {t : ℝ} (h_close : ‖γ.toPath.extend t - s‖ ≤ ε) :
    cpvIntegrandOn {s} f γ.toPath.extend ε t = 0 :=
  cpvIntegrandOn_of_exists_le ⟨s, Finset.mem_singleton_self s, h_close⟩

/-- The CPV integrand for a singleton equals the indicator of the "far from `s`" set
applied to the contour integrand: pointwise,
`cpvIntegrandOn {s} f γ ε t = ({t | ε < ‖γ(t) - s‖}).indicator (f(γ t) · γ'(t)) t`. -/
theorem cpvIntegrandOn_singleton_eq_indicator
    (γ : PiecewiseC1Path x x) (s : ℂ) (f : ℂ → ℂ) (ε : ℝ) (t : ℝ) :
    cpvIntegrandOn {s} f γ.toPath.extend ε t =
      ({t | ε < ‖γ.toPath.extend t - s‖}.indicator
        (fun t ↦ f (γ.toPath.extend t) * deriv γ.toPath.extend t)) t := by
  by_cases h : ε < ‖γ.toPath.extend t - s‖
  · rw [Set.indicator_of_mem (h : t ∈ _)]
    exact cpvIntegrandOn_singleton_eq_contour_of_far γ h
  · rw [Set.indicator_of_notMem (h : t ∉ _)]
    push Not at h
    exact cpvIntegrandOn_singleton_eq_zero_of_close γ h

/-! ## Integral splitting under the shape hypothesis -/

/-- The CPV integrand integral on `[0, α]` equals the contour integrand integral when
`ε < ‖γ(t) - s‖` on `(0, α)`. Boundary points are measure-zero, so the equality goes
via `Ioc → Ioo` conversion. -/
theorem integral_cpvIntegrandOn_singleton_eq_contour_left
    (γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε α : ℝ}
    (hα : 0 ≤ α)
    (h_outside : ∀ t ∈ Ioo (0 : ℝ) α, ε < ‖γ.toPath.extend t - s‖) :
    ∫ t in (0 : ℝ)..α, cpvIntegrandOn {s} f γ.toPath.extend ε t =
      ∫ t in (0 : ℝ)..α, f (γ.toPath.extend t) * deriv γ.toPath.extend t := by
  rw [intervalIntegral.integral_of_le hα, intervalIntegral.integral_of_le hα,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht ↦
    cpvIntegrandOn_singleton_eq_contour_of_far γ (h_outside t ht)

/-- The CPV integrand integral on `[β, 1]` equals the contour integrand integral when
`ε < ‖γ(t) - s‖` on `(β, 1)`. -/
theorem integral_cpvIntegrandOn_singleton_eq_contour_right
    (γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε β : ℝ} (hβ : β ≤ 1)
    (h_outside : ∀ t ∈ Ioo β (1 : ℝ), ε < ‖γ.toPath.extend t - s‖) :
    ∫ t in β..(1 : ℝ), cpvIntegrandOn {s} f γ.toPath.extend ε t =
      ∫ t in β..(1 : ℝ), f (γ.toPath.extend t) * deriv γ.toPath.extend t := by
  rw [intervalIntegral.integral_of_le hβ, intervalIntegral.integral_of_le hβ,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht ↦
    cpvIntegrandOn_singleton_eq_contour_of_far γ (h_outside t ht)

/-- The CPV integrand integral on `[α, β]` is zero when `‖γ(t) - s‖ ≤ ε` on
`(α, β)`. -/
theorem integral_cpvIntegrandOn_singleton_eq_zero_middle
    (γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε α β : ℝ}
    (h_le : α ≤ β)
    (h_inside : ∀ t ∈ Ioo α β, ‖γ.toPath.extend t - s‖ ≤ ε) :
    ∫ t in α..β, cpvIntegrandOn {s} f γ.toPath.extend ε t = 0 := by
  rw [intervalIntegral.integral_of_le h_le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    MeasureTheory.setIntegral_congr_fun (g := fun _ ↦ (0 : ℂ)) measurableSet_Ioo
      (fun t ht ↦ cpvIntegrandOn_singleton_eq_zero_of_close γ (h_inside t ht))]
  simp

/-- Under the shape hypothesis on `(0, α) ∪ (α, β) ∪ (β, 1)`, the cpvIntegrandOn
integral on `[0, 1]` equals the symmetric-excision integral. -/
theorem cpvIntegrandOn_singleton_integral_eq_excision
    (γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε : ℝ}
    {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) (h_le : α ≤ β)
    (h_outside_left : ∀ t ∈ Ioo (0 : ℝ) α, ε < ‖γ.toPath.extend t - s‖)
    (h_outside_right : ∀ t ∈ Ioo β (1 : ℝ), ε < ‖γ.toPath.extend t - s‖)
    (h_inside : ∀ t ∈ Ioo α β, ‖γ.toPath.extend t - s‖ ≤ ε)
    (h_int_full : IntervalIntegrable
      (fun t ↦ cpvIntegrandOn {s} f γ.toPath.extend ε t) volume 0 1) :
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
    have h01 : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le (zero_le_one' ℝ)
    have h_int_α : IntervalIntegrable
        (fun t ↦ cpvIntegrandOn {s} f γ.toPath.extend ε t) volume 0 α :=
      h_int_full.mono_set <| by
        rw [Set.uIcc_of_le hα, h01]
        exact Set.Icc_subset_Icc le_rfl hα1
    have h_int_β : IntervalIntegrable
        (fun t ↦ cpvIntegrandOn {s} f γ.toPath.extend ε t) volume α β :=
      h_int_full.mono_set <| by
        rw [Set.uIcc_of_le h_le, h01]
        exact Set.Icc_subset_Icc hα hβ
    have h_int_1 : IntervalIntegrable
        (fun t ↦ cpvIntegrandOn {s} f γ.toPath.extend ε t) volume β 1 :=
      h_int_full.mono_set <| by
        rw [Set.uIcc_of_le hβ, h01]
        exact Set.Icc_subset_Icc h0β le_rfl
    rw [← intervalIntegral.integral_add_adjacent_intervals (h_int_α.trans h_int_β) h_int_1,
        ← intervalIntegral.integral_add_adjacent_intervals h_int_α h_int_β]
  rw [h_split,
      integral_cpvIntegrandOn_singleton_eq_contour_left γ hα h_outside_left,
      integral_cpvIntegrandOn_singleton_eq_zero_middle γ h_le h_inside,
      integral_cpvIntegrandOn_singleton_eq_contour_right γ hβ h_outside_right,
      add_zero]

/-! ## Bridge to `HasCauchyPVOn` -/

/-- Bridge from parametric symmetric-excision PV to `HasCauchyPVOn`: given functions
`α, β : ℝ → ℝ` (the exit-time functions, e.g., `firstExitTimeLeft` and
`firstExitTimeRight`) such that:

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
      (fun t ↦ cpvIntegrandOn {s} f γ.toPath.extend ε t) volume 0 1)
    (h_excision : Tendsto (fun ε ↦
      (∫ t in (0 : ℝ)..(α ε), f (γ.toPath.extend t) * deriv γ.toPath.extend t) +
      ∫ t in (β ε)..(1 : ℝ), f (γ.toPath.extend t) * deriv γ.toPath.extend t)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    HasCauchyPVOn {s} f γ 0 := by
  refine h_excision.congr' ?_
  filter_upwards [h_shape, h_int_full] with ε ⟨ha, hb, hc, hd, he, hf⟩ h_int
  exact (cpvIntegrandOn_singleton_integral_eq_excision γ
    ha hb hc hd he hf h_int).symm

/-! ## Specialization to firstExitTimeLeft / firstExitTimeRight -/

/-- Specialization of `hasCauchyPVOn_singleton_of_excision_tendsto` to the canonical
exit times `α = firstExitTimeLeft` and `β = firstExitTimeRight`. -/
theorem hasCauchyPVOn_singleton_of_exitTime_excision
    (γ : PiecewiseC1Path x x) (s : ℂ) (f : ℂ → ℂ)
    {t₀ δMinus δPlus : ℝ}
    (h_shape : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ LeanModularForms.firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε ∧
      LeanModularForms.firstExitTimeRight γ.toPath.extend t₀ δPlus s ε ≤ 1 ∧
      LeanModularForms.firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε ≤
        LeanModularForms.firstExitTimeRight γ.toPath.extend t₀ δPlus s ε ∧
      (∀ t ∈ Ioo (0 : ℝ)
          (LeanModularForms.firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε),
        ε < ‖γ.toPath.extend t - s‖) ∧
      (∀ t ∈ Ioo
          (LeanModularForms.firstExitTimeRight γ.toPath.extend t₀ δPlus s ε)
          (1 : ℝ),
        ε < ‖γ.toPath.extend t - s‖) ∧
      (∀ t ∈ Ioo
          (LeanModularForms.firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε)
          (LeanModularForms.firstExitTimeRight γ.toPath.extend t₀ δPlus s ε),
        ‖γ.toPath.extend t - s‖ ≤ ε))
    (h_int_full : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t ↦ cpvIntegrandOn {s} f γ.toPath.extend ε t) volume 0 1)
    (h_excision : Tendsto (fun ε ↦
      (∫ t in (0 : ℝ)..
          (LeanModularForms.firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε),
        f (γ.toPath.extend t) * deriv γ.toPath.extend t) +
      ∫ t in
          (LeanModularForms.firstExitTimeRight γ.toPath.extend t₀ δPlus s ε)..
          (1 : ℝ),
        f (γ.toPath.extend t) * deriv γ.toPath.extend t)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    HasCauchyPVOn {s} f γ 0 :=
  hasCauchyPVOn_singleton_of_excision_tendsto γ s f
    (LeanModularForms.firstExitTimeLeft γ.toPath.extend t₀ δMinus s)
    (LeanModularForms.firstExitTimeRight γ.toPath.extend t₀ δPlus s)
    h_shape h_int_full h_excision

/-! ## Shape hypothesis from local strict monotonicity -/

/-- Left-side shape from strict anti-monotonicity. If `γ` is continuous on
`[t₀ - δMinus, t₀]` with `‖γ - s‖` strictly anti-monotone there, and `γ` avoids `s`
on `[0, t₀ - δMinus]` with margin `δ_avoid > 0`, then for sufficiently small `ε > 0`,
`0 ≤ firstExitTimeLeft γ t₀ δMinus s ε` and for `t ∈ Ioo 0 (firstExitTimeLeft …)`,
`ε < ‖γ(t) - s‖`. -/
theorem shape_left_of_strictAntiOn
    {γ : ℝ → ℂ} {s : ℂ} {t₀ δMinus : ℝ}
    (h_t₀_minus_pos : 0 ≤ t₀ - δMinus)
    (hδMinus : 0 < δMinus)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - δMinus) t₀))
    (hγ_anti : StrictAntiOn (fun t ↦ ‖γ t - s‖) (Icc (t₀ - δMinus) t₀))
    {δ_avoid : ℝ} (h_avoid : ∀ t ∈ Icc (0 : ℝ) (t₀ - δMinus), δ_avoid ≤ ‖γ t - s‖)
    {ε : ℝ} (hε_lt_avoid : ε < δ_avoid)
    (hε_le_max : ε ≤ ‖γ (t₀ - δMinus) - s‖) :
    0 ≤ LeanModularForms.firstExitTimeLeft γ t₀ δMinus s ε ∧
    ∀ t ∈ Ioo (0 : ℝ) (LeanModularForms.firstExitTimeLeft γ t₀ δMinus s ε),
      ε < ‖γ t - s‖ := by
  have h_inIcc :=
    LeanModularForms.firstExitTimeLeft_mem_Icc hδMinus.le hε_le_max
  refine ⟨h_t₀_minus_pos.trans h_inIcc.1, ?_⟩
  intro t ⟨ht_pos, ht_lt⟩
  by_cases h_outer : t ≤ t₀ - δMinus
  · linarith [h_avoid t ⟨ht_pos.le, h_outer⟩]
  · push Not at h_outer
    linarith [LeanModularForms.ε_le_norm_at_firstExitTimeLeft hδMinus hγ_cont hε_le_max,
      hγ_anti ⟨h_outer.le, (ht_lt.trans_le h_inIcc.2).le⟩ h_inIcc ht_lt]

/-- Right-side counterpart of `shape_left_of_strictAntiOn`: `γ` continuous on
`[t₀, t₀ + δPlus]` with `‖γ - s‖` strictly monotone there, plus an avoidance margin on
`[t₀ + δPlus, 1]`, gives the right-side shape. -/
theorem shape_right_of_strictMonoOn
    {γ : ℝ → ℂ} {s : ℂ} {t₀ δPlus : ℝ}
    (h_t₀_plus_le : t₀ + δPlus ≤ 1)
    (hδPlus : 0 < δPlus)
    (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δPlus)))
    (hγ_mono : StrictMonoOn (fun t ↦ ‖γ t - s‖) (Icc t₀ (t₀ + δPlus)))
    {δ_avoid : ℝ} (h_avoid : ∀ t ∈ Icc (t₀ + δPlus) (1 : ℝ), δ_avoid ≤ ‖γ t - s‖)
    {ε : ℝ} (hε_lt_avoid : ε < δ_avoid)
    (hε_le_max : ε ≤ ‖γ (t₀ + δPlus) - s‖) :
    LeanModularForms.firstExitTimeRight γ t₀ δPlus s ε ≤ 1 ∧
    ∀ t ∈ Ioo (LeanModularForms.firstExitTimeRight γ t₀ δPlus s ε) (1 : ℝ),
      ε < ‖γ t - s‖ := by
  have h_inIcc :=
    LeanModularForms.firstExitTimeRight_mem_Icc hδPlus.le hε_le_max
  refine ⟨h_inIcc.2.trans h_t₀_plus_le, ?_⟩
  intro t ⟨ht_lt, ht_lt_one⟩
  by_cases h_outer : t₀ + δPlus ≤ t
  · linarith [h_avoid t ⟨h_outer, ht_lt_one.le⟩]
  · push Not at h_outer
    linarith [LeanModularForms.ε_le_norm_at_firstExitTimeRight hδPlus hγ_cont hε_le_max,
      hγ_mono h_inIcc ⟨(h_inIcc.1.trans_lt ht_lt).le, h_outer.le⟩ ht_lt]

/-! ## Eventual shape from monotonicity + avoidance margins -/

/-- Eventual right-side shape from strict monotonicity plus an avoidance margin. -/
theorem shape_right_eventually
    {γ : ℝ → ℂ} {s : ℂ} {t₀ δPlus : ℝ}
    (h_t₀_plus_le : t₀ + δPlus ≤ 1) (hδPlus : 0 < δPlus)
    (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δPlus)))
    (hγ_mono : StrictMonoOn (fun t ↦ ‖γ t - s‖) (Icc t₀ (t₀ + δPlus)))
    (_ : γ t₀ = s)
    {δ_avoid : ℝ} (h_avoid_pos : 0 < δ_avoid)
    (h_avoid : ∀ t ∈ Icc (t₀ + δPlus) (1 : ℝ), δ_avoid ≤ ‖γ t - s‖) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      LeanModularForms.firstExitTimeRight γ t₀ δPlus s ε ≤ 1 ∧
      ∀ t ∈ Ioo (LeanModularForms.firstExitTimeRight γ t₀ δPlus s ε) (1 : ℝ),
        ε < ‖γ t - s‖ := by
  filter_upwards [Ioo_mem_nhdsGT (lt_min (h_avoid_pos.trans_le
    (h_avoid (t₀ + δPlus) ⟨le_rfl, by linarith⟩)) h_avoid_pos)] with ε hε
  obtain ⟨h1, h2⟩ := lt_min_iff.mp hε.2
  exact shape_right_of_strictMonoOn h_t₀_plus_le hδPlus hγ_cont
    hγ_mono h_avoid h2 h1.le

/-- Eventual left-side shape from strict anti-monotonicity plus an avoidance
margin. -/
theorem shape_left_eventually
    {γ : ℝ → ℂ} {s : ℂ} {t₀ δMinus : ℝ}
    (h_t₀_minus_pos : 0 ≤ t₀ - δMinus) (hδMinus : 0 < δMinus)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - δMinus) t₀))
    (hγ_anti : StrictAntiOn (fun t ↦ ‖γ t - s‖) (Icc (t₀ - δMinus) t₀))
    (_ : γ t₀ = s)
    {δ_avoid : ℝ} (h_avoid_pos : 0 < δ_avoid)
    (h_avoid : ∀ t ∈ Icc (0 : ℝ) (t₀ - δMinus), δ_avoid ≤ ‖γ t - s‖) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ LeanModularForms.firstExitTimeLeft γ t₀ δMinus s ε ∧
      ∀ t ∈ Ioo (0 : ℝ) (LeanModularForms.firstExitTimeLeft γ t₀ δMinus s ε),
        ε < ‖γ t - s‖ := by
  filter_upwards [Ioo_mem_nhdsGT (lt_min (h_avoid_pos.trans_le
    (h_avoid (t₀ - δMinus) ⟨h_t₀_minus_pos, le_rfl⟩)) h_avoid_pos)] with ε hε
  obtain ⟨h1, h2⟩ := lt_min_iff.mp hε.2
  exact shape_left_of_strictAntiOn h_t₀_minus_pos hδMinus hγ_cont
    hγ_anti h_avoid h2 h1.le

/-- Combined shape (left + right) eventually from strict monotonicity, bundling
`shape_left_eventually` and `shape_right_eventually` plus the trivial `α ε ≤ β ε`
inequality into a single `∀ᶠ ε` statement matching the shape input of
`hasCauchyPVOn_singleton_of_exitTime_excision`. The `‖γ - s‖ ≤ ε on Ioo α β` part
holds automatically from the sSup/sInf properties of the exit-time definitions. -/
theorem shape_eventually_of_strict_mono
    {γ : ℝ → ℂ} {s : ℂ} {t₀ δMinus δPlus : ℝ}
    (h_t₀_minus_pos : 0 ≤ t₀ - δMinus) (h_t₀_plus_le : t₀ + δPlus ≤ 1)
    (hδMinus : 0 < δMinus) (hδPlus : 0 < δPlus)
    (hγ_cont_left : ContinuousOn γ (Icc (t₀ - δMinus) t₀))
    (hγ_cont_right : ContinuousOn γ (Icc t₀ (t₀ + δPlus)))
    (hγ_anti : StrictAntiOn (fun t ↦ ‖γ t - s‖) (Icc (t₀ - δMinus) t₀))
    (hγ_mono : StrictMonoOn (fun t ↦ ‖γ t - s‖) (Icc t₀ (t₀ + δPlus)))
    (h_s : γ t₀ = s)
    {δ_avoid_left δ_avoid_right : ℝ}
    (h_avoid_left_pos : 0 < δ_avoid_left)
    (h_avoid_right_pos : 0 < δ_avoid_right)
    (h_avoid_left : ∀ t ∈ Icc (0 : ℝ) (t₀ - δMinus), δ_avoid_left ≤ ‖γ t - s‖)
    (h_avoid_right : ∀ t ∈ Icc (t₀ + δPlus) (1 : ℝ), δ_avoid_right ≤ ‖γ t - s‖) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ LeanModularForms.firstExitTimeLeft γ t₀ δMinus s ε ∧
      LeanModularForms.firstExitTimeRight γ t₀ δPlus s ε ≤ 1 ∧
      LeanModularForms.firstExitTimeLeft γ t₀ δMinus s ε ≤
        LeanModularForms.firstExitTimeRight γ t₀ δPlus s ε ∧
      (∀ t ∈ Ioo (0 : ℝ) (LeanModularForms.firstExitTimeLeft γ t₀ δMinus s ε),
        ε < ‖γ t - s‖) ∧
      (∀ t ∈ Ioo (LeanModularForms.firstExitTimeRight γ t₀ δPlus s ε) (1 : ℝ),
        ε < ‖γ t - s‖) ∧
      (∀ t ∈ Ioo (LeanModularForms.firstExitTimeLeft γ t₀ δMinus s ε)
        (LeanModularForms.firstExitTimeRight γ t₀ δPlus s ε),
        ‖γ t - s‖ ≤ ε) := by
  have h_left := shape_left_eventually h_t₀_minus_pos hδMinus hγ_cont_left
    hγ_anti h_s h_avoid_left_pos h_avoid_left
  have h_right := shape_right_eventually h_t₀_plus_le hδPlus hγ_cont_right
    hγ_mono h_s h_avoid_right_pos h_avoid_right
  have h_in_brackets : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      LeanModularForms.firstExitTimeLeft γ t₀ δMinus s ε ≤
        LeanModularForms.firstExitTimeRight γ t₀ δPlus s ε ∧
      ∀ t ∈ Ioo (LeanModularForms.firstExitTimeLeft γ t₀ δMinus s ε)
        (LeanModularForms.firstExitTimeRight γ t₀ δPlus s ε),
        ‖γ t - s‖ ≤ ε := by
    have hL := h_avoid_left_pos.trans_le
      (h_avoid_left (t₀ - δMinus) ⟨h_t₀_minus_pos, le_rfl⟩)
    have hR := h_avoid_right_pos.trans_le
      (h_avoid_right (t₀ + δPlus) ⟨le_rfl, by linarith⟩)
    filter_upwards [Ioo_mem_nhdsGT (lt_min hL hR)] with ε hε
    refine ⟨(LeanModularForms.firstExitTimeLeft_mem_Icc hδMinus.le
      ((lt_min_iff.mp hε.2).1.le)).2.trans
      (LeanModularForms.firstExitTimeRight_mem_Icc hδPlus.le
        ((lt_min_iff.mp hε.2).2.le)).1, ?_⟩
    intro t ht
    by_cases h_t_t₀ : t ≤ t₀
    · have ht_in_Icc : t ∈ Icc (t₀ - δMinus) t₀ := by
        refine ⟨?_, h_t_t₀⟩
        linarith [(LeanModularForms.firstExitTimeLeft_mem_Icc hδMinus.le
          ((lt_min_iff.mp hε.2).1.le)).1, ht.1]
      by_contra h_ge
      have h_in_set : t ∈ {t' ∈ Set.Icc (t₀ - δMinus) t₀ | ε ≤ ‖γ t' - s‖} :=
        ⟨ht_in_Icc, (not_le.mp h_ge).le⟩
      have h_le : t ≤ LeanModularForms.firstExitTimeLeft γ t₀ δMinus s ε :=
        le_csSup ⟨t₀, LeanModularForms.firstExitTimeLeft_set_ub γ t₀ δMinus ε s⟩ h_in_set
      linarith [ht.1]
    · have ht_in_Icc : t ∈ Icc t₀ (t₀ + δPlus) := by
        refine ⟨(not_le.mp h_t_t₀).le, ?_⟩
        linarith [(LeanModularForms.firstExitTimeRight_mem_Icc hδPlus.le
          ((lt_min_iff.mp hε.2).2.le)).2, ht.2]
      by_contra h_ge
      have h_in_set : t ∈ {t' ∈ Set.Icc t₀ (t₀ + δPlus) | ε ≤ ‖γ t' - s‖} :=
        ⟨ht_in_Icc, (not_le.mp h_ge).le⟩
      have h_le : LeanModularForms.firstExitTimeRight γ t₀ δPlus s ε ≤ t :=
        csInf_le ⟨t₀, LeanModularForms.firstExitTimeRight_set_lb γ t₀ δPlus ε s⟩ h_in_set
      linarith [ht.2]
  filter_upwards [h_left, h_right, h_in_brackets] with ε ⟨hL1, hL2⟩ ⟨hR1, hR2⟩ ⟨hLR1, hLR2⟩
  exact ⟨hL1, hR1, hLR1, hL2, hR2, hLR2⟩

end HungerbuhlerWasem

end
