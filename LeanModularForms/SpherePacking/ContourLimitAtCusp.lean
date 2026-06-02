/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.SpherePacking.CuspDecay
import LeanModularForms.SpherePacking.PhiHolomorphic
import LeanModularForms.SpherePacking.RectangularContour
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Cusp-neighborhood limits of contour integrals

Reusable analytic-decay lemmas for the "top of the box" segment in any
rectangular contour that closes at the cusp `z = i∞`. The headline
result `tendsto_topSegment_integral_zero` says: if `f` is bounded on a
cusp neighborhood `{Im z ≥ R₀}` and `r > 0`, then
`∫_a^b f(x + iR) · e^{π·i·r·(x + iR)} dx → 0` as `R → ∞`.

These results combine pointwise modular-form decay at the cusp
(from `CuspDecay.lean`, e.g. `phi0_isBoundedAtImInfty`) with the
exponential decay `|e^{πirz}| = e^{-π·r·Im z}` to discharge
"top-of-box" contributions in HW-3.3-style contour arguments.

## Main results

* `tendsto_topSegment_integral_zero_of_bound`: primary result. If the
  interval integrand `g R x` is bounded by `M · e^{-π·r·R}` eventually
  in `R`, then `∫_a^b g R x dx → 0` as `R → ∞`.
* `tendsto_topSegment_integral_zero`: thin wrapper specialised to the
  Viazovska-style integrand `f(x + iR) · e^{π·i·r·(x + iR)}` with
  `f` bounded on a cusp neighborhood. -/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

noncomputable section

namespace LeanModularForms

/-! ## Exponential-decay helpers -/

/-- Real exponential at a coefficient times a parameter going to infinity:
`exp(-c · R) → 0` as `R → ∞`, for `c > 0`. -/
lemma tendsto_real_exp_neg_const_mul_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun R : ℝ => Real.exp (-c * R)) atTop (nhds 0) := by
  have h_pos : Tendsto (fun R : ℝ => c * R) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop hc
  have h_arg : Tendsto (fun R : ℝ => -c * R) atTop atBot := by
    have := Filter.tendsto_neg_atTop_atBot.comp h_pos
    simpa [Function.comp_def, neg_mul] using this
  exact Real.tendsto_exp_atBot.comp h_arg

/-! ## Primary result: integrand bounded by `M · e^{-πrR}` -/

/-- **Primary form.** If the integrand `g R x` is bounded (uniformly in `x ∈ [a,b]`)
by `M · e^{-π·r·R}` for all sufficiently large `R`, then the interval integral
`∫_a^b g R x dx` tends to `0` as `R → ∞`.

The bound on `M` (e.g. `0 ≤ M`) is *not* a hypothesis: it follows from
`‖g R x‖ ≥ 0` combined with the eventual bound at any point. Note also that
no integrability assumption is needed: if `g R` is not integrable on `[a,b]`,
its integral is zero and the bound is trivial. -/
theorem tendsto_topSegment_integral_zero_of_bound
    {g : ℝ → ℝ → ℂ} {M : ℝ}
    {r : ℝ} (hr : 0 < r) (a b : ℝ)
    (h_bound : ∀ᶠ R in atTop, ∀ x ∈ Set.uIcc a b,
        ‖g R x‖ ≤ M * Real.exp (-Real.pi * r * R)) :
    Tendsto (fun R : ℝ => ∫ x in a..b, g R x) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  -- Sandwich: 0 ≤ ‖∫‖ ≤ M · |b - a| · e^{-πrR} → 0
  have hπr : 0 < Real.pi * r := mul_pos Real.pi_pos hr
  have h_exp_tendsto : Tendsto (fun R : ℝ => Real.exp (-Real.pi * r * R)) atTop (nhds 0) := by
    have := tendsto_real_exp_neg_const_mul_atTop hπr
    refine this.congr fun R => ?_
    ring_nf
  have h_majorant : Tendsto
      (fun R : ℝ => M * |b - a| * Real.exp (-Real.pi * r * R)) atTop (nhds 0) := by
    have := h_exp_tendsto.const_mul (M * |b - a|)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h_majorant
  filter_upwards [h_bound] with R hR
  -- Convert ‖∫‖ bound via norm_integral_le_of_norm_le_const
  have h_uIoc_subset : ∀ x ∈ Ι a b, ‖g R x‖ ≤ M * Real.exp (-Real.pi * r * R) := by
    intro x hx
    exact hR x (uIoc_subset_uIcc hx)
  have h_le := intervalIntegral.norm_integral_le_of_norm_le_const h_uIoc_subset
  -- Reshuffle: ‖∫‖ ≤ (M · exp(-πrR)) · |b - a| = M · |b - a| · exp(-πrR)
  calc ‖∫ x in a..b, g R x‖
      ≤ M * Real.exp (-Real.pi * r * R) * |b - a| := h_le
    _ = M * |b - a| * Real.exp (-Real.pi * r * R) := by ring

/-! ## Bounded-integrand decay: Viazovska-style integrand -/

/-- **Theorem A.** If `f : ℂ → ℂ` is bounded by `M` on the cusp neighborhood
`{Im z ≥ R₀}`, and `r > 0`, then the horizontal-segment integral
`∫_a^b f(x + i·R) · e^{π·i·r·(x + i·R)} dx` tends to `0` as `R → ∞`.

The bound comes from `|e^{πirz}| = e^{-π·r·Im z}` decay combined with the
constant bound on `f`. -/
theorem tendsto_topSegment_integral_zero
    {f : ℂ → ℂ} {M R₀ : ℝ}
    (hf_bounded : ∀ z : ℂ, R₀ ≤ z.im → ‖f z‖ ≤ M)
    {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    Tendsto
      (fun R : ℝ =>
        ∫ x in a..b, f ((x : ℂ) + R * Complex.I) *
          Complex.exp (Real.pi * Complex.I * r * ((x : ℂ) + R * Complex.I)))
      atTop (nhds 0) := by
  set g : ℝ → ℝ → ℂ := fun R x => f ((x : ℂ) + R * Complex.I) *
    Complex.exp (Real.pi * Complex.I * r * ((x : ℂ) + R * Complex.I)) with hg_def
  apply tendsto_topSegment_integral_zero_of_bound (g := g) hr a b
  -- Pointwise bound for R ≥ R₀ and x ∈ [a,b]
  filter_upwards [Filter.eventually_ge_atTop R₀] with R hR x _
  simp only [hg_def]
  -- Step 1: the imaginary part of (x + R·I) is R
  have him : ((x : ℂ) + R * Complex.I).im = R := by
    simp [Complex.add_im, Complex.mul_im]
  have hf_le : ‖f ((x : ℂ) + R * Complex.I)‖ ≤ M := by
    apply hf_bounded
    rw [him]; exact hR
  -- Step 2: the real part of πirz = πir(x + iR) is -πrR
  have hzre : (Real.pi * Complex.I * r * ((x : ℂ) + R * Complex.I)).re =
      -(Real.pi * r * R) := by
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  have h_exp_norm : ‖Complex.exp (Real.pi * Complex.I * r * ((x : ℂ) + R * Complex.I))‖ =
      Real.exp (-(Real.pi * r * R)) := by
    rw [Complex.norm_exp, hzre]
  rw [norm_mul, h_exp_norm]
  have h_le : ‖f ((x : ℂ) + R * Complex.I)‖ * Real.exp (-(Real.pi * r * R))
      ≤ M * Real.exp (-(Real.pi * r * R)) :=
    mul_le_mul_of_nonneg_right hf_le (Real.exp_nonneg _)
  refine h_le.trans (le_of_eq ?_)
  ring_nf

/-! ## Convenience: φ₀-flavoured corollary

A specialised form that combines `phi0_isBoundedAtImInfty` from `CuspDecay.lean`
with `tendsto_topSegment_integral_zero` to give the decay statement directly
for the Viazovska tail integrand `φ₀''(z) · e^{π·i·r·z}`. -/

/-- `φ₀''` is bounded by some constant on a cusp neighborhood `{Im z ≥ R₀}`. -/
lemma phi0''_bounded_on_cusp_neighborhood :
    ∃ M R₀ : ℝ, 0 < R₀ ∧ ∀ z : ℂ, R₀ ≤ z.im → ‖φ₀'' z‖ ≤ M := by
  obtain ⟨M, A, hM⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp phi0_isBoundedAtImInfty
  refine ⟨M, max A 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun z hz => ?_⟩
  by_cases hpos : 0 < z.im
  · -- Then z lifts to UHP and the bound applies
    have hA : A ≤ (⟨z, hpos⟩ : UpperHalfPlane).im :=
      (le_max_left A 1).trans hz
    have := hM ⟨z, hpos⟩ hA
    -- Need to identify φ₀'' z with φ₀ ⟨z, hpos⟩
    have heq : φ₀'' z = φ₀ ⟨z, hpos⟩ := by
      simp [φ₀'', hpos]
    rw [heq]
    exact this
  · -- This case never happens because R₀ ≥ 1 > 0
    exfalso
    apply hpos
    exact lt_of_lt_of_le one_pos ((le_max_right A 1).trans hz)

/-- **Convenience for the Viazovska tail.** The integrand `φ₀''(x + i·R) · e^{πirz}`
integrated horizontally tends to zero as `R → ∞`, for any `r > 0` and any interval. -/
theorem tendsto_phi0_topSegment_integral_zero {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    Tendsto
      (fun R : ℝ =>
        ∫ x in a..b, φ₀'' ((x : ℂ) + R * Complex.I) *
          Complex.exp (Real.pi * Complex.I * r * ((x : ℂ) + R * Complex.I)))
      atTop (nhds 0) := by
  obtain ⟨M, R₀, _, hbound⟩ := phi0''_bounded_on_cusp_neighborhood
  exact tendsto_topSegment_integral_zero (f := φ₀'') (M := M) (R₀ := R₀) hbound hr a b

end LeanModularForms

end
