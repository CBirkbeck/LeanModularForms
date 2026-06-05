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

/-! ## Semi-infinite rectangle Cauchy

For a holomorphic `f` on a convex open set containing the closed semi-infinite
rectangle `[a, b] × [c, ∞)`, if `f`'s top-edge integral vanishes as height → ∞,
then the bottom-edge integral equals the difference of the two upward vertical
integrals.

Strategy: For each finite height `R > c`, the bounded-rectangle Cauchy theorem
(`cauchy_rectangle_zero`) combined with the decomposition lemma
(`contourIntegral_rectangleContour_eq`) gives a four-segment identity. Each
segment integral reduces to a "standard" interval integral via the affine
change of variables. Passing to the limit using
`MeasureTheory.intervalIntegral_tendsto_integral_Ioi` finishes the job. -/

/-- Bottom-side standard form. The segment integral `∫ s ∈ 0..1, f((a+ci) +
s•((b+ci) - (a+ci))) · ((b+ci) - (a+ci))` simplifies to `∫ x ∈ a..b, f(x + ci) dx`. -/
private lemma rect_seg_bottom_standard (a b c : ℝ) (f : ℂ → ℂ) :
    (∫ s in (0:ℝ)..1, f ((a : ℂ) + c * I + s • (((b : ℂ) + c * I) - ((a : ℂ) + c * I))) *
        (((b : ℂ) + c * I) - ((a : ℂ) + c * I)))
      = ∫ x in a..b, f ((x : ℂ) + c * I) := by
  -- Step 1: simplify the difference and the integrand pointwise.
  rw [show (((b : ℂ) + c * I) - ((a : ℂ) + c * I)) = ((b - a : ℝ) : ℂ) by push_cast; ring]
  have h_pointwise : ∀ s : ℝ,
      f ((a : ℂ) + c * I + s • ((b - a : ℝ) : ℂ)) * ((b - a : ℝ) : ℂ)
        = ((b - a : ℝ) : ℂ) * f ((((b - a) * s + a : ℝ) : ℂ) + c * I) := by
    intro s
    rw [Complex.real_smul]
    have h_inner : (a : ℂ) + c * I + (s : ℂ) * ((b - a : ℝ) : ℂ) =
        (((b - a) * s + a : ℝ) : ℂ) + c * I := by push_cast; ring
    rw [h_inner, mul_comm]
  rw [intervalIntegral.integral_congr (fun s _ => h_pointwise s)]
  -- Step 2: pull out the constant.
  have h_pull := intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
    (a := (0:ℝ)) (b := 1) (((b - a) : ℝ) : ℂ)
    (fun x => f ((((b - a) * x + a : ℝ) : ℂ) + c * I))
  refine h_pull.trans ?_
  -- Step 3: apply the affine change of variables.
  have h_cov := intervalIntegral.smul_integral_comp_mul_add (a := (0:ℝ)) (b := 1)
    (f := fun x => f ((x : ℂ) + c * I)) (b - a) a
  simp only [mul_zero, zero_add, mul_one] at h_cov
  rw [show (b - a + a : ℝ) = b from by ring] at h_cov
  rw [← Complex.real_smul]
  exact h_cov

/-- Right-side standard form. The segment integral `∫ s ∈ 0..1, f((b+ci) +
s•((b+di) - (b+ci))) · ((b+di) - (b+ci))` simplifies to
`(∫ y ∈ c..d, f(b + yi) dy) · I`. -/
private lemma rect_seg_right_standard (b c d : ℝ) (f : ℂ → ℂ) :
    (∫ s in (0:ℝ)..1, f ((b : ℂ) + c * I + s • (((b : ℂ) + d * I) - ((b : ℂ) + c * I))) *
        (((b : ℂ) + d * I) - ((b : ℂ) + c * I)))
      = (∫ y in c..d, f ((b : ℂ) + y * I)) * I := by
  -- Step 1: rewrite the difference as (d-c)*I.
  rw [show (((b : ℂ) + d * I) - ((b : ℂ) + c * I)) = ((d - c : ℝ) : ℂ) * I by push_cast; ring]
  -- Step 2: simplify the integrand pointwise: extract the constant `(d-c)*I`.
  have h_pointwise : ∀ s : ℝ,
      f ((b : ℂ) + c * I + s • (((d - c : ℝ) : ℂ) * I)) * (((d - c : ℝ) : ℂ) * I)
        = ((d - c : ℝ) : ℂ) * I * f ((b : ℂ) + ((d - c) * s + c : ℝ) * I) := by
    intro s
    rw [Complex.real_smul]
    have h_inner : (b : ℂ) + c * I + (s : ℂ) * (((d - c : ℝ) : ℂ) * I) =
        (b : ℂ) + (((d - c) * s + c : ℝ) : ℂ) * I := by push_cast; ring
    rw [h_inner, mul_comm]
  rw [intervalIntegral.integral_congr (fun s _ => h_pointwise s)]
  -- Step 3: pull the constant `(d-c)*I` out of the integral.
  have h_pull := intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
    (a := (0:ℝ)) (b := 1) (((d - c : ℝ) : ℂ) * I)
    (fun s => f ((b : ℂ) + ((d - c) * s + c : ℝ) * I))
  refine h_pull.trans ?_
  -- Step 4: apply the affine change of variables on the inner integral.
  have h_cov := intervalIntegral.smul_integral_comp_mul_add (a := (0:ℝ)) (b := 1)
    (f := fun y => f ((b : ℂ) + y * I)) (d - c) c
  simp only [mul_zero, zero_add, mul_one] at h_cov
  rw [show (d - c + c : ℝ) = d from by ring] at h_cov
  -- h_cov : (d-c) • ∫ s in 0..1, f(b + ((d-c)*s + c : ℝ) * I) = ∫ y in c..d, f(b + y*I)
  -- Step 5: combine: A * I * B = (A * B) * I = ((d-c) • B) * I = (∫ ... y ...) * I
  have h_smul : ((d - c : ℝ) : ℂ) *
      ∫ s in (0:ℝ)..1, f ((b : ℂ) + ((d - c) * s + c : ℝ) * I)
      = ∫ y in c..d, f ((b : ℂ) + y * I) := by
    rw [← Complex.real_smul]; exact h_cov
  calc ((d - c : ℝ) : ℂ) * I *
        ∫ s in (0:ℝ)..1, f ((b : ℂ) + ((d - c) * s + c : ℝ) * I)
      = (((d - c : ℝ) : ℂ) *
          ∫ s in (0:ℝ)..1, f ((b : ℂ) + ((d - c) * s + c : ℝ) * I)) * I := by ring
    _ = (∫ y in c..d, f ((b : ℂ) + y * I)) * I := by rw [h_smul]

/-- Top-side standard form. The segment integral `∫ s ∈ 0..1, f((b+di) +
s•((a+di) - (b+di))) · ((a+di) - (b+di))` simplifies to `-∫ x ∈ a..b, f(x + di) dx`. -/
private lemma rect_seg_top_standard (a b d : ℝ) (f : ℂ → ℂ) :
    (∫ s in (0:ℝ)..1, f ((b : ℂ) + d * I + s • (((a : ℂ) + d * I) - ((b : ℂ) + d * I))) *
        (((a : ℂ) + d * I) - ((b : ℂ) + d * I)))
      = -∫ x in a..b, f ((x : ℂ) + d * I) := by
  -- Step 1: simplify the difference, which is (a - b : ℂ).
  rw [show (((a : ℂ) + d * I) - ((b : ℂ) + d * I)) = ((a - b : ℝ) : ℂ) by push_cast; ring]
  -- Step 2: simplify the integrand pointwise.
  have h_pointwise : ∀ s : ℝ,
      f ((b : ℂ) + d * I + s • ((a - b : ℝ) : ℂ)) * ((a - b : ℝ) : ℂ)
        = ((a - b : ℝ) : ℂ) * f ((((a - b) * s + b : ℝ) : ℂ) + d * I) := by
    intro s
    rw [Complex.real_smul]
    have h_inner : (b : ℂ) + d * I + (s : ℂ) * ((a - b : ℝ) : ℂ) =
        (((a - b) * s + b : ℝ) : ℂ) + d * I := by push_cast; ring
    rw [h_inner, mul_comm]
  rw [intervalIntegral.integral_congr (fun s _ => h_pointwise s)]
  -- Step 3: pull out the constant.
  have h_pull := intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
    (a := (0:ℝ)) (b := 1) (((a - b) : ℝ) : ℂ)
    (fun s => f ((((a - b) * s + b : ℝ) : ℂ) + d * I))
  refine h_pull.trans ?_
  -- Step 4: change of variables `x = b + (a-b)*s`, going from [0,1] to [b, a].
  have h_cov := intervalIntegral.smul_integral_comp_mul_add (a := (0:ℝ)) (b := 1)
    (f := fun x => f ((x : ℂ) + d * I)) (a - b) b
  simp only [mul_zero, zero_add, mul_one] at h_cov
  rw [show (a - b + b : ℝ) = a from by ring] at h_cov
  -- h_cov : (a-b) • ∫ s in 0..1, f(((a-b)*s + b : ℝ) : ℂ + d*I)
  --        = ∫ x in b..a, f((x:ℝ):ℂ + d*I)
  have h_ba : (∫ x in b..a, f ((x : ℂ) + d * I))
      = -∫ x in a..b, f ((x : ℂ) + d * I) :=
    intervalIntegral.integral_symm (μ := MeasureTheory.volume) a b
  rw [← Complex.real_smul]
  exact h_cov.trans h_ba

/-- Left-side standard form. The segment integral `∫ s ∈ 0..1, f((a+di) +
s•((a+ci) - (a+di))) · ((a+ci) - (a+di))` simplifies to
`-(∫ y ∈ c..d, f(a + yi) dy) · I`. -/
private lemma rect_seg_left_standard (a c d : ℝ) (f : ℂ → ℂ) :
    (∫ s in (0:ℝ)..1, f ((a : ℂ) + d * I + s • (((a : ℂ) + c * I) - ((a : ℂ) + d * I))) *
        (((a : ℂ) + c * I) - ((a : ℂ) + d * I)))
      = -((∫ y in c..d, f ((a : ℂ) + y * I)) * I) := by
  -- Step 1: rewrite the difference as (c-d)*I.
  rw [show (((a : ℂ) + c * I) - ((a : ℂ) + d * I)) = ((c - d : ℝ) : ℂ) * I by push_cast; ring]
  -- Step 2: simplify the integrand pointwise.
  have h_pointwise : ∀ s : ℝ,
      f ((a : ℂ) + d * I + s • (((c - d : ℝ) : ℂ) * I)) * (((c - d : ℝ) : ℂ) * I)
        = ((c - d : ℝ) : ℂ) * I * f ((a : ℂ) + ((c - d) * s + d : ℝ) * I) := by
    intro s
    rw [Complex.real_smul]
    have h_inner : (a : ℂ) + d * I + (s : ℂ) * (((c - d : ℝ) : ℂ) * I) =
        (a : ℂ) + (((c - d) * s + d : ℝ) : ℂ) * I := by push_cast; ring
    rw [h_inner, mul_comm]
  rw [intervalIntegral.integral_congr (fun s _ => h_pointwise s)]
  -- Step 3: pull the constant `(c-d)*I` out of the integral.
  have h_pull := intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
    (a := (0:ℝ)) (b := 1) (((c - d : ℝ) : ℂ) * I)
    (fun s => f ((a : ℂ) + ((c - d) * s + d : ℝ) * I))
  refine h_pull.trans ?_
  -- Step 4: change of variables `y = d + (c-d)*s`, going from [0,1] to [d, c].
  have h_cov := intervalIntegral.smul_integral_comp_mul_add (a := (0:ℝ)) (b := 1)
    (f := fun y => f ((a : ℂ) + y * I)) (c - d) d
  simp only [mul_zero, zero_add, mul_one] at h_cov
  rw [show (c - d + d : ℝ) = c from by ring] at h_cov
  -- h_cov : (c-d) • ∫ s in 0..1, f(a + ((c-d)*s + d : ℝ) * I) = ∫ y in d..c, f(a + y*I)
  -- Now ∫ y in d..c, ... = -∫ y in c..d, ...
  have h_smul : ((c - d : ℝ) : ℂ) *
      ∫ s in (0:ℝ)..1, f ((a : ℂ) + ((c - d) * s + d : ℝ) * I)
      = ∫ y in d..c, f ((a : ℂ) + y * I) := by
    rw [← Complex.real_smul]; exact h_cov
  have h_dc : (∫ y in d..c, f ((a : ℂ) + y * I))
      = -∫ y in c..d, f ((a : ℂ) + y * I) :=
    intervalIntegral.integral_symm (μ := MeasureTheory.volume) c d
  calc ((c - d : ℝ) : ℂ) * I *
        ∫ s in (0:ℝ)..1, f ((a : ℂ) + ((c - d) * s + d : ℝ) * I)
      = (((c - d : ℝ) : ℂ) *
          ∫ s in (0:ℝ)..1, f ((a : ℂ) + ((c - d) * s + d : ℝ) * I)) * I := by ring
    _ = (∫ y in d..c, f ((a : ℂ) + y * I)) * I := by rw [h_smul]
    _ = (-∫ y in c..d, f ((a : ℂ) + y * I)) * I := by rw [h_dc]
    _ = -((∫ y in c..d, f ((a : ℂ) + y * I)) * I) := by ring

/-! ### Finite-height rectangle identity

For each height `R > c`, the closed-rectangle Cauchy theorem combined with the
4-segment decomposition gives the identity
`(bottom) + (right) - (top') - (left') = 0`, where bottom and top' are
horizontal integrals and right, left' are vertical integrals (times `I`). -/

/-- The closed-rectangle Cauchy identity in "side-by-side" form: bottom +
right·I - top - left·I = 0, where bottom/top are horizontal segment
integrals and right/left are vertical segment integrals (without the `I`
factor). -/
private lemma cauchy_finite_rectangle_id
    {a b c R : ℝ} (hab : a < b) (hcR : c < R)
    {U : Set ℂ} (hU_open : IsOpen U) (hU_convex : Convex ℝ U)
    (h_rect_in_U : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c R, (x : ℂ) + y * I ∈ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    (∫ x in a..b, f ((x : ℂ) + c * I))
      + (∫ y in c..R, f ((b : ℂ) + y * I)) * I
      - (∫ x in a..b, f ((x : ℂ) + R * I))
      - (∫ y in c..R, f ((a : ℂ) + y * I)) * I = 0 := by
  -- Step 1: Nonempty (use bottom-left corner).
  have hU_ne : U.Nonempty :=
    ⟨(a : ℂ) + c * I, h_rect_in_U a ⟨le_refl _, hab.le⟩ c ⟨le_refl _, hcR.le⟩⟩
  -- Step 2: Cauchy on closed rectangle.
  have h_cauchy : (rectangleContour a b c R hab hcR).toPwC1Immersion.toPiecewiseC1Path.contourIntegral f = 0 :=
    cauchy_rectangle_zero hab hcR hU_open hU_ne hU_convex h_rect_in_U hf
  -- Step 3: Image-subset (the contour stays in U).
  have hf_cont_U : ContinuousOn f U := hf.continuousOn
  have h_image_subset : (rectangleContour a b c R hab hcR).toPwC1Immersion.toPiecewiseC1Path
      '' Icc (0:ℝ) 1 ⊆ U := by
    rintro w ⟨t, ht, rfl⟩
    exact rectangleContour_image_subset_rect hab hcR h_rect_in_U t ht
  have hf_cont : ContinuousOn f
      ((rectangleContour a b c R hab hcR).toPwC1Immersion.toPiecewiseC1Path '' Icc (0:ℝ) 1) :=
    hf_cont_U.mono h_image_subset
  -- Step 4: Decompose using `contourIntegral_rectangleContour_eq`.
  have h_decomp := contourIntegral_rectangleContour_eq hab hcR hf_cont
  rw [h_cauchy] at h_decomp
  -- Step 5: Convert each segment to standard form.
  rw [rect_seg_bottom_standard a b c f, rect_seg_right_standard b c R f,
      rect_seg_top_standard a b R f, rect_seg_left_standard a c R f] at h_decomp
  -- Step 6: Algebraic rearrangement.
  -- h_decomp : 0 = bottom + right·I + (-top) + (-(left·I))
  -- Goal:    bottom + right·I - top - left·I = 0
  linear_combination -h_decomp

/-! ### Main theorem: semi-infinite rectangle Cauchy -/

/-- **Cauchy's theorem on a semi-infinite rectangle.** For a holomorphic
function `f` on a convex open set `U` containing the closed semi-infinite
rectangle `[a, b] × [c, ∞)`, if `f`'s integral over the top horizontal
segment `[a, b] × {R}` tends to 0 as `R → ∞`, then the bottom horizontal
integral equals the difference of the two upward vertical integrals:

  `∫ x in a..b, f(x + ci) + (∫ y in Ioi c, f(b + yi)) * I - (∫ y in Ioi c, f(a + yi)) * I = 0`. -/
theorem cauchy_semi_infinite_rectangle_eq
    {a b c : ℝ} (hab : a < b)
    {U : Set ℂ} (hU_open : IsOpen U) (hU_convex : Convex ℝ U)
    (h_strip_in_U : ∀ x ∈ Set.Icc a b, ∀ y, c ≤ y → (x : ℂ) + y * I ∈ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (h_top_vanish : Tendsto (fun R : ℝ => ∫ x in a..b, f ((x : ℂ) + R * I)) atTop (𝓝 0))
    (h_int_b : MeasureTheory.IntegrableOn
      (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * I)) (Set.Ioi c))
    (h_int_a : MeasureTheory.IntegrableOn
      (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I)) (Set.Ioi c)) :
    (∫ x in a..b, f ((x : ℂ) + c * I))
      + (∫ y in Set.Ioi c, f ((b : ℂ) + (y : ℂ) * I)) * I
      - (∫ y in Set.Ioi c, f ((a : ℂ) + (y : ℂ) * I)) * I
    = 0 := by
  -- The finite-rectangle identity holds for every R > c.
  have h_eq : ∀ᶠ R : ℝ in atTop,
      (∫ x in a..b, f ((x : ℂ) + c * I))
        + (∫ y in c..R, f ((b : ℂ) + y * I)) * I
        - (∫ x in a..b, f ((x : ℂ) + R * I))
        - (∫ y in c..R, f ((a : ℂ) + y * I)) * I = 0 := by
    filter_upwards [Filter.eventually_gt_atTop c] with R hcR
    apply cauchy_finite_rectangle_id hab hcR hU_open hU_convex _ hf
    intro x hx y hy
    exact h_strip_in_U x hx y hy.1
  -- The identity, rearranged: bottom + right·I - top - left·I = 0
  -- Equivalently: bottom + right·I - left·I = top
  -- Take R → ∞.
  -- Left side (R-dependent): bottom + right·I - top - left·I.
  -- Limits:
  -- bottom: constant.
  -- right: ∫ y in c..R, f(b + yi) → ∫ y in Ioi c, f(b + yi).
  -- top: ∫ x in a..b, f(x + Ri) → 0.
  -- left: ∫ y in c..R, f(a + yi) → ∫ y in Ioi c, f(a + yi).
  have h_lim_right : Tendsto (fun R : ℝ => ∫ y in c..R, f ((b : ℂ) + y * I)) atTop
      (𝓝 (∫ y in Set.Ioi c, f ((b : ℂ) + y * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi c h_int_b Filter.tendsto_id
  have h_lim_left : Tendsto (fun R : ℝ => ∫ y in c..R, f ((a : ℂ) + y * I)) atTop
      (𝓝 (∫ y in Set.Ioi c, f ((a : ℂ) + y * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi c h_int_a Filter.tendsto_id
  -- Build the full LHS-tendsto.
  have h_lim_right_I :
      Tendsto (fun R : ℝ => (∫ y in c..R, f ((b : ℂ) + y * I)) * I) atTop
      (𝓝 ((∫ y in Set.Ioi c, f ((b : ℂ) + y * I)) * I)) :=
    h_lim_right.mul_const I
  have h_lim_left_I :
      Tendsto (fun R : ℝ => (∫ y in c..R, f ((a : ℂ) + y * I)) * I) atTop
      (𝓝 ((∫ y in Set.Ioi c, f ((a : ℂ) + y * I)) * I)) :=
    h_lim_left.mul_const I
  have h_lim_bottom : Tendsto (fun _ : ℝ => ∫ x in a..b, f ((x : ℂ) + c * I)) atTop
      (𝓝 (∫ x in a..b, f ((x : ℂ) + c * I))) := tendsto_const_nhds
  have h_lim_total :
      Tendsto
        (fun R : ℝ =>
          (∫ x in a..b, f ((x : ℂ) + c * I))
            + (∫ y in c..R, f ((b : ℂ) + y * I)) * I
            - (∫ x in a..b, f ((x : ℂ) + R * I))
            - (∫ y in c..R, f ((a : ℂ) + y * I)) * I) atTop
        (𝓝 ((∫ x in a..b, f ((x : ℂ) + c * I))
              + (∫ y in Set.Ioi c, f ((b : ℂ) + y * I)) * I
              - 0
              - (∫ y in Set.Ioi c, f ((a : ℂ) + y * I)) * I)) :=
    ((h_lim_bottom.add h_lim_right_I).sub h_top_vanish).sub h_lim_left_I
  -- The function is eventually 0, so the limit is 0.
  have h_eventually_zero :
      Tendsto
        (fun R : ℝ =>
          (∫ x in a..b, f ((x : ℂ) + c * I))
            + (∫ y in c..R, f ((b : ℂ) + y * I)) * I
            - (∫ x in a..b, f ((x : ℂ) + R * I))
            - (∫ y in c..R, f ((a : ℂ) + y * I)) * I) atTop (𝓝 0) :=
    Tendsto.congr' (h_eq.mono fun _ h => h.symm) tendsto_const_nhds
  -- Conclude by uniqueness of limits.
  have h_eq_lim : (∫ x in a..b, f ((x : ℂ) + c * I))
        + (∫ y in Set.Ioi c, f ((b : ℂ) + y * I)) * I
        - 0
        - (∫ y in Set.Ioi c, f ((a : ℂ) + y * I)) * I = 0 :=
    tendsto_nhds_unique h_lim_total h_eventually_zero
  -- The `- 0` term drops.
  linear_combination h_eq_lim

end LeanModularForms

end
