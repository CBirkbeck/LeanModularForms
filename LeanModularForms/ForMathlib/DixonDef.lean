/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.SimplePoleIntegral
import Mathlib.Analysis.Calculus.DSlope

/-!
# Dixon Function Definitions and the h1/h2 Identity

This file defines the Dixon h1 and h2 functions and proves the fundamental identity
relating them. These are the core building blocks for Dixon's proof of the homological
Cauchy integral formula.

## Main definitions

* `dixonH1` -- the Dixon integral `∮_γ dslope(f, w, γ(t)) · γ'(t) dt`.
  Well-defined for all `w`, including points on the curve.
* `dixonH2` -- the Cauchy-type integral `∮_γ f(γ(t))/(γ(t) - w) · γ'(t) dt`.
  Well-defined for `w` off the curve.
* `dixonFunction` -- piecewise: `h1` on `U`, `h2` off `U`.

## Main results

* `dixonH1_eq_dixonH2_sub_winding_f` -- the key identity:
  `h1(w) = h2(w) - 2πi · n(γ, w) · f(w)` for `w` off the curve.

## Design notes

The definitions use `PiecewiseC1Path x x` (closed paths) from the ForMathlib infrastructure,
with `dslope` from mathlib. The h1/h2 identity follows from expanding `dslope` into
`(f(z) - f(w))/(z - w) = f(z)/(z - w) - f(w)/(z - w)` and splitting the integral.

The `dslope f w (γ t)` has center `w` (second argument) and evaluation point `γ t`
(third argument): `dslope f a b = (f b - f a) / (b - a)` when `b ≠ a`, and
`dslope f a a = deriv f a`.

## References

* J. D. Dixon, *A brief proof of Cauchy's integral theorem*, 1971
* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set Filter Topology MeasureTheory
open scoped Classical Real Interval

noncomputable section

variable {x : ℂ}

/-! ## Definitions -/

/-- The Dixon h1 function: `∮_γ dslope(f, w, γ(t)) · γ'(t) dt`.

This is well-defined for all `w` including points on the curve, because
`dslope f w z` is continuous in `z` even at `z = w` (where it equals `deriv f w`). -/
def dixonH1 (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (w : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, dslope f w (γ t) * deriv γ.toPath.extend t

/-- The Dixon h2 function: `∮_γ f(γ(t))/(γ(t) - w) · γ'(t) dt`.

This is the standard Cauchy-type integral, well-defined for `w` off the curve. -/
def dixonH2 (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (w : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, f (γ t) / (γ t - w) * deriv γ.toPath.extend t

/-- The Dixon function: `h1` on `U`, `h2` off `U`.

This piecewise construction is the key to Dixon's proof: both pieces are analytic
(h1 on U, h2 on the complement of the curve image), and they agree on the overlap
by the h1/h2 identity, yielding an entire function. -/
def dixonFunction (f : ℂ → ℂ) (U : Set ℂ)
    (γ : PiecewiseC1Path x x) (w : ℂ) : ℂ :=
  if w ∈ U then dixonH1 f γ w else dixonH2 f γ w

/-! ## The h1/h2 Identity -/

/-- Pointwise identity: when `γ(t) ≠ w`, the dslope integrand equals the difference of
the Cauchy integrand and the winding integrand.

Uses `dslope f w (γ t) = slope f w (γ t) = (f(γ t) - f(w)) / (γ t - w)`. -/
private lemma dslope_integrand_eq {f : ℂ → ℂ} {γ : PiecewiseC1Path x x} {w : ℂ}
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      dslope f w (γ t) * deriv γ.toPath.extend t =
        f (γ t) / (γ t - w) * deriv γ.toPath.extend t -
          f w / (γ t - w) * deriv γ.toPath.extend t := by
  intro t ht
  have ht_Icc : t ∈ Icc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one] at ht
  have hne : γ t ≠ w := hoff t ht_Icc
  rw [dslope_of_ne _ hne, slope_def_field]
  have hsub : γ t - w ≠ 0 := sub_ne_zero.mpr hne
  field_simp

/-- The winding integrand `f(w)/(γ(t) - w) · γ'(t)` equals `f(w) · (γ(t) - w)⁻¹ · γ'(t)`. -/
private lemma winding_integrand_eq_const_mul (f : ℂ → ℂ)
    (γ : PiecewiseC1Path x x) (w : ℂ) :
    (fun t => f w / (γ t - w) * deriv γ.toPath.extend t) =
      (fun t => f w * ((γ t - w)⁻¹ * deriv γ.toPath.extend t)) := by
  ext t
  rw [div_eq_mul_inv]
  ring

/-- The contour integral of `f(w)/(z - w)` equals `f(w)` times the contour integral
of `(z - w)⁻¹`. -/
private lemma contourIntegral_fw_div_eq (f : ℂ → ℂ)
    (γ : PiecewiseC1Path x x) (w : ℂ) :
    ∫ t in (0 : ℝ)..1, f w / (γ t - w) * deriv γ.toPath.extend t =
      f w * γ.contourIntegral (fun z => (z - w)⁻¹) := by
  simp only [PiecewiseC1Path.contourIntegral]
  rw [winding_integrand_eq_const_mul f γ w]
  exact intervalIntegral.integral_const_mul _ _

/-- When the path avoids `w`, the winding integrand `f(w)/(γ(t) - w) · γ'(t)` is
interval integrable provided the base integrand `(γ(t) - w)⁻¹ · γ'(t)` is. -/
private lemma winding_integrand_intervalIntegrable (f : ℂ → ℂ)
    (γ : PiecewiseC1Path x x) (w : ℂ)
    (h_base : IntervalIntegrable
      (fun t => (γ t - w)⁻¹ * deriv γ.toPath.extend t) volume 0 1) :
    IntervalIntegrable
      (fun t => f w / (γ t - w) * deriv γ.toPath.extend t) volume 0 1 := by
  rw [winding_integrand_eq_const_mul f γ w]
  exact h_base.const_mul _

/-- If a piecewise C^1 path avoids a point, there is a positive distance lower bound. -/
private theorem avoids_delta_bound (γ : PiecewiseC1Path x x) (w : ℂ)
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - w‖ := by
  have h_compact : IsCompact (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image γ.toPath.continuous_extend
  have h_nonempty : (γ.toPath.extend '' Icc (0 : ℝ) 1).Nonempty :=
    ⟨γ.toPath.extend 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩
  have h_not_mem : w ∉ γ.toPath.extend '' Icc (0 : ℝ) 1 :=
    fun ⟨t, ht, heq⟩ => hoff t ht heq
  have h_pos : 0 < Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
    (h_compact.isClosed.notMem_iff_infDist_pos h_nonempty).mp h_not_mem
  exact ⟨_, h_pos, fun t ht => by
    calc Metric.infDist w _ ≤ dist w (γ.toPath.extend t) :=
          Metric.infDist_le_dist_of_mem (mem_image_of_mem _ ht)
      _ = ‖γ.toPath.extend t - w‖ := by rw [Complex.dist_eq, norm_sub_rev]⟩

/-- **The fundamental h1/h2 identity.**

For a closed piecewise C^1 path `γ` and a point `w` off the curve:

  `h1(w) = h2(w) - 2πi · n(γ, w) · f(w)`

where `n(γ, w)` is the generalized winding number.

The proof expands `dslope f w (γ t) = (f(γ t) - f(w)) / (γ t - w)` (since `γ t ≠ w`),
splits into `f(γ t)/(γ t - w) - f(w)/(γ t - w)`, and identifies the second term as
`f(w) · ∮ (z - w)⁻¹ dz = 2πi · n(γ, w) · f(w)`. -/
theorem dixonH1_eq_dixonH2_sub_winding_f {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x x}
    (w : ℂ) (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w)
    (h_cauchy_int : IntervalIntegrable
      (fun t => f (γ t) / (γ t - w) * deriv γ.toPath.extend t) volume 0 1)
    (h_base_int : IntervalIntegrable
      (fun t => (γ t - w)⁻¹ * deriv γ.toPath.extend t) volume 0 1) :
    dixonH1 f γ w =
      dixonH2 f γ w - 2 * ↑Real.pi * I * generalizedWindingNumber γ w * f w := by
  simp only [dixonH1, dixonH2]
  -- Step 1: expand dslope and split the integral
  rw [intervalIntegral.integral_congr (dslope_integrand_eq hoff)]
  rw [intervalIntegral.integral_sub h_cauchy_int
    (winding_integrand_intervalIntegrable f γ w h_base_int)]
  -- Step 2: identify the winding number term
  congr 1
  -- Goal: ∫ f(w)/(γ t - w) · γ'(t) dt = 2πi · n(γ,w) · f(w)
  rw [contourIntegral_fw_div_eq f γ w]
  -- Now need: f(w) * ∮ (z-w)⁻¹ = 2πi · n(γ,w) · f(w)
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := avoids_delta_bound γ w hoff
  rw [integral_inv_sub_eq_winding ⟨δ, hδ_pos, hδ_bound⟩]
  ring

/-- Variant of the h1/h2 identity with the winding number on the other side. -/
theorem dixonH2_eq_dixonH1_add_winding_f {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x x}
    (w : ℂ) (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w)
    (h_cauchy_int : IntervalIntegrable
      (fun t => f (γ t) / (γ t - w) * deriv γ.toPath.extend t) volume 0 1)
    (h_base_int : IntervalIntegrable
      (fun t => (γ t - w)⁻¹ * deriv γ.toPath.extend t) volume 0 1) :
    dixonH2 f γ w =
      dixonH1 f γ w + 2 * ↑Real.pi * I * generalizedWindingNumber γ w * f w := by
  have h := dixonH1_eq_dixonH2_sub_winding_f w hoff h_cauchy_int h_base_int
  linear_combination -h

/-! ## Dixon function agreement lemmas -/

/-- On `U`, the Dixon function equals `h1`. -/
theorem dixonFunction_eq_dixonH1 {f : ℂ → ℂ} {U : Set ℂ}
    {γ : PiecewiseC1Path x x} {w : ℂ} (hw : w ∈ U) :
    dixonFunction f U γ w = dixonH1 f γ w :=
  if_pos hw

/-- Off `U`, the Dixon function equals `h2`. -/
theorem dixonFunction_eq_dixonH2 {f : ℂ → ℂ} {U : Set ℂ}
    {γ : PiecewiseC1Path x x} {w : ℂ} (hw : w ∉ U) :
    dixonFunction f U γ w = dixonH2 f γ w :=
  if_neg hw

/-! ## Reformulations using contourIntegral -/

/-- `dixonH2` expressed using the contour integral notation. -/
theorem dixonH2_eq_contourIntegral' {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x x} {w : ℂ} :
    dixonH2 f γ w = γ.contourIntegral (fun z => f z / (z - w)) := by
  simp only [dixonH2, PiecewiseC1Path.contourIntegral]

/-- `dixonH1` expressed using the contour integral notation. -/
theorem dixonH1_eq_contourIntegral' {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x x} {w : ℂ} :
    dixonH1 f γ w = γ.contourIntegral (fun z => dslope f w z) := by
  simp only [dixonH1, PiecewiseC1Path.contourIntegral]

end
