/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.NullHomologous
import LeanModularForms.ForMathlib.PoincareBridge
import LeanModularForms.ForMathlib.HomotopyInvariance
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Dixon's Approach to the Cauchy Integral Formula

The Dixon kernel `g(z, w) = (f(z) - f(w))/(z - w)` (extended to `f'(w)` at `z = w`)
is exactly mathlib's `dslope f z w`. The key insight is that for `f` holomorphic on
an open set `U` and `z ∈ U`, the function `w ↦ dslope f z w` is holomorphic on `U`
(by the removable singularity theorem). By `slope_comm`, this is equivalent to
`z ↦ dslope f z w` being holomorphic on `U` for any fixed `w`.

## Main definitions

* `dixonH1` -- the Dixon integral `h₁(w) = ∮_γ dslope(f, γ(t), w) · γ'(t) dt`
* `dixonH2` -- the Cauchy-type integral `h₂(w) = ∮_γ f(z)/(z-w) · γ'(t) dt`
* `dixonFunction` -- piecewise: `h₁` on `U`, `h₂` outside `U`

## Main results

* `differentiableOn_dslope_fst` -- for `f` holomorphic on open `U` and any `w`,
  the function `z ↦ dslope f z w` is holomorphic on `U`.

* `dixonH1_eq_zero_of_convex` -- `h₁(w) = 0` for convex domains (by FTC).

* `dixonH1_add_winding_eq_dixonH2` -- the key identity:
  `h₁(w) + f(w) · ∮_γ (z-w)⁻¹ dz = h₂(w)` when `γ` avoids `w`.

* `cauchyIntegralFormula_convex` -- Cauchy integral formula for convex domains:
  `∮_γ f(z)/(z-w) dz = f(w) · ∮_γ (z-w)⁻¹ dz`.

* `contourIntegral_eq_zero_of_holomorphic_nullHomologous` -- vanishing theorem:
  the contour integral of a holomorphic function along a null-homologous path in a
  convex domain vanishes.

* `dixonFunction_eq_zero_of_convex` -- the Dixon function is identically zero on
  convex domains.

## Design notes

The full Dixon theorem (for arbitrary open sets) requires showing that the piecewise
Dixon function `h(w) = h₁(w)` on `U`, `h(w) = h₂(w)` off `U` is entire, bounded,
and tends to zero, then applying Liouville's theorem. This requires ~500 lines of
differentiation-under-the-integral arguments and is provided separately in
`GeneralizedResidueTheory/HomologicalCauchy/DixonProof.lean`.

This file provides the convex-domain specialisation, which suffices for many
applications and avoids the heavy machinery. The definitions and helper lemmas
are structured to be reusable by the full proof.

## References

* J. D. Dixon, *A brief proof of Cauchy's integral theorem*, Proc. AMS (1971)
* R. B. Ash, W. P. Novinger, *Complex Variables*, Chapter 2
-/

open Complex Set Filter Topology MeasureTheory intervalIntegral PiecewiseC1Path
open scoped Real Interval Classical

noncomputable section

variable {x : ℂ}

/-! ### The Dixon kernel -/

/-- The Dixon kernel is exactly `dslope`: `dixonKernel f z w = dslope f z w`.

For `z ≠ w`, this equals `(f w - f z) / (w - z)`. At `z = w`, it equals `deriv f z`.
We use `dslope` directly rather than a custom definition so that all of mathlib's
`dslope` API applies without coercion. -/
abbrev dixonKernel (f : ℂ → ℂ) (z w : ℂ) : ℂ := dslope f z w

/-! ### The Dixon integrals -/

/-- `h₁(w) = ∮_γ dslope(f, γ(t), w) · γ'(t) dt` -- the Dixon integral.

This is the contour integral of `z ↦ dslope f z w` along `γ`. When `f` is holomorphic
on an open set `U` containing the image of `γ`, `h₁` is holomorphic on all of `U`
(including points on the curve), because `dslope` removes the singularity. -/
def dixonH1 (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (w : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, dslope f (γ t) w * deriv γ.toPath.extend t

/-- `h₂(w) = ∮_γ f(z)/(z-w) · γ'(t) dt` -- the Cauchy-type integral.

This is the contour integral of `z ↦ f(z)/(z - w)` along `γ`. It is holomorphic
on `ℂ \ image(γ)`, i.e., at every point not on the curve. -/
def dixonH2 (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (w : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, f (γ t) / (γ t - w) * deriv γ.toPath.extend t

/-- `dixonH1` equals the contour integral of `z ↦ dslope f z w`. -/
theorem dixonH1_eq_contourIntegral (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (w : ℂ) :
    dixonH1 f γ w = γ.contourIntegral (fun z => dslope f z w) := rfl

/-- `dixonH2` equals the contour integral of `z ↦ f z / (z - w)`. -/
theorem dixonH2_eq_contourIntegral (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (w : ℂ) :
    dixonH2 f γ w = γ.contourIntegral (fun z => f z / (z - w)) := rfl

/-! ### Holomorphicity of the Dixon kernel in the first variable -/

/-- For `f` holomorphic on an open set `U` and any `w`, the function `z ↦ dslope f z w`
is holomorphic on `U`.

The proof uses the symmetry `dslope f z w = dslope f w z` (from `slope_comm`) to
reduce to the standard mathlib result about `dslope` in the second variable:
* For `w ∈ U`: `Complex.differentiableOn_dslope` (removable singularity).
* For `w ∉ U`: `differentiableOn_dslope_of_notMem` (no singularity in `U`). -/
theorem differentiableOn_dslope_fst {f : ℂ → ℂ} {U : Set ℂ} {w : ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) :
    DifferentiableOn ℂ (fun z => dslope f z w) U := by
  have heq : ∀ z, dslope f z w = dslope f w z := by
    intro z
    by_cases h : z = w
    · subst h; simp [dslope_same]
    · simp only [dslope_of_ne _ (Ne.symm h), dslope_of_ne _ h, slope_comm]
  simp_rw [heq]
  by_cases hw : w ∈ U
  · exact (Complex.differentiableOn_dslope (hU.mem_nhds hw)).mpr hf
  · exact (differentiableOn_dslope_of_notMem hw).mpr hf

/-! ### Key identity: h₁ + winding = h₂ -/

/-- Pointwise identity: `dslope f z w * c + f(w) * ((z-w)⁻¹ * c) = f(z) * ((z-w)⁻¹ * c)`
when `z ≠ w`. This is the algebraic core of the Dixon decomposition. -/
private theorem dslope_add_winding_mul {f : ℂ → ℂ} {z w c : ℂ} (hne : z ≠ w) :
    dslope f z w * c + f w * ((z - w)⁻¹ * c) =
    f z * ((z - w)⁻¹ * c) := by
  rw [dslope_of_ne _ (Ne.symm hne), slope_def_field, div_eq_mul_inv]
  have hinv : (w - z)⁻¹ = -(z - w)⁻¹ := by
    rw [show w - z = -(z - w) from by ring, inv_neg]
  rw [hinv]; ring

/-- **Key identity**: `h₁(w) + f(w) · ∮_γ (z-w)⁻¹ dz = h₂(w)` when `γ` avoids `w`.

This follows from the pointwise identity `dslope f z w + f(w)/(z-w) = f(z)/(z-w)`,
integrated over the curve. The identity decomposes the Cauchy-type integral `h₂` into
the Dixon integral `h₁` (holomorphic across the curve) and a winding number term. -/
theorem dixonH1_add_winding_eq_dixonH2 {f : ℂ → ℂ} {γ : PiecewiseC1Path x x} {w : ℂ}
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w)
    (h_int_h1 : IntervalIntegrable
      (fun t => dslope f (γ t) w * deriv γ.toPath.extend t) volume 0 1)
    (h_int_wn : IntervalIntegrable
      (fun t => (γ t - w)⁻¹ * deriv γ.toPath.extend t) volume 0 1) :
    dixonH1 f γ w + f w * γ.contourIntegral (fun z => (z - w)⁻¹) =
    dixonH2 f γ w := by
  simp only [dixonH1, dixonH2, contourIntegral, div_eq_mul_inv, mul_assoc]
  have h_pull : f w * ∫ t in (0:ℝ)..1, (γ t - w)⁻¹ * deriv γ.toPath.extend t =
    ∫ t in (0:ℝ)..1, f w * ((γ t - w)⁻¹ * deriv γ.toPath.extend t) :=
    (intervalIntegral.integral_const_mul _ _).symm
  rw [h_pull, ← integral_add h_int_h1 (h_int_wn.const_mul _)]
  apply integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  exact dslope_add_winding_mul (hoff t ht')

/-- Equivalent form: `h₁(w) = h₂(w) - f(w) · ∮_γ (z-w)⁻¹ dz`. -/
theorem dixonH1_eq_dixonH2_sub {f : ℂ → ℂ} {γ : PiecewiseC1Path x x} {w : ℂ}
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w)
    (h_int_h1 : IntervalIntegrable
      (fun t => dslope f (γ t) w * deriv γ.toPath.extend t) volume 0 1)
    (h_int_wn : IntervalIntegrable
      (fun t => (γ t - w)⁻¹ * deriv γ.toPath.extend t) volume 0 1) :
    dixonH1 f γ w = dixonH2 f γ w -
      f w * γ.contourIntegral (fun z => (z - w)⁻¹) :=
  eq_sub_of_add_eq (dixonH1_add_winding_eq_dixonH2 hoff h_int_h1 h_int_wn)

/-! ### h₁ vanishes on convex domains -/

/-- `h₁(w) = 0` for any `w` when `f` is holomorphic on a convex domain and `γ` is
a closed path in `U`.

The proof uses `differentiableOn_dslope_fst` to show that `z ↦ dslope f z w` is
holomorphic on `U`, then applies FTC for closed paths in convex domains. -/
theorem dixonH1_eq_zero_of_convex {U : Set ℂ} {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x x} (hnh : IsNullHomologous γ U)
    (hf : DifferentiableOn ℂ f U) (hU : Convex ℝ U)
    (hUo : IsOpen U) (hUne : U.Nonempty) (w : ℂ)
    (h_int : IntervalIntegrable
      (fun t => dslope f (γ t) w * deriv γ.toPath.extend t) volume 0 1) :
    dixonH1 f γ w = 0 :=
  γ.contourIntegral_eq_zero_of_differentiableOn_convex_aux rfl hU hUo hUne
    (differentiableOn_dslope_fst hf hUo) hnh.image_subset h_int

/-! ### Cauchy integral formula for convex domains -/

/-- **Cauchy integral formula for null-homologous paths in convex domains.**

If `f` is holomorphic on a convex open set `U`, `γ` is a closed null-homologous path
in `U`, and `w ∈ U` is a point that `γ` avoids, then:

`∮_γ f(z)/(z-w) dz = f(w) · ∮_γ (z-w)⁻¹ dz`

This follows from the Dixon identity `h₁ + f(w) · winding = h₂` and the fact that
`h₁ = 0` on convex domains. The winding integral
`∮_γ (z-w)⁻¹ dz = 2πi · n(γ, w)` relates to the winding number. -/
theorem cauchyIntegralFormula_convex {U : Set ℂ} {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x x} (hnh : IsNullHomologous γ U)
    (hf : DifferentiableOn ℂ f U) (hU : Convex ℝ U)
    (hUo : IsOpen U) (hUne : U.Nonempty) {w : ℂ} (_ : w ∈ U)
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w)
    (h_int_ds : IntervalIntegrable
      (fun t => dslope f (γ t) w * deriv γ.toPath.extend t) volume 0 1)
    (h_int_wn : IntervalIntegrable
      (fun t => (γ t - w)⁻¹ * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral (fun z => f z / (z - w)) =
      f w * γ.contourIntegral (fun z => (z - w)⁻¹) := by
  have h1_zero := dixonH1_eq_zero_of_convex hnh hf hU hUo hUne w h_int_ds
  have h1_add := dixonH1_add_winding_eq_dixonH2 hoff h_int_ds h_int_wn
  rw [h1_zero, zero_add] at h1_add; exact h1_add.symm

/-! ### Holomorphic integrals vanish on null-homologous paths -/

/-- If `f` is holomorphic on an open set `U` and `w ∉ U`, then `z ↦ f z / (z - w)` is
holomorphic on `U`. -/
theorem differentiableOn_div_sub_of_notMem {U : Set ℂ} {f : ℂ → ℂ} {w : ℂ}
    (hf : DifferentiableOn ℂ f U) (hw : w ∉ U) :
    DifferentiableOn ℂ (fun z => f z / (z - w)) U :=
  hf.div (differentiableOn_id.sub (differentiableOn_const w))
    (fun _ hz => sub_ne_zero.mpr (fun heq => hw (heq ▸ hz)))

/-- The contour integral of `z ↦ f z / (z - w)` vanishes when `f` is holomorphic on a
convex open set `U`, `γ` is null-homologous in `U`, and `w ∉ U`. -/
theorem dixonH2_eq_zero_of_convex_outside {U : Set ℂ} {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x x} (hnh : IsNullHomologous γ U)
    (hf : DifferentiableOn ℂ f U) {w : ℂ} (hw : w ∉ U)
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) / (γ t - w) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral (fun z => f z / (z - w)) = 0 :=
  hnh.contourIntegral_eq_zero (differentiableOn_div_sub_of_notMem hf hw) hU hUo hUne h_int

/-- **Cauchy's theorem for null-homologous paths in convex domains.**

If `f` is holomorphic on a convex open set `U` and `γ` is a closed null-homologous
path in `U`, then `∮_γ f dz = 0`.

This strengthens `IsNullHomologous.contourIntegral_eq_zero` only in documentation;
the proof is identical (FTC + primitive on convex domain). -/
theorem contourIntegral_eq_zero_of_holomorphic_nullHomologous
    {U : Set ℂ} {f : ℂ → ℂ} {γ : PiecewiseC1Path x x}
    (hnh : IsNullHomologous γ U) (hf : DifferentiableOn ℂ f U)
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f = 0 :=
  hnh.contourIntegral_eq_zero hf hU hUo hUne h_int

/-! ### Dixon function definition -/

/-- The **Dixon function**: a piecewise-defined function that combines `h₁` on `U` and
`h₂` outside `U`. When `γ` is null-homologous in `U` and `f` is holomorphic on `U`,
this function is entire (holomorphic on all of `ℂ`), bounded, and tends to zero at
infinity. By Liouville's theorem, it is identically zero.

For the convex case, `h₁ = 0` on `U` by FTC, and `h₂ = 0` outside `U` by Cauchy's
theorem, so the Dixon function is trivially zero.

For the general (non-convex) case, the proof that this function is entire requires
showing that `h₁` and `h₂` agree on `∂U` (using the null-homologous condition to
show the winding number is locally constant and zero near the boundary). This proof
is provided in `GeneralizedResidueTheory/HomologicalCauchy/DixonProof.lean`. -/
def dixonFunction (f : ℂ → ℂ) (U : Set ℂ) (γ : PiecewiseC1Path x x) (w : ℂ) : ℂ :=
  if w ∈ U then dixonH1 f γ w else dixonH2 f γ w

/-- On `U`, the Dixon function equals `h₁`. -/
theorem dixonFunction_eq_dixonH1 {f : ℂ → ℂ} {U : Set ℂ} {γ : PiecewiseC1Path x x}
    {w : ℂ} (hw : w ∈ U) :
    dixonFunction f U γ w = dixonH1 f γ w := if_pos hw

/-- Outside `U`, the Dixon function equals `h₂`. -/
theorem dixonFunction_eq_dixonH2 {f : ℂ → ℂ} {U : Set ℂ} {γ : PiecewiseC1Path x x}
    {w : ℂ} (hw : w ∉ U) :
    dixonFunction f U γ w = dixonH2 f γ w := if_neg hw

/-- The Dixon function is identically zero on convex domains.

For `w ∈ U`: `dixonFunction = h₁ = 0` by FTC (dslope is holomorphic, convex domain).
For `w ∉ U`: `dixonFunction = h₂`, and `h₂ = 0` because `f(z)/(z-w)` is holomorphic
on `U` (since `w ∉ U`) and the contour integral of a holomorphic function on a convex
domain vanishes. -/
theorem dixonFunction_eq_zero_of_convex {U : Set ℂ} {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x x} (hnh : IsNullHomologous γ U)
    (hf : DifferentiableOn ℂ f U) (hU : Convex ℝ U)
    (hUo : IsOpen U) (hUne : U.Nonempty) (w : ℂ)
    (h_int_ds : IntervalIntegrable
      (fun t => dslope f (γ t) w * deriv γ.toPath.extend t) volume 0 1)
    (h_int_h2 : IntervalIntegrable
      (fun t => f (γ t) / (γ t - w) * deriv γ.toPath.extend t) volume 0 1) :
    dixonFunction f U γ w = 0 := by
  simp only [dixonFunction]
  split_ifs with hw
  · exact dixonH1_eq_zero_of_convex hnh hf hU hUo hUne w h_int_ds
  · exact hnh.contourIntegral_eq_zero
      (differentiableOn_div_sub_of_notMem hf hw) hU hUo hUne h_int_h2

end
