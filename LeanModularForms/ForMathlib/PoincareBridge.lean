/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.PiecewiseContourIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Convex Domain Primitives (Poincare Bridge)

This file provides the bridge between the holomorphic primitive theorem on convex domains
and the piecewise C¹ contour integration framework. The main results are:

1. A holomorphic function on a convex open set has a holomorphic primitive.
2. Cauchy's theorem for convex domains: the contour integral of a holomorphic function
   along a closed piecewise C¹ path in a convex set vanishes.

## Main results

* `DifferentiableOn.hasPrimitive_of_convex` — if `f` is holomorphic on a convex open set `U`,
  then there exists `F` with `HasDerivAt F (f z) z` for all `z ∈ U`.
* `DifferentiableOn.isExactOn_convex` — same result using mathlib's `Complex.IsExactOn`.
* `contourIntegral_eq_zero_of_differentiableOn_convex_aux` — Cauchy's theorem: the contour
  integral of a holomorphic function along a closed piecewise C¹ path in a convex open set is
  zero, assuming integrability of the integrand.

## References

* R. B. Ash, W. P. Novinger, *Complex Variables*, Theorem 2.6.2
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ### Primitives on convex domains -/

/-- A holomorphic function on a convex open set has a holomorphic primitive.

If `f` is differentiable on a convex open set `U`, then there exists `F : ℂ → ℂ` such that
`HasDerivAt F (f z) z` for all `z ∈ U`. The proof uses the segment-integral construction
`F(z) = ∫₀¹ f(c + t(z-c)) · (z-c) dt` from a fixed basepoint `c ∈ U`. -/
theorem DifferentiableOn.hasPrimitive_of_convex {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : Convex ℝ U) (hUo : IsOpen U)
    (_ : U.Nonempty) :
    ∃ F : ℂ → ℂ, ∀ z ∈ U, HasDerivAt F (f z) z := by
  obtain ⟨F, hF⟩ := hU.exists_forall_hasDerivWithinAt hf
  exact ⟨F, fun z hz ↦ (hF z hz).hasDerivAt (hUo.mem_nhds hz)⟩

/-- A holomorphic function on a convex open set has a primitive, stated using
mathlib's `Complex.IsExactOn`. -/
theorem DifferentiableOn.isExactOn_convex {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : Convex ℝ U) (hUo : IsOpen U)
    (hUne : U.Nonempty) :
    Complex.IsExactOn f U :=
  hf.hasPrimitive_of_convex hU hUo hUne

/-- The primitive from `hasPrimitive_of_convex` is itself differentiable on `U`. -/
theorem DifferentiableOn.primitive_differentiableOn {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : Convex ℝ U) (hUo : IsOpen U)
    (hUne : U.Nonempty) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, HasDerivAt F (f z) z := by
  obtain ⟨F, hF⟩ := hf.hasPrimitive_of_convex hU hUo hUne
  exact ⟨F, fun z hz ↦ (hF z hz).differentiableAt.differentiableWithinAt, hF⟩

/-! ### Cauchy's theorem for convex domains -/

namespace PiecewiseC1Path

variable {x y : ℂ}

/-- **Cauchy's theorem for convex domains (with integrability hypothesis).**

If `f` is holomorphic on a convex open nonempty set `U` and `γ` is a closed piecewise C¹
path whose image lies in `U`, then the contour integral of `f` along `γ` is zero.

This version requires the integrability of the contour integrand as a hypothesis. -/
theorem contourIntegral_eq_zero_of_differentiableOn_convex_aux {f : ℂ → ℂ}
    {U : Set ℂ} (γ : PiecewiseC1Path x y) (hclosed : x = y)
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    (hf : DifferentiableOn ℂ f U)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f = 0 := by
  obtain ⟨F, hF⟩ := hf.hasPrimitive_of_convex hU hUo hUne
  exact contourIntegral_eq_zero_of_hasDerivAt_of_closed γ hclosed hγ hF h_int

/-- **Cauchy's theorem for convex domains (FTC formulation).**

If `f` is holomorphic on a convex open nonempty set `U` and `γ` is a piecewise C¹
path whose image lies in `U`, then the contour integral of `f` along `γ` equals
`F(y) - F(x)` for any primitive `F` of `f` on `U`.

end PiecewiseC1Path

/-! ### Path-free formulation using `Complex.IsExactOn` -/

/-- If `f` is exact (has a primitive) on `U`, then the contour integral of `f` along any
piecewise C¹ path in `U` equals the difference of the primitive at the endpoints. -/
theorem Complex.IsExactOn.contourIntegral_eq_sub {f : ℂ → ℂ} {U : Set ℂ}
    {x y : ℂ} (hf : Complex.IsExactOn f U)
    (γ : PiecewiseC1Path x y)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1) :
    ∃ F : ℂ → ℂ, γ.contourIntegral f = F y - F x ∧
      ∀ z ∈ U, HasDerivAt F (f z) z := by
  obtain ⟨F, hF⟩ := hf
  exact ⟨F, γ.contourIntegral_eq_sub_of_hasDerivAt hγ hF h_int, hF⟩

/-- If `f` is exact (has a primitive) on `U`, then the contour integral of `f` along any
closed piecewise C¹ path in `U` is zero. -/
theorem Complex.IsExactOn.contourIntegral_eq_zero_of_closed {f : ℂ → ℂ} {U : Set ℂ}
    {x : ℂ} (hf : Complex.IsExactOn f U)
    (γ : PiecewiseC1Path x x)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f = 0 := by
  obtain ⟨F, hF⟩ := hf
  exact γ.contourIntegral_eq_zero_of_hasDerivAt_of_closed rfl hγ hF h_int

end
