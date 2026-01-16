/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.RingTheory.LaurentSeries

/-!
# Basic Definitions for Complex Analysis with Principal Values

This file contains the core definitions used throughout the complex analysis
formalization, including piecewise C¹ curves, principal value integrals,
and generalized winding numbers.

## Main Definitions

* `PiecewiseC1Curve'` - A piecewise continuously differentiable curve
* `PiecewiseC1Immersion'` - A piecewise C¹ curve with nonzero derivative
* `CauchyPrincipalValue` - The Cauchy principal value integral
* `CauchyPrincipalValueExists` - Predicate for PV existence
* `GeneralizedWindingNumber` - Winding number via principal values

## References

* Isabelle's HOL-Complex_Analysis library
* [Ahlfors, *Complex Analysis*]
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ## Piecewise C¹ Curves -/

/-- A piecewise continuously differentiable curve γ : [a,b] → ℂ.
    The curve is C¹ on each subinterval between partition points. -/
structure PiecewiseC1Curve where
  /-- The underlying function -/
  toFun : ℝ → ℂ
  /-- Left endpoint of the parameter interval -/
  a : ℝ
  /-- Right endpoint of the parameter interval -/
  b : ℝ
  /-- The interval is non-degenerate -/
  hab : a < b
  /-- Finite set of partition points where smoothness may fail -/
  partition : Finset ℝ
  /-- Partition points are in [a,b] -/
  partition_subset : ↑partition ⊆ Icc a b
  /-- Endpoints are in the partition -/
  endpoints_in_partition : a ∈ partition ∧ b ∈ partition
  /-- The function is continuous on [a,b] -/
  continuous_toFun : ContinuousOn toFun (Icc a b)
  /-- The function is C¹ away from partition points -/
  smooth_off_partition : ∀ t ∈ Icc a b, t ∉ partition →
    DifferentiableAt ℝ toFun t
  /-- The derivative is continuous on each smooth piece -/
  deriv_continuous_off_partition : ∀ t ∈ Ioo a b, t ∉ partition →
    ContinuousAt (deriv toFun) t

instance : CoeFun PiecewiseC1Curve (fun _ => ℝ → ℂ) where
  coe := PiecewiseC1Curve.toFun

/-- A closed curve has γ(a) = γ(b) -/
def PiecewiseC1Curve.IsClosed (γ : PiecewiseC1Curve) : Prop :=
  γ.toFun γ.a = γ.toFun γ.b

/-- A piecewise C¹ immersion: a piecewise C¹ curve with nonzero derivative.
    This ensures the curve doesn't "stop" at any point. -/
structure PiecewiseC1Immersion extends PiecewiseC1Curve where
  /-- Derivative is nonzero away from partition points -/
  deriv_ne_zero : ∀ t ∈ Icc a b, t ∉ partition → deriv toFun t ≠ 0
  /-- Left limit of derivative exists and is nonzero at partition points -/
  left_deriv_limit : ∀ p ∈ partition, a < p →
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv toFun) (𝓝[<] p) (𝓝 L)
  /-- Right limit of derivative exists and is nonzero at partition points -/
  right_deriv_limit : ∀ p ∈ partition, p < b →
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv toFun) (𝓝[>] p) (𝓝 L)

/-! ## Cauchy Principal Value -/

/-- The Cauchy principal value of ∮_γ f(z) dz, excluding ε-neighborhoods of z₀.

    PV ∮_γ f = lim_{ε→0⁺} ∫_{t : ‖γ(t) - z₀‖ > ε} f(γ(t)) · γ'(t) dt
-/
def cauchyPrincipalValue' (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

/-- The integrand for the Cauchy principal value at a given ε. -/
def cauchyPrincipalValueIntegrand' (f : ℂ → ℂ) (γ : ℝ → ℂ) (z₀ : ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

/-- The Cauchy principal value exists if the limit exists. -/
def CauchyPrincipalValueExists' (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∃ L : ℂ, Tendsto (fun ε =>
    ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
    (𝓝[>] 0) (𝓝 L)

/-! ## Generalized Winding Number -/

/-- The generalized winding number of γ around z₀, defined via principal value.

    n_{z₀}(γ) = (1/2πi) · PV ∮_γ dz/(z - z₀)

    This equals the classical winding number when γ avoids z₀, and can take
    non-integer values when γ passes through z₀.
-/
def generalizedWindingNumber' (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * cauchyPrincipalValue' (·⁻¹) (fun t => γ t - z₀) a b 0

/-! ## Model Sector Curve -/

/-- A model sector curve: the standard curve for computing angle contributions.

    The curve goes from r to 0 along the positive real axis, then from 0 to r·e^{iα}
    along the ray at angle α. The principal value integral gives α/(2π).
-/
structure ModelSectorCurve where
  /-- Radius of the sector -/
  r : ℝ
  /-- Radius is positive -/
  hr : 0 < r
  /-- Angle of the sector -/
  α : ℝ
  /-- Angle is nonnegative -/
  hα_nonneg : 0 ≤ α
  /-- Angle is at most 2π -/
  hα_le : α ≤ 2 * Real.pi

/-- First leg of model sector: from r to ε along positive real axis -/
def ModelSectorCurve.γ₁ (C : ModelSectorCurve) : ℝ → ℂ := fun t => t

/-- Second leg: arc at the origin (degenerate, but conceptually the angle contribution) -/
def ModelSectorCurve.γ₂ (C : ModelSectorCurve) : ℝ → ℂ := fun t => C.r * exp (I * t)

/-- Third leg: from 0 to r along the ray at angle α -/
def ModelSectorCurve.γ₃ (C : ModelSectorCurve) : ℝ → ℂ := fun t => t * exp (I * C.α)

/-! ## Residue -/

/-- The residue of f at z₀, defined as the coefficient of (z - z₀)⁻¹ in the
    Laurent expansion of f around z₀.

    For a simple pole: res_{z₀}(f) = lim_{z→z₀} (z - z₀) · f(z)
-/
def residue' (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  -- Using the limit definition for simple poles
  -- For general poles, would need Laurent series coefficient
  limUnder (𝓝[≠] z₀) fun z => (z - z₀) * f z

/-- Alternative residue definition via contour integral (Isabelle style).
    res_{z₀}(f) = (1/2πi) ∮_{|z-z₀|=ε} f(z) dz for small ε
-/
def residueIntegral' (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * ∮ z in C(z₀, 1), f z

/-! ## Homotopy of Curves -/

/-- Two curves are homotopic relative to endpoints if there exists a continuous
    deformation H : [a,b] × [0,1] → ℂ with:
    - H(t, 0) = Γ(t) and H(t, 1) = γ(t)
    - H(a, s) and H(b, s) are constant in s
    - H(t, s) ≠ z₀ for all interior t and all s (if avoiding z₀)
-/
def CurvesHomotopic (Γ γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    Continuous H ∧
    (∀ t ∈ Icc a b, H (t, 0) = Γ t) ∧
    (∀ t ∈ Icc a b, H (t, 1) = γ t) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, H (a, s) = H (a, 0) ∧ H (b, s) = H (b, 0))

/-- Homotopy avoiding a point z₀ (for winding number invariance) -/
def CurvesHomotopicAvoiding (Γ γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    Continuous H ∧
    (∀ t ∈ Icc a b, H (t, 0) = Γ t) ∧
    (∀ t ∈ Icc a b, H (t, 1) = γ t) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, H (a, s) = z₀ ∧ H (b, s) = z₀) ∧
    (∀ t ∈ Ioo a b, ∀ s ∈ Icc (0 : ℝ) 1, H (t, s) ≠ z₀)

end
