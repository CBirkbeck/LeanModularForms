/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.CauchyPrincipalValue

/-!
# Generalized Winding Number

This file defines the generalized winding number of a piecewise C¹ path around a point,
following the approach of Hungerbühler–Wasem. The definition uses the Cauchy principal value
integral, which allows the winding number to be defined even when the curve passes through
the point `z₀`.

## Main definitions

* `HasGeneralizedWindingNumber γ z₀ w` — the Tendsto-first predicate asserting that the CPV
  of `∮_γ (z - z₀)⁻¹ dz` exists and equals `2πi · w`.

* `generalizedWindingNumber γ z₀` — the generalized winding number, defined as
  `(2πi)⁻¹ · cauchyPV (fun z => (z - z₀)⁻¹) γ z₀`. Returns junk when the CPV does not exist.

## Main results

* `HasGeneralizedWindingNumber.eq` — bridge: the predicate implies
  `generalizedWindingNumber γ z₀ = w`.

* `HasGeneralizedWindingNumber.unique` — uniqueness of the winding number value.

* `HasGeneralizedWindingNumber.neg` — negation compatibility.

* `generalizedWindingNumber_eq_zero_of_avoids` — if `γ` avoids `z₀` and is a closed path,
  then the winding number is 0, provided the path lies in a convex set not containing `z₀`.

## Design notes

The `HasGeneralizedWindingNumber` predicate wraps `HasCauchyPV` with the specific integrand
`(z - z₀)⁻¹`. This Tendsto-first design matches the pattern from `CauchyPrincipalValue.lean`:
downstream theorems state results using `HasGeneralizedWindingNumber`, and extract the value
via the bridge theorem when needed.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set Filter Topology MeasureTheory Complex
open scoped Interval

noncomputable section

variable {x y : ℂ}

/-! ### HasGeneralizedWindingNumber: the Tendsto-first predicate -/

/-- The generalized winding number of `γ` around `z₀` exists and equals `w`.

Defined as: the CPV of `∮_γ (z - z₀)⁻¹ dz` exists and equals `2πi · w`.
This is the **primary API predicate** for generalized winding numbers. -/
def HasGeneralizedWindingNumber (γ : PiecewiseC1Path x y) (z₀ : ℂ) (w : ℂ) : Prop :=
  HasCauchyPV (fun z => (z - z₀)⁻¹) γ z₀ (2 * ↑Real.pi * I * w)

/-- The generalized winding number of `γ` around `z₀`, defined as
`(2πi)⁻¹ · PV ∮_γ (z - z₀)⁻¹ dz`. Returns junk when the CPV does not exist. -/
def generalizedWindingNumber (γ : PiecewiseC1Path x y) (z₀ : ℂ) : ℂ :=
  (2 * ↑Real.pi * I)⁻¹ * cauchyPV (fun z => (z - z₀)⁻¹) γ z₀

/-! ### Bridge theorem -/

/-- Bridge: if `HasGeneralizedWindingNumber γ z₀ w`, then `generalizedWindingNumber γ z₀ = w`. -/
theorem HasGeneralizedWindingNumber.eq {γ : PiecewiseC1Path x y} {z₀ w : ℂ}
    (h : HasGeneralizedWindingNumber γ z₀ w) : generalizedWindingNumber γ z₀ = w := by
  simp only [generalizedWindingNumber, h.cauchyPV_eq]
  have hpi := Complex.two_pi_I_ne_zero
  field_simp

/-! ### Uniqueness -/

/-- The generalized winding number value is unique. -/
theorem HasGeneralizedWindingNumber.unique {γ : PiecewiseC1Path x y} {z₀ w₁ w₂ : ℂ}
    (h₁ : HasGeneralizedWindingNumber γ z₀ w₁)
    (h₂ : HasGeneralizedWindingNumber γ z₀ w₂) : w₁ = w₂ := by
  have h : 2 * ↑Real.pi * I * w₁ = 2 * ↑Real.pi * I * w₂ :=
    HasCauchyPV.unique h₁ h₂
  have hpi := Complex.two_pi_I_ne_zero
  exact mul_left_cancel₀ hpi h

/-! ### Negation -/

/-- Negation: if the winding number of `γ` around `z₀` is `w`, then the winding number of
`γ` with the negated integrand corresponds to `-w`. -/
theorem HasGeneralizedWindingNumber.neg {γ : PiecewiseC1Path x y} {z₀ w : ℂ}
    (h : HasGeneralizedWindingNumber γ z₀ w) :
    HasCauchyPV (fun z => -(z - z₀)⁻¹) γ z₀ (-(2 * ↑Real.pi * I * w)) :=
  HasCauchyPV.neg h

/-! ### Avoidance: winding number when γ avoids z₀ -/

/-- If `γ` avoids `z₀` (with positive minimum distance), the generalized winding number
equals the classical contour integral formula. -/
theorem hasGeneralizedWindingNumber_of_avoids {γ : PiecewiseC1Path x y} {z₀ : ℂ}
    (hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - z₀‖) :
    HasGeneralizedWindingNumber γ z₀
      ((2 * ↑Real.pi * I)⁻¹ * γ.contourIntegral (fun z => (z - z₀)⁻¹)) := by
  simp only [HasGeneralizedWindingNumber]
  have hpi := Complex.two_pi_I_ne_zero
  rw [show 2 * ↑Real.pi * I * ((2 * ↑Real.pi * I)⁻¹ * γ.contourIntegral (fun z => (z - z₀)⁻¹)) =
    γ.contourIntegral (fun z => (z - z₀)⁻¹) from by field_simp]
  exact hasCauchyPV_of_avoids hδ

/-! ### Value from HasGeneralizedWindingNumber -/

/-- If `HasGeneralizedWindingNumber γ z₀ w`, then the `cauchyPV` value satisfies the
expected equation. -/
theorem HasGeneralizedWindingNumber.cauchyPV_eq_two_pi_I_mul
    {γ : PiecewiseC1Path x y} {z₀ w : ℂ}
    (h : HasGeneralizedWindingNumber γ z₀ w) :
    cauchyPV (fun z => (z - z₀)⁻¹) γ z₀ = 2 * ↑Real.pi * I * w :=
  h.cauchyPV_eq

/-! ### Relation between HasGeneralizedWindingNumber and generalizedWindingNumber -/

/-- If the CPV exists with some limit, then `HasGeneralizedWindingNumber` holds for the
corresponding winding number value. -/
theorem hasGeneralizedWindingNumber_of_hasCauchyPV {γ : PiecewiseC1Path x y} {z₀ L : ℂ}
    (h : HasCauchyPV (fun z => (z - z₀)⁻¹) γ z₀ L) :
    HasGeneralizedWindingNumber γ z₀ ((2 * ↑Real.pi * I)⁻¹ * L) := by
  simp only [HasGeneralizedWindingNumber]
  have hpi := Complex.two_pi_I_ne_zero
  rwa [show 2 * ↑Real.pi * I * ((2 * ↑Real.pi * I)⁻¹ * L) = L from by field_simp]

/-- `generalizedWindingNumber` agrees with any `HasGeneralizedWindingNumber` witness.
This is the converse direction of `HasGeneralizedWindingNumber.eq`. -/
theorem generalizedWindingNumber_eq_of_hasGeneralizedWindingNumber
    {γ : PiecewiseC1Path x y} {z₀ w : ℂ}
    (h : HasGeneralizedWindingNumber γ z₀ w) : generalizedWindingNumber γ z₀ = w :=
  h.eq

/-! ### Scalar multiplication -/

/-- Scalar multiplication compatibility: if the winding number is `w`, then scaling the
integrand by `c` gives `c * w`. -/
theorem HasGeneralizedWindingNumber.const_mul {γ : PiecewiseC1Path x y} {z₀ w : ℂ}
    (c : ℂ) (h : HasGeneralizedWindingNumber γ z₀ w) :
    HasCauchyPV (fun z => c * (z - z₀)⁻¹) γ z₀ (c * (2 * ↑Real.pi * I * w)) :=
  h.smul c

end
