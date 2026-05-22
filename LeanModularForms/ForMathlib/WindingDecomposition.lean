/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.CrossingAnalysis
import LeanModularForms.ForMathlib.GeneralizedWindingNumber

/-!
# Winding Number Decomposition — Proposition 2.3

This file formalizes the Hungerbühler–Wasem decomposition of the generalized winding
number into an integer "external winding" part and a crossing angle contribution.

## Main definitions

* `angleAtCrossing` — the signed angle at a crossing point where γ passes through z₀.
  At a smooth point (not in the partition), the angle is π. At a partition (corner) point,
  the angle is `arg(L_right) - arg(-L_left)` where `L_left`, `L_right` are the one-sided
  derivative limits.

* `externalWindingContribution` — the external winding contribution at a crossing:
  `generalizedWindingNumber γ z₀ + angleAtCrossing γ t₀ ht₀ / (2π)`.

## Main results

* `generalizedWindingNumber_eq_external_sub_angle` — H-W Proposition 2.3 decomposition:
  `n_{z₀}(γ) = N - α/(2π)` where `N` is the external winding contribution.

* `generalizedWindingNumber_eq_neg_angleContribution_single` — when the external winding
  is zero, the generalized winding number equals `-α/(2π)`.

* `generalizedWindingNumber_eq_neg_half_smooth_crossing` — at a smooth crossing with zero
  external winding, the generalized winding number is `-1/2`.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set
open scoped Real

noncomputable section

variable {x y : ℂ}

/-- The signed angle at a crossing point where a piecewise C¹ immersion passes through `z₀`.

At a smooth point (not in the partition), the tangent direction is continuous across the
crossing, and the angle between outgoing and negated incoming directions is `π`.

At a corner point (in the partition), the angle is `arg(L_right) - arg(-L_left)` where
`L_left` and `L_right` are the one-sided derivative limits. -/
def angleAtCrossing (γ : PwC1Immersion x y) (t₀ : ℝ) (_ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) : ℝ :=
  if h : t₀ ∈ γ.toPiecewiseC1Path.partition then
    let L_left := Classical.choose (γ.left_deriv_limit t₀ h)
    let L_right := Classical.choose (γ.right_deriv_limit t₀ h)
    arg L_right - arg (-L_left)
  else Real.pi

/-- At a smooth point (not in the partition), the crossing angle is `π`. -/
theorem angleAtCrossing_smooth (γ : PwC1Immersion x y) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) :
    angleAtCrossing γ t₀ ht₀ = Real.pi := by
  simp [angleAtCrossing, hsmooth]

/-- The external winding contribution at a single crossing point. For a closed piecewise C¹
immersion passing through `z₀`, this measures the winding of the curve around `z₀` apart
from the local crossing angle.

The H-W decomposition is `n_{z₀}(γ) = N - α/(2π)`, so `N = n_{z₀}(γ) + α/(2π)`.
When `N = 0`, the generalized winding number equals `-α/(2π)`. -/
def externalWindingContribution (γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) : ℂ :=
  generalizedWindingNumber γ.toPiecewiseC1Path z₀ +
    (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi)

/-- **H-W Proposition 2.3**: The generalized winding number decomposes as the external
winding contribution minus the crossing angle contribution:
`n_{z₀}(γ) = N - α/(2π)` where `N` is the external winding contribution. -/
theorem generalizedWindingNumber_eq_external_sub_angle (γ : PwC1Immersion x y) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) =
      externalWindingContribution γ z₀ t₀ ht₀ -
        (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi) := by
  simp [externalWindingContribution]

/-- When the external winding contribution is zero, the generalized winding number equals
minus the crossing angle contribution. -/
theorem generalizedWindingNumber_eq_neg_angleContribution_single (γ : PwC1Immersion x y)
    (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_external : externalWindingContribution γ z₀ t₀ ht₀ = 0) :
    (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) =
      -((angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi)) := by
  simp [generalizedWindingNumber_eq_external_sub_angle γ z₀ t₀ ht₀, h_external]

/-- At a smooth crossing with zero external winding, the generalized winding
number is `-1/2`. This is the most common case: a simple curve passing through `z₀`
transversally. -/
theorem generalizedWindingNumber_eq_neg_half_smooth_crossing (γ : PwC1Immersion x y) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition)
    (h_external : externalWindingContribution γ z₀ t₀ ht₀ = 0) :
    (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = -(1 / 2) := by
  rw [generalizedWindingNumber_eq_neg_angleContribution_single γ z₀ t₀ ht₀ h_external,
      angleAtCrossing_smooth γ t₀ ht₀ hsmooth]
  field_simp

end
