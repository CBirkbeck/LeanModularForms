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

* `generalizedWindingNumber_eq_neg_corner_contribution` — at a corner crossing with angle
  `α` and zero external winding, the generalized winding number is `-α/(2π)`.

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

/-- The crossing angle is positive at a smooth point. -/
theorem angleAtCrossing_smooth_pos (γ : PwC1Immersion x y) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) :
    0 < angleAtCrossing γ t₀ ht₀ := by
  rw [angleAtCrossing_smooth γ t₀ ht₀ hsmooth]
  exact Real.pi_pos

/-- Crossings at smooth points contribute `1/2` to the angle sum. -/
theorem angleAtCrossing_smooth_div_two_pi (γ : PwC1Immersion x y) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) :
    (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi) = 1 / 2 := by
  rw [angleAtCrossing_smooth γ t₀ ht₀ hsmooth]
  field_simp

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

/-- Variant: express the external winding contribution in terms of the generalized
winding number and the crossing angle. -/
theorem externalWindingContribution_eq (γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    externalWindingContribution γ z₀ t₀ ht₀ =
      generalizedWindingNumber γ.toPiecewiseC1Path z₀ +
        (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi) := rfl

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

/-- At a corner crossing with angle `α` and zero external winding, the generalized
winding number is `-α/(2π)`. -/
theorem generalizedWindingNumber_eq_neg_corner_contribution (γ : PwC1Immersion x y) (z₀ : ℂ)
    (t₀ : ℝ) (α : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hangle : angleAtCrossing γ t₀ ht₀ = α)
    (h_external : externalWindingContribution γ z₀ t₀ ht₀ = 0) :
    (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = -(↑α / (2 * ↑Real.pi)) := by
  rw [generalizedWindingNumber_eq_neg_angleContribution_single γ z₀ t₀ ht₀ h_external, hangle]

/-- If the generalized winding number equals `-α/(2π)`, then the external
winding contribution is zero. -/
theorem externalWindingContribution_zero_of_windingNumber_eq (γ : PwC1Immersion x y) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_eq : (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) =
      -((angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi))) :
    externalWindingContribution γ z₀ t₀ ht₀ = 0 := by
  simp [externalWindingContribution, h_eq]

/-- If the generalized winding number equals `-1/2` and the crossing is smooth,
then the external winding contribution is zero. -/
theorem externalWindingContribution_zero_of_neg_half (γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition)
    (h_eq : (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = -(1 / 2)) :
    externalWindingContribution γ z₀ t₀ ht₀ = 0 :=
  externalWindingContribution_zero_of_windingNumber_eq γ z₀ t₀ ht₀ <| by
    rw [angleAtCrossing_smooth γ t₀ ht₀ hsmooth, h_eq]
    field_simp

/-- The external winding contribution determines the generalized winding number
via the crossing angle. -/
theorem generalizedWindingNumber_of_external_eq (γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (N : ℂ) (hN : externalWindingContribution γ z₀ t₀ ht₀ = N) :
    (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) =
      N - (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi) := by
  rw [generalizedWindingNumber_eq_external_sub_angle, hN]

/-- When the external winding is an integer `n`, the generalized winding number is
`n - α/(2π)`. -/
theorem generalizedWindingNumber_of_external_int (γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (n : ℤ) (hn : externalWindingContribution γ z₀ t₀ ht₀ = (n : ℂ)) :
    (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) =
      (n : ℂ) - (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi) :=
  generalizedWindingNumber_of_external_eq γ z₀ t₀ ht₀ n hn

/-- When the external winding is 1 and the crossing is smooth, the generalized
winding number is `1/2`. -/
theorem generalizedWindingNumber_eq_half_of_external_one_smooth (γ : PwC1Immersion x y) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition)
    (h_external : externalWindingContribution γ z₀ t₀ ht₀ = 1) :
    (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = 1 / 2 := by
  rw [generalizedWindingNumber_of_external_eq γ z₀ t₀ ht₀ 1 h_external,
    angleAtCrossing_smooth γ t₀ ht₀ hsmooth]
  field_simp
  ring

/-- When the external winding is -1 and the crossing is smooth, the generalized
winding number is `-3/2`. -/
theorem generalizedWindingNumber_eq_neg_three_halves_of_external_neg_one_smooth
    (γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition)
    (h_external : externalWindingContribution γ z₀ t₀ ht₀ = -1) :
    (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = -(3 / 2) := by
  rw [generalizedWindingNumber_of_external_eq γ z₀ t₀ ht₀ (-1) h_external,
    angleAtCrossing_smooth γ t₀ ht₀ hsmooth]
  field_simp
  ring

/-- The external winding contribution is an integer. This is the mathematical content of
HW Proposition 2.3 — the "external" part of the decomposition `n_{z₀}(γ) = N - α/(2π)` is
integer-valued. -/
def HasIntegerExternalWinding (γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) : Prop :=
  ∃ n : ℤ, externalWindingContribution γ z₀ t₀ ht₀ = (n : ℂ)

/-- When external winding is zero, the predicate holds with `n = 0`. -/
theorem HasIntegerExternalWinding.of_zero {γ : PwC1Immersion x y} {z₀ : ℂ} {t₀ : ℝ}
    {ht₀ : t₀ ∈ Ioo (0 : ℝ) 1} (h : externalWindingContribution γ z₀ t₀ ht₀ = 0) :
    HasIntegerExternalWinding γ z₀ t₀ ht₀ :=
  ⟨0, by simp [h]⟩

/-- At a smooth crossing where the generalized winding number is `-1/2`, the
external winding is 0, hence integer. -/
theorem HasIntegerExternalWinding.of_neg_half_smooth {γ : PwC1Immersion x y} {z₀ : ℂ}
    {t₀ : ℝ} {ht₀ : t₀ ∈ Ioo (0 : ℝ) 1} (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition)
    (h_gWN : (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = -(1 / 2)) :
    HasIntegerExternalWinding γ z₀ t₀ ht₀ :=
  .of_zero (externalWindingContribution_zero_of_neg_half γ z₀ t₀ ht₀ hsmooth h_gWN)

/-- **HW Proposition 2.3 in complete form.** Given that the external winding is
integer-valued (`HasIntegerExternalWinding`), the generalized winding number
decomposes as an integer minus the crossing angle contribution. -/
theorem generalizedWindingNumber_eq_int_sub_angle_of_hasInt {γ : PwC1Immersion x y} {z₀ : ℂ}
    {t₀ : ℝ} {ht₀ : t₀ ∈ Ioo (0 : ℝ) 1} (h : HasIntegerExternalWinding γ z₀ t₀ ht₀) :
    ∃ n : ℤ, (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) =
      (n : ℂ) - (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi) :=
  h.imp fun n hn ↦ generalizedWindingNumber_of_external_int γ z₀ t₀ ht₀ n hn

/-- The winding number contribution from a single crossing, defined as
`angleAtCrossing / (2π)`. This is the angle-based formula from H-W. -/
def windingContributionAt (γ : PwC1Immersion x y) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) : ℂ :=
  (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi)

/-- A smooth crossing contributes `1/2` to the angle-based winding. -/
theorem windingContributionAt_smooth (γ : PwC1Immersion x y) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) :
    windingContributionAt γ t₀ ht₀ = 1 / 2 :=
  angleAtCrossing_smooth_div_two_pi γ t₀ ht₀ hsmooth

/-- A corner crossing with angle `α` contributes `α/(2π)` to the angle-based winding. -/
theorem windingContributionAt_corner (γ : PwC1Immersion x y) (t₀ : ℝ) (α : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hangle : angleAtCrossing γ t₀ ht₀ = α) :
    windingContributionAt γ t₀ ht₀ = ↑α / (2 * ↑Real.pi) := by
  simp [windingContributionAt, hangle]

/-- The decomposition in terms of `windingContributionAt`:
`n_{z₀}(γ) = N - windingContributionAt γ t₀`. -/
theorem generalizedWindingNumber_eq_external_sub_contribution (γ : PwC1Immersion x y) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) =
      externalWindingContribution γ z₀ t₀ ht₀ - windingContributionAt γ t₀ ht₀ :=
  generalizedWindingNumber_eq_external_sub_angle γ z₀ t₀ ht₀

/-- If a crossing is the unique crossing in `[0,1]` and lies in `(0,1)`, then the
endpoints avoid `z₀`. -/
theorem endpoint_avoidance_of_unique_interior_crossing (γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (_hcross : (γ : ℝ → ℂ) t₀ = z₀)
    (honly : ∀ t ∈ Icc (0 : ℝ) 1, (γ : ℝ → ℂ) t = z₀ → t = t₀) :
    (γ : ℝ → ℂ) 0 ≠ z₀ ∧ (γ : ℝ → ℂ) 1 ≠ z₀ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · linarith [ht₀.1, honly 0 (left_mem_Icc.mpr zero_le_one) h]
  · linarith [ht₀.2, honly 1 (right_mem_Icc.mpr zero_le_one) h]

end
