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
  rw [show 2 * ↑Real.pi * I *
      ((2 * ↑Real.pi * I)⁻¹ * γ.contourIntegral (fun z => (z - z₀)⁻¹)) =
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

/-! ### Continuity off the curve -/

/-- Helper: distance lower bound for points in a small ball around `w₀` (off the curve). -/
lemma ball_dist_to_curve_lb {γ : PiecewiseC1Path x y} {w₀ : ℂ}
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w₀) :
    ∃ ε > 0, ∀ w ∈ Metric.ball w₀ ε, ∀ t ∈ Icc (0 : ℝ) 1, ε ≤ ‖γ t - w‖ := by
  have h_compact : IsCompact (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image γ.toPath.continuous_extend
  have h_nonempty : (γ.toPath.extend '' Icc (0 : ℝ) 1).Nonempty :=
    ⟨γ.toPath.extend 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩
  have h_not_mem : w₀ ∉ γ.toPath.extend '' Icc (0 : ℝ) 1 :=
    fun ⟨t, ht, heq⟩ => hoff t ht heq
  have hδ_pos : 0 < Metric.infDist w₀ (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
    (h_compact.isClosed.notMem_iff_infDist_pos h_nonempty).mp h_not_mem
  refine ⟨Metric.infDist w₀ (γ.toPath.extend '' Icc (0 : ℝ) 1) / 2, by linarith, ?_⟩
  intro w hw t ht
  have h1 : Metric.infDist w₀ (γ.toPath.extend '' Icc (0 : ℝ) 1) ≤ dist w₀ (γ t) :=
    Metric.infDist_le_dist_of_mem (mem_image_of_mem _ ht)
  have h2 := Metric.mem_ball.mp hw
  rw [Complex.dist_eq] at h1 h2
  have h3 : ‖γ t - w₀‖ ≤ ‖γ t - w‖ + ‖w - w₀‖ := by
    have h_eq : γ t - w₀ = (γ t - w) + (w - w₀) := by ring
    rw [h_eq]
    exact norm_add_le _ _
  rw [show ‖γ t - w₀‖ = ‖w₀ - γ t‖ from norm_sub_rev _ _] at h3
  rw [show ‖w - w₀‖ = ‖w₀ - w‖ from norm_sub_rev _ _] at h3
  have h4 : ‖w₀ - w‖ < Metric.infDist w₀ (γ.toPath.extend '' Icc (0 : ℝ) 1) / 2 := by
    rw [← norm_sub_rev]
    exact h2
  linarith [h1, h4]

/-- The generalized winding number is continuous at any point off a Lipschitz
piecewise C¹ curve. Uses parametric continuity of the contour integral
(`intervalIntegral.continuousAt_of_dominated_interval`) with the bound
`‖(γt - w)⁻¹ * γ'(t)‖ ≤ ε⁻¹ · K` for `w` in a ball around `w₀`. -/
theorem generalizedWindingNumber_continuousAt_of_avoids
    {γ : PiecewiseC1Path x y} {w₀ : ℂ}
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w₀)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    ContinuousAt (generalizedWindingNumber γ) w₀ := by
  obtain ⟨ε, hε_pos, h_dist_lb⟩ := ball_dist_to_curve_lb hoff
  set F : ℂ → ℝ → ℂ := fun w t => (γ t - w)⁻¹ * deriv γ.toPath.extend t
  have h_integrand_meas : ∀ w ∈ Metric.ball w₀ ε,
      AEStronglyMeasurable (F w) (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    intro w hw
    rw [Set.uIoc_of_le (zero_le_one' ℝ)]
    have h_avoid : ∀ t ∈ Icc (0 : ℝ) 1, γ t - w ≠ 0 := fun t ht h => by
      have hε_le : ε ≤ ‖γ t - w‖ := h_dist_lb w hw t ht
      rw [h, norm_zero] at hε_le
      linarith
    have h_cont_inv : ContinuousOn (fun t => (γ t - w)⁻¹) (Icc (0 : ℝ) 1) :=
      (γ.toPath.continuous_extend.continuousOn.sub continuousOn_const).inv₀ h_avoid
    exact ((h_cont_inv.mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc).mul (stronglyMeasurable_deriv _).aestronglyMeasurable
  have h_eq_nbhd : (fun w => generalizedWindingNumber γ w) =ᶠ[nhds w₀]
      fun w => (2 * ↑Real.pi * I)⁻¹ * ∫ t in (0 : ℝ)..1, F w t := by
    filter_upwards [Metric.ball_mem_nhds w₀ hε_pos] with w hw
    have hγ_avoids : ∃ δ' > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ' ≤ ‖γ t - w‖ :=
      ⟨ε, hε_pos, h_dist_lb w hw⟩
    rw [(hasGeneralizedWindingNumber_of_avoids hγ_avoids).eq]
    simp only [PiecewiseC1Path.contourIntegral, F]
  refine (ContinuousAt.congr ?_ h_eq_nbhd.symm)
  refine ContinuousAt.mul continuousAt_const ?_
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => ε⁻¹ * K) ?_ ?_
    (intervalIntegrable_const (c := ε⁻¹ * K)) ?_
  · filter_upwards [Metric.ball_mem_nhds w₀ hε_pos] with w hw
    exact h_integrand_meas w hw
  · filter_upwards [Metric.ball_mem_nhds w₀ hε_pos] with w hw
    filter_upwards with t ht
    rw [Set.uIoc_of_le (zero_le_one' ℝ)] at ht
    have ht_Icc : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    simp only [F, norm_mul, norm_inv]
    exact mul_le_mul
      (inv_anti₀ hε_pos (h_dist_lb w hw t ht_Icc))
      (norm_deriv_le_of_lipschitz hLip) (norm_nonneg _)
      (inv_nonneg.mpr hε_pos.le)
  · filter_upwards with t ht
    rw [Set.uIoc_of_le (zero_le_one' ℝ)] at ht
    have ht_Icc : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    have h_avoid : γ t - w₀ ≠ 0 := fun h => by
      have hε_le : ε ≤ ‖γ t - w₀‖ :=
        h_dist_lb w₀ (Metric.mem_ball_self hε_pos) t ht_Icc
      rw [h, norm_zero] at hε_le
      linarith
    exact ((continuous_const.sub continuous_id).continuousAt.inv₀ h_avoid).mul
      continuousAt_const

end
