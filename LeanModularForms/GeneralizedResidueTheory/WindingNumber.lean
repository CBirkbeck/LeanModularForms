/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Basic
import LeanModularForms.GeneralizedResidueTheory.PrincipalValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Winding Number Theory

Generalized winding numbers for piecewise C¹ curves, including the
Hungerbühler-Wasem angle-based approach for curves passing through
singularities.

## Main Definitions

* `angleAtCrossing` — angle at a crossing point where γ passes through z₀
* `windingNumberWithAngles'` — winding number via explicit angle sum

## Main Results

* `windingNumber_smooth_crossing` — smooth crossing contributes 1/2
* `windingNumber_corner_crossing` — corner with angle α contributes α/(2π)
* `generalizedWindingNumber_eq_angleContribution_single` — H-W Proposition 2.3
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- The angle at a crossing point where γ passes through z₀.
`arg(L_out) - arg(-L_in)` where L_in and L_out are one-sided derivative
limits. At smooth points (not in partition), returns π. -/
def angleAtCrossing (γ : PiecewiseC1Immersion) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) : ℝ :=
  if h : t₀ ∈ γ.toPiecewiseC1Curve.partition then
    let L_left :=
      Classical.choose (γ.left_deriv_limit t₀ h ht₀.1)
    let L_right :=
      Classical.choose (γ.right_deriv_limit t₀ h ht₀.2)
    arg L_right - arg (-L_left)
  else Real.pi

theorem angleAtCrossing_smooth (γ : PiecewiseC1Immersion)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Curve.partition) :
    angleAtCrossing γ t₀ ht₀ = Real.pi := by
  simp only [angleAtCrossing, hsmooth, ↓reduceDIte]

/-- Winding number via explicit angle sum at crossings. -/
def windingNumberWithAngles'
    (γ : PiecewiseC1Immersion) (_z₀ : ℂ)
    (crossings : Finset ℝ)
    (hcrossings_in : ∀ t ∈ crossings, t ∈ Ioo γ.a γ.b)
    (_hcrossings_at : ∀ t ∈ crossings, γ.toFun t = _z₀) :
    ℂ :=
  ∑ t : crossings,
    (angleAtCrossing γ t
      (hcrossings_in t t.prop)) / (2 * Real.pi)

theorem singleton_mem_Ioo (t₀ : ℝ) (a b : ℝ)
    (ht₀ : t₀ ∈ Ioo a b) :
    ∀ t ∈ ({t₀} : Finset ℝ), t ∈ Ioo a b := by
  intro t ht
  simp only [Finset.mem_singleton] at ht
  rw [ht]; exact ht₀

theorem singleton_at_crossing (γ : PiecewiseC1Immersion)
    (t₀ : ℝ) (z₀ : ℂ) (hcross : γ.toFun t₀ = z₀) :
    ∀ t ∈ ({t₀} : Finset ℝ), γ.toFun t = z₀ := by
  intro t ht
  simp only [Finset.mem_singleton] at ht
  rw [ht]; exact hcross

/-- A single smooth crossing contributes 1/2 to the winding number. -/
theorem windingNumber_smooth_crossing
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Curve.partition) :
    windingNumberWithAngles' γ z₀ {t₀}
      (singleton_mem_Ioo t₀ γ.a γ.b ht₀)
      (singleton_at_crossing γ t₀ z₀ hcross) = 1/2 := by
  simp only [windingNumberWithAngles']
  rw [Fintype.sum_unique]
  simp only [Finset.default_singleton]
  rw [angleAtCrossing_smooth γ t₀ ht₀ hsmooth]
  field_simp [Real.pi_ne_zero]

/-- A corner crossing with angle α contributes α/(2π). -/
theorem windingNumber_corner_crossing
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (α : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (hangle : angleAtCrossing γ t₀ ht₀ = α) :
    windingNumberWithAngles' γ z₀ {t₀}
      (singleton_mem_Ioo t₀ γ.a γ.b ht₀)
      (singleton_at_crossing γ t₀ z₀ hcross) =
    α / (2 * Real.pi) := by
  simp only [windingNumberWithAngles']
  rw [Fintype.sum_unique]
  simp only [Finset.default_singleton]
  rw [hangle]

/-- When γ avoids z₀, the PV cutoff is trivial below minimum distance. -/
theorem cauchyPrincipalValue_eq_classical_off_curve'
    (γ : PiecewiseC1Curve) (z₀ : ℂ)
    (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) :
    ∃ δ > 0, ∀ ε < δ, ∀ t ∈ Icc γ.a γ.b,
      ‖γ.toFun t - z₀‖ > ε := by
  have h_compact : IsCompact (γ.toFun '' Icc γ.a γ.b) :=
    isCompact_Icc.image_of_continuousOn γ.continuous_toFun
  have hz_notin : z₀ ∉ γ.toFun '' Icc γ.a γ.b := by
    rw [mem_image]; push_neg; intro t ht; exact hoff t ht
  have h_nonempty : (γ.toFun '' Icc γ.a γ.b).Nonempty :=
    ⟨γ.toFun γ.a,
      mem_image_of_mem _ (left_mem_Icc.mpr γ.hab.le)⟩
  have h_dist_pos :
      0 < Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b) := by
    rw [← Metric.infDist_pos_iff_notMem_closure h_nonempty,
      h_compact.isClosed.closure_eq]
    exact hz_notin
  exact ⟨_, h_dist_pos, fun ε hε t ht => by
    calc ‖γ.toFun t - z₀‖
        = dist (γ.toFun t) z₀ := (dist_eq_norm _ _).symm
      _ = dist z₀ (γ.toFun t) := dist_comm _ _
      _ ≥ Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b) :=
          Metric.infDist_le_dist_of_mem (mem_image_of_mem _ ht)
      _ > ε := hε⟩

theorem integral_inv_real_axis (r ε : ℝ) (hr : 0 < r)
    (hε : 0 < ε) :
    ∫ t in ε..r, (t : ℂ)⁻¹ =
    Complex.log r - Complex.log ε := by
  have h_real : ∫ t in ε..r, (t : ℝ)⁻¹ =
      Real.log r - Real.log ε := by
    rw [integral_inv_of_pos hε hr,
      Real.log_div hr.ne' hε.ne']
  simp_rw [← Complex.ofReal_inv]
  rw [intervalIntegral.integral_ofReal, h_real]
  simp only [Complex.ofReal_sub,
    Complex.ofReal_log hr.le, Complex.ofReal_log hε.le]

/-- Translate a piecewise C¹ immersion by a constant. -/
def PiecewiseC1Immersion.translate
    (γ : PiecewiseC1Immersion) (c : ℂ) :
    PiecewiseC1Immersion where
  toFun := fun t => γ.toFun t + c
  a := γ.a
  b := γ.b
  hab := γ.hab
  partition := γ.partition
  partition_subset := γ.partition_subset
  endpoints_in_partition := γ.endpoints_in_partition
  continuous_toFun := γ.continuous_toFun.add continuousOn_const
  smooth_off_partition := fun t ht ht' =>
    (γ.smooth_off_partition t ht ht').add
      (differentiableAt_const _)
  deriv_continuous_off_partition := by
    intro t ht hnp
    have := γ.deriv_continuous_off_partition t ht hnp
    convert this using 1
    exact funext fun x => by rw [deriv_add_const]
  deriv_ne_zero := by
    intro t ht ht'
    rw [deriv_add_const]
    exact γ.deriv_ne_zero t ht ht'
  left_deriv_limit := by
    intro p hp hp'
    obtain ⟨L, hL_ne, hL⟩ := γ.left_deriv_limit p hp hp'
    exact ⟨L, hL_ne, by
      have h : deriv (fun t => γ.toFun t + c) =
          deriv γ.toFun := funext fun _ => deriv_add_const c
      rwa [h]⟩
  right_deriv_limit := by
    intro p hp hp'
    obtain ⟨L, hL_ne, hL⟩ := γ.right_deriv_limit p hp hp'
    exact ⟨L, hL_ne, by
      have h : deriv (fun t => γ.toFun t + c) =
          deriv γ.toFun := funext fun _ => deriv_add_const c
      rwa [h]⟩

/-- The angle at a crossing is invariant under translation. -/
theorem angleAtCrossing_translate
    (γ : PiecewiseC1Immersion) (c : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) :
    angleAtCrossing (γ.translate c) t₀ ht₀ =
    angleAtCrossing γ t₀ ht₀ := by
  unfold angleAtCrossing
  generalize_proofs at *
  unfold PiecewiseC1Immersion.translate; aesop

/-- H-W Proposition 2.3: For a closed piecewise C¹ immersion passing
through z₀ exactly once at t₀, the generalized winding number equals
the crossing angle divided by 2π. -/
theorem generalizedWindingNumber_eq_angleContribution_single
    (γ : PiecewiseC1Immersion)
    (hclosed : γ.toPiecewiseC1Curve.IsClosed) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀)
    (h_orientation : ∀ᶠ δ in 𝓝[>] 0,
      ((γ.toFun (t₀ - δ) - z₀) /
        (γ.toFun (t₀ + δ) - z₀)).im > 0) :
    generalizedWindingNumber' γ.toFun γ.a γ.b z₀ =
      (angleAtCrossing γ t₀ ht₀ : ℂ) /
        (2 * Real.pi) := by
  sorry

/-- At a smooth crossing, the winding number contribution is 1/2. -/
theorem generalizedWindingNumber_eq_half_smooth_crossing
    (γ : PiecewiseC1Immersion)
    (hclosed : γ.toPiecewiseC1Curve.IsClosed) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Curve.partition)
    (h_orientation : ∀ᶠ δ in 𝓝[>] 0,
      ((γ.toFun (t₀ - δ) - z₀) /
        (γ.toFun (t₀ + δ) - z₀)).im > 0) :
    generalizedWindingNumber' γ.toFun γ.a γ.b z₀ =
      1 / 2 := by
  rw [generalizedWindingNumber_eq_angleContribution_single
    γ hclosed z₀ t₀ ht₀ hcross honly h_orientation,
    angleAtCrossing_smooth γ t₀ ht₀ hsmooth]
  have : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [this]

/-- At a corner crossing with angle α, contribution is α/(2π). -/
theorem generalizedWindingNumber_eq_corner_contribution
    (γ : PiecewiseC1Immersion)
    (hclosed : γ.toPiecewiseC1Curve.IsClosed) (z₀ : ℂ)
    (t₀ : ℝ) (α : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀)
    (hangle : angleAtCrossing γ t₀ ht₀ = α)
    (h_orientation : ∀ᶠ δ in 𝓝[>] 0,
      ((γ.toFun (t₀ - δ) - z₀) /
        (γ.toFun (t₀ + δ) - z₀)).im > 0) :
    generalizedWindingNumber' γ.toFun γ.a γ.b z₀ =
      α / (2 * Real.pi) := by
  rw [generalizedWindingNumber_eq_angleContribution_single
    γ hclosed z₀ t₀ ht₀ hcross honly h_orientation,
    hangle]

/-- Winding number with angles is additive over disjoint crossing sets. -/
theorem windingNumberWithAngles_union
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (S T : Finset ℝ) (hST : Disjoint S T)
    (hS_in : ∀ t ∈ S, t ∈ Ioo γ.a γ.b)
    (hT_in : ∀ t ∈ T, t ∈ Ioo γ.a γ.b)
    (hS_at : ∀ t ∈ S, γ.toFun t = z₀)
    (hT_at : ∀ t ∈ T, γ.toFun t = z₀) :
    windingNumberWithAngles' γ z₀ (S ∪ T)
      (fun t ht => by
        simp only [Finset.mem_union] at ht
        exact ht.elim (hS_in t) (hT_in t))
      (fun t ht => by
        simp only [Finset.mem_union] at ht
        exact ht.elim (hS_at t) (hT_at t)) =
    windingNumberWithAngles' γ z₀ S hS_in hS_at +
    windingNumberWithAngles' γ z₀ T hT_in hT_at := by
  simp only [windingNumberWithAngles']
  symm
  convert Finset.sum_union ?_
  any_goals exact hST
  any_goals try infer_instance
  rotate_right
  use fun x =>
    if hx : x ∈ S then
      (angleAtCrossing γ x (hS_in x hx) : ℂ) /
        (2 * Real.pi)
    else if hx : x ∈ T then
      (angleAtCrossing γ x (hT_in x hx) : ℂ) /
        (2 * Real.pi)
    else 0
  · rw [Finset.sum_union hST]
    congr! 1
    · refine Finset.sum_bij (fun x hx => x)
        ?_ ?_ ?_ ?_ <;> aesop
    · refine Finset.sum_bij (fun x hx => x.val)
        ?_ ?_ ?_ ?_ <;> aesop
  · rw [← Finset.sum_union hST]
    refine Finset.sum_bij (fun x hx => x.val)
      ?_ ?_ ?_ ?_ <;>
      simp +decide
    tauto

end
