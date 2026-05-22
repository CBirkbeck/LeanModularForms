/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ClassicalCPV
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.PrincipalValue
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.WindingNumber.Proposition2_2
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Homotopy.Integrality
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Winding Number: Definitions and Simple Results

Definitions for generalized winding numbers of piecewise C¹ curves,
including the Hungerbühler-Wasem angle-based approach.

## Main Definitions

* `angleAtCrossing` — angle at a crossing point where γ passes through z₀
* `windingNumberWithAngles'` — winding number via explicit angle sum
* `PiecewiseC1Immersion.translate` — translate an immersion
* `externalWindingContribution` — winding from the curve's global topology

## Main Results

* `windingNumber_smooth_crossing` — smooth crossing contributes 1/2
* `windingNumber_corner_crossing` — corner with angle α contributes α/(2π)
* `angleAtCrossing_translate` — translation invariance of crossing angle
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- The angle at a crossing point where γ passes through z₀.
`arg(L_out) - arg(-L_in)` where `L_in` and `L_out` are one-sided derivative
limits. At smooth points (not in partition), returns π. -/
def angleAtCrossing (γ : PiecewiseC1Immersion) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) : ℝ :=
  if h : t₀ ∈ γ.toPiecewiseC1Curve.partition then
    let lLeft := Classical.choose (γ.left_deriv_limit t₀ h ht₀.1)
    let lRight := Classical.choose (γ.right_deriv_limit t₀ h ht₀.2)
    arg lRight - arg (-lLeft)
  else Real.pi

theorem angleAtCrossing_smooth (γ : PiecewiseC1Immersion) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hsmooth : t₀ ∉ γ.toPiecewiseC1Curve.partition) :
    angleAtCrossing γ t₀ ht₀ = Real.pi := by
  unfold angleAtCrossing
  rw [dif_neg hsmooth]

/-- Winding number via explicit angle sum at crossings. -/
def windingNumberWithAngles' (γ : PiecewiseC1Immersion) (_z₀ : ℂ) (crossings : Finset ℝ)
    (hcrossings_in : ∀ t ∈ crossings, t ∈ Ioo γ.a γ.b)
    (_hcrossings_at : ∀ t ∈ crossings, γ.toFun t = _z₀) : ℂ :=
  ∑ t : crossings, (angleAtCrossing γ t (hcrossings_in t t.prop)) / (2 * Real.pi)

theorem singleton_mem_Ioo (t₀ : ℝ) (a b : ℝ) (ht₀ : t₀ ∈ Ioo a b) :
    ∀ t ∈ ({t₀} : Finset ℝ), t ∈ Ioo a b := by
  intro t ht
  rwa [Finset.mem_singleton.mp ht]

theorem singleton_at_crossing (γ : PiecewiseC1Immersion) (t₀ : ℝ) (z₀ : ℂ)
    (hcross : γ.toFun t₀ = z₀) : ∀ t ∈ ({t₀} : Finset ℝ), γ.toFun t = z₀ := by
  intro t ht
  rwa [Finset.mem_singleton.mp ht]

/-- A single smooth crossing contributes 1/2 to the winding number. -/
theorem windingNumber_smooth_crossing (γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = z₀)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Curve.partition) :
    windingNumberWithAngles' γ z₀ {t₀} (singleton_mem_Ioo t₀ γ.a γ.b ht₀)
      (singleton_at_crossing γ t₀ z₀ hcross) = 1 / 2 := by
  simp only [windingNumberWithAngles']
  rw [Fintype.sum_unique]
  simp only [Finset.default_singleton]
  rw [angleAtCrossing_smooth γ t₀ ht₀ hsmooth]
  field_simp [Real.pi_ne_zero]

/-- A corner crossing with angle α contributes α/(2π). -/
theorem windingNumber_corner_crossing (γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ α : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = z₀)
    (hangle : angleAtCrossing γ t₀ ht₀ = α) :
    windingNumberWithAngles' γ z₀ {t₀} (singleton_mem_Ioo t₀ γ.a γ.b ht₀)
      (singleton_at_crossing γ t₀ z₀ hcross) = α / (2 * Real.pi) := by
  simp only [windingNumberWithAngles']
  rw [Fintype.sum_unique]
  simp only [Finset.default_singleton]
  rw [hangle]

/-- When γ avoids z₀, the PV cutoff is trivial below minimum distance. -/
theorem cauchyPrincipalValue_eq_classical_off_curve' (γ : PiecewiseC1Curve) (z₀ : ℂ)
    (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) :
    ∃ δ > 0, ∀ ε < δ, ∀ t ∈ Icc γ.a γ.b, ‖γ.toFun t - z₀‖ > ε := by
  have h_dist_pos : 0 < Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b) := by
    rw [← Metric.infDist_pos_iff_notMem_closure
      ⟨γ.toFun γ.a, mem_image_of_mem _ (left_mem_Icc.mpr γ.hab.le)⟩,
      (isCompact_Icc.image_of_continuousOn γ.continuous_toFun).isClosed.closure_eq,
      mem_image]
    push Not
    exact hoff
  exact ⟨_, h_dist_pos, fun ε hε t ht => by
    calc ‖γ.toFun t - z₀‖
        = dist (γ.toFun t) z₀ := (dist_eq_norm _ _).symm
      _ = dist z₀ (γ.toFun t) := dist_comm _ _
      _ ≥ Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b) :=
          Metric.infDist_le_dist_of_mem (mem_image_of_mem _ ht)
      _ > ε := hε⟩

theorem integral_inv_real_axis (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) :
    ∫ t in ε..r, (t : ℂ)⁻¹ = Complex.log r - Complex.log ε := by
  simp_rw [← Complex.ofReal_inv]
  rw [intervalIntegral.integral_ofReal, integral_inv_of_pos hε hr,
    Real.log_div hr.ne' hε.ne']
  simp [Complex.ofReal_log hr.le, Complex.ofReal_log hε.le]

/-- Translate a piecewise C¹ immersion by a constant. -/
def PiecewiseC1Immersion.translate (γ : PiecewiseC1Immersion) (c : ℂ) :
    PiecewiseC1Immersion where
  a := γ.a
  b := γ.b
  x := γ.x + c
  y := γ.y + c
  hab := γ.hab
  toPiecewiseC1PathOn :=
    { toFun := fun t => γ.toFun t + c
      source := by show γ.toPiecewiseC1PathOn.toFun γ.a + c = _; rw [γ.toPiecewiseC1PathOn.source]
      target := by show γ.toPiecewiseC1PathOn.toFun γ.b + c = _; rw [γ.toPiecewiseC1PathOn.target]
      continuous_toFun := γ.continuous_toFun.add continuousOn_const
      partition := γ.toPiecewiseC1PathOn.partition
      partition_subset := γ.toPiecewiseC1PathOn.partition_subset
      differentiable_off := fun t ht ht' =>
        (γ.toPiecewiseC1PathOn.differentiable_off t ht ht').add (differentiableAt_const _)
      deriv_continuous_off := fun t ht hnp => by
        convert γ.toPiecewiseC1PathOn.deriv_continuous_off t ht hnp using 1
        exact funext fun _ => by
          show deriv (fun s => γ.toPiecewiseC1PathOn.toFun s + c) _ = _
          rw [deriv_add_const] }
  partition := γ.partition
  partition_subset := γ.partition_subset
  endpoints_in_partition := γ.endpoints_in_partition
  partition_eq := γ.partition_eq
  deriv_ne_zero := fun t ht ht' => by
    show deriv (fun s => γ.toFun s + c) t ≠ 0
    rw [deriv_add_const]; exact γ.deriv_ne_zero t ht ht'
  left_deriv_limit := fun p hp hp' => by
    obtain ⟨L, hL_ne, hL⟩ := γ.left_deriv_limit p hp hp'
    refine ⟨L, hL_ne, ?_⟩
    show Tendsto (deriv fun s => γ.toFun s + c) (𝓝[<] p) (𝓝 L)
    rwa [show deriv (fun t => γ.toFun t + c) = deriv γ.toFun from
      funext fun _ => deriv_add_const c]
  right_deriv_limit := fun p hp hp' => by
    obtain ⟨L, hL_ne, hL⟩ := γ.right_deriv_limit p hp hp'
    refine ⟨L, hL_ne, ?_⟩
    show Tendsto (deriv fun s => γ.toFun s + c) (𝓝[>] p) (𝓝 L)
    rwa [show deriv (fun t => γ.toFun t + c) = deriv γ.toFun from
      funext fun _ => deriv_add_const c]

/-- The angle at a crossing is invariant under translation. -/
theorem angleAtCrossing_translate (γ : PiecewiseC1Immersion) (c : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) :
    angleAtCrossing (γ.translate c) t₀ ht₀ = angleAtCrossing γ t₀ ht₀ := by
  unfold angleAtCrossing
  have h_part : (γ.translate c).partition = γ.partition := rfl
  have h_deriv : ∀ s, deriv (γ.translate c).toFun s = deriv γ.toFun s := fun s => by
    show deriv (fun u => γ.toFun u + c) s = _; rw [deriv_add_const]
  by_cases h_mem : t₀ ∈ γ.partition
  · have h_mem' : t₀ ∈ (γ.translate c).partition := h_part ▸ h_mem
    simp only [dif_pos h_mem, dif_pos h_mem']
    rw [tendsto_nhds_unique
        ((Classical.choose_spec ((γ.translate c).left_deriv_limit t₀ h_mem' ht₀.1)).2.congr h_deriv)
        (Classical.choose_spec (γ.left_deriv_limit t₀ h_mem ht₀.1)).2,
      tendsto_nhds_unique
        ((Classical.choose_spec ((γ.translate c).right_deriv_limit t₀ h_mem' ht₀.2)).2.congr h_deriv)
        (Classical.choose_spec (γ.right_deriv_limit t₀ h_mem ht₀.2)).2]
  · have h_mem' : t₀ ∉ (γ.translate c).partition := h_part ▸ h_mem
    simp only [dif_neg h_mem, dif_neg h_mem']

/-- The external winding contribution at a single crossing point.
For a closed piecewise C¹ immersion passing through z₀ exactly once,
this measures the winding of the curve around z₀ apart from the local
crossing angle. Mathematically, this is the classical winding number
of the modified curve Λ̄ that detours around z₀ (H-W Proposition 2.2).

The decomposition is `n_{z₀}(γ) = N - α/(2π)`, so `N = n_{z₀}(γ) + α/(2π)`.
When `N = 0`, the generalized winding number equals `-α/(2π)`. -/
def externalWindingContribution (γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) : ℂ :=
  generalizedWindingNumber' γ.toFun γ.a γ.b z₀ +
    (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * Real.pi)

end
