/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.MultipointPV
import LeanModularForms.ForMathlib.GeneralizedWindingNumber

/-!
# PV Integrals of Simple Pole Terms

This file computes the Cauchy principal value integral of `c / (z - s)` along a
piecewise C¹ path in terms of the generalized winding number.

## Main results

* `hasCauchyPV_inv_sub` — PV of `(z - s)⁻¹` equals `2πi · w`, directly from the
  definition of `HasGeneralizedWindingNumber`.

* `hasCauchyPV_div_sub` — PV of `c / (z - s)` equals `2πi · w · c`.

* `integral_simple_pole_eq_winding` — when `γ` avoids `s`, the ordinary contour integral
  of `c / (z - s)` equals `2πi · w · c` where `w` is the generalized winding number.

* `hasCauchyPVOn_singleton_div_sub` — the singleton-set version of `hasCauchyPV_div_sub`,
  as a `HasCauchyPVOn` statement.

* `hasCauchyPVOn_sum_div_sub_of_avoids` — PV of `∑ s ∈ S, c s / (z - s)` when `γ`
  avoids all poles: equals the ordinary contour integral.

* `integral_sum_simple_poles_eq_winding` — contour integral of `∑ s ∈ S, c s / (z - s)`
  equals `∑ s ∈ S, 2πi · w s · c s` when `γ` avoids all poles.

## Design notes

These results are the computational core of the generalized residue theorem: the PV
of the "residue part" of a meromorphic function (a sum of `residue / (z - pole)` terms)
is computable from winding numbers alone.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set Filter Topology MeasureTheory Complex
open scoped Interval

noncomputable section

variable {x y : ℂ}

/-! ### Pointwise integrand equality: `c / (z - s) = c * (z - s)⁻¹` -/

private theorem cpvIntegrand_div_eq_mul_inv (c s : ℂ) (γ : ℝ → ℂ) (ε t : ℝ) :
    cpvIntegrand (fun z => c / (z - s)) γ s ε t =
      cpvIntegrand (fun z => c * (z - s)⁻¹) γ s ε t := by
  simp only [cpvIntegrand]
  split_ifs <;> simp [div_eq_mul_inv]

/-! ### PV of a single simple pole term -/

/-- PV of `(z - s)⁻¹` equals `2πi · w`: this is exactly the definition of
`HasGeneralizedWindingNumber`. -/
theorem hasCauchyPV_inv_sub {s : ℂ} {γ : PiecewiseC1Path x y} {w : ℂ}
    (hw : HasGeneralizedWindingNumber γ s w) :
    HasCauchyPV (fun z => (z - s)⁻¹) γ s (2 * ↑Real.pi * I * w) :=
  hw

/-- PV integral of `c / (z - s)` equals `2πi · w · c`. -/
theorem hasCauchyPV_div_sub {s c : ℂ} {γ : PiecewiseC1Path x y} {w : ℂ}
    (hw : HasGeneralizedWindingNumber γ s w) :
    HasCauchyPV (fun z => c / (z - s)) γ s (2 * ↑Real.pi * I * w * c) := by
  have h := hw.const_mul c
  rw [show (2 : ℂ) * ↑Real.pi * I * w * c = c * (2 * ↑Real.pi * I * w) from by ring]
  refine h.congr fun ε => ?_
  apply intervalIntegral.integral_congr
  intro t _
  exact cpvIntegrand_div_eq_mul_inv c s γ.toPath.extend ε t

/-- PV integral of `c * (z - s)⁻¹` equals `2πi · w · c` (variant form). -/
theorem hasCauchyPV_mul_inv_sub {s c : ℂ} {γ : PiecewiseC1Path x y} {w : ℂ}
    (hw : HasGeneralizedWindingNumber γ s w) :
    HasCauchyPV (fun z => c * (z - s)⁻¹) γ s (2 * ↑Real.pi * I * w * c) := by
  have h := hw.const_mul c
  rw [show (2 : ℂ) * ↑Real.pi * I * w * c = c * (2 * ↑Real.pi * I * w) from by ring]
  exact h

/-- `cauchyPV` value for `c / (z - s)`. -/
theorem cauchyPV_div_sub_eq {s c : ℂ} {γ : PiecewiseC1Path x y} {w : ℂ}
    (hw : HasGeneralizedWindingNumber γ s w) :
    cauchyPV (fun z => c / (z - s)) γ s = 2 * ↑Real.pi * I * w * c :=
  (hasCauchyPV_div_sub hw).cauchyPV_eq

/-- `cauchyPV` value for `(z - s)⁻¹`. -/
theorem cauchyPV_inv_sub_eq {s : ℂ} {γ : PiecewiseC1Path x y} {w : ℂ}
    (hw : HasGeneralizedWindingNumber γ s w) :
    cauchyPV (fun z => (z - s)⁻¹) γ s = 2 * ↑Real.pi * I * w :=
  hw.cauchyPV_eq

/-! ### Ordinary contour integral when the path avoids the singularity -/

/-- When `γ` avoids `s` with positive minimum distance, the ordinary contour integral
of `(z - s)⁻¹` equals `2πi · generalizedWindingNumber γ s`. -/
theorem integral_inv_sub_eq_winding {s : ℂ} {γ : PiecewiseC1Path x y}
    (hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖) :
    γ.contourIntegral (fun z => (z - s)⁻¹) =
      2 * ↑Real.pi * I * generalizedWindingNumber γ s := by
  have hw := hasGeneralizedWindingNumber_of_avoids hδ
  have hpv_avoids : HasCauchyPV (fun z => (z - s)⁻¹) γ s
      (γ.contourIntegral (fun z => (z - s)⁻¹)) := hasCauchyPV_of_avoids hδ
  have heq := HasCauchyPV.unique hpv_avoids hw
  rw [heq, hw.eq]

/-- When `γ` avoids `s` with positive minimum distance, the ordinary contour integral
of `c / (z - s)` equals `2πi · generalizedWindingNumber γ s · c`. -/
theorem integral_simple_pole_eq_winding {s c : ℂ} {γ : PiecewiseC1Path x y}
    (hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖) :
    γ.contourIntegral (fun z => c / (z - s)) =
      2 * ↑Real.pi * I * generalizedWindingNumber γ s * c := by
  have hw := hasGeneralizedWindingNumber_of_avoids hδ
  have hpv_avoids : HasCauchyPV (fun z => c / (z - s)) γ s
      (γ.contourIntegral (fun z => c / (z - s))) := hasCauchyPV_of_avoids hδ
  have heq := HasCauchyPV.unique hpv_avoids (hasCauchyPV_div_sub hw)
  rw [heq, hw.eq]

/-! ### Singleton set versions -/

/-- The singleton case: PV of `c / (z - s)` as a `HasCauchyPVOn` statement. -/
theorem hasCauchyPVOn_singleton_div_sub {s c : ℂ} {γ : PiecewiseC1Path x y} {w : ℂ}
    (hw : HasGeneralizedWindingNumber γ s w) :
    HasCauchyPVOn {s} (fun z => c / (z - s)) γ (2 * ↑Real.pi * I * w * c) :=
  hasCauchyPVOn_singleton_of_hasCauchyPV (hasCauchyPV_div_sub hw)

/-- The singleton case: PV of `(z - s)⁻¹` as a `HasCauchyPVOn` statement. -/
theorem hasCauchyPVOn_singleton_inv_sub {s : ℂ} {γ : PiecewiseC1Path x y} {w : ℂ}
    (hw : HasGeneralizedWindingNumber γ s w) :
    HasCauchyPVOn {s} (fun z => (z - s)⁻¹) γ (2 * ↑Real.pi * I * w) :=
  hasCauchyPVOn_singleton_of_hasCauchyPV hw

/-! ### Sum of simple pole terms (avoidance case) -/

/-- When `γ` avoids all points in `S`, the multi-point CPV of `∑ s ∈ S, c s / (z - s)`
equals the ordinary contour integral. -/
theorem hasCauchyPVOn_sum_div_sub_of_avoids {S : Finset ℂ} {c : ℂ → ℂ}
    {γ : PiecewiseC1Path x y}
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖) :
    HasCauchyPVOn S (fun z => ∑ s ∈ S, c s / (z - s)) γ
      (γ.contourIntegral (fun z => ∑ s ∈ S, c s / (z - s))) :=
  hasCauchyPVOn_of_avoids hδ

/-- Contour integral of a sum of simple pole terms equals the sum of
`2πi · winding · coefficient` when `γ` avoids all poles.

This is the key computation for the classical residue theorem: the contour integral
of the singular part `∑ cₛ/(z-s)` equals `∑ 2πi · n(γ,s) · cₛ`. -/
theorem integral_sum_simple_poles_eq_winding {S : Finset ℂ} {c : ℂ → ℂ}
    {γ : PiecewiseC1Path x y}
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (c s / (γ.toPath.extend t - s)) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral (fun z => ∑ s ∈ S, c s / (z - s)) =
      ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s * c s := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hδ
  have h_ind : ∀ s ∈ S, γ.contourIntegral (fun z => c s / (z - s)) =
      2 * ↑Real.pi * I * generalizedWindingNumber γ s * c s :=
    fun s hs => integral_simple_pole_eq_winding ⟨δ, hδ_pos, hδ_bound s hs⟩
  simp only [PiecewiseC1Path.contourIntegral, PiecewiseC1Path.extendedPath_eq]
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finset_sum hI]
  exact Finset.sum_congr rfl h_ind

end
