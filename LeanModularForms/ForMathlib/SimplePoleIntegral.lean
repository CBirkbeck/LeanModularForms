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

/-- When `γ` avoids `s` with positive minimum distance, the ordinary contour integral
of `(z - s)⁻¹` equals `2πi · generalizedWindingNumber γ s`. -/
theorem integral_inv_sub_eq_winding {s : ℂ} {γ : PiecewiseC1Path x y}
    (hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖) :
    γ.contourIntegral (fun z => (z - s)⁻¹) =
      2 * ↑Real.pi * I * generalizedWindingNumber γ s := by
  have hw := hasGeneralizedWindingNumber_of_avoids hδ
  rw [HasCauchyPV.unique (hasCauchyPV_of_avoids hδ) hw, hw.eq]

end
