/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.FlatnessConditions
import LeanModularForms.ForMathlib.SegmentFTC
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Sector Curve Analysis

Model curves for crossing analysis: sector curves that serve as local models near
pole crossings. These are used to analyze the CPV of higher-order polar terms
`a_k / (z - s)^k` along a curve that crosses `s`.

## Main definitions

* `SectorCurve.lineCurve` — a straight line through the origin at angle `α`,
  parametrized as `t ↦ r * t * exp(i α)`.

* `SectorCurve.higherOrderFactor` — the constant factor `r⁻ᵏ * exp(-ikα)` appearing
  when computing `z⁻⁽ᵏ⁺¹⁾ dz` along the line curve.

## Main results

* `SectorCurve.lineCurve_integrand_inv` — the integrand of `z⁻¹ dz` simplifies to `t⁻¹`.
* `SectorCurve.exp_factor_eq_one_of_angle_condition` — `exp(-ikα) = 1` when `kα ∈ 2πℤ`.
* `SectorCurve.pv_odd_power_vanishes` — for odd `k ≥ 1`, PV of `(↑t)⁻¹ ^ k` is zero.
* `SectorCurve.higherOrder_terms_odd_vanish` — for odd `k ≥ 3`, the PV of
  `z⁻ᵏ dz` along the sector curve vanishes.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2, Lemma 3.1 and Theorem 3.3
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

noncomputable section

namespace SectorCurve

/-! ### The model line curve through the origin -/

/-- A model straight-line curve through the origin at angle `α`:
`γ(t) = r * t * exp(i α)`. -/
def lineCurve (r : ℝ) (α : ℝ) (t : ℝ) : ℂ :=
  ↑(r * t) * exp (↑α * I)

@[simp]
theorem lineCurve_zero (r : ℝ) (α : ℝ) : lineCurve r α 0 = 0 := by
  simp [lineCurve]

/-- The constant factor `r⁻ᵏ · exp(-ikα)` in the higher-order integrand. -/
def higherOrderFactor (r : ℝ) (α : ℝ) (k : ℕ) : ℂ :=
  ↑(r⁻¹ ^ k) * exp (-(↑k : ℂ) * (↑α * I))

@[simp]
theorem higherOrderFactor_zero (r : ℝ) (α : ℝ) : higherOrderFactor r α 0 = 1 := by
  simp [higherOrderFactor]

end SectorCurve
