/-
Copyright (c) 2026 LeanModularForms contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
module

public import LeanModularForms.ForMathlib.HungerbuhlerWasem
public import LeanModularForms.ForMathlib.CurveMeasureZero
public import LeanModularForms.ForMathlib.FlatnessConditions

/-! # Crossing CPV — simple-pole CPV algebra

Two small CPV conversion lemmas used by the crossing residue theorems:

* `HungerbuhlerWasem.hasCauchyPV_simplePole_of_inv` — if the CPV of
  `(z - s)⁻¹` along `γ` exists with limit `L`, then the CPV of `c / (z - s)`
  exists with limit `c * L`.
* `HungerbuhlerWasem.HasCauchyPV.to_singletonOn` — the single-point CPV
  predicate `HasCauchyPV f γ z₀ L` upgrades to the multi-point predicate
  `HasCauchyPVOn {z₀} f γ L` on the singleton.
-/

open Filter Topology Set Complex MeasureTheory

@[expose] public section

noncomputable section

variable {x y : ℂ}

/-- **From inverse-CPV to simple-pole CPV.** If the CPV of `(z - s)⁻¹` along `γ`
exists with limit `L`, then the CPV of `c / (z - s)` exists with limit `c * L`.

This is just `HasCauchyPV.smul c` together with the rewrite
`c * (z - s)⁻¹ = c / (z - s)`. -/
theorem HungerbuhlerWasem.hasCauchyPV_simplePole_of_inv
    {γ : PiecewiseC1Path x y} {s L : ℂ} (c : ℂ)
    (h : HasCauchyPV (fun z => (z - s)⁻¹) γ s L) :
    HasCauchyPV (fun z => c / (z - s)) γ s (c * L) := by
  simpa [div_eq_mul_inv] using h.smul c

namespace HungerbuhlerWasem

/-- **`HasCauchyPV` upgrades to `HasCauchyPVOn {z₀}`.** The single-point CPV
predicate is equivalent to the multi-point CPV predicate on the singleton
`{z₀}`, since the integrands `cpvIntegrand` and `cpvIntegrandOn {z₀}` agree
pointwise (`cpvIntegrand_eq_cpvIntegrandOn_singleton`). -/
theorem HasCauchyPV.to_singletonOn
    {f : ℂ → ℂ} {γ : PiecewiseC1Path x y} {z₀ L : ℂ}
    (h : HasCauchyPV f γ z₀ L) : HasCauchyPVOn {z₀} f γ L :=
  h.congr fun _ => intervalIntegral.integral_congr fun _ _ =>
    cpvIntegrand_eq_cpvIntegrandOn_singleton

end HungerbuhlerWasem

end

end
