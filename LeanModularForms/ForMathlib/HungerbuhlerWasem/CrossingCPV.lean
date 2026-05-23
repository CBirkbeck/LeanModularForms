/-
Copyright (c) 2026 LeanModularForms contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem
import LeanModularForms.ForMathlib.SingleCrossing
import LeanModularForms.ForMathlib.AsymmetricSingleCrossing
import LeanModularForms.ForMathlib.DixonTheorem
import LeanModularForms.ForMathlib.CurveMeasureZero
import LeanModularForms.ForMathlib.FlatnessConditions

/-! # Crossing CPV — single-pole CPV at transverse crossing + analytic remainder Cauchy

Helpers for `residueTheorem_crossing`. This file contains:
* `analyticRemainder_contourIntegral_zero` (T-AR-01) — see
  `HungerbuhlerWasem.analyticRemainder_contourIntegral_zero` in the parent file
  `LeanModularForms.ForMathlib.HungerbuhlerWasem`. The theorem must live there
  (rather than here) so that `residueTheorem_avoidance` — which is in the
  parent file and is the entry point that imports cascade up to — can call it.
  Importing this file (`CrossingCPV.lean`) gives access via the transitive
  import of the parent.
* `cpv_simplePole_at_crossing` (T-CC-01) — CPV of `c/(z-s)` at a transverse
  crossing equals `2πi · w · c`, where `w = generalizedWindingNumber γ s`.

## T-CC-01 strategy

The CPV value `2πi · w · c` is essentially **by definition** of
`generalizedWindingNumber`:

  `generalizedWindingNumber γ s := (2πi)⁻¹ · cauchyPV (fun z => 1/(z-s)) γ s`.

So the theorem reduces to **CPV existence**: once we know
`HasCauchyPV (fun z => (z - s)⁻¹) γ s L`, multiplying by `c` and rewriting the
inverse as a fraction gives the simple-pole CPV with value `c · L`.

For a transverse crossing the CPV existence is supplied by
`SingleCrossingData γ s`, which encapsulates the geometric (far/near) bounds
plus the FTC limit from each side, and produces `D.hasCauchyPV` with limit
`D.L`. Combining `D.hasCauchyPV` with `D.windingNumber_eq` gives that
`D.L = 2πi · generalizedWindingNumber γ s`, completing the formula.
-/

open Filter Topology Set Complex MeasureTheory

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

namespace SingleCrossingData

/-- **Simple-pole CPV from `SingleCrossingData`.** Given a `SingleCrossingData γ s`
witnessing a single transverse crossing, the CPV of `c / (z - s)` along `γ` exists
with value `c · D.L`. -/
theorem hasCauchyPV_simplePole {γ : PiecewiseC1Path x y} {s : ℂ}
    (D : SingleCrossingData γ s) (c : ℂ) :
    HasCauchyPV (fun z => c / (z - s)) γ s (c * D.L) :=
  HungerbuhlerWasem.hasCauchyPV_simplePole_of_inv c D.hasCauchyPV

/-- **Value form: CPV at simple pole equals `2πi · w · c`.** Given a
`SingleCrossingData γ s`, the CPV of `c / (z - s)` along `γ` exists with value
`2πi · w · c`, where `w = generalizedWindingNumber γ s`. -/
theorem hasCauchyPV_simplePole_eq_two_pi_I_mul
    {γ : PiecewiseC1Path x y} {s : ℂ} (D : SingleCrossingData γ s) (c : ℂ) :
    HasCauchyPV (fun z => c / (z - s)) γ s
      (2 * ↑Real.pi * I * generalizedWindingNumber γ s * c) := by
  have hpi : (2 * ↑Real.pi * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h_eq : c * D.L =
      2 * ↑Real.pi * I * generalizedWindingNumber γ s * c := by
    rw [D.windingNumber_eq]; field_simp
  exact h_eq ▸ D.hasCauchyPV_simplePole c

end SingleCrossingData

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

/-- **T-CC-01 — single-pole CPV at a transverse crossing.**

For a closed (or open) piecewise C¹ path `γ : PiecewiseC1Path x y` admitting a
`SingleCrossingData γ s` (the standard data witnessing a single transverse
crossing of `s`), the simple-pole contribution `c / (z − s)` has a Cauchy
principal value equal to `2πi · w · c`, where
`w = generalizedWindingNumber γ s` is the corner-corrected winding number.

This is the simple-pole (`k = 1`) analogue of `T-SC-01`'s `k ≥ 2` cancellation
result. The simple pole does **not** vanish — it contributes
`2πi · w · residue` to the residue theorem at a crossing. -/
theorem cpv_simplePole_at_crossing
    {γ : PiecewiseC1Path x y} {s : ℂ} (D : SingleCrossingData γ s) (c : ℂ) :
    HasCauchyPV (fun z => c / (z - s)) γ s
      (2 * ↑Real.pi * I * generalizedWindingNumber γ s * c) :=
  D.hasCauchyPV_simplePole_eq_two_pi_I_mul c


/-- **Asymmetric variant of T-CC-01.** Given an `AsymmetricSingleCrossingData γ s`
(separate left/right cutoffs), the simple-pole contribution `c / (z − s)` has a
Cauchy principal value equal to `2πi · w · c`. The asymmetric form admits curves
with `‖L_-‖ ≠ ‖L_+‖` (chord-to-tangent constants differing between the two
sides), which the symmetric `SingleCrossingData` cannot express. -/
theorem cpv_simplePole_at_crossing_asymmetric
    {γ : PiecewiseC1Path x y} {s : ℂ} (D : AsymmetricSingleCrossingData γ s)
    (c : ℂ) :
    HasCauchyPV (fun z => c / (z - s)) γ s
      (2 * ↑Real.pi * I * generalizedWindingNumber γ s * c) :=
  D.hasCauchyPV_simplePole_eq_two_pi_I_mul c


end HungerbuhlerWasem

end
