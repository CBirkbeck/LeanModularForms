# HungerbuhlerWasem/CrossingCPV.lean Inventory

**Path**: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HungerbuhlerWasem/CrossingCPV.lean
**Lines**: 157
**Imports**: `LeanModularForms.ForMathlib.HungerbuhlerWasem`, `LeanModularForms.ForMathlib.SingleCrossing`, `LeanModularForms.ForMathlib.AsymmetricSingleCrossing`, `LeanModularForms.ForMathlib.DixonTheorem`, `LeanModularForms.ForMathlib.CurveMeasureZero`, `LeanModularForms.ForMathlib.FlatnessConditions`

## Entries

### theorem `HungerbuhlerWasem.hasCauchyPV_simplePole_of_inv`
- **Type**: theorem
- **What**: From inverse-CPV to simple-pole CPV: if `HasCauchyPV (·-s)⁻¹ γ s L`, then `HasCauchyPV (c/(·-s)) γ s (c*L)`.
- **How**: `simpa [div_eq_mul_inv] using h.smul c`.
- **Hypotheses**: `c : ℂ`, `h : HasCauchyPV (fun z => (z - s)⁻¹) γ s L`.
- **Uses-from-project**: `HasCauchyPV.smul`, `PiecewiseC1Path`.
- **Used by**: `SingleCrossingData.hasCauchyPV_simplePole`.
- **Visibility**: public (in `HungerbuhlerWasem` namespace)
- **Lines**: 56–60
- **Notes**: Rewrites `c * (z-s)⁻¹` to `c / (z-s)`.

### theorem `SingleCrossingData.hasCauchyPV_simplePole`
- **Type**: theorem
- **What**: Given a `SingleCrossingData γ s`, the CPV of `c / (z - s)` along `γ` exists with value `c · D.L`.
- **How**: `HungerbuhlerWasem.hasCauchyPV_simplePole_of_inv c D.hasCauchyPV`.
- **Hypotheses**: `D : SingleCrossingData γ s`, `c : ℂ`.
- **Uses-from-project**: `SingleCrossingData.hasCauchyPV`, `HungerbuhlerWasem.hasCauchyPV_simplePole_of_inv`.
- **Used by**: `SingleCrossingData.hasCauchyPV_simplePole_eq_two_pi_I_mul`.
- **Visibility**: public (in `SingleCrossingData` namespace)
- **Lines**: 67–70
- **Notes**: One-line lift of the inverse-CPV from the `SingleCrossingData` witness.

### theorem `SingleCrossingData.hasCauchyPV_simplePole_eq_two_pi_I_mul`
- **Type**: theorem
- **What**: Given `SingleCrossingData γ s`, the CPV of `c / (z - s)` along `γ` equals `2πi · w · c` where `w = generalizedWindingNumber γ s`.
- **How**: Establish `h_eq : c * D.L = 2πi · gWN · c` by rewriting via `D.windingNumber_eq` (`L = 2πi · gWN`); use `Complex.two_pi_I_ne_zero` and `field_simp`. Conclude via `h_eq ▸ D.hasCauchyPV_simplePole c`.
- **Hypotheses**: `D : SingleCrossingData γ s`, `c : ℂ`.
- **Uses-from-project**: `SingleCrossingData.windingNumber_eq`, `SingleCrossingData.hasCauchyPV_simplePole`, `Complex.two_pi_I_ne_zero`, `generalizedWindingNumber`.
- **Used by**: `HungerbuhlerWasem.cpv_simplePole_at_crossing`.
- **Visibility**: public (in `SingleCrossingData` namespace)
- **Lines**: 75–84
- **Notes**: Computes the value side and substitutes; `field_simp` resolves the `c * (2πi·gWN) = 2πi·gWN·c` rearrangement.

### theorem `HungerbuhlerWasem.HasCauchyPV.to_singletonOn`
- **Type**: theorem
- **What**: `HasCauchyPV` upgrades to `HasCauchyPVOn {z₀}` (single-point ⇒ multi-point on singleton).
- **How**: `h.congr fun _ => intervalIntegral.integral_congr fun _ _ => cpvIntegrand_eq_cpvIntegrandOn_singleton`.
- **Hypotheses**: `f : ℂ → ℂ`, `γ : PiecewiseC1Path x y`, `z₀ L : ℂ`, `h : HasCauchyPV f γ z₀ L`.
- **Uses-from-project**: `HasCauchyPV.congr`, `cpvIntegrand_eq_cpvIntegrandOn_singleton`.
- **Used by**: `cpv_simplePole_at_crossing_singleton`, `cpv_simplePole_at_crossing_singleton_asymmetric`.
- **Visibility**: public (in `HungerbuhlerWasem` namespace)
- **Lines**: 96–99
- **Notes**: Pointwise integrand agreement promotes single-point CPV to the singleton-set form needed for `HasCauchyPVOn.add` composition.

### theorem `HungerbuhlerWasem.cpv_simplePole_at_crossing`
- **Type**: theorem
- **What**: **T-CC-01** — Single-pole CPV at a transverse crossing: given `SingleCrossingData γ s`, the simple-pole contribution `c / (z − s)` has Cauchy PV equal to `2πi · w · c` (`w = generalizedWindingNumber γ s`).
- **How**: `D.hasCauchyPV_simplePole_eq_two_pi_I_mul c`.
- **Hypotheses**: `D : SingleCrossingData γ s`, `c : ℂ`.
- **Uses-from-project**: `SingleCrossingData.hasCauchyPV_simplePole_eq_two_pi_I_mul`.
- **Used by**: `cpv_simplePole_at_crossing_singleton`.
- **Visibility**: public (in `HungerbuhlerWasem` namespace)
- **Lines**: 115–119
- **Notes**: The simple-pole (k=1) analogue of T-SC-01's k≥2 cancellation result. Headline T-CC-01.

### theorem `HungerbuhlerWasem.cpv_simplePole_at_crossing_singleton`
- **Type**: theorem
- **What**: Singleton-on form of T-CC-01: `HasCauchyPVOn {s} (c/(z-s)) γ (2πi · w · c)`.
- **How**: `HasCauchyPV.to_singletonOn (cpv_simplePole_at_crossing D c)`.
- **Hypotheses**: `D : SingleCrossingData γ s`, `c : ℂ`.
- **Uses-from-project**: `HasCauchyPV.to_singletonOn`, `cpv_simplePole_at_crossing`.
- **Used by**: Multi-pole CPV composition via `HasCauchyPVOn.add`.
- **Visibility**: public (in `HungerbuhlerWasem` namespace)
- **Lines**: 125–129
- **Notes**: Provides the form needed for `HasCauchyPVOn.add` and friends.

### theorem `HungerbuhlerWasem.cpv_simplePole_at_crossing_asymmetric`
- **Type**: theorem
- **What**: Asymmetric variant of T-CC-01: given `AsymmetricSingleCrossingData γ s` (separate left/right cutoffs), the CPV of `c / (z − s)` equals `2πi · w · c`.
- **How**: `D.hasCauchyPV_simplePole_eq_two_pi_I_mul c` (analogous method on `AsymmetricSingleCrossingData`).
- **Hypotheses**: `D : AsymmetricSingleCrossingData γ s`, `c : ℂ`.
- **Uses-from-project**: `AsymmetricSingleCrossingData.hasCauchyPV_simplePole_eq_two_pi_I_mul`.
- **Used by**: `cpv_simplePole_at_crossing_singleton_asymmetric`.
- **Visibility**: public (in `HungerbuhlerWasem` namespace)
- **Lines**: 138–143
- **Notes**: Required for corner crossings where chord-to-tangent constants differ on the two sides — `SingleCrossingData` (symmetric) cannot express this.

### theorem `HungerbuhlerWasem.cpv_simplePole_at_crossing_singleton_asymmetric`
- **Type**: theorem
- **What**: Singleton-on form of the asymmetric variant: `HasCauchyPVOn {s} (c/(z-s)) γ (2πi · w · c)` via `AsymmetricSingleCrossingData`.
- **How**: `HasCauchyPV.to_singletonOn (cpv_simplePole_at_crossing_asymmetric D c)`.
- **Hypotheses**: `D : AsymmetricSingleCrossingData γ s`, `c : ℂ`.
- **Uses-from-project**: `HasCauchyPV.to_singletonOn`, `cpv_simplePole_at_crossing_asymmetric`.
- **Used by**: Multi-pole CPV composition.
- **Visibility**: public (in `HungerbuhlerWasem` namespace)
- **Lines**: 148–153
- **Notes**: Asymmetric companion of `cpv_simplePole_at_crossing_singleton`.

## File Summary

Eight short theorems split between two namespaces (`HungerbuhlerWasem` and the inner `SingleCrossingData`). The headline result is T-CC-01: the simple-pole `c / (z − s)` term has CPV `2πi · w · c` at any transverse crossing witnessed by `SingleCrossingData` (or its asymmetric variant). The proof is essentially by definition of `generalizedWindingNumber` — CPV existence is supplied by the data, and `D.L = 2πi · gWN` by `windingNumber_eq`. Four lemmas + four singleton-on variants. The `to_singletonOn` bridge upgrades each `HasCauchyPV` to `HasCauchyPVOn {s}` so it can be composed via `HasCauchyPVOn.add` into multi-pole CPVs. The asymmetric variants exist because corner crossings (e.g. ρ, ρ+1) have differing tangent constants on the two sides that the symmetric form cannot express.
