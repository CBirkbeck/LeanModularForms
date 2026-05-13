# SimplePoleIntegral.lean Inventory

**Path**: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/SimplePoleIntegral.lean
**Lines**: 171
**Imports**: `LeanModularForms.ForMathlib.MultipointPV`, `LeanModularForms.ForMathlib.GeneralizedWindingNumber`

## Entries

### private theorem `cpvIntegrand_div_eq_mul_inv`
- **Type**: theorem (private)
- **What**: Pointwise equality of `cpvIntegrand` for `c / (z - s)` vs. `c * (z - s)⁻¹`.
- **How**: Unfold `cpvIntegrand`; `split_ifs` and `simp [div_eq_mul_inv]`.
- **Hypotheses**: `c s : ℂ`, `γ : ℝ → ℂ`, `ε t : ℝ` (all explicit).
- **Uses-from-project**: `cpvIntegrand` (from MultipointPV).
- **Used by**: `hasCauchyPV_div_sub` within this file.
- **Visibility**: private
- **Lines**: 53–57
- **Notes**: Algebraic helper, identifies the two equivalent forms of the simple-pole integrand.

### theorem `hasCauchyPV_inv_sub`
- **Type**: theorem
- **What**: PV of `(z - s)⁻¹` along `γ` equals `2πi · w` directly from `HasGeneralizedWindingNumber`.
- **How**: Identity proof — `HasCauchyPV` is the defining property of `HasGeneralizedWindingNumber`, so `hw` itself is the term.
- **Hypotheses**: `hw : HasGeneralizedWindingNumber γ s w`.
- **Uses-from-project**: `HasCauchyPV`, `HasGeneralizedWindingNumber`, `PiecewiseC1Path`.
- **Used by**: Downstream PV chain; foundational lemma exported via `## Main results`.
- **Visibility**: public
- **Lines**: 63–66
- **Notes**: Definitional unfolding; no proof body beyond `:= hw`.

### theorem `hasCauchyPV_div_sub`
- **Type**: theorem
- **What**: PV of `c / (z - s)` equals `2πi · w · c`.
- **How**: Multiply by `c` via `hw.const_mul c`; rewrite product order with `ring`-style `rw [show ...]`; use `HasCauchyPV.congr` plus `intervalIntegral.integral_congr` and `cpvIntegrand_div_eq_mul_inv`.
- **Hypotheses**: `hw : HasGeneralizedWindingNumber γ s w`; `s c : ℂ`, `γ : PiecewiseC1Path x y`, `w : ℂ` implicit.
- **Uses-from-project**: `HasCauchyPV.const_mul`, `HasCauchyPV.congr`, `cpvIntegrand_div_eq_mul_inv`.
- **Used by**: `cauchyPV_div_sub_eq`, `hasCauchyPVOn_singleton_div_sub`, `integral_simple_pole_eq_winding`.
- **Visibility**: public
- **Lines**: 69–77
- **Notes**: Headline result; the `const_mul + congr` pattern.

### theorem `hasCauchyPV_mul_inv_sub`
- **Type**: theorem
- **What**: PV of `c * (z - s)⁻¹` equals `2πi · w · c` (variant of `hasCauchyPV_div_sub`).
- **How**: `hw.const_mul c`; rewrite product order with `show ... from by ring` and exact result.
- **Hypotheses**: `hw : HasGeneralizedWindingNumber γ s w`.
- **Uses-from-project**: `HasCauchyPV.const_mul`.
- **Used by**: Convenience variant; downstream files using `mul` form.
- **Visibility**: public
- **Lines**: 80–85
- **Notes**: Companion to `hasCauchyPV_div_sub` for `mul`-form integrand.

### theorem `cauchyPV_div_sub_eq`
- **Type**: theorem
- **What**: The `cauchyPV` value for `c / (z - s)` is `2πi · w · c`.
- **How**: `(hasCauchyPV_div_sub hw).cauchyPV_eq`.
- **Hypotheses**: `hw : HasGeneralizedWindingNumber γ s w`.
- **Uses-from-project**: `hasCauchyPV_div_sub`, `HasCauchyPV.cauchyPV_eq`.
- **Used by**: Callers wanting the explicit value form.
- **Visibility**: public
- **Lines**: 88–91
- **Notes**: One-line wrapper.

### theorem `cauchyPV_inv_sub_eq`
- **Type**: theorem
- **What**: The `cauchyPV` value for `(z - s)⁻¹` is `2πi · w`.
- **How**: `hw.cauchyPV_eq`.
- **Hypotheses**: `hw : HasGeneralizedWindingNumber γ s w`.
- **Uses-from-project**: `HasGeneralizedWindingNumber.cauchyPV_eq`.
- **Used by**: Downstream PV value lemmas.
- **Visibility**: public
- **Lines**: 94–97
- **Notes**: One-line wrapper.

### theorem `integral_inv_sub_eq_winding`
- **Type**: theorem
- **What**: When `γ` avoids `s` with positive distance δ, ordinary contour integral of `(z-s)⁻¹` equals `2πi · generalizedWindingNumber γ s`.
- **How**: Use `hasGeneralizedWindingNumber_of_avoids` and `hasCauchyPV_of_avoids` to build two `HasCauchyPV` witnesses; conclude via `HasCauchyPV.unique`, then rewrite using `hw.eq`.
- **Hypotheses**: `hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖`.
- **Uses-from-project**: `hasGeneralizedWindingNumber_of_avoids`, `hasCauchyPV_of_avoids`, `HasCauchyPV.unique`, `generalizedWindingNumber`.
- **Used by**: `integral_simple_pole_eq_winding`.
- **Visibility**: public
- **Lines**: 103–111
- **Notes**: Bridges PV and ordinary contour integral in the avoidance case.

### theorem `integral_simple_pole_eq_winding`
- **Type**: theorem
- **What**: When `γ` avoids `s`, contour integral of `c / (z - s)` equals `2πi · generalizedWindingNumber γ s · c`.
- **How**: Same avoid-bound pattern: `hasGeneralizedWindingNumber_of_avoids` + `hasCauchyPV_of_avoids`, then `HasCauchyPV.unique` with `hasCauchyPV_div_sub hw`; rewrite via `hw.eq`.
- **Hypotheses**: `hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖`.
- **Uses-from-project**: `hasGeneralizedWindingNumber_of_avoids`, `hasCauchyPV_of_avoids`, `HasCauchyPV.unique`, `hasCauchyPV_div_sub`, `generalizedWindingNumber`.
- **Used by**: `integral_sum_simple_poles_eq_winding`.
- **Visibility**: public
- **Lines**: 115–123
- **Notes**: Headline corollary for the simple-pole case under avoidance.

### theorem `hasCauchyPVOn_singleton_div_sub`
- **Type**: theorem
- **What**: Singleton-set version: PV of `c / (z - s)` as a `HasCauchyPVOn {s} ...` statement.
- **How**: `hasCauchyPVOn_singleton_of_hasCauchyPV (hasCauchyPV_div_sub hw)`.
- **Hypotheses**: `hw : HasGeneralizedWindingNumber γ s w`.
- **Uses-from-project**: `hasCauchyPVOn_singleton_of_hasCauchyPV`, `hasCauchyPV_div_sub`.
- **Used by**: Multi-pole CPV composition via `HasCauchyPVOn.add`.
- **Visibility**: public
- **Lines**: 128–131
- **Notes**: Singleton bridge for additivity.

### theorem `hasCauchyPVOn_singleton_inv_sub`
- **Type**: theorem
- **What**: Singleton-set version: PV of `(z - s)⁻¹` as a `HasCauchyPVOn {s} ...` statement.
- **How**: `hasCauchyPVOn_singleton_of_hasCauchyPV hw`.
- **Hypotheses**: `hw : HasGeneralizedWindingNumber γ s w`.
- **Uses-from-project**: `hasCauchyPVOn_singleton_of_hasCauchyPV`.
- **Used by**: Composable singleton CPV facts.
- **Visibility**: public
- **Lines**: 134–137
- **Notes**: Companion of `hasCauchyPVOn_singleton_div_sub`.

### theorem `hasCauchyPVOn_sum_div_sub_of_avoids`
- **Type**: theorem
- **What**: When `γ` avoids all `s ∈ S`, the multi-point CPV of `∑ s, c s / (z - s)` equals the ordinary contour integral.
- **How**: Direct application of `hasCauchyPVOn_of_avoids`.
- **Hypotheses**: `hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s‖`.
- **Uses-from-project**: `hasCauchyPVOn_of_avoids`, `PiecewiseC1Path.contourIntegral`.
- **Used by**: Multi-pole assembly.
- **Visibility**: public
- **Lines**: 143–148
- **Notes**: One-line bridge in the avoidance case.

### theorem `integral_sum_simple_poles_eq_winding`
- **Type**: theorem
- **What**: Contour integral of `∑ s ∈ S, c s / (z - s)` equals `∑ s, 2πi · n(γ,s) · c s` when γ avoids all poles.
- **How**: Get `δ` from `hδ`; pointwise `integral_simple_pole_eq_winding` on each `s ∈ S` (named `h_ind`); unfold `contourIntegral` and `extendedPath_eq`; pull out `Finset.sum_mul`; commute `intervalIntegral.integral_finset_sum hI`; close with `Finset.sum_congr rfl h_ind`.
- **Hypotheses**: `hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s‖`; `hI : ∀ s ∈ S, IntervalIntegrable (fun t => (c s / (γ.extend t - s)) * deriv γ.extend t) volume 0 1`.
- **Uses-from-project**: `integral_simple_pole_eq_winding`, `PiecewiseC1Path.contourIntegral`, `generalizedWindingNumber`.
- **Used by**: Final residue theorem statements (closed avoidance form).
- **Visibility**: public
- **Lines**: 155–169
- **Notes**: Key Finset-sum composition step.

## File Summary

Ten public theorems plus one private helper, all about Cauchy PV / contour integrals of simple-pole integrands `c/(z-s)` (and the inverse-form `(z-s)⁻¹`) along piecewise C¹ paths. Splits into two regimes: (i) general PV form directly via `HasGeneralizedWindingNumber` (`hasCauchyPV_inv_sub`, `hasCauchyPV_div_sub`, `hasCauchyPV_mul_inv_sub` and their `cauchyPV_*_eq` value-form companions, plus singleton-set versions); (ii) avoidance form where contour integral coincides with PV (`integral_inv_sub_eq_winding`, `integral_simple_pole_eq_winding`, `hasCauchyPVOn_sum_div_sub_of_avoids`, `integral_sum_simple_poles_eq_winding`). This is the computational core for the generalized residue theorem: the singular part `∑ cₛ/(z-s)` integrates to `∑ 2πi · n(γ,s) · cₛ`.
