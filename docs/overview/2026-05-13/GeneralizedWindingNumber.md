# GeneralizedWindingNumber.lean Inventory

**Path**: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedWindingNumber.lean`
**Top-level**: `noncomputable section` (no namespace); declarations are at root.
**Imports**: `LeanModularForms.ForMathlib.CauchyPrincipalValue`

---

### def `HasGeneralizedWindingNumber`
- **Type**: `PiecewiseC1Path x y → ℂ → ℂ → Prop`
- **What**: Predicate: CPV of `∮_γ (z - z₀)⁻¹ dz` exists and equals `2πi · w`.
- **How**: Reduces to `HasCauchyPV (fun z => (z - z₀)⁻¹) γ z₀ (2 * Real.pi * I * w)`.
- **Hypotheses**: none on the definition itself.
- **Uses-from-project**: `PiecewiseC1Path`, `HasCauchyPV` (from `CauchyPrincipalValue`).
- **Used by**: `HasGeneralizedWindingNumber.eq`, `.unique`, `.neg`, `.cauchyPV_eq_two_pi_I_mul`, `.const_mul`, `hasGeneralizedWindingNumber_of_avoids`, `hasGeneralizedWindingNumber_of_hasCauchyPV`.
- **Visibility**: public
- **Lines**: 61–62
- **Notes**: Tendsto-first API predicate.

### def `generalizedWindingNumber`
- **Type**: `PiecewiseC1Path x y → ℂ → ℂ`
- **What**: Generalized winding number value, `(2πi)⁻¹ · cauchyPV (z↦(z-z₀)⁻¹) γ z₀` (junk if CPV does not exist).
- **How**: One-line definition.
- **Hypotheses**: none.
- **Uses-from-project**: `PiecewiseC1Path`, `cauchyPV`.
- **Used by**: `HasGeneralizedWindingNumber.eq`, `generalizedWindingNumber_eq_of_hasGeneralizedWindingNumber`, `generalizedWindingNumber_continuousAt_of_avoids`.
- **Visibility**: public
- **Lines**: 66–67
- **Notes**: Returns junk on failure of the CPV.

### theorem `HasGeneralizedWindingNumber.eq`
- **Type**: predicate `→ generalizedWindingNumber γ z₀ = w`.
- **What**: Bridge: the CPV predicate determines the value of `generalizedWindingNumber`.
- **How**: Unfolds `generalizedWindingNumber`, rewrites with `h.cauchyPV_eq`, then `field_simp` using `Complex.two_pi_I_ne_zero`.
- **Hypotheses**: `HasGeneralizedWindingNumber γ z₀ w`.
- **Uses-from-project**: `HasGeneralizedWindingNumber`, `generalizedWindingNumber`, `HasCauchyPV.cauchyPV_eq`.
- **Used by**: `generalizedWindingNumber_eq_of_hasGeneralizedWindingNumber`; `generalizedWindingNumber_continuousAt_of_avoids` (via `.eq`).
- **Visibility**: public
- **Lines**: 72–76
- **Notes**: 4 tactic lines.

### theorem `HasGeneralizedWindingNumber.unique`
- **Type**: two witnesses agree.
- **What**: Uniqueness of the winding-number value.
- **How**: Calls `HasCauchyPV.unique` to obtain equality of `2πi·wᵢ`, then `mul_left_cancel₀` using `Complex.two_pi_I_ne_zero`.
- **Hypotheses**: two `HasGeneralizedWindingNumber` witnesses for the same `γ, z₀`.
- **Uses-from-project**: `HasGeneralizedWindingNumber`, `HasCauchyPV.unique`.
- **Used by**: downstream API where uniqueness is needed (e.g. assembling winding-number identities).
- **Visibility**: public
- **Lines**: 81–87
- **Notes**: 5 tactic lines.

### theorem `HasGeneralizedWindingNumber.neg`
- **Type**: gives `HasCauchyPV (z↦ -(z-z₀)⁻¹) γ z₀ (- (2πi·w))`.
- **What**: Negation compatibility for the CPV integrand.
- **How**: Direct application of `HasCauchyPV.neg`.
- **Hypotheses**: `HasGeneralizedWindingNumber γ z₀ w`.
- **Uses-from-project**: `HasCauchyPV.neg`.
- **Used by**: callers needing sign flips of the integrand (orientation reversal).
- **Visibility**: public
- **Lines**: 93–96
- **Notes**: 1-line proof.

### theorem `hasGeneralizedWindingNumber_of_avoids`
- **Type**: avoidance → predicate at the classical contour-integral value `(2πi)⁻¹ · γ.contourIntegral …`.
- **What**: When `γ` is uniformly bounded away from `z₀`, the generalized predicate holds with the classical value.
- **How**: Unfolds the predicate, rewrites the `2πi`-multiplication via a small algebraic `show … from by field_simp` (using `Complex.two_pi_I_ne_zero`), then applies `hasCauchyPV_of_avoids hδ`.
- **Hypotheses**: `∃ δ > 0, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - z₀‖` (positive infimum distance).
- **Uses-from-project**: `HasGeneralizedWindingNumber`, `hasCauchyPV_of_avoids`, `PiecewiseC1Path.contourIntegral`.
- **Used by**: `generalizedWindingNumber_continuousAt_of_avoids` (eventual equality on balls).
- **Visibility**: public
- **Lines**: 102–111
- **Notes**: 7 tactic lines.

### theorem `HasGeneralizedWindingNumber.cauchyPV_eq_two_pi_I_mul`
- **Type**: `cauchyPV (z↦(z-z₀)⁻¹) γ z₀ = 2πi · w`.
- **What**: Direct readout of the CPV value once the predicate holds.
- **How**: `h.cauchyPV_eq` (single term-level call).
- **Hypotheses**: predicate holds.
- **Uses-from-project**: `HasCauchyPV.cauchyPV_eq`.
- **Used by**: downstream identities that need the raw CPV value.
- **Visibility**: public
- **Lines**: 117–121
- **Notes**: Term-mode.

### theorem `hasGeneralizedWindingNumber_of_hasCauchyPV`
- **Type**: CPV with limit `L` → predicate with `w := (2πi)⁻¹ · L`.
- **What**: Converse to the bridge: a CPV witness implies the generalized winding-number witness.
- **How**: Unfolds the predicate, rewrites `2πi · ((2πi)⁻¹ · L) = L` via a small `show … from by field_simp` (using `Complex.two_pi_I_ne_zero`), then `rwa`.
- **Hypotheses**: `HasCauchyPV (z↦(z-z₀)⁻¹) γ z₀ L`.
- **Uses-from-project**: `HasGeneralizedWindingNumber`, `HasCauchyPV`.
- **Used by**: bridging external CPV results into the winding-number predicate.
- **Visibility**: public
- **Lines**: 127–132
- **Notes**: 4 tactic lines.

### theorem `generalizedWindingNumber_eq_of_hasGeneralizedWindingNumber`
- **Type**: predicate → value equation.
- **What**: Restatement of the bridge as a free theorem (no dot notation).
- **How**: Direct term `h.eq`.
- **Hypotheses**: predicate holds.
- **Uses-from-project**: `HasGeneralizedWindingNumber.eq`.
- **Used by**: callers preferring the un-dotted name.
- **Visibility**: public
- **Lines**: 136–139
- **Notes**: 1-line proof.

### theorem `HasGeneralizedWindingNumber.const_mul`
- **Type**: scaled CPV identity: `HasCauchyPV (z↦ c·(z-z₀)⁻¹) γ z₀ (c · (2πi · w))`.
- **What**: Scalar-multiplication compatibility.
- **How**: `h.smul c` (term-level).
- **Hypotheses**: predicate; constant `c`.
- **Uses-from-project**: `HasCauchyPV.smul`.
- **Used by**: weighted winding-number constructions.
- **Visibility**: public
- **Lines**: 145–148
- **Notes**: 1-line proof.

### lemma `ball_dist_to_curve_lb`
- **Type**: from a curve avoiding `w₀`, produce a ball around `w₀` on which every `w` has uniform distance `≥ ε` to the whole curve.
- **What**: Strengthens "avoids" to a uniform lower bound valid on a small ball around `w₀`.
- **How**: Compact image `γ.toPath.extend '' Icc 0 1` is closed; uses `IsClosed.notMem_iff_infDist_pos`, set `ε := infDist/2`, then triangle inequality `‖γ t - w₀‖ ≤ ‖γ t - w‖ + ‖w - w₀‖` combined with `Metric.mem_ball.mp`/`Complex.dist_eq` and `linarith` (proof spans lines 153–179; >10 lines; key lemmas named).
- **Hypotheses**: `∀ t ∈ Icc 0 1, γ t ≠ w₀`.
- **Uses-from-project**: `PiecewiseC1Path` (`γ.toPath.extend` and continuity).
- **Used by**: `generalizedWindingNumber_continuousAt_of_avoids`.
- **Visibility**: public
- **Lines**: 153–179
- **Notes**: Quotient `infDist/2` keeps `w` safely inside the favorable region.

### theorem `generalizedWindingNumber_continuousAt_of_avoids`
- **Type**: `ContinuousAt (generalizedWindingNumber γ) w₀` for `w₀` off a Lipschitz piecewise-C¹ curve.
- **What**: Continuity of the winding-number function at any point not on the (Lipschitz) curve.
- **How**: Get a ball + uniform distance bound from `ball_dist_to_curve_lb`; rewrite `generalizedWindingNumber` on the ball using `hasGeneralizedWindingNumber_of_avoids.eq`; apply `intervalIntegral.continuousAt_of_dominated_interval` with constant bound `ε⁻¹ · K` (using `norm_deriv_le_of_lipschitz`); AE measurability from `ContinuousOn.aestronglyMeasurable` × `stronglyMeasurable_deriv` (proof spans lines 185–236; >10 lines; key lemmas named).
- **Hypotheses**: curve avoids `w₀`; `LipschitzWith K γ.toPath.extend`.
- **Uses-from-project**: `ball_dist_to_curve_lb`, `hasGeneralizedWindingNumber_of_avoids`, `HasGeneralizedWindingNumber.eq`, `PiecewiseC1Path.contourIntegral`, `generalizedWindingNumber`.
- **Used by**: external analysis where continuity of `gWN` off the curve is needed (e.g. integer-valuedness, homotopy).
- **Visibility**: public
- **Lines**: 185–236
- **Notes**: Uses parametric continuity for integrals (Mathlib's dominated-convergence-style continuity).

---

## File Summary

GeneralizedWindingNumber.lean introduces the CPV-based winding number for piecewise-C¹ paths, following Hungerbühler–Wasem. It defines a Tendsto-first predicate `HasGeneralizedWindingNumber` and a junk-on-failure value `generalizedWindingNumber`, then proves the bridge `predicate → value`, uniqueness, negation/scaling compatibilities, two converters between `HasCauchyPV` and the new predicate, an avoidance theorem matching the classical contour integral, and finally continuity of the winding-number function at any point off a Lipschitz piecewise-C¹ curve (helper `ball_dist_to_curve_lb` extracts a uniform distance lower bound on a ball around the off-curve point).
