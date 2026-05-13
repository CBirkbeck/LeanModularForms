# FlatChordBound.lean Inventory

**Path**: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/FlatChordBound.lean`
**Namespace**: `LeanModularForms`
**Imports**: `LeanModularForms.ForMathlib.FlatnessConditions`

---

### theorem `orthogonal_deviation_at_radius_right`
- **Type**: `‖tangentDeviation (γ t - s) L‖ =o[𝓝[>] t₀] (fun t => ‖γ t - s‖ ^ n)`.
- **What**: Right-side restatement of `IsFlatOfOrder.right_flat` after substituting `γ t₀ = s`: the orthogonal deviation is `o(‖γ-s‖ⁿ)` from the right.
- **How**: Pulls `h_flat.right_flat L hL hL_right`, rewrites `γ t - γ t₀` to `γ t - s` by `simp only [h_eq]`, then `exact h`.
- **Hypotheses**: `IsFlatOfOrder γ t₀ n`; `L ≠ 0`; `Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)`; `γ t₀ = s`.
- **Uses-from-project**: `IsFlatOfOrder`, `IsFlatOfOrder.right_flat`, `tangentDeviation` (all from `FlatnessConditions`).
- **Used by**: Phase 3.3 chord-bound consumers (HW Theorem 3.3 higher-order proof on the right side).
- **Visibility**: public
- **Lines**: 47–57
- **Notes**: 5 tactic lines.

### theorem `orthogonal_deviation_at_radius_left`
- **Type**: symmetric on `𝓝[<] t₀`.
- **What**: Left-side counterpart of the right-side orthogonal-deviation bound.
- **How**: Same template using `h_flat.left_flat L hL hL_left`, `simp only [h_eq]`, `exact h`.
- **Hypotheses**: `IsFlatOfOrder γ t₀ n`; `L ≠ 0`; `Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L)`; `γ t₀ = s`.
- **Uses-from-project**: `IsFlatOfOrder.left_flat`, `tangentDeviation`.
- **Used by**: left-side chord-bound consumers.
- **Visibility**: public
- **Lines**: 60–70
- **Notes**: Mirror of the right-side proof.

### theorem `orthogonal_pythagoras`
- **Type**: `‖orthogonalProjectionComplex w L‖² + ‖tangentDeviation w L‖² = ‖w‖²`.
- **What**: Pythagorean identity for the parallel/orthogonal decomposition of `w` relative to `L`.
- **How**: Splits `L = 0` vs `L ≠ 0`; in the nonzero case, expands `Complex.sq_norm`, then sets `u := (w · conj L).re`, `N := Complex.normSq L`, computes `Complex.normSq ((u/N : ℂ) * L) = (u/N)²·N` via `Complex.normSq_mul + normSq_ofReal` and the cross-term `(w · conj((u/N)·L)).re = (u/N)·u` via `Complex.conj_ofReal` plus rearrangement; finishes with `Complex.normSq_sub`, `field_simp`, `ring` (proof spans lines 78–99; >10 lines; key lemmas named).
- **Hypotheses**: arbitrary `w L : ℂ`.
- **Uses-from-project**: `orthogonalProjectionComplex`, `tangentDeviation`.
- **Used by**: `norm_sq_orthogonalProjection`, `norm_orthogonalProjection_shortfall_le`, `norm_orthogonalProjection_minus_target_eq`, `norm_chord_to_tangent_target_le`.
- **Visibility**: public
- **Lines**: 78–99
- **Notes**: Central algebraic identity for the file.

### theorem `norm_sq_orthogonalProjection`
- **Type**: `‖orthogonalProjectionComplex w L‖² = ‖w‖² - ‖tangentDeviation w L‖²`.
- **What**: Solved form of `orthogonal_pythagoras` for the parallel component.
- **How**: `have := orthogonal_pythagoras w L; linarith`.
- **Hypotheses**: arbitrary `w L`.
- **Uses-from-project**: `orthogonal_pythagoras`.
- **Used by**: clients reasoning about the parallel projection's norm.
- **Visibility**: public
- **Lines**: 103–106
- **Notes**: 2-line proof.

### theorem `real_sqrt_shortfall_le`
- **Type**: `ε - √(ε² - δ²) ≤ δ²/ε` for `0 < ε`, `0 ≤ δ ≤ ε`.
- **What**: Sqrt-shortfall estimate by rationalization: bounds `ε - √(ε² - δ²)` by `δ²/ε`.
- **How**: Sets up `h_sq_nonneg`, `h_sqrt_sq` (via `Real.sq_sqrt`), `h_eq : (ε - √…)·(ε + √…) = δ²` (using `linarith` on squared identity and `sq_nonneg`), turns it into `h_diff_eq : ε - √… = δ²/(ε + √…)` by `field_simp` + `linarith`, then `div_le_div_of_nonneg_left` against `ε ≤ ε + √…` (proof spans lines 120–138; >10 lines; key lemmas named).
- **Hypotheses**: `0 < ε`, `0 ≤ δ`, `δ ≤ ε`.
- **Uses-from-project**: none beyond Mathlib (`Real.sqrt`, `Real.sq_sqrt`).
- **Used by**: `norm_orthogonalProjection_shortfall_le`.
- **Visibility**: public
- **Lines**: 120–138
- **Notes**: Key arithmetic estimate for the chord bound.

### theorem `norm_orthogonalProjection_shortfall_le`
- **Type**: `‖w‖ - ‖orthogonalProjectionComplex w L‖ ≤ ‖tangentDeviation w L‖² / ‖w‖`.
- **What**: Shortfall of the parallel-projection's norm against `‖w‖` is bounded by the orthogonal-deviation squared over `‖w‖`.
- **How**: Take `h_pyth := orthogonal_pythagoras`, derive `h_proj_sq` by `linarith`, then `h_dev_le : ‖tangentDev‖ ≤ ‖w‖` by `nlinarith` on the nonneg difference; apply `real_sqrt_shortfall_le hw h_dev_nonneg h_dev_le`, then rewrite the sqrt back to `‖proj‖` via `Real.sqrt_sq` (proof spans lines 148–167; >10 lines; key lemmas named).
- **Hypotheses**: `0 < ‖w‖`.
- **Uses-from-project**: `orthogonal_pythagoras`, `real_sqrt_shortfall_le`, `tangentDeviation`, `orthogonalProjectionComplex`.
- **Used by**: `norm_chord_to_tangent_target_le`.
- **Visibility**: public
- **Lines**: 148–167
- **Notes**: Combines Pythagoras with sqrt asymptotic.

### theorem `norm_orthogonalProjection_minus_target_eq`
- **Type**: when `Re(w · conj L) ≥ 0`, `‖orthogonalProj w L - (‖w‖/‖L‖) • L‖ = ‖w‖ - ‖orthogonalProj w L‖`.
- **What**: Same-direction shortfall identity: in the `+L`-hemisphere, the difference between the parallel projection and the same-magnitude target on the `+L` ray is exactly the magnitude shortfall.
- **How**: Sets `c := (w · conj L).re / Complex.normSq L ≥ 0`, computes `‖orthogonalProj‖ = c · ‖L‖` via `norm_smul`, proves `‖orthogonalProj‖ ≤ ‖w‖` from Pythagoras (`abs_le_of_sq_le_sq'`), derives `c ≤ ‖w‖/‖L‖` via `le_div_iff₀`, factors `(c - ‖w‖/‖L‖) • L`, `norm_smul`, `abs_of_nonpos`, then `field_simp + ring` (proof spans lines 181–208; >10 lines; key lemmas named).
- **Hypotheses**: `L ≠ 0`; `0 ≤ (w · conj L).re`.
- **Uses-from-project**: `orthogonal_pythagoras`, `orthogonalProjectionComplex`, `tangentDeviation`.
- **Used by**: `norm_chord_to_tangent_target_le`.
- **Visibility**: public
- **Lines**: 181–208
- **Notes**: Captures the geometric "same-ray" simplification.

### theorem `norm_chord_to_tangent_target_le`
- **Type**: `‖w - (‖w‖/‖L‖) • L‖ ≤ ‖tangentDeviation w L‖ + ‖tangentDeviation w L‖² / ‖w‖` under `+L`-hemisphere and `0 < ‖w‖`.
- **What**: Full chord-to-tangent bound: distance from `w` to the natural tangent target is dominated by orthogonal deviation plus its squared shortfall.
- **How**: Decomposes `w - (‖w‖/‖L‖)•L = (orthogonalProj w L - (‖w‖/‖L‖)•L) + tangentDeviation w L` (by `ring` after `unfold tangentDeviation`); triangle inequality `norm_add_le`; replaces the first summand by the shortfall identity (`norm_orthogonalProjection_minus_target_eq`); adds `norm_orthogonalProjection_shortfall_le` and concludes with `linarith` (proof spans lines 220–233; >10 lines; key lemmas named).
- **Hypotheses**: `L ≠ 0`; `0 < ‖w‖`; `0 ≤ (w · conj L).re`.
- **Uses-from-project**: `orthogonalProjectionComplex`, `tangentDeviation`, `norm_orthogonalProjection_minus_target_eq`, `norm_orthogonalProjection_shortfall_le`.
- **Used by**: HW Theorem 3.3 higher-order chord analysis (Phase 3.3 consumer; downstream connecting-arc analysis).
- **Visibility**: public
- **Lines**: 220–233
- **Notes**: This is the named target theorem of the file.

---

## File Summary

FlatChordBound.lean is Phase 3.3 of the HW Theorem 3.3 higher-order proof — it bridges parameter-based flatness to radius-based chord bounds. Two `orthogonal_deviation_at_radius_{right,left}` theorems restate `IsFlatOfOrder.{right,left}_flat` after substituting `γ t₀ = s`. The arithmetic core is `orthogonal_pythagoras` (Pythagorean identity for the complex parallel/orthogonal decomposition), specialized to `norm_sq_orthogonalProjection`. The sqrt-shortfall estimate `real_sqrt_shortfall_le` and Pythagoras combine in `norm_orthogonalProjection_shortfall_le`. The geometric same-ray identity `norm_orthogonalProjection_minus_target_eq` (for points in the `+L` hemisphere) plus the shortfall bound yield the headline result `norm_chord_to_tangent_target_le`, bounding the chord from `w` to its natural tangent target by `‖tangentDev‖ + ‖tangentDev‖²/‖w‖`.
