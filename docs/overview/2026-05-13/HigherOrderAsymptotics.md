# HigherOrderAsymptotics.lean Inventory

File: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HungerbuhlerWasem/HigherOrderAsymptotics.lean
Lines: 785
Namespace: `HungerbuhlerWasem`

### `theorem tangentApproximation_of_isFlatOfOrder_right`
- **Type**: From `IsFlatOfOrder γ t₀ n` + right derivative `L ≠ 0` + local differentiability + continuity → `(fun t => ‖tangentDeviation (γ t − γ t₀) L‖) =o[𝓝[>] t₀] (|t − t₀|^n)`.
- **What**: Right-side: tangent deviation is `o(|t − t₀|^n)`.
- **How**: Use `h_flat.right_flat` to get `o(‖γt − γt₀‖^n)`; build `HasDerivWithinAt γ L (Ioi t₀) t₀` from `hasDerivWithinAt_Ioi_iff_Ici.mpr (hasDerivWithinAt_Ici_of_tendsto_deriv ...)`; conclude `(γt − γt₀) =O (t − t₀)` via `isBigO_sub`; raise to `n`-th power (`.pow n`); transfer norms via `norm_pow` and `Real.norm_eq_abs`; chain `trans_isBigO`.
- **Hypotheses**: `h_flat`, `hL ≠ 0`, `hL_right`, `hγ_diff` eventually, `hγ_cont`.
- **Uses from project**: `IsFlatOfOrder`, `tangentDeviation`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 55-83.
- **Notes**: 29 lines.

### `theorem tangentApproximation_of_isFlatOfOrder_left`
- **Type**: Mirror of the previous for left-side limits.
- **What**: Left-side: tangent deviation is `o(|t − t₀|^n)`.
- **How**: Identical scaffolding to the right-side proof, using `h_flat.left_flat`, `hasDerivWithinAt_Iio_iff_Iic`, and `hasDerivWithinAt_Iic_of_tendsto_deriv`.
- **Hypotheses**: `h_flat`, `hL ≠ 0`, `hL_left`, `hγ_diff` eventually, `hγ_cont`.
- **Uses from project**: `IsFlatOfOrder`, `tangentDeviation`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 87-115.
- **Notes**: 29 lines (mirror of right-side).

### `theorem hasDerivAt_antiderivative_pow_inv`
- **Type**: `(hk : 2 ≤ k) (hγ : HasDerivAt γ γ' t) (h_ne : γ t − s ≠ 0) → HasDerivAt (fun u => −((k−1)⁻¹)·((γu − s)^(k−1))⁻¹) (γ' / (γ t − s)^k) t`.
- **What**: Antiderivative of `γ'/(γ−s)^k` for `k ≥ 2`.
- **How**: Chain rule: differentiate `γ u − s`, then `(γu−s)^(k−1)`, then take inverse via `hasDerivAt_inv` (composition with `scomp`), multiply by the constant `−(k−1)⁻¹`; reconcile with the target via `convert _ using 1` + a power identity `(γt−s)^(2(k−1)) = (γt−s)^k · (γt−s)^(k−2)` and `field_simp`.
- **Hypotheses**: `2 ≤ k`, `HasDerivAt γ γ' t`, `γ t ≠ s`.
- **Uses from project**: [].
- **Used by**: `integral_pow_inv_eq_FTC`.
- **Visibility**: public.
- **Lines**: 125-149.
- **Notes**: 25 lines.

### `theorem integral_pow_inv_eq_FTC`
- **Type**: `(hk : 2 ≤ k) (hγ : ∀ t ∈ uIcc a b, HasDerivAt γ (γ' t) t) (h_avoids : ∀ t ∈ uIcc a b, γ t ≠ s) (h_int) → ∫ a..b, γ'/(γ−s)^k = F(γ b) − F(γ a)`, where `F(z) := −(k−1)⁻¹·(z−s)^{-(k−1)}`.
- **What**: Fundamental theorem of calculus for `γ'/(γ−s)^k` on a smooth piece.
- **How**: Apply `intervalIntegral.integral_eq_sub_of_hasDerivAt` with pointwise derivative `hasDerivAt_antiderivative_pow_inv` and the avoidance hypothesis.
- **Hypotheses**: `hk ≥ 2`, smoothness/avoidance on `uIcc a b`, integrability.
- **Uses from project**: `hasDerivAt_antiderivative_pow_inv`.
- **Used by**: `closed_excised_integral_eq_antideriv_diff`.
- **Visibility**: public.
- **Lines**: 156-167.
- **Notes**: short.

### `theorem hasDerivAt_antiderivative_pow_inv_complex`
- **Type**: `(hk : 2 ≤ k) (hz : z ≠ s) → HasDerivAt (fun w => −((k−1)⁻¹)·((w−s)^(k−1))⁻¹) (1 / (z−s)^k) z`.
- **What**: Complex-variable antiderivative: the function `F(w) := −(k−1)⁻¹·(w−s)^{-(k−1)}` is `ℂ`-differentiable with derivative `1/(w−s)^k`.
- **How**: Identical scaffolding to the real composition lemma but starting from `(hasDerivAt_id z).sub_const s`; uses `HasDerivAt.inv`, multiplied by the constant; `convert ... using 1`, power identity, `field_simp`.
- **Hypotheses**: `2 ≤ k`, `z ≠ s`.
- **Uses from project**: [].
- **Used by**: `norm_F_diff_le_segment_bound`.
- **Visibility**: public.
- **Lines**: 173-195.
- **Notes**: 23 lines.

### `theorem closed_excised_integral_eq_antideriv_diff`
- **Type**: For closed `γ a = γ b` and `k ≥ 2`, the parameter-excised integral over `[a, t_minus] ∪ [t_plus, b]` equals `F(γ t_minus) − F(γ t_plus)`.
- **What**: Closed-form expression for the parameter-excised integral via antiderivative endpoints.
- **How**: Apply `integral_pow_inv_eq_FTC` on each smooth piece and use `h_close` plus `ring` to collapse the endpoints.
- **Hypotheses**: `hk`, `h_close`, smoothness, avoidance, integrability of both wings.
- **Uses from project**: `integral_pow_inv_eq_FTC`.
- **Used by**: `cpv_excised_tendsto_zero_of_F_diff_zero`.
- **Visibility**: public.
- **Lines**: 202-218.
- **Notes**: short (17 lines).

### `theorem norm_F_diff_le_segment_bound`
- **Type**: For `z₁, z₂, s` with segment from `z₁` to `z₂` at distance `≥ ε` from `s`: `‖F(z₂) − F(z₁)‖ ≤ (1/ε^k)·‖z₂ − z₁‖`.
- **What**: Mean-value-style segment bound for the antiderivative `F`.
- **How**: KEY: `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` applied to the segment with pointwise complex derivative (`hasDerivAt_antiderivative_pow_inv_complex`) bounded by `1/ε^k` via `pow_le_pow_left₀` and `div_le_div_of_nonneg_left`.
- **Hypotheses**: `2 ≤ k`, `0 < ε`, segment avoids `s` with margin `ε`.
- **Uses from project**: `hasDerivAt_antiderivative_pow_inv_complex`.
- **Used by**: `norm_F_diff_at_tangent_target_le`.
- **Visibility**: public.
- **Lines**: 225-249.
- **Notes**: 25 lines.

### `theorem eventually_re_pos_right`
- **Type**: For `γ` with right-derivative `L ≠ 0` at `t₀` and `γ t₀ = s`: eventually for `t → t₀⁺`, `Re((γt − s)·conj L) ≥ 0`.
- **What**: The right-side curve emerges into the `+L` hemisphere.
- **How**: Use `HasDerivWithinAt.isLittleO` to bound `‖γt − γt₀ − (t−t₀)·L‖ ≤ ‖L‖/2 · |t−t₀|`; decompose `γt − s = (t−t₀)·L + remainder`, compute `((t−t₀)·L · conj L).re = (t−t₀)·‖L‖^2`, and bound the remainder term using `abs_re_le_norm` and `Complex.norm_conj`; close with `nlinarith`.
- **Hypotheses**: `hL ≠ 0`, `HasDerivWithinAt γ L (Ioi t₀) t₀`, `γ t₀ = s`.
- **Uses from project**: [].
- **Used by**: `chord_to_tangent_isLittleO_right`.
- **Visibility**: public.
- **Lines**: 256-288.
- **Notes**: 33 lines.

### `theorem eventually_re_neg_left`
- **Type**: Left-side analogue: eventually for `t → t₀⁻`, `Re((γt − s)·conj L) ≤ 0`.
- **What**: Left-side: curve emerges into the `−L` hemisphere.
- **How**: Mirror of `eventually_re_pos_right` with sign adjustments — `t − t₀ < 0`, `‖t − t₀‖ = −(t − t₀)`.
- **Hypotheses**: as above with `Iio t₀`.
- **Uses from project**: [].
- **Used by**: `chord_to_tangent_isLittleO_left`.
- **Visibility**: public.
- **Lines**: 292-324.
- **Notes**: 33 lines.

### `theorem eventually_ne_right`
- **Type**: With right derivative `L ≠ 0` and `γ t₀ = s`: eventually `γ t ≠ s` for `t → t₀⁺`.
- **What**: Right-side curve cannot stay at `s` past `t₀`.
- **How**: From `HasDerivWithinAt.isLittleO`: bound the remainder `‖γt − γt₀ − (t−t₀)·L‖ ≤ ‖L‖/2 · |t − t₀|`; if `γ t = s = γ t₀`, then the remainder equals `−(t − t₀)·L` whose norm is `‖L‖ · (t − t₀)`, contradicting `(‖L‖/2) · (t − t₀)`; `nlinarith`.
- **Hypotheses**: `hL ≠ 0`, `HasDerivWithinAt γ L (Ioi t₀) t₀`, `γ t₀ = s`.
- **Uses from project**: [].
- **Used by**: `chord_to_tangent_isLittleO_right`, `F_diff_at_tangent_target_tendsto_zero_right`.
- **Visibility**: public.
- **Lines**: 329-351.
- **Notes**: 23 lines.

### `theorem eventually_ne_left`
- **Type**: Left-side: eventually `γ t ≠ s` for `t → t₀⁻`.
- **What**: Left-side curve cannot stay at `s` past `t₀`.
- **How**: Mirror of `eventually_ne_right` with sign adjustments.
- **Hypotheses**: `hL ≠ 0`, `HasDerivWithinAt γ L (Iio t₀) t₀`, `γ t₀ = s`.
- **Uses from project**: [].
- **Used by**: `chord_to_tangent_isLittleO_left`, `F_diff_at_tangent_target_tendsto_zero_left`.
- **Visibility**: public.
- **Lines**: 354-376.
- **Notes**: 23 lines.

### `theorem chord_to_tangent_isLittleO_right`
- **Type**: `(fun t => ‖γ t − s − (‖γt − s‖/‖L‖)·L‖) =o[𝓝[>] t₀] (‖γt − s‖^n)`.
- **What**: The chord from `γ t` to the radial tangent target on the `+L` ray is `o(‖γt − s‖^n)`.
- **How**: KEY: `LeanModularForms.orthogonal_deviation_at_radius_right` gives `o(‖γt − s‖^n)` for tangent deviation; combine via `LeanModularForms.norm_chord_to_tangent_target_le` (chord ≤ 3·deviation under positivity/non-vanishing) — established `eventually` using `eventually_re_pos_right` and `eventually_ne_right`; bound `deviation^2 / d ≤ 2·deviation` via `norm_tangentDeviation_le`; conclude with `IsBigO.of_bound 3` and `trans_isLittleO`.
- **Hypotheses**: `h_flat`, `hL`, `h_deriv`, `hL_right`, `h_s`.
- **Uses from project**: `IsFlatOfOrder`, `tangentDeviation`, `LeanModularForms.orthogonal_deviation_at_radius_right`, `LeanModularForms.norm_chord_to_tangent_target_le`, `norm_tangentDeviation_le`, `eventually_re_pos_right`, `eventually_ne_right`.
- **Used by**: `F_diff_at_tangent_target_tendsto_zero_right`.
- **Visibility**: public.
- **Lines**: 382-419.
- **Notes**: 38 lines.

### `theorem chord_to_tangent_isLittleO_left`
- **Type**: Left-side version: with target on the `−L` ray.
- **What**: Left-side chord-to-tangent o-relation.
- **How**: As right-side but with `−L` substituted; use `LeanModularForms.orthogonal_deviation_at_radius_left`, prove `tangentDeviation (·) (−L) = tangentDeviation (·) L` via `Complex.normSq_neg` and `Complex.neg_re`, and convert the `re_neg_left` eventual sign condition to the `+L` form via `map_neg` and `Complex.neg_re`.
- **Hypotheses**: `h_flat`, `hL`, `h_deriv` (Iio), `hL_left`, `h_s`.
- **Uses from project**: `IsFlatOfOrder`, `tangentDeviation`, `orthogonalProjectionComplex`, `LeanModularForms.orthogonal_deviation_at_radius_left`, `LeanModularForms.norm_chord_to_tangent_target_le`, `norm_tangentDeviation_le`, `eventually_re_neg_left`, `eventually_ne_left`.
- **Used by**: `F_diff_at_tangent_target_tendsto_zero_left`.
- **Visibility**: public.
- **Lines**: 423-483.
- **Notes**: 61 lines (long — needs an additional unfolding/equality between `tangentDeviation _ (−L)` and `tangentDeviation _ L`).

### `theorem norm_sq_segment_to_pole_lower_bound`
- **Type**: For `z₁, z₂` equidistant (`= d`) from `s` and `z` on the segment, `d^2 − ‖z₁ − z₂‖^2/4 ≤ ‖z − s‖^2`.
- **What**: Lower bound on the segment distance to a fixed pole.
- **How**: Unpack `z = α·z₁ + β·z₂` with `α + β = 1`; expand `‖α(z₁−s) + β(z₂−s)‖^2` using `Complex.sq_norm` and `Complex.normSq_add/mul`; use cross-product identity from `normSq_sub` to express `Re((z₁−s)·conj (z₂−s))` in terms of `‖z₁−s‖^2 + ‖z₂−s‖^2 − ‖z₁−z₂‖^2`; rewrite, then `nlinarith` with `α·β ≤ 1/4` (`(α−β)^2 ≥ 0`).
- **Hypotheses**: `‖z₁ − s‖ = d`, `‖z₂ − s‖ = d`, `z ∈ segment ℝ z₁ z₂`.
- **Uses from project**: [].
- **Used by**: `norm_segment_to_pole_lower_bound_half`.
- **Visibility**: public.
- **Lines**: 489-533.
- **Notes**: 45 lines.

### `theorem norm_segment_to_pole_lower_bound_half`
- **Type**: For chord `‖z₁ − z₂‖ ≤ d`, the segment from `z₁` to `z₂` stays at distance `≥ d/2` from `s`.
- **What**: When the chord is at most `d`, segment never gets closer to `s` than `d/2`.
- **How**: Use `norm_sq_segment_to_pole_lower_bound`, bound `(d/2)^2 ≤ ‖z−s‖^2`, then `abs_le_of_sq_le_sq'` to extract `‖z−s‖ ≥ d/2`.
- **Hypotheses**: `_hd_pos`, `‖z₁ − s‖ = d`, `‖z₂ − s‖ = d`, `chord ≤ d`, segment membership.
- **Uses from project**: `norm_sq_segment_to_pole_lower_bound`.
- **Used by**: `norm_F_diff_at_tangent_target_le`.
- **Visibility**: public.
- **Lines**: 537-546.
- **Notes**: short.

### `theorem norm_F_diff_at_tangent_target_le`
- **Type**: `‖F(γt) − F(tgt)‖ ≤ (1/(‖γt−s‖/2)^k) · ‖γt − tgt‖` where `tgt = s + (‖γt−s‖/‖L‖)·L`.
- **What**: F-difference vs tangent-target bound, given a chord control `‖γt − tgt‖ ≤ ‖γt − s‖`.
- **How**: Apply `norm_segment_to_pole_lower_bound_half` to verify segment stays at distance `≥ ‖γt−s‖/2` from `s`, then `norm_F_diff_le_segment_bound` (with `ε := d/2`); finally swap the sign so the absolute-value notation works (`norm_sub_rev`, `norm_neg`).
- **Hypotheses**: `2 ≤ k`, `hL ≠ 0`, `γ t ≠ s`, chord ≤ d.
- **Uses from project**: `norm_F_diff_le_segment_bound`, `norm_segment_to_pole_lower_bound_half`.
- **Used by**: `F_diff_at_tangent_target_tendsto_zero_right`, `F_diff_at_tangent_target_tendsto_zero_left`.
- **Visibility**: public.
- **Lines**: 551-575.
- **Notes**: 25 lines.

### `theorem tendsto_div_pow_zero_of_isLittleO`
- **Type**: `chord =o[l] (d^n)` and `d → 0` (positive) and `k ≤ n` → `chord / d^k → 0`.
- **What**: Auxiliary o-asymptotic: when chord is `o(d^n)` and `k ≤ n`, the ratio `chord/d^k` tends to zero.
- **How**: `Metric.tendsto_nhds`: for given ε, use `h_chord.bound (ε/2)`; eventually `d < 1` (from `d → 0`); estimate `|chord|/d^k ≤ (ε/2)·d^(n−k) ≤ ε/2` since `d^(n−k) ≤ 1`.
- **Hypotheses**: `chord =o[l] d^n`, `d → 0`, eventually `d > 0`, `k ≤ n`.
- **Uses from project**: [].
- **Used by**: `F_diff_at_tangent_target_tendsto_zero_right`, `F_diff_at_tangent_target_tendsto_zero_left`.
- **Visibility**: public.
- **Lines**: 581-610.
- **Notes**: 30 lines.

### `theorem F_diff_at_tangent_target_tendsto_zero_right`
- **Type**: Under `h_flat`, `hL`, right-derivative, `hL_right`, `h_s`, `2 ≤ k ≤ n`, `1 ≤ n`: F-difference between `γt` and the tangent target tends to zero from the right.
- **What**: Right-side: F-diff vs tangent target → 0.
- **How**: KEY: chord-isLittleO from `chord_to_tangent_isLittleO_right`; `d := ‖γt − s‖ → 0` from continuity; eventually `d > 0` from `eventually_ne_right`; ratio `chord/d^k → 0` via `tendsto_div_pow_zero_of_isLittleO`; eventually chord ≤ d via `pow_le_pow_of_le_one` (uses `n ≥ 1`); F-difference bounded via `norm_F_diff_at_tangent_target_le`; squeeze via `tendsto_of_tendsto_of_tendsto_of_le_of_le'`.
- **Hypotheses**: `h_flat`, `hL`, `h_deriv` (Ioi), `hL_right`, `h_s`, `2 ≤ k`, `k ≤ n`, `1 ≤ n`.
- **Uses from project**: `IsFlatOfOrder`, `chord_to_tangent_isLittleO_right`, `eventually_ne_right`, `tendsto_div_pow_zero_of_isLittleO`, `norm_F_diff_at_tangent_target_le`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 615-674.
- **Notes**: 60 lines.

### `theorem F_diff_at_tangent_target_tendsto_zero_left`
- **Type**: Left-side counterpart, with target on `−L` ray.
- **What**: Left-side: F-diff vs (−L)-tangent target → 0.
- **How**: Mirror of right-side proof using `chord_to_tangent_isLittleO_left`, `eventually_ne_left`, and `−L` substitutions in the calc.
- **Hypotheses**: as above with `Iio` versions.
- **Uses from project**: `IsFlatOfOrder`, `chord_to_tangent_isLittleO_left`, `eventually_ne_left`, `tendsto_div_pow_zero_of_isLittleO`, `norm_F_diff_at_tangent_target_le`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 677-740.
- **Notes**: 64 lines.

### `theorem cpv_excised_tendsto_zero_of_F_diff_zero`
- **Type**: Combines the closed-curve excised integral formula with an F-diff-Tendsto hypothesis to conclude the parameter-excised integral tends to `0` as `ε → 0⁺`.
- **What**: Excised CPV `→ 0` for higher-order poles on a closed curve.
- **How**: `tendsto_zero_iff_norm_tendsto_zero`, then `congr'` with `h_F_diff_to_zero` after rewriting via `closed_excised_integral_eq_antideriv_diff` on the eventual filter `self_mem_nhdsWithin`.
- **Hypotheses**: `h_close`, `hk ≥ 2`, smoothness/avoidance/integrability on both wings at every `ε > 0`, and `h_F_diff_to_zero`.
- **Uses from project**: `closed_excised_integral_eq_antideriv_diff`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 755-781.
- **Notes**: 27 lines.

## File Summary

- **Total declarations**: 21 (all public theorems).
- **Key API (headline)**: `integral_pow_inv_eq_FTC`, `closed_excised_integral_eq_antideriv_diff`, `F_diff_at_tangent_target_tendsto_zero_right`, `F_diff_at_tangent_target_tendsto_zero_left`, `cpv_excised_tendsto_zero_of_F_diff_zero`.
- **Unused in file**: `tangentApproximation_of_isFlatOfOrder_right/left`, `F_diff_at_tangent_target_tendsto_zero_right/left`, `cpv_excised_tendsto_zero_of_F_diff_zero` (these are headline theorems consumed downstream).
- **Sorries**: 0.
- **`set_option` lines**: 0.
- **Long proofs (>30 lines)**: `eventually_re_pos_right` (33), `eventually_re_neg_left` (33), `chord_to_tangent_isLittleO_right` (38), `chord_to_tangent_isLittleO_left` (61), `norm_sq_segment_to_pole_lower_bound` (45), `tendsto_div_pow_zero_of_isLittleO` (30), `F_diff_at_tangent_target_tendsto_zero_right` (60), `F_diff_at_tangent_target_tendsto_zero_left` (64).
- **Purpose**: Restores the F-diff asymptotic subset of the deleted `HigherOrderCancel.lean` from git ref `79bcaa5^`. The chain establishes that, for a curve `γ` flat of order `n` at `t₀` with `γ t₀ = s`, the antiderivative `F(z) = −((k−1)⁻¹)·(z−s)^{-(k−1)}` of `γ'/(γ−s)^k` (for `k ≥ 2`, `k ≤ n`) satisfies `F(γt) − F(tangent target) → 0` from each side. Combined with FTC on each smooth piece, this gives the parameter-excised CPV `→ 0` result needed by the sector cancellation argument of T-SC-01 in the Hungerbühler-Wasem developement. The file is organized as: tangent approximation under flatness → antiderivative for `γ'/(γ−s)^k` → FTC → segment bound → eventual sign / non-zero conditions → asymptotic chord bound → segment-distance lower bound → F-diff → 0 limit → excised CPV → 0.
