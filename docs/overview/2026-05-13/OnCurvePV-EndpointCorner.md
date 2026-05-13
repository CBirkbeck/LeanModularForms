# Inventory: ValenceFormula/OnCurvePV/EndpointCorner.lean

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ValenceFormula/OnCurvePV/EndpointCorner.lean`

### `private lemma mul_inv_rev_cancel`
- **Type**: `(a b : ℂ) (_ : a ≠ 0) (hb : b ≠ 0) : (a * b)⁻¹ * b = a⁻¹`
- **What**: Algebraic identity `(a·b)⁻¹ · b = a⁻¹` when `b ≠ 0`.
- **How**: Apply `mul_inv_rev`, reassociate via `mul_assoc`/`mul_comm`, cancel `b` using `inv_mul_cancel₀ hb`.
- **Hypotheses**: `b ≠ 0`.
- **Uses from project**: none.
- **Used by**: `endpoint_integrand_seg1`, `cpv_at_corner` (in the seg4 integrand step).
- **Visibility**: private
- **Lines**: 23--25
- **Notes**: none.

### `private lemma integral_inv_eq_log_sub`
- **Type**: `(a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) : ∫ t in a..1, (↑t : ℂ)⁻¹ = Complex.log ↑(1:ℝ) - Complex.log ↑a`
- **What**: Real-axis log integral: `∫_a^1 t⁻¹ dt = log 1 - log a` (as complex), for `0 < a ≤ 1`.
- **How**: Pull out `ofReal`, apply `intervalIntegral.integral_eq_sub_of_hasDerivAt` with `Real.hasDerivAt_log` (nonzero `t > 0` on `uIcc a 1`), then `Real.log_one` and `Complex.ofReal_log`.
- **Hypotheses**: `0 < a ≤ 1`.
- **Uses from project**: none.
- **Used by**: `cpv_at_endpoint`, `cpv_at_corner`.
- **Visibility**: private
- **Lines**: 28--47
- **Notes**: none.

### `private lemma integral_shifted_inv_eq_log`
- **Type**: `(η : ℝ) (hη : 0 < η) (hη1 : η < 1) : ∫ t in (4:ℝ)..(5 - η), (↑(t - 5) : ℂ)⁻¹ = ↑(Real.log η)`
- **What**: Shifted log integral: `∫_4^{5-η} (t-5)⁻¹ dt = log η` (real-valued cast), for `0 < η < 1`.
- **How**: Apply FTC via `Real.hasDerivAt_log .comp (hasDerivAt_id .sub_const 5)`. Compute boundary: `log(-η) = log η` and `log(-1) = log 1 = 0` via `Real.log_neg_eq_log`.
- **Hypotheses**: `0 < η < 1`.
- **Uses from project**: none.
- **Used by**: `cpv_at_endpoint`.
- **Visibility**: private
- **Lines**: 50--73
- **Notes**: none.

### `private lemma endpoint_avoid_14`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) : let s := (1/2 : ℂ) + ↑H * I; ∀ t ∈ Set.Icc (1:ℝ) 4, fdBoundary_H H t ≠ s`
- **What**: The endpoint `s = 1/2 + H·i` is not hit by segments 1--4 of `fdBoundary_H H` (the arc and the top-left horizontal).
- **How**: Case-split `t ≤ 3` or `t > 3`. If `t ≤ 3`: subcases `t = 1` (contradicts via imaginary part `Im(ρ+1) ≠ H`), `t = 3` (similar via `Im(ρ) ≠ H`), else on arc `t ∈ (1,3)`: `‖γ(t)‖ = 1` but `‖s‖ > 1` from `normSq s > 1` (using `H > √3/2` and `nlinarith`). If `t > 3`: use `fdBoundary_H_seg4_re'` which gives `Re(γ(t)) = -1/2 ≠ 1/2`.
- **Hypotheses**: `H > √3/2`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_at_one`, `fdBoundary_H_at_three`, `fdBoundary_H_eq_arc`, `fdBoundary_H_seg4_re'`, `fdBoundary_at_three`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`, `ellipticPointRho`, `ellipticPointRho'`.
- **Used by**: `endpoint_min_dist`.
- **Visibility**: private
- **Lines**: 76--126
- **Notes**: >30 lines.

### `private lemma endpoint_min_dist`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) : let s := (1/2 : ℂ) + ↑H * I; ∃ δ > 0, ∀ t ∈ Set.Icc (1:ℝ) 4, δ ≤ ‖fdBoundary_H H t - s‖`
- **What**: Positive uniform distance from the endpoint `s = 1/2 + H·i` to the curve `fdBoundary_H H` on `[1,4]`.
- **How**: `IsCompact.exists_forall_le'` on `Icc 1 4` with continuous norm of `γ - s`; positivity from `endpoint_avoid_14`.
- **Hypotheses**: `H > √3/2`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_continuous`, `endpoint_avoid_14`.
- **Used by**: `cpv_at_endpoint`.
- **Visibility**: private
- **Lines**: 129--139
- **Notes**: none.

### `private lemma endpoint_diff_seg1`
- **Type**: `(H : ℝ) (s : ℂ) (hs_def : s = (1/2 : ℂ) + ↑H * I) (c : ℝ) (hc_def : c = H - Real.sqrt 3 / 2) (t : ℝ) (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) : fdBoundary_H H t - s = ↑((-t) * c) * I`
- **What**: On seg1 (`t ∈ [0,1]`), `γ(t) - s = -t·c · i` (purely imaginary, going downward).
- **How**: Rewrite via `fdBoundary_H_eq_seg1_H`, unfold `fdBoundary_seg1_H`, `push_cast`, `ring`.
- **Hypotheses**: `0 ≤ t ≤ 1`.
- **Uses from project**: `fdBoundary_H_eq_seg1_H`, `fdBoundary_seg1_H`.
- **Used by**: `endpoint_norm_seg1`, `endpoint_integrand_seg1`.
- **Visibility**: private
- **Lines**: 142--148
- **Notes**: none.

### `private lemma endpoint_diff_seg5`
- **Type**: `(H : ℝ) (s : ℂ) (hs_def : s = (1/2 : ℂ) + ↑H * I) (t : ℝ) (ht4 : 4 < t) : fdBoundary_H H t - s = ↑(t - 5)`
- **What**: On seg5 (`t > 4`), `γ(t) - s = t - 5` (purely real, negative for `t < 5`).
- **How**: Rewrite via `fdBoundary_H_eq_seg5_H`, unfold `fdBoundary_seg5_H`, `push_cast`, `ring`.
- **Hypotheses**: `t > 4`.
- **Uses from project**: `fdBoundary_H_eq_seg5_H`, `fdBoundary_seg5_H`.
- **Used by**: `endpoint_norm_seg5`, `endpoint_integrand_seg5`.
- **Visibility**: private
- **Lines**: 151--157
- **Notes**: none.

### `private lemma endpoint_norm_seg1`
- **Type**: `(H : ℝ) (s : ℂ) (hs_def : s = (1/2 : ℂ) + ↑H * I) (c : ℝ) (hc_def : c = H - Real.sqrt 3 / 2) (hc : 0 < c) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ‖fdBoundary_H H t - s‖ = t * c`
- **What**: Norm on seg1: `‖γ(t) - s‖ = t · c`.
- **How**: Use `endpoint_diff_seg1`, then `norm_mul`, `Complex.norm_real`, `Complex.norm_I = 1`, and `abs_of_nonpos` for `(-t)·c`.
- **Hypotheses**: `0 ≤ t ≤ 1`, `0 < c`.
- **Uses from project**: `endpoint_diff_seg1`.
- **Used by**: `cpv_at_endpoint`.
- **Visibility**: private
- **Lines**: 160--166
- **Notes**: none.

### `private lemma endpoint_norm_seg5`
- **Type**: `(H : ℝ) (s : ℂ) (hs_def : s = (1/2 : ℂ) + ↑H * I) (t : ℝ) (ht4 : 4 < t) (ht5 : t ≤ 5) : ‖fdBoundary_H H t - s‖ = 5 - t`
- **What**: Norm on seg5: `‖γ(t) - s‖ = 5 - t`.
- **How**: Use `endpoint_diff_seg5`, then `Complex.norm_real`, `abs_of_nonpos`.
- **Hypotheses**: `4 < t ≤ 5`.
- **Uses from project**: `endpoint_diff_seg5`.
- **Used by**: `cpv_at_endpoint`.
- **Visibility**: private
- **Lines**: 169--174
- **Notes**: none.

### `private lemma endpoint_integrand_seg1`
- **Type**: `(H : ℝ) (s : ℂ) (hs_def : s = (1/2 : ℂ) + ↑H * I) (c : ℝ) (hc_def : c = H - Real.sqrt 3 / 2) (hc : 0 < c) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t = (↑t : ℂ)⁻¹`
- **What**: Integrand on seg1 simplifies to `1/t`: `(γ(t)-s)⁻¹ · γ'(t) = 1/t`.
- **How**: Use `endpoint_diff_seg1` and `fdBoundary_H_hasDerivAt_seg1`. Factor the imaginary `c·i` and apply `mul_inv_rev_cancel`.
- **Hypotheses**: `0 < t < 1`, `0 < c`.
- **Uses from project**: `endpoint_diff_seg1`, `fdBoundary_H_hasDerivAt_seg1`, `mul_inv_rev_cancel`.
- **Used by**: `cpv_at_endpoint`.
- **Visibility**: private
- **Lines**: 177--192
- **Notes**: `erw`.

### `private lemma endpoint_integrand_seg5`
- **Type**: `(H : ℝ) (s : ℂ) (hs_def : s = (1/2 : ℂ) + ↑H * I) (t : ℝ) (ht4 : 4 < t) : (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t = (↑(t - 5) : ℂ)⁻¹`
- **What**: Integrand on seg5 simplifies to `1/(t-5)`.
- **How**: Use `endpoint_diff_seg5` and `fdBoundary_H_hasDerivAt_seg5`, then `mul_one`.
- **Hypotheses**: `t > 4`.
- **Uses from project**: `endpoint_diff_seg5`, `fdBoundary_H_hasDerivAt_seg5`.
- **Used by**: `cpv_at_endpoint`.
- **Visibility**: private
- **Lines**: 195--200
- **Notes**: `erw`.

### `lemma cpv_at_endpoint`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) : CauchyPrincipalValueExists' (fun z => (z - ((1/2 : ℂ) + ↑H * I))⁻¹) (fdBoundary_H H) 0 5 ((1/2 : ℂ) + ↑H * I)`
- **What**: The Cauchy principal value of `1/(z - s)` along `fdBoundary_H H` on `[0,5]` exists at the endpoint `s = 1/2 + H·i` (where seg1 meets seg5).
- **How**: "Eventually constant" approach. Define `F(η) = ∫_0^5 1_{η<‖γ-s‖} · (γ-s)⁻¹ γ'`. Show `F(η) = log c + C` for `η < ε₀ := min(c, 1, δ)`, where `C := ∫_1^4 (γ-s)⁻¹ γ'` and `c = H - √3/2`. Split `F(η)` into segments `[0,1]`, `[1,4]`, `[4,5]`. On `[1,4]` use `endpoint_min_dist`. On `[0,1]`: cutoff active iff `t > η/c`; integrand becomes `1/t`; integral is `log 1 - log(η/c)`. On `[4,5]`: cutoff active iff `t < 5-η`; integrand becomes `1/(t-5)`; integral is `log η`. Sum yields `log c + C`. ~200 lines.
- **Hypotheses**: `H > √3/2`.
- **Uses from project**: `CauchyPrincipalValueExists'`, `fdBoundary_H`, `fdBoundary_H_at_five`, `fdBoundary_H_cutout_ii`, `endpoint_min_dist`, `endpoint_norm_seg1`, `endpoint_norm_seg5`, `endpoint_integrand_seg1`, `endpoint_integrand_seg5`, `integral_inv_eq_log_sub`, `integral_shifted_inv_eq_log`.
- **Used by**: unused in file (terminal API).
- **Visibility**: public
- **Lines**: 202--400
- **Notes**: >30 lines.

### `private lemma corner_cpv_03`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) : CauchyPrincipalValueExists' (fun z => (z - (-(1/2 : ℂ) + ↑H * I))⁻¹) (fdBoundary_H H) 0 3 (-(1/2 : ℂ) + ↑H * I)`
- **What**: CPV at corner `s = -1/2 + H·i` exists on `[0,3]` because the corner avoids the curve there (so the integrand is continuous; no actual cutoff is needed).
- **How**: Use `cpv_avoidance` with `(fdBoundary_H_continuous H).continuousOn` and an avoidance proof: case-split `t ≤ 1` (use `fdBoundary_H_seg1_re' = -1/2 ≠ -1/2`... wait, on seg1 Re=H is not -1/2; actually uses `fdBoundary_H_seg1_re'` to get a re-value, contradiction via linarith), `t ∈ (1,3)` (arc has `‖γ‖ = 1` but `‖s‖ > 1`), `t = 3` (use `Im(ρ) = √3/2 ≠ H`).
- **Hypotheses**: `H > √3/2`.
- **Uses from project**: `CauchyPrincipalValueExists'`, `cpv_avoidance`, `fdBoundary_H`, `fdBoundary_H_continuous`, `fdBoundary_H_seg1_re'`, `fdBoundary_H_eq_arc`, `fdBoundary_H_at_three`, `fdBoundary_at_three`, `ellipticPointRho`, `ellipticPointRho'`.
- **Used by**: `cpv_at_corner`.
- **Visibility**: private
- **Lines**: 403--450
- **Notes**: >30 lines.

### `lemma cpv_at_corner`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) : CauchyPrincipalValueExists' (fun z => (z - (-(1/2 : ℂ) + ↑H * I))⁻¹) (fdBoundary_H H) 0 5 (-(1/2 : ℂ) + ↑H * I)`
- **What**: CPV existence at corner `s = -1/2 + H·i` over `[0,5]` (corner = top-left corner where seg4 meets seg5).
- **How**: Split `[0,5] = [0,3] ∪ [3,5]`. On `[0,3]` use `corner_cpv_03` (avoidance — corner not on curve there). On `[3,5]` use "eventually constant" pattern analogous to `cpv_at_endpoint`: on seg4 (`t ∈ (3,4)`) `(γ-s) = (t-4)·c·i`, so cutoff active iff `t < 4 - η/c`; integrand `(t-4)⁻¹`; integral is `log(-1) - log(-(η/c)) = -log(η/c)`. On seg5 (`t > 4`) `(γ-s) = t-4`, cutoff active iff `t > 4+η`; integrand `(t-4)⁻¹`; integral is `log 1 - log η`. Sum equals `-log c`. Concatenate via `cpv_concat`. ~240 lines.
- **Hypotheses**: `H > √3/2`.
- **Uses from project**: `CauchyPrincipalValueExists'`, `cpv_concat`, `corner_cpv_03`, `fdBoundary_H`, `fdBoundary_H_eq_seg4_H`, `fdBoundary_seg4_H`, `fdBoundary_H_eq_seg5_H`, `fdBoundary_seg5_H`, `fdBoundary_H_hasDerivAt_seg4`, `fdBoundary_H_hasDerivAt_seg5`, `fdBoundary_H_at_four`, `fdBoundary_H_cutout_ii`, `mul_inv_rev_cancel`, `integral_inv_eq_log_sub`.
- **Used by**: unused in file (terminal API).
- **Visibility**: public
- **Lines**: 452--691
- **Notes**: `erw`; >30 lines.

---

## File Summary

- **Total declarations**: 14 (10 private lemmas, 2 public lemmas — `cpv_at_endpoint`, `cpv_at_corner` — and 2 private analytic helpers `integral_inv_eq_log_sub`, `integral_shifted_inv_eq_log`).
- **Key API (public)**: `cpv_at_endpoint`, `cpv_at_corner`. Both witness that the Cauchy principal value of `1/(z - s)` along the truncated fundamental-domain boundary `fdBoundary_H H` exists at the on-curve singular points `s = ±1/2 + H·i`.
- **Unused in file**: `cpv_at_endpoint`, `cpv_at_corner` (terminal exports for `OnCurvePVProvider`).
- **Sorries**: none.
- **set_options**: `attribute [local instance] Classical.propDecidable` (no `set_option` directives).
- **Long proofs (>30 lines)**: `endpoint_avoid_14` (~51), `cpv_at_endpoint` (~199), `corner_cpv_03` (~48), `cpv_at_corner` (~240).
- **One-paragraph purpose**: Establishes Cauchy-principal-value existence at the two on-curve singular points of the boundary parameterization `fdBoundary_H H`: the "endpoint" `1/2 + H·i` (junction of segments 1 and 5) and the "corner" `-1/2 + H·i` (junction of segments 4 and 5). The strategy is to show that, for sufficiently small cutoff `η`, the cutoff integral `F(η)` is *constant*. Each side contributes a divergent log (∫ t⁻¹ near 0 on seg1 / ∫ (t-5)⁻¹ near 5 on seg5, etc.) but these divergent logs exactly cancel by odd symmetry of `1/(t-t₀)`, leaving the finite combination `± log c + C` independent of `η`. Once `F(η)` is constant for small `η`, the principal-value limit is just that constant. The two public lemmas feed `fdBoundary_H_OnCurvePVProvider` (Worker A's deliverable) to populate the on-curve CPV requirement of the valence-formula assembly.
