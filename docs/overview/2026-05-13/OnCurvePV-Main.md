# Inventory: `LeanModularForms/ForMathlib/ValenceFormula/OnCurvePV/Main.lean`

### `private theorem cpv_exists_at_I_H_lt_one`
- **Type**: `(H : ℝ) (hH : √3/2 < H) (h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹) (fdBoundary_H H) (3/2) (5/2) I) (h_arc_I_iff : ∀ {t : ℝ}, 1 < t → t < 3 → (fdBoundary_H H t = I ↔ t = 2)) (h_seg5_ne_I : ∀ {t : ℝ}, 4 < t → t ≤ 5 → fdBoundary_H H t ≠ I) (hγ3_ne_I : fdBoundary_H H 3 ≠ I) : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹) (fdBoundary_H H) 0 5 I`
- **What**: For `H < 1` (and `H > √3/2`), CPV at `s = I` extends from the small arc subinterval to the full `[0, 5]` by avoidance on the remaining segments.
- **How**: Applies `cpv_extend_to_full_interval` and verifies `γ(t) ≠ I` outside `(3/2, 5/2)`: on seg1 via real-part contradiction (`fdBoundary_H_seg1_re' = 1/2 ≠ 0`); on arc via `h_arc_I_iff` forcing `t = 2 ∉ ht`; on seg3 corner via `hγ3_ne_I`; on seg4 via `fdBoundary_H_seg4_re' = -1/2`; on seg5 via `h_seg5_ne_I`.
- **Hypotheses**: `√3/2 < H`, CPV on `(3/2, 5/2)`, uniqueness/avoidance facts on segments.
- **Uses from project**: `CauchyPrincipalValueExists'`, `fdBoundary_H`, `cpv_extend_to_full_interval`, `fdBoundary_H_seg1_re'`, `fdBoundary_H_seg4_re'`.
- **Used by**: `fdBoundary_H_cpv_exists_of_onCurve`.
- **Visibility**: private
- **Lines**: 23-53
- **Notes**: 31 lines.

### `private theorem cpv_exists_at_I_H_eq_one`
- **Type**: `(hH : √3/2 < (1 : ℝ)) (h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹) (fdBoundary_H 1) (3/2) (5/2) I) (h_arc_I_iff : ∀ {t : ℝ}, 1 < t → t < 3 → (fdBoundary_H 1 t = I ↔ t = 2)) (hγ3_ne_I : fdBoundary_H 1 3 ≠ I) : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹) (fdBoundary_H 1) 0 5 I`
- **What**: Special case `H = 1`: now `γ(9/2) = I` as well (seg5 crosses `I`), so the CPV must be assembled via two crossings — at `t = 2` on the arc and at `t = 9/2` on seg5.
- **How**: Build `h_seg5_cpv` at `9/2` via `cpv_exists_on_smooth_subinterval` (seg5 is `s - 9/2 + i`, smooth, derivative `1`, avoidance via real-part injectivity); split `[0, 5]` as `[0, 5/2] ∪ [5/2, 19/4] ∪ [19/4, 5]` and concatenate via `cpv_concat` and `cpv_avoidance` (away from both crossings).
- **Hypotheses**: `H = 1`, CPV on arc, uniqueness on arc, `γ(3) ≠ I`.
- **Uses from project**: `CauchyPrincipalValueExists'`, `fdBoundary_H_eq_seg5_H`, `fdBoundary_seg5_H`, `cpv_exists_on_smooth_subinterval`, `fdBoundary_H_hasDerivAt_seg5`, `fdBoundary_H_deriv_continuousOn_Ioo_45`, `fdBoundary_H_seg5_re'`, `cpv_concat`, `cpv_avoidance`, `fdBoundary_H_continuous`, `fdBoundary_H_seg1_re'`, `fdBoundary_H_seg4_re'`, `fdBoundary_H_cutout_ii`.
- **Used by**: `fdBoundary_H_cpv_exists_of_onCurve`.
- **Visibility**: private
- **Lines**: 57-162
- **Notes**: 106 lines, large case-splitting argument; key lemma `cpv_concat` + `cpv_exists_on_smooth_subinterval`.

### `private theorem cpv_exists_generic_seg1`
- **Type**: `(H : ℝ) (hH : √3/2 < H) (s : ℂ) (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ) (ht₀_mem : 0 ≤ t₀ ∧ t₀ ≤ 5) (hγt₀ : fdBoundary_H H t₀ = s) (ht₀_ne_0 : t₀ ≠ 0) (ht₀_lt_1 : t₀ < 1) : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s`
- **What**: For a generic point `s = γ(t₀)` with `0 < t₀ < 1` (on the right vertical edge, seg1), CPV exists on `[0, 5]`.
- **How**: Apply `cpv_extend_to_full_interval` with sub-interval `(t₀/2, (t₀+1)/2)`; on this strict sub-interval `γ` is smooth (`(1/2 + (H - t·(H-√3/2)) i)`), derivative non-zero, locally injective in imaginary part. Then verify `γ(t) ≠ s` outside: outside seg1 use real-part `≠ 1/2`, on arc use `normSq ≠ 1`, at corner `t=3` use `hs_rho`, etc.
- **Hypotheses**: `s ≠ ρ`, `0 < t₀ < 1`.
- **Uses from project**: `CauchyPrincipalValueExists'`, `fdBoundary_H`, `ellipticPointRho`, `cpv_extend_to_full_interval`, `cpv_exists_on_smooth_subinterval`, `fdBoundary_H_eq_seg1_H`, `fdBoundary_seg1_H`, `fdBoundary_H_hasDerivAt_seg1`, `fdBoundary_H_deriv_continuousOn_Ioo_01`, `fdBoundary_H_seg1_re'`, `fdBoundary_H_eq_arc`, `fdBoundary_H_at_three`, `fdBoundary_at_three`, `fdBoundary_H_seg4_re'`, `fdBoundary_H_seg5_im'`.
- **Used by**: `fdBoundary_H_cpv_exists_of_onCurve`.
- **Visibility**: private
- **Lines**: 166-265
- **Notes**: 100 lines, heavy case-split structure.

### `private theorem cpv_exists_generic_arc_seg5_cross`
- **Type**: `(H : ℝ) (hH : √3/2 < H) (s : ℂ) (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ) (hγt₀ : fdBoundary_H H t₀ = s) (ht₀_gt_1 : 1 < t₀) (ht₀_lt_3 : t₀ < 3) (h_re_s_lt : s.re < 1/2) (h_re_s_gt : -(1:ℝ)/2 < s.re) (h_arc_cpv : CauchyPrincipalValueExists' …) (h_seg5_cross : s.im = H) : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s`
- **What**: For `s = γ(t₀)` on the arc with `s.im = H` (i.e., the point also lies on the seg5 top edge, double crossing), CPV exists on `[0,5]`.
- **How**: Define `t₁ = s.re + 9/2` (so `γ(t₁) = s` via seg5 parametrization). Build `h_seg5_cpv` near `t₁` via `cpv_exists_on_smooth_subinterval`. Split `[0,5]` into `[0, (t₀+3)/2] ∪ [(t₀+3)/2, (t₁+5)/2] ∪ [(t₁+5)/2, 5]` and concatenate using `cpv_concat`, `cpv_avoidance` with `arc_angle_injective` and segment real/imaginary part analysis to rule out `γ(t) = s` elsewhere.
- **Hypotheses**: `s` on arc, also on seg5 (so `s.im = H`).
- **Uses from project**: `CauchyPrincipalValueExists'`, `fdBoundary_H`, `ellipticPointRho`, `fdBoundary_H_eq_seg5_H`, `fdBoundary_seg5_H`, `cpv_exists_on_smooth_subinterval`, `fdBoundary_H_hasDerivAt_seg5`, `fdBoundary_H_deriv_continuousOn_Ioo_45`, `fdBoundary_H_seg5_re'`, `cpv_concat`, `cpv_avoidance`, `fdBoundary_H_continuous`, `fdBoundary_H_seg1_re'`, `arc_angle_injective`, `fdBoundary_H_eq_arc`, `fdBoundary_H_at_three`, `fdBoundary_at_three`, `fdBoundary_H_seg4_re'`, `fdBoundary_H_cutout_ii`.
- **Used by**: `cpv_exists_generic_arc`.
- **Visibility**: private
- **Lines**: 269-399
- **Notes**: 131 lines, multi-interval concatenation.

### `private theorem cpv_exists_generic_arc_no_cross`
- **Type**: `(H : ℝ) (hH : √3/2 < H) (s : ℂ) (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ) (hγt₀ : fdBoundary_H H t₀ = s) (ht₀_gt_1 : 1 < t₀) (ht₀_lt_3 : t₀ < 3) (h_re_s_lt : s.re < 1/2) (h_re_s_gt : -(1:ℝ)/2 < s.re) (h_arc_cpv : CauchyPrincipalValueExists' …) (h_seg5_cross : ¬(s.im = H)) : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s`
- **What**: For `s = γ(t₀)` on the arc with `s.im ≠ H` (no seg5 crossing), CPV extends.
- **How**: Apply `cpv_extend_to_full_interval` to `((t₀+1)/2, (t₀+3)/2)`, avoidance everywhere else: outside arc use real-part or `arc_angle_injective` to rule out `γ(t) = s`; on seg5 use `h_seg5_cross : s.im ≠ H`.
- **Hypotheses**: `s` on arc strict-interior, `s.im ≠ H`.
- **Uses from project**: `CauchyPrincipalValueExists'`, `fdBoundary_H`, `ellipticPointRho`, `cpv_extend_to_full_interval`, `arc_angle_injective`, `fdBoundary_H_eq_arc`, `fdBoundary_H_at_three`, `fdBoundary_at_three`, `fdBoundary_H_seg4_re'`, `fdBoundary_H_seg1_re'`, `fdBoundary_H_seg5_im'`.
- **Used by**: `cpv_exists_generic_arc`.
- **Visibility**: private
- **Lines**: 403-448
- **Notes**: 46 lines.

### `private theorem cpv_exists_generic_arc`
- **Type**: `(H : ℝ) (hH : √3/2 < H) (s : ℂ) (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ) (hγt₀ : fdBoundary_H H t₀ = s) (ht₀_gt_1 : 1 < t₀) (ht₀_lt_3 : t₀ < 3) : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s`
- **What**: Dispatch for `s` on arc strict-interior (`1 < t₀ < 3`): split into seg5-crossing and non-crossing cases.
- **How**: Establishes Re/Im in terms of `cos`/`sin` (via `fdBoundary_H_arc_re'`/`fdBoundary_H_arc_im'`), shows `normSq s = 1` and strict bounds `-1/2 < Re < 1/2` using `Real.strictAntiOn_cos`. Builds local `h_arc_cpv` via `cpv_exists_on_smooth_subinterval` on `((t₀+1)/2, (t₀+3)/2)`. Then `by_cases s.im = H` and dispatches.
- **Hypotheses**: `s ≠ ρ`, `1 < t₀ < 3`.
- **Uses from project**: `CauchyPrincipalValueExists'`, `fdBoundary_H`, `ellipticPointRho`, `fdBoundary_H_arc_re'`, `fdBoundary_H_arc_im'`, `fdBoundary_H_eq_arc`, `cpv_exists_on_smooth_subinterval`, `fdBoundary_H_hasDerivAt_arc`, `fdBoundary_H_deriv_continuousOn_Ioo_13`, `arc_angle_injective`, `cpv_exists_generic_arc_seg5_cross`, `cpv_exists_generic_arc_no_cross`.
- **Used by**: `fdBoundary_H_cpv_exists_of_onCurve`.
- **Visibility**: private
- **Lines**: 452-517
- **Notes**: 66 lines.

### `private theorem cpv_exists_generic_seg4`
- **Type**: `(H : ℝ) (hH : √3/2 < H) (s : ℂ) (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ) (hγt₀ : fdBoundary_H H t₀ = s) (ht₀_gt_3 : 3 < t₀) (ht₀_lt_4 : t₀ < 4) : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s`
- **What**: For `s = γ(t₀)` with `3 < t₀ < 4` (left vertical seg3 in code: but `seg4` in file's segment naming), CPV exists.
- **How**: Apply `cpv_extend_to_full_interval` with sub-interval `((t₀+3)/2, (t₀+4)/2)`; show smoothness on seg via `fdBoundary_H_eq_seg4_H` and derivative non-zero. Avoidance elsewhere: `Re s = -1/2`, `normSq s > 1`; rule out other parameters via comparison of Im components and `mul_right_cancel₀`.
- **Hypotheses**: `s ≠ ρ`, `3 < t₀ < 4`.
- **Uses from project**: `CauchyPrincipalValueExists'`, `fdBoundary_H`, `ellipticPointRho`, `cpv_extend_to_full_interval`, `cpv_exists_on_smooth_subinterval`, `fdBoundary_H_eq_seg4_H`, `fdBoundary_seg4_H`, `fdBoundary_H_hasDerivAt_seg4`, `fdBoundary_H_deriv_continuousOn_Ioo_34`, `fdBoundary_H_seg4_re'`, `fdBoundary_H_seg1_re'`, `fdBoundary_H_eq_arc`, `fdBoundary_H_at_three`, `fdBoundary_at_three`, `fdBoundary_H_at_four`, `fdBoundary_H_seg5_re'`.
- **Used by**: `fdBoundary_H_cpv_exists_of_onCurve`.
- **Visibility**: private
- **Lines**: 521-647
- **Notes**: 127 lines, many nested cases.

### `private theorem cpv_exists_generic_seg5_normSq_one`
- **Type**: `(H : ℝ) (hH : √3/2 < H) (s : ℂ) (hs_rho : ¬s = ρ) (hs_endpoint : ¬s = 1/2 + H·I) (t₀ : ℝ) (ht₀_gt_4 : 4 < t₀) (ht₀_lt_5 : t₀ < 5) (h_im_s : s.im = H) (h_re_s : s.re = t₀ - 9/2) (h_seg5_cpv : CauchyPrincipalValueExists' …) (h_normSq : normSq s = 1) : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s`
- **What**: For `s = γ(t₀)` on seg5 (top edge, `4 < t₀ < 5`) with `‖s‖ = 1`, so `s` is also on the arc: double crossing.
- **How**: Find `t₁ ∈ (1, 3)` with `cos(π(1+t₁)/6) = s.re` via `intermediate_value_Icc'`, so `γ(t₁) = s` on arc. Build arc-side CPV via `cpv_exists_on_smooth_subinterval` at `t₁`, then concatenate intervals `[0, (t₁+3)/2] ∪ [(t₁+3)/2, (t₀+5)/2] ∪ [(t₀+5)/2, 5]` via `cpv_concat` and avoidance.
- **Hypotheses**: `s` on seg5, `‖s‖ = 1`, `s ≠ ρ`, `s` not the endpoint.
- **Uses from project**: `CauchyPrincipalValueExists'`, `fdBoundary_H`, `ellipticPointRho`, `fdBoundary_H_eq_arc`, `arc_angle_injective`, `cpv_exists_on_smooth_subinterval`, `fdBoundary_H_hasDerivAt_arc`, `fdBoundary_H_deriv_continuousOn_Ioo_13`, `cpv_concat`, `cpv_avoidance`, `fdBoundary_H_continuous`, `fdBoundary_H_at_zero`, `fdBoundary_H_eq_seg1_H`, `fdBoundary_seg1_H`, `fdBoundary_H_at_three`, `fdBoundary_at_three`, `fdBoundary_H_seg4_re'`, `fdBoundary_H_seg5_re'`, `fdBoundary_H_cutout_ii`.
- **Used by**: `cpv_exists_generic_seg5`.
- **Visibility**: private
- **Lines**: 651-818
- **Notes**: 168 lines, longest theorem in file; key lemma `intermediate_value_Icc'`, plus repeated `arc_angle_injective` and `cpv_concat` chaining.

### `private theorem cpv_exists_generic_seg5_normSq_ne_one`
- **Type**: `(H : ℝ) (hH : √3/2 < H) (s : ℂ) (hs_rho : ¬s = ρ) (t₀ : ℝ) (ht₀_gt_4 : 4 < t₀) (ht₀_lt_5 : t₀ < 5) (h_re_s : s.re = t₀ - 9/2) (h_seg5_cpv : CauchyPrincipalValueExists' …) (h_normSq : ¬normSq s = 1) (hs_endpoint : ¬s = 1/2 + H·I) (h_im_s : s.im = H) : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s`
- **What**: For `s` on seg5 with `‖s‖ ≠ 1` (so off arc), CPV extends via avoidance.
- **How**: `cpv_extend_to_full_interval` with sub-interval `((t₀+4)/2, (t₀+5)/2)`. Outside this interval: on `t = 0` use `hs_endpoint`; on seg1 use Im comparison; on arc use `normSq = 1 ≠ h_normSq`; at `t = 3` use `hs_rho`; on seg4 and other seg5 use Re-part comparison.
- **Hypotheses**: `s` on seg5, off arc, off endpoint.
- **Uses from project**: `CauchyPrincipalValueExists'`, `fdBoundary_H`, `ellipticPointRho`, `cpv_extend_to_full_interval`, `fdBoundary_H_at_zero`, `fdBoundary_H_eq_seg1_H`, `fdBoundary_seg1_H`, `fdBoundary_H_eq_arc`, `fdBoundary_H_at_three`, `fdBoundary_H_seg4_re'`, `fdBoundary_H_seg5_re'`.
- **Used by**: `cpv_exists_generic_seg5`.
- **Visibility**: private
- **Lines**: 822-871
- **Notes**: 50 lines.

### `private theorem cpv_exists_generic_seg5`
- **Type**: `(H : ℝ) (hH : √3/2 < H) (s : ℂ) (hs_rho : ¬s = ρ) (t₀ : ℝ) (ht₀_mem : 0 ≤ t₀ ∧ t₀ ≤ 5) (hγt₀ : fdBoundary_H H t₀ = s) (hs_endpoint : ¬s = 1/2 + H·I) (ht₀_ne_5 : t₀ ≠ 5) (ht₀_gt_4 : 4 < t₀) : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s`
- **What**: Dispatch for `t₀` on seg5 strict-interior: split into `‖s‖ = 1` vs `≠ 1`.
- **How**: Computes `s.im = H` and `s.re = t₀ - 9/2`. Builds local seg5 CPV at `t₀` via `cpv_exists_on_smooth_subinterval` on `((t₀+4)/2, (t₀+5)/2)`. Then `by_cases normSq s = 1` and dispatches.
- **Hypotheses**: `s ≠ ρ`, `s ≠ endpoint`, `4 < t₀ < 5`.
- **Uses from project**: `CauchyPrincipalValueExists'`, `fdBoundary_H`, `ellipticPointRho`, `fdBoundary_H_seg5_im'`, `fdBoundary_H_seg5_re'`, `cpv_exists_on_smooth_subinterval`, `fdBoundary_H_eq_seg5_H`, `fdBoundary_seg5_H`, `fdBoundary_H_hasDerivAt_seg5`, `fdBoundary_H_deriv_continuousOn_Ioo_45`, `cpv_exists_generic_seg5_normSq_one`, `cpv_exists_generic_seg5_normSq_ne_one`.
- **Used by**: `fdBoundary_H_cpv_exists_of_onCurve`.
- **Visibility**: private
- **Lines**: 875-920
- **Notes**: 46 lines.

### `theorem fdBoundary_H_cpv_exists_of_onCurve`
- **Type**: `(H : ℝ) (hH : √3/2 < H) (s : ℂ) (h_on : ∃ t ∈ Set.Icc (0:ℝ) 5, fdBoundary_H H t = s) : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s`
- **What**: Main theorem: for any point `s` lying on the boundary contour `fdBoundary_H H` (`H > √3/2`), the Cauchy principal value integral of `(z - s)⁻¹` along the contour exists.
- **How**: Big case split on the type of `s` (elliptic fixed points + corners + interior cases). (i) `s = ρ`: use existing `cpv_exists_at_rho`. (ii) `s = ρ+1`: use `cpv_exists_at_rho_plus_one`. (iii) `s = I`: dispatch into `H > 1` (existing `cpv_exists_at_i`) vs `H ≤ 1` (set up `h_arc_cpv` near `t = 2` via `cpv_exists_on_smooth_subinterval` and arc-injectivity, then dispatch into `cpv_exists_at_I_H_lt_one` or `cpv_exists_at_I_H_eq_one`). (iv) Generic: parametrize `t₀`, exclude corner cases (`t₀ ∉ {0, 1, 3, 4, 5}` ruled out by `hs_endpoint`, `hs_rho'`, `hs_rho`, `hs_corner`, `hs_endpoint`), then dispatch into the appropriate `cpv_exists_generic_*` helper based on segment of `t₀`. Corners handled by `cpv_at_endpoint` and `cpv_at_corner`.
- **Hypotheses**: `√3/2 < H`, `s` on contour.
- **Uses from project**: `CauchyPrincipalValueExists'`, `fdBoundary_H`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, `cpv_exists_at_rho`, `cpv_exists_at_rho_plus_one`, `cpv_exists_at_i`, `fdBoundary_H_eq_arc`, `cpv_exists_on_smooth_subinterval`, `fdBoundary_H_hasDerivAt_arc`, `fdBoundary_H_deriv_continuousOn_Ioo_13`, `arc_angle_injective`, `fdBoundary_H_at_three`, `fdBoundary_H_at_four`, `cpv_exists_at_I_H_lt_one`, `cpv_exists_at_I_H_eq_one`, `fdBoundary_H_seg5_im'`, `cpv_at_endpoint`, `cpv_at_corner`, `fdBoundary_H_at_zero`, `fdBoundary_H_at_one`, `fdBoundary_H_at_five`, `cpv_exists_generic_seg1`, `cpv_exists_generic_arc`, `cpv_exists_generic_seg4`, `cpv_exists_generic_seg5`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 925-1060
- **Notes**: 136 lines, top-level dispatcher.

## File Summary

- **Total declarations**: 11 (10 private helper theorems, 1 public theorem).
- **Key API**: `fdBoundary_H_cpv_exists_of_onCurve` — for any point `s` lying on the rectangular fundamental-domain boundary (height `H > √3/2`), the Cauchy principal value of `∫ (γ(t) - s)⁻¹ γ'(t) dt` over `[0, 5]` exists.
- **Unused in file**: `fdBoundary_H_cpv_exists_of_onCurve` is the consumer-facing API (used elsewhere, e.g., in `OnCurvePVProvider` constructions).
- **Sorries**: none.
- **set_options**: none (only `attribute [local instance] Classical.propDecidable`).
- **Long proofs (>30 lines)**: every theorem in this file is >30 lines. `cpv_exists_generic_seg5_normSq_one` is the longest (168 lines), followed by `fdBoundary_H_cpv_exists_of_onCurve` (136), `cpv_exists_generic_arc_seg5_cross` (131), `cpv_exists_generic_seg4` (127), `cpv_exists_at_I_H_eq_one` (106), `cpv_exists_generic_seg1` (100), `cpv_exists_generic_arc` (66), `cpv_exists_generic_seg5_normSq_ne_one` (50), `cpv_exists_generic_seg5` (46), `cpv_exists_generic_arc_no_cross` (46), `cpv_exists_at_I_H_lt_one` (31).
- **Purpose**: This file proves the on-curve CPV existence theorem — a core ingredient for the residue side of the valence formula. For every point `s` actually lying on the rectangular boundary contour `fdBoundary_H H` (height `H > √3/2` around the standard fundamental domain of `SL₂(ℤ)`), it shows the Cauchy principal value `lim_{ε → 0} ∫_{|γ - s| > ε} (γ - s)⁻¹ γ'` converges. The proof is a 10-way case analysis on which segment `s` belongs to: (a) the three elliptic fixed points `ρ, ρ+1, i` are handled by dedicated infrastructure from sibling files (`OnCurvePV.Rho`, `OnCurvePV.RhoPlusOne`, `OnCurvePV.I`), with the `s = I, H ≤ 1` subcase requiring a separate two-crossing argument (`H = 1` makes `γ(9/2) = i` too); (b) the two corner points `1/2 + Hi` and `-1/2 + Hi` are handled via `cpv_at_endpoint`/`cpv_at_corner`; (c) interior points of each of the four smooth segments (seg1, arc, seg3/seg4 in code, seg5) are handled by dedicated generic theorems that extract a smooth subinterval on which `cpv_exists_on_smooth_subinterval` applies, then extend via `cpv_concat`/`cpv_avoidance` to the full `[0, 5]`. The arc case further splits depending on whether `s.im = H` (double crossing with seg5) or not; the seg5 case splits on `‖s‖ = 1` (double crossing with arc) or not. The intermediate value theorem produces the arc-side crossing parameter `t₁` in the double-crossing branches.
