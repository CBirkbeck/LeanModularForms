# Inventory: PVChain/ArcContribution.lean

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ValenceFormula/PVChain/ArcContribution.lean`

### `private lemma deriv_fdBoundary_H_arc`
- **Type**: `(H : ℝ) {t : ℝ} (h1 : 1 < t) (h3 : t < 3) : deriv (fdBoundary_H H) t = ↑(Real.pi / 6) * I * fdBoundary_H H t`
- **What**: The derivative of `fdBoundary_H H` at an arc parameter `t ∈ (1,3)` equals `(π/6) i · fdBoundary_H H t`.
- **How**: Rewrites with `fdBoundary_H_eq_arc`, applies `fdBoundary_H_hasDerivAt_arc`, then ring normalization via `push_cast; ring`.
- **Hypotheses**: `1 < t < 3` (arc subinterval).
- **Uses from project**: `fdBoundary_H_eq_arc`, `fdBoundary_H_hasDerivAt_arc`.
- **Used by**: `cpv_integrand_intervalIntegrable_arc`, `arc_cpv_integral_S_identity`.
- **Visibility**: private
- **Lines**: 38--48
- **Notes**: uses `erw`.

### `private lemma analyticAt_logDeriv_off_zeros`
- **Type**: `(z : ℂ) (hz : 0 < z.im) (hfz : modularFormCompOfComplex f z ≠ 0) : AnalyticAt ℂ (logDeriv (modularFormCompOfComplex f)) z`
- **What**: `logDeriv f` is analytic at any point `z` in the upper half-plane where `f(z) ≠ 0`.
- **How**: From `UpperHalfPlane.mdifferentiable_iff` get differentiability on UHP, derive analyticity, then take `.deriv.fun_div _ hfz`.
- **Hypotheses**: `0 < z.im`; `f(z) ≠ 0`.
- **Uses from project**: `modularFormCompOfComplex`, `UpperHalfPlane.mdifferentiable_iff`, `UpperHalfPlane.isOpen_upperHalfPlaneSet`, modular form holo field `f.holo'`.
- **Used by**: `cpv_integrand_intervalIntegrable_arc`.
- **Visibility**: private
- **Lines**: 52--59
- **Notes**: depends on outer `variable f`.

### `lemma logDeriv_modform_S_transform`
- **Type**: `(z : ℂ) (hz : 0 < z.im) (hz_ne : z ≠ 0) (hgz : modularFormCompOfComplex f z ≠ 0) : logDeriv (modularFormCompOfComplex f) z = logDeriv (modularFormCompOfComplex f) (-(1:ℂ)/z) / z ^ 2 - ↑k / z`
- **What**: Functional equation of `logDeriv f` under the modular S-transform `z ↦ -1/z`: the log-derivative at `z` equals the log-derivative at `-1/z` divided by `z²`, minus `k/z`.
- **How**: Set `g := modularFormCompOfComplex f`. Build the local equality `g(-1/w) =ᶠ w^k · g(w)` from `modform_comp_ofComplex_S_identity`. Compute `deriv(w ↦ -1/w)(z) = 1/z²` via `hasDerivAt_inv`. Apply `logDeriv_comp` and `logDeriv_mul` to factor; substitute `logDeriv_zpow z k = k/z`; conclude with `linear_combination`/`ring`. Around 48 lines.
- **Hypotheses**: `0 < z.im`, `z ≠ 0`, `f(z) ≠ 0`.
- **Uses from project**: `modularFormCompOfComplex`, `modform_comp_ofComplex_S_identity`, `UpperHalfPlane.isOpen_upperHalfPlaneSet`, `UpperHalfPlane.mdifferentiable_iff`, `f.holo'`.
- **Used by**: `arc_cpv_integral_S_identity`.
- **Visibility**: public
- **Lines**: 62--110
- **Notes**: `omit hf in`; >30 lines.

### `lemma S_isometry_unit_circle`
- **Type**: `(z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) : ‖-(1:ℂ)/z - (-(1:ℂ)/w)‖ = ‖z - w‖`
- **What**: `z ↦ -1/z` is an isometry on the unit circle: distances between two unit-modulus points are preserved.
- **How**: Show `z, w ≠ 0` from unit norm, rewrite `-1/z - (-1/w) = (z-w)/(z·w)` via `field_simp`, take norms.
- **Hypotheses**: `‖z‖ = ‖w‖ = 1`.
- **Uses from project**: none.
- **Used by**: `arc_indicator_symmetric_of_sArcOfS`.
- **Visibility**: public
- **Lines**: 115--129
- **Notes**: `omit f hf`.

### `lemma fdBoundary_arc_S_reverse`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ∈ Set.Ioo (1:ℝ) 3) : fdBoundary_H H (4 - t) = -(1:ℂ) / fdBoundary_H H t`
- **What**: On the arc segment, the boundary parameterization satisfies the S-reflection identity `γ(4-t) = -1/γ(t)`.
- **How**: Rewrite both sides via `fdBoundary_H_eq_arc`, clear denominator using `eq_div_iff (exp_ne_zero _)`, combine exponentials via `← Complex.exp_add`, then `exp(iπ) = -1`.
- **Hypotheses**: `1 < t < 3`.
- **Uses from project**: `fdBoundary_H_eq_arc`.
- **Used by**: `arc_indicator_symmetric_of_sArcOfS`, `arc_cpv_integral_S_identity`.
- **Visibility**: public
- **Lines**: 134--142
- **Notes**: `omit f hf`.

### `private lemma arc_indicator_symmetric_of_sArcOfS`
- **Type**: `(S : Finset UpperHalfPlane) (H ε : ℝ) (t : ℝ) (ht : t ∈ Set.Ioo (1:ℝ) 3) : (∃ s ∈ sArcOfS S, ‖fdBoundary_H H (4 - t) - s‖ ≤ ε) ↔ (∃ s ∈ sArcOfS S, ‖fdBoundary_H H t - s‖ ≤ ε)`
- **What**: The arc-singularity indicator (∃ s near boundary point) is invariant under the S-symmetry `t ↦ 4-t` on the arc.
- **How**: Use `sArcOfS_unit`, `sArcOfS_closed`, `fdBoundary_arc_S_reverse`, `S_isometry_unit_circle`; for `↦`, witness `-1/s₀ ∈ sArcOfS S` and chain a calc with isometry, field_simp, and the reverse identity. ~30 lines.
- **Hypotheses**: `t ∈ (1,3)`.
- **Uses from project**: `sArcOfS_unit`, `sArcOfS_closed`, `fdBoundary_arc_S_reverse`, `S_isometry_unit_circle`, `fdBoundary_H_eq_arc`.
- **Used by**: `arc_cpv_integral_S_identity`.
- **Visibility**: private
- **Lines**: 147--177
- **Notes**: `omit f hf`; >30 lines.

### `private lemma cpv_integrand_intervalIntegrable_arc`
- **Type**: `(S : Finset UpperHalfPlane) (H : ℝ) (ε : ℝ) (hε : 0 < ε) (h_oncurve : ∀ t ∈ Set.Ioo (1:ℝ) 3, modularFormCompOfComplex f (fdBoundary_H H t) = 0 → fdBoundary_H H t ∈ (↑(sArcOfS S) : Set ℂ)) : IntervalIntegrable (fun t => cauchyPrincipalValueIntegrandOn (sArcOfS S) (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) volume 1 3`
- **What**: The CPV integrand for `logDeriv f` along the arc with `ε`-cutout around `sArcOfS S` is interval-integrable over `[1,3]`.
- **How**: Define `K' = {t ∈ [1,3] | dist≥ε for all s ∈ sArcOfS S}`, a closed subset of compact `Icc 1 3`, hence compact. Show integrand continuous on `K'` (using `analyticAt_logDeriv_off_zeros`, `fdBoundary_H_continuous`, `deriv_fdBoundary_H_arc`), giving `IntegrableOn` via `ContinuousOn.integrableOn_compact`. Show CPV indicator vanishes outside `K`. Conclude `IntervalIntegrable` via union decomposition. ~80 lines.
- **Hypotheses**: `0 < ε`; if `f` vanishes on arc, vanishing point is in `sArcOfS S`.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `sArcOfS`, `sArcOfS_rho_in`, `sArcOfS_rho_plus_one_in`, `fdBoundary_H`, `fdBoundary_H_at_one`, `fdBoundary_H_at_three`, `fdBoundary_H_continuous`, `fdBoundary_H_eq_arc`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, `analyticAt_logDeriv_off_zeros`, `deriv_fdBoundary_H_arc`, `modularFormCompOfComplex`.
- **Used by**: `arc_cpv_integral_S_identity`.
- **Visibility**: private
- **Lines**: 181--294
- **Notes**: >30 lines.

### `private lemma arc_preimage_subsingleton`
- **Type**: `(H : ℝ) (s : ℂ) : Set.Subsingleton ({t ∈ Set.Ioo (1:ℝ) 3 | fdBoundary_H H t = s})`
- **What**: The arc parameterization `fdBoundary_H H` is injective on `(1,3)`: each point in the image has at most one preimage parameter.
- **How**: Compare real parts via `exp_ofReal_mul_I_re`, use `Real.strictAntiOn_cos.injOn` on `[0,π]` to deduce `t₁ = t₂` via `mul_left_cancel₀`/`linarith`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_H_eq_arc`.
- **Used by**: `arc_non_excluded_measure_tendsto`.
- **Visibility**: private
- **Lines**: 299--315
- **Notes**: `omit f hf`.

### `private lemma arc_min_dist_pos`
- **Type**: `(S : Finset UpperHalfPlane) (H : ℝ) {t : ℝ} (_ht : t ∈ Set.Ioo (1:ℝ) 3) (h_not_in : (fdBoundary_H H t : ℂ) ∉ (↑(sArcOfS S) : Set ℂ)) : ∃ δ > 0, ∀ s ∈ sArcOfS S, δ ≤ ‖fdBoundary_H H t - s‖`
- **What**: If the boundary point at parameter `t` is not in `sArcOfS S`, then it has positive minimum distance to that finset.
- **How**: Case-split on `sArcOfS S = ∅` (use `1`) or use `Finset.exists_min_image` to extract minimizer `s₀`; `δ = ‖γ(t) - s₀‖ > 0` from `h_not_in`.
- **Hypotheses**: `γ(t) ∉ sArcOfS S`.
- **Uses from project**: `sArcOfS`, `fdBoundary_H`.
- **Used by**: `arc_non_excluded_measure_tendsto`.
- **Visibility**: private
- **Lines**: 318--329
- **Notes**: `omit f hf`.

### `lemma arc_cpv_integral_S_identity`
- **Type**: `(S : Finset UpperHalfPlane) (H : ℝ) (ε : ℝ) (hε : 0 < ε) (h_oncurve : ...) : (∫ t in 1..3, cauchyPrincipalValueIntegrandOn (sArcOfS S) (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) = -(↑k * (↑Real.pi / 12 * I)) * ↑(∫ t in 1..3, if (∃ s ∈ sArcOfS S, ‖fdBoundary_H H t - s‖ ≤ ε) then 0 else 1)`
- **What**: The ε-cutout CPV integral on the arc equals `-(k · π/12 · i)` times the Lebesgue measure of `t ∈ [1,3]` excluded from the cutout.
- **How**: Show pointwise on `[1,3]`: `F(4-t) + F(t) = -(k·π/6·i) · indicator(t)` by S-symmetry combined with `logDeriv_modform_S_transform`. Integrate, use `intervalIntegral.integral_comp_sub_left` to get `∫ F(4-t) = ∫ F(t)`, divide by 2, getting `I = -(k·π/12·i) · m`. ~125 lines.
- **Hypotheses**: `0 < ε`; on-curve avoidance for zeros of `f`.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `sArcOfS`, `sArcOfS_rho_in`, `sArcOfS_rho_plus_one_in`, `fdBoundary_H`, `fdBoundary_H_at_one`, `fdBoundary_H_at_three`, `fdBoundary_H_eq_arc`, `fdBoundary_arc_S_reverse`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, `modularFormCompOfComplex`, `arc_indicator_symmetric_of_sArcOfS`, `cpv_integrand_intervalIntegrable_arc`, `logDeriv_modform_S_transform`, `deriv_fdBoundary_H_arc`.
- **Used by**: `arc_cpv_contribution_tendsto`.
- **Visibility**: public
- **Lines**: 334--469
- **Notes**: `omit hf`; >30 lines.

### `lemma arc_non_excluded_measure_tendsto`
- **Type**: `(S : Finset UpperHalfPlane) (H : ℝ) : Tendsto (fun ε => ∫ t in 1..3, if (∃ s ∈ sArcOfS S, ‖fdBoundary_H H t - s‖ ≤ ε) then 0 else 1) (𝓝[>] 0) (𝓝 2)`
- **What**: The Lebesgue measure of `t ∈ [1,3]` outside the ε-cutout around `sArcOfS S` tends to 2 as `ε → 0⁺`.
- **How**: Use `tendsto_integral_filter_of_dominated_convergence` with dominating constant 1; show that off a null set (preimages of finite singular set under arc map, plus `{3}`), the indicator is eventually `1`. Uses `arc_min_dist_pos` and `arc_preimage_subsingleton`. ~60 lines.
- **Hypotheses**: none.
- **Uses from project**: `sArcOfS`, `fdBoundary_H`, `fdBoundary_H_continuous`, `arc_min_dist_pos`, `arc_preimage_subsingleton`.
- **Used by**: `arc_cpv_contribution_tendsto`.
- **Visibility**: public
- **Lines**: 474--532
- **Notes**: `omit f hf`; >30 lines.

### `theorem arc_cpv_contribution_tendsto`
- **Type**: `(S : Finset UpperHalfPlane) (H : ℝ) (h_oncurve : ∀ t ∈ Set.Ioo (1:ℝ) 3, modularFormCompOfComplex f (fdBoundary_H H t) = 0 → fdBoundary_H H t ∈ (↑(sArcOfS S) : Set ℂ)) : Tendsto (fun ε => ∫ t in 1..3, cauchyPrincipalValueIntegrandOn (sArcOfS S) (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) (𝓝[>] 0) (𝓝 (-(2 * ↑Real.pi * I * (k : ℂ) / 12)))`
- **What**: The ε-truncated CPV arc integral of `logDeriv f` tends to `-(2πik/12)` as `ε → 0⁺` — the modular arc contribution to the valence formula.
- **How**: From `arc_cpv_integral_S_identity` express integrand as `g(m(ε))`; use `arc_non_excluded_measure_tendsto` (m → 2) and continuity of `g(x) = -(k · π/12 · i)·x` to conclude.
- **Hypotheses**: on-curve avoidance.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `sArcOfS`, `fdBoundary_H`, `modularFormCompOfComplex`, `arc_cpv_integral_S_identity`, `arc_non_excluded_measure_tendsto`.
- **Used by**: `tendsto_pvIntegral_arc_bridge`.
- **Visibility**: public
- **Lines**: 537--562
- **Notes**: `omit hf`.

### `private lemma arc_re_strictly_between`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ∈ Set.Ioo (1:ℝ) 3) : -1/2 < (fdBoundary_H H t).re ∧ (fdBoundary_H H t).re < 1/2`
- **What**: On the open arc `t ∈ (1,3)`, the real part of the boundary lies strictly in `(-1/2, 1/2)`.
- **How**: Express `Re(γ(t)) = cos(π(1+t)/6)`; use `Real.strictAntiOn_cos` on `[0,π]` with `cos(2π/3) = -1/2`, `cos(π/3) = 1/2` to bound.
- **Hypotheses**: `t ∈ (1,3)`.
- **Uses from project**: `fdBoundary_H_eq_arc`.
- **Used by**: `arc_ne_svert`.
- **Visibility**: private
- **Lines**: 567--588
- **Notes**: `omit f hf`.

### `private lemma arc_ne_svert`
- **Type**: `(H : ℝ) (S : Finset UpperHalfPlane) (s : ℂ) (hs_re : s.re = 1/2 ∨ s.re = -1/2) (hs_not : s ∉ sArcOfS S) (t : ℝ) (ht : t ∈ Set.Icc (1:ℝ) 3) : fdBoundary_H H t ≠ s`
- **What**: A vertical-line singular point (Re = ±1/2) that is not on the arc cannot coincide with any boundary point in the closed arc parameter range `[1,3]`.
- **How**: Split `t ∈ {1, 3, (1,3)}`. On `(1,3)` use `arc_re_strictly_between`. At endpoints `1, 3` use that the value is `ρ+1` resp. `ρ`, both lying in `sArcOfS S` by `sArcOfS_rho_*_in`, contradicting `hs_not`.
- **Hypotheses**: `s` is on a vertical edge; `s ∉ sArcOfS S`.
- **Uses from project**: `arc_re_strictly_between`, `sArcOfS`, `sArcOfS_rho_in`, `sArcOfS_rho_plus_one_in`, `fdBoundary_H_at_one`, `fdBoundary_H_at_three`.
- **Used by**: `arc_min_dist_pos_of_svert`.
- **Visibility**: private
- **Lines**: 591--604
- **Notes**: `omit f hf`.

### `private lemma arc_min_dist_pos_of_svert`
- **Type**: `(H : ℝ) (S : Finset UpperHalfPlane) (s : ℂ) (hs_re : s.re = 1/2 ∨ s.re = -1/2) (hs_not : s ∉ sArcOfS S) : ∃ δ > 0, ∀ t ∈ Set.Icc (1:ℝ) 3, δ ≤ ‖fdBoundary_H H t - s‖`
- **What**: A vertical-line singular point not on the arc has a positive uniform distance from the arc on `[1,3]`.
- **How**: Use `IsCompact.exists_isMinOn` on `Icc 1 3` (compact, nonempty) with continuous function `‖γ(t) - s‖`; positivity at the minimizer follows from `arc_ne_svert`.
- **Hypotheses**: `s.re = ±1/2`; `s ∉ sArcOfS S`.
- **Uses from project**: `fdBoundary_H_continuous`, `arc_ne_svert`.
- **Used by**: `arc_svert_combined_dist`.
- **Visibility**: private
- **Lines**: 607--617
- **Notes**: `omit f hf`.

### `private lemma arc_svert_combined_dist`
- **Type**: `(H : ℝ) (S : Finset UpperHalfPlane) : ∃ δ > 0, ∀ s ∈ sVertOfS S, s ∉ sArcOfS S → ∀ t ∈ Set.Icc (1:ℝ) 3, δ ≤ ‖fdBoundary_H H t - s‖`
- **What**: A uniform positive distance δ separates the arc from any vertical-edge singular point that lies outside `sArcOfS S` (a finite "min over finset" construction).
- **How**: Per-point `arc_min_dist_pos_of_svert` gives `δₛ`; induct on the finset `SV` taking pairwise minima with `min δ₁ δ₂` to combine bounds.
- **Hypotheses**: none.
- **Uses from project**: `sVertOfS`, `sVertOfS_re`, `sArcOfS`, `arc_min_dist_pos_of_svert`.
- **Used by**: `arc_cpv_eventually_eq_union`.
- **Visibility**: private
- **Lines**: 620--655
- **Notes**: `omit f hf`; >30 lines.

### `lemma arc_cpv_eventually_eq_union`
- **Type**: `(S : Finset UpperHalfPlane) (H : ℝ) (g : ℂ → ℂ) : ∀ᶠ ε in 𝓝[>] 0, ∫ t in 1..3, cauchyPrincipalValueIntegrandOn (sArcOfS S ∪ sVertOfS S) g (fdBoundary_H H) ε t = ∫ t in 1..3, cauchyPrincipalValueIntegrandOn (sArcOfS S) g (fdBoundary_H H) ε t`
- **What**: For small enough ε, the CPV integral cutout based on `sArcOfS S ∪ sVertOfS S` equals the one based on `sArcOfS S` alone on the arc parameter interval (i.e., vertical edges contribute nothing for small ε).
- **How**: Get uniform δ from `arc_svert_combined_dist`; for `ε < δ` and any `t ∈ [1,3]`, a vert point that is not on the arc lies at distance >ε, so cutout decisions match. Conclude via `intervalIntegral.integral_congr`.
- **Hypotheses**: none on `g`.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `sArcOfS`, `sVertOfS`, `arc_svert_combined_dist`, `fdBoundary_H`.
- **Used by**: `tendsto_pvIntegral_arc_bridge`.
- **Visibility**: public
- **Lines**: 658--687
- **Notes**: `omit f hf`.

### `theorem tendsto_pvIntegral_arc_bridge`
- **Type**: `(S : Finset UpperHalfPlane) {H : ℝ} (_hH : Real.sqrt 3 / 2 < H) (h_oncurve_arc : ∀ t ∈ Set.Ioo (1:ℝ) 3, modularFormCompOfComplex f (fdBoundary_H H t) = 0 → fdBoundary_H H t ∈ (↑(sArcOfS S) : Set ℂ)) : Tendsto (fun ε => ∫ t in 1..3, pvIntegrand f (fdBoundary_H H) (sArcOfS S ∪ sVertOfS S) ε t) (𝓝[>] 0) (𝓝 (-(2 * ↑Real.pi * I * ((k : ℂ) / 12))))`
- **What**: Final bridge for `Assembly.lean`: the ε-truncated PV integral of `pvIntegrand` along the arc using the *combined* `sArcOfS ∪ sVertOfS` singular set tends to `-(2πi(k/12))`.
- **How**: Combine `arc_cpv_contribution_tendsto` with the `arc_cpv_eventually_eq_union` rewrite (target rewritten via small ring fact).
- **Hypotheses**: `H > √3/2`; on-curve avoidance for `f` on arc.
- **Uses from project**: `pvIntegrand`, `sArcOfS`, `sVertOfS`, `fdBoundary_H`, `modularFormCompOfComplex`, `arc_cpv_contribution_tendsto`, `arc_cpv_eventually_eq_union`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 692--706
- **Notes**: `omit hf`.

---

## File Summary

- **Total declarations**: 15 (1 theorem, 8 lemmas (5 of which `omit` `f`/`hf`), 6 private lemmas).
- **Key API (public)**: `arc_cpv_contribution_tendsto`, `tendsto_pvIntegral_arc_bridge` (Assembly-facing bridge); supporting `arc_cpv_integral_S_identity`, `arc_cpv_eventually_eq_union`, `logDeriv_modform_S_transform`, `S_isometry_unit_circle`, `fdBoundary_arc_S_reverse`, `arc_non_excluded_measure_tendsto`.
- **Unused in file**: `tendsto_pvIntegral_arc_bridge` (terminal export to Assembly.lean).
- **Sorries**: none.
- **set_options**: `attribute [local instance] Classical.propDecidable` (no `set_option` directives).
- **Long proofs (>30 lines)**: `logDeriv_modform_S_transform` (~48), `arc_indicator_symmetric_of_sArcOfS` (~30), `cpv_integrand_intervalIntegrable_arc` (~114), `arc_cpv_integral_S_identity` (~135), `arc_non_excluded_measure_tendsto` (~58), `arc_svert_combined_dist` (~36).
- **One-paragraph purpose**: Proves the modular arc contribution to the principal-value chain in the valence formula. The key identity is that on the unit-circle arc of the fundamental domain, the modular S-transformation `z ↦ -1/z` is an isometry, and the log-derivative functional equation `logDeriv f(z) = logDeriv f(-1/z)/z² - k/z` paired with the parameter symmetry `t ↦ 4-t` yields `F(4-t) + F(t) = -(k·π/6·i) · indicator(t)`. Integrating and using `t ↦ 4-t` substitution forces `2·I(ε) = -(k·π/6·i)·m(ε)`, hence `I(ε) = -(k·π/12·i)·m(ε)`. Since the excluded measure m(ε) → 2 as ε → 0⁺ (the singular set has measure zero), `I(ε) → -(2πik/12)`. The file exports `tendsto_pvIntegral_arc_bridge` for use in `Assembly.lean` to identify the arc segment's contribution in the global PV chain.
