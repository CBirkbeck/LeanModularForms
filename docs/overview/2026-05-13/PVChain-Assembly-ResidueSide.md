# PVChain/Assembly/ResidueSide.lean — Inventory

### `private lemma fd_point_mem_fdBox`
- **Type**: `(S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) {H M : ℝ} (hM_half : 1/2 < M) (hH_lt_M : H < M) (hH_bound : ∀ s ∈ S, (s : ℂ).im < H) (p : UpperHalfPlane) (hp_S : p ∈ S) (hp_zero : f p = 0) : (↑p : ℂ) ∈ allZerosInFdBox f hf hM_half`
- **What**: A zero of `f` in `S ⊆ 𝒟` with `im < H < M` and `|re| ≤ 1/2` lies in the `allZerosInFdBox` set at level `M`.
- **How**: Unfold `mem_allZerosInFdBox_iff`, split into the box-membership tuple (`re ≥ -M`, `re ≤ M`, `im > 1/2`, `im < M`) via `abs_le` and `linarith`, and use `nlinarith` against `‖p‖ ≥ 1` (from FD) to discharge `im > 1/2`. The function-value condition is reduced via `UpperHalfPlane.ofComplex_apply_of_im_pos` so `modularFormCompOfComplex f (↑p) = f p = 0`. 25-line proof; key lemmas `mem_allZerosInFdBox_iff`, `abs_le`, `Complex.normSq_apply`, `UpperHalfPlane.coe_re/coe_im`.
- **Hypotheses**: `f`, `hf`, finite `S` in `𝒟`, `H < M`, height bound on `S`, zero hypothesis
- **Uses from project**: `𝒟`, `allZerosInFdBox`, `mem_allZerosInFdBox_iff`, `modularFormCompOfComplex`, `UpperHalfPlane.ofComplex_apply_of_im_pos`, `UpperHalfPlane.coe_re`, `UpperHalfPlane.coe_im`
- **Used by**: `cpv_residue_side_sum_convert`
- **Visibility**: private
- **Lines**: 33-59
- **Notes**: `include hf`; 27 lines

### `private lemma exists_height_above_sqrt3_and_S`
- **Type**: `(S : Finset UpperHalfPlane) : ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧ 1 ≤ H₀ ∧ ∀ s ∈ S, (s : ℂ).im < H₀`
- **What**: Stronger version of `exists_height_above_S_and_sqrt3`: also forces `H₀ ≥ 1`.
- **How**: Empty case picks `H₀ = 1` using `Real.sq_sqrt 3`. Nonempty case picks `max 1 (sup' im S + 1)` and uses `Finset.le_sup'` plus `lt_add_one`.
- **Hypotheses**: none (`omit f hf in`)
- **Uses from project**: []
- **Used by**: `cpv_residue_side_tendsto`
- **Visibility**: private
- **Lines**: 61-74
- **Notes**: `omit f hf in`

### `private lemma cpv_residue_side_simplePoles`
- **Type**: `(S : Finset UpperHalfPlane) {H : ℝ} (_hH_sqrt3 : √3/2 < H) {M : ℝ} (hM_half : 1/2 < M) (Sbox : Finset ℂ) (hSbox : Sbox = allZerosInFdBox f hf hM_half) (S_on : Finset ℂ) (hS_on : S_on = sArcOfS S ∪ sVertOfS S) : ∀ s ∈ Sbox ∪ S_on, HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) s`
- **What**: Every point of `Sbox ∪ S_on` has positive imaginary part, so `logDeriv(f ∘ ofComplex)` has a simple pole there.
- **How**: Case-split `Finset.mem_union`; in the `Sbox` branch, use `fdBox_im_pos` after unpacking `mem_allZerosInFdBox_iff`; in the `S_on` branch, split via `sArcOfS_im_pos` and `sVertOfS_im_pos`. Then apply `hasSimplePoleAt_logDeriv_at_point`.
- **Hypotheses**: `include hf`; height ≥ √3/2; box index level; box and on-curve set definitions
- **Uses from project**: `allZerosInFdBox`, `mem_allZerosInFdBox_iff`, `sArcOfS`, `sVertOfS`, `sArcOfS_im_pos`, `sVertOfS_im_pos`, `fdBox_im_pos`, `hasSimplePoleAt_logDeriv_at_point`, `modularFormCompOfComplex`
- **Used by**: `cpv_residue_side_tendsto`
- **Visibility**: private
- **Lines**: 76-94
- **Notes**: `include hf`

### `private lemma cpv_residue_side_Fp_diffOn`
- **Type**: `(_S : Finset UpperHalfPlane) {M : ℝ} (hM_half : 1/2 < M) (Sbox : Finset ℂ) (hSbox : Sbox = allZerosInFdBox f hf hM_half) (S_on : Finset ℂ) (S0 : Finset ℂ) (hS0 : S0 = Sbox ∪ S_on) (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) s) : let F := logDeriv (modularFormCompOfComplex f); let Fp := logDerivPatched F S0 hSimplePoles; DifferentiableOn ℂ Fp (fdBox M \ ↑S0)`
- **What**: The patched `logDeriv` is differentiable on `fdBox M \ S0` (the singular set is removed).
- **How**: For `z ∉ S0`, an open neighborhood (`S0.finite_toSet.isClosed.isOpen_compl.mem_nhds`) makes `Fp =ᶠ[𝓝 z] F`; `f ∘ ofComplex` is nonzero there (else `z ∈ allZerosInFdBox ⊆ S0`), so `analyticAt_logDeriv_off_zeros'` gives differentiability, lifted to `DifferentiableWithinAt`.
- **Hypotheses**: `include hf`; equations relating `Sbox`/`S_on`/`S0`; simple-pole certificate
- **Uses from project**: `allZerosInFdBox`, `mem_allZerosInFdBox_iff`, `fdBox`, `fdBox_im_pos`, `logDerivPatched`, `logDerivPatched_eq_raw_off`, `analyticAt_logDeriv_off_zeros'`, `modularFormCompOfComplex`
- **Used by**: `cpv_residue_side_tendsto`
- **Visibility**: private
- **Lines**: 96-118
- **Notes**: `include hf`

### `private lemma cpv_residue_side_cpvExists`
- **Type**: `(_S : Finset UpperHalfPlane) {H : ℝ} (hH_sqrt3 : √3/2 < H) (S0 : Finset ℂ) (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) s) : let F := logDeriv (modularFormCompOfComplex f); let _γ := fdBoundary_H H; let Fp := logDerivPatched F S0 hSimplePoles; let γ_imm := fdBoundary_HImmersion H hH_sqrt3; ∀ s ∈ S0, CauchyPrincipalValueExists' (fun z => residueSimplePole Fp s / (z - s)) γ_imm.toFun γ_imm.a γ_imm.b s`
- **What**: For each `s ∈ S0`, the CPV of `residue/(z-s)` along the FD boundary exists.
- **How**: Replace `Fp`-residue by `F`-residue via `residue_logDerivPatched_eq_raw`. Case on whether γ hits `s`: on-curve uses `fdBoundary_H_cpv_exists_of_onCurve` lifted by `cpvExists_scale`; off-curve uses `cpvExists_of_off_curve` with `fdBoundary_H_continuous`.
- **Hypotheses**: height ≥ √3/2; simple-pole certificate (no `include hf` because indirect via `logDerivPatched`)
- **Uses from project**: `logDerivPatched`, `residueSimplePole`, `residue_logDerivPatched_eq_raw`, `fdBoundary_H`, `fdBoundary_HImmersion`, `fdBoundary_H_cpv_exists_of_onCurve`, `fdBoundary_H_continuous`, `cpvExists_scale`, `cpvExists_of_off_curve`, `CauchyPrincipalValueExists'`, `modularFormCompOfComplex`
- **Used by**: `cpv_residue_side_tendsto`
- **Visibility**: private
- **Lines**: 120-141
- **Notes**: none

### `private lemma cpv_residue_side_off_curve_min_dist`
- **Type**: `(S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) {H : ℝ} (hH_sqrt3 : √3/2 < H) (hH_ge1 : 1 ≤ H) (hH_bound : ∀ s ∈ S, (s : ℂ).im < H) {M : ℝ} (hM_half : 1/2 < M) (_hHM : H < M) (Sbox : Finset ℂ) (hSbox : Sbox = allZerosInFdBox f hf hM_half) (S_on : Finset ℂ) (hS_on : S_on = sArcOfS S ∪ sVertOfS S) : ∀ s ∈ Sbox \ S_on, ∃ δ > 0, ∀ t ∈ Icc 0 5, δ ≤ ‖fdBoundary_H H t - s‖`
- **What**: For zeros in the box but not on the boundary curve (i.e. `s ∈ Sbox \ S_on`), the curve maintains a positive distance from `s`.
- **How**: Use `oncurve_full_capture` to certify that any curve point making `f = 0` is in `S_on`; by contradiction, any curve point equal to `s` would force `s ∈ S_on`. Then apply `IsCompact.exists_isMinOn` on the continuous norm function `t ↦ ‖γ t - s‖` on `[0,5]` to extract a minimizing `t₀` with positive norm.
- **Hypotheses**: `include hf`; completeness of `S`; height ≥ √3/2 and ≥ 1; height bounds on `S`; level `M`; set definitions
- **Uses from project**: `𝒟`, `orderOfVanishingAt'`, `oncurve_full_capture`, `fdBoundary_H`, `fdBoundary_H_continuous`, `allZerosInFdBox`, `mem_allZerosInFdBox_iff`, `sArcOfS`, `sVertOfS`, `modularFormCompOfComplex`
- **Used by**: `cpv_residue_side_eventually_eq`
- **Visibility**: private
- **Lines**: 143-173
- **Notes**: `include hf`; uses `IsCompact.exists_isMinOn`

### `private lemma cpv_residue_side_eventually_eq`
- **Type**: `(S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ...) {H : ℝ} (hH_sqrt3 : √3/2 < H) (hH_ge1 : 1 ≤ H) (hH_bound : ∀ s ∈ S, (s : ℂ).im < H) {M : ℝ} (hM_half : 1/2 < M) (hHM : H < M) (Sbox : Finset ℂ) (hSbox : Sbox = allZerosInFdBox f hf hM_half) (S_on : Finset ℂ) (hS_on : ...) (S0 : Finset ℂ) (hS0 : S0 = Sbox ∪ S_on) : let F := ...; let γ := fdBoundary_H H; ∀ᶠ ε in 𝓝[>] 0, ∀ t ∈ uIcc 0 5, cauchyPrincipalValueIntegrandOn S0 F γ ε t = cauchyPrincipalValueIntegrandOn S_on F γ ε t`
- **What**: Eventually in ε, the ε-truncated integrand against `S0` equals the integrand against `S_on` — the off-curve points in `Sbox \ S_on` don't influence the truncation.
- **How**: Use `cpv_residue_side_off_curve_min_dist` to get a δ-bound for each `s ∈ Sbox \ S_on`; via `Filter.eventually_all` applied to the finite subtype `(Sbox \ S_on)`, lift to a uniform eventually-`ε < ‖γ t - s‖`. Then on the split-if comparing the two integrand definitions, the off-curve `S0` membership case is excluded by this bound — proven via a logical `↔` between `(∃ s ∈ S0, ‖γ t - s‖ ≤ ε)` and `(∃ s ∈ S_on, ‖γ t - s‖ ≤ ε)`. 56-line proof; key lemmas `Filter.eventually_all`, `Ioo_mem_nhdsGT`, `Finset.mem_sdiff`.
- **Hypotheses**: `include hf`; completeness; height + level conditions; set definitions
- **Uses from project**: `cpv_residue_side_off_curve_min_dist`, `cauchyPrincipalValueIntegrandOn`, `fdBoundary_H`, `allZerosInFdBox`, `sArcOfS`, `sVertOfS`, `modularFormCompOfComplex`
- **Used by**: `cpv_residue_side_tendsto`
- **Visibility**: private
- **Lines**: 175-230
- **Notes**: `include hf`; 56 lines

### `private lemma cpv_residue_side_sum_convert`
- **Type**: `(S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ...) {H : ℝ} (hH_sqrt3 : √3/2 < H) (hH_ge1 : 1 ≤ H) (hH_bound : ∀ s ∈ S, (s : ℂ).im < H) (S_on : Finset ℂ) (hS_on : S_on = sArcOfS S ∪ sVertOfS S) : let hM_half : 1/2 < H + 1; let Sbox := allZerosInFdBox f hf hM_half; let F := logDeriv (modularFormCompOfComplex f); let γ := fdBoundary_H H; ∑ s ∈ Sbox, generalizedWindingNumber' γ 0 5 s * residueSimplePole F s = ∑ s ∈ S, generalizedWindingNumber' γ 0 5 (↑s : ℂ) * (orderOfVanishingAt' (⇑f) s : ℂ)`
- **What**: Identity converting the residue sum over `Sbox` to the order sum over `S` (the relevant upper half-plane zeros of `f`).
- **How**: Show `S_on \ Sbox` contributes zero (because non-Sbox curve points are non-zeros, residue = 0 there). Set `S_zeros := S.filter (fun p => f p = 0)`, show `S_zeros.image ⊆ Sbox`. By `Finset.sum_subset`, restrict from `Sbox` to the image; by `Finset.sum_image` (injectivity from `UpperHalfPlane.ext`), rewrite as sum over `S_zeros`; substitute residue = order via `residueSimplePole_logDeriv_eq_order`; finally extend from `S_zeros` to all of `S` via `sum_gWN_ord_eq_filter_zeros`. 60-line `calc` proof; key lemmas `Finset.sum_subset`, `Finset.sum_image`, `residueSimplePole_logDeriv_eq_zero_at_nonzero`, `residueSimplePole_logDeriv_eq_order`, `sum_gWN_ord_eq_filter_zeros`.
- **Hypotheses**: `include hf`; completeness; bounds; on-curve set definition
- **Uses from project**: `fd_point_mem_fdBox`, `winding_zero_for_non_fd_point_H_geo`, `residueSimplePole_logDeriv_eq_zero_at_nonzero`, `residueSimplePole_logDeriv_eq_order`, `sum_gWN_ord_eq_filter_zeros`, `fdBox_of_on_curve`, `allZerosInFdBox`, `mem_allZerosInFdBox_iff`, `sArcOfS`, `sArcOfS_im_pos`, `sVertOfS`, `sVertOfS_im_pos`, `fdBoundary_H`, `generalizedWindingNumber'`, `residueSimplePole`, `orderOfVanishingAt'`, `UpperHalfPlane.ofComplex_apply_of_im_pos`, `modularFormCompOfComplex`, `𝒟`
- **Used by**: `cpv_residue_side_tendsto`
- **Visibility**: private
- **Lines**: 232-311
- **Notes**: `include hf`; 80 lines

### `theorem cpv_residue_side_tendsto`
- **Type**: `(S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) : ∃ H₀ : ℝ, √3/2 < H₀ ∧ ∀ {H : ℝ}, H₀ ≤ H → Tendsto (fun ε => ∫ t in 0..5, pvIntegrand f (fdBoundary_H H) (sArcOfS S ∪ sVertOfS S) ε t) (𝓝[>] 0) (𝓝 (2 * ↑Real.pi * I * ∑ s ∈ S, generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) * (orderOfVanishingAt' (⇑f) s : ℂ)))`
- **What**: **Main result.** For every sufficiently large height `H`, the ε-truncated principal-value integral of `f'/f` along the FD boundary tends as ε → 0⁺ to `2πi · Σ gWN · ord`.
- **How**: Pick `H₀` via `exists_height_above_sqrt3_and_S`. Construct `Sbox := allZerosInFdBox` (level `M = H + 1`), `S_on := sArcOfS S ∪ sVertOfS S`, `S0 := Sbox ∪ S_on`, `Fp := logDerivPatched F S0`. Apply `generalizedResidueTheorem'` with `fdBox_isOpen/convex`, `finset_discrete`, `cpv_residue_side_simplePoles`, `cpv_residue_side_Fp_diffOn`, `cpv_residue_side_cpvExists`, and `logDerivPatched`-related lemmas. The result gives a Tendsto towards an `L` equal to `cauchyPrincipalValueOn S0 Fp γ 0 5`. Two congr' steps adjust the integrand: first `Fp → F` (since they agree off `S0`), second `S0 → S_on` truncation (via `cpv_residue_side_eventually_eq`). Finally, `cpv_residue_side_sum_convert` rewrites `L` as `2πi · Σ gWN · ord`, with the `S_on \ Sbox` part contributing 0 (re-proven inline). 119-line proof; key lemmas `generalizedResidueTheorem'`, `Tendsto.congr'`, `Finset.sum_union`, `intervalIntegral.integral_congr`.
- **Hypotheses**: `include hf`; `S ⊆ 𝒟`; completeness of `S`
- **Uses from project**: `exists_height_above_sqrt3_and_S`, `cpv_residue_side_simplePoles`, `cpv_residue_side_Fp_diffOn`, `cpv_residue_side_cpvExists`, `cpv_residue_side_eventually_eq`, `cpv_residue_side_sum_convert`, `allZerosInFdBox`, `mem_allZerosInFdBox_iff`, `fdBoundary_H`, `fdBoundary_H_mem_fdBox'`, `fdBoundary_HCurve_closed`, `fdBoundary_HImmersion`, `fdBox`, `fdBox_isOpen`, `fdBox_convex`, `fdBox_of_on_curve`, `finset_discrete`, `logDerivPatched`, `logDerivPatched_eq_raw_off`, `hasSimplePoleAt_logDerivPatched`, `logDerivPatched_hf_ext`, `residueSimplePole`, `residueSimplePole_logDeriv_eq_zero_at_nonzero`, `residue_logDerivPatched_eq_raw`, `generalizedResidueTheorem'`, `cauchyPrincipalValueIntegrandOn`, `cauchyPrincipalValueOn`, `pvIntegrand`, `generalizedWindingNumber'`, `orderOfVanishingAt'`, `modularFormCompOfComplex`, `sArcOfS`, `sArcOfS_im_pos`, `sVertOfS`, `sVertOfS_im_pos`, `𝒟`
- **Used by**: unused in file (public export)
- **Visibility**: public
- **Lines**: 313-448
- **Notes**: `include hf`; 136-line proof (>30)

## File Summary

- **Total declarations**: 9 (1 public theorem, 8 private lemmas)
- **Purpose**: Discharges the **residue side** of the PV chain for the valence formula. Proves that the ε-truncated integral of `f'/f` around the FD boundary at height `H` converges to `2πi · Σ gWN · ord` over the chosen finite set `S`.
- **Imports used**: `OnCurveCapture` (`oncurve_full_capture`), `ResidueSideInfra` (most of the toolkit: `logDerivPatched`, `allZerosInFdBox`, `fdBox`, `fdBoundary_H` and immersion, `generalizedResidueTheorem'`, residue helpers, capture lemmas), `ModularInvariance`
- **External dependencies**: `modularFormCompOfComplex`, `UpperHalfPlane.ofComplex_apply_of_im_pos`, `IsCompact.exists_isMinOn`, `intervalIntegral`, `pvIntegrand`
- **No sorries, no axioms, no `set_option`**.
- **Architecture**: helper lemmas build up the three ingredients of the generalized residue theorem (simple poles, differentiability, CPV existence) and the residue-to-order identity (`sum_convert`), then assemble via `generalizedResidueTheorem'` and adjust truncation/integrand to match `pvIntegrand`.
