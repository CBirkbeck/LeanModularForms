# ModularInvariance.lean Inventory

### `abbrev modularFormCompOfComplex`
- **Type**: `(f : ModularForm (Gamma 1) k) → ℂ → ℂ`
- **What**: Composes a modular form with `UpperHalfPlane.ofComplex` to view it as `ℂ → ℂ` (zero outside `ℍ`), used in contour-integration setups.
- **How**: `f ∘ UpperHalfPlane.ofComplex`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `modularForm_finitely_many_zeros_in_fdBox`
- **Visibility**: public
- **Lines**: 30
- **Notes**: none

### `private lemma mero_sub_const_fwd`
- **Type**: `(g : ℂ → ℂ) (x c : ℂ) (h_sub_an : AnalyticAt ℂ (· − c) (x + c)) (hg : MeromorphicAt g x) → MeromorphicAt (fun w => g (w − c)) (x + c)`
- **What**: Meromorphy is transported forward through the affine shift `w ↦ w − c`.
- **How**: Use the meromorphy witness `n`; rewrite `(w − (x + c))^n • g (w − c)` as `(· − x)^n • g(·) ∘ (· − c)`; conclude via `AnalyticAt.comp_of_eq`.
- **Hypotheses**: `g` meromorphic at `x`; `(· − c)` analytic at `x + c`.
- **Uses from project**: []
- **Used by**: `meromorphicOrderAt_comp_sub_const`
- **Visibility**: private
- **Lines**: 32-43
- **Notes**: none

### `private lemma mero_sub_const_bwd`
- **Type**: `(g : ℂ → ℂ) (x c : ℂ) (h_add_an : AnalyticAt ℂ (· + c) x) (hgφ : MeromorphicAt (fun w => g (w − c)) (x + c)) → MeromorphicAt g x`
- **What**: Reverse direction: meromorphy of the shifted function pulls back to `g`.
- **How** (~11 lines): Use the witness `n` for the shifted version; rewrite to factor through `(· + c)`; apply `AnalyticAt.comp_of_eq`.
- **Hypotheses**: Same as forward (analyticity of `· + c`).
- **Uses from project**: []
- **Used by**: `meromorphicOrderAt_comp_sub_const`
- **Visibility**: private
- **Lines**: 45-56
- **Notes**: none

### `private lemma filter_map_sub_const`
- **Type**: `(x c : ℂ) {p : ℂ → Prop} (hp : ∀ᶠ z in 𝓝[≠] x, p z) → ∀ᶠ w in 𝓝[≠] (x + c), p (w − c)`
- **What**: Eventual statements on punctured nhd of `x` transfer to punctured nhd of `x + c` via the substitution `w − c`.
- **How**: Push forward via `Homeomorph.addRight (-c)` using `Homeomorph.map_punctured_nhds_eq`.
- **Hypotheses**: Eventual property on `𝓝[≠] x`.
- **Uses from project**: []
- **Used by**: `meromorphicOrderAt_comp_sub_const`
- **Visibility**: private
- **Lines**: 58-65
- **Notes**: none

### `private lemma meromorphicOrderAt_comp_sub_const`
- **Type**: `(g : ℂ → ℂ) (x c : ℂ) → meromorphicOrderAt (fun w => g (w − c)) (x + c) = meromorphicOrderAt g x`
- **What**: The meromorphic order is invariant under affine shifts.
- **How** (~22 lines): Case-split on meromorphy and `⊤`-order. In the finite case, extract a witness `(h, hh_an, hh_ne, hh_eq)` via `meromorphicOrderAt_eq_int_iff`, build the corresponding witness for the shifted function as `h(· − c)` using `AnalyticAt.comp_of_eq` and `filter_map_sub_const`, then close with `smul_eq_mul` rewriting.
- **Hypotheses**: None on `g`.
- **Uses from project**: [`mero_sub_const_fwd`, `mero_sub_const_bwd`, `filter_map_sub_const`]
- **Used by**: `ord_add_one_eq`
- **Visibility**: private
- **Lines**: 67-89
- **Notes**: none

### `private lemma mero_neg_inv_fwd`
- **Type**: `(g : ℂ → ℂ) (p : ℂ) (hp : p ≠ 0) (hg : MeromorphicAt g (−p⁻¹)) → MeromorphicAt (fun z => g (−z⁻¹)) p`
- **What**: Meromorphy at `−p⁻¹` transports forward through the S-substitution `z ↦ −z⁻¹` at `p`.
- **How**: Compose with analytic `neg` and `inv`, congruence to the literal lambda.
- **Hypotheses**: `p ≠ 0`.
- **Uses from project**: []
- **Used by**: `meromorphicOrderAt_comp_neg_inv`
- **Visibility**: private
- **Lines**: 91-96
- **Notes**: none

### `private lemma mero_neg_inv_bwd`
- **Type**: `(g : ℂ → ℂ) (p : ℂ) (hp : p ≠ 0) (hgφ : MeromorphicAt (fun z => g (−z⁻¹)) p) → MeromorphicAt g (−p⁻¹)`
- **What**: Reverse: meromorphy of `g(−z⁻¹)` at `p ≠ 0` gives meromorphy of `g` at `−p⁻¹`.
- **How** (~14 lines): Treat as `(g ∘ Neg.neg) ∘ Inv.inv`; replace `p = p⁻¹⁻¹`, compose with `inv`, congrue with `inv_inv`; then compose with `neg` and congrue with `neg_neg`.
- **Hypotheses**: `p ≠ 0`.
- **Uses from project**: []
- **Used by**: `meromorphicOrderAt_comp_neg_inv`
- **Visibility**: private
- **Lines**: 98-112
- **Notes**: none

### `private lemma filter_map_neg_inv`
- **Type**: `(p : ℂ) (hp : p ≠ 0) {Q : ℂ → Prop} (hQ : ∀ᶠ z in 𝓝[≠] (−p⁻¹), Q z) → ∀ᶠ w in 𝓝[≠] p, Q (−w⁻¹)`
- **What**: Eventually-`Q` on punctured nhd of `−p⁻¹` pulls back through `−·⁻¹` to a punctured nhd of `p`.
- **How** (~10 lines): Build `Tendsto` of `−z⁻¹` from `𝓝[≠] p` to `𝓝[≠] (−p⁻¹)` via `tendsto_nhdsWithin_iff`, using analyticity at `p`, then apply.
- **Hypotheses**: `p ≠ 0`.
- **Uses from project**: []
- **Used by**: `meromorphicOrderAt_comp_neg_inv`, `neg_inv_finite_order_witness`
- **Visibility**: private
- **Lines**: 114-123
- **Notes**: none

### `private lemma neg_inv_finite_order_witness`
- **Type**: `(g : ℂ → ℂ) (p : ℂ) (hp : p ≠ 0) (n : ℤ) (h : ℂ → ℂ) (hh_an : AnalyticAt ℂ h (−p⁻¹)) (hh_ne : h (−p⁻¹) ≠ 0) (hh_eq : ∀ᶠ z in 𝓝[≠] (−p⁻¹), g z = (z − (−p⁻¹))^n • h z) → ∃ h' : ℂ → ℂ, AnalyticAt ℂ h' p ∧ h' p ≠ 0 ∧ ∀ᶠ z in 𝓝[≠] p, g (−z⁻¹) = (z − p)^n • h' z`
- **What**: Transport a finite-order Laurent-style witness for `g` at `−p⁻¹` to a witness for `g(−·⁻¹)` at `p`.
- **How** (~20 lines): Choose `h' z := (z·p)^(−n) · h(−z⁻¹)`; check analyticity (`zpow`+composition), nonvanishing (`mul_ne_zero`); use `−z⁻¹ − (−p⁻¹) = (z − p) · (z·p)⁻¹` to rewrite `(z − p)^n · (z·p)⁻¹^n · h(−z⁻¹) = (z − p)^n · ((z·p)^(−n) · h(−z⁻¹))`.
- **Hypotheses**: `p ≠ 0`; finite-order data for `g` at `−p⁻¹`.
- **Uses from project**: [`filter_map_neg_inv`]
- **Used by**: `meromorphicOrderAt_comp_neg_inv`
- **Visibility**: private
- **Lines**: 125-146
- **Notes**: none

### `private lemma meromorphicOrderAt_comp_neg_inv`
- **Type**: `(g : ℂ → ℂ) (p : ℂ) (hp : p ≠ 0) → meromorphicOrderAt (fun z => g (−z⁻¹)) p = meromorphicOrderAt g (−p⁻¹)`
- **What**: Meromorphic order is invariant under the S-substitution `z ↦ −z⁻¹`.
- **How** (~14 lines): Case-split on meromorphy and `⊤`-order. In the finite case extract via `meromorphicOrderAt_eq_int_iff` and apply `neg_inv_finite_order_witness`.
- **Hypotheses**: `p ≠ 0`.
- **Uses from project**: [`mero_neg_inv_fwd`, `mero_neg_inv_bwd`, `filter_map_neg_inv`, `neg_inv_finite_order_witness`]
- **Used by**: `ord_S_eq`
- **Visibility**: private
- **Lines**: 148-161
- **Notes**: none

### `lemma ord_add_one_eq`
- **Type**: `(f : ModularForm (Gamma 1) k) (p : ℍ) → orderOfVanishingAt' f ((1 : ℝ) +ᵥ p) = orderOfVanishingAt' f p`
- **What**: T-invariance of the vanishing order: `ord(f, z+1) = ord(f, z)`.
- **How** (~25 lines): Unfold `orderOfVanishingAt'`; set `G(w) := if 0 < w.im then f ⟨w, _⟩ else 0`; show `G =ᶠ[𝓝[≠] (p + 1)] (G ∘ (· − 1))` using `SlashInvariantForm.vAdd_width_periodic` at width 1; conclude via `meromorphicOrderAt_congr` and `meromorphicOrderAt_comp_sub_const`.
- **Hypotheses**: None beyond the implicit `f`.
- **Uses from project**: [`meromorphicOrderAt_comp_sub_const`]
- **Used by**: `ord_rho_plus_one_eq_ord_rho`
- **Visibility**: public
- **Lines**: 164-189
- **Notes**: none

### `lemma ord_rho_plus_one_eq_ord_rho`
- **Type**: `orderOfVanishingAt' f ellipticPointRhoPlusOne' = orderOfVanishingAt' f ellipticPointRho'`
- **What**: T-invariance at the elliptic point `ρ`: `ord(f, ρ+1) = ord(f, ρ)`.
- **How**: Show `(1 : ℝ) +ᵥ ρ' = (ρ+1)'` via `UpperHalfPlane.ext`, then apply `ord_add_one_eq`.
- **Hypotheses**: None.
- **Uses from project**: [`ord_add_one_eq`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 192-203
- **Notes**: none

### `lemma modform_comp_ofComplex_S_identity`
- **Type**: `(z : ℂ) (hz : 0 < z.im) → f (UpperHalfPlane.ofComplex (−1/z)) = z^k * f (UpperHalfPlane.ofComplex z)`
- **What**: The S-transformation identity at the level of `ℂ`-coercion: `f(−1/z) = z^k · f(z)`.
- **How** (~24 lines): Compute `(−1/z).im > 0`; rewrite via `ofComplex_apply_of_im_pos`; show `⟨−1/z, _⟩ = S • ⟨z, _⟩` (using `UpperHalfPlane.modular_S_smul`); apply `SlashInvariantForm.slash_action_eqn_SL''` for `S ∈ Gamma 1` and rewrite `denom_S`.
- **Hypotheses**: `0 < z.im`.
- **Uses from project**: []
- **Used by**: `modform_G_S_identity`
- **Visibility**: public
- **Lines**: 206-229
- **Notes**: none

### `private lemma modform_G_S_identity`
- **Type**: `(G : ℂ → ℂ) (hG_def : G = …) (z : ℂ) (hz : 0 < z.im) → G (−z⁻¹) = z^k * G z`
- **What**: S-identity in the indicator form `G` used by `ord_S_eq`.
- **How** (~20 lines): Reduce both sides of the `if` to `f` evaluated on the appropriate UHP elements; apply `modform_comp_ofComplex_S_identity`.
- **Hypotheses**: `G` agrees with the indicator extension; `0 < z.im`.
- **Uses from project**: [`modform_comp_ofComplex_S_identity`]
- **Used by**: `ord_S_eq`
- **Visibility**: private
- **Lines**: 231-251
- **Notes**: none

### `private lemma modform_G_meromorphicAt`
- **Type**: `(G : ℂ → ℂ) (hG_def : …) (p : ℍ) → MeromorphicAt G (p : ℂ)`
- **What**: The indicator extension `G` is meromorphic (in fact analytic) at every point of `ℍ`.
- **How** (~13 lines): Use `AnalyticAt.meromorphicAt`; differentiate `f ∘ ofComplex` on the open UHP set via `UpperHalfPlane.mdifferentiable_iff.mp f.holo'`; transfer via `congr_of_eventuallyEq` using the `if 0 < w.im` branch.
- **Hypotheses**: `G` is the indicator extension.
- **Uses from project**: []
- **Used by**: `ord_S_eq`
- **Visibility**: private
- **Lines**: 253-267
- **Notes**: none

### `private lemma meromorphicOrderAt_zpow_eq_zero`
- **Type**: `(p_cplx : ℂ) (hp_ne : p_cplx ≠ 0) → meromorphicOrderAt (fun z : ℂ => z^k) p_cplx = 0`
- **What**: The `zpow` function has meromorphic order `0` at any nonzero point.
- **How** (~7 lines): It is analytic with no zero, so `analyticOrderAt_eq_zero.mpr (Or.inr (zpow_ne_zero …))`; transfer via `AnalyticAt.meromorphicOrderAt_eq`.
- **Hypotheses**: `p_cplx ≠ 0`.
- **Uses from project**: []
- **Used by**: `ord_S_eq`
- **Visibility**: private
- **Lines**: 269-276
- **Notes**: none

### `lemma ord_S_eq`
- **Type**: `(p : ℍ) → orderOfVanishingAt' f (ModularGroup.S • p) = orderOfVanishingAt' f p`
- **What**: S-invariance of the vanishing order: `ord(f, S·z) = ord(f, z)`.
- **How** (~25 lines): Set `G` the indicator extension and `p_cplx := (p : ℂ)`; rewrite `((S • p) : ℂ) = −p_cplx⁻¹`. Calc-chain: `meromorphicOrderAt G (−p_cplx⁻¹) = meromorphicOrderAt (G ∘ (−·⁻¹)) p_cplx` (by `meromorphicOrderAt_comp_neg_inv`) `= meromorphicOrderAt (z^k · G z) p_cplx` (by `meromorphicOrderAt_congr` using `modform_G_S_identity`) `= meromorphicOrderAt z^k + meromorphicOrderAt G` (by `meromorphicOrderAt_mul`) `= meromorphicOrderAt G p_cplx` (by `meromorphicOrderAt_zpow_eq_zero`).
- **Hypotheses**: None.
- **Uses from project**: [`meromorphicOrderAt_comp_neg_inv`, `modform_G_S_identity`, `modform_G_meromorphicAt`, `meromorphicOrderAt_zpow_eq_zero`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 279-305
- **Notes**: none

### `def fdBox`
- **Type**: `(M : ℝ) → Set ℂ`
- **What**: An open box `{z : −1 < re < 1, 1/2 < im < M}` containing the truncated fundamental domain.
- **How**: Set-builder.
- **Hypotheses**: None (definition).
- **Uses from project**: []
- **Used by**: `fdBox_im_pos`, `modularForm_finitely_many_zeros_in_fdBox`
- **Visibility**: public
- **Lines**: 308
- **Notes**: none

### `lemma fdBox_im_pos`
- **Type**: `{M : ℝ} {z : ℂ} (hz : z ∈ fdBox M) → 0 < z.im`
- **What**: Points of `fdBox M` lie in the open upper half-plane.
- **How**: `linarith [hz.2.2.1]`.
- **Hypotheses**: `z ∈ fdBox M`.
- **Uses from project**: [`fdBox`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 310-311
- **Notes**: none

### `theorem modularForm_finitely_many_zeros_in_fdBox`
- **Type**: `(hf : f ≠ 0) {M : ℝ} (hM : 1/2 < M) → Set.Finite {z ∈ fdBox M | modularFormCompOfComplex f z = 0}`
- **What**: A nonzero modular form has only finitely many zeros inside the bounded box `fdBox M`.
- **How** (~30 lines): Suppose infinitely many; the bounded box has a compact closure where an accumulation point `z₀` exists (`Set.Infinite.exists_accPt_of_subset_isCompact`); accumulating zeros at `z₀ ∈ ℍ` plus `AnalyticOnNhd` on `U := {z : 0 < z.im}` (connected, by `Complex.isConnected_of_upperHalfPlane`) force the form to vanish identically on `U` via `eqOn_zero_of_preconnected_of_frequently_eq_zero`, contradicting `hf`.
- **Hypotheses**: `f ≠ 0`; `1/2 < M`.
- **Uses from project**: [`fdBox`, `modularFormCompOfComplex`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 314-344
- **Notes**: > 30 lines

### `theorem cuspFunction_not_eventually_zero`
- **Type**: `(hf : f ≠ 0) → ¬ ∀ᶠ q in 𝓝 0, SlashInvariantFormClass.cuspFunction 1 (⇑f) q = 0`
- **What**: The cusp function of a nonzero modular form is not identically zero on any neighborhood of `0`.
- **How** (~17 lines): If it were, analyticity on `Metric.ball 0 1` plus connectedness force `cuspFunction = 0` on the ball; using `SlashInvariantFormClass.eq_cuspFunction` evaluated at the q-parameter, conclude `f ≡ 0` (contradiction).
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: []
- **Used by**: `cuspFunction_eventually_ne_zero`
- **Visibility**: public
- **Lines**: 347-369
- **Notes**: none

### `theorem cuspFunction_eventually_ne_zero`
- **Type**: `(hf : f ≠ 0) → ∀ᶠ q in 𝓝[≠] (0 : ℂ), SlashInvariantFormClass.cuspFunction 1 (⇑f) q ≠ 0`
- **What**: Near `0`, the cusp function avoids `0` except possibly at `0` itself.
- **How**: Apply `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` and rule out the zero case with `cuspFunction_not_eventually_zero`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: [`cuspFunction_not_eventually_zero`]
- **Used by**: `exists_radius_cusp_nonvanishing`
- **Visibility**: public
- **Lines**: 372-379
- **Notes**: none

### `theorem exists_radius_cusp_nonvanishing`
- **Type**: `(hf : f ≠ 0) → ∃ r > 0, ∀ q ∈ Metric.closedBall 0 r, q ≠ 0 → cuspFunction 1 (⇑f) q ≠ 0`
- **What**: There is a positive radius on whose punctured closed ball the cusp function is nonvanishing.
- **How** (~6 lines): Extract a witness from `cuspFunction_eventually_ne_zero` via `eventually_nhds_iff`/`Metric.isOpen_iff`, then use `r/2` for the closed ball.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: [`cuspFunction_eventually_ne_zero`]
- **Used by**: `exists_height_cusp_nonvanishing`
- **Visibility**: public
- **Lines**: 382-390
- **Notes**: none

### `noncomputable def heightOfRadius`
- **Type**: `(r : ℝ) → ℝ`
- **What**: Converts a q-radius `r` to a height `−log r / (2π)`; inverse of `q = exp(−2πH)`.
- **How**: Direct definition.
- **Hypotheses**: None (definition).
- **Uses from project**: []
- **Used by**: `exists_height_cusp_nonvanishing`
- **Visibility**: public
- **Lines**: 393
- **Notes**: none

### `theorem exists_height_cusp_nonvanishing`
- **Type**: `(hf : f ≠ 0) → ∃ H > √3/2, ∀ q ∈ Metric.closedBall 0 (exp (−2π H)), q ≠ 0 → cuspFunction 1 (⇑f) q ≠ 0`
- **What**: There is a fundamental-domain-boundary height `H > √3/2` above which the cusp function is nonvanishing.
- **How** (~16 lines): Take `r` from `exists_radius_cusp_nonvanishing`; set `H₀ := max (heightOfRadius r) (√3/2 + 1)`; both clauses follow from `max` properties and `Real.exp_log`, using `Metric.closedBall_subset_closedBall`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: [`exists_radius_cusp_nonvanishing`, `heightOfRadius`]
- **Used by**: `exists_height_cusp_nonvanishing_above`
- **Visibility**: public
- **Lines**: 396-416
- **Notes**: none

### `lemma cusp_nonvanishing_height_mono`
- **Type**: `{H₁ H₂ : ℝ} (hH : H₁ ≤ H₂) (h : … H₁ …) → … H₂ …`
- **What**: The cusp-nonvanishing property is monotone in `H` (larger heights are weaker constraints on `q`).
- **How**: `Metric.closedBall_subset_closedBall` with `Real.exp_le_exp` and `nlinarith [Real.pi_pos]`.
- **Hypotheses**: `H₁ ≤ H₂`.
- **Uses from project**: []
- **Used by**: `exists_height_cusp_nonvanishing_above`
- **Visibility**: public
- **Lines**: 419-425
- **Notes**: none

### `theorem exists_height_cusp_nonvanishing_above`
- **Type**: `(hf : f ≠ 0) (Hmin : ℝ) → ∃ H, Hmin ≤ H ∧ √3/2 < H ∧ (∀ q ∈ Metric.closedBall 0 (exp (−2π H)), q ≠ 0 → cuspFunction 1 (⇑f) q ≠ 0)`
- **What**: Cusp nonvanishing above any prescribed floor height.
- **How**: Combine `exists_height_cusp_nonvanishing` and `cusp_nonvanishing_height_mono` with `max H₀ Hmin`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: [`exists_height_cusp_nonvanishing`, `cusp_nonvanishing_height_mono`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 428-434
- **Notes**: none

## File Summary

Establishes invariance of the vanishing order of a level-1 modular form under the full modular group SL₂(ℤ): T-invariance (`ord_add_one_eq`, `ord_rho_plus_one_eq_ord_rho`) and S-invariance (`ord_S_eq`), routed through generic shift/S-substitution lemmas for `meromorphicOrderAt` (`meromorphicOrderAt_comp_sub_const`, `meromorphicOrderAt_comp_neg_inv`) plus the S-identity `modform_comp_ofComplex_S_identity`. Adds the `fdBox` truncation of the fundamental domain with finiteness of zeros (`modularForm_finitely_many_zeros_in_fdBox`) and a chain on cusp nonvanishing culminating in `exists_height_cusp_nonvanishing` and `exists_height_cusp_nonvanishing_above`.
