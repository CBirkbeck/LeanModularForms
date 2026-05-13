# Inventory: Residue/MultipointPV/DominatedConvergence.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/Residue/MultipointPV/DominatedConvergence.lean`

Imports: `MultipointPV`.

### `private lemma continuousOn_deriv_off_partition`
- **Type**: `(γ : PiecewiseC1Immersion) → ContinuousOn (deriv γ.toFun) (Icc γ.a γ.b \ γ.partition)`
- **What**: The derivative of a piecewise-C¹ immersion is continuous on `[a,b]` minus the partition.
- **How**: Case-split on `t ∈ Ioo a b`: smooth case uses `deriv_continuous_off_partition`; endpoint case derives contradiction from `endpoints_in_partition`.
- **Hypotheses**: γ piecewise C¹ immersion.
- **Uses from project**: `PiecewiseC1Curve.deriv_continuous_off_partition`, `PiecewiseC1Curve.endpoints_in_partition`.
- **Used by**: `A_int_aEStronglyMeasurable`, `pvIntegrand_intervalIntegrable_of_nonempty`
- **Visibility**: private
- **Lines**: 30-47
- **Notes**: none

### `private lemma uIoc_subset_Icc_of_lt`
- **Type**: `{a b : ℝ} (hab : a < b) → Set.uIoc a b ⊆ Icc a b`
- **What**: Under `a < b`, the unsigned interval `uIoc a b` is contained in `Icc a b`.
- **How**: One-liner: `Set.uIoc_of_le ∘ Set.Ioc_subset_Icc_self`.
- **Hypotheses**: `a < b`.
- **Uses from project**: []
- **Used by**: `A_int_aEStronglyMeasurable`, `A_int_norm_bound`
- **Visibility**: private
- **Lines**: 49-50
- **Notes**: none

### `private lemma γt_not_mem_S0_of_all_far`
- **Type**: `{S0 : Finset ℂ} {γ : ℝ → ℂ} {t : ℝ} {ε : ℝ} (hε : 0 < ε) (hall : ∀ s ∈ S0, ε < ‖γ t - s‖) → γ t ∉ (S0 : Set ℂ)`
- **What**: If `γ(t)` is `ε`-far from every point of `S0`, then `γ(t) ∉ S0`.
- **How**: By contradiction: if `γ(t) ∈ S0`, then `0 = ‖γ(t) - γ(t)‖ > ε`, contradiction.
- **Hypotheses**: `0 < ε`, all distances `> ε`.
- **Uses from project**: []
- **Used by**: `A_int_eq_greg_mul_deriv`, `norm_A_int_bound_all_far`, `pvIntegrand_intervalIntegrable_of_nonempty`
- **Visibility**: private
- **Lines**: 52-59
- **Notes**: none

### `private lemma residue_sum_ifs_eq_mul_deriv`
- **Type**: `{S0 : Finset ℂ} {f : ℂ → ℂ} {γ : ℝ → ℂ} {t : ℝ} {ε : ℝ} (hall : ∀ s ∈ S0, ε < ‖γ t - s‖) → ∑ s ∈ S0, (if ε < ‖γ t - s‖ then residueSimplePole f s / (γ t - s) * deriv γ t else 0) = (∑ s ∈ S0, residueSimplePole f s / (γ t - s)) * deriv γ t`
- **What**: When every singular point is far from `γ(t)`, the indicator-sum factors as `(sum of singular fractions) * deriv γ t`.
- **How**: `Finset.sum_mul` plus `if_pos hall s` on each term.
- **Hypotheses**: `ε < ‖γ t - s‖` for all `s ∈ S0`.
- **Uses from project**: `residueSimplePole`.
- **Used by**: `pointwise_ae_limit_off_crossing`, `norm_A_int_bound_all_far`
- **Visibility**: private
- **Lines**: 61-68
- **Notes**: none

### `private lemma A_int_eq_greg_mul_deriv`
- **Type**: `{S0 : Finset ℂ} {f g_reg : ℂ → ℂ} {γ : ℝ → ℂ} {t : ℝ} {ε : ℝ} (hε : 0 < ε) (hall : ∀ s ∈ S0, ε < ‖γ t - s‖) (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) → f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s)) → f (γ t) * deriv γ t - (∑ s ∈ S0, residueSimplePole f s / (γ t - s)) * deriv γ t = g_reg (γ t) * deriv γ t`
- **What**: With `γ(t)` far from all singular points, the difference of `f∘γ · γ'` and the singular fractions equals `g_reg(γ(t)) · γ'(t)`.
- **How**: Use `hg_decomp` at `γ(t)` (via `γt_not_mem_S0_of_all_far`), then `ring`/`sub_mul`.
- **Hypotheses**: `0 < ε`, `γ(t)` ε-far from `S0`, `hg_decomp` regular/singular split.
- **Uses from project**: `γt_not_mem_S0_of_all_far`, `residueSimplePole`.
- **Used by**: unused in file
- **Visibility**: private
- **Lines**: 70-80
- **Notes**: unused in file

### `private lemma residueSimplePole_norm_bound`
- **Type**: `(S0 : Finset ℂ) (f : ℂ → ℂ) (hS0_ne : S0.Nonempty) → ∃ Mc, ∀ s ∈ S0, ‖residueSimplePole f s‖ ≤ Mc`
- **What**: A finite nonempty set has a uniform bound on the norms of `residueSimplePole f s`.
- **How**: Use `Finset.sup'` as the witness; bound by `Finset.le_sup'`.
- **Hypotheses**: `S0` nonempty.
- **Uses from project**: `residueSimplePole`.
- **Used by**: `dominated_convergence_multipoint_helper`
- **Visibility**: private
- **Lines**: 82-87
- **Notes**: none

### `private lemma dominated_convergence_empty_case`
- **Type**: `(f g_reg : ℂ → ℂ) (γ : PiecewiseC1Immersion) (hg_decomp : ∀ z, z ∉ ∅ → f z = g_reg z + ∑ s ∈ ∅, residueSimplePole f s / (z - s)) → Tendsto A (𝓝[>] 0) (𝓝 G)` (with `M`, `S'`, `A`, `G` defined inline as in `dominated_convergence_multipoint_helper`)
- **What**: In the empty-S0 case, `A(ε) ≡ M(ε) ≡ G` so the convergence is trivial.
- **How**: KEY: rewrite `S' ≡ 0` via `Finset.attach_empty`/`Finset.sum_empty`; show `M(ε)` equals the integral of `f∘γ · γ'` via `intervalIntegral.integral_congr` (the indicator is always false on empty); since `f = g_reg` everywhere (from `hg_decomp` on empty), `M(ε) = G`; conclude with `tendsto_const_nhds`.
- **Hypotheses**: trivial empty-set decomposition.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `residueSimplePole`.
- **Used by**: `dominated_convergence_multipoint_helper`
- **Visibility**: private
- **Lines**: 91-126
- **Notes**: >30 lines

### `private lemma pointwise_ae_limit_off_crossing`
- **Type**: `(S0 : Finset ℂ) (f g_reg : ℂ → ℂ) (γ : PiecewiseC1Immersion) (hS0_ne : S0 ≠ ∅) (h_crossing_null : volume {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t ∈ S0} = 0) (hg_decomp : ...) → ∀ᵐ t, t ∈ Ι γ.a γ.b → Tendsto (A_int · t) (𝓝[>] 0) (𝓝 (f_lim t))` (with `A_int` the cutoff integrand minus the singular sum, `f_lim` the regular-part integrand)
- **What**: Off the (measure-zero) crossing set, the cutoff-minus-singular-sum integrand tends pointwise to the regular-part integrand `g_reg(γ(t)) · γ'(t)`.
- **How**: Use `ae_iff` and bound the bad set by the crossing set (measure zero); for any `t` with `γ(t) ∉ S0`, let `δ` be the infimum of distances from `γ(t)` to `S0`; eventually `ε < δ`, so all `S0` points are far, and `A_int ε t = g_reg(γ(t)) · γ'(t)` by `residue_sum_ifs_eq_mul_deriv` and `hg_decomp`; conclude with `Tendsto.congr'`/`tendsto_const_nhds`.
- **Hypotheses**: `S0 ≠ ∅`, crossing set has measure zero, `hg_decomp` split.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `residueSimplePole`, `residue_sum_ifs_eq_mul_deriv`.
- **Used by**: `dominated_convergence_multipoint_helper`
- **Visibility**: private
- **Lines**: 130-191
- **Notes**: >30 lines

### `private lemma norm_A_int_bound_all_far`
- **Type**: `(S0 : Finset ℂ) (f g_reg : ℂ → ℂ) (γ : PiecewiseC1Immersion) (Mg Mγ' : ℝ) (hMg : ‖g_reg‖ ≤ Mg on image) (hMγ' : ‖γ'‖ ≤ Mγ' on Icc) (hg_decomp) {t ε : ℝ} (hε : 0 < ε) (ht : t ∈ Icc a b) (hall : ∀ s ∈ S0, ε < ‖γ t - s‖) (B) (hB) → ‖A_int ε t‖ ≤ B`
- **What**: In the all-far case, the integrand difference is bounded by `Mg · Mγ' ≤ B`.
- **How**: Use `if_neg` (since hall implies no near singular point), `residue_sum_ifs_eq_mul_deriv` and the decomposition to identify it with `g_reg(γt) · γ't`, then `norm_mul_le` and the explicit bounds.
- **Hypotheses**: γ measurable bounds, `0 < ε`, all-far at `t`, `B ≥ max 0 Mg · max 0 Mγ'`.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `γt_not_mem_S0_of_all_far`, `residue_sum_ifs_eq_mul_deriv`, `residueSimplePole`.
- **Used by**: `A_int_norm_bound`
- **Visibility**: private
- **Lines**: 195-226
- **Notes**: >30 lines

### `private lemma residue_sum_norm_le_singular_bound`
- **Type**: `{S0 : Finset ℂ} {f : ℂ → ℂ} {z : ℂ} {Mc δ ε : ℝ} (hδ_pos : 0 < δ) (hMc : norms bounded by Mc) (hδ_sep : pairwise δ-separation) {s₀ : ℂ} (hs₀ ∈ S0) (hs₀_near : ‖z - s₀‖ ≤ ε) → ∀ s ∈ S0, ‖if ‖z - s‖ > ε then residueSimplePole f s / (z - s) else 0‖ ≤ 2 * Mc / δ`
- **What**: Termwise norm bound `2Mc/δ` for each residue term in the singular sum when there is a nearby singular point `s₀`.
- **How**: Case `s = s₀` or `s ≠ s₀`. For `s ≠ s₀`: use triangle inequality `‖z - s‖ ≥ ‖s - s₀‖ - ‖z - s₀‖ ≥ δ - ε ≥ δ/2` (since either `ε ≤ δ/2` or `ε > δ/2` but then `‖z - s‖ > ε > δ/2`); then `norm_div` and `div_le_div_of_nonneg_left` give the bound.
- **Hypotheses**: `0 < δ`, residues bounded by `Mc`, pairwise `δ`-separation, nearby singular point `s₀`.
- **Uses from project**: `residueSimplePole`.
- **Used by**: `norm_A_int_bound_some_near`
- **Visibility**: private
- **Lines**: 228-268
- **Notes**: >30 lines

### `private lemma norm_A_int_bound_some_near`
- **Type**: `(S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) (Mc Mγ' δ : ℝ) (hδ_pos) (hMc) (hMγ') (hδ_sep) {t ε : ℝ} (ht ∈ Icc a b) {s₀} (hs₀ ∈ S0) (hs₀_near) (B) (hB) → ‖A_int ε t‖ ≤ B`
- **What**: In the some-near case, the integrand difference is bounded by `(2 |S0| Mc / δ) · Mγ' ≤ B`.
- **How**: `if_pos` handles the cutoff (`= 0` minus singular sum); refactor the sum via `Finset.sum_mul`; bound the sum by `card · 2Mc/δ` using `residue_sum_norm_le_singular_bound` and `Finset.sum_le_sum`; multiply by `Mγ'`.
- **Hypotheses**: bounds on `‖res‖, ‖γ'‖`, separation, `B ≥ max 0 (2·card·Mc/δ) · max 0 Mγ'`.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `residue_sum_norm_le_singular_bound`, `residueSimplePole`.
- **Used by**: `A_int_norm_bound`
- **Visibility**: private
- **Lines**: 270-324
- **Notes**: >30 lines

### `private lemma A_int_norm_bound`
- **Type**: `(S0 : Finset ℂ) (f g_reg : ℂ → ℂ) (γ : PiecewiseC1Immersion) (Mg Mγ' Mc δ : ℝ) (hδ_pos) (hMg) (hMγ') (hMc) (hg_decomp) (hδ_sep) → ∀ ε > 0, ∀ᵐ t, t ∈ Ι a b → ‖A_int ε t‖ ≤ B` (with `B := max 1 (max (max 0 Mg) (max 0 (2·card·Mc/δ)) · max 0 Mγ')`)
- **What**: A uniform-in-ε norm bound on `A_int ε t` for a.e. `t`, providing the dominating constant for DCT.
- **How**: Use `ae_of_all`; case split on whether all singular points are far from `γ(t)`, dispatching to `norm_A_int_bound_all_far` or `norm_A_int_bound_some_near`; bound feeds into `max` chains.
- **Hypotheses**: same as constituent lemmas.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `norm_A_int_bound_all_far`, `norm_A_int_bound_some_near`, `uIoc_subset_Icc_of_lt`.
- **Used by**: `dominated_convergence_multipoint_helper`
- **Visibility**: private
- **Lines**: 326-352
- **Notes**: >30 lines

### `private lemma A_int_aEStronglyMeasurable`
- **Type**: `(S0 : Finset ℂ) (f g_reg : ℂ → ℂ) (γ : PiecewiseC1Immersion) (hg_decomp) (hg_cont) {ε : ℝ} (hε : 0 < ε) → AEStronglyMeasurable (A_int ε) (volume.restrict (Ι γ.a γ.b))`
- **What**: `A_int ε` is a.e. strongly measurable on the parameter interval.
- **How**: Rewrite `cauchyPrincipalValueIntegrandOn` as the decomposed form (using `hg_decomp` away from `S0`); apply `aEStronglyMeasurable_pv_integrand_decomposed` and `aEStronglyMeasurable_pv_sum_residue`; subtract and pass through `mono_measure`.
- **Hypotheses**: regular split `hg_decomp`, continuity of `g_reg` on image, `0 < ε`.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `continuousOn_deriv_off_partition`, `aEStronglyMeasurable_pv_integrand_decomposed`, `aEStronglyMeasurable_pv_sum_residue`, `uIoc_subset_Icc_of_lt`, `residueSimplePole`.
- **Used by**: `dominated_convergence_multipoint_helper`
- **Visibility**: private
- **Lines**: 356-393
- **Notes**: >30 lines

### `private lemma pvIntegrand_intervalIntegrable_of_nonempty`
- **Type**: `(S0 : Finset ℂ) (f g_reg : ℂ → ℂ) (γ : PiecewiseC1Immersion) (hS0_ne : S0 ≠ ∅) (hg_decomp) (hg_cont) {ε : ℝ} (hε : 0 < ε) → IntervalIntegrable (cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε) volume γ.a γ.b`
- **What**: For nonempty `S0`, the cutoff Cauchy-PV integrand is interval-integrable.
- **How**: KEY: produce a bound `Mb := (|Mg| + |S0| · res_bound / ε) · |Mγ'| + 1` valid on `Icc a b` via the decomposition `hg_decomp` (each `‖residueSimplePole f s / (γt - s)‖ ≤ res_bound/ε` because `‖γt - s‖ > ε`); a.e.-equality to the decomposed expression plus `integrableOn_of_bounded_aeMeasurable` then `mono_set` to `Ioc`.
- **Hypotheses**: `S0 ≠ ∅`, `hg_decomp`, `hg_cont`, `0 < ε`.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `continuousOn_deriv_off_partition`, `piecewiseC1Immersion_deriv_bounded`, `continuousOn_image_bounded`, `residueSimplePole`, `aEStronglyMeasurable_pv_integrand_decomposed`, `γt_not_mem_S0_of_all_far`.
- **Used by**: `A_eq_integral_A_int`
- **Visibility**: private
- **Lines**: 397-478
- **Notes**: >30 lines

### `private lemma A_eq_integral_A_int`
- **Type**: `(S0 : Finset ℂ) (f g_reg : ℂ → ℂ) (γ : PiecewiseC1Immersion) (hS0_ne : S0 ≠ ∅) (hg_decomp) (hg_cont) → ∀ ε > 0, M ε - S' ε = ∫ t in γ.a..γ.b, A_int ε t`
- **What**: Linearity: the difference between the full PV integral and the singular-sum integrals equals the integral of `A_int ε`.
- **How**: `intervalIntegral.integral_finset_sum` puts the sum inside the integral (using termwise `intervalIntegrable_residueTerm`), then a single `integral_sub` against `pvIntegrand_intervalIntegrable_of_nonempty`. Termwise integrability of `Finset.sum` is proved by `Finset.induction_on` (`IntervalIntegrable.add`/`intervalIntegrable_const`).
- **Hypotheses**: nonempty `S0`, decomposition, continuity.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `pvIntegrand_intervalIntegrable_of_nonempty`, `intervalIntegrable_residueTerm`, `residueSimplePole`.
- **Used by**: `dominated_convergence_multipoint_helper`
- **Visibility**: private
- **Lines**: 480-524
- **Notes**: >30 lines

### `lemma dominated_convergence_multipoint_helper`
- **Type**: `(S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) (g_reg : ℂ → ℂ) (_h_crossing_null) (_hg_decomp) (_hg_cont) (hS0_sep : ∃ δ > 0, pairwise) → Tendsto A (𝓝[>] 0) (𝓝 G)`
- **What**: Core DCT for multi-point PV: the difference between the multi-point cutoff integral and the sum of single-point cutoff integrals converges to the regular-part integral.
- **How**: KEY: empty case via `dominated_convergence_empty_case`; nonempty case rewrites `S'` via `Finset.sum_attach`, rewrites `A ε = ∫ A_int ε t` via `A_eq_integral_A_int`, then applies `tendsto_integral_of_dominated'` with measurability `A_int_aEStronglyMeasurable`, bound `A_int_norm_bound` (with constants from `piecewiseC1Immersion_deriv_bounded`, `continuousOn_image_bounded`, `residueSimplePole_norm_bound`), and pointwise limit `pointwise_ae_limit_off_crossing`.
- **Hypotheses**: regular split, continuity of `g_reg`, pairwise separation of `S0`, crossing null.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `residueSimplePole`, `piecewiseC1Immersion_deriv_bounded`, `continuousOn_image_bounded`, `residueSimplePole_norm_bound`, `dominated_convergence_empty_case`, `A_eq_integral_A_int`, `A_int_aEStronglyMeasurable`, `A_int_norm_bound`, `pointwise_ae_limit_off_crossing`.
- **Used by**: `multipointPV_diff_tendsto`
- **Visibility**: public (`lemma`)
- **Lines**: 529-581
- **Notes**: >30 lines

### `lemma multipointPV_diff_tendsto`
- **Type**: `(S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) (_h_crossing_null) (g_reg : ℂ → ℂ) (_hg_decomp) (hg_cont) (hS0_sep) → Tendsto A (𝓝[>] 0) (𝓝 G)`
- **What**: Same convergence statement as the helper, with `S'` expressed via `Finset.attach`.
- **How**: Rewrite the attached sum into a plain `S0`-indexed sum via `Finset.sum_attach`, then defer to `dominated_convergence_multipoint_helper`.
- **Hypotheses**: same as helper.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `residueSimplePole`, `dominated_convergence_multipoint_helper`.
- **Used by**: `multipointPV_eq_sum_of_integral_zero`
- **Visibility**: public (`lemma`)
- **Lines**: 584-608
- **Notes**: none

### `lemma multipointPV_eq_sum_of_integral_zero`
- **Type**: `(S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) (_h_crossing_null) (_g_reg) (_hg_decomp) (_hg_cont) (_hS0_sep) (_hg_zero : regular integral = 0) (_hPV_exists : CauchyPrincipalValueExistsOn) (_hPV_each_tendsto : sum-of-single-PV cutoffs convergent) → cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b = ∑ s ∈ S0, cauchyPrincipalValue' (fun z => residueSimplePole f s / (z - s)) γ.toFun γ.a γ.b s`
- **What**: When the regular-part integral vanishes, the multi-point PV equals the sum of the single-pole PVs.
- **How**: From `multipointPV_diff_tendsto` (with regular integral = 0), conclude `S' → L`. Combined with `_hPV_each_tendsto → ∑ (single PV)`, `tendsto_nhds_unique` gives `L = ∑ (single PV)`. Then `hL.limUnder_eq` translates `cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b = L`.
- **Hypotheses**: PV exists, regular integral zero, separation, decomposition, continuity.
- **Uses from project**: `multipointPV_diff_tendsto`, `cauchyPrincipalValueOn`, `cauchyPrincipalValue'`, `residueSimplePole`, `CauchyPrincipalValueExistsOn`, `cauchyPrincipalValueIntegrandOn`.
- **Used by**: unused in file
- **Visibility**: public (`lemma`)
- **Lines**: 611-666
- **Notes**: >30 lines

## File Summary

- **Total declarations**: 16 (including private lemmas).
- **Key public API**:
  - `dominated_convergence_multipoint_helper` — core DCT statement (attach-sum form).
  - `multipointPV_diff_tendsto` — DCT statement (plain sum form).
  - `multipointPV_eq_sum_of_integral_zero` — final equality decomposing multi-point PV into a sum of single-pole PVs.
- **Unused (within this file)**: `A_int_eq_greg_mul_deriv`, `multipointPV_eq_sum_of_integral_zero`.
- **Sorries**: none.
- **set_options**: none.
- **Long proofs** (>30 lines): `dominated_convergence_empty_case`, `pointwise_ae_limit_off_crossing`, `norm_A_int_bound_all_far`, `residue_sum_norm_le_singular_bound`, `norm_A_int_bound_some_near`, `A_int_norm_bound`, `A_int_aEStronglyMeasurable`, `pvIntegrand_intervalIntegrable_of_nonempty`, `A_eq_integral_A_int`, `dominated_convergence_multipoint_helper`, `multipointPV_eq_sum_of_integral_zero`.
- **Purpose**: This file constructs the dominated-convergence engine that decomposes the Cauchy principal value of an integrand `f∘γ · γ'` (with `f` having simple poles at points in a finite set `S0`) into the sum of single-pole CPVs along a piecewise-C¹ immersion. It supplies the pointwise a.e. limit (off the measure-zero crossing set), uniform-in-ε norm bounds via case-split on near/far singular points, joint measurability of `A_int ε`, interval-integrability of the cutoff integrand, and an integral linearity identity. The main theorems package these via `tendsto_integral_of_dominated'` to yield the multi-point PV decomposition that's used downstream when the regular-part integral vanishes.
