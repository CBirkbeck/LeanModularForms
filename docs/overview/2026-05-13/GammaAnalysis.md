# GammaAnalysis.lean Inventory

### `private lemma hasDerivAt_remainder_bound`
- **Type**: `{γ t₀ L} (hγ : HasDerivAt γ L t₀) : ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < |t - t₀| → |t - t₀| < δ → ‖γ t - γ t₀ - (t-t₀) • L‖ ≤ ε · |t - t₀|`
- **What**: Little-o remainder: `γ(t) - γ(t₀) - (t-t₀)·L` is bounded by `ε|t-t₀|` near `t₀`.
- **How**: Rewrite `HasDerivAt` via `hasDerivAt_iff_isLittleO` and `Asymptotics.isLittleO_iff`, extract the `δ`-ball from `Metric.mem_nhds_iff`, then `simpa` to drop `Real.norm_eq_abs`.
- **Hypotheses**: `HasDerivAt γ L t₀`.
- **Uses from project**: []
- **Used by**: `gamma_lower_bound_of_hasDerivAt`, `gamma_upper_bound_of_hasDerivAt`
- **Visibility**: private
- **Lines**: 33-42
- **Notes**: 10 lines.

### `private lemma norm_real_smul`
- **Type**: `(x : ℝ) (L : ℂ) : ‖x • L‖ = |x| · ‖L‖`
- **What**: Norm of a real-scalar multiple equals `|x|·‖L‖`.
- **How**: `simp [Complex.real_smul]`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `gamma_lower_bound_of_hasDerivAt`, `gamma_upper_bound_of_hasDerivAt`
- **Visibility**: private
- **Lines**: 44-45
- **Notes**: None.

### `private lemma norm_add_lower_bound`
- **Type**: `(a b : ℂ) : ‖a + b‖ ≥ ‖a‖ - ‖b‖`
- **What**: Reverse triangle inequality.
- **How**: `norm_sub_norm_le a (-b)`, then `linarith` after `sub_neg_eq_add`/`norm_neg`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `gamma_lower_bound_of_hasDerivAt`
- **Visibility**: private
- **Lines**: 47-50
- **Notes**: None.

### `private lemma farSet_isCompact`
- **Type**: `(a b t₀ δ : ℝ) (_hab : a < b) (_hδ : 0 < δ) : IsCompact {t | t ∈ Icc a b ∧ δ ≤ |t - t₀|}`
- **What**: The "far set" `{t ∈ [a,b] : δ ≤ |t - t₀|}` is compact.
- **How**: `IsCompact.inter_right` of `isCompact_Icc` with closedness from continuity of `|· - t₀|`.
- **Hypotheses**: `a < b`, `0 < δ` (both unused but kept for shape).
- **Uses from project**: []
- **Used by**: `norm_sub_pos_on_farSet`
- **Visibility**: private
- **Lines**: 52-55
- **Notes**: None.

### `private lemma norm_sub_pos_on_farSet`
- **Type**: `(γ a b t₀ δ) (hab hδ) (hγ_cont) (h_inj_far) : ∃ m > 0, ∀ t ∈ Icc a b, δ ≤ |t - t₀| → m ≤ ‖γ t - γ t₀‖`
- **What**: Uniform positive lower bound of `‖γ - γ(t₀)‖` on the far set.
- **How**: Extract minimum via `IsCompact.exists_isMinOn` on the continuous norm restricted to the compact far set; positivity from injectivity `h_inj_far` via `norm_pos_iff`; empty far set returns the trivial bound `1`.
- **Hypotheses**: `a < b`, `0 < δ`, continuity, injectivity at `γ(t₀)` on the far set.
- **Uses from project**: [`farSet_isCompact`]
- **Used by**: unused in file
- **Visibility**: private
- **Lines**: 57-75
- **Notes**: 19 lines.

### `lemma integrand_times_t_tendsto_one`
- **Type**: `(γ t₀ L) (hL : L ≠ 0) (hγ_hasderiv) (hγ_cont_at) : Tendsto (fun t => ↑(t - t₀) · (γ t - γ t₀)⁻¹ · deriv γ t) (𝓝[≠] t₀) (𝓝 1)`
- **What**: Key PV estimate: `(t-t₀) · (γ-γ₀)⁻¹ · γ' → 1` as `t → t₀`.
- **How**: Combine `hasDerivAt_iff_tendsto_slope_zero` (slope tends to `L`) with `Tendsto.inv₀` to get ratio limit `L⁻¹`, multiply by `deriv γ` (tendsto `L` from continuity), inv-cancel to `L⁻¹·L = 1`.
- **Hypotheses**: `L ≠ 0`, `HasDerivAt γ L t₀`, `ContinuousAt (deriv γ) t₀`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 80-129
- **Notes**: 50 lines; deep tendsto-massaging using `Tendsto.comp`, `Algebra.smul_def`, and case-splits on `γ t - γ t₀ = 0`/`(t : ℂ) - t₀ = 0`.

### `lemma integrand_asymptotic`
- **Type**: `(γ t₀ L) (_hL) (_hγ_hasderiv) (_hγ_cont_at) (h_tendsto) : ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < |t-t₀| → |t-t₀| < δ → ‖(γ t - γ t₀)⁻¹ · deriv γ t - (↑(t-t₀))⁻¹‖ ≤ ε / |t-t₀|`
- **What**: Quantitative asymptotic of the residual `(γ - γ₀)⁻¹ · γ' - (t-t₀)⁻¹` near `t₀`.
- **How**: Translate `Tendsto … 1` into a `Metric.tendsto_nhdsWithin_nhds` ε-δ statement; algebraically rewrite the residual via `field_simp` as `(quantity - 1) · (↑(t-t₀))⁻¹` and bound by `ε · ‖(t-t₀)⁻¹‖ = ε/|t-t₀|`.
- **Hypotheses**: Existence of the limit-1 from `integrand_times_t_tendsto_one`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 133-159
- **Notes**: 27 lines.

### `lemma gamma_lower_bound_of_hasDerivAt`
- **Type**: `{γ t₀ L} (hL : L ≠ 0) (hγ_hasderiv) : ∃ δ > 0, ∀ t, 0 < |t-t₀| → |t-t₀| < δ → ‖γ t - γ t₀‖ ≥ (‖L‖/2) · |t-t₀|`
- **What**: Lower bound `‖γ - γ₀‖ ≥ (‖L‖/2)|t - t₀|` near `t₀` when the derivative is nonzero.
- **How**: Use `hasDerivAt_remainder_bound` with `ε = ‖L‖/2`; reverse triangle inequality `norm_add_lower_bound` against `(t-t₀)·L` after writing `γ - γ₀ = (t-t₀)·L + remainder`; close with `linarith`/`ring` after `norm_real_smul`.
- **Hypotheses**: `L ≠ 0`, `HasDerivAt γ L t₀`.
- **Uses from project**: [`hasDerivAt_remainder_bound`, `norm_add_lower_bound`, `norm_real_smul`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 163-185
- **Notes**: 23 lines.

### `lemma gamma_upper_bound_of_hasDerivAt`
- **Type**: `{γ t₀ L} (hL : L ≠ 0) (hγ_hasderiv) : ∃ δ > 0, ∀ t, 0 < |t-t₀| → |t-t₀| < δ → ‖γ t - γ t₀‖ ≤ 2·‖L‖·|t - t₀|`
- **What**: Upper bound `‖γ - γ₀‖ ≤ 2‖L‖|t - t₀|` near `t₀`.
- **How**: `hasDerivAt_remainder_bound` with `ε = ‖L‖`; triangle inequality on `γ - γ₀ = (t-t₀)·L + remainder`; finish with `linarith`/`ring` using `norm_real_smul`.
- **Hypotheses**: `L ≠ 0`, `HasDerivAt γ L t₀`.
- **Uses from project**: [`hasDerivAt_remainder_bound`, `norm_real_smul`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 189-210
- **Notes**: 22 lines.

### `lemma no_return_of_inj_continuous`
- **Type**: `{γ a b t₀ c} (hc_pos : 0 < c) (hγ_cont) (h_inj : ∀ t ∈ Icc a b, γ t = γ t₀ → t = t₀) : ∃ ρ > 0, ∀ t ∈ Icc a b, c ≤ |t - t₀| → ρ ≤ ‖γ t - γ t₀‖`
- **What**: If `γ` is continuous on `[a,b]` and injective at `γ(t₀)`, it stays bounded away from `γ(t₀)` outside any neighborhood of `t₀`.
- **How**: Take `S = Icc a b ∩ {δ ≤ |·-t₀|}` (compact via `isCompact_Icc.inter_right`), use continuity of `‖γ - γ₀‖` and positivity via injectivity to invoke `IsCompact.exists_forall_le'` for the global minimum `ρ`.
- **Hypotheses**: `0 < c`, continuity, injectivity at `γ(t₀)`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 214-233
- **Notes**: 20 lines.

### `lemma t_bound_from_gamma_bound`
- **Type**: `{γ t₀ t L εC δ} (hL) (_hδ_pos) (ht_pos) (ht_lt) (h_lower) (h_gamma_bound : ‖γ t - γ t₀‖ ≤ εC) : |t - t₀| ≤ 2·εC/‖L‖`
- **What**: From γ-space upper bound to t-space upper bound via the lower-bound inversion.
- **How**: From `h_lower` get `(‖L‖/2)·|t-t₀| ≤ εC`, then `calc` divides by `‖L‖/2` using `div_le_div_of_nonneg_right`.
- **Hypotheses**: `L ≠ 0`, parameter-distance positivity, lower bound on `‖γ - γ₀‖`, γ-space upper bound.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 237-248
- **Notes**: 12 lines.

### `lemma t_lower_from_gamma_lower`
- **Type**: `{γ t₀ t L εC δ} (hL) (_hδ_pos) (ht_pos) (ht_lt) (h_upper) (h_gamma_lower : εC < ‖γ t - γ t₀‖) : εC / (2·‖L‖) < |t - t₀|`
- **What**: From γ-space lower bound to t-space lower bound via the upper-bound inversion.
- **How**: From `h_upper` get `εC < 2·‖L‖·|t-t₀|`, then `calc` divides by `2·‖L‖` via `div_lt_div_of_pos_right`.
- **Hypotheses**: `L ≠ 0`, parameter-distance positivity, upper bound on `‖γ - γ₀‖`, γ-space lower bound.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 252-262
- **Notes**: 11 lines.

### `lemma contAt_deriv_of_contDiffAt_two`
- **Type**: `{γ t₀} (hγ_C2 : ContDiffAt ℝ 2 γ t₀) : ContinuousAt (deriv γ) t₀`
- **What**: C² regularity gives continuity of `deriv γ` at `t₀`.
- **How**: Extract a `ContDiffOn` neighborhood via `ContDiffAt.contDiffOn`, refine to a metric ball, derive continuity of `fderiv ℝ γ` via `contDiffOn_fderiv_of_isOpen`, then convert to `deriv` using `fderiv_apply_one_eq_deriv` (handling non-differentiable points with `deriv_zero_of_not_differentiableAt`/`fderiv_zero_of_not_differentiableAt`).
- **Hypotheses**: `ContDiffAt ℝ 2 γ t₀`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 265-281
- **Notes**: 17 lines.

## File Summary
PV-infrastructure file establishing derivative-based two-sided bounds on a curve `γ : ℝ → ℂ` near a parameter `t₀`. Private helpers handle the `HasDerivAt`-style little-o remainder, scalar norm, reverse triangle inequality, and a compact far-set lemma. Public results: the principal-value-flavoured estimates `integrand_times_t_tendsto_one` and `integrand_asymptotic`, the symmetric `gamma_lower_bound_of_hasDerivAt`/`gamma_upper_bound_of_hasDerivAt`, `no_return_of_inj_continuous`, the two-way translation lemmas `t_bound_from_gamma_bound`/`t_lower_from_gamma_lower`, and `contAt_deriv_of_contDiffAt_two`. Used as a self-contained toolkit; no internal cross-uses besides the documented chains. No sorries, no axioms.
