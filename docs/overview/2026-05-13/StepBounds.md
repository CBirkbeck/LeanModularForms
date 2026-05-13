# Inventory: GeneralizedResidueTheory/PVInfrastructure/StepBounds.lean

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/PVInfrastructure/StepBounds.lean`

### `lemma remainder_integral_O_eps`
- **Type**: `{r : ℝ → ℂ} {t₀ ε C : ℝ} (hε_pos : 0 < ε) (_hC_pos : 0 < C) (hr_bound : ∀ t, 0 < |t - t₀| → |t - t₀| ≤ 2 * ε → ‖r t‖ ≤ C) : ‖∫ t in (t₀ - 2*ε)..(t₀ - ε), r t‖ + ‖∫ t in (t₀ + ε)..(t₀ + 2*ε), r t‖ ≤ 2 * C * ε`
- **What**: O(ε) integral bound on the two annulus pieces `[t₀-2ε, t₀-ε] ∪ [t₀+ε, t₀+2ε]` when the integrand has a uniform bound `C` there.
- **How**: For each side, use `intervalIntegral.norm_integral_le_of_norm_le_const` with the uniform constant `C` to bound by `C · ε`; sum is `2Cε`.
- **Hypotheses**: `0 < ε`; integrand bounded by `C` on the punctured annulus radius `2ε`.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 37--65
- **Notes**: none.

### `lemma integral_inv_symm`
- **Type**: `(t₀ ε₁ ε₂ : ℝ) (_hε₁ : 0 < ε₁) (_hε₂ : 0 < ε₂) (_hε₁₂ : ε₁ ≤ ε₂) : (∫ t in (t₀ - ε₂)..(t₀ - ε₁), (↑(t - t₀) : ℂ)⁻¹) + (∫ t in (t₀ + ε₁)..(t₀ + ε₂), (↑(t - t₀) : ℂ)⁻¹) = 0`
- **What**: Odd-symmetric cancellation: the symmetric pair of integrals of `1/(t-t₀)` across a punctured annulus sums to zero.
- **How**: Use oddness `(↑(-u))⁻¹ = -(↑u)⁻¹` and `intervalIntegral.integral_comp_sub_left` with `d = 2t₀` to identify left piece with `-` of the right.
- **Hypotheses**: `0 < ε₁ ≤ ε₂`.
- **Uses from project**: none.
- **Used by**: `pv_singular_cancels`.
- **Visibility**: public
- **Lines**: 68--83
- **Notes**: none.

### `lemma remainder_annulus_bound`
- **Type**: `{r : ℝ → ℂ} {t₀ c₁ c₂ η : ℝ} (hc₁_pos : 0 < c₁) (hc₂_pos : 0 < c₂) (hc₁₂ : c₁ < c₂) (_hη_pos : 0 < η) (hr_bound : ∀ t, c₁ < |t - t₀| → |t - t₀| < c₂ → ‖r t‖ ≤ η / |t - t₀|) : ‖∫ t in (t₀ - c₂)..(t₀ - c₁), r t‖ + ‖∫ t in (t₀ + c₁)..(t₀ + c₂), r t‖ ≤ 2 * η * Real.log (c₂ / c₁)`
- **What**: Bound for the integral of a `1/|t-t₀|`-type remainder over a symmetric annulus by `2η · log(c₂/c₁)`.
- **How**: For each side, bound `‖r(t)‖ ≤ η/|t-t₀|` and compare to `g(t) = η/(t₀-t)` (left) or `η/(t-t₀)` (right). Use `intervalIntegral.norm_integral_le_of_norm_le` with continuous dominating function. Compute `∫ η/u du = η · log(c₂/c₁)` using `integral_inv_of_pos` and `integral_comp_sub_left/right`. ~120 lines.
- **Hypotheses**: `0 < c₁ < c₂`; bound proportional to `η/|t-t₀|` on punctured annulus.
- **Uses from project**: none.
- **Used by**: `step_bound_with_eta`, `remainder_step_bound`, `remainder_bounded_ratio`.
- **Visibility**: public
- **Lines**: 86--209
- **Notes**: >30 lines.

### `lemma exists_eta_delta`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0) (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀) (η : ℝ) (hη : 0 < η) : ∃ δ > 0, ∀ t, 0 < |t - t₀| → |t - t₀| < δ → ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ η / |t - t₀|`
- **What**: For each tolerance `η > 0`, a scale `δ` exists such that the difference between `(γ(t)-γ(t₀))⁻¹·γ'(t)` and `1/(t-t₀)` is bounded by `η/|t-t₀|` on the punctured `δ`-ball.
- **How**: Direct application of `integrand_asymptotic` (from GammaAnalysis) using the auxiliary limit `integrand_times_t_tendsto_one`.
- **Hypotheses**: `L ≠ 0`; `γ` has derivative `L` at `t₀`; `deriv γ` continuous at `t₀`.
- **Uses from project**: `integrand_asymptotic`, `integrand_times_t_tendsto_one` (from GammaAnalysis).
- **Used by**: `error_at_smaller_scale`.
- **Visibility**: public
- **Lines**: 212--218
- **Notes**: none.

### `lemma step_bound_with_eta`
- **Type**: `{r : ℝ → ℂ} {t₀ ε η : ℝ} (hε_pos : 0 < ε) (hη_pos : 0 < η) (hr_bound : ∀ t, 0 < |t - t₀| → |t - t₀| ≤ ε → ‖r t‖ ≤ η / |t - t₀|) : ‖∫ t in (t₀ - ε)..(t₀ - ε/2), r t‖ + ‖∫ t in (t₀ + ε/2)..(t₀ + ε), r t‖ ≤ 2 * η * Real.log 2`
- **What**: Dyadic step bound `[ε/2, ε]`: the remainder contributes at most `2η · log 2`.
- **How**: Apply `remainder_annulus_bound` with `c₁ = ε/2`, `c₂ = ε`, simplifying `log(ε/(ε/2)) = log 2`.
- **Hypotheses**: `0 < ε, η`; bound proportional to `η/|t-t₀|` on `(0, ε]`.
- **Uses from project**: `remainder_annulus_bound`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 221--229
- **Notes**: none.

### `lemma error_at_smaller_scale`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0) (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀) : ∀ η' > 0, ∃ δ > 0, ∀ ε, 0 < ε → ε < δ → (∀ t, 0 < |t - t₀| → |t - t₀| ≤ ε → ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ η' / |t - t₀|)`
- **What**: Re-cast of `exists_eta_delta`: the asymptotic bound `η'/|t-t₀|` holds on all balls `[0,ε]` with `ε < δ`.
- **How**: Unpack `exists_eta_delta` and propagate `|t-t₀| ≤ ε < δ`.
- **Hypotheses**: same as `exists_eta_delta`.
- **Uses from project**: `exists_eta_delta`.
- **Used by**: `exists_delta_for_error_bound`.
- **Visibility**: public
- **Lines**: 232--240
- **Notes**: none.

### `abbrev cutoffIntegral`
- **Type**: `(γ : ℝ → ℂ) (a b t₀ ε : ℝ) : ℂ`
- **What**: The cutoff integral `I(ε) = ∫_a^b 1_{ε < ‖γ(t)-γ(t₀)‖} · (γ(t)-γ(t₀))⁻¹ · γ'(t) dt`, an `abbrev` for the cutoff approximation to the PV integral.
- **How**: Pure definition.
- **Hypotheses**: none.
- **Uses from project**: none.
- **Used by**: unused in file (referenced documentation only).
- **Visibility**: public
- **Lines**: 243--244
- **Notes**: `abbrev`.

### `lemma exists_delta_for_error_bound`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0) (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀) (n : ℕ) : ∃ δ > 0, ∀ ε, 0 < ε → ε < δ → (∀ t, 0 < |t - t₀| → |t - t₀| ≤ ε → ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ (1/2)^n / |t - t₀|)`
- **What**: At the `n`-th dyadic level, supply a scale `δ` so that the remainder bound has constant `(1/2)^n`.
- **How**: Specialization of `error_at_smaller_scale` with `η' = (1/2)^n`.
- **Hypotheses**: as above.
- **Uses from project**: `error_at_smaller_scale`.
- **Used by**: `summableSubseqAux`, `summableSubseqAux_zero/_succ/_pos/_halving/_lt_delta/_error_bound`.
- **Visibility**: public
- **Lines**: 247--253
- **Notes**: none.

### `def summableSubseqAux`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0) (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀) (δ₀ : ℝ) : ℕ → ℝ`
- **What**: Recursive definition of a halving sequence `ε(n)`: `ε(0) = min(δ₀, δ(0))/2`, `ε(n+1) = min(ε(n)/2, δ(n+1))/2` where `δ(n)` comes from `exists_delta_for_error_bound`.
- **How**: `Nat.rec` over `ℕ` with the indicated recurrence.
- **Hypotheses**: `δ₀ : ℝ`.
- **Uses from project**: `exists_delta_for_error_bound`.
- **Used by**: `summableSubseqAux_zero/_succ/_pos/_halving/_lt_delta/_error_bound/_le_geometric/_tendsto_zero`, `exists_summable_subseq`.
- **Visibility**: public
- **Lines**: 255--259
- **Notes**: `def` using `.choose`.

### `lemma summableSubseqAux_zero`
- **Type**: `(hL : L ≠ 0) ... (δ₀ : ℝ) : summableSubseqAux ... δ₀ 0 = min δ₀ ((exists_delta_for_error_bound ... 0).choose) / 2`
- **What**: Base-case unfolding equation for the recursive sequence.
- **How**: `rfl` (definitional equality).
- **Hypotheses**: as above.
- **Uses from project**: `summableSubseqAux`, `exists_delta_for_error_bound`.
- **Used by**: `summableSubseqAux_pos`, `summableSubseqAux_lt_delta`.
- **Visibility**: public
- **Lines**: 261--266
- **Notes**: `rfl`.

### `lemma summableSubseqAux_succ`
- **Type**: `(hL : L ≠ 0) ... (δ₀ : ℝ) (n : ℕ) : let ε := summableSubseqAux ...; let δ := fun m => (exists_delta_for_error_bound ... m).choose; ε (n+1) = min (ε n / 2) (δ (n+1)) / 2`
- **What**: Step-case unfolding for the recursive sequence.
- **How**: `rfl`.
- **Hypotheses**: as above.
- **Uses from project**: `summableSubseqAux`, `exists_delta_for_error_bound`.
- **Used by**: `summableSubseqAux_pos`, `summableSubseqAux_halving`, `summableSubseqAux_lt_delta`.
- **Visibility**: public
- **Lines**: 268--273
- **Notes**: `rfl`.

### `lemma summableSubseqAux_pos`
- **Type**: `(hL : L ≠ 0) ... (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (n : ℕ) : 0 < summableSubseqAux ... δ₀ n`
- **What**: The sequence `ε(n)` is strictly positive for all `n`.
- **How**: Induction on `n`; base case uses `lt_min hδ₀_pos (hδ_pos 0)` and `positivity`; step case combines `ih` with min positivity.
- **Hypotheses**: `0 < δ₀`.
- **Uses from project**: `summableSubseqAux`, `summableSubseqAux_zero/_succ`, `exists_delta_for_error_bound` (via `.choose_spec.1`).
- **Used by**: `summableSubseqAux_halving`, `summableSubseqAux_lt_delta`, `summableSubseqAux_error_bound`, `exists_summable_subseq`, `summableSubseqAux_le_geometric`, `summableSubseqAux_tendsto_zero`.
- **Visibility**: public
- **Lines**: 275--292
- **Notes**: none.

### `lemma summableSubseqAux_halving`
- **Type**: `(hL : L ≠ 0) ... (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (n : ℕ) : summableSubseqAux ... δ₀ (n+1) ≤ summableSubseqAux ... δ₀ n / 2`
- **What**: Each step at least halves the sequence value.
- **How**: From `summableSubseqAux_succ`, bound `min(ε(n)/2, δ(n+1))/2 ≤ (ε(n)/2)/2 = ε(n)/4 ≤ ε(n)/2` using `summableSubseqAux_pos`.
- **Hypotheses**: `0 < δ₀`.
- **Uses from project**: `summableSubseqAux`, `summableSubseqAux_succ`, `summableSubseqAux_pos`, `exists_delta_for_error_bound`.
- **Used by**: `exists_summable_subseq`, `summableSubseqAux_le_geometric`.
- **Visibility**: public
- **Lines**: 294--308
- **Notes**: none.

### `lemma summableSubseqAux_lt_delta`
- **Type**: `(hL : L ≠ 0) ... (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (n : ℕ) : summableSubseqAux ... δ₀ n < (exists_delta_for_error_bound ... n).choose`
- **What**: `ε(n) < δ(n)`, ensuring the error bound holds at the chosen scale.
- **How**: Induction. Base: `min δ₀ (δ 0) / 2 ≤ δ(0)/2 < δ(0)`. Step: `min(ε(n)/2, δ(n+1))/2 ≤ δ(n+1)/2 < δ(n+1)` via `half_lt_self`.
- **Hypotheses**: `0 < δ₀`.
- **Uses from project**: `summableSubseqAux`, `summableSubseqAux_zero/_succ/_pos`, `exists_delta_for_error_bound`.
- **Used by**: `summableSubseqAux_error_bound`.
- **Visibility**: public
- **Lines**: 310--333
- **Notes**: none.

### `lemma summableSubseqAux_error_bound`
- **Type**: `(hL : L ≠ 0) ... (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (n : ℕ) : let ε_n := summableSubseqAux ... δ₀ n; ∀ t, 0 < |t - t₀| → |t - t₀| ≤ ε_n → ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ (1/2)^n / |t - t₀|`
- **What**: At the constructed `ε(n)`, the asymptotic remainder bound with constant `(1/2)^n` holds.
- **How**: Apply `(exists_delta_for_error_bound ... n).choose_spec.2` with `ε := ε_n`, using `summableSubseqAux_pos` and `summableSubseqAux_lt_delta`.
- **Hypotheses**: `0 < δ₀`.
- **Uses from project**: `summableSubseqAux`, `summableSubseqAux_pos`, `summableSubseqAux_lt_delta`, `exists_delta_for_error_bound`.
- **Used by**: `exists_summable_subseq`.
- **Visibility**: public
- **Lines**: 335--346
- **Notes**: none.

### `lemma exists_summable_subseq`
- **Type**: `(hL : L ≠ 0) ... (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) : ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ (∀ n, ε (n+1) ≤ ε n / 2) ∧ (∀ n, ∀ t, 0 < |t - t₀| → |t - t₀| ≤ ε n → ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ (1/2)^n / |t - t₀|)`
- **What**: Existence of a positive halving subsequence `ε(n)` with `(1/2)^n / |t-t₀|` remainder bound at scale `ε(n)`.
- **How**: Witness `summableSubseqAux`; positivity from `summableSubseqAux_pos`; halving from `summableSubseqAux_halving`; remainder bound from `summableSubseqAux_error_bound`.
- **Hypotheses**: `0 < δ₀`.
- **Uses from project**: `summableSubseqAux`, `summableSubseqAux_pos`, `summableSubseqAux_halving`, `summableSubseqAux_error_bound`.
- **Used by**: unused in file (terminal API).
- **Visibility**: public
- **Lines**: 348--357
- **Notes**: none.

### `lemma summableSubseqAux_le_geometric`
- **Type**: `(hL : L ≠ 0) ... (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (n : ℕ) : summableSubseqAux ... δ₀ n ≤ summableSubseqAux ... δ₀ 0 / 2^n`
- **What**: Geometric decay: `ε(n) ≤ ε(0)/2^n`.
- **How**: Induction; step uses `summableSubseqAux_halving` and `pow_succ`.
- **Hypotheses**: `0 < δ₀`.
- **Uses from project**: `summableSubseqAux`, `summableSubseqAux_halving`.
- **Used by**: `summableSubseqAux_tendsto_zero`.
- **Visibility**: public
- **Lines**: 360--375
- **Notes**: none.

### `lemma summableSubseqAux_tendsto_zero`
- **Type**: `(hL : L ≠ 0) ... (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) : Tendsto (summableSubseqAux ... δ₀) atTop (𝓝 0)`
- **What**: The constructed sequence `ε(n)` tends to 0.
- **How**: Squeeze between 0 and `ε(0)·(1/2)^n` using `summableSubseqAux_le_geometric` and `tendsto_pow_atTop_nhds_zero_of_lt_one`; conclude via `tendsto_of_tendsto_of_tendsto_of_le_of_le`.
- **Hypotheses**: `0 < δ₀`.
- **Uses from project**: `summableSubseqAux`, `summableSubseqAux_le_geometric`, `summableSubseqAux_pos`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 378--395
- **Notes**: none.

### `lemma cutoff_integrand_intervalIntegrable`
- **Type**: `{γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ} (hat₀ : t₀ ∈ Set.Ioo a b) (_hL : L ≠ 0) (hγ_meas : Measurable γ) (hγ_cont_deriv : ContinuousOn (deriv γ) (Set.Icc a b)) (ε : ℝ) (hε_pos : 0 < ε) : IntervalIntegrable (fun t => if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0) volume a b`
- **What**: The cutoff integrand `1_{ε < ‖γ(t)-γ(t₀)‖} · (γ(t)-γ(t₀))⁻¹ · γ'(t)` is interval-integrable on `[a,b]`.
- **How**: Bound deriv on `Icc a b` (compact + continuous, via `IsCompact.exists_isMaxOn`); on the cutoff set `‖(γ-γ₀)⁻¹‖ ≤ 1/ε`, so the integrand is bounded by `M/ε`. Use `MeasureTheory.IntegrableOn.of_bound` with `AEStronglyMeasurable.indicator` and `measure_Ioc_lt_top`. ~45 lines.
- **Hypotheses**: `t₀ ∈ (a,b)`; `γ` measurable; `deriv γ` continuous on `Icc a b`; `0 < ε`.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 398--441
- **Notes**: >30 lines.

### `lemma cutoff_diff_eq_annulus_integral`
- **Type**: `{f : ℝ → ℂ} {γ : ℝ → ℂ} {a b t₀ : ℝ} {ε₁ ε₂ : ℝ} (h_le : ε₁ ≤ ε₂) (h_int₁ : IntervalIntegrable ...) (h_int₂ : ...) : (∫ t in a..b, if ε₁ < ‖γ t - γ t₀‖ then f t else 0) - (∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ then f t else 0) = ∫ t in a..b, if ε₁ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₂ then f t else 0`
- **What**: Difference of cutoff integrals at two scales equals the integral over the annulus `ε₁ < ‖γ - γ₀‖ ≤ ε₂`.
- **How**: Combine integrals via `intervalIntegral.integral_sub` and `congr` on the integrand; case-split on whether each side condition holds.
- **Hypotheses**: `ε₁ ≤ ε₂`; integrability at both scales.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 444--462
- **Notes**: none.

### `lemma pv_singular_cancels`
- **Type**: `(t₀ ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) (hεδ : ε < δ) : (∫ t in (t₀ - δ)..(t₀ - ε), (↑(t - t₀) : ℂ)⁻¹) + (∫ t in (t₀ + ε)..(t₀ + δ), (↑(t - t₀) : ℂ)⁻¹) = 0`
- **What**: Symmetric cancellation of the singular `1/(t-t₀)` integral over `[t₀-δ, t₀-ε] ∪ [t₀+ε, t₀+δ]`.
- **How**: Direct from `integral_inv_symm`.
- **Hypotheses**: `0 < ε < δ`.
- **Uses from project**: `integral_inv_symm`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 465--468
- **Notes**: none.

### `lemma remainder_step_bound`
- **Type**: `{r : ℝ → ℂ} {t₀ ε η : ℝ} (hε_pos : 0 < ε) (_hη_pos : 0 < η) (hr_bound : ∀ t, ε/2 < |t - t₀| → |t - t₀| < ε → ‖r t‖ ≤ η / |t - t₀|) : ‖∫ t in (t₀ - ε)..(t₀ - ε/2), r t‖ + ‖∫ t in (t₀ + ε/2)..(t₀ + ε), r t‖ ≤ 2 * η * Real.log 2`
- **What**: Dyadic step bound on `[ε/2, ε]` matching `step_bound_with_eta` but with the bound restricted to the strict-open annulus.
- **How**: `remainder_annulus_bound` with `c₁ = ε/2`, `c₂ = ε`; simplify `log(ε/(ε/2)) = log 2`.
- **Hypotheses**: as above.
- **Uses from project**: `remainder_annulus_bound`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 471--478
- **Notes**: none.

### `lemma remainder_bounded_ratio`
- **Type**: `{r : ℝ → ℂ} {t₀ ε₁ ε₂ η K : ℝ} (hε₁_pos : 0 < ε₁) (hε₁₂ : ε₁ < ε₂) (hη_pos : 0 < η) (_hK : 1 < K) (h_ratio : ε₂/ε₁ ≤ K) (hr_bound : ∀ t, ε₁ < |t - t₀| → |t - t₀| < ε₂ → ‖r t‖ ≤ η / |t - t₀|) : ‖∫ t in (t₀ - ε₂)..(t₀ - ε₁), r t‖ + ‖∫ t in (t₀ + ε₁)..(t₀ + ε₂), r t‖ ≤ 2 * η * Real.log K`
- **What**: Generalized annulus bound: if `ε₂/ε₁ ≤ K`, the symmetric annulus integral is at most `2η · log K`.
- **How**: `remainder_annulus_bound` gives `2η · log(ε₂/ε₁)`; monotonicity `log(ε₂/ε₁) ≤ log K` via `Real.log_le_log`.
- **Hypotheses**: as above.
- **Uses from project**: `remainder_annulus_bound`.
- **Used by**: `remainder_dyadic_step`.
- **Visibility**: public
- **Lines**: 481--491
- **Notes**: none.

### `lemma remainder_dyadic_step`
- **Type**: `{r : ℝ → ℂ} {t₀ ε₀ η : ℝ} (n : ℕ) (hε₀_pos : 0 < ε₀) (hη_pos : 0 < η) (hr_bound : ∀ t, 0 < |t - t₀| → |t - t₀| < ε₀ → ‖r t‖ ≤ η / |t - t₀|) : ‖∫ t in (t₀ - ε₀/2^n)..(t₀ - ε₀/2^(n+1)), r t‖ + ‖∫ t in (t₀ + ε₀/2^(n+1))..(t₀ + ε₀/2^n), r t‖ ≤ 2 * η * Real.log 2`
- **What**: At dyadic step `n`, the remainder integral over the corresponding shells is bounded by `2η · log 2`.
- **How**: Compute `(ε₀/2^n)/(ε₀/2^(n+1)) = 2` and apply `remainder_bounded_ratio` with `K = 2`.
- **Hypotheses**: as above.
- **Uses from project**: `remainder_bounded_ratio`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 494--523
- **Notes**: none.

### `lemma pv_dyadic_step_O_eps`
- **Type**: `{r : ℝ → ℂ} {t₀ δ₀ C : ℝ} (n : ℕ) (hδ₀_pos : 0 < δ₀) (_hC_pos : 0 < C) (hr_bounded : ∀ t, 0 < |t - t₀| → |t - t₀| ≤ δ₀ → ‖r t‖ ≤ C) : let ε_n := δ₀/2^n; ‖∫ t in (t₀ - ε_n)..(t₀ - ε_n/2), r t‖ + ‖∫ t in (t₀ + ε_n/2)..(t₀ + ε_n), r t‖ ≤ C * ε_n`
- **What**: With remainder bounded uniformly by `C`, the dyadic step contributes `O(ε_n) = C·ε_n`.
- **How**: Same shape as `remainder_integral_O_eps`: bound each piece by `C · (ε_n/2)`, sum to `C · ε_n`.
- **Hypotheses**: as above.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 526--563
- **Notes**: >30 lines.

### `lemma cauchySeq_pv_dyadic`
- **Type**: `{I : ℝ → ℂ} {δ₀ C : ℝ} (_hδ₀_pos : 0 < δ₀) (_hC_pos : 0 < C) (h_step : ∀ n, ‖I (δ₀/2^(n+1)) - I (δ₀/2^n)‖ ≤ C * δ₀ / 2^n) : CauchySeq (fun n => I (δ₀/2^n))`
- **What**: If consecutive cutoff integrals at dyadic scales differ by at most `C·δ₀/2^n`, the dyadic sequence is Cauchy.
- **How**: `cauchySeq_of_le_geometric` with ratio `1/2` and bound `C·δ₀`; rewrite `dist` as norm and `C·δ₀/2^n = C·δ₀ · (1/2)^n`.
- **Hypotheses**: geometric step bound.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 566--576
- **Notes**: none.

### `lemma t_bound_from_gamma_annulus`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {δ₁ ε : ℝ} (hL : L ≠ 0) (_hε_pos : 0 < ε) (h_lower : ∀ t, 0 < |t-t₀| → |t-t₀| < δ₁ → ‖γ t - γ t₀‖ ≥ (‖L‖/2) · |t-t₀|) (t : ℝ) (ht_pos : 0 < |t-t₀|) (ht_lt : |t-t₀| < δ₁) (hγ_bound : ‖γ t - γ t₀‖ ≤ ε) : |t-t₀| ≤ 2·ε/‖L‖`
- **What**: From a lower bound `‖γ(t)-γ(t₀)‖ ≥ (‖L‖/2)|t-t₀|` and an upper bound `‖γ(t)-γ(t₀)‖ ≤ ε`, we get `|t-t₀| ≤ 2ε/‖L‖`.
- **How**: Calc chain dividing through by `‖L‖ > 0` via `div_le_div_of_nonneg_right`.
- **Hypotheses**: as above.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 579--595
- **Notes**: none.

### `lemma integrand_bound_on_annulus`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {C δ₀ : ℝ} (hr_bounded : ∀ t, 0 < |t-t₀| → |t-t₀| < δ₀ → ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t-t₀))⁻¹‖ ≤ C) (t : ℝ) (ht_pos : 0 < |t-t₀|) (ht_lt : |t-t₀| < δ₀) : ‖(γ t - γ t₀)⁻¹ * deriv γ t‖ ≤ |t-t₀|⁻¹ + C`
- **What**: Triangle-inequality bound for the integrand `|integrand| ≤ |1/(t-t₀)| + C` on the punctured annulus when the difference is bounded by `C`.
- **How**: Use `norm_sub_norm_le` and `norm_inv` with `Complex.norm_real`.
- **Hypotheses**: as above.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 598--611
- **Notes**: none.

### `lemma annulus_implies_t_local`
- **Type**: `{γ : ℝ → ℂ} {a b t₀ : ℝ} {ε₁ δ₀ δ₁ : ℝ} (h_localize : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₀ δ₁) (t : ℝ) (ht_ab : t ∈ Set.Icc a b) (hγ_bound : ‖γ t - γ t₀‖ ≤ ε₁) : |t-t₀| < δ₀ ∧ |t-t₀| < δ₁`
- **What**: If the localization hypothesis bounds `|t-t₀| < min(δ₀,δ₁)`, then both individual bounds `< δ₀` and `< δ₁` follow.
- **How**: `min_le_left`/`min_le_right` with `lt_of_lt_of_le`.
- **Hypotheses**: as above.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 614--619
- **Notes**: none.

### `lemma exists_dyadic_bracket`
- **Type**: `{δ ε : ℝ} (hδ_pos : 0 < δ) (hε_pos : 0 < ε) (hε_le : ε ≤ δ) : ∃ n : ℕ, δ/2^(n+1) < ε ∧ ε ≤ δ/2^n`
- **What**: For ε ∈ (0, δ], find a dyadic shell `n` with `δ/2^(n+1) < ε ≤ δ/2^n`.
- **How**: Since `δ/2^n → 0` (proved using `tendsto_pow_atTop_atTop_of_one_lt` and `tendsto_inv_atTop_zero`), find `N` with `δ/2^N < ε`; take the minimum `m = Nat.find` such that `δ/2^m < ε`. Case `m = 0` is ruled out (contradicts `ε ≤ δ`); otherwise let `n + 1 = m`.
- **Hypotheses**: `0 < δ`, `0 < ε ≤ δ`.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 622--654
- **Notes**: >30 lines.

### `lemma telescoping_sum_bound`
- **Type**: `{X : Type*} [SeminormedAddCommGroup X] {I : ℕ → X} {K δ : ℝ} (_hK_pos : 0 < K) (_hδ_pos : 0 < δ) (h_step : ∀ n, ‖I (n+1) - I n‖ ≤ K · δ / 2^n) (N : ℕ) : ∀ M, M > N → ‖I M - I N‖ ≤ 2·K·δ/2^N - 2·K·δ/2^M`
- **What**: Telescoping bound for differences of a sequence with geometrically-decaying step bound.
- **How**: Write `M = N + d + 1`, induct on `d`. Base `d = 0`: from `h_step N` and `2·K·δ/2^N - 2·K·δ/2^(N+1) = K·δ/2^N`. Step: split as `(I(N+d+2)-I(N+d+1)) + (I(N+d+1)-I N)`, use triangle inequality and IH.
- **Hypotheses**: step bound `K·δ/2^n`.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 657--697
- **Notes**: >30 lines.

---

## File Summary

- **Total declarations**: 26 (1 `def`, 1 `abbrev`, 24 lemmas).
- **Key API (public, downstream-facing)**:
  - Convergence rate primitives: `remainder_integral_O_eps`, `integral_inv_symm`, `remainder_annulus_bound`, `step_bound_with_eta`, `remainder_step_bound`, `remainder_bounded_ratio`, `remainder_dyadic_step`, `pv_dyadic_step_O_eps`.
  - Subsequence construction: `exists_summable_subseq` (top-level) supported by `summableSubseqAux` and its 7 unfolding/property lemmas, `exists_eta_delta`, `error_at_smaller_scale`, `exists_delta_for_error_bound`, `summableSubseqAux_le_geometric`, `summableSubseqAux_tendsto_zero`.
  - Integrability / Cauchy / bracket: `cutoff_integrand_intervalIntegrable`, `cutoff_diff_eq_annulus_integral`, `pv_singular_cancels`, `cauchySeq_pv_dyadic`, `t_bound_from_gamma_annulus`, `integrand_bound_on_annulus`, `annulus_implies_t_local`, `exists_dyadic_bracket`, `telescoping_sum_bound`.
  - The `abbrev` `cutoffIntegral` defines the documented `I(ε)`.
- **Unused in file**: many top-level lemmas are exported (downstream usage): `remainder_integral_O_eps`, `step_bound_with_eta`, `exists_summable_subseq`, `summableSubseqAux_tendsto_zero`, `cutoff_integrand_intervalIntegrable`, `cutoff_diff_eq_annulus_integral`, `pv_singular_cancels`, `remainder_step_bound`, `remainder_dyadic_step`, `pv_dyadic_step_O_eps`, `cauchySeq_pv_dyadic`, `t_bound_from_gamma_annulus`, `integrand_bound_on_annulus`, `annulus_implies_t_local`, `exists_dyadic_bracket`, `telescoping_sum_bound`, `cutoffIntegral`.
- **Sorries**: none.
- **set_options**: none.
- **Long proofs (>30 lines)**: `remainder_annulus_bound` (~120), `cutoff_integrand_intervalIntegrable` (~43), `pv_dyadic_step_O_eps` (~37), `exists_dyadic_bracket` (~32), `telescoping_sum_bound` (~40).
- **One-paragraph purpose**: Provides the dyadic-step convergence infrastructure that proves Cauchy-principal-value integrals converge along curves of class `C¹` past a singularity. It packages four kinds of ingredients: (1) integral bounds for remainder terms on symmetric annuli `[t₀-c₂,t₀-c₁] ∪ [t₀+c₁,t₀+c₂]` (sharp `O(log)` and `O(ε)` versions); (2) symmetry-based cancellation of the singular `1/(t-t₀)` piece; (3) a recursively-defined dyadic subsequence `ε(n)` of scales for which the asymptotic remainder bound `(1/2)^n / |t-t₀|` holds (so that `2η·log 2` step bounds sum geometrically); (4) Cauchyness, dyadic bracketing, t-space localization, and telescoping bounds packaged for downstream use by the generalized residue theory. The asymptotic input comes from `GammaAnalysis` (`integrand_asymptotic`).
