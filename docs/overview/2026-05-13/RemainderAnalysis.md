# Inventory: GeneralizedResidueTheory/PVInfrastructure/RemainderAnalysis.lean

### `lemma contDiffAt_one_deriv_of_contDiffAt_two`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} (hγ_C2 : ContDiffAt ℝ 2 γ t₀) : ContDiffAt ℝ 1 (deriv γ) t₀`
- **What**: If `γ` is C² at `t₀`, then `deriv γ` is C¹ at `t₀`.
- **How**: Express `2 = 1 + 1`; use `ContDiffAt.fderiv_right_succ` to get a C¹ map into linear maps, apply at the constant `1`; rewrite `(fderiv ℝ γ t) 1 = deriv γ t` via `fderiv_apply_one_eq_deriv`.
- **Hypotheses**: `ContDiffAt ℝ 2 γ t₀`.
- **Uses from project**: []
- **Used by**: `deriv_deviation_bound_of_C2`.
- **Visibility**: public
- **Lines**: 31–41
- **Notes**: none

### `lemma deriv_deviation_bound_of_C2`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L) : ∃ K δ, 0 < δ ∧ ∀ t, |t - t₀| < δ → ‖deriv γ t - L‖ ≤ K * |t - t₀|`
- **What**: For `γ` C² at `t₀` with `deriv γ t₀ = L`, deriv γ is Lipschitz around `t₀` with constant `K` relative to `L`.
- **How**: Apply `ContDiffAt.exists_lipschitzOnWith` to `contDiffAt_one_deriv_of_contDiffAt_two hγ_C2` to obtain Lipschitz on a nhd `s`; convert to a metric ball via `Metric.mem_nhds_iff`. Use `LipschitzOnWith.dist_le_mul` and rewrite via `dist_eq_norm`, `hγ_deriv`, `Real.dist_eq`.
- **Hypotheses**: `ContDiffAt ℝ 2 γ t₀`, `deriv γ t₀ = L`.
- **Uses from project**: `contDiffAt_one_deriv_of_contDiffAt_two`.
- **Used by**: `quadratic_approx_of_contDiffAt_two`, `numerator_quadratic_bound`.
- **Visibility**: public
- **Lines**: 44–57
- **Notes**: none

### `lemma quadratic_approx_of_contDiffAt_two`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hγ_C2) (hγ_deriv) : ∃ K δ, 0 < δ ∧ 0 < K ∧ ∀ t, |t - t₀| < δ → ‖γ t - γ t₀ - (t-t₀) • L‖ ≤ K * |t - t₀|^2`
- **What**: Quadratic Taylor approximation: the deviation from the first-order Taylor polynomial is `O((t-t₀)²)`.
- **How**: From `deriv_deviation_bound_of_C2`, get Lipschitz constant `M` and radius `δ₁`. Build a smaller `δ` from `δ₁` and a `δ₂` where γ is differentiable (using `ContDiffAt.eventually`). Set `K = M + 1`, show `0 ≤ M` by contradiction using positivity of `‖deriv γ t - L‖`. For `t ≠ t₀`, define `h(s) = γ(s) - γ(t₀) - (s-t₀)•L`, show `h(t₀)=0`, `deriv h s = deriv γ s - L` on `uIcc t₀ t` (via `deriv_smul_const`, `deriv_const`, `deriv_sub`), bound `‖deriv h s‖ ≤ M·|t-t₀|`, then apply `Convex.norm_image_sub_le_of_norm_deriv_le` (with `Set.abs_sub_left_of_mem_uIcc`). (~88 lines.)
- **Hypotheses**: `ContDiffAt ℝ 2 γ t₀`, `deriv γ t₀ = L`.
- **Uses from project**: `deriv_deviation_bound_of_C2`.
- **Used by**: `bounded_slope_deviation_of_contDiffAt_two`, `numerator_quadratic_bound`.
- **Visibility**: public
- **Lines**: 60–193
- **Notes**: >30 lines

### `lemma bounded_slope_deviation_of_contDiffAt_two`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hγ_C2) (hγ_deriv) : ∃ K δ, 0 < δ ∧ 0 < K ∧ ∀ t, 0 < |t-t₀| → |t-t₀| < δ → ‖(γ t - γ t₀)/↑(t-t₀) - L‖ ≤ K * |t-t₀|`
- **What**: The slope `(γ t − γ t₀)/(t − t₀)` deviates from `L` by `O(|t − t₀|)`.
- **How**: Take the quadratic-approx constants from `quadratic_approx_of_contDiffAt_two`; rewrite the slope deviation as `(γ t - γ t₀ - (t-t₀)•L)/↑(t-t₀)` via `field_simp` and `Complex.real_smul`. Divide the quadratic norm bound by `|t-t₀|`. (~14 lines.)
- **Hypotheses**: `ContDiffAt ℝ 2 γ t₀`, `deriv γ t₀ = L`.
- **Uses from project**: `quadratic_approx_of_contDiffAt_two`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 196–218
- **Notes**: >10 lines

### `lemma numerator_quadratic_bound`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hγ_C2) (hγ_deriv) : ∃ K δ, 0 < δ ∧ ∀ t, |t-t₀| < δ → ‖↑(t-t₀) * deriv γ t - (γ t - γ t₀)‖ ≤ K * |t-t₀|²`
- **What**: Numerator of the chord-vs-tangent discrepancy is `O((t-t₀)²)`.
- **How**: Use `quadratic_approx_of_contDiffAt_two` for `K₁` bound and `deriv_deviation_bound_of_C2` for `K₂` bound, with smaller δ. Use identity `↑(t-t₀)·deriv γ t − (γ t − γ t₀) = ↑(t-t₀)·(deriv γ t − L) − (γ t − γ t₀ − (t-t₀)•L)` (via `Complex.real_smul`, `ring`). Apply triangle inequality (`norm_sub_le`); bound first term by `|t-t₀|·(K₂·|t-t₀|)` and second by `K₁·|t-t₀|²`. Combine into `(K₁+K₂+1)·|t-t₀|²`. (~26 lines.)
- **Hypotheses**: `ContDiffAt ℝ 2 γ t₀`, `deriv γ t₀ = L`.
- **Uses from project**: `quadratic_approx_of_contDiffAt_two`, `deriv_deviation_bound_of_C2`.
- **Used by**: `remainder_bounded_of_C2`.
- **Visibility**: public
- **Lines**: 221–267
- **Notes**: >10 lines

### `lemma remainder_bounded_of_C2`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0) (hγ_C2) (hγ_deriv) : ∃ C δ, 0 < δ ∧ ∀ t, 0 < |t-t₀| → |t-t₀| < δ → ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t-t₀))⁻¹‖ ≤ C`
- **What**: The PV-integrand remainder `r(t) = (γ-γ₀)⁻¹·γ' − (t-t₀)⁻¹` is bounded by a constant near `t₀`.
- **How**: Establish `HasDerivAt γ L t₀` via differentiability of C². Get linear lower bound `(‖L‖/2)·|t-t₀| ≤ ‖γ t − γ t₀‖` from `gamma_lower_bound_of_hasDerivAt`. Numerator bound `K·|t-t₀|²` from `numerator_quadratic_bound`. Show `γ t - γ t₀ ≠ 0`. Use identity `(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t-t₀))⁻¹ = (↑(t-t₀)·deriv γ t − (γ t − γ t₀))/((γ t − γ t₀)·↑(t-t₀))` (via `field_simp`). Apply `div_le_div₀` with denominator lower bound `(‖L‖/2)·|t-t₀|²` to get final `2K/‖L‖` bound. (~30 lines.)
- **Hypotheses**: `L ≠ 0`, `ContDiffAt ℝ 2 γ t₀`, `deriv γ t₀ = L`.
- **Uses from project**: `numerator_quadratic_bound`, `gamma_lower_bound_of_hasDerivAt` (imported from `GammaAnalysis`).
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 270–334
- **Notes**: >30 lines

## File Summary
- 6 declarations, all public, forming a chain culminating in the main `remainder_bounded_of_C2` result.
- Chain: `contDiffAt_one_deriv_of_contDiffAt_two` (C² ⇒ C¹ on `deriv`) → `deriv_deviation_bound_of_C2` (Lipschitz of `deriv γ`) → `quadratic_approx_of_contDiffAt_two` (Taylor 2nd-order remainder bound) → `numerator_quadratic_bound` (chord-vs-tangent numerator is `O(Δt²)`) → `remainder_bounded_of_C2` (PV remainder is `O(1)`).
- Side branch: `bounded_slope_deviation_of_contDiffAt_two` derives slope bound but is unused in file (exposed to clients).
- All sorry-free; no axioms; no `set_option`; file in `noncomputable section`.
- The big proofs all rely on standard MVT-style results (`Convex.norm_image_sub_le_of_norm_deriv_le`) and `field_simp`/`ring` for algebraic identities.
