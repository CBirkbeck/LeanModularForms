# Inventory: LocalCutoffs.lean

### `theorem strict_mono_inverse_exists_local`
- **Type**: `(f : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (hf₀ : f 0 = 0) (hf_strict : StrictMonoOn f (Set.Icc 0 r)) (hf_cont : ContinuousOn f (Set.Icc 0 r)) : ∀ ε ∈ Set.Ioo (0 : ℝ) (f r), ∃! τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) r ∧ f τ = ε`
- **What**: Intermediate value theorem with uniqueness: for `ε ∈ (0, f r)`, the strictly monotone `f` has a unique preimage `τ ∈ (0, r)`.
- **How**: Uses `intermediate_value_Ioo` to get existence and `StrictMonoOn.injOn` for uniqueness.
- **Hypotheses**: `f` continuous and strictly monotone on `[0, r]`, with `f 0 = 0`.
- **Uses from project**: []
- **Used by**: `exists_right_cutoff_local`, `exists_left_cutoff_local`
- **Visibility**: private
- **Lines**: 67-82

### `theorem exists_right_cutoff_local`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ r : ℝ} (h_window_pos : 0 < r) (h_window_Icc : Icc (t₀ - r) (t₀ + r) ⊆ Icc 0 1) (h_at : γ.extend t₀ = s) (h_local_unique : ∀ t ∈ Icc (t₀ - r) (t₀ + r), γ.extend t = s → t = t₀) : ∃ (δ_right : ℝ → ℝ) (threshold : ℝ), 0 < threshold ∧ [pos] ∧ [< r] ∧ [exit-norm = ε] ∧ [far bound on (t₀+δ_R(ε), t₀+r]] ∧ [near bound on [t₀, t₀+δ_R(ε)]]`
- **What**: Localized right exit-time cutoff: constructs `δ_right : ℝ → ℝ` and a threshold under local uniqueness on the window, giving asymmetric far/near bounds inside `[t₀, t₀+r]`.
- **How**: Extracts the right derivative `L ≠ 0`, applies `norm_sub_strictMonoOn_right` for strict monotonicity of `‖γ-s‖` on a small `r₀`, sets `r_eff := min r₀ (r/2)`, builds the inverse via `strict_mono_inverse_exists_local`, and combines with `multi_pole_local_far_bound` for the far bound on `[t₀+r_eff, t₀+r]`.
- **Hypotheses**: Window `[t₀-r, t₀+r] ⊆ [0,1]`, local uniqueness on the window, `γ(t₀) = s`.
- **Uses from project**: `exists_right_deriv_limit`, `eventually_differentiable_right`, `norm_sub_strictMonoOn_right`, `multi_pole_local_far_bound`, `strict_mono_inverse_exists_local`
- **Used by**: `localDerivedCutoffs`
- **Visibility**: private
- **Lines**: 95-263
- **Notes**: proof >30 lines (>150 lines), uses classical

### `theorem exists_left_cutoff_local`
- **Type**: Symmetric signature to `exists_right_cutoff_local` for the left side; produces `δ_left : ℝ → ℝ` and threshold with mirror-image bounds.
- **What**: Localized left exit-time cutoff analogous to `exists_right_cutoff_local`.
- **How**: Same template using `norm_sub_strictAntiOn_left` for strict anti-monotonicity (norm decreases approaching `t₀` from the left, so `f(τ) := ‖γ(t₀-τ)-s‖` is strictly monotone increasing in `τ`).
- **Hypotheses**: Same as the right version.
- **Uses from project**: `exists_left_deriv_limit`, `eventually_differentiable_left`, `norm_sub_strictAntiOn_left`, `multi_pole_local_far_bound`, `strict_mono_inverse_exists_local`
- **Used by**: `localDerivedCutoffs`
- **Visibility**: private
- **Lines**: 271-436
- **Notes**: proof >30 lines (>160 lines), uses classical

### `structure LocalDerivedCutoffs`
- **Type**: `(γ : ClosedPwC1Immersion x) (s : ℂ) (t₀ r : ℝ)` — record bundling `δ_left`, `δ_right`, `threshold`, positivity proofs `hthresh`, `hδ_*_pos`, `hδ_*_lt`, exit-time equalities `h_exit_left`, `h_exit_right`, far bounds `h_far_left`, `h_far_right`, near bounds `h_near_left`, `h_near_right`.
- **What**: Per-crossing local cutoff bundle: packages both `δ_left` and `δ_right` together with all asymmetric far/near bounds on a window `[t₀-r, t₀+r]`, replacing the global `DerivedAsymmetricCutoffs`.
- **How**: Plain Lean structure declaration.
- **Hypotheses**: None — pure data type.
- **Uses from project**: []
- **Used by**: `localDerivedCutoffs`, `LocalDerivedCutoffs.δ_right_tendsto_zero`, `LocalDerivedCutoffs.δ_left_tendsto_zero`, `perCrossing_window_integral_tendsto_exact`
- **Visibility**: public
- **Lines**: 448-475

### `def localDerivedCutoffs`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ r : ℝ} (h_window_pos : 0 < r) (h_window_Icc : ...) (h_at : ...) (h_local_unique : ...) : LocalDerivedCutoffs γ s t₀ r`
- **What**: Noncomputable builder for `LocalDerivedCutoffs` from a single-crossing local geometric data: combines the existence outputs of `exists_right_cutoff_local` and `exists_left_cutoff_local` into the bundle, taking the minimum of the two thresholds.
- **How**: Calls both existence theorems, destructures the `Classical.choose`/`choose_spec` chains, and packages into the record with min-threshold and the appropriate `min_le_left/right` chained inequalities.
- **Hypotheses**: As in `exists_*_cutoff_local`.
- **Uses from project**: `exists_right_cutoff_local`, `exists_left_cutoff_local`
- **Used by**: `perCrossing_window_integral_tendsto_exact`
- **Visibility**: public
- **Lines**: 485-528
- **Notes**: proof >30 lines, noncomputable

### `theorem exists_chord_slitPlane_radius_right`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Set.Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) : ∃ r > 0, ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r → (γ b - s) / (γ a - s) ∈ Complex.slitPlane`
- **What**: Pure repackaging of `exists_slitPlane_chord_quotient_right` — provides a positive radius below which all right-side chord quotients lie in the slit plane.
- **How**: One-line forwarding to `exists_slitPlane_chord_quotient_right`.
- **Hypotheses**: Right derivative `L ≠ 0`.
- **Uses from project**: `exists_slitPlane_chord_quotient_right`
- **Used by**: `cpvFullSetup_local`
- **Visibility**: public
- **Lines**: 588-594

### `theorem exists_chord_slitPlane_radius_left`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Set.Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) : ∃ r > 0, ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ → (γ b - s) / (γ a - s) ∈ Complex.slitPlane`
- **What**: Symmetric repackaging of `exists_slitPlane_chord_quotient_left_forward`.
- **How**: One-line forwarding call.
- **Hypotheses**: Left derivative `L ≠ 0`.
- **Uses from project**: `exists_slitPlane_chord_quotient_left_forward`
- **Used by**: `cpvFullSetup_local`
- **Visibility**: public
- **Lines**: 602-608

### `theorem exists_chord_div_endpoint_slitPlane_right`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Set.Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) : ∃ r > 0, ∀ r', 0 < r' → r' ≤ r → (γ (t₀ + r') - s) / L ∈ Complex.slitPlane`
- **What**: Existence of a radius `r > 0` such that the boundary chord-to-tangent quotient `(γ(t₀+r') - s)/L` lies in the slit plane for all `0 < r' ≤ r`.
- **How**: Uses `exists_normalized_chord_right` with `ρ = 1/4` to obtain `‖normalized chord - 1‖ ≤ 1/4`, giving `Re ≥ 3/4`; rewrites `(γ(t₀+r')-s)/L = r' · (normalized chord)` and concludes via `Complex.mem_slitPlane_iff` plus positive multiplication.
- **Hypotheses**: Right derivative `L ≠ 0`.
- **Uses from project**: `exists_normalized_chord_right`
- **Used by**: `cpvFullSetup_local`
- **Visibility**: public
- **Lines**: 619-657
- **Notes**: proof >30 lines

### `theorem exists_chord_div_endpoint_slitPlane_left`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Set.Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) : ∃ r > 0, ∀ r', 0 < r' → r' ≤ r → γ (t₀ - r') ≠ s → (-L) / (γ (t₀ - r') - s) ∈ Complex.slitPlane`
- **What**: Left-side boundary slit-plane radius existence: the negated quotient `-L/(γ(t₀-r')-s)` lies in the slit plane for all `0 < r' ≤ r` provided `γ(t₀-r') ≠ s`.
- **How**: Uses `exists_normalized_chord_left` with `ρ = 1/4`; observes `‖-q - 1‖ ≤ 1/4` where `q = (γ(t₀-r')-s)/(L·r')`; derives `‖q‖ ≥ 3/4`, then `‖-1/q - 1‖ ≤ 1/3`, so `Re(-1/q) ≥ 2/3`; multiplies by `1/r' > 0` to obtain the slit-plane condition.
- **Hypotheses**: Left derivative `L ≠ 0`, plus user-supplied `γ(t₀-r') ≠ s`.
- **Uses from project**: `exists_normalized_chord_left`
- **Used by**: `cpvFullSetup_local`
- **Visibility**: public
- **Lines**: 668-737
- **Notes**: proof >30 lines

### `theorem oneSided_deriv_setup`
- **Type**: `(γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo 0 1) : ∃ (L_R L_L : ℂ), L_R ≠ 0 ∧ L_L ≠ 0 ∧ HasDerivWithinAt γ.extend L_R (Set.Ioi t₀) t₀ ∧ HasDerivWithinAt γ.extend L_L (Set.Iio t₀) t₀`
- **What**: Radius-independent setup extracting nonzero one-sided derivatives `L_R, L_L` and the corresponding `HasDerivWithinAt` witnesses at an interior crossing.
- **How**: Calls `exists_right_deriv_limit` and `exists_left_deriv_limit` for the limits, plus `eventually_differentiable_right/left` to obtain differentiable neighborhoods, then converts to `HasDerivWithinAt` via `hasDerivWithinAt_Ioi_iff_Ici` (and the `Iio/Iic` variant).
- **Hypotheses**: Interior `t₀ ∈ Ioo 0 1`.
- **Uses from project**: `exists_right_deriv_limit`, `exists_left_deriv_limit`, `eventually_differentiable_right`, `eventually_differentiable_left`
- **Used by**: `cpvFullSetup_local`
- **Visibility**: public
- **Lines**: 744-776
- **Notes**: proof >30 lines, uses classical

### `theorem cpvFullSetup_local_exact`
- **Type**: Conjunction repackaging — given `γ`, `t₀ ∈ Ioo 0 1`, `γ(t₀) = s`, fixed radius `r > 0` with window contained in `[0,1]`, local uniqueness, nonzero derivatives `L_R, L_L`, derivative witnesses, and four slit-plane preconditions (two chord-quotient + two boundary), returns the same conjunction packaged as the existential body.
- **What**: Local geometric setup in exact-radius form: takes slit-plane chord-quotient and boundary slit-plane data at a fixed (user-chosen) radius `r > 0` as hypotheses, rather than internally shrinking the radius.
- **How**: Pure repackaging — `exact ⟨...⟩` constructor.
- **Hypotheses**: Numerous documentation parameters plus the derivative and slit-plane witnesses (all explicit).
- **Uses from project**: []
- **Used by**: unused in file (intended for multi-crossing aggregation external callers)
- **Visibility**: public
- **Lines**: 801-848

### `theorem cpvFullSetup_local`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo 0 1) (h_at : ...) {r₀ : ℝ} (hr₀_pos : 0 < r₀) (_h_window_in_unit : ...) (h_local_unique : ...) : ∃ (L_R L_L : ℂ) (r : ℝ), L_R ≠ 0 ∧ L_L ≠ 0 ∧ 0 < r ∧ r ≤ r₀ ∧ [derivs] ∧ [slit-plane chord R/L] ∧ [boundary R/L slit-plane]`
- **What**: Legacy local geometric setup at a crossing, returning a shrunken output radius `r ≤ r₀`. Now a thin wrapper around `cpvFullSetup_local_exact`.
- **How**: Calls `oneSided_deriv_setup`, then the four threshold-radius lemmas (`exists_chord_slitPlane_radius_right/left`, `exists_chord_div_endpoint_slitPlane_right/left`); takes `r = min` of all four with `r₀`; derives the slit-plane conditions at the new `r`; assembles into the conjunction.
- **Hypotheses**: Interior `t₀`, window contained in `[0,1]`, local uniqueness on `[t₀-r₀, t₀+r₀]`.
- **Uses from project**: `oneSided_deriv_setup`, `exists_chord_slitPlane_radius_right`, `exists_chord_slitPlane_radius_left`, `exists_chord_div_endpoint_slitPlane_right`, `exists_chord_div_endpoint_slitPlane_left`
- **Used by**: `perCrossing_window_integral_tendsto`
- **Visibility**: private
- **Lines**: 856-923
- **Notes**: proof >30 lines, uses classical

### `theorem right_annular_log_diff_local`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ} {L_right : ℂ} (_hL_right_ne : L_right ≠ 0) (_h_deriv_right : ...) (_h_at : ...) {r δ_R : ℝ} (hδ_R_pos : 0 < δ_R) (hδ_R_lt : δ_R < r) (_hr_pos : 0 < r) (h_window_in_unit : ...) (h_slit_R : ...) (h_local_unique : ...) : ∫ t in (t₀ + δ_R)..(t₀ + r), deriv γ.extend t / (γ.extend t - s) = Complex.log ((γ.extend (t₀ + r) - s) / (γ.extend (t₀ + δ_R) - s))`
- **What**: Local-uniqueness version of `right_annular_log_diff`: the FTC log-difference identity on the right annular piece under local (not global) uniqueness on the window.
- **How**: Sets `a := t₀ + δ_R, b := t₀ + r`, derives `γ(a) ≠ s` via local uniqueness, establishes integrability via `inv_sub_mul_deriv_intervalIntegrable` (the generic version), continuity from `Path.continuous_extend`, and concludes with `segment_log_FTC`.
- **Hypotheses**: Local uniqueness on the window, positive `δ_R < r`, slit-plane chord conditions.
- **Uses from project**: `inv_sub_mul_deriv_intervalIntegrable`, `segment_log_FTC`
- **Used by**: `perCrossing_window_integral_tendsto_exact`
- **Visibility**: private
- **Lines**: 933-1032
- **Notes**: proof >30 lines

### `theorem left_annular_log_diff_local`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ} {L_left : ℂ} (_hL_left_ne : L_left ≠ 0) (_h_deriv_left : ...) (_h_at : ...) {r δ_L : ℝ} (hδ_L_pos : 0 < δ_L) (hδ_L_lt : δ_L < r) (_hr_pos : 0 < r) (h_window_in_unit : ...) (h_slit_L : ...) (h_local_unique : ...) : ∫ t in (t₀ - r)..(t₀ - δ_L), deriv γ.extend t / (γ.extend t - s) = Complex.log ((γ.extend (t₀ - δ_L) - s) / (γ.extend (t₀ - r) - s))`
- **What**: Symmetric left-side FTC log-difference under local uniqueness.
- **How**: Symmetric to `right_annular_log_diff_local`: `a := t₀ - r, b := t₀ - δ_L`, integrability via `inv_sub_mul_deriv_intervalIntegrable`, then `segment_log_FTC`.
- **Hypotheses**: Same as right version on the left.
- **Uses from project**: `inv_sub_mul_deriv_intervalIntegrable`, `segment_log_FTC`
- **Used by**: `perCrossing_window_integral_tendsto_exact`
- **Visibility**: private
- **Lines**: 1037-1119
- **Notes**: proof >30 lines

### `theorem LocalDerivedCutoffs.δ_right_tendsto_zero`
- **Type**: `{γ : ClosedPwC1Immersion x} {s : ℂ} {t₀ r : ℝ} (_hr_pos : 0 < r) (h_window_Icc : ...) (h_local_unique : ...) (D : LocalDerivedCutoffs γ s t₀ r) : Tendsto D.δ_right (𝓝[>] 0) (𝓝[>] 0)`
- **What**: The right cutoff of a `LocalDerivedCutoffs` bundle tends to `0⁺` as `ε → 0⁺`.
- **How**: For any target `δ₀ > 0`, set `δ₀' := min(δ₀, r/2)` and `m := ‖γ(t₀+δ₀')-s‖` (positive by local uniqueness). For `ε < min(m, threshold)`, the contrapositive of `D.h_near_right` forces `δ_right(ε) < δ₀'`.
- **Hypotheses**: Local uniqueness on the window, `r > 0` (decorative), bundle `D`.
- **Uses from project**: `LocalDerivedCutoffs` (h_near_right, hδ_right_pos, hthresh fields)
- **Used by**: `perCrossing_window_integral_tendsto_exact`
- **Visibility**: public
- **Lines**: 1124-1170
- **Notes**: proof >30 lines, namespaced, uses classical

### `theorem LocalDerivedCutoffs.δ_left_tendsto_zero`
- **Type**: Symmetric to right version.
- **What**: Same statement for the left cutoff.
- **How**: Symmetric template using `D.h_near_left`.
- **Hypotheses**: Same as right version.
- **Uses from project**: `LocalDerivedCutoffs`
- **Used by**: `perCrossing_window_integral_tendsto_exact`
- **Visibility**: public
- **Lines**: 1173-1219
- **Notes**: proof >30 lines, namespaced, uses classical

### `theorem perCrossing_window_integral_tendsto_exact`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo 0 1) (h_at : ...) {r : ℝ} (hr_pos : 0 < r) (h_window_Icc : ...) (h_local_unique_r : ...) {L_R L_L : ℂ} (hL_R_ne, hL_L_ne) (h_deriv_right, h_deriv_left) (h_slit_R, h_slit_L, h_γPlus_div_LR, h_LL_neg_div_γMinus) : ∃ L_i : ℂ, Tendsto (fun ε => ∫ t in (t₀ - r)..(t₀ + r), cpvIntegrand (fun z => (z - s)⁻¹) γ.extend s ε t) (𝓝[>] 0) (𝓝 L_i)`
- **What**: Exact-radius form of per-window cutoff integral convergence: given local geometric data at a chosen fixed radius `r`, the cutoff integral over `[t₀-r, t₀+r]` converges as `ε → 0⁺`.
- **How**: Builds the local cutoff bundle `D = localDerivedCutoffs ...`; uses `LocalDerivedCutoffs.δ_*_tendsto_zero` for cutoff-vanishing; introduces `Λ_R(ε), Λ_L(ε)` annular log functions; applies `arg_right_annular_tendsto`/`arg_left_annular_tendsto` for arg limits; splits the cutoff integral into far (FTC-evaluated to `Λ_*`) + near (zero by indicator) parts; identifies `L_i := logNorm_diff + (argR + argL)·I`; finally uses `Complex.log_re`/`Complex.log_im` decomposition to verify Re/Im convergence.
- **Hypotheses**: All four slit-plane preconditions explicitly as inputs (chord R, chord L, boundary R, boundary L), plus local uniqueness on `[t₀-r, t₀+r]`.
- **Uses from project**: `localDerivedCutoffs`, `LocalDerivedCutoffs.δ_right_tendsto_zero`, `LocalDerivedCutoffs.δ_left_tendsto_zero`, `arg_right_annular_tendsto`, `arg_left_annular_tendsto`, `left_annular_log_diff_local`, `right_annular_log_diff_local`, `cpvIntegrand`, `inv_sub_mul_deriv_intervalIntegrable`
- **Used by**: `perCrossing_window_integral_tendsto`
- **Visibility**: public
- **Lines**: 1242-1570
- **Notes**: proof >30 lines (>320 lines), uses classical, longest proof in file

### `theorem perCrossing_window_integral_tendsto`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo 0 1) (h_at : ...) {r₀ : ℝ} (hr₀_pos : 0 < r₀) (h_window_in_unit : ...) (h_local_unique : ...) : ∃ (r : ℝ) (_hr_pos : 0 < r) (_hr_le : r ≤ r₀) (L_i : ℂ), Tendsto (fun ε => ∫ t in (t₀ - r)..(t₀ + r), cpvIntegrand (fun z => (z - s)⁻¹) γ.extend s ε t) (𝓝[>] 0) (𝓝 L_i)`
- **What**: Thin wrapper around the exact-radius version: derives the slit-plane chord-quotient data via `cpvFullSetup_local` (which shrinks the output radius), then delegates to `perCrossing_window_integral_tendsto_exact`.
- **How**: Invokes `cpvFullSetup_local`, restricts local uniqueness to the smaller radius, calls `perCrossing_window_integral_tendsto_exact`.
- **Hypotheses**: Interior `t₀`, window in `[0,1]`, local uniqueness on `[t₀-r₀, t₀+r₀]`.
- **Uses from project**: `cpvFullSetup_local`, `perCrossing_window_integral_tendsto_exact`
- **Used by**: unused in file (consumed by external callers — `Crossing.lean` per file header docs)
- **Visibility**: public
- **Lines**: 1587-1616

### `theorem multi_pole_smooth_complement_far_bound`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {crossings : Finset ℝ} (h_complete : ∀ t ∈ Icc 0 1, γ.extend t = s → t ∈ crossings) (r_at : ℝ → ℝ) (hr_at_pos : ∀ t ∈ crossings, 0 < r_at t) : ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Icc 0 1, (∀ t_i ∈ crossings, t ∉ Ioo (t_i - r_at t_i) (t_i + r_at t_i)) → m ≤ ‖γ.extend t - s‖`
- **What**: For a multi-crossing scenario, the function `t ↦ ‖γ(t) - s‖` admits a positive lower bound on the closed complement of the union of open per-crossing windows in `[0, 1]`.
- **How**: The complement `C` of the union of open windows in `[0, 1]` is closed (finite intersection of closed sets via `isClosed_biInter` + `isOpen_Ioo.isClosed_compl`), hence compact (subset of `[0, 1]`). If `C = ∅`, vacuously true with `m = 1`. Otherwise, use `IsCompact.exists_isMinOn` to find a minimizer `t_min` on `C`; `‖γ(t_min) - s‖ > 0` because if it were zero then `t_min` would be a crossing (by `h_complete`) but every crossing lies in its own open window, contradicting `t_min ∈ C`.
- **Hypotheses**: Completeness `γ(t) = s → t ∈ crossings`, positive radii `r_at`.
- **Uses from project**: []
- **Used by**: unused in file (consumed by external callers — `Crossing.lean`)
- **Visibility**: public
- **Lines**: 1675-1753
- **Notes**: proof >30 lines, uses classical, `by_cases hC_empty`

### File Summary
- Total declarations: 18
- Key API (used by 3+ others in this file): `strict_mono_inverse_exists_local` (2 here), `LocalDerivedCutoffs` (4 here), `localDerivedCutoffs` (1 here but a gateway), `exists_normalized_chord_*` (indirect via the slit-plane radius wrappers — those wrappers are used 1× each in `cpvFullSetup_local`)
- Unused in this file: `cpvFullSetup_local_exact`, `perCrossing_window_integral_tendsto`, `multi_pole_smooth_complement_far_bound` (all are public API consumed by `Crossing.lean` and other downstream modules for multi-crossing aggregation)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `exists_right_cutoff_local`, `exists_left_cutoff_local`, `localDerivedCutoffs`, `exists_chord_div_endpoint_slitPlane_right`, `exists_chord_div_endpoint_slitPlane_left`, `oneSided_deriv_setup`, `cpvFullSetup_local`, `right_annular_log_diff_local`, `left_annular_log_diff_local`, `LocalDerivedCutoffs.δ_right_tendsto_zero`, `LocalDerivedCutoffs.δ_left_tendsto_zero`, `perCrossing_window_integral_tendsto_exact`, `multi_pole_smooth_complement_far_bound`
- File purpose: This file localizes the exit-time cutoff infrastructure used in single-crossing CPV existence (`CPVExistence.lean`) to support the multi-crossing CPV existence programme (T-BR-Y6c/d). The global uniqueness hypothesis on `[0, 1]` is replaced by local uniqueness on a window `[t₀ - r, t₀ + r]`, so each crossing in a `MultiPoleCrossData` can be equipped with its own local asymmetric cutoffs `δ_left^i, δ_right^i`, threshold `θ_i`, and far/near bounds — bundled into the `LocalDerivedCutoffs` structure. The file also factors `cpvFullSetup` into a radius-independent derivative-setup (`oneSided_deriv_setup`) plus four radius-existence theorems for the slit-plane preconditions, producing an exact-radius API (`cpvFullSetup_local_exact`, `perCrossing_window_integral_tendsto_exact`) that allows callers to first take a global `r = min_i r_i` over all crossings and then apply per-window convergence with the SAME fixed radius — the technical key to multi-crossing aggregation. The headline result `perCrossing_window_integral_tendsto_exact` proves that for each window the cutoff integral `∫_{[t_i - r, t_i + r]} cpvIntegrand(ε)` converges as `ε → 0⁺`, while the auxiliary `multi_pole_smooth_complement_far_bound` provides a compactness-based positive lower bound for `‖γ - s‖` on the complement of all open windows — the input needed to add a smooth complement integral and complete the global CPV existence proof in downstream modules.
