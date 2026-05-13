# Inventory: CPVExistence.lean

### `theorem chord_div_t_tendsto_right`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) : Tendsto (fun t => (γ t - s) / ((t - t₀ : ℝ) : ℂ)) (𝓝[>] t₀) (𝓝 L)`
- **What**: The right-sided chord quotient `(γ(t) - s)/(t - t₀)` tends to the right-derivative `L` as `t → t₀⁺`.
- **How**: Decomposes the chord into `L + remainder/(t-t₀)`; the remainder/`(t-t₀)` tends to zero via the little-o characterization `hasDerivWithinAt_iff_isLittleO` of `HasDerivWithinAt`.
- **Hypotheses**: One-sided derivative `L` from the right at `t₀` and `γ(t₀) = s`.
- **Uses from project**: []
- **Used by**: `exit_chord_tendsto_right`, `normalized_chord_close_right`
- **Visibility**: public
- **Lines**: 66-107
- **Notes**: proof >30 lines

### `theorem chord_div_t_tendsto_left`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) : Tendsto (fun t => (γ t - s) / ((t - t₀ : ℝ) : ℂ)) (𝓝[<] t₀) (𝓝 L)`
- **What**: The left-sided chord quotient `(γ(t) - s)/(t - t₀)` tends to the left-derivative `L` as `t → t₀⁻`.
- **How**: Symmetric to the right case: decompose as `L + remainder/(t-t₀)`, with the remainder a little-o of `|t-t₀|`, leveraging `hasDerivWithinAt_iff_isLittleO`.
- **Hypotheses**: One-sided derivative `L` from the left at `t₀` and `γ(t₀) = s`.
- **Uses from project**: []
- **Used by**: `exit_chord_tendsto_left`, `normalized_chord_close_left`
- **Visibility**: public
- **Lines**: 112-149
- **Notes**: proof >30 lines

### `theorem exit_chord_tendsto_right`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) {δ_right : ℝ → ℝ} (hδ_pos : ∀ᶠ ε in 𝓝[>] 0, 0 < δ_right ε) (hδ_to_zero : Tendsto δ_right (𝓝[>] 0) (𝓝[>] 0)) : Tendsto (fun ε => (γ (t₀ + δ_right ε) - s) / ((δ_right ε : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 L)`
- **What**: The exit-point chord ratio `(γ(t₀ + δ_R(ε)) - s)/δ_R(ε)` tends to `L_+` as `ε → 0⁺` whenever `δ_R` is positive and tends to zero from above.
- **How**: Composes `chord_div_t_tendsto_right` with the map `ε ↦ t₀ + δ_R(ε)`, observing this carries `𝓝[>] 0` to `𝓝[>] t₀`.
- **Hypotheses**: Right derivative at `t₀`, `γ(t₀) = s`, and a positive cutoff `δ_R` tending to `0⁺`.
- **Uses from project**: `chord_div_t_tendsto_right`
- **Used by**: `exit_chord_tendsto_left` (no — symmetric), `exit_arg_tendsto_right`, `arg_right_annular_tendsto`
- **Visibility**: public
- **Lines**: 161-194
- **Notes**: proof >30 lines

### `theorem exit_chord_tendsto_left`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) {δ_left : ℝ → ℝ} (hδ_pos : ∀ᶠ ε in 𝓝[>] 0, 0 < δ_left ε) (hδ_to_zero : Tendsto δ_left (𝓝[>] 0) (𝓝[>] 0)) : Tendsto (fun ε => (γ (t₀ - δ_left ε) - s) / ((-(δ_left ε) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 L)`
- **What**: The left exit-point chord ratio `(γ(t₀ - δ_L(ε)) - s)/(-δ_L(ε))` tends to `L_-` as `ε → 0⁺`.
- **How**: Composes `chord_div_t_tendsto_left` with the map `ε ↦ t₀ - δ_L(ε)` which sends `𝓝[>] 0` to `𝓝[<] t₀`.
- **Hypotheses**: Left derivative at `t₀`, `γ(t₀) = s`, positive `δ_L` tending to `0⁺`.
- **Uses from project**: `chord_div_t_tendsto_left`
- **Used by**: `exit_arg_tendsto_left`, `arg_left_annular_tendsto`
- **Visibility**: public
- **Lines**: 202-234
- **Notes**: proof >30 lines

### `theorem exit_arg_tendsto_right`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL_slit : L ∈ Complex.slitPlane) {δ_right : ℝ → ℝ} (hδ_pos : ...) (hδ_to_zero : ...) : Tendsto (fun ε => Complex.arg (γ (t₀ + δ_right ε) - s)) (𝓝[>] 0) (𝓝 L.arg)`
- **What**: As `ε → 0⁺`, `arg(γ(t₀ + δ_R(ε)) - s) → arg L_+`, provided `L_+` lies in the slit plane.
- **How**: Uses `exit_chord_tendsto_right` to obtain convergence of the chord-ratio to `L`, then continuity of `Complex.arg` on `Complex.slitPlane` and the fact that arg is invariant under positive-real scaling.
- **Hypotheses**: `L_+ ∈ Complex.slitPlane`, plus the standard one-sided derivative / cutoff data.
- **Uses from project**: `exit_chord_tendsto_right`
- **Used by**: `exit_log_tendsto_right`
- **Visibility**: public
- **Lines**: 247-277
- **Notes**: proof >30 lines

### `theorem exit_arg_tendsto_left`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hnegL_slit : -L ∈ Complex.slitPlane) {δ_left : ℝ → ℝ} (hδ_pos : ...) (hδ_to_zero : ...) : Tendsto (fun ε => Complex.arg (γ (t₀ - δ_left ε) - s)) (𝓝[>] 0) (𝓝 (-L).arg)`
- **What**: Mirror image: `arg(γ(t₀ - δ_L(ε)) - s) → arg(-L_-)` as `ε → 0⁺`.
- **How**: Negates `exit_chord_tendsto_left` to obtain convergence to `-L`, then uses continuity of `Complex.arg` at `-L` (slit-plane assumption) and positive-real scaling invariance.
- **Hypotheses**: `-L_- ∈ Complex.slitPlane`, standard cutoff data.
- **Uses from project**: `exit_chord_tendsto_left`
- **Used by**: `exit_log_tendsto_left`
- **Visibility**: public
- **Lines**: 285-327
- **Notes**: proof >30 lines

### `theorem exit_log_tendsto_right`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL_slit : L ∈ Complex.slitPlane) {δ_right : ℝ → ℝ} (hδ_pos : ...) (hδ_to_zero : ...) (h_exit : ∀ᶠ ε in 𝓝[>] 0, ‖γ (t₀ + δ_right ε) - s‖ = ε) : Tendsto (fun ε => Complex.log (γ (t₀ + δ_right ε) - s) - ((Real.log ε : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (L.arg * Complex.I))`
- **What**: `log(γ(t₀ + δ_R(ε)) - s) - log ε` tends to `arg(L_+) · I` as `ε → 0⁺` under the exit-time property `‖γ-s‖ = ε`.
- **How**: Decomposes `Complex.log z = Real.log ‖z‖ + arg z · I`; the norm cancels `Real.log ε` exactly via the exit-time hypothesis, and the arg part converges by `exit_arg_tendsto_right`.
- **Hypotheses**: `L ∈ Complex.slitPlane`, exit-time equality `‖γ(t₀ + δ_R(ε)) - s‖ = ε`, plus cutoff data.
- **Uses from project**: `exit_arg_tendsto_right`
- **Used by**: `exit_log_diff_tendsto`
- **Visibility**: public
- **Lines**: 338-380
- **Notes**: proof >30 lines

### `theorem exit_log_tendsto_left`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hnegL_slit : -L ∈ Complex.slitPlane) {δ_left : ℝ → ℝ} (hδ_pos : ...) (hδ_to_zero : ...) (h_exit : ∀ᶠ ε in 𝓝[>] 0, ‖γ (t₀ - δ_left ε) - s‖ = ε) : Tendsto (fun ε => Complex.log (γ (t₀ - δ_left ε) - s) - ((Real.log ε : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 ((-L).arg * Complex.I))`
- **What**: Symmetric left version: `log(γ(t₀ - δ_L(ε)) - s) - log ε → arg(-L_-) · I`.
- **How**: Same as the right case but using `exit_arg_tendsto_left` for the arg limit and the left exit-time equality for the norm cancellation.
- **Hypotheses**: `-L ∈ Complex.slitPlane`, left exit-time equality, cutoff data.
- **Uses from project**: `exit_arg_tendsto_left`
- **Used by**: `exit_log_diff_tendsto`
- **Visibility**: public
- **Lines**: 383-418
- **Notes**: proof >30 lines

### `theorem exit_log_diff_tendsto`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L_right L_left : ℂ} (h_deriv_right : HasDerivWithinAt γ L_right (Ioi t₀) t₀) (h_deriv_left : HasDerivWithinAt γ L_left (Iio t₀) t₀) (h_at : γ t₀ = s) (hL_right_slit : ...) (hnegL_left_slit : ...) {δ_left δ_right : ℝ → ℝ} (hδ_left_pos : ...) (hδ_right_pos : ...) (hδ_left_to_zero : ...) (hδ_right_to_zero : ...) (h_exit_left : ...) (h_exit_right : ...) : Tendsto (fun ε => Complex.log (γ (t₀ + δ_right ε) - s) - Complex.log (γ (t₀ - δ_left ε) - s)) (𝓝[>] 0) (𝓝 (L_right.arg * I - (-L_left).arg * I))`
- **What**: The symmetric log-difference between right and left exit points tends to `(arg L_+ - arg(-L_-))·I` as `ε → 0⁺`, with the divergent `log ε` terms canceling.
- **How**: Subtracts `exit_log_tendsto_right` and `exit_log_tendsto_left`, exploiting that `(log z_R - log ε) - (log z_L - log ε) = log z_R - log z_L`.
- **Hypotheses**: Two-sided derivative data, both slit-plane conditions, both exit-time equalities.
- **Uses from project**: `exit_log_tendsto_right`, `exit_log_tendsto_left`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 429-459

### `theorem normalized_chord_close_right`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) {ρ : ℝ} (hρ_pos : 0 < ρ) : ∀ᶠ t in 𝓝[>] t₀, ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ`
- **What**: For any `ρ > 0`, eventually as `t → t₀⁺`, the normalized chord `(γ(t) - s)/(L·(t - t₀))` is within `ρ` of `1`.
- **How**: Divides the chord-to-tangent limit `chord_div_t_tendsto_right` by the nonzero `L`, then extracts the eventually-close statement from `Metric.tendsto_nhds`.
- **Hypotheses**: Right derivative `L ≠ 0`, `γ(t₀) = s`.
- **Uses from project**: `chord_div_t_tendsto_right`
- **Used by**: `exists_normalized_chord_right`
- **Visibility**: public
- **Lines**: 474-507
- **Notes**: proof >30 lines

### `theorem normalized_chord_close_left`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) {ρ : ℝ} (hρ_pos : 0 < ρ) : ∀ᶠ t in 𝓝[<] t₀, ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ`
- **What**: Symmetric statement on the left side.
- **How**: Divides `chord_div_t_tendsto_left` by `L`, extracts eventually-close.
- **Hypotheses**: Left derivative `L ≠ 0`.
- **Uses from project**: `chord_div_t_tendsto_left`
- **Used by**: `exists_normalized_chord_left`
- **Visibility**: public
- **Lines**: 511-539

### `theorem exists_normalized_chord_right`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : ...) (h_at : ...) (hL : L ≠ 0) {ρ : ℝ} (hρ_pos : 0 < ρ) : ∃ r > 0, ∀ t ∈ Ioc t₀ (t₀ + r), ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ`
- **What**: Extracts a fixed positive radius `r` such that the normalized chord stays close to `1` uniformly on `(t₀, t₀ + r]`.
- **How**: Unfolds the eventually-statement of `normalized_chord_close_right` to a metric ball `(t₀ - r, t₀ + r)` then halves the radius for the closed interval.
- **Hypotheses**: As in `normalized_chord_close_right`.
- **Uses from project**: `normalized_chord_close_right`
- **Used by**: `exists_slitPlane_chord_quotient_right`, `cpvFullSetup`, `exists_chord_div_endpoint_slitPlane_right` (in `LocalCutoffs`)
- **Visibility**: public
- **Lines**: 544-564
- **Notes**: proof >30 lines

### `theorem exists_normalized_chord_left`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : ...) (h_at : ...) (hL : L ≠ 0) {ρ : ℝ} (hρ_pos : 0 < ρ) : ∃ r > 0, ∀ t ∈ Ico (t₀ - r) t₀, ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ`
- **What**: Symmetric extraction of a fixed radius for left-side normalized chord closeness.
- **How**: Unfolds `normalized_chord_close_left` to a metric ball and halves.
- **Hypotheses**: Left derivative `L ≠ 0`.
- **Uses from project**: `normalized_chord_close_left`
- **Used by**: `exists_slitPlane_chord_quotient_left_forward`, `exists_slitPlane_chord_quotient_left`, `cpvFullSetup`, `exists_chord_div_endpoint_slitPlane_left` (in `LocalCutoffs`)
- **Visibility**: public
- **Lines**: 567-587
- **Notes**: proof >30 lines

### `theorem div_mem_slitPlane_of_close_to_one`
- **Type**: `{z w : ℂ} (hz : ‖z - 1‖ ≤ 1/4) (hw : ‖w - 1‖ ≤ 1/4) : z / w ∈ Complex.slitPlane`
- **What**: If `z` and `w` are each within `1/4` of `1`, then `z/w` lies in the slit plane (real part positive).
- **How**: Triangle inequality gives `‖z - w‖ ≤ 1/2`; reverse triangle gives `‖w‖ ≥ 3/4`; hence `‖z/w - 1‖ ≤ 2/3 < 1`; then `|Re(z/w) - 1| ≤ ‖z/w - 1‖ < 1` forces `Re(z/w) > 0` so `z/w ∈ slitPlane`.
- **Hypotheses**: Both `z` and `w` close (≤ 1/4 in norm) to 1.
- **Uses from project**: []
- **Used by**: `exists_slitPlane_chord_quotient_right`, `exists_slitPlane_chord_quotient_left_forward`, `exists_slitPlane_chord_quotient_left`
- **Visibility**: public
- **Lines**: 596-635
- **Notes**: proof >30 lines

### `theorem exists_slitPlane_chord_quotient_right`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) : ∃ r > 0, ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r → (γ b - s) / (γ a - s) ∈ Complex.slitPlane`
- **What**: For all chord pairs in a small right interval, the chord quotient `(γ(b)-s)/(γ(a)-s)` lies in the slit plane.
- **How**: Uses `exists_normalized_chord_right` with `ρ = 1/4`, then `div_mem_slitPlane_of_close_to_one` on the normalized chords, then handles positive-real scaling via `Complex.mem_slitPlane_iff`.
- **Hypotheses**: Right derivative `L ≠ 0`.
- **Uses from project**: `exists_normalized_chord_right`, `div_mem_slitPlane_of_close_to_one`
- **Used by**: `cpvFullSetup`, `exists_chord_slitPlane_radius_right` (in `LocalCutoffs`)
- **Visibility**: public
- **Lines**: 645-716
- **Notes**: proof >30 lines

### `theorem exists_slitPlane_chord_quotient_left_forward`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) : ∃ r > 0, ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ → (γ b - s) / (γ a - s) ∈ Complex.slitPlane`
- **What**: Forward-direction slit-plane chord quotient `(γ(b)-s)/(γ(a)-s)` on left intervals (with `b` closer to `t₀`).
- **How**: Applies `exists_normalized_chord_left` with `ρ = 1/4`, then `div_mem_slitPlane_of_close_to_one`, then positive-real-scaling argument via `div_pos_of_neg_of_neg`.
- **Hypotheses**: Left derivative `L ≠ 0`.
- **Uses from project**: `exists_normalized_chord_left`, `div_mem_slitPlane_of_close_to_one`
- **Used by**: `cpvFullSetup`, `exists_chord_slitPlane_radius_left` (in `LocalCutoffs`)
- **Visibility**: public
- **Lines**: 725-787
- **Notes**: proof >30 lines

### `theorem exists_slitPlane_chord_quotient_left`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) : ∃ r > 0, ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ → (γ a - s) / (γ b - s) ∈ Complex.slitPlane`
- **What**: Backward-direction (FTC-relevant) variant: the quotient `(γ(a)-s)/(γ(b)-s)` (further-over-closer) is in the slit plane on the left.
- **How**: Same template as the forward version, but with roles of `z` and `w` swapped in `div_mem_slitPlane_of_close_to_one`.
- **Hypotheses**: Left derivative `L ≠ 0`.
- **Uses from project**: `exists_normalized_chord_left`, `div_mem_slitPlane_of_close_to_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 795-855
- **Notes**: proof >30 lines

### `theorem annulus_FTC_right`
- **Type**: `{γ : ℝ → ℂ} {s : ℂ} {a b : ℝ} (hab : a ≤ b) (hγ_cont : ContinuousOn γ (Icc a b)) {P : Set ℝ} (hP_count : P.Countable) (hγ_diff : ∀ t ∈ Ioo a b \ P, HasDerivAt γ (deriv γ t) t) (h_ne : γ a - s ≠ 0) (h_slit : ∀ t ∈ Icc a b, (γ t - s) / (γ a - s) ∈ Complex.slitPlane) (h_int : IntervalIntegrable (fun t => deriv γ t / (γ t - s)) volume a b) : ∫ t in a..b, deriv γ t / (γ t - s) = Complex.log ((γ b - s) / (γ a - s))`
- **What**: FTC restatement for the right annular piece: the integral `∫ γ'/(γ-s)` equals the log of the chord quotient, given continuity, off-partition differentiability, and slit-plane data.
- **How**: One-line invocation of `segment_log_FTC` from the project's WindingInteger module.
- **Hypotheses**: Standard FTC data plus slit-plane condition for chord quotients.
- **Uses from project**: `segment_log_FTC`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 867-879

### `theorem right_annulus_log_FTC`
- **Type**: `(γ : ℝ → ℂ) {s : ℂ} {t₀ a b : ℝ} (_ht₀_lt_a : t₀ < a) (hab : a ≤ b) (hγ_cont : ...) {P : Set ℝ} (hP_count : P.Countable) (hγ_diff : ...) (h_ne_a : γ a - s ≠ 0) (h_slit : ...) (h_int : ...) : ∫ t in a..b, deriv γ t / (γ t - s) = Complex.log ((γ b - s) / (γ a - s))`
- **What**: Variant of `annulus_FTC_right` with an explicit (but unused) hypothesis `t₀ < a` for documentation.
- **How**: Direct call to `segment_log_FTC`.
- **Hypotheses**: Same as `annulus_FTC_right`, plus `t₀ < a` (decorative).
- **Uses from project**: `segment_log_FTC`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 909-921

### `theorem right_annular_log_diff`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ} {L_right : ℂ} (_hL_right_ne : L_right ≠ 0) (_h_deriv_right : ...) (_h_at : ...) {r δ_R : ℝ} (hδ_R_pos : 0 < δ_R) (hδ_R_lt : δ_R < r) (_hr_pos : 0 < r) (hr_le_one_sub : t₀ + r ≤ 1) (h_slit_R : ...) (h_unique : ...) (ht₀_pos : 0 < t₀) : ∫ t in (t₀ + δ_R)..(t₀ + r), deriv γ.extend t / (γ.extend t - s) = Complex.log ((γ.extend (t₀ + r) - s) / (γ.extend (t₀ + δ_R) - s))`
- **What**: For a closed pw-C¹ immersion, the integral on the right annular piece `[t₀+δ_R, t₀+r]` equals the chord-quotient log.
- **How**: Sets `a := t₀+δ_R, b := t₀+r`, establishes `γ(a) ≠ s` via global uniqueness, integrability via `inv_sub_mul_deriv_intervalIntegrable_right` from `CrossingDataBuilder`, and concludes with `segment_log_FTC`.
- **Hypotheses**: Global uniqueness on `[0, 1]`, interior `t₀`, positive `δ_R < r`, slit-plane chord condition.
- **Uses from project**: `inv_sub_mul_deriv_intervalIntegrable_right`, `segment_log_FTC`
- **Used by**: `hasCauchyPV_inv_sub_of_flat_one_full`
- **Visibility**: public
- **Lines**: 948-1016
- **Notes**: proof >30 lines

### `theorem exit_time_eq_right`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ} (D : DerivedAsymmetricCutoffs γ s t₀) (ht₀ : t₀ ∈ Ioo 0 1) {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold) : ‖γ.extend (t₀ + D.δ_right ε) - s‖ = ε`
- **What**: For the derived asymmetric cutoff bundle, the exit-time norm equation `‖γ(t₀ + δ_R(ε)) - s‖ = ε` holds at the cutoff endpoint.
- **How**: Squeezes between `D.h_near_right` (upper bound `≤ ε`) and a continuity-based argument using `D.h_far_right` applied to nearby points slightly past the cutoff, taking the limit via `ge_of_tendsto`.
- **Hypotheses**: Cutoff bundle `D` with both near and far bounds, `t₀ ∈ Ioo 0 1`.
- **Uses from project**: `DerivedAsymmetricCutoffs` (h_near_right, h_far_right, hδ_right_pos, hδ_right_small fields)
- **Used by**: `hasCauchyPV_inv_sub_of_flat_one_full`
- **Visibility**: public
- **Lines**: 1024-1063
- **Notes**: proof >30 lines

### `theorem exit_time_eq_left`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ} (D : DerivedAsymmetricCutoffs γ s t₀) (ht₀ : t₀ ∈ Ioo 0 1) {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold) : ‖γ.extend (t₀ - D.δ_left ε) - s‖ = ε`
- **What**: Symmetric left-side exit-time norm equation `‖γ(t₀ - δ_L(ε)) - s‖ = ε`.
- **How**: Same squeezing pattern as `exit_time_eq_right`, using `D.h_near_left` and `D.h_far_left`.
- **Hypotheses**: Same as right version.
- **Uses from project**: `DerivedAsymmetricCutoffs`
- **Used by**: `hasCauchyPV_inv_sub_of_flat_one_full`
- **Visibility**: public
- **Lines**: 1066-1104
- **Notes**: proof >30 lines

### `theorem left_annular_log_diff`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ} {L_left : ℂ} (_hL_left_ne : L_left ≠ 0) (_h_deriv_left : ...) (_h_at : ...) {r δ_L : ℝ} (hδ_L_pos : 0 < δ_L) (hδ_L_lt : δ_L < r) (_hr_pos : 0 < r) (hr_le_t₀ : 0 ≤ t₀ - r) (h_slit_L : ...) (h_unique : ...) (ht₀_lt_one : t₀ < 1) : ∫ t in (t₀ - r)..(t₀ - δ_L), deriv γ.extend t / (γ.extend t - s) = Complex.log ((γ.extend (t₀ - δ_L) - s) / (γ.extend (t₀ - r) - s))`
- **What**: Symmetric left annular FTC log-difference identity for a closed pw-C¹ immersion.
- **How**: Same template as `right_annular_log_diff`: set `a, b`, use `inv_sub_mul_deriv_intervalIntegrable_left` for integrability, then `segment_log_FTC`.
- **Hypotheses**: Mirror of right version: global uniqueness, interior `t₀`, slit-plane chord condition on left.
- **Uses from project**: `inv_sub_mul_deriv_intervalIntegrable_left`, `segment_log_FTC`
- **Used by**: `hasCauchyPV_inv_sub_of_flat_one_full`
- **Visibility**: public
- **Lines**: 1109-1180
- **Notes**: proof >30 lines

### `theorem arg_right_annular_tendsto`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) {δ_right : ℝ → ℝ} {r : ℝ} (h_γr_div_L : (γ (t₀ + r) - s) / L ∈ Complex.slitPlane) (hδ_pos : ...) (hδ_to_zero : ...) : Tendsto (fun ε => Complex.arg ((γ (t₀ + r) - s) / (γ (t₀ + δ_right ε) - s))) (𝓝[>] 0) (𝓝 ((γ (t₀ + r) - s) / L).arg)`
- **What**: The argument of the annular chord quotient `(γ(t₀+r)-s)/(γ(t₀+δ_R(ε))-s)` converges as `ε → 0⁺`.
- **How**: Inverts `exit_chord_tendsto_right` to get `δ_R(ε)/(γ(...)-s) → 1/L`; multiplies by the fixed numerator; applies continuity of `Complex.arg` at the slit-plane point; uses arg invariance under positive-real scaling.
- **Hypotheses**: Right derivative `L ≠ 0`, slit-plane condition on chord-tangent quotient at radius `r`.
- **Uses from project**: `exit_chord_tendsto_right`
- **Used by**: `hasCauchyPV_inv_sub_of_flat_one_full`, `perCrossing_window_integral_tendsto_exact` (in `LocalCutoffs`)
- **Visibility**: public
- **Lines**: 1189-1243
- **Notes**: proof >30 lines

### `theorem arg_left_annular_tendsto`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (_hL : L ≠ 0) {δ_left : ℝ → ℝ} {r : ℝ} (h_γnegr_div_L : (-L) / (γ (t₀ - r) - s) ∈ Complex.slitPlane) (hδ_pos : ...) (hδ_to_zero : ...) : Tendsto (fun ε => Complex.arg ((γ (t₀ - δ_left ε) - s) / (γ (t₀ - r) - s))) (𝓝[>] 0) (𝓝 ((-L) / (γ (t₀ - r) - s)).arg)`
- **What**: Symmetric left-side arg convergence for the annular chord quotient.
- **How**: From `exit_chord_tendsto_left`, derive `(γ(t₀-δ_L(ε))-s)/δ_L(ε) → -L`; divide by the fixed denominator; apply continuity of arg at the slit-plane point.
- **Hypotheses**: Left derivative, slit-plane condition for `(-L)/(γ(t₀-r) - s)`.
- **Uses from project**: `exit_chord_tendsto_left`
- **Used by**: `hasCauchyPV_inv_sub_of_flat_one_full`, `perCrossing_window_integral_tendsto_exact` (in `LocalCutoffs`)
- **Visibility**: public
- **Lines**: 1246-1292
- **Notes**: proof >30 lines

### `theorem DerivedAsymmetricCutoffs.δ_right_tendsto_zero`
- **Type**: `{γ : ClosedPwC1Immersion x} {s : ℂ} {t₀ : ℝ} (ht₀_Ioo : t₀ ∈ Ioo 0 1) (h_unique : ...) (D : DerivedAsymmetricCutoffs γ s t₀) : Tendsto D.δ_right (𝓝[>] 0) (𝓝[>] 0)`
- **What**: The right cutoff function `δ_right` tends to `0⁺` as `ε → 0⁺`.
- **How**: For any target `δ₀ > 0`, set `m := ‖γ(t₀+δ₀)-s‖ > 0` (positive by uniqueness). For `ε < min(m, threshold)`, the contrapositive of `D.h_near_right` (with `t = t₀ + δ₀`) gives `δ_right(ε) < δ₀`.
- **Hypotheses**: Interior `t₀`, global uniqueness, derived cutoff bundle.
- **Uses from project**: `DerivedAsymmetricCutoffs` (h_near_right, hδ_right_pos, hthresh fields)
- **Used by**: `hasCauchyPV_inv_sub_of_flat_one_full`
- **Visibility**: public
- **Lines**: 1304-1362
- **Notes**: proof >30 lines, namespaced (DerivedAsymmetricCutoffs.)

### `theorem DerivedAsymmetricCutoffs.δ_left_tendsto_zero`
- **Type**: `{γ : ClosedPwC1Immersion x} {s : ℂ} {t₀ : ℝ} (ht₀_Ioo : t₀ ∈ Ioo 0 1) (h_unique : ...) (D : DerivedAsymmetricCutoffs γ s t₀) : Tendsto D.δ_left (𝓝[>] 0) (𝓝[>] 0)`
- **What**: Symmetric statement for the left cutoff.
- **How**: Same template using `D.h_near_left` and the contrapositive argument.
- **Hypotheses**: Interior `t₀`, global uniqueness.
- **Uses from project**: `DerivedAsymmetricCutoffs`
- **Used by**: `hasCauchyPV_inv_sub_of_flat_one_full`
- **Visibility**: public
- **Lines**: 1365-1409
- **Notes**: proof >30 lines, namespaced

### `theorem cpvFullSetup`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 1) (h_at : γ.extend t₀ = s) (h_unique : ...) : ∃ (L_R L_L : ℂ) (r : ℝ), L_R ≠ 0 ∧ L_L ≠ 0 ∧ 0 < r ∧ r ≤ t₀ ∧ r ≤ 1 - t₀ ∧ HasDerivWithinAt ... L_R (Ioi t₀) t₀ ∧ HasDerivWithinAt ... L_L (Iio t₀) t₀ ∧ [chord slit-plane R] ∧ [chord slit-plane L] ∧ [boundary R slit-plane] ∧ [boundary L slit-plane]`
- **What**: Geometric setup bundle: extracts one-sided derivative limits, a small common radius `r > 0` satisfying all slit-plane chord and boundary conditions for the full CPV existence theorem.
- **How**: Calls `exists_right_deriv_limit` / `exists_left_deriv_limit` for derivative limits; builds `HasDerivWithinAt` from `Tendsto` of `deriv` via `hasDerivWithinAt_Ici/Iic_of_tendsto_deriv`; obtains four threshold radii from chord and normalized-chord lemmas and takes their min; verifies the four required slit-plane conditions by detailed real-imaginary-part arithmetic.
- **Hypotheses**: Interior crossing parameter `t₀`, global uniqueness.
- **Uses from project**: `exists_right_deriv_limit`, `exists_left_deriv_limit`, `eventually_differentiable_right`, `eventually_differentiable_left`, `exists_slitPlane_chord_quotient_right`, `exists_slitPlane_chord_quotient_left_forward`, `exists_normalized_chord_right`, `exists_normalized_chord_left`
- **Used by**: `hasCauchyPV_inv_sub_of_flat_one_full`
- **Visibility**: private
- **Lines**: 1428-1678
- **Notes**: proof >30 lines (>200 lines), uses classical

### `theorem hasCauchyPV_inv_sub_of_flat_one_full`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 1) (h_at : γ.extend t₀ = s) (h_unique : ...) (_h_flat : IsFlatOfOrder γ.extend t₀ 1) : ∃ L : ℂ, HasCauchyPV (fun z => (z - s)⁻¹) γ.toPwC1Immersion.toPiecewiseC1Path s L`
- **What**: Main theorem: full CPV existence at a transverse single crossing for a `C¹`-immersion-extended path.
- **How**: 1) Uses `cpvFullSetup` to extract `L_R, L_L, r` and slit-plane conditions. 2) Builds `DerivedAsymmetricCutoffs` via `deriveAsymmetricCutoffs_anywhere`. 3) Decomposes the cutoff integral via `cutoff_integral_eq_outer_sum` into fixed integrals `C₁, C₂` plus annular logs `Λ_L(ε), Λ_R(ε)`. 4) The annular logs equal FTC log-differences via `right_annular_log_diff` and `left_annular_log_diff`. 5) Identifies `L := C₁ + C₂ + logNorm_diff + (argR_lim + argL_lim)·I`. 6) Proves real-part `Real.log ε` cancellation symmetrically and arg-limit convergence via `arg_*_annular_tendsto`.
- **Hypotheses**: Interior `t₀`, global uniqueness, `IsFlatOfOrder` (unused — automatic for `C¹`).
- **Uses from project**: `cpvFullSetup`, `deriveAsymmetricCutoffs_anywhere`, `DerivedAsymmetricCutoffs.δ_right_tendsto_zero`, `DerivedAsymmetricCutoffs.δ_left_tendsto_zero`, `cutoff_integral_eq_outer_sum`, `right_annular_log_diff`, `left_annular_log_diff`, `arg_right_annular_tendsto`, `arg_left_annular_tendsto`, `exit_time_eq_right`, `exit_time_eq_left`, `inv_sub_mul_deriv_intervalIntegrable_left`, `inv_sub_mul_deriv_intervalIntegrable_right`, `HasCauchyPV`
- **Used by**: `hasCauchyPV_inv_sub_of_flat_one_full_anywhere`
- **Visibility**: public
- **Lines**: 1689-1977
- **Notes**: proof >30 lines (>280 lines), uses classical

### `theorem hasCauchyPV_inv_sub_of_flat_one_full_anywhere`
- **Type**: Same signature as `hasCauchyPV_inv_sub_of_flat_one_full`.
- **What**: Corner-friendly alias of `hasCauchyPV_inv_sub_of_flat_one_full` for callers wanting the explicit "anywhere" naming.
- **How**: One-line forwarding call.
- **Hypotheses**: Same as the main theorem.
- **Uses from project**: `hasCauchyPV_inv_sub_of_flat_one_full`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1985-1995

### File Summary
- Total declarations: 25
- Key API (used by 3+ others in this file): `chord_div_t_tendsto_right` (2 here), `chord_div_t_tendsto_left` (2 here), `exit_chord_tendsto_right` (2 here + downstream), `exit_chord_tendsto_left` (2 here + downstream), `div_mem_slitPlane_of_close_to_one` (3 here), `exists_normalized_chord_right` (2 in file, plus downstream), `exists_normalized_chord_left` (3 here + downstream), `cpvFullSetup` (1 here + key gateway for the main theorem)
- Unused in this file: `exit_log_diff_tendsto`, `exists_slitPlane_chord_quotient_left`, `annulus_FTC_right`, `right_annulus_log_FTC`, `hasCauchyPV_inv_sub_of_flat_one_full_anywhere` (all are public API consumed by other modules)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `chord_div_t_tendsto_right`, `chord_div_t_tendsto_left`, `exit_chord_tendsto_right`, `exit_chord_tendsto_left`, `exit_arg_tendsto_right`, `exit_arg_tendsto_left`, `exit_log_tendsto_right`, `exit_log_tendsto_left`, `normalized_chord_close_right`, `exists_normalized_chord_right`, `exists_normalized_chord_left`, `div_mem_slitPlane_of_close_to_one`, `exists_slitPlane_chord_quotient_right`, `exists_slitPlane_chord_quotient_left_forward`, `exists_slitPlane_chord_quotient_left`, `right_annular_log_diff`, `exit_time_eq_right`, `exit_time_eq_left`, `left_annular_log_diff`, `arg_right_annular_tendsto`, `arg_left_annular_tendsto`, `DerivedAsymmetricCutoffs.δ_right_tendsto_zero`, `DerivedAsymmetricCutoffs.δ_left_tendsto_zero`, `cpvFullSetup`, `hasCauchyPV_inv_sub_of_flat_one_full`
- File purpose: This file establishes the analytic content underlying Cauchy principal value (CPV) existence for a closed piecewise-`C¹` immersion `γ` crossing a pole `s` at an isolated transverse single crossing `t₀`. It builds the chord-to-tangent quotient limits (right and left), exit-point chord ratios, exit-point arg and log convergences, slit-plane conditions on chord quotients, and FTC log-difference identities on annular pieces. Combining these, the `Real.log ε` divergences from the two exit points cancel symmetrically, and the imaginary parts converge via continuity of `Complex.arg` on the slit plane. The headline theorem `hasCauchyPV_inv_sub_of_flat_one_full` produces an explicit `L : ℂ` (assembled from fixed-integral constants, a logarithmic norm difference, and an argument-sum imaginary part) realizing `HasCauchyPV (fun z => (z - s)⁻¹) γ s L`, eliminating the previously-axiomatic `h_geometry_cpv` oracle in the residue theorem at a transverse crossing (T-BR-Y3g).
