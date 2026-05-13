# Inventory: ForMathlib/CrossingDataConstruction.lean

### `structure CrossingGeometry`
- **Type**: `(γ : ClosedPwC1Immersion x) (s : ℂ) : Type _` with fields `t₀ : ℝ`, `ht₀ : t₀ ∈ Ioo 0 1`, `cross : γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s`, `unique_crossing : ∀ t ∈ Icc 0 1, γ ... t = s → t = t₀`
- **What**: Packaged data witnessing a unique transverse crossing of `γ` at `s`: the crossing parameter `t₀ ∈ (0,1)`, that γ(t₀) = s, and uniqueness of the crossing on `[0,1]`.
- **How**: `structure` declaration with four explicit fields (constructor by data).
- **Hypotheses**: parameterised by `γ : ClosedPwC1Immersion x` and `s : ℂ` (with `x : ℂ` implicit).
- **Uses from project**: `ClosedPwC1Immersion`, `PwC1Immersion`, `PiecewiseC1Path`.
- **Used by**: `CrossingGeometry.toIsCrossed`, `CrossingGeometry.of_isCrossed_unique`, `CrossingGeometry.γE`, `CrossingGeometry.normFn_eq_zero_iff`, `CrossingGeometry.exists_farMin_pos`, `CrossingGeometry.normFn_tendsto_zero`, `CrossingGeometry.exists_near_delta`, `CrossingGeometry.exists_near_delta_lt`, `SingleCrossingData.ofGeometryAndFTC`.
- **Visibility**: public (in `namespace LeanModularForms`)
- **Lines**: 80–89
- **Notes**: none

### `theorem CrossingGeometry.toIsCrossed`
- **Type**: `(γ : ClosedPwC1Immersion x) (s : ℂ) (G : CrossingGeometry γ s) : IsCrossed γ.toPwC1Immersion s`
- **What**: `CrossingGeometry γ s` implies the existential `IsCrossed γ.toPwC1Immersion s`.
- **How**: Anonymous-constructor `⟨G.t₀, G.ht₀, G.cross⟩`.
- **Hypotheses**: `CrossingGeometry γ s`.
- **Uses from project**: `CrossingGeometry`, `IsCrossed`, `ClosedPwC1Immersion`, `PwC1Immersion`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 92–94
- **Notes**: none

### `noncomputable def CrossingGeometry.of_isCrossed_unique`
- **Type**: `(γ : ClosedPwC1Immersion x) (s : ℂ) (h_cross : IsCrossed γ.toPwC1Immersion s) (h_unique : ∀ t ∈ Icc 0 1, γ.toPwC1Immersion.toPiecewiseC1Path t = s → t = crossingParam γ.toPwC1Immersion s) : CrossingGeometry γ s`
- **What**: Build `CrossingGeometry γ s` from existential `IsCrossed` plus uniqueness of the crossing.
- **How**: Set `t₀ := crossingParam γ.toPwC1Immersion s` (chosen via `Classical.choose` inside `crossingParam`); membership `ht₀` from `crossingParam_mem_Ioo`; `cross` from `γ_at_crossingParam`; `unique_crossing` is the supplied hypothesis.
- **Hypotheses**: `IsCrossed γ.toPwC1Immersion s`, uniqueness of crossing in `[0,1]`.
- **Uses from project**: `CrossingGeometry`, `IsCrossed`, `crossingParam`, `crossingParam_mem_Ioo`, `γ_at_crossingParam`, `ClosedPwC1Immersion`, `PwC1Immersion`, `PiecewiseC1Path`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 105–115
- **Notes**: `noncomputable` declaration

### `private noncomputable abbrev CrossingGeometry.γE`
- **Type**: `(γ : ClosedPwC1Immersion x) : ℝ → ℂ`
- **What**: Abbreviation for `γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend`, the underlying ℝ→ℂ extension of the curve.
- **How**: Definition by `abbrev`.
- **Hypotheses**: `γ : ClosedPwC1Immersion x`.
- **Uses from project**: `ClosedPwC1Immersion`, `PwC1Immersion`, `PiecewiseC1Path`.
- **Used by**: `normFn`, `normFn_zero_iff_eq`.
- **Visibility**: private
- **Lines**: 122–123
- **Notes**: none

### `private noncomputable def CrossingGeometry.normFn`
- **Type**: `(γ : ClosedPwC1Immersion x) (s : ℂ) (t : ℝ) : ℝ`
- **What**: `t ↦ ‖γE γ t − s‖` — the distance from the curve to `s` as a function of parameter `t`.
- **How**: Direct definition.
- **Hypotheses**: `γ : ClosedPwC1Immersion x`, `s : ℂ`, `t : ℝ`.
- **Uses from project**: `γE`, `ClosedPwC1Immersion`.
- **Used by**: `normFn_continuous`, `normFn_zero_iff_eq`, `normFn_eq_zero_iff`, `exists_farMin_pos`, `normFn_tendsto_zero`, `exists_near_delta`, `exists_near_delta_lt`.
- **Visibility**: private
- **Lines**: 126–127
- **Notes**: none

### `private theorem CrossingGeometry.normFn_continuous`
- **Type**: `(γ : ClosedPwC1Immersion x) (s : ℂ) : Continuous (normFn γ s)`
- **What**: `t ↦ ‖γ(t) − s‖` is continuous.
- **How**: Continuity of `γ.toPwC1Immersion.toPiecewiseC1Path.continuous` combined with `continuous_const` for `s`, subtracted and post-composed with `norm`.
- **Hypotheses**: none.
- **Uses from project**: `normFn`, `ClosedPwC1Immersion`, `PwC1Immersion`, `PiecewiseC1Path`.
- **Used by**: `exists_farMin_pos`, `normFn_tendsto_zero`.
- **Visibility**: private
- **Lines**: 129–131
- **Notes**: none

### `private theorem CrossingGeometry.normFn_zero_iff_eq`
- **Type**: `(γ : ClosedPwC1Immersion x) (s : ℂ) (t : ℝ) : normFn γ s t = 0 ↔ γE γ t = s`
- **What**: The distance to `s` vanishes iff the curve hits `s`.
- **How**: `simp only [normFn, norm_eq_zero, sub_eq_zero]`.
- **Hypotheses**: none.
- **Uses from project**: `normFn`, `γE`.
- **Used by**: `normFn_eq_zero_iff`, `normFn_tendsto_zero`.
- **Visibility**: private
- **Lines**: 133–135
- **Notes**: none

### `private theorem CrossingGeometry.normFn_eq_zero_iff`
- **Type**: `(G : CrossingGeometry γ s) {t : ℝ} (ht : t ∈ Icc 0 1) : normFn γ s t = 0 ↔ t = G.t₀`
- **What**: On `[0,1]`, the unique zero of `normFn γ s` is `t₀`.
- **How**: Apply `normFn_zero_iff_eq`; the forward direction uses `G.unique_crossing`; the reverse substitutes `t = t₀` and applies `G.cross`.
- **Hypotheses**: `t ∈ Icc 0 1`.
- **Uses from project**: `CrossingGeometry`, `normFn`, `normFn_zero_iff_eq`.
- **Used by**: `exists_farMin_pos`.
- **Visibility**: private
- **Lines**: 138–144
- **Notes**: none

### `theorem CrossingGeometry.exists_farMin_pos`
- **Type**: `(G : CrossingGeometry γ s) {r : ℝ} (hr_pos : 0 < r) (hr_lt : r < min G.t₀ (1 - G.t₀)) : ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Icc 0 1, r ≤ |t - G.t₀| → m ≤ normFn γ s t`
- **What**: For `r > 0` small enough that `[t₀ − r, t₀ + r] ⊆ (0,1)`, `‖γ − s‖` attains a positive minimum on the complement `K := {t ∈ [0,1] : r ≤ |t - t₀|}`.
- **How**: Define `K` as a setOf; show closed (intersection of `isClosed_Icc` with `{t | r ≤ |t - t₀|}`, the latter via `isClosed_le continuous_const ((continuous_id.sub continuous_const).abs)`); show compact via `IsCompact.of_isClosed_subset`. Show `K` nonempty: `0 ∈ K` since `|0 - t₀| = t₀ > r`. Apply `IsCompact.exists_isMinOn` to `normFn` on `K`. Show the minimiser satisfies `t_min ≠ t₀` (since `|t_min − t₀| ≥ r > 0`); conclude `normFn t_min ≠ 0` via `normFn_eq_zero_iff`; positivity follows from `norm_nonneg` and `lt_of_le_of_ne`. (~38 lines.)
- **Hypotheses**: `0 < r`, `r < min t₀ (1-t₀)`.
- **Uses from project**: `CrossingGeometry`, `normFn`, `normFn_continuous`, `normFn_eq_zero_iff`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 149–186
- **Notes**: >30 lines; uses `classical`

### `theorem CrossingGeometry.normFn_tendsto_zero`
- **Type**: `(G : CrossingGeometry γ s) : Tendsto (normFn γ s) (𝓝 G.t₀) (𝓝 0)`
- **What**: `‖γ(t) − s‖ → 0` as `t → t₀`.
- **How**: Use `normFn_continuous` to extract `Tendsto (normFn γ s) (𝓝 t₀) (𝓝 (normFn γ s t₀))`; show `normFn γ s t₀ = 0` via `normFn_zero_iff_eq` and `G.cross`.
- **Hypotheses**: none beyond `CrossingGeometry`.
- **Uses from project**: `CrossingGeometry`, `normFn`, `normFn_continuous`, `normFn_zero_iff_eq`.
- **Used by**: `exists_near_delta`.
- **Visibility**: public
- **Lines**: 195–202
- **Notes**: none

### `theorem CrossingGeometry.exists_near_delta`
- **Type**: `(G : CrossingGeometry γ s) {ε : ℝ} (hε_pos : 0 < ε) : ∃ δ, 0 < δ ∧ δ < min G.t₀ (1 - G.t₀) ∧ ∀ t, |t - G.t₀| ≤ δ → normFn γ s t ≤ ε`
- **What**: For each `ε > 0`, there exists `δ > 0` (smaller than the distance from `t₀` to the boundary) so that `‖γ(t) - s‖ ≤ ε` for all `t` within `δ` of `t₀`.
- **How**: From `normFn_tendsto_zero` and `Metric.tendsto_nhds_nhds`, get `δ' > 0`. Define `M := min t₀ (1-t₀)` (positive from `G.ht₀`). Set `δ := min (δ'/2) (M/2)`; show δ < M via `min_le_right` + `half_lt_self`. For `t` with `|t - t₀| ≤ δ`, transport to `δ' / 2 < δ'` and apply continuity bound (with `dist_eq_norm`); `abs_of_nonneg` handles the nonnegativity. (~30 lines.)
- **Hypotheses**: `0 < ε`.
- **Uses from project**: `CrossingGeometry`, `normFn`, `normFn_tendsto_zero`.
- **Used by**: `exists_near_delta_lt`.
- **Visibility**: public
- **Lines**: 206–235
- **Notes**: >10 lines; uses `classical`

### `theorem CrossingGeometry.exists_near_delta_lt`
- **Type**: `(G : CrossingGeometry γ s) {ε : ℝ} (hε_pos : 0 < ε) : ∃ δ, 0 < δ ∧ δ < min G.t₀ (1 - G.t₀) ∧ ∀ t, |t - G.t₀| ≤ δ → normFn γ s t < ε`
- **What**: Strict variant of `exists_near_delta`: `‖γ(t) − s‖ < ε` instead of `≤ ε`.
- **How**: Apply `exists_near_delta` to `ε/2`; conclude `< ε` via `linarith` (since `normFn γ s t ≤ ε/2 < ε`).
- **Hypotheses**: `0 < ε`.
- **Uses from project**: `CrossingGeometry`, `normFn`, `exists_near_delta`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 244–250
- **Notes**: none

### `def SingleCrossingData.ofGeometryAndFTC`
- **Type**: `(γ : ClosedPwC1Immersion x) (s : ℂ) (G : CrossingGeometry γ s) (L : ℂ) (δ : ℝ → ℝ) (threshold : ℝ) (hthresh : 0 < threshold) (hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε) (hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min G.t₀ (1 - G.t₀)) (h_far : ∀ ε, 0 < ε → ε < threshold → ∀ t ∈ Icc 0 1, δ ε < |t - G.t₀| → ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path t - s‖) (h_near : ∀ ε, 0 < ε → ε < threshold → ∀ t, |t - G.t₀| ≤ δ ε → ‖γ.toPwC1Immersion.toPiecewiseC1Path t - s‖ ≤ ε) (ftcHyp : ArcFTCHyp γ.toPwC1Immersion.toPiecewiseC1Path s G.t₀ δ threshold L) : SingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s`
- **What**: Constructor for `SingleCrossingData` packaging a `CrossingGeometry`, the user-supplied δ-function/threshold/near-far bounds, and an `ArcFTCHyp`. Routes uniqueness through `CrossingGeometry` and exposes `t₀`, `δ`, FTC fields.
- **How**: Structure-literal — copies field-by-field: `t₀ := G.t₀`, `ht₀ := G.ht₀`, geometric fields from the explicit hypotheses, and the FTC fields (`E`, `h_ftc`, `hint_left`, `hint_right`, `h_limit`) from the supplied `ArcFTCHyp`.
- **Hypotheses**: `CrossingGeometry γ s`, a δ-function with near/far/positivity bounds inside a positive threshold, and an `ArcFTCHyp`.
- **Uses from project**: `CrossingGeometry`, `SingleCrossingData`, `ClosedPwC1Immersion`, `PwC1Immersion`, `PiecewiseC1Path`, `ArcFTCHyp`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 307–332
- **Notes**: >10 lines (structure construction with 14 named fields)

## File Summary
- 13 declarations: 1 `structure` (`CrossingGeometry`), 4 internal private definitions/lemmas (`γE`, `normFn`, `normFn_continuous`, `normFn_zero_iff_eq`, `normFn_eq_zero_iff` — 5 private items), 5 public theorems (`toIsCrossed`, `of_isCrossed_unique`, `exists_farMin_pos`, `normFn_tendsto_zero`, `exists_near_delta`, `exists_near_delta_lt`), and the constructor `SingleCrossingData.ofGeometryAndFTC`.
- All proofs sorry-free; no axioms; no `set_option`; in `noncomputable section` under `namespace LeanModularForms`.
- Two larger proofs (>10 lines) use `classical` and `IsCompact.exists_isMinOn` / `Metric.tendsto_nhds_nhds` patterns.
- Strategy: `CrossingGeometry` packages uniqueness + transversality; the file derives geometric near/far bounds via compactness + continuity but stops short of fully automating δ(ε) — leaves it to the user via `ofGeometryAndFTC`.
- Imports: `PaperPwC1Immersion`, `SingleCrossing`, `WindingWeightProofs`, `HW33LaurentPolarPart`.
