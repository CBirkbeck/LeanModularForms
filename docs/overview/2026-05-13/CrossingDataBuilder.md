# CrossingDataBuilder.lean — Declaration Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HungerbuhlerWasem/CrossingDataBuilder.lean` (1733 lines).

Namespace: `HungerbuhlerWasem`.

---

### `theorem exists_far_bound_compact`
- **Type**: `(γ : ℝ → ℂ) (hγ : Continuous γ) (s : ℂ) (t₀ : ℝ) (h_unique : ∀ t ∈ Icc 0 1, γ t = s → t = t₀) {r : ℝ} (hr_pos : 0 < r) (hr_lt₀ : r ≤ t₀) (hr_lt₁ : r ≤ 1 - t₀) → ∃ m > 0, (∀ t ∈ Icc 0 (t₀ - r), m ≤ ‖γ t - s‖) ∧ (∀ t ∈ Icc (t₀ + r) 1, m ≤ ‖γ t - s‖)`
- **What**: A uniqueness-based far bound: if `γ` reaches `s` only at `t₀` on `[0,1]`, then `‖γ - s‖` is bounded below by a positive constant on the compact complement of an `r`-neighborhood.
- **How**: Apply `IsCompact.exists_isMinOn` to the continuous function `t ↦ ‖γ t - s‖` on each of `Icc 0 (t₀-r)` and `Icc (t₀+r) 1`; use `h_unique` to derive positivity from `norm_pos_iff`/`sub_ne_zero`; take `min` of the two bounds.
- **Hypotheses**: `γ` continuous, `s` reached only at `t₀`, `r` is in `(0, min t₀ (1-t₀)]`.
- **Uses from project**: []
- **Used by**: `exists_right_cutoff`, `exists_left_cutoff`.
- **Visibility**: public
- **Lines**: 99–153
- **Notes**: proof >30 lines

### `theorem exists_right_deriv_limit`
- **Type**: `(γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 1) → ∃ L ≠ 0, Tendsto (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend) (𝓝[>] t₀) (𝓝 L)`
- **What**: At any interior parameter `t₀`, a closed piecewise-`C¹` immersion has a nonzero right one-sided derivative limit.
- **How**: Case-split on whether `t₀` lies on the partition: in the on-partition case use `PwC1Immersion.right_deriv_limit`; off-partition use continuity of `deriv` (`deriv_continuous_off`) and `deriv_ne_zero` for the immersion.
- **Hypotheses**: `γ` a closed piecewise-`C¹` immersion, `t₀ ∈ Ioo 0 1`.
- **Uses from project**: `ClosedPwC1Immersion`, `PwC1Immersion.right_deriv_limit`, `PiecewiseC1Path.deriv_continuous_off`, `PwC1Immersion.deriv_ne_zero`.
- **Used by**: `exists_right_cutoff`.
- **Visibility**: public
- **Lines**: 157–171

### `theorem exists_left_deriv_limit`
- **Type**: Symmetric to `exists_right_deriv_limit` for `𝓝[<] t₀`.
- **What**: At any interior parameter `t₀`, a closed piecewise-`C¹` immersion has a nonzero left one-sided derivative limit.
- **How**: Same structure as `exists_right_deriv_limit`: case-split on partition membership; for off-partition use `deriv_continuous_off`+`deriv_ne_zero`.
- **Hypotheses**: `γ : ClosedPwC1Immersion x`, `t₀ ∈ Ioo 0 1`.
- **Uses from project**: `ClosedPwC1Immersion`, `PwC1Immersion.left_deriv_limit`, `PiecewiseC1Path.deriv_continuous_off`, `PwC1Immersion.deriv_ne_zero`.
- **Used by**: `exists_left_cutoff`.
- **Visibility**: public
- **Lines**: 173–187

### `theorem eventually_differentiable_right`
- **Type**: `(γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 1) → ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t`
- **What**: Differentiability of the extend of `γ` holds eventually on `𝓝[>] t₀` (off the finite partition set away from `t₀`).
- **How**: Build the closed set `(partition \ {t₀})` (finite, hence closed), then `filter_upwards` with its complement, an `Ioo` neighborhood, and `self_mem_nhdsWithin`, applying `PiecewiseC1Path.differentiable_off`.
- **Hypotheses**: `γ` a closed piecewise-`C¹` immersion, `t₀` interior.
- **Uses from project**: `PiecewiseC1Path.differentiable_off`.
- **Used by**: `exists_right_cutoff`.
- **Visibility**: public
- **Lines**: 191–205

### `theorem eventually_differentiable_left`
- **Type**: Symmetric to `eventually_differentiable_right` for `𝓝[<] t₀`.
- **What**: Differentiability of the extend of `γ` holds eventually on `𝓝[<] t₀`.
- **How**: Identical structure: complement of `partition \ {t₀}`, plus an `Ioo` neighborhood, plus `self_mem_nhdsWithin`.
- **Hypotheses**: same as `eventually_differentiable_right`.
- **Uses from project**: `PiecewiseC1Path.differentiable_off`.
- **Used by**: `exists_left_cutoff`.
- **Visibility**: public
- **Lines**: 207–221

### `theorem chord_lower_bound_right_eventually`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s) {L : ℂ} (hL : L ≠ 0) (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)) (hγ_cont : ContinuousAt γ t₀) (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t) → ∀ᶠ t in 𝓝[>] t₀, (‖L‖/2) * (t - t₀) ≤ ‖γ t - s‖`
- **What**: Eventually `‖γ(t)−s‖ ≥ (‖L‖/2)(t−t₀)` from the right, using a chord-to-tangent estimate.
- **How**: Use `hasDerivWithinAt_iff_isLittleO` for the right-side derivative and reverse triangle inequality `norm_sub_norm_le`: bound `(t-t₀)‖L‖` minus the `o(t-t₀)` error from below.
- **Hypotheses**: γ continuous and eventually differentiable on the right with derivative tending to `L ≠ 0`, `γ(t₀)=s`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 234–273
- **Notes**: proof >30 lines

### `theorem chord_upper_bound_right_eventually`
- **Type**: Symmetric upper bound version: `∀ᶠ t in 𝓝[>] t₀, ‖γ t - s‖ ≤ (3‖L‖/2)(t - t₀)`.
- **What**: Eventually `‖γ(t)−s‖ ≤ (3‖L‖/2)(t−t₀)` from the right.
- **How**: Triangle inequality `norm_add_le` plus the `o(t-t₀)` little-o bound from `hasDerivWithinAt_iff_isLittleO`.
- **Hypotheses**: same as `chord_lower_bound_right_eventually`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 277–308
- **Notes**: proof >30 lines

### `theorem chord_lower_bound_left_eventually`
- **Type**: Symmetric to `chord_lower_bound_right_eventually` for `𝓝[<] t₀`, with `(t₀ - t)`.
- **What**: Eventually `‖γ(t)−s‖ ≥ (‖L‖/2)(t₀−t)` from the left.
- **How**: Same chord-to-tangent argument as right-side, using `hasDerivWithinAt_Iio_iff_Iic`/`hasDerivWithinAt_Iic_of_tendsto_deriv`.
- **Hypotheses**: γ has nonzero left derivative limit `L`, continuous at `t₀`, eventually differentiable on the left, `γ(t₀)=s`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 312–348
- **Notes**: proof >30 lines

### `theorem chord_upper_bound_left_eventually`
- **Type**: Symmetric upper bound `∀ᶠ t in 𝓝[<] t₀, ‖γ t - s‖ ≤ (3‖L‖/2)(t₀ - t)`.
- **What**: Eventually `‖γ(t)−s‖ ≤ (3‖L‖/2)(t₀−t)` from the left.
- **How**: Triangle inequality + little-o bound, symmetric to right version.
- **Hypotheses**: same as `chord_lower_bound_left_eventually`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 352–383

### `def reInner`
- **Type**: `(z w : ℂ) : ℝ := z.re * w.re + z.im * w.im`
- **What**: Real inner product of two complex numbers viewed as ℝ² (equal to `Re(z·conj w)`).
- **How**: Definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `reInner_le_norm_mul_norm`, `reInner_add_left`, `reInner_add_right`, `reInner_smul_left`, `reInner_self`, `reInner_eq_inner_real`, `reInner_lower_bound_right_eventually`, `reInner_upper_bound_left_eventually`, `norm_sub_strictMonoOn_right`, `norm_sub_strictAntiOn_left`.
- **Visibility**: private
- **Lines**: 395

### `lemma reInner_le_norm_mul_norm`
- **Type**: `(z w : ℂ) → |reInner z w| ≤ ‖z‖ * ‖w‖`
- **What**: Cauchy–Schwarz bound for `reInner`.
- **How**: Identify `reInner z w = (z · conj w).re`, then use `Complex.abs_re_le_norm` and `‖z·conj w‖ = ‖z‖·‖w‖`.
- **Hypotheses**: none.
- **Uses from project**: `reInner`.
- **Used by**: `reInner_lower_bound_right_eventually`, `reInner_upper_bound_left_eventually`.
- **Visibility**: private
- **Lines**: 397–406

### `lemma reInner_add_left`
- **Type**: `(a b c : ℂ) → reInner (a + b) c = reInner a c + reInner b c`
- **What**: Additivity of `reInner` in the first argument.
- **How**: Unfold + `simp [Complex.add_re, Complex.add_im]` + `ring`.
- **Hypotheses**: none.
- **Uses from project**: `reInner`.
- **Used by**: `reInner_lower_bound_right_eventually`, `reInner_upper_bound_left_eventually`.
- **Visibility**: private
- **Lines**: 408–411

### `lemma reInner_add_right`
- **Type**: `(a b c : ℂ) → reInner a (b + c) = reInner a b + reInner a c`
- **What**: Additivity of `reInner` in the second argument.
- **How**: Same as `reInner_add_left`.
- **Hypotheses**: none.
- **Uses from project**: `reInner`.
- **Used by**: `reInner_lower_bound_right_eventually`, `reInner_upper_bound_left_eventually`.
- **Visibility**: private
- **Lines**: 413–416

### `lemma reInner_smul_left`
- **Type**: `(r : ℝ) (a c : ℂ) → reInner (r • a) c = r * reInner a c`
- **What**: Real-scalar homogeneity of `reInner` in the first argument.
- **How**: Unfold + `Complex.real_smul`/`Complex.mul_re`/`Complex.mul_im` + `ring`.
- **Hypotheses**: none.
- **Uses from project**: `reInner`.
- **Used by**: `reInner_lower_bound_right_eventually`, `reInner_upper_bound_left_eventually`.
- **Visibility**: private
- **Lines**: 418–423

### `lemma reInner_self`
- **Type**: `(z : ℂ) → reInner z z = ‖z‖^2`
- **What**: Self-inner-product equals squared norm.
- **How**: Unfold and rewrite via `Complex.normSq_eq_norm_sq`/`Complex.normSq_apply`.
- **Hypotheses**: none.
- **Uses from project**: `reInner`.
- **Used by**: `reInner_lower_bound_right_eventually`, `reInner_upper_bound_left_eventually`.
- **Visibility**: private
- **Lines**: 425–429

### `theorem reInner_lower_bound_right_eventually`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s) {L : ℂ} (hL : L ≠ 0) (hL_right : ...) (hγ_cont : ContinuousAt γ t₀) (hγ_diff : ...) → ∀ᶠ t in 𝓝[>] t₀, (t - t₀) * ‖L‖^2 / 2 ≤ reInner (γ t - s) (deriv γ t)`
- **What**: Key right-side positive-derivative bound: the inner product `Re((γ(t)−s)·conj(γ'(t)))` is bounded below by `(t−t₀)·‖L‖²/2` near `t₀`.
- **How**: Set `η = ‖L‖/8`, decompose `γ(t)-s = (t-t₀)•L + R` (chord remainder, `‖R‖ ≤ η(t-t₀)`) and `deriv γ t = L + D` (`‖D‖ ≤ η`); expand `reInner` via bilinearity (using `reInner_add_left`, `reInner_add_right`, `reInner_smul_left`, `reInner_self`) and bound each error term by `reInner_le_norm_mul_norm`. Solve via `nlinarith`/`linarith`.
- **Hypotheses**: γ has right derivative limit `L ≠ 0` and is eventually differentiable; `γ(t₀)=s`.
- **Uses from project**: `reInner`, `reInner_le_norm_mul_norm`, `reInner_add_left`, `reInner_add_right`, `reInner_smul_left`, `reInner_self`.
- **Used by**: `norm_sub_strictMonoOn_right`.
- **Visibility**: private
- **Lines**: 439–527
- **Notes**: proof >30 lines (heavy `nlinarith` use)

### `lemma reInner_eq_inner_real`
- **Type**: `(z w : ℂ) → reInner z w = inner ℝ w z`
- **What**: Identifies `reInner` with the real inner product `⟪w, z⟫_ℝ` on ℂ as a real inner-product space.
- **How**: Unfold `reInner` and `Inner.rclikeToReal`, identify `(z · conj w).re` with `z.re * w.re + z.im * w.im` via `Complex.mul_re`/`Complex.conj_re/im`.
- **Hypotheses**: none.
- **Uses from project**: `reInner`.
- **Used by**: `norm_sub_strictMonoOn_right`, `norm_sub_strictAntiOn_left`.
- **Visibility**: private
- **Lines**: 532–541

### `theorem norm_sub_strictMonoOn_right`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s) {L : ℂ} (hL : L ≠ 0) (hL_right : ...) (hγ_cont : ...) (hγ_diff : ...) → ∃ r > 0, StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + r))`
- **What**: Strict monotonicity of `‖γ(t)-s‖` on a right-neighborhood `[t₀, t₀+r]`.
- **How**: Combine `reInner_lower_bound_right_eventually` (positive derivative) with `eventually_nhdsWithin_iff` to extract a radius `r₀` of validity, then apply `strictMonoOn_of_hasDerivWithinAt_pos` using `HasDerivAt.norm_sq` on `‖γ-s‖²` (derivative is `2·reInner((γ-s),γ')`), and convert via `reInner_eq_inner_real`. Finally lift squared strict mono to strict mono via `lt_of_pow_lt_pow_left₀`.
- **Hypotheses**: γ has right derivative limit `L ≠ 0`, eventually differentiable, `γ(t₀)=s`.
- **Uses from project**: `reInner_lower_bound_right_eventually`, `reInner`, `reInner_eq_inner_real`.
- **Used by**: `exists_right_cutoff`.
- **Visibility**: public
- **Lines**: 548–624
- **Notes**: proof >30 lines, key strict-mono lemma

### `theorem reInner_upper_bound_left_eventually`
- **Type**: Symmetric to `reInner_lower_bound_right_eventually`, with `≤ (t-t₀)·‖L‖²/2` (negative) on `𝓝[<] t₀`.
- **What**: Left-side negative-derivative bound: `reInner(γ(t)-s, γ'(t)) ≤ (t-t₀)·‖L‖²/2 < 0`.
- **How**: Same decomposition strategy as the right version, with `(t-t₀) < 0` so leading term is negative; tracks `(t₀-t) > 0` as the positive parameter for error bounds. Uses `nlinarith`.
- **Hypotheses**: γ has left derivative limit `L ≠ 0`, eventually differentiable on the left, `γ(t₀)=s`.
- **Uses from project**: `reInner`, `reInner_le_norm_mul_norm`, `reInner_add_left`, `reInner_add_right`, `reInner_smul_left`, `reInner_self`.
- **Used by**: `norm_sub_strictAntiOn_left`.
- **Visibility**: private
- **Lines**: 630–701
- **Notes**: proof >30 lines

### `theorem norm_sub_strictAntiOn_left`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s) {L : ℂ} (hL : L ≠ 0) (hL_left : ...) (hγ_cont : ...) (hγ_diff : ...) → ∃ r > 0, StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - r) t₀)`
- **What**: Strict anti-monotonicity of `‖γ(t)-s‖` on a left-neighborhood `[t₀-r, t₀]`.
- **How**: Symmetric to `norm_sub_strictMonoOn_right`: extract validity radius from `reInner_upper_bound_left_eventually`, apply `strictAntiOn_of_hasDerivWithinAt_neg`, use `reInner_eq_inner_real`, lift via `lt_of_pow_lt_pow_left₀`.
- **Hypotheses**: same as `reInner_upper_bound_left_eventually`.
- **Uses from project**: `reInner_upper_bound_left_eventually`, `reInner`, `reInner_eq_inner_real`.
- **Used by**: `exists_left_cutoff`.
- **Visibility**: public
- **Lines**: 707–776
- **Notes**: proof >30 lines

### `theorem strict_mono_inverse_exists`
- **Type**: `(f : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (hf₀ : f 0 = 0) (hf_strict : StrictMonoOn f (Icc 0 r)) (hf_cont : ContinuousOn f (Icc 0 r)) → ∀ ε ∈ Ioo 0 (f r), ∃! τ : ℝ, τ ∈ Ioo 0 r ∧ f τ = ε`
- **What**: For a strictly monotone continuous `f: [0, r] → ℝ` with `f(0)=0`, every `ε ∈ (0, f r)` has a unique preimage `τ ∈ (0, r)` (IVT-style inverse).
- **How**: `intermediate_value_Ioo` gives existence; `StrictMonoOn.injOn` gives uniqueness.
- **Hypotheses**: as in signature.
- **Uses from project**: []
- **Used by**: `exists_right_cutoff`, `exists_left_cutoff`.
- **Visibility**: private
- **Lines**: 787–804

### `structure DerivedAsymmetricCutoffs`
- **Type**: `(γ : ClosedPwC1Immersion x) (s : ℂ) (t₀ : ℝ)`-parameterized record containing two side-cutoffs `δ_left, δ_right : ℝ → ℝ`, a positive `threshold`, positivity/smallness, and `h_far_*`/`h_near_*` bounds (14 fields).
- **What**: Bundled "geometric scaffolding" for an asymmetric single crossing: per-side level-set cutoffs and far/near bounds for `‖γ(t)-s‖` versus `ε`.
- **How**: structure declaration.
- **Hypotheses**: as in type signature.
- **Uses from project**: `ClosedPwC1Immersion`, `PwC1Immersion`, `PiecewiseC1Path`.
- **Used by**: `deriveAsymmetricCutoffs_anywhere`, `deriveAsymmetricCutoffs`, `AsymmetricSingleCrossingData.ofDerivedCutoffs`, `AsymmetricSingleCrossingData.ofClosedImmersion_flat_one_derived`, `cutoff_integral_eq_outer_sum`, `AsymmetricArcFTCHyp.ofHasCauchyPV`, `AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV`, `AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV_anywhere`.
- **Visibility**: public
- **Lines**: 818–842

### `theorem exists_right_cutoff`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ} (ht₀_Ioo : t₀ ∈ Ioo 0 1) (h_at : ...) (h_unique : ...) → ∃ (δ_right : ℝ → ℝ) (threshold : ℝ), 0 < threshold ∧ (positivity) ∧ (smallness) ∧ (h_far_right) ∧ (h_near_right)`
- **What**: Derive a right-side cutoff function `δ_right` with positive threshold satisfying the `h_far_right`/`h_near_right` axioms, from strict monotonicity + compact far bound.
- **How**: Build `f(τ) = ‖γ(t₀+τ)-s‖` on `[0,r]` (continuous + strict mono via `norm_sub_strictMonoOn_right`); use `strict_mono_inverse_exists` to invert (via `Classical.choose`) and obtain `δ_right`; the `threshold` is `min (f r) m` where `m` comes from `exists_far_bound_compact`.
- **Hypotheses**: `γ` closed pw-`C¹` immersion crossing `s` only at `t₀ ∈ Ioo 0 1`.
- **Uses from project**: `exists_right_deriv_limit`, `eventually_differentiable_right`, `norm_sub_strictMonoOn_right`, `exists_far_bound_compact`, `strict_mono_inverse_exists`, `ClosedPwC1Immersion`.
- **Used by**: `deriveAsymmetricCutoffs_anywhere`, `deriveAsymmetricCutoffs`.
- **Visibility**: private
- **Lines**: 848–995
- **Notes**: proof >30 lines (largest in file, uses `classical`)

### `theorem exists_left_cutoff`
- **Type**: Symmetric to `exists_right_cutoff`, producing `δ_left` with `h_far_left`/`h_near_left`.
- **What**: Derive a left-side cutoff function `δ_left` satisfying far/near bounds.
- **How**: Symmetric to `exists_right_cutoff`: `f(τ) = ‖γ(t₀-τ)-s‖` on `[0,r]`, monotone because anti-mono of `‖γ(·)-s‖` flips signs; invert via `strict_mono_inverse_exists` and add the compact far bound.
- **Hypotheses**: same as `exists_right_cutoff`.
- **Uses from project**: `exists_left_deriv_limit`, `eventually_differentiable_left`, `norm_sub_strictAntiOn_left`, `exists_far_bound_compact`, `strict_mono_inverse_exists`, `ClosedPwC1Immersion`.
- **Used by**: `deriveAsymmetricCutoffs_anywhere`, `deriveAsymmetricCutoffs`.
- **Visibility**: private
- **Lines**: 999–1143
- **Notes**: proof >30 lines

### `def deriveAsymmetricCutoffs_anywhere`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ} (ht₀_Ioo) (h_at) (h_unique) → DerivedAsymmetricCutoffs γ s t₀`
- **What**: Corner-friendly version of `deriveAsymmetricCutoffs`: bundles `exists_right_cutoff` and `exists_left_cutoff` into a single `DerivedAsymmetricCutoffs` without requiring off-partition.
- **How**: Unfold both existential statements via `.choose`/`.choose_spec`, take `min` of thresholds.
- **Hypotheses**: γ crosses `s` only at `t₀ ∈ Ioo 0 1`.
- **Uses from project**: `exists_right_cutoff`, `exists_left_cutoff`, `DerivedAsymmetricCutoffs`.
- **Used by**: `AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV_anywhere`.
- **Visibility**: public (noncomputable)
- **Lines**: 1150–1186
- **Notes**: proof >30 lines

### `def deriveAsymmetricCutoffs`
- **Type**: As `deriveAsymmetricCutoffs_anywhere` plus extra `_h_part_off` hypothesis (unused; same body).
- **What**: Same as `deriveAsymmetricCutoffs_anywhere`; the unused `_h_part_off` is retained for legacy callers using off-partition flatness as a precondition.
- **How**: Same construction; `_h_part_off` is ignored.
- **Hypotheses**: same as `_anywhere` + ignored partition-off hypothesis.
- **Uses from project**: `exists_right_cutoff`, `exists_left_cutoff`, `DerivedAsymmetricCutoffs`.
- **Used by**: `AsymmetricSingleCrossingData.ofClosedImmersion_flat_one_derived`, `AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV`.
- **Visibility**: public (noncomputable)
- **Lines**: 1191–1228
- **Notes**: proof >30 lines; duplicates `_anywhere`

### `def AsymmetricSingleCrossingData.ofDerivedCutoffs`
- **Type**: `{γ : ClosedPwC1Immersion x} {s t₀ L} (D : DerivedAsymmetricCutoffs γ s t₀) (ftcHyp : AsymmetricArcFTCHyp γ.toPwC1Immersion.toPiecewiseC1Path s t₀ D.δ_left D.δ_right D.threshold L) → AsymmetricSingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s`
- **What**: Combine derived geometric cutoffs (from `DerivedAsymmetricCutoffs`) with FTC analytic content (from `AsymmetricArcFTCHyp`) into the full `AsymmetricSingleCrossingData`.
- **How**: Structure constructor; extracts `ht₀` from the smallness fields at `ε = threshold/2` via `linarith`. All other fields are inherited from `D` / `ftcHyp`.
- **Hypotheses**: bundled cutoffs and FTC hypothesis matching.
- **Uses from project**: `DerivedAsymmetricCutoffs`, `AsymmetricArcFTCHyp`, `AsymmetricSingleCrossingData`, `ClosedPwC1Immersion`.
- **Used by**: `AsymmetricSingleCrossingData.ofClosedImmersion_flat_one_derived`, `AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV`, `AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV_anywhere`.
- **Visibility**: public
- **Lines**: 1236–1273

### `def AsymmetricSingleCrossingData.ofClosedImmersion_flat_one_derived`
- **Type**: `(γ : ClosedPwC1Immersion x) {s t₀} (ht₀_Ioo) (h_at) (h_unique) (h_part_off) {L} (mkFTCHyp : (D : DerivedAsymmetricCutoffs γ s t₀) → AsymmetricArcFTCHyp ...) → AsymmetricSingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s`
- **What**: Headline asymmetric builder: from immersion data + a user-supplied FTC factory depending on the derived cutoffs, build the full structure.
- **How**: Call `deriveAsymmetricCutoffs` to make `D`, then `ofDerivedCutoffs D (mkFTCHyp D)`.
- **Hypotheses**: as in signature.
- **Uses from project**: `deriveAsymmetricCutoffs`, `AsymmetricSingleCrossingData.ofDerivedCutoffs`, `ClosedPwC1Immersion`, `DerivedAsymmetricCutoffs`, `AsymmetricArcFTCHyp`.
- **Used by**: unused in file
- **Visibility**: public (noncomputable)
- **Lines**: 1295–1308

### `def SingleCrossingData.ofClosedImmersion_flat_one`
- **Type**: `(γ : ClosedPwC1Immersion x) {s t₀} (ht₀_Ioo) (_h_at) (_h_unique) (_h_flat) (L : ℂ) (δ : ℝ → ℝ) (threshold) (hthresh) (hδ_pos) (hδ_small) (h_far) (h_near) (ftcHyp : ArcFTCHyp ...) → SingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s`
- **What**: Symmetric-cutoff builder for `SingleCrossingData` from immersion + flatness + uniqueness, given a single cutoff `δ`.
- **How**: Structure constructor; copies fields from inputs.
- **Hypotheses**: as in signature.
- **Uses from project**: `ClosedPwC1Immersion`, `SingleCrossingData`, `ArcFTCHyp`, `IsFlatOfOrder`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1324–1359

### `def AsymmetricSingleCrossingData.ofClosedImmersion_flat_one`
- **Type**: Asymmetric counterpart to `SingleCrossingData.ofClosedImmersion_flat_one`: caller supplies `δ_left, δ_right, threshold, h_far_*, h_near_*` plus an `AsymmetricArcFTCHyp`.
- **What**: Build `AsymmetricSingleCrossingData` from explicit asymmetric cutoffs and analytic content.
- **How**: Delegate to `AsymmetricSingleCrossingData.mk_from_bounds`.
- **Hypotheses**: as in signature.
- **Uses from project**: `ClosedPwC1Immersion`, `AsymmetricSingleCrossingData.mk_from_bounds`, `AsymmetricArcFTCHyp`, `IsFlatOfOrder`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1384–1416

### `theorem inv_sub_mul_deriv_intervalIntegrable`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {a b : ℝ} (hab : a ≤ b) (h_in_Icc : Icc a b ⊆ Icc 0 1) (h_ne : ∀ t ∈ Icc a b, γ ... ≠ s) → IntervalIntegrable (fun t => (γ... t - s)⁻¹ * deriv γ... t) volume a b`
- **What**: The integrand `(γ-s)⁻¹·γ'` is interval-integrable on `[a, b]` when `γ` avoids `s` on that interval.
- **How**: Use `ClosedPwC1Curve.deriv_extend_intervalIntegrable` for `γ'` integrability and `ContinuousOn.inv₀` for continuity of `(γ-s)⁻¹`; combine via `IntervalIntegrable.mul_continuousOn` and reorder factors with `congr` + `ring`.
- **Hypotheses**: `Icc a b ⊆ Icc 0 1`, γ avoids `s` on `[a,b]`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Curve.deriv_extend_intervalIntegrable`, `PiecewiseC1Path`.
- **Used by**: `inv_sub_mul_deriv_intervalIntegrable_left`, `inv_sub_mul_deriv_intervalIntegrable_right`.
- **Visibility**: public
- **Lines**: 1441–1473

### `theorem inv_sub_mul_deriv_intervalIntegrable_left`
- **Type**: Specialisation to `(0, t₀ - δ_left_ε)` interval.
- **What**: The integrand is interval-integrable on `[0, t₀ - δ_left ε]` given uniqueness and `δ_left ε < t₀`.
- **How**: Apply `inv_sub_mul_deriv_intervalIntegrable` after showing γ ≠ s via `h_unique`.
- **Hypotheses**: `0 < δ_left_ε < t₀`, uniqueness of crossing at `t₀`.
- **Uses from project**: `inv_sub_mul_deriv_intervalIntegrable`, `ClosedPwC1Immersion`.
- **Used by**: `cutoff_integral_eq_outer_sum`, `AsymmetricArcFTCHyp.ofHasCauchyPV`.
- **Visibility**: public
- **Lines**: 1478–1498

### `theorem inv_sub_mul_deriv_intervalIntegrable_right`
- **Type**: Specialisation to `(t₀ + δ_right_ε, 1)` interval.
- **What**: Symmetric of `_left`: integrand integrable on `[t₀ + δ_right ε, 1]`.
- **How**: Same structure; uses `inv_sub_mul_deriv_intervalIntegrable` with the right-side `Icc`.
- **Hypotheses**: `0 < δ_right_ε < 1 - t₀`, uniqueness.
- **Uses from project**: `inv_sub_mul_deriv_intervalIntegrable`, `ClosedPwC1Immersion`.
- **Used by**: `cutoff_integral_eq_outer_sum`, `AsymmetricArcFTCHyp.ofHasCauchyPV`.
- **Visibility**: public
- **Lines**: 1501–1521

### `theorem cutoff_integral_eq_outer_sum`
- **Type**: `(γ) {s t₀} (ht₀_Ioo) (D : DerivedAsymmetricCutoffs γ s t₀) (h_unique) {ε} (hε_pos) (hε_lt) → ∫ t in 0..1, cpvIntegrand (·-s)⁻¹ γ s ε t = (∫ t in 0..(t₀ - D.δ_left ε), ...) + (∫ t in (t₀ + D.δ_right ε)..1, ...)`
- **What**: The cutoff CPV integral equals the sum of "outer" integrals (left of `t₀ - δ_left ε` and right of `t₀ + δ_right ε`), since the middle is zero.
- **How**: Decompose into three pieces using `intervalIntegral.integral_add_adjacent_intervals` after showing the cpvIntegrand equals `(γ-s)⁻¹·γ'` a.e. on the outer pieces (via `h_far_*`) and equals 0 on the middle piece (via `h_near_*`); use the integrability lemmas to invoke `congr_ae`. Key lemmas: `intervalIntegral.integral_zero_ae`, `intervalIntegral.integral_congr_ae`.
- **Hypotheses**: ε in `(0, threshold)`, uniqueness of crossing, derived cutoffs.
- **Uses from project**: `DerivedAsymmetricCutoffs`, `inv_sub_mul_deriv_intervalIntegrable_left`, `inv_sub_mul_deriv_intervalIntegrable_right`, `cpvIntegrand`, `ClosedPwC1Immersion`.
- **Used by**: `AsymmetricArcFTCHyp.ofHasCauchyPV`.
- **Visibility**: public
- **Lines**: 1527–1630
- **Notes**: proof >30 lines, uses `classical`

### `def AsymmetricArcFTCHyp.ofHasCauchyPV`
- **Type**: `{γ s t₀} (ht₀_Ioo) (D : DerivedAsymmetricCutoffs γ s t₀) (h_unique) {L} (hCPV : HasCauchyPV (·-s)⁻¹ γ s L) → AsymmetricArcFTCHyp γ s t₀ D.δ_left D.δ_right D.threshold L`
- **What**: Construct `AsymmetricArcFTCHyp` (analytic FTC oracle) from a single `HasCauchyPV` hypothesis plus the geometric scaffolding.
- **How**: Define `E ε` as the outer-integral sum; `h_ftc := rfl`; integrability via the `_left/_right` integrability lemmas; `h_limit` proven via `Tendsto.congr'` using `cutoff_integral_eq_outer_sum` as an eventual equality on `𝓝[>] 0`.
- **Hypotheses**: existence of Cauchy PV `L`, uniqueness of crossing, derived cutoffs.
- **Uses from project**: `DerivedAsymmetricCutoffs`, `AsymmetricArcFTCHyp`, `inv_sub_mul_deriv_intervalIntegrable_left/right`, `cutoff_integral_eq_outer_sum`, `HasCauchyPV`, `ClosedPwC1Immersion`.
- **Used by**: `AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV`, `AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV_anywhere`.
- **Visibility**: public (noncomputable)
- **Lines**: 1639–1682
- **Notes**: proof >30 lines, uses `classical`

### `def AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV`
- **Type**: `(γ : ClosedPwC1Immersion x) {s t₀} (ht₀_Ioo) (h_at) (h_unique) (h_part_off) {L} (hCPV : HasCauchyPV (·-s)⁻¹ γ s L) → AsymmetricSingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s`
- **What**: Headline T-BR-Y3c constructor: from a single `HasCauchyPV` hypothesis plus immersion data (with off-partition), build `AsymmetricSingleCrossingData`.
- **How**: Call `deriveAsymmetricCutoffs` and `AsymmetricArcFTCHyp.ofHasCauchyPV`, compose with `AsymmetricSingleCrossingData.ofDerivedCutoffs`.
- **Hypotheses**: immersion γ crossing `s` only at off-partition `t₀ ∈ Ioo 0 1`, `HasCauchyPV` known.
- **Uses from project**: `deriveAsymmetricCutoffs`, `AsymmetricArcFTCHyp.ofHasCauchyPV`, `AsymmetricSingleCrossingData.ofDerivedCutoffs`, `HasCauchyPV`, `ClosedPwC1Immersion`.
- **Used by**: unused in file
- **Visibility**: public (noncomputable)
- **Lines**: 1697–1710

### `def AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV_anywhere`
- **Type**: Same as `ofClosedImmersion_hasCauchyPV` but without `h_part_off`.
- **What**: Corner-friendly variant of `ofClosedImmersion_hasCauchyPV`, allowing `t₀` to lie on the partition.
- **How**: Same composition via `deriveAsymmetricCutoffs_anywhere`.
- **Hypotheses**: same as `_hasCauchyPV` minus `h_part_off`.
- **Uses from project**: `deriveAsymmetricCutoffs_anywhere`, `AsymmetricArcFTCHyp.ofHasCauchyPV`, `AsymmetricSingleCrossingData.ofDerivedCutoffs`, `HasCauchyPV`, `ClosedPwC1Immersion`.
- **Used by**: unused in file
- **Visibility**: public (noncomputable)
- **Lines**: 1717–1729

---

### File Summary
- **Total declarations**: 27 (2 def-with-proof helpers private; 7 reInner lemmas private; 1 structure; rest theorems and constructors).
- **Key API (used by 3+ others in this file)**: `reInner`, `DerivedAsymmetricCutoffs`, `AsymmetricArcFTCHyp.ofHasCauchyPV` indirectly via two terminal constructors; geometric building blocks (`exists_right_cutoff`/`exists_left_cutoff`/`deriveAsymmetricCutoffs[_anywhere]`) each used twice; the seven `reInner_*` helpers used by both `reInner_lower_bound_right_eventually` and `reInner_upper_bound_left_eventually`.
- **Unused in this file**: `chord_lower_bound_right_eventually`, `chord_upper_bound_right_eventually`, `chord_lower_bound_left_eventually`, `chord_upper_bound_left_eventually`, `AsymmetricSingleCrossingData.ofClosedImmersion_flat_one_derived`, `SingleCrossingData.ofClosedImmersion_flat_one`, `AsymmetricSingleCrossingData.ofClosedImmersion_flat_one`, `AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV`, `AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV_anywhere` (terminal API, used by downstream files).
- **Declarations with sorry**: none.
- **Declarations with set_option**: none.
- **Proofs >30 lines**: `exists_far_bound_compact`, `chord_lower_bound_right_eventually`, `chord_upper_bound_right_eventually`, `chord_lower_bound_left_eventually`, `reInner_lower_bound_right_eventually`, `norm_sub_strictMonoOn_right`, `reInner_upper_bound_left_eventually`, `norm_sub_strictAntiOn_left`, `exists_right_cutoff`, `exists_left_cutoff`, `deriveAsymmetricCutoffs_anywhere`, `deriveAsymmetricCutoffs`, `cutoff_integral_eq_outer_sum`, `AsymmetricArcFTCHyp.ofHasCauchyPV`.
- **File purpose**: This file delivers the T-BR-Y3a/b/c generic builder API for `SingleCrossingData` and especially `AsymmetricSingleCrossingData` from a closed piecewise-`C¹` immersion γ with a unique transverse crossing at `t₀ ∈ Ioo 0 1`. The core mathematics is: (1) chord-to-tangent two-sided estimates that yield strict monotonicity of `‖γ-s‖` on one-sided neighborhoods (via `reInner` positivity arguments); (2) IVT inversion to construct level-set cutoffs `δ_left, δ_right`; (3) bundling these as `DerivedAsymmetricCutoffs`; (4) building the analytic FTC oracle `AsymmetricArcFTCHyp` from a single `HasCauchyPV` hypothesis using these cutoffs. The headline terminal constructors `AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV[_anywhere]` reduce the per-pole geometric scaffold from a 14-field oracle to a single `HasCauchyPV` existence statement, a key reduction in the Hungerbühler–Wasem residue programme.
