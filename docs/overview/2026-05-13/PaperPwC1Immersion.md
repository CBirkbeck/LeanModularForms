# Inventory: PaperPwC1Immersion.lean

### `def Finset.IsConsecutive`
- **Type**: `(S : Finset ℝ) (a b : ℝ) : Prop`
- **What**: Predicate stating that `(a, b)` are consecutive members of a finite real set `S` — both lie in `S`, `a < b`, and no element of `S` lies strictly between them.
- **How**: Simple conjunction definition; no proof body.
- **Hypotheses**: None (definition).
- **Uses from project**: []
- **Used by**: `ClosedPwC1Curve.contDiffOn_pieces`, `ClosedPwC1Immersion.derivWithin_ne_zero_pieces`, `ClosedPwC1Curve.deriv_intervalIntegrable_piece`, `intervalIntegrable_of_consecutive_pieces`, `ClosedPwC1Curve.exists_consecutive_pair_containing`, and many more (all consecutive-pair lemmas).
- **Visibility**: public
- **Lines**: 62-65
- **Notes**: Core definition for the paper-style partition.

### `structure ClosedPwC1Curve`
- **Type**: `(x : E) extends Path x x`
- **What**: A closed piecewise C¹ curve from Hungerbühler-Wasem: a path `[0,1] → E` returning to its starting point, with partition including endpoints, where each closed sub-interval is C¹.
- **How**: Definition with fields `partition`, `zero_mem_partition`, `one_mem_partition`, `partition_subset`, `contDiffOn_pieces`.
- **Hypotheses**: Implicit: `E` is a normed real vector space.
- **Uses from project**: `Finset.IsConsecutive`
- **Used by**: `ClosedPwC1Immersion` (extends), all `ClosedPwC1Curve.*` lemmas.
- **Visibility**: public
- **Lines**: 67-83

### `structure ClosedPwC1Immersion`
- **Type**: `(x : E) extends ClosedPwC1Curve x`
- **What**: A closed piecewise C¹ immersion: a `ClosedPwC1Curve` whose within-derivative is non-vanishing on every closed sub-interval between consecutive partition points.
- **How**: Definition extending `ClosedPwC1Curve` with field `derivWithin_ne_zero_pieces`.
- **Hypotheses**: Implicit: `E` is a normed real vector space.
- **Uses from project**: `ClosedPwC1Curve`, `Finset.IsConsecutive`
- **Used by**: All `ClosedPwC1Immersion.*` lemmas and theorems.
- **Visibility**: public
- **Lines**: 85-97

### `theorem ClosedPwC1Curve.continuous`
- **Type**: `(γ : ClosedPwC1Curve x) : Continuous γ.toPath.extend`
- **What**: The underlying extended path of a `ClosedPwC1Curve` is continuous.
- **How**: Direct application of `Path.continuous_extend`.
- **Hypotheses**: None additional.
- **Uses from project**: `ClosedPwC1Curve`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 104-105

### `private lemma ClosedPwC1Curve.derivWithin_eq_deriv_on_Ioo`
- **Type**: `(f : ℝ → E) {a b t : ℝ} (ht : t ∈ Ioo a b) : derivWithin f (Icc a b) t = deriv f t`
- **What**: On the open interior of `[a, b]`, the within-derivative agrees with the global derivative.
- **How**: Direct application of `derivWithin_of_mem_nhds` with `Icc_mem_nhds`.
- **Hypotheses**: `t` lies in the open interval `(a, b)`.
- **Uses from project**: []
- **Used by**: `ClosedPwC1Curve.deriv_intervalIntegrable_piece`, `ClosedPwC1Curve.toPiecewiseC1Path`, `ClosedPwC1Immersion.toPwC1Immersion`
- **Visibility**: private
- **Lines**: 117-120

### `theorem ClosedPwC1Curve.deriv_intervalIntegrable_piece`
- **Type**: `(γ : ClosedPwC1Curve x) {a b : ℝ} (h : γ.partition.IsConsecutive a b) : IntervalIntegrable (deriv γ.toPath.extend) volume a b`
- **What**: On each closed piece between consecutive partition members, the derivative of the curve is interval-integrable.
- **How**: Uses `ContDiffOn.continuousOn_derivWithin` to get continuous `derivWithin`, then `ContinuousOn.intervalIntegrable_of_Icc` plus a.e. equality with `deriv` via `derivWithin_eq_deriv_on_Ioo` (since they differ only at the single endpoint, of measure zero).
- **Hypotheses**: `(a, b)` consecutive in partition.
- **Uses from project**: `ClosedPwC1Curve.contDiffOn_pieces`, `derivWithin_eq_deriv_on_Ioo`
- **Used by**: `ClosedPwC1Curve.deriv_extend_intervalIntegrable`
- **Visibility**: public
- **Lines**: 125-149
- **Notes**: Proof >10 lines; key lemmas: `ContDiffOn.continuousOn_derivWithin`, `uniqueDiffOn_Icc`, `Real.volume_singleton`.

### `private theorem intervalIntegrable_of_consecutive_pieces`
- **Type**: `∀ s : Finset ℝ, ∀ a b : ℝ, a ∈ s → b ∈ s → a ≤ b → (∀ c ∈ s, a ≤ c ∧ c ≤ b) → (∀ p q, s.IsConsecutive p q → IntervalIntegrable f μ p q) → IntervalIntegrable f μ a b`
- **What**: If `f` is interval-integrable on every consecutive pair of a finite partition of `[a, b]` (containing both endpoints), then `f` is interval-integrable on `[a, b]`.
- **How**: Strong induction on `Finset` size; picks smallest partition member strictly above `a`, splits `[a, b]` at `a'`, recurses on `s.erase a`. Key lemma: `IntervalIntegrable.trans`.
- **Hypotheses**: `a, b ∈ s`, `a ≤ b`, `s` bounded by `[a, b]`, pieces integrable.
- **Uses from project**: `Finset.IsConsecutive`
- **Used by**: `ClosedPwC1Curve.deriv_extend_intervalIntegrable`
- **Visibility**: private
- **Lines**: 157-222
- **Notes**: Proof >30 lines. Key lemmas used: `Finset.strongInduction`, `Finset.mem_filter`, `Finset.min'_mem`, `Finset.min'_le`, `Finset.erase_ssubset`, `IntervalIntegrable.refl`, `IntervalIntegrable.trans`.

### `theorem ClosedPwC1Curve.deriv_extend_intervalIntegrable`
- **Type**: `(γ : ClosedPwC1Curve x) : IntervalIntegrable (deriv γ.toPath.extend) volume 0 1`
- **What**: For a paper-faithful closed piecewise C¹ curve, the derivative is interval-integrable on `[0, 1]` (TIGHT-6 global form).
- **How**: Apply `intervalIntegrable_of_consecutive_pieces` to `γ.partition` with the piece-level integrability `γ.deriv_intervalIntegrable_piece`.
- **Hypotheses**: None additional.
- **Uses from project**: `intervalIntegrable_of_consecutive_pieces`, `ClosedPwC1Curve.zero_mem_partition`, `ClosedPwC1Curve.one_mem_partition`, `ClosedPwC1Curve.partition_subset`, `ClosedPwC1Curve.deriv_intervalIntegrable_piece`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 232-237

### `private lemma ClosedPwC1Curve.exists_consecutive_pair_containing`
- **Type**: `(γ : ClosedPwC1Curve x) {t : ℝ} (ht : t ∈ Ioo 0 1) (htn : t ∉ γ.partition) : ∃ a b, γ.partition.IsConsecutive a b ∧ t ∈ Ioo a b`
- **What**: For `t` strictly inside `(0, 1)` not in the partition, find the consecutive partition pair containing `t` in its open interior.
- **How**: Take `a = max{p ∈ partition : p < t}`, `b = min{p ∈ partition : p > t}`; trichotomy to show no element strictly between. Key lemmas: `Finset.max'_mem`, `Finset.min'_mem`, `Finset.mem_filter`.
- **Hypotheses**: `t ∈ (0, 1)` and `t` not in partition.
- **Uses from project**: `ClosedPwC1Curve.zero_mem_partition`, `ClosedPwC1Curve.one_mem_partition`, `Finset.IsConsecutive`
- **Used by**: `ClosedPwC1Curve.toPiecewiseC1Path`, `ClosedPwC1Immersion.toPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift_hasDerivAt_no_wrap`, `ClosedPwC1Immersion.cyclicShift_hasDerivAt_wrap`, `ClosedPwC1Immersion.preimage_finite`
- **Visibility**: private
- **Lines**: 247-269
- **Notes**: Proof >10 lines.

### `private lemma ClosedPwC1Curve.legacy_partition_subset_Ioo`
- **Type**: `(γ : ClosedPwC1Curve x) : (((γ.partition.erase 0).erase 1 : Finset ℝ) : Set ℝ) ⊆ Ioo 0 1`
- **What**: The legacy partition (erasing 0 and 1 from the paper partition) lies strictly inside `(0, 1)`.
- **How**: Unpack `Finset.mem_erase` twice; use `partition_subset` and `lt_of_le_of_ne`.
- **Hypotheses**: None.
- **Uses from project**: `ClosedPwC1Curve.partition_subset`
- **Used by**: `ClosedPwC1Curve.toPiecewiseC1Path`
- **Visibility**: private
- **Lines**: 273-282

### `private lemma ClosedPwC1Curve.not_mem_partition_of_not_mem_legacy`
- **Type**: `(γ : ClosedPwC1Curve x) {t : ℝ} (ht : t ∈ Ioo 0 1) (htn : t ∉ (γ.partition.erase 0).erase 1) : t ∉ γ.partition`
- **What**: If `t` is strictly in `(0, 1)` and not in the erased legacy partition, then `t` is not in the original partition.
- **How**: Contrapositive: rebuild the erase containment from `t ≠ 0` and `t ≠ 1` (from `ht`).
- **Hypotheses**: `t ∈ Ioo 0 1`, `t ∉` legacy partition.
- **Uses from project**: []
- **Used by**: `ClosedPwC1Curve.toPiecewiseC1Path`, `ClosedPwC1Immersion.toPwC1Immersion`
- **Visibility**: private
- **Lines**: 285-289

### `private lemma ClosedPwC1Curve.legacy_mem_unpack`
- **Type**: `(γ : ClosedPwC1Curve x) {p : ℝ} (hp : p ∈ (γ.partition.erase 0).erase 1) : 0 < p ∧ p < 1 ∧ p ∈ γ.partition`
- **What**: Unpack a legacy interior partition point: it lies strictly inside `(0, 1)` and is in the paper partition.
- **How**: Unwrap `Finset.mem_erase` twice and apply `partition_subset` with `lt_of_le_of_ne`.
- **Hypotheses**: `p` in the legacy partition.
- **Uses from project**: `ClosedPwC1Curve.partition_subset`
- **Used by**: `ClosedPwC1Immersion.toPwC1Immersion`, `ClosedPwC1Immersion.preimage_finite` (indirectly)
- **Visibility**: private
- **Lines**: 293-302

### `def ClosedPwC1Curve.toPiecewiseC1Path`
- **Type**: `(γ : ClosedPwC1Curve x) : PiecewiseC1Path x x`
- **What**: Construct a legacy `PiecewiseC1Path` from a paper-faithful `ClosedPwC1Curve` by erasing endpoints from the partition.
- **How**: Provides `partition := (γ.partition.erase 0).erase 1` and uses `exists_consecutive_pair_containing` to get differentiability and continuity off the legacy partition. Key: `ContDiffOn.differentiableOn_one`, `ContDiffOn.continuousOn_derivWithin`.
- **Hypotheses**: None additional.
- **Uses from project**: `ClosedPwC1Curve.legacy_partition_subset_Ioo`, `ClosedPwC1Curve.not_mem_partition_of_not_mem_legacy`, `ClosedPwC1Curve.exists_consecutive_pair_containing`, `ClosedPwC1Curve.contDiffOn_pieces`, `ClosedPwC1Curve.derivWithin_eq_deriv_on_Ioo`
- **Used by**: `ClosedPwC1Immersion.toPwC1Immersion`, `ClosedPwC1Immersion.preimage_finite`, `ClosedPwC1Immersion.preimage_countable`
- **Visibility**: public
- **Lines**: 305-330
- **Notes**: Proof >10 lines (definition body). Uses `Icc_mem_nhds`, `Ioo_subset_Icc_self`, `derivWithin_eq_deriv_on_Ioo`.

### `private lemma ClosedPwC1Immersion.exists_predecessor`
- **Type**: `(γ : ClosedPwC1Immersion x) {p : ℝ} (hp_in : p ∈ γ.partition) (hp_pos : 0 < p) : ∃ a, γ.partition.IsConsecutive a p`
- **What**: At an interior partition point `p`, the predecessor `a := max{c ∈ partition : c < p}` is well-defined and `(a, p)` is consecutive.
- **How**: Filter partition by `< p`, take `max'`; show no element strictly between by trichotomy via `Finset.le_max'`.
- **Hypotheses**: `p ∈ partition`, `0 < p` (so `0` is in the filter).
- **Uses from project**: `ClosedPwC1Curve.zero_mem_partition`, `Finset.IsConsecutive`
- **Used by**: `ClosedPwC1Immersion.toPwC1Immersion`, `ClosedPwC1Immersion.preimage_finite`
- **Visibility**: private
- **Lines**: 341-354

### `private lemma ClosedPwC1Immersion.exists_successor`
- **Type**: `(γ : ClosedPwC1Immersion x) {p : ℝ} (hp_in : p ∈ γ.partition) (hp_lt_one : p < 1) : ∃ b, γ.partition.IsConsecutive p b`
- **What**: At an interior partition point `p`, the successor `b := min{c ∈ partition : p < c}` is well-defined and `(p, b)` is consecutive.
- **How**: Symmetric to `exists_predecessor`; filter by `p <` and take `min'`.
- **Hypotheses**: `p ∈ partition`, `p < 1`.
- **Uses from project**: `ClosedPwC1Curve.one_mem_partition`, `Finset.IsConsecutive`
- **Used by**: `ClosedPwC1Immersion.toPwC1Immersion`, `ClosedPwC1Immersion.preimage_finite`
- **Visibility**: private
- **Lines**: 359-372

### `def ClosedPwC1Immersion.toPwC1Immersion`
- **Type**: `(γ : ClosedPwC1Immersion x) : PwC1Immersion x x`
- **What**: Construct a legacy `PwC1Immersion` from a paper-faithful `ClosedPwC1Immersion` by reusing the curve bridge plus showing non-vanishing deriv and one-sided derivative limits at corner points.
- **How**: Underlying path uses `toPiecewiseC1Path`; `deriv_ne_zero` via `derivWithin_ne_zero_pieces` + `derivWithin_eq_deriv_on_Ioo`; `left_deriv_limit`/`right_deriv_limit` via `ContDiffOn.continuousOn_derivWithin` and conversion of `𝓝[<] p` to `𝓝[Ioo a p] p`. Key lemmas: `nhdsWithin_inter_of_mem'`, `Tendsto.mono_left`, `Tendsto.congr'`.
- **Hypotheses**: None additional.
- **Uses from project**: `ClosedPwC1Curve.toPiecewiseC1Path`, `ClosedPwC1Curve.not_mem_partition_of_not_mem_legacy`, `ClosedPwC1Curve.exists_consecutive_pair_containing`, `ClosedPwC1Immersion.derivWithin_ne_zero_pieces`, `ClosedPwC1Curve.derivWithin_eq_deriv_on_Ioo`, `ClosedPwC1Curve.legacy_mem_unpack`, `ClosedPwC1Immersion.exists_predecessor`, `ClosedPwC1Immersion.exists_successor`
- **Used by**: `ClosedPwC1Immersion.preimage_finite`, `ClosedPwC1Immersion.preimage_countable`
- **Visibility**: public
- **Lines**: 375-442
- **Notes**: Proof >30 lines (definition body) — main bridge to legacy. Uses `Ioi_mem_nhds`, `Iio_mem_nhds`, `Set.Iio_inter_Ioi`, `Set.Ioi_inter_Iio`.

### `private lemma lipschitzOnWith_Icc_trans`
- **Type**: `{f : ℝ → E} {a b c : ℝ} {C : NNReal} (hab : a ≤ b) (hbc : b ≤ c) (hf₁ : LipschitzOnWith C f (Icc a b)) (hf₂ : LipschitzOnWith C f (Icc b c)) : LipschitzOnWith C f (Icc a c)`
- **What**: Glue two `LipschitzOnWith` results across a shared midpoint `b` to get Lipschitz on the union.
- **How**: Case split on positions of `x, y` relative to `b`; in the straddling case, use triangle inequality `‖f x - f y‖ ≤ ‖f x - f b‖ + ‖f b - f y‖` and additivity of `|x - y| = |x - b| + |b - y|`. Key lemmas: `norm_add_le`, `abs_of_nonpos`, `gcongr`.
- **Hypotheses**: `a ≤ b ≤ c`, Lipschitz on each half.
- **Uses from project**: []
- **Used by**: `lipschitzOnWith_of_consecutive_pieces`
- **Visibility**: private
- **Lines**: 453-514
- **Notes**: Proof >30 lines. Uses `lipschitzOnWith_iff_norm_sub_le`, `Real.norm_eq_abs`, `norm_sub_rev`.

### `private lemma lipschitzOnWith_of_consecutive_pieces`
- **Type**: `∀ s : Finset ℝ, ∀ a b : ℝ, a ∈ s → b ∈ s → a ≤ b → (∀ c ∈ s, a ≤ c ∧ c ≤ b) → (∀ p q, s.IsConsecutive p q → LipschitzOnWith C f (Icc p q)) → LipschitzOnWith C f (Icc a b)`
- **What**: Inductive gluing of piecewise `LipschitzOnWith` constants over a finite partition.
- **How**: Strong induction on `Finset` (cf. `intervalIntegrable_of_consecutive_pieces`); picks smallest partition member above `a`, recurses on `s.erase a`, glues with `lipschitzOnWith_Icc_trans`.
- **Hypotheses**: Endpoints in `s`, `a ≤ b`, `s` bounded by `[a, b]`, pieces Lipschitz.
- **Uses from project**: `Finset.IsConsecutive`, `lipschitzOnWith_Icc_trans`
- **Used by**: `ClosedPwC1Curve.lipschitzOnWith_Icc01`
- **Visibility**: private
- **Lines**: 518-573
- **Notes**: Proof >30 lines. Uses `Finset.strongInduction`, `Finset.mem_filter`, `Finset.min'_le`, `Finset.erase_ssubset`.

### `theorem ClosedPwC1Curve.lipschitzOnWith_piece`
- **Type**: `(γ : ClosedPwC1Curve x) {a b : ℝ} (h : γ.partition.IsConsecutive a b) : ∃ K : NNReal, LipschitzOnWith K γ.toPath.extend (Icc a b)`
- **What**: On each closed piece, `γ.toPath.extend` is Lipschitz with constant given by the maximum norm of `derivWithin` on the piece.
- **How**: Use `ContDiffOn.continuousOn_derivWithin` to get continuity of `derivWithin`, then `IsCompact.exists_isMaxOn` on the norm. Apply `Convex.lipschitzOnWith_of_nnnorm_derivWithin_le`. Key lemmas: `convex_Icc`, `isCompact_Icc`.
- **Hypotheses**: `(a, b)` consecutive.
- **Uses from project**: `ClosedPwC1Curve.contDiffOn_pieces`
- **Used by**: `ClosedPwC1Curve.lipschitzOnWith_Icc01`
- **Visibility**: public
- **Lines**: 582-603
- **Notes**: Proof >10 lines. Key lemma: `Convex.lipschitzOnWith_of_nnnorm_derivWithin_le`.

### `theorem ClosedPwC1Curve.lipschitzOnWith_Icc01`
- **Type**: `(γ : ClosedPwC1Curve x) : ∃ K : NNReal, LipschitzOnWith K γ.toPath.extend (Icc 0 1)`
- **What**: Existence of a global Lipschitz constant on `[0, 1]` for `γ.toPath.extend` by gluing piece-wise constants.
- **How**: Use `choose` to pick a Lipschitz constant on each consecutive piece, take `Finset.sup` over the attach, then apply `lipschitzOnWith_of_consecutive_pieces`. Key lemma: `LipschitzOnWith.weaken`.
- **Hypotheses**: None.
- **Uses from project**: `ClosedPwC1Curve.lipschitzOnWith_piece`, `lipschitzOnWith_of_consecutive_pieces`, `ClosedPwC1Curve.zero_mem_partition`, `ClosedPwC1Curve.one_mem_partition`, `ClosedPwC1Curve.partition_subset`
- **Used by**: `ClosedPwC1Curve.lipschitzWith_extend`
- **Visibility**: public
- **Lines**: 607-634
- **Notes**: Proof >10 lines. Uses `Finset.le_sup`, `Finset.mem_attach`.

### `theorem ClosedPwC1Curve.lipschitzWith_extend`
- **Type**: `(γ : ClosedPwC1Curve x) : ∃ K : NNReal, LipschitzWith K γ.toPath.extend`
- **What**: A `ClosedPwC1Curve` extends to a globally Lipschitz function `ℝ → E`; outside `[0, 1]` the extended path is constant.
- **How**: From `lipschitzOnWith_Icc01`, extend by clamping `s', t' := max 0 (min · 1)`. Show `extend s = extend s'` via `extend_of_le_zero`/`extend_of_one_le`/`extend_zero`/`extend_one`. Use 1-Lipschitz clamping via `abs_max_sub_max_le_max`, `abs_min_sub_min_le_max`.
- **Hypotheses**: None.
- **Uses from project**: `ClosedPwC1Curve.lipschitzOnWith_Icc01`
- **Used by**: `ClosedPwC1Immersion.lipschitzWith_extend`
- **Visibility**: public
- **Lines**: 638-697
- **Notes**: Proof >30 lines. Key lemmas: `lipschitzOnWith_iff_norm_sub_le`, `lipschitzWith_iff_norm_sub_le`, `Path.extend_of_le_zero`, `Path.extend_of_one_le`, `Path.extend_zero`, `Path.extend_one`, `abs_max_sub_max_le_max`, `abs_min_sub_min_le_max`.

### `theorem ClosedPwC1Immersion.lipschitzWith_extend`
- **Type**: `(γ : ClosedPwC1Immersion x) : ∃ K : NNReal, LipschitzWith K γ.toPath.extend`
- **What**: A `ClosedPwC1Immersion` extends to a globally Lipschitz function `ℝ → E`.
- **How**: Delegate to `γ.toClosedPwC1Curve.lipschitzWith_extend`.
- **Hypotheses**: None.
- **Uses from project**: `ClosedPwC1Curve.lipschitzWith_extend`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 706-708

### `noncomputable def cyclicShiftFun`
- **Type**: `(f : ℝ → E) (τ : ℝ) : ℝ → E`
- **What**: The cyclic-shift function: for a closed loop `f` and shift `τ`, returns `f(t + τ)` if `t + τ ≤ 1`, else `f(t + τ - 1)`.
- **How**: Definition by `if-then-else`.
- **Hypotheses**: None (definition).
- **Uses from project**: []
- **Used by**: `cyclicShiftFun_zero`, `cyclicShiftFun_one`, `cyclicShiftFun_at_breakpoint`, `cyclicShiftFun_at_breakpoint_else`, `Continuous.cyclicShiftFun`, `cyclicShiftFun_closed`, `Path.cyclicShift`, `cyclicShiftFun_eq_on_no_wrap`, `cyclicShiftFun_eq_on_wrap`, and downstream invariance lemmas.
- **Visibility**: public
- **Lines**: 739-740

### `theorem cyclicShiftFun_zero`
- **Type**: `(f : ℝ → E) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) : cyclicShiftFun f τ 0 = f τ`
- **What**: Value of `cyclicShiftFun` at `t = 0` equals `f τ` when `τ ∈ (0, 1)`.
- **How**: Unfold; take the `if_pos` branch since `0 + τ ≤ 1`.
- **Hypotheses**: `τ ∈ Ioo 0 1`.
- **Uses from project**: `cyclicShiftFun`
- **Used by**: `cyclicShiftFun_closed`, `Path.cyclicShift`
- **Visibility**: public
- **Lines**: 744-749
- **Notes**: `omit [NormedSpace ℝ E]`; `@[simp]`.

### `theorem cyclicShiftFun_one`
- **Type**: `(f : ℝ → E) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) (_hclosed : f 0 = f 1) : cyclicShiftFun f τ 1 = f τ`
- **What**: Value at `t = 1` equals `f τ` for closed loops with `τ ∈ (0, 1)`.
- **How**: Take `if_neg` branch (since `1 + τ > 1` for `τ > 0`); then `f(1 + τ - 1) = f τ`.
- **Hypotheses**: `τ ∈ (0, 1)`, `f 0 = f 1`.
- **Uses from project**: `cyclicShiftFun`
- **Used by**: `cyclicShiftFun_closed`, `Path.cyclicShift`
- **Visibility**: public
- **Lines**: 751-762
- **Notes**: `omit [NormedAddCommGroup E] [NormedSpace ℝ E]`.

### `theorem cyclicShiftFun_at_breakpoint`
- **Type**: `(f : ℝ → E) (τ : ℝ) : cyclicShiftFun f τ (1 - τ) = f 1`
- **What**: At `t = 1 - τ`, the value (from the if-true branch) is `f 1`.
- **How**: `if_pos` branch since `(1 - τ) + τ = 1 ≤ 1`; arithmetic gives `f 1`.
- **Hypotheses**: None.
- **Uses from project**: `cyclicShiftFun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 764-771
- **Notes**: `omit [NormedAddCommGroup E] [NormedSpace ℝ E]`.

### `theorem cyclicShiftFun_at_breakpoint_else`
- **Type**: `(f : ℝ → E) (τ : ℝ) : f ((1 - τ) + τ - 1) = f 0`
- **What**: The else-branch limit at `1 - τ` gives `f 0` (matches the true branch via closedness).
- **How**: Arithmetic: `(1 - τ) + τ - 1 = 0`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 773-777
- **Notes**: `omit [NormedAddCommGroup E] [NormedSpace ℝ E]`.

### `theorem Continuous.cyclicShiftFun`
- **Type**: `{f : ℝ → E} (hf : Continuous f) {τ : ℝ} (hclosed : f 0 = f 1) : Continuous (cyclicShiftFun f τ)`
- **What**: Continuity of `cyclicShiftFun` for a continuous closed loop.
- **How**: Apply `Continuous.if_le` to decompose; check matching condition at `t + τ = 1` using closedness `f(1) = f(0)`.
- **Hypotheses**: `f` continuous, `f 0 = f 1`.
- **Uses from project**: `cyclicShiftFun`
- **Used by**: `Path.cyclicShift`
- **Visibility**: public
- **Lines**: 779-797
- **Notes**: Proof >10 lines. Uses `Continuous.if_le`.

### `theorem cyclicShiftFun_closed`
- **Type**: `(f : ℝ → E) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) (hclosed : f 0 = f 1) : cyclicShiftFun f τ 0 = cyclicShiftFun f τ 1`
- **What**: The cyclic-shift function preserves closedness: `g(0) = g(1) = f(τ)`.
- **How**: Rewrite both endpoints via `cyclicShiftFun_zero` and `cyclicShiftFun_one`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `f 0 = f 1`.
- **Uses from project**: `cyclicShiftFun_zero`, `cyclicShiftFun_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 800-803

### `noncomputable def Path.cyclicShift`
- **Type**: `{x : E} (γ : Path x x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) : Path (γ.extend τ) (γ.extend τ)`
- **What**: The cyclic-shift `Path` from `γ(τ)` to `γ(τ)`.
- **How**: Build via `Path` structure: `toFun t = cyclicShiftFun γ.extend τ t`, continuity via `Continuous.cyclicShiftFun`, endpoints via `cyclicShiftFun_zero`/`cyclicShiftFun_one`.
- **Hypotheses**: `τ ∈ Ioo 0 1`.
- **Uses from project**: `cyclicShiftFun`, `Continuous.cyclicShiftFun`, `cyclicShiftFun_zero`, `cyclicShiftFun_one`
- **Used by**: `Path.cyclicShift_apply`, `Path.cyclicShift_extend_on_Icc`, `ClosedPwC1Curve.cyclicShift`, downstream invariance lemmas
- **Visibility**: public
- **Lines**: 808-822

### `theorem Path.cyclicShift_apply`
- **Type**: `{x : E} (γ : Path x x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) (t : ↑(Set.Icc 0 1)) : γ.cyclicShift hτ t = cyclicShiftFun γ.extend τ (t : ℝ)`
- **What**: Application of `Path.cyclicShift` equals `cyclicShiftFun`.
- **How**: `rfl`.
- **Hypotheses**: `τ ∈ Ioo 0 1`.
- **Uses from project**: `Path.cyclicShift`, `cyclicShiftFun`
- **Used by**: `Path.cyclicShift_extend_on_Icc`
- **Visibility**: public
- **Lines**: 825-827

### `theorem Path.cyclicShift_extend_on_Icc`
- **Type**: `{x : E} (γ : Path x x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t : ℝ} (ht : t ∈ Icc 0 1) : (γ.cyclicShift hτ).extend t = cyclicShiftFun γ.extend τ t`
- **What**: The `extend` of `Path.cyclicShift` agrees with `cyclicShiftFun` on `[0, 1]`.
- **How**: Apply `Path.extend_apply` and `Path.cyclicShift_apply`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `t ∈ Icc 0 1`.
- **Uses from project**: `Path.cyclicShift`, `Path.cyclicShift_apply`
- **Used by**: `ClosedPwC1Curve.cyclicShift_extend_contDiffOn_piece`, `ClosedPwC1Immersion.cyclicShift_derivWithin_ne_zero_piece`, `ClosedPwC1Immersion.cyclicShift_extend_eq_no_wrap`, `ClosedPwC1Immersion.cyclicShift_extend_eq_wrap`, `ClosedPwC1Immersion.cyclicShift_hasDerivAt_no_wrap`, `ClosedPwC1Immersion.cyclicShift_hasDerivAt_wrap`
- **Visibility**: public
- **Lines**: 830-833

### `noncomputable def cyclicShiftPartition`
- **Type**: `(P : Finset ℝ) (τ : ℝ) : Finset ℝ`
- **What**: The partition for the cyclic-shifted curve: image of `P` under `(· - τ)` ∪ image under `(· - τ + 1)`, intersected with `[0, 1]`.
- **How**: `Finset.image` + `Finset.filter`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `mem_cyclicShiftPartition_iff`, `cyclicShiftPartition_subset_Icc`, `cyclicShiftPartitionExt`, indirectly downstream.
- **Visibility**: public
- **Lines**: 853-856

### `theorem mem_cyclicShiftPartition_iff`
- **Type**: `(P : Finset ℝ) (τ : ℝ) (t : ℝ) : t ∈ cyclicShiftPartition P τ ↔ t ∈ Icc 0 1 ∧ ((t + τ ∈ P) ∨ (t + τ - 1 ∈ P))`
- **What**: Characterization: `t` lies in the cyclic-shift partition iff `t ∈ [0, 1]` and either `t + τ` or `t + τ - 1` is in `P`.
- **How**: Unfold definition; use `Finset.mem_filter` and `Finset.mem_image`; convert via `ring`.
- **Hypotheses**: None.
- **Uses from project**: `cyclicShiftPartition`
- **Used by**: `cyclicShiftPartition_subset_Icc`, `ClosedPwC1Curve.cyclicShift_consecutive_lift_no_wrap`, `ClosedPwC1Curve.cyclicShift_consecutive_lift_wrap`, downstream (`mem_cyclicShift_partition_no_wrap_iff`, etc.)
- **Visibility**: public
- **Lines**: 861-876
- **Notes**: `omit [NormedAddCommGroup E] [NormedSpace ℝ E]`.

### `theorem cyclicShiftPartition_subset_Icc`
- **Type**: `(P : Finset ℝ) (τ : ℝ) : ((cyclicShiftPartition P τ : Finset ℝ) : Set ℝ) ⊆ Icc 0 1`
- **What**: The cyclic-shift partition lies inside `Icc 0 1`.
- **How**: Direct from `mem_cyclicShiftPartition_iff`.
- **Hypotheses**: None.
- **Uses from project**: `mem_cyclicShiftPartition_iff`
- **Used by**: `cyclicShiftPartitionExt_subset_Icc`
- **Visibility**: public
- **Lines**: 879-884
- **Notes**: `omit [NormedAddCommGroup E] [NormedSpace ℝ E]`.

### `noncomputable def cyclicShiftPartitionExt`
- **Type**: `(P : Finset ℝ) (τ : ℝ) : Finset ℝ`
- **What**: The cyclic-shift augmented partition: includes 0, 1, and the breakpoint `1 - τ`, plus the basic cyclic-shift partition.
- **How**: `insert 0 (insert 1 (insert (1 - τ) (cyclicShiftPartition P τ)))`.
- **Hypotheses**: None.
- **Uses from project**: `cyclicShiftPartition`
- **Used by**: `mem_cyclicShiftPartitionExt_iff`, `cyclicShiftPartitionExt_subset_Icc`, `zero_mem_cyclicShiftPartitionExt`, `one_mem_cyclicShiftPartitionExt`, `oneSubTau_mem_cyclicShiftPartitionExt`, `ClosedPwC1Curve.cyclicShift`, downstream lemmas.
- **Visibility**: public
- **Lines**: 901-904

### `theorem mem_cyclicShiftPartitionExt_iff`
- **Type**: `(P : Finset ℝ) (τ : ℝ) (t : ℝ) : t ∈ cyclicShiftPartitionExt P τ ↔ t = 0 ∨ t = 1 ∨ t = 1 - τ ∨ t ∈ cyclicShiftPartition P τ`
- **What**: Characterization of membership in the extended partition.
- **How**: Unfold and use `Finset.mem_insert`.
- **Hypotheses**: None.
- **Uses from project**: `cyclicShiftPartitionExt`, `cyclicShiftPartition`
- **Used by**: `cyclicShiftPartitionExt_subset_Icc`, `zero_mem_cyclicShiftPartitionExt`, `one_mem_cyclicShiftPartitionExt`, `oneSubTau_mem_cyclicShiftPartitionExt`, `ClosedPwC1Curve.cyclicShift_consecutive_lift_no_wrap`, `ClosedPwC1Curve.cyclicShift_consecutive_lift_wrap`, downstream lemmas.
- **Visibility**: public
- **Lines**: 906-911
- **Notes**: `omit [NormedAddCommGroup E] [NormedSpace ℝ E]`.

### `theorem cyclicShiftPartitionExt_subset_Icc`
- **Type**: `(P : Finset ℝ) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) : ((cyclicShiftPartitionExt P τ : Finset ℝ) : Set ℝ) ⊆ Icc 0 1`
- **What**: The extended partition lies inside `Icc 0 1` when `τ ∈ (0, 1)`.
- **How**: Case split on `t = 0, 1, 1 - τ`, or `t ∈ cyclicShiftPartition`; for each, linarith from `hτ`.
- **Hypotheses**: `τ ∈ Ioo 0 1`.
- **Uses from project**: `cyclicShiftPartitionExt`, `mem_cyclicShiftPartitionExt_iff`, `cyclicShiftPartition_subset_Icc`
- **Used by**: `ClosedPwC1Curve.cyclicShift`, `ClosedPwC1Curve.cyclicShift_extend_contDiffOn_piece`, `ClosedPwC1Immersion.cyclicShift_derivWithin_ne_zero_piece`, `ClosedPwC1Immersion.cyclicShift_hasDerivAt_no_wrap`, `ClosedPwC1Immersion.cyclicShift_hasDerivAt_wrap`
- **Visibility**: public
- **Lines**: 913-922
- **Notes**: `omit [NormedAddCommGroup E] [NormedSpace ℝ E]`.

### `theorem zero_mem_cyclicShiftPartitionExt`
- **Type**: `(P : Finset ℝ) (τ : ℝ) : (0 : ℝ) ∈ cyclicShiftPartitionExt P τ`
- **What**: 0 is in the extended partition.
- **How**: Rewrite via membership iff and use `tauto`.
- **Hypotheses**: None.
- **Uses from project**: `cyclicShiftPartitionExt`, `mem_cyclicShiftPartitionExt_iff`
- **Used by**: `ClosedPwC1Curve.cyclicShift`
- **Visibility**: public
- **Lines**: 924-928
- **Notes**: `@[simp]`; `omit`.

### `theorem one_mem_cyclicShiftPartitionExt`
- **Type**: `(P : Finset ℝ) (τ : ℝ) : (1 : ℝ) ∈ cyclicShiftPartitionExt P τ`
- **What**: 1 is in the extended partition.
- **How**: Rewrite via membership iff and use `tauto`.
- **Hypotheses**: None.
- **Uses from project**: `cyclicShiftPartitionExt`, `mem_cyclicShiftPartitionExt_iff`
- **Used by**: `ClosedPwC1Curve.cyclicShift`, downstream invariance lemmas.
- **Visibility**: public
- **Lines**: 930-934
- **Notes**: `@[simp]`; `omit`.

### `theorem oneSubTau_mem_cyclicShiftPartitionExt`
- **Type**: `(P : Finset ℝ) (τ : ℝ) : (1 - τ : ℝ) ∈ cyclicShiftPartitionExt P τ`
- **What**: The breakpoint `1 - τ` is in the extended partition.
- **How**: Rewrite via membership iff and use `tauto`.
- **Hypotheses**: None.
- **Uses from project**: `cyclicShiftPartitionExt`, `mem_cyclicShiftPartitionExt_iff`
- **Used by**: `not_straddle_oneSubTau`, downstream invariance lemmas.
- **Visibility**: public
- **Lines**: 936-940
- **Notes**: `@[simp]`; `omit`.

### `private theorem ge_one_sub_tau_of_second_clause`
- **Type**: `(P : Finset ℝ) (hP_sub : (P : Set ℝ) ⊆ Icc 0 1) {τ : ℝ} (_hτ : τ ∈ Ioo 0 1) {t : ℝ} (_ht_Icc : t ∈ Icc 0 1) (hp : t + τ - 1 ∈ P) : t ≥ 1 - τ`
- **What**: Under `P ⊆ Icc 0 1`, an element `t + τ - 1 ∈ P` forces `t ≥ 1 - τ`.
- **How**: From `hP_sub`, `0 ≤ t + τ - 1`; linarith.
- **Hypotheses**: `P ⊆ Icc 0 1`, `t ∈ Icc 0 1`, `t + τ - 1 ∈ P`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: private
- **Lines**: 944-949

### `private theorem le_one_sub_tau_of_first_clause`
- **Type**: `(P : Finset ℝ) (hP_sub : (P : Set ℝ) ⊆ Icc 0 1) {τ : ℝ} (_hτ : τ ∈ Ioo 0 1) {t : ℝ} (_ht_Icc : t ∈ Icc 0 1) (hp : t + τ ∈ P) : t ≤ 1 - τ`
- **What**: Under `P ⊆ Icc 0 1`, an element `t + τ ∈ P` forces `t ≤ 1 - τ`.
- **How**: From `hP_sub`, `t + τ ≤ 1`; linarith.
- **Hypotheses**: `P ⊆ Icc 0 1`, `t ∈ Icc 0 1`, `t + τ ∈ P`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: private
- **Lines**: 953-958

### `private theorem not_straddle_oneSubTau`
- **Type**: `(P : Finset ℝ) {τ : ℝ} {a b : ℝ} (h_cons : (cyclicShiftPartitionExt P τ).IsConsecutive a b) : b ≤ 1 - τ ∨ a ≥ 1 - τ`
- **What**: A consecutive pair in the extended partition does not straddle `1 - τ`.
- **How**: By contradiction; if `a < 1 - τ < b`, then `1 - τ` would lie between consecutive members, but `1 - τ` is in the partition.
- **Hypotheses**: `(a, b)` consecutive in extended partition.
- **Uses from project**: `cyclicShiftPartitionExt`, `Finset.IsConsecutive`, `oneSubTau_mem_cyclicShiftPartitionExt`
- **Used by**: `ClosedPwC1Curve.cyclicShift_consecutive_lift`
- **Visibility**: private
- **Lines**: 962-968

### `theorem ClosedPwC1Curve.cyclicShift_consecutive_lift_no_wrap`
- **Type**: `(γ : ClosedPwC1Curve x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {a b : ℝ} (h_cons : (cyclicShiftPartitionExt γ.partition τ).IsConsecutive a b) (h_b_le : b ≤ 1 - τ) : ∃ c d, γ.partition.IsConsecutive c d ∧ Icc (a + τ) (b + τ) ⊆ Icc c d`
- **What**: Step 1 (no-wrap): For a consecutive pair in the shifted partition with `b ≤ 1 - τ`, the interval `[a + τ, b + τ]` lies inside a γ-piece.
- **How**: Take `c = max{p ∈ γ.partition : p ≤ a + τ}` and `d = min{p : p ≥ b + τ}`; show consecutiveness by trichotomy on hypothetical `e` strictly between.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `(a, b)` consecutive in extended partition, `b ≤ 1 - τ`.
- **Uses from project**: `cyclicShiftPartitionExt`, `cyclicShiftPartitionExt_subset_Icc`, `ClosedPwC1Curve.zero_mem_partition`, `ClosedPwC1Curve.one_mem_partition`, `Finset.IsConsecutive`, `mem_cyclicShiftPartition_iff`, `mem_cyclicShiftPartitionExt_iff`
- **Used by**: `ClosedPwC1Curve.cyclicShift_consecutive_lift`
- **Visibility**: public
- **Lines**: 977-1040
- **Notes**: Proof >30 lines. Uses `Finset.max'_mem`, `Finset.min'_mem`, `Finset.mem_filter`.

### `theorem ClosedPwC1Curve.cyclicShift_consecutive_lift_wrap`
- **Type**: `(γ : ClosedPwC1Curve x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {a b : ℝ} (h_cons : (cyclicShiftPartitionExt γ.partition τ).IsConsecutive a b) (h_a_ge : a ≥ 1 - τ) : ∃ c d, γ.partition.IsConsecutive c d ∧ Icc (a + τ - 1) (b + τ - 1) ⊆ Icc c d`
- **What**: Step 1 (wrap): For a consecutive pair in the shifted partition with `a ≥ 1 - τ`, the interval `[a + τ - 1, b + τ - 1]` lies inside a γ-piece.
- **How**: Symmetric to no-wrap case; take `c = max{p : p ≤ a + τ - 1}` and `d = min{p : p ≥ b + τ - 1}`; trichotomy via `e + 1 - τ`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `(a, b)` consecutive in extended partition, `a ≥ 1 - τ`.
- **Uses from project**: `cyclicShiftPartitionExt`, `cyclicShiftPartitionExt_subset_Icc`, `ClosedPwC1Curve.zero_mem_partition`, `ClosedPwC1Curve.one_mem_partition`, `Finset.IsConsecutive`, `mem_cyclicShiftPartition_iff`, `mem_cyclicShiftPartitionExt_iff`
- **Used by**: `ClosedPwC1Curve.cyclicShift_consecutive_lift`
- **Visibility**: public
- **Lines**: 1046-1105
- **Notes**: Proof >30 lines. Symmetric structure to no-wrap variant.

### `theorem ClosedPwC1Curve.cyclicShift_consecutive_lift`
- **Type**: `(γ : ClosedPwC1Curve x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {a b : ℝ} (h_cons : (cyclicShiftPartitionExt γ.partition τ).IsConsecutive a b) : (b ≤ 1 - τ ∧ ∃ c d, ...) ∨ (a ≥ 1 - τ ∧ ∃ c d, ...)`
- **What**: Step 1 (combined): For a consecutive pair in the shifted partition, either no-wrap or wrap case applies.
- **How**: Use `not_straddle_oneSubTau` to dispatch, then `cyclicShift_consecutive_lift_no_wrap` or `_wrap`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `(a, b)` consecutive.
- **Uses from project**: `cyclicShiftPartitionExt`, `Finset.IsConsecutive`, `not_straddle_oneSubTau`, `ClosedPwC1Curve.cyclicShift_consecutive_lift_no_wrap`, `ClosedPwC1Curve.cyclicShift_consecutive_lift_wrap`
- **Used by**: `ClosedPwC1Curve.cyclicShift_extend_contDiffOn_piece`, `ClosedPwC1Immersion.cyclicShift_derivWithin_ne_zero_piece`, `ClosedPwC1Immersion.cyclicShift_hasDerivAt_no_wrap`, `ClosedPwC1Immersion.cyclicShift_hasDerivAt_wrap`
- **Visibility**: public
- **Lines**: 1111-1125

### `private lemma cyclicShiftFun_eq_on_no_wrap`
- **Type**: `(f : ℝ → E) {τ : ℝ} (_hτ : τ ∈ Ioo 0 1) : Set.EqOn (cyclicShiftFun f τ) (fun t => f (t + τ)) (Icc 0 (1 - τ))`
- **What**: On `Icc 0 (1 - τ)`, `cyclicShiftFun f τ` equals `f ∘ (· + τ)`.
- **How**: Unfold; take `if_pos` branch since `t + τ ≤ 1`.
- **Hypotheses**: `τ ∈ Ioo 0 1`.
- **Uses from project**: `cyclicShiftFun`
- **Used by**: `ClosedPwC1Curve.cyclicShift_extend_contDiffOn_piece`, `ClosedPwC1Immersion.cyclicShift_derivWithin_ne_zero_piece`, `ClosedPwC1Immersion.cyclicShift_extend_eq_no_wrap`, `ClosedPwC1Immersion.cyclicShift_hasDerivAt_no_wrap`
- **Visibility**: private
- **Lines**: 1138-1143

### `private lemma cyclicShiftFun_eq_on_wrap`
- **Type**: `(f : ℝ → E) {τ : ℝ} (_hτ : τ ∈ Ioo 0 1) (hclosed : f 0 = f 1) : Set.EqOn (cyclicShiftFun f τ) (fun t => f (t + τ - 1)) (Icc (1 - τ) 1)`
- **What**: On `Icc (1 - τ) 1`, `cyclicShiftFun f τ` equals `f ∘ (· + τ - 1)`, provided `f` is closed.
- **How**: Case split on `t = 1 - τ` (use `if_pos` and closedness) vs `t > 1 - τ` (use `if_neg`).
- **Hypotheses**: `τ ∈ Ioo 0 1`, `f 0 = f 1`.
- **Uses from project**: `cyclicShiftFun`
- **Used by**: `ClosedPwC1Curve.cyclicShift_extend_contDiffOn_piece`, `ClosedPwC1Immersion.cyclicShift_derivWithin_ne_zero_piece`, `ClosedPwC1Immersion.cyclicShift_extend_eq_wrap`, `ClosedPwC1Immersion.cyclicShift_hasDerivAt_wrap`
- **Visibility**: private
- **Lines**: 1147-1161

### `private theorem ClosedPwC1Curve.cyclicShift_extend_contDiffOn_piece`
- **Type**: `(γ : ClosedPwC1Curve x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {a b : ℝ} (h_cons : (cyclicShiftPartitionExt γ.partition τ).IsConsecutive a b) : ContDiffOn ℝ 1 (γ.toPath.cyclicShift hτ).extend (Icc a b)`
- **What**: The shifted curve is `ContDiffOn ℝ 1` on each consecutive piece (Step 2).
- **How**: Use the consecutive-pair lift; in each case, show `cyclicShift extend` equals `γ.extend ∘ shift` on the piece, then transfer ContDiffOn via `ContDiffOn.congr` and composition with smooth shift.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `(a, b)` consecutive.
- **Uses from project**: `ClosedPwC1Curve`, `cyclicShiftPartitionExt`, `cyclicShiftPartitionExt_subset_Icc`, `Path.cyclicShift_extend_on_Icc`, `ClosedPwC1Curve.cyclicShift_consecutive_lift`, `cyclicShiftFun_eq_on_no_wrap`, `cyclicShiftFun_eq_on_wrap`, `ClosedPwC1Curve.contDiffOn_pieces`
- **Used by**: `ClosedPwC1Curve.cyclicShift`
- **Visibility**: private
- **Lines**: 1168-1226
- **Notes**: Proof >30 lines. Uses `ContDiffOn.comp`, `contDiff_id.add`, `Path.extend_zero/_one`.

### `noncomputable def ClosedPwC1Curve.cyclicShift`
- **Type**: `(γ : ClosedPwC1Curve x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) : ClosedPwC1Curve (γ.toPath.extend τ)`
- **What**: Step 2: Cyclic shift of a `ClosedPwC1Curve` — produces a new paper-faithful curve based at `γ(τ)`.
- **How**: Build via structure: path is `γ.toPath.cyclicShift hτ`, partition is `cyclicShiftPartitionExt γ.partition τ`, ContDiffOn from `cyclicShift_extend_contDiffOn_piece`.
- **Hypotheses**: `τ ∈ Ioo 0 1`.
- **Uses from project**: `ClosedPwC1Curve`, `Path.cyclicShift`, `cyclicShiftPartitionExt`, `zero_mem_cyclicShiftPartitionExt`, `one_mem_cyclicShiftPartitionExt`, `cyclicShiftPartitionExt_subset_Icc`, `ClosedPwC1Curve.cyclicShift_extend_contDiffOn_piece`
- **Used by**: `ClosedPwC1Immersion.cyclicShift`, `ClosedPwC1Immersion.cyclicShift_derivWithin_ne_zero_piece`, downstream
- **Visibility**: public
- **Lines**: 1229-1237

### `private theorem ClosedPwC1Immersion.cyclicShift_derivWithin_ne_zero_piece`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {a b : ℝ} (h_cons : (cyclicShiftPartitionExt γ.partition τ).IsConsecutive a b) {t : ℝ} (ht : t ∈ Icc a b) : derivWithin (γ.toPath.cyclicShift hτ).extend (Icc a b) t ≠ 0`
- **What**: On each piece of the cyclic shift, the within-derivative is nonzero.
- **How**: Use consecutive-pair lift; in each case, find `t + τ` (or `t + τ - 1`) in a γ-piece where derivWithin is nonzero; transfer via composition `HasDerivWithinAt.scomp` and `HasDerivWithinAt.congr`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `(a, b)` consecutive, `t ∈ Icc a b`.
- **Uses from project**: `ClosedPwC1Immersion`, `cyclicShiftPartitionExt`, `cyclicShiftPartitionExt_subset_Icc`, `Path.cyclicShift_extend_on_Icc`, `cyclicShiftFun_eq_on_no_wrap`, `cyclicShiftFun_eq_on_wrap`, `ClosedPwC1Curve.cyclicShift_consecutive_lift`, `ClosedPwC1Curve.contDiffOn_pieces`, `ClosedPwC1Immersion.derivWithin_ne_zero_pieces`
- **Used by**: `ClosedPwC1Immersion.cyclicShift`
- **Visibility**: private
- **Lines**: 1253-1351
- **Notes**: Proof >30 lines. Uses `HasDerivWithinAt.scomp`, `HasDerivWithinAt.congr`, `HasDerivWithinAt.derivWithin`, `uniqueDiffOn_Icc`.

### `noncomputable def ClosedPwC1Immersion.cyclicShift`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) : ClosedPwC1Immersion (γ.toPath.extend τ)`
- **What**: Step 3: Cyclic shift of a `ClosedPwC1Immersion`.
- **How**: Build via structure: underlying curve is `γ.toClosedPwC1Curve.cyclicShift hτ`, immersion property via `cyclicShift_derivWithin_ne_zero_piece`.
- **Hypotheses**: `τ ∈ Ioo 0 1`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Curve.cyclicShift`, `ClosedPwC1Immersion.cyclicShift_derivWithin_ne_zero_piece`
- **Used by**: `ClosedPwC1Immersion.cyclicShift_extend_eq_no_wrap`, `_eq_wrap`, `_hasDerivAt_no_wrap`, `_hasDerivAt_wrap`, `_deriv_eq_no_wrap`, `_deriv_eq_wrap`, and the invariance file's main theorems.
- **Visibility**: public
- **Lines**: 1353-1359

### `theorem ClosedPwC1Immersion.cyclicShift_extend_eq_no_wrap`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t : ℝ} (ht : t ∈ Icc 0 (1 - τ)) : (γ.cyclicShift hτ).toPath.extend t = γ.toPath.extend (t + τ)`
- **What**: Step 4: The shifted curve agrees with `γ ∘ (· + τ)` on `[0, 1 - τ]`.
- **How**: Rewrite via `Path.cyclicShift_extend_on_Icc` and `cyclicShiftFun_eq_on_no_wrap`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `t ∈ Icc 0 (1 - τ)`.
- **Uses from project**: `ClosedPwC1Immersion.cyclicShift`, `Path.cyclicShift_extend_on_Icc`, `cyclicShiftFun_eq_on_no_wrap`
- **Used by**: `ClosedPwC1Immersion.cyclicShift_hasDerivAt_no_wrap`, and downstream invariance file lemmas.
- **Visibility**: public
- **Lines**: 1368-1375

### `theorem ClosedPwC1Immersion.cyclicShift_extend_eq_wrap`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t : ℝ} (ht : t ∈ Icc (1 - τ) 1) : (γ.cyclicShift hτ).toPath.extend t = γ.toPath.extend (t + τ - 1)`
- **What**: Step 4: The shifted curve agrees with `γ ∘ (· + τ - 1)` on `[1 - τ, 1]`.
- **How**: Rewrite via `Path.cyclicShift_extend_on_Icc` and `cyclicShiftFun_eq_on_wrap`; use closedness `extend 0 = extend 1`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `t ∈ Icc (1 - τ) 1`.
- **Uses from project**: `ClosedPwC1Immersion.cyclicShift`, `Path.cyclicShift_extend_on_Icc`, `cyclicShiftFun_eq_on_wrap`
- **Used by**: `ClosedPwC1Immersion.cyclicShift_hasDerivAt_wrap`, and downstream invariance file lemmas.
- **Visibility**: public
- **Lines**: 1378-1387

### `theorem ClosedPwC1Immersion.cyclicShift_hasDerivAt_no_wrap`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t : ℝ} (ht : t ∈ Ioo 0 (1 - τ)) (htn : t ∉ (γ.cyclicShift hτ).partition) : HasDerivAt (γ.cyclicShift hτ).toPath.extend (deriv γ.toPath.extend (t + τ)) t`
- **What**: The cyclic-shifted path has derivative `deriv γ.toPath.extend (t + τ)` at `t ∈ Ioo 0 (1 - τ)` off the shifted partition.
- **How**: Find a piece containing `t` (via `exists_consecutive_pair_containing`); use no-wrap case of the consecutive-pair lift to get a γ-piece containing `t + τ`; compose `HasDerivAt γ.extend` with `HasDerivAt (· + τ) 1`; transfer via `congr_of_eventuallyEq`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `t ∈ Ioo 0 (1 - τ)`, `t` not in shifted partition.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `ClosedPwC1Curve.exists_consecutive_pair_containing`, `cyclicShiftPartitionExt_subset_Icc`, `Path.cyclicShift_extend_on_Icc`, `ClosedPwC1Curve.cyclicShift_consecutive_lift`, `cyclicShiftFun_eq_on_no_wrap`, `ClosedPwC1Curve.contDiffOn_pieces`
- **Used by**: `ClosedPwC1Immersion.cyclicShift_deriv_eq_no_wrap`, downstream invariance lemmas.
- **Visibility**: public
- **Lines**: 1395-1482
- **Notes**: Proof >30 lines. Uses `HasDerivAt.scomp`, `HasDerivAt.congr_of_eventuallyEq`, `hasDerivAt_id`, `add_const`.

### `theorem ClosedPwC1Immersion.cyclicShift_hasDerivAt_wrap`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t : ℝ} (ht : t ∈ Ioo (1 - τ) 1) (htn : t ∉ (γ.cyclicShift hτ).partition) : HasDerivAt (γ.cyclicShift hτ).toPath.extend (deriv γ.toPath.extend (t + τ - 1)) t`
- **What**: Symmetric to `_no_wrap`: derivative on the wrap region.
- **How**: Same strategy as `_no_wrap`, but with the wrap case of the consecutive-pair lift; use `(· + τ - 1)` shift with `sub_const` step. Composition of `HasDerivAt`s plus `congr_of_eventuallyEq`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `t ∈ Ioo (1 - τ) 1`, `t ∉` shifted partition.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `ClosedPwC1Curve.exists_consecutive_pair_containing`, `cyclicShiftPartitionExt_subset_Icc`, `Path.cyclicShift_extend_on_Icc`, `ClosedPwC1Curve.cyclicShift_consecutive_lift`, `cyclicShiftFun_eq_on_wrap`, `ClosedPwC1Curve.contDiffOn_pieces`
- **Used by**: `ClosedPwC1Immersion.cyclicShift_deriv_eq_wrap`, downstream invariance lemmas.
- **Visibility**: public
- **Lines**: 1485-1560
- **Notes**: Proof >30 lines. Symmetric structure to no-wrap variant.

### `theorem ClosedPwC1Immersion.cyclicShift_deriv_eq_no_wrap`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t : ℝ} (ht : t ∈ Ioo 0 (1 - τ)) (htn : t ∉ (γ.cyclicShift hτ).partition) : deriv (γ.cyclicShift hτ).toPath.extend t = deriv γ.toPath.extend (t + τ)`
- **What**: Equality of `deriv` on the open no-wrap interior, off shifted partition.
- **How**: Direct corollary of `cyclicShift_hasDerivAt_no_wrap`: apply `.deriv`.
- **Hypotheses**: As in `_hasDerivAt_no_wrap`.
- **Uses from project**: `ClosedPwC1Immersion.cyclicShift`, `ClosedPwC1Immersion.cyclicShift_hasDerivAt_no_wrap`
- **Used by**: downstream invariance lemmas.
- **Visibility**: public
- **Lines**: 1563-1569

### `theorem ClosedPwC1Immersion.cyclicShift_deriv_eq_wrap`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t : ℝ} (ht : t ∈ Ioo (1 - τ) 1) (htn : t ∉ (γ.cyclicShift hτ).partition) : deriv (γ.cyclicShift hτ).toPath.extend t = deriv γ.toPath.extend (t + τ - 1)`
- **What**: Equality of `deriv` on the open wrap interior, off shifted partition.
- **How**: Direct corollary of `cyclicShift_hasDerivAt_wrap`: apply `.deriv`.
- **Hypotheses**: As in `_hasDerivAt_wrap`.
- **Uses from project**: `ClosedPwC1Immersion.cyclicShift`, `ClosedPwC1Immersion.cyclicShift_hasDerivAt_wrap`
- **Used by**: downstream invariance lemmas.
- **Visibility**: public
- **Lines**: 1572-1578

### `private theorem ClosedPwC1Immersion.preimage_finite_piece`
- **Type**: `(γ : ClosedPwC1Immersion x) {a b : ℝ} (h : γ.partition.IsConsecutive a b) (s : E) : Set.Finite {t ∈ Icc a b | γ.toPath.extend t = s}`
- **What**: Per-piece, the preimage of a single point `s` under the extended path on `Icc a b` is finite.
- **How**: Show set `T` is closed (preimage of singleton) and compact (closed in compact `Icc a b`); show `DiscreteTopology` via `noAccPts` using `HasDerivWithinAt.eventually_ne` (non-vanishing derivWithin forces isolated zeros); compact + discrete ⇒ finite.
- **Hypotheses**: `(a, b)` consecutive.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Curve.contDiffOn_pieces`, `ClosedPwC1Immersion.derivWithin_ne_zero_pieces`
- **Used by**: `ClosedPwC1Immersion.preimage_finite_piece_of_finset`
- **Visibility**: private
- **Lines**: 1605-1659
- **Notes**: Proof >30 lines. Key lemmas: `HasDerivWithinAt.eventually_ne`, `discreteTopology_of_noAccPts`, `accPt_principal_iff_nhdsWithin`, `isCompact_iff_compactSpace`, `finite_of_compact_of_discrete`, `Set.finite_coe_iff`.

### `private theorem ClosedPwC1Immersion.preimage_finite_piece_of_finset`
- **Type**: `(γ : ClosedPwC1Immersion x) {a b : ℝ} (h : γ.partition.IsConsecutive a b) (S : Finset E) : Set.Finite {t ∈ Icc a b | γ.toPath.extend t ∈ (↑S : Set E)}`
- **What**: Per-piece, the preimage of a finite set `S` on `Icc a b` is finite.
- **How**: Rewrite as `⋃ s ∈ S, {t ∈ Icc a b | extend t = s}`; finite-union of finite sets via `preimage_finite_piece`.
- **Hypotheses**: `(a, b)` consecutive.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.preimage_finite_piece`
- **Used by**: `ClosedPwC1Immersion.preimage_finite`
- **Visibility**: private
- **Lines**: 1664-1680
- **Notes**: Uses `Set.Finite.biUnion`, `Finset.finite_toSet`.

### `theorem ClosedPwC1Immersion.preimage_finite`
- **Type**: `(γ : ClosedPwC1Immersion x) (S : Finset E) : Set.Finite {t ∈ Icc 0 1 | γ.toPwC1Immersion.toPiecewiseC1Path t ∈ (↑S : Set E)}`
- **What**: The parameter preimage of a finite set under a closed paper-piecewise C¹ immersion is finite.
- **How**: Decompose `[0, 1]` along the partition into closed pieces; for each `t`, find a containing piece via `exists_consecutive_pair_containing`, `exists_predecessor`, or `exists_successor`; apply `preimage_finite_piece_of_finset` on each piece and take the finite union.
- **Hypotheses**: None additional.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.toPwC1Immersion`, `Finset.IsConsecutive`, `ClosedPwC1Curve.zero_mem_partition`, `ClosedPwC1Curve.one_mem_partition`, `ClosedPwC1Immersion.exists_predecessor`, `ClosedPwC1Immersion.exists_successor`, `ClosedPwC1Curve.exists_consecutive_pair_containing`, `ClosedPwC1Immersion.preimage_finite_piece_of_finset`
- **Used by**: `ClosedPwC1Immersion.preimage_countable`
- **Visibility**: public
- **Lines**: 1688-1744
- **Notes**: Proof >30 lines. Uses `Set.mem_iUnion₂`, `Finset.mem_filter`, `Finset.mem_product`, `Finset.finite_toSet`, `Set.Finite.biUnion`, `Set.Finite.subset`.

### `theorem ClosedPwC1Immersion.preimage_countable`
- **Type**: `(γ : ClosedPwC1Immersion x) (S : Finset E) : Set.Countable {t ∈ Icc 0 1 | γ.toPwC1Immersion.toPiecewiseC1Path t ∈ (↑S : Set E)}`
- **What**: The preimage of a finite set is countable.
- **How**: Direct corollary of `preimage_finite` via `Set.Finite.countable`.
- **Hypotheses**: None.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.toPwC1Immersion`, `ClosedPwC1Immersion.preimage_finite`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1747-1750

### File Summary
- **Total declarations**: 49
- **Key API (used by 3+ others in this file)**:
  - `Finset.IsConsecutive` (definition used in 10+ places)
  - `ClosedPwC1Curve` (structure used by many)
  - `ClosedPwC1Immersion` (structure used by many)
  - `cyclicShiftFun` (foundation for cyclic shift)
  - `ClosedPwC1Curve.derivWithin_eq_deriv_on_Ioo`
  - `ClosedPwC1Curve.exists_consecutive_pair_containing`
  - `ClosedPwC1Curve.not_mem_partition_of_not_mem_legacy`
  - `cyclicShiftPartitionExt` and helpers (`mem_*`, subset, zero/one/oneSubTau members)
  - `Path.cyclicShift_extend_on_Icc`
  - `cyclicShiftFun_eq_on_no_wrap` and `_eq_on_wrap`
  - `ClosedPwC1Curve.cyclicShift_consecutive_lift` (and its two halves)
  - `ClosedPwC1Curve.contDiffOn_pieces`, `partition_subset`, `zero_mem_partition`, `one_mem_partition` (structure projections)
  - `ClosedPwC1Immersion.derivWithin_ne_zero_pieces` (structure projection)
- **Unused in this file**:
  - `ClosedPwC1Curve.continuous`
  - `ClosedPwC1Curve.deriv_extend_intervalIntegrable`
  - `ClosedPwC1Immersion.lipschitzWith_extend`
  - `cyclicShiftFun_at_breakpoint`
  - `cyclicShiftFun_at_breakpoint_else`
  - `cyclicShiftFun_closed`
  - `ge_one_sub_tau_of_second_clause`
  - `le_one_sub_tau_of_first_clause`
  - `ClosedPwC1Immersion.preimage_countable`
- **Declarations with sorry**: None
- **Declarations with set_option**: None
- **Proofs >30 lines**:
  - `intervalIntegrable_of_consecutive_pieces`
  - `lipschitzOnWith_Icc_trans`
  - `lipschitzOnWith_of_consecutive_pieces`
  - `ClosedPwC1Curve.lipschitzWith_extend`
  - `ClosedPwC1Curve.cyclicShift_consecutive_lift_no_wrap`
  - `ClosedPwC1Curve.cyclicShift_consecutive_lift_wrap`
  - `ClosedPwC1Curve.cyclicShift_extend_contDiffOn_piece`
  - `ClosedPwC1Immersion.cyclicShift_derivWithin_ne_zero_piece`
  - `ClosedPwC1Immersion.cyclicShift_hasDerivAt_no_wrap`
  - `ClosedPwC1Immersion.cyclicShift_hasDerivAt_wrap`
  - `ClosedPwC1Immersion.preimage_finite_piece`
  - `ClosedPwC1Immersion.preimage_finite`
  - `ClosedPwC1Immersion.toPwC1Immersion` (definition body)
- **File purpose**: This file builds a paper-faithful (Hungerbühler-Wasem) notion of closed piecewise C¹ curves and immersions on `[0, 1]`, with partition including endpoints and ContDiffOn on closed subintervals. It provides the core structures `ClosedPwC1Curve` and `ClosedPwC1Immersion`, equips them with a bridge to the legacy `PiecewiseC1Path`/`PwC1Immersion` (which uses open-interior partitions), proves the derivative is interval-integrable on `[0, 1]` (TIGHT-6), establishes global Lipschitzness (Phase 1), constructs cyclic shifts changing the basepoint from `γ(0) = x` to `γ(τ)` (Phases 2-3) with parameter-level equation-on lemmas on no-wrap and wrap regions, and proves that the preimage of any finite target set under a closed piecewise C¹ immersion is finite. The cyclic-shift machinery (`Path.cyclicShift`, `cyclicShiftFun`, `cyclicShiftPartition(Ext)`, consecutive-pair lifting, derivative equations) is the foundational layer used by the invariance file.
