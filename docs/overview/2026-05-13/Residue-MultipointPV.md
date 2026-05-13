# Inventory: Residue/MultipointPV.lean

### `private lemma measurableSet_norm_gt_of_continuousOn`
- **Type**: `{f : ℝ → ℂ} {s : Set ℝ} (ε : ℝ) (hf : ContinuousOn f s) (hs : MeasurableSet s) : MeasurableSet ({t | ε < ‖f t‖} ∩ s)`
- **What**: Set `{t ∈ s : ‖f t‖ > ε}` is measurable when `f` is continuous on a measurable set.
- **How**: Continuity of `‖f·‖`, `isOpen_Ioi.preimage`, unpack `isOpen_induced_iff` to get open `U` with `{‖f t‖ > ε} ∩ s = U ∩ s`, intersect with measurable `s`.
- **Hypotheses**: `f` continuous on `s`, `s` measurable.
- **Uses from project**: []
- **Used by**: `measurableSet_norm_gt_Icc`
- **Visibility**: private
- **Lines**: 36–62
- **Notes**: 27 lines.

### `private lemma measurableSet_norm_gt_Icc`
- **Type**: `{f : ℝ → ℂ} {a b : ℝ} (ε : ℝ) (hf : ContinuousOn f (Icc a b)) : MeasurableSet ({t | ε < ‖f t‖} ∩ Icc a b)`
- **What**: Specialization of the above with `s = Icc a b`.
- **How**: Apply `measurableSet_norm_gt_of_continuousOn` with `isClosed_Icc.measurableSet`.
- **Hypotheses**: `f` continuous on `Icc a b`.
- **Uses from project**: `measurableSet_norm_gt_of_continuousOn`
- **Used by**: `measurableSet_multipoint_condition`, `aEStronglyMeasurable_residueProd_on_goodset`, `aEStronglyMeasurable_pv_integrand_residue`
- **Visibility**: private
- **Lines**: 64–67

### `theorem aEStronglyMeasurable_of_continuousOn_off_finite`
- **Type**: `{f : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ} (hf_cont : ContinuousOn f (Icc a b \ P)) : AEStronglyMeasurable f (volume.restrict (Icc a b))`
- **What**: Functions continuous off a finite set are AE strongly measurable.
- **How**: Split `volume.restrict (Icc a b) = restrict (Icc a b \ P) + restrict (↑P ∩ Icc a b)`, first piece via `hf_cont.aestronglyMeasurable`, second has measure zero (`Set.Finite.measure_zero`), apply `AEStronglyMeasurable.add_measure`.
- **Hypotheses**: `f` continuous on `Icc a b \ P` for finite `P`.
- **Uses from project**: []
- **Used by**: `aEStronglyMeasurable_pv_integrand_multipoint`, `aEStronglyMeasurable_residueProd_on_goodset`, `aEStronglyMeasurable_decomposed_on_goodset`
- **Visibility**: public
- **Lines**: 69–94
- **Notes**: 26 lines.

### `private lemma measurableSet_multipoint_condition`
- **Type**: `{γ : ℝ → ℂ} {a b ε : ℝ} (S : Finset ℂ) (hγ : ContinuousOn γ (Icc a b)) : MeasurableSet ({t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} ∩ Icc a b)`
- **What**: "Some pole is within ε" condition gives a measurable subset of `Icc a b`.
- **How**: Rewrite as `⋃ s ∈ S, ({t | ‖γ t - s‖ ≤ ε} ∩ Icc a b)`, each summand is `Icc a b \ {t : ε < ‖γ t - s‖} ∩ Icc a b` measurable via `measurableSet_norm_gt_Icc`, conclude with `Finset.measurableSet_biUnion`.
- **Hypotheses**: `γ` continuous on `Icc a b`.
- **Uses from project**: `measurableSet_norm_gt_Icc`
- **Used by**: `measurableSet_multipoint_goodset`
- **Visibility**: private
- **Lines**: 96–126
- **Notes**: 31 lines.

### `private lemma measurableSet_multipoint_goodset`
- **Type**: `{γ : ℝ → ℂ} {a b ε : ℝ} (S : Finset ℂ) (hγ : ContinuousOn γ (Icc a b)) : MeasurableSet ({t | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b)`
- **What**: The "good set" — every pole is more than ε away — is measurable.
- **How**: Express as complement of `measurableSet_multipoint_condition` in `Icc a b`; use `isClosed_Icc.measurableSet.diff`.
- **Hypotheses**: `γ` continuous on `Icc a b`.
- **Uses from project**: `measurableSet_multipoint_condition`
- **Used by**: `aEStronglyMeasurable_pv_integrand_multipoint`, `aEStronglyMeasurable_singularSum_on_goodset`, `aEStronglyMeasurable_pv_integrand_decomposed`
- **Visibility**: private
- **Lines**: 128–146
- **Notes**: 19 lines.

### `private lemma goodset_piecewise_ae_eq_multipoint`
- **Type**: `{g : ℂ → ℂ} {γ : ℝ → ℂ} {a b ε : ℝ} (S : Finset ℂ) : (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else g (γ t) * deriv γ t) =ᵐ[volume.restrict (Icc a b)] ({t | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b).piecewise (fun t => g (γ t) * deriv γ t) (fun _ => 0)`
- **What**: AE rewrites the "outside-balls integrand" as a `Set.piecewise` form for the good set.
- **How**: `filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet]`, case on `ht_good`, push negations across `∃/∀`.
- **Hypotheses**: none additional.
- **Uses from project**: []
- **Used by**: `aEStronglyMeasurable_pv_integrand_multipoint`
- **Visibility**: private
- **Lines**: 148–165
- **Notes**: 18 lines.

### `private theorem aEStronglyMeasurable_pv_integrand_multipoint`
- **Type**: `{g : ℂ → ℂ} {γ : ℝ → ℂ} {a b ε : ℝ} {P : Finset ℝ} (S : Finset ℂ) (hg : ContinuousOn g (γ '' Icc a b)) (hγ : ContinuousOn γ (Icc a b)) (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) : AEStronglyMeasurable (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else g (γ t) * deriv γ t) (volume.restrict (Icc a b))`
- **What**: The "multipoint PV integrand" `g ∘ γ · γ'` cut off near every pole in `S` is AE strongly measurable on `Icc a b`.
- **How**: Compose AE-measurability of `g ∘ γ * deriv γ` (`hg.comp hγ` + `aEStronglyMeasurable_of_continuousOn_off_finite`) with `AEStronglyMeasurable.piecewise` on `measurableSet_multipoint_goodset`, then `congr (goodset_piecewise_ae_eq_multipoint S).symm`.
- **Hypotheses**: `g` continuous on `γ '' Icc a b`, `γ` continuous on `Icc a b`, `deriv γ` continuous off finite `P`.
- **Uses from project**: `aEStronglyMeasurable_of_continuousOn_off_finite`, `measurableSet_multipoint_goodset`, `goodset_piecewise_ae_eq_multipoint`
- **Used by**: `intervalIntegrable_cauchyPrincipalValueIntegrandOn`, `aEStronglyMeasurable_multipointPV_diff`
- **Visibility**: private
- **Lines**: 167–183

### `private lemma aEStronglyMeasurable_residueProd_on_goodset`
- **Type**: `{γ : ℝ → ℂ} {a b ε : ℝ} {P : Finset ℝ} {s c : ℂ} (hε : 0 < ε) (hγ : ContinuousOn γ (Icc a b)) (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) : AEStronglyMeasurable (fun t => (c / (γ t - s)) * deriv γ t) (volume.restrict ({t | ε < ‖γ t - s‖} ∩ Icc a b))`
- **What**: Residue-style integrand `c / (γ - s) · γ'` is AE-measurable on the ε-far good set.
- **How**: Ratio continuous on the good set (`ContinuousOn.div` with the non-vanishing denominator from `lt_trans hε ht_good`), then mul with `aEStronglyMeasurable_of_continuousOn_off_finite hγ'_off_P`.
- **Hypotheses**: `0 < ε`, `γ` continuous, `deriv γ` continuous off `P`.
- **Uses from project**: `measurableSet_norm_gt_Icc`, `aEStronglyMeasurable_of_continuousOn_off_finite`
- **Used by**: `aEStronglyMeasurable_pv_integrand_residue`
- **Visibility**: private
- **Lines**: 185–199

### `private theorem aEStronglyMeasurable_pv_integrand_residue`
- **Type**: `{γ : ℝ → ℂ} {a b ε : ℝ} {P : Finset ℝ} {s c : ℂ} (_hε : 0 < ε) (hγ : ContinuousOn γ (Icc a b)) (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) : AEStronglyMeasurable (fun t => if ‖γ t - s‖ > ε then (c / (γ t - s)) * deriv γ t else 0) (volume.restrict (Icc a b))`
- **What**: Cut-off residue integrand at a single pole `s` is AE strongly measurable on `Icc a b`.
- **How**: Combine `aEStronglyMeasurable_residueProd_on_goodset` with `aEStronglyMeasurable_piecewise` on `measurableSet_norm_gt_Icc`, then AE-congr to the `if-then-else` form via `ae_restrict_mem`.
- **Hypotheses**: `0 < ε`, `γ` continuous on `Icc a b`, `deriv γ` continuous off `P`.
- **Uses from project**: `measurableSet_norm_gt_Icc`, `aEStronglyMeasurable_residueProd_on_goodset`
- **Used by**: `intervalIntegrable_residueTerm`, `aEStronglyMeasurable_pv_sum_residue`
- **Visibility**: private
- **Lines**: 201–222

### `private lemma aEStronglyMeasurable_singularSum_on_goodset`
- **Type**: `{γ : ℝ → ℂ} {a b ε : ℝ} (S : Finset ℂ) (coeffs : ℂ → ℂ) (hε : 0 < ε) (hγ : ContinuousOn γ (Icc a b)) : AEStronglyMeasurable (fun t => ∑ s ∈ S, coeffs s / (γ t - s)) (volume.restrict ({t | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b))`
- **What**: Finite Laurent sum `Σ coeffs s / (γ - s)` is AE-measurable on the ε-far good set.
- **How**: `Finset.aestronglyMeasurable_fun_sum`; each term is continuous on the good set with denominator non-vanishing (`norm_ne_zero_iff.mp (ne_of_gt ...)`), then `ContinuousOn.aestronglyMeasurable` on `measurableSet_multipoint_goodset`.
- **Hypotheses**: `0 < ε`, `γ` continuous on `Icc a b`.
- **Uses from project**: `measurableSet_multipoint_goodset`
- **Used by**: `aEStronglyMeasurable_decomposed_on_goodset`
- **Visibility**: private
- **Lines**: 224–234

### `private lemma aEStronglyMeasurable_decomposed_on_goodset`
- **Type**: `{g_reg : ℂ → ℂ} {γ : ℝ → ℂ} {a b ε : ℝ} {P : Finset ℝ} (S : Finset ℂ) (coeffs : ℂ → ℂ) (hε : 0 < ε) (hg : ContinuousOn g_reg (γ '' Icc a b)) (hγ : ContinuousOn γ (Icc a b)) (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) : AEStronglyMeasurable (fun t => (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t) (volume.restrict ({t | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b))`
- **What**: Decomposed integrand `(regular + Laurent) · γ'` is AE-measurable on the good set.
- **How**: `hg.comp hγ` gives `g_reg ∘ γ` continuous on Icc, then add `aEStronglyMeasurable_singularSum_on_goodset` and multiply by `aEStronglyMeasurable_of_continuousOn_off_finite hγ'_off_P` (all restricted to good set via `Measure.restrict_mono`).
- **Hypotheses**: `0 < ε`, `g_reg`, `γ`, `deriv γ` continuity assumptions.
- **Uses from project**: `aEStronglyMeasurable_singularSum_on_goodset`, `aEStronglyMeasurable_of_continuousOn_off_finite`
- **Used by**: `aEStronglyMeasurable_pv_integrand_decomposed`
- **Visibility**: private
- **Lines**: 236–250

### `private lemma goodset_piecewise_ae_eq_decomposed`
- **Type**: `{g_reg : ℂ → ℂ} {γ : ℝ → ℂ} {a b ε : ℝ} (S : Finset ℂ) (coeffs : ℂ → ℂ) : ... =ᵐ[volume.restrict (Icc a b)] (... ).piecewise ...`
- **What**: AE equality between the "if-near-pole-then-0" and the `Set.piecewise` form of the decomposed integrand.
- **How**: Same scheme as `goodset_piecewise_ae_eq_multipoint`: `filter_upwards`, case on `ht_good`, push `∃/∀`.
- **Hypotheses**: none additional.
- **Uses from project**: []
- **Used by**: `aEStronglyMeasurable_pv_integrand_decomposed`
- **Visibility**: private
- **Lines**: 252–271
- **Notes**: 20 lines.

### `theorem aEStronglyMeasurable_pv_integrand_decomposed`
- **Type**: `{g_reg : ℂ → ℂ} {γ : ℝ → ℂ} {a b ε : ℝ} {P : Finset ℝ} (S : Finset ℂ) (coeffs : ℂ → ℂ) (hε : 0 < ε) (hg : ContinuousOn g_reg (γ '' Icc a b)) (hγ : ContinuousOn γ (Icc a b)) (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) : AEStronglyMeasurable (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t) (volume.restrict (Icc a b))`
- **What**: Decomposed (regular + Laurent) PV integrand is AE strongly measurable on `Icc a b`.
- **How**: `AEStronglyMeasurable.piecewise (measurableSet_multipoint_goodset)` + `aEStronglyMeasurable_decomposed_on_goodset` + `aestronglyMeasurable_const`, then `congr (goodset_piecewise_ae_eq_decomposed S coeffs).symm`.
- **Hypotheses**: as above.
- **Uses from project**: `measurableSet_multipoint_goodset`, `aEStronglyMeasurable_decomposed_on_goodset`, `goodset_piecewise_ae_eq_decomposed`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 273–283

### `theorem integrableOn_of_bounded_aeMeasurable`
- **Type**: `{f : ℝ → ℂ} {a b : ℝ} (M : ℝ) (hf_meas : AEStronglyMeasurable f (volume.restrict (Icc a b))) (hf_bound : ∀ x ∈ Icc a b, ‖f x‖ ≤ M) : IntegrableOn f (Icc a b) volume`
- **What**: AE-measurable functions bounded by `M` on a compact `Icc` are integrable.
- **How**: `IntegrableOn.of_bound measure_Icc_lt_top hf_meas (max M 0)` with `filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet]` and `le_max_left`.
- **Hypotheses**: `f` AE strongly measurable on `Icc a b`, pointwise norm bound on `Icc a b`.
- **Uses from project**: []
- **Used by**: `intervalIntegrable_cauchyPrincipalValueIntegrandOn`, `intervalIntegrable_residueTerm`
- **Visibility**: public
- **Lines**: 285–292

### `theorem tendsto_integral_of_dominated'`
- **Type**: `{a b : ℝ} {F : ℝ → ℝ → ℂ} {f : ℝ → ℂ} {g : ℝ → ℝ} (hF_meas : ∀ ε > 0, AEStronglyMeasurable (F ε) (volume.restrict (Ι a b))) (hF_le : ∀ ε > 0, ∀ᵐ t ∂volume, t ∈ Ι a b → ‖F ε t‖ ≤ g t) (hg_int : IntervalIntegrable g volume a b) (hF_lim : ∀ᵐ t ∂volume, t ∈ Ι a b → Tendsto (fun ε => F ε t) (𝓝[>] 0) (𝓝 (f t))) : Tendsto (fun ε => ∫ t in a..b, F ε t) (𝓝[>] 0) (𝓝 (∫ t in a..b, f t))`
- **What**: Dominated convergence for interval integrals along the filter `𝓝[>] 0`.
- **How**: Apply `intervalIntegral.tendsto_integral_filter_of_dominated_convergence g` with `self_mem_nhdsWithin` to discharge the "eventually `ε > 0`" requirements.
- **Hypotheses**: AE-measurability, AE-bound, dominating `g` integrable, AE-pointwise limit.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 294–304

### `lemma finset_discrete_min_sep`
- **Type**: `(S0 : Finset ℂ) (hS0_nonempty : S0.Nonempty) (hS0_discrete : ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → 0 < ‖s' - s‖) : ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖`
- **What**: A finite, pairwise-distinct subset of `ℂ` has a positive minimum pairwise separation.
- **How**: `by_cases S0.card ≤ 1`: singleton case trivially uses `δ = 1` and contradiction from `hne`. Otherwise build `dists : Finset ℝ := S0.biUnion (s => (S0.filter (· ≠ s)).image (fun s' => ‖s' - s‖))`, take `δ := dists.min'` using `Finset.min'_mem` for positivity and `Finset.min'_le` for the bound.
- **Hypotheses**: `S0` nonempty, pairwise distinct.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 308–354
- **Notes**: 47 lines.

### `lemma disjoint_balls_of_small_epsilon`
- **Type**: `(S0 : Finset ℂ) (ε : ℝ) (_hε : 0 < ε) (δ : ℝ) (_hδ : 0 < δ) (hε_small : ε < δ / 2) (h_sep : ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖) : ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → Disjoint (Metric.ball s ε) (Metric.ball s' ε)`
- **What**: Balls of radius `ε < δ/2` around distinct points with separation `≥ δ` are disjoint.
- **How**: `Metric.ball_disjoint_ball` requires `ε + ε ≤ dist s s'`; rewrite `dist = norm_sub` and use `h_sep` + `linarith` with `hε_small`.
- **Hypotheses**: positive ε, δ; `ε < δ/2`; minimum separation `δ` on `S0`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 357–368

### `lemma continuousOn_image_bounded`
- **Type**: `{g : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} (hγ_cont : ContinuousOn γ (Icc a b)) (hg_cont : ContinuousOn g (γ '' Icc a b)) : ∃ Mg : ℝ, ∀ z ∈ γ '' Icc a b, ‖g z‖ ≤ Mg`
- **What**: Continuous functions on the image of a compact interval are bounded.
- **How**: `(isCompact_Icc.image_of_continuousOn hγ_cont).exists_bound_of_continuousOn hg_cont`.
- **Hypotheses**: `γ` continuous on Icc, `g` continuous on the image.
- **Uses from project**: []
- **Used by**: `intervalIntegrable_cauchyPrincipalValueIntegrandOn`
- **Visibility**: public
- **Lines**: 373–376

### `lemma intervalIntegrable_cauchyPrincipalValueIntegrandOn`
- **Type**: `{S0 : Finset ℂ} {f : ℂ → ℂ} {γ : PiecewiseC1Immersion} {ε : ℝ} (_hε : 0 < ε) (hf_cont : ContinuousOn f (γ.toFun '' Icc γ.a γ.b)) : IntervalIntegrable (cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε) volume γ.a γ.b`
- **What**: The multi-point CPV integrand (zero near poles, `f∘γ · γ'` elsewhere) is interval-integrable along the curve.
- **How**: Bound the integrand by `|Mf|·|Mγ'| + 1` (split_ifs: zero branch positivity; non-zero branch uses `norm_mul` and `mul_le_mul` with `continuousOn_image_bounded` for `f` and `piecewiseC1Immersion_deriv_bounded` for `γ'`). Combine with AE-measurability via `aEStronglyMeasurable_pv_integrand_multipoint` and `integrableOn_of_bounded_aeMeasurable`, then convert via `intervalIntegrable_iff_integrableOn_Ioc_of_le`.
- **Hypotheses**: `0 < ε`, `f` continuous on the curve image.
- **Uses from project**: `continuousOn_image_bounded`, `piecewiseC1Immersion_deriv_bounded`, `aEStronglyMeasurable_pv_integrand_multipoint`, `integrableOn_of_bounded_aeMeasurable`, `cauchyPrincipalValueIntegrandOn`, `PiecewiseC1Immersion`, `PiecewiseC1Curve.deriv_continuous_off_partition`, `PiecewiseC1Curve.endpoints_in_partition`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 381–425
- **Notes**: 45 lines.

### `lemma intervalIntegrable_residueTerm`
- **Type**: `{γ : PiecewiseC1Immersion} {s c : ℂ} {ε : ℝ} (hε : 0 < ε) : IntervalIntegrable (fun t => if ‖γ.toFun t - s‖ > ε then (c / (γ.toFun t - s)) * deriv γ.toFun t else 0) volume γ.a γ.b`
- **What**: Single-pole residue integrand cut off at radius ε is interval-integrable.
- **How**: Bound by `M = ‖c‖/ε·|Mγ'| + 1` (`norm_mul`, `norm_div`, `div_le_div_of_nonneg_left` against `‖γ - s‖ > ε`), combine with AE-measurability from `aEStronglyMeasurable_pv_integrand_residue`, then `integrableOn_of_bounded_aeMeasurable` + `intervalIntegrable_iff_integrableOn_Ioc_of_le`.
- **Hypotheses**: `0 < ε`.
- **Uses from project**: `piecewiseC1Immersion_deriv_bounded`, `aEStronglyMeasurable_pv_integrand_residue`, `integrableOn_of_bounded_aeMeasurable`, `PiecewiseC1Immersion`, `PiecewiseC1Curve.deriv_continuous_off_partition`, `PiecewiseC1Curve.endpoints_in_partition`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 428–473
- **Notes**: 46 lines.

### `lemma aEStronglyMeasurable_pv_sum_residue`
- **Type**: `(S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (ε : ℝ) (hε : 0 < ε) (a b : ℝ) {P : Finset ℝ} (hγ_cont : ContinuousOn γ (Icc a b)) (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) : AEStronglyMeasurable (fun t => ∑ s ∈ S, if ‖γ t - s‖ > ε then residueSimplePole f s / (γ t - s) * deriv γ t else 0) (volume.restrict (Icc a b))`
- **What**: Finite sum of cut-off residue integrands over `S` is AE strongly measurable.
- **How**: `Finset.induction_on S`: empty → constant; insert step → AE-add of `aEStronglyMeasurable_pv_integrand_residue` (current `x`) and IH, then `congr` via `Finset.sum_insert hx`.
- **Hypotheses**: `0 < ε`, `γ` continuous, `deriv γ` continuous off `P`.
- **Uses from project**: `aEStronglyMeasurable_pv_integrand_residue`, `residueSimplePole`
- **Used by**: `aEStronglyMeasurable_multipointPV_diff`
- **Visibility**: public
- **Lines**: 477–491

### `lemma aEStronglyMeasurable_multipointPV_diff`
- **Type**: `(S0 : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (ε : ℝ) (hε : 0 < ε) (a b : ℝ) {P : Finset ℝ} (hf_cont : ContinuousOn f (γ '' Set.uIcc a b)) (hγ_cont : ContinuousOn γ (Set.uIcc a b)) (hγ'_off_P : ContinuousOn (deriv γ) (Set.uIcc a b \ P)) : AEStronglyMeasurable (fun t => cauchyPrincipalValueIntegrandOn S0 f γ ε t - ∑ s ∈ S0, if ‖γ t - s‖ > ε then residueSimplePole f s / (γ t - s) * deriv γ t else 0) (volume.restrict (Ι a b))`
- **What**: The "decomposition difference" integrand (CPV integrand minus sum of cut-off residues) is AE strongly measurable on `Ι a b`.
- **How**: `rcases le_or_gt a b`. Each case rewrites `Set.uIcc = Icc a b` (or `Icc b a`), then `AEStronglyMeasurable.sub` between `aEStronglyMeasurable_pv_integrand_multipoint` and `aEStronglyMeasurable_pv_sum_residue`, `mono_measure` from `Ι a b ⊆ Icc` (via `Set.uIoc_of_le` and `Set.Ioc_subset_Icc_self`).
- **Hypotheses**: `0 < ε`; `f`, `γ`, `deriv γ` continuity over `Set.uIcc`.
- **Uses from project**: `aEStronglyMeasurable_pv_integrand_multipoint`, `aEStronglyMeasurable_pv_sum_residue`, `cauchyPrincipalValueIntegrandOn`, `residueSimplePole`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 493–521
- **Notes**: 29 lines.

## File Summary
Multi-point Cauchy Principal Value infrastructure: measurability of cut-off integrands at finite singular sets `S0`, integrability bounds using `PiecewiseC1Immersion`, dominated-convergence variant for `𝓝[>] 0`, and the technical separation lemma `finset_discrete_min_sep`. Two private helpers (`measurableSet_*`) and a piecewise AE-equality drive the main AE-measurability theorems. Public API: `aEStronglyMeasurable_of_continuousOn_off_finite`, `aEStronglyMeasurable_pv_integrand_decomposed`, `intervalIntegrable_cauchyPrincipalValueIntegrandOn`, `intervalIntegrable_residueTerm`, `aEStronglyMeasurable_pv_sum_residue`, `aEStronglyMeasurable_multipointPV_diff`, `tendsto_integral_of_dominated'`, plus separation lemmas. 0 sorry, no `set_option`.
