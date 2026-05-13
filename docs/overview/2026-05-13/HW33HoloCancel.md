# HW33HoloCancel.lean Inventory

### `noncomputable def laurentHolomorphicRemainderCorrection`
- **Type**: `{γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (z : ℂ) → ℂ`
- **What**: The "limit-corrected" Laurent holomorphic remainder: equals `laurentHolomorphicRemainder hCondB z` away from `S`, and the punctured-nhd limit at each `s ∈ S`. Mirrors `MeromorphicCauchy.correction` for the simple-pole case.
- **How**: `if z ∈ ↑S then limUnder (𝓝[≠] z) (laurentHolomorphicRemainder hCondB) else laurentHolomorphicRemainder hCondB z`, in `open Classical`.
- **Hypotheses**: None beyond inputs (definition).
- **Uses from project**: [`laurentHolomorphicRemainder`, `SatisfiesConditionB`, `PwC1Immersion`]
- **Used by**: `laurentHolomorphicRemainderCorrection_eventuallyEq_analyticExt`, `laurentHolomorphicRemainderCorrection_eventuallyEq_rem`, `laurentHolomorphicRemainder_correction_differentiableOn`, `h_holo_cancel_of_conditionB`
- **Visibility**: public
- **Lines**: 56-61
- **Notes**: noncomputable

### `private lemma laurentHolomorphicRemainderCorrection_eventuallyEq_analyticExt`
- **Type**: `(hCondB) {z : ℂ} (g_z : ℂ → ℂ) (hzS : z ∈ ↑S) (hg_z_an : AnalyticAt ℂ g_z z) (hg_z_eq : laurentHolomorphicRemainder hCondB =ᶠ[𝓝[≠] z] g_z) → laurentHolomorphicRemainderCorrection hCondB =ᶠ[𝓝 z] g_z`
- **What**: At each pole `z ∈ S`, the correction equals the local analytic extension `g_z` in a *full* neighborhood of `z`.
- **How** (~25 lines): Establish `limUnder (𝓝[≠] z) (laurentHolomorphicRemainder …) = g_z z` from `hg_z_an.continuousAt.tendsto`. Then `correction z = g_z z` at the pole, and on `V ∩ (S.erase z)ᶜ` (`V` extracted from `hg_z_eq`), points are not in `S` so `correction` reduces to the remainder, which equals `g_z` on `V \ {z}` by hypothesis. Combine via `Filter.mem_of_superset (inter_mem …)`.
- **Hypotheses**: `z ∈ ↑S`; analytic extension `g_z` with `=ᶠ[𝓝[≠] z]`.
- **Uses from project**: [`laurentHolomorphicRemainderCorrection`, `laurentHolomorphicRemainder`]
- **Used by**: `laurentHolomorphicRemainder_correction_differentiableOn`
- **Visibility**: private
- **Lines**: 65-96
- **Notes**: > 30 lines

### `private lemma laurentHolomorphicRemainderCorrection_eventuallyEq_rem`
- **Type**: `(hCondB) {z : ℂ} (hzS : z ∉ ↑S) → laurentHolomorphicRemainderCorrection hCondB =ᶠ[𝓝 z] laurentHolomorphicRemainder hCondB`
- **What**: Off `S`, the correction is eventually equal to the remainder.
- **How** (~6 lines): Use `(↑S)ᶜ` open in a nhd of `z`; on that nhd the `if`-branch never triggers and the correction reduces to the remainder by definition.
- **Hypotheses**: `z ∉ ↑S`.
- **Uses from project**: [`laurentHolomorphicRemainderCorrection`, `laurentHolomorphicRemainder`]
- **Used by**: `laurentHolomorphicRemainder_correction_differentiableOn`
- **Visibility**: private
- **Lines**: 99-108
- **Notes**: none

### `theorem laurentHolomorphicRemainder_correction_differentiableOn`
- **Type**: `(hCondB) (hSimple : ∀ s ∈ S, HasSimplePoleAt f s) {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ ↑S)) → DifferentiableOn ℂ (laurentHolomorphicRemainderCorrection hCondB) U`
- **What**: Riemann removable-singularity bridge: the corrected remainder is differentiable on the full open set `U` (poles of the remainder are filled in).
- **How** (~15 lines): For `z ∈ U`, split on `z ∈ ↑S`. At a pole, take the analytic extension `g_z` from `laurentHolomorphicRemainder_eventuallyEq_analyticAt`; transfer differentiability of `g_z` to the correction via `congr_of_eventuallyEq` using `laurentHolomorphicRemainderCorrection_eventuallyEq_analyticExt`. Off `S`, transfer differentiability of the remainder (from `laurentHolomorphicRemainder_differentiableOn`) via `laurentHolomorphicRemainderCorrection_eventuallyEq_rem`.
- **Hypotheses**: Simple poles, `U` open, `f` differentiable off `S` on `U`.
- **Uses from project**: [`laurentHolomorphicRemainderCorrection`, `laurentHolomorphicRemainder`, `laurentHolomorphicRemainder_eventuallyEq_analyticAt`, `laurentHolomorphicRemainder_differentiableOn`, `laurentHolomorphicRemainderCorrection_eventuallyEq_analyticExt`, `laurentHolomorphicRemainderCorrection_eventuallyEq_rem`, `SatisfiesConditionB`, `HasSimplePoleAt`]
- **Used by**: `h_holo_cancel_of_conditionB`
- **Visibility**: public
- **Lines**: 112-132
- **Notes**: none

### `theorem contourIntegral_analytic_eq_zero_of_nullHomologous`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U) {K : NNReal} (hLip : LipschitzWith K γ.toPiecewiseC1Path.toPath.extend) → γ.toPiecewiseC1Path.contourIntegral g = 0`
- **What**: For null-homologous closed PwC¹ immersions in `U` and analytic `g`, the contour integral vanishes.
- **How** (~50 lines): Pick `w₀ ∈ U` off the image of `γ` (`exists_mem_not_mem_path_image_of_isOpen`) with quantitative avoidance `δ' > 0` (`avoids_delta_bound`). Apply Dixon to the auxiliary function `(z − w₀) · g(z)` (also analytic on `U`) via `dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded`; this gives `dixonFunction G U γ w = 0` for all `w`. Set up `IntervalIntegrable` integrability for `deriv γE` (Lipschitz bound), for `(γ t − w₀)⁻¹` (continuity off zero), and for `contourIntegrand g γP`; show the Cauchy-style integrand equals the original times `(γ t − w₀)/(γ t − w₀) = 1`, then invoke `contourIntegral_eq_zero_of_nullHomologous_at`.
- **Hypotheses**: `U` open and nonempty, `g` differentiable on `U`, `γ` null-homologous, `γ` Lipschitz.
- **Uses from project**: [`PwC1Immersion`, `PiecewiseC1Path`, `IsNullHomologous`, `IsNullHomologous.image_subset`, `IsNullHomologous.winding_zero_nhds_of_not_mem_of_closed`, `PiecewiseC1Path.contourIntegral`, `PiecewiseC1Path.contourIntegrand`, `ForMathlib.exists_mem_not_mem_path_image_of_isOpen`, `avoids_delta_bound`, `dixonFunction`, `dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded`, `contourIntegral_eq_zero_of_nullHomologous_at`, `norm_deriv_le_of_lipschitz`, `stronglyMeasurable_deriv`]
- **Used by**: `h_holo_cancel_of_conditionB`
- **Visibility**: public
- **Lines**: 138-202
- **Notes**: > 30 lines

### `private lemma cpvCutoff_isClosed`
- **Type**: `{γE : ℝ → ℂ} (hγE : Continuous γE) (S : Finset ℂ) (ε : ℝ) → IsClosed {t : ℝ | ∃ s ∈ S, ‖γE t − s‖ ≤ ε}`
- **What**: The ε-cutoff condition (point on the curve is within ε of some `s ∈ S`) is closed in `t`.
- **How** (~6 lines): Rewrite as `⋃ s ∈ S, {t | ‖γE t − s‖ ≤ ε}` and apply `Finset.finite_toSet.isClosed_biUnion` with `isClosed_le`.
- **Hypotheses**: `γE` continuous.
- **Uses from project**: []
- **Used by**: `cpvCutoff_measurableSet`
- **Visibility**: private
- **Lines**: 207-217
- **Notes**: none

### `private lemma cpvCutoff_measurableSet`
- **Type**: `{γE : ℝ → ℂ} (hγE : Continuous γE) (S : Finset ℂ) (ε : ℝ) → MeasurableSet {t : ℝ | ∃ s ∈ S, ‖γE t − s‖ ≤ ε}`
- **What**: The same cutoff set is measurable.
- **How**: Closed implies measurable.
- **Hypotheses**: `γE` continuous.
- **Uses from project**: [`cpvCutoff_isClosed`]
- **Used by**: `hasCauchyPVOn_continuousOn_of_countable_preimage`
- **Visibility**: private
- **Lines**: 219-222
- **Notes**: none

### `private lemma cpvIntegrandOn_tendsto_pointwise_of_not_mem`
- **Type**: `{γE : ℝ → ℂ} {S : Finset ℂ} {g : ℂ → ℂ} {t : ℝ} (h_not_mem : γE t ∉ ↑S) → Tendsto (fun ε => cpvIntegrandOn S g γE ε t) (𝓝[>] 0) (𝓝 (g (γE t) * deriv γE t))`
- **What**: At every `t` where `γE t` is not in `S`, the ε-cutoff integrand becomes eventually equal to the full contour integrand `g(γE t) · γE'(t)` as `ε → 0⁺`.
- **How** (~16 lines): Case on `S` nonempty. If nonempty, set `δ := S.inf' hS (·‖γE t − ·‖)`; `δ > 0` since `γE t ∉ S`; eventually `ε < δ ≤ ‖γE t − s‖` for all `s ∈ S`, so the `if` branch fails and `cpvIntegrandOn` reduces to the full integrand by `cpvIntegrandOn_of_forall_gt`. If empty, the same holds by `cpvIntegrandOn_empty`.
- **Hypotheses**: `γE t ∉ ↑S`.
- **Uses from project**: [`cpvIntegrandOn`, `cpvIntegrandOn_of_forall_gt`, `cpvIntegrandOn_empty`]
- **Used by**: `hasCauchyPVOn_continuousOn_of_countable_preimage`
- **Visibility**: private
- **Lines**: 226-249
- **Notes**: none

### `private lemma norm_cpvIntegrandOn_le`
- **Type**: `{S : Finset ℂ} {g : ℂ → ℂ} {γE : ℝ → ℂ} {ε : ℝ} {t : ℝ} → ‖cpvIntegrandOn S g γE ε t‖ ≤ ‖g (γE t)‖ · ‖deriv γE t‖`
- **What**: Pointwise norm bound on the ε-cutoff integrand by the product of `‖g(γE t)‖` and `‖γE'(t)‖`.
- **How** (~5 lines): Split the `if`: zero branch is `0 ≤ ‖g(·)‖ · ‖·‖` (`mul_nonneg`); non-zero branch is `norm_mul`.
- **Hypotheses**: None.
- **Uses from project**: [`cpvIntegrandOn`]
- **Used by**: `hasCauchyPVOn_continuousOn_of_countable_preimage`
- **Visibility**: private
- **Lines**: 252-258
- **Notes**: none

### `theorem hasCauchyPVOn_continuousOn_of_countable_preimage`
- **Type**: `{γ : PiecewiseC1Path x x} (S : Finset ℂ) {g : ℂ → ℂ} (h_g_cont : ContinuousOn g (γ.toPath.extend '' Icc 0 1)) {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) (h_preimage : Set.Countable {t ∈ Icc 0 1 | γ t ∈ ↑S}) → HasCauchyPVOn S g γ (γ.contourIntegral g)`
- **What**: DCT-based bridge: under countability of `γ⁻¹(S) ∩ [0,1]`, the ε-truncated CPV integral of `g` along `γ` converges to the contour integral.
- **How** (~75 lines): Bound `‖g(γE t)‖ ≤ M'` on `[0,1]` (compactness, `max M 0`); bound `‖γE'(t)‖ ≤ K` (Lipschitz). Dominating function `M' · K`. AEStronglyMeasurable: write the cutoff integrand as a measurable `Set.piecewise` (the cutoff set is measurable via `cpvCutoff_measurableSet`). Apply `intervalIntegral.tendsto_integral_filter_of_dominated_convergence`; the three premises are: filter-eventual measurability (via `self_mem_nhdsWithin` + `uIoc_of_le`), pointwise bound (via `norm_cpvIntegrandOn_le` and `gcongr`), and pointwise convergence almost everywhere (via `h_preimage.ae_notMem` and `cpvIntegrandOn_tendsto_pointwise_of_not_mem`).
- **Hypotheses**: `g` continuous on the image of `γ`; `γ` Lipschitz; γ-preimage of `S` countable.
- **Uses from project**: [`PiecewiseC1Path`, `cpvIntegrandOn`, `HasCauchyPVOn`, `PiecewiseC1Path.contourIntegral`, `cpvCutoff_measurableSet`, `norm_cpvIntegrandOn_le`, `cpvIntegrandOn_tendsto_pointwise_of_not_mem`, `norm_deriv_le_of_lipschitz`, `stronglyMeasurable_deriv`]
- **Used by**: `h_holo_cancel_of_conditionB`
- **Visibility**: public
- **Lines**: 263-343
- **Notes**: > 30 lines

### `theorem h_holo_cancel_of_conditionB`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U \ ↑S)) (γ : ClosedPwC1Immersion x) (h_null : IsNullHomologous γ.toPwC1Immersion U) (hSimple : ∀ s ∈ S, HasSimplePoleAt f s) (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S) → HasCauchyPVOn S (laurentHolomorphicRemainder hCondB) γ.toPwC1Immersion.toPiecewiseC1Path 0`
- **What**: Phase-4 headline: under (B), simple poles, null-homology, and the automatic countable preimage from `ClosedPwC1Immersion`, the CPV of the Laurent holomorphic remainder along `γ` is zero — discharging the `h_holo_cancel` oracle of `hw_3_3_paper`/`hw_3_3_tight`.
- **How** (~45 lines): (1) `γ.preimage_countable S` provides countability automatically; (2) `laurentHolomorphicRemainder_correction_differentiableOn` makes the correction differentiable on `U`; (3) `ClosedPwC1Immersion.lipschitzWith_extend` gives Lipschitzness, then `contourIntegral_analytic_eq_zero_of_nullHomologous` kills the correction's contour integral; (4) the correction's CPV equals its contour integral (now `0`) by `hasCauchyPVOn_continuousOn_of_countable_preimage`; (5) finally, the CPV of the original remainder equals the CPV of the correction because the ε-cutoff integrands agree pointwise — at points satisfying the cutoff `if`-branch both are `0`, and at points off the cutoff (in particular off `S`, since `‖γt − s‖ ≤ ε ≥ 0` would force a self-pole) the correction matches the remainder by definition — closed via `HasCauchyPVOn.congr'` + `intervalIntegral.integral_congr`.
- **Hypotheses**: `U` open nonempty; `S ⊆ U`; `f` differentiable off `S`; null-homology; simple poles; (B).
- **Uses from project**: [`laurentHolomorphicRemainder`, `laurentHolomorphicRemainderCorrection`, `laurentHolomorphicRemainder_correction_differentiableOn`, `contourIntegral_analytic_eq_zero_of_nullHomologous`, `hasCauchyPVOn_continuousOn_of_countable_preimage`, `ClosedPwC1Immersion`, `ClosedPwC1Immersion.preimage_countable`, `ClosedPwC1Immersion.lipschitzWith_extend`, `PwC1Immersion`, `PiecewiseC1Path`, `IsNullHomologous`, `IsNullHomologous.image_subset`, `HasCauchyPVOn`, `HasCauchyPVOn.congr'`, `SatisfiesConditionB`, `HasSimplePoleAt`, `cpvIntegrandOn`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 365-420
- **Notes**: > 30 lines

## File Summary

Discharges the `h_holo_cancel` oracle of HW Theorem 3.3 (paper-tight version) for simple-pole crossings under condition (B) and null-homology. Builds the Riemann-removable correction `laurentHolomorphicRemainderCorrection` of the holomorphic remainder, proves it is differentiable on all of `U` (`laurentHolomorphicRemainder_correction_differentiableOn`), invokes Dixon to kill its contour integral (`contourIntegral_analytic_eq_zero_of_nullHomologous`), then bridges CPV to the contour integral via dominated convergence (`hasCauchyPVOn_continuousOn_of_countable_preimage`). The headline `h_holo_cancel_of_conditionB` assembles these into the vanishing of the CPV of the original remainder, leveraging `ClosedPwC1Immersion.preimage_countable` for the automatic countability hypothesis.
