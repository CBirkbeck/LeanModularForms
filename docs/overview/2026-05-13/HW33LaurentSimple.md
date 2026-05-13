# Inventory: HW33LaurentSimple.lean

File: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HW33LaurentSimple.lean
Lines: 479

### `theorem laurentHigherOrderPolarAt_eventuallyEq_analyticAt`
- **Type**: `{γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (hSimple : ∀ s ∈ S, HasSimplePoleAt f s) {s : ℂ} (hs : s ∈ S) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ (laurentHigherOrderPolarAt hCondB s hs) =ᶠ[𝓝[≠] s] g`
- **What**: Per-pole `laurentHigherOrderPolarAt s` is eventually equal to an analytic function in the punctured neighborhood of `s`, under simple-pole hypothesis.
- **How**: `by_cases h_cross : IsCrossed γ s`. **Crossed**: `regularPart - laurentAnalyticPartAt` is analytic; `filter_upwards [pole_eventually_eq, laurent_eq]` and `linear_combination` (using `(hSimple s hs).eventually_eq`, `f_eq_analyticPart_plus_polarPart_eventually`, `residue_eq_coeff`). **Uncrossed**: `laurentHigherOrderPolarAt = 0` trivially.
- **Hypotheses**: `SatisfiesConditionB γ f S`, `∀ s ∈ S, HasSimplePoleAt f s`, `s ∈ S`.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `HasSimplePoleAt`, `IsCrossed`, `HasSimplePoleAt.regularPart`, `HasSimplePoleAt.regularPart_analyticAt`, `HasSimplePoleAt.eventually_eq`, `HasSimplePoleAt.coeff`, `residue_eq_coeff`, `residue`, `laurentAnalyticPartAt`, `laurentAnalyticPartAt_analyticAt`, `laurentHigherOrderPolarAt`, `laurentPolarPartAt`, `f_eq_analyticPart_plus_polarPart_eventually`
- **Used by**: `laurentHigherOrderPolar_eventuallyEq_analyticAt`
- **Visibility**: public
- **Lines**: 77-105
- **Notes**: >10 lines

### `theorem laurentHigherOrderPolar_eventuallyEq_analyticAt`
- **Type**: `(hCondB : SatisfiesConditionB γ f S) (hSimple : ∀ s ∈ S, HasSimplePoleAt f s) {s : ℂ} (hs : s ∈ S) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ (laurentHigherOrderPolar hCondB) =ᶠ[𝓝[≠] s] g`
- **What**: The aggregate `laurentHigherOrderPolar` (finite sum over `S`) is eventually equal to an analytic function at every `s ∈ S`.
- **How**: Get analytic extension `g_s` for `s` via `laurentHigherOrderPolarAt_eventuallyEq_analyticAt`; define `rest` = sum over `t.1 ≠ s` of `laurentHigherOrderPolarAt t.1`; prove `rest` is analytic at `s` using `Finset.analyticAt_fun_sum` + `Complex.analyticAt_iff_eventually_differentiableAt` + `laurentHigherOrderPolarAt_differentiableAt` (singularity at `t.1` ≠ `s`); decompose the full sum as `s-term + rest` via `Finset.sum_filter_add_sum_filter_not` and singleton filter `S.attach.filter (·.1 = s) = {⟨s, hs⟩}`.
- **Hypotheses**: same as above.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `HasSimplePoleAt`, `laurentHigherOrderPolarAt`, `laurentHigherOrderPolarAt_eventuallyEq_analyticAt`, `laurentHigherOrderPolarAt_differentiableAt`, `laurentHigherOrderPolar`
- **Used by**: `laurentHigherOrderPolar_correction_differentiableOn`
- **Visibility**: public
- **Lines**: 109-150
- **Notes**: >10 lines

### `def laurentHigherOrderPolarCorrection`
- **Type**: `(hCondB : SatisfiesConditionB γ f S) (z : ℂ) : ℂ`
- **What**: "Limit-corrected" higher-order polar function: equals `laurentHigherOrderPolar` off `S` and the punctured-nhd limit at each `s ∈ S`. Mirrors `laurentHolomorphicRemainderCorrection`.
- **How**: `if z ∈ ↑S then limUnder (𝓝[≠] z) (laurentHigherOrderPolar hCondB) else laurentHigherOrderPolar hCondB z` using `Classical`.
- **Hypotheses**: implicit context.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `laurentHigherOrderPolar`
- **Used by**: `laurentHigherOrderPolarCorrection_eventuallyEq_analyticExt`, `laurentHigherOrderPolarCorrection_eventuallyEq_polar`, `laurentHigherOrderPolar_correction_differentiableOn`, `cpvIntegrandOn_polar_eq_correction`, `h_polar_cancel_of_conditionB_simple`, `hI_polar_of_conditionB_simple`
- **Visibility**: public (`noncomputable def`)
- **Lines**: 157-162
- **Notes**: none

### `lemma laurentHigherOrderPolarCorrection_eventuallyEq_analyticExt`
- **Type**: `(hCondB) {z : ℂ} (g_z : ℂ → ℂ) (hzS : z ∈ ↑S) (hg_z_an : AnalyticAt ℂ g_z z) (hg_z_eq : (laurentHigherOrderPolar hCondB) =ᶠ[𝓝[≠] z] g_z) : laurentHigherOrderPolarCorrection hCondB =ᶠ[𝓝 z] g_z`
- **What**: At a pole `z ∈ S`, the correction agrees with its analytic extension `g_z` on a *full* (not just punctured) neighborhood of `z`.
- **How**: Compute `limUnder (𝓝[≠] z) (laurentHigherOrderPolar) = g_z z` via `hg_z_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr' ... |>.limUnder_eq`. Use `mem_nhdsWithin.mp hg_z_eq` to extract open `V`. Combine with `(↑(S.erase z))ᶜ ∈ 𝓝 z` (Finset complement open, z ∉ erase). Case-split on `w = z` vs `w ≠ z`.
- **Hypotheses**: `z ∈ ↑S`, `g_z` analytic at `z`, eventual agreement on `𝓝[≠] z`.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `laurentHigherOrderPolar`, `laurentHigherOrderPolarCorrection`
- **Used by**: `laurentHigherOrderPolar_correction_differentiableOn`
- **Visibility**: private
- **Lines**: 166-197
- **Notes**: >10 lines

### `lemma laurentHigherOrderPolarCorrection_eventuallyEq_polar`
- **Type**: `(hCondB) {z : ℂ} (hzS : z ∉ ↑S) : laurentHigherOrderPolarCorrection hCondB =ᶠ[𝓝 z] laurentHigherOrderPolar hCondB`
- **What**: Off `S`, the correction agrees with `laurentHigherOrderPolar` on a full neighborhood.
- **How**: `Filter.mem_of_superset` of the open complement of `↑S` (closed Finset), and definitional unfolding.
- **Hypotheses**: `z ∉ ↑S`.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `laurentHigherOrderPolar`, `laurentHigherOrderPolarCorrection`
- **Used by**: `laurentHigherOrderPolar_correction_differentiableOn`
- **Visibility**: private
- **Lines**: 200-209
- **Notes**: none

### `theorem laurentHigherOrderPolar_correction_differentiableOn`
- **Type**: `(hCondB) (hSimple : ∀ s ∈ S, HasSimplePoleAt f s) {U : Set ℂ} (hU : IsOpen U) (hS_in_U : ↑S ⊆ U) : DifferentiableOn ℂ (laurentHigherOrderPolarCorrection hCondB) U`
- **What**: Riemann removable-singularity bridge: the correction is differentiable on all of `U`.
- **How**: `intro z hz`; `by_cases hzS : z ∈ ↑S`. **In S**: get analytic extension `g_z` via `laurentHigherOrderPolar_eventuallyEq_analyticAt`; use `laurentHigherOrderPolarCorrection_eventuallyEq_analyticExt` and `.differentiableAt.congr_of_eventuallyEq`. **Off S**: use `laurentHigherOrderPolar_differentiableAt` and `laurentHigherOrderPolarCorrection_eventuallyEq_polar`.
- **Hypotheses**: `SatisfiesConditionB`, `∀ s ∈ S, HasSimplePoleAt f s`, `IsOpen U`, `↑S ⊆ U`.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `HasSimplePoleAt`, `laurentHigherOrderPolar_eventuallyEq_analyticAt`, `laurentHigherOrderPolarCorrection_eventuallyEq_analyticExt`, `laurentHigherOrderPolar_differentiableAt`, `laurentHigherOrderPolarCorrection_eventuallyEq_polar`, `laurentHigherOrderPolarCorrection`
- **Used by**: `h_polar_cancel_of_conditionB_simple`, `hI_polar_of_conditionB_simple`
- **Visibility**: public
- **Lines**: 213-232
- **Notes**: >10 lines

### `lemma cpvIntegrandOn_polar_eq_correction`
- **Type**: `(hCondB) {ε : ℝ} (hε_pos : 0 < ε) (t : ℝ) : cpvIntegrandOn S (laurentHigherOrderPolar hCondB) γE ε t = cpvIntegrandOn S (laurentHigherOrderPolarCorrection hCondB) γE ε t`
- **What**: The cpv integrand (with cutoff at radius `ε`) for `laurentHigherOrderPolar` and its correction agree pointwise.
- **How**: `by_cases h_cutoff` on whether the path point is within `ε` of any pole. **If cutoff active**: both `cpvIntegrandOn` return zero (via `if_pos`). **Off cutoff**: path point ∉ `↑S` (else it'd be its own ε-neighbor), so correction definitionally equals polar.
- **Hypotheses**: `0 < ε`.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `cpvIntegrandOn`, `laurentHigherOrderPolar`, `laurentHigherOrderPolarCorrection`
- **Used by**: `h_polar_cancel_of_conditionB_simple`, `hI_polar_of_conditionB_simple`
- **Visibility**: private
- **Lines**: 239-260
- **Notes**: >10 lines

### `lemma cpvIntegrandOn_holo_eq_correction`
- **Type**: `(hCondB) {ε : ℝ} (hε_pos : 0 < ε) (t : ℝ) : cpvIntegrandOn S (laurentHolomorphicRemainder hCondB) γE ε t = cpvIntegrandOn S (laurentHolomorphicRemainderCorrection hCondB) γE ε t`
- **What**: Same as above for the holomorphic remainder and its correction.
- **How**: Same structure: `by_cases h_cutoff`; both vanish via `if_pos` under cutoff; off cutoff, path point not in `S` so correction = remainder.
- **Hypotheses**: `0 < ε`.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `cpvIntegrandOn`, `laurentHolomorphicRemainder`, `laurentHolomorphicRemainderCorrection`
- **Used by**: `hI_holo_of_conditionB_simple`
- **Visibility**: private
- **Lines**: 263-284
- **Notes**: >10 lines

### `theorem h_polar_cancel_of_conditionB_simple`
- **Type**: `{U} (hU_open) (hU_ne) {S} (hS_in_U) {f} (γ : ClosedPwC1Immersion x) (h_null : IsNullHomologous γ.toPwC1Immersion U) (hSimple : ∀ s ∈ S, HasSimplePoleAt f s) (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S) : HasCauchyPVOn S (laurentHigherOrderPolar hCondB) γ 0`
- **What**: Auto-discharge of `h_polar_cancel`: the higher-order Laurent polar part has zero Cauchy principal value over `S` along `γ`.
- **How**: `classical`. Set up γ-paths/correction. Get `Set.Countable` preimage from `γ.preimage_countable S`. Differentiability of correction via `laurentHigherOrderPolar_correction_differentiableOn`. Obtain Lipschitz extension via `ClosedPwC1Immersion.lipschitzWith_extend`. Dixon: `contourIntegral_analytic_eq_zero_of_nullHomologous` gives correction integral = 0. Continuity on image: bound `γE '' Icc 0 1 ⊆ U`. `hasCauchyPVOn_continuousOn_of_countable_preimage` for correction. Use `cpvIntegrandOn_polar_eq_correction` to congruence-transfer back to original integrand via `.congr'`.
- **Hypotheses**: 8 paper hypotheses (`hU_open`, `hU_ne`, `hS_in_U`, `γ closed immersion`, `h_null`, `hSimple`, `hCondB`).
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.lipschitzWith_extend`, `ClosedPwC1Immersion.preimage_countable`, `IsNullHomologous`, `IsNullHomologous.image_subset`, `HasSimplePoleAt`, `SatisfiesConditionB`, `HasCauchyPVOn`, `HasCauchyPVOn.congr'`, `cpvIntegrandOn`, `cpvIntegrandOn_polar_eq_correction`, `laurentHigherOrderPolar`, `laurentHigherOrderPolarCorrection`, `laurentHigherOrderPolar_correction_differentiableOn`, `contourIntegral_analytic_eq_zero_of_nullHomologous`, `hasCauchyPVOn_continuousOn_of_countable_preimage`, `PiecewiseC1Path.contourIntegral`, `PwC1Immersion`
- **Used by**: `hw_3_3_simple_with_crossData_no_laurent_oracles`
- **Visibility**: public
- **Lines**: 290-331
- **Notes**: >10 lines

### `theorem hI_polar_of_conditionB_simple`
- **Type**: `{U} (hU_open) {S} (hS_in_U) {f} (γ) (h_null) (hSimple) (hCondB) : ∀ ε > 0, IntervalIntegrable (fun t => cpvIntegrandOn S (laurentHigherOrderPolar hCondB) γE ε t) volume 0 1`
- **What**: Auto-discharge of `hI_polar`: the cutoff polar-part integrand is interval-integrable on `[0,1]`.
- **How**: `classical`; `intro ε hε_pos`. Continuity of correction on `γE '' Icc 0 1`. `IntervalIntegrable (deriv γE)` on `[0,1]` via Lipschitz bound on derivative (using `stronglyMeasurable_deriv` and `Measure.integrableOn_of_bounded`). Compose to get `corr ∘ γE` continuous on `uIcc`. Conclude contour integrand is interval-integrable (`continuousOn_mul`). Apply `cpvIntegrandOn_intervalIntegrable_of_contourIntegrand`. Finally `.congr` with `cpvIntegrandOn_polar_eq_correction`.
- **Hypotheses**: 7 paper hypotheses (omits `hU_ne`).
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.lipschitzWith_extend`, `IsNullHomologous`, `IsNullHomologous.image_subset`, `HasSimplePoleAt`, `SatisfiesConditionB`, `cpvIntegrandOn`, `cpvIntegrandOn_polar_eq_correction`, `cpvIntegrandOn_intervalIntegrable_of_contourIntegrand`, `laurentHigherOrderPolar`, `laurentHigherOrderPolarCorrection`, `laurentHigherOrderPolar_correction_differentiableOn`, `PiecewiseC1Path.contourIntegrand`, `norm_deriv_le_of_lipschitz`, `PwC1Immersion`
- **Used by**: `hw_3_3_simple_with_crossData_no_laurent_oracles`
- **Visibility**: public
- **Lines**: 336-382
- **Notes**: >10 lines

### `theorem hI_holo_of_conditionB_simple`
- **Type**: `{U} (hU_open) {S} (_hS_in_U) {f} (hf : DifferentiableOn ℂ f (U \ ↑S)) (γ) (h_null) (hSimple) (hCondB) : ∀ ε > 0, IntervalIntegrable (fun t => cpvIntegrandOn S (laurentHolomorphicRemainder hCondB) γE ε t) volume 0 1`
- **What**: Auto-discharge of `hI_holo`: the cutoff holomorphic-remainder integrand is interval-integrable.
- **How**: Mirrors `hI_polar_of_conditionB_simple` exactly but using `laurentHolomorphicRemainderCorrection` and `laurentHolomorphicRemainder_correction_differentiableOn` (which needs `hf` for the differentiability bound).
- **Hypotheses**: 8 paper-ish (uses `hf : DifferentiableOn ℂ f (U \ ↑S)`).
- **Uses from project**: same as `hI_polar_of_conditionB_simple` plus `laurentHolomorphicRemainder`, `laurentHolomorphicRemainderCorrection`, `laurentHolomorphicRemainder_correction_differentiableOn`, `cpvIntegrandOn_holo_eq_correction`
- **Used by**: `hw_3_3_simple_with_crossData_no_laurent_oracles`
- **Visibility**: public
- **Lines**: 385-429
- **Notes**: >10 lines; `_hS_in_U` parameter is unused (underscore).

### `theorem hw_3_3_simple_with_crossData_no_laurent_oracles`
- **Type**: `(hU_open) (hU_ne) (S) (hS_in_U) (f) (hf) (γ) (h_null) (hSimple) (hCondA) (hCondB) (crossData : ∀ s ∈ S, SingleCrossingData γ s) {δ} (hδ_pos) (h_avoid_pairs) (h_int_perpole) : HasCauchyPVOn S f γ (2 π I · ∑ s, w(s)·residue f s)`
- **What**: Simple-pole HW Theorem 3.3 with all three Laurent oracles (`h_polar_cancel`, `hI_polar`, `hI_holo`) auto-discharged. Remaining hypotheses: paper 8 + `crossData` for each pole + pairwise avoidance margin `δ` + per-pole CPV-integrand integrability for `residue f s / (z - s)`.
- **How**: Discharge the three Laurent oracles by calling the three auto-discharge theorems, then chain into `hw_3_3_simple_with_crossData`.
- **Hypotheses**: 8 paper + per-pole `SingleCrossingData` + pairwise avoidance + per-pole integrability.
- **Uses from project**: `ClosedPwC1Immersion`, `IsNullHomologous`, `HasSimplePoleAt`, `SatisfiesConditionA'`, `SatisfiesConditionB`, `SingleCrossingData`, `HasCauchyPVOn`, `cpvIntegrandOn`, `residue`, `generalizedWindingNumber`, `poleOrderAt`, `h_polar_cancel_of_conditionB_simple`, `hI_polar_of_conditionB_simple`, `hI_holo_of_conditionB_simple`, `hw_3_3_simple_with_crossData`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 446-475
- **Notes**: >10 lines

## File Summary

HW33LaurentSimple.lean: 479 lines, namespace `LeanModularForms`. Uses the analytic-correction strategy from `HW33HoloCancel` to auto-discharge three Laurent-side oracles (`h_polar_cancel`, `hI_polar`, `hI_holo`) under simple-pole hypotheses and Condition (B). The architecture:

1. **Step 1 — Eventual analyticity**: `laurentHigherOrderPolarAt_eventuallyEq_analyticAt` and its sum-over-S version. Under `HasSimplePoleAt f s`, the higher-order polar contribution = `regularPart − analyticPart` (both analytic).
2. **Step 2 — Global correction**: `laurentHigherOrderPolarCorrection` patches the function to its analytic extension at each pole; Riemann removable-singularity gives `DifferentiableOn ℂ correction U` (`laurentHigherOrderPolar_correction_differentiableOn`).
3. **Step 3 — Integrand equality**: cutoff integrands for the original and the correction agree pointwise (`cpvIntegrandOn_polar_eq_correction`, `cpvIntegrandOn_holo_eq_correction`).
4. **Step 4 — Dixon + integrand equality**: `h_polar_cancel_of_conditionB_simple` uses Dixon (`contourIntegral_analytic_eq_zero_of_nullHomologous`) on the correction + `hasCauchyPVOn_continuousOn_of_countable_preimage` + congruence to discharge `h_polar_cancel`.
5. **Step 5 — Integrability**: `hI_polar_of_conditionB_simple` and `hI_holo_of_conditionB_simple` discharge interval-integrability via continuity of correction on the path image + Lipschitz bound on `deriv γE`.
6. **Final**: `hw_3_3_simple_with_crossData_no_laurent_oracles` packages it all.

No sorries, no axioms, no `set_option`s, no TODOs. Three private helper lemmas, five public theorems, one public def.
