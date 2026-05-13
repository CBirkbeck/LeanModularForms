# HW33PVSing.md

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HW33PVSing.lean` (421 lines)

Namespace: `LeanModularForms`

### `theorem hasCauchyPVOn_div_sub_of_singleton_and_avoid_others`
- **Type**: `{γ : PiecewiseC1Path x x} (S : Finset ℂ) {s : ℂ} {c w : ℂ} (hs : s ∈ S) (hw : HasGeneralizedWindingNumber γ s w) {δ : ℝ} (hδ_pos : 0 < δ) (h_avoid : ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s'‖) : HasCauchyPVOn S (fun z => c / (z - s)) γ (2*π*I*w*c)`
- **What**: Lift a singleton CPV to a multi-pole CPV: if γ has a generalized winding number w at s ∈ S and avoids the other poles in `S \ {s}` with positive margin δ, then the CPV of `c/(z-s)` over the full pole set S equals `2πi·w·c`.
- **How**: Apply `hasCauchyPVOn_extend_of_avoid {s} S …` after rewriting `S \ {s}` membership via `Finset.mem_sdiff` + `Finset.mem_singleton`; base singleton CPV from `hasCauchyPVOn_singleton_div_sub`.
- **Hypotheses**: s ∈ S; generalized winding witness at s; avoidance of other poles.
- **Uses from project**: `PiecewiseC1Path`, `HasGeneralizedWindingNumber`, `HasCauchyPVOn`, `hasCauchyPVOn_extend_of_avoid`, `hasCauchyPVOn_singleton_div_sub`.
- **Used by**: `hPV_sing_of_winding_and_avoid_others`.
- **Visibility**: public
- **Lines**: 84-95
- **Notes**: none

### `theorem hPV_sing_from_per_pole_cpv`
- **Type**: `{γ : PiecewiseC1Path x x} (S : Finset ℂ) (c w : ℂ → ℂ) (h_per_pole : ∀ s ∈ S, HasCauchyPVOn S (fun z => c s / (z - s)) γ (2*π*I*w s*c s)) (h_per_pole_int : …) : HasCauchyPVOn S (principalPartSum S c) γ (∑ s ∈ S, 2*π*I*w s*c s)`
- **What**: Sum the per-pole CPVs to obtain the CPV of the principal-part-sum `∑ s, c s / (z-s)`. Output value is the winding-weighted residue formula.
- **How**: Direct invocation of `HasCauchyPVOn.finset_sum` (with `ι_set := S`); the resulting CPV is for `fun z => ∑ s ∈ S, c s / (z - s)`, which definitionally unfolds to `principalPartSum S c`.
- **Hypotheses**: per-pole CPV with respect to full pole set; per-pole CPV-integrand integrability for every ε > 0.
- **Uses from project**: `PiecewiseC1Path`, `HasCauchyPVOn`, `HasCauchyPVOn.finset_sum`, `cpvIntegrandOn`, `principalPartSum`.
- **Used by**: `hPV_sing_of_winding_and_avoid_others`.
- **Visibility**: public
- **Lines**: 103-115
- **Notes**: none

### `theorem hPV_sing_of_winding_and_avoid_others`
- **Type**: `{γ : PiecewiseC1Path x x} (S : Finset ℂ) (c w : ℂ → ℂ) (hw : ∀ s ∈ S, HasGeneralizedWindingNumber γ s (w s)) {δ : ℝ} (hδ_pos : 0 < δ) (h_avoid_pairs : ∀ s ∈ S, ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s'‖) (h_int : …) : HasCauchyPVOn S (principalPartSum S c) γ (∑ s ∈ S, 2*π*I*w s*c s)`
- **What**: Closed form of `hPV_sing` discharge for single-crossing (i.e., per-pole single-crossing) cases. Combines `hasCauchyPVOn_div_sub_of_singleton_and_avoid_others` (per pole) with `hPV_sing_from_per_pole_cpv` (sum).
- **How**: Compose the two preceding theorems.
- **Hypotheses**: per-pole generalized winding witnesses; pairwise avoidance with positive margin δ; per-pole CPV-integrand integrability.
- **Uses from project**: `PiecewiseC1Path`, `HasGeneralizedWindingNumber`, `HasCauchyPVOn`, `principalPartSum`, `cpvIntegrandOn`, `hasCauchyPVOn_div_sub_of_singleton_and_avoid_others`, `hPV_sing_from_per_pole_cpv`.
- **Used by**: `hPV_sing_of_conditionB`, `hPV_sing_of_conditionB_avoids`.
- **Visibility**: public
- **Lines**: 124-137
- **Notes**: none

### `theorem hPV_sing_of_conditionB`
- **Type**: `{U : Set ℂ} (_hU_open : IsOpen U) {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ} (γ : ClosedPwC1Immersion x) (_hSimple : ∀ s ∈ S, HasSimplePoleAt f s) (_hCondB : SatisfiesConditionB γ.toPwC1Immersion f S) (hw : ∀ s ∈ S, HasGeneralizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s (generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s)) {δ : ℝ} (hδ_pos : 0 < δ) (h_avoid_pairs) (h_int) : HasCauchyPVOn S (principalPartSum S (residue f)) γ.…path (∑ s, 2πI · generalizedWindingNumber γ_path s · residue f s)`
- **What**: Master-template form of `hPV_sing` discharge: signature matches the hypothesis name `hPV_sing` in `hw_3_3_paper` (with c = residue f). Unused hypotheses `_hU_open`, `_hS_in_U`, `_hSimple`, `_hCondB` kept for signature consistency.
- **How**: Direct delegation to `hPV_sing_of_winding_and_avoid_others` with `c = residue f` and `w = generalizedWindingNumber γ_path`.
- **Hypotheses**: per-pole canonical winding-number existence; pairwise avoidance; per-pole CPV-integrand integrability.
- **Uses from project**: `ClosedPwC1Immersion`, `SatisfiesConditionB`, `HasSimplePoleAt`, `HasGeneralizedWindingNumber`, `HasCauchyPVOn`, `principalPartSum`, `residue`, `generalizedWindingNumber`, `cpvIntegrandOn`, `hPV_sing_of_winding_and_avoid_others`.
- **Used by**: `hPV_sing_of_conditionB_singleCrossing`, `hPV_sing_of_conditionB_pointwise_winding`.
- **Visibility**: public
- **Lines**: 152-175
- **Notes**: none

### `theorem cpvIntegrandOn_div_sub_intervalIntegrable_of_avoids`
- **Type**: `(γ : ClosedPwC1Immersion x) (S : Finset ℂ) (s : ℂ) (c : ℂ) {δ : ℝ} (hδ_pos : 0 < δ) (hδ_bd : ∀ t ∈ Icc 0 1, δ ≤ ‖γ_path_extend t - s‖) {K : NNReal} (hLip : LipschitzWith K γ_path_extend) (ε : ℝ) : IntervalIntegrable (fun t => cpvIntegrandOn S (c/(z-s)) γ_path_extend ε t) volume 0 1`
- **What**: Integrability of the CPV integrand for a single simple-pole term, under avoidance with positive margin and Lipschitz path. Used to discharge the `h_int` residual.
- **How**: Apply `intervalIntegrable_pow_inv_mul_deriv_of_avoids` with k=1 to get integrability of `1/(γ(t)-s)^1 · γ'(t)`; multiply by constant c via `IntervalIntegrable.const_mul`; identify it pointwise with `PiecewiseC1Path.contourIntegrand`; transport through `cpvIntegrandOn_intervalIntegrable_of_contourIntegrand`. Key lemma: `intervalIntegrable_pow_inv_mul_deriv_of_avoids`.
- **Hypotheses**: avoidance margin δ > 0 on `[0,1]`; Lipschitz extended path.
- **Uses from project**: `ClosedPwC1Immersion`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path.extendedPath_eq`, `cpvIntegrandOn`, `intervalIntegrable_pow_inv_mul_deriv_of_avoids`, `cpvIntegrandOn_intervalIntegrable_of_contourIntegrand`.
- **Used by**: `hPV_sing_of_conditionB_avoids`.
- **Visibility**: public
- **Lines**: 193-223
- **Notes**: >30 lines.

### `theorem hPV_sing_of_conditionB_avoids`
- **Type**: `{U : Set ℂ} (_hU_open : IsOpen U) {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ} (γ : ClosedPwC1Immersion x) (_hSimple : ∀ s ∈ S, HasSimplePoleAt f s) (_hCondB : SatisfiesConditionB γ.toPwC1Immersion f S) (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc 0 1, γ_path t ≠ s) : HasCauchyPVOn S (principalPartSum S (residue f)) γ_path (∑ s, 2πI · generalizedWindingNumber γ_path s · residue f s)`
- **What**: Phase 5b — full discharge of all three residuals (`hw`, `h_avoid_pairs`, `h_int`) under the pure paper-faithful avoidance hypothesis `hγ_avoids`.
- **How**: Get Lipschitz K from `ClosedPwC1Immersion.lipschitzWith_extend`; get uniform avoidance margin δ from `avoids_finset_delta_bound`; for each pole s, derive `HasGeneralizedWindingNumber` via `hasGeneralizedWindingNumber_of_avoids` and reconcile its value with `generalizedWindingNumber γ s` via `.eq`. Restrict to pairwise avoidance trivially. Discharge integrability via `cpvIntegrandOn_div_sub_intervalIntegrable_of_avoids` (with the extended-path reformulation `PiecewiseC1Path.extendedPath_eq`). Conclude via `hPV_sing_of_winding_and_avoid_others`. Key lemma: `hasGeneralizedWindingNumber_of_avoids`.
- **Hypotheses**: γ avoids every pole in S.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.lipschitzWith_extend`, `SatisfiesConditionB`, `HasSimplePoleAt`, `HasGeneralizedWindingNumber`, `HasCauchyPVOn`, `principalPartSum`, `residue`, `generalizedWindingNumber`, `cpvIntegrandOn`, `avoids_finset_delta_bound`, `hasGeneralizedWindingNumber_of_avoids`, `cpvIntegrandOn_div_sub_intervalIntegrable_of_avoids`, `PiecewiseC1Path.extendedPath_eq`, `hPV_sing_of_winding_and_avoid_others`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 248-294
- **Notes**: >30 lines; `classical` enabled.

### `theorem hasGeneralizedWindingNumber_canonical_of_singleCrossingData`
- **Type**: `{γ : PiecewiseC1Path x x} {s : ℂ} (D : SingleCrossingData γ s) : HasGeneralizedWindingNumber γ s (generalizedWindingNumber γ s)`
- **What**: Bridge from `SingleCrossingData` to the canonical `HasGeneralizedWindingNumber γ s (generalizedWindingNumber γ s)` form expected by `hPV_sing_of_conditionB`.
- **How**: From `D.hasWindingNumber : HasGeneralizedWindingNumber γ s (D.L / (2πi))`, use `.eq` to rewrite the canonical winding number into `D.L/(2πi)`.
- **Hypotheses**: a `SingleCrossingData` witness.
- **Uses from project**: `SingleCrossingData`, `SingleCrossingData.hasWindingNumber`, `HasGeneralizedWindingNumber`, `generalizedWindingNumber`, `HasGeneralizedWindingNumber.eq`.
- **Used by**: `hPV_sing_of_conditionB_singleCrossing`.
- **Visibility**: public
- **Lines**: 322-329
- **Notes**: none

### `theorem hasGeneralizedWindingNumber_canonical_of_value`
- **Type**: `{γ : PiecewiseC1Path x x} {s w : ℂ} (hw : HasGeneralizedWindingNumber γ s w) : HasGeneralizedWindingNumber γ s (generalizedWindingNumber γ s)`
- **What**: Bridge from an arbitrary `HasGeneralizedWindingNumber γ s w` witness to its canonical form (with value `generalizedWindingNumber γ s`).
- **How**: Rewrite via `hw.eq` and use `hw`.
- **Hypotheses**: a generalized-winding-number witness at value w.
- **Uses from project**: `HasGeneralizedWindingNumber`, `generalizedWindingNumber`, `HasGeneralizedWindingNumber.eq`.
- **Used by**: `hPV_sing_of_conditionB_pointwise_winding`.
- **Visibility**: public
- **Lines**: 335-339
- **Notes**: none

### `theorem hPV_sing_of_conditionB_singleCrossing`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) {S : Finset ℂ} (hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ} (γ : ClosedPwC1Immersion x) (hSimple) (hCondB) (Dat : ∀ s ∈ S, SingleCrossingData γ_path s) {δ : ℝ} (hδ_pos : 0 < δ) (h_avoid_pairs) (h_int) : HasCauchyPVOn S (principalPartSum S (residue f)) γ_path (∑ s, 2πI · generalizedWindingNumber γ_path s · residue f s)`
- **What**: Phase 6.1 — discharge `hPV_sing` from per-pole `SingleCrossingData` witnesses, modeling unique transverse crossings.
- **How**: For each pole derive the canonical winding form via `hasGeneralizedWindingNumber_canonical_of_singleCrossingData`, then plug into `hPV_sing_of_conditionB`.
- **Hypotheses**: `SingleCrossingData` per pole; pairwise avoidance; per-pole integrability.
- **Uses from project**: `ClosedPwC1Immersion`, `SatisfiesConditionB`, `HasSimplePoleAt`, `SingleCrossingData`, `HasGeneralizedWindingNumber`, `HasCauchyPVOn`, `principalPartSum`, `residue`, `generalizedWindingNumber`, `cpvIntegrandOn`, `hasGeneralizedWindingNumber_canonical_of_singleCrossingData`, `hPV_sing_of_conditionB`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 356-381
- **Notes**: none

### `theorem hPV_sing_of_conditionB_pointwise_winding`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) {S : Finset ℂ} (hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ} (γ : ClosedPwC1Immersion x) (hSimple) (hCondB) (hw_val : ∀ s ∈ S, ∃ w : ℂ, HasGeneralizedWindingNumber γ_path s w) {δ : ℝ} (hδ_pos : 0 < δ) (h_avoid_pairs) (h_int) : HasCauchyPVOn S (principalPartSum S (residue f)) γ_path (∑ s, 2πI · generalizedWindingNumber γ_path s · residue f s)`
- **What**: Variant accepting arbitrary `HasGeneralizedWindingNumber` witnesses (any value, not just `(SingleCrossingData.L) / (2πi)`). The conclusion uses the canonical `generalizedWindingNumber γ s` automatically.
- **How**: Extract per-pole witnesses via `obtain ⟨w, hwval⟩`, bridge each to canonical form via `hasGeneralizedWindingNumber_canonical_of_value`, then plug into `hPV_sing_of_conditionB`.
- **Hypotheses**: existence of a generalized-winding-number witness at each pole (no fixed value); pairwise avoidance; per-pole integrability.
- **Uses from project**: `ClosedPwC1Immersion`, `SatisfiesConditionB`, `HasSimplePoleAt`, `HasGeneralizedWindingNumber`, `HasCauchyPVOn`, `principalPartSum`, `residue`, `generalizedWindingNumber`, `cpvIntegrandOn`, `hasGeneralizedWindingNumber_canonical_of_value`, `hPV_sing_of_conditionB`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 389-417
- **Notes**: `classical` enabled.

## File Summary

`HW33PVSing.lean` discharges the `hPV_sing` (singular CPV) oracle in `hw_3_3_paper` / `hw_3_3_tight`. The file is a sequence of progressively higher-level discharge theorems.

Layout (in dependency order):
1. Singleton-to-multi-pole lift: `hasCauchyPVOn_div_sub_of_singleton_and_avoid_others`.
2. Multi-pole assembly: `hPV_sing_from_per_pole_cpv` (sum over poles) and `hPV_sing_of_winding_and_avoid_others` (closed form combining the previous two).
3. Master-template form: `hPV_sing_of_conditionB` (matches the hypothesis name in `hw_3_3_paper`, with `c = residue f`).
4. Phase 5b — pure avoidance: `cpvIntegrandOn_div_sub_intervalIntegrable_of_avoids` (integrability) and `hPV_sing_of_conditionB_avoids` (full discharge under γ avoiding every pole).
5. Phase 6.1 — single-crossing: `hasGeneralizedWindingNumber_canonical_of_singleCrossingData`, `hasGeneralizedWindingNumber_canonical_of_value`, `hPV_sing_of_conditionB_singleCrossing`, `hPV_sing_of_conditionB_pointwise_winding`.

Total: 10 public theorems, all in `namespace LeanModularForms`. No sorries, no axioms. Two theorems use `classical`. The longest individual proof is `hPV_sing_of_conditionB_avoids` at ~47 lines, which combines Lipschitz, finite-set avoidance, generalized winding number existence, and CPV-integrand integrability into the paper-faithful conclusion.
