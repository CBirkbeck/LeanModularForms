# MultiPoleDCT.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HungerbuhlerWasem/MultiPoleDCT.lean` (529 lines)

Namespace: `HungerbuhlerWasem.MultiPoleDCT`

### `def badSetIcc`
- **Type**: `(γP : PiecewiseC1Path x x) (T : Finset ℂ) (ε : ℝ) → Set ℝ`
- **What**: The "bad set" of parameters `t ∈ [0,1]` where `γ(t)` is within `ε` of some pole candidate `s' ∈ T`. As `ε → 0+`, these shrink to `γ⁻¹(T) ∩ [0,1]`.
- **How**: Direct set-builder `{t ∈ Icc 0 1 | ∃ s' ∈ T, ‖γP.toPath.extend t - s'‖ ≤ ε}`.
- **Hypotheses**: None.
- **Uses from project**: `PiecewiseC1Path`
- **Used by**: `badSetIcc_measurableSet`, `badSetIcc_mono`, `badSetIcc_subset_Icc`, `badSetIcc_volume_ne_top`, `badSetIcc_iInter_pos`, `badSet_volume_tendsto_zero`, `cpvIntegrand_polarPart_intervalIntegrable`, `hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole`
- **Visibility**: public
- **Lines**: 60-61
- **Notes**: None.

### `theorem badSetIcc_measurableSet`
- **Type**: `(γP : PiecewiseC1Path x x) (T : Finset ℂ) (ε : ℝ) → MeasurableSet (badSetIcc γP T ε)`
- **What**: Measurability of `badSetIcc`.
- **How**: Rewrite as `Icc ∩ ⋃ s' ∈ T, {t : ‖γP.extend t - s'‖ ≤ ε}`; the inner sets are closed (preimage of `≤ ε` under continuous norm), apply `MeasurableSet.biUnion T.countable_toSet`.
- **Hypotheses**: None.
- **Uses from project**: `badSetIcc`, `PiecewiseC1Path`
- **Used by**: `badSet_volume_tendsto_zero`, `hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole`
- **Visibility**: public
- **Lines**: 63-76
- **Notes**: >10 lines (14 lines).

### `theorem badSetIcc_mono`
- **Type**: `(γP : PiecewiseC1Path x x) (T : Finset ℂ) → Monotone (badSetIcc γP T)`
- **What**: `badSetIcc` is monotone in `ε`.
- **How**: From `ε₁ ≤ ε₂` and `h_le ≤ ε₁`, get `h_le ≤ ε₂` by `h_le.trans hε`.
- **Hypotheses**: None.
- **Uses from project**: `badSetIcc`, `PiecewiseC1Path`
- **Used by**: `badSet_volume_tendsto_zero`
- **Visibility**: public
- **Lines**: 78-82
- **Notes**: None.

### `theorem badSetIcc_subset_Icc`
- **Type**: `(γP : PiecewiseC1Path x x) (T : Finset ℂ) (ε : ℝ) → badSetIcc γP T ε ⊆ Icc 0 1`
- **What**: `badSetIcc` is contained in `[0, 1]`.
- **How**: First projection of the set-builder definition.
- **Hypotheses**: None.
- **Uses from project**: `badSetIcc`, `PiecewiseC1Path`
- **Used by**: `badSetIcc_volume_ne_top`
- **Visibility**: public
- **Lines**: 84-85
- **Notes**: None.

### `theorem badSetIcc_volume_ne_top`
- **Type**: `(γP : PiecewiseC1Path x x) (T : Finset ℂ) (ε : ℝ) → volume (badSetIcc γP T ε) ≠ ⊤`
- **What**: `badSetIcc` has finite (`<∞`) volume.
- **How**: `measure_mono badSetIcc_subset_Icc` then `measure_Icc_lt_top`.
- **Hypotheses**: None.
- **Uses from project**: `badSetIcc`, `badSetIcc_subset_Icc`, `PiecewiseC1Path`
- **Used by**: `badSet_volume_tendsto_zero`, `hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole`
- **Visibility**: public
- **Lines**: 87-89
- **Notes**: None.

### `theorem badSetIcc_iInter_pos`
- **Type**: `(γP : PiecewiseC1Path x x) (T : Finset ℂ) → (⋂ ε ∈ Ioi 0, badSetIcc γP T ε) = {t ∈ Icc 0 1 | γP.toPath.extend t ∈ (↑T : Set ℂ)}`
- **What**: Intersection over `ε > 0` of bad sets equals preimage of `T` in `[0,1]`.
- **How**: Forward: pick smallest distance `ε₀ := ‖γ(t) - s_min‖/2`; if no point equals any `s' ∈ T`, the min over `T` of `‖γ(t) - s'‖` is positive, contradicting `ε₀`-closeness. Reverse: if `γ(t) = s' ∈ T`, then for any `ε > 0`, `s'` itself witnesses bad-set membership.
- **Hypotheses**: None.
- **Uses from project**: `badSetIcc`, `PiecewiseC1Path`
- **Used by**: `badSet_volume_tendsto_zero`
- **Visibility**: public
- **Lines**: 92-131
- **Notes**: >10 lines (40 lines).

### `theorem badSet_volume_tendsto_zero`
- **Type**: `(γ : ClosedPwC1Immersion x) (T : Finset ℂ) → Tendsto (fun ε : ℝ => volume (badSetIcc γ.toPwC1Immersion.toPiecewiseC1Path T ε)) (𝓝[>] 0) (𝓝 0)`
- **What**: The volume of the bad set tends to zero as `ε → 0+` for a closed piecewise-`C¹` immersion.
- **How**: Apply `MeasureTheory.tendsto_measure_biInter_gt` with monotonicity and finiteness; identify `iInter` with preimage of `T` in `[0,1]` via `badSetIcc_iInter_pos`; close with `volume_preimage_finset_in_Icc01_zero γ T` (immersion → finite preimage measure zero).
- **Hypotheses**: `γ` is `ClosedPwC1Immersion`.
- **Uses from project**: `badSetIcc`, `badSetIcc_measurableSet`, `badSetIcc_mono`, `badSetIcc_volume_ne_top`, `badSetIcc_iInter_pos`, `ClosedPwC1Immersion`, `volume_preimage_finset_in_Icc01_zero`
- **Used by**: `hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole`
- **Visibility**: public
- **Lines**: 135-160
- **Notes**: >10 lines (26 lines).

### `theorem cpvIntegrand_polarPart_intervalIntegrable`
- **Type**: `(γ : ClosedPwC1Immersion x) {U : Set ℂ} {S : Finset ℂ} {f : ℂ → ℂ} (decomp : PolarPartDecomposition f S U) {s : ℂ} (hs : s ∈ S) {ε : ℝ} (hε : 0 < ε) → IntervalIntegrable (fun t => cpvIntegrand (decomp.polarPart s) γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε t) volume 0 1`
- **What**: The singleton-CPV cutoff integrand for the polar part `decomp.polarPart s` is interval-integrable on `[0,1]` for every `ε > 0`.
- **How**: Extract Lipschitz constant `K` from `ClosedPwC1Immersion.lipschitzWith_extend`. Rewrite `cpvIntegrand` as indicator of `{t : ε < ‖γ(t) - s‖}` of the Laurent form `(∑ a_k/(γ(t) - s)^(k+1)) · γ'(t)` using `decomp.polarPart_eq`. Pointwise bound: on the indicator set, `‖∑ a_k/(γ-s)^(k+1)‖ ≤ M_polar = ∑ ‖a_k‖/ε^(k+1)` (since `ε < ‖γ - s‖`), and `‖γ'‖ ≤ K`, so the product is `≤ M_polar · K`. Apply `IntegrableOn.of_bound` with `M = M_polar · K` and measurability via `Measurable.indicator`.
- **Hypotheses**: Closed PWC1 immersion, polar-part decomposition with `s ∈ S`, `ε > 0`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.lipschitzWith_extend`, `PiecewiseC1Path`, `PolarPartDecomposition`, `PolarPartDecomposition.polarPart`, `PolarPartDecomposition.polarPart_eq`, `PolarPartDecomposition.order`, `PolarPartDecomposition.coeff`, `cpvIntegrand`, `norm_deriv_le_of_lipschitz`
- **Used by**: `hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole`
- **Visibility**: public
- **Lines**: 167-252
- **Notes**: >10 lines (86 lines).

### `theorem hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole`
- **Type**: `{S : Finset ℂ} {f : ℂ → ℂ} (hS_in_U : ↑S ⊆ U) (decomp : PolarPartDecomposition f S U) (γ : ClosedPwC1Immersion x) {s : ℂ} (hs : s ∈ S) {L : ℂ} → IsNullHomologous γ.toPwC1Immersion U → HasCauchyPV (decomp.polarPart s) γ.toPwC1Immersion.toPiecewiseC1Path s L → HasCauchyPVOn S (decomp.polarPart s) γ.toPwC1Immersion.toPiecewiseC1Path L`
- **What**: **T-BR-Y5 headline**: A singleton CPV at one pole `s ∈ S` lifts to the multi-pole form on `S` without requiring `γ` to avoid the other poles in `S \ {s}`.
- **How**: Case split on `T := S.erase s`. (1) If `T = ∅` then `S = {s}` and `cpvIntegrand = cpvIntegrandOn` pointwise — use `congr` on integral. (2) Otherwise, choose minimum distance `R := ‖s - s'_min‖/4`. The pointwise difference `cpvIntegrand - cpvIntegrandOn` is supported on the bad-set `D(ε) ⊆ badSetIcc γP T ε`. On that bad set, when `ε < R`, every nearby other pole forces `‖γ(t) - s‖ ≥ 3R`, so `‖polarPart s (γ(t))‖ ≤ M_polar = ∑ ‖a_k‖/(3R)^(k+1)`; combined with `‖γ'‖ ≤ K`, the difference is uniformly bounded by `M = M_polar · K`. Use `intervalIntegral.norm_integral_le_of_norm_le` with the badSet indicator bound, get `‖∫(cpv - cpvOn)‖ ≤ M · vol(badSetIcc T ε)`. Apply `badSet_volume_tendsto_zero` and `squeeze_zero_norm'` to conclude `∫(cpv - cpvOn) → 0` along `𝓝[>] 0`; combine with `h` (CPV at `s`) via `.sub`.
- **Hypotheses**: `S ⊆ U`, polar-part decomposition, closed PWC1 immersion `γ` (with null-homologous data for the auxiliary `cpvIntegrandOn` integrability), `s ∈ S`, singleton CPV at `s`.
- **Uses from project**: `PolarPartDecomposition`, `PolarPartDecomposition.polarPart`, `PolarPartDecomposition.polarPart_eq`, `PolarPartDecomposition.order`, `PolarPartDecomposition.coeff`, `ClosedPwC1Immersion`, `ClosedPwC1Immersion.lipschitzWith_extend`, `PiecewiseC1Path`, `IsNullHomologous`, `HasCauchyPV`, `HasCauchyPVOn`, `cpvIntegrand`, `cpvIntegrandOn`, `cpvIntegrandOn_polarPart_intervalIntegrable`, `cpvIntegrand_polarPart_intervalIntegrable`, `badSetIcc`, `badSetIcc_measurableSet`, `badSetIcc_volume_ne_top`, `badSet_volume_tendsto_zero`, `norm_deriv_le_of_lipschitz`
- **Used by**: External (HungerbuhlerWasem PR chain).
- **Visibility**: public
- **Lines**: 265-523
- **Notes**: >10 lines (259 lines). Main result of the file.

## File Summary

This file proves **T-BR-Y5**, a multi-pole DCT lift for the polar-part Cauchy principal value: given a polar-part decomposition `f = ∑_s polarPart s + analytic` on `U ⊇ S`, a closed piecewise-`C¹` immersion `γ`, and a singleton CPV `HasCauchyPV (polarPart s) γ s L` at one pole `s ∈ S`, the multi-pole CPV `HasCauchyPVOn S (polarPart s) γ L` follows **without** requiring `γ` to avoid `S \ {s}`. The key argument: the difference between singleton-cutoff and multipole-cutoff integrands is supported on the "bad set" `badSetIcc γ T ε` (parameters where `γ(t)` is `ε`-close to some other pole `s' ∈ T = S \ {s}`). For small `ε < R = min_{s' ∈ T} ‖s - s'‖/4`, the polar-part `‖polarPart s ∘ γ‖` is bounded by `M_polar` on this bad set (triangle inequality forces `‖γ - s‖ ≥ 3R`), giving uniform bound `M = M_polar · K` with `K` the Lipschitz constant of `γ'`. Since `vol(badSetIcc T ε) → 0` as `ε → 0+` (immersion ⇒ finite preimage has measure zero), DCT squeeze yields the limit. Total: 1 definition + 7 theorems. Headline theorem is 259 lines. No `sorry`, no axioms, no `set_option maxHeartbeats`.
