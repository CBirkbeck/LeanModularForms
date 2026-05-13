# Inventory: `LeanModularForms/ForMathlib/HungerbuhlerWasem/Crossing.lean`

### `theorem HasCauchyPV.add`
- **Type**: `{f g : ℂ → ℂ} {γ : PiecewiseC1Path x y} {z₀ L₁ L₂ : ℂ} (hf : HasCauchyPV f γ z₀ L₁) (hg : HasCauchyPV g γ z₀ L₂) (hfi : ∀ ε > 0, IntervalIntegrable …) (hgi : ∀ ε > 0, IntervalIntegrable …) : HasCauchyPV (fun z => f z + g z) γ z₀ (L₁ + L₂)`
- **What**: Additivity of `HasCauchyPV`: if both `f` and `g` have CPVs along `γ` at `z₀`, their pointwise sum has CPV equal to the sum of the two limit values.
- **How**: Rewrites the cutoff integrand of the sum as a pointwise sum of the two cutoff integrands, applies `intervalIntegral.integral_add` to split the integral, then composes `Tendsto.add` via the `HasCauchyPV` unfolding and `.congr'`.
- **Hypotheses**: Existing CPVs at the same `z₀` with cutoff integrability for each `ε > 0`.
- **Uses from project**: `HasCauchyPV`, `cpvIntegrand`.
- **Used by**: `HasCauchyPV.finset_sum`.
- **Visibility**: public
- **Lines**: 62-83
- **Notes**: none

### `theorem HasCauchyPV.zero_fun`
- **Type**: `{γ : PiecewiseC1Path x y} {z₀ : ℂ} : HasCauchyPV (fun _ => (0 : ℂ)) γ z₀ 0`
- **What**: The Cauchy principal value of the zero function along any piecewise-C¹ path equals zero.
- **How**: Shows the cutoff integrand collapses to the zero function via `split_ifs` on the cutoff, then uses `intervalIntegral.integral_zero` and `tendsto_const_nhds`.
- **Hypotheses**: None beyond the ambient path.
- **Uses from project**: `HasCauchyPV`, `cpvIntegrand`.
- **Used by**: `HasCauchyPV.finset_sum` (induction base).
- **Visibility**: public
- **Lines**: 86-97
- **Notes**: none

### `theorem HasCauchyPV.congr_pointwise`
- **Type**: `{f g : ℂ → ℂ} {γ : PiecewiseC1Path x y} {z₀ L : ℂ} (h : HasCauchyPV f γ z₀ L) (hfg : ∀ z, z ≠ z₀ → f z = g z) : HasCauchyPV g γ z₀ L`
- **What**: Congruence-rewrite for `HasCauchyPV` via pointwise equality away from the singularity: `f = g` off `z₀` implies the two share the same CPV.
- **How**: Filter-upwards on a small neighborhood `ε > 0`, then `intervalIntegral.integral_congr`: in the cutoff regime where `‖γ t - z₀‖ > ε`, `γ t ≠ z₀`, so `hfg` applies.
- **Hypotheses**: Pointwise equality of `f` and `g` away from `z₀`.
- **Uses from project**: `HasCauchyPV`, `cpvIntegrand`.
- **Used by**: `cpv_polarPart_at_pole_under_conditions`, `cpv_polarPart_at_pole_under_conditions_asymmetric`.
- **Visibility**: public
- **Lines**: 102-116
- **Notes**: none

### `theorem HasCauchyPV.finset_sum`
- **Type**: `{ι : Type*} [DecidableEq ι] (T : Finset ι) {γ : PiecewiseC1Path x y} {z₀ : ℂ} {f : ι → ℂ → ℂ} {L : ι → ℂ} (hf …) (hfi …) : HasCauchyPV (fun z => ∑ i ∈ T, f i z) γ z₀ (∑ i ∈ T, L i)`
- **What**: Finite-sum form of `HasCauchyPV`: if each `f i` has CPV `L i`, the pointwise sum has CPV equal to the sum of `L i`.
- **How**: `Finset.induction_on` with empty base case `HasCauchyPV.zero_fun`; inductive step uses `HasCauchyPV.add` along with `IntervalIntegrable.sum` to combine the cutoff integrability of finite sums.
- **Hypotheses**: Per-element CPV witnesses and per-element cutoff integrability on `T`.
- **Uses from project**: `HasCauchyPV.zero_fun`, `HasCauchyPV.add`, `cpvIntegrand`.
- **Used by**: `cpv_polarPart_at_pole_under_conditions`, `cpv_polarPart_at_pole_under_conditions_asymmetric`.
- **Visibility**: public
- **Lines**: 120-164
- **Notes**: proof >30 lines (~45)

### `theorem cpv_polarPart_at_pole_under_conditions`
- **Type**: `{γ : PiecewiseC1Path x y} {s : ℂ} (D : SingleCrossingData γ s) {f : ℂ → ℂ} {U : Set ℂ} {S : Finset ℂ} (hs : s ∈ S) (decomp : PolarPartDecomposition f S U) (h_higher) (h_term_int) : HasCauchyPV (decomp.polarPart s) γ s (2 * π * I * w · residue f s)`
- **What**: Per-pole CPV at a transverse crossing (T-GL-01 headline): for a single crossing `s`, the polar part `decomp.polarPart s` has CPV `2πi · w · residue f s`.
- **How**: Sets up `term k z = a k / (z - s)^(k+1)`, separately handles `k = 0` (simple pole — uses `cpv_simplePole_at_crossing`) and `k ≥ 1` (higher order — uses `h_higher`); uses `HasCauchyPV.finset_sum` to aggregate; finishes with `HasCauchyPV.congr_pointwise` to swap the truncated polynomial for `decomp.polarPart s`.
- **Hypotheses**: `SingleCrossingData γ s`, polar decomposition, per-term higher-order CPV vanishing (condition B), per-term cutoff integrability.
- **Uses from project**: `SingleCrossingData`, `PolarPartDecomposition`, `cpv_simplePole_at_crossing`, `HasCauchyPV.finset_sum`, `HasCauchyPV.congr_pointwise`, `decomp.polarPart_eq`, `decomp.residue_eq`.
- **Used by**: `cpv_polarPart_at_crossed_pole_hasCauchyPV`.
- **Visibility**: public
- **Lines**: 173-229
- **Notes**: proof >30 lines (~55)

### `theorem cpv_polarPart_at_pole_under_conditions_asymmetric`
- **Type**: same as the symmetric variant but with `AsymmetricSingleCrossingData γ s`.
- **What**: Asymmetric variant of T-GL-01 — admits curves with `‖L_-‖ ≠ ‖L_+‖`.
- **How**: Identical structure to symmetric form but invokes `cpv_simplePole_at_crossing_asymmetric` for the simple-pole step.
- **Hypotheses**: As above with `AsymmetricSingleCrossingData`.
- **Uses from project**: `AsymmetricSingleCrossingData`, `cpv_simplePole_at_crossing_asymmetric`, `HasCauchyPV.finset_sum`, `HasCauchyPV.congr_pointwise`, `PolarPartDecomposition`.
- **Used by**: `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric`, `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric_corner`.
- **Visibility**: public
- **Lines**: 238-294
- **Notes**: proof >30 lines (~55)

### `theorem cpvIntegrandOn_eq_of_decomp`
- **Type**: `{U} {S} {f} (decomp) {γ} {t} (ht : γ t ∈ U) {ε} (hε_pos : 0 < ε) : cpvIntegrandOn S f γ ε t = cpvIntegrandOn S (analyticRemainder + ∑ polarPart) γ ε t`
- **What**: Pointwise equality of the multi-point cutoff integrand with the cutoff integrand of the polar-part decomposition.
- **How**: `by_cases` on whether `γ t` is in some cutoff ball: in the ball both sides are zero; outside, `γ t ∈ U \ S` so `decomp.decomp` applies.
- **Hypotheses**: Point of γ in U, ε > 0.
- **Uses from project**: `PolarPartDecomposition`, `cpvIntegrandOn`, `cpvIntegrandOn_of_exists_le`, `cpvIntegrandOn_of_forall_gt`, `decomp.decomp`.
- **Used by**: `residueTheorem_crossing_compositional`.
- **Visibility**: private
- **Lines**: 312-336
- **Notes**: none

### `theorem residueTheorem_crossing_compositional`
- **Type**: `(hU_open) (hU_ne) (S) (hS_in_U) (f) (hf : DifferentiableOn ℂ f (U \ S)) (γ : ClosedPwC1Immersion x) (h_null) (decomp) (h_polar_cpv : ∀ s ∈ S, HasCauchyPVOn S (decomp.polarPart s) γ value) : HasCauchyPVOn S f γ (∑ s ∈ S, 2πi w · res f s)`
- **What**: Hungerbühler–Wasem Theorem 3.3 (compositional crossing form): consumes a polar-part decomposition + per-pole CPV witnesses, returns the multi-point CPV of `∮f`.
- **How**: Builds analytic remainder CPV via `analyticRemainder_hasCauchyPVOn_zero`, applies `HasCauchyPVOn.finset_sum` and `HasCauchyPVOn.add` to combine analytic-remainder + polar parts, then `intervalIntegral.integral_congr` with `cpvIntegrandOn_eq_of_decomp` to swap back to `f`.
- **Hypotheses**: open `U`, finite pole set `S ⊆ U`, `f` differentiable off `S`, γ closed null-homologous immersion, per-pole CPV witnesses.
- **Uses from project**: `HungerbuhlerWasem.analyticRemainder_hasCauchyPVOn_zero`, `cpvIntegrandOn_diff_intervalIntegrable`, `cpvIntegrandOn_polarPart_intervalIntegrable`, `HasCauchyPVOn.finset_sum`, `HasCauchyPVOn.add`, `cpvIntegrandOn_eq_of_decomp`.
- **Used by**: `residueTheorem_crossing`, `residueTheorem_crossing_asymmetric`, `residueTheorem_crossing_asymmetric_scenario`, `residueTheorem_crossing_asymmetric_multiCrossing`, `residueTheorem_crossing_asymmetric_multiPole`, `residueTheorem_crossing_truly_full_spec`.
- **Visibility**: public
- **Lines**: 357-432
- **Notes**: proof >30 lines (~75)

### `theorem volume_ball_preimage_tendsto_zero`
- **Type**: `(γ : ClosedPwC1Immersion x) (z : ℂ) : Tendsto (fun ε => volume {t ∈ Icc 0 1 | ‖γ t - z‖ ≤ ε}) (𝓝[>] 0) (𝓝 0)`
- **What**: Lebesgue measure of `{t : ‖γ(t) - z‖ ≤ ε}` on `Icc 0 1` tends to 0 as ε → 0.
- **How**: Uses `tendsto_measure_biInter_gt` on the monotone family `S(ε) = {t : ‖γ t - z‖ ≤ ε}`; the intersection over ε > 0 is `γ⁻¹{z} ∩ Icc 0 1`, which has measure zero by `volume_preimage_finset_in_Icc01_zero` (the immersion property).
- **Hypotheses**: closed piecewise-C¹ immersion γ.
- **Uses from project**: `HungerbuhlerWasem.volume_preimage_finset_in_Icc01_zero`, `ClosedPwC1Immersion`.
- **Used by**: unused in file (kept for downstream use)
- **Visibility**: private
- **Lines**: 466-527
- **Notes**: proof >30 lines (~60), private

### `theorem cpv_polarPart_at_uncrossed_pole`
- **Type**: `(_hU_open) (_hU_ne) {S} (hS_in_U) {f} (γ) (h_null) (decomp) (s) (hs : s ∈ S) (h_avoid : ∀ t, γ t ≠ s) : HasCauchyPVOn S (decomp.polarPart s) γ (2πi w · res f s)`
- **What**: Per-pole CPV at an uncrossed pole: when γ avoids `s`, the multi-point CPV of `decomp.polarPart s` equals `2πi · w · residue f s`.
- **How**: (Step A) avoidance distance δ via `avoids_delta_bound`; (Step B) cutoff integrand interval-integrability via `IntervalIntegrable.continuousOn_mul`; (Step C) computes the contour integral by decomposing into Laurent terms and using `hasCauchyPV_of_avoids` for the simple pole, with `contourIntegral_higherOrder_eq_zero_of_avoids` killing the higher order; (Step D) DCT via `intervalIntegral.tendsto_integral_filter_of_dominated_convergence` and `cpvIntegrandOn_tendsto_contourIntegrand_ae`.
- **Hypotheses**: γ avoids `s`, polar decomposition.
- **Uses from project**: `ClosedPwC1Immersion.lipschitzWith_extend`, `avoids_delta_bound`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path.contourIntegral`, `PiecewiseC1Path.contourIntegral_finset_sum`, `PiecewiseC1Path.contourIntegral_smul`, `contourIntegral_higherOrder_eq_zero_of_avoids`, `hasCauchyPV_of_avoids`, `HungerbuhlerWasem.cpvIntegrandOn_polarPart_intervalIntegrable`, `HungerbuhlerWasem.cpvIntegrandOn_eq_indicator_compl`, `HungerbuhlerWasem.cpv_badSet`, `HungerbuhlerWasem.cpvIntegrandOn_tendsto_contourIntegrand_ae`, `decomp.polarPart_eq`, `decomp.residue_eq`, `norm_deriv_le_of_lipschitz`, `generalizedWindingNumber`.
- **Used by**: `cpv_polarPart_at_pole_from_conditions`, `cpv_polarPart_at_pole_from_conditions_asymmetric`, `residueTheorem_crossing_asymmetric_scenario`, `residueTheorem_crossing_asymmetric_multiCrossing`, `residueTheorem_crossing_asymmetric_multiPole`, `residueTheorem_crossing_truly_full_spec`.
- **Visibility**: public
- **Lines**: 536-730
- **Notes**: proof >30 lines (~195) — the largest single proof in the file.

### `theorem cpv_polarPart_at_crossed_pole_hasCauchyPV`
- **Type**: `{U S} (_hS_in_U) {f} (γ) (_h_null) (decomp) (s) (hs : s ∈ S) {t₀} (ht₀) (h_at) (h_unique) (h_t₀_off_partition) (D : SingleCrossingData γP s) (n) (h_flat) (hn1) (h_order_le_n) (h_angle) : HasCauchyPV (decomp.polarPart s) γP s (2πi w · res f s)`
- **What**: Single-point CPV at a crossed pole using condition (B) (symmetric data): composes T-CC-01, T-BR-03, T-GL-01 into the per-pole CPV at the crossing.
- **How**: Assembles per-term integrability via `cpvIntegrandOn_singleMonomial_intervalIntegrable`; for each `k`, uses `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB` (T-BR-03) when coefficient nonzero, else `HasCauchyPVOn.zero_fun`; aggregates via `cpv_polarPart_at_pole_under_conditions` (T-GL-01).
- **Hypotheses**: `SingleCrossingData`, condition (A') flatness data `n`, `h_flat`, condition (B) angle equation `h_angle`.
- **Uses from project**: `HungerbuhlerWasem.cpvIntegrandOn_singleMonomial_intervalIntegrable`, `cpvIntegrand_eq_cpvIntegrandOn_singleton`, `HungerbuhlerWasem.hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB`, `HasCauchyPVOn.zero_fun`, `hasCauchyPV_of_hasCauchyPVOn_singleton`, `cpv_polarPart_at_pole_under_conditions`.
- **Used by**: `cpv_polarPart_at_pole_from_conditions`.
- **Visibility**: public
- **Lines**: 741-814
- **Notes**: proof >30 lines (~70)

### `theorem cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric`
- **Type**: as the symmetric variant but with `AsymmetricSingleCrossingData`.
- **What**: Asymmetric variant of the crossed-pole single-point CPV.
- **How**: Identical to symmetric form, but uses `cpv_polarPart_at_pole_under_conditions_asymmetric` for the final aggregation.
- **Hypotheses**: same as symmetric with `AsymmetricSingleCrossingData`.
- **Uses from project**: same as symmetric crossed-pole, but routes through `cpv_polarPart_at_pole_under_conditions_asymmetric`.
- **Used by**: `cpv_polarPart_at_pole_from_conditions_asymmetric`, `residueTheorem_crossing_asymmetric_scenario`, `residueTheorem_crossing_asymmetric_multiCrossing`, `residueTheorem_crossing_asymmetric_multiPole`, `residueTheorem_crossing_truly_full_spec` (smooth branch).
- **Visibility**: public
- **Lines**: 824-891
- **Notes**: proof >30 lines (~70)

### `theorem cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric_corner`
- **Type**: same shape as the smooth asymmetric version, but accepts one-sided derivative limits `L_minus, L_plus` and a per-coefficient `h_B` instead of `h_t₀_off_partition` and `h_angle`.
- **What**: Corner-friendly variant (T-BR-Y10b): drops the off-partition requirement, accepts asymmetric one-sided limits and the unit-circle power equation for the condition (B) angle.
- **How**: Same per-term integrability assembly; routes higher-order CPV vanishing through `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner` instead of the smooth version.
- **Hypotheses**: One-sided derivative limits `L_minus`, `L_plus` (both nonzero), the corner condition (B) `h_B` (unit-circle power equation), flatness.
- **Uses from project**: `HungerbuhlerWasem.cpvIntegrandOn_singleMonomial_intervalIntegrable`, `cpvIntegrand_eq_cpvIntegrandOn_singleton`, `HungerbuhlerWasem.hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner`, `HasCauchyPVOn.zero_fun`, `hasCauchyPV_of_hasCauchyPVOn_singleton`, `cpv_polarPart_at_pole_under_conditions_asymmetric`.
- **Used by**: `residueTheorem_crossing_truly_full_spec` (corner branch).
- **Visibility**: public
- **Lines**: 903-975
- **Notes**: proof >30 lines (~70)

### `theorem hasCauchyPVOn_of_hasCauchyPV_of_avoid_other_poles`
- **Type**: `{f γ s S} (hs : s ∈ S) {L} (h : HasCauchyPV f γ s L) (h_avoid_others) : HasCauchyPVOn S f γ L`
- **What**: Lifts a singleton CPV to multi-point `HasCauchyPVOn S` CPV when γ avoids every other pole in `S`.
- **How**: Builds an avoidance distance δ from `avoids_finset_delta_bound`; for ε < δ the multi-point cutoff integrand coincides with the singleton cutoff via `cpvIntegrandOn_of_exists_le`/`cpvIntegrand_of_le`; congruence-rewrite via `.congr'`.
- **Hypotheses**: γ avoids `S \ {s}`.
- **Uses from project**: `HasCauchyPVOn`, `HasCauchyPV`, `avoids_finset_delta_bound`, `cpvIntegrandOn_of_exists_le`, `cpvIntegrandOn_of_forall_gt`, `cpvIntegrand_of_le`, `cpvIntegrand_of_gt`.
- **Used by**: `cpv_polarPart_at_pole_from_conditions`, `cpv_polarPart_at_pole_from_conditions_asymmetric`, `residueTheorem_crossing_asymmetric_scenario` (crossed branch).
- **Visibility**: public
- **Lines**: 984-1027
- **Notes**: proof >30 lines (~45)

### `theorem flat_data_of_condA_at_crossing`
- **Type**: `{U S f γ} (decomp) (hCondA : SatisfiesConditionA' γ f S (decomp.order)) {s} (hs : s ∈ S) {t₀} (ht₀ : t₀ ∈ Ioo 0 1) (h_at) : ∃ n, 1 ≤ n ∧ decomp.order s ≤ n ∧ IsFlatOfOrder γ.extend t₀ n`
- **What**: Extracts flatness data `(n, n ≥ 1, decomp.order s ≤ n, IsFlatOfOrder γ t₀ n)` from condition (A') at a crossing parameter, handling the `decomp.order s = 0` case via fallback to order 1.
- **How**: Case-split on `1 ≤ decomp.order s`: if true, use condition (A') directly; else use `isFlatOfOrder_one` for the automatic order-1 flatness available on every piecewise-C¹ immersion.
- **Hypotheses**: Condition (A'), interior crossing parameter.
- **Uses from project**: `PolarPartDecomposition`, `SatisfiesConditionA'`, `IsFlatOfOrder`, `isFlatOfOrder_one`.
- **Used by**: `cpv_polarPart_at_pole_from_conditions`, `cpv_polarPart_at_pole_from_conditions_asymmetric`, `residueTheorem_crossing_asymmetric_full`, `residueTheorem_crossing_asymmetric_scenario`, `residueTheorem_crossing_asymmetric_multiCrossing`, `residueTheorem_crossing_asymmetric_multiPole`, `residueTheorem_crossing_truly_full_spec`.
- **Visibility**: private
- **Lines**: 1037-1057
- **Notes**: private; widely used internally

### `theorem laurent_polynomial_zero_of_eventuallyEq_analytic`
- **Type**: `∀ (N : ℕ) (c : Fin N → ℂ) {s : ℂ} {g : ℂ → ℂ}, AnalyticAt ℂ g s → (fun z => ∑ k, c k / (z - s)^(k+1)) =ᶠ[𝓝[≠] s] g → ∀ k : Fin N, c k = 0`
- **What**: Laurent polynomial uniqueness — vanishing form: if a finite Laurent polynomial agrees with an analytic function in a punctured neighborhood of `s`, all coefficients vanish.
- **How**: Reverse induction on `N`. Define `P(z) = Σ c_k (z-s)^(N-k)` and `Q(z) = (z-s)^(N+1) g(z)`; show `P =ᶠ Q` in `𝓝[≠] s`, lift to `𝓝 s` via `AnalyticAt.frequently_eq_iff_eventually_eq`, evaluate at `s`: `P s = c_{N-1}` and `Q s = 0`, so `c_{N-1} = 0`; recurse via `Fin.sum_univ_castSucc`.
- **Hypotheses**: Analytic at `s`, Laurent polynomial eventually equal in `𝓝[≠] s`.
- **Uses from project**: [] (purely mathlib).
- **Used by**: `laurent_extended_coeff_eq_of_diff_analytic`.
- **Visibility**: private
- **Lines**: 1073-1164
- **Notes**: private; proof >30 lines (~90)

### `lemma laurent_sum_extend`
- **Type**: `{N M : ℕ} (hNM : N ≤ M) (c : Fin N → ℂ) (s z : ℂ) (_hz : z ≠ s) : (∑ k : Fin N, c k / (z - s)^(k+1)) = ∑ j : Fin M, (if hj : j.val < N then c ⟨j.val, hj⟩ else 0) / (z - s)^(j+1)`
- **What**: A Laurent polynomial of length `N` equals its extension to length `M ≥ N` (with zeros padded).
- **How**: Reindex via the inclusion `Fin N ↪ Fin M`, using `Finset.sum_image` and `Finset.sum_filter` to bridge the filtered sum and the image sum.
- **Hypotheses**: `N ≤ M`.
- **Uses from project**: [].
- **Used by**: `laurent_extended_coeff_eq_of_diff_analytic`.
- **Visibility**: private
- **Lines**: 1168-1202
- **Notes**: private; proof >30 lines (~35)

### `theorem laurent_extended_coeff_eq_of_diff_analytic`
- **Type**: `{N₁ N₂} (c₁ : Fin N₁ → ℂ) (c₂ : Fin N₂ → ℂ) {s h} (hh : AnalyticAt ℂ h s) (h_diff : (Σc₁/... - Σc₂/...) =ᶠ[𝓝[≠] s] h) : ∀ j : ℕ, (if hj : j < N₁ then c₁ ⟨j,hj⟩ else 0) = (if hj : j < N₂ then c₂ ⟨j,hj⟩ else 0)`
- **What**: Bridge between Laurent decompositions: if the difference of two Laurent polynomials is eventually analytic at `s`, their extended coefficients agree at every index.
- **How**: Pads to `M = max N₁ N₂` via `laurent_sum_extend`, applies `laurent_polynomial_zero_of_eventuallyEq_analytic` to the coefficient differences `d j = c₁_ext j - c₂_ext j`, then unpacks.
- **Hypotheses**: Two Laurent polynomials with analytic difference at `s`.
- **Uses from project**: `laurent_polynomial_zero_of_eventuallyEq_analytic`, `laurent_sum_extend`.
- **Used by**: `angle_compat_of_condB`, `angle_compat_of_condB_anywhere`.
- **Visibility**: private
- **Lines**: 1210-1254
- **Notes**: private; proof >30 lines (~45)

### `theorem angle_compat_of_condB`
- **Type**: `{U S f} (hU_open) (hS_in_U) (γ) (decomp) (hCondB : SatisfiesConditionB γ f S) {s} (hs : s ∈ S) {t₀} (ht₀ : t₀ ∈ Ioo 0 1) (h_at₀) (h_t₀_off : t₀ ∉ partition) : ∀ k : Fin (decomp.order s), 1 ≤ k.val → decomp.coeff s k ≠ 0 → ∃ m : ℤ, k.val * π = m · 2π`
- **What**: T-BR-Y1: derives angle compatibility for `decomp.coeff` at a smooth crossing from condition (B) via Laurent uniqueness; the smooth case fixes the crossing angle as π.
- **How**: Uses `angleAtCrossing_smooth` to compute the angle as π; extracts Laurent data via `hCondB.laurent_compatible`; shows the difference between `decomp.polarPart s`'s Laurent and the condition-(B) Laurent is analytic; applies `laurent_extended_coeff_eq_of_diff_analytic` to identify coefficients and ports the angle equation.
- **Hypotheses**: Open `U`, smooth (off-partition) interior crossing, conditions (B).
- **Uses from project**: `angleAtCrossing`, `angleAtCrossing_smooth`, `SatisfiesConditionB`, `PolarPartDecomposition` (analyticRemainder_diff, polarPart_eq, decomp, order, coeff), `laurent_extended_coeff_eq_of_diff_analytic`.
- **Used by**: `cpv_polarPart_at_pole_from_conditions`, `cpv_polarPart_at_pole_from_conditions_asymmetric`, `residueTheorem_crossing_asymmetric_scenario`, `residueTheorem_crossing_asymmetric_multiCrossing`, `residueTheorem_crossing_asymmetric_multiPole`, `residueTheorem_crossing_truly_full_spec` (smooth branch).
- **Visibility**: public
- **Lines**: 1262-1424
- **Notes**: proof >30 lines (~165)

### `theorem angle_compat_of_condB_anywhere`
- **Type**: same as `angle_compat_of_condB` but returns `k.val * angleAtCrossing γ t₀ ht₀ = m · 2π` (angle in symbolic form, not specialized to π).
- **What**: Corner-friendly form of `angle_compat_of_condB` (T-BR-Y10b): drops the off-partition hypothesis, returns the angle equation symbolically in terms of `angleAtCrossing`.
- **How**: Same Laurent-uniqueness skeleton as `angle_compat_of_condB`, but without specializing the angle to π via `angleAtCrossing_smooth`.
- **Hypotheses**: Open `U`, interior crossing, condition (B); no off-partition.
- **Uses from project**: `angleAtCrossing`, `SatisfiesConditionB`, `PolarPartDecomposition`, `laurent_extended_coeff_eq_of_diff_analytic`.
- **Used by**: `residueTheorem_crossing_truly_full_spec` (corner branch).
- **Visibility**: public
- **Lines**: 1432-1551
- **Notes**: proof >30 lines (~120)

### `theorem cpv_polarPart_at_pole_from_conditions`
- **Type**: `(hU_open) (hU_ne) {S} (hS_in_U) {f} (_hf) (γ) (h_null) (decomp) (hCondA) (hCondB) (h_geometry : ∀ s ∈ S, …, SingleCrossingData γP s) (h_unique_cross) (h_no_corner_crossings) (h_avoid_others_per_pole) (s) (hs) : HasCauchyPVOn S (decomp.polarPart s) γP value`
- **What**: T-BR-04 headline: per-pole CPV at any pole, paper-faithful form. Case-splits on crossed/uncrossed, derives flat & angle data from (A')/(B), routes through smooth crossed-pole machinery.
- **How**: `by_cases` on whether `∃ t, γ t = s`: uncrossed branch uses `cpv_polarPart_at_uncrossed_pole`; crossed branch extracts `t₀` from `h_unique_cross`, builds `SingleCrossingData` from `h_geometry`, derives flat data via `flat_data_of_condA_at_crossing`, angle compat via `angle_compat_of_condB`, then applies `cpv_polarPart_at_crossed_pole_hasCauchyPV` + lifts via `hasCauchyPVOn_of_hasCauchyPV_of_avoid_other_poles`.
- **Hypotheses**: `(hCondA, hCondB)`, residual geometry oracles (`h_geometry`, `h_unique_cross`, `h_no_corner_crossings`, `h_avoid_others_per_pole`).
- **Uses from project**: `flat_data_of_condA_at_crossing`, `angle_compat_of_condB`, `cpv_polarPart_at_crossed_pole_hasCauchyPV`, `hasCauchyPVOn_of_hasCauchyPV_of_avoid_other_poles`, `cpv_polarPart_at_uncrossed_pole`, `SingleCrossingData`.
- **Used by**: `residueTheorem_crossing`, `cpv_polarPart_at_pole_from_conditions_singleton`.
- **Visibility**: public
- **Lines**: 1575-1634
- **Notes**: proof >30 lines (~60)

### `theorem cpv_polarPart_at_pole_from_conditions_asymmetric`
- **Type**: same as `cpv_polarPart_at_pole_from_conditions` but with `AsymmetricSingleCrossingData` in `h_geometry`.
- **What**: Asymmetric variant of T-BR-04: strict generalization (every symmetric upgrades).
- **How**: Identical to symmetric form, routes through `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric`.
- **Hypotheses**: As above with `AsymmetricSingleCrossingData`.
- **Uses from project**: `flat_data_of_condA_at_crossing`, `angle_compat_of_condB`, `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric`, `hasCauchyPVOn_of_hasCauchyPV_of_avoid_other_poles`, `cpv_polarPart_at_uncrossed_pole`, `AsymmetricSingleCrossingData`.
- **Used by**: `residueTheorem_crossing_asymmetric`.
- **Visibility**: public
- **Lines**: 1641-1693
- **Notes**: proof >30 lines (~50)

### `theorem cpv_polarPart_at_pole_from_conditions_singleton`
- **Type**: same signature as `cpv_polarPart_at_pole_from_conditions` but specialized to `S = {s₀}` and drops `h_avoid_others_per_pole`.
- **What**: Singleton-S specialisation (T-BR-Y1b): drops the vacuous `h_avoid_others_per_pole` hypothesis.
- **How**: Builds the trivial avoidance hypothesis (vacuous when `S = {s₀}`), then delegates to `cpv_polarPart_at_pole_from_conditions`.
- **Hypotheses**: All hypotheses of the multi-pole form, sans `h_avoid_others_per_pole`.
- **Uses from project**: `cpv_polarPart_at_pole_from_conditions`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 1712-1754
- **Notes**: none

### `theorem residueTheorem_crossing`
- **Type**: `(hU_open) (hU_ne) {S} (hS_in_U) {f} (hf) (γ : ClosedPwC1Immersion x) (h_null) (hMero) (hCondB) (hCondA) (h_geometry : … SingleCrossingData …) (h_unique_cross) (h_no_corner_crossings) (h_avoid_others_per_pole) : HasCauchyPVOn S f γP (∑ s, 2πi w · res f s)`
- **What**: Paper-faithful Hungerbühler–Wasem 3.3 with `SingleCrossingData`-style geometric scaffolding.
- **How**: Builds the polar-part decomposition via `PolarPartDecomposition.ofMeromorphicWithCondB`; applies `cpv_polarPart_at_pole_from_conditions` per pole; composes with `residueTheorem_crossing_compositional`.
- **Hypotheses**: Conditions A' and B, residual geometric oracles.
- **Uses from project**: `PolarPartDecomposition.ofMeromorphicWithCondB`, `cpv_polarPart_at_pole_from_conditions`, `residueTheorem_crossing_compositional`.
- **Used by**: `residueTheorem_crossing_singleton`.
- **Visibility**: public
- **Lines**: 1800-1849
- **Notes**: none

### `theorem residueTheorem_crossing_singleton`
- **Type**: same as `residueTheorem_crossing` specialized to `S = {s₀}` (drops `h_avoid_others_per_pole`).
- **What**: Singleton specialization of `residueTheorem_crossing` (T-BR-Y1b).
- **How**: Builds the vacuous avoidance hypothesis, delegates to `residueTheorem_crossing`.
- **Hypotheses**: All of `residueTheorem_crossing` sans avoidance.
- **Uses from project**: `residueTheorem_crossing`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 1856-1897
- **Notes**: none

### `theorem residueTheorem_crossing_asymmetric`
- **Type**: same as `residueTheorem_crossing` but `h_geometry` returns `AsymmetricSingleCrossingData`.
- **What**: T-BR-Y3 asymmetric variant of `residueTheorem_crossing`.
- **How**: Builds the polar decomposition; applies `cpv_polarPart_at_pole_from_conditions_asymmetric`; composes with `residueTheorem_crossing_compositional`.
- **Hypotheses**: as `residueTheorem_crossing` with asymmetric geometry.
- **Uses from project**: `PolarPartDecomposition.ofMeromorphicWithCondB`, `cpv_polarPart_at_pole_from_conditions_asymmetric`, `residueTheorem_crossing_compositional`.
- **Used by**: `residueTheorem_crossing_asymmetric_derived`, `residueTheorem_crossing_asymmetric_cpv`, `residueTheorem_crossing_singleton_asymmetric`.
- **Visibility**: public
- **Lines**: 1916-1962
- **Notes**: none

### `theorem residueTheorem_crossing_asymmetric_derived`
- **Type**: Same as `residueTheorem_crossing_asymmetric`, but `h_geometry` is replaced by `h_geometry_derived : ∀ s ∈ S, … Σ' L, DerivedAsymmetricCutoffs γ s t₀ → AsymmetricArcFTCHyp γP s t₀ D.δ_left D.δ_right D.threshold L`.
- **What**: T-BR-Y3b — derives the geometric scaffolding automatically via `AsymmetricSingleCrossingData.ofClosedImmersion_flat_one_derived`; user supplies only analytic FTC content.
- **How**: Uses `Classical.choose` to extract the unique crossing parameter from `h_unique_cross`, then constructs `AsymmetricSingleCrossingData` via the derived constructor; defers to `residueTheorem_crossing_asymmetric`.
- **Hypotheses**: FTC bundle `mkFTCHyp` per pole, residual geometric oracles.
- **Uses from project**: `HungerbuhlerWasem.DerivedAsymmetricCutoffs`, `AsymmetricArcFTCHyp`, `HungerbuhlerWasem.AsymmetricSingleCrossingData.ofClosedImmersion_flat_one_derived`, `residueTheorem_crossing_asymmetric`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 1990-2057
- **Notes**: proof >30 lines (~30)

### `theorem residueTheorem_crossing_singleton_asymmetric`
- **Type**: singleton specialization of `residueTheorem_crossing_asymmetric`.
- **What**: Drops the vacuous `h_avoid_others_per_pole` for `S = {s₀}`.
- **How**: Builds the vacuous avoidance hypothesis, delegates to `residueTheorem_crossing_asymmetric`.
- **Hypotheses**: all of `residueTheorem_crossing_asymmetric` sans avoidance.
- **Uses from project**: `residueTheorem_crossing_asymmetric`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 2063-2104
- **Notes**: none

### `theorem residueTheorem_crossing_asymmetric_cpv`
- **Type**: same as `_asymmetric_derived`, but the geometry oracle is reduced to `Σ' L, HasCauchyPV (fun z => (z - s)⁻¹) γP s L` (CPV existence).
- **What**: T-BR-Y3c: reduces the FTC bundle to a single `HasCauchyPV` per pole.
- **How**: Builds `AsymmetricSingleCrossingData` via `ofClosedImmersion_hasCauchyPV` (the CPV-based constructor) from the chosen unique parameter; defers to `residueTheorem_crossing_asymmetric`.
- **Hypotheses**: Per-pole `HasCauchyPV` for `(z - s)⁻¹`, geometric oracles.
- **Uses from project**: `HasCauchyPV`, `HungerbuhlerWasem.AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV`, `residueTheorem_crossing_asymmetric`.
- **Used by**: `residueTheorem_crossing_asymmetric_full`.
- **Visibility**: public
- **Lines**: 2129-2188
- **Notes**: proof >30 lines (~25)

### `theorem residueTheorem_crossing_asymmetric_full`
- **Type**: Same conclusion as `_asymmetric_cpv`, but drops the geometry CPV oracle in favour of internal construction.
- **What**: T-BR-Y3h: fully oracle-free crossing form. CPV existence built internally from immersion data via `hasCauchyPV_inv_sub_of_flat_one_full`; order-1 flatness derived from (A') via `flat_data_of_condA_at_crossing` + `IsFlatOfOrder.of_le`.
- **How**: Builds the polar decomposition, derives `IsFlatOfOrder γ t₀ 1` from condition (A'), invokes `hasCauchyPV_inv_sub_of_flat_one_full` to get CPV existence, then routes through `residueTheorem_crossing_asymmetric_cpv`.
- **Hypotheses**: Analytic content + uniqueness/non-corner/avoidance data only.
- **Uses from project**: `PolarPartDecomposition.ofMeromorphicWithCondB`, `flat_data_of_condA_at_crossing`, `IsFlatOfOrder.of_le`, `hasCauchyPV_inv_sub_of_flat_one_full`, `residueTheorem_crossing_asymmetric_cpv`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 2211-2264
- **Notes**: proof >30 lines (~25)

### `inductive CrossingScenario`
- **Type**: `(γ : ClosedPwC1Immersion x) (S : Finset ℂ) : Type` with constructors `avoidance` and `oneCrossing`.
- **What**: Captures the (`avoidance` | `oneCrossing`) dichotomy for γ relative to a finite pole set `S`.
- **How**: `avoidance` packs the proof that γ avoids every `s ∈ S`; `oneCrossing` packs a single interior off-partition crossing parameter `t₀`, pole `s_cross ∈ S`, uniqueness, and avoidance of all other poles.
- **Hypotheses**: -
- **Uses from project**: `ClosedPwC1Immersion`.
- **Used by**: `residueTheorem_crossing_asymmetric_scenario`.
- **Visibility**: public
- **Lines**: 2295-2309
- **Notes**: inductive type

### `theorem residueTheorem_crossing_asymmetric_scenario`
- **Type**: HW3.3 with the residual three hypotheses (`h_unique_cross`, `h_no_corner_crossings`, `h_avoid_others_per_pole`) absorbed into a single `scenario : CrossingScenario γ S` datum.
- **What**: T-BR-Y4: cleaner API — single structured scenario rather than three quantifier-laden hypotheses.
- **How**: Case-splits on `scenario`. `avoidance` branch uses `residueTheorem_avoidance` directly; `oneCrossing` branch builds per-pole CPV witnesses via either `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric` (for `s = s_cross`) or `cpv_polarPart_at_uncrossed_pole` (other poles), then composes with `residueTheorem_crossing_compositional`.
- **Hypotheses**: Conditions A'/B; single scenario datum.
- **Uses from project**: `CrossingScenario`, `HungerbuhlerWasem.residueTheorem_avoidance`, `residueTheorem_crossing_compositional`, `flat_data_of_condA_at_crossing`, `IsFlatOfOrder.of_le`, `hasCauchyPV_inv_sub_of_flat_one_full`, `HungerbuhlerWasem.AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV`, `angle_compat_of_condB`, `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric`, `hasCauchyPVOn_of_hasCauchyPV_of_avoid_other_poles`, `cpv_polarPart_at_uncrossed_pole`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 2330-2407
- **Notes**: proof >30 lines (~60)

### `structure PerPoleCrossData`
- **Type**: `(γ : ClosedPwC1Immersion x) (s : ℂ) where t₀ : ℝ; ht₀_Ioo, h_at, h_off, h_unique`
- **What**: Per-pole geometric crossing data: a single interior off-partition crossing parameter at which γ meets pole `s`, with uniqueness.
- **How**: Bundled record.
- **Hypotheses**: -
- **Uses from project**: `ClosedPwC1Immersion`.
- **Used by**: `MultiCrossingScenario`, `PerPoleCrossData.toMulti`, `MultiPoleCrossData.toPerPole_of_card_one`.
- **Visibility**: public
- **Lines**: 2427-2438
- **Notes**: structure

### `structure MultiPoleCrossData`
- **Type**: `(γ : ClosedPwC1Immersion x) (s : ℂ) where crossings : Finset ℝ; h_Ioo, h_at, h_off, h_complete`
- **What**: Multi-crossing data for a single pole: γ may cross `s` at multiple parameters, each interior off-partition; `h_complete` asserts the finset enumerates all crossings.
- **How**: Bundled record (no uniqueness).
- **Hypotheses**: -
- **Uses from project**: `ClosedPwC1Immersion`.
- **Used by**: `PerPoleCrossData.toMulti`, `MultiPoleCrossData.ofAvoidance`, `MultiPoleCrossData.avoids_of_crossings_empty`, `MultiPoleCrossData.toPerPole_of_card_one`, `hasCauchyPV_inv_sub_multiCrossing_card_le_one`, `MultiPoleCrossScenario`, `residueTheorem_crossing_asymmetric_multiPole`.
- **Visibility**: public
- **Lines**: 2453-2465
- **Notes**: structure

### `def PerPoleCrossData.toMulti`
- **Type**: `{γ s} (D : PerPoleCrossData γ s) : MultiPoleCrossData γ s`
- **What**: Converts a single-crossing datum into a multi-crossing datum with `crossings = {D.t₀}`.
- **How**: Direct construction; the `h_complete` clause uses `D.h_unique` for the singleton membership.
- **Hypotheses**: -
- **Uses from project**: `PerPoleCrossData`, `MultiPoleCrossData`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 2469-2482
- **Notes**: noncomputable

### `def MultiPoleCrossData.ofAvoidance`
- **Type**: `{γ s} (h_avoid : ∀ t ∈ Icc 0 1, γ t ≠ s) : MultiPoleCrossData γ s`
- **What**: The avoidance case as an empty-crossings `MultiPoleCrossData`.
- **How**: Direct construction with `crossings = ∅`.
- **Hypotheses**: γ avoids `s` on `Icc 0 1`.
- **Uses from project**: `MultiPoleCrossData`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 2485-2496
- **Notes**: noncomputable

### `theorem MultiPoleCrossData.avoids_of_crossings_empty`
- **Type**: `{γ s} (M : MultiPoleCrossData γ s) (h_empty : M.crossings = ∅) : ∀ t ∈ Icc 0 1, γ t ≠ s`
- **What**: If the crossings finset is empty, γ avoids `s` on `Icc 0 1`.
- **How**: Direct use of `M.h_complete` and `Finset.notMem_empty`.
- **Hypotheses**: Empty crossings finset.
- **Uses from project**: `MultiPoleCrossData`.
- **Used by**: `hasCauchyPV_inv_sub_multiCrossing_card_le_one`, `residueTheorem_crossing_asymmetric_multiPole`.
- **Visibility**: public
- **Lines**: 2499-2507
- **Notes**: none

### `def MultiPoleCrossData.toPerPole_of_card_one`
- **Type**: `{γ s} (M : MultiPoleCrossData γ s) (h_one : M.crossings.card = 1) : PerPoleCrossData γ s`
- **What**: Extracts a `PerPoleCrossData` when the crossings finset has exactly one element.
- **How**: `Finset.card_eq_one.mp` provides the unique element via `Classical.choose`; per-field extraction from `M`.
- **Hypotheses**: `M.crossings.card = 1`.
- **Uses from project**: `MultiPoleCrossData`, `PerPoleCrossData`.
- **Used by**: `residueTheorem_crossing_asymmetric_multiPole`.
- **Visibility**: public
- **Lines**: 2511-2525
- **Notes**: noncomputable

### `theorem hasCauchyPV_inv_sub_multiCrossing_card_le_one`
- **Type**: `{γ s} (D : MultiPoleCrossData γ s) (h_card_le_one : D.crossings.card ≤ 1) (h_flat_at_each : ∀ t₀ ∈ D.crossings, IsFlatOfOrder γ.extend t₀ 1) : ∃ L, HasCauchyPV (fun z => (z - s)⁻¹) γP s L`
- **What**: T-BR-Y6e: Multi-crossing CPV existence for `card ≤ 1`. Case `card = 0` → avoidance; case `card = 1` → simple pole at the unique crossing.
- **How**: `card = 0` extracts the avoidance via `D.avoids_of_crossings_empty`, finds δ > 0 via `IsCompact.exists_isMinOn` on continuous `‖γ t - s‖`, applies `hasCauchyPV_of_avoids`. `card = 1` extracts the unique parameter, applies `hasCauchyPV_inv_sub_of_flat_one_full` with the supplied flatness.
- **Hypotheses**: Multi-crossing data with at most 1 element; flatness at each crossing.
- **Uses from project**: `MultiPoleCrossData`, `IsFlatOfOrder`, `hasCauchyPV_of_avoids`, `hasCauchyPV_inv_sub_of_flat_one_full`, `HasCauchyPV`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 2558-2610
- **Notes**: proof >30 lines (~50)

### `structure MultiCrossingScenario`
- **Type**: `(γ S) where data : ∀ s ∈ S, PSum (PLift (avoidance)) (PerPoleCrossData γ s)`
- **What**: Per-pole scenario data combining the avoidance and single-crossing cases via `PSum` (since avoidance lives in `Prop` and crossing data lives in `Type`).
- **How**: Bundled record.
- **Hypotheses**: -
- **Uses from project**: `PerPoleCrossData`, `ClosedPwC1Immersion`.
- **Used by**: `residueTheorem_crossing_asymmetric_multiCrossing`.
- **Visibility**: public
- **Lines**: 2621-2628
- **Notes**: structure

### `structure MultiPoleCrossScenario`
- **Type**: `(γ S) where data : ∀ s ∈ S, MultiPoleCrossData γ s`
- **What**: Per-pole scenario data using `MultiPoleCrossData` (allows multiple crossings per pole).
- **How**: Bundled record.
- **Hypotheses**: -
- **Uses from project**: `MultiPoleCrossData`, `ClosedPwC1Immersion`.
- **Used by**: `residueTheorem_crossing_asymmetric_multiPole`, `residueTheorem_crossing_asymmetric_multiPole_card_le_one`, `MultiPoleCrossScenario.ofImmersion`, `residueTheorem_crossing_card_le_one_full_spec`, `residueTheorem_crossing_no_basepoint_no_unique_constraint`, `residueTheorem_crossing_no_basepoint_no_unique_constraint_of_unique`.
- **Visibility**: public
- **Lines**: 2636-2638
- **Notes**: structure

### `theorem residueTheorem_crossing_asymmetric_multiCrossing`
- **Type**: Same conclusion as `_asymmetric` but takes `scenario : MultiCrossingScenario γ S`.
- **What**: T-BR-Y5: multi-crossing scenario form. γ may cross multiple poles in `S` (one transverse crossing per pole).
- **How**: Compositional via `residueTheorem_crossing_compositional`. Per pole, case-splits on `scenario.data s hs`: avoidance → `cpv_polarPart_at_uncrossed_pole`; crossing → build singleton CPV via `hasCauchyPV_inv_sub_of_flat_one_full` + `ofClosedImmersion_hasCauchyPV`, then lift via `MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole`.
- **Hypotheses**: Conditions A'/B, scenario.
- **Uses from project**: `PolarPartDecomposition.ofMeromorphicWithCondB`, `residueTheorem_crossing_compositional`, `MultiCrossingScenario`, `cpv_polarPart_at_uncrossed_pole`, `flat_data_of_condA_at_crossing`, `IsFlatOfOrder.of_le`, `hasCauchyPV_inv_sub_of_flat_one_full`, `HungerbuhlerWasem.AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV`, `angle_compat_of_condB`, `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric`, `MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 2648-2706
- **Notes**: proof >30 lines (~40)

### `theorem residueTheorem_crossing_asymmetric_multiPole`
- **Type**: Same as `_multiCrossing` but accepts `MultiPoleCrossScenario γ S` (allows multiple crossings per pole) and an `h_multi_cpv` oracle for poles with ≥ 2 crossings.
- **What**: T-BR-Y6: multi-crossings-per-pole form. Oracle dispatches `≥ 2` case; `≤ 1` case uses existing infrastructure.
- **How**: For each pole, case-split on `M.crossings.card`: `0` → uncrossed branch; `1` → extract `PerPoleCrossData`, build single-point CPV, lift via multi-pole DCT; `≥ 2` → oracle.
- **Hypotheses**: Conditions A'/B, multi-pole scenario, oracle for `card ≥ 2`.
- **Uses from project**: `PolarPartDecomposition.ofMeromorphicWithCondB`, `residueTheorem_crossing_compositional`, `MultiPoleCrossScenario`, `MultiPoleCrossData`, `cpv_polarPart_at_uncrossed_pole`, `MultiPoleCrossData.toPerPole_of_card_one`, `MultiPoleCrossData.avoids_of_crossings_empty`, `flat_data_of_condA_at_crossing`, `IsFlatOfOrder.of_le`, `hasCauchyPV_inv_sub_of_flat_one_full`, `HungerbuhlerWasem.AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV`, `angle_compat_of_condB`, `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric`, `MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole`.
- **Used by**: `residueTheorem_crossing_asymmetric_multiPole_card_le_one`, `residueTheorem_crossing_no_basepoint_no_unique_constraint`.
- **Visibility**: public
- **Lines**: 2735-2819
- **Notes**: proof >30 lines (~60)

### `theorem residueTheorem_crossing_asymmetric_multiPole_card_le_one`
- **Type**: Same as `_multiPole` but adds hypothesis `h_card_le_one : ∀ s ∈ S, … card ≤ 1` and drops the multi-CPV oracle.
- **What**: Convenience corollary when every pole has at most 1 crossing.
- **How**: Delegates to `residueTheorem_crossing_asymmetric_multiPole`, with the `card ≥ 2` oracle discharged by `omega` (vacuous under `h_card_le_one`).
- **Hypotheses**: Same as `_multiPole` with `h_card_le_one`.
- **Uses from project**: `residueTheorem_crossing_asymmetric_multiPole`, `MultiPoleCrossScenario`.
- **Used by**: `residueTheorem_crossing_card_le_one_full_spec`.
- **Visibility**: public
- **Lines**: 2824-2845
- **Notes**: none

### `def MultiPoleCrossScenario.ofImmersion`
- **Type**: `{γ : ClosedPwC1Immersion x} {S} (hx_notin_S) (h_no_corner_crossings) : MultiPoleCrossScenario γ S`
- **What**: T-BR-Y7: auto-derives a `MultiPoleCrossScenario` from immersion data via Proposition 2.2 (`crossingSet_finite`).
- **How**: For each `s ∈ S`, derives `γ 0 ≠ s` and `γ 1 ≠ s` from `hx_notin_S`; applies `PwC1Immersion.crossingSet_finite` to get a finite set; packages as `MultiPoleCrossData`.
- **Hypotheses**: `x ∉ S`; no pole crossings at partition points.
- **Uses from project**: `MultiPoleCrossScenario`, `MultiPoleCrossData`, `PwC1Immersion.crossingSet_finite`, `PwC1Immersion.crossingSet`, `ClosedPwC1Immersion`.
- **Used by**: `residueTheorem_crossing_card_le_one_full_spec`, `residueTheorem_crossing_no_basepoint_no_unique_constraint`, `residueTheorem_crossing_no_basepoint_no_unique_constraint_of_unique`.
- **Visibility**: public
- **Lines**: 2872-2940
- **Notes**: noncomputable; proof >30 lines (~65)

### `theorem exists_basepoint_shift_param`
- **Type**: `(γ : ClosedPwC1Immersion x) (S : Finset ℂ) : ∃ τ ∈ Ioo 0 1, γP τ ∉ ↑S`
- **What**: T-BR-Y8b: Existence of a non-pole interior parameter; the preimage `γ⁻¹(S) ∩ Icc 0 1` has measure zero while `Ioo 0 1` has positive measure.
- **How**: `by_contra` + show `Ioo 0 1 ⊆ badSet`, then `volume (Ioo 0 1) ≤ volume badSet = 0` contradicts `Real.volume_Ioo > 0`. Uses `volume_preimage_finset_in_Icc01_zero`.
- **Hypotheses**: -
- **Uses from project**: `volume_preimage_finset_in_Icc01_zero`, `ClosedPwC1Immersion`.
- **Used by**: unused in file (kept for cyclic-shift work).
- **Visibility**: public
- **Lines**: 2962-2986
- **Notes**: none

### `theorem residueTheorem_crossing_card_le_one_full_spec`
- **Type**: HW3.3 with paper spec + `hx_notin_S`, `h_no_corner_crossings`, `h_unique_cross` only.
- **What**: T-BR-Y7: eliminates the scenario oracle; auto-derives via `MultiPoleCrossScenario.ofImmersion`.
- **How**: Builds scenario via `MultiPoleCrossScenario.ofImmersion`, shows `card ≤ 1` via `Finset.card_le_one` + `h_unique_cross`, delegates to `residueTheorem_crossing_asymmetric_multiPole_card_le_one`.
- **Hypotheses**: As above.
- **Uses from project**: `MultiPoleCrossScenario.ofImmersion`, `residueTheorem_crossing_asymmetric_multiPole_card_le_one`.
- **Used by**: `residueTheorem_crossing_card_le_one_full_spec_reparam`, `residueTheorem_crossing_card_le_one_full_spec_basepoint_off`, `residueTheorem_crossing_card_le_one_full_spec_general`, `residueTheorem_crossing_card_le_one_no_basepoint_constraint`.
- **Visibility**: public
- **Lines**: 3038-3082
- **Notes**: proof >30 lines (~45)

### `theorem residueTheorem_crossing_card_le_one_full_spec_reparam`
- **Type**: HW3.3 without `hx_notin_S`, plus an explicit reparametrization-lift hypothesis `h_reparam_lift`.
- **What**: T-BR-Y8 reparametrization shim: drops `hx_notin_S` from the spec by accepting reparametrization invariance as an explicit hypothesis.
- **How**: Direct delegation: the lift hypothesis takes a generic `γ'` with `x' ∉ S` and the per-pole spec hypotheses; passes them through `_full_spec`.
- **Hypotheses**: Paper spec, conditions A'/B, reparametrization-lift hypothesis.
- **Uses from project**: `residueTheorem_crossing_card_le_one_full_spec`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 3130-3177
- **Notes**: none

### `theorem residueTheorem_crossing_card_le_one_full_spec_basepoint_off`
- **Type**: HW3.3 with the same signature as `_full_spec`, just renamed.
- **What**: T-BR-Y8b common case: `x ∉ S` packaged as the entry point for the `_general` case-split.
- **How**: Direct delegation to `_full_spec`.
- **Hypotheses**: Same as `_full_spec`.
- **Uses from project**: `residueTheorem_crossing_card_le_one_full_spec`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 3213-3238
- **Notes**: none

### `theorem residueTheorem_crossing_card_le_one_full_spec_general`
- **Type**: HW3.3 without `hx_notin_S` but with `h_reparam_lift_at_pole_basepoint : x ∈ S → (lift hypothesis)`.
- **What**: T-BR-Y8b general case: case-split on `x ∈ S` — easy case delegates to `_full_spec`; pole-basepoint case uses the named cyclic-shift lift.
- **How**: `by_cases hx : x ∈ S`; in the `True` branch invokes the lift hypothesis; in the `False` branch delegates to `_full_spec`.
- **Hypotheses**: Paper spec; named lift in the pole-basepoint case.
- **Uses from project**: `residueTheorem_crossing_card_le_one_full_spec`.
- **Used by**: `residueTheorem_crossing_card_le_one_full_spec_general_basepoint_off`.
- **Visibility**: public
- **Lines**: 3271-3331
- **Notes**: none

### `theorem residueTheorem_crossing_card_le_one_full_spec_general_basepoint_off`
- **Type**: Same as `_general` but with `hx_notin_S` packaged into the spec hypotheses.
- **What**: T-BR-Y8b corollary: when `x ∉ S`, the cyclic-shift lift is vacuous; auto-discharge.
- **How**: Direct delegation to `_general` with a vacuous lift constructor.
- **Hypotheses**: As `_general` with `hx_notin_S`.
- **Uses from project**: `residueTheorem_crossing_card_le_one_full_spec_general`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 3346-3372
- **Notes**: none

### `theorem residueTheorem_crossing_card_le_one_no_basepoint_constraint`
- **Type**: HW3.3 with paper spec + `h_no_corner_crossings`, `h_unique_cross` only — drops both `hx_notin_S` and the cyclic-shift lift.
- **What**: T-BR-Y8f: cleanest form via the observation that `x ∈ S` combined with `h_unique_cross` (applied at `s := x, t₁ := 0, t₂ := 1`) yields `0 = 1`, so the `x ∈ S` case is automatically inconsistent.
- **How**: `by_cases hx : x ∈ S`; `True` case derives `0 = 1` from `h_unique_cross` and `apply_zero`/`apply_one` — contradiction; `False` case delegates to `_full_spec`.
- **Hypotheses**: Paper spec + corner avoidance + uniqueness.
- **Uses from project**: `residueTheorem_crossing_card_le_one_full_spec`, `apply_zero`, `apply_one` on `PiecewiseC1Path.toPath`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 3396-3434
- **Notes**: none

### `theorem residueTheorem_crossing_no_basepoint_no_unique_constraint`
- **Type**: HW3.3 with paper spec + `hx_notin_S`, `h_no_corner_crossings`, plus per-pole oracle `h_multi_cpv_polar_part` for poles with ≥ 2 crossings.
- **What**: T-BR-Y9: drops `h_unique_cross`, exposes the multi-crossing CPV oracle for poles with ≥ 2 crossings; vacuous for unique-crossing scenarios.
- **How**: Builds scenario via `MultiPoleCrossScenario.ofImmersion`, delegates to `residueTheorem_crossing_asymmetric_multiPole` with the oracle.
- **Hypotheses**: Conditions A'/B, `hx_notin_S`, no-corner, per-pole oracle.
- **Uses from project**: `MultiPoleCrossScenario.ofImmersion`, `residueTheorem_crossing_asymmetric_multiPole`.
- **Used by**: `residueTheorem_crossing_no_basepoint_no_unique_constraint_of_unique`.
- **Visibility**: public
- **Lines**: 3487-3526
- **Notes**: none

### `theorem residueTheorem_crossing_no_basepoint_no_unique_constraint_of_unique`
- **Type**: Same as `_no_unique_constraint` but with `h_unique_cross` restored.
- **What**: Convenience corollary: when uniqueness holds the multi-CPV oracle is vacuous.
- **How**: Delegates to `residueTheorem_crossing_no_basepoint_no_unique_constraint`, discharging the `card ≥ 2` oracle by deriving `card ≤ 1` from `h_unique_cross` and `omega`.
- **Hypotheses**: Paper spec + uniqueness + `hx_notin_S`.
- **Uses from project**: `residueTheorem_crossing_no_basepoint_no_unique_constraint`, `MultiPoleCrossScenario.ofImmersion`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 3541-3585
- **Notes**: none

### `theorem corner_angle_compat_to_h_B`
- **Type**: `(γ) {t₀} (ht₀) (h_part : t₀ ∈ partition) {L_minus L_plus} (hL_minus_ne) (hL_plus_ne) (hL_left_spec : L_minus = Classical.choose left_deriv_limit) (hL_right_spec : L_plus = Classical.choose right_deriv_limit) {k} (hk : 2 ≤ k) (h_angle_raw : ∃ m, (k - 1 : ℕ) * angleAtCrossing γ t₀ ht₀ = m · 2π) : (L_plus / ↑‖L_plus‖)^(k-1) = ((-L_minus) / ↑‖L_minus‖)^(k-1)`
- **What**: Bridge from the symbolic angle equation at a corner to the unit-circle power equation used by the corner-friendly CPV machinery.
- **How**: Computes `angleAtCrossing` at a corner as `arg L_plus - arg (-L_minus)` via `dif_pos h_part` on the definition; applies `h_B_of_angle_compat_corner`.
- **Hypotheses**: γ partition crossing, nonzero one-sided limits, `k ≥ 2`, the raw angle equation.
- **Uses from project**: `angleAtCrossing`, `h_B_of_angle_compat_corner`, `ClosedPwC1Immersion`.
- **Used by**: `residueTheorem_crossing_truly_full_spec` (corner branch).
- **Visibility**: public
- **Lines**: 3615-3637
- **Notes**: none

### `theorem residueTheorem_crossing_truly_full_spec`
- **Type**: HW3.3 with paper spec + `h_unique_cross` only — no `h_no_corner_crossings`, no `hx_notin_S`, no other technical hypotheses.
- **What**: T-BR-Y10b: the truly final paper-faithful form. Admits both smooth and corner crossings; `hx_notin_S` is auto-discharged from `h_unique_cross`.
- **How**: Auto-discharges `hx_notin_S` (as in `_no_basepoint_constraint`). For each pole, derives endpoint avoidance, case-splits avoidance vs crossing; in crossing case extracts `t₀`, derives flat data, single-pole CPV via `hasCauchyPV_inv_sub_of_flat_one_full`, then case-splits on `t₀ ∈ partition`: corner branch uses `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric_corner` with `corner_angle_compat_to_h_B` bridge; smooth branch uses `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric`. Final lift via `MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole`.
- **Hypotheses**: Paper spec + conditions A'/B + uniqueness.
- **Uses from project**: `PolarPartDecomposition.ofMeromorphicWithCondB`, `apply_zero`, `apply_one`, `residueTheorem_crossing_compositional`, `cpv_polarPart_at_uncrossed_pole`, `flat_data_of_condA_at_crossing`, `IsFlatOfOrder.of_le`, `hasCauchyPV_inv_sub_of_flat_one_full`, `HungerbuhlerWasem.AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV_anywhere`, `PwC1Immersion.left_deriv_limit`, `PwC1Immersion.right_deriv_limit`, `angle_compat_of_condB_anywhere`, `corner_angle_compat_to_h_B`, `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric_corner`, `angle_compat_of_condB`, `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric`, `MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole`.
- **Used by**: unused in file (the final headline; consumed externally).
- **Visibility**: public
- **Lines**: 3661-3824
- **Notes**: proof >30 lines (~165) — the final headline overlay; combines all infrastructure.

### File Summary

- **Total declarations**: 45
  - 3 defs (`PerPoleCrossData.toMulti`, `MultiPoleCrossData.ofAvoidance`, `MultiPoleCrossData.toPerPole_of_card_one`, `MultiPoleCrossScenario.ofImmersion`) — actually 4 defs.
  - 38 lemmas/theorems
  - 0 instances
  - 4 structures (`PerPoleCrossData`, `MultiPoleCrossData`, `MultiCrossingScenario`, `MultiPoleCrossScenario`) + 1 inductive (`CrossingScenario`) = 5 type declarations
  - 0 abbrevs
  - Adjusted count: 4 defs + 38 theorems/lemmas + 1 inductive + 4 structures = 47. (Some counts above are approximate; exact: 38 named theorems + 4 defs + 1 inductive + 4 structures.)

- **Key API (used by 3+ others in this file)**:
  - `cpv_polarPart_at_uncrossed_pole` (used by 6: from-conditions sym/asym, scenario, multiCrossing, multiPole, truly_full_spec)
  - `flat_data_of_condA_at_crossing` (used by 7)
  - `angle_compat_of_condB` (used by 6)
  - `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric` (used by 5)
  - `residueTheorem_crossing_compositional` (used by 6)
  - `residueTheorem_crossing_card_le_one_full_spec` (used by 4)
  - `MultiPoleCrossScenario.ofImmersion` (used by 3)
  - `MultiPoleCrossData` (used by many)
  - `MultiPoleCrossScenario` (used by many)
  - `cpv_polarPart_at_pole_under_conditions` and `_asymmetric` (used by their crossed-pole variants)
  - `hasCauchyPVOn_of_hasCauchyPV_of_avoid_other_poles` (used by 3)
  - `HasCauchyPV.add`/`zero_fun`/`finset_sum`/`congr_pointwise` (used internally throughout T-GL-01 form)

- **Unused in this file (external API surface)**:
  - `cpv_polarPart_at_pole_from_conditions_singleton`
  - `residueTheorem_crossing_singleton`
  - `residueTheorem_crossing_asymmetric_derived`
  - `residueTheorem_crossing_singleton_asymmetric`
  - `residueTheorem_crossing_asymmetric_full`
  - `residueTheorem_crossing_asymmetric_scenario`
  - `residueTheorem_crossing_asymmetric_multiCrossing`
  - `residueTheorem_crossing_asymmetric_multiPole_card_le_one`
  - `MultiPoleCrossData.ofAvoidance`
  - `PerPoleCrossData.toMulti`
  - `hasCauchyPV_inv_sub_multiCrossing_card_le_one`
  - `exists_basepoint_shift_param`
  - `volume_ball_preimage_tendsto_zero`
  - `residueTheorem_crossing_card_le_one_full_spec_reparam`
  - `residueTheorem_crossing_card_le_one_full_spec_basepoint_off`
  - `residueTheorem_crossing_card_le_one_full_spec_general_basepoint_off`
  - `residueTheorem_crossing_card_le_one_no_basepoint_constraint`
  - `residueTheorem_crossing_no_basepoint_no_unique_constraint_of_unique`
  - `residueTheorem_crossing_truly_full_spec` (the final headline; consumed externally)

- **Declarations with `sorry`**: none.

- **Declarations with `set_option`**: none.

- **Proofs > 30 lines**:
  - `HasCauchyPV.finset_sum` (~45 lines)
  - `cpv_polarPart_at_pole_under_conditions` (~55)
  - `cpv_polarPart_at_pole_under_conditions_asymmetric` (~55)
  - `residueTheorem_crossing_compositional` (~75)
  - `volume_ball_preimage_tendsto_zero` (~60)
  - `cpv_polarPart_at_uncrossed_pole` (~195) — largest
  - `cpv_polarPart_at_crossed_pole_hasCauchyPV` (~70)
  - `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric` (~70)
  - `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric_corner` (~70)
  - `hasCauchyPVOn_of_hasCauchyPV_of_avoid_other_poles` (~45)
  - `laurent_polynomial_zero_of_eventuallyEq_analytic` (~90)
  - `laurent_sum_extend` (~35)
  - `laurent_extended_coeff_eq_of_diff_analytic` (~45)
  - `angle_compat_of_condB` (~165)
  - `angle_compat_of_condB_anywhere` (~120)
  - `cpv_polarPart_at_pole_from_conditions` (~60)
  - `cpv_polarPart_at_pole_from_conditions_asymmetric` (~50)
  - `residueTheorem_crossing_asymmetric_scenario` (~60)
  - `residueTheorem_crossing_asymmetric_multiCrossing` (~40)
  - `residueTheorem_crossing_asymmetric_multiPole` (~60)
  - `MultiPoleCrossScenario.ofImmersion` (~65)
  - `hasCauchyPV_inv_sub_multiCrossing_card_le_one` (~50)
  - `residueTheorem_crossing_card_le_one_full_spec` (~45)
  - `residueTheorem_crossing_truly_full_spec` (~165)

- **File purpose (one paragraph)**:
  This file implements the **crossing form of Hungerbühler–Wasem Theorem 3.3** — the unified statement that the multi-point Cauchy principal value of `∮f` along a closed piecewise-`C¹` immersion `γ` null-homologous in `U` equals `∑ s ∈ S, 2πi · w(γ, s) · residue f s`, even when `γ` may transversely cross poles of any order. Architecturally, it composes three pieces: (i) `T-CC-01` (simple-pole CPV at a crossing) for the residue contribution, (ii) `T-SC-01` / `T-BR-03` (higher-order Laurent vanishing under condition B) for the higher-order terms, and (iii) `T-GL-01` (per-pole composition via `HasCauchyPV.add`, `zero_fun`, `finset_sum`, `congr_pointwise`). The file develops three orthogonal generalisations: an **asymmetric variant** (admitting curves with `‖L_-‖ ≠ ‖L_+‖`), a **corner variant** (admitting crossings at partition points via `corner_angle_compat_to_h_B` + `angle_compat_of_condB_anywhere`), and **scenario abstractions** (`CrossingScenario`, `MultiCrossingScenario`, `MultiPoleCrossScenario`) that progressively absorb geometric residual hypotheses. The Laurent uniqueness machinery (`laurent_polynomial_zero_of_eventuallyEq_analytic`, `laurent_extended_coeff_eq_of_diff_analytic`) bridges condition (B)'s Laurent data to `decomp.coeff` — this is the analytic heart enabling `angle_compat_of_condB`. The chain of overlays (`_full_spec` → `_full_spec_general` → `_no_basepoint_constraint` → `_no_basepoint_no_unique_constraint` → `_truly_full_spec`) progressively eliminates technical hypotheses (`hx_notin_S`, `h_no_corner_crossings`, `h_avoid_others_per_pole`) until reaching the final paper-faithful spec form `residueTheorem_crossing_truly_full_spec` whose only parametric assumption beyond `(hf, h_null, hMero, hCondA, hCondB)` is `h_unique_cross` (each pole crossed at most once). The user-visible final headline is the entry point for downstream applications (e.g., modular forms).
