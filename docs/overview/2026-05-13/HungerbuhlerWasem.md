# Inventory: HungerbuhlerWasem.lean

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HungerbuhlerWasem.lean`
Namespace: `HungerbuhlerWasem` (inside `noncomputable section`)
Lines: 1–1050.

---

### `structure PolarPartDecomposition`
- **Type**: `(f : ℂ → ℂ) (S : Finset ℂ) (U : Set ℂ) : Type` carrying fields `polarPart : ℂ → ℂ → ℂ`, `order : ℂ → ℕ`, `coeff : (s : ℂ) → Fin (order s) → ℂ`, `polarPart_eq`, `residue_eq`, `analyticRemainder : ℂ → ℂ`, `analyticRemainder_diff`, `decomp`.
- **What**: Explicit Laurent polar-part data for a meromorphic `f` on `U \ S`: for each pole `s ∈ S` an order `N`, coefficients `a_{s,k}`, polar part `∑_{k<N} a_{s,k}/(z-s)^{k+1}`, and an analytic remainder `g` differentiable on all of `U`, with `f = g + ∑_s polarPart s` on `U \ S`.
- **How**: Pure bundle declaration. Records the data and equations needed downstream without invoking Mathlib's Laurent-extraction API.
- **Hypotheses**: None (structure schema).
- **Uses from project**: `residue` (from `Residue`).
- **Used by**: `analyticRemainder_contourIntegral_zero`, `analyticRemainder_hasCauchyPVOn_zero`, `cpvIntegrandOn_polarPart_intervalIntegrable`, `residueTheorem_avoidance`, `PolarPartDecomposition.ofSimplePoles`, `residueTheorem_simplePoles_avoidance`, `residueTheorem_convex_avoidance`, `residueTheorem_simplePoles_convex_avoidance`.
- **Visibility**: public (namespaced).
- **Lines**: 71–91.
- **Notes**: structure with 9 fields.

### `def higherOrderPart`
- **Type**: `{N : ℕ} (a : Fin N → ℂ) (s z : ℂ) : ℂ`
- **What**: The strictly higher-order portion of a polar part: sum over `k ≥ 1` of `a k / (z - s)^(k+1)`.
- **How**: Direct `Finset.sum` of an `if k.val ≥ 1` indicator term.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `polarPart_eq_simplePole_add_higherOrder`, `contourIntegral_higherOrderPart_eq_zero_of_avoids`.
- **Visibility**: public (`noncomputable def`).
- **Lines**: 96–97.
- **Notes**: noncomputable.

### `def simplePolePart`
- **Type**: `{N : ℕ} (a : Fin N → ℂ) (s z : ℂ) : ℂ`
- **What**: Simple-pole portion `a₀/(z-s)` (or `0` when `N = 0`).
- **How**: `if h : 0 < N then a ⟨0, h⟩ / (z - s) else 0`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `polarPart_eq_simplePole_add_higherOrder`.
- **Visibility**: public (`noncomputable def`).
- **Lines**: 100–101.
- **Notes**: noncomputable.

### `theorem polarPart_eq_simplePole_add_higherOrder`
- **Type**: `{N : ℕ} (a : Fin N → ℂ) (s z : ℂ) : (∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) = simplePolePart a s z + higherOrderPart a s z`
- **What**: A polar Laurent sum splits as simple-pole + higher-order parts.
- **How**: Case split on `0 < N`. Defines a per-term split `a k / (z-s)^(k+1) = (if k = 0 then a₀/(z-s) else 0) + (if k ≥ 1 then a k / (z-s)^(k+1) else 0)`; then `Finset.sum_add_distrib` and `Finset.sum_eq_single ⟨0,h⟩` collapse the first sum.
- **Hypotheses**: none.
- **Uses from project**: `simplePolePart`, `higherOrderPart`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 104–138.
- **Notes**: 35-line proof; `classical`.

### `theorem contourIntegral_higherOrder_eq_zero_of_avoids`
- **Type**: `{x s : ℂ} (γ : PiecewiseC1Path x x) (h_avoids : ∀ t ∈ Icc 0 1, γ.toPath.extend t ≠ s) {k : ℕ} (hk : 2 ≤ k) (c : ℂ) (h_int : IntervalIntegrable …) : γ.contourIntegral (fun z => c / (z - s) ^ k) = 0`
- **What**: For `k ≥ 2`, the integrand `c/(z-s)^k` has a single-valued antiderivative on `ℂ \ {s}`, so its contour integral over any closed avoiding γ vanishes.
- **How**: Construct antiderivative `F z = (-c/(k-1)) (z - s)^(-(k-1))` and apply `PiecewiseC1Path.contourIntegral_eq_zero_of_hasDerivAt_of_closed`. Derivative computed via `hasDerivAt_zpow` composed with `z ↦ z - s`.
- **Hypotheses**: `k ≥ 2`, γ closed avoiding `s`, integrand interval-integrable.
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.contourIntegral`, `PiecewiseC1Path.contourIntegral_eq_zero_of_hasDerivAt_of_closed`.
- **Used by**: `contourIntegral_higherOrderPart_eq_zero_of_avoids`, `residueTheorem_avoidance`.
- **Visibility**: public.
- **Lines**: 145–175.
- **Notes**: 31 lines.

### `theorem contourIntegral_higherOrderPart_eq_zero_of_avoids`
- **Type**: `{x s : ℂ} (γ : PiecewiseC1Path x x) (h_avoids : …) {N : ℕ} (a : Fin N → ℂ) (h_int_each : ∀ k : Fin N, k.val ≥ 1 → IntervalIntegrable …) : γ.contourIntegral (higherOrderPart a s) = 0`
- **What**: The contour integral over a closed γ avoiding `s` of the higher-order polar part vanishes — each `k ≥ 1` term has antiderivative `−a_k/((k)(z−s)^k)`.
- **How**: `PiecewiseC1Path.contourIntegral_finset_sum` reduces to per-term integrals. Per term: when `k.val ≥ 1`, apply `contourIntegral_higherOrder_eq_zero_of_avoids`; when `k.val = 0`, the term is `0` and `contourIntegral_zero` finishes.
- **Hypotheses**: γ closed avoiding `s`; per-term integrability for `k ≥ 1`.
- **Uses from project**: `higherOrderPart`, `PiecewiseC1Path`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path.contourIntegral_finset_sum`, `PiecewiseC1Path.contourIntegral_zero`, `contourIntegral_higherOrder_eq_zero_of_avoids`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 182–225.
- **Notes**: 44 lines, `classical`.

### `theorem analyticRemainder_contourIntegral_zero`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ} (γ : ClosedPwC1Immersion x) (h_null : IsNullHomologous γ.toPwC1Immersion U) (decomp : PolarPartDecomposition f S U) : γ.toPwC1Immersion.toPiecewiseC1Path.contourIntegral decomp.analyticRemainder = 0`
- **What**: Contour integral of the analytic remainder along null-homologous closed γ in `U` vanishes, even if γ passes through poles of `f`.
- **How**: Existence-pick `w₀ ∈ U` off γ's image (`exists_mem_not_mem_path_image_of_isOpen`), avoidance bound `δ` via `avoids_delta_bound`. Define `G(z) = (z − w₀) · analyticRemainder(z)`, differentiable on `U`. Use Dixon's lemma `dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded` to get `dixonFunction G U γ w = 0` for all `w`. Apply `contourIntegral_eq_zero_of_nullHomologous_at w₀` after rewriting `G/(z−w₀) = analyticRemainder`.
- **Hypotheses**: `U` open, nonempty; γ closed null-homologous; `decomp` provided.
- **Uses from project**: `PolarPartDecomposition`, `ClosedPwC1Immersion`, `PiecewiseC1Path`, `ForMathlib.exists_mem_not_mem_path_image_of_isOpen`, `avoids_delta_bound`, `IsNullHomologous`, `IsNullHomologous.image_subset`, `IsNullHomologous.winding_zero_nhds_of_not_mem_of_closed`, `ClosedPwC1Immersion.lipschitzWith_extend`, `norm_deriv_le_of_lipschitz`, `dixonFunction`, `dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded`, `contourIntegral_eq_zero_of_nullHomologous_at`, `PiecewiseC1Path.contourIntegrand`.
- **Used by**: `analyticRemainder_hasCauchyPVOn_zero`, `residueTheorem_avoidance`.
- **Visibility**: public.
- **Lines**: 234–302.
- **Notes**: 69 lines, `classical`.

### `theorem volume_preimage_finset_in_Icc01_zero`
- **Type**: `(γ : ClosedPwC1Immersion x) (S : Finset ℂ) : volume {t ∈ Icc 0 1 | γ.toPwC1Immersion.toPiecewiseC1Path t ∈ (↑S : Set ℂ)} = 0`
- **What**: For a piecewise-`C¹` immersion γ and finite `S`, the preimage `γ⁻¹(S) ∩ [0,1]` has Lebesgue measure zero.
- **How**: Almost-everywhere `t` lies in `Ioo 0 1` off the partition. There γ is differentiable with nonzero derivative (immersion property). Apply `preimage_finset_measure_zero_of_deriv_ne_zero`.
- **Hypotheses**: γ a closed piecewise-`C¹` immersion.
- **Uses from project**: `ClosedPwC1Immersion`, `PiecewiseC1Path`, `PiecewiseC1Path.partition`, `PiecewiseC1Path.differentiable_off`, `PwC1Immersion.deriv_ne_zero`, `preimage_finset_measure_zero_of_deriv_ne_zero`.
- **Used by**: `cpv_ae_not_mem_S`.
- **Visibility**: public.
- **Lines**: 314–342.
- **Notes**: 29 lines, `classical`.

### `private theorem contourIntegrand_diff_intervalIntegrable`
- **Type**: `(γ : ClosedPwC1Immersion x) {U : Set ℂ} {g : ℂ → ℂ} (h_diff : DifferentiableOn ℂ g U) (hγ_in_U : ∀ t ∈ Icc 0 1, γ.toPwC1Immersion.toPiecewiseC1Path t ∈ U) : IntervalIntegrable (PiecewiseC1Path.contourIntegrand g γ.toPwC1Immersion.toPiecewiseC1Path) volume 0 1`
- **What**: For `g` differentiable on `U` containing γ's image, the contour integrand `g(γ(t)) γ'(t)` is interval-integrable on `[0,1]`.
- **How**: Lipschitz-bounded deriv ⇒ derivative interval-integrable. Composition `g ∘ γ` is continuous on `[0,1]`. Multiply via `IntervalIntegrable.continuousOn_mul`.
- **Hypotheses**: γ closed, `g` differentiable on `U`, γ image in `U`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.lipschitzWith_extend`, `PiecewiseC1Path.contourIntegrand`, `norm_deriv_le_of_lipschitz`.
- **Used by**: `cpvIntegrandOn_diff_intervalIntegrable`, `analyticRemainder_hasCauchyPVOn_zero`.
- **Visibility**: private.
- **Lines**: 347–368.
- **Notes**: 22 lines.

### `def cpv_badSet`
- **Type**: `(γP : PiecewiseC1Path x x) (S : Finset ℂ) (ε : ℝ) : Set ℝ`
- **What**: Times where γ comes within ε of some pole in `S`: `{t | ∃ s ∈ S, ‖γ(t) − s‖ ≤ ε}`.
- **How**: Direct `setOf` definition.
- **Hypotheses**: none.
- **Uses from project**: `PiecewiseC1Path`.
- **Used by**: `cpv_badSet_isClosed`, `cpv_badSet_measurableSet`, `cpvIntegrandOn_eq_indicator_compl`, `cpvIntegrandOn_diff_intervalIntegrable`, `analyticRemainder_hasCauchyPVOn_zero`, `cpvIntegrandOn_polarPart_intervalIntegrable`.
- **Visibility**: public.
- **Lines**: 371–372.

### `private theorem cpv_badSet_isClosed`
- **Type**: `(γP : PiecewiseC1Path x x) (S : Finset ℂ) (ε : ℝ) : IsClosed (cpv_badSet γP S ε)`
- **What**: The bad set is closed in ℝ.
- **How**: Rewrite as finite union `⋃ s ∈ S, {t | ‖γ(t) - s‖ ≤ ε}`, each closed by continuity of `γ` and `‖·‖`; apply `isClosed_biUnion_finset`.
- **Hypotheses**: none.
- **Uses from project**: `cpv_badSet`, `PiecewiseC1Path`.
- **Used by**: `cpv_badSet_measurableSet`.
- **Visibility**: private.
- **Lines**: 374–384.

### `private theorem cpv_badSet_measurableSet`
- **Type**: `(γP : PiecewiseC1Path x x) (S : Finset ℂ) (ε : ℝ) : MeasurableSet (cpv_badSet γP S ε)`
- **What**: The bad set is measurable.
- **How**: `(cpv_badSet_isClosed …).measurableSet`.
- **Hypotheses**: none.
- **Uses from project**: `cpv_badSet`, `cpv_badSet_isClosed`.
- **Used by**: `cpvIntegrandOn_diff_intervalIntegrable`, `cpvIntegrandOn_polarPart_intervalIntegrable`.
- **Visibility**: private.
- **Lines**: 386–388.

### `theorem cpvIntegrandOn_eq_indicator_compl`
- **Type**: `(γP : PiecewiseC1Path x x) (S : Finset ℂ) (g : ℂ → ℂ) (ε : ℝ) (t : ℝ) : cpvIntegrandOn S g γP.toPath.extend ε t = (cpv_badSet γP S ε)ᶜ.indicator (PiecewiseC1Path.contourIntegrand g γP) t`
- **What**: The CPV cutoff integrand at scale ε equals the indicator on the complement of the bad set of the ordinary contour integrand.
- **How**: Case on `∃ s ∈ S, ‖γ(t) - s‖ ≤ ε`; in each branch unfold the `if` of `cpvIntegrandOn` and the indicator's membership.
- **Hypotheses**: none.
- **Uses from project**: `cpvIntegrandOn`, `cpv_badSet`, `PiecewiseC1Path.contourIntegrand`.
- **Used by**: `cpvIntegrandOn_diff_intervalIntegrable`, `analyticRemainder_hasCauchyPVOn_zero`, `cpvIntegrandOn_polarPart_intervalIntegrable`.
- **Visibility**: public.
- **Lines**: 392–407.

### `theorem cpvIntegrandOn_diff_intervalIntegrable`
- **Type**: `(γ : ClosedPwC1Immersion x) (S : Finset ℂ) {U : Set ℂ} {g : ℂ → ℂ} (h_diff : DifferentiableOn ℂ g U) (hγ_in_U : ∀ t ∈ Icc 0 1, γ.toPwC1Immersion.toPiecewiseC1Path t ∈ U) (ε : ℝ) : IntervalIntegrable (fun t => cpvIntegrandOn S g γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1`
- **What**: CPV cutoff integrand is interval-integrable on `[0,1]` for any ε, when `g` is differentiable on `U` ⊇ γ's image.
- **How**: Realize cutoff as indicator of `(cpv_badSet)ᶜ` (measurable) applied to the full contour integrand (interval-integrable by `contourIntegrand_diff_intervalIntegrable`), then `IntervalIntegrable.indicator`.
- **Hypotheses**: γ closed; `g` differentiable on `U`; γ image in `U`.
- **Uses from project**: `cpvIntegrandOn`, `cpv_badSet`, `cpv_badSet_measurableSet`, `cpvIntegrandOn_eq_indicator_compl`, `contourIntegrand_diff_intervalIntegrable`, `ClosedPwC1Immersion`, `PiecewiseC1Path.contourIntegrand`.
- **Used by**: `analyticRemainder_hasCauchyPVOn_zero`.
- **Visibility**: public.
- **Lines**: 413–432.

### `private theorem cpv_ae_not_mem_S`
- **Type**: `(γ : ClosedPwC1Immersion x) (S : Finset ℂ) : ∀ᵐ t ∂(volume.restrict (Icc 0 1)), γ.toPwC1Immersion.toPiecewiseC1Path t ∉ (↑S : Set ℂ)`
- **What**: Almost every `t ∈ [0,1]` has `γ(t) ∉ S` (a measure-zero exceptional set).
- **How**: Use `volume_preimage_finset_in_Icc01_zero` and `MeasureTheory.measure_mono_null` after rewriting `ae` via `ae_restrict_iff'` and `ae_iff`.
- **Hypotheses**: γ a closed piecewise-`C¹` immersion.
- **Uses from project**: `ClosedPwC1Immersion`, `volume_preimage_finset_in_Icc01_zero`.
- **Used by**: `cpvIntegrandOn_tendsto_contourIntegrand_ae`.
- **Visibility**: private.
- **Lines**: 436–445.

### `theorem cpvIntegrandOn_tendsto_contourIntegrand_ae`
- **Type**: `(γ : ClosedPwC1Immersion x) (S : Finset ℂ) (g : ℂ → ℂ) : ∀ᵐ t ∂(volume.restrict (Ι 0 1)), Tendsto (fun ε => cpvIntegrandOn S g γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) (𝓝[>] 0) (𝓝 (PiecewiseC1Path.contourIntegrand g γ.toPwC1Immersion.toPiecewiseC1Path t))`
- **What**: Pointwise a.e. on `[0,1]`, the cutoff integrands converge to the full contour integrand as `ε → 0⁺`.
- **How**: From `cpv_ae_not_mem_S`, for a.e. `t` we have `δ := min_{s ∈ S} ‖γ(t)-s‖ > 0` (via `Finset.exists_min_image`); for `ε ∈ (0, δ)` the cutoff equals the contour integrand by `cpvIntegrandOn_of_forall_gt`; conclude with `Tendsto.congr' … tendsto_const_nhds`. Empty-S branch handled separately.
- **Hypotheses**: γ closed piecewise-`C¹` immersion.
- **Uses from project**: `cpvIntegrandOn`, `cpv_ae_not_mem_S`, `cpvIntegrandOn_of_forall_gt`, `ClosedPwC1Immersion`, `PiecewiseC1Path.contourIntegrand`.
- **Used by**: `analyticRemainder_hasCauchyPVOn_zero`.
- **Visibility**: public.
- **Lines**: 449–491.
- **Notes**: 43 lines, `classical`.

### `theorem analyticRemainder_hasCauchyPVOn_zero`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) {S : Finset ℂ} (hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ} (γ : ClosedPwC1Immersion x) (h_null : IsNullHomologous γ.toPwC1Immersion U) (decomp : PolarPartDecomposition f S U) : HasCauchyPVOn S decomp.analyticRemainder γ.toPwC1Immersion.toPiecewiseC1Path 0`
- **What**: The Cauchy principal value of the analytic remainder along null-homologous γ is zero, even if γ may cross poles.
- **How**: Apply `intervalIntegral.tendsto_integral_filter_of_dominated_convergence` with bounding function `‖contourIntegrand decomp.analyticRemainder γP‖` (from `contourIntegrand_diff_intervalIntegrable`), the per-ε pointwise bound (indicator ≤ identity), and the a.e. pointwise convergence `cpvIntegrandOn_tendsto_contourIntegrand_ae`. Limit value `0` comes from `analyticRemainder_contourIntegral_zero`.
- **Hypotheses**: `U` open, nonempty; `S ⊆ U`; γ closed null-homologous; `decomp` provided.
- **Uses from project**: `HasCauchyPVOn`, `cpvIntegrandOn`, `cpvIntegrandOn_eq_indicator_compl`, `cpvIntegrandOn_diff_intervalIntegrable`, `cpvIntegrandOn_tendsto_contourIntegrand_ae`, `analyticRemainder_contourIntegral_zero`, `contourIntegrand_diff_intervalIntegrable`, `ClosedPwC1Immersion`, `PolarPartDecomposition`, `IsNullHomologous`, `IsNullHomologous.image_subset`, `PiecewiseC1Path.contourIntegrand`, `cpv_badSet`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 499–547.
- **Notes**: 49 lines, `classical`. Eliminates the `h_rem_cpv` oracle for the crossing-form proof.

### `theorem cpvIntegrandOn_polarPart_intervalIntegrable`
- **Type**: `(γ : ClosedPwC1Immersion x) {U : Set ℂ} {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ} (decomp : PolarPartDecomposition f S U) {s : ℂ} (hs : s ∈ S) (_h_null : IsNullHomologous γ.toPwC1Immersion U) {ε : ℝ} (hε : 0 < ε) : IntervalIntegrable (fun t => cpvIntegrandOn S (decomp.polarPart s) γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1`
- **What**: The CPV cutoff integrand of an individual polar part `decomp.polarPart s` is interval-integrable on `[0,1]` for every ε > 0.
- **How**: 7-step argument: (1) rewrite cutoff as indicator of `(cpv_badSet)ᶜ` applied to contour integrand of `polarPart s`; (2) on `(badSet)ᶜ` polar part equals explicit Laurent sum `laurentSum` (by `polarPart_eq`); (3) bound `‖laurentSum(γ(t))‖ ≤ M_polar = ∑ k ‖a k‖/ε^(k+1)` and `‖γ'‖ ≤ K` (Lipschitz); (4) extend bound to indicator; (5) measurability via `Measurable.const_div ∘ Measurable.pow_const`; (6) AE strongly measurable indicator; (7) `IntegrableOn.of_bound`.
- **Hypotheses**: γ closed, `s ∈ S`, `ε > 0`.
- **Uses from project**: `cpvIntegrandOn`, `cpv_badSet`, `cpv_badSet_measurableSet`, `cpvIntegrandOn_eq_indicator_compl`, `PolarPartDecomposition`, `PolarPartDecomposition.polarPart_eq`, `ClosedPwC1Immersion`, `ClosedPwC1Immersion.lipschitzWith_extend`, `PiecewiseC1Path.contourIntegrand`, `IsNullHomologous`, `norm_deriv_le_of_lipschitz`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 562–677.
- **Notes**: 116 lines, `classical`. Eliminates the `h_polar_int` oracle.

### `theorem residueTheorem_avoidance`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) (S : Finset ℂ) (hS_in_U : ↑S ⊆ U) (f : ℂ → ℂ) (_hf : DifferentiableOn ℂ f (U \ ↑S)) (γ : ClosedPwC1Immersion x) (h_null : IsNullHomologous γ.toPwC1Immersion U) (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc 0 1, γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s) (decomp : PolarPartDecomposition f S U) : HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path (∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s * residue f s)`
- **What**: **Central theorem A** (Hungerbühler–Wasem 3.3, avoidance form): contour integral of `f` along avoiding γ equals `∑ s, 2πi · w(γ,s) · res(f,s)`.
- **How**: Use `avoids_finset_delta_bound` to get uniform avoidance margin δ. Per pole, decompose `polarPart s` via `polarPart_eq`. Sum decomposes by `PiecewiseC1Path.contourIntegral_finset_sum`; higher-order coefficients (`k ≥ 1`) drop by `contourIntegral_higherOrder_eq_zero_of_avoids`; simple-pole coefficient equals `residue f s` via `decomp.residue_eq`. Winding-integral relation `∮ 1/(z-s) = 2πi · w(γ, s)` from `hasCauchyPV_of_avoids` and `generalizedWindingNumber` definition. Analytic remainder contributes zero via `analyticRemainder_contourIntegral_zero`. Finally `hasCauchyPVOn_of_avoids` lifts to CPV statement.
- **Hypotheses**: `U` open, nonempty; `S ⊆ U`; `f` diff on `U \ S`; γ closed null-homologous avoiding `S`; `decomp` provided.
- **Uses from project**: `PolarPartDecomposition`, `PolarPartDecomposition.polarPart_eq`, `PolarPartDecomposition.residue_eq`, `PolarPartDecomposition.decomp`, `HasCauchyPVOn`, `hasCauchyPVOn_of_avoids`, `hasCauchyPV_of_avoids`, `avoids_finset_delta_bound`, `ClosedPwC1Immersion`, `ClosedPwC1Immersion.lipschitzWith_extend`, `PiecewiseC1Path`, `PiecewiseC1Path.contourIntegral`, `PiecewiseC1Path.contourIntegral_finset_sum`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path.contourIntegral_smul`, `PiecewiseC1Path.contourIntegral_add`, `generalizedWindingNumber`, `residue`, `contourIntegral_higherOrder_eq_zero_of_avoids`, `analyticRemainder_contourIntegral_zero`, `IsNullHomologous`, `IsNullHomologous.image_subset`, `norm_deriv_le_of_lipschitz`.
- **Used by**: `residueTheorem_simplePoles_avoidance`, `residueTheorem_convex_avoidance`.
- **Visibility**: public.
- **Lines**: 688–920.
- **Notes**: 233 lines, `classical`. Largest theorem in file. Main "central A" result.

### `noncomputable def PolarPartDecomposition.ofSimplePoles`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) {S : Finset ℂ} (hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U \ ↑S)) (h_simple : ∀ s ∈ S, HasSimplePoleAt f s) : PolarPartDecomposition f S U`
- **What**: Builds a `PolarPartDecomposition` from "every pole is simple": each polar part is `coeff(s)/(z-s)` with `coeff(s) = residue f s`, and the analytic remainder is `f − ∑ res(f,s)/(z-s)`.
- **How**: Set per-pole `c s := (h_simple s _).coeff`; use `residue_eq_coeff_of_hasSimplePoleAt` for `c s = residue f s`. Get analytic extension `g` from `sub_principalPartSum_corrected_differentiableOn` (via `Exists.choose`). Provide structure with `order = 1`, `coeff s _ = c s`, `polarPart s z = c s/(z-s)`; verify `polarPart_eq`, `residue_eq`, `decomp` via `linear_combination`.
- **Hypotheses**: `U` open, `S ⊆ U`, `f` diff on `U \ S`, every `s ∈ S` is a simple pole.
- **Uses from project**: `PolarPartDecomposition`, `HasSimplePoleAt`, `HasSimplePoleAt.coeff`, `residue_eq_coeff_of_hasSimplePoleAt`, `sub_principalPartSum_corrected_differentiableOn`, `principalPartSum`, `residue`.
- **Used by**: `residueTheorem_simplePoles_avoidance`, `residueTheorem_simplePoles_convex_avoidance`.
- **Visibility**: public (`noncomputable def`).
- **Lines**: 927–966.

### `theorem residueTheorem_simplePoles_avoidance`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) (S : Finset ℂ) (hS_in_U : ↑S ⊆ U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S)) (γ : ClosedPwC1Immersion x) (h_null : IsNullHomologous γ.toPwC1Immersion U) (h_simple : ∀ s ∈ S, HasSimplePoleAt f s) (hγ_avoids : …) : HasCauchyPVOn S f … (∑ s ∈ S, 2πi · w(γ,s) · residue f s)`
- **What**: Simple-pole specialization of `residueTheorem_avoidance` — `PolarPartDecomposition` is built automatically from the `HasSimplePoleAt` hypothesis.
- **How**: One-liner: `residueTheorem_avoidance hU_open hU_ne S hS_in_U f hf γ h_null hγ_avoids (PolarPartDecomposition.ofSimplePoles …)`.
- **Hypotheses**: as above + simple poles.
- **Uses from project**: `residueTheorem_avoidance`, `PolarPartDecomposition.ofSimplePoles`, `HasSimplePoleAt`, `ClosedPwC1Immersion`, `IsNullHomologous`, `HasCauchyPVOn`, `generalizedWindingNumber`, `residue`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 975–989.

### `theorem residueTheorem_convex_avoidance`
- **Type**: `{U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty) (S : Finset ℂ) (hS_in_U : ↑S ⊆ U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S)) (γ : ClosedPwC1Immersion x) (hγ_in_U : …) (hγ_avoids : …) (decomp : PolarPartDecomposition f S U) : HasCauchyPVOn S f … (∑ s ∈ S, 2πi · w(γ,s) · residue f s)`
- **What**: Convex-domain corollary: when `U` is convex, null-homology is automatic; higher-order poles allowed via decomposition.
- **How**: One-liner: derive `IsNullHomologous` via `isNullHomologous_of_convex hU_convex hU_open hU_ne γ.toPwC1Immersion hγ_in_U`, then apply `residueTheorem_avoidance`.
- **Hypotheses**: `U` convex/open/nonempty; γ in `U`, avoids `S`; decomposition.
- **Uses from project**: `residueTheorem_avoidance`, `isNullHomologous_of_convex`, `PolarPartDecomposition`, `ClosedPwC1Immersion`, `HasCauchyPVOn`, `generalizedWindingNumber`, `residue`.
- **Used by**: `residueTheorem_simplePoles_convex_avoidance`.
- **Visibility**: public.
- **Lines**: 997–1013.

### `theorem residueTheorem_simplePoles_convex_avoidance`
- **Type**: `{U : Set ℂ} (hU_convex) (hU_open) (hU_ne) (S : Finset ℂ) (hS_in_U) (f) (hf : DifferentiableOn ℂ f (U \ ↑S)) (γ : ClosedPwC1Immersion x) (hγ_in_U) (h_simple : ∀ s ∈ S, HasSimplePoleAt f s) (hγ_avoids) : HasCauchyPVOn S f … (∑ s ∈ S, 2πi · w(γ,s) · residue f s)`
- **What**: Classical residue theorem (textbook form): convex `U`, simple poles, γ avoids poles.
- **How**: One-liner combining `residueTheorem_convex_avoidance` with `PolarPartDecomposition.ofSimplePoles`.
- **Hypotheses**: convex/open/nonempty `U`, simple poles, γ in `U` avoiding `S`.
- **Uses from project**: `residueTheorem_convex_avoidance`, `PolarPartDecomposition.ofSimplePoles`, `HasSimplePoleAt`, `HasCauchyPVOn`, `ClosedPwC1Immersion`, `generalizedWindingNumber`, `residue`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 1020–1036.

---

## File Summary

- **Total declarations**: 18 (1 structure, 2 noncomputable defs + 1 noncomputable constructor `ofSimplePoles`, 1 plain def `cpv_badSet`, 13 theorems — 5 private).
- **Key API**:
  - Data: `PolarPartDecomposition` structure, `PolarPartDecomposition.ofSimplePoles` constructor.
  - Polar-part split: `higherOrderPart`, `simplePolePart`, `polarPart_eq_simplePole_add_higherOrder`, `contourIntegral_higherOrder_eq_zero_of_avoids`, `contourIntegral_higherOrderPart_eq_zero_of_avoids`.
  - Cauchy principal value plumbing: `cpv_badSet`, `cpvIntegrandOn_eq_indicator_compl`, `cpvIntegrandOn_diff_intervalIntegrable`, `cpvIntegrandOn_tendsto_contourIntegrand_ae`, `analyticRemainder_contourIntegral_zero`, `analyticRemainder_hasCauchyPVOn_zero`, `cpvIntegrandOn_polarPart_intervalIntegrable`, `volume_preimage_finset_in_Icc01_zero`.
  - Main theorems: `residueTheorem_avoidance` (central A) + corollaries `residueTheorem_simplePoles_avoidance`, `residueTheorem_convex_avoidance`, `residueTheorem_simplePoles_convex_avoidance`.
- **Unused (in this file)**: `polarPart_eq_simplePole_add_higherOrder`, `contourIntegral_higherOrderPart_eq_zero_of_avoids`, `analyticRemainder_hasCauchyPVOn_zero`, `cpvIntegrandOn_polarPart_intervalIntegrable`, `residueTheorem_simplePoles_avoidance`, `residueTheorem_simplePoles_convex_avoidance`. These are intended for downstream `HungerbuhlerWasem.Crossing` and external API consumers.
- **Sorries**: 0.
- **`set_option`s**: 0.
- **Long proofs (>30 lines)**: `polarPart_eq_simplePole_add_higherOrder` (35), `contourIntegral_higherOrder_eq_zero_of_avoids` (31), `contourIntegral_higherOrderPart_eq_zero_of_avoids` (44), `analyticRemainder_contourIntegral_zero` (69), `cpvIntegrandOn_tendsto_contourIntegrand_ae` (43), `analyticRemainder_hasCauchyPVOn_zero` (49), `cpvIntegrandOn_polarPart_intervalIntegrable` (116), `residueTheorem_avoidance` (233).
- **One-paragraph purpose**: Provides the avoidance-form of the Hungerbühler–Wasem generalized residue theorem (arXiv:1808.00997v2 Theorem 3.3) for a closed piecewise-`C¹` immersion γ null-homologous in an open `U` and avoiding a finite set of poles `S ⊆ U`. The proof packages a meromorphic function's Laurent polar parts at each pole as the `PolarPartDecomposition` data, separates the strictly-higher-order Laurent terms (whose contour integrals vanish via explicit antiderivatives), and reduces the integral to `∑_s 2πi · w(γ,s) · residue(f,s)` plus a vanishing analytic-remainder contribution proved via Dixon's lemma. Auxiliary CPV (Cauchy principal value) infrastructure — `cpv_badSet`, dominated-convergence pointwise convergence, and bounded-cutoff integrability — is also provided so downstream files can eliminate the `h_rem_cpv` / `h_polar_int` oracles in the crossing form. Three named specializations (simple-pole avoidance, convex-domain avoidance, classical textbook simple-pole+convex form) are included as one-line corollaries.
