# Inventory: HW33HigherOrderAvoidance.lean

### `structure PolarPartDecomposition`
- **Type**: `(f : ℂ → ℂ) (S : Finset ℂ) (U : Set ℂ)` with fields `polarPart : ℂ → ℂ → ℂ`, `order : ℂ → ℕ`, `coeff : (s : ℂ) → Fin (order s) → ℂ`, `polarPart_eq`, `residue_eq`, `analyticRemainder : ℂ → ℂ`, `analyticRemainder_diff`, `decomp`.
- **What**: User-supplied polar-part decomposition data for a meromorphic `f` on `U \ S`: per-pole polar part `polarPart s z = ∑ k, coeff s k / (z-s)^(k+1)`, the residue at `s` is `coeff s ⟨0,_⟩`, and `f - Σ polarPart` extends differentiable to all of `U`.
- **How**: Plain structure definition.
- **Hypotheses**: none on the structure itself; the fields encode data + relations.
- **Uses from project**: `residue`
- **Used by**: `hw_3_3_higherOrder_avoidance_paper`
- **Visibility**: public
- **Lines**: 64–84

### `noncomputable def higherOrderPart`
- **Type**: `{N : ℕ} (a : Fin N → ℂ) (s z : ℂ) : ℂ := ∑ k : Fin N, if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0`
- **What**: Higher-order ("k ≥ 1", i.e. order ≥ 2) part of a polar Laurent sum.
- **How**: Definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `polarPart_eq_simplePole_add_higherOrder`, `contourIntegral_higherOrderPart_eq_zero_of_avoids`
- **Visibility**: public, `noncomputable`
- **Lines**: 94–95

### `noncomputable def simplePolePart`
- **Type**: `{N : ℕ} (a : Fin N → ℂ) (s z : ℂ) : ℂ := if h : 0 < N then a ⟨0, h⟩ / (z - s) else 0`
- **What**: Simple-pole ("k = 0") part of a polar Laurent sum.
- **How**: Definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `polarPart_eq_simplePole_add_higherOrder`
- **Visibility**: public, `noncomputable`
- **Lines**: 98–99

### `theorem polarPart_eq_simplePole_add_higherOrder`
- **Type**: `{N : ℕ} (a : Fin N → ℂ) (s z : ℂ) : (∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) = simplePolePart a s z + higherOrderPart a s z`
- **What**: A polar Laurent sum decomposes as `simplePolePart + higherOrderPart`.
- **How**: `by_cases 0 < N`. Positive case: per-`k` split `a k / (z - s)^(k+1) = (if k.val = 0 then a ⟨0,h⟩/(z-s) else 0) + (if k.val ≥ 1 then a k/(z-s)^(k+1) else 0)` (using `Fin.ext` to convert `k.val = 0` to `k = ⟨0,h⟩`), then `Finset.sum_add_distrib` + `Finset.sum_eq_single ⟨0,h⟩` for the `=0` filter. `N = 0` case: empty sum, both pieces zero.
- **Hypotheses**: none.
- **Uses from project**: `simplePolePart`, `higherOrderPart`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 102–136
- **Notes**: 35 lines.

### `theorem contourIntegral_higherOrder_eq_zero_of_avoids`
- **Type**: `{x s : ℂ} (γ : PiecewiseC1Path x x) (h_avoids : ∀ t ∈ Set.Icc (0:ℝ) 1, γ.toPath.extend t ≠ s) {k : ℕ} (hk : 2 ≤ k) (c : ℂ) (h_int : IntervalIntegrable (fun t => c/(γ t - s)^k * deriv γ.toPath.extend t) volume 0 1) : γ.contourIntegral (fun z => c / (z - s) ^ k) = 0`
- **What**: For `k ≥ 2`, the contour integral of `c/(z-s)^k` along any closed path avoiding `s` is zero.
- **How**: Antiderivative `F z = (-c / (k-1)) * (z - s) ^ (-(k - 1 : ℤ))`. Build `HasDerivAt F (c/(z-s)^k) z` for `z ≠ s` via `(hasDerivAt_zpow (-(k-1)) ...).comp z ((hasDerivAt_id z).sub_const s).const_mul`, then `field_simp; ring`. Apply `PiecewiseC1Path.contourIntegral_eq_zero_of_hasDerivAt_of_closed γ rfl hU_img hF h_int`.
- **Hypotheses**: closed γ, avoids `s`, `k ≥ 2`, integrand integrable.
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.contourIntegral`, `PiecewiseC1Path.contourIntegral_eq_zero_of_hasDerivAt_of_closed`
- **Used by**: `contourIntegral_higherOrderPart_eq_zero_of_avoids`, `hw_3_3_higherOrder_avoidance_paper`
- **Visibility**: public
- **Lines**: 143–173
- **Notes**: 31 lines.

### `theorem contourIntegral_higherOrderPart_eq_zero_of_avoids`
- **Type**: `{x s : ℂ} (γ : PiecewiseC1Path x x) (h_avoids : ...) {N : ℕ} (a : Fin N → ℂ) (h_int_each : ∀ k : Fin N, k.val ≥ 1 → IntervalIntegrable ...) : γ.contourIntegral (higherOrderPart a s) = 0`
- **What**: Contour integral of `higherOrderPart a s` along closed γ avoiding `s` is zero.
- **How**: `change` to expose `Σ` form; `contourIntegral_finset_sum` to split; `Finset.sum_eq_zero` term-by-term. Per term: `by_cases hk : k.val ≥ 1` — true branch uses `contourIntegral_higherOrder_eq_zero_of_avoids γ h_avoids hk_ge_2 (a k) (h_int_each k hk)`; false branch reduces integrand to `0` via `if_neg` and applies `PiecewiseC1Path.contourIntegral_zero`.
- **Hypotheses**: closed γ avoiding `s`; each `k≥1` term integrable.
- **Uses from project**: `PiecewiseC1Path`, `higherOrderPart`, `PiecewiseC1Path.contourIntegrand`, `contourIntegral_finset_sum`, `contourIntegral_higherOrder_eq_zero_of_avoids`, `PiecewiseC1Path.contourIntegral_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 180–223
- **Notes**: 44 lines.

### `theorem hw_3_3_higherOrder_avoidance_paper`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) (S : Finset ℂ) (hS_in_U : ↑S ⊆ U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S)) (γ : ClosedPwC1Immersion x) (h_null : IsNullHomologous γ.toPwC1Immersion U) (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0:ℝ) 1, γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s) (decomp : PolarPartDecomposition f S U) : HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path (∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s * residue f s)`
- **What**: **HW Theorem 3.3 — higher-order pole avoidance, paper-faithful.** Cauchy PV of `f` along null-homologous closed γ that avoids every pole equals `Σ 2πi · winding(γ,s) · residue f s`.
- **How**: 
  (1) Bound deriv via `ClosedPwC1Immersion.lipschitzWith_extend` and avoidance distance via `avoids_finset_delta_bound`.
  (2) Per-pole integrability of `coeff s k/(γ-s)^(k+1) · γ'` via `h_deriv_int.continuousOn_mul` (`ContinuousOn.div` with `pow_eq_zero_iff.mp` ruling out denominator zero) for all `k ≥ 1`.
  (3) `h_polarPart_integral`: for each `s ∈ S`, `γP.contourIntegral (decomp.polarPart s) = 2πi·w(γ,s)·residue f s` — rewrite polar-part to Laurent sum on the curve (`decomp.polarPart_eq` via `intervalIntegral.integral_congr`), split via `contourIntegral_finset_sum`. Case `decomp.order s > 0`: `Finset.sum_eq_single_of_mem ⟨0, h_order_pos⟩` kills `k ≥ 1` terms with `contourIntegral_higherOrder_eq_zero_of_avoids`, the remaining `k=0` term gives the winding number via `hasCauchyPV_of_avoids` and the `circleIntegral`-style formula `2πi·w = γP.contourIntegral 1/(z-s)`; rewrite scalar `residue f s = coeff s ⟨0,_⟩` via `decomp.residue_eq` and `dif_pos`. Case `order = 0`: `decomp.residue_eq` gives `residue f s = 0`, empty sum.
  (4) `dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded` applied to `(z - w₀)·decomp.analyticRemainder z` (using `exists_mem_not_mem_path_image_of_isOpen` to find off-curve `w₀ ∈ U`) yields `dixonFunction (· · analyticRemainder) U γP w = 0`; turn into `contourIntegral analyticRemainder = 0` via `contourIntegral_eq_zero_of_nullHomologous_at w₀ ...` and a `(γP t - w₀) · analyticRemainder / (γP t - w₀)` cancellation (`field_simp`).
  (5) Final identity `γP.contourIntegral f = Σ 2πi · w · residue f s`: rewrite the integrand via `decomp.decomp` (using `hγ_in_U`, `hγ_avoids` for `γP t ∈ U \ S`), split with `PiecewiseC1Path.contourIntegral_add` + `contourIntegral_finset_sum`, substitute step (3) and (4). Convert to `HasCauchyPVOn` via `hasCauchyPVOn_of_avoids`.
- **Hypotheses**: `U` open, nonempty; `↑S ⊆ U`; `f` differentiable on `U \ S`; γ closed PwC1 immersion null-homologous in `U`; γ avoids every `s ∈ S`; `PolarPartDecomposition f S U`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.lipschitzWith_extend`, `avoids_finset_delta_bound`, `avoids_delta_bound`, `PolarPartDecomposition`, `PiecewiseC1Path`, `PiecewiseC1Path.contourIntegral`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path.contourIntegral_add`, `PiecewiseC1Path.contourIntegral_smul`, `contourIntegral_finset_sum`, `contourIntegral_higherOrder_eq_zero_of_avoids`, `generalizedWindingNumber`, `hasCauchyPV_of_avoids`, `dixonFunction`, `dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded`, `IsNullHomologous`, `IsNullHomologous.winding_zero_nhds_of_not_mem_of_closed`, `IsNullHomologous.image_subset`, `contourIntegral_eq_zero_of_nullHomologous_at`, `hasCauchyPVOn_of_avoids`, `HasCauchyPVOn`, `ForMathlib.exists_mem_not_mem_path_image_of_isOpen`, `norm_deriv_le_of_lipschitz`, `stronglyMeasurable_deriv`, `residue`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 228–499
- **Notes**: ~272-line proof (>30); no sorry, no `set_option`.

## File Summary
HW Theorem 3.3 higher-order pole-avoidance form. Introduces `PolarPartDecomposition` (user-supplied per-pole Laurent data + analytic remainder). Helper definitions `higherOrderPart` / `simplePolePart` and decomposition lemma. Core: `contourIntegral_higherOrder_eq_zero_of_avoids` (single-valued antiderivative kills `k ≥ 2` terms); `contourIntegral_higherOrderPart_eq_zero_of_avoids` (the full higher-order sum). The flagship theorem `hw_3_3_higherOrder_avoidance_paper` combines Dixon (analytic remainder integrates to zero on null-homologous γ) with term-by-term residue extraction to give `Σ 2πi·w(γ,s)·residue f s`. 0 sorry, no `set_option`.
