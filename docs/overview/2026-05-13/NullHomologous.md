# NullHomologous.lean — Inventory

### `structure IsNullHomologous`
- **Type**: `(γ : PwC1Immersion x x) (U : Set ℂ) : Prop`
- **What**: Predicate stating a closed piecewise-`C¹` immersion `γ` is null-homologous in an open set `U`: its image lies in `U` and its generalized winding number is `0` at every point outside `U`.
- **How**: Two fields: `image_subset` (γ stays in `U`) and `winding_zero` (winding vanishes off `U`).
- **Hypotheses**: a closed (start = end) immersion `γ`, a set `U`
- **Uses from project**: `PwC1Immersion`, `PiecewiseC1Path.toPiecewiseC1Path`, `generalizedWindingNumber`
- **Used by**: `IsNullHomologous.closed`, `IsNullHomologous.mono`, `IsNullHomologous.winding_zero_nhds_of_not_mem_closure`, `IsNullHomologous.winding_eventually_zero_cocompact_of_bounded`, `IsNullHomologous.winding_zero_nhds_of_not_mem_of_closed`, `isNullHomologous_of_convex`
- **Visibility**: public
- **Lines**: 57-62
- **Notes**: none

### `theorem IsNullHomologous.closed`
- **Type**: `{γ : PwC1Immersion x x} {U : Set ℂ} (_h : IsNullHomologous γ U) : γ.toPiecewiseC1Path.IsClosed`
- **What**: The underlying path is closed (trivially, since `x = x`).
- **How**: `:= rfl`.
- **Hypotheses**: an `IsNullHomologous` certificate (unused)
- **Uses from project**: `IsNullHomologous`, `PwC1Immersion`, `PiecewiseC1Path.toPiecewiseC1Path`, `PiecewiseC1Path.IsClosed`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 67-69
- **Notes**: none

### `theorem IsNullHomologous.mono`
- **Type**: `{γ : PwC1Immersion x x} {U V : Set ℂ} (h : IsNullHomologous γ U) (hUV : U ⊆ V) : IsNullHomologous γ V`
- **What**: Monotonicity: if `γ` is null-homologous in `U` and `U ⊆ V`, then `γ` is null-homologous in `V`.
- **How**: New structure: `image_subset` transports via `hUV`; `winding_zero` lifts using `(fun hmem => hz (hUV hmem))`.
- **Hypotheses**: null-homology in `U`; `U ⊆ V`
- **Uses from project**: `IsNullHomologous`, `PwC1Immersion`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 73-76
- **Notes**: none

### `theorem avoids_delta_bound`
- **Type**: `(γ : PiecewiseC1Path x x) (z₀ : ℂ) (h_avoids : ∀ t ∈ Icc 0 1, γ t ≠ z₀) : ∃ δ > 0, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - z₀‖`
- **What**: A continuous path avoiding a point has a positive distance bound to that point.
- **How**: The image of `[0,1]` under `γ.toPath.extend` is compact and nonempty; `z₀` is not in the image, so `IsCompact.isClosed.notMem_iff_infDist_pos` gives `0 < infDist z₀ (image)`. Use `Metric.infDist_le_dist_of_mem` plus `Complex.dist_eq` and `norm_sub_rev` for the bound. 14-line proof; key lemmas `IsCompact.image`, `IsClosed.notMem_iff_infDist_pos`, `Metric.infDist_le_dist_of_mem`.
- **Hypotheses**: γ avoids `z₀` on `[0,1]`
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.toPath`
- **Used by**: `avoids_finset_delta_bound`, `isNullHomologous_of_convex`
- **Visibility**: public
- **Lines**: 81-95
- **Notes**: 15 lines

### `theorem avoids_finset_delta_bound`
- **Type**: `(γ : PiecewiseC1Path x x) (S : Finset ℂ) (h_avoids : ∀ s ∈ S, ∀ t ∈ Icc 0 1, γ t ≠ s) : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s‖`
- **What**: Iterates `avoids_delta_bound` over a finite set to get a single positive distance bound.
- **How**: `Finset.induction_on`: base case `δ = 1`; insert step uses `min δ_T δ_a` from the IH and a fresh `avoids_delta_bound` for `a`. 18-line proof; key lemma `Finset.induction_on`.
- **Hypotheses**: γ avoids every point of `S`
- **Uses from project**: `avoids_delta_bound`, `PiecewiseC1Path`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 99-116
- **Notes**: 18 lines

### `private theorem contourIntegral_inv_eq_zero_of_convex`
- **Type**: `{U : Set ℂ} (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty) (γ : PiecewiseC1Path x x) (hγ : ∀ t ∈ Icc 0 1, γ t ∈ U) (z : ℂ) (hz : z ∉ U) : γ.contourIntegral (fun w => (w - z)⁻¹) = 0`
- **What**: For a closed piecewise-`C¹` path in a convex open set avoiding `z`, the contour integral of `(w - z)⁻¹` is zero.
- **How**: Case on integrability. If integrable: `w ↦ (w - z)⁻¹` is holomorphic on `U`; `hasPrimitive_of_convex` gives a primitive `F`, then `PiecewiseC1Path.contourIntegral_eq_zero_of_hasDerivAt_of_closed` closes via FTC telescope. If not integrable: `intervalIntegral.integral_undef` gives `0` by convention. 13-line proof; key lemmas `hasPrimitive_of_convex`, `contourIntegral_eq_zero_of_hasDerivAt_of_closed`, `integral_undef`.
- **Hypotheses**: convex open nonempty `U`, γ in `U`, `z ∉ U`
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.contourIntegral`, `PiecewiseC1Path.contourIntegral_eq_zero_of_hasDerivAt_of_closed`, `DifferentiableOn.hasPrimitive_of_convex`
- **Used by**: `isNullHomologous_of_convex`
- **Visibility**: private
- **Lines**: 125-142
- **Notes**: 18 lines

### `theorem IsNullHomologous.winding_zero_nhds_of_not_mem_closure`
- **Type**: `{γ : PwC1Immersion x x} {U : Set ℂ} (h_null : IsNullHomologous γ U) {w : ℂ} (hw : w ∉ closure U) : ∃ ε > 0, ∀ w' ∈ Metric.ball w ε, generalizedWindingNumber γ.toPiecewiseC1Path w' = 0`
- **What**: **B-1 weak**: If `γ` is null-homologous in `U` and `w ∉ closure U`, then winding vanishes throughout some ball around `w`.
- **How**: `(closure U)ᶜ` is open; `Metric.isOpen_iff.mp` produces an ε-ball in `(closure U)ᶜ`; for each `w'` in the ball, `w' ∉ U` (since ball ⊆ (closure U)ᶜ ⊆ Uᶜ), so `h_null.winding_zero` applies.
- **Hypotheses**: null-homology; `w ∉ closure U`
- **Uses from project**: `IsNullHomologous`, `PwC1Immersion`, `PiecewiseC1Path.toPiecewiseC1Path`, `generalizedWindingNumber`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 157-166
- **Notes**: none

### `theorem IsNullHomologous.winding_eventually_zero_cocompact_of_bounded`
- **Type**: `{γ : PwC1Immersion x x} {U : Set ℂ} (h_null : IsNullHomologous γ U) (hU_bounded : Bornology.IsBounded U) : ∀ᶠ w in Filter.cocompact ℂ, (∀ t ∈ Icc 0 1, γ.toPiecewiseC1Path t ≠ w) ∧ generalizedWindingNumber γ.toPiecewiseC1Path w = 0`
- **What**: **B-1 cocompact**: For `γ` null-homologous in a bounded `U`, eventually (in cocompact) `γ` avoids `w` and winding `= 0`.
- **How**: `Uᶜ ∈ cocompact ℂ` via `Metric.cobounded_eq_cocompact` and `Bornology.isBounded_def`. `filter_upwards [h_compl]` and apply image-avoidance from `h_null.image_subset` plus `h_null.winding_zero`.
- **Hypotheses**: null-homology; `U` bounded
- **Uses from project**: `IsNullHomologous`, `PwC1Immersion`, `PiecewiseC1Path.toPiecewiseC1Path`, `generalizedWindingNumber`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 173-184
- **Notes**: 12 lines

### `lemma lipschitzWith_norm_bound_on_Icc01`
- **Type**: `{x : ℂ} {γ : PwC1Immersion x x} {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) (t : ℝ) (ht : t ∈ Icc 0 1) : ‖γ.toPath.extend t‖ ≤ ‖γ.toPath.extend 0‖ + (K : ℝ)`
- **What**: A Lipschitz path on `[0,1]` has its image norm bounded by `‖γ(0)‖ + K`.
- **How**: `dist t 0 ≤ 1` from `ht`; Lipschitz gives `dist (γ t) (γ 0) ≤ K`; then `‖γ t‖ ≤ ‖γ 0‖ + ‖γ t - γ 0‖ ≤ ‖γ 0‖ + K` via `norm_add_le`. 20-line proof; key lemma `LipschitzWith.dist_le_mul`.
- **Hypotheses**: γ Lipschitz with constant `K`; `t ∈ [0,1]`
- **Uses from project**: `PwC1Immersion`
- **Used by**: `generalizedWindingNumber_eq_zero_of_far_lipschitz`, `winding_eventually_zero_cocompact_of_lipschitz`
- **Visibility**: public
- **Lines**: 190-212
- **Notes**: 23 lines

### `private lemma contourIntegral_inv_norm_le_of_far`
- **Type**: `{x : ℂ} {γ : PiecewiseC1Path x x} {R M_d : ℝ} (hR : ∀ t ∈ Icc 0 1, ‖γ.toPath.extend t‖ ≤ R) (hM_d : ∀ t ∈ Icc 0 1, ‖deriv γ.toPath.extend t‖ ≤ M_d) {w : ℂ} (hw : R < ‖w‖) : ‖γ.contourIntegral (fun z => (z - w)⁻¹)‖ ≤ M_d / (‖w‖ - R)`
- **What**: Contour integral of `(z - w)⁻¹` along γ inside a ball of radius `R` is bounded by `M_d / (‖w‖ - R)` whenever `‖w‖ > R`.
- **How**: Distance lower bound `‖w‖ - R ≤ ‖γ t - w‖` from reverse triangle. Pointwise norm bound on `(γ t - w)⁻¹ * γ'(t)` via `inv_anti₀`. Apply `intervalIntegral.norm_integral_le_of_norm_le_const` with constant `M_d / (‖w‖ - R)`. 25-line proof; key lemmas `inv_anti₀`, `intervalIntegral.norm_integral_le_of_norm_le_const`.
- **Hypotheses**: γ inside ball of radius `R`; derivative bounded by `M_d`; `R < ‖w‖`
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.contourIntegral`
- **Used by**: `generalizedWindingNumber_eq_zero_of_far_lipschitz`
- **Visibility**: private
- **Lines**: 219-256
- **Notes**: 38 lines

### `theorem generalizedWindingNumber_eq_zero_of_far_lipschitz`
- **Type**: `{x : ℂ} {γ : PwC1Immersion x x} {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) {w : ℂ} (hw : ‖γ.toPath.extend 0‖ + (K : ℝ) + (K : ℝ) / (2 * Real.pi) < ‖w‖) : generalizedWindingNumber γ.toPiecewiseC1Path w = 0`
- **What**: For a Lipschitz closed piecewise-`C¹` immersion γ, the generalized winding number around `w` is `0` whenever `‖w‖` exceeds `‖γ(0)‖ + K + K/(2π)`.
- **How**: Set `R = ‖γ(0)‖ + K`. Then `R < ‖w‖`. γ stays in ball of radius `R` via `lipschitzWith_norm_bound_on_Icc01`. γ' bounded by `K` via `norm_deriv_le_of_lipschitz`. δ-bound via reverse triangle. Get integer `n` with winding `= n` from `hasGeneralizedWindingNumber_integer_of_closed`. `HasCauchyPV` of `(z - w)⁻¹` exists by avoidance; Tendsto uniqueness yields contour integral `= 2πi · n`. Bound via `contourIntegral_inv_norm_le_of_far`: `2π · |n| ≤ K/(‖w‖ - R) < 2π`. Hence `|n| < 1`, forcing `n = 0`. 95-line proof; key lemmas `hasGeneralizedWindingNumber_integer_of_closed`, `hasCauchyPV_of_avoids`, `tendsto_nhds_unique`, `intervalIntegrable_div_lipschitz`, `contourIntegral_inv_norm_le_of_far`.
- **Hypotheses**: γ Lipschitz; `‖w‖ > ‖γ(0)‖ + K + K/(2π)`
- **Uses from project**: `PwC1Immersion`, `PiecewiseC1Path.toPiecewiseC1Path`, `PiecewiseC1Path.contourIntegral`, `lipschitzWith_norm_bound_on_Icc01`, `norm_deriv_le_of_lipschitz`, `intervalIntegrable_div_lipschitz`, `hasGeneralizedWindingNumber_integer_of_closed`, `hasCauchyPV_of_avoids`, `HasCauchyPV`, `generalizedWindingNumber`, `contourIntegral_inv_norm_le_of_far`
- **Used by**: `winding_eventually_zero_cocompact_of_lipschitz`, `IsNullHomologous.winding_zero_nhds_of_not_mem_of_closed` (indirectly via locally const)
- **Visibility**: public
- **Lines**: 264-358
- **Notes**: 95 lines

### `theorem winding_eventually_zero_cocompact_of_lipschitz`
- **Type**: `{x : ℂ} {γ : PwC1Immersion x x} {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) : ∀ᶠ w in Filter.cocompact ℂ, (∀ t ∈ Icc 0 1, γ.toPiecewiseC1Path t ≠ w) ∧ generalizedWindingNumber γ.toPiecewiseC1Path w = 0`
- **What**: **Lipschitz analog** of `winding_eventually_zero_cocompact_of_bounded`: for Lipschitz γ, the avoid-and-winding-zero conjunction holds eventually in cocompact ℂ — no boundedness of `U` required.
- **How**: Define `RR := ‖γ(0)‖ + K + K/(2π)`; the set `{w : ‖w‖ > RR}` is in `cocompact ℂ` (complement of closed ball is compact-complement). For each such `w`: γ-avoidance via `hR_bound`; winding zero via `generalizedWindingNumber_eq_zero_of_far_lipschitz`. 25-line proof.
- **Hypotheses**: γ Lipschitz with `K`
- **Uses from project**: `PwC1Immersion`, `PiecewiseC1Path.toPiecewiseC1Path`, `lipschitzWith_norm_bound_on_Icc01`, `generalizedWindingNumber_eq_zero_of_far_lipschitz`, `generalizedWindingNumber`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 368-398
- **Notes**: 31 lines

### `theorem IsNullHomologous.winding_zero_nhds_of_not_mem_of_closed`
- **Type**: `{γ : PwC1Immersion x x} {U : Set ℂ} (h_null : IsNullHomologous γ U) {w : ℂ} (hw : w ∉ U) (h_avoid : ∀ t ∈ Icc 0 1, γ.toPiecewiseC1Path t ≠ w) {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) : ∃ ε > 0, ∀ w' ∈ Metric.ball w ε, generalizedWindingNumber γ.toPiecewiseC1Path w' = 0`
- **What**: **B-1 full**: For Lipschitz null-homologous γ and `w ∉ U` with γ avoiding `w`, winding vanishes on a whole neighborhood of `w`. Works even when `w ∈ closure U \ U`.
- **How**: Use `Complex.generalizedWindingNumber_locally_const_of_closed` to get an ε such that winding is constant on `ball w ε`; combine with `h_null.winding_zero w hw` to get winding = 0 throughout.
- **Hypotheses**: null-homology; `w ∉ U`; γ avoids `w`; γ Lipschitz
- **Uses from project**: `IsNullHomologous`, `PwC1Immersion`, `PiecewiseC1Path.toPiecewiseC1Path`, `Complex.generalizedWindingNumber_locally_const_of_closed`, `generalizedWindingNumber`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 409-421
- **Notes**: none

### `theorem isNullHomologous_of_convex`
- **Type**: `{U : Set ℂ} (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty) (γ : PwC1Immersion x x) (hγ : ∀ t ∈ Icc 0 1, γ.toPiecewiseC1Path t ∈ U) : IsNullHomologous γ U`
- **What**: Every closed piecewise-`C¹` immersion in a convex open set is null-homologous.
- **How**: `image_subset := hγ`. For `winding_zero`: for `z ∉ U`, γ avoids `z`; use `avoids_delta_bound` for a δ-bound; reduce winding to contour integral via `hasGeneralizedWindingNumber_of_avoids`; apply `contourIntegral_inv_eq_zero_of_convex` to make contour integral 0; finish with `mul_zero`.
- **Hypotheses**: convex open nonempty `U`; γ in `U`
- **Uses from project**: `IsNullHomologous`, `PwC1Immersion`, `PiecewiseC1Path.toPiecewiseC1Path`, `avoids_delta_bound`, `hasGeneralizedWindingNumber_of_avoids`, `contourIntegral_inv_eq_zero_of_convex`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 431-445
- **Notes**: 15 lines

## File Summary

- **Total declarations**: 14 (1 structure, 11 theorems, 2 private lemmas/theorems)
- **Purpose**: Defines the **null-homologous** predicate `IsNullHomologous γ U` for closed piecewise-`C¹` immersions and proves the key facts: monotonicity in `U`, vanishing of winding in neighborhoods of exterior points (weak and full forms), cocompact-eventually vanishing, and the fundamental construction that convex domains yield null-homologous closed paths. This is the topological backbone for the Hungerbuhler-Wasem generalized residue theorem.
- **Imports used**: `GeneralizedWindingNumber` (`generalizedWindingNumber`, `hasGeneralizedWindingNumber_of_avoids`, `hasGeneralizedWindingNumber_integer_of_closed`, `hasCauchyPV_of_avoids`, `HasCauchyPV`, `intervalIntegrable_div_lipschitz`), `PoincareBridge` (`Complex.generalizedWindingNumber_locally_const_of_closed`), `CurveUtilities` (`PwC1Immersion`, `PiecewiseC1Path`, `contourIntegral_eq_zero_of_hasDerivAt_of_closed`, `norm_deriv_le_of_lipschitz`, `hasPrimitive_of_convex`), `WindingArgDiff`
- **External dependencies**: `Metric.infDist`, `IsCompact.isClosed.notMem_iff_infDist_pos`, `LipschitzWith.dist_le_mul`, `intervalIntegral.norm_integral_le_of_norm_le_const`, `Filter.cocompact`, `Metric.cobounded_eq_cocompact`
- **No sorries, no axioms, no `set_option`**.
- **Architecture**: Five logical groups: definition (`IsNullHomologous`); basic properties (`closed`, `mono`); auxiliary distance bounds (`avoids_delta_bound`, `avoids_finset_delta_bound`); neighborhood-vanishing of winding (`winding_zero_nhds_of_not_mem_closure`, cocompact-bounded form, Lipschitz "far-from-γ" inequality, `winding_eventually_zero_cocompact_of_lipschitz`, full `winding_zero_nhds_of_not_mem_of_closed`); convex domain construction (`isNullHomologous_of_convex`).
