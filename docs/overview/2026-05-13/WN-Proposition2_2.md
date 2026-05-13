# Inventory: Proposition2_2.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/WindingNumber/Proposition2_2.lean`

Imports: `ClassicalCPV`, `OnCurvePV.Basic`, mathlib topology/calculus.

### `private lemma HasDerivAt.re'`
- **Type**: `{f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) → HasDerivAt (fun t => (f t).re) f'.re x`
- **What**: The real-part projection of a complex-valued differentiable function is differentiable with derivative equal to the real part of the original derivative.
- **How**: Composition `Complex.reCLM.hasFDerivAt.comp_hasDerivAt`.
- **Hypotheses**: `f` has derivative `f'` at `x`.
- **Uses from project**: []
- **Used by**: `PiecewiseC1Immersion.eventually_ne_left_of_partition`, `PiecewiseC1Immersion.eventually_ne_right_of_partition`
- **Visibility**: private
- **Lines**: 46-48
- **Notes**: short, none

### `private lemma eventually_not_in_partition_left`
- **Type**: `(γ : PiecewiseC1Immersion) (p : ℝ) → ∀ᶠ t in 𝓝[<] p, t ∉ γ.toPiecewiseC1Curve.partition`
- **What**: Sufficiently close to `p` from the left, parameters do not lie in the partition (which is finite and hence closed).
- **How**: `partition \ {p}` is closed and `p` lies in its complement; combine with `t < p` filter via `Filter.Eventually.mono`.
- **Hypotheses**: `γ : PiecewiseC1Immersion`, `p : ℝ`.
- **Uses from project**: `PiecewiseC1Immersion.toPiecewiseC1Curve` (and its `partition` field).
- **Used by**: `PiecewiseC1Immersion.eventually_ne_left_of_partition`
- **Visibility**: private
- **Lines**: 53-65
- **Notes**: none

### `private lemma eventually_not_in_partition_right`
- **Type**: `(γ : PiecewiseC1Immersion) (p : ℝ) → ∀ᶠ t in 𝓝[>] p, t ∉ γ.toPiecewiseC1Curve.partition`
- **What**: Right-sided analogue of the left version: parameters close to `p` from the right avoid the partition.
- **How**: Same argument as the left version, swapping `Ioi/Iio` and direction of `<`.
- **Hypotheses**: `γ : PiecewiseC1Immersion`, `p : ℝ`.
- **Uses from project**: `PiecewiseC1Immersion.toPiecewiseC1Curve` (partition).
- **Used by**: `PiecewiseC1Immersion.eventually_ne_right_of_partition`
- **Visibility**: private
- **Lines**: 67-79
- **Notes**: none

### `theorem PiecewiseC1Immersion.eventually_ne_at_smooth_crossing`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc γ.a γ.b) (hcross : γ.toFun t₀ = z₀) (hsmooth : t₀ ∉ γ.toPiecewiseC1Curve.partition) → ∀ᶠ t in 𝓝[≠] t₀, γ.toFun t ≠ z₀`
- **What**: At a smooth crossing point, the curve avoids `z₀` on a punctured neighborhood of `t₀`.
- **How**: One-liner: `HasDerivAt.eventually_ne` applied to nonzero derivative from `γ.deriv_ne_zero`.
- **Hypotheses**: `γ` piecewise C¹ immersion, `t₀ ∈ [a,b]`, `γ(t₀)=z₀`, `t₀` not in partition.
- **Uses from project**: `PiecewiseC1Immersion.smooth_off_partition`, `PiecewiseC1Immersion.deriv_ne_zero`.
- **Used by**: `PiecewiseC1Immersion.crossing_isolated_nhds`
- **Visibility**: public
- **Lines**: 85-92
- **Notes**: none

### `theorem PiecewiseC1Immersion.eventually_ne_left_of_partition`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (p : ℝ) (hp : p ∈ γ.toPiecewiseC1Curve.partition) (hap : γ.a < p) (hpb : p ≤ γ.b) (hcross : γ.toFun p = z₀) → ∀ᶠ t in 𝓝[<] p, γ.toFun t ≠ z₀`
- **What**: At a partition point `p` with `a < p`, the one-sided left limit of the derivative is nonzero, so `γ(t) ≠ γ(p)` for `t` just below `p`.
- **How**: KEY: build `h(t) = Re(conj(L) · (γ(t) - z₀))`; show `h` is strictly monotone on `[q,p]` via `strictMonoOn_of_deriv_pos` (using `HasDerivAt.re'` and `h_lim_val : Re(conj L · L) = ‖L‖²`); thus `h(t) < h(p) = 0`, contradicting `h(t)=0` if `γ(t)=z₀`.
- **Hypotheses**: `p ∈ partition`, `a < p ≤ b`, `γ(p)=z₀`.
- **Uses from project**: `PiecewiseC1Immersion.left_deriv_limit`, `eventually_not_in_partition_left`, `HasDerivAt.re'`, `PiecewiseC1Immersion.smooth_off_partition`.
- **Used by**: `PiecewiseC1Immersion.crossing_isolated_nhds`
- **Visibility**: public
- **Lines**: 98-152
- **Notes**: >30 lines

### `theorem PiecewiseC1Immersion.eventually_ne_right_of_partition`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (p : ℝ) (hp : p ∈ γ.toPiecewiseC1Curve.partition) (hap : γ.a ≤ p) (hpb : p < γ.b) (hcross : γ.toFun p = z₀) → ∀ᶠ t in 𝓝[>] p, γ.toFun t ≠ z₀`
- **What**: Right-sided analogue: at a partition point `p < b`, the curve avoids `z₀` for `t` just above `p`.
- **How**: Mirror of left version using `right_deriv_limit`; same `h(t) = Re(conj(L)·(γ(t)-z₀))` strict monotonicity argument via `strictMonoOn_of_deriv_pos`.
- **Hypotheses**: `p ∈ partition`, `a ≤ p < b`, `γ(p)=z₀`.
- **Uses from project**: `PiecewiseC1Immersion.right_deriv_limit`, `eventually_not_in_partition_right`, `HasDerivAt.re'`, `PiecewiseC1Immersion.smooth_off_partition`.
- **Used by**: `PiecewiseC1Immersion.crossing_isolated_nhds`
- **Visibility**: public
- **Lines**: 156-209
- **Notes**: >30 lines

### `theorem PiecewiseC1Immersion.crossing_isolated_nhds`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc γ.a γ.b) (hcross : γ.toFun t₀ = z₀) → ∀ᶠ t in 𝓝[≠] t₀, γ.toFun t ≠ z₀ ∨ t ∉ Icc γ.a γ.b`
- **What**: At any crossing, there is a punctured neighborhood where the curve either avoids `z₀` or exits `[a,b]`.
- **How**: Case split on `t₀ ∈ partition`. Smooth case: `eventually_ne_at_smooth_crossing`. Partition case: split via `punctured_nhds_eq_nhdsWithin_sup_nhdsWithin`, then handle each side using `eventually_ne_left/right_of_partition` or the trivial endpoint case.
- **Hypotheses**: `t₀ ∈ [a,b]`, `γ(t₀)=z₀`.
- **Uses from project**: `PiecewiseC1Immersion.eventually_ne_at_smooth_crossing`, `PiecewiseC1Immersion.eventually_ne_left_of_partition`, `PiecewiseC1Immersion.eventually_ne_right_of_partition`.
- **Used by**: `PiecewiseC1Immersion.crossing_not_accPt`, `exists_isolated_crossing_interval`
- **Visibility**: public
- **Lines**: 215-246
- **Notes**: >30 lines

### `theorem PiecewiseC1Immersion.crossing_not_accPt`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc γ.a γ.b) (hcross : γ.toFun t₀ = z₀) → ¬AccPt t₀ (𝓟 {t ∈ Icc γ.a γ.b | γ.toFun t = z₀})`
- **What**: No crossing point is an accumulation point of the crossing set.
- **How**: Translate `AccPt` via `accPt_iff_frequently_nhdsNE`; the eventual isolation from `crossing_isolated_nhds` directly contradicts the eventually-not-frequently structure.
- **Hypotheses**: `t₀ ∈ [a,b]`, `γ(t₀)=z₀`.
- **Uses from project**: `PiecewiseC1Immersion.crossing_isolated_nhds`.
- **Used by**: `finite_crossings`
- **Visibility**: public
- **Lines**: 249-258
- **Notes**: none

### `theorem crossing_set_isClosed`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) → IsClosed {t ∈ Icc γ.a γ.b | γ.toFun t = z₀}`
- **What**: The crossing set is closed in `ℝ`.
- **How**: Rewrite as `Icc ∩ γ⁻¹({z₀})`; apply `Continuous.preimage_isClosed_of_isClosed`.
- **Hypotheses**: γ piecewise C¹ immersion.
- **Uses from project**: `PiecewiseC1Immersion.continuous_toFun`.
- **Used by**: `finite_crossings`
- **Visibility**: public
- **Lines**: 261-267
- **Notes**: none

### `theorem finite_crossings`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) → Set.Finite {t ∈ Icc γ.a γ.b | γ.toFun t = z₀}`
- **What**: Proposition 2.2 (HW): the crossing set is finite.
- **How**: By contradiction. If infinite, then by `Set.Infinite.exists_accPt_of_subset_isCompact` it has an accumulation point in `Icc`; the set is closed so this point lies in it, contradicting `crossing_not_accPt`.
- **Hypotheses**: γ piecewise C¹ immersion.
- **Uses from project**: `crossing_set_isClosed`, `PiecewiseC1Immersion.crossing_not_accPt`.
- **Used by**: `cpv_exists_inv_sub`
- **Visibility**: public
- **Lines**: 272-281
- **Notes**: none

### `theorem exists_isolated_crossing_interval`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = z₀) → ∃ a' b', a' < t₀ ∧ t₀ < b' ∧ Icc a' b' ⊆ Icc γ.a γ.b ∧ (∀ t ∈ Icc a' b', γ.toFun t = z₀ → t = t₀) ∧ (∀ t ∈ Ioo a' b', t ∉ partition → DifferentiableAt ℝ γ.toFun t)`
- **What**: Each interior crossing has an isolating subinterval on which it is the only crossing, with smoothness off the partition.
- **How**: From `crossing_isolated_nhds`, obtain `Ioo l u` with the isolating property; choose `a' = (max l a + t₀)/2`, `b' = (t₀ + min u b)/2`, verify all inclusions via `linarith`/`max_lt`/`lt_min` chains; smoothness from `smooth_off_partition`.
- **Hypotheses**: `t₀ ∈ Ioo a b`, `γ(t₀) = z₀`.
- **Uses from project**: `PiecewiseC1Immersion.crossing_isolated_nhds`, `PiecewiseC1Immersion.smooth_off_partition`.
- **Used by**: `cpv_exists_on_subinterval`
- **Visibility**: public
- **Lines**: 286-331
- **Notes**: >30 lines

### `private lemma continuousAt_deriv_of_contDiffAt_two`
- **Type**: `{f : ℝ → ℂ} {x : ℝ} (h : ContDiffAt ℝ 2 f x) → ContinuousAt (deriv f) x`
- **What**: `C²` regularity at a point implies continuity of the derivative there.
- **How**: Downcast `ContDiffAt ℝ 2 f x` to `ContDiffAt ℝ 1 f x`, obtain an open neighborhood `V` where `f` is `C¹On`, then `ContDiffOn.continuousOn_deriv_of_isOpen` gives continuity of `deriv f` on `V`.
- **Hypotheses**: `ContDiffAt ℝ 2 f x`.
- **Uses from project**: []
- **Used by**: `PiecewiseC1Immersion.deriv_ne_zero_of_C2`
- **Visibility**: private
- **Lines**: 341-351
- **Notes**: none

### `theorem PiecewiseC1Immersion.deriv_ne_zero_of_C2`
- **Type**: `(γ : PiecewiseC1Immersion) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hγ_C2 : ContDiffAt ℝ 2 γ.toFun t₀) → deriv γ.toFun t₀ ≠ 0`
- **What**: Under `C²` at an interior point, the derivative is nonzero (combining `C²` continuity with the one-sided limit at partition points).
- **How**: Case `t₀ ∈ partition`: continuity of `deriv` from `continuousAt_deriv_of_contDiffAt_two` plus `tendsto_nhds_unique` against `right_deriv_limit` show `deriv γ t₀ = L ≠ 0`. Else use `γ.deriv_ne_zero`.
- **Hypotheses**: `t₀ ∈ Ioo a b`, `C² γ` at `t₀`.
- **Uses from project**: `continuousAt_deriv_of_contDiffAt_two`, `PiecewiseC1Immersion.right_deriv_limit`, `PiecewiseC1Immersion.deriv_ne_zero`.
- **Used by**: `cpv_exists_single_crossing`
- **Visibility**: public
- **Lines**: 353-366
- **Notes**: none

### `theorem cpv_exists_single_crossing`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (a' b' t₀ : ℝ) (hat₀ : t₀ ∈ Ioo a' b') (hcross : γ.toFun t₀ = z₀) (h_sub : Icc a' b' ⊆ Icc γ.a γ.b) (h_inj : ∀ t ∈ Icc a' b', γ.toFun t = z₀ → t = t₀) (hγ_C2 : ContDiffAt ℝ 2 γ.toFun t₀) (h_cont_deriv : ContinuousOn (deriv γ.toFun) (Icc a' b')) (hγ_meas : Measurable γ.toFun) → CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun a' b' z₀`
- **What**: CPV of `(z - z₀)⁻¹` exists on a subinterval containing exactly one crossing.
- **How**: Build `Ioo γ.a γ.b` membership of `t₀`; show derivative nonzero via `deriv_ne_zero_of_C2`; apply `pv_limit_via_dyadic` (KEY external) to obtain a limit; transfer the integrand via `intervalIntegral.integral_congr`.
- **Hypotheses**: `t₀` unique crossing in `[a',b']`, `C²` at `t₀`, deriv continuous on `[a',b']`, γ measurable.
- **Uses from project**: `PiecewiseC1Immersion.deriv_ne_zero_of_C2`, `pv_limit_via_dyadic`, `CauchyPrincipalValueExists'`.
- **Used by**: `cpv_exists_on_subinterval`
- **Visibility**: public
- **Lines**: 373-397
- **Notes**: none

### `theorem cpv_integrand_intervalIntegrable`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (c d : ℝ) (hcd : c ≤ d) (h_sub : Icc c d ⊆ Icc γ.a γ.b) (ε : ℝ) (hε : 0 < ε) → IntervalIntegrable (fun t => if ε < ‖γ.toFun t - z₀‖ then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0) volume c d`
- **What**: The ε-cutoff Cauchy integrand for `(z - z₀)⁻¹` is interval-integrable along the piecewise C¹ immersion.
- **How**: KEY: the integrand is uniformly bounded by `ε⁻¹·D` (via `piecewiseC1Immersion_deriv_bounded`); measurable-set machinery decomposes the integrand as a piecewise function on `({‖γ-z₀‖>ε}∩Icc) \ partition` (where it's continuous via product rule and `inv₀` away from zero) plus a measure-zero part on `partition`; then `IntegrableOn.of_bound` and conversion to `IntervalIntegrable`.
- **Hypotheses**: `c ≤ d`, `Icc c d ⊆ Icc a b`, `0 < ε`.
- **Uses from project**: `piecewiseC1Immersion_deriv_bounded`, `measurableSet_norm_gt_Icc`, `PiecewiseC1Curve.deriv_continuous_off_partition`, `PiecewiseC1Curve.endpoints_in_partition`, `PiecewiseC1Immersion.continuous_toFun`, `PiecewiseC1Immersion.partition`.
- **Used by**: `cpv_exists_on_subinterval`
- **Visibility**: public
- **Lines**: 403-497
- **Notes**: >30 lines

### `private theorem cpv_avoidance_sub`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (c d : ℝ) (hcd : c ≤ d) (h_sub : Icc c d ⊆ Icc γ.a γ.b) (h_avoid : ∀ t ∈ Icc c d, γ.toFun t ≠ z₀) → CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun c d z₀`
- **What**: CPV exists on any subinterval with no crossings.
- **How**: Direct application of external `cpv_avoidance` lemma.
- **Hypotheses**: `c ≤ d`, `Icc c d ⊆ Icc a b`, γ avoids `z₀` on `[c,d]`.
- **Uses from project**: `cpv_avoidance`, `PiecewiseC1Immersion.continuous_toFun`.
- **Used by**: `cpv_exists_on_subinterval`
- **Visibility**: private
- **Lines**: 501-506
- **Notes**: none

### `private theorem cpv_exists_on_subinterval`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (hγ_meas : Measurable γ.toFun) (n : ℕ) (c d : ℝ) (hcd : c ≤ d) (h_sub : Icc c d ⊆ Icc γ.a γ.b) (h_no_endpt : γ.toFun c ≠ z₀ ∧ γ.toFun d ≠ z₀) (h_fin_cd : Set.Finite {t ∈ Icc c d | γ.toFun t = z₀}) (h_card : h_fin_cd.toFinset.card ≤ n) (hC2 : ...) (h_cont_deriv_cross : ...) → CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun c d z₀`
- **What**: Recursive CPV existence on `[c,d]` by induction on the cardinal bound `n` of the crossing set.
- **How**: KEY: induction on `n`. Base case: no crossings, apply `cpv_avoidance_sub`. Step: pick a crossing `t₁`, use `exists_isolated_crossing_interval` to get an isolating window, apply `cpv_exists_single_crossing` on the middle and IH on left/right, then stitch via `cpv_concat` using `cpv_integrand_intervalIntegrable` for integrability.
- **Hypotheses**: γ measurable, crossings counted in `n`, no endpoint crossings, C² + continuous derivative at each crossing.
- **Uses from project**: `cpv_avoidance_sub`, `exists_isolated_crossing_interval`, `cpv_exists_single_crossing`, `cpv_concat`, `cpv_integrand_intervalIntegrable`.
- **Used by**: `cpv_exists_inv_sub`
- **Visibility**: private
- **Lines**: 514-649
- **Notes**: >30 lines

### `theorem cpv_exists_inv_sub`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (hγ_meas : Measurable γ.toFun) (h_no_endpt : γ.toFun γ.a ≠ z₀ ∧ γ.toFun γ.b ≠ z₀) (hC2 : ∀ t ∈ Ioo γ.a γ.b, γ.toFun t = z₀ → ContDiffAt ℝ 2 γ.toFun t) (h_cont_deriv_cross : ...) → CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun γ.a γ.b z₀`
- **What**: CPV of `(z - z₀)⁻¹` exists along the full piecewise C¹ immersion.
- **How**: Apply `cpv_exists_on_subinterval` with `n` = cardinality of `finite_crossings`.
- **Hypotheses**: γ measurable, no endpoint crossings, C² and continuous-derivative neighborhoods at each interior crossing.
- **Uses from project**: `finite_crossings`, `cpv_exists_on_subinterval`.
- **Used by**: `cpv_exists_inv_sub_of_C2`
- **Visibility**: public
- **Lines**: 661-674
- **Notes**: none

### `theorem cpv_exists_inv_sub_of_C2`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (hγ_meas : Measurable γ.toFun) (h_no_endpt : γ.toFun γ.a ≠ z₀ ∧ γ.toFun γ.b ≠ z₀) (hC2 : ∀ t ∈ Icc γ.a γ.b, ContDiffAt ℝ 2 γ.toFun t) (h_cont_deriv : ContinuousOn (deriv γ.toFun) (Icc γ.a γ.b)) → CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun γ.a γ.b z₀`
- **What**: Specialization of `cpv_exists_inv_sub` to globally C² curves with continuous derivative.
- **How**: Call `cpv_exists_inv_sub`, taking the global C² and continuous-derivative hypotheses and forgetting the dependence on crossings.
- **Hypotheses**: globally C² γ, continuous derivative on `[a,b]`, no endpoint crossings.
- **Uses from project**: `cpv_exists_inv_sub`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 682-691
- **Notes**: none

## File Summary

- **Total declarations**: 18 (including private lemmas).
- **Key public API**:
  - `finite_crossings` — Proposition 2.2.
  - `exists_isolated_crossing_interval` — neighborhood structure of each crossing.
  - `crossing_isolated_nhds`, `crossing_not_accPt`, `crossing_set_isClosed` — supporting topology of the crossing set.
  - `PiecewiseC1Immersion.eventually_ne_*` family — three isolation lemmas (smooth point, left/right partition point).
  - `PiecewiseC1Immersion.deriv_ne_zero_of_C2` — derivative non-vanishing under C² at partition.
  - `cpv_exists_single_crossing`, `cpv_integrand_intervalIntegrable` — CPV existence at single crossing and integrability of cutoff integrand.
  - `cpv_exists_inv_sub`, `cpv_exists_inv_sub_of_C2` — top-level CPV existence theorems for `(z - z₀)⁻¹`.
- **Unused (within this file)**: `cpv_exists_inv_sub_of_C2` (top-level export).
- **Sorries**: none.
- **set_options**: none. `attribute [local instance] Classical.propDecidable` at line 39.
- **Long proofs** (>30 lines): `eventually_ne_left_of_partition`, `eventually_ne_right_of_partition`, `crossing_isolated_nhds`, `exists_isolated_crossing_interval`, `cpv_integrand_intervalIntegrable`, `cpv_exists_on_subinterval`.
- **Purpose**: Proves Proposition 2.2 of Hungerbuhler-Wasem: crossings of a piecewise-C¹ immersion through a point form a finite set, and each crossing is isolated in an explicit sub-interval. Builds on top of this a chain of CPV-existence results culminating in the existence of the Cauchy principal value of `(z - z₀)⁻¹` integrated along the immersion, with both a general version (C² only at crossings) and a clean global-C² specialization, providing the analytic infrastructure used downstream for residue/winding-number arguments.
