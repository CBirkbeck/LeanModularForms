# Inventory: MultipointPV.lean

### `theorem finset_discrete_min_sep`
- **Type**: `(S : Finset ℂ) → S.Nonempty → (∀ s s' ∈ S, s ≠ s' → 0 < ‖s' - s‖) → ∃ δ > 0, ∀ s s' ∈ S, s ≠ s' → δ ≤ ‖s' - s‖`
- **What**: Positive minimum separation in a finite set of distinct complex numbers.
- **How**: 27 lines — `by_cases S.card ≤ 1`; singleton case uses `Finset.card_eq_one`; multi-element case builds `dists := S.biUnion (fun s => S.filter (·≠s)|>.image (·-s))`, shows nonempty via `Finset.exists_mem_ne`, takes `δ := dists.min'`, uses `Finset.min'_mem` and `Finset.min'_le`.
- **Hypotheses**: `S.Nonempty`, all distinct pairs have positive distance
- **Uses from project**: []
- **Used by**: `finset_discrete_min_sep'`
- **Visibility**: public
- **Lines**: 56-88
- **Notes**: >10 lines; `classical`; key lemma `Finset.min'_mem`, `Finset.exists_mem_ne`

### `theorem finset_discrete_min_sep'`
- **Type**: `1 < S.card → ∃ δ > 0, ∀ s₁ s₂ ∈ S, s₁ ≠ s₂ → δ ≤ ‖s₁ - s₂‖`
- **What**: Variant with the more natural `S.card > 1` hypothesis (forward subtraction).
- **How**: `Finset.card_pos.mp` for nonemptiness; apply `finset_discrete_min_sep` with `norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)`; flip arguments.
- **Hypotheses**: `1 < S.card`
- **Uses from project**: `finset_discrete_min_sep`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 92-98
- **Notes**: none

### `theorem disjoint_balls_of_small_epsilon`
- **Type**: `ε < δ/2 → (∀ s s' ∈ S, s≠s' → δ ≤ ‖s'-s‖) → ∀ s s' ∈ S, s≠s' → Disjoint (ball s ε) (ball s' ε)`
- **What**: Disjoint balls for sufficiently small ε.
- **How**: `Metric.ball_disjoint_ball`; convert `‖s'-s‖` to `dist s s'` via `dist_eq_norm, norm_sub_rev`; conclude with `linarith`.
- **Hypotheses**: `ε < δ/2`, pairwise separation by `δ`
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 102-113
- **Notes**: none

### `theorem cpvIntegrandOn_sub`
- **Type**: `cpvIntegrandOn S (f - g) γ ε t = cpvIntegrandOn S f γ ε t - cpvIntegrandOn S g γ ε t`
- **What**: Pointwise subtraction distribution of CPV integrand.
- **How**: Unfold `cpvIntegrandOn`; `split_ifs <;> ring`.
- **Hypotheses**: none
- **Uses from project**: `cpvIntegrandOn`
- **Used by**: `HasCauchyPVOn.sub`, `hasCauchyPVOn_of_tendsto_sub`
- **Visibility**: public
- **Lines**: 118-122
- **Notes**: none

### `theorem cpvIntegrandOn_add`
- **Type**: `cpvIntegrandOn S (f + g) γ ε t = cpvIntegrandOn S f γ ε t + cpvIntegrandOn S g γ ε t`
- **What**: Pointwise addition distribution of CPV integrand.
- **How**: Unfold `cpvIntegrandOn`; `split_ifs <;> ring`.
- **Hypotheses**: none
- **Uses from project**: `cpvIntegrandOn`
- **Used by**: `HasCauchyPVOn.add`
- **Visibility**: public
- **Lines**: 125-129
- **Notes**: none

### `theorem cpvIntegrandOn_neg`
- **Type**: `cpvIntegrandOn S (-f) γ ε t = -cpvIntegrandOn S f γ ε t`
- **What**: Pointwise negation commutation of CPV integrand.
- **How**: Unfold `cpvIntegrandOn`; `split_ifs <;> ring`.
- **Hypotheses**: none
- **Uses from project**: `cpvIntegrandOn`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 132-135
- **Notes**: none

### `theorem cpvIntegrandOn_subset_eq`
- **Type**: `S ⊆ T → (∀ s ∈ T, ε < ‖γ t - s‖) → cpvIntegrandOn S f γ ε t = cpvIntegrandOn T f γ ε t`
- **What**: When all `T`-singularities are far from `γ(t)`, the integrand on `S` equals the one on `T`.
- **How**: Derive `h_far_S` for `S` via `hST`; `simp [cpvIntegrandOn_of_forall_gt h_far_S, cpvIntegrandOn_of_forall_gt h_far]`.
- **Hypotheses**: `S ⊆ T`, all of `T` is `>ε` from `γ t`
- **Uses from project**: `cpvIntegrandOn`, `cpvIntegrandOn_of_forall_gt`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 139-144
- **Notes**: none

### `theorem cpvIntegrandOn_const_mul`
- **Type**: `cpvIntegrandOn S (c · f) γ ε t = c · cpvIntegrandOn S f γ ε t`
- **What**: Scalar multiplication distributes through the multi-point CPV integrand.
- **How**: `split_ifs`; on `then` branch `simp`, else `ring`.
- **Hypotheses**: none
- **Uses from project**: `cpvIntegrandOn`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 147-154
- **Notes**: none

### `theorem HasCauchyPVOn.sub`
- **Type**: `HasCauchyPVOn S f γ L₁ → HasCauchyPVOn S g γ L₂ → (∀ ε > 0, IntervalIntegrable (cpvIntegrandOn S f γ.ext ε) volume 0 1) → … → HasCauchyPVOn S (f-g) γ (L₁ - L₂)`
- **What**: Subtraction of multi-point CPV limits, requiring integrability.
- **How**: 15 lines — unfold `HasCauchyPVOn`; show the integral of difference is eventually equal to the difference of integrals via `filter_upwards [self_mem_nhdsWithin]`; pointwise apply `cpvIntegrandOn_sub`; split using `intervalIntegral.integral_sub`; conclude `(hf.sub hg).congr' heq.symm`.
- **Hypotheses**: both have CPV; both are interval integrable on `[0,1]` for each `ε > 0`
- **Uses from project**: `HasCauchyPVOn`, `cpvIntegrandOn`, `cpvIntegrandOn_sub`, `PiecewiseC1Path`
- **Used by**: unused in file (composition with `add` only)
- **Visibility**: public
- **Lines**: 172-193
- **Notes**: >10 lines; key lemma `intervalIntegral.integral_sub`, `Filter.Tendsto.sub`

### `theorem HasCauchyPVOn.add`
- **Type**: `HasCauchyPVOn S f γ L₁ → HasCauchyPVOn S g γ L₂ → integrability → HasCauchyPVOn S (f+g) γ (L₁ + L₂)`
- **What**: Addition of multi-point CPV limits.
- **How**: 15 lines — same pattern as `HasCauchyPVOn.sub` using `cpvIntegrandOn_add` and `intervalIntegral.integral_add`; conclude `(hf.add hg).congr' heq.symm`.
- **Hypotheses**: both have CPV; both interval-integrable on `[0,1]` for each `ε > 0`
- **Uses from project**: `HasCauchyPVOn`, `cpvIntegrandOn`, `cpvIntegrandOn_add`, `PiecewiseC1Path`
- **Used by**: `hasCauchyPVOn_of_tendsto_sub`, `HasCauchyPVOn.finset_sum`
- **Visibility**: public
- **Lines**: 197-218
- **Notes**: >10 lines; key lemma `intervalIntegral.integral_add`, `Filter.Tendsto.add`

### `theorem hasCauchyPVOn_of_tendsto_sub`
- **Type**: `HasCauchyPVOn S (f - g) γ 0 → HasCauchyPVOn S g γ L → integrability → HasCauchyPVOn S f γ L`
- **What**: Transfer via vanishing difference: if `f - g` has CPV `0` and `g` has CPV `L`, then `f` has CPV `L`.
- **How**: 17 lines — show integral of `f` is eventually equal to integral of `f-g` plus integral of `g` via `filter_upwards`; pointwise `cpvIntegrandOn_sub` then `ring`; sum tendsto via `hfg.add hg` and `zero_add`; conclude `.congr' heq.symm`.
- **Hypotheses**: `f - g` has CPV `0`, `g` has CPV `L`, integrability of `f-g` and `g`
- **Uses from project**: `HasCauchyPVOn`, `cpvIntegrandOn`, `cpvIntegrandOn_sub`, `HasCauchyPVOn.add` (implicit via `hfg.add hg`), `PiecewiseC1Path`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 227-259
- **Notes**: >10 lines; key lemma `intervalIntegral.integral_add`, `Filter.Tendsto.add`

### `theorem hasCauchyPVOn_singleton_of_hasCauchyPV`
- **Type**: `HasCauchyPV f γ z₀ L → HasCauchyPVOn {z₀} f γ L`
- **What**: Single-point CPV gives multi-point CPV on the singleton set.
- **How**: Unfold both; `h.congr` for each ε using `integral_congr` and `cpvIntegrand_eq_cpvIntegrandOn_singleton`.
- **Hypotheses**: `HasCauchyPV f γ z₀ L`
- **Uses from project**: `HasCauchyPV`, `HasCauchyPVOn`, `cpvIntegrand_eq_cpvIntegrandOn_singleton`, `PiecewiseC1Path`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 264-271
- **Notes**: none

### `theorem hasCauchyPV_of_hasCauchyPVOn_singleton`
- **Type**: `HasCauchyPVOn {z₀} f γ L → HasCauchyPV f γ z₀ L`
- **What**: Multi-point CPV on a singleton gives single-point CPV.
- **How**: Reverse of previous; `h.congr` for each ε using `integral_congr` and `cpvIntegrand_eq_cpvIntegrandOn_singleton.symm`.
- **Hypotheses**: `HasCauchyPVOn {z₀} f γ L`
- **Uses from project**: `HasCauchyPV`, `HasCauchyPVOn`, `cpvIntegrand_eq_cpvIntegrandOn_singleton`, `PiecewiseC1Path`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 274-281
- **Notes**: none

### `theorem HasCauchyPVOn.zero_fun`
- **Type**: `HasCauchyPVOn S (fun _ => 0) γ 0`
- **What**: The multi-point CPV of the zero function is zero.
- **How**: Show `cpvIntegrandOn S 0 γ.ext ε t = 0` (split_ifs <;> simp); apply `Tendsto.congr` with `tendsto_const_nhds`; integral of zero is `0` via `integral_zero.symm`.
- **Hypotheses**: none
- **Uses from project**: `HasCauchyPVOn`, `cpvIntegrandOn`, `PiecewiseC1Path`
- **Used by**: `HasCauchyPVOn.finset_sum`
- **Visibility**: public
- **Lines**: 286-297
- **Notes**: none

### `theorem HasCauchyPVOn.finset_sum`
- **Type**: `(T : Finset ι) → (∀ i ∈ T, HasCauchyPVOn S (f i) γ (L i)) → integrability → HasCauchyPVOn S (∑ i ∈ T, f i) γ (∑ i ∈ T, L i)`
- **What**: Finite-sum closure of `HasCauchyPVOn` with cutoff integrability.
- **How**: 35 lines — `Finset.induction_on T`; empty: reduce to `HasCauchyPVOn.zero_fun`; insert: combine `h_a` (member) with `ih` via `HasCauchyPVOn.add`; for the inductive `T'` integrability prove pointwise that `cpvIntegrandOn S (∑ f i) γ.ext ε t = ∑ cpvIntegrandOn S (f i) γ.ext ε t` (split_ifs branches: `Finset.sum_const_zero.symm` or `Finset.sum_mul`); use `IntervalIntegrable.sum T'` with `funext (Finset.sum_apply)`; conclude `rw [Finset.sum_insert hia]`.
- **Hypotheses**: each `f i` has CPV with limit `L i`; each `f i` cutoff-integrable on `[0,1]`
- **Uses from project**: `HasCauchyPVOn`, `cpvIntegrandOn`, `HasCauchyPVOn.zero_fun`, `HasCauchyPVOn.add`, `PiecewiseC1Path`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 301-345
- **Notes**: >10 lines; key lemma `Finset.induction_on`, `IntervalIntegrable.sum`, `Finset.sum_apply`

## File Summary
- 14 public theorems organized into four blocks:
  1. **Finite-set separation** (3): `finset_discrete_min_sep`, `finset_discrete_min_sep'`, `disjoint_balls_of_small_epsilon`.
  2. **Pointwise algebra of `cpvIntegrandOn`** (5): `_sub`, `_add`, `_neg`, `_subset_eq`, `_const_mul`.
  3. **Algebraic closure of `HasCauchyPVOn`** (3): `.sub`, `.add`, `hasCauchyPVOn_of_tendsto_sub`.
  4. **Single-point ↔ multi-point bridge & sums** (4): `hasCauchyPVOn_singleton_of_hasCauchyPV`, `hasCauchyPV_of_hasCauchyPVOn_singleton`, `.zero_fun`, `.finset_sum`.
- Builds on `CauchyPrincipalValue.lean` (`HasCauchyPV`, `HasCauchyPVOn`, `cpvIntegrand`, `cpvIntegrandOn`, `cpvIntegrand_eq_cpvIntegrandOn_singleton`, `cpvIntegrandOn_of_forall_gt`, `PiecewiseC1Path`).
- No sorries, no axioms, no `set_option`. `noncomputable section`. Variable `{x y : ℂ}` for `PiecewiseC1Path` endpoints.
