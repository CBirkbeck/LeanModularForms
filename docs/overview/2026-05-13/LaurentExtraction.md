# Inventory: LaurentExtraction.lean

**File**: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HungerbuhlerWasem/LaurentExtraction.lean`
**Lines**: 1130
**Imports**: `LeanModularForms.ForMathlib.FlatnessConditions`, `LeanModularForms.ForMathlib.HungerbuhlerWasem`, `Mathlib.Analysis.Meromorphic.Order`, `Mathlib.Analysis.Analytic.Order`, `Mathlib.Analysis.Analytic.IsolatedZeros`
**Namespace**: `HungerbuhlerWasem` (with section variable `{x : ℂ}`)

---

### `def IsCrossed`
- **Type**: `(γ : PwC1Immersion x x) (s : ℂ) : Prop`
- **What**: Predicate stating `γ` crosses `s` in the open interval `(0, 1)`: there exists `t₀ ∈ (0,1)` with `γ(t₀) = s`.
- **How**: Direct `Prop` definition `∃ t₀ ∈ Set.Ioo (0:ℝ) 1, (γ : ℝ → ℂ) t₀ = s`.
- **Hypotheses**: none.
- **Uses from project**: `PwC1Immersion`.
- **Used by**: `crossingParam`, `crossingParam_mem_Ioo`, `γ_at_crossingParam`, `laurent_data_exists`, `laurentPolarPartAt`, `laurentPolarOrderAt`, `laurentPolarCoeffAt`, `laurentAnalyticPartAt`, `laurentAnalyticPartAt_eq_data`, `laurentPolarPartAt_eq_data`, `laurentPolarPartAt_uncrossed`, `laurentPolarOrderAt_eq_data`, `laurentPolarOrderAt_uncrossed`, `laurentAnalyticPartAt_analyticAt`, `f_eq_analyticPart_plus_polarPart_eventually`, `f_minus_polarPartAt_eventuallyEq_analyticPartAt`, `laurentPolarPartAt_differentiableAt`, `laurentPolarPartAt_eq_sum`, `laurentPolarCoeffAt_zero_eq_residue`, `otherPolar_analyticAt`, `f_minus_total_eventuallyEq_analytic`, `PolarPartDecomposition.ofConditionB`.
- **Visibility**: public
- **Lines**: 53-54

### `noncomputable def crossingParam`
- **Type**: `(γ : PwC1Immersion x x) (s : ℂ) : ℝ`
- **What**: The selected crossing parameter `t₀ ∈ (0,1)` with `γ(t₀) = s` (via `Classical.choose`), or `0` if `s` is not crossed.
- **How**: Uses `Classical.choose h` when `IsCrossed γ s` holds, else returns `0`.
- **Hypotheses**: none.
- **Uses from project**: `PwC1Immersion`, `IsCrossed`.
- **Used by**: `crossingParam_mem_Ioo`, `γ_at_crossingParam`, `laurent_data_exists`.
- **Visibility**: public
- **Lines**: 58-59

### `theorem crossingParam_mem_Ioo`
- **Type**: `{γ : PwC1Immersion x x} {s : ℂ} (h : IsCrossed γ s) → crossingParam γ s ∈ Set.Ioo (0:ℝ) 1`
- **What**: The selected crossing parameter lives in the open interval `(0,1)`.
- **How**: `simpa [crossingParam, h]` unfolds the dependent if, then projection `.1` of `Classical.choose_spec h`.
- **Hypotheses**: `IsCrossed γ s`.
- **Uses from project**: `PwC1Immersion`, `IsCrossed`, `crossingParam`.
- **Used by**: `laurent_data_exists`.
- **Visibility**: public
- **Lines**: 61-63

### `theorem γ_at_crossingParam`
- **Type**: `{γ : PwC1Immersion x x} {s : ℂ} (h : IsCrossed γ s) → (γ : ℝ → ℂ) (crossingParam γ s) = s`
- **What**: At the selected crossing parameter, `γ` indeed equals `s`.
- **How**: `simpa [crossingParam, h]` and projection `.2` of `Classical.choose_spec h`.
- **Hypotheses**: `IsCrossed γ s`.
- **Uses from project**: `PwC1Immersion`, `IsCrossed`, `crossingParam`.
- **Used by**: `laurent_data_exists`.
- **Visibility**: public
- **Lines**: 65-67

### `private theorem laurent_data_exists`
- **Type**: `{γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S) (h_cross : IsCrossed γ s) → ∃ N a g, AnalyticAt ℂ g s ∧ (∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ k : Fin N, a k / (z - s)^(k.val + 1)) ∧ (...)`
- **What**: From condition (B), at a crossed pole `s ∈ S`, extracts the Laurent data `(N, a, g)`: order, coefficients, analytic remainder, plus the angle-quantization condition.
- **How**: Invokes `hCondB.laurent_compatible s hs` at the crossing parameter; uses `crossingParam_mem_Ioo` and `γ_at_crossingParam`.
- **Hypotheses**: condition (B), `s ∈ S`, crossing.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `SatisfiesConditionB.laurent_compatible`, `IsCrossed`, `crossingParam`, `crossingParam_mem_Ioo`, `γ_at_crossingParam`, `angleAtCrossing`.
- **Used by**: `laurentPolarPartAt`, `laurentPolarOrderAt`, `laurentPolarCoeffAt`, `laurentAnalyticPartAt`, `laurentAnalyticPartAt_eq_data`, `laurentPolarPartAt_eq_data`, `laurentPolarOrderAt_eq_data`, `laurentAnalyticPartAt_analyticAt`, `f_eq_analyticPart_plus_polarPart_eventually`, `laurentPolarCoeffAt_zero_eq_residue`, `PolarPartDecomposition.ofConditionB`.
- **Visibility**: private
- **Lines**: 73-84

### `noncomputable def laurentPolarPartAt`
- **Type**: `{γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S) (z : ℂ) : ℂ`
- **What**: Local polar part at pole `s`: `∑ k ∈ Fin N, a_k / (z-s)^(k+1)` for crossed `s`, zero otherwise.
- **How**: Single `if h : IsCrossed γ s then ... else 0` with `Classical.choose` extracting `N` and `a`. Single conditional avoids dependent-type clashes.
- **Hypotheses**: none beyond what's in the signature.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurent_data_exists`.
- **Used by**: `laurentPolarPartAt_eq_data`, `laurentPolarPartAt_uncrossed`, `f_eq_analyticPart_plus_polarPart_eventually`, `f_minus_polarPartAt_eventuallyEq_analyticPartAt`, `laurentPolarPartAt_differentiableAt`, `laurentPolarPartAt_eq_sum`, `otherPolar_analyticAt`, `f_minus_total_eventuallyEq_analytic`, `laurentPolarPartTotal`, `PolarPartDecomposition.ofConditionB`.
- **Visibility**: public
- **Lines**: 94-102

### `noncomputable def laurentPolarOrderAt`
- **Type**: `{γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S) : ℕ`
- **What**: Order of the local polar part at `s`: `N` from condition (B) for crossed poles, `0` otherwise.
- **How**: Single `if h : IsCrossed γ s then (laurent_data_exists ...).choose else 0`.
- **Hypotheses**: none beyond signature.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurent_data_exists`.
- **Used by**: `laurentPolarCoeffAt`, `laurentPolarOrderAt_eq_data`, `laurentPolarOrderAt_uncrossed`, `laurentPolarPartAt_eq_sum`, `laurentPolarCoeffAt_zero_eq_residue`, `PolarPartDecomposition.ofConditionB`.
- **Visibility**: public
- **Lines**: 106-112

### `noncomputable def laurentPolarCoeffAt`
- **Type**: `{γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S) (k : Fin (laurentPolarOrderAt hCondB s hs)) : ℂ`
- **What**: The k-th Laurent coefficient at `s`. Uses `Fin.cast` to identify the local `Fin (order)` with `Fin N` from the choose data.
- **How**: For crossed `s`, casts `k` along `laurentPolarOrderAt = N` and applies the extracted coefficient family; for uncrossed `s`, `order = 0`, so the `Fin (order s)` index is impossible (`absurd k.isLt`).
- **Hypotheses**: none beyond signature.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurentPolarOrderAt`, `laurent_data_exists`.
- **Used by**: `laurentPolarPartAt_eq_sum`, `laurentPolarCoeffAt_zero_eq_residue`, `PolarPartDecomposition.ofConditionB`.
- **Visibility**: public
- **Lines**: 117-130

### `noncomputable def laurentAnalyticPartAt`
- **Type**: `{γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S) : ℂ → ℂ`
- **What**: The analytic remainder `g` at pole `s`. For crossed `s`, returned by condition (B). For uncrossed, this is `f` itself (since no polar part is subtracted).
- **How**: `if h : IsCrossed γ s then (laurent_data_exists ...).choose_spec.choose_spec.choose else f`.
- **Hypotheses**: none beyond signature.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurent_data_exists`.
- **Used by**: `laurentAnalyticPartAt_eq_data`, `laurentAnalyticPartAt_analyticAt`, `f_eq_analyticPart_plus_polarPart_eventually`, `f_minus_polarPartAt_eventuallyEq_analyticPartAt`, `f_minus_total_eventuallyEq_analytic`.
- **Visibility**: public
- **Lines**: 137-143

### `private lemma laurentAnalyticPartAt_eq_data`
- **Type**: `{γ} {f} {S} (hCondB) {s} (hs) (h_cross) → laurentAnalyticPartAt hCondB s hs = (laurent_data_exists hCondB hs h_cross).choose_spec.choose_spec.choose`
- **What**: Unfolding lemma: for crossed `s`, the analytic part equals the chosen data.
- **How**: `simp [laurentAnalyticPartAt, h_cross]`.
- **Hypotheses**: crossing.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurentAnalyticPartAt`, `laurent_data_exists`.
- **Used by**: `laurentAnalyticPartAt_analyticAt`, `f_eq_analyticPart_plus_polarPart_eventually`.
- **Visibility**: private
- **Lines**: 147-152

### `private lemma laurentPolarPartAt_eq_data`
- **Type**: `{γ} {f} {S} (hCondB) {s} (hs) (h_cross) (z) → laurentPolarPartAt hCondB s hs z = ∑ k : Fin (laurent_data_exists ...).choose, (laurent_data_exists ...).choose_spec.choose k / (z - s)^(k.val + 1)`
- **What**: Unfolding lemma: for crossed `s`, the polar part equals the explicit Laurent sum from the chosen data.
- **How**: `simp [laurentPolarPartAt, h_cross]`.
- **Hypotheses**: crossing.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurentPolarPartAt`, `laurent_data_exists`.
- **Used by**: `f_eq_analyticPart_plus_polarPart_eventually`, `laurentPolarPartAt_eq_sum`.
- **Visibility**: private
- **Lines**: 154-161

### `private lemma laurentPolarPartAt_uncrossed`
- **Type**: `{γ} {f} {S} (hCondB) {s} (hs) (h_not_cross) (z) → laurentPolarPartAt hCondB s hs z = 0`
- **What**: For uncrossed poles, the polar part is identically zero.
- **How**: `simp [laurentPolarPartAt, h_not_cross]`.
- **Hypotheses**: `¬ IsCrossed γ s`.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurentPolarPartAt`.
- **Used by**: `laurentPolarPartAt_eq_sum`.
- **Visibility**: private
- **Lines**: 163-167

### `private lemma laurentPolarOrderAt_eq_data`
- **Type**: `{γ} {f} {S} (hCondB) {s} (hs) (h_cross) → laurentPolarOrderAt hCondB s hs = (laurent_data_exists hCondB hs h_cross).choose`
- **What**: Unfolding lemma: for crossed `s`, the order equals `N` from the choose data.
- **How**: `simp [laurentPolarOrderAt, h_cross]`.
- **Hypotheses**: crossing.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurentPolarOrderAt`, `laurent_data_exists`.
- **Used by**: `laurentPolarPartAt_eq_sum`, `laurentPolarCoeffAt_zero_eq_residue`, `PolarPartDecomposition.ofConditionB`.
- **Visibility**: private
- **Lines**: 169-173

### `private lemma laurentPolarOrderAt_uncrossed`
- **Type**: `{γ} {f} {S} (hCondB) {s} (hs) (h_not_cross) → laurentPolarOrderAt hCondB s hs = 0`
- **What**: For uncrossed `s`, the order is zero.
- **How**: `simp [laurentPolarOrderAt, h_not_cross]`.
- **Hypotheses**: `¬ IsCrossed γ s`.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurentPolarOrderAt`.
- **Used by**: `laurentPolarPartAt_eq_sum`.
- **Visibility**: private
- **Lines**: 175-179

### `theorem laurentAnalyticPartAt_analyticAt`
- **Type**: `{γ} {f} {S} (hCondB) {s} (hs) (h_cross) → AnalyticAt ℂ (laurentAnalyticPartAt hCondB s hs) s`
- **What**: For crossed `s`, the analytic part is analytic at `s`.
- **How**: Rewrites via `laurentAnalyticPartAt_eq_data`, applies `.choose_spec.choose_spec.choose_spec.1` of `laurent_data_exists`.
- **Hypotheses**: crossing.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurentAnalyticPartAt`, `laurentAnalyticPartAt_eq_data`, `laurent_data_exists`.
- **Used by**: `f_minus_total_eventuallyEq_analytic`.
- **Visibility**: public
- **Lines**: 182-187

### `theorem f_eq_analyticPart_plus_polarPart_eventually`
- **Type**: `{γ} {f} {S} (hCondB) {s} (hs) (h_cross) → ∀ᶠ z in 𝓝[≠] s, f z = laurentAnalyticPartAt hCondB s hs z + laurentPolarPartAt hCondB s hs z`
- **What**: Near a crossed pole `s`, `f` decomposes as analytic part + polar part (in the punctured neighborhood).
- **How**: `filter_upwards` from the eventual equation in the choose data, then rewrites via `laurentPolarPartAt_eq_data` and `laurentAnalyticPartAt_eq_data`.
- **Hypotheses**: crossing.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurentAnalyticPartAt`, `laurentAnalyticPartAt_eq_data`, `laurentPolarPartAt`, `laurentPolarPartAt_eq_data`, `laurent_data_exists`.
- **Used by**: `f_minus_polarPartAt_eventuallyEq_analyticPartAt`, `f_minus_total_eventuallyEq_analytic`.
- **Visibility**: public
- **Lines**: 192-202

### `theorem f_minus_polarPartAt_eventuallyEq_analyticPartAt`
- **Type**: `{γ} {f} {S} (hCondB) {s} (hs) (h_cross) → (fun z => f z - laurentPolarPartAt hCondB s hs z) =ᶠ[𝓝[≠] s] laurentAnalyticPartAt hCondB s hs`
- **What**: Corollary: `f - polarPart =ᶠ analyticPart` near a crossed pole.
- **How**: `filter_upwards` from `f_eq_analyticPart_plus_polarPart_eventually` and `ring`.
- **Hypotheses**: crossing.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurentAnalyticPartAt`, `laurentPolarPartAt`, `f_eq_analyticPart_plus_polarPart_eventually`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 206-213

### `theorem laurentPolarPartAt_differentiableAt`
- **Type**: `{γ} {f} {S} (hCondB) {s} (hs) {z : ℂ} (hz : z ≠ s) → DifferentiableAt ℂ (laurentPolarPartAt hCondB s hs) z`
- **What**: The polar part is differentiable at any `z ≠ s`.
- **How**: Case on `IsCrossed γ s`. For crossed: `DifferentiableAt.fun_sum`, each summand uses `differentiableAt_const.div` with `(differentiableAt_id.sub_const).pow` and `pow_ne_zero` from `sub_ne_zero.mpr hz`. For uncrossed: zero function.
- **Hypotheses**: `z ≠ s`.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurentPolarPartAt`.
- **Used by**: `PolarPartDecomposition.ofConditionB`.
- **Visibility**: public
- **Lines**: 218-230

### `theorem laurentPolarPartAt_eq_sum`
- **Type**: `{γ} {f} {S} (hCondB) {s} (hs) (z) → laurentPolarPartAt hCondB s hs z = ∑ k : Fin (laurentPolarOrderAt hCondB s hs), laurentPolarCoeffAt hCondB s hs k / (z - s)^(k.val + 1)`
- **What**: The polar part written as the explicit Laurent sum in `order` and `coeff` form. This is the canonical form needed by `PolarPartDecomposition.polarPart_eq`.
- **How**: Case on `IsCrossed γ s`. Crossed case: `laurentPolarPartAt_eq_data`, `Fin.sum_congr'` to identify orders, `Finset.sum_congr`, unfolding `laurentPolarCoeffAt`. Uncrossed case: `laurentPolarPartAt_uncrossed`, `Finset.sum_eq_zero`, `laurentPolarOrderAt_uncrossed`, `absurd k.isLt`.
- **Hypotheses**: none beyond signature.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurentPolarPartAt`, `laurentPolarPartAt_eq_data`, `laurentPolarPartAt_uncrossed`, `laurentPolarOrderAt`, `laurentPolarOrderAt_eq_data`, `laurentPolarOrderAt_uncrossed`, `laurentPolarCoeffAt`, `laurent_data_exists`.
- **Used by**: `PolarPartDecomposition.ofConditionB`.
- **Visibility**: public
- **Lines**: 237-254

### `private lemma circleIntegral_higherOrder_eq_zero`
- **Type**: `{s : ℂ} {r : ℝ} {n : ℕ} (hn : 2 ≤ n) (c : ℂ) → ∮ z in C(s, r), c / (z - s)^n = 0`
- **What**: The circle integral `∮ c/(z-s)^n` vanishes for `n ≥ 2`.
- **How**: Rewrites `1/(z-s)^n = (z-s)^(-n:ℤ)` via `div_eq_mul_inv`, `zpow_neg`, `zpow_natCast`, then applies `circleIntegral.integral_sub_zpow_of_ne` (which gives 0 for exponents ≠ -1).
- **Hypotheses**: `2 ≤ n`.
- **Uses from project**: `[]` (mathlib only).
- **Used by**: `residue_of_laurent_expansion`.
- **Visibility**: private
- **Lines**: 268-275

### `private lemma circleIntegral_higherOrder_sum_eq_zero`
- **Type**: `{s : ℂ} {r : ℝ} (hr : 0 < r) {N : ℕ} (a : Fin N → ℂ) → ∮ z in C(s, r), (∑ k : Fin N, if k.val ≥ 1 then a k / (z - s)^(k.val + 1) else 0) = 0`
- **What**: The circle integral of the higher-order Laurent terms (exponents ≥ 2) vanishes.
- **How**: Establishes each summand is circle-integrable via `circleIntegrable_sub_zpow_iff`, applies `circleIntegral.integral_fun_sum`, then term-by-term: nonzero branch is `circleIntegral_higherOrder_eq_zero`, zero branch trivial.
- **Hypotheses**: `0 < r`.
- **Uses from project**: `circleIntegral_higherOrder_eq_zero`.
- **Used by**: `residue_of_laurent_expansion`.
- **Visibility**: private
- **Lines**: 277-307
- **Notes**: proof ≈30 lines.

### `theorem residue_of_laurent_expansion`
- **Type**: `{f g : ℂ → ℂ} {s : ℂ} (N : ℕ) (a : Fin N → ℂ) (hg : AnalyticAt ℂ g s) (hf_eq : ∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ k : Fin N, a k / (z - s)^(k.val + 1)) → residue f s = if h : 0 < N then a ⟨0, h⟩ else 0`
- **What**: **Residue from Laurent data**: given the Laurent expansion `f = g + ∑ a_k/(z-s)^(k+1)` (with `g` analytic), the residue equals `a 0` if `N > 0`, else `0`.
- **How**: Higher-order generalization of `residue_eq_of_simple_pole_decomp`. Case `0 < N`: split `∑ = a_0/(z-s) + rest`, where `rest = g + ∑_{k≥1} ...`. Use `tendsto_nhds_of_eventually_eq`, `hg.exists_ball_analyticOnNhd`, `Filter.Iio_mem_nhds`, expand `eventually_nhdsWithin_iff`, get `EqOn` on `sphere s r`, then compute circle integral: `circleIntegral.integral_congr`, `integral_add`, `integral_const_mul`, `integral_sub_center_inv` for `2πi · a_0`; `circleIntegral_eq_zero_of_differentiable_on_off_countable` for `g`; `circleIntegral_higherOrder_sum_eq_zero` for higher-order terms; conclude `field_simp`. Case `N = 0`: use `residue_congr` and `residue_eq_zero_of_analyticAt`.
- **Hypotheses**: analyticity of `g`, eventual Laurent equation.
- **Uses from project**: `residue`, `residue_congr`, `residue_eq_zero_of_analyticAt`, `circleIntegral_higherOrder_sum_eq_zero`.
- **Used by**: `laurentPolarCoeffAt_zero_eq_residue`, `PolarPartDecomposition.ofConditionB`, `meroPolarCoeffAt_zero_eq_residue`, `PolarPartDecomposition.ofMeromorphicWithCondB`.
- **Visibility**: public
- **Lines**: 317-445
- **Notes**: proof ≈128 lines.

### `theorem laurentPolarCoeffAt_zero_eq_residue`
- **Type**: `{γ} {f} {S} (hCondB) {s} (hs) (h_cross : IsCrossed γ s) (h_pos : 0 < laurentPolarOrderAt hCondB s hs) → laurentPolarCoeffAt hCondB s hs ⟨0, h_pos⟩ = residue f s`
- **What**: The leading Laurent coefficient `a₀` from condition (B) equals the residue (for crossed `s`).
- **How**: Sets `N`, `a`, `g` from `laurent_data_exists`; applies `residue_of_laurent_expansion`; rewrites `dif_pos`; unfolds `laurentPolarCoeffAt`.
- **Hypotheses**: crossing, positive order.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurentPolarOrderAt`, `laurentPolarOrderAt_eq_data`, `laurentPolarCoeffAt`, `laurent_data_exists`, `residue`, `residue_of_laurent_expansion`.
- **Used by**: `PolarPartDecomposition.ofConditionB`.
- **Visibility**: public
- **Lines**: 449-468

### `noncomputable def laurentPolarPartTotal`
- **Type**: `{γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (z : ℂ) : ℂ`
- **What**: Total polar part: sum over `S.attach` of `laurentPolarPartAt`.
- **How**: `∑ s ∈ S.attach, laurentPolarPartAt hCondB s.1 s.2 z`.
- **Hypotheses**: none beyond signature.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `laurentPolarPartAt`.
- **Used by**: `f_minus_total_eventuallyEq_analytic`, `PolarPartDecomposition.ofConditionB`.
- **Visibility**: public
- **Lines**: 485-487

### `private theorem otherPolar_analyticAt`
- **Type**: `{γ} {f} {S} (hCondB) {s} (_hs) → AnalyticAt ℂ (fun z => ∑ s' ∈ S.attach.filter (·.1 ≠ s), laurentPolarPartAt hCondB s'.1 s'.2 z) s`
- **What**: The sum of polar parts at other poles (excluding `s`) is analytic at `s`.
- **How**: `Finset.analyticAt_fun_sum`; case on `IsCrossed γ s'.1`: if crossed, each summand is `analyticAt_const.div` of analytic numerator and analytic denominator (`pow_ne_zero` from `s'.1 ≠ s`); if uncrossed, `analyticAt_const` (zero).
- **Hypotheses**: `s ∈ S`.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurentPolarPartAt`.
- **Used by**: `f_minus_total_eventuallyEq_analytic`.
- **Visibility**: private
- **Lines**: 491-504

### `private theorem f_minus_total_eventuallyEq_analytic`
- **Type**: `{γ} {f} {S} (hCondB) {s} (hs) (h_cross) → ∃ g_s : ℂ → ℂ, AnalyticAt ℂ g_s s ∧ ∀ᶠ z in 𝓝[≠] s, f z - laurentPolarPartTotal hCondB z = g_s z`
- **What**: Near `s` (crossed), `f - polarPartTotal` is analytic at `s` (equal to `analyticPart s - sum of other polar parts`).
- **How**: Sets `g_s = analyticPart s - ∑_{s' ≠ s} polarPart s'`, uses `f_eq_analyticPart_plus_polarPart_eventually`. Uses `Finset.sum_filter_add_sum_filter_not S.attach` to split into the `{s}` singleton and rest. Singleton case via `Finset.sum_singleton`.
- **Hypotheses**: crossing.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurentAnalyticPartAt`, `laurentAnalyticPartAt_analyticAt`, `laurentPolarPartAt`, `laurentPolarPartTotal`, `f_eq_analyticPart_plus_polarPart_eventually`, `otherPolar_analyticAt`.
- **Used by**: `PolarPartDecomposition.ofConditionB`.
- **Visibility**: private
- **Lines**: 511-545
- **Notes**: proof ≈35 lines.

### `noncomputable def PolarPartDecomposition.ofConditionB`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U \ ↑S)) {γ : PwC1Immersion x x} (hCondB : SatisfiesConditionB γ f S) (hAllCrossed : ∀ s ∈ S, IsCrossed γ s) → PolarPartDecomposition f S U`
- **What**: **Constructor**: builds a `PolarPartDecomposition` from condition (B) when γ crosses every pole.
- **How**: Tactic-mode construction. Sets `polarPart`, `order`, `coeff` as if-then-else wrappers; `rem = f - polarPartTotal`; `correction = if z ∈ S then limUnder rem else rem z`. Refines the structure with 4 obligations: `polarPart_eq` (via `laurentPolarPartAt_eq_sum`), `residue_eq` (via `laurentPolarCoeffAt_zero_eq_residue` and `residue_of_laurent_expansion`), `analyticRemainder_diff` (case `z ∈ S`: via `f_minus_total_eventuallyEq_analytic`, `congr_of_eventuallyEq`; case `z ∉ S`: via `hU_open.sdiff`, `DifferentiableAt.fun_sum`, `laurentPolarPartAt_differentiableAt`), `decomp` (algebra).
- **Hypotheses**: open `U`, `S ⊆ U`, differentiability off `S`, condition (B), all poles crossed.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `PolarPartDecomposition`, `laurentPolarPartAt`, `laurentPolarPartAt_eq_sum`, `laurentPolarPartAt_differentiableAt`, `laurentPolarOrderAt`, `laurentPolarOrderAt_eq_data`, `laurentPolarCoeffAt`, `laurentPolarCoeffAt_zero_eq_residue`, `laurentPolarPartTotal`, `laurent_data_exists`, `residue_of_laurent_expansion`, `f_minus_total_eventuallyEq_analytic`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 557-679
- **Notes**: proof ≈122 lines; key downstream consumer.

### `private lemma analyticAt_peel_one`
- **Type**: `{g : ℂ → ℂ} {s : ℂ} (hg : AnalyticAt ℂ g s) → ∃ g₁ : ℂ → ℂ, AnalyticAt ℂ g₁ s ∧ ∀ᶠ z in 𝓝 s, g z = g s + (z - s) * g₁ z`
- **What**: Peeling lemma: if `g` is analytic at `s`, then `g(z) = g(s) + (z-s) · g₁(z)` for some `g₁` analytic at `s`.
- **How**: Set `g - g s` (analytic), has value `0` at `s`. Use `analyticOrderAt_eq_zero` to deduce order ≥ 1, then `natCast_le_analyticOrderAt` to get the factorization `(z-s) · g₁`. Simplify `smul_eq_mul, pow_one`. Conclude via `linear_combination`.
- **Hypotheses**: `g` analytic at `s`.
- **Uses from project**: `[]` (mathlib only).
- **Used by**: `analyticAt_taylor_decomp`.
- **Visibility**: private
- **Lines**: 702-719

### `private lemma analyticAt_taylor_decomp`
- **Type**: `{g : ℂ → ℂ} {s : ℂ} (hg : AnalyticAt ℂ g s) (k : ℕ) → ∃ (c : Fin k → ℂ) (R : ℂ → ℂ), AnalyticAt ℂ R s ∧ ∀ᶠ z in 𝓝 s, g z = (∑ j : Fin k, c j * (z - s)^j.val) + (z - s)^k * R z`
- **What**: Taylor decomposition to depth `k`: extract `k` coefficients and an analytic remainder.
- **How**: Induction on `k`. Base case `k=0`: `Fin.elim0` and `R = g`. Successor case: apply IH to get `c, R`, then peel `R` via `analyticAt_peel_one`. Use `Fin.snoc` to extend `c`, `Fin.sum_univ_castSucc` to split the sum, `Fin.snoc_castSucc`, `Fin.snoc_last`, `ring`.
- **Hypotheses**: `g` analytic at `s`.
- **Uses from project**: `analyticAt_peel_one`.
- **Used by**: `mero_laurent_data_exists`.
- **Visibility**: private
- **Lines**: 725-742

### `private lemma pow_div_pow_neg`
- **Type**: `{w : ℂ} (hw : w ≠ 0) {k j : ℕ} (hjk : j < k) → w^j * (w^k)⁻¹ = (w^(k-j))⁻¹`
- **What**: Algebraic helper: `w^j / w^k = 1/w^(k-j)` for `j < k`.
- **How**: Writes `(w^k)⁻¹ = (w^((k-j)+j))⁻¹` via `omega`, then `pow_add`, `field_simp`.
- **Hypotheses**: `w ≠ 0`, `j < k`.
- **Uses from project**: `[]`.
- **Used by**: `mero_laurent_data_exists`.
- **Visibility**: private
- **Lines**: 745-752

### `private lemma reindex_sum_fin_neg`
- **Type**: `{k : ℕ} (_hk : 0 < k) (c : Fin k → ℂ) (w : ℂ) → (∑ j : Fin k, c j / w^(k - j.val)) = ∑ i : Fin k, c ⟨k - 1 - i.val, _⟩ / w^(i.val + 1)`
- **What**: Reindex helper: sum over `Fin k` with index transformation `j ↦ k - 1 - j`.
- **How**: Defines involution `σ : Fin k → Fin k`, `σ j = ⟨k - 1 - j.val, ...⟩`; uses `Equiv.sum_comp` with `⟨σ, σ, σ.leftInverse, σ.rightInverse⟩`; final `Finset.sum_congr` and `omega`.
- **Hypotheses**: `0 < k`.
- **Uses from project**: `[]`.
- **Used by**: `mero_laurent_data_exists`.
- **Visibility**: private
- **Lines**: 756-777

### `theorem mero_laurent_data_exists`
- **Type**: `{f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) → ∃ (N : ℕ) (a : Fin N → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g s ∧ ∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ k : Fin N, a k / (z - s)^(k.val + 1)`
- **What**: **Generic Laurent extraction**: for any meromorphic `f` at `s`, there exist `(N, a, g)` giving the Laurent form `f = g + ∑ a_k/(z-s)^(k+1)`.
- **How**: Two cases via `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`. Pole case `n < 0`: set `k = (-n).toNat`, apply `analyticAt_taylor_decomp` to `g₀` at depth `k`, reindex coefficients using `pow_div_pow_neg` and `reindex_sum_fin_neg`. Removable case `n ≥ 0`: set `m = n.toNat`, return `N = 0`, `g = (z-s)^m * g₀`.
- **Hypotheses**: `MeromorphicAt f s`.
- **Uses from project**: `analyticAt_taylor_decomp`, `pow_div_pow_neg`, `reindex_sum_fin_neg`.
- **Used by**: `meroPolarPartAt`, `meroPolarOrderAt`, `meroPolarCoeffAt`, `meroAnalyticPartAt`, `meroAnalyticPartAt_analyticAt`, `mero_f_eq_analyticPart_plus_polarPart_eventually`, `meroPolarCoeffAt_zero_eq_residue`, `PolarPartDecomposition.ofMeromorphicWithCondB`.
- **Visibility**: public
- **Lines**: 782-834
- **Notes**: proof ≈52 lines.

### `noncomputable def meroPolarPartAt`
- **Type**: `{f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) (z : ℂ) : ℂ`
- **What**: Local polar part at `s` from `MeromorphicAt`.
- **How**: `∑ k : Fin (mero_laurent_data_exists hMero).choose, (mero_laurent_data_exists hMero).choose_spec.choose k / (z - s)^(k.val + 1)`.
- **Hypotheses**: none beyond signature.
- **Uses from project**: `mero_laurent_data_exists`.
- **Used by**: `mero_f_eq_analyticPart_plus_polarPart_eventually`, `mero_f_minus_polarPartAt_eventuallyEq_analyticPartAt`, `meroPolarPartAt_differentiableAt`, `meroPolarPartAt_analyticAt_off`, `meroPolarPartAt_eq_sum`, `meroPolarPartTotal`, `mero_otherPolar_analyticAt`, `mero_f_minus_total_eventuallyEq_analytic`, `PolarPartDecomposition.ofMeromorphicWithCondB`.
- **Visibility**: public
- **Lines**: 840-844

### `noncomputable def meroPolarOrderAt`
- **Type**: `{f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) : ℕ`
- **What**: Order of the polar part at `s` from `MeromorphicAt`.
- **How**: `(mero_laurent_data_exists hMero).choose`.
- **Hypotheses**: none beyond signature.
- **Uses from project**: `mero_laurent_data_exists`.
- **Used by**: `meroPolarCoeffAt`, `meroPolarPartAt_eq_sum`, `meroPolarCoeffAt_zero_eq_residue`, `PolarPartDecomposition.ofMeromorphicWithCondB`.
- **Visibility**: public
- **Lines**: 847-849

### `noncomputable def meroPolarCoeffAt`
- **Type**: `{f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) (k : Fin (meroPolarOrderAt hMero)) : ℂ`
- **What**: k-th Laurent coefficient at `s` from `MeromorphicAt`.
- **How**: `(mero_laurent_data_exists hMero).choose_spec.choose (Fin.cast (by simp [meroPolarOrderAt]) k)`.
- **Hypotheses**: none beyond signature.
- **Uses from project**: `mero_laurent_data_exists`, `meroPolarOrderAt`.
- **Used by**: `meroPolarPartAt_eq_sum`, `meroPolarCoeffAt_zero_eq_residue`, `PolarPartDecomposition.ofMeromorphicWithCondB`.
- **Visibility**: public
- **Lines**: 852-855

### `noncomputable def meroAnalyticPartAt`
- **Type**: `{f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) : ℂ → ℂ`
- **What**: Analytic remainder at `s` from `MeromorphicAt`.
- **How**: `(mero_laurent_data_exists hMero).choose_spec.choose_spec.choose`.
- **Hypotheses**: none beyond signature.
- **Uses from project**: `mero_laurent_data_exists`.
- **Used by**: `meroAnalyticPartAt_analyticAt`, `mero_f_eq_analyticPart_plus_polarPart_eventually`, `mero_f_minus_polarPartAt_eventuallyEq_analyticPartAt`, `mero_f_minus_total_eventuallyEq_analytic`.
- **Visibility**: public
- **Lines**: 858-860

### `theorem meroAnalyticPartAt_analyticAt`
- **Type**: `{f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) → AnalyticAt ℂ (meroAnalyticPartAt hMero) s`
- **What**: The analytic part from `MeromorphicAt` is analytic at `s`.
- **How**: Direct extraction `.choose_spec.choose_spec.choose_spec.1` from `mero_laurent_data_exists`.
- **Hypotheses**: `MeromorphicAt f s`.
- **Uses from project**: `mero_laurent_data_exists`, `meroAnalyticPartAt`.
- **Used by**: `mero_f_minus_total_eventuallyEq_analytic`.
- **Visibility**: public
- **Lines**: 863-865

### `theorem mero_f_eq_analyticPart_plus_polarPart_eventually`
- **Type**: `{f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) → ∀ᶠ z in 𝓝[≠] s, f z = meroAnalyticPartAt hMero z + meroPolarPartAt hMero z`
- **What**: Local Laurent decomposition near `s` from `MeromorphicAt`.
- **How**: `filter_upwards` from `.choose_spec.choose_spec.choose_spec.2` of `mero_laurent_data_exists`; `rw [hz]` and `rfl`.
- **Hypotheses**: `MeromorphicAt f s`.
- **Uses from project**: `mero_laurent_data_exists`, `meroAnalyticPartAt`, `meroPolarPartAt`.
- **Used by**: `mero_f_minus_polarPartAt_eventuallyEq_analyticPartAt`, `mero_f_minus_total_eventuallyEq_analytic`.
- **Visibility**: public
- **Lines**: 869-876

### `theorem mero_f_minus_polarPartAt_eventuallyEq_analyticPartAt`
- **Type**: `{f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) → (fun z => f z - meroPolarPartAt hMero z) =ᶠ[𝓝[≠] s] meroAnalyticPartAt hMero`
- **What**: Corollary: `f - polarPart =ᶠ analyticPart` near `s`.
- **How**: `filter_upwards [mero_f_eq_analyticPart_plus_polarPart_eventually hMero]`, `ring`.
- **Hypotheses**: `MeromorphicAt f s`.
- **Uses from project**: `mero_f_eq_analyticPart_plus_polarPart_eventually`, `meroAnalyticPartAt`, `meroPolarPartAt`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 880-885

### `theorem meroPolarPartAt_differentiableAt`
- **Type**: `{f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) {z : ℂ} (hz : z ≠ s) → DifferentiableAt ℂ (meroPolarPartAt hMero) z`
- **What**: The mero polar part is differentiable at any `z ≠ s`.
- **How**: `DifferentiableAt.fun_sum`, each summand by `differentiableAt_const.div` with `(differentiableAt_id.sub (differentiableAt_const _)).pow` and `pow_ne_zero` from `sub_ne_zero.mpr hz`.
- **Hypotheses**: `z ≠ s`.
- **Uses from project**: `meroPolarPartAt`.
- **Used by**: `PolarPartDecomposition.ofMeromorphicWithCondB`.
- **Visibility**: public
- **Lines**: 888-895

### `theorem meroPolarPartAt_analyticAt_off`
- **Type**: `{f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) {w : ℂ} (hw : w ≠ s) → AnalyticAt ℂ (meroPolarPartAt hMero) w`
- **What**: The mero polar part is analytic at any `w ≠ s`.
- **How**: `Finset.analyticAt_fun_sum`; each summand `analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)` with `pow_ne_zero` from `sub_ne_zero.mpr hw`.
- **Hypotheses**: `w ≠ s`.
- **Uses from project**: `meroPolarPartAt`.
- **Used by**: `mero_otherPolar_analyticAt`.
- **Visibility**: public
- **Lines**: 898-904

### `theorem meroPolarPartAt_eq_sum`
- **Type**: `{f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) (z : ℂ) → meroPolarPartAt hMero z = ∑ k : Fin (meroPolarOrderAt hMero), meroPolarCoeffAt hMero k / (z - s)^(k.val + 1)`
- **What**: The mero polar part written in canonical `order`/`coeff` form.
- **How**: Unfolds the three definitions; `rfl`.
- **Hypotheses**: none beyond signature.
- **Uses from project**: `meroPolarPartAt`, `meroPolarOrderAt`, `meroPolarCoeffAt`.
- **Used by**: `PolarPartDecomposition.ofMeromorphicWithCondB`.
- **Visibility**: public
- **Lines**: 907-913

### `theorem meroPolarCoeffAt_zero_eq_residue`
- **Type**: `{f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) (h_pos : 0 < meroPolarOrderAt hMero) → meroPolarCoeffAt hMero ⟨0, h_pos⟩ = residue f s`
- **What**: The leading mero Laurent coefficient `a₀` equals the residue at `s`.
- **How**: Sets `N`, `a`, `g` from `mero_laurent_data_exists`; applies `residue_of_laurent_expansion`; rewrites `dif_pos`; unfolds `meroPolarCoeffAt`.
- **Hypotheses**: positive order.
- **Uses from project**: `mero_laurent_data_exists`, `meroPolarOrderAt`, `meroPolarCoeffAt`, `residue`, `residue_of_laurent_expansion`.
- **Used by**: `PolarPartDecomposition.ofMeromorphicWithCondB`.
- **Visibility**: public
- **Lines**: 916-931

### `noncomputable def meroPolarPartTotal`
- **Type**: `{S : Finset ℂ} {f : ℂ → ℂ} (hMero : ∀ s ∈ S, MeromorphicAt f s) (z : ℂ) : ℂ`
- **What**: Total polar part: sum over `S.attach` using `MeromorphicAt` data.
- **How**: `∑ s ∈ S.attach, meroPolarPartAt (hMero s.1 s.2) z`.
- **Hypotheses**: meromorphicity at every point of `S`.
- **Uses from project**: `meroPolarPartAt`.
- **Used by**: `mero_f_minus_total_eventuallyEq_analytic`, `PolarPartDecomposition.ofMeromorphicWithCondB`.
- **Visibility**: public
- **Lines**: 937-939

### `private theorem mero_otherPolar_analyticAt`
- **Type**: `{S : Finset ℂ} {f : ℂ → ℂ} (hMero : ∀ s ∈ S, MeromorphicAt f s) {s : ℂ} (_hs : s ∈ S) → AnalyticAt ℂ (fun z => ∑ s' ∈ S.attach.filter (·.1 ≠ s), meroPolarPartAt (hMero s'.1 s'.2) z) s`
- **What**: Sum of mero polar parts at other poles is analytic at `s`.
- **How**: `Finset.analyticAt_fun_sum`, each summand by `meroPolarPartAt_analyticAt_off (hMero s'.1 s'.2) h_ne.symm`.
- **Hypotheses**: `s ∈ S` (vacuous), all poles meromorphic.
- **Uses from project**: `meroPolarPartAt`, `meroPolarPartAt_analyticAt_off`.
- **Used by**: `mero_f_minus_total_eventuallyEq_analytic`.
- **Visibility**: private
- **Lines**: 943-949

### `private theorem mero_f_minus_total_eventuallyEq_analytic`
- **Type**: `{S : Finset ℂ} {f : ℂ → ℂ} (hMero) {s : ℂ} (hs : s ∈ S) → ∃ g_s : ℂ → ℂ, AnalyticAt ℂ g_s s ∧ ∀ᶠ z in 𝓝[≠] s, f z - meroPolarPartTotal hMero z = g_s z`
- **What**: Near `s ∈ S`, `f - polarPartTotal` is analytic at `s`.
- **How**: Sets `g_s = analyticPart s - ∑_{s' ≠ s} polarPart s'`, uses `mero_f_eq_analyticPart_plus_polarPart_eventually`. Splits the total via `Finset.sum_filter_add_sum_filter_not S.attach`, identifies the singleton `S.attach.filter (·.1 = s) = {⟨s, hs⟩}` via `Finset.mem_filter`, `Fin.ext`.
- **Hypotheses**: `s ∈ S`, meromorphicity at every pole.
- **Uses from project**: `meroAnalyticPartAt`, `meroAnalyticPartAt_analyticAt`, `meroPolarPartAt`, `meroPolarPartTotal`, `mero_f_eq_analyticPart_plus_polarPart_eventually`, `mero_otherPolar_analyticAt`.
- **Used by**: `PolarPartDecomposition.ofMeromorphicWithCondB`.
- **Visibility**: private
- **Lines**: 954-986
- **Notes**: proof ≈33 lines.

### `noncomputable def PolarPartDecomposition.ofMeromorphicWithCondB`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U \ ↑S)) {γ : PwC1Immersion x x} (hMero : ∀ s ∈ S, MeromorphicAt f s) (_hCondB : SatisfiesConditionB γ f S) → PolarPartDecomposition f S U`
- **What**: **New constructor**: builds `PolarPartDecomposition` from meromorphicity at every pole — handles **both crossed and uncrossed** poles (no `hAllCrossed`).
- **How**: Tactic-mode construction parallel to `ofConditionB` but using `mero*` family instead. Sets `polarPart`, `order`, `coeff` via `if-then-else` using `meroPolarPartAt`, `meroPolarOrderAt`, `meroPolarCoeffAt`. Refines 4 obligations: `polarPart_eq` via `meroPolarPartAt_eq_sum`; `residue_eq` via `meroPolarCoeffAt_zero_eq_residue` and `residue_of_laurent_expansion`; `analyticRemainder_diff` (case `z ∈ S` via `mero_f_minus_total_eventuallyEq_analytic`, `congr_of_eventuallyEq`; case `z ∉ S` via `hU_open.sdiff`, `DifferentiableAt.fun_sum`, `meroPolarPartAt_differentiableAt`); `decomp` (algebra). `hCondB` kept for downstream use but unused in body.
- **Hypotheses**: open `U`, `S ⊆ U`, differentiability off `S`, meromorphicity at every pole, condition (B) (unused but in signature).
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `PolarPartDecomposition`, `meroPolarPartAt`, `meroPolarPartAt_differentiableAt`, `meroPolarOrderAt`, `meroPolarCoeffAt`, `meroPolarCoeffAt_zero_eq_residue`, `meroPolarPartAt_eq_sum`, `meroPolarPartTotal`, `mero_laurent_data_exists`, `residue_of_laurent_expansion`, `mero_f_minus_total_eventuallyEq_analytic`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 1004-1126
- **Notes**: proof ≈122 lines; near-mirror of `ofConditionB` for mero data.

---

## File Summary

- **Total declarations**: 38
  - **Defs**: `IsCrossed`, `crossingParam`, `laurentPolarPartAt`, `laurentPolarOrderAt`, `laurentPolarCoeffAt`, `laurentAnalyticPartAt`, `laurentPolarPartTotal`, `PolarPartDecomposition.ofConditionB`, `meroPolarPartAt`, `meroPolarOrderAt`, `meroPolarCoeffAt`, `meroAnalyticPartAt`, `meroPolarPartTotal`, `PolarPartDecomposition.ofMeromorphicWithCondB` (14)
  - **Theorems/Lemmas**: 24
- **Private**: `laurent_data_exists`, `laurentAnalyticPartAt_eq_data`, `laurentPolarPartAt_eq_data`, `laurentPolarPartAt_uncrossed`, `laurentPolarOrderAt_eq_data`, `laurentPolarOrderAt_uncrossed`, `circleIntegral_higherOrder_eq_zero`, `circleIntegral_higherOrder_sum_eq_zero`, `otherPolar_analyticAt`, `f_minus_total_eventuallyEq_analytic`, `analyticAt_peel_one`, `analyticAt_taylor_decomp`, `pow_div_pow_neg`, `reindex_sum_fin_neg`, `mero_otherPolar_analyticAt`, `mero_f_minus_total_eventuallyEq_analytic`.
- **Key public API**: `IsCrossed`, `crossingParam`, `laurentPolarPartAt`, `laurentPolarOrderAt`, `laurentPolarCoeffAt`, `laurentAnalyticPartAt`, `laurentAnalyticPartAt_analyticAt`, `f_eq_analyticPart_plus_polarPart_eventually`, `laurentPolarPartAt_eq_sum`, `laurentPolarCoeffAt_zero_eq_residue`, `residue_of_laurent_expansion`, `PolarPartDecomposition.ofConditionB`, `mero_laurent_data_exists`, `meroPolarPartAt`, `meroPolarOrderAt`, `meroPolarCoeffAt`, `meroAnalyticPartAt`, `meroAnalyticPartAt_analyticAt`, `mero_f_eq_analyticPart_plus_polarPart_eventually`, `meroPolarPartAt_eq_sum`, `meroPolarCoeffAt_zero_eq_residue`, `PolarPartDecomposition.ofMeromorphicWithCondB`.
- **Unused in file**: `crossingParam_mem_Ioo`, `γ_at_crossingParam` (only via `laurent_data_exists`), `f_minus_polarPartAt_eventuallyEq_analyticPartAt`, `mero_f_minus_polarPartAt_eventuallyEq_analyticPartAt`, `PolarPartDecomposition.ofConditionB`, `PolarPartDecomposition.ofMeromorphicWithCondB` (terminal public APIs).
- **Sorries**: 0.
- **Axioms / `native_decide` / TODOs**: none.
- **`set_option`**: none.
- **Long proofs (>30 lines)**: `circleIntegral_higherOrder_sum_eq_zero` (~30), `residue_of_laurent_expansion` (~128), `laurentPolarPartAt_eq_sum` (~18 — borderline), `f_minus_total_eventuallyEq_analytic` (~35), `PolarPartDecomposition.ofConditionB` (~122), `mero_laurent_data_exists` (~52), `mero_f_minus_total_eventuallyEq_analytic` (~33), `PolarPartDecomposition.ofMeromorphicWithCondB` (~122).

**File purpose**: Extracts Laurent decomposition data `(N, a, g)` for the Hungerbuhler–Wasem residue theorem (Theorem 3.3) and constructs the `PolarPartDecomposition` structure. Provides **two parallel data extraction pipelines**: (1) the `laurent*` family extracts data directly from `SatisfiesConditionB.laurent_compatible` for crossed poles only (constructor `PolarPartDecomposition.ofConditionB` requires `hAllCrossed`); (2) the `mero*` family extracts data uniformly from `MeromorphicAt` via Taylor decomposition of the analytic factorization, handling both crossed and uncrossed poles (constructor `PolarPartDecomposition.ofMeromorphicWithCondB` does not need `hAllCrossed`). Key theorem `residue_of_laurent_expansion` computes the residue as the leading Laurent coefficient `a₀` via circle integration (analytic part contributes 0, simple pole term contributes `2πi · a₀`, higher-order terms contribute 0 by `circleIntegral.integral_sub_zpow_of_ne`). The `mero_laurent_data_exists` theorem provides a generic extraction of Laurent form from any meromorphic-at-point function, using a Taylor decomposition (`analyticAt_taylor_decomp`) and a `Fin` reindexing (`reindex_sum_fin_neg`).
