# Inventory: HW33LaurentPolarPart.lean

### `def IsCrossed`
- **Type**: `(γ : PwC1Immersion x x) (s : ℂ) : Prop := ∃ t₀ ∈ Set.Ioo (0 : ℝ) 1, (γ : ℝ → ℂ) t₀ = s`
- **What**: Predicate: pole `s` is crossed by `γ` at some interior parameter.
- **How**: Definition only.
- **Hypotheses**: none.
- **Uses from project**: `PwC1Immersion`
- **Used by**: `crossingParam`, `crossingParam_mem_Ioo`, `γ_at_crossingParam`, `laurent_data_exists`, and the polar/analytic part definitions.
- **Visibility**: public
- **Lines**: 50–51

### `noncomputable def crossingParam`
- **Type**: `(γ : PwC1Immersion x x) (s : ℂ) : ℝ := if h : IsCrossed γ s then Classical.choose h else 0`
- **What**: Selector for the crossing parameter `t₀ ∈ (0,1)` of pole `s` (default `0` if uncrossed).
- **How**: Definition via `Classical.choose`.
- **Hypotheses**: none.
- **Uses from project**: `IsCrossed`
- **Used by**: `crossingParam_mem_Ioo`, `γ_at_crossingParam`, `laurent_data_exists`
- **Visibility**: public, `noncomputable`
- **Lines**: 56–57

### `theorem crossingParam_mem_Ioo`
- **Type**: `{γ : PwC1Immersion x x} {s : ℂ} (h : IsCrossed γ s) : crossingParam γ s ∈ Set.Ioo (0 : ℝ) 1`
- **What**: `crossingParam` lies in `(0,1)` whenever `IsCrossed γ s`.
- **How**: `simp` unfolds via `dif_pos h`, then `(Classical.choose_spec h).1`.
- **Hypotheses**: `IsCrossed γ s`.
- **Uses from project**: `IsCrossed`, `crossingParam`
- **Used by**: `laurent_data_exists`
- **Visibility**: public
- **Lines**: 59–62

### `theorem γ_at_crossingParam`
- **Type**: `{γ : PwC1Immersion x x} {s : ℂ} (h : IsCrossed γ s) : (γ : ℝ → ℂ) (crossingParam γ s) = s`
- **What**: At the crossing parameter, γ evaluates to `s`.
- **How**: `simp` + `(Classical.choose_spec h).2`.
- **Hypotheses**: `IsCrossed γ s`.
- **Uses from project**: `IsCrossed`, `crossingParam`
- **Used by**: `laurent_data_exists`
- **Visibility**: public
- **Lines**: 64–67

### `private theorem laurent_data_exists`
- **Type**: `{γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S) (h_cross : IsCrossed γ s) : ∃ (N : ℕ) (a : Fin N → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g s ∧ (∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) ∧ (∀ k : Fin N, a k ≠ 0 → k.val ≥ 1 → ∃ m : ℤ, (↑k.val : ℝ) * angleAtCrossing γ (crossingParam γ s) (crossingParam_mem_Ioo h_cross) = ↑m * (2 * Real.pi))`
- **What**: Existential extraction of condition (B)'s Laurent compatibility data at a crossed pole.
- **How**: `Set.Ioo_subset_Icc_self` gives `Icc`-membership; apply `hCondB.laurent_compatible s hs (crossingParam γ s) ht_mem (γ_at_crossingParam h_cross) (crossingParam_mem_Ioo h_cross)`.
- **Hypotheses**: `SatisfiesConditionB γ f S`, `s ∈ S`, `IsCrossed γ s`.
- **Uses from project**: `SatisfiesConditionB`, `IsCrossed`, `crossingParam`, `crossingParam_mem_Ioo`, `γ_at_crossingParam`, `angleAtCrossing`, `SatisfiesConditionB.laurent_compatible`
- **Used by**: `laurentPolarPartAt`, `laurentAnalyticPartAt`, `laurentAnalyticPartAt_analyticAt`, `laurentAnalyticPartAt_eq_data`, `laurentPolarPartAt_eq_data`, `f_eq_analyticPart_plus_polarPart_eventually`
- **Visibility**: private
- **Lines**: 74–87

### `noncomputable def laurentPolarPartAt`
- **Type**: `{γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S) (z : ℂ) : ℂ`
- **What**: Local polar part at pole `s`: `∑ k ∈ Fin N, a_k / (z - s)^(k+1)` if crossed, else 0.
- **How**: Definition with single `if h : IsCrossed γ s` using `laurent_data_exists hCondB hs h` to access `N`, `a`.
- **Hypotheses**: `SatisfiesConditionB γ f S`, `s ∈ S`.
- **Uses from project**: `PwC1Immersion`, `SatisfiesConditionB`, `IsCrossed`, `laurent_data_exists`
- **Used by**: `laurentPolarPartTotal`, `laurentPolarPartAt_eq_data`, `f_eq_analyticPart_plus_polarPart_eventually`, `f_minus_polarPartAt_eventuallyEq_analyticPartAt`, `laurentPolarPartAt_differentiableAt`, `laurentHigherOrderPolarAt`, and downstream.
- **Visibility**: public, `noncomputable`
- **Lines**: 97–104

### `noncomputable def laurentPolarPartTotal`
- **Type**: `{γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (z : ℂ) : ℂ := ∑ s ∈ S.attach, laurentPolarPartAt hCondB s.1 s.2 z`
- **What**: Total polar part: sum over `S` of per-pole local polar parts.
- **How**: Definition.
- **Hypotheses**: `SatisfiesConditionB γ f S`.
- **Uses from project**: `laurentPolarPartAt`, `SatisfiesConditionB`
- **Used by**: unused in file
- **Visibility**: public, `noncomputable`
- **Lines**: 107–109

### `noncomputable def laurentAnalyticPartAt`
- **Type**: `{γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S) : ℂ → ℂ`
- **What**: The analytic remainder `g` from condition (B)'s Laurent compatibility at a crossed pole (0 if uncrossed).
- **How**: `if h : IsCrossed γ s` selects `(laurent_data_exists hCondB hs h).choose_spec.choose_spec.choose`, else `0`.
- **Hypotheses**: `SatisfiesConditionB γ f S`, `s ∈ S`.
- **Uses from project**: `SatisfiesConditionB`, `IsCrossed`, `laurent_data_exists`
- **Used by**: `laurentAnalyticPartAt_analyticAt`, `laurentAnalyticPartAt_eq_data`, `f_eq_analyticPart_plus_polarPart_eventually`, `f_minus_polarPartAt_eventuallyEq_analyticPartAt`, `laurentHigherOrderPolarAt_eventuallyEq_analytic_of_crossed`, `laurentHolomorphicRemainder_eventuallyEq_analyticAt`
- **Visibility**: public, `noncomputable`
- **Lines**: 122–127

### `theorem laurentAnalyticPartAt_analyticAt`
- **Type**: `{γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S) (h_cross : IsCrossed γ s) : AnalyticAt ℂ (laurentAnalyticPartAt hCondB s hs) s`
- **What**: Analytic part is analytic at `s` (for crossed `s`).
- **How**: `unfold` + `dif_pos h_cross`, then `.choose_spec.choose_spec.choose_spec.1`.
- **Hypotheses**: `SatisfiesConditionB γ f S`, `s ∈ S`, `IsCrossed γ s`.
- **Uses from project**: `laurentAnalyticPartAt`, `laurent_data_exists`
- **Used by**: `laurentHolomorphicRemainder_eventuallyEq_analyticAt`
- **Visibility**: public
- **Lines**: 130–136

### `private lemma laurentAnalyticPartAt_eq_data`
- **Type**: `... laurentAnalyticPartAt hCondB s hs = (laurent_data_exists hCondB hs h_cross).choose_spec.choose_spec.choose`
- **What**: Definitional unfolding helper.
- **How**: `unfold` + `simp [dif_pos h_cross]`.
- **Hypotheses**: as in `laurentAnalyticPartAt_analyticAt`.
- **Uses from project**: `laurentAnalyticPartAt`, `laurent_data_exists`
- **Used by**: `f_eq_analyticPart_plus_polarPart_eventually`
- **Visibility**: private
- **Lines**: 139–145

### `private lemma laurentPolarPartAt_eq_data`
- **Type**: `... laurentPolarPartAt hCondB s hs z = ∑ k : Fin N, aₖ / (z - s) ^ (k.val + 1)` (the data-defined Laurent sum)
- **What**: Definitional unfolding helper for polar part.
- **How**: `unfold` + `simp [dif_pos h_cross]`.
- **Hypotheses**: `SatisfiesConditionB γ f S`, `s ∈ S`, `IsCrossed γ s`.
- **Uses from project**: `laurentPolarPartAt`, `laurent_data_exists`
- **Used by**: `f_eq_analyticPart_plus_polarPart_eventually`
- **Visibility**: private
- **Lines**: 148–157

### `theorem f_eq_analyticPart_plus_polarPart_eventually`
- **Type**: `{γ ...} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S) (h_cross : IsCrossed γ s) : ∀ᶠ z in 𝓝[≠] s, f z = laurentAnalyticPartAt hCondB s hs z + laurentPolarPartAt hCondB s hs z`
- **What**: Local Laurent decomposition: `f = analyticPart + polarPart` eventually in punctured nhd.
- **How**: Extract `h_data := (...).choose_spec.choose_spec.choose_spec.2.1`. `filter_upwards [h_data]`, `rw [hz, laurentPolarPartAt_eq_data]`, `congr 1`, `congrArg (· z)` of `laurentAnalyticPartAt_eq_data ...sym`.
- **Hypotheses**: `SatisfiesConditionB γ f S`, `s ∈ S`, `IsCrossed γ s`.
- **Uses from project**: `laurentAnalyticPartAt`, `laurentPolarPartAt`, `laurent_data_exists`, `laurentPolarPartAt_eq_data`, `laurentAnalyticPartAt_eq_data`
- **Used by**: `f_minus_polarPartAt_eventuallyEq_analyticPartAt`, `laurentHigherOrderPolarAt_eventuallyEq_analytic_of_crossed`, `laurentHolomorphicRemainder_eventuallyEq_analyticAt`
- **Visibility**: public
- **Lines**: 164–175

### `theorem f_minus_polarPartAt_eventuallyEq_analyticPartAt`
- **Type**: `... (fun z => f z - laurentPolarPartAt hCondB s hs z) =ᶠ[𝓝[≠] s] laurentAnalyticPartAt hCondB s hs`
- **What**: Corollary: `f - polarPart = analyticPart` eventually near a crossed `s`.
- **How**: `filter_upwards [f_eq_analyticPart_plus_polarPart_eventually ...]`, `rw [hz]; ring`.
- **Hypotheses**: as before.
- **Uses from project**: `f_eq_analyticPart_plus_polarPart_eventually`, `laurentPolarPartAt`, `laurentAnalyticPartAt`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 179–187

### `theorem laurentPolarPartAt_differentiableAt`
- **Type**: `{γ ...} {z : ℂ} (hz : z ≠ s) : DifferentiableAt ℂ (laurentPolarPartAt hCondB s hs) z`
- **What**: `laurentPolarPartAt s` is differentiable at every `z ≠ s`.
- **How**: `unfold` + by_cases on `IsCrossed γ s`. Crossed: `DifferentiableAt.fun_sum`; each `a_k / (z - s)^(k+1)` is `const.div ((id - const).pow ...)` with non-vanishing power from `pow_ne_zero ... (sub_ne_zero.mpr hz)`. Uncrossed: `differentiableAt_const`.
- **Hypotheses**: `SatisfiesConditionB γ f S`, `s ∈ S`, `z ≠ s`.
- **Uses from project**: `laurentPolarPartAt`, `IsCrossed`
- **Used by**: `laurentHigherOrderPolarAt_differentiableAt`
- **Visibility**: public
- **Lines**: 192–207

### `noncomputable def laurentHigherOrderPolarAt`
- **Type**: `... → (s : ℂ) → (hs : s ∈ S) → (z : ℂ) → ℂ`
- **What**: Per-pole higher-order polar part: `laurentPolarPartAt s - residue f s / (z - s)` (crossed) or `0` (uncrossed).
- **How**: Definition with `if IsCrossed γ s then ... else 0`.
- **Hypotheses**: `SatisfiesConditionB γ f S`, `s ∈ S`.
- **Uses from project**: `IsCrossed`, `laurentPolarPartAt`, `residue`
- **Used by**: `laurentHigherOrderPolar`, `laurentHigherOrderPolarAt_differentiableAt`, `laurentHigherOrderPolarAt_eventuallyEq_analytic_of_crossed`, `laurentHigherOrderPolarAt_analyticAt_of_ne`, `laurentHigherOrderPolar_rest`, `laurentHigherOrderPolar_eq_term_add_rest`, `laurentHolomorphicRemainder_eventuallyEq_analyticAt`
- **Visibility**: public, `noncomputable`
- **Lines**: 232–237

### `noncomputable def laurentHigherOrderPolar`
- **Type**: `{γ ...} (z : ℂ) : ℂ := ∑ s ∈ S.attach, laurentHigherOrderPolarAt hCondB s.1 s.2 z`
- **What**: Total higher-order polar part: sum over `S` of per-pole guarded contributions.
- **How**: Definition.
- **Hypotheses**: `SatisfiesConditionB γ f S`.
- **Uses from project**: `laurentHigherOrderPolarAt`
- **Used by**: `laurentHolomorphicRemainder`, `f_minus_pp_eq_higherOrder_plus_holo`, `laurentHigherOrderPolar_differentiableAt`, `laurentHigherOrderPolar_eq_term_add_rest`, `laurentHolomorphicRemainder_eventuallyEq_analyticAt`
- **Visibility**: public, `noncomputable`
- **Lines**: 241–243

### `noncomputable def laurentHolomorphicRemainder`
- **Type**: `{γ ...} (z : ℂ) : ℂ := f z - principalPartSum S (fun s => residue f s) z - laurentHigherOrderPolar hCondB z`
- **What**: Holomorphic remainder in the refactored decomposition.
- **How**: Definition.
- **Hypotheses**: `SatisfiesConditionB γ f S`.
- **Uses from project**: `principalPartSum`, `residue`, `laurentHigherOrderPolar`
- **Used by**: `f_minus_pp_eq_higherOrder_plus_holo`, `laurentHolomorphicRemainder_differentiableOn`, `laurentHolomorphicRemainder_eventuallyEq_analyticAt`, `laurentHolomorphicRemainder_residue_zero`
- **Visibility**: public, `noncomputable`
- **Lines**: 256–259

### `theorem f_minus_pp_eq_higherOrder_plus_holo`
- **Type**: `{γ ...} (z : ℂ) : f z - principalPartSum S (fun s => residue f s) z = laurentHigherOrderPolar hCondB z + laurentHolomorphicRemainder hCondB z`
- **What**: Algebraic decomposition for `hCancel` discharge.
- **How**: `simp only [laurentHolomorphicRemainder]; ring`.
- **Hypotheses**: `SatisfiesConditionB γ f S`.
- **Uses from project**: `laurentHigherOrderPolar`, `laurentHolomorphicRemainder`, `principalPartSum`, `residue`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 266–272

### `theorem laurentHigherOrderPolarAt_differentiableAt`
- **Type**: `{γ ...} {z : ℂ} (hz : z ≠ s) : DifferentiableAt ℂ (laurentHigherOrderPolarAt hCondB s hs) z`
- **What**: Per-pole higher-order polar part is differentiable at every `z ≠ s`.
- **How**: `unfold` + by_cases on `IsCrossed γ s`. Crossed: `(laurentPolarPartAt_differentiableAt hCondB hs hz).fun_sub` minus `const.div (id.sub const)` with `sub_ne_zero.mpr hz`. Uncrossed: `differentiableAt_const`.
- **Hypotheses**: `SatisfiesConditionB γ f S`, `s ∈ S`, `z ≠ s`.
- **Uses from project**: `laurentHigherOrderPolarAt`, `IsCrossed`, `laurentPolarPartAt_differentiableAt`
- **Used by**: `laurentHigherOrderPolar_differentiableAt`, `laurentHigherOrderPolarAt_analyticAt_of_ne`
- **Visibility**: public
- **Lines**: 277–290

### `theorem laurentHigherOrderPolar_differentiableAt`
- **Type**: `{γ ...} {z : ℂ} (hz : z ∉ (↑S : Set ℂ)) : DifferentiableAt ℂ (laurentHigherOrderPolar hCondB) z`
- **What**: Total higher-order polar part differentiable away from `S`.
- **How**: `DifferentiableAt.fun_sum`; each `s : S.attach` has `s.2 : s.1 ∈ S` and `z ≠ s.1` (via `Finset.mem_coe`).
- **Hypotheses**: `SatisfiesConditionB γ f S`, `z ∉ S`.
- **Uses from project**: `laurentHigherOrderPolar`, `laurentHigherOrderPolarAt_differentiableAt`
- **Used by**: `laurentHolomorphicRemainder_differentiableOn`
- **Visibility**: public
- **Lines**: 293–301

### `theorem principalPartSum_differentiableAt`
- **Type**: `(S : Finset ℂ) (c : ℂ → ℂ) {z : ℂ} (hz : z ∉ (↑S : Set ℂ)) : DifferentiableAt ℂ (principalPartSum S c) z`
- **What**: `principalPartSum` is differentiable away from `S`.
- **How**: `DifferentiableAt.fun_sum`; each `c t / (z - t)` differentiable via `(differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _))` with `sub_ne_zero` from `hz`.
- **Hypotheses**: `z ∉ S`.
- **Uses from project**: `principalPartSum`
- **Used by**: `laurentHolomorphicRemainder_differentiableOn`
- **Visibility**: public
- **Lines**: 304–313

### `theorem laurentHolomorphicRemainder_differentiableOn`
- **Type**: `{γ ...} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ ↑S)) : DifferentiableOn ℂ (laurentHolomorphicRemainder hCondB) (U \ ↑S)`
- **What**: Holomorphic remainder differentiable on `U \ S`.
- **How**: Use `hU.sdiff (Finite.isClosed (toFinite ↑S))` to get open `U \ ↑S`, lift to `DifferentiableAt ℂ f z` via `(hf z hz).differentiableAt (hU_open_diff.mem_nhds hz)`, then subtract `principalPartSum_differentiableAt` and `laurentHigherOrderPolar_differentiableAt`.
- **Hypotheses**: `U` open, `f` differentiable on `U \ S`.
- **Uses from project**: `laurentHolomorphicRemainder`, `principalPartSum_differentiableAt`, `laurentHigherOrderPolar_differentiableAt`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 316–327

### `private theorem laurentHigherOrderPolarAt_eventuallyEq_analytic_of_crossed`
- **Type**: `... (h_pole : HasSimplePoleAt f s) : (fun z => laurentHigherOrderPolarAt hCondB s hs z) =ᶠ[𝓝[≠] s] (fun z => h_pole.regularPart z - laurentAnalyticPartAt hCondB s hs z)`
- **What**: At a crossed simple pole, the per-pole higher-order polar part is eventually equal to `regularPart f - analyticPart`.
- **How**: From `h_pole.eventually_eq` (gives `f = coeff/(z-s) + regularPart`) and `f_eq_analyticPart_plus_polarPart_eventually` (gives `f = analyticPart + polarPart`). `residue_eq_coeff` identifies `coeff = residue f s`. `filter_upwards` both, simplify `laurentHigherOrderPolarAt = polarPart - residue/(z-s)` via `if_pos h_cross`, conclude with `linear_combination hpole - hlaurent`.
- **Hypotheses**: `SatisfiesConditionB γ f S`, `s ∈ S`, crossed, `HasSimplePoleAt f s`.
- **Uses from project**: `laurentHigherOrderPolarAt`, `laurentPolarPartAt`, `laurentAnalyticPartAt`, `f_eq_analyticPart_plus_polarPart_eventually`, `HasSimplePoleAt`, `residue_eq_coeff`, `residue`
- **Used by**: unused in file (subsumed by inline argument in `laurentHolomorphicRemainder_eventuallyEq_analyticAt`)
- **Visibility**: private
- **Lines**: 342–363

### `private theorem laurentHigherOrderPolarAt_analyticAt_of_ne`
- **Type**: `... (ht : t ∈ S) (h_ne : t ≠ s) : AnalyticAt ℂ (laurentHigherOrderPolarAt hCondB t ht) s`
- **What**: The per-pole higher-order term at `t ≠ s` is analytic at `s`.
- **How**: `analyticAt_iff_eventually_differentiableAt`, take open nhd `{t}ᶜ`, `filter_upwards`, apply `laurentHigherOrderPolarAt_differentiableAt hCondB ht (mem_compl_singleton_iff.mp hz)`.
- **Hypotheses**: `t ∈ S`, `t ≠ s`.
- **Uses from project**: `laurentHigherOrderPolarAt`, `laurentHigherOrderPolarAt_differentiableAt`
- **Used by**: `laurentHigherOrderPolar_rest_analyticAt`
- **Visibility**: private
- **Lines**: 368–376

### `private noncomputable def laurentHigherOrderPolar_rest`
- **Type**: `... (s : ℂ) (_hs : s ∈ S) (z : ℂ) : ℂ := ∑ t ∈ S.attach.filter (fun t => t.1 ≠ s), laurentHigherOrderPolarAt hCondB t.1 t.2 z`
- **What**: The sum-of-other-terms (excluding the `s`-term) of `laurentHigherOrderPolar`.
- **How**: Definition.
- **Hypotheses**: `SatisfiesConditionB γ f S`, `s ∈ S`.
- **Uses from project**: `laurentHigherOrderPolarAt`
- **Used by**: `laurentHigherOrderPolar_rest_analyticAt`, `laurentHigherOrderPolar_eq_term_add_rest`, `laurentHolomorphicRemainder_eventuallyEq_analyticAt`
- **Visibility**: private, `noncomputable`
- **Lines**: 380–384

### `private theorem laurentHigherOrderPolar_rest_analyticAt`
- **Type**: `... : AnalyticAt ℂ (laurentHigherOrderPolar_rest hCondB s hs) s`
- **What**: The "rest" sum is analytic at `s`.
- **How**: `Finset.analyticAt_fun_sum`; each filtered term `t.1 ≠ s` is analytic at `s` via `laurentHigherOrderPolarAt_analyticAt_of_ne`.
- **Hypotheses**: `SatisfiesConditionB γ f S`, `s ∈ S`.
- **Uses from project**: `laurentHigherOrderPolar_rest`, `laurentHigherOrderPolarAt_analyticAt_of_ne`
- **Used by**: `laurentHolomorphicRemainder_eventuallyEq_analyticAt`
- **Visibility**: private
- **Lines**: 387–396

### `private theorem laurentHigherOrderPolar_eq_term_add_rest`
- **Type**: `... : laurentHigherOrderPolar hCondB z = laurentHigherOrderPolarAt hCondB s hs z + laurentHigherOrderPolar_rest hCondB s hs z`
- **What**: Decomposition of total higher-order polar part into `s`-term + rest.
- **How**: Split `S.attach` along `t.1 = s`/`t.1 ≠ s` via `Finset.sum_filter_add_sum_filter_not`, show the `= s` filter equals `{⟨s, hs⟩}` (via `Subtype.ext`), then `Finset.sum_singleton`.
- **Hypotheses**: `SatisfiesConditionB γ f S`, `s ∈ S`.
- **Uses from project**: `laurentHigherOrderPolar`, `laurentHigherOrderPolar_rest`, `laurentHigherOrderPolarAt`
- **Used by**: `laurentHolomorphicRemainder_eventuallyEq_analyticAt`
- **Visibility**: private
- **Lines**: 400–417

### `private theorem principalPartSum_rest_analyticAt_at_s`
- **Type**: `{S : Finset ℂ} {c : ℂ → ℂ} {s : ℂ} (_hs : s ∈ S) : AnalyticAt ℂ (fun z => ∑ t ∈ S.erase s, c t / (z - t)) s`
- **What**: Sum-of-other-terms of `principalPartSum` is analytic at `s`.
- **How**: `Finset.analyticAt_fun_sum`; for each `t ∈ S.erase s`, `Finset.ne_of_mem_erase` gives `t ≠ s` so `(z - t)` is non-vanishing at `s`. Apply `analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hts.symm)`.
- **Hypotheses**: `s ∈ S`.
- **Uses from project**: []
- **Used by**: `laurentHolomorphicRemainder_eventuallyEq_analyticAt`
- **Visibility**: private
- **Lines**: 421–428

### `theorem laurentHolomorphicRemainder_eventuallyEq_analyticAt`
- **Type**: `{γ ...} (hSimple : ∀ s ∈ S, HasSimplePoleAt f s) {s : ℂ} (hs : s ∈ S) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ (laurentHolomorphicRemainder hCondB) =ᶠ[𝓝[≠] s] g`
- **What**: The holomorphic remainder is eventually equal (in `𝓝[≠] s`) to an analytic-at-`s` function.
- **How**: Set `rest_pp := ∑ t ∈ S.erase s, residue f t/(z-t)`, `rest_holo := laurentHigherOrderPolar_rest`; both analytic at `s` (via `principalPartSum_rest_analyticAt_at_s` and `laurentHigherOrderPolar_rest_analyticAt`). `pp_decomp` from `principalPartSum_eq_term_add_rest`, `holo_decomp` from `laurentHigherOrderPolar_eq_term_add_rest`. Then by_cases `h_cross : IsCrossed γ s`: crossed branch sets `g := analyticPart - rest_pp - rest_holo`, filter_upwards on `h_pole.eventually_eq` and `f_eq_analyticPart_plus_polarPart_eventually` and discharges with `ring`. Uncrossed branch sets `g := regularPart - rest_pp - rest_holo`, uses `h_term_zero` (`laurentHigherOrderPolarAt = 0` via `if_neg h_cross`) and `h_pole.regularPart_analyticAt`.
- **Hypotheses**: `SatisfiesConditionB γ f S`, `∀ s ∈ S, HasSimplePoleAt f s`, `s ∈ S`.
- **Uses from project**: `laurentHolomorphicRemainder`, `laurentHigherOrderPolar`, `laurentHigherOrderPolarAt`, `laurentPolarPartAt`, `laurentAnalyticPartAt`, `laurentAnalyticPartAt_analyticAt`, `laurentHigherOrderPolar_rest`, `laurentHigherOrderPolar_rest_analyticAt`, `laurentHigherOrderPolar_eq_term_add_rest`, `principalPartSum_rest_analyticAt_at_s`, `principalPartSum_eq_term_add_rest`, `f_eq_analyticPart_plus_polarPart_eventually`, `HasSimplePoleAt`, `residue_eq_coeff`, `residue`
- **Used by**: `laurentHolomorphicRemainder_residue_zero`
- **Visibility**: public
- **Lines**: 452–503
- **Notes**: 52 lines.

### `theorem laurentHolomorphicRemainder_residue_zero`
- **Type**: `{γ ...} (hSimple : ∀ s ∈ S, HasSimplePoleAt f s) {s : ℂ} (hs : s ∈ S) : residue (laurentHolomorphicRemainder hCondB) s = 0`
- **What**: Holomorphic remainder has zero residue at every pole in `S`.
- **How**: `laurentHolomorphicRemainder_eventuallyEq_analyticAt` to get `g` analytic at `s` with eventual equality, `residue_congr h_evEq`, `residue_eq_zero_of_analyticAt g_an`.
- **Hypotheses**: `SatisfiesConditionB γ f S`, all `s ∈ S` simple poles.
- **Uses from project**: `laurentHolomorphicRemainder_eventuallyEq_analyticAt`, `residue_congr`, `residue_eq_zero_of_analyticAt`, `residue`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 507–515

## File Summary
Laurent polar-part extraction from condition (B) (`SatisfiesConditionB`). Extracts via `Classical.choose` the data `(N, aₖ, g)` from `hCondB.laurent_compatible` and packages as `laurentPolarPartAt`, `laurentAnalyticPartAt`, `laurentHigherOrderPolarAt`, and the global `laurentHolomorphicRemainder`. Main results: local Laurent decomposition `f = analyticPart + polarPart` near each crossed pole; per-pole differentiability away from `s`; `laurentHolomorphicRemainder_differentiableOn (U \ S)`; **TIGHT-2 core**: `laurentHolomorphicRemainder_eventuallyEq_analyticAt` (eventually equal to an analytic function near each pole) and the key consequence `laurentHolomorphicRemainder_residue_zero`. 0 sorry, no `set_option`, no `axiom`.
