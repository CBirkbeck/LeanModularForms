# Inventory: PaperPwC1ImmersionInvariance.lean

### `private def ClosedPwC1Immersion.cpvIntegrandOnPer`
- **Type**: `(γ : ClosedPwC1Immersion x) (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) (u : ℝ) : ℂ`
- **What**: The 1-periodic extension of the cutoff integrand `cpvIntegrandOn S f γ.extend ε` to all of `ℝ`, defined by `cpvIntegrandOn S f γ.extend ε (Int.fract u)`.
- **How**: Definition using `Int.fract`.
- **Hypotheses**: None (definition).
- **Uses from project**: `ClosedPwC1Immersion`, `cpvIntegrandOn`
- **Used by**: `cpvIntegrandOnPer_periodic`, `cpvIntegrandOnPer_eq_on_Ico`, `cpvIntegrandOnPer_eq_on_Ico_one_two`, `cpvIntegrandOn_cyclicShift_eq_per_ae`, `cpvIntegrandOn_cyclicShift_integral_eq`
- **Visibility**: private
- **Lines**: 63-65

### `private lemma ClosedPwC1Immersion.cpvIntegrandOnPer_periodic`
- **Type**: `(γ : ClosedPwC1Immersion x) (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) : Function.Periodic (cpvIntegrandOnPer γ S f ε) 1`
- **What**: The periodic extension is periodic with period 1.
- **How**: Unfold and use `Int.fract_add_one`.
- **Hypotheses**: None.
- **Uses from project**: `cpvIntegrandOnPer`
- **Used by**: `cpvIntegrandOnPer_eq_on_Ico_one_two`, `cpvIntegrandOn_cyclicShift_integral_eq`
- **Visibility**: private
- **Lines**: 68-73

### `private lemma ClosedPwC1Immersion.cpvIntegrandOnPer_eq_on_Ico`
- **Type**: `(γ : ClosedPwC1Immersion x) (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) {u : ℝ} (hu : u ∈ Ico 0 1) : cpvIntegrandOnPer γ S f ε u = cpvIntegrandOn S f γ.toPath.extend ε u`
- **What**: On `[0, 1)`, the periodic extension equals the original cutoff integrand.
- **How**: Use `Int.fract_eq_self` for `u ∈ Ico 0 1`.
- **Hypotheses**: `u ∈ Ico 0 1`.
- **Uses from project**: `cpvIntegrandOnPer`, `cpvIntegrandOn`
- **Used by**: `cpvIntegrandOnPer_eq_on_Ico_one_two`, `cpvIntegrandOn_cyclicShift_eq_per_ae`, `cpvIntegrandOn_cyclicShift_integral_eq`
- **Visibility**: private
- **Lines**: 76-81

### `private lemma ClosedPwC1Immersion.cpvIntegrandOnPer_eq_on_Ico_one_two`
- **Type**: `(γ : ClosedPwC1Immersion x) (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) {u : ℝ} (hu : u ∈ Ico 1 2) : cpvIntegrandOnPer γ S f ε u = cpvIntegrandOn S f γ.toPath.extend ε (u - 1)`
- **What**: On `[1, 2)`, the periodic extension equals the original cutoff integrand shifted by `-1`.
- **How**: Use periodicity `G(u) = G(u - 1)` via `cpvIntegrandOnPer_periodic`, then apply `cpvIntegrandOnPer_eq_on_Ico` to `u - 1 ∈ Ico 0 1`.
- **Hypotheses**: `u ∈ Ico 1 2`.
- **Uses from project**: `cpvIntegrandOnPer`, `cpvIntegrandOnPer_periodic`, `cpvIntegrandOnPer_eq_on_Ico`
- **Used by**: `cpvIntegrandOn_cyclicShift_eq_per_ae`
- **Visibility**: private
- **Lines**: 84-99

### `private lemma ClosedPwC1Immersion.cpvIntegrandOn_cyclicShift_eq_per_ae`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc 0 1 → cpvIntegrandOn S f (γ.cyclicShift hτ).toPath.extend ε t = cpvIntegrandOnPer γ S f ε (t + τ)`
- **What**: The cutoff integrand for the cyclic-shifted curve equals `G(t + τ)` for a.e. `t ∈ uIoc 0 1`, where `G` is the periodic extension. Key technical lemma combining no-wrap and wrap regions.
- **How**: Bad set = shifted-curve partition points (finite, measure zero). For each `t` not in partition, case-split on `t ≤ 1 - τ` (no-wrap, use `cyclicShift_extend_eq_no_wrap`, `cyclicShift_deriv_eq_no_wrap`) vs `t > 1 - τ` (wrap, use `cyclicShift_extend_eq_wrap`, `cyclicShift_deriv_eq_wrap`); show interior crossing avoids `t = 1` and `t = 1 - τ` via partition membership.
- **Hypotheses**: `τ ∈ Ioo 0 1`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `cpvIntegrandOnPer`, `cpvIntegrandOn`, `cpvIntegrandOnPer_eq_on_Ico`, `cpvIntegrandOnPer_eq_on_Ico_one_two`, `oneSubTau_mem_cyclicShiftPartitionExt`, `one_mem_cyclicShiftPartitionExt`, `ClosedPwC1Immersion.cyclicShift_extend_eq_no_wrap`, `ClosedPwC1Immersion.cyclicShift_extend_eq_wrap`, `ClosedPwC1Immersion.cyclicShift_deriv_eq_no_wrap`, `ClosedPwC1Immersion.cyclicShift_deriv_eq_wrap`
- **Used by**: `cpvIntegrandOn_cyclicShift_integral_eq`
- **Visibility**: private
- **Lines**: 105-192
- **Notes**: Proof >30 lines. Uses `Finset.measure_zero`, `MeasureTheory.compl_mem_ae_iff`, `Set.uIoc_of_le`, `filter_upwards`.

### `private lemma ClosedPwC1Immersion.cpvIntegrandOn_cyclicShift_integral_eq`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) : (∫ t in 0..1, cpvIntegrandOn S f (γ.cyclicShift hτ).toPath.extend ε t) = (∫ t in 0..1, cpvIntegrandOn S f γ.toPath.extend ε t)`
- **What**: For each `ε`, the cutoff integrals over `γ_τ` and `γ` are equal.
- **How**: Step 1: rewrite LHS as `∫_0^1 G(t + τ) dt` via `integral_congr_ae` and `cpvIntegrandOn_cyclicShift_eq_per_ae`. Step 2: substitute `u = t + τ` via `intervalIntegral.integral_comp_add_right`. Step 3: shift interval via `Function.Periodic.intervalIntegral_add_eq`. Step 4: relate `G` back to `cpvIntegrandOn` on `[0, 1)` via a.e. equality (off the singleton `{1}`).
- **Hypotheses**: `τ ∈ Ioo 0 1`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `cpvIntegrandOn`, `cpvIntegrandOnPer`, `cpvIntegrandOn_cyclicShift_eq_per_ae`, `cpvIntegrandOnPer_periodic`, `cpvIntegrandOnPer_eq_on_Ico`
- **Used by**: `hasCauchyPVOn_cyclicShift`, `cauchyPVOn_cyclicShift`, `cauchyPV_cyclicShift`
- **Visibility**: private
- **Lines**: 200-239
- **Notes**: Proof >30 lines. Uses `intervalIntegral.integral_congr_ae`, `intervalIntegral.integral_comp_add_right`, `Function.Periodic.intervalIntegral_add_eq`, `Real.volume_singleton`.

### `theorem ClosedPwC1Immersion.hasCauchyPVOn_cyclicShift`
- **Type**: `{γ : ClosedPwC1Immersion x} {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 1) (S : Finset ℂ) (f : ℂ → ℂ) (L : ℂ) : HasCauchyPVOn S f (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path L ↔ HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path L`
- **What**: Invariance of `HasCauchyPVOn` under cyclic shift.
- **How**: Unfold `HasCauchyPVOn`; the two cutoff integrals agree for each `ε` by `cpvIntegrandOn_cyclicShift_integral_eq`; conclude via `Tendsto.congr`.
- **Hypotheses**: `τ ∈ Ioo 0 1`.
- **Uses from project**: `HasCauchyPVOn`, `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `ClosedPwC1Immersion.toPwC1Immersion`, `cpvIntegrandOn_cyclicShift_integral_eq`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 242-254

### `private lemma ClosedPwC1Immersion.limUnder_congr_eventually_local`
- **Type**: `{α β : Type*} [Nonempty β] [TopologicalSpace β] {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) : limUnder l f = limUnder l g`
- **What**: `limUnder` is congruent under `eventuallyEq`.
- **How**: Unfold; apply `Filter.map_congr`.
- **Hypotheses**: `f =ᶠ[l] g`.
- **Uses from project**: []
- **Used by**: `cauchyPVOn_cyclicShift`, `cauchyPV_cyclicShift`
- **Visibility**: private
- **Lines**: 259-263

### `theorem ClosedPwC1Immersion.cauchyPVOn_cyclicShift`
- **Type**: `{γ : ClosedPwC1Immersion x} {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 1) (S : Finset ℂ) (f : ℂ → ℂ) : cauchyPVOn S f (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path = cauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path`
- **What**: The Cauchy principal value as a value (not a `Tendsto` witness) is invariant under cyclic shift.
- **How**: Unfold; apply `limUnder_congr_eventually_local` with `cpvIntegrandOn_cyclicShift_integral_eq` on the whole space.
- **Hypotheses**: `τ ∈ Ioo 0 1`.
- **Uses from project**: `cauchyPVOn`, `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `ClosedPwC1Immersion.toPwC1Immersion`, `limUnder_congr_eventually_local`, `cpvIntegrandOn_cyclicShift_integral_eq`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 267-275

### `private lemma ClosedPwC1Immersion.cauchyPV_cyclicShift`
- **Type**: `{γ : ClosedPwC1Immersion x} {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 1) (z₀ : ℂ) (f : ℂ → ℂ) : cauchyPV f (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path z₀ = cauchyPV f γ.toPwC1Immersion.toPiecewiseC1Path z₀`
- **What**: The CPV in single-pole form is invariant under cyclic shift.
- **How**: Reduce both sides to integrals via `cpvIntegrandOn {z₀}` using `cpvIntegrand_eq_cpvIntegrandOn_singleton`; apply `cpvIntegrandOn_cyclicShift_integral_eq` on `S = {z₀}`.
- **Hypotheses**: `τ ∈ Ioo 0 1`.
- **Uses from project**: `cauchyPV`, `cpvIntegrand`, `cpvIntegrand_eq_cpvIntegrandOn_singleton`, `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `ClosedPwC1Immersion.toPwC1Immersion`, `limUnder_congr_eventually_local`, `cpvIntegrandOn_cyclicShift_integral_eq`
- **Used by**: `generalizedWindingNumber_cyclicShift`
- **Visibility**: private
- **Lines**: 278-308
- **Notes**: Proof >10 lines. Uses `intervalIntegral.integral_congr`.

### `theorem ClosedPwC1Immersion.generalizedWindingNumber_cyclicShift`
- **Type**: `{γ : ClosedPwC1Immersion x} {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 1) (s : ℂ) : generalizedWindingNumber (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path s = generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s`
- **What**: Invariance of `generalizedWindingNumber` under cyclic shift.
- **How**: Simp with `generalizedWindingNumber` definition and `cauchyPV_cyclicShift`.
- **Hypotheses**: `τ ∈ Ioo 0 1`.
- **Uses from project**: `generalizedWindingNumber`, `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `ClosedPwC1Immersion.toPwC1Immersion`, `cauchyPV_cyclicShift`
- **Used by**: `isNullHomologous_cyclicShift`
- **Visibility**: public
- **Lines**: 311-316

### `private lemma ClosedPwC1Immersion.deriv_comp_add_const`
- **Type**: `(g : ℝ → ℂ) (c t : ℝ) : deriv (fun s : ℝ => g (s + c)) t = deriv g (t + c)`
- **What**: Derivative of `g ∘ (·+c)` equals `(deriv g) ∘ (·+c)`, both when `g` is differentiable at `t + c` and when neither side is.
- **How**: Case split: if `g` differentiable, apply `HasDerivAt.scomp` with `HasDerivAt (·+c) 1`; else, both sides are zero by `deriv_zero_of_not_differentiableAt`, proven via composition with `(·-c)`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `deriv_eventuallyEq_of_shift`
- **Visibility**: private
- **Lines**: 327-358
- **Notes**: Proof >30 lines. Uses `HasDerivAt.scomp`, `DifferentiableAt.comp`, `hasDerivAt_id.sub_const`.

### `private lemma ClosedPwC1Immersion.deriv_eventuallyEq_of_shift`
- **Type**: `{f g : ℝ → ℂ} {t₀ c : ℝ} (h_eq : ∀ᶠ t in 𝓝 t₀, f t = g (t + c)) : ∀ᶠ t in 𝓝 t₀, deriv f t = deriv g (t + c)`
- **What**: Eventual derivative agreement under shift: if `f =ᶠ[𝓝 t₀] g ∘ (·+c)`, then `deriv f = (deriv g) ∘ (·+c)` on a neighborhood.
- **How**: Strengthen `h_eq` to "eventually eventually" via `eventually_eventually_nhds`; on each `t`, apply `Filter.EventuallyEq.deriv_eq` and `deriv_comp_add_const`.
- **Hypotheses**: Eventual equality near `t₀`.
- **Uses from project**: `deriv_comp_add_const`
- **Used by**: `isFlatOfOrder_of_eventuallyEq_shift`
- **Visibility**: private
- **Lines**: 362-370

### `private lemma ClosedPwC1Immersion.tendsto_add_const_nhdsGT`
- **Type**: `(t₀ c : ℝ) : Tendsto (fun t : ℝ => t + c) (𝓝[>] t₀) (𝓝[>] (t₀ + c))`
- **What**: `(·+c)` tends from `𝓝[>] t₀` to `𝓝[>] (t₀+c)`.
- **How**: `tendsto_nhdsWithin_iff`; continuity for the main tendsto and `(add_lt_add_iff_right c).mpr` for the right-side filter.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `isFlatOfOrder_of_eventuallyEq_shift`
- **Visibility**: private
- **Lines**: 373-381

### `private lemma ClosedPwC1Immersion.tendsto_add_const_nhdsLT`
- **Type**: `(t₀ c : ℝ) : Tendsto (fun t : ℝ => t + c) (𝓝[<] t₀) (𝓝[<] (t₀ + c))`
- **What**: `(·+c)` tends from `𝓝[<] t₀` to `𝓝[<] (t₀+c)`.
- **How**: Symmetric to `tendsto_add_const_nhdsGT`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `isFlatOfOrder_of_eventuallyEq_shift`
- **Visibility**: private
- **Lines**: 384-392

### `private lemma ClosedPwC1Immersion.tendsto_sub_const_nhdsGT`
- **Type**: `(t₀ c : ℝ) : Tendsto (fun t : ℝ => t - c) (𝓝[>] (t₀ + c)) (𝓝[>] t₀)`
- **What**: `(·-c)` tends from `𝓝[>] (t₀+c)` to `𝓝[>] t₀`.
- **How**: Use continuity at `t₀ + c` (subtracting `c` gives `t₀`), and arithmetic for the right-side filter.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `isFlatOfOrder_of_eventuallyEq_shift`, `angleAtCrossing_cyclicShift_no_wrap`, `angleAtCrossing_cyclicShift_wrap` (indirectly via `_eq_pt`)
- **Visibility**: private
- **Lines**: 395-408

### `private lemma ClosedPwC1Immersion.tendsto_sub_const_nhdsLT`
- **Type**: `(t₀ c : ℝ) : Tendsto (fun t : ℝ => t - c) (𝓝[<] (t₀ + c)) (𝓝[<] t₀)`
- **What**: `(·-c)` tends from `𝓝[<] (t₀+c)` to `𝓝[<] t₀`.
- **How**: Symmetric to `tendsto_sub_const_nhdsGT`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `isFlatOfOrder_of_eventuallyEq_shift`, `angleAtCrossing_cyclicShift_no_wrap`, `angleAtCrossing_cyclicShift_wrap` (indirectly)
- **Visibility**: private
- **Lines**: 411-423

### `private lemma ClosedPwC1Immersion.isFlatOfOrder_of_eventuallyEq_shift`
- **Type**: `{f g : ℝ → ℂ} {t₀ c : ℝ} {n : ℕ} (h_eq : ∀ᶠ t in 𝓝 t₀, f t = g (t + c)) (h_g : IsFlatOfOrder g (t₀ + c) n) : IsFlatOfOrder f t₀ n`
- **What**: Affine-shift transport of `IsFlatOfOrder`: flatness of `g` at `t₀ + c` transports to flatness of `f` at `t₀`.
- **How**: Transport both `right_flat` and `left_flat` separately. For each side: use `h_deriv` (derivative shift) to convert Tendsto on `deriv f` to Tendsto on `deriv g (·+c)`; compose with `tendsto_sub_const_nhds{GT,LT}` to land at `t₀ + c`; apply `h_g.right_flat`/`left_flat`; push the resulting little-o back through `tendsto_add_const_nhds{GT,LT}` and substitute `f` for `g(·+c)` via `congr'`.
- **Hypotheses**: Eventual equality `f = g ∘ (·+c)` near `t₀`, flatness of `g` at `t₀ + c` of order `n`.
- **Uses from project**: `IsFlatOfOrder`, `deriv_eventuallyEq_of_shift`, `tendsto_add_const_nhdsGT`, `tendsto_add_const_nhdsLT`, `tendsto_sub_const_nhdsGT`, `tendsto_sub_const_nhdsLT`
- **Used by**: `satisfiesConditionA'_cyclicShift`
- **Visibility**: private
- **Lines**: 426-476
- **Notes**: Proof >30 lines. Uses `IsFlatOfOrder.right_flat`, `IsFlatOfOrder.left_flat`, `Tendsto.congr'`, `IsLittleO.comp_tendsto`, `sub_add_cancel`.

### `theorem ClosedPwC1Immersion.cyclicShift_image_subset`
- **Type**: `{γ : ClosedPwC1Immersion x} {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 1) : ∀ t ∈ Icc 0 1, ∃ u ∈ Icc 0 1, (γ.cyclicShift hτ).toPath.extend t = γ.toPath.extend u`
- **What**: The image of the cyclic-shifted path lies inside the image of the original path.
- **How**: Case split on `t ≤ 1 - τ` (use `u = t + τ` and `cyclicShift_extend_eq_no_wrap`) vs `t > 1 - τ` (use `u = t + τ - 1` and `cyclicShift_extend_eq_wrap`).
- **Hypotheses**: `τ ∈ Ioo 0 1`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `ClosedPwC1Immersion.cyclicShift_extend_eq_no_wrap`, `ClosedPwC1Immersion.cyclicShift_extend_eq_wrap`
- **Used by**: `isNullHomologous_cyclicShift`
- **Visibility**: public
- **Lines**: 479-493

### `theorem ClosedPwC1Immersion.isNullHomologous_cyclicShift`
- **Type**: `{γ : ClosedPwC1Immersion x} {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 1) {U : Set ℂ} (h : IsNullHomologous γ.toPwC1Immersion U) : IsNullHomologous (γ.cyclicShift hτ).toPwC1Immersion U`
- **What**: Invariance of `IsNullHomologous` under cyclic shift.
- **How**: Build the structure: `image_subset` via `cyclicShift_image_subset`; `winding_zero` via `generalizedWindingNumber_cyclicShift`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, null-homologous for the original curve.
- **Uses from project**: `IsNullHomologous`, `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `ClosedPwC1Immersion.toPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift_image_subset`, `ClosedPwC1Immersion.generalizedWindingNumber_cyclicShift`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 496-509

### `theorem ClosedPwC1Immersion.satisfiesConditionA'_cyclicShift`
- **Type**: `{γ : ClosedPwC1Immersion x} {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 1) {S : Finset ℂ} {f : ℂ → ℂ} {ord : ℂ → ℕ} (h_basepoint_ord : ∀ s ∈ S, γ.toPath.extend 1 = s → ord s ≤ 1) (h : SatisfiesConditionA' γ.toPwC1Immersion f S ord) : SatisfiesConditionA' (γ.cyclicShift hτ).toPwC1Immersion f S ord`
- **What**: Cyclic-shift invariance of `SatisfiesConditionA'` (T-BR-Y9h-A). Pole orders transport along the cyclic shift via affine parameter substitution; at the breakpoint, basepoint hypothesis caps order at 1.
- **How**: Trichotomy on `t₀'` vs `1 - τ`. No-wrap case: `t₀ = t₀' + τ`, apply `h` and transport via `isFlatOfOrder_of_eventuallyEq_shift`. Breakpoint case: use `isFlatOfOrder_one` for the PwC¹ immersion plus `IsFlatOfOrder.of_le` with `h_basepoint_ord`. Wrap case: `t₀ = t₀' + τ - 1`, similar transport.
- **Hypotheses**: `τ ∈ Ioo 0 1`; basepoint order ≤ 1 at `s = γ(1)`; condition A' holds for the original curve.
- **Uses from project**: `SatisfiesConditionA'`, `IsFlatOfOrder`, `IsFlatOfOrder.of_le`, `isFlatOfOrder_one`, `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `ClosedPwC1Immersion.toPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift_extend_eq_no_wrap`, `ClosedPwC1Immersion.cyclicShift_extend_eq_wrap`, `isFlatOfOrder_of_eventuallyEq_shift`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 536-627
- **Notes**: Proof >30 lines. Uses `lt_trichotomy`, `isOpen_Ioo.mem_nhds`, `PwC1Immersion.continuous`.

### `private theorem ClosedPwC1Immersion.mem_cyclicShift_partition_no_wrap_iff`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo 0 (1 - τ)) : t₀' ∈ (γ.cyclicShift hτ).partition ↔ t₀' + τ ∈ γ.partition`
- **What**: For `t₀'` in the no-wrap region, `t₀'` is in the shifted partition iff `t₀' + τ` is in the original partition.
- **How**: Rewrite `cyclicShiftPartitionExt` via `mem_cyclicShiftPartitionExt_iff`; exclude the trivial cases (`t₀' ≠ 0, 1, 1 - τ`) by `ne_of_gt`/`ne_of_lt`; for `t₀' + τ - 1` direction, use `partition_subset` to derive `t₀' + τ - 1 ≥ 0` contradicting `t₀' + τ - 1 < 0`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `t₀' ∈ Ioo 0 (1 - τ)`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `cyclicShiftPartitionExt`, `mem_cyclicShiftPartitionExt_iff`, `mem_cyclicShiftPartition_iff`, `ClosedPwC1Curve.partition_subset`
- **Used by**: `angleAtCrossing_cyclicShift_no_wrap`
- **Visibility**: private
- **Lines**: 651-673
- **Notes**: Proof >10 lines. Uses `Finset.mem_image`, `Finset.mem_insert`.

### `private theorem ClosedPwC1Immersion.mem_cyclicShift_partition_wrap_iff`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (1 - τ) 1) : t₀' ∈ (γ.cyclicShift hτ).partition ↔ t₀' + τ - 1 ∈ γ.partition`
- **What**: Analogue of `mem_cyclicShift_partition_no_wrap_iff` for the wrap region.
- **How**: Symmetric to no-wrap variant; here, `t₀' + τ > 1` would contradict `partition_subset`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `t₀' ∈ Ioo (1 - τ) 1`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `cyclicShiftPartitionExt`, `mem_cyclicShiftPartitionExt_iff`, `mem_cyclicShiftPartition_iff`, `ClosedPwC1Curve.partition_subset`
- **Used by**: `angleAtCrossing_cyclicShift_wrap`
- **Visibility**: private
- **Lines**: 677-699
- **Notes**: Proof >10 lines.

### `private lemma ClosedPwC1Immersion.exists_partition_isolating_nhd_no_wrap`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo 0 (1 - τ)) : ∃ a b : ℝ, a < t₀' ∧ t₀' < b ∧ Ioo a b ⊆ Ioo 0 (1 - τ) ∧ ((↑(γ.cyclicShift hτ).partition : Set ℝ) ∩ Ioo a b) ⊆ {t₀'}`
- **What**: A `Ioo`-neighborhood of `t₀' ∈ Ioo 0 (1 - τ)` whose intersection with the shifted partition is at most `{t₀'}`.
- **How**: Define `δ_box = min t₀' (1 - τ - t₀')`; if `P' = P.erase t₀'` is nonempty, refine with `δ_pre = inf' (fun p => |t₀' - p|)`; take `δ = min δ_box δ_pre`. The neighborhood is `Ioo (t₀' - δ) (t₀' + δ)`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `t₀' ∈ Ioo 0 (1 - τ)`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`
- **Used by**: `deriv_cyclicShift_eventuallyEq_left_no_wrap`, `deriv_cyclicShift_eventuallyEq_right_no_wrap`
- **Visibility**: private
- **Lines**: 703-757
- **Notes**: Proof >30 lines. Uses `Finset.lt_inf'_iff`, `Finset.inf'_le`, `abs_pos`, `abs_lt`.

### `private lemma ClosedPwC1Immersion.exists_partition_isolating_nhd_wrap`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (1 - τ) 1) : ∃ a b : ℝ, a < t₀' ∧ t₀' < b ∧ Ioo a b ⊆ Ioo (1 - τ) 1 ∧ ((↑(γ.cyclicShift hτ).partition : Set ℝ) ∩ Ioo a b) ⊆ {t₀'}`
- **What**: Symmetric `exists_partition_isolating_nhd_no_wrap` for the wrap region.
- **How**: Symmetric structure with `δ_box = min (t₀' - (1 - τ)) (1 - t₀')`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `t₀' ∈ Ioo (1 - τ) 1`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`
- **Used by**: `deriv_cyclicShift_eventuallyEq_left_wrap`, `deriv_cyclicShift_eventuallyEq_right_wrap`
- **Visibility**: private
- **Lines**: 761-811
- **Notes**: Proof >30 lines. Symmetric structure to no-wrap variant.

### `private lemma ClosedPwC1Immersion.deriv_cyclicShift_eventuallyEq_left_no_wrap`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo 0 (1 - τ)) : ∀ᶠ t in 𝓝[<] t₀', deriv (γ.cyclicShift hτ).toPath.extend t = deriv γ.toPath.extend (t + τ)`
- **What**: Eventually on `𝓝[<] t₀'`, the derivative `deriv γ'.extend t = deriv γ.extend (t + τ)`.
- **How**: Take the isolating neighborhood from `exists_partition_isolating_nhd_no_wrap`; `filter_upwards` with `Iio t₀' ∩ Ioo a b`; conclude via `cyclicShift_deriv_eq_no_wrap`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `t₀' ∈ Ioo 0 (1 - τ)`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `exists_partition_isolating_nhd_no_wrap`, `ClosedPwC1Immersion.cyclicShift_deriv_eq_no_wrap`
- **Used by**: `angleAtCrossing_cyclicShift_no_wrap`
- **Visibility**: private
- **Lines**: 817-835
- **Notes**: Proof >10 lines.

### `private lemma ClosedPwC1Immersion.deriv_cyclicShift_eventuallyEq_right_no_wrap`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo 0 (1 - τ)) : ∀ᶠ t in 𝓝[>] t₀', deriv (γ.cyclicShift hτ).toPath.extend t = deriv γ.toPath.extend (t + τ)`
- **What**: Right-side variant of `deriv_cyclicShift_eventuallyEq_left_no_wrap`.
- **How**: Symmetric to left-side variant with `Ioi`.
- **Hypotheses**: As in left-side variant.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `exists_partition_isolating_nhd_no_wrap`, `ClosedPwC1Immersion.cyclicShift_deriv_eq_no_wrap`
- **Used by**: `angleAtCrossing_cyclicShift_no_wrap`
- **Visibility**: private
- **Lines**: 838-856
- **Notes**: Proof >10 lines.

### `private lemma ClosedPwC1Immersion.deriv_cyclicShift_eventuallyEq_left_wrap`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (1 - τ) 1) : ∀ᶠ t in 𝓝[<] t₀', deriv (γ.cyclicShift hτ).toPath.extend t = deriv γ.toPath.extend (t + τ - 1)`
- **What**: Wrap-region analogue of `deriv_cyclicShift_eventuallyEq_left_no_wrap`.
- **How**: Symmetric structure: use `exists_partition_isolating_nhd_wrap` and `cyclicShift_deriv_eq_wrap`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `t₀' ∈ Ioo (1 - τ) 1`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `exists_partition_isolating_nhd_wrap`, `ClosedPwC1Immersion.cyclicShift_deriv_eq_wrap`
- **Used by**: `angleAtCrossing_cyclicShift_wrap`
- **Visibility**: private
- **Lines**: 860-878
- **Notes**: Proof >10 lines.

### `private lemma ClosedPwC1Immersion.deriv_cyclicShift_eventuallyEq_right_wrap`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (1 - τ) 1) : ∀ᶠ t in 𝓝[>] t₀', deriv (γ.cyclicShift hτ).toPath.extend t = deriv γ.toPath.extend (t + τ - 1)`
- **What**: Right-side wrap-region variant.
- **How**: Symmetric to `_left_wrap` with `Ioi`.
- **Hypotheses**: As in `_left_wrap`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `exists_partition_isolating_nhd_wrap`, `ClosedPwC1Immersion.cyclicShift_deriv_eq_wrap`
- **Used by**: `angleAtCrossing_cyclicShift_wrap`
- **Visibility**: private
- **Lines**: 881-899
- **Notes**: Proof >10 lines.

### `private theorem ClosedPwC1Immersion.angleAtCrossing_cyclicShift_no_wrap`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo 0 (1 - τ)) (ht₀'_Ioo : t₀' ∈ Ioo 0 1) (ht₀_Ioo : t₀' + τ ∈ Ioo 0 1) : angleAtCrossing (γ.cyclicShift hτ).toPwC1Immersion t₀' ht₀'_Ioo = angleAtCrossing γ.toPwC1Immersion (t₀' + τ) ht₀_Ioo`
- **What**: `angleAtCrossing` is invariant under cyclic shift for crossings in the no-wrap region.
- **How**: Two cases. (1) `t₀'` is a corner crossing: derive `t₀' + τ ∈ γ.partition` legacy via `mem_cyclicShift_partition_no_wrap_iff`; unfold `angleAtCrossing`; equate the `Classical.choose`-extracted left/right derivative limits by transferring tendsto using `deriv_cyclicShift_eventuallyEq_{left,right}_no_wrap` and `tendsto_nhds_unique`. (2) Smooth case (not a corner): apply `angleAtCrossing_smooth` on both sides.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `t₀' ∈ Ioo 0 (1 - τ)`, `t₀'` and `t₀' + τ` in `Ioo 0 1`.
- **Uses from project**: `angleAtCrossing`, `angleAtCrossing_smooth`, `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `ClosedPwC1Immersion.toPwC1Immersion`, `mem_cyclicShift_partition_no_wrap_iff`, `deriv_cyclicShift_eventuallyEq_left_no_wrap`, `deriv_cyclicShift_eventuallyEq_right_no_wrap`, `tendsto_sub_const_nhdsLT`, `tendsto_sub_const_nhdsGT`
- **Used by**: `satisfiesConditionB_cyclicShift`
- **Visibility**: private
- **Lines**: 904-1010
- **Notes**: Proof >30 lines. Uses `Classical.choose_spec`, `Tendsto.congr'`, `Tendsto.comp`, `tendsto_nhds_unique`, `sub_add_cancel`.

### `private theorem ClosedPwC1Immersion.angleAtCrossing_cyclicShift_wrap`
- **Type**: `(γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (1 - τ) 1) (ht₀'_Ioo : t₀' ∈ Ioo 0 1) (ht₀_Ioo : t₀' + τ - 1 ∈ Ioo 0 1) : angleAtCrossing (γ.cyclicShift hτ).toPwC1Immersion t₀' ht₀'_Ioo = angleAtCrossing γ.toPwC1Immersion (t₀' + τ - 1) ht₀_Ioo`
- **What**: Wrap-region analogue of `angleAtCrossing_cyclicShift_no_wrap`.
- **How**: Symmetric to no-wrap variant; use `mem_cyclicShift_partition_wrap_iff`, `deriv_cyclicShift_eventuallyEq_{left,right}_wrap`. Inverse shift `(·-(τ-1))` needed to land at `t₀' + τ - 1`.
- **Hypotheses**: `τ ∈ Ioo 0 1`, `t₀' ∈ Ioo (1 - τ) 1`, both `t₀'` and `t₀' + τ - 1` in `Ioo 0 1`.
- **Uses from project**: `angleAtCrossing`, `angleAtCrossing_smooth`, `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `ClosedPwC1Immersion.toPwC1Immersion`, `mem_cyclicShift_partition_wrap_iff`, `deriv_cyclicShift_eventuallyEq_left_wrap`, `deriv_cyclicShift_eventuallyEq_right_wrap`, `tendsto_sub_const_nhdsLT`, `tendsto_sub_const_nhdsGT`
- **Used by**: `satisfiesConditionB_cyclicShift`
- **Visibility**: private
- **Lines**: 1014-1123
- **Notes**: Proof >30 lines. Symmetric structure to no-wrap variant.

### `theorem ClosedPwC1Immersion.satisfiesConditionB_cyclicShift`
- **Type**: `{γ : ClosedPwC1Immersion x} {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 1) {S : Finset ℂ} {f : ℂ → ℂ} (h_basepoint_angleB : ∀ s ∈ S, γ.toPath.extend 1 = s → ∀ ht_oneSubTau : (1 - τ) ∈ Ioo 0 1, ∃ p q : ℕ, q ≠ 0 ∧ Nat.Coprime p q ∧ angleAtCrossing (γ.cyclicShift hτ).toPwC1Immersion (1 - τ) ht_oneSubTau = ↑p * Real.pi / ↑q) (h_basepoint_laurentB : ∀ s ∈ S, γ.toPath.extend 1 = s → ∀ ht_oneSubTau : (1 - τ) ∈ Ioo 0 1, ∃ N a g, ...) (h : SatisfiesConditionB γ.toPwC1Immersion f S) : SatisfiesConditionB (γ.cyclicShift hτ).toPwC1Immersion f S`
- **What**: Cyclic-shift invariance of `SatisfiesConditionB` (T-BR-Y9h-B). Angle rationality and Laurent compatibility transport. Breakpoint handled via basepoint hypotheses.
- **How**: Trichotomy on `t₀'` vs `1 - τ`. Each side has two cases (angle_rational and laurent_compatible) handled similarly: no-wrap → apply `h` at `t₀ = t₀' + τ` and use `angleAtCrossing_cyclicShift_no_wrap` to transport; breakpoint → substitute `t₀' = 1 - τ` and apply basepoint hypothesis; wrap → analogous to no-wrap using `angleAtCrossing_cyclicShift_wrap` and `t₀ = t₀' + τ - 1`.
- **Hypotheses**: `τ ∈ Ioo 0 1`; basepoint angle/Laurent hypotheses at `s = γ(1)`; condition B holds for original curve.
- **Uses from project**: `SatisfiesConditionB`, `SatisfiesConditionB.angle_rational`, `SatisfiesConditionB.laurent_compatible`, `angleAtCrossing`, `ClosedPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift`, `ClosedPwC1Immersion.toPwC1Immersion`, `ClosedPwC1Immersion.cyclicShift_extend_eq_no_wrap`, `ClosedPwC1Immersion.cyclicShift_extend_eq_wrap`, `angleAtCrossing_cyclicShift_no_wrap`, `angleAtCrossing_cyclicShift_wrap`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1140-1256
- **Notes**: Proof >30 lines. Uses `lt_trichotomy`.

### File Summary
- **Total declarations**: 26
- **Key API (used by 3+ others in this file)**:
  - `cpvIntegrandOnPer` (used in 4 places — periodic extension foundation)
  - `cpvIntegrandOnPer_eq_on_Ico` (used in 3+ places)
  - `cpvIntegrandOn_cyclicShift_integral_eq` (used by 3 invariance theorems)
  - `tendsto_sub_const_nhdsGT` and `_LT` (used in flatness transport and angle-crossing proofs)
  - `tendsto_add_const_nhdsGT` and `_LT` (used in flatness transport)
  - `exists_partition_isolating_nhd_no_wrap` and `_wrap` (used in derivative-eventually-eq lemmas)
  - `deriv_cyclicShift_eventuallyEq_{left,right}_{no_wrap,wrap}` (used in angle-crossing proofs)
- **Unused in this file** (these are public theorems exported to downstream files):
  - `hasCauchyPVOn_cyclicShift`
  - `cauchyPVOn_cyclicShift`
  - `isNullHomologous_cyclicShift`
  - `satisfiesConditionA'_cyclicShift`
  - `satisfiesConditionB_cyclicShift`
- **Declarations with sorry**: None
- **Declarations with set_option**: None
- **Proofs >30 lines**:
  - `cpvIntegrandOn_cyclicShift_eq_per_ae`
  - `cpvIntegrandOn_cyclicShift_integral_eq`
  - `deriv_comp_add_const`
  - `isFlatOfOrder_of_eventuallyEq_shift`
  - `satisfiesConditionA'_cyclicShift`
  - `exists_partition_isolating_nhd_no_wrap`
  - `exists_partition_isolating_nhd_wrap`
  - `angleAtCrossing_cyclicShift_no_wrap`
  - `angleAtCrossing_cyclicShift_wrap`
  - `satisfiesConditionB_cyclicShift`
- **File purpose**: This file establishes the headline cyclic-shift invariance theorems for `ClosedPwC1Immersion`, used as bookkeeping in the HW3.3 spec chain. The integral identity for `HasCauchyPVOn`, `cauchyPVOn`, `cauchyPV`, and `generalizedWindingNumber` is established via a periodic-extension trick (`cpvIntegrandOnPer`): the cutoff integrand for the shifted curve equals `G(t+τ)` for the 1-periodic extension `G`, and `∫_0^1 G(t+τ) dt = ∫_0^1 G(u) du` follows from `Function.Periodic.intervalIntegral_add_eq` without any integrability requirement. The file then provides affine-shift transport machinery for `IsFlatOfOrder` (via `deriv_comp_add_const`, `tendsto_{add,sub}_const_nhds{GT,LT}`, `isFlatOfOrder_of_eventuallyEq_shift`) used to prove `SatisfiesConditionA'` invariance. The angle-crossing invariance under cyclic shift requires partition-isolating neighborhoods (`exists_partition_isolating_nhd_{no_wrap,wrap}`) and eventually-equal derivative lemmas, leading to `angleAtCrossing_cyclicShift_{no_wrap,wrap}` and finally `satisfiesConditionB_cyclicShift`. All public theorems are exported for downstream use; the breakpoint `1 - τ` cases require basepoint hypotheses (vacuous when the basepoint is not in `S`).
