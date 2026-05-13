# HW33HigherOrderC4.lean Inventory

**Path**: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HW33HigherOrderC4.lean
**Lines**: 160
**Imports**: `LeanModularForms.ForMathlib.HW33HigherOrderC3`, `LeanModularForms.ForMathlib.HigherOrderAssembly`

## Entries

### theorem `hasCauchyPVOn_add_higherOrderPolar_of_avoids`
- **Type**: theorem
- **What**: Adding a single higher-order polar term `∑ s ∈ S, c s / (z - s)^k` (`k ≥ 2`) to a function `f` with CPV `L` along `γ` (avoiding `S`) preserves the CPV value `L`. I.e., higher-order polar corrections contribute zero in the avoidance case.
- **How**: One-liner: `simpa only [add_zero] using HasCauchyPVOn.add h_f (hasCauchyPVOn_finset_pow_inv_of_avoids S k hk c γ hδ h_int_HO) h_f_int h_HO_int`.
- **Hypotheses**: `hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s‖`, `h_f : HasCauchyPVOn S f γ L`, `h_f_int` (integrability of cpvIntegrand for `f`), `k : ℕ`, `hk : 2 ≤ k`, `c : ℂ → ℂ`, `h_int_HO` (per-pole HO integrability), `h_HO_int` (cpvIntegrand integrability for HO sum).
- **Uses-from-project**: `HasCauchyPVOn.add` (additivity of HasCauchyPVOn), `hasCauchyPVOn_finset_pow_inv_of_avoids` (C-3 avoidance: HO polar gives CPV 0).
- **Used by**: `hasCauchyPVOn_add_higherOrderPolarSum_of_avoids` and `generalizedResidueTheorem_higherOrder_avoids_closed`.
- **Visibility**: public
- **Lines**: 48–65
- **Notes**: Inside `namespace LeanModularForms`. Composes B-6 (additivity) with C-3 (HO avoidance = 0).

### theorem `hasCauchyPVOn_add_higherOrderPolarSum_of_avoids`
- **Type**: theorem
- **What**: Iterates `hasCauchyPVOn_add_higherOrderPolar_of_avoids` over `k ∈ Finset.Ico 2 (M + 1)` — sum over a power range of higher-order polar terms is absorbed into a fixed CPV value `L`.
- **How**: Build `h_HOsum : HasCauchyPVOn S (∑ k, ∑ s, c_HO k s / (z-s)^k) γ 0` via `h_each_k : ∀ k ∈ Finset.Ico 2 (M+1), HasCauchyPVOn S (∑ s, c_HO k s / (z-s)^k) γ 0`, each from `hasCauchyPVOn_finset_pow_inv_of_avoids` (with `Finset.mem_Ico.mp hk_mem`'s left part for `k ≥ 2`), then `simpa only [Finset.sum_const_zero] using HasCauchyPVOn.finset_sum (Finset.Ico 2 (M+1)) h_each_k h_HO_int`. Integrability of the cpvIntegrand for the HO sum follows from `cpvIntegrandOn_finset_sum_intervalIntegrable`. Conclude via `simpa only [add_zero] using HasCauchyPVOn.add h_f h_HOsum h_f_int h_HOsum_int`.
- **Hypotheses**: Same as `hasCauchyPVOn_add_higherOrderPolar_of_avoids` but quantified over a power range `Finset.Ico 2 (M + 1)` rather than a single `k`.
- **Uses-from-project**: `HasCauchyPVOn.add`, `HasCauchyPVOn.finset_sum`, `hasCauchyPVOn_finset_pow_inv_of_avoids`, `cpvIntegrandOn_finset_sum_intervalIntegrable`.
- **Used by**: `generalizedResidueTheorem_higherOrder_avoids_closed`.
- **Visibility**: public
- **Lines**: 71–105
- **Notes**: Inside `namespace LeanModularForms`. Iterates the single-`k` lemma over a Finset range. Uses `Finset.sum_const_zero` to discard zero-CPV summands.

### theorem `generalizedResidueTheorem_higherOrder_avoids_closed`
- **Type**: theorem
- **What**: **C-4 closed-form residue theorem (avoidance case)**: for `f_simple + (HO Laurent corrections)` on a bounded open set `U`, with `γ : PwC1Immersion` closed null-homologous in `U` avoiding poles `S`, the CPV equals `2πi · ∑ s ∈ S, w(γ,s) · res(f_simple, s)`.
- **How**: Obtain `hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s‖` via `avoids_finset_delta_bound γ.toPiecewiseC1Path S hγ_avoids`. Conclude with `hasCauchyPVOn_add_higherOrderPolarSum_of_avoids S f_simple γ.toPiecewiseC1Path hδ (generalizedResidueTheorem_simplePoles_nullHomologous_closed hU_open hU_ne hU_bounded S hS_in_U f_simple hf_simple γ h_null hSimplePoles hγ_avoids hδ hLip) h_simple_int M c_HO h_int_HO h_HO_int`.
- **Hypotheses**: `hU_open`, `hU_ne`, `hU_bounded`, `S : Finset ℂ`, `hS_in_U`, `γ : PwC1Immersion`, `h_null : IsNullHomologous γ U`, `f_simple : ℂ → ℂ`, `hf_simple : DifferentiableOn ℂ f_simple (U \ ↑S)`, `hSimplePoles`, `M : ℕ`, `c_HO : ℕ → ℂ → ℂ`, `h_int_HO`, `h_HO_int`, `h_simple_int`, `hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc 0 1, γ t ≠ s`, `hLip : LipschitzWith K γ.toPath.extend`.
- **Uses-from-project**: `hasCauchyPVOn_add_higherOrderPolarSum_of_avoids`, `generalizedResidueTheorem_simplePoles_nullHomologous_closed` (B-6), `avoids_finset_delta_bound`, `PwC1Immersion`, `IsNullHomologous`, `HasSimplePoleAt`, `residue`, `generalizedWindingNumber`.
- **Used by**: Top-level avoidance form of HW Theorem 3.3 closed residue theorem.
- **Visibility**: public
- **Lines**: 122–156
- **Notes**: Inside `namespace LeanModularForms`. Closes the C-4 avoidance case by composing B-6 (simple-pole closed null-homologous) with the HO Laurent absorption. The odd transverse-crossing case is handled separately by `hw_theorem_3_3_odd_transverse_concrete` in `HW33ExitTimeWrapper.lean`.

## File Summary

Three public theorems inside `namespace LeanModularForms`, organized as a tower over the C-3 (higher-order avoidance) cancellation result. The first theorem (`hasCauchyPVOn_add_higherOrderPolar_of_avoids`) handles a single power `k ≥ 2`. The second (`hasCauchyPVOn_add_higherOrderPolarSum_of_avoids`) iterates over a power range. The third (`generalizedResidueTheorem_higherOrder_avoids_closed`) is the C-4 endpoint: closed-form residue theorem for `f_simple + (HO Laurent corrections)` on a bounded null-homologous Lipschitz immersion avoiding the singular set, with value `2πi · ∑ w(γ,s) · res(f_simple, s)`. The file is short by design — it's a thin compositional layer that joins the B-6 simple-pole closure with C-3 avoidance cancellation.
