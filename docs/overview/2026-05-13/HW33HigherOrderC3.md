# HW33HigherOrderC3.md

**Path**: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HW33HigherOrderC3.lean
**Lines**: 209
**Imports**: `HigherOrderCancel`, `MultipointPV`
**Namespace**: `LeanModularForms` (and `variable {x : ℂ}`)

---

## theorem `contourIntegral_finset_sum`
- **Type**: `{ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {y : ℂ} (γ : PiecewiseC1Path x y) (hf : ∀ i ∈ s, IntervalIntegrable (PiecewiseC1Path.contourIntegrand (f i) γ) volume 0 1) : γ.contourIntegral (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, γ.contourIntegral (f i)`
- **What**: Linearity of contour integration over `Finset` sums, when each integrand is interval-integrable.
- **How** (>10 lines): `Finset.induction_on s`. Empty case: `Finset.sum_empty` then `PiecewiseC1Path.contourIntegral_zero`. Insert case: extract individual integrability `h_j` and `h_t`; build `h_t_int` by rewriting `Finset.sum_mul` and applying `IntervalIntegrable.sum t h_t`; rewrite `Finset.sum_insert hi`, `(fun z => ∑ i ∈ insert j t, f i z) = fun z => f j z + ∑ i ∈ t, f i z`, then apply `PiecewiseC1Path.contourIntegral_add (f j) (...) γ h_j h_t_int` and the induction hypothesis `ih h_t`.
- **Hypotheses**: per-term interval-integrability over `[0,1]`.
- **Uses-from-project**: `PiecewiseC1Path`, `PiecewiseC1Path.contourIntegral`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path.contourIntegral_zero`, `PiecewiseC1Path.contourIntegral_add`.
- **Used by**: `hasCauchyPVOn_finset_pow_inv_of_avoids`.
- **Visibility**: public.
- **Lines**: 47-89.
- **Notes**: Foundational `Finset.sum` linearity, with explicit integrability bookkeeping for the inductive step.

## theorem `cpvIntegrandOn_finset_sum_intervalIntegrable`
- **Type**: `{ι : Type*} (ι_set : Finset ι) (S : Finset ℂ) {f : ι → ℂ → ℂ} {γ : PiecewiseC1Path x x} {ε : ℝ} (hf : ∀ i ∈ ι_set, IntervalIntegrable (fun t => cpvIntegrandOn S (f i) γ.toPath.extend ε t) volume 0 1) : IntervalIntegrable (fun t => cpvIntegrandOn S (fun z => ∑ i ∈ ι_set, f i z) γ.toPath.extend ε t) volume 0 1`
- **What**: Integrability of the CPV integrand transfers through finite sums.
- **How**: `convert IntervalIntegrable.sum ι_set hf using 1`, then pointwise via `funext t; simp only [cpvIntegrandOn, Finset.sum_apply]; split_ifs with h; · rw [Finset.sum_const_zero]; · rw [Finset.sum_mul]`.
- **Hypotheses**: per-term integrability of `cpvIntegrandOn S (f i) ...`.
- **Uses-from-project**: `cpvIntegrandOn` (from `MultipointPV`), `PiecewiseC1Path`.
- **Used by**: `HasCauchyPVOn.finset_sum`.
- **Visibility**: public.
- **Lines**: 95-108.
- **Notes**: Sum-closure preliminary for `HasCauchyPVOn`.

## theorem `HasCauchyPVOn.finset_sum`
- **Type**: `{ι : Type*} (ι_set : Finset ι) {S : Finset ℂ} {f : ι → ℂ → ℂ} {L : ι → ℂ} {γ : PiecewiseC1Path x x} (hf : ∀ i ∈ ι_set, HasCauchyPVOn S (f i) γ (L i)) (hf_int : ∀ i ∈ ι_set, ∀ ε > 0, IntervalIntegrable (fun t => cpvIntegrandOn S (f i) γ.toPath.extend ε t) volume 0 1) : HasCauchyPVOn S (fun z => ∑ i ∈ ι_set, f i z) γ (∑ i ∈ ι_set, L i)`
- **What**: `HasCauchyPVOn` is closed under `Finset` sums of integrands with matching limit sums.
- **How** (>10 lines): `Finset.induction_on ι_set`. Empty case: `Finset.sum_empty`; use `Filter.Tendsto.congr'` with `eventuallyEq_iff_exists_mem` on `univ` to show the empty-sum CPV reduces to `tendsto_const_nhds 0`, with `cpvIntegrandOn` of the zero function equal to zero via `split_ifs <;> simp` and `intervalIntegral.integral_zero`. Insert case: extract per-element `hf_j`/`hf_t` and per-element integrability; build `hf_int_sum` via `cpvIntegrandOn_finset_sum_intervalIntegrable`; rewrite `Finset.sum_insert j_t_disj`; apply `hf_j.add ih_app hf_int_j hf_int_sum` (i.e., `HasCauchyPVOn.add`, presumably from `MultipointPV`/`HigherOrderCancel`).
- **Hypotheses**: per-term `HasCauchyPVOn` and ε-uniform CPV integrand integrability.
- **Uses-from-project**: `HasCauchyPVOn`, `HasCauchyPVOn.add`, `cpvIntegrandOn`, `cpvIntegrandOn_finset_sum_intervalIntegrable`, `PiecewiseC1Path`.
- **Used by**: external (general HW3.3 avoidance assembly).
- **Visibility**: public.
- **Lines**: 113-156.
- **Notes**: Carries the Finset-induction bookkeeping for both the limit and the ε-uniform integrability.

## theorem `hasCauchyPVOn_finset_pow_inv_of_avoids`
- **Type**: `(S : Finset ℂ) (k : ℕ) (hk : 2 ≤ k) (c : ℂ → ℂ) (γ : PiecewiseC1Path x x) (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s‖) (h_int : ∀ s ∈ S, IntervalIntegrable (fun t => (1 / (γ.toPath.extend t - s) ^ k) * deriv γ.toPath.extend t) volume 0 1) : HasCauchyPVOn S (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ 0`
- **What**: For `k ≥ 2`, the CPV of `∑ s ∈ S, c s / (z - s)^k` along a closed γ avoiding S vanishes — the avoidance form of HW Theorem 3.3 (C-3 case).
- **How** (>10 lines): From `hδ` get avoidance `γ t ≠ s` (via `sub_self` and `norm_zero`). Show each term's contour integrand `c s / (γ t - s)^k * γ'(t)` is integrable via `IntervalIntegrable.const_mul` (`convert (h_int s hs).const_mul (c s) using 1; funext t; ring`). For each pole, `γ.contourIntegral_pow_inv_eq_zero hk (h_avoids s hs) (h_int s hs) = 0` gives the per-term contour integral is zero; multiply through by `c s` (via `contourIntegral_smul`) and conclude `γ.contourIntegral (fun z => ∑ s ∈ S, c s / (z - s)^k) = 0` using `contourIntegral_finset_sum` and `Finset.sum_eq_zero`. Close with `hCancel_of_contourIntegral_zero S _ γ hδ h_sum_zero`.
- **Hypotheses**: uniform positive avoidance distance from γ to S, per-pole integrability of the base integrand.
- **Uses-from-project**: `PiecewiseC1Path`, `PiecewiseC1Path.contourIntegral_pow_inv_eq_zero`, `PiecewiseC1Path.contourIntegral_smul`, `contourIntegral_finset_sum`, `hCancel_of_contourIntegral_zero` (from `HigherOrderCancel`), `HasCauchyPVOn`.
- **Used by**: external (HW3.3 avoidance branch).
- **Visibility**: public.
- **Lines**: 169-205.
- **Notes**: The main theorem of this file — closes the avoidance case of C-3 (higher-order polar cancellation, k ≥ 2). The transverse k-odd case is handled separately in `HW33ExitTimeWrapper.lean`.

---

## File Summary

Avoidance form of HW3.3 condition C-3: when `γ` avoids every pole of `S` with positive margin, the CPV of `∑ s ∈ S, c s / (z - s)^k` (k ≥ 2) vanishes. Three building blocks are proved by `Finset.induction_on`: `contourIntegral_finset_sum` linearity for contour integration, `cpvIntegrandOn_finset_sum_intervalIntegrable` for CPV-integrand sum integrability, and `HasCauchyPVOn.finset_sum` for `HasCauchyPVOn` Finset-closure. The main theorem `hasCauchyPVOn_finset_pow_inv_of_avoids` combines `contourIntegral_pow_inv_eq_zero` (single pole) with these closure lemmas and `hCancel_of_contourIntegral_zero` to deduce the multi-pole avoidance result. The transverse k-odd case is out of scope and routed to `HW33ExitTimeWrapper.lean`'s `hw_theorem_3_3_odd_transverse_concrete`.
