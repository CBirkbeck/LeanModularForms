# HW33Final.md — Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HW33Final.lean` (247 lines)

## Entries

### theorem `LeanModularForms.shape_right_eventually`
- **Type**: `{γ : ℝ → ℂ} {s : ℂ} {t₀ δPlus : ℝ} (…) : ∀ᶠ ε in 𝓝[>] 0, firstExitTimeRight γ t₀ δPlus s ε ≤ 1 ∧ ∀ t ∈ Ioo (firstExitTimeRight …) 1, ε < ‖γ t - s‖`
- **What**: Packages `shape_right_of_strictMonoOn` into the eventually-as-ε→0⁺ form expected by the CPV bridge.
- **How**: Take `h := h_avoid_pos.trans_le (h_avoid (t₀ + δPlus) ⟨le_rfl, by linarith⟩)`; `filter_upwards [Ioo_mem_nhdsGT (lt_min h h_avoid_pos)]`; destructure via `lt_min_iff.mp hε.2`; close with `shape_right_of_strictMonoOn`.
- **Hypotheses**: `t₀ + δPlus ≤ 1`, `0 < δPlus`, continuity on `[t₀, t₀+δPlus]`, strict mono of `‖γ-s‖`, `γ t₀ = s`, avoidance margin `δ_avoid > 0` on `[t₀+δPlus, 1]`.
- **Uses-from-project**: `firstExitTimeRight`, `shape_right_of_strictMonoOn`.
- **Used by**: `shape_eventually_of_strict_mono`.
- **Visibility**: public.
- **Lines**: 35–51.

### theorem `LeanModularForms.shape_left_eventually`
- **Type**: Symmetric left-side analog.
- **What**: Packages `shape_left_of_strictAntiOn` into eventually form.
- **How**: Mirror argument: `h_avoid_pos.trans_le (h_avoid (t₀ - δMinus) ⟨h_t₀_minus_pos, le_rfl⟩)`; `filter_upwards [Ioo_mem_nhdsGT (lt_min h h_avoid_pos)]`; `lt_min_iff.mp`; close with `shape_left_of_strictAntiOn`.
- **Hypotheses**: `0 ≤ t₀ - δMinus`, `0 < δMinus`, continuity on `[t₀-δMinus, t₀]`, strict anti of `‖γ-s‖`, `γ t₀ = s`, avoidance margin on `[0, t₀-δMinus]`.
- **Uses-from-project**: `firstExitTimeLeft`, `shape_left_of_strictAntiOn`.
- **Used by**: `shape_eventually_of_strict_mono`.
- **Visibility**: public.
- **Lines**: 54–70.

### theorem `LeanModularForms.shape_eventually_of_strict_mono`
- **Type**: `… : ∀ᶠ ε in 𝓝[>] 0, ⟨α ε ≥ 0, β ε ≤ 1, α ε ≤ β ε, ∀ t ∈ (0, α ε), ε < ‖γ - s‖, ∀ t ∈ (β ε, 1), ε < ‖γ - s‖, ∀ t ∈ (α ε, β ε), ‖γ - s‖ ≤ ε⟩` (with `α = firstExitTimeLeft`, `β = firstExitTimeRight`).
- **What**: Combined two-sided shape eventually, bundling left+right exit-time and "inside ≤ ε / outside > ε" properties into the exact hypothesis form needed by `hasCauchyPVOn_singleton_of_exitTime_excision`.
- **How**: Build `h_left` from `shape_left_eventually` and `h_right` from `shape_right_eventually`; separately establish `h_in_brackets : ∀ᶠ ε, firstExitTimeLeft ≤ firstExitTimeRight ∧ inside-bound` by `filter_upwards [Ioo_mem_nhdsGT (lt_min hL hR)]`, casework on `t ≤ t₀` vs `t > t₀`, using `le_csSup`/`csInf_le` against `firstExitTimeLeft_set_ub` / `firstExitTimeRight_set_lb` and `firstExitTimeLeft_mem_Icc` / `firstExitTimeRight_mem_Icc`; finally `filter_upwards [h_left, h_right, h_in_brackets]`.
- **Hypotheses**: Two-sided continuity + strict mono/anti hypotheses, avoidance margins, `γ t₀ = s`.
- **Uses-from-project**: `firstExitTimeLeft`, `firstExitTimeRight`, `firstExitTimeLeft_mem_Icc`, `firstExitTimeRight_mem_Icc`, `firstExitTimeLeft_set_ub`, `firstExitTimeRight_set_lb`, `shape_left_eventually`, `shape_right_eventually`.
- **Used by**: `hasCauchyPVOn_singleton_pow_of_transverse_assembled`.
- **Visibility**: public.
- **Lines**: 80–144.
- **Notes**: Proof >10 lines; key lemmas `le_csSup`, `csInf_le`, `Ioo_mem_nhdsGT`, exit-time membership lemmas.

### theorem `LeanModularForms.hasCauchyPVOn_singleton_pow_of_transverse_assembled`
- **Type**: `{γ : PiecewiseC1Path x x} {s L : ℂ} {t₀ δMinus δPlus : ℝ} {n k : ℕ} (…) : HasCauchyPVOn {s} (fun z => (1:ℂ)/(z-s)^k) γ 0`
- **What**: Full HW Theorem 3.3 closure for the k-odd transverse single-pole case in `HasCauchyPVOn` form.
- **How**: Compose three pieces via `hasCauchyPVOn_singleton_of_exitTime_excision`:
  - shape hypothesis from `shape_eventually_of_strict_mono`,
  - integrability hypothesis `h_int_full`,
  - parametric symmetric-excision PV from `hw_theorem_3_3_odd_transverse_concrete` (with all of its many transversality / flatness / smoothness / integrability data passed through),
  congr-corrected by `intervalIntegral.integral_congr` with pointwise `ring`.
- **Hypotheses**: Long bundle: positivity / interval-membership of `t₀ ± δ`, closed γ, `IsFlatOfOrder γ t₀ n`, derivative `L ≠ 0` from both sides plus tendsto, `γ t₀ = s`, `k ≥ 2` odd with `k ≤ n` and `1 ≤ n`, two-sided continuity, leave-conditions, strict mono/anti, avoidance margins, two-sided smoothness/avoidance/interval-integrability across exit-time-bounded pieces, full-interval integrability of the cpvIntegrandOn eventually as ε → 0⁺.
- **Uses-from-project**: `PiecewiseC1Path`, `IsFlatOfOrder`, `firstExitTimeLeft`, `firstExitTimeRight`, `cpvIntegrandOn`, `HasCauchyPVOn`, `hasCauchyPVOn_singleton_of_exitTime_excision`, `hw_theorem_3_3_odd_transverse_concrete`, `shape_eventually_of_strict_mono`.
- **Used by**: User-facing entry point for Hungerbühler–Wasem Theorem 3.3 single-pole transverse k-odd case.
- **Visibility**: public.
- **Lines**: 171–243.
- **Notes**: Proof >10 lines (largely composition + congr); key lemmas `hasCauchyPVOn_singleton_of_exitTime_excision`, `hw_theorem_3_3_odd_transverse_concrete`.

## File Summary
- **Total entries**: 4 (all public theorems, namespaced under `LeanModularForms`).
- **Key API**: `shape_right_eventually`, `shape_left_eventually`, `shape_eventually_of_strict_mono`, `hasCauchyPVOn_singleton_pow_of_transverse_assembled`.
- **Unused**: None — `shape_right_eventually` and `shape_left_eventually` feed `shape_eventually_of_strict_mono`, which feeds the final assembled HW 3.3 theorem.
- **Sorries**: 0.
- **set_options**: None.
- **Long proofs (>10 lines)**: `shape_eventually_of_strict_mono`, `hasCauchyPVOn_singleton_pow_of_transverse_assembled`.
- **Purpose**: Assembles the full HW Theorem 3.3 closure for the k-odd transverse single-pole case. Bridges the lower-level strict-monotonicity shape results from `HW33Monotonicity.lean` into the `∀ᶠ ε in 𝓝[>] 0, …` form expected by `hasCauchyPVOn_singleton_of_exitTime_excision`, then composes with the concrete odd-transverse parametric PV theorem to discharge `HasCauchyPVOn {s} (fun z => 1/(z-s)^k) γ 0` from a long but completely concrete bundle of geometric and analytic transversality data. This is the final user-facing assembled form of HW 3.3 for k-odd transverse single poles.
