# SingleCrossing.md — Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/SingleCrossing.lean` (252 lines)

## Entries

### structure `SingleCrossingData`
- **Type**: `(γ : PiecewiseC1Path x y) (z₀ : ℂ) → Type`
- **What**: Bundles all geometric ingredients for a single-crossing CPV computation: target limit `L`, crossing time `t₀`, cutoff `δ`, threshold, far/near bounds, FTC expression `E`, integrability, and `E → L`.
- **How**: Plain `structure` declaration with 13 fields.
- **Hypotheses**: positivity of δ on `(0, threshold)`, δ small enough to keep `t₀ ± δ ⊆ (0,1)`, far/near norm bounds, FTC equality, integrability on outer pieces, `Tendsto E (𝓝[>] 0) (𝓝 L)`.
- **Uses-from-project**: `PiecewiseC1Path`.
- **Used by**: All theorems in this namespace; downstream edge/arc winding proofs (RightEdge, LeftEdge, UnitArc).
- **Visibility**: public.
- **Lines**: 55–95.

### private theorem `SingleCrossingData.cpvIntegrand_zero_on_middle`
- **Type**: `(D : SingleCrossingData γ z₀) {ε} (hε_pos hε_lt) (h_mid_lt : t₀ - δ ε < t₀ + δ ε) : ∀ t ∈ Set.uIoc (t₀ - δ ε) (t₀ + δ ε), cpvIntegrand … z₀ ε t = 0`
- **What**: Cutoff integrand vanishes on the central window because `‖γ - z₀‖ ≤ ε` there.
- **How**: Translate `uIoc` to `Ioc` via `uIoc_of_le`; `simp [cpvIntegrand]`; `if_neg`; close threshold via `D.h_near` with `abs_le` and `linarith`.
- **Hypotheses**: `D.h_near` (near bound), `hε_pos`, `hε_lt`.
- **Uses-from-project**: `cpvIntegrand`, `SingleCrossingData.h_near`.
- **Used by**: `cutoff_integral_eq_E`.
- **Visibility**: private.
- **Lines**: 103–114.

### private theorem `SingleCrossingData.cpvIntegrand_eq_full_left_ae`
- **Type**: `(D : SingleCrossingData γ z₀) {ε} … : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 (t₀ - δ ε) → cpvIntegrand … = (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t`
- **What**: Cutoff integrand matches the full integrand a.e. on the left outer piece.
- **How**: Exclude singleton `{t₀ - δ ε}` via `compl_mem_ae_iff` + `finite_singleton.measure_zero`; `filter_upwards`; rewrite cutoff with `if_pos`; apply `D.h_far` using `abs_of_nonpos` + `linarith`.
- **Hypotheses**: `D.h_far` (far bound), positivity.
- **Uses-from-project**: `cpvIntegrand`, `SingleCrossingData.h_far`, `SingleCrossingData.hδ_pos`.
- **Used by**: `cutoff_integral_eq_E`.
- **Visibility**: private.
- **Lines**: 118–136.

### private theorem `SingleCrossingData.cpvIntegrand_eq_full_right_ae`
- **Type**: Symmetric right-side version of `cpvIntegrand_eq_full_left_ae`.
- **What**: Cutoff integrand matches full integrand a.e. on `[t₀ + δ, 1]`.
- **How**: Same singleton-exclusion pattern; `if_pos`; `D.h_far` with `abs_of_pos`.
- **Hypotheses**: `D.h_far`, `D.ht₀.1`, positivity.
- **Uses-from-project**: `cpvIntegrand`, `SingleCrossingData.h_far`.
- **Used by**: `cutoff_integral_eq_E`.
- **Visibility**: private.
- **Lines**: 140–156.

### private theorem `SingleCrossingData.cutoff_integral_eq_E`
- **Type**: `(D : SingleCrossingData γ z₀) {ε} (hε_pos hε_lt) : ∫ t in (0:ℝ)..1, cpvIntegrand … = D.E ε`
- **What**: Cutoff integral over `[0,1]` equals `E(ε)` by splitting at `t₀ ± δ`.
- **How**: Use `δ` smallness to prove `0 < t₀ - δε`, `t₀ - δε < t₀ + δε`, `t₀ + δε < 1`; establish integrability of `F = cpvIntegrand` on each piece via `IntervalIntegrable.congr_ae` and `IntervalIntegrable.zero.congr`; split with `intervalIntegral.integral_add_adjacent_intervals` (twice); zero the middle via `integral_zero_ae`; congr the outer pieces via `integral_congr_ae`; finish via `D.h_ftc`.
- **Hypotheses**: positivity, δ smallness, integrability, FTC.
- **Uses-from-project**: `cpvIntegrand`, `SingleCrossingData` fields (h_far/h_near/h_ftc/hint_left/hint_right/hδ_pos/hδ_small/ht₀).
- **Used by**: `hasCauchyPV`.
- **Visibility**: private.
- **Lines**: 160–199.
- **Notes**: Proof >10 lines; key lemmas `integral_add_adjacent_intervals`, `integral_zero_ae`, `integral_congr_ae`.

### theorem `SingleCrossingData.hasCauchyPV`
- **Type**: `(D : SingleCrossingData γ z₀) : HasCauchyPV (·⁻¹ ∘ (· - z₀)) γ z₀ D.L`
- **What**: CPV exists with value `D.L`.
- **How**: Unfold `HasCauchyPV`; build `h_ev : (cutoff integral) =ᶠ[𝓝[>] 0] D.E` via `filter_upwards [Ioo_mem_nhdsGT D.hthresh]` plus `cutoff_integral_eq_E`; conclude with `D.h_limit.congr' h_ev.symm`.
- **Hypotheses**: bundled `D`.
- **Uses-from-project**: `HasCauchyPV`, `cpvIntegrand`, `cutoff_integral_eq_E`, `SingleCrossingData.hthresh`, `SingleCrossingData.h_limit`.
- **Used by**: `hasWindingNumber`.
- **Visibility**: public.
- **Lines**: 208–216.

### theorem `SingleCrossingData.hasWindingNumber`
- **Type**: `(D : SingleCrossingData γ z₀) : HasGeneralizedWindingNumber γ z₀ (D.L / (2 * Real.pi * I))`
- **What**: Generalized winding number equals `L / (2πi)`.
- **How**: Rewrite `D.L / (2πI)` as `(2πI)⁻¹ * D.L`; apply `hasGeneralizedWindingNumber_of_hasCauchyPV D.hasCauchyPV`.
- **Hypotheses**: bundled `D`.
- **Uses-from-project**: `HasGeneralizedWindingNumber`, `hasGeneralizedWindingNumber_of_hasCauchyPV`.
- **Used by**: `windingNumber_eq`, `windingNumber_neg_half`, `windingNumber_neg_sixth`.
- **Visibility**: public.
- **Lines**: 219–222.

### theorem `SingleCrossingData.windingNumber_eq`
- **Type**: `(D : SingleCrossingData γ z₀) : generalizedWindingNumber γ z₀ = D.L / (2 * Real.pi * I)`
- **What**: Concrete value of the generalized winding number.
- **How**: `D.hasWindingNumber.eq`.
- **Hypotheses**: bundled `D`.
- **Uses-from-project**: `generalizedWindingNumber`, `HasGeneralizedWindingNumber.eq`, `hasWindingNumber`.
- **Used by**: `windingNumber_neg_half`, `windingNumber_neg_sixth`.
- **Visibility**: public.
- **Lines**: 225–227.

### theorem `SingleCrossingData.windingNumber_neg_half`
- **Type**: `(D … hL : D.L = -(↑Real.pi * I)) : generalizedWindingNumber γ z₀ = -1 / 2`
- **What**: Specialization: `L = -πi` ⇒ winding number `-1/2`.
- **How**: Rewrite with `windingNumber_eq` and `hL`; `field_simp` using `π ≠ 0` (via `ofReal_ne_zero.mpr Real.pi_ne_zero`) and `I_ne_zero`.
- **Hypotheses**: `D.L = -πi`.
- **Uses-from-project**: `windingNumber_eq`.
- **Used by**: Edge winding proofs at non-elliptic points.
- **Visibility**: public.
- **Lines**: 231–237.

### theorem `SingleCrossingData.windingNumber_neg_sixth`
- **Type**: `(D … hL : D.L = -(↑Real.pi / 3 * I)) : generalizedWindingNumber γ z₀ = -1 / 6`
- **What**: Specialization: `L = -πi/3` ⇒ winding number `-1/6`.
- **How**: Rewrite with `windingNumber_eq` and `hL`; `field_simp` (π ≠ 0, I ≠ 0); `ring`.
- **Hypotheses**: `D.L = -πi/3`.
- **Uses-from-project**: `windingNumber_eq`.
- **Used by**: Elliptic-point winding proofs (ρ, ρ+1).
- **Visibility**: public.
- **Lines**: 241–248.

## File Summary
- **Total entries**: 10 (1 structure + 4 private helpers + 5 public theorems).
- **Key API**: `SingleCrossingData` (the bundling structure), `hasCauchyPV`, `hasWindingNumber`, `windingNumber_eq`, `windingNumber_neg_half`, `windingNumber_neg_sixth`.
- **Unused**: None — the private helpers all feed `cutoff_integral_eq_E`, which feeds `hasCauchyPV`.
- **Sorries**: 0.
- **set_options**: None.
- **Long proofs (>10 lines)**: `cutoff_integral_eq_E`.
- **Purpose**: Provides the unified `SingleCrossingData` framework for computing `generalizedWindingNumber γ z₀` when γ crosses `z₀` at exactly one parameter `t₀ ∈ (0,1)`. The five-step structure (identify t₀; cutoff radius δ(ε); far/near bounds; FTC telescope to `E(ε)`; `E → L`) is bundled into one structure so that downstream proofs (RightEdge, LeftEdge, UnitArc of the FD boundary) need only supply geometric data and inherit `gWN = L/(2πi)` with specializations to `-1/2` and `-1/6`.
