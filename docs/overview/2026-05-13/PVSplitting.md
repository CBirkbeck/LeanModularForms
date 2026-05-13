# PVSplitting.lean Inventory

**Path**: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/PVSplitting.lean`
**Namespace**: `PVSplitting`
**Imports**: `LeanModularForms.ForMathlib.CauchyPrincipalValue`

---

### private theorem `cutoff_eq_zero_of_near`
- **Type**: `∀ {γ : ℝ → ℂ} {s : ℂ} {ε a b : ℝ}, a ≤ b → (∀ t ∈ Icc a b, ‖γ t - s‖ ≤ ε) → ∀ t ∈ uIoc a b, (fun t => if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) t = 0`
- **What**: The cutoff integrand vanishes pointwise on `[a,b]` whenever the curve is within `ε` of the crossing point `s`.
- **How**: Unfolds `uIoc_of_le hab`, then `if_neg (not_lt.mpr (h_near …))` discharges the branch.
- **Hypotheses**: ordered endpoints `a ≤ b`; uniform near-bound on `Icc a b`.
- **Uses-from-project**: none beyond Mathlib (`uIoc_of_le`, `if_neg`, `not_lt`).
- **Used by**: `pv_split_asymmetric` (zero-middle step).
- **Visibility**: private
- **Lines**: 38–45
- **Notes**: Direct pointwise statement (no a.e.); covers the closed middle window.

### private theorem `cutoff_eq_integrand_ae_left`
- **Type**: a.e. (volume) on `uIoc 0 a`, the cutoff integrand equals `(γ t - s)⁻¹ * deriv γ t`.
- **What**: On a left far-segment the cutoff selector is `true` away from the measure-zero endpoint `{a}`.
- **How**: Excludes `{a}` via `Set.finite_singleton _).measure_zero`, `filter_upwards`, then `if_pos (h_far …)` using strict bound from `lt_of_le_of_ne`.
- **Hypotheses**: `0 < a`; strict far bound on `Ico 0 a`.
- **Uses-from-project**: none beyond Mathlib.
- **Used by**: `pv_split_asymmetric` (left-segment integrability/integral congruence).
- **Visibility**: private
- **Lines**: 49–60
- **Notes**: Excises the right endpoint where `‖γ a - s‖ = ε` is permitted.

### private theorem `cutoff_eq_integrand_ae_right`
- **Type**: a.e. on `uIoc b 1`, the cutoff integrand equals `(γ t - s)⁻¹ * deriv γ t`.
- **What**: Right-side symmetric counterpart of `cutoff_eq_integrand_ae_left`.
- **How**: Same template — exclude `{b}` from `ae volume`, `filter_upwards`, then `if_pos (h_far …)` with `ht_mem.1, ht_mem.2`.
- **Hypotheses**: `b < 1`; strict far bound on `Ioc b 1`.
- **Uses-from-project**: none beyond Mathlib.
- **Used by**: `pv_split_asymmetric` (right-segment a.e. equality).
- **Visibility**: private
- **Lines**: 64–74
- **Notes**: Excises the left endpoint of the segment.

### private theorem `cutoff_intervalIntegrable_of_ae`
- **Type**: `IntervalIntegrable g volume a b → (∀ᵐ t, t ∈ uIoc a b → F t = g t) → IntervalIntegrable F volume a b`.
- **What**: Transfers interval integrability from a reference function `g` to a function `F` agreeing a.e. on `uIoc a b`.
- **How**: `hint.congr_ae` after lifting via `ae_restrict_iff' measurableSet_uIoc` (3-line proof).
- **Hypotheses**: `g` interval-integrable; a.e. equality conditional on membership.
- **Uses-from-project**: none beyond Mathlib.
- **Used by**: `pv_split_asymmetric` (integrability of the cutoff integrand on far segments).
- **Visibility**: private
- **Lines**: 78–83
- **Notes**: Small reusable adapter.

### private theorem `pv_split_asymmetric`
- **Type**: cutoff integral on `[0,1]` equals sum of left integral on `[0, t₀-δL]` and right on `[t₀+δR, 1]`.
- **What**: Core asymmetric split: zero-middle window plus a.e. agreement on far segments yields the decomposition.
- **How**: Calculation chain via `integral_add_adjacent_intervals` (applied twice), then `integral_congr_ae`, `integral_zero_ae`, and `ring` (proof spans lines 100–123, >10 lines; key lemmas named).
- **Hypotheses**: positivity `0 < δL, δR`; window strictly inside `(0,1)` (`δL < t₀`, `δR < 1 - t₀`); far/near triplet on `Ico 0 (t₀-δL)`, `Ioc (t₀+δR) 1`, `Icc (t₀-δL) (t₀+δR)`; interval-integrability on both far segments.
- **Uses-from-project**: `cutoff_eq_zero_of_near`, `cutoff_eq_integrand_ae_left`, `cutoff_eq_integrand_ae_right`, `cutoff_intervalIntegrable_of_ae`.
- **Used by**: `pv_split_at_crossing`; `pv_tendsto_of_crossing_limit_asymmetric`.
- **Visibility**: private
- **Lines**: 90–123
- **Notes**: Asymmetric radii crucial for corner crossings (e.g. `ρ`, `ρ+1`).

### theorem `pv_split_at_crossing`
- **Type**: symmetric split: cutoff integral = `∫₀^{t₀-δ} + ∫_{t₀+δ}^1` of raw integrand.
- **What**: Symmetric specialization of `pv_split_asymmetric` with a single radius `δ` controlled by `min t₀ (1-t₀)`.
- **How**: Reduces both `δL := δ` and `δR := δ` to `pv_split_asymmetric`; supplies `Ico/Ioc` far-witnesses by `abs_of_nonpos / abs_of_nonneg` and `linarith` (15-line proof; main lemma is `pv_split_asymmetric`).
- **Hypotheses**: `t₀ ∈ Ioo 0 1`; `0 < ε`, `0 < δ`, `δ < min t₀ (1 - t₀)`; `|t - t₀|`-based far/near; integrability on both far segments.
- **Uses-from-project**: `pv_split_asymmetric`.
- **Used by**: `pv_tendsto_of_crossing_limit`.
- **Visibility**: public (no modifier)
- **Lines**: 136–163
- **Notes**: `_ht₀`/`_hε` unused but kept for symmetry of the API.

### theorem `pv_tendsto_of_crossing_limit`
- **Type**: under symmetric crossing data, the cutoff PV integral tends to `L` as `ε → 0⁺`.
- **What**: Master crossing-limit theorem on `[0,1]`: from a symmetric `δ(ε)` and an FTC-form `E(ε)` that tends to `L`, the cutoff integral also tends to `L`.
- **How**: Builds an eventual equality `cutoff = E` near 0 via `Ioo_mem_nhdsGT hthresh` + `pv_split_at_crossing` + `h_ftc`, then `h_limit.congr' h_ev.symm` (11-line proof; main lemma is `pv_split_at_crossing`).
- **Hypotheses**: `t₀ ∈ Ioo 0 1`; threshold positivity; `δ` positive, small, controlling far/near, plus FTC identity and integrability for each `ε ∈ (0, threshold)`; `E → L`.
- **Uses-from-project**: `pv_split_at_crossing`.
- **Used by**: downstream PV chain that delivers limits as `ε → 0⁺`.
- **Visibility**: public
- **Lines**: 170–200
- **Notes**: Filter base is `nhdsWithin 0 (Ioi 0)`.

### theorem `pv_tendsto_of_crossing_limit_asymmetric`
- **Type**: asymmetric variant: separate `δ_left, δ_right` cutoff radii on either side of `t₀`.
- **What**: Master crossing-limit allowing different radii — used at corner crossings where geometry is asymmetric (e.g. vertical edge meets arc).
- **How**: Same skeleton as the symmetric version but routes through `pv_split_asymmetric` directly; eventual equality + `h_limit.congr'` (12-line proof; main lemma is `pv_split_asymmetric`).
- **Hypotheses**: `t₀ ∈ Ioo 0 1`; threshold positivity; positivity, smallness, far on `Ico`/`Ioc`, near on the joined `Icc`, FTC identity, integrability — all parameterised by `ε`; `E → L`.
- **Uses-from-project**: `pv_split_asymmetric`.
- **Used by**: corner-crossing limit infrastructure in the PV chain.
- **Visibility**: public; `set_option linter.unusedVariables false` is in effect.
- **Lines**: 206–243
- **Notes**: Linter option suppresses unused-binding warnings for the optional `ht₀`/`hthresh`.

---

## File Summary

PVSplitting.lean establishes the splitting principle behind Cauchy-principal-value integrals at curve crossings. Four `private` helpers (`cutoff_eq_zero_of_near`, two a.e. equalities on far segments, and an integrability transfer) feed a `private` asymmetric core lemma `pv_split_asymmetric`; that core powers the public API `pv_split_at_crossing` (symmetric exact split) plus the two `Tendsto`-style limit theorems `pv_tendsto_of_crossing_limit` and `pv_tendsto_of_crossing_limit_asymmetric` driving `ε → 0⁺` arguments. The asymmetric variant exists specifically for corner crossings such as `ρ`, `ρ+1` where the cutoff geometries differ on the two sides.
