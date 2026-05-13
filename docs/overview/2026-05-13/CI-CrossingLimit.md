# ContourIntegral/CrossingLimit.lean Inventory

**Path**: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ContourIntegral/CrossingLimit.lean
**Lines**: 169
**Imports**: `LeanModularForms.ForMathlib.ContourIntegral.PVSplit`, `LeanModularForms.ForMathlib.ContourIntegral.SegmentFTC`, `Mathlib`

## Entries

### theorem `pv_tendsto_of_crossing_limit`
- **Type**: theorem
- **What**: Master crossing-limit theorem: the symmetric PV integral of `(γ-s)⁻¹·γ'` on `[a,b]` with unique crossing at `t₀` tends to `L` provided the far-segment FTC sum `E(ε)` tends to `L` and the geometric/integrability hypotheses hold (symmetric cutoff `δ(ε)`).
- **How**: `hab := ht₀.1.trans ht₀.2`. Build `h_ev : (fun ε => ε-truncated integral) =ᶠ[𝓝[>] 0] E` by `filter_upwards [Ioo_mem_nhdsGT hthresh]` with `ε`, extracting `hε_pos, hε_lt`; rewrite the truncated integral by `pv_split_at_crossing hab ht₀ hε_pos (hδ_pos ε hε_pos hε_lt) (hδ_small ε hε_pos hε_lt) (h_far ε ...) (h_near ε ...) (hint_left ε ...) (hint_right ε ...)`, then close with `h_ftc ε hε_pos hε_lt`. Conclude `h_limit.congr' h_ev.symm`.
- **Hypotheses**: `ht₀ : t₀ ∈ Ioo a b`, `hthresh : 0 < threshold`, `hδ_pos`/`hδ_small`/`h_far`/`h_near`/`h_ftc`/`hint_left`/`hint_right` quantified `∀ ε, 0 < ε → ε < threshold → ...`, `h_limit : Tendsto E (𝓝[>] 0) (𝓝 L)`.
- **Uses-from-project**: `pv_split_at_crossing` (from PVSplit), `Ioo_mem_nhdsGT`.
- **Used by**: All ValenceFormula winding-number crossing limit computations (i, ρ, ρ+1 corner cases, and the symmetric on-curve crossing).
- **Visibility**: public
- **Lines**: 41–69
- **Notes**: The general version of the pattern across 6 winding-number computations. `E(ε)` is typically `log(g(t₀-δ)) - log(g(t₀+δ))` with possible `-2πi` branch-cut correction (e.g. at `i`).

### theorem `pv_tendsto_of_crossing_limit_asymmetric`
- **Type**: theorem
- **What**: Asymmetric crossing-limit theorem: same as `pv_tendsto_of_crossing_limit` but with independent left/right cutoff radii `δ_left ε`, `δ_right ε`. Required for corner crossings (ρ, ρ+1) where vertical-segment and arc geometries differ.
- **How**: `hab := ht₀.1.trans ht₀.2`. Build `h_ev` via `filter_upwards [Ioo_mem_nhdsGT hthresh]` over `ε`. Obtain `hδL, hδR, hδL_bd, hδR_bd` and derive `h_left_lt : a < t₀ - δ_left ε`, `h_right_lt : t₀ + δ_right ε < b`, `h_mid_lt`. Set `F := fun t => if ‖γ t - s‖ > ε then ... else 0`. Show three integrability facts: `hF_mid` (zero on mid interval via `h_near` and `if_neg`), `hF_left` (a.e. equal to integrand via cofinite-measure-zero singleton excluded from `uIoc`, then `if_pos` from `h_far_left`), `hF_right` (analogous via `h_far_right`). Build `hF_int_left/_mid/_right : IntervalIntegrable F volume ...` via `.congr_ae` and `ae_restrict_iff' measurableSet_uIoc`. Split `∫_a^b F = ∫_a^{t₀-δL} + ∫_{t₀-δL}^{t₀+δR} + ∫_{t₀+δR}^b` via `intervalIntegral.integral_add_adjacent_intervals` (applied twice); `h_mid_zero` via `intervalIntegral.integral_zero_ae`; `h_eq_left`, `h_eq_right` via `intervalIntegral.integral_congr_ae`. `change ∫ t in a..b, F t = E ε`, rewrite via `h_split, h_mid_zero, h_eq_left, h_eq_right`, `simp only [add_zero]`, close with `h_ftc ε hε_pos hε_lt`. Conclude `h_limit.congr' h_ev.symm`.
- **Hypotheses**: `ht₀ : t₀ ∈ Ioo a b`, `hthresh : 0 < threshold`, `hδL_pos`/`hδR_pos`/`hδL_small`/`hδR_small`/`h_far_left` (on `Ico a (t₀-δL ε)`)/`h_far_right` (on `Ioc (t₀+δR ε) b`)/`h_near` (on `Icc (t₀-δL ε) (t₀+δR ε)`)/`h_ftc`/`hint_left`/`hint_right`, `h_limit : Tendsto E (𝓝[>] 0) (𝓝 L)`.
- **Uses-from-project**: `Ioo_mem_nhdsGT`. (Self-contained PV-split implementation rather than calling `pv_split_at_crossing`.)
- **Used by**: Asymmetric corner-crossing FTC computations (ρ, ρ+1 in the ValenceFormula chain).
- **Visibility**: public
- **Lines**: 74–167
- **Notes**: ~93 lines. Reimplements the PV split inline because the asymmetric setup has no off-the-shelf split lemma. Uses `(Set.finite_singleton _).measure_zero` to discard the partition-point set, and `.congr_ae`/`.congr` to interconvert `F` with `(γ-s)⁻¹·γ'` on far segments.

## File Summary

Two public theorems in `namespace ContourIntegral`: a symmetric and an asymmetric "crossing limit" master theorem. Both reduce computing `lim_{ε→0⁺} ∫ ε-truncated PV` to (i) showing the path is ε-far from `s` off a small interval `[t₀-δ, t₀+δ]` (resp. `[t₀-δL, t₀+δR]`), (ii) FTC-evaluating the far segments to get some `E(ε)`, (iii) showing `E(ε) → L`. The symmetric version delegates the split to `pv_split_at_crossing`; the asymmetric version inlines the split with three-piece additivity and a.e. integrand replacement. These are the central tools for every winding-number computation at elliptic and corner points in the ValenceFormula chain.
