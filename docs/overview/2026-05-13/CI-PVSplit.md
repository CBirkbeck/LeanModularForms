# /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ContourIntegral/PVSplit.lean

## theorem `ContourIntegral.pv_split_at_crossing`
- **Type**: For `γ : ℝ → ℂ`, `a < b`, `t₀ ∈ Ioo a b`, `ε δ > 0`, `δ < min (t₀ - a) (b - t₀)`,
  far/near witnesses `h_far`, `h_near`, plus left/right interval integrability:
  `(∫ t in a..b, if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
   = (∫ t in a..(t₀ - δ), (γ t - s)⁻¹ * deriv γ t) +
     (∫ t in (t₀ + δ)..b, (γ t - s)⁻¹ * deriv γ t)`.
- **What**: The PV cutoff integral splits at a unique crossing into a left
  segment, a middle segment that vanishes, and a right segment. The cutoff
  forces the integrand to 0 on the near-crossing window `(t₀ - δ, t₀ + δ)`.
- **How**: Let `F t := if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0`.
  Three a.e.-equality / pointwise facts: (i) `hF_mid` shows `F = 0` on
  `uIoc (t₀ - δ) (t₀ + δ)` using `h_near`; (ii) `hF_left` and `hF_right`
  show `F t = (γ t - s)⁻¹ * deriv γ t` a.e. on the side intervals (modulo a
  null endpoint set) using `h_far`. Combine via
  `IntervalIntegrable.congr_ae` + `integral_add_adjacent_intervals` to split
  `∫_a^b F` into three adjacent pieces; the middle equals 0 by
  `integral_congr_ae` + `integral_zero`; rewrite the side pieces with
  `integral_congr_ae hF_left` / `hF_right`; finish with `ring`.
- **Hypotheses**: `a < b` (unused name `_hab`); `t₀ ∈ Ioo a b`; `0 < ε`
  (unused name `_hε`); `0 < δ`; `δ < min (t₀ - a) (b - t₀)`; `h_far`,
  `h_near` characterising far/near behaviour; `IntervalIntegrable` on each
  side interval.
- **Uses-from-project**: imports `LeanModularForms.ForMathlib.ClassicalCPV`
  (for the `pv` cutoff integrand convention; the proof itself only uses
  mathlib).
- **Used by**: Downstream PV-decomposition assemblies in the contour-integral
  layer (consumed where a single crossing is isolated and the residue/CPV
  is taken as the symmetric limit).
- **Visibility**: public (`theorem`); namespace `ContourIntegral`.
- **Lines**: 38-108 (proof body lines 47-108).
- **Notes**: Heavy use of `uIoc_of_le`, `Set.finite_singleton.measure_zero`
  to drop boundary points, and `filter_upwards`. The two integrability
  hypotheses are stated on the same direction (`a..(t₀-δ)` and
  `(t₀+δ)..b`), so `IntervalIntegrable.trans`/`integral_add_adjacent_intervals`
  apply directly.

## File Summary
A single theorem `pv_split_at_crossing` (one public declaration) that splits
the PV cutoff integral of `(γ-s)⁻¹ * γ'` at an isolated crossing into a sum
of left and right integrals, with the middle window contributing 0. Pure
mathlib + the `ClassicalCPV` import for the cutoff convention. Self-contained
proof, ~70 lines, axiom-clean (no `sorry`).
