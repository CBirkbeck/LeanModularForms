import LeanModularForms.ContourIntegral.PVSplit
import LeanModularForms.ContourIntegral.SegmentFTC
import Mathlib

/-!
# Crossing Limit Theorem

The master theorem: for a closed piecewise C1 curve with a unique crossing
at t₀, the PV integral of (γ-s)⁻¹ · γ' equals the limit of the log ratio
log(g(t₀-δ)) - log(g(t₀+δ)) as δ → 0⁺.

This combines PVSplit (integral splitting) with SegmentFTC (telescoping)
to reduce PV computation to a single crossing-local limit.

## Main results

* `pv_tendsto_of_crossing_limit` — the PV integral tends to L if the log
  ratio at the crossing tends to L
-/

open Set MeasureTheory Complex Filter

namespace ContourIntegral

/-- Master crossing limit theorem: the PV integral of (γ-s)⁻¹ · γ' along a
curve with unique crossing at t₀ tends to L, provided:
1. For small ε, the curve is ε-far from s except near t₀
2. The far-segment integrals sum to some expression E(ε)
3. E(ε) → L as ε → 0⁺

The expression E(ε) is typically `log(g(t₀-δ)) - log(g(t₀+δ))` (simple case)
or `log(g(t₀-δ)) - log(g(t₀+δ)) + correction` (when the curve crosses a
branch cut of complex log, e.g., the `-2πi` correction at the elliptic point i).

This is the general version of the pattern used in all 6 ValenceFormula
winding number computations. -/
theorem pv_tendsto_of_crossing_limit
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} {L : ℂ}
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    {δ : ℝ → ℝ}
    {threshold : ℝ} (hthresh : 0 < threshold)
    (hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε)
    (hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min (t₀ - a) (b - t₀))
    (h_far : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Icc a b, δ ε ≤ |t - t₀| → ε < ‖γ t - s‖)
    (h_near : ∀ ε, 0 < ε → ε < threshold →
      ∀ t, |t - t₀| ≤ δ ε → ‖γ t - s‖ ≤ ε)
    -- The far-segment integrals equal some expression E(ε)
    {E : ℝ → ℂ}
    (h_ftc : ∀ ε, 0 < ε → ε < threshold →
      (∫ t in a..(t₀ - δ ε), (γ t - s)⁻¹ * deriv γ t) +
      (∫ t in (t₀ + δ ε)..b, (γ t - s)⁻¹ * deriv γ t) = E ε)
    (hint_left : ∀ ε, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume a (t₀ - δ ε))
    (hint_right : ∀ ε, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume (t₀ + δ ε) b)
    -- E(ε) → L
    (h_limit : Tendsto E (nhdsWithin 0 (Ioi 0)) (nhds L)) :
    Tendsto (fun ε =>
      ∫ t in a..b, if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      (nhdsWithin 0 (Ioi 0)) (nhds L) := by
  have hab : a < b := lt_trans ht₀.1 ht₀.2
  have h_ev : (fun ε => ∫ t in a..b, if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      =ᶠ[nhdsWithin 0 (Ioi 0)] E := by
    filter_upwards [Ioo_mem_nhdsGT hthresh] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt : ε < threshold := hε.2
    rw [pv_split_at_crossing hab ht₀ hε_pos (hδ_pos ε hε_pos hε_lt)
        (hδ_small ε hε_pos hε_lt) (h_far ε hε_pos hε_lt) (h_near ε hε_pos hε_lt)
        (hint_left ε hε_pos hε_lt) (hint_right ε hε_pos hε_lt)]
    exact h_ftc ε hε_pos hε_lt
  exact h_limit.congr' h_ev.symm

end ContourIntegral
