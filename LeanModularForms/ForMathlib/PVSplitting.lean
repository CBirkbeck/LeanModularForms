/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.CauchyPrincipalValue

/-!
# PV Integral Splitting at Crossings

For a curve `γ : [0,1] → ℂ` with a unique crossing of point `s` at parameter `t₀`,
the PV cutoff integral splits into left and right pieces — the near-crossing part vanishes.

The key observation: when `‖γ(t) - s‖ ≤ ε` (i.e., `t` is near the crossing), the
cutoff integrand `if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0` is `0`.
On the far segments, the cutoff condition is satisfied so the integrand equals
`(γ t - s)⁻¹ * deriv γ t` a.e.

## Main results

* `pv_split_at_crossing` — the PV cutoff integral on `[0,1]` equals the sum of left
  and right integrals, where the middle part is zero.

* `pv_tendsto_of_crossing_limit` — if for small `ε` the far-segment integrals equal
  `E(ε)` and `E(ε) → L`, then the PV integral tends to `L`.

* `pv_tendsto_of_crossing_limit_asymmetric` — variant with different cutoff radii on
  left and right of the crossing point.
-/

open Set MeasureTheory Complex Filter intervalIntegral
open scoped Interval Topology

namespace PVSplitting

/-! ### Helper lemmas -/

/-- The cutoff integrand is zero wherever the curve is within `ε` of `s`. -/
private theorem cutoff_eq_zero_of_near {γ : ℝ → ℂ} {s : ℂ} {ε : ℝ}
    {a b : ℝ} (hab : a ≤ b)
    (h_near : ∀ t ∈ Icc a b, ‖γ t - s‖ ≤ ε) :
    ∀ t ∈ uIoc a b,
      (fun t => if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) t = 0 := by
  intro t ht
  rw [uIoc_of_le hab] at ht
  simp only
  rw [if_neg (not_lt.mpr (h_near t ⟨le_of_lt ht.1, ht.2⟩))]

/-- On a left segment `(0, a]` where the curve is `ε`-far from `s`,
the cutoff integrand agrees a.e. with the raw integrand. -/
private theorem cutoff_eq_integrand_ae_left {γ : ℝ → ℂ} {s : ℂ} {ε a : ℝ}
    (ha : 0 < a)
    (h_far : ∀ t ∈ Ico 0 a, ε < ‖γ t - s‖) :
    ∀ᵐ t ∂volume, t ∈ uIoc 0 a →
      (fun t => if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) t =
        (γ t - s)⁻¹ * deriv γ t := by
  have h_ne : ({a} : Set ℝ)ᶜ ∈ ae volume := by
    rw [mem_ae_iff, compl_compl]; exact (Set.finite_singleton _).measure_zero volume
  filter_upwards [h_ne] with t ht_ne ht_mem
  rw [uIoc_of_le (le_of_lt ha)] at ht_mem
  rw [if_pos (h_far t ⟨le_of_lt ht_mem.1,
    lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (Set.mem_singleton_iff.mpr h))⟩)]

/-- On a right segment `(b, 1]` where the curve is `ε`-far from `s`,
the cutoff integrand agrees a.e. with the raw integrand. -/
private theorem cutoff_eq_integrand_ae_right {γ : ℝ → ℂ} {s : ℂ} {ε b : ℝ}
    (hb : b < 1)
    (h_far : ∀ t ∈ Ioc b 1, ε < ‖γ t - s‖) :
    ∀ᵐ t ∂volume, t ∈ uIoc b 1 →
      (fun t => if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) t =
        (γ t - s)⁻¹ * deriv γ t := by
  have h_ne : ({b} : Set ℝ)ᶜ ∈ ae volume := by
    rw [mem_ae_iff, compl_compl]; exact (Set.finite_singleton _).measure_zero volume
  filter_upwards [h_ne] with t ht_ne ht_mem
  rw [uIoc_of_le (le_of_lt hb)] at ht_mem
  rw [if_pos (h_far t ⟨ht_mem.1, ht_mem.2⟩)]

/-- Given a.e. equality on `uIoc`, derive integrability of the cutoff integrand
from integrability of the raw integrand. -/
private theorem cutoff_intervalIntegrable_of_ae {F g : ℝ → ℂ} {a b : ℝ}
    (hint : IntervalIntegrable g volume a b)
    (hae : ∀ᵐ t ∂volume, t ∈ uIoc a b → F t = g t) :
    IntervalIntegrable F volume a b :=
  hint.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
    (hae.mono (fun _ ht hm => (ht hm).symm)))

/-! ### Asymmetric splitting -/

/-- Core asymmetric splitting: the PV cutoff integral on `[0,1]` equals left + right
integrals when the middle window `[t₀ - δL, t₀ + δR]` has the curve within `ε` of `s`,
and the outer segments have the curve `ε`-far from `s`. -/
private theorem pv_split_asymmetric {γ : ℝ → ℂ} {s : ℂ} {ε δL δR : ℝ}
    {t₀ : ℝ} (hδL : 0 < δL) (hδR : 0 < δR)
    (hδL_bd : δL < t₀) (hδR_bd : δR < 1 - t₀)
    (h_far_left : ∀ t ∈ Ico 0 (t₀ - δL), ε < ‖γ t - s‖)
    (h_far_right : ∀ t ∈ Ioc (t₀ + δR) 1, ε < ‖γ t - s‖)
    (h_near : ∀ t ∈ Icc (t₀ - δL) (t₀ + δR), ‖γ t - s‖ ≤ ε)
    (hint_left : IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t)
      volume 0 (t₀ - δL))
    (hint_right : IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t)
      volume (t₀ + δR) 1) :
    (∫ t in (0 : ℝ)..1,
      if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) =
    (∫ t in (0 : ℝ)..(t₀ - δL), (γ t - s)⁻¹ * deriv γ t) +
    (∫ t in (t₀ + δR)..1, (γ t - s)⁻¹ * deriv γ t) := by
  set F := fun t => if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0
  have h_left_lt : (0 : ℝ) < t₀ - δL := by linarith
  have h_mid_lt : t₀ - δL < t₀ + δR := by linarith
  have h_right_lt : t₀ + δR < 1 := by linarith
  have hF_mid := cutoff_eq_zero_of_near (le_of_lt h_mid_lt) h_near
  have hF_left := cutoff_eq_integrand_ae_left h_left_lt h_far_left
  have hF_right := cutoff_eq_integrand_ae_right h_right_lt h_far_right
  have hF_int_left := cutoff_intervalIntegrable_of_ae hint_left hF_left
  have hF_int_mid : IntervalIntegrable F volume (t₀ - δL) (t₀ + δR) :=
    (intervalIntegrable_const (c := (0 : ℂ))).congr (fun t ht => (hF_mid t ht).symm)
  have hF_int_right := cutoff_intervalIntegrable_of_ae hint_right hF_right
  calc ∫ t in (0 : ℝ)..1, F t
      _ = (∫ t in (0 : ℝ)..(t₀ - δL), F t) +
          (∫ t in (t₀ - δL)..(t₀ + δR), F t) +
          (∫ t in (t₀ + δR)..1, F t) := by
        rw [← integral_add_adjacent_intervals (hF_int_left.trans hF_int_mid) hF_int_right,
            ← integral_add_adjacent_intervals hF_int_left hF_int_mid]
      _ = (∫ t in (0 : ℝ)..(t₀ - δL), (γ t - s)⁻¹ * deriv γ t) + 0 +
          (∫ t in (t₀ + δR)..1, (γ t - s)⁻¹ * deriv γ t) := by
        rw [integral_congr_ae hF_left,
            integral_zero_ae (ae_of_all _ (fun t ht => hF_mid t ht)),
            integral_congr_ae hF_right]
      _ = _ := by ring

/-! ### Main theorems -/

/-- The PV cutoff integral on `[0,1]` splits at a crossing.

For `ε, δ > 0` with `δ < min t₀ (1 - t₀)`, if:
- the curve is far from `s` (norm `> ε`) outside the `δ`-window, and
- near to `s` (norm `≤ ε`) inside the `δ`-window,

then the full cutoff integral equals the sum of the left and right integrals of
`(γ t - s)⁻¹ * deriv γ t`. The middle piece vanishes because the cutoff sets the
integrand to `0` whenever `‖γ t - s‖ ≤ ε`. -/
theorem pv_split_at_crossing {γ : ℝ → ℂ} {s : ℂ} {ε δ : ℝ}
    {t₀ : ℝ} (_ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (_hε : 0 < ε) (hδ : 0 < δ)
    (hδ_small : δ < min t₀ (1 - t₀))
    (h_far : ∀ t ∈ Icc (0 : ℝ) 1, δ < |t - t₀| → ε < ‖γ t - s‖)
    (h_near : ∀ t, |t - t₀| ≤ δ → ‖γ t - s‖ ≤ ε)
    (hint_left : IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t)
      volume 0 (t₀ - δ))
    (hint_right : IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t)
      volume (t₀ + δ) 1) :
    (∫ t in (0 : ℝ)..1,
      if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) =
    (∫ t in (0 : ℝ)..(t₀ - δ), (γ t - s)⁻¹ * deriv γ t) +
    (∫ t in (t₀ + δ)..1, (γ t - s)⁻¹ * deriv γ t) := by
  have hδ_lt_left : δ < t₀ := lt_of_lt_of_le hδ_small (min_le_left _ _)
  have hδ_lt_right : δ < 1 - t₀ := lt_of_lt_of_le hδ_small (min_le_right _ _)
  exact pv_split_asymmetric hδ hδ hδ_lt_left hδ_lt_right
    (fun t ht => h_far t ⟨ht.1, le_trans (le_of_lt ht.2) (by linarith)⟩
      (by rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.2]))
    (fun t ht => h_far t ⟨le_trans (by linarith) (le_of_lt ht.1), ht.2⟩
      (by rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.1]))
    (fun t ht => h_near t (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]))
    hint_left hint_right

/-- Master crossing limit theorem on `[0,1]`: the PV integral of `(γ-s)⁻¹ · γ'`
along a curve with unique crossing at `t₀` tends to `L`, provided:
1. For small `ε`, the curve is `ε`-far from `s` except near `t₀`
2. The far-segment integrals sum to some expression `E(ε)`
3. `E(ε) → L` as `ε → 0⁺` -/
theorem pv_tendsto_of_crossing_limit
    {γ : ℝ → ℂ} {s : ℂ} {L : ℂ}
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    {δ : ℝ → ℝ} {threshold : ℝ} (hthresh : 0 < threshold)
    (hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε)
    (hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min t₀ (1 - t₀))
    (h_far : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Icc (0 : ℝ) 1, δ ε < |t - t₀| → ε < ‖γ t - s‖)
    (h_near : ∀ ε, 0 < ε → ε < threshold →
      ∀ t, |t - t₀| ≤ δ ε → ‖γ t - s‖ ≤ ε)
    {E : ℝ → ℂ}
    (h_ftc : ∀ ε, 0 < ε → ε < threshold →
      (∫ t in (0 : ℝ)..(t₀ - δ ε), (γ t - s)⁻¹ * deriv γ t) +
      (∫ t in (t₀ + δ ε)..1, (γ t - s)⁻¹ * deriv γ t) = E ε)
    (hint_left : ∀ ε, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume 0 (t₀ - δ ε))
    (hint_right : ∀ ε, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume (t₀ + δ ε) 1)
    (h_limit : Tendsto E (nhdsWithin 0 (Ioi 0)) (nhds L)) :
    Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..1,
        if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      (nhdsWithin 0 (Ioi 0)) (nhds L) := by
  have h_ev : (fun ε => ∫ t in (0 : ℝ)..1,
      if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      =ᶠ[nhdsWithin 0 (Ioi 0)] E := by
    filter_upwards [Ioo_mem_nhdsGT hthresh] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt : ε < threshold := hε.2
    rw [pv_split_at_crossing ht₀ hε_pos (hδ_pos ε hε_pos hε_lt)
        (hδ_small ε hε_pos hε_lt) (h_far ε hε_pos hε_lt) (h_near ε hε_pos hε_lt)
        (hint_left ε hε_pos hε_lt) (hint_right ε hε_pos hε_lt)]
    exact h_ftc ε hε_pos hε_lt
  exact h_limit.congr' h_ev.symm

set_option linter.unusedVariables false in
/-- Asymmetric crossing limit: allows different cutoff radii on left and right
of the crossing point. Needed for corner crossings (e.g., `ρ`, `ρ+1`) where
the geometry differs on each side (e.g., vertical segment vs arc). -/
theorem pv_tendsto_of_crossing_limit_asymmetric
    {γ : ℝ → ℂ} {s : ℂ} {L : ℂ}
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    {δ_left δ_right : ℝ → ℝ}
    {threshold : ℝ} (hthresh : 0 < threshold)
    (hδL_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_left ε)
    (hδR_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_right ε)
    (hδL_small : ∀ ε, 0 < ε → ε < threshold → δ_left ε < t₀)
    (hδR_small : ∀ ε, 0 < ε → ε < threshold → δ_right ε < 1 - t₀)
    (h_far_left : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Ico (0 : ℝ) (t₀ - δ_left ε), ε < ‖γ t - s‖)
    (h_far_right : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Ioc (t₀ + δ_right ε) 1, ε < ‖γ t - s‖)
    (h_near : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Icc (t₀ - δ_left ε) (t₀ + δ_right ε), ‖γ t - s‖ ≤ ε)
    {E : ℝ → ℂ}
    (h_ftc : ∀ ε, 0 < ε → ε < threshold →
      (∫ t in (0 : ℝ)..(t₀ - δ_left ε), (γ t - s)⁻¹ * deriv γ t) +
      (∫ t in (t₀ + δ_right ε)..1, (γ t - s)⁻¹ * deriv γ t) = E ε)
    (hint_left : ∀ ε, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t)
        volume 0 (t₀ - δ_left ε))
    (hint_right : ∀ ε, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t)
        volume (t₀ + δ_right ε) 1)
    (h_limit : Tendsto E (nhdsWithin 0 (Ioi 0)) (nhds L)) :
    Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..1,
        if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      (nhdsWithin 0 (Ioi 0)) (nhds L) := by
  have h_ev : (fun ε => ∫ t in (0 : ℝ)..1,
      if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      =ᶠ[nhdsWithin 0 (Ioi 0)] E := by
    filter_upwards [Ioo_mem_nhdsGT hthresh] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt : ε < threshold := hε.2
    exact (pv_split_asymmetric (hδL_pos ε hε_pos hε_lt) (hδR_pos ε hε_pos hε_lt)
      (hδL_small ε hε_pos hε_lt) (hδR_small ε hε_pos hε_lt)
      (h_far_left ε hε_pos hε_lt) (h_far_right ε hε_pos hε_lt)
      (h_near ε hε_pos hε_lt) (hint_left ε hε_pos hε_lt)
      (hint_right ε hε_pos hε_lt)).trans (h_ftc ε hε_pos hε_lt)
  exact h_limit.congr' h_ev.symm

end PVSplitting
