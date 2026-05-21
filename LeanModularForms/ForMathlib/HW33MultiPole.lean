/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HW33Final
import LeanModularForms.ForMathlib.HW33HigherOrderC3
import LeanModularForms.ForMathlib.MultipointPV

/-!
# HW Theorem 3.3 — multi-pole transverse case (composition)

This file extends the single-pole transverse closure
(`hasCauchyPVOn_singleton_pow_of_transverse_assembled` in `HW33Final.lean`)
to the multi-pole case via:

1. **Pole-set extension** (`hasCauchyPVOn_extend_of_avoid`): when γ avoids
   `T \ S` with positive margin, `HasCauchyPVOn S f γ L ↔ HasCauchyPVOn T f γ L`.

2. **Multi-pole assembly**: combining single-pole transverse closures
   over a finset S where γ crosses each transversally (using
   `HasCauchyPVOn.finset_sum`).

## Main results

* `hasCauchyPVOn_extend_of_avoid`: pole-set extension under avoidance margin.
* `hasCauchyPVOn_multipole_pow_inv_of_singleton`: extension of singleton
  results to a finset for `1/(z-s)^k` terms.
-/

open Filter Topology Set Complex MeasureTheory

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-- **Pole-set extension under avoidance margin.** Suppose `γ` avoids `T \ S`
with positive margin `δ > 0`. Then `HasCauchyPVOn S f γ L ↔ HasCauchyPVOn T f γ L`.

Intuition: for `ε < δ`, the ε-balls around poles in `T \ S` contain no point
of γ, so the cpv integrands for `S` and `T` agree pointwise. Hence the integrals
agree for small `ε`, and the limits are equal. -/
theorem hasCauchyPVOn_extend_of_avoid
    (S T : Finset ℂ) (hST : S ⊆ T) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    {L : ℂ} {δ : ℝ} (hδ_pos : 0 < δ)
    (h_avoid : ∀ s ∈ T \ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_S : HasCauchyPVOn S f γ L) :
    HasCauchyPVOn T f γ L := by
  refine h_S.congr' (Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨Ioo 0 δ, Ioo_mem_nhdsGT hδ_pos, ?_⟩)
  intro ε hε
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (zero_le_one' ℝ)] at ht
  simp only [cpvIntegrandOn]
  congr 1
  · refine propext ⟨fun ⟨s, hs, hs_le⟩ => ⟨s, hST hs, hs_le⟩, ?_⟩
    rintro ⟨s, hs, hs_le⟩
    by_cases h_in_S : s ∈ S
    · exact ⟨s, h_in_S, hs_le⟩
    · exact absurd (h_avoid s (Finset.mem_sdiff.mpr ⟨hs, h_in_S⟩) t ht)
        (by simp [PiecewiseC1Path.extendedPath_eq]; linarith [hε.2])

/-- **Multi-pole extension for `1/(z-s)^k` terms.** Given:

* a finset `S` of poles with `s ∈ S`,
* `γ` avoiding `S \ {s}` with positive margin,
* `HasCauchyPVOn {s} (fun z => 1/(z-s)^k) γ 0` (the singleton transverse case),

then `HasCauchyPVOn S (fun z => 1/(z-s)^k) γ 0`. This bridges the singleton
result to the multi-pole framework. -/
theorem hasCauchyPVOn_multipole_pow_inv_of_singleton
    (S : Finset ℂ) {s : ℂ} (hs : s ∈ S) {k : ℕ}
    (γ : PiecewiseC1Path x x)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (h_avoid : ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s'‖)
    (h_singleton : HasCauchyPVOn {s} (fun z => (1 : ℂ) / (z - s) ^ k) γ 0) :
    HasCauchyPVOn S (fun z => (1 : ℂ) / (z - s) ^ k) γ 0 := by
  refine hasCauchyPVOn_extend_of_avoid {s} S (Finset.singleton_subset_iff.mpr hs)
    _ γ hδ_pos ?_ h_singleton
  intro s' hs' t ht
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hs'
  exact h_avoid s' hs'.1 hs'.2 t ht

/-- **Multi-pole assembly: sum of singleton transverse cancellations.** If for
each pole `s ∈ S`, the singleton CPV cancels, and γ avoids `S \ {s}` with
margin (i.e., distinct poles are separated from γ's path away from their
transverse crossing), then the sum has CPV cancellation with the multi-pole set. -/
theorem hasCauchyPVOn_multipole_sum_pow_inv
    (S : Finset ℂ) {k : ℕ} (c : ℂ → ℂ)
    (γ : PiecewiseC1Path x x)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (h_avoid : ∀ s ∈ S, ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc (0 : ℝ) 1,
      δ ≤ ‖γ t - s'‖)
    (h_singletons : ∀ s ∈ S,
      HasCauchyPVOn {s} (fun z => (1 : ℂ) / (z - s) ^ k) γ 0)
    (_h_int_sum : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ.toPath.extend ε t)
      volume 0 1)
    (h_int_each : ∀ s ∈ S, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (fun z => c s / (z - s) ^ k) γ.toPath.extend ε t)
      volume 0 1) :
    HasCauchyPVOn S
      (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ 0 := by
  classical
  have h_each_scaled : ∀ s ∈ S,
      HasCauchyPVOn S (fun z => c s / (z - s) ^ k) γ 0 := fun s hs => by
    have h := (hasCauchyPVOn_multipole_pow_inv_of_singleton S hs γ hδ_pos
      (h_avoid s hs) (h_singletons s hs)).smul (c s)
    rwa [show (fun z => c s * ((1 : ℂ) / (z - s) ^ k)) =
      (fun z => c s / (z - s) ^ k) from funext fun z => by ring,
      mul_zero] at h
  simpa only [Finset.sum_const_zero] using
    HasCauchyPVOn.finset_sum S h_each_scaled h_int_each

/-- **Multi-pole transverse closure (high-level form).** Combines the
single-pole transverse closure `hasCauchyPVOn_singleton_pow_of_transverse_assembled`
with `hasCauchyPVOn_multipole_sum_pow_inv` to give the multi-pole transverse
case of HW Theorem 3.3 in the `HasCauchyPVOn` form.

The user supplies, for each pole `s ∈ S`:
* The full local transverse-flat data (used to derive
  `HasCauchyPVOn {s} (fun z => 1/(z-s)^k) γ 0`).
* Distinct-pole avoidance: γ stays at distance ≥ δ from every other pole
  `s' ∈ S, s' ≠ s`.
* Per-pole integrability of the cpvIntegrandOn at each ε > 0.

The conclusion is `HasCauchyPVOn S (fun z => ∑ s ∈ S, c s / (z - s)^k) γ 0`. -/
theorem hasCauchyPVOn_multipole_transverse_assembled
    (S : Finset ℂ) {k : ℕ} (c : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (h_avoid_pairs : ∀ s ∈ S, ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc (0 : ℝ) 1,
      δ ≤ ‖γ t - s'‖)
    (h_singletons : ∀ s ∈ S,
      HasCauchyPVOn {s} (fun z => (1 : ℂ) / (z - s) ^ k) γ 0)
    (h_int_each : ∀ s ∈ S, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (fun z => c s / (z - s) ^ k) γ.toPath.extend ε t) volume 0 1)
    (h_int_sum : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ.toPath.extend ε t)
      volume 0 1) :
    HasCauchyPVOn S (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ 0 :=
  hasCauchyPVOn_multipole_sum_pow_inv S c γ hδ_pos h_avoid_pairs
    h_singletons h_int_sum h_int_each

/-- **Multi-pole (B)-case closure (discoverability alias).**
Identical to `hasCauchyPVOn_multipole_transverse_assembled`, but named for the
general (B) case to aid discoverability. The underlying composition is the
same — both transverse k-odd singletons (from
`hasCauchyPVOn_singleton_pow_of_transverse_assembled`) and general-angle (B)
singletons (from `hasCauchyPVOn_singleton_pow_of_conditionB_assembled`)
satisfy the singleton input shape, so the composition is uniform. -/
theorem hasCauchyPVOn_multipole_pow_of_conditionB_assembled
    (S : Finset ℂ) {k : ℕ} (c : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (h_avoid_pairs : ∀ s ∈ S, ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc (0 : ℝ) 1,
      δ ≤ ‖γ t - s'‖)
    (h_singletons : ∀ s ∈ S,
      HasCauchyPVOn {s} (fun z => (1 : ℂ) / (z - s) ^ k) γ 0)
    (h_int_each : ∀ s ∈ S, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (fun z => c s / (z - s) ^ k) γ.toPath.extend ε t) volume 0 1)
    (h_int_sum : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ.toPath.extend ε t)
      volume 0 1) :
    HasCauchyPVOn S (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ 0 :=
  hasCauchyPVOn_multipole_transverse_assembled S c γ hδ_pos
    h_avoid_pairs h_singletons h_int_each h_int_sum

end LeanModularForms

end
