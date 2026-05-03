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
  refine h_S.congr' ?_
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Ioo 0 δ, Ioo_mem_nhdsGT hδ_pos, ?_⟩
  intro ε hε
  have hε_pos : 0 < ε := hε.1
  have hε_lt : ε < δ := hε.2
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (zero_le_one' ℝ)] at ht
  -- For t ∈ [0,1] and ε < δ:
  -- cpvIntegrandOn S = 0 ↔ ∃ s ∈ S, ‖γ t - s‖ ≤ ε
  -- cpvIntegrandOn T = 0 ↔ ∃ s' ∈ T, ‖γ t - s'‖ ≤ ε
  -- The latter is iff (∃ s ∈ S, ...) ∨ (∃ s' ∈ T \ S, ...)
  -- For s' ∈ T \ S: ‖γ t - s'‖ ≥ δ > ε, so the second disjunct is false
  -- Hence cpvIntegrandOn T = cpvIntegrandOn S
  simp only [cpvIntegrandOn]
  congr 1
  · -- if-condition: same set membership
    apply propext
    constructor
    · rintro ⟨s, hs, hs_le⟩
      exact ⟨s, hST hs, hs_le⟩
    · rintro ⟨s, hs, hs_le⟩
      by_cases h_in_S : s ∈ S
      · exact ⟨s, h_in_S, hs_le⟩
      · -- s ∈ T \ S — use avoidance
        exfalso
        have hs_in_diff : s ∈ T \ S := Finset.mem_sdiff.mpr ⟨hs, h_in_S⟩
        have h_far : δ ≤ ‖γ t - s‖ := h_avoid s hs_in_diff t ht
        have h_eq : γ.toPath.extend t = γ t := by
          rw [PiecewiseC1Path.extendedPath_eq]
        rw [h_eq] at hs_le
        linarith

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
  apply hasCauchyPVOn_extend_of_avoid {s} S (Finset.singleton_subset_iff.mpr hs)
    _ γ hδ_pos _ h_singleton
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
  -- Each singleton lifts to S via extension
  have h_each_S : ∀ s ∈ S,
      HasCauchyPVOn S (fun z => (1 : ℂ) / (z - s) ^ k) γ 0 := by
    intro s hs
    exact hasCauchyPVOn_multipole_pow_inv_of_singleton S hs γ hδ_pos
      (fun s' hs' h_ne_s => h_avoid s hs s' hs' h_ne_s) (h_singletons s hs)
  -- Multiply by c s: HasCauchyPVOn is closed under const_mul
  -- Use HasCauchyPVOn.finset_sum
  have h_each_scaled : ∀ s ∈ S,
      HasCauchyPVOn S (fun z => c s / (z - s) ^ k) γ 0 := by
    intro s hs
    have h := (h_each_S s hs).smul (c s)
    rw [show (fun z => c s * ((1 : ℂ) / (z - s) ^ k)) =
      (fun z => c s / (z - s) ^ k) from funext fun z => by ring,
      mul_zero] at h
    exact h
  have h_sum := HasCauchyPVOn.finset_sum S h_each_scaled
    (fun s hs ε hε => h_int_each s hs ε hε)
  simpa only [Finset.sum_const_zero] using h_sum

end LeanModularForms

end
