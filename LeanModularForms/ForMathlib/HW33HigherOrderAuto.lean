/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HW33HigherOrderC4

/-!
# Auto-discharge wrappers for the higher-order avoidance theorems

This file provides user-friendly wrappers around `HW33HigherOrderC3.lean` that
auto-discharge the integrability hypotheses when `γ` is Lipschitz and avoids
the pole `s` with positive margin.

## Main results

* `intervalIntegrable_pow_inv_mul_deriv_of_avoids`: integrability of
  `1/(γ - s)^k · γ'` for Lipschitz γ avoiding `s` with positive margin.
-/

open Filter Topology MeasureTheory Set Complex
open scoped Classical Real Interval

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-! ## Integrability helpers (Lipschitz + avoidance) -/

/-- **Integrability of `1/(γ - s)^k · γ'` from Lipschitz + avoidance.** When `γ`
is Lipschitz and avoids `s` with positive margin `δ > 0`, the integrand
`1/(γ(t) - s)^k · γ'(t)` is interval-integrable on `[0, 1]`.

Proof: `1/(γ - s)^k` is `ContinuousOn (Icc 0 1)` (since `γ - s` is continuous and
nonzero by avoidance) hence essentially bounded by `1/δ^k`. The Lipschitz
hypothesis gives integrability of `deriv γ` on `Ioc 0 1` (via the Lipschitz
norm bound `K`). Combining via `Integrable.bdd_mul`. -/
theorem intervalIntegrable_pow_inv_mul_deriv_of_avoids
    (γ : PiecewiseC1Path x x) (s : ℂ) (k : ℕ) {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_bd : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ.toPath.extend t - s‖)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    IntervalIntegrable
      (fun t => 1 / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t)
      volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
  -- deriv γ is integrable on Ioc 0 1 (Lipschitz ⇒ bounded by K)
  have h_deriv_int : IntegrableOn (deriv γ.toPath.extend) (Ioc (0 : ℝ) 1) volume :=
    MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (stronglyMeasurable_deriv _).aestronglyMeasurable
      (ae_restrict_of_ae (Filter.Eventually.of_forall
        (fun _ => norm_deriv_le_of_lipschitz hLip)))
  -- The factor 1/(γ - s)^k is continuous on Icc 0 1 with the right bound
  have h_ne : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t - s ≠ 0 := fun t ht hzero => by
    have := hδ_bd t ht
    rw [hzero, norm_zero] at this
    linarith
  have h_cont : ContinuousOn
      (fun t => (1 : ℂ) / (γ.toPath.extend t - s) ^ k) (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const
    · exact ((γ.toPath.continuous_extend.continuousOn).sub continuousOn_const).pow k
    · exact fun t ht => pow_ne_zero _ (h_ne t ht)
  have h_meas : AEStronglyMeasurable
      (fun t => (1 : ℂ) / (γ.toPath.extend t - s) ^ k)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (h_cont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have h_bound_ae : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖(1 : ℂ) / (γ.toPath.extend t - s) ^ k‖ ≤ 1 / δ ^ k := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht_Icc : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    rw [norm_div, norm_one, norm_pow]
    apply div_le_div_of_nonneg_left zero_le_one (pow_pos hδ_pos k)
    exact pow_le_pow_left₀ (le_of_lt hδ_pos) (hδ_bd t ht_Icc) k
  exact h_deriv_int.bdd_mul h_meas h_bound_ae

/-! ## Auto-discharge wrappers for the higher-order avoidance theorems -/

/-- **C-3 single-power avoidance, integrability auto-derived (Lipschitz form).**
For `γ` Lipschitz avoiding `S` with positive margin, the higher-order polar sum
`∑ s ∈ S, c s / (z - s)^k` (`k ≥ 2`) has CPV zero. The interval-integrability
hypothesis of `hasCauchyPVOn_finset_pow_inv_of_avoids` is auto-discharged via
`intervalIntegrable_pow_inv_mul_deriv_of_avoids`. -/
theorem hasCauchyPVOn_finset_pow_inv_of_avoids_lip
    (S : Finset ℂ) (k : ℕ) (hk : 2 ≤ k) (c : ℂ → ℂ)
    (γ : PiecewiseC1Path x x) {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_bd : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S
      (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ 0 := by
  refine hasCauchyPVOn_finset_pow_inv_of_avoids S k hk c γ
    ⟨δ, hδ_pos, hδ_bd⟩ ?_
  intro s hs
  have hδ_bd_extend : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ.toPath.extend t - s‖ := by
    intro t ht
    have := hδ_bd s hs t ht
    rwa [PiecewiseC1Path.extendedPath_eq] at this
  exact intervalIntegrable_pow_inv_mul_deriv_of_avoids γ s k hδ_pos
    hδ_bd_extend hLip

/-! ## CPV integrand norm bound -/

/-- **CPV integrand is dominated by the contour integrand.** Pointwise:
`‖cpvIntegrandOn S f γ ε t‖ ≤ ‖contourIntegrand f γ t‖`, since the CPV integrand
is either 0 or equal to the contour integrand. This is the pointwise step
toward dominated-convergence integrability arguments for `cpvIntegrandOn`. -/
theorem norm_cpvIntegrandOn_le_norm_contourIntegrand
    {y : ℂ} (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (ε : ℝ) (t : ℝ) :
    ‖cpvIntegrandOn S f γ.toPath.extend ε t‖ ≤
      ‖PiecewiseC1Path.contourIntegrand f γ t‖ := by
  simp only [cpvIntegrandOn, PiecewiseC1Path.contourIntegrand,
    PiecewiseC1Path.extendedPath_eq]
  split_ifs
  · rw [norm_zero]; exact norm_nonneg _
  · exact le_refl _

/-- **C-3 single-power avoidance, δ-free + Lipschitz form.** Same as
`hasCauchyPVOn_finset_pow_inv_of_avoids_lip` but with the positive margin
auto-derived from pointwise avoidance via `avoids_finset_delta_bound`. -/
theorem hasCauchyPVOn_finset_pow_inv_of_avoids_lip_avoids
    (S : Finset ℂ) (k : ℕ) (hk : 2 ≤ k) (c : ℂ → ℂ)
    (γ : PiecewiseC1Path x x)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S
      (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ 0 := by
  obtain ⟨δ, hδ_pos, hδ_bd⟩ := avoids_finset_delta_bound γ S hγ_avoids
  exact hasCauchyPVOn_finset_pow_inv_of_avoids_lip S k hk c γ hδ_pos hδ_bd hLip

end LeanModularForms

end
