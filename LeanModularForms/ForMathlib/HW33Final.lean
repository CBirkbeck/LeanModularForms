/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HW33Monotonicity
import LeanModularForms.ForMathlib.HW33Bridge

/-!
# HW Theorem 3.3 — eventual shape from monotonicity + avoidance margins

This file packages the shape-derivation chain into "eventually as ε → 0⁺"
form, ready for use with the bridge `hasCauchyPVOn_singleton_of_exitTime_excision`.

## Main results

* `shape_right_eventually`: combines `shape_right_of_strictMonoOn` with the
  natural eventual-quantifier form.

* `shape_left_eventually`: symmetric on the left.

These are the user-facing `∀ᶠ ε in 𝓝[>] 0, ...` forms expected by the bridge.
The transverse-data → strict mono step is in `HW33Monotonicity.lean`; combining
gives the full chain transverse-data → shape eventually.
-/

open Filter Topology Set Complex MeasureTheory

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-- **Eventual right-side shape from strict monotonicity + avoidance margin.** -/
theorem shape_right_eventually
    {γ : ℝ → ℂ} {s : ℂ} {t₀ δPlus : ℝ}
    (h_t₀_plus_le : t₀ + δPlus ≤ 1) (hδPlus : 0 < δPlus)
    (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δPlus)))
    (hγ_mono : StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + δPlus)))
    (h_s : γ t₀ = s)
    {δ_avoid : ℝ} (h_avoid_pos : 0 < δ_avoid)
    (h_avoid : ∀ t ∈ Icc (t₀ + δPlus) (1 : ℝ), δ_avoid ≤ ‖γ t - s‖) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      firstExitTimeRight γ t₀ δPlus s ε ≤ 1 ∧
      ∀ t ∈ Ioo (firstExitTimeRight γ t₀ δPlus s ε) (1 : ℝ),
        ε < ‖γ t - s‖ := by
  -- ‖γ(t₀+δPlus) - s‖ > 0 from avoidance margin
  have h_far_pos : 0 < ‖γ (t₀ + δPlus) - s‖ :=
    lt_of_lt_of_le h_avoid_pos
      (h_avoid (t₀ + δPlus) ⟨le_refl _, by linarith⟩)
  filter_upwards [Ioo_mem_nhdsGT (lt_min h_far_pos h_avoid_pos)] with ε hε
  have hε_pos : 0 < ε := hε.1
  have hε_lt_far : ε < ‖γ (t₀ + δPlus) - s‖ := lt_min_iff.mp hε.2 |>.1
  have hε_lt_avoid : ε < δ_avoid := lt_min_iff.mp hε.2 |>.2
  exact shape_right_of_strictMonoOn h_t₀_plus_le hδPlus hγ_cont
    hγ_mono h_avoid hε_lt_avoid (le_of_lt hε_lt_far)

/-- **Eventual left-side shape from strict anti-monotonicity + avoidance margin.** -/
theorem shape_left_eventually
    {γ : ℝ → ℂ} {s : ℂ} {t₀ δMinus : ℝ}
    (h_t₀_minus_pos : 0 ≤ t₀ - δMinus) (hδMinus : 0 < δMinus)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - δMinus) t₀))
    (hγ_anti : StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - δMinus) t₀))
    (h_s : γ t₀ = s)
    {δ_avoid : ℝ} (h_avoid_pos : 0 < δ_avoid)
    (h_avoid : ∀ t ∈ Icc (0 : ℝ) (t₀ - δMinus), δ_avoid ≤ ‖γ t - s‖) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ firstExitTimeLeft γ t₀ δMinus s ε ∧
      ∀ t ∈ Ioo (0 : ℝ) (firstExitTimeLeft γ t₀ δMinus s ε),
        ε < ‖γ t - s‖ := by
  have h_far_pos : 0 < ‖γ (t₀ - δMinus) - s‖ :=
    lt_of_lt_of_le h_avoid_pos
      (h_avoid (t₀ - δMinus) ⟨h_t₀_minus_pos, le_refl _⟩)
  filter_upwards [Ioo_mem_nhdsGT (lt_min h_far_pos h_avoid_pos)] with ε hε
  have hε_pos : 0 < ε := hε.1
  have hε_lt_far : ε < ‖γ (t₀ - δMinus) - s‖ := lt_min_iff.mp hε.2 |>.1
  have hε_lt_avoid : ε < δ_avoid := lt_min_iff.mp hε.2 |>.2
  exact shape_left_of_strictAntiOn h_t₀_minus_pos hδMinus hγ_cont
    hγ_anti h_avoid hε_lt_avoid (le_of_lt hε_lt_far)

/-- **Combined shape (left + right) eventually from strict monotonicity.**
Bundles `shape_left_eventually` and `shape_right_eventually` plus the trivial
`(α ε ≤ β ε)` inequality (always holds since both bracket `t₀`) into a single
`∀ᶠ ε` statement matching the hypothesis of
`hasCauchyPVOn_singleton_of_exitTime_excision`'s shape input.

The "‖γ - s‖ ≤ ε on Ioo α β" part holds automatically from the sSup/sInf
properties of the exit-time definitions (no monotonicity needed). -/
theorem shape_eventually_of_strict_mono
    {γ : ℝ → ℂ} {s : ℂ} {t₀ δMinus δPlus : ℝ}
    (h_t₀_minus_pos : 0 ≤ t₀ - δMinus) (h_t₀_plus_le : t₀ + δPlus ≤ 1)
    (hδMinus : 0 < δMinus) (hδPlus : 0 < δPlus)
    (hγ_cont_left : ContinuousOn γ (Icc (t₀ - δMinus) t₀))
    (hγ_cont_right : ContinuousOn γ (Icc t₀ (t₀ + δPlus)))
    (hγ_anti : StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - δMinus) t₀))
    (hγ_mono : StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + δPlus)))
    (h_s : γ t₀ = s)
    {δ_avoid_left δ_avoid_right : ℝ}
    (h_avoid_left_pos : 0 < δ_avoid_left)
    (h_avoid_right_pos : 0 < δ_avoid_right)
    (h_avoid_left : ∀ t ∈ Icc (0 : ℝ) (t₀ - δMinus), δ_avoid_left ≤ ‖γ t - s‖)
    (h_avoid_right : ∀ t ∈ Icc (t₀ + δPlus) (1 : ℝ), δ_avoid_right ≤ ‖γ t - s‖) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ firstExitTimeLeft γ t₀ δMinus s ε ∧
      firstExitTimeRight γ t₀ δPlus s ε ≤ 1 ∧
      firstExitTimeLeft γ t₀ δMinus s ε ≤
        firstExitTimeRight γ t₀ δPlus s ε ∧
      (∀ t ∈ Ioo (0 : ℝ) (firstExitTimeLeft γ t₀ δMinus s ε),
        ε < ‖γ t - s‖) ∧
      (∀ t ∈ Ioo (firstExitTimeRight γ t₀ δPlus s ε) (1 : ℝ),
        ε < ‖γ t - s‖) ∧
      (∀ t ∈ Ioo (firstExitTimeLeft γ t₀ δMinus s ε)
        (firstExitTimeRight γ t₀ δPlus s ε),
        ‖γ t - s‖ ≤ ε) := by
  have h_left := shape_left_eventually h_t₀_minus_pos hδMinus hγ_cont_left
    hγ_anti h_s h_avoid_left_pos h_avoid_left
  have h_right := shape_right_eventually h_t₀_plus_le hδPlus hγ_cont_right
    hγ_mono h_s h_avoid_right_pos h_avoid_right
  -- Need eventually for the "tLeft ≤ tRight" and "‖γ - s‖ ≤ ε on Ioo (tLeft, tRight)"
  -- Both follow directly from the definitions when ε is small enough.
  have h_far_left : 0 < ‖γ (t₀ - δMinus) - s‖ :=
    lt_of_lt_of_le h_avoid_left_pos
      (h_avoid_left (t₀ - δMinus) ⟨h_t₀_minus_pos, le_refl _⟩)
  have h_far_right : 0 < ‖γ (t₀ + δPlus) - s‖ :=
    lt_of_lt_of_le h_avoid_right_pos
      (h_avoid_right (t₀ + δPlus) ⟨le_refl _, by linarith⟩)
  have h_in_brackets : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      firstExitTimeLeft γ t₀ δMinus s ε ≤
        firstExitTimeRight γ t₀ δPlus s ε ∧
      ∀ t ∈ Ioo (firstExitTimeLeft γ t₀ δMinus s ε)
        (firstExitTimeRight γ t₀ δPlus s ε),
        ‖γ t - s‖ ≤ ε := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min h_far_left h_far_right)] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt_far_left : ε ≤ ‖γ (t₀ - δMinus) - s‖ :=
      le_of_lt (lt_min_iff.mp hε.2).1
    have hε_lt_far_right : ε ≤ ‖γ (t₀ + δPlus) - s‖ :=
      le_of_lt (lt_min_iff.mp hε.2).2
    -- firstExitTimeLeft ≤ t₀ ≤ firstExitTimeRight
    have h_tL_le_t₀ :=
      (firstExitTimeLeft_mem_Icc hδMinus.le hε_lt_far_left).2
    have h_t₀_le_tR :=
      (firstExitTimeRight_mem_Icc hδPlus.le hε_lt_far_right).1
    refine ⟨h_tL_le_t₀.trans h_t₀_le_tR, ?_⟩
    -- For t ∈ Ioo (firstExitTimeLeft, firstExitTimeRight):
    -- - If t ≤ t₀: t > firstExitTimeLeft, so by sSup, ‖γ t - s‖ < ε ≤ ε ✓
    -- - If t ≥ t₀: t < firstExitTimeRight, so by sInf, ‖γ t - s‖ < ε ✓
    -- - Combined: ‖γ t - s‖ ≤ ε
    intro t ht
    by_cases h_t_t₀ : t ≤ t₀
    · -- t ∈ (firstExitTimeLeft, t₀], use sSup property
      have ht_in_Icc : t ∈ Icc (t₀ - δMinus) t₀ := by
        refine ⟨?_, h_t_t₀⟩
        have : t₀ - δMinus ≤ firstExitTimeLeft γ t₀ δMinus s ε :=
          (firstExitTimeLeft_mem_Icc hδMinus.le hε_lt_far_left).1
        linarith [ht.1]
      have h_lt_ε : ‖γ t - s‖ < ε := by
        -- t > firstExitTimeLeft means t ∉ {t' ∈ [t₀-δ, t₀] | ε ≤ ‖γ t' - s‖}
        -- by sSup property
        by_contra h_ge
        push Not at h_ge
        -- Need: t ≤ sSup {t' | ε ≤ ‖γ t' - s‖}, contradicting t > firstExitTimeLeft
        have h_in_set : t ∈ {t' ∈ Set.Icc (t₀ - δMinus) t₀ | ε ≤ ‖γ t' - s‖} :=
          ⟨ht_in_Icc, h_ge⟩
        have h_le_sup : t ≤ firstExitTimeLeft γ t₀ δMinus s ε := by
          unfold firstExitTimeLeft
          apply le_csSup
          · exact ⟨t₀, firstExitTimeLeft_set_ub γ t₀ δMinus ε s⟩
          · exact h_in_set
        linarith [ht.1]
      linarith
    · -- t ∈ [t₀, firstExitTimeRight), use sInf property
      push Not at h_t_t₀
      have ht_in_Icc : t ∈ Icc t₀ (t₀ + δPlus) := by
        refine ⟨le_of_lt h_t_t₀, ?_⟩
        have : firstExitTimeRight γ t₀ δPlus s ε ≤ t₀ + δPlus :=
          (firstExitTimeRight_mem_Icc hδPlus.le hε_lt_far_right).2
        linarith [ht.2]
      have h_lt_ε : ‖γ t - s‖ < ε := by
        by_contra h_ge
        push Not at h_ge
        have h_in_set : t ∈ {t' ∈ Set.Icc t₀ (t₀ + δPlus) | ε ≤ ‖γ t' - s‖} :=
          ⟨ht_in_Icc, h_ge⟩
        have h_ge_inf : firstExitTimeRight γ t₀ δPlus s ε ≤ t := by
          unfold firstExitTimeRight
          apply csInf_le
          · exact ⟨t₀, firstExitTimeRight_set_lb γ t₀ δPlus ε s⟩
          · exact h_in_set
        linarith [ht.2]
      linarith
  filter_upwards [h_left, h_right, h_in_brackets] with ε hL hR hLR
  exact ⟨hL.1, hR.1, hLR.1, hL.2, hR.2, hLR.2⟩

end LeanModularForms

end
