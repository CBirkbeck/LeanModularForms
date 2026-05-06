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
    (_ : γ t₀ = s)
    {δ_avoid : ℝ} (h_avoid_pos : 0 < δ_avoid)
    (h_avoid : ∀ t ∈ Icc (t₀ + δPlus) (1 : ℝ), δ_avoid ≤ ‖γ t - s‖) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      firstExitTimeRight γ t₀ δPlus s ε ≤ 1 ∧
      ∀ t ∈ Ioo (firstExitTimeRight γ t₀ δPlus s ε) (1 : ℝ),
        ε < ‖γ t - s‖ := by
  have h := h_avoid_pos.trans_le (h_avoid (t₀ + δPlus) ⟨le_rfl, by linarith⟩)
  filter_upwards [Ioo_mem_nhdsGT (lt_min h h_avoid_pos)] with ε hε
  obtain ⟨h1, h2⟩ := lt_min_iff.mp hε.2
  exact shape_right_of_strictMonoOn h_t₀_plus_le hδPlus hγ_cont
    hγ_mono h_avoid h2 h1.le

/-- **Eventual left-side shape from strict anti-monotonicity + avoidance margin.** -/
theorem shape_left_eventually
    {γ : ℝ → ℂ} {s : ℂ} {t₀ δMinus : ℝ}
    (h_t₀_minus_pos : 0 ≤ t₀ - δMinus) (hδMinus : 0 < δMinus)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - δMinus) t₀))
    (hγ_anti : StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - δMinus) t₀))
    (_ : γ t₀ = s)
    {δ_avoid : ℝ} (h_avoid_pos : 0 < δ_avoid)
    (h_avoid : ∀ t ∈ Icc (0 : ℝ) (t₀ - δMinus), δ_avoid ≤ ‖γ t - s‖) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ firstExitTimeLeft γ t₀ δMinus s ε ∧
      ∀ t ∈ Ioo (0 : ℝ) (firstExitTimeLeft γ t₀ δMinus s ε),
        ε < ‖γ t - s‖ := by
  have h := h_avoid_pos.trans_le (h_avoid (t₀ - δMinus) ⟨h_t₀_minus_pos, le_rfl⟩)
  filter_upwards [Ioo_mem_nhdsGT (lt_min h h_avoid_pos)] with ε hε
  obtain ⟨h1, h2⟩ := lt_min_iff.mp hε.2
  exact shape_left_of_strictAntiOn h_t₀_minus_pos hδMinus hγ_cont
    hγ_anti h_avoid h2 h1.le

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
  have h_in_brackets : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      firstExitTimeLeft γ t₀ δMinus s ε ≤
        firstExitTimeRight γ t₀ δPlus s ε ∧
      ∀ t ∈ Ioo (firstExitTimeLeft γ t₀ δMinus s ε)
        (firstExitTimeRight γ t₀ δPlus s ε),
        ‖γ t - s‖ ≤ ε := by
    have hL := h_avoid_left_pos.trans_le
      (h_avoid_left (t₀ - δMinus) ⟨h_t₀_minus_pos, le_rfl⟩)
    have hR := h_avoid_right_pos.trans_le
      (h_avoid_right (t₀ + δPlus) ⟨le_rfl, by linarith⟩)
    filter_upwards [Ioo_mem_nhdsGT (lt_min hL hR)] with ε hε
    refine ⟨(firstExitTimeLeft_mem_Icc hδMinus.le ((lt_min_iff.mp hε.2).1.le)).2.trans
      (firstExitTimeRight_mem_Icc hδPlus.le ((lt_min_iff.mp hε.2).2.le)).1, ?_⟩
    intro t ht
    by_cases h_t_t₀ : t ≤ t₀
    · have ht_in_Icc : t ∈ Icc (t₀ - δMinus) t₀ := by
        refine ⟨?_, h_t_t₀⟩
        linarith [(firstExitTimeLeft_mem_Icc hδMinus.le ((lt_min_iff.mp hε.2).1.le)).1, ht.1]
      by_contra h_ge
      have h_in_set : t ∈ {t' ∈ Set.Icc (t₀ - δMinus) t₀ | ε ≤ ‖γ t' - s‖} :=
        ⟨ht_in_Icc, (not_le.mp h_ge).le⟩
      have h_le : t ≤ firstExitTimeLeft γ t₀ δMinus s ε :=
        le_csSup ⟨t₀, firstExitTimeLeft_set_ub γ t₀ δMinus ε s⟩ h_in_set
      linarith [ht.1]
    · have ht_in_Icc : t ∈ Icc t₀ (t₀ + δPlus) := by
        refine ⟨(not_le.mp h_t_t₀).le, ?_⟩
        linarith [(firstExitTimeRight_mem_Icc hδPlus.le ((lt_min_iff.mp hε.2).2.le)).2, ht.2]
      by_contra h_ge
      have h_in_set : t ∈ {t' ∈ Set.Icc t₀ (t₀ + δPlus) | ε ≤ ‖γ t' - s‖} :=
        ⟨ht_in_Icc, (not_le.mp h_ge).le⟩
      have h_le : firstExitTimeRight γ t₀ δPlus s ε ≤ t :=
        csInf_le ⟨t₀, firstExitTimeRight_set_lb γ t₀ δPlus ε s⟩ h_in_set
      linarith [ht.2]
  filter_upwards [h_left, h_right, h_in_brackets] with ε ⟨hL1, hL2⟩ ⟨hR1, hR2⟩ ⟨hLR1, hLR2⟩
  exact ⟨hL1, hR1, hLR1, hL2, hR2, hLR2⟩

/-! ## Full HW 3.3 closure for k-odd transverse case via `HasCauchyPVOn` -/

/-- **HW Theorem 3.3 — k-odd transverse case (single pole, `HasCauchyPVOn` form).**

For a closed Lipschitz `γ : PiecewiseC1Path x x` with a single transverse
crossing at `t₀ ∈ (0, 1)` of pole `s`, where `γ' (t₀) = L ≠ 0` from both sides,
γ is flat of order `n ≥ k` (with `k` odd), strict (anti-)monotonicity of
`‖γ - s‖` near `t₀`, and avoidance margins / integrability outside, the CPV
along γ vanishes:

  `HasCauchyPVOn {s} (fun z => 1 / (z - s)^k) γ 0`.

This is the **fully assembled HW 3.3 closure for the k-odd transverse case**
in the `HasCauchyPVOn` form, composing:

* `hw_theorem_3_3_odd_transverse_concrete` (parametric symmetric-excision PV)
* `shape_eventually_of_strict_mono` (shape hypothesis)
* `hasCauchyPVOn_singleton_of_exitTime_excision` (bridge to `HasCauchyPVOn`).

All lower-level machinery (exit times, strict mono from transverse, integral
splitting under shape) closes cleanly with no new sorries.

The strict (anti-)monotonicity hypotheses can be derived from the more basic
transverse data via `exists_strictMonoOn_norm_right_of_transverse` and
`exists_strictAntiOn_norm_left_of_transverse` from `HW33Monotonicity.lean`. -/
theorem hasCauchyPVOn_singleton_pow_of_transverse_assembled
    {γ : PiecewiseC1Path x x} {s L : ℂ}
    {t₀ δMinus δPlus : ℝ} {n k : ℕ}
    (h_t₀_minus_pos : 0 ≤ t₀ - δMinus) (h_t₀_plus_le : t₀ + δPlus ≤ 1)
    (hδMinus : 0 < δMinus) (hδPlus : 0 < δPlus)
    (h_close : γ.toPath.extend 0 = γ.toPath.extend 1)
    (h_flat : IsFlatOfOrder γ.toPath.extend t₀ n) (hL : L ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ.toPath.extend L (Set.Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ.toPath.extend L (Set.Iio t₀) t₀)
    (hL_right : Tendsto (deriv γ.toPath.extend) (𝓝[>] t₀) (𝓝 L))
    (hL_left : Tendsto (deriv γ.toPath.extend) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ.toPath.extend t₀ = s)
    (hk : 2 ≤ k) (hk_odd : Odd k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (hγ_cont_right : ContinuousOn γ.toPath.extend (Set.Icc t₀ (t₀ + δPlus)))
    (hγ_cont_left : ContinuousOn γ.toPath.extend (Set.Icc (t₀ - δMinus) t₀))
    (h_leave_right : ∀ t ∈ Set.Ioc t₀ (t₀ + δPlus), γ.toPath.extend t ≠ s)
    (h_leave_left : ∀ t ∈ Set.Ico (t₀ - δMinus) t₀, γ.toPath.extend t ≠ s)
    (hγ_anti : StrictAntiOn (fun t => ‖γ.toPath.extend t - s‖)
      (Set.Icc (t₀ - δMinus) t₀))
    (hγ_mono : StrictMonoOn (fun t => ‖γ.toPath.extend t - s‖)
      (Set.Icc t₀ (t₀ + δPlus)))
    {δ_avoid_left δ_avoid_right : ℝ}
    (h_avoid_left_pos : 0 < δ_avoid_left)
    (h_avoid_right_pos : 0 < δ_avoid_right)
    (h_avoid_left : ∀ t ∈ Set.Icc (0 : ℝ) (t₀ - δMinus),
      δ_avoid_left ≤ ‖γ.toPath.extend t - s‖)
    (h_avoid_right : ∀ t ∈ Set.Icc (t₀ + δPlus) (1 : ℝ),
      δ_avoid_right ≤ ‖γ.toPath.extend t - s‖)
    (h_minus_smooth : ∀ ε > 0,
      ∀ t ∈ Set.uIcc (0 : ℝ)
        (firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε),
      HasDerivAt γ.toPath.extend (deriv γ.toPath.extend t) t)
    (h_minus_avoids : ∀ ε > 0,
      ∀ t ∈ Set.uIcc (0 : ℝ)
        (firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε),
      γ.toPath.extend t ≠ s)
    (h_minus_int : ∀ ε > 0,
      IntervalIntegrable
        (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - s) ^ k)
        MeasureTheory.volume 0
        (firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε))
    (h_plus_smooth : ∀ ε > 0,
      ∀ t ∈ Set.uIcc
        (firstExitTimeRight γ.toPath.extend t₀ δPlus s ε) (1 : ℝ),
      HasDerivAt γ.toPath.extend (deriv γ.toPath.extend t) t)
    (h_plus_avoids : ∀ ε > 0,
      ∀ t ∈ Set.uIcc
        (firstExitTimeRight γ.toPath.extend t₀ δPlus s ε) (1 : ℝ),
      γ.toPath.extend t ≠ s)
    (h_plus_int : ∀ ε > 0,
      IntervalIntegrable
        (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - s) ^ k)
        MeasureTheory.volume
        (firstExitTimeRight γ.toPath.extend t₀ δPlus s ε) (1 : ℝ))
    (h_int_full : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => cpvIntegrandOn {s}
        (fun z => (1 : ℂ) / (z - s) ^ k) γ.toPath.extend ε t)
      MeasureTheory.volume 0 1) :
    HasCauchyPVOn {s} (fun z => (1 : ℂ) / (z - s) ^ k) γ 0 := by
  exact hasCauchyPVOn_singleton_of_exitTime_excision γ s
    (fun z => (1 : ℂ) / (z - s) ^ k)
    (shape_eventually_of_strict_mono h_t₀_minus_pos h_t₀_plus_le hδMinus hδPlus
      hγ_cont_left hγ_cont_right hγ_anti hγ_mono h_s
      h_avoid_left_pos h_avoid_right_pos h_avoid_left h_avoid_right) h_int_full
    ((hw_theorem_3_3_odd_transverse_concrete (γ := γ.toPath.extend)
      (γ' := deriv γ.toPath.extend) (s := s) (L := L) (n := n) (k := k)
      (a := 0) (b := 1) (t₀ := t₀) (δMinus := δMinus) (δPlus := δPlus)
      hδPlus hδMinus h_close h_flat hL h_deriv_right h_deriv_left
      hL_right hL_left h_s hk hk_odd hkn hn1
      hγ_cont_right hγ_cont_left h_leave_right h_leave_left
      h_minus_smooth h_minus_avoids h_minus_int
      h_plus_smooth h_plus_avoids h_plus_int).congr fun ε => by
        congr 1 <;> exact intervalIntegral.integral_congr fun t _ => by ring)

end LeanModularForms

end
