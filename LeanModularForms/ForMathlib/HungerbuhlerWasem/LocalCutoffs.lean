/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CPVExistenceMulti

/-!
# Localized exit-time cutoffs for multi-crossing CPV existence (T-BR-Y6c)

This file adapts the exit-time cutoff infrastructure in
`CrossingDataBuilder.lean` from **global** uniqueness on `Icc 0 1` to
**local** uniqueness on a window `Icc (t₀ - r) (t₀ + r)`. This is the
infrastructure required by the multi-crossing CPV discharge programme:
each crossing parameter `t_i ∈ M.crossings` is equipped with its own
local cutoffs `δ_left^i, δ_right^i : ℝ → ℝ`, threshold `θ_i`, and
asymmetric far/near bounds. These per-crossing bundles, when combined,
discharge the `h_multi_cpv` oracle in
`residueTheorem_crossing_asymmetric_multiPole`.

## Setup

Throughout this file we fix a closed piecewise-`C¹` immersion `γ` (with
range avoidance `x : ℂ`), a pole `s : ℂ`, and a crossing parameter
`t₀ : ℝ`. The local window is `Icc (t₀ - r) (t₀ + r)` for some `r > 0`
with `Icc (t₀ - r) (t₀ + r) ⊆ Icc 0 1`. We assume:
* `h_at` — `γ(t₀) = s`;
* `h_off` — `t₀` is off the legacy partition;
* `h_local_unique` — `t₀` is the unique crossing on the window.

These local-uniqueness assumptions come from `multi_pole_local_uniqueness`
in `CPVExistenceMulti.lean` (applied with the common radius `r` from
`multi_pole_common_radius`).

## Main results

* `exists_right_cutoff_local` — right exit-time cutoff `δ_right : ℝ → ℝ`
  with threshold above which `δ_right(ε) < r` and the far-bound holds on
  `(t₀ + δ_right(ε), t₀ + r]`.
* `exists_left_cutoff_local` — symmetric on the left.
* `LocalDerivedCutoffs` — bundle structure containing both cutoffs and
  all asymmetric far/near bounds.
* `localDerivedCutoffs` — noncomputable builder from local geometric data.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2 §3.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

/-! ### IVT exit-time inversion helper (local copy)

The same exit-time inversion lemma as in `CrossingDataBuilder.lean`,
restated here for use inside this file. Given a strictly monotone
continuous `f` on `[0, r]` with `f 0 = 0`, every `ε ∈ (0, f r)` has a
unique preimage `τ ∈ (0, r)`. -/

private theorem strict_mono_inverse_exists_local
    (f : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (hf₀ : f 0 = 0)
    (hf_strict : StrictMonoOn f (Set.Icc 0 r))
    (hf_cont : ContinuousOn f (Set.Icc 0 r)) :
    ∀ ε ∈ Set.Ioo (0 : ℝ) (f r),
      ∃! τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) r ∧ f τ = ε := by
  intro ε hε
  have h_image : Set.Ioo (f 0) (f r) ⊆ f '' Set.Ioo 0 r :=
    intermediate_value_Ioo hr.le hf_cont
  have hε_in : ε ∈ Set.Ioo (f 0) (f r) := by
    rw [hf₀]; exact hε
  obtain ⟨τ, hτ_mem, hfτ⟩ := h_image hε_in
  refine ⟨τ, ⟨hτ_mem, hfτ⟩, ?_⟩
  rintro τ' ⟨hτ'_mem, hfτ'⟩
  exact hf_strict.injOn (Set.Ioo_subset_Icc_self hτ'_mem)
    (Set.Ioo_subset_Icc_self hτ_mem) (hfτ'.trans hfτ.symm)

/-! ### Localized right cutoff

The right cutoff function `δ_right : ℝ → ℝ` with threshold, derived from
local strict-monotonicity of `‖γ(t) - s‖` on a right neighborhood of `t₀`
and local uniqueness on the window. -/

/-- **Localized right cutoff existence (corner-friendly).** Given a closed
pw-`C¹` immersion `γ` crossing `s` at an **interior** parameter `t₀`
(smooth OR corner — no off-partition assumption), with local uniqueness on
the window `[t₀ - r, t₀ + r] ⊆ [0, 1]`, produce a right cutoff
`δ_right : ℝ → ℝ` and threshold satisfying the asymmetric far/near bounds. -/
private theorem exists_right_cutoff_local
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ r : ℝ}
    (h_window_pos : 0 < r)
    (h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∃ (δ_right : ℝ → ℝ) (threshold : ℝ),
      0 < threshold ∧
      (∀ ε, 0 < ε → ε < threshold → 0 < δ_right ε) ∧
      (∀ ε, 0 < ε → ε < threshold → δ_right ε < r) ∧
      (∀ ε, 0 < ε → ε < threshold →
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + δ_right ε) - s‖ = ε) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ t,
        t₀ + δ_right ε < t → t ≤ t₀ + r →
        ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ t,
        t₀ ≤ t → t - t₀ ≤ δ_right ε →
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε) := by
  classical
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
    with hγf_def
  -- Step 1: t₀ ∈ Ioo 0 1 from window membership.
  have h_t₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1 := by
    have h_t₀_in : t₀ ∈ Set.Icc (t₀ - r) (t₀ + r) :=
      ⟨by linarith, by linarith⟩
    have h_t₀_in_01 := h_window_Icc h_t₀_in
    have h_t₀_minus_in : (t₀ - r) ∈ Set.Icc (t₀ - r) (t₀ + r) :=
      ⟨le_rfl, by linarith⟩
    have h_t₀_plus_in : (t₀ + r) ∈ Set.Icc (t₀ - r) (t₀ + r) :=
      ⟨by linarith, le_rfl⟩
    have h_minus_in_01 := h_window_Icc h_t₀_minus_in
    have h_plus_in_01 := h_window_Icc h_t₀_plus_in
    refine ⟨?_, ?_⟩
    · linarith [h_minus_in_01.1, h_window_pos]
    · linarith [h_plus_in_01.2, h_window_pos]
  -- Step 2: Strict monotonicity on a right neighborhood of t₀.
  obtain ⟨L, hL_ne, hL_right⟩ := exists_right_deriv_limit γ h_t₀_Ioo
  have hγf_cont : ContinuousAt γf t₀ :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousAt
  have hγf_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γf t :=
    eventually_differentiable_right γ h_t₀_Ioo
  obtain ⟨r₀, hr₀_pos, hmono⟩ :=
    norm_sub_strictMonoOn_right h_at hL_ne hL_right hγf_cont hγf_diff
  -- Step 3: Define internal effective radius for the strict-mono part.
  -- r_eff_mono = min(r₀, r/2): strict mono on [t₀, t₀ + r_eff_mono].
  set r_eff_mono : ℝ := min r₀ (r / 2) with hr_eff_def
  have hr_eff_pos : 0 < r_eff_mono := by
    rw [hr_eff_def]
    exact lt_min hr₀_pos (by linarith)
  have hr_eff_le_r₀ : r_eff_mono ≤ r₀ := by
    rw [hr_eff_def]; exact min_le_left _ _
  have hr_eff_le_r_half : r_eff_mono ≤ r / 2 := by
    rw [hr_eff_def]; exact min_le_right _ _
  have hr_eff_lt_r : r_eff_mono < r := by linarith
  -- Strict mono on [t₀, t₀ + r_eff_mono].
  have hmono_r : StrictMonoOn (fun t => ‖γf t - s‖) (Set.Icc t₀ (t₀ + r_eff_mono)) :=
    hmono.mono (Set.Icc_subset_Icc le_rfl (by linarith))
  -- Step 4: Define f(τ) := ‖γf(t₀ + τ) - s‖ on [0, r_eff_mono].
  set f : ℝ → ℝ := fun τ => ‖γf (t₀ + τ) - s‖ with hf_def
  have hf₀ : f 0 = 0 := by
    show ‖γf (t₀ + 0) - s‖ = 0
    rw [add_zero]
    have heq : γf t₀ = s := h_at
    rw [heq, sub_self, norm_zero]
  have hγ_cont_all : Continuous γf := by
    show Continuous (fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t)
    exact γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  have hf_cont : ContinuousOn f (Set.Icc 0 r_eff_mono) := by
    have h_total : Continuous f := by
      show Continuous (fun τ => ‖γf (t₀ + τ) - s‖)
      exact ((hγ_cont_all.comp (continuous_const.add continuous_id)).sub
        continuous_const).norm
    exact h_total.continuousOn
  have hf_strict : StrictMonoOn f (Set.Icc 0 r_eff_mono) := by
    intro a ha b hb hab
    have h_eq : f a = (fun t => ‖γf t - s‖) (t₀ + a) := rfl
    have h_eq' : f b = (fun t => ‖γf t - s‖) (t₀ + b) := rfl
    rw [h_eq, h_eq']
    exact hmono_r ⟨by linarith [ha.1], by linarith [ha.2]⟩
      ⟨by linarith [hb.1], by linarith [hb.2]⟩ (by linarith)
  have hf_r_pos : 0 < f r_eff_mono := by
    rw [show (0 : ℝ) = f 0 from hf₀.symm]
    apply hf_strict (Set.left_mem_Icc.mpr hr_eff_pos.le)
      (Set.right_mem_Icc.mpr hr_eff_pos.le)
    exact hr_eff_pos
  -- Step 5: Far bound on [t₀ + r_eff_mono, t₀ + r] from multi_pole_local_far_bound.
  obtain ⟨m, hm_pos, _h_far_left, h_far_right⟩ :=
    multi_pole_local_far_bound γ h_window_pos h_local_unique hr_eff_pos
      hr_eff_lt_r.le
  -- Step 6: Threshold and δ_right definition.
  set threshold : ℝ := min (f r_eff_mono) m with hthresh_def
  have hthresh_pos : 0 < threshold := lt_min hf_r_pos hm_pos
  have hthresh_le_fr : threshold ≤ f r_eff_mono := by
    rw [hthresh_def]; exact min_le_left _ _
  have hthresh_le_m : threshold ≤ m := by
    rw [hthresh_def]; exact min_le_right _ _
  set δ_right : ℝ → ℝ := fun ε =>
    if h : ε ∈ Set.Ioo (0 : ℝ) (f r_eff_mono) then
      (strict_mono_inverse_exists_local f hr_eff_pos hf₀ hf_strict hf_cont ε h).choose
    else r_eff_mono / 2 with hδ_def
  have hδ_spec : ∀ ε, 0 < ε → ε < f r_eff_mono →
      δ_right ε ∈ Set.Ioo (0 : ℝ) r_eff_mono ∧ f (δ_right ε) = ε := by
    intro ε hε_pos hε_lt
    have hε_in : ε ∈ Set.Ioo (0 : ℝ) (f r_eff_mono) := ⟨hε_pos, hε_lt⟩
    simp only [hδ_def, dif_pos hε_in]
    exact
      (strict_mono_inverse_exists_local f hr_eff_pos hf₀ hf_strict hf_cont ε hε_in).choose_spec.1
  refine ⟨δ_right, threshold, hthresh_pos, ?_, ?_, ?_, ?_, ?_⟩
  · -- δ_right ε > 0
    intro ε hε_pos hε_lt
    exact (hδ_spec ε hε_pos (lt_of_lt_of_le hε_lt hthresh_le_fr)).1.1
  · -- δ_right ε < r
    intro ε hε_pos hε_lt
    have h_in_Ioo := (hδ_spec ε hε_pos (lt_of_lt_of_le hε_lt hthresh_le_fr)).1
    linarith [h_in_Ioo.2]
  · -- ‖γ(t₀ + δ_right ε) - s‖ = ε
    intro ε hε_pos hε_lt
    have ⟨_, hfδ⟩ := hδ_spec ε hε_pos (lt_of_lt_of_le hε_lt hthresh_le_fr)
    exact hfδ
  · -- Far bound: ε < ‖γf t - s‖ for t ∈ (t₀ + δ_right ε, t₀ + r]
    intro ε hε_pos hε_lt t ht_gt ht_le
    have hε_lt_fr : ε < f r_eff_mono := lt_of_lt_of_le hε_lt hthresh_le_fr
    obtain ⟨hδ_in, hfδ⟩ := hδ_spec ε hε_pos hε_lt_fr
    by_cases ht_le_eff : t ≤ t₀ + r_eff_mono
    · -- t ∈ (t₀ + δ_right ε, t₀ + r_eff_mono]: use strict mono.
      have ht_τ_mem : t - t₀ ∈ Set.Icc (0 : ℝ) r_eff_mono :=
        ⟨by linarith [hδ_in.1], by linarith⟩
      have hδ_τ_mem : δ_right ε ∈ Set.Icc (0 : ℝ) r_eff_mono :=
        ⟨le_of_lt hδ_in.1, le_of_lt hδ_in.2⟩
      have h_lt : f (δ_right ε) < f (t - t₀) :=
        hf_strict hδ_τ_mem ht_τ_mem (by linarith)
      rw [hfδ] at h_lt
      have h_eq : f (t - t₀) = ‖γf t - s‖ := by
        show ‖γf (t₀ + (t - t₀)) - s‖ = ‖γf t - s‖
        rw [show t₀ + (t - t₀) = t from by ring]
      rwa [h_eq] at h_lt
    · -- t > t₀ + r_eff_mono: use the local far bound on [t₀ + r_eff_mono, t₀ + r].
      push Not at ht_le_eff
      have hε_lt_m : ε < m := lt_of_lt_of_le hε_lt hthresh_le_m
      have h_ge_m : m ≤ ‖γf t - s‖ :=
        h_far_right t ⟨le_of_lt ht_le_eff, ht_le⟩
      linarith
  · -- Near bound: ‖γf t - s‖ ≤ ε for t ∈ [t₀, t₀ + δ_right ε]
    intro ε hε_pos hε_lt t ht_ge hgap
    have hε_lt_fr : ε < f r_eff_mono := lt_of_lt_of_le hε_lt hthresh_le_fr
    obtain ⟨hδ_in, hfδ⟩ := hδ_spec ε hε_pos hε_lt_fr
    have ht_τ_mem : t - t₀ ∈ Set.Icc (0 : ℝ) r_eff_mono := by
      refine ⟨by linarith, ?_⟩
      linarith [hδ_in.2]
    have hδ_τ_mem : δ_right ε ∈ Set.Icc (0 : ℝ) r_eff_mono :=
      ⟨le_of_lt hδ_in.1, le_of_lt hδ_in.2⟩
    by_cases h_t_eq : t = t₀
    · rw [h_t_eq, h_at, sub_self, norm_zero]
      exact le_of_lt hε_pos
    · have ht_τ_pos : (0 : ℝ) < t - t₀ := by
        rcases lt_or_eq_of_le ht_ge with h | h
        · linarith
        · exact absurd h.symm h_t_eq
      have h_le : f (t - t₀) ≤ f (δ_right ε) := by
        rcases lt_or_eq_of_le hgap with h_lt | h_eq
        · exact le_of_lt (hf_strict ht_τ_mem hδ_τ_mem h_lt)
        · have : t - t₀ = δ_right ε := h_eq
          rw [this]
      rw [hfδ] at h_le
      have h_eq : f (t - t₀) = ‖γf t - s‖ := by
        show ‖γf (t₀ + (t - t₀)) - s‖ = ‖γf t - s‖
        rw [show t₀ + (t - t₀) = t from by ring]
      rwa [h_eq] at h_le

/-! ### Localized left cutoff

Symmetric to `exists_right_cutoff_local`. -/

/-- **Localized left cutoff existence (corner-friendly).** Symmetric
counterpart of `exists_right_cutoff_local`. -/
private theorem exists_left_cutoff_local
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ r : ℝ}
    (h_window_pos : 0 < r)
    (h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∃ (δ_left : ℝ → ℝ) (threshold : ℝ),
      0 < threshold ∧
      (∀ ε, 0 < ε → ε < threshold → 0 < δ_left ε) ∧
      (∀ ε, 0 < ε → ε < threshold → δ_left ε < r) ∧
      (∀ ε, 0 < ε → ε < threshold →
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - δ_left ε) - s‖ = ε) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ t,
        t₀ - r ≤ t → t < t₀ - δ_left ε →
        ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ t,
        t₀ - δ_left ε ≤ t → t ≤ t₀ →
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε) := by
  classical
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
    with hγf_def
  -- Step 1: t₀ ∈ Ioo 0 1 from window membership.
  have h_t₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1 := by
    have h_t₀_minus_in : (t₀ - r) ∈ Set.Icc (t₀ - r) (t₀ + r) :=
      ⟨le_rfl, by linarith⟩
    have h_t₀_plus_in : (t₀ + r) ∈ Set.Icc (t₀ - r) (t₀ + r) :=
      ⟨by linarith, le_rfl⟩
    have h_minus_in_01 := h_window_Icc h_t₀_minus_in
    have h_plus_in_01 := h_window_Icc h_t₀_plus_in
    refine ⟨?_, ?_⟩
    · linarith [h_minus_in_01.1, h_window_pos]
    · linarith [h_plus_in_01.2, h_window_pos]
  -- Step 2: Strict anti-monotonicity on a left neighborhood of t₀.
  obtain ⟨L, hL_ne, hL_left⟩ := exists_left_deriv_limit γ h_t₀_Ioo
  have hγf_cont : ContinuousAt γf t₀ :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousAt
  have hγf_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γf t :=
    eventually_differentiable_left γ h_t₀_Ioo
  obtain ⟨r₀, hr₀_pos, hanti⟩ :=
    norm_sub_strictAntiOn_left h_at hL_ne hL_left hγf_cont hγf_diff
  -- Step 3: Effective radius for strict-mono part.
  set r_eff_mono : ℝ := min r₀ (r / 2) with hr_eff_def
  have hr_eff_pos : 0 < r_eff_mono := by
    rw [hr_eff_def]
    exact lt_min hr₀_pos (by linarith)
  have hr_eff_le_r₀ : r_eff_mono ≤ r₀ := by
    rw [hr_eff_def]; exact min_le_left _ _
  have hr_eff_le_r_half : r_eff_mono ≤ r / 2 := by
    rw [hr_eff_def]; exact min_le_right _ _
  have hr_eff_lt_r : r_eff_mono < r := by linarith
  -- Anti-mono on [t₀ - r_eff_mono, t₀].
  have hanti_r : StrictAntiOn (fun t => ‖γf t - s‖) (Set.Icc (t₀ - r_eff_mono) t₀) :=
    hanti.mono (Set.Icc_subset_Icc (by linarith) le_rfl)
  -- Step 4: Define f(τ) := ‖γf(t₀ - τ) - s‖ on [0, r_eff_mono] — strictly increasing.
  set f : ℝ → ℝ := fun τ => ‖γf (t₀ - τ) - s‖ with hf_def
  have hf₀ : f 0 = 0 := by
    show ‖γf (t₀ - 0) - s‖ = 0
    rw [sub_zero]
    have heq : γf t₀ = s := h_at
    rw [heq, sub_self, norm_zero]
  have hγ_cont_all : Continuous γf := by
    show Continuous (fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t)
    exact γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  have hf_cont : ContinuousOn f (Set.Icc 0 r_eff_mono) := by
    have h_total : Continuous f := by
      show Continuous (fun τ => ‖γf (t₀ - τ) - s‖)
      exact ((hγ_cont_all.comp (continuous_const.sub continuous_id)).sub
        continuous_const).norm
    exact h_total.continuousOn
  have hf_strict : StrictMonoOn f (Set.Icc 0 r_eff_mono) := by
    intro a ha b hb hab
    have h_ge : t₀ - b ∈ Set.Icc (t₀ - r_eff_mono) t₀ :=
      ⟨by linarith [hb.2], by linarith [hb.1]⟩
    have h_le : t₀ - a ∈ Set.Icc (t₀ - r_eff_mono) t₀ :=
      ⟨by linarith [ha.2], by linarith [ha.1]⟩
    have h_lt : t₀ - b < t₀ - a := by linarith
    exact hanti_r h_ge h_le h_lt
  have hf_r_pos : 0 < f r_eff_mono := by
    rw [show (0 : ℝ) = f 0 from hf₀.symm]
    apply hf_strict (Set.left_mem_Icc.mpr hr_eff_pos.le)
      (Set.right_mem_Icc.mpr hr_eff_pos.le)
    exact hr_eff_pos
  -- Step 5: Far bound on [t₀ - r, t₀ - r_eff_mono] from multi_pole_local_far_bound.
  obtain ⟨m, hm_pos, h_far_left, _h_far_right⟩ :=
    multi_pole_local_far_bound γ h_window_pos h_local_unique hr_eff_pos
      hr_eff_lt_r.le
  -- Step 6: Threshold and δ_left definition.
  set threshold : ℝ := min (f r_eff_mono) m with hthresh_def
  have hthresh_pos : 0 < threshold := lt_min hf_r_pos hm_pos
  have hthresh_le_fr : threshold ≤ f r_eff_mono := by
    rw [hthresh_def]; exact min_le_left _ _
  have hthresh_le_m : threshold ≤ m := by
    rw [hthresh_def]; exact min_le_right _ _
  set δ_left : ℝ → ℝ := fun ε =>
    if h : ε ∈ Set.Ioo (0 : ℝ) (f r_eff_mono) then
      (strict_mono_inverse_exists_local f hr_eff_pos hf₀ hf_strict hf_cont ε h).choose
    else r_eff_mono / 2 with hδ_def
  have hδ_spec : ∀ ε, 0 < ε → ε < f r_eff_mono →
      δ_left ε ∈ Set.Ioo (0 : ℝ) r_eff_mono ∧ f (δ_left ε) = ε := by
    intro ε hε_pos hε_lt
    have hε_in : ε ∈ Set.Ioo (0 : ℝ) (f r_eff_mono) := ⟨hε_pos, hε_lt⟩
    simp only [hδ_def, dif_pos hε_in]
    exact
      (strict_mono_inverse_exists_local f hr_eff_pos hf₀ hf_strict hf_cont ε hε_in).choose_spec.1
  refine ⟨δ_left, threshold, hthresh_pos, ?_, ?_, ?_, ?_, ?_⟩
  · intro ε hε_pos hε_lt
    exact (hδ_spec ε hε_pos (lt_of_lt_of_le hε_lt hthresh_le_fr)).1.1
  · intro ε hε_pos hε_lt
    have h_in_Ioo := (hδ_spec ε hε_pos (lt_of_lt_of_le hε_lt hthresh_le_fr)).1
    linarith [h_in_Ioo.2]
  · -- ‖γ(t₀ - δ_left ε) - s‖ = ε
    intro ε hε_pos hε_lt
    have ⟨_, hfδ⟩ := hδ_spec ε hε_pos (lt_of_lt_of_le hε_lt hthresh_le_fr)
    exact hfδ
  · -- Far bound: ε < ‖γf t - s‖ for t ∈ [t₀ - r, t₀ - δ_left ε)
    intro ε hε_pos hε_lt t ht_ge ht_lt
    have hε_lt_fr : ε < f r_eff_mono := lt_of_lt_of_le hε_lt hthresh_le_fr
    obtain ⟨hδ_in, hfδ⟩ := hδ_spec ε hε_pos hε_lt_fr
    by_cases ht_ge_eff : t₀ - r_eff_mono ≤ t
    · -- t ∈ [t₀ - r_eff_mono, t₀ - δ_left ε): use strict mono.
      have ht_τ_mem : t₀ - t ∈ Set.Icc (0 : ℝ) r_eff_mono :=
        ⟨by linarith [hδ_in.1], by linarith⟩
      have hδ_τ_mem : δ_left ε ∈ Set.Icc (0 : ℝ) r_eff_mono :=
        ⟨le_of_lt hδ_in.1, le_of_lt hδ_in.2⟩
      have h_lt : f (δ_left ε) < f (t₀ - t) :=
        hf_strict hδ_τ_mem ht_τ_mem (by linarith)
      rw [hfδ] at h_lt
      have h_eq : f (t₀ - t) = ‖γf t - s‖ := by
        show ‖γf (t₀ - (t₀ - t)) - s‖ = ‖γf t - s‖
        rw [show t₀ - (t₀ - t) = t from by ring]
      rwa [h_eq] at h_lt
    · -- t < t₀ - r_eff_mono: use the local far bound on [t₀ - r, t₀ - r_eff_mono].
      push Not at ht_ge_eff
      have hε_lt_m : ε < m := lt_of_lt_of_le hε_lt hthresh_le_m
      have h_ge_m : m ≤ ‖γf t - s‖ :=
        h_far_left t ⟨ht_ge, le_of_lt ht_ge_eff⟩
      linarith
  · -- Near bound: ‖γf t - s‖ ≤ ε for t ∈ [t₀ - δ_left ε, t₀]
    intro ε hε_pos hε_lt t ht_ge ht_le
    have hε_lt_fr : ε < f r_eff_mono := lt_of_lt_of_le hε_lt hthresh_le_fr
    obtain ⟨hδ_in, hfδ⟩ := hδ_spec ε hε_pos hε_lt_fr
    have ht_τ_mem : t₀ - t ∈ Set.Icc (0 : ℝ) r_eff_mono := by
      refine ⟨by linarith, ?_⟩
      linarith [hδ_in.2]
    have hδ_τ_mem : δ_left ε ∈ Set.Icc (0 : ℝ) r_eff_mono :=
      ⟨le_of_lt hδ_in.1, le_of_lt hδ_in.2⟩
    by_cases h_t_eq : t = t₀
    · rw [h_t_eq, h_at, sub_self, norm_zero]
      exact le_of_lt hε_pos
    · have ht_τ_pos : (0 : ℝ) < t₀ - t := by
        rcases lt_or_eq_of_le ht_le with h | h
        · linarith
        · exact absurd h h_t_eq
      have h_le : f (t₀ - t) ≤ f (δ_left ε) := by
        rcases lt_or_eq_of_le ht_ge with h_lt | h_eq
        · -- t₀ - δ_left ε < t  →  t₀ - t < δ_left ε
          exact le_of_lt (hf_strict ht_τ_mem hδ_τ_mem (by linarith))
        · -- t = t₀ - δ_left ε  →  t₀ - t = δ_left ε
          have : t₀ - t = δ_left ε := by linarith [h_eq]
          rw [this]
      rw [hfδ] at h_le
      have h_eq : f (t₀ - t) = ‖γf t - s‖ := by
        show ‖γf (t₀ - (t₀ - t)) - s‖ = ‖γf t - s‖
        rw [show t₀ - (t₀ - t) = t from by ring]
      rwa [h_eq] at h_le

/-! ### Per-crossing local cutoff bundle

The `LocalDerivedCutoffs` structure packages both `δ_left` and `δ_right`
together with all asymmetric far/near bounds on the window
`[t₀ - r, t₀ + r]`. -/

/-- **Per-crossing local cutoffs** for a multi-crossing scenario. Each
crossing parameter `t₀` is equipped with its own asymmetric cutoffs
`δ_left, δ_right : ℝ → ℝ`, threshold, and far/near bounds on the local
window `[t₀ - r, t₀ + r]`. -/
structure LocalDerivedCutoffs (γ : ClosedPwC1Immersion x) (s : ℂ) (t₀ r : ℝ) where
  /-- Left cutoff function. -/
  δ_left : ℝ → ℝ
  /-- Right cutoff function. -/
  δ_right : ℝ → ℝ
  /-- Threshold below which all bounds hold. -/
  threshold : ℝ
  hthresh : 0 < threshold
  hδ_left_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_left ε
  hδ_right_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_right ε
  hδ_left_lt : ∀ ε, 0 < ε → ε < threshold → δ_left ε < r
  hδ_right_lt : ∀ ε, 0 < ε → ε < threshold → δ_right ε < r
  h_exit_left : ∀ ε, 0 < ε → ε < threshold →
    ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - δ_left ε) - s‖ = ε
  h_exit_right : ∀ ε, 0 < ε → ε < threshold →
    ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + δ_right ε) - s‖ = ε
  h_far_left : ∀ ε, 0 < ε → ε < threshold → ∀ t,
    t₀ - r ≤ t → t < t₀ - δ_left ε →
    ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖
  h_far_right : ∀ ε, 0 < ε → ε < threshold → ∀ t,
    t₀ + δ_right ε < t → t ≤ t₀ + r →
    ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖
  h_near_left : ∀ ε, 0 < ε → ε < threshold → ∀ t,
    t₀ - δ_left ε ≤ t → t ≤ t₀ →
    ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε
  h_near_right : ∀ ε, 0 < ε → ε < threshold → ∀ t,
    t₀ ≤ t → t - t₀ ≤ δ_right ε →
    ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε

/-- **Builder for `LocalDerivedCutoffs`** from a single-crossing local
geometric data: window radius `r > 0`, window-in-unit-interval, off-partition,
local uniqueness on the window. The far-bound information is derived
internally from `multi_pole_local_far_bound`.

(The `h_flat` hypothesis is recorded but not used in the proof body: the
flatness is implicit in the strict-monotonicity result, which uses only
the nonzero one-sided derivative limits provided by the immersion.) -/
noncomputable def localDerivedCutoffs
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ r : ℝ}
    (h_window_pos : 0 < r)
    (h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    LocalDerivedCutoffs γ s t₀ r :=
  let dR := exists_right_cutoff_local γ h_window_pos h_window_Icc h_at
    h_local_unique
  let dL := exists_left_cutoff_local γ h_window_pos h_window_Icc h_at
    h_local_unique
  let δR := dR.choose
  let dR_th := dR.choose_spec
  let threshR := dR_th.choose
  let dR_props := dR_th.choose_spec
  let δL := dL.choose
  let dL_th := dL.choose_spec
  let threshL := dL_th.choose
  let dL_props := dL_th.choose_spec
  { δ_left := δL
    δ_right := δR
    threshold := min threshR threshL
    hthresh := lt_min dR_props.1 dL_props.1
    hδ_left_pos := fun ε hε hεt =>
      dL_props.2.1 ε hε (lt_of_lt_of_le hεt (min_le_right _ _))
    hδ_right_pos := fun ε hε hεt =>
      dR_props.2.1 ε hε (lt_of_lt_of_le hεt (min_le_left _ _))
    hδ_left_lt := fun ε hε hεt =>
      dL_props.2.2.1 ε hε (lt_of_lt_of_le hεt (min_le_right _ _))
    hδ_right_lt := fun ε hε hεt =>
      dR_props.2.2.1 ε hε (lt_of_lt_of_le hεt (min_le_left _ _))
    h_exit_left := fun ε hε hεt =>
      dL_props.2.2.2.1 ε hε (lt_of_lt_of_le hεt (min_le_right _ _))
    h_exit_right := fun ε hε hεt =>
      dR_props.2.2.2.1 ε hε (lt_of_lt_of_le hεt (min_le_left _ _))
    h_far_left := fun ε hε hεt =>
      dL_props.2.2.2.2.1 ε hε (lt_of_lt_of_le hεt (min_le_right _ _))
    h_far_right := fun ε hε hεt =>
      dR_props.2.2.2.2.1 ε hε (lt_of_lt_of_le hεt (min_le_left _ _))
    h_near_left := fun ε hε hεt =>
      dL_props.2.2.2.2.2 ε hε (lt_of_lt_of_le hεt (min_le_right _ _))
    h_near_right := fun ε hε hεt =>
      dR_props.2.2.2.2.2 ε hε (lt_of_lt_of_le hεt (min_le_left _ _)) }

/-! ### Multi-crossing CPV existence (T-BR-Y6d)

This section assembles the multi-crossing analog of
`hasCauchyPV_inv_sub_of_flat_one_full`: given a curve `γ` crossing the pole
`s` at finitely many parameters (collected in a `MultiPoleCrossData γ s`),
there exists `L` such that `HasCauchyPV (fun z => (z - s)⁻¹) γ s L`.

The strategy:

1. **Geometric scaffolding (`multi_pole_common_radius`)**: extract a common
   window radius `r > 0` such that each crossing's window
   `[t_i - r, t_i + r] ⊆ [0, 1]` is partition-free and pairwise disjoint.
2. **Per-crossing local cutoff bundles**: for each `t_i`, build
   `LocalDerivedCutoffs γ s t_i r` (each provides exit-time cutoffs
   `δ_left^i, δ_right^i` and asymmetric far/near bounds).
3. **Global threshold**: `θ_global = min_i θ_i` (minimum of all local
   thresholds), plus a positive lower bound `m` for `‖γ(t) - s‖` on the
   complement of `⋃_i (t_i - r, t_i + r)` (from `MultiPoleCrossData.h_complete`
   + compactness + continuity).
4. **Cutoff integral decomposition**: for `ε < min(θ_global, m)`, the cutoff
   integral `∫₀¹ cpvIntegrand` equals a sum of per-crossing pieces
   `T_i(ε) := ∫_{t_i + δ_right^i ε}^{t_i + r} + ∫_{t_i - r}^{t_i - δ_left^i ε}`
   plus a constant smooth piece over the complement.
5. **Per-crossing convergence**: each `T_i(ε)` converges via
   `right_annular_log_diff` + `left_annular_log_diff` + `exit_log_diff_tendsto`
   applied locally.
6. **Total convergence**: by `Tendsto.add` and `Finset.sum`-tendsto, the cutoff
   integral converges to a finite limit `L`.

For existence (`∃ L`), step 5 only needs that each piece is convergent — the
explicit value of `L` (which is `2πi · generalizedWindingNumber γ s` by the
forced identification) is not computed here. -/

/-! ### Localized geometric setup (analog of `cpvFullSetup` for a single window)

Restates `cpvFullSetup` using local uniqueness on `[t₀ - r, t₀ + r]` rather
than global uniqueness on `[0, 1]`.

The development is structured around an **exact-radius** API
(`cpvFullSetup_local_exact`) that accepts the slit-plane chord-quotient bounds
at a user-chosen radius `r > 0`, plus dedicated **radius-existence** theorems
(`exists_chord_slitPlane_radius_right/left`,
`exists_chord_div_endpoint_slitPlane_right/left`) that produce a positive
radius below which the slit-plane conditions hold.

This exact-radius decomposition is crucial for **multi-crossing aggregation**:
each crossing supplies its own threshold radius, and the caller can take the
minimum over all crossings so that every crossing's window has the *same*
fixed radius `r`. The legacy `cpvFullSetup_local` (which returns a shrunk
radius) is now a thin wrapper around `cpvFullSetup_local_exact`. -/

/-- **Right-side chord-quotient radius existence**: given a right one-sided
derivative limit `L ≠ 0`, there exists `r > 0` such that the chord quotient
`(γ(b) - s) / (γ(a) - s) ∈ Complex.slitPlane` for all `t₀ < a ≤ b ≤ t₀ + r`.

Pure repackaging of `exists_slitPlane_chord_quotient_right`. Provided as a
companion to the exact-radius API so that callers can derive their per-crossing
threshold radius before invoking `cpvFullSetup_local_exact`. -/
theorem exists_chord_slitPlane_radius_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Set.Ioi t₀) t₀)
    (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane :=
  exists_slitPlane_chord_quotient_right h_deriv h_at hL

/-- **Left-side chord-quotient radius existence (forward direction)**: given a
left one-sided derivative limit `L ≠ 0`, there exists `r > 0` such that the
chord quotient `(γ(b) - s) / (γ(a) - s) ∈ Complex.slitPlane` for all
`t₀ - r ≤ a ≤ b < t₀`.

Pure repackaging of `exists_slitPlane_chord_quotient_left_forward`. -/
theorem exists_chord_slitPlane_radius_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Set.Iio t₀) t₀)
    (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane :=
  exists_slitPlane_chord_quotient_left_forward h_deriv h_at hL

/-- **Right boundary slit-plane radius existence**: given a right one-sided
derivative limit `L ≠ 0`, there exists `r > 0` such that for every
`0 < r' ≤ r`, the boundary chord-to-tangent quotient
`(γ(t₀ + r') - s) / L ∈ Complex.slitPlane`.

The proof uses the normalized chord bound
`‖(γ(t₀ + r') - s) / (L · r') - 1‖ ≤ 1/4`, which yields
`Re((γ(t₀ + r') - s) / (L · r')) ≥ 3/4`. Multiplying by the positive real
`r'` (which preserves slit-plane membership) gives the desired result. -/
theorem exists_chord_div_endpoint_slitPlane_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Set.Ioi t₀) t₀)
    (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      (γ (t₀ + r') - s) / L ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_right h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun r' hr'_pos hr'_le => ?_⟩
  have h_in : (t₀ + r') ∈ Set.Ioc t₀ (t₀ + r) := ⟨by linarith, by linarith⟩
  have h_simp : (((t₀ + r') - t₀ : ℝ) : ℂ) = ((r' : ℝ) : ℂ) := by push_cast; ring
  have h_close : ‖(γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)) - 1‖ ≤ 1 / 4 := by
    rw [← h_simp]; exact hr_close (t₀ + r') h_in
  have h_re_close : (3 / 4 : ℝ) ≤
      ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))).re := by
    have h_abs_le :
        |((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)) - 1).re| ≤ 1 / 4 :=
      le_trans (Complex.abs_re_le_norm _) h_close
    have h_re_eq : ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)) - 1).re =
        ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))).re - 1 := by simp
    rw [h_re_eq] at h_abs_le
    linarith [(abs_le.mp h_abs_le).1]
  have hr'_C_ne : ((r' : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hr'_pos)
  have hLr'_ne : L * ((r' : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL hr'_C_ne
  have h_div_eq : (γ (t₀ + r') - s) / L =
      ((r' : ℝ) : ℂ) * ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))) := by
    field_simp
  rw [h_div_eq, Complex.mem_slitPlane_iff]
  left
  have h_re_calc :
      (((r' : ℝ) : ℂ) * ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)))).re =
        r' * ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  rw [h_re_calc]
  have h_pos_prod : 0 < r' * (3 / 4 : ℝ) := by positivity
  exact lt_of_lt_of_le h_pos_prod
    (mul_le_mul_of_nonneg_left h_re_close hr'_pos.le)

/-- **Left boundary slit-plane radius existence**: given a left one-sided
derivative limit `L ≠ 0`, there exists `r > 0` such that for every
`0 < r' ≤ r` with `γ(t₀ - r') ≠ s`, the negated boundary quotient
`-L / (γ(t₀ - r') - s) ∈ Complex.slitPlane`.

The `γ(t₀ - r') ≠ s` hypothesis is supplied by the caller (typically via
local uniqueness on the window). The proof uses `‖−q − 1‖ ≤ 1/4` where
`q = (γ(t₀ - r') - s) / (L · r')`, then deduces `‖q‖ ≥ 3/4`, then
`‖−1/q − 1‖ ≤ 1/3`, then `Re(−1/q) ≥ 2/3`, and finally multiplies by `1/r' > 0`. -/
theorem exists_chord_div_endpoint_slitPlane_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Set.Iio t₀) t₀)
    (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r → γ (t₀ - r') ≠ s →
      (-L) / (γ (t₀ - r') - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_left h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun r' hr'_pos hr'_le h_γ_ne => ?_⟩
  have h_in : (t₀ - r') ∈ Set.Ico (t₀ - r) t₀ :=
    ⟨by linarith, by linarith⟩
  have h_simp_in : (((t₀ - r') - t₀ : ℝ) : ℂ) = -((r' : ℝ) : ℂ) := by
    push_cast; ring
  have h_close : ‖(γ (t₀ - r') - s) / (L * -((r' : ℝ) : ℂ)) - 1‖ ≤ 1 / 4 := by
    rw [← h_simp_in]; exact hr_close (t₀ - r') h_in
  have hr'_C_ne : ((r' : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hr'_pos)
  have h_γMinus_ne : γ (t₀ - r') - s ≠ 0 := sub_ne_zero.mpr h_γ_ne
  set q : ℂ := (γ (t₀ - r') - s) / (L * ((r' : ℝ) : ℂ)) with hq_def
  have hq_close : ‖-q - 1‖ ≤ 1 / 4 := by
    have h_eq : (γ (t₀ - r') - s) / (L * -((r' : ℝ) : ℂ)) = -q := by
      rw [hq_def, mul_neg, div_neg]
    rw [h_eq] at h_close
    exact h_close
  have hq_norm : 3 / 4 ≤ ‖q‖ := by
    have h1 : ‖q + 1‖ = ‖-q - 1‖ := by
      rw [show q + 1 = -(-q - 1) from by ring, norm_neg]
    have h2 : ‖q + 1‖ ≤ 1 / 4 := h1.trans_le hq_close
    have h_rev : ‖(-1 : ℂ)‖ - ‖q‖ ≤ ‖-1 - q‖ := norm_sub_norm_le _ _
    rw [norm_neg, norm_one] at h_rev
    have h_eq : (-1 : ℂ) - q = -(q + 1) := by ring
    rw [h_eq, norm_neg] at h_rev
    linarith
  have hq_ne : q ≠ 0 := by
    intro h_eq
    rw [h_eq, norm_zero] at hq_norm
    linarith
  have h_neg_inv_q_close : ‖(-1 / q) - 1‖ ≤ 1 / 3 := by
    have h_eq : ((-1 : ℂ) / q) - 1 = -((1 + q) / q) := by
      field_simp; ring
    rw [h_eq, norm_neg, norm_div]
    have h_one_plus_q : ‖(1 : ℂ) + q‖ = ‖-q - 1‖ := by
      have : (1 : ℂ) + q = -(-q - 1) := by ring
      rw [this, norm_neg]
    rw [h_one_plus_q]
    have hq_norm_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq_ne
    rw [div_le_iff₀ hq_norm_pos]
    calc ‖-q - 1‖ ≤ 1 / 4 := hq_close
      _ ≤ (1 / 3) * (3 / 4) := by norm_num
      _ ≤ (1 / 3) * ‖q‖ :=
        mul_le_mul_of_nonneg_left hq_norm (by norm_num)
  have h_eq_target : (-L) / (γ (t₀ - r') - s) =
      (((1 / r' : ℝ)) : ℂ) * (-1 / q) := by
    rw [hq_def]; push_cast; field_simp
  rw [h_eq_target, Complex.mem_slitPlane_iff]
  left
  have h_re_calc :
      ((((1 / r' : ℝ)) : ℂ) * (-1 / q)).re = (1 / r') * (-1 / q).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  rw [h_re_calc]
  have h_abs_re_le : |(-1 / q - 1).re| ≤ 1 / 3 :=
    le_trans (Complex.abs_re_le_norm _) h_neg_inv_q_close
  have h_re_eq : (-1 / q - 1).re = (-1 / q).re - 1 := by simp
  rw [h_re_eq] at h_abs_re_le
  have h_re_ge : (2 / 3 : ℝ) ≤ (-1 / q).re := by
    linarith [(abs_le.mp h_abs_re_le).1]
  have h_inv_r_pos : 0 < 1 / r' := by positivity
  have h_prod_pos : 0 < (1 / r') * (2 / 3 : ℝ) := by positivity
  linarith [mul_le_mul_of_nonneg_left h_re_ge h_inv_r_pos.le]

/-- **One-sided derivative limit setup at an interior crossing.** Extracts the
nonzero one-sided derivatives `L_R, L_L` and the corresponding
`HasDerivWithinAt` witnesses on `Ioi t₀, Iio t₀` from the immersion
infrastructure. This is the radius-independent substrate of
`cpvFullSetup_local`. -/
theorem oneSided_deriv_setup
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ (L_R L_L : ℂ),
      L_R ≠ 0 ∧ L_L ≠ 0 ∧
      HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_R
        (Set.Ioi t₀) t₀ ∧
      HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_L
        (Set.Iio t₀) t₀ := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  obtain ⟨L_R, hL_R_ne, hL_R_tendsto⟩ := exists_right_deriv_limit γ ht₀
  obtain ⟨L_L, hL_L_ne, hL_L_tendsto⟩ := exists_left_deriv_limit γ ht₀
  have hγf_cont : ContinuousAt γf t₀ :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousAt
  have hγf_diff_right : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γf t :=
    eventually_differentiable_right γ ht₀
  have hγf_diff_left : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γf t :=
    eventually_differentiable_left γ ht₀
  obtain ⟨S_R, hS_R_mem, hS_R_diff⟩ := hγf_diff_right.exists_mem
  obtain ⟨S_L, hS_L_mem, hS_L_diff⟩ := hγf_diff_left.exists_mem
  have h_deriv_right : HasDerivWithinAt γf L_R (Set.Ioi t₀) t₀ :=
    hasDerivWithinAt_Ioi_iff_Ici.mpr
      (hasDerivWithinAt_Ici_of_tendsto_deriv
        (fun t ht => (hS_R_diff t ht).differentiableWithinAt)
        hγf_cont.continuousWithinAt hS_R_mem hL_R_tendsto)
  have h_deriv_left : HasDerivWithinAt γf L_L (Set.Iio t₀) t₀ :=
    hasDerivWithinAt_Iio_iff_Iic.mpr
      (hasDerivWithinAt_Iic_of_tendsto_deriv
        (fun t ht => (hS_L_diff t ht).differentiableWithinAt)
        hγf_cont.continuousWithinAt hS_L_mem hL_L_tendsto)
  exact ⟨L_R, L_L, hL_R_ne, hL_L_ne, h_deriv_right, h_deriv_left⟩

/-- **Local geometric setup at a crossing, exact-radius form.** Accepts the
slit-plane chord-quotient bounds at an arbitrary user-chosen radius `r > 0`
as hypotheses, rather than internally shrinking the radius to obtain them.

This is the headline of T-BR-Y9c. Compared to the legacy `cpvFullSetup_local`
(which returns an *output* radius `r ≤ r₀`), the exact form keeps the input
radius `r` and exposes the slit-plane conditions as named hypotheses. This is
essential for multi-crossing aggregation: take
`r = min_i r_i` where each `r_i` is the threshold from
`exists_chord_slitPlane_radius_right/left` and
`exists_chord_div_endpoint_slitPlane_right/left` at the `i`-th crossing.

The hypothesis `h_local_unique` is used only to derive `γ(t₀ - r) ≠ s` for the
boundary slit-plane condition on the left side; for the right side, the chord
quotient hypothesis already ensures `γ(t₀ + r) - s ≠ 0`.

This is a pure repackaging theorem: it takes derivative-side and slit-plane
data already in hand and bundles them in the same shape as the legacy
`cpvFullSetup_local`. Most parameters (`ht₀`, `h_at`, `hr_pos`,
`h_window_in_unit`, `h_local_unique`, `hL_R_ne`, `hL_L_ne`) are *contract*
parameters — they document the setting in which the bundled output is to be
used downstream, even though they are not directly consumed by the proof body.
Underscored locally to silence the unused-variable linter. -/
theorem cpvFullSetup_local_exact
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (_ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (_h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    {r : ℝ} (_hr_pos : 0 < r)
    (_h_window_in_unit : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (_h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    {L_R L_L : ℂ} (_hL_R_ne : L_R ≠ 0) (_hL_L_ne : L_L ≠ 0)
    (h_deriv_right : HasDerivWithinAt
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_R (Set.Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_L (Set.Iio t₀) t₀)
    (h_slit_chord_R : ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
          Complex.slitPlane)
    (h_slit_chord_L : ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
          Complex.slitPlane)
    (h_γPlus_div_LR :
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + r) - s) / L_R ∈
        Complex.slitPlane)
    (h_LL_neg_div_γMinus :
      (-L_L) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - r) - s) ∈
        Complex.slitPlane) :
    HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_R
        (Set.Ioi t₀) t₀ ∧
      HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_L
        (Set.Iio t₀) t₀ ∧
      (∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
          (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
            Complex.slitPlane) ∧
      (∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
          (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
            Complex.slitPlane) ∧
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + r) - s) / L_R ∈
        Complex.slitPlane ∧
      (-L_L) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - r) - s) ∈
        Complex.slitPlane := by
  -- All structure was supplied; just repackage.
  exact ⟨h_deriv_right, h_deriv_left, h_slit_chord_R, h_slit_chord_L,
    h_γPlus_div_LR, h_LL_neg_div_γMinus⟩

/-- **Local geometric setup at a crossing.** Replicates `cpvFullSetup` but
requires only local uniqueness on the window `[t₀ - r₀, t₀ + r₀] ⊆ [0, 1]`.

Legacy form: returns a radius `r ≤ r₀` chosen as the minimum of four
threshold radii (chord-quotient + boundary, on each side). Now a thin wrapper
around `cpvFullSetup_local_exact` + the radius-existence theorems. -/
private theorem cpvFullSetup_local
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    {r₀ : ℝ} (hr₀_pos : 0 < r₀)
    (_h_window_in_unit : Set.Icc (t₀ - r₀) (t₀ + r₀) ⊆ Set.Icc (0 : ℝ) 1)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r₀) (t₀ + r₀),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∃ (L_R L_L : ℂ) (r : ℝ),
      L_R ≠ 0 ∧ L_L ≠ 0 ∧ 0 < r ∧ r ≤ r₀ ∧
      HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_R
        (Set.Ioi t₀) t₀ ∧
      HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_L
        (Set.Iio t₀) t₀ ∧
      (∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
          (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
            Complex.slitPlane) ∧
      (∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
          (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
            Complex.slitPlane) ∧
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + r) - s) / L_R ∈
        Complex.slitPlane ∧
      (-L_L) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - r) - s) ∈
        Complex.slitPlane := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  obtain ⟨L_R, L_L, hL_R_ne, hL_L_ne, h_deriv_right, h_deriv_left⟩ :=
    oneSided_deriv_setup γ ht₀
  obtain ⟨r_R₁, hr_R₁_pos, hr_R₁_slit⟩ :=
    exists_chord_slitPlane_radius_right h_deriv_right h_at hL_R_ne
  obtain ⟨r_L₁, hr_L₁_pos, hr_L₁_slit⟩ :=
    exists_chord_slitPlane_radius_left h_deriv_left h_at hL_L_ne
  obtain ⟨r_R₂, hr_R₂_pos, hr_R₂_endpoint⟩ :=
    exists_chord_div_endpoint_slitPlane_right h_deriv_right h_at hL_R_ne
  obtain ⟨r_L₂, hr_L₂_pos, hr_L₂_endpoint⟩ :=
    exists_chord_div_endpoint_slitPlane_left h_deriv_left h_at hL_L_ne
  set r : ℝ := min (min r_R₁ r_L₁) (min (min r_R₂ r_L₂) r₀) with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    exact lt_min (lt_min hr_R₁_pos hr_L₁_pos)
      (lt_min (lt_min hr_R₂_pos hr_L₂_pos) hr₀_pos)
  have hr_le_R₁ : r ≤ r_R₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hr_le_L₁ : r ≤ r_L₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hr_le_R₂ : r ≤ r_R₂ :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hr_le_L₂ : r ≤ r_L₂ :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hr_le_r₀ : r ≤ r₀ := le_trans (min_le_right _ _) (min_le_right _ _)
  have h_γMinus_ne : γf (t₀ - r) ≠ s := by
    intro h_eq
    have h_in_window : t₀ - r ∈ Set.Icc (t₀ - r₀) (t₀ + r₀) :=
      ⟨by linarith [hr_le_r₀], by linarith⟩
    have h_eq_t₀ := h_local_unique _ h_in_window h_eq
    linarith
  have h_γPlus_div_LR : (γf (t₀ + r) - s) / L_R ∈ Complex.slitPlane :=
    hr_R₂_endpoint r hr_pos hr_le_R₂
  have h_LL_neg_div_γMinus : (-L_L) / (γf (t₀ - r) - s) ∈ Complex.slitPlane :=
    hr_L₂_endpoint r hr_pos hr_le_L₂ h_γMinus_ne
  refine ⟨L_R, L_L, r, hL_R_ne, hL_L_ne, hr_pos, hr_le_r₀,
    h_deriv_right, h_deriv_left, ?_, ?_, h_γPlus_div_LR, h_LL_neg_div_γMinus⟩
  · intro a b ha_gt hab hb_le
    exact hr_R₁_slit a b ha_gt hab (le_trans hb_le (by linarith [hr_le_R₁]))
  · intro a b ha_ge hab hb_lt
    exact hr_L₁_slit a b (le_trans (by linarith [hr_le_L₁]) ha_ge) hab hb_lt

/-! ### Localized FTC log-difference (replaces global uniqueness)

Restates `right_annular_log_diff` and `left_annular_log_diff` using local
uniqueness on the window. -/

/-- **Local right annular log-difference**: integral on `[t₀ + δ_R, t₀ + r]`
of `γ'/(γ-s)` equals the log of the chord quotient. Local-uniqueness version
of `right_annular_log_diff`. -/
private theorem right_annular_log_diff_local
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    {L_right : ℂ} (_hL_right_ne : L_right ≠ 0)
    (_h_deriv_right : HasDerivWithinAt
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_right (Set.Ioi t₀) t₀)
    (_h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    {r δ_R : ℝ} (hδ_R_pos : 0 < δ_R) (hδ_R_lt : δ_R < r) (_hr_pos : 0 < r)
    (h_window_in_unit : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_slit_R : ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
        Complex.slitPlane)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∫ t in (t₀ + δ_R)..(t₀ + r),
      deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s) =
    Complex.log
      ((γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + r) - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + δ_R) - s)) := by
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  set a : ℝ := t₀ + δ_R
  set b : ℝ := t₀ + r
  have hab : a ≤ b := by simp only [a, b]; linarith
  have ha_gt : t₀ < a := by simp only [a]; linarith
  have hb_le : b ≤ t₀ + r := by simp only [b]; linarith
  -- Window endpoints lie in [0, 1].
  have hb_in_01 : b ∈ Set.Icc (0 : ℝ) 1 :=
    h_window_in_unit ⟨by simp only [b]; linarith, le_rfl⟩
  have ha_in_01 : a ∈ Set.Icc (0 : ℝ) 1 :=
    h_window_in_unit ⟨by simp only [a]; linarith, by simp only [a]; linarith⟩
  have h_slit_ab : ∀ t ∈ Set.Icc a b, (γf t - s) / (γf a - s) ∈ Complex.slitPlane := by
    intro t ht_in
    apply h_slit_R a t ha_gt ht_in.1 (le_trans ht_in.2 hb_le)
  -- γ a - s ≠ 0 via h_local_unique on [t₀ - r, t₀ + r].
  have ha_ne : γf a - s ≠ 0 := by
    intro h_eq
    have h_in_window : a ∈ Set.Icc (t₀ - r) (t₀ + r) :=
      ⟨by simp only [a]; linarith, by simp only [a]; linarith⟩
    have : a = t₀ := h_local_unique a h_in_window (sub_eq_zero.mp h_eq)
    simp only [a] at this
    linarith
  have hγ_cont : ContinuousOn γf (Set.Icc a b) :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousOn
  set P : Set ℝ := ↑γ.toPwC1Immersion.toPiecewiseC1Path.partition with hP_def
  have hP_count : P.Countable :=
    γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.countable
  have hγ_diff : ∀ t ∈ Set.Ioo a b \ P, HasDerivAt γf (deriv γf t) t := by
    intro t ht
    have h_t_in_Icc : t ∈ Set.Icc a b := Set.Ioo_subset_Icc_self ht.1
    have h_t_in_01_Icc : t ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_trans ha_in_01.1 h_t_in_Icc.1, le_trans h_t_in_Icc.2 hb_in_01.2⟩
    have ht_in_Ioo : t ∈ Set.Ioo (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · have h_lt_a : t > a := ht.1.1
        have : 0 < a := by
          rcases lt_or_eq_of_le ha_in_01.1 with h | h
          · exact h
          · -- a = 0; but a = t₀ + δ_R > t₀ > 0 if t₀ > 0. Otherwise we use ht.1.1
            exfalso
            -- We have a = 0 → t₀ + δ_R = 0 → t₀ = -δ_R < 0, contradicting t₀ ≥ ... ah
            -- Actually we need a > 0 from window. Hmm.
            -- a ∈ Icc 0 1, a = 0 means t₀ + δ_R = 0; if t₀ ≥ 0 (window ⊆ [0,1])
            -- then δ_R ≤ 0, contradicting hδ_R_pos.
            -- The window [t₀ - r, t₀ + r] ⊆ [0, 1] means t₀ - r ≥ 0, so t₀ ≥ r > 0,
            -- so a = t₀ + δ_R > t₀ > 0. So a = 0 is impossible.
            have h_tw_r_ge_0 : t₀ - r ≥ 0 := by
              have := (h_window_in_unit (Set.left_mem_Icc.mpr (by linarith))).1
              exact this
            have : 0 < a := by simp only [a]; linarith
            linarith
        linarith
      · have h_lt_b : t < b := ht.1.2
        have : b ≤ 1 := hb_in_01.2
        linarith
    have h_diff_at : DifferentiableAt ℝ γf t :=
      γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off t ht_in_Ioo ht.2
    exact h_diff_at.hasDerivAt
  -- Integrability of γ'/(γ-s) on [a, b].
  have h_int : IntervalIntegrable
      (fun t => deriv γf t / (γf t - s)) MeasureTheory.volume a b := by
    -- Build via inv_sub_mul_deriv_intervalIntegrable.
    have h_in_01 : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1 := by
      intro u hu
      exact ⟨le_trans ha_in_01.1 hu.1, le_trans hu.2 hb_in_01.2⟩
    have h_ne : ∀ t ∈ Set.Icc a b,
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t ≠ s := by
      intro t ht h_eq
      have h_in_window : t ∈ Set.Icc (t₀ - r) (t₀ + r) := by
        refine ⟨?_, le_trans ht.2 hb_le⟩
        have : a > t₀ - r := by simp only [a]; linarith
        linarith [ht.1]
      have h_t_eq : t = t₀ := h_local_unique t h_in_window h_eq
      have h_t_gt_t₀ : t₀ < t := lt_of_lt_of_le ha_gt ht.1
      linarith
    have h1 := inv_sub_mul_deriv_intervalIntegrable γ hab h_in_01 h_ne
    refine h1.congr (fun t _ => ?_)
    simp only [hγf_def]; ring
  exact segment_log_FTC hab hP_count hγ_cont hγ_diff ha_ne h_slit_ab h_int

/-- **Local left annular log-difference**: integral on `[t₀ - r, t₀ - δ_L]`
of `γ'/(γ-s)` equals the log of the chord quotient. Local-uniqueness version
of `left_annular_log_diff`. -/
private theorem left_annular_log_diff_local
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    {L_left : ℂ} (_hL_left_ne : L_left ≠ 0)
    (_h_deriv_left : HasDerivWithinAt
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_left (Set.Iio t₀) t₀)
    (_h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    {r δ_L : ℝ} (hδ_L_pos : 0 < δ_L) (hδ_L_lt : δ_L < r) (_hr_pos : 0 < r)
    (h_window_in_unit : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_slit_L : ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
        Complex.slitPlane)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∫ t in (t₀ - r)..(t₀ - δ_L),
      deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s) =
    Complex.log
      ((γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - δ_L) - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - r) - s)) := by
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  set a : ℝ := t₀ - r
  set b : ℝ := t₀ - δ_L
  have hab : a ≤ b := by simp only [a, b]; linarith
  have ha_ge : t₀ - r ≤ a := le_refl _
  have hb_lt : b < t₀ := by simp only [b]; linarith
  have ha_in_01 : a ∈ Set.Icc (0 : ℝ) 1 :=
    h_window_in_unit ⟨le_rfl, by simp only [a]; linarith⟩
  have hb_in_01 : b ∈ Set.Icc (0 : ℝ) 1 :=
    h_window_in_unit ⟨by simp only [b]; linarith, by simp only [b]; linarith⟩
  have h_slit_ab : ∀ t ∈ Set.Icc a b, (γf t - s) / (γf a - s) ∈ Complex.slitPlane := by
    intro t ht_in
    apply h_slit_L a t ha_ge ht_in.1 (lt_of_le_of_lt ht_in.2 hb_lt)
  have ha_ne : γf a - s ≠ 0 := by
    intro h_eq
    have h_in_window : a ∈ Set.Icc (t₀ - r) (t₀ + r) :=
      ⟨le_rfl, by simp only [a]; linarith⟩
    have : a = t₀ := h_local_unique a h_in_window (sub_eq_zero.mp h_eq)
    simp only [a] at this
    linarith
  have hγ_cont : ContinuousOn γf (Set.Icc a b) :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousOn
  set P : Set ℝ := ↑γ.toPwC1Immersion.toPiecewiseC1Path.partition with hP_def
  have hP_count : P.Countable :=
    γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.countable
  have hγ_diff : ∀ t ∈ Set.Ioo a b \ P, HasDerivAt γf (deriv γf t) t := by
    intro t ht
    have h_t_in_Icc : t ∈ Set.Icc a b := Set.Ioo_subset_Icc_self ht.1
    have ht_in_Ioo : t ∈ Set.Ioo (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · have h_gt_a : t > a := ht.1.1
        have h_a_pos_or_zero := ha_in_01.1
        -- a ∈ Icc 0 1, a = t₀ - r. We need 0 < t. From t > a and a ≥ 0 we only get t > 0
        -- if a > 0. Note a ≥ 0 means t₀ ≥ r > 0. But if a = 0 then t₀ = r and t > 0.
        rcases lt_or_eq_of_le h_a_pos_or_zero with h | h
        · linarith
        · linarith
      · have h_lt_b : t < b := ht.1.2
        have : b ≤ 1 := hb_in_01.2
        linarith
    have h_diff_at : DifferentiableAt ℝ γf t :=
      γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off t ht_in_Ioo ht.2
    exact h_diff_at.hasDerivAt
  have h_int : IntervalIntegrable
      (fun t => deriv γf t / (γf t - s)) MeasureTheory.volume a b := by
    have h_in_01 : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1 := by
      intro u hu
      exact ⟨le_trans ha_in_01.1 hu.1, le_trans hu.2 hb_in_01.2⟩
    have h_ne : ∀ t ∈ Set.Icc a b,
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t ≠ s := by
      intro t ht h_eq
      have h_in_window : t ∈ Set.Icc (t₀ - r) (t₀ + r) := by
        refine ⟨le_trans ha_ge ht.1, ?_⟩
        have : b < t₀ + r := by simp only [b]; linarith
        linarith [ht.2]
      have h_t_eq : t = t₀ := h_local_unique t h_in_window h_eq
      have h_t_lt_t₀ : t < t₀ := lt_of_le_of_lt ht.2 hb_lt
      linarith
    have h1 := inv_sub_mul_deriv_intervalIntegrable γ hab h_in_01 h_ne
    refine h1.congr (fun t _ => ?_)
    simp only [hγf_def]; ring
  exact segment_log_FTC hab hP_count hγ_cont hγ_diff ha_ne h_slit_ab h_int

/-! ### Local versions of `δ_*_tendsto_zero` -/

/-- **`δ_right` of a `LocalDerivedCutoffs` tends to `0⁺` as `ε → 0⁺`**. -/
theorem LocalDerivedCutoffs.δ_right_tendsto_zero
    {γ : ClosedPwC1Immersion x} {s : ℂ} {t₀ r : ℝ} (_hr_pos : 0 < r)
    (h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (D : LocalDerivedCutoffs γ s t₀ r) :
    Tendsto D.δ_right (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro δ₀ hδ₀_pos
    set δ₀' : ℝ := min δ₀ (r / 2) with hδ₀'_def
    have hδ₀'_pos : 0 < δ₀' := lt_min hδ₀_pos (by linarith)
    have hδ₀'_le : δ₀' ≤ δ₀ := min_le_left _ _
    have hδ₀'_le_r : δ₀' ≤ r / 2 := min_le_right _ _
    have hδ₀'_lt_r : δ₀' < r := by linarith
    have h_in_window : t₀ + δ₀' ∈ Set.Icc (t₀ - r) (t₀ + r) :=
      ⟨by linarith, by linarith⟩
    set m : ℝ := ‖γf (t₀ + δ₀') - s‖ with hm_def
    have hm_pos : 0 < m := by
      rw [hm_def]
      refine norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
      intro h_eq
      have ht_eq : t₀ + δ₀' = t₀ := h_local_unique _ h_in_window h_eq
      linarith
    set ε_star : ℝ := min m D.threshold with hε_star_def
    have hε_star_pos : 0 < ε_star := lt_min hm_pos D.hthresh
    have hmem : Set.Ioo (0 : ℝ) ε_star ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hε_star_pos
    filter_upwards [hmem] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt_thresh : ε < D.threshold := lt_of_lt_of_le hε.2 (min_le_right _ _)
    have hε_lt_m : ε < m := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hδR_pos := D.hδ_right_pos ε hε_pos hε_lt_thresh
    by_contra h_ge
    push Not at h_ge
    rw [Real.dist_eq, sub_zero, abs_of_pos hδR_pos] at h_ge
    have h_δ_ge_δ₀' : δ₀' ≤ D.δ_right ε := hδ₀'_le.trans h_ge
    have h_t_in : t₀ + δ₀' - t₀ ≤ D.δ_right ε := by linarith
    have h_norm_le := D.h_near_right ε hε_pos hε_lt_thresh (t₀ + δ₀')
      (by linarith) h_t_in
    linarith
  · have hmem : Set.Ioo (0 : ℝ) D.threshold ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT D.hthresh
    filter_upwards [hmem] with ε hε
    exact D.hδ_right_pos ε hε.1 hε.2

/-- **`δ_left` of a `LocalDerivedCutoffs` tends to `0⁺` as `ε → 0⁺`**. -/
theorem LocalDerivedCutoffs.δ_left_tendsto_zero
    {γ : ClosedPwC1Immersion x} {s : ℂ} {t₀ r : ℝ} (_hr_pos : 0 < r)
    (h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (D : LocalDerivedCutoffs γ s t₀ r) :
    Tendsto D.δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro δ₀ hδ₀_pos
    set δ₀' : ℝ := min δ₀ (r / 2) with hδ₀'_def
    have hδ₀'_pos : 0 < δ₀' := lt_min hδ₀_pos (by linarith)
    have hδ₀'_le : δ₀' ≤ δ₀ := min_le_left _ _
    have hδ₀'_le_r : δ₀' ≤ r / 2 := min_le_right _ _
    have hδ₀'_lt_r : δ₀' < r := by linarith
    have h_in_window : t₀ - δ₀' ∈ Set.Icc (t₀ - r) (t₀ + r) :=
      ⟨by linarith, by linarith⟩
    set m : ℝ := ‖γf (t₀ - δ₀') - s‖ with hm_def
    have hm_pos : 0 < m := by
      rw [hm_def]
      refine norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
      intro h_eq
      have ht_eq : t₀ - δ₀' = t₀ := h_local_unique _ h_in_window h_eq
      linarith
    set ε_star : ℝ := min m D.threshold with hε_star_def
    have hε_star_pos : 0 < ε_star := lt_min hm_pos D.hthresh
    have hmem : Set.Ioo (0 : ℝ) ε_star ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hε_star_pos
    filter_upwards [hmem] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt_thresh : ε < D.threshold := lt_of_lt_of_le hε.2 (min_le_right _ _)
    have hε_lt_m : ε < m := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hδL_pos := D.hδ_left_pos ε hε_pos hε_lt_thresh
    by_contra h_ge
    push Not at h_ge
    rw [Real.dist_eq, sub_zero, abs_of_pos hδL_pos] at h_ge
    have h_δ_ge_δ₀' : δ₀' ≤ D.δ_left ε := hδ₀'_le.trans h_ge
    have h_t_ge : t₀ - D.δ_left ε ≤ t₀ - δ₀' := by linarith
    have h_norm_le := D.h_near_left ε hε_pos hε_lt_thresh (t₀ - δ₀')
      h_t_ge (by linarith)
    linarith
  · have hmem : Set.Ioo (0 : ℝ) D.threshold ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT D.hthresh
    filter_upwards [hmem] with ε hε
    exact D.hδ_left_pos ε hε.1 hε.2

/-! ### Per-window cutoff integral convergence (T-BR-Y6d core lemma)

For a single crossing `t_i` with local cutoffs from `LocalDerivedCutoffs`, the
per-window cutoff integral `∫_{[t_i - r, t_i + r]} cpvIntegrand(ε)` converges
as `ε → 0⁺`. This is the multi-crossing analog of the convergence proof in
`hasCauchyPV_inv_sub_of_flat_one_full`, localized to a single window. -/

/-- **Per-window cutoff integral converges, exact-radius form** (T-BR-Y9c).

Like `perCrossing_window_integral_tendsto`, but takes the window radius `r`
and all slit-plane chord-quotient/boundary data as INPUTS rather than deriving
them via `cpvFullSetup_local` (which would shrink `r`). This unblocks
multi-crossing aggregation: each crossing supplies its threshold radius
`r_i`, the caller takes `r = min_i r_i`, and every crossing's window uses the
SAME fixed radius `r`.

The caller is responsible for ensuring the slit-plane bounds hold at the
chosen `r`. The companion theorems
`exists_chord_slitPlane_radius_right/left` and
`exists_chord_div_endpoint_slitPlane_right/left` produce per-crossing
threshold radii. -/
theorem perCrossing_window_integral_tendsto_exact
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    {r : ℝ} (hr_pos : 0 < r)
    (h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_local_unique_r : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    {L_R L_L : ℂ} (hL_R_ne : L_R ≠ 0) (hL_L_ne : L_L ≠ 0)
    (h_deriv_right : HasDerivWithinAt
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_R (Set.Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_L (Set.Iio t₀) t₀)
    (h_slit_R : ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
          Complex.slitPlane)
    (h_slit_L : ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
          Complex.slitPlane)
    (h_γPlus_div_LR :
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + r) - s) / L_R ∈
        Complex.slitPlane)
    (h_LL_neg_div_γMinus :
      (-L_L) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - r) - s) ∈
        Complex.slitPlane) :
    ∃ L_i : ℂ,
      Tendsto (fun ε : ℝ =>
        ∫ t in (t₀ - r)..(t₀ + r),
          cpvIntegrand (fun z => (z - s)⁻¹)
            γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε t)
        (𝓝[>] (0 : ℝ)) (𝓝 L_i) := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  -- Build local cutoffs on window [t₀ - r, t₀ + r].
  set D := localDerivedCutoffs γ hr_pos h_window_Icc h_at h_local_unique_r
    with hD_def
  have hδR_tendsto : Tendsto D.δ_right (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    LocalDerivedCutoffs.δ_right_tendsto_zero hr_pos h_window_Icc h_local_unique_r D
  have hδL_tendsto : Tendsto D.δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    LocalDerivedCutoffs.δ_left_tendsto_zero hr_pos h_window_Icc h_local_unique_r D
  have hδR_lt_r : ∀ᶠ ε in 𝓝[>] (0 : ℝ), D.δ_right ε < r := by
    have h_abs := (hδR_tendsto.mono_right nhdsWithin_le_nhds).eventually
      (Metric.ball_mem_nhds (0 : ℝ) hr_pos)
    filter_upwards [h_abs] with ε hε
    rw [Real.dist_eq, sub_zero] at hε
    have h_le_abs : D.δ_right ε ≤ |D.δ_right ε| := le_abs_self _
    linarith
  have hδL_lt_r : ∀ᶠ ε in 𝓝[>] (0 : ℝ), D.δ_left ε < r := by
    have h_abs := (hδL_tendsto.mono_right nhdsWithin_le_nhds).eventually
      (Metric.ball_mem_nhds (0 : ℝ) hr_pos)
    filter_upwards [h_abs] with ε hε
    rw [Real.dist_eq, sub_zero] at hε
    have h_le_abs : D.δ_left ε ≤ |D.δ_left ε| := le_abs_self _
    linarith
  have hδR_pos_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < D.δ_right ε := by
    have hmem : Set.Ioo (0 : ℝ) D.threshold ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT D.hthresh
    filter_upwards [hmem] with ε hε
    exact D.hδ_right_pos ε hε.1 hε.2
  have hδL_pos_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < D.δ_left ε := by
    have hmem : Set.Ioo (0 : ℝ) D.threshold ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT D.hthresh
    filter_upwards [hmem] with ε hε
    exact D.hδ_left_pos ε hε.1 hε.2
  -- Step 2: Define the per-window annular log-quotients.
  set Λ_R : ℝ → ℂ := fun ε =>
    Complex.log ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)) with hΛR_def
  set Λ_L : ℝ → ℂ := fun ε =>
    Complex.log ((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)) with hΛL_def
  -- Step 3: arg-limit data.
  have h_arg_R_clean : Tendsto (fun ε : ℝ =>
      Complex.arg ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((γf (t₀ + r) - s) / L_R).arg) :=
    arg_right_annular_tendsto h_deriv_right h_at hL_R_ne h_γPlus_div_LR
      hδR_pos_ev hδR_tendsto
  have h_arg_L_clean : Tendsto (fun ε : ℝ =>
      Complex.arg ((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L_L) / (γf (t₀ - r) - s)).arg) :=
    arg_left_annular_tendsto h_deriv_left h_at hL_L_ne h_LL_neg_div_γMinus
      hδL_pos_ev hδL_tendsto
  set argR_lim : ℝ := ((γf (t₀ + r) - s) / L_R).arg with hargR_def
  set argL_lim : ℝ := ((-L_L) / (γf (t₀ - r) - s)).arg with hargL_def
  set logNorm_diff : ℝ :=
    Real.log ‖γf (t₀ + r) - s‖ - Real.log ‖γf (t₀ - r) - s‖ with hlogND_def
  set L_i : ℂ := ((logNorm_diff : ℝ) : ℂ) +
    (((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I) with hL_i_def
  refine ⟨L_i, ?_⟩
  -- Step 4: Show the cutoff window integral equals Λ_L ε + Λ_R ε eventually.
  have h_eventually_eq :
      (fun ε : ℝ => ∫ t in (t₀ - r)..(t₀ + r),
        cpvIntegrand (fun z => (z - s)⁻¹) γf s ε t) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε => Λ_L ε + Λ_R ε) := by
    filter_upwards [Ioo_mem_nhdsGT D.hthresh, hδR_lt_r, hδL_lt_r,
        hδR_pos_ev, hδL_pos_ev] with ε hε_thresh hδR_r hδL_r hδR_pos hδL_pos
    have hε_pos : 0 < ε := hε_thresh.1
    have hε_lt_thresh : ε < D.threshold := hε_thresh.2
    -- Express window integral via decomposition into 3 pieces.
    -- I = ∫_{t₀-r}^{t₀-δL} cpv + ∫_{t₀-δL}^{t₀+δR} cpv (= 0) + ∫_{t₀+δR}^{t₀+r} cpv.
    -- On outer pieces, cpv = (γ-s)⁻¹ · γ' (far bound).
    -- The two outer integrals = Λ_L(ε) + Λ_R(ε) by FTC.
    set F : ℝ → ℂ := fun t =>
      cpvIntegrand (fun z => (z - s)⁻¹) γf s ε t with hF_def
    set integrand : ℝ → ℂ := fun t => (γf t - s)⁻¹ * deriv γf t with hI_def
    have h_left_lt : t₀ - r < t₀ - D.δ_left ε := by linarith
    have h_mid_lt : t₀ - D.δ_left ε < t₀ + D.δ_right ε := by linarith
    have h_right_lt : t₀ + D.δ_right ε < t₀ + r := by linarith
    -- F = integrand a.e. on left outer piece.
    have hF_left_ae : ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIoc (t₀ - r) (t₀ - D.δ_left ε) → F t = integrand t := by
      have h_sing : ({t₀ - D.δ_left ε} : Set ℝ)ᶜ ∈
          MeasureTheory.ae MeasureTheory.volume :=
        MeasureTheory.compl_mem_ae_iff.mpr
          (by exact (Set.finite_singleton _).measure_zero MeasureTheory.volume)
      filter_upwards [h_sing] with t ht_ne ht_mem
      rw [Set.uIoc_of_le (le_of_lt h_left_lt)] at ht_mem
      have ht_lt : t < t₀ - D.δ_left ε :=
        lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (Set.mem_singleton_iff.mpr h))
      simp only [hF_def, hI_def, cpvIntegrand]
      rw [if_pos]
      refine D.h_far_left ε hε_pos hε_lt_thresh t
        (le_of_lt ht_mem.1) ht_lt
    -- F = 0 a.e. on middle piece.
    have hF_mid : ∀ t ∈ Set.uIoc (t₀ - D.δ_left ε) (t₀ + D.δ_right ε), F t = 0 := by
      intro t ht
      rw [Set.uIoc_of_le (le_of_lt h_mid_lt)] at ht
      simp only [hF_def, cpvIntegrand]
      rw [if_neg (not_lt.mpr _)]
      by_cases h_t_le : t ≤ t₀
      · refine D.h_near_left ε hε_pos hε_lt_thresh t ?_ h_t_le
        linarith [ht.1]
      · push Not at h_t_le
        refine D.h_near_right ε hε_pos hε_lt_thresh t (le_of_lt h_t_le) ?_
        linarith [ht.2]
    -- F = integrand a.e. on right outer piece.
    have hF_right_ae : ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIoc (t₀ + D.δ_right ε) (t₀ + r) → F t = integrand t := by
      have h_sing : ({t₀ + D.δ_right ε} : Set ℝ)ᶜ ∈
          MeasureTheory.ae MeasureTheory.volume :=
        MeasureTheory.compl_mem_ae_iff.mpr
          (by exact (Set.finite_singleton _).measure_zero MeasureTheory.volume)
      filter_upwards [h_sing] with t ht_ne ht_mem
      rw [Set.uIoc_of_le (le_of_lt h_right_lt)] at ht_mem
      have ht_gt : t₀ + D.δ_right ε < t := ht_mem.1
      simp only [hF_def, hI_def, cpvIntegrand]
      rw [if_pos]
      refine D.h_far_right ε hε_pos hε_lt_thresh t ht_gt ht_mem.2
    -- Integrability of integrand on outer pieces.
    have h_in_window_left : Set.Icc (t₀ - r) (t₀ - D.δ_left ε) ⊆
        Set.Icc (0 : ℝ) 1 := by
      intro u hu
      refine ⟨?_, ?_⟩
      · have : (t₀ - r) ∈ Set.Icc (0 : ℝ) 1 :=
          h_window_Icc (Set.left_mem_Icc.mpr (by linarith))
        linarith [hu.1, this.1]
      · linarith [hu.2, ht₀.2]
    have h_in_window_right : Set.Icc (t₀ + D.δ_right ε) (t₀ + r) ⊆
        Set.Icc (0 : ℝ) 1 := by
      intro u hu
      refine ⟨?_, ?_⟩
      · linarith [hu.1, ht₀.1]
      · have : (t₀ + r) ∈ Set.Icc (0 : ℝ) 1 :=
          h_window_Icc (Set.right_mem_Icc.mpr (by linarith))
        linarith [hu.2, this.2]
    have h_int_left :
        IntervalIntegrable integrand MeasureTheory.volume (t₀ - r) (t₀ - D.δ_left ε) := by
      have h_ne_left : ∀ t ∈ Set.Icc (t₀ - r) (t₀ - D.δ_left ε), γf t ≠ s := by
        intro t ht h_eq
        have h_in_window : t ∈ Set.Icc (t₀ - r) (t₀ + r) :=
          ⟨ht.1, by linarith [ht.2]⟩
        have h_t_eq : t = t₀ := h_local_unique_r t h_in_window h_eq
        linarith [ht.2]
      have h1 := inv_sub_mul_deriv_intervalIntegrable γ (le_of_lt h_left_lt)
        h_in_window_left h_ne_left
      exact h1.congr (fun t _ => by ring)
    have h_int_right :
        IntervalIntegrable integrand MeasureTheory.volume (t₀ + D.δ_right ε) (t₀ + r) := by
      have h_ne_right : ∀ t ∈ Set.Icc (t₀ + D.δ_right ε) (t₀ + r), γf t ≠ s := by
        intro t ht h_eq
        have h_in_window : t ∈ Set.Icc (t₀ - r) (t₀ + r) :=
          ⟨by linarith [ht.1], ht.2⟩
        have h_t_eq : t = t₀ := h_local_unique_r t h_in_window h_eq
        linarith [ht.1]
      have h1 := inv_sub_mul_deriv_intervalIntegrable γ (le_of_lt h_right_lt)
        h_in_window_right h_ne_right
      exact h1.congr (fun t _ => by ring)
    -- Integrability of F.
    have hF_int_left : IntervalIntegrable F MeasureTheory.volume
        (t₀ - r) (t₀ - D.δ_left ε) :=
      h_int_left.congr_ae
        ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr
          (hF_left_ae.mono (fun t ht hm => (ht hm).symm)))
    have hF_int_mid :
        IntervalIntegrable F MeasureTheory.volume
          (t₀ - D.δ_left ε) (t₀ + D.δ_right ε) :=
      (IntervalIntegrable.zero (μ := MeasureTheory.volume)
        (a := t₀ - D.δ_left ε) (b := t₀ + D.δ_right ε)).congr
        (fun t ht => (hF_mid t ht).symm)
    have hF_int_right : IntervalIntegrable F MeasureTheory.volume
        (t₀ + D.δ_right ε) (t₀ + r) :=
      h_int_right.congr_ae
        ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr
          (hF_right_ae.mono (fun t ht hm => (ht hm).symm)))
    -- Split the integral.
    have h_split : ∫ t in (t₀ - r)..(t₀ + r), F t =
        (∫ t in (t₀ - r)..(t₀ - D.δ_left ε), F t) +
        (∫ t in (t₀ - D.δ_left ε)..(t₀ + D.δ_right ε), F t) +
        (∫ t in (t₀ + D.δ_right ε)..(t₀ + r), F t) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
            (hF_int_left.trans hF_int_mid) hF_int_right,
          ← intervalIntegral.integral_add_adjacent_intervals hF_int_left hF_int_mid]
    rw [h_split,
        intervalIntegral.integral_zero_ae (MeasureTheory.ae_of_all _ (fun t ht => hF_mid t ht)),
        intervalIntegral.integral_congr_ae hF_left_ae,
        intervalIntegral.integral_congr_ae hF_right_ae, add_zero]
    -- Now have: ∫_{[t₀-r, t₀-δL]} integrand + ∫_{[t₀+δR, t₀+r]} integrand.
    -- Identify with Λ_L ε + Λ_R ε via FTC.
    -- ∫_{[t₀-r, t₀-δL]} (γ-s)⁻¹ γ' = ∫ γ'/(γ-s) = log((γ(t₀-δL)-s)/(γ(t₀-r)-s)) = Λ_L ε.
    have h_LL := left_annular_log_diff_local γ hL_L_ne h_deriv_left h_at
      hδL_pos hδL_r hr_pos h_window_Icc h_slit_L h_local_unique_r
    have h_RR := right_annular_log_diff_local γ hL_R_ne h_deriv_right h_at
      hδR_pos hδR_r hr_pos h_window_Icc h_slit_R h_local_unique_r
    have h_congr_L : ∫ t in (t₀ - r)..(t₀ - D.δ_left ε), integrand t =
        ∫ t in (t₀ - r)..(t₀ - D.δ_left ε), deriv γf t / (γf t - s) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [hI_def, hγf_def]
      rw [div_eq_mul_inv, mul_comm]
    have h_congr_R : ∫ t in (t₀ + D.δ_right ε)..(t₀ + r), integrand t =
        ∫ t in (t₀ + D.δ_right ε)..(t₀ + r), deriv γf t / (γf t - s) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [hI_def, hγf_def]
      rw [div_eq_mul_inv, mul_comm]
    rw [h_congr_L, h_congr_R, h_LL, h_RR]
  refine Tendsto.congr' h_eventually_eq.symm ?_
  -- Now show Λ_L ε + Λ_R ε → L_i.
  -- L_i = logNorm_diff + (argR_lim + argL_lim) · I.
  -- Λ_L ε = log((γ(t₀-δL)-s)/(γ(t₀-r)-s)), Λ_R ε = log((γ(t₀+r)-s)/(γ(t₀+δR)-s)).
  -- Re Λ_L ε = log ‖γ(t₀-δL)-s‖ - log ‖γ(t₀-r)-s‖ = log ε - log ‖γ(t₀-r)-s‖.
  -- Re Λ_R ε = log ‖γ(t₀+r)-s‖ - log ε.
  -- Sum: log ‖γ(t₀+r)-s‖ - log ‖γ(t₀-r)-s‖ = logNorm_diff. Real.log ε cancels!
  -- Im Λ_L ε = arg L, Im Λ_R ε = arg R.
  have h_decomp : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Λ_L ε + Λ_R ε = ((logNorm_diff : ℝ) : ℂ) +
        ((((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg +
          ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg : ℝ) : ℂ) * Complex.I := by
    filter_upwards [Ioo_mem_nhdsGT D.hthresh, hδR_lt_r, hδL_lt_r,
        hδR_pos_ev, hδL_pos_ev] with ε hε_thresh hδR_r hδL_r hδR_pos hδL_pos
    have hε_pos : 0 < ε := hε_thresh.1
    have hε_lt_thresh : ε < D.threshold := hε_thresh.2
    have h_eq_R : ‖γf (t₀ + D.δ_right ε) - s‖ = ε :=
      D.h_exit_right ε hε_pos hε_lt_thresh
    have h_eq_L : ‖γf (t₀ - D.δ_left ε) - s‖ = ε :=
      D.h_exit_left ε hε_pos hε_lt_thresh
    have h_γPlus_ne : γf (t₀ + r) - s ≠ 0 := by
      intro h_eq
      have : (t₀ + r) ∈ Set.Icc (t₀ - r) (t₀ + r) := Set.right_mem_Icc.mpr (by linarith)
      have ht_eq := h_local_unique_r _ this (sub_eq_zero.mp h_eq)
      linarith
    have h_γMinus_ne : γf (t₀ - r) - s ≠ 0 := by
      intro h_eq
      have : (t₀ - r) ∈ Set.Icc (t₀ - r) (t₀ + r) := Set.left_mem_Icc.mpr (by linarith)
      have ht_eq := h_local_unique_r _ this (sub_eq_zero.mp h_eq)
      linarith
    have h_γR_ne : γf (t₀ + D.δ_right ε) - s ≠ 0 := by
      rw [← norm_pos_iff, h_eq_R]; exact hε_pos
    have h_γL_ne : γf (t₀ - D.δ_left ε) - s ≠ 0 := by
      rw [← norm_pos_iff, h_eq_L]; exact hε_pos
    have h_log_R_decomp : Λ_R ε =
        ((Real.log ‖γf (t₀ + r) - s‖ - Real.log ‖γf (t₀ + D.δ_right ε) - s‖ : ℝ) : ℂ) +
        (((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg : ℂ) * Complex.I := by
      rw [hΛR_def]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, mul_zero, mul_one, Complex.ofReal_im, sub_zero, add_zero]
        rw [Complex.log_re, norm_div]
        rw [Real.log_div (norm_ne_zero_iff.mpr h_γPlus_ne) (norm_ne_zero_iff.mpr h_γR_ne)]
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, mul_one, Complex.ofReal_re, zero_add]
        rw [Complex.log_im]
        ring
    have h_log_L_decomp : Λ_L ε =
        ((Real.log ‖γf (t₀ - D.δ_left ε) - s‖ - Real.log ‖γf (t₀ - r) - s‖ : ℝ) : ℂ) +
        (((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg : ℂ) * Complex.I := by
      rw [hΛL_def]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, mul_zero, mul_one, Complex.ofReal_im, sub_zero, add_zero]
        rw [Complex.log_re, norm_div]
        rw [Real.log_div (norm_ne_zero_iff.mpr h_γL_ne) (norm_ne_zero_iff.mpr h_γMinus_ne)]
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, mul_one, Complex.ofReal_re, zero_add]
        rw [Complex.log_im]
        ring
    rw [h_log_L_decomp, h_log_R_decomp, h_eq_R, h_eq_L]
    simp only [hlogND_def]
    push_cast
    ring
  -- Use h_decomp to reduce convergence of Λ_L + Λ_R to convergence of arg parts.
  have h_decomp' : (fun ε : ℝ => ((logNorm_diff : ℝ) : ℂ) +
      ((((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg +
        ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg : ℝ) : ℂ) *
          Complex.I) =ᶠ[𝓝[>] (0 : ℝ)] (fun ε => Λ_L ε + Λ_R ε) := by
    filter_upwards [h_decomp] with ε hε
    exact hε.symm
  refine Tendsto.congr' h_decomp' ?_
  refine tendsto_const_nhds.add ?_
  have h_arg_sum : Tendsto (fun ε : ℝ =>
      ((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg +
        ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg)
      (𝓝[>] (0 : ℝ)) (𝓝 (argL_lim + argR_lim)) := by
    simpa [hargL_def, hargR_def] using h_arg_L_clean.add h_arg_R_clean
  have h_cast : Tendsto (fun ε : ℝ =>
      ((((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg +
          ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((argL_lim + argR_lim : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp h_arg_sum
  have h_mul_I : Tendsto (fun ε : ℝ =>
      ((((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg +
          ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg : ℝ) : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝 (((argL_lim + argR_lim : ℝ) : ℂ) * Complex.I)) :=
    h_cast.mul tendsto_const_nhds
  have h_target_eq : ((argL_lim + argR_lim : ℝ) : ℂ) * Complex.I =
      ((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [← h_target_eq]
  exact h_mul_I

/-- **Per-window cutoff integral converges**. Given local geometric data at
crossing `t_i`, the per-window cutoff integral
`∫_{[t_i - r, t_i + r]} cpvIntegrand (fun z => (z-s)⁻¹) γ s ε t dt`
tends to a finite limit as `ε → 0⁺`.

The limit is identified with
`logNorm_diff + (argR_lim + argL_lim) · I`
where `logNorm_diff = Real.log ‖γ(t_i + r) - s‖ - Real.log ‖γ(t_i - r) - s‖`
and the args are derivative-side arg limits.

This is a thin wrapper around `perCrossing_window_integral_tendsto_exact`:
it derives the slit-plane chord-quotient hypotheses via
`cpvFullSetup_local`, which produces a smaller output radius `r ≤ r₀`. For
the multi-crossing aggregation use case where every crossing must share the
SAME fixed radius, call `perCrossing_window_integral_tendsto_exact` directly. -/
theorem perCrossing_window_integral_tendsto
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    {r₀ : ℝ} (hr₀_pos : 0 < r₀)
    (h_window_in_unit : Set.Icc (t₀ - r₀) (t₀ + r₀) ⊆ Set.Icc (0 : ℝ) 1)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r₀) (t₀ + r₀),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∃ (r : ℝ) (_hr_pos : 0 < r) (_hr_le : r ≤ r₀) (L_i : ℂ),
      Tendsto (fun ε : ℝ =>
        ∫ t in (t₀ - r)..(t₀ + r),
          cpvIntegrand (fun z => (z - s)⁻¹)
            γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε t)
        (𝓝[>] (0 : ℝ)) (𝓝 L_i) := by
  obtain ⟨L_R, L_L, r, hL_R_ne, hL_L_ne, hr_pos, hr_le_r₀,
    h_deriv_right, h_deriv_left, h_slit_R, h_slit_L, h_γPlus_div_LR,
    h_LL_neg_div_γMinus⟩ :=
    cpvFullSetup_local γ ht₀ h_at hr₀_pos h_window_in_unit h_local_unique
  have h_window_sub : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (t₀ - r₀) (t₀ + r₀) :=
    Set.Icc_subset_Icc (by linarith) (by linarith)
  have h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1 :=
    h_window_sub.trans h_window_in_unit
  have h_local_unique_r : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀ :=
    fun t ht heq => h_local_unique t (h_window_sub ht) heq
  obtain ⟨L_i, hL_i⟩ :=
    perCrossing_window_integral_tendsto_exact γ ht₀ h_at hr_pos h_window_Icc
      h_local_unique_r hL_R_ne hL_L_ne h_deriv_right h_deriv_left
      h_slit_R h_slit_L h_γPlus_div_LR h_LL_neg_div_γMinus
  exact ⟨r, hr_pos, hr_le_r₀, L_i, hL_i⟩

/-! ### Multi-crossing CPV existence — generic form (T-BR-Y6d headline)

Given a closed piecewise-`C¹` immersion `γ` crossing the pole `s` at finitely
many parameters (the `crossings` finset, with completeness, off-partition and
interior properties), the cutoff integral `∫₀¹ cpvIntegrand((z-s)⁻¹) γ s ε`
converges as `ε → 0⁺`.

This is the multi-crossing analog of `hasCauchyPV_inv_sub_of_flat_one_full`
in the existence-only formulation: `∃ L : ℂ, HasCauchyPV ((z-s)⁻¹) γ s L`.

## Implementation status

The supporting infrastructure for the proof is complete and exposed in this file:

* `cpvFullSetup_local` — local derivative-limit/slit-plane setup at a single
  crossing using local uniqueness on a window rather than global uniqueness;
* `right_annular_log_diff_local`, `left_annular_log_diff_local` — FTC on
  local windows under local uniqueness;
* `LocalDerivedCutoffs.δ_right_tendsto_zero`, `δ_left_tendsto_zero` — the
  per-window exit-time cutoffs tend to `0⁺` as `ε → 0⁺`;
* `perCrossing_window_integral_tendsto` — per-window cutoff integral
  `∫_{[t_i - r, t_i + r]} cpvIntegrand(ε) dt` converges to a definite limit
  as `ε → 0⁺` (the per-crossing analytic core).

These pieces together discharge the analytic content at each crossing. The
final assembly to a global CPV existence statement (`∃ L, HasCauchyPV ...`)
requires the cross-window aggregation:

* split the cutoff integral over `[0, 1]` into a sum of per-window pieces
  (each converging by `perCrossing_window_integral_tendsto`) plus a constant
  smooth complement integral (well-defined since γ keeps positive distance
  from s outside the windows, by `h_complete` + compactness + continuity);
* combine using `Tendsto.add` and a finset-sum over crossings.

The aggregation requires careful integration over the smooth complement and
is performed in `Crossing.lean` (see `hasCauchyPV_inv_sub_multiCrossing_card_le_one`),
which has access to the `MultiPoleCrossData` structure. -/

/-! ### Smooth complement avoidance bound (T-BR-Y9)

For a finite set of disjoint windows `{[t_i - r, t_i + r] : i ∈ crossings}`
covering all crossings of γ at `s` (in the sense that `γ(t) = s → t ∈ crossings`),
the function `‖γ(t) - s‖` has a positive minimum on the **complement of the
union of open windows**. This is a corollary of compactness + continuity +
window-completeness: the complement is closed in `[0, 1]` (compact), and
`‖γ(t) - s‖ ≠ 0` everywhere on it (else `t` is a crossing, hence in the union).

This is the smooth-complement bound used for the cross-window aggregation
(T-BR-Y9). -/

/-- **Smooth complement positive bound** for a multi-crossing setup.

Given a finite set of crossings `crossings : Finset ℝ` (each in `Icc 0 1`,
with `γ(t) = s` only when `t ∈ crossings`), and a common radius function
`r_at : crossings → ℝ` with each `r_at t_i > 0`, the function `t ↦ ‖γ(t) - s‖`
has a positive minimum on the **closed complement** `[0, 1] \ ⋃_i (t_i - r_at t_i,
t_i + r_at t_i)`. -/
theorem multi_pole_smooth_complement_far_bound
    (γ : ClosedPwC1Immersion x) {s : ℂ}
    {crossings : Finset ℝ}
    (h_complete : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t ∈ crossings)
    (r_at : ℝ → ℝ) (hr_at_pos : ∀ t ∈ crossings, 0 < r_at t) :
    ∃ m : ℝ, 0 < m ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (∀ t_i ∈ crossings, t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)) →
        m ≤ ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ := by
  classical
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
    with hγf_def
  have hγ_cont : Continuous γf := by
    show Continuous (fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t)
    exact γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  -- The smooth complement: {t ∈ [0, 1] : t ∉ ⋃_i (t_i - r_at t_i, t_i + r_at t_i)}.
  set C : Set ℝ := {t ∈ Set.Icc (0 : ℝ) 1 |
    ∀ t_i ∈ crossings, t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)} with hC_def
  -- C is the intersection of [0, 1] with the complements of finitely many open
  -- intervals, hence closed in [0, 1], hence compact.
  have hC_subset : C ⊆ Set.Icc (0 : ℝ) 1 := fun t ht => ht.1
  -- C is closed (intersection of closed sets).
  have hC_closed : IsClosed C := by
    have h1 : IsClosed (Set.Icc (0 : ℝ) 1) := isClosed_Icc
    have h2 : IsClosed ({t : ℝ | ∀ t_i ∈ crossings,
        t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)}) := by
      have h_eq : {t : ℝ | ∀ t_i ∈ crossings,
            t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)} =
          ⋂ t_i ∈ crossings, (Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i))ᶜ := by
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
      rw [h_eq]
      refine isClosed_biInter ?_
      intro t_i _
      exact (isOpen_Ioo).isClosed_compl
    have hC_eq : C = Set.Icc (0 : ℝ) 1 ∩
        {t : ℝ | ∀ t_i ∈ crossings,
          t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)} := by
      ext t
      simp only [hC_def, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [hC_eq]
    exact h1.inter h2
  have hC_compact : IsCompact C :=
    isCompact_Icc.of_isClosed_subset hC_closed hC_subset
  -- C is nonempty: t = 0 if 0 ∉ ⋃ open windows; or take any boundary point.
  -- Actually, even if 0 is in a window, the LEFT endpoint of that window may be
  -- in C. Let's just take a concrete point. If 0 is not in any open window, done.
  -- Otherwise, pick the leftmost window left-endpoint that's in [0, 1].
  by_cases hC_empty : C = ∅
  · -- Vacuously true with m = 1 (or any positive).
    refine ⟨1, one_pos, ?_⟩
    intro t ht h_avoid
    exfalso
    have : t ∈ C := ⟨ht, h_avoid⟩
    rw [hC_empty] at this
    exact absurd this (Set.notMem_empty t)
  · have hC_nonempty : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_empty
    have h_norm_cont : ContinuousOn (fun t => ‖γf t - s‖) C :=
      ((hγ_cont.continuousOn).sub continuousOn_const).norm
    obtain ⟨t_min, ht_min_mem, ht_min⟩ :=
      hC_compact.exists_isMinOn hC_nonempty h_norm_cont
    refine ⟨‖γf t_min - s‖, ?_, ?_⟩
    · -- Positive: t_min ∈ C ⊆ [0, 1], and γ(t_min) ≠ s (else t_min ∈ crossings,
      -- so t_min ∈ (t_i - r_at t_i, t_i + r_at t_i) for t_i = t_min, contradicting
      -- t_min ∈ C).
      refine norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
      intro h_eq
      have h_t_min_in_01 : t_min ∈ Set.Icc (0 : ℝ) 1 := hC_subset ht_min_mem
      have h_t_min_in_crossings : t_min ∈ crossings :=
        h_complete t_min h_t_min_in_01 h_eq
      have h_t_min_avoid := ht_min_mem.2 t_min h_t_min_in_crossings
      have h_t_min_in_window : t_min ∈ Set.Ioo (t_min - r_at t_min)
          (t_min + r_at t_min) :=
        ⟨by linarith [hr_at_pos t_min h_t_min_in_crossings],
         by linarith [hr_at_pos t_min h_t_min_in_crossings]⟩
      exact h_t_min_avoid h_t_min_in_window
    · intro t ht h_avoid
      exact ht_min ⟨ht, h_avoid⟩

end HungerbuhlerWasem

end
