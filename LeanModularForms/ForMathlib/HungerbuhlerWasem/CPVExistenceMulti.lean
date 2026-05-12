/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CPVExistence

/-!
# Multi-crossing CPV existence — geometric foundations (T-BR-Y6b)

This file builds the geometric foundations needed to extend
`hasCauchyPV_inv_sub_of_flat_one_full` (the single-crossing CPV existence
theorem in `CPVExistence.lean`) to handle a **finite set of transverse
crossings** on the same pole `s`.

## Setup

A "multi-crossing setup" consists of:
* `γ : ClosedPwC1Immersion x` — the curve;
* `s : ℂ` — the pole;
* `crossings : Finset ℝ` — the finite set of crossing parameters;
* `h_Ioo` — each crossing is in `Ioo 0 1`;
* `h_at` — `γ(t) = s` for each `t ∈ crossings`;
* `h_off` — each crossing is off the legacy partition;
* `h_complete` — every parameter where `γ = s` is in `crossings`.

For `card crossings ≤ 1`, the existing single-crossing infrastructure
applies directly (after handling avoidance separately). For `card ≥ 2`,
this file builds the supporting geometric scaffolding: common radius
`r > 0` ensuring per-crossing local uniqueness windows
`[t_i - r, t_i + r]` are pairwise disjoint, contained in `(0, 1)`, and
avoid all partition points.

## Main results

* `multi_pole_common_radius` — extracts a common `r > 0` from a multi-crossing
  setup satisfying the disjointness/interiority/partition-avoidance properties.
* `multi_pole_local_uniqueness` — on each window `[t_i - r, t_i + r]`, the only
  parameter mapping to `s` is `t_i` itself.

## Status

The local-uniqueness statements established here provide the geometric
foundation needed to apply per-crossing single-crossing CPV machinery in a
multi-crossing setting. The full multi-crossing CPV existence theorem (with
matching value `2πi · generalizedWindingNumber γ s`) requires additionally
adapting the analytic infrastructure (`exit_log_diff_tendsto`,
`cpvFullSetup`, etc.) to work with local rather than global uniqueness, and
then combining per-crossing contributions through telescoping. That adaptation
is a substantial undertaking (effectively rewriting the single-crossing proof
to take per-crossing local data); it is left as the next step, with the
oracle `h_multi_cpv` remaining as the user-facing hypothesis in
`residueTheorem_crossing_asymmetric_multiPole` (in `Crossing.lean`) until
that work is completed.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2 §3.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

/-! ### Geometric foundations: common radius from multi-crossing data -/

/-- **Pairwise minimum distance between elements of a finset**: for any finset
of reals with `card ≥ 2`, the minimum pairwise distance between distinct
elements is positive. -/
private theorem min_pairwise_distance_pos
    {crossings : Finset ℝ} (h_card_ge_two : 2 ≤ crossings.card) :
    ∃ d > 0, ∀ t₁ ∈ crossings, ∀ t₂ ∈ crossings, t₁ ≠ t₂ → d ≤ |t₁ - t₂| := by
  classical
  -- The pair-set of distinct elements is finite and nonempty.
  let pairs : Finset (ℝ × ℝ) :=
    (crossings ×ˢ crossings).filter (fun p => p.1 ≠ p.2)
  have hpairs_nonempty : pairs.Nonempty := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h_card_ge_two
    refine ⟨(a, b), ?_⟩
    simp only [pairs, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨ha, hb⟩, hab⟩
  obtain ⟨p_min, hp_min_mem, hp_min⟩ :=
    Finset.exists_min_image pairs (fun p => |p.1 - p.2|) hpairs_nonempty
  have hp_min_filt :
      p_min ∈ (crossings ×ˢ crossings).filter (fun p => p.1 ≠ p.2) := hp_min_mem
  rw [Finset.mem_filter, Finset.mem_product] at hp_min_filt
  refine ⟨|p_min.1 - p_min.2|, abs_pos.mpr (sub_ne_zero.mpr hp_min_filt.2), ?_⟩
  intro t₁ ht₁ t₂ ht₂ ht_ne
  have h_pair_mem : (t₁, t₂) ∈ pairs := by
    simp only [pairs, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨ht₁, ht₂⟩, ht_ne⟩
  exact hp_min (t₁, t₂) h_pair_mem

/-- **Lower bound on min(t, 1-t) over a nonempty finset of points in `Ioo 0 1`**.
For any nonempty finset of reals all lying in `Ioo 0 1`, there is `a > 0` such
that `a ≤ t` and `t ≤ 1 - a` for every `t` in the finset. -/
private theorem crossings_bounded_from_endpoints_finset
    {crossings : Finset ℝ} (h_nonempty : crossings.Nonempty)
    (h_Ioo : ∀ t ∈ crossings, t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ a > 0, ∀ t ∈ crossings, a ≤ t ∧ t ≤ 1 - a := by
  classical
  obtain ⟨t_min, ht_min_mem, ht_min⟩ :=
    Finset.exists_min_image crossings (fun t => min t (1 - t)) h_nonempty
  have h_t_min_Ioo := h_Ioo t_min ht_min_mem
  refine ⟨min t_min (1 - t_min),
    lt_min h_t_min_Ioo.1 (by linarith [h_t_min_Ioo.2]), ?_⟩
  intro t ht
  have h_ge := ht_min t ht
  refine ⟨le_trans h_ge (min_le_left _ _), ?_⟩
  have h_le_1mt := le_trans h_ge (min_le_right _ _)
  linarith

/-- **Lower bound on |t - p| over a nonempty finset of "off-partition" points**.
For any nonempty finset `crossings` of reals each disjoint from a finset
`partition` of reals, there is `b > 0` such that `b ≤ |t - p|` for every
`t ∈ crossings`, `p ∈ partition`. -/
private theorem crossings_bounded_from_partition_finset
    {crossings partition : Finset ℝ} (h_nonempty : crossings.Nonempty)
    (h_off : ∀ t ∈ crossings, t ∉ partition) :
    ∃ b > 0, ∀ t ∈ crossings, ∀ p ∈ partition, b ≤ |t - p| := by
  classical
  by_cases hP_empty : partition = ∅
  · refine ⟨1, one_pos, ?_⟩
    intro t _ p hp
    rw [hP_empty] at hp
    exact absurd hp (Finset.notMem_empty p)
  · have hP_nonempty : partition.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP_empty
    obtain ⟨p₀, hp₀⟩ := hP_nonempty
    obtain ⟨t₀, ht₀⟩ := h_nonempty
    let pairs : Finset (ℝ × ℝ) := crossings ×ˢ partition
    have hpairs_nonempty : pairs.Nonempty :=
      ⟨(t₀, p₀), Finset.mem_product.mpr ⟨ht₀, hp₀⟩⟩
    obtain ⟨q_min, hq_min_mem, hq_min⟩ :=
      Finset.exists_min_image pairs (fun q => |q.1 - q.2|) hpairs_nonempty
    have hq_min_prod : q_min ∈ crossings ×ˢ partition := hq_min_mem
    rw [Finset.mem_product] at hq_min_prod
    have hb_pos : 0 < |q_min.1 - q_min.2| := by
      apply abs_pos.mpr
      intro h_eq
      have h_eq' : q_min.1 = q_min.2 := sub_eq_zero.mp h_eq
      have h_t_off := h_off q_min.1 hq_min_prod.1
      rw [h_eq'] at h_t_off
      exact h_t_off hq_min_prod.2
    refine ⟨|q_min.1 - q_min.2|, hb_pos, ?_⟩
    intro t ht p hp
    have h_pair_mem : (t, p) ∈ pairs :=
      Finset.mem_product.mpr ⟨ht, hp⟩
    exact hq_min (t, p) h_pair_mem

/-! ### Common radius for multi-crossing geometric scaffolding -/

/-- **Common local-uniqueness radius** for a multi-crossing setup. Returns
`r > 0` such that for every `t_i ∈ crossings`:
- `t_i - r ≥ 0` and `t_i + r ≤ 1` (the window stays in `[0, 1]`);
- No other crossing `t_j ≠ t_i` lies in `[t_i - r, t_i + r]` (distinct
  windows are pairwise disjoint up to width `2r`);
- No partition point lies in `[t_i - r, t_i + r]` (each window avoids the
  legacy partition). -/
theorem multi_pole_common_radius
    {crossings partition : Finset ℝ}
    (h_nonempty : crossings.Nonempty)
    (h_Ioo : ∀ t ∈ crossings, t ∈ Set.Ioo (0 : ℝ) 1)
    (h_off : ∀ t ∈ crossings, t ∉ partition) :
    ∃ r > 0,
      (∀ t ∈ crossings, r ≤ t ∧ t ≤ 1 - r) ∧
      (∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t →
        2 * r < |t - t'|) ∧
      (∀ t ∈ crossings, ∀ p ∈ partition, r < |t - p|) := by
  classical
  obtain ⟨a, ha_pos, h_endpts⟩ :=
    crossings_bounded_from_endpoints_finset h_nonempty h_Ioo
  obtain ⟨b, hb_pos, h_part⟩ :=
    crossings_bounded_from_partition_finset h_nonempty h_off
  by_cases h_card_one : crossings.card = 1
  · -- Single crossing: pairwise condition is vacuously true.
    refine ⟨min a (b / 2),
      lt_min ha_pos (by linarith), ?_, ?_, ?_⟩
    · intro t ht
      have ⟨h1, _h2⟩ := h_endpts t ht
      have hr_le_a : min a (b / 2) ≤ a := min_le_left _ _
      refine ⟨le_trans hr_le_a h1, ?_⟩
      have := h_endpts t ht
      linarith [this.2, hr_le_a]
    · intro t ht t' ht' ht_ne
      rcases Finset.card_eq_one.mp h_card_one with ⟨c, hc⟩
      rw [hc, Finset.mem_singleton] at ht ht'
      exact absurd (ht'.trans ht.symm) ht_ne
    · intro t ht p hp
      have h_bd := h_part t ht p hp
      have hr_le : min a (b / 2) ≤ b / 2 := min_le_right _ _
      linarith
  · -- card ≥ 2: use the pairwise distance bound.
    have h_card_ge_two : 2 ≤ crossings.card := by
      have h_pos : 0 < crossings.card := Finset.card_pos.mpr h_nonempty
      omega
    obtain ⟨d, hd_pos, h_dist⟩ := min_pairwise_distance_pos h_card_ge_two
    refine ⟨min a (min (b / 2) (d / 4)),
      lt_min ha_pos (lt_min (by linarith) (by linarith)), ?_, ?_, ?_⟩
    · intro t ht
      have ⟨h1, _h2⟩ := h_endpts t ht
      have hr_le_a : min a (min (b / 2) (d / 4)) ≤ a := min_le_left _ _
      refine ⟨le_trans hr_le_a h1, ?_⟩
      have := h_endpts t ht
      linarith [this.2, hr_le_a]
    · intro t ht t' ht' ht_ne
      have h_d := h_dist t' ht' t ht ht_ne
      rw [abs_sub_comm] at h_d
      have hr_le_d_quart : min a (min (b / 2) (d / 4)) ≤ d / 4 :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
    · intro t ht p hp
      have h_bd := h_part t ht p hp
      have hr_le_b_half : min a (min (b / 2) (d / 4)) ≤ b / 2 :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      linarith

/-! ### Per-crossing local uniqueness from completeness -/

/-- **Per-crossing local uniqueness.** Given a common radius `r` from
`multi_pole_common_radius` (in particular satisfying interiority of windows
and pairwise disjointness) and the completeness assumption that every
parameter `t ∈ Icc 0 1` with `γ(t) = s` lies in `crossings`, the only
parameter `t ∈ Icc (t_i - r) (t_i + r)` with
`γ.toPiecewiseC1Path.toPath.extend t = s` is `t = t_i`. -/
theorem multi_pole_local_uniqueness
    (γ : ClosedPwC1Immersion x) {s : ℂ}
    {crossings : Finset ℝ} {r : ℝ} (hr_pos : 0 < r)
    (h_endpts : ∀ t ∈ crossings, r ≤ t ∧ t ≤ 1 - r)
    (h_pairwise : ∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t →
      2 * r < |t - t'|)
    (h_complete : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t ∈ crossings)
    {t_i : ℝ} (ht_i_mem : t_i ∈ crossings)
    {t : ℝ} (ht_in : t ∈ Set.Icc (t_i - r) (t_i + r))
    (h_eq : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s) :
    t = t_i := by
  classical
  have ⟨h_t_i_ge, h_t_i_le⟩ := h_endpts t_i ht_i_mem
  have h_t_in_01 : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [ht_in.1], by linarith [ht_in.2]⟩
  have h_t_cross : t ∈ crossings := h_complete t h_t_in_01 h_eq
  by_contra h_ne
  -- h_ne : ¬ t = t_i, so t ≠ t_i.
  have h_ne' : t ≠ t_i := h_ne
  -- h_pairwise t t_i requires `t_i ≠ t`, which is t ≠ t_i's symmetric form.
  have h_dist := h_pairwise t_i ht_i_mem t h_t_cross h_ne'
  have h_dist_le_r : |t_i - t| ≤ r := by
    rw [abs_sub_comm, abs_le]
    refine ⟨by linarith [ht_in.1], by linarith [ht_in.2]⟩
  linarith [hr_pos]

/-! ### Localized far bound for multi-crossings -/

/-- **Localized far-bound from local uniqueness.** On the window `[t_i - r, t_i + r]`,
since the only parameter where γ = s is `t_i`, the distance `‖γ(t) - s‖` has a positive
minimum on each closed half-window `[t_i - r, t_i - r']` and `[t_i + r', t_i + r]`,
for any `0 < r' < r`. -/
theorem multi_pole_local_far_bound
    (γ : ClosedPwC1Immersion x) {s : ℂ}
    {t_i : ℝ} {r : ℝ} (hr_pos : 0 < r)
    (h_local_unique : ∀ t ∈ Set.Icc (t_i - r) (t_i + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t_i)
    {r' : ℝ} (hr'_pos : 0 < r') (hr'_le : r' ≤ r) :
    ∃ m : ℝ, 0 < m ∧
      (∀ t ∈ Set.Icc (t_i - r) (t_i - r'), m ≤ ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖) ∧
      (∀ t ∈ Set.Icc (t_i + r') (t_i + r), m ≤ ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖) := by
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  have hγ_cont : Continuous γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  have h_norm_cont : ContinuousOn (fun t => ‖γf t - s‖) (Set.univ : Set ℝ) :=
    ((hγ_cont.continuousOn).sub continuousOn_const).norm
  -- Left compact: Icc (t_i - r) (t_i - r').
  have h_left_compact : IsCompact (Set.Icc (t_i - r) (t_i - r')) := isCompact_Icc
  have h_left_nonempty : (Set.Icc (t_i - r) (t_i - r')).Nonempty :=
    ⟨t_i - r, ⟨le_rfl, by linarith⟩⟩
  obtain ⟨t_l, ht_l_mem, ht_l_min⟩ :=
    h_left_compact.exists_isMinOn h_left_nonempty
      (h_norm_cont.mono (Set.subset_univ _))
  set m_l := ‖γf t_l - s‖
  have h_t_l_in_window : t_l ∈ Set.Icc (t_i - r) (t_i + r) :=
    ⟨ht_l_mem.1, by linarith [ht_l_mem.2]⟩
  have h_t_l_ne_t_i : t_l ≠ t_i := by
    intro h_eq
    have : t_i ≤ t_i - r' := h_eq ▸ ht_l_mem.2
    linarith
  have hm_l_pos : 0 < m_l := by
    refine norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
    intro h_eq
    exact h_t_l_ne_t_i (h_local_unique t_l h_t_l_in_window h_eq)
  -- Right compact: Icc (t_i + r') (t_i + r).
  have h_right_compact : IsCompact (Set.Icc (t_i + r') (t_i + r)) := isCompact_Icc
  have h_right_nonempty : (Set.Icc (t_i + r') (t_i + r)).Nonempty :=
    ⟨t_i + r, ⟨by linarith, le_rfl⟩⟩
  obtain ⟨t_r, ht_r_mem, ht_r_min⟩ :=
    h_right_compact.exists_isMinOn h_right_nonempty
      (h_norm_cont.mono (Set.subset_univ _))
  set m_r := ‖γf t_r - s‖
  have h_t_r_in_window : t_r ∈ Set.Icc (t_i - r) (t_i + r) :=
    ⟨by linarith [ht_r_mem.1], ht_r_mem.2⟩
  have h_t_r_ne_t_i : t_r ≠ t_i := by
    intro h_eq
    have : t_i + r' ≤ t_i := h_eq ▸ ht_r_mem.1
    linarith
  have hm_r_pos : 0 < m_r := by
    refine norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
    intro h_eq
    exact h_t_r_ne_t_i (h_local_unique t_r h_t_r_in_window h_eq)
  refine ⟨min m_l m_r, lt_min hm_l_pos hm_r_pos, ?_, ?_⟩
  · intro t ht
    exact le_trans (min_le_left _ _) (ht_l_min ht)
  · intro t ht
    exact le_trans (min_le_right _ _) (ht_r_min ht)

/-! ### Status

The local-uniqueness and local-far-bound lemmas above provide the geometric
foundation needed to apply the single-crossing CPV existence machinery
(`hasCauchyPV_inv_sub_of_flat_one_full` in `CPVExistence.lean`) at each
crossing `t_i` of a multi-crossing setup. -/

/-! ### Reduction lemma: multi-crossings to single crossings on a window

A key observation: the existing single-crossing `hasCauchyPV_inv_sub_of_flat_one_full`
theorem requires `h_unique` on `Icc 0 1`. In a multi-crossing setup, this global
uniqueness fails. However, after restricting attention to a window `[t_i - r, t_i + r]`
around each crossing (where local uniqueness DOES hold), the theorem's strategy
(`cpvFullSetup` + per-crossing FTC + log-cancellation via `exit_log_diff_tendsto`)
applies in a localized form. -/

/-- **Window membership of a crossing.** Each crossing lies strictly inside its window. -/
theorem multi_pole_crossing_mem_window
    {t_i : ℝ} {r : ℝ} (hr_pos : 0 < r) :
    t_i ∈ Set.Ioo (t_i - r) (t_i + r) :=
  ⟨by linarith, by linarith⟩

/-- **Crossing parameter is in `Ioo 0 1` from window constraints.** -/
theorem multi_pole_crossing_in_Ioo
    {t_i : ℝ} {r : ℝ} (hr_pos : 0 < r) (h_ge : r ≤ t_i) (h_le : t_i ≤ 1 - r) :
    t_i ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨by linarith, by linarith⟩

/-! ### Path forward

The full discharge of the `h_multi_cpv` oracle in
`residueTheorem_crossing_asymmetric_multiPole` (in `Crossing.lean`) proceeds
along the following template:

1. **Per-crossing local data**: For each `t_i ∈ M.crossings`, use
   `multi_pole_local_uniqueness` to get local uniqueness on `[t_i - r, t_i + r]`.
2. **Per-crossing exit-time cutoffs**: Build `δ_left^i, δ_right^i : ℝ → ℝ` using
   the local strict-monotonicity / strict-antimonotonicity of `‖γ(t) - s‖`
   (which only requires the local derivative data, not global uniqueness;
   see `norm_sub_strictMonoOn_right` and `norm_sub_strictAntiOn_left` in
   `CrossingDataBuilder.lean`).
3. **Global cutoff function**: Combine the per-crossing cutoff functions
   `δ_•^i` into a single threshold `θ = min_i (θ_i)`, with the per-crossing
   data active inside each window. Outside the windows, `γ` stays a positive
   distance from `s` (by completeness of `M.crossings` + continuity +
   compactness).
4. **Cutoff integral decomposition**: For `ε < θ` small,
   `I(ε) = Σ_i [annular_i(ε)] + smooth_total`, where each `annular_i(ε)` is
   the integral over the ε-cutoff zone around `t_i`, and `smooth_total` is
   the constant integral over the smooth complement.
5. **Per-crossing convergence**: Apply `exit_log_diff_tendsto` at each `t_i`
   to get `annular_i(ε) → L_i` as `ε → 0⁺`. Each `L_i` corresponds to the
   local winding contribution at `t_i`.
6. **Total convergence**: `I(ε) → Σ_i L_i + smooth_total =: L`.
7. **Polar-part lift**: For higher-order polar parts (`coeff(s, k)` with `k ≥ 1`),
   apply the multi-crossing analog of
   `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB` (per-crossing
   vanishing under angle compatibility from condition (B), summed over
   crossings).

Steps 1-3 are dischargeable using the local-uniqueness lemmas above.
Steps 4-7 require careful bookkeeping of the cutoff integral decomposition
and sum-of-limits convergence (using `Tendsto.sum` over the crossings finset).

The total work is substantial (estimated ~800-1500 LOC) due to the volume of
analytic bookkeeping required, but the core strategy follows the existing
`hasCauchyPV_inv_sub_of_flat_one_full` proof template directly. -/

end HungerbuhlerWasem

end
