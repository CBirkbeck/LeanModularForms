/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Exit-time function for curves crossing a point

For a curve `γ : ℝ → ℂ` with `γ(t₀) = s`, the **exit time at radius `ε`** is a
parameter `t_ε > t₀` such that `‖γ(t_ε) - s‖ = ε`. This file constructs the exit
time via the Intermediate Value Theorem and establishes its basic properties.

## Main results

* `exit_time_right_exists`: existence of `t_ε ∈ Ici t₀` with `‖γ(t_ε) - s‖ = ε`,
  given `γ` continuous on `[t₀, t₀ + δ]`, `γ(t₀) = s`, and the curve reaches
  distance ≥ ε within `[t₀, t₀ + δ]`.
* `exit_time_left_exists`: symmetric version on the left side.

## Phase 3 context

This lemma is foundational for HW Theorem 3.3 higher-order proof: at each
crossing of `γ` with a pole `s`, we excise the segment of `γ` inside the small
ball `B_ε(s)`, and replace it with a "connecting arc" on the boundary
`{|z - s| = ε}`. The exit time `t_ε` parameter where `γ` first leaves
`B_ε(s)` is the boundary of this excision.

By flatness of order `n` (Hungerbühler-Wasem condition (A)), the connecting
arc length is `o(ε^n)`, controlling the contribution of arcs in the limit.
-/

open Set Filter Topology

namespace LeanModularForms

/-- **Exit-time existence (right side).** Given `γ : ℝ → ℂ` continuous on
`[t₀, t₀ + δ]` with `γ(t₀) = s` and `‖γ(t₀ + δ) - s‖ ≥ ε`, there exists
`t_ε ∈ [t₀, t₀ + δ]` with `‖γ(t_ε) - s‖ = ε`.

Proof: apply IVT to `f(t) = ‖γ(t) - s‖`, which is continuous, has `f(t₀) = 0`
and `f(t₀ + δ) ≥ ε`, so `ε ∈ Icc (f t₀) (f (t₀ + δ))`. -/
theorem exit_time_right_exists
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ}
    {δ : ℝ} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s)
    {ε : ℝ} (hε_pos : 0 ≤ ε) (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    ∃ t_ε ∈ Icc t₀ (t₀ + δ), ‖γ t_ε - s‖ = ε := by
  have hf_cont : ContinuousOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + δ)) :=
    (hγ_cont.sub continuousOn_const).norm
  have h_ε_mem : ε ∈ Icc ‖γ t₀ - s‖ ‖γ (t₀ + δ) - s‖ := by
    simp [h_s, hε_pos, hε_le]
  exact intermediate_value_Icc (by linarith) hf_cont h_ε_mem

/-- **Exit-time existence (left side).** Given `γ : ℝ → ℂ` continuous on
`[t₀ - δ, t₀]` with `γ(t₀) = s` and `‖γ(t₀ - δ) - s‖ ≥ ε`, there exists
`t_ε ∈ [t₀ - δ, t₀]` with `‖γ(t_ε) - s‖ = ε`. -/
theorem exit_time_left_exists
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ}
    {δ : ℝ} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s)
    {ε : ℝ} (hε_pos : 0 ≤ ε) (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    ∃ t_ε ∈ Icc (t₀ - δ) t₀, ‖γ t_ε - s‖ = ε := by
  have hf_cont : ContinuousOn (fun t => ‖γ t - s‖) (Icc (t₀ - δ) t₀) :=
    (hγ_cont.sub continuousOn_const).norm
  have h_ε_mem : ε ∈ Icc ‖γ t₀ - s‖ ‖γ (t₀ - δ) - s‖ := by
    simp [h_s, hε_pos, hε_le]
  exact intermediate_value_Icc' (by linarith) hf_cont h_ε_mem

/-! ## First exit-time function via sInf

For `γ : ℝ → ℂ` with `γ(t₀) = s` and continuous on a right-neighborhood, the
**first exit time** at radius `ε` is the infimum of times `t ≥ t₀` for which
`‖γ(t) - s‖ ≥ ε`. This provides a default construction satisfying the
existence hypotheses needed by Phase 3 PV theorems. -/

/-- **First exit time at radius ε (right side).** Defined via `sInf` of the set
of times `t ∈ [t₀, t₀+δ]` with `‖γ(t) - s‖ ≥ ε`. Returns `t₀` as junk if the
set is empty.

Properties (under appropriate hypotheses, requiring monotonicity arguments):
- `‖γ (firstExitTimeRight ε) - s‖ = ε` when valid
- `firstExitTimeRight γ t₀ s δ ε ∈ Icc t₀ (t₀ + δ)`
- `Tendsto (firstExitTimeRight γ t₀ s δ) (𝓝[>] 0) (𝓝[>] t₀)` requires
  γ to enter B_ε within an arbitrarily small right-neighborhood of t₀
  (e.g., when γ has right-derivative L ≠ 0). -/
noncomputable def firstExitTimeRight (γ : ℝ → ℂ) (t₀ δ : ℝ) (s : ℂ) (ε : ℝ) : ℝ :=
  sInf {t ∈ Set.Icc t₀ (t₀ + δ) | ε ≤ ‖γ t - s‖}

/-- The set defining `firstExitTimeRight` is nonempty when `γ(t₀+δ)` is far enough. -/
theorem firstExitTimeRight_set_nonempty
    {γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ}
    (hδ : 0 ≤ δ) (h_far : ε ≤ ‖γ (t₀ + δ) - s‖) :
    (t₀ + δ) ∈ {t ∈ Set.Icc t₀ (t₀ + δ) | ε ≤ ‖γ t - s‖} :=
  ⟨⟨by linarith, le_rfl⟩, h_far⟩

/-- The set defining `firstExitTimeRight` is bounded below by t₀. -/
theorem firstExitTimeRight_set_lb
    (γ : ℝ → ℂ) (t₀ δ ε : ℝ) (s : ℂ) :
    ∀ t ∈ {t ∈ Set.Icc t₀ (t₀ + δ) | ε ≤ ‖γ t - s‖}, t₀ ≤ t :=
  fun _ ⟨hmem, _⟩ => hmem.1

/-- **First exit time lies in `[t₀, t₀+δ]`.** -/
theorem firstExitTimeRight_mem_Icc
    {γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} (hδ : 0 ≤ δ)
    (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    t₀ ≤ firstExitTimeRight γ t₀ δ s ε ∧
    firstExitTimeRight γ t₀ δ s ε ≤ t₀ + δ :=
  ⟨le_csInf ⟨t₀ + δ, firstExitTimeRight_set_nonempty hδ hε_le⟩
      (firstExitTimeRight_set_lb γ t₀ δ ε s),
    csInf_le ⟨t₀, firstExitTimeRight_set_lb γ t₀ δ ε s⟩
      (firstExitTimeRight_set_nonempty hδ hε_le)⟩

/-- **Radius lower bound at first exit time.** For γ continuous on `[t₀, t₀+δ]`
with `γ(t₀+δ)` at distance ≥ ε from s, the radius at the first exit time
satisfies `ε ≤ ‖γ (firstExitTimeRight ...) - s‖`.

This shows the first exit time IS an exit time (membership in S is preserved
at the infimum). -/
theorem ε_le_norm_at_firstExitTimeRight
    {γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ}
    (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Set.Icc t₀ (t₀ + δ)))
    (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    ε ≤ ‖γ (firstExitTimeRight γ t₀ δ s ε) - s‖ := by
  have h_S_closed : IsClosed
      (Set.Icc t₀ (t₀ + δ) ∩ (fun t => ‖γ t - s‖) ⁻¹' Set.Ici ε) :=
    (hγ_cont.sub continuousOn_const).norm.preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici
  have h_S_nonempty : ({t ∈ Set.Icc t₀ (t₀ + δ) | ε ≤ ‖γ t - s‖}).Nonempty :=
    ⟨t₀ + δ, firstExitTimeRight_set_nonempty hδ.le hε_le⟩
  have h_S_bdd : BddBelow {t ∈ Set.Icc t₀ (t₀ + δ) | ε ≤ ‖γ t - s‖} :=
    ⟨t₀, firstExitTimeRight_set_lb γ t₀ δ ε s⟩
  exact (h_S_closed.csInf_mem h_S_nonempty h_S_bdd).2

/-! ## Exact-radius equality at the first exit time -/

/-- **Strict-positive first exit time (right).** For `γ(t₀) = s` and `ε > 0`, the
first exit time is strictly `> t₀`: at `t₀` itself, `γ` is at distance `0 < ε`,
so `t₀` is not in the defining set. -/
theorem t₀_lt_firstExitTimeRight
    {γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Set.Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s) (hε_pos : 0 < ε)
    (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    t₀ < firstExitTimeRight γ t₀ δ s ε := by
  have h_cont_at_t₀ : ContinuousWithinAt (fun t => ‖γ t - s‖) (Set.Icc t₀ (t₀ + δ)) t₀ :=
    ((hγ_cont t₀ ⟨le_rfl, by linarith⟩).sub continuousWithinAt_const).norm
  have h_eventually : ∀ᶠ t in 𝓝[Set.Icc t₀ (t₀ + δ)] t₀, ‖γ t - s‖ < ε :=
    h_cont_at_t₀.tendsto.eventually_lt_const (by simp [h_s, hε_pos])
  obtain ⟨η, hη_pos, hη⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp h_eventually
  refine lt_of_lt_of_le (a := t₀) (b := t₀ + min η δ / 2) (by linarith [lt_min hη_pos hδ]) ?_
  refine le_csInf ⟨t₀ + δ, firstExitTimeRight_set_nonempty hδ.le hε_le⟩ ?_
  intro t ht
  by_contra! h_lt
  have h_in_Icc : t ∈ Set.Icc t₀ (t₀ + δ) := ht.1
  have h_dist_lt_η : dist t t₀ < η := by
    rw [Real.dist_eq, abs_of_nonneg (by linarith [h_in_Icc.1] : 0 ≤ t - t₀)]
    linarith [min_le_left η δ]
  exact absurd ht.2 (not_le.mpr (hη ⟨Metric.mem_ball.mpr h_dist_lt_η, h_in_Icc⟩))

/-- **Exact-radius equality at first exit time (right).** Combining the lower
bound `ε ≤ ‖γ (firstExitTime...) - s‖` with the upper bound from continuity at
the supremum-via-sInf, the first exit time is at *exactly* distance `ε`.

Requires `γ(t₀) = s` (so `firstExitTime > t₀`) and `ε > 0`. -/
theorem norm_at_firstExitTimeRight_eq
    {γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ}
    (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Set.Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s) (hε_pos : 0 < ε)
    (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    ‖γ (firstExitTimeRight γ t₀ δ s ε) - s‖ = ε := by
  refine le_antisymm ?_ (ε_le_norm_at_firstExitTimeRight hδ hγ_cont hε_le)
  set t_ε := firstExitTimeRight γ t₀ δ s ε
  have h_t₀_lt : t₀ < t_ε :=
    t₀_lt_firstExitTimeRight hδ hγ_cont h_s hε_pos hε_le
  have h_t_ε_mem : t_ε ∈ Set.Icc t₀ (t₀ + δ) :=
    (firstExitTimeRight_mem_Icc hδ.le hε_le)
  by_contra! h
  have h_cont_at_t_ε : ContinuousWithinAt (fun t => ‖γ t - s‖)
      (Set.Icc t₀ (t₀ + δ)) t_ε :=
    ((hγ_cont t_ε h_t_ε_mem).sub continuousWithinAt_const).norm
  have h_ev : ∀ᶠ t in 𝓝[Set.Icc t₀ (t₀ + δ)] t_ε, ε < ‖γ t - s‖ :=
    h_cont_at_t_ε.tendsto.eventually_const_lt h
  obtain ⟨η, hη_pos, hη⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp h_ev
  set r := min (η / 2) ((t_ε - t₀) / 2)
  have hr_pos : 0 < r := lt_min (by linarith) (by linarith)
  have h_t_in_Icc : t_ε - r ∈ Set.Icc t₀ (t₀ + δ) := by
    refine ⟨?_, by linarith [h_t_ε_mem.2]⟩
    linarith [min_le_right (η / 2) ((t_ε - t₀) / 2)]
  have h_dist : dist (t_ε - r) t_ε < η := by
    rw [Real.dist_eq, abs_of_neg (by linarith : t_ε - r - t_ε < 0)]
    linarith [min_le_left (η / 2) ((t_ε - t₀) / 2)]
  have h_norm_gt := hη ⟨Metric.mem_ball.mpr h_dist, h_t_in_Icc⟩
  have h_inf_le : t_ε ≤ t_ε - r :=
    csInf_le ⟨t₀, firstExitTimeRight_set_lb γ t₀ δ ε s⟩
      ⟨h_t_in_Icc, h_norm_gt.le⟩
  linarith

/-! ## First exit-time function (left side) via sSup -/

/-- **Last exit time at radius ε (left side).** Defined via `sSup` of the set
of times `t ∈ [t₀-δ, t₀]` with `‖γ(t) - s‖ ≥ ε`. Returns `t₀-δ` (or junk) when
the set is empty.

The left-side analog of `firstExitTimeRight`: as `t` increases toward `t₀`,
the curve approaches `s`, so the LATEST time in `[t₀-δ, t₀]` where `γ` is at
distance `≥ ε` is the supremum. This equals the "first" exit time when
approaching `t₀` from the left. -/
noncomputable def firstExitTimeLeft (γ : ℝ → ℂ) (t₀ δ : ℝ) (s : ℂ) (ε : ℝ) : ℝ :=
  sSup {t ∈ Set.Icc (t₀ - δ) t₀ | ε ≤ ‖γ t - s‖}

/-- The set defining `firstExitTimeLeft` is nonempty when `γ(t₀-δ)` is far enough. -/
theorem firstExitTimeLeft_set_nonempty
    {γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ}
    (hδ : 0 ≤ δ) (h_far : ε ≤ ‖γ (t₀ - δ) - s‖) :
    (t₀ - δ) ∈ {t ∈ Set.Icc (t₀ - δ) t₀ | ε ≤ ‖γ t - s‖} :=
  ⟨⟨le_rfl, by linarith⟩, h_far⟩

/-- The set defining `firstExitTimeLeft` is bounded above by `t₀`. -/
theorem firstExitTimeLeft_set_ub
    (γ : ℝ → ℂ) (t₀ δ ε : ℝ) (s : ℂ) :
    ∀ t ∈ {t ∈ Set.Icc (t₀ - δ) t₀ | ε ≤ ‖γ t - s‖}, t ≤ t₀ :=
  fun _ ⟨hmem, _⟩ => hmem.2

/-- **First exit time (left) lies in `[t₀-δ, t₀]`.** -/
theorem firstExitTimeLeft_mem_Icc
    {γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} (hδ : 0 ≤ δ)
    (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    t₀ - δ ≤ firstExitTimeLeft γ t₀ δ s ε ∧
    firstExitTimeLeft γ t₀ δ s ε ≤ t₀ :=
  ⟨le_csSup ⟨t₀, firstExitTimeLeft_set_ub γ t₀ δ ε s⟩
      (firstExitTimeLeft_set_nonempty hδ hε_le),
    csSup_le ⟨t₀ - δ, firstExitTimeLeft_set_nonempty hδ hε_le⟩
      (firstExitTimeLeft_set_ub γ t₀ δ ε s)⟩

/-- **Radius lower bound at first exit time (left).** For `γ` continuous on
`[t₀-δ, t₀]` with `γ(t₀-δ)` at distance ≥ ε from `s`, the radius at the (left)
first exit time satisfies `ε ≤ ‖γ (firstExitTimeLeft ...) - s‖`.

The closed-and-bounded set of "outside-the-ball" times has a supremum that
itself is "outside the ball" (closed under sequential limits). -/
theorem ε_le_norm_at_firstExitTimeLeft
    {γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ}
    (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Set.Icc (t₀ - δ) t₀))
    (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    ε ≤ ‖γ (firstExitTimeLeft γ t₀ δ s ε) - s‖ := by
  have h_S_closed : IsClosed
      (Set.Icc (t₀ - δ) t₀ ∩ (fun t => ‖γ t - s‖) ⁻¹' Set.Ici ε) :=
    (hγ_cont.sub continuousOn_const).norm.preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici
  have h_S_nonempty : ({t ∈ Set.Icc (t₀ - δ) t₀ | ε ≤ ‖γ t - s‖}).Nonempty :=
    ⟨t₀ - δ, firstExitTimeLeft_set_nonempty hδ.le hε_le⟩
  have h_S_bdd : BddAbove {t ∈ Set.Icc (t₀ - δ) t₀ | ε ≤ ‖γ t - s‖} :=
    ⟨t₀, firstExitTimeLeft_set_ub γ t₀ δ ε s⟩
  exact (h_S_closed.csSup_mem h_S_nonempty h_S_bdd).2

/-! ## Exact-radius equality at the first exit time (left side) -/

/-- **Strict-positive first exit time (left).** For `γ(t₀) = s` and `ε > 0`, the
left first exit time is strictly `< t₀`: at `t₀` itself, `γ` is at distance `0 < ε`,
so `t₀` is not in the defining set. -/
theorem firstExitTimeLeft_lt_t₀
    {γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Set.Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s) (hε_pos : 0 < ε)
    (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    firstExitTimeLeft γ t₀ δ s ε < t₀ := by
  have h_cont_at_t₀ : ContinuousWithinAt (fun t => ‖γ t - s‖) (Set.Icc (t₀ - δ) t₀) t₀ :=
    ((hγ_cont t₀ ⟨by linarith, le_rfl⟩).sub continuousWithinAt_const).norm
  have h_eventually : ∀ᶠ t in 𝓝[Set.Icc (t₀ - δ) t₀] t₀, ‖γ t - s‖ < ε :=
    h_cont_at_t₀.tendsto.eventually_lt_const (by simp [h_s, hε_pos])
  obtain ⟨η, hη_pos, hη⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp h_eventually
  refine lt_of_le_of_lt (a := firstExitTimeLeft γ t₀ δ s ε)
    (b := t₀ - min η δ / 2) ?_ (by linarith [lt_min hη_pos hδ])
  refine csSup_le ⟨t₀ - δ, firstExitTimeLeft_set_nonempty hδ.le hε_le⟩ ?_
  intro t ht
  by_contra! h_lt
  have h_in_Icc : t ∈ Set.Icc (t₀ - δ) t₀ := ht.1
  have h_dist_lt_η : dist t t₀ < η := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith [h_in_Icc.2] : t - t₀ ≤ 0)]
    linarith [min_le_left η δ]
  exact absurd ht.2 (not_le.mpr (hη ⟨Metric.mem_ball.mpr h_dist_lt_η, h_in_Icc⟩))

/-- **Exact-radius equality at first exit time (left).** Combining the lower
bound with the continuity-at-sSup upper bound, the (left) first exit time is at
*exactly* distance `ε`. -/
theorem norm_at_firstExitTimeLeft_eq
    {γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ}
    (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Set.Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s) (hε_pos : 0 < ε)
    (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    ‖γ (firstExitTimeLeft γ t₀ δ s ε) - s‖ = ε := by
  refine le_antisymm ?_ (ε_le_norm_at_firstExitTimeLeft hδ hγ_cont hε_le)
  set t_ε := firstExitTimeLeft γ t₀ δ s ε
  have h_t_ε_lt : t_ε < t₀ :=
    firstExitTimeLeft_lt_t₀ hδ hγ_cont h_s hε_pos hε_le
  have h_t_ε_mem : t_ε ∈ Set.Icc (t₀ - δ) t₀ :=
    (firstExitTimeLeft_mem_Icc hδ.le hε_le)
  by_contra! h
  have h_cont_at_t_ε : ContinuousWithinAt (fun t => ‖γ t - s‖)
      (Set.Icc (t₀ - δ) t₀) t_ε :=
    ((hγ_cont t_ε h_t_ε_mem).sub continuousWithinAt_const).norm
  have h_ev : ∀ᶠ t in 𝓝[Set.Icc (t₀ - δ) t₀] t_ε, ε < ‖γ t - s‖ :=
    h_cont_at_t_ε.tendsto.eventually_const_lt h
  obtain ⟨η, hη_pos, hη⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp h_ev
  set r := min (η / 2) ((t₀ - t_ε) / 2)
  have hr_pos : 0 < r := lt_min (by linarith) (by linarith)
  have h_t_in_Icc : t_ε + r ∈ Set.Icc (t₀ - δ) t₀ := by
    refine ⟨by linarith [h_t_ε_mem.1], ?_⟩
    linarith [min_le_right (η / 2) ((t₀ - t_ε) / 2)]
  have h_dist : dist (t_ε + r) t_ε < η := by
    rw [Real.dist_eq, abs_of_pos (by linarith : 0 < t_ε + r - t_ε)]
    linarith [min_le_left (η / 2) ((t₀ - t_ε) / 2)]
  have h_norm_gt := hη ⟨Metric.mem_ball.mpr h_dist, h_t_in_Icc⟩
  have h_sup_ge : t_ε + r ≤ t_ε :=
    le_csSup ⟨t₀, firstExitTimeLeft_set_ub γ t₀ δ ε s⟩
      ⟨h_t_in_Icc, h_norm_gt.le⟩
  linarith

/-! ## Continuity-derived modulus and basic asymptotic ingredients -/

/-- **Right-side continuity modulus.** For `γ : ℝ → ℂ` continuous on
`[t₀, t₀+δ]` with `γ(t₀) = s` and any `ε > 0`, there exists `η ∈ (0, δ)` such
that `‖γ t - s‖ < ε` for all `t ∈ [t₀, t₀+η]`. This is the `(ε, δ)` form of
continuity of `t ↦ ‖γ t - s‖` at `t₀`. -/
theorem exists_right_modulus
    {γ : ℝ → ℂ} {t₀ δ : ℝ} {s : ℂ} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Set.Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s) {ε : ℝ} (hε_pos : 0 < ε) :
    ∃ η ∈ Set.Ioc (0 : ℝ) δ, ∀ t ∈ Set.Icc t₀ (t₀ + η), ‖γ t - s‖ < ε := by
  have h_cont_at_t₀ : ContinuousWithinAt (fun t => ‖γ t - s‖) (Set.Icc t₀ (t₀ + δ)) t₀ :=
    ((hγ_cont t₀ ⟨le_rfl, by linarith⟩).sub continuousWithinAt_const).norm
  have h_eventually : ∀ᶠ t in 𝓝[Set.Icc t₀ (t₀ + δ)] t₀, ‖γ t - s‖ < ε :=
    h_cont_at_t₀.tendsto.eventually_lt_const (by simp [h_s, hε_pos])
  obtain ⟨η₀, hη₀_pos, hη₀⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp h_eventually
  refine ⟨min (η₀ / 2) (δ / 2), ⟨by positivity, min_le_of_right_le (by linarith)⟩, ?_⟩
  intro t ht
  refine hη₀ ⟨Metric.mem_ball.mpr ?_, ht.1, ?_⟩
  · rw [Real.dist_eq, abs_of_nonneg (by linarith [ht.1] : 0 ≤ t - t₀)]
    linarith [min_le_left (η₀ / 2) (δ / 2), ht.2]
  · linarith [min_le_right (η₀ / 2) (δ / 2), ht.2]

/-- **Left-side continuity modulus.** Symmetric to `exists_right_modulus`. -/
theorem exists_left_modulus
    {γ : ℝ → ℂ} {t₀ δ : ℝ} {s : ℂ} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Set.Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s) {ε : ℝ} (hε_pos : 0 < ε) :
    ∃ η ∈ Set.Ioc (0 : ℝ) δ, ∀ t ∈ Set.Icc (t₀ - η) t₀, ‖γ t - s‖ < ε := by
  have h_cont_at_t₀ : ContinuousWithinAt (fun t => ‖γ t - s‖) (Set.Icc (t₀ - δ) t₀) t₀ :=
    ((hγ_cont t₀ ⟨by linarith, le_rfl⟩).sub continuousWithinAt_const).norm
  have h_eventually : ∀ᶠ t in 𝓝[Set.Icc (t₀ - δ) t₀] t₀, ‖γ t - s‖ < ε :=
    h_cont_at_t₀.tendsto.eventually_lt_const (by simp [h_s, hε_pos])
  obtain ⟨η₀, hη₀_pos, hη₀⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp h_eventually
  refine ⟨min (η₀ / 2) (δ / 2), ⟨by positivity, min_le_of_right_le (by linarith)⟩, ?_⟩
  intro t ht
  refine hη₀ ⟨Metric.mem_ball.mpr ?_, ?_, ht.2⟩
  · rw [Real.dist_eq, abs_of_nonpos (by linarith [ht.2] : t - t₀ ≤ 0)]
    linarith [min_le_left (η₀ / 2) (δ / 2), ht.1]
  · linarith [min_le_right (η₀ / 2) (δ / 2), ht.1]

/-! ## Upper bounds: first exit time ≤ any witness in the defining set -/

/-- **Right-side upper bound.** For any `t₁ ∈ [t₀, t₀+δ]` with `ε ≤ ‖γ t₁ - s‖`,
the first exit time is at most `t₁`. -/
theorem firstExitTimeRight_le_of_mem
    {γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ}
    {t₁ : ℝ} (ht₁ : t₁ ∈ Set.Icc t₀ (t₀ + δ))
    (h_far : ε ≤ ‖γ t₁ - s‖) :
    firstExitTimeRight γ t₀ δ s ε ≤ t₁ :=
  csInf_le ⟨t₀, firstExitTimeRight_set_lb γ t₀ δ ε s⟩ ⟨ht₁, h_far⟩

/-- **Left-side lower bound.** For any `t₁ ∈ [t₀-δ, t₀]` with `ε ≤ ‖γ t₁ - s‖`,
the first exit time (sup) is at least `t₁`. -/
theorem firstExitTimeLeft_ge_of_mem
    {γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ}
    {t₁ : ℝ} (ht₁ : t₁ ∈ Set.Icc (t₀ - δ) t₀)
    (h_far : ε ≤ ‖γ t₁ - s‖) :
    t₁ ≤ firstExitTimeLeft γ t₀ δ s ε :=
  le_csSup ⟨t₀, firstExitTimeLeft_set_ub γ t₀ δ ε s⟩ ⟨ht₁, h_far⟩

/-! ## Monotonicity in `ε` (under nonemptiness witness) -/

/-- **First exit time (right) is monotone in `ε` when bounded by a witness.**
For `ε₁ ≤ ε₂` with `ε₂` reachable (i.e., `∃ t ∈ [t₀, t₀+δ]` with
`ε₂ ≤ ‖γ t - s‖`), `firstExitTimeRight ε₁ ≤ firstExitTimeRight ε₂`.

Larger excision radius → later first exit. The condition `ε ≤ ‖γ t - s‖` is
harder to satisfy for larger ε, so the defining set shrinks, and `sInf`
increases. -/
theorem firstExitTimeRight_mono_of_witness
    (γ : ℝ → ℂ) (t₀ δ : ℝ) (s : ℂ) {ε₁ ε₂ : ℝ} (h_le : ε₁ ≤ ε₂)
    (h_witness : ∃ t ∈ Set.Icc t₀ (t₀ + δ), ε₂ ≤ ‖γ t - s‖) :
    firstExitTimeRight γ t₀ δ s ε₁ ≤ firstExitTimeRight γ t₀ δ s ε₂ := by
  obtain ⟨t₂, ht₂_mem, ht₂_far⟩ := h_witness
  exact csInf_le_csInf ⟨t₀, firstExitTimeRight_set_lb γ t₀ δ ε₁ s⟩
    ⟨t₂, ht₂_mem, ht₂_far⟩
    fun _ ⟨hmem, h_far⟩ => ⟨hmem, h_le.trans h_far⟩

/-- **First exit time (left) is anti-monotone in `ε` under nonemptiness.**
Symmetric to the right-side: larger ε shrinks the set, so `sSup` decreases. -/
theorem firstExitTimeLeft_anti_of_witness
    (γ : ℝ → ℂ) (t₀ δ : ℝ) (s : ℂ) {ε₁ ε₂ : ℝ} (h_le : ε₁ ≤ ε₂)
    (h_witness : ∃ t ∈ Set.Icc (t₀ - δ) t₀, ε₂ ≤ ‖γ t - s‖) :
    firstExitTimeLeft γ t₀ δ s ε₂ ≤ firstExitTimeLeft γ t₀ δ s ε₁ := by
  obtain ⟨t₂, ht₂_mem, ht₂_far⟩ := h_witness
  exact csSup_le_csSup ⟨t₀, firstExitTimeLeft_set_ub γ t₀ δ ε₁ s⟩
    ⟨t₂, ht₂_mem, ht₂_far⟩
    fun _ ⟨hmem, h_far⟩ => ⟨hmem, h_le.trans h_far⟩

/-! ## Asymptotic: first exit time tends to `t₀` as `ε → 0⁺` -/

/-- **Right-side asymptotic.** For `γ` continuous on `[t₀, t₀+δ]` with `γ(t₀) = s`
and `γ(t) ≠ s` for `t ∈ (t₀, t₀+δ]`, the first exit time tends to `t₀` (from above)
as `ε → 0⁺`.

The "γ leaves the pole" hypothesis ensures the defining set is nonempty for
arbitrarily small ε, and convergence to `t₀` follows from continuity. -/
theorem firstExitTimeRight_tendsto_t₀
    {γ : ℝ → ℂ} {t₀ δ : ℝ} {s : ℂ} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Set.Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s)
    (h_leave : ∀ t ∈ Set.Ioc t₀ (t₀ + δ), γ t ≠ s) :
    Tendsto (fun ε => firstExitTimeRight γ t₀ δ s ε) (𝓝[>] 0) (𝓝[>] t₀) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro η hη_pos
    have hη_min : 0 < min η δ := lt_min hη_pos hδ
    set t₁ := t₀ + min η δ / 2 with ht₁_def
    have ht₁_mem : t₁ ∈ Set.Ioc t₀ (t₀ + δ) := by
      refine ⟨by linarith, ?_⟩
      have : min η δ ≤ δ := min_le_right _ _
      linarith
    have ht₁_ne : γ t₁ ≠ s := h_leave t₁ ht₁_mem
    refine ⟨‖γ t₁ - s‖, by simpa [norm_pos_iff, sub_ne_zero] using ht₁_ne, ?_⟩
    intro ε hε_pos hε_lt
    rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos] at hε_lt
    have h_t₁_mem_Icc : t₁ ∈ Set.Icc t₀ (t₀ + δ) := ⟨ht₁_mem.1.le, ht₁_mem.2⟩
    have h_inf_le : firstExitTimeRight γ t₀ δ s ε ≤ t₁ :=
      firstExitTimeRight_le_of_mem h_t₁_mem_Icc hε_lt.le
    have h_t₀_le : t₀ ≤ firstExitTimeRight γ t₀ δ s ε :=
      le_csInf ⟨t₁, h_t₁_mem_Icc, hε_lt.le⟩
        (firstExitTimeRight_set_lb γ t₀ δ ε s)
    rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ firstExitTimeRight γ t₀ δ s ε - t₀)]
    have h_t₁_diff : t₁ - t₀ < η := by
      simp only [ht₁_def]
      linarith [min_le_left η δ]
    linarith
  · have h_far_pos : (0 : ℝ) < ‖γ (t₀ + δ) - s‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (h_leave _ ⟨by linarith, le_rfl⟩))
    rw [eventually_iff_exists_mem]
    refine ⟨Set.Ioo 0 ‖γ (t₀ + δ) - s‖, Ioo_mem_nhdsGT h_far_pos, ?_⟩
    intro ε hε
    exact t₀_lt_firstExitTimeRight hδ hγ_cont h_s hε.1 hε.2.le

/-- **Left-side asymptotic.** Symmetric to `firstExitTimeRight_tendsto_t₀`:
the left first exit time tends to `t₀` (from below) as `ε → 0⁺`, given
`γ(t) ≠ s` for `t ∈ [t₀-δ, t₀)`. -/
theorem firstExitTimeLeft_tendsto_t₀
    {γ : ℝ → ℂ} {t₀ δ : ℝ} {s : ℂ} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Set.Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s)
    (h_leave : ∀ t ∈ Set.Ico (t₀ - δ) t₀, γ t ≠ s) :
    Tendsto (fun ε => firstExitTimeLeft γ t₀ δ s ε) (𝓝[>] 0) (𝓝[<] t₀) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro η hη_pos
    have hη_min : 0 < min η δ := lt_min hη_pos hδ
    set t₁ := t₀ - min η δ / 2 with ht₁_def
    have ht₁_mem : t₁ ∈ Set.Ico (t₀ - δ) t₀ := by
      refine ⟨?_, by linarith⟩
      have : min η δ ≤ δ := min_le_right _ _
      linarith
    have ht₁_ne : γ t₁ ≠ s := h_leave t₁ ht₁_mem
    refine ⟨‖γ t₁ - s‖, by simpa [norm_pos_iff, sub_ne_zero] using ht₁_ne, ?_⟩
    intro ε hε_pos hε_lt
    rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos] at hε_lt
    have h_t₁_mem_Icc : t₁ ∈ Set.Icc (t₀ - δ) t₀ := ⟨ht₁_mem.1, ht₁_mem.2.le⟩
    have h_inf_le : t₁ ≤ firstExitTimeLeft γ t₀ δ s ε :=
      firstExitTimeLeft_ge_of_mem h_t₁_mem_Icc hε_lt.le
    have h_t_le : firstExitTimeLeft γ t₀ δ s ε ≤ t₀ :=
      csSup_le ⟨t₁, h_t₁_mem_Icc, hε_lt.le⟩
        (firstExitTimeLeft_set_ub γ t₀ δ ε s)
    rw [Real.dist_eq, abs_of_nonpos
      (by linarith : firstExitTimeLeft γ t₀ δ s ε - t₀ ≤ 0)]
    have h_t₁_diff : t₀ - t₁ < η := by
      simp only [ht₁_def]
      linarith [min_le_left η δ]
    linarith
  · have h_far_pos : (0 : ℝ) < ‖γ (t₀ - δ) - s‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (h_leave _ ⟨le_rfl, by linarith⟩))
    rw [eventually_iff_exists_mem]
    refine ⟨Set.Ioo 0 ‖γ (t₀ - δ) - s‖, Ioo_mem_nhdsGT h_far_pos, ?_⟩
    intro ε hε
    exact firstExitTimeLeft_lt_t₀ hδ hγ_cont h_s hε.1 hε.2.le

/-! ## Eventual radius equality (matches parametric theorem signatures) -/

/-- **Right-side eventual exact radius.** For `γ` continuous with `γ(t₀) = s`
and `γ` leaving `s` on `(t₀, t₀+δ]`, the equality `‖γ (firstExitTimeRight ε) - s‖ = ε`
holds for all sufficiently small `ε > 0`. This is the form expected by
`hw_theorem_3_3_odd_transverse_parametric`. -/
theorem firstExitTimeRight_radius_eventually
    {γ : ℝ → ℂ} {t₀ δ : ℝ} {s : ℂ} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Set.Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s)
    (h_leave : ∀ t ∈ Set.Ioc t₀ (t₀ + δ), γ t ≠ s) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖γ (firstExitTimeRight γ t₀ δ s ε) - s‖ = ε := by
  have h_far_pos : (0 : ℝ) < ‖γ (t₀ + δ) - s‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (h_leave _ ⟨by linarith, le_rfl⟩))
  filter_upwards [Ioo_mem_nhdsGT h_far_pos] with ε hε
  exact norm_at_firstExitTimeRight_eq hδ hγ_cont h_s hε.1 hε.2.le

/-- **Left-side eventual exact radius.** Symmetric to the right-side. -/
theorem firstExitTimeLeft_radius_eventually
    {γ : ℝ → ℂ} {t₀ δ : ℝ} {s : ℂ} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Set.Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s)
    (h_leave : ∀ t ∈ Set.Ico (t₀ - δ) t₀, γ t ≠ s) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖γ (firstExitTimeLeft γ t₀ δ s ε) - s‖ = ε := by
  have h_far_pos : (0 : ℝ) < ‖γ (t₀ - δ) - s‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (h_leave _ ⟨le_rfl, by linarith⟩))
  filter_upwards [Ioo_mem_nhdsGT h_far_pos] with ε hε
  exact norm_at_firstExitTimeLeft_eq hδ hγ_cont h_s hε.1 hε.2.le

/-! ## Bundled exit-time data for HW Theorem 3.3 -/

/-- **Bundled exit-time data.** The four hypotheses on `t_eps_plus`/`t_eps_minus`
required by `hw_theorem_3_3_odd_transverse_parametric`, packaged as a single
structure. -/
structure HW33ExitData (γ : ℝ → ℂ) (t₀ : ℝ) (s : ℂ) where
  /-- Exit-time function on the right side. -/
  tPlus : ℝ → ℝ
  /-- Exit-time function on the left side. -/
  tMinus : ℝ → ℝ
  /-- `tPlus ε → t₀⁺` as `ε → 0⁺`. -/
  plus_to : Tendsto tPlus (𝓝[>] (0 : ℝ)) (𝓝[>] t₀)
  /-- Eventually, `‖γ(tPlus ε) - s‖ = ε`. -/
  plus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (tPlus ε) - s‖ = ε
  /-- `tMinus ε → t₀⁻` as `ε → 0⁺`. -/
  minus_to : Tendsto tMinus (𝓝[>] (0 : ℝ)) (𝓝[<] t₀)
  /-- Eventually, `‖γ(tMinus ε) - s‖ = ε`. -/
  minus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (tMinus ε) - s‖ = ε

/-- **Build `HW33ExitData` from `firstExitTimeRight` and `firstExitTimeLeft`.**
This is the canonical construction: given continuity of `γ` near `t₀` and the
"γ leaves `s` away from `t₀`" hypothesis on each side, the first-exit-time
functions provide all four asymptotic conditions. -/
noncomputable def HW33ExitData.ofExitTimes
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ}
    {δPlus δMinus : ℝ} (hδPlus : 0 < δPlus) (hδMinus : 0 < δMinus)
    (hγ_cont_right : ContinuousOn γ (Set.Icc t₀ (t₀ + δPlus)))
    (hγ_cont_left : ContinuousOn γ (Set.Icc (t₀ - δMinus) t₀))
    (h_s : γ t₀ = s)
    (h_leave_right : ∀ t ∈ Set.Ioc t₀ (t₀ + δPlus), γ t ≠ s)
    (h_leave_left : ∀ t ∈ Set.Ico (t₀ - δMinus) t₀, γ t ≠ s) :
    HW33ExitData γ t₀ s where
  tPlus := firstExitTimeRight γ t₀ δPlus s
  tMinus := firstExitTimeLeft γ t₀ δMinus s
  plus_to :=
    firstExitTimeRight_tendsto_t₀ hδPlus hγ_cont_right h_s h_leave_right
  plus_radius :=
    firstExitTimeRight_radius_eventually hδPlus hγ_cont_right h_s h_leave_right
  minus_to :=
    firstExitTimeLeft_tendsto_t₀ hδMinus hγ_cont_left h_s h_leave_left
  minus_radius :=
    firstExitTimeLeft_radius_eventually hδMinus hγ_cont_left h_s h_leave_left

end LeanModularForms
