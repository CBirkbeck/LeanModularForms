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
  -- Define f(t) = ‖γ(t) - s‖
  let f : ℝ → ℝ := fun t => ‖γ t - s‖
  have hf_cont : ContinuousOn f (Icc t₀ (t₀ + δ)) :=
    (hγ_cont.sub continuousOn_const).norm
  have h_t₀_le : t₀ ≤ t₀ + δ := by linarith
  -- f(t₀) = 0
  have h_f_t₀ : f t₀ = 0 := by
    simp only [f, h_s, sub_self, norm_zero]
  -- f(t₀ + δ) ≥ ε
  have h_f_end : ε ≤ f (t₀ + δ) := hε_le
  -- IVT: ε ∈ Icc (f t₀) (f (t₀ + δ)) ⊆ f '' Icc t₀ (t₀ + δ)
  have h_ε_mem : ε ∈ Icc (f t₀) (f (t₀ + δ)) := by
    rw [h_f_t₀]
    exact ⟨hε_pos, h_f_end⟩
  have h_image := intermediate_value_Icc h_t₀_le hf_cont h_ε_mem
  obtain ⟨t_ε, ht_ε_mem, ht_ε_eq⟩ := h_image
  exact ⟨t_ε, ht_ε_mem, ht_ε_eq⟩

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
  let f : ℝ → ℝ := fun t => ‖γ t - s‖
  have hf_cont : ContinuousOn f (Icc (t₀ - δ) t₀) :=
    (hγ_cont.sub continuousOn_const).norm
  have h_t₀_le : t₀ - δ ≤ t₀ := by linarith
  have h_f_t₀ : f t₀ = 0 := by simp only [f, h_s, sub_self, norm_zero]
  have h_f_start : ε ≤ f (t₀ - δ) := hε_le
  -- ε ∈ Icc (f t₀) (f (t₀ - δ)), use intermediate_value_Icc' (decreasing case)
  have h_ε_mem : ε ∈ Icc (f t₀) (f (t₀ - δ)) := by
    rw [h_f_t₀]; exact ⟨hε_pos, h_f_start⟩
  have h_image := intermediate_value_Icc' h_t₀_le hf_cont h_ε_mem
  obtain ⟨t_ε, ht_ε_mem, ht_ε_eq⟩ := h_image
  exact ⟨t_ε, ht_ε_mem, ht_ε_eq⟩

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
    (t₀ + δ) ∈ {t ∈ Set.Icc t₀ (t₀ + δ) | ε ≤ ‖γ t - s‖} := by
  refine ⟨⟨by linarith, le_refl _⟩, h_far⟩

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
    firstExitTimeRight γ t₀ δ s ε ≤ t₀ + δ := by
  unfold firstExitTimeRight
  refine ⟨?_, ?_⟩
  · apply le_csInf
    · exact ⟨t₀ + δ, firstExitTimeRight_set_nonempty hδ hε_le⟩
    · exact firstExitTimeRight_set_lb γ t₀ δ ε s
  · apply csInf_le
    · exact ⟨t₀, fun t ⟨hmem, _⟩ => hmem.1⟩
    · exact firstExitTimeRight_set_nonempty hδ hε_le

end LeanModularForms
