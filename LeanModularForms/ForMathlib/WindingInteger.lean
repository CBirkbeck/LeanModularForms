/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Continuous argument lift and integer-valued winding number

For a continuous curve `γ : ℝ → ℂ` avoiding a point `w`, the function
`t ↦ γ(t) - w` is continuous and never zero. We build a continuous "argument lift"
`θ : ℝ → ℝ` such that `γ(t) - w = ‖γ(t) - w‖ · exp(i θ(t))`.

For closed Lipschitz `γ` (with `γ(0) = γ(1)`), the difference `θ(1) - θ(0)` is
an integer multiple of `2π`, giving the integer-valuedness of the winding number.

## Main results

* `Complex.exists_continuous_arg_lift_of_avoids` — existence of continuous arg lift
  for `γ : ℝ → ℂ` continuous on `[0,1]` avoiding `w`.

## Strategy

The lift is built piecewise: choose a partition `0 = t₀ < ... < t_n = 1` fine enough
that each segment `γ([t_i, t_{i+1}]) - w` lies in a "rotated slitPlane" (a half-plane
disjoint from `{0}`). On each segment, use `Complex.log` to extract the argument,
adjusted by the running sum of previous segments' angles.
-/

open Set Filter Topology

noncomputable section

namespace Complex

/-! ### Partition lemma -/

/-- For a continuous function `γ : ℝ → ℂ` avoiding `w` on a compact interval, there
exists `δ > 0` such that on any sub-interval of length `< δ`, `γ` varies by less than
half the minimum distance to `w`. This gives a partition where each segment of
`γ - w` lies in a ball avoiding `0`. -/
theorem exists_uniform_modulus_avoiding {γ : ℝ → ℂ} {w : ℂ}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (h_avoid : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    ∃ δ' > 0, ∃ ρ > 0, (∀ t ∈ Icc (0 : ℝ) 1, ρ ≤ ‖γ t - w‖) ∧
      ∀ t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → |t - s| < δ' →
        ‖γ t - γ s‖ < ρ / 2 := by
  -- Step 1: get a positive lower bound ρ for ‖γ t - w‖
  have h_image_compact : IsCompact (γ '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hγ
  have h_image_nonempty : (γ '' Icc (0 : ℝ) 1).Nonempty :=
    ⟨γ 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩
  have h_w_not_mem : w ∉ γ '' Icc (0 : ℝ) 1 :=
    fun ⟨t, ht, heq⟩ => h_avoid t ht heq
  have hρ_pos : 0 < Metric.infDist w (γ '' Icc (0 : ℝ) 1) :=
    (h_image_compact.isClosed.notMem_iff_infDist_pos h_image_nonempty).mp h_w_not_mem
  set ρ := Metric.infDist w (γ '' Icc (0 : ℝ) 1)
  have h_dist_lb : ∀ t ∈ Icc (0 : ℝ) 1, ρ ≤ ‖γ t - w‖ := by
    intro t ht
    have h1 : Metric.infDist w (γ '' Icc (0 : ℝ) 1) ≤ dist w (γ t) :=
      Metric.infDist_le_dist_of_mem (mem_image_of_mem γ ht)
    rw [Complex.dist_eq, norm_sub_rev] at h1
    exact h1
  -- Step 2: by uniform continuity on compact, get δ' for variation < ρ/2
  have h_unif : UniformContinuousOn γ (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hγ
  rw [Metric.uniformContinuousOn_iff] at h_unif
  obtain ⟨δ', hδ'_pos, h_unif⟩ := h_unif (ρ / 2) (by linarith)
  refine ⟨δ', hδ'_pos, ρ, hρ_pos, h_dist_lb, ?_⟩
  intro t s ht hs h_dist
  rw [← Complex.dist_eq]
  exact h_unif t ht s hs (by rwa [Real.dist_eq])

/-! ### Slit-plane containment for small balls -/

/-- The closed ball of radius `1/2` around `1` is contained in `Complex.slitPlane`. -/
theorem mem_slitPlane_of_ball_one (z : ℂ) (hz : ‖z - 1‖ < 1 / 2) :
    z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have h_re : |(z - 1).re| ≤ ‖z - 1‖ := Complex.abs_re_le_norm _
  have h_re_eq : (z - 1).re = z.re - 1 := by simp
  rw [h_re_eq] at h_re
  have : |z.re - 1| < 1 / 2 := lt_of_le_of_lt h_re hz
  rw [abs_sub_lt_iff] at this
  linarith

/-! ### W-1 helpers (deferred main theorem)

The main `exists_continuous_arg_lift_of_avoids` theorem is deferred — it uses
the telescoping-sum approach with `Finset.sum` over `N` partition segments,
each contributing `Im(log(segRatio j t))` where `segRatio j t` lies in
`ball(1, 1/2) ⊆ slitPlane` by W-0 + `mem_slitPlane_of_ball_one`.

Helper definitions and theorems for this construction are below. -/

/-- Helper: clamp `t` to `[s_j, s_{j+1}]`. For partition segment `j`. -/
def segClamp (s_j s_jp1 t : ℝ) : ℝ := max s_j (min t s_jp1)

theorem segClamp_continuous (s_j s_jp1 : ℝ) :
    Continuous (segClamp s_j s_jp1) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem segClamp_mem_Icc (s_j s_jp1 t : ℝ) (h : s_j ≤ s_jp1) :
    segClamp s_j s_jp1 t ∈ Icc s_j s_jp1 := by
  refine ⟨le_max_left _ _, ?_⟩
  unfold segClamp
  rcases le_total t s_jp1 with ht | ht
  · simp only [min_eq_left ht]; exact max_le h ht
  · rw [min_eq_right ht, max_le_iff]; exact ⟨h, le_refl _⟩

/-- Helper: the segment ratio `(γ(clamp t) - w) / (γ s_j - w)`. -/
noncomputable def segRatio (γ : ℝ → ℂ) (w : ℂ) (s_j s_jp1 t : ℝ) : ℂ :=
  (γ (segClamp s_j s_jp1 t) - w) / (γ s_j - w)

/-- For partition with mesh < δ' and segments [s_j, s_{j+1}] of length ≤ mesh,
on the j-th segment, `γ(clamp t) - γ s_j` is small, so `segRatio j t ∈ ball(1, 1/2)`. -/
theorem segRatio_mem_ball_one
    {γ : ℝ → ℂ} {w : ℂ} {δ' ρ : ℝ} (hρ_pos : 0 < ρ)
    (h_dist_lb : ∀ t ∈ Icc (0 : ℝ) 1, ρ ≤ ‖γ t - w‖)
    (h_unif : ∀ t s : ℝ, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      |t - s| < δ' → ‖γ t - γ s‖ < ρ / 2)
    {s_j s_jp1 : ℝ} (hsj : s_j ∈ Icc (0 : ℝ) 1) (hsjp1 : s_jp1 ∈ Icc (0 : ℝ) 1)
    (h_le : s_j ≤ s_jp1) (h_mesh : s_jp1 - s_j < δ') (t : ℝ) :
    ‖segRatio γ w s_j s_jp1 t - 1‖ < 1 / 2 := by
  have h_clamp_mem : segClamp s_j s_jp1 t ∈ Icc s_j s_jp1 :=
    segClamp_mem_Icc s_j s_jp1 t h_le
  have h_clamp_in_01 : segClamp s_j s_jp1 t ∈ Icc (0 : ℝ) 1 :=
    ⟨le_trans hsj.1 h_clamp_mem.1, le_trans h_clamp_mem.2 hsjp1.2⟩
  have h_dist : |segClamp s_j s_jp1 t - s_j| < δ' := by
    have h_nn : 0 ≤ segClamp s_j s_jp1 t - s_j := by linarith [h_clamp_mem.1]
    rw [abs_of_nonneg h_nn]
    linarith [h_clamp_mem.2]
  have h_diff : ‖γ (segClamp s_j s_jp1 t) - γ s_j‖ < ρ / 2 :=
    h_unif _ _ h_clamp_in_01 hsj h_dist
  have h_lb : ρ ≤ ‖γ s_j - w‖ := h_dist_lb _ hsj
  have h_pos : 0 < ‖γ s_j - w‖ := lt_of_lt_of_le hρ_pos h_lb
  have h_ne : γ s_j - w ≠ 0 := norm_pos_iff.mp h_pos
  unfold segRatio
  have h_rewrite : (γ (segClamp s_j s_jp1 t) - w) / (γ s_j - w) - 1 =
      (γ (segClamp s_j s_jp1 t) - γ s_j) / (γ s_j - w) := by
    rw [div_sub_one h_ne, sub_sub_sub_cancel_right]
  rw [h_rewrite, norm_div, div_lt_iff₀ h_pos]
  calc ‖γ (segClamp s_j s_jp1 t) - γ s_j‖
      < ρ / 2 := h_diff
    _ ≤ ‖γ s_j - w‖ / 2 := by linarith
    _ = 1 / 2 * ‖γ s_j - w‖ := by ring

/-- Continuity of `t ↦ segRatio γ w s_j s_jp1 t` on `Icc (0 : ℝ) 1`. -/
theorem continuousOn_segRatio {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {w : ℂ} {s_j s_jp1 : ℝ} (hsj : s_j ∈ Icc (0 : ℝ) 1)
    (hsjp1 : s_jp1 ∈ Icc (0 : ℝ) 1) (h_le : s_j ≤ s_jp1) :
    ContinuousOn (fun t => segRatio γ w s_j s_jp1 t) (Icc (0 : ℝ) 1) := by
  unfold segRatio
  refine ContinuousOn.div_const ?_ _
  refine ContinuousOn.sub ?_ continuousOn_const
  refine hγ.comp (segClamp_continuous s_j s_jp1).continuousOn ?_
  intro t _
  exact ⟨le_trans hsj.1 (segClamp_mem_Icc s_j s_jp1 t h_le).1,
    le_trans (segClamp_mem_Icc s_j s_jp1 t h_le).2 hsjp1.2⟩

end Complex

end
