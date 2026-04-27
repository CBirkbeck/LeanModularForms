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

/-! ### W-1 sketch (continuous arg lift, not yet implemented)

The continuous arg lift theorem to be proved next:

```
theorem Complex.exists_continuous_arg_lift_of_avoids
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1)) {w : ℂ}
    (h_avoid : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 1) ∧
      ∀ t ∈ Icc 0 1, γ t - w = (‖γ t - w‖ : ℂ) * Complex.exp (θ t * Complex.I)
```

**Proof outline (deferred):**

1. Use `exists_uniform_modulus_avoiding` (W-0) to get `δ', ρ > 0`.
2. Choose `N : ℕ` with `1 / N < δ'`. Partition `[0,1]` as `s_i = i/N`.
3. By W-0: on `[s_i, s_{i+1}]`, `‖γ t - γ s_i‖ < ρ/2 ≤ ‖γ s_i - w‖/2`,
   so `(γ t - w) / (γ s_i - w) ∈ ball(1, 1/2) ⊆ Complex.slitPlane`
   (by `mem_slitPlane_of_ball_one`).
4. Define `θ(s_i)` recursively: `θ(s_0) := 0`,
   `θ(s_{i+1}) := θ(s_i) + (Complex.log ((γ s_{i+1} - w) / (γ s_i - w))).im`.
5. For `t ∈ [s_i, s_{i+1}]`, set
   `θ(t) := θ(s_i) + (Complex.log ((γ t - w) / (γ s_i - w))).im`.
6. Continuity of `θ`: continuous on each segment via `Complex.continuousAt_log`
   (and the slit-plane containment), gluing at `s_{i+1}` by definition.
7. The lift property `γ(t) - w = ‖γ(t) - w‖ · exp(i θ(t))` follows from
   `Complex.exp_log` on each segment, plus induction over partition points.

Implementation deferred — substantial recursive construction. -/

end Complex

end
