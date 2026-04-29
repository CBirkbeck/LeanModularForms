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

theorem segClamp_eq_left {s_j s_jp1 t : ℝ} (h : s_j ≤ s_jp1) (ht : t ≤ s_j) :
    segClamp s_j s_jp1 t = s_j := by
  unfold segClamp
  rw [min_eq_left (ht.trans h), max_eq_left ht]

theorem segClamp_eq_self {s_j s_jp1 t : ℝ} (ht_lo : s_j ≤ t) (ht_hi : t ≤ s_jp1) :
    segClamp s_j s_jp1 t = t := by
  unfold segClamp
  rw [min_eq_left ht_hi, max_eq_right ht_lo]

theorem segClamp_eq_right {s_j s_jp1 t : ℝ} (h : s_j ≤ s_jp1) (ht : s_jp1 ≤ t) :
    segClamp s_j s_jp1 t = s_jp1 := by
  unfold segClamp
  rw [min_eq_right ht, max_eq_right h]

/-- Helper: the segment ratio `(γ(clamp t) - w) / (γ s_j - w)`. -/
noncomputable def segRatio (γ : ℝ → ℂ) (w : ℂ) (s_j s_jp1 t : ℝ) : ℂ :=
  (γ (segClamp s_j s_jp1 t) - w) / (γ s_j - w)

theorem segRatio_eq_one_of_le {γ : ℝ → ℂ} {w : ℂ} {s_j s_jp1 t : ℝ}
    (h : s_j ≤ s_jp1) (ht : t ≤ s_j) (h_ne : γ s_j - w ≠ 0) :
    segRatio γ w s_j s_jp1 t = 1 := by
  unfold segRatio
  rw [segClamp_eq_left h ht, div_self h_ne]

theorem segRatio_eq_self_div {γ : ℝ → ℂ} {w : ℂ} {s_j s_jp1 t : ℝ}
    (ht_lo : s_j ≤ t) (ht_hi : t ≤ s_jp1) :
    segRatio γ w s_j s_jp1 t = (γ t - w) / (γ s_j - w) := by
  unfold segRatio
  rw [segClamp_eq_self ht_lo ht_hi]

theorem segRatio_eq_full {γ : ℝ → ℂ} {w : ℂ} {s_j s_jp1 t : ℝ}
    (h : s_j ≤ s_jp1) (ht : s_jp1 ≤ t) :
    segRatio γ w s_j s_jp1 t = (γ s_jp1 - w) / (γ s_j - w) := by
  unfold segRatio
  rw [segClamp_eq_right h ht]

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

/-- Combined: for partition with mesh < δ', `segRatio j t ∈ slitPlane`. -/
theorem segRatio_mem_slitPlane
    {γ : ℝ → ℂ} {w : ℂ} {δ' ρ : ℝ} (hρ_pos : 0 < ρ)
    (h_dist_lb : ∀ t ∈ Icc (0 : ℝ) 1, ρ ≤ ‖γ t - w‖)
    (h_unif : ∀ t s : ℝ, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      |t - s| < δ' → ‖γ t - γ s‖ < ρ / 2)
    {s_j s_jp1 : ℝ} (hsj : s_j ∈ Icc (0 : ℝ) 1) (hsjp1 : s_jp1 ∈ Icc (0 : ℝ) 1)
    (h_le : s_j ≤ s_jp1) (h_mesh : s_jp1 - s_j < δ') (t : ℝ) :
    segRatio γ w s_j s_jp1 t ∈ Complex.slitPlane :=
  mem_slitPlane_of_ball_one _
    (segRatio_mem_ball_one hρ_pos h_dist_lb h_unif hsj hsjp1 h_le h_mesh t)

/-! ### Telescoping product over a partition -/

/-- Telescoping product in `ℂ` over `Finset.range`. For `a : ℕ → ℂ` nonzero on
indices `0..k`, the product `∏ j ∈ range k, a (j+1)/a j = a k / a 0`. -/
private lemma prod_range_div_complex (a : ℕ → ℂ) (k : ℕ)
    (ha : ∀ j ≤ k, a j ≠ 0) :
    ∏ j ∈ Finset.range k, (a (j + 1) / a j) = a k / a 0 := by
  induction k with
  | zero => simp [div_self (ha 0 le_rfl)]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih (fun j hj => ha j (by omega)),
        div_mul_div_comm, mul_comm (a n) (a (n + 1)),
        mul_div_mul_right _ _ (ha n (by omega))]

/-- Telescoping product: for `t ∈ [s_k, s_{k+1}]` along a monotone partition
`s : ℕ → ℝ` of `[0,1]` with `s 0 = 0` and `γ(s_j) ≠ w` for `0 ≤ j ≤ N`, the
product `∏_{j < N} segRatio γ w (s j) (s (j+1)) t` collapses to
`(γ t - w) / (γ 0 - w)`.

This is the key identity making `Im(log)` of each `segRatio` add up to a
continuous argument lift of `t ↦ γ t - w`. -/
theorem prod_segRatio_telescope
    {γ : ℝ → ℂ} {w : ℂ} {N : ℕ} {s : ℕ → ℝ}
    (hs_zero : s 0 = 0) (hs_mono : Monotone s)
    (h_avoid : ∀ j ≤ N, γ (s j) - w ≠ 0)
    {t : ℝ} {k : ℕ} (hk : k < N) (hk_lo : s k ≤ t) (hk_hi : t ≤ s (k + 1)) :
    ∏ j ∈ Finset.range N, segRatio γ w (s j) (s (j + 1)) t = (γ t - w) / (γ 0 - w) := by
  -- Split range N = range (k+1) ∪ Ico (k+1) N
  rw [Finset.range_eq_Ico, ← Finset.prod_Ico_consecutive _ (Nat.zero_le (k + 1)) hk,
      ← Finset.range_eq_Ico]
  -- Tail Ico (k+1) N: each segRatio = 1
  have h_ico_eq_one : ∀ j ∈ Finset.Ico (k + 1) N,
      segRatio γ w (s j) (s (j + 1)) t = 1 := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    refine segRatio_eq_one_of_le (hs_mono (Nat.le_succ _)) ?_ (h_avoid j hj.2.le)
    exact hk_hi.trans (hs_mono hj.1)
  rw [Finset.prod_congr rfl h_ico_eq_one, Finset.prod_const_one, mul_one]
  -- Peel off middle term j = k from range (k+1)
  rw [Finset.prod_range_succ]
  -- Range k: each segRatio = (γ s_{j+1} - w) / (γ s_j - w) (full ratio)
  have h_range_k_eq : ∀ j ∈ Finset.range k,
      segRatio γ w (s j) (s (j + 1)) t = (γ (s (j + 1)) - w) / (γ (s j) - w) := by
    intro j hj
    rw [Finset.mem_range] at hj
    refine segRatio_eq_full (hs_mono (Nat.le_succ _)) ?_
    exact (hs_mono (Nat.succ_le_of_lt hj)).trans hk_lo
  rw [Finset.prod_congr rfl h_range_k_eq]
  -- Middle term: segRatio at index k = (γ t - w) / (γ s_k - w)
  rw [segRatio_eq_self_div hk_lo hk_hi]
  -- Apply telescoping lemma to range k product
  rw [prod_range_div_complex (fun j => γ (s j) - w) k
        (fun j hj => h_avoid j (hj.trans hk.le))]
  -- Use s 0 = 0 and cancel γ s_k - w
  rw [hs_zero, div_mul_div_comm, mul_comm (γ (s k) - w) (γ t - w),
      mul_div_mul_right _ _ (h_avoid k hk.le)]

/-! ### Continuous arg-lift summand (continued) -/

/-- Each summand in the telescoping arg-lift sum is continuous. -/
theorem continuousOn_im_log_segRatio {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1)) {w : ℂ} {δ' ρ : ℝ} (hρ_pos : 0 < ρ)
    (h_dist_lb : ∀ t ∈ Icc (0 : ℝ) 1, ρ ≤ ‖γ t - w‖)
    (h_unif : ∀ t s : ℝ, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      |t - s| < δ' → ‖γ t - γ s‖ < ρ / 2)
    {s_j s_jp1 : ℝ} (hsj : s_j ∈ Icc (0 : ℝ) 1) (hsjp1 : s_jp1 ∈ Icc (0 : ℝ) 1)
    (h_le : s_j ≤ s_jp1) (h_mesh : s_jp1 - s_j < δ') :
    ContinuousOn (fun t => (Complex.log (segRatio γ w s_j s_jp1 t)).im)
      (Icc (0 : ℝ) 1) := by
  refine Complex.continuous_im.comp_continuousOn ?_
  exact (continuousOn_segRatio hγ hsj hsjp1 h_le).clog
    fun t _ => segRatio_mem_slitPlane hρ_pos h_dist_lb h_unif hsj hsjp1 h_le h_mesh t

/-! ### Helper: `exp(I · Im(log z)) = z / ‖z‖` -/

/-- For a nonzero complex number `z`, `exp(I · Im(log z)) = z / ↑‖z‖`. -/
private lemma exp_I_log_im_eq_div_norm {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (Complex.I * ((Complex.log z).im : ℂ)) = z / (‖z‖ : ℂ) := by
  have h_norm_pos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have h_split : Complex.I * ((Complex.log z).im : ℂ) =
      Complex.log z - ((Complex.log z).re : ℂ) := by
    rw [mul_comm, eq_sub_iff_add_eq, add_comm]
    exact Complex.re_add_im (Complex.log z)
  rw [h_split, Complex.exp_sub, Complex.exp_log hz, Complex.log_re,
      ← Complex.ofReal_exp, Real.exp_log h_norm_pos]

/-! ### Partition-segment existence -/

/-- For a uniform partition `s_j = j/N` of `[0,1]` with `N > 0`, every `t ∈ [0,1]`
lies in some segment `[s_k, s_{k+1}]` with `k < N`. -/
private lemma partition_segment_exists {N : ℕ} (hN : 0 < N) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ k : ℕ, k < N ∧ (k : ℝ) / N ≤ t ∧ t ≤ ((k + 1 : ℕ) : ℝ) / N := by
  have hN_real : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h_tN_nn : 0 ≤ t * N := mul_nonneg ht.1 hN_real.le
  rcases lt_or_eq_of_le ht.2 with h_t_lt_1 | h_t_eq_1
  · refine ⟨⌊t * N⌋₊, ?_, ?_, ?_⟩
    · have h_tN_lt : t * N < N := by nlinarith
      exact_mod_cast lt_of_le_of_lt (Nat.floor_le h_tN_nn) h_tN_lt
    · rw [div_le_iff₀ hN_real]; exact_mod_cast Nat.floor_le h_tN_nn
    · rw [le_div_iff₀ hN_real]
      have h_lt : t * N < ⌊t * N⌋₊ + 1 := Nat.lt_floor_add_one _
      have h_cast : ((⌊t * N⌋₊ + 1 : ℕ) : ℝ) = (⌊t * N⌋₊ : ℝ) + 1 := by push_cast; ring
      rw [h_cast]; linarith
  · refine ⟨N - 1, Nat.sub_lt hN zero_lt_one, ?_, ?_⟩
    · have hNcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub hN, Nat.cast_one]
      rw [hNcast, h_t_eq_1, div_le_one hN_real]; linarith
    · have h_eq : ((N - 1 + 1 : ℕ) : ℝ) = (N : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hN
      rw [h_eq, div_self hN_real.ne']; exact ht.2

/-! ### Main theorem: continuous argument lift -/

/-- For a continuous curve `γ : ℝ → ℂ` on `[0,1]` avoiding a point `w`, there is a
continuous "argument lift" `θ : ℝ → ℝ` such that `γ(t) - w = ‖γ(t) - w‖ · exp(i θ(t))`
on `[0,1]`. -/
theorem exists_continuous_arg_lift_of_avoids
    {γ : ℝ → ℂ} {w : ℂ}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (h_avoid : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc (0 : ℝ) 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        γ t - w = (‖γ t - w‖ : ℂ) * Complex.exp (Complex.I * (θ t : ℂ)) := by
  -- Step 1: get uniform modulus
  obtain ⟨δ', hδ'_pos, ρ, hρ_pos, h_dist_lb, h_unif⟩ :=
    exists_uniform_modulus_avoiding hγ h_avoid
  -- Step 2: pick N : ℕ with 1/N < δ'
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ')
  have hN_pos : 0 < N := by
    have h0 : (0 : ℝ) ≤ 1 / δ' := div_nonneg zero_le_one hδ'_pos.le
    have : (0 : ℝ) < N := lt_of_le_of_lt h0 hN
    exact_mod_cast this
  have hN_real : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
  have hN_mesh : (1 : ℝ) / N < δ' := by
    rw [div_lt_iff₀ hN_real]
    rw [div_lt_iff₀ hδ'_pos] at hN
    linarith
  -- Step 3: define partition s : ℕ → ℝ
  set s : ℕ → ℝ := fun j => (j : ℝ) / N with hs_def
  have hs_zero : s 0 = 0 := by simp [hs_def]
  have hs_mono : Monotone s := fun a b hab =>
    div_le_div_of_nonneg_right (by exact_mod_cast hab) hN_real.le
  have hs_in : ∀ j, j ≤ N → s j ∈ Icc (0 : ℝ) 1 := by
    intro j hj
    refine ⟨div_nonneg (by exact_mod_cast Nat.zero_le j) hN_real.le, ?_⟩
    rw [div_le_one hN_real]; exact_mod_cast hj
  have hs_avoid : ∀ j ≤ N, γ (s j) - w ≠ 0 := fun j hj =>
    sub_ne_zero.mpr (h_avoid (s j) (hs_in j hj))
  have hs_mesh : ∀ j, s (j + 1) - s j = 1 / N := by
    intro j; simp only [hs_def]; push_cast; ring
  have hs_le : ∀ j, s j ≤ s (j + 1) := fun j => hs_mono (Nat.le_succ _)
  -- Step 4: define θ(t)
  let θ : ℝ → ℝ := fun t =>
    Complex.arg (γ 0 - w) +
      ∑ j ∈ Finset.range N, (Complex.log (segRatio γ w (s j) (s (j + 1)) t)).im
  refine ⟨θ, ?_, ?_⟩
  -- Step 5: continuity of θ
  · refine ContinuousOn.add continuousOn_const ?_
    refine continuousOn_finset_sum _ ?_
    intro j hj
    refine continuousOn_im_log_segRatio hγ hρ_pos h_dist_lb h_unif
      (hs_in j (Finset.mem_range.mp hj).le) (hs_in (j + 1) (Finset.mem_range.mp hj)) (hs_le j) ?_
    rw [hs_mesh j]; exact hN_mesh
  -- Step 6: lift property
  · intro t ht
    have h_avoid_t : γ t - w ≠ 0 := sub_ne_zero.mpr (h_avoid t ht)
    have h_avoid_0 : γ 0 - w ≠ 0 :=
      sub_ne_zero.mpr (h_avoid 0 ⟨le_refl _, zero_le_one⟩)
    -- Get segment index
    obtain ⟨k, hk_lt, hk_lo, hk_hi⟩ := partition_segment_exists hN_pos ht
    -- Convert hk_lo, hk_hi from explicit to s notation
    have hk_lo' : s k ≤ t := hk_lo
    have hk_hi' : t ≤ s (k + 1) := by
      simp only [hs_def]
      have : ((k + 1 : ℕ) : ℝ) / N = (↑(k + 1) : ℝ) / N := rfl
      exact hk_hi
    -- Apply telescoping product
    have h_telescope := prod_segRatio_telescope hs_zero hs_mono hs_avoid hk_lt hk_lo' hk_hi'
    -- segRatio at each j is in slitPlane (hence ≠ 0)
    have h_ratio_ne : ∀ j ∈ Finset.range N,
        segRatio γ w (s j) (s (j + 1)) t ≠ 0 := fun j hj =>
      Complex.slitPlane_ne_zero
        (segRatio_mem_slitPlane hρ_pos h_dist_lb h_unif
          (hs_in j (Finset.mem_range.mp hj).le)
          (hs_in (j + 1) (Finset.mem_range.mp hj))
          (hs_le j) (by rw [hs_mesh j]; exact hN_mesh) t)
    -- Multiply telescoping through: (γ 0 - w) * ∏ z_j = γ t - w
    have h_prod_eq : (γ 0 - w) *
        ∏ j ∈ Finset.range N, segRatio γ w (s j) (s (j + 1)) t = γ t - w := by
      rw [h_telescope, mul_div_cancel₀ _ h_avoid_0]
    -- Cast θ t to ℂ
    have h_theta_cast : ((θ t : ℝ) : ℂ) = (Complex.arg (γ 0 - w) : ℂ) +
        ∑ j ∈ Finset.range N,
          ((Complex.log (segRatio γ w (s j) (s (j + 1)) t)).im : ℂ) := by
      simp only [θ, Complex.ofReal_add, Complex.ofReal_sum]
    -- exp(I · θ t) splits as exp(I · arg(γ 0 - w)) * ∏ exp(I · (log z_j).im)
    have h_exp_split : Complex.exp (Complex.I * ((θ t : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (Complex.arg (γ 0 - w) : ℂ)) *
          ∏ j ∈ Finset.range N,
            Complex.exp (Complex.I *
              ((Complex.log (segRatio γ w (s j) (s (j + 1)) t)).im : ℂ)) := by
      rw [h_theta_cast, mul_add, Complex.exp_add, Finset.mul_sum, Complex.exp_sum]
    -- exp(I · arg(γ 0 - w)) = (γ 0 - w) / ↑‖γ 0 - w‖
    have h_arg : Complex.exp (Complex.I * (Complex.arg (γ 0 - w) : ℂ)) =
        (γ 0 - w) / ((‖γ 0 - w‖ : ℝ) : ℂ) := by
      rw [show (Complex.arg (γ 0 - w) : ℂ) = ((Complex.log (γ 0 - w)).im : ℂ) by
            rw [Complex.log_im]]
      exact exp_I_log_im_eq_div_norm h_avoid_0
    -- Each summand: exp(I · ↑(log z_j).im) = z_j / ↑‖z_j‖
    have h_z_eq : ∀ j ∈ Finset.range N,
        Complex.exp (Complex.I *
          ((Complex.log (segRatio γ w (s j) (s (j + 1)) t)).im : ℂ)) =
          segRatio γ w (s j) (s (j + 1)) t /
            ((‖segRatio γ w (s j) (s (j + 1)) t‖ : ℝ) : ℂ) :=
      fun j hj => exp_I_log_im_eq_div_norm (h_ratio_ne j hj)
    -- Norm side: ‖γ 0 - w‖ * ∏ ‖z_j‖ = ‖γ t - w‖
    have h_norm_prod_real : (‖γ 0 - w‖ : ℝ) *
        (∏ j ∈ Finset.range N, ‖segRatio γ w (s j) (s (j + 1)) t‖) = ‖γ t - w‖ := by
      rw [← Complex.norm_prod, ← norm_mul, h_prod_eq]
    -- ‖γ t - w‖ ≠ 0 in ℂ
    have h_norm_t_ne : ((‖γ t - w‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h_avoid_t)
    -- Combine
    rw [h_exp_split, h_arg, Finset.prod_congr rfl h_z_eq, Finset.prod_div_distrib,
        div_mul_div_comm, ← Complex.ofReal_prod, ← Complex.ofReal_mul,
        h_norm_prod_real, h_prod_eq, mul_div_cancel₀ _ h_norm_t_ne]
