/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.BoundaryWinding
import LeanModularForms.ForMathlib.InteriorWinding
import LeanModularForms.ForMathlib.SmoothBoundaryWindingProof

/-!
# SmoothBoundaryWindingData for seg1 (right vertical edge)

At a point `z₀` strictly inside the right vertical edge of the FD boundary
(`z₀.re = 1/2`, `z₀.im ∈ (√3/2, H)`), we construct `SmoothBoundaryWindingData`
assuming the analytical `ArcFTCHyp` hypothesis is provided externally.

## Geometric setup

On seg1, `γ(t) = 1/2 + (H - K·t)·I` where `K = 5(H - √3/2)` is the vertical
speed. For `z₀ = 1/2 + c·I` with `c ∈ (√3/2, H)`, the crossing parameter is
`t₀ = (H - c)/K ∈ (0, 1/5)`, and the distance to `γ(t)` on seg1 is exactly
`‖γ(t) - z₀‖ = K·|t - t₀|`, giving the linear cutoff `δ(ε) = ε/K`.

## Main results

* `smoothBoundaryData_seg1_of_ftcHyp` -- constructs `SmoothBoundaryWindingData`
  at a generic smooth seg1 point from an external `ArcFTCHyp`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ### Parameters for seg1 -/

/-- Vertical speed on seg1: `K = 5(H - √3/2)`. Positive when `H > √3/2`. -/
def seg1Speed (H : ℝ) : ℝ := 5 * (H - Real.sqrt 3 / 2)

theorem seg1Speed_pos {H : ℝ} (hH : Real.sqrt 3 / 2 < H) : 0 < seg1Speed H := by
  unfold seg1Speed; linarith

/-- Crossing parameter on seg1 for the point `1/2 + c·I`:
`t₀ = (H - c) / seg1Speed H`. -/
def seg1T₀ (H c : ℝ) : ℝ := (H - c) / seg1Speed H

theorem seg1T₀_pos {H c : ℝ} (hH : Real.sqrt 3 / 2 < H) (hc : c < H) :
    0 < seg1T₀ H c :=
  div_pos (by linarith) (seg1Speed_pos hH)

theorem seg1T₀_lt_one_fifth {H c : ℝ}
    (hH : Real.sqrt 3 / 2 < H) (hc : Real.sqrt 3 / 2 < c) :
    seg1T₀ H c < 1/5 := by
  unfold seg1T₀ seg1Speed
  rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 5 * (H - Real.sqrt 3 / 2))]
  linarith

theorem seg1T₀_mem_Ioo {H c : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (hc_lo : Real.sqrt 3 / 2 < c) (hc_hi : c < H) :
    seg1T₀ H c ∈ Ioo (0 : ℝ) 1 :=
  ⟨seg1T₀_pos hH hc_hi,
    lt_trans (seg1T₀_lt_one_fifth hH hc_lo) (by norm_num : (1/5 : ℝ) < 1)⟩

/-! ### Distance formula on seg1 -/

/-- On seg1, the imaginary part of `fdBoundaryFun H t` is `H - (seg1Speed H)·t`. -/
private theorem fdBoundaryFun_seg1_im_speed (H t : ℝ) (ht : t ≤ 1/5) :
    (fdBoundaryFun H t).im = H - seg1Speed H * t := by
  rw [fdBoundaryFun_seg1_im H t ht]; unfold seg1Speed; ring

/-- For `z₀` on seg1 (i.e. `z₀.re = 1/2` and `z₀.im = c`), the distance from
`fdBoundaryFun H t` to `z₀` on seg1 equals `seg1Speed H · |t - seg1T₀ H c|`. -/
theorem fdBoundaryFun_seg1_dist_eq {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2) (t : ℝ) (ht : t ≤ 1/5) :
    ‖fdBoundaryFun H t - z₀‖ = seg1Speed H * |t - seg1T₀ H z₀.im| := by
  have hK_pos : 0 < seg1Speed H := seg1Speed_pos hH
  have h_re_zero : (fdBoundaryFun H t - z₀).re = 0 := by
    rw [sub_re, fdBoundaryFun_seg1_re H t ht, hz_re, sub_self]
  have h_im_eq : (fdBoundaryFun H t - z₀).im =
      seg1Speed H * (seg1T₀ H z₀.im - t) := by
    rw [sub_im, fdBoundaryFun_seg1_im_speed H t ht]
    unfold seg1T₀
    field_simp
    ring
  have h_norm : ‖fdBoundaryFun H t - z₀‖ = |(fdBoundaryFun H t - z₀).im| := by
    rw [Complex.norm_def, Complex.normSq_apply, h_re_zero, mul_zero, zero_add,
        show (fdBoundaryFun H t - z₀).im * (fdBoundaryFun H t - z₀).im
          = (fdBoundaryFun H t - z₀).im ^ 2 from by ring,
        Real.sqrt_sq_eq_abs]
  rw [h_norm, h_im_eq, abs_mul, abs_of_pos hK_pos, abs_sub_comm]

/-! ### Near bound -/

/-- `K · t₀ = H - z₀.im` for the seg1 crossing parameter. -/
private theorem seg1Speed_mul_t₀ {H c : ℝ} (hH : Real.sqrt 3 / 2 < H) :
    seg1Speed H * seg1T₀ H c = H - c := by
  have hK : seg1Speed H ≠ 0 := ne_of_gt (seg1Speed_pos hH)
  unfold seg1T₀; field_simp

/-- `K · (1/5 - t₀) = z₀.im - √3/2` for the seg1 crossing parameter. -/
private theorem seg1Speed_mul_one_fifth_sub_t₀ {H c : ℝ}
    (hH : Real.sqrt 3 / 2 < H) :
    seg1Speed H * (1/5 - seg1T₀ H c) = c - Real.sqrt 3 / 2 := by
  have h_over_five : seg1Speed H * (1/5) = H - Real.sqrt 3 / 2 := by
    unfold seg1Speed; ring
  rw [mul_sub, h_over_five, seg1Speed_mul_t₀ hH]
  ring

/-- Near bound on seg1: for `|t - t₀| ≤ ε/(seg1Speed H)` with `ε` small enough to keep
`t ∈ [0, 1/5]`, the distance is `≤ ε`. -/
theorem seg1_near_of_linDelta {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    {ε : ℝ} (hε_hi : ε < H - z₀.im)
    (hε_lo : ε < z₀.im - Real.sqrt 3 / 2)
    {t : ℝ} (ht : |t - seg1T₀ H z₀.im| ≤ ε / seg1Speed H) :
    ‖fdBoundaryFun H t - z₀‖ ≤ ε := by
  have hK_pos : 0 < seg1Speed H := seg1Speed_pos hH
  have h_t₀_lo : ε / seg1Speed H < seg1T₀ H z₀.im := by
    rw [div_lt_iff₀ hK_pos, mul_comm, seg1Speed_mul_t₀ hH]
    exact hε_hi
  have h_t₀_hi : ε / seg1Speed H < 1/5 - seg1T₀ H z₀.im := by
    rw [div_lt_iff₀ hK_pos, mul_comm, seg1Speed_mul_one_fifth_sub_t₀ hH]
    exact hε_lo
  have h_t_lo : 0 ≤ t := by linarith [(abs_le.mp ht).1]
  have h_t_hi : t ≤ 1/5 := by linarith [(abs_le.mp ht).2]
  rw [fdBoundaryFun_seg1_dist_eq hH hz_re t h_t_hi]
  calc seg1Speed H * |t - seg1T₀ H z₀.im|
      ≤ seg1Speed H * (ε / seg1Speed H) :=
        mul_le_mul_of_nonneg_left ht hK_pos.le
    _ = ε := by field_simp

/-! ### Off-seg1 uniform distance bounds -/

/-- For `z₀` on seg1 with `z₀.im > √3/2`, the norm `‖z₀‖` exceeds 1. -/
theorem norm_gt_one_of_seg1_interior {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) : 1 < ‖z₀‖ := by
  have h_nsq : 1 < Complex.normSq z₀ := by
    rw [Complex.normSq_apply, hz_re]
    have h_pow : (Real.sqrt 3 / 2) ^ 2 < z₀.im ^ 2 := by
      have h_nn : 0 ≤ Real.sqrt 3 / 2 := by positivity
      exact pow_lt_pow_left₀ hc_lo h_nn (by norm_num)
    have h_sqrt : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
    nlinarith
  have h_eq := Complex.normSq_eq_norm_sq z₀
  nlinarith [norm_nonneg z₀, h_eq]

/-- Distance from a seg1 interior point to seg2/seg3 (unit-circle arcs):
at least `‖z₀‖ - 1 > 0`. -/
theorem seg1_dist_arc {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) {H t : ℝ}
    (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    ‖z₀‖ - 1 ≤ ‖fdBoundaryFun H t - z₀‖ :=
  fdBoundaryFun_arc_dist (norm_gt_one_of_seg1_interior hz_re hc_lo) ht1 ht2

/-- Distance from a seg1 point to seg4 (left vertical): at least 1. -/
theorem seg1_dist_seg4 {z₀ : ℂ} (hz_re : z₀.re = 1/2) {H t : ℝ}
    (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    1 ≤ ‖fdBoundaryFun H t - z₀‖ := by
  have h1 := fdBoundaryFun_seg4_re H t ht3 ht4
  have hre : (fdBoundaryFun H t - z₀).re = -1 := by
    rw [sub_re, h1, hz_re]; norm_num
  calc (1 : ℝ) = |(-1 : ℝ)| := by norm_num
    _ = |(fdBoundaryFun H t - z₀).re| := by rw [hre]
    _ ≤ ‖fdBoundaryFun H t - z₀‖ := Complex.abs_re_le_norm _

/-- Distance from a seg1 interior point to seg5 (horizontal top): at least `H - z₀.im`. -/
theorem seg1_dist_seg5 {z₀ : ℂ} (hz_hi : z₀.im < H) {t : ℝ}
    (ht : 4/5 < t) : H - z₀.im ≤ ‖fdBoundaryFun H t - z₀‖ :=
  fdBoundaryFun_seg5_im_dist hz_hi ht

/-! ### Seg1 portion of the far bound -/

/-- Far bound on seg1: for `t ∈ [0, 1/5]` with `ε/(seg1Speed H) < |t - t₀|`,
the distance exceeds `ε`. -/
theorem seg1_far_on_seg1 {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    {ε : ℝ} {t : ℝ} (ht : t ≤ 1/5)
    (hδt : ε / seg1Speed H < |t - seg1T₀ H z₀.im|) :
    ε < ‖fdBoundaryFun H t - z₀‖ := by
  have hK_pos : 0 < seg1Speed H := seg1Speed_pos hH
  rw [fdBoundaryFun_seg1_dist_eq hH hz_re t ht]
  have : seg1Speed H * (ε / seg1Speed H) < seg1Speed H * |t - seg1T₀ H z₀.im| :=
    mul_lt_mul_of_pos_left hδt hK_pos
  have h_eq : seg1Speed H * (ε / seg1Speed H) = ε := by field_simp
  linarith

/-! ### Arc bound dominates the width bound -/

/-- For `z₀` on seg1 with `z₀.im > √3/2`, the arc-distance bound `‖z₀‖ - 1`
is at most the vertical-width bound `z₀.im - √3/2`. This lets us drop one of
the constraints in the threshold computation. -/
theorem norm_sub_one_le_im_sub_sqrt3 {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 ≤ z₀.im) :
    ‖z₀‖ - 1 ≤ z₀.im - Real.sqrt 3 / 2 := by
  have h_norm_sq : ‖z₀‖ ^ 2 = 1/4 + z₀.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hz_re]; ring
  have h_sqrt3 : Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 3/4 := by
    rw [show Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = (Real.sqrt 3 / 2) ^ 2 from by ring,
        div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]
    norm_num
  have h_nn := norm_nonneg z₀
  have h_sqrt3_lt_2 : Real.sqrt 3 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_nonneg 3]
  have h_nn_rhs : 0 ≤ z₀.im + 1 - Real.sqrt 3 / 2 := by linarith
  have h_sq_ineq : ‖z₀‖ ^ 2 ≤ (z₀.im + 1 - Real.sqrt 3 / 2) ^ 2 := by
    rw [h_norm_sq]
    -- Need: 1/4 + z₀.im² ≤ (z₀.im + 1 - √3/2)²
    -- Equivalently: 1/4 ≤ 2 * z₀.im * (1 - √3/2) + (1 - √3/2)²
    -- (1 - √3/2)² = 1 - √3 + 3/4 = 7/4 - √3
    -- So: 1/4 ≤ 2 * z₀.im * (1 - √3/2) + 7/4 - √3
    -- i.e., √3 - 3/2 ≤ 2 * z₀.im * (1 - √3/2) = z₀.im * (2 - √3)
    -- Since z₀.im ≥ √3/2: z₀.im * (2 - √3) ≥ (√3/2) * (2 - √3) = √3 - 3/2 ✓
    have h_sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 :=
      Real.mul_self_sqrt (by norm_num : (3 : ℝ) ≥ 0)
    nlinarith [h_sqrt3_sq, hc_lo, h_sqrt3_lt_2]
  have h_target : ‖z₀‖ ≤ z₀.im + 1 - Real.sqrt 3 / 2 := by
    have h_sqrt_mono : Real.sqrt (‖z₀‖ ^ 2) ≤
        Real.sqrt ((z₀.im + 1 - Real.sqrt 3 / 2) ^ 2) :=
      Real.sqrt_le_sqrt h_sq_ineq
    rwa [Real.sqrt_sq h_nn, Real.sqrt_sq h_nn_rhs] at h_sqrt_mono
  linarith

/-! ### Threshold for ε bounds -/

/-- The threshold below which `ε` must lie for every near/far bound to hold
at a seg1 interior point `z₀`:
`min(‖z₀‖ - 1, 1, H - z₀.im)`. All three are positive. The arc bound
`‖z₀‖ - 1` dominates the seg1 vertical-width constraint `z₀.im - √3/2`. -/
def seg1Threshold (H : ℝ) (z₀ : ℂ) : ℝ :=
  min (min (‖z₀‖ - 1) 1) (H - z₀.im)

theorem seg1Threshold_pos {H : ℝ} {z₀ : ℂ}
    (hz_re : z₀.re = 1/2) (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H) :
    0 < seg1Threshold H z₀ := by
  unfold seg1Threshold
  refine lt_min (lt_min ?_ zero_lt_one) (by linarith)
  linarith [norm_gt_one_of_seg1_interior hz_re hc_lo]

/-! ### Combined far bound -/

/-- Far bound: for `t ∈ [0, 1]` outside the δ-window around `t₀`, the distance
to `z₀` exceeds `ε`. -/
theorem seg1_far_bound {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H)
    {ε : ℝ} (hε_lt : ε < seg1Threshold H z₀)
    {t : ℝ} (_ht_mem : t ∈ Icc (0 : ℝ) 1)
    (hδt : ε / seg1Speed H < |t - seg1T₀ H z₀.im|) :
    ε < ‖fdBoundaryFun H t - z₀‖ := by
  have h_eps_arc : ε < ‖z₀‖ - 1 :=
    lt_of_lt_of_le hε_lt (le_trans (min_le_left _ _) (min_le_left _ _))
  have h_eps_one : ε < 1 :=
    lt_of_lt_of_le hε_lt (le_trans (min_le_left _ _) (min_le_right _ _))
  have h_eps_top : ε < H - z₀.im := lt_of_lt_of_le hε_lt (min_le_right _ _)
  by_cases h1 : t ≤ 1/5
  · exact seg1_far_on_seg1 hH hz_re h1 hδt
  push Not at h1
  by_cases h2 : t ≤ 3/5
  · calc ε < ‖z₀‖ - 1 := h_eps_arc
      _ ≤ ‖fdBoundaryFun H t - z₀‖ := seg1_dist_arc hz_re hc_lo h1 h2
  push Not at h2
  by_cases h3 : t ≤ 4/5
  · calc ε < 1 := h_eps_one
      _ ≤ ‖fdBoundaryFun H t - z₀‖ := seg1_dist_seg4 hz_re h2 h3
  push Not at h3
  calc ε < H - z₀.im := h_eps_top
    _ ≤ ‖fdBoundaryFun H t - z₀‖ := seg1_dist_seg5 hc_hi h3

/-! ### Main constructor: SmoothBoundaryWindingData on seg1 -/

/-- For a smooth seg1 point `z₀` (i.e. `z₀.re = 1/2`, `z₀.im ∈ (√3/2, H)`),
construct `SmoothBoundaryWindingData` from an external `ArcFTCHyp`. -/
def smoothBoundaryData_seg1_of_ftcHyp {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H)
    (ftcHyp : ArcFTCHyp γ z₀ (seg1T₀ H z₀.im) (linDelta (seg1Speed H))
      (seg1Threshold H z₀) (-(↑Real.pi * I))) :
    SmoothBoundaryWindingData γ z₀ where
  t₀ := seg1T₀ H z₀.im
  ht₀ := seg1T₀_mem_Ioo hH hc_lo hc_hi
  δ := linDelta (seg1Speed H)
  threshold := seg1Threshold H z₀
  hthresh := seg1Threshold_pos hz_re hc_lo hc_hi
  hδ_pos := fun _ hε _ => linDelta_pos (seg1Speed_pos hH) hε
  hδ_small := fun ε hε hε_thr => by
    have h_eps_top : ε < H - z₀.im :=
      lt_of_lt_of_le hε_thr (min_le_right _ _)
    have h_eps_arc : ε < ‖z₀‖ - 1 :=
      lt_of_lt_of_le hε_thr (le_trans (min_le_left _ _) (min_le_left _ _))
    have h_eps_width : ε < z₀.im - Real.sqrt 3 / 2 :=
      lt_of_lt_of_le h_eps_arc (norm_sub_one_le_im_sub_sqrt3 hz_re hc_lo.le)
    have h_lin_lt_t₀ : linDelta (seg1Speed H) ε < seg1T₀ H z₀.im := by
      unfold linDelta
      rw [div_lt_iff₀ (seg1Speed_pos hH), mul_comm, seg1Speed_mul_t₀ hH]
      exact h_eps_top
    have h_t₀_lt_half : seg1T₀ H z₀.im < 1 - seg1T₀ H z₀.im := by
      have := seg1T₀_lt_one_fifth hH hc_lo
      linarith
    exact lt_min h_lin_lt_t₀ (lt_trans h_lin_lt_t₀ h_t₀_lt_half)
  h_far := fun ε _ hε_thr t ht hδt => by
    rw [hγ t ht]
    exact seg1_far_bound hH hz_re hc_lo hc_hi hε_thr ht hδt
  h_near := fun ε hε hε_thr t ht => by
    have h_eps_top : ε < H - z₀.im :=
      lt_of_lt_of_le hε_thr (min_le_right _ _)
    have h_eps_arc : ε < ‖z₀‖ - 1 :=
      lt_of_lt_of_le hε_thr (le_trans (min_le_left _ _) (min_le_left _ _))
    have h_eps_width : ε < z₀.im - Real.sqrt 3 / 2 :=
      lt_of_lt_of_le h_eps_arc (norm_sub_one_le_im_sub_sqrt3 hz_re hc_lo.le)
    -- Need to transfer from γ.toPath.extend to fdBoundaryFun via hγ.
    have h_lin_lt_t₀ : linDelta (seg1Speed H) ε < seg1T₀ H z₀.im := by
      unfold linDelta
      rw [div_lt_iff₀ (seg1Speed_pos hH), mul_comm, seg1Speed_mul_t₀ hH]
      exact h_eps_top
    have h_lin_lt_one_fifth_sub : linDelta (seg1Speed H) ε < 1/5 - seg1T₀ H z₀.im := by
      unfold linDelta
      rw [div_lt_iff₀ (seg1Speed_pos hH), mul_comm, seg1Speed_mul_one_fifth_sub_t₀ hH]
      exact h_eps_width
    have h_t_lo : 0 ≤ t := by linarith [(abs_le.mp ht).1, seg1T₀_pos hH hc_hi]
    have h_t_hi : t ≤ 1 := by
      have : t ≤ seg1T₀ H z₀.im + linDelta (seg1Speed H) ε := by
        linarith [(abs_le.mp ht).2]
      linarith [seg1T₀_lt_one_fifth hH hc_lo]
    rw [hγ t ⟨h_t_lo, h_t_hi⟩]
    exact seg1_near_of_linDelta hH hz_re h_eps_top h_eps_width ht
  ftcHyp := ftcHyp

end

