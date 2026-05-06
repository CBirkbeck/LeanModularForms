/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.BoundaryWindingSeg1Proof

/-!
# SmoothBoundaryWindingData for seg4 (left vertical edge)

Symmetric to seg1: at a point `z₀` strictly inside the left vertical edge
(`z₀.re = -1/2`, `z₀.im ∈ (√3/2, H)`), the linear cutoff `δ(ε) = ε/K` with
`K = seg1Speed H` gives the geometric data for `SmoothBoundaryWindingData`.

## Main results

* `smoothBoundaryData_seg4_of_ftcHyp` -- constructs `SmoothBoundaryWindingData`
  at a generic smooth seg4 point from an external `ArcFTCHyp`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ### Parameters for seg4 -/

/-- Crossing parameter on seg4 for the point `-1/2 + c·I`:
`t₀ = 3/5 + (c - √3/2) / seg1Speed H`. -/
def seg4T₀ (H c : ℝ) : ℝ := 3/5 + (c - Real.sqrt 3 / 2) / seg1Speed H

theorem seg4T₀_gt_three_fifths {H c : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (hc : Real.sqrt 3 / 2 < c) : 3/5 < seg4T₀ H c := by
  have : 0 < (c - Real.sqrt 3 / 2) / seg1Speed H :=
    div_pos (by linarith) (seg1Speed_pos hH)
  unfold seg4T₀
  linarith

theorem seg4T₀_lt_four_fifths {H c : ℝ} (hH : Real.sqrt 3 / 2 < H) (hc : c < H) :
    seg4T₀ H c < 4/5 := by
  have : (c - Real.sqrt 3 / 2) / seg1Speed H < 1/5 := by
    rw [div_lt_iff₀ (seg1Speed_pos hH)]
    unfold seg1Speed
    linarith
  unfold seg4T₀
  linarith

theorem seg4T₀_mem_Ioo {H c : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (hc_lo : Real.sqrt 3 / 2 < c) (hc_hi : c < H) :
    seg4T₀ H c ∈ Ioo (0 : ℝ) 1 :=
  ⟨(by norm_num : (0 : ℝ) < 3/5).trans (seg4T₀_gt_three_fifths hH hc_lo),
    (seg4T₀_lt_four_fifths hH hc_hi).trans (by norm_num : (4/5 : ℝ) < 1)⟩

/-! ### Distance formula on seg4 -/

/-- On seg4, the imaginary part of `fdBoundaryFun H t` is
`√3/2 + seg1Speed H · (t - 3/5)`. -/
private theorem fdBoundaryFun_seg4_im_speed (H t : ℝ)
    (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    (fdBoundaryFun H t).im = Real.sqrt 3 / 2 + seg1Speed H * (t - 3/5) := by
  have h : (fdBoundaryFun H t).im = Real.sqrt 3 / 2 + (5 * t - 3) * (H - Real.sqrt 3 / 2) := by
    simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
      show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
      ht4, ite_true, ite_false]
    simp [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, div_ofNat, neg_im]
  rw [h]
  unfold seg1Speed
  ring

/-- For `z₀` on seg4 (`z₀.re = -1/2` and `z₀.im = c`), the distance from
`fdBoundaryFun H t` to `z₀` on seg4 equals `seg1Speed H · |t - seg4T₀ H c|`. -/
theorem fdBoundaryFun_seg4_dist_eq {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2) {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    ‖fdBoundaryFun H t - z₀‖ = seg1Speed H * |t - seg4T₀ H z₀.im| := by
  have h_re_zero : (fdBoundaryFun H t - z₀).re = 0 := by
    rw [sub_re, fdBoundaryFun_seg4_re H t ht3 ht4, hz_re, sub_self]
  have h_im_eq : (fdBoundaryFun H t - z₀).im = seg1Speed H * (t - seg4T₀ H z₀.im) := by
    rw [sub_im, fdBoundaryFun_seg4_im_speed H t ht3 ht4]
    unfold seg4T₀
    field_simp [(seg1Speed_pos hH).ne']
    ring
  rw [Complex.norm_def, Complex.normSq_apply, h_re_zero, mul_zero, zero_add,
    ← sq, Real.sqrt_sq_eq_abs, h_im_eq, abs_mul, abs_of_pos (seg1Speed_pos hH)]

/-- `K · (t₀ - 3/5) = z₀.im - √3/2` for the seg4 crossing parameter. -/
theorem seg1Speed_mul_t₀_sub_three_fifths {H c : ℝ} (hH : Real.sqrt 3 / 2 < H) :
    seg1Speed H * (seg4T₀ H c - 3/5) = c - Real.sqrt 3 / 2 := by
  unfold seg4T₀
  field_simp [(seg1Speed_pos hH).ne']
  ring

/-- `K · (4/5 - t₀) = H - c` for the seg4 crossing parameter. -/
theorem seg1Speed_mul_four_fifths_sub_t₀ {H c : ℝ} (hH : Real.sqrt 3 / 2 < H) :
    seg1Speed H * (4/5 - seg4T₀ H c) = H - c := by
  unfold seg4T₀
  field_simp [(seg1Speed_pos hH).ne']
  unfold seg1Speed
  ring

/-! ### Near bound -/

/-- Near bound on seg4: for `|t - t₀| ≤ ε/K` with `ε` small enough to keep
`t ∈ [3/5, 4/5]`, the distance is `≤ ε`. -/
theorem seg4_near_of_linDelta {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    {ε : ℝ} (hε_hi : ε < H - z₀.im) (hε_lo : ε < z₀.im - Real.sqrt 3 / 2)
    {t : ℝ} (ht : |t - seg4T₀ H z₀.im| ≤ ε / seg1Speed H) :
    ‖fdBoundaryFun H t - z₀‖ ≤ ε := by
  have hK_pos : 0 < seg1Speed H := seg1Speed_pos hH
  have h_lo_gap : ε / seg1Speed H < seg4T₀ H z₀.im - 3/5 := by
    rw [div_lt_iff₀ hK_pos, mul_comm, seg1Speed_mul_t₀_sub_three_fifths hH]
    exact hε_lo
  have h_hi_gap : ε / seg1Speed H < 4/5 - seg4T₀ H z₀.im := by
    rw [div_lt_iff₀ hK_pos, mul_comm, seg1Speed_mul_four_fifths_sub_t₀ hH]
    exact hε_hi
  have h_t_lo : 3/5 < t := by linarith [(abs_le.mp ht).1]
  have h_t_hi : t ≤ 4/5 := by linarith [(abs_le.mp ht).2]
  rw [fdBoundaryFun_seg4_dist_eq hH hz_re h_t_lo h_t_hi]
  calc seg1Speed H * |t - seg4T₀ H z₀.im|
      ≤ seg1Speed H * (ε / seg1Speed H) := by gcongr
    _ = ε := by field_simp

/-! ### Seg4 portion of the far bound -/

/-- Far bound on seg4 itself: for `t ∈ (3/5, 4/5]` with `ε/K < |t - t₀|`. -/
theorem seg4_far_on_seg4 {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2) {ε t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5)
    (hδt : ε / seg1Speed H < |t - seg4T₀ H z₀.im|) :
    ε < ‖fdBoundaryFun H t - z₀‖ := by
  rw [fdBoundaryFun_seg4_dist_eq hH hz_re ht3 ht4]
  calc ε = seg1Speed H * (ε / seg1Speed H) :=
        (mul_div_cancel₀ _ (seg1Speed_pos hH).ne').symm
    _ < seg1Speed H * |t - seg4T₀ H z₀.im| := by
        gcongr
        exact seg1Speed_pos hH

/-! ### Off-seg4 distance bounds -/

/-- For `z₀` on seg4 with `z₀.im > √3/2`, the norm `‖z₀‖` exceeds 1. -/
theorem norm_gt_one_of_seg4_interior {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) : 1 < ‖z₀‖ := by
  have h_sq3 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num : (3 : ℝ) ≥ 0)
  have h_nsq : 1 < Complex.normSq z₀ := by
    rw [Complex.normSq_apply, hz_re]
    nlinarith [h_sq3, hc_lo, Real.sqrt_nonneg 3]
  nlinarith [Complex.normSq_eq_norm_sq z₀, norm_nonneg z₀]

/-- Seg4 version of `norm_sub_one_le_im_sub_sqrt3` (the proof is identical
since it only depends on `|z₀.re| = 1/2`). -/
theorem norm_sub_one_le_im_sub_sqrt3_seg4 {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    (hc_lo : Real.sqrt 3 / 2 ≤ z₀.im) :
    ‖z₀‖ - 1 ≤ z₀.im - Real.sqrt 3 / 2 := by
  have h_sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num : (3 : ℝ) ≥ 0)
  have h_nn_rhs : 0 ≤ z₀.im + 1 - Real.sqrt 3 / 2 := by
    nlinarith [h_sqrt3_sq, hc_lo, Real.sqrt_nonneg 3]
  have h_sq_ineq : ‖z₀‖ ^ 2 ≤ (z₀.im + 1 - Real.sqrt 3 / 2) ^ 2 := by
    have h_norm_sq : ‖z₀‖ ^ 2 = 1/4 + z₀.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hz_re]
      ring
    rw [h_norm_sq]
    nlinarith [h_sqrt3_sq, hc_lo]
  have h_target := Real.sqrt_le_sqrt h_sq_ineq
  rw [Real.sqrt_sq (norm_nonneg z₀), Real.sqrt_sq h_nn_rhs] at h_target
  linarith

/-- Distance from a seg4 interior point to seg2/seg3 (arcs): at least `‖z₀‖ - 1`. -/
theorem seg4_dist_arc {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) {H t : ℝ}
    (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    ‖z₀‖ - 1 ≤ ‖fdBoundaryFun H t - z₀‖ :=
  fdBoundaryFun_arc_dist (norm_gt_one_of_seg4_interior hz_re hc_lo) ht1 ht2

/-- Distance from a seg4 point to seg1 (right vertical): at least 1. -/
theorem seg4_dist_seg1 {z₀ : ℂ} (hz_re : z₀.re = -1/2) {H t : ℝ}
    (ht : t ≤ 1/5) : 1 ≤ ‖fdBoundaryFun H t - z₀‖ := by
  have hre : (fdBoundaryFun H t - z₀).re = 1 := by
    rw [sub_re, fdBoundaryFun_seg1_re H t ht, hz_re]
    norm_num
  calc (1 : ℝ) = |(fdBoundaryFun H t - z₀).re| := by
        rw [hre]
        norm_num
    _ ≤ ‖fdBoundaryFun H t - z₀‖ := Complex.abs_re_le_norm _

/-- Distance from a seg4 interior point to seg5: at least `H - z₀.im`. -/
theorem seg4_dist_seg5 {z₀ : ℂ} (hz_hi : z₀.im < H) {t : ℝ}
    (ht : 4/5 < t) : H - z₀.im ≤ ‖fdBoundaryFun H t - z₀‖ :=
  fdBoundaryFun_seg5_im_dist hz_hi ht

/-! ### Threshold -/

/-- Seg4 threshold, same shape as seg1. -/
def seg4Threshold (H : ℝ) (z₀ : ℂ) : ℝ :=
  min (min (‖z₀‖ - 1) 1) (H - z₀.im)

theorem seg4Threshold_pos {H : ℝ} {z₀ : ℂ}
    (hz_re : z₀.re = -1/2) (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H) :
    0 < seg4Threshold H z₀ := by
  unfold seg4Threshold
  refine lt_min (lt_min ?_ zero_lt_one) (by linarith)
  linarith [norm_gt_one_of_seg4_interior hz_re hc_lo]

/-! ### Combined far bound -/

/-- Far bound: for `t ∈ [0, 1]` outside the δ-window around `t₀`, the distance
to `z₀` exceeds `ε`. -/
theorem seg4_far_bound {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H)
    {ε : ℝ} (hε_lt : ε < seg4Threshold H z₀)
    {t : ℝ} (_ht_mem : t ∈ Icc (0 : ℝ) 1)
    (hδt : ε / seg1Speed H < |t - seg4T₀ H z₀.im|) :
    ε < ‖fdBoundaryFun H t - z₀‖ := by
  have h_eps_arc : ε < ‖z₀‖ - 1 :=
    hε_lt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h_eps_one : ε < 1 :=
    hε_lt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have h_eps_top : ε < H - z₀.im := hε_lt.trans_le (min_le_right _ _)
  rcases le_or_gt t (1/5) with h1 | h1
  · exact h_eps_one.trans_le (seg4_dist_seg1 hz_re h1)
  rcases le_or_gt t (3/5) with h2 | h2
  · exact h_eps_arc.trans_le (seg4_dist_arc hz_re hc_lo h1 h2)
  rcases le_or_gt t (4/5) with h3 | h3
  · exact seg4_far_on_seg4 hH hz_re h2 h3 hδt
  exact h_eps_top.trans_le (seg4_dist_seg5 hc_hi h3)

/-! ### Main constructor: SmoothBoundaryWindingData on seg4 -/

/-- For a smooth seg4 point `z₀` (i.e. `z₀.re = -1/2`, `z₀.im ∈ (√3/2, H)`),
construct `SmoothBoundaryWindingData` from an external `ArcFTCHyp`. -/
def smoothBoundaryData_seg4_of_ftcHyp {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H)
    (ftcHyp : ArcFTCHyp γ z₀ (seg4T₀ H z₀.im) (linDelta (seg1Speed H))
      (seg4Threshold H z₀) (-(↑Real.pi * I))) :
    SmoothBoundaryWindingData γ z₀ where
  t₀ := seg4T₀ H z₀.im
  ht₀ := seg4T₀_mem_Ioo hH hc_lo hc_hi
  δ := linDelta (seg1Speed H)
  threshold := seg4Threshold H z₀
  hthresh := seg4Threshold_pos hz_re hc_lo hc_hi
  hδ_pos := fun _ hε _ => linDelta_pos (seg1Speed_pos hH) hε
  hδ_small := fun ε _ hε_thr => by
    have h_eps_arc : ε < ‖z₀‖ - 1 :=
      hε_thr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have h_eps_width : ε < z₀.im - Real.sqrt 3 / 2 :=
      h_eps_arc.trans_le (norm_sub_one_le_im_sub_sqrt3_seg4 hz_re hc_lo.le)
    have h_eps_top : ε < H - z₀.im := hε_thr.trans_le (min_le_right _ _)
    have h_lin_lt_lo : linDelta (seg1Speed H) ε < seg4T₀ H z₀.im - 3/5 := by
      unfold linDelta
      rw [div_lt_iff₀ (seg1Speed_pos hH), mul_comm, seg1Speed_mul_t₀_sub_three_fifths hH]
      exact h_eps_width
    have h_lin_lt_hi : linDelta (seg1Speed H) ε < 4/5 - seg4T₀ H z₀.im := by
      unfold linDelta
      rw [div_lt_iff₀ (seg1Speed_pos hH), mul_comm, seg1Speed_mul_four_fifths_sub_t₀ hH]
      exact h_eps_top
    refine lt_min (by linarith) ?_
    linarith [show (1 : ℝ) - seg4T₀ H z₀.im = (4/5 - seg4T₀ H z₀.im) + 1/5 from by ring]
  h_far := fun _ _ hε_thr t ht hδt => by
    rw [hγ t ht]
    exact seg4_far_bound hH hz_re hc_lo hc_hi hε_thr ht hδt
  h_near := fun ε _ hε_thr t ht => by
    have h_eps_top : ε < H - z₀.im := hε_thr.trans_le (min_le_right _ _)
    have h_eps_arc : ε < ‖z₀‖ - 1 :=
      hε_thr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have h_eps_width : ε < z₀.im - Real.sqrt 3 / 2 :=
      h_eps_arc.trans_le (norm_sub_one_le_im_sub_sqrt3_seg4 hz_re hc_lo.le)
    have h_lin_lt_lo : linDelta (seg1Speed H) ε < seg4T₀ H z₀.im - 3/5 := by
      unfold linDelta
      rw [div_lt_iff₀ (seg1Speed_pos hH), mul_comm, seg1Speed_mul_t₀_sub_three_fifths hH]
      exact h_eps_width
    have h_lin_lt_hi : linDelta (seg1Speed H) ε < 4/5 - seg4T₀ H z₀.im := by
      unfold linDelta
      rw [div_lt_iff₀ (seg1Speed_pos hH), mul_comm, seg1Speed_mul_four_fifths_sub_t₀ hH]
      exact h_eps_top
    have h_t_lo : 0 ≤ t := by linarith [(abs_le.mp ht).1]
    have h_t_hi : t ≤ 1 := by
      linarith [(abs_le.mp ht).2, seg4T₀_lt_four_fifths hH hc_hi]
    rw [hγ t ⟨h_t_lo, h_t_hi⟩]
    exact seg4_near_of_linDelta hH hz_re h_eps_top h_eps_width ht
  ftcHyp := ftcHyp

end
