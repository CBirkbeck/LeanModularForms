/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ValenceFormula.RectHomotopy.Geometry

/-!
# Homotopy infrastructure for FD boundary → polygon deformation

Defines the segment helper functions `H_seg1`..`H_seg5`, proves their
continuity and matching at breakpoints, and establishes the main results:

* `fdBoundaryToPolygonHomotopy_continuous`
* `fdBoundaryToPolygonHomotopy_avoids`
* `fdBoundaryToPolygonHomotopy_closed`
* `fdBoundaryToPolygon_homotopy_avoids_interior`
* `circleAround` and `polygonToCircleHomotopy`
-/

open Complex Set Metric Filter

namespace RectHomotopyProof

noncomputable def H_seg1 (p : ℝ × ℝ) : ℂ :=
  1/2 + (H_height - p.1 * (H_height - Real.sqrt 3 / 2)) * I

noncomputable def H_seg2 (p : ℝ × ℝ) : ℂ :=
  let arc_point :=
    Complex.exp ((Real.pi / 3 + (p.1 - 1) *
      (Real.pi / 2 - Real.pi / 3)) * I)
  let chord_point := chordSegment rho' i_point (p.1 - 1)
  (1 - p.2) • arc_point + p.2 • chord_point

noncomputable def H_seg3 (p : ℝ × ℝ) : ℂ :=
  let arc_point :=
    Complex.exp ((Real.pi / 2 + (p.1 - 2) *
      (2 * Real.pi / 3 - Real.pi / 2)) * I)
  let chord_point := chordSegment i_point rho (p.1 - 2)
  (1 - p.2) • arc_point + p.2 • chord_point

noncomputable def H_seg4 (p : ℝ × ℝ) : ℂ :=
  -1/2 + (Real.sqrt 3 / 2 + (p.1 - 3) *
    (H_height - Real.sqrt 3 / 2)) * I

noncomputable def H_seg5 (p : ℝ × ℝ) : ℂ :=
  (p.1 - 9/2) + H_height * I

lemma H_seg1_continuous : Continuous H_seg1 := by
  unfold H_seg1; continuity

lemma H_seg2_continuous : Continuous H_seg2 := by
  unfold H_seg2 chordSegment; continuity

lemma H_seg3_continuous : Continuous H_seg3 := by
  unfold H_seg3 chordSegment; continuity

lemma H_seg4_continuous : Continuous H_seg4 := by
  unfold H_seg4; continuity

lemma H_seg5_continuous : Continuous H_seg5 := by
  unfold H_seg5; continuity

lemma exp_real_mul_I (θ : ℝ) :
    Complex.exp (↑θ * I) =
      ↑(Real.cos θ) + ↑(Real.sin θ) * I := by
  rw [Complex.exp_mul_I, Complex.ofReal_cos,
    Complex.ofReal_sin]

lemma Real.cos_two_pi_div_three' :
    Real.cos (2 * Real.pi / 3) = -1/2 := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by
    ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num

lemma Real.sin_two_pi_div_three' :
    Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by
    ring
  rw [h, Real.sin_pi_sub, Real.sin_pi_div_three]

lemma exp_pi_div_three_eq_rho' :
    Complex.exp (↑(Real.pi / 3) * I) = rho' := by
  rw [exp_real_mul_I, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  simp only [rho', Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]

lemma exp_pi_div_two_eq_I :
    Complex.exp (↑(Real.pi / 2) * I) = I := by
  rw [exp_real_mul_I, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp only [Complex.ofReal_zero, Complex.ofReal_one,
    zero_add, one_mul]

lemma exp_two_pi_div_three_eq_rho :
    Complex.exp (↑(2 * Real.pi / 3) * I) = rho := by
  rw [exp_real_mul_I, Real.cos_two_pi_div_three',
    Real.sin_two_pi_div_three']
  simp only [rho, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]

lemma H_match_at_t1 (p : ℝ × ℝ) (hp : p.1 = 1) :
    H_seg1 p = H_seg2 p := by
  obtain ⟨t, s⟩ := p
  simp only at hp; subst hp
  simp only [H_seg1, H_seg2, chordSegment, H_height,
    rho', i_point]
  have hLHS :
      (↑(Real.sqrt 3 / 2 + 1) - ↑(1:ℝ) *
        (↑(Real.sqrt 3 / 2 + 1) -
          ↑(Real.sqrt 3) / 2) : ℂ) =
        ↑(Real.sqrt 3) / 2 := by push_cast; ring
  simp only [hLHS]
  have hangle :
      (↑Real.pi / 3 + (↑(1:ℝ) - 1) *
        (↑Real.pi / 2 - ↑Real.pi / 3) : ℂ) =
        ↑Real.pi / 3 := by
    simp only [Complex.ofReal_one, sub_self,
      zero_mul, add_zero]
  simp only [hangle]
  have hpi3 : (↑Real.pi / 3 : ℂ) = ↑(Real.pi / 3) := by
    push_cast; ring
  rw [hpi3, exp_pi_div_three_eq_rho']
  simp only [sub_self, zero_smul, add_zero, rho']
  simp only [smul_add, Complex.real_smul,
    Complex.ofReal_sub, Complex.ofReal_one,
    sub_zero, one_mul]
  ring

lemma H_match_at_t2 (p : ℝ × ℝ) (hp : p.1 = 2) :
    H_seg2 p = H_seg3 p := by
  obtain ⟨t, s⟩ := p
  simp only at hp; subst hp
  unfold H_seg2 H_seg3 chordSegment rho' i_point rho
  simp only [Complex.ofReal_ofNat]
  norm_num

lemma H_match_at_t3 (p : ℝ × ℝ) (hp : p.1 = 3) :
    H_seg3 p = H_seg4 p := by
  obtain ⟨t, s⟩ := p
  simp only at hp; subst hp
  unfold H_seg3 H_seg4 chordSegment i_point rho H_height
  simp only [Complex.ofReal_ofNat]
  norm_num
  have hexp :
      Complex.exp (2 * ↑Real.pi / 3 * I) =
        -1/2 + ↑(Real.sqrt 3) / 2 * I := by
    have h : (2 * ↑Real.pi / 3 * I : ℂ) =
        ↑(2 * Real.pi / 3) * I := by push_cast; ring
    rw [h, exp_two_pi_div_three_eq_rho, rho]
  simp only [hexp]; ring

lemma H_match_at_t4 (p : ℝ × ℝ) (hp : p.1 = 4) :
    H_seg4 p = H_seg5 p := by
  obtain ⟨t, s⟩ := p
  simp only at hp; subst hp
  simp only [H_seg4, H_seg5, H_height]
  ring_nf
  simp only [Complex.ofReal_add, Complex.ofReal_ofNat]
  ring

lemma fdBoundaryToPolygonHomotopy_continuous :
    Continuous fdBoundaryToPolygonHomotopy := by
  have h45 : Continuous (fun p =>
      if p.1 ≤ 4 then H_seg4 p else H_seg5 p) := by
    apply Continuous.if_le H_seg4_continuous
      H_seg5_continuous continuous_fst continuous_const
    intro p hp; exact H_match_at_t4 p hp
  have h345 : Continuous (fun p =>
      if p.1 ≤ 3 then H_seg3 p
      else if p.1 ≤ 4 then H_seg4 p
      else H_seg5 p) := by
    apply Continuous.if_le H_seg3_continuous h45
      continuous_fst continuous_const
    intro p hp
    simp only [show p.1 ≤ 4 from
      le_trans (le_of_eq hp) (by norm_num : (3 : ℝ) ≤ 4),
      if_true]
    exact H_match_at_t3 p hp
  have h2345 : Continuous (fun p =>
      if p.1 ≤ 2 then H_seg2 p
      else if p.1 ≤ 3 then H_seg3 p
      else if p.1 ≤ 4 then H_seg4 p
      else H_seg5 p) := by
    apply Continuous.if_le H_seg2_continuous h345
      continuous_fst continuous_const
    intro p hp
    simp only [show p.1 ≤ 3 from
      le_trans (le_of_eq hp) (by norm_num : (2 : ℝ) ≤ 3),
      if_true]
    exact H_match_at_t2 p hp
  have h12345 : Continuous (fun p =>
      if p.1 ≤ 1 then H_seg1 p
      else if p.1 ≤ 2 then H_seg2 p
      else if p.1 ≤ 3 then H_seg3 p
      else if p.1 ≤ 4 then H_seg4 p
      else H_seg5 p) := by
    apply Continuous.if_le H_seg1_continuous h2345
      continuous_fst continuous_const
    intro p hp
    simp only [show p.1 ≤ 2 from
      le_trans (le_of_eq hp) (by norm_num : (1 : ℝ) ≤ 2),
      if_true]
    exact H_match_at_t1 p hp
  convert h12345 using 1

lemma fdBoundaryToPolygonHomotopy_at_zero
    (t : ℝ) (_ht : t ∈ Icc 0 5) :
    fdBoundaryToPolygonHomotopy (t, 0) = fdBoundary t := by
  simp only [fdBoundaryToPolygonHomotopy, fdBoundary]
  split_ifs with h1 h2 h3 h4
  · rfl
  · simp only [sub_zero, one_smul, zero_smul, add_zero]
  · simp only [sub_zero, one_smul, zero_smul, add_zero]
  · rfl
  · rfl

lemma fdBoundaryToPolygonHomotopy_at_one
    (t : ℝ) (_ht : t ∈ Icc 0 5) :
    fdBoundaryToPolygonHomotopy (t, 1) = fdPolygon t := by
  simp only [fdBoundaryToPolygonHomotopy, fdPolygon]
  split_ifs with h1 h2 h3 h4
  · rfl
  · simp only [sub_self, zero_smul, one_smul, zero_add]
  · simp only [sub_self, zero_smul, one_smul, zero_add]
  · rfl
  · rfl

lemma fdBoundaryToPolygonHomotopy_avoids (p : ℂ)
    (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2)
    (hp_im : p.im < H_height)
    (t : ℝ) (_ht : t ∈ Icc 0 5) (s : ℝ)
    (hs : s ∈ Icc 0 1) :
    fdBoundaryToPolygonHomotopy (t, s) ≠ p := by
  simp only [fdBoundaryToPolygonHomotopy]
  split_ifs with h1 h2 h3 h4
  · intro heq
    have hre :
        (1/2 + (↑H_height - ↑t *
          (↑H_height - ↑(Real.sqrt 3) / 2)) *
            I : ℂ).re = 1/2 := by
      simp only [Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, mul_zero,
        Complex.I_im, mul_one, Complex.sub_re,
        Complex.div_ofNat_re, Complex.sub_im,
        Complex.ofReal_im, Complex.div_ofNat_im,
        Complex.mul_im]
      norm_num
    rw [heq] at hre
    have : |p.re| = 1/2 := by rw [hre]; norm_num
    linarith
  · have ht2 : t - 1 ∈ Icc 0 1 := by
      constructor <;> linarith [h1, h2]
    have h_arc_in := segment2_arc_in_closed_unit_ball t
    have h_chord_in := chord1_in_closed_unit_ball (t - 1) ht2
    have h_in_ball :
        (1 - s) • Complex.exp
          ((Real.pi / 3 + (t - 1) *
            (Real.pi / 2 - Real.pi / 3)) * I) +
          s • chordSegment rho' i_point (t - 1) ∈
            closedBall (0 : ℂ) 1 :=
      chordSegment_in_convex convex_closedBall_zero_one
        h_arc_in h_chord_in s hs
    have hp_out := outside_closed_unit_ball p hp_norm
    exact fun h => hp_out (h ▸ h_in_ball)
  · have ht3 : t - 2 ∈ Icc 0 1 := by
      constructor <;> linarith [h2, h3]
    have h_arc_in := segment3_arc_in_closed_unit_ball t
    have h_chord_in := chord2_in_closed_unit_ball (t - 2) ht3
    have h_in_ball :
        (1 - s) • Complex.exp
          ((Real.pi / 2 + (t - 2) *
            (2 * Real.pi / 3 - Real.pi / 2)) * I) +
          s • chordSegment i_point rho (t - 2) ∈
            closedBall (0 : ℂ) 1 :=
      chordSegment_in_convex convex_closedBall_zero_one
        h_arc_in h_chord_in s hs
    have hp_out := outside_closed_unit_ball p hp_norm
    exact fun h => hp_out (h ▸ h_in_ball)
  · intro heq
    have hre :
        ((-1/2 : ℂ) + (↑(Real.sqrt 3) / 2 +
          (↑t - 3) * (↑H_height -
            ↑(Real.sqrt 3) / 2)) * I).re = -1/2 := by
      simp only [Complex.add_re, Complex.mul_re,
        Complex.I_re, mul_zero,
        Complex.I_im, mul_one, Complex.sub_re,
        Complex.div_ofNat_re,
        Complex.sub_im, Complex.ofReal_im,
        Complex.div_ofNat_im]
      norm_num
    rw [heq] at hre
    have : |p.re| = 1/2 := by rw [hre]; norm_num
    linarith
  · intro heq
    have him :
        (↑t - 9/2 + ↑H_height * I : ℂ).im =
          H_height := by
      simp only [Complex.add_im, Complex.sub_im,
        Complex.ofReal_im, Complex.div_ofNat_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        mul_zero, Complex.I_im, mul_one]
      simp only [show (9 : ℂ).im = 0 from rfl,
        add_zero, zero_div, sub_zero, zero_add]
    rw [heq] at him; linarith

lemma fdBoundaryToPolygonHomotopy_closed (s : ℝ)
    (_hs : s ∈ Icc 0 1) :
    fdBoundaryToPolygonHomotopy (0, s) =
      fdBoundaryToPolygonHomotopy (5, s) := by
  simp only [fdBoundaryToPolygonHomotopy]
  simp only [show (0 : ℝ) ≤ 1 from by norm_num,
    ↓reduceIte,
    show ¬(5 : ℝ) ≤ 1 from by norm_num,
    show ¬(5 : ℝ) ≤ 2 from by norm_num,
    show ¬(5 : ℝ) ≤ 3 from by norm_num,
    show ¬(5 : ℝ) ≤ 4 from by norm_num]
  simp only [H_height]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]
  norm_cast; ring

noncomputable def circleAround (p : ℂ) (ε : ℝ) :
    ℝ → ℂ := fun t =>
  p + ε * Complex.exp (2 * Real.pi * I * t / 5)

lemma circleAround_closed (p : ℂ) (ε : ℝ) :
    circleAround p ε 0 = circleAround p ε 5 := by
  simp only [circleAround]
  congr 1
  have h0 : 2 * Real.pi * I * (0 : ℂ) / 5 = 0 := by ring
  have h5 : 2 * Real.pi * I * (5 : ℂ) / 5 =
      2 * Real.pi * I := by ring
  simp only [Complex.ofReal_zero, mul_zero, zero_div,
    Complex.ofReal_ofNat]
  rw [h5, Complex.exp_zero, Complex.exp_two_pi_mul_I]

lemma circleAround_continuous (p : ℂ) (ε : ℝ) :
    Continuous (circleAround p ε) := by
  unfold circleAround; continuity

lemma circleAround_dist (p : ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (t : ℝ) : ‖circleAround p ε t - p‖ = ε := by
  simp only [circleAround, add_sub_cancel_left]
  rw [Complex.norm_mul]
  have hform :
      2 * Real.pi * I * (t : ℂ) / 5 =
        ↑(2 * Real.pi * t / 5) * I := by
    push_cast; ring
  rw [hform, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real]
  exact abs_of_nonneg hε

noncomputable def polygonToCircleHomotopy (p : ℂ)
    (ε : ℝ) : ℝ × ℝ → ℂ := fun (t, s) =>
  let z := fdPolygon t
  let dir := z - p
  p + (1 - s) * dir + s * ε * (dir / ‖dir‖)

lemma fdPolygon_avoids_interior (p : ℂ)
    (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2)
    (hp_im : p.im < H_height)
    (t : ℝ) (_ht : t ∈ Icc 0 5) :
    fdPolygon t ≠ p := by
  have h := fdBoundaryToPolygonHomotopy_avoids p hp_norm
    hp_re hp_im t _ht 1 ⟨zero_le_one, le_refl 1⟩
  simp only [fdBoundaryToPolygonHomotopy_at_one t _ht] at h
  exact h

theorem fdBoundaryToPolygon_homotopy_avoids_interior
    (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2)
    (hp_im : p.im < H_height) :
    ∀ t ∈ Icc 0 5, ∀ s ∈ Icc (0:ℝ) 1,
      fdBoundaryToPolygonHomotopy (t, s) ≠ p :=
  fdBoundaryToPolygonHomotopy_avoids p hp_norm hp_re hp_im

theorem fdBoundaryToPolygon_homotopy_closed :
    ∀ s ∈ Icc (0:ℝ) 1,
      fdBoundaryToPolygonHomotopy (0, s) =
        fdBoundaryToPolygonHomotopy (5, s) :=
  fdBoundaryToPolygonHomotopy_closed

theorem fdBoundaryToPolygon_homotopy_continuous :
    Continuous fdBoundaryToPolygonHomotopy :=
  fdBoundaryToPolygonHomotopy_continuous

theorem winding_number_one_summary (p : ℂ)
    (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2)
    (hp_im : p.im < H_height) :
    (∀ t ∈ Icc 0 5, ∀ s ∈ Icc (0:ℝ) 1,
      fdBoundaryToPolygonHomotopy (t, s) ≠ p) ∧
    Continuous fdBoundaryToPolygonHomotopy ∧
    (∀ s ∈ Icc (0:ℝ) 1,
      fdBoundaryToPolygonHomotopy (0, s) =
        fdBoundaryToPolygonHomotopy (5, s)) :=
  ⟨fdBoundaryToPolygon_homotopy_avoids_interior p
      hp_norm hp_re hp_im,
   fdBoundaryToPolygon_homotopy_continuous,
   fdBoundaryToPolygon_homotopy_closed⟩

end RectHomotopyProof
