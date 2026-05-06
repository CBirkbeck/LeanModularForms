/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.BoundaryWindingSeg4Proof
import LeanModularForms.ForMathlib.SegmentAnalysis
import LeanModularForms.ForMathlib.SegmentFTC
import LeanModularForms.ForMathlib.WindingWeightProofs

/-!
# `ArcFTCHyp` for the left vertical edge (seg4) at a generic point

Symmetric to seg1, but the crossing direction is reversed (seg4 goes UP
while seg1 goes DOWN). Because of this reversed orientation, we use
`ftc_log_on_segment` (not `ftc_log_neg_on_segment`): for seg4 z₀ all
relevant trajectory pieces are themselves in `Complex.slitPlane`, so
log can be taken directly without negation.

## Main results

* `arcFTCHyp_seg4` — the full `ArcFTCHyp` at any seg4 interior point
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ### Per-segment reference functions for `fdBoundaryFun H t - z₀` on seg4 -/

private def seg4_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((1/2 - z₀.re : ℝ) : ℂ) +
  ((H - 5 * t * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I

private lemma fdBoundary_sub_eq_seg4_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) (ht : t ≤ 1/5) :
    fdBoundaryFun H t - z₀ = seg4_h₀ H z₀ t := by
  simp only [fdBoundaryFun, ht, ite_true, seg4_h₀]
  apply Complex.ext
  · simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
  · simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]

private lemma seg4_h₀_continuous (H : ℝ) (z₀ : ℂ) : Continuous (seg4_h₀ H z₀) := by
  unfold seg4_h₀
  refine Continuous.add continuous_const ?_
  refine Continuous.mul ?_ continuous_const
  exact Complex.continuous_ofReal.comp (by fun_prop)

private lemma hasDerivAt_seg4_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (seg4_h₀ H z₀) (-(seg1Speed H : ℂ) * I) t := by
  have h1 : HasDerivAt
      (fun s : ℝ => ((H - 5 * s * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ))
      (-(seg1Speed H : ℂ)) t := by
    have h_real : HasDerivAt (fun s : ℝ => H - 5 * s * (H - Real.sqrt 3 / 2) - z₀.im)
        (-seg1Speed H) t := by
      have hd : HasDerivAt (fun s : ℝ => 5 * s * (H - Real.sqrt 3 / 2))
          (5 * (H - Real.sqrt 3 / 2)) t := by
        have := (hasDerivAt_id t).const_mul (5 : ℝ)
        exact (this.mul_const (H - Real.sqrt 3 / 2)).congr_deriv (by ring)
      have := (hasDerivAt_const t H).sub hd |>.sub_const z₀.im
      exact this.congr_deriv (by unfold seg1Speed; ring)
    exact (h_real.ofReal_comp).congr_deriv (by push_cast; ring)
  exact ((hasDerivAt_const t (((1/2 - z₀.re : ℝ) : ℂ))).add (h1.mul_const I)).congr_deriv
    (by ring)

private lemma deriv_seg4_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (seg4_h₀ H z₀) t = -(seg1Speed H : ℂ) * I :=
  (hasDerivAt_seg4_h₀ H z₀ t).deriv

/-- Arc reference function (same as seg1). -/
private def seg4_h_arc (z₀ : ℂ) (t : ℝ) : ℂ :=
  exp (↑(fdArcAngle t) * I) - z₀

private lemma fdBoundary_sub_eq_seg4_h_arc {H : ℝ} (z₀ : ℂ) {t : ℝ}
    (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t - z₀ = seg4_h_arc z₀ t := by
  unfold seg4_h_arc
  rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2]

private lemma seg4_h_arc_continuous (z₀ : ℂ) : Continuous (seg4_h_arc z₀) := by
  unfold seg4_h_arc
  exact (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp fdArcAngle_continuous).mul continuous_const)).sub
    continuous_const

private lemma hasDerivAt_seg4_h_arc (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (seg4_h_arc z₀)
      (↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I)) t := by
  unfold seg4_h_arc
  have h1 : HasDerivAt fdArcAngle (5 * Real.pi / 6) t := by
    unfold fdArcAngle
    have hd1 : HasDerivAt (fun s : ℝ => Real.pi / 3 + (5 * s - 1) * (Real.pi / 6))
        (5 * (Real.pi / 6)) t := by
      have h := ((hasDerivAt_id t).const_mul (5 : ℝ)).sub_const 1
      have := (h.mul_const (Real.pi / 6)).const_add (Real.pi / 3)
      exact this.congr_deriv (by ring)
    exact hd1.congr_deriv (by ring)
  have h2 : HasDerivAt (fun s : ℝ => (↑(fdArcAngle s) : ℂ) * I)
      (↑(5 * Real.pi / 6) * I) t :=
    ((h1.ofReal_comp).mul_const I).congr_deriv (by push_cast; ring)
  exact (h2.cexp.congr_deriv (by ring)).sub_const z₀

private lemma deriv_seg4_h_arc (z₀ : ℂ) (t : ℝ) :
    deriv (seg4_h_arc z₀) t = ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I) :=
  (hasDerivAt_seg4_h_arc z₀ t).deriv

/-- For `z₀ = -1/2 + c · I` with `c > √3/2`, `seg4_h_arc z₀ t` lies in `slitPlane`:
`re = cos θ + 1/2 ≥ 0` (= 0 only at θ = 2π/3 where im < 0). -/
private lemma seg4_h_arc_slitPlane {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im)
    {t : ℝ} (ht1 : 1/5 ≤ t) (ht3 : t ≤ 3/5) :
    seg4_h_arc z₀ t ∈ Complex.slitPlane := by
  unfold seg4_h_arc
  rcases eq_or_lt_of_le ht3 with h_eq | ht3_lt
  · -- t = 3/5: γ = ρ
    rw [Complex.mem_slitPlane_iff]
    right
    rw [h_eq]
    have hpi := Real.pi_pos
    rw [show (fdArcAngle (3/5) : ℝ) = 2 * Real.pi / 3 from by unfold fdArcAngle; ring]
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_add, add_zero]
    intro h_eq2
    nlinarith
  · rw [Complex.mem_slitPlane_iff]
    left
    have hpi := Real.pi_pos
    have hθ_lo : Real.pi / 3 ≤ fdArcAngle t := by
      unfold fdArcAngle
      nlinarith
    have hθ_hi : fdArcAngle t < 2 * Real.pi / 3 := by
      unfold fdArcAngle
      nlinarith
    have h_cos_gt : Real.cos (fdArcAngle t) > -1/2 := by
      have h_2pi3 : (2 * Real.pi / 3) ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
      have hθ_Icc : fdArcAngle t ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
      have := Real.strictAntiOn_cos hθ_Icc h_2pi3 hθ_hi
      have h_cos_2pi3 : Real.cos (2 * Real.pi / 3) = -1/2 := by
        rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring,
            Real.cos_pi_sub, Real.cos_pi_div_three]
        norm_num
      linarith
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, mul_one]
    rw [hz_re]
    linarith

/-- For `z₀.re = -1/2`, `seg4_h₀(t)` (the seg1 reference) has `re = 1`,
hence is in `slitPlane`. -/
private lemma seg4_h₀_slitPlane {H : ℝ} {z₀ : ℂ} (hz_re : z₀.re = -1/2) (t : ℝ) :
    seg4_h₀ H z₀ t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  unfold seg4_h₀
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero]
  rw [hz_re]
  norm_num

/-- Seg4 reference (the crossing segment for seg4 z₀). -/
private def seg4_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((-1/2 - z₀.re : ℝ) : ℂ) +
  ((Real.sqrt 3 / 2 + (5 * t - 3) * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I

/-- For `z₀.re = -1/2`, `seg4_h₃` simplifies to a purely imaginary expression. -/
private lemma seg4_h₃_eq_pure_im {H : ℝ} {z₀ : ℂ} (hz_re : z₀.re = -1/2) (t : ℝ) :
    seg4_h₃ H z₀ t =
      ((Real.sqrt 3 / 2 + (5 * t - 3) * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I := by
  unfold seg4_h₃
  rw [show (-1/2 - z₀.re : ℝ) = 0 from by rw [hz_re]; ring]
  simp

private lemma fdBoundary_sub_eq_seg4_h₃ (H : ℝ) (z₀ : ℂ) {t : ℝ}
    (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    fdBoundaryFun H t - z₀ = seg4_h₃ H z₀ t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    ht4, ite_true, ite_false, seg4_h₃]
  apply Complex.ext
  · simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.div_ofNat]
  · simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]

private lemma seg4_h₃_continuous (H : ℝ) (z₀ : ℂ) : Continuous (seg4_h₃ H z₀) := by
  unfold seg4_h₃
  refine Continuous.add continuous_const ?_
  refine Continuous.mul ?_ continuous_const
  exact Complex.continuous_ofReal.comp (by fun_prop)

private lemma hasDerivAt_seg4_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (seg4_h₃ H z₀) ((seg1Speed H : ℂ) * I) t := by
  have h1 : HasDerivAt
      (fun s : ℝ =>
        ((Real.sqrt 3 / 2 + (5 * s - 3) * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ))
      ((seg1Speed H : ℂ)) t := by
    have h_real : HasDerivAt
        (fun s : ℝ => Real.sqrt 3 / 2 + (5 * s - 3) * (H - Real.sqrt 3 / 2) - z₀.im)
        (seg1Speed H) t := by
      have hd : HasDerivAt (fun s : ℝ => 5 * s - 3) 5 t :=
        (((hasDerivAt_id t).const_mul 5).sub_const 3).congr_deriv (by ring)
      have := ((hd.mul_const (H - Real.sqrt 3 / 2)).const_add (Real.sqrt 3 / 2)).sub_const z₀.im
      exact this.congr_deriv (by unfold seg1Speed; ring)
    exact (h_real.ofReal_comp).congr_deriv (by ring)
  exact ((hasDerivAt_const t (((-1/2 - z₀.re : ℝ) : ℂ))).add (h1.mul_const I)).congr_deriv
    (by ring)

private lemma deriv_seg4_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (seg4_h₃ H z₀) t = (seg1Speed H : ℂ) * I :=
  (hasDerivAt_seg4_h₃ H z₀ t).deriv

/-- For seg4 z₀ at left half [3/5, t₀-δ], `seg4_h₃ ∈ slitPlane` (negative imaginary). -/
private lemma seg4_h₃_left_slitPlane {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    {δ : ℝ} (hδ_pos : 0 < δ)
    {t : ℝ} (htd : t ≤ seg4T₀ H z₀.im - δ) :
    seg4_h₃ H z₀ t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  rw [seg4_h₃_eq_pure_im hz_re]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero]
  intro h_eq
  have hK : 0 < seg1Speed H := seg1Speed_pos hH
  have hK_eq_seg4 : seg1Speed H * (seg4T₀ H z₀.im - 3/5) = z₀.im - Real.sqrt 3 / 2 := by
    unfold seg4T₀
    field_simp
    ring
  have h_t : t = seg4T₀ H z₀.im := by
    have h_speed_eq : seg1Speed H * (t - 3/5) = z₀.im - Real.sqrt 3 / 2 := by
      unfold seg1Speed
      linarith
    have hcancel : t - 3/5 = seg4T₀ H z₀.im - 3/5 :=
      mul_left_cancel₀ (ne_of_gt hK) (h_speed_eq.trans hK_eq_seg4.symm)
    linarith
  linarith

/-- For seg4 z₀ at right half [t₀+δ, 4/5], `seg4_h₃ ∈ slitPlane`. -/
private lemma seg4_h₃_right_slitPlane {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    {δ : ℝ} (hδ_pos : 0 < δ)
    {t : ℝ} (htd : seg4T₀ H z₀.im + δ ≤ t) :
    seg4_h₃ H z₀ t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  rw [seg4_h₃_eq_pure_im hz_re]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero]
  intro h_eq
  have hK : 0 < seg1Speed H := seg1Speed_pos hH
  have hK_eq_seg4 : seg1Speed H * (seg4T₀ H z₀.im - 3/5) = z₀.im - Real.sqrt 3 / 2 := by
    unfold seg4T₀
    field_simp
    ring
  have h_t : t = seg4T₀ H z₀.im := by
    have h_speed_eq : seg1Speed H * (t - 3/5) = z₀.im - Real.sqrt 3 / 2 := by
      unfold seg1Speed
      linarith
    have hcancel : t - 3/5 = seg4T₀ H z₀.im - 3/5 :=
      mul_left_cancel₀ (ne_of_gt hK) (h_speed_eq.trans hK_eq_seg4.symm)
    linarith
  linarith

/-- Seg5 reference. -/
private def seg4_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((5 * t - 9/2 - z₀.re : ℝ) : ℂ) + ((H - z₀.im : ℝ) : ℂ) * I

private lemma fdBoundary_sub_eq_seg4_h₅ (H : ℝ) (z₀ : ℂ) {t : ℝ} (ht : 4/5 < t) :
    fdBoundaryFun H t - z₀ = seg4_h₅ H z₀ t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    show ¬t ≤ 4/5 from by linarith, ite_false, seg4_h₅]
  apply Complex.ext
  · simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
  · simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]

private lemma seg4_h₅_continuous (H : ℝ) (z₀ : ℂ) : Continuous (seg4_h₅ H z₀) := by
  unfold seg4_h₅
  refine Continuous.add ?_ continuous_const
  exact Complex.continuous_ofReal.comp (by fun_prop)

private lemma hasDerivAt_seg4_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (seg4_h₅ H z₀) (5 : ℂ) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((5 * s - 9/2 - z₀.re : ℝ) : ℂ)) 5 t := by
    have h_real : HasDerivAt (fun s : ℝ => 5 * s - 9/2 - z₀.re) 5 t :=
      ((((hasDerivAt_id t).const_mul 5).sub_const (9/2)).sub_const z₀.re).congr_deriv (by ring)
    exact (h_real.ofReal_comp).congr_deriv (by push_cast; ring)
  exact (h1.add_const _).congr_deriv (by ring)

private lemma deriv_seg4_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (seg4_h₅ H z₀) t = 5 :=
  (hasDerivAt_seg4_h₅ H z₀ t).deriv

/-- For `z₀.im < H`, `seg4_h₅ ∈ slitPlane` (positive imaginary). -/
private lemma seg4_h₅_slitPlane {H : ℝ} {z₀ : ℂ} (hc_hi : z₀.im < H) (t : ℝ) :
    seg4_h₅ H z₀ t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  unfold seg4_h₅
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
  intro h
  linarith

/-! ### Per-segment FTC pieces (using `ftc_log_on_segment`) -/

/-- FTC for seg1 [0, 1/5] (full, since the crossing is on seg4). -/
private lemma seg4_seg1_ftc (H : ℝ) {z₀ : ℂ} (hz_re : z₀.re = -1/2) :
    IntervalIntegrable
      (fun t => deriv (seg4_h₀ H z₀) t / seg4_h₀ H z₀ t) volume 0 (1/5) ∧
    ∫ t in (0:ℝ)..(1/5),
        deriv (seg4_h₀ H z₀) t / seg4_h₀ H z₀ t =
      Complex.log (seg4_h₀ H z₀ (1/5)) - Complex.log (seg4_h₀ H z₀ 0) := by
  apply LogDerivFTC.ftc_log_on_segment (by norm_num : (0 : ℝ) ≤ 1/5)
    (seg4_h₀_continuous H z₀).continuousOn
    (fun t _ => (hasDerivAt_seg4_h₀ H z₀ t).differentiableAt)
    (by
      rw [show deriv (seg4_h₀ H z₀) = fun _ => -(seg1Speed H : ℂ) * I from
        funext (deriv_seg4_h₀ H z₀)]
      exact continuousOn_const)
  intro t _
  exact seg4_h₀_slitPlane hz_re t

/-- FTC for arc [1/5, 3/5] (full). -/
private lemma seg4_arc_ftc {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) :
    IntervalIntegrable
      (fun t => deriv (seg4_h_arc z₀) t / seg4_h_arc z₀ t) volume (1/5) (3/5) ∧
    ∫ t in (1/5 : ℝ)..(3/5),
        deriv (seg4_h_arc z₀) t / seg4_h_arc z₀ t =
      Complex.log (seg4_h_arc z₀ (3/5)) - Complex.log (seg4_h_arc z₀ (1/5)) := by
  apply LogDerivFTC.ftc_log_on_segment (by norm_num : (1/5 : ℝ) ≤ 3/5)
    (seg4_h_arc_continuous z₀).continuousOn
    (fun t _ => (hasDerivAt_seg4_h_arc z₀ t).differentiableAt)
    (by
      have : ContinuousOn
          (fun t : ℝ => ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I)) (Icc (1/5) (3/5)) := by
        apply Continuous.continuousOn
        exact continuous_const.mul ((Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp fdArcAngle_continuous).mul continuous_const)))
      have h_eq : deriv (seg4_h_arc z₀) =
          fun t => ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I) :=
        funext (deriv_seg4_h_arc z₀)
      rw [h_eq]; exact this)
  intro t ⟨ht1, ht3⟩
  exact seg4_h_arc_slitPlane hz_re hc_lo ht1 ht3

/-- FTC for the seg4 left half [3/5, t₀ - δ]. -/
private lemma seg4_left_ftc {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < seg4T₀ H z₀.im - 3/5) :
    IntervalIntegrable
      (fun t => deriv (seg4_h₃ H z₀) t / seg4_h₃ H z₀ t) volume (3/5) (seg4T₀ H z₀.im - δ) ∧
    ∫ t in (3/5 : ℝ)..(seg4T₀ H z₀.im - δ),
        deriv (seg4_h₃ H z₀) t / seg4_h₃ H z₀ t =
      Complex.log (seg4_h₃ H z₀ (seg4T₀ H z₀.im - δ)) -
      Complex.log (seg4_h₃ H z₀ (3/5)) := by
  apply LogDerivFTC.ftc_log_on_segment (by linarith : (3/5 : ℝ) ≤ seg4T₀ H z₀.im - δ)
    (seg4_h₃_continuous H z₀).continuousOn
    (fun t _ => (hasDerivAt_seg4_h₃ H z₀ t).differentiableAt)
    (by
      rw [show deriv (seg4_h₃ H z₀) = fun _ => (seg1Speed H : ℂ) * I from
        funext (deriv_seg4_h₃ H z₀)]
      exact continuousOn_const)
  intro t ⟨_, htd⟩
  exact seg4_h₃_left_slitPlane hH hz_re hδ_pos htd

/-- FTC for the seg4 right half [t₀ + δ, 4/5]. -/
private lemma seg4_right_ftc {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 4/5 - seg4T₀ H z₀.im) :
    IntervalIntegrable
      (fun t => deriv (seg4_h₃ H z₀) t / seg4_h₃ H z₀ t) volume (seg4T₀ H z₀.im + δ) (4/5) ∧
    ∫ t in (seg4T₀ H z₀.im + δ)..(4/5 : ℝ),
        deriv (seg4_h₃ H z₀) t / seg4_h₃ H z₀ t =
      Complex.log (seg4_h₃ H z₀ (4/5)) -
      Complex.log (seg4_h₃ H z₀ (seg4T₀ H z₀.im + δ)) := by
  apply LogDerivFTC.ftc_log_on_segment (by linarith : seg4T₀ H z₀.im + δ ≤ 4/5)
    (seg4_h₃_continuous H z₀).continuousOn
    (fun t _ => (hasDerivAt_seg4_h₃ H z₀ t).differentiableAt)
    (by
      rw [show deriv (seg4_h₃ H z₀) = fun _ => (seg1Speed H : ℂ) * I from
        funext (deriv_seg4_h₃ H z₀)]
      exact continuousOn_const)
  intro t ⟨htd, _⟩
  exact seg4_h₃_right_slitPlane hH hz_re hδ_pos htd

/-- FTC for seg5 [4/5, 1] (full). -/
private lemma seg4_seg5_ftc (H : ℝ) {z₀ : ℂ} (hc_hi : z₀.im < H) :
    IntervalIntegrable
      (fun t => deriv (seg4_h₅ H z₀) t / seg4_h₅ H z₀ t) volume (4/5) 1 ∧
    ∫ t in (4/5 : ℝ)..(1 : ℝ),
        deriv (seg4_h₅ H z₀) t / seg4_h₅ H z₀ t =
      Complex.log (seg4_h₅ H z₀ 1) - Complex.log (seg4_h₅ H z₀ (4/5)) := by
  apply LogDerivFTC.ftc_log_on_segment (by norm_num : (4/5 : ℝ) ≤ 1)
    (seg4_h₅_continuous H z₀).continuousOn
    (fun t _ => (hasDerivAt_seg4_h₅ H z₀ t).differentiableAt)
    (by
      rw [show deriv (seg4_h₅ H z₀) = fun _ => (5 : ℂ) from
        funext (deriv_seg4_h₅ H z₀)]
      exact continuousOn_const)
  intro t _
  exact seg4_h₅_slitPlane hc_hi t

/-! ### Junction equalities -/

private lemma seg4_junction_15 (H : ℝ) (z₀ : ℂ) :
    seg4_h₀ H z₀ (1/5) = seg4_h_arc z₀ (1/5) := by
  unfold seg4_h₀ seg4_h_arc
  have hθ : (fdArcAngle (1/5) : ℝ) = Real.pi / 3 := by unfold fdArcAngle; ring
  rw [hθ, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  apply Complex.ext
  · simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
  · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    ring

private lemma seg4_junction_35 (H : ℝ) (z₀ : ℂ) :
    seg4_h_arc z₀ (3/5) = seg4_h₃ H z₀ (3/5) := by
  unfold seg4_h_arc seg4_h₃
  have hθ : (fdArcAngle (3/5) : ℝ) = 2 * Real.pi / 3 := by unfold fdArcAngle; ring
  rw [hθ, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
    ring
  · simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    ring

private lemma seg4_junction_45 (H : ℝ) (z₀ : ℂ) :
    seg4_h₃ H z₀ (4/5) = seg4_h₅ H z₀ (4/5) := by
  unfold seg4_h₃ seg4_h₅
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    ring

private lemma seg4_closed (H : ℝ) (z₀ : ℂ) :
    seg4_h₀ H z₀ 0 = seg4_h₅ H z₀ 1 := by
  unfold seg4_h₀ seg4_h₅
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    ring

/-! ### Final log computation -/

/-- For seg4 z₀, the log diff at the crossing equals `-π · I`. -/
private lemma seg4_log_diff_eq_neg_pi_I {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2) {δ : ℝ} (hδ_pos : 0 < δ) :
    Complex.log (seg4_h₃ H z₀ (seg4T₀ H z₀.im - δ)) -
    Complex.log (seg4_h₃ H z₀ (seg4T₀ H z₀.im + δ)) = -(↑Real.pi * I) := by
  have hK : 0 < seg1Speed H := seg1Speed_pos hH
  have hKδ : 0 < seg1Speed H * δ := mul_pos hK hδ_pos
  have hK_eq_seg4 : seg1Speed H * (seg4T₀ H z₀.im - 3/5) = z₀.im - Real.sqrt 3 / 2 := by
    unfold seg4T₀; field_simp; ring
  -- At t₀ - δ: seg4_h₃ = -K*δ * I (negative imaginary)
  have h_minus : seg4_h₃ H z₀ (seg4T₀ H z₀.im - δ) =
      ((-(seg1Speed H * δ) : ℝ) : ℂ) * I := by
    rw [seg4_h₃_eq_pure_im hz_re]
    congr 1
    have h_real :
        Real.sqrt 3 / 2 + (5 * (seg4T₀ H z₀.im - δ) - 3) * (H - Real.sqrt 3 / 2) - z₀.im =
        -(seg1Speed H * δ) := by
      have h_speed : (5 * (seg4T₀ H z₀.im - δ) - 3) * (H - Real.sqrt 3 / 2) =
          seg1Speed H * (seg4T₀ H z₀.im - δ - 3/5) := by unfold seg1Speed; ring
      rw [h_speed]
      have h_sub : seg4T₀ H z₀.im - δ - 3/5 = (seg4T₀ H z₀.im - 3/5) - δ := by ring
      rw [h_sub, mul_sub, hK_eq_seg4]
      ring
    exact_mod_cast h_real
  -- At t₀ + δ: seg4_h₃ = K*δ * I (positive imaginary)
  have h_plus : seg4_h₃ H z₀ (seg4T₀ H z₀.im + δ) =
      ((seg1Speed H * δ : ℝ) : ℂ) * I := by
    rw [seg4_h₃_eq_pure_im hz_re]
    congr 1
    have h_real :
        Real.sqrt 3 / 2 + (5 * (seg4T₀ H z₀.im + δ) - 3) * (H - Real.sqrt 3 / 2) - z₀.im =
        seg1Speed H * δ := by
      have h_speed : (5 * (seg4T₀ H z₀.im + δ) - 3) * (H - Real.sqrt 3 / 2) =
          seg1Speed H * (seg4T₀ H z₀.im + δ - 3/5) := by unfold seg1Speed; ring
      rw [h_speed]
      have h_add : seg4T₀ H z₀.im + δ - 3/5 = (seg4T₀ H z₀.im - 3/5) + δ := by ring
      rw [h_add, mul_add, hK_eq_seg4]
      ring
    exact_mod_cast h_real
  rw [h_minus, h_plus]
  -- log(-K·δ·I) - log(K·δ·I)
  rw [show (((-(seg1Speed H * δ) : ℝ) : ℂ) * I) = ((seg1Speed H * δ : ℝ) : ℂ) * (-I) from by
        push_cast; ring]
  rw [Complex.log_ofReal_mul hKδ (show (-I : ℂ) ≠ 0 from neg_ne_zero.mpr I_ne_zero),
      Complex.log_ofReal_mul hKδ I_ne_zero]
  rw [Complex.log_neg_I, Complex.log_I]
  ring

/-! ### A.e. equalities -/

private lemma seg4_ae_eq_h₀ (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) (1/5) →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (seg4_h₀ H z₀) t / seg4_h₀ H z₀ t := by
  have h_excl : ({1/5} : Set ℝ)ᶜ ∈ ae volume :=
    compl_mem_ae_iff.mpr (measure_singleton _)
  filter_upwards [h_excl] with t ht_ne ht_mem
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1/5)] at ht_mem
  have ht_lt : t < 1/5 :=
    lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (Set.mem_singleton_iff.mpr h))
  have h_eq : fdBoundaryFun H t - z₀ = seg4_h₀ H z₀ t :=
    fdBoundary_sub_eq_seg4_h₀ H z₀ t (le_of_lt ht_lt)
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] seg4_h₀ H z₀ :=
    Filter.eventually_of_mem (Iio_mem_nhds ht_lt)
      (fun s hs => fdBoundary_sub_eq_seg4_h₀ H z₀ s (le_of_lt hs))
  have h_deriv : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (seg4_h₀ H z₀) t :=
    h_evEq.deriv_eq
  have h_deriv_sub : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (fdBoundaryFun H) t :=
    deriv_sub_const (f := fdBoundaryFun H) _
  rw [h_eq, ← h_deriv_sub, h_deriv, div_eq_mul_inv, mul_comm]

private lemma seg4_ae_eq_h_arc (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (1/5 : ℝ) (3/5) →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (seg4_h_arc z₀) t / seg4_h_arc z₀ t := by
  have h_excl : ({3/5} : Set ℝ)ᶜ ∈ ae volume :=
    compl_mem_ae_iff.mpr (measure_singleton _)
  filter_upwards [h_excl] with t ht_ne ht_mem
  rw [uIoc_of_le (by norm_num : (1/5 : ℝ) ≤ 3/5)] at ht_mem
  have ht1 : 1/5 < t := ht_mem.1
  have ht3_lt : t < 3/5 :=
    lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (Set.mem_singleton_iff.mpr h))
  have h_eq : fdBoundaryFun H t - z₀ = seg4_h_arc z₀ t :=
    fdBoundary_sub_eq_seg4_h_arc z₀ ht1 (le_of_lt ht3_lt)
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] seg4_h_arc z₀ :=
    Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht3_lt))
      fun s ⟨hs1, hs3⟩ => fdBoundary_sub_eq_seg4_h_arc z₀ hs1 (le_of_lt hs3)
  have h_deriv : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (seg4_h_arc z₀) t :=
    h_evEq.deriv_eq
  have h_deriv_sub : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (fdBoundaryFun H) t :=
    deriv_sub_const (f := fdBoundaryFun H) _
  rw [h_eq, ← h_deriv_sub, h_deriv, div_eq_mul_inv, mul_comm]

private lemma seg4_ae_eq_h₃ (H : ℝ) (z₀ : ℂ) {a b : ℝ} (hab : a ≤ b)
    (ha_ge : 3/5 ≤ a) (hb_le : b ≤ 4/5) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (seg4_h₃ H z₀) t / seg4_h₃ H z₀ t := by
  have h_excl : ({a, b} : Set ℝ)ᶜ ∈ ae volume := by
    refine compl_mem_ae_iff.mpr ?_
    exact (Set.toFinite ({a, b} : Set ℝ)).measure_zero volume
  filter_upwards [h_excl] with t ht_ne ht_mem
  rw [uIoc_of_le hab] at ht_mem
  have ht_lt_b : t < b :=
    lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (Set.mem_insert_iff.mpr (Or.inr h)))
  have ht_gt_a : a < t := ht_mem.1
  have ht3_lt : 3/5 < t := lt_of_le_of_lt ha_ge ht_gt_a
  have ht4_lt : t < 4/5 := lt_of_lt_of_le ht_lt_b hb_le
  have h_eq : fdBoundaryFun H t - z₀ = seg4_h₃ H z₀ t :=
    fdBoundary_sub_eq_seg4_h₃ H z₀ ht3_lt (le_of_lt ht4_lt)
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] seg4_h₃ H z₀ :=
    Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht3_lt) (Iio_mem_nhds ht4_lt))
      fun s ⟨hs3, hs4⟩ => fdBoundary_sub_eq_seg4_h₃ H z₀ hs3 (le_of_lt hs4)
  have h_deriv : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (seg4_h₃ H z₀) t :=
    h_evEq.deriv_eq
  have h_deriv_sub : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (fdBoundaryFun H) t :=
    deriv_sub_const (f := fdBoundaryFun H) _
  rw [h_eq, ← h_deriv_sub, h_deriv, div_eq_mul_inv, mul_comm]

private lemma seg4_ae_eq_h₅ (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (4/5 : ℝ) 1 →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (seg4_h₅ H z₀) t / seg4_h₅ H z₀ t := by
  refine ae_of_all _ (fun t ht_mem => ?_)
  rw [uIoc_of_le (by norm_num : (4/5 : ℝ) ≤ 1)] at ht_mem
  have ht4 : 4/5 < t := ht_mem.1
  have h_eq : fdBoundaryFun H t - z₀ = seg4_h₅ H z₀ t :=
    fdBoundary_sub_eq_seg4_h₅ H z₀ ht4
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] seg4_h₅ H z₀ :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht4)
      fun s hs => fdBoundary_sub_eq_seg4_h₅ H z₀ hs
  have h_deriv : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (seg4_h₅ H z₀) t :=
    h_evEq.deriv_eq
  have h_deriv_sub : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (fdBoundaryFun H) t :=
    deriv_sub_const (f := fdBoundaryFun H) _
  rw [h_eq, ← h_deriv_sub, h_deriv, div_eq_mul_inv, mul_comm]

/-! ### Telescope theorem for seg4 -/

/-- The full FTC telescope for the seg4 crossing. -/
theorem fdBoundary_ftc_telescope_seg4 {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_lo : δ < seg4T₀ H z₀.im - 3/5)
    (hδ_lt_hi : δ < 4/5 - seg4T₀ H z₀.im) :
    (∫ t in (0 : ℝ)..(seg4T₀ H z₀.im - δ),
        (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
    (∫ t in (seg4T₀ H z₀.im + δ)..(1 : ℝ),
        (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) =
    -(↑Real.pi * I) := by
  set t₀ := seg4T₀ H z₀.im with ht₀_def
  have ht₀_lo : 3/5 < t₀ := seg4T₀_gt_three_fifths hH hc_lo
  have ht₀_hi : t₀ < 4/5 := seg4T₀_lt_four_fifths hH hc_hi
  -- Per-segment FTC pieces
  have h_seg1 := seg4_seg1_ftc H hz_re
  have h_arc := seg4_arc_ftc hz_re hc_lo
  have h_left := seg4_left_ftc hH hz_re hδ_pos hδ_lt_lo
  have h_right := seg4_right_ftc hH hz_re hδ_pos hδ_lt_hi
  have h_seg5 := seg4_seg5_ftc H hc_hi
  -- Convert each integral via ae equality
  have h_int_seg1 :
      ∫ t in (0:ℝ)..(1/5), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      Complex.log (seg4_h₀ H z₀ (1/5)) - Complex.log (seg4_h₀ H z₀ 0) := by
    rw [intervalIntegral.integral_congr_ae (seg4_ae_eq_h₀ H z₀)]
    exact h_seg1.2
  have h_int_arc :
      ∫ t in (1/5:ℝ)..(3/5), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      Complex.log (seg4_h_arc z₀ (3/5)) - Complex.log (seg4_h_arc z₀ (1/5)) := by
    rw [intervalIntegral.integral_congr_ae (seg4_ae_eq_h_arc H z₀)]
    exact h_arc.2
  have h_int_left :
      ∫ t in (3/5:ℝ)..(t₀ - δ), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      Complex.log (seg4_h₃ H z₀ (t₀ - δ)) - Complex.log (seg4_h₃ H z₀ (3/5)) := by
    rw [intervalIntegral.integral_congr_ae
      (seg4_ae_eq_h₃ H z₀ (by linarith) le_rfl (by linarith))]
    exact h_left.2
  have h_int_right :
      ∫ t in (t₀ + δ)..(4/5:ℝ), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      Complex.log (seg4_h₃ H z₀ (4/5)) - Complex.log (seg4_h₃ H z₀ (t₀ + δ)) := by
    rw [intervalIntegral.integral_congr_ae
      (seg4_ae_eq_h₃ H z₀ (by linarith) (by linarith) le_rfl)]
    exact h_right.2
  have h_int_seg5 :
      ∫ t in (4/5 : ℝ)..(1 : ℝ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      Complex.log (seg4_h₅ H z₀ 1) - Complex.log (seg4_h₅ H z₀ (4/5)) := by
    rw [intervalIntegral.integral_congr_ae (seg4_ae_eq_h₅ H z₀)]
    exact h_seg5.2
  -- Integrability for splitting
  have hint_seg1 : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume 0 (1/5) :=
    h_seg1.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((seg4_ae_eq_h₀ H z₀).mono (fun t ht hm => (ht hm).symm)))
  have hint_arc : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (1/5) (3/5) :=
    h_arc.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((seg4_ae_eq_h_arc H z₀).mono (fun t ht hm => (ht hm).symm)))
  have hint_left : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (3/5) (t₀ - δ) :=
    h_left.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((seg4_ae_eq_h₃ H z₀ (by linarith) le_rfl (by linarith)).mono
        (fun t ht hm => (ht hm).symm)))
  have hint_right : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (t₀ + δ) (4/5) :=
    h_right.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((seg4_ae_eq_h₃ H z₀ (by linarith) (by linarith) le_rfl).mono
        (fun t ht hm => (ht hm).symm)))
  have hint_seg5 : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (4/5) 1 :=
    h_seg5.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((seg4_ae_eq_h₅ H z₀).mono (fun t ht hm => (ht hm).symm)))
  -- Split the left integral [0, t₀-δ] = [0, 1/5] + [1/5, 3/5] + [3/5, t₀-δ]
  have h_split_left :
      ∫ t in (0:ℝ)..(t₀ - δ), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      (∫ t in (0:ℝ)..(1/5),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (1/5:ℝ)..(3/5),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (3/5:ℝ)..(t₀ - δ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals hint_seg1 hint_arc
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hint_seg1.trans hint_arc) hint_left
    linear_combination -h1 - h2
  -- Split the right integral [t₀+δ, 1] = [t₀+δ, 4/5] + [4/5, 1]
  have h_split_right :
      ∫ t in (t₀ + δ)..(1 : ℝ), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      (∫ t in (t₀ + δ)..(4/5 : ℝ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (4/5 : ℝ)..(1 : ℝ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) := by
    have h := intervalIntegral.integral_add_adjacent_intervals hint_right hint_seg5
    linear_combination -h
  -- Combine and telescope
  rw [h_split_left, h_split_right, h_int_seg1, h_int_arc, h_int_left, h_int_right, h_int_seg5,
      seg4_junction_15 H z₀, seg4_junction_35 H z₀, seg4_junction_45 H z₀,
      seg4_closed H z₀]
  have h_alg :
      Complex.log (seg4_h_arc z₀ (1/5)) - Complex.log (seg4_h₅ H z₀ 1) +
      (Complex.log (seg4_h₃ H z₀ (3/5)) - Complex.log (seg4_h_arc z₀ (1/5))) +
      (Complex.log (seg4_h₃ H z₀ (t₀ - δ)) - Complex.log (seg4_h₃ H z₀ (3/5))) +
      ((Complex.log (seg4_h₅ H z₀ (4/5)) - Complex.log (seg4_h₃ H z₀ (t₀ + δ))) +
        (Complex.log (seg4_h₅ H z₀ 1) - Complex.log (seg4_h₅ H z₀ (4/5))))
      = Complex.log (seg4_h₃ H z₀ (t₀ - δ)) - Complex.log (seg4_h₃ H z₀ (t₀ + δ)) := by
    ring
  rw [h_alg]
  exact seg4_log_diff_eq_neg_pi_I hH hz_re hδ_pos

/-! ### Final assembly: the ArcFTCHyp for seg4 -/

/-- The full `ArcFTCHyp` at any seg4 interior point, with limit `-π · I`. -/
def arcFTCHyp_seg4 {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H) :
    ArcFTCHyp γ z₀ (seg4T₀ H z₀.im) (linDelta (seg1Speed H))
      (seg4Threshold H z₀) (-(↑Real.pi * I)) where
  E := fun _ => -(↑Real.pi * I)
  h_ftc := by
    intro ε hε hε_thr
    have hK_pos : 0 < seg1Speed H := seg1Speed_pos hH
    have h_lin_pos : 0 < linDelta (seg1Speed H) ε := linDelta_pos hK_pos hε
    have h_eps_top : ε < H - z₀.im :=
      lt_of_lt_of_le hε_thr (min_le_right _ _)
    have h_eps_arc : ε < ‖z₀‖ - 1 :=
      lt_of_lt_of_le hε_thr (le_trans (min_le_left _ _) (min_le_left _ _))
    have h_eps_width : ε < z₀.im - Real.sqrt 3 / 2 :=
      lt_of_lt_of_le h_eps_arc (norm_sub_one_le_im_sub_sqrt3_seg4 hz_re hc_lo.le)
    have h_lin_lt_lo : linDelta (seg1Speed H) ε < seg4T₀ H z₀.im - 3/5 := by
      unfold linDelta
      rw [div_lt_iff₀ hK_pos, mul_comm, seg1Speed_mul_t₀_sub_three_fifths hH]
      exact h_eps_width
    have h_lin_lt_hi : linDelta (seg1Speed H) ε < 4/5 - seg4T₀ H z₀.im := by
      unfold linDelta
      rw [div_lt_iff₀ hK_pos, mul_comm, seg1Speed_mul_four_fifths_sub_t₀ hH]
      exact h_eps_top
    have h_t₀_lo : 3/5 < seg4T₀ H z₀.im := seg4T₀_gt_three_fifths hH hc_lo
    have h_t₀_hi : seg4T₀ H z₀.im < 4/5 := seg4T₀_lt_four_fifths hH hc_hi
    have h1 : seg4T₀ H z₀.im - linDelta (seg1Speed H) ε ≤ 1 := by linarith
    have h2 : 0 ≤ seg4T₀ H z₀.im + linDelta (seg1Speed H) ε := by linarith
    rw [transfer_integral z₀ (by linarith) (le_refl 0) h1 hγ,
        transfer_integral z₀ (by linarith) h2 (le_refl 1) hγ]
    exact fdBoundary_ftc_telescope_seg4 hH hz_re hc_lo hc_hi h_lin_pos
      h_lin_lt_lo h_lin_lt_hi
  hint_left := by
    intro ε hε hε_thr
    have hK_pos : 0 < seg1Speed H := seg1Speed_pos hH
    have h_lin_pos : 0 < linDelta (seg1Speed H) ε := linDelta_pos hK_pos hε
    have h_eps_top : ε < H - z₀.im :=
      lt_of_lt_of_le hε_thr (min_le_right _ _)
    have h_eps_arc : ε < ‖z₀‖ - 1 :=
      lt_of_lt_of_le hε_thr (le_trans (min_le_left _ _) (min_le_left _ _))
    have h_eps_width : ε < z₀.im - Real.sqrt 3 / 2 :=
      lt_of_lt_of_le h_eps_arc (norm_sub_one_le_im_sub_sqrt3_seg4 hz_re hc_lo.le)
    have h_lin_lt_lo : linDelta (seg1Speed H) ε < seg4T₀ H z₀.im - 3/5 := by
      unfold linDelta
      rw [div_lt_iff₀ hK_pos, mul_comm, seg1Speed_mul_t₀_sub_three_fifths hH]
      exact h_eps_width
    have h_t₀_lo : 3/5 < seg4T₀ H z₀.im := seg4T₀_gt_three_fifths hH hc_lo
    have h_t₀_hi : seg4T₀ H z₀.im < 4/5 := seg4T₀_lt_four_fifths hH hc_hi
    have h1 : seg4T₀ H z₀.im - linDelta (seg1Speed H) ε ≤ 1 := by linarith
    apply transfer_integrability z₀ (by linarith) (le_refl 0) h1 hγ
    -- Need integrability on [0, t₀-δ]; combine seg1 + arc + left half of seg4
    have h_seg1 := seg4_seg1_ftc H hz_re
    have h_arc := seg4_arc_ftc hz_re hc_lo
    have h_left := seg4_left_ftc hH hz_re h_lin_pos h_lin_lt_lo
    have hint_seg1 : IntervalIntegrable
        (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
        volume 0 (1/5) :=
      h_seg1.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
        ((seg4_ae_eq_h₀ H z₀).mono (fun t ht hm => (ht hm).symm)))
    have hint_arc : IntervalIntegrable
        (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
        volume (1/5) (3/5) :=
      h_arc.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
        ((seg4_ae_eq_h_arc H z₀).mono (fun t ht hm => (ht hm).symm)))
    have hint_left : IntervalIntegrable
        (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
        volume (3/5) (seg4T₀ H z₀.im - linDelta (seg1Speed H) ε) :=
      h_left.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
        ((seg4_ae_eq_h₃ H z₀ (by linarith) le_rfl (by linarith)).mono
          (fun t ht hm => (ht hm).symm)))
    exact (hint_seg1.trans hint_arc).trans hint_left
  hint_right := by
    intro ε hε hε_thr
    have hK_pos : 0 < seg1Speed H := seg1Speed_pos hH
    have h_lin_pos : 0 < linDelta (seg1Speed H) ε := linDelta_pos hK_pos hε
    have h_eps_top : ε < H - z₀.im :=
      lt_of_lt_of_le hε_thr (min_le_right _ _)
    have h_lin_lt_hi : linDelta (seg1Speed H) ε < 4/5 - seg4T₀ H z₀.im := by
      unfold linDelta
      rw [div_lt_iff₀ hK_pos, mul_comm, seg1Speed_mul_four_fifths_sub_t₀ hH]
      exact h_eps_top
    have h_t₀_lo : 3/5 < seg4T₀ H z₀.im := seg4T₀_gt_three_fifths hH hc_lo
    have h_t₀_hi : seg4T₀ H z₀.im < 4/5 := seg4T₀_lt_four_fifths hH hc_hi
    have h2 : 0 ≤ seg4T₀ H z₀.im + linDelta (seg1Speed H) ε := by linarith
    apply transfer_integrability z₀ (by linarith) h2 (le_refl 1) hγ
    have h_right := seg4_right_ftc hH hz_re h_lin_pos h_lin_lt_hi
    have h_seg5 := seg4_seg5_ftc H hc_hi
    have hint_right : IntervalIntegrable
        (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
        volume (seg4T₀ H z₀.im + linDelta (seg1Speed H) ε) (4/5) :=
      h_right.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
        ((seg4_ae_eq_h₃ H z₀ (by linarith) (by linarith) le_rfl).mono
          (fun t ht hm => (ht hm).symm)))
    have hint_seg5 : IntervalIntegrable
        (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
        volume (4/5) 1 :=
      h_seg5.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
        ((seg4_ae_eq_h₅ H z₀).mono (fun t ht hm => (ht hm).symm)))
    exact hint_right.trans hint_seg5
  h_limit := tendsto_const_nhds

end



