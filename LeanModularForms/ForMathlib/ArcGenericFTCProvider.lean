/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.BoundaryWindingArcProof
import LeanModularForms.ForMathlib.BoundaryWindingSeg1Proof
import LeanModularForms.ForMathlib.SegmentAnalysis
import LeanModularForms.ForMathlib.SegmentFTC
import LeanModularForms.ForMathlib.WindingWeightProofs

/-!
# `ArcFTCHyp` for the unit-circle arc at a generic angle

For `z₀ = exp(i·θ₀)` with `θ₀ ∈ (π/3, 2π/3) \ {π/2}`, this file constructs
the analytical FTC hypothesis needed by `BoundaryWindingArcProof`.

## Branch structure

- seg1 (right vertical): `log(h)` since `h.re = 1/2 - cos θ₀ > 0`.
- arc left (1/5 → t₀-δ): `log(h)` since `arg(h) ∈ (-π/6, π/6)` (re > 0).
- arc right (t₀+δ → 3/5): `log(-h)` since `-h.re = cos θ₀ - cos θ > 0`.
- seg4 (left vertical): `log(-h)` since `-h.re = 1/2 + cos θ₀ > 0`.
- seg5 (top): `log(h)` since `h.im = H - sin θ₀ > 0`.

The branch correction at the 4/5 junction (between `log(-h_seg4)` and
`log(h_seg5)`) gives `-π · I`, while all other junctions cancel by
junction equalities. The crossing contribution at `t₀` converges to `0`.

## Main results

* `arcFTCHyp_arc_generic` — full `ArcFTCHyp` at any non-elliptic, non-I
  arc point, axiom-clean.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ### Reference function on seg1 -/

private def arc_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((1/2 - z₀.re : ℝ) : ℂ) +
  ((H - 5 * t * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I

private lemma fdBoundary_sub_eq_arc_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) (ht : t ≤ 1/5) :
    fdBoundaryFun H t - z₀ = arc_h₀ H z₀ t := by
  simp only [fdBoundaryFun, ht, ite_true, arc_h₀]
  apply Complex.ext
  · simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
  · simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]

private lemma arc_h₀_continuous (H : ℝ) (z₀ : ℂ) : Continuous (arc_h₀ H z₀) := by
  unfold arc_h₀
  refine Continuous.add continuous_const ?_
  refine Continuous.mul ?_ continuous_const
  exact Complex.continuous_ofReal.comp (by fun_prop)

private lemma hasDerivAt_arc_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (arc_h₀ H z₀) (-(seg1Speed H : ℂ) * I) t := by
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

private lemma deriv_arc_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (arc_h₀ H z₀) t = -(seg1Speed H : ℂ) * I :=
  (hasDerivAt_arc_h₀ H z₀ t).deriv

/-- For arc z₀ with `θ₀ ∈ (π/3, 2π/3)`, `arc_h₀.re = 1/2 - cos θ₀ > 0`. -/
private lemma arc_h₀_slitPlane {H : ℝ} {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) (t : ℝ) :
    arc_h₀ H (exp (↑θ₀ * I)) t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  unfold arc_h₀
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero]
  rw [arcZ₀_re_eq]
  have hpi := Real.pi_pos
  have hθ₀ : θ₀ ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have hpi3 : (Real.pi / 3) ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have h_cos : Real.cos θ₀ < Real.cos (Real.pi / 3) :=
    Real.strictAntiOn_cos hpi3 hθ₀ h_lo
  rw [Real.cos_pi_div_three] at h_cos
  linarith

/-! ### Reference function on seg5 -/

private def arc_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((5 * t - 9/2 - z₀.re : ℝ) : ℂ) + ((H - z₀.im : ℝ) : ℂ) * I

private lemma fdBoundary_sub_eq_arc_h₅ (H : ℝ) (z₀ : ℂ) {t : ℝ} (ht : 4/5 < t) :
    fdBoundaryFun H t - z₀ = arc_h₅ H z₀ t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    show ¬t ≤ 4/5 from by linarith, ite_false, arc_h₅]
  apply Complex.ext
  · simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
  · simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]

private lemma arc_h₅_continuous (H : ℝ) (z₀ : ℂ) : Continuous (arc_h₅ H z₀) := by
  unfold arc_h₅
  refine Continuous.add ?_ continuous_const
  exact Complex.continuous_ofReal.comp (by fun_prop)

private lemma hasDerivAt_arc_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (arc_h₅ H z₀) (5 : ℂ) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((5 * s - 9/2 - z₀.re : ℝ) : ℂ)) 5 t := by
    have h_real : HasDerivAt (fun s : ℝ => 5 * s - 9/2 - z₀.re) 5 t :=
      ((((hasDerivAt_id t).const_mul 5).sub_const (9/2)).sub_const z₀.re).congr_deriv (by ring)
    exact (h_real.ofReal_comp).congr_deriv (by push_cast; ring)
  exact (h1.add_const _).congr_deriv (by ring)

private lemma deriv_arc_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (arc_h₅ H z₀) t = 5 :=
  (hasDerivAt_arc_h₅ H z₀ t).deriv

/-- For arc z₀ with `H > 1`, `arc_h₅.im = H - sin θ₀ > 0`. -/
private lemma arc_h₅_slitPlane {H : ℝ} (hH : 1 < H) {θ₀ : ℝ} (t : ℝ) :
    arc_h₅ H (exp (↑θ₀ * I)) t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  unfold arc_h₅
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
  rw [arcZ₀_im_eq]
  have := Real.sin_le_one θ₀
  intro h; linarith

/-! ### Reference function on seg4 -/

private def arc_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((-1/2 - z₀.re : ℝ) : ℂ) +
  ((Real.sqrt 3 / 2 + (5 * t - 3) * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I

private lemma fdBoundary_sub_eq_arc_h₃ (H : ℝ) (z₀ : ℂ) {t : ℝ}
    (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    fdBoundaryFun H t - z₀ = arc_h₃ H z₀ t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    ht4, ite_true, ite_false, arc_h₃]
  apply Complex.ext
  · simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.div_ofNat]
  · simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]

private lemma arc_h₃_continuous (H : ℝ) (z₀ : ℂ) : Continuous (arc_h₃ H z₀) := by
  unfold arc_h₃
  refine Continuous.add continuous_const ?_
  refine Continuous.mul ?_ continuous_const
  exact Complex.continuous_ofReal.comp (by fun_prop)

private lemma hasDerivAt_arc_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (arc_h₃ H z₀) ((seg1Speed H : ℂ) * I) t := by
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
    exact (h_real.ofReal_comp).congr_deriv (by push_cast; ring)
  exact ((hasDerivAt_const t (((-1/2 - z₀.re : ℝ) : ℂ))).add (h1.mul_const I)).congr_deriv
    (by ring)

private lemma deriv_arc_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (arc_h₃ H z₀) t = (seg1Speed H : ℂ) * I :=
  (hasDerivAt_arc_h₃ H z₀ t).deriv

/-- For arc z₀, `-arc_h₃.re = 1/2 + cos θ₀ > 0`. -/
private lemma neg_arc_h₃_slitPlane {H : ℝ} {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) (t : ℝ) :
    -(arc_h₃ H (exp (↑θ₀ * I)) t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  unfold arc_h₃
  simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero]
  rw [arcZ₀_re_eq]
  have hpi := Real.pi_pos
  have hθ₀ : θ₀ ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have h2pi3 : (2 * Real.pi / 3) ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have h_cos : Real.cos (2 * Real.pi / 3) < Real.cos θ₀ :=
    Real.strictAntiOn_cos hθ₀ h2pi3 h_hi
  have h_cos_2pi3 : Real.cos (2 * Real.pi / 3) = -1/2 := by
    rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  linarith

/-! ### Arc reference function -/

private def arc_h_arc (z₀ : ℂ) (t : ℝ) : ℂ :=
  exp (↑(fdArcAngle t) * I) - z₀

private lemma fdBoundary_sub_eq_arc_h_arc {H : ℝ} (z₀ : ℂ) {t : ℝ}
    (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t - z₀ = arc_h_arc z₀ t := by
  unfold arc_h_arc; rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2]

private lemma arc_h_arc_continuous (z₀ : ℂ) : Continuous (arc_h_arc z₀) := by
  unfold arc_h_arc
  exact (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp fdArcAngle_continuous).mul continuous_const)).sub
    continuous_const

private lemma hasDerivAt_arc_h_arc (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (arc_h_arc z₀)
      (↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I)) t := by
  unfold arc_h_arc
  have h1 : HasDerivAt fdArcAngle (5 * Real.pi / 6) t := by
    unfold fdArcAngle
    have hd1 : HasDerivAt (fun s : ℝ => Real.pi / 3 + (5 * s - 1) * (Real.pi / 6))
        (5 * (Real.pi / 6)) t := by
      have h := ((hasDerivAt_id t).const_mul (5 : ℝ)).sub_const 1
      have := (h.mul_const (Real.pi / 6)).const_add (Real.pi / 3)
      exact this.congr_deriv (by ring)
    exact hd1.congr_deriv (by ring)
  have h2 : HasDerivAt (fun s : ℝ => (↑(fdArcAngle s) : ℂ) * I)
      (↑(5 * Real.pi / 6) * I) t := by
    have := (h1.ofReal_comp).mul_const I
    exact this.congr_deriv (by push_cast; ring)
  have h3 : HasDerivAt (fun s : ℝ => exp ((↑(fdArcAngle s) : ℂ) * I))
      (↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I)) t := by
    have := h2.cexp
    exact this.congr_deriv (by ring)
  exact h3.sub_const z₀

private lemma deriv_arc_h_arc (z₀ : ℂ) (t : ℝ) :
    deriv (arc_h_arc z₀) t = ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I) :=
  (hasDerivAt_arc_h_arc z₀ t).deriv

/-- For arc z₀ and t < t₀ (left arc), `arc_h_arc z₀ t` has `re > 0`. The arg of
`(γ - z₀)` is `(θ + θ₀ - π)/2` where `θ < θ₀`, and this lies in `[-π/6, π/6)`. -/
private lemma arc_h_arc_left_slitPlane {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    {t : ℝ} (ht1 : 1/5 ≤ t) (ht_lt : t < arcT₀ θ₀) :
    arc_h_arc (exp (↑θ₀ * I)) t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  unfold arc_h_arc
  rw [exp_mul_I, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos, ← ofReal_sin]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one]
  -- Goal: cos (fdArcAngle t) - cos θ₀ > 0
  have hpi := Real.pi_pos
  have h_t_arc : fdArcAngle t < θ₀ := by
    have h := fdArcAngle_arcT₀ θ₀
    have h_mono : fdArcAngle t < fdArcAngle (arcT₀ θ₀) := by
      unfold fdArcAngle
      nlinarith
    rw [h] at h_mono
    exact h_mono
  have h_t_ge : Real.pi / 3 ≤ fdArcAngle t := by
    unfold fdArcAngle; nlinarith
  have h_t_Icc : fdArcAngle t ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have hθ₀_Icc : θ₀ ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have h_cos := Real.strictAntiOn_cos h_t_Icc hθ₀_Icc h_t_arc
  linarith

/-- For arc z₀ and t > t₀ (right arc), `-(arc_h_arc z₀ t)` has `re > 0`. -/
private lemma neg_arc_h_arc_right_slitPlane {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    {t : ℝ} (ht_gt : arcT₀ θ₀ < t) (ht3 : t ≤ 3/5) :
    -(arc_h_arc (exp (↑θ₀ * I)) t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  unfold arc_h_arc
  rw [exp_mul_I, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos, ← ofReal_sin]
  simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, mul_one]
  -- Goal: -(cos (fdArcAngle t) - cos θ₀) > 0, i.e., cos θ₀ > cos (fdArcAngle t)
  have hpi := Real.pi_pos
  have h_t_arc : θ₀ < fdArcAngle t := by
    have h := fdArcAngle_arcT₀ θ₀
    have h_mono : fdArcAngle (arcT₀ θ₀) < fdArcAngle t := by
      unfold fdArcAngle
      nlinarith
    rw [h] at h_mono
    exact h_mono
  have h_t_le : fdArcAngle t ≤ 2 * Real.pi / 3 := by
    unfold fdArcAngle; nlinarith
  have h_t_Icc : fdArcAngle t ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have hθ₀_Icc : θ₀ ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have h_cos := Real.strictAntiOn_cos hθ₀_Icc h_t_Icc h_t_arc
  linarith

/-! ### Per-segment FTC pieces -/

private lemma arc_seg1_ftc (H : ℝ) {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    IntervalIntegrable
      (fun t => deriv (arc_h₀ H (exp (↑θ₀ * I))) t / arc_h₀ H (exp (↑θ₀ * I)) t)
      volume 0 (1/5) ∧
    ∫ t in (0:ℝ)..(1/5),
        deriv (arc_h₀ H (exp (↑θ₀ * I))) t / arc_h₀ H (exp (↑θ₀ * I)) t =
      Complex.log (arc_h₀ H (exp (↑θ₀ * I)) (1/5)) -
      Complex.log (arc_h₀ H (exp (↑θ₀ * I)) 0) := by
  apply LogDerivFTCFM.ftc_log_on_segment (by norm_num : (0 : ℝ) ≤ 1/5)
    (arc_h₀_continuous H _).continuousOn
    (fun t _ => (hasDerivAt_arc_h₀ H _ t).differentiableAt)
    (by
      rw [show deriv (arc_h₀ H (exp (↑θ₀ * I))) =
        fun _ => -(seg1Speed H : ℂ) * I from funext (deriv_arc_h₀ H _)]
      exact continuousOn_const)
  intro t _
  exact arc_h₀_slitPlane h_lo h_hi t

private lemma arc_arc_left_ftc {H : ℝ} {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < arcT₀ θ₀ - 1/5) :
    IntervalIntegrable
      (fun t => deriv (arc_h_arc (exp (↑θ₀ * I))) t / arc_h_arc (exp (↑θ₀ * I)) t)
      volume (1/5) (arcT₀ θ₀ - δ) ∧
    ∫ t in (1/5 : ℝ)..(arcT₀ θ₀ - δ),
        deriv (arc_h_arc (exp (↑θ₀ * I))) t / arc_h_arc (exp (↑θ₀ * I)) t =
      Complex.log (arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - δ)) -
      Complex.log (arc_h_arc (exp (↑θ₀ * I)) (1/5)) := by
  apply LogDerivFTCFM.ftc_log_on_segment (by linarith : (1/5 : ℝ) ≤ arcT₀ θ₀ - δ)
    (arc_h_arc_continuous _).continuousOn
    (fun t _ => (hasDerivAt_arc_h_arc _ t).differentiableAt)
    (by
      have hcont : ContinuousOn
          (fun t : ℝ => ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I))
          (Icc (1/5) (arcT₀ θ₀ - δ)) :=
        Continuous.continuousOn (continuous_const.mul (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp fdArcAngle_continuous).mul continuous_const)))
      have h_eq : deriv (arc_h_arc (exp (↑θ₀ * I))) =
          fun t => ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I) :=
        funext (deriv_arc_h_arc _)
      rw [h_eq]; exact hcont)
  intro t ⟨ht1, ht_lt⟩
  exact arc_h_arc_left_slitPlane h_lo h_hi ht1 (by linarith)

private lemma arc_arc_right_ftc {H : ℝ} {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 3/5 - arcT₀ θ₀) :
    IntervalIntegrable
      (fun t => deriv (arc_h_arc (exp (↑θ₀ * I))) t / arc_h_arc (exp (↑θ₀ * I)) t)
      volume (arcT₀ θ₀ + δ) (3/5) ∧
    ∫ t in (arcT₀ θ₀ + δ)..(3/5 : ℝ),
        deriv (arc_h_arc (exp (↑θ₀ * I))) t / arc_h_arc (exp (↑θ₀ * I)) t =
      Complex.log (-(arc_h_arc (exp (↑θ₀ * I)) (3/5))) -
      Complex.log (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + δ))) := by
  apply LogDerivFTCFM.ftc_log_neg_on_segment (by linarith : arcT₀ θ₀ + δ ≤ 3/5)
    (arc_h_arc_continuous _).continuousOn
    (fun t _ => (hasDerivAt_arc_h_arc _ t).differentiableAt)
    (by
      have hcont : ContinuousOn
          (fun t : ℝ => ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I))
          (Icc (arcT₀ θ₀ + δ) (3/5)) :=
        Continuous.continuousOn (continuous_const.mul (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp fdArcAngle_continuous).mul continuous_const)))
      have h_eq : deriv (arc_h_arc (exp (↑θ₀ * I))) =
          fun t => ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I) :=
        funext (deriv_arc_h_arc _)
      rw [h_eq]; exact hcont)
  intro t ⟨ht_gt, ht3⟩
  exact neg_arc_h_arc_right_slitPlane h_lo h_hi (by linarith) ht3

private lemma arc_seg4_ftc (H : ℝ) {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    IntervalIntegrable
      (fun t => deriv (arc_h₃ H (exp (↑θ₀ * I))) t / arc_h₃ H (exp (↑θ₀ * I)) t)
      volume (3/5) (4/5) ∧
    ∫ t in (3/5 : ℝ)..(4/5),
        deriv (arc_h₃ H (exp (↑θ₀ * I))) t / arc_h₃ H (exp (↑θ₀ * I)) t =
      Complex.log (-(arc_h₃ H (exp (↑θ₀ * I)) (4/5))) -
      Complex.log (-(arc_h₃ H (exp (↑θ₀ * I)) (3/5))) := by
  apply LogDerivFTCFM.ftc_log_neg_on_segment (by norm_num : (3/5 : ℝ) ≤ 4/5)
    (arc_h₃_continuous H _).continuousOn
    (fun t _ => (hasDerivAt_arc_h₃ H _ t).differentiableAt)
    (by
      rw [show deriv (arc_h₃ H (exp (↑θ₀ * I))) =
        fun _ => (seg1Speed H : ℂ) * I from funext (deriv_arc_h₃ H _)]
      exact continuousOn_const)
  intro t _
  exact neg_arc_h₃_slitPlane h_lo h_hi t

private lemma arc_seg5_ftc {H : ℝ} (hH : 1 < H) {θ₀ : ℝ} :
    IntervalIntegrable
      (fun t => deriv (arc_h₅ H (exp (↑θ₀ * I))) t / arc_h₅ H (exp (↑θ₀ * I)) t)
      volume (4/5) 1 ∧
    ∫ t in (4/5 : ℝ)..(1 : ℝ),
        deriv (arc_h₅ H (exp (↑θ₀ * I))) t / arc_h₅ H (exp (↑θ₀ * I)) t =
      Complex.log (arc_h₅ H (exp (↑θ₀ * I)) 1) - Complex.log (arc_h₅ H (exp (↑θ₀ * I)) (4/5)) := by
  apply LogDerivFTCFM.ftc_log_on_segment (by norm_num : (4/5 : ℝ) ≤ 1)
    (arc_h₅_continuous H _).continuousOn
    (fun t _ => (hasDerivAt_arc_h₅ H _ t).differentiableAt)
    (by
      rw [show deriv (arc_h₅ H (exp (↑θ₀ * I))) =
        fun _ => (5 : ℂ) from funext (deriv_arc_h₅ H _)]
      exact continuousOn_const)
  intro t _
  exact arc_h₅_slitPlane hH t

/-! ### Junction equalities -/

private lemma arc_junction_15 (H : ℝ) (z₀ : ℂ) :
    arc_h₀ H z₀ (1/5) = arc_h_arc z₀ (1/5) := by
  unfold arc_h₀ arc_h_arc
  have hθ : (fdArcAngle (1/5) : ℝ) = Real.pi / 3 := by unfold fdArcAngle; ring
  rw [hθ, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  apply Complex.ext
  · simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
  · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero,
      zero_sub]
    ring

private lemma arc_junction_35 (H : ℝ) (z₀ : ℂ) :
    arc_h_arc z₀ (3/5) = arc_h₃ H z₀ (3/5) := by
  unfold arc_h_arc arc_h₃
  have hθ : (fdArcAngle (3/5) : ℝ) = 2 * Real.pi / 3 := by unfold fdArcAngle; ring
  rw [hθ, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, neg_zero,
      Complex.neg_re, Complex.one_re, Complex.div_ofNat]
    ring
  · simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero,
      Complex.neg_im, Complex.one_im, Complex.div_ofNat]
    ring

private lemma arc_junction_45 (H : ℝ) (z₀ : ℂ) :
    arc_h₃ H z₀ (4/5) = arc_h₅ H z₀ (4/5) := by
  unfold arc_h₃ arc_h₅
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    ring

private lemma arc_closed (H : ℝ) (z₀ : ℂ) :
    arc_h₀ H z₀ 0 = arc_h₅ H z₀ 1 := by
  unfold arc_h₀ arc_h₅
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    ring

/-! ### Branch correction at t = 4/5 -/

/-- For arc z₀ with `θ₀ ∈ (π/3, 2π/3)` and `H > 1`, `arc_h₃(4/5) = arc_h₅(4/5)`
lies in the upper-left quadrant (re < 0, im > 0). Hence
`log(-h(4/5)) - log(h(4/5)) = -π · I`. -/
private lemma arc_branch_correction_45 {H : ℝ} (hH : 1 < H) {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    Complex.log (-(arc_h₃ H (exp (↑θ₀ * I)) (4/5))) -
    Complex.log (arc_h₅ H (exp (↑θ₀ * I)) (4/5)) = -(↑Real.pi * I) := by
  have h_eq : arc_h₃ H (exp (↑θ₀ * I)) (4/5) = arc_h₅ H (exp (↑θ₀ * I)) (4/5) :=
    arc_junction_45 H _
  rw [h_eq]
  -- Now compute log(-w) - log(w) where w = arc_h₅(4/5)
  -- w has re < 0, im > 0 (upper-left quadrant)
  -- Specifically: w = -1 - cos θ₀ + (H - sin θ₀)*I... wait
  -- arc_h₅(4/5) = ((5*(4/5) - 9/2 - z₀.re : ℝ) : ℂ) + ((H - z₀.im : ℝ) : ℂ) * I
  --            = ((4 - 9/2 - cos θ₀) : ℂ) + ((H - sin θ₀) : ℂ) * I
  --            = ((-1/2 - cos θ₀) : ℂ) + ((H - sin θ₀) : ℂ) * I
  have h_val : arc_h₅ H (exp (↑θ₀ * I)) (4/5) =
      ((-1/2 - Real.cos θ₀ : ℝ) : ℂ) + ((H - Real.sin θ₀ : ℝ) : ℂ) * I := by
    unfold arc_h₅
    rw [arcZ₀_re_eq, arcZ₀_im_eq]
    have h_eq : ((5 * (4/5) - 9/2 - Real.cos θ₀ : ℝ) : ℂ) =
        ((-1/2 - Real.cos θ₀ : ℝ) : ℂ) := by push_cast; ring
    rw [h_eq]
  rw [h_val]
  -- Apply Complex.log_neg_eq: log(-z) = log(z) - iπ (when z.im > 0)
  -- Or compute directly
  set w := ((-1/2 - Real.cos θ₀ : ℝ) : ℂ) + ((H - Real.sin θ₀ : ℝ) : ℂ) * I with hw_def
  have hpi := Real.pi_pos
  have hθ₀_Icc : θ₀ ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have h2pi3 : (2 * Real.pi / 3) ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have h_cos_2pi3 : Real.cos (2 * Real.pi / 3) = -1/2 := by
    rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  have h_cos : Real.cos (2 * Real.pi / 3) < Real.cos θ₀ :=
    Real.strictAntiOn_cos hθ₀_Icc h2pi3 h_hi
  rw [h_cos_2pi3] at h_cos
  have h_w_re : w.re = -1/2 - Real.cos θ₀ := by
    rw [hw_def]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero]
    ring
  have h_w_im : w.im = H - Real.sin θ₀ := by
    rw [hw_def]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
    ring
  have h_re_neg : w.re < 0 := by rw [h_w_re]; linarith
  have h_im_pos : w.im > 0 := by
    rw [h_w_im]
    have := Real.sin_le_one θ₀
    linarith
  -- For z with re < 0 and im > 0, log(-z) = log(z) - iπ
  have h_w_ne : w ≠ 0 := by intro h; rw [h] at h_re_neg; simp at h_re_neg
  have h_neg_w_ne : -w ≠ 0 := neg_ne_zero.mpr h_w_ne
  have h_arg_neg : (-w).arg = w.arg - Real.pi :=
    Complex.arg_neg_eq_arg_sub_pi_of_im_pos h_im_pos
  have h_log_neg : Complex.log (-w) = Complex.log w - ↑Real.pi * I := by
    rw [Complex.log, Complex.log, h_arg_neg, norm_neg]
    push_cast
    ring
  rw [h_log_neg]
  ring

/-! ### A.e. equalities -/

private lemma arc_ae_eq_h₀ (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) (1/5) →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (arc_h₀ H z₀) t / arc_h₀ H z₀ t := by
  have h_excl : ({1/5} : Set ℝ)ᶜ ∈ ae volume :=
    compl_mem_ae_iff.mpr (measure_singleton _)
  filter_upwards [h_excl] with t ht_ne ht_mem
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1/5)] at ht_mem
  have ht_lt : t < 1/5 :=
    lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (Set.mem_singleton_iff.mpr h))
  have h_eq : fdBoundaryFun H t - z₀ = arc_h₀ H z₀ t :=
    fdBoundary_sub_eq_arc_h₀ H z₀ t (le_of_lt ht_lt)
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] arc_h₀ H z₀ :=
    Filter.eventually_of_mem (Iio_mem_nhds ht_lt)
      (fun s hs => fdBoundary_sub_eq_arc_h₀ H z₀ s (le_of_lt hs))
  have h_deriv : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (arc_h₀ H z₀) t :=
    h_evEq.deriv_eq
  have h_deriv_sub : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (fdBoundaryFun H) t :=
    deriv_sub_const (f := fdBoundaryFun H) _
  rw [h_eq, ← h_deriv_sub, h_deriv, div_eq_mul_inv, mul_comm]

private lemma arc_ae_eq_h_arc (H : ℝ) (z₀ : ℂ) {a b : ℝ} (hab : a ≤ b)
    (ha_ge : 1/5 ≤ a) (hb_le : b ≤ 3/5) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (arc_h_arc z₀) t / arc_h_arc z₀ t := by
  have h_excl : ({a, b} : Set ℝ)ᶜ ∈ ae volume := by
    refine compl_mem_ae_iff.mpr ?_
    exact (Set.toFinite ({a, b} : Set ℝ)).measure_zero volume
  filter_upwards [h_excl] with t ht_ne ht_mem
  rw [uIoc_of_le hab] at ht_mem
  have ht_lt_b : t < b :=
    lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (Set.mem_insert_iff.mpr (Or.inr h)))
  have ht_gt_a : a < t := ht_mem.1
  have ht1 : 1/5 < t := lt_of_le_of_lt ha_ge ht_gt_a
  have ht3_lt : t < 3/5 := lt_of_lt_of_le ht_lt_b hb_le
  have h_eq : fdBoundaryFun H t - z₀ = arc_h_arc z₀ t :=
    fdBoundary_sub_eq_arc_h_arc z₀ ht1 (le_of_lt ht3_lt)
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] arc_h_arc z₀ :=
    Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht3_lt))
      fun s ⟨hs1, hs3⟩ => fdBoundary_sub_eq_arc_h_arc z₀ hs1 (le_of_lt hs3)
  have h_deriv : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (arc_h_arc z₀) t :=
    h_evEq.deriv_eq
  have h_deriv_sub : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (fdBoundaryFun H) t :=
    deriv_sub_const (f := fdBoundaryFun H) _
  rw [h_eq, ← h_deriv_sub, h_deriv, div_eq_mul_inv, mul_comm]

private lemma arc_ae_eq_h₃ (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (3/5 : ℝ) (4/5) →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (arc_h₃ H z₀) t / arc_h₃ H z₀ t := by
  have h_excl : ({4/5} : Set ℝ)ᶜ ∈ ae volume :=
    compl_mem_ae_iff.mpr (measure_singleton _)
  filter_upwards [h_excl] with t ht_ne ht_mem
  rw [uIoc_of_le (by norm_num : (3/5 : ℝ) ≤ 4/5)] at ht_mem
  have ht3 : 3/5 < t := ht_mem.1
  have ht4_lt : t < 4/5 :=
    lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (Set.mem_singleton_iff.mpr h))
  have h_eq : fdBoundaryFun H t - z₀ = arc_h₃ H z₀ t :=
    fdBoundary_sub_eq_arc_h₃ H z₀ ht3 (le_of_lt ht4_lt)
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] arc_h₃ H z₀ :=
    Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht3) (Iio_mem_nhds ht4_lt))
      fun s ⟨hs3, hs4⟩ => fdBoundary_sub_eq_arc_h₃ H z₀ hs3 (le_of_lt hs4)
  have h_deriv : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (arc_h₃ H z₀) t :=
    h_evEq.deriv_eq
  have h_deriv_sub : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (fdBoundaryFun H) t :=
    deriv_sub_const (f := fdBoundaryFun H) _
  rw [h_eq, ← h_deriv_sub, h_deriv, div_eq_mul_inv, mul_comm]

private lemma arc_ae_eq_h₅ (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (4/5 : ℝ) 1 →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (arc_h₅ H z₀) t / arc_h₅ H z₀ t := by
  refine ae_of_all _ (fun t ht_mem => ?_)
  rw [uIoc_of_le (by norm_num : (4/5 : ℝ) ≤ 1)] at ht_mem
  have ht4 : 4/5 < t := ht_mem.1
  have h_eq : fdBoundaryFun H t - z₀ = arc_h₅ H z₀ t :=
    fdBoundary_sub_eq_arc_h₅ H z₀ ht4
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] arc_h₅ H z₀ :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht4)
      fun s hs => fdBoundary_sub_eq_arc_h₅ H z₀ hs
  have h_deriv : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (arc_h₅ H z₀) t :=
    h_evEq.deriv_eq
  have h_deriv_sub : deriv (fun s => fdBoundaryFun H s - z₀) t = deriv (fdBoundaryFun H) t :=
    deriv_sub_const (f := fdBoundaryFun H) _
  rw [h_eq, ← h_deriv_sub, h_deriv, div_eq_mul_inv, mul_comm]

/-! ### Telescope: the trimmed integral for arc crossings -/

set_option maxHeartbeats 400000 in
/-- The trimmed integral for an arc crossing equals
`log(h_arc(t₀-δ)) - log(-h_arc(t₀+δ)) + (-π·I)`. The first part is the
"crossing contribution" (which → 0 as δ → 0), and the second is the branch
correction at the 4/5 junction. -/
theorem fdBoundary_ftc_telescope_arc_aux {H : ℝ} (hH : 1 < H) {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_lo : δ < arcT₀ θ₀ - 1/5)
    (hδ_lt_hi : δ < 3/5 - arcT₀ θ₀) :
    (∫ t in (0 : ℝ)..(arcT₀ θ₀ - δ),
        (fdBoundaryFun H t - exp (↑θ₀ * I))⁻¹ * deriv (fdBoundaryFun H) t) +
    (∫ t in (arcT₀ θ₀ + δ)..(1 : ℝ),
        (fdBoundaryFun H t - exp (↑θ₀ * I))⁻¹ * deriv (fdBoundaryFun H) t) =
    Complex.log (arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - δ)) -
    Complex.log (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + δ))) +
    (-(↑Real.pi * I)) := by
  set z₀ := exp (↑θ₀ * I) with hz₀_def
  have ht₀_lo : 1/5 < arcT₀ θ₀ := arcT₀_gt_one_fifth h_lo
  have ht₀_hi : arcT₀ θ₀ < 3/5 := arcT₀_lt_three_fifths h_hi
  have h_seg1 := arc_seg1_ftc H h_lo h_hi
  have h_arc_left := arc_arc_left_ftc (H := H) h_lo h_hi hδ_pos hδ_lt_lo
  have h_arc_right := arc_arc_right_ftc (H := H) h_lo h_hi hδ_pos hδ_lt_hi
  have h_seg4 := arc_seg4_ftc H h_lo h_hi
  have h_seg5 := arc_seg5_ftc hH (θ₀ := θ₀)
  have h_int_seg1 :
      ∫ t in (0:ℝ)..(1/5), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      Complex.log (arc_h₀ H z₀ (1/5)) - Complex.log (arc_h₀ H z₀ 0) := by
    rw [intervalIntegral.integral_congr_ae (arc_ae_eq_h₀ H z₀)]
    exact h_seg1.2
  have h_int_arc_left :
      ∫ t in (1/5:ℝ)..(arcT₀ θ₀ - δ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      Complex.log (arc_h_arc z₀ (arcT₀ θ₀ - δ)) - Complex.log (arc_h_arc z₀ (1/5)) := by
    rw [intervalIntegral.integral_congr_ae
      (arc_ae_eq_h_arc H z₀ (by linarith) le_rfl (by linarith))]
    exact h_arc_left.2
  have h_int_arc_right :
      ∫ t in (arcT₀ θ₀ + δ)..(3/5:ℝ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      Complex.log (-(arc_h_arc z₀ (3/5))) - Complex.log (-(arc_h_arc z₀ (arcT₀ θ₀ + δ))) := by
    rw [intervalIntegral.integral_congr_ae
      (arc_ae_eq_h_arc H z₀ (by linarith) (by linarith) le_rfl)]
    exact h_arc_right.2
  have h_int_seg4 :
      ∫ t in (3/5 : ℝ)..(4/5), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      Complex.log (-(arc_h₃ H z₀ (4/5))) - Complex.log (-(arc_h₃ H z₀ (3/5))) := by
    rw [intervalIntegral.integral_congr_ae (arc_ae_eq_h₃ H z₀)]
    exact h_seg4.2
  have h_int_seg5 :
      ∫ t in (4/5 : ℝ)..(1 : ℝ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      Complex.log (arc_h₅ H z₀ 1) - Complex.log (arc_h₅ H z₀ (4/5)) := by
    rw [intervalIntegral.integral_congr_ae (arc_ae_eq_h₅ H z₀)]
    exact h_seg5.2
  -- Integrability for splitting
  have hint_seg1 : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume 0 (1/5) :=
    h_seg1.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((arc_ae_eq_h₀ H z₀).mono (fun t ht hm => (ht hm).symm)))
  have hint_arc_left : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (1/5) (arcT₀ θ₀ - δ) :=
    h_arc_left.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((arc_ae_eq_h_arc H z₀ (by linarith) le_rfl (by linarith)).mono
        (fun t ht hm => (ht hm).symm)))
  have hint_arc_right : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (arcT₀ θ₀ + δ) (3/5) :=
    h_arc_right.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((arc_ae_eq_h_arc H z₀ (by linarith) (by linarith) le_rfl).mono
        (fun t ht hm => (ht hm).symm)))
  have hint_seg4 : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (3/5) (4/5) :=
    h_seg4.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((arc_ae_eq_h₃ H z₀).mono (fun t ht hm => (ht hm).symm)))
  have hint_seg5 : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (4/5) 1 :=
    h_seg5.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((arc_ae_eq_h₅ H z₀).mono (fun t ht hm => (ht hm).symm)))
  -- Splits
  have h_split_left :
      ∫ t in (0 : ℝ)..(arcT₀ θ₀ - δ),
        (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      (∫ t in (0:ℝ)..(1/5), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (1/5:ℝ)..(arcT₀ θ₀ - δ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) := by
    have h := intervalIntegral.integral_add_adjacent_intervals hint_seg1 hint_arc_left
    linear_combination -h
  have h_split_right :
      ∫ t in (arcT₀ θ₀ + δ)..(1 : ℝ),
        (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      (∫ t in (arcT₀ θ₀ + δ)..(3/5:ℝ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (3/5:ℝ)..(4/5),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (4/5:ℝ)..(1:ℝ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals hint_arc_right hint_seg4
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hint_arc_right.trans hint_seg4) hint_seg5
    linear_combination -h1 - h2
  rw [h_split_left, h_split_right, h_int_seg1, h_int_arc_left, h_int_arc_right,
      h_int_seg4, h_int_seg5,
      arc_junction_15 H z₀, arc_junction_35 H z₀, arc_junction_45 H z₀,
      arc_closed H z₀]
  -- Use the branch correction. After arc_junction_45, the seg4 final term becomes
  -- log(-arc_h₅(4/5)). Restate the branch correction in those terms:
  have h_branch_45 : Complex.log (-(arc_h₅ H z₀ (4/5))) -
      Complex.log (arc_h₅ H z₀ (4/5)) = -(↑Real.pi * I) := by
    have h_orig := arc_branch_correction_45 hH h_lo h_hi
    have h_eq : arc_h₃ H z₀ (4/5) = arc_h₅ H z₀ (4/5) := arc_junction_45 H z₀
    rwa [h_eq] at h_orig
  -- Algebra: collect terms, junction values cancel, branch correction at 4/5 gives -π·I
  linear_combination h_branch_45

/-- Helper: for `a, b : ℂ` with both having positive real part,
`log(a/b) = log(a) - log(b)`. -/
private lemma log_div_of_re_posFM {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Complex.log (a / b) = Complex.log a - Complex.log b := by
  have ha_ne : a ≠ 0 := by intro h; simp [h] at ha
  have hb_ne : b ≠ 0 := by intro h; simp [h] at hb
  have hb_inv_ne : b⁻¹ ≠ 0 := inv_ne_zero hb_ne
  rw [div_eq_mul_inv]
  have hb_arg_ne_pi : b.arg ≠ Real.pi := by
    intro h; have := Complex.arg_eq_pi_iff.mp h; linarith [this.1]
  have hb_inv_arg : b⁻¹.arg = -b.arg := by
    rw [Complex.arg_inv]; simp [hb_arg_ne_pi]
  have ha_abs_arg : |a.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha)
  have hb_abs_arg : |b.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  have hbi_abs_arg : |b⁻¹.arg| < Real.pi / 2 := by
    rw [hb_inv_arg, abs_neg]; exact hb_abs_arg
  have h_sum : a.arg + b⁻¹.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · linarith [abs_lt.mp ha_abs_arg, abs_lt.mp hbi_abs_arg]
    · linarith [abs_lt.mp ha_abs_arg, abs_lt.mp hbi_abs_arg]
  rw [Complex.log_mul ha_ne hb_inv_ne h_sum, Complex.log_inv b hb_arg_ne_pi]
  ring

/-! ### Ratio identity for the arc crossing -/

/-- The ratio `(h_arc(t₀-δ)) / (-h_arc(t₀+δ)) = exp(-i·5π/6·δ)`.

By the half-angle factoring: both numerator and denominator factor as
`exp(iθ₀) * (exp(∓i·5πδ/6) - 1)`, and the ratio simplifies to `exp(-i·5πδ/6)`. -/
private lemma arc_h_arc_ratio_eq {θ₀ : ℝ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_small : δ * (5 * Real.pi / 6) < Real.pi) :
    arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - δ) /
      (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + δ))) =
      exp (↑(-(5 * Real.pi / 6 * δ)) * I) := by
  unfold arc_h_arc
  have h_m : fdArcAngle (arcT₀ θ₀ - δ) = θ₀ - 5 * Real.pi / 6 * δ := by
    have h := fdArcAngle_arcT₀ θ₀
    unfold fdArcAngle at h ⊢
    linarith
  have h_p : fdArcAngle (arcT₀ θ₀ + δ) = θ₀ + 5 * Real.pi / 6 * δ := by
    have h := fdArcAngle_arcT₀ θ₀
    unfold fdArcAngle at h ⊢
    linarith
  rw [h_m, h_p]
  have hφ_pos : (0 : ℝ) < 5 * Real.pi / 6 * δ := by positivity
  have hφ_lt_pi : 5 * Real.pi / 6 * δ < Real.pi := by
    linarith [hδ_small, mul_comm δ (5 * Real.pi / 6)]
  have h_left : (↑(θ₀ - 5 * Real.pi / 6 * δ) * I : ℂ) =
      (↑θ₀ * I) - (↑(5 * Real.pi / 6 * δ) * I) := by push_cast; ring
  have h_right : (↑(θ₀ + 5 * Real.pi / 6 * δ) * I : ℂ) =
      (↑θ₀ * I) + (↑(5 * Real.pi / 6 * δ) * I) := by push_cast; ring
  have h_neg : (↑(-(5 * Real.pi / 6 * δ)) * I : ℂ) =
      -(↑(5 * Real.pi / 6 * δ) * I) := by push_cast; ring
  rw [h_left, h_right, h_neg, Complex.exp_sub, Complex.exp_add, Complex.exp_neg]
  -- Set z := exp(iθ₀), w := exp(i·5π/6·δ)
  set z := exp (↑θ₀ * I) with hz_def
  set w := exp (↑(5 * Real.pi / 6 * δ) * I) with hw_def
  have hz_ne : z ≠ 0 := exp_ne_zero _
  have hw_ne : w ≠ 0 := exp_ne_zero _
  have hw_ne_one : w ≠ 1 := by
    intro h
    have him := congr_arg Complex.im h
    rw [hw_def, exp_ofReal_mul_I_im, one_im] at him
    linarith [Real.sin_pos_of_pos_of_lt_pi hφ_pos hφ_lt_pi]
  -- Goal: (z/w - z) / -(z*w - z) = w⁻¹
  have hzw_sub_ne : z * w - z ≠ 0 := by
    intro h
    apply hw_ne_one
    have h1 : z * (w - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h1 with hz | hw
    · exact absurd hz hz_ne
    · exact sub_eq_zero.mp hw
  rw [div_eq_iff (neg_ne_zero.mpr hzw_sub_ne)]
  field_simp
  ring

/-! ### Log diff tends to 0 -/

/-- As δ → 0+, `log(arc_h_arc(t₀-δ)) - log(-arc_h_arc(t₀+δ)) → 0`. -/
private lemma arc_log_diff_tendsto {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    Tendsto (fun δ => Complex.log (arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - δ)) -
        Complex.log (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + δ))))
      (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  have ht₀_lo : 1/5 < arcT₀ θ₀ := arcT₀_gt_one_fifth h_lo
  have ht₀_hi : arcT₀ θ₀ < 3/5 := arcT₀_lt_three_fifths h_hi
  -- Auxiliary: log ratio → 0 (since ratio = exp(-i·5π/6·δ) → 1 → log 1 = 0)
  have h_ratio_tendsto : Tendsto
      (fun δ : ℝ => Complex.log (cexp (↑(-(5 * Real.pi / 6 * δ)) * I)))
      (𝓝[>] 0) (𝓝 0) := by
    have hcont : ContinuousAt
        (fun δ : ℝ => Complex.log (cexp (↑(-(5 * Real.pi / 6 * δ)) * I))) 0 := by
      have h1 : (↑(-(5 * Real.pi / 6 * (0 : ℝ))) * I : ℂ) = 0 := by push_cast; ring
      have h_exp_val : cexp (↑(-(5 * Real.pi / 6 * (0 : ℝ))) * I) = 1 := by
        rw [h1]; exact Complex.exp_zero
      have h_in_slit : cexp (↑(-(5 * Real.pi / 6 * (0 : ℝ))) * I) ∈ Complex.slitPlane := by
        rw [h_exp_val]; exact Complex.one_mem_slitPlane
      have h_inner_cont : ContinuousAt
          (fun δ : ℝ => cexp (↑(-(5 * Real.pi / 6 * δ)) * I)) 0 :=
        Complex.continuous_exp.continuousAt.comp
          ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const).continuousAt
      exact h_inner_cont.clog h_in_slit
    have h_val_zero : Complex.log (cexp (↑(-(5 * Real.pi / 6 * (0 : ℝ))) * I)) = 0 := by
      have h1 : (↑(-(5 * Real.pi / 6 * (0 : ℝ))) * I : ℂ) = 0 := by push_cast; ring
      rw [h1, Complex.exp_zero, Complex.log_one]
    have htendsto : Tendsto
        (fun δ : ℝ => Complex.log (cexp (↑(-(5 * Real.pi / 6 * δ)) * I)))
        (𝓝 0) (𝓝 (Complex.log (cexp (↑(-(5 * Real.pi / 6 * (0 : ℝ))) * I)))) := hcont.tendsto
    rw [h_val_zero] at htendsto
    exact htendsto.mono_left nhdsWithin_le_nhds
  -- Need to stay within arc interval: δ must be less than min(t₀ - 1/5, 3/5 - t₀)
  set gap := min (arcT₀ θ₀ - 1/5) (3/5 - arcT₀ θ₀) with h_gap_def
  have h_gap_pos : 0 < gap := lt_min (by linarith) (by linarith)
  have h_gap_le_fifth : gap ≤ 1/5 := by
    show min (arcT₀ θ₀ - 1/5) (3/5 - arcT₀ θ₀) ≤ 1/5
    rcases le_total (arcT₀ θ₀ - 1/5) (3/5 - arcT₀ θ₀) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  -- On a neighborhood of 0+ (below gap), the log diff equals the log of the ratio
  have h_eventually_eq : ∀ᶠ δ in (𝓝[>] (0 : ℝ)),
      Complex.log (cexp (↑(-(5 * Real.pi / 6 * δ)) * I)) =
      Complex.log (arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - δ)) -
      Complex.log (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + δ))) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds h_gap_pos] with δ hδ_lt hδ_pos
    rw [mem_Ioi] at hδ_pos; rw [mem_Iio] at hδ_lt
    have h_δ_lt_gap_l : δ < arcT₀ θ₀ - 1/5 := lt_of_lt_of_le hδ_lt (min_le_left _ _)
    have h_δ_lt_gap_r : δ < 3/5 - arcT₀ θ₀ := lt_of_lt_of_le hδ_lt (min_le_right _ _)
    have h_δ_lt_fifth : δ < 1/5 := lt_of_lt_of_le hδ_lt h_gap_le_fifth
    have hδ_small : δ * (5 * Real.pi / 6) < Real.pi := by
      have : δ * (5 * Real.pi / 6) < (1/5) * (5 * Real.pi / 6) :=
        mul_lt_mul_of_pos_right h_δ_lt_fifth (by positivity)
      have h_simp : (1/5 : ℝ) * (5 * Real.pi / 6) = Real.pi / 6 := by ring
      linarith [h_simp, Real.pi_pos]
    have h_ratio := arc_h_arc_ratio_eq (θ₀ := θ₀) hδ_pos hδ_small
    -- Verify the left and right arc endpoints are in slitPlane via re > 0
    have h_a_re : 0 < (arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - δ)).re := by
      -- Directly prove: re = cos(fdArcAngle (t₀-δ)) - cos(θ₀) > 0
      show 0 < (arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - δ)).re
      unfold arc_h_arc
      rw [exp_mul_I, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos, ← ofReal_sin]
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, mul_one]
      have h_t_arc : fdArcAngle (arcT₀ θ₀ - δ) < θ₀ := by
        have h := fdArcAngle_arcT₀ θ₀
        unfold fdArcAngle at h ⊢
        nlinarith
      have h_t_ge : Real.pi / 3 ≤ fdArcAngle (arcT₀ θ₀ - δ) := by
        unfold fdArcAngle; nlinarith
      have h_t_Icc : fdArcAngle (arcT₀ θ₀ - δ) ∈ Icc (0 : ℝ) Real.pi :=
        ⟨by linarith, by linarith⟩
      have hθ₀_Icc : θ₀ ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
      have h_cos := Real.strictAntiOn_cos h_t_Icc hθ₀_Icc h_t_arc
      linarith
    have h_b_re : 0 < (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + δ))).re := by
      unfold arc_h_arc
      rw [exp_mul_I, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos, ← ofReal_sin]
      simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, mul_one]
      have hpi := Real.pi_pos
      have h_t_arc : θ₀ < fdArcAngle (arcT₀ θ₀ + δ) := by
        have h := fdArcAngle_arcT₀ θ₀
        unfold fdArcAngle at h ⊢
        nlinarith
      have h_t_le : fdArcAngle (arcT₀ θ₀ + δ) ≤ 2 * Real.pi / 3 := by
        unfold fdArcAngle; nlinarith
      have h_t_Icc : fdArcAngle (arcT₀ θ₀ + δ) ∈ Icc (0 : ℝ) Real.pi :=
        ⟨by linarith, by linarith⟩
      have hθ₀_Icc : θ₀ ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
      have h_cos := Real.strictAntiOn_cos hθ₀_Icc h_t_Icc h_t_arc
      linarith
    rw [← log_div_of_re_posFM h_a_re h_b_re]
    rw [h_ratio]
  exact h_ratio_tendsto.congr' h_eventually_eq

/-! ### `arcsinDelta` tendsto helper -/

private lemma arc_arcsinDelta_tendsto :
    Tendsto arcsinDelta (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have : arcsinDelta = fun ε => 12 / (5 * Real.pi) * Real.arcsin (ε / 2) := rfl
    rw [this]
    have hcont : ContinuousAt (fun ε : ℝ =>
        12 / (5 * Real.pi) * Real.arcsin (ε / 2)) 0 := by
      exact continuousAt_const.mul
        (Real.continuous_arcsin.continuousAt.comp (continuousAt_id.div_const 2))
    convert hcont.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp only [Real.arcsin_zero, mul_zero, zero_div]
  · rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0:ℝ) < 1 from by norm_num)] with ε _ hε
    exact mem_Ioi.mpr (arcsinDelta_pos (by rwa [mem_Ioi] at hε))

/-! ### Arc E function and its limit -/

private def arc_E (θ₀ : ℝ) (ε : ℝ) : ℂ :=
  Complex.log (arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - arcsinDelta ε)) -
    Complex.log (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + arcsinDelta ε))) +
    (-(↑Real.pi * I))

private lemma arc_E_tendsto {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    Tendsto (arc_E θ₀) (𝓝[>] 0) (𝓝 (-(↑Real.pi * I))) := by
  unfold arc_E
  have h_inner := arc_log_diff_tendsto h_lo h_hi
  have h_comp : Tendsto (fun ε : ℝ =>
      Complex.log (arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - arcsinDelta ε)) -
      Complex.log (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + arcsinDelta ε))))
      (𝓝[>] 0) (𝓝 0) :=
    h_inner.comp arc_arcsinDelta_tendsto
  have := h_comp.add (tendsto_const_nhds : Tendsto (fun _ : ℝ => -(↑Real.pi * I))
    (𝓝[>] 0) (𝓝 (-(↑Real.pi * I))))
  simpa using this

/-! ### Final assembly: the ArcFTCHyp at a generic arc point -/

/-! ### Helpers for ArcFTCHyp fields -/

private lemma arc_h_ftc_helper {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {θ₀ : ℝ} (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    (ε : ℝ) (hε : 0 < ε) (hε_thr : ε < arcThreshold H θ₀) :
    (∫ t in (0 : ℝ)..(arcT₀ θ₀ - arcsinDelta ε),
        (γ.toPath.extend t - exp (↑θ₀ * I))⁻¹ * deriv γ.toPath.extend t) +
    (∫ t in (arcT₀ θ₀ + arcsinDelta ε)..1,
        (γ.toPath.extend t - exp (↑θ₀ * I))⁻¹ * deriv γ.toPath.extend t) =
    arc_E θ₀ ε := by
  have h_δ_pos : 0 < arcsinDelta ε := arcsinDelta_pos hε
  have h_lt_gap : arcsinDelta ε < arcGap θ₀ :=
    arcsinDelta_lt_arcGap h_lo h_hi hε hε_thr
  have h_gap_lo : arcGap θ₀ ≤ arcT₀ θ₀ - 1/5 := min_le_left _ _
  have h_gap_hi : arcGap θ₀ ≤ 3/5 - arcT₀ θ₀ := min_le_right _ _
  have h_δ_lt_lo : arcsinDelta ε < arcT₀ θ₀ - 1/5 := lt_of_lt_of_le h_lt_gap h_gap_lo
  have h_δ_lt_hi : arcsinDelta ε < 3/5 - arcT₀ θ₀ := lt_of_lt_of_le h_lt_gap h_gap_hi
  have h_t₀_lo : (1/5 : ℝ) < arcT₀ θ₀ := arcT₀_gt_one_fifth h_lo
  have h_t₀_hi : arcT₀ θ₀ < 3/5 := arcT₀_lt_three_fifths h_hi
  rw [transfer_integral (exp (↑θ₀ * I)) (by linarith) (le_refl 0) (by linarith) hγ,
      transfer_integral (exp (↑θ₀ * I)) (by linarith) (by linarith) (le_refl 1) hγ]
  unfold arc_E
  exact fdBoundary_ftc_telescope_arc_aux hH h_lo h_hi h_δ_pos h_δ_lt_lo h_δ_lt_hi

set_option maxHeartbeats 2000000 in
private lemma arc_hint_left_helper {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {θ₀ : ℝ} (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    (ε : ℝ) (hε : 0 < ε) (hε_thr : ε < arcThreshold H θ₀) :
    IntervalIntegrable
      (fun t => (γ.toPath.extend t - exp (↑θ₀ * I))⁻¹ * deriv γ.toPath.extend t)
      volume 0 (arcT₀ θ₀ - arcsinDelta ε) := by
  have h_δ_pos : 0 < arcsinDelta ε := arcsinDelta_pos hε
  have h_lt_gap : arcsinDelta ε < arcGap θ₀ :=
    arcsinDelta_lt_arcGap h_lo h_hi hε hε_thr
  have h_gap_lo : arcGap θ₀ ≤ arcT₀ θ₀ - 1/5 := min_le_left _ _
  have h_δ_lt_lo : arcsinDelta ε < arcT₀ θ₀ - 1/5 := lt_of_lt_of_le h_lt_gap h_gap_lo
  have h_t₀_lo : (1/5 : ℝ) < arcT₀ θ₀ := arcT₀_gt_one_fifth h_lo
  have h_t₀_hi : arcT₀ θ₀ < 3/5 := arcT₀_lt_three_fifths h_hi
  apply transfer_integrability (exp (↑θ₀ * I)) (by linarith) (le_refl 0) (by linarith) hγ
  have h_seg1 := arc_seg1_ftc H h_lo h_hi
  have h_arc_left := arc_arc_left_ftc (H := H) h_lo h_hi h_δ_pos h_δ_lt_lo
  have hint_seg1 : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - exp (↑θ₀ * I))⁻¹ * deriv (fdBoundaryFun H) t)
      volume 0 (1/5) :=
    h_seg1.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((arc_ae_eq_h₀ H (exp (↑θ₀ * I))).mono (fun t ht hm => (ht hm).symm)))
  have hint_arc_left : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - exp (↑θ₀ * I))⁻¹ * deriv (fdBoundaryFun H) t)
      volume (1/5) (arcT₀ θ₀ - arcsinDelta ε) :=
    h_arc_left.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((arc_ae_eq_h_arc H (exp (↑θ₀ * I)) (by linarith) le_rfl (by linarith)).mono
        (fun t ht hm => (ht hm).symm)))
  exact hint_seg1.trans hint_arc_left

set_option maxHeartbeats 4000000 in
private lemma arc_hint_right_helper {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {θ₀ : ℝ} (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    (ε : ℝ) (hε : 0 < ε) (hε_thr : ε < arcThreshold H θ₀) :
    IntervalIntegrable
      (fun t => (γ.toPath.extend t - exp (↑θ₀ * I))⁻¹ * deriv γ.toPath.extend t)
      volume (arcT₀ θ₀ + arcsinDelta ε) 1 := by
  have h_δ_pos : 0 < arcsinDelta ε := arcsinDelta_pos hε
  have h_lt_gap : arcsinDelta ε < arcGap θ₀ :=
    arcsinDelta_lt_arcGap h_lo h_hi hε hε_thr
  have h_gap_hi : arcGap θ₀ ≤ 3/5 - arcT₀ θ₀ := min_le_right _ _
  have h_δ_lt_hi : arcsinDelta ε < 3/5 - arcT₀ θ₀ := lt_of_lt_of_le h_lt_gap h_gap_hi
  have h_t₀_lo : (1/5 : ℝ) < arcT₀ θ₀ := arcT₀_gt_one_fifth h_lo
  have h_t₀_hi : arcT₀ θ₀ < 3/5 := arcT₀_lt_three_fifths h_hi
  apply transfer_integrability (exp (↑θ₀ * I)) (by linarith) (by linarith) (le_refl 1) hγ
  have h_arc_right := arc_arc_right_ftc (H := H) h_lo h_hi h_δ_pos h_δ_lt_hi
  have h_seg4 := arc_seg4_ftc H h_lo h_hi
  have h_seg5 := arc_seg5_ftc hH (θ₀ := θ₀)
  have hint_arc_right : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - exp (↑θ₀ * I))⁻¹ * deriv (fdBoundaryFun H) t)
      volume (arcT₀ θ₀ + arcsinDelta ε) (3/5) :=
    h_arc_right.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((arc_ae_eq_h_arc H (exp (↑θ₀ * I)) (by linarith) (by linarith) le_rfl).mono
        (fun t ht hm => (ht hm).symm)))
  have hint_seg4 : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - exp (↑θ₀ * I))⁻¹ * deriv (fdBoundaryFun H) t)
      volume (3/5) (4/5) :=
    h_seg4.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((arc_ae_eq_h₃ H (exp (↑θ₀ * I))).mono (fun t ht hm => (ht hm).symm)))
  have hint_seg5 : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - exp (↑θ₀ * I))⁻¹ * deriv (fdBoundaryFun H) t)
      volume (4/5) 1 :=
    h_seg5.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((arc_ae_eq_h₅ H (exp (↑θ₀ * I))).mono (fun t ht hm => (ht hm).symm)))
  exact (hint_arc_right.trans hint_seg4).trans hint_seg5

/-- The full `ArcFTCHyp` at any smooth arc point `z₀ = exp(i·θ₀)` with
`θ₀ ∈ (π/3, 2π/3)`. The limit is `-π · I`. -/
def arcFTCHyp_arc_generic {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {θ₀ : ℝ} (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    ArcFTCHyp γ (exp (↑θ₀ * I)) (arcT₀ θ₀) arcsinDelta
      (arcThreshold H θ₀) (-(↑Real.pi * I)) where
  E := arc_E θ₀
  h_ftc := arc_h_ftc_helper hH γ hγ h_lo h_hi
  hint_left := arc_hint_left_helper hH γ hγ h_lo h_hi
  hint_right := arc_hint_right_helper hH γ hγ h_lo h_hi
  h_limit := arc_E_tendsto h_lo h_hi

end

