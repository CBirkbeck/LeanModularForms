/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.BoundaryWindingSeg1Proof
import LeanModularForms.ForMathlib.SegmentAnalysis
import LeanModularForms.ForMathlib.SegmentFTC
import LeanModularForms.ForMathlib.WindingWeightProofs

/-!
# `ArcFTCHyp` for the right vertical edge (seg1) at a generic point

Constructs `ArcFTCHyp` for any point `z₀` in the interior of the right vertical
edge of the FD boundary (`z₀.re = 1/2`, `z₀.im ∈ (√3/2, H)`), using the linear
cutoff `linDelta (seg1Speed H)`.

The proof structure mirrors the existing `ArcFTCAtI.lean` (which handles the
crossing at `i`), but adapted for a generic seg1 point. Key differences:
- The crossing is on seg1 (not seg2), with linear distance formula `K · |t - t₀|`
- The δ-window only excludes a sub-interval of seg1; seg2/3/4/5 contribute
  full integrals
- The branch correction comes from log of negative imaginary numbers

## Strategy

For `z₀ = 1/2 + c · I` with `c ∈ (√3/2, H)`:
1. Define per-segment reference functions for `fdBoundaryFun H t - z₀`.
2. Show each (or its negation) lies in `Complex.slitPlane`.
3. Apply `ftc_log_neg_on_segment` (or `ftc_log_on_segment`) to get
   `∫ deriv h / h = log(-h(b)) - log(-h(a))` for each piece.
4. Telescope: the boundary-junction values cancel, leaving
   `log(-h₀(t₀-δ)) - log(-h₀(t₀+δ))`.
5. Compute that this equals `-π · I` (independent of `δ`).
6. Wrap into `ArcFTCHyp γ z₀ t₀ (linDelta K) threshold (-(π·I))`.

## Main results

* `arcFTCHyp_seg1` — the full `ArcFTCHyp` at any seg1 interior point
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ### Per-segment reference functions for `fdBoundaryFun H t - z₀` -/

/-- The seg1 reference: `fdBoundaryFun H t - z₀` on seg1 (`t ≤ 1/5`). -/
private def seg1_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((H - 5 * t * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I + ((1/2 - z₀.re : ℝ) : ℂ)

/-- For `z₀.re = 1/2`, `seg1_h₀` simplifies to `((H - K·t - z₀.im) : ℂ) · I`. -/
private lemma seg1_h₀_eq_pure_im {H : ℝ} {z₀ : ℂ} (hz_re : z₀.re = 1/2) (t : ℝ) :
    seg1_h₀ H z₀ t = ((H - 5 * t * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I := by
  unfold seg1_h₀
  rw [show (1/2 - z₀.re : ℝ) = 0 from by rw [hz_re]; ring]
  simp

/-- On seg1, `fdBoundaryFun H t - z₀` agrees with `seg1_h₀ H z₀ t`. -/
private lemma fdBoundary_sub_eq_seg1_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) (ht : t ≤ 1/5) :
    fdBoundaryFun H t - z₀ = seg1_h₀ H z₀ t := by
  simp only [fdBoundaryFun, ht, ite_true, seg1_h₀]
  refine Complex.ext ?_ ?_ <;> simp

private lemma seg1_h₀_contDiff (H : ℝ) (z₀ : ℂ) : ContDiff ℝ ⊤ (seg1_h₀ H z₀) := by
  unfold seg1_h₀
  have h_real : ContDiff ℝ ⊤ (fun t : ℝ => H - 5 * t * (H - Real.sqrt 3 / 2) - z₀.im) := by
    fun_prop
  have h_cplx : ContDiff ℝ ⊤
      (fun t : ℝ => ((H - 5 * t * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h_real
  exact (h_cplx.mul contDiff_const).add contDiff_const

private lemma hasDerivAt_seg1_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (seg1_h₀ H z₀) (-(seg1Speed H : ℂ) * I) t := by
  have h_real : HasDerivAt (fun s : ℝ => H - 5 * s * (H - Real.sqrt 3 / 2) - z₀.im)
      (-seg1Speed H) t := by
    have hd : HasDerivAt (fun s : ℝ => 5 * s * (H - Real.sqrt 3 / 2))
        (5 * (H - Real.sqrt 3 / 2)) t :=
      (((hasDerivAt_id t).const_mul 5).mul_const (H - Real.sqrt 3 / 2)).congr_deriv (by ring)
    exact (((hasDerivAt_const t H).sub hd).sub_const z₀.im).congr_deriv
      (by unfold seg1Speed; ring)
  have h2 : HasDerivAt
      (fun s : ℝ => ((H - 5 * s * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ))
      (-(seg1Speed H : ℂ)) t :=
    (h_real.ofReal_comp).congr_deriv (by push_cast; ring)
  exact ((h2.mul_const I).add (hasDerivAt_const t (((1/2 - z₀.re : ℝ) : ℂ)))).congr_deriv (by ring)

private lemma seg1_h₀_continuous (H : ℝ) (z₀ : ℂ) : Continuous (seg1_h₀ H z₀) :=
  (seg1_h₀_contDiff H z₀).continuous

private lemma deriv_seg1_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (seg1_h₀ H z₀) t = -(seg1Speed H : ℂ) * I :=
  (hasDerivAt_seg1_h₀ H z₀ t).deriv

/-! ### Negation in slitPlane: seg1 left half (t ≤ t₀ - δ) -/

/-- For `z₀` on seg1 and `t < t₀`, `-(seg1_h₀(t)) = -(γ - z₀)` has negative imaginary
part, hence lies in `slitPlane` (since `im ≠ 0`). -/
private lemma neg_seg1_h₀_left_slitPlane {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    {δ : ℝ} (hδ_pos : 0 < δ)
    {t : ℝ} (htd : t ≤ seg1T₀ H z₀.im - δ) :
    -(seg1_h₀ H z₀ t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  rw [seg1_h₀_eq_pure_im hz_re]
  simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  -- Since t ≤ t₀ - δ < t₀, we have 5*t*(H-√3/2) < (H-z₀.im), so H - 5*t*(H-√3/2) > z₀.im.
  intro h_eq
  have hK : 0 < seg1Speed H := seg1Speed_pos hH
  have hK_eq : seg1Speed H * seg1T₀ H z₀.im = H - z₀.im := seg1Speed_mul_t₀ hH
  have h_t : t = seg1T₀ H z₀.im :=
    mul_left_cancel₀ (ne_of_gt hK) <| by rw [hK_eq]; unfold seg1Speed; linarith
  linarith

/-! ### Negation in slitPlane: seg1 right half (t₀ + δ ≤ t ≤ 1/5) -/

private lemma neg_seg1_h₀_right_slitPlane {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    {δ : ℝ} (hδ_pos : 0 < δ)
    {t : ℝ} (htd : seg1T₀ H z₀.im + δ ≤ t) :
    -(seg1_h₀ H z₀ t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  rw [seg1_h₀_eq_pure_im hz_re]
  simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  intro h_eq
  have hK : 0 < seg1Speed H := seg1Speed_pos hH
  have hK_eq : seg1Speed H * seg1T₀ H z₀.im = H - z₀.im := seg1Speed_mul_t₀ hH
  have h_t : t = seg1T₀ H z₀.im :=
    mul_left_cancel₀ (ne_of_gt hK) <| by rw [hK_eq]; unfold seg1Speed; linarith
  linarith

/-! ### Arc reference function (seg2 ∪ seg3) -/

/-- The arc reference: `exp(i · fdArcAngle t) - z₀`. -/
private def seg1_h_arc (z₀ : ℂ) (t : ℝ) : ℂ :=
  exp (↑(fdArcAngle t) * I) - z₀

private lemma fdBoundary_sub_eq_seg1_h_arc {H : ℝ} (z₀ : ℂ) {t : ℝ}
    (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t - z₀ = seg1_h_arc z₀ t := by
  unfold seg1_h_arc; rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2]

private lemma seg1_h_arc_continuous (z₀ : ℂ) : Continuous (seg1_h_arc z₀) := by
  unfold seg1_h_arc
  exact (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp fdArcAngle_continuous).mul continuous_const)).sub
    continuous_const

private lemma hasDerivAt_seg1_h_arc (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (seg1_h_arc z₀)
      (↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I)) t := by
  unfold seg1_h_arc
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

private lemma deriv_seg1_h_arc (z₀ : ℂ) (t : ℝ) :
    deriv (seg1_h_arc z₀) t = ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I) :=
  (hasDerivAt_seg1_h_arc z₀ t).deriv

/-- For `z₀ = 1/2 + c · I` with `c > √3/2`, the arc trajectory `-(γ - z₀)` lies in
slitPlane: at `t = 1/5` (ρ+1) it has `re = 0` but `im = z₀.im - √3/2 > 0`;
elsewhere on the arc, `re = 1/2 - cos θ > 0` (since `θ > π/3`). -/
private lemma neg_seg1_h_arc_slitPlane {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im)
    {t : ℝ} (ht1 : 1/5 ≤ t) (ht3 : t ≤ 3/5) :
    -(seg1_h_arc z₀ t) ∈ Complex.slitPlane := by
  unfold seg1_h_arc
  rcases eq_or_lt_of_le ht1 with h_eq | ht1_lt
  · -- t = 1/5: γ = ρ+1
    rw [Complex.mem_slitPlane_iff]; right
    rw [← h_eq]
    have hpi := Real.pi_pos
    rw [show (fdArcAngle (1/5) : ℝ) = Real.pi / 3 from by unfold fdArcAngle; ring]
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
    simp only [Complex.neg_im, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_add]
    intro h_eq
    -- Goal: -(0 - z₀.im) = 0, but z₀.im > √3/2 > 0
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
  · rw [Complex.mem_slitPlane_iff]; left
    have hpi := Real.pi_pos
    have hθ_lo : Real.pi / 3 < fdArcAngle t := by unfold fdArcAngle; nlinarith
    have hθ_hi : fdArcAngle t ≤ 2 * Real.pi / 3 := by unfold fdArcAngle; nlinarith
    have h_cos_lt : Real.cos (fdArcAngle t) < 1/2 := by
      have := Real.strictAntiOn_cos (⟨by linarith, by linarith⟩ : Real.pi / 3 ∈ Icc 0 Real.pi)
        (⟨by linarith, by linarith⟩ : fdArcAngle t ∈ Icc 0 Real.pi) hθ_lo
      rwa [Real.cos_pi_div_three] at this
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, mul_one]
    rw [hz_re]; linarith

/-! ### Seg4 reference function -/

/-- The seg4 reference: `fdBoundaryFun H t - z₀` on seg4 (`3/5 < t ≤ 4/5`). -/
private def seg1_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((-1/2 - z₀.re : ℝ) : ℂ) +
  ((Real.sqrt 3 / 2 + (5 * t - 3) * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I

private lemma fdBoundary_sub_eq_seg1_h₃ (H : ℝ) (z₀ : ℂ) {t : ℝ}
    (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    fdBoundaryFun H t - z₀ = seg1_h₃ H z₀ t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    ht4, ite_true, ite_false, seg1_h₃]
  refine Complex.ext ?_ ?_ <;> simp

private lemma seg1_h₃_continuous (H : ℝ) (z₀ : ℂ) : Continuous (seg1_h₃ H z₀) := by
  unfold seg1_h₃
  refine Continuous.add continuous_const ?_
  refine Continuous.mul ?_ continuous_const
  exact Complex.continuous_ofReal.comp (by fun_prop)

private lemma hasDerivAt_seg1_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (seg1_h₃ H z₀) ((seg1Speed H : ℂ) * I) t := by
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

private lemma deriv_seg1_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (seg1_h₃ H z₀) t = (seg1Speed H : ℂ) * I :=
  (hasDerivAt_seg1_h₃ H z₀ t).deriv

/-- For `z₀.re = 1/2`, `-(seg4 - z₀)` has `re = 1`, in slitPlane. -/
private lemma neg_seg1_h₃_slitPlane {H : ℝ} {z₀ : ℂ} (hz_re : z₀.re = 1/2) (t : ℝ) :
    -(seg1_h₃ H z₀ t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  unfold seg1_h₃
  simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
  rw [hz_re]; norm_num

/-! ### Seg5 reference function -/

/-- The seg5 reference: `fdBoundaryFun H t - z₀` on seg5 (`4/5 < t ≤ 1`). -/
private def seg1_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((5 * t - 9/2 - z₀.re : ℝ) : ℂ) + ((H - z₀.im : ℝ) : ℂ) * I

private lemma fdBoundary_sub_eq_seg1_h₅ (H : ℝ) (z₀ : ℂ) {t : ℝ} (ht : 4/5 < t) :
    fdBoundaryFun H t - z₀ = seg1_h₅ H z₀ t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    show ¬t ≤ 4/5 from by linarith, ite_false, seg1_h₅]
  refine Complex.ext ?_ ?_ <;> simp

private lemma seg1_h₅_continuous (H : ℝ) (z₀ : ℂ) : Continuous (seg1_h₅ H z₀) := by
  unfold seg1_h₅
  refine Continuous.add ?_ continuous_const
  exact Complex.continuous_ofReal.comp (by fun_prop)

private lemma hasDerivAt_seg1_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (seg1_h₅ H z₀) (5 : ℂ) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((5 * s - 9/2 - z₀.re : ℝ) : ℂ)) 5 t := by
    have h_real : HasDerivAt (fun s : ℝ => 5 * s - 9/2 - z₀.re) 5 t :=
      ((((hasDerivAt_id t).const_mul 5).sub_const (9/2)).sub_const z₀.re).congr_deriv (by ring)
    exact (h_real.ofReal_comp).congr_deriv (by push_cast; ring)
  exact (h1.add_const _).congr_deriv (by ring)

private lemma deriv_seg1_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (seg1_h₅ H z₀) t = 5 :=
  (hasDerivAt_seg1_h₅ H z₀ t).deriv

/-- For `z₀.im < H`, `-(seg5 - z₀)` has `im = z₀.im - H < 0`, in slitPlane. -/
private lemma neg_seg1_h₅_slitPlane {H : ℝ} {z₀ : ℂ} (hc_hi : z₀.im < H) (t : ℝ) :
    -(seg1_h₅ H z₀ t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  unfold seg1_h₅
  simp only [Complex.neg_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
  intro h; linarith

/-! ### Per-segment FTC pieces (using `ftc_log_neg_on_segment`) -/

/-- FTC for the seg1 left half `[0, t₀ - δ]`. -/
private lemma seg1_left_ftc {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_t₀ : δ < seg1T₀ H z₀.im) :
    IntervalIntegrable
      (fun t => deriv (seg1_h₀ H z₀) t / seg1_h₀ H z₀ t) volume 0 (seg1T₀ H z₀.im - δ) ∧
    ∫ t in (0:ℝ)..(seg1T₀ H z₀.im - δ),
        deriv (seg1_h₀ H z₀) t / seg1_h₀ H z₀ t =
      Complex.log (-(seg1_h₀ H z₀ (seg1T₀ H z₀.im - δ))) -
      Complex.log (-(seg1_h₀ H z₀ 0)) := by
  apply LogDerivFTC.ftc_log_neg_on_segment (by linarith : (0:ℝ) ≤ seg1T₀ H z₀.im - δ)
    (seg1_h₀_continuous H z₀).continuousOn
    (fun t _ => (hasDerivAt_seg1_h₀ H z₀ t).differentiableAt)
    (by rw [funext (deriv_seg1_h₀ H z₀)]; exact continuousOn_const)
  intro t ⟨_, htd⟩
  exact neg_seg1_h₀_left_slitPlane hH hz_re hδ_pos htd

/-- FTC for the seg1 right half `[t₀ + δ, 1/5]`. -/
private lemma seg1_right_ftc {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 1/5 - seg1T₀ H z₀.im) :
    IntervalIntegrable
      (fun t => deriv (seg1_h₀ H z₀) t / seg1_h₀ H z₀ t) volume (seg1T₀ H z₀.im + δ) (1/5) ∧
    ∫ t in (seg1T₀ H z₀.im + δ)..(1/5 : ℝ),
        deriv (seg1_h₀ H z₀) t / seg1_h₀ H z₀ t =
      Complex.log (-(seg1_h₀ H z₀ (1/5))) -
      Complex.log (-(seg1_h₀ H z₀ (seg1T₀ H z₀.im + δ))) := by
  apply LogDerivFTC.ftc_log_neg_on_segment (by linarith : seg1T₀ H z₀.im + δ ≤ 1/5)
    (seg1_h₀_continuous H z₀).continuousOn
    (fun t _ => (hasDerivAt_seg1_h₀ H z₀ t).differentiableAt)
    (by rw [funext (deriv_seg1_h₀ H z₀)]; exact continuousOn_const)
  intro t ⟨htd, _⟩
  exact neg_seg1_h₀_right_slitPlane hH hz_re hδ_pos htd

/-- FTC for the arc `[1/5, 3/5]`. -/
private lemma seg1_arc_ftc {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) :
    IntervalIntegrable
      (fun t => deriv (seg1_h_arc z₀) t / seg1_h_arc z₀ t) volume (1/5) (3/5) ∧
    ∫ t in (1/5 : ℝ)..(3/5),
        deriv (seg1_h_arc z₀) t / seg1_h_arc z₀ t =
      Complex.log (-(seg1_h_arc z₀ (3/5))) -
      Complex.log (-(seg1_h_arc z₀ (1/5))) := by
  apply LogDerivFTC.ftc_log_neg_on_segment (by norm_num : (1/5 : ℝ) ≤ 3/5)
    (seg1_h_arc_continuous z₀).continuousOn
    (fun t _ => (hasDerivAt_seg1_h_arc z₀ t).differentiableAt)
    (by
      rw [funext (deriv_seg1_h_arc z₀)]
      exact (continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp fdArcAngle_continuous).mul continuous_const))).continuousOn)
  intro t ⟨ht1, ht3⟩
  exact neg_seg1_h_arc_slitPlane hz_re hc_lo ht1 ht3

/-- FTC for seg4 `[3/5, 4/5]`. -/
private lemma seg1_seg4_ftc (H : ℝ) {z₀ : ℂ} (hz_re : z₀.re = 1/2) :
    IntervalIntegrable
      (fun t => deriv (seg1_h₃ H z₀) t / seg1_h₃ H z₀ t) volume (3/5) (4/5) ∧
    ∫ t in (3/5 : ℝ)..(4/5),
        deriv (seg1_h₃ H z₀) t / seg1_h₃ H z₀ t =
      Complex.log (-(seg1_h₃ H z₀ (4/5))) -
      Complex.log (-(seg1_h₃ H z₀ (3/5))) := by
  apply LogDerivFTC.ftc_log_neg_on_segment (by norm_num : (3/5 : ℝ) ≤ 4/5)
    (seg1_h₃_continuous H z₀).continuousOn
    (fun t _ => (hasDerivAt_seg1_h₃ H z₀ t).differentiableAt)
    (by rw [funext (deriv_seg1_h₃ H z₀)]; exact continuousOn_const)
  intro t _
  exact neg_seg1_h₃_slitPlane hz_re t

/-- FTC for seg5 `[4/5, 1]`. -/
private lemma seg1_seg5_ftc (H : ℝ) {z₀ : ℂ} (hc_hi : z₀.im < H) :
    IntervalIntegrable
      (fun t => deriv (seg1_h₅ H z₀) t / seg1_h₅ H z₀ t) volume (4/5) 1 ∧
    ∫ t in (4/5 : ℝ)..(1 : ℝ),
        deriv (seg1_h₅ H z₀) t / seg1_h₅ H z₀ t =
      Complex.log (-(seg1_h₅ H z₀ 1)) -
      Complex.log (-(seg1_h₅ H z₀ (4/5))) := by
  apply LogDerivFTC.ftc_log_neg_on_segment (by norm_num : (4/5 : ℝ) ≤ 1)
    (seg1_h₅_continuous H z₀).continuousOn
    (fun t _ => (hasDerivAt_seg1_h₅ H z₀ t).differentiableAt)
    (by rw [funext (deriv_seg1_h₅ H z₀)]; exact continuousOn_const)
  intro t _
  exact neg_seg1_h₅_slitPlane hc_hi t

/-! ### Junction value equalities (for telescope) -/

/-- Junction at `t = 1/5`: `seg1_h₀(1/5) = seg1_h_arc(1/5)`. -/
private lemma seg1_junction_15 (H : ℝ) (z₀ : ℂ) :
    seg1_h₀ H z₀ (1/5) = seg1_h_arc z₀ (1/5) := by
  unfold seg1_h₀ seg1_h_arc
  rw [show (fdArcAngle (1/5) : ℝ) = Real.pi / 3 from by unfold fdArcAngle; ring,
    exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
  refine Complex.ext ?_ ?_ <;> simp

/-- Junction at `t = 3/5`: `seg1_h_arc(3/5) = seg1_h₃(3/5)`. -/
private lemma seg1_junction_35 (H : ℝ) (z₀ : ℂ) :
    seg1_h_arc z₀ (3/5) = seg1_h₃ H z₀ (3/5) := by
  unfold seg1_h_arc seg1_h₃
  rw [show (fdArcAngle (3/5) : ℝ) = 2 * Real.pi / 3 from by unfold fdArcAngle; ring,
    exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  refine Complex.ext ?_ ?_
  · simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
    ring
  · simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    ring

/-- Junction at `t = 4/5`: `seg1_h₃(4/5) = seg1_h₅(4/5)`. -/
private lemma seg1_junction_45 (H : ℝ) (z₀ : ℂ) :
    seg1_h₃ H z₀ (4/5) = seg1_h₅ H z₀ (4/5) := by
  unfold seg1_h₃ seg1_h₅
  refine Complex.ext ?_ ?_ <;> simp <;> ring

/-- Closed-curve identity: `seg1_h₀(0) = seg1_h₅(1)`. -/
private lemma seg1_closed (H : ℝ) (z₀ : ℂ) :
    seg1_h₀ H z₀ 0 = seg1_h₅ H z₀ 1 := by
  unfold seg1_h₀ seg1_h₅
  refine Complex.ext ?_ ?_ <;> simp; ring

/-! ### Final log computation: `E(ε) = -π · I` -/

/-- The seg1 left and right endpoints around the crossing telescope to `-π · I`. -/
private lemma seg1_log_diff_eq_neg_pi_I {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2) {δ : ℝ} (hδ_pos : 0 < δ) :
    Complex.log (-(seg1_h₀ H z₀ (seg1T₀ H z₀.im - δ))) -
    Complex.log (-(seg1_h₀ H z₀ (seg1T₀ H z₀.im + δ))) = -(↑Real.pi * I) := by
  have hK : 0 < seg1Speed H := seg1Speed_pos hH
  have hKδ : 0 < seg1Speed H * δ := mul_pos hK hδ_pos
  -- Compute the values
  have h_minus : seg1_h₀ H z₀ (seg1T₀ H z₀.im - δ) =
      ((seg1Speed H * δ : ℝ) : ℂ) * I := by
    rw [seg1_h₀_eq_pure_im hz_re]
    congr 1
    have : 5 * (seg1T₀ H z₀.im - δ) * (H - Real.sqrt 3 / 2) =
        seg1Speed H * (seg1T₀ H z₀.im - δ) := by unfold seg1Speed; ring
    exact_mod_cast by rw [this, mul_sub, seg1Speed_mul_t₀ hH]; ring
  have h_plus : seg1_h₀ H z₀ (seg1T₀ H z₀.im + δ) =
      ((-(seg1Speed H * δ) : ℝ) : ℂ) * I := by
    rw [seg1_h₀_eq_pure_im hz_re]
    congr 1
    have : 5 * (seg1T₀ H z₀.im + δ) * (H - Real.sqrt 3 / 2) =
        seg1Speed H * (seg1T₀ H z₀.im + δ) := by unfold seg1Speed; ring
    exact_mod_cast by rw [this, mul_add, seg1Speed_mul_t₀ hH]; ring
  rw [h_minus, h_plus]
  -- LHS: log(-(K*δ * I)) - log(-((-K*δ) * I)) = log(-K*δ * I) - log(K*δ * I) = -π*I
  rw [show -(((seg1Speed H * δ : ℝ) : ℂ) * I) = ((seg1Speed H * δ : ℝ) : ℂ) * (-I) from by ring,
      show -(((-(seg1Speed H * δ) : ℝ) : ℂ) * I) = ((seg1Speed H * δ : ℝ) : ℂ) * I from by
        push_cast; ring]
  rw [Complex.log_ofReal_mul hKδ (show (-I : ℂ) ≠ 0 from neg_ne_zero.mpr I_ne_zero),
      Complex.log_ofReal_mul hKδ I_ne_zero]
  rw [Complex.log_neg_I, Complex.log_I]
  ring

/-! ### A.e. equality between `(γ - z₀)⁻¹ · γ'` and `deriv h_seg / h_seg` -/

/-- On the interior of seg1 `(0, 1/5)`, `(γ - z₀)⁻¹ · γ' = deriv (seg1_h₀) / seg1_h₀`
a.e. -/
private lemma ae_eq_seg1_h₀ (H : ℝ) (z₀ : ℂ) {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 1/5) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (seg1_h₀ H z₀) t / seg1_h₀ H z₀ t := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton b)] with t ht_ne ht_mem
  rw [uIoc_of_le hab] at ht_mem
  have ht_lt : t < 1/5 :=
    (lt_of_le_of_ne ht_mem.2 fun h => ht_ne (Set.mem_singleton_iff.mpr h)).trans_le hb
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] seg1_h₀ H z₀ :=
    Filter.eventually_of_mem (Iio_mem_nhds ht_lt)
      fun s hs => fdBoundary_sub_eq_seg1_h₀ H z₀ s hs.le
  rw [fdBoundary_sub_eq_seg1_h₀ H z₀ t ht_lt.le,
    ← deriv_sub_const (f := fdBoundaryFun H) z₀, h_evEq.deriv_eq, div_eq_mul_inv, mul_comm]

/-- On the open arc `(1/5, 3/5)`, `(γ - z₀)⁻¹ · γ' = deriv (seg1_h_arc) / seg1_h_arc` a.e. -/
private lemma ae_eq_seg1_h_arc (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (1/5 : ℝ) (3/5) →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (seg1_h_arc z₀) t / seg1_h_arc z₀ t := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (3/5 : ℝ))] with t ht_ne ht_mem
  rw [uIoc_of_le (by norm_num : (1/5 : ℝ) ≤ 3/5)] at ht_mem
  have ht1 : 1/5 < t := ht_mem.1
  have ht3_lt : t < 3/5 :=
    lt_of_le_of_ne ht_mem.2 fun h => ht_ne (Set.mem_singleton_iff.mpr h)
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] seg1_h_arc z₀ :=
    Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht3_lt))
      fun _ ⟨hs1, hs3⟩ => fdBoundary_sub_eq_seg1_h_arc z₀ hs1 hs3.le
  rw [fdBoundary_sub_eq_seg1_h_arc z₀ ht1 ht3_lt.le,
    ← deriv_sub_const (f := fdBoundaryFun H) z₀, h_evEq.deriv_eq, div_eq_mul_inv, mul_comm]

/-- On the open seg4 `(3/5, 4/5)`, similar a.e. equality. -/
private lemma ae_eq_seg1_h₃ (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (3/5 : ℝ) (4/5) →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (seg1_h₃ H z₀) t / seg1_h₃ H z₀ t := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (4/5 : ℝ))] with t ht_ne ht_mem
  rw [uIoc_of_le (by norm_num : (3/5 : ℝ) ≤ 4/5)] at ht_mem
  have ht3 : 3/5 < t := ht_mem.1
  have ht4_lt : t < 4/5 :=
    lt_of_le_of_ne ht_mem.2 fun h => ht_ne (Set.mem_singleton_iff.mpr h)
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] seg1_h₃ H z₀ :=
    Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht3) (Iio_mem_nhds ht4_lt))
      fun _ ⟨hs3, hs4⟩ => fdBoundary_sub_eq_seg1_h₃ H z₀ hs3 hs4.le
  rw [fdBoundary_sub_eq_seg1_h₃ H z₀ ht3 ht4_lt.le,
    ← deriv_sub_const (f := fdBoundaryFun H) z₀, h_evEq.deriv_eq, div_eq_mul_inv, mul_comm]

/-- On the open seg5 `(4/5, 1)`, similar a.e. equality. -/
private lemma ae_eq_seg1_h₅ (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (4/5 : ℝ) 1 →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (seg1_h₅ H z₀) t / seg1_h₅ H z₀ t := by
  refine ae_of_all _ fun t ht_mem => ?_
  rw [uIoc_of_le (by norm_num : (4/5 : ℝ) ≤ 1)] at ht_mem
  have ht4 : 4/5 < t := ht_mem.1
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] seg1_h₅ H z₀ :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht4) fun _ hs => fdBoundary_sub_eq_seg1_h₅ H z₀ hs
  rw [fdBoundary_sub_eq_seg1_h₅ H z₀ ht4,
    ← deriv_sub_const (f := fdBoundaryFun H) z₀, h_evEq.deriv_eq, div_eq_mul_inv, mul_comm]

/-! ### Telescope theorem -/

/-- The full FTC telescope for the seg1 crossing: the trimmed integral equals `-π · I`. -/
theorem fdBoundary_ftc_telescope_seg1 {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_t₀ : δ < seg1T₀ H z₀.im)
    (hδ_lt_one_fifth_sub : δ < 1/5 - seg1T₀ H z₀.im) :
    (∫ t in (0 : ℝ)..(seg1T₀ H z₀.im - δ),
        (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
    (∫ t in (seg1T₀ H z₀.im + δ)..(1 : ℝ),
        (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) =
    -(↑Real.pi * I) := by
  set t₀ := seg1T₀ H z₀.im
  have ht₀_pos : 0 < t₀ := seg1T₀_pos hH hc_hi
  have ht₀_lt : t₀ < 1/5 := seg1T₀_lt_one_fifth hH hc_lo
  -- Per-segment FTC pieces
  have h_left := seg1_left_ftc hH hz_re hδ_pos hδ_lt_t₀
  have h_right := seg1_right_ftc hH hz_re hδ_pos hδ_lt_one_fifth_sub
  have h_arc := seg1_arc_ftc hz_re hc_lo
  have h_seg4 := seg1_seg4_ftc H hz_re
  have h_seg5 := seg1_seg5_ftc H hc_hi
  -- Convert each integral via ae equality
  have h_int_left :
      ∫ t in (0 : ℝ)..(t₀ - δ), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      Complex.log (-(seg1_h₀ H z₀ (t₀ - δ))) - Complex.log (-(seg1_h₀ H z₀ 0)) := by
    rw [intervalIntegral.integral_congr_ae (ae_eq_seg1_h₀ H z₀ (by linarith) (by linarith))]
    exact h_left.2
  have h_int_right_seg1 :
      ∫ t in (t₀ + δ)..(1/5 : ℝ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      Complex.log (-(seg1_h₀ H z₀ (1/5))) - Complex.log (-(seg1_h₀ H z₀ (t₀ + δ))) := by
    rw [intervalIntegral.integral_congr_ae (ae_eq_seg1_h₀ H z₀ (by linarith) le_rfl)]
    exact h_right.2
  have h_int_arc :
      ∫ t in (1/5 : ℝ)..(3/5),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      Complex.log (-(seg1_h_arc z₀ (3/5))) - Complex.log (-(seg1_h_arc z₀ (1/5))) := by
    rw [intervalIntegral.integral_congr_ae (ae_eq_seg1_h_arc H z₀)]
    exact h_arc.2
  have h_int_seg4 :
      ∫ t in (3/5 : ℝ)..(4/5),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      Complex.log (-(seg1_h₃ H z₀ (4/5))) - Complex.log (-(seg1_h₃ H z₀ (3/5))) := by
    rw [intervalIntegral.integral_congr_ae (ae_eq_seg1_h₃ H z₀)]
    exact h_seg4.2
  have h_int_seg5 :
      ∫ t in (4/5 : ℝ)..(1 : ℝ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      Complex.log (-(seg1_h₅ H z₀ 1)) - Complex.log (-(seg1_h₅ H z₀ (4/5))) := by
    rw [intervalIntegral.integral_congr_ae (ae_eq_seg1_h₅ H z₀)]
    exact h_seg5.2
  -- Integrability for adjacent splitting on [t₀+δ, 1]
  have hint_right_seg1 : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (t₀ + δ) (1/5) :=
    h_right.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((ae_eq_seg1_h₀ H z₀ (by linarith) le_rfl).mono (fun t ht hm => (ht hm).symm)))
  have hint_arc : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (1/5) (3/5) :=
    h_arc.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((ae_eq_seg1_h_arc H z₀).mono (fun t ht hm => (ht hm).symm)))
  have hint_seg4 : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (3/5) (4/5) :=
    h_seg4.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((ae_eq_seg1_h₃ H z₀).mono (fun t ht hm => (ht hm).symm)))
  have hint_seg5 : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (4/5) 1 :=
    h_seg5.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((ae_eq_seg1_h₅ H z₀).mono (fun t ht hm => (ht hm).symm)))
  -- Split the right integral
  have h_split :
      ∫ t in (t₀ + δ)..(1 : ℝ), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      (∫ t in (t₀ + δ)..(1/5 : ℝ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (1/5 : ℝ)..(3/5), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (3/5 : ℝ)..(4/5), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (4/5 : ℝ)..(1 : ℝ), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals hint_right_seg1 hint_arc
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hint_right_seg1.trans hint_arc) hint_seg4
    have h3 := intervalIntegral.integral_add_adjacent_intervals
      ((hint_right_seg1.trans hint_arc).trans hint_seg4) hint_seg5
    linear_combination -h1 - h2 - h3
  -- Combine: total = log(-h₀(t₀-δ)) - log(-h₀(t₀+δ))
  rw [h_split, h_int_left, h_int_right_seg1, h_int_arc, h_int_seg4, h_int_seg5,
      seg1_junction_15 H z₀, seg1_junction_35 H z₀, seg1_junction_45 H z₀,
      seg1_closed H z₀]
  -- Junctions cancel
  have h_alg :
      Complex.log (-(seg1_h₀ H z₀ (t₀ - δ))) - Complex.log (-(seg1_h₅ H z₀ 1)) +
      ((Complex.log (-(seg1_h_arc z₀ (1/5))) - Complex.log (-(seg1_h₀ H z₀ (t₀ + δ))) +
        (Complex.log (-(seg1_h₃ H z₀ (3/5))) - Complex.log (-(seg1_h_arc z₀ (1/5)))) +
        (Complex.log (-(seg1_h₅ H z₀ (4/5))) - Complex.log (-(seg1_h₃ H z₀ (3/5)))) +
        (Complex.log (-(seg1_h₅ H z₀ 1)) - Complex.log (-(seg1_h₅ H z₀ (4/5))))))
      = Complex.log (-(seg1_h₀ H z₀ (t₀ - δ))) - Complex.log (-(seg1_h₀ H z₀ (t₀ + δ))) := by
    ring
  rw [h_alg]
  exact seg1_log_diff_eq_neg_pi_I hH hz_re hδ_pos

/-! ### Final assembly: the ArcFTCHyp for seg1 -/

/-- The full `ArcFTCHyp` at any seg1 interior point, with limit `-π · I`. -/
def arcFTCHyp_seg1 {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H) :
    ArcFTCHyp γ z₀ (seg1T₀ H z₀.im) (linDelta (seg1Speed H))
      (seg1Threshold H z₀) (-(↑Real.pi * I)) where
  E := fun _ => -(↑Real.pi * I)
  h_ftc := by
    intro ε hε hε_thr
    have hK_pos : 0 < seg1Speed H := seg1Speed_pos hH
    have h_lin_pos : 0 < linDelta (seg1Speed H) ε := linDelta_pos hK_pos hε
    -- ε bounds derived from threshold
    have h_eps_top : ε < H - z₀.im :=
      lt_of_lt_of_le hε_thr (min_le_right _ _)
    have h_eps_arc : ε < ‖z₀‖ - 1 :=
      lt_of_lt_of_le hε_thr (le_trans (min_le_left _ _) (min_le_left _ _))
    have h_eps_width : ε < z₀.im - Real.sqrt 3 / 2 :=
      lt_of_lt_of_le h_eps_arc (norm_sub_one_le_im_sub_sqrt3 hz_re hc_lo.le)
    have h_lin_lt_t₀ : linDelta (seg1Speed H) ε < seg1T₀ H z₀.im := by
      unfold linDelta
      rw [div_lt_iff₀ hK_pos, mul_comm, seg1Speed_mul_t₀ hH]
      exact h_eps_top
    have h_lin_lt_one_fifth_sub :
        linDelta (seg1Speed H) ε < 1/5 - seg1T₀ H z₀.im := by
      unfold linDelta
      rw [div_lt_iff₀ hK_pos, mul_comm, seg1Speed_mul_one_fifth_sub_t₀ hH]
      exact h_eps_width
    -- Transfer to fdBoundaryFun-based integrand
    have h_t₀_pos : 0 < seg1T₀ H z₀.im := seg1T₀_pos hH hc_hi
    have h_t₀_lt : seg1T₀ H z₀.im < 1/5 := seg1T₀_lt_one_fifth hH hc_lo
    rw [transfer_integral z₀ (by linarith) (le_refl 0) (by linarith) hγ,
        transfer_integral z₀ (by linarith) (by linarith) (le_refl 1) hγ]
    exact fdBoundary_ftc_telescope_seg1 hH hz_re hc_lo hc_hi h_lin_pos
      h_lin_lt_t₀ h_lin_lt_one_fifth_sub
  hint_left := by
    intro ε hε hε_thr
    have hK_pos : 0 < seg1Speed H := seg1Speed_pos hH
    have h_lin_pos : 0 < linDelta (seg1Speed H) ε := linDelta_pos hK_pos hε
    have h_eps_top : ε < H - z₀.im :=
      lt_of_lt_of_le hε_thr (min_le_right _ _)
    have h_eps_arc : ε < ‖z₀‖ - 1 :=
      lt_of_lt_of_le hε_thr (le_trans (min_le_left _ _) (min_le_left _ _))
    have h_eps_width : ε < z₀.im - Real.sqrt 3 / 2 :=
      lt_of_lt_of_le h_eps_arc (norm_sub_one_le_im_sub_sqrt3 hz_re hc_lo.le)
    have h_lin_lt_t₀ : linDelta (seg1Speed H) ε < seg1T₀ H z₀.im := by
      unfold linDelta
      rw [div_lt_iff₀ hK_pos, mul_comm, seg1Speed_mul_t₀ hH]
      exact h_eps_top
    have h_t₀_pos : 0 < seg1T₀ H z₀.im := seg1T₀_pos hH hc_hi
    have h_t₀_lt : seg1T₀ H z₀.im < 1/5 := seg1T₀_lt_one_fifth hH hc_lo
    apply transfer_integrability z₀ (by linarith) (le_refl 0) (by linarith) hγ
    have h_left := seg1_left_ftc hH hz_re h_lin_pos h_lin_lt_t₀
    exact h_left.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((ae_eq_seg1_h₀ H z₀ (by linarith) (by linarith)).mono (fun t ht hm => (ht hm).symm)))
  hint_right := by
    intro ε hε hε_thr
    have hK_pos : 0 < seg1Speed H := seg1Speed_pos hH
    have h_lin_pos : 0 < linDelta (seg1Speed H) ε := linDelta_pos hK_pos hε
    have h_eps_top : ε < H - z₀.im :=
      lt_of_lt_of_le hε_thr (min_le_right _ _)
    have h_eps_arc : ε < ‖z₀‖ - 1 :=
      lt_of_lt_of_le hε_thr (le_trans (min_le_left _ _) (min_le_left _ _))
    have h_eps_width : ε < z₀.im - Real.sqrt 3 / 2 :=
      lt_of_lt_of_le h_eps_arc (norm_sub_one_le_im_sub_sqrt3 hz_re hc_lo.le)
    have h_lin_lt_t₀ : linDelta (seg1Speed H) ε < seg1T₀ H z₀.im := by
      unfold linDelta
      rw [div_lt_iff₀ hK_pos, mul_comm, seg1Speed_mul_t₀ hH]
      exact h_eps_top
    have h_lin_lt_one_fifth_sub :
        linDelta (seg1Speed H) ε < 1/5 - seg1T₀ H z₀.im := by
      unfold linDelta
      rw [div_lt_iff₀ hK_pos, mul_comm, seg1Speed_mul_one_fifth_sub_t₀ hH]
      exact h_eps_width
    have h_t₀_pos : 0 < seg1T₀ H z₀.im := seg1T₀_pos hH hc_hi
    have h_t₀_lt : seg1T₀ H z₀.im < 1/5 := seg1T₀_lt_one_fifth hH hc_lo
    apply transfer_integrability z₀ (by linarith) (by linarith) (le_refl 1) hγ
    -- Need integrability on [t₀+δ, 1]; combine seg1_right + arc + seg4 + seg5
    have h_right := seg1_right_ftc hH hz_re h_lin_pos h_lin_lt_one_fifth_sub
    have h_arc := seg1_arc_ftc hz_re hc_lo
    have h_seg4 := seg1_seg4_ftc H hz_re
    have h_seg5 := seg1_seg5_ftc H hc_hi
    have hint_right_seg1 : IntervalIntegrable
        (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
        volume (seg1T₀ H z₀.im + linDelta (seg1Speed H) ε) (1/5) :=
      h_right.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
        ((ae_eq_seg1_h₀ H z₀ (by linarith) le_rfl).mono (fun t ht hm => (ht hm).symm)))
    have hint_arc : IntervalIntegrable
        (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
        volume (1/5) (3/5) :=
      h_arc.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
        ((ae_eq_seg1_h_arc H z₀).mono (fun t ht hm => (ht hm).symm)))
    have hint_seg4 : IntervalIntegrable
        (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
        volume (3/5) (4/5) :=
      h_seg4.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
        ((ae_eq_seg1_h₃ H z₀).mono (fun t ht hm => (ht hm).symm)))
    have hint_seg5 : IntervalIntegrable
        (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
        volume (4/5) 1 :=
      h_seg5.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
        ((ae_eq_seg1_h₅ H z₀).mono (fun t ht hm => (ht hm).symm)))
    exact ((hint_right_seg1.trans hint_arc).trans hint_seg4).trans hint_seg5
  h_limit := tendsto_const_nhds

end




