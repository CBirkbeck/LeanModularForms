/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.BoundaryWindingSeg1Proof
import LeanModularForms.ForMathlib.SegmentAnalysis
import LeanModularForms.ForMathlib.SegmentFTC
import LeanModularForms.ForMathlib.VertSegFTCProvider
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

The arc, seg3, and seg5 pieces are shared with `Seg4FTCProvider.lean` via
`VertSegFTCProvider.lean`.

## Main results

* `arcFTCHyp_seg1` — the full `ArcFTCHyp` at any seg1 interior point
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

private def seg1_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((H - 5 * t * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I + ((1/2 - z₀.re : ℝ) : ℂ)

private lemma seg1_h₀_eq_pure_im {H : ℝ} {z₀ : ℂ} (hz_re : z₀.re = 1/2) (t : ℝ) :
    seg1_h₀ H z₀ t = ((H - 5 * t * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I := by
  simp [seg1_h₀, hz_re]

private lemma fdBoundary_sub_eq_seg1_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) (ht : t ≤ 1/5) :
    fdBoundaryFun H t - z₀ = seg1_h₀ H z₀ t := by
  simp only [fdBoundaryFun, ht, ite_true, seg1_h₀]
  refine Complex.ext ?_ ?_ <;> simp

private lemma seg1_h₀_contDiff (H : ℝ) (z₀ : ℂ) : ContDiff ℝ ⊤ (seg1_h₀ H z₀) := by
  unfold seg1_h₀
  have h_real : ContDiff ℝ ⊤ (fun t : ℝ => H - 5 * t * (H - Real.sqrt 3 / 2) - z₀.im) := by
    fun_prop
  exact ((Complex.ofRealCLM.contDiff.comp h_real).mul contDiff_const).add contDiff_const

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
  exact ((h2.mul_const I).add (hasDerivAt_const t (((1/2 - z₀.re : ℝ) : ℂ)))).congr_deriv
    (by ring)

private lemma seg1_h₀_continuous (H : ℝ) (z₀ : ℂ) : Continuous (seg1_h₀ H z₀) :=
  (seg1_h₀_contDiff H z₀).continuous

private lemma deriv_seg1_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (seg1_h₀ H z₀) t = -(seg1Speed H : ℂ) * I :=
  (hasDerivAt_seg1_h₀ H z₀ t).deriv

private lemma neg_seg1_h₀_left_slitPlane {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    {δ : ℝ} (hδ_pos : 0 < δ)
    {t : ℝ} (htd : t ≤ seg1T₀ H z₀.im - δ) :
    -(seg1_h₀ H z₀ t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  rw [seg1_h₀_eq_pure_im hz_re]
  simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  intro h_eq
  have hK : 0 < seg1Speed H := seg1Speed_pos hH
  have : t = seg1T₀ H z₀.im :=
    mul_left_cancel₀ hK.ne' <| by rw [seg1Speed_mul_t₀ hH]; unfold seg1Speed; linarith
  linarith

private lemma neg_seg1_h₀_right_slitPlane {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    {δ : ℝ} (hδ_pos : 0 < δ)
    {t : ℝ} (htd : seg1T₀ H z₀.im + δ ≤ t) :
    -(seg1_h₀ H z₀ t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  rw [seg1_h₀_eq_pure_im hz_re]
  simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  intro h_eq
  have hK : 0 < seg1Speed H := seg1Speed_pos hH
  have : t = seg1T₀ H z₀.im :=
    mul_left_cancel₀ hK.ne' <| by rw [seg1Speed_mul_t₀ hH]; unfold seg1Speed; linarith
  linarith

/-- Local alias: the arc reference is the shared `vertSeg_h_arc`. -/
private abbrev seg1_h_arc := vertSeg_h_arc

private lemma neg_seg1_h_arc_slitPlane {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im)
    {t : ℝ} (ht1 : 1/5 ≤ t) (ht3 : t ≤ 3/5) :
    -(seg1_h_arc z₀ t) ∈ Complex.slitPlane := by
  unfold seg1_h_arc vertSeg_h_arc
  rcases eq_or_lt_of_le ht1 with h_eq | ht1_lt
  · rw [Complex.mem_slitPlane_iff]
    right
    rw [← h_eq]
    have hpi := Real.pi_pos
    rw [show (fdArcAngle (1/5) : ℝ) = Real.pi / 3 from by unfold fdArcAngle; ring]
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
    simp only [Complex.neg_im, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_add]
    intro h_eq
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
  · rw [Complex.mem_slitPlane_iff]
    left
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
    rw [hz_re]
    linarith

/-- Local alias: the seg3 reference is the shared `vertSeg_h₃`. -/
private abbrev seg1_h₃ := vertSeg_h₃

private lemma neg_seg1_h₃_slitPlane {H : ℝ} {z₀ : ℂ} (hz_re : z₀.re = 1/2) (t : ℝ) :
    -(seg1_h₃ H z₀ t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  unfold seg1_h₃ vertSeg_h₃
  simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
  rw [hz_re]
  norm_num

/-- Local alias: the top horizontal reference is the shared `vertSeg_h₅`. -/
private abbrev seg1_h₅ := vertSeg_h₅

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
    (continuousOn_const.congr (fun t _ => deriv_seg1_h₀ H z₀ t))
  intro t ⟨_, htd⟩
  exact neg_seg1_h₀_left_slitPlane hH hz_re hδ_pos htd

private lemma seg1_right_ftc {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 1/5 - seg1T₀ H z₀.im) :
    IntervalIntegrable (fun t => deriv (seg1_h₀ H z₀) t / seg1_h₀ H z₀ t) volume
        (seg1T₀ H z₀.im + δ) (1/5) ∧
    ∫ t in (seg1T₀ H z₀.im + δ)..(1/5 : ℝ),
        deriv (seg1_h₀ H z₀) t / seg1_h₀ H z₀ t =
      Complex.log (-(seg1_h₀ H z₀ (1/5))) -
      Complex.log (-(seg1_h₀ H z₀ (seg1T₀ H z₀.im + δ))) := by
  apply LogDerivFTC.ftc_log_neg_on_segment (by linarith : seg1T₀ H z₀.im + δ ≤ 1/5)
    (seg1_h₀_continuous H z₀).continuousOn
    (fun t _ => (hasDerivAt_seg1_h₀ H z₀ t).differentiableAt)
    (continuousOn_const.congr (fun t _ => deriv_seg1_h₀ H z₀ t))
  intro t ⟨htd, _⟩
  exact neg_seg1_h₀_right_slitPlane hH hz_re hδ_pos htd

private lemma seg1_arc_ftc {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) :
    IntervalIntegrable
      (fun t => deriv (seg1_h_arc z₀) t / seg1_h_arc z₀ t) volume (1/5) (3/5) ∧
    ∫ t in (1/5 : ℝ)..(3/5),
        deriv (seg1_h_arc z₀) t / seg1_h_arc z₀ t =
      Complex.log (-(seg1_h_arc z₀ (3/5))) -
      Complex.log (-(seg1_h_arc z₀ (1/5))) := by
  apply LogDerivFTC.ftc_log_neg_on_segment (by norm_num : (1/5 : ℝ) ≤ 3/5)
    (vertSeg_h_arc_continuous z₀).continuousOn
    (fun t _ => (hasDerivAt_vertSeg_h_arc z₀ t).differentiableAt)
    ((Continuous.mul continuous_const (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp fdArcAngle_continuous).mul
        continuous_const))).continuousOn.congr (fun t _ => deriv_vertSeg_h_arc z₀ t))
  intro t ⟨ht1, ht3⟩
  exact neg_seg1_h_arc_slitPlane hz_re hc_lo ht1 ht3

private lemma seg1_seg4_ftc (H : ℝ) {z₀ : ℂ} (hz_re : z₀.re = 1/2) :
    IntervalIntegrable
      (fun t => deriv (seg1_h₃ H z₀) t / seg1_h₃ H z₀ t) volume (3/5) (4/5) ∧
    ∫ t in (3/5 : ℝ)..(4/5),
        deriv (seg1_h₃ H z₀) t / seg1_h₃ H z₀ t =
      Complex.log (-(seg1_h₃ H z₀ (4/5))) -
      Complex.log (-(seg1_h₃ H z₀ (3/5))) := by
  apply LogDerivFTC.ftc_log_neg_on_segment (by norm_num : (3/5 : ℝ) ≤ 4/5)
    (vertSeg_h₃_continuous H z₀).continuousOn
    (fun t _ => (hasDerivAt_vertSeg_h₃ H z₀ t).differentiableAt)
    (continuousOn_const.congr (fun t _ => deriv_vertSeg_h₃ H z₀ t))
  intro t _
  exact neg_seg1_h₃_slitPlane hz_re t

private lemma seg1_seg5_ftc (H : ℝ) {z₀ : ℂ} (hc_hi : z₀.im < H) :
    IntervalIntegrable
      (fun t => deriv (seg1_h₅ H z₀) t / seg1_h₅ H z₀ t) volume (4/5) 1 ∧
    ∫ t in (4/5 : ℝ)..(1 : ℝ),
        deriv (seg1_h₅ H z₀) t / seg1_h₅ H z₀ t =
      Complex.log (-(seg1_h₅ H z₀ 1)) -
      Complex.log (-(seg1_h₅ H z₀ (4/5))) := by
  apply LogDerivFTC.ftc_log_neg_on_segment (by norm_num : (4/5 : ℝ) ≤ 1)
    (vertSeg_h₅_continuous H z₀).continuousOn
    (fun t _ => (hasDerivAt_vertSeg_h₅ H z₀ t).differentiableAt)
    (continuousOn_const.congr (fun t _ => deriv_vertSeg_h₅ H z₀ t))
  intro t _
  exact neg_vertSeg_h₅_slitPlane hc_hi t

private lemma seg1_junction_15 (H : ℝ) (z₀ : ℂ) :
    seg1_h₀ H z₀ (1/5) = seg1_h_arc z₀ (1/5) := by
  unfold seg1_h₀ seg1_h_arc vertSeg_h_arc
  rw [show (fdArcAngle (1/5) : ℝ) = Real.pi / 3 from by unfold fdArcAngle; ring,
    exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
  refine Complex.ext ?_ ?_ <;> simp

private lemma seg1_closed (H : ℝ) (z₀ : ℂ) :
    seg1_h₀ H z₀ 0 = seg1_h₅ H z₀ 1 := by
  unfold seg1_h₀ seg1_h₅ vertSeg_h₅
  refine Complex.ext ?_ ?_ <;> simp
  ring

private lemma seg1_log_diff_eq_neg_pi_I {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2) {δ : ℝ} (hδ_pos : 0 < δ) :
    Complex.log (-(seg1_h₀ H z₀ (seg1T₀ H z₀.im - δ))) -
    Complex.log (-(seg1_h₀ H z₀ (seg1T₀ H z₀.im + δ))) = -(↑Real.pi * I) := by
  have hK : 0 < seg1Speed H := seg1Speed_pos hH
  have hKδ : 0 < seg1Speed H * δ := mul_pos hK hδ_pos
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
  rw [h_minus, h_plus,
    show -(((seg1Speed H * δ : ℝ) : ℂ) * I) = ((seg1Speed H * δ : ℝ) : ℂ) * (-I) from by ring,
    show -(((-(seg1Speed H * δ) : ℝ) : ℂ) * I) = ((seg1Speed H * δ : ℝ) : ℂ) * I from by
      push_cast; ring,
    Complex.log_ofReal_mul hKδ (neg_ne_zero.mpr I_ne_zero),
    Complex.log_ofReal_mul hKδ I_ne_zero, Complex.log_neg_I, Complex.log_I]
  ring

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
      fun _ ⟨hs3, hs4⟩ => fdBoundary_sub_eq_vertSeg_h₃ H z₀ hs3 hs4.le
  rw [fdBoundary_sub_eq_vertSeg_h₃ H z₀ ht3 ht4_lt.le,
    ← deriv_sub_const (f := fdBoundaryFun H) z₀, h_evEq.deriv_eq, div_eq_mul_inv, mul_comm]

private theorem fdBoundary_ftc_telescope_seg1 {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
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
  have h_left := seg1_left_ftc hH hz_re hδ_pos hδ_lt_t₀
  have h_right := seg1_right_ftc hH hz_re hδ_pos hδ_lt_one_fifth_sub
  have h_arc := seg1_arc_ftc hz_re hc_lo
  have h_seg4 := seg1_seg4_ftc H hz_re
  have h_seg5 := seg1_seg5_ftc H hc_hi
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
    rw [intervalIntegral.integral_congr_ae (ae_eq_vertSeg_h_arc H z₀)]
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
    rw [intervalIntegral.integral_congr_ae (ae_eq_vertSeg_h₅ H z₀)]
    exact h_seg5.2
  have hint_right_seg1 : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (t₀ + δ) (1/5) :=
    h_right.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((ae_eq_seg1_h₀ H z₀ (by linarith) le_rfl).mono (fun t ht hm => (ht hm).symm)))
  have hint_arc : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (1/5) (3/5) :=
    h_arc.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((ae_eq_vertSeg_h_arc H z₀).mono (fun t ht hm => (ht hm).symm)))
  have hint_seg4 : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (3/5) (4/5) :=
    h_seg4.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((ae_eq_seg1_h₃ H z₀).mono (fun t ht hm => (ht hm).symm)))
  have hint_seg5 : IntervalIntegrable
      (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (4/5) 1 :=
    h_seg5.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((ae_eq_vertSeg_h₅ H z₀).mono (fun t ht hm => (ht hm).symm)))
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
  rw [h_split, h_int_left, h_int_right_seg1, h_int_arc, h_int_seg4, h_int_seg5,
    seg1_junction_15 H z₀,
    show seg1_h_arc z₀ (3/5) = seg1_h₃ H z₀ (3/5) from vertSeg_junction_35 H z₀,
    show seg1_h₃ H z₀ (4/5) = seg1_h₅ H z₀ (4/5) from vertSeg_junction_45 H z₀,
    seg1_closed H z₀]
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

private lemma seg1_lin_lt_t₀ {H : ℝ} (hH : Real.sqrt 3 / 2 < H) {z₀ : ℂ}
    {ε : ℝ} (hε_thr : ε < seg1Threshold H z₀) :
    linDelta (seg1Speed H) ε < seg1T₀ H z₀.im := by
  unfold linDelta
  rw [div_lt_iff₀ (seg1Speed_pos hH), mul_comm, seg1Speed_mul_t₀ hH]
  exact lt_of_lt_of_le hε_thr (min_le_right _ _)

private lemma seg1_lin_lt_one_fifth_sub {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2) (hc_lo : Real.sqrt 3 / 2 < z₀.im)
    {ε : ℝ} (hε_thr : ε < seg1Threshold H z₀) :
    linDelta (seg1Speed H) ε < 1/5 - seg1T₀ H z₀.im := by
  unfold linDelta
  rw [div_lt_iff₀ (seg1Speed_pos hH), mul_comm, seg1Speed_mul_one_fifth_sub_t₀ hH]
  exact lt_of_lt_of_le (lt_of_lt_of_le hε_thr (le_trans (min_le_left _ _) (min_le_left _ _)))
    (norm_sub_one_le_im_sub_sqrt3 hz_re hc_lo.le)

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
    have h_lin_pos : 0 < linDelta (seg1Speed H) ε := linDelta_pos (seg1Speed_pos hH) hε
    have h_lin_lt_t₀ := seg1_lin_lt_t₀ hH hε_thr
    have h_lin_lt_one_fifth_sub := seg1_lin_lt_one_fifth_sub hH hz_re hc_lo hε_thr
    have h_t₀_pos : 0 < seg1T₀ H z₀.im := seg1T₀_pos hH hc_hi
    have h_t₀_lt : seg1T₀ H z₀.im < 1/5 := seg1T₀_lt_one_fifth hH hc_lo
    rw [transfer_integral z₀ (by linarith) le_rfl (by linarith) hγ,
      transfer_integral z₀ (by linarith) (by linarith) le_rfl hγ]
    exact fdBoundary_ftc_telescope_seg1 hH hz_re hc_lo hc_hi h_lin_pos
      h_lin_lt_t₀ h_lin_lt_one_fifth_sub
  hint_left := by
    intro ε hε hε_thr
    have h_lin_pos : 0 < linDelta (seg1Speed H) ε := linDelta_pos (seg1Speed_pos hH) hε
    have h_lin_lt_t₀ := seg1_lin_lt_t₀ hH hε_thr
    have h_t₀_pos : 0 < seg1T₀ H z₀.im := seg1T₀_pos hH hc_hi
    have h_t₀_lt : seg1T₀ H z₀.im < 1/5 := seg1T₀_lt_one_fifth hH hc_lo
    apply transfer_integrability z₀ (by linarith) le_rfl (by linarith) hγ
    have h_left := seg1_left_ftc hH hz_re h_lin_pos h_lin_lt_t₀
    exact h_left.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((ae_eq_seg1_h₀ H z₀ (by linarith) (by linarith)).mono (fun t ht hm => (ht hm).symm)))
  hint_right := by
    intro ε hε hε_thr
    have h_lin_pos : 0 < linDelta (seg1Speed H) ε := linDelta_pos (seg1Speed_pos hH) hε
    have h_lin_lt_t₀ := seg1_lin_lt_t₀ hH hε_thr
    have h_lin_lt_one_fifth_sub := seg1_lin_lt_one_fifth_sub hH hz_re hc_lo hε_thr
    have h_t₀_pos : 0 < seg1T₀ H z₀.im := seg1T₀_pos hH hc_hi
    have h_t₀_lt : seg1T₀ H z₀.im < 1/5 := seg1T₀_lt_one_fifth hH hc_lo
    apply transfer_integrability z₀ (by linarith) (by linarith) le_rfl hγ
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
        ((ae_eq_vertSeg_h_arc H z₀).mono (fun t ht hm => (ht hm).symm)))
    have hint_seg4 : IntervalIntegrable
        (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
        volume (3/5) (4/5) :=
      h_seg4.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
        ((ae_eq_seg1_h₃ H z₀).mono (fun t ht hm => (ht hm).symm)))
    have hint_seg5 : IntervalIntegrable
        (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
        volume (4/5) 1 :=
      h_seg5.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
        ((ae_eq_vertSeg_h₅ H z₀).mono (fun t ht hm => (ht hm).symm)))
    exact ((hint_right_seg1.trans hint_arc).trans hint_seg4).trans hint_seg5
  h_limit := tendsto_const_nhds

end
