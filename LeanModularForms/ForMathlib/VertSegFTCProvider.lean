/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.BoundaryWindingSeg1Proof
import LeanModularForms.ForMathlib.SegmentAnalysis
import LeanModularForms.ForMathlib.SegmentFTC

/-!
# Shared helpers for the vertical-edge `ArcFTCHyp` providers

The files `Seg1FTCProvider.lean` and `Seg4FTCProvider.lean` build
`ArcFTCHyp` for points on the right and left vertical edges of the
fundamental domain boundary. They share a great deal of mechanical
infrastructure about the arc piece (`vertSeg_h_arc`), the upper
horizontal piece (`vertSeg_h₅`), and the seg3 piece (`vertSeg_h₃`),
all of which use `fdBoundaryFun H t - z₀` and only differ on which
side `z₀` lies on.

This file collects:
* the shared reference functions `vertSeg_h_arc`, `vertSeg_h₃`,
  `vertSeg_h₅` (which depend only on `H`, `z₀`, `t`),
* their continuity / `HasDerivAt` / derivative formulas,
* the equality `fdBoundaryFun H t - z₀ = ...` on each segment,
* slitPlane membership lemmas that are direction-independent
  (`vertSeg_h₅`'s positive imaginary part, and the four `junction`
  identities).

Side-specific lemmas (the `slitPlane` membership for `-h` versus `h`,
the seg1-vs-seg4 t₀ computations, and the final FTC telescopes)
remain in their respective files.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ### Arc reference function (shared) -/

/-- The arc trajectory reference for any vertical-edge target `z₀`. -/
def vertSeg_h_arc (z₀ : ℂ) (t : ℝ) : ℂ :=
  exp (↑(fdArcAngle t) * I) - z₀

lemma fdBoundary_sub_eq_vertSeg_h_arc {H : ℝ} (z₀ : ℂ) {t : ℝ}
    (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t - z₀ = vertSeg_h_arc z₀ t := by
  unfold vertSeg_h_arc
  rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2]

lemma vertSeg_h_arc_continuous (z₀ : ℂ) : Continuous (vertSeg_h_arc z₀) := by
  unfold vertSeg_h_arc
  exact (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp fdArcAngle_continuous).mul continuous_const)).sub
    continuous_const

lemma hasDerivAt_vertSeg_h_arc (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (vertSeg_h_arc z₀)
      (↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I)) t := by
  unfold vertSeg_h_arc
  have h1 : HasDerivAt fdArcAngle (5 * Real.pi / 6) t := by
    unfold fdArcAngle
    exact (((((hasDerivAt_id t).const_mul (5 : ℝ)).sub_const 1).mul_const
      (Real.pi / 6)).const_add (Real.pi / 3)).congr_deriv (by ring)
  have h2 : HasDerivAt (fun s : ℝ => (↑(fdArcAngle s) : ℂ) * I)
      (↑(5 * Real.pi / 6) * I) t :=
    (h1.ofReal_comp.mul_const I).congr_deriv (by push_cast; ring)
  exact (h2.cexp.congr_deriv (by ring)).sub_const z₀

lemma deriv_vertSeg_h_arc (z₀ : ℂ) (t : ℝ) :
    deriv (vertSeg_h_arc z₀) t = ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I) :=
  (hasDerivAt_vertSeg_h_arc z₀ t).deriv

/-! ### Seg3 reference function (shared definition) -/

/-- The seg3 trajectory reference for any vertical-edge target `z₀`. -/
def vertSeg_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((-1/2 - z₀.re : ℝ) : ℂ) +
  ((Real.sqrt 3 / 2 + (5 * t - 3) * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I

lemma fdBoundary_sub_eq_vertSeg_h₃ (H : ℝ) (z₀ : ℂ) {t : ℝ}
    (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    fdBoundaryFun H t - z₀ = vertSeg_h₃ H z₀ t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    ht4, ite_true, ite_false, vertSeg_h₃]
  refine Complex.ext ?_ ?_ <;> simp

lemma vertSeg_h₃_continuous (H : ℝ) (z₀ : ℂ) : Continuous (vertSeg_h₃ H z₀) := by
  unfold vertSeg_h₃; fun_prop

lemma hasDerivAt_vertSeg_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (vertSeg_h₃ H z₀) ((seg1Speed H : ℂ) * I) t := by
  have h_real : HasDerivAt
      (fun s : ℝ => Real.sqrt 3 / 2 + (5 * s - 3) * (H - Real.sqrt 3 / 2) - z₀.im)
      (seg1Speed H) t := by
    have hd : HasDerivAt (fun s : ℝ => 5 * s - 3) 5 t :=
      (((hasDerivAt_id t).const_mul 5).sub_const 3).congr_deriv (by ring)
    exact (((hd.mul_const (H - Real.sqrt 3 / 2)).const_add
      (Real.sqrt 3 / 2)).sub_const z₀.im).congr_deriv (by unfold seg1Speed; ring)
  exact ((hasDerivAt_const t (((-1/2 - z₀.re : ℝ) : ℂ))).add
    ((h_real.ofReal_comp.congr_deriv (by ring)).mul_const I)).congr_deriv (by ring)

lemma deriv_vertSeg_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (vertSeg_h₃ H z₀) t = (seg1Speed H : ℂ) * I :=
  (hasDerivAt_vertSeg_h₃ H z₀ t).deriv

/-! ### Top horizontal reference function (shared) -/

/-- The top horizontal (seg5) trajectory reference for any vertical-edge target. -/
def vertSeg_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((5 * t - 9/2 - z₀.re : ℝ) : ℂ) + ((H - z₀.im : ℝ) : ℂ) * I

lemma fdBoundary_sub_eq_vertSeg_h₅ (H : ℝ) (z₀ : ℂ) {t : ℝ} (ht : 4/5 < t) :
    fdBoundaryFun H t - z₀ = vertSeg_h₅ H z₀ t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    show ¬t ≤ 4/5 from by linarith, ite_false, vertSeg_h₅]
  refine Complex.ext ?_ ?_ <;> simp

lemma vertSeg_h₅_continuous (H : ℝ) (z₀ : ℂ) : Continuous (vertSeg_h₅ H z₀) := by
  unfold vertSeg_h₅; fun_prop

lemma hasDerivAt_vertSeg_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (vertSeg_h₅ H z₀) (5 : ℂ) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((5 * s - 9/2 - z₀.re : ℝ) : ℂ)) 5 t := by
    have h_real : HasDerivAt (fun s : ℝ => 5 * s - 9/2 - z₀.re) 5 t :=
      ((((hasDerivAt_id t).const_mul 5).sub_const (9/2)).sub_const z₀.re).congr_deriv (by ring)
    exact (h_real.ofReal_comp).congr_deriv (by push_cast; ring)
  exact (h1.add_const _).congr_deriv (by ring)

lemma deriv_vertSeg_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (vertSeg_h₅ H z₀) t = 5 :=
  (hasDerivAt_vertSeg_h₅ H z₀ t).deriv

/-- `vertSeg_h₅` lies in `slitPlane` whenever `z₀.im < H`. -/
lemma vertSeg_h₅_slitPlane {H : ℝ} {z₀ : ℂ} (hc_hi : z₀.im < H) (t : ℝ) :
    vertSeg_h₅ H z₀ t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  unfold vertSeg_h₅
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
  intro h
  linarith

/-- `-vertSeg_h₅` lies in `slitPlane` whenever `z₀.im < H`. -/
lemma neg_vertSeg_h₅_slitPlane {H : ℝ} {z₀ : ℂ} (hc_hi : z₀.im < H) (t : ℝ) :
    -(vertSeg_h₅ H z₀ t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  unfold vertSeg_h₅
  simp only [Complex.neg_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
  intro h
  linarith

/-! ### Junction identities (shared) -/

lemma vertSeg_junction_35 (H : ℝ) (z₀ : ℂ) :
    vertSeg_h_arc z₀ (3/5) = vertSeg_h₃ H z₀ (3/5) := by
  unfold vertSeg_h_arc vertSeg_h₃
  rw [show (fdArcAngle (3/5) : ℝ) = 2 * Real.pi / 3 from by unfold fdArcAngle; ring,
    exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  refine Complex.ext ?_ ?_ <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, zero_add, add_zero] <;> ring

lemma vertSeg_junction_45 (H : ℝ) (z₀ : ℂ) :
    vertSeg_h₃ H z₀ (4/5) = vertSeg_h₅ H z₀ (4/5) := by
  unfold vertSeg_h₃ vertSeg_h₅
  refine Complex.ext ?_ ?_ <;> simp <;> ring

/-! ### Shared ae-equality for h_arc, h₃, h₅ pieces -/

lemma ae_eq_vertSeg_h_arc (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (1/5 : ℝ) (3/5) →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (vertSeg_h_arc z₀) t / vertSeg_h_arc z₀ t := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (3/5 : ℝ))] with t ht_ne ht_mem
  rw [uIoc_of_le (by norm_num : (1/5 : ℝ) ≤ 3/5)] at ht_mem
  have ht1 : 1/5 < t := ht_mem.1
  have ht3_lt : t < 3/5 :=
    lt_of_le_of_ne ht_mem.2 fun h => ht_ne (Set.mem_singleton_iff.mpr h)
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] vertSeg_h_arc z₀ :=
    Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht3_lt))
      fun _ ⟨hs1, hs3⟩ => fdBoundary_sub_eq_vertSeg_h_arc z₀ hs1 hs3.le
  rw [fdBoundary_sub_eq_vertSeg_h_arc z₀ ht1 ht3_lt.le,
    ← deriv_sub_const (f := fdBoundaryFun H) z₀, h_evEq.deriv_eq, div_eq_mul_inv, mul_comm]

lemma ae_eq_vertSeg_h₅ (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (4/5 : ℝ) 1 →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (vertSeg_h₅ H z₀) t / vertSeg_h₅ H z₀ t := by
  refine ae_of_all _ fun t ht_mem => ?_
  rw [uIoc_of_le (by norm_num : (4/5 : ℝ) ≤ 1)] at ht_mem
  have ht4 : 4/5 < t := ht_mem.1
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] vertSeg_h₅ H z₀ :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht4) fun _ hs => fdBoundary_sub_eq_vertSeg_h₅ H z₀ hs
  rw [fdBoundary_sub_eq_vertSeg_h₅ H z₀ ht4,
    ← deriv_sub_const (f := fdBoundaryFun H) z₀, h_evEq.deriv_eq, div_eq_mul_inv, mul_comm]

end
