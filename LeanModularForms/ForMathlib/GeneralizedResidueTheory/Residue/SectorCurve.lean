/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LeanModularForms.ForMathlib.ClassicalCPV
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.PrincipalValue
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue

/-!
# Sector Curve PV Computation (Lemma 3.1)

Model sector-curve and PV integral computations for Laurent series terms.
This implements the key computation from Hungerbuhler-Wasem (arXiv:1808.00997v2)
Lemma 3.1: the principal value of `dz/z` along a sector curve equals `i * alpha`,
where `alpha` is the opening angle of the sector.

## Main Definitions

* `sectorCurve` -- the model sector-curve parameterized on [0,3]

## Main Results

* `pv_sector_dz_over_z` -- PV of `dz/z` along sector curve equals `I * alpha`

See `SectorCurveLemma.lean` for higher-order results (`pv_sector_higher_power`,
`cauchyPV_sectorCurve_simplePole`, etc.).

## Mathematical Overview

The sector curve `sigma_{r,alpha}` is a closed curve from the origin, along the
positive real axis to radius `r`, then around an arc of angle `alpha`, then back
to the origin along the ray at angle `alpha`. Specifically:

* Segment 1 (`t in [0,1]`): radial ray `t |-> t * r` (outgoing along real axis)
* Segment 2 (`t in [1,2]`): arc `t |-> r * exp(i * (t-1) * alpha)` at radius `r`
* Segment 3 (`t in [2,3]`): radial ray `t |-> (3-t) * r * exp(i * alpha)` (returning)

The PV of `dz/z` along this curve decomposes as:
* Segments 1 and 3 contribute symmetric logarithmic divergences that cancel
* Segment 2 contributes `int_0^alpha i d theta = i * alpha`

Reference: Hungerbuhler-Wasem, arXiv:1808.00997v2, Lemma 3.1.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- The model sector curve parameterized on [0,3].
- [0,1]: radial ray from 0 to r along the positive real axis
- [1,2]: circular arc of radius r from angle 0 to angle alpha
- [2,3]: radial ray from r*exp(i*alpha) back to 0 -/
def sectorCurve (r : ℝ) (α : ℝ) (t : ℝ) : ℂ :=
  if t ≤ 1 then
    ↑(t * r)
  else if t ≤ 2 then
    ↑r * exp (I * ↑((t - 1) * α))
  else
    ↑((3 - t) * r) * exp (I * ↑α)

/-- The sector curve at t=0 is 0. -/
theorem sectorCurve_zero (r : ℝ) (α : ℝ) :
    sectorCurve r α 0 = 0 := by
  simp [sectorCurve]

/-- The sector curve at t=3 is 0. -/
theorem sectorCurve_three (r : ℝ) (α : ℝ) :
    sectorCurve r α 3 = 0 := by
  simp [sectorCurve, show ¬(3 : ℝ) ≤ 2 from by norm_num]

/-- Segment 1: for t in [0,1], the sector curve is `t * r`. -/
theorem sectorCurve_seg1 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    sectorCurve r α t = ↑(t * r) := by
  simp [sectorCurve, ht.2]

/-- Segment 2: for t in [1,2], the sector curve is `r * exp(i*(t-1)*alpha)`. -/
theorem sectorCurve_seg2 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 1 2) :
    sectorCurve r α t = ↑r * exp (I * ↑((t - 1) * α)) := by
  rcases eq_or_lt_of_le ht.1 with rfl | h1
  · simp [sectorCurve, Complex.exp_zero]
  · simp only [sectorCurve, if_neg (not_le.mpr h1), if_pos ht.2]

/-- Segment 3: for t in [2,3], the sector curve is `(3-t)*r * exp(i*alpha)`. -/
theorem sectorCurve_seg3 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 2 3) :
    sectorCurve r α t = ↑((3 - t) * r) * exp (I * ↑α) := by
  rcases eq_or_lt_of_le ht.1 with rfl | h2
  · simp only [sectorCurve, show ¬(2 : ℝ) ≤ 1 from by norm_num,
      show (2 : ℝ) ≤ 2 from le_refl 2, ↓reduceIte]
    push_cast
    ring_nf
  · simp only [sectorCurve, if_neg (not_le.mpr (one_lt_two.trans h2)),
      if_neg (not_le.mpr h2)]

/-- The sector curve is continuous on [0,3]. -/
theorem sectorCurve_continuousOn (r : ℝ) (α : ℝ) :
    ContinuousOn (sectorCurve r α) (Icc 0 3) := by
  have h_union : Icc (0 : ℝ) 3 = Icc 0 1 ∪ Icc 1 2 ∪ Icc 2 3 := by
    rw [Set.Icc_union_Icc_eq_Icc (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 2),
      Set.Icc_union_Icc_eq_Icc (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) ≤ 3)]
  rw [h_union]
  have hc1 : ContinuousOn (sectorCurve r α) (Icc 0 1) :=
    ContinuousOn.congr (by fun_prop) fun t ht => sectorCurve_seg1 r α t ht
  have hc2 : ContinuousOn (sectorCurve r α) (Icc 1 2) :=
    ContinuousOn.congr (by fun_prop) fun t ht => sectorCurve_seg2 r α t ht
  have hc3 : ContinuousOn (sectorCurve r α) (Icc 2 3) :=
    ContinuousOn.congr (by fun_prop) fun t ht => sectorCurve_seg3 r α t ht
  exact (hc1.union_of_isClosed hc2 isClosed_Icc isClosed_Icc).union_of_isClosed hc3
    (isClosed_Icc.union isClosed_Icc) isClosed_Icc

/-- On the arc segment (t in [1,2]), the sector curve has modulus r. -/
theorem sectorCurve_norm_on_arc (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 1 2) :
    ‖sectorCurve r α t‖ = r := by
  rw [sectorCurve_seg2 r α t ht]
  simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  exact Complex.norm_of_nonneg hr.le

/-- Derivative on segment 1 (t in (0,1)): `deriv (sectorCurve r alpha) t = r`. -/
theorem deriv_sectorCurve_seg1 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    deriv (sectorCurve r α) t = ↑r := by
  have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => ↑(s * r) := by
    filter_upwards [Iio_mem_nhds ht.2] with s hs
    simp only [sectorCurve, if_pos (mem_Iio.mp hs).le]
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  exact (by simpa using (hasDerivAt_id t).mul_const r :
    HasDerivAt (fun s => s * r) r t).ofReal_comp.deriv

/-- Derivative on segment 2 (t in (1,2)):
  `deriv (sectorCurve r alpha) t = r * (I * alpha) * exp(I * (t-1) * alpha)`. -/
theorem deriv_sectorCurve_seg2 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 1 2) :
    deriv (sectorCurve r α) t =
      ↑r * (I * ↑α) * exp (I * ↑((t - 1) * α)) := by
  have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => ↑r * exp (I * ↑((s - 1) * α)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    rw [sectorCurve_seg2 r α s ⟨hs.1.le, hs.2.le⟩]
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have h_inner : HasDerivAt (fun s => (↑((s - 1) * α) : ℂ)) (↑α) t :=
    (by simpa using ((hasDerivAt_id t).sub_const 1).mul_const α :
      HasDerivAt (fun s => (s - 1) * α) α t).ofReal_comp
  have h_exp : HasDerivAt (fun s => exp (I * ↑((s - 1) * α)))
      (I * ↑α * exp (I * ↑((t - 1) * α))) t := by
    convert (hasDerivAt_exp (I * ↑((t - 1) * α))).comp t
      ((hasDerivAt_const t I).mul h_inner) using 1
    ring
  have h_full : HasDerivAt (fun s => ↑r * exp (I * ↑((s - 1) * α)))
      (↑r * (I * ↑α * exp (I * ↑((t - 1) * α)))) t := by
    convert (hasDerivAt_const t (↑r : ℂ)).mul h_exp using 1
    ring
  rw [h_full.deriv]
  ring

/-- Derivative on segment 3 (t in (2,3)):
  `deriv (sectorCurve r alpha) t = -r * exp(I * alpha)`. -/
theorem deriv_sectorCurve_seg3 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 2 3) :
    deriv (sectorCurve r α) t = -(↑r) * exp (I * ↑α) := by
  have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => ↑((3 - s) * r) * exp (I * ↑α) := by
    filter_upwards [Ioi_mem_nhds ht.1] with s hs
    simp only [sectorCurve,
      if_neg (not_le.mpr ((by norm_num : (1 : ℝ) < 2).trans (mem_Ioi.mp hs))),
      if_neg (not_le.mpr (mem_Ioi.mp hs))]
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have h_inner : HasDerivAt (fun s => (↑((3 - s) * r) : ℂ)) (↑(-r)) t :=
    (by convert ((hasDerivAt_const t 3).sub (hasDerivAt_id t)).mul_const r using 1; ring :
      HasDerivAt (fun s => (3 - s) * r) (-r) t).ofReal_comp
  rw [(h_inner.mul_const (exp (I * ↑α))).deriv]
  push_cast
  ring

/-- The integrand `(sectorCurve r alpha t)^(-1) * deriv (sectorCurve r alpha) t`
on segment 1 (t in (0,1)) simplifies to `1/t` (as a complex number). -/
theorem pv_integrand_seg1 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = ↑(t⁻¹) := by
  rw [sectorCurve_seg1 r α t ⟨ht.1.le, ht.2.le⟩, deriv_sectorCurve_seg1 r α t ht]
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  push_cast
  field_simp

/-- The integrand on segment 2 (t in (1,2)) simplifies to `I * alpha`. -/
theorem pv_integrand_seg2 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 1 2) :
    (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = I * ↑α := by
  rw [sectorCurve_seg2 r α t ⟨ht.1.le, ht.2.le⟩, deriv_sectorCurve_seg2 r α t ht]
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have h_exp_ne : exp (I * ↑((t - 1) * α)) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- On segment 1, the norm of the sector curve is `t * r`. -/
theorem sectorCurve_norm_seg1 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    ‖sectorCurve r α t‖ = t * r := by
  rw [sectorCurve_seg1 r α t ht]
  exact Complex.norm_of_nonneg (mul_nonneg ht.1 hr.le)

/-- On segment 3, the norm of the sector curve is `(3 - t) * r`. -/
theorem sectorCurve_norm_seg3' (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 2 3) :
    ‖sectorCurve r α t‖ = (3 - t) * r := by
  rw [sectorCurve_seg3 r α t ht, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
    Complex.norm_of_nonneg (mul_nonneg (by linarith [ht.2]) hr.le)]

/-- The logarithmic integrals from segments 1 and 3 cancel. -/
theorem log_cancellation (r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    (∫ t in (ε / r)..(1 : ℝ), (↑(t⁻¹) : ℂ)) +
    (∫ t in (2 : ℝ)..(3 - ε / r), (-(↑((3 - t)⁻¹)) : ℂ)) = 0 := by
  have hεr_pos : 0 < ε / r := div_pos hε hr
  have hεr_lt1 : ε / r < 1 := by rwa [div_lt_one hr]
  have h1 : ∫ t in (ε / r)..(1 : ℝ), (t⁻¹ : ℝ) = -(Real.log (ε / r)) := by
    rw [integral_inv_of_pos hεr_pos one_pos, Real.log_div one_ne_zero hεr_pos.ne',
      Real.log_one, zero_sub]
  have h2 : ∫ t in (2 : ℝ)..(3 - ε / r), -((3 - t)⁻¹ : ℝ) = Real.log (ε / r) := by
    rw [intervalIntegral.integral_neg]
    have h_sub : ∫ t in (2 : ℝ)..(3 - ε / r), (3 - t)⁻¹ = ∫ u in (ε / r)..1, u⁻¹ := by
      rw [intervalIntegral.integral_comp_sub_left (fun u => u⁻¹) (3 : ℝ)
        (a := (2 : ℝ)) (b := 3 - ε / r)]
      congr 1 <;> ring
    rw [h_sub, integral_inv_of_pos hεr_pos one_pos, Real.log_div one_ne_zero hεr_pos.ne',
      Real.log_one, zero_sub, neg_neg]
  have h1c : ∫ t in (ε / r)..(1 : ℝ), (↑(t⁻¹) : ℂ) = ↑(-(Real.log (ε / r))) := by
    rw [← h1, intervalIntegral.integral_ofReal]
  have h2c : ∫ t in (2 : ℝ)..(3 - ε / r), (-(↑((3 - t)⁻¹)) : ℂ) = ↑(Real.log (ε / r)) := by
    simp_rw [show ∀ t : ℝ, (-(↑((3 - t)⁻¹) : ℂ)) = (↑((-((3 - t)⁻¹)) : ℝ)) from
      fun _ => by push_cast; ring, intervalIntegral.integral_ofReal, h2]
  rw [h1c, h2c, ← Complex.ofReal_add, neg_add_cancel, Complex.ofReal_zero]

private theorem pv_cutoff_F_integrable_0_delta (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    IntervalIntegrable F volume 0 (ε / r) := by
  intro F
  set δ := ε / r
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  apply (intervalIntegrable_const (c := (0 : ℂ))).congr
  intro t ht
  rw [Set.uIoc_of_le hδ.le] at ht
  dsimp only [F]
  simp only [sub_zero]
  rw [if_neg (not_lt.mpr ?_)]
  rw [sectorCurve_norm_seg1 r hr α t ⟨ht.1.le, ht.2.trans hδ1.le⟩]
  calc t * r ≤ δ * r := mul_le_mul_of_nonneg_right ht.2 hr.le
    _ = ε := div_mul_cancel₀ ε hr.ne'

private theorem pv_cutoff_F_integrable_3delta_3 (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    IntervalIntegrable F volume (3 - ε / r) 3 := by
  intro F
  set δ := ε / r
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  apply (intervalIntegrable_const (c := (0 : ℂ))).congr
  intro t ht
  rw [Set.uIoc_of_le (by linarith : 3 - δ ≤ 3)] at ht
  dsimp only [F]
  simp only [sub_zero]
  rw [if_neg (not_lt.mpr ?_)]
  rw [sectorCurve_norm_seg3' r hr α t ⟨by linarith [ht.1], ht.2⟩]
  calc (3 - t) * r ≤ δ * r := mul_le_mul_of_nonneg_right (by linarith [ht.1]) hr.le
    _ = ε := div_mul_cancel₀ ε hr.ne'

private theorem pv_cutoff_F_integrable_delta_1 (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    IntervalIntegrable F volume (ε / r) 1 := by
  intro F
  set δ := ε / r
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  have hcont : ContinuousOn (fun t : ℝ => (↑(t⁻¹) : ℂ)) (Set.uIcc δ 1) := by
    rw [Set.uIcc_of_le hδ1.le]
    intro t ht
    exact (Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_inv₀ (hδ.trans_le ht.1).ne')).continuousWithinAt
  rw [intervalIntegrable_iff, Set.uIoc_of_le hδ1.le]
  have h_eq : ∀ t ∈ Ioo δ (1 : ℝ), F t = (↑(t⁻¹) : ℂ) := fun t ⟨htδ, ht1⟩ => by
    dsimp only [F]
    simp only [sub_zero]
    rw [if_pos]
    · exact pv_integrand_seg1 r hr α t ⟨hδ.trans htδ, ht1⟩
    · rw [sectorCurve_norm_seg1 r hr α t ⟨(hδ.trans htδ).le, ht1.le⟩]
      calc ε = δ * r := (div_mul_cancel₀ ε hr.ne').symm
        _ < t * r := by nlinarith
  have h_g_Ioo : IntegrableOn (fun t : ℝ => (↑(t⁻¹) : ℂ)) (Ioo δ 1) volume :=
    (intervalIntegrable_iff.mp hcont.intervalIntegrable).mono_set (by
      rw [Set.uIoc_of_le hδ1.le]; exact Ioo_subset_Ioc_self)
  rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact h_g_Ioo.congr ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm)

private theorem pv_cutoff_F_integrable_1_2 (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (_hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    IntervalIntegrable F volume 1 2 := by
  intro F
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  have h_eq : ∀ t ∈ Ioo (1 : ℝ) 2, F t = I * ↑α := by
    intro t ⟨ht1, ht2⟩
    dsimp only [F]
    simp only [sub_zero]
    rw [if_pos]
    · rw [sectorCurve_seg2 r α t ⟨ht1.le, ht2.le⟩,
          deriv_sectorCurve_seg2 r α t ⟨ht1, ht2⟩]
      have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
      have h_exp_ne : exp (I * ↑((t - 1) * α)) ≠ 0 := Complex.exp_ne_zero _
      field_simp
    · rw [sectorCurve_seg2 r α t ⟨ht1.le, ht2.le⟩]
      simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
      rw [Complex.norm_of_nonneg hr.le]
      linarith
  have h_const_Ioo : IntegrableOn (fun (_ : ℝ) => I * (↑α : ℂ)) (Ioo (1 : ℝ) 2) volume :=
    (intervalIntegrable_iff.mp (intervalIntegrable_const :
      IntervalIntegrable (fun _ => I * (↑α : ℂ)) volume 1 2)).mono_set (by
        rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]; exact Ioo_subset_Ioc_self)
  rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact h_const_Ioo.congr
    ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm)

private theorem pv_cutoff_F_integrable_2_3delta (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    IntervalIntegrable F volume 2 (3 - ε / r) := by
  intro F
  set δ := ε / r
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  have h3δ : 2 < 3 - δ := by linarith
  rw [intervalIntegrable_iff, Set.uIoc_of_le h3δ.le]
  have h_eq : ∀ t ∈ Ioo (2 : ℝ) (3 - δ), F t = -(↑((3 - t)⁻¹) : ℂ) := by
    intro t ⟨ht2, ht3δ⟩
    have h3 : t < 3 := by linarith
    dsimp only [F]
    simp only [sub_zero]
    rw [if_pos]
    · rw [sectorCurve_seg3 r α t ⟨ht2.le, h3.le⟩,
          deriv_sectorCurve_seg3 r α t ⟨ht2, h3⟩]
      have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
      have h_exp_ne : exp (I * ↑α) ≠ 0 := Complex.exp_ne_zero _
      have h3t_ne : (3 - t : ℝ) ≠ 0 := by linarith
      push_cast
      field_simp
    · rw [sectorCurve_norm_seg3' r hr α t ⟨ht2.le, h3.le⟩]
      calc ε = δ * r := (div_mul_cancel₀ ε hr.ne').symm
        _ < (3 - t) * r := by nlinarith
  have hcont : ContinuousOn (fun t : ℝ => -(↑((3 - t)⁻¹) : ℂ)) (Set.uIcc 2 (3 - δ)) := by
    rw [Set.uIcc_of_le h3δ.le]
    intro t ht
    exact (continuous_neg.continuousAt.comp
      (Complex.continuous_ofReal.continuousAt.comp
        ((continuousAt_inv₀ (show (0 : ℝ) < 3 - t by linarith [ht.2]).ne').comp
         (continuousAt_const.sub continuousAt_id)))).continuousWithinAt
  have h_g_Ioo : IntegrableOn (fun t : ℝ => -(↑((3 - t)⁻¹) : ℂ))
      (Ioo (2 : ℝ) (3 - δ)) volume :=
    (intervalIntegrable_iff.mp hcont.intervalIntegrable).mono_set (by
      rw [Set.uIoc_of_le h3δ.le]; exact Ioo_subset_Ioc_self)
  rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact h_g_Ioo.congr ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm)

private theorem pv_cutoff_integral_seg1_eq_inv (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    let δ := ε / r
    ∫ t in δ..(1 : ℝ), F t = ∫ t in δ..(1 : ℝ), (↑(t⁻¹) : ℂ) := by
  intro F δ
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  have h_on_Ioo : ∀ t ∈ Ioo δ 1, F t = (↑(t⁻¹) : ℂ) := fun t ⟨htδ, ht1⟩ => by
    dsimp only [F]
    simp only [sub_zero]
    rw [if_pos]
    · rw [sectorCurve_seg1 r α t ⟨(hδ.trans htδ).le, ht1.le⟩,
          deriv_sectorCurve_seg1 r α t ⟨hδ.trans htδ, ht1⟩]
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hδ.trans htδ).ne'
      have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
      push_cast
      field_simp
    · rw [sectorCurve_norm_seg1 r hr α t ⟨(hδ.trans htδ).le, ht1.le⟩]
      calc ε = δ * r := (div_mul_cancel₀ ε hr.ne').symm
        _ < t * r := by nlinarith
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(Filter.eventuallyEq_set.mp Ioo_ae_eq_Ioc)] with t ht
  rw [Set.uIoc_of_le hδ1.le]
  exact fun ht_mem => h_on_Ioo t (ht.mpr ht_mem)

private theorem pv_cutoff_integral_seg2_eq_Ialpha (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (_hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    ∫ t in (1 : ℝ)..2, F t = I * ↑α := by
  intro F
  have h_on_Ioo : ∀ t ∈ Ioo 1 2, F t = I * ↑α := by
    intro t ⟨ht1, ht2⟩
    dsimp only [F]
    simp only [sub_zero]
    rw [if_pos]
    · rw [sectorCurve_seg2 r α t ⟨ht1.le, ht2.le⟩,
          deriv_sectorCurve_seg2 r α t ⟨ht1, ht2⟩]
      have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
      have h_exp_ne : exp (I * ↑((t - 1) * α)) ≠ 0 := Complex.exp_ne_zero _
      field_simp
    · rw [sectorCurve_seg2 r α t ⟨ht1.le, ht2.le⟩]
      simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
      rw [Complex.norm_of_nonneg hr.le]
      linarith
  show ∫ (t : ℝ) in (1 : ℝ)..2, F t = I * ↑α
  rw [intervalIntegral.integral_congr_ae (by
    filter_upwards [(Filter.eventuallyEq_set.mp Ioo_ae_eq_Ioc)] with t ht
    rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    exact fun ht_mem => h_on_Ioo t (ht.mpr ht_mem)), intervalIntegral.integral_const]
  module

private theorem pv_cutoff_integral_seg3_eq_neg_inv (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    let δ := ε / r
    ∫ t in (2 : ℝ)..(3 - δ), F t =
      ∫ t in (2 : ℝ)..(3 - δ), -(↑((3 - t)⁻¹) : ℂ) := by
  intro F δ
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  have h3δ : 2 < 3 - δ := by linarith
  have h_on_Ioo : ∀ t ∈ Ioo 2 (3 - δ), F t = -(↑((3 - t)⁻¹) : ℂ) := by
    intro t ⟨ht2, ht3δ⟩
    have h3 : t < 3 := by linarith
    dsimp only [F]
    simp only [sub_zero]
    rw [if_pos]
    · rw [sectorCurve_seg3 r α t ⟨ht2.le, h3.le⟩,
          deriv_sectorCurve_seg3 r α t ⟨ht2, h3⟩]
      have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
      have h_exp_ne : exp (I * ↑α) ≠ 0 := Complex.exp_ne_zero _
      have h3t_ne : (3 - t : ℝ) ≠ 0 := by linarith
      push_cast
      field_simp
    · rw [sectorCurve_norm_seg3' r hr α t ⟨ht2.le, h3.le⟩]
      calc ε = δ * r := (div_mul_cancel₀ ε hr.ne').symm
        _ < (3 - t) * r := by nlinarith
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(Filter.eventuallyEq_set.mp Ioo_ae_eq_Ioc)] with t ht
  rw [Set.uIoc_of_le h3δ.le]
  exact fun ht_mem => h_on_Ioo t (ht.mpr ht_mem)

/-- For `0 < ε < r`, the PV cutoff integral of `dz/z` along the sector curve equals `I * α`.
This is the key cancellation lemma: the logarithmic divergences from segments 1 and 3 cancel. -/
theorem pv_sector_cutoff_eq (r : ℝ) (hr : 0 < r) (α : ℝ)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    ∫ t in (0 : ℝ)..3,
      (if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t
        else 0) = I * ↑α := by
  set F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
      then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
  set δ := ε / r
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  have hFint_0δ := pv_cutoff_F_integrable_0_delta r hr α ε hε hεr
  have hFint_3δ3 := pv_cutoff_F_integrable_3delta_3 r hr α ε hε hεr
  have hFint_δ1 := pv_cutoff_F_integrable_delta_1 r hr α ε hε hεr
  have hFint_12 := pv_cutoff_F_integrable_1_2 r hr α ε hε hεr
  have hFint_2_3δ := pv_cutoff_F_integrable_2_3delta r hr α ε hε hεr
  have hFint_01 := hFint_0δ.trans hFint_δ1
  have hFint_02 := hFint_01.trans hFint_12
  have hFint_0_3δ := hFint_02.trans hFint_2_3δ
  have hI1 : ∫ t in (0 : ℝ)..δ, F t = 0 := by
    rw [show ∫ t in (0 : ℝ)..δ, F t = ∫ t in (0 : ℝ)..δ, (0 : ℂ) from by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hδ.le] at ht
      dsimp only [F]
      simp only [sub_zero]
      rw [if_neg (not_lt.mpr ?_)]
      rw [sectorCurve_norm_seg1 r hr α t ⟨ht.1, ht.2.trans hδ1.le⟩]
      calc t * r ≤ δ * r := by nlinarith [ht.2]
        _ = ε := div_mul_cancel₀ ε hr.ne']
    exact intervalIntegral.integral_zero
  have hI5 : ∫ t in (3 - δ)..(3 : ℝ), F t = 0 := by
    rw [show ∫ t in (3 - δ)..(3 : ℝ), F t = ∫ t in (3 - δ)..(3 : ℝ), (0 : ℂ) from by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith : 3 - δ ≤ 3)] at ht
      dsimp only [F]
      simp only [sub_zero]
      rw [if_neg (not_lt.mpr ?_)]
      rw [sectorCurve_norm_seg3' r hr α t ⟨by linarith [ht.1], ht.2⟩]
      calc (3 - t) * r ≤ δ * r := by nlinarith [ht.1]
        _ = ε := div_mul_cancel₀ ε hr.ne']
    exact intervalIntegral.integral_zero
  have hI2 := pv_cutoff_integral_seg1_eq_inv r hr α ε hε hεr
  have hI3 := pv_cutoff_integral_seg2_eq_Ialpha r hr α ε hε hεr
  have hI4 := pv_cutoff_integral_seg3_eq_neg_inv r hr α ε hε hεr
  have h_split : ∫ t in (0 : ℝ)..3, F t =
      (∫ t in (0 : ℝ)..δ, F t) + (∫ t in δ..(1 : ℝ), F t) + (∫ t in (1 : ℝ)..2, F t) +
      (∫ t in (2 : ℝ)..(3 - δ), F t) + (∫ t in (3 - δ)..(3 : ℝ), F t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hFint_0_3δ hFint_3δ3,
        ← intervalIntegral.integral_add_adjacent_intervals hFint_02 hFint_2_3δ,
        ← intervalIntegral.integral_add_adjacent_intervals hFint_01 hFint_12,
        ← intervalIntegral.integral_add_adjacent_intervals hFint_0δ hFint_δ1]
  rw [h_split, hI1, hI2, hI3, hI4, hI5, zero_add, add_zero]
  linear_combination log_cancellation r hr ε hε hεr

/-- **Lemma 3.1 (dz/z part)**: The principal value of `dz/z` along the sector curve
from 0 to 3 equals `I * alpha`.

The divergences from the radial segments cancel, leaving only the arc contribution. -/
theorem pv_sector_dz_over_z (r : ℝ) (hr : 0 < r) (α : ℝ)
    (_hα_nonneg : 0 ≤ α) (_hα_le : α ≤ 2 * Real.pi) :
    CauchyPrincipalValueExists' (fun z => z⁻¹) (sectorCurve r α) 0 3 0 ∧
    cauchyPrincipalValue' (fun z => z⁻¹) (sectorCurve r α) 0 3 0 = I * ↑α := by
  have h_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫ t in (0 : ℝ)..3,
        (if ‖sectorCurve r α t - 0‖ > ε
          then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t
          else 0) = I * ↑α := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hr] with ε hε hε_pos
    simp only [mem_Ioi] at hε_pos
    exact pv_sector_cutoff_eq r hr α ε hε_pos (mem_Iio.mp hε)
  have h_tendsto : Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..3,
        if ‖sectorCurve r α t - 0‖ > ε
          then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t
          else 0)
      (𝓝[>] 0) (𝓝 (I * ↑α)) :=
    tendsto_const_nhds.congr' (h_ev.mono (fun ε h => h.symm))
  refine ⟨⟨I * ↑α, h_tendsto⟩, ?_⟩
  unfold cauchyPrincipalValue'
  exact h_tendsto.limUnder_eq

end
