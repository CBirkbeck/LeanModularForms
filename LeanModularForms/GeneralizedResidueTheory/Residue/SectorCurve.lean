/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Basic
import LeanModularForms.GeneralizedResidueTheory.Residue
import LeanModularForms.GeneralizedResidueTheory.PrincipalValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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
* `pv_sector_higher_power` -- for n >= 1, `PV int z^{n-1} dz = 0` (angle condition)
* `lemma_3_1_simple_pole` -- Lemma 3.1 for simple poles: PV = `I * alpha * residue`

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

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Definition of the sector curve -/

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

/-! ### Basic properties of the sector curve -/

/-- The sector curve at t=0 is 0. -/
theorem sectorCurve_zero (r : ℝ) (α : ℝ) :
    sectorCurve r α 0 = 0 := by
  simp [sectorCurve]

/-- The sector curve at t=3 is 0. -/
theorem sectorCurve_three (r : ℝ) (α : ℝ) :
    sectorCurve r α 3 = 0 := by
  simp only [sectorCurve, show ¬(3 : ℝ) ≤ 1 from by norm_num,
    show ¬(3 : ℝ) ≤ 2 from by norm_num, ↓reduceIte, sub_self, zero_mul,
    Complex.ofReal_zero, zero_mul]

/-- The sector curve is a closed curve (starts and ends at 0). -/
theorem sectorCurve_closed (r : ℝ) (α : ℝ) :
    sectorCurve r α 0 = sectorCurve r α 3 := by
  rw [sectorCurve_zero, sectorCurve_three]

/-- The sector curve at t=1 is r (the transition from radial to arc). -/
theorem sectorCurve_one (r : ℝ) (α : ℝ) :
    sectorCurve r α 1 = ↑r := by
  simp [sectorCurve]

/-- The sector curve at t=2 is r * exp(i * alpha) (end of arc). -/
theorem sectorCurve_two (r : ℝ) (α : ℝ) :
    sectorCurve r α 2 = ↑r * exp (I * ↑α) := by
  simp only [sectorCurve, show ¬(2 : ℝ) ≤ 1 from by norm_num,
    show (2 : ℝ) ≤ 2 from le_refl 2, ↓reduceIte]
  congr 1; congr 1; push_cast; ring

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
  · -- t = 2: second branch applies (2 ≤ 2), result matches by computation
    simp only [sectorCurve, show ¬(2 : ℝ) ≤ 1 from by norm_num,
      show (2 : ℝ) ≤ 2 from le_refl 2, ↓reduceIte]
    push_cast; ring
  · simp only [sectorCurve, if_neg (not_le.mpr (lt_trans one_lt_two h2)),
      if_neg (not_le.mpr h2)]

/-- The sector curve is continuous on [0,3]. -/
theorem sectorCurve_continuousOn (r : ℝ) (α : ℝ) :
    ContinuousOn (sectorCurve r α) (Icc 0 3) := by
  -- Decompose [0,3] = [0,1] ∪ [1,2] ∪ [2,3]
  have h_union : Icc (0 : ℝ) 3 = Icc 0 1 ∪ Icc 1 2 ∪ Icc 2 3 := by
    ext x; simp only [mem_Icc, mem_union]; constructor
    · intro ⟨h0, h3⟩
      by_cases h1 : x ≤ 1
      · left; left; exact ⟨h0, h1⟩
      · push_neg at h1
        by_cases h2 : x ≤ 2
        · left; right; exact ⟨le_of_lt h1, h2⟩
        · push_neg at h2; right; exact ⟨le_of_lt h2, h3⟩
    · rintro ((⟨h0, h1⟩ | ⟨h1, h2⟩) | ⟨h2, h3⟩)
      · exact ⟨h0, le_trans h1 (by norm_num)⟩
      · exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩
      · exact ⟨le_trans (by norm_num) h2, h3⟩
  rw [h_union]
  -- Continuity on [0,1]: sectorCurve r α t = ↑(t * r)
  have hc1 : ContinuousOn (sectorCurve r α) (Icc 0 1) := by
    apply ContinuousOn.congr _ (fun t ht => sectorCurve_seg1 r α t ht)
    exact (continuous_ofReal.comp (continuous_id.mul continuous_const)).continuousOn
  -- Continuity on [1,2]: sectorCurve r α t = ↑r * exp(I * ↑((t-1) * α))
  have hc2 : ContinuousOn (sectorCurve r α) (Icc 1 2) := by
    apply ContinuousOn.congr _ (fun t ht => sectorCurve_seg2 r α t ht)
    apply ContinuousOn.mul continuousOn_const
    exact (Complex.continuous_exp.comp
      (continuous_const.mul (continuous_ofReal.comp
        ((continuous_id.sub continuous_const).mul continuous_const)))).continuousOn
  -- Continuity on [2,3]: sectorCurve r α t = ↑((3-t) * r) * exp(I * ↑α)
  have hc3 : ContinuousOn (sectorCurve r α) (Icc 2 3) := by
    apply ContinuousOn.congr _ (fun t ht => sectorCurve_seg3 r α t ht)
    apply ContinuousOn.mul _ continuousOn_const
    exact (continuous_ofReal.comp
      ((continuous_const.sub continuous_id).mul continuous_const)).continuousOn
  -- Combine using union_of_isClosed
  exact ((hc1.union_of_isClosed hc2 isClosed_Icc isClosed_Icc).union_of_isClosed hc3
    (isClosed_Icc.union isClosed_Icc) isClosed_Icc)

/-- The sector curve passes through the origin at t=0 and t=3. -/
theorem sectorCurve_passes_through_origin (r : ℝ) (α : ℝ) :
    sectorCurve r α 0 = 0 ∧ sectorCurve r α 3 = 0 :=
  ⟨sectorCurve_zero r α, sectorCurve_three r α⟩

/-- On the arc segment (t in [1,2]), the sector curve has modulus r. -/
theorem sectorCurve_norm_on_arc (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ)
    (ht : t ∈ Icc 1 2) :
    ‖sectorCurve r α t‖ = r := by
  rw [sectorCurve_seg2 r α t ht]
  simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  exact Complex.norm_of_nonneg (le_of_lt hr)

/-- On segment 1 (t in [0,1]), the sector curve has modulus |t * r|. -/
theorem sectorCurve_norm_on_seg1 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    ‖sectorCurve r α t‖ = |t * r| := by
  rw [sectorCurve_seg1 r α t ht]
  exact Complex.norm_real _

/-- On segment 3 (t in [2,3]), the sector curve has modulus (3-t)*r. -/
theorem sectorCurve_norm_on_seg3 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ)
    (ht : t ∈ Icc 2 3) :
    ‖sectorCurve r α t‖ = (3 - t) * r := by
  rw [sectorCurve_seg3 r α t ht]
  simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  exact Complex.norm_of_nonneg (mul_nonneg (by linarith [ht.2]) (le_of_lt hr))

/-! ### Derivative of the sector curve -/

/-- Derivative on segment 1 (t in (0,1)): `deriv (sectorCurve r alpha) t = r`. -/
theorem deriv_sectorCurve_seg1 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    deriv (sectorCurve r α) t = ↑r := by
  have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => ↑(s * r) := by
    have h_nhds : Iio 1 ∈ 𝓝 t := Iio_mem_nhds ht.2
    filter_upwards [h_nhds] with s hs
    simp only [sectorCurve, if_pos (le_of_lt (mem_Iio.mp hs))]
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have : HasDerivAt (fun s => (↑(s * r) : ℂ)) (↑r) t := by
    have h1 : HasDerivAt (fun s => s * r) r t := by
      have := (hasDerivAt_id t).mul_const r
      simpa using this
    exact h1.ofReal_comp
  exact this.deriv

/-- Derivative on segment 2 (t in (1,2)):
  `deriv (sectorCurve r alpha) t = r * (I * alpha) * exp(I * (t-1) * alpha)`. -/
theorem deriv_sectorCurve_seg2 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 1 2) :
    deriv (sectorCurve r α) t =
      ↑r * (I * ↑α) * exp (I * ↑((t - 1) * α)) := by
  have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => ↑r * exp (I * ↑((s - 1) * α)) := by
    have h_nhds : Ioo 1 2 ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    filter_upwards [h_nhds] with s hs
    rw [sectorCurve_seg2 r α s ⟨le_of_lt hs.1, le_of_lt hs.2⟩]
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have h_inner : HasDerivAt (fun s => (↑((s - 1) * α) : ℂ)) (↑α) t := by
    have h1 : HasDerivAt (fun s => (s - 1) * α) α t := by
      have := ((hasDerivAt_id t).sub_const 1).mul_const α
      simpa using this
    exact h1.ofReal_comp
  have h_exp : HasDerivAt (fun s => exp (I * ↑((s - 1) * α)))
      (I * ↑α * exp (I * ↑((t - 1) * α))) t := by
    have := (hasDerivAt_exp (I * ↑((t - 1) * α))).comp t
      ((hasDerivAt_const t I).mul h_inner)
    convert this using 1
    ring
  have h_full : HasDerivAt (fun s => ↑r * exp (I * ↑((s - 1) * α)))
      (↑r * (I * ↑α * exp (I * ↑((t - 1) * α)))) t := by
    have := (hasDerivAt_const t (↑r : ℂ)).mul h_exp
    convert this using 1; ring
  rw [h_full.deriv]; ring

/-- Derivative on segment 3 (t in (2,3)):
  `deriv (sectorCurve r alpha) t = -r * exp(I * alpha)`. -/
theorem deriv_sectorCurve_seg3 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 2 3) :
    deriv (sectorCurve r α) t = -(↑r) * exp (I * ↑α) := by
  have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => ↑((3 - s) * r) * exp (I * ↑α) := by
    have h_nhds : Ioi 2 ∈ 𝓝 t := Ioi_mem_nhds ht.1
    filter_upwards [h_nhds] with s hs
    simp only [sectorCurve,
      if_neg (not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 2) (mem_Ioi.mp hs))),
      if_neg (not_le.mpr (mem_Ioi.mp hs))]
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have h_inner : HasDerivAt (fun s => (↑((3 - s) * r) : ℂ)) (↑(-r)) t := by
    have h1 : HasDerivAt (fun s => (3 - s) * r) (-r) t := by
      have := ((hasDerivAt_const t 3).sub (hasDerivAt_id t)).mul_const r
      convert this using 1; ring
    exact h1.ofReal_comp
  have h_full : HasDerivAt (fun s => ↑((3 - s) * r) * exp (I * ↑α))
      (↑(-r) * exp (I * ↑α)) t :=
    h_inner.mul_const _
  rw [h_full.deriv]; push_cast; ring

/-! ### PV integrand analysis -/

/-- The integrand `(sectorCurve r alpha t)^(-1) * deriv (sectorCurve r alpha) t`
on segment 1 (t in (0,1)) simplifies to `1/t` (as a complex number). -/
theorem pv_integrand_seg1 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = ↑(t⁻¹) := by
  rw [sectorCurve_seg1 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg1 r α t ht]
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht.1)
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  push_cast; field_simp

/-- The integrand on segment 2 (t in (1,2)) simplifies to `I * alpha`. -/
theorem pv_integrand_seg2 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 1 2) :
    (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = I * ↑α := by
  rw [sectorCurve_seg2 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg2 r α t ht]
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have h_exp_ne : exp (I * ↑((t - 1) * α)) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- The integrand on segment 3 (t in (2,3)) simplifies to `-1/(3-t)`. -/
theorem pv_integrand_seg3 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 2 3) :
    (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = -↑((3 - t)⁻¹) := by
  rw [sectorCurve_seg3 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg3 r α t ht]
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have h_exp_ne : exp (I * ↑α) ≠ 0 := Complex.exp_ne_zero _
  have h3t_ne : (3 - t : ℝ) ≠ 0 := by linarith [ht.2]
  have h3t_ne' : (↑(3 - t) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h3t_ne
  push_cast; field_simp

/-! ### PV computation: Lemma 3.1 -/

/-- The integral of `1/t` from `epsilon` to `1` is `-log(epsilon)`. -/
theorem integral_seg1_eq_neg_log (ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) :
    ∫ t in ε..1, (t : ℝ)⁻¹ = -Real.log ε := by
  rw [integral_inv_of_pos hε one_pos,
    Real.log_div one_ne_zero (ne_of_gt hε), Real.log_one, zero_sub]

/-- The integral of `-1/(3-t)` from `2` to `3-epsilon` is `log(epsilon)`. -/
theorem integral_seg3_eq_log (ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) :
    ∫ t in (2 : ℝ)..(3 - ε), -((3 - t)⁻¹) = Real.log ε := by
  rw [intervalIntegral.integral_neg]
  -- Substitute u = 3 - t: ∫ t in 2..(3-ε), (3-t)⁻¹ = ∫ u in ε..1, u⁻¹
  have h1 : ∫ t in (2 : ℝ)..(3 - ε), (3 - t)⁻¹ = ∫ u in ε..1, u⁻¹ := by
    have := intervalIntegral.integral_comp_sub_left (fun u => u⁻¹) (3 : ℝ)
      (a := (2 : ℝ)) (b := 3 - ε)
    simp only at this
    rw [this]
    congr 1 <;> ring
  rw [h1, integral_inv_of_pos hε one_pos,
    Real.log_div one_ne_zero (ne_of_gt hε), Real.log_one, zero_sub, neg_neg]

/-- On segment 1, the norm of the sector curve is `t * r`. -/
theorem sectorCurve_norm_seg1 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    ‖sectorCurve r α t‖ = t * r := by
  rw [sectorCurve_seg1 r α t ht]
  exact Complex.norm_of_nonneg (mul_nonneg ht.1 (le_of_lt hr))

/-- On segment 3, the norm of the sector curve is `(3 - t) * r`. -/
theorem sectorCurve_norm_seg3' (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 2 3) :
    ‖sectorCurve r α t‖ = (3 - t) * r := by
  rw [sectorCurve_seg3 r α t ht, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
    Complex.norm_of_nonneg (mul_nonneg (by linarith [ht.2]) (le_of_lt hr))]

/-- The logarithmic integrals from segments 1 and 3 cancel. -/
theorem log_cancellation (r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    (∫ t in (ε / r)..(1 : ℝ), (↑(t⁻¹) : ℂ)) +
    (∫ t in (2 : ℝ)..(3 - ε / r), (-(↑((3 - t)⁻¹)) : ℂ)) = 0 := by
  have hεr_pos : 0 < ε / r := div_pos hε hr
  have hεr_lt1 : ε / r < 1 := by rwa [div_lt_one hr]
  -- ∫ ε/r..1 t⁻¹ dt = -log(ε/r)
  have h1 : ∫ t in (ε / r)..(1 : ℝ), (t⁻¹ : ℝ) = -(Real.log (ε / r)) := by
    rw [integral_inv_of_pos hεr_pos one_pos, Real.log_div one_ne_zero (ne_of_gt hεr_pos),
      Real.log_one, zero_sub]
  -- ∫ 2..3-ε/r -(3-t)⁻¹ dt = log(ε/r)
  have h2 : ∫ t in (2 : ℝ)..(3 - ε / r), -((3 - t)⁻¹ : ℝ) = Real.log (ε / r) := by
    rw [intervalIntegral.integral_neg]
    have h_sub : ∫ t in (2 : ℝ)..(3 - ε / r), (3 - t)⁻¹ = ∫ u in (ε / r)..1, u⁻¹ := by
      have := intervalIntegral.integral_comp_sub_left (fun u => u⁻¹) (3 : ℝ)
        (a := (2 : ℝ)) (b := 3 - ε / r)
      simp only at this; rw [this]; congr 1 <;> ring
    rw [h_sub, integral_inv_of_pos hεr_pos one_pos, Real.log_div one_ne_zero
      (ne_of_gt hεr_pos), Real.log_one, zero_sub, neg_neg]
  -- Convert to complex and add
  have h1c : ∫ t in (ε / r)..(1 : ℝ), (↑(t⁻¹) : ℂ) = ↑(-(Real.log (ε / r))) := by
    rw [← h1, intervalIntegral.integral_ofReal]
  have h2c : ∫ t in (2 : ℝ)..(3 - ε / r), (-(↑((3 - t)⁻¹)) : ℂ) =
      ↑(Real.log (ε / r)) := by
    have : ∀ t : ℝ, (-(↑((3 - t)⁻¹) : ℂ)) = (↑((-((3 - t)⁻¹)) : ℝ)) := by
      intro t; push_cast; ring
    simp_rw [this, intervalIntegral.integral_ofReal, h2]
  rw [h1c, h2c, ← Complex.ofReal_add, neg_add_cancel, Complex.ofReal_zero]

set_option maxHeartbeats 1600000 in
/-- For `0 < ε < r`, the PV cutoff integral of `dz/z` along the sector curve equals `I * α`.
This is the key cancellation lemma: the logarithmic divergences from segments 1 and 3 cancel. -/
theorem pv_sector_cutoff_eq (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    ∫ t in (0 : ℝ)..3,
      (if ‖sectorCurve r α t - 0‖ > ε then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t
       else 0) = I * ↑α := by
  set F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
      then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
  -- Key bounds
  set δ := ε / r with hδ_def
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  have h3δ : 2 < 3 - δ := by linarith
  -- Norm characterizations that determine the cutoff behavior
  -- seg1: ‖sectorCurve‖ = t*r, so ‖·‖ > ε ↔ t > δ
  -- seg2: ‖sectorCurve‖ = r > ε, always above cutoff
  -- seg3: ‖sectorCurve‖ = (3-t)*r, so ‖·‖ > ε ↔ t < 3-δ
  -- Split [0,3] = [0, δ] ∪ [δ, 1] ∪ [1, 2] ∪ [2, 3-δ] ∪ [3-δ, 3]
  -- and compute each integral
  -- I1: ∫ [0, δ] F = 0 (below cutoff)
  have hI1 : ∫ t in (0 : ℝ)..δ, F t = 0 := by
    have : ∫ t in (0 : ℝ)..δ, F t = ∫ t in (0 : ℝ)..δ, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (le_of_lt hδ)] at ht
      dsimp only [F]; simp only [sub_zero]
      rw [if_neg (not_lt.mpr _)]
      rw [sectorCurve_norm_seg1 r hr α t ⟨ht.1, le_trans ht.2 (le_of_lt hδ1)⟩]
      calc t * r ≤ δ * r := by nlinarith [ht.2]
        _ = ε := by rw [hδ_def]; field_simp
    rw [this, intervalIntegral.integral_zero]
  -- I5: ∫ [3-δ, 3] F = 0 (below cutoff)
  have hI5 : ∫ t in (3 - δ)..(3 : ℝ), F t = 0 := by
    have : ∫ t in (3 - δ)..(3 : ℝ), F t = ∫ t in (3 - δ)..(3 : ℝ), (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith : 3 - δ ≤ 3)] at ht
      dsimp only [F]; simp only [sub_zero]
      rw [if_neg (not_lt.mpr _)]
      have h2 : 2 ≤ t := by linarith [ht.1]
      rw [sectorCurve_norm_seg3' r hr α t ⟨h2, ht.2⟩]
      calc (3 - t) * r ≤ δ * r := by nlinarith [ht.1]
        _ = ε := by rw [hδ_def]; field_simp
    rw [this, intervalIntegral.integral_zero]
  -- I3: ∫ [1, 2] F = I * α (arc contribution)
  have hI3 : ∫ t in (1 : ℝ)..2, F t = I * ↑α := by
    -- The equality holds on Ioo 1 2 (open interval); endpoints are measure zero
    have h_on_Ioo : ∀ t ∈ Ioo 1 2, F t = I * ↑α := by
      intro t ⟨ht1, ht2⟩
      dsimp only [F]; simp only [sub_zero]
      rw [if_pos]
      · rw [sectorCurve_seg2 r α t ⟨le_of_lt ht1, le_of_lt ht2⟩,
            deriv_sectorCurve_seg2 r α t ⟨ht1, ht2⟩]
        have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
        have : exp (I * ↑((t - 1) * α)) ≠ 0 := Complex.exp_ne_zero _
        field_simp
      · rw [sectorCurve_seg2 r α t ⟨le_of_lt ht1, le_of_lt ht2⟩]
        simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
        rw [Complex.norm_of_nonneg (le_of_lt hr)]; linarith
    have h_ae : ∀ᵐ t, t ∈ Ι 1 2 → F t = I * ↑α := by
      have : Ioo (1 : ℝ) 2 =ᵐ[volume] Ioc 1 2 := Ioo_ae_eq_Ioc
      rw [Filter.eventuallyEq_set] at this
      filter_upwards [this] with t ht
      rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      intro ht_mem
      exact h_on_Ioo t (ht.mpr ht_mem)
    rw [intervalIntegral.integral_congr_ae h_ae, intervalIntegral.integral_const]
    norm_num
  -- I2: ∫ [δ, 1] F = ∫ [δ, 1] ↑(t⁻¹) (radial outgoing)
  have hI2 : ∫ t in δ..(1 : ℝ), F t = ∫ t in δ..(1 : ℝ), (↑(t⁻¹) : ℂ) := by
    -- The equality holds on Ioo δ 1; endpoint t=1 is measure zero
    have h_on_Ioo : ∀ t ∈ Ioo δ 1, F t = (↑(t⁻¹) : ℂ) := by
      intro t ⟨htδ, ht1⟩
      dsimp only [F]; simp only [sub_zero]
      rw [if_pos]
      · rw [sectorCurve_seg1 r α t ⟨le_of_lt (lt_trans hδ htδ), le_of_lt ht1⟩,
            deriv_sectorCurve_seg1 r α t ⟨lt_trans hδ htδ, ht1⟩]
        have ht_ne : (t : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans hδ htδ))
        have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
        push_cast; field_simp
      · rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt (lt_trans hδ htδ), le_of_lt ht1⟩]
        calc ε = δ * r := by rw [hδ_def]; field_simp
          _ < t * r := by nlinarith
    apply intervalIntegral.integral_congr_ae
    have : Ioo δ 1 =ᵐ[volume] Ioc δ 1 := Ioo_ae_eq_Ioc
    rw [Filter.eventuallyEq_set] at this
    filter_upwards [this] with t ht
    rw [Set.uIoc_of_le (le_of_lt hδ1)]
    intro ht_mem
    exact h_on_Ioo t (ht.mpr ht_mem)
  -- I4: ∫ [2, 3-δ] F = ∫ [2, 3-δ] -(↑((3-t)⁻¹)) (radial returning)
  have hI4 : ∫ t in (2 : ℝ)..(3 - δ), F t =
      ∫ t in (2 : ℝ)..(3 - δ), -(↑((3 - t)⁻¹) : ℂ) := by
    -- The equality holds on Ioo 2 (3-δ); endpoint t=3-δ is measure zero
    have h_on_Ioo : ∀ t ∈ Ioo 2 (3 - δ), F t = -(↑((3 - t)⁻¹) : ℂ) := by
      intro t ⟨ht2, ht3δ⟩
      dsimp only [F]; simp only [sub_zero]
      rw [if_pos]
      · have h3 : t < 3 := by linarith
        rw [sectorCurve_seg3 r α t ⟨le_of_lt ht2, le_of_lt h3⟩,
            deriv_sectorCurve_seg3 r α t ⟨ht2, h3⟩]
        have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
        have : exp (I * ↑α) ≠ 0 := Complex.exp_ne_zero _
        have : (3 - t : ℝ) ≠ 0 := by linarith
        push_cast; field_simp
      · have h3 : t < 3 := by linarith
        rw [sectorCurve_norm_seg3' r hr α t ⟨le_of_lt ht2, le_of_lt h3⟩]
        calc ε = δ * r := by rw [hδ_def]; field_simp
          _ < (3 - t) * r := by nlinarith
    apply intervalIntegral.integral_congr_ae
    have : Ioo 2 (3 - δ) =ᵐ[volume] Ioc 2 (3 - δ) := Ioo_ae_eq_Ioc
    rw [Filter.eventuallyEq_set] at this
    filter_upwards [this] with t ht
    rw [Set.uIoc_of_le (le_of_lt h3δ)]
    intro ht_mem
    exact h_on_Ioo t (ht.mpr ht_mem)
  -- F equals a continuous function on each sub-interval, hence integrable
  have hFint_0δ : IntervalIntegrable F volume 0 δ := by
    apply (intervalIntegrable_const (c := (0 : ℂ))).congr
    intro t ht; rw [Set.uIoc_of_le hδ.le] at ht
    dsimp only [F]; simp only [sub_zero]; rw [if_neg (not_lt.mpr _)]
    rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt ht.1, le_trans ht.2 (le_of_lt hδ1)⟩]
    exact le_trans (mul_le_mul_of_nonneg_right ht.2 hr.le)
      (le_of_eq (by rw [hδ_def]; field_simp))
  have hFint_3δ3 : IntervalIntegrable F volume (3 - δ) 3 := by
    apply (intervalIntegrable_const (c := (0 : ℂ))).congr
    intro t ht; rw [Set.uIoc_of_le (by linarith : 3 - δ ≤ 3)] at ht
    dsimp only [F]; simp only [sub_zero]; rw [if_neg (not_lt.mpr _)]
    have h2 : 2 ≤ t := by linarith [ht.1]
    rw [sectorCurve_norm_seg3' r hr α t ⟨h2, ht.2⟩]
    have : (3 - t) * r ≤ δ * r := mul_le_mul_of_nonneg_right (by linarith [ht.1]) hr.le
    linarith [show δ * r = ε from by rw [hδ_def]; field_simp]
  have hFint_δ1 : IntervalIntegrable F volume δ 1 := by
    -- F = ↑(t⁻¹) on Ioo δ 1, and t ↦ ↑(t⁻¹) is continuous on [δ, 1] since δ > 0
    have hcont : ContinuousOn (fun t : ℝ => (↑(t⁻¹) : ℂ)) (Set.uIcc δ 1) := by
      intro t ht; rw [Set.uIcc_of_le hδ1.le] at ht
      have ht_pos : 0 < t := lt_of_lt_of_le hδ ht.1
      exact (Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_inv₀ (ne_of_gt ht_pos))).continuousWithinAt
    rw [intervalIntegrable_iff, Set.uIoc_of_le hδ1.le]
    -- F = ↑(t⁻¹) on Ioo δ 1 (at t=1, the sector curve derivative is undefined)
    have h_eq : ∀ t ∈ Ioo δ (1 : ℝ), F t = (↑(t⁻¹) : ℂ) := fun t ⟨htδ, ht1⟩ => by
      dsimp only [F]; simp only [sub_zero]; rw [if_pos]
      · exact pv_integrand_seg1 r hr α t ⟨lt_trans hδ htδ, ht1⟩
      · rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt (lt_trans hδ htδ), le_of_lt ht1⟩]
        calc ε = δ * r := by rw [hδ_def]; field_simp
          _ < t * r := by nlinarith
    -- ↑(t⁻¹) is integrable on Ioo δ 1 (restriction of continuous function on [δ,1])
    have h_g_Ioo : IntegrableOn (fun t : ℝ => (↑(t⁻¹) : ℂ)) (Ioo δ 1) volume :=
      (intervalIntegrable_iff.mp hcont.intervalIntegrable).mono_set
        (by rw [Set.uIoc_of_le hδ1.le]; exact Ioo_subset_Ioc_self)
    -- F is integrable on Ioo δ 1 (a.e. equal to ↑(t⁻¹))
    have h_F_Ioo : IntegrableOn F (Ioo δ 1) volume :=
      Integrable.congr h_g_Ioo
        ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm)
    -- Ioo and Ioc differ by a null set {1}, so IntegrableOn transfers
    rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]; exact h_F_Ioo
  have hFint_12 : IntervalIntegrable F volume 1 2 := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    -- F = I*α on Ioo 1 2 (the derivative only exists on the open interval)
    have h_eq : ∀ t ∈ Ioo (1 : ℝ) 2, F t = I * ↑α := by
      intro t ⟨ht1, ht2⟩
      dsimp only [F]; simp only [sub_zero]; rw [if_pos]
      · rw [sectorCurve_seg2 r α t ⟨le_of_lt ht1, le_of_lt ht2⟩,
            deriv_sectorCurve_seg2 r α t ⟨ht1, ht2⟩]
        have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
        have : exp (I * ↑((t - 1) * α)) ≠ 0 := Complex.exp_ne_zero _
        field_simp
      · rw [sectorCurve_seg2 r α t ⟨le_of_lt ht1, le_of_lt ht2⟩]
        simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
        rw [Complex.norm_of_nonneg (le_of_lt hr)]; linarith
    -- The constant I*α is integrable on Ioo 1 2 (restrict from IntervalIntegrable on [1,2])
    have h_const_Ioo : IntegrableOn (fun (_ : ℝ) => I * (↑α : ℂ)) (Ioo (1 : ℝ) 2) volume :=
      (intervalIntegrable_iff.mp (intervalIntegrable_const :
        IntervalIntegrable (fun _ => I * (↑α : ℂ)) volume 1 2)).mono_set
        (by rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]; exact Ioo_subset_Ioc_self)
    -- F is integrable on Ioo 1 2 (a.e. equal to the constant I*α)
    have h_F_Ioo : IntegrableOn F (Ioo (1 : ℝ) 2) volume :=
      Integrable.congr h_const_Ioo
        ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm)
    -- Ioo and Ioc differ by the null set {2}, so IntegrableOn transfers
    rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]; exact h_F_Ioo
  have hFint_2_3δ : IntervalIntegrable F volume 2 (3 - δ) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le h3δ.le]
    -- F = -(↑((3-t)⁻¹)) on Ioo 2 (3-δ) (derivative only on open interval)
    have h_eq : ∀ t ∈ Ioo (2 : ℝ) (3 - δ), F t = -(↑((3 - t)⁻¹) : ℂ) := by
      intro t ⟨ht2, ht3δ⟩
      dsimp only [F]; simp only [sub_zero]; rw [if_pos]
      · have h3 : t < 3 := by linarith
        rw [sectorCurve_seg3 r α t ⟨le_of_lt ht2, le_of_lt h3⟩,
            deriv_sectorCurve_seg3 r α t ⟨ht2, h3⟩]
        have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
        have : exp (I * ↑α) ≠ 0 := Complex.exp_ne_zero _
        have : (3 - t : ℝ) ≠ 0 := by linarith
        push_cast; field_simp
      · have h3 : t < 3 := by linarith
        rw [sectorCurve_norm_seg3' r hr α t ⟨le_of_lt ht2, le_of_lt h3⟩]
        calc ε = δ * r := by rw [hδ_def]; field_simp
          _ < (3 - t) * r := by nlinarith
    -- The comparison function t ↦ -(↑((3-t)⁻¹)) is continuous on [2, 3-δ] since 3-t ≥ δ > 0
    have hcont : ContinuousOn (fun t : ℝ => -(↑((3 - t)⁻¹) : ℂ)) (Set.uIcc 2 (3 - δ)) := by
      rw [Set.uIcc_of_le h3δ.le]
      intro t ht
      apply ContinuousAt.continuousWithinAt
      exact continuous_neg.continuousAt.comp
        (Complex.continuous_ofReal.continuousAt.comp
          ((continuousAt_inv₀ (ne_of_gt (show (0 : ℝ) < 3 - t by linarith [ht.2]))).comp
           (continuousAt_const.sub continuousAt_id)))
    -- Get integrability on Ioo via monotonicity from the IntervalIntegrable on uIoc
    have h_g_Ioo : IntegrableOn (fun t : ℝ => -(↑((3 - t)⁻¹) : ℂ))
        (Ioo (2 : ℝ) (3 - δ)) volume :=
      (intervalIntegrable_iff.mp hcont.intervalIntegrable).mono_set
        (by rw [Set.uIoc_of_le h3δ.le]; exact Ioo_subset_Ioc_self)
    -- F is integrable on Ioo 2 (3-δ) (a.e. equal to the comparison function)
    have h_F_Ioo : IntegrableOn F (Ioo (2 : ℝ) (3 - δ)) volume :=
      Integrable.congr h_g_Ioo
        ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm)
    -- Ioo and Ioc differ by a null set, so IntegrableOn transfers
    rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]; exact h_F_Ioo
  -- Combine integrabilities for adjacent intervals
  have hFint_01 : IntervalIntegrable F volume 0 1 := by
    rw [intervalIntegrable_iff]
    have h0δ := hFint_0δ.def'; rw [Set.uIoc_of_le hδ.le] at h0δ
    have hδ1' := hFint_δ1.def'; rw [Set.uIoc_of_le hδ1.le] at hδ1'
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply (h0δ.union hδ1').mono_set
    intro t ht
    rcases le_or_gt t δ with h | h
    · left; exact ⟨ht.1, h⟩
    · right; exact ⟨h, ht.2⟩
  have hFint_02 : IntervalIntegrable F volume 0 2 := by
    rw [intervalIntegrable_iff]
    have h01' := hFint_01.def'; rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h01'
    have h12' := hFint_12.def'; rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at h12'
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    apply (h01'.union h12').mono_set
    intro t ht
    rcases le_or_gt t 1 with h | h
    · left; exact ⟨ht.1, h⟩
    · right; exact ⟨h, ht.2⟩
  have hFint_0_3δ : IntervalIntegrable F volume 0 (3 - δ) := by
    rw [intervalIntegrable_iff]
    have h02' := hFint_02.def'; rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at h02'
    have h23' := hFint_2_3δ.def'; rw [Set.uIoc_of_le h3δ.le] at h23'
    rw [Set.uIoc_of_le (by linarith : (0 : ℝ) ≤ 3 - δ)]
    apply (h02'.union h23').mono_set
    intro t ht
    rcases le_or_gt t 2 with h | h
    · left; exact ⟨ht.1, h⟩
    · right; exact ⟨h, ht.2⟩
  -- Split: ∫ [0,3] = ∫ [0,δ] + ∫ [δ,1] + ∫ [1,2] + ∫ [2,3-δ] + ∫ [3-δ,3]
  have h01 := intervalIntegral.integral_add_adjacent_intervals hFint_0δ hFint_δ1
  have h02 := intervalIntegral.integral_add_adjacent_intervals hFint_01 hFint_12
  have h03 := intervalIntegral.integral_add_adjacent_intervals hFint_02 hFint_2_3δ
  have h04 := intervalIntegral.integral_add_adjacent_intervals hFint_0_3δ hFint_3δ3
  have h_split : ∫ t in (0 : ℝ)..3, F t =
      (∫ t in (0 : ℝ)..δ, F t) + (∫ t in δ..(1 : ℝ), F t) + (∫ t in (1 : ℝ)..2, F t) +
      (∫ t in (2 : ℝ)..(3 - δ), F t) + (∫ t in (3 - δ)..(3 : ℝ), F t) := by
    rw [← h04, ← h03, ← h02, ← h01]
  rw [h_split, hI1, hI2, hI3, hI4, hI5, zero_add, add_zero]
  have h_cancel := log_cancellation r hr ε hε hεr
  have : (∫ t in δ..(1 : ℝ), (↑(t⁻¹) : ℂ)) + I * ↑α +
      (∫ t in (2 : ℝ)..(3 - δ), -(↑((3 - t)⁻¹) : ℂ)) =
    ((∫ t in δ..(1 : ℝ), (↑(t⁻¹) : ℂ)) + (∫ t in (2 : ℝ)..(3 - δ), -(↑((3 - t)⁻¹) : ℂ))) +
      I * ↑α := by ring
  rw [this, h_cancel, zero_add]

/-- **Lemma 3.1 (dz/z part)**: The principal value of `dz/z` along the sector curve
from 0 to 3 equals `I * alpha`.

The divergences from the radial segments cancel, leaving only the arc contribution. -/
theorem pv_sector_dz_over_z (r : ℝ) (hr : 0 < r) (α : ℝ)
    (_hα_nonneg : 0 ≤ α) (_hα_le : α ≤ 2 * Real.pi) :
    CauchyPrincipalValueExists' (fun z => z⁻¹) (sectorCurve r α) 0 3 0 ∧
    cauchyPrincipalValue' (fun z => z⁻¹) (sectorCurve r α) 0 3 0 = I * ↑α := by
  -- The PV integral is eventually constant = I * α for ε < r
  have h_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫ t in (0 : ℝ)..3,
        (if ‖sectorCurve r α t - 0‖ > ε then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t
         else 0) = I * ↑α := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hr] with ε hε hε_pos
    simp only [mem_Ioi] at hε_pos
    exact pv_sector_cutoff_eq r hr α ε hε_pos (mem_Iio.mp hε)
  have h_tendsto : Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..3,
        if ‖sectorCurve r α t - 0‖ > ε then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t
        else 0)
      (𝓝[>] 0) (𝓝 (I * ↑α)) :=
    tendsto_const_nhds.congr' (h_ev.mono (fun ε h => h.symm))
  constructor
  · -- The PV exists
    exact ⟨I * ↑α, h_tendsto⟩
  · -- The PV value is I * α
    have : cauchyPrincipalValue' (fun z => z⁻¹) (sectorCurve r α) 0 3 0 = I * ↑α := by
      unfold cauchyPrincipalValue'
      exact h_tendsto.limUnder_eq
    exact this

/-- For `n >= 1`, the integral of `z^(n-1) dz` along the sector curve is 0
when `n * alpha` is a multiple of `2 * pi`. -/
theorem pv_sector_higher_power (r : ℝ) (_hr : 0 < r) (α : ℝ)
    (_hα_nonneg : 0 ≤ α) (_hα_le : α ≤ 2 * Real.pi)
    (n : ℕ) (hn : 1 ≤ n) (_h_angle : ∃ k : ℤ, n * α = k * (2 * Real.pi)) :
    ∫ t in (0 : ℝ)..3,
      (sectorCurve r α t) ^ (n - 1) * deriv (sectorCurve r α) t = 0 := by
  -- By FTC: the integrand is d/dt[γ(t)^n / n], so the integral telescopes to
  -- γ(3)^n/n - γ(0)^n/n = 0. The angle hypothesis is unused.
  have hn_ne : (↑n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Abbreviation for the integrand
  set f : ℝ → ℂ := fun t =>
    (sectorCurve r α t) ^ (n - 1) * deriv (sectorCurve r α) t
  -- Primitive F(t) = γ(t)^n / n
  set F : ℝ → ℂ := fun t => (sectorCurve r α t) ^ n / (↑n : ℂ)
  -- F is continuous on [0, 3]
  have hF_cont : ContinuousOn F (Icc 0 3) :=
    ((sectorCurve_continuousOn r α).pow n).div_const _
  -- Exceptional set {1, 2} is countable
  have hS_count : ({1, 2} ∩ Ioo (0:ℝ) 3 : Set ℝ).Countable :=
    (Set.Finite.inter_of_left (Set.toFinite {1, 2}) _).countable
  -- sectorCurve is differentiable at t for t ∈ (0,3) \ {1, 2}
  have hγ_diff : ∀ t ∈ Ioo (0:ℝ) 3,
      t ∉ ({1, 2} : Set ℝ) → DifferentiableAt ℝ (sectorCurve r α) t := by
    intro t ht ht_not
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_not
    rcases lt_or_gt_of_ne ht_not.1 with h1 | h1
    · -- t < 1: sectorCurve =ᶠ fun s => ↑(s * r)
      have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => (↑(s * r) : ℂ) := by
        filter_upwards [Iio_mem_nhds h1] with s hs
        simp only [sectorCurve, if_pos (le_of_lt (mem_Iio.mp hs))]
      exact h_eq.differentiableAt_iff.mpr
        ((hasDerivAt_id t).mul_const r).ofReal_comp.differentiableAt
    · rcases lt_or_gt_of_ne ht_not.2 with h2 | h2
      · -- 1 < t < 2
        have h_eq : sectorCurve r α =ᶠ[𝓝 t]
            fun s => (↑r : ℂ) * exp (I * ↑((s - 1) * α)) := by
          filter_upwards [isOpen_Ioo.mem_nhds ⟨h1, h2⟩] with s hs
          exact sectorCurve_seg2 r α s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
        refine h_eq.differentiableAt_iff.mpr ?_
        apply DifferentiableAt.const_mul
        apply DifferentiableAt.cexp
        apply DifferentiableAt.const_mul
        exact (((hasDerivAt_id t).sub (hasDerivAt_const t (1 : ℝ))).mul_const α).ofReal_comp.differentiableAt
      · -- t > 2
        have h_eq : sectorCurve r α =ᶠ[𝓝 t]
            fun s => (↑((3 - s) * r) : ℂ) * exp (I * ↑α) := by
          filter_upwards [Ioi_mem_nhds h2] with s hs
          simp only [sectorCurve,
            if_neg (not_le.mpr (lt_trans one_lt_two (mem_Ioi.mp hs))),
            if_neg (not_le.mpr (mem_Ioi.mp hs))]
        refine h_eq.differentiableAt_iff.mpr ?_
        apply DifferentiableAt.mul_const
        exact (((hasDerivAt_const t (3 : ℝ)).sub (hasDerivAt_id t)).mul_const r).ofReal_comp.differentiableAt
  -- HasDerivAt F f on (0,3) \ {1, 2}
  have hF_deriv : ∀ t ∈ Ioo (0:ℝ) 3 \ ({1, 2} ∩ Ioo (0:ℝ) 3),
      HasDerivAt F (f t) t := by
    intro t ⟨ht, ht_not⟩
    have ht_not' : t ∉ ({1, 2} : Set ℝ) := fun h => ht_not ⟨h, ht⟩
    have h_pow := (hγ_diff t ht ht_not').hasDerivAt.pow n
    have h_div := h_pow.div_const (↑n : ℂ)
    show HasDerivAt F (sectorCurve r α t ^ (n - 1) * deriv (sectorCurve r α) t) t
    convert h_div using 1
    rw [mul_assoc, mul_div_cancel_left₀ _ hn_ne]
  -- Integrability: split [0,3] into 3 segments, each a.e. equal to a continuous function
  have hf_int : IntervalIntegrable f volume 0 3 := by
    have h01 : IntervalIntegrable f volume 0 1 := by
      have h_cont_int : IntervalIntegrable
          (fun t => (↑(t * r) : ℂ) ^ (n - 1) * ↑r) volume 0 1 :=
        (show ContinuousOn (fun t => (↑(t * r) : ℂ) ^ (n - 1) * (↑r : ℂ))
          (Set.uIcc 0 1) by rw [Set.uIcc_of_le (by norm_num)]; fun_prop).intervalIntegrable
      exact h_cont_int.congr_ae (by
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),
          ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        show (↑(t * r) : ℂ) ^ (n - 1) * ↑r = f t
        simp only [f, sectorCurve_seg1 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
          deriv_sectorCurve_seg1 r α t ht])
    have h12 : IntervalIntegrable f volume 1 2 := by
      have h_cont_int : IntervalIntegrable
          (fun t => (↑r * exp (I * ↑((t - 1) * α))) ^ (n - 1) *
            (↑r * (I * ↑α) * exp (I * ↑((t - 1) * α)))) volume 1 2 :=
        (show ContinuousOn (fun t => ((↑r : ℂ) * exp (I * ↑((t - 1) * α))) ^ (n - 1) *
            (↑r * (I * ↑α) * exp (I * ↑((t - 1) * α))))
          (Set.uIcc 1 2) by rw [Set.uIcc_of_le (by norm_num)]; fun_prop).intervalIntegrable
      exact h_cont_int.congr_ae (by
        rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 2),
          ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        show _ = f t
        simp only [f, sectorCurve_seg2 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
          deriv_sectorCurve_seg2 r α t ht])
    have h23 : IntervalIntegrable f volume 2 3 := by
      have h_cont_int : IntervalIntegrable
          (fun t => (↑((3 - t) * r) * exp (I * ↑α)) ^ (n - 1) *
            (-(↑r) * exp (I * ↑α))) volume 2 3 :=
        (show ContinuousOn (fun t => ((↑((3 - t) * r) : ℂ) * exp (I * ↑α)) ^ (n - 1) *
            (-(↑r : ℂ) * exp (I * ↑α)))
          (Set.uIcc 2 3) by rw [Set.uIcc_of_le (by norm_num)]; fun_prop).intervalIntegrable
      exact h_cont_int.congr_ae (by
        rw [Set.uIoc_of_le (by norm_num : (2:ℝ) ≤ 3),
          ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        show _ = f t
        simp only [f, sectorCurve_seg3 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
          deriv_sectorCurve_seg3 r α t ht])
    exact h01.trans h12 |>.trans h23
  -- Apply FTC
  have h_ftc := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    F f (by norm_num : (0:ℝ) ≤ 3) hS_count hF_cont hF_deriv hf_int
  rw [h_ftc]
  -- F(3) - F(0) = 0^n/n - 0^n/n = 0
  show F 3 - F 0 = 0
  simp only [F, sectorCurve_zero, sectorCurve_three, zero_pow (by omega : n ≠ 0),
    zero_div, sub_self]

/-- The integral of an analytic function along the sector curve is zero,
because the sector starts and ends at 0, and analytic functions on
a convex open set have primitives. -/
private theorem integral_analytic_sectorCurve_eq_zero (r : ℝ) (hr : 0 < r) (α : ℝ)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    ∫ t in (0 : ℝ)..3, g (sectorCurve r α t) * deriv (sectorCurve r α) t = 0 := by
  -- g is differentiable on ball(0, r+1) which is convex and open
  have hball_convex : Convex ℝ (Metric.ball (0 : ℂ) (↑r + 1)) :=
    convex_ball 0 _
  have hball_open : IsOpen (Metric.ball (0 : ℂ) (↑r + 1)) := Metric.isOpen_ball
  have hball_ne : (Metric.ball (0 : ℂ) (↑r + 1)).Nonempty :=
    ⟨0, Metric.mem_ball_self (by positivity)⟩
  have hg_diff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) (↑r + 1)) :=
    hg.differentiableOn
  -- Get primitive F with HasDerivAt F (g z) z for z in ball
  obtain ⟨F, hF⟩ := holomorphic_convex_primitive hball_convex hball_open hball_ne hg_diff
  -- F ∘ γ is continuous on [0, 3]
  have norm_exp_I : ∀ (x : ℝ), ‖Complex.exp (I * ↑x)‖ = 1 := by
    intro x; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  have hγ_in_ball : ∀ t ∈ Icc (0 : ℝ) 3, sectorCurve r α t ∈ Metric.ball (0 : ℂ) (↑r + 1) := by
    intro t ⟨ht0, ht3⟩
    simp only [Metric.mem_ball, dist_zero_right]
    rcases le_or_gt t 1 with h1 | h1
    · rw [sectorCurve_seg1 r α t ⟨ht0, h1⟩, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 hr.le)]
      nlinarith
    · rcases le_or_gt t 2 with h2 | h2
      · rw [sectorCurve_seg2 r α t ⟨le_of_lt h1, h2⟩, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
          norm_exp_I, mul_one]
        linarith
      · rw [sectorCurve_seg3 r α t ⟨le_of_lt h2, ht3⟩, norm_mul,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (by linarith) hr.le),
          norm_exp_I, mul_one]
        nlinarith
  have hF_contOn : ContinuousOn F (Metric.ball (0 : ℂ) (↑r + 1)) :=
    fun z hz => (hF z hz).continuousAt.continuousWithinAt
  have hF_cont : ContinuousOn (F ∘ sectorCurve r α) (Icc 0 3) :=
    hF_contOn.comp (sectorCurve_continuousOn r α) hγ_in_ball
  -- HasDerivAt (F ∘ γ) (g(γ(t)) * γ'(t)) t for t ∉ {1, 2}
  have hF_deriv : ∀ t ∈ Ioo (0 : ℝ) 3 \ ({1, 2} ∩ Ioo 0 3),
      HasDerivAt (F ∘ sectorCurve r α) (g (sectorCurve r α t) * deriv (sectorCurve r α) t) t := by
    intro t ⟨ht, ht_not⟩
    have ht' : t ∈ Icc 0 3 := Ioo_subset_Icc_self ht
    have ht_not' : t ∉ ({1, 2} : Set ℝ) := fun h => ht_not ⟨h, ht⟩
    have hγ_diff : DifferentiableAt ℝ (sectorCurve r α) t := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_not'
      rcases lt_or_gt_of_ne ht_not'.1 with h1 | h1
      · have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => (↑(s * r) : ℂ) := by
          filter_upwards [Iio_mem_nhds h1] with s hs
          simp only [sectorCurve, if_pos (le_of_lt (mem_Iio.mp hs))]
        exact h_eq.differentiableAt_iff.mpr
          ((hasDerivAt_id t).mul_const r).ofReal_comp.differentiableAt
      · rcases lt_or_gt_of_ne ht_not'.2 with h2 | h2
        · have h_eq : sectorCurve r α =ᶠ[𝓝 t]
              fun s => (↑r : ℂ) * exp (I * ↑((s - 1) * α)) := by
            filter_upwards [isOpen_Ioo.mem_nhds ⟨h1, h2⟩] with s hs
            exact sectorCurve_seg2 r α s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
          refine h_eq.differentiableAt_iff.mpr ?_
          apply DifferentiableAt.const_mul
          apply DifferentiableAt.cexp
          apply DifferentiableAt.const_mul
          exact (((hasDerivAt_id t).sub (hasDerivAt_const t (1 : ℝ))).mul_const α).ofReal_comp.differentiableAt
        · have h_eq : sectorCurve r α =ᶠ[𝓝 t]
              fun s => (↑((3 - s) * r) : ℂ) * exp (I * ↑α) := by
            filter_upwards [Ioi_mem_nhds h2] with s hs
            simp only [sectorCurve,
              if_neg (not_le.mpr (lt_trans one_lt_two (mem_Ioi.mp hs))),
              if_neg (not_le.mpr (mem_Ioi.mp hs))]
          refine h_eq.differentiableAt_iff.mpr ?_
          apply DifferentiableAt.mul_const
          exact (((hasDerivAt_const t (3 : ℝ)).sub (hasDerivAt_id t)).mul_const r).ofReal_comp.differentiableAt
    exact (hF _ (hγ_in_ball t ht')).comp_of_eq t hγ_diff.hasDerivAt rfl
  -- Countable exceptional set
  have hS_count : ({1, 2} ∩ Ioo (0 : ℝ) 3 : Set ℝ).Countable :=
    (Set.Finite.inter_of_left (Set.toFinite {1, 2}) _).countable
  -- Integrability: split into 3 segments, each a.e. equal to a continuous function
  set φ := fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t
  have h_int : IntervalIntegrable φ volume 0 3 := by
    -- Each segment: show an explicit continuous function agrees a.e. with φ
    have h01 : IntervalIntegrable φ volume 0 1 := by
      have hc : ContinuousOn (fun t : ℝ => g ((t * r : ℝ) : ℂ) * (r : ℂ)) (Icc 0 1) := by
        apply ContinuousOn.mul
        · exact hg.continuousOn.comp
            ((continuous_ofReal.comp (continuous_id.mul continuous_const)).continuousOn)
            (fun t ht => by
              have := hγ_in_ball t ⟨ht.1, by linarith [ht.2]⟩
              rwa [sectorCurve_seg1 r α t ht] at this)
        · exact continuousOn_const
      exact (hc.intervalIntegrable_of_Icc (by norm_num)).congr_ae (by
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),
          ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        show _ = φ t
        simp only [φ, sectorCurve_seg1 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
          deriv_sectorCurve_seg1 r α t ht])
    have h12 : IntervalIntegrable φ volume 1 2 := by
      have hc : ContinuousOn (fun t : ℝ => g ((r : ℂ) * exp (I * ((t - 1) * α : ℝ))) *
          ((r : ℂ) * (I * (α : ℂ)) * exp (I * ((t - 1) * α : ℝ)))) (Icc 1 2) := by
        apply ContinuousOn.mul
        · exact hg.continuousOn.comp
            ((continuous_const.mul (continuous_exp.comp
              (continuous_const.mul (continuous_ofReal.comp
                ((continuous_id.sub continuous_const).mul continuous_const))))).continuousOn)
            (fun t ht => by
              have := hγ_in_ball t ⟨by linarith [ht.1], by linarith [ht.2]⟩
              rwa [sectorCurve_seg2 r α t ht] at this)
        · exact (continuous_const.mul (continuous_exp.comp
            (continuous_const.mul (continuous_ofReal.comp
              ((continuous_id.sub continuous_const).mul continuous_const))))).continuousOn
      exact (hc.intervalIntegrable_of_Icc (by norm_num)).congr_ae (by
        rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 2),
          ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        show _ = φ t
        simp only [φ, sectorCurve_seg2 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
          deriv_sectorCurve_seg2 r α t ht])
    have h23 : IntervalIntegrable φ volume 2 3 := by
      have hc : ContinuousOn (fun t : ℝ => g (((3 - t) * r : ℝ) * exp (I * (α : ℂ))) *
          (-(r : ℂ) * exp (I * (α : ℂ)))) (Icc 2 3) := by
        apply ContinuousOn.mul
        · exact hg.continuousOn.comp
            ((continuous_ofReal.comp ((continuous_const.sub continuous_id).mul
              continuous_const)).mul continuous_const).continuousOn
            (fun t ht => by
              have := hγ_in_ball t ⟨by linarith [ht.1], ht.2⟩
              rwa [sectorCurve_seg3 r α t ht] at this)
        · exact continuousOn_const
      exact (hc.intervalIntegrable_of_Icc (by norm_num)).congr_ae (by
        rw [Set.uIoc_of_le (by norm_num : (2:ℝ) ≤ 3),
          ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        show _ = φ t
        simp only [φ, sectorCurve_seg3 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
          deriv_sectorCurve_seg3 r α t ht])
    exact h01.trans h12 |>.trans h23
  -- Apply FTC
  have h_ftc := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (F ∘ sectorCurve r α) _ (by norm_num : (0 : ℝ) ≤ 3)
    hS_count hF_cont hF_deriv h_int
  rw [h_ftc, Function.comp_apply, Function.comp_apply,
    sectorCurve_zero, sectorCurve_three, sub_self]

/-- **Lemma 3.1 (Simple pole version)**:
For `f(z) = c/z + g(z)` where `g` is analytic on a ball containing the sector,
the principal value along the sector curve equals `I * α * c`.

The hypotheses require `g` analytic on a ball strictly containing the sector image
(to guarantee a primitive exists) and `f = c/z + g` at all nonzero points. -/
theorem lemma_3_1_simple_pole (r : ℝ) (hr : 0 < r) (α : ℝ)
    (hα_nonneg : 0 ≤ α) (hα_le : α ≤ 2 * Real.pi)
    (c : ℂ) (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    CauchyPrincipalValueExists' (fun z => c / z + g z) (sectorCurve r α) 0 3 0 ∧
    cauchyPrincipalValue' (fun z => c / z + g z) (sectorCurve r α) 0 3 0 = I * ↑α * c := by
  -- The strategy: decompose PV(c/z + g) into PV(c/z) + ∫g, where ∫g = 0 by FTC.
  -- Step 1: PV of z⁻¹ exists and equals I * α
  have hpv_inv := pv_sector_dz_over_z r hr α hα_nonneg hα_le
  have hpv_inv_exists := hpv_inv.1
  have hpv_inv_val := hpv_inv.2
  -- Step 2: ∫ g(γ(t)) γ'(t) dt = 0 by FTC
  have hg_zero := integral_analytic_sectorCurve_eq_zero r hr α g hg
  -- Get the Tendsto for z⁻¹ PV with the correct limit value
  obtain ⟨L_inv, hL_inv⟩ := hpv_inv_exists
  have hL_inv_eq : L_inv = I * ↑α := by
    have h1 := hL_inv.limUnder_eq
    simp only [cauchyPrincipalValue'] at hpv_inv_val
    exact h1.symm.trans hpv_inv_val
  rw [hL_inv_eq] at hL_inv
  -- Integrability of g∘γ * γ' (needed for DCT)
  have norm_exp_I : ∀ (x : ℝ), ‖Complex.exp (I * ↑x)‖ = 1 := by
    intro x; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  have hγ_in_ball : ∀ t ∈ Icc (0 : ℝ) 3,
      sectorCurve r α t ∈ Metric.ball (0 : ℂ) (↑r + 1) := by
    intro t ⟨ht0, ht3⟩
    simp only [Metric.mem_ball, dist_zero_right]
    rcases le_or_gt t 1 with h1 | h1
    · rw [sectorCurve_seg1 r α t ⟨ht0, h1⟩, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 hr.le)]
      nlinarith
    · rcases le_or_gt t 2 with h2 | h2
      · rw [sectorCurve_seg2 r α t ⟨le_of_lt h1, h2⟩, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
          norm_exp_I, mul_one]
        linarith
      · rw [sectorCurve_seg3 r α t ⟨le_of_lt h2, ht3⟩, norm_mul,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (by linarith) hr.le),
          norm_exp_I, mul_one]
        nlinarith
  set φ_g := fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t
  have h_int_g : IntervalIntegrable φ_g volume 0 3 := by
    have h01 : IntervalIntegrable φ_g volume 0 1 := by
      have hc : ContinuousOn (fun t : ℝ => g ((t * r : ℝ) : ℂ) * (r : ℂ)) (Icc 0 1) := by
        apply ContinuousOn.mul
        · exact hg.continuousOn.comp
            ((continuous_ofReal.comp (continuous_id.mul continuous_const)).continuousOn)
            (fun t ht => by
              have := hγ_in_ball t ⟨ht.1, by linarith [ht.2]⟩
              rwa [sectorCurve_seg1 r α t ht] at this)
        · exact continuousOn_const
      exact (hc.intervalIntegrable_of_Icc (by norm_num)).congr_ae (by
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),
          ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        show _ = φ_g t
        simp only [φ_g, sectorCurve_seg1 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
          deriv_sectorCurve_seg1 r α t ht])
    have h12 : IntervalIntegrable φ_g volume 1 2 := by
      have hc : ContinuousOn (fun t : ℝ => g ((r : ℂ) * exp (I * ((t - 1) * α : ℝ))) *
          ((r : ℂ) * (I * (α : ℂ)) * exp (I * ((t - 1) * α : ℝ)))) (Icc 1 2) := by
        apply ContinuousOn.mul
        · exact hg.continuousOn.comp
            ((continuous_const.mul (continuous_exp.comp
              (continuous_const.mul (continuous_ofReal.comp
                ((continuous_id.sub continuous_const).mul continuous_const))))).continuousOn)
            (fun t ht => by
              have := hγ_in_ball t ⟨by linarith [ht.1], by linarith [ht.2]⟩
              rwa [sectorCurve_seg2 r α t ht] at this)
        · exact (continuous_const.mul (continuous_exp.comp
            (continuous_const.mul (continuous_ofReal.comp
              ((continuous_id.sub continuous_const).mul continuous_const))))).continuousOn
      exact (hc.intervalIntegrable_of_Icc (by norm_num)).congr_ae (by
        rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 2),
          ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        show _ = φ_g t
        simp only [φ_g, sectorCurve_seg2 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
          deriv_sectorCurve_seg2 r α t ht])
    have h23 : IntervalIntegrable φ_g volume 2 3 := by
      have hc : ContinuousOn (fun t : ℝ => g (((3 - t) * r : ℝ) * exp (I * (α : ℂ))) *
          (-(r : ℂ) * exp (I * (α : ℂ)))) (Icc 2 3) := by
        apply ContinuousOn.mul
        · exact hg.continuousOn.comp
            ((continuous_ofReal.comp ((continuous_const.sub continuous_id).mul
              continuous_const)).mul continuous_const).continuousOn
            (fun t ht => by
              have := hγ_in_ball t ⟨by linarith [ht.1], ht.2⟩
              rwa [sectorCurve_seg3 r α t ht] at this)
        · exact continuousOn_const
      exact (hc.intervalIntegrable_of_Icc (by norm_num)).congr_ae (by
        rw [Set.uIoc_of_le (by norm_num : (2:ℝ) ≤ 3),
          ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        show _ = φ_g t
        simp only [φ_g, sectorCurve_seg3 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
          deriv_sectorCurve_seg3 r α t ht])
    exact h01.trans h12 |>.trans h23
  -- DCT: ∫ PV_integrand(g, ε) → ∫ g∘γ γ' = 0
  -- Follows pattern from cauchyPrincipalValueExists_of_continuous_piecewise
  have h_zero_set : Set.Finite ({t ∈ Icc (0:ℝ) 3 | sectorCurve r α t = 0}) := by
    apply Set.Finite.subset (Set.toFinite {(0:ℝ), 3})
    intro t ⟨⟨ht0, ht3⟩, h0⟩
    rcases le_or_gt t 1 with h1 | h1
    · rw [sectorCurve_seg1 r α t ⟨ht0, h1⟩] at h0
      simp only [Complex.ofReal_eq_zero] at h0
      simp [(mul_eq_zero.mp h0).resolve_right hr.ne']
    · rcases le_or_gt t 2 with h2 | h2
      · exfalso; rw [sectorCurve_seg2 r α t ⟨le_of_lt h1, h2⟩] at h0
        simp only [mul_eq_zero, Complex.ofReal_eq_zero] at h0
        exact h0.elim (fun h => by linarith) (Complex.exp_ne_zero _)
      · rw [sectorCurve_seg3 r α t ⟨le_of_lt h2, ht3⟩] at h0
        simp only [mul_eq_zero, Complex.ofReal_eq_zero] at h0
        exact h0.elim (fun h => by
          rcases h with h | h
          · simp [show t = 3 from by linarith]
          · exact absurd h hr.ne') (fun h => absurd h (Complex.exp_ne_zero _))
  have h_g_tend : Tendsto (fun ε => ∫ t in (0:ℝ)..3,
      cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε t)
      (𝓝[>] 0) (𝓝 0) := by
    suffices h : Tendsto (fun ε => ∫ t in (0:ℝ)..3,
        cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε t)
        (𝓝[>] 0) (𝓝 (∫ t in (0:ℝ)..3, φ_g t)) by rwa [hg_zero] at h
    exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun t => ‖φ_g t‖)
      (by -- AE strong measurability
          filter_upwards [self_mem_nhdsWithin] with ε _
          rw [show Ι (0:ℝ) 3 = Ioc 0 3 from uIoc_of_le (by norm_num)]
          exact (h_int_g.aestronglyMeasurable.indicator
            (measurableSet_pv_support (sectorCurve r α) 0 3 0 ε
              (sectorCurve_continuousOn r α))).congr (by
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
            simp only [cauchyPrincipalValueIntegrand', Set.indicator_apply]
            by_cases h : ‖sectorCurve r α t - 0‖ > ε
            · rw [if_pos (show t ∈ {t | ε < ‖sectorCurve r α t - 0‖} ∩ Icc 0 3 from
                ⟨h, Ioc_subset_Icc_self ht⟩), if_pos h]
            · rw [if_neg (show t ∉ {t | ε < ‖sectorCurve r α t - 0‖} ∩ Icc 0 3 from
                fun ⟨hm, _⟩ => h hm), if_neg h]))
      (by -- Domination
          filter_upwards [self_mem_nhdsWithin] with ε _
          exact Eventually.of_forall fun t _ => by
            simp only [cauchyPrincipalValueIntegrand', sub_zero]
            split_ifs with h
            · exact le_refl _
            · exact norm_nonneg _)
      h_int_g.norm
      (by -- Pointwise convergence
          filter_upwards [h_zero_set.countable.ae_notMem _] with t ht ht_uIoc
          have h_ne : sectorCurve r α t ≠ 0 := fun heq =>
            ht ⟨Ioc_subset_Icc_self (uIoc_of_le (by norm_num : (0:ℝ) ≤ 3) ▸ ht_uIoc), heq⟩
          exact tendsto_const_nhds.congr' (by
            filter_upwards [Ioo_mem_nhdsGT
              (norm_pos_iff.mpr (sub_ne_zero.mpr h_ne))] with ε hε
            simp only [cauchyPrincipalValueIntegrand', sub_zero, gt_iff_lt]
            rw [if_pos hε.2]))
  -- c * ∫ PV(z⁻¹) → c * I * α
  have h_c_inv : Tendsto (fun ε => c * ∫ t in (0:ℝ)..3,
      cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t)
      (𝓝[>] 0) (𝓝 (c * (I * ↑α))) := hL_inv.const_mul c
  -- Integral splitting: ∫ PV(c/z+g) = c * ∫ PV(z⁻¹) + ∫ PV(g)
  have h_split : ∀ᶠ ε in 𝓝[>] 0,
      (∫ t in (0:ℝ)..3, cauchyPrincipalValueIntegrand' (fun z => c / z + g z)
        (sectorCurve r α) 0 ε t) =
      c * (∫ t in (0:ℝ)..3, cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
        (sectorCurve r α) 0 ε t) +
      (∫ t in (0:ℝ)..3, cauchyPrincipalValueIntegrand' g
        (sectorCurve r α) 0 ε t) := by
    -- We show the splitting eventually, filtering to ε < r
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hr] with ε hε_lt_r hε_pos
    simp only [mem_Ioi] at hε_pos
    -- Pointwise decomposition: PV(c/z+g, ε, t) = c * PV(z⁻¹, ε, t) + PV(g, ε, t)
    have h_decomp : ∀ t, cauchyPrincipalValueIntegrand' (fun z => c / z + g z)
        (sectorCurve r α) 0 ε t =
      c * cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t +
      cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε t := by
      intro t; simp only [cauchyPrincipalValueIntegrand', sub_zero, div_eq_mul_inv]
      split_ifs <;> ring
    -- Integrability of g's PV integrand (dominated by g∘γ*γ')
    have h_g_pv_int : IntervalIntegrable
        (cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε)
        volume 0 3 :=
      h_int_g.mono_fun (by
        rw [show Ι (0:ℝ) 3 = Ioc 0 3 from uIoc_of_le (by norm_num)]
        exact (h_int_g.aestronglyMeasurable.indicator
          (measurableSet_pv_support (sectorCurve r α) 0 3 0 ε
            (sectorCurve_continuousOn r α))).congr (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          simp only [cauchyPrincipalValueIntegrand', Set.indicator_apply]
          by_cases h : ‖sectorCurve r α t - 0‖ > ε
          · rw [if_pos (show t ∈ {t | ε < ‖sectorCurve r α t - 0‖} ∩ Icc 0 3 from
              ⟨h, Ioc_subset_Icc_self ht⟩), if_pos h]
          · rw [if_neg (show t ∉ {t | ε < ‖sectorCurve r α t - 0‖} ∩ Icc 0 3 from
              fun ⟨hm, _⟩ => h hm), if_neg h]))
        (by filter_upwards with t _
            simp only [cauchyPrincipalValueIntegrand', sub_zero]
            split_ifs with h
            · exact le_refl _
            · simp [norm_nonneg])
    -- PV(z⁻¹, ε) integrable on [0,3] via segment-by-segment argument
    have h_inv_03 : IntervalIntegrable
        (cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε) volume 0 3 := by
      set δ := ε / r
      have hδ : 0 < δ := div_pos hε_pos hr
      have hδ1 : δ < 1 := by rwa [div_lt_one hr]
      have h3δ : 2 < 3 - δ := by linarith
      -- On [0,δ] and [3-δ,3]: PV = 0 (below cutoff), hence integrable
      have hF0δ : IntervalIntegrable
          (cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε) volume 0 δ :=
        (intervalIntegrable_const (c := (0 : ℂ))).congr (fun t ht => by
          rw [Set.uIoc_of_le hδ.le] at ht
          simp only [cauchyPrincipalValueIntegrand', sub_zero]
          rw [if_neg (not_lt.mpr _)]
          rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt ht.1, le_trans ht.2 (le_of_lt hδ1)⟩]
          exact le_trans (mul_le_mul_of_nonneg_right ht.2 hr.le)
            (le_of_eq (by field_simp [δ])))
      have hF3δ3 : IntervalIntegrable
          (cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε)
          volume (3 - δ) 3 :=
        (intervalIntegrable_const (c := (0 : ℂ))).congr (fun t ht => by
          rw [Set.uIoc_of_le (by linarith : 3 - δ ≤ 3)] at ht
          simp only [cauchyPrincipalValueIntegrand', sub_zero]
          rw [if_neg (not_lt.mpr _)]
          have h2 : 2 ≤ t := by linarith [ht.1]
          rw [sectorCurve_norm_seg3' r hr α t ⟨h2, ht.2⟩]
          have : (3 - t) * r ≤ δ * r := mul_le_mul_of_nonneg_right (by linarith [ht.1]) hr.le
          have hδr : δ * r = ε := by field_simp [δ]
          linarith)
      -- On [δ,1]: PV(z⁻¹) = t⁻¹ (continuous, integrable)
      have hFδ1 : IntervalIntegrable
          (cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε)
          volume δ 1 := by
        have hcont : ContinuousOn (fun t : ℝ => (↑(t⁻¹) : ℂ)) (Set.uIcc δ 1) := by
          intro t ht; rw [Set.uIcc_of_le hδ1.le] at ht
          exact (Complex.continuous_ofReal.continuousAt.comp
            (continuousAt_inv₀ (ne_of_gt (lt_of_lt_of_le hδ ht.1)))).continuousWithinAt
        rw [intervalIntegrable_iff, Set.uIoc_of_le hδ1.le]
        have h_eq : ∀ t ∈ Ioo δ (1 : ℝ),
            cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t =
            (↑(t⁻¹) : ℂ) := fun t ⟨htδ, ht1⟩ => by
          simp only [cauchyPrincipalValueIntegrand', sub_zero]
          rw [if_pos]; · exact pv_integrand_seg1 r hr α t ⟨lt_trans hδ htδ, ht1⟩
          · rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt (lt_trans hδ htδ), le_of_lt ht1⟩]
            have hδr : δ * r = ε := by field_simp [δ]
            calc ε = δ * r := hδr.symm
              _ < t * r := by nlinarith
        have h_g_Ioo := (intervalIntegrable_iff.mp hcont.intervalIntegrable).mono_set
          (by rw [Set.uIoc_of_le hδ1.le]; exact Ioo_subset_Ioc_self)
        rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        exact Integrable.congr h_g_Ioo
          ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm)
      -- On [1,2]: PV(z⁻¹) = I*α (constant, integrable)
      have hF12 : IntervalIntegrable
          (cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε)
          volume 1 2 := by
        rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
        have h_eq : ∀ t ∈ Ioo (1 : ℝ) 2,
            cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t =
            I * ↑α := fun t ⟨ht1, ht2⟩ => by
          simp only [cauchyPrincipalValueIntegrand', sub_zero]
          rw [if_pos]; · exact pv_integrand_seg2 r hr α t ⟨ht1, ht2⟩
          · rw [sectorCurve_seg2 r α t ⟨le_of_lt ht1, le_of_lt ht2⟩]
            simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
            rw [Complex.norm_of_nonneg (le_of_lt hr)]; linarith
        have h_const_Ioo := (intervalIntegrable_iff.mp (intervalIntegrable_const :
          IntervalIntegrable (fun _ => I * (↑α : ℂ)) volume 1 2)).mono_set
          (by rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]; exact Ioo_subset_Ioc_self)
        rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        exact Integrable.congr h_const_Ioo
          ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm)
      -- On [2,3-δ]: PV(z⁻¹) = -(3-t)⁻¹ (continuous, integrable)
      have hF2_3δ : IntervalIntegrable
          (cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε)
          volume 2 (3 - δ) := by
        have hcont : ContinuousOn (fun t : ℝ => -(↑((3 - t)⁻¹) : ℂ))
            (Set.uIcc 2 (3 - δ)) := by
          rw [Set.uIcc_of_le h3δ.le]
          intro t ht
          exact (continuous_neg.continuousAt.comp
            (Complex.continuous_ofReal.continuousAt.comp
              ((continuousAt_inv₀ (ne_of_gt (by linarith [ht.2] : (0:ℝ) < 3 - t))).comp
               (continuousAt_const.sub continuousAt_id)))).continuousWithinAt
        rw [intervalIntegrable_iff, Set.uIoc_of_le h3δ.le]
        have h_eq : ∀ t ∈ Ioo (2 : ℝ) (3 - δ),
            cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t =
            -(↑((3 - t)⁻¹) : ℂ) := fun t ⟨ht2, ht3δ⟩ => by
          simp only [cauchyPrincipalValueIntegrand', sub_zero]
          rw [if_pos]
          · rw [sectorCurve_seg3 r α t ⟨le_of_lt ht2, by linarith⟩,
                deriv_sectorCurve_seg3 r α t ⟨ht2, by linarith⟩]
            have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
            have : exp (I * ↑α) ≠ 0 := Complex.exp_ne_zero _
            have : (3 - t : ℝ) ≠ 0 := by linarith
            push_cast; field_simp
          · rw [sectorCurve_norm_seg3' r hr α t ⟨le_of_lt ht2, by linarith⟩]
            have hδr : δ * r = ε := div_mul_cancel₀ ε (ne_of_gt hr)
            calc ε = δ * r := hδr.symm
              _ < (3 - t) * r := by nlinarith
        have h_g_Ioo := (intervalIntegrable_iff.mp hcont.intervalIntegrable).mono_set
          (by rw [Set.uIoc_of_le h3δ.le]; exact Ioo_subset_Ioc_self)
        rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        exact Integrable.congr h_g_Ioo
          ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm)
      -- Combine segments
      exact ((hF0δ.trans hFδ1).trans hF12 |>.trans hF2_3δ).trans hF3δ3
    have h_c_inv_int := h_inv_03.const_mul c
    rw [show (∫ t in (0:ℝ)..3, cauchyPrincipalValueIntegrand' (fun z => c / z + g z)
        (sectorCurve r α) 0 ε t) =
      ∫ t in (0:ℝ)..3, (c * cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
        (sectorCurve r α) 0 ε t +
      cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε t) from
      intervalIntegral.integral_congr (fun t _ => h_decomp t),
      ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_add h_c_inv_int h_g_pv_int
  -- Combine: PV limit = c * (I * α) + 0 = I * α * c
  have h_tendsto : Tendsto (fun ε => ∫ t in (0:ℝ)..3,
      cauchyPrincipalValueIntegrand' (fun z => c / z + g z) (sectorCurve r α) 0 ε t)
      (𝓝[>] 0) (𝓝 (I * ↑α * c)) := by
    rw [show I * ↑α * c = c * (I * ↑α) + 0 from by ring]
    exact (h_c_inv.add h_g_tend).congr' (h_split.mono (fun _ h => h.symm))
  refine ⟨⟨_, h_tendsto⟩, ?_⟩
  exact h_tendsto.limUnder_eq

/-- Variant of Lemma 3.1: for an arbitrary `f` equal to `c/z + g` at nonzero points,
with `g` analytic on a ball containing the sector, the PV equals `I * α * c`. -/
theorem lemma_3_1_residue (r : ℝ) (hr : 0 < r) (α : ℝ)
    (hα_nonneg : 0 ≤ α) (hα_le : α ≤ 2 * Real.pi)
    (f : ℂ → ℂ) (c : ℂ) (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1)))
    (hf_eq : ∀ z, z ≠ 0 → f z = c / z + g z)
    (hc : c = residueSimplePole f 0) :
    CauchyPrincipalValueExists' f (sectorCurve r α) 0 3 0 ∧
    cauchyPrincipalValue' f (sectorCurve r α) 0 3 0 = I * ↑α * residueSimplePole f 0 := by
  -- PV(f) = PV(c/z + g) since f(z) = c/z + g(z) for z ≠ 0,
  -- and the PV integrand only evaluates f at nonzero points (where ‖γ(t)‖ > ε > 0)
  have h_eq : ∀ ε > 0, ∀ t,
      (if ε < ‖sectorCurve r α t - 0‖ then f (sectorCurve r α t) * deriv (sectorCurve r α) t else 0) =
      (if ε < ‖sectorCurve r α t - 0‖ then (c / sectorCurve r α t + g (sectorCurve r α t)) * deriv (sectorCurve r α) t else 0) := by
    intro ε hε t; split_ifs with h
    · have hne : sectorCurve r α t ≠ 0 := by
        intro heq; simp [heq] at h; linarith
      rw [hf_eq _ hne]
    · rfl
  -- Get the result for c/z + g
  have h_sp := lemma_3_1_simple_pole r hr α hα_nonneg hα_le c g hg
  -- Transfer: PV integrals of f and c/z+g agree for ε > 0
  have h_int_eq : ∀ᶠ ε in 𝓝[>] 0,
      (∫ t in (0:ℝ)..3, cauchyPrincipalValueIntegrand' f (sectorCurve r α) 0 ε t) =
      (∫ t in (0:ℝ)..3, cauchyPrincipalValueIntegrand' (fun z => c / z + g z)
        (sectorCurve r α) 0 ε t) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    congr 1; ext t; exact h_eq ε (mem_Ioi.mp hε) t
  -- Existence: transfer from c/z+g to f
  obtain ⟨L, hL⟩ := h_sp.1
  refine ⟨⟨L, hL.congr' (h_int_eq.mono (fun _ h => h.symm))⟩, ?_⟩
  -- Value: PV(f) = PV(c/z+g) = I * α * c = I * α * residueSimplePole f 0
  have h_f_tend := hL.congr' (h_int_eq.mono (fun _ h => h.symm))
  have hpv_f : cauchyPrincipalValue' f (sectorCurve r α) 0 3 0 = L := h_f_tend.limUnder_eq
  have hpv_cg : cauchyPrincipalValue' (fun z => c / z + g z)
      (sectorCurve r α) 0 3 0 = L := hL.limUnder_eq
  rw [hpv_f, ← hpv_cg, h_sp.2, hc]

/-- The generalized winding number of the sector curve around 0
equals `alpha / (2 * pi)`. -/
theorem generalizedWindingNumber_sectorCurve (r : ℝ) (hr : 0 < r) (α : ℝ)
    (hα_nonneg : 0 ≤ α) (hα_le : α ≤ 2 * Real.pi)
    (_hPV : CauchyPrincipalValueExists' (fun z => z⁻¹) (sectorCurve r α) 0 3 0) :
    generalizedWindingNumber' (sectorCurve r α) 0 3 0 = ↑α / (2 * ↑Real.pi) := by
  unfold generalizedWindingNumber'
  -- The PV of dz/z along the sector curve equals I * α
  have hpv_val := (pv_sector_dz_over_z r hr α hα_nonneg hα_le).2
  -- We need: cauchyPrincipalValue' (·⁻¹) (fun t => sectorCurve r α t - 0) 0 3 0
  -- = cauchyPrincipalValue' (·⁻¹) (sectorCurve r α) 0 3 0 = I * α
  have h_sub_zero : (fun t => sectorCurve r α t - 0) = sectorCurve r α := by ext; simp
  rw [h_sub_zero, hpv_val]
  -- Now: (2πi)⁻¹ * (I * α) = α/(2π)
  have h_pi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h_I_ne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp

end
