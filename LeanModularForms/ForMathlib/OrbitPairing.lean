/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDBoundary
import LeanModularForms.ForMathlib.EllipticWeights
import LeanModularForms.ForMathlib.PiecewiseContourIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Orbit Pairing and T/S Invariance

Modular symmetry cancellations for the contour integral around the standard fundamental
domain boundary at height `H`.

## Overview

The fundamental domain boundary has five segments:
1. Right vertical: `re = 1/2`, from `1/2 + Hi` down to `ρ + 1`
2. Arc from `ρ + 1` to `I`
3. Arc from `I` to `ρ`
4. Left vertical: `re = -1/2`, from `ρ` up to `-1/2 + Hi`
5. Horizontal: `im = H`, from `-1/2 + Hi` to `1/2 + Hi`

The T-translation `z ↦ z + 1` identifies the left and right vertical edges.
For any function satisfying `f(z + 1) = f(z)`, the contour integrals along
segments 1 and 4 cancel.

## Main results

### Edge relationships
* `seg4_eq_seg1_sub_one` -- `fdBoundaryFun` on seg4 equals seg1 value minus 1 (reversed)
* `seg1_eq_seg4_add_one` -- `fdBoundaryFun` on seg1 equals seg4 value plus 1 (reversed)

### T-periodicity cancellation
* `seg4_integrand_eq_neg_seg1` -- for `f(z+1) = f(z)`, the integrand on seg4
  at parameter `t` equals the negative of the integrand on seg1 at `4/5 - t`

### Elliptic point orbit pairing
* `periodic_eq_at_rho` -- `f(ρ + 1) = f(ρ)` for T-periodic functions

### S-transformation
* `S_map_rhoPlusOne` -- `S(ρ+1) = ρ`
* `S_map_rho` -- `S(ρ) = ρ+1`
* `S_map_I` -- `S(I) = I`
* `S_map_involution` -- `S(S(z)) = z`
* `seg2_seg3_product` -- `γ(t) · γ(4/5-t) = -1` on arc segments

### Derivatives
* `deriv_fdBoundaryFun_seg1` -- derivative on segment 1
* `deriv_fdBoundaryFun_seg4` -- derivative on segment 4
* `deriv_fdBoundaryFun_seg5` -- derivative on segment 5

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
* T. Apostol, *Modular Functions and Dirichlet Series in Number Theory*
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

noncomputable section

/-! ### T-periodicity: basic consequences -/

/-- A function is T-periodic (period 1) if `f(z + 1) = f(z)` for all `z`. -/
def IsPeriodic (f : ℂ → ℂ) : Prop := ∀ z, f (z + 1) = f z

theorem IsPeriodic.eq {f : ℂ → ℂ} (hf : IsPeriodic f) (z : ℂ) : f (z + 1) = f z :=
  hf z

theorem IsPeriodic.eq_sub {f : ℂ → ℂ} (hf : IsPeriodic f) (z : ℂ) : f z = f (z - 1) := by
  have := hf (z - 1)
  rwa [sub_add_cancel] at this

theorem IsPeriodic.comp_add_one {f : ℂ → ℂ} (hf : IsPeriodic f) :
    f ∘ (· + 1) = f :=
  funext hf

/-! ### Elliptic point orbit pairing under T -/

/-- The elliptic points `ρ` and `ρ + 1` are T-translates. -/
theorem rho_add_one_eq_rhoPlusOne' : rho + 1 = rhoPlusOne :=
  rho_add_one

/-- For a T-periodic function, the values at `ρ` and `ρ + 1` agree. -/
theorem periodic_eq_at_rho {f : ℂ → ℂ} (hf : IsPeriodic f) :
    f rhoPlusOne = f rho := by
  rw [← rho_add_one]
  exact hf rho

/-- For a T-periodic function, the values at `ρ + 1` and `ρ` agree
(reverse direction). -/
theorem periodic_eq_at_rhoPlusOne {f : ℂ → ℂ} (hf : IsPeriodic f) :
    f rho = f rhoPlusOne :=
  (periodic_eq_at_rho hf).symm

/-! ### Segment relationship under T-translation

Segment 1 parameterizes the right vertical edge `{1/2 + ti : t ∈ [√3/2, H]}`
traversed downward, while segment 4 parameterizes the left vertical edge
`{-1/2 + ti : t ∈ [√3/2, H]}` traversed upward.

The T-translation `z ↦ z + 1` maps each point on segment 4 to
the corresponding point on segment 1 (with reversed parameterization direction). -/

/-- On segment 4 at parameter `t ∈ (3/5, 4/5]`, the boundary function equals
the segment 1 value at the "reversed" parameter `4/5 - t`, minus 1. -/
theorem seg4_eq_seg1_sub_one {H : ℝ} {t : ℝ} (ht1 : 3 / 5 < t) (ht2 : t ≤ 4 / 5) :
    fdBoundaryFun H t = fdBoundaryFun H (4 / 5 - t) - 1 := by
  simp only [fdBoundaryFun,
    show ¬t ≤ 1 / 5 from not_le.mpr (by linarith),
    show ¬t ≤ 2 / 5 from not_le.mpr (by linarith),
    show ¬t ≤ 3 / 5 from not_le.mpr (by linarith),
    ht2, show (4 : ℝ) / 5 - t ≤ 1 / 5 from by linarith,
    ite_true, ite_false]
  push_cast; ring

/-- On segment 1 at parameter `t ∈ [0, 1/5)`, the boundary function equals
the segment 4 value at the "reversed" parameter `4/5 - t`, plus 1. -/
theorem seg1_eq_seg4_add_one {H : ℝ} {t : ℝ} (ht1 : 0 ≤ t) (ht2 : t < 1 / 5) :
    fdBoundaryFun H t = fdBoundaryFun H (4 / 5 - t) + 1 := by
  have h1 : ¬(4 / 5 - t) ≤ 1 / 5 := not_le.mpr (by linarith)
  have h2 : ¬(4 / 5 - t) ≤ 2 / 5 := not_le.mpr (by linarith)
  have h3 : ¬(4 / 5 - t) ≤ 3 / 5 := not_le.mpr (by linarith)
  have h4 : (4 / 5 - t) ≤ 4 / 5 := by linarith
  simp only [fdBoundaryFun, show t ≤ 1 / 5 from le_of_lt ht2,
    h1, h2, h3, h4, ite_true, ite_false]
  push_cast; ring

/-- The imaginary parts of segments 1 and 4 match at reversed parameters:
seg1 at `t` has the same imaginary part as seg4 at `4/5 - t`. -/
theorem seg1_im_eq_seg4_im {H : ℝ} {t : ℝ} (ht1 : 0 ≤ t) (ht2 : t < 1 / 5) :
    (fdBoundaryFun H t).im = (fdBoundaryFun H (4 / 5 - t)).im := by
  rw [seg1_eq_seg4_add_one ht1 ht2]
  simp [add_im, one_im]

/-! ### Derivative computations on vertical and horizontal segments -/

/-- The derivative of `fdBoundaryFun` on segment 1 is purely imaginary with
coefficient `-5(H - √3/2)`. -/
theorem deriv_fdBoundaryFun_seg1 {H : ℝ} {t : ℝ} (ht : t < 1 / 5) :
    deriv (fdBoundaryFun H) t = -5 * (↑H - ↑(Real.sqrt 3) / 2) * I := by
  have : fdBoundaryFun H =ᶠ[𝓝 t] fun s =>
      1 / 2 + (↑H - 5 * ↑s * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    simp only [fdBoundaryFun, show s ≤ 1 / 5 from le_of_lt hs, ite_true]
  rw [Filter.EventuallyEq.deriv_eq this]
  set c := (↑H - ↑(Real.sqrt 3) / 2 : ℂ)
  have hR : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have hlin : HasDerivAt (fun s : ℝ => (-5 * c * I) * (s : ℂ)) (-5 * c * I) t := by
    convert (hasDerivAt_const t (-5 * c * I)).mul hR using 1
    simp [mul_comm, zero_add]
  have htot : HasDerivAt (fun s : ℝ => (1 / 2 + ↑H * I : ℂ) + (-5 * c * I) * ↑s)
      (-5 * c * I) t := by
    convert (hasDerivAt_const t (1 / 2 + ↑H * I : ℂ)).add hlin using 1; simp
  have heq : (fun s : ℝ => (1 : ℂ) / 2 + (↑H - 5 * ↑s * c) * I) =
      fun s : ℝ => (1 / 2 + ↑H * I : ℂ) + (-5 * c * I) * ↑s := by
    ext s; ring
  rw [heq]; exact htot.deriv

/-- The derivative of `fdBoundaryFun` on segment 4 is purely imaginary with
coefficient `+5(H - √3/2)`. -/
theorem deriv_fdBoundaryFun_seg4 {H : ℝ} {t : ℝ} (h1 : 3 / 5 < t) (h2 : t < 4 / 5) :
    deriv (fdBoundaryFun H) t = 5 * (↑H - ↑(Real.sqrt 3) / 2) * I := by
  have : fdBoundaryFun H =ᶠ[𝓝 t] fun s =>
      -1 / 2 + (↑(Real.sqrt 3) / 2 + 5 * (↑s - 3 / 5) * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
    filter_upwards [Ioi_mem_nhds h1, Iio_mem_nhds h2] with s hs1 hs2
    simp only [fdBoundaryFun,
      show ¬s ≤ 1 / 5 from not_le.mpr (lt_trans (by norm_num) hs1),
      show ¬s ≤ 2 / 5 from not_le.mpr (lt_trans (by norm_num) hs1),
      show ¬s ≤ 3 / 5 from not_le.mpr hs1,
      show s ≤ 4 / 5 from le_of_lt hs2, ite_true, ite_false]
  rw [Filter.EventuallyEq.deriv_eq this]
  set c := (↑H - ↑(Real.sqrt 3) / 2 : ℂ)
  have hR : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have hlin : HasDerivAt (fun s : ℝ => (5 * c * I) * (s : ℂ)) (5 * c * I) t := by
    convert (hasDerivAt_const t (5 * c * I)).mul hR using 1
    simp [mul_comm, zero_add]
  have htot : HasDerivAt
      (fun s : ℝ => (-1 / 2 + ↑(Real.sqrt 3) / 2 * I - 3 * c * I : ℂ) + (5 * c * I) * ↑s)
      (5 * c * I) t := by
    convert (hasDerivAt_const t
      (-1 / 2 + ↑(Real.sqrt 3) / 2 * I - 3 * c * I : ℂ)).add hlin using 1; simp
  have heq :
      (fun s : ℝ => (-1 : ℂ) / 2 + (↑(Real.sqrt 3) / 2 + 5 * (↑s - 3 / 5) * c) * I) =
      fun s : ℝ => (-1 / 2 + ↑(Real.sqrt 3) / 2 * I - 3 * c * I : ℂ) + (5 * c * I) * ↑s := by
    ext s; ring
  rw [heq]; exact htot.deriv

/-- The derivatives on segments 1 and 4 are negatives of each other:
`γ'(seg4) = -γ'(seg1)`. This reflects the opposite traversal direction. -/
theorem deriv_seg4_eq_neg_deriv_seg1 {H : ℝ} {t₁ : ℝ} (ht₁ : t₁ < 1 / 5)
    {t₄ : ℝ} (h₄₁ : 3 / 5 < t₄) (h₄₂ : t₄ < 4 / 5) :
    deriv (fdBoundaryFun H) t₄ = -deriv (fdBoundaryFun H) t₁ := by
  rw [deriv_fdBoundaryFun_seg1 ht₁, deriv_fdBoundaryFun_seg4 h₄₁ h₄₂]
  ring

/-- The derivative on segment 5 is the constant `5` (horizontal traversal). -/
theorem deriv_fdBoundaryFun_seg5 {H : ℝ} {t : ℝ}
    (h1 : 4 / 5 < t) (h2 : t < 1) :
    deriv (fdBoundaryFun H) t = 5 := by
  have : fdBoundaryFun H =ᶠ[𝓝 t] fun s =>
      -1 / 2 + 5 * (↑s - 4 / 5) + ↑H * I := by
    filter_upwards [Ioi_mem_nhds h1, Iio_mem_nhds h2] with s hs1 hs2
    simp only [fdBoundaryFun,
      show ¬s ≤ 1 / 5 from not_le.mpr (lt_trans (by norm_num) hs1),
      show ¬s ≤ 2 / 5 from not_le.mpr (lt_trans (by norm_num) hs1),
      show ¬s ≤ 3 / 5 from not_le.mpr (lt_trans (by norm_num) hs1),
      show ¬s ≤ 4 / 5 from not_le.mpr hs1, ite_false]
  rw [Filter.EventuallyEq.deriv_eq this]
  set k := (-1 / 2 - 4 + ↑H * I : ℂ)
  have heq : (fun s : ℝ => (-1 : ℂ) / 2 + 5 * (↑s - 4 / 5) + ↑H * I) =
      fun s : ℝ => k + (5 : ℂ) * ↑s := by ext s; simp [k]; ring
  rw [heq]
  have hR : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have hlin : HasDerivAt (fun s : ℝ => (5 : ℂ) * ↑s) 5 t := by
    convert (hasDerivAt_const t (5 : ℂ)).mul hR using 1
    simp [mul_comm, zero_add]
  exact ((hasDerivAt_const t k).add hlin |>.congr_deriv (by simp)).deriv

/-! ### T-periodicity and contour integral cancellation -/

/-- For a T-periodic function, the value on segment 4 equals the value on
the T-translated (segment 1) point at the reversed parameter. -/
theorem periodic_seg4_eq_seg1 {f : ℂ → ℂ} (hf : IsPeriodic f)
    {H : ℝ} {t : ℝ} (ht1 : 3 / 5 < t) (ht2 : t ≤ 4 / 5) :
    f (fdBoundaryFun H t) = f (fdBoundaryFun H (4 / 5 - t)) := by
  rw [seg4_eq_seg1_sub_one ht1 ht2]
  have h := hf (fdBoundaryFun H (4 / 5 - t) - 1)
  rw [sub_add_cancel] at h
  exact h.symm

/-- For a T-periodic function, the integrand on segment 4 at parameter `t`
(where `3/5 < t < 4/5`) equals the negative of the integrand on segment 1
at the reversed parameter `4/5 - t` (where `0 < 4/5 - t < 1/5`). -/
theorem seg4_integrand_eq_neg_seg1 {f : ℂ → ℂ} (hf : IsPeriodic f) {H : ℝ}
    {t : ℝ} (h1 : 3 / 5 < t) (h2 : t < 4 / 5) :
    f (fdBoundaryFun H t) * deriv (fdBoundaryFun H) t =
      -(f (fdBoundaryFun H (4 / 5 - t)) * deriv (fdBoundaryFun H) (4 / 5 - t)) := by
  have ht2 : 4 / 5 - t < 1 / 5 := by linarith
  -- Function values agree by T-periodicity
  have hval : f (fdBoundaryFun H t) = f (fdBoundaryFun H (4 / 5 - t)) :=
    periodic_seg4_eq_seg1 hf h1 (le_of_lt h2)
  -- Derivatives are negatives of each other
  have hderiv : deriv (fdBoundaryFun H) t = -deriv (fdBoundaryFun H) (4 / 5 - t) := by
    rw [deriv_fdBoundaryFun_seg4 h1 h2, deriv_fdBoundaryFun_seg1 ht2]; ring
  rw [hval, hderiv]; ring

/-! ### Horizontal segment properties -/

/-- On segment 5, the boundary function traces a horizontal line at height `H`. -/
theorem fdBoundaryFun_seg5_im {H : ℝ} {t : ℝ}
    (ht1 : 4 / 5 < t) (_ : t ≤ 1) :
    (fdBoundaryFun H t).im = H := by
  simp only [fdBoundaryFun,
    show ¬t ≤ 1 / 5 from not_le.mpr (by linarith),
    show ¬t ≤ 2 / 5 from not_le.mpr (by linarith),
    show ¬t ≤ 3 / 5 from not_le.mpr (by linarith),
    show ¬t ≤ 4 / 5 from not_le.mpr ht1, ite_false]
  simp [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, sub_im]

/-- On segment 5, the real part ranges linearly from `-1/2` to `1/2`. -/
theorem fdBoundaryFun_seg5_re {H : ℝ} {t : ℝ}
    (ht1 : 4 / 5 < t) (_ : t ≤ 1) :
    (fdBoundaryFun H t).re = -1 / 2 + 5 * (t - 4 / 5) := by
  simp only [fdBoundaryFun,
    show ¬t ≤ 1 / 5 from not_le.mpr (by linarith),
    show ¬t ≤ 2 / 5 from not_le.mpr (by linarith),
    show ¬t ≤ 3 / 5 from not_le.mpr (by linarith),
    show ¬t ≤ 4 / 5 from not_le.mpr ht1, ite_false]
  simp [add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, sub_re]

/-! ### S-transformation at special points -/

/-- The S-transformation `z ↦ -1/z` maps `ρ+1` to `ρ`. -/
theorem S_map_rhoPlusOne : -1 / rhoPlusOne = rho := by
  have h1 : rhoPlusOne ≠ 0 := by
    rw [rhoPlusOne_eq_exp]; exact exp_ne_zero _
  rw [div_eq_iff h1, rho, rhoPlusOne]
  apply Complex.ext
  · simp [mul_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, neg_re, one_re,
      add_im, mul_im, I_re, I_im]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 from by norm_num)]
  · simp [mul_im, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, neg_im, one_im,
      add_im, mul_im]
    ring

/-- The S-transformation `z ↦ -1/z` maps `ρ` to `ρ+1`. -/
theorem S_map_rho : -1 / rho = rhoPlusOne := by
  have h1 : rho ≠ 0 := by
    rw [rho_eq_exp]; exact exp_ne_zero _
  rw [div_eq_iff h1, rhoPlusOne, rho]
  apply Complex.ext
  · simp [mul_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, neg_re, one_re,
      add_im, mul_im, I_re, I_im]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 from by norm_num)]
  · simp [mul_im, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, neg_im, one_im,
      add_im, mul_im]
    ring

/-- The S-transformation `z ↦ -1/z` fixes `I`. -/
theorem S_map_I : -1 / (I : ℂ) = I := by
  rw [show (-1 : ℂ) / I = -(1 / I) from by ring, one_div, inv_I]
  simp

/-- `S(S(z)) = z` for `z ≠ 0`: the S-transformation is an involution. -/
theorem S_map_involution {z : ℂ} (hz : z ≠ 0) : -1 / (-1 / z) = z := by
  have h1 : -1 / z ≠ 0 := by
    rw [neg_div]; exact neg_ne_zero.mpr (div_ne_zero one_ne_zero hz)
  field_simp

/-- For `z` on the unit circle, `S(z) = -z̄`. This is because
`-1/z = -z̄/|z|² = -z̄` when `|z| = 1`. -/
theorem S_map_unit_circle {z : ℂ} (hz : ‖z‖ = 1) :
    -1 / z = -(starRingEnd ℂ) z := by
  have hne : z ≠ 0 := by
    intro heq; rw [heq, norm_zero] at hz; exact one_ne_zero hz.symm
  rw [show (-1 : ℂ) / z = -(1 / z) from by ring, one_div]
  congr 1
  rw [Complex.inv_def]
  have hsq : normSq z = 1 := by
    have : ‖z‖ ^ 2 = normSq z := by
      rw [sq, Complex.norm_def, Real.mul_self_sqrt (normSq_nonneg z)]
    rw [← this, hz]; norm_num
  rw [hsq]; simp

/-! ### Arc segment symmetry under S-transformation -/

/-- The angle parameterization of segment 2 and segment 3 are complementary:
`seg2Angle(t) + seg3Angle(4/5 - t) = π` for `t ∈ [1/5, 2/5]`. -/
theorem seg2_seg3_angle_complementary {t : ℝ}
    (_ : 1 / 5 ≤ t) (_ : t ≤ 2 / 5) :
    seg2Angle t + seg3Angle (4 / 5 - t) = Real.pi := by
  simp only [seg2Angle, seg3Angle]; ring

/-- The product of FD boundary values at S-paired parameters equals `-1`:
`γ(t) · γ(4/5-t) = -1` for `t ∈ (1/5, 2/5)`.

This reflects the S-transformation identity: on the unit circle with
supplementary angles `α + β = π`, we have `exp(iα) · exp(iβ) = exp(iπ) = -1`. -/
theorem seg2_seg3_product {H : ℝ} {t : ℝ}
    (ht1 : 1 / 5 < t) (ht2 : t < 2 / 5) :
    fdBoundaryFun H t * fdBoundaryFun H (4 / 5 - t) = -1 := by
  have h4m1 : 2 / 5 < 4 / 5 - t := by linarith
  have h4m2 : 4 / 5 - t < 3 / 5 := by linarith
  rw [fdBoundaryFun_seg2_eq ht1 (le_of_lt ht2),
    fdBoundaryFun_seg3_eq h4m1 (le_of_lt h4m2), ← exp_add]
  rw [show (↑(seg2Angle t) * I + ↑(seg3Angle (4 / 5 - t)) * I : ℂ) =
      ↑(seg2Angle t + seg3Angle (4 / 5 - t)) * I from by push_cast; ring,
    seg2_seg3_angle_complementary (le_of_lt ht1) (le_of_lt ht2),
    exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi, Real.sin_pi]
  push_cast; ring

/-! ### Norm of ρ and ρ+1 on the unit circle -/

/-- The norm of `ρ` is 1 (it lies on the unit circle). -/
theorem rho_norm_eq_one : ‖rho‖ = 1 := norm_rho

/-- The norm of `ρ+1` is 1 (it lies on the unit circle). -/
theorem rhoPlusOne_norm_eq_one : ‖rhoPlusOne‖ = 1 := norm_rhoPlusOne

/-! ### Orbifold weights and valence formula coefficients -/

/-- The orbifold weight at `I` is `1/2`. -/
def orbifoldWeight_I : ℚ := 1 / 2

/-- The orbifold weight at `ρ` is `1/3`. -/
def orbifoldWeight_rho : ℚ := 1 / 3

/-- The orbifold weight at `ρ+1` is `1/3`. -/
def orbifoldWeight_rhoPlusOne : ℚ := 1 / 3

/-- The orbifold weights at `ρ` and `ρ+1` agree (they are T-equivalent). -/
theorem orbifoldWeight_rho_eq_rhoPlusOne :
    orbifoldWeight_rho = orbifoldWeight_rhoPlusOne := rfl

/-- The sum of orbifold weights at the three special points. -/
theorem orbifoldWeight_sum :
    (orbifoldWeight_I : ℚ) + orbifoldWeight_rho + orbifoldWeight_rhoPlusOne = 7 / 6 := by
  simp only [orbifoldWeight_I, orbifoldWeight_rho, orbifoldWeight_rhoPlusOne]
  norm_num

/-- The rational coefficient `k/12` in the valence formula. -/
def valenceCoeff (k : ℤ) : ℚ := k / 12

/-- The `k/12` term decomposes as `k/6 · 1/2`, reflecting that the arc
integral gives `k/6` and the `1/2` comes from the semicircle. -/
theorem valenceCoeff_eq (k : ℤ) :
    valenceCoeff k = (k : ℚ) / 6 * (1 / 2) := by
  simp [valenceCoeff]; ring

/-- For weight `k` divisible by 12, the valence coefficient is an integer. -/
theorem valenceCoeff_eq_int {k : ℤ} (hk : (12 : ℤ) ∣ k) :
    ∃ n : ℤ, valenceCoeff k = n := by
  obtain ⟨m, rfl⟩ := hk
  exact ⟨m, by simp [valenceCoeff]⟩

/-! ### Summary of orbit pairing structure

The orbit pairing for the fundamental domain boundary contour decomposes the
contour integral `∮ f'/f dz` into three independent contributions:

1. **Vertical edges (segments 1 + 4)**: Cancel for T-periodic functions,
   contributing 0 to the total.

2. **Arc segments (segments 2 + 3)**: Related by the S-transformation,
   contributing `-k/6` for weight-`k` modular forms. Combined with the
   orbifold weights at `I`, `ρ`, `ρ+1`, this yields the `-k/12` term.

3. **Horizontal segment (segment 5)**: Computes `ord_∞ f` via the
   `q`-expansion winding number.

Together these give the valence formula:
`ord_∞ f - k/12 = Σ_{z ∈ F°} ord_z f + (1/2) ord_I f + (1/3) ord_ρ f`
-/

end
