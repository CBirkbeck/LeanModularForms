/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDBoundary
import LeanModularForms.ForMathlib.HomotopyInvariance
import LeanModularForms.ForMathlib.SingleCrossing

/-!
# Interior Winding Number for the FD Boundary

Supporting infrastructure for the theorem that the generalized winding number of
the fundamental domain boundary around any strict interior point equals `-1`.

A **strict interior point** `z` satisfies `1 < ‖z‖`, `|z.re| < 1/2`, and
`z.im < H` (for the chosen height `H > √3/2`). Such a point lies strictly
inside the fundamental domain boundary contour but is not on the boundary itself.

## Main results

* `fdBoundaryFun_ne_strictInterior` -- pointwise: the FD boundary never
  equals a strict interior point.

* `fdBoundary_avoids_strictInterior` -- the FD boundary has positive minimum
  distance from any strict interior point.

* `hasGeneralizedWindingNumber_fdBoundary_of_strictInterior` -- the generalized
  winding number exists and equals `(2πi)⁻¹ * ∮_γ (w - z)⁻¹ dw`.

* `generalizedWindingNumber_fdBoundary_eq_contourIntegral` -- the generalized
  winding number value equals the contour integral formula.

* `fdBoundary_image_subset_compl_singleton` -- the FD boundary image avoids `z`.

* Distance bounds for each segment type: `norm_sub_ge_of_unit_circle`,
  `norm_sub_ge_of_re_half`, `norm_sub_ge_of_re_neg_half`, `norm_sub_ge_of_im_eq`.

## Design notes

The full proof that the winding number equals `-1` requires a homotopy argument
(deforming the FD boundary to a small circle around `z`) or a direct segment-by-segment
computation of the contour integral. Both approaches require ~1000+ lines of
infrastructure beyond what is currently available sorry-free.

This file provides the sorry-free reduction to the contour integral value, plus
all the distance and avoidance bounds needed by downstream consumers.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

noncomputable section

/-! ### Segment-by-segment avoidance

Each segment of the FD boundary has a distinguishing feature that separates it
from any strict interior point:
- Segments 1, 4: real part equals `±1/2`
- Segments 2, 3: norm equals `1` (unit circle arc)
- Segment 5: imaginary part equals `H`
-/

/-- On segment 1 (`t ∈ [0, 1/5]`), the FD boundary has `re = 1/2`,
so `fdBoundaryFun H t ≠ z` when `z.re < 1/2`. -/
theorem fdBoundaryFun_ne_seg1 {z : ℂ} (hz : z.re < 1 / 2) {H : ℝ}
    {t : ℝ} (ht : t ≤ 1 / 5) : fdBoundaryFun H t ≠ z := by
  simp only [fdBoundaryFun, ht, ite_true]
  intro heq
  have hre : (1 / 2 + (↑H - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I : ℂ).re = 1 / 2 := by
    simp [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
  linarith [congr_arg re heq, hre]

/-- On segment 4 (`t ∈ (3/5, 4/5]`), the FD boundary has `re = -1/2`,
so `fdBoundaryFun H t ≠ z` when `-(1/2) < z.re`. -/
theorem fdBoundaryFun_ne_seg4 {z : ℂ} (hz : -(1 / 2) < z.re) {H : ℝ}
    {t : ℝ} (ht1 : ¬t ≤ 1 / 5) (ht2 : ¬t ≤ 2 / 5) (ht3 : ¬t ≤ 3 / 5) (ht4 : t ≤ 4 / 5) :
    fdBoundaryFun H t ≠ z := by
  simp only [fdBoundaryFun, ht1, ht2, ht3, ht4, ite_true, ite_false]
  intro heq
  have hre : (-1 / 2 + (↑(Real.sqrt 3) / 2 + 5 * (↑t - 3 / 5) *
      (↑H - ↑(Real.sqrt 3) / 2)) * I : ℂ).re = -(1 / 2) := by
    simp [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, sub_re]
    norm_num
  linarith [congr_arg re heq, hre]

/-- On segment 5 (`t ∈ (4/5, 1]`), the FD boundary has `im = H`,
so `fdBoundaryFun H t ≠ z` when `z.im < H`. -/
theorem fdBoundaryFun_ne_seg5 {z : ℂ} {H : ℝ} (hz : z.im < H) {t : ℝ}
    (ht1 : ¬t ≤ 1 / 5) (ht2 : ¬t ≤ 2 / 5) (ht3 : ¬t ≤ 3 / 5) (ht4 : ¬t ≤ 4 / 5) :
    fdBoundaryFun H t ≠ z := by
  simp only [fdBoundaryFun, ht1, ht2, ht3, ht4, ite_false]
  intro heq
  have him : (-1 / 2 + 5 * (↑t - 4 / 5) + ↑H * I : ℂ).im = H := by
    simp [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, sub_im]
  linarith [congr_arg im heq, him]

/-- On segments 2-3 (the unit circle arcs), `‖fdBoundaryFun H t‖ = 1`,
so `fdBoundaryFun H t ≠ z` when `‖z‖ > 1`. -/
theorem fdBoundaryFun_ne_arc {z : ℂ} (hz : 1 < ‖z‖) {H : ℝ}
    {t : ℝ} (ht1 : ¬t ≤ 1 / 5) (ht2_or_3 : t ≤ 2 / 5 ∨ (¬t ≤ 2 / 5 ∧ t ≤ 3 / 5)) :
    fdBoundaryFun H t ≠ z := by
  intro heq
  rcases ht2_or_3 with ht2 | ⟨ht2, ht3⟩
  · -- Segment 2: exp(angle * I) on the unit circle
    simp only [fdBoundaryFun, ht1, ht2, ite_true, ite_false] at heq
    have h_eq_ofReal : (↑Real.pi / 3 + 5 * (↑t - 1 / 5) *
        (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
        ↑(Real.pi / 3 + 5 * (t - 1 / 5) * (Real.pi / 2 - Real.pi / 3)) * I := by
      push_cast; ring
    rw [h_eq_ofReal] at heq
    linarith [congr_arg (‖·‖) heq, norm_exp_ofReal_mul_I
      (Real.pi / 3 + 5 * (t - 1 / 5) * (Real.pi / 2 - Real.pi / 3))]
  · -- Segment 3: exp(angle * I) on the unit circle
    simp only [fdBoundaryFun, ht1, ht2, ht3, ite_true, ite_false] at heq
    have h_eq_ofReal : (↑Real.pi / 2 + 5 * (↑t - 2 / 5) *
        (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
        ↑(Real.pi / 2 + 5 * (t - 2 / 5) * (2 * Real.pi / 3 - Real.pi / 2)) * I := by
      push_cast; ring
    rw [h_eq_ofReal] at heq
    linarith [congr_arg (‖·‖) heq, norm_exp_ofReal_mul_I
      (Real.pi / 2 + 5 * (t - 2 / 5) * (2 * Real.pi / 3 - Real.pi / 2))]

/-! ### Main avoidance theorem -/

/-- **The FD boundary never passes through a strict interior point.**

For each parameter `t`, the contour value `fdBoundaryFun H t ≠ z`
when `z` satisfies `‖z‖ > 1`, `|z.re| < 1/2`, and `z.im < H`.

The proof is by cases on the 5 segments:
- Segments 1, 4: `re = ±1/2` but `|z.re| < 1/2`
- Segments 2, 3: `‖w‖ = 1` but `‖z‖ > 1`
- Segment 5: `im = H` but `z.im < H` -/
theorem fdBoundaryFun_ne_strictInterior {z : ℂ} (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1 / 2)
    (H : ℝ) (_ : H > Real.sqrt 3 / 2) (hz_im : z.im < H) (t : ℝ) :
    fdBoundaryFun H t ≠ z := by
  have hz_re_lt : z.re < 1 / 2 := lt_of_le_of_lt (le_abs_self _) hz_re
  have hz_re_gt : -(1 / 2) < z.re := lt_of_lt_of_le (neg_lt_neg hz_re) (neg_abs_le _)
  by_cases h1 : t ≤ 1 / 5
  · exact fdBoundaryFun_ne_seg1 hz_re_lt h1
  · by_cases h2 : t ≤ 2 / 5
    · exact fdBoundaryFun_ne_arc hz_norm h1 (Or.inl h2)
    · by_cases h3 : t ≤ 3 / 5
      · exact fdBoundaryFun_ne_arc hz_norm h1 (Or.inr ⟨h2, h3⟩)
      · by_cases h4 : t ≤ 4 / 5
        · exact fdBoundaryFun_ne_seg4 hz_re_gt h1 h2 h3 h4
        · exact fdBoundaryFun_ne_seg5 hz_im h1 h2 h3 h4

/-! ### Path.extend agrees with fdBoundaryFun on [0, 1] -/

/-- On `Icc 0 1`, `Path.extend` of the FD boundary equals `fdBoundaryFun`. -/
private theorem fdBoundary_extend_eq_fun (H : ℝ) (hH : H > Real.sqrt 3 / 2)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (fdBoundary H hH).toPath.extend t = fdBoundaryFun H t := by
  simp only [fdBoundary, fdBoundaryPath, Path.extend, IccExtend,
    ContinuousMap.coe_mk, Function.comp_def]
  simp only [projIcc_of_mem zero_le_one ht]; rfl

/-! ### Quantitative distance bound -/

/-- **The FD boundary has a positive minimum distance from any strict interior point.**

This is the key input to `hasGeneralizedWindingNumber_of_avoids`. The proof
uses compactness of `[0, 1]` and the pointwise avoidance from
`fdBoundaryFun_ne_strictInterior`. -/
theorem fdBoundary_avoids_strictInterior {z : ℂ}
    (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1 / 2)
    (H : ℝ) (hH : H > Real.sqrt 3 / 2) (hz_im : z.im < H) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1,
      δ ≤ ‖(fdBoundary H hH).toPath.extend t - z‖ := by
  set γ := (fdBoundary H hH).toPath.extend
  have h_ne : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ z := by
    intro t ht
    rw [fdBoundary_extend_eq_fun H hH t ht]
    exact fdBoundaryFun_ne_strictInterior hz_norm hz_re H hH hz_im t
  have h_cont : ContinuousOn (fun t => ‖γ t - z‖) (Icc 0 1) :=
    ((fdBoundary H hH).continuous.continuousOn.sub continuousOn_const).norm
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨0, left_mem_Icc.mpr zero_le_one⟩ h_cont
  exact ⟨‖γ t₀ - z‖, norm_pos_iff.mpr (sub_ne_zero.mpr (h_ne t₀ ht₀)),
    fun t ht => hmin ht⟩

/-! ### Winding number via avoidance -/

/-- **The generalized winding number of the FD boundary around a strict interior point
exists** and equals `(2πi)⁻¹ * ∮_γ (w - z)⁻¹ dw`.

This reduces the winding number computation to the contour integral value.
The proof uses the positive distance bound from `fdBoundary_avoids_strictInterior`
and the general `hasGeneralizedWindingNumber_of_avoids` theorem. -/
theorem hasGeneralizedWindingNumber_fdBoundary_of_strictInterior
    {z : ℂ} (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1 / 2)
    (H : ℝ) (hH : H > Real.sqrt 3 / 2) (hz_im : z.im < H) :
    HasGeneralizedWindingNumber (fdBoundary H hH) z
      ((2 * ↑Real.pi * I)⁻¹ *
        (fdBoundary H hH).contourIntegral (fun w => (w - z)⁻¹)) :=
  hasGeneralizedWindingNumber_of_avoids
    (fdBoundary_avoids_strictInterior hz_norm hz_re H hH hz_im)

/-- **The generalized winding number value** equals the contour integral formula. -/
theorem generalizedWindingNumber_fdBoundary_eq_contourIntegral
    {z : ℂ} (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1 / 2)
    (H : ℝ) (hH : H > Real.sqrt 3 / 2) (hz_im : z.im < H) :
    generalizedWindingNumber (fdBoundary H hH) z =
      (2 * ↑Real.pi * I)⁻¹ *
        (fdBoundary H hH).contourIntegral (fun w => (w - z)⁻¹) :=
  (hasGeneralizedWindingNumber_fdBoundary_of_strictInterior
    hz_norm hz_re H hH hz_im).eq

/-! ### Image containment -/

/-- **The FD boundary image lies in `{z}ᶜ`** (complement of the singleton)
when `z` is a strict interior point. -/
theorem fdBoundary_image_subset_compl_singleton
    {z : ℂ} (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1 / 2)
    (H : ℝ) (hH : H > Real.sqrt 3 / 2) (hz_im : z.im < H) :
    ∀ t ∈ Icc (0 : ℝ) 1, (fdBoundary H hH) t ∈ ({z} : Set ℂ)ᶜ := by
  intro t ht
  simp only [mem_compl_iff, mem_singleton_iff]
  obtain ⟨δ, hδ_pos, hδ_bound⟩ :=
    fdBoundary_avoids_strictInterior hz_norm hz_re H hH hz_im
  intro heq
  have h := hδ_bound t ht
  simp only [PiecewiseC1Path.extendedPath_eq] at heq
  rw [heq, sub_self, norm_zero] at h
  linarith

/-! ### Supporting computation: distance bounds by segment type

These lemmas provide explicit lower bounds on `‖w - z‖` based on the
geometric properties of each contour segment. They are useful for
downstream computations that need quantitative distance estimates. -/

/-- Distance from a unit-circle point to a point with `‖z‖ > 1`. -/
theorem norm_sub_ge_of_unit_circle {w z : ℂ} (hw : ‖w‖ = 1) (_ : 1 < ‖z‖) :
    ‖z‖ - 1 ≤ ‖w - z‖ := by
  calc ‖z‖ - 1 = ‖z‖ - ‖w‖ := by rw [hw]
    _ ≤ ‖z - w‖ := norm_sub_norm_le z w
    _ = ‖w - z‖ := norm_sub_rev z w

/-- Distance from a point with `re = 1/2` to a point with `re < 1/2`. -/
theorem norm_sub_ge_of_re_half {w z : ℂ} (hw : w.re = 1 / 2) (_ : z.re < 1 / 2) :
    1 / 2 - z.re ≤ ‖w - z‖ := by
  calc 1 / 2 - z.re = w.re - z.re := by rw [hw]
    _ = (w - z).re := by simp [sub_re]
    _ ≤ |(w - z).re| := le_abs_self _
    _ ≤ ‖w - z‖ := Complex.abs_re_le_norm (w - z)

/-- Distance from a point with `re = -1/2` to a point with `re > -1/2`. -/
theorem norm_sub_ge_of_re_neg_half {w z : ℂ} (hw : w.re = -(1 / 2))
    (_ : -(1 / 2) < z.re) :
    z.re - (-(1 / 2)) ≤ ‖w - z‖ := by
  have : z.re + 1 / 2 = z.re - (-(1 / 2)) := by ring
  calc z.re - (-(1 / 2)) = z.re - w.re := by rw [hw]
    _ = -((w - z).re) := by simp [sub_re]
    _ ≤ |(w - z).re| := neg_le_abs _
    _ ≤ ‖w - z‖ := Complex.abs_re_le_norm (w - z)

/-- Distance from a point with `im = H` to a point with `im < H`. -/
theorem norm_sub_ge_of_im_eq {w z : ℂ} {H : ℝ} (hw : w.im = H) (_ : z.im < H) :
    H - z.im ≤ ‖w - z‖ := by
  calc H - z.im = w.im - z.im := by rw [hw]
    _ = (w - z).im := by simp [sub_im]
    _ ≤ |(w - z).im| := le_abs_self _
    _ ≤ ‖w - z‖ := Complex.abs_im_le_norm (w - z)

end
