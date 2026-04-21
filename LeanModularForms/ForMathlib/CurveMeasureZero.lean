/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.HausdorffDimension
import LeanModularForms.ForMathlib.PiecewiseC1Path

/-!
# Curve images have Lebesgue measure zero

The image of a Lipschitz map from a 1-dimensional space into ℂ has 2-D Lebesgue
measure zero. This is the foundation for proving that for any open `U ⊆ ℂ` with
nonempty intersection with a continuous Lipschitz curve, there exists a point in
`U` off the curve (needed for the Cauchy integral formula trick in
`contourIntegral_eq_zero_of_nullHomologous`).

## Main results

* `volume_image_lipschitz_real_zero` — Lipschitz image of a subset of `ℝ` has
  Lebesgue measure `0` in `ℂ`.
* `exists_mem_not_mem_of_isOpen_of_lipschitz` — for open nonempty `U` and
  Lipschitz `γ : ℝ → ℂ` on a compact interval, there exists `w₀ ∈ U` off
  `γ.image`.
-/

open MeasureTheory Set Filter Topology

namespace ForMathlib

/-- The 2-dimensional Hausdorff measure on ℝ is zero on any set.
Follows from `Real.hausdorffMeasure_of_finrank_lt` since `finrank ℝ ℝ = 1 < 2`. -/
theorem hausdorffMeasure_two_real_zero (s : Set ℝ) :
    (MeasureTheory.Measure.hausdorffMeasure 2 : Measure ℝ) s = 0 := by
  have h : (MeasureTheory.Measure.hausdorffMeasure 2 : Measure ℝ) = 0 :=
    Real.hausdorffMeasure_of_finrank_lt (by
      simp only [Module.finrank_self, Nat.cast_one]
      norm_num)
  rw [h]; rfl

/-- The 2-dimensional Hausdorff measure of the image of a set `s ⊆ ℝ` under a
Lipschitz map `f : ℝ → ℂ` is zero. -/
theorem hausdorffMeasure_two_lipschitz_image_zero
    {K : NNReal} {f : ℝ → ℂ} (hf : LipschitzWith K f) (s : Set ℝ) :
    MeasureTheory.Measure.hausdorffMeasure 2 (f '' s) = 0 := by
  have h_le := hf.hausdorffMeasure_image_le (d := 2) (by norm_num) s
  rw [hausdorffMeasure_two_real_zero] at h_le
  simp only [mul_zero, nonpos_iff_eq_zero] at h_le
  exact h_le

/-- The Lebesgue volume in ℂ of the image of a set `s ⊆ ℝ` under a Lipschitz
map `f : ℝ → ℂ` is zero.

Uses that volume on `ℂ` is absolutely continuous w.r.t. the 2-dimensional
Hausdorff measure (both are `AddHaarMeasure`s on a 2-dim real normed space),
so vanishing of Hausdorff 2-measure implies vanishing of volume. -/
theorem volume_image_lipschitz_real_zero
    {K : NNReal} {f : ℝ → ℂ} (hf : LipschitzWith K f) (s : Set ℝ) :
    MeasureTheory.volume (f '' s) = 0 := by
  have h_finrank : ((Module.finrank ℝ ℂ : ℕ) : ℝ) = 2 := by
    simp [Complex.finrank_real_complex]
  have h_haar : (MeasureTheory.Measure.hausdorffMeasure 2 :
      MeasureTheory.Measure ℂ).IsAddHaarMeasure := by
    rw [show (2 : ℝ) = ((Module.finrank ℝ ℂ : ℕ) : ℝ) from h_finrank.symm]
    exact MeasureTheory.isAddHaarMeasure_hausdorffMeasure
  have h_ac : (MeasureTheory.volume : MeasureTheory.Measure ℂ).AbsolutelyContinuous
      (MeasureTheory.Measure.hausdorffMeasure 2) :=
    MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure _ _
  exact h_ac (hausdorffMeasure_two_lipschitz_image_zero hf s)

/-- Existence of a point `w₀ ∈ U` off a Lipschitz curve's image. For open
nonempty `U ⊆ ℂ` and Lipschitz `f : ℝ → ℂ`, since Lipschitz images have
measure zero in `ℂ`, their complement in `U` has positive measure and is
in particular nonempty. -/
theorem exists_mem_not_mem_image_of_isOpen_of_lipschitz
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {K : NNReal} {f : ℝ → ℂ} (hf : LipschitzWith K f) (s : Set ℝ) :
    ∃ w₀ ∈ U, w₀ ∉ f '' s := by
  by_contra h
  push Not at h
  have h_sub : U ⊆ f '' s := fun w hw => h w hw
  have h_zero : MeasureTheory.volume U ≤ 0 := by
    rw [← volume_image_lipschitz_real_zero hf s]
    exact MeasureTheory.measure_mono h_sub
  have h_pos : 0 < MeasureTheory.volume U := hU_open.measure_pos _ hU_ne
  exact (h_zero.trans_lt h_pos).false

end ForMathlib
