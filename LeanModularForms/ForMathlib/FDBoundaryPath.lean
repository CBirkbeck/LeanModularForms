/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDBoundary

/-!
# PiecewiseC1Path for the FD Boundary

This file constructs the `PiecewiseC1Path` for the fundamental domain boundary,
proving that `fdBoundaryFun H` is differentiable with continuous derivative on each
segment away from partition points.

## Main definitions

* `fdBoundaryPC1Path` — the FD boundary as a `PiecewiseC1Path`

## Main results

* `fdBoundaryPC1Path_eq` — the path agrees with `fdBoundaryFun` on `[0, 1]`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ### Path.extend agrees with fdBoundaryFun on Icc 0 1 -/

private lemma fdBoundaryPath_extend_eq (H : ℝ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (fdBoundaryPath H).extend t = fdBoundaryFun H t := by
  rw [Path.extend_apply _ ht]; rfl

private lemma fdBoundaryPath_extend_eventuallyEq (H : ℝ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (fdBoundaryPath H).extend =ᶠ[𝓝 t] fdBoundaryFun H :=
  Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs =>
    fdBoundaryPath_extend_eq H s (Ioo_subset_Icc_self hs)

/-! ### Segment functions -/

private def seg1Fun (H : ℝ) : ℝ → ℂ := fun t =>
  1/2 + (↑H - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I

private def seg2Fun : ℝ → ℂ := fun t =>
  exp ((↑Real.pi / 3 + (5 * ↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I)

private def seg3Fun : ℝ → ℂ := fun t =>
  exp ((↑Real.pi / 2 + (5 * ↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)

private def seg4Fun (H : ℝ) : ℝ → ℂ := fun t =>
  -1/2 + (↑(Real.sqrt 3) / 2 + (5 * ↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I

private def seg5Fun (H : ℝ) : ℝ → ℂ := fun t =>
  (5 * ↑t - 9/2) + ↑H * I

/-! ### Segment differentiability -/

private lemma seg1Fun_differentiableAt (H : ℝ) (t : ℝ) :
    DifferentiableAt ℝ (seg1Fun H) t :=
  (differentiableAt_const _).add
    (((differentiableAt_const _).sub
      (((differentiableAt_const _).mul Complex.ofRealCLM.differentiable.differentiableAt).mul
        (differentiableAt_const _))).mul (differentiableAt_const _))

private lemma seg2Fun_differentiableAt (t : ℝ) :
    DifferentiableAt ℝ seg2Fun t :=
  Complex.differentiable_exp.differentiableAt.comp t
    (((differentiableAt_const _).add
      ((((differentiableAt_const _).mul Complex.ofRealCLM.differentiable.differentiableAt).sub
        (differentiableAt_const _)).mul (differentiableAt_const _))).mul
      (differentiableAt_const _))

private lemma seg3Fun_differentiableAt (t : ℝ) :
    DifferentiableAt ℝ seg3Fun t :=
  Complex.differentiable_exp.differentiableAt.comp t
    (((differentiableAt_const _).add
      ((((differentiableAt_const _).mul Complex.ofRealCLM.differentiable.differentiableAt).sub
        (differentiableAt_const _)).mul (differentiableAt_const _))).mul
      (differentiableAt_const _))

private lemma seg4Fun_differentiableAt (H : ℝ) (t : ℝ) :
    DifferentiableAt ℝ (seg4Fun H) t :=
  (differentiableAt_const _).add
    (((differentiableAt_const _).add
      ((((differentiableAt_const _).mul Complex.ofRealCLM.differentiable.differentiableAt).sub
        (differentiableAt_const _)).mul (differentiableAt_const _))).mul
      (differentiableAt_const _))

private lemma seg5Fun_differentiableAt (H : ℝ) (t : ℝ) :
    DifferentiableAt ℝ (seg5Fun H) t :=
  (((differentiableAt_const _).mul Complex.ofRealCLM.differentiable.differentiableAt).sub
    (differentiableAt_const _)).add (differentiableAt_const _)

/-! ### Segment ContDiff -/

private lemma seg1Fun_contDiff (H : ℝ) : ContDiff ℝ ⊤ (seg1Fun H) :=
  contDiff_const.add
    ((contDiff_const.sub
      ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const)).mul
      contDiff_const)

private lemma seg2Fun_contDiff : ContDiff ℝ ⊤ seg2Fun :=
  Complex.contDiff_exp.comp
    ((contDiff_const.add
      (((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).mul
        contDiff_const)).mul contDiff_const)

private lemma seg3Fun_contDiff : ContDiff ℝ ⊤ seg3Fun :=
  Complex.contDiff_exp.comp
    ((contDiff_const.add
      (((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).mul
        contDiff_const)).mul contDiff_const)

private lemma seg4Fun_contDiff (H : ℝ) : ContDiff ℝ ⊤ (seg4Fun H) :=
  contDiff_const.add
    ((contDiff_const.add
      (((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).mul
        contDiff_const)).mul contDiff_const)

private lemma seg5Fun_contDiff (H : ℝ) : ContDiff ℝ ⊤ (seg5Fun H) :=
  ((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).add contDiff_const

/-! ### fdBoundaryFun agrees with segment functions on neighborhoods -/

private lemma fdBoundaryFun_eventuallyEq_seg1 (H : ℝ) (t : ℝ)
    (ht1 : t < 1/5) :
    fdBoundaryFun H =ᶠ[𝓝 t] seg1Fun H :=
  Filter.eventually_of_mem (Iio_mem_nhds ht1) fun s (hs : s < 1/5) => by
    simp only [fdBoundaryFun, seg1Fun, show s ≤ 1/5 from le_of_lt hs, ite_true]

private lemma fdBoundaryFun_eventuallyEq_seg2 (H : ℝ) (t : ℝ)
    (ht1 : 1/5 < t) (ht2 : t < 2/5) :
    fdBoundaryFun H =ᶠ[𝓝 t] seg2Fun :=
  Filter.eventually_of_mem
    (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht2))
    fun s ⟨hs1, hs2⟩ => by
      simp only [fdBoundaryFun, seg2Fun,
        show ¬s ≤ 1/5 from not_le.mpr hs1,
        show s ≤ 2/5 from le_of_lt hs2, ite_true, ite_false]

private lemma fdBoundaryFun_eventuallyEq_seg3 (H : ℝ) (t : ℝ)
    (ht2 : 2/5 < t) (ht3 : t < 3/5) :
    fdBoundaryFun H =ᶠ[𝓝 t] seg3Fun :=
  Filter.eventually_of_mem
    (Filter.inter_mem (Ioi_mem_nhds ht2) (Iio_mem_nhds ht3))
    fun s ⟨hs2, hs3⟩ => by
      simp only [fdBoundaryFun, seg3Fun,
        show ¬s ≤ 1/5 from not_le.mpr (lt_trans (by norm_num : (1:ℝ)/5 < 2/5) hs2),
        show ¬s ≤ 2/5 from not_le.mpr hs2,
        show s ≤ 3/5 from le_of_lt hs3, ite_true, ite_false]

private lemma fdBoundaryFun_eventuallyEq_seg4 (H : ℝ) (t : ℝ)
    (ht3 : 3/5 < t) (ht4 : t < 4/5) :
    fdBoundaryFun H =ᶠ[𝓝 t] seg4Fun H :=
  Filter.eventually_of_mem
    (Filter.inter_mem (Ioi_mem_nhds ht3) (Iio_mem_nhds ht4))
    fun s ⟨hs3, hs4⟩ => by
      simp only [fdBoundaryFun, seg4Fun,
        show ¬s ≤ 1/5 from not_le.mpr (lt_trans (by norm_num : (1:ℝ)/5 < 3/5) hs3),
        show ¬s ≤ 2/5 from not_le.mpr (lt_trans (by norm_num : (2:ℝ)/5 < 3/5) hs3),
        show ¬s ≤ 3/5 from not_le.mpr hs3,
        show s ≤ 4/5 from le_of_lt hs4, ite_true, ite_false]

private lemma fdBoundaryFun_eventuallyEq_seg5 (H : ℝ) (t : ℝ)
    (ht4 : 4/5 < t) :
    fdBoundaryFun H =ᶠ[𝓝 t] seg5Fun H :=
  Filter.eventually_of_mem (Ioi_mem_nhds ht4) fun s (hs4 : 4/5 < s) => by
    simp only [fdBoundaryFun, seg5Fun,
      show ¬s ≤ 1/5 from not_le.mpr (lt_trans (by norm_num : (1:ℝ)/5 < 4/5) hs4),
      show ¬s ≤ 2/5 from not_le.mpr (lt_trans (by norm_num : (2:ℝ)/5 < 4/5) hs4),
      show ¬s ≤ 3/5 from not_le.mpr (lt_trans (by norm_num : (3:ℝ)/5 < 4/5) hs4),
      show ¬s ≤ 4/5 from not_le.mpr hs4, ite_false]

/-! ### Differentiability of fdBoundaryFun -/

private lemma fdBoundaryFun_differentiableAt_off (H : ℝ) (t : ℝ)
    (_ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ fdBoundaryPartition) :
    DifferentiableAt ℝ (fdBoundaryFun H) t := by
  simp only [fdBoundaryPartition, Finset.mem_insert, Finset.mem_singleton] at htp
  push_neg at htp; obtain ⟨ht1, ht2, ht3, ht4⟩ := htp
  by_cases h1 : t < 1/5
  · exact (seg1Fun_differentiableAt H t).congr_of_eventuallyEq
      (fdBoundaryFun_eventuallyEq_seg1 H t h1)
  · push_neg at h1
    by_cases h2 : t < 2/5
    · exact (seg2Fun_differentiableAt t).congr_of_eventuallyEq
        (fdBoundaryFun_eventuallyEq_seg2 H t (lt_of_le_of_ne h1 (Ne.symm ht1)) h2)
    · push_neg at h2
      by_cases h3 : t < 3/5
      · exact (seg3Fun_differentiableAt t).congr_of_eventuallyEq
          (fdBoundaryFun_eventuallyEq_seg3 H t (lt_of_le_of_ne h2 (Ne.symm ht2)) h3)
      · push_neg at h3
        by_cases h4 : t < 4/5
        · exact (seg4Fun_differentiableAt H t).congr_of_eventuallyEq
            (fdBoundaryFun_eventuallyEq_seg4 H t (lt_of_le_of_ne h3 (Ne.symm ht3)) h4)
        · push_neg at h4
          exact (seg5Fun_differentiableAt H t).congr_of_eventuallyEq
            (fdBoundaryFun_eventuallyEq_seg5 H t (lt_of_le_of_ne h4 (Ne.symm ht4)))

/-! ### Derivative continuity of fdBoundaryFun -/

private lemma fdBoundaryFun_deriv_continuousAt_off (H : ℝ) (t : ℝ)
    (_ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ fdBoundaryPartition) :
    ContinuousAt (deriv (fdBoundaryFun H)) t := by
  simp only [fdBoundaryPartition, Finset.mem_insert, Finset.mem_singleton] at htp
  push_neg at htp; obtain ⟨ht1, ht2, ht3, ht4⟩ := htp
  by_cases h1 : t < 1/5
  · exact (continuousAt_congr (fdBoundaryFun_eventuallyEq_seg1 H t h1).deriv).mpr
      ((seg1Fun_contDiff H).continuous_deriv le_top).continuousAt
  · push_neg at h1
    by_cases h2 : t < 2/5
    · exact (continuousAt_congr (fdBoundaryFun_eventuallyEq_seg2 H t
          (lt_of_le_of_ne h1 (Ne.symm ht1)) h2).deriv).mpr
        (seg2Fun_contDiff.continuous_deriv le_top).continuousAt
    · push_neg at h2
      by_cases h3 : t < 3/5
      · exact (continuousAt_congr (fdBoundaryFun_eventuallyEq_seg3 H t
            (lt_of_le_of_ne h2 (Ne.symm ht2)) h3).deriv).mpr
          (seg3Fun_contDiff.continuous_deriv le_top).continuousAt
      · push_neg at h3
        by_cases h4 : t < 4/5
        · exact (continuousAt_congr (fdBoundaryFun_eventuallyEq_seg4 H t
              (lt_of_le_of_ne h3 (Ne.symm ht3)) h4).deriv).mpr
            ((seg4Fun_contDiff H).continuous_deriv le_top).continuousAt
        · push_neg at h4
          exact (continuousAt_congr (fdBoundaryFun_eventuallyEq_seg5 H t
              (lt_of_le_of_ne h4 (Ne.symm ht4))).deriv).mpr
            ((seg5Fun_contDiff H).continuous_deriv le_top).continuousAt

/-! ### Transfer from fdBoundaryFun to Path.extend -/

private lemma fdBoundaryPath_differentiableAt_off (H : ℝ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ fdBoundaryPartition) :
    DifferentiableAt ℝ (fdBoundaryPath H).extend t :=
  (fdBoundaryFun_differentiableAt_off H t ht htp).congr_of_eventuallyEq
    (fdBoundaryPath_extend_eventuallyEq H t ht)

private lemma fdBoundaryPath_deriv_continuousAt_off (H : ℝ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ fdBoundaryPartition) :
    ContinuousAt (deriv (fdBoundaryPath H).extend) t :=
  (continuousAt_congr (fdBoundaryPath_extend_eventuallyEq H t ht).deriv).mpr
    (fdBoundaryFun_deriv_continuousAt_off H t ht htp)

/-! ### The PiecewiseC1Path construction -/

/-- The fundamental domain boundary as a `PiecewiseC1Path`. -/
def fdBoundaryPC1Path (H : ℝ) (_hH : H > Real.sqrt 3 / 2) :
    PiecewiseC1Path (fdStart H) (fdStart H) where
  toPath := fdBoundaryPath H
  partition := fdBoundaryPartition
  partition_subset := fdBoundaryPartition_subset_Ioo
  differentiable_off := fun t ht htp =>
    fdBoundaryPath_differentiableAt_off H t ht htp
  deriv_continuous_off := fun t ht htp =>
    fdBoundaryPath_deriv_continuousAt_off H t ht htp

/-- The `PiecewiseC1Path` agrees with `fdBoundaryFun` on `[0, 1]`. -/
theorem fdBoundaryPC1Path_eq (H : ℝ) (hH : H > Real.sqrt 3 / 2) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (fdBoundaryPC1Path H hH).toPath.extend t = fdBoundaryFun H t :=
  fdBoundaryPath_extend_eq H t ht

end
