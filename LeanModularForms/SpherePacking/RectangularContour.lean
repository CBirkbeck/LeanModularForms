/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.PaperPwC1Immersion
import LeanModularForms.ForMathlib.NullHomologous
import LeanModularForms.ForMathlib.CauchyPrincipalValue
import LeanModularForms.SpherePacking.CauchyCorollaries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Star

/-!
# Rectangular contours in the complex plane

Building blocks for applying the Hungerbühler-Wasem residue theorem
(`hw_3_3_clean_full_mero`) to rectangular contours. Defines:

* `rectangleContour a b c d (hab : a < b) (hcd : c < d)` — the boundary of the
  closed rectangle `[a,b] × [c,d]` as a `ClosedPwC1Immersion` starting at the
  bottom-left corner `a + c·I`, traversed counterclockwise.
* `IsNullHomologous.of_convex_open` — every closed piecewise C¹ immersion whose
  image lies in a convex open set is null-homologous there.
* `cauchy_rectangle_zero` — Cauchy's theorem on a rectangle: if `f` is
  holomorphic on a convex open set `U` containing the closed rectangle
  `[a,b] × [c,d]`, then the contour integral of `f` along the boundary of that
  rectangle is zero. (Direct consequence of `cauchy_integral_zero_pwc1`.)

## Mathlib-friendliness

The three results are stated in maximal generality (no sphere-packing-specific
content). The intention is that they can later move into mathlib as part of a
clean upstream of the HW 3.3 framework. -/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

noncomputable section

namespace LeanModularForms

/-! ## The four sides of a rectangle as smooth segments -/

/-- The bottom side of the rectangle `[a, b] × [c, d]`, parameterised on all of
`ℝ` by `t ↦ (a + 4t(b - a)) + c·I`. -/
private def rectSeg1 (a b c : ℝ) : ℝ → ℂ := fun t =>
  ((a : ℂ) + 4 * t * (b - a)) + (c : ℂ) * I

/-- The right side of the rectangle, parameterised by
`t ↦ b + (c + 4(t - 1/4)(d - c))·I`. -/
private def rectSeg2 (b c d : ℝ) : ℝ → ℂ := fun t =>
  (b : ℂ) + ((c : ℂ) + 4 * (t - 1/4) * (d - c)) * I

/-- The top side of the rectangle, parameterised by
`t ↦ (b - 4(t - 1/2)(b - a)) + d·I`. -/
private def rectSeg3 (a b d : ℝ) : ℝ → ℂ := fun t =>
  ((b : ℂ) - 4 * (t - 1/2) * (b - a)) + (d : ℂ) * I

/-- The left side of the rectangle, parameterised by
`t ↦ a + (d - 4(t - 3/4)(d - c))·I`. -/
private def rectSeg4 (a c d : ℝ) : ℝ → ℂ := fun t =>
  (a : ℂ) + ((d : ℂ) - 4 * (t - 3/4) * (d - c)) * I

/-- The full parameterisation of the rectangular boundary on `[0, 1]`. Outside
`[0, 1]` the value is whatever the last segment gives; this is fine because
we only ever use the path via its restriction to `Icc 0 1`. -/
private def rectangleFun (a b c d : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 1/4 then rectSeg1 a b c t
  else if t ≤ 1/2 then rectSeg2 b c d t
  else if t ≤ 3/4 then rectSeg3 a b d t
  else rectSeg4 a c d t

/-! ### Junction values -/

private lemma rectSeg1_at_zero (a b c : ℝ) :
    rectSeg1 a b c 0 = (a : ℂ) + (c : ℂ) * I := by
  simp [rectSeg1]

private lemma rectSeg1_at_quarter (a b c : ℝ) :
    rectSeg1 a b c (1/4) = (b : ℂ) + (c : ℂ) * I := by
  simp only [rectSeg1]
  push_cast; ring

private lemma rectSeg2_at_quarter (b c d : ℝ) :
    rectSeg2 b c d (1/4) = (b : ℂ) + (c : ℂ) * I := by
  simp only [rectSeg2]
  push_cast; ring

private lemma rectSeg2_at_half (b c d : ℝ) :
    rectSeg2 b c d (1/2) = (b : ℂ) + (d : ℂ) * I := by
  simp only [rectSeg2]
  push_cast; ring

private lemma rectSeg3_at_half (a b d : ℝ) :
    rectSeg3 a b d (1/2) = (b : ℂ) + (d : ℂ) * I := by
  simp only [rectSeg3]
  push_cast; ring

private lemma rectSeg3_at_three_quarters (a b d : ℝ) :
    rectSeg3 a b d (3/4) = (a : ℂ) + (d : ℂ) * I := by
  simp only [rectSeg3]
  push_cast; ring

private lemma rectSeg4_at_three_quarters (a c d : ℝ) :
    rectSeg4 a c d (3/4) = (a : ℂ) + (d : ℂ) * I := by
  simp only [rectSeg4]
  push_cast; ring

private lemma rectSeg4_at_one (a c d : ℝ) :
    rectSeg4 a c d 1 = (a : ℂ) + (c : ℂ) * I := by
  simp only [rectSeg4]
  push_cast; ring

lemma rectangleFun_at_zero (a b c d : ℝ) :
    rectangleFun a b c d 0 = (a : ℂ) + (c : ℂ) * I := by
  simp [rectangleFun, rectSeg1_at_zero]

lemma rectangleFun_at_one (a b c d : ℝ) :
    rectangleFun a b c d 1 = (a : ℂ) + (c : ℂ) * I := by
  simp only [rectangleFun, show ¬(1 : ℝ) ≤ 1/4 by norm_num,
    show ¬(1 : ℝ) ≤ 1/2 by norm_num, show ¬(1 : ℝ) ≤ 3/4 by norm_num,
    if_false, rectSeg4_at_one]

lemma rectangleFun_closed (a b c d : ℝ) :
    rectangleFun a b c d 0 = rectangleFun a b c d 1 := by
  rw [rectangleFun_at_zero, rectangleFun_at_one]

/-! ### `ContDiff ℝ ⊤` for each segment -/

private lemma rectSeg1_contDiff (a b c : ℝ) : ContDiff ℝ ⊤ (rectSeg1 a b c) :=
  (contDiff_const.add
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const)).add
      contDiff_const

private lemma rectSeg2_contDiff (b c d : ℝ) : ContDiff ℝ ⊤ (rectSeg2 b c d) :=
  contDiff_const.add
    ((contDiff_const.add
      ((contDiff_const.mul (Complex.ofRealCLM.contDiff.sub contDiff_const)).mul
        contDiff_const)).mul contDiff_const)

private lemma rectSeg3_contDiff (a b d : ℝ) : ContDiff ℝ ⊤ (rectSeg3 a b d) :=
  (contDiff_const.sub
    ((contDiff_const.mul (Complex.ofRealCLM.contDiff.sub contDiff_const)).mul
      contDiff_const)).add contDiff_const

private lemma rectSeg4_contDiff (a c d : ℝ) : ContDiff ℝ ⊤ (rectSeg4 a c d) :=
  contDiff_const.add
    ((contDiff_const.sub
      ((contDiff_const.mul (Complex.ofRealCLM.contDiff.sub contDiff_const)).mul
        contDiff_const)).mul contDiff_const)

private lemma rectSeg1_continuous (a b c : ℝ) : Continuous (rectSeg1 a b c) :=
  (rectSeg1_contDiff a b c).continuous

private lemma rectSeg2_continuous (b c d : ℝ) : Continuous (rectSeg2 b c d) :=
  (rectSeg2_contDiff b c d).continuous

private lemma rectSeg3_continuous (a b d : ℝ) : Continuous (rectSeg3 a b d) :=
  (rectSeg3_contDiff a b d).continuous

private lemma rectSeg4_continuous (a c d : ℝ) : Continuous (rectSeg4 a c d) :=
  (rectSeg4_contDiff a c d).continuous

/-! ### Layered continuity of `rectangleFun` -/

private def rectangleFun_inner34 (a b c d : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 3/4 then rectSeg3 a b d t else rectSeg4 a c d t

private lemma rectangleFun_inner34_continuous (a b c d : ℝ) :
    Continuous (rectangleFun_inner34 a b c d) :=
  Continuous.if_le (rectSeg3_continuous a b d) (rectSeg4_continuous a c d)
    continuous_id continuous_const (fun t (ht : t = 3/4) => by
      subst ht
      rw [rectSeg3_at_three_quarters, rectSeg4_at_three_quarters])

private def rectangleFun_inner234 (a b c d : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 1/2 then rectSeg2 b c d t else rectangleFun_inner34 a b c d t

private lemma rectangleFun_inner234_continuous (a b c d : ℝ) :
    Continuous (rectangleFun_inner234 a b c d) := by
  apply Continuous.if_le (rectSeg2_continuous b c d)
    (rectangleFun_inner34_continuous a b c d) continuous_id continuous_const
  intro t ht
  simp only [id] at ht
  obtain rfl : t = 1/2 := by linarith
  unfold rectangleFun_inner34
  simp only [show (1/2 : ℝ) ≤ 3/4 by norm_num, if_true,
    rectSeg2_at_half, rectSeg3_at_half]

private lemma rectangleFun_eq_layered (a b c d : ℝ) (t : ℝ) :
    rectangleFun a b c d t =
      (if t ≤ 1/4 then rectSeg1 a b c t else rectangleFun_inner234 a b c d t) := by
  unfold rectangleFun rectangleFun_inner234 rectangleFun_inner34
  split_ifs <;> rfl

@[fun_prop]
theorem rectangleFun_continuous (a b c d : ℝ) :
    Continuous (rectangleFun a b c d) := by
  rw [show rectangleFun a b c d =
    (fun t => if t ≤ 1/4 then rectSeg1 a b c t else rectangleFun_inner234 a b c d t) from
    funext (rectangleFun_eq_layered a b c d)]
  apply Continuous.if_le (rectSeg1_continuous a b c)
    (rectangleFun_inner234_continuous a b c d) continuous_id continuous_const
  intro t ht
  simp only [id] at ht
  obtain rfl : t = 1/4 := by linarith
  unfold rectangleFun_inner234
  simp only [show (1/4 : ℝ) ≤ 1/2 by norm_num, if_true,
    rectSeg1_at_quarter, rectSeg2_at_quarter]

/-! ### Eventual-equality lemmas to each segment -/

private lemma rectangleFun_eventuallyEq_seg1 (a b c d : ℝ) {t : ℝ} (ht1 : t < 1/4) :
    rectangleFun a b c d =ᶠ[𝓝 t] rectSeg1 a b c :=
  Filter.eventually_of_mem (Iio_mem_nhds ht1) fun s (hs : s < 1/4) => by
    simp only [rectangleFun, if_pos hs.le]

private lemma rectangleFun_eventuallyEq_seg2 (a b c d : ℝ) {t : ℝ}
    (ht1 : 1/4 < t) (ht2 : t < 1/2) :
    rectangleFun a b c d =ᶠ[𝓝 t] rectSeg2 b c d :=
  Filter.eventually_of_mem
    (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht2))
    fun s ⟨hs1, hs2⟩ => by
      simp only [rectangleFun,
        show ¬s ≤ 1/4 from not_le.mpr hs1,
        show s ≤ 1/2 from le_of_lt hs2, if_true, if_false]

private lemma rectangleFun_eventuallyEq_seg3 (a b c d : ℝ) {t : ℝ}
    (ht2 : 1/2 < t) (ht3 : t < 3/4) :
    rectangleFun a b c d =ᶠ[𝓝 t] rectSeg3 a b d :=
  Filter.eventually_of_mem
    (Filter.inter_mem (Ioi_mem_nhds ht2) (Iio_mem_nhds ht3))
    fun s ⟨hs2, hs3⟩ => by
      simp only [rectangleFun,
        show ¬s ≤ 1/4 from not_le.mpr (lt_trans (by norm_num : (1:ℝ)/4 < 1/2) hs2),
        show ¬s ≤ 1/2 from not_le.mpr hs2,
        show s ≤ 3/4 from le_of_lt hs3, if_true, if_false]

private lemma rectangleFun_eventuallyEq_seg4 (a b c d : ℝ) {t : ℝ}
    (ht3 : 3/4 < t) :
    rectangleFun a b c d =ᶠ[𝓝 t] rectSeg4 a c d :=
  Filter.eventually_of_mem (Ioi_mem_nhds ht3) fun s (hs3 : 3/4 < s) => by
    simp only [rectangleFun,
      show ¬s ≤ 1/4 from not_le.mpr (lt_trans (by norm_num : (1:ℝ)/4 < 3/4) hs3),
      show ¬s ≤ 1/2 from not_le.mpr (lt_trans (by norm_num : (1:ℝ)/2 < 3/4) hs3),
      show ¬s ≤ 3/4 from not_le.mpr hs3, if_false]

/-! ### Partition and differentiability off-partition -/

/-- The interior partition points for `rectangleFun`: `{1/4, 1/2, 3/4}`. -/
def rectanglePartition : Finset ℝ := {1/4, 1/2, 3/4}

lemma rectanglePartition_subset_Ioo :
    (rectanglePartition : Set ℝ) ⊆ Ioo 0 1 := by
  intro x hx
  simp only [rectanglePartition, Finset.coe_insert, Finset.coe_singleton,
    mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩

/-- The closed partition `{0, 1/4, 1/2, 3/4, 1}`. -/
def rectangleClosedPartition : Finset ℝ := {0, 1/4, 1/2, 3/4, 1}

lemma rectangleClosedPartition_subset_Icc :
    (rectangleClosedPartition : Set ℝ) ⊆ Icc 0 1 := by
  intro x hx
  simp only [rectangleClosedPartition, Finset.coe_insert, Finset.coe_singleton,
    mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩

lemma rectangleClosedPartition_eq :
    rectangleClosedPartition = insert 0 (insert 1 rectanglePartition) := by
  ext x
  simp only [rectangleClosedPartition, rectanglePartition, Finset.mem_insert,
    Finset.mem_singleton]
  tauto

private lemma rectangleFun_differentiableAt_off (a b c d : ℝ) (t : ℝ)
    (_ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ rectanglePartition) :
    DifferentiableAt ℝ (rectangleFun a b c d) t := by
  simp only [rectanglePartition, Finset.mem_insert, Finset.mem_singleton] at htp
  push Not at htp
  obtain ⟨ht1, ht2, ht3⟩ := htp
  have hT : (⊤ : WithTop ℕ∞) ≠ 0 := WithTop.top_ne_zero
  rcases lt_or_gt_of_ne ht1 with h1 | h1
  · exact ((rectSeg1_contDiff a b c).differentiable hT).differentiableAt.congr_of_eventuallyEq
      (rectangleFun_eventuallyEq_seg1 a b c d h1)
  rcases lt_or_gt_of_ne ht2 with h2 | h2
  · exact ((rectSeg2_contDiff b c d).differentiable hT).differentiableAt.congr_of_eventuallyEq
      (rectangleFun_eventuallyEq_seg2 a b c d h1 h2)
  rcases lt_or_gt_of_ne ht3 with h3 | h3
  · exact ((rectSeg3_contDiff a b d).differentiable hT).differentiableAt.congr_of_eventuallyEq
      (rectangleFun_eventuallyEq_seg3 a b c d h2 h3)
  exact ((rectSeg4_contDiff a c d).differentiable hT).differentiableAt.congr_of_eventuallyEq
    (rectangleFun_eventuallyEq_seg4 a b c d h3)

private lemma rectangleFun_deriv_continuousAt_off (a b c d : ℝ) (t : ℝ)
    (_ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ rectanglePartition) :
    ContinuousAt (deriv (rectangleFun a b c d)) t := by
  simp only [rectanglePartition, Finset.mem_insert, Finset.mem_singleton] at htp
  push Not at htp
  obtain ⟨ht1, ht2, ht3⟩ := htp
  rcases lt_or_gt_of_ne ht1 with h1 | h1
  · exact (continuousAt_congr (rectangleFun_eventuallyEq_seg1 a b c d h1).deriv).mpr
      ((rectSeg1_contDiff a b c).continuous_deriv le_top).continuousAt
  rcases lt_or_gt_of_ne ht2 with h2 | h2
  · exact (continuousAt_congr (rectangleFun_eventuallyEq_seg2 a b c d h1 h2).deriv).mpr
      ((rectSeg2_contDiff b c d).continuous_deriv le_top).continuousAt
  rcases lt_or_gt_of_ne ht3 with h3 | h3
  · exact (continuousAt_congr (rectangleFun_eventuallyEq_seg3 a b c d h2 h3).deriv).mpr
      ((rectSeg3_contDiff a b d).continuous_deriv le_top).continuousAt
  exact (continuousAt_congr (rectangleFun_eventuallyEq_seg4 a b c d h3).deriv).mpr
    ((rectSeg4_contDiff a c d).continuous_deriv le_top).continuousAt

/-! ### The `Path` and `PiecewiseC1Path` instances -/

/-- The rectangular boundary as a mathlib `Path` from the bottom-left corner back
to itself. -/
def rectanglePath (a b c d : ℝ) :
    Path ((a : ℂ) + (c : ℂ) * I) ((a : ℂ) + (c : ℂ) * I) where
  toFun t := rectangleFun a b c d t
  continuous_toFun := (rectangleFun_continuous a b c d).continuousOn.restrict
  source' := rectangleFun_at_zero a b c d
  target' := rectangleFun_at_one a b c d

private lemma rectanglePath_extend_eq (a b c d : ℝ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (rectanglePath a b c d).extend t = rectangleFun a b c d t :=
  Path.extend_apply _ ht

private lemma rectanglePath_extend_eventuallyEq (a b c d : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (rectanglePath a b c d).extend =ᶠ[𝓝 t] rectangleFun a b c d :=
  Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs =>
    rectanglePath_extend_eq a b c d s (Ioo_subset_Icc_self hs)

private lemma rectanglePath_differentiableAt_off (a b c d : ℝ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ rectanglePartition) :
    DifferentiableAt ℝ (rectanglePath a b c d).extend t :=
  (rectangleFun_differentiableAt_off a b c d t ht htp).congr_of_eventuallyEq
    (rectanglePath_extend_eventuallyEq a b c d ht)

private lemma rectanglePath_deriv_continuousAt_off (a b c d : ℝ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ rectanglePartition) :
    ContinuousAt (deriv (rectanglePath a b c d).extend) t :=
  (continuousAt_congr (rectanglePath_extend_eventuallyEq a b c d ht).deriv).mpr
    (rectangleFun_deriv_continuousAt_off a b c d t ht htp)

/-- The rectangular boundary as a `PiecewiseC1Path`. -/
def rectanglePC1Path (a b c d : ℝ) :
    PiecewiseC1Path ((a : ℂ) + (c : ℂ) * I) ((a : ℂ) + (c : ℂ) * I) where
  toFun := (rectanglePath a b c d).extend
  source := (rectanglePath a b c d).extend_zero
  target := (rectanglePath a b c d).extend_one
  continuous_toFun := (rectanglePath a b c d).continuous_extend.continuousOn
  toPath := rectanglePath a b c d
  toPath_extend_eq_toFun := fun _ _ => rfl
  partition := rectanglePartition
  partition_subset := rectanglePartition_subset_Ioo
  differentiable_off := rectanglePath_differentiableAt_off a b c d
  deriv_continuous_off := rectanglePath_deriv_continuousAt_off a b c d

/-! ### Identifying consecutive pairs of the closed partition

The closed partition `{0, 1/4, 1/2, 3/4, 1}` has exactly four consecutive pairs:
`(0, 1/4)`, `(1/4, 1/2)`, `(1/2, 3/4)`, `(3/4, 1)`. We case-split on these in
order to provide `contDiffOn_pieces` and `derivWithin_ne_zero_pieces`. -/

private lemma rectangleClosedPartition_consecutive_cases {p q : ℝ}
    (h : rectangleClosedPartition.IsConsecutive p q) :
    (p = 0 ∧ q = 1/4) ∨ (p = 1/4 ∧ q = 1/2) ∨ (p = 1/2 ∧ q = 3/4) ∨ (p = 3/4 ∧ q = 1) := by
  obtain ⟨hp, hq, hpq, hno⟩ := h
  simp only [rectangleClosedPartition, Finset.mem_insert, Finset.mem_singleton] at hp hq
  -- Forbid any element strictly between p and q.
  have ban : ∀ r ∈ ({0, 1/4, 1/2, 3/4, 1} : Finset ℝ), ¬ (p < r ∧ r < q) := by
    intro r hr ⟨hr1, hr2⟩
    exact hno r hr ⟨hr1, hr2⟩
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact absurd hpq (by norm_num)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact absurd (ban (1/4) (by simp)
        ⟨by norm_num, by norm_num⟩) (by tauto)
    · exact absurd (ban (1/4) (by simp)
        ⟨by norm_num, by norm_num⟩) (by tauto)
    · exact absurd (ban (1/4) (by simp)
        ⟨by norm_num, by norm_num⟩) (by tauto)
  · rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact absurd hpq (by norm_num)
    · exact absurd hpq (by norm_num)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact absurd (ban (1/2) (by simp)
        ⟨by norm_num, by norm_num⟩) (by tauto)
    · exact absurd (ban (1/2) (by simp)
        ⟨by norm_num, by norm_num⟩) (by tauto)
  · rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact absurd hpq (by norm_num)
    · exact absurd hpq (by norm_num)
    · exact absurd hpq (by norm_num)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact absurd (ban (3/4) (by simp)
        ⟨by norm_num, by norm_num⟩) (by tauto)
  · rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact absurd hpq (by norm_num)
    · exact absurd hpq (by norm_num)
    · exact absurd hpq (by norm_num)
    · exact absurd hpq (by norm_num)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals exact absurd hpq (by norm_num)

/-! ### Each closed-piece restriction equals a segment

On each of the four closed sub-intervals, `(rectanglePath a b c d).extend` agrees
with the corresponding analytically-defined segment function. -/

private lemma rectangleFun_eq_seg1_on_Icc (a b c d : ℝ) :
    EqOn (rectangleFun a b c d) (rectSeg1 a b c) (Icc 0 (1/4 : ℝ)) := by
  intro t ht
  simp only [rectangleFun, if_pos ht.2]

private lemma rectangleFun_eq_seg2_on_Icc (a b c d : ℝ) :
    EqOn (rectangleFun a b c d) (rectSeg2 b c d) (Icc (1/4 : ℝ) (1/2)) := by
  intro t ht
  by_cases h_eq : t = 1/4
  · subst h_eq
    simp only [rectangleFun, le_refl, if_true]
    rw [rectSeg1_at_quarter, rectSeg2_at_quarter]
  · have ht1 : ¬ t ≤ 1/4 := not_le.mpr (lt_of_le_of_ne ht.1 (Ne.symm h_eq))
    simp only [rectangleFun, if_neg ht1, if_pos ht.2]

private lemma rectangleFun_eq_seg3_on_Icc (a b c d : ℝ) :
    EqOn (rectangleFun a b c d) (rectSeg3 a b d) (Icc (1/2 : ℝ) (3/4)) := by
  intro t ht
  by_cases h_eq : t = 1/2
  · subst h_eq
    simp only [rectangleFun, show ¬(1/2 : ℝ) ≤ 1/4 by norm_num, le_refl,
      if_true, if_false]
    rw [rectSeg2_at_half, rectSeg3_at_half]
  · have ht2 : ¬ t ≤ 1/2 := not_le.mpr (lt_of_le_of_ne ht.1 (Ne.symm h_eq))
    have ht1 : ¬ t ≤ 1/4 := not_le.mpr (lt_trans (by norm_num : (1:ℝ)/4 < 1/2)
      (not_le.mp ht2))
    simp only [rectangleFun, if_neg ht1, if_neg ht2, if_pos ht.2]

private lemma rectangleFun_eq_seg4_on_Icc (a b c d : ℝ) :
    EqOn (rectangleFun a b c d) (rectSeg4 a c d) (Icc (3/4 : ℝ) 1) := by
  intro t ht
  by_cases h_eq : t = 3/4
  · subst h_eq
    simp only [rectangleFun, show ¬(3/4 : ℝ) ≤ 1/4 by norm_num,
      show ¬(3/4 : ℝ) ≤ 1/2 by norm_num, le_refl, if_true, if_false]
    rw [rectSeg3_at_three_quarters, rectSeg4_at_three_quarters]
  · have ht3 : ¬ t ≤ 3/4 := not_le.mpr (lt_of_le_of_ne ht.1 (Ne.symm h_eq))
    have ht1 : ¬ t ≤ 1/4 := not_le.mpr (lt_trans (by norm_num : (1:ℝ)/4 < 3/4)
      (lt_of_le_of_ne ht.1 (Ne.symm h_eq)))
    have ht2 : ¬ t ≤ 1/2 := not_le.mpr (lt_trans (by norm_num : (1:ℝ)/2 < 3/4)
      (lt_of_le_of_ne ht.1 (Ne.symm h_eq)))
    simp only [rectangleFun, if_neg ht1, if_neg ht2, if_neg ht3]

private lemma rectanglePath_extend_eq_seg1_on_Icc (a b c d : ℝ) :
    EqOn (rectanglePath a b c d).extend (rectSeg1 a b c) (Icc 0 (1/4 : ℝ)) := fun t ht => by
  have hIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  rw [rectanglePath_extend_eq a b c d t hIcc, rectangleFun_eq_seg1_on_Icc a b c d ht]

private lemma rectanglePath_extend_eq_seg2_on_Icc (a b c d : ℝ) :
    EqOn (rectanglePath a b c d).extend (rectSeg2 b c d) (Icc (1/4 : ℝ) (1/2)) :=
  fun t ht => by
    have hIcc : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [rectanglePath_extend_eq a b c d t hIcc, rectangleFun_eq_seg2_on_Icc a b c d ht]

private lemma rectanglePath_extend_eq_seg3_on_Icc (a b c d : ℝ) :
    EqOn (rectanglePath a b c d).extend (rectSeg3 a b d) (Icc (1/2 : ℝ) (3/4)) :=
  fun t ht => by
    have hIcc : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [rectanglePath_extend_eq a b c d t hIcc, rectangleFun_eq_seg3_on_Icc a b c d ht]

private lemma rectanglePath_extend_eq_seg4_on_Icc (a b c d : ℝ) :
    EqOn (rectanglePath a b c d).extend (rectSeg4 a c d) (Icc (3/4 : ℝ) 1) :=
  fun t ht => by
    have hIcc : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    rw [rectanglePath_extend_eq a b c d t hIcc, rectangleFun_eq_seg4_on_Icc a b c d ht]

/-! ### Derivatives of each segment

Each segment is affine-linear in `t`, so its derivative is the constant
"velocity" complex number. -/

private lemma rectSeg1_hasDerivAt (a b c : ℝ) (t : ℝ) :
    HasDerivAt (rectSeg1 a b c) (4 * ((b : ℂ) - a)) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ))) (1 : ℂ) t :=
    Complex.ofRealCLM.hasDerivAt
  -- f(t) = a + 4*t*(b - a) + c*I
  -- The chunk in the middle is `4 * (s : ℂ) * (b - a)`
  have h_mid : HasDerivAt (fun s : ℝ => (4 : ℂ) * (s : ℂ) * ((b : ℂ) - a))
      (4 * ((b : ℂ) - a)) t := by
    have := (h1.const_mul (4 : ℂ)).mul_const ((b : ℂ) - a)
    simpa using this
  -- Now `a + (...) + c*I`
  have h_outer : HasDerivAt
      (fun s : ℝ => (a : ℂ) + (4 : ℂ) * (s : ℂ) * ((b : ℂ) - a) + (c : ℂ) * I)
      (4 * ((b : ℂ) - a)) t := by
    have := ((hasDerivAt_const t ((a : ℂ))).add h_mid).add_const ((c : ℂ) * I)
    simpa using this
  exact h_outer

private lemma rectSeg1_deriv (a b c : ℝ) (t : ℝ) :
    deriv (rectSeg1 a b c) t = 4 * ((b : ℂ) - a) :=
  (rectSeg1_hasDerivAt a b c t).deriv

private lemma rectSeg2_hasDerivAt (b c d : ℝ) (t : ℝ) :
    HasDerivAt (rectSeg2 b c d) (4 * ((d : ℂ) - c) * I) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ))) (1 : ℂ) t :=
    Complex.ofRealCLM.hasDerivAt
  have h_mid : HasDerivAt (fun s : ℝ => (4 : ℂ) * ((s : ℂ) - 1/4) * ((d : ℂ) - c))
      (4 * ((d : ℂ) - c)) t := by
    have := ((h1.sub_const ((1 : ℂ)/4)).const_mul (4 : ℂ)).mul_const ((d : ℂ) - c)
    simpa using this
  have h_inner : HasDerivAt
      (fun s : ℝ => (c : ℂ) + (4 : ℂ) * ((s : ℂ) - 1/4) * ((d : ℂ) - c))
      (4 * ((d : ℂ) - c)) t := by
    have h := (hasDerivAt_const t ((c : ℂ))).add h_mid
    convert h using 1; ring
  have h_imag : HasDerivAt
      (fun s : ℝ => ((c : ℂ) + (4 : ℂ) * ((s : ℂ) - 1/4) * ((d : ℂ) - c)) * I)
      (4 * ((d : ℂ) - c) * I) t := h_inner.mul_const I
  have h_outer : HasDerivAt
      (fun s : ℝ => (b : ℂ) + ((c : ℂ) + (4 : ℂ) * ((s : ℂ) - 1/4) * ((d : ℂ) - c)) * I)
      (4 * ((d : ℂ) - c) * I) t := by
    have h := (hasDerivAt_const t ((b : ℂ))).add h_imag
    convert h using 1; ring
  exact h_outer

private lemma rectSeg2_deriv (b c d : ℝ) (t : ℝ) :
    deriv (rectSeg2 b c d) t = 4 * ((d : ℂ) - c) * I :=
  (rectSeg2_hasDerivAt b c d t).deriv

private lemma rectSeg3_hasDerivAt (a b d : ℝ) (t : ℝ) :
    HasDerivAt (rectSeg3 a b d) (-(4 * ((b : ℂ) - a))) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ))) (1 : ℂ) t :=
    Complex.ofRealCLM.hasDerivAt
  have h_mid : HasDerivAt (fun s : ℝ => (4 : ℂ) * ((s : ℂ) - 1/2) * ((b : ℂ) - a))
      (4 * ((b : ℂ) - a)) t := by
    have := ((h1.sub_const ((1 : ℂ)/2)).const_mul (4 : ℂ)).mul_const ((b : ℂ) - a)
    simpa using this
  have h_real : HasDerivAt
      (fun s : ℝ => (b : ℂ) - (4 : ℂ) * ((s : ℂ) - 1/2) * ((b : ℂ) - a))
      (-(4 * ((b : ℂ) - a))) t := by
    have := (hasDerivAt_const t ((b : ℂ))).sub h_mid
    convert this using 1; ring
  have h_outer : HasDerivAt
      (fun s : ℝ => ((b : ℂ) - (4 : ℂ) * ((s : ℂ) - 1/2) * ((b : ℂ) - a)) + (d : ℂ) * I)
      (-(4 * ((b : ℂ) - a))) t := by
    have := h_real.add_const ((d : ℂ) * I)
    simpa using this
  exact h_outer

private lemma rectSeg3_deriv (a b d : ℝ) (t : ℝ) :
    deriv (rectSeg3 a b d) t = -(4 * ((b : ℂ) - a)) :=
  (rectSeg3_hasDerivAt a b d t).deriv

private lemma rectSeg4_hasDerivAt (a c d : ℝ) (t : ℝ) :
    HasDerivAt (rectSeg4 a c d) (-(4 * ((d : ℂ) - c)) * I) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ))) (1 : ℂ) t :=
    Complex.ofRealCLM.hasDerivAt
  have h_mid : HasDerivAt (fun s : ℝ => (4 : ℂ) * ((s : ℂ) - 3/4) * ((d : ℂ) - c))
      (4 * ((d : ℂ) - c)) t := by
    have := ((h1.sub_const ((3 : ℂ)/4)).const_mul (4 : ℂ)).mul_const ((d : ℂ) - c)
    simpa using this
  have h_inner : HasDerivAt
      (fun s : ℝ => (d : ℂ) - (4 : ℂ) * ((s : ℂ) - 3/4) * ((d : ℂ) - c))
      (-(4 * ((d : ℂ) - c))) t := by
    have h := (hasDerivAt_const t ((d : ℂ))).sub h_mid
    convert h using 1; ring
  have h_imag : HasDerivAt
      (fun s : ℝ => ((d : ℂ) - (4 : ℂ) * ((s : ℂ) - 3/4) * ((d : ℂ) - c)) * I)
      (-(4 * ((d : ℂ) - c)) * I) t := h_inner.mul_const I
  have h_outer : HasDerivAt
      (fun s : ℝ => (a : ℂ) + ((d : ℂ) - (4 : ℂ) * ((s : ℂ) - 3/4) * ((d : ℂ) - c)) * I)
      (-(4 * ((d : ℂ) - c)) * I) t := by
    have h := (hasDerivAt_const t ((a : ℂ))).add h_imag
    convert h using 1; ring
  exact h_outer

private lemma rectSeg4_deriv (a c d : ℝ) (t : ℝ) :
    deriv (rectSeg4 a c d) t = -(4 * ((d : ℂ) - c)) * I :=
  (rectSeg4_hasDerivAt a c d t).deriv

/-! ### `ContDiffOn ℝ 1` of `(rectanglePath a b c d).extend` on each closed piece -/

private lemma rectanglePath_extend_contDiffOn_seg1 (a b c d : ℝ) :
    ContDiffOn ℝ 1 (rectanglePath a b c d).extend (Icc 0 (1/4 : ℝ)) :=
  (((rectSeg1_contDiff a b c).of_le le_top).contDiffOn).congr fun _ ht =>
    rectanglePath_extend_eq_seg1_on_Icc a b c d ht

private lemma rectanglePath_extend_contDiffOn_seg2 (a b c d : ℝ) :
    ContDiffOn ℝ 1 (rectanglePath a b c d).extend (Icc (1/4 : ℝ) (1/2)) :=
  (((rectSeg2_contDiff b c d).of_le le_top).contDiffOn).congr fun _ ht =>
    rectanglePath_extend_eq_seg2_on_Icc a b c d ht

private lemma rectanglePath_extend_contDiffOn_seg3 (a b c d : ℝ) :
    ContDiffOn ℝ 1 (rectanglePath a b c d).extend (Icc (1/2 : ℝ) (3/4)) :=
  (((rectSeg3_contDiff a b d).of_le le_top).contDiffOn).congr fun _ ht =>
    rectanglePath_extend_eq_seg3_on_Icc a b c d ht

private lemma rectanglePath_extend_contDiffOn_seg4 (a b c d : ℝ) :
    ContDiffOn ℝ 1 (rectanglePath a b c d).extend (Icc (3/4 : ℝ) 1) :=
  (((rectSeg4_contDiff a c d).of_le le_top).contDiffOn).congr fun _ ht =>
    rectanglePath_extend_eq_seg4_on_Icc a b c d ht

/-! ### `derivWithin` on each closed piece

We compute the within-derivative of `(rectanglePath a b c d).extend` on each
closed sub-interval. Each is the constant complex "velocity" of the
corresponding side: `4(b-a)`, `4i(d-c)`, `-4(b-a)`, `-4i(d-c)`. -/

private lemma rectanglePath_extend_eventuallyEq_seg1_nhdsWithin (a b c d : ℝ) {t : ℝ}
    (_ht : t ∈ Icc (0 : ℝ) (1/4)) :
    (rectanglePath a b c d).extend =ᶠ[𝓝[Icc (0 : ℝ) (1/4)] t] rectSeg1 a b c :=
  Filter.eventually_of_mem self_mem_nhdsWithin (rectanglePath_extend_eq_seg1_on_Icc a b c d)

private lemma rectanglePath_extend_eventuallyEq_seg2_nhdsWithin (a b c d : ℝ) {t : ℝ}
    (_ht : t ∈ Icc (1/4 : ℝ) (1/2)) :
    (rectanglePath a b c d).extend =ᶠ[𝓝[Icc (1/4 : ℝ) (1/2)] t] rectSeg2 b c d :=
  Filter.eventually_of_mem self_mem_nhdsWithin (rectanglePath_extend_eq_seg2_on_Icc a b c d)

private lemma rectanglePath_extend_eventuallyEq_seg3_nhdsWithin (a b c d : ℝ) {t : ℝ}
    (_ht : t ∈ Icc (1/2 : ℝ) (3/4)) :
    (rectanglePath a b c d).extend =ᶠ[𝓝[Icc (1/2 : ℝ) (3/4)] t] rectSeg3 a b d :=
  Filter.eventually_of_mem self_mem_nhdsWithin (rectanglePath_extend_eq_seg3_on_Icc a b c d)

private lemma rectanglePath_extend_eventuallyEq_seg4_nhdsWithin (a b c d : ℝ) {t : ℝ}
    (_ht : t ∈ Icc (3/4 : ℝ) 1) :
    (rectanglePath a b c d).extend =ᶠ[𝓝[Icc (3/4 : ℝ) 1] t] rectSeg4 a c d :=
  Filter.eventually_of_mem self_mem_nhdsWithin (rectanglePath_extend_eq_seg4_on_Icc a b c d)

private lemma rectanglePath_extend_derivWithin_seg1 (a b c d : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (1/4)) :
    derivWithin (rectanglePath a b c d).extend (Icc (0 : ℝ) (1/4)) t = 4 * ((b : ℂ) - a) := by
  have h_seg : HasDerivWithinAt (rectSeg1 a b c) (4 * ((b : ℂ) - a)) (Icc (0 : ℝ) (1/4)) t :=
    (rectSeg1_hasDerivAt a b c t).hasDerivWithinAt
  have h_path : HasDerivWithinAt (rectanglePath a b c d).extend
      (4 * ((b : ℂ) - a)) (Icc (0 : ℝ) (1/4)) t :=
    h_seg.congr_of_eventuallyEq
      (rectanglePath_extend_eventuallyEq_seg1_nhdsWithin a b c d ht)
      (rectanglePath_extend_eq_seg1_on_Icc a b c d ht)
  have hUDiff : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) (1/4)) t :=
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1/4)) t ht
  exact h_path.derivWithin hUDiff

private lemma rectanglePath_extend_derivWithin_seg2 (a b c d : ℝ) {t : ℝ}
    (ht : t ∈ Icc (1/4 : ℝ) (1/2)) :
    derivWithin (rectanglePath a b c d).extend (Icc (1/4 : ℝ) (1/2)) t =
      4 * ((d : ℂ) - c) * I := by
  have h_seg : HasDerivWithinAt (rectSeg2 b c d) (4 * ((d : ℂ) - c) * I)
      (Icc (1/4 : ℝ) (1/2)) t :=
    (rectSeg2_hasDerivAt b c d t).hasDerivWithinAt
  have h_path : HasDerivWithinAt (rectanglePath a b c d).extend
      (4 * ((d : ℂ) - c) * I) (Icc (1/4 : ℝ) (1/2)) t :=
    h_seg.congr_of_eventuallyEq
      (rectanglePath_extend_eventuallyEq_seg2_nhdsWithin a b c d ht)
      (rectanglePath_extend_eq_seg2_on_Icc a b c d ht)
  have hUDiff : UniqueDiffWithinAt ℝ (Icc (1/4 : ℝ) (1/2)) t :=
    (uniqueDiffOn_Icc (by norm_num : (1/4 : ℝ) < 1/2)) t ht
  exact h_path.derivWithin hUDiff

private lemma rectanglePath_extend_derivWithin_seg3 (a b c d : ℝ) {t : ℝ}
    (ht : t ∈ Icc (1/2 : ℝ) (3/4)) :
    derivWithin (rectanglePath a b c d).extend (Icc (1/2 : ℝ) (3/4)) t =
      -(4 * ((b : ℂ) - a)) := by
  have h_seg : HasDerivWithinAt (rectSeg3 a b d) (-(4 * ((b : ℂ) - a)))
      (Icc (1/2 : ℝ) (3/4)) t :=
    (rectSeg3_hasDerivAt a b d t).hasDerivWithinAt
  have h_path : HasDerivWithinAt (rectanglePath a b c d).extend
      (-(4 * ((b : ℂ) - a))) (Icc (1/2 : ℝ) (3/4)) t :=
    h_seg.congr_of_eventuallyEq
      (rectanglePath_extend_eventuallyEq_seg3_nhdsWithin a b c d ht)
      (rectanglePath_extend_eq_seg3_on_Icc a b c d ht)
  have hUDiff : UniqueDiffWithinAt ℝ (Icc (1/2 : ℝ) (3/4)) t :=
    (uniqueDiffOn_Icc (by norm_num : (1/2 : ℝ) < 3/4)) t ht
  exact h_path.derivWithin hUDiff

private lemma rectanglePath_extend_derivWithin_seg4 (a b c d : ℝ) {t : ℝ}
    (ht : t ∈ Icc (3/4 : ℝ) 1) :
    derivWithin (rectanglePath a b c d).extend (Icc (3/4 : ℝ) 1) t =
      -(4 * ((d : ℂ) - c)) * I := by
  have h_seg : HasDerivWithinAt (rectSeg4 a c d) (-(4 * ((d : ℂ) - c)) * I)
      (Icc (3/4 : ℝ) 1) t :=
    (rectSeg4_hasDerivAt a c d t).hasDerivWithinAt
  have h_path : HasDerivWithinAt (rectanglePath a b c d).extend
      (-(4 * ((d : ℂ) - c)) * I) (Icc (3/4 : ℝ) 1) t :=
    h_seg.congr_of_eventuallyEq
      (rectanglePath_extend_eventuallyEq_seg4_nhdsWithin a b c d ht)
      (rectanglePath_extend_eq_seg4_on_Icc a b c d ht)
  have hUDiff : UniqueDiffWithinAt ℝ (Icc (3/4 : ℝ) 1) t :=
    (uniqueDiffOn_Icc (by norm_num : (3/4 : ℝ) < 1)) t ht
  exact h_path.derivWithin hUDiff

/-! ### Building the `ClosedPwC1Immersion` -/

/-- **The rectangular contour** as a `ClosedPwC1Immersion`. Starts at the
bottom-left corner `a + c·I` and traverses the boundary counterclockwise:
bottom → right → top → left.

The parametrisation has breakpoints `{1/4, 1/2, 3/4}` in `(0, 1)` and is
`C¹` on each closed piece with non-vanishing derivative. -/
noncomputable def rectangleContour
    (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    ClosedPwC1Immersion ((a : ℂ) + (c : ℂ) * I) where
  toPiecewiseC1Path := rectanglePC1Path a b c d
  closedPartition := rectangleClosedPartition
  zero_mem_closedPartition := by simp [rectangleClosedPartition]
  one_mem_closedPartition := by simp [rectangleClosedPartition]
  closedPartition_subset := rectangleClosedPartition_subset_Icc
  closedPartition_eq := rectangleClosedPartition_eq
  contDiffOn_pieces := by
    intro p q hcons
    show ContDiffOn ℝ 1 (rectanglePath a b c d).extend (Icc p q)
    rcases rectangleClosedPartition_consecutive_cases hcons with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact rectanglePath_extend_contDiffOn_seg1 a b c d
    · exact rectanglePath_extend_contDiffOn_seg2 a b c d
    · exact rectanglePath_extend_contDiffOn_seg3 a b c d
    · exact rectanglePath_extend_contDiffOn_seg4 a b c d
  derivWithin_ne_zero_pieces := by
    intro p q hcons t ht
    have hb_ne_a : (b : ℂ) - (a : ℂ) ≠ 0 := sub_ne_zero.mpr (Complex.ofReal_injective.ne hab.ne')
    have hd_ne_c : (d : ℂ) - (c : ℂ) ≠ 0 := sub_ne_zero.mpr (Complex.ofReal_injective.ne hcd.ne')
    have h_I_ne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
    have h_4_ne : (4 : ℂ) ≠ 0 := by norm_num
    -- The toPath of `rectanglePC1Path` is `rectanglePath` by definition.
    show derivWithin (rectanglePath a b c d).extend (Icc p q) t ≠ 0
    rcases rectangleClosedPartition_consecutive_cases hcons with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [rectanglePath_extend_derivWithin_seg1 a b c d ht]
      exact mul_ne_zero h_4_ne hb_ne_a
    · rw [rectanglePath_extend_derivWithin_seg2 a b c d ht]
      exact mul_ne_zero (mul_ne_zero h_4_ne hd_ne_c) h_I_ne
    · rw [rectanglePath_extend_derivWithin_seg3 a b c d ht]
      exact neg_ne_zero.mpr (mul_ne_zero h_4_ne hb_ne_a)
    · rw [rectanglePath_extend_derivWithin_seg4 a b c d ht]
      exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero h_4_ne hd_ne_c)) h_I_ne

/-! ## Null-homologous from convex open set -/

/-- Auxiliary: every continuous `ℝ`-linear functional `f : ℂ →L[ℝ] ℝ` has the
form `f w = Re (α * w)` for `α = ⟨f 1, -(f I)⟩ : ℂ`. -/
private lemma realCLM_eq_re_mul {f : ℂ →L[ℝ] ℝ} (w : ℂ) :
    f w = ((Complex.mk (f 1) (-(f I))) * w).re := by
  have hf_decomp : f w = w.re * f 1 + w.im * f I := by
    have h_decomp : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I := by
      simp [Complex.real_smul]
    conv_lhs => rw [h_decomp]
    rw [map_add, map_smul, map_smul]
    simp [smul_eq_mul]
  rw [hf_decomp, Complex.mul_re]
  simp; ring

/-- Auxiliary: if `f z < f w` for some `w`, the complex direction
`⟨f 1, -(f I)⟩` is nonzero. -/
private lemma realCLM_dir_ne_zero {f : ℂ →L[ℝ] ℝ} {z w : ℂ} (h : f z < f w) :
    Complex.mk (f 1) (-(f I)) ≠ 0 := by
  intro hα
  rw [Complex.ext_iff] at hα
  simp at hα
  obtain ⟨h1, hI⟩ := hα
  have hf_zero : ∀ u : ℂ, f u = 0 := fun u => by
    rw [realCLM_eq_re_mul u, h1, hI]
    simp
  rw [hf_zero w, hf_zero z] at h
  exact lt_irrefl _ h

/-- Auxiliary: on the open half-plane where `Re(α * (u - z)) > 0`, the function
`u ↦ Complex.log(α * (u - z))` is a holomorphic primitive of `u ↦ (u - z)⁻¹`. -/
private lemma hasDerivAt_log_mul_sub_const {α z : ℂ} (hα : α ≠ 0) {w : ℂ}
    (h : 0 < (α * (w - z)).re) :
    HasDerivAt (fun u => Complex.log (α * (u - z))) (w - z)⁻¹ w := by
  have hα_wz_slit : α * (w - z) ∈ slitPlane := Or.inl h
  have h_inner : HasDerivAt (fun u => α * (u - z)) α w := by
    have h1 : HasDerivAt (fun u : ℂ => u - z) 1 w := (hasDerivAt_id w).sub_const z
    simpa using h1.const_mul α
  have h_log : HasDerivAt (fun u => Complex.log (α * (u - z)))
      (α / (α * (w - z))) w :=
    h_inner.clog hα_wz_slit
  convert h_log using 1
  field_simp

/-- Every closed pw-C¹ immersion whose image lies in a convex open subset of `ℂ`
is null-homologous there.

**Proof.** For a point `z` outside the convex open set `U`, geometric
Hahn–Banach (`geometric_hahn_banach_point_open`) produces an `ℝ`-linear
functional `f : ℂ →L[ℝ] ℝ` with `f z < f w` for every `w ∈ U`. Writing
`f` as `Re (α * ·)` for some `α ≠ 0` (since `f` is nontrivial), we conclude
that the open half-plane `H := {w | 0 < Re (α * (w - z))}` contains the
image of `γ` but not `z`. On `H` the function `w ↦ Complex.log (α * (w - z))`
is a holomorphic primitive of `w ↦ (w - z)⁻¹`, so the FTC for closed
piecewise-`C¹` paths (`contourIntegral_eq_zero_of_hasDerivAt_of_closed`)
gives `∮_γ (w - z)⁻¹ dw = 0`. Combined with `hasGeneralizedWindingNumber_of_avoids`,
this forces the generalized winding number to vanish. -/
theorem IsNullHomologous.of_convex_open {x : ℂ}
    (γ : ClosedPwC1Immersion x) {U : Set ℂ}
    (hU_open : IsOpen U) (hU_convex : Convex ℝ U)
    (h_image : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPwC1Immersion.toPiecewiseC1Path t ∈ U) :
    IsNullHomologous γ.toPwC1Immersion U where
  image_subset := h_image
  winding_zero := by
    intro z hz
    -- (1) Hahn–Banach separation: get `f : ℂ →L[ℝ] ℝ` with `f z < f w` on `U`.
    obtain ⟨f, h_sep⟩ := geometric_hahn_banach_point_open hU_convex hU_open hz
    -- (2) Pick any point in U to witness `f z < f _` (the curve does the job).
    have h_strict : ∃ w₀ ∈ U, f z < f w₀ := by
      refine ⟨γ.toPwC1Immersion.toPiecewiseC1Path 0, h_image 0 ⟨le_rfl, zero_le_one⟩, ?_⟩
      exact h_sep _ (h_image 0 ⟨le_rfl, zero_le_one⟩)
    obtain ⟨w₀, hw₀_U, hfzw₀⟩ := h_strict
    -- (3) Build the complex direction α = ⟨f 1, -(f I)⟩ ≠ 0 with `f w = Re(α * w)`.
    set α : ℂ := Complex.mk (f 1) (-(f I)) with hα_def
    have hα_ne : α ≠ 0 := realCLM_dir_ne_zero hfzw₀
    have hα_eq : ∀ w : ℂ, f w = (α * w).re := fun w => realCLM_eq_re_mul w
    -- (4) γ avoids z: every γ t is in U, so f(γ t - z) > 0, so γ t ≠ z.
    have h_avoid : ∀ t ∈ Icc (0 : ℝ) 1,
        γ.toPwC1Immersion.toPiecewiseC1Path t ≠ z := by
      intro t ht heq
      have hγt_U : γ.toPwC1Immersion.toPiecewiseC1Path t ∈ U := h_image t ht
      have := h_sep _ hγt_U
      rw [heq] at this
      exact lt_irrefl _ this
    -- (5) Half-plane H = {w | 0 < Re(α * (w - z))} contains γ's image and not z.
    have h_image_re_pos : ∀ t ∈ Icc (0 : ℝ) 1,
        0 < (α * (γ.toPwC1Immersion.toPiecewiseC1Path t - z)).re := by
      intro t ht
      rw [← hα_eq, map_sub]
      linarith [h_sep _ (h_image t ht)]
    -- (6) Get a positive distance lower bound (γ avoids z and is on a compact set).
    have hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1,
        δ ≤ ‖γ.toPwC1Immersion.toPiecewiseC1Path t - z‖ :=
      avoids_delta_bound γ.toPwC1Immersion.toPiecewiseC1Path z h_avoid
    -- (7) γ is Lipschitz on ℝ (paper-faithful structure).
    obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
    -- (8) Integrability of (γ t - z)⁻¹ * γ'(t).
    obtain ⟨δ, hδ_pos, h_dist_lb⟩ := hδ
    have h_int : IntervalIntegrable
        (fun t => (γ.toPwC1Immersion.toPiecewiseC1Path t - z)⁻¹ *
          deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t)
        volume 0 1 := by
      have h_aux := intervalIntegrable_div_lipschitz γ.toPwC1Immersion.toPiecewiseC1Path
        hδ_pos h_dist_lb hLip
      -- `h_aux` integrates `deriv γ.toPath.extend t / (γ.toPath.extend t - z)`; we want
      -- `(γ t - z)⁻¹ * deriv γ.toPath.extend t`. The two forms agree by
      -- `div_eq_mul_inv` + `mul_comm` (the coercion `γ t = γ.toPath.extend t` is `rfl`).
      refine h_aux.congr (fun t _ => ?_)
      show deriv (⇑γ.toPwC1Immersion.toPath.extend) t /
            (γ.toPwC1Immersion.toPath.extend t - z) =
          (γ.toPwC1Immersion.toPiecewiseC1Path t - z)⁻¹ *
            deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
      rw [div_eq_mul_inv, mul_comm]
      rfl
    -- (9) Primitive: F(w) = log(α * (w - z)) on H has derivative (w - z)⁻¹.
    have h_prim : ∀ w ∈ {w : ℂ | 0 < (α * (w - z)).re},
        HasDerivAt (fun u => Complex.log (α * (u - z))) (w - z)⁻¹ w := by
      intro w hw
      exact hasDerivAt_log_mul_sub_const hα_ne hw
    -- (10) FTC for closed paths: contour integral is 0.
    have h_contour_zero :
        γ.toPwC1Immersion.toPiecewiseC1Path.contourIntegral (fun w => (w - z)⁻¹) = 0 :=
      PiecewiseC1Path.contourIntegral_eq_zero_of_hasDerivAt_of_closed
        γ.toPwC1Immersion.toPiecewiseC1Path rfl
        h_image_re_pos h_prim h_int
    -- (11) Bridge to generalized winding number.
    have h_wind : HasGeneralizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path z
        ((2 * ↑Real.pi * I)⁻¹ * γ.toPwC1Immersion.toPiecewiseC1Path.contourIntegral
          (fun w => (w - z)⁻¹)) :=
      hasGeneralizedWindingNumber_of_avoids ⟨δ, hδ_pos, h_dist_lb⟩
    rw [h_wind.eq, h_contour_zero, mul_zero]

/-! ## Cauchy's theorem on a rectangle -/

/-- **Cauchy's theorem on a rectangle.** If `f` is holomorphic on a convex open
set `U` containing the closed rectangle `[a, b] × [c, d]`, then the contour
integral of `f` along the boundary of the rectangle (traversed counterclockwise)
is zero.

Combines `cauchy_integral_zero_pwc1` (HW 3.3 specialised to `S = ∅`) with
`IsNullHomologous.of_convex_open`. -/
theorem cauchy_rectangle_zero
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) (hU_convex : Convex ℝ U)
    (h_rect_in_U : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, (x : ℂ) + y * Complex.I ∈ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    (rectangleContour a b c d hab hcd).toPwC1Immersion.toPiecewiseC1Path.contourIntegral f
      = 0 := by
  -- Build the corner-containment hypothesis: at parameter `t ∈ [0,1]`, the
  -- rectangle is in `U`. We use `h_rect_in_U` after locating which segment we
  -- are on. Each segment is a convex combination of corner points; since each
  -- corner is in `U` and `U` is convex, the whole segment is in `U`.
  have h_corners : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, (x : ℂ) + (y : ℂ) * I ∈ U := by
    intro x hx y hy
    have := h_rect_in_U x hx y hy
    -- `h_rect_in_U` uses `Complex.I`; our goal is the same.
    exact this
  -- Image-in-U via segment-wise reasoning.
  have h_image : ∀ t ∈ Icc (0 : ℝ) 1,
      (rectangleContour a b c d hab hcd).toPwC1Immersion.toPiecewiseC1Path t ∈ U := by
    intro t ht
    -- Recall: the contour is `(rectanglePath a b c d).extend = rectangleFun a b c d`
    -- on `[0, 1]`, broken into 4 pieces. On each piece, the path is an affine
    -- combination of two corners of the rectangle.
    show (rectanglePath a b c d).extend t ∈ U
    rw [rectanglePath_extend_eq a b c d t ht]
    -- Locate the segment.
    by_cases ht1 : t ≤ 1/4
    · -- bottom: (a + 4t(b-a)) + c·I
      have hcoeff_nn : 0 ≤ 4 * t := by linarith [ht.1]
      have hcoeff_le : 4 * t ≤ 1 := by linarith [ht1]
      -- x = a + 4t(b - a) ∈ [a, b]
      have hx_mem : a + 4 * t * (b - a) ∈ Icc a b := by
        refine ⟨?_, ?_⟩
        · nlinarith [hab.le]
        · nlinarith [hab.le]
      have hy_mem : c ∈ Icc c d := ⟨le_refl _, hcd.le⟩
      have h_in_U := h_corners _ hx_mem c hy_mem
      simp only [rectangleFun, if_pos ht1, rectSeg1]
      have h_eq : ((a : ℂ) + 4 * (t : ℂ) * (b - a)) + (c : ℂ) * I =
          ((a + 4 * t * (b - a) : ℝ) : ℂ) + (c : ℂ) * I := by push_cast; ring
      rw [h_eq]; exact h_in_U
    · push Not at ht1
      by_cases ht2 : t ≤ 1/2
      · -- right: b + (c + 4(t - 1/4)(d - c))·I
        have hcoeff_nn : 0 ≤ 4 * (t - 1/4) := by linarith
        have hcoeff_le : 4 * (t - 1/4) ≤ 1 := by linarith
        have hy_mem : c + 4 * (t - 1/4) * (d - c) ∈ Icc c d := by
          refine ⟨?_, ?_⟩
          · nlinarith [hcd.le]
          · nlinarith [hcd.le]
        have hx_mem : b ∈ Icc a b := ⟨hab.le, le_refl _⟩
        have h_in_U := h_corners b hx_mem _ hy_mem
        simp only [rectangleFun, if_neg (not_le.mpr ht1), if_pos ht2, rectSeg2]
        have h_eq : ((b : ℂ) + ((c : ℂ) + 4 * ((t : ℂ) - 1/4) * (d - c)) * I) =
            ((b : ℝ) : ℂ) + ((c + 4 * (t - 1/4) * (d - c) : ℝ) : ℂ) * I := by
          push_cast; ring
        rw [h_eq]; exact h_in_U
      · push Not at ht2
        by_cases ht3 : t ≤ 3/4
        · -- top: (b - 4(t - 1/2)(b - a)) + d·I
          have hcoeff_nn : 0 ≤ 4 * (t - 1/2) := by linarith
          have hcoeff_le : 4 * (t - 1/2) ≤ 1 := by linarith
          have hx_mem : b - 4 * (t - 1/2) * (b - a) ∈ Icc a b := by
            refine ⟨?_, ?_⟩
            · nlinarith [hab.le]
            · nlinarith [hab.le]
          have hy_mem : d ∈ Icc c d := ⟨hcd.le, le_refl _⟩
          have h_in_U := h_corners _ hx_mem d hy_mem
          simp only [rectangleFun, if_neg (not_le.mpr ht1), if_neg (not_le.mpr ht2),
            if_pos ht3, rectSeg3]
          have h_eq : ((b : ℂ) - 4 * ((t : ℂ) - 1/2) * (b - a)) + (d : ℂ) * I =
              ((b - 4 * (t - 1/2) * (b - a) : ℝ) : ℂ) + (d : ℂ) * I := by
            push_cast; ring
          rw [h_eq]; exact h_in_U
        · push Not at ht3
          -- left: a + (d - 4(t - 3/4)(d - c))·I
          have hcoeff_nn : 0 ≤ 4 * (t - 3/4) := by linarith
          have hcoeff_le : 4 * (t - 3/4) ≤ 1 := by linarith [ht.2]
          have hy_mem : d - 4 * (t - 3/4) * (d - c) ∈ Icc c d := by
            refine ⟨?_, ?_⟩
            · nlinarith [hcd.le]
            · nlinarith [hcd.le]
          have hx_mem : a ∈ Icc a b := ⟨le_refl _, hab.le⟩
          have h_in_U := h_corners a hx_mem _ hy_mem
          simp only [rectangleFun, if_neg (not_le.mpr ht1), if_neg (not_le.mpr ht2),
            if_neg (not_le.mpr ht3), rectSeg4]
          have h_eq : ((a : ℂ) + ((d : ℂ) - 4 * ((t : ℂ) - 3/4) * (d - c)) * I) =
              ((a : ℝ) : ℂ) + ((d - 4 * (t - 3/4) * (d - c) : ℝ) : ℂ) * I := by
            push_cast; ring
          rw [h_eq]; exact h_in_U
  -- The basepoint is at parameter `0`, i.e. `(a + c·I) ∈ U`.
  have hx : ((a : ℂ) + (c : ℂ) * I) ∈ U :=
    h_corners a ⟨le_refl _, hab.le⟩ c ⟨le_refl _, hcd.le⟩
  exact cauchy_integral_zero_pwc1 hU_open hU_ne hf (rectangleContour a b c d hab hcd)
    (IsNullHomologous.of_convex_open _ hU_open hU_convex h_image) hx

end LeanModularForms

end
