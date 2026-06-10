/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Convex.Star
public import LeanModularForms.ForMathlib.PaperPwC1Immersion
public import LeanModularForms.SpherePacking.AffineSegment
public import LeanModularForms.SpherePacking.CauchyCorollaries
public import LeanModularForms.SpherePacking.RectangularContour

/-!
# Triangular contours in the complex plane

Triangular-contour analogue of `RectangularContour.lean`. Provides
`triangleContour a b c (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)` as a
`ClosedPwC1Immersion a`, plus the Cauchy-on-triangle corollary
`cauchy_triangle_zero` and the decomposition
`contourIntegral_triangleContour_eq` into the three segment integrals.

The parametrisation glues the three sides `a → b → c → a` — each an
`affineSegment` at rate `3` — at the breakpoints `{1/3, 2/3}`; all segment
calculus comes from `AffineSegment.lean`.

Used by sphere-packing's Viazovska contour decomposition (e.g.
`I12_eq_rectangular`, which is actually a *triangle* identity).
-/

open Complex Set Filter Topology MeasureTheory

@[expose] public section

noncomputable section

namespace LeanModularForms

section Triangle

variable (a b c : ℂ)

/-- The boundary of the triangle `a b c`, parameterised on `[0, 1]` as
`a → b → c → a` with breakpoints at `1/3`, `2/3`. Outside `[0, 1]` the value is
whatever the last segment gives; we only ever use the restriction to `Icc 0 1`. -/
def triangleFun : ℝ → ℂ :=
  ifLE (1/3) (affineSegment 3 0 a b) (ifLE (2/3) (affineSegment 3 1 b c) (affineSegment 3 2 c a))

lemma triangleFun_zero : triangleFun a b c 0 = a := by
  norm_num [triangleFun, ifLE, affineSegment]

lemma triangleFun_one : triangleFun a b c 1 = a := by
  norm_num [triangleFun, ifLE, affineSegment]

@[fun_prop]
theorem triangleFun_continuous : Continuous (triangleFun a b c) :=
  ifLE_continuous (affineSegment_continuous _ _ _ _)
    (ifLE_continuous (affineSegment_continuous _ _ _ _) (affineSegment_continuous _ _ _ _)
      (by norm_num [affineSegment]))
    (by norm_num [ifLE, affineSegment])

/-- The interior breakpoints of `triangleFun`: `{1/3, 2/3}`. -/
def trianglePartition : Finset ℝ := {1/3, 2/3}

lemma trianglePartition_subset_Ioo : (trianglePartition : Set ℝ) ⊆ Ioo 0 1 := by
  intro x hx
  simp only [trianglePartition, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
    mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> norm_num

/-- The closed partition `{0, 1/3, 2/3, 1}`. -/
def triangleClosedPartition : Finset ℝ := {0, 1/3, 2/3, 1}

lemma triangleClosedPartition_subset_Icc : (triangleClosedPartition : Set ℝ) ⊆ Icc 0 1 := by
  intro x hx
  simp only [triangleClosedPartition, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
    mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> norm_num

lemma triangleClosedPartition_eq :
    triangleClosedPartition = insert 0 (insert 1 trianglePartition) := by
  ext x
  simp only [triangleClosedPartition, trianglePartition, Finset.mem_insert, Finset.mem_singleton]
  tauto

private lemma triangleFun_eventuallyEq_off {t : ℝ} (htp : t ∉ trianglePartition) :
    ∃ r k p q, triangleFun a b c =ᶠ[𝓝 t] affineSegment r k p q := by
  simp only [trianglePartition, Finset.mem_insert, Finset.mem_singleton] at htp
  push Not at htp
  obtain ⟨ht1, ht2⟩ := htp
  rcases lt_or_gt_of_ne ht1 with h1 | h1
  · exact ⟨_, _, _, _, ifLE_eventuallyEq_left h1⟩
  rcases lt_or_gt_of_ne ht2 with h2 | h2
  · exact ⟨_, _, _, _, (ifLE_eventuallyEq_right h1).trans (ifLE_eventuallyEq_left h2)⟩
  exact ⟨_, _, _, _, (ifLE_eventuallyEq_right h1).trans (ifLE_eventuallyEq_right h2)⟩

/-- The triangular boundary as a mathlib `Path` from the basepoint `a` back to itself. -/
def trianglePath : Path a a where
  toFun t := triangleFun a b c t
  continuous_toFun := (triangleFun_continuous a b c).continuousOn.restrict
  source' := triangleFun_zero a b c
  target' := triangleFun_one a b c

private lemma trianglePath_extend_eq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (trianglePath a b c).extend t = triangleFun a b c t :=
  Path.extend_apply _ ht

private lemma trianglePath_extend_eventuallyEq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (trianglePath a b c).extend =ᶠ[𝓝 t] triangleFun a b c :=
  Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs =>
    trianglePath_extend_eq a b c s (Ioo_subset_Icc_self hs)

private lemma trianglePath_extend_eventuallyEq_off {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (htp : t ∉ trianglePartition) :
    ∃ r k p q, (trianglePath a b c).extend =ᶠ[𝓝 t] affineSegment r k p q := by
  obtain ⟨r, k, p, q, h⟩ := triangleFun_eventuallyEq_off a b c htp
  exact ⟨r, k, p, q, (trianglePath_extend_eventuallyEq a b c ht).trans h⟩

/-- The triangular boundary as a `PiecewiseC1Path`. -/
def trianglePC1Path : PiecewiseC1Path a a where
  toFun := (trianglePath a b c).extend
  source := (trianglePath a b c).extend_zero
  target := (trianglePath a b c).extend_one
  continuous_toFun := (trianglePath a b c).continuous_extend.continuousOn
  toPath := trianglePath a b c
  toPath_extend_eq_toFun := fun _ _ => rfl
  partition := trianglePartition
  partition_subset := trianglePartition_subset_Ioo
  differentiable_off := fun t ht htp => by
    obtain ⟨_, _, _, _, h⟩ := trianglePath_extend_eventuallyEq_off a b c ht htp
    exact affineSegment_differentiableAt_of_eventuallyEq h
  deriv_continuous_off := fun t ht htp => by
    obtain ⟨_, _, _, _, h⟩ := trianglePath_extend_eventuallyEq_off a b c ht htp
    exact affineSegment_deriv_continuousAt_of_eventuallyEq h

/-- On `[0, 1/3]` the extended triangle path is the side `a → b`. -/
lemma trianglePath_extend_eqOn_seg1 :
    EqOn (trianglePath a b c).extend (affineSegment 3 0 a b) (Icc 0 (1/3 : ℝ)) := fun t ht =>
  (trianglePath_extend_eq a b c t ⟨ht.1, ht.2.trans (by norm_num)⟩).trans
    (ifLE_apply_of_le ht.2)

/-- On `[1/3, 2/3]` the extended triangle path is the side `b → c`. -/
lemma trianglePath_extend_eqOn_seg2 :
    EqOn (trianglePath a b c).extend (affineSegment 3 1 b c) (Icc (1/3 : ℝ) (2/3)) := fun t ht =>
  (trianglePath_extend_eq a b c t ⟨le_trans (by norm_num) ht.1, ht.2.trans (by norm_num)⟩).trans
    ((ifLE_eqOn_right (by norm_num [ifLE, affineSegment]) ht.1).trans (ifLE_apply_of_le ht.2))

/-- On `[2/3, 1]` the extended triangle path is the side `c → a`. -/
lemma trianglePath_extend_eqOn_seg3 :
    EqOn (trianglePath a b c).extend (affineSegment 3 2 c a) (Icc (2/3 : ℝ) 1) := fun t ht =>
  (trianglePath_extend_eq a b c t ⟨le_trans (by norm_num) ht.1, ht.2⟩).trans
    ((ifLE_eqOn_right (by norm_num [ifLE, affineSegment]) (le_trans (by norm_num) ht.1)).trans
      (ifLE_eqOn_right (by norm_num [affineSegment]) ht.1))

private lemma triangleClosedPartition_consecutive_cases {p q : ℝ}
    (h : triangleClosedPartition.IsConsecutive p q) :
    (p = 0 ∧ q = 1/3) ∨ (p = 1/3 ∧ q = 2/3) ∨ (p = 2/3 ∧ q = 1) := by
  obtain ⟨hp, hq, hpq, hno⟩ := h
  have h1 := hno (1/3) (by norm_num [triangleClosedPartition])
  have h2 := hno (2/3) (by norm_num [triangleClosedPartition])
  simp only [triangleClosedPartition, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    (revert hpq h1 h2; norm_num [mem_Ioo])

/-- **The triangular contour** as a `ClosedPwC1Immersion`. Starts at the
vertex `a` and traverses the boundary `a → b → c → a`.

The parametrisation has breakpoints `{1/3, 2/3}` in `(0, 1)` and is
`C¹` on each closed piece with non-vanishing derivative. -/
def triangleContour (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    ClosedPwC1Immersion a where
  toPiecewiseC1Path := trianglePC1Path a b c
  closedPartition := triangleClosedPartition
  zero_mem_closedPartition := by simp [triangleClosedPartition]
  one_mem_closedPartition := by simp [triangleClosedPartition]
  closedPartition_subset := triangleClosedPartition_subset_Icc
  closedPartition_eq := triangleClosedPartition_eq
  contDiffOn_pieces := by
    intro p q hcons
    show ContDiffOn ℝ 1 (trianglePath a b c).extend (Icc p q)
    rcases triangleClosedPartition_consecutive_cases hcons with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact affineSegment_contDiffOn_of_eqOn (trianglePath_extend_eqOn_seg1 a b c)
    · exact affineSegment_contDiffOn_of_eqOn (trianglePath_extend_eqOn_seg2 a b c)
    · exact affineSegment_contDiffOn_of_eqOn (trianglePath_extend_eqOn_seg3 a b c)
  derivWithin_ne_zero_pieces := by
    intro p q hcons t ht
    show derivWithin (trianglePath a b c).extend (Icc p q) t ≠ 0
    rcases triangleClosedPartition_consecutive_cases hcons with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [affineSegment_derivWithin_of_eqOn (trianglePath_extend_eqOn_seg1 a b c)
        (by norm_num) ht]
      exact smul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm hab))
    · rw [affineSegment_derivWithin_of_eqOn (trianglePath_extend_eqOn_seg2 a b c)
        (by norm_num) ht]
      exact smul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm hbc))
    · rw [affineSegment_derivWithin_of_eqOn (trianglePath_extend_eqOn_seg3 a b c)
        (by norm_num) ht]
      exact smul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm hca))

end Triangle

/-- The image of the triangular contour `triangleContour a b c` on `[0, 1]` lies
inside any convex set containing the three vertices. This is the key
"image-in-U" fact that makes the triangle contour amenable to Cauchy's
theorem on convex open sets. -/
theorem triangleContour_image_subset_of_convex
    {a b c : ℂ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    {U : Set ℂ} (hU_convex : Convex ℝ U)
    (h_a_in_U : a ∈ U) (h_b_in_U : b ∈ U) (h_c_in_U : c ∈ U) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      (triangleContour a b c hab hbc hca).toPwC1Immersion.toPiecewiseC1Path t ∈ U := by
  intro t ht
  show (trianglePath a b c).extend t ∈ U
  rcases le_or_gt t (1/3) with h1 | h1
  · rw [trianglePath_extend_eqOn_seg1 a b c ⟨ht.1, h1⟩]
    exact hU_convex.segment_subset h_a_in_U h_b_in_U
      (affineSegment_mem_segment (by linarith [ht.1]) (by linarith) a b)
  rcases le_or_gt t (2/3) with h2 | h2
  · rw [trianglePath_extend_eqOn_seg2 a b c ⟨h1.le, h2⟩]
    exact hU_convex.segment_subset h_b_in_U h_c_in_U
      (affineSegment_mem_segment (by linarith) (by linarith) b c)
  · rw [trianglePath_extend_eqOn_seg3 a b c ⟨h2.le, ht.2⟩]
    exact hU_convex.segment_subset h_c_in_U h_a_in_U
      (affineSegment_mem_segment (by linarith) (by linarith [ht.2]) c a)

/-- **Cauchy's theorem on a triangle.** If `f` is holomorphic on a convex open
set `U` containing the three vertices `a`, `b`, `c`, then the contour integral
of `f` along the boundary of the triangle (traversed `a → b → c → a`) is zero.

Combines `cauchy_integral_zero_pwc1` (HW 3.3 specialised to `S = ∅`) with
`IsNullHomologous.of_convex_open`. -/
theorem cauchy_triangle_zero
    {a b c : ℂ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) (hU_convex : Convex ℝ U)
    (h_a_in_U : a ∈ U) (h_b_in_U : b ∈ U) (h_c_in_U : c ∈ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    (triangleContour a b c hab hbc hca).toPwC1Immersion.toPiecewiseC1Path.contourIntegral f
      = 0 :=
  cauchy_integral_zero_pwc1 hU_open hU_ne hf (triangleContour a b c hab hbc hca)
    (IsNullHomologous.of_convex_open _ hU_open hU_convex
      (triangleContour_image_subset_of_convex hab hbc hca hU_convex h_a_in_U h_b_in_U h_c_in_U))
    h_a_in_U

/-- **Decomposition of the contour integral over the triangle into three segment
integrals.** For a function `f` continuous on the image of the triangular contour,
the contour integral of `f` along the boundary of `triangleContour a b c hab hbc hca`
equals the sum of the three segment integrals `(a → b) + (b → c) + (c → a)`, each
parameterised on `[0, 1]` via `(p, q) ↦ ∫ s in 0..1, f (p + s • (q - p)) * (q - p)`. -/
theorem contourIntegral_triangleContour_eq
    {a b c : ℂ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    {f : ℂ → ℂ}
    (hf : ContinuousOn f
      ((triangleContour a b c hab hbc hca).toPwC1Immersion.toPiecewiseC1Path '' Icc (0:ℝ) 1)) :
    (triangleContour a b c hab hbc hca).toPwC1Immersion.toPiecewiseC1Path.contourIntegral f
      = (∫ s in (0:ℝ)..1, f (a + s • (b - a)) * (b - a))
      + (∫ s in (0:ℝ)..1, f (b + s • (c - b)) * (c - b))
      + (∫ s in (0:ℝ)..1, f (c + s • (a - c)) * (a - c)) := by
  show ∫ t in (0:ℝ)..1, f ((trianglePath a b c).extend t) * deriv (trianglePath a b c).extend t
    = _
  have hf' : ContinuousOn f ((trianglePath a b c).extend '' Icc (0 : ℝ) 1) := hf
  have h₁ := affineSegment_integrand_intervalIntegrable_of_eqOn
    (trianglePath_extend_eqOn_seg1 a b c) (by norm_num)
    (Icc_subset_Icc le_rfl (by norm_num)) hf'
  have h₂ := affineSegment_integrand_intervalIntegrable_of_eqOn
    (trianglePath_extend_eqOn_seg2 a b c) (by norm_num)
    (Icc_subset_Icc (by norm_num) (by norm_num)) hf'
  have h₃ := affineSegment_integrand_intervalIntegrable_of_eqOn
    (trianglePath_extend_eqOn_seg3 a b c) (by norm_num)
    (Icc_subset_Icc (by norm_num) le_rfl) hf'
  rw [← intervalIntegral.integral_add_adjacent_intervals h₁ (h₂.trans h₃),
    ← intervalIntegral.integral_add_adjacent_intervals h₂ h₃,
    affineSegment_integral_eq_of_eqOn (by norm_num) (by norm_num) (by norm_num)
      (trianglePath_extend_eqOn_seg1 a b c) f,
    affineSegment_integral_eq_of_eqOn (by norm_num) (by norm_num) (by norm_num)
      (trianglePath_extend_eqOn_seg2 a b c) f,
    affineSegment_integral_eq_of_eqOn (by norm_num) (by norm_num) (by norm_num)
      (trianglePath_extend_eqOn_seg3 a b c) f,
    ← add_assoc]

end LeanModularForms

end

end
