/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import LeanModularForms.ForMathlib.PaperPwC1Immersion
public import LeanModularForms.ForMathlib.NullHomologous
public import LeanModularForms.ForMathlib.CauchyPrincipalValue
public import LeanModularForms.SpherePacking.CauchyCorollaries
public import LeanModularForms.SpherePacking.RectangularContour
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Convex.Star

/-!
# Triangular contours in the complex plane

Triangular-contour analogue of `RectangularContour.lean`. Provides
`triangleContour a b c (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)` as a
`ClosedPwC1Immersion a`, plus the Cauchy-on-triangle corollary
`cauchy_triangle_zero`.

The parametrisation on `[0, 1]` uses breakpoints `{1/3, 2/3}`:

* `t ∈ [0, 1/3]`:  `(1 - 3t) · a + 3t · b`        (a → b)
* `t ∈ [1/3, 2/3]`: `(2 - 3t) · b + (3t - 1) · c`  (b → c)
* `t ∈ [2/3, 1]`:  `(3 - 3t) · c + (3t - 2) · a`   (c → a)

Used by sphere-packing's Viazovska contour decomposition (e.g.
`I12_eq_rectangular`, which is actually a *triangle* identity).
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

@[expose] public section

noncomputable section

namespace LeanModularForms

/-! ## The three sides of a triangle as smooth segments -/

/-- The first side of the triangle, parameterised on all of `ℝ` by
`t ↦ (1 - 3t) · a + 3t · b`. -/
def triSeg1 (a b : ℂ) : ℝ → ℂ := fun t =>
  (1 - 3 * (t : ℂ)) * a + 3 * (t : ℂ) * b

/-- The second side of the triangle, parameterised by
`t ↦ (2 - 3t) · b + (3t - 1) · c`. -/
def triSeg2 (b c : ℂ) : ℝ → ℂ := fun t =>
  (2 - 3 * (t : ℂ)) * b + (3 * (t : ℂ) - 1) * c

/-- The third side of the triangle, parameterised by
`t ↦ (3 - 3t) · c + (3t - 2) · a`. -/
def triSeg3 (a c : ℂ) : ℝ → ℂ := fun t =>
  (3 - 3 * (t : ℂ)) * c + (3 * (t : ℂ) - 2) * a

/-- The full parameterisation of the triangular boundary on `[0, 1]`. Outside
`[0, 1]` the value is whatever the last segment gives; this is fine because
we only ever use the path via its restriction to `Icc 0 1`. -/
def triangleFun (a b c : ℂ) : ℝ → ℂ := fun t =>
  if t ≤ 1/3 then triSeg1 a b t
  else if t ≤ 2/3 then triSeg2 b c t
  else triSeg3 a c t

/-! ### Junction values -/

lemma triSeg1_at_zero (a b : ℂ) : triSeg1 a b 0 = a := by
  simp [triSeg1]

lemma triSeg1_at_third (a b : ℂ) : triSeg1 a b (1/3) = b := by
  simp only [triSeg1]; push_cast; ring

lemma triSeg2_at_third (b c : ℂ) : triSeg2 b c (1/3) = b := by
  simp only [triSeg2]; push_cast; ring

lemma triSeg2_at_two_thirds (b c : ℂ) : triSeg2 b c (2/3) = c := by
  simp only [triSeg2]; push_cast; ring

lemma triSeg3_at_two_thirds (a c : ℂ) : triSeg3 a c (2/3) = c := by
  simp only [triSeg3]; push_cast; ring

lemma triSeg3_at_one (a c : ℂ) : triSeg3 a c 1 = a := by
  simp only [triSeg3]; push_cast; ring

lemma triangleFun_at_zero (a b c : ℂ) : triangleFun a b c 0 = a := by
  simp [triangleFun, triSeg1_at_zero]

lemma triangleFun_at_one (a b c : ℂ) : triangleFun a b c 1 = a := by
  simp only [triangleFun, show ¬(1 : ℝ) ≤ 1/3 by norm_num,
    show ¬(1 : ℝ) ≤ 2/3 by norm_num, if_false, triSeg3_at_one]

lemma triangleFun_closed (a b c : ℂ) :
    triangleFun a b c 0 = triangleFun a b c 1 := by
  rw [triangleFun_at_zero, triangleFun_at_one]

/-! ### `ContDiff ℝ ⊤` for each segment -/

lemma triSeg1_contDiff (a b : ℂ) : ContDiff ℝ ⊤ (triSeg1 a b) :=
  ((contDiff_const.sub
    (contDiff_const.mul Complex.ofRealCLM.contDiff)).mul contDiff_const).add
      ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const)

lemma triSeg2_contDiff (b c : ℂ) : ContDiff ℝ ⊤ (triSeg2 b c) :=
  ((contDiff_const.sub
    (contDiff_const.mul Complex.ofRealCLM.contDiff)).mul contDiff_const).add
      (((contDiff_const.mul Complex.ofRealCLM.contDiff).sub
        contDiff_const).mul contDiff_const)

lemma triSeg3_contDiff (a c : ℂ) : ContDiff ℝ ⊤ (triSeg3 a c) :=
  ((contDiff_const.sub
    (contDiff_const.mul Complex.ofRealCLM.contDiff)).mul contDiff_const).add
      (((contDiff_const.mul Complex.ofRealCLM.contDiff).sub
        contDiff_const).mul contDiff_const)

lemma triSeg1_continuous (a b : ℂ) : Continuous (triSeg1 a b) :=
  (triSeg1_contDiff a b).continuous

lemma triSeg2_continuous (b c : ℂ) : Continuous (triSeg2 b c) :=
  (triSeg2_contDiff b c).continuous

lemma triSeg3_continuous (a c : ℂ) : Continuous (triSeg3 a c) :=
  (triSeg3_contDiff a c).continuous

/-! ### Layered continuity of `triangleFun` -/

def triangleFun_inner23 (a b c : ℂ) : ℝ → ℂ := fun t =>
  if t ≤ 2/3 then triSeg2 b c t else triSeg3 a c t

lemma triangleFun_inner23_continuous (a b c : ℂ) :
    Continuous (triangleFun_inner23 a b c) :=
  Continuous.if_le (triSeg2_continuous b c) (triSeg3_continuous a c)
    continuous_id continuous_const (fun t (ht : t = 2/3) => by
      subst ht
      rw [triSeg2_at_two_thirds, triSeg3_at_two_thirds])

lemma triangleFun_eq_layered (a b c : ℂ) (t : ℝ) :
    triangleFun a b c t =
      (if t ≤ 1/3 then triSeg1 a b t else triangleFun_inner23 a b c t) := by
  unfold triangleFun triangleFun_inner23
  split_ifs <;> rfl

@[fun_prop]
theorem triangleFun_continuous (a b c : ℂ) :
    Continuous (triangleFun a b c) := by
  rw [show triangleFun a b c =
    (fun t => if t ≤ 1/3 then triSeg1 a b t else triangleFun_inner23 a b c t) from
    funext (triangleFun_eq_layered a b c)]
  apply Continuous.if_le (triSeg1_continuous a b)
    (triangleFun_inner23_continuous a b c) continuous_id continuous_const
  intro t ht
  simp only [id] at ht
  obtain rfl : t = 1/3 := by linarith
  unfold triangleFun_inner23
  simp only [show (1/3 : ℝ) ≤ 2/3 by norm_num, if_true,
    triSeg1_at_third, triSeg2_at_third]

/-! ### Eventual-equality lemmas to each segment -/

lemma triangleFun_eventuallyEq_seg1 (a b c : ℂ) {t : ℝ} (ht1 : t < 1/3) :
    triangleFun a b c =ᶠ[𝓝 t] triSeg1 a b :=
  Filter.eventually_of_mem (Iio_mem_nhds ht1) fun s (hs : s < 1/3) => by
    simp only [triangleFun, if_pos hs.le]

lemma triangleFun_eventuallyEq_seg2 (a b c : ℂ) {t : ℝ}
    (ht1 : 1/3 < t) (ht2 : t < 2/3) :
    triangleFun a b c =ᶠ[𝓝 t] triSeg2 b c :=
  Filter.eventually_of_mem
    (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht2))
    fun s ⟨hs1, hs2⟩ => by
      simp only [triangleFun,
        show ¬s ≤ 1/3 from not_le.mpr hs1,
        show s ≤ 2/3 from le_of_lt hs2, if_true, if_false]

lemma triangleFun_eventuallyEq_seg3 (a b c : ℂ) {t : ℝ}
    (ht2 : 2/3 < t) :
    triangleFun a b c =ᶠ[𝓝 t] triSeg3 a c :=
  Filter.eventually_of_mem (Ioi_mem_nhds ht2) fun s (hs2 : 2/3 < s) => by
    simp only [triangleFun,
      show ¬s ≤ 1/3 from not_le.mpr (lt_trans (by norm_num : (1:ℝ)/3 < 2/3) hs2),
      show ¬s ≤ 2/3 from not_le.mpr hs2, if_false]

/-! ### Partition and differentiability off-partition -/

/-- The interior partition points for `triangleFun`: `{1/3, 2/3}`. -/
def trianglePartition : Finset ℝ := {1/3, 2/3}

lemma trianglePartition_subset_Ioo :
    (trianglePartition : Set ℝ) ⊆ Ioo 0 1 := by
  intro x hx
  simp only [trianglePartition, Finset.coe_insert, Finset.coe_singleton,
    mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩

/-- The closed partition `{0, 1/3, 2/3, 1}`. -/
def triangleClosedPartition : Finset ℝ := {0, 1/3, 2/3, 1}

lemma triangleClosedPartition_subset_Icc :
    (triangleClosedPartition : Set ℝ) ⊆ Icc 0 1 := by
  intro x hx
  simp only [triangleClosedPartition, Finset.coe_insert, Finset.coe_singleton,
    mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩

lemma triangleClosedPartition_eq :
    triangleClosedPartition = insert 0 (insert 1 trianglePartition) := by
  ext x
  simp only [triangleClosedPartition, trianglePartition, Finset.mem_insert,
    Finset.mem_singleton]
  tauto

lemma triangleFun_differentiableAt_off (a b c : ℂ) (t : ℝ)
    (_ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ trianglePartition) :
    DifferentiableAt ℝ (triangleFun a b c) t := by
  simp only [trianglePartition, Finset.mem_insert, Finset.mem_singleton] at htp
  push Not at htp
  obtain ⟨ht1, ht2⟩ := htp
  have hT : (⊤ : WithTop ℕ∞) ≠ 0 := WithTop.top_ne_zero
  rcases lt_or_gt_of_ne ht1 with h1 | h1
  · exact ((triSeg1_contDiff a b).differentiable hT).differentiableAt.congr_of_eventuallyEq
      (triangleFun_eventuallyEq_seg1 a b c h1)
  rcases lt_or_gt_of_ne ht2 with h2 | h2
  · exact ((triSeg2_contDiff b c).differentiable hT).differentiableAt.congr_of_eventuallyEq
      (triangleFun_eventuallyEq_seg2 a b c h1 h2)
  exact ((triSeg3_contDiff a c).differentiable hT).differentiableAt.congr_of_eventuallyEq
    (triangleFun_eventuallyEq_seg3 a b c h2)

lemma triangleFun_deriv_continuousAt_off (a b c : ℂ) (t : ℝ)
    (_ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ trianglePartition) :
    ContinuousAt (deriv (triangleFun a b c)) t := by
  simp only [trianglePartition, Finset.mem_insert, Finset.mem_singleton] at htp
  push Not at htp
  obtain ⟨ht1, ht2⟩ := htp
  rcases lt_or_gt_of_ne ht1 with h1 | h1
  · exact (continuousAt_congr (triangleFun_eventuallyEq_seg1 a b c h1).deriv).mpr
      ((triSeg1_contDiff a b).continuous_deriv le_top).continuousAt
  rcases lt_or_gt_of_ne ht2 with h2 | h2
  · exact (continuousAt_congr (triangleFun_eventuallyEq_seg2 a b c h1 h2).deriv).mpr
      ((triSeg2_contDiff b c).continuous_deriv le_top).continuousAt
  exact (continuousAt_congr (triangleFun_eventuallyEq_seg3 a b c h2).deriv).mpr
    ((triSeg3_contDiff a c).continuous_deriv le_top).continuousAt

/-! ### The `Path` and `PiecewiseC1Path` instances -/

/-- The triangular boundary as a mathlib `Path` from the basepoint `a` back to itself. -/
def trianglePath (a b c : ℂ) : Path a a where
  toFun t := triangleFun a b c t
  continuous_toFun := (triangleFun_continuous a b c).continuousOn.restrict
  source' := triangleFun_at_zero a b c
  target' := triangleFun_at_one a b c

lemma trianglePath_extend_eq (a b c : ℂ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (trianglePath a b c).extend t = triangleFun a b c t :=
  Path.extend_apply _ ht

lemma trianglePath_extend_eventuallyEq (a b c : ℂ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (trianglePath a b c).extend =ᶠ[𝓝 t] triangleFun a b c :=
  Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs =>
    trianglePath_extend_eq a b c s (Ioo_subset_Icc_self hs)

lemma trianglePath_differentiableAt_off (a b c : ℂ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ trianglePartition) :
    DifferentiableAt ℝ (trianglePath a b c).extend t :=
  (triangleFun_differentiableAt_off a b c t ht htp).congr_of_eventuallyEq
    (trianglePath_extend_eventuallyEq a b c ht)

lemma trianglePath_deriv_continuousAt_off (a b c : ℂ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ trianglePartition) :
    ContinuousAt (deriv (trianglePath a b c).extend) t :=
  (continuousAt_congr (trianglePath_extend_eventuallyEq a b c ht).deriv).mpr
    (triangleFun_deriv_continuousAt_off a b c t ht htp)

/-- The triangular boundary as a `PiecewiseC1Path`. -/
def trianglePC1Path (a b c : ℂ) : PiecewiseC1Path a a where
  toFun := (trianglePath a b c).extend
  source := (trianglePath a b c).extend_zero
  target := (trianglePath a b c).extend_one
  continuous_toFun := (trianglePath a b c).continuous_extend.continuousOn
  toPath := trianglePath a b c
  toPath_extend_eq_toFun := fun _ _ => rfl
  partition := trianglePartition
  partition_subset := trianglePartition_subset_Ioo
  differentiable_off := trianglePath_differentiableAt_off a b c
  deriv_continuous_off := trianglePath_deriv_continuousAt_off a b c

/-! ### Identifying consecutive pairs of the closed partition

The closed partition `{0, 1/3, 2/3, 1}` has exactly three consecutive pairs:
`(0, 1/3)`, `(1/3, 2/3)`, `(2/3, 1)`. We case-split on these in order to provide
`contDiffOn_pieces` and `derivWithin_ne_zero_pieces`. -/

lemma triangleClosedPartition_consecutive_cases {p q : ℝ}
    (h : triangleClosedPartition.IsConsecutive p q) :
    (p = 0 ∧ q = 1/3) ∨ (p = 1/3 ∧ q = 2/3) ∨ (p = 2/3 ∧ q = 1) := by
  obtain ⟨hp, hq, hpq, hno⟩ := h
  simp only [triangleClosedPartition, Finset.mem_insert,
    Finset.mem_singleton] at hp hq
  -- Forbid any element strictly between p and q.
  have ban : ∀ r ∈ ({0, 1/3, 2/3, 1} : Finset ℝ), ¬ (p < r ∧ r < q) := by
    intro r hr ⟨hr1, hr2⟩
    exact hno r hr ⟨hr1, hr2⟩
  rcases hp with rfl | rfl | rfl | rfl
  · rcases hq with rfl | rfl | rfl | rfl
    · exact absurd hpq (by norm_num)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact absurd (ban (1/3) (by simp)
        ⟨by norm_num, by norm_num⟩) (by tauto)
    · exact absurd (ban (1/3) (by simp)
        ⟨by norm_num, by norm_num⟩) (by tauto)
  · rcases hq with rfl | rfl | rfl | rfl
    · exact absurd hpq (by norm_num)
    · exact absurd hpq (by norm_num)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact absurd (ban (2/3) (by simp)
        ⟨by norm_num, by norm_num⟩) (by tauto)
  · rcases hq with rfl | rfl | rfl | rfl
    · exact absurd hpq (by norm_num)
    · exact absurd hpq (by norm_num)
    · exact absurd hpq (by norm_num)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rcases hq with rfl | rfl | rfl | rfl
    all_goals exact absurd hpq (by norm_num)

/-! ### Each closed-piece restriction equals a segment

On each of the three closed sub-intervals, `(trianglePath a b c).extend` agrees
with the corresponding analytically-defined segment function. -/

lemma triangleFun_eq_seg1_on_Icc (a b c : ℂ) :
    EqOn (triangleFun a b c) (triSeg1 a b) (Icc 0 (1/3 : ℝ)) := by
  intro t ht
  simp only [triangleFun, if_pos ht.2]

lemma triangleFun_eq_seg2_on_Icc (a b c : ℂ) :
    EqOn (triangleFun a b c) (triSeg2 b c) (Icc (1/3 : ℝ) (2/3)) := by
  intro t ht
  by_cases h_eq : t = 1/3
  · subst h_eq
    simp only [triangleFun, le_refl, if_true]
    rw [triSeg1_at_third, triSeg2_at_third]
  · have ht1 : ¬ t ≤ 1/3 := not_le.mpr (lt_of_le_of_ne ht.1 (Ne.symm h_eq))
    simp only [triangleFun, if_neg ht1, if_pos ht.2]

lemma triangleFun_eq_seg3_on_Icc (a b c : ℂ) :
    EqOn (triangleFun a b c) (triSeg3 a c) (Icc (2/3 : ℝ) 1) := by
  intro t ht
  by_cases h_eq : t = 2/3
  · subst h_eq
    simp only [triangleFun, show ¬(2/3 : ℝ) ≤ 1/3 by norm_num, le_refl,
      if_true, if_false]
    rw [triSeg2_at_two_thirds, triSeg3_at_two_thirds]
  · have ht2 : ¬ t ≤ 2/3 := not_le.mpr (lt_of_le_of_ne ht.1 (Ne.symm h_eq))
    have ht1 : ¬ t ≤ 1/3 := not_le.mpr (lt_trans (by norm_num : (1:ℝ)/3 < 2/3)
      (not_le.mp ht2))
    simp only [triangleFun, if_neg ht1, if_neg ht2]

lemma trianglePath_extend_eq_seg1_on_Icc (a b c : ℂ) :
    EqOn (trianglePath a b c).extend (triSeg1 a b) (Icc 0 (1/3 : ℝ)) := fun t ht => by
  have hIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  rw [trianglePath_extend_eq a b c t hIcc, triangleFun_eq_seg1_on_Icc a b c ht]

lemma trianglePath_extend_eq_seg2_on_Icc (a b c : ℂ) :
    EqOn (trianglePath a b c).extend (triSeg2 b c) (Icc (1/3 : ℝ) (2/3)) := fun t ht => by
  have hIcc : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [trianglePath_extend_eq a b c t hIcc, triangleFun_eq_seg2_on_Icc a b c ht]

lemma trianglePath_extend_eq_seg3_on_Icc (a b c : ℂ) :
    EqOn (trianglePath a b c).extend (triSeg3 a c) (Icc (2/3 : ℝ) 1) := fun t ht => by
  have hIcc : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  rw [trianglePath_extend_eq a b c t hIcc, triangleFun_eq_seg3_on_Icc a b c ht]

/-! ### Derivatives of each segment

Each segment is affine-linear in `t`, so its derivative is the constant
"velocity" complex number `3·(next - prev)`. -/

lemma triSeg1_hasDerivAt (a b : ℂ) (t : ℝ) :
    HasDerivAt (triSeg1 a b) (3 * (b - a)) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ))) (1 : ℂ) t :=
    Complex.ofRealCLM.hasDerivAt
  -- f(t) = (1 - 3t) * a + 3t * b
  have h_left : HasDerivAt (fun s : ℝ => (1 - 3 * (s : ℂ)) * a) (-(3 * a)) t := by
    have h_inner : HasDerivAt (fun s : ℝ => (1 : ℂ) - 3 * (s : ℂ)) (-3) t := by
      have := (hasDerivAt_const t (1 : ℂ)).sub (h1.const_mul (3 : ℂ))
      simpa using this
    have := h_inner.mul_const a
    convert this using 1; ring
  have h_right : HasDerivAt (fun s : ℝ => 3 * (s : ℂ) * b) (3 * b) t := by
    have := (h1.const_mul (3 : ℂ)).mul_const b
    simpa using this
  have h_sum : HasDerivAt (fun s : ℝ => (1 - 3 * (s : ℂ)) * a + 3 * (s : ℂ) * b)
      (3 * (b - a)) t := by
    have := h_left.add h_right
    convert this using 1; ring
  exact h_sum

lemma triSeg1_deriv (a b : ℂ) (t : ℝ) :
    deriv (triSeg1 a b) t = 3 * (b - a) :=
  (triSeg1_hasDerivAt a b t).deriv

lemma triSeg2_hasDerivAt (b c : ℂ) (t : ℝ) :
    HasDerivAt (triSeg2 b c) (3 * (c - b)) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ))) (1 : ℂ) t :=
    Complex.ofRealCLM.hasDerivAt
  have h_left : HasDerivAt (fun s : ℝ => (2 - 3 * (s : ℂ)) * b) (-(3 * b)) t := by
    have h_inner : HasDerivAt (fun s : ℝ => (2 : ℂ) - 3 * (s : ℂ)) (-3) t := by
      have := (hasDerivAt_const t (2 : ℂ)).sub (h1.const_mul (3 : ℂ))
      simpa using this
    have := h_inner.mul_const b
    convert this using 1; ring
  have h_right : HasDerivAt (fun s : ℝ => (3 * (s : ℂ) - 1) * c) (3 * c) t := by
    have h_inner : HasDerivAt (fun s : ℝ => (3 : ℂ) * (s : ℂ) - 1) 3 t := by
      have := (h1.const_mul (3 : ℂ)).sub_const ((1 : ℂ))
      simpa using this
    have := h_inner.mul_const c
    simpa using this
  have h_sum : HasDerivAt (fun s : ℝ => (2 - 3 * (s : ℂ)) * b + (3 * (s : ℂ) - 1) * c)
      (3 * (c - b)) t := by
    have := h_left.add h_right
    convert this using 1; ring
  exact h_sum

lemma triSeg2_deriv (b c : ℂ) (t : ℝ) :
    deriv (triSeg2 b c) t = 3 * (c - b) :=
  (triSeg2_hasDerivAt b c t).deriv

lemma triSeg3_hasDerivAt (a c : ℂ) (t : ℝ) :
    HasDerivAt (triSeg3 a c) (3 * (a - c)) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ))) (1 : ℂ) t :=
    Complex.ofRealCLM.hasDerivAt
  have h_left : HasDerivAt (fun s : ℝ => (3 - 3 * (s : ℂ)) * c) (-(3 * c)) t := by
    have h_inner : HasDerivAt (fun s : ℝ => (3 : ℂ) - 3 * (s : ℂ)) (-3) t := by
      have := (hasDerivAt_const t (3 : ℂ)).sub (h1.const_mul (3 : ℂ))
      simpa using this
    have := h_inner.mul_const c
    convert this using 1; ring
  have h_right : HasDerivAt (fun s : ℝ => (3 * (s : ℂ) - 2) * a) (3 * a) t := by
    have h_inner : HasDerivAt (fun s : ℝ => (3 : ℂ) * (s : ℂ) - 2) 3 t := by
      have := (h1.const_mul (3 : ℂ)).sub_const ((2 : ℂ))
      simpa using this
    have := h_inner.mul_const a
    simpa using this
  have h_sum : HasDerivAt (fun s : ℝ => (3 - 3 * (s : ℂ)) * c + (3 * (s : ℂ) - 2) * a)
      (3 * (a - c)) t := by
    have := h_left.add h_right
    convert this using 1; ring
  exact h_sum

lemma triSeg3_deriv (a c : ℂ) (t : ℝ) :
    deriv (triSeg3 a c) t = 3 * (a - c) :=
  (triSeg3_hasDerivAt a c t).deriv

/-! ### `ContDiffOn ℝ 1` of `(trianglePath a b c).extend` on each closed piece -/

lemma trianglePath_extend_contDiffOn_seg1 (a b c : ℂ) :
    ContDiffOn ℝ 1 (trianglePath a b c).extend (Icc 0 (1/3 : ℝ)) :=
  (((triSeg1_contDiff a b).of_le le_top).contDiffOn).congr fun _ ht =>
    trianglePath_extend_eq_seg1_on_Icc a b c ht

lemma trianglePath_extend_contDiffOn_seg2 (a b c : ℂ) :
    ContDiffOn ℝ 1 (trianglePath a b c).extend (Icc (1/3 : ℝ) (2/3)) :=
  (((triSeg2_contDiff b c).of_le le_top).contDiffOn).congr fun _ ht =>
    trianglePath_extend_eq_seg2_on_Icc a b c ht

lemma trianglePath_extend_contDiffOn_seg3 (a b c : ℂ) :
    ContDiffOn ℝ 1 (trianglePath a b c).extend (Icc (2/3 : ℝ) 1) :=
  (((triSeg3_contDiff a c).of_le le_top).contDiffOn).congr fun _ ht =>
    trianglePath_extend_eq_seg3_on_Icc a b c ht

/-! ### `derivWithin` on each closed piece

We compute the within-derivative of `(trianglePath a b c).extend` on each
closed sub-interval. Each is the constant complex "velocity" of the
corresponding side: `3(b-a)`, `3(c-b)`, `3(a-c)`. -/

lemma trianglePath_extend_eventuallyEq_seg1_nhdsWithin (a b c : ℂ) {t : ℝ}
    (_ht : t ∈ Icc (0 : ℝ) (1/3)) :
    (trianglePath a b c).extend =ᶠ[𝓝[Icc (0 : ℝ) (1/3)] t] triSeg1 a b :=
  Filter.eventually_of_mem self_mem_nhdsWithin (trianglePath_extend_eq_seg1_on_Icc a b c)

lemma trianglePath_extend_eventuallyEq_seg2_nhdsWithin (a b c : ℂ) {t : ℝ}
    (_ht : t ∈ Icc (1/3 : ℝ) (2/3)) :
    (trianglePath a b c).extend =ᶠ[𝓝[Icc (1/3 : ℝ) (2/3)] t] triSeg2 b c :=
  Filter.eventually_of_mem self_mem_nhdsWithin (trianglePath_extend_eq_seg2_on_Icc a b c)

lemma trianglePath_extend_eventuallyEq_seg3_nhdsWithin (a b c : ℂ) {t : ℝ}
    (_ht : t ∈ Icc (2/3 : ℝ) 1) :
    (trianglePath a b c).extend =ᶠ[𝓝[Icc (2/3 : ℝ) 1] t] triSeg3 a c :=
  Filter.eventually_of_mem self_mem_nhdsWithin (trianglePath_extend_eq_seg3_on_Icc a b c)

lemma trianglePath_extend_derivWithin_seg1 (a b c : ℂ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (1/3)) :
    derivWithin (trianglePath a b c).extend (Icc (0 : ℝ) (1/3)) t = 3 * (b - a) := by
  have h_seg : HasDerivWithinAt (triSeg1 a b) (3 * (b - a)) (Icc (0 : ℝ) (1/3)) t :=
    (triSeg1_hasDerivAt a b t).hasDerivWithinAt
  have h_path : HasDerivWithinAt (trianglePath a b c).extend
      (3 * (b - a)) (Icc (0 : ℝ) (1/3)) t :=
    h_seg.congr_of_eventuallyEq
      (trianglePath_extend_eventuallyEq_seg1_nhdsWithin a b c ht)
      (trianglePath_extend_eq_seg1_on_Icc a b c ht)
  have hUDiff : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) (1/3)) t :=
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1/3)) t ht
  exact h_path.derivWithin hUDiff

lemma trianglePath_extend_derivWithin_seg2 (a b c : ℂ) {t : ℝ}
    (ht : t ∈ Icc (1/3 : ℝ) (2/3)) :
    derivWithin (trianglePath a b c).extend (Icc (1/3 : ℝ) (2/3)) t = 3 * (c - b) := by
  have h_seg : HasDerivWithinAt (triSeg2 b c) (3 * (c - b)) (Icc (1/3 : ℝ) (2/3)) t :=
    (triSeg2_hasDerivAt b c t).hasDerivWithinAt
  have h_path : HasDerivWithinAt (trianglePath a b c).extend
      (3 * (c - b)) (Icc (1/3 : ℝ) (2/3)) t :=
    h_seg.congr_of_eventuallyEq
      (trianglePath_extend_eventuallyEq_seg2_nhdsWithin a b c ht)
      (trianglePath_extend_eq_seg2_on_Icc a b c ht)
  have hUDiff : UniqueDiffWithinAt ℝ (Icc (1/3 : ℝ) (2/3)) t :=
    (uniqueDiffOn_Icc (by norm_num : (1/3 : ℝ) < 2/3)) t ht
  exact h_path.derivWithin hUDiff

lemma trianglePath_extend_derivWithin_seg3 (a b c : ℂ) {t : ℝ}
    (ht : t ∈ Icc (2/3 : ℝ) 1) :
    derivWithin (trianglePath a b c).extend (Icc (2/3 : ℝ) 1) t = 3 * (a - c) := by
  have h_seg : HasDerivWithinAt (triSeg3 a c) (3 * (a - c)) (Icc (2/3 : ℝ) 1) t :=
    (triSeg3_hasDerivAt a c t).hasDerivWithinAt
  have h_path : HasDerivWithinAt (trianglePath a b c).extend
      (3 * (a - c)) (Icc (2/3 : ℝ) 1) t :=
    h_seg.congr_of_eventuallyEq
      (trianglePath_extend_eventuallyEq_seg3_nhdsWithin a b c ht)
      (trianglePath_extend_eq_seg3_on_Icc a b c ht)
  have hUDiff : UniqueDiffWithinAt ℝ (Icc (2/3 : ℝ) 1) t :=
    (uniqueDiffOn_Icc (by norm_num : (2/3 : ℝ) < 1)) t ht
  exact h_path.derivWithin hUDiff

/-! ### Building the `ClosedPwC1Immersion` -/

/-- **The triangular contour** as a `ClosedPwC1Immersion`. Starts at the
vertex `a` and traverses the boundary `a → b → c → a`.

The parametrisation has breakpoints `{1/3, 2/3}` in `(0, 1)` and is
`C¹` on each closed piece with non-vanishing derivative. -/
noncomputable def triangleContour
    (a b c : ℂ) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
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
    · exact trianglePath_extend_contDiffOn_seg1 a b c
    · exact trianglePath_extend_contDiffOn_seg2 a b c
    · exact trianglePath_extend_contDiffOn_seg3 a b c
  derivWithin_ne_zero_pieces := by
    intro p q hcons t ht
    have hb_ne_a : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have hc_ne_b : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
    have ha_ne_c : a - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hca)
    have h_3_ne : (3 : ℂ) ≠ 0 := by norm_num
    -- The toPath of `trianglePC1Path` is `trianglePath` by definition.
    show derivWithin (trianglePath a b c).extend (Icc p q) t ≠ 0
    rcases triangleClosedPartition_consecutive_cases hcons with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [trianglePath_extend_derivWithin_seg1 a b c ht]
      exact mul_ne_zero h_3_ne hb_ne_a
    · rw [trianglePath_extend_derivWithin_seg2 a b c ht]
      exact mul_ne_zero h_3_ne hc_ne_b
    · rw [trianglePath_extend_derivWithin_seg3 a b c ht]
      exact mul_ne_zero h_3_ne ha_ne_c

/-! ## Cauchy's theorem on a triangle -/

/-- Helper: every convex combination of two points in a convex set is in the set.
This is `convex_iff_add_mem` applied. -/
lemma convex_combo_mem {U : Set ℂ} (hU : Convex ℝ U) {x y : ℂ}
    (hx : x ∈ U) (hy : y ∈ U) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ((1 - s : ℝ) : ℂ) * x + (s : ℂ) * y ∈ U := by
  have h_combo : (1 - s) • x + s • y ∈ U := by
    apply hU hx hy (by linarith : (0 : ℝ) ≤ 1 - s) hs0
    ring
  -- Convert smul to coercion-mul.
  have h_eq : ((1 - s : ℝ) : ℂ) * x + (s : ℂ) * y = (1 - s) • x + s • y := by
    simp [Complex.real_smul]
  rw [h_eq]; exact h_combo

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
  rw [trianglePath_extend_eq a b c t ht]
  by_cases ht1 : t ≤ 1/3
  · have hcoeff_nn : 0 ≤ 3 * t := by linarith [ht.1]
    have hcoeff_le : 3 * t ≤ 1 := by linarith [ht1]
    simp only [triangleFun, if_pos ht1, triSeg1]
    have h_eq : (1 - 3 * (t : ℂ)) * a + 3 * (t : ℂ) * b
        = ((1 - 3 * t : ℝ) : ℂ) * a + ((3 * t : ℝ) : ℂ) * b := by push_cast; ring
    rw [h_eq]
    exact convex_combo_mem hU_convex h_a_in_U h_b_in_U hcoeff_nn hcoeff_le
  · push Not at ht1
    by_cases ht2 : t ≤ 2/3
    · have hcoeff_nn : 0 ≤ 3 * t - 1 := by linarith
      have hcoeff_le : 3 * t - 1 ≤ 1 := by linarith
      simp only [triangleFun, if_neg (not_le.mpr ht1), if_pos ht2, triSeg2]
      have h_eq : (2 - 3 * (t : ℂ)) * b + (3 * (t : ℂ) - 1) * c
          = ((1 - (3 * t - 1) : ℝ) : ℂ) * b + ((3 * t - 1 : ℝ) : ℂ) * c := by
        push_cast; ring
      rw [h_eq]
      exact convex_combo_mem hU_convex h_b_in_U h_c_in_U hcoeff_nn hcoeff_le
    · push Not at ht2
      have hcoeff_nn : 0 ≤ 3 * t - 2 := by linarith
      have hcoeff_le : 3 * t - 2 ≤ 1 := by linarith [ht.2]
      simp only [triangleFun, if_neg (not_le.mpr ht1), if_neg (not_le.mpr ht2), triSeg3]
      have h_eq : (3 - 3 * (t : ℂ)) * c + (3 * (t : ℂ) - 2) * a
          = ((1 - (3 * t - 2) : ℝ) : ℂ) * c + ((3 * t - 2 : ℝ) : ℂ) * a := by
        push_cast; ring
      rw [h_eq]
      exact convex_combo_mem hU_convex h_c_in_U h_a_in_U hcoeff_nn hcoeff_le

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

/-! ## Decomposition into three segment integrals

The contour integral along `triangleContour a b c` decomposes as
`(a → b) + (b → c) + (c → a)`, each parameterised over `[0, 1]`. -/

/-- `HasDerivAt` of `(trianglePath a b c).extend` on the open first piece. -/
lemma trianglePath_extend_hasDerivAt_seg1 (a b c : ℂ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (1/3)) :
    HasDerivAt (trianglePath a b c).extend (3 * (b - a)) t :=
  (triSeg1_hasDerivAt a b t).congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun _ hs =>
      trianglePath_extend_eq_seg1_on_Icc a b c (Ioo_subset_Icc_self hs))

/-- `HasDerivAt` of `(trianglePath a b c).extend` on the open second piece. -/
lemma trianglePath_extend_hasDerivAt_seg2 (a b c : ℂ) {t : ℝ}
    (ht : t ∈ Ioo (1/3 : ℝ) (2/3)) :
    HasDerivAt (trianglePath a b c).extend (3 * (c - b)) t :=
  (triSeg2_hasDerivAt b c t).congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun _ hs =>
      trianglePath_extend_eq_seg2_on_Icc a b c (Ioo_subset_Icc_self hs))

/-- `HasDerivAt` of `(trianglePath a b c).extend` on the open third piece. -/
lemma trianglePath_extend_hasDerivAt_seg3 (a b c : ℂ) {t : ℝ}
    (ht : t ∈ Ioo (2/3 : ℝ) 1) :
    HasDerivAt (trianglePath a b c).extend (3 * (a - c)) t :=
  (triSeg3_hasDerivAt a c t).congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun _ hs =>
      trianglePath_extend_eq_seg3_on_Icc a b c (Ioo_subset_Icc_self hs))

/-- The derivative of `(trianglePath a b c).extend` on the open first piece. -/
lemma trianglePath_extend_deriv_seg1 (a b c : ℂ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (1/3)) :
    deriv (trianglePath a b c).extend t = 3 * (b - a) :=
  (trianglePath_extend_hasDerivAt_seg1 a b c ht).deriv

/-- The derivative of `(trianglePath a b c).extend` on the open second piece. -/
lemma trianglePath_extend_deriv_seg2 (a b c : ℂ) {t : ℝ}
    (ht : t ∈ Ioo (1/3 : ℝ) (2/3)) :
    deriv (trianglePath a b c).extend t = 3 * (c - b) :=
  (trianglePath_extend_hasDerivAt_seg2 a b c ht).deriv

/-- The derivative of `(trianglePath a b c).extend` on the open third piece. -/
lemma trianglePath_extend_deriv_seg3 (a b c : ℂ) {t : ℝ}
    (ht : t ∈ Ioo (2/3 : ℝ) 1) :
    deriv (trianglePath a b c).extend t = 3 * (a - c) :=
  (trianglePath_extend_hasDerivAt_seg3 a b c ht).deriv

/-- On the open first piece `Ioo 0 (1/3)`, the contour integrand of `f` along
`triangleContour` equals `f (triSeg1 a b t) * (3 * (b - a))`. -/
lemma triangleContour_integrand_seg1_ae (a b c : ℂ) (f : ℂ → ℂ) :
    ∀ᵐ t, t ∈ Ι (0 : ℝ) (1/3) →
      f ((trianglePath a b c).extend t) * deriv (trianglePath a b c).extend t
        = f (triSeg1 a b t) * (3 * (b - a)) := by
  filter_upwards [MeasureTheory.Measure.ae_ne volume (1/3 : ℝ)] with t ht hI
  rw [show Ι (0 : ℝ) (1/3) = Ioc 0 (1/3) from uIoc_of_le (by norm_num)] at hI
  have ht' : t ∈ Ioo (0 : ℝ) (1/3) := ⟨hI.1, lt_of_le_of_ne hI.2 ht⟩
  rw [trianglePath_extend_deriv_seg1 a b c ht',
      trianglePath_extend_eq_seg1_on_Icc a b c (Ioo_subset_Icc_self ht')]

/-- On the open second piece `Ioo (1/3) (2/3)`, the contour integrand of `f` along
`triangleContour` equals `f (triSeg2 b c t) * (3 * (c - b))`. -/
lemma triangleContour_integrand_seg2_ae (a b c : ℂ) (f : ℂ → ℂ) :
    ∀ᵐ t, t ∈ Ι (1/3 : ℝ) (2/3) →
      f ((trianglePath a b c).extend t) * deriv (trianglePath a b c).extend t
        = f (triSeg2 b c t) * (3 * (c - b)) := by
  filter_upwards [MeasureTheory.Measure.ae_ne volume (2/3 : ℝ)] with t ht hI
  rw [show Ι (1/3 : ℝ) (2/3) = Ioc (1/3) (2/3) from uIoc_of_le (by norm_num)] at hI
  have ht' : t ∈ Ioo (1/3 : ℝ) (2/3) := ⟨hI.1, lt_of_le_of_ne hI.2 ht⟩
  rw [trianglePath_extend_deriv_seg2 a b c ht',
      trianglePath_extend_eq_seg2_on_Icc a b c (Ioo_subset_Icc_self ht')]

/-- On the open third piece `Ioo (2/3) 1`, the contour integrand of `f` along
`triangleContour` equals `f (triSeg3 a c t) * (3 * (a - c))`. -/
lemma triangleContour_integrand_seg3_ae (a b c : ℂ) (f : ℂ → ℂ) :
    ∀ᵐ t, t ∈ Ι (2/3 : ℝ) 1 →
      f ((trianglePath a b c).extend t) * deriv (trianglePath a b c).extend t
        = f (triSeg3 a c t) * (3 * (a - c)) := by
  filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ)] with t ht hI
  rw [show Ι (2/3 : ℝ) 1 = Ioc (2/3) 1 from uIoc_of_le (by norm_num)] at hI
  have ht' : t ∈ Ioo (2/3 : ℝ) 1 := ⟨hI.1, lt_of_le_of_ne hI.2 ht⟩
  rw [trianglePath_extend_deriv_seg3 a b c ht',
      trianglePath_extend_eq_seg3_on_Icc a b c (Ioo_subset_Icc_self ht')]

/-! ### Continuity helpers for the segment integrands

If `f` is continuous on the image of the triangle path, then the
"segment integrand" `t ↦ f (triSeg_i ...) * (3 * v_i)` (where `v_i` is the
segment velocity) is continuous on the corresponding closed sub-interval. -/

/-- The image of `triSeg1 a b` on `Icc 0 (1/3)` lies inside the image of the
triangle path on `Icc 0 1`. -/
lemma triSeg1_image_subset_path_image (a b c : ℂ) :
    triSeg1 a b '' Icc (0 : ℝ) (1/3)
      ⊆ (trianglePath a b c).extend '' Icc (0 : ℝ) 1 := by
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, ⟨ht.1, le_trans ht.2 (by norm_num)⟩,
    trianglePath_extend_eq_seg1_on_Icc a b c ht⟩

/-- The image of `triSeg2 b c` on `Icc (1/3) (2/3)` lies inside the image of the
triangle path on `Icc 0 1`. -/
lemma triSeg2_image_subset_path_image (a b c : ℂ) :
    triSeg2 b c '' Icc (1/3 : ℝ) (2/3)
      ⊆ (trianglePath a b c).extend '' Icc (0 : ℝ) 1 := by
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, ⟨le_trans (by norm_num) ht.1, le_trans ht.2 (by norm_num)⟩,
    trianglePath_extend_eq_seg2_on_Icc a b c ht⟩

/-- The image of `triSeg3 a c` on `Icc (2/3) 1` lies inside the image of the
triangle path on `Icc 0 1`. -/
lemma triSeg3_image_subset_path_image (a b c : ℂ) :
    triSeg3 a c '' Icc (2/3 : ℝ) 1
      ⊆ (trianglePath a b c).extend '' Icc (0 : ℝ) 1 := by
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, ⟨le_trans (by norm_num) ht.1, ht.2⟩,
    trianglePath_extend_eq_seg3_on_Icc a b c ht⟩

/-- If `f` is continuous on the image of the triangle path on `Icc 0 1`, then
`fun t ↦ f (triSeg1 a b t) * (3 * (b - a))` is continuous on `Icc 0 (1/3)`. -/
lemma seg1_integrand_continuousOn (a b c : ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f ((trianglePath a b c).extend '' Icc (0 : ℝ) 1)) :
    ContinuousOn (fun t : ℝ => f (triSeg1 a b t) * (3 * (b - a))) (Icc (0 : ℝ) (1/3)) :=
  ((hf.comp (triSeg1_continuous a b).continuousOn
    (fun _ ht => triSeg1_image_subset_path_image a b c (mem_image_of_mem _ ht))).mul
    continuousOn_const)

/-- If `f` is continuous on the image of the triangle path on `Icc 0 1`, then
`fun t ↦ f (triSeg2 b c t) * (3 * (c - b))` is continuous on `Icc (1/3) (2/3)`. -/
lemma seg2_integrand_continuousOn (a b c : ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f ((trianglePath a b c).extend '' Icc (0 : ℝ) 1)) :
    ContinuousOn (fun t : ℝ => f (triSeg2 b c t) * (3 * (c - b))) (Icc (1/3 : ℝ) (2/3)) :=
  ((hf.comp (triSeg2_continuous b c).continuousOn
    (fun _ ht => triSeg2_image_subset_path_image a b c (mem_image_of_mem _ ht))).mul
    continuousOn_const)

/-- If `f` is continuous on the image of the triangle path on `Icc 0 1`, then
`fun t ↦ f (triSeg3 a c t) * (3 * (a - c))` is continuous on `Icc (2/3) 1`. -/
lemma seg3_integrand_continuousOn (a b c : ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f ((trianglePath a b c).extend '' Icc (0 : ℝ) 1)) :
    ContinuousOn (fun t : ℝ => f (triSeg3 a c t) * (3 * (a - c))) (Icc (2/3 : ℝ) 1) :=
  ((hf.comp (triSeg3_continuous a c).continuousOn
    (fun _ ht => triSeg3_image_subset_path_image a b c (mem_image_of_mem _ ht))).mul
    continuousOn_const)

/-! ### Integrability of the original integrand on each sub-interval -/

lemma triangleContour_integrand_intervalIntegrable_seg1 (a b c : ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f ((trianglePath a b c).extend '' Icc (0 : ℝ) 1)) :
    IntervalIntegrable
      (fun t => f ((trianglePath a b c).extend t) * deriv (trianglePath a b c).extend t)
      volume 0 (1/3) := by
  have hg_cont : ContinuousOn (fun t : ℝ => f (triSeg1 a b t) * (3 * (b - a)))
      (uIcc (0 : ℝ) (1/3)) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/3)]
    exact seg1_integrand_continuousOn a b c hf
  have hg_int : IntervalIntegrable
      (fun t : ℝ => f (triSeg1 a b t) * (3 * (b - a))) volume 0 (1/3) :=
    hg_cont.intervalIntegrable
  rw [intervalIntegrable_congr_ae
    ((ae_restrict_iff' measurableSet_uIoc).mpr (triangleContour_integrand_seg1_ae a b c f))]
  exact hg_int

lemma triangleContour_integrand_intervalIntegrable_seg2 (a b c : ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f ((trianglePath a b c).extend '' Icc (0 : ℝ) 1)) :
    IntervalIntegrable
      (fun t => f ((trianglePath a b c).extend t) * deriv (trianglePath a b c).extend t)
      volume (1/3) (2/3) := by
  have hg_cont : ContinuousOn (fun t : ℝ => f (triSeg2 b c t) * (3 * (c - b)))
      (uIcc (1/3 : ℝ) (2/3)) := by
    rw [uIcc_of_le (by norm_num : (1/3:ℝ) ≤ 2/3)]
    exact seg2_integrand_continuousOn a b c hf
  have hg_int : IntervalIntegrable
      (fun t : ℝ => f (triSeg2 b c t) * (3 * (c - b))) volume (1/3) (2/3) :=
    hg_cont.intervalIntegrable
  rw [intervalIntegrable_congr_ae
    ((ae_restrict_iff' measurableSet_uIoc).mpr (triangleContour_integrand_seg2_ae a b c f))]
  exact hg_int

lemma triangleContour_integrand_intervalIntegrable_seg3 (a b c : ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f ((trianglePath a b c).extend '' Icc (0 : ℝ) 1)) :
    IntervalIntegrable
      (fun t => f ((trianglePath a b c).extend t) * deriv (trianglePath a b c).extend t)
      volume (2/3) 1 := by
  have hg_cont : ContinuousOn (fun t : ℝ => f (triSeg3 a c t) * (3 * (a - c)))
      (uIcc (2/3 : ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (2/3:ℝ) ≤ 1)]
    exact seg3_integrand_continuousOn a b c hf
  have hg_int : IntervalIntegrable
      (fun t : ℝ => f (triSeg3 a c t) * (3 * (a - c))) volume (2/3) 1 :=
    hg_cont.intervalIntegrable
  rw [intervalIntegrable_congr_ae
    ((ae_restrict_iff' measurableSet_uIoc).mpr (triangleContour_integrand_seg3_ae a b c f))]
  exact hg_int

/-! ### Each segment integral equals the corresponding "standard form" integral

After an affine change of variables `t = (k + s)/3`, the integral on the `k`-th
sub-interval becomes `∫₀¹ f(v + s • Δ) * Δ ds`, where `v` is the starting
vertex and `Δ` is the segment direction. -/

lemma triangleContour_seg1_integral_eq (a b c : ℂ) (f : ℂ → ℂ) :
    (∫ t in (0 : ℝ)..(1/3),
        f ((trianglePath a b c).extend t) * deriv (trianglePath a b c).extend t)
      = ∫ s in (0 : ℝ)..1, f (a + s • (b - a)) * (b - a) := by
  -- Step 1: rewrite the integrand using a.e. equality to a "smooth" form.
  rw [intervalIntegral.integral_congr_ae (triangleContour_integrand_seg1_ae a b c f)]
  -- Step 2: change of variable `t = s/3`, mapping `[0, 1]` to `[0, 1/3]`.
  have h_cov := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (f := fun y => f (triSeg1 a b y) * (3 * (b - a))) (1/3 : ℝ)
  simp only [mul_zero, mul_one] at h_cov
  rw [← h_cov, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro x _hx
  show (1/3 : ℝ) • (f (triSeg1 a b ((1/3) * x)) * (3 * (b - a)))
    = f (a + x • (b - a)) * (b - a)
  rw [Complex.real_smul, Complex.real_smul]
  simp only [triSeg1]
  push_cast
  ring_nf

lemma triangleContour_seg2_integral_eq (a b c : ℂ) (f : ℂ → ℂ) :
    (∫ t in (1/3 : ℝ)..(2/3),
        f ((trianglePath a b c).extend t) * deriv (trianglePath a b c).extend t)
      = ∫ s in (0 : ℝ)..1, f (b + s • (c - b)) * (c - b) := by
  rw [intervalIntegral.integral_congr_ae (triangleContour_integrand_seg2_ae a b c f)]
  have h_cov := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
    (f := fun y => f (triSeg2 b c y) * (3 * (c - b))) (1/3 : ℝ) (1/3 : ℝ)
  simp only [mul_zero, mul_one, zero_add, show (1/3 : ℝ) + 1/3 = 2/3 by norm_num] at h_cov
  rw [← h_cov, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro x _hx
  show (1/3 : ℝ) • (f (triSeg2 b c ((1/3) * x + 1/3)) * (3 * (c - b)))
    = f (b + x • (c - b)) * (c - b)
  rw [Complex.real_smul, Complex.real_smul]
  simp only [triSeg2]
  push_cast
  ring_nf

lemma triangleContour_seg3_integral_eq (a b c : ℂ) (f : ℂ → ℂ) :
    (∫ t in (2/3 : ℝ)..1,
        f ((trianglePath a b c).extend t) * deriv (trianglePath a b c).extend t)
      = ∫ s in (0 : ℝ)..1, f (c + s • (a - c)) * (a - c) := by
  rw [intervalIntegral.integral_congr_ae (triangleContour_integrand_seg3_ae a b c f)]
  have h_cov := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
    (f := fun y => f (triSeg3 a c y) * (3 * (a - c))) (1/3 : ℝ) (2/3 : ℝ)
  simp only [mul_zero, mul_one, zero_add, show (1/3 : ℝ) + 2/3 = 1 by norm_num] at h_cov
  rw [← h_cov, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro x _hx
  show (1/3 : ℝ) • (f (triSeg3 a c ((1/3) * x + 2/3)) * (3 * (a - c)))
    = f (c + x • (a - c)) * (a - c)
  rw [Complex.real_smul, Complex.real_smul]
  simp only [triSeg3]
  push_cast
  ring_nf

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
  -- Unfold the contour integral. The triangle's path is `(trianglePath a b c).extend`.
  show ∫ t in (0:ℝ)..1, f ((trianglePath a b c).extend t) * deriv (trianglePath a b c).extend t
    = _
  -- `hf` becomes `ContinuousOn f ((trianglePath a b c).extend '' Icc 0 1)`.
  have hf' : ContinuousOn f ((trianglePath a b c).extend '' Icc (0 : ℝ) 1) := hf
  -- Split the integral at `1/3` and `2/3`.
  have h_int1 := triangleContour_integrand_intervalIntegrable_seg1 a b c hf'
  have h_int2 := triangleContour_integrand_intervalIntegrable_seg2 a b c hf'
  have h_int3 := triangleContour_integrand_intervalIntegrable_seg3 a b c hf'
  rw [← intervalIntegral.integral_add_adjacent_intervals h_int1 (h_int2.trans h_int3),
      ← intervalIntegral.integral_add_adjacent_intervals h_int2 h_int3,
      triangleContour_seg1_integral_eq a b c f,
      triangleContour_seg2_integral_eq a b c f,
      triangleContour_seg3_integral_eq a b c f, ← add_assoc]

end LeanModularForms

end

end
