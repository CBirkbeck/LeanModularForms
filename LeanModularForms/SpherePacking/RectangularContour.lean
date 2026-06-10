/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Convex.Star
public import LeanModularForms.ForMathlib.NullHomologous
public import LeanModularForms.ForMathlib.PaperPwC1Immersion
public import LeanModularForms.SpherePacking.AffineSegment
public import LeanModularForms.SpherePacking.CauchyCorollaries

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
* `contourIntegral_rectangleContour_eq` — the contour integral decomposes into
  the four segment integrals `∫ s in 0..1, f (p + s • (q - p)) * (q - p)`.

The parametrisation glues the four sides — each an `affineSegment` at rate `4`
— at the breakpoints `{1/4, 1/2, 3/4}`; all segment calculus comes from
`AffineSegment.lean`.

## Mathlib-friendliness

The results are stated in maximal generality (no sphere-packing-specific
content). The intention is that they can later move into mathlib as part of a
clean upstream of the HW 3.3 framework. -/

open Complex Set Filter Topology MeasureTheory

@[expose] public section

noncomputable section

namespace LeanModularForms

section Rectangle

variable (a b c d : ℝ)

/-- The boundary of the rectangle `[a, b] × [c, d]`, parameterised on `[0, 1]`
counterclockwise from the bottom-left corner — bottom, right, top, left — with
breakpoints at `1/4`, `1/2`, `3/4`. Outside `[0, 1]` the value is whatever the
last segment gives; we only ever use the restriction to `Icc 0 1`. -/
def rectangleFun : ℝ → ℂ :=
  ifLE (1/4) (affineSegment 4 0 ((a : ℂ) + c * I) ((b : ℂ) + c * I))
    (ifLE (1/2) (affineSegment 4 1 ((b : ℂ) + c * I) ((b : ℂ) + d * I))
      (ifLE (3/4) (affineSegment 4 2 ((b : ℂ) + d * I) ((a : ℂ) + d * I))
        (affineSegment 4 3 ((a : ℂ) + d * I) ((a : ℂ) + c * I))))

lemma rectangleFun_zero : rectangleFun a b c d 0 = (a : ℂ) + (c : ℂ) * I := by
  norm_num [rectangleFun, ifLE, affineSegment]

lemma rectangleFun_one : rectangleFun a b c d 1 = (a : ℂ) + (c : ℂ) * I := by
  norm_num [rectangleFun, ifLE, affineSegment]

@[fun_prop]
theorem rectangleFun_continuous : Continuous (rectangleFun a b c d) :=
  ifLE_continuous (affineSegment_continuous _ _ _ _)
    (ifLE_continuous (affineSegment_continuous _ _ _ _)
      (ifLE_continuous (affineSegment_continuous _ _ _ _) (affineSegment_continuous _ _ _ _)
        (by norm_num [affineSegment, Complex.ext_iff]))
      (by norm_num [ifLE, affineSegment, Complex.ext_iff]))
    (by norm_num [ifLE, affineSegment, Complex.ext_iff])

/-- The interior breakpoints of `rectangleFun`: `{1/4, 1/2, 3/4}`. -/
def rectanglePartition : Finset ℝ := {1/4, 1/2, 3/4}

lemma rectanglePartition_subset_Ioo : (rectanglePartition : Set ℝ) ⊆ Ioo 0 1 := by
  intro x hx
  simp only [rectanglePartition, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
    mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> norm_num

/-- The closed partition `{0, 1/4, 1/2, 3/4, 1}`. -/
def rectangleClosedPartition : Finset ℝ := {0, 1/4, 1/2, 3/4, 1}

lemma rectangleClosedPartition_subset_Icc : (rectangleClosedPartition : Set ℝ) ⊆ Icc 0 1 := by
  intro x hx
  simp only [rectangleClosedPartition, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
    mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma rectangleClosedPartition_eq :
    rectangleClosedPartition = insert 0 (insert 1 rectanglePartition) := by
  ext x
  simp only [rectangleClosedPartition, rectanglePartition, Finset.mem_insert,
    Finset.mem_singleton]
  tauto

private lemma rectangleFun_eventuallyEq_off {t : ℝ} (htp : t ∉ rectanglePartition) :
    ∃ r k p q, rectangleFun a b c d =ᶠ[𝓝 t] affineSegment r k p q := by
  simp only [rectanglePartition, Finset.mem_insert, Finset.mem_singleton] at htp
  push Not at htp
  obtain ⟨ht1, ht2, ht3⟩ := htp
  rcases lt_or_gt_of_ne ht1 with h1 | h1
  · exact ⟨_, _, _, _, ifLE_eventuallyEq_left h1⟩
  rcases lt_or_gt_of_ne ht2 with h2 | h2
  · exact ⟨_, _, _, _, (ifLE_eventuallyEq_right h1).trans (ifLE_eventuallyEq_left h2)⟩
  rcases lt_or_gt_of_ne ht3 with h3 | h3
  · exact ⟨_, _, _, _, (ifLE_eventuallyEq_right h1).trans
      ((ifLE_eventuallyEq_right h2).trans (ifLE_eventuallyEq_left h3))⟩
  exact ⟨_, _, _, _, (ifLE_eventuallyEq_right h1).trans
    ((ifLE_eventuallyEq_right h2).trans (ifLE_eventuallyEq_right h3))⟩

/-- The rectangular boundary as a mathlib `Path` from the bottom-left corner back
to itself. -/
def rectanglePath : Path ((a : ℂ) + (c : ℂ) * I) ((a : ℂ) + (c : ℂ) * I) where
  toFun t := rectangleFun a b c d t
  continuous_toFun := (rectangleFun_continuous a b c d).continuousOn.restrict
  source' := rectangleFun_zero a b c d
  target' := rectangleFun_one a b c d

private lemma rectanglePath_extend_eq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (rectanglePath a b c d).extend t = rectangleFun a b c d t :=
  Path.extend_apply _ ht

private lemma rectanglePath_extend_eventuallyEq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (rectanglePath a b c d).extend =ᶠ[𝓝 t] rectangleFun a b c d :=
  Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs =>
    rectanglePath_extend_eq a b c d s (Ioo_subset_Icc_self hs)

private lemma rectanglePath_extend_eventuallyEq_off {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (htp : t ∉ rectanglePartition) :
    ∃ r k p q, (rectanglePath a b c d).extend =ᶠ[𝓝 t] affineSegment r k p q := by
  obtain ⟨r, k, p, q, h⟩ := rectangleFun_eventuallyEq_off a b c d htp
  exact ⟨r, k, p, q, (rectanglePath_extend_eventuallyEq a b c d ht).trans h⟩

/-- The rectangular boundary as a `PiecewiseC1Path`. -/
def rectanglePC1Path : PiecewiseC1Path ((a : ℂ) + (c : ℂ) * I) ((a : ℂ) + (c : ℂ) * I) where
  toFun := (rectanglePath a b c d).extend
  source := (rectanglePath a b c d).extend_zero
  target := (rectanglePath a b c d).extend_one
  continuous_toFun := (rectanglePath a b c d).continuous_extend.continuousOn
  toPath := rectanglePath a b c d
  toPath_extend_eq_toFun := fun _ _ => rfl
  partition := rectanglePartition
  partition_subset := rectanglePartition_subset_Ioo
  differentiable_off := fun t ht htp => by
    obtain ⟨_, _, _, _, h⟩ := rectanglePath_extend_eventuallyEq_off a b c d ht htp
    exact affineSegment_differentiableAt_of_eventuallyEq h
  deriv_continuous_off := fun t ht htp => by
    obtain ⟨_, _, _, _, h⟩ := rectanglePath_extend_eventuallyEq_off a b c d ht htp
    exact affineSegment_deriv_continuousAt_of_eventuallyEq h

/-- On `[0, 1/4]` the extended rectangle path is the bottom side. -/
lemma rectanglePath_extend_eqOn_seg1 :
    EqOn (rectanglePath a b c d).extend
      (affineSegment 4 0 ((a : ℂ) + c * I) ((b : ℂ) + c * I)) (Icc 0 (1/4 : ℝ)) := fun t ht =>
  (rectanglePath_extend_eq a b c d t ⟨ht.1, ht.2.trans (by norm_num)⟩).trans
    (ifLE_apply_of_le ht.2)

/-- On `[1/4, 1/2]` the extended rectangle path is the right side. -/
lemma rectanglePath_extend_eqOn_seg2 :
    EqOn (rectanglePath a b c d).extend
      (affineSegment 4 1 ((b : ℂ) + c * I) ((b : ℂ) + d * I)) (Icc (1/4 : ℝ) (1/2)) :=
  fun t ht =>
    (rectanglePath_extend_eq a b c d t
      ⟨le_trans (by norm_num) ht.1, ht.2.trans (by norm_num)⟩).trans
      ((ifLE_eqOn_right (by norm_num [ifLE, affineSegment, Complex.ext_iff]) ht.1).trans
        (ifLE_apply_of_le ht.2))

/-- On `[1/2, 3/4]` the extended rectangle path is the top side. -/
lemma rectanglePath_extend_eqOn_seg3 :
    EqOn (rectanglePath a b c d).extend
      (affineSegment 4 2 ((b : ℂ) + d * I) ((a : ℂ) + d * I)) (Icc (1/2 : ℝ) (3/4)) :=
  fun t ht =>
    (rectanglePath_extend_eq a b c d t
      ⟨le_trans (by norm_num) ht.1, ht.2.trans (by norm_num)⟩).trans
      ((ifLE_eqOn_right (by norm_num [ifLE, affineSegment, Complex.ext_iff])
          (le_trans (by norm_num) ht.1)).trans
        ((ifLE_eqOn_right (by norm_num [ifLE, affineSegment, Complex.ext_iff]) ht.1).trans
          (ifLE_apply_of_le ht.2)))

/-- On `[3/4, 1]` the extended rectangle path is the left side. -/
lemma rectanglePath_extend_eqOn_seg4 :
    EqOn (rectanglePath a b c d).extend
      (affineSegment 4 3 ((a : ℂ) + d * I) ((a : ℂ) + c * I)) (Icc (3/4 : ℝ) 1) :=
  fun t ht =>
    (rectanglePath_extend_eq a b c d t ⟨le_trans (by norm_num) ht.1, ht.2⟩).trans
      ((ifLE_eqOn_right (by norm_num [ifLE, affineSegment, Complex.ext_iff])
          (le_trans (by norm_num) ht.1)).trans
        ((ifLE_eqOn_right (by norm_num [ifLE, affineSegment, Complex.ext_iff])
            (le_trans (by norm_num) ht.1)).trans
          (ifLE_eqOn_right (by norm_num [affineSegment, Complex.ext_iff]) ht.1)))

private lemma rectangleClosedPartition_consecutive_cases {p q : ℝ}
    (h : rectangleClosedPartition.IsConsecutive p q) :
    (p = 0 ∧ q = 1/4) ∨ (p = 1/4 ∧ q = 1/2) ∨ (p = 1/2 ∧ q = 3/4) ∨ (p = 3/4 ∧ q = 1) := by
  obtain ⟨hp, hq, hpq, hno⟩ := h
  have h1 := hno (1/4) (by norm_num [rectangleClosedPartition])
  have h2 := hno (1/2) (by norm_num [rectangleClosedPartition])
  have h3 := hno (3/4) (by norm_num [rectangleClosedPartition])
  simp only [rectangleClosedPartition, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl | rfl <;>
    (revert hpq h1 h2 h3; norm_num [mem_Ioo])

/-- **The rectangular contour** as a `ClosedPwC1Immersion`. Starts at the
bottom-left corner `a + c·I` and traverses the boundary counterclockwise:
bottom → right → top → left.

The parametrisation has breakpoints `{1/4, 1/2, 3/4}` in `(0, 1)` and is
`C¹` on each closed piece with non-vanishing derivative. -/
def rectangleContour (hab : a < b) (hcd : c < d) :
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
    · exact affineSegment_contDiffOn_of_eqOn (rectanglePath_extend_eqOn_seg1 a b c d)
    · exact affineSegment_contDiffOn_of_eqOn (rectanglePath_extend_eqOn_seg2 a b c d)
    · exact affineSegment_contDiffOn_of_eqOn (rectanglePath_extend_eqOn_seg3 a b c d)
    · exact affineSegment_contDiffOn_of_eqOn (rectanglePath_extend_eqOn_seg4 a b c d)
  derivWithin_ne_zero_pieces := by
    intro p q hcons t ht
    show derivWithin (rectanglePath a b c d).extend (Icc p q) t ≠ 0
    rcases rectangleClosedPartition_consecutive_cases hcons with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [affineSegment_derivWithin_of_eqOn (rectanglePath_extend_eqOn_seg1 a b c d)
        (by norm_num) ht]
      exact smul_ne_zero (by norm_num) (sub_ne_zero.mpr (by simp [Complex.ext_iff, hab.ne']))
    · rw [affineSegment_derivWithin_of_eqOn (rectanglePath_extend_eqOn_seg2 a b c d)
        (by norm_num) ht]
      exact smul_ne_zero (by norm_num) (sub_ne_zero.mpr (by simp [Complex.ext_iff, hcd.ne']))
    · rw [affineSegment_derivWithin_of_eqOn (rectanglePath_extend_eqOn_seg3 a b c d)
        (by norm_num) ht]
      exact smul_ne_zero (by norm_num) (sub_ne_zero.mpr (by simp [Complex.ext_iff, hab.ne]))
    · rw [affineSegment_derivWithin_of_eqOn (rectanglePath_extend_eqOn_seg4 a b c d)
        (by norm_num) ht]
      exact smul_ne_zero (by norm_num) (sub_ne_zero.mpr (by simp [Complex.ext_iff, hcd.ne]))

end Rectangle

private lemma realCLM_eq_re_mul {f : ℂ →L[ℝ] ℝ} (w : ℂ) :
    f w = ((Complex.mk (f 1) (-(f I))) * w).re := by
  have hf_decomp : f w = w.re * f 1 + w.im * f I := by
    have hw : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I := by simp [Complex.real_smul]
    conv_lhs => rw [hw]
    rw [map_add, map_smul, map_smul]
    simp [smul_eq_mul]
  rw [hf_decomp, Complex.mul_re]
  ring

private lemma realCLM_dir_ne_zero {f : ℂ →L[ℝ] ℝ} {z w : ℂ} (h : f z < f w) :
    Complex.mk (f 1) (-(f I)) ≠ 0 := fun hα => by
  have hf_zero : ∀ u : ℂ, f u = 0 := fun u => by
    rw [realCLM_eq_re_mul u, hα, zero_mul, Complex.zero_re]
  rw [hf_zero w, hf_zero z] at h
  exact lt_irrefl _ h

private lemma hasDerivAt_log_mul_sub_const {α z : ℂ} (hα : α ≠ 0) {w : ℂ}
    (h : 0 < (α * (w - z)).re) :
    HasDerivAt (fun u => Complex.log (α * (u - z))) (w - z)⁻¹ w := by
  have h_log := (((hasDerivAt_id w).sub_const z).const_mul α).clog (Or.inl h)
  rwa [mul_one, div_mul_cancel_left₀ hα] at h_log

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
    obtain ⟨f, h_sep⟩ := geometric_hahn_banach_point_open hU_convex hU_open hz
    set α : ℂ := Complex.mk (f 1) (-(f I)) with hα_def
    have hα_ne : α ≠ 0 :=
      realCLM_dir_ne_zero (h_sep _ (h_image 0 ⟨le_rfl, zero_le_one⟩))
    have hα_eq : ∀ w : ℂ, f w = (α * w).re := fun w => realCLM_eq_re_mul w
    have h_image_re_pos : ∀ t ∈ Icc (0 : ℝ) 1,
        0 < (α * (γ.toPwC1Immersion.toPiecewiseC1Path t - z)).re := fun t ht => by
      rw [← hα_eq, map_sub]
      linarith [h_sep _ (h_image t ht)]
    obtain ⟨δ, hδ_pos, h_dist_lb⟩ := avoids_delta_bound γ.toPwC1Immersion.toPiecewiseC1Path z
      fun t ht heq => lt_irrefl _ (heq ▸ h_sep _ (h_image t ht))
    obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
    have h_int : IntervalIntegrable
        (fun t => (γ.toPwC1Immersion.toPiecewiseC1Path t - z)⁻¹ *
          deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t) volume 0 1 :=
      (intervalIntegrable_div_lipschitz γ.toPwC1Immersion.toPiecewiseC1Path hδ_pos h_dist_lb
        hLip).congr fun t _ => by rw [div_eq_mul_inv, mul_comm]; rfl
    have h_contour_zero :
        γ.toPwC1Immersion.toPiecewiseC1Path.contourIntegral (fun w => (w - z)⁻¹) = 0 :=
      PiecewiseC1Path.contourIntegral_eq_zero_of_hasDerivAt_of_closed
        γ.toPwC1Immersion.toPiecewiseC1Path rfl h_image_re_pos
        (fun w hw => hasDerivAt_log_mul_sub_const hα_ne hw) h_int
    rw [(hasGeneralizedWindingNumber_of_avoids ⟨δ, hδ_pos, h_dist_lb⟩).eq, h_contour_zero,
      mul_zero]

private lemma horizontal_segment_mem {a b c d x₁ x₂ y : ℝ} (hx₁ : x₁ ∈ Icc a b)
    (hx₂ : x₂ ∈ Icc a b) (hy : y ∈ Icc c d) {U : Set ℂ}
    (h_corners : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, (x : ℂ) + (y : ℂ) * I ∈ U)
    {r k t : ℝ} (h0 : 0 ≤ r * t - k) (h1 : r * t - k ≤ 1) :
    affineSegment r k ((x₁ : ℂ) + y * I) ((x₂ : ℂ) + y * I) t ∈ U := by
  have h_eq : affineSegment r k ((x₁ : ℂ) + y * I) ((x₂ : ℂ) + y * I) t
      = ((x₁ + (r * t - k) * (x₂ - x₁) : ℝ) : ℂ) + (y : ℂ) * I := by
    simp only [affineSegment, Complex.real_smul]
    push_cast
    ring
  rw [h_eq]
  refine h_corners _ ⟨?_, ?_⟩ y hy
  · nlinarith [hx₁.1, hx₂.1]
  · nlinarith [hx₁.2, hx₂.2]

private lemma vertical_segment_mem {a b c d y₁ y₂ x : ℝ} (hy₁ : y₁ ∈ Icc c d)
    (hy₂ : y₂ ∈ Icc c d) (hx : x ∈ Icc a b) {U : Set ℂ}
    (h_corners : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, (x : ℂ) + (y : ℂ) * I ∈ U)
    {r k t : ℝ} (h0 : 0 ≤ r * t - k) (h1 : r * t - k ≤ 1) :
    affineSegment r k ((x : ℂ) + y₁ * I) ((x : ℂ) + y₂ * I) t ∈ U := by
  have h_eq : affineSegment r k ((x : ℂ) + y₁ * I) ((x : ℂ) + y₂ * I) t
      = (x : ℂ) + ((y₁ + (r * t - k) * (y₂ - y₁) : ℝ) : ℂ) * I := by
    simp only [affineSegment, Complex.real_smul]
    push_cast
    ring
  rw [h_eq]
  refine h_corners x hx _ ⟨?_, ?_⟩
  · nlinarith [hy₁.1, hy₂.1]
  · nlinarith [hy₁.2, hy₂.2]

/-- The image of the rectangular contour `rectangleContour a b c d` on `[0, 1]`
lies inside any set containing every point of the closed rectangle
`[a, b] × [c, d]`. Useful for applying Cauchy on the rectangle. -/
theorem rectangleContour_image_subset_rect
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {U : Set ℂ} (h_corners : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, (x : ℂ) + (y : ℂ) * I ∈ U) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      (rectangleContour a b c d hab hcd).toPwC1Immersion.toPiecewiseC1Path t ∈ U := by
  intro t ht
  show (rectanglePath a b c d).extend t ∈ U
  rcases le_or_gt t (1/4) with h1 | h1
  · rw [rectanglePath_extend_eqOn_seg1 a b c d ⟨ht.1, h1⟩]
    exact horizontal_segment_mem (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le)
      (left_mem_Icc.mpr hcd.le) h_corners (by linarith [ht.1]) (by linarith)
  rcases le_or_gt t (1/2) with h2 | h2
  · rw [rectanglePath_extend_eqOn_seg2 a b c d ⟨h1.le, h2⟩]
    exact vertical_segment_mem (left_mem_Icc.mpr hcd.le) (right_mem_Icc.mpr hcd.le)
      (right_mem_Icc.mpr hab.le) h_corners (by linarith) (by linarith)
  rcases le_or_gt t (3/4) with h3 | h3
  · rw [rectanglePath_extend_eqOn_seg3 a b c d ⟨h2.le, h3⟩]
    exact horizontal_segment_mem (right_mem_Icc.mpr hab.le) (left_mem_Icc.mpr hab.le)
      (right_mem_Icc.mpr hcd.le) h_corners (by linarith) (by linarith)
  · rw [rectanglePath_extend_eqOn_seg4 a b c d ⟨h3.le, ht.2⟩]
    exact vertical_segment_mem (right_mem_Icc.mpr hcd.le) (left_mem_Icc.mpr hcd.le)
      (left_mem_Icc.mpr hab.le) h_corners (by linarith) (by linarith [ht.2])

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
      = 0 :=
  cauchy_integral_zero_pwc1 hU_open hU_ne hf (rectangleContour a b c d hab hcd)
    (IsNullHomologous.of_convex_open _ hU_open hU_convex
      (rectangleContour_image_subset_rect hab hcd h_rect_in_U))
    (h_rect_in_U a (left_mem_Icc.mpr hab.le) c (left_mem_Icc.mpr hcd.le))

/-- **Decomposition of the contour integral over the rectangle into four segment
integrals.** For `f` continuous on the image of the rectangle, the contour
integral of `f` along the boundary of `rectangleContour a b c d hab hcd`
equals the sum of the four segment integrals
`(bottom: a+ci → b+ci) + (right: b+ci → b+di) + (top: b+di → a+di) + (left: a+di → a+ci)`,
each parameterised on `[0, 1]` as `(p, q) ↦ ∫ s in 0..1, f (p + s • (q - p)) * (q - p)`. -/
theorem contourIntegral_rectangleContour_eq
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {f : ℂ → ℂ}
    (hf : ContinuousOn f
      ((rectangleContour a b c d hab hcd).toPwC1Immersion.toPiecewiseC1Path '' Icc (0:ℝ) 1)) :
    (rectangleContour a b c d hab hcd).toPwC1Immersion.toPiecewiseC1Path.contourIntegral f
      = (∫ s in (0:ℝ)..1, f ((a : ℂ) + c * I + s • (((b : ℂ) + c * I) - ((a : ℂ) + c * I))) *
                          (((b : ℂ) + c * I) - ((a : ℂ) + c * I)))
      + (∫ s in (0:ℝ)..1, f ((b : ℂ) + c * I + s • (((b : ℂ) + d * I) - ((b : ℂ) + c * I))) *
                          (((b : ℂ) + d * I) - ((b : ℂ) + c * I)))
      + (∫ s in (0:ℝ)..1, f ((b : ℂ) + d * I + s • (((a : ℂ) + d * I) - ((b : ℂ) + d * I))) *
                          (((a : ℂ) + d * I) - ((b : ℂ) + d * I)))
      + (∫ s in (0:ℝ)..1, f ((a : ℂ) + d * I + s • (((a : ℂ) + c * I) - ((a : ℂ) + d * I))) *
                          (((a : ℂ) + c * I) - ((a : ℂ) + d * I))) := by
  show ∫ t in (0:ℝ)..1, f ((rectanglePath a b c d).extend t) *
      deriv (rectanglePath a b c d).extend t = _
  have hf' : ContinuousOn f ((rectanglePath a b c d).extend '' Icc (0 : ℝ) 1) := hf
  have h₁ := affineSegment_integrand_intervalIntegrable_of_eqOn
    (rectanglePath_extend_eqOn_seg1 a b c d) (by norm_num)
    (Icc_subset_Icc le_rfl (by norm_num)) hf'
  have h₂ := affineSegment_integrand_intervalIntegrable_of_eqOn
    (rectanglePath_extend_eqOn_seg2 a b c d) (by norm_num)
    (Icc_subset_Icc (by norm_num) (by norm_num)) hf'
  have h₃ := affineSegment_integrand_intervalIntegrable_of_eqOn
    (rectanglePath_extend_eqOn_seg3 a b c d) (by norm_num)
    (Icc_subset_Icc (by norm_num) (by norm_num)) hf'
  have h₄ := affineSegment_integrand_intervalIntegrable_of_eqOn
    (rectanglePath_extend_eqOn_seg4 a b c d) (by norm_num)
    (Icc_subset_Icc (by norm_num) le_rfl) hf'
  rw [← intervalIntegral.integral_add_adjacent_intervals h₁ ((h₂.trans h₃).trans h₄),
    ← intervalIntegral.integral_add_adjacent_intervals h₂ (h₃.trans h₄),
    ← intervalIntegral.integral_add_adjacent_intervals h₃ h₄,
    affineSegment_integral_eq_of_eqOn (by norm_num) (by norm_num) (by norm_num)
      (rectanglePath_extend_eqOn_seg1 a b c d) f,
    affineSegment_integral_eq_of_eqOn (by norm_num) (by norm_num) (by norm_num)
      (rectanglePath_extend_eqOn_seg2 a b c d) f,
    affineSegment_integral_eq_of_eqOn (by norm_num) (by norm_num) (by norm_num)
      (rectanglePath_extend_eqOn_seg3 a b c d) f,
    affineSegment_integral_eq_of_eqOn (by norm_num) (by norm_num) (by norm_num)
      (rectanglePath_extend_eqOn_seg4 a b c d) f,
    ← add_assoc, ← add_assoc]

end LeanModularForms

end

end
