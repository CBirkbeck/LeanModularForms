/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.PiecewiseC1Path
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Fundamental Domain Boundary Contour

The 5-segment closed contour around the standard fundamental domain for SL₂(ℤ)
at height `H`, parameterized on `[0, 1]`.

## Main definitions

* `fdBoundaryFun H` — the piecewise-defined contour function `ℝ → ℂ`
* `fdBoundaryPath H` — the contour as a `Path`
* `fdBoundary H hH` — the contour as a `PiecewiseC1Path` (closed path)

## Segments

The contour traverses the boundary clockwise:
1. `[0, 1/5]`: Right vertical from `1/2 + Hi` down to `ρ + 1 = 1/2 + (√3/2)i`
2. `[1/5, 2/5]`: Unit circle arc from `ρ + 1` (angle `π/3`) to `i` (angle `π/2`)
3. `[2/5, 3/5]`: Unit circle arc from `i` (angle `π/2`) to `ρ` (angle `2π/3`)
4. `[3/5, 4/5]`: Left vertical from `ρ = -1/2 + (√3/2)i` up to `-1/2 + Hi`
5. `[4/5, 1]`: Horizontal from `-1/2 + Hi` to `1/2 + Hi`
-/

open Complex Set Filter Topology
open scoped Real

noncomputable section

/-! ### The boundary function -/

/-- The 5-segment boundary of the standard fundamental domain at height `H`,
parameterized on `[0, 1]`. -/
def fdBoundaryFun (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 1 / 5 then
    1 / 2 + (↑H - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I
  else if t ≤ 2 / 5 then
    Complex.exp ((↑Real.pi / 3 + 5 * (↑t - 1 / 5) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I)
  else if t ≤ 3 / 5 then
    Complex.exp ((↑Real.pi / 2 + 5 * (↑t - 2 / 5) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)
  else if t ≤ 4 / 5 then
    -1 / 2 + (↑(Real.sqrt 3) / 2 + 5 * (↑t - 3 / 5) * (↑H - ↑(Real.sqrt 3) / 2)) * I
  else
    -1 / 2 + 5 * (↑t - 4 / 5) + ↑H * I

/-! ### Segment functions and their smoothness -/

private def seg1Fun (H : ℝ) : ℝ → ℂ := fun t =>
  1 / 2 + (↑H - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I

private def seg2Fun : ℝ → ℂ := fun t =>
  Complex.exp ((↑Real.pi / 3 + 5 * (↑t - 1 / 5) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I)

private def seg3Fun : ℝ → ℂ := fun t =>
  Complex.exp ((↑Real.pi / 2 + 5 * (↑t - 2 / 5) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)

private def seg4Fun (H : ℝ) : ℝ → ℂ := fun t =>
  -1 / 2 + (↑(Real.sqrt 3) / 2 + 5 * (↑t - 3 / 5) * (↑H - ↑(Real.sqrt 3) / 2)) * I

private def seg5Fun (H : ℝ) : ℝ → ℂ := fun t =>
  -1 / 2 + 5 * (↑t - 4 / 5) + ↑H * I

private lemma seg1_contDiff (H : ℝ) : ContDiff ℝ 1 (seg1Fun H) :=
  ContDiff.add contDiff_const (ContDiff.mul (ContDiff.sub contDiff_const
    (ContDiff.mul (ContDiff.mul contDiff_const Complex.ofRealCLM.contDiff) contDiff_const))
    contDiff_const)

private lemma seg2_contDiff : ContDiff ℝ 1 seg2Fun := by
  show ContDiff ℝ 1 (Complex.exp ∘ fun t : ℝ =>
    (↑Real.pi / 3 + 5 * (↑t - 1 / 5) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I)
  exact Complex.contDiff_exp.comp (ContDiff.mul (ContDiff.add contDiff_const
    (ContDiff.mul (ContDiff.mul contDiff_const
      (Complex.ofRealCLM.contDiff.sub contDiff_const)) contDiff_const)) contDiff_const)

private lemma seg3_contDiff : ContDiff ℝ 1 seg3Fun := by
  show ContDiff ℝ 1 (Complex.exp ∘ fun t : ℝ =>
    (↑Real.pi / 2 + 5 * (↑t - 2 / 5) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)
  exact Complex.contDiff_exp.comp (ContDiff.mul (ContDiff.add contDiff_const
    (ContDiff.mul (ContDiff.mul contDiff_const
      (Complex.ofRealCLM.contDiff.sub contDiff_const)) contDiff_const)) contDiff_const)

private lemma seg4_contDiff (H : ℝ) : ContDiff ℝ 1 (seg4Fun H) :=
  ContDiff.add contDiff_const (ContDiff.mul (ContDiff.add contDiff_const
    (ContDiff.mul (ContDiff.mul contDiff_const
      (Complex.ofRealCLM.contDiff.sub contDiff_const)) contDiff_const))
    contDiff_const)

private lemma seg5_contDiff (H : ℝ) : ContDiff ℝ 1 (seg5Fun H) :=
  ContDiff.add (ContDiff.add contDiff_const (ContDiff.mul contDiff_const
    (Complex.ofRealCLM.contDiff.sub contDiff_const))) contDiff_const

private lemma contDiff_continuous_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    Continuous (deriv f) := by
  have : ContDiff ℝ (0 + 1) f := by rwa [show (0 : WithTop ℕ∞) + 1 = 1 from by norm_num]
  exact contDiff_zero.mp this.deriv'

/-! ### Values at key points -/

theorem fdBoundaryFun_at_zero (H : ℝ) :
    fdBoundaryFun H 0 = 1 / 2 + ↑H * I := by
  simp only [fdBoundaryFun, show (0 : ℝ) ≤ 1 / 5 from by norm_num, ite_true]
  push_cast; ring

theorem fdBoundaryFun_at_one_fifth (H : ℝ) :
    fdBoundaryFun H (1 / 5) = 1 / 2 + ↑(Real.sqrt 3) / 2 * I := by
  simp only [fdBoundaryFun, show (1 / 5 : ℝ) ≤ 1 / 5 from le_refl _, ite_true]
  push_cast; ring

theorem fdBoundaryFun_at_two_fifths (H : ℝ) :
    fdBoundaryFun H (2 / 5) = I := by
  simp only [fdBoundaryFun, show ¬(2 / 5 : ℝ) ≤ 1 / 5 from by norm_num,
    show (2 / 5 : ℝ) ≤ 2 / 5 from le_refl _, ite_true, ite_false]
  have h : (↑Real.pi / 3 + 5 * (↑(2 / 5 : ℝ) - 1 / 5) *
      (↑Real.pi / 2 - ↑Real.pi / 3)) * (I : ℂ) = ↑(Real.pi / 2) * I := by
    push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem fdBoundaryFun_at_three_fifths (H : ℝ) :
    fdBoundaryFun H (3 / 5) = -1 / 2 + ↑(Real.sqrt 3) / 2 * I := by
  simp only [fdBoundaryFun, show ¬(3 / 5 : ℝ) ≤ 1 / 5 from by norm_num,
    show ¬(3 / 5 : ℝ) ≤ 2 / 5 from by norm_num,
    show (3 / 5 : ℝ) ≤ 3 / 5 from le_refl _, ite_true, ite_false]
  have h : (↑Real.pi / 2 + 5 * (↑(3 / 5 : ℝ) - 2 / 5) *
      (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * (I : ℂ) = ↑(2 * Real.pi / 3) * I := by
    push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  push_cast; ring

theorem fdBoundaryFun_at_four_fifths (H : ℝ) :
    fdBoundaryFun H (4 / 5) = -1 / 2 + ↑H * I := by
  simp only [fdBoundaryFun, show ¬(4 / 5 : ℝ) ≤ 1 / 5 from by norm_num,
    show ¬(4 / 5 : ℝ) ≤ 2 / 5 from by norm_num,
    show ¬(4 / 5 : ℝ) ≤ 3 / 5 from by norm_num,
    show (4 / 5 : ℝ) ≤ 4 / 5 from le_refl _, ite_true, ite_false]
  push_cast; ring

theorem fdBoundaryFun_at_one (H : ℝ) :
    fdBoundaryFun H 1 = 1 / 2 + ↑H * I := by
  simp only [fdBoundaryFun, show ¬(1 : ℝ) ≤ 1 / 5 from by norm_num,
    show ¬(1 : ℝ) ≤ 2 / 5 from by norm_num,
    show ¬(1 : ℝ) ≤ 3 / 5 from by norm_num,
    show ¬(1 : ℝ) ≤ 4 / 5 from by norm_num, ite_false]
  push_cast; ring

/-- The boundary contour is closed: it starts and ends at `1/2 + Hi`. -/
theorem fdBoundaryFun_closed (H : ℝ) :
    fdBoundaryFun H 0 = fdBoundaryFun H 1 := by
  rw [fdBoundaryFun_at_zero, fdBoundaryFun_at_one]

/-! ### Continuity -/

private def inner45 (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 4 / 5 then seg4Fun H t else seg5Fun H t

private lemma inner45_cont (H : ℝ) : Continuous (inner45 H) :=
  Continuous.if_le (seg4_contDiff H).continuous (seg5_contDiff H).continuous
    continuous_id continuous_const (fun t (ht : t = 4 / 5) => by
      subst ht; simp only [seg4Fun, seg5Fun]; push_cast; ring)

private def inner345 (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 3 / 5 then seg3Fun t else inner45 H t

private lemma inner345_cont (H : ℝ) : Continuous (inner345 H) := by
  apply Continuous.if_le seg3_contDiff.continuous (inner45_cont H)
    continuous_id continuous_const
  intro t ht; simp only [id] at ht; have : t = 3 / 5 := by linarith
  subst this; simp only [inner45, seg3Fun, seg4Fun,
    show (3 / 5 : ℝ) ≤ 4 / 5 from by norm_num, ite_true]
  have h : (↑Real.pi / 2 + 5 * (↑(3 / 5 : ℝ) - 2 / 5) *
      (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      ↑(2 * Real.pi / 3) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  push_cast; ring

private def inner2345 (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 2 / 5 then seg2Fun t else inner345 H t

private lemma inner2345_cont (H : ℝ) : Continuous (inner2345 H) := by
  apply Continuous.if_le seg2_contDiff.continuous (inner345_cont H)
    continuous_id continuous_const
  intro t ht; simp only [id] at ht; have : t = 2 / 5 := by linarith
  subst this; simp only [inner345, seg2Fun, seg3Fun,
    show (2 / 5 : ℝ) ≤ 3 / 5 from by norm_num, ite_true]
  have h1 : (↑Real.pi / 3 + 5 * (↑(2 / 5 : ℝ) - 1 / 5) *
      (↑Real.pi / 2 - ↑Real.pi / 3)) * I = ↑(Real.pi / 2) * I := by push_cast; ring
  have h2 : (↑Real.pi / 2 + 5 * (↑(2 / 5 : ℝ) - 2 / 5) *
      (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I = ↑(Real.pi / 2) * I := by push_cast; ring
  rw [h1, h2]

private lemma fdBoundaryFun_eq_layered (H : ℝ) (t : ℝ) :
    fdBoundaryFun H t =
      (if t ≤ 1 / 5 then seg1Fun H t else inner2345 H t) := by
  simp only [fdBoundaryFun, seg1Fun, inner2345, inner345, inner45, seg2Fun, seg3Fun, seg4Fun,
    seg5Fun]

/-- The boundary function is continuous. -/
theorem fdBoundaryFun_continuous (H : ℝ) : Continuous (fdBoundaryFun H) := by
  have heq : fdBoundaryFun H = (fun t => if t ≤ 1 / 5 then seg1Fun H t
      else inner2345 H t) := by ext t; exact fdBoundaryFun_eq_layered H t
  rw [heq]
  apply Continuous.if_le (seg1_contDiff H).continuous (inner2345_cont H)
    continuous_id continuous_const
  intro t ht; simp only [id] at ht; have : t = 1 / 5 := by linarith
  subst this; simp only [inner2345, seg1Fun, seg2Fun,
    show (1 / 5 : ℝ) ≤ 2 / 5 from by norm_num, ite_true]
  have h : (↑Real.pi / 3 + 5 * (↑(1 / 5 : ℝ) - 1 / 5) *
      (↑Real.pi / 2 - ↑Real.pi / 3)) * I = ↑(Real.pi / 3) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring

/-! ### Path construction -/

/-- The boundary contour as a `Path` from `1/2 + Hi` to `1/2 + Hi`. -/
def fdBoundaryPath (H : ℝ) : Path (1 / 2 + (H : ℂ) * I) (1 / 2 + (H : ℂ) * I) where
  toFun := Set.restrict (Icc 0 1) (fdBoundaryFun H)
  continuous_toFun := (fdBoundaryFun_continuous H).continuousOn.restrict
  source' := by
    show fdBoundaryFun H ((⟨0, left_mem_Icc.mpr zero_le_one⟩ : Icc (0 : ℝ) 1) : ℝ) = _
    simp [fdBoundaryFun_at_zero]
  target' := by
    show fdBoundaryFun H ((⟨1, right_mem_Icc.mpr zero_le_one⟩ : Icc (0 : ℝ) 1) : ℝ) = _
    simp [fdBoundaryFun_at_one]

/-! ### Path.extend agrees with fdBoundaryFun on (0, 1) -/

private lemma extend_eventuallyEq (H : ℝ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (fdBoundaryPath H).extend =ᶠ[𝓝 t] fdBoundaryFun H := by
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Ioo 0 1, Ioo_mem_nhds ht.1 ht.2, fun s hs => ?_⟩
  simp only [Path.extend, Set.IccExtend, fdBoundaryPath, ContinuousMap.coe_mk, Function.comp_def]
  show fdBoundaryFun H (Set.projIcc 0 1 zero_le_one s : ℝ) = fdBoundaryFun H s
  congr 1
  simp [Set.projIcc_of_mem zero_le_one ⟨le_of_lt hs.1, le_of_lt hs.2⟩]

/-! ### Local agreement with segment functions -/

private lemma fdBoundaryFun_eq_seg1 (H : ℝ) (t : ℝ) (ht : t < 1 / 5) :
    fdBoundaryFun H =ᶠ[𝓝 t] seg1Fun H := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  simp only [fdBoundaryFun, show s ≤ 1 / 5 from le_of_lt hs, ite_true, seg1Fun]

private lemma fdBoundaryFun_eq_seg2 (H : ℝ) (t : ℝ) (h1 : 1 / 5 < t) (h2 : t < 2 / 5) :
    fdBoundaryFun H =ᶠ[𝓝 t] seg2Fun := by
  filter_upwards [Ioi_mem_nhds h1, Iio_mem_nhds h2] with s hs1 hs2
  simp only [fdBoundaryFun, show ¬s ≤ 1 / 5 from not_le.mpr hs1,
    show s ≤ 2 / 5 from le_of_lt hs2, ite_true, ite_false, seg2Fun]

private lemma fdBoundaryFun_eq_seg3 (H : ℝ) (t : ℝ) (h1 : 2 / 5 < t) (h2 : t < 3 / 5) :
    fdBoundaryFun H =ᶠ[𝓝 t] seg3Fun := by
  filter_upwards [Ioi_mem_nhds h1, Iio_mem_nhds h2] with s hs1 hs2
  simp only [fdBoundaryFun, show ¬s ≤ 1 / 5 from not_le.mpr (lt_trans (by norm_num) hs1),
    show ¬s ≤ 2 / 5 from not_le.mpr hs1,
    show s ≤ 3 / 5 from le_of_lt hs2, ite_true, ite_false, seg3Fun]

private lemma fdBoundaryFun_eq_seg4 (H : ℝ) (t : ℝ) (h1 : 3 / 5 < t) (h2 : t < 4 / 5) :
    fdBoundaryFun H =ᶠ[𝓝 t] seg4Fun H := by
  filter_upwards [Ioi_mem_nhds h1, Iio_mem_nhds h2] with s hs1 hs2
  simp only [fdBoundaryFun,
    show ¬s ≤ 1 / 5 from not_le.mpr (lt_trans (by norm_num) hs1),
    show ¬s ≤ 2 / 5 from not_le.mpr (lt_trans (by norm_num) hs1),
    show ¬s ≤ 3 / 5 from not_le.mpr hs1,
    show s ≤ 4 / 5 from le_of_lt hs2, ite_true, ite_false, seg4Fun]

private lemma fdBoundaryFun_eq_seg5 (H : ℝ) (t : ℝ) (h1 : 4 / 5 < t) (h2 : t < 1) :
    fdBoundaryFun H =ᶠ[𝓝 t] seg5Fun H := by
  filter_upwards [Ioi_mem_nhds h1, Iio_mem_nhds h2] with s hs1 hs2
  simp only [fdBoundaryFun,
    show ¬s ≤ 1 / 5 from not_le.mpr (lt_trans (by norm_num) hs1),
    show ¬s ≤ 2 / 5 from not_le.mpr (lt_trans (by norm_num) hs1),
    show ¬s ≤ 3 / 5 from not_le.mpr (lt_trans (by norm_num) hs1),
    show ¬s ≤ 4 / 5 from not_le.mpr hs1, ite_false, seg5Fun]

/-! ### PiecewiseC1Path construction -/

/-- For each `t ∈ (0, 1)` off the partition, `Path.extend` eventually equals a `C^1` function.
This gives both differentiability and derivative continuity. -/
private lemma extend_eventuallyEq_smooth (H : ℝ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (h15 : t ≠ 1 / 5) (h25 : t ≠ 2 / 5) (h35 : t ≠ 3 / 5) (h45 : t ≠ 4 / 5) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 1 g ∧ (fdBoundaryPath H).extend =ᶠ[𝓝 t] g := by
  have hext := extend_eventuallyEq H t ht
  by_cases h1 : t < 1 / 5
  · exact ⟨seg1Fun H, seg1_contDiff H, hext.trans (fdBoundaryFun_eq_seg1 H t h1)⟩
  · replace h1 : 1 / 5 < t := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h15)
    by_cases h2 : t < 2 / 5
    · exact ⟨seg2Fun, seg2_contDiff, hext.trans (fdBoundaryFun_eq_seg2 H t h1 h2)⟩
    · replace h2 : 2 / 5 < t := lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h25)
      by_cases h3 : t < 3 / 5
      · exact ⟨seg3Fun, seg3_contDiff, hext.trans (fdBoundaryFun_eq_seg3 H t h2 h3)⟩
      · replace h3 : 3 / 5 < t := lt_of_le_of_ne (not_lt.mp h3) (Ne.symm h35)
        by_cases h4 : t < 4 / 5
        · exact ⟨seg4Fun H, seg4_contDiff H,
            hext.trans (fdBoundaryFun_eq_seg4 H t h3 h4)⟩
        · replace h4 : 4 / 5 < t := lt_of_le_of_ne (not_lt.mp h4) (Ne.symm h45)
          exact ⟨seg5Fun H, seg5_contDiff H,
            hext.trans (fdBoundaryFun_eq_seg5 H t h4 ht.2)⟩

/-- The boundary contour as a `PiecewiseC1Path`. The hypothesis `hH` ensures the vertical
segments have nonzero length; it is not used in the construction but documents the geometric
constraint. -/
def fdBoundary (H : ℝ) (_ : H > Real.sqrt 3 / 2) :
    PiecewiseC1Path (1 / 2 + (H : ℂ) * I) (1 / 2 + (H : ℂ) * I) where
  toPath := fdBoundaryPath H
  partition := {1 / 5, 2 / 5, 3 / 5, 4 / 5}
  partition_subset := by
    intro t ht
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at ht
    constructor <;> rcases ht with rfl | rfl | rfl | rfl <;> norm_num
  differentiable_off := by
    intro t ht htp
    simp only [Finset.mem_insert, Finset.mem_singleton] at htp; push_neg at htp
    obtain ⟨g, hg, heq⟩ := extend_eventuallyEq_smooth H t ht htp.1 htp.2.1 htp.2.2.1 htp.2.2.2
    exact heq.differentiableAt_iff.mpr (hg.differentiable one_ne_zero).differentiableAt
  deriv_continuous_off := by
    intro t ht htp
    simp only [Finset.mem_insert, Finset.mem_singleton] at htp; push_neg at htp
    obtain ⟨g, hg, heq⟩ := extend_eventuallyEq_smooth H t ht htp.1 htp.2.1 htp.2.2.1 htp.2.2.2
    exact (contDiff_continuous_deriv hg).continuousAt.congr heq.symm.deriv

/-- The boundary contour is closed. -/
theorem fdBoundary_isClosed (H : ℝ) (hH : H > Real.sqrt 3 / 2) :
    (fdBoundary H hH).IsClosed := rfl

end
