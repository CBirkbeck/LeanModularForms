/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDBoundary
import LeanModularForms.ForMathlib.PiecewiseC1PathOn

/-!
# FD Boundary as a `PiecewiseC1PathOn` via `concat₅`

This file assembles the fundamental-domain boundary as a free-interval
`PiecewiseC1PathOn 0 1 zero_lt_one (fdStart H) (fdStart H)` by gluing five
smooth segments using `PiecewiseC1PathOn.concat₅`.

The five segments live on `[0, 1/5]`, `[1/5, 2/5]`, …, `[4/5, 1]` and match
the corresponding pieces of `fdBoundaryFun` exactly.

## Main definitions

* `fdSeg₁PathOn`, `fdSeg₂PathOn`, `fdSeg₃PathOn`, `fdSeg₄PathOn`, `fdSeg₅PathOn`
  — the five segment paths.
* `fdBoundaryPathOn` — the assembled five-fold concatenation.

## Main results

* `fdBoundaryPathOn_apply` — pointwise equality with `fdBoundaryFun H` on all of `ℝ`.

## Design notes

This file is purely additive infrastructure built on top of the new `concat`/`concat₅`
operations in `PiecewiseC1PathOn.lean`. The existing 14 simp-locked callers of
`fdBoundaryFun` are deliberately not migrated; the new bundled object is available
for future call sites.
-/

open Complex Set Filter Topology
open scoped Real Interval

noncomputable section

namespace FDBoundary

/-- Smooth (`C^∞`) parametrization of segment 1: the right vertical edge
`1/2 + Hi ↦ 1/2 + (√3/2) i`. The formula matches `fdBoundaryFun H` on `[0, 1/5]`. -/
def seg₁Fun (H : ℝ) : ℝ → ℂ := fun t =>
  1/2 + (↑H - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I

/-- Smooth parametrization of segment 2: the arc from `ρ + 1` to `i`. -/
def seg₂Fun : ℝ → ℂ := fun t =>
  exp ((↑Real.pi / 3 + (5 * ↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I)

/-- Smooth parametrization of segment 3: the arc from `i` to `ρ`. -/
def seg₃Fun : ℝ → ℂ := fun t =>
  exp ((↑Real.pi / 2 + (5 * ↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)

/-- Smooth parametrization of segment 4: the left vertical edge
`ρ ↦ -1/2 + Hi`. -/
def seg₄Fun (H : ℝ) : ℝ → ℂ := fun t =>
  -1/2 + (↑(Real.sqrt 3) / 2 + (5 * ↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I

/-- Smooth parametrization of segment 5: the top horizontal edge
`-1/2 + Hi ↦ 1/2 + Hi`. -/
def seg₅Fun (H : ℝ) : ℝ → ℂ := fun t =>
  (5 * ↑t - 9/2) + ↑H * I

/-! ### Smoothness of the segment parametrizations -/

private lemma seg₁Fun_contDiff (H : ℝ) : ContDiff ℝ ⊤ (seg₁Fun H) :=
  contDiff_const.add
    ((contDiff_const.sub
      ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const)).mul
      contDiff_const)

private lemma seg₂Fun_contDiff : ContDiff ℝ ⊤ seg₂Fun :=
  Complex.contDiff_exp.comp
    ((contDiff_const.add
      (((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).mul
        contDiff_const)).mul contDiff_const)

private lemma seg₃Fun_contDiff : ContDiff ℝ ⊤ seg₃Fun :=
  Complex.contDiff_exp.comp
    ((contDiff_const.add
      (((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).mul
        contDiff_const)).mul contDiff_const)

private lemma seg₄Fun_contDiff (H : ℝ) : ContDiff ℝ ⊤ (seg₄Fun H) :=
  contDiff_const.add
    ((contDiff_const.add
      (((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).mul
        contDiff_const)).mul contDiff_const)

private lemma seg₅Fun_contDiff (H : ℝ) : ContDiff ℝ ⊤ (seg₅Fun H) :=
  ((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).add contDiff_const

end FDBoundary

/-! ### Helper: build a `PiecewiseC1PathOn` from a globally `C^∞` function. -/

namespace PiecewiseC1PathOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Package a globally `C^∞` function on `ℝ` into a `PiecewiseC1PathOn` with empty
partition: differentiability and continuous derivative hold everywhere, so the
piecewise framework reduces to the smooth case. -/
noncomputable def ofContDiff {a b : ℝ} {x y : E} (hab : a < b)
    (f : ℝ → E) (hf : ContDiff ℝ ⊤ f) (hxa : f a = x) (hyb : f b = y) :
    PiecewiseC1PathOn a b hab x y where
  toFun := f
  source := hxa
  target := hyb
  continuous_toFun := (hf.continuous).continuousOn
  partition := ∅
  partition_subset := by
    intro t ht
    simp at ht
  differentiable_off := by
    intro t _ _
    exact (hf.differentiable (by exact_mod_cast (WithTop.top_ne_zero))).differentiableAt
  deriv_continuous_off := by
    intro t _ _
    exact (hf.continuous_deriv le_top).continuousAt

end PiecewiseC1PathOn

/-! ### Segment paths -/

namespace FDBoundary

/-- Segment 1 of the FD boundary as a `PiecewiseC1PathOn` on `[0, 1/5]`. -/
noncomputable def fdSeg₁PathOn (H : ℝ) :
    PiecewiseC1PathOn 0 (1/5) (by norm_num)
      (fdStart H) ((1 : ℂ)/2 + (↑(Real.sqrt 3) / 2) * I) :=
  PiecewiseC1PathOn.ofContDiff (by norm_num) (seg₁Fun H) (seg₁Fun_contDiff H)
    (by simp only [seg₁Fun, fdStart]; push_cast; ring)
    (by simp only [seg₁Fun]; push_cast; ring)

/-- Segment 2 of the FD boundary as a `PiecewiseC1PathOn` on `[1/5, 2/5]`. -/
noncomputable def fdSeg₂PathOn :
    PiecewiseC1PathOn (1/5) (2/5) (by norm_num)
      ((1 : ℂ)/2 + (↑(Real.sqrt 3) / 2) * I) I :=
  PiecewiseC1PathOn.ofContDiff (by norm_num) seg₂Fun seg₂Fun_contDiff
    (by
      show seg₂Fun (1/5) = _
      simp only [seg₂Fun]
      rw [show ((↑Real.pi / 3 + (5 * ↑(1/5 : ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I : ℂ)
          = ↑(Real.pi / 3) * I by push_cast; ring,
        exp_mul_I, ← ofReal_cos, ← ofReal_sin,
        Real.cos_pi_div_three, Real.sin_pi_div_three]
      push_cast; ring)
    (by
      show seg₂Fun (2/5) = _
      simp only [seg₂Fun]
      rw [show ((↑Real.pi / 3 + (5 * ↑(2/5 : ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I : ℂ)
          = ↑(Real.pi / 2) * I by push_cast; ring,
        exp_mul_I, ← ofReal_cos, ← ofReal_sin,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      push_cast; ring)

/-- Segment 3 of the FD boundary as a `PiecewiseC1PathOn` on `[2/5, 3/5]`. -/
noncomputable def fdSeg₃PathOn :
    PiecewiseC1PathOn (2/5) (3/5) (by norm_num)
      I ((-1 : ℂ)/2 + (↑(Real.sqrt 3) / 2) * I) :=
  PiecewiseC1PathOn.ofContDiff (by norm_num) seg₃Fun seg₃Fun_contDiff
    (by
      show seg₃Fun (2/5) = _
      simp only [seg₃Fun]
      rw [show ((↑Real.pi / 2 + (5 * ↑(2/5 : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I : ℂ)
          = ↑(Real.pi / 2) * I by push_cast; ring,
        exp_mul_I, ← ofReal_cos, ← ofReal_sin,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      push_cast; ring)
    (by
      show seg₃Fun (3/5) = _
      simp only [seg₃Fun]
      rw [show ((↑Real.pi / 2 + (5 * ↑(3/5 : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I : ℂ)
          = ↑(2 * Real.pi / 3) * I by push_cast; ring,
        exp_mul_I, ← ofReal_cos, ← ofReal_sin,
        show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
      push_cast; ring)

/-- Segment 4 of the FD boundary as a `PiecewiseC1PathOn` on `[3/5, 4/5]`. -/
noncomputable def fdSeg₄PathOn (H : ℝ) :
    PiecewiseC1PathOn (3/5) (4/5) (by norm_num)
      ((-1 : ℂ)/2 + (↑(Real.sqrt 3) / 2) * I) ((-1 : ℂ)/2 + ↑H * I) :=
  PiecewiseC1PathOn.ofContDiff (by norm_num) (seg₄Fun H) (seg₄Fun_contDiff H)
    (by simp only [seg₄Fun]; push_cast; ring)
    (by simp only [seg₄Fun]; push_cast; ring)

/-- Segment 5 of the FD boundary as a `PiecewiseC1PathOn` on `[4/5, 1]`. -/
noncomputable def fdSeg₅PathOn (H : ℝ) :
    PiecewiseC1PathOn (4/5) 1 (by norm_num)
      ((-1 : ℂ)/2 + ↑H * I) (fdStart H) :=
  PiecewiseC1PathOn.ofContDiff (by norm_num) (seg₅Fun H) (seg₅Fun_contDiff H)
    (by simp only [seg₅Fun]; push_cast; ring)
    (by simp only [seg₅Fun, fdStart]; push_cast; ring)

/-! ### Assembly via `concat₅` -/

/-- The full FD boundary on `[0, 1]` as a `PiecewiseC1PathOn`, assembled from the
five segment paths via `PiecewiseC1PathOn.concat₅`. -/
noncomputable def fdBoundaryPathOn (H : ℝ) :
    PiecewiseC1PathOn 0 1 zero_lt_one (fdStart H) (fdStart H) :=
  PiecewiseC1PathOn.concat₅
    (by norm_num : (0 : ℝ) < 1/5) (by norm_num : (1/5 : ℝ) < 2/5)
    (by norm_num : (2/5 : ℝ) < 3/5) (by norm_num : (3/5 : ℝ) < 4/5)
    (by norm_num : (4/5 : ℝ) < 1)
    (fdSeg₁PathOn H) fdSeg₂PathOn fdSeg₃PathOn (fdSeg₄PathOn H) (fdSeg₅PathOn H)

/-! ### Bridge to `fdBoundaryFun` -/

/-- Under the empty-partition packaging `ofContDiff`, the underlying function is
exactly the supplied `f`. -/
private lemma ofContDiff_toFun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {x y : E} (hab : a < b) (f : ℝ → E) (hf : ContDiff ℝ ⊤ f)
    (hxa : f a = x) (hyb : f b = y) (t : ℝ) :
    (PiecewiseC1PathOn.ofContDiff hab f hf hxa hyb).toFun t = f t := rfl

/-- The `PiecewiseC1PathOn`-form of the FD boundary agrees pointwise with the
nested-if function `fdBoundaryFun H` on all of `ℝ`. -/
theorem fdBoundaryPathOn_apply (H : ℝ) (t : ℝ) :
    (fdBoundaryPathOn H).toFun t = fdBoundaryFun H t := by
  -- Unfold the four nested `concat` operations and split into five cases.
  set step1 := (fdSeg₁PathOn H).concat (by norm_num : (0 : ℝ) < 1/5)
    (by norm_num : (1/5 : ℝ) < 2/5) fdSeg₂PathOn with hstep1
  set step2 := step1.concat (by norm_num : (0 : ℝ) < 2/5)
    (by norm_num : (2/5 : ℝ) < 3/5) fdSeg₃PathOn with hstep2
  set step3 := step2.concat (by norm_num : (0 : ℝ) < 3/5)
    (by norm_num : (3/5 : ℝ) < 4/5) (fdSeg₄PathOn H) with hstep3
  have hpath_eq : fdBoundaryPathOn H = step3.concat
      (by norm_num : (0 : ℝ) < 4/5) (by norm_num : (4/5 : ℝ) < 1)
      (fdSeg₅PathOn H) := rfl
  rw [hpath_eq]
  -- Convenience: a generic "case t ∈ segment i" closes via the matching segment.
  by_cases h4 : t ≤ 4/5
  · -- Inside `[0, 4/5]`: drop the outer concat onto `step3`.
    rw [PiecewiseC1PathOn.concat_apply_of_le _ _ _ _ h4, hstep3]
    by_cases h3 : t ≤ 3/5
    · -- Inside `[0, 3/5]`: drop the next concat onto `step2`.
      rw [PiecewiseC1PathOn.concat_apply_of_le _ _ _ _ h3, hstep2]
      by_cases h2 : t ≤ 2/5
      · -- Inside `[0, 2/5]`: drop onto `step1`.
        rw [PiecewiseC1PathOn.concat_apply_of_le _ _ _ _ h2, hstep1]
        by_cases h1 : t ≤ 1/5
        · -- Segment 1.
          rw [PiecewiseC1PathOn.concat_apply_of_le _ _ _ _ h1]
          simp only [fdBoundaryFun, h1, ite_true, fdSeg₁PathOn, ofContDiff_toFun, seg₁Fun]
        · -- Segment 2.
          push Not at h1
          rw [PiecewiseC1PathOn.concat_apply_of_lt _ _ _ _ h1]
          simp only [fdBoundaryFun, not_le.mpr h1, h2, ite_true, ite_false,
            fdSeg₂PathOn, ofContDiff_toFun, seg₂Fun]
      · -- Segment 3.
        push Not at h2
        have h1' : ¬ t ≤ 1/5 := by linarith
        rw [PiecewiseC1PathOn.concat_apply_of_lt _ _ _ _ h2]
        simp only [fdBoundaryFun, h1', not_le.mpr h2, h3, ite_true, ite_false,
          fdSeg₃PathOn, ofContDiff_toFun, seg₃Fun]
    · -- Segment 4.
      push Not at h3
      have h1' : ¬ t ≤ 1/5 := by linarith
      have h2' : ¬ t ≤ 2/5 := by linarith
      rw [PiecewiseC1PathOn.concat_apply_of_lt _ _ _ _ h3]
      simp only [fdBoundaryFun, h1', h2', not_le.mpr h3, h4, ite_true, ite_false,
        fdSeg₄PathOn, ofContDiff_toFun, seg₄Fun]
  · -- Segment 5.
    push Not at h4
    have h1' : ¬ t ≤ 1/5 := by linarith
    have h2' : ¬ t ≤ 2/5 := by linarith
    have h3' : ¬ t ≤ 3/5 := by linarith
    rw [PiecewiseC1PathOn.concat_apply_of_lt _ _ _ _ h4]
    simp only [fdBoundaryFun, h1', h2', h3', not_le.mpr h4, ite_false,
      fdSeg₅PathOn, ofContDiff_toFun, seg₅Fun]

end FDBoundary

end
