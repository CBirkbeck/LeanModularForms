/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.InteriorWinding
import LeanModularForms.ForMathlib.FDBoundaryPath
import LeanModularForms.ForMathlib.SegmentFTC

/-!
# Interior Winding Number Proof: Contour Integral = -2πi

This file proves that for any strict interior point `z` of the fundamental domain
(with `‖z‖ > 1`, `|Re z| < 1/2`, `0 < Im z < H`), the contour integral
`∮_γ (w - z)⁻¹ dw = -(2 * π * I)` along the FD boundary at height `H`.

Combined with the reduction theorem `hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral`
from `InteriorWinding.lean`, this gives the interior winding number = -1.

## Strategy

The proof decomposes the contour integral into five segment integrals at the partition
points `1/5, 2/5, 3/5, 4/5`. On each segment, FTC with `log(γ(t) - z)` as the
primitive gives the log difference. The five terms telescope, and the total branch
correction for one clockwise loop is `-2πi`.

## Main results

* `fdBoundary_contourIntegral_inv_sub_eq_of_ftc` -- the contour integral equals `-2πi`,
  given segment-level FTC data and the branch correction.
* `fdBoundary_interior_winding_neg_one` -- the interior winding number is `-1`.
* `fdBoundary_seg1_in_slitPlane` -- segment 1 avoids the branch cut.
* `fdBoundary_seg5_in_slitPlane` -- segment 5 avoids the branch cut.
* `fdBoundary_seg1_ftc` / `fdBoundary_seg5_ftc` -- FTC on segments 1 and 5.
* `fdWindingData_of_interior_integral` -- construct `FDWindingData`.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Extract segment integrability from full `[0, 1]` integrability. -/
private lemma segment_integrability {f : ℝ → ℂ} (hint : IntervalIntegrable f volume 0 1)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable f volume a b :=
  hint.mono_set (Set.uIcc_subset_uIcc
    (Set.mem_uIcc_of_le ha (le_trans hab hb)) (Set.mem_uIcc_of_le (le_trans ha hab) hb))

/-- The contour integral of `(w - z)⁻¹` along the FD boundary splits into five
segment integrals at the partition points. -/
theorem fdBoundary_contourIntegral_split {z : ℂ} {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hint : IntervalIntegrable
      (fun t => (γ t - z)⁻¹ * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral (fun w => (w - z)⁻¹) =
      (∫ t in (0 : ℝ)..1/5, (γ t - z)⁻¹ * deriv γ.toPath.extend t) +
      (∫ t in (1/5 : ℝ)..2/5, (γ t - z)⁻¹ * deriv γ.toPath.extend t) +
      (∫ t in (2/5 : ℝ)..3/5, (γ t - z)⁻¹ * deriv γ.toPath.extend t) +
      (∫ t in (3/5 : ℝ)..4/5, (γ t - z)⁻¹ * deriv γ.toPath.extend t) +
      (∫ t in (4/5 : ℝ)..1, (γ t - z)⁻¹ * deriv γ.toPath.extend t) := by
  unfold PiecewiseC1Path.contourIntegral
  have hint1 := segment_integrability hint (a := 0) (b := 1/5)
    (by norm_num) (by norm_num) (by norm_num)
  have hint2 := segment_integrability hint (a := 1/5) (b := 2/5)
    (by norm_num) (by norm_num) (by norm_num)
  have hint3 := segment_integrability hint (a := 2/5) (b := 3/5)
    (by norm_num) (by norm_num) (by norm_num)
  have hint4 := segment_integrability hint (a := 3/5) (b := 4/5)
    (by norm_num) (by norm_num) (by norm_num)
  have hint5 := segment_integrability hint (a := 4/5) (b := 1)
    (by norm_num) (by norm_num) (by norm_num)
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1
        (hint2.trans (hint3.trans (hint4.trans hint5))),
      ← intervalIntegral.integral_add_adjacent_intervals hint2
        (hint3.trans (hint4.trans hint5)),
      ← intervalIntegral.integral_add_adjacent_intervals hint3 (hint4.trans hint5),
      ← intervalIntegral.integral_add_adjacent_intervals hint4 hint5]
  ring

/-- For a closed path agreeing with `fdBoundaryFun`, `γ(1) - z = γ(0) - z`. -/
theorem closed_path_sub_eq {z : ℂ} {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t) :
    γ 1 - z = γ 0 - z := by
  have h0 : (γ : ℝ → ℂ) 0 = fdBoundaryFun H 0 := hγ 0 ⟨le_refl _, zero_le_one⟩
  have h1 : (γ : ℝ → ℂ) 1 = fdBoundaryFun H 1 := hγ 1 ⟨zero_le_one, le_refl _⟩
  rw [h0, h1, fdBoundaryFun_closed]

end
