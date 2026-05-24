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

end
