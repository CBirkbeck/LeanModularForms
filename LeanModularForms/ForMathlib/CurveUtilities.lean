/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.PiecewiseC1Path
import Mathlib.Analysis.Complex.Basic

/-!
# Curve Utilities and Avoidance

Utility lemmas for working with `PiecewiseC1Path` partition structure and curve avoidance.

## Main definitions

* `PiecewiseC1Path.Avoids` -- a piecewise C^1 path avoids a point z_0
* `PiecewiseC1Path.infDist` -- infimum distance from z_0 to the path image on [0,1]
* `PiecewiseC1Path.fullPartition` -- sorted partition including endpoints 0 and 1

## Main results

* `PiecewiseC1Path.image_compact` -- the image of [0,1] under gamma is compact
* `PiecewiseC1Path.infDist_pos_of_avoids` -- positive inf distance when path avoids z_0
* `PiecewiseC1Path.avoids_of_im_lt` -- imaginary part criterion for avoidance
* `PiecewiseC1Path.avoids_of_re_ne` -- real part criterion for avoidance
* `PiecewiseC1Path.avoids_of_norm_ne` -- norm criterion for avoidance
* `PiecewiseC1Path.fullPartition_sorted` -- the full partition is sorted
* `PiecewiseC1Path.fullPartition_head_eq_zero` -- first element is 0
* `PiecewiseC1Path.fullPartition_last_eq_one` -- last element is 1
-/

open Set Complex Metric

noncomputable section

variable {x y : ℂ}

namespace PiecewiseC1Path

/-! ### Avoidance -/

/-- Infimum distance from `z_0` to the path image on `[0, 1]`. -/
noncomputable def infDist (γ : PiecewiseC1Path x y) (z₀ : ℂ) : ℝ :=
  Metric.infDist z₀ (γ.toPath.extend '' Icc 0 1)

/-! ### Compactness of the image -/

/-- The underlying finset for the full partition: `{0, 1} ∪ partition`. -/
private def fullPartitionFinset (γ : PiecewiseC1Path x y) : Finset ℝ :=
  ({0, 1} : Finset ℝ) ∪ γ.partition

/-- The full sorted partition including endpoints 0 and 1. The partition of a
`PiecewiseC1Path` contains breakpoints in `(0, 1)`; the full partition adds the
endpoints `{0, 1}`. -/
noncomputable def fullPartition (γ : PiecewiseC1Path x y) : List ℝ :=
  γ.fullPartitionFinset.sort (· ≤ ·)

end PiecewiseC1Path

end
