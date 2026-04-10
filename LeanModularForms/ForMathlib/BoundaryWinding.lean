/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDBoundaryPath
import LeanModularForms.ForMathlib.SingleCrossing

/-!
# Smooth Boundary Winding Number

At a smooth boundary crossing of the fundamental domain -- any point on the
FD boundary that is NOT an elliptic point (i, rho, rho+1) and not at a
partition endpoint -- the generalized winding number is `-1/2`.

These smooth crossings include:
* Points on the unit-circle arc with `Re z in (-1/2, 0) union (0, 1/2)`,
  excluding `i` (where `Re z = 0`).
* Points on the right vertical edge (`Re z = 1/2`, `Im z > sqrt(3)/2`).
* Points on the left vertical edge (`Re z = -1/2`, `Im z > sqrt(3)/2`).
* Points on the horizontal top edge (`Im z = H`).

At any such point the FD boundary passes through `z₀` as a smooth curve
(locally a line segment or arc), making an angle of `π` from entry to exit.
The Hungerbuhler--Wasem decomposition gives winding = `angle / (2π) = -1/2`.

## Main results

* `hasGeneralizedWindingNumber_neg_half_of_scd` -- if `SingleCrossingData`
  has `L = -(π * I)`, then `HasGeneralizedWindingNumber γ z₀ (-1/2)`.
* `generalizedWindingNumber_neg_half_of_scd` -- the corresponding equality.
* `fdBoundary_winding_neg_half_of_smooth_crossing` -- specialization to the
  FD boundary: given `SingleCrossingData` with `L = -(π * I)` for a
  non-partition crossing point, the winding number is `-1/2`.
* `fdBoundary_hasWindingNumber_neg_half_of_smooth_crossing` -- the
  `HasGeneralizedWindingNumber` version.

## Design

Rather than constructing `SingleCrossingData` for every possible smooth
boundary point (which would require parameterizing over all crossing
positions and proving near/far/FTC bounds for each), we take the
`SingleCrossingData` as a hypothesis. The key content of this file is:

1. The general bridge from `SingleCrossingData` with `L = -(π * I)` to
   the winding number `-1/2`, for an arbitrary point `z₀`.
2. The FD-specific version that additionally packages the boundary
   agreement and crossing conditions.

The `SingleCrossingData` framework already handles the CPV integral
computation; this file just performs the final division `L / (2πi)`.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

variable {x y : ℂ}

/-! ### Part 1: General smooth crossing winding number -/

/-- At any single crossing with limit `L = -(π * I)`, the generalized winding
number is `-1/2`. This is the universal smooth-crossing result: the angle
swept from entry to exit is `π`, giving `-(π * I) / (2 * π * I) = -1/2`.

This generalizes `hasWindingNumber_atI_of_scd` from
`WindingWeightsUnconditional.lean` to arbitrary crossing points. -/
theorem hasGeneralizedWindingNumber_neg_half_of_scd
    {γ : PiecewiseC1Path x y} {z₀ : ℂ}
    (D : SingleCrossingData γ z₀)
    (hL : D.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber γ z₀ (-1 / 2) := by
  convert D.hasWindingNumber using 1
  rw [hL]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- The `generalizedWindingNumber` value version: if `SingleCrossingData` has
limit `L = -(π * I)`, then `generalizedWindingNumber γ z₀ = -1/2`. -/
theorem generalizedWindingNumber_neg_half_of_scd
    {γ : PiecewiseC1Path x y} {z₀ : ℂ}
    (D : SingleCrossingData γ z₀)
    (hL : D.L = -(↑Real.pi * I)) :
    generalizedWindingNumber γ z₀ = -1 / 2 :=
  D.windingNumber_neg_half hL

/-- `HasGeneralizedWindingNumber` version of the `-1/2` smooth crossing result.
This bridges from `SingleCrossingData.hasCauchyPV` to the winding number predicate. -/
theorem hasGeneralizedWindingNumber_neg_half_of_hasCauchyPV
    {γ : PiecewiseC1Path x y} {z₀ : ℂ}
    (D : SingleCrossingData γ z₀)
    (hL : D.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber γ z₀ (-1 / 2) :=
  hasGeneralizedWindingNumber_neg_half_of_scd D hL

/-! ### Part 2: Smooth crossing characterization for the FD boundary -/

/-- A parameter `t₀ ∈ (0, 1)` is a smooth crossing parameter for the FD boundary
if it is not one of the partition points `{1/5, 2/5, 3/5, 4/5}`. At such parameters,
the boundary is locally a smooth curve (either a line segment or a smooth arc),
and the crossing angle is always `π`. -/
def IsSmoothCrossingParam (t₀ : ℝ) : Prop :=
  t₀ ∈ Ioo 0 1 ∧ t₀ ∉ fdBoundaryPartition

theorem isSmoothCrossingParam_iff (t₀ : ℝ) :
    IsSmoothCrossingParam t₀ ↔
      t₀ ∈ Ioo 0 1 ∧ t₀ ≠ 1/5 ∧ t₀ ≠ 2/5 ∧ t₀ ≠ 3/5 ∧ t₀ ≠ 4/5 := by
  simp only [IsSmoothCrossingParam, fdBoundaryPartition, Finset.mem_insert,
    Finset.mem_singleton, not_or]

/-- Smooth crossing parameters lie in the open unit interval. -/
theorem IsSmoothCrossingParam.mem_Ioo {t₀ : ℝ} (h : IsSmoothCrossingParam t₀) :
    t₀ ∈ Ioo 0 1 := h.1

/-- Smooth crossing parameters are not partition points. -/
theorem IsSmoothCrossingParam.not_partition {t₀ : ℝ} (h : IsSmoothCrossingParam t₀) :
    t₀ ∉ fdBoundaryPartition := h.2

/-! ### Part 3: FD boundary smooth crossing winding number -/

/-- At any smooth crossing point of the FD boundary, the generalized winding
number is `-1/2`.

The hypotheses capture the geometric setup:
* `z₀` is the crossing point, `t₀` is the crossing parameter
* `t₀` is a smooth crossing parameter (in `(0,1)`, not a partition point)
* `fdBoundaryFun H t₀ = z₀` records the crossing
* A `SingleCrossingData` instance with limit `L = -(π * I)` witnesses the
  CPV computation

The `-1/2` value follows because at a smooth crossing the boundary is locally
a straight line or smooth arc, sweeping angle `π` from entry to exit. -/
theorem fdBoundary_hasWindingNumber_neg_half_of_smooth_crossing
    {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    {z₀ : ℂ} {t₀ : ℝ}
    (_ht₀ : IsSmoothCrossingParam t₀)
    (_hcross : fdBoundaryFun H t₀ = z₀)
    (scd : SingleCrossingData (fdBoundaryPC1Path H hH) z₀)
    (hL : scd.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber (fdBoundaryPC1Path H hH) z₀ (-1 / 2) :=
  hasGeneralizedWindingNumber_neg_half_of_scd scd hL

/-- The `generalizedWindingNumber` value at a smooth crossing is `-1/2`. -/
theorem fdBoundary_winding_neg_half_of_smooth_crossing
    {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    {z₀ : ℂ} {t₀ : ℝ}
    (_ht₀ : IsSmoothCrossingParam t₀)
    (_hcross : fdBoundaryFun H t₀ = z₀)
    (scd : SingleCrossingData (fdBoundaryPC1Path H hH) z₀)
    (hL : scd.L = -(↑Real.pi * I)) :
    generalizedWindingNumber (fdBoundaryPC1Path H hH) z₀ = -1 / 2 :=
  generalizedWindingNumber_neg_half_of_scd scd hL

/-- Convenience version taking `1 < H` and using `fdHeightValid_of_one_lt`. -/
theorem fdBoundary_hasWindingNumber_neg_half_of_smooth_crossing'
    {H : ℝ} (hH : 1 < H)
    {z₀ : ℂ} {t₀ : ℝ}
    (ht₀ : IsSmoothCrossingParam t₀)
    (hcross : fdBoundaryFun H t₀ = z₀)
    (scd : SingleCrossingData (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)) z₀)
    (hL : scd.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber
      (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)) z₀ (-1 / 2) :=
  fdBoundary_hasWindingNumber_neg_half_of_smooth_crossing
    (fdHeightValid_of_one_lt H hH) ht₀ hcross scd hL

/-! ### Part 4: Segment-specific corollaries -/

/-- The winding number is `-1/2` at any smooth point on the right vertical
edge (segment 1: `t ∈ (0, 1/5)`, `Re z = 1/2`). -/
theorem fdBoundary_hasWindingNumber_neg_half_rightVert
    {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    {z₀ : ℂ} {t₀ : ℝ} (_ht₀ : t₀ ∈ Ioo 0 (1/5))
    (_hcross : fdBoundaryFun H t₀ = z₀)
    (scd : SingleCrossingData (fdBoundaryPC1Path H hH) z₀)
    (hL : scd.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber (fdBoundaryPC1Path H hH) z₀ (-1 / 2) :=
  hasGeneralizedWindingNumber_neg_half_of_scd scd hL

/-- The winding number is `-1/2` at any smooth point on arc segment 2
(`t ∈ (1/5, 2/5)`, unit circle from `ρ+1` to `i`). -/
theorem fdBoundary_hasWindingNumber_neg_half_arc2
    {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    {z₀ : ℂ} {t₀ : ℝ} (_ht₀ : t₀ ∈ Ioo (1/5) (2/5))
    (_hcross : fdBoundaryFun H t₀ = z₀)
    (scd : SingleCrossingData (fdBoundaryPC1Path H hH) z₀)
    (hL : scd.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber (fdBoundaryPC1Path H hH) z₀ (-1 / 2) :=
  hasGeneralizedWindingNumber_neg_half_of_scd scd hL

/-- The winding number is `-1/2` at any smooth point on arc segment 3
(`t ∈ (2/5, 3/5)`, unit circle from `i` to `ρ`). -/
theorem fdBoundary_hasWindingNumber_neg_half_arc3
    {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    {z₀ : ℂ} {t₀ : ℝ} (_ht₀ : t₀ ∈ Ioo (2/5) (3/5))
    (_hcross : fdBoundaryFun H t₀ = z₀)
    (scd : SingleCrossingData (fdBoundaryPC1Path H hH) z₀)
    (hL : scd.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber (fdBoundaryPC1Path H hH) z₀ (-1 / 2) :=
  hasGeneralizedWindingNumber_neg_half_of_scd scd hL

/-- The winding number is `-1/2` at any smooth point on the left vertical
edge (segment 4: `t ∈ (3/5, 4/5)`, `Re z = -1/2`). -/
theorem fdBoundary_hasWindingNumber_neg_half_leftVert
    {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    {z₀ : ℂ} {t₀ : ℝ} (_ht₀ : t₀ ∈ Ioo (3/5) (4/5))
    (_hcross : fdBoundaryFun H t₀ = z₀)
    (scd : SingleCrossingData (fdBoundaryPC1Path H hH) z₀)
    (hL : scd.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber (fdBoundaryPC1Path H hH) z₀ (-1 / 2) :=
  hasGeneralizedWindingNumber_neg_half_of_scd scd hL

/-- The winding number is `-1/2` at any smooth point on the horizontal
top edge (segment 5: `t ∈ (4/5, 1)`, `Im z = H`). -/
theorem fdBoundary_hasWindingNumber_neg_half_horizontal
    {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    {z₀ : ℂ} {t₀ : ℝ} (_ht₀ : t₀ ∈ Ioo (4/5) 1)
    (_hcross : fdBoundaryFun H t₀ = z₀)
    (scd : SingleCrossingData (fdBoundaryPC1Path H hH) z₀)
    (hL : scd.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber (fdBoundaryPC1Path H hH) z₀ (-1 / 2) :=
  hasGeneralizedWindingNumber_neg_half_of_scd scd hL

/-! ### Part 5: Smooth crossing parameter witnesses -/

/-- Any parameter in `(0, 1/5)` is a smooth crossing parameter. -/
theorem isSmoothCrossingParam_of_seg1 {t₀ : ℝ} (ht : t₀ ∈ Ioo 0 (1/5)) :
    IsSmoothCrossingParam t₀ := by
  rw [isSmoothCrossingParam_iff]
  exact ⟨Ioo_subset_Ioo_right (by norm_num : (1 : ℝ)/5 ≤ 1) ht,
    by intro h; linarith [ht.2],
    by intro h; linarith [ht.2],
    by intro h; linarith [ht.2],
    by intro h; linarith [ht.2]⟩

/-- Any parameter in `(1/5, 2/5)` is a smooth crossing parameter. -/
theorem isSmoothCrossingParam_of_seg2 {t₀ : ℝ} (ht : t₀ ∈ Ioo (1/5) (2/5)) :
    IsSmoothCrossingParam t₀ := by
  rw [isSmoothCrossingParam_iff]
  exact ⟨Ioo_subset_Ioo (by norm_num : (0 : ℝ) ≤ 1/5) (by norm_num : (2 : ℝ)/5 ≤ 1) ht,
    by intro h; linarith [ht.1],
    by intro h; linarith [ht.2],
    by intro h; linarith [ht.2],
    by intro h; linarith [ht.2]⟩

/-- Any parameter in `(2/5, 3/5)` is a smooth crossing parameter. -/
theorem isSmoothCrossingParam_of_seg3 {t₀ : ℝ} (ht : t₀ ∈ Ioo (2/5) (3/5)) :
    IsSmoothCrossingParam t₀ := by
  rw [isSmoothCrossingParam_iff]
  exact ⟨Ioo_subset_Ioo (by norm_num : (0 : ℝ) ≤ 2/5) (by norm_num : (3 : ℝ)/5 ≤ 1) ht,
    by intro h; linarith [ht.1],
    by intro h; linarith [ht.1],
    by intro h; linarith [ht.2],
    by intro h; linarith [ht.2]⟩

/-- Any parameter in `(3/5, 4/5)` is a smooth crossing parameter. -/
theorem isSmoothCrossingParam_of_seg4 {t₀ : ℝ} (ht : t₀ ∈ Ioo (3/5) (4/5)) :
    IsSmoothCrossingParam t₀ := by
  rw [isSmoothCrossingParam_iff]
  exact ⟨Ioo_subset_Ioo (by norm_num : (0 : ℝ) ≤ 3/5) (by norm_num : (4 : ℝ)/5 ≤ 1) ht,
    by intro h; linarith [ht.1],
    by intro h; linarith [ht.1],
    by intro h; linarith [ht.1],
    by intro h; linarith [ht.2]⟩

/-- Any parameter in `(4/5, 1)` is a smooth crossing parameter. -/
theorem isSmoothCrossingParam_of_seg5 {t₀ : ℝ} (ht : t₀ ∈ Ioo (4/5) 1) :
    IsSmoothCrossingParam t₀ := by
  rw [isSmoothCrossingParam_iff]
  exact ⟨Ioo_subset_Ioo_left (by norm_num : (0 : ℝ) ≤ 4/5) ht,
    by intro h; linarith [ht.1],
    by intro h; linarith [ht.1],
    by intro h; linarith [ht.1],
    by intro h; linarith [ht.1]⟩

end
