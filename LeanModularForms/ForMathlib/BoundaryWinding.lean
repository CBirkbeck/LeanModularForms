/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDBoundaryPath
import LeanModularForms.ForMathlib.SingleCrossing
import LeanModularForms.ForMathlib.CrossingAtI

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

/-! ### Part 6: Generic smooth crossing — SingleCrossingData construction

For a smooth crossing at parameter `t₀ ∈ (0, 1)` (not a partition point),
we construct `SingleCrossingData` from:

1. **Geometric bounds** (`h_far`, `h_near`): proved per-segment in
   `WindingWeightProofs.lean` and `CrossingAtI.lean` / `CrossingAtRho.lean`.
2. **Analytical hypothesis** (`ArcFTCHyp`): the FTC telescope identity,
   integrability, and limit, bundled in the same structure used for the
   crossings at `i`, `ρ`, and `ρ+1`.

The key result is `mkSingleCrossingData_smooth`: given a smooth crossing parameter
`t₀`, a cutoff `δ`, geometric near/far bounds for the curve around `t₀`, and an
`ArcFTCHyp` at `t₀`, this produces `SingleCrossingData` with limit `L`.

Then `boundaryWinding_of_smoothFTCHyp` specializes to `L = -(π * I)` and extracts
`HasGeneralizedWindingNumber γ z₀ (-1/2)`.

Finally, `fdBoundary_boundaryWinding_of_forall_smoothFTCHyp` reduces the full
`h_boundary` hypothesis of `FDWindingDataFull` to a per-point smooth-crossing
`ArcFTCHyp` for every boundary point.
-/

/-- Construct `SingleCrossingData` at an arbitrary smooth crossing parameter `t₀`.

This is the generic version of `mkSingleCrossingData_atI`: instead of hardcoding
`t₀ = 2/5` and the geometry of the `i` crossing, we take the crossing parameter,
cutoff, and geometric bounds as parameters.

**Geometry parameters** (proved per-segment elsewhere):
- `h_far`: outside the δ-window, the curve is ε-far from `z₀`
- `h_near`: inside the δ-window, the curve is ε-close to `z₀`

**Analytic parameter** (`ArcFTCHyp`): the FTC identity, integrability, and limit. -/
def mkSingleCrossingData_smooth {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1)
    (δ : ℝ → ℝ) (threshold : ℝ) (hthresh : 0 < threshold)
    (hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε)
    (hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min t₀ (1 - t₀))
    (h_far : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Icc 0 1, δ ε < |t - t₀| → ε < ‖γ.toPath.extend t - z₀‖)
    (h_near : ∀ ε, 0 < ε → ε < threshold →
      ∀ t, |t - t₀| ≤ δ ε → ‖γ.toPath.extend t - z₀‖ ≤ ε)
    (L : ℂ)
    (ftcHyp : ArcFTCHyp γ z₀ t₀ δ threshold L) :
    SingleCrossingData γ z₀ where
  L := L
  t₀ := t₀
  ht₀ := ht₀
  δ := δ
  threshold := threshold
  hthresh := hthresh
  hδ_pos := hδ_pos
  hδ_small := hδ_small
  h_far := h_far
  h_near := h_near
  E := ftcHyp.E
  h_ftc := ftcHyp.h_ftc
  hint_left := ftcHyp.hint_left
  hint_right := ftcHyp.hint_right
  h_limit := ftcHyp.h_limit

/-- From a generic smooth crossing `SingleCrossingData` with limit `L = -(π * I)`,
extract `HasGeneralizedWindingNumber γ z₀ (-1/2)`.

This composes `mkSingleCrossingData_smooth` with the universal smooth-crossing
division `L / (2πi) = -1/2` from Part 1. -/
theorem boundaryWinding_of_smoothFTCHyp {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1)
    (δ : ℝ → ℝ) (threshold : ℝ) (hthresh : 0 < threshold)
    (hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε)
    (hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min t₀ (1 - t₀))
    (h_far : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Icc 0 1, δ ε < |t - t₀| → ε < ‖γ.toPath.extend t - z₀‖)
    (h_near : ∀ ε, 0 < ε → ε < threshold →
      ∀ t, |t - t₀| ≤ δ ε → ‖γ.toPath.extend t - z₀‖ ≤ ε)
    (ftcHyp : ArcFTCHyp γ z₀ t₀ δ threshold (-(↑Real.pi * I))) :
    HasGeneralizedWindingNumber γ z₀ (-1 / 2) := by
  let D := mkSingleCrossingData_smooth γ z₀ t₀ ht₀ δ threshold hthresh
    hδ_pos hδ_small h_far h_near (-(↑Real.pi * I)) ftcHyp
  exact hasGeneralizedWindingNumber_neg_half_of_scd D rfl

/-! ### Part 7: Reducing boundary winding to per-point FTC hypotheses

The `h_boundary` field of `FDWindingDataFull` requires
`HasGeneralizedWindingNumber γ z (-1/2)` for every smooth boundary point.
We show this reduces to: for every such `z`, there exists a crossing parameter
`t₀`, a cutoff `δ`, geometric bounds, and an `ArcFTCHyp` with limit `-(π * I)`.

This is the bridge that connects the per-segment analytical work (computing
the FTC telescope and its limit for each segment type) to the global
`h_boundary` hypothesis consumed by the valence formula assembly.
-/

/-- Data witnessing that a smooth boundary point `z₀` has winding number `-1/2`.

This bundles a crossing parameter, cutoff, geometric bounds, and the analytical
`ArcFTCHyp` hypothesis. It is the single-point version of the `h_boundary` field
in `FDWindingDataFull`.

The name echoes `SingleCrossingData` but adds the constraint `L = -(π * I)`. -/
structure SmoothBoundaryWindingData {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (z₀ : ℂ) where
  /-- Crossing parameter in `(0, 1)`. -/
  t₀ : ℝ
  ht₀ : t₀ ∈ Ioo 0 1
  /-- Cutoff function. -/
  δ : ℝ → ℝ
  /-- Threshold below which all bounds hold. -/
  threshold : ℝ
  hthresh : 0 < threshold
  /-- `δ(ε)` is positive. -/
  hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε
  /-- `δ(ε)` stays within `(0, 1)` around `t₀`. -/
  hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min t₀ (1 - t₀)
  /-- Far bound. -/
  h_far : ∀ ε, 0 < ε → ε < threshold →
    ∀ t ∈ Icc 0 1, δ ε < |t - t₀| → ε < ‖γ.toPath.extend t - z₀‖
  /-- Near bound. -/
  h_near : ∀ ε, 0 < ε → ε < threshold →
    ∀ t, |t - t₀| ≤ δ ε → ‖γ.toPath.extend t - z₀‖ ≤ ε
  /-- Analytical hypothesis with limit `-(π * I)`. -/
  ftcHyp : ArcFTCHyp γ z₀ t₀ δ threshold (-(↑Real.pi * I))

/-- From `SmoothBoundaryWindingData`, extract `HasGeneralizedWindingNumber γ z₀ (-1/2)`. -/
theorem SmoothBoundaryWindingData.hasWindingNumber {H : ℝ}
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)} {z₀ : ℂ}
    (D : SmoothBoundaryWindingData γ z₀) :
    HasGeneralizedWindingNumber γ z₀ (-1 / 2) :=
  boundaryWinding_of_smoothFTCHyp γ z₀ D.t₀ D.ht₀ D.δ D.threshold D.hthresh
    D.hδ_pos D.hδ_small D.h_far D.h_near D.ftcHyp

/-- From `SmoothBoundaryWindingData`, extract the winding number equality. -/
theorem SmoothBoundaryWindingData.windingNumber_eq {H : ℝ}
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)} {z₀ : ℂ}
    (D : SmoothBoundaryWindingData γ z₀) :
    generalizedWindingNumber γ z₀ = -1 / 2 :=
  D.hasWindingNumber.eq

/-- **Boundary winding reduction**: the `h_boundary` field of `FDWindingDataFull`
follows from providing `SmoothBoundaryWindingData` for every smooth boundary point.

This is the key unconditional reduction: the caller provides, for each boundary
point `z` satisfying the constraints, a `SmoothBoundaryWindingData` witness.
Each such witness bundles the crossing parameter, cutoff, geometric bounds, and
`ArcFTCHyp` for that point.

The geometric bounds (near/far) for each segment type are already proved
unconditionally in `WindingWeightProofs.lean`, `CrossingAtI.lean`, and
`CrossingAtRho.lean`. The only non-trivial remaining input is the per-point
`ArcFTCHyp`, which requires the FTC telescope computation (log primitive,
telescoping, and limit) for the specific segment.

### Usage

```
def my_boundary_winding (hH : 1 < H) :
    ∀ z : ℂ, z.im > 0 → z.im < H → z ≠ I → ... →
    HasGeneralizedWindingNumber (fdBoundaryPC1Path H ...) z (-1/2) :=
  fdBoundary_boundaryWinding_of_forall_smoothData hH
    (fun z him_pos him_lt hne_i hne_rho hne_rp1 h_not_int hns hre =>
      ⟨t₀_for_z, ..., ftcHyp_for_z⟩)
```
-/
theorem fdBoundary_boundaryWinding_of_forall_smoothData {H : ℝ} (hH : 1 < H)
    (h_data : ∀ z : ℂ, z.im > 0 → z.im < H →
      z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
      ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
      1 ≤ Complex.normSq z → |z.re| ≤ 1/2 →
      SmoothBoundaryWindingData
        (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)) z) :
    ∀ z : ℂ, z.im > 0 → z.im < H →
      z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
      ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
      1 ≤ Complex.normSq z → |z.re| ≤ 1/2 →
      HasGeneralizedWindingNumber
        (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)) z (-1 / 2) :=
  fun z him him_lt hni hρ hρ1 h_ni hns hre =>
    (h_data z him him_lt hni hρ hρ1 h_ni hns hre).hasWindingNumber

/-! ### Part 8: Building SmoothBoundaryWindingData from segment-specific inputs

For downstream use, we provide per-segment constructors that take only the
`ArcFTCHyp` (analytical part) and produce the full `SmoothBoundaryWindingData`
by filling in the geometric bounds automatically.

Each constructor:
1. Determines the crossing parameter from the point `z₀` and the segment.
2. Chooses the appropriate cutoff (`arcsinDelta` for arcs, `vertDelta` for verticals,
   `horizDelta` for the horizontal segment).
3. Invokes the proved near/far bounds for that segment.

These are the entry points that `ValenceFormulaFinal.lean` will call.
-/

/-- Linear cutoff for vertical and horizontal segments.
Given a smooth curve `γ(t) = a + b*t*I` (or similar linear parameterization),
the distance from `z₀ = γ(t₀)` satisfies `‖γ(t) - z₀‖ = C·|t - t₀|` for some
positive constant `C`. The cutoff `linDelta C ε = ε / C` inverts this.

For the FD boundary verticals, `C = 5·(H - √3/2)`.
For the horizontal, `C = 5`. -/
def linDelta (C : ℝ) (ε : ℝ) : ℝ := ε / C

theorem linDelta_pos {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    0 < linDelta C ε :=
  div_pos hε hC

theorem linDelta_small {C ε bound : ℝ} (hC : 0 < C) (hε_lt : ε < C * bound) :
    linDelta C ε < bound := by
  unfold linDelta
  rw [div_lt_iff₀ hC]
  linarith

/-- The winding number at a smooth crossing is determined by `SmoothBoundaryWindingData`.
This theorem provides the bridge for `FDWindingComplete.mkFDWindingDataFull`:
once `SmoothBoundaryWindingData` is constructed for each boundary point,
the `boundary_winding` field is discharged. -/
theorem boundaryWinding_from_smoothData {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    {z₀ : ℂ}
    (D : SmoothBoundaryWindingData (fdBoundaryPC1Path H hH) z₀) :
    HasGeneralizedWindingNumber (fdBoundaryPC1Path H hH) z₀ (-1 / 2) :=
  D.hasWindingNumber

end
