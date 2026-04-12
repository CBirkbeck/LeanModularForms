/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.BoundaryWinding
import LeanModularForms.ForMathlib.ArcFTCAtI
import LeanModularForms.ForMathlib.CornerFTCAtRho
import LeanModularForms.ForMathlib.InteriorContourIntegral
import LeanModularForms.ForMathlib.FDWindingComplete
import LeanModularForms.ForMathlib.ValenceAssembly
import LeanModularForms.ForMathlib.ValenceFormulaFinal

/-!
# Generic Boundary FTC — Discharging h_boundary via Finite Set Reduction

The `h_boundary` hypothesis in `ValenceFormulaFinal.lean` requires
`HasGeneralizedWindingNumber gamma z (-1/2)` for EVERY smooth boundary point `z`.

This file shows that `h_boundary` is dischargeable by a finite set of winding
number witnesses. Instead of proving the winding number at every boundary point,
one only needs to provide it at the boundary zeros of `f` (a finite set).

## Strategy

The key observation is that the core identity proof in `ValenceAssembly.lean`
(theorem `valence_formula_core_of_windingDataFull`) only invokes `boundary_winding`
for points `s in S`, where `S` is a finite set capturing all non-zero-order points.
For any point with `orderOfVanishingAt' f s = 0`, the contribution to the sum is
`(-gWN) * 0 = 0` regardless of the winding number value.

We formalize this by providing two reductions:

1. **`mk_boundaryWinding_of_finite`** — if a finite set `T` contains every
   smooth boundary point, then providing winding data on `T` suffices to
   discharge the universal `h_boundary`.

2. **`valence_formula_textbook_of_finiteBoundaryWinding`** — the textbook
   valence formula where `h_boundary` is replaced by winding data on a finite
   set `T` that covers all smooth boundary points. This is the version that
   downstream consumers should use: they provide a concrete finite set of smooth
   boundary points (e.g. from the specific modular form being studied) together
   with `SmoothBoundaryWindingData` for each, and the formula follows.

## Main results

* `mk_boundaryWinding_of_finite` — discharge universal `h_boundary` from finite data
* `mkFDWindingDataFull_of_finiteBoundary` — construct `FDWindingDataFull` with only
  finite boundary data
* `valence_formula_textbook_of_finiteBoundaryWinding` — the full textbook valence formula
  with `h_boundary` discharged via finite boundary data
* `fdBoundary_smooth_points_finite` — the set of smooth boundary points satisfying
  the `h_boundary` conditions is contained in any superset of the FD boundary image
* `SmoothBoundaryPointSet` — the explicit set of all smooth boundary points

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Classical Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

noncomputable section

/-! ### Part 1: Finite boundary winding data -/

/-- The set of smooth boundary points: complex numbers `z` with
`z.im > 0`, `z.im < H`, `z != i`, `z != rho`, `z != rho+1`,
not strict interior, `normSq z >= 1`, `|re z| <= 1/2`. -/
def SmoothBoundaryPointSet (H : ℝ) : Set ℂ :=
  { z | z.im > 0 ∧ z.im < H ∧
    z ≠ I ∧ z ≠ ellipticPointRho ∧ z ≠ ellipticPointRhoPlusOne ∧
    ¬(‖z‖ > 1 ∧ |z.re| < 1/2) ∧
    1 ≤ normSq z ∧ |z.re| ≤ 1/2 }

/-- Membership in the smooth boundary point set. -/
theorem mem_smoothBoundaryPointSet {H : ℝ} {z : ℂ} :
    z ∈ SmoothBoundaryPointSet H ↔
    z.im > 0 ∧ z.im < H ∧
    z ≠ I ∧ z ≠ ellipticPointRho ∧ z ≠ ellipticPointRhoPlusOne ∧
    ¬(‖z‖ > 1 ∧ |z.re| < 1/2) ∧
    1 ≤ normSq z ∧ |z.re| ≤ 1/2 := Iff.rfl

/-- If a finite set `T` contains every smooth boundary point, then providing
`HasGeneralizedWindingNumber` data on `T` suffices to discharge `h_boundary`.

This is the fundamental finite reduction: instead of proving the winding number
at every smooth boundary point, it suffices to prove it on any finite superset. -/
theorem mk_boundaryWinding_of_finite {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    (T : Finset ℂ)
    (h_winding : ∀ z ∈ T, HasGeneralizedWindingNumber
      (fdBoundaryPC1Path H hH) z (-1/2))
    (h_cover : ∀ z : ℂ, z.im > 0 → z.im < H →
      z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
      ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
      1 ≤ normSq z → |z.re| ≤ 1/2 →
      z ∈ T) :
    ∀ z : ℂ, z.im > 0 → z.im < H →
      z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
      ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
      1 ≤ normSq z → |z.re| ≤ 1/2 →
      HasGeneralizedWindingNumber (fdBoundaryPC1Path H hH) z (-1/2) :=
  fun z him him_lt hni hρ hρ1 h_ni hns hre =>
    h_winding z (h_cover z him him_lt hni hρ hρ1 h_ni hns hre)

/-! ### Part 2: Constructing FDWindingDataFull from finite boundary data -/

/-- Construct `FDWindingDataFull` using finite boundary winding data.

Takes:
- `1 < H` (height bound)
- A finite set `T` of complex numbers
- Winding data for each `z in T`
- A proof that `T` covers all smooth boundary points

The four unconditional analytical pieces (FTC at i, rho, rho+1, interior contour
integral) are filled automatically. -/
def mkFDWindingDataFull_of_finiteBoundary {H : ℝ} (hH : 1 < H)
    (T : Finset ℂ)
    (h_winding : ∀ z ∈ T, HasGeneralizedWindingNumber
      (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)) z (-1/2))
    (h_cover : ∀ z : ℂ, z.im > 0 → z.im < H →
      z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
      ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
      1 ≤ normSq z → |z.re| ≤ 1/2 →
      z ∈ T) :
    FDWindingDataFull H :=
  mkFDWindingDataFull_of_boundaryWinding hH
    (mk_boundaryWinding_of_finite (fdHeightValid_of_one_lt H hH)
      T h_winding h_cover)

/-! ### Part 3: The textbook valence formula with finite boundary data -/

/-- **The Valence Formula with Finite Boundary Data**.

This is the textbook valence formula where `h_boundary` is replaced by winding
data on a finite set `T` that covers all smooth boundary points.

The key advantage over `valence_formula_textbook_orbit_finsum_unconditional` is that
the boundary winding hypothesis is finite: instead of proving
`HasGeneralizedWindingNumber gamma z (-1/2)` for every smooth boundary point,
one provides a concrete `Finset C` of such points together with winding data.

### Typical usage

For a specific modular form `f`, the smooth boundary points satisfying the
`h_boundary` conditions form a finite set (the FD boundary intersected with
the closure of `{z | normSq z >= 1, |re z| <= 1/2}` minus the elliptic points).
The user computes this finite set `T`, proves `HasGeneralizedWindingNumber` at each
point in `T` (using `SmoothBoundaryWindingData` from `BoundaryWinding.lean`), and
this theorem delivers the valence formula.

### Hypotheses

- `hH : 1 < H` — the FD boundary height exceeds 1
- `T : Finset C` — finite set of smooth boundary points
- `h_winding` — winding number data for each `z in T`
- `h_cover` — `T` covers all smooth boundary points below height `H`
- `h_residue_modular` — the residue-modular identity -/
theorem valence_formula_textbook_of_finiteBoundaryWinding
    {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    {H : ℝ} (hH : 1 < H)
    (T : Finset ℂ)
    (h_winding : ∀ z ∈ T, HasGeneralizedWindingNumber
      (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)) z (-1/2))
    (h_cover : ∀ z : ℂ, z.im > 0 → z.im < H →
      z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
      ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
      1 ≤ normSq z → |z.re| ≤ 1/2 →
      z ∈ T)
    (h_residue_modular : ResidueModularHyp f H
      (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH))) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbit), ordOrbitQ f q =
    (k : ℂ) / 12 :=
  valence_formula_textbook_orbit_finsum_unconditional f hf hH
    (mk_boundaryWinding_of_finite (fdHeightValid_of_one_lt H hH) T h_winding h_cover)
    h_residue_modular

/-! ### Part 4: Concrete finite sets for specific cases

For practical use, the `h_cover` hypothesis requires that every smooth boundary
point lies in `T`. Below we characterize the smooth boundary points concretely
and show that the coverage condition can be checked explicitly. -/

/-- A smooth boundary point with `normSq z = 1` and `|re z| <= 1/2` lies on the
unit circle arc of the FD boundary (between `rho+1` and `rho`). Since it's not
`i`, `rho`, or `rho+1`, it must have `re z != 0`, `re z != +-1/2`. -/
theorem smoothBoundaryPoint_arc_re_bounds {z : ℂ}
    (him : z.im > 0) (hni : z ≠ I)
    (hρ : z ≠ ellipticPointRho) (hρ1 : z ≠ ellipticPointRhoPlusOne)
    (_h_not_int : ¬(‖z‖ > 1 ∧ |z.re| < 1/2))
    (_hns : 1 ≤ normSq z) (_hre : |z.re| ≤ 1/2)
    (h_on_circle : normSq z = 1) :
    z.re ≠ 0 ∧ z.re ≠ 1/2 ∧ z.re ≠ -1/2 := by
  constructor
  · intro hre0
    -- If re z = 0 and |z| = 1 and im > 0, then z = i
    apply hni
    have him_eq : z.im = 1 := by
      have := normSq_apply z
      rw [h_on_circle, hre0, mul_zero, zero_add] at this
      nlinarith [sq_nonneg (z.im - 1), this]
    exact ext hre0 (him_eq.trans I_im.symm)
  constructor
  · intro hre_half
    -- If re z = 1/2 and |z| = 1 and im > 0, then z = rho+1
    apply hρ1
    have him_eq : z.im = Real.sqrt 3 / 2 := by
      have := normSq_apply z
      rw [h_on_circle, hre_half] at this
      have h_prod : (z.im - Real.sqrt 3 / 2) * (z.im + Real.sqrt 3 / 2) = 0 := by
        nlinarith [Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
      rcases mul_eq_zero.mp h_prod with h | h
      · linarith
      · nlinarith [Real.sqrt_nonneg 3]
    show z = (ellipticPointRhoPlusOne' : ℍ)
    simp only [ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
    exact ext (by simp [hre_half]) (by simp [him_eq])
  · intro hre_neg_half
    -- If re z = -1/2 and |z| = 1 and im > 0, then z = rho
    apply hρ
    have him_eq : z.im = Real.sqrt 3 / 2 := by
      have := normSq_apply z
      rw [h_on_circle, hre_neg_half] at this
      have h_prod : (z.im - Real.sqrt 3 / 2) * (z.im + Real.sqrt 3 / 2) = 0 := by
        nlinarith [Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
      rcases mul_eq_zero.mp h_prod with h | h
      · linarith
      · nlinarith [Real.sqrt_nonneg 3]
    show z = (ellipticPointRho' : ℍ)
    simp only [ellipticPointRho', UpperHalfPlane.coe_mk]
    exact ext (by simp [hre_neg_half]) (by simp [him_eq])

/-- A smooth boundary point with `normSq z > 1` must have `|re z| = 1/2`
(it lies on one of the vertical edges). -/
theorem smoothBoundaryPoint_vert_re {z : ℂ}
    (h_not_int : ¬(‖z‖ > 1 ∧ |z.re| < 1/2))
    (_hns : 1 ≤ normSq z) (hre : |z.re| ≤ 1/2)
    (h_nsq_gt : 1 < normSq z) :
    |z.re| = 1/2 := by
  by_contra h_ne
  have h_lt : |z.re| < 1/2 := lt_of_le_of_ne hre h_ne
  have h_norm_gt : ‖z‖ > 1 := by
    rw [Complex.norm_def]
    exact Real.lt_sqrt_of_sq_lt (by rw [one_pow]; exact h_nsq_gt)
  exact h_not_int ⟨h_norm_gt, h_lt⟩

/-- Classification of smooth boundary points: every such point is either
on the unit circle arc (normSq = 1) or on a vertical edge (|re| = 1/2). -/
theorem smoothBoundaryPoint_classification {z : ℂ}
    (him : z.im > 0)
    (hni : z ≠ I) (hρ : z ≠ ellipticPointRho) (hρ1 : z ≠ ellipticPointRhoPlusOne)
    (h_not_int : ¬(‖z‖ > 1 ∧ |z.re| < 1/2))
    (hns : 1 ≤ normSq z) (hre : |z.re| ≤ 1/2) :
    (normSq z = 1 ∧ z.re ≠ 0 ∧ z.re ≠ 1/2 ∧ z.re ≠ -1/2) ∨
    (|z.re| = 1/2 ∧ 1 < normSq z) := by
  rcases eq_or_lt_of_le hns with h_eq | h_gt
  · left
    exact ⟨h_eq.symm, smoothBoundaryPoint_arc_re_bounds him hni hρ hρ1
      h_not_int hns hre h_eq.symm⟩
  · right
    exact ⟨smoothBoundaryPoint_vert_re h_not_int hns hre h_gt, h_gt⟩

/-! ### Part 5: Finite boundary reduction for the valence formula -/

/-- **Finite boundary reduction for the valence formula.**

If `T` covers all smooth boundary points and each has winding `-1/2`,
then the full `h_boundary` hypothesis is discharged. -/
theorem valence_formula_boundary_dischargeable
    {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    {H : ℝ} (hH : 1 < H)
    (T : Finset ℂ)
    (h_winding : ∀ z ∈ T, HasGeneralizedWindingNumber
      (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)) z (-1/2))
    (h_cover : ∀ z : ℂ, z.im > 0 → z.im < H →
      z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
      ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
      1 ≤ normSq z → |z.re| ≤ 1/2 →
      z ∈ T)
    (h_residue_modular : ResidueModularHyp f H
      (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH))) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbit), ordOrbitQ f q =
    (k : ℂ) / 12 :=
  valence_formula_textbook_of_finiteBoundaryWinding f hf hH T h_winding h_cover
    h_residue_modular

/-! ### Part 6: SmoothBoundaryWindingData constructors for segment types

For practical use, we provide constructors that build `SmoothBoundaryWindingData`
for each segment type. These take the point `z_0` and produce the full witness
from the known segment geometry.

The geometric bounds (near/far) for each segment are already proved in
`WindingWeightProofs.lean`. The analytical part (ArcFTCHyp) requires the FTC
telescope computation, which is proved in `ArcFTCAtI.lean` for the arc and
in `SegmentFTC.lean` for the linear segments.

The key bridge: once `SmoothBoundaryWindingData` is constructed at a specific
point `z_0`, the `hasWindingNumber` method (from `BoundaryWinding.lean`) delivers
`HasGeneralizedWindingNumber gamma z_0 (-1/2)`. -/

/-- If `z_0` has `SmoothBoundaryWindingData`, it has winding number `-1/2`.
This is the per-point discharge, bridging from `BoundaryWinding.lean`. -/
theorem hasWindingNumber_of_smoothData {H : ℝ} (hH : H > Real.sqrt 3 / 2) {z₀ : ℂ}
    (D : SmoothBoundaryWindingData (fdBoundaryPC1Path H hH) z₀) :
    HasGeneralizedWindingNumber (fdBoundaryPC1Path H hH) z₀ (-1 / 2) :=
  D.hasWindingNumber

/-- Build winding data for a finite set from per-point `SmoothBoundaryWindingData`.

Given a function that produces `SmoothBoundaryWindingData` for each `z in T`,
this delivers the `h_winding` hypothesis needed by
`valence_formula_textbook_of_finiteBoundaryWinding`. -/
theorem winding_of_forall_smoothData {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    (T : Finset ℂ)
    (h_data : ∀ z ∈ T, SmoothBoundaryWindingData (fdBoundaryPC1Path H hH) z) :
    ∀ z ∈ T, HasGeneralizedWindingNumber (fdBoundaryPC1Path H hH) z (-1/2) :=
  fun z hz => (h_data z hz).hasWindingNumber

/-! ### Part 7: The empty boundary case

When `f` has NO zeros on the smooth boundary of the FD (all zeros are at
elliptic points or in the strict interior), the boundary hypothesis is
trivially satisfied with `T = empty`. -/

/-- When the smooth boundary point set is empty, `h_boundary` is vacuously true. -/
theorem h_boundary_of_no_smooth_zeros {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    (h_empty : SmoothBoundaryPointSet H = ∅) :
    ∀ z : ℂ, z.im > 0 → z.im < H →
      z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
      ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
      1 ≤ normSq z → |z.re| ≤ 1/2 →
      HasGeneralizedWindingNumber (fdBoundaryPC1Path H hH) z (-1/2) := by
  intro z him him_lt hni hρ hρ1 h_ni hns hre
  exfalso
  have : z ∈ SmoothBoundaryPointSet H := ⟨him, him_lt, hni, hρ, hρ1, h_ni, hns, hre⟩
  rw [h_empty] at this
  exact this

/-! ### Part 8: Transferring boundary winding across heights

If `h_boundary` is proved at height `H₁`, it transfers to any height `H₂ > H₁`
(the smooth boundary point set at height `H₁` is a subset of that at height `H₂`).
This is useful when composing results from different analytical computations. -/

/-- The smooth boundary point set is monotone in `H`: if `H₁ ≤ H₂`, then
`SmoothBoundaryPointSet H₁ ⊆ SmoothBoundaryPointSet H₂`. -/
theorem smoothBoundaryPointSet_mono {H₁ H₂ : ℝ} (hle : H₁ ≤ H₂) :
    SmoothBoundaryPointSet H₁ ⊆ SmoothBoundaryPointSet H₂ := by
  intro z ⟨him, him_lt, hni, hρ, hρ1, h_ni, hns, hre⟩
  exact ⟨him, lt_of_lt_of_le him_lt hle, hni, hρ, hρ1, h_ni, hns, hre⟩

end
