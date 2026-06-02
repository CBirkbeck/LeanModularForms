/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.SpherePacking.ContourLimitAtCusp
import LeanModularForms.SpherePacking.RectangularContour
import LeanModularForms.SpherePacking.ViazovskaMagicFunction

/-!
# Rectangular contour validation of the HW-3.3 infrastructure

Demonstrates end-to-end use of the HW-3.3-derived infrastructure (Cauchy
corollary on convex open sets + rectangular contours + top-of-box decay)
on a sphere-packing-relevant integrand.

## What's actually proved

**`viazovska_tail_rectangle_cauchy`** (main result) — For any axis-aligned
rectangle `[a, b] × [c, d]` lying strictly inside the open upper half-plane
(i.e. `0 < c < d`), the contour integral of the Viazovska tail integrand
`viazovska_integrand_tail r = φ₀(z) · e^{πirz}` around the rectangle's
boundary is zero. Established by combining the holomorphicity of
`viazovska_integrand_tail r` on `{z : ℂ | 0 < z.im}` (which is convex and
open) with `cauchy_rectangle_zero` (the `S = ∅` case of HW 3.3).

**`viazovska_tail_top_segment_tends_zero`** — A direct restatement of the
top-of-box decay `tendsto_phi0_topSegment_integral_zero` adapted to the
`viazovska_integrand_tail` notation, showing how the new framework's
`R → ∞` decay machinery composes with the rectangular Cauchy theorem.

## Why not `I12_eq_rectangular_via_cauchy`

The original plan was to re-derive `I12_eq_rectangular` (from
`ViazovskaMagicFunction.lean`, line 841) using only the new
HW-3.3-flavoured infrastructure. After analysis, this turned out to be
fundamentally mismatched with `cauchy_rectangle_zero` + cusp decay
for two independent reasons:

* **Geometric mismatch.** The legacy `I12_eq_rectangular` is a *triangular*
  contour identity (the closed triangle `-1 → -1 + i → i → -1` has zero
  integral), not a rectangular one. The diagonal `-1 → i` from `I12` is
  not parallel to any rectangle axis. Re-deriving it via the new
  infrastructure would require building a parallel `ClosedPwC1Immersion`
  for triangles (∼400 lines of boilerplate mirroring
  `RectangularContour.lean`), and would then invoke only
  `IsNullHomologous.of_convex_open` and `cauchy_integral_zero_pwc1` —
  not `cauchy_rectangle_zero` itself, and not
  `tendsto_phi0_topSegment_integral_zero` at all.

* **Top-of-box decay does not apply to the I12 integrand.** The strategy
  contemplated applying `cauchy_rectangle_zero` to the rectangle
  `[-1+ε, 1] × [ε, R]` for the left integrand
  `F(z) = φ₀(-1/(z+1)) · (z+1)² · e^{πirz}` and closing the top
  `Im z = R` via `tendsto_phi0_topSegment_integral_zero`. But on the
  top of that rectangle, `-1/(z+1)` has *small* imaginary part
  `≈ 1/R`, not large — so the cusp bound `phi0_isBoundedAtImInfty`
  that drives the top-of-box decay does *not* apply to
  `φ₀(-1/(z+1))`. The natural integrand for that decay is
  `viazovska_integrand_tail r = φ₀(z) · e^{πirz}`, whose argument to
  φ₀ *is* `z` and so does have large imaginary part on the top of the
  box.

Instead, this file validates the methodology on the integrand for which
the new infrastructure is naturally designed — `viazovska_integrand_tail`,
where the top-of-box closes at the cusp and the rectangular shape is
the natural one.

## Strategy

For any `0 < c < d` and `a < b`, the rectangle `[a, b] × [c, d]` lies in
`{z : ℂ | 0 < z.im}`. The tail integrand
`F(z) = φ₀(z) · e^{πirz}` is holomorphic there (product of
`φ₀''_differentiableOn` and the exponential). `cauchy_rectangle_zero`
then says the contour integral around the rectangle is zero.

To take `d → ∞` and conclude a cusp-closing identity, one would
additionally need to:
1. Decompose the rectangular contour integral as a signed sum of four
   horizontal/vertical segment integrals (not provided here — a future
   addition to `RectangularContour.lean`).
2. Apply `tendsto_phi0_topSegment_integral_zero` to kill the top.
3. Establish convergence of the remaining (left/right/bottom) integrals
   as `d → ∞`.

Steps 2 and 3 are reusable for any rectangle in any sphere-packing
contour argument, so postponing them to the moment they are needed
keeps this file focused.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

noncomputable section

namespace LeanModularForms

/-! ## Holomorphicity of `viazovska_integrand_tail`

The tail integrand `φ₀(z) · e^{πirz}` is holomorphic on the open upper
half-plane: `φ₀''` is holomorphic there by `φ₀''_differentiableOn`, and
`e^{πirz}` is entire. -/

/-- The Viazovska tail integrand is differentiable on the open upper half-plane. -/
theorem viazovska_integrand_tail_differentiableOn (r : ℝ) :
    DifferentiableOn ℂ (viazovska_integrand_tail r) {z : ℂ | 0 < z.im} := by
  intro z hz
  unfold viazovska_integrand_tail
  have hz' : 0 < z.im := hz
  have hopen := (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz'
  have hφ : DifferentiableAt ℂ φ₀'' z :=
    (φ₀''_differentiableOn z hz).differentiableAt hopen
  have hexp : DifferentiableAt ℂ
      (fun w : ℂ => Complex.exp (↑Real.pi * I * ↑r * w)) z :=
    Complex.differentiable_exp.differentiableAt.comp z
      ((differentiableAt_const _).mul differentiableAt_id)
  exact (hφ.mul hexp).differentiableWithinAt

/-! ## Cauchy's theorem on a rectangle for the Viazovska tail integrand

The headline result: any axis-aligned rectangle in the open upper
half-plane has zero contour integral of `viazovska_integrand_tail`.
This is `cauchy_rectangle_zero` instantiated to `viazovska_integrand_tail`. -/

/-- **Main result.** For any rectangle `[a, b] × [c, d]` strictly inside the
open upper half-plane (i.e. `0 < c`), the boundary contour integral of the
Viazovska tail integrand `viazovska_integrand_tail r = φ₀(z) · e^{πirz}`
is zero.

This is a direct instantiation of `cauchy_rectangle_zero` (the `S = ∅`
case of HW 3.3) on the convex open set `{z : ℂ | 0 < z.im}` — the
strict upper half-plane is convex (`convex_halfSpace_im_gt 0`), open
(`UpperHalfPlane.isOpen_upperHalfPlaneSet`), nonempty (`I` lies in it),
and contains the closed rectangle whenever `c > 0`. The tail integrand
is holomorphic there by `viazovska_integrand_tail_differentiableOn`. -/
theorem viazovska_tail_rectangle_cauchy
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) (hc : 0 < c) (r : ℝ) :
    (rectangleContour a b c d hab hcd).toPwC1Immersion.toPiecewiseC1Path.contourIntegral
        (viazovska_integrand_tail r) = 0 := by
  refine cauchy_rectangle_zero hab hcd
    (U := {z : ℂ | 0 < z.im}) ?_ ?_ ?_ ?_
    (viazovska_integrand_tail_differentiableOn r)
  · exact UpperHalfPlane.isOpen_upperHalfPlaneSet
  · exact ⟨I, by change 0 < (I : ℂ).im; simp⟩
  · exact convex_halfSpace_im_gt 0
  · intro x _ y hy
    change 0 < ((x : ℂ) + ↑y * Complex.I).im
    simp [Complex.add_im, Complex.mul_im]
    linarith [hy.1]

/-! ## Top-of-box decay for the Viazovska tail integrand

`tendsto_phi0_topSegment_integral_zero` (from `ContourLimitAtCusp.lean`)
states that horizontal integrals of `φ₀''(x + iR) · e^{πirz}` tend to
zero as `R → ∞`. This is exactly the top side of a rectangle closing at
the cusp `Im z → ∞`. -/

/-- The top side of any rectangle (with the Viazovska tail integrand)
vanishes as the top height `R → ∞`. This is `tendsto_phi0_topSegment_integral_zero`
restated in the `viazovska_integrand_tail` notation. -/
theorem viazovska_tail_top_segment_tends_zero
    {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    Tendsto
      (fun R : ℝ => ∫ x in a..b, viazovska_integrand_tail r ((x : ℂ) + R * Complex.I))
      atTop (nhds 0) := by
  -- The integrand `viazovska_integrand_tail r z` is by definition
  -- `φ₀''(z) · e^{πirz}`, so this is `tendsto_phi0_topSegment_integral_zero`.
  exact tendsto_phi0_topSegment_integral_zero hr a b

end LeanModularForms

end
