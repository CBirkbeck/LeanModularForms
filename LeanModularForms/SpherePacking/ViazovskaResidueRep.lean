/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.SpherePacking.ContourLimitAtCusp
import LeanModularForms.SpherePacking.RectangularContour
import LeanModularForms.SpherePacking.TriangleContour
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

The original plan was to derive the decomposition `I12 = I12_vert + I12_horiz`
(now `I12_eq_rectangular_via_triangle` below) using only the new
HW-3.3-flavoured infrastructure. After analysis, this turned out to be
fundamentally mismatched with `cauchy_rectangle_zero` + cusp decay
for two independent reasons:

* **Geometric mismatch.** Despite the historical name, the decomposition
  `I12 = I12_vert + I12_horiz` is a *triangular*
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

/-! ## Triangular contour validation for the I12 integrand

The Viazovska left integrand `F(z) = φ₀(-1/(z+1)) · (z+1)² · e^{πirz}` is
holomorphic on the open upper half-plane `{z : ℂ | 0 < z.im}`, which is
convex (`convex_halfSpace_im_gt 0`) and open. By `cauchy_triangle_zero`
(HW 3.3 specialised to `S = ∅`), the contour integral of `F` around any
triangle strictly inside the upper half-plane is zero.

This is the parallel of `viazovska_tail_rectangle_cauchy` for the triangular
contour. It is the key building block for the triangle-based proof of
`I12_eq_rectangular_via_triangle`, which states
`I12 = I12_vert + I12_horiz`.
-/

/-- **Cauchy on a triangle for the I12 integrand.** For any triangle whose
three vertices lie strictly inside the open upper half-plane, the contour
integral of `viazovska_integrand_left r` around its boundary is zero.

This is a direct instantiation of `cauchy_triangle_zero` on the convex open
set `{z : ℂ | 0 < z.im}`, using the holomorphicity of the left integrand
(`viazovska_integrand_left_differentiableOn`). -/
theorem viazovska_left_triangle_cauchy
    {a b c : ℂ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (ha : 0 < a.im) (hb : 0 < b.im) (hc : 0 < c.im) (r : ℝ) :
    (triangleContour a b c hab hbc hca).toPwC1Immersion.toPiecewiseC1Path.contourIntegral
        (viazovska_integrand_left r) = 0 :=
  cauchy_triangle_zero hab hbc hca
    (U := {z : ℂ | 0 < z.im}) UpperHalfPlane.isOpen_upperHalfPlaneSet
    ⟨I, by change 0 < (I : ℂ).im; simp⟩
    convex_upperHalfPlaneSet ha hb hc (viazovska_integrand_left_differentiableOn r)

/-! ## Triangle-based re-derivation of `I12 = I12_vert + I12_horiz`

We prove `I12 = I12_vert + I12_horiz` (originally proved in
`ViazovskaMagicFunction.lean` via path-independence through a primitive; that
legacy proof has been retired) using the new triangle Cauchy infrastructure.

**Strategy.** For each `δ ∈ (0, 1)`, the triangle with vertices
`(-1 + δI, -1 + I, I)` lies strictly inside the upper half-plane. By
`cauchy_triangle_zero` and the segment decomposition
`contourIntegral_triangleContour_eq`, the sum of the three segment integrals
is zero:

1. **Vertical sub-side** `(P_δ → -1 + I)` (where `P_δ := -1 + δI`): a sub-segment
   of `I12_vert`. Specifically equals `G(-1+I) - G(P_δ)` by FTC.

2. **Horizontal side** `(-1+I → I)`: exactly `I12_horiz r`. Equals `G(I) - G(-1+I)`
   by FTC.

3. **Slanted closing side** `(I → P_δ)`: equals `G(P_δ) - G(I)` by FTC.

Triangle Cauchy gives `0 = sum`, which combined with FTC representations of
`I12 r`, `I12_vert r`, `I12_horiz r` (via `I12_split_at_delta`, `ftc_tail_diag`,
`I12_vert_split_at_delta`, `ftc_tail_vert`, `horizontal_eq_primitive_sub`)
yields
```
I12 r - (I12_vert r + I12_horiz r) =
  HeadDiag(δ) - HeadVert(δ) + G(-1 + δI) - G(-1 + δ + δI)
```
The δ → 0⁺ limit of the RHS is `0` by `head_integral_tendsto_zero` and
`G_diff_tendsto_zero`. Hence `I12 r = I12_vert r + I12_horiz r`.
-/

/-- The vertices `-1 + δI`, `-1 + I`, `I` of the truncated triangle are pairwise
distinct for `0 < δ < 1`. This is needed to instantiate `triangleContour`. -/
private lemma triangle_vertices_distinct {δ : ℝ} (_hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    ((-1 + ↑δ * I : ℂ) ≠ -1 + I) ∧ ((-1 + I : ℂ) ≠ I) ∧ ((I : ℂ) ≠ -1 + ↑δ * I) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have him := congrArg Complex.im h
    simp [Complex.add_im, Complex.mul_im] at him
    linarith
  · intro h
    have hre := congrArg Complex.re h
    simp at hre
  · intro h
    have hre := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re] at hre

/-- The three vertices `-1 + δI`, `-1 + I`, `I` lie in the open upper half-plane
for `0 < δ`. -/
private lemma triangle_vertices_im_pos {δ : ℝ} (hδ_pos : 0 < δ) :
    (0 < (-1 + ↑δ * I : ℂ).im) ∧ (0 < (-1 + I : ℂ).im) ∧ (0 < (I : ℂ).im) := by
  refine ⟨?_, ?_, ?_⟩
  · change 0 < (-1 + ↑δ * I : ℂ).im; simp; linarith
  · change 0 < (-1 + I : ℂ).im; simp
  · change 0 < (I : ℂ).im; simp

/-- The first side of the triangle `(-1 + δI, -1 + I, I)` parameterised on
`[0, 1]` is the vertical sub-segment from height `δ` to height `1` at `x = -1`.
Specifically, `∫ s in 0..1, F(-1+δI + s•((-1+I)-(-1+δI))) * ((-1+I)-(-1+δI))`
equals the FTC tail `G(-1+I) - G(-1+δI)`. -/
private lemma triangle_side1_eq_primitive_sub (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovska_integrand_left r z) z)
    {δ : ℝ} (hδ_pos : 0 < δ) :
    (∫ s in (0:ℝ)..1, viazovska_integrand_left r
        ((-1 + ↑δ * I) + s • ((-1 + I) - (-1 + ↑δ * I))) *
          ((-1 + I) - (-1 + ↑δ * I))) =
      G (-1 + I) - G (-1 + ↑δ * I) :=
  segment_integral_eq_sub_of_hasDerivAt convex_upperHalfPlaneSet
    (neg_one_add_delta_I_mem_uhp hδ_pos) neg_one_add_I_mem_uhp hG
    (viazovska_integrand_left_differentiableOn r).continuousOn

/-- The second side of the triangle `(-1+δI, -1+I, I)` parameterised on
`[0, 1]` is the horizontal segment from `-1 + I` to `I`. This equals
`G(I) - G(-1 + I)` by FTC. -/
private lemma triangle_side2_eq_primitive_sub (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovska_integrand_left r z) z) :
    (∫ s in (0:ℝ)..1, viazovska_integrand_left r
        ((-1 + I) + s • (I - (-1 + I))) * (I - (-1 + I))) =
      G I - G (-1 + I) :=
  segment_integral_eq_sub_of_hasDerivAt convex_upperHalfPlaneSet
    neg_one_add_I_mem_uhp I_mem_uhp hG
    (viazovska_integrand_left_differentiableOn r).continuousOn

/-- The third (slanted) side of the triangle `(-1+δI, -1+I, I)` parameterised
on `[0, 1]`: the segment from `I` back to `-1 + δI`. This equals
`G(-1+δI) - G(I)` by FTC. -/
private lemma triangle_side3_eq_primitive_sub (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovska_integrand_left r z) z)
    {δ : ℝ} (hδ_pos : 0 < δ) :
    (∫ s in (0:ℝ)..1, viazovska_integrand_left r
        (I + s • ((-1 + ↑δ * I) - I)) * ((-1 + ↑δ * I) - I)) =
      G (-1 + ↑δ * I) - G I :=
  segment_integral_eq_sub_of_hasDerivAt convex_upperHalfPlaneSet
    I_mem_uhp (neg_one_add_delta_I_mem_uhp hδ_pos) hG
    (viazovska_integrand_left_differentiableOn r).continuousOn

/-- The contour integral around the triangle `(-1+δI, -1+I, I)` for the Viazovska
integrand decomposes as the sum of the three segment integrals between vertices.
This is `contourIntegral_triangleContour_eq` specialised; needs continuity of
the integrand on the triangle's image, supplied by holomorphicity on the UHP. -/
private lemma triangle_contour_decomposition (r : ℝ) {δ : ℝ}
    (hδ_pos : 0 < δ)
    (hab : (-1 + ↑δ * I : ℂ) ≠ -1 + I)
    (hbc : (-1 + I : ℂ) ≠ I)
    (hca : (I : ℂ) ≠ -1 + ↑δ * I) :
    (triangleContour (-1 + ↑δ * I) (-1 + I) I hab hbc hca).toPwC1Immersion.toPiecewiseC1Path.contourIntegral
        (viazovska_integrand_left r)
      = (∫ s in (0:ℝ)..1, viazovska_integrand_left r
          ((-1 + ↑δ * I) + s • ((-1 + I) - (-1 + ↑δ * I))) * ((-1 + I) - (-1 + ↑δ * I)))
      + (∫ s in (0:ℝ)..1, viazovska_integrand_left r
          ((-1 + I) + s • (I - (-1 + I))) * (I - (-1 + I)))
      + (∫ s in (0:ℝ)..1, viazovska_integrand_left r
          (I + s • ((-1 + ↑δ * I) - I)) * ((-1 + ↑δ * I) - I)) := by
  refine contourIntegral_triangleContour_eq hab hbc hca ?_
  -- Continuity of `viazovska_integrand_left r` on the image of the triangle path.
  -- The image lies inside the UHP (`triangleContour_image_subset_of_convex`),
  -- where the integrand is holomorphic and hence continuous.
  refine (viazovska_integrand_left_differentiableOn r).continuousOn.mono ?_
  rintro _ ⟨t, ht, rfl⟩
  exact triangleContour_image_subset_of_convex hab hbc hca convex_upperHalfPlaneSet
    (neg_one_add_delta_I_mem_uhp hδ_pos) neg_one_add_I_mem_uhp I_mem_uhp t ht

/-- For each `δ ∈ (0, 1)`, the difference `I12 r - (I12_vert r + I12_horiz r)`
equals the sum of three "small" terms that all vanish as `δ → 0⁺`:
the diagonal head, the (negative) vertical head, and the difference of the
primitive `G` at the two truncation points. This is the algebraic identity
obtained by combining the triangle Cauchy with FTC on the three sides and
on the truncated `I12`/`I12_vert` integrals. -/
private lemma I12_difference_eq_via_triangle (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovska_integrand_left r z) z)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    I12 r - (I12_vert r + I12_horiz r) =
      (∫ t in (0:ℝ)..δ, viazovska_integrand_left r (contour_neg1_to_i t) * (1 + I)) -
      (∫ t in (0:ℝ)..δ, viazovska_integrand_left r (-1 + I * ↑t) * I) +
      (G (-1 + ↑δ * I) - G (contour_neg1_to_i δ)) := by
  -- Triangle Cauchy: contour integral around (a, b, c) is zero.
  obtain ⟨hab, hbc, hca⟩ := triangle_vertices_distinct hδ_pos hδ_lt
  obtain ⟨ha_im, hb_im, hc_im⟩ := triangle_vertices_im_pos hδ_pos
  have h_cauchy := viazovska_left_triangle_cauchy hab hbc hca ha_im hb_im hc_im r
  -- Decompose the triangle contour into three side integrals.
  have h_decomp := triangle_contour_decomposition r hδ_pos hab hbc hca
  -- Combine: from `h_cauchy = 0` and `h_decomp`, we get `side1 + side2 + side3 = 0`.
  have h_sides_sum : (∫ s in (0:ℝ)..1, viazovska_integrand_left r
          ((-1 + ↑δ * I) + s • ((-1 + I) - (-1 + ↑δ * I))) * ((-1 + I) - (-1 + ↑δ * I)))
      + (∫ s in (0:ℝ)..1, viazovska_integrand_left r
          ((-1 + I) + s • (I - (-1 + I))) * (I - (-1 + I)))
      + (∫ s in (0:ℝ)..1, viazovska_integrand_left r
          (I + s • ((-1 + ↑δ * I) - I)) * ((-1 + ↑δ * I) - I)) = 0 := by
    rw [← h_decomp]; exact h_cauchy
  -- Evaluate each side via FTC.
  have h_side1 := triangle_side1_eq_primitive_sub r G hG hδ_pos
  have h_side2 := triangle_side2_eq_primitive_sub r G hG
  have h_side3 := triangle_side3_eq_primitive_sub r G hG hδ_pos
  -- Substituting FTC into `h_sides_sum`:
  rw [h_side1, h_side2, h_side3] at h_sides_sum
  -- The result is `(G(-1+I) - G(-1+δI)) + (G(I) - G(-1+I)) + (G(-1+δI) - G(I)) = 0`,
  -- which is algebraically trivial.
  -- Now express `I12`, `I12_vert`, `I12_horiz` via head + primitive_difference.
  have hsd := I12_split_at_delta r δ hδ_pos.le hδ_lt.le (continuousOn_diagonal_integrand r)
  have htd := ftc_tail_diag r G hG δ hδ_pos hδ_lt.le
  have hc1 : contour_neg1_to_i 1 = I := by simp [contour_neg1_to_i]
  rw [hc1] at htd
  have hsv := I12_vert_split_at_delta r δ hδ_pos.le hδ_lt.le (continuousOn_vertical_integrand r)
  have htv := ftc_tail_vert r G hG δ hδ_pos hδ_lt.le
  have hv1 : (-1 : ℂ) + I * (1 : ℝ) = -1 + I := by push_cast; ring
  rw [hv1] at htv
  have hhoriz := horizontal_eq_primitive_sub r G hG
  have hcomm : (-1 : ℂ) + ↑δ * I = -1 + I * ↑δ := by ring
  rw [hcomm]
  linear_combination hsd + htd - hsv - htv - hhoriz

/-- **The rectangular decomposition of `I12`, via the triangle Cauchy theorem.**
Proves `I12 r = I12_vert r + I12_horiz r` using the new triangular Cauchy
theorem (`cauchy_triangle_zero`) and the contour decomposition
(`contourIntegral_triangleContour_eq`), instead of the legacy
path-independence argument (since retired from `ViazovskaMagicFunction.lean`).

The full proof uses:
* `cauchy_triangle_zero` (HW 3.3, `S = ∅`) for the truncated triangle
  `(-1 + δI, -1 + I, I)` with `0 < δ < 1`.
* `contourIntegral_triangleContour_eq` to decompose the triangle contour
  into three segment integrals.
* `head_integral_tendsto_zero` (×2) and `G_diff_tendsto_zero` from
  `ViazovskaMagicFunction.lean` for the `δ → 0⁺` limit.
-/
theorem I12_eq_rectangular_via_triangle (r : ℝ) :
    I12 r = I12_vert r + I12_horiz r := by
  suffices hsuff : I12 r - (I12_vert r + I12_horiz r) = 0 from eq_of_sub_eq_zero hsuff
  obtain ⟨G, hG⟩ := exists_primitive_viazovska_integrand_left r
  set F := viazovska_integrand_left r
  set S := fun δ : ℝ => (∫ t in (0:ℝ)..δ, F (contour_neg1_to_i t) * (1 + I)) -
    (∫ t in (0:ℝ)..δ, F (-1 + I * ↑t) * I) + (G (-1 + ↑δ * I) - G (contour_neg1_to_i δ))
  -- For each `δ ∈ (0, 1)`, the difference equals `S δ` by the triangle-Cauchy identity.
  have heq : ∀ᶠ δ in 𝓝[>] 0, I12 r - (I12_vert r + I12_horiz r) = S δ := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℝ) one_pos)] with δ hδ hδ_ball
    simp only [Set.mem_Ioi] at hδ
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at hδ_ball
    exact I12_difference_eq_via_triangle r G hG hδ (by linarith [abs_of_pos hδ])
  -- As `δ → 0⁺`, all three terms of `S` tend to zero.
  have hS : Filter.Tendsto S (𝓝[>] 0) (𝓝 0) := by
    have := (head_integral_tendsto_zero (continuousOn_diagonal_integrand r)).sub
      (head_integral_tendsto_zero (continuousOn_vertical_integrand r))
      |>.add (G_diff_tendsto_zero r G hG)
    simp only [S]
    simpa using this
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' heq) hS

end LeanModularForms

end
