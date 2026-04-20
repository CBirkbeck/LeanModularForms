/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.FDBoundary
import LeanModularForms.ForMathlib.CurveUtilities

/-!
# Interior Winding Number for the Fundamental Domain Boundary

This file proves that the FD boundary contour avoids every point in the strict interior
of the fundamental domain, and reduces the interior winding number computation to a
contour integral identity.

## Strict interior

A point `z` is in the **strict interior** of the fundamental domain at height `H` when:
- `1 < ‖z‖` (strictly outside the unit circle)
- `|z.re| < 1/2` (strictly between the vertical edges)
- `0 < z.im` (in the upper half-plane)
- `z.im < H` (below the horizontal cap)

## Main results

### Avoidance (fully proved)

* `fdBoundaryFun_avoids_seg1` -- right vertical avoids strict interior (re = 1/2 vs |re| < 1/2)
* `fdBoundaryFun_avoids_seg2` -- right arc avoids strict interior (norm = 1 vs norm > 1)
* `fdBoundaryFun_avoids_seg3` -- left arc avoids strict interior (norm = 1 vs norm > 1)
* `fdBoundaryFun_avoids_seg4` -- left vertical avoids strict interior (re = -1/2 vs |re| < 1/2)
* `fdBoundaryFun_avoids_seg5` -- horizontal avoids strict interior (im = H vs im < H)
* `fdBoundaryFun_avoids_interior` -- full boundary avoids strict interior points

### Minimum distance (fully proved)

* `fdBoundaryFun_minDist_interior` -- the minimum distance from any strict interior point
  to the boundary is positive

### Reduction to contour integral (fully proved)

* `hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral` -- if a `PiecewiseC1Path` agrees
  with `fdBoundaryFun` and its contour integral of `(z - z₀)⁻¹` equals `-2πi`, then
  the interior winding number is `-1`.

### Clean constructor (fully proved)

* `FDWindingData.mk_of_interior_contourIntegral` -- build `FDWindingData` by supplying
  the interior contour integral identity as a hypothesis (together with the three
  `SingleCrossingData` for the elliptic points).

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ### Strict interior predicate -/

/-- A point `z` is in the strict interior of the fundamental domain at height `H`.
This means `‖z‖ > 1`, `|z.re| < 1/2`, `0 < z.im`, and `z.im < H`. -/
def FDStrictInterior (z : ℂ) (H : ℝ) : Prop :=
  1 < ‖z‖ ∧ |z.re| < 1/2 ∧ 0 < z.im ∧ z.im < H

theorem FDStrictInterior.norm_gt {z : ℂ} {H : ℝ} (h : FDStrictInterior z H) :
    1 < ‖z‖ := h.1

theorem FDStrictInterior.re_abs_lt {z : ℂ} {H : ℝ} (h : FDStrictInterior z H) :
    |z.re| < 1/2 := h.2.1

theorem FDStrictInterior.im_pos {z : ℂ} {H : ℝ} (h : FDStrictInterior z H) :
    0 < z.im := h.2.2.1

theorem FDStrictInterior.im_lt {z : ℂ} {H : ℝ} (h : FDStrictInterior z H) :
    z.im < H := h.2.2.2

/-! ### Segment 1 avoidance: right vertical (re = 1/2) -/

/-- The right vertical segment has `re = 1/2`, so it avoids any point with `|re| < 1/2`. -/
theorem fdBoundaryFun_avoids_seg1 {z : ℂ} (hz_re : |z.re| < 1/2)
    {H : ℝ} {t : ℝ} (ht : t ≤ 1/5) :
    fdBoundaryFun H t ≠ z := by
  intro heq
  have h1 := fdBoundaryFun_seg1_re H t ht
  rw [heq] at h1
  rw [h1] at hz_re
  norm_num at hz_re

/-! ### Segments 2 and 3 avoidance: arcs (norm = 1) -/

/-- The arc segments lie on the unit circle, so they avoid any point with `‖z‖ > 1`. -/
theorem fdBoundaryFun_avoids_arc {z : ℂ} (hz_norm : 1 < ‖z‖)
    {H : ℝ} {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t ≠ z := by
  intro heq
  have h1 := fdBoundaryFun_arc_norm H t ht1 ht2
  rw [heq] at h1
  linarith

/-! ### Segment 4 avoidance: left vertical (re = -1/2) -/

/-- The left vertical segment has `re = -1/2`, so it avoids any point with `|re| < 1/2`. -/
theorem fdBoundaryFun_avoids_seg4 {z : ℂ} (hz_re : |z.re| < 1/2)
    {H : ℝ} {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    fdBoundaryFun H t ≠ z := by
  intro heq
  have h1 := fdBoundaryFun_seg4_re H t ht3 ht4
  rw [heq] at h1
  rw [h1] at hz_re
  norm_num at hz_re

/-! ### Segment 5 avoidance: horizontal (im = H) -/

/-- The horizontal segment has `im = H`, so it avoids any point with `im < H`. -/
theorem fdBoundaryFun_avoids_seg5 {z : ℂ} (hz_im : z.im < H)
    {t : ℝ} (ht : 4/5 < t) :
    fdBoundaryFun H t ≠ z := by
  intro heq
  have h1 := fdBoundaryFun_seg5_im H t ht
  rw [heq] at h1
  linarith

/-! ### Full boundary avoidance -/

/-- The FD boundary avoids every point in the strict interior of the fundamental domain.
This follows by case-splitting on the segment and applying the segment-specific avoidance. -/
theorem fdBoundaryFun_avoids_interior {z : ℂ} {H : ℝ}
    (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : z.im < H) :
    ∀ t ∈ Icc (0 : ℝ) 1, fdBoundaryFun H t ≠ z := by
  intro t ⟨ht0, ht1⟩
  by_cases h1 : t ≤ 1/5
  · exact fdBoundaryFun_avoids_seg1 hz_re h1
  · push Not at h1
    by_cases h2 : t ≤ 3/5
    · exact fdBoundaryFun_avoids_arc hz_norm h1 h2
    · push Not at h2
      by_cases h3 : t ≤ 4/5
      · exact fdBoundaryFun_avoids_seg4 hz_re h2 h3
      · push Not at h3
        exact fdBoundaryFun_avoids_seg5 hz_im h3

/-! ### Minimum distance to boundary -/

/-- For a strict interior point, the minimum distance to the FD boundary on `[0, 1]`
is positive. This follows from avoidance + compactness. -/
theorem fdBoundaryFun_minDist_interior_pos {z : ℂ} {H : ℝ}
    (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : z.im < H) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖fdBoundaryFun H t - z‖ := by
  -- The image of [0,1] under fdBoundaryFun is compact
  have h_cont : Continuous (fdBoundaryFun H) := fdBoundaryFun_continuous H
  have h_compact : IsCompact (fdBoundaryFun H '' Icc 0 1) :=
    isCompact_Icc.image h_cont
  have h_closed := h_compact.isClosed
  have h_nonempty : (fdBoundaryFun H '' Icc (0 : ℝ) 1).Nonempty :=
    ⟨fdBoundaryFun H 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩
  -- z is not in the image (by avoidance)
  have h_nmem : z ∉ fdBoundaryFun H '' Icc (0 : ℝ) 1 := by
    intro ⟨t, ht, heq⟩
    exact fdBoundaryFun_avoids_interior hz_norm hz_re hz_im t ht heq
  -- So infDist is positive
  have h_pos : 0 < Metric.infDist z (fdBoundaryFun H '' Icc 0 1) := by
    rwa [← h_closed.notMem_iff_infDist_pos h_nonempty]
  -- infDist is a lower bound on distances
  refine ⟨Metric.infDist z (fdBoundaryFun H '' Icc 0 1), h_pos, fun t ht => ?_⟩
  rw [← dist_eq_norm]
  rw [dist_comm]
  exact Metric.infDist_le_dist_of_mem (mem_image_of_mem _ ht)

/-! ### Avoidance for PiecewiseC1Path agreeing with fdBoundaryFun -/

/-- If a `PiecewiseC1Path` agrees with `fdBoundaryFun` on `[0, 1]`, then it also
avoids every strict interior point. -/
theorem piecewiseC1Path_avoids_interior {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {z : ℂ} (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : z.im < H) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - z‖ := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := fdBoundaryFun_minDist_interior_pos hz_norm hz_re hz_im
  exact ⟨δ, hδ_pos, fun t ht => by
    show δ ≤ ‖γ.toPath.extend t - z‖
    rw [hγ t ht]; exact hδ_bound t ht⟩

/-! ### Interior winding number from contour integral -/

/-- **Reduction to contour integral**: if a `PiecewiseC1Path` agrees with `fdBoundaryFun`
on `[0, 1]`, and the contour integral of `(z - z₀)⁻¹` equals `-2πi`, then the
generalized winding number at `z₀` is `-1`.

This reduces the interior winding number (a CPV/PV limit) to an ordinary contour integral
identity, which is the hard computational content. -/
theorem hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {z : ℂ} (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2)
    (_hz_im_pos : 0 < z.im) (hz_im_lt : z.im < H)
    (h_integral : γ.contourIntegral (fun w => (w - z)⁻¹) =
      -(2 * ↑Real.pi * I)) :
    HasGeneralizedWindingNumber γ z (-1) := by
  -- The path avoids z with positive minimum distance
  have hδ := piecewiseC1Path_avoids_interior γ hγ hz_norm hz_re hz_im_lt
  -- So HasGeneralizedWindingNumber holds for the contour integral value
  have h_gWN := hasGeneralizedWindingNumber_of_avoids hδ
  -- The contour integral formula gives the winding number
  -- h_gWN : HasGeneralizedWindingNumber γ z ((2 * pi * I)⁻¹ * contourIntegral ...)
  -- We need to show (2 * pi * I)⁻¹ * (-(2 * pi * I)) = -1
  convert h_gWN using 1
  rw [h_integral]
  have hpi : (2 : ℂ) * ↑Real.pi * I ≠ 0 := by
    simp [mul_eq_zero, Complex.ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero]
  field_simp

/-! ### Interior winding from contour integral, all-quantified version -/

/-- **All-quantified interior winding**: if a `PiecewiseC1Path` agrees with `fdBoundaryFun`,
and for every strict interior point the contour integral of `(w - z)⁻¹` equals `-2πi`,
then the interior winding hypothesis of `FDWindingData` is satisfied. -/
theorem hasGeneralizedWindingNumber_fdBoundary_interior_of_contourIntegral {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (h_int : ∀ z : ℂ, 1 < ‖z‖ → |z.re| < 1/2 → 0 < z.im → z.im < H →
      γ.contourIntegral (fun w => (w - z)⁻¹) = -(2 * ↑Real.pi * I)) :
    ∀ z : ℂ, ‖z‖ > 1 → |z.re| < 1/2 → z.im > 0 → z.im < H →
      HasGeneralizedWindingNumber γ z (-1) := by
  intro z hz_norm hz_re hz_im_pos hz_im_lt
  exact hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral γ hγ
    hz_norm hz_re hz_im_pos hz_im_lt (h_int z hz_norm hz_re hz_im_pos hz_im_lt)

/-! ### FDWindingData constructor from contour integral hypothesis -/

/-- Build `FDWindingData` by providing the interior contour integral identity as a
hypothesis, together with `SingleCrossingData` for the three elliptic points.

This is the cleanest way to construct `FDWindingData` when the interior winding number
is established via a contour integral computation (rather than homotopy). The caller
provides:
1. A `PiecewiseC1Path` agreeing with `fdBoundaryFun` on `[0, 1]`
2. For each strict interior point `z`, a proof that `∮_γ (w - z)⁻¹ dw = -2πi`
3. `SingleCrossingData` at `i`, `ρ`, and `ρ+1` with the correct CPV limits -/
def FDWindingData.mk_of_interior_contourIntegral {H : ℝ}
    (boundary : PiecewiseC1Path (fdStart H) (fdStart H))
    (hbdy : ∀ t ∈ Icc (0 : ℝ) 1, boundary.toPath.extend t = fdBoundaryFun H t)
    (h_int : ∀ z : ℂ, 1 < ‖z‖ → |z.re| < 1/2 → 0 < z.im → z.im < H →
      boundary.contourIntegral (fun w => (w - z)⁻¹) = -(2 * ↑Real.pi * I))
    (D_i : SingleCrossingData boundary I)
    (hL_i : D_i.L = -(↑Real.pi * I))
    (D_rho : SingleCrossingData boundary ellipticPointRho)
    (hL_rho : D_rho.L = -(↑Real.pi / 3 * I))
    (D_rho1 : SingleCrossingData boundary ellipticPointRhoPlusOne)
    (hL_rho1 : D_rho1.L = -(↑Real.pi / 3 * I)) :
    FDWindingData H :=
  FDWindingData.mk_of_crossing boundary hbdy
    (hasGeneralizedWindingNumber_fdBoundary_interior_of_contourIntegral
      boundary hbdy h_int)
    D_i hL_i D_rho hL_rho D_rho1 hL_rho1

/-! ### Avoidance: alternative formulations -/

/-- The FD boundary function at any parameter in `[0, 1]` is different from any
strict interior point. This is the raw function-level avoidance. -/
theorem fdBoundaryFun_ne_of_strictInterior {z : ℂ} {H : ℝ}
    (hz : FDStrictInterior z H) :
    ∀ t ∈ Icc (0 : ℝ) 1, fdBoundaryFun H t ≠ z :=
  fdBoundaryFun_avoids_interior hz.norm_gt hz.re_abs_lt hz.im_lt

/-- The positive minimum distance from a strict interior point to the FD boundary. -/
theorem fdBoundaryFun_minDist_of_strictInterior {z : ℂ} {H : ℝ}
    (hz : FDStrictInterior z H) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖fdBoundaryFun H t - z‖ :=
  fdBoundaryFun_minDist_interior_pos hz.norm_gt hz.re_abs_lt hz.im_lt

/-! ### Segment-by-segment distance lower bounds -/

/-- On segment 1, the distance to `z` is at least `1/2 - |z.re|`, which is positive
for strict interior points. -/
theorem fdBoundaryFun_seg1_re_dist {z : ℂ} (_hz_re : |z.re| < 1/2)
    {H : ℝ} {t : ℝ} (ht : t ≤ 1/5) :
    1/2 - |z.re| ≤ ‖fdBoundaryFun H t - z‖ := by
  have h1 := fdBoundaryFun_seg1_re H t ht
  have hre : (fdBoundaryFun H t - z).re = 1/2 - z.re := by rw [sub_re, h1]
  have h2 : 1/2 - |z.re| ≤ |1/2 - z.re| := by
    have := abs_sub_abs_le_abs_sub (1/2 : ℝ) z.re
    simp only [show |(1 : ℝ)/2| = 1/2 from by norm_num] at this
    linarith
  calc 1/2 - |z.re| ≤ |1/2 - z.re| := h2
    _ = |(fdBoundaryFun H t - z).re| := by rw [hre]
    _ ≤ ‖fdBoundaryFun H t - z‖ := Complex.abs_re_le_norm _

/-- On segments 2-3, the distance to `z` is at least `‖z‖ - 1`, which is positive
for strict interior points. -/
theorem fdBoundaryFun_arc_dist {z : ℂ} (_hz_norm : 1 < ‖z‖)
    {H : ℝ} {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    ‖z‖ - 1 ≤ ‖fdBoundaryFun H t - z‖ := by
  have h1 := fdBoundaryFun_arc_norm H t ht1 ht2
  calc ‖z‖ - 1 = ‖z‖ - ‖fdBoundaryFun H t‖ := by rw [h1]
    _ ≤ ‖z - fdBoundaryFun H t‖ := norm_sub_norm_le z (fdBoundaryFun H t)
    _ = ‖fdBoundaryFun H t - z‖ := by rw [norm_sub_rev]

/-- On segment 4, the distance to `z` is at least `1/2 - |z.re|`, which is positive
for strict interior points. -/
theorem fdBoundaryFun_seg4_re_dist {z : ℂ} (_hz_re : |z.re| < 1/2)
    {H : ℝ} {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    1/2 - |z.re| ≤ ‖fdBoundaryFun H t - z‖ := by
  have h1 := fdBoundaryFun_seg4_re H t ht3 ht4
  have hre : (fdBoundaryFun H t - z).re = -1/2 - z.re := by rw [sub_re, h1]
  have h2 : 1/2 - |z.re| ≤ |-1/2 - z.re| := by
    have := abs_sub_abs_le_abs_sub (-1/2 : ℝ) z.re
    simp only [show |(-1 : ℝ)/2| = 1/2 from by norm_num] at this
    linarith
  calc 1/2 - |z.re| ≤ |-1/2 - z.re| := h2
    _ = |(fdBoundaryFun H t - z).re| := by rw [hre]
    _ ≤ ‖fdBoundaryFun H t - z‖ := Complex.abs_re_le_norm _

/-- On segment 5, the distance to `z` is at least `H - z.im`, which is positive
for strict interior points. -/
theorem fdBoundaryFun_seg5_im_dist {z : ℂ} (hz_im : z.im < H)
    {t : ℝ} (ht : 4/5 < t) :
    H - z.im ≤ ‖fdBoundaryFun H t - z‖ := by
  have h1 := fdBoundaryFun_seg5_im H t ht
  calc H - z.im = |(fdBoundaryFun H t - z).im| := by
        rw [sub_im, h1]; rw [abs_of_pos (by linarith)]
    _ ≤ ‖fdBoundaryFun H t - z‖ := Complex.abs_im_le_norm _

/-! ### Explicit minimum distance bound -/

/-- An explicit positive lower bound on the minimum distance from a strict interior
point to the FD boundary: `min(1/2 - |z.re|, ‖z‖ - 1, H - z.im)`. -/
theorem fdBoundaryFun_minDist_explicit {z : ℂ} {H : ℝ}
    (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : z.im < H) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      min (min (1/2 - |z.re|) (‖z‖ - 1)) (H - z.im) ≤
        ‖fdBoundaryFun H t - z‖ := by
  intro t ⟨ht0, ht1⟩
  by_cases h1 : t ≤ 1/5
  · calc min (min (1/2 - |z.re|) (‖z‖ - 1)) (H - z.im)
        ≤ 1/2 - |z.re| := le_trans (min_le_left _ _) (min_le_left _ _)
      _ ≤ ‖fdBoundaryFun H t - z‖ := fdBoundaryFun_seg1_re_dist hz_re h1
  · push Not at h1
    by_cases h2 : t ≤ 3/5
    · calc min (min (1/2 - |z.re|) (‖z‖ - 1)) (H - z.im)
          ≤ ‖z‖ - 1 := le_trans (min_le_left _ _) (min_le_right _ _)
        _ ≤ ‖fdBoundaryFun H t - z‖ := fdBoundaryFun_arc_dist hz_norm h1 h2
    · push Not at h2
      by_cases h3 : t ≤ 4/5
      · calc min (min (1/2 - |z.re|) (‖z‖ - 1)) (H - z.im)
            ≤ 1/2 - |z.re| := le_trans (min_le_left _ _) (min_le_left _ _)
          _ ≤ ‖fdBoundaryFun H t - z‖ := fdBoundaryFun_seg4_re_dist hz_re h2 h3
      · push Not at h3
        calc min (min (1/2 - |z.re|) (‖z‖ - 1)) (H - z.im)
            ≤ H - z.im := min_le_right _ _
          _ ≤ ‖fdBoundaryFun H t - z‖ := fdBoundaryFun_seg5_im_dist hz_im h3

/-- The explicit minimum distance is positive for strict interior points. -/
theorem fdBoundaryFun_minDist_explicit_pos {z : ℂ} {H : ℝ}
    (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : z.im < H) :
    0 < min (min (1/2 - |z.re|) (‖z‖ - 1)) (H - z.im) := by
  apply lt_min
  · apply lt_min
    · linarith
    · linarith
  · linarith

/-- The explicit minimum distance formulation as an existential, directly usable
by `hasGeneralizedWindingNumber_of_avoids`. -/
theorem fdBoundaryFun_avoids_with_explicit_bound {z : ℂ} {H : ℝ}
    (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : z.im < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - z‖ := by
  refine ⟨min (min (1/2 - |z.re|) (‖z‖ - 1)) (H - z.im),
    fdBoundaryFun_minDist_explicit_pos hz_norm hz_re hz_im, fun t ht => ?_⟩
  show _ ≤ ‖γ.toPath.extend t - z‖
  rw [hγ t ht]
  exact fdBoundaryFun_minDist_explicit hz_norm hz_re hz_im t ht

end
