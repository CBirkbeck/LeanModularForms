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

/-- On segment 1 (right vertical, re = 1/2), `γ(t) - z` is in the slit plane
when `z.re < 1/2`, because the real part is `1/2 - z.re > 0`. -/
theorem fdBoundary_seg1_in_slitPlane {z : ℂ} {H : ℝ}
    (hz_re : z.re < 1/2) (t : ℝ) (ht : t ≤ 1/5) :
    fdBoundaryFun H t - z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr <| Or.inl <| by
    rw [sub_re, fdBoundaryFun_seg1_re H t ht]
    linarith

/-- On segment 5 (horizontal, im = H), `γ(t) - z` has positive imaginary part
when `z.im < H`, because `(γ(t) - z).im = H - z.im > 0`. -/
theorem fdBoundary_seg5_in_slitPlane {z : ℂ} {H : ℝ}
    (hz_im : z.im < H) (t : ℝ) (ht : 4/5 < t) :
    fdBoundaryFun H t - z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr <| Or.inr <| by
    rw [sub_im, fdBoundaryFun_seg5_im H t ht]
    linarith

/-- On segment 4 (left vertical, re = -1/2), `γ(t) - z` is in the slit plane
when `(γ(t) - z).im ≠ 0`. -/
theorem fdBoundary_seg4_in_slitPlane_of_im_ne {z : ℂ} {H : ℝ} (t : ℝ)
    (him_ne : (fdBoundaryFun H t - z).im ≠ 0) :
    fdBoundaryFun H t - z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inr him_ne)

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

/-- The contour integral of `(w - z)⁻¹` along the FD boundary equals `-2πi`,
given the FTC computation on each of the five segments and the total branch correction.

Each `h_seg*` hypothesis gives the segment integral as a log difference. The `h_total`
hypothesis gives the algebraic sum of these log differences as `-(2 * π * I)`. -/
theorem fdBoundary_contourIntegral_inv_sub_eq_of_ftc {z : ℂ} {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hint : IntervalIntegrable
      (fun t => (γ t - z)⁻¹ * deriv γ.toPath.extend t) volume 0 1)
    (h_seg1 : ∫ t in (0 : ℝ)..1/5, (γ t - z)⁻¹ * deriv γ.toPath.extend t =
      Complex.log (γ (1/5 : ℝ) - z) - Complex.log (γ 0 - z))
    (h_seg2 : ∫ t in (1/5 : ℝ)..2/5, (γ t - z)⁻¹ * deriv γ.toPath.extend t =
      Complex.log (γ (2/5 : ℝ) - z) - Complex.log (γ (1/5 : ℝ) - z))
    (h_seg3 : ∫ t in (2/5 : ℝ)..3/5, (γ t - z)⁻¹ * deriv γ.toPath.extend t =
      Complex.log (γ (3/5 : ℝ) - z) - Complex.log (γ (2/5 : ℝ) - z))
    (h_seg4 : ∫ t in (3/5 : ℝ)..4/5, (γ t - z)⁻¹ * deriv γ.toPath.extend t =
      Complex.log (γ (4/5 : ℝ) - z) - Complex.log (γ (3/5 : ℝ) - z))
    (h_seg5 : ∫ t in (4/5 : ℝ)..1, (γ t - z)⁻¹ * deriv γ.toPath.extend t =
      Complex.log (γ 1 - z) - Complex.log (γ (4/5 : ℝ) - z))
    (h_total : Complex.log (γ (1/5 : ℝ) - z) - Complex.log (γ 0 - z) +
      (Complex.log (γ (2/5 : ℝ) - z) - Complex.log (γ (1/5 : ℝ) - z)) +
      (Complex.log (γ (3/5 : ℝ) - z) - Complex.log (γ (2/5 : ℝ) - z)) +
      (Complex.log (γ (4/5 : ℝ) - z) - Complex.log (γ (3/5 : ℝ) - z)) +
      (Complex.log (γ 1 - z) - Complex.log (γ (4/5 : ℝ) - z)) =
      -(2 * ↑Real.pi * I)) :
    γ.contourIntegral (fun w => (w - z)⁻¹) = -(2 * ↑Real.pi * I) := by
  rw [fdBoundary_contourIntegral_split γ hint,
      h_seg1, h_seg2, h_seg3, h_seg4, h_seg5, h_total]

/-- The five log differences telescope to `log(f) - log(a)`. -/
theorem log_telescope_five {a b c d e f : ℂ} :
    (b - a) + (c - b) + (d - c) + (e - d) + (f - e) = f - a := by ring

/-- For a closed path agreeing with `fdBoundaryFun`, `γ(1) - z = γ(0) - z`. -/
theorem closed_path_sub_eq {z : ℂ} {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t) :
    γ 1 - z = γ 0 - z := by
  have h0 : (γ : ℝ → ℂ) 0 = fdBoundaryFun H 0 := hγ 0 ⟨le_refl _, zero_le_one⟩
  have h1 : (γ : ℝ → ℂ) 1 = fdBoundaryFun H 1 := hγ 1 ⟨zero_le_one, le_refl _⟩
  rw [h0, h1, fdBoundaryFun_closed]

/-- For a closed path, `log(γ(1) - z) - log(γ(0) - z) = 0`. -/
theorem closed_path_log_telescope_eq_zero {z : ℂ} {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t) :
    Complex.log (γ 1 - z) - Complex.log (γ 0 - z) = 0 := by
  rw [closed_path_sub_eq γ hγ, sub_self]

/-- The five log differences for a closed path telescope to zero (using the standard
branch everywhere). This means the `-2πi` correction must come from using a different
branch on at least one segment. -/
theorem closed_path_log_telescope_five {z : ℂ} {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t) :
    (Complex.log (γ (1/5 : ℝ) - z) - Complex.log (γ 0 - z)) +
    (Complex.log (γ (2/5 : ℝ) - z) - Complex.log (γ (1/5 : ℝ) - z)) +
    (Complex.log (γ (3/5 : ℝ) - z) - Complex.log (γ (2/5 : ℝ) - z)) +
    (Complex.log (γ (4/5 : ℝ) - z) - Complex.log (γ (3/5 : ℝ) - z)) +
    (Complex.log (γ 1 - z) - Complex.log (γ (4/5 : ℝ) - z)) =
    0 := by
  rw [log_telescope_five, closed_path_log_telescope_eq_zero γ hγ]

/-- **Interior winding number = -1** for the FD boundary, given the contour integral
identity as a hypothesis. -/
theorem fdBoundary_interior_winding_neg_one {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    {z : ℂ} (hz : FDStrictInterior z H)
    (h_integral : (fdBoundaryPC1Path H hH).contourIntegral (fun w => (w - z)⁻¹) =
      -(2 * ↑Real.pi * I)) :
    HasGeneralizedWindingNumber (fdBoundaryPC1Path H hH) z (-1) :=
  hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral (fdBoundaryPC1Path H hH)
    (fdBoundaryPC1Path_eq H hH) hz.norm_gt hz.re_abs_lt hz.im_pos hz.im_lt h_integral

/-- If the contour integral is an integer multiple of `2πi` and the integer is `-1`,
then the integral equals `-(2πi)`. -/
theorem contourIntegral_inv_sub_of_winding_neg_one
    {x : ℂ} (γ : PiecewiseC1Path x x) {z : ℂ}
    (h_val : ∃ n : ℤ, γ.contourIntegral (fun w => (w - z)⁻¹) =
      n * (2 * ↑Real.pi * I))
    (hn : ∀ n : ℤ, γ.contourIntegral (fun w => (w - z)⁻¹) =
      n * (2 * ↑Real.pi * I) → n = -1) :
    γ.contourIntegral (fun w => (w - z)⁻¹) = -(2 * ↑Real.pi * I) := by
  obtain ⟨n, hn_eq⟩ := h_val
  rw [hn_eq, hn n hn_eq]
  simp

/-- FTC on segment 1: the integral of `(γ(t) - z)⁻¹ γ'(t)` over `[0, 1/5]` equals
the log difference, because `γ(t) - z` has positive real part on this segment. -/
theorem fdBoundary_seg1_ftc {z : ℂ} {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (h_int : IntervalIntegrable
      (fun t => (γ t - z)⁻¹ * deriv γ.toPath.extend t) volume 0 (1/5))
    (hFγ_cont : ContinuousOn
      (fun t => Complex.log (γ.toPath.extend t - z)) (Icc 0 (1/5)))
    (hFγ_deriv : ∀ t ∈ Ioo (0 : ℝ) (1/5),
      HasDerivAt (fun s => Complex.log (γ.toPath.extend s - z))
        ((γ t - z)⁻¹ * deriv γ.toPath.extend t) t) :
    ∫ t in (0 : ℝ)..1/5, (γ t - z)⁻¹ * deriv γ.toPath.extend t =
      Complex.log (γ (1/5 : ℝ) - z) - Complex.log (γ 0 - z) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 1/5)
    hFγ_cont hFγ_deriv h_int

/-- FTC on segment 5: the integral of `(γ(t) - z)⁻¹ γ'(t)` over `[4/5, 1]` equals
the log difference, because `γ(t) - z` has positive imaginary part on this segment. -/
theorem fdBoundary_seg5_ftc {z : ℂ} {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (h_int : IntervalIntegrable
      (fun t => (γ t - z)⁻¹ * deriv γ.toPath.extend t) volume (4/5) 1)
    (hFγ_cont : ContinuousOn
      (fun t => Complex.log (γ.toPath.extend t - z)) (Icc (4/5) 1))
    (hFγ_deriv : ∀ t ∈ Ioo (4/5 : ℝ) 1,
      HasDerivAt (fun s => Complex.log (γ.toPath.extend s - z))
        ((γ t - z)⁻¹ * deriv γ.toPath.extend t) t) :
    ∫ t in (4/5 : ℝ)..1, (γ t - z)⁻¹ * deriv γ.toPath.extend t =
      Complex.log (γ 1 - z) - Complex.log (γ (4/5 : ℝ) - z) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (4 : ℝ)/5 ≤ 1)
    hFγ_cont hFγ_deriv h_int

/-- Construct `FDWindingData` from the interior contour integral identity.

Given that `∮_γ (w - z)⁻¹ dw = -2πi` for every strict interior point `z`, together
with the crossing data at the three elliptic points, we obtain `FDWindingData`. -/
def fdWindingData_of_interior_integral {H : ℝ} (hH : H > Real.sqrt 3 / 2)
    (h_int : ∀ z : ℂ, 1 < ‖z‖ → |z.re| < 1/2 → 0 < z.im → z.im < H →
      (fdBoundaryPC1Path H hH).contourIntegral (fun w => (w - z)⁻¹) =
        -(2 * ↑Real.pi * I))
    (D_i : SingleCrossingData (fdBoundaryPC1Path H hH) I)
    (hL_i : D_i.L = -(↑Real.pi * I))
    (D_rho : SingleCrossingData (fdBoundaryPC1Path H hH) ellipticPointRho)
    (hL_rho : D_rho.L = -(↑Real.pi / 3 * I))
    (D_rho1 : SingleCrossingData (fdBoundaryPC1Path H hH) ellipticPointRhoPlusOne)
    (hL_rho1 : D_rho1.L = -(↑Real.pi / 3 * I)) :
    FDWindingData H :=
  FDWindingData.mk_of_interior_contourIntegral (fdBoundaryPC1Path H hH)
    (fdBoundaryPC1Path_eq H hH) h_int D_i hL_i D_rho hL_rho D_rho1 hL_rho1

/-- FTC for `(w - z)⁻¹` on a sub-interval `[a, b]` of a piecewise C¹ path, when
`γ(t) - z` stays in the slit plane and the open interval `(a, b)` contains no
partition points. -/
theorem ftc_inv_sub_on_slitPlane {x : ℂ} {z : ℂ}
    (γ : PiecewiseC1Path x x) {a b : ℝ} (hab : a ≤ b)
    (hsub : Icc a b ⊆ Icc (0 : ℝ) 1)
    (hγ_slit : ∀ t ∈ Icc a b, γ t - z ∈ Complex.slitPlane)
    (h_no_part : ∀ p ∈ γ.partition, p ∉ Ioo a b)
    (h_int : IntervalIntegrable
      (fun t => (γ t - z)⁻¹ * deriv γ.toPath.extend t) volume a b) :
    ∫ t in a..b, (γ t - z)⁻¹ * deriv γ.toPath.extend t =
      Complex.log (γ b - z) - Complex.log (γ a - z) := by
  have hFγ_cont : ContinuousOn
      (fun t => Complex.log (γ.toPath.extend t - z)) (Icc a b) :=
    ContinuousOn.clog
      ((γ.toPath.continuous_extend.continuousOn.mono hsub).sub continuousOn_const) hγ_slit
  have hFγ_deriv : ∀ t ∈ Ioo a b,
      HasDerivAt (fun s => Complex.log (γ.toPath.extend s - z))
        ((γ t - z)⁻¹ * deriv γ.toPath.extend t) t := by
    intro t ht
    have ht_01 : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_lt (hsub (left_mem_Icc.mpr hab)).1 ht.1,
       lt_of_lt_of_le ht.2 (hsub (right_mem_Icc.mpr hab)).2⟩
    rw [inv_mul_eq_div]
    exact ((γ.differentiable_off t ht_01 (fun hp => h_no_part t hp ht)).hasDerivAt.sub_const
      z).clog_real (hγ_slit t (Ioo_subset_Icc_self ht))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hFγ_cont hFγ_deriv h_int

end
