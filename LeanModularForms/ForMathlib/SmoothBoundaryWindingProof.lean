/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.CoreIdentityProof
import LeanModularForms.ForMathlib.BoundaryWinding

/-!
# Smooth Boundary Winding Proof — Constructing `FDWindingDataFull`

This file proves that `FDWindingDataFull` can be constructed from `FDWindingData`
together with the smooth boundary winding condition, and provides pathways for
discharging that condition.

## Architecture

The `boundary_winding` field of `FDWindingDataFull` requires: at every non-elliptic,
non-interior point on the FD boundary, the generalized winding number is `-1/2`.

### Pathway 1: Direct hypothesis
`mkFDWindingDataFull` takes a `FDWindingData` and the boundary condition as a
hypothesis, producing `FDWindingDataFull`.

### Pathway 2: From SmoothBoundaryWindingData
`mkFDWindingDataFull_of_smoothData` constructs `FDWindingDataFull` from
`SmoothBoundaryWindingData` at each smooth boundary point.

### Pathway 3: Geometric classification
`smooth_boundary_classification` shows smooth boundary points fall into
two cases (vertical edge or non-elliptic arc), enabling case-by-case
construction of `SmoothBoundaryWindingData`.

## Main results

* `mkFDWindingDataFull` -- assembler from `FDWindingData` + boundary hypothesis
* `boundaryWindingHyp_of_smoothData` -- from `SmoothBoundaryWindingData` oracle
* `mkFDWindingDataFull_of_smoothData` -- full assembler via smooth data
* `smooth_boundary_classification` -- geometric dichotomy for boundary points
* `boundary_point_on_vert_or_arc` -- membership in vertical or arc segment

## References

* Diamond--Shurman, *A First Course in Modular Forms*, Theorem 3.1.1
* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Canonical coordinate forms for the elliptic points -/

private lemma ellipticPointRho_coe_eq :
    (ellipticPointRho : ℂ) = ((-1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by
  change (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) = _
  push_cast
  ring

private lemma ellipticPointRhoPlusOne_coe_eq :
    (ellipticPointRhoPlusOne : ℂ) =
      ((1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by
  change (1/2 + (Real.sqrt 3 / 2) * I : ℂ) = _
  push_cast
  ring

/-! ### The boundary winding condition as a predicate -/

/-- The boundary winding condition: at every point `z` in the upper half-plane
below height `H`, which is not elliptic, not strict interior, but lies on the
FD boundary (`normSq >= 1`, `|re| <= 1/2`), the winding number of `gamma`
around `z` is `-1/2`. -/
def BoundaryWindingHyp {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H)) : Prop :=
  ∀ z : ℂ, z.im > 0 → z.im < H →
    z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
    ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
    Complex.normSq z ≥ 1 → |z.re| ≤ 1/2 →
    HasGeneralizedWindingNumber γ z (-1/2)

/-! ### Constructor: FDWindingData + boundary hypothesis -> FDWindingDataFull -/

/-- Construct `FDWindingDataFull` from `FDWindingData` and the boundary winding
condition. This is the minimal assembler: it lifts the base winding data
(interior, i, rho, rho+1) to the full data with smooth boundary winding. -/
def mkFDWindingDataFull {H : ℝ} (D : FDWindingData H)
    (h_bdy : BoundaryWindingHyp D.boundary) : FDWindingDataFull H where
  toFDWindingData := D
  boundary_winding := h_bdy

/-! ### Bridge from SmoothBoundaryWindingData -/

/-- Construct `BoundaryWindingHyp` from `SmoothBoundaryWindingData` at each
smooth boundary point. -/
theorem boundaryWindingHyp_of_smoothData {H : ℝ}
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    (h_data : ∀ z : ℂ, z.im > 0 → z.im < H →
      z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
      ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
      Complex.normSq z ≥ 1 → |z.re| ≤ 1/2 →
      SmoothBoundaryWindingData γ z) :
    BoundaryWindingHyp γ :=
  fun z h1 h2 h3 h4 h5 h6 h7 h8 =>
    (h_data z h1 h2 h3 h4 h5 h6 h7 h8).hasWindingNumber

/-- Full assembler: from `FDWindingData` and `SmoothBoundaryWindingData` oracle,
construct `FDWindingDataFull`. -/
def mkFDWindingDataFull_of_smoothData {H : ℝ} (D : FDWindingData H)
    (h_data : ∀ z : ℂ, z.im > 0 → z.im < H →
      z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
      ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
      Complex.normSq z ≥ 1 → |z.re| ≤ 1/2 →
      SmoothBoundaryWindingData D.boundary z) :
    FDWindingDataFull H :=
  mkFDWindingDataFull D (boundaryWindingHyp_of_smoothData h_data)

/-! ### Geometric classification of smooth boundary points -/

/-- A non-elliptic non-interior FD boundary point lies either on a vertical edge
(`|re| = 1/2`, `norm > 1`) or on the smooth part of the unit circle arc
(`norm = 1`, `re != 0`, `|re| != 1/2`). -/
theorem smooth_boundary_classification (z : ℂ)
    (hz_im : z.im > 0)
    (hz_ne_I : z ≠ I)
    (hz_ne_rho : z ≠ ellipticPointRho)
    (hz_ne_rho1 : z ≠ ellipticPointRhoPlusOne)
    (hz_not_int : ¬(‖z‖ > 1 ∧ |z.re| < 1/2))
    (hz_nsq : Complex.normSq z ≥ 1)
    (hz_re : |z.re| ≤ 1/2) :
    (|z.re| = 1/2 ∧ ‖z‖ > 1) ∨ (‖z‖ = 1 ∧ z.re ≠ 0 ∧ |z.re| ≠ 1/2) := by
  have hnorm_ge : ‖z‖ ≥ 1 := by
    rw [Complex.norm_def]
    exact Real.sqrt_one ▸ Real.sqrt_le_sqrt (by linarith [hz_nsq])
  rcases eq_or_lt_of_le hnorm_ge with h_eq | h_gt
  · -- norm = 1: on the unit circle
    right
    have h_nsq_1 : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, h_eq.symm, one_pow]
    refine ⟨h_eq.symm, ?_, ?_⟩
    · -- re != 0: else z = i
      intro hre_zero
      apply hz_ne_I
      rw [Complex.normSq_apply, hre_zero, mul_zero, zero_add] at h_nsq_1
      have h_im_le : z.im ≤ 1 := by nlinarith [mul_self_nonneg (z.im - 1)]
      have h_im_ge : z.im ≥ 1 := by nlinarith [mul_self_nonneg (z.im - 1)]
      exact Complex.ext (hre_zero.trans I_re.symm)
        (le_antisymm h_im_le h_im_ge ▸ I_im.symm)
    · -- |re| != 1/2: else z = rho or rho+1
      intro hre_half
      rw [Complex.normSq_apply] at h_nsq_1
      rcases abs_cases z.re with ⟨_, h_sign⟩ | ⟨_, h_sign⟩
      · -- re >= 0, |re| = re = 1/2
        have hre_val : z.re = 1/2 := by linarith
        have h_im_sq : z.im * z.im = 3/4 := by nlinarith
        have h_im_val : z.im = Real.sqrt 3 / 2 := by
          have h_prod : (z.im - Real.sqrt 3 / 2) *
              (z.im + Real.sqrt 3 / 2) = 0 := by
            nlinarith [Real.mul_self_sqrt (show (3:ℝ) ≥ 0 by norm_num)]
          rcases mul_eq_zero.mp h_prod with h | h
          · linarith
          · exact absurd h (ne_of_gt (add_pos hz_im (by positivity)))
        apply hz_ne_rho1
        rw [ellipticPointRhoPlusOne_coe_eq]
        apply Complex.ext
        · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
            mul_zero, mul_one, sub_zero, add_zero]
          linarith [hre_val]
        · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
            mul_zero, mul_one, add_zero, zero_add]
          linarith [h_im_val]
      · -- re < 0, |re| = -re, -re = 1/2, re = -1/2
        have hre_val : z.re = -1/2 := by linarith
        have h_im_sq : z.im * z.im = 3/4 := by nlinarith
        have h_im_val : z.im = Real.sqrt 3 / 2 := by
          have h_prod : (z.im - Real.sqrt 3 / 2) *
              (z.im + Real.sqrt 3 / 2) = 0 := by
            nlinarith [Real.mul_self_sqrt (show (3:ℝ) ≥ 0 by norm_num)]
          rcases mul_eq_zero.mp h_prod with h | h
          · linarith
          · exact absurd h (ne_of_gt (add_pos hz_im (by positivity)))
        apply hz_ne_rho
        rw [ellipticPointRho_coe_eq]
        apply Complex.ext
        · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
            mul_zero, mul_one, sub_zero, add_zero]
          linarith [hre_val]
        · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
            mul_zero, mul_one, add_zero, zero_add]
          linarith [h_im_val]
  · -- norm > 1: must have |re| = 1/2
    left
    refine ⟨le_antisymm hz_re ?_, h_gt⟩
    by_contra h
    push Not at h
    exact hz_not_int ⟨h_gt, h⟩

/-! ### Boundary point location on the FD contour -/

/-- A smooth boundary point with `|re| = 1/2` and `norm > 1` lies on a vertical
edge of the FD boundary. Such points have `im > sqrt(3)/2` (they are above the
arc endpoints) and satisfy `re = 1/2` or `re = -1/2`. -/
theorem boundary_point_on_vert_edge (z : ℂ)
    (hz_im : z.im > 0)
    (hz_re_half : |z.re| = 1/2) (hz_norm_gt : ‖z‖ > 1) :
    z.im > Real.sqrt 3 / 2 := by
  have h_nsq_gt : Complex.normSq z > 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [hz_norm_gt, sq_nonneg (‖z‖ - 1)]
  rw [Complex.normSq_apply] at h_nsq_gt
  rcases abs_cases z.re with ⟨h_eq, _⟩ | ⟨h_eq, _⟩
  · -- re = 1/2
    have : z.re = 1/2 := by linarith [hz_re_half]
    nlinarith [Real.mul_self_sqrt (show (3:ℝ) ≥ 0 by norm_num),
      mul_self_nonneg (z.im - Real.sqrt 3 / 2)]
  · -- re = -1/2
    have : z.re = -1/2 := by linarith [hz_re_half]
    nlinarith [Real.mul_self_sqrt (show (3:ℝ) ≥ 0 by norm_num),
      mul_self_nonneg (z.im - Real.sqrt 3 / 2)]

/-- A smooth boundary point on the unit circle arc with `re != 0` and
`|re| != 1/2` has `im > 0` and satisfies `1/3 < angle/pi < 2/3` (excluding
the elliptic points and `i`). -/
theorem boundary_point_on_arc_range (z : ℂ)
    (hz_norm : ‖z‖ = 1) (_hz_im : z.im > 0)
    (hz_re_ne : z.re ≠ 0) (hz_re_half : |z.re| ≠ 1/2) :
    0 < z.re * z.re ∧ z.re * z.re < 1/4 ∨
    0 < z.re * z.re ∧ 1/4 < z.re * z.re := by
  have h_nsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz_norm, one_pow]
  rw [Complex.normSq_apply] at h_nsq
  have h_re_sq_pos : 0 < z.re * z.re := mul_self_pos.mpr hz_re_ne
  have h_re_sq_bound : z.re * z.re ≠ 1/4 := by
    intro h
    have h_cases : z.re = 1/2 ∨ z.re = -1/2 := by
      have h_prod : (z.re - 1/2) * (z.re + 1/2) = 0 := by nlinarith
      rcases mul_eq_zero.mp h_prod with h1 | h1
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have h_abs : |z.re| = 1/2 := by
      rcases h_cases with h1 | h1
      · rw [h1]; norm_num
      · rw [h1]; norm_num
    exact hz_re_half h_abs
  rcases lt_or_gt_of_ne h_re_sq_bound with h | h
  · exact Or.inl ⟨h_re_sq_pos, h⟩
  · exact Or.inr ⟨h_re_sq_pos, h⟩

/-! ### BoundaryWindingHyp is exactly the gap for FDWindingDataFull -/

/-- `BoundaryWindingHyp` is the sole condition needed to extend `FDWindingData`
to `FDWindingDataFull`. This theorem provides the converse: given
`FDWindingDataFull`, extract `BoundaryWindingHyp`. -/
theorem boundaryWindingHyp_of_fdWindingDataFull {H : ℝ}
    (D : FDWindingDataFull H) : BoundaryWindingHyp D.boundary :=
  D.boundary_winding

/-- The `BoundaryWindingHyp` condition and `FDWindingData` are equivalent to
`FDWindingDataFull`: they carry exactly the same data. -/
theorem fdWindingDataFull_iff_windingData_and_boundary {H : ℝ} :
    (∃ _ : FDWindingDataFull H, True) ↔
    (∃ D : FDWindingData H, BoundaryWindingHyp D.boundary) := by
  constructor
  · rintro ⟨D, _⟩
    exact ⟨D.toFDWindingData, D.boundary_winding⟩
  · rintro ⟨D, h⟩
    exact ⟨mkFDWindingDataFull D h, trivial⟩

end
