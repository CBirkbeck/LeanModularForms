/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.CauchyPrimitive
import LeanModularForms.ForMathlib.Instances
import LeanModularForms.SpherePacking.PhiHolomorphic
import LeanModularForms.SpherePacking.CuspDecay

/-!
# Viazovska's Magic Function — Original Contour Integrals

This file defines the magic function `a(r)` from Viazovska's proof of the
optimality of the E₈ sphere packing [Via2017] and proves the key contour
equivalence `I₁₂ = I₁₂_vert + I₁₂_horiz` (rectangular decomposition of the
diagonal contour from `-1` to `i`).

## What we prove

The function `a_rad(r)` is defined using the **original triangular contours**
from Viazovska's paper:
```
a_rad(r) = ∫_{-1→i} φ₀(-1/(z+1)) · (z+1)² · e^{πirz} dz
         + ∫_{1→i}  φ₀(-1/(z-1)) · (z-1)² · e^{πirz} dz
         - 2 ∫_{0→i} φ₀(-1/z) · z² · e^{πirz} dz
         + 2 ∫_{i→i∞} φ₀(z) · e^{πirz} dz
```
where `φ₀(z) = (E₂E₄ - E₆)² / Δ(z)`.

The main result `I12_eq_rectangular` proves that the diagonal contour integral
`∫_{-1→i}` equals the sum of a vertical integral `∫_{-1→-1+i}` and a
horizontal integral `∫_{-1+i→i}`. This is the first step toward evaluating
`a_rad(r)` via the Fourier expansion of φ₀.

## How this differs from Sphere-Packing-Lean (Gauss2 PR)

The Sphere-Packing-Lean formalization
deforms the original triangular contours into **rectangular** contours from the
start, avoiding the cusp singularity at `z = -1, 0, 1` entirely. The contour
integrals are then evaluated on rectangles where all four sides lie strictly
inside the upper half-plane.

Our approach keeps Viazovska's original contours and handles the cusp
singularities directly:

1. **Holomorphicity of φ₀**: We prove `E₂` is holomorphic on ℍ via
   `E₂ = (πI/12)⁻¹ · logDeriv(η)` (Dedekind eta), then build up to `φ₀''`
   holomorphic on ℍ (`PhiHolomorphic.lean`). The Gauss2 PR instead uses the
   Serre derivative and Ramanujan's identity `E₂E₄ - E₆ = 3D(E₄)`.

2. **Cusp decay**: We prove `φ₀` is bounded at `Im → ∞` via the q-expansion
   bound `|E₂E₄-E₆| ≤ K|q|` (`CuspDecay.lean`), using `|E₂-1| ≤ 192|q|`
   from a comparison test on the Eisenstein series.

3. **Contour equivalence**: We prove `I₁₂ = I₁₂_vert + I₁₂_horiz` using
   path independence from `holomorphic_convex_primitive` on the convex upper
   half-plane. The proof takes a primitive `G` of the integrand, applies FTC
   to truncated integrals (starting at height `δ > 0`), then takes `δ → 0`
   using the cusp cancellation `(z+1)² → 0` at `z = -1`.

4. **Infrastructure**: The key tool is `holomorphic_convex_primitive` from
   `GeneralizedResidueTheory/CauchyPrimitive.lean`, which gives path independence
   for holomorphic functions on convex open sets. This is part of our broader
   generalized residue theorem framework (Hungerbühler-Wasem, Theorem 3.3),
   though this file only uses the convex primitive — the full generalized
   residue theorem and `ContourCycle` framework will be applied when computing
   `a_rad(r)` via the S-transformation of φ₀.

## Main results

* `φ₀''_differentiableOn` : φ₀ is holomorphic on ℍ
* `continuousOn_diagonal_integrand` : the parameterized diagonal integrand is
  continuous on `[0,1]` (including the cusp endpoint `t = 0`)
* `continuousOn_vertical_integrand` : same for the vertical parameterization
* `I12_eq_rectangular` : `I₁₂(r) = I₁₂_vert(r) + I₁₂_horiz(r)`

## References

* Viazovska, M. S. (2017). "The sphere packing problem in dimension 8."
  Annals of Mathematics, 185(3), 991-1015.
* Hungerbühler, N., Wasem, M. (2019). "A generalized version of the
  residue theorem." arXiv:1808.00997v2.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Interval

noncomputable section

/-- The integrand for I₁+I₂: φ₀(-1/(z+1)) · (z+1)² · e^{πirz}.
At z = -1 (the cusp), (z+1)² = 0 cancels the singularity of φ₀. -/
def viazovska_integrand_left (r : ℝ) (z : ℂ) : ℂ :=
  φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * Complex.exp (↑Real.pi * I * ↑r * z)

/-- The integrand for I₃+I₄: φ₀(-1/(z-1)) · (z-1)² · e^{πirz}.
At z = 1 (the cusp), (z-1)² = 0 cancels the singularity. -/
def viazovska_integrand_right (r : ℝ) (z : ℂ) : ℂ :=
  φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * Complex.exp (↑Real.pi * I * ↑r * z)

/-- The integrand for I₅: φ₀(-1/z) · z² · e^{πirz}.
At z = 0 (the cusp), z² = 0 cancels the singularity. -/
def viazovska_integrand_center (r : ℝ) (z : ℂ) : ℂ :=
  φ₀'' (-1 / z) * z ^ 2 * Complex.exp (↑Real.pi * I * ↑r * z)

/-- The integrand for I₆: φ₀(z) · e^{πirz}.
No singularity issues (Im(z) ≥ 1 on the contour). -/
def viazovska_integrand_tail (r : ℝ) (z : ℂ) : ℂ :=
  φ₀'' z * Complex.exp (↑Real.pi * I * ↑r * z)

/-- The straight-line contour from -1 to i (original Viazovska path). -/
def contour_neg1_to_i (t : ℝ) : ℂ := -1 + (1 + I) * ↑t

/-- The straight-line contour from 1 to i (original Viazovska path). -/
def contour_1_to_i (t : ℝ) : ℂ := 1 + (-1 + I) * ↑t

/-- The straight-line contour from 0 to i (vertical segment). -/
def contour_0_to_i (t : ℝ) : ℂ := I * ↑t

/-- I₁₂(r) = ∫_{-1}^{i} φ₀(-1/(z+1)) · (z+1)² · e^{πirz} dz -/
def I12 (r : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..1, viazovska_integrand_left r (contour_neg1_to_i t) *
    deriv contour_neg1_to_i t

/-- I₃₄(r) = ∫_{1}^{i} φ₀(-1/(z-1)) · (z-1)² · e^{πirz} dz -/
def I34 (r : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..1, viazovska_integrand_right r (contour_1_to_i t) *
    deriv contour_1_to_i t

/-- I₅(r) = -2 ∫_{0}^{i} φ₀(-1/z) · z² · e^{πirz} dz -/
def I5 (r : ℝ) : ℂ :=
  -2 * ∫ t in (0:ℝ)..1, viazovska_integrand_center r (contour_0_to_i t) *
    deriv contour_0_to_i t

/-- I₆(r) = 2 ∫_{i}^{i∞} φ₀(z) · e^{πirz} dz
(the semi-infinite vertical integral). -/
def I6 (r : ℝ) : ℂ :=
  2 * ∫ t in Set.Ici (1:ℝ), viazovska_integrand_tail r (I * ↑t)  * I

/-- The radial magic function a_rad(r) from Viazovska [Via2017]. -/
def a_rad (r : ℝ) : ℂ := I12 r + I34 r + I5 r + I6 r

/-- φ₀'' is holomorphic on the upper half-plane. -/
theorem φ₀''_differentiableOn : DifferentiableOn ℂ φ₀'' {z : ℂ | 0 < z.im} := by
  have hE₄ := UpperHalfPlane.mdifferentiable_iff.mp E₄.holo'
  have hE₆ := UpperHalfPlane.mdifferentiable_iff.mp E₆.holo'
  have hΔ := UpperHalfPlane.mdifferentiable_iff.mp Delta.holo'
  intro z hz
  have hz' : 0 < z.im := hz
  have hopen := (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz'
  have hE₂z := (E₂_differentiableOn z hz).differentiableAt hopen
  have hE₄z := (hE₄ z hz).differentiableAt hopen
  have hE₆z := (hE₆ z hz).differentiableAt hopen
  have hΔz := (hΔ z hz).differentiableAt hopen
  have hΔ_ne : (⇑Delta ∘ UpperHalfPlane.ofComplex) z ≠ 0 := by
    simp only [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    exact Delta_ne_zero ⟨z, hz'⟩
  apply (((hE₂z.mul hE₄z).sub hE₆z).pow 2 |>.div hΔz hΔ_ne).differentiableWithinAt.congr_of_eventuallyEq
  rw [nhdsWithin_eq_nhds.mpr (Filter.mem_of_superset hopen (fun _ h => h))]
  filter_upwards [hopen] with w hw
  simp only [φ₀'', hw, dif_pos, φ₀, Function.comp,
    UpperHalfPlane.ofComplex_apply_of_im_pos hw, Pi.mul_apply, Pi.sub_apply,
    Pi.pow_apply, Pi.div_apply]; rfl
  · simp only [φ₀'', hz', dif_pos, φ₀, Function.comp,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz', Pi.mul_apply, Pi.sub_apply,
      Pi.pow_apply, Pi.div_apply]; rfl

/-- The upper half-plane `{z : ℂ | 0 < z.im}` is convex. -/
theorem convex_upperHalfPlaneSet : Convex ℝ {z : ℂ | 0 < z.im} := convex_halfSpace_im_gt 0

/-- When `Im(z) > 0`, the point `-1/(z+1)` also has positive imaginary part. -/
theorem neg_inv_add_one_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (-1 / (z + 1)).im := by
  have hne : z + 1 ≠ 0 := fun h => by
    have := (Complex.ext_iff.mp h).2; simp at this; linarith
  rw [neg_div, Complex.neg_im, Complex.div_im, Complex.one_im, Complex.one_re,
    zero_mul, zero_div, one_mul, zero_sub, neg_neg]
  exact div_pos (by simp [Complex.add_im]; linarith) (Complex.normSq_pos.mpr hne)

/-- The integrand `viazovska_integrand_left r` is holomorphic on the upper half-plane. -/
theorem viazovska_integrand_left_differentiableOn (r : ℝ) :
    DifferentiableOn ℂ (viazovska_integrand_left r) {z : ℂ | 0 < z.im} := fun z hz => by
  unfold viazovska_integrand_left
  have hz' : 0 < z.im := hz
  have hne : z + 1 ≠ 0 := fun h => by
    have := (Complex.ext_iff.mp h).2; simp at this; linarith
  have him := neg_inv_add_one_im_pos hz'
  have hφ : DifferentiableAt ℂ φ₀'' (-1 / (z + 1)) :=
    (φ₀''_differentiableOn _ him).differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds him)
  have hinv : DifferentiableAt ℂ (fun w => -1 / (w + 1)) z :=
    (differentiableAt_const _).div
      (differentiableAt_id.add (differentiableAt_const _)) hne
  exact ((hφ.comp z hinv).mul
    ((differentiableAt_id.add (differentiableAt_const _)).pow 2) |>.mul
    (Complex.differentiable_exp.differentiableAt.comp z
      ((differentiableAt_const _).mul differentiableAt_id))).differentiableWithinAt

/-- FTC for segment integrals: if `G' = f` on a convex set,
then the segment integral of `f` from `a` to `b` equals `G(b) - G(a)`. -/
theorem segment_integral_eq_sub_of_hasDerivAt {f G : ℂ → ℂ} {S : Set ℂ}
    (hS_convex : Convex ℝ S) {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S)
    (hG : ∀ z ∈ S, HasDerivAt G (f z) z) (hf_cont : ContinuousOn f S) :
    ∫ t in (0:ℝ)..1, f (a + t • (b - a)) * (b - a) = G b - G a := by
  have h_mem : ∀ t ∈ Icc (0 : ℝ) 1, a + ↑t • (b - a) ∈ S := fun t ht => by
    have : a + ↑t • (b - a) = (1 - t) • a + t • b := by
      simp only [Complex.real_smul]; push_cast; ring
    rw [this]
    exact hS_convex ha hb (by linarith [ht.2]) ht.1 (by ring)
  have hcont : ContinuousOn (fun t : ℝ => f (a + t • (b - a))) (Icc 0 1) :=
    hf_cont.comp (continuous_const.add
      (continuous_ofReal.smul continuous_const)).continuousOn h_mem
  have key := @intervalIntegral.integral_unitInterval_deriv_eq_sub ℂ ℂ _ _ _ _ _
    IsScalarTower.right G f a (b - a) hcont (fun t ht => hG _ (h_mem t ht))
  rw [show a + (b - a) = b by ring] at key
  rw [smul_eq_mul] at key
  erw [intervalIntegral.integral_mul_const]; rw [mul_comm]
  exact key

/-- Contour additivity: for a holomorphic function on a convex open set,
the segment integral from `a` to `b` equals the sum of segment integrals
from `a` to `c` and from `c` to `b`. -/
theorem segment_integral_add_of_holomorphic {f : ℂ → ℂ} {S : Set ℂ}
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S)
    (hf : DifferentiableOn ℂ f S)
    {a b c : ℂ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    ∫ t in (0:ℝ)..1, f (a + t • (b - a)) * (b - a) =
    (∫ t in (0:ℝ)..1, f (a + t • (c - a)) * (c - a)) +
    (∫ t in (0:ℝ)..1, f (c + t • (b - c)) * (b - c)) := by
  obtain ⟨G, hG⟩ := holomorphic_convex_primitive hS_convex hS_open ⟨a, ha⟩ hf
  rw [segment_integral_eq_sub_of_hasDerivAt hS_convex ha hb hG hf.continuousOn,
      segment_integral_eq_sub_of_hasDerivAt hS_convex ha hc hG hf.continuousOn,
      segment_integral_eq_sub_of_hasDerivAt hS_convex hc hb hG hf.continuousOn]
  ring

/-- The derivative of `contour_neg1_to_i` as a `HasDerivAt` statement. -/
theorem hasDerivAt_contour_neg1_to_i (t : ℝ) :
    HasDerivAt contour_neg1_to_i (1 + I : ℂ) t := by
  change HasDerivAt (fun s : ℝ => (-1 : ℂ) + (1 + I) * ↑s) _ _
  have h1 := (ofRealCLM.hasDerivAt (x := t)).const_mul (1 + I : ℂ)
  simp [ofRealCLM] at h1
  convert (hasDerivAt_const t (-1 : ℂ)).add h1 using 1; ring

/-- The derivative of `contour_neg1_to_i` is the constant `1 + I`. -/
theorem deriv_contour_neg1_to_i (t : ℝ) : deriv contour_neg1_to_i t = 1 + I :=
  (hasDerivAt_contour_neg1_to_i t).deriv

/-- `I12` expressed as a segment integral from `-1` to `I`. -/
theorem I12_eq_segment_integral (r : ℝ) :
    I12 r = ∫ t in (0:ℝ)..1,
      viazovska_integrand_left r ((-1 : ℂ) + t • ((I : ℂ) - (-1))) *
        ((I : ℂ) - (-1)) := by
  unfold I12; congr 1; ext t
  rw [deriv_contour_neg1_to_i]
  have h1 : contour_neg1_to_i t = (-1 : ℂ) + ↑t • ((I : ℂ) - (-1)) := by
    simp [contour_neg1_to_i, Complex.real_smul, sub_neg_eq_add]; ring
  rw [h1, show (1 : ℂ) + I = (I : ℂ) - (-1) by ring]

/-- The vertical integral from `-1` to `-1+I`: left side of the rectangular path. -/
def I12_vert (r : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..1, viazovska_integrand_left r (-1 + I * ↑t) * I

/-- The horizontal integral from `-1+I` to `I`: top side of the rectangular path. -/
def I12_horiz (r : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..1, viazovska_integrand_left r (-1 + I + ↑t)

/-- `I12_vert` expressed as a segment integral from `-1` to `-1+I`. -/
theorem I12_vert_eq_segment (r : ℝ) :
    I12_vert r = ∫ t in (0:ℝ)..1,
      viazovska_integrand_left r ((-1 : ℂ) + t • ((-1 + I) - (-1 : ℂ))) *
        ((-1 + I) - (-1 : ℂ)) := by
  simp only [I12_vert]; congr 1; ext t
  congr 1
  · congr 1; simp [Complex.real_smul]; ring
  · ring

/-- `I12_horiz` expressed as a segment integral from `-1+I` to `I`. -/
theorem I12_horiz_eq_segment (r : ℝ) :
    I12_horiz r = ∫ t in (0:ℝ)..1,
      viazovska_integrand_left r ((-1 + I : ℂ) + t • ((I : ℂ) - (-1 + I))) *
        ((I : ℂ) - (-1 + I)) := by
  simp only [I12_horiz]; congr 1; ext t
  have h1 : (I : ℂ) - (-1 + I) = 1 := by ring
  rw [h1, mul_one]
  congr 1; simp [Complex.real_smul]

/-- The point `-1 + δI` lies in the upper half-plane for `δ > 0`. -/
theorem neg_one_add_delta_I_mem_uhp {δ : ℝ} (hδ : 0 < δ) :
    (-1 + ↑δ * I : ℂ) ∈ {z : ℂ | 0 < z.im} := by
  change 0 < (-1 + ↑δ * I : ℂ).im; simp; linarith

/-- The point `-1 + I` lies in the upper half-plane. -/
theorem neg_one_add_I_mem_uhp : (-1 + I : ℂ) ∈ {z : ℂ | 0 < z.im} := by
  change 0 < (-1 + I : ℂ).im; simp

/-- The point `I` lies in the upper half-plane. -/
theorem I_mem_uhp : (I : ℂ) ∈ {z : ℂ | 0 < z.im} := by
  change 0 < (I : ℂ).im; simp

/-- Truncated contour equivalence: for `δ > 0`, the diagonal segment integral from
`-1 + δI` to `I` equals the vertical from `-1 + δI` to `-1 + I` plus the
horizontal from `-1 + I` to `I`. This is path independence for holomorphic
functions on the convex open upper half-plane. -/
theorem truncated_contour_equivalence (r : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    let a : ℂ := -1 + ↑δ * I
    let c : ℂ := -1 + I
    let b : ℂ := I
    let F := viazovska_integrand_left r
    (∫ t in (0:ℝ)..1, F (a + t • (b - a)) * (b - a)) =
    (∫ t in (0:ℝ)..1, F (a + t • (c - a)) * (c - a)) +
    (∫ t in (0:ℝ)..1, F (c + t • (b - c)) * (b - c)) :=
  segment_integral_add_of_holomorphic UpperHalfPlane.isOpen_upperHalfPlaneSet convex_upperHalfPlaneSet
    (viazovska_integrand_left_differentiableOn r)
    (neg_one_add_delta_I_mem_uhp hδ) I_mem_uhp neg_one_add_I_mem_uhp

private theorem integrand_at_zero_diag (r : ℝ) :
    viazovska_integrand_left r (contour_neg1_to_i 0) * (1 + I) = 0 := by
  simp [viazovska_integrand_left, contour_neg1_to_i]

private theorem integrand_at_zero_vert (r : ℝ) :
    viazovska_integrand_left r (-1 + I * (0 : ℝ)) * I = 0 := by
  simp [viazovska_integrand_left]

private theorem contour_neg1_to_i_im_pos {t : ℝ} (ht : 0 < t) :
    0 < (contour_neg1_to_i t).im := by
  simp [contour_neg1_to_i]; linarith

private theorem vertical_contour_im_pos {t : ℝ} (ht : 0 < t) :
    0 < (-1 + I * (↑t : ℂ)).im := by
  simp; linarith

private theorem diag_contour_add_one (t : ℝ) :
    contour_neg1_to_i t + 1 = (1 + I) * ↑t := by
  simp [contour_neg1_to_i]

private theorem vert_contour_add_one (t : ℝ) :
    (-1 : ℂ) + I * ↑t + 1 = I * ↑t := by ring

private theorem im_neg_inv_diag {t : ℝ} (ht : 0 < t) :
    (-1 / (contour_neg1_to_i t + 1)).im = 1 / (2 * t) := by
  rw [diag_contour_add_one, neg_div, Complex.neg_im, Complex.div_im]
  simp [Complex.mul_re, Complex.mul_im]
  rw [Complex.normSq_mk]; simp; field_simp; ring

private theorem im_neg_inv_vert {t : ℝ} (_ht : 0 < t) :
    (-1 / ((-1 : ℂ) + I * ↑t + 1)).im = 1 / t := by
  rw [vert_contour_add_one, neg_div, Complex.neg_im, Complex.div_im]
  simp [Complex.mul_re, Complex.mul_im]

private theorem norm_sq_diag {t : ℝ} (ht : 0 < t) :
    ‖(contour_neg1_to_i t + 1) ^ 2‖ ≤ 2 * t ^ 2 := by
  rw [diag_contour_add_one]
  simp only [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  rw [mul_pow]; gcongr ?_ * _
  rw [← Complex.normSq_eq_norm_sq]; norm_num [Complex.normSq_apply]

private theorem norm_sq_vert {t : ℝ} (ht : 0 < t) :
    ‖((-1 : ℂ) + I * ↑t + 1) ^ 2‖ ≤ t ^ 2 := by
  rw [vert_contour_add_one]
  simp [norm_pow, Complex.norm_real, abs_of_pos ht, Complex.norm_I]

private theorem exp_bound_diag {r : ℝ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖Complex.exp (↑Real.pi * I * ↑r * contour_neg1_to_i t)‖ ≤
      Real.exp (Real.pi * |r| * 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp_of_le
  simp [contour_neg1_to_i]
  nlinarith [Real.pi_pos, neg_abs_le r, abs_nonneg r, ht1,
    mul_le_mul_of_nonneg_right (neg_abs_le r) ht.le,
    mul_le_mul_of_nonneg_left (show t ≤ 2 by linarith) (abs_nonneg r)]

private theorem exp_bound_vert {r : ℝ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖Complex.exp (↑Real.pi * I * ↑r * ((-1 : ℂ) + I * ↑t))‖ ≤
      Real.exp (Real.pi * |r|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp_of_le
  simp
  nlinarith [Real.pi_pos, neg_abs_le r, abs_nonneg r, ht1,
    mul_le_mul_of_nonneg_right (neg_abs_le r) ht.le,
    mul_le_mul_of_nonneg_left ht1 (abs_nonneg r)]

private theorem phi0_bound_of_small_diag {t A : ℝ} (ht : 0 < t) (ht_lt : t < 1 / (2 * max A 1))
    (M : ℝ) (hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M) :
    ‖φ₀'' (-1 / (contour_neg1_to_i t + 1))‖ ≤ M := by
  have him_w : 0 < (-1 / (contour_neg1_to_i t + 1)).im :=
    neg_inv_add_one_im_pos (contour_neg1_to_i_im_pos ht)
  simp only [φ₀'', him_w, dif_pos]
  refine hMA ⟨_, him_w⟩ ?_
  simp [UpperHalfPlane.im]; rw [im_neg_inv_diag ht]
  have : max A 1 ≤ 1 / (2 * t) := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * max A 1)] at ht_lt
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * t)]; linarith
  linarith [le_max_left A 1]

private theorem phi0_bound_of_small_vert {t A : ℝ} (ht : 0 < t) (ht_lt : t < 1 / max A 1)
    (M : ℝ) (hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M) :
    ‖φ₀'' (-1 / ((-1 : ℂ) + I * ↑t + 1))‖ ≤ M := by
  have him_w : 0 < (-1 / ((-1 : ℂ) + I * ↑t + 1)).im :=
    neg_inv_add_one_im_pos (vertical_contour_im_pos ht)
  simp only [φ₀'', him_w, dif_pos]
  refine hMA ⟨_, him_w⟩ ?_
  change A ≤ (-1 / ((-1 : ℂ) + I * ↑t + 1)).im
  rw [im_neg_inv_vert ht]
  have : max A 1 ≤ 1 / t := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < max A 1)] at ht_lt
    rw [le_div_iff₀ (by positivity : (0:ℝ) < t)]; linarith
  linarith [le_max_left A 1]

private theorem integrand_norm_bound_diag {r : ℝ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {M A : ℝ} (hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M) (hM_nn : 0 ≤ M)
    (ht_lt_A : t < 1 / (2 * max A 1)) :
    ‖viazovska_integrand_left r (contour_neg1_to_i t) * (1 + I)‖ ≤
      ((M + 1) * 2 * Real.exp (Real.pi * |r| * 2) * ‖(1 : ℂ) + I‖ + 1) * t ^ 2 := by
  set C_bd := (M + 1) * 2 * Real.exp (Real.pi * |r| * 2) * ‖(1 : ℂ) + I‖ + 1
  calc ‖viazovska_integrand_left r (contour_neg1_to_i t) * (1 + I)‖
      ≤ ‖viazovska_integrand_left r (contour_neg1_to_i t)‖ * ‖(1 : ℂ) + I‖ :=
        norm_mul_le _ _
    _ ≤ (‖φ₀'' (-1 / (contour_neg1_to_i t + 1))‖ *
          ‖(contour_neg1_to_i t + 1) ^ 2‖ *
          ‖Complex.exp (↑Real.pi * I * ↑r * contour_neg1_to_i t)‖) *
        ‖(1 : ℂ) + I‖ := by
        gcongr; unfold viazovska_integrand_left
        exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ (M * (2 * t ^ 2) * Real.exp (Real.pi * |r| * 2)) * ‖(1 : ℂ) + I‖ := by
        gcongr
        · exact phi0_bound_of_small_diag ht ht_lt_A M hMA
        · exact norm_sq_diag ht
        · exact exp_bound_diag ht ht1
    _ ≤ C_bd * t ^ 2 := by
        simp only [C_bd]
        nlinarith [hM_nn, norm_nonneg ((1 : ℂ) + I), Real.exp_pos (Real.pi * |r| * 2),
          sq_nonneg t,
          mul_nonneg (Real.exp_pos (Real.pi * |r| * 2)).le (norm_nonneg ((1:ℂ) + I))]

private theorem integrand_norm_bound_vert {r : ℝ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {M A : ℝ} (hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M) (hM_nn : 0 ≤ M)
    (ht_lt_A : t < 1 / max A 1) :
    ‖viazovska_integrand_left r (-1 + I * ↑t) * I‖ ≤
      ((M + 1) * Real.exp (Real.pi * |r|) * ‖(I : ℂ)‖ + 1) * t ^ 2 := by
  set C_bd := (M + 1) * Real.exp (Real.pi * |r|) * ‖(I : ℂ)‖ + 1
  calc ‖viazovska_integrand_left r (-1 + I * ↑t) * I‖
      ≤ ‖viazovska_integrand_left r (-1 + I * ↑t)‖ * ‖(I : ℂ)‖ :=
        norm_mul_le _ _
    _ ≤ (‖φ₀'' (-1 / ((-1 : ℂ) + I * ↑t + 1))‖ *
          ‖((-1 : ℂ) + I * ↑t + 1) ^ 2‖ *
          ‖Complex.exp (↑Real.pi * I * ↑r * ((-1 : ℂ) + I * ↑t))‖) *
        ‖(I : ℂ)‖ := by
        gcongr; unfold viazovska_integrand_left
        exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ (M * t ^ 2 * Real.exp (Real.pi * |r|)) * ‖(I : ℂ)‖ := by
        gcongr
        · exact phi0_bound_of_small_vert ht ht_lt_A M hMA
        · exact norm_sq_vert ht
        · exact exp_bound_vert ht ht1
    _ ≤ C_bd * t ^ 2 := by
        simp only [C_bd]
        nlinarith [hM_nn, norm_nonneg (I : ℂ), Real.exp_pos (Real.pi * |r|),
          sq_nonneg t,
          mul_nonneg (Real.exp_pos (Real.pi * |r|)).le (norm_nonneg (I : ℂ))]

private theorem continuousWithinAt_zero_diag (r : ℝ) :
    ContinuousWithinAt (fun t : ℝ =>
      viazovska_integrand_left r (contour_neg1_to_i t) * (1 + I : ℂ))
      (Icc 0 1) 0 := by
  have hval := integrand_at_zero_diag r
  rw [ContinuousWithinAt, hval, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M₀, A, hMA₀⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp phi0_isBoundedAtImInfty
  set M := max M₀ 0
  have hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M :=
    fun z hz => (hMA₀ z hz).trans (le_max_left _ _)
  set C_bd := (M + 1) * 2 * Real.exp (Real.pi * |r| * 2) * ‖(1 : ℂ) + I‖ + 1
  have hC_pos : 0 < C_bd := by simp only [C_bd]; positivity
  set δ := min (1 / (2 * max A 1)) (Real.sqrt (ε / C_bd))
  filter_upwards [inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds 0
    (by positivity : 0 < δ))) self_mem_nhdsWithin] with t ⟨ht_ball, ht_Icc⟩
  simp only [dist_zero_right]
  simp [Metric.mem_ball] at ht_ball
  by_cases ht0 : t = 0
  · rw [ht0, hval]; simp [norm_zero]; exact hε
  · have ht_pos : 0 < t := lt_of_le_of_ne ht_Icc.1 (Ne.symm ht0)
    have ht_abs : t < δ := by rwa [abs_of_pos ht_pos] at ht_ball
    calc ‖viazovska_integrand_left r (contour_neg1_to_i t) * (1 + I)‖
        ≤ C_bd * t ^ 2 := integrand_norm_bound_diag ht_pos ht_Icc.2 hMA
            (le_max_right _ _) (lt_of_lt_of_le ht_abs (min_le_left _ _))
      _ < C_bd * (ε / C_bd) := by
          gcongr
          calc t ^ 2 < (Real.sqrt (ε / C_bd)) ^ 2 :=
                pow_lt_pow_left₀ (lt_of_lt_of_le ht_abs (min_le_right _ _))
                  ht_pos.le (by norm_num : 2 ≠ 0)
            _ = ε / C_bd := Real.sq_sqrt (by positivity)
      _ = ε := by field_simp

private theorem continuousWithinAt_zero_vert (r : ℝ) :
    ContinuousWithinAt (fun t : ℝ =>
      viazovska_integrand_left r (-1 + I * ↑t) * I)
      (Icc 0 1) 0 := by
  have hval := integrand_at_zero_vert r
  rw [ContinuousWithinAt, hval, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M₀, A, hMA₀⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp phi0_isBoundedAtImInfty
  set M := max M₀ 0
  have hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M :=
    fun z hz => (hMA₀ z hz).trans (le_max_left _ _)
  set C_bd := (M + 1) * Real.exp (Real.pi * |r|) * ‖(I : ℂ)‖ + 1
  have hC_pos : 0 < C_bd := by simp only [C_bd]; positivity
  set δ := min (1 / max A 1) (Real.sqrt (ε / C_bd))
  filter_upwards [inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds 0
    (by positivity : 0 < δ))) self_mem_nhdsWithin] with t ⟨ht_ball, ht_Icc⟩
  simp only [dist_zero_right]
  simp [Metric.mem_ball] at ht_ball
  by_cases ht0 : t = 0
  · rw [ht0, hval]; simp [norm_zero]; exact hε
  · have ht_pos : 0 < t := lt_of_le_of_ne ht_Icc.1 (Ne.symm ht0)
    have ht_abs : t < δ := by rwa [abs_of_pos ht_pos] at ht_ball
    calc ‖viazovska_integrand_left r (-1 + I * ↑t) * I‖
        ≤ C_bd * t ^ 2 := integrand_norm_bound_vert ht_pos ht_Icc.2 hMA
            (le_max_right _ _) (lt_of_lt_of_le ht_abs (min_le_left _ _))
      _ < C_bd * (ε / C_bd) := by
          gcongr
          calc t ^ 2 < (Real.sqrt (ε / C_bd)) ^ 2 :=
                pow_lt_pow_left₀ (lt_of_lt_of_le ht_abs (min_le_right _ _))
                  ht_pos.le (by norm_num : 2 ≠ 0)
            _ = ε / C_bd := Real.sq_sqrt (by positivity)
      _ = ε := by field_simp

/-- The parameterized diagonal integrand is continuous on `[0,1]`. -/
theorem continuousOn_diagonal_integrand (r : ℝ) :
    ContinuousOn (fun t : ℝ =>
      viazovska_integrand_left r (contour_neg1_to_i t) * (1 + I : ℂ))
      (Icc 0 1) := fun x hx => by
  rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
  · exact continuousWithinAt_zero_diag r
  · exact ((viazovska_integrand_left_differentiableOn r).continuousOn.comp
      (continuous_const.add (continuous_const.mul continuous_ofReal)).continuousOn
      (fun _ ht => contour_neg1_to_i_im_pos ht) |>.mul continuousOn_const
      |>.continuousAt (Ioi_mem_nhds hx_pos)).continuousWithinAt

/-- The parameterized vertical integrand is continuous on `[0,1]`. -/
theorem continuousOn_vertical_integrand (r : ℝ) :
    ContinuousOn (fun t : ℝ =>
      viazovska_integrand_left r (-1 + I * ↑t) * I)
      (Icc 0 1) := fun x hx => by
  rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
  · exact continuousWithinAt_zero_vert r
  · exact ((viazovska_integrand_left_differentiableOn r).continuousOn.comp
      (continuous_const.add (continuous_const.mul continuous_ofReal)).continuousOn
      (fun _ ht => vertical_contour_im_pos ht) |>.mul continuousOn_const
      |>.continuousAt (Ioi_mem_nhds hx_pos)).continuousWithinAt

/-- The primitive `G` of `viazovska_integrand_left r` on the upper half-plane,
whose existence follows from `holomorphic_convex_primitive`. -/
theorem exists_primitive_viazovska_integrand_left (r : ℝ) :
    ∃ G : ℂ → ℂ, ∀ z ∈ {z : ℂ | 0 < z.im},
      HasDerivAt G (viazovska_integrand_left r z) z :=
  holomorphic_convex_primitive convex_upperHalfPlaneSet UpperHalfPlane.isOpen_upperHalfPlaneSet
    ⟨I, I_mem_uhp⟩ (viazovska_integrand_left_differentiableOn r)

/-- The truncated diagonal integral from `-1 + δI` to `I` equals `G(I) - G(-1+δI)`
for the primitive `G` of the integrand. -/
theorem truncated_diagonal_eq_primitive_sub (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovska_integrand_left r z) z)
    (δ : ℝ) (hδ : 0 < δ) :
    (∫ t in (0:ℝ)..1, viazovska_integrand_left r
      ((-1 + ↑δ * I) + t • ((I : ℂ) - (-1 + ↑δ * I))) *
        ((I : ℂ) - (-1 + ↑δ * I))) = G I - G (-1 + ↑δ * I) :=
  segment_integral_eq_sub_of_hasDerivAt convex_upperHalfPlaneSet
    (neg_one_add_delta_I_mem_uhp hδ) I_mem_uhp hG
    (viazovska_integrand_left_differentiableOn r).continuousOn

/-- The truncated vertical integral from `-1 + δI` to `-1 + I` equals
`G(-1+I) - G(-1+δI)` for the primitive. -/
theorem truncated_vertical_eq_primitive_sub (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovska_integrand_left r z) z)
    (δ : ℝ) (hδ : 0 < δ) :
    (∫ t in (0:ℝ)..1, viazovska_integrand_left r
      ((-1 + ↑δ * I) + t • ((-1 + I) - (-1 + ↑δ * I))) *
        ((-1 + I) - (-1 + ↑δ * I))) = G (-1 + I) - G (-1 + ↑δ * I) :=
  segment_integral_eq_sub_of_hasDerivAt convex_upperHalfPlaneSet
    (neg_one_add_delta_I_mem_uhp hδ) neg_one_add_I_mem_uhp hG
    (viazovska_integrand_left_differentiableOn r).continuousOn

/-- The horizontal integral from `-1 + I` to `I` equals `G(I) - G(-1+I)`. -/
theorem horizontal_eq_primitive_sub (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovska_integrand_left r z) z) :
    I12_horiz r = G I - G (-1 + I) := by
  rw [I12_horiz_eq_segment]
  exact segment_integral_eq_sub_of_hasDerivAt convex_upperHalfPlaneSet
    neg_one_add_I_mem_uhp I_mem_uhp hG
    (viazovska_integrand_left_differentiableOn r).continuousOn

/-- `I12` equals the integral restricted to `[δ, 1]` plus the integral on `[0, δ]`.
For continuous integrands (from `continuousOn_diagonal_integrand`), the `[0, δ]` part
vanishes as `δ → 0`. -/
theorem I12_split_at_delta (r : ℝ) (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hcont : ContinuousOn (fun t : ℝ =>
      viazovska_integrand_left r (contour_neg1_to_i t) * (1 + I : ℂ)) (Icc 0 1)) :
    I12 r = (∫ t in (0:ℝ)..δ,
      viazovska_integrand_left r (contour_neg1_to_i t) * (1 + I)) +
      (∫ t in δ..1,
      viazovska_integrand_left r (contour_neg1_to_i t) * (1 + I)) := by
  have hI12 : I12 r = ∫ t in (0:ℝ)..1,
      viazovska_integrand_left r (contour_neg1_to_i t) * (1 + I) := by
    unfold I12; congr 1; ext t; rw [deriv_contour_neg1_to_i]
  rw [hI12]
  have hint := hcont.intervalIntegrable_of_Icc (μ := volume) (by linarith : (0:ℝ) ≤ 1)
  have hδ_mem : δ ∈ Set.uIcc (0:ℝ) 1 := Set.mem_uIcc.mpr (Or.inl ⟨hδ₀, hδ₁⟩)
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set (Set.uIcc_subset_uIcc_left hδ_mem))
    (hint.mono_set (Set.uIcc_subset_uIcc_right hδ_mem))).symm

/-- `I12_vert` equals the integral restricted to `[δ, 1]` plus the integral on `[0, δ]`. -/
theorem I12_vert_split_at_delta (r : ℝ) (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hcont : ContinuousOn (fun t : ℝ =>
      viazovska_integrand_left r (-1 + I * ↑t) * I) (Icc 0 1)) :
    I12_vert r = (∫ t in (0:ℝ)..δ,
      viazovska_integrand_left r (-1 + I * ↑t) * I) +
      (∫ t in δ..1,
      viazovska_integrand_left r (-1 + I * ↑t) * I) := by
  unfold I12_vert
  have hint := hcont.intervalIntegrable_of_Icc (μ := volume) (by linarith : (0:ℝ) ≤ 1)
  have hδ_mem : δ ∈ Set.uIcc (0:ℝ) 1 := Set.mem_uIcc.mpr (Or.inl ⟨hδ₀, hδ₁⟩)
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set (Set.uIcc_subset_uIcc_left hδ_mem))
    (hint.mono_set (Set.uIcc_subset_uIcc_right hδ_mem))).symm

private theorem hasDerivAt_vert_contour (t : ℝ) :
    HasDerivAt (fun s : ℝ => (-1 : ℂ) + I * ↑s) (I : ℂ) t := by
  have h1 := (ofRealCLM.hasDerivAt (x := t)).const_mul (I : ℂ)
  simp [ofRealCLM] at h1
  convert (hasDerivAt_const t (-1 : ℂ)).add h1 using 1; ring

theorem ftc_tail_diag (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovska_integrand_left r z) z)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ t in δ..1, viazovska_integrand_left r (contour_neg1_to_i t) * (1 + I) =
      G (contour_neg1_to_i 1) - G (contour_neg1_to_i δ) := by
  have hcont := continuousOn_diagonal_integrand r
  have hGdiag : ∀ t ∈ Set.uIcc δ 1, HasDerivAt (fun s => G (contour_neg1_to_i s))
      (viazovska_integrand_left r (contour_neg1_to_i t) * (1 + I)) t := by
    intro t ht
    have ht_pos : 0 < t := by
      rcases Set.mem_uIcc.mp ht with ⟨h1, _⟩ | ⟨_, h2⟩ <;> linarith
    exact ((@HasDerivAt.scomp ℝ _ ℂ _ _ t ℂ _ _ _ IsScalarTower.right _ _ _ _
      (hG _ (contour_neg1_to_i_im_pos ht_pos))
      (hasDerivAt_contour_neg1_to_i t))).congr_deriv (by simp [smul_eq_mul]; ring)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hGdiag
    ((hcont.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)).intervalIntegrable_of_Icc
      (by linarith))
  simpa [Function.comp] using h

theorem ftc_tail_vert (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovska_integrand_left r z) z)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ t in δ..1, viazovska_integrand_left r (-1 + I * ↑t) * I =
      G (-1 + I * (1 : ℝ)) - G (-1 + I * ↑δ) := by
  have hcont := continuousOn_vertical_integrand r
  have hGvert : ∀ t ∈ Set.uIcc δ 1, HasDerivAt (fun s : ℝ => G (-1 + I * ↑s))
      (viazovska_integrand_left r (-1 + I * ↑t) * I) t := by
    intro t ht
    have ht_pos : 0 < t := by
      rcases Set.mem_uIcc.mp ht with ⟨h1, _⟩ | ⟨_, h2⟩ <;> linarith
    exact ((@HasDerivAt.scomp ℝ _ ℂ _ _ t ℂ _ _ _ IsScalarTower.right _ _ _ _
      (hG _ (vertical_contour_im_pos ht_pos))
      (hasDerivAt_vert_contour t))).congr_deriv (by simp [smul_eq_mul]; ring)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hGvert
    ((hcont.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)).intervalIntegrable_of_Icc
      (by linarith))

private theorem D_eq_three_terms (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovska_integrand_left r z) z)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    I12 r - (I12_vert r + I12_horiz r) =
      (∫ t in (0:ℝ)..δ, viazovska_integrand_left r (contour_neg1_to_i t) * (1 + I)) -
      (∫ t in (0:ℝ)..δ, viazovska_integrand_left r (-1 + I * ↑t) * I) +
      (G (-1 + ↑δ * I) - G (contour_neg1_to_i δ)) := by
  have hsd := I12_split_at_delta r δ hδ.le hδ1 (continuousOn_diagonal_integrand r)
  have hsv := I12_vert_split_at_delta r δ hδ.le hδ1 (continuousOn_vertical_integrand r)
  have htd := ftc_tail_diag r G hG δ hδ hδ1
  have hc1 : contour_neg1_to_i 1 = I := by simp [contour_neg1_to_i]
  rw [hc1] at htd
  have htv := ftc_tail_vert r G hG δ hδ hδ1
  have hv1 : (-1 : ℂ) + I * (1 : ℝ) = -1 + I := by push_cast; ring
  rw [hv1] at htv
  have hhoriz := horizontal_eq_primitive_sub r G hG
  have hcomm : (-1 : ℂ) + ↑δ * I = -1 + I * ↑δ := by ring
  rw [hcomm]
  linear_combination hsd + htd - hsv - htv - hhoriz

theorem head_integral_tendsto_zero {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Icc 0 1)) :
    Filter.Tendsto (fun δ => ∫ t in (0:ℝ)..δ, f t) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hC_nn : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_refl _, zero_le_one⟩)
  rw [Metric.tendsto_nhds]; intro ε hε
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds 0 (show 0 < min (ε / (C + 1)) 1 by positivity)]
    with δ hball hδ_pos
  simp only [Set.mem_Ioi] at hδ_pos
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at hball
  rw [abs_of_pos hδ_pos] at hball
  rw [dist_zero_right]
  calc ‖∫ t in (0:ℝ)..δ, f t‖
      ≤ (C + 1) * |δ - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht; rcases Set.mem_uIoc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact (hC t ⟨by linarith, by linarith [lt_of_lt_of_le hball (min_le_right _ _)]⟩).trans
            (by linarith)
        · linarith
    _ < (C + 1) * (ε / (C + 1)) := by
        rw [sub_zero, abs_of_pos hδ_pos]
        exact mul_lt_mul_of_pos_left
          (lt_of_lt_of_le hball (min_le_left _ _)) (by linarith)
    _ = ε := by field_simp

private theorem segment_integrand_norm_bound (r : ℝ) {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ1 : δ ≤ 1) {M A : ℝ}
    (hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M) (hM_nn : 0 ≤ M)
    (hδ_lt_A : δ < 1 / (2 * max A 1))
    (hδ_lt_sqrt : δ < Real.sqrt (1 / ((M + 1) * 2 * Real.exp (Real.pi * |r| * 2))))
    {t : ℝ} (ht1 : 0 < t) (ht2 : t ≤ 1) :
    let a : ℂ := -1 + ↑δ * ((1 : ℂ) + I)
    let dir : ℂ := -(↑δ : ℂ)
    ‖viazovska_integrand_left r (a + ↑t • dir) * dir‖ ≤ δ := by
  intro a dir
  set z₀ := a + ↑t • dir
  have him : 0 < z₀.im := by simp [z₀, a, dir]; linarith
  have hz_plus_1 : z₀ + 1 = ↑δ * ((1 - ↑t : ℂ) + I) := by simp [z₀, a, dir]; ring
  have him_w : 0 < (-1 / (z₀ + 1)).im := neg_inv_add_one_im_pos him
  have hnsq : Complex.normSq (z₀ + 1) = δ ^ 2 * ((1 - t) ^ 2 + 1) := by
    rw [hz_plus_1, Complex.normSq_apply]; simp; ring
  have him_eq : (z₀ + 1).im = δ := by rw [hz_plus_1]; simp
  have h1t_sq : (1 - t) ^ 2 + 1 ≤ 2 := by nlinarith
  have him_lb : 1 / (2 * δ) ≤ (-1 / (z₀ + 1)).im := by
    rw [neg_div, Complex.neg_im, Complex.div_im]
    simp only [Complex.one_re, Complex.one_im, zero_mul, zero_div, one_mul, zero_sub, neg_neg]
    rw [hnsq, him_eq]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * δ)
      (by positivity : 0 < δ ^ 2 * ((1 - t) ^ 2 + 1))]
    nlinarith [sq_nonneg δ]
  have hA_le : A ≤ (-1 / (z₀ + 1)).im := by
    have : max A 1 ≤ 1 / (2 * δ) := by
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * max A 1)] at hδ_lt_A
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * δ)]; linarith
    linarith [le_max_left A 1]
  have hφ : ‖φ₀'' (-1 / (z₀ + 1))‖ ≤ M := by
    simp only [φ₀'', him_w, dif_pos]
    exact hMA ⟨_, him_w⟩ (by simp [UpperHalfPlane.im]; linarith)
  have hsq : ‖(z₀ + 1) ^ 2‖ ≤ 2 * δ ^ 2 := by
    rw [norm_pow, ← Complex.normSq_eq_norm_sq, hnsq]
    nlinarith [sq_nonneg δ, h1t_sq]
  have hexp : ‖Complex.exp (↑Real.pi * I * ↑r * z₀)‖ ≤
      Real.exp (Real.pi * |r| * 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp_of_le
    simp [z₀, a, dir]
    nlinarith [Real.pi_pos, neg_abs_le r, abs_nonneg r,
      mul_le_mul_of_nonneg_right (neg_abs_le r) hδ_pos.le,
      mul_le_mul_of_nonneg_left hδ1 (abs_nonneg r)]
  set C_seg := (M + 1) * 2 * Real.exp (Real.pi * |r| * 2)
  have hC_seg_pos : 0 < C_seg := by positivity
  have hFb : ‖viazovska_integrand_left r z₀‖ ≤ 1 := by
    have hF_unfold : ‖viazovska_integrand_left r z₀‖ ≤
        ‖φ₀'' (-1 / (z₀ + 1))‖ * ‖(z₀ + 1) ^ 2‖ *
        ‖Complex.exp (↑Real.pi * I * ↑r * z₀)‖ := by
      unfold viazovska_integrand_left
      exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    have hCδ : C_seg * δ ^ 2 ≤ 1 := by
      have h1 : δ ^ 2 < (Real.sqrt (1 / C_seg)) ^ 2 :=
        pow_lt_pow_left₀ hδ_lt_sqrt hδ_pos.le (by norm_num : 2 ≠ 0)
      rw [Real.sq_sqrt (by positivity)] at h1
      have h2 : C_seg * δ ^ 2 < C_seg * (1 / C_seg) :=
        mul_lt_mul_of_pos_left h1 hC_seg_pos
      simp [ne_of_gt hC_seg_pos] at h2; linarith
    calc ‖viazovska_integrand_left r z₀‖
        ≤ M * (2 * δ ^ 2) * Real.exp (Real.pi * |r| * 2) :=
          hF_unfold.trans (by gcongr)
      _ ≤ C_seg * δ ^ 2 := by
          simp only [C_seg]
          nlinarith [hM_nn, Real.exp_pos (Real.pi * |r| * 2), sq_nonneg δ]
      _ ≤ 1 := hCδ
  have hneg_norm : ‖dir‖ = δ := by
    show ‖(-(↑δ : ℂ))‖ = δ
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ_pos]
  calc ‖viazovska_integrand_left r z₀ * dir‖
      ≤ ‖viazovska_integrand_left r z₀‖ * ‖dir‖ := norm_mul_le _ _
    _ ≤ 1 * δ := by rw [hneg_norm]; exact mul_le_mul_of_nonneg_right hFb hδ_pos.le
    _ = δ := one_mul _

theorem G_diff_tendsto_zero (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovska_integrand_left r z) z) :
    Filter.Tendsto
      (fun δ : ℝ => G (-1 + ↑δ * I) - G (contour_neg1_to_i δ)) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]; intro ε hε
  obtain ⟨M₀, A, hMA₀⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp phi0_isBoundedAtImInfty
  set M := max M₀ 0
  have hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M :=
    fun z hz => (hMA₀ z hz).trans (le_max_left _ _)
  have hM_nn : (0 : ℝ) ≤ M := le_max_right _ _
  set C_seg := (M + 1) * 2 * Real.exp (Real.pi * |r| * 2)
  have hC_seg_pos : 0 < C_seg := by positivity
  set δ_bd := min (min ε (1 / (2 * max A 1))) (min (Real.sqrt (1 / C_seg)) 1)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds 0 (by positivity : 0 < δ_bd)] with δ hball_δ hδ_pos
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero, Set.mem_Ioi] at hball_δ hδ_pos
  rw [abs_of_pos hδ_pos] at hball_δ
  have hδ_lt_ε : δ < ε :=
    lt_of_lt_of_le hball_δ (min_le_left _ _ |>.trans (min_le_left _ _))
  have hδ_lt_A : δ < 1 / (2 * max A 1) :=
    lt_of_lt_of_le hball_δ (min_le_left _ _ |>.trans (min_le_right _ _))
  have hδ_lt_sqrt : δ < Real.sqrt (1 / C_seg) :=
    lt_of_lt_of_le hball_δ (min_le_right _ _ |>.trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 :=
    le_of_lt (lt_of_lt_of_le hball_δ (min_le_right _ _ |>.trans (min_le_right _ _)))
  have hcδ : contour_neg1_to_i δ = -1 + ↑δ * ((1 : ℂ) + I) := by
    simp [contour_neg1_to_i]; ring
  rw [dist_zero_right, hcδ]
  set a : ℂ := -1 + ↑δ * ((1 : ℂ) + I)
  set dir : ℂ := -(↑δ : ℂ)
  have ha_uhp : a ∈ {z : ℂ | 0 < z.im} := by simp [a]; nlinarith
  have hb_uhp := neg_one_add_delta_I_mem_uhp hδ_pos
  have hdir_eq : (-1 + ↑δ * I : ℂ) - a = dir := by simp [a, dir]; ring
  have hG_seg : G (-1 + ↑δ * I) - G a =
      ∫ t in (0:ℝ)..1, viazovska_integrand_left r (a + ↑t • dir) * dir := by
    rw [show dir = (-1 + ↑δ * I : ℂ) - a from hdir_eq.symm]
    symm
    exact segment_integral_eq_sub_of_hasDerivAt convex_upperHalfPlaneSet ha_uhp hb_uhp hG
      (viazovska_integrand_left_differentiableOn r).continuousOn
  rw [hG_seg]
  have hpt_bound : ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖viazovska_integrand_left r (a + ↑t • dir) * dir‖ ≤ δ := by
    intro t ht
    rcases Set.mem_uIoc.mp ht with ⟨ht1, ht2⟩ | ⟨ht1, ht2⟩
    swap; · linarith
    exact segment_integrand_norm_bound r hδ_pos hδ1 hMA hM_nn hδ_lt_A hδ_lt_sqrt ht1 ht2
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpt_bound
  simp only [sub_zero, abs_one, mul_one] at hbound
  linarith

/-- **Full contour equivalence**: the diagonal integral `I12` from `-1` to `I`
equals the sum of the vertical integral `I12_vert` (from `-1` to `-1+I`)
and the horizontal integral `I12_horiz` (from `-1+I` to `I`). -/
theorem I12_eq_rectangular (r : ℝ) : I12 r = I12_vert r + I12_horiz r := by
  suffices hsuff : I12 r - (I12_vert r + I12_horiz r) = 0 from eq_of_sub_eq_zero hsuff
  obtain ⟨G, hG⟩ := exists_primitive_viazovska_integrand_left r
  set F := viazovska_integrand_left r
  set S := fun δ : ℝ => (∫ t in (0:ℝ)..δ, F (contour_neg1_to_i t) * (1 + I)) -
    (∫ t in (0:ℝ)..δ, F (-1 + I * ↑t) * I) + (G (-1 + ↑δ * I) - G (contour_neg1_to_i δ))
  have heq : ∀ᶠ δ in 𝓝[>] 0, I12 r - (I12_vert r + I12_horiz r) = S δ := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℝ) one_pos)] with δ hδ hδ_ball
    simp only [Set.mem_Ioi] at hδ; simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at hδ_ball
    exact D_eq_three_terms r G hG δ hδ (by linarith [abs_of_pos hδ])
  have hS : Filter.Tendsto S (𝓝[>] 0) (𝓝 0) := by
    have := (head_integral_tendsto_zero (continuousOn_diagonal_integrand r)).sub
      (head_integral_tendsto_zero (continuousOn_vertical_integrand r))
      |>.add (G_diff_tendsto_zero r G hG)
    simpa using this
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' heq) hS

end
