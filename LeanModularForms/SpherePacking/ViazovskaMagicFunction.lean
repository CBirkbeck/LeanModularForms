/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.GeneralizedResidueTheorem
import LeanModularForms.GeneralizedResidueTheory.Cycle
import LeanModularForms.GeneralizedResidueTheory.CauchyPrimitive
import LeanModularForms.Modularforms.Eisenstein
import LeanModularForms.SpherePacking.PhiHolomorphic

/-!
# Viazovska's Magic Function via Generalized Residue Theorem

This file defines the magic function `a(r)` from Viazovska's proof of
the optimality of the E₈ sphere packing [Via2017], using the **original
contour integrals** from the paper rather than the rectangular deformation
used in other formalizations.

## The original contour integrals

The function `a_rad(r)` is defined as:
```
a_rad(r) = ∫_{-1}^{i} φ₀(-1/(z+1)) · (z+1)² · e^{πirz} dz
         + ∫_{1}^{i}  φ₀(-1/(z-1)) · (z-1)² · e^{πirz} dz
         - 2 ∫_{0}^{i} φ₀(-1/z) · z² · e^{πirz} dz
         + 2 ∫_{i}^{i∞} φ₀(z) · e^{πirz} dz
```

where `φ₀(z) = (E₂E₄ - E₆)² / Δ(z)`.

The contours are straight line segments from the real axis to `i`.
At the starting points `-1`, `1`, `0` on the real axis, the Dedekind
discriminant `Δ → 0` (cusp singularity), but the factors `(z+1)²`,
`(z-1)²`, `z²` cancel this singularity, making the integrands vanish
at the boundary.

## Approach

Using the generalized residue theorem (Hungerbühler-Wasem, Theorem 3.3),
we can work directly with these original contours, handling the boundary
behavior at the cusps via the Cauchy principal value framework. This
avoids the rectangular contour deformation used in the Sphere-Packing-Lean
formalization.

## References

* Viazovska, M. S. (2017). "The sphere packing problem in dimension 8."
  Annals of Mathematics, 185(3), 991-1015.
* Hungerbühler, N., Wasem, M. (2019). "A generalized version of the
  residue theorem." arXiv:1808.00997v2.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Interval

noncomputable section

/-! ## Modular form ingredients

We use `φ₀''` (the ℂ-extended version of φ₀) from `Modularforms/Eisenstein.lean`.
This is defined as `φ₀''(z) = φ₀(z)` when `Im(z) > 0`, and `0` otherwise.
The underlying `φ₀(z) = (E₂E₄ - E₆)² / Δ(z)` is defined on the upper half-plane ℍ.

Key properties (proven in Eisenstein.lean and Delta.lean):
- `φ₀` is holomorphic on ℍ (since Δ ≠ 0 on ℍ)
- Periodic: `φ₀(z+1) = φ₀(z)`
- S-transform: `φ₀(-1/z) = φ₀(z) - (12i/π)·(1/z)·φ₋₂(z) - (36/π²)·(1/z²)·φ₋₄(z)`
- Vanishing: `φ₀(z) = O(e^{-2πIm(z)})` as `Im(z) → ∞`
-/

/-! ## Original Viazovska contour integrals

The four integrals defining a_rad(r), using straight-line contours
from the real axis to i. -/

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

/-! ## The magic function a_rad(r)

Defined using the original Viazovska contours. -/

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

/-! ## Holomorphicity of φ₀

φ₀ = (E₂·E₄ - E₆)² / Δ is holomorphic on ℍ because:
- E₂ is holomorphic (proved in PhiHolomorphic.lean via `E₂ = const · logDeriv(η)`)
- E₄, E₆ are modular forms (holomorphic by `.holo'`)
- Δ is a cusp form (holomorphic) and Δ ≠ 0 on ℍ
- Products, differences, squares, and ratios of holomorphic functions
  (with nonzero denominator) are holomorphic -/

/-- φ₀'' is holomorphic on the upper half-plane. -/
theorem φ₀''_differentiableOn : DifferentiableOn ℂ φ₀'' {z : ℂ | 0 < z.im} := by
  have hE₂ := E₂_differentiableOn
  have hE₄ := UpperHalfPlane.mdifferentiable_iff.mp E₄.holo'
  have hE₆ := UpperHalfPlane.mdifferentiable_iff.mp E₆.holo'
  have hΔ := UpperHalfPlane.mdifferentiable_iff.mp Delta.holo'
  intro z hz
  have hz' : 0 < z.im := hz
  have hE₂z := (E₂_differentiableOn z hz).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz')
  have hE₄z := (hE₄ z hz).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz')
  have hE₆z := (hE₆ z hz).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz')
  have hΔz := (hΔ z hz).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz')
  have hΔ_ne : (Delta.toSlashInvariantForm ∘ UpperHalfPlane.ofComplex) z ≠ 0 := by
    simp [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz']; exact Δ_ne_zero ⟨z, hz'⟩
  have hdiff := ((hE₂z.mul hE₄z).sub hE₆z).pow 2 |>.div hΔz hΔ_ne
  have hopen := (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz'
  apply hdiff.differentiableWithinAt.congr_of_eventuallyEq
  rw [nhdsWithin_eq_nhds.mpr (Filter.mem_of_superset hopen (fun _ h => h))]
  filter_upwards [hopen] with w hw
  simp only [φ₀'', hw, dif_pos, φ₀, Function.comp,
    UpperHalfPlane.ofComplex_apply_of_im_pos hw, Pi.mul_apply, Pi.sub_apply,
    Pi.pow_apply, Pi.div_apply]; rfl
  · simp only [φ₀'', hz', dif_pos, φ₀, Function.comp,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz', Pi.mul_apply, Pi.sub_apply,
      Pi.pow_apply, Pi.div_apply]; rfl

/-! ## Upper half-plane: convexity and openness -/

/-- The upper half-plane `{z : ℂ | 0 < z.im}` is open. -/
theorem isOpen_upperHalfPlaneSet : IsOpen {z : ℂ | 0 < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

/-- The upper half-plane `{z : ℂ | 0 < z.im}` is convex. -/
theorem convex_upperHalfPlaneSet : Convex ℝ {z : ℂ | 0 < z.im} := by
  intro x hx y hy a b ha hb hab
  show 0 < (a • x + b • y).im
  have him : (a • x + b • y).im = a * x.im + b * y.im := by
    simp [Complex.add_im]
  rw [him]
  have hx' : (0 : ℝ) < x.im := hx
  have hy' : (0 : ℝ) < y.im := hy
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp at hab; subst hab; simp; linarith
  · linarith [mul_pos ha' hx', mul_nonneg hb (le_of_lt hy')]

/-! ## Holomorphicity of the integrand -/

/-- When `Im(z) > 0`, the point `-1/(z+1)` also has positive imaginary part. -/
theorem neg_inv_add_one_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (-1 / (z + 1)).im := by
  have hne : z + 1 ≠ 0 := by
    intro h; have := (Complex.ext_iff.mp h).2; simp at this; linarith
  rw [neg_div, Complex.neg_im, Complex.div_im]
  rw [Complex.one_im, Complex.one_re, zero_mul, zero_div, one_mul, zero_sub, neg_neg]
  exact div_pos (by simp [Complex.add_im]; linarith) (Complex.normSq_pos.mpr hne)

/-- The integrand `viazovska_integrand_left r` is holomorphic on the upper half-plane.
This follows from holomorphicity of `φ₀''` and the algebraic factors. -/
theorem viazovska_integrand_left_differentiableOn (r : ℝ) :
    DifferentiableOn ℂ (viazovska_integrand_left r) {z : ℂ | 0 < z.im} := by
  intro z hz
  unfold viazovska_integrand_left
  have hz' : 0 < z.im := hz
  have hne : z + 1 ≠ 0 := by
    intro h; have := (Complex.ext_iff.mp h).2; simp at this; linarith
  have him := neg_inv_add_one_im_pos hz'
  have hφ : DifferentiableAt ℂ φ₀'' (-1 / (z + 1)) :=
    (φ₀''_differentiableOn _ him).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds him)
  have hinv : DifferentiableAt ℂ (fun w => -1 / (w + 1)) z :=
    (differentiableAt_const _).div
      (differentiableAt_id.add (differentiableAt_const _)) hne
  exact ((hφ.comp z hinv).mul
    ((differentiableAt_id.add (differentiableAt_const _)).pow 2) |>.mul
    (Complex.differentiable_exp.differentiableAt.comp z
      ((differentiableAt_const _).mul differentiableAt_id))).differentiableWithinAt

/-! ## Contour equivalence infrastructure

### Segment integrals and the fundamental theorem of calculus

Given a holomorphic function `f` on a convex open set `S` with primitive `G`
(i.e., `G' = f` on `S`), the segment integral from `a` to `b` equals `G(b) - G(a)`.
This gives path independence: for `a, b, c ∈ S`,
```
∫_{a→b} f dz = ∫_{a→c} f dz + ∫_{c→b} f dz
```
since both sides equal `G(b) - G(a)`. -/

/-- FTC for segment integrals: if `G' = f` on a convex open set,
then the segment integral of `f` from `a` to `b` equals `G(b) - G(a)`. -/
theorem segment_integral_eq_sub_of_hasDerivAt {f G : ℂ → ℂ} {S : Set ℂ}
    (_hS_open : IsOpen S) (hS_convex : Convex ℝ S)
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S)
    (hG : ∀ z ∈ S, HasDerivAt G (f z) z)
    (hf_cont : ContinuousOn f S) :
    ∫ t in (0:ℝ)..1, f (a + t • (b - a)) * (b - a) = G b - G a := by
  have h_mem : ∀ t ∈ Icc (0 : ℝ) 1, a + ↑t • (b - a) ∈ S := by
    intro t ht
    have : a + ↑t • (b - a) = (1 - t) • a + t • b := by
      simp only [smul_sub, sub_smul, one_smul]; ring
    rw [this]
    exact hS_convex ha hb (by linarith [ht.2]) ht.1 (by ring)
  have hcont : ContinuousOn (fun t : ℝ => f (a + t • (b - a))) (Icc 0 1) :=
    hf_cont.comp (continuous_const.add
      (continuous_ofReal.smul continuous_const)).continuousOn h_mem
  have key := intervalIntegral.integral_unitInterval_deriv_eq_sub (𝕜 := ℂ)
    (f := G) (f' := f) (z₀ := a) (z₁ := b - a)
    hcont (fun t ht => hG _ (h_mem t ht))
  rw [show a + (b - a) = b from by ring] at key
  rw [smul_eq_mul] at key
  rw [intervalIntegral.integral_mul_const, mul_comm]
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
  rw [segment_integral_eq_sub_of_hasDerivAt hS_open hS_convex ha hb hG hf.continuousOn,
      segment_integral_eq_sub_of_hasDerivAt hS_open hS_convex ha hc hG hf.continuousOn,
      segment_integral_eq_sub_of_hasDerivAt hS_open hS_convex hc hb hG hf.continuousOn]
  ring

/-! ### Contour parameterization lemmas -/

/-- The derivative of `contour_neg1_to_i` is the constant `1 + I`. -/
theorem deriv_contour_neg1_to_i (t : ℝ) : deriv contour_neg1_to_i t = 1 + I := by
  have h1 : HasDerivAt (fun s : ℝ => (-1 : ℂ) + (1 + I) * ↑s) (1 + I) t := by
    have h := (ofRealCLM.hasDerivAt (x := t)).const_mul (1 + I : ℂ)
    have hv : (1 + I) * ofRealCLM (1 : ℝ) = 1 + I := by
      simp [ofRealCLM, Complex.ofReal_one]
    rw [hv] at h
    exact (hasDerivAt_const t (-1 : ℂ)).add h |>.congr_deriv (by ring)
  have h2 : (fun s : ℝ => (-1 : ℂ) + (1 + I) * ↑s) = contour_neg1_to_i := by
    ext s; simp [contour_neg1_to_i]
  rw [h2] at h1; exact h1.deriv

/-- `I12` expressed as a segment integral from `-1` to `I`. -/
theorem I12_eq_segment_integral (r : ℝ) :
    I12 r = ∫ t in (0:ℝ)..1,
      viazovska_integrand_left r ((-1 : ℂ) + t • ((I : ℂ) - (-1))) *
        ((I : ℂ) - (-1)) := by
  unfold I12; congr 1; ext t
  rw [deriv_contour_neg1_to_i]
  have h1 : contour_neg1_to_i t = (-1 : ℂ) + ↑t • ((I : ℂ) - (-1)) := by
    simp [contour_neg1_to_i, Complex.real_smul, sub_neg_eq_add]; ring
  rw [h1, show (1 : ℂ) + I = (I : ℂ) - (-1) from by ring]

/-! ### Rectangular decomposition integrals -/

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

/-! ### Truncated contour equivalence

For `δ > 0`, the diagonal integral from `-1 + δI` to `I` equals the
vertical integral from `-1 + δI` to `-1 + I` plus the horizontal integral
from `-1 + I` to `I`. All three segments lie in the upper half-plane,
so path independence (from `holomorphic_convex_primitive`) applies. -/

/-- The point `-1 + δI` lies in the upper half-plane for `δ > 0`. -/
theorem neg_one_add_delta_I_mem_uhp {δ : ℝ} (hδ : 0 < δ) :
    (-1 + ↑δ * I : ℂ) ∈ {z : ℂ | 0 < z.im} := by
  show 0 < (-1 + ↑δ * I : ℂ).im
  simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]; linarith

/-- The point `-1 + I` lies in the upper half-plane. -/
theorem neg_one_add_I_mem_uhp : (-1 + I : ℂ) ∈ {z : ℂ | 0 < z.im} := by
  show 0 < (-1 + I : ℂ).im; simp [Complex.add_im, Complex.I_im]

/-- The point `I` lies in the upper half-plane. -/
theorem I_mem_uhp : (I : ℂ) ∈ {z : ℂ | 0 < z.im} := by
  show 0 < (I : ℂ).im; simp [Complex.I_im]

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
    (∫ t in (0:ℝ)..1, F (c + t • (b - c)) * (b - c)) := by
  exact segment_integral_add_of_holomorphic
    isOpen_upperHalfPlaneSet convex_upperHalfPlaneSet
    (viazovska_integrand_left_differentiableOn r)
    (neg_one_add_delta_I_mem_uhp hδ) I_mem_uhp neg_one_add_I_mem_uhp

/-- The horizontal part of the truncated equivalence equals `I12_horiz`.
The segment from `-1+I` to `I` does not depend on `δ`. -/
theorem truncated_horiz_eq_I12_horiz (r : ℝ) :
    (∫ t in (0:ℝ)..1, viazovska_integrand_left r
      ((-1 + I : ℂ) + t • ((I : ℂ) - (-1 + I))) * ((I : ℂ) - (-1 + I))) =
    I12_horiz r := by
  rw [I12_horiz_eq_segment]

/-! ### Step 5: Cusp decay and integrand boundary behavior

To pass from the truncated contour equivalence (δ > 0) to the full equivalence
(starting at -1), we need the integrand to vanish at z = -1. This follows from
the cusp behavior of φ₀: as z → -1, the substitution w = -1/(z+1) sends
Im(w) → +∞, and the q-expansion of φ₀ shows φ₀(w) = O(e^{-2πIm(w)}).
The factor (z+1)² cancels the 1/w² from the change of variables, leaving
the integrand → 0.

We state the key cusp estimates as sorry'd lemmas (requiring q-expansion
infrastructure) and prove the contour equivalence from them. -/

/-- The integrand `viazovska_integrand_left r` vanishes at z = -1.

**Proof sketch:** Under w = -1/(z+1), as z → -1 we have Im(w) → +∞.
The q-expansion gives φ₀(w) = O(e^{2πi·w}) = O(e^{-2π·Im(w)}) → 0 as
Im(w) → +∞. Meanwhile (z+1)² → 0, exp(πirz) → exp(-πir) (bounded), and
the composition φ₀(-1/(z+1)) remains bounded (the cusp form property
(E₂E₄-E₆)²/Δ starts at q¹ in its q-expansion, so φ₀(w) → 0).
Therefore the product → 0.

**Dependency:** Requires q-expansion infrastructure for Eisenstein series
and the Dedekind discriminant, specifically that (E₂E₄-E₆)²/Δ is a
cusp form (vanishes at ∞). -/
theorem viazovska_integrand_left_tendsto_zero (r : ℝ) :
    Filter.Tendsto (viazovska_integrand_left r) (𝓝[{z | 0 < z.im}] (-1)) (𝓝 0) := by
  sorry

/-- The parameterized diagonal integrand is continuous on `[0,1]`.

The function `t ↦ F(contour_neg1_to_i(t)) · (1+I)` is continuous on `(0,1]`
(since `Im(contour_neg1_to_i(t)) = t > 0` there) and extends continuously
to `t = 0` with value `0` (since `φ₀''(-1) = 0` by definition:
`Im(-1) ≤ 0` so the `dif_neg` branch of `φ₀''` applies).

At `t = 0`: `contour_neg1_to_i(0) = -1`, so `φ₀''(-1/(−1+1)) = φ₀''(-1/0)`,
but actually `viazovska_integrand_left r (-1)` has factor `(-1+1)² = 0`,
so the integrand is `0 · exp(…) = 0` regardless.

**Dependency:** `viazovska_integrand_left_tendsto_zero` (cusp decay).
Specifically, needs `F(contour_neg1_to_i(t)) → F(-1)` as `t → 0⁺`,
which follows from the tendsto-zero estimate since `contour_neg1_to_i(t)` enters
the upper half-plane for `t > 0` and approaches `-1` as `t → 0`. -/
theorem continuousOn_diagonal_integrand (r : ℝ) :
    ContinuousOn (fun t : ℝ =>
      viazovska_integrand_left r (contour_neg1_to_i t) * (1 + I : ℂ))
      (Icc 0 1) := by
  sorry

/-- The parameterized vertical integrand is continuous on `[0,1]`.

The function `t ↦ F(-1 + tI) · I` is continuous on `(0,1]`
(since `Im(-1 + tI) = t > 0`) and at `t = 0` the integrand equals `0`
because the factor `(-1+1)² = 0` in `viazovska_integrand_left` vanishes
(here `z = -1`, so `z + 1 = 0`).

**Dependency:** Same as `continuousOn_diagonal_integrand`. -/
theorem continuousOn_vertical_integrand (r : ℝ) :
    ContinuousOn (fun t : ℝ =>
      viazovska_integrand_left r (-1 + I * ↑t) * I)
      (Icc 0 1) := by
  sorry

/-! ### Step 5b: FTC-based limit argument

The key observation is that all segment integrals equal `G(endpoint) - G(startpoint)`
for a primitive `G` on the upper half-plane. As `δ → 0`, the starting point
`-1 + δI` approaches `-1`, and `G(-1 + δI)` converges by continuity.

We work with the primitive directly to avoid dominated convergence. -/

/-- The primitive `G` of `viazovska_integrand_left r` on the upper half-plane,
whose existence follows from `holomorphic_convex_primitive`. -/
theorem exists_primitive_viazovska_integrand_left (r : ℝ) :
    ∃ G : ℂ → ℂ, ∀ z ∈ {z : ℂ | 0 < z.im},
      HasDerivAt G (viazovska_integrand_left r z) z := by
  obtain ⟨G, hG⟩ := holomorphic_convex_primitive convex_upperHalfPlaneSet
    isOpen_upperHalfPlaneSet ⟨I, I_mem_uhp⟩ (viazovska_integrand_left_differentiableOn r)
  exact ⟨G, hG⟩

/-- The truncated diagonal integral from `-1 + δI` to `I` equals `G(I) - G(-1+δI)`
for the primitive `G` of the integrand. -/
theorem truncated_diagonal_eq_primitive_sub (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovska_integrand_left r z) z)
    (δ : ℝ) (hδ : 0 < δ) :
    (∫ t in (0:ℝ)..1, viazovska_integrand_left r
      ((-1 + ↑δ * I) + t • ((I : ℂ) - (-1 + ↑δ * I))) *
        ((I : ℂ) - (-1 + ↑δ * I))) = G I - G (-1 + ↑δ * I) :=
  segment_integral_eq_sub_of_hasDerivAt isOpen_upperHalfPlaneSet convex_upperHalfPlaneSet
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
  segment_integral_eq_sub_of_hasDerivAt isOpen_upperHalfPlaneSet convex_upperHalfPlaneSet
    (neg_one_add_delta_I_mem_uhp hδ) neg_one_add_I_mem_uhp hG
    (viazovska_integrand_left_differentiableOn r).continuousOn

/-- The horizontal integral from `-1 + I` to `I` equals `G(I) - G(-1+I)`. -/
theorem horizontal_eq_primitive_sub (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovska_integrand_left r z) z) :
    I12_horiz r = G I - G (-1 + I) := by
  rw [I12_horiz_eq_segment]
  exact segment_integral_eq_sub_of_hasDerivAt isOpen_upperHalfPlaneSet convex_upperHalfPlaneSet
    neg_one_add_I_mem_uhp I_mem_uhp hG
    (viazovska_integrand_left_differentiableOn r).continuousOn

/-! ### Step 6: Full contour equivalence via primitive cancellation

The full contour equivalence `I12 = I12_vert + I12_horiz` follows from
the primitive approach: both sides equal `G(I) - lim_{δ→0} G(-1+δI)`.

The truncated versions give:
- Diagonal: `G(I) - G(-1+δI)`
- Vertical + Horizontal: `(G(-1+I) - G(-1+δI)) + (G(I) - G(-1+I)) = G(I) - G(-1+δI)`

So truncated diagonal = truncated vertical + horizontal for all δ > 0.
Taking δ → 0 and using continuity of the integrals gives the result. -/

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

/-- **Full contour equivalence**: the diagonal integral `I12` from `-1` to `I`
equals the sum of the vertical integral `I12_vert` (from `-1` to `-1+I`)
and the horizontal integral `I12_horiz` (from `-1+I` to `I`).

This is the rectangular decomposition of the original Viazovska contour integral.
The proof uses path independence on the upper half-plane (truncated at height δ)
and then takes the limit δ → 0, using the cusp decay estimate to control the
boundary behavior at z = -1.

**Proof strategy (once cusp decay is available):**
1. Split `I12 = ∫₀^δ (diag) + ∫_δ^1 (diag)` via `I12_split_at_delta`
2. Split `I12_vert = ∫₀^δ (vert) + ∫_δ^1 (vert)` via `I12_vert_split_at_delta`
3. The `∫_δ^1` parts satisfy the truncated contour equivalence (reparameterized)
4. Both `∫₀^δ` parts → 0 as δ → 0 by `continuousOn_diagonal_integrand` /
   `continuousOn_vertical_integrand` (integrand value is 0 at t=0)
5. `I12_horiz` is δ-independent (`truncated_horiz_eq_I12_horiz`)

**Dependencies:** `viazovska_integrand_left_tendsto_zero` (cusp decay),
via `continuousOn_diagonal_integrand` and `continuousOn_vertical_integrand`. -/
theorem I12_eq_rectangular (r : ℝ) : I12 r = I12_vert r + I12_horiz r := by
  sorry

/-! ### Summary of sorry dependencies

The file contains the following sorry'd lemmas:

1. **`viazovska_integrand_left_tendsto_zero`** (root dependency)
   - The integrand F(z) → 0 as z → -1 within the upper half-plane
   - Requires: q-expansion of (E₂E₄-E₆)²/Δ showing it is a cusp form
   - This is the fundamental analytic input from modular forms theory

2. **`continuousOn_diagonal_integrand`** (depends on 1)
   - Continuity of parameterized diagonal integrand on [0,1]
   - Proof: combine holomorphicity on (0,1] with the tendsto-zero limit at t=0

3. **`continuousOn_vertical_integrand`** (depends on 1)
   - Continuity of parameterized vertical integrand on [0,1]
   - Proof: same strategy as 2, different parameterization

4. **`I12_eq_rectangular`** (depends on 2, 3)
   - Full contour equivalence I12 = I12_vert + I12_horiz
   - Proof: split at δ, use truncated equivalence, take limit

Everything else in this file is **sorry-free and axiom-clean**. -/

end
