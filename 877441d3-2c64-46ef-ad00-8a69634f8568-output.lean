/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 877441d3-2c64-46ef-ad00-8a69634f8568

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma safeRotationHomotopy_deriv_cont (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ) (_hab : a < b)
    (_hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p)
    (P : Finset ℝ)
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ t ∈ Ioo a b, t ∉ P → ContinuousAt (deriv γ) t)
    (p₁ p₂ : ℝ) (_hp : p₁ < p₂) (h_subset : Ioo p₁ p₂ ⊆ Ioo a b)
    (hp_smooth : ∀ t ∈ Ioo p₁ p₂, t ∉ P) :
    ContinuousOn (fun (q : ℝ × ℝ) =>
      deriv (fun t' => safeRotationHomotopy p γ a b hγ_ne (t', q.2)) q.1)
      (Ioo p₁ p₂ ×ˢ Icc 0 1)
-/

/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import LeanModularForms.Modularforms.valence.ComplexAnalysis.PiecewiseHomotopy
import Mathlib.Analysis.InnerProductSpace.Calculus


/-!
# Winding Number = 1 via Radial Homotopy

This file provides general-purpose theorems for proving that the winding number
of a closed piecewise-C¹ curve around a point equals 1 using radial homotopy.

## Main Results

* `radial_homotopy_avoids` - The radial homotopy H(t,s) = p + c(t,s)•(γ(t)-p) avoids p
* `circleParam_winding_eq_one` - A standard circle parameterization has winding = 1
* `radialHomotopy_winding_eq` - Radial homotopy preserves winding number
* `winding_eq_one_of_wraps_once` - If γ wraps once counterclockwise, winding = 1

## Strategy

Given a closed piecewise-C¹ curve γ that avoids p:
1. Extend γ via clamping to a globally continuous γ_ext
2. Define the radial projection rc(t) = p + (γ_ext(t) - p)/‖γ_ext(t) - p‖
3. Show γ ∼ rc via radial homotopy (preserves winding)
4. Show winding(rc) = 1 using the degree of the S¹ map

All theorems are parametric and can be instantiated for any specific curve.
-/

open Complex MeasureTheory Set Filter Topology

open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Circle Parameterization -/

/-- Standard circle parameterization: z₀ + r·exp(2πi(t-a)/(b-a)). -/
def circleParam (z₀ : ℂ) (r : ℝ) (a b : ℝ) (t : ℝ) : ℂ :=
  z₀ + r * exp (2 * Real.pi * I * ((t - a) / (b - a)))

lemma circleParam_continuous (z₀ : ℂ) (r : ℝ) (a b : ℝ) :
    Continuous (circleParam z₀ r a b) := by
  unfold circleParam
  exact Continuous.add continuous_const (Continuous.mul continuous_const
    (Complex.continuous_exp.comp (Continuous.mul continuous_const
    ((continuous_ofReal.sub continuous_const).div_const _))))

lemma circleParam_closed (z₀ : ℂ) (r : ℝ) (a b : ℝ) (hab : a < b) :
    circleParam z₀ r a b a = circleParam z₀ r a b b := by
  simp only [circleParam]
  have hne : (b : ℂ) - a ≠ 0 := by
    simp [sub_ne_zero, Complex.ofReal_inj]; exact ne_of_gt hab
  have ha : ((a : ℂ) - a) / ((b : ℂ) - a) = 0 := by simp
  have hb : ((b : ℂ) - a) / ((b : ℂ) - a) = 1 := div_self hne
  simp only [ha, hb, mul_zero, exp_zero, mul_one, exp_two_pi_mul_I]

lemma circleParam_dist (z₀ : ℂ) (r : ℝ) (hr : 0 ≤ r) (a b : ℝ) (hab : a < b) (t : ℝ) :
    ‖circleParam z₀ r a b t - z₀‖ = r := by
  simp only [circleParam, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Complex.norm_exp, mul_re, ofReal_re, ofReal_im, I_re, I_im]
  ring_nf
  simp [Real.exp_zero, abs_of_nonneg hr]

/-- Derivative of circleParam. -/
lemma circleParam_deriv (z₀ : ℂ) (r : ℝ) (a b : ℝ) (hab : a < b) (t : ℝ) :
    deriv (circleParam z₀ r a b) t =
    r * (2 * Real.pi * I / (b - a)) * exp (2 * Real.pi * I * ((t - a) / (b - a))) := by
  unfold circleParam
  let f : ℝ → ℂ := fun t => 2 * Real.pi * I * (((t : ℂ) - a) / (b - a))
  have hf_deriv : HasDerivAt f (2 * Real.pi * I / (b - a)) t := by
    have h_eq : f = fun t : ℝ => (2 * Real.pi * I / (b - a)) * ((t : ℂ) - a) := by
      ext t; simp only [f]; field_simp
    rw [h_eq]
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) - (a : ℂ)) 1 t :=
      Complex.ofRealCLM.hasDerivAt.sub_const (a : ℂ)
    convert h1.const_mul (2 * Real.pi * I / (b - a)) using 1; ring
  have hexp_comp : HasDerivAt (fun t => exp (f t))
      (exp (f t) * (2 * Real.pi * I / (b - a))) t := by
    convert (hasDerivAt_exp (f t)).scomp t hf_deriv using 1
    rw [smul_eq_mul, mul_comm]
  have hmul : HasDerivAt (fun t => (r : ℂ) * exp (f t))
      ((r : ℂ) * (exp (f t) * (2 * Real.pi * I / (b - a)))) t :=
    hexp_comp.const_mul (r : ℂ)
  have hadd : HasDerivAt (fun t => z₀ + (r : ℂ) * exp (f t))
      (0 + (r : ℂ) * (exp (f t) * (2 * Real.pi * I / (b - a)))) t :=
    (hasDerivAt_const t z₀).add hmul
  simp only [zero_add] at hadd
  rw [hadd.deriv]; ring

/-- Integrand γ'/(γ-z₀) for circleParam is constant: 2πi/(b-a). -/
lemma circleParam_integrand_const (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (a b : ℝ) (hab : a < b) (t : ℝ) :
    (circleParam z₀ r a b t - z₀)⁻¹ * deriv (circleParam z₀ r a b) t =
    2 * Real.pi * I / (b - a) := by
  rw [circleParam_deriv z₀ r a b hab t]
  simp only [circleParam, add_sub_cancel_left]
  field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hr), exp_ne_zero _]

/-- The winding number of a circle around its center is 1. -/
theorem circleParam_winding_eq_one (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (a b : ℝ) (hab : a < b) :
    generalizedWindingNumber' (circleParam z₀ r a b) a b z₀ = 1 := by
  have havoids : ∀ t, ‖circleParam z₀ r a b t - z₀‖ = r := fun t =>
    circleParam_dist z₀ r (le_of_lt hr) a b hab t
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  -- For ε < r, integrand is constant 2πi/(b-a)
  have hint_const : ∀ ε > 0, ε < r →
      (∫ t in a..b, if ‖circleParam z₀ r a b t - z₀‖ > ε then
        (circleParam z₀ r a b t - z₀)⁻¹ * deriv (circleParam z₀ r a b) t else 0) =
      2 * Real.pi * I := by
    intro ε _hε_pos hε_lt_r
    have h_cond : ∀ t, ‖circleParam z₀ r a b t - z₀‖ > ε := fun t => by
      rw [havoids]; exact hε_lt_r
    have h_simp : (fun t => if ‖circleParam z₀ r a b t - z₀‖ > ε then
        (circleParam z₀ r a b t - z₀)⁻¹ * deriv (circleParam z₀ r a b) t else 0) =
        fun _ => 2 * Real.pi * I / (b - a) := by
      ext t; simp only [h_cond t, ↓reduceIte]
      exact circleParam_integrand_const z₀ r hr a b hab t
    rw [h_simp, intervalIntegral.integral_const]
    have hba_ne : (b : ℂ) - a ≠ 0 := by
      simp [sub_ne_zero, Complex.ofReal_inj]; exact ne_of_gt hab
    simp only [Complex.real_smul, Complex.ofReal_sub]; field_simp
  have hlim : limUnder (𝓝[>] (0 : ℝ)) (fun ε =>
      ∫ t in a..b, if ‖circleParam z₀ r a b t - z₀‖ > ε then
        (circleParam z₀ r a b t - z₀)⁻¹ * deriv (circleParam z₀ r a b) t else 0) =
      2 * Real.pi * I := by
    apply limUnder_eventually_eq_const
    filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
    exact hint_const ε (mem_Ioo.mp hε).1 (mem_Ioo.mp hε).2
  have h_match : (fun ε => ∫ t in a..b,
      if ‖(fun t => circleParam z₀ r a b t - z₀) t - 0‖ > ε then
        (fun x => x⁻¹) ((fun t => circleParam z₀ r a b t - z₀) t) *
        deriv (fun t => circleParam z₀ r a b t - z₀) t
      else 0) = (fun ε => ∫ t in a..b,
      if ‖circleParam z₀ r a b t - z₀‖ > ε then
        (circleParam z₀ r a b t - z₀)⁻¹ * deriv (circleParam z₀ r a b) t
      else 0) := by
    ext ε; congr 1 with t; simp only [sub_zero, deriv_sub_const]
  simp only [h_match, hlim]
  have hpi_ne : (2 : ℂ) * Real.pi * I ≠ 0 := by
    simp [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero]
  field_simp

/-! ## Clamping Infrastructure -/

/-- Clamp t to [a, b]. -/
def clampTo (a b t : ℝ) : ℝ := max a (min b t)

lemma clampTo_mem (hab : a ≤ b) (t : ℝ) : clampTo a b t ∈ Icc a b := by
  constructor
  · exact le_max_left a _
  · by_cases h : a ≤ min b t
    · rw [clampTo, max_eq_right h]; exact min_le_left b t
    · push_neg at h; rw [clampTo, max_eq_left (le_of_lt h)]; exact hab

lemma clampTo_eq_self (ht : t ∈ Icc a b) : clampTo a b t = t := by
  rw [clampTo, min_eq_right ht.2, max_eq_right ht.1]

/-- Clamped extension of a ContinuousOn function to a Continuous function. -/
lemma continuousOn_extend_clamp {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    Continuous (fun t => f (clampTo a b t)) :=
  hf.comp_continuous
    (continuous_const.max (continuous_const.min continuous_id))
    (fun t => clampTo_mem hab t)

/-- Clamped extension agrees with original on [a, b]. -/
lemma clampTo_extend_eq {f : ℝ → ℂ} {a b : ℝ} (t : ℝ) (ht : t ∈ Icc a b) :
    f (clampTo a b t) = f t := by
  rw [clampTo_eq_self ht]

/-- clampTo returns a when t < a. -/
lemma clampTo_of_lt_left (ht : t < a) (_hab : a ≤ b) : clampTo a b t = a := by
  rw [clampTo]; simp [max_eq_left, min_le_of_right_le (le_of_lt ht)]

/-- clampTo returns b when t > b. -/
lemma clampTo_of_gt_right (ht : b < t) (hab : a ≤ b) : clampTo a b t = b := by
  rw [clampTo, min_eq_left (le_of_lt ht), max_eq_right hab]

/-- clampTo returns a when t ≤ a (and a ≤ b). -/
lemma clampTo_of_le_left (ht : t ≤ a) (_hab : a ≤ b) : clampTo a b t = a := by
  rw [clampTo]; simp [max_eq_left, min_le_of_right_le ht]

/-- clampTo returns b when t ≥ b (and a ≤ b). -/
lemma clampTo_of_ge_right (ht : b ≤ t) (hab : a ≤ b) : clampTo a b t = b := by
  rw [clampTo, min_eq_left ht, max_eq_right hab]

/-! ## Radial Homotopy -/

/-- The radial homotopy avoids p. Key geometric lemma.

    H(t,s) = p + c(t,s)•(γ(t)-p) where c = (1-s) + s*r/‖γ(t)-p‖
    never equals p when γ(t) ≠ p, r > 0, s ∈ [0,1].
-/
lemma radial_homotopy_avoids (γ : ℝ → ℂ) (p : ℂ) (r : ℝ) (t s : ℝ)
    (hr : 0 < r) (hs : s ∈ Icc (0:ℝ) 1) (hne : γ t ≠ p) :
    p + ((1 - s) + s * r / ‖γ t - p‖) • (γ t - p) ≠ p := by
  intro h_eq
  have h_sub_ne : γ t - p ≠ 0 := sub_ne_zero.mpr hne
  have h_coeff : ((1 - s) + s * r / ‖γ t - p‖) • (γ t - p) = 0 := by
    have := congrArg (· - p) h_eq
    simp only [add_sub_cancel_left, sub_self] at this; exact this
  have h_coeff_zero : (1 - s) + s * r / ‖γ t - p‖ = 0 := by
    cases smul_eq_zero.mp h_coeff with
    | inl h => exact h
    | inr h => exact (h_sub_ne h).elim
  have h_norm_pos : 0 < ‖γ t - p‖ := norm_pos_iff.mpr h_sub_ne
  have h_pos : 0 < (1 - s) + s * r / ‖γ t - p‖ := by
    by_cases h : s < 1
    · linarith [div_nonneg (mul_nonneg hs.1 (le_of_lt hr)) (norm_nonneg (γ t - p))]
    · push_neg at h
      have hs1 : s = 1 := le_antisymm hs.2 h
      subst hs1; simp only [sub_self, zero_add]
      exact div_pos (mul_pos (by norm_num : (0:ℝ) < 1) hr) h_norm_pos
  linarith

/-! ## Helper Lemmas for Derivative Continuity in Radial Homotopy

These lemmas establish the joint continuity of the t-derivative of the radial homotopy
H(t,s) = p + c(t,s) • (γ(t) - p) where c(t,s) = (1-s) + s/‖γ(t) - p‖.

The t-derivative is: deriv_t H = (∂c/∂t) • (γ - p) + c • γ'
-/

/-- z(t) = γ(t) - p is continuous. -/
private lemma cont_z (γ : ℝ → ℂ) (p : ℂ) (hγ : Continuous γ) :
    Continuous (fun t => γ t - p) := hγ.sub continuous_const

/-- ‖γ(t) - p‖ is continuous. -/
private lemma cont_norm_z (γ : ℝ → ℂ) (p : ℂ) (hγ : Continuous γ) :
    Continuous (fun t => ‖γ t - p‖) := continuous_norm.comp (cont_z γ p hγ)

/-- 1/‖γ(t) - p‖ is continuous when γ avoids p. -/
private lemma cont_inv_norm (γ : ℝ → ℂ) (p : ℂ) (hγ : Continuous γ) (hne : ∀ t, γ t ≠ p) :
    Continuous (fun t => (‖γ t - p‖)⁻¹) := by
  apply Continuous.inv₀ (cont_norm_z γ p hγ)
  intro t; exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hne t))

/-- deriv γ is continuous on an open interval where γ is C¹. -/
private lemma cont_deriv_on_piece (γ : ℝ → ℂ) (p₁ p₂ : ℝ)
    (hγ_deriv_cont : ∀ t ∈ Ioo p₁ p₂, ContinuousAt (deriv γ) t) :
    ContinuousOn (deriv γ) (Ioo p₁ p₂) :=
  fun t ht => (hγ_deriv_cont t ht).continuousWithinAt

/-- The coefficient c(t,s) = (1-s) + s/‖γ(t) - p‖ is jointly continuous. -/
private lemma cont_coeff (γ : ℝ → ℂ) (p : ℂ) (hγ : Continuous γ) (hne : ∀ t, γ t ≠ p) :
    Continuous (fun (x : ℝ × ℝ) => (1 - x.2) + x.2 / ‖γ x.1 - p‖) := by
  apply Continuous.add
  · exact continuous_const.sub continuous_snd
  · apply Continuous.div continuous_snd
    · exact (cont_norm_z γ p hγ).comp continuous_fst
    · intro ⟨t, _⟩; exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hne t))

/-- ∂c/∂t is continuous on an open piece (away from partition points). -/
private lemma cont_dc_on_piece (γ : ℝ → ℂ) (p : ℂ) (p₁ p₂ : ℝ)
    (hγ : Continuous γ) (hne : ∀ t, γ t ≠ p)
    (_hγ_diff : ∀ t ∈ Ioo p₁ p₂, DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ t ∈ Ioo p₁ p₂, ContinuousAt (deriv γ) t) :
    ContinuousOn (fun (x : ℝ × ℝ) =>
      -x.2 * (Complex.re (starRingEnd ℂ (γ x.1 - p) * deriv γ x.1)) / ‖γ x.1 - p‖ ^ 3)
      (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
  apply ContinuousOn.div
  · apply ContinuousOn.mul
    · exact continuous_snd.neg.continuousOn
    · -- Re(conj(γ - p) * deriv γ) is continuous
      -- star(γ - p) is continuous (global, from γ continuous)
      have hstar : Continuous (fun t => starRingEnd ℂ (γ t - p)) :=
        continuous_star.comp (hγ.sub continuous_const)
      -- deriv γ is continuous on Ioo p₁ p₂
      have hderiv : ContinuousOn (deriv γ) (Ioo p₁ p₂) := cont_deriv_on_piece γ p₁ p₂ hγ_deriv_cont
      -- star(γ(x.1) - p) * deriv γ(x.1) is continuous on the product
      have h_prod : ContinuousOn (fun x : ℝ × ℝ => starRingEnd ℂ (γ x.1 - p) * deriv γ x.1)
          (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
        apply ContinuousOn.mul
        · exact hstar.continuousOn.comp continuousOn_fst (fun x hx => mem_univ _)
        · exact hderiv.comp continuousOn_fst (fun x hx => hx.1)
      -- Re of the product is continuous
      exact continuous_re.continuousOn.comp h_prod (fun x _ => mem_univ _)
  · apply ContinuousOn.pow
    exact (cont_norm_z γ p hγ).continuousOn.comp continuousOn_fst (fun _ h => h.1)
  · intro ⟨t, _⟩ _
    have hz : γ t - p ≠ 0 := sub_ne_zero.mpr (hne t)
    exact pow_ne_zero 3 (norm_ne_zero_iff.mpr hz)

/-! ### Helper Lemmas for Derivative of Radial Homotopy

These lemmas compute the derivative of H(t,s) = p + c(t,s) • (γ(t) - p)
with respect to t, where c(t,s) = (1-s) + s/‖γ(t) - p‖.
-/

/-- HasDerivAt for z(t) = γ(t) - p. -/
private lemma hasDerivAt_z (γ : ℝ → ℂ) (p : ℂ) (t : ℝ) (hγ : DifferentiableAt ℝ γ t) :
    HasDerivAt (fun t' => γ t' - p) (deriv γ t) t :=
  hγ.hasDerivAt.sub_const p

/-- Re(a * b) = Re(b * a) for complex numbers -/
private lemma Complex.re_mul_comm (a b : ℂ) : (a * b).re = (b * a).re := by
  simp only [Complex.mul_re]; ring

/-- HasDerivAt for ‖z(t)‖ via sqrt(‖z‖²).
    The derivative is Re⟨z, z'⟩ / ‖z‖ = inner_ℝ(z, z') / ‖z‖. -/
private lemma hasDerivAt_norm_of_hasDerivAt {z : ℝ → ℂ} {z' : ℂ} {t : ℝ}
    (hz : HasDerivAt z z' t) (hne : z t ≠ 0) :
    HasDerivAt (fun t' => ‖z t'‖) (Complex.re (starRingEnd ℂ (z t) * z') / ‖z t‖) t := by
  -- ‖z‖ = sqrt(‖z‖²)
  have h_norm_sq : HasDerivAt (fun t' => ‖z t'‖ ^ 2) (2 * @inner ℝ ℂ _ (z t) z') t := hz.norm_sq
  have h_norm_sq_ne : ‖z t‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  have h_sqrt := h_norm_sq.sqrt h_norm_sq_ne
  -- sqrt(‖z‖²) = ‖z‖
  have h_eq : ∀ u, Real.sqrt (‖z u‖ ^ 2) = ‖z u‖ := fun u => Real.sqrt_sq (norm_nonneg _)
  have h_sqrt' : HasDerivAt (fun u => ‖z u‖)
      ((2 * @inner ℝ ℂ _ (z t) z') / (2 * Real.sqrt (‖z t‖ ^ 2))) t := by
    have h_eq' : (fun u => ‖z u‖) = (fun u => Real.sqrt (‖z u‖ ^ 2)) := funext (fun u => (h_eq u).symm)
    rw [h_eq']; exact h_sqrt
  convert h_sqrt' using 1
  -- Simplify: (2 * inner) / (2 * ‖z‖) = inner / ‖z‖ = Re(conj(z) * z') / ‖z‖
  rw [h_eq t]
  have h_norm_ne : ‖z t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  field_simp [h_norm_ne]
  -- inner ℝ w z = (z * star w).re, but we have (star w * z).re
  rw [Complex.inner, Complex.re_mul_comm]

/-- HasDerivAt for 1/‖z(t)‖. -/
private lemma hasDerivAt_inv_norm {z : ℝ → ℂ} {z' : ℂ} {t : ℝ}
    (hz : HasDerivAt z z' t) (hne : z t ≠ 0) :
    HasDerivAt (fun t' => (‖z t'‖)⁻¹)
      (-Complex.re (starRingEnd ℂ (z t) * z') / ‖z t‖ ^ 3) t := by
  have h_norm_ne : ‖z t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have h_norm := hasDerivAt_norm_of_hasDerivAt hz hne
  have h_inv := h_norm.inv h_norm_ne
  convert h_inv using 1
  field_simp [h_norm_ne]

/-- HasDerivAt for c(t) = (1-s) + s/‖z(t)‖. -/
private lemma hasDerivAt_c {z : ℝ → ℂ} {z' : ℂ} {t s : ℝ}
    (hz : HasDerivAt z z' t) (hne : z t ≠ 0) :
    let dc := -s * Complex.re (starRingEnd ℂ (z t) * z') / ‖z t‖ ^ 3
    HasDerivAt (fun t' => (1 - s) + s / ‖z t'‖) dc t := by
  intro dc
  have h_inv := hasDerivAt_inv_norm hz hne
  have h_const : HasDerivAt (fun _ : ℝ => (1 : ℝ) - s) 0 t := hasDerivAt_const t (1 - s)
  have h_mul : HasDerivAt (fun t' => s * (‖z t'‖)⁻¹)
      (s * (-Complex.re (starRingEnd ℂ (z t) * z') / ‖z t‖ ^ 3)) t :=
    h_inv.const_mul s
  have h_add := h_const.add h_mul
  have h_fn_eq : (fun t' => (1 - s) + s / ‖z t'‖) = ((fun _ => 1 - s) + fun t' => s * (‖z t'‖)⁻¹) := by
    funext u; simp [div_eq_mul_inv]
  rw [h_fn_eq]
  convert h_add using 1
  simp only [dc, zero_add]; ring

/-- Product rule for scalar-vector smul: deriv(c • z) = c' • z + c • z'. -/
private lemma hasDerivAt_smul_vector (c : ℝ → ℝ) (z : ℝ → ℂ) (t : ℝ) (c' : ℝ) (z' : ℂ)
    (hc : HasDerivAt c c' t) (hz : HasDerivAt z z' t) :
    HasDerivAt (fun t' => c t' • z t') (c' • z t + c t • z') t := by
  have h := hc.smul hz
  convert h using 1
  ring

/-- The derivative formula for H(t,s) with respect to t.

    H(t, s) = p + c(t,s) • (γ(t) - p) where c(t,s) = (1-s) + s/‖γ(t) - p‖

    By the product rule for scalar-vector multiplication:
    deriv_t H = (∂c/∂t) • (γ - p) + c • γ'

    where ∂c/∂t = -s * Re⟨γ-p, γ'⟩ / ‖γ-p‖³

    **Mathematical proof:**
    1. z(t) = γ(t) - p, so z' = γ'
    2. ‖z(t)‖ is differentiable when z ≠ 0, with derivative:
       d/dt ‖z‖ = Re⟨z, z'⟩ / ‖z‖ (standard inner product formula)
    3. c(t) = (1-s) + s/‖z‖, so by chain rule:
       c'(t) = s * d/dt(‖z‖⁻¹) = -s * ‖z‖⁻² * (Re⟨z, z'⟩ / ‖z‖) = -s * Re⟨z, z'⟩ / ‖z‖³ = dc
    4. Product rule: d/dt(c • z) = c' • z + c • z'
    5. H = p + c • z, so H' = c' • z + c • z' = dc • z + c • γ'

    All components are differentiable by hypotheses.
-/
private lemma deriv_H_formula (γ : ℝ → ℂ) (p : ℂ) (t s : ℝ)
    (hγ_diff : DifferentiableAt ℝ γ t) (hne : γ t ≠ p) :
    let z := γ t - p
    let c := (1 - s) + s / ‖z‖
    let dc := -s * (Complex.re (starRingEnd ℂ z * deriv γ t)) / ‖z‖ ^ 3
    let H := fun t' => p + ((1 - s) + s / ‖γ t' - p‖) • (γ t' - p)
    deriv H t = dc • z + c • deriv γ t := by
  intro z c dc H
  have hz : z ≠ 0 := sub_ne_zero.mpr hne
  -- HasDerivAt for z(t) = γ(t) - p with derivative deriv γ t
  have hz_deriv : HasDerivAt (fun t' => γ t' - p) (deriv γ t) t :=
    hasDerivAt_z γ p t hγ_diff
  -- HasDerivAt for c(t) = (1-s) + s/‖z(t)‖ with derivative dc
  have hc_deriv : HasDerivAt (fun t' => (1 - s) + s / ‖γ t' - p‖) dc t :=
    hasDerivAt_c hz_deriv hz
  -- Product rule: deriv(c • z) = c' • z + c • z' = dc • z + c • deriv γ t
  have h_smul : HasDerivAt (fun t' => ((1 - s) + s / ‖γ t' - p‖) • (γ t' - p))
      (dc • (γ t - p) + ((1 - s) + s / ‖γ t - p‖) • deriv γ t) t :=
    hasDerivAt_smul_vector _ _ t dc (deriv γ t) hc_deriv hz_deriv
  -- H(t) = p + c(t) • z(t), so deriv H = 0 + deriv(c • z)
  have h_H : HasDerivAt H (dc • z + c • deriv γ t) t := by
    have h_const : HasDerivAt (fun _ : ℝ => p) 0 t := hasDerivAt_const t p
    have h_add := h_const.add h_smul
    simp only [zero_add] at h_add
    exact h_add
  exact h_H.deriv

/-- The main continuity lemma for deriv_t H. -/
private lemma derivH_continuousOn (γ : ℝ → ℂ) (p : ℂ) (p₁ p₂ : ℝ)
    (hγ : Continuous γ) (hne : ∀ t, γ t ≠ p)
    (hγ_diff : ∀ t ∈ Ioo p₁ p₂, DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ t ∈ Ioo p₁ p₂, ContinuousAt (deriv γ) t) :
    let H := fun (x : ℝ × ℝ) => p + ((1 - x.2) + x.2 / ‖γ x.1 - p‖) • (γ x.1 - p)
    ContinuousOn (fun (x : ℝ × ℝ) => deriv (fun t' => H (t', x.2)) x.1)
      (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
  intro H
  -- The deriv equals dc • z + c • γ' where all components are continuous
  have h_formula : ∀ x ∈ Ioo p₁ p₂ ×ˢ Icc (0:ℝ) 1,
      deriv (fun t' => H (t', x.2)) x.1 =
      (-x.2 * (Complex.re (starRingEnd ℂ (γ x.1 - p) * deriv γ x.1)) / ‖γ x.1 - p‖ ^ 3) • (γ x.1 - p) +
      ((1 - x.2) + x.2 / ‖γ x.1 - p‖) • deriv γ x.1 := by
    intro ⟨t, s⟩ ⟨ht, _⟩
    exact deriv_H_formula γ p t s (hγ_diff t ht) (hne t)
  apply ContinuousOn.congr _ h_formula
  apply ContinuousOn.add
  -- First term: dc • z
  · apply ContinuousOn.smul
    · exact cont_dc_on_piece γ p p₁ p₂ hγ hne hγ_diff hγ_deriv_cont
    · exact (hγ.sub continuous_const).continuousOn.comp continuousOn_fst (fun _ h => h.1)
  -- Second term: c • γ'
  · apply ContinuousOn.smul
    · exact (cont_coeff γ p hγ hne).continuousOn
    · exact (cont_deriv_on_piece γ p₁ p₂ hγ_deriv_cont).comp continuousOn_fst (fun _ h => h.1)

/-! ## Radial Homotopy Preserves Winding Number -/

/-- Radial homotopy from γ to its unit radial projection preserves winding number.

    Given a closed piecewise-C¹ curve γ avoiding p, the homotopy
      H(t,s) = p + ((1-s) + s/‖γ(t)-p‖)•(γ(t)-p)
    deforms γ (at s=0) to its radial projection onto S¹ (at s=1).

    The proof extends γ via clamping for global continuity,
    then verifies the PiecewiseCurvesHomotopicAvoiding conditions.
-/
theorem radialHomotopy_winding_eq (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p)
    (hγ_closed : γ a = γ b)
    (P : Finset ℝ) (hP : ∀ t ∈ P, t ∈ Ioo a b)
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ t ∈ Ioo a b, t ∉ P → ContinuousAt (deriv γ) t) :
    let rc := fun t => p + (γ t - p) / ‖γ t - p‖
    generalizedWindingNumber' γ a b p = generalizedWindingNumber' rc a b p := by
  intro rc
  -- Step 1: Extend γ via clamping
  let γ_ext : ℝ → ℂ := fun t => γ (clampTo a b t)
  have hγ_ext_cont : Continuous γ_ext := continuousOn_extend_clamp hab.le hγ_cont
  have hγ_ext_eq : ∀ t ∈ Icc a b, γ_ext t = γ t := fun t ht => clampTo_extend_eq t ht
  have hγ_ext_ne : ∀ t, γ_ext t ≠ p := fun t => hγ_ne _ (clampTo_mem hab.le t)
  have hγ_ext_closed : γ_ext a = γ_ext b := by
    simp only [γ_ext, clampTo_eq_self (left_mem_Icc.mpr hab.le),
      clampTo_eq_self (right_mem_Icc.mpr hab.le), hγ_closed]
  -- Step 2: Define radial circle and homotopy using γ_ext
  let rc_ext : ℝ → ℂ := fun t => p + (γ_ext t - p) / ‖γ_ext t - p‖
  have hRC_eq : ∀ t ∈ Icc a b, rc_ext t = rc t := by
    intro t ht; simp only [rc_ext, rc, hγ_ext_eq t ht]
  let H : ℝ × ℝ → ℂ := fun ⟨t, s⟩ =>
    p + ((1 - s) + s / ‖γ_ext t - p‖) • (γ_ext t - p)
  -- Step 3: Verify conditions
  have hH_cont : Continuous H := by
    apply Continuous.add continuous_const
    apply Continuous.smul
    · apply Continuous.add
      · exact continuous_const.sub continuous_snd
      · apply Continuous.div continuous_snd
        · exact continuous_norm.comp (hγ_ext_cont.comp continuous_fst |>.sub continuous_const)
        · intro ⟨t, _⟩; exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hγ_ext_ne t))
    · exact (hγ_ext_cont.comp continuous_fst).sub continuous_const
  have hH0 : ∀ t ∈ Icc a b, H (t, 0) = γ t := by
    intro t ht
    simp only [H, sub_zero, zero_div, add_zero, one_smul, add_sub_cancel, hγ_ext_eq t ht]
  have hH1 : ∀ t ∈ Icc a b, H (t, 1) = rc t := by
    intro t ht
    simp only [H, sub_self, zero_add]
    have hne : ‖γ_ext t - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hγ_ext_ne t))
    rw [one_div, Complex.real_smul, Complex.ofReal_inv, mul_comm, ← div_eq_mul_inv,
      hγ_ext_eq t ht]
  have hH_closed : ∀ s ∈ Icc (0:ℝ) 1, H (a, s) = H (b, s) := by
    intro s _; simp only [H, hγ_ext_closed]
  have hH_avoids : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ p := by
    intro t _ht s hs
    have h := radial_homotopy_avoids γ_ext p 1 t s (by norm_num) hs (hγ_ext_ne t)
    simp only [mul_one] at h; exact h
  -- Differentiability in t away from P
  -- Need: for t ∈ Ioo a b with t ∉ P, H is differentiable in t
  -- We include a ∪ b ∪ P in the partition to handle clamping boundaries
  let P_ext : Finset ℝ := P ∪ {a, b}
  have hH_diff : ∀ t ∈ Ioo a b, t ∉ P_ext → ∀ s ∈ Icc (0:ℝ) 1,
      DifferentiableAt ℝ (fun t' => H (t', s)) t := by
    intro t ht ht_not_P s _hs
    have ht_not_P' : t ∉ P := by
      intro hP; exact ht_not_P (Finset.mem_union_left _ hP)
    have hγ_ext_diff : DifferentiableAt ℝ γ_ext t := by
      have h_eq : γ_ext =ᶠ[𝓝 t] γ := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
        exact hγ_ext_eq u (Ioo_subset_Icc_self hu)
      exact (hγ_diff t ht ht_not_P').congr_of_eventuallyEq h_eq
    have h_sub_ne : γ_ext t - p ≠ 0 := sub_ne_zero.mpr (hγ_ext_ne t)
    have h_diff_sub : DifferentiableAt ℝ (fun t' => γ_ext t' - p) t :=
      hγ_ext_diff.sub (differentiableAt_const p)
    have h_norm_diff : DifferentiableAt ℝ (fun t' => ‖γ_ext t' - p‖) t :=
      DifferentiableAt.norm ℂ h_diff_sub h_sub_ne
    have h_coeff_diff : DifferentiableAt ℝ (fun t' => (1 - s) + s / ‖γ_ext t' - p‖) t :=
      (differentiableAt_const _).add ((differentiableAt_const _).div h_norm_diff
        (norm_ne_zero_iff.mpr h_sub_ne))
    exact (differentiableAt_const p).add (h_coeff_diff.smul h_diff_sub)
  -- Derivative continuity on pieces
  have hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P_ext) →
      ContinuousOn (fun (x : ℝ × ℝ) => deriv (fun t' => H (t', x.2)) x.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
    intro p₁ p₂ hp₁p₂ h_avoid
    -- Strategy: Use deriv_H_formula and show the formula is continuous.
    -- Key: γ_ext is continuous everywhere, and on pieces avoiding P_ext,
    -- either γ_ext = γ (C¹) or γ_ext is constant.

    -- Helper to show t ∈ P_ext when t = a or t = b
    have h_a_in_P_ext : a ∈ P_ext := Finset.mem_union_right P (by simp : a ∈ ({a, b} : Finset ℝ))
    have h_b_in_P_ext : b ∈ P_ext := Finset.mem_union_right P (by simp : b ∈ ({a, b} : Finset ℝ))

    -- First establish that deriv γ_ext is continuous on Ioo p₁ p₂
    have h_deriv_ext_cont : ContinuousOn (deriv γ_ext) (Ioo p₁ p₂) := by
      intro t ht
      -- t avoids P_ext = P ∪ {a, b}
      have h_not_P_ext := h_avoid t ht
      have h_not_a : t ≠ a := fun heq => h_not_P_ext (heq ▸ h_a_in_P_ext)
      have h_not_b : t ≠ b := fun heq => h_not_P_ext (heq ▸ h_b_in_P_ext)
      -- Case analysis: t < a, a < t < b, or b < t
      by_cases hta : t < a
      · -- t < a: γ_ext is constant = γ a in neighborhood, so deriv γ_ext = 0
        have h_deriv_zero : deriv γ_ext =ᶠ[𝓝 t] fun _ => 0 := by
          have h_eq : γ_ext =ᶠ[𝓝 t] fun _ => γ a := by
            filter_upwards [Iio_mem_nhds hta] with u hu
            simp only [γ_ext, clampTo_of_lt_left hu hab.le]
          filter_upwards [h_eq.deriv] with u hu
          rw [hu, deriv_const]
        exact h_deriv_zero.continuousAt.continuousWithinAt
      · push_neg at hta
        by_cases htb : b < t
        · -- t > b: γ_ext is constant = γ b in neighborhood, so deriv γ_ext = 0
          have h_deriv_zero : deriv γ_ext =ᶠ[𝓝 t] fun _ => 0 := by
            have h_eq : γ_ext =ᶠ[𝓝 t] fun _ => γ b := by
              filter_upwards [Ioi_mem_nhds htb] with u hu
              simp only [γ_ext, clampTo_of_gt_right hu hab.le]
            filter_upwards [h_eq.deriv] with u hu
            rw [hu, deriv_const]
          exact h_deriv_zero.continuousAt.continuousWithinAt
        · -- a ≤ t ≤ b, and t ≠ a, t ≠ b, so a < t < b
          push_neg at htb
          have ht_Ioo : t ∈ Ioo a b := ⟨lt_of_le_of_ne hta (Ne.symm h_not_a),
            lt_of_le_of_ne htb h_not_b⟩
          -- γ_ext = γ in neighborhood of t
          have h_deriv_eq : deriv γ_ext =ᶠ[𝓝 t] deriv γ := by
            have h_eq : γ_ext =ᶠ[𝓝 t] γ := by
              filter_upwards [isOpen_Ioo.mem_nhds ht_Ioo] with u hu
              exact hγ_ext_eq u (Ioo_subset_Icc_self hu)
            exact h_eq.deriv
          have h_not_P : t ∉ P := fun hP => h_not_P_ext (Finset.mem_union_left _ hP)
          exact ((hγ_deriv_cont t ht_Ioo h_not_P).congr_of_eventuallyEq h_deriv_eq).continuousWithinAt

    -- Now show the formula is continuous
    have h_formula : ∀ x ∈ Ioo p₁ p₂ ×ˢ Icc (0:ℝ) 1,
        deriv (fun t' => H (t', x.2)) x.1 =
        (-x.2 * (Complex.re (starRingEnd ℂ (γ_ext x.1 - p) * deriv γ_ext x.1)) / ‖γ_ext x.1 - p‖ ^ 3) • (γ_ext x.1 - p) +
        ((1 - x.2) + x.2 / ‖γ_ext x.1 - p‖) • deriv γ_ext x.1 := by
      intro ⟨t, s⟩ ⟨ht, _⟩
      -- Need differentiability of γ_ext at t
      have h_not_P_ext := h_avoid t ht
      have h_not_a : t ≠ a := fun heq => h_not_P_ext (heq ▸ h_a_in_P_ext)
      have h_not_b : t ≠ b := fun heq => h_not_P_ext (heq ▸ h_b_in_P_ext)
      have h_γext_diff : DifferentiableAt ℝ γ_ext t := by
        by_cases hta : t < a
        · -- t < a: γ_ext is constant
          have h_eq : γ_ext =ᶠ[𝓝 t] fun _ => γ a := by
            filter_upwards [Iio_mem_nhds hta] with u hu
            simp only [γ_ext, clampTo_of_lt_left hu hab.le]
          exact (differentiableAt_const (γ a)).congr_of_eventuallyEq h_eq
        · push_neg at hta
          by_cases htb : b < t
          · -- t > b: γ_ext is constant
            have h_eq : γ_ext =ᶠ[𝓝 t] fun _ => γ b := by
              filter_upwards [Ioi_mem_nhds htb] with u hu
              simp only [γ_ext, clampTo_of_gt_right hu hab.le]
            exact (differentiableAt_const (γ b)).congr_of_eventuallyEq h_eq
          · -- a < t < b
            push_neg at htb
            have ht_Ioo : t ∈ Ioo a b := ⟨lt_of_le_of_ne hta (Ne.symm h_not_a),
              lt_of_le_of_ne htb h_not_b⟩
            have h_eq : γ_ext =ᶠ[𝓝 t] γ := by
              filter_upwards [isOpen_Ioo.mem_nhds ht_Ioo] with u hu
              exact hγ_ext_eq u (Ioo_subset_Icc_self hu)
            have h_not_P : t ∉ P := fun hP => h_not_P_ext (Finset.mem_union_left _ hP)
            exact (hγ_diff t ht_Ioo h_not_P).congr_of_eventuallyEq h_eq
      exact deriv_H_formula γ_ext p t s h_γext_diff (hγ_ext_ne t)

    apply ContinuousOn.congr _ h_formula
    apply ContinuousOn.add
    -- First term: dc • z
    · apply ContinuousOn.smul
      · -- dc is continuous
        apply ContinuousOn.div
        · apply ContinuousOn.mul
          · exact continuous_snd.neg.continuousOn
          · have hstar : Continuous (fun t => starRingEnd ℂ (γ_ext t - p)) :=
              continuous_star.comp (hγ_ext_cont.sub continuous_const)
            have h_prod : ContinuousOn (fun x : ℝ × ℝ => starRingEnd ℂ (γ_ext x.1 - p) * deriv γ_ext x.1)
                (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
              apply ContinuousOn.mul
              · exact hstar.continuousOn.comp continuousOn_fst (fun x _ => mem_univ _)
              · exact h_deriv_ext_cont.comp continuousOn_fst (fun x hx => hx.1)
            exact continuous_re.continuousOn.comp h_prod (fun x _ => mem_univ _)
        · apply ContinuousOn.pow
          exact (continuous_norm.comp (hγ_ext_cont.sub continuous_const)).continuousOn.comp
            continuousOn_fst (fun _ h => h.1)
        · intro ⟨t, _⟩ _
          have hz : γ_ext t - p ≠ 0 := sub_ne_zero.mpr (hγ_ext_ne t)
          exact pow_ne_zero 3 (norm_ne_zero_iff.mpr hz)
      · exact (hγ_ext_cont.sub continuous_const).continuousOn.comp continuousOn_fst (fun _ h => h.1)
    -- Second term: c • γ'
    · apply ContinuousOn.smul
      · exact (cont_coeff γ_ext p hγ_ext_cont hγ_ext_ne).continuousOn
      · exact h_deriv_ext_cont.comp continuousOn_fst (fun _ h => h.1)
  -- Build homotopy and apply invariance
  have hhom : PiecewiseCurvesHomotopicAvoiding γ rc a b p P_ext :=
    ⟨H, hH_cont, hH0, hH1, hH_closed, hH_avoids, hH_diff, hH_deriv_cont⟩
  exact windingNumber_eq_of_piecewise_homotopic γ rc a b p P_ext hab hhom

/-! ## Helper: HasDerivAt for ofReal composition -/

/-- Composition of ofReal with a differentiable function preserves HasDerivAt. -/
private lemma hasDerivAt_ofReal_comp (θ : ℝ → ℝ) (t : ℝ) (hθ : DifferentiableAt ℝ θ t) :
    HasDerivAt (fun u => (θ u : ℂ)) (Complex.ofReal (deriv θ t)) t := by
  have h3f := (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).hasFDerivAt (x := θ t) |>.comp t
    hθ.hasDerivAt.hasFDerivAt
  rw [show Complex.ofRealCLM ∘ θ = fun u => (θ u : ℂ) from rfl] at h3f
  convert h3f.hasDerivAt using 1
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

/-! ## Winding Number of S¹ Curve Equals Degree -/

/-- For a C¹ curve on S¹ with angle lift θ, the winding number equals the degree.

    Given γ(t) = z₀ + exp(iθ(t)) with θ globally C¹, the integrand simplifies:
    - (γ-z₀)⁻¹ · γ' = exp(-iθ) · iθ'·exp(iθ) = iθ'
    - ∫ iθ' = i·(θ(b)-θ(a)) by FTC = i·2πn
    - Winding = (2πi)⁻¹ · 2πin = n
-/
theorem winding_of_S1_curve_eq_degree (z₀ : ℂ) (a b : ℝ) (hab : a < b)
    (n : ℤ) (θ : ℝ → ℝ) (hθ_diff : Differentiable ℝ θ)
    (hθ_deriv_cont : Continuous (deriv θ))
    (hθ_change : θ b - θ a = 2 * Real.pi * n) :
    let γ := fun t => z₀ + exp (I * (θ t : ℂ))
    generalizedWindingNumber' γ a b z₀ = n := by
  intro γ
  -- Step 1: Compute deriv γ using chain rule
  have hγ_deriv : ∀ t, HasDerivAt γ (I * (Complex.ofReal (deriv θ t)) * exp (I * (θ t : ℂ))) t := by
    intro t
    have h1 := hasDerivAt_ofReal_comp θ t (hθ_diff t)
    have h2 := h1.const_mul I
    have h3 : HasDerivAt (fun u => exp (I * (θ u : ℂ)))
        (exp (I * (θ t : ℂ)) * (I * (Complex.ofReal (deriv θ t)))) t :=
      ((hasDerivAt_exp _).scomp t h2).congr_deriv (by rw [smul_eq_mul]; ring)
    have h4 := (hasDerivAt_const t z₀).add h3
    simp only [zero_add] at h4; convert h4 using 1; ring
  -- Step 2: Integrand simplifies to I * θ'
  have h_integrand : ∀ t, (γ t - z₀)⁻¹ * deriv γ t = I * (Complex.ofReal (deriv θ t)) := by
    intro t
    have hderiv : deriv γ t = I * (Complex.ofReal (deriv θ t)) * exp (I * (θ t : ℂ)) :=
      (hγ_deriv t).deriv
    simp only [γ, add_sub_cancel_left, hderiv]
    field_simp [exp_ne_zero]
  -- Step 3: Integral = I * (θ(b) - θ(a)) by FTC
  have h_integral : ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t = 2 * Real.pi * I * n := by
    have h1 : ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t =
        ∫ t in a..b, I * (Complex.ofReal (deriv θ t)) := by
      congr 1; ext t; exact h_integrand t
    have h_pull : ∫ t in a..b, I * Complex.ofReal (deriv θ t) =
        I * ∫ t in a..b, Complex.ofReal (deriv θ t) := by
      simp_rw [← smul_eq_mul]; exact intervalIntegral.integral_smul I _
    rw [h1, h_pull]
    -- ∫ ofReal(θ') = ofReal(θ(b) - θ(a)) by FTC in ℂ
    have h_ofReal_int : IntervalIntegrable (fun t => Complex.ofReal (deriv θ t)) volume a b :=
      ⟨(hθ_deriv_cont.intervalIntegrable a b).1.ofReal,
       (hθ_deriv_cont.intervalIntegrable a b).2.ofReal⟩
    have h_ftc : ∫ t in a..b, Complex.ofReal (deriv θ t) = (θ b : ℂ) - (θ a : ℂ) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hasDerivAt_ofReal_comp θ x (hθ_diff x)) h_ofReal_int
    rw [h_ftc, show (θ b : ℂ) - (θ a : ℂ) = ((θ b - θ a : ℝ) : ℂ) from by push_cast; ring,
      hθ_change]; push_cast; ring
  -- Step 4: For ε < 1, cutoff integral = full integral
  have h_S1 : ∀ t, ‖γ t - z₀‖ = 1 := by
    intro t; simp only [γ, add_sub_cancel_left, mul_comm I]; exact norm_exp_ofReal_mul_I _
  have hint_const : ∀ ε > 0, ε < 1 →
      (∫ t in a..b, if ‖γ t - z₀‖ > ε then (γ t - z₀)⁻¹ * deriv γ t else 0) =
      2 * Real.pi * I * n := by
    intro ε _ hε_lt
    have h_cond : ∀ t, ‖γ t - z₀‖ > ε := fun t => by rw [h_S1]; exact hε_lt
    have : (fun t => if ‖γ t - z₀‖ > ε then (γ t - z₀)⁻¹ * deriv γ t else 0) =
        fun t => (γ t - z₀)⁻¹ * deriv γ t := by
      ext t; simp only [h_cond t, ↓reduceIte]
    rw [this, h_integral]
  -- Step 5: PV limit
  have hlim : limUnder (𝓝[>] (0 : ℝ)) (fun ε =>
      ∫ t in a..b, if ‖γ t - z₀‖ > ε then (γ t - z₀)⁻¹ * deriv γ t else 0) =
      2 * Real.pi * I * n := by
    apply limUnder_eventually_eq_const
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with ε hε
    exact hint_const ε (mem_Ioo.mp hε).1 (mem_Ioo.mp hε).2
  -- Step 6: Conclude
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  have h_match : (fun ε => ∫ t in a..b,
      if ‖(fun t => γ t - z₀) t - 0‖ > ε then
        (fun x => x⁻¹) ((fun t => γ t - z₀) t) * deriv (fun t => γ t - z₀) t
      else 0) = (fun ε => ∫ t in a..b,
      if ‖γ t - z₀‖ > ε then (γ t - z₀)⁻¹ * deriv γ t else 0) := by
    ext ε; congr 1 with t; simp only [sub_zero, deriv_sub_const]
  simp only [h_match, hlim]
  have hpi_ne : (2 : ℂ) * Real.pi * I ≠ 0 := by
    simp [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero]
  field_simp

/-! ## Composition: Winding = 1 from Wrapping Once -/

/-- If a closed curve avoids p, has a piecewise-C¹ angle lift with total change 2π,
    and satisfies the piecewise-C¹ conditions, then its winding number is 1.

    This combines radial homotopy invariance with a direct FTC computation
    of the PV integral on the radial projection.
-/
theorem winding_eq_one_of_wraps_once (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p)
    (hγ_closed : γ a = γ b)
    (P : Finset ℝ) (hP : ∀ t ∈ P, t ∈ Ioo a b)
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ t ∈ Ioo a b, t ∉ P → ContinuousAt (deriv γ) t)
    -- The curve wraps once counterclockwise around p with C¹ angle lift:
    (h_wraps : ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc a b) ∧
      (∀ t ∈ Ioo a b, DifferentiableAt ℝ θ t) ∧
      IntervalIntegrable (deriv θ) volume a b ∧
      (∀ t ∈ Icc a b, γ t - p = ‖γ t - p‖ * exp (I * θ t)) ∧
      θ b - θ a = 2 * Real.pi) :
    generalizedWindingNumber' γ a b p = 1 := by
  -- Step 1: Radial homotopy shows winding(γ) = winding(rc)
  let rc := fun t => p + (γ t - p) / ‖γ t - p‖
  have h_eq := radialHomotopy_winding_eq p γ a b hab hγ_cont hγ_ne hγ_closed P hP
    hγ_diff hγ_deriv_cont
  rw [h_eq]
  -- Step 2: Extract angle data
  obtain ⟨θ, hθ_cont, hθ_diff, hθ_int, hθ_eq, hθ_change⟩ := h_wraps
  -- Step 3: rc(t) = p + exp(iθ(t)) on [a,b]
  have h_rc_eq : ∀ t ∈ Icc a b, rc t = p + exp (I * θ t) := by
    intro t ht
    simp only [rc]
    have h := hθ_eq t ht
    have hne : ‖γ t - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hγ_ne t ht))
    have h_exp_norm : ‖exp (I * θ t)‖ = 1 := by
      rw [mul_comm]; exact norm_exp_ofReal_mul_I (θ t)
    rw [h]
    have h_norm : ‖(‖γ t - p‖ : ℂ) * exp (I * θ t)‖ = ‖γ t - p‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), h_exp_norm, mul_one]
    rw [h_norm]; field_simp [hne]
  -- Step 4: rc - p = exp(iθ) locally on (a,b)
  have h_rc_sub_eq : ∀ t ∈ Ioo a b,
      (fun u => rc u - p) =ᶠ[𝓝 t] (fun u => exp (I * (θ u : ℂ))) := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    have := h_rc_eq u (Ioo_subset_Icc_self hu)
    simp only [rc] at this ⊢; rw [this, add_sub_cancel_left]
  -- Step 5: ‖rc t - p‖ = 1 on [a,b]
  have h_rc_S1 : ∀ t ∈ Icc a b, ‖rc t - p‖ = 1 := by
    intro t ht
    simp only [rc, add_sub_cancel_left]
    have hne : ‖γ t - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hγ_ne t ht))
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), div_self hne]
  -- Step 6: Integrand = I * θ' on (a,b) via chain rule
  have h_integrand_eq : ∀ t ∈ Ioo a b,
      (rc t - p)⁻¹ * deriv (fun u => rc u - p) t = I * (Complex.ofReal (deriv θ t)) := by
    intro t ht
    -- Use local equality to compute deriv
    have h_deriv : deriv (fun u => rc u - p) t = deriv (fun u => exp (I * (θ u : ℂ))) t :=
      (h_rc_sub_eq t ht).deriv_eq
    -- Compute deriv of exp(I * θ) by chain rule
    have h_ofReal := hasDerivAt_ofReal_comp θ t (hθ_diff t ht)
    have h_mul_I := h_ofReal.const_mul I
    have h_exp : HasDerivAt (fun u => exp (I * (θ u : ℂ)))
        (exp (I * (θ t : ℂ)) * (I * (Complex.ofReal (deriv θ t)))) t :=
      ((hasDerivAt_exp _).scomp t h_mul_I).congr_deriv (by rw [smul_eq_mul]; ring)
    rw [h_deriv, h_exp.deriv]
    -- rc t - p = exp(I * θ t) on [a,b]
    have h_val : rc t - p = exp (I * (θ t : ℂ)) := by
      rw [h_rc_eq t (Ioo_subset_Icc_self ht), add_sub_cancel_left]
    rw [h_val]; field_simp [exp_ne_zero]
  -- Step 7: Full integral = 2πi by FTC
  have h_integral :
      ∫ t in a..b, (rc t - p)⁻¹ * deriv (fun u => rc u - p) t = 2 * Real.pi * I := by
    -- Rewrite integrand a.e. using h_integrand_eq
    have h1 : ∫ t in a..b, (rc t - p)⁻¹ * deriv (fun u => rc u - p) t =
        ∫ t in a..b, I * Complex.ofReal (deriv θ t) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton b)] with t hne hmem
      rw [uIoc_of_le hab.le] at hmem
      exact h_integrand_eq t ⟨hmem.1, lt_of_le_of_ne hmem.2 (Set.notMem_singleton_iff.mp hne)⟩
    have h_pull : ∫ t in a..b, I * Complex.ofReal (deriv θ t) =
        I * ∫ t in a..b, Complex.ofReal (deriv θ t) := by
      simp_rw [← smul_eq_mul]; exact intervalIntegral.integral_smul I _
    rw [h1, h_pull]
    -- FTC in ℂ: ∫ ofReal(θ') = ofReal(θ(b)) - ofReal(θ(a))
    have h_ofReal_int : IntervalIntegrable (fun t => Complex.ofReal (deriv θ t)) volume a b :=
      ⟨hθ_int.1.ofReal, hθ_int.2.ofReal⟩
    have h_ftc : ∫ t in a..b, Complex.ofReal (deriv θ t) = (θ b : ℂ) - (θ a : ℂ) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le
        (Complex.continuous_ofReal.comp_continuousOn hθ_cont)
        (fun x hx => hasDerivAt_ofReal_comp θ x (hθ_diff x hx)) h_ofReal_int
    rw [h_ftc, show (θ b : ℂ) - (θ a : ℂ) = ((θ b - θ a : ℝ) : ℂ) from by push_cast; ring,
      hθ_change]; push_cast; ring
  -- Step 8: For ε < 1, cutoff integral = full integral
  have hint_const : ∀ ε > 0, ε < 1 →
      (∫ t in a..b, if ‖(rc t - p) - 0‖ > ε then
        (rc t - p)⁻¹ * deriv (fun u => rc u - p) t else 0) =
      2 * Real.pi * I := by
    intro ε _ hε_lt
    have h_cond : ∀ t ∈ uIcc a b, ‖(rc t - p) - 0‖ > ε := by
      intro t ht; rw [sub_zero]; rw [uIcc_of_le hab.le] at ht
      rw [h_rc_S1 t ht]; exact hε_lt
    have : ∀ t ∈ uIcc a b,
        (if ‖(rc t - p) - 0‖ > ε then
          (rc t - p)⁻¹ * deriv (fun u => rc u - p) t else 0) =
        (rc t - p)⁻¹ * deriv (fun u => rc u - p) t := by
      intro t ht; rw [if_pos (h_cond t ht)]
    rw [intervalIntegral.integral_congr this, h_integral]
  -- Step 9: PV limit = 2πi
  have hlim : limUnder (𝓝[>] (0 : ℝ)) (fun ε =>
      ∫ t in a..b, if ‖(rc t - p) - 0‖ > ε then
        (rc t - p)⁻¹ * deriv (fun u => rc u - p) t else 0) =
      2 * Real.pi * I := by
    apply limUnder_eventually_eq_const
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with ε hε
    exact hint_const ε (mem_Ioo.mp hε).1 (mem_Ioo.mp hε).2
  -- Step 10: Conclude winding = 1
  unfold generalizedWindingNumber'
  suffices h_cpv : cauchyPrincipalValue' (·⁻¹) (fun t => rc t - p) a b 0 =
      2 * Real.pi * I by
    rw [h_cpv]; field_simp
  unfold cauchyPrincipalValue'
  convert hlim using 1

/-! ## Winding = 1 via Homotopy to Circle (No Angle Lift) -/

/-- If γ is piecewise-homotopic to a circle around p, then winding(γ) = 1.

    This is the "pure homotopy" approach: we don't need angle lifts or argument change.
    Just compose homotopies: γ → radialCircle → circleParam → winding = 1.
-/
theorem winding_eq_one_of_homotopic_to_circle (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ) (P : Finset ℝ)
    (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p)
    (hγ_closed : γ a = γ b)
    (hhom : PiecewiseCurvesHomotopicAvoiding γ (circleParam p 1 a b) a b p P) :
    generalizedWindingNumber' γ a b p = 1 := by
  have h_eq := windingNumber_eq_of_piecewise_homotopic γ (circleParam p 1 a b) a b p P hab hhom
  have h_circle := circleParam_winding_eq_one p 1 (by norm_num : (0:ℝ) < 1) a b hab
  rw [h_eq, h_circle]

/-!
## Radial-to-Circle Homotopy Construction

For the fundamental domain boundary, we construct a homotopy to the circle via:
1. Radial homotopy: γ → rc (radial projection to S¹)
2. S¹ rotation homotopy: rc → circleParam

Both homotopies stay away from p (the center), so they can be composed.
-/

/-- The radial projection onto S¹ centered at p. -/
def radialProjection (p : ℂ) (γ : ℝ → ℂ) (hγ_ne : ∀ t, γ t ≠ p) : ℝ → ℂ :=
  fun t => p + (γ t - p) / ‖γ t - p‖

/-- The radial projection lies on the unit circle around p. -/
lemma radialProjection_on_S1 (p : ℂ) (γ : ℝ → ℂ) (hγ_ne : ∀ t, γ t ≠ p) (t : ℝ) :
    ‖radialProjection p γ hγ_ne t - p‖ = 1 := by
  simp only [radialProjection, add_sub_cancel_left]
  have h_ne : γ t - p ≠ 0 := sub_ne_zero.mpr (hγ_ne t)
  have h_norm_ne : ‖γ t - p‖ ≠ 0 := norm_ne_zero_iff.mpr h_ne
  rw [norm_div]
  have h_norm_ofReal : ‖(‖γ t - p‖ : ℂ)‖ = ‖γ t - p‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [h_norm_ofReal, div_self h_norm_ne]

/-- Rotation factor for safe rotation homotopy.

    rot(s) = (1 - s) + s·I

    This is never zero for s ∈ [0,1]:
    - At s = 0: rot(0) = 1
    - At s = 1: rot(1) = I
    - For s ∈ (0,1): real part (1-s) > 0 or imaginary part s > 0
-/
def rotFactor (s : ℝ) : ℂ := (1 - s) + s * Complex.I

/-- The rotation factor is never zero for s ∈ [0,1]. -/
lemma rotFactor_ne_zero (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : rotFactor s ≠ 0 := by
  simp only [rotFactor, ne_eq]
  intro h
  -- If (1-s) + s*I = 0, then taking the norm squared: (1-s)² + s² = 0
  -- This is impossible unless both 1-s = 0 and s = 0, which contradicts.
  have h_normSq : Complex.normSq ((1 - s : ℂ) + s * Complex.I) = 0 := by
    rw [h]; exact Complex.normSq_zero
  have h_convert : (1 - s : ℂ) + s * Complex.I = ↑(1 - s) + ↑s * Complex.I := by simp
  rw [h_convert, Complex.normSq_add_mul_I] at h_normSq
  -- (1-s)² + s² = 0 implies 1-s = 0 and s = 0, contradiction
  have h1 : (1 - s) ^ 2 ≥ 0 := sq_nonneg _
  have h2 : s ^ 2 ≥ 0 := sq_nonneg _
  have h_both : (1 - s) ^ 2 = 0 ∧ s ^ 2 = 0 := by
    constructor <;> nlinarith
  have h_real : 1 - s = 0 := pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h_both.1
  have h_imag : s = 0 := pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h_both.2
  linarith

/-- The norm of the rotation factor. -/
lemma rotFactor_norm (s : ℝ) : ‖rotFactor s‖ = Real.sqrt ((1 - s)^2 + s^2) := by
  simp only [rotFactor]
  -- ‖(1-s) + s*I‖ = sqrt(normSq((1-s) + s*I)) = sqrt((1-s)² + s²)
  show Real.sqrt (Complex.normSq ((1 - s : ℂ) + s * Complex.I)) = Real.sqrt ((1 - s)^2 + s^2)
  congr 1
  have h : (1 - s : ℂ) + s * Complex.I = ↑(1 - s) + ↑s * Complex.I := by simp
  rw [h, Complex.normSq_add_mul_I]

/-- The norm of the rotation factor is positive for s ∈ [0,1]. -/
lemma rotFactor_norm_pos (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : 0 < ‖rotFactor s‖ :=
  norm_pos_iff.mpr (rotFactor_ne_zero s hs)

/-- Safe rotation homotopy from radialCircle to i·radialCircle.

    At each t:
    - u(t) = radialCircle(t) - p is a unit vector

    The homotopy is: H₁(t, s) = p + rot(s) * u(t) / ‖rot(s)‖

    where rot(s) = (1-s) + s·I.

    At s = 0: H₁(t, 0) = p + u(t) = radialCircle(t)
    At s = 1: H₁(t, 1) = p + I * u(t)

    This homotopy is safe because rot(s) ≠ 0 for all s ∈ [0,1],
    avoiding the antipodal condition issue.
-/
def safeRotationHomotopy (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p) : ℝ × ℝ → ℂ :=
  fun ⟨t, s⟩ =>
    let u := (γ t - p) / ‖γ t - p‖
    p + rotFactor s * u / ‖rotFactor s‖

/-- The safe rotation homotopy is continuous. -/
lemma safeRotationHomotopy_continuous (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_cont : ContinuousOn γ (Icc a b)) (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p) :
    ContinuousOn (safeRotationHomotopy p γ a b hγ_ne) (Icc a b ×ˢ Icc 0 1) := by
  unfold safeRotationHomotopy
  have h_rot_cont : Continuous rotFactor := by
    unfold rotFactor
    exact (continuous_const.sub continuous_ofReal).add
      (continuous_ofReal.mul continuous_const)
  apply ContinuousOn.add continuousOn_const
  apply ContinuousOn.div
  · -- rot(s) * u(t) is continuous
    apply ContinuousOn.mul
    · -- rotFactor is continuous in s
      exact h_rot_cont.continuousOn.comp continuousOn_snd (mapsTo_univ _ _)
    · -- u(t) = (γ(t) - p) / ‖γ(t) - p‖ is continuous on Icc a b
      apply ContinuousOn.div
      · exact (hγ_cont.sub continuousOn_const).comp continuousOn_fst (fun x hx => hx.1)
      · have h_norm_cont : ContinuousOn (fun t => (‖γ t - p‖ : ℂ)) (Icc a b) :=
          continuous_ofReal.comp_continuousOn
            (continuous_norm.comp_continuousOn (hγ_cont.sub continuousOn_const))
        exact h_norm_cont.comp continuousOn_fst (fun x hx => hx.1)
      · intro ⟨t, s⟩ ⟨ht, _⟩
        simp only [Complex.ofReal_ne_zero]
        exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hγ_ne t ht))
  · -- ‖rot(s)‖ is continuous as a complex number
    have h_norm_rot : Continuous (fun s => (‖rotFactor s‖ : ℂ)) :=
      continuous_ofReal.comp (continuous_norm.comp h_rot_cont)
    exact h_norm_rot.continuousOn.comp continuousOn_snd (mapsTo_univ _ _)
  · intro ⟨t, s⟩ ⟨_, hs⟩
    simp only [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr (rotFactor_ne_zero s hs)

/-- The safe rotation homotopy at s = 0 equals radialCircle. -/
lemma safeRotationHomotopy_at_zero (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p) (t : ℝ) (ht : t ∈ Icc a b) :
    safeRotationHomotopy p γ a b hγ_ne (t, 0) = p + (γ t - p) / ‖γ t - p‖ := by
  simp only [safeRotationHomotopy, rotFactor]
  -- At s = 0: rot(0) = (1 - 0) + 0*I = 1, ‖1‖ = 1
  norm_num

/-- The safe rotation homotopy at s = 1 equals p + I · u(t). -/
lemma safeRotationHomotopy_at_one (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p) (t : ℝ) (ht : t ∈ Icc a b) :
    safeRotationHomotopy p γ a b hγ_ne (t, 1) =
      p + Complex.I * ((γ t - p) / ‖γ t - p‖) := by
  simp only [safeRotationHomotopy, rotFactor]
  -- At s = 1: rot(1) = (1 - 1) + 1*I = I, ‖I‖ = 1
  norm_num [Complex.normSq_I]

/-- The safe rotation homotopy preserves closed curves. -/
lemma safeRotationHomotopy_closed (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p) (hγ_closed : γ a = γ b)
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    safeRotationHomotopy p γ a b hγ_ne (a, s) = safeRotationHomotopy p γ a b hγ_ne (b, s) := by
  simp only [safeRotationHomotopy]
  rw [hγ_closed]

/-- The safe rotation homotopy avoids p. -/
lemma safeRotationHomotopy_avoids (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p)
    (t : ℝ) (ht : t ∈ Icc a b) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    safeRotationHomotopy p γ a b hγ_ne (t, s) ≠ p := by
  simp only [safeRotationHomotopy]
  intro heq
  have h_sub : rotFactor s * ((γ t - p) / ‖γ t - p‖) / (‖rotFactor s‖ : ℂ) = 0 := by
    have := add_right_eq_self.mp heq; exact this
  rw [div_eq_zero_iff] at h_sub
  cases h_sub with
  | inl h =>
    rw [mul_eq_zero] at h
    cases h with
    | inl h_rot => exact rotFactor_ne_zero s hs h_rot
    | inr h_u =>
      rw [div_eq_zero_iff] at h_u
      cases h_u with
      | inl h_num =>
        have := sub_ne_zero.mpr (hγ_ne t ht)
        exact this h_num
      | inr h_denom =>
        have h_ne := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hγ_ne t ht))
        simp only [Complex.ofReal_eq_zero] at h_denom
        exact h_ne h_denom
  | inr h =>
    have h_ne := rotFactor_norm_pos s hs
    simp only [Complex.ofReal_eq_zero] at h
    linarith

/-- The safe rotation homotopy is differentiable in t away from partition points. -/
lemma safeRotationHomotopy_diff (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p)
    (P : Finset ℝ)
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (t : ℝ) (ht : t ∈ Ioo a b) (ht_not_P : t ∉ P) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    DifferentiableAt ℝ (fun t' => safeRotationHomotopy p γ a b hγ_ne (t', s)) t := by
  -- H(t, s) = p + rot(s) * u(t) / ‖rot(s)‖ where u(t) = (γ(t) - p) / ‖γ(t) - p‖
  -- rot(s) is constant in t, so we just need u(t) differentiable
  simp only [safeRotationHomotopy]
  -- p is constant
  apply DifferentiableAt.add (differentiableAt_const p)
  -- rot(s) / ‖rot(s)‖ is constant in t
  have h_rot_ne : (‖rotFactor s‖ : ℂ) ≠ 0 := by
    simp only [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr (rotFactor_ne_zero s hs)
  apply DifferentiableAt.div_const
  apply DifferentiableAt.const_mul
  -- u(t) = (γ(t) - p) / ‖γ(t) - p‖ is differentiable
  have hγ_diff_at := hγ_diff t ht ht_not_P
  have h_sub_diff : DifferentiableAt ℝ (fun t' => γ t' - p) t :=
    hγ_diff_at.sub (differentiableAt_const p)
  have h_sub_ne : γ t - p ≠ 0 := sub_ne_zero.mpr (hγ_ne t (Ioo_subset_Icc_self ht))
  -- The denominator ‖γ t' - p‖ needs to be viewed as a ℂ-valued function
  have h_norm_diff : DifferentiableAt ℝ (fun t' => (‖γ t' - p‖ : ℂ)) t :=
    Complex.ofRealCLM.differentiableAt.comp t (DifferentiableAt.norm ℂ h_sub_diff h_sub_ne)
  have h_norm_ne : (‖γ t - p‖ : ℂ) ≠ 0 := by
    simp only [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr h_sub_ne
  exact h_sub_diff.div h_norm_diff h_norm_ne

/-! ### Helper lemmas for derivative continuity -/

/-- The rotation factor is continuous. -/
lemma rotFactor_continuous : Continuous rotFactor := by
  unfold rotFactor
  exact (continuous_const.sub continuous_ofReal).add (continuous_ofReal.mul continuous_const)

/-- The normalized rotation factor is continuous on [0,1]. -/
lemma rotFactor_unit_continuousOn : ContinuousOn (fun s => rotFactor s / ‖rotFactor s‖) (Icc 0 1) := by
  apply ContinuousOn.div rotFactor_continuous.continuousOn
  · exact Complex.ofRealCLM.continuous.comp_continuousOn (continuous_norm.comp rotFactor_continuous).continuousOn
  · intro s hs
    simp only [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr (rotFactor_ne_zero s hs)

/-- The unit direction u(t) = (γ(t) - p) / ‖γ(t) - p‖ is continuous where γ is continuous. -/
lemma unitDirection_continuousOn (p : ℂ) (γ : ℝ → ℂ) (S : Set ℝ)
    (hγ_cont : ContinuousOn γ S) (hγ_ne : ∀ t ∈ S, γ t ≠ p) :
    ContinuousOn (fun t => (γ t - p) / ‖γ t - p‖) S := by
  apply ContinuousOn.div (hγ_cont.sub continuousOn_const)
  · exact Complex.ofRealCLM.continuous.comp_continuousOn (continuous_norm.comp_continuousOn (hγ_cont.sub continuousOn_const))
  · intro t ht
    simp only [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hγ_ne t ht))

/-- The t-derivative of the safe rotation homotopy is continuous on pieces.

    Technical lemma: The derivative of H(t, s) = p + rot(s)/‖rot(s)‖ * u(t)
    with respect to t is continuous on Ioo p₁ p₂ ×ˢ Icc 0 1.

    The proof uses:
    1. The derivative equals rot(s)/‖rot(s)‖ * deriv u(t)
    2. rot(s)/‖rot(s)‖ is continuous in s
    3. deriv u(t) is continuous in t (u is C¹ when γ is C¹ and γ ≠ p)
    4. Products of continuous functions are continuous

    This is standard calculus but requires careful handling of the C¹ quotient rule. -/
lemma safeRotationHomotopy_deriv_cont (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ) (_hab : a < b)
    (_hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p)
    (P : Finset ℝ)
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ t ∈ Ioo a b, t ∉ P → ContinuousAt (deriv γ) t)
    (p₁ p₂ : ℝ) (_hp : p₁ < p₂) (h_subset : Ioo p₁ p₂ ⊆ Ioo a b)
    (hp_smooth : ∀ t ∈ Ioo p₁ p₂, t ∉ P) :
    ContinuousOn (fun (q : ℝ × ℝ) =>
      deriv (fun t' => safeRotationHomotopy p γ a b hγ_ne (t', q.2)) q.1)
      (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
  -- H(t, s) = p + rot(s)/‖rot(s)‖ * u(t) where u(t) = (γ(t) - p)/‖γ(t) - p‖
  -- The t-derivative is: rot(s)/‖rot(s)‖ * deriv u(t)
  -- We show this is jointly continuous in (t, s).
  let u := fun t' => (γ t' - p) / (‖γ t' - p‖ : ℂ)
  -- Step 1: Show deriv u is continuous on Ioo p₁ p₂
  -- We use that u = (γ - p)/‖γ - p‖ is C¹ when γ is C¹ and γ ≠ p.
  --
  -- Technical proof: u is a composition of C¹ functions (γ is C¹ on pieces, norm is
  -- smooth away from zero, division is smooth when denominator is nonzero).
  -- The derivative formula is:
  --   u'(t) = γ'(t)/‖γ(t)-p‖ - (γ(t)-p) · Re⟨γ(t)-p, γ'(t)⟩ / ‖γ(t)-p‖³
  -- which is continuous when γ, γ' are continuous and γ(t) ≠ p.
  have h_deriv_u_cont_on : ContinuousOn (deriv u) (Ioo p₁ p₂) := by
    apply continuousOn_of_forall_continuousAt
    intro t' ht'
    have h_t'_in_ab_open : t' ∈ Ioo a b := h_subset ht'
    have h_t'_in_ab : t' ∈ Icc a b := Ioo_subset_Icc_self h_t'_in_ab_open
    have h_γ_ne' : γ t' ≠ p := hγ_ne t' h_t'_in_ab
    have h_sub_ne' : γ t' - p ≠ 0 := sub_ne_zero.mpr h_γ_ne'
    have h_norm_ne' : ‖γ t' - p‖ ≠ 0 := norm_ne_zero_iff.mpr h_sub_ne'
    have _h_γ'_cont_at : ContinuousAt (deriv γ) t' := hγ_deriv_cont t' h_t'_in_ab_open (hp_smooth t' ht')
    -- The proof requires showing u is C¹, which follows from the quotient rule
    -- for C¹ functions. This is technical but standard.
    -- We use: γ is C¹ at t' (diff in nhd + deriv continuous), hence γ - p is C¹,
    -- ‖·‖ is C∞ away from 0, so ‖γ - p‖ is C¹, and the quotient is C¹.
    -- Since γ is differentiable at t', and the norm is continuous, the derivative of the norm component is continuous. Therefore, the derivative of u is continuous at t'.
    have h_deriv_u_cont : ContinuousAt (fun t' => (1 / ‖γ t' - p‖) • deriv γ t' - (γ t' - p) • (deriv (fun t' => ‖γ t' - p‖) t') / ‖γ t' - p‖ ^ 2) t' := by
      have h_deriv_norm_cont : ContinuousAt (fun t' => (Complex.re (starRingEnd ℂ (γ t' - p) * deriv γ t')) / ‖γ t' - p‖) t' := by
        refine' ContinuousAt.div _ _ _;
        · exact ContinuousAt.comp ( Complex.continuous_re.continuousAt ) ( ContinuousAt.mul ( Complex.continuous_conj.continuousAt.comp ( ContinuousAt.sub ( _hγ_cont.continuousAt ( Icc_mem_nhds h_t'_in_ab_open.1 h_t'_in_ab_open.2 ) ) continuousAt_const ) ) _h_γ'_cont_at );
        · exact ContinuousAt.norm ( ContinuousAt.sub ( _hγ_cont.continuousAt ( Icc_mem_nhds h_t'_in_ab_open.1 h_t'_in_ab_open.2 ) ) continuousAt_const );
        · assumption;
      have h_deriv_norm_eq : ∀ t' ∈ Set.Ioo a b, t' ∉ P → deriv (fun t' => ‖γ t' - p‖) t' = (Complex.re (starRingEnd ℂ (γ t' - p) * deriv γ t')) / ‖γ t' - p‖ := by
        intro t' ht' ht'_not_P; exact (by
        convert HasDerivAt.deriv ( hasDerivAt_norm_of_hasDerivAt ( hasDerivAt_z γ p t' ( hγ_diff t' ht' ht'_not_P ) ) ( sub_ne_zero_of_ne ( hγ_ne t' <| Set.Ioo_subset_Icc_self ht' ) ) ) using 1);
      refine' ContinuousAt.sub _ _;
      · exact ContinuousAt.smul ( ContinuousAt.div continuousAt_const ( ContinuousAt.norm ( ContinuousAt.sub ( _hγ_cont.continuousAt ( Icc_mem_nhds h_t'_in_ab_open.1 h_t'_in_ab_open.2 ) ) continuousAt_const ) ) h_norm_ne' ) _h_γ'_cont_at;
      · refine' ContinuousAt.div _ _ _;
        · refine' ContinuousAt.smul _ _;
          · exact ContinuousAt.sub ( _hγ_cont.continuousAt ( Icc_mem_nhds h_t'_in_ab_open.1 h_t'_in_ab_open.2 ) ) continuousAt_const;
          · exact Complex.continuous_ofReal.continuousAt.comp ( h_deriv_norm_cont.congr ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhds ht'.1 ht'.2 ) fun x hx => by rw [ h_deriv_norm_eq x ( h_subset hx ) ( hp_smooth x hx ) ] ) );
        · exact ContinuousAt.pow ( Complex.continuous_ofReal.continuousAt.comp <| ContinuousAt.norm <| ContinuousAt.sub ( _hγ_cont.continuousAt <| Icc_mem_nhds h_t'_in_ab_open.1 h_t'_in_ab_open.2 ) continuousAt_const ) _;
        · exact pow_ne_zero _ ( Complex.ofReal_ne_zero.mpr h_norm_ne' );
    convert h_deriv_u_cont.congr _ using 1;
    filter_upwards [ IsOpen.mem_nhds ( isOpen_Ioo ) ht' ] with t' ht';
    convert HasDerivAt.deriv ( HasDerivAt.div ( HasDerivAt.sub ( hγ_diff t' ( h_subset ht' ) ( hp_smooth t' ht' ) |> DifferentiableAt.hasDerivAt ) ( hasDerivAt_const _ _ ) ) ( HasDerivAt.ofReal_comp ( hasDerivAt_deriv_iff.mpr _ ) ) _ ) |> Eq.symm using 1;
    · simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, sub_mul, mul_sub, pow_two, ne_of_gt ( norm_pos_iff.mpr ( sub_ne_zero.mpr ( hγ_ne t' ( h_subset ht' |> Set.Ioo_subset_Icc_self ) ) ) ) ];
    · exact DifferentiableAt.norm ℝ ( hγ_diff t' ( h_subset ht' ) ( hp_smooth t' ht' ) |> DifferentiableAt.sub <| differentiableAt_const _ ) <| sub_ne_zero_of_ne <| hγ_ne t' <| h_subset ht' |> fun h => ⟨ h.1.le, h.2.le ⟩;
    · exact mod_cast norm_ne_zero_iff.mpr ( sub_ne_zero.mpr ( hγ_ne t' ( h_subset ht' |> Set.Ioo_subset_Icc_self ) ) )
  -- Step 2: Use h_deriv_u_cont_on to show the full derivative is continuous
  -- The derivative equals r(s) * deriv u(t), a product of continuous functions.
  refine' ContinuousOn.congr _ _;
  use fun q => ( rotFactor q.2 / ‖rotFactor q.2‖ ) * deriv u q.1;
  · refine' ContinuousOn.mul _ ( h_deriv_u_cont_on.comp continuousOn_fst _ );
    · refine' ContinuousOn.div _ _ _;
      · exact Continuous.continuousOn ( by continuity );
      · exact Complex.continuous_ofReal.comp_continuousOn ( Continuous.continuousOn ( by continuity ) );
      · simp +zetaDelta at *;
        exact fun t s ht₁ ht₂ hs₁ hs₂ => rotFactor_ne_zero s ⟨ hs₁, hs₂ ⟩;
    · exact fun x hx => hx.1;
  · field_simp;
    intro q hq; unfold safeRotationHomotopy; aesop;

/- Aristotle failed to find a proof. -/
/-- Safe rotation homotopy gives a piecewise homotopy from rc to I·rc. -/
lemma safeRotationHomotopy_piecewise_avoiding (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p)
    (hγ_closed : γ a = γ b)
    (P : Finset ℝ) (hP : ∀ t ∈ P, t ∈ Ioo a b)
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ t ∈ Ioo a b, t ∉ P → ContinuousAt (deriv γ) t) :
    let rc := fun t => p + (γ t - p) / ‖γ t - p‖
    let rc_rot := fun t => p + Complex.I * ((γ t - p) / ‖γ t - p‖)
    PiecewiseCurvesHomotopicAvoiding rc rc_rot a b p P := by
  intro rc rc_rot
  -- Define a clamped version that's continuous everywhere
  let clamp_t := fun t => max a (min b t)
  let clamp_s := fun s => max (0:ℝ) (min 1 s)
  let H := fun (ts : ℝ × ℝ) => safeRotationHomotopy p γ a b hγ_ne (clamp_t ts.1, clamp_s ts.2)
  -- Key: clamping is identity on Icc a b × Icc 0 1
  have h_clamp_t_id : ∀ t ∈ Icc a b, clamp_t t = t := by
    intro t ht
    simp only [clamp_t]
    -- min b t = t when t ≤ b, then max a t = t when a ≤ t
    rw [min_eq_right ht.2, max_eq_right ht.1]
  have h_clamp_s_id : ∀ s ∈ Icc (0:ℝ) 1, clamp_s s = s := by
    intro s hs
    simp only [clamp_s]
    rw [min_eq_right hs.2, max_eq_right hs.1]
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. Continuity via clamping
  · -- H = safeRotationHomotopy ∘ (clamp_t, clamp_s)
    -- clamp functions are continuous
    have hclamp_t_cont : Continuous clamp_t := by
      apply Continuous.max continuous_const
      exact Continuous.min continuous_const continuous_id
    have hclamp_s_cont : Continuous clamp_s := by
      apply Continuous.max continuous_const
      exact Continuous.min continuous_const continuous_id
    -- The clamped point is always in the domain Icc a b ×ˢ Icc 0 1
    have h_clamp_range : ∀ ts : ℝ × ℝ, (clamp_t ts.1, clamp_s ts.2) ∈ Icc a b ×ˢ Icc (0:ℝ) 1 := by
      intro ⟨t, s⟩
      simp only [Set.mem_prod, Set.mem_Icc, clamp_t, clamp_s]
      refine ⟨⟨le_max_left a _, ?_⟩, ⟨le_max_left 0 _, ?_⟩⟩
      · -- max a (min b t) ≤ b
        exact max_le hab.le (min_le_left b t)
      · -- max 0 (min 1 s) ≤ 1
        exact max_le (by norm_num : (0:ℝ) ≤ 1) (min_le_left 1 s)
    -- Compose: continuous clamp → ContinuousOn domain → Continuous
    have h_pair_cont : Continuous (fun ts : ℝ × ℝ => (clamp_t ts.1, clamp_s ts.2)) :=
      hclamp_t_cont.fst'.prod_mk (hclamp_s_cont.comp continuous_snd)
    exact (safeRotationHomotopy_continuous p γ a b hγ_cont hγ_ne).comp_continuous
      h_pair_cont h_clamp_range
  -- 2. H(t, 0) = rc(t) for t ∈ Icc a b
  · intro t ht
    simp only [H, h_clamp_t_id t ht, h_clamp_s_id 0 (by simp : (0:ℝ) ∈ Icc 0 1)]
    exact safeRotationHomotopy_at_zero p γ a b hγ_ne t ht
  -- 3. H(t, 1) = rc_rot(t) for t ∈ Icc a b
  · intro t ht
    simp only [H, h_clamp_t_id t ht, h_clamp_s_id 1 (by simp : (1:ℝ) ∈ Icc 0 1)]
    exact safeRotationHomotopy_at_one p γ a b hγ_ne t ht
  -- 4. H(a, s) = H(b, s) (closed) for s ∈ Icc 0 1
  · intro s hs
    simp only [H, h_clamp_t_id a (left_mem_Icc.mpr hab.le),
      h_clamp_t_id b (right_mem_Icc.mpr hab.le), h_clamp_s_id s hs]
    exact safeRotationHomotopy_closed p γ a b hγ_ne hγ_closed s hs
  -- 5. H avoids p
  · intro t ht s hs
    simp only [H, h_clamp_t_id t ht, h_clamp_s_id s hs]
    exact safeRotationHomotopy_avoids p γ a b hγ_ne t ht s hs
  -- 6. Differentiability away from P
  · intro t ht ht_not_P s hs
    -- The clamped version is differentiable because clamp is identity on the domain
    simp only [H]
    have h_t_eq : clamp_t t = t := h_clamp_t_id t (Ioo_subset_Icc_self ht)
    have h_s_eq : clamp_s s = s := h_clamp_s_id s hs
    -- Since clamp_t is identity on Ioo a b, H(t, s) = safeRotationHomotopy(t, s)
    -- Use safeRotationHomotopy_diff
    have h_diff : DifferentiableAt ℝ (fun t' => safeRotationHomotopy p γ a b hγ_ne (t', s)) t :=
      safeRotationHomotopy_diff p γ a b hab hγ_cont hγ_ne P hγ_diff t ht ht_not_P s hs
    -- Now show the clamped version has the same derivative
    -- Since clamp_t t' = t' in a neighborhood of t (because t ∈ Ioo a b)
    have h_nhd : ∀ᶠ t' in 𝓝 t, clamp_t t' = t' := by
      -- t is in the interior Ioo a b, so there's a ball around t in Ioo a b
      have h_open : IsOpen (Ioo a b) := isOpen_Ioo
      filter_upwards [h_open.mem_nhds ht] with t' ht'
      exact h_clamp_t_id t' (Ioo_subset_Icc_self ht')
    apply h_diff.congr_of_eventuallyEq
    filter_upwards [h_nhd] with t' ht'_eq
    simp only [ht'_eq, h_s_eq]
  -- 7. Derivative continuity on pieces
  · intro p₁ p₂ hp hp_smooth
    -- This requires showing derivative continuity for the clamped homotopy H.
    -- The proof splits into cases:
    -- (a) When Ioo p₁ p₂ ⊆ Ioo a b: use safeRotationHomotopy_deriv_cont
    -- (b) When Ioo p₁ p₂ is outside [a, b]: derivative is 0 (clamping is constant)
    -- (c) Boundary cases: requires careful analysis of derivative at clamp boundary
    --
    -- For the valence formula, we only ever apply this to the actual partition
    -- where Ioo p₁ p₂ ⊆ Ioo a b holds (the partition comes from elliptic points
    -- which are at t = 1, 2, 3, 4 inside [0, 4]).
    --
    -- Technical note: safeRotationHomotopy_deriv_cont requires h_subset : Ioo p₁ p₂ ⊆ Ioo a b
    -- which is NOT directly derivable from hp_smooth. In practice, this is always true
    -- for our use cases, but proving it in full generality requires handling clamping
    -- boundaries carefully.
    sorry

/-!
## Pure Homotopy Approach (NO ANGLE LIFTS)

The following theorems use ONLY homotopy invariance - no angle lifts or argument change.
This avoids circular dependencies with `fundamentalDomainBoundary_wraps_once`.

The key theorem is `winding_eq_one_of_homotopic_to_circle` (above), which says:
  If γ is piecewise-homotopic to circleParam (avoiding p), then winding(γ) = 1.

The safe rotation infrastructure (rotFactor, safeRotationHomotopy) can be used to
BUILD the homotopy for specific curves like the fundamental domain boundary.
-/

/-- Main theorem: winding = 1 via pure homotopy (NO angle lifts).

    **Pure Homotopy Approach:**
    Takes a homotopy γ → circleParam as hypothesis, uses homotopy invariance.
    No dependence on angle lifts or argument_change_2pi.

    For the fundamental domain boundary, the homotopy is constructed in ValenceFormula.lean
    using safe rotation and reparameterization on S¹.
-/
theorem winding_eq_one_via_homotopy (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p)
    (hγ_closed : γ a = γ b)
    (P : Finset ℝ)
    (hP : ∀ t ∈ P, t ∈ Ioo a b)
    -- KEY: Takes homotopy to circle as hypothesis (no angle lift!)
    (hhom : PiecewiseCurvesHomotopicAvoiding γ (circleParam p 1 a b) a b p P) :
    generalizedWindingNumber' γ a b p = 1 :=
  winding_eq_one_of_homotopic_to_circle p γ a b P hab hγ_cont hγ_ne hγ_closed hhom

end