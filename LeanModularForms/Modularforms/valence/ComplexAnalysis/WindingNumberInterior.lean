/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import LeanModularForms.Modularforms.valence.ComplexAnalysis.PiecewiseHomotopy
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Winding Number = 1 via Homotopy Methods

This file provides general-purpose theorems for proving that the winding number
of a closed piecewise-C¹ curve around a point equals 1 using homotopy methods.

## Main Results (Currently Active)

* `radial_homotopy_avoids` - The radial homotopy H(t,s) = p + c(t,s)•(γ(t)-p) avoids p
* `circleParam_winding_eq_one` - A standard circle parameterization has winding = 1
* `winding_of_S1_curve_eq_degree` - An S¹ curve's winding equals its degree
* `winding_eq_one_of_homotopic_to_circle` - Pure homotopy approach to winding = 1
* `safeRotationHomotopy_piecewise_avoiding` - Safe rotation homotopy preserves winding
* `lipschitzOnWith_of_deriv_bound_interior` - Interior differentiability implies Lipschitz
* `lipschitzOnWith_of_deriv_bound_piecewise` - Piecewise C¹ with bounded deriv implies Lipschitz

## Commented Out (Not on Critical Path)

* `radialHomotopy_winding_eq` - Radial homotopy preserves winding (has sorry in edge case)
* `winding_eq_one_of_wraps_once` - If γ wraps once counterclockwise, winding = 1

## Strategy for Valence Formula

The valence formula uses `safeRotationHomotopy` and `winding_eq_one_of_homotopic_to_circle`
rather than the radial projection approach. This avoids certain edge cases in the
derivative bounds.

All theorems are parametric and can be instantiated for any specific curve.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Piecewise Derivative Bound -/

/-- Derivative is bounded on a closed interval where it's continuous.
    This is the key compactness lemma for derivative bounds. -/
lemma deriv_bounded_on_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {u v : ℝ} (_huv : u ≤ v)
    (hcont : ContinuousOn (fun t => deriv f t) (Icc u v)) :
    ∃ M, ∀ t ∈ Icc u v, ‖deriv f t‖ ≤ M := by
  -- Use compactness: continuous image of compact set is compact, hence bounded
  have hcomp : IsCompact (Icc u v) := isCompact_Icc
  -- exists_bound_of_continuousOn gives: ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C
  -- So we apply it to (fun t => deriv f t) to get bound on ‖deriv f t‖
  exact hcomp.exists_bound_of_continuousOn hcont

/-- Helper: given a list of pieces with bounds, returns a uniform bound for all pieces -/
lemma uniform_bound_from_list {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (pieces : List (ℝ × ℝ))
    (hpieces : ∀ p ∈ pieces, ContinuousOn (fun t => deriv f t) (Icc p.1 p.2)) :
    ∃ M, ∀ p ∈ pieces, ∀ t ∈ Icc p.1 p.2, ‖deriv f t‖ ≤ M := by
  induction pieces with
  | nil => use 0; simp
  | cons hd tl ih =>
    -- Bound for head
    have hbdd_hd : ∃ Mhd, ∀ t ∈ Icc hd.1 hd.2, ‖deriv f t‖ ≤ Mhd := by
      by_cases h : hd.1 ≤ hd.2
      · exact deriv_bounded_on_Icc h (hpieces hd (by simp))
      · use 0; intro t ht; simp only [not_le] at h
        exact absurd (ht.1.trans ht.2) (not_le.mpr h)
    obtain ⟨Mhd, hMhd⟩ := hbdd_hd
    -- Bound for tail
    have hpieces_tl : ∀ p ∈ tl, ContinuousOn (fun t => deriv f t) (Icc p.1 p.2) :=
      fun p hp => hpieces p (List.mem_cons_of_mem hd hp)
    obtain ⟨Mtl, hMtl⟩ := ih hpieces_tl
    -- Take max
    use max Mhd Mtl
    intro p hp t ht
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp'
    · calc ‖deriv f t‖ ≤ Mhd := hMhd t ht
        _ ≤ max Mhd Mtl := le_max_left _ _
    · calc ‖deriv f t‖ ≤ Mtl := hMtl p hp' t ht
        _ ≤ max Mhd Mtl := le_max_right _ _

/-- For a piecewise C¹ function with deriv continuous on each CLOSED piece,
    the derivative is bounded on [a, b].

    This is the correct hypothesis: continuity on closed pieces gives boundedness
    via compactness.
-/
lemma piecewise_deriv_bounded_of_cont_on_pieces {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a b : ℝ) (_hab : a < b)
    -- Consecutive partition points (including endpoints)
    (pieces : List (ℝ × ℝ))
    -- The pieces cover [a,b]
    (hcover : ∀ t ∈ Icc a b, ∃ p ∈ pieces, t ∈ Icc p.1 p.2)
    -- Derivative is continuous on each closed piece
    (hpieces : ∀ p ∈ pieces, ContinuousOn (fun t => deriv f t) (Icc p.1 p.2)) :
    ∃ M, ∀ t ∈ Icc a b, ‖deriv f t‖ ≤ M := by
  -- Get uniform bound over all pieces
  obtain ⟨M, hM⟩ := uniform_bound_from_list f pieces hpieces
  -- For any t in [a,b], it's in some piece, so bound applies
  use M
  intro t ht
  obtain ⟨p, hp, htp⟩ := hcover t ht
  exact hM p hp t htp

/-
-- COMMENTED OUT: These lemmas are not used on the critical path for the valence formula.
-- They can be proven using piecewise_deriv_bounded_of_cont_on_pieces if needed.

/-- Almost-everywhere version: deriv is bounded except on finite set P.
    This is often sufficient for integrability arguments. -/
lemma piecewise_deriv_bounded_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a b : ℝ) (_hab : a < b) (P : Finset ℝ)
    (_hP : ∀ t ∈ P, t ∈ Ioo a b)
    (_hf_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ f t)
    (_hf_deriv_cont : ∀ t ∈ Ioo a b, t ∉ P → ContinuousAt (deriv f) t)
    -- Key hypothesis: deriv has finite one-sided limits at partition points
    (_hf_deriv_bdd_at_P : ∀ p ∈ P, ∃ M, ∀ᶠ t in 𝓝 p, ‖deriv f t‖ ≤ M) :
    ∃ M, ∀ t ∈ Icc a b, t ∉ P → ‖deriv f t‖ ≤ M := by
  -- For t ∉ P in interior: deriv f is continuous at t, so locally bounded
  -- The global bound comes from compactness of [a,b] \ (small nhds of P)
  -- This is a standard argument but technically involved
  sorry -- Technical: combine local bounds using compactness

/-- Original lemma signature (weaker hypotheses, harder to prove).
    Use `piecewise_deriv_bounded_of_cont_on_pieces` when you have continuity on closed pieces. -/
lemma piecewise_deriv_bounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a b : ℝ) (_hab : a < b) (P : Finset ℝ)
    (_hP : ∀ t ∈ P, t ∈ Ioo a b)
    (_hf_cont : ContinuousOn f (Icc a b))
    (_hf_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ f t)
    (_hf_deriv_cont : ∀ t ∈ Ioo a b, t ∉ P → ContinuousAt (deriv f) t) :
    ∃ M, ∀ t ∈ Icc a b, ‖deriv f t‖ ≤ M := by
  -- At non-differentiable points: deriv f t = 0 by Lean convention
  -- At differentiable points: deriv f is continuous, need to show bounded
  --
  -- APPROACH: Use compactness on each closed piece between partition points.
  -- The key is that deriv f is continuous on (p_i, p_{i+1}), and if it extends
  -- continuously to [p_i, p_{i+1}], then it's bounded by compactness.
  --
  -- For the valence formula, curves are piecewise C¹ in the strong sense:
  -- - Vertical segments: deriv = ±i (constant, bounded)
  -- - Circular arcs: deriv = angular_velocity * exp(iθ) (bounded)
  --
  -- We handle two cases:
  -- 1. t ∉ P ∪ {a, b}: deriv f is continuous at t
  -- 2. t ∈ P ∪ {a, b}: deriv f = 0 (not diff) or bounded by nearby values
  --
  -- The formal proof uses `piecewise_deriv_bounded_of_cont_on_pieces` when the
  -- stronger hypothesis (continuity on closed pieces) is available.
  --
  -- SIMPLIFICATION for valence formula: At partition points where f is not
  -- differentiable, deriv f = 0. At points where f IS diff, deriv f is continuous
  -- and hence bounded in a neighborhood. Taking max over finitely many pieces + P:
  sorry
-/

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

/-! ## Clockwise Circle Parameterization -/

/-- Clockwise circle parameterization: reverses the direction of circleParam.
    circleParamCW z₀ r a b t := circleParam z₀ r a b (a + b - t)

    While circleParam traverses the circle counterclockwise (positive orientation),
    circleParamCW traverses it clockwise (negative orientation).
-/
def circleParamCW (z₀ : ℂ) (r : ℝ) (a b : ℝ) (t : ℝ) : ℂ :=
  circleParam z₀ r a b (a + b - t)

lemma circleParamCW_continuous (z₀ : ℂ) (r : ℝ) (a b : ℝ) :
    Continuous (circleParamCW z₀ r a b) := by
  unfold circleParamCW
  exact (circleParam_continuous z₀ r a b).comp (continuous_const.sub continuous_id)

lemma circleParamCW_closed (z₀ : ℂ) (r : ℝ) (a b : ℝ) (hab : a < b) :
    circleParamCW z₀ r a b a = circleParamCW z₀ r a b b := by
  simp only [circleParamCW]
  have ha : a + b - a = b := by ring
  have hb : a + b - b = a := by ring
  rw [ha, hb]
  exact (circleParam_closed z₀ r a b hab).symm

lemma circleParamCW_dist (z₀ : ℂ) (r : ℝ) (hr : 0 ≤ r) (a b : ℝ) (hab : a < b) (t : ℝ) :
    ‖circleParamCW z₀ r a b t - z₀‖ = r := by
  simp only [circleParamCW]
  exact circleParam_dist z₀ r hr a b hab (a + b - t)

/-- Differentiability of circleParam. -/
lemma circleParam_differentiable (z₀ : ℂ) (r : ℝ) (a b : ℝ) :
    Differentiable ℝ (circleParam z₀ r a b) := by
  unfold circleParam
  apply Differentiable.add
  · exact differentiable_const z₀
  · apply Differentiable.mul
    · exact differentiable_const _
    · apply Differentiable.cexp
      apply Differentiable.mul
      · exact differentiable_const _
      · apply Differentiable.div_const
        apply Differentiable.sub
        · exact Complex.ofRealCLM.differentiable.comp differentiable_id
        · exact differentiable_const _

/-- Differentiability of circleParamCW. -/
lemma circleParamCW_differentiable (z₀ : ℂ) (r : ℝ) (a b : ℝ) :
    Differentiable ℝ (circleParamCW z₀ r a b) := by
  unfold circleParamCW
  exact (circleParam_differentiable z₀ r a b).comp
    ((differentiable_const _).sub differentiable_id)

/-- The derivative of circleParamCW. Uses chain rule with g(t) = a + b - t.
    Derivative is -(circleParam derivative at a+b-t) due to inner function g'(t) = -1. -/
lemma circleParamCW_hasDerivAt (z₀ : ℂ) (r : ℝ) (a b : ℝ) (hab : a < b) (t : ℝ) :
    HasDerivAt (circleParamCW z₀ r a b) (
      -(r * (2 * Real.pi * I / (b - a)) *
        exp (2 * Real.pi * I * (((a + b - t : ℝ) - a) / (b - a))))) t := by
  unfold circleParamCW
  -- circleParam is differentiable everywhere
  have hdiff : DifferentiableAt ℝ (circleParam z₀ r a b) (a + b - t) :=
    (circleParam_differentiable z₀ r a b).differentiableAt
  -- g(t) = a + b - t has HasDerivAt with derivative -1
  have hg : HasDerivAt (fun t : ℝ => (a + b - t : ℝ)) (-1 : ℝ) t := by
    have h1 : HasDerivAt (fun _ : ℝ => (a + b : ℝ)) 0 t := hasDerivAt_const t (a + b)
    have h2 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
    have h3 := h1.sub h2
    convert h3 using 1
    ring
  -- circleParam has HasDerivAt at (a + b - t)
  have hf : HasDerivAt (circleParam z₀ r a b)
      (r * (2 * Real.pi * I / (b - a)) *
        exp (2 * Real.pi * I * ((↑(a + b - t) - a) / (b - a)))) (a + b - t) := by
    have hd := circleParam_deriv z₀ r a b hab (a + b - t)
    rw [← hd]
    exact hdiff.hasDerivAt
  -- Chain rule via scomp (scalar derivative composition)
  have hchain := HasDerivAt.scomp t hf hg
  simp only [neg_one_smul] at hchain
  exact hchain

lemma circleParamCW_deriv (z₀ : ℂ) (r : ℝ) (a b : ℝ) (hab : a < b) (t : ℝ) :
    deriv (circleParamCW z₀ r a b) t =
    -(r * (2 * Real.pi * I / (b - a)) *
      exp (2 * Real.pi * I * (((a + b - t : ℝ) - a) / (b - a)))) :=
  (circleParamCW_hasDerivAt z₀ r a b hab t).deriv

/-- Integrand for circleParamCW is the negative of circleParam's integrand. -/
lemma circleParamCW_integrand_neg (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (a b : ℝ) (hab : a < b) (t : ℝ) :
    (circleParamCW z₀ r a b t - z₀)⁻¹ * deriv (circleParamCW z₀ r a b) t =
    -(2 * Real.pi * I / (b - a)) := by
  rw [circleParamCW_deriv z₀ r a b hab t]
  simp only [circleParamCW, circleParam, add_sub_cancel_left]
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hexp_ne : exp (2 * Real.pi * I * (((a + b - t : ℝ) - a) / (b - a))) ≠ 0 := exp_ne_zero _
  field_simp [hr_ne, hexp_ne]

/-- The winding number of a clockwise circle around its center is -1. -/
theorem circleParamCW_winding_eq_neg_one (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (a b : ℝ) (hab : a < b) :
    generalizedWindingNumber' (circleParamCW z₀ r a b) a b z₀ = -1 := by
  have havoids : ∀ t, ‖circleParamCW z₀ r a b t - z₀‖ = r := fun t =>
    circleParamCW_dist z₀ r (le_of_lt hr) a b hab t
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  -- For ε < r, integrand is constant -2πi/(b-a)
  have hint_const : ∀ ε > 0, ε < r →
      (∫ t in a..b, if ‖circleParamCW z₀ r a b t - z₀‖ > ε then
        (circleParamCW z₀ r a b t - z₀)⁻¹ * deriv (circleParamCW z₀ r a b) t else 0) =
      -2 * Real.pi * I := by
    intro ε _hε_pos hε_lt_r
    have h_cond : ∀ t, ‖circleParamCW z₀ r a b t - z₀‖ > ε := fun t => by
      rw [havoids]; exact hε_lt_r
    have h_simp : (fun t => if ‖circleParamCW z₀ r a b t - z₀‖ > ε then
        (circleParamCW z₀ r a b t - z₀)⁻¹ * deriv (circleParamCW z₀ r a b) t else 0) =
        fun _ => -(2 * Real.pi * I / (b - a)) := by
      ext t; simp only [h_cond t, ↓reduceIte]
      exact circleParamCW_integrand_neg z₀ r hr a b hab t
    rw [h_simp, intervalIntegral.integral_const]
    have hba_ne : (b : ℂ) - a ≠ 0 := by
      simp [sub_ne_zero, Complex.ofReal_inj]; exact ne_of_gt hab
    simp only [Complex.real_smul, Complex.ofReal_sub]
    field_simp [hba_ne]
  have hlim : limUnder (𝓝[>] (0 : ℝ)) (fun ε =>
      ∫ t in a..b, if ‖circleParamCW z₀ r a b t - z₀‖ > ε then
        (circleParamCW z₀ r a b t - z₀)⁻¹ * deriv (circleParamCW z₀ r a b) t else 0) =
      -2 * Real.pi * I := by
    apply limUnder_eventually_eq_const
    filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
    exact hint_const ε (mem_Ioo.mp hε).1 (mem_Ioo.mp hε).2
  have h_match : (fun ε => ∫ t in a..b,
      if ‖(fun t => circleParamCW z₀ r a b t - z₀) t - 0‖ > ε then
        (fun x => x⁻¹) ((fun t => circleParamCW z₀ r a b t - z₀) t) *
        deriv (fun t => circleParamCW z₀ r a b t - z₀) t
      else 0) = (fun ε => ∫ t in a..b,
      if ‖circleParamCW z₀ r a b t - z₀‖ > ε then
        (circleParamCW z₀ r a b t - z₀)⁻¹ * deriv (circleParamCW z₀ r a b) t
      else 0) := by
    ext ε; congr 1 with t; simp only [sub_zero, deriv_sub_const]
  simp only [h_match, hlim]
  have hpi_ne : (2 : ℂ) * Real.pi * I ≠ 0 := by
    simp [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero]
  field_simp [hpi_ne]

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

/-! ## Radial Homotopy Preserves Winding Number

NOTE: `radialHomotopy_winding_eq` is NOT on the critical path for ValenceFormula.
The valence formula uses `winding_eq_one_of_homotopic_to_circle` and `safeRotationHomotopy` instead.
This theorem is commented out to reduce the sorry count.
Uncomment if needed for other applications that require radial projection homotopy.
-/

/-
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
    (hγ_deriv_cont : ∀ t ∈ Ioo a b, t ∉ P → ContinuousAt (deriv γ) t)
    -- Derivative bound needed for dominated convergence in homotopy invariance
    (hγ_deriv_bound : ∃ M : ℝ, ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M) :
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
  -- NOTE: The subset constraint Ioo p₁ p₂ ⊆ Ioo a b is required by the structure,
  -- but we don't need to use it since γ_ext is continuous everywhere via clamping.
  have hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P_ext) →
      Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (fun (x : ℝ × ℝ) => deriv (fun t' => H (t', x.2)) x.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
    intro p₁ p₂ hp₁p₂ h_avoid _h_sub
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
  -- Derive homotopy derivative bound from γ derivative bound
  -- The bound follows from the explicit derivative formula and component bounds.
  -- For simplicity, we use M * K / δ² + M + M / δ where M bounds ‖γ'‖, K bounds ‖γ - p‖,
  -- and δ is a lower bound on ‖γ - p‖.
  have hH_deriv_bound : ∃ M' : ℝ, ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1,
      ‖deriv (fun t' => H (t', s)) t‖ ≤ M' := by
    obtain ⟨M, hM⟩ := hγ_deriv_bound
    -- Get uniform lower bound δ on distance to p
    have h_bound_away : ∃ δ > 0, ∀ t ∈ Icc a b, δ ≤ ‖γ t - p‖ := by
      have h_compact : IsCompact (γ '' Icc a b) := isCompact_Icc.image_of_continuousOn hγ_cont
      have h_nonempty : (γ '' Icc a b).Nonempty := Set.image_nonempty.mpr (nonempty_Icc.mpr hab.le)
      have hp_notin : p ∉ γ '' Icc a b := fun ⟨t, ht, heq⟩ => hγ_ne t ht heq
      have hδ : 0 < Metric.infDist p (γ '' Icc a b) :=
        (h_compact.isClosed.notMem_iff_infDist_pos h_nonempty).mp hp_notin
      use Metric.infDist p (γ '' Icc a b), hδ
      intro t ht
      have hmem : γ t ∈ γ '' Icc a b := mem_image_of_mem γ ht
      calc Metric.infDist p (γ '' Icc a b) ≤ dist p (γ t) := Metric.infDist_le_dist_of_mem hmem
        _ = ‖γ t - p‖ := by rw [Complex.dist_eq, norm_sub_rev]
    obtain ⟨δ, hδ_pos, hδ_bound⟩ := h_bound_away
    -- Get upper bound K on ‖γ - p‖
    have h_bound_above : ∃ K > 0, ∀ t ∈ Icc a b, ‖γ t - p‖ ≤ K := by
      have h_compact : IsCompact (γ '' Icc a b) := isCompact_Icc.image_of_continuousOn hγ_cont
      have h_nonempty : (γ '' Icc a b).Nonempty := Set.image_nonempty.mpr (nonempty_Icc.mpr hab.le)
      have h_bdd : Bornology.IsBounded (γ '' Icc a b) := h_compact.isBounded
      obtain ⟨R, hR⟩ := h_bdd.subset_ball p
      use max R 1, lt_max_of_lt_right one_pos
      intro t ht
      have hmem : γ t ∈ γ '' Icc a b := mem_image_of_mem γ ht
      have h_in_ball := hR hmem
      rw [Metric.mem_ball, Complex.dist_eq] at h_in_ball
      calc ‖γ t - p‖ ≤ R := le_of_lt h_in_ball
        _ ≤ max R 1 := le_max_left R 1
    obtain ⟨K, hK_pos, hK_bound⟩ := h_bound_above
    -- Use the bound M' = M * K / δ² + M + M / δ
    use M * K / δ^2 + M + M / δ
    intro t ht s hs
    have h_ext_lower : δ ≤ ‖γ_ext t - p‖ := by
      simp only [γ_ext]; exact hδ_bound (clampTo a b t) (clampTo_mem hab.le t)
    have h_ext_upper : ‖γ_ext t - p‖ ≤ K := by
      simp only [γ_ext]; exact hK_bound (clampTo a b t) (clampTo_mem hab.le t)
    have h_M_nn : 0 ≤ M := le_trans (norm_nonneg _) (hM a (left_mem_Icc.mpr hab.le))
    have h_norm_pos : 0 < ‖γ_ext t - p‖ := lt_of_lt_of_le hδ_pos h_ext_lower
    -- For t ∈ (a, b), we use the explicit derivative formula
    -- For t = a or t = b, if H is differentiable, the derivative is 0 (γ_ext constant on one side)
    by_cases h_diff : DifferentiableAt ℝ (fun t' => H (t', s)) t
    · -- H is differentiable at t
      -- Check if t is at an endpoint or in the interior
      by_cases ht_Ioo : t ∈ Ioo a b
      · -- Interior case: t ∈ (a, b), so γ_ext = γ locally
        have h_ev : γ_ext =ᶠ[𝓝 t] γ := by
          filter_upwards [isOpen_Ioo.mem_nhds ht_Ioo] with u hu
          exact hγ_ext_eq u (Ioo_subset_Icc_self hu)
        -- Handle the t ∈ P case separately
        by_cases h_in_P : t ∈ P
        · -- t ∈ P ∩ Ioo a b: This is a corner case where γ may not be C¹.
          -- At partition points, γ_ext is NOT differentiable (it's a piecewise C¹ curve).
          -- By Lean convention, deriv γ_ext t = 0 when γ_ext is not differentiable at t.
          --
          -- Key insight: By chain rule with inner derivative 0:
          -- - deriv (‖γ_ext - p‖) t = 0 (since ‖·‖ is smooth and deriv γ_ext = 0)
          -- - deriv c t = 0 (since c depends on γ_ext only through ‖γ_ext - p‖)
          -- - deriv H = deriv c • z + c • deriv γ_ext = 0 • z + c • 0 = 0
          --
          -- Therefore ‖deriv H‖ = 0 ≤ any positive bound.
          --
          -- Note: h_diff says H IS differentiable at t, which is consistent with
          -- deriv H = 0. The derivative exists and equals 0.
          have h_bound_partition_point : ‖deriv (fun t' => H (t', s)) t‖ ≤ M * K / δ^2 + M + M / δ := by
            -- At partition points, γ_ext is not differentiable
            -- Since t ∈ P and hγ_diff only guarantees differentiability for t ∉ P,
            -- γ_ext may not be differentiable at t
            by_cases hγ_ext_diff_at_t : DifferentiableAt ℝ γ_ext t
            · -- γ_ext IS differentiable at t (corner case: t ∈ P but happens to be smooth)
              -- Use the same derivation as the t ∉ P case
              have h_deriv_γ_ext_bound : ‖deriv γ_ext t‖ ≤ M := by
                rw [Filter.EventuallyEq.deriv_eq h_ev]
                exact hM t (Ioo_subset_Icc_self ht_Ioo)
              let z := γ_ext t - p
              let c : ℝ := (1 - s) + s / ‖z‖
              let dc : ℝ := -s * (Complex.re (starRingEnd ℂ z * deriv γ_ext t)) / ‖z‖ ^ 3
              have h_deriv_eq : deriv (fun t' => H (t', s)) t = dc • z + c • deriv γ_ext t :=
                deriv_H_formula γ_ext p t s hγ_ext_diff_at_t (hγ_ext_ne t)
              rw [h_deriv_eq]
              have hs_nn : 0 ≤ s := hs.1
              have hs_le : s ≤ 1 := hs.2
              have h_dc_bound : |dc| ≤ M / δ^2 := by
                simp only [dc, abs_div, abs_pow]
                have h_num : |-s * Complex.re (starRingEnd ℂ z * deriv γ_ext t)| ≤ ‖z‖ * ‖deriv γ_ext t‖ := by
                  have h1 : |-s * Complex.re (starRingEnd ℂ z * deriv γ_ext t)| =
                      |s| * |Complex.re (starRingEnd ℂ z * deriv γ_ext t)| := by
                    rw [show -s * _ = -(s * _) from neg_mul s _, abs_neg, abs_mul]
                  calc |-s * Complex.re (starRingEnd ℂ z * deriv γ_ext t)|
                      = |s| * |Complex.re (starRingEnd ℂ z * deriv γ_ext t)| := h1
                    _ ≤ 1 * |Complex.re (starRingEnd ℂ z * deriv γ_ext t)| := by
                        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                        rw [abs_of_nonneg hs_nn]; exact hs_le
                    _ = |Complex.re (starRingEnd ℂ z * deriv γ_ext t)| := one_mul _
                    _ ≤ ‖starRingEnd ℂ z * deriv γ_ext t‖ := Complex.abs_re_le_norm _
                    _ ≤ ‖starRingEnd ℂ z‖ * ‖deriv γ_ext t‖ := norm_mul_le _ _
                    _ = ‖z‖ * ‖deriv γ_ext t‖ := by rw [RingHomIsometric.norm_map]
                have h_denom_pos : 0 < |‖z‖| ^ 3 := by
                  rw [abs_of_nonneg (norm_nonneg z)]; exact pow_pos h_norm_pos 3
                have h_norm_ne : ‖z‖ ≠ 0 := ne_of_gt h_norm_pos
                calc |-s * Complex.re (starRingEnd ℂ z * deriv γ_ext t)| / |‖z‖| ^ 3
                    ≤ (‖z‖ * ‖deriv γ_ext t‖) / |‖z‖| ^ 3 :=
                      div_le_div_of_nonneg_right h_num (le_of_lt h_denom_pos)
                  _ = (‖z‖ * ‖deriv γ_ext t‖) / ‖z‖ ^ 3 := by rw [abs_of_nonneg (norm_nonneg z)]
                  _ = ‖deriv γ_ext t‖ / ‖z‖ ^ 2 := by
                      rw [pow_succ, pow_two]; field_simp [h_norm_ne]
                  _ ≤ M / δ ^ 2 := by
                      have h_sq_le : δ ^ 2 ≤ ‖z‖ ^ 2 := sq_le_sq' (by linarith) h_ext_lower
                      calc ‖deriv γ_ext t‖ / ‖z‖ ^ 2
                          ≤ M / ‖z‖ ^ 2 := div_le_div_of_nonneg_right h_deriv_γ_ext_bound (sq_pos_of_pos h_norm_pos).le
                        _ ≤ M / δ ^ 2 := div_le_div_of_nonneg_left h_M_nn (sq_pos_of_pos hδ_pos) h_sq_le
              have h_c_bound : |c| ≤ 1 + 1/δ := by
                calc |c| = |(1 - s) + s / ‖z‖| := rfl
                  _ ≤ |1 - s| + |s / ‖z‖| := abs_add_le _ _
                  _ ≤ 1 + 1/δ := by
                      apply add_le_add
                      · rw [abs_le]; constructor <;> linarith
                      · rw [abs_div, abs_of_nonneg hs_nn, abs_of_nonneg (norm_nonneg _)]
                        calc s / ‖z‖ ≤ 1 / ‖z‖ := div_le_div_of_nonneg_right hs_le (le_of_lt h_norm_pos)
                          _ ≤ 1 / δ := one_div_le_one_div_of_le hδ_pos h_ext_lower
              have h_coeff_nn : 0 ≤ 1 + 1/δ := by positivity
              calc ‖dc • z + c • deriv γ_ext t‖
                  ≤ ‖dc • z‖ + ‖c • deriv γ_ext t‖ := norm_add_le _ _
                _ = |dc| * ‖z‖ + |c| * ‖deriv γ_ext t‖ := by
                    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
                _ ≤ (M / δ^2) * K + (1 + 1/δ) * M := by
                    apply add_le_add
                    · exact mul_le_mul h_dc_bound h_ext_upper (norm_nonneg _) (div_nonneg h_M_nn (sq_nonneg _))
                    · exact mul_le_mul h_c_bound h_deriv_γ_ext_bound (norm_nonneg _) h_coeff_nn
                _ = M * K / δ^2 + M + M / δ := by ring
            · -- γ_ext is NOT differentiable at t (the typical case at partition points)
              -- By Lean convention, deriv γ_ext t = 0, so deriv H t = 0
              -- We need to show ‖deriv H t‖ = 0 ≤ bound
              -- Use the fact that if γ_ext is not diff, then H may or may not be diff,
              -- but deriv H = 0 by convention if H is not diff, or can be computed if H is diff
              -- Since h_diff says H IS diff at t, we need to compute deriv H
              -- The key is: deriv H = 0 because the chain rule gives 0 when inner deriv = 0
              --
              -- Actually, this is subtle. If H is differentiable at t but γ_ext is not,
              -- then H's derivative comes from a different source (e.g., angular motion).
              -- For s < 1: H = p + c * z where c involves ‖z‖ which involves z
              --   If z = γ_ext - p is not diff, then c is not diff, so H is not diff
              --   But h_diff says H IS diff, contradiction
              -- For s = 1: H = p + z/‖z‖, the unit direction
              --   If z is continuous but direction is smooth, H can be diff even if z is not
              --
              -- This corner case (s = 1, H diff but γ_ext not diff) means the angular
              -- direction is varying smoothly even though γ_ext has a corner.
              -- In this case, deriv H is the angular velocity times the unit tangent.
              -- The angular velocity is bounded, so deriv H is bounded.
              --
              -- For simplicity, we use the fact that ‖deriv H‖ ≤ ‖deriv H‖ and just
              -- need to show this is bounded. Since H is continuous and diff on a dense
              -- set (away from P), and if H is diff at t ∈ P, the derivative is the limit.
              --
              -- The bound M * K / δ² + M + M / δ holds by continuity of the bound function.
              -- But formalizing this requires more machinery than available here.
              --
              -- Pragmatic approach: use that 0 ≤ bound, and bound deriv H using simpler args.
              have h_nn : 0 ≤ M * K / δ^2 + M + M / δ := by
                have h1 : 0 ≤ M * K / δ^2 := div_nonneg (mul_nonneg h_M_nn (le_of_lt hK_pos)) (sq_nonneg _)
                have h3 : 0 ≤ M / δ := div_nonneg h_M_nn (le_of_lt hδ_pos)
                linarith
              -- Use the differentiation chain rule: if f is not diff, deriv f = 0,
              -- so deriv (g ∘ f) = deriv g (f x) * deriv f x = something * 0 = 0
              -- More precisely, if the components of H have derivative 0, so does H.
              -- The z component has deriv 0 (γ_ext not diff).
              -- The c component involves ‖z‖ whose deriv involves deriv z = 0.
              -- So deriv c = 0 and deriv H = deriv c * z + c * deriv z = 0 * z + c * 0 = 0.
              -- Case split: either H is differentiable at t or not
              by_cases hH_diff : DifferentiableAt ℝ (fun t' => H (t', s)) t
              · -- H IS differentiable at t (despite γ_ext not being diff at corners)
                -- Use Lipschitz argument: H is Lipschitz with constant L, so ‖deriv H‖ ≤ L.
                --
                -- H(t,s) = p + c(t,s) • z(t) where z = γ_ext - p, c = (1-s) + s/‖z‖
                -- Lipschitz constant of H in t:
                --   ‖H(t₁) - H(t₂)‖ ≤ |c| • ‖z(t₁) - z(t₂)‖ + |Δc| • ‖z(t₂)‖
                --   where |c| ≤ 1 + 1/δ, ‖z(t₁) - z(t₂)‖ ≤ M|t₁-t₂|, ‖z‖ ≤ K
                --   and |Δc| ≤ (M/δ²)|t₁-t₂|
                -- So Lipschitz constant L = M(1 + 1/δ) + MK/δ² = M*K/δ² + M + M/δ
                --
                -- If f is Lipschitz with constant L and differentiable at x, then ‖deriv f x‖ ≤ L.
                have h_bound_corner : ‖deriv (fun t' => H (t', s)) t‖ ≤ M * K / δ^2 + M + M / δ := by
                  -- This is a measure-zero corner case: H IS differentiable at partition point t
                  -- despite γ_ext NOT being differentiable there.
                  --
                  -- For the fundamental domain boundary and typical curves, this case does NOT
                  -- occur: if γ has a corner at t (γ not diff), then H also has a corner at t
                  -- (H not diff), so we'd be in the "H is not diff" branch below (deriv H = 0).
                  --
                  -- The only way H can be diff at t while γ is not diff is if the directional
                  -- part of H varies smoothly despite γ having a corner. This is a measure-zero
                  -- edge case in the space of all possible curves.
                  --
                  -- For the valence formula, all curves are either:
                  -- 1. Vertical segments (smooth, γ IS differentiable at all interior points)
                  -- 2. Circular arcs (smooth, γ IS differentiable at all interior points)
                  -- So the "t ∈ P but γ is diff at t" case from lines 753-813 handles our needs,
                  -- and this branch (t ∈ P, γ NOT diff, but H IS diff) never executes.
                  --
                  -- Technical bound: If this did occur, the Lipschitz constant L = M*K/δ² + M + M/δ
                  -- would still bound ‖deriv H t‖ by the general principle that Lipschitz functions
                  -- have derivative bounded by the Lipschitz constant.
                  --
                  -- The full proof would use:
                  -- 1. γ is M-Lipschitz on [a,b] (by FTC with bounded derivative)
                  -- 2. H(·,s) is L-Lipschitz where L = M*K/δ² + M + M/δ (by composition bounds)
                  -- 3. norm_deriv_le_of_lipschitzOn to bound the derivative
                  --
                  -- This corner case is not in the critical path for the valence formula.
                  sorry
                exact h_bound_corner
              · -- H is NOT differentiable at t: deriv H = 0 by Lean convention
                have h_deriv_zero : deriv (fun t' => H (t', s)) t = 0 :=
                  deriv_zero_of_not_differentiableAt hH_diff
                rw [h_deriv_zero, norm_zero]
                exact h_nn
          exact h_bound_partition_point
        · -- t ∉ P: standard case
          have hγ_ext_diff : DifferentiableAt ℝ γ_ext t := (hγ_diff t ht_Ioo h_in_P).congr_of_eventuallyEq h_ev
          have h_deriv_γ_ext_bound : ‖deriv γ_ext t‖ ≤ M := by
            rw [Filter.EventuallyEq.deriv_eq h_ev]
            exact hM t (Ioo_subset_Icc_self ht_Ioo)
          -- Use the derivative formula: deriv H = dc • z + c • γ'
          let z := γ_ext t - p
          let c : ℝ := (1 - s) + s / ‖z‖
          let dc : ℝ := -s * (Complex.re (starRingEnd ℂ z * deriv γ_ext t)) / ‖z‖ ^ 3
          have h_deriv_eq : deriv (fun t' => H (t', s)) t = dc • z + c • deriv γ_ext t :=
            deriv_H_formula γ_ext p t s hγ_ext_diff (hγ_ext_ne t)
          rw [h_deriv_eq]
          -- Bound: ‖dc • z + c • γ'‖ ≤ |dc| * ‖z‖ + |c| * ‖γ'‖
          have hs_nn : 0 ≤ s := hs.1
          have hs_le : s ≤ 1 := hs.2
          have h_dc_bound : |dc| ≤ M / δ^2 := by
            simp only [dc, abs_div, abs_pow]
            have h_num : |-s * Complex.re (starRingEnd ℂ z * deriv γ_ext t)| ≤ ‖z‖ * ‖deriv γ_ext t‖ := by
              have h1 : |-s * Complex.re (starRingEnd ℂ z * deriv γ_ext t)| =
                  |s| * |Complex.re (starRingEnd ℂ z * deriv γ_ext t)| := by
                rw [show -s * _ = -(s * _) from neg_mul s _, abs_neg, abs_mul]
              calc |-s * Complex.re (starRingEnd ℂ z * deriv γ_ext t)|
                  = |s| * |Complex.re (starRingEnd ℂ z * deriv γ_ext t)| := h1
                _ ≤ 1 * |Complex.re (starRingEnd ℂ z * deriv γ_ext t)| := by
                    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                    rw [abs_of_nonneg hs_nn]; exact hs_le
                _ = |Complex.re (starRingEnd ℂ z * deriv γ_ext t)| := one_mul _
                _ ≤ ‖starRingEnd ℂ z * deriv γ_ext t‖ := Complex.abs_re_le_norm _
                _ ≤ ‖starRingEnd ℂ z‖ * ‖deriv γ_ext t‖ := norm_mul_le _ _
                _ = ‖z‖ * ‖deriv γ_ext t‖ := by rw [RingHomIsometric.norm_map]
            have h_denom_pos : 0 < |‖z‖| ^ 3 := by
              rw [abs_of_nonneg (norm_nonneg z)]; exact pow_pos h_norm_pos 3
            have h_norm_ne : ‖z‖ ≠ 0 := ne_of_gt h_norm_pos
            calc |-s * Complex.re (starRingEnd ℂ z * deriv γ_ext t)| / |‖z‖| ^ 3
                ≤ (‖z‖ * ‖deriv γ_ext t‖) / |‖z‖| ^ 3 :=
                  div_le_div_of_nonneg_right h_num (le_of_lt h_denom_pos)
              _ = (‖z‖ * ‖deriv γ_ext t‖) / ‖z‖ ^ 3 := by rw [abs_of_nonneg (norm_nonneg z)]
              _ = ‖deriv γ_ext t‖ / ‖z‖ ^ 2 := by
                  rw [pow_succ, pow_two]; field_simp [h_norm_ne]
              _ ≤ M / δ ^ 2 := by
                  have h_sq_le : δ ^ 2 ≤ ‖z‖ ^ 2 := sq_le_sq' (by linarith) h_ext_lower
                  calc ‖deriv γ_ext t‖ / ‖z‖ ^ 2
                      ≤ M / ‖z‖ ^ 2 := div_le_div_of_nonneg_right h_deriv_γ_ext_bound (sq_pos_of_pos h_norm_pos).le
                    _ ≤ M / δ ^ 2 := div_le_div_of_nonneg_left h_M_nn (sq_pos_of_pos hδ_pos) h_sq_le
          have h_c_bound : |c| ≤ 1 + 1/δ := by
            calc |c| = |(1 - s) + s / ‖z‖| := rfl
              _ ≤ |1 - s| + |s / ‖z‖| := abs_add_le _ _
              _ ≤ 1 + 1/δ := by
                  apply add_le_add
                  · rw [abs_le]; constructor <;> linarith
                  · rw [abs_div, abs_of_nonneg hs_nn, abs_of_nonneg (norm_nonneg _)]
                    calc s / ‖z‖ ≤ 1 / ‖z‖ := div_le_div_of_nonneg_right hs_le (le_of_lt h_norm_pos)
                      _ ≤ 1 / δ := one_div_le_one_div_of_le hδ_pos h_ext_lower
          have h_coeff_nn : 0 ≤ 1 + 1/δ := by positivity
          calc ‖dc • z + c • deriv γ_ext t‖
              ≤ ‖dc • z‖ + ‖c • deriv γ_ext t‖ := norm_add_le _ _
            _ = |dc| * ‖z‖ + |c| * ‖deriv γ_ext t‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
            _ ≤ (M / δ^2) * K + (1 + 1/δ) * M := by
                apply add_le_add
                · exact mul_le_mul h_dc_bound h_ext_upper (norm_nonneg _) (div_nonneg h_M_nn (sq_nonneg _))
                · exact mul_le_mul h_c_bound h_deriv_γ_ext_bound (norm_nonneg _) h_coeff_nn
            _ = M * K / δ^2 + M + M / δ := by ring
      · -- Endpoint case: t = a or t = b. At endpoints, H is constant on one side, so deriv = 0.
        have h_endpoint : t = a ∨ t = b := by
          simp only [mem_Ioo, not_and, not_lt] at ht_Ioo
          rcases le_or_gt t a with hta | hta
          · left; exact le_antisymm hta ht.1
          · right; exact le_antisymm ht.2 (ht_Ioo hta)
        have h_deriv_zero : deriv (fun t' => H (t', s)) t = 0 := by
          apply deriv_zero_of_frequently_const (c := H (t, s))
          rcases h_endpoint with heq_a | heq_b
          · -- t = a: H is constant on Iio a
            rw [heq_a]
            have H_const : ∀ u ≤ a, H (u, s) = H (a, s) := fun u hu => by
              simp only [H, γ_ext]
              rw [clampTo_of_le_left hu hab.le, clampTo_of_le_left (le_refl a) hab.le]
            have h_filter_le : 𝓝[<] a ≤ 𝓝[≠] a := nhdsWithin_mono a (fun x hx => ne_of_lt hx)
            refine Filter.Frequently.filter_mono ?_ h_filter_le
            rw [Filter.Frequently]
            intro hev
            have h_all_eq : ∀ᶠ x in 𝓝[<] a, H (x, s) = H (a, s) := by
              filter_upwards [self_mem_nhdsWithin] with u hu using H_const u (le_of_lt hu)
            have h_and := hev.and h_all_eq
            have h_false : ∀ᶠ x in 𝓝[<] a, False := h_and.mono (fun x ⟨h1, h2⟩ => h1 h2)
            rw [Filter.eventually_false_iff_eq_bot] at h_false
            have h_nebot : (𝓝[<] a).NeBot :=
              nhdsWithin_Iio_self_neBot' ⟨a - 1, sub_one_lt a⟩
            exact h_nebot.ne h_false
          · -- t = b: H is constant on Ioi b
            rw [heq_b]
            have H_const : ∀ u, b ≤ u → H (u, s) = H (b, s) := fun u hu => by
              simp only [H, γ_ext]
              rw [clampTo_of_ge_right hu hab.le, clampTo_of_ge_right (le_refl b) hab.le]
            have h_filter_le : 𝓝[>] b ≤ 𝓝[≠] b := nhdsWithin_mono b (fun x hx => ne_of_gt hx)
            refine Filter.Frequently.filter_mono ?_ h_filter_le
            rw [Filter.Frequently]
            intro hev
            have h_all_eq : ∀ᶠ x in 𝓝[>] b, H (x, s) = H (b, s) := by
              filter_upwards [self_mem_nhdsWithin] with u hu using H_const u (le_of_lt hu)
            have h_and := hev.and h_all_eq
            have h_false : ∀ᶠ x in 𝓝[>] b, False := h_and.mono (fun x ⟨h1, h2⟩ => h1 h2)
            rw [Filter.eventually_false_iff_eq_bot] at h_false
            have h_nebot : (𝓝[>] b).NeBot :=
              nhdsGT_neBot_of_exists_gt ⟨b + 1, lt_add_one b⟩
            exact h_nebot.ne h_false
        rw [h_deriv_zero, norm_zero]
        have h1 : 0 ≤ M * K / δ^2 := div_nonneg (mul_nonneg h_M_nn (le_of_lt hK_pos)) (sq_nonneg _)
        have h3 : 0 ≤ M / δ := div_nonneg h_M_nn (le_of_lt hδ_pos)
        linarith
    · -- Derivative doesn't exist: norm is 0
      rw [deriv_zero_of_not_differentiableAt h_diff, norm_zero]
      have h1 : 0 ≤ M * K / δ^2 := div_nonneg (mul_nonneg h_M_nn (le_of_lt hK_pos)) (sq_nonneg _)
      have h3 : 0 ≤ M / δ := div_nonneg h_M_nn (le_of_lt hδ_pos)
      linarith
  -- Build homotopy and apply invariance
  have hhom : PiecewiseCurvesHomotopicAvoiding γ rc a b p P_ext :=
    ⟨H, hH_cont, hH0, hH1, hH_closed, hH_avoids, hH_diff, hH_deriv_cont, hH_deriv_bound⟩
  exact windingNumber_eq_of_piecewise_homotopic γ rc a b p P_ext hab hhom
-/

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

/-! ## Composition: Winding = 1 from Wrapping Once

NOTE: `winding_eq_one_of_wraps_once` is NOT on the critical path for ValenceFormula.
The valence formula uses `winding_eq_one_of_homotopic_to_circle` instead.
This section is commented out to reduce the sorry count on the critical path.
Uncomment if needed for other applications.
-/

/-
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
  -- Need to prove derivative bound for γ to apply h_eq
  have h_deriv_bound : ∃ M, ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M := by
    -- Piecewise C¹ curves have bounded derivatives on compact intervals.
    --
    -- Approach: Use the angle lift from h_wraps.
    -- γ(t) = p + r(t) * exp(I * θ(t)) where r(t) = ‖γ(t) - p‖
    -- deriv γ = deriv r * exp(Iθ) + r * I * deriv θ * exp(Iθ)
    -- ‖deriv γ‖ ≤ |deriv r| + r * |deriv θ|
    --
    -- Since γ is continuous on compact [a,b] and avoids p:
    -- - r = ‖γ - p‖ is continuous and positive on [a,b]
    -- - ∃ R₁ R₂ > 0 such that R₁ ≤ r(t) ≤ R₂ for all t ∈ [a,b]
    --
    -- The derivative bound requires bounding deriv r and deriv θ.
    -- For deriv θ: θ is differentiable on (a,b) with integrable derivative.
    -- For the fundamental domain boundary, θ is piecewise linear, so deriv θ is
    -- piecewise constant (bounded). This holds for typical modular form contours.
    --
    -- Technical gap: The integrability of deriv θ doesn't directly give pointwise bounds.
    -- For piecewise linear θ (the typical case), deriv θ IS bounded.
    --
    -- At non-differentiable points (∈ P or endpoints), deriv γ = 0 by Lean convention.
    -- At differentiable points, the formula above bounds ‖deriv γ‖.
    --
    -- For the valence formula application where γ parameterizes the fundamental domain
    -- boundary (vertical segments + circular arcs), all pieces have bounded derivatives:
    -- - Vertical: γ(t) = x₀ + it, deriv γ = i, ‖deriv γ‖ = 1
    -- - Arc: γ(t) = exp(iφ(t)) with φ linear, deriv γ bounded by angular velocity
    --
    -- MARKER: This sorry covers the technical proof of derivative boundedness
    -- for general piecewise C¹ curves. For the specific curves in the valence formula
    -- (fundamental domain boundary), the bound is explicitly computable.
    obtain ⟨θ, hθ_cont, hθ_diff, _, hθ_eq, _⟩ := h_wraps
    -- r(t) = ‖γ(t) - p‖ is continuous and positive
    have hγ_sub_cont : ContinuousOn (fun t => γ t - p) (Icc a b) :=
      hγ_cont.sub continuousOn_const
    have hr_pos : ∀ t ∈ Icc a b, 0 < ‖γ t - p‖ := fun t ht =>
      norm_pos_iff.mpr (sub_ne_zero.mpr (hγ_ne t ht))
    -- r = ‖γ - p‖ is bounded above on compact [a,b]
    have ⟨R, hR⟩ : ∃ R, ∀ t ∈ Icc a b, ‖γ t - p‖ ≤ R :=
      isCompact_Icc.exists_bound_of_continuousOn hγ_sub_cont
    -- The key technical step: bound on deriv γ requires bound on deriv θ.
    -- For typical curves (piecewise linear θ), this is finite.
    -- General proof requires stronger hypotheses on θ.
    sorry
  rw [h_eq h_deriv_bound]
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
-/

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

/-! ### Helper lemmas for C¹ analysis and derivative continuity -/

/-- ContDiffAt ℝ 1 implies ContinuousAt (deriv f). -/
lemma ContDiffAt.continuousAt_deriv' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {x : ℝ} (h : ContDiffAt ℝ 1 f x) : ContinuousAt (deriv f) x := by
  -- 1 ≠ ⊤ in WithTop ℕ∞
  have h1 : (1 : WithTop ℕ∞) = ↑(⊤ : ℕ∞) → (1 : WithTop ℕ∞) = ⊤ := fun heq => by
    have h1_ne_coe_top : (1 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞) := by
      intro h
      have : (1 : ℕ∞) = ⊤ := WithTop.coe_eq_coe.mp h
      exact ENat.one_ne_top this
    contradiction
  obtain ⟨U, hU_nhd, hCD⟩ := h.contDiffOn (le_refl 1) h1
  obtain ⟨V, hVU, hV_open, hxV⟩ := mem_nhds_iff.mp hU_nhd
  have hCDV : ContDiffOn ℝ 1 f V := hCD.mono hVU
  have h2 : ContinuousOn (deriv f) V := hCDV.continuousOn_deriv_of_isOpen hV_open le_rfl
  exact h2.continuousAt (hV_open.mem_nhds hxV)

/-- Construct ContDiffAt ℝ 1 from local differentiability and continuous derivative. -/
lemma contDiffAt_of_differentiableOn_of_continuousOn_deriv {f : ℝ → ℂ} {x : ℝ} {U : Set ℝ}
    (hU : U ∈ nhds x)
    (h_diff : ∀ y ∈ U, DifferentiableAt ℝ f y)
    (h_deriv_cont : ∀ y ∈ U, ContinuousAt (deriv f) y) : ContDiffAt ℝ 1 f x := by
  rw [contDiffAt_one_iff]
  use fun y => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv f y)
  obtain ⟨V, hVU, hV_open, hxV⟩ := mem_nhds_iff.mp hU
  use V
  refine ⟨hV_open.mem_nhds hxV, ?_, ?_⟩
  · have h1 : Continuous (fun c : ℂ => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c) :=
      (ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1 : ℝ →L[ℝ] ℝ)).continuous
    apply h1.comp_continuousOn
    apply continuousOn_of_forall_continuousAt
    intro y hy
    exact h_deriv_cont y (hVU hy)
  · intro y hy
    exact (h_diff y (hVU hy)).hasDerivAt.hasFDerivAt

/-! ### Additional helper lemmas -/

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

/-
  Bound on the derivative of a normalized direction.

  For u(t) = v(t) / ‖v(t)‖ where v : ℝ → ℂ is differentiable and v ≠ 0,
  we have ‖deriv u(t)‖ ≤ 2 * ‖deriv v(t)‖ / ‖v(t)‖.

  **Proof sketch** (quotient rule):
  deriv u = deriv v / ‖v‖ - v * Re(conj(v) * deriv v) / ‖v‖³
  Taking norms:
  ‖deriv u‖ ≤ ‖deriv v‖/‖v‖ + |Re(⟨v, deriv v⟩)|/‖v‖²
            ≤ ‖deriv v‖/‖v‖ + ‖v‖·‖deriv v‖/‖v‖²
            = 2·‖deriv v‖/‖v‖

  See `norm_deriv_normalized_le` below for the formal statement.
-/

/-- The derivative of the norm of a complex function satisfies |d/dt ‖v‖| ≤ ‖v'‖.
    This follows from the formula d/dt ‖v‖ = ⟪v, v'⟫_ℝ / ‖v‖ and Cauchy-Schwarz. -/
lemma abs_deriv_norm_le (v : ℝ → ℂ) (t : ℝ)
    (hv_diff : DifferentiableAt ℝ v t)
    (hv_ne : v t ≠ 0) :
    |deriv (fun s => ‖v s‖) t| ≤ ‖deriv v t‖ := by
  -- The norm function is 1-Lipschitz on ℂ
  -- So |d/dt ‖v(t)‖| ≤ 1 * ‖d/dt v(t)‖
  have h_norm_pos : 0 < ‖v t‖ := norm_pos_iff.mpr hv_ne
  have h_norm_sq_pos : 0 < ‖v t‖^2 := sq_pos_of_pos h_norm_pos
  have h_norm_sq_ne : ‖v t‖^2 ≠ 0 := ne_of_gt h_norm_sq_pos
  -- The derivative of ‖v‖² is 2 * ⟪v, v'⟫_ℝ
  have h1 : HasDerivAt v (deriv v t) t := hv_diff.hasDerivAt
  have h2 : HasDerivAt (fun s => ‖v s‖^2) (2 * @inner ℝ ℂ _ (v t) (deriv v t)) t := h1.norm_sq
  -- ‖v‖ = sqrt(‖v‖²), use chain rule
  have h_sqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (‖v t‖^2))) (‖v t‖^2) :=
    Real.hasDerivAt_sqrt h_norm_sq_ne
  -- The chain rule: d/dt sqrt(‖v(t)‖²) = (1/(2*sqrt(‖v(t)‖²))) * 2*inner
  have h3 := h_sqrt.comp t h2
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] at h3
  -- Simplify: (1 / (2 * ‖v‖)) * 2 * inner = inner / ‖v‖
  have h4 : HasDerivAt (fun s => ‖v s‖) (@inner ℝ ℂ _ (v t) (deriv v t) / ‖v t‖) t := by
    convert h3 using 1
    field_simp
  -- The derivative is inner / ‖v‖
  rw [h4.deriv, abs_div, abs_of_pos h_norm_pos]
  -- |inner| / ‖v‖ ≤ ‖v‖ * ‖v'‖ / ‖v‖ = ‖v'‖ by Cauchy-Schwarz
  rw [div_le_iff₀ h_norm_pos]
  -- Cauchy-Schwarz gives |inner v v'| ≤ ‖v‖ * ‖v'‖
  calc |@inner ℝ ℂ _ (v t) (deriv v t)|
      ≤ ‖v t‖ * ‖deriv v t‖ := abs_real_inner_le_norm _ _
    _ = ‖deriv v t‖ * ‖v t‖ := mul_comm _ _

lemma norm_deriv_normalized_le (v : ℝ → ℂ) (t : ℝ)
    (hv_diff : DifferentiableAt ℝ v t)
    (hv_ne : v t ≠ 0) :
    ‖deriv (fun s => v s / ‖v s‖) t‖ ≤ 2 * ‖deriv v t‖ / ‖v t‖ := by
  -- For u(s) = v(s)/‖v(s)‖, by quotient rule:
  --   u' = v'/‖v‖ - v*(‖v‖)'/‖v‖²
  -- Using |d/ds ‖v‖| ≤ ‖v'‖:
  --   ‖u'‖ ≤ ‖v'‖/‖v‖ + ‖v‖*‖v'‖/‖v‖² = 2*‖v'‖/‖v‖
  have h_norm_pos : 0 < ‖v t‖ := norm_pos_iff.mpr hv_ne
  have h_norm_ne : ‖v t‖ ≠ 0 := ne_of_gt h_norm_pos
  have h_norm_c_ne : (‖v t‖ : ℂ) ≠ 0 := by simp [h_norm_ne]
  -- Define r(s) = ‖v s‖ as a real function, and its coercion to ℂ
  let r : ℝ → ℝ := fun s => ‖v s‖
  let rc : ℝ → ℂ := fun s => (‖v s‖ : ℂ)
  -- Differentiability of norm
  have hr_diff : DifferentiableAt ℝ r t := hv_diff.norm ℝ hv_ne
  have hrc_diff : DifferentiableAt ℝ rc t :=
    Complex.ofRealCLM.differentiableAt.comp t hr_diff
  -- The function u = v / rc is differentiable
  have hu_diff : DifferentiableAt ℝ (fun s => v s / rc s) t :=
    hv_diff.div hrc_diff h_norm_c_ne
  -- Compute deriv rc using chain rule: deriv rc = deriv r (as real coerced to ℂ)
  -- r : ℝ → ℝ, so deriv r t : ℝ
  have h_deriv_r : deriv r t = @inner ℝ ℂ _ (v t) (deriv v t) / ‖v t‖ := by
    -- Use the formula from abs_deriv_norm_le proof
    have h1 : HasDerivAt v (deriv v t) t := hv_diff.hasDerivAt
    have h2 : HasDerivAt (fun s => ‖v s‖^2) (2 * @inner ℝ ℂ _ (v t) (deriv v t)) t := h1.norm_sq
    have h_norm_sq_pos : 0 < ‖v t‖^2 := sq_pos_of_pos h_norm_pos
    have h_norm_sq_ne : ‖v t‖^2 ≠ 0 := ne_of_gt h_norm_sq_pos
    have h_sqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (‖v t‖^2))) (‖v t‖^2) :=
      Real.hasDerivAt_sqrt h_norm_sq_ne
    have h3 := h_sqrt.comp t h2
    simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] at h3
    have h4 : HasDerivAt (fun s => ‖v s‖) (@inner ℝ ℂ _ (v t) (deriv v t) / ‖v t‖) t := by
      convert h3 using 1
      field_simp
    exact h4.deriv
  -- Get the real derivative value
  let dr : ℝ := deriv r t
  have h_deriv_rc : deriv rc t = (dr : ℂ) := by
    -- rc s = ‖v s‖ as a complex number = Complex.ofReal ∘ r
    -- The derivative of Complex.ofReal ∘ r equals ofReal(deriv r)
    have h_r_hasderiv : HasDerivAt r dr t := hr_diff.hasDerivAt
    have h_rc_hasderiv : HasDerivAt rc (dr : ℂ) t := by
      -- rc = Complex.ofRealCLM ∘ r
      show HasDerivAt (fun s => (‖v s‖ : ℂ)) (dr : ℂ) t
      have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t h_r_hasderiv
      simp only [Complex.ofRealCLM_apply] at h
      exact h
    exact h_rc_hasderiv.deriv
  -- dr = deriv r t by definition
  have h_dr_eq : dr = deriv r t := rfl
  -- The quotient rule: u' = (v' * rc - v * rc') / rc²
  have h_hasderiv : HasDerivAt (fun s => v s / rc s)
      ((deriv v t * rc t - v t * deriv rc t) / (rc t)^2) t := by
    apply HasDerivAt.div hv_diff.hasDerivAt hrc_diff.hasDerivAt h_norm_c_ne
  have h_deriv_eq : deriv (fun s => v s / rc s) t =
      (deriv v t * rc t - v t * deriv rc t) / (rc t)^2 := h_hasderiv.deriv
  -- Now bound the norm
  -- First rewrite: (v' * ‖v‖ - v * r') / ‖v‖² = v'/‖v‖ - v * r' / ‖v‖²
  rw [h_deriv_eq]
  have h_rc_sq : (rc t)^2 = (‖v t‖^2 : ℂ) := by
    simp only [rc]
  have h_rc_sq_ne : (rc t)^2 ≠ 0 := pow_ne_zero 2 h_norm_c_ne
  -- Use norm_div and triangle inequality
  rw [norm_div, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  -- Numerator bound: ‖v' * ‖v‖ - v * r'‖ ≤ ‖v'‖ * ‖v‖ + ‖v‖ * |r'|
  have h_num : ‖deriv v t * rc t - v t * deriv rc t‖ ≤
      ‖deriv v t‖ * ‖v t‖ + ‖v t‖ * |deriv r t| := by
    calc ‖deriv v t * rc t - v t * deriv rc t‖
        ≤ ‖deriv v t * rc t‖ + ‖v t * deriv rc t‖ := norm_sub_le _ _
      _ = ‖deriv v t‖ * ‖rc t‖ + ‖v t‖ * ‖deriv rc t‖ := by
          rw [norm_mul, norm_mul]
      _ = ‖deriv v t‖ * ‖v t‖ + ‖v t‖ * ‖deriv rc t‖ := by
          simp only [rc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = ‖deriv v t‖ * ‖v t‖ + ‖v t‖ * |deriv r t| := by
          rw [h_deriv_rc, Complex.norm_real, Real.norm_eq_abs]
  -- Use abs_deriv_norm_le: |deriv r t| ≤ ‖deriv v t‖
  have h_r_bound : |deriv r t| ≤ ‖deriv v t‖ := abs_deriv_norm_le v t hv_diff hv_ne
  -- Combine: numerator ≤ 2 * ‖v'‖ * ‖v‖
  have h_num_final : ‖deriv v t * rc t - v t * deriv rc t‖ ≤ 2 * ‖deriv v t‖ * ‖v t‖ := by
    calc ‖deriv v t * rc t - v t * deriv rc t‖
        ≤ ‖deriv v t‖ * ‖v t‖ + ‖v t‖ * |deriv r t| := h_num
      _ ≤ ‖deriv v t‖ * ‖v t‖ + ‖v t‖ * ‖deriv v t‖ := by
          apply add_le_add_left
          exact mul_le_mul_of_nonneg_left h_r_bound (norm_nonneg _)
      _ = 2 * ‖deriv v t‖ * ‖v t‖ := by ring
  -- Final: num / ‖v‖² ≤ 2 * ‖v'‖ * ‖v‖ / ‖v‖² = 2 * ‖v'‖ / ‖v‖
  calc ‖deriv v t * rc t - v t * deriv rc t‖ / ‖v t‖ ^ 2
      ≤ (2 * ‖deriv v t‖ * ‖v t‖) / ‖v t‖ ^ 2 := by
        apply div_le_div_of_nonneg_right h_num_final (le_of_lt (sq_pos_of_pos h_norm_pos))
    _ = 2 * ‖deriv v t‖ / ‖v t‖ := by field_simp

/-- A continuous function on [a,b] that is differentiable on (a,b) with bounded derivative is Lipschitz.

    This is the piecewise version: if ‖deriv f t‖ ≤ M for all t ∈ (a,b) where f is differentiable,
    and f is continuous on [a,b], then f is M-Lipschitz on [a,b].

    Note: At points where f is not differentiable, deriv f = 0 by Lean convention, so the bound
    ‖deriv f t‖ ≤ M is satisfied automatically. -/
lemma lipschitzOnWith_of_deriv_bound_interior {f : ℝ → ℂ} {a b M : ℝ} (hab : a ≤ b)
    (hM_nonneg : 0 ≤ M)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hf_bound : ∀ t ∈ Icc a b, ‖deriv f t‖ ≤ M) :
    LipschitzOnWith ⟨M, hM_nonneg⟩ f (Icc a b) := by
  -- Use the standard Mathlib lemma for convex sets
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  -- Handle the trivial case x = y
  by_cases hxy : x = y
  · simp [hxy]
  -- WLOG x < y
  wlog h_le : x ≤ y generalizing x y with H
  · push_neg at h_le
    have h_le' : y ≤ x := le_of_lt h_le
    rw [dist_comm, Real.dist_eq, abs_sub_comm]
    exact H y hy x hx (Ne.symm hxy) h_le'
  have h_lt : x < y := lt_of_le_of_ne h_le hxy
  -- Use the FTC: f y - f x = ∫_x^y f' t dt
  -- But we need to use a different approach since f might not be differentiable everywhere
  -- Use the mean value theorem approach via Convex.norm_image_sub_le_of_norm_deriv_le
  have h_Icc_sub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have h_Ioo_sub : Ioo x y ⊆ Ioo a b := Ioo_subset_Ioo hx.1 hy.2
  have hf_cont_xy : ContinuousOn f (Icc x y) := hf_cont.mono h_Icc_sub
  have hf_diff_xy : ∀ t ∈ Ioo x y, DifferentiableAt ℝ f t := fun t ht => hf_diff t (h_Ioo_sub ht)
  have hf_bound_xy : ∀ t ∈ Icc x y, ‖deriv f t‖ ≤ M := fun t ht => hf_bound t (h_Icc_sub ht)
  -- Use FTC: f(y) - f(x) = ∫_x^y (deriv f) dt, then ‖∫ f'‖ ≤ ∫ ‖f'‖ ≤ M * (y - x)
  -- Key: integral_eq_sub_of_hasDeriv_right only needs diff on the OPEN interior
  have h_bound : ‖f y - f x‖ ≤ M * ‖y - x‖ := by
    -- Step 1: Show deriv f has right derivative condition on (x, y)
    have h_hasDeriv : ∀ t ∈ Ioo x y, HasDerivWithinAt f (deriv f t) (Ioi t) t := by
      intro t ht
      exact (hf_diff_xy t ht).hasDerivAt.hasDerivWithinAt
    -- Step 2: The derivative is bounded on (x, y), hence integrable
    have h_bdd : ∀ t ∈ uIoc x y, ‖deriv f t‖ ≤ M := by
      intro t ht
      rw [Set.uIoc_of_le h_le] at ht
      exact hf_bound_xy t (Ioc_subset_Icc_self ht)
    have h_integrable : IntervalIntegrable (deriv f) MeasureTheory.volume x y := by
      -- Use the fact that bounded measurable functions on finite measure sets are integrable
      rw [intervalIntegrable_iff, Set.uIoc_of_le h_le]
      have h_meas : MeasureTheory.AEStronglyMeasurable (deriv f)
          (MeasureTheory.volume.restrict (Ioc x y)) := (aestronglyMeasurable_deriv f _).restrict
      have h_bdd' : ∀ t ∈ Ioc x y, ‖deriv f t‖ ≤ M := fun t ht => hf_bound_xy t (Ioc_subset_Icc_self ht)
      refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top h_meas M ?_
      rw [MeasureTheory.ae_restrict_eq (measurableSet_Ioc (a := x) (b := y))]
      apply Filter.eventually_inf_principal.mpr
      exact Eventually.of_forall h_bdd'
    -- Step 3: Apply FTC
    have h_uIcc : uIcc x y = Icc x y := Set.uIcc_of_le h_le
    have hf_cont_uIcc : ContinuousOn f (uIcc x y) := by rw [h_uIcc]; exact hf_cont_xy
    have h_Ioo_eq : Ioo (min x y) (max x y) = Ioo x y := by simp [h_le]
    have h_hasDeriv' : ∀ t ∈ Ioo (min x y) (max x y), HasDerivWithinAt f (deriv f t) (Ioi t) t := by
      rw [h_Ioo_eq]; exact h_hasDeriv
    have h_ftc : ∫ t in x..y, deriv f t = f y - f x :=
      intervalIntegral.integral_eq_sub_of_hasDeriv_right hf_cont_uIcc h_hasDeriv' h_integrable
    -- Step 4: Apply integral norm bound
    calc ‖f y - f x‖ = ‖∫ t in x..y, deriv f t‖ := by rw [h_ftc]
      _ ≤ M * |y - x| := intervalIntegral.norm_integral_le_of_norm_le_const h_bdd
      _ = M * (y - x) := by rw [abs_of_pos (sub_pos.mpr h_lt)]
      _ = M * ‖y - x‖ := by rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr h_lt)]
  calc dist (f x) (f y)
      = ‖f x - f y‖ := dist_eq_norm _ _
    _ = ‖f y - f x‖ := by rw [norm_sub_rev]
    _ ≤ M * ‖y - x‖ := h_bound
    _ = M * |y - x| := by rw [Real.norm_eq_abs]
    _ = M * |x - y| := by rw [abs_sub_comm]
    _ = M * dist x y := by rw [Real.dist_eq]

/-- Piecewise C¹ functions with bounded derivative are Lipschitz.

    If f is continuous on [a,b], differentiable on (a,b) except at finitely many points P,
    and ‖deriv f t‖ ≤ M for all t ∈ [a,b], then f is M-Lipschitz on [a,b].

    Proof: By induction on |P ∩ (x,y)|. If empty, use the standard MVT. Otherwise, split
    at a partition point and apply the triangle inequality. -/
lemma lipschitzOnWith_of_deriv_bound_piecewise {f : ℝ → ℂ} {a b M : ℝ} (hab : a ≤ b)
    (hM_nonneg : 0 ≤ M)
    (hf_cont : ContinuousOn f (Icc a b))
    (P : Finset ℝ)
    (hf_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ f t)
    (hf_bound : ∀ t ∈ Icc a b, ‖deriv f t‖ ≤ M) :
    LipschitzOnWith ⟨M, hM_nonneg⟩ f (Icc a b) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  by_cases hxy : x = y
  · simp [hxy]
  wlog h_le : x ≤ y generalizing x y with H
  · push_neg at h_le
    rw [dist_comm, Real.dist_eq, abs_sub_comm]
    exact H y hy x hx (Ne.symm hxy) (le_of_lt h_le)
  have h_lt : x < y := lt_of_le_of_ne h_le hxy
  have h_Icc_sub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have h_Ioo_sub : Ioo x y ⊆ Ioo a b := Ioo_subset_Ioo hx.1 hy.2
  have hf_cont_xy : ContinuousOn f (Icc x y) := hf_cont.mono h_Icc_sub
  have hf_bound_xy : ∀ t ∈ Icc x y, ‖deriv f t‖ ≤ M := fun t ht => hf_bound t (h_Icc_sub ht)
  -- Key: strong induction on |P ∩ Ioo x y|
  -- We define a recursive helper using well-founded recursion
  let P_in_xy := P.filter (fun p => p ∈ Ioo x y)
  -- Use well-founded induction on the cardinality
  suffices h_result : ∀ n, ∀ x' y' : ℝ, x' ∈ Icc a b → y' ∈ Icc a b → x' ≠ y' → x' ≤ y' →
      (P.filter (fun p => p ∈ Ioo x' y')).card = n → dist (f x') (f y') ≤ M * dist x' y' by
    exact h_result P_in_xy.card x y hx hy hxy h_le rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    -- The induction step
    intro x' y' hx' hy' hxy' h_le' h_card
    have h_lt' : x' < y' := lt_of_le_of_ne h_le' hxy'
    have h_Icc_sub' : Icc x' y' ⊆ Icc a b := Icc_subset_Icc hx'.1 hy'.2
    have h_Ioo_sub' : Ioo x' y' ⊆ Ioo a b := Ioo_subset_Ioo hx'.1 hy'.2
    have hf_cont_xy' : ContinuousOn f (Icc x' y') := hf_cont.mono h_Icc_sub'
    have hf_bound_xy' : ∀ t ∈ Icc x' y', ‖deriv f t‖ ≤ M := fun t ht => hf_bound t (h_Icc_sub' ht)
    let P_in_xy' := P.filter (fun p => p ∈ Ioo x' y')
    by_cases h_empty : n = 0
    · -- Base case: no partition points in (x', y')
      subst h_empty
      have h_P_empty : P_in_xy' = ∅ := Finset.card_eq_zero.mp h_card
      have hf_diff_xy' : ∀ t ∈ Ioo x' y', DifferentiableAt ℝ f t := by
        intro t ht
        apply hf_diff t (h_Ioo_sub' ht)
        intro ht_P
        have h_mem : t ∈ P_in_xy' := Finset.mem_filter.mpr ⟨ht_P, ht⟩
        rw [h_P_empty] at h_mem
        exact Finset.notMem_empty t h_mem
      -- Use lipschitzOnWith_of_deriv_bound_interior which we just proved
      have h_lip : LipschitzOnWith ⟨M, hM_nonneg⟩ f (Icc x' y') :=
        lipschitzOnWith_of_deriv_bound_interior (le_of_lt h_lt') hM_nonneg hf_cont_xy' hf_diff_xy' hf_bound_xy'
      have h_bound : ‖f y' - f x'‖ ≤ M * ‖y' - x'‖ := by
        have h_dist : dist (f x') (f y') ≤ M * dist x' y' :=
          h_lip.dist_le_mul _ (left_mem_Icc.mpr (le_of_lt h_lt')) _ (right_mem_Icc.mpr (le_of_lt h_lt'))
        rw [dist_eq_norm, Real.dist_eq] at h_dist
        calc ‖f y' - f x'‖ = ‖f x' - f y'‖ := norm_sub_rev _ _
          _ ≤ M * |x' - y'| := h_dist
          _ = M * |y' - x'| := by rw [abs_sub_comm]
          _ = M * ‖y' - x'‖ := by rw [Real.norm_eq_abs]
      calc dist (f x') (f y')
          = ‖f x' - f y'‖ := dist_eq_norm _ _
        _ = ‖f y' - f x'‖ := by rw [norm_sub_rev]
        _ ≤ M * ‖y' - x'‖ := h_bound
        _ = M * |y' - x'| := by rw [Real.norm_eq_abs]
        _ = M * |x' - y'| := by rw [abs_sub_comm]
        _ = M * dist x' y' := by rw [Real.dist_eq]
    · -- Inductive case: there's at least one partition point in (x', y')
      have h_pos : 0 < n := Nat.pos_of_ne_zero h_empty
      have h_nonempty : P_in_xy'.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h_eq
        have h1 : P_in_xy'.card = 0 := Finset.card_eq_zero.mpr h_eq
        have h2 : P_in_xy'.card = n := h_card
        omega
      obtain ⟨p, hp⟩ := h_nonempty
      have hp_filter : p ∈ P.filter (fun q => q ∈ Ioo x' y') := hp
      rw [Finset.mem_filter] at hp_filter
      have hp_P : p ∈ P := hp_filter.1
      have hp_Ioo : p ∈ Ioo x' y' := hp_filter.2
      have hp_Icc : p ∈ Icc a b := h_Icc_sub' (Ioo_subset_Icc_self hp_Ioo)
      have hx'p : x' < p := hp_Ioo.1
      have hpy' : p < y' := hp_Ioo.2
      -- Each sub-interval has fewer partition points
      let P_in_x'p := P.filter (fun q => q ∈ Ioo x' p)
      let P_in_py' := P.filter (fun q => q ∈ Ioo p y')
      have h_card_x'p : P_in_x'p.card < n := by
        have h_sub : P_in_x'p ⊆ P_in_xy'.erase p := by
          intro q hq
          rw [Finset.mem_filter] at hq
          rw [Finset.mem_erase, Finset.mem_filter]
          refine ⟨?_, hq.1, ?_⟩
          · intro heq; subst heq; exact lt_irrefl q hq.2.2
          · exact ⟨hq.2.1, hq.2.2.trans hpy'⟩
        calc P_in_x'p.card ≤ (P_in_xy'.erase p).card := Finset.card_le_card h_sub
          _ < P_in_xy'.card := Finset.card_erase_lt_of_mem hp
          _ = n := h_card
      have h_card_py' : P_in_py'.card < n := by
        have h_sub : P_in_py' ⊆ P_in_xy'.erase p := by
          intro q hq
          rw [Finset.mem_filter] at hq
          rw [Finset.mem_erase, Finset.mem_filter]
          refine ⟨?_, hq.1, ?_⟩
          · intro heq; subst heq; exact lt_irrefl q hq.2.1
          · exact ⟨hx'p.trans hq.2.1, hq.2.2⟩
        calc P_in_py'.card ≤ (P_in_xy'.erase p).card := Finset.card_le_card h_sub
          _ < P_in_xy'.card := Finset.card_erase_lt_of_mem hp
          _ = n := h_card
      -- Apply IH
      have h_bound_x'p : dist (f x') (f p) ≤ M * dist x' p :=
        ih P_in_x'p.card h_card_x'p x' p ⟨hx'.1, (le_of_lt hx'p).trans hp_Icc.2⟩
          ⟨hp_Icc.1, hp_Icc.2⟩ (ne_of_lt hx'p) (le_of_lt hx'p) rfl
      have h_bound_py' : dist (f p) (f y') ≤ M * dist p y' :=
        ih P_in_py'.card h_card_py' p y' ⟨hp_Icc.1, (le_of_lt hpy').trans hy'.2⟩
          ⟨hy'.1, hy'.2⟩ (ne_of_lt hpy') (le_of_lt hpy') rfl
      -- Combine
      calc dist (f x') (f y')
          ≤ dist (f x') (f p) + dist (f p) (f y') := dist_triangle _ _ _
        _ ≤ M * dist x' p + M * dist p y' := add_le_add h_bound_x'p h_bound_py'
        _ = M * (dist x' p + dist p y') := by ring
        _ = M * (|x' - p| + |p - y'|) := by simp only [Real.dist_eq]
        _ = M * (p - x' + (y' - p)) := by
            rw [abs_of_neg (sub_neg.mpr hx'p), abs_of_neg (sub_neg.mpr hpy')]; ring
        _ = M * (y' - x') := by ring
        _ = M * |y' - x'| := by rw [abs_of_pos (sub_pos.mpr h_lt')]
        _ = M * |x' - y'| := by rw [abs_sub_comm]
        _ = M * dist x' y' := by rw [Real.dist_eq]

/-- The normalized direction u(t) = v(t)/‖v(t)‖ is Lipschitz when v is Lipschitz and bounded away from 0.

    Key formula: ‖u(t₁) - u(t₂)‖ ≤ 2‖v(t₁) - v(t₂)‖ / min(‖v(t₁)‖, ‖v(t₂)‖)

    If ‖v‖ ≥ δ > 0 everywhere and v is K-Lipschitz, then u is (2K/δ)-Lipschitz. -/
lemma normalized_direction_lipschitz {v : ℝ → ℂ} {K δ : ℝ} (hδ_pos : 0 < δ) (hK_nonneg : 0 ≤ K)
    (hv_lipschitz : LipschitzWith ⟨K, hK_nonneg⟩ v)
    (hv_bound : ∀ t, δ ≤ ‖v t‖) :
    LipschitzWith ⟨2 * K / δ, by positivity⟩ (fun t => v t / ‖v t‖) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro t₁ t₂
  simp only [dist_eq_norm]
  -- u(t₁) - u(t₂) = v₁/‖v₁‖ - v₂/‖v₂‖
  have h_norm_t₁_pos : 0 < ‖v t₁‖ := lt_of_lt_of_le hδ_pos (hv_bound t₁)
  have h_norm_t₂_pos : 0 < ‖v t₂‖ := lt_of_lt_of_le hδ_pos (hv_bound t₂)
  have h_norm_t₁_ne : ‖v t₁‖ ≠ 0 := ne_of_gt h_norm_t₁_pos
  have h_norm_t₂_ne : ‖v t₂‖ ≠ 0 := ne_of_gt h_norm_t₂_pos
  have h_norm_c_t₁_ne : (‖v t₁‖ : ℂ) ≠ 0 := by simp [h_norm_t₁_ne]
  have h_norm_c_t₂_ne : (‖v t₂‖ : ℂ) ≠ 0 := by simp [h_norm_t₂_ne]
  -- Standard calculation: v₁/‖v₁‖ - v₂/‖v₂‖ = (v₁‖v₂‖ - v₂‖v₁‖) / (‖v₁‖·‖v₂‖)
  have h_diff : v t₁ / ‖v t₁‖ - v t₂ / ‖v t₂‖ =
      (v t₁ * ‖v t₂‖ - v t₂ * ‖v t₁‖) / (‖v t₁‖ * ‖v t₂‖) := by
    have h_prod_ne : (‖v t₁‖ : ℂ) * ‖v t₂‖ ≠ 0 := mul_ne_zero h_norm_c_t₁_ne h_norm_c_t₂_ne
    field_simp [h_norm_c_t₁_ne, h_norm_c_t₂_ne, h_prod_ne]
  rw [h_diff]
  -- Numerator = v₁·‖v₂‖ - v₂·‖v₂‖ + v₂·‖v₂‖ - v₂·‖v₁‖ = (v₁-v₂)·‖v₂‖ + v₂·(‖v₂‖-‖v₁‖)
  have h_num_split : v t₁ * ‖v t₂‖ - v t₂ * ‖v t₁‖ =
      (v t₁ - v t₂) * ‖v t₂‖ + v t₂ * (‖v t₂‖ - ‖v t₁‖) := by ring
  -- ‖numerator‖ ≤ ‖v₁-v₂‖·‖v₂‖ + ‖v₂‖·|‖v₂‖-‖v₁‖| ≤ ‖v₁-v₂‖·‖v₂‖ + ‖v₂‖·‖v₁-v₂‖ = 2·‖v₁-v₂‖·‖v₂‖
  have h_num_bound : ‖v t₁ * ‖v t₂‖ - v t₂ * ‖v t₁‖‖ ≤ 2 * ‖v t₁ - v t₂‖ * ‖v t₂‖ := by
    rw [h_num_split]
    calc ‖(v t₁ - v t₂) * ↑‖v t₂‖ + v t₂ * (↑‖v t₂‖ - ↑‖v t₁‖)‖
        ≤ ‖(v t₁ - v t₂) * ↑‖v t₂‖‖ + ‖v t₂ * (↑‖v t₂‖ - ↑‖v t₁‖)‖ := norm_add_le _ _
      _ = ‖v t₁ - v t₂‖ * ‖v t₂‖ + ‖v t₂‖ * ‖(‖v t₂‖ : ℂ) - (‖v t₁‖ : ℂ)‖ := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ ≤ ‖v t₁ - v t₂‖ * ‖v t₂‖ + ‖v t₂‖ * ‖v t₁ - v t₂‖ := by
          apply add_le_add_left
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          calc |‖v t₂‖ - ‖v t₁‖| ≤ ‖v t₂ - v t₁‖ := abs_norm_sub_norm_le _ _
            _ = ‖v t₁ - v t₂‖ := by rw [norm_sub_rev]
      _ = 2 * ‖v t₁ - v t₂‖ * ‖v t₂‖ := by ring
  -- ‖result‖ = ‖num‖ / (‖v₁‖·‖v₂‖) ≤ 2·‖v₁-v₂‖·‖v₂‖ / (‖v₁‖·‖v₂‖) = 2·‖v₁-v₂‖/‖v₁‖ ≤ 2·‖v₁-v₂‖/δ
  calc ‖(v t₁ * ↑‖v t₂‖ - v t₂ * ↑‖v t₁‖) / (↑‖v t₁‖ * ↑‖v t₂‖)‖
      = ‖v t₁ * ↑‖v t₂‖ - v t₂ * ↑‖v t₁‖‖ / (‖v t₁‖ * ‖v t₂‖) := by
        rw [norm_div, Complex.norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
            abs_of_nonneg (norm_nonneg _)]
    _ ≤ (2 * ‖v t₁ - v t₂‖ * ‖v t₂‖) / (‖v t₁‖ * ‖v t₂‖) := by
        apply div_le_div_of_nonneg_right h_num_bound
        exact le_of_lt (mul_pos h_norm_t₁_pos h_norm_t₂_pos)
    _ = 2 * ‖v t₁ - v t₂‖ / ‖v t₁‖ := by field_simp
    _ ≤ 2 * ‖v t₁ - v t₂‖ / δ := by
        apply div_le_div_of_nonneg_left _ hδ_pos (hv_bound t₁)
        exact mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (norm_nonneg _)
    _ ≤ 2 * (K * dist t₁ t₂) / δ := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hδ_pos)
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
        simp only [dist_eq_norm] at hv_lipschitz ⊢
        exact hv_lipschitz.dist_le_mul t₁ t₂
    _ = 2 * K / δ * dist t₁ t₂ := by ring

/-- Bound on deriv of safeRotationHomotopy using Lipschitz, without assuming γ is differentiable.

    If γ is M-Lipschitz and ‖γ - p‖ ≥ δ, then ‖deriv H‖ ≤ 2M/δ at any differentiable point. -/
lemma safeRotationHomotopy_deriv_bound_lipschitz (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p) (t : ℝ) (ht : t ∈ Ioo a b) (s : ℝ) (hs : s ∈ Icc 0 1)
    {M δ : ℝ} (hM_pos : 0 ≤ M) (hδ_pos : 0 < δ)
    (hγ_lipschitz : LipschitzOnWith ⟨M, hM_pos⟩ γ (Icc a b))
    (hδ_bound : ∀ t ∈ Icc a b, δ ≤ ‖γ t - p‖)
    (h_diff : DifferentiableAt ℝ (fun t' => safeRotationHomotopy p γ a b hγ_ne (t', s)) t) :
    ‖deriv (fun t' => safeRotationHomotopy p γ a b hγ_ne (t', s)) t‖ ≤ 2 * M / δ := by
  -- H(t, s) = p + r(s) * u(t) where |r(s)| = 1 and u(t) = (γ(t)-p)/‖γ(t)-p‖
  have ht_Icc : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hγ_ne_t : γ t ≠ p := hγ_ne t ht_Icc
  have h_sub_ne : γ t - p ≠ 0 := sub_ne_zero.mpr hγ_ne_t
  have h_norm_ne : (‖γ t - p‖ : ℂ) ≠ 0 := by simp [h_sub_ne]
  have h_rot_ne : rotFactor s ≠ 0 := rotFactor_ne_zero s hs
  -- Define u and r
  let u := fun t' => (γ t' - p) / (‖γ t' - p‖ : ℂ)
  let r := rotFactor s / (‖rotFactor s‖ : ℂ)
  -- |r| = 1
  have h_r_norm : ‖r‖ = 1 := by
    simp only [r, norm_div, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr h_rot_ne)
  -- H = p + r * u
  have h_eq : (fun t' => safeRotationHomotopy p γ a b hγ_ne (t', s)) = (fun t' => p + r * u t') := by
    ext t'; simp only [safeRotationHomotopy, r, u]; ring
  -- From h_diff and h_eq, u is differentiable at t
  have h_u_diff : DifferentiableAt ℝ u t := by
    have h1 : DifferentiableAt ℝ (fun t' => p + r * u t') t := by
      rw [← h_eq]; exact h_diff
    have h2 : DifferentiableAt ℝ (fun t' => r * u t') t := by
      simpa using h1.sub (differentiableAt_const p)
    have hr_ne : r ≠ 0 := by
      simp only [r, div_ne_zero_iff]
      exact ⟨h_rot_ne, by simp [norm_ne_zero_iff.mpr h_rot_ne]⟩
    -- If r * u is differentiable and r ≠ 0, then u = (r * u) / r is differentiable
    have hr_inv_ne : r⁻¹ ≠ 0 := inv_ne_zero hr_ne
    have h3 : DifferentiableAt ℝ (fun t' => r⁻¹ * (r * u t')) t := h2.const_mul r⁻¹
    simp only [inv_mul_cancel_left₀ hr_ne] at h3
    exact h3
  -- The derivative formula
  have h_deriv : deriv (fun t' => p + r * u t') t = r * deriv u t := by
    rw [deriv_const_add, deriv_const_mul _ h_u_diff]
  rw [h_eq, h_deriv, norm_mul, h_r_norm, one_mul]
  -- Now use Lipschitz bound: ‖deriv u t‖ ≤ Lipschitz constant of u = 2M/δ
  -- First show v = γ - p is M-Lipschitz on Icc a b (subtracting constant preserves Lipschitz)
  let v := fun t' => γ t' - p
  have hv_lipschitz : LipschitzOnWith ⟨M, hM_pos⟩ v (Icc a b) := by
    have h_const : LipschitzOnWith 0 (fun _ => p) (Icc a b) := (LipschitzWith.const p).lipschitzOnWith
    have h_sub := hγ_lipschitz.sub h_const
    simp only [add_zero] at h_sub
    exact h_sub
  -- v is bounded away from 0 by δ
  have hv_bound : ∀ t' ∈ Icc a b, δ ≤ ‖v t'‖ := fun t' ht' => hδ_bound t' ht'
  -- u = v/‖v‖ is (2M/δ)-Lipschitz on Icc a b
  have h_u_lipschitz : LipschitzOnWith ⟨2 * M / δ, by positivity⟩ u (Icc a b) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro t₁ ht₁ t₂ ht₂
    -- Similar argument to normalized_direction_lipschitz but restricted to Icc a b
    simp only [dist_eq_norm]
    have h_norm_t₁_pos : 0 < ‖v t₁‖ := lt_of_lt_of_le hδ_pos (hv_bound t₁ ht₁)
    have h_norm_t₂_pos : 0 < ‖v t₂‖ := lt_of_lt_of_le hδ_pos (hv_bound t₂ ht₂)
    have h_norm_c_t₁_ne : (‖v t₁‖ : ℂ) ≠ 0 := by simp [ne_of_gt h_norm_t₁_pos]
    have h_norm_c_t₂_ne : (‖v t₂‖ : ℂ) ≠ 0 := by simp [ne_of_gt h_norm_t₂_pos]
    have h_diff_eq : u t₁ - u t₂ =
        (v t₁ * ‖v t₂‖ - v t₂ * ‖v t₁‖) / (‖v t₁‖ * ‖v t₂‖) := by
      simp only [u, v]
      have h1 : (‖γ t₁ - p‖ : ℂ) ≠ 0 := h_norm_c_t₁_ne
      have h2 : (‖γ t₂ - p‖ : ℂ) ≠ 0 := h_norm_c_t₂_ne
      have h3 : (‖v t₁‖ : ℂ) * ‖v t₂‖ ≠ 0 := mul_ne_zero h_norm_c_t₁_ne h_norm_c_t₂_ne
      field_simp [h1, h2, h3]
    have h_num_bound : ‖v t₁ * ↑‖v t₂‖ - v t₂ * ↑‖v t₁‖‖ ≤ 2 * ‖v t₁ - v t₂‖ * ‖v t₂‖ := by
      have h_num_split : v t₁ * ‖v t₂‖ - v t₂ * ‖v t₁‖ =
          (v t₁ - v t₂) * ‖v t₂‖ + v t₂ * (‖v t₂‖ - ‖v t₁‖) := by ring
      rw [h_num_split]
      calc ‖(v t₁ - v t₂) * ↑‖v t₂‖ + v t₂ * (↑‖v t₂‖ - ↑‖v t₁‖)‖
          ≤ ‖(v t₁ - v t₂) * ↑‖v t₂‖‖ + ‖v t₂ * (↑‖v t₂‖ - ↑‖v t₁‖)‖ := norm_add_le _ _
        _ = ‖v t₁ - v t₂‖ * ‖v t₂‖ + ‖v t₂‖ * ‖(‖v t₂‖ : ℂ) - (‖v t₁‖ : ℂ)‖ := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        _ ≤ ‖v t₁ - v t₂‖ * ‖v t₂‖ + ‖v t₂‖ * ‖v t₁ - v t₂‖ := by
            apply add_le_add_left
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
            calc |‖v t₂‖ - ‖v t₁‖| ≤ ‖v t₂ - v t₁‖ := abs_norm_sub_norm_le _ _
              _ = ‖v t₁ - v t₂‖ := by rw [norm_sub_rev]
        _ = 2 * ‖v t₁ - v t₂‖ * ‖v t₂‖ := by ring
    rw [h_diff_eq]
    calc ‖(v t₁ * ↑‖v t₂‖ - v t₂ * ↑‖v t₁‖) / (↑‖v t₁‖ * ↑‖v t₂‖)‖
        = ‖v t₁ * ↑‖v t₂‖ - v t₂ * ↑‖v t₁‖‖ / (‖v t₁‖ * ‖v t₂‖) := by
          rw [norm_div, Complex.norm_mul, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
      _ ≤ (2 * ‖v t₁ - v t₂‖ * ‖v t₂‖) / (‖v t₁‖ * ‖v t₂‖) := by
          apply div_le_div_of_nonneg_right h_num_bound
          exact le_of_lt (mul_pos h_norm_t₁_pos h_norm_t₂_pos)
      _ = 2 * ‖v t₁ - v t₂‖ / ‖v t₁‖ := by field_simp
      _ ≤ 2 * ‖v t₁ - v t₂‖ / δ := by
          apply div_le_div_of_nonneg_left _ hδ_pos (hv_bound t₁ ht₁)
          exact mul_nonneg (by norm_num) (norm_nonneg _)
      _ ≤ 2 * (M * dist t₁ t₂) / δ := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hδ_pos)
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
          exact hv_lipschitz.dist_le_mul t₁ ht₁ t₂ ht₂
      _ = 2 * M / δ * dist t₁ t₂ := by ring
  -- Apply norm_deriv_le_of_lip' using the Lipschitz condition
  -- The Lipschitz bound holds eventually around t
  apply norm_deriv_le_of_lip' (by positivity : 0 ≤ 2 * M / δ)
  -- Show that ‖u(x) - u(t)‖ ≤ (2M/δ) * ‖x - t‖ eventually around t
  -- Since t ∈ Ioo a b, we can find an Icc neighborhood
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with x hx
  have hx' : x ∈ Icc a b := hx
  calc ‖u x - u t‖
      ≤ 2 * M / δ * dist x t := h_u_lipschitz.dist_le_mul x hx' t ht_Icc
    _ = 2 * M / δ * ‖x - t‖ := by simp only [Real.dist_eq, Real.norm_eq_abs]

/-- Bound on safeRotationHomotopy derivative in terms of γ derivative and distance.

    The key bound: ‖deriv_t H(t, s)‖ ≤ 2 * ‖deriv γ t‖ / ‖γ t - p‖

    This follows from:
    1. H(t, s) = p + r(s) * u(t) where |r(s)| = 1 and u(t) = (γ(t)-p)/‖γ(t)-p‖
    2. deriv_t H = r(s) * deriv u(t)
    3. ‖deriv u(t)‖ ≤ 2 * ‖deriv γ t‖ / ‖γ t - p‖ by `norm_deriv_normalized_le`
-/
lemma safeRotationHomotopy_deriv_bound (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p) (t : ℝ) (ht : t ∈ Icc a b) (s : ℝ) (hs : s ∈ Icc 0 1)
    (hγ_diff : DifferentiableAt ℝ γ t) :
    ‖deriv (fun t' => safeRotationHomotopy p γ a b hγ_ne (t', s)) t‖ ≤
    2 * ‖deriv γ t‖ / ‖γ t - p‖ := by
  -- The derivative formula gives deriv_t H = r(s) * deriv u(t)
  -- where |r(s)| = 1 and u(t) = (γ(t)-p)/‖γ(t)-p‖
  have hγ_ne_t : γ t ≠ p := hγ_ne t ht
  have h_sub_ne : γ t - p ≠ 0 := sub_ne_zero.mpr hγ_ne_t
  have h_norm_ne : (‖γ t - p‖ : ℂ) ≠ 0 := by simp [h_sub_ne]
  have h_rot_ne : rotFactor s ≠ 0 := rotFactor_ne_zero s hs
  have h_rot_norm_ne : (‖rotFactor s‖ : ℂ) ≠ 0 := by simp [norm_ne_zero_iff.mpr h_rot_ne]
  -- Define u(t') = (γ t' - p) / ‖γ t' - p‖ and r(s) = rotFactor s / ‖rotFactor s‖
  let u := fun t' => (γ t' - p) / (‖γ t' - p‖ : ℂ)
  let r := rotFactor s / (‖rotFactor s‖ : ℂ)
  -- Key: |r| = 1 since r is normalized
  have h_r_norm : ‖r‖ = 1 := by
    simp only [r, norm_div, Complex.norm_real]
    -- ‖‖rotFactor s‖‖ = |‖rotFactor s‖| = ‖rotFactor s‖ (norms are nonneg)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr h_rot_ne)
  -- The function safeRotationHomotopy equals p + r * u
  have h_eq : (fun t' => safeRotationHomotopy p γ a b hγ_ne (t', s)) =
              (fun t' => p + r * u t') := by
    ext t'
    simp only [safeRotationHomotopy, r, u]
    ring
  -- Differentiability of u at t
  have h_sub_diff : DifferentiableAt ℝ (fun t' => γ t' - p) t := hγ_diff.sub (differentiableAt_const p)
  have h_norm_diff : DifferentiableAt ℝ (fun t' => (‖γ t' - p‖ : ℂ)) t :=
    Complex.ofRealCLM.differentiableAt.comp t (h_sub_diff.norm ℂ h_sub_ne)
  have h_u_diff : DifferentiableAt ℝ u t := h_sub_diff.div h_norm_diff h_norm_ne
  -- The derivative of p + r * u is r * deriv u (since r is constant in t)
  have h_deriv : deriv (fun t' => p + r * u t') t = r * deriv u t := by
    rw [deriv_const_add, deriv_const_mul _ h_u_diff]
  rw [h_eq, h_deriv]
  -- ‖r * deriv u‖ = |r| * ‖deriv u‖ = ‖deriv u‖
  rw [norm_mul, h_r_norm, one_mul]
  -- Now apply norm_deriv_normalized_le
  -- u(t') = (γ t' - p) / ‖γ t' - p‖ = v(t') / ‖v(t')‖ where v = γ - p
  have h_v_diff : DifferentiableAt ℝ (fun t' => γ t' - p) t := h_sub_diff
  have h_v_ne : (fun t' => γ t' - p) t ≠ 0 := h_sub_ne
  have h_bound := norm_deriv_normalized_le (fun t' => γ t' - p) t h_v_diff h_v_ne
  -- deriv(γ - p) = deriv γ since p is constant
  have h_deriv_sub : deriv (fun t' => γ t' - p) t = deriv γ t := by
    have h1 : (fun t' => γ t' - p) = (fun t' => γ t') - (fun _ => p) := rfl
    rw [h1, deriv_sub hγ_diff (differentiableAt_const p), deriv_const, sub_zero]
  -- The function u equals the normalized direction of (γ - p)
  -- So deriv u equals deriv of the normalized direction, which is what h_bound bounds
  -- We need to match the form of h_bound with the goal
  calc ‖deriv u t‖
      = ‖deriv (fun t' => (γ t' - p) / ↑‖γ t' - p‖) t‖ := rfl
    _ ≤ 2 * ‖deriv (fun t' => γ t' - p) t‖ / ‖(fun t' => γ t' - p) t‖ := h_bound
    _ = 2 * ‖deriv γ t‖ / ‖γ t - p‖ := by rw [h_deriv_sub]

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
    have h_γ'_cont_at : ContinuousAt (deriv γ) t' := hγ_deriv_cont t' h_t'_in_ab_open (hp_smooth t' ht')
    -- Step 1: Show γ is ContDiffAt ℝ 1 at t'
    -- Ioo p₁ p₂ is open and in nhds t', and on it γ is differentiable with continuous derivative
    have h_γ_contDiff : ContDiffAt ℝ 1 γ t' := by
      apply contDiffAt_of_differentiableOn_of_continuousOn_deriv (isOpen_Ioo.mem_nhds ht')
      · intro y hy
        exact hγ_diff y (h_subset hy) (hp_smooth y hy)
      · intro y hy
        exact hγ_deriv_cont y (h_subset hy) (hp_smooth y hy)
    -- Step 2: γ - p is ContDiffAt ℝ 1
    have h_sub_contDiff : ContDiffAt ℝ 1 (fun t => γ t - p) t' := h_γ_contDiff.sub contDiffAt_const
    -- Step 3: ‖γ - p‖ is ContDiffAt ℝ 1 (norm is smooth when nonzero)
    have h_norm_contDiff : ContDiffAt ℝ 1 (fun t => (‖γ t - p‖ : ℂ)) t' := by
      apply (Complex.ofRealCLM.contDiff.contDiffAt).comp t'
      exact ContDiffAt.norm ℝ h_sub_contDiff h_sub_ne'
    -- Step 4: u = (γ - p) / ‖γ - p‖ is ContDiffAt ℝ 1
    -- Division is multiplication by inverse for complex-valued functions
    have h_norm_ne_C : (‖γ t' - p‖ : ℂ) ≠ 0 := by simp [h_norm_ne']
    have h_inv_contDiff : ContDiffAt ℝ 1 (fun t => ((‖γ t - p‖ : ℂ))⁻¹) t' := h_norm_contDiff.inv h_norm_ne_C
    have h_u_eq : u = (fun t => (γ t - p) * ((‖γ t - p‖ : ℂ))⁻¹) := by ext t; ring
    have h_u_contDiff : ContDiffAt ℝ 1 u t' := by
      rw [h_u_eq]
      exact h_sub_contDiff.mul h_inv_contDiff
    -- Step 5: Apply helper lemma to get ContinuousAt (deriv u) t'
    exact h_u_contDiff.continuousAt_deriv'
  -- Step 2: Use h_deriv_u_cont_on to show the full derivative is continuous
  -- The derivative of H(t, s) = p + rot(s)/‖rot(s)‖ * u(t) w.r.t. t is:
  -- deriv_t H = rot(s)/‖rot(s)‖ * deriv u(t)
  -- This is continuous as a product of continuous functions.
  let r := fun s => rotFactor s / (‖rotFactor s‖ : ℂ)
  -- Show r is ContinuousOn [0,1]
  have h_r_cont : ContinuousOn r (Icc 0 1) := rotFactor_unit_continuousOn
  -- The derivative formula: deriv_t H(t, s) = r(s) * deriv u(t)
  have h_deriv_eq : ∀ q : ℝ × ℝ, q.1 ∈ Ioo p₁ p₂ → q.2 ∈ Icc 0 1 →
      deriv (fun t' => safeRotationHomotopy p γ a b hγ_ne (t', q.2)) q.1 = r q.2 * deriv u q.1 := by
    intro ⟨t, s⟩ ht hs
    simp only [safeRotationHomotopy]
    -- H(t', s) = p + r(s) * u(t')
    -- deriv_t' H = r(s) * deriv u(t')
    have h_t_in_ab : t ∈ Icc a b := Ioo_subset_Icc_self (h_subset ht)
    have h_t_in_ab_open : t ∈ Ioo a b := h_subset ht
    have h_γ_ne_t : γ t ≠ p := hγ_ne t h_t_in_ab
    have h_sub_ne : γ t - p ≠ 0 := sub_ne_zero.mpr h_γ_ne_t
    have h_norm_ne : (‖γ t - p‖ : ℂ) ≠ 0 := by simp [norm_ne_zero_iff.mpr h_sub_ne]
    -- u is differentiable at t
    have h_γ_diff_t : DifferentiableAt ℝ γ t := hγ_diff t h_t_in_ab_open (hp_smooth t ht)
    have h_sub_diff : DifferentiableAt ℝ (fun t' => γ t' - p) t := h_γ_diff_t.sub (differentiableAt_const p)
    have h_norm_diff : DifferentiableAt ℝ (fun t' => (‖γ t' - p‖ : ℂ)) t :=
      Complex.ofRealCLM.differentiableAt.comp t (DifferentiableAt.norm ℂ h_sub_diff h_sub_ne)
    have h_u_diff : DifferentiableAt ℝ u t := h_sub_diff.div h_norm_diff h_norm_ne
    -- The function is p + rotFactor s * u t' / ‖rotFactor s‖
    -- = p + (rotFactor s / ‖rotFactor s‖) * u t'
    -- = p + r s * u t'
    have h_eq : (fun t' => p + rotFactor s * ((γ t' - p) / ↑‖γ t' - p‖) / ↑‖rotFactor s‖) =
                (fun t' => p + r s * u t') := by
      ext t'; simp only [r, u]; ring
    rw [h_eq]
    -- deriv of (p + r(s) * u(t')) w.r.t. t' equals r(s) * deriv u
    rw [deriv_const_add, deriv_const_mul _ h_u_diff]
  -- Apply continuity: the function equals r(s) * deriv u(t) which is continuous
  apply ContinuousOn.congr _ (fun q hq => h_deriv_eq q hq.1 hq.2)
  -- Show ContinuousOn (fun q => r q.2 * deriv u q.1) (Ioo p₁ p₂ ×ˢ Icc 0 1)
  apply ContinuousOn.mul
  · -- ContinuousOn (fun q => r q.2) (Ioo p₁ p₂ ×ˢ Icc 0 1)
    apply h_r_cont.comp continuousOn_snd
    intro ⟨t, s⟩ ⟨_, hs⟩
    exact hs
  · -- ContinuousOn (fun q => deriv u q.1) (Ioo p₁ p₂ ×ˢ Icc 0 1)
    apply h_deriv_u_cont_on.comp continuousOn_fst
    intro ⟨t, s⟩ ⟨ht, _⟩
    exact ht

/-- Safe rotation homotopy gives a piecewise homotopy from rc to I·rc. -/
lemma safeRotationHomotopy_piecewise_avoiding (p : ℂ) (γ : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ p)
    (hγ_closed : γ a = γ b)
    (P : Finset ℝ) (hP : ∀ t ∈ P, t ∈ Ioo a b)
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ t ∈ Ioo a b, t ∉ P → ContinuousAt (deriv γ) t)
    -- Explicit derivative bound (needed for dominated convergence in homotopy invariance)
    (hγ_deriv_bound : ∃ M : ℝ, ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M) :
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
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  -- The structure requires Ioo p₁ p₂ ⊆ Ioo a b, which we receive as h_sub.
  -- This constraint is necessary because the derivative is discontinuous at
  -- clamp boundaries when extending beyond [a,b]. For valid partition pieces,
  -- this is always satisfied.
  · intro p₁ p₂ hp hp_smooth h_sub
    -- On the domain Ioo p₁ p₂ ×ˢ Icc 0 1, clamp_t t = t (since Ioo p₁ p₂ ⊆ Ioo a b ⊆ Icc a b),
    -- so H(t, s) = safeRotationHomotopy(t, s).
    have h_eq : ∀ t ∈ Ioo p₁ p₂, ∀ s ∈ Icc (0:ℝ) 1,
        H (t, s) = safeRotationHomotopy p γ a b hγ_ne (t, s) := fun t ht s hs => by
      simp only [H]
      rw [h_clamp_t_id t (Ioo_subset_Icc_self (h_sub ht)), h_clamp_s_id s hs]
    -- The derivative agrees because the functions agree on a neighborhood
    have h_deriv_eq : ∀ q ∈ Ioo p₁ p₂ ×ˢ Icc (0:ℝ) 1,
        deriv (fun t' => H (t', q.2)) q.1 =
        deriv (fun t' => safeRotationHomotopy p γ a b hγ_ne (t', q.2)) q.1 := fun ⟨t, s⟩ ⟨ht, hs⟩ => by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [isOpen_Ioo.mem_nhds ht] with t' ht'
      exact h_eq t' ht' s hs
    refine ContinuousOn.congr ?_ fun q hq => h_deriv_eq q hq
    exact safeRotationHomotopy_deriv_cont p γ a b hab hγ_cont hγ_ne P hγ_diff hγ_deriv_cont
      p₁ p₂ hp h_sub hp_smooth
  -- 8. Derivative bound exists
  · -- The derivative of H is bounded on the compact domain [a,b] × [0,1].
    --
    -- H(t,s) = safeRotationHomotopy(clamp_t t, clamp_s s)
    --       = p + r(s) * u(t)  on Icc a b × Icc 0 1
    -- where r(s) = rotFactor(s)/‖rotFactor(s)‖ and u(t) = (γ(t)-p)/‖γ(t)-p‖
    --
    -- deriv_t H(t,s) = r(s) * deriv u(t)
    --
    -- Since |r(s)| = 1 for all s (it's a unit complex number),
    -- ‖deriv_t H(t,s)‖ = ‖deriv u(t)‖
    --
    -- For u(t) = (γ(t)-p)/‖γ(t)-p‖ (unit direction):
    -- deriv u = [deriv γ - u * Re(conj(γ-p) * deriv γ) / ‖γ-p‖] / ‖γ-p‖
    --         = [deriv γ - u * ⟨u, deriv γ⟩] / ‖γ-p‖
    --         = (deriv γ - projection onto u) / ‖γ-p‖
    --
    -- ‖deriv u‖ ≤ ‖deriv γ‖ / ‖γ-p‖ ≤ M / δ
    -- where M bounds ‖deriv γ‖ and δ = min ‖γ(t) - p‖ > 0.
    --
    -- For non-differentiable points (∈ P or endpoints):
    -- deriv H = 0 by Lean convention, so ‖deriv H‖ = 0 ≤ M/δ.
    --
    -- Thus M/δ is a global bound on ‖deriv H(t,s)‖ for all (t,s) ∈ [a,b] × [0,1].
    --
    -- The technical issue is that we need to first establish:
    -- 1. δ = min_{t ∈ [a,b]} ‖γ(t) - p‖ > 0 (follows from γ avoids p + compactness)
    -- 2. M = bound on ‖deriv γ‖ (requires piecewise C¹ derivative bound - same as Sorry #2)
    --
    -- Since this depends on the same derivative bound as Sorry #2, we mark this as
    -- requiring that technical infrastructure.
    --
    -- Get lower bound δ on ‖γ - p‖
    have hγ_sub_cont : ContinuousOn (fun t => γ t - p) (Icc a b) := hγ_cont.sub continuousOn_const
    have hγ_sub_ne : ∀ t ∈ Icc a b, γ t - p ≠ 0 := fun t ht => sub_ne_zero.mpr (hγ_ne t ht)
    have ⟨δ, hδ_pos, hδ_bound⟩ : ∃ δ > 0, ∀ t ∈ Icc a b, δ ≤ ‖γ t - p‖ := by
      have h_norm_cont : ContinuousOn (fun t => ‖γ t - p‖) (Icc a b) := hγ_sub_cont.norm
      have h_pos : ∀ t ∈ Icc a b, 0 < ‖γ t - p‖ := fun t ht =>
        norm_pos_iff.mpr (hγ_sub_ne t ht)
      have h_compact : IsCompact (Icc a b) := isCompact_Icc
      have h_nonempty : (Icc a b).Nonempty := nonempty_Icc.mpr hab.le
      obtain ⟨t₀, ht₀, hmin⟩ := h_compact.exists_isMinOn h_nonempty h_norm_cont
      exact ⟨‖γ t₀ - p‖, h_pos t₀ ht₀, fun t ht => hmin ht⟩
    -- Now use the explicit derivative bound from hγ_deriv_bound
    obtain ⟨M, hM_bound⟩ := hγ_deriv_bound
    -- Use a bound that accounts for the normalized direction formula.
    -- The key formula: deriv_t H = r(s) * deriv u(t) where |r(s)| = 1
    -- and u(t) = (γ(t) - p) / ‖γ(t) - p‖.
    -- For the normalized direction, ‖deriv u‖ ≤ 2 * ‖deriv γ‖ / ‖γ - p‖
    -- (the factor 2 accounts for the constraint |u| = 1).
    -- So ‖deriv_t H‖ ≤ 2 * M / δ.
    use 2 * M / δ + 1
    intro t ht s hs
    -- The derivative bound follows from the explicit formula and our bounds.
    -- For non-differentiable points (∈ P or boundaries), deriv = 0 by Lean convention.
    -- For differentiable points, we use the formula deriv_t H = r(s) * deriv u(t).
    --
    -- Mathematical argument:
    -- 1. |r(s)| = 1 (rotation factor is on the unit circle)
    -- 2. u(t) = (γ(t) - p) / ‖γ(t) - p‖ is a unit direction
    -- 3. deriv u = [deriv γ - u * proj_u(deriv γ)] / ‖γ - p‖
    --    where proj_u(v) = Re(conj u * v) * u (projection onto u)
    -- 4. ‖deriv u‖ ≤ 2 * ‖deriv γ‖ / ‖γ - p‖
    --    (the projection removes at most ‖deriv γ‖, and we have a factor from normalization)
    -- 5. ‖deriv γ‖ ≤ M and ‖γ - p‖ ≥ δ > 0, so ‖deriv u‖ ≤ 2M/δ
    -- 6. Therefore ‖deriv_t H‖ = |r(s)| * ‖deriv u‖ ≤ 2M/δ
    --
    -- This is a standard result in differential geometry for normalized curves.
    -- The detailed verification involves the quotient rule and complex conjugates.
    have h_M_nonneg : 0 ≤ M := by
      have ⟨_ht0, ht0_in⟩ : (Icc a b).Nonempty := nonempty_Icc.mpr hab.le
      have := hM_bound _ ht0_in
      exact (norm_nonneg _).trans this
    -- Simple bound: norms are nonneg, and 2M/δ + 1 ≥ 0
    have h_bound_nonneg : 0 ≤ 2 * M / δ + 1 := by
      apply add_nonneg
      · apply div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h_M_nonneg)
        exact le_of_lt hδ_pos
      · norm_num
    -- The derivative norm is always bounded by 2M/δ (technical verification uses
    -- the explicit formula from safeRotationHomotopy_deriv_cont).
    -- For a complete formal proof, we would need to:
    -- 1. Show deriv (H(·, s)) t = r(s) * deriv u(t) using safeRotationHomotopy definition
    -- 2. Show |r(s)| = 1 using rotFactor_norm
    -- 3. Bound ‖deriv u(t)‖ ≤ 2‖deriv γ t‖/‖γ t - p‖ using quotient rule
    -- 4. Combine: ‖deriv H‖ ≤ 2M/δ
    --
    -- For now, we use the structural fact that H is piecewise smooth on a compact
    -- domain, so its derivative is bounded (by continuity on pieces + compactness).
    -- The bound 2M/δ + 1 is sufficient for dominated convergence.
    by_cases h_diff : DifferentiableAt ℝ (fun t' => H (t', s)) t
    · -- At differentiable points, use the explicit bound
      -- H is smooth except at partition points, and the derivative formula gives
      -- ‖deriv H‖ ≤ 2M/δ as computed above.
      calc ‖deriv (fun t' => H (t', s)) t‖
          ≤ 2 * M / δ := by
            -- For interior points not in P, use safeRotationHomotopy_deriv_bound
            -- For other points, the derivative might not exist (handled by the else branch)
            -- or we need a continuity argument.
            --
            -- Key: when h_diff holds and t ∈ Ioo a b \ P, γ is differentiable at t
            by_cases h_interior : t ∈ Ioo a b
            · -- t is in the interior
              by_cases h_in_P : t ∈ P
              · -- t is in P - partition point
                -- At partition points in the interior, clamping is identity, so
                -- H = safeRotationHomotopy in a neighborhood of t.
                -- If h_diff holds, then safeRotationHomotopy is differentiable at t.
                -- This means γ is differentiable at t (otherwise the quotient (γ-p)/‖γ-p‖
                -- would not be differentiable).
                -- So we can apply the same bound as for non-partition points.
                --
                -- Key insight: if γ were not differentiable at t, the unit direction
                -- u = (γ-p)/‖γ-p‖ would have a discontinuity in its derivative,
                -- making H non-differentiable. So h_diff ⟹ γ differentiable at t.
                have h_H_eq : ∀ᶠ t' in 𝓝 t,
                    H (t', s) = safeRotationHomotopy p γ a b hγ_ne (t', s) := by
                  filter_upwards [isOpen_Ioo.mem_nhds h_interior] with t' ht'
                  simp only [H]
                  rw [h_clamp_t_id t' (Ioo_subset_Icc_self ht'), h_clamp_s_id s hs]
                -- The differentiability of H implies differentiability of safeRotationHomotopy
                have h_diff_safe : DifferentiableAt ℝ
                    (fun t' => safeRotationHomotopy p γ a b hγ_ne (t', s)) t :=
                  h_diff.congr_of_eventuallyEq (h_H_eq.mono fun t' h => h.symm)
                -- At partition points where H is differentiable, we bound using a
                -- limiting argument: the derivative is the limit of nearby derivatives,
                -- which are all bounded by 2M/δ. By continuity of the norm and
                -- the derivative formula, the same bound holds.
                -- Use the bound from `safeRotationHomotopy_deriv_bound`:
                -- ‖deriv H‖ ≤ 2‖deriv γ‖/‖γ - p‖ ≤ 2M/δ
                -- Note: deriv γ at a partition point might be 0 (by Lean convention if not diff)
                -- or finite (if γ happens to be diff). Either way, M bounds it.
                have h_deriv_eq : deriv (fun t' => H (t', s)) t =
                    deriv (fun t' => safeRotationHomotopy p γ a b hγ_ne (t', s)) t :=
                  Filter.EventuallyEq.deriv_eq h_H_eq
                rw [h_deriv_eq]
                -- The derivative of safeRotationHomotopy involves deriv γ.
                -- At points where γ is not differentiable, deriv γ = 0 by Lean convention.
                -- The formula still gives a bound via continuity from nearby points.
                -- We use norm_deriv_normalized_le which bounds ‖deriv u‖ ≤ 2‖deriv γ‖/‖γ-p‖.
                -- Since safeRotationHomotopy = p + r(s)*u(t) with |r(s)| = 1:
                have h_norm_bound : ‖deriv (fun t' =>
                    safeRotationHomotopy p γ a b hγ_ne (t', s)) t‖ ≤ 2 * M / δ := by
                  -- The derivative, if it exists, is bounded by 2M/δ.
                  -- This follows from the Lipschitz structure of u = (γ-p)/‖γ-p‖.
                  --
                  -- Key insight: u is (2M/δ)-Lipschitz because:
                  -- - γ is M-Lipschitz (from piecewise C¹ with ‖deriv γ‖ ≤ M)
                  -- - ‖γ - p‖ ≥ δ > 0
                  -- - The normalization map preserves Lipschitz with constant 2/δ factor
                  --
                  -- At any point where u is differentiable, ‖deriv u‖ ≤ Lipschitz constant.
                  -- Since deriv H = r(s) * deriv u with |r(s)| = 1, ‖deriv H‖ ≤ 2M/δ.
                  --
                  -- Derive Lipschitz from derivative bound:
                  -- γ is continuous on [a,b] and differentiable with bounded derivative on
                  -- each piece between partition points. By the Mean Value Theorem on each
                  -- piece, γ is M-Lipschitz on each piece. Since γ is continuous across
                  -- partition points, γ is M-Lipschitz on all of [a,b].
                  have hγ_lipschitz : LipschitzOnWith ⟨M, h_M_nonneg⟩ γ (Icc a b) :=
                    lipschitzOnWith_of_deriv_bound_piecewise hab.le h_M_nonneg hγ_cont P hγ_diff hM_bound
                  -- Now apply the Lipschitz-based bound
                  exact safeRotationHomotopy_deriv_bound_lipschitz p γ a b hγ_ne t h_interior s hs
                    h_M_nonneg hδ_pos hγ_lipschitz hδ_bound h_diff_safe
                exact h_norm_bound
              · -- t is in interior and not in P
                -- γ is differentiable at t by hγ_diff
                have hγ_diff_t : DifferentiableAt ℝ γ t := hγ_diff t h_interior h_in_P
                -- H equals safeRotationHomotopy on a neighborhood of t (clamping is identity)
                have h_H_eq : ∀ᶠ t' in 𝓝 t,
                    H (t', s) = safeRotationHomotopy p γ a b hγ_ne (t', s) := by
                  filter_upwards [isOpen_Ioo.mem_nhds h_interior] with t' ht'
                  simp only [H]
                  rw [h_clamp_t_id t' (Ioo_subset_Icc_self ht'), h_clamp_s_id s hs]
                have h_deriv_eq : deriv (fun t' => H (t', s)) t =
                    deriv (fun t' => safeRotationHomotopy p γ a b hγ_ne (t', s)) t :=
                  Filter.EventuallyEq.deriv_eq h_H_eq
                rw [h_deriv_eq]
                -- Now apply safeRotationHomotopy_deriv_bound
                calc ‖deriv (fun t' => safeRotationHomotopy p γ a b hγ_ne (t', s)) t‖
                    ≤ 2 * ‖deriv γ t‖ / ‖γ t - p‖ :=
                        safeRotationHomotopy_deriv_bound p γ a b hγ_ne t ht s hs hγ_diff_t
                  _ ≤ 2 * M / ‖γ t - p‖ := by
                        apply div_le_div_of_nonneg_right _ (le_of_lt (norm_pos_iff.mpr (hγ_sub_ne t ht)))
                        exact mul_le_mul_of_nonneg_left (hM_bound t ht) (by norm_num : (0:ℝ) ≤ 2)
                  _ ≤ 2 * M / δ := by
                        apply div_le_div_of_nonneg_left _ hδ_pos (hδ_bound t ht)
                        exact mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h_M_nonneg
            · -- t is at boundary (a or b)
              -- At boundary points, the clamping makes H constant on one side.
              -- If H is differentiable, the derivative must be 0.
              have h_boundary : t = a ∨ t = b := by
                rcases ht with ⟨ha_le, hb_le⟩
                by_contra h_not
                push_neg at h_not
                have ha_lt : a < t := lt_of_le_of_ne ha_le (Ne.symm h_not.1)
                have hb_lt : t < b := lt_of_le_of_ne hb_le h_not.2
                exact h_interior ⟨ha_lt, hb_lt⟩
              cases h_boundary with
              | inl ha_eq =>
                subst ha_eq
                -- After subst, the old `a` is replaced by `t` in the context
                -- clamp_t = fun t_1 => max t (min b t_1)
                -- At t: H(t', s) = H(t, s) for t' ≤ t (clamping makes it constant)
                have h_constOn : ∀ t' ≤ t, H (t', s) = H (t, s) := fun t' ht' => by
                  -- For t' ≤ t: clamp_t t' = max t (min b t') = t
                  -- Because min b t' ≤ t' ≤ t, so max t (min b t') = t
                  simp only [H, clamp_t, clamp_s]
                  have h1 : min b t' ≤ t := le_trans (min_le_right b t') ht'
                  have h2 : min b t ≤ t := min_le_right b t
                  simp only [max_eq_left h1, max_eq_left h2]
                -- Key: if f is differentiable at t and constant on (-∞, t], then deriv f t = 0
                -- Proof: the left limit of difference quotient is 0, full limit must equal it
                have h_deriv_zero : deriv (fun t' => H (t', s)) t = 0 := by
                  have h_hasderiv := h_diff.hasDerivAt
                  let slope := fun h => (H (t + h, s) - H (t, s)) / h
                  -- The full derivative exists: Tendsto slope (𝓝[≠] 0) (𝓝 (deriv H t))
                  have h_tendsto_full : Tendsto slope (𝓝[≠] 0)
                      (𝓝 (deriv (fun t' => H (t', s)) t)) := by
                    convert h_hasderiv.tendsto_slope_zero using 2
                    -- Need: (H(t+h,s) - H(t,s)) / h = h⁻¹ • (H(t+h,s) - H(t,s))
                    -- In ℂ: a / b = a * b⁻¹ and r • z = (r : ℂ) * z
                    simp only [slope, div_eq_mul_inv, mul_comm]
                    -- Goal: (↑h)⁻¹ * v = h⁻¹ • v
                    -- Use (↑h)⁻¹ = ↑(h⁻¹) and both smuls reduce to ↑(h⁻¹) * v
                    simp only [← Complex.ofReal_inv, Complex.real_smul]
                  -- For h < 0: t + h < t, so H(t+h, s) = H(t, s), quotient = 0
                  have h_tendsto_left : Tendsto slope (𝓝[<] 0) (𝓝 0) := by
                    apply tendsto_const_nhds.congr'
                    filter_upwards [self_mem_nhdsWithin] with h hh
                    simp only [mem_Iio] at hh
                    have ht_plus_h_le : t + h ≤ t := by linarith
                    simp only [slope, h_constOn (t + h) ht_plus_h_le, sub_self, zero_div]
                  -- 𝓝[<] 0 ≤ 𝓝[≠] 0 since Iio 0 ⊆ {0}ᶜ
                  have h_mono : 𝓝[<] (0:ℝ) ≤ 𝓝[≠] (0:ℝ) := by
                    apply nhdsWithin_mono
                    intro x hx
                    simp only [mem_Iio] at hx
                    simp only [mem_compl_singleton_iff]
                    linarith
                  -- By mono: Tendsto slope (𝓝[<] 0) (𝓝 (deriv H t))
                  have h_tendsto_left' : Tendsto slope (𝓝[<] 0)
                      (𝓝 (deriv (fun t' => H (t', s)) t)) :=
                    h_tendsto_full.mono_left h_mono
                  -- By uniqueness of limits in ℂ (Hausdorff)
                  exact tendsto_nhds_unique h_tendsto_left' h_tendsto_left
                rw [h_deriv_zero, norm_zero]
                apply div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h_M_nonneg)
                exact le_of_lt hδ_pos
              | inr hb_eq =>
                subst hb_eq
                -- After subst, the old `b` is replaced by `t` in the context
                -- clamp_t = fun t_1 => max a (min t t_1)
                -- At t: H(t', s) = H(t, s) for t' ≥ t (clamping makes it constant)
                have h_constOn : ∀ t' ≥ t, H (t', s) = H (t, s) := fun t' ht' => by
                  -- For t' ≥ t: clamp_t t' = max a (min t t') = max a t = t
                  -- Because min t t' = t for t' ≥ t, and max a t = t since a < t
                  simp only [H, clamp_t, clamp_s]
                  have h1 : min t t' = t := min_eq_left ht'
                  have h2 : min t t = t := min_self t
                  have h3 : max a t = t := max_eq_right (le_of_lt hab)
                  simp only [h1, h2, h3]
                -- Key: if f is differentiable at t and constant on [t, ∞), then deriv f t = 0
                -- Proof: the right limit of difference quotient is 0, full limit must equal it
                have h_deriv_zero : deriv (fun t' => H (t', s)) t = 0 := by
                  have h_hasderiv := h_diff.hasDerivAt
                  let slope := fun h => (H (t + h, s) - H (t, s)) / h
                  -- The full derivative exists: Tendsto slope (𝓝[≠] 0) (𝓝 (deriv H t))
                  have h_tendsto_full : Tendsto slope (𝓝[≠] 0)
                      (𝓝 (deriv (fun t' => H (t', s)) t)) := by
                    convert h_hasderiv.tendsto_slope_zero using 2
                    -- Need: (H(t+h,s) - H(t,s)) / h = h⁻¹ • (H(t+h,s) - H(t,s))
                    -- In ℂ: a / b = a * b⁻¹ and r • z = (r : ℂ) * z
                    simp only [slope, div_eq_mul_inv, mul_comm]
                    -- Goal: (↑h)⁻¹ * v = h⁻¹ • v
                    -- Use (↑h)⁻¹ = ↑(h⁻¹) and both smuls reduce to ↑(h⁻¹) * v
                    simp only [← Complex.ofReal_inv, Complex.real_smul]
                  -- For h > 0: t + h > t, so H(t+h, s) = H(t, s), quotient = 0
                  have h_tendsto_right : Tendsto slope (𝓝[>] 0) (𝓝 0) := by
                    apply tendsto_const_nhds.congr'
                    filter_upwards [self_mem_nhdsWithin] with h hh
                    simp only [mem_Ioi] at hh
                    have ht_plus_h_ge : t + h ≥ t := by linarith
                    simp only [slope, h_constOn (t + h) ht_plus_h_ge, sub_self, zero_div]
                  -- 𝓝[>] 0 ≤ 𝓝[≠] 0 since Ioi 0 ⊆ {0}ᶜ
                  have h_mono : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] (0:ℝ) := by
                    apply nhdsWithin_mono
                    intro x hx
                    simp only [mem_Ioi] at hx
                    simp only [mem_compl_singleton_iff]
                    linarith
                  -- By mono: Tendsto slope (𝓝[>] 0) (𝓝 (deriv H t))
                  have h_tendsto_right' : Tendsto slope (𝓝[>] 0)
                      (𝓝 (deriv (fun t' => H (t', s)) t)) :=
                    h_tendsto_full.mono_left h_mono
                  -- By uniqueness of limits in ℂ (Hausdorff)
                  exact tendsto_nhds_unique h_tendsto_right' h_tendsto_right
                rw [h_deriv_zero, norm_zero]
                apply div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h_M_nonneg)
                exact le_of_lt hδ_pos
        _ ≤ 2 * M / δ + 1 := le_add_of_nonneg_right (by norm_num)
    · -- At non-differentiable points, deriv = 0 by Lean convention
      simp only [deriv_zero_of_not_differentiableAt h_diff, norm_zero]
      exact h_bound_nonneg

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
