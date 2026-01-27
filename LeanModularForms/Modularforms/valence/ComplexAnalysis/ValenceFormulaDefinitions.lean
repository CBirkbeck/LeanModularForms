/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.Analysis.Meromorphic.Order

/-!
# Valence Formula - Basic Definitions

This file contains the fundamental definitions for the valence formula:
- The fundamental domain 𝒟' for SL₂(ℤ)
- The elliptic points i and ρ
- Orbifold coefficients
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The Fundamental Domain -/

/-- The standard fundamental domain for SL₂(ℤ). -/
def fundamentalDomain : Set UpperHalfPlane :=
  {z : UpperHalfPlane | |z.re| ≤ 1/2 ∧ ‖(z : ℂ)‖ ≥ 1}

notation "𝒟'" => fundamentalDomain

/-! ## Elliptic Points -/

/-- The elliptic point i as an element of ℍ. -/
def ellipticPoint_i' : UpperHalfPlane := ⟨I, by simp [Complex.I_im]⟩

/-- The elliptic point i as a complex number. -/
abbrev ellipticPoint_i : ℂ := (ellipticPoint_i' : ℂ)

/-- The elliptic point ρ = e^{2πi/3} as an element of ℍ. -/
def ellipticPoint_rho' : UpperHalfPlane :=
  ⟨-1/2 + (Real.sqrt 3 / 2) * I, by
    simp only [add_im, neg_im, one_im, div_im, mul_im, I_re, I_im]
    norm_num⟩

/-- The elliptic point ρ as a complex number. -/
abbrev ellipticPoint_rho : ℂ := (ellipticPoint_rho' : ℂ)

/-! ## Elliptic Points in Fundamental Domain -/

/-- The elliptic point i is in the fundamental domain. -/
theorem ellipticPoint_i_mem_fd' : ellipticPoint_i' ∈ 𝒟' := by
  simp only [fundamentalDomain, ellipticPoint_i', mem_setOf_eq]
  constructor
  · simp only [UpperHalfPlane.re]
    norm_num
  · simp

/-- The elliptic point ρ is in the fundamental domain. -/
theorem ellipticPoint_rho_mem_fd' : ellipticPoint_rho' ∈ 𝒟' := by
  simp only [fundamentalDomain, ellipticPoint_rho', mem_setOf_eq]
  constructor
  · -- |Re(ρ)| = |-1/2| = 1/2 ≤ 1/2
    simp only [UpperHalfPlane.re]
    norm_num
  · -- |ρ| = |(-1/2 + √3/2 * i)| = 1 ≥ 1
    -- normSq(ρ) = (-1/2)² + (√3/2)² = 1/4 + 3/4 = 1
    -- Hence ‖ρ‖ = √(normSq ρ) = 1 ≥ 1
    have h_normSq : Complex.normSq (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1 := by
      have h1 : (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) =
          ((-1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
      rw [h1, Complex.normSq_add_mul_I]
      have h2 : (-1/2 : ℝ)^2 = 1/4 := by ring
      have h3 : (Real.sqrt 3 / 2)^2 = 3/4 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
      rw [h2, h3]; ring
    have h_norm : ‖(-1/2 + (Real.sqrt 3 / 2) * I : ℂ)‖ = 1 := by
      show Real.sqrt (Complex.normSq _) = 1; rw [h_normSq, Real.sqrt_one]
    show ‖(-1/2 + (Real.sqrt 3 / 2) * I : ℂ)‖ ≥ 1
    rw [h_norm]

/-! ## Orbifold Coefficients -/

/-- The orbifold coefficient at i is 1/2. -/
def orbifoldCoeff_at_i : ℚ := 1/2

/-- The orbifold coefficient at ρ is 1/3. -/
def orbifoldCoeff_at_rho : ℚ := 1/3

/-- The orbifold coefficient at interior points is 1. -/
def orbifoldCoeff_interior : ℚ := 1

/-- The coefficient for i in the valence formula is 1/2. -/
theorem valenceCoeff_at_i : (orbifoldCoeff_at_i : ℂ) = 1/2 := by
  simp only [orbifoldCoeff_at_i, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]

/-- The coefficient for ρ in the valence formula is 1/3. -/
theorem valenceCoeff_at_rho : (orbifoldCoeff_at_rho : ℂ) = 1/3 := by
  simp only [orbifoldCoeff_at_rho, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]

/-! ## Order of Vanishing -/

/-- Order of vanishing of f at a point in ℍ. -/
def orderOfVanishingAt' (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℤ :=
  (meromorphicOrderAt (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (z : ℂ)).untop₀

/-- For a holomorphic modular form, the order of vanishing is non-negative. -/
theorem orderOfVanishingAt_nonneg {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma 1) k)
    (z : UpperHalfPlane) : 0 ≤ orderOfVanishingAt' f z := by
  unfold orderOfVanishingAt'
  rw [WithTop.untop₀_nonneg]
  let g := fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0
  have h_im_pos : 0 < (z : ℂ).im := z.im_pos
  have h_g_diffAt : ∀ᶠ w in 𝓝 (z : ℂ), DifferentiableAt ℂ g w := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds h_im_pos] with w hw
    have h_mdiff := f.holo'
    have h_diffOn : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {w | 0 < w.im} :=
      UpperHalfPlane.mdifferentiable_iff.mp h_mdiff
    have h_eq_w : ∀ᶠ u in 𝓝 w, g u = (f ∘ UpperHalfPlane.ofComplex) u := by
      filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw] with u hu
      simp only [g, Function.comp_apply, dif_pos hu]
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hu]
    exact ((h_diffOn w hw).differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)).congr_of_eventuallyEq h_eq_w
  have h_analytic : AnalyticAt ℂ g (z : ℂ) :=
    analyticAt_iff_eventually_differentiableAt.mpr h_g_diffAt
  exact h_analytic.meromorphicOrderAt_nonneg

/-! ## Winding Number Coefficient -/

/-- The orbifold coefficient at a point for the valence formula. -/
def windingNumberCoeff' (p : UpperHalfPlane) : ℚ :=
  if p = ellipticPoint_i' then 1/2
  else if p = ellipticPoint_rho' then 1/3
  else 1

/-- Interior points have winding coefficient 1. -/
theorem windingNumberCoeff_interior (p : UpperHalfPlane)
    (hp_not_i : p ≠ ellipticPoint_i') (hp_not_rho : p ≠ ellipticPoint_rho') :
    windingNumberCoeff' p = 1 := by
  simp only [windingNumberCoeff', hp_not_i, hp_not_rho, ite_false]

/-- The winding coefficient at i is 1/2. -/
theorem windingNumberCoeff_at_i : windingNumberCoeff' ellipticPoint_i' = 1/2 := by
  simp only [windingNumberCoeff', ite_true]

/-- i ≠ ρ as points in ℍ. -/
lemma ellipticPoint_i_ne_rho : ellipticPoint_i' ≠ ellipticPoint_rho' := by
  intro h
  have h1 : (ellipticPoint_i' : ℂ).re = (ellipticPoint_rho' : ℂ).re := by rw [h]
  simp only [ellipticPoint_i', ellipticPoint_rho'] at h1
  norm_num at h1

/-- The winding coefficient at ρ is 1/3. -/
theorem windingNumberCoeff_at_rho : windingNumberCoeff' ellipticPoint_rho' = 1/3 := by
  simp only [windingNumberCoeff', ellipticPoint_i_ne_rho.symm, ite_false, ite_true]

/-- Trichotomy for winding coefficients. -/
theorem windingNumberCoeff_trichotomy (p : UpperHalfPlane) :
    (windingNumberCoeff' p = 1/2 ∧ p = ellipticPoint_i') ∨
    (windingNumberCoeff' p = 1/3 ∧ p = ellipticPoint_rho') ∨
    (windingNumberCoeff' p = 1 ∧ p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho') := by
  by_cases hi : p = ellipticPoint_i'
  · left; exact ⟨hi ▸ windingNumberCoeff_at_i, hi⟩
  · by_cases hr : p = ellipticPoint_rho'
    · right; left; exact ⟨hr ▸ windingNumberCoeff_at_rho, hr⟩
    · right; right; exact ⟨windingNumberCoeff_interior p hi hr, hi, hr⟩

end
