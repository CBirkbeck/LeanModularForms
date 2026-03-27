/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Valence Formula Definitions

Definitions for the valence formula for SL₂(ℤ): elliptic points i and ρ,
orbifold coefficients, the order of vanishing, and the canonical fundamental domain.

We use `ModularGroup.fd` (notation `𝒟`) from mathlib for the standard fundamental domain.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The canonical fundamental domain with half-open right edge.
Left edge included (Re = -1/2), right edge excluded (Re = 1/2).
Avoids T-equivalent duplicates: ρ ∈ 𝒟c but ρ+1 ∉ 𝒟c. -/
def fundamentalDomainCanonical : Set UpperHalfPlane :=
  {z : UpperHalfPlane | (-1/2 ≤ z.re ∧ z.re < 1/2) ∧ 1 ≤ Complex.normSq (z : ℂ)}

notation "𝒟c" => fundamentalDomainCanonical

theorem fundamentalDomainCanonical_subset_fd : 𝒟c ⊆ 𝒟 :=
  fun _ ⟨⟨hre_left, hre_right⟩, hnorm⟩ =>
    ⟨hnorm, abs_le.mpr ⟨by linarith, le_of_lt hre_right⟩⟩

/-- The elliptic point i as an element of ℍ. -/
def ellipticPointI' : UpperHalfPlane := ⟨I, by simp [Complex.I_im]⟩

/-- The elliptic point `i` as a complex number. -/
abbrev ellipticPointI : ℂ := (ellipticPointI' : ℂ)

/-- The elliptic point ρ = e^{2πi/3} = -1/2 + (√3/2)i as an element of ℍ. -/
def ellipticPointRho' : UpperHalfPlane :=
  ⟨-1/2 + (Real.sqrt 3 / 2) * I, by
    simp only [add_im, neg_im, one_im, div_im, mul_im, I_re, I_im]
    norm_num⟩

/-- The elliptic point `ρ` as a complex number. -/
abbrev ellipticPointRho : ℂ := (ellipticPointRho' : ℂ)

/-- The T-translate ρ+1 = e^{πi/3} = 1/2 + (√3/2)i. -/
def ellipticPointRhoPlusOne' : UpperHalfPlane :=
  ⟨1/2 + (Real.sqrt 3 / 2) * I, by
    simp only [add_im, one_im, div_im, mul_im, I_re, I_im]
    norm_num⟩

/-- The T-translate `ρ + 1` as a complex number. -/
abbrev ellipticPointRhoPlusOne : ℂ := (ellipticPointRhoPlusOne' : ℂ)

theorem ellipticPointRho_add_one_eq :
    ellipticPointRho + 1 = ellipticPointRhoPlusOne := by
  change (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) + 1 = 1/2 + (Real.sqrt 3 / 2) * I; ring

private lemma rho_normSq_eq_one : Complex.normSq (ellipticPointRho' : ℂ) = 1 := by
  change Complex.normSq (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
  have h1 : (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) =
      ((-1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, Complex.normSq_add_mul_I]
  have h2 : (-1/2 : ℝ)^2 = 1/4 := by ring
  have h3 : (Real.sqrt 3 / 2)^2 = 3/4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
  rw [h2, h3]; ring

private lemma rho_plus_one_normSq_eq_one :
    Complex.normSq (ellipticPointRhoPlusOne' : ℂ) = 1 := by
  change Complex.normSq (1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
  have h1 : (1/2 + (Real.sqrt 3 / 2) * I : ℂ) =
      ((1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, Complex.normSq_add_mul_I]
  have h2 : (1/2 : ℝ)^2 = 1/4 := by ring
  have h3 : (Real.sqrt 3 / 2)^2 = 3/4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
  rw [h2, h3]; ring

theorem ellipticPointRhoPlusOne_norm : ‖ellipticPointRhoPlusOne‖ = 1 := by
  change Real.sqrt (Complex.normSq _) = 1; rw [rho_plus_one_normSq_eq_one, Real.sqrt_one]

theorem ellipticPointRho_norm : ‖ellipticPointRho‖ = 1 := by
  change Real.sqrt (Complex.normSq _) = 1; rw [rho_normSq_eq_one, Real.sqrt_one]

theorem ellipticPointI_mem_fd : ellipticPointI' ∈ 𝒟 := by
  simp only [ModularGroup.fd, ellipticPointI', mem_setOf_eq]
  constructor
  · simp [Complex.normSq_I]
  · simp only [UpperHalfPlane.re]; norm_num

theorem ellipticPointRho_mem_fd : ellipticPointRho' ∈ 𝒟 := by
  simp only [ModularGroup.fd, ellipticPointRho', mem_setOf_eq]
  exact ⟨rho_normSq_eq_one ▸ le_refl _, by simp only [UpperHalfPlane.re]; norm_num⟩

theorem ellipticPointI_mem_fundamentalDomainCanonical : ellipticPointI' ∈ 𝒟c := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [ellipticPointI', UpperHalfPlane.re]; norm_num
  · simp only [ellipticPointI', UpperHalfPlane.re]; norm_num
  · simp [ellipticPointI', Complex.normSq_I]

theorem ellipticPointRho_mem_fundamentalDomainCanonical : ellipticPointRho' ∈ 𝒟c := by
  refine ⟨⟨?_, ?_⟩, rho_normSq_eq_one.symm.le⟩
  · simp only [ellipticPointRho', UpperHalfPlane.re]; norm_num
  · simp only [ellipticPointRho', UpperHalfPlane.re]; norm_num

theorem ellipticPointRhoPlusOne_not_mem_fundamentalDomainCanonical :
    ellipticPointRhoPlusOne' ∉ 𝒟c := by
  simp only [fundamentalDomainCanonical, ellipticPointRhoPlusOne', mem_setOf_eq, not_and]
  intro ⟨_, hre_right⟩
  simp only [UpperHalfPlane.re] at hre_right; norm_num at hre_right

lemma ellipticPointI_ne_rho : ellipticPointI' ≠ ellipticPointRho' := by
  intro h
  have h1 : (ellipticPointI' : ℂ).re = (ellipticPointRho' : ℂ).re := by rw [h]
  simp only [ellipticPointI', ellipticPointRho'] at h1; norm_num at h1

/-- Order of vanishing of f at a point in ℍ. -/
def orderOfVanishingAt' (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℤ :=
  (meromorphicOrderAt (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (z : ℂ)).untop₀

theorem orderOfVanishingAt_nonneg {k : ℤ} (f : ModularForm (Gamma 1) k)
    (z : UpperHalfPlane) : 0 ≤ orderOfVanishingAt' f z := by
  unfold orderOfVanishingAt'
  rw [WithTop.untop₀_nonneg]
  let g := fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0
  have h_im_pos : 0 < (z : ℂ).im := z.im_pos
  have h_g_diffAt : ∀ᶠ w in 𝓝 (z : ℂ), DifferentiableAt ℂ g w := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds h_im_pos] with w hw
    have h_diffOn : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {w | 0 < w.im} :=
      UpperHalfPlane.mdifferentiable_iff.mp f.holo'
    have h_eq_w : ∀ᶠ u in 𝓝 w, g u = (f ∘ UpperHalfPlane.ofComplex) u := by
      filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw] with u hu
      simp only [g, Function.comp_apply, dif_pos hu]
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hu]
    exact ((h_diffOn w hw).differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)).congr_of_eventuallyEq h_eq_w
  have h_analytic : AnalyticAt ℂ g (z : ℂ) :=
    analyticAt_iff_eventually_differentiableAt.mpr h_g_diffAt
  exact h_analytic.meromorphicOrderAt_nonneg

/-- The order of vanishing at the cusp (in the q-expansion). -/
noncomputable def orderAtCusp' {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma 1) k) : ℤ :=
  (ModularFormClass.qExpansion 1 f).order.toNat

/-- The orbifold coefficient at a point for the valence formula:
1/2 at i, 1/3 at ρ, 1 elsewhere. -/
def windingNumberCoeff' (p : UpperHalfPlane) : ℚ :=
  if p = ellipticPointI' then 1/2
  else if p = ellipticPointRho' then 1/3
  else 1

theorem windingNumberCoeff_interior (p : UpperHalfPlane)
    (hp_not_i : p ≠ ellipticPointI') (hp_not_rho : p ≠ ellipticPointRho') :
    windingNumberCoeff' p = 1 := by
  simp only [windingNumberCoeff', hp_not_i, hp_not_rho, ite_false]

theorem windingNumberCoeff_at_i : windingNumberCoeff' ellipticPointI' = 1/2 := by
  simp only [windingNumberCoeff', ite_true]

theorem windingNumberCoeff_at_rho : windingNumberCoeff' ellipticPointRho' = 1/3 := by
  simp only [windingNumberCoeff', ellipticPointI_ne_rho.symm, ite_false, ite_true]

theorem windingNumberCoeff_trichotomy (p : UpperHalfPlane) :
    (windingNumberCoeff' p = 1/2 ∧ p = ellipticPointI') ∨
    (windingNumberCoeff' p = 1/3 ∧ p = ellipticPointRho') ∨
    (windingNumberCoeff' p = 1 ∧ p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho') := by
  by_cases hi : p = ellipticPointI'
  · left; exact ⟨hi ▸ windingNumberCoeff_at_i, hi⟩
  · by_cases hr : p = ellipticPointRho'
    · right; left; exact ⟨hr ▸ windingNumberCoeff_at_rho, hr⟩
    · right; right; exact ⟨windingNumberCoeff_interior p hi hr, hi, hr⟩

end
