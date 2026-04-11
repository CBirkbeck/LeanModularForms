/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Elliptic Points and Order Definitions

Core definitions for the valence formula for SL₂(Z): the elliptic points `i` and `ρ`
as elements of the upper half-plane, the order of vanishing at a point, and the order
of vanishing at the cusp.

We use `ModularGroup.fd` (notation `𝒟`) from mathlib for the standard fundamental domain.

## Main definitions

* `ellipticPointI'` : the point `i` as an `UpperHalfPlane`
* `ellipticPointRho'` : the point `ρ = -1/2 + (√3/2)i` as an `UpperHalfPlane`
* `ellipticPointRhoPlusOne'` : the T-translate `ρ + 1 = 1/2 + (√3/2)i`
* `orderOfVanishingAt'` : order of vanishing of a function on the upper half-plane at a point
* `orderAtCusp'` : order of vanishing at the cusp via the q-expansion

## Main results

* `ellipticPointRho_add_one_eq` : `ρ + 1 = ρ+1` as complex numbers
* `ellipticPointRho_norm` : `‖ρ‖ = 1`
* `ellipticPointRhoPlusOne_norm` : `‖ρ+1‖ = 1`
* `ellipticPointI_mem_fd` : `i ∈ 𝒟`
* `ellipticPointRho_mem_fd` : `ρ ∈ 𝒟`
* `ellipticPointI_ne_rho` : `i ≠ ρ`
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular

noncomputable section

/-! ### Elliptic points -/

/-- The elliptic point `i` as an element of the upper half-plane. This is `UpperHalfPlane.I`
from mathlib. -/
abbrev ellipticPointI' : UpperHalfPlane := UpperHalfPlane.I

/-- The elliptic point `i` as a complex number. -/
abbrev ellipticPointI : ℂ := (ellipticPointI' : ℂ)

/-- The elliptic point `ρ = e^{2πi/3} = -1/2 + (√3/2)i` as an element of the upper
half-plane. -/
def ellipticPointRho' : UpperHalfPlane :=
  ⟨-1/2 + (Real.sqrt 3 / 2) * I, by
    simp only [add_im, neg_im, one_im, div_im, mul_im, I_re, I_im]
    norm_num⟩

/-- The elliptic point `ρ` as a complex number. -/
abbrev ellipticPointRho : ℂ := (ellipticPointRho' : ℂ)

/-- The T-translate `ρ + 1 = e^{πi/3} = 1/2 + (√3/2)i` as an element of the upper
half-plane. -/
def ellipticPointRhoPlusOne' : UpperHalfPlane :=
  ⟨1/2 + (Real.sqrt 3 / 2) * I, by
    simp only [add_im, one_im, div_im, mul_im, I_re, I_im]
    norm_num⟩

/-- The T-translate `ρ + 1` as a complex number. -/
abbrev ellipticPointRhoPlusOne : ℂ := (ellipticPointRhoPlusOne' : ℂ)

/-! ### Algebraic relations between elliptic points -/

theorem ellipticPointRho_add_one_eq :
    ellipticPointRho + 1 = ellipticPointRhoPlusOne := by
  change (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) + 1 = 1/2 + (Real.sqrt 3 / 2) * I
  ring

/-! ### Norm computations -/

private lemma rho_normSq_eq_one : Complex.normSq (ellipticPointRho' : ℂ) = 1 := by
  change Complex.normSq (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
  have h1 : (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) =
      ((-1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, Complex.normSq_add_mul_I]
  have h2 : (-1/2 : ℝ) ^ 2 = 1/4 := by ring
  have h3 : (Real.sqrt 3 / 2) ^ 2 = 3/4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
  rw [h2, h3]; ring

private lemma rho_plus_one_normSq_eq_one :
    Complex.normSq (ellipticPointRhoPlusOne' : ℂ) = 1 := by
  change Complex.normSq (1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
  have h1 : (1/2 + (Real.sqrt 3 / 2) * I : ℂ) =
      ((1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, Complex.normSq_add_mul_I]
  have h2 : (1/2 : ℝ) ^ 2 = 1/4 := by ring
  have h3 : (Real.sqrt 3 / 2) ^ 2 = 3/4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
  rw [h2, h3]; ring

theorem ellipticPointRho_norm : ‖ellipticPointRho‖ = 1 := by
  change Real.sqrt (Complex.normSq _) = 1
  rw [rho_normSq_eq_one, Real.sqrt_one]

theorem ellipticPointRhoPlusOne_norm : ‖ellipticPointRhoPlusOne‖ = 1 := by
  change Real.sqrt (Complex.normSq _) = 1
  rw [rho_plus_one_normSq_eq_one, Real.sqrt_one]

/-! ### Fundamental domain membership -/

theorem ellipticPointI_mem_fd : ellipticPointI' ∈ 𝒟 := by
  simp only [ModularGroup.fd, ellipticPointI', mem_setOf_eq]
  constructor
  · simp only [UpperHalfPlane.coe_I, Complex.normSq_I]; norm_num
  · simp only [UpperHalfPlane.re]; norm_num

theorem ellipticPointRho_mem_fd : ellipticPointRho' ∈ 𝒟 := by
  simp only [ModularGroup.fd, ellipticPointRho', mem_setOf_eq]
  exact ⟨rho_normSq_eq_one ▸ le_refl _, by simp only [UpperHalfPlane.re]; norm_num⟩

/-! ### Distinctness -/

lemma ellipticPointI_ne_rho : ellipticPointI' ≠ ellipticPointRho' := by
  intro h
  have h1 : (ellipticPointI' : ℂ).re = (ellipticPointRho' : ℂ).re := by rw [h]
  simp only [ellipticPointI', ellipticPointRho'] at h1
  norm_num at h1

/-! ### Order of vanishing -/

/-- Order of vanishing of `f` at a point `z` in the upper half-plane. Extends `f` to a
function on `ℂ` (zero below the real axis) and takes the meromorphic order. -/
def orderOfVanishingAt' (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℤ :=
  (meromorphicOrderAt (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (z : ℂ)).untop₀

/-- The order of vanishing at the cusp, defined as the order of the q-expansion. -/
noncomputable def orderAtCusp' {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma 1) k) : ℤ :=
  (ModularFormClass.qExpansion 1 f).order.toNat

end
