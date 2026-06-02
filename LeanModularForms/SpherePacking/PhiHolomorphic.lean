/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.NumberTheory.ModularForms.DedekindEta

/-!
# Holomorphicity of E₂ and φ₀ on the upper half-plane

E₂ is holomorphic because `E₂ = (πI/12)⁻¹ · logDeriv(η)` where η is
the Dedekind eta function. Since η is holomorphic and nonvanishing on ℍ,
`logDeriv(η)` is holomorphic, hence E₂ is holomorphic.
-/

open ModularForm EisensteinSeries UpperHalfPlane Set Filter Topology Function
open scoped Real

noncomputable section

/-- The Dedekind eta function is differentiable on ℍ (as a function ℂ → ℂ). -/
private theorem eta_differentiableOn :
    DifferentiableOn ℂ eta {z : ℂ | 0 < z.im} :=
  fun _ hz => (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt

/-- `logDeriv(η)` is differentiable on ℍ. -/
theorem logDeriv_eta_differentiableOn :
    DifferentiableOn ℂ (logDeriv eta) {z : ℂ | 0 < z.im} :=
  (eta_differentiableOn.deriv isOpen_upperHalfPlaneSet).div eta_differentiableOn
    (fun _ hz => eta_ne_zero hz)

/-- E₂ is holomorphic on the upper half-plane.
Proof: `logDeriv(η) = (π·I/12) · E₂` by `ModularForm.logDeriv_eta_eq_E2`, so
`E₂ = (π·I/12)⁻¹ · logDeriv(η)` is holomorphic. -/
theorem E₂_differentiableOn :
    DifferentiableOn ℂ (E2 ∘ ofComplex) {z : ℂ | 0 < z.im} := by
  apply DifferentiableOn.congr ((differentiableOn_const _).mul logDeriv_eta_differentiableOn)
  intro z hz
  simp only [comp, ofComplex_apply_of_im_pos hz, Pi.mul_apply]
  have h := ModularForm.logDeriv_eta_eq_E2 ⟨z, hz⟩
  have hpi : (↑Real.pi : ℂ) * Complex.I / 12 ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero
    · norm_num
  rw [h, inv_mul_cancel_left₀ hpi]

end
