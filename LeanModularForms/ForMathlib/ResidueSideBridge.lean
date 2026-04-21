/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDBoundaryReparametrization
import LeanModularForms.ForMathlib.ResidueSide

/-!
# ForMathlib-native Residue and Modular Sides via the Reparametrization Bridge

This file uses `FDBoundaryReparametrization.lean` to convert the old-chain
residue and modular side results into new-chain `HasCauchyPVOn` statements
suitable for combining with `valence_formula_unconditional_mkD`.

## Main results

* `cpv_residue_side_HasCauchyPVOn` — ForMathlib-style residue side
  returning a `HasCauchyPVOn` on a `PiecewiseC1Path`
* `cpv_modular_side_HasCauchyPVOn` — ForMathlib-style modular side
  returning a `HasCauchyPVOn` with the modular limit value
-/

open Complex Set CongruenceSubgroup
open scoped UpperHalfPlane ModularForm Modular

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

include hf in
/-- **Residue side (ForMathlib form)**: the ε-truncated integral of
`logDeriv(f)` around any `PiecewiseC1Path` agreeing with `fdBoundaryFun H`
converges to `2πi · Σ gWN(γ, s) · ord(f, s)` where `gWN'` is the old
chain's winding number.

This is the result from the old chain bridged through the
reparametrization. It can be further post-processed to replace
`generalizedWindingNumber'` with `generalizedWindingNumber` via
`generalizedWindingNumber_eq_generalizedWindingNumber'`. -/
theorem cpv_residue_side_HasCauchyPVOn
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
      ∀ (γ : PiecewiseC1Path (fdStart H) (fdStart H))
        (_hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t),
        HasCauchyPVOn (sArcOfS S ∪ sVertOfS S)
          (logDeriv (modularFormCompOfComplex f)) γ
          (2 * ↑Real.pi * I *
            ∑ s ∈ S,
              generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
                (orderOfVanishingAt' (⇑f) s : ℂ)) := by
  obtain ⟨H₀, hH₀, h_old⟩ := cpv_residue_side_forMathlib f hf S hS hS_complete
  exact ⟨H₀, hH₀, fun hH γ hγ => hasCauchyPVOn_of_cauchyPVOn'_tendsto γ hγ (h_old hH)⟩

include hf in
/-- **Modular side (ForMathlib form)**: the ε-truncated integral of
`logDeriv(f)` around any `PiecewiseC1Path` agreeing with `fdBoundaryFun H`
converges to `-(2πi)(k/12 - ord_∞)`. -/
theorem cpv_modular_side_HasCauchyPVOn
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
      ∀ (γ : PiecewiseC1Path (fdStart H) (fdStart H))
        (_hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t),
        HasCauchyPVOn (sArcOfS S ∪ sVertOfS S)
          (logDeriv (modularFormCompOfComplex f)) γ
          (-(2 * ↑Real.pi * I *
            ((k : ℂ) / 12 - (orderAtCusp' f : ℂ)))) := by
  obtain ⟨H₀, hH₀, h_old⟩ := cpv_modular_side_forMathlib f hf S hS hS_complete
  exact ⟨H₀, hH₀, fun hH γ hγ => hasCauchyPVOn_of_cauchyPVOn'_tendsto γ hγ (h_old hH)⟩

end
