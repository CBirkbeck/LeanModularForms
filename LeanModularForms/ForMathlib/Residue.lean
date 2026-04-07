/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.GeneralizedWindingNumber
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Residue Theory

Definitions and basic results for residues of meromorphic functions.

## Main definitions

* `HasSimplePoleAt f z₀` — simple pole decomposition: `f(z) = c/(z-z₀) + g(z)` near `z₀`
  with `g` analytic.
* `HasSimplePoleAt.coeff` — the coefficient `c` in the pole decomposition.
* `residue f z₀` — the residue of `f` at `z₀`, defined via circle integral limit.

## Main results

* `hasCauchyPV_simple_pole` — PV of `c/(z-s)` along `γ` equals `2πi · winding · c`.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set Filter Topology MeasureTheory
open scoped Interval Real

noncomputable section

variable {x y : ℂ}

/-! ### Simple pole predicate -/

/-- Simple pole decomposition: `f(z) = c/(z-z₀) + g(z)` near `z₀`, where `g` is analytic
at `z₀` and `c` is the residue. -/
def HasSimplePoleAt (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ c : ℂ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
    ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z

/-- Extract the pole coefficient from a simple pole decomposition. -/
noncomputable def HasSimplePoleAt.coeff {f : ℂ → ℂ} {z₀ : ℂ}
    (h : HasSimplePoleAt f z₀) : ℂ :=
  h.choose

/-- The analytic part of a simple pole decomposition. -/
noncomputable def HasSimplePoleAt.regularPart {f : ℂ → ℂ} {z₀ : ℂ}
    (h : HasSimplePoleAt f z₀) : ℂ → ℂ :=
  h.choose_spec.choose

theorem HasSimplePoleAt.regularPart_analyticAt {f : ℂ → ℂ} {z₀ : ℂ}
    (h : HasSimplePoleAt f z₀) : AnalyticAt ℂ h.regularPart z₀ :=
  h.choose_spec.choose_spec.1

theorem HasSimplePoleAt.eventually_eq {f : ℂ → ℂ} {z₀ : ℂ}
    (h : HasSimplePoleAt f z₀) :
    ∀ᶠ z in 𝓝[≠] z₀, f z = h.coeff / (z - z₀) + h.regularPart z :=
  h.choose_spec.choose_spec.2

/-- A simple pole can be constructed from explicit data. -/
theorem hasSimplePoleAt_of_decomposition {f : ℂ → ℂ} {z₀ : ℂ} {c : ℂ} {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g z₀) (hf : ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z) :
    HasSimplePoleAt f z₀ :=
  ⟨c, g, hg, hf⟩

/-! ### Residue via circle integral -/

/-- The residue of `f` at `z₀`, defined as the limit of normalized circle integrals:
`Res(f, z₀) = lim_{r→0⁺} (2πi)⁻¹ ∮_{|z-z₀|=r} f(z) dz`. -/
noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun r =>
    (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(z₀, r), f z

/-! ### CPV of simple pole = winding × coefficient -/

/-- The Cauchy principal value of `c/(z - s)` along a path `γ` equals `2πi · w · c`,
where `w` is the generalized winding number. This is the key computation linking
residues to winding numbers.

The proof factors out the constant `c` from the CPV integrand and uses the
definition of the generalized winding number. -/
theorem hasCauchyPV_simple_pole {s : ℂ} {c : ℂ}
    {γ : PiecewiseC1Path x y} {w : ℂ}
    (hw : HasGeneralizedWindingNumber γ s w) :
    HasCauchyPV (fun z => c / (z - s)) γ s (2 * ↑Real.pi * I * w * c) := by
  have heq : (fun z => c / (z - s)) = (fun z => c * (z - s)⁻¹) := by
    ext z; rw [div_eq_mul_inv]
  have hlim : 2 * ↑Real.pi * I * w * c = c * (2 * ↑Real.pi * I * w) := by ring
  rw [heq, hlim]
  exact hw.const_mul c

/-- Variant with zero coefficient: `HasCauchyPV` of `0/(z-s)` is trivially 0. -/
theorem hasCauchyPV_simple_pole_zero {s : ℂ}
    {γ : PiecewiseC1Path x y} {w : ℂ}
    (hw : HasGeneralizedWindingNumber γ s w) :
    HasCauchyPV (fun z => (0 : ℂ) / (z - s)) γ s 0 := by
  have h := hasCauchyPV_simple_pole (c := (0 : ℂ)) hw
  simp only [mul_zero] at h
  exact h

end
