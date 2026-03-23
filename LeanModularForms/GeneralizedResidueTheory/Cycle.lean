/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.GeneralizedResidueTheorem
import Mathlib.Data.Finsupp.Defs

/-!
# Contour Cycles

Formal Z-linear combinations of piecewise C^1 immersions ("cycles"), with
contour integration and winding numbers extended by linearity.

## Main definitions

* `ContourCycle` -- formal Z-linear combination of `PiecewiseC1Immersion`s.
* `contourIntegralCycle f Gamma` -- contour integral of `f` over a cycle.
* `windingNumberCycle Gamma z` -- winding number of a cycle around `z`.
* `IsNullHomologousCycle Gamma U` -- each component is null-homologous in `U`.

## Main results

* `contourIntegralCycle_single` -- single curve with multiplicity 1.
* `windingNumberCycle_single` -- same for winding numbers.
* `contourIntegralCycle_eq_zero_of_nullHomologous` -- Cauchy theorem for cycles.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Classical Interval

noncomputable section

/-! ### Definitions -/

/-- A contour cycle is a formal Z-linear combination of piecewise C^1 immersions. -/
abbrev ContourCycle := PiecewiseC1Immersion →₀ ℤ

/-- Contour integral of `f` over a cycle `Gamma`, extended by linearity:
`sum_gamma n_gamma * integral_gamma f(z) dz`. -/
def contourIntegralCycle (f : ℂ → ℂ) (Γ : ContourCycle) : ℂ :=
  Γ.sum fun γ n =>
    (n : ℂ) * ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t

/-- Winding number of a cycle around `z`, extended by linearity:
`sum_gamma n_gamma * n(gamma, z)`. -/
def windingNumberCycle (Γ : ContourCycle) (z : ℂ) : ℂ :=
  Γ.sum fun γ n =>
    (n : ℂ) * generalizedWindingNumber' γ.toFun γ.a γ.b z

/-- A cycle is null-homologous in `U` when every component curve is
null-homologous in `U`. -/
def IsNullHomologousCycle (Γ : ContourCycle) (U : Set ℂ) : Prop :=
  ∀ γ ∈ Γ.support, IsNullHomologous γ U

/-! ### Bridge lemmas for single curves -/

/-- Contour integral of a single curve with multiplicity 1. -/
theorem contourIntegralCycle_single (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) :
    contourIntegralCycle f (Finsupp.single γ 1) =
      ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t := by
  unfold contourIntegralCycle
  rw [Finsupp.sum_single_index]
  · simp
  · simp

/-- Winding number of a single curve with multiplicity 1. -/
theorem windingNumberCycle_single (γ : PiecewiseC1Immersion) (z : ℂ) :
    windingNumberCycle (Finsupp.single γ 1) z =
      generalizedWindingNumber' γ.toFun γ.a γ.b z := by
  unfold windingNumberCycle
  rw [Finsupp.sum_single_index]
  · simp
  · simp

/-- A null-homologous single curve gives a null-homologous cycle. -/
theorem isNullHomologousCycle_single (γ : PiecewiseC1Immersion) (U : Set ℂ)
    (h : IsNullHomologous γ U) :
    IsNullHomologousCycle (Finsupp.single γ 1) U := by
  intro γ' hγ'
  rw [Finsupp.support_single_ne_zero _ (one_ne_zero), Finset.mem_singleton] at hγ'
  rwa [hγ']

/-! ### Main theorems -/

/-- **Cauchy theorem for cycles**: if `f` is holomorphic on `U` and `Gamma` is
null-homologous in `U`, then the contour integral of `f` over `Gamma` is zero.

Proof: each summand `n * integral_gamma f dz` has `integral_gamma f dz = 0`
by the single-curve Dixon theorem, so `n * 0 = 0`. -/
theorem contourIntegralCycle_eq_zero_of_nullHomologous
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (Γ : ContourCycle) (h_null : IsNullHomologousCycle Γ U) :
    contourIntegralCycle f Γ = 0 := by
  unfold contourIntegralCycle
  apply Finset.sum_eq_zero
  intro γ hγ
  simp only
  rw [contourIntegral_eq_zero_of_nullHomologous hU hf γ (h_null γ hγ), mul_zero]

/-- Winding number of a null-homologous cycle is zero outside `U`. -/
theorem windingNumberCycle_eq_zero_outside
    {U : Set ℂ} (Γ : ContourCycle) (h_null : IsNullHomologousCycle Γ U)
    {z : ℂ} (hz : z ∉ U) :
    windingNumberCycle Γ z = 0 := by
  unfold windingNumberCycle
  apply Finset.sum_eq_zero
  intro γ hγ
  simp only
  rw [(h_null γ hγ).winding_zero z hz, mul_zero]

end
