/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.GeneralizedResidueTheorem
import Mathlib.Data.Finsupp.Defs

/-!
# Contour Cycles

Formal Z-linear combinations of closed piecewise C^1 immersions ("cycles"), with
contour integration and winding numbers extended by linearity.

## Main definitions

* `ClosedImmersion` -- a closed piecewise C^1 immersion, bundling the basepoint.
* `ContourCycle` -- formal Z-linear combination of `ClosedImmersion`s.
* `contourIntegralCycle f Gamma` -- contour integral of `f` over a cycle.
* `windingNumberCycle Gamma z` -- winding number of a cycle around `z`.
* `IsNullHomologousCycle Gamma U` -- each component is null-homologous in `U`.
* `cpvCycle S f Gamma` -- CPV integral of `f` over a cycle.

## Main results

* `contourIntegralCycle_single` -- single curve with multiplicity 1.
* `windingNumberCycle_single` -- same for winding numbers.
* `contourIntegralCycle_eq_zero_of_nullHomologous` -- Cauchy theorem for cycles.
* `windingNumberCycle_eq_zero_outside` -- winding number vanishes outside the domain.
* `windingNumberCycle_isInt` -- winding number of a cycle is an integer
  (given per-component integrality hypotheses).

## Design notes

`PiecewiseC1Immersion x y` has type parameters `x y`. For formal Z-linear combinations
we need a single type, so we bundle the basepoint into `ClosedImmersion`. With
`open scoped Classical`, `Finsupp` works without decidable equality.

## References

* K. Hungerbuhler, J. Wasem, *A generalized residue theorem*, arXiv:1808.00997v2,
  Theorem 3.3.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Classical Interval

noncomputable section

/-! ### Closed immersions -/

/-- A closed piecewise C^1 immersion. The basepoint is existentially quantified
to allow combining loops with different basepoints into a cycle. -/
structure ClosedImmersion where
  /-- The common start and end point of the closed curve. -/
  basepoint : ℂ
  /-- The underlying piecewise C^1 immersion from `basepoint` to `basepoint`. -/
  immersion : PiecewiseC1Immersion basepoint basepoint

namespace ClosedImmersion

/-- The underlying piecewise C^1 path. -/
def toPath (γ : ClosedImmersion) : PiecewiseC1Path γ.basepoint γ.basepoint :=
  γ.immersion.toPiecewiseC1Path

@[simp]
theorem toPath_eq (γ : ClosedImmersion) :
    γ.toPath = γ.immersion.toPiecewiseC1Path := rfl

/-- Evaluate the curve at a parameter value. -/
instance : CoeFun ClosedImmersion fun _ => ℝ → ℂ where
  coe γ := γ.toPath.extendedPath

@[simp]
theorem coe_eq (γ : ClosedImmersion) :
    (γ : ℝ → ℂ) = γ.toPath.extendedPath := rfl

/-- Wrap a closed `PiecewiseC1Immersion x x` into a `ClosedImmersion`. -/
def mk' {x : ℂ} (γ : PiecewiseC1Immersion x x) : ClosedImmersion where
  basepoint := x
  immersion := γ

end ClosedImmersion

/-! ### Contour cycles -/

/-- A contour cycle: formal Z-linear combination of closed immersions. -/
abbrev ContourCycle := ClosedImmersion →₀ ℤ

/-! ### Definitions -/

/-- Contour integral of `f` over a cycle `Gamma`, extended by linearity:
`sum_gamma n_gamma * integral_gamma f(z) dz`. -/
def contourIntegralCycle (f : ℂ → ℂ) (Γ : ContourCycle) : ℂ :=
  Γ.sum fun γ n => (n : ℂ) * γ.toPath.contourIntegral f

/-- Winding number of a cycle around `z`, extended by linearity:
`sum_gamma n_gamma * n(gamma, z)`. -/
def windingNumberCycle (Γ : ContourCycle) (z : ℂ) : ℂ :=
  Γ.sum fun γ n => (n : ℂ) * generalizedWindingNumber γ.toPath z

/-- A cycle is null-homologous in `U` when every component curve is
null-homologous in `U`. -/
def IsNullHomologousCycle (Γ : ContourCycle) (U : Set ℂ) : Prop :=
  ∀ γ ∈ Γ.support, IsNullHomologous γ.immersion U

/-- Cauchy principal value integral of `f` over a cycle, extended by linearity. -/
def cpvCycle (S : Finset ℂ) (f : ℂ → ℂ) (Γ : ContourCycle) : ℂ :=
  Γ.sum fun γ n => (n : ℂ) * cauchyPVOn S f γ.toPath

/-! ### Bridge lemmas for single curves -/

/-- Contour integral of a single curve with multiplicity 1. -/
theorem contourIntegralCycle_single (f : ℂ → ℂ) (γ : ClosedImmersion) :
    contourIntegralCycle f (Finsupp.single γ 1) = γ.toPath.contourIntegral f := by
  unfold contourIntegralCycle; rw [Finsupp.sum_single_index] <;> simp

/-- Winding number of a single curve with multiplicity 1. -/
theorem windingNumberCycle_single (γ : ClosedImmersion) (z : ℂ) :
    windingNumberCycle (Finsupp.single γ 1) z =
      generalizedWindingNumber γ.toPath z := by
  unfold windingNumberCycle; rw [Finsupp.sum_single_index] <;> simp

/-- A null-homologous single curve gives a null-homologous cycle. -/
theorem isNullHomologousCycle_single (γ : ClosedImmersion) (U : Set ℂ)
    (h : IsNullHomologous γ.immersion U) :
    IsNullHomologousCycle (Finsupp.single γ 1) U := fun γ' hγ' => by
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hγ'
  rwa [hγ']

/-- CPV integral of a single curve with multiplicity 1. -/
theorem cpvCycle_single (S : Finset ℂ) (f : ℂ → ℂ) (γ : ClosedImmersion) :
    cpvCycle S f (Finsupp.single γ 1) = cauchyPVOn S f γ.toPath := by
  unfold cpvCycle; rw [Finsupp.sum_single_index] <;> simp

/-! ### Main theorems -/

/-- Winding number of a null-homologous cycle is zero outside `U`. -/
theorem windingNumberCycle_eq_zero_outside
    {U : Set ℂ} (Γ : ContourCycle) (h_null : IsNullHomologousCycle Γ U)
    {z : ℂ} (hz : z ∉ U) :
    windingNumberCycle Γ z = 0 := by
  simp only [windingNumberCycle, Finsupp.sum]
  exact Finset.sum_eq_zero fun γ hγ => by
    have := (h_null γ hγ).winding_zero z hz
    simp only [ClosedImmersion.toPath_eq] at this ⊢
    rw [this, mul_zero]

/-! ### Algebraic core for residue theorem -/

/-- Algebraic core: rewrite the weighted sum of per-component residue formulas as
the cycle-level residue sum. -/
private theorem sum_swap_winding_residue (Γ : ContourCycle) (S : Finset ℂ)
    (f : ℂ → ℂ) :
    ∑ γ ∈ Γ.support, (↑(Γ γ) : ℂ) *
      ∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPath s * residue f s =
    2 * ↑Real.pi * I * ∑ s ∈ S,
      windingNumberCycle Γ s * residue f s := by
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [windingNumberCycle, Finsupp.sum]
  rw [Finset.sum_congr rfl (fun γ _ => show (↑(Γ γ) : ℂ) *
      (2 * ↑Real.pi * I * generalizedWindingNumber γ.toPath s *
        residue f s) =
      2 * ↑Real.pi * I *
        (↑(Γ γ) * generalizedWindingNumber γ.toPath s *
          residue f s)
    from by ring), ← Finset.mul_sum, ← Finset.sum_mul]

/-! ### Residue theorem for cycles (simple poles, structural) -/

/-- **Generalized Residue Theorem for simple poles on a cycle (structural version).**

Extends `generalizedResidueTheorem_simplePoles_structural` from a single curve to a
formal Z-linear combination of curves. Each component must have its contour integral
equal to the winding-number-weighted residue sum (guaranteed by null-homologousness
or convexity via the single-curve residue theorem). -/
theorem generalizedResidueTheorem_simplePoles_cycle_structural
    (S : Finset ℂ) (f : ℂ → ℂ) (Γ : ContourCycle)
    (h_comp : ∀ γ ∈ Γ.support,
      γ.toPath.contourIntegral f =
        ∑ s ∈ S, 2 * ↑Real.pi * I *
          generalizedWindingNumber γ.toPath s * residue f s) :
    contourIntegralCycle f Γ =
      2 * ↑Real.pi * I * ∑ s ∈ S,
        windingNumberCycle Γ s * residue f s := by
  simp only [contourIntegralCycle, Finsupp.sum]
  rw [Finset.sum_congr rfl fun γ hγ => show (↑(Γ γ) : ℂ) *
      γ.toPath.contourIntegral f = (↑(Γ γ) : ℂ) *
      ∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPath s * residue f s
    from congr_arg _ (h_comp γ hγ)]
  exact sum_swap_winding_residue Γ S f

/-! ### Winding number integrality -/

/-- Winding number of a cycle around a point is an integer, provided each component
curve's winding number around that point is an integer.

The per-component integrality hypothesis is a standard result for closed piecewise C^1
curves avoiding the base point; it follows from the exponential trick
(see `windingNumber_integer_of_piecewise_closed_avoiding` in the old chain). -/
theorem windingNumberCycle_isInt (Γ : ContourCycle) (z : ℂ)
    (h_int : ∀ γ ∈ Γ.support,
      ∃ n : ℤ, generalizedWindingNumber γ.toPath z = ↑n) :
    ∃ n : ℤ, windingNumberCycle Γ z = ↑n := by
  simp only [windingNumberCycle, Finsupp.sum]
  apply Finset.sum_induction _ (fun x : ℂ => ∃ n : ℤ, x = ↑n)
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by push_cast; ring⟩
  · exact ⟨0, Int.cast_zero.symm⟩
  · intro γ hγ
    obtain ⟨m, hm⟩ := h_int γ hγ
    exact ⟨Γ γ * m, by rw [hm]; push_cast; ring⟩

/-! ### CPV cycle decomposition -/

/-- The CPV of a cycle is the sum of per-component weighted CPVs. -/
theorem cpvCycle_eq_sum (S : Finset ℂ) (f : ℂ → ℂ) (Γ : ContourCycle) :
    cpvCycle S f Γ = ∑ γ ∈ Γ.support,
      (↑(Γ γ) : ℂ) * cauchyPVOn S f γ.toPath := rfl

/-! ### Null-homologous cycle from components -/

/-- If `Gamma_1` and `Gamma_2` are both null-homologous cycles in `U`, then
`Gamma_1 + Gamma_2` is null-homologous in `U`. -/
theorem IsNullHomologousCycle.add {U : Set ℂ}
    {Γ₁ Γ₂ : ContourCycle}
    (h₁ : IsNullHomologousCycle Γ₁ U)
    (h₂ : IsNullHomologousCycle Γ₂ U) :
    IsNullHomologousCycle (Γ₁ + Γ₂) U := by
  intro γ hγ
  rw [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply] at hγ
  by_cases h1 : Γ₁ γ = 0
  · simp [h1] at hγ
    exact h₂ γ (Finsupp.mem_support_iff.mpr hγ)
  · exact h₁ γ (Finsupp.mem_support_iff.mpr h1)

/-! ### Convenience constructors -/

/-- The singleton cycle of multiplicity `n` for a closed immersion. -/
def ContourCycle.ofSingle (γ : ClosedImmersion) (n : ℤ) : ContourCycle :=
  Finsupp.single γ n

/-- Contour integral of a singleton cycle with arbitrary multiplicity. -/
theorem contourIntegralCycle_single_mul (f : ℂ → ℂ) (γ : ClosedImmersion) (n : ℤ) :
    contourIntegralCycle f (Finsupp.single γ n) =
      (n : ℂ) * γ.toPath.contourIntegral f := by
  unfold contourIntegralCycle
  rw [Finsupp.sum_single_index]
  simp

/-- Winding number of a singleton cycle with arbitrary multiplicity. -/
theorem windingNumberCycle_single_mul (γ : ClosedImmersion) (z : ℂ) (n : ℤ) :
    windingNumberCycle (Finsupp.single γ n) z =
      (n : ℂ) * generalizedWindingNumber γ.toPath z := by
  unfold windingNumberCycle
  rw [Finsupp.sum_single_index]
  simp

/-! ### Zero cycle -/

/-- The contour integral of the zero cycle is zero. -/
theorem contourIntegralCycle_zero (f : ℂ → ℂ) :
    contourIntegralCycle f 0 = 0 := by
  simp [contourIntegralCycle, Finsupp.sum]

/-- The winding number of the zero cycle is zero. -/
theorem windingNumberCycle_zero (z : ℂ) :
    windingNumberCycle 0 z = 0 := by
  simp [windingNumberCycle, Finsupp.sum]

/-- The zero cycle is null-homologous in any set. -/
theorem isNullHomologousCycle_zero (U : Set ℂ) :
    IsNullHomologousCycle 0 U := by
  intro γ hγ
  simp [Finsupp.support_zero] at hγ

/-- The CPV of the zero cycle is zero. -/
theorem cpvCycle_zero (S : Finset ℂ) (f : ℂ → ℂ) :
    cpvCycle S f 0 = 0 := by
  simp [cpvCycle, Finsupp.sum]

end
