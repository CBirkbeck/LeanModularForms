/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.ModularSideProof

/-!
# Horizontal Contribution: seg5 integral = 2piI * orderAtCusp'

This file proves that the integral of `logDeriv(f)` along the horizontal
segment (seg5) of the FD boundary at height `H` equals `2piI * orderAtCusp'(f)`.

## Mathematical overview

The horizontal segment goes from `-1/2 + Hi` to `1/2 + Hi` (one full period
at height `H`). Via the substitution `q = exp(2piI*z)`, this horizontal line
maps to a circle of radius `R = exp(-2*pi*H)` in the q-plane. The integral
of `logDeriv(f)` along one period becomes the circle integral of
`logDeriv(cuspFunction)`, which by the factorization `F(q) = q^m * g(q)`
(where `m = orderAtCusp' f` and `g(0) != 0`) equals `2*pi*I * m`.

## Architecture

On `(4/5, 1)`, `fdBoundaryFun H t = (5*t - 9/2) + H*I` is a horizontal line
at height `H` with derivative `5`. Taking the seg5 integral equation as a
hypothesis (proved via cusp function factorization in the q-expansion
theory), we construct `HorizontalContributionData`.

## Main results

* `deriv_fdBoundaryFun_seg5` -- derivative of `fdBoundaryFun` on seg5 equals `5`
* `fdBoundaryFun_seg5_eq` -- value of `fdBoundaryFun` on seg5
* `horizontalContribution_eq` -- the integral using `γ` equals the integral
  using `fdBoundaryFun`, given they agree on `[0, 1]`
* `horizontalContributionData_of_seg5_eq` -- fill `HorizontalContributionData`

## References

* Diamond--Shurman, *A First Course in Modular Forms*, Theorem 3.1.1
* Serre, *A Course in Arithmetic*, Chapter VII
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-! ### Seg5 derivative -/

/-- On seg5 (`4/5 < t`), `fdBoundaryFun H` agrees with the affine function
`t ↦ (5*t - 9/2) + H*I` in a neighborhood. -/
private theorem fdBoundaryFun_eventuallyEq_affine_seg5 (H : ℝ) (t : ℝ) (ht : 4/5 < t) :
    fdBoundaryFun H =ᶠ[𝓝 t] fun s => (5 * (s : ℂ) - 9/2) + ↑H * I :=
  Filter.eventually_of_mem (Ioi_mem_nhds ht) fun s (hs : 4/5 < s) => by
    simp only [fdBoundaryFun,
      show ¬s ≤ 1/5 from by linarith, show ¬s ≤ 2/5 from by linarith,
      show ¬s ≤ 3/5 from by linarith, show ¬s ≤ 4/5 from by linarith, ite_false]

/-- `HasDerivAt` for the affine seg5 function: derivative is `5`. -/
private theorem hasDerivAt_seg5_affine (H : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (5 * (s : ℂ) - 9/2) + ↑H * I) 5 t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  simpa using ((h1.const_mul (5 : ℂ)).sub_const (9/2 : ℂ)).add_const (↑H * I : ℂ)

/-- Derivative of `fdBoundaryFun H` on seg5 (horizontal, `4/5 < t`) equals `5`. -/
theorem deriv_fdBoundaryFun_seg5 (H : ℝ) (t : ℝ) (ht : 4/5 < t) :
    deriv (fdBoundaryFun H) t = 5 := by
  rw [(fdBoundaryFun_eventuallyEq_affine_seg5 H t ht).deriv_eq]
  exact (hasDerivAt_seg5_affine H t).deriv

/-- On seg5 (`4/5 < t`), `fdBoundaryFun H t = (5*t - 9/2) + H*I`, the horizontal
line from `-1/2 + Hi` to `1/2 + Hi`. -/
theorem fdBoundaryFun_seg5_eq (H : ℝ) (t : ℝ) (ht : 4/5 < t) :
    fdBoundaryFun H t = (5 * ↑t - 9/2 : ℂ) + ↑H * I := by
  simp only [fdBoundaryFun,
    show ¬t ≤ 1/5 from by linarith, show ¬t ≤ 2/5 from by linarith,
    show ¬t ≤ 3/5 from by linarith, show ¬t ≤ 4/5 from by linarith, ite_false]

/-! ### Main theorem: horizontal contribution from seg5 integral equation -/

/-- **Horizontal contribution theorem.** Given the seg5 integral equation
for `fdBoundaryFun`, transfer it to the integral using the path `γ` (which
agrees with `fdBoundaryFun` on `[0, 1]`). -/
theorem horizontalContribution_eq
    {H : ℝ} (_hH : Real.sqrt 3 / 2 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (h_seg5 : ∫ t in (4/5 : ℝ)..1,
      logDeriv (modularFormCompOfComplex f) (fdBoundaryFun H t) *
        deriv (fdBoundaryFun H) t =
      2 * ↑Real.pi * I * (orderAtCusp' f : ℂ)) :
    ∫ t in (4/5 : ℝ)..1,
      logDeriv (⇑f ∘ UpperHalfPlane.ofComplex) (γ.toPath.extend t) *
      deriv γ.toPath.extend t =
    2 * ↑Real.pi * I * (orderAtCusp' f : ℂ) := by
  refine (intervalIntegral.integral_congr_ae ?_).trans h_seg5
  have h_null : (volume : Measure ℝ) {(1 : ℝ)} = 0 := by simp
  rw [ae_iff]
  refine measure_mono_null (fun t ht => ?_) h_null
  simp only [mem_setOf_eq, not_forall] at ht
  obtain ⟨ht_mem, ht_ne⟩ := ht
  rw [Set.uIoc_of_le (by norm_num : (4:ℝ)/5 ≤ 1)] at ht_mem
  simp only [mem_singleton_iff]
  by_contra ht_ne_one
  refine ht_ne ?_
  have ht_lt : t < 1 := lt_of_le_of_ne ht_mem.2 ht_ne_one
  have ht_cc : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht_mem.1], ht_mem.2⟩
  have h_ev : γ.toPath.extend =ᶠ[𝓝 t] fdBoundaryFun H :=
    Filter.eventually_of_mem
      (Filter.inter_mem (Ioi_mem_nhds ht_mem.1) (Iio_mem_nhds ht_lt))
      fun s ⟨(hs4 : 4/5 < s), (hs1 : s < 1)⟩ => hγ s ⟨by linarith, by linarith⟩
  rw [hγ t ht_cc, h_ev.deriv_eq]

/-- Build `HorizontalContributionData` from the seg5 integral equation. -/
theorem horizontalContributionData_of_seg5_eq
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (h_seg5 : ∫ t in (4/5 : ℝ)..1,
      logDeriv (modularFormCompOfComplex f) (fdBoundaryFun H t) *
        deriv (fdBoundaryFun H) t =
      2 * ↑Real.pi * I * (orderAtCusp' f : ℂ)) :
    HorizontalContributionData f γ where
  seg5_integral_eq := horizontalContribution_eq f hH γ hγ h_seg5

end
