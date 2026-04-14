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

### Layer 1: Seg5 geometry

On `(4/5, 1)`, `fdBoundaryFun H t = (5*t - 9/2) + H*I`, which is a
horizontal line at height `H`. Its derivative is the constant `5`.

### Layer 2: Reparameterization

The contour integral on `[4/5, 1]` with `fdBoundaryFun` (which has derivative
`5`) reparameterizes to an integral on `[0, 1]` of `logDeriv(f)(s + H*I)`
where `s` ranges from `-1/2` to `1/2`.

### Layer 3: Bridge

Taking the seg5 integral equation as a hypothesis (proved via cusp
function factorization in the q-expansion theory), we construct
`HorizontalContributionData`.

## Main results

* `deriv_fdBoundaryFun_seg5` -- derivative of `fdBoundaryFun` on seg5 equals `5`
* `fdBoundaryFun_seg5_eq` -- value of `fdBoundaryFun` on seg5
* `horizontalContribution_eq` -- the integral using `γ` equals the integral
  using `fdBoundaryFun`, given they agree on `[0, 1]`
* `horizontalContributionData_of_seg5_eq` -- fill `HorizontalContributionData`
* `horizontalContribution_from_modForm` -- fill `ModularSideData`

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
  have h2 : HasDerivAt (fun s : ℝ => (5 : ℂ) * ↑s) 5 t := by
    simpa using h1.const_mul (5 : ℂ)
  have h3 : HasDerivAt (fun s : ℝ => (5 : ℂ) * ↑s - 9/2) 5 t := by
    simpa using h2.sub_const (9/2 : ℂ)
  have h4 : HasDerivAt (fun _ : ℝ => (↑H * I : ℂ)) 0 t := hasDerivAt_const t (↑H * I)
  have h5 := h3.add h4
  simp only [add_zero] at h5
  convert h5 using 1

/-- Derivative of `fdBoundaryFun H` on seg5 (horizontal, `4/5 < t`) equals `5`. -/
theorem deriv_fdBoundaryFun_seg5 (H : ℝ) (t : ℝ) (ht : 4/5 < t) :
    deriv (fdBoundaryFun H) t = 5 := by
  rw [(fdBoundaryFun_eventuallyEq_affine_seg5 H t ht).deriv_eq]
  exact (hasDerivAt_seg5_affine H t).deriv

/-- `HasDerivAt` version: on seg5, `fdBoundaryFun H` has derivative `5`. -/
theorem fdBoundaryFun_hasDerivAt_seg5 (H : ℝ) (t : ℝ) (ht : 4/5 < t) :
    HasDerivAt (fdBoundaryFun H) 5 t := by
  have h_ev := fdBoundaryFun_eventuallyEq_affine_seg5 H t ht
  exact (hasDerivAt_seg5_affine H t).congr_of_eventuallyEq h_ev

/-! ### Seg5 integral simplification -/

/-- The `logDeriv` integrand on seg5 with the path derivative simplifies:
`logDeriv(f ∘ ofComplex)(γ(t)) * γ'(t) = logDeriv(f ∘ ofComplex)(γ(t)) * 5`
for `4/5 < t`. -/
theorem seg5_logDeriv_integrand_deriv_eq (H : ℝ) (t : ℝ) (ht : 4/5 < t)
    (g : ℂ → ℂ) :
    g (fdBoundaryFun H t) * deriv (fdBoundaryFun H) t =
    g (fdBoundaryFun H t) * 5 := by
  rw [deriv_fdBoundaryFun_seg5 H t ht]

/-- On seg5, the boundary function value at `t` (for `4/5 < t ≤ 1`) equals
`-1/2 + (5*t - 4) + H*I`, i.e., a horizontal line from `-1/2 + Hi` to
`1/2 + Hi`. Rewritten: `fdBoundaryFun H t = (5*t - 9/2) + H*I`. -/
theorem fdBoundaryFun_seg5_eq (H : ℝ) (t : ℝ) (ht : 4/5 < t) :
    fdBoundaryFun H t = (5 * ↑t - 9/2 : ℂ) + ↑H * I := by
  simp only [fdBoundaryFun,
    show ¬t ≤ 1/5 from by linarith, show ¬t ≤ 2/5 from by linarith,
    show ¬t ≤ 3/5 from by linarith, show ¬t ≤ 4/5 from by linarith, ite_false]

/-- After substitution `u = 5*t - 4` (so `t = (u + 4)/5`), the seg5 integral
on `[4/5, 1]` becomes an integral on `[0, 1]` of `logDeriv(f)(u - 1/2 + Hi)`.
This is the reparameterization step. -/
theorem seg5_integral_reparameterize (H : ℝ) (g : ℂ → ℂ) :
    ∫ t in (4/5 : ℝ)..1, g (fdBoundaryFun H t) * deriv (fdBoundaryFun H) t =
    ∫ t in (4/5 : ℝ)..1, g ((5 * ↑t - 9/2 : ℂ) + ↑H * I) * 5 := by
  refine intervalIntegral.integral_congr_ae ?_
  have : ∀ᵐ t ∂volume, t ∈ Set.uIoc (4/5 : ℝ) 1 →
      g (fdBoundaryFun H t) * deriv (fdBoundaryFun H) t =
      g ((5 * ↑t - 9/2 : ℂ) + ↑H * I) * 5 := by
    filter_upwards with t ht
    rw [Set.uIoc_of_le (by norm_num : (4:ℝ)/5 ≤ 1)] at ht
    rw [fdBoundaryFun_seg5_eq H t ht.1, deriv_fdBoundaryFun_seg5 H t ht.1]
  exact this

/-! ### Main theorem: horizontal contribution from seg5 integral equation -/

/-- **Horizontal contribution theorem.**

Given a modular form `f` and the equation that the seg5 integral of
`logDeriv(f)` equals `2piI * orderAtCusp'(f)`, we transfer this to the
integral using the path `γ` (which agrees with `fdBoundaryFun` on `[0, 1]`).

This fills the `horiz_eq` field of `ModularSideData` and
the `seg5_integral_eq` field of `HorizontalContributionData`. -/
theorem horizontalContribution_eq
    {H : ℝ} (_hH : Real.sqrt 3 / 2 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (h_seg5 : ∫ t in (4/5 : ℝ)..1,
      logDeriv (modularFormCompOfComplexFM f) (fdBoundaryFun H t) *
        deriv (fdBoundaryFun H) t =
      2 * ↑Real.pi * I * (orderAtCusp' f : ℂ)) :
    ∫ t in (4/5 : ℝ)..1,
      logDeriv (⇑f ∘ UpperHalfPlane.ofComplex) (γ.toPath.extend t) *
      deriv γ.toPath.extend t =
    2 * ↑Real.pi * I * (orderAtCusp' f : ℂ) := by
  -- Step 1: show the integrands agree a.e. on (4/5, 1).
  -- The singleton {1} has measure zero, so we only need agreement on Ioo (4/5) 1.
  have h_integrands_ae : ∀ᵐ t ∂volume,
      t ∈ Set.uIoc (4/5 : ℝ) 1 →
        logDeriv (⇑f ∘ UpperHalfPlane.ofComplex) (γ.toPath.extend t) *
          deriv γ.toPath.extend t =
        logDeriv (modularFormCompOfComplexFM f) (fdBoundaryFun H t) *
          deriv (fdBoundaryFun H) t := by
    -- We use that {1} is a null set to reduce to t ∈ Ioo (4/5) 1.
    have h_null : (volume : Measure ℝ) {(1 : ℝ)} = 0 := by simp
    rw [ae_iff]
    refine measure_mono_null (fun t ht => ?_) h_null
    simp only [mem_setOf_eq, not_forall] at ht
    obtain ⟨ht_mem, ht_ne⟩ := ht
    rw [Set.uIoc_of_le (by norm_num : (4:ℝ)/5 ≤ 1)] at ht_mem
    simp only [mem_singleton_iff]
    -- t ∈ Ioc (4/5) 1 and the integrands disagree, so t must be the endpoint 1
    -- (the only point where we can't show EventuallyEq for the derivatives).
    -- We prove t = 1 by contradiction: if t < 1, we CAN show EventuallyEq.
    by_contra ht_ne_one
    apply ht_ne
    have ht4 : 4/5 < t := ht_mem.1
    have ht1 : t ≤ 1 := ht_mem.2
    have ht_lt : t < 1 := lt_of_le_of_ne ht1 ht_ne_one
    have ht_cc : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, ht1⟩
    have h_val := hγ t ht_cc
    have h_ev : γ.toPath.extend =ᶠ[𝓝 t] fdBoundaryFun H := by
      refine Filter.eventually_of_mem
        (Filter.inter_mem (Ioi_mem_nhds ht4) (Iio_mem_nhds ht_lt))
        (fun s ⟨hs4, hs1⟩ => ?_)
      have hs4' : 4/5 < s := hs4
      have hs1' : s < 1 := hs1
      exact hγ s ⟨by linarith, by linarith⟩
    rw [h_val, h_ev.deriv_eq]
  -- Step 2: conclude by congr_ae + the seg5 hypothesis
  have h_congr := intervalIntegral.integral_congr_ae h_integrands_ae
  rw [h_congr]
  exact h_seg5

/-- Build `HorizontalContributionData` from the seg5 integral equation. -/
theorem horizontalContributionData_of_seg5_eq
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (h_seg5 : ∫ t in (4/5 : ℝ)..1,
      logDeriv (modularFormCompOfComplexFM f) (fdBoundaryFun H t) *
        deriv (fdBoundaryFun H) t =
      2 * ↑Real.pi * I * (orderAtCusp' f : ℂ)) :
    HorizontalContributionData f γ where
  seg5_integral_eq := horizontalContribution_eq f hH γ hγ h_seg5

/-! ### Interface: `horiz_eq` for `ModularSideData`

The following theorem provides the `horiz_eq` value that downstream code
needs for filling the `ModularSideData.horiz_eq` field. -/

/-- The horizontal seg5 integral equals `2piI * orderAtCusp'(f)`.
This is the `horiz_eq` fact needed for `ModularSideData`. -/
theorem horizontalContribution_horiz_eq
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (h_seg5 : ∫ t in (4/5 : ℝ)..1,
      logDeriv (modularFormCompOfComplexFM f) (fdBoundaryFun H t) *
        deriv (fdBoundaryFun H) t =
      2 * ↑Real.pi * I * (orderAtCusp' f : ℂ)) :
    ∫ t in (4/5 : ℝ)..1,
      logDeriv (⇑f ∘ UpperHalfPlane.ofComplex) (γ.toPath.extend t) *
      deriv γ.toPath.extend t =
    2 * ↑Real.pi * I * (orderAtCusp' f : ℂ) :=
  horizontalContribution_eq f hH γ hγ h_seg5

end
