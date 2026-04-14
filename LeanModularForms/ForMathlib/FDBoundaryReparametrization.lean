/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.CauchyPrincipalValue
import LeanModularForms.ForMathlib.FDBoundary
import LeanModularForms.ForMathlib.FDBoundaryPath
import LeanModularForms.ValenceFormula.Boundary.Basic
import LeanModularForms.GeneralizedResidueTheory.Basic

/-!
# Bridge: `fdBoundaryFun` ↔ `fdBoundary_H`

This file establishes the reparametrization bridge between:
- `fdBoundaryFun H : ℝ → ℂ` parametrized on `[0, 1]` (ForMathlib chain)
- `fdBoundary_H H : ℝ → ℂ` parametrized on `[0, 5]` (old ValenceFormula chain)

The bridge is simply `u = 5*t`: `fdBoundaryFun H t = fdBoundary_H H (5*t)`.

This is used to bridge residue/modular side Tendsto results between the two
chains until the residue side is fully ported to the ForMathlib chain.

## Main results

* `fdBoundaryFun_eq_fdBoundary_H_scaled` — the key reparametrization identity
* `fdBoundaryFun_eq_comp` — the equation as a function composition
* `fdBoundaryFun_integral_eq_fdBoundary_H_integral` — integral change of variables
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

/-- The ForMathlib `fdBoundaryFun` is the old-chain `fdBoundary_H` after
reparametrization `t ↦ 5t`. -/
theorem fdBoundaryFun_eq_fdBoundary_H_scaled (H : ℝ) (t : ℝ) :
    fdBoundaryFun H t = fdBoundary_H H (5 * t) := by
  unfold fdBoundaryFun fdBoundary_H
  by_cases h1 : t ≤ 1/5
  · have h1' : 5 * t ≤ 1 := by linarith
    simp only [h1, h1', ite_true]
    push_cast; ring
  · have h1' : ¬ (5 * t ≤ 1) := by push Not at h1; linarith
    by_cases h2 : t ≤ 2/5
    · have h2' : 5 * t ≤ 2 := by linarith
      simp only [h1, h2, h1', h2', ite_true, ite_false]
      congr 1; push_cast; ring
    · have h2' : ¬ (5 * t ≤ 2) := by push Not at h2; linarith
      by_cases h3 : t ≤ 3/5
      · have h3' : 5 * t ≤ 3 := by linarith
        simp only [h1, h2, h3, h1', h2', h3', ite_true, ite_false]
        congr 1; push_cast; ring
      · have h3' : ¬ (5 * t ≤ 3) := by push Not at h3; linarith
        by_cases h4 : t ≤ 4/5
        · have h4' : 5 * t ≤ 4 := by linarith
          simp only [h1, h2, h3, h4, h1', h2', h3', h4', ite_true, ite_false]
          push_cast; ring
        · have h4' : ¬ (5 * t ≤ 4) := by push Not at h4; linarith
          simp only [h1, h2, h3, h4, h1', h2', h3', h4', ite_false]
          push_cast; ring

/-- As a function composition identity. -/
theorem fdBoundaryFun_eq_comp (H : ℝ) :
    fdBoundaryFun H = fun t => fdBoundary_H H (5 * t) :=
  funext (fdBoundaryFun_eq_fdBoundary_H_scaled H)

/-! ### Integral change of variables for `[0, 1] ↔ [0, 5]` -/

/-- Linear change-of-variable identity:
`∫_{0}^{5} F u du = 5 * ∫_{0}^{1} F(5t) dt`.

This is a specialization of `intervalIntegral.smul_integral_comp_mul_add`
with `c = 5, d = 0, a = 0, b = 1`. -/
theorem integral_zero_to_five_eq_five_smul_zero_to_one (F : ℝ → ℂ) :
    ∫ u in (0 : ℝ)..5, F u = (5 : ℝ) • ∫ t in (0 : ℝ)..1, F (5 * t) := by
  have h := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1) F
    (5 : ℝ) (0 : ℝ)
  simp only [add_zero, mul_zero, mul_one] at h
  exact h.symm

/-! ### Derivative chain rule for the reparametrization -/

/-- The derivative of `fdBoundaryFun H` is 5 times the derivative of
`fdBoundary_H H` at the reparametrized point. Works everywhere thanks to
`deriv_comp_mul_left` (which handles both the differentiable and the
non-differentiable case uniformly). -/
theorem deriv_fdBoundaryFun_eq_five_deriv_fdBoundary_H (H : ℝ) (t : ℝ) :
    deriv (fdBoundaryFun H) t = (5 : ℝ) • deriv (fdBoundary_H H) (5 * t) := by
  rw [fdBoundaryFun_eq_comp]
  exact deriv_comp_mul_left (5 : ℝ) (fdBoundary_H H) t

/-- Complex-valued version: `deriv (fdBoundaryFun H) t = 5 * deriv (fdBoundary_H H) (5*t)`. -/
theorem deriv_fdBoundaryFun_eq (H : ℝ) (t : ℝ) :
    deriv (fdBoundaryFun H) t = (5 : ℂ) * deriv (fdBoundary_H H) (5 * t) := by
  rw [deriv_fdBoundaryFun_eq_five_deriv_fdBoundary_H]
  rw [show ((5 : ℝ) • deriv (fdBoundary_H H) (5 * t) : ℂ) =
    (5 : ℝ) * deriv (fdBoundary_H H) (5 * t) from rfl]
  push_cast; ring

/-! ### Integrand equivalence for Cauchy PV -/

/-- The Cauchy PV integrand using `fdBoundaryFun` and `[0,1]` equals
`5` times the integrand using `fdBoundary_H` and `[0,5]` after reparametrization.

Specifically, at any point `t`, the integrand at parameter `t` (new chain)
equals `5` times the integrand at parameter `5*t` (old chain). This factor
of 5 is absorbed by the integration domain via change of variables. -/
theorem cpvIntegrand_fdBoundaryFun_eq_smul_cpvIntegrand_fdBoundary_H
    (f : ℂ → ℂ) (z₀ : ℂ) (ε : ℝ) (t : ℝ) (H : ℝ) :
    cpvIntegrand f (fdBoundaryFun H) z₀ ε t =
    (5 : ℂ) * (if ‖fdBoundary_H H (5 * t) - z₀‖ > ε
      then f (fdBoundary_H H (5 * t)) * deriv (fdBoundary_H H) (5 * t) else 0) := by
  simp only [cpvIntegrand]
  rw [fdBoundaryFun_eq_fdBoundary_H_scaled, deriv_fdBoundaryFun_eq]
  split_ifs with h
  · ring
  · ring

/-- The integral of the old-chain CPV integrand from 0 to 5 equals
the integral of the new-chain CPV integrand from 0 to 1. -/
theorem integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun
    (f : ℂ → ℂ) (z₀ : ℂ) (ε : ℝ) (H : ℝ) :
    ∫ u in (0 : ℝ)..5,
      (if ‖fdBoundary_H H u - z₀‖ > ε then
        f (fdBoundary_H H u) * deriv (fdBoundary_H H) u else 0) =
    ∫ t in (0 : ℝ)..1, cpvIntegrand f (fdBoundaryFun H) z₀ ε t := by
  -- Strategy: show both sides equal ∫ t in 0..1, 5 * old_integrand t
  -- LHS via change of variables and integral_const_mul
  -- RHS via h_pointwise equation
  have h_left : (∫ u in (0 : ℝ)..5,
      (if ‖fdBoundary_H H u - z₀‖ > ε then
        f (fdBoundary_H H u) * deriv (fdBoundary_H H) u else 0)) =
      ∫ t in (0 : ℝ)..1, (5 : ℂ) *
        (if ‖fdBoundary_H H (5 * t) - z₀‖ > ε then
          f (fdBoundary_H H (5 * t)) * deriv (fdBoundary_H H) (5 * t) else 0) := by
    rw [integral_zero_to_five_eq_five_smul_zero_to_one]
    rw [show ∀ v : ℂ, ((5 : ℝ) • v) = (5 : ℂ) * v from fun v => by
      rw [Complex.real_smul]; push_cast; ring]
    exact (intervalIntegral.integral_const_mul (5 : ℂ) _).symm
  rw [h_left]
  exact intervalIntegral.integral_congr (fun t _ =>
    (cpvIntegrand_fdBoundaryFun_eq_smul_cpvIntegrand_fdBoundary_H f z₀ ε t H).symm)

/-! ### Winding number equivalence -/

/-- For a `PiecewiseC1Path` that agrees with `fdBoundaryFun H` on `[0, 1]`,
the ForMathlib-style `HasCauchyPV` predicate at `z₀` for `(· - z₀)⁻¹`
corresponds exactly to the old-chain's `cauchyPrincipalValueExists'`
for `fdBoundary_H H` on `[0, 5]`.

This is the bridge that allows old-chain residue side results to be
transferred to the new chain. -/
theorem hasCauchyPV_of_cauchyPV'_tendsto
    {H : ℝ} {z₀ : ℂ} {L : ℂ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (h_old : Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..5,
        if ‖fdBoundary_H H t - z₀‖ > ε then
          (fdBoundary_H H t - z₀)⁻¹ * deriv (fdBoundary_H H) t
        else 0)
      (𝓝[>] 0) (𝓝 L)) :
    HasCauchyPV (fun z => (z - z₀)⁻¹) γ z₀ L := by
  have h_eq : ∀ ε : ℝ,
      (∫ t in (0 : ℝ)..5,
        if ‖fdBoundary_H H t - z₀‖ > ε then
          (fdBoundary_H H t - z₀)⁻¹ * deriv (fdBoundary_H H) t else 0) =
      ∫ t in (0 : ℝ)..1, cpvIntegrand (fun z => (z - z₀)⁻¹) γ.toPath.extend z₀ ε t := by
    intro ε
    rw [integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun
      (fun z => (z - z₀)⁻¹) z₀ ε H]
    -- Use a.e. equality on the open interval (0,1)
    apply intervalIntegral.integral_congr_ae
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton 1)] with t ht_ne_1 ht_mem
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht_mem
    have ht_open : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 fun h => ht_ne_1 (mem_singleton_iff.mpr h)⟩
    have ht_icc : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht_open
    show cpvIntegrand (fun z => (z - z₀)⁻¹) (fdBoundaryFun H) z₀ ε t =
      cpvIntegrand (fun z => (z - z₀)⁻¹) γ.toPath.extend z₀ ε t
    simp only [cpvIntegrand, hγ t ht_icc]
    have hee : γ.toPath.extend =ᶠ[𝓝 t] fdBoundaryFun H := by
      filter_upwards [Ioo_mem_nhds ht_open.1 ht_open.2] with s hs
      exact hγ s (Ioo_subset_Icc_self hs)
    rw [hee.symm.deriv_eq]
  simp only [HasCauchyPV]
  exact (h_old.congr h_eq)

end
