/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.CauchyPrincipalValue
import LeanModularForms.ForMathlib.ClassicalCPV
import LeanModularForms.ForMathlib.FDBoundary
import LeanModularForms.ForMathlib.FDBoundaryH
import LeanModularForms.ForMathlib.FDBoundaryPath
import LeanModularForms.ForMathlib.GeneralizedWindingNumber

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
* `integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun` — integral change of variables
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

/-- The ForMathlib `fdBoundaryFun` is the old-chain `fdBoundary_H` after
reparametrization `t ↦ 5t`. -/
theorem fdBoundaryFun_eq_fdBoundary_H_scaled (H : ℝ) (t : ℝ) :
    fdBoundaryFun H t = fdBoundary_H H (5 * t) := by
  unfold fdBoundaryFun fdBoundary_H
  by_cases h1 : t ≤ 1/5
  · rw [if_pos h1, if_pos (by linarith : 5 * t ≤ 1)]
    push_cast
    ring
  rw [if_neg h1, if_neg (by linarith : ¬ 5 * t ≤ 1)]
  by_cases h2 : t ≤ 2/5
  · rw [if_pos h2, if_pos (by linarith : 5 * t ≤ 2)]
    congr 1
    push_cast
    ring
  rw [if_neg h2, if_neg (by linarith : ¬ 5 * t ≤ 2)]
  by_cases h3 : t ≤ 3/5
  · rw [if_pos h3, if_pos (by linarith : 5 * t ≤ 3)]
    congr 1
    push_cast
    ring
  rw [if_neg h3, if_neg (by linarith : ¬ 5 * t ≤ 3)]
  by_cases h4 : t ≤ 4/5
  · rw [if_pos h4, if_pos (by linarith : 5 * t ≤ 4)]
    push_cast
    ring
  rw [if_neg h4, if_neg (by linarith : ¬ 5 * t ≤ 4)]
  push_cast
  ring

/-- As a function composition identity. -/
theorem fdBoundaryFun_eq_comp (H : ℝ) :
    fdBoundaryFun H = fun t => fdBoundary_H H (5 * t) :=
  funext (fdBoundaryFun_eq_fdBoundary_H_scaled H)

/-- Linear change-of-variable identity:
`∫_{0}^{5} F u du = 5 * ∫_{0}^{1} F(5t) dt`.

This is a specialization of `intervalIntegral.smul_integral_comp_mul_left`
with `a = 0, b = 1, c = 5`. -/
theorem integral_zero_to_five_eq_five_smul_zero_to_one (F : ℝ → ℂ) :
    ∫ u in (0 : ℝ)..5, F u = (5 : ℝ) • ∫ t in (0 : ℝ)..1, F (5 * t) := by
  simpa only [mul_zero, mul_one] using
    (intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1) (f := F) 5).symm

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
  exact_mod_cast deriv_fdBoundaryFun_eq_five_deriv_fdBoundary_H H t

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
  simp only [cpvIntegrand, fdBoundaryFun_eq_fdBoundary_H_scaled, deriv_fdBoundaryFun_eq]
  split_ifs <;> ring

/-- The integral of the old-chain CPV integrand from 0 to 5 equals
the integral of the new-chain CPV integrand from 0 to 1. -/
theorem integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun
    (f : ℂ → ℂ) (z₀ : ℂ) (ε : ℝ) (H : ℝ) :
    ∫ u in (0 : ℝ)..5,
      (if ‖fdBoundary_H H u - z₀‖ > ε then
        f (fdBoundary_H H u) * deriv (fdBoundary_H H) u else 0) =
    ∫ t in (0 : ℝ)..1, cpvIntegrand f (fdBoundaryFun H) z₀ ε t := by
  have h_left : (∫ u in (0 : ℝ)..5,
      (if ‖fdBoundary_H H u - z₀‖ > ε then
        f (fdBoundary_H H u) * deriv (fdBoundary_H H) u else 0)) =
      ∫ t in (0 : ℝ)..1, (5 : ℂ) *
        (if ‖fdBoundary_H H (5 * t) - z₀‖ > ε then
          f (fdBoundary_H H (5 * t)) * deriv (fdBoundary_H H) (5 * t) else 0) := by
    rw [integral_zero_to_five_eq_five_smul_zero_to_one, Complex.real_smul]
    push_cast
    exact (intervalIntegral.integral_const_mul (5 : ℂ) _).symm
  rw [h_left]
  exact intervalIntegral.integral_congr fun t _ =>
    (cpvIntegrand_fdBoundaryFun_eq_smul_cpvIntegrand_fdBoundary_H f z₀ ε t H).symm

private lemma mem_Ioo_zero_one_of_uIoc {t : ℝ} (ht_ne_1 : t ∈ ({1} : Set ℝ)ᶜ)
    (ht_mem : t ∈ Ioc (0 : ℝ) 1) : t ∈ Ioo (0 : ℝ) 1 :=
  ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 fun h => ht_ne_1 (mem_singleton_iff.mpr h)⟩

/-- Helper: a path agreeing with `fdBoundaryFun H` on `Icc 0 1` is eventually
equal to `fdBoundaryFun H` in a punctured neighborhood of any interior point. -/
private lemma extend_eventuallyEq_fdBoundaryFun {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    γ.toPath.extend =ᶠ[𝓝 t] fdBoundaryFun H := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact hγ s (Ioo_subset_Icc_self hs)

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
    rw [integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun (fun z => (z - z₀)⁻¹) z₀ ε H]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton 1)] with t ht_ne_1 ht_mem
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht_mem
    have ht_open : t ∈ Ioo (0 : ℝ) 1 := mem_Ioo_zero_one_of_uIoc ht_ne_1 ht_mem
    simp only [cpvIntegrand, hγ t (Ioo_subset_Icc_self ht_open)]
    rw [(extend_eventuallyEq_fdBoundaryFun γ hγ ht_open).symm.deriv_eq]
  simpa [HasCauchyPV] using h_old.congr h_eq

/-- Multi-point version: the integrand at parameter `t` on the new chain
equals 5 times the integrand at parameter `5*t` on the old chain. -/
theorem cpvIntegrandOn_fdBoundaryFun_eq_smul_fdBoundary_H
    (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) (t : ℝ) (H : ℝ) :
    cpvIntegrandOn S f (fdBoundaryFun H) ε t =
    (5 : ℂ) * (if ∃ s ∈ S, ‖fdBoundary_H H (5 * t) - s‖ ≤ ε then 0
      else f (fdBoundary_H H (5 * t)) * deriv (fdBoundary_H H) (5 * t)) := by
  simp only [cpvIntegrandOn, fdBoundaryFun_eq_fdBoundary_H_scaled, deriv_fdBoundaryFun_eq]
  split_ifs <;> ring

/-- Multi-point integral equivalence: the integral over `[0, 5]` of the
old-chain CPV integrand equals the integral over `[0, 1]` of the new-chain
`cpvIntegrandOn` integrand. -/
theorem integral_cpvIntegrandOn_fdBoundary_H_eq_fdBoundaryFun
    (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) (H : ℝ) :
    ∫ u in (0 : ℝ)..5,
      (if ∃ s ∈ S, ‖fdBoundary_H H u - s‖ ≤ ε then 0
        else f (fdBoundary_H H u) * deriv (fdBoundary_H H) u) =
    ∫ t in (0 : ℝ)..1, cpvIntegrandOn S f (fdBoundaryFun H) ε t := by
  have h_left : (∫ u in (0 : ℝ)..5,
      (if ∃ s ∈ S, ‖fdBoundary_H H u - s‖ ≤ ε then 0
        else f (fdBoundary_H H u) * deriv (fdBoundary_H H) u)) =
      ∫ t in (0 : ℝ)..1, (5 : ℂ) *
        (if ∃ s ∈ S, ‖fdBoundary_H H (5 * t) - s‖ ≤ ε then 0
          else f (fdBoundary_H H (5 * t)) * deriv (fdBoundary_H H) (5 * t)) := by
    rw [integral_zero_to_five_eq_five_smul_zero_to_one, Complex.real_smul]
    push_cast
    exact (intervalIntegral.integral_const_mul (5 : ℂ) _).symm
  rw [h_left]
  exact intervalIntegral.integral_congr fun t _ =>
    (cpvIntegrandOn_fdBoundaryFun_eq_smul_fdBoundary_H S f ε t H).symm

/-- Multi-point version: convert a Tendsto statement about the old-chain
multi-point CPV integrand on `[0, 5]` into a ForMathlib `HasCauchyPVOn`
statement on a `PiecewiseC1Path` agreeing with `fdBoundaryFun H`. -/
theorem hasCauchyPVOn_of_cauchyPVOn'_tendsto
    {H : ℝ} {S : Finset ℂ} {f : ℂ → ℂ} {L : ℂ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (h_old : Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..5,
        if ∃ s ∈ S, ‖fdBoundary_H H t - s‖ ≤ ε then 0
          else f (fdBoundary_H H t) * deriv (fdBoundary_H H) t)
      (𝓝[>] 0) (𝓝 L)) :
    HasCauchyPVOn S f γ L := by
  have h_eq : ∀ ε : ℝ,
      (∫ t in (0 : ℝ)..5,
        if ∃ s ∈ S, ‖fdBoundary_H H t - s‖ ≤ ε then 0
          else f (fdBoundary_H H t) * deriv (fdBoundary_H H) t) =
      ∫ t in (0 : ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t := by
    intro ε
    rw [integral_cpvIntegrandOn_fdBoundary_H_eq_fdBoundaryFun S f ε H]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton 1)] with t ht_ne_1 ht_mem
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht_mem
    have ht_open : t ∈ Ioo (0 : ℝ) 1 := mem_Ioo_zero_one_of_uIoc ht_ne_1 ht_mem
    simp only [cpvIntegrandOn, hγ t (Ioo_subset_Icc_self ht_open)]
    rw [(extend_eventuallyEq_fdBoundaryFun γ hγ ht_open).symm.deriv_eq]
  simpa [HasCauchyPVOn] using h_old.congr h_eq

/-- Bridge: from an old-chain `CauchyPrincipalValueExists'` result, derive the
new-chain `HasGeneralizedWindingNumber`. -/
theorem hasGeneralizedWindingNumber_of_cauchyPrincipalValueExists'_tendsto
    {H : ℝ} {z₀ : ℂ} {w : ℂ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (h_old : Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..5,
        if ‖fdBoundary_H H t - z₀‖ > ε then
          (fdBoundary_H H t - z₀)⁻¹ * deriv (fdBoundary_H H) t
        else 0)
      (𝓝[>] 0) (𝓝 (2 * ↑Real.pi * I * w))) :
    HasGeneralizedWindingNumber γ z₀ w := by
  simp only [HasGeneralizedWindingNumber]
  exact hasCauchyPV_of_cauchyPV'_tendsto γ hγ h_old

/-- **Winding number equality**: if a new-chain `PiecewiseC1Path` agrees with
`fdBoundaryFun H` on `[0, 1]` and the old-chain winding number has a value,
then so does the new-chain one and they are equal. -/
theorem generalizedWindingNumber_eq_of_agreement
    {H : ℝ} {z₀ : ℂ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (w : ℂ)
    (h_old : Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..5,
        if ‖fdBoundary_H H t - z₀‖ > ε then
          (fdBoundary_H H t - z₀)⁻¹ * deriv (fdBoundary_H H) t
        else 0)
      (𝓝[>] 0) (𝓝 (2 * ↑Real.pi * I * w))) :
    generalizedWindingNumber γ z₀ = w :=
  (hasGeneralizedWindingNumber_of_cauchyPrincipalValueExists'_tendsto γ hγ h_old).eq

/-- **Reverse bridge**: from a new-chain `HasGeneralizedWindingNumber` (with a
known value `w`), derive the old chain's `generalizedWindingNumber' = w`.

This is the per-point converter: if the new chain proves a winding number value,
the old chain's parametrization gives the same value. -/
theorem generalizedWindingNumberPrime_eq_of_hasGeneralizedWindingNumber
    {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {z₀ w : ℂ} (h : HasGeneralizedWindingNumber γ z₀ w) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 z₀ = w := by
  simp only [HasGeneralizedWindingNumber, HasCauchyPV] at h
  have h_eq : ∀ ε : ℝ,
      (∫ t in (0 : ℝ)..1, cpvIntegrand (fun z => (z - z₀)⁻¹) γ.toPath.extend z₀ ε t) =
      ∫ t in (0 : ℝ)..5,
        if ‖fdBoundary_H H t - z₀‖ > ε then
          (fdBoundary_H H t - z₀)⁻¹ * deriv (fdBoundary_H H) t
        else 0 := by
    intro ε
    have h_swap :
        (∫ t in (0 : ℝ)..1, cpvIntegrand (fun z => (z - z₀)⁻¹) γ.toPath.extend z₀ ε t) =
          ∫ t in (0 : ℝ)..1, cpvIntegrand (fun z => (z - z₀)⁻¹) (fdBoundaryFun H) z₀ ε t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton 1)] with t ht_ne_1 ht_mem
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht_mem
      have ht_open : t ∈ Ioo (0 : ℝ) 1 := mem_Ioo_zero_one_of_uIoc ht_ne_1 ht_mem
      simp only [cpvIntegrand, hγ t (Ioo_subset_Icc_self ht_open)]
      rw [(extend_eventuallyEq_fdBoundaryFun γ hγ ht_open).symm.deriv_eq]
    rw [h_swap,
      ← integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun (fun z => (z - z₀)⁻¹) z₀ ε H]
  have h_pv_val : cauchyPrincipalValue' (·⁻¹) (fun t => fdBoundary_H H t - z₀) 0 5 0 =
      2 * ↑Real.pi * I * w := by
    simp only [cauchyPrincipalValue']
    refine ((h.congr h_eq).congr' ?_).limUnder_eq
    filter_upwards with ε
    exact intervalIntegral.integral_congr fun t _ => by simp [deriv_sub_const]
  simp only [generalizedWindingNumber', h_pv_val]
  field_simp [Complex.two_pi_I_ne_zero]

/-- When the old chain's `cauchyPrincipalValueExists'` for the winding integrand
has an old-chain value, the new chain's `generalizedWindingNumber` equals the
old chain's `generalizedWindingNumber'`. -/
theorem generalizedWindingNumber_eq_generalizedWindingNumber'
    {H : ℝ} {z₀ : ℂ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (h_exists : CauchyPrincipalValueExists' (·⁻¹)
      (fun t => fdBoundary_H H t - z₀) 0 5 0) :
    generalizedWindingNumber γ z₀ =
      generalizedWindingNumber' (fdBoundary_H H) 0 5 z₀ := by
  obtain ⟨L, hL⟩ := h_exists
  set w := (2 * ↑Real.pi * I)⁻¹ * L with hw_def
  have hL_eq : L = 2 * ↑Real.pi * I * w := by
    rw [hw_def]
    field_simp [Complex.two_pi_I_ne_zero]
  have h_simpl : Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..5,
        if ‖fdBoundary_H H t - z₀‖ > ε then
          (fdBoundary_H H t - z₀)⁻¹ * deriv (fdBoundary_H H) t
        else 0) (𝓝[>] 0) (𝓝 (2 * ↑Real.pi * I * w)) := by
    rw [← hL_eq]
    refine hL.congr' ?_
    filter_upwards with ε
    exact intervalIntegral.integral_congr fun t _ => by simp [deriv_sub_const]
  have h_gWN' : generalizedWindingNumber' (fdBoundary_H H) 0 5 z₀ = w := by
    simp only [generalizedWindingNumber', cauchyPrincipalValue']
    exact congr_arg _ hL.limUnder_eq
  rw [h_gWN']
  exact generalizedWindingNumber_eq_of_agreement γ hγ w h_simpl

end
