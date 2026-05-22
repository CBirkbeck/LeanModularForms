/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.FlatnessConditions
import LeanModularForms.ForMathlib.SegmentFTC
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Sector Curve Analysis

Model curves for crossing analysis: sector curves that serve as local models near
pole crossings. These are used to analyze the CPV of higher-order polar terms
`a_k / (z - s)^k` along a curve that crosses `s`.

## Main definitions

* `SectorCurve.lineCurve` — a straight line through the origin at angle `α`,
  parametrized as `t ↦ r * t * exp(i α)`.

* `SectorCurve.higherOrderFactor` — the constant factor `r⁻ᵏ * exp(-ikα)` appearing
  when computing `z⁻⁽ᵏ⁺¹⁾ dz` along the line curve.

## Main results

* `SectorCurve.lineCurve_integrand_inv` — the integrand of `z⁻¹ dz` simplifies to `t⁻¹`.
* `SectorCurve.exp_factor_eq_one_of_angle_condition` — `exp(-ikα) = 1` when `kα ∈ 2πℤ`.
* `SectorCurve.pv_odd_power_vanishes` — for odd `k ≥ 1`, PV of `(↑t)⁻¹ ^ k` is zero.
* `SectorCurve.higherOrder_terms_odd_vanish` — for odd `k ≥ 3`, the PV of
  `z⁻ᵏ dz` along the sector curve vanishes.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2, Lemma 3.1 and Theorem 3.3
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

noncomputable section

namespace SectorCurve

/-! ### The model line curve through the origin -/

/-- A model straight-line curve through the origin at angle `α`:
`γ(t) = r * t * exp(i α)`. -/
def lineCurve (r : ℝ) (α : ℝ) (t : ℝ) : ℂ :=
  ↑(r * t) * exp (↑α * I)

@[simp]
theorem lineCurve_zero (r : ℝ) (α : ℝ) : lineCurve r α 0 = 0 := by
  simp [lineCurve]

theorem lineCurve_eq (r : ℝ) (α : ℝ) (t : ℝ) :
    lineCurve r α t = ↑(r * t) * exp (↑α * I) := rfl

theorem lineCurve_neg (r : ℝ) (α : ℝ) (t : ℝ) :
    lineCurve r α (-t) = -lineCurve r α t := by
  simp [lineCurve, mul_neg]

theorem lineCurve_ne_zero (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ≠ 0) :
    lineCurve r α t ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero hr.ne' ht)) (exp_ne_zero _)

theorem lineCurve_continuous (r : ℝ) (α : ℝ) : Continuous (lineCurve r α) := by
  unfold lineCurve; fun_prop

theorem lineCurve_hasDerivAt (r : ℝ) (α : ℝ) (t : ℝ) :
    HasDerivAt (lineCurve r α) (↑r * exp (↑α * I)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (↑(r * s) : ℂ)) (↑r) t := by
    simpa using ((hasDerivAt_id t).const_mul r).ofReal_comp
  exact h1.mul_const _

theorem lineCurve_deriv (r : ℝ) (α : ℝ) (t : ℝ) :
    deriv (lineCurve r α) t = ↑r * exp (↑α * I) :=
  (lineCurve_hasDerivAt r α t).deriv

theorem lineCurve_deriv_const (r : ℝ) (α : ℝ) :
    deriv (lineCurve r α) = fun _ => ↑r * exp (↑α * I) :=
  funext (lineCurve_deriv r α)

/-! ### Integrand computation -/

/-- The integrand of `z⁻¹ · dz` along the line curve simplifies to `t⁻¹`. -/
theorem lineCurve_integrand_inv (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ≠ 0) :
    (lineCurve r α t)⁻¹ * deriv (lineCurve r α) t = ↑t⁻¹ := by
  rw [lineCurve_eq, lineCurve_deriv]
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hexp : exp (↑α * I) ≠ 0 := exp_ne_zero _
  simp only [mul_inv_rev, Complex.ofReal_mul]
  field_simp
  push_cast
  field_simp

/-! ### The higher-order factor -/

/-- The constant factor `r⁻ᵏ · exp(-ikα)` in the higher-order integrand. -/
def higherOrderFactor (r : ℝ) (α : ℝ) (k : ℕ) : ℂ :=
  ↑(r⁻¹ ^ k) * exp (-(↑k : ℂ) * (↑α * I))

@[simp]
theorem higherOrderFactor_zero (r : ℝ) (α : ℝ) : higherOrderFactor r α 0 = 1 := by
  simp [higherOrderFactor]

/-- When `k · α ∈ 2πℤ`, the exponential factor `exp(-ikα)` equals `1`. -/
theorem exp_factor_eq_one_of_angle_condition (k : ℕ) (α : ℝ)
    (h : ∃ m : ℤ, (↑k : ℝ) * α = ↑m * (2 * Real.pi)) :
    exp (-(↑k : ℂ) * (↑α * I)) = 1 := by
  obtain ⟨m, hm⟩ := h
  have hcast : (↑k : ℂ) * ↑α = ↑m * (2 * ↑Real.pi) := by exact_mod_cast hm
  rw [show -(↑k : ℂ) * (↑α * I) = ↑(-m) * (2 * ↑Real.pi * I) by
        push_cast; linear_combination -hcast * I]
  exact exp_int_mul_two_pi_mul_I (-m)

/-! ### Odd-power PV vanishes by symmetry

The key technique: rewrite `∫_{-1}^{-ε} f(t) dt` as `∫_{ε}^{1} f(-t) dt`
using `integral_comp_neg`, then use the odd-symmetry `f(-t) = -f(t)` to cancel. -/

/-- Helper: the odd-symmetry cancellation pattern. Given `f(-t) = -f(t)`,
the function `ε ↦ ∫_{-1}^{-ε} f + ∫_{ε}^{1} f` is identically zero. -/
private theorem pv_odd_cancel_aux {f : ℝ → ℂ} (hodd : ∀ t, f (-t) = -f t) :
    (fun ε => (∫ t in (-1 : ℝ)..(-ε), f t) + ∫ t in ε..(1 : ℝ), f t) =
    (fun _ => (0 : ℂ)) := by
  funext ε
  have key : ∫ t in (-1 : ℝ)..(-ε), f t = -(∫ t in ε..(1 : ℝ), f t) := by
    calc ∫ t in (-1 : ℝ)..(-ε), f t
        = ∫ t in ε..1, f (-t) := (intervalIntegral.integral_comp_neg f).symm
      _ = ∫ t in ε..1, -f t := by simp_rw [hodd]
      _ = -(∫ t in ε..1, f t) := intervalIntegral.integral_neg
  rw [key, neg_add_cancel]

/-- For odd `k ≥ 1`, the PV integral of `(↑t)⁻¹ ^ k` on `[-1, 1]` is zero. -/
theorem pv_odd_power_vanishes (k : ℕ) (_hk : 1 ≤ k) (hk_odd : Odd k) :
    Tendsto (fun ε =>
      (∫ t in (-1 : ℝ)..(-ε), (↑t : ℂ)⁻¹ ^ k) +
      ∫ t in ε..(1 : ℝ), (↑t : ℂ)⁻¹ ^ k)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [pv_odd_cancel_aux (fun t => by
    rw [Complex.ofReal_neg, inv_neg, neg_pow, hk_odd.neg_one_pow, neg_one_mul])]
  exact tendsto_const_nhds

/-! ### Line-curve integrand: odd symmetry -/

/-- For odd `k ≥ 3`, the PV of `z⁻ᵏ dz` along the line curve vanishes. -/
theorem higherOrder_terms_odd_vanish (r : ℝ) (_hr : 0 < r) (α : ℝ)
    (k : ℕ) (_hk : 3 ≤ k) (hk_odd : Odd k) :
    Tendsto (fun ε =>
      (∫ t in (-1 : ℝ)..(-ε),
        (lineCurve r α t)⁻¹ ^ k * deriv (lineCurve r α) t) +
      ∫ t in ε..(1 : ℝ),
        (lineCurve r α t)⁻¹ ^ k * deriv (lineCurve r α) t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [pv_odd_cancel_aux (fun t => by
    rw [lineCurve_neg, inv_neg, neg_pow, hk_odd.neg_one_pow, neg_one_mul,
        lineCurve_deriv, lineCurve_deriv, neg_mul])]
  exact tendsto_const_nhds

end SectorCurve
