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
  simp only [lineCurve, mul_neg, Complex.ofReal_neg, neg_mul]

theorem lineCurve_norm (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) :
    ‖lineCurve r α t‖ = r * |t| := by
  simp only [lineCurve, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
    mul_one, Real.norm_eq_abs, abs_of_pos hr]

theorem lineCurve_ne_zero (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ≠ 0) :
    lineCurve r α t ≠ 0 := by
  rw [lineCurve]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero hr.ne' ht)) (exp_ne_zero _)

theorem lineCurve_continuous (r : ℝ) (α : ℝ) : Continuous (lineCurve r α) := by
  unfold lineCurve
  exact (continuous_ofReal.comp (continuous_const.mul continuous_id')).mul continuous_const

theorem lineCurve_hasDerivAt (r : ℝ) (α : ℝ) (t : ℝ) :
    HasDerivAt (lineCurve r α) (↑r * exp (↑α * I)) t := by
  unfold lineCurve
  have h1 : HasDerivAt (fun s => (↑(r * s) : ℂ)) (↑r) t := by
    have := ((hasDerivAt_id t).const_mul r).ofReal_comp
    convert this using 1; simp
  exact h1.mul_const _

theorem lineCurve_differentiableAt (r : ℝ) (α : ℝ) (t : ℝ) :
    DifferentiableAt ℝ (lineCurve r α) t :=
  (lineCurve_hasDerivAt r α t).differentiableAt

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
  have hexp : exp (↑α * I) ≠ 0 := exp_ne_zero _
  rw [mul_inv_rev]
  calc (exp (↑α * I))⁻¹ * (↑(r * t))⁻¹ * (↑r * exp (↑α * I))
      = (↑(r * t))⁻¹ * ((exp (↑α * I))⁻¹ * (↑r * exp (↑α * I))) := by ring
    _ = (↑(r * t))⁻¹ * (↑r * ((exp (↑α * I))⁻¹ * exp (↑α * I))) := by ring
    _ = (↑(r * t))⁻¹ * (↑r * 1) := by rw [inv_mul_cancel₀ hexp]
    _ = (↑(r * t))⁻¹ * ↑r := by ring
    _ = ↑t⁻¹ := by
        have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
        have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
        push_cast
        rw [mul_inv]
        -- Goal: (↑r)⁻¹ * (↑t)⁻¹ * ↑r = (↑t)⁻¹
        rw [show (↑r : ℂ)⁻¹ * (↑t)⁻¹ * ↑r = (↑r)⁻¹ * ↑r * (↑t)⁻¹ from by ring,
            inv_mul_cancel₀ hr', one_mul]

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
  rw [show -(↑k : ℂ) * (↑α * I) = ↑(-m) * (2 * ↑Real.pi * I) from by
    push_cast
    rw [show -(↑k : ℂ) * (↑α * I) = -((↑k * ↑α) * I) from by ring,
        show (↑k : ℂ) * ↑α = (↑(↑k * α) : ℂ) from by push_cast; ring, hm]
    push_cast; ring]
  exact exp_int_mul_two_pi_mul_I (-m)

/-- The higher-order factor simplifies when the angle condition holds. -/
theorem higherOrderFactor_eq_of_angle_condition (r : ℝ) (α : ℝ) (k : ℕ)
    (h : ∃ m : ℤ, (↑k : ℝ) * α = ↑m * (2 * Real.pi)) :
    higherOrderFactor r α k = ↑(r⁻¹ ^ k) := by
  unfold higherOrderFactor
  rw [exp_factor_eq_one_of_angle_condition k α h, mul_one]

/-- Condition B implies the exponential prefactor equals 1. -/
theorem conditionB_exp_factor (k : ℕ) (α : ℝ) (_hk : 1 ≤ k)
    (h_angle : ∃ m : ℤ, (↑k : ℝ) * α = ↑m * (2 * Real.pi)) :
    exp (-(↑k : ℂ) * (↑α * I)) = 1 :=
  exp_factor_eq_one_of_angle_condition k α h_angle

/-! ### Odd-power PV vanishes by symmetry

The key technique: rewrite `∫_{-1}^{-ε} f(t) dt` as `∫_{ε}^{1} f(-t) dt`
using `integral_comp_neg`, then use the odd-symmetry `f(-t) = -f(t)` to cancel. -/

/-- Helper: the odd-symmetry cancellation pattern. Given `f(-t) = -f(t)`,
the function `ε ↦ ∫_{-1}^{-ε} f + ∫_{ε}^{1} f` is identically zero. -/
private theorem pv_odd_cancel_aux {f : ℝ → ℂ} (hodd : ∀ t, f (-t) = -f t) :
    (fun ε => (∫ t in (-1 : ℝ)..(-ε), f t) + ∫ t in ε..(1 : ℝ), f t) =
    (fun _ => (0 : ℂ)) := by
  have key : ∀ ε, ∫ t in (-1 : ℝ)..(-ε), f t = -(∫ t in ε..(1 : ℝ), f t) := by
    intro ε
    calc ∫ t in (-1 : ℝ)..(-ε), f t
        = ∫ t in ε..1, f (-t) := (intervalIntegral.integral_comp_neg f).symm
      _ = ∫ t in ε..1, -f t := by congr 1; ext t; exact hodd t
      _ = -(∫ t in ε..1, f t) := intervalIntegral.integral_neg
  funext ε
  have h := key ε
  exact (congr_arg (· + ∫ t in ε..1, f t) h).trans (neg_add_cancel _)

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

/-- For odd `k ≥ 3`, the CPV of `z⁻ᵏ dz` along the line curve is zero (variant). -/
theorem cpv_lineCurve_inv_pow_odd (r : ℝ) (hr : 0 < r) (α : ℝ) (k : ℕ)
    (hk : 2 ≤ k) (hk_odd : Odd k) :
    Tendsto (fun ε =>
      (∫ t in (-1 : ℝ)..(-ε),
        (lineCurve r α t)⁻¹ ^ k * deriv (lineCurve r α) t) +
      ∫ t in ε..(1 : ℝ),
        (lineCurve r α t)⁻¹ ^ k * deriv (lineCurve r α) t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hk3 : 3 ≤ k := by obtain ⟨m, hm⟩ := hk_odd; omega
  exact higherOrder_terms_odd_vanish r hr α k hk3 hk_odd

/-! ### Integrability of line-curve integrand -/

/-- The integrand is interval-integrable on `[ε, 1]` for `ε > 0`. -/
theorem lineCurve_integrand_intervalIntegrable (r : ℝ) (hr : 0 < r) (α : ℝ) (k : ℕ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IntervalIntegrable (fun t => (lineCurve r α t)⁻¹ ^ k * deriv (lineCurve r α) t)
      volume ε 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hε1]
  apply ContinuousOn.mul
  · apply ContinuousOn.pow
    intro t ht
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.inv₀ ((lineCurve_continuous r α).continuousAt)
        (lineCurve_ne_zero r hr α t (ne_of_gt (lt_of_lt_of_le hε ht.1))))
  · rw [lineCurve_deriv_const]; exact continuousOn_const

/-- The integrand is interval-integrable on `[-1, -ε]` for `ε > 0`. -/
theorem lineCurve_integrand_intervalIntegrable_neg (r : ℝ) (hr : 0 < r) (α : ℝ) (k : ℕ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IntervalIntegrable (fun t => (lineCurve r α t)⁻¹ ^ k * deriv (lineCurve r α) t)
      volume (-1) (-ε) := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by linarith)]
  apply ContinuousOn.mul
  · apply ContinuousOn.pow
    intro t ht
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.inv₀ ((lineCurve_continuous r α).continuousAt)
        (lineCurve_ne_zero r hr α t (by linarith [ht.2])))
  · rw [lineCurve_deriv_const]; exact continuousOn_const

end SectorCurve
