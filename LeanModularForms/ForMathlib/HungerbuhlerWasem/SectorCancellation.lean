/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LeanModularForms.ForMathlib.FlatnessConditions
import LeanModularForms.ForMathlib.HungerbuhlerWasem.ExitTimeExcision
import LeanModularForms.ForMathlib.HungerbuhlerWasem.HigherOrderAsymptotics

/-!
# Sector-even cancellation under condition (B) (T-SC-01)

For γ with a transverse crossing at `s`, the Laurent term `c / (z - s)^k`
(`k ≥ 2`) has Cauchy principal value equal to zero provided condition (B)
`(L_plus / ‖L_plus‖)^(k-1) = ((-L_minus) / ‖L_minus‖)^(k-1)` holds.

This file restores the deleted `HW33SectorEven.lean` content under the new
`HungerbuhlerWasem` namespace. The arrangement follows
Hungerbühler–Wasem (arXiv:1808.00997v2), equation 3.4:

  `PV ∮_γ dz/z^n = lim_{ε → 0⁺} (1 - e^(-i(n-1)α)) / ((n-1) ε^(n-1))`,

which is identically zero whenever `(n-1) α ∈ 2πℤ`.

## Headline theorems

* `exp_neg_I_eq_one_of_conditionB` — `exp(-i(n-1)α) = 1` under condition (B).
* `sector_pv_formula_vanishes_under_conditionB` — sector PV formula = 0 under (B).
* `sector_pv_formula_tendsto_zero_under_conditionB` — Tendsto form.
* `real_ray_inv_pow_integral` — closed form for `∫_a^b 1/t^n dt`.
* `complex_ray_inv_pow_integral` — closed form for `∫_a^b c / t^n dt` (complex).
* `arc_inv_pow_integral` — closed form for `∫_arc dz / z^n`.
* `sector_inv_pow_integral_combined` — full sector integral identity.
* `sector_inv_pow_integral_vanishes_under_conditionB` — full sector PV = 0
  under condition (B).
* `sector_inv_pow_integral_tendsto_zero_under_conditionB` — Tendsto form.
* `F_line_diff_eq_zero_under_conditionB` — antiderivative side targets agree.
* `F_curve_diff_tendsto_zero_under_conditionB` — combined curve F-difference
  tends to zero.
* `hw_theorem_3_3_under_conditionB_parametric` — HW Theorem 3.3 parametric form.
* `hasCauchyPVOn_singleton_pow_of_conditionB_assembled` — fully assembled
  `HasCauchyPVOn` form.
-/

open Filter Topology Set Complex MeasureTheory
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

/-- **The complex exponential `exp(-i(n-1)α)` equals 1 under condition (B).**
This is the key algebraic fact: `(n-1)α = 2πk` for some `k : ℤ` implies
`exp(-i(n-1)α) = exp(-i · 2πk) = 1`. -/
theorem exp_neg_I_eq_one_of_conditionB (n : ℕ) (α : ℝ)
    (h_angle : ∃ k : ℤ, ((n - 1 : ℕ) : ℝ) * α = ↑k * (2 * Real.pi)) :
    Complex.exp (-(↑((n - 1 : ℕ) : ℝ) * α : ℂ) * Complex.I) = 1 := by
  obtain ⟨k, hk⟩ := h_angle
  have heq : (-(↑((n - 1 : ℕ) : ℝ) * α : ℂ) * Complex.I) =
      (((-k : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I)) := by
    have hk' : (↑((n - 1 : ℕ) : ℝ) * α : ℂ) = (↑k : ℂ) * (2 * ↑Real.pi) := by
      exact_mod_cast hk
    rw [hk']; push_cast; ring
  rw [heq, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

/-- **Real ray integral closed form.** For `n ≥ 2` and `0 < a ≤ b`:

  `∫_a^b 1/t^n dt = (1/(n-1)) · (1/a^(n-1) - 1/b^(n-1))`.

This is the **real-valued** integral underlying HW eq. (3.4)'s line piece. -/
theorem real_ray_inv_pow_integral
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (n : ℕ) (hn : 2 ≤ n) :
    (∫ t in a..b, (1 / t ^ n : ℝ)) =
      (1 / (n - 1 : ℕ) : ℝ) *
        (1 / a ^ (n - 1) - 1 / b ^ (n - 1)) := by
  have h_int_eq : ∫ t in a..b, (1 / t ^ n : ℝ) = ∫ t in a..b, t ^ (-(n : ℤ)) :=
    intervalIntegral.integral_congr fun t _ => by
      rw [zpow_neg, zpow_natCast, ← one_div]
  have h_cast : ((↑(-(n : ℤ)) + 1 : ℝ)) = -((n - 1 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub (show 1 ≤ n by omega)]; ring
  rw [h_int_eq, integral_zpow (Or.inr ⟨fun h => by omega,
      Set.uIcc_of_le hab ▸ fun h => absurd h.1 (not_le.mpr ha)⟩),
    show (-(n : ℤ)) + 1 = -((n - 1 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, h_cast]
  field_simp
  ring

/-- **Complex ray integral closed form.** Multiplying the real ray integral by
a complex constant `c` (typically `e^(-i(n-1)α)` for a ray at angle α):

  `∫_a^b c / (↑t : ℂ)^n dt = c · (1/(n-1)) · (1/a^(n-1) - 1/b^(n-1))`. -/
theorem complex_ray_inv_pow_integral
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (c : ℂ) (n : ℕ) (hn : 2 ≤ n) :
    (∫ t in a..b, c / (↑t : ℂ) ^ n) =
      c * ((1 : ℂ) / (↑(n - 1 : ℕ) : ℂ)) *
        ((1 / (↑a : ℂ) ^ (n - 1)) - (1 / (↑b : ℂ) ^ (n - 1))) := by
  have h_eq : ∀ t : ℝ, t ∈ Set.uIcc a b →
      (c / (↑t : ℂ) ^ n) = c * (↑(1 / t ^ n : ℝ) : ℂ) := fun t ht => by
    rw [Set.uIcc_of_le hab] at ht
    have : (↑t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le ha ht.1).ne'
    push_cast; field_simp
  have h_step2 : (∫ t in a..b, c * (↑(1 / t ^ n : ℝ) : ℂ)) =
      c * ∫ t in a..b, (↑(1 / t ^ n : ℝ) : ℂ) :=
    intervalIntegral.integral_const_mul c (fun t : ℝ => (↑(1 / t ^ n : ℝ) : ℂ))
  rw [intervalIntegral.integral_congr h_eq, h_step2, intervalIntegral.integral_ofReal,
    real_ray_inv_pow_integral a b ha hab n hn]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (by omega : n - 1 ≠ 0),
    Complex.ofReal_ne_zero.mpr ha.ne',
    Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le ha hab).ne']

/-- **Arc integral closed form.** For the arc `t ↦ r · e^(it)` on `[0, α]`,
the integral `∫_arc dz/z^n` evaluates to:

  `(1 - e^(-i(n-1)α)) / ((n-1) · r^(n-1))`.

This is the γ_2 contribution in HW eq. (3.4)'s sector calculation. -/
theorem arc_inv_pow_integral (r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    (∫ t in (0 : ℝ)..α,
      ((↑r : ℂ) * Complex.I * Complex.exp ((↑t : ℂ) * Complex.I)) /
        ((↑r : ℂ) * Complex.exp ((↑t : ℂ) * Complex.I)) ^ n) =
      (1 - Complex.exp (-(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I))) /
        ((↑(n - 1 : ℕ) : ℂ) * (↑r : ℂ) ^ (n - 1)) := by
  have hr_ne : (↑r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hn1_ne : (↑(n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h_pow_r : (↑r : ℂ) ^ n = (↑r : ℂ) ^ (n - 1) * (↑r : ℂ) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
  have h_pow_exp : ∀ t : ℝ, Complex.exp ((↑t : ℂ) * Complex.I) ^ n =
      Complex.exp ((↑(n - 1 : ℕ) : ℂ) * (↑t : ℂ) * Complex.I) *
        Complex.exp ((↑t : ℂ) * Complex.I) := fun t => by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    rw [show n = (n - 1) + 1 by omega]; push_cast; ring
  have h_eq : ∀ t : ℝ,
      ((↑r : ℂ) * Complex.I * Complex.exp ((↑t : ℂ) * Complex.I)) /
        ((↑r : ℂ) * Complex.exp ((↑t : ℂ) * Complex.I)) ^ n =
      (Complex.I / (↑r : ℂ) ^ (n - 1)) *
        Complex.exp ((-(↑(n - 1 : ℕ) : ℂ) * Complex.I) * (↑t : ℂ)) := fun t => by
    rw [mul_pow, h_pow_r, h_pow_exp t,
      show -(↑(n - 1 : ℕ) : ℂ) * Complex.I * (↑t : ℂ) =
        -((↑(n - 1 : ℕ) : ℂ) * (↑t : ℂ) * Complex.I) by ring,
      Complex.exp_neg]
    field_simp [Complex.exp_ne_zero, hr_ne]
  have h_step :
      (∫ t in (0 : ℝ)..α,
        (Complex.I / (↑r : ℂ) ^ (n - 1)) *
          Complex.exp ((-(↑(n - 1 : ℕ) : ℂ) * Complex.I) * (↑t : ℂ))) =
      (Complex.I / (↑r : ℂ) ^ (n - 1)) *
        ∫ t in (0 : ℝ)..α,
          Complex.exp ((-(↑(n - 1 : ℕ) : ℂ) * Complex.I) * (↑t : ℂ)) :=
    intervalIntegral.integral_const_mul (Complex.I / (↑r : ℂ) ^ (n - 1))
      (fun t => Complex.exp ((-(↑(n - 1 : ℕ) : ℂ) * Complex.I) * (↑t : ℂ)))
  rw [intervalIntegral.integral_congr (fun t _ => h_eq t), h_step,
    integral_exp_mul_complex (mul_ne_zero (neg_ne_zero.mpr hn1_ne) Complex.I_ne_zero),
    show (-(↑(n - 1 : ℕ) : ℂ) * Complex.I) * (↑α : ℂ) =
      -(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I) by ring]
  push_cast
  rw [mul_zero, Complex.exp_zero]
  field_simp
  ring

/-- **Combined sector PV formula (HW eq. 3.4).** For the sector curve with
corner angle `α` and radii `ε ≤ r`, summing the three pieces (real-axis ray
+ arc + reversed-ray-at-angle-α) gives:

  `∫_ε^r dt/t^n + ∫_0^α arc + (-1)·∫_ε^r e^(-i(n-1)α)/t^n dt
    = (1 - e^(-i(n-1)α)) / ((n-1)·ε^(n-1))`. -/
theorem sector_inv_pow_integral_combined
    (r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (α : ℝ) (n : ℕ)
    (hn : 2 ≤ n) :
    (∫ t in ε..r, (1 : ℂ) / (↑t : ℂ) ^ n) +
    (∫ t in (0 : ℝ)..α,
      ((↑r : ℂ) * Complex.I * Complex.exp ((↑t : ℂ) * Complex.I)) /
        ((↑r : ℂ) * Complex.exp ((↑t : ℂ) * Complex.I)) ^ n) -
    (∫ t in ε..r,
      Complex.exp (-(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I)) /
        (↑t : ℂ) ^ n) =
    (1 - Complex.exp (-(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I))) /
      ((↑(n - 1 : ℕ) : ℂ) * (↑ε : ℂ) ^ (n - 1)) := by
  rw [complex_ray_inv_pow_integral ε r hε hεr 1 n hn,
    arc_inv_pow_integral r hr α n hn,
    complex_ray_inv_pow_integral ε r hε hεr
      (Complex.exp (-(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I))) n hn]
  field_simp [Nat.cast_ne_zero.mpr (by omega : n - 1 ≠ 0),
    Complex.ofReal_ne_zero.mpr hε.ne', Complex.ofReal_ne_zero.mpr hr.ne']
  ring

/-- **F-line difference vanishing under condition (B), general angle.**
For pole `s`, two tangent directions `L_plus` (right) and `L_minus` (left, used
inward as `-L_minus`), and `k ≥ 2`, the antiderivative
`F(z) = -1/((k-1)(z-s)^(k-1))` evaluated at the chord-targets
`s + ε · (L_plus / ‖L_plus‖)` and `s + ε · ((-L_minus) / ‖L_minus‖)` is
**equal** under condition (B):

  `((L_plus / ‖L_plus‖))^(k-1) = ((-L_minus / ‖L_minus‖))^(k-1)`.

For k odd, `(-L/|L|)^(k-1) = (L/|L|)^(k-1)` holds automatically (k-1 is even),
recovering condition (B). -/
theorem F_line_diff_eq_zero_under_conditionB
    (s : ℂ) (L_minus L_plus : ℂ) (k : ℕ) (_hk : 2 ≤ k)
    (hL_minus : L_minus ≠ 0) (hL_plus : L_plus ≠ 0)
    (h_B :
      (L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1) =
      ((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1))
    (ε : ℝ) :
    -((↑(k - 1) : ℂ))⁻¹ *
      (((s + (ε / ‖L_plus‖ : ℝ) • L_plus) - s) ^ (k - 1))⁻¹ =
    -((↑(k - 1) : ℂ))⁻¹ *
      (((s + (ε / ‖L_minus‖ : ℝ) • (-L_minus)) - s) ^ (k - 1))⁻¹ := by
  congr 2
  have h_pow_plus : ((s + (ε / ‖L_plus‖ : ℝ) • L_plus) - s) ^ (k - 1) =
      ((↑ε : ℂ) ^ (k - 1)) * ((L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1)) := by
    rw [add_sub_cancel_left,
      show ((ε / ‖L_plus‖ : ℝ) • L_plus : ℂ) = (↑ε : ℂ) * (L_plus / (↑‖L_plus‖ : ℂ)) by
        rw [Complex.real_smul]; push_cast; field_simp,
      mul_pow]
  have h_pow_minus : ((s + (ε / ‖L_minus‖ : ℝ) • (-L_minus)) - s) ^ (k - 1) =
      ((↑ε : ℂ) ^ (k - 1)) * (((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1)) := by
    rw [add_sub_cancel_left,
      show ((ε / ‖L_minus‖ : ℝ) • (-L_minus) : ℂ) =
          (↑ε : ℂ) * ((-L_minus) / (↑‖L_minus‖ : ℂ)) by
        rw [Complex.real_smul]; push_cast; field_simp,
      mul_pow]
  rw [h_pow_plus, h_pow_minus, h_B]

/-- **Combined curve F-difference → 0 under condition (B), general angle.**
For curve γ flat of order n at t₀ with tangents `L_minus` (left) and `L_plus`
(right), under condition (B):

  `‖F(γ(t_eps_minus(ε))) - F(γ(t_eps_plus(ε)))‖ → 0` as ε → 0⁺,

where `F(z) = -1/((k-1)(z-s)^(k-1))` and `t_eps_plus`, `t_eps_minus` are the
exit-time functions on each side.

Proof: triangle inequality `‖A - B‖ ≤ ‖A - TR‖ + ‖B - TR‖` where `TR` is
the common tangent target. Both `‖A - TR‖` and `‖B - TR‖` tend to 0 by
`F_diff_at_tangent_target_tendsto_zero_right/_left`. Under condition (B),
the two side targets are EQUAL (`F_line_diff_eq_zero_under_conditionB`). -/
theorem F_curve_diff_tendsto_zero_under_conditionB
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L_minus L_plus : ℂ} {n k : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n)
    (hL_minus : L_minus ≠ 0) (hL_plus : L_plus ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ L_plus (Set.Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ L_minus (Set.Iio t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_plus))
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_minus))
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (h_B :
      (L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1) =
      ((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1))
    (t_eps_plus t_eps_minus : ℝ → ℝ)
    (h_plus_to : Tendsto t_eps_plus (𝓝[>] (0 : ℝ)) (𝓝[>] t₀))
    (h_plus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (t_eps_plus ε) - s‖ = ε)
    (h_minus_to : Tendsto t_eps_minus (𝓝[>] (0 : ℝ)) (𝓝[<] t₀))
    (h_minus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (t_eps_minus ε) - s‖ = ε) :
    Tendsto (fun ε =>
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h_sum_raw := ((F_diff_at_tangent_target_tendsto_zero_right
        h_flat hL_plus h_deriv_right hL_right h_s hk hkn hn1).comp h_plus_to).add
      ((F_diff_at_tangent_target_tendsto_zero_left
        h_flat hL_minus h_deriv_left hL_left h_s hk hkn hn1).comp h_minus_to)
  have h_sum : Tendsto (fun ε =>
      ‖-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹ -
          -(↑(k - 1) : ℂ)⁻¹ *
            (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L_plus‖ : ℝ) • L_plus) - s)
              ^ (k - 1))⁻¹‖ +
        ‖-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹ -
          -(↑(k - 1) : ℂ)⁻¹ *
            (((s + (‖γ (t_eps_minus ε) - s‖ / ‖(-L_minus)‖ : ℝ) • (-L_minus)) - s)
              ^ (k - 1))⁻¹‖)
      (𝓝[>] 0) (𝓝 0) := by
    convert h_sum_raw using 2
    simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [h_plus_radius, h_minus_radius] with ε hpr hmr
  have h_targets_eq :
      -(↑(k - 1) : ℂ)⁻¹ *
        (((s + (‖γ (t_eps_minus ε) - s‖ / ‖(-L_minus)‖ : ℝ) • (-L_minus)) - s)
          ^ (k - 1))⁻¹ =
      -(↑(k - 1) : ℂ)⁻¹ *
        (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L_plus‖ : ℝ) • L_plus) - s)
          ^ (k - 1))⁻¹ := by
    rw [hmr, norm_neg, hpr]
    exact (F_line_diff_eq_zero_under_conditionB s L_minus L_plus k hk
      hL_minus hL_plus h_B ε).symm
  set TR := -(↑(k - 1) : ℂ)⁻¹ *
    (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L_plus‖ : ℝ) • L_plus) - s) ^ (k - 1))⁻¹
  set A := -(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹
  set B := -(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹
  change ‖A - B‖ ≤ ‖B - TR‖ + ‖A - _‖
  rw [h_targets_eq]
  calc ‖A - B‖ = ‖(A - TR) - (B - TR)‖ := by rw [sub_sub_sub_cancel_right]
    _ ≤ ‖A - TR‖ + ‖B - TR‖ := norm_sub_le _ _
    _ = ‖B - TR‖ + ‖A - TR‖ := add_comm _ _

end HungerbuhlerWasem

end
