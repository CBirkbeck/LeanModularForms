/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.SectorCurve
import LeanModularForms.ForMathlib.HigherOrderCancel
import LeanModularForms.ForMathlib.HW33Final
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# k-even sector PV under condition (B) — explicit formula

For the **sector curve** with corner angle α, traversed as the boundary of the
ε-radius sector at the origin, the Hungerbühler-Wasem paper (arXiv:1808.00997v2,
equation 3.4) gives the explicit formula:

  `PV ∮_γ dz/z^n = lim_{ε → 0⁺} (1 - e^(-i(n-1)α)) / ((n-1) ε^(n-1))`

Under **condition (B)** `(n-1)α ∈ 2πℤ`, we have `e^(-i(n-1)α) = 1`, so the
numerator is identically zero and the limit is zero. Otherwise the formula
diverges (complex infinity).

This file formalizes the explicit-formula vanishing under condition (B), which
is the key building block for the k-even case of HW Theorem 3.3 missing from
the previous infrastructure (the symmetric-line model `lineCurve` does not
admit a k-even PV — the sector model is needed).

## Main result

* `sector_pv_formula_vanishes_under_conditionB`: the explicit formula
  `(1 - e^(-i(n-1)α)) / ((n-1) ε^(n-1))` is identically zero for all `ε > 0`
  under condition (B).

This characterizes the limit cleanly: combined with the explicit closed-form
sector-curve integral, one obtains `PV ∮_γ dz/z^n = 0` for the sector curve
under condition (B).
-/

open Filter Topology Set Complex Real MeasureTheory

noncomputable section

namespace LeanModularForms

/-- **The complex exponential `exp(-i(n-1)α)` equals 1 under condition (B).**
This is the key algebraic fact: `(n-1)α = 2πk` for some `k : ℤ` implies
`exp(-i(n-1)α) = exp(-i · 2πk) = 1`. -/
theorem exp_neg_I_eq_one_of_conditionB (n : ℕ) (α : ℝ)
    (h_angle : ∃ k : ℤ, ((n - 1 : ℕ) : ℝ) * α = ↑k * (2 * Real.pi)) :
    Complex.exp (-(↑((n - 1 : ℕ) : ℝ) * α : ℂ) * Complex.I) = 1 := by
  obtain ⟨k, hk⟩ := h_angle
  have hk' : (↑((n - 1 : ℕ) : ℝ) * α : ℂ) = (↑k : ℂ) * (2 * ↑Real.pi) := by exact_mod_cast hk
  rw [show (-(↑((n - 1 : ℕ) : ℝ) * α : ℂ) * Complex.I) =
    (((-k : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I)) from by rw [hk']; push_cast; ring,
    Complex.exp_int_mul, Complex.exp_two_pi_mul_I]
  exact one_zpow _

/-- **The HW Theorem 3.3 (eq. 3.4) sector-PV formula vanishes under condition (B).**

The paper gives `PV ∮_γ dz/z^n = (1 - e^(-i(n-1)α)) / ((n-1) ε^(n-1))` for the
sector curve with corner angle `α`. Under condition (B) `(n-1)α ∈ 2πℤ`,
`e^(-i(n-1)α) = 1`, so the numerator is identically zero and the formula
evaluates to zero for every `ε > 0`. Hence the Tendsto limit is zero. -/
theorem sector_pv_formula_vanishes_under_conditionB
    (n : ℕ) (_hn : 2 ≤ n) (α : ℝ)
    (h_angle : ∃ k : ℤ, ((n - 1 : ℕ) : ℝ) * α = ↑k * (2 * Real.pi)) :
    ∀ ε > (0 : ℝ),
      (1 - Complex.exp (-(↑((n - 1 : ℕ) : ℝ) * α : ℂ) * Complex.I)) /
        ((↑(n - 1) : ℂ) * (↑ε : ℂ) ^ (n - 1)) = 0 := by
  intro ε _
  rw [exp_neg_I_eq_one_of_conditionB n α h_angle, sub_self, zero_div]

/-- **Tendsto form**: the explicit formula tends to 0 as ε → 0⁺ under condition (B).
Combined with the explicit closed-form sector integral (3 pieces: two rays plus
an arc), this gives the **k-even sector PV vanishing** of HW Theorem 3.3
under condition (B). -/
theorem sector_pv_formula_tendsto_zero_under_conditionB
    (n : ℕ) (_hn : 2 ≤ n) (α : ℝ)
    (h_angle : ∃ k : ℤ, ((n - 1 : ℕ) : ℝ) * α = ↑k * (2 * Real.pi)) :
    Tendsto (fun ε : ℝ =>
      (1 - Complex.exp (-(↑((n - 1 : ℕ) : ℝ) * α : ℂ) * Complex.I)) /
        ((↑(n - 1) : ℂ) * (↑ε : ℂ) ^ (n - 1)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine Tendsto.congr' (f₁ := fun _ : ℝ => (0 : ℂ)) ?_ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (sector_pv_formula_vanishes_under_conditionB n _hn α h_angle ε hε).symm

/-! ## Line integral along a ray at angle α (real factor) -/

/-- **Real ray integral closed form.** For `n ≥ 2` and `0 < a ≤ b`:

  `∫_a^b 1/t^n dt = (1/(n-1)) · (1/a^(n-1) - 1/b^(n-1))`.

This is the **real-valued** integral underlying HW eq. (3.4)'s line piece.
Converting to the complex form `∫_a^b c/(↑t : ℂ)^n dt = c · (above)` is the
remaining bookkeeping step. -/
theorem real_ray_inv_pow_integral
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (n : ℕ) (hn : 2 ≤ n) :
    (∫ t in a..b, (1 / t ^ n : ℝ)) =
      (1 / (n - 1 : ℕ) : ℝ) *
        (1 / a ^ (n - 1) - 1 / b ^ (n - 1)) := by
  have h_int_eq : ∫ t in a..b, (1 / t ^ n : ℝ) = ∫ t in a..b, t ^ (-(n : ℤ)) :=
    intervalIntegral.integral_congr fun t _ => by
      rw [zpow_neg, zpow_natCast, ← one_div]
  rw [h_int_eq]
  have h_zero_not_in : (0 : ℝ) ∉ Set.uIcc a b :=
    Set.uIcc_of_le hab ▸ fun h => absurd h.1 (not_le.mpr ha)
  rw [integral_zpow (Or.inr ⟨by intro h; omega, h_zero_not_in⟩),
    show (-(n : ℤ)) + 1 = -((n - 1 : ℕ) : ℤ) from by omega,
    zpow_neg, zpow_neg, zpow_natCast, zpow_natCast,
    show ((↑(-(n : ℤ)) + 1 : ℝ)) = -((n - 1 : ℕ) : ℝ) from by
      push_cast [Nat.cast_sub (show 1 ≤ n by omega)]; ring]
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
  -- Rewrite c/t^n = c * (↑(1/t^n : ℝ) : ℂ) on (a, b) (where t > 0)
  have h_eq : ∀ t : ℝ, t ∈ Set.uIcc a b →
      (c / (↑t : ℂ) ^ n) = c * (↑(1 / t ^ n : ℝ) : ℂ) := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht_ne : (↑t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le ha ht.1).ne'
    push_cast
    field_simp
  rw [intervalIntegral.integral_congr h_eq]
  have h_step2 : (∫ t in a..b, c * (↑(1 / t ^ n : ℝ) : ℂ)) =
      c * ∫ t in a..b, (↑(1 / t ^ n : ℝ) : ℂ) :=
    intervalIntegral.integral_const_mul c (fun t : ℝ => (↑(1 / t ^ n : ℝ) : ℂ))
  rw [h_step2, intervalIntegral.integral_ofReal,
    real_ray_inv_pow_integral a b ha hab n hn]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (by omega : n - 1 ≠ 0),
    Complex.ofReal_ne_zero.mpr ha.ne',
    Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le ha hab).ne']

/-! ## Arc integral (γ_2 piece) -/

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
  -- Simplify the integrand to (i/r^(n-1)) · exp(c · t) where c = -i(n-1)
  have h_eq : ∀ t : ℝ,
      ((↑r : ℂ) * Complex.I * Complex.exp ((↑t : ℂ) * Complex.I)) /
        ((↑r : ℂ) * Complex.exp ((↑t : ℂ) * Complex.I)) ^ n =
      (Complex.I / (↑r : ℂ) ^ (n - 1)) *
        Complex.exp ((-(↑(n - 1 : ℕ) : ℂ) * Complex.I) * (↑t : ℂ)) := by
    intro t
    rw [mul_pow,
      show (↑r : ℂ) ^ n = (↑r : ℂ) ^ (n - 1) * (↑r : ℂ) by
        conv_lhs => rw [show n = (n - 1) + 1 from by omega]
        rw [pow_succ],
      show Complex.exp ((↑t : ℂ) * Complex.I) ^ n =
        Complex.exp ((↑(n - 1 : ℕ) : ℂ) * (↑t : ℂ) * Complex.I) *
          Complex.exp ((↑t : ℂ) * Complex.I) by
        rw [← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        rw [show n = (n - 1) + 1 from by omega]; push_cast; ring,
      show -(↑(n - 1 : ℕ) : ℂ) * Complex.I * (↑t : ℂ) =
        -((↑(n - 1 : ℕ) : ℂ) * (↑t : ℂ) * Complex.I) from by ring,
      Complex.exp_neg]
    field_simp [Complex.exp_ne_zero]
  rw [intervalIntegral.integral_congr (fun t _ => h_eq t)]
  -- Pull out (i/r^(n-1)) using integral_const_mul (with explicit f)
  have h_step :
      (∫ t in (0 : ℝ)..α,
        (Complex.I / (↑r : ℂ) ^ (n - 1)) *
          Complex.exp ((-(↑(n - 1 : ℕ) : ℂ) * Complex.I) * (↑t : ℂ))) =
      (Complex.I / (↑r : ℂ) ^ (n - 1)) *
        ∫ t in (0 : ℝ)..α,
          Complex.exp ((-(↑(n - 1 : ℕ) : ℂ) * Complex.I) * (↑t : ℂ)) :=
    intervalIntegral.integral_const_mul (Complex.I / (↑r : ℂ) ^ (n - 1))
      (fun t => Complex.exp ((-(↑(n - 1 : ℕ) : ℂ) * Complex.I) * (↑t : ℂ)))
  rw [h_step,
    integral_exp_mul_complex (mul_ne_zero (neg_ne_zero.mpr hn1_ne) Complex.I_ne_zero)]
  push_cast
  rw [show (-(↑(n - 1 : ℕ) : ℂ) * Complex.I) * (↑α : ℂ) =
    -(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I) from by ring,
    mul_zero, Complex.exp_zero]
  field_simp
  ring

/-! ## Combined sector formula -/

/-- **Combined sector PV formula (HW eq. 3.4).** For the sector curve with
corner angle `α` and radii `ε ≤ r`, summing the three pieces (real-axis ray
+ arc + reversed-ray-at-angle-α) gives:

  `∫_ε^r dt/t^n + ∫_0^α arc + (-1)·∫_ε^r e^(-i(n-1)α)/t^n dt
    = (1 - e^(-i(n-1)α)) / ((n-1)·ε^(n-1))`.

This is the explicit formula in equation 3.4 of HW (arXiv:1808.00997v2),
identically equal as functions of `ε > 0`. Under condition (B), the prefactor
`(1 - e^(-i(n-1)α)) = 0`, so the sector PV vanishes for every `ε > 0`. -/
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
  rw [complex_ray_inv_pow_integral ε r hε hεr 1 n hn]
  rw [arc_inv_pow_integral r hr α n hn]
  rw [complex_ray_inv_pow_integral ε r hε hεr
    (Complex.exp (-(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I))) n hn]
  -- Algebraic simplification: combine the three closed forms
  field_simp [Nat.cast_ne_zero.mpr (by omega : n - 1 ≠ 0),
    Complex.ofReal_ne_zero.mpr hε.ne', Complex.ofReal_ne_zero.mpr hr.ne']
  ring

/-- **Sector PV vanishing under condition (B).** Combining the explicit formula
`sector_inv_pow_integral_combined` with the algebraic vanishing
`exp_neg_I_eq_one_of_conditionB`, the sector PV is **identically zero** for
every `ε > 0` under condition (B).

This closes the **k-even case** of HW Theorem 3.3 for the model sector
curve under condition (B). The full closure for general curves follows
from the curve→sector comparison via flatness (analog of
`F_curve_diff_tendsto_zero_odd`, which is the remaining mechanical step). -/
theorem sector_inv_pow_integral_vanishes_under_conditionB
    (r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (α : ℝ) (n : ℕ)
    (hn : 2 ≤ n)
    (h_angle : ∃ k : ℤ, ((n - 1 : ℕ) : ℝ) * α = ↑k * (2 * Real.pi)) :
    (∫ t in ε..r, (1 : ℂ) / (↑t : ℂ) ^ n) +
    (∫ t in (0 : ℝ)..α,
      ((↑r : ℂ) * Complex.I * Complex.exp ((↑t : ℂ) * Complex.I)) /
        ((↑r : ℂ) * Complex.exp ((↑t : ℂ) * Complex.I)) ^ n) -
    (∫ t in ε..r,
      Complex.exp (-(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I)) /
        (↑t : ℂ) ^ n) = 0 := by
  rw [sector_inv_pow_integral_combined r hr ε hε hεr α n hn,
    show (-(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I) : ℂ) =
      (-(↑((n - 1 : ℕ) : ℝ) * α : ℂ)) * Complex.I from by push_cast; ring,
    exp_neg_I_eq_one_of_conditionB n α h_angle]
  simp

/-- **Sector PV Tendsto vanishing under condition (B).** The sector curve's
excised integral tends to 0 as `ε → 0⁺` (and in fact equals 0 for all
`0 < ε ≤ r`) under condition (B). This is the **end-state vanishing**
for the k-even case of HW Theorem 3.3 in the model-sector form. -/
theorem sector_inv_pow_integral_tendsto_zero_under_conditionB
    (r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (h_angle : ∃ k : ℤ, ((n - 1 : ℕ) : ℝ) * α = ↑k * (2 * Real.pi)) :
    Tendsto (fun ε : ℝ =>
      (∫ t in ε..r, (1 : ℂ) / (↑t : ℂ) ^ n) +
      (∫ t in (0 : ℝ)..α,
        ((↑r : ℂ) * Complex.I * Complex.exp ((↑t : ℂ) * Complex.I)) /
          ((↑r : ℂ) * Complex.exp ((↑t : ℂ) * Complex.I)) ^ n) -
      (∫ t in ε..r,
        Complex.exp (-(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I)) /
          (↑t : ℂ) ^ n))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine Tendsto.congr' (f₁ := fun _ : ℝ => (0 : ℂ)) ?_ tendsto_const_nhds
  filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
  exact (sector_inv_pow_integral_vanishes_under_conditionB r hr ε hε.1
    hε.2.le α n hn h_angle).symm

/-! ## F-line difference under condition (B) — generalizes the k-odd case -/

/-- **F-line difference vanishing under condition (B), general angle.**
For pole `s`, two tangent directions `L_plus` (right tangent, pointing AWAY
from `t₀` on `t > t₀` side) and `L_minus` (left tangent, also pointing away
from `t₀` on `t < t₀` side, so we use `-L_minus` for the inward direction),
and `k ≥ 2`, the antiderivative `F(z) = -1/((k-1)(z-s)^(k-1))` evaluated at
the chord-targets `s + ε · (L_plus / ‖L_plus‖)` and `s + ε · ((-L_minus) / ‖L_minus‖)`
is **equal** under condition (B):

  `((L_plus / ‖L_plus‖))^(k-1) = ((-L_minus / ‖L_minus‖))^(k-1)`.

This generalizes `F_line_diff_eq_zero_of_odd` (which assumes `L_plus = L_minus`,
i.e., the transverse case): for k odd, `(-L/|L|)^(k-1) = (L/|L|)^(k-1)` holds
automatically (k-1 is even), recovering condition (B). -/
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
  -- Reduce to ((s + ε • L_plus / ‖L_plus‖) - s)^(k-1) = ((s + ε • (-L_minus / ‖L_minus‖)) - s)^(k-1)
  -- which simplifies to (ε • L_plus / ‖L_plus‖)^(k-1) = (ε • (-L_minus / ‖L_minus‖))^(k-1)
  -- which factors out ε^(k-1), giving (L_plus/‖L_plus‖)^(k-1) = (-L_minus/‖L_minus‖)^(k-1) (B).
  have h_lhs : ((s + (ε / ‖L_plus‖ : ℝ) • L_plus) - s) ^ (k - 1) =
      ((↑ε : ℂ) ^ (k - 1)) * ((L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1)) := by
    rw [add_sub_cancel_left,
      show ((ε / ‖L_plus‖ : ℝ) • L_plus : ℂ) = (↑ε : ℂ) * (L_plus / (↑‖L_plus‖ : ℂ))
        from by rw [Complex.real_smul]; push_cast; field_simp, mul_pow]
  have h_rhs : ((s + (ε / ‖L_minus‖ : ℝ) • (-L_minus)) - s) ^ (k - 1) =
      ((↑ε : ℂ) ^ (k - 1)) * (((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1)) := by
    rw [add_sub_cancel_left,
      show ((ε / ‖L_minus‖ : ℝ) • (-L_minus) : ℂ) =
          (↑ε : ℂ) * ((-L_minus) / (↑‖L_minus‖ : ℂ))
        from by rw [Complex.real_smul]; push_cast; field_simp, mul_pow]
  rw [h_lhs, h_rhs, h_B]

/-! ## Curve F-difference under condition (B), general angle -/

/-- **Combined curve F-difference → 0 under condition (B), general angle.**
The general-angle analog of `F_curve_diff_tendsto_zero_odd` from
`HigherOrderCancel.lean`, replacing the odd-power-symmetry with condition (B).

For curve γ flat of order n at t₀ with tangents `L_minus` (left) and `L_plus`
(right), under condition (B) `(L_plus/‖L_plus‖)^(k-1) = ((-L_minus)/‖L_minus‖)^(k-1)`:

  `‖F(γ(t_eps_minus(ε))) - F(γ(t_eps_plus(ε)))‖ → 0` as ε → 0⁺

where `F(z) = -1/((k-1)(z-s)^(k-1))` and `t_eps_plus`, `t_eps_minus` are the
exit-time functions on each side.

Proof: triangle inequality `‖A - B‖ ≤ ‖A - TR‖ + ‖B - TR‖` where `TR` is
the common tangent target. Both `‖A - TR‖` (left F-diff) and `‖B - TR‖`
(right F-diff) tend to 0 by `F_diff_at_tangent_target_tendsto_zero_right/_left`.
Under condition (B), the two side targets are EQUAL (by
`F_line_diff_eq_zero_under_conditionB`), so we can use a common `TR`. -/
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
  -- Right- and left-side F-diff at chord target → 0; sum still → 0
  have h_sum_raw := ((F_diff_at_tangent_target_tendsto_zero_right
        h_flat hL_plus h_deriv_right hL_right h_s hk hkn hn1).comp h_plus_to).add
      ((F_diff_at_tangent_target_tendsto_zero_left
        h_flat hL_minus h_deriv_left hL_left h_s hk hkn hn1).comp h_minus_to)
  -- The summed F-diffs tend to 0
  have h_sum : Tendsto (fun ε =>
      ‖-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹ -
          -(↑(k - 1) : ℂ)⁻¹ *
            (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L_plus‖ : ℝ) • L_plus) - s) ^ (k - 1))⁻¹‖ +
        ‖-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹ -
          -(↑(k - 1) : ℂ)⁻¹ *
            (((s + (‖γ (t_eps_minus ε) - s‖ / ‖(-L_minus)‖ : ℝ) • (-L_minus)) - s)
              ^ (k - 1))⁻¹‖)
      (𝓝[>] 0) (𝓝 0) := by
    convert h_sum_raw using 2; simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [h_plus_radius, h_minus_radius] with ε hpr hmr
  -- Use F_line_diff_eq_zero_under_conditionB to identify the two side targets
  have h_targets_eq :
      -(↑(k - 1) : ℂ)⁻¹ *
        (((s + (‖γ (t_eps_minus ε) - s‖ / ‖(-L_minus)‖ : ℝ) • (-L_minus)) - s)
          ^ (k - 1))⁻¹ =
      -(↑(k - 1) : ℂ)⁻¹ *
        (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L_plus‖ : ℝ) • L_plus) - s) ^ (k - 1))⁻¹ := by
    rw [hmr, norm_neg, hpr]
    exact (F_line_diff_eq_zero_under_conditionB s L_minus L_plus k hk
      hL_minus hL_plus h_B ε).symm
  set TR := -(↑(k - 1) : ℂ)⁻¹ *
    (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L_plus‖ : ℝ) • L_plus) - s) ^ (k - 1))⁻¹
  set A := -(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹
  set B := -(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹
  have h_triangle : ‖A - B‖ ≤ ‖B - TR‖ + ‖A - TR‖ :=
    calc ‖A - B‖ = ‖(A - TR) - (B - TR)‖ := by ring_nf
      _ ≤ ‖A - TR‖ + ‖B - TR‖ := norm_sub_le _ _
      _ = ‖B - TR‖ + ‖A - TR‖ := add_comm _ _
  show ‖A - B‖ ≤ ‖B - TR‖ + ‖A - _‖
  rw [h_targets_eq]
  exact h_triangle

/-! ## HW Theorem 3.3 — general angle under condition (B), parametric form -/

/-- **HW Theorem 3.3 — general angle parametric form.** The general-angle
analog of `hw_theorem_3_3_odd_transverse_parametric` (in `HigherOrderCancel.lean`).

For closed γ with single crossing at t₀ where γ has TWO different tangent
directions `L_minus` (entering) and `L_plus` (leaving), and condition (B) holds:
the symmetric-excision PV vanishes as ε → 0⁺. -/
theorem hw_theorem_3_3_under_conditionB_parametric
    {γ : ℝ → ℂ} {γ' : ℝ → ℂ} {a b t₀ : ℝ} {s L_minus L_plus : ℂ} {n k : ℕ}
    (h_close : γ a = γ b)
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
    (h_minus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (t_eps_minus ε) - s‖ = ε)
    (h_minus_smooth : ∀ ε > 0, ∀ t ∈ Set.uIcc a (t_eps_minus ε),
      HasDerivAt γ (γ' t) t)
    (h_minus_avoids : ∀ ε > 0, ∀ t ∈ Set.uIcc a (t_eps_minus ε), γ t ≠ s)
    (h_minus_int : ∀ ε > 0,
      IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k)
        MeasureTheory.volume a (t_eps_minus ε))
    (h_plus_smooth : ∀ ε > 0, ∀ t ∈ Set.uIcc (t_eps_plus ε) b,
      HasDerivAt γ (γ' t) t)
    (h_plus_avoids : ∀ ε > 0, ∀ t ∈ Set.uIcc (t_eps_plus ε) b, γ t ≠ s)
    (h_plus_int : ∀ ε > 0,
      IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k)
        MeasureTheory.volume (t_eps_plus ε) b) :
    Tendsto (fun ε =>
      (∫ t in a..(t_eps_minus ε), γ' t / (γ t - s) ^ k) +
        (∫ t in (t_eps_plus ε)..b, γ' t / (γ t - s) ^ k))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact cpv_excised_tendsto_zero_of_F_diff_zero h_close hk
    t_eps_plus t_eps_minus
    h_minus_smooth h_minus_avoids h_minus_int
    h_plus_smooth h_plus_avoids h_plus_int
    (F_curve_diff_tendsto_zero_under_conditionB h_flat hL_minus hL_plus
      h_deriv_right h_deriv_left hL_right hL_left h_s hk hkn hn1 h_B
      t_eps_plus t_eps_minus h_plus_to h_plus_radius h_minus_to h_minus_radius)

/-! ## HW Theorem 3.3 — final HasCauchyPVOn closure under condition (B) -/

/-- **HW Theorem 3.3 — fully assembled k-even/general angle case under (B).**
The general-angle analog of `hasCauchyPVOn_singleton_pow_of_transverse_assembled`
(in `HW33Final.lean`).

For closed `γ : PiecewiseC1Path x x` with single corner crossing at `t₀ ∈ (0, 1)`
of pole `s` with TWO tangent directions `L_minus` (left) and `L_plus` (right),
condition (B) holds, γ flat of order n ≥ k, plus strict (anti-)monotonicity
of `‖γ - s‖` on each side and avoidance margins on the outer regions:

  `HasCauchyPVOn {s} (fun z => 1/(z-s)^k) γ 0`.

This is the **fully assembled HW 3.3 closure for the general (B) case** in the
`HasCauchyPVOn` form. The k-odd transverse case is the special case `L_plus = L_minus`. -/
theorem hasCauchyPVOn_singleton_pow_of_conditionB_assembled
    {x : ℂ} {γ : PiecewiseC1Path x x} {s L_minus L_plus : ℂ}
    {t₀ δMinus δPlus : ℝ} {n k : ℕ}
    (h_t₀_minus_pos : 0 ≤ t₀ - δMinus) (h_t₀_plus_le : t₀ + δPlus ≤ 1)
    (hδMinus : 0 < δMinus) (hδPlus : 0 < δPlus)
    -- Closure
    (h_close : γ.toPath.extend 0 = γ.toPath.extend 1)
    -- Flatness and tangent data
    (h_flat : IsFlatOfOrder γ.toPath.extend t₀ n)
    (hL_minus : L_minus ≠ 0) (hL_plus : L_plus ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ.toPath.extend L_plus (Set.Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ.toPath.extend L_minus (Set.Iio t₀) t₀)
    (hL_right : Tendsto (deriv γ.toPath.extend) (𝓝[>] t₀) (𝓝 L_plus))
    (hL_left : Tendsto (deriv γ.toPath.extend) (𝓝[<] t₀) (𝓝 L_minus))
    (h_s : γ.toPath.extend t₀ = s)
    (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    -- Condition (B)
    (h_B :
      (L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1) =
      ((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1))
    -- Continuity / smoothness on each side
    (hγ_cont_right : ContinuousOn γ.toPath.extend (Set.Icc t₀ (t₀ + δPlus)))
    (hγ_cont_left : ContinuousOn γ.toPath.extend (Set.Icc (t₀ - δMinus) t₀))
    (h_leave_right : ∀ t ∈ Set.Ioc t₀ (t₀ + δPlus), γ.toPath.extend t ≠ s)
    (h_leave_left : ∀ t ∈ Set.Ico (t₀ - δMinus) t₀, γ.toPath.extend t ≠ s)
    -- Strict monotonicity (from transverse via L_minus / L_plus respectively)
    (hγ_anti : StrictAntiOn (fun t => ‖γ.toPath.extend t - s‖)
      (Set.Icc (t₀ - δMinus) t₀))
    (hγ_mono : StrictMonoOn (fun t => ‖γ.toPath.extend t - s‖)
      (Set.Icc t₀ (t₀ + δPlus)))
    -- Avoidance margins on outer regions
    {δ_avoid_left δ_avoid_right : ℝ}
    (h_avoid_left_pos : 0 < δ_avoid_left)
    (h_avoid_right_pos : 0 < δ_avoid_right)
    (h_avoid_left : ∀ t ∈ Set.Icc (0 : ℝ) (t₀ - δMinus),
      δ_avoid_left ≤ ‖γ.toPath.extend t - s‖)
    (h_avoid_right : ∀ t ∈ Set.Icc (t₀ + δPlus) (1 : ℝ),
      δ_avoid_right ≤ ‖γ.toPath.extend t - s‖)
    -- Smoothness on outer punctured intervals
    (h_minus_smooth : ∀ ε > 0,
      ∀ t ∈ Set.uIcc (0 : ℝ)
        (firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε),
      HasDerivAt γ.toPath.extend (deriv γ.toPath.extend t) t)
    (h_minus_avoids : ∀ ε > 0,
      ∀ t ∈ Set.uIcc (0 : ℝ)
        (firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε),
      γ.toPath.extend t ≠ s)
    (h_minus_int : ∀ ε > 0,
      IntervalIntegrable
        (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - s) ^ k)
        MeasureTheory.volume 0
        (firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε))
    (h_plus_smooth : ∀ ε > 0,
      ∀ t ∈ Set.uIcc
        (firstExitTimeRight γ.toPath.extend t₀ δPlus s ε) (1 : ℝ),
      HasDerivAt γ.toPath.extend (deriv γ.toPath.extend t) t)
    (h_plus_avoids : ∀ ε > 0,
      ∀ t ∈ Set.uIcc
        (firstExitTimeRight γ.toPath.extend t₀ δPlus s ε) (1 : ℝ),
      γ.toPath.extend t ≠ s)
    (h_plus_int : ∀ ε > 0,
      IntervalIntegrable
        (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - s) ^ k)
        MeasureTheory.volume
        (firstExitTimeRight γ.toPath.extend t₀ δPlus s ε) (1 : ℝ))
    -- CPV-integrand integrability (from contour integrability via auto-discharge helpers)
    (h_int_full : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => cpvIntegrandOn {s}
        (fun z => (1 : ℂ) / (z - s) ^ k) γ.toPath.extend ε t)
      MeasureTheory.volume 0 1) :
    HasCauchyPVOn {s} (fun z => (1 : ℂ) / (z - s) ^ k) γ 0 := by
  -- Step 1: Parametric PV under (B)
  have h_parametric :=
    hw_theorem_3_3_under_conditionB_parametric (γ := γ.toPath.extend)
      (γ' := deriv γ.toPath.extend) (s := s) (L_minus := L_minus)
      (L_plus := L_plus) (n := n) (k := k) (a := 0) (b := 1) (t₀ := t₀)
      h_close h_flat hL_minus hL_plus h_deriv_right h_deriv_left
      hL_right hL_left h_s hk hkn hn1 h_B
      (firstExitTimeRight γ.toPath.extend t₀ δPlus s)
      (firstExitTimeLeft γ.toPath.extend t₀ δMinus s)
      (firstExitTimeRight_tendsto_t₀ hδPlus hγ_cont_right h_s h_leave_right)
      (firstExitTimeRight_radius_eventually hδPlus hγ_cont_right h_s h_leave_right)
      (firstExitTimeLeft_tendsto_t₀ hδMinus hγ_cont_left h_s h_leave_left)
      (firstExitTimeLeft_radius_eventually hδMinus hγ_cont_left h_s h_leave_left)
      h_minus_smooth h_minus_avoids h_minus_int
      h_plus_smooth h_plus_avoids h_plus_int
  -- Step 2 + 3: Shape hypothesis from strict mono, then apply the bridge
  refine hasCauchyPVOn_singleton_of_exitTime_excision γ s
    (fun z => (1 : ℂ) / (z - s) ^ k)
    (shape_eventually_of_strict_mono
      h_t₀_minus_pos h_t₀_plus_le hδMinus hδPlus
      hγ_cont_left hγ_cont_right hγ_anti hγ_mono h_s
      h_avoid_left_pos h_avoid_right_pos h_avoid_left h_avoid_right)
    h_int_full ?_
  -- Reconcile integrand: deriv γ / (γ - s)^k = (1/(γ-s)^k) · deriv γ
  refine h_parametric.congr fun ε => ?_
  congr 1 <;>
  · refine intervalIntegral.integral_congr fun t _ => ?_
    show deriv γ.toPath.extend t / (γ.toPath.extend t - s) ^ k =
         (1 / (γ.toPath.extend t - s) ^ k) * deriv γ.toPath.extend t
    ring

end LeanModularForms

end
