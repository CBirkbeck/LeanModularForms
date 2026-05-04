/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.SectorCurve
import LeanModularForms.ForMathlib.HigherOrderCancel
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
  rw [show (-(↑((n - 1 : ℕ) : ℝ) * α : ℂ) * Complex.I) =
    -(↑(((n - 1 : ℕ) : ℝ) * α) * Complex.I) from by push_cast; ring]
  rw [hk]
  push_cast
  rw [show ((-(↑k * (2 * ↑Real.pi) * Complex.I)) : ℂ) =
    (((-k : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I)) from by push_cast; ring]
  rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I]
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
  rw [exp_neg_I_eq_one_of_conditionB n α h_angle]
  rw [sub_self, zero_div]

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
  apply Tendsto.congr' (f₁ := fun _ : ℝ => (0 : ℂ)) _ tendsto_const_nhds
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
  have h_zpow_eq : ∀ t : ℝ, t > 0 → (1 / t ^ n : ℝ) = t ^ (-(n : ℤ)) := by
    intro t ht
    rw [zpow_neg, zpow_natCast, ← one_div]
  have h_int_eq : ∫ t in a..b, (1 / t ^ n : ℝ) = ∫ t in a..b, t ^ (-(n : ℤ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact h_zpow_eq t (lt_of_lt_of_le ha ht.1)
  rw [h_int_eq]
  have h_not_neg_one : (-(n : ℤ)) ≠ -1 := by intro h; omega
  have h_zero_not_in : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact fun h => absurd h.1 (not_le.mpr ha)
  rw [integral_zpow (Or.inr ⟨h_not_neg_one, h_zero_not_in⟩)]
  have h_neg_n_plus_one : (-(n : ℤ)) + 1 = -((n - 1 : ℕ) : ℤ) := by omega
  rw [h_neg_n_plus_one]
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  have ha_pow : a ^ (n - 1) > 0 := pow_pos ha (n - 1)
  have hb_pow : b ^ (n - 1) > 0 := pow_pos (lt_of_lt_of_le ha hab) (n - 1)
  have hn1_pos : (0 : ℝ) < (n - 1 : ℕ) := by
    have h1 : (1 : ℕ) ≤ n - 1 := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
  have h_denom_eq : ((↑(-(n : ℤ)) + 1 : ℝ)) = -((n - 1 : ℕ) : ℝ) := by
    push_cast
    have hn1_real : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have h1 : 1 ≤ n := by omega
      rw [Nat.cast_sub h1]
      push_cast; rfl
    rw [hn1_real]
    ring
  rw [h_denom_eq]
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
    have ht_pos : 0 < t := lt_of_lt_of_le ha ht.1
    have ht_ne : (↑t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_pos.ne'
    have ht_pow_ne : (↑t : ℂ) ^ n ≠ 0 := pow_ne_zero _ ht_ne
    push_cast
    field_simp
  have h_step1 : (∫ t in a..b, c / (↑t : ℂ) ^ n) =
      ∫ t in a..b, c * (↑(1 / t ^ n : ℝ) : ℂ) :=
    intervalIntegral.integral_congr h_eq
  rw [h_step1]
  have h_step2 : (∫ t in a..b, c * (↑(1 / t ^ n : ℝ) : ℂ)) =
      c * ∫ t in a..b, (↑(1 / t ^ n : ℝ) : ℂ) :=
    intervalIntegral.integral_const_mul c (fun t : ℝ => (↑(1 / t ^ n : ℝ) : ℂ))
  rw [h_step2]
  rw [intervalIntegral.integral_ofReal]
  rw [real_ray_inv_pow_integral a b ha hab n hn]
  push_cast
  have hn1_ne : (↑(n - 1 : ℕ) : ℂ) ≠ 0 := by rw [Nat.cast_ne_zero]; omega
  have ha_ne : (↑a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hb_ne : (↑b : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le ha hab).ne'
  have ha_pow : (↑a : ℂ) ^ (n - 1) ≠ 0 := pow_ne_zero _ ha_ne
  have hb_pow : (↑b : ℂ) ^ (n - 1) ≠ 0 := pow_ne_zero _ hb_ne
  field_simp

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
  have hr_pow_ne : (↑r : ℂ) ^ (n - 1) ≠ 0 := pow_ne_zero _ hr_ne
  have hn1_ne : (↑(n - 1 : ℕ) : ℂ) ≠ 0 := by rw [Nat.cast_ne_zero]; omega
  -- Simplify the integrand to (i/r^(n-1)) · exp(c · t) where c = -i(n-1)
  have h_eq : ∀ t : ℝ,
      ((↑r : ℂ) * Complex.I * Complex.exp ((↑t : ℂ) * Complex.I)) /
        ((↑r : ℂ) * Complex.exp ((↑t : ℂ) * Complex.I)) ^ n =
      (Complex.I / (↑r : ℂ) ^ (n - 1)) *
        Complex.exp ((-(↑(n - 1 : ℕ) : ℂ) * Complex.I) * (↑t : ℂ)) := by
    intro t
    have h_exp_ne : Complex.exp ((↑t : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have h_prod_ne : (↑r : ℂ) * Complex.exp ((↑t : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero hr_ne h_exp_ne
    rw [mul_pow]
    have h_pow_n : (↑r : ℂ) ^ n = (↑r : ℂ) ^ (n - 1) * (↑r : ℂ) := by
      conv_lhs => rw [show n = (n - 1) + 1 from by omega]
      rw [pow_succ]
    rw [h_pow_n]
    -- exp factor: exp(it)^n = exp(int) = exp(i(n-1)t) · exp(it)
    have h_exp_pow : Complex.exp ((↑t : ℂ) * Complex.I) ^ n =
        Complex.exp ((↑(n - 1 : ℕ) : ℂ) * (↑t : ℂ) * Complex.I) *
          Complex.exp ((↑t : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      rw [show n = (n - 1) + 1 from by omega]
      push_cast; ring
    rw [h_exp_pow]
    rw [show -(↑(n - 1 : ℕ) : ℂ) * Complex.I * (↑t : ℂ) =
      -((↑(n - 1 : ℕ) : ℂ) * (↑t : ℂ) * Complex.I) from by ring]
    rw [Complex.exp_neg]
    field_simp
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
  rw [h_step]
  -- Now ∫_0^α exp(c · t) dt = (exp(c·α) - 1)/c where c = -i(n-1)
  have h_c_ne : (-(↑(n - 1 : ℕ) : ℂ) * Complex.I) ≠ 0 := by
    apply mul_ne_zero (neg_ne_zero.mpr hn1_ne) Complex.I_ne_zero
  rw [integral_exp_mul_complex h_c_ne]
  push_cast
  rw [show (-(↑(n - 1 : ℕ) : ℂ) * Complex.I) * (↑α : ℂ) =
    -(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I) from by ring]
  rw [show (-(↑(n - 1 : ℕ) : ℂ) * Complex.I) * ((0 : ℂ)) = 0 from by ring]
  rw [Complex.exp_zero]
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
  have hn1_ne : (↑(n - 1 : ℕ) : ℂ) ≠ 0 := by rw [Nat.cast_ne_zero]; omega
  have hε_ne : (↑ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  have hr_ne : (↑r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hε_pow : (↑ε : ℂ) ^ (n - 1) ≠ 0 := pow_ne_zero _ hε_ne
  have hr_pow : (↑r : ℂ) ^ (n - 1) ≠ 0 := pow_ne_zero _ hr_ne
  field_simp
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
  rw [sector_inv_pow_integral_combined r hr ε hε hεr α n hn]
  -- Under condition (B), exp(-(n-1) * α * I) = 1
  have h_exp_one :
      Complex.exp (-(↑((n - 1 : ℕ) : ℝ) * α : ℂ) * Complex.I) = 1 :=
    exp_neg_I_eq_one_of_conditionB n α h_angle
  -- Match form
  rw [show (-(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I) : ℂ) =
    (-(↑((n - 1 : ℕ) : ℝ) * α : ℂ)) * Complex.I from by push_cast; ring]
  rw [h_exp_one]
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
  apply Tendsto.congr' (f₁ := fun _ : ℝ => (0 : ℂ)) _ tendsto_const_nhds
  filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
  have hε_pos : 0 < ε := hε.1
  have hε_le_r : ε ≤ r := le_of_lt hε.2
  exact (sector_inv_pow_integral_vanishes_under_conditionB r hr ε hε_pos
    hε_le_r α n hn h_angle).symm

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
  congr 1
  congr 1
  -- Reduce to ((s + ε • L_plus / ‖L_plus‖) - s)^(k-1) = ((s + ε • (-L_minus / ‖L_minus‖)) - s)^(k-1)
  -- which simplifies to (ε • L_plus / ‖L_plus‖)^(k-1) = (ε • (-L_minus / ‖L_minus‖))^(k-1)
  -- which factors out ε^(k-1), giving (L_plus/‖L_plus‖)^(k-1) = (-L_minus/‖L_minus‖)^(k-1) (B).
  have hLp_norm_ne : (‖L_plus‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hL_plus
  have hLm_norm_ne : (‖L_minus‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hL_minus
  have hLp_norm_ne_C : (↑‖L_plus‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLp_norm_ne
  have hLm_norm_ne_C : (↑‖L_minus‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLm_norm_ne
  have h_lhs : ((s + (ε / ‖L_plus‖ : ℝ) • L_plus) - s) ^ (k - 1) =
      ((↑ε : ℂ) ^ (k - 1)) * ((L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1)) := by
    rw [add_sub_cancel_left]
    have h_smul_eq : ((ε / ‖L_plus‖ : ℝ) • L_plus : ℂ) =
        (↑ε : ℂ) * (L_plus / (↑‖L_plus‖ : ℂ)) := by
      rw [Complex.real_smul]
      push_cast
      field_simp
    rw [h_smul_eq, mul_pow]
  have h_rhs : ((s + (ε / ‖L_minus‖ : ℝ) • (-L_minus)) - s) ^ (k - 1) =
      ((↑ε : ℂ) ^ (k - 1)) * (((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1)) := by
    rw [add_sub_cancel_left]
    have h_smul_eq : ((ε / ‖L_minus‖ : ℝ) • (-L_minus) : ℂ) =
        (↑ε : ℂ) * ((-L_minus) / (↑‖L_minus‖ : ℂ)) := by
      rw [Complex.real_smul]
      push_cast
      field_simp
    rw [h_smul_eq, mul_pow]
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
  -- Right-side F-diff at chord target (with L_plus) → 0
  have h_right := F_diff_at_tangent_target_tendsto_zero_right
    h_flat hL_plus h_deriv_right hL_right h_s hk hkn hn1
  have h_right_comp := h_right.comp h_plus_to
  -- Left-side F-diff at chord target (with L_minus) → 0
  have h_left := F_diff_at_tangent_target_tendsto_zero_left
    h_flat hL_minus h_deriv_left hL_left h_s hk hkn hn1
  have h_left_comp := h_left.comp h_minus_to
  have h_sum_raw := h_right_comp.add h_left_comp
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
  have h_neg_norm : ‖(-L_minus)‖ = ‖L_minus‖ := norm_neg L_minus
  have h_targets_eq :
      -(↑(k - 1) : ℂ)⁻¹ *
        (((s + (‖γ (t_eps_minus ε) - s‖ / ‖(-L_minus)‖ : ℝ) • (-L_minus)) - s)
          ^ (k - 1))⁻¹ =
      -(↑(k - 1) : ℂ)⁻¹ *
        (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L_plus‖ : ℝ) • L_plus) - s) ^ (k - 1))⁻¹ := by
    rw [hmr, h_neg_norm, hpr]
    -- Now show: F at (s + (ε / ‖L_minus‖) • (-L_minus)) = F at (s + (ε / ‖L_plus‖) • L_plus)
    exact (F_line_diff_eq_zero_under_conditionB s L_minus L_plus k hk
      hL_minus hL_plus h_B ε).symm
  set TR := -(↑(k - 1) : ℂ)⁻¹ *
    (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L_plus‖ : ℝ) • L_plus) - s) ^ (k - 1))⁻¹
  set A := -(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹
  set B := -(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹
  have h_triangle : ‖A - B‖ ≤ ‖B - TR‖ + ‖A - TR‖ := by
    calc ‖A - B‖ = ‖(A - TR) - (B - TR)‖ := by ring_nf
      _ ≤ ‖A - TR‖ + ‖B - TR‖ := norm_sub_le _ _
      _ = ‖B - TR‖ + ‖A - TR‖ := add_comm _ _
  show ‖A - B‖ ≤ ‖B - TR‖ + ‖A - _‖
  rw [h_targets_eq]
  exact h_triangle

end LeanModularForms

end
