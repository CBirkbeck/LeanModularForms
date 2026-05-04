/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.SectorCurve
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

end LeanModularForms

end
