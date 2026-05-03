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

open Filter Topology Set Complex Real

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

end LeanModularForms

end
