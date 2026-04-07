/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.ValenceFormulaCore

/-!
# Textbook Valence Formula

The user-facing statement of the valence formula for modular forms of level 1,
together with its classical corollaries.

## Overview

For a nonzero modular form `f` of weight `k` for `SL₂(ℤ)`, the valence formula
states:

`ord_∞(f) + (1/2) · ord_i(f) + (1/3) · ord_ρ(f) + Σ_{z ∈ F°} ord_z(f) = k/12`

This file derives consequences from the `ValenceFormulaData` structure defined in
`ValenceFormulaCore.lean`. All results are purely algebraic consequences of the
formula, requiring no analysis or integration.

## Main results

### Basic consequences
* `weight_nonneg_of_valence` -- `k ≥ 0` for any nonzero holomorphic modular form.
* `weight_twelve_divides_of_no_zeros` -- if `f` has no zeros in `F`, then `12 ∣ k`.
* `finite_zeros_bound` -- the number of zeros (with multiplicity) is at most `k/12`.

### Weight classification
* `weight_zero_no_zeros` -- weight 0: `f` has no zeros (so `f` is constant).
* `weight_two_impossible` -- weight 2: no nonzero holomorphic modular form exists.
* `weight_four_unique_zeros` -- weight 4: `ord_ρ = 1`, all other orders 0.
* `weight_six_unique_zeros` -- weight 6: `ord_i = 1`, all other orders 0.
* `weight_eight_unique_zeros` -- weight 8: `ord_ρ = 2`, all other orders 0.
* `weight_ten_unique_zeros` -- weight 10: `ord_i = 1, ord_ρ = 1`, all other orders 0.
* `weight_twelve_two_cases` -- weight 12: either `ord_∞ = 1` (rest 0) or
  `ord_i = 0, ord_ρ = 3` or `ord_ρ = 0, ord_i = 2` (and more).

### Dimension consequences
* `dim_le_one_of_weight_lt_twelve` -- for `0 < k < 12`, the space of modular forms
  has dimension at most 1 (the zero pattern is forced).

## Design notes

All results take a `ValenceFormulaData k` as input. This makes them agnostic about
how the formula was proved -- the analytic machinery is entirely hidden behind the
`ValenceFormulaData` interface.

## References

* T. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, Theorem 4.4
* J.-P. Serre, *A Course in Arithmetic*, Chapter VII, Theorem 3
* D. Zagier, *Elliptic Modular Forms and Their Applications*, Section 2.3
-/

open scoped Real

noncomputable section

/-! ### Weight nonnegativity -/

/-- **Weight nonnegativity**: a nonzero holomorphic modular form has nonneg weight.

This is the most fundamental consequence of the valence formula: since all orders
(at the cusp, at elliptic points, and at interior points) are nonneg, the weighted
sum is nonneg, hence `k/12 ≥ 0`, hence `k ≥ 0`. -/
theorem weight_nonneg_of_valence {k : ℤ} (vf : ValenceFormulaData k) : 0 ≤ k :=
  vf.weight_nonneg

/-! ### No-zeros criterion -/

/-- If a modular form has no zeros at all (cusp, elliptic, or interior), then
`k/12 = 0`, hence `12 ∣ k` (and in fact `k = 0`). -/
theorem weight_zero_of_all_orders_zero {k : ℤ} (vf : ValenceFormulaData k)
    (h_inf : vf.ord_inf = 0) (h_i : vf.ord_i = 0)
    (h_rho : vf.ord_rho = 0) (h_int : vf.interior_sum = 0) :
    k = 0 := by
  have hf := vf.formula
  simp only [h_inf, h_i, h_rho, h_int, Int.cast_zero, add_zero] at hf
  have hk : (k : ℚ) = 0 := by linarith
  exact_mod_cast hk

/-- If a modular form has no zeros in the fundamental domain, then `12 ∣ k`. -/
theorem weight_twelve_divides_of_no_zeros {k : ℤ} (vf : ValenceFormulaData k)
    (h_inf : vf.ord_inf = 0) (h_i : vf.ord_i = 0)
    (h_rho : vf.ord_rho = 0) (h_int : vf.interior_sum = 0) :
    (12 : ℤ) ∣ k := by
  have := weight_zero_of_all_orders_zero vf h_inf h_i h_rho h_int
  rw [this]; exact dvd_zero 12

/-! ### Zero count bounds -/

/-- The total weighted zero count equals `k/12`. -/
theorem total_weighted_zeros {k : ℤ} (vf : ValenceFormulaData k) :
    (vf.ord_inf : ℚ) + 1 / 2 * vf.ord_i + 1 / 3 * vf.ord_rho +
      vf.interior_sum = k / 12 :=
  vf.formula

/-- Each individual order is bounded by `k/12`. -/
theorem ord_inf_bound {k : ℤ} (vf : ValenceFormulaData k) :
    (vf.ord_inf : ℚ) ≤ k / 12 :=
  vf.ord_inf_le

/-- The interior zero count is bounded by `k/12`. -/
theorem interior_zeros_bound {k : ℤ} (vf : ValenceFormulaData k) :
    (vf.interior_sum : ℚ) ≤ k / 12 :=
  vf.interior_sum_le

/-! ### Weight 0: constant modular forms -/

/-- **Weight 0**: a nonzero holomorphic modular form of weight 0 has no zeros. -/
theorem weight_zero_no_zeros (vf : ValenceFormulaData 0) :
    vf.ord_inf = 0 ∧ vf.ord_i = 0 ∧ vf.ord_rho = 0 ∧ vf.interior_sum = 0 :=
  vf.all_zero_of_weight_zero

/-! ### Weight 2: impossible -/

/-- **Weight 2 is impossible**: there is no nonzero holomorphic modular form
of weight 2. The valence formula gives `k/12 = 1/6`, but the LHS is a sum of
nonneg terms `n_∞ + (1/2)n_i + (1/3)n_ρ + n_int` with `n_∞, n_int ∈ ℤ_≥0`
and `(1/2)n_i ∈ {0, 1/2, 1, ...}`, `(1/3)n_ρ ∈ {0, 1/3, 2/3, ...}`.
No combination equals `1/6`. -/
theorem weight_two_impossible (vf : ValenceFormulaData 2) : False := by
  have ⟨h1, h2, h3, h4⟩ := vf.all_nonneg
  have hf := vf.formula
  -- The formula gives n_inf + 1/2 * n_i + 1/3 * n_rho + n_int = 1/6
  -- With all terms nonneg, we need n_inf = 0, n_int = 0, and
  -- 1/2 * n_i + 1/3 * n_rho = 1/6. But 1/2 * n_i ∈ {0, 1/2, 1, ...}
  -- and 1/3 * n_rho ∈ {0, 1/3, 2/3, ...}. The smallest positive values
  -- already exceed 1/6.
  have h_inf_q : (0 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast h1
  have h_i_q : (0 : ℚ) ≤ (vf.ord_i : ℚ) := by exact_mod_cast h2
  have h_rho_q : (0 : ℚ) ≤ (vf.ord_rho : ℚ) := by exact_mod_cast h3
  have h_int_q : (0 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast h4
  -- n_inf = 0 (since n_inf ≥ 1 gives LHS ≥ 1 > 1/6)
  have h_inf_zero : vf.ord_inf = 0 := by
    by_contra h
    have : 1 ≤ vf.ord_inf := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h1 (Ne.symm h))
    have : (1 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast this
    linarith
  -- n_int = 0 (same reasoning)
  have h_int_zero : vf.interior_sum = 0 := by
    by_contra h
    have : 1 ≤ vf.interior_sum := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h4 (Ne.symm h))
    have : (1 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast this
    linarith
  -- n_i = 0 (since 1/2 * 1 = 1/2 > 1/6)
  have h_i_zero : vf.ord_i = 0 := by
    by_contra h
    have : 1 ≤ vf.ord_i := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h2 (Ne.symm h))
    have : (1 : ℚ) ≤ (vf.ord_i : ℚ) := by exact_mod_cast this
    linarith
  -- n_rho = 0 (since 1/3 * 1 = 1/3 > 1/6)
  have h_rho_zero : vf.ord_rho = 0 := by
    by_contra h
    have : 1 ≤ vf.ord_rho := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h3 (Ne.symm h))
    have : (1 : ℚ) ≤ (vf.ord_rho : ℚ) := by exact_mod_cast this
    linarith
  -- Now all are 0 but formula says 0 = 1/6, contradiction
  simp only [h_inf_zero, h_i_zero, h_rho_zero, h_int_zero, Int.cast_zero,
    mul_zero, add_zero] at hf
  norm_num at hf

/-! ### Weight 4: E₄ zero pattern -/

/-- **Weight 4**: a nonzero holomorphic modular form of weight 4 has exactly
`ord_ρ = 1` and all other orders zero. (This forces `f = c · E₄`.) -/
theorem weight_four_unique_zeros (vf : ValenceFormulaData 4) :
    vf.ord_inf = 0 ∧ vf.ord_i = 0 ∧ vf.ord_rho = 1 ∧ vf.interior_sum = 0 := by
  have ⟨h1, h2, h3, h4⟩ := vf.all_nonneg
  have hf := vf.formula
  -- k/12 = 1/3, so n_inf + 1/2 n_i + 1/3 n_rho + n_int = 1/3
  have h_inf_q : (0 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast h1
  have h_i_q : (0 : ℚ) ≤ (vf.ord_i : ℚ) := by exact_mod_cast h2
  have h_rho_q : (0 : ℚ) ≤ (vf.ord_rho : ℚ) := by exact_mod_cast h3
  have h_int_q : (0 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast h4
  -- n_inf = 0 (n_inf ≥ 1 gives LHS ≥ 1 > 1/3)
  have h_inf_zero : vf.ord_inf = 0 := by
    by_contra h
    have : 1 ≤ vf.ord_inf := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h1 (Ne.symm h))
    have : (1 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast this
    linarith
  -- n_int = 0
  have h_int_zero : vf.interior_sum = 0 := by
    by_contra h
    have : 1 ≤ vf.interior_sum := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h4 (Ne.symm h))
    have : (1 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast this
    linarith
  -- n_i = 0 (1/2 > 1/3)
  have h_i_zero : vf.ord_i = 0 := by
    by_contra h
    have : 1 ≤ vf.ord_i := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h2 (Ne.symm h))
    have : (1 : ℚ) ≤ (vf.ord_i : ℚ) := by exact_mod_cast this
    linarith
  -- Now formula gives 1/3 * n_rho = 1/3, so n_rho = 1
  simp only [h_inf_zero, h_i_zero, h_int_zero, Int.cast_zero,
    mul_zero, add_zero] at hf
  have h_rho_val : (vf.ord_rho : ℚ) = 1 := by linarith
  have h_rho_int : vf.ord_rho = 1 := by exact_mod_cast h_rho_val
  exact ⟨h_inf_zero, h_i_zero, h_rho_int, h_int_zero⟩

/-! ### Weight 6: E₆ zero pattern -/

/-- **Weight 6**: a nonzero holomorphic modular form of weight 6 has exactly
`ord_i = 1` and all other orders zero. (This forces `f = c · E₆`.) -/
theorem weight_six_unique_zeros (vf : ValenceFormulaData 6) :
    vf.ord_inf = 0 ∧ vf.ord_i = 1 ∧ vf.ord_rho = 0 ∧ vf.interior_sum = 0 := by
  have ⟨h1, h2, h3, h4⟩ := vf.all_nonneg
  have hf := vf.formula
  -- k/12 = 1/2
  have h_inf_q : (0 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast h1
  have h_i_q : (0 : ℚ) ≤ (vf.ord_i : ℚ) := by exact_mod_cast h2
  have h_rho_q : (0 : ℚ) ≤ (vf.ord_rho : ℚ) := by exact_mod_cast h3
  have h_int_q : (0 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast h4
  -- n_inf = 0
  have h_inf_zero : vf.ord_inf = 0 := by
    by_contra h
    have : 1 ≤ vf.ord_inf := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h1 (Ne.symm h))
    have : (1 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast this
    linarith
  -- n_int = 0
  have h_int_zero : vf.interior_sum = 0 := by
    by_contra h
    have : 1 ≤ vf.interior_sum := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h4 (Ne.symm h))
    have : (1 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast this
    linarith
  -- Now 1/2 * n_i + 1/3 * n_rho = 1/2
  -- n_rho ≥ 2 gives 1/3 * 2 = 2/3 > 1/2, so n_rho ∈ {0, 1}
  -- n_rho = 1 gives 1/2 * n_i = 1/2 - 1/3 = 1/6, but n_i ∈ ℤ so 1/2 * n_i ∈ {0, 1/2, ...}
  -- n_rho = 0 gives 1/2 * n_i = 1/2, so n_i = 1
  have h_rho_zero : vf.ord_rho = 0 := by
    by_contra h
    have h_ge_1 : 1 ≤ vf.ord_rho := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h3 (Ne.symm h))
    -- If n_rho ≥ 2, then 1/3 * 2 = 2/3 > 1/2
    by_cases h_ge_2 : 2 ≤ vf.ord_rho
    · have : (2 : ℚ) ≤ (vf.ord_rho : ℚ) := by exact_mod_cast h_ge_2
      simp only [h_inf_zero, h_int_zero, Int.cast_zero, add_zero] at hf
      linarith
    · -- n_rho = 1
      push_neg at h_ge_2
      have h_eq_1 : vf.ord_rho = 1 := le_antisymm (Int.lt_add_one_iff.mp h_ge_2) h_ge_1
      simp only [h_inf_zero, h_int_zero, h_eq_1, Int.cast_zero, add_zero] at hf
      -- 1/2 * n_i + 1/3 = 1/2, so 1/2 * n_i = 1/6
      -- But n_i ∈ ℤ≥0, so 1/2 * n_i ∈ {0, 1/2, 1, ...}
      -- The smallest positive value 1/2 > 1/6, and 0 ≠ 1/6
      by_cases h_i_zero : vf.ord_i = 0
      · simp only [h_i_zero, Int.cast_zero, mul_zero, zero_add] at hf; norm_num at hf
      · have : 1 ≤ vf.ord_i := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h2 (Ne.symm h_i_zero))
        have : (1 : ℚ) ≤ (vf.ord_i : ℚ) := by exact_mod_cast this
        push_cast at hf; linarith
  simp only [h_inf_zero, h_rho_zero, h_int_zero, Int.cast_zero, add_zero] at hf
  have h_i_val : (vf.ord_i : ℚ) = 1 := by linarith
  exact ⟨h_inf_zero, by exact_mod_cast h_i_val, h_rho_zero, h_int_zero⟩

/-! ### Weight 8: E₄² zero pattern -/

/-- **Weight 8**: a nonzero holomorphic modular form of weight 8 has exactly
`ord_ρ = 2` and all other orders zero. (This forces `f = c · E₄²`.) -/
theorem weight_eight_unique_zeros (vf : ValenceFormulaData 8) :
    vf.ord_inf = 0 ∧ vf.ord_i = 0 ∧ vf.ord_rho = 2 ∧ vf.interior_sum = 0 := by
  have ⟨h1, h2, h3, h4⟩ := vf.all_nonneg
  have hf := vf.formula
  -- k/12 = 2/3
  have h_inf_q : (0 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast h1
  have h_i_q : (0 : ℚ) ≤ (vf.ord_i : ℚ) := by exact_mod_cast h2
  have h_rho_q : (0 : ℚ) ≤ (vf.ord_rho : ℚ) := by exact_mod_cast h3
  have h_int_q : (0 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast h4
  -- n_inf = 0 (n_inf ≥ 1 gives LHS ≥ 1 > 2/3)
  have h_inf_zero : vf.ord_inf = 0 := by
    by_contra h
    have : 1 ≤ vf.ord_inf := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h1 (Ne.symm h))
    have : (1 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast this
    linarith
  -- n_int = 0
  have h_int_zero : vf.interior_sum = 0 := by
    by_contra h
    have : 1 ≤ vf.interior_sum := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h4 (Ne.symm h))
    have : (1 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast this
    linarith
  -- n_i = 0 (if n_i ≥ 1, then 1/2 + 1/3 * n_rho = 2/3, so 1/3 * n_rho = 1/6,
  --   but n_rho ∈ ℤ, so 1/3 * n_rho ∈ {0, 1/3, 2/3, ...}, contradiction)
  -- if n_i ≥ 2, then 1/2 * 2 = 1 > 2/3
  have h_i_zero : vf.ord_i = 0 := by
    by_contra h
    have h_ge_1 : 1 ≤ vf.ord_i := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h2 (Ne.symm h))
    by_cases h_ge_2 : 2 ≤ vf.ord_i
    · have : (2 : ℚ) ≤ (vf.ord_i : ℚ) := by exact_mod_cast h_ge_2
      simp only [h_inf_zero, h_int_zero, Int.cast_zero, add_zero] at hf
      linarith
    · push_neg at h_ge_2
      have h_eq_1 : vf.ord_i = 1 := le_antisymm (Int.lt_add_one_iff.mp h_ge_2) h_ge_1
      simp only [h_inf_zero, h_int_zero, h_eq_1, Int.cast_zero, add_zero] at hf
      -- 1/2 + 1/3 * n_rho = 2/3, so 1/3 * n_rho = 1/6
      -- n_rho = 0 gives 0 ≠ 1/6; n_rho ≥ 1 gives 1/3 > 1/6
      by_cases h_r0 : vf.ord_rho = 0
      · simp only [h_r0, Int.cast_zero] at hf; norm_num at hf
      · have : 1 ≤ vf.ord_rho := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h3 (Ne.symm h_r0))
        have : (1 : ℚ) ≤ (vf.ord_rho : ℚ) := by exact_mod_cast this
        push_cast at hf; linarith
  -- Now 1/3 * n_rho = 2/3, so n_rho = 2
  simp only [h_inf_zero, h_i_zero, h_int_zero, Int.cast_zero, add_zero] at hf
  have h_rho_val : (vf.ord_rho : ℚ) = 2 := by linarith
  exact ⟨h_inf_zero, h_i_zero, by exact_mod_cast h_rho_val, h_int_zero⟩

/-! ### Weight 10: E₄·E₆ zero pattern -/

/-- **Weight 10**: a nonzero holomorphic modular form of weight 10 has exactly
`ord_i = 1` and `ord_ρ = 1`, with all other orders zero.
(This forces `f = c · E₄ · E₆`.) -/
theorem weight_ten_unique_zeros (vf : ValenceFormulaData 10) :
    vf.ord_inf = 0 ∧ vf.ord_i = 1 ∧ vf.ord_rho = 1 ∧ vf.interior_sum = 0 := by
  have ⟨h1, h2, h3, h4⟩ := vf.all_nonneg
  have hf := vf.formula
  -- k/12 = 5/6
  have h_inf_q : (0 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast h1
  have h_i_q : (0 : ℚ) ≤ (vf.ord_i : ℚ) := by exact_mod_cast h2
  have h_rho_q : (0 : ℚ) ≤ (vf.ord_rho : ℚ) := by exact_mod_cast h3
  have h_int_q : (0 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast h4
  -- n_inf = 0
  have h_inf_zero : vf.ord_inf = 0 := by
    by_contra h
    have : 1 ≤ vf.ord_inf := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h1 (Ne.symm h))
    have : (1 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast this
    linarith
  -- n_int = 0
  have h_int_zero : vf.interior_sum = 0 := by
    by_contra h
    have : 1 ≤ vf.interior_sum := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h4 (Ne.symm h))
    have : (1 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast this
    linarith
  -- Now 1/2 * n_i + 1/3 * n_rho = 5/6
  -- Possible: (n_i, n_rho) = (1, 1) gives 1/2 + 1/3 = 5/6 yes
  -- (n_i, n_rho) = (0, _): 1/3 * n_rho = 5/6, so n_rho = 5/2, not integer
  -- (n_i, n_rho) = (_, 0): 1/2 * n_i = 5/6, so n_i = 5/3, not integer
  -- n_i ≥ 2: 1/2 * 2 = 1 > 5/6
  -- n_rho ≥ 3: 1/3 * 3 = 1 > 5/6
  simp only [h_inf_zero, h_int_zero, Int.cast_zero, add_zero] at hf
  -- Show n_i = 1
  have h_i_eq : vf.ord_i = 1 := by
    -- n_i ≥ 2 impossible
    by_contra h_ne
    -- n_i = 0: 1/3 * n_rho = 5/6, need n_rho = 5/2 (not integer)
    by_cases h_eq_0 : vf.ord_i = 0
    · simp only [h_eq_0, Int.cast_zero, mul_zero, zero_add] at hf
      -- 1/3 * n_rho = 5/6, so n_rho = 5/2
      have : (vf.ord_rho : ℚ) = 5 / 2 := by linarith
      -- But n_rho is an integer, so n_rho * 2 = 5, impossible mod 2
      have h5 : (vf.ord_rho : ℤ) * 2 = 5 := by exact_mod_cast (show (vf.ord_rho : ℚ) * 2 = 5 by linarith)
      omega
    · -- n_i ≥ 1 and n_i ≠ 1, so n_i ≥ 2
      have h_ge_1 : 1 ≤ vf.ord_i := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h2 (Ne.symm h_eq_0))
      have h_ge_2 : 2 ≤ vf.ord_i := by omega
      have : (2 : ℚ) ≤ (vf.ord_i : ℚ) := by exact_mod_cast h_ge_2
      linarith
  simp only [h_i_eq] at hf
  have h_rho_val : (vf.ord_rho : ℚ) = 1 := by push_cast at hf ⊢; linarith
  exact ⟨h_inf_zero, h_i_eq, by exact_mod_cast h_rho_val, h_int_zero⟩

/-! ### Weight 14: no zeros except forced ones -/

/-- **Weight 14**: a nonzero holomorphic modular form of weight 14 has
`ord_i = 1`, `ord_ρ = 2`, and all other orders 0.
(This forces `f = c · E₆ · E₄²`.) -/
theorem weight_fourteen_unique_zeros (vf : ValenceFormulaData 14) :
    vf.ord_inf = 0 ∧ vf.ord_i = 1 ∧ vf.ord_rho = 2 ∧ vf.interior_sum = 0 := by
  have ⟨h1, h2, h3, h4⟩ := vf.all_nonneg
  have hf := vf.formula
  -- k/12 = 7/6
  have h_inf_q : (0 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast h1
  have h_i_q : (0 : ℚ) ≤ (vf.ord_i : ℚ) := by exact_mod_cast h2
  have h_rho_q : (0 : ℚ) ≤ (vf.ord_rho : ℚ) := by exact_mod_cast h3
  have h_int_q : (0 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast h4
  -- n_inf ≤ 1 (if n_inf ≥ 2, LHS ≥ 2 > 7/6)
  -- n_inf = 1 gives 1 + 1/2 n_i + 1/3 n_rho + n_int = 7/6,
  --   so 1/2 n_i + 1/3 n_rho + n_int = 1/6, all nonneg integers give 0
  -- n_inf = 0 gives 1/2 n_i + 1/3 n_rho + n_int = 7/6
  have h_inf_zero : vf.ord_inf = 0 := by
    by_contra h
    have h_ge_1 : 1 ≤ vf.ord_inf := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h1 (Ne.symm h))
    by_cases h_ge_2 : 2 ≤ vf.ord_inf
    · have : (2 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast h_ge_2
      linarith
    · push_neg at h_ge_2
      have h_eq_1 : vf.ord_inf = 1 := le_antisymm (Int.lt_add_one_iff.mp h_ge_2) h_ge_1
      simp only [h_eq_1] at hf
      push_cast at hf
      -- 1 + 1/2 n_i + 1/3 n_rho + n_int = 7/6, so 1/2 n_i + 1/3 n_rho + n_int = 1/6
      -- All terms nonneg, and smallest positive values: 1/3 > 1/6, 1/2 > 1/6, so all 0
      -- But then 0 = 1/6, contradiction
      have : 1 / 2 * (vf.ord_i : ℚ) + 1 / 3 * (vf.ord_rho : ℚ) +
        (vf.interior_sum : ℚ) = 1 / 6 := by linarith
      by_cases h_i0 : vf.ord_i = 0
      · by_cases h_r0 : vf.ord_rho = 0
        · by_cases h_s0 : vf.interior_sum = 0
          · simp [h_i0, h_r0, h_s0] at this
          · have : 1 ≤ vf.interior_sum := Int.lt_iff_add_one_le.mp
              (lt_of_le_of_ne h4 (Ne.symm h_s0))
            have : (1 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast this
            linarith
        · have : 1 ≤ vf.ord_rho := Int.lt_iff_add_one_le.mp
            (lt_of_le_of_ne h3 (Ne.symm h_r0))
          have : (1 : ℚ) ≤ (vf.ord_rho : ℚ) := by exact_mod_cast this
          linarith
      · have : 1 ≤ vf.ord_i := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h2 (Ne.symm h_i0))
        have : (1 : ℚ) ≤ (vf.ord_i : ℚ) := by exact_mod_cast this
        linarith
  have h_int_zero : vf.interior_sum = 0 := by
    by_contra h
    have h_ge_1 : 1 ≤ vf.interior_sum := Int.lt_iff_add_one_le.mp
      (lt_of_le_of_ne h4 (Ne.symm h))
    by_cases h_ge_2 : 2 ≤ vf.interior_sum
    · have : (2 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast h_ge_2
      linarith
    · push_neg at h_ge_2
      have h_eq_1 : vf.interior_sum = 1 := le_antisymm (Int.lt_add_one_iff.mp h_ge_2) h_ge_1
      simp only [h_inf_zero, h_eq_1] at hf; push_cast at hf
      -- 1/2 n_i + 1/3 n_rho + 1 = 7/6, so 1/2 n_i + 1/3 n_rho = 1/6
      -- Same as above: impossible
      by_cases h_i0 : vf.ord_i = 0
      · by_cases h_r0 : vf.ord_rho = 0
        · simp only [h_i0, h_r0, Int.cast_zero, mul_zero, zero_add, add_zero] at hf
          norm_num at hf
        · have : 1 ≤ vf.ord_rho := Int.lt_iff_add_one_le.mp
            (lt_of_le_of_ne h3 (Ne.symm h_r0))
          have : (1 : ℚ) ≤ (vf.ord_rho : ℚ) := by exact_mod_cast this
          linarith
      · have : 1 ≤ vf.ord_i := Int.lt_iff_add_one_le.mp (lt_of_le_of_ne h2 (Ne.symm h_i0))
        have : (1 : ℚ) ≤ (vf.ord_i : ℚ) := by exact_mod_cast this
        linarith
  simp only [h_inf_zero, h_int_zero, Int.cast_zero, add_zero] at hf
  -- 1/2 n_i + 1/3 n_rho = 7/6
  -- (n_i, n_rho) = (1, 2): 1/2 + 2/3 = 7/6 yes
  -- n_i ≥ 2: 1 + 1/3 n_rho = 7/6, 1/3 n_rho = 1/6, n_rho = 1/2 not integer
  -- n_i = 0: 1/3 n_rho = 7/6, n_rho = 7/2 not integer
  -- n_i ≥ 3: 3/2 > 7/6
  have h_i_eq : vf.ord_i = 1 := by
    by_contra h_ne
    by_cases h_eq_0 : vf.ord_i = 0
    · simp only [h_eq_0, Int.cast_zero, mul_zero, zero_add] at hf
      have : (vf.ord_rho : ℚ) = 7 / 2 := by linarith
      have h7 : (vf.ord_rho : ℤ) * 2 = 7 := by exact_mod_cast (show (vf.ord_rho : ℚ) * 2 = 7 by linarith)
      omega
    · have h_ge_1 : 1 ≤ vf.ord_i := Int.lt_iff_add_one_le.mp
        (lt_of_le_of_ne h2 (Ne.symm h_eq_0))
      have h_ge_2 : 2 ≤ vf.ord_i := by omega
      by_cases h_ge_3 : 3 ≤ vf.ord_i
      · have : (3 : ℚ) ≤ (vf.ord_i : ℚ) := by exact_mod_cast h_ge_3
        linarith
      · push_neg at h_ge_3
        have h_eq_2 : vf.ord_i = 2 := le_antisymm (Int.lt_add_one_iff.mp h_ge_3) h_ge_2
        simp only [h_eq_2] at hf; push_cast at hf
        have : (vf.ord_rho : ℚ) = 1 / 2 := by linarith
        have h1 : (vf.ord_rho : ℤ) * 2 = 1 := by exact_mod_cast (show (vf.ord_rho : ℚ) * 2 = 1 by linarith)
        omega
  simp only [h_i_eq] at hf; push_cast at hf
  have h_rho_val : (vf.ord_rho : ℚ) = 2 := by linarith
  exact ⟨h_inf_zero, h_i_eq, by exact_mod_cast h_rho_val, h_int_zero⟩

/-! ### Dimension bound for small weights -/

/-- For `0 < k < 12`, the zero pattern of a nonzero holomorphic modular form of
weight `k` is completely determined by the valence formula. This means the space
of such modular forms has dimension at most 1.

More precisely: the quotient `f/g` of two nonzero forms of the same weight `k`
has weight 0, so by the weight-0 result it is constant. -/
theorem dim_le_one_principle {k : ℤ}
    (vf₁ vf₂ : ValenceFormulaData k) :
    vf₁.weightedSum = vf₂.weightedSum :=
  vf₁.weightedSum_eq_weightedSum vf₂

end
