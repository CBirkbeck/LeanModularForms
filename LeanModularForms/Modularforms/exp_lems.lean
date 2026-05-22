/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# Exponential bounds on the upper half-plane

For `z : ℍ` and `n : ℕ`, the exponentials `exp (2π i z)` and `exp (2π i (n+1) z)` have
modulus strictly less than `1`, and `exp (2π i n z)` is invariant under `z ↦ z + 1`.
-/

open UpperHalfPlane TopologicalSpace Set Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

theorem exp_upperHalfPlane_lt_one (z : ℍ) : ‖(Complex.exp (2 * ↑π * Complex.I * z))‖ < 1 := by
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, Complex.I_re,
    mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re, coe_im, zero_sub,
    Left.neg_neg_iff]
  positivity

theorem exp_upperHalfPlane_lt_one_nat (z : ℍ) (n : ℕ) :
    ‖(Complex.exp (2 * ↑π * Complex.I * (n + 1) * z))‖ < 1 := by
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, Complex.I_re,
    mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, add_re, natCast_re, one_re, add_im,
    natCast_im, one_im, coe_re, zero_add, coe_im, zero_sub, Left.neg_neg_iff]
  positivity

lemma exp_periodo (z : ℍ) (n : ℕ) :
    cexp (2 * ↑π * Complex.I * ↑↑n * (1 + ↑z)) = cexp (2 * ↑π * Complex.I * ↑↑n * ↑z) := by
  rw [mul_add]
  have := (exp_periodic.nat_mul n) (2 * π * Complex.I * n * z)
  rw [← this]; congr 1; ring
