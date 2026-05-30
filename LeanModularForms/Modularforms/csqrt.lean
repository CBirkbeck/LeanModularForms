/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

@[expose] public section

/-!
# A complex square root via `exp ∘ (½ • log)`

We define a complex square root `csqrt` on the slit plane and record its derivative,
differentiability on the upper half-plane, and powers used in the theory of the modular
discriminant.
-/

open UpperHalfPlane Complex

/-- A complex square root on the slit plane, given by `cexp ((1 / 2) * log a)`. -/
noncomputable def csqrt : ℂ → ℂ := fun a : ℂ ↦ cexp ((1 / (2 : ℂ)) * log a)

/-- A point of the upper half-plane lies in the slit plane. -/
private lemma upperHalfPlane_mem_slitPlane (z : ℍ) : (z : ℂ) ∈ slitPlane :=
  mem_slitPlane_iff.mpr <| .inr (ne_of_lt z.2).symm

/-- The derivative of `csqrt` at `z` in the upper half-plane is `(2 z)⁻¹ • csqrt z⁻¹`. -/
lemma csqrt_deriv (z : ℍ) : deriv (fun a : ℂ ↦ cexp ((1 / (2 : ℂ)) * log a)) z =
    (2 : ℂ)⁻¹ • (fun a : ℂ ↦ cexp (-(1 / (2 : ℂ)) * log a)) z := by
  have hzz : (z : ℂ) ∈ slitPlane := upperHalfPlane_mem_slitPlane z
  have hcomp : (fun a ↦ cexp (1 / 2 * Complex.log a)) =
      cexp ∘ (fun a ↦ 1 / 2 * Complex.log a) := by ext; simp
  rw [hcomp, deriv_comp]
  · simp
    rw [Complex.exp_neg]
    field_simp
    have hsq : cexp (Complex.log (z : ℂ) / 2) ^ 2 = cexp (Complex.log (z : ℂ)) := by
      rw [← Complex.exp_nat_mul]; grind
    simpa [hsq, (Complex.hasDerivAt_log hzz).deriv, Complex.exp_log <| ne_zero z]
      using Complex.mul_inv_cancel <| ne_zero z
  · fun_prop
  · exact (Complex.differentiableAt_log hzz).const_mul _

/-- `csqrt` is differentiable at every point of the upper half-plane. -/
lemma csqrt_differentiableAt (z : ℍ) : DifferentiableAt ℂ csqrt z := by
  unfold csqrt
  exact ((Complex.differentiableAt_log (upperHalfPlane_mem_slitPlane z)).const_mul _).cexp

/-- `csqrt z ^ 24 = z ^ 12` for `z ≠ 0`. -/
lemma csqrt_pow_24 (z : ℂ) (hz : z ≠ 0) : (csqrt z) ^ 24 = z ^ 12 := by
  rw [csqrt, ← Complex.exp_nat_mul]
  have : ((24 : ℕ) : ℂ) * (1 / 2 * Complex.log z) = (12 : ℕ) * Complex.log z := by ring
  rw [this, Complex.exp_nat_mul, Complex.exp_log hz]

/-- `csqrt I ^ 24 = 1`. -/
lemma csqrt_I : (csqrt Complex.I) ^ 24 = 1 := by
  rw [csqrt_pow_24 _ I_ne_zero, show (12 : ℕ) = 4 * 3 from rfl, pow_mul,
    Complex.I_pow_four, one_pow]
