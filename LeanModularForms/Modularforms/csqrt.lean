module

public import Mathlib.Algebra.Group.NatPowAssoc
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

/-!
# A complex square-root via the principal logarithm

This file defines `csqrt`, the complex square-root branch obtained by composing the
principal branch of the complex logarithm with `(1/2) • ·` and then `cexp`. We record
its derivative on the upper half-plane and the identities `csqrt I ^ 24 = 1` and
`csqrt z ^ 24 = z ^ 12` (for `z ≠ 0`).

## Main definitions

* `csqrt`: the complex square-root branch `z ↦ exp ((log z) / 2)`.

## Main results

* `csqrt_deriv`: derivative of `csqrt` at a point of the upper half-plane.
* `csqrt_differentiableAt`: differentiability of `csqrt` at points of `ℍ`.
* `csqrt_pow_24`: `(csqrt z) ^ 24 = z ^ 12` whenever `z ≠ 0`.
-/

@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ArithmeticFunction

/-- The complex square-root branch defined via the principal logarithm:
`csqrt z = exp ((log z) / 2)`. -/
noncomputable def csqrt : ℂ → ℂ := fun a : ℂ => cexp ((1 / (2 : ℂ)) * log a)

lemma csqrt_deriv (z : ℍ) : deriv (fun a : ℂ => cexp ((1 / (2 : ℂ))* (log a))) z =
    (2 : ℂ)⁻¹ • (fun a : ℂ => cexp (-(1 / (2 : ℂ)) * (log a))) z:= by
  have : (fun a ↦ cexp (1 / 2 * Complex.log a)) = cexp ∘ (fun a ↦ (1 / 2 * Complex.log a)) := by
    ext z
    simp
  have hzz : ↑z ∈ slitPlane := by
    rw [@mem_slitPlane_iff]
    right
    have hz := z.2
    exact Ne.symm (ne_of_lt hz)
  rw [this, deriv_comp]
  · simp
    rw [Complex.exp_neg]
    field_simp
    have hsq : cexp (Complex.log (z : ℂ) / 2) ^ 2 = cexp (Complex.log (z : ℂ)) := by
      rw [← Complex.exp_nat_mul]; grind
    simpa [hsq, (Complex.hasDerivAt_log hzz).deriv, Complex.exp_log <| ne_zero z]
      using Complex.mul_inv_cancel <| ne_zero z
  · fun_prop
  · apply DifferentiableAt.const_mul
    refine Complex.differentiableAt_log hzz

lemma csqrt_differentiableAt (z : ℍ) : DifferentiableAt ℂ csqrt z := by
  unfold csqrt
  apply DifferentiableAt.cexp
  apply DifferentiableAt.const_mul
  apply Complex.differentiableAt_log
  rw [@mem_slitPlane_iff]
  right
  have hz := z.2
  exact Ne.symm (ne_of_lt hz)


lemma csqrt_I : (csqrt (Complex.I)) ^ 24 = 1 := by
  unfold csqrt
  rw [← Complex.exp_nat_mul]
  conv =>
    enter [1,1]
    rw [← mul_assoc]
    rw [show ((24 : ℕ) : ℂ) * (1 / 2) = (12 : ℕ) by
      field_simp; ring]
  rw [Complex.exp_nat_mul]
  rw [Complex.exp_log I_ne_zero]
  have hi4 := Complex.I_pow_four
  have : Complex.I ^ 12 = (.I ^ 4) ^ 3 := by rw [← @npow_mul]
  simp [this, hi4]

lemma csqrt_pow_24 (z : ℂ) (hz : z ≠ 0) : (csqrt z) ^ 24 = z ^ 12 := by
  unfold csqrt
  rw [← Complex.exp_nat_mul]
  conv =>
    enter [1,1]
    rw [← mul_assoc]
    rw [show ((24 : ℕ) : ℂ) * (1 / 2) = (12 : ℕ) by
      field_simp; ring]
  rw [Complex.exp_nat_mul, Complex.exp_log hz]
