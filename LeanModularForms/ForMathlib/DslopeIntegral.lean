/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# `dslope` as a parameter integral

For `f : ℂ → ℂ` differentiable on an open convex set `U` and `c, w ∈ U`, we have
the integral representation:

  `dslope f c w = ∫₀¹ deriv f (c + t • (w - c)) ∂t`

This is the fundamental theorem of calculus applied to `f` on the segment `[c, w] ⊆ U`.
The representation unifies the two cases in `dslope` (`c = w` giving `deriv f c`, and
`c ≠ w` giving the usual slope formula).

From this integral representation we deduce:

* Joint continuity of `(c, w) ↦ dslope f c w` on convex open sets

## Main results

* `dslope_eq_integral_deriv` — `dslope f c w = ∫₀¹ deriv f (c + t•(w-c))` on convex `U`
-/

open Set MeasureTheory Filter Topology intervalIntegral

noncomputable section

namespace Complex

variable {f : ℂ → ℂ}

set_option backward.isDefEq.respectTransparency false in
/-- The `dslope` integral representation on a convex open set: when `f` is
differentiable on `U` and both `c, w ∈ U` (so the segment `[c, w] ⊆ U`), then
`dslope f c w` equals the integral of the derivative of `f` along the segment. -/
theorem dslope_eq_integral_deriv {U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c w : ℂ} (hc : c ∈ U) (hw : w ∈ U) :
    dslope f c w = ∫ t in (0 : ℝ)..1, deriv f (c + t • (w - c)) := by
  have h_seg : ∀ t ∈ Icc (0 : ℝ) 1, c + t • (w - c) ∈ U := by
    intro t ht
    have h_eq : c + t • (w - c) = (1 - t) • c + t • w := by module
    rw [h_eq]
    exact hU hc hw (by linarith [ht.2]) ht.1 (by linarith)
  have h_deriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt f (deriv f (c + t • (w - c))) (c + t • (w - c)) := fun t ht =>
    ((hf (c + t • (w - c)) (h_seg t ht)).differentiableAt
      (hU_open.mem_nhds (h_seg t ht))).hasDerivAt
  have h_cont : ContinuousOn (fun t : ℝ => deriv f (c + t • (w - c))) (Icc (0 : ℝ) 1) := by
    have h1 : Continuous (fun t : ℝ => c + t • (w - c)) := by continuity
    have h2 : ContinuousOn (deriv f) U :=
      (hf.analyticOnNhd hU_open).deriv.continuousOn
    exact h2.comp h1.continuousOn h_seg
  have h_int := integral_unitInterval_deriv_eq_sub h_cont h_deriv
  have heq : c + (w - c) = w := by ring
  rw [heq] at h_int
  by_cases hwc : w = c
  · have h_const : ∀ t : ℝ, c + t • (w - c) = c := by
      intro t; rw [hwc]; simp
    simp_rw [h_const]
    rw [hwc, dslope_same, intervalIntegral.integral_const, sub_zero, one_smul]
  · have hne : w - c ≠ 0 := sub_ne_zero.mpr hwc
    have h_mul : (w - c) * ∫ t in (0 : ℝ)..1, deriv f (c + t • (w - c)) = f w - f c := by
      rw [← smul_eq_mul]; exact h_int
    rw [dslope_of_ne f hwc, slope_def_module, smul_eq_mul]
    rw [show (w - c)⁻¹ * (f w - f c) = ∫ t in (0 : ℝ)..1, deriv f (c + t • (w - c)) from ?_]
    rw [← h_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end Complex

end
