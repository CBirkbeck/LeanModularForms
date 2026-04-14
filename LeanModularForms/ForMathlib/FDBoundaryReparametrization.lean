/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDBoundary
import LeanModularForms.ValenceFormula.Boundary.Basic

/-!
# Bridge: `fdBoundaryFun` ↔ `fdBoundary_H`

This file establishes the reparametrization bridge between:
- `fdBoundaryFun H : ℝ → ℂ` parametrized on `[0, 1]` (ForMathlib chain)
- `fdBoundary_H H : ℝ → ℂ` parametrized on `[0, 5]` (old ValenceFormula chain)

The bridge is simply `u = 5*t`: `fdBoundaryFun H t = fdBoundary_H H (5*t)`.

This is used to bridge residue/modular side Tendsto results between the two
chains until the residue side is fully ported to the ForMathlib chain.

## Main results

* `fdBoundaryFun_eq_fdBoundary_H_scaled` — the key reparametrization identity
* `fdBoundaryFun_eq_comp` — the equation as a function composition
* `fdBoundaryFun_integral_eq_fdBoundary_H_integral` — integral change of variables
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

/-- The ForMathlib `fdBoundaryFun` is the old-chain `fdBoundary_H` after
reparametrization `t ↦ 5t`. -/
theorem fdBoundaryFun_eq_fdBoundary_H_scaled (H : ℝ) (t : ℝ) :
    fdBoundaryFun H t = fdBoundary_H H (5 * t) := by
  unfold fdBoundaryFun fdBoundary_H
  by_cases h1 : t ≤ 1/5
  · have h1' : 5 * t ≤ 1 := by linarith
    simp only [h1, h1', ite_true]
    push_cast; ring
  · have h1' : ¬ (5 * t ≤ 1) := by push Not at h1; linarith
    by_cases h2 : t ≤ 2/5
    · have h2' : 5 * t ≤ 2 := by linarith
      simp only [h1, h2, h1', h2', ite_true, ite_false]
      congr 1; push_cast; ring
    · have h2' : ¬ (5 * t ≤ 2) := by push Not at h2; linarith
      by_cases h3 : t ≤ 3/5
      · have h3' : 5 * t ≤ 3 := by linarith
        simp only [h1, h2, h3, h1', h2', h3', ite_true, ite_false]
        congr 1; push_cast; ring
      · have h3' : ¬ (5 * t ≤ 3) := by push Not at h3; linarith
        by_cases h4 : t ≤ 4/5
        · have h4' : 5 * t ≤ 4 := by linarith
          simp only [h1, h2, h3, h4, h1', h2', h3', h4', ite_true, ite_false]
          push_cast; ring
        · have h4' : ¬ (5 * t ≤ 4) := by push Not at h4; linarith
          simp only [h1, h2, h3, h4, h1', h2', h3', h4', ite_false]
          push_cast; ring

/-- As a function composition identity. -/
theorem fdBoundaryFun_eq_comp (H : ℝ) :
    fdBoundaryFun H = fun t => fdBoundary_H H (5 * t) :=
  funext (fdBoundaryFun_eq_fdBoundary_H_scaled H)

/-! ### Integral change of variables for `[0, 1] ↔ [0, 5]` -/

/-- Linear change-of-variable identity:
`∫_{0}^{5} F u du = 5 * ∫_{0}^{1} F(5t) dt`.

This is a specialization of `intervalIntegral.smul_integral_comp_mul_add`
with `c = 5, d = 0, a = 0, b = 1`. -/
theorem integral_zero_to_five_eq_five_smul_zero_to_one (F : ℝ → ℂ) :
    ∫ u in (0 : ℝ)..5, F u = (5 : ℝ) • ∫ t in (0 : ℝ)..1, F (5 * t) := by
  have h := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1) F
    (5 : ℝ) (0 : ℝ)
  simp only [add_zero, mul_zero, mul_one] at h
  exact h.symm

end
