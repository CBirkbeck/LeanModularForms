# GeneralizedResidueTheory/ArcCalculus.lean — Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/ArcCalculus.lean`
Lines: 115

Namespace: `ArcCalculus`.

## def/`unitArc`
- **Type**: `(θ₁ θ₂ a b t : ℝ) → ℂ`
- **What**: Unit-circle arc linearly parameterized on `[a,b]`, going from angle `θ₁` to `θ₂`: `t ↦ exp(i·(θ₁ + (t-a)/(b-a)·(θ₂-θ₁)))`.
- **How**: Direct definition `exp(↑(θ₁ + (t-a)/(b-a)·(θ₂-θ₁)) · I)`.
- **Hypotheses**: None (`a = b` degenerate case lives downstream).
- **Uses-from-project**: None (pure mathlib).
- **Used by**: `unitArc_norm`, `unitArc_at_start`, `unitArc_at_end`, `unitArc_continuous`, `unitArc_hasDerivAt`, `unitArc_angle_hasDerivAt` (this file); downstream arc winding/distance lemmas.
- **Visibility**: public
- **Lines**: 30–31

## theorem/`unitArc_norm`
- **Type**: `(θ₁ θ₂ a b t : ℝ) → ‖unitArc θ₁ θ₂ a b t‖ = 1`
- **What**: Points on the arc lie on the unit circle.
- **How**: `simp [unitArc, Complex.norm_exp_ofReal_mul_I]`.
- **Hypotheses**: None.
- **Uses-from-project**: `unitArc`.
- **Used by**: Downstream winding/distance proofs.
- **Visibility**: public
- **Lines**: 34–35

## theorem/`unitArc_at_start`
- **Type**: `(θ₁ θ₂ a b : ℝ) → unitArc θ₁ θ₂ a b a = exp(↑θ₁ · I)`
- **What**: Start of the arc is `e^{iθ₁}`.
- **How**: `simp [unitArc, sub_self, zero_div, zero_mul, add_zero]`.
- **Hypotheses**: None.
- **Uses-from-project**: `unitArc`.
- **Used by**: Downstream arc lemmas.
- **Visibility**: public
- **Lines**: 38–40

## theorem/`unitArc_at_end`
- **Type**: `(θ₁ θ₂ a b : ℝ) → a ≠ b → unitArc θ₁ θ₂ a b b = exp(↑θ₂ · I)`
- **What**: End of the arc is `e^{iθ₂}`.
- **How**: `simp [unitArc]; congr 1; push_cast; rw [div_self ⟨b-a ≠ 0⟩, one_mul]; ring`.
- **Hypotheses**: `a ≠ b`.
- **Uses-from-project**: `unitArc`.
- **Used by**: Downstream arc lemmas.
- **Visibility**: public
- **Lines**: 43–50

## theorem/`unitArc_continuous`
- **Type**: `(θ₁ θ₂ a b : ℝ) → Continuous (unitArc θ₁ θ₂ a b)`
- **What**: Continuity of the arc parameterization in `t`.
- **How**: `unfold unitArc; fun_prop`.
- **Hypotheses**: None.
- **Uses-from-project**: `unitArc`.
- **Used by**: Downstream arc lemmas.
- **Visibility**: public
- **Lines**: 53–55

## lemma/`unitArc_angle_hasDerivAt` (private)
- **Type**: `(θ₁ θ₂ a b t : ℝ) → b - a ≠ 0 → HasDerivAt (fun s ↦ θ₁ + (s - a)/(b - a)·(θ₂ - θ₁)) ((θ₂ - θ₁)/(b - a)) t`
- **What**: Derivative of the linear angle interpolation.
- **How**: Build `HasDerivAt (s ↦ (s-a)/(b-a)) (1/(b-a)) t` from `hasDerivAt_id`, `.sub_const`, `.div_const`; multiply by `(θ₂-θ₁)`; `field_simp` to clean; `const_add θ₁`.
- **Hypotheses**: `b - a ≠ 0`.
- **Uses-from-project**: None.
- **Used by**: `unitArc_hasDerivAt` (this file).
- **Visibility**: private
- **Lines**: 57–67

## theorem/`unitArc_hasDerivAt`
- **Type**: `(θ₁ θ₂ a b t : ℝ) → a < b → HasDerivAt (unitArc θ₁ θ₂ a b) (unitArc θ₁ θ₂ a b t · (↑((θ₂ - θ₁)/(b - a))·I)) t`
- **What**: Derivative of the unit arc parameterization.
- **How**: Apply `unitArc_angle_hasDerivAt`, lift to `ℂ` via `.ofReal_comp`, multiply by `I` via `.mul_const I`, compose with `exp` via `.cexp`; close with `convert` after `simp [unitArc]`.
- **Hypotheses**: `a < b`.
- **Uses-from-project**: `unitArc`, `unitArc_angle_hasDerivAt`.
- **Used by**: Downstream arc winding-number formulas.
- **Visibility**: public
- **Lines**: 70–79

## theorem/`exp_sub_norm_sq`
- **Type**: `(θ₁ θ₂ : ℝ) → ‖exp(↑θ₁·I) - exp(↑θ₂·I)‖² = 2 - 2·cos(θ₁ - θ₂)`
- **What**: Distance formula between two unit-circle points expressed as `2 - 2cos Δθ`.
- **How**: Rewrite `‖·‖² = normSq`; expand `Complex.exp_mul_I` and `normSq_apply`; `Real.cos_sub`; close with `nlinarith` using `sin²+cos²=1` (twice) and `sq_nonneg` of `cos θ₁ - cos θ₂`, `sin θ₁ - sin θ₂`.
- **Hypotheses**: None.
- **Uses-from-project**: None.
- **Used by**: Arc distance lemmas / half-angle bounds.
- **Visibility**: public
- **Lines**: 82–92

## theorem/`sin_pos_of_mem_Ioo_zero_pi`
- **Type**: `{θ : ℝ} → θ ∈ Ioo 0 π → 0 < Real.sin θ`
- **What**: Positivity of `sin` on the open interval `(0, π)`.
- **How**: `Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2`.
- **Hypotheses**: `θ ∈ Ioo 0 π`.
- **Uses-from-project**: None.
- **Used by**: Arc winding-direction lemmas.
- **Visibility**: public
- **Lines**: 95–96

## theorem/`abs_cos_le_half_of_mem_Icc`
- **Type**: `{θ : ℝ} → θ ∈ Icc (π/3) (2π/3) → |cos θ| ≤ 1/2`
- **What**: Bound `|cos θ| ≤ 1/2` for `θ ∈ [π/3, 2π/3]` (the arc-angle range).
- **How**: `rw [abs_le]`; two `Real.cos_le_cos_of_nonneg_of_le_pi` applications (one comparing to `cos(2π/3) = -cos(π/3)`, one to `cos(π/3)`); close each branch with `Real.cos_pi_div_three = 1/2` and `linarith`.
- **Hypotheses**: `θ ∈ Icc (π/3) (2π/3)`.
- **Uses-from-project**: None.
- **Used by**: Arc-distance lower-bound machinery for `ρ`, `ρ+1` crossings.
- **Visibility**: public
- **Lines**: 99–113

## File Summary
Self-contained mathlib-style API for unit-circle arc parameterizations, scoped in namespace `ArcCalculus`. Defines `unitArc θ₁ θ₂ a b t = exp(i·linear-interpolated-angle)` and proves: start/end values, continuity, derivative formula `arc · i · (Δθ/Δt)`, the cosine distance identity `‖e^{iθ₁} - e^{iθ₂}‖² = 2 − 2cos Δθ`, `sin > 0` on `(0,π)`, and `|cos| ≤ 1/2` on `[π/3, 2π/3]`. No project dependencies (single `import Mathlib`); used downstream by arc winding-weight and distance proofs at `i`, `ρ`, `ρ+1`.
