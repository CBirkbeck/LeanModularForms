/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cca8386d-97da-4bf9-97aa-1ff0ad99a81c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- lemma windingContribution_add (γ : ℝ → ℂ) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (hγ_ne_ac : ∀ t ∈ Icc a c, γ t ≠ 0) :
    let hγ_ne_ab : ∀ t ∈ Icc a b, γ t ≠ 0

- theorem integral_logDeriv_eq_liftedLogDiff
    (γ : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0) :
    ∫ t in a..b, deriv γ t / γ t = liftedLogDiff γ a b hγ_ne

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus


/-!
# Branch Cut Tracking for Complex Logarithm

This file develops the theory of "lifted logarithms" that track branch cuts
along paths. This is necessary for proving properties of integrals like
∫ γ'/γ = log γ(b) - log γ(a) when the path may cross the branch cut.

## Main Definitions

* `WindingContribution` - The 2πi correction from crossing the branch cut
* `liftedLogDiff` - log γ(b) - log γ(a) with winding correction
* `integral_logDeriv_eq_liftedLogDiff` - FTC with branch tracking

## Key Results

For a piecewise C¹ path γ : [a, b] → ℂ \ {0}:
* ∫_a^b γ'/γ = log γ(b) - log γ(a) + 2πi × (winding number of γ around 0)

For a closed path with γ(a) = γ(b):
* ∫_a^b γ'/γ = 2πi × (winding number of γ around 0)

## Mathematical Background

The complex logarithm log : ℂ \ {0} → ℂ has a branch cut along (-∞, 0].
When a path crosses this branch cut, the principal value log jumps by ±2πi.

For the integral ∫ γ'/γ:
- If γ crosses from upper to lower half-plane through (-∞, 0), add -2πi
- If γ crosses from lower to upper half-plane through (-∞, 0), add +2πi

The total correction is 2πi × (winding number of γ around 0).

## References

* Hungerbühler-Wasem: "Generalized Winding Numbers"
* Complex Analysis: The monodromy of complex logarithm
-/

open Complex MeasureTheory Set Filter Topology Metric Classical

open scoped Real Interval

noncomputable section

/-! ## Branch Cut Crossing Detection -/

/-- A point z is on the branch cut if z ∈ (-∞, 0]. -/
def onBranchCut (z : ℂ) : Prop := z.re ≤ 0 ∧ z.im = 0

/-- A path segment from z to w crosses the branch cut if:
    1. One of z, w has positive imaginary part and the other has negative
    2. The crossing point has negative real part -/
def crossesBranchCut (z w : ℂ) : Prop :=
  (z.im > 0 ∧ w.im < 0 ∧ ∃ t ∈ Ioo (0:ℝ) 1,
    let p := (1 - t) • z + t • w
    p.re < 0 ∧ p.im = 0) ∨
  (z.im < 0 ∧ w.im > 0 ∧ ∃ t ∈ Ioo (0:ℝ) 1,
    let p := (1 - t) • z + t • w
    p.re < 0 ∧ p.im = 0)

/-- The direction of crossing: +1 if crossing from lower to upper half-plane,
    -1 if crossing from upper to lower half-plane. -/
def branchCrossDirection (z w : ℂ) : ℤ :=
  if z.im < 0 ∧ w.im > 0 ∧ ∃ t ∈ Ioo (0:ℝ) 1,
      let p := (1 - t) • z + t • w
      p.re < 0 ∧ p.im = 0
  then 1
  else if z.im > 0 ∧ w.im < 0 ∧ ∃ t ∈ Ioo (0:ℝ) 1,
      let p := (1 - t) • z + t • w
      p.re < 0 ∧ p.im = 0
  then -1
  else 0

/-! ## Winding Number as Integer -/

/-- The winding number of a closed curve γ around 0, as an integer.
    For a piecewise linear approximation, this counts branch cut crossings. -/
def windingNumberInt (γ : ℝ → ℂ) (a b : ℝ) (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0)
    (hclosed : γ a = γ b) : ℤ := by
  -- This is the sum of branch crossing directions along the path
  -- For a rigorous definition, use the change in argument divided by 2π
  exact Int.floor ((Complex.arg (γ b) - Complex.arg (γ a)) / (2 * Real.pi) + 1/2)

/-- The winding contribution to the log integral is 2πi times the winding number. -/
def windingContribution (γ : ℝ → ℂ) (a b : ℝ) (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0) : ℂ :=
  2 * Real.pi * I * (⌊(Complex.arg (γ b) - Complex.arg (γ a)) / (2 * Real.pi)⌋ : ℂ)

/-! ## Lifted Logarithm Difference -/

/-- The "lifted" difference of logarithms, accounting for branch cut crossings.
    This equals log γ(b) - log γ(a) + 2πi × k where k is the winding correction. -/
def liftedLogDiff (γ : ℝ → ℂ) (a b : ℝ) (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0) : ℂ :=
  Complex.log (γ b) - Complex.log (γ a) + windingContribution γ a b hγ_ne

/-! ## Key Properties -/

/-- For a closed curve, the lifted log difference is 2πi × (winding number). -/
lemma liftedLogDiff_closed (γ : ℝ → ℂ) (a b : ℝ) (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0)
    (hclosed : γ a = γ b) :
    liftedLogDiff γ a b hγ_ne = windingContribution γ a b hγ_ne := by
  simp only [liftedLogDiff, hclosed, sub_self, zero_add]

/- Aristotle failed to find a proof. -/
/-- For a path that doesn't wind around 0, the winding contribution is 0. -/
lemma windingContribution_zero_of_no_winding (γ : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (h_no_wind : ∀ t ∈ Icc a b, γ t ∈ Complex.slitPlane) :
    windingContribution γ a b hγ_ne = 0 := by
  -- If the path stays in slitPlane, the argument change is less than 2π
  -- so the floor is 0
  simp only [windingContribution]
  have h_a : γ a ∈ Complex.slitPlane := h_no_wind a (left_mem_Icc.mpr hab)
  have h_b : γ b ∈ Complex.slitPlane := h_no_wind b (right_mem_Icc.mpr hab)
  -- In slitPlane, arg is in (-π, π), so |arg(γ b) - arg(γ a)| < 2π
  -- and the floor of the normalized difference is 0
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Additivity of winding contribution over adjacent intervals.
-/
lemma windingContribution_add (γ : ℝ → ℂ) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (hγ_ne_ac : ∀ t ∈ Icc a c, γ t ≠ 0) :
    let hγ_ne_ab : ∀ t ∈ Icc a b, γ t ≠ 0 := fun t ht => hγ_ne_ac t ⟨ht.1, ht.2.trans hbc⟩
    let hγ_ne_bc : ∀ t ∈ Icc b c, γ t ≠ 0 := fun t ht => hγ_ne_ac t ⟨hab.trans ht.1, ht.2⟩
    windingContribution γ a c hγ_ne_ac =
      windingContribution γ a b hγ_ne_ab + windingContribution γ b c hγ_ne_bc := by
  -- The winding contribution is based on arg changes, which are additive
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the path γ(t) = e^(it) for t in [0, 2π].
  use fun t : ℝ => Complex.exp (t * Complex.I), 0, Real.pi, 2 * Real.pi;
  refine' ⟨ Real.pi_pos.le, by linarith [ Real.pi_pos ], _, _ ⟩ <;> norm_num [ windingContribution ];
  -- Simplify the expression for the winding contribution.
  ring_nf at *; norm_num [ Real.pi_ne_zero ] at *

-/
/-- Additivity of winding contribution over adjacent intervals. -/
lemma windingContribution_add (γ : ℝ → ℂ) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (hγ_ne_ac : ∀ t ∈ Icc a c, γ t ≠ 0) :
    let hγ_ne_ab : ∀ t ∈ Icc a b, γ t ≠ 0 := fun t ht => hγ_ne_ac t ⟨ht.1, ht.2.trans hbc⟩
    let hγ_ne_bc : ∀ t ∈ Icc b c, γ t ≠ 0 := fun t ht => hγ_ne_ac t ⟨hab.trans ht.1, ht.2⟩
    windingContribution γ a c hγ_ne_ac =
      windingContribution γ a b hγ_ne_ab + windingContribution γ b c hγ_ne_bc := by
  -- The winding contribution is based on arg changes, which are additive
  sorry

/-! ## FTC with Branch Tracking -/

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
**Fundamental Theorem of Calculus for log integrals with branch tracking.**

    For a piecewise C¹ path γ : [a, b] → ℂ \ {0}, we have:
    ∫_a^b γ'/γ = liftedLogDiff γ a b

    This is the key result that relates the integral to log differences
    while accounting for branch cut crossings.
-/
theorem integral_logDeriv_eq_liftedLogDiff
    (γ : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0) :
    ∫ t in a..b, deriv γ t / γ t = liftedLogDiff γ a b hγ_ne := by
  -- The proof proceeds by:
  -- 1. Breaking the path into segments that don't cross the branch cut
  -- 2. On each segment, applying FTC (since we're in slitPlane)
  -- 3. Accounting for the 2πi jumps at branch crossings
  -- 4. Summing up to get the total
  have := @liftedLogDiff_closed;
  specialize this ( fun t => Complex.exp ( t * Complex.I ) ) 0 ( 2 * Real.pi ) ; norm_num [ Complex.exp_ne_zero ] at this;
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  refine' ⟨ fun t => Complex.exp ( t * Complex.I ), 0, 2 * Real.pi, _, _, _, _, _ ⟩ <;> norm_num [ Complex.exp_ne_zero ];
  · positivity;
  · fun_prop;
  · exact fun t ht₁ ht₂ => Complex.differentiableAt_exp.comp t ( differentiableAt_id.smul_const Complex.I );
  · unfold liftedLogDiff windingContribution; norm_num [ Complex.exp_ne_zero, Complex.differentiableAt_exp ] ; ring_nf ;
    -- Let's simplify the integral.
    have h_integral : ∫ t in (0 : ℝ)..Real.pi * 2, deriv (fun t : ℝ => Complex.exp (t * Complex.I)) t * (Complex.exp (Complex.I * t))⁻¹ = ∫ t in (0 : ℝ)..Real.pi * 2, Complex.I := by
      refine' intervalIntegral.integral_congr fun t ht => _;
      rw [ show deriv ( fun t : ℝ => cexp ( t * Complex.I ) ) t = Complex.I * cexp ( t * Complex.I ) by simpa [ mul_comm ] using HasDerivAt.deriv ( HasDerivAt.comp t ( Complex.hasDerivAt_exp _ ) ( hasDerivAt_id t |> HasDerivAt.smul_const <| Complex.I ) ) ] ; ring ; norm_num [ Complex.exp_ne_zero ] ;
    norm_num [ h_integral, Real.pi_ne_zero ]

-/
/-- **Fundamental Theorem of Calculus for log integrals with branch tracking.**

    For a piecewise C¹ path γ : [a, b] → ℂ \ {0}, we have:
    ∫_a^b γ'/γ = liftedLogDiff γ a b

    This is the key result that relates the integral to log differences
    while accounting for branch cut crossings. -/
theorem integral_logDeriv_eq_liftedLogDiff
    (γ : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0) :
    ∫ t in a..b, deriv γ t / γ t = liftedLogDiff γ a b hγ_ne := by
  -- The proof proceeds by:
  -- 1. Breaking the path into segments that don't cross the branch cut
  -- 2. On each segment, applying FTC (since we're in slitPlane)
  -- 3. Accounting for the 2πi jumps at branch crossings
  -- 4. Summing up to get the total
  sorry

/-- For closed curves, the integral of γ'/γ equals the winding contribution. -/
theorem integral_logDeriv_closed_eq_winding
    (γ : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0)
    (hclosed : γ a = γ b) :
    ∫ t in a..b, deriv γ t / γ t = windingContribution γ a b hγ_ne := by
  rw [integral_logDeriv_eq_liftedLogDiff γ a b hab hγ_cont hγ_diff hγ_ne]
  exact liftedLogDiff_closed γ a b hγ_ne hclosed

/-- For closed curves that don't wind around 0, the integral is 0. -/
theorem integral_logDeriv_closed_zero
    (γ : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0)
    (hclosed : γ a = γ b)
    (h_no_wind : ∀ t ∈ Icc a b, γ t ∈ Complex.slitPlane) :
    ∫ t in a..b, deriv γ t / γ t = 0 := by
  rw [integral_logDeriv_closed_eq_winding γ a b hab hγ_cont hγ_diff hγ_ne hclosed]
  exact windingContribution_zero_of_no_winding γ a b hab hγ_ne hγ_cont h_no_wind

/-! ## Application to Single Crossing -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `integral_logDeriv_eq_liftedLogDiff`
No goals to be solved
Unknown identifier `integral_logDeriv_eq_liftedLogDiff`
No goals to be solved-/
/-- For a closed curve with a single crossing at t₀, excluding a δ-neighborhood,
    the sum of integrals equals the log difference at the boundary.

    This is the key result for `integral_logDeriv_closed_single_crossing`. -/
theorem integral_logDeriv_closed_single_crossing_eq
    (γ : ℝ → ℂ) (a b t₀ : ℝ) (hab : a < b) (ht₀ : t₀ ∈ Ioo a b)
    (hclosed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, t ≠ t₀ → DifferentiableAt ℝ γ t)
    (hγ_ne : ∀ t ∈ Icc a b, t ≠ t₀ → γ t ≠ 0)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_small : t₀ - δ > a ∧ t₀ + δ < b)
    -- Key condition: the path from a to t₀-δ and from t₀+δ to b
    -- together don't wind around 0 (they form an "almost closed" path)
    (h_no_extra_wind : windingContribution γ a (t₀ - δ)
        (fun t ht => hγ_ne t ⟨ht.1, ht.2.trans (by linarith : t₀ - δ ≤ b)⟩ (by linarith [ht.2])) +
      windingContribution γ (t₀ + δ) b
        (fun t ht => hγ_ne t ⟨(by linarith : a ≤ t₀ + δ).trans ht.1, ht.2⟩ (by linarith [ht.1])) = 0) :
    ∫ t in a..(t₀ - δ), deriv γ t / γ t + ∫ t in (t₀ + δ)..b, deriv γ t / γ t =
    Complex.log (γ (t₀ - δ)) - Complex.log (γ (t₀ + δ)) := by
  -- Use integral_logDeriv_eq_liftedLogDiff for each segment
  have ha_le : a ≤ t₀ - δ := le_of_lt hδ_small.1
  have hb_ge : t₀ + δ ≤ b := le_of_lt hδ_small.2

  have hγ_ne1 : ∀ t ∈ Icc a (t₀ - δ), γ t ≠ 0 := fun t ht =>
    hγ_ne t ⟨ht.1, ht.2.trans (by linarith : t₀ - δ ≤ b)⟩ (by linarith [ht.2])
  have hγ_ne2 : ∀ t ∈ Icc (t₀ + δ) b, γ t ≠ 0 := fun t ht =>
    hγ_ne t ⟨(by linarith : a ≤ t₀ + δ).trans ht.1, ht.2⟩ (by linarith [ht.1])

  have h1 : ∫ t in a..(t₀ - δ), deriv γ t / γ t = liftedLogDiff γ a (t₀ - δ) hγ_ne1 := by
    apply integral_logDeriv_eq_liftedLogDiff
    · exact ha_le
    · exact hγ_cont.mono (Icc_subset_Icc_right (by linarith))
    · intro t ht
      exact hγ_diff t ⟨ht.1, by linarith [ht.2]⟩ (by linarith [ht.2])

  have h2 : ∫ t in (t₀ + δ)..b, deriv γ t / γ t = liftedLogDiff γ (t₀ + δ) b hγ_ne2 := by
    apply integral_logDeriv_eq_liftedLogDiff
    · exact hb_ge
    · exact hγ_cont.mono (Icc_subset_Icc_left (by linarith))
    · intro t ht
      exact hγ_diff t ⟨by linarith [ht.1], ht.2⟩ (by linarith [ht.1])

  -- Apply h1 and h2 using substitution
  -- Note: direct rw fails due to Lean 4 interval integral elaboration quirks
  -- so we use a calculation approach
  -- The winding contributions cancel by h_no_extra_wind
  -- And log γ(a) = log γ(b) by hclosed
  have h_log_eq : Complex.log (γ a) = Complex.log (γ b) := by rw [hclosed]
  have hwind_eq1 : windingContribution γ a (t₀ - δ)
      (fun t ht => hγ_ne t ⟨ht.1, ht.2.trans (by linarith : t₀ - δ ≤ b)⟩ (by linarith [ht.2])) =
      windingContribution γ a (t₀ - δ) hγ_ne1 := rfl
  have hwind_eq2 : windingContribution γ (t₀ + δ) b
      (fun t ht => hγ_ne t ⟨(by linarith : a ≤ t₀ + δ).trans ht.1, ht.2⟩ (by linarith [ht.1])) =
      windingContribution γ (t₀ + δ) b hγ_ne2 := rfl
  have h_no_extra_wind' : windingContribution γ a (t₀ - δ) hγ_ne1 +
      windingContribution γ (t₀ + δ) b hγ_ne2 = 0 := by
    rw [← hwind_eq1, ← hwind_eq2]; exact h_no_extra_wind
  -- Apply the FTC results and simplify
  -- First step: apply h1 and h2 which say:
  --   ∫ ... = liftedLogDiff γ a (t₀ - δ) hγ_ne1  (by h1)
  --   ∫ ... = liftedLogDiff γ (t₀ + δ) b hγ_ne2  (by h2)
  -- Then expand liftedLogDiff and simplify
  calc ∫ t in a..(t₀ - δ), deriv γ t / γ t + ∫ t in (t₀ + δ)..b, deriv γ t / γ t
      = liftedLogDiff γ a (t₀ - δ) hγ_ne1 + liftedLogDiff γ (t₀ + δ) b hγ_ne2 := by
        -- TODO: Resolve Lean 4 interval integral elaboration quirks
        -- h1 and h2 give us exactly this, but rw/simp can't match
        sorry
    _ = (Complex.log (γ (t₀ - δ)) - Complex.log (γ a) + windingContribution γ a (t₀ - δ) hγ_ne1) +
        (Complex.log (γ b) - Complex.log (γ (t₀ + δ)) + windingContribution γ (t₀ + δ) b hγ_ne2) := by
        simp only [liftedLogDiff]
    _ = Complex.log (γ (t₀ - δ)) - Complex.log (γ (t₀ + δ)) +
        (Complex.log (γ b) - Complex.log (γ a)) +
        (windingContribution γ a (t₀ - δ) hγ_ne1 + windingContribution γ (t₀ + δ) b hγ_ne2) := by ring
    _ = Complex.log (γ (t₀ - δ)) - Complex.log (γ (t₀ + δ)) + 0 + 0 := by
        rw [h_log_eq, sub_self, h_no_extra_wind']
    _ = Complex.log (γ (t₀ - δ)) - Complex.log (γ (t₀ + δ)) := by ring

end