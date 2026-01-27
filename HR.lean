/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e9e57f8d-2871-4ba3-b0d8-e451ab577961

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem smooth_crossing_opposite_values
    (γ : ℝ → ℂ) (t₀ : ℝ)
    (hγ_diff : DifferentiableAt ℝ γ t₀)
    (hγ_zero : γ t₀ = 0)
    (hγ'_ne : deriv γ t₀ ≠ 0)
    (hγ_ne : ∀ᶠ δ in 𝓝[>] 0, γ (t₀ - δ) ≠ 0 ∧ γ (t₀ + δ) ≠ 0) :
    Tendsto (fun δ => γ (t₀ - δ) / γ (t₀ + δ)) (𝓝[>] 0) (𝓝 (-1))

The following was negated by Aristotle:

- lemma log_ratio_tendsto_pi_I_of_ratio_tendsto_neg_one
    {f g : ℝ → ℂ} {l : Filter ℝ}
    (hf : ∀ᶠ t in l, f t ≠ 0)
    (hg : ∀ᶠ t in l, g t ≠ 0)
    (h_ratio : Tendsto (fun t => f t / g t) l (𝓝 (-1)))
    (h_approach : ∀ᶠ t in l, (f t / g t).im ≥ 0 ∨ (f t / g t).re > -1) :
    Tendsto (fun t => log (f t / g t)) l (𝓝 (I * Real.pi))

- theorem pv_smooth_crossing_contribution_eq_pi_I
    (γ : ℝ → ℂ) (t₀ : ℝ)
    (hγ_diff : DifferentiableAt ℝ γ t₀)
    (hγ_zero : γ t₀ = 0)
    (hγ'_ne : deriv γ t₀ ≠ 0)
    (hγ_ne : ∀ᶠ δ in 𝓝[>] 0, γ (t₀ - δ) ≠ 0 ∧ γ (t₀ + δ) ≠ 0) :
    Tendsto (fun δ => log (γ (t₀ - δ)) - log (γ (t₀ + δ))) (𝓝[>] 0) (𝓝 (I * Real.pi))

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
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousOn
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic


/-!
# Half-Residue Theorem and Principal Value Integrals

This file contains the half-residue theorem and supporting lemmas for computing
principal value integrals of 1/z along curves passing through the origin.

## Main Results

* `semicircle_integral_eq_pi_I` - The integral of 1/z over a semicircle = πI
* `smooth_crossing_opposite_values` - For smooth crossings, ratio → -1
* `log_ratio_smooth_crossing_tendsto_pi_I` - For smooth crossings, log(ratio) → πI

## Mathematical Background

The **half-residue theorem** states that for f(z) = 1/z, a semicircular arc
of radius r around the origin contributes πi to the contour integral.

**Proof sketch** (LibreTexts 10.6):
1. Parameterize: z = re^{iθ} for θ ∈ [0, π]
2. dz = ire^{iθ} dθ
3. ∫ (1/z) dz = ∫₀^π (1/re^{iθ}) · ire^{iθ} dθ = ∫₀^π i dθ = πi

This is independent of r, so the limit as r → 0 is πi.

## References

* Hungerbühler-Wasem, "Non-integer valued winding numbers", 2019
* LibreTexts 10.6, "Integrals over portions of circles"
-/

open Complex MeasureTheory Set Filter Topology

open scoped Real Interval

noncomputable section

/-! ## Semicircle Integrals -/

/-- Parameterization of an upper semicircle of radius r centered at 0.
    γ(θ) = r · e^{iθ} for θ ∈ [0, π] -/
def upperSemicircle (r : ℝ) : ℝ → ℂ := fun θ => r * exp (I * θ)

/-- The integrand 1/z · dz on the semicircle simplifies to i · dθ.

    This is the key calculation: (1/(re^{iθ})) · (ire^{iθ}) = i

    This result is independent of r and θ (for r ≠ 0). -/
lemma semicircle_integrand_eq_I (r : ℝ) (hr : r ≠ 0) (θ : ℝ) :
    (upperSemicircle r θ)⁻¹ * (I * r * exp (I * θ)) = I := by
  unfold upperSemicircle
  have h_exp_ne : exp (I * θ) ≠ 0 := exp_ne_zero _
  have h_ne : (r : ℂ) * exp (I * θ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, ofReal_eq_zero, h_exp_ne, or_false]
    exact hr
  have hr_ne : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  calc (↑r * exp (I * ↑θ))⁻¹ * (I * ↑r * exp (I * ↑θ))
      = (↑r)⁻¹ * (exp (I * ↑θ))⁻¹ * (I * ↑r * exp (I * ↑θ)) := by rw [mul_inv]
    _ = (↑r)⁻¹ * ↑r * ((exp (I * ↑θ))⁻¹ * exp (I * ↑θ)) * I := by ring
    _ = 1 * 1 * I := by rw [inv_mul_cancel₀ hr_ne, inv_mul_cancel₀ h_exp_ne]
    _ = I := by ring

/-- The integral of 1/z over an upper semicircle of radius r equals πi.

    ∫₀^π (1/z) dz = ∫₀^π i dθ = πi

    This is independent of r > 0 and is the half-residue theorem. -/
theorem semicircle_integral_eq_pi_I (r : ℝ) (hr : 0 < r) :
    ∫ θ in (0 : ℝ)..Real.pi, (upperSemicircle r θ)⁻¹ * (I * r * exp (I * θ)) =
    I * Real.pi := by
  have hr_ne : r ≠ 0 := ne_of_gt hr
  -- The integrand is constantly I
  have h_eq : ∀ θ : ℝ, (upperSemicircle r θ)⁻¹ * (I * r * exp (I * θ)) = I := fun θ =>
    semicircle_integrand_eq_I r hr_ne θ
  -- Integral of constant I from 0 to π
  simp only [h_eq]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero]
  -- π • I = I * π (smul vs mul for complex scalars)
  show (Real.pi : ℂ) * I = I * (Real.pi : ℂ)
  ring

/-- As the radius shrinks, the semicircle integral remains πi.

    This is the half-residue theorem: the contribution is independent of r. -/
theorem semicircle_integral_limit :
    Tendsto (fun r => ∫ θ in (0 : ℝ)..Real.pi,
      (upperSemicircle r θ)⁻¹ * (I * r * exp (I * θ)))
    (𝓝[>] 0) (𝓝 (I * Real.pi)) := by
  -- The integral equals I * π for all r > 0, so it's constant on Ioi 0
  have h_const : ∀ r : ℝ, 0 < r → (∫ θ in (0 : ℝ)..Real.pi,
      (upperSemicircle r θ)⁻¹ * (I * r * exp (I * θ))) = I * Real.pi :=
    fun r hr => semicircle_integral_eq_pi_I r hr
  -- A function that's eventually constant converges to that constant
  apply Tendsto.congr' _ tendsto_const_nhds
  rw [EventuallyEq]
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [mem_Ioi] at hr
  exact (h_const r hr).symm

/-! ## Log Ratio for Opposite Points -/

/-- log(-1) = πI (from mathlib, reformulated) -/
lemma log_neg_one_eq : log (-1 : ℂ) = I * Real.pi := by
  rw [Complex.log_neg_one]
  ring

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
The argument function is continuous at -1 when restricted to the upper half-plane.
-/
lemma continuousWithinAt_arg_neg_one_upper :
    ContinuousWithinAt Complex.arg {z : ℂ | 0 ≤ z.im} (-1) := by
      refine' tendsto_iff_norm_sub_tendsto_zero.mpr _;
      norm_num [ Complex.arg ];
      -- We'll use the fact that as $e$ approaches $-1$ from the upper half-plane, the argument of $e$ approaches $\pi$.
      have h_arg : Filter.Tendsto (fun e : ℂ => Real.arcsin (-e.im / ‖e‖) + Real.pi) (nhdsWithin (-1) {z : ℂ | 0 ≤ z.im}) (nhds (Real.arcsin (0) + Real.pi)) := by
        refine' Filter.Tendsto.add _ tendsto_const_nhds;
        refine' Real.continuous_arcsin.continuousAt.tendsto.comp _;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( ContinuousAt.tendsto ( show ContinuousAt ( fun e : ℂ => -e.im / ‖e‖ ) ( -1 ) from ContinuousAt.div ( ContinuousAt.neg ( Complex.continuous_im.continuousAt ) ) ( continuous_norm.continuousAt ) ( by norm_num ) ) |> fun h => h.trans ( by norm_num ) );
      field_simp;
      convert Filter.Tendsto.abs ( h_arg.sub_const Real.pi ) |> Filter.Tendsto.congr' _ using 2;
      · norm_num;
      · rw [ Filter.EventuallyEq, eventually_nhdsWithin_iff ] ; norm_num;
        rw [ Metric.eventually_nhds_iff ];
        refine' ⟨ 1 / 2, by norm_num, fun y hy hy' => _ ⟩ ; split_ifs <;> norm_num [ abs_of_nonneg, Real.pi_pos.le ];
        · norm_num [ Complex.dist_eq, Complex.normSq, Complex.norm_def ] at hy;
          rw [ Real.sqrt_lt' ] at hy <;> nlinarith;
        · rw [ ← abs_neg ] ; rw [ ← Real.arcsin_neg ] ; ring;

/-
The complex logarithm tends to -πi as z approaches -1 from the lower half-plane.
-/
lemma tendsto_log_nhdsWithin_im_neg :
    Tendsto log (nhdsWithin (-1) {z : ℂ | z.im < 0}) (𝓝 (-I * Real.pi)) := by
      have h_arg : Filter.Tendsto (fun z : ℂ => Complex.arg z) (𝓝[ { z : ℂ | z.im < 0 } ] (-1)) (𝓝 (-Real.pi)) := by
        -- The argument function is continuous at -1 when restricted to the lower half-plane.
        have h_arg_cont : Filter.Tendsto (fun z : ℂ => Complex.arg z) (𝓝[ { z : ℂ | z.im < 0 } ] (-1)) (𝓝 (-Real.pi)) := by
          have h_arg_neg : ∀ᶠ z in 𝓝[ { z : ℂ | z.im < 0 } ] (-1), Complex.arg z = -Real.pi + Complex.arg (z / -1) := by
            refine' Filter.eventually_of_mem self_mem_nhdsWithin fun z hz => _;
            norm_num [ Complex.arg ];
            split_ifs <;> simp_all +decide [ Complex.div_re, Complex.div_im ] <;> ring;
            any_goals linarith;
            norm_num [ show z.re = 0 by linarith, Complex.normSq, Complex.norm_def ] at *;
            rw [ Real.sqrt_mul_self_eq_abs, abs_of_neg hz ] ; ring ; norm_num [ Real.pi_pos.ne', hz.ne ];
            ring
          -- Since $z / -1 \to 1$ as $z \to -1$, we have $\arg(z / -1) \to \arg(1) = 0$.
          have h_arg_div_neg_one : Filter.Tendsto (fun z : ℂ => Complex.arg (z / -1)) (𝓝[ { z : ℂ | z.im < 0 } ] (-1)) (nhds 0) := by
            convert Filter.Tendsto.comp ( Complex.continuousAt_arg _ ) ( Filter.Tendsto.div_const ( Filter.tendsto_id.mono_left inf_le_left ) _ ) using 2 <;> norm_num;
          rw [ Filter.tendsto_congr' h_arg_neg ] ; simpa using h_arg_div_neg_one.const_add ( -Real.pi ) ;
        convert h_arg_cont using 1;
      rw [ tendsto_iff_norm_sub_tendsto_zero ] at *;
      simp_all +decide [ Complex.log, Complex.norm_def, Complex.normSq ];
      convert Filter.Tendsto.sqrt ( Filter.Tendsto.add ( Filter.Tendsto.mul ( Filter.Tendsto.log ( Filter.Tendsto.sqrt ( Filter.Tendsto.add ( Filter.Tendsto.mul ( Complex.continuous_re.continuousWithinAt ) ( Complex.continuous_re.continuousWithinAt ) ) ( Filter.Tendsto.mul ( Complex.continuous_im.continuousWithinAt ) ( Complex.continuous_im.continuousWithinAt ) ) ) ) _ ) ( Filter.Tendsto.log ( Filter.Tendsto.sqrt ( Filter.Tendsto.add ( Filter.Tendsto.mul ( Complex.continuous_re.continuousWithinAt ) ( Complex.continuous_re.continuousWithinAt ) ) ( Filter.Tendsto.mul ( Complex.continuous_im.continuousWithinAt ) ( Complex.continuous_im.continuousWithinAt ) ) ) ) _ ) ) ( h_arg.pow 2 ) ) using 2 <;> norm_num;
      grind

/-
Counterexample functions for the false lemma.
-/
def counterexample_f (t : ℝ) : ℂ := -1 + t - I * t
def counterexample_g (t : ℝ) : ℂ := 1

/-
πi is not equal to -πi.
-/
lemma pi_I_ne_neg_pi_I : I * Real.pi ≠ -I * Real.pi := by
  norm_num [ Complex.ext_iff, Real.pi_ne_zero ];
  linarith [ Real.pi_pos ]

/-
The ratio of the counterexample functions tends to -1 as t approaches 0 from the right.
-/
lemma counterexample_ratio_tendsto :
    Tendsto (fun t => counterexample_f t / counterexample_g t) (𝓝[>] 0) (𝓝 (-1)) := by
      refine' Filter.Tendsto.mono_left _ nhdsWithin_le_nhds;
      unfold counterexample_f counterexample_g; norm_num [ mul_comm ] ;
      exact Continuous.tendsto' ( by continuity ) _ _ ( by norm_num )

/-
The log of the counterexample ratio tends to -πi.
-/
lemma counterexample_limit :
  Tendsto (fun t => log (counterexample_f t / counterexample_g t)) (𝓝[>] 0) (𝓝 (-I * Real.pi)) := by
    convert tendsto_log_nhdsWithin_im_neg.comp _ using 2;
    refine' tendsto_nhdsWithin_iff.mpr _;
    unfold counterexample_f counterexample_g ; norm_num [ Complex.ext_iff ];
    exact ⟨ tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ), Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => hx ⟩

end AristotleLemmas

/-
For the ratio approaching -1, log(ratio) → πI.

    If z/w → -1 where z, w approach 0 from opposite directions along a line,
    then log(z/w) → log(-1) = πI.

    This is a key step in the half-residue theorem proof. The subtlety is that
    log is discontinuous at -1, but for ratios arising from smooth crossings,
    the approach is from a consistent direction that gives πI (not -πI).
-/
lemma log_ratio_tendsto_pi_I_of_ratio_tendsto_neg_one
    {f g : ℝ → ℂ} {l : Filter ℝ}
    (hf : ∀ᶠ t in l, f t ≠ 0)
    (hg : ∀ᶠ t in l, g t ≠ 0)
    (h_ratio : Tendsto (fun t => f t / g t) l (𝓝 (-1)))
    (h_approach : ∀ᶠ t in l, (f t / g t).im ≥ 0 ∨ (f t / g t).re > -1) :
    Tendsto (fun t => log (f t / g t)) l (𝓝 (I * Real.pi)) := by
  -- For ratios approaching -1 from above (positive imaginary part) or from the right,
  -- the log converges to πI.
  -- This follows from continuity of log on ℂ \ (-∞, 0] and the specific approach direction.
  rw [← log_neg_one_eq]
  -- The formal proof requires careful analysis of the branch cut.
  -- For the half-residue theorem application, the approach is always from above.
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose the counterexample functions $f(t) = -1 + t - i t$ and $g(t) = 1$.
  use counterexample_f, counterexample_g, nhdsWithin 0 (Set.Ioi 0);
  refine' ⟨ _, _, _, _, _ ⟩;
  · filter_upwards [ self_mem_nhdsWithin ] with t ht using by unfold counterexample_f; norm_num [ Complex.ext_iff ] ; aesop;
  · exact Filter.Eventually.of_forall fun t => one_ne_zero;
  · convert counterexample_ratio_tendsto using 1;
  · norm_num [ counterexample_f, counterexample_g ];
    exact Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => Or.inr ht;
  · intro H;
    convert absurd ( tendsto_nhds_unique H ( counterexample_limit ) ) _ using 1 ; norm_num [ Complex.ext_iff, Complex.log_re, Complex.log_im ];
    linarith [ Real.pi_pos ]

-/
/-- For the ratio approaching -1, log(ratio) → πI.

    If z/w → -1 where z, w approach 0 from opposite directions along a line,
    then log(z/w) → log(-1) = πI.

    This is a key step in the half-residue theorem proof. The subtlety is that
    log is discontinuous at -1, but for ratios arising from smooth crossings,
    the approach is from a consistent direction that gives πI (not -πI). -/
lemma log_ratio_tendsto_pi_I_of_ratio_tendsto_neg_one
    {f g : ℝ → ℂ} {l : Filter ℝ}
    (hf : ∀ᶠ t in l, f t ≠ 0)
    (hg : ∀ᶠ t in l, g t ≠ 0)
    (h_ratio : Tendsto (fun t => f t / g t) l (𝓝 (-1)))
    (h_approach : ∀ᶠ t in l, (f t / g t).im ≥ 0 ∨ (f t / g t).re > -1) :
    Tendsto (fun t => log (f t / g t)) l (𝓝 (I * Real.pi)) := by
  -- For ratios approaching -1 from above (positive imaginary part) or from the right,
  -- the log converges to πI.
  -- This follows from continuity of log on ℂ \ (-∞, 0] and the specific approach direction.
  rw [← log_neg_one_eq]
  -- The formal proof requires careful analysis of the branch cut.
  -- For the half-residue theorem application, the approach is always from above.
  sorry

/-! ## Smooth Crossing Principal Value -/

/-- For a curve γ passing smoothly through 0 at t₀, the values γ(t₀-δ) and γ(t₀+δ)
    are approximately opposite: γ(t₀-δ) ≈ -γ(t₀+δ) for small δ.

    More precisely, if γ(t₀) = 0 and γ'(t₀) = L ≠ 0:
    - γ(t₀ - δ) ≈ -δL
    - γ(t₀ + δ) ≈ +δL
    So γ(t₀ - δ) / γ(t₀ + δ) → -1 as δ → 0⁺ -/
theorem smooth_crossing_opposite_values
    (γ : ℝ → ℂ) (t₀ : ℝ)
    (hγ_diff : DifferentiableAt ℝ γ t₀)
    (hγ_zero : γ t₀ = 0)
    (hγ'_ne : deriv γ t₀ ≠ 0)
    (hγ_ne : ∀ᶠ δ in 𝓝[>] 0, γ (t₀ - δ) ≠ 0 ∧ γ (t₀ + δ) ≠ 0) :
    Tendsto (fun δ => γ (t₀ - δ) / γ (t₀ + δ)) (𝓝[>] 0) (𝓝 (-1)) := by
  -- Key: γ(t₀ ± δ) ≈ ±δ · γ'(t₀) for small δ
  -- So γ(t₀ - δ) / γ(t₀ + δ) ≈ (-δ · L) / (δ · L) = -1
  --
  -- The proof uses the derivative definition and limit arithmetic.
  -- This is the content of H-W Proposition 2.3, step 1.
  -- Apply the fact that the limit of a quotient is the quotient of the limits, provided the denominator does not tend to 0.
  have h_limit : Filter.Tendsto (fun δ => γ (t₀ - δ) / δ) (𝓝[>] 0) (𝓝 (-deriv γ t₀)) ∧ Filter.Tendsto (fun δ => γ (t₀ + δ) / δ) (𝓝[>] 0) (𝓝 (deriv γ t₀)) := by
    have := hγ_diff.hasDerivAt;
    rw [ hasDerivAt_iff_tendsto_slope_zero ] at this;
    constructor;
    · convert this.neg.comp ( show Filter.Tendsto ( fun δ : ℝ => -δ ) ( 𝓝[>] 0 ) ( 𝓝[≠] 0 ) from ?_ ) using 2 ; norm_num ; ring;
      · aesop;
      · rw [ Metric.tendsto_nhdsWithin_nhdsWithin ] ; aesop;
    · simpa [ div_eq_inv_mul, hγ_zero ] using this.comp ( show Filter.Tendsto ( fun δ : ℝ => δ ) ( 𝓝[>] 0 ) ( 𝓝[≠] 0 ) from Filter.tendsto_id.mono_left <| nhdsWithin_mono _ <| by simp +decide );
  have := h_limit.1.div h_limit.2;
  simpa [ hγ'_ne ] using this hγ'_ne |> fun h => h.congr' ( by filter_upwards [ self_mem_nhdsWithin ] with x hx using by rw [ Pi.div_apply, div_div_div_cancel_right₀ ( by aesop ) ] )

/- Aristotle took a wrong turn (reason code: 8). Please try again. -/
/-- The log of the ratio γ(t₀-δ)/γ(t₀+δ) tends to πI for smooth crossings.

    This follows from:
    1. The ratio → -1 (smooth_crossing_opposite_values)
    2. log(-1) = πI
    3. The approach direction ensures we get πI (not -πI)

    This is the mathematical content of H-W Proposition 2.3. -/
theorem log_ratio_smooth_crossing_tendsto_pi_I
    (γ : ℝ → ℂ) (t₀ : ℝ)
    (hγ_diff : DifferentiableAt ℝ γ t₀)
    (hγ_zero : γ t₀ = 0)
    (hγ'_ne : deriv γ t₀ ≠ 0)
    (hγ_ne : ∀ᶠ δ in 𝓝[>] 0, γ (t₀ - δ) ≠ 0 ∧ γ (t₀ + δ) ≠ 0) :
    Tendsto (fun δ => log (γ (t₀ - δ) / γ (t₀ + δ))) (𝓝[>] 0) (𝓝 (I * Real.pi)) := by
  -- Strategy: Use the half-residue theorem interpretation
  --
  -- For small δ:
  -- γ(t₀ - δ) ≈ -δL where L = γ'(t₀)
  -- γ(t₀ + δ) ≈ +δL
  --
  -- So log(γ(t₀-δ)/γ(t₀+δ)) = log(γ(t₀-δ)) - log(γ(t₀+δ))
  --                         ≈ log(-δL) - log(δL)
  --                         = [log|δL| + i·arg(-L)] - [log|δL| + i·arg(L)]
  --                         = i·(arg(-L) - arg(L))
  --
  -- For L not on the negative real axis: arg(-L) - arg(L) = ±π
  -- The half-residue theorem ensures we get +π for the PV interpretation.
  have h_ratio := smooth_crossing_opposite_values γ t₀ hγ_diff hγ_zero hγ'_ne hγ_ne
  rw [← log_neg_one_eq]
  -- The key insight: as the ratio → -1, if the approach is from the upper half-plane
  -- (or from the right of -1), then log(ratio) → log(-1) = πI.
  --
  -- For smooth crossings with γ'(t₀) = L, the ratio is approximately
  -- (-δL)/(δL) = -1, and the imaginary part of the ratio comes from
  -- higher-order terms that make it approach -1 from above.
  --
  -- The formal proof uses the specific structure of smooth crossings.
  sorry

/-! ## Key Consequence for Principal Value Integrals -/

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Counterexample curve γ(t) = -t.
Properties: differentiable, zero at 0, deriv = -1.
Limit of log difference is -πi.
-/
def bad_gamma (t : ℝ) : ℂ := -t

lemma log_neg_of_pos_real (r : ℝ) (hr : 0 < r) : log (-r) = log r + I * Real.pi := by
  norm_num [ Complex.log, Complex.arg, hr.ne' ] ; ring;
  split_ifs <;> simp_all +decide [ Complex.ext_iff ] ; linarith [ Real.pi_pos ];
  · linarith;
  · linarith

theorem bad_gamma_counterexample :
    Tendsto (fun δ => log (bad_gamma (0 - δ)) - log (bad_gamma (0 + δ)))
    (𝓝[>] 0) (𝓝 (-I * Real.pi)) := by
      unfold bad_gamma; norm_num [ Complex.log ] ; ring;
      norm_num [ Complex.arg, mul_comm ];
      exact tendsto_const_nhds.congr' ( by filter_upwards [ self_mem_nhdsWithin ] with x hx using by rw [ if_pos hx.out.le, if_neg hx.out.not_le ] ; norm_num )

/-
Disproof of the original theorem using the counterexample.
-/
theorem pv_smooth_crossing_contribution_eq_pi_I_false :
    ¬ (∀ (γ : ℝ → ℂ) (t₀ : ℝ),
       DifferentiableAt ℝ γ t₀ →
       γ t₀ = 0 →
       deriv γ t₀ ≠ 0 →
       (∀ᶠ δ in 𝓝[>] 0, γ (t₀ - δ) ≠ 0 ∧ γ (t₀ + δ) ≠ 0) →
       Tendsto (fun δ => log (γ (t₀ - δ)) - log (γ (t₀ + δ))) (𝓝[>] 0) (𝓝 (I * Real.pi))) := by
         push_neg;
         refine' ⟨ fun x => -x, 0, _, _, _, _, _ ⟩ <;> norm_num;
         · exact Complex.ofRealCLM.differentiableAt;
         · erw [ Complex.ofRealCLM.deriv ] ; norm_num;
         · exact Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => ne_of_gt hx;
         · -- For the counterexample, we show that the limit of the logarithmic difference is not $i\pi$.
           have h_log_diff : Filter.Tendsto (fun δ : ℝ => Complex.log (↑δ) - Complex.log (-↑δ)) (𝓝[>] 0) (𝓝 (-I * Real.pi)) := by
             convert bad_gamma_counterexample using 2 ; norm_num [ Complex.log ] ; ring;
             unfold bad_gamma; norm_num [ Complex.arg ] ; ring;
           intro H; have := tendsto_nhds_unique H h_log_diff; norm_num [ Complex.ext_iff ] at this; linarith [ Real.pi_pos ] ;

end AristotleLemmas

/-
For a smooth crossing at t₀, the principal value integral of 1/z equals πI.

    This is the main result connecting smooth crossings to the half-residue theorem.

    PV ∫_{t₀-δ}^{t₀+δ} γ'(t)/γ(t) dt = log(γ(t₀+δ)) - log(γ(t₀-δ)) → -πI

    So the excluded contribution (what we would add to get the full integral) is +πI.
-/
theorem pv_smooth_crossing_contribution_eq_pi_I
    (γ : ℝ → ℂ) (t₀ : ℝ)
    (hγ_diff : DifferentiableAt ℝ γ t₀)
    (hγ_zero : γ t₀ = 0)
    (hγ'_ne : deriv γ t₀ ≠ 0)
    (hγ_ne : ∀ᶠ δ in 𝓝[>] 0, γ (t₀ - δ) ≠ 0 ∧ γ (t₀ + δ) ≠ 0) :
    Tendsto (fun δ => log (γ (t₀ - δ)) - log (γ (t₀ + δ))) (𝓝[>] 0) (𝓝 (I * Real.pi)) := by
  -- This follows from log_ratio_smooth_crossing_tendsto_pi_I combined with
  -- the fact that for smooth crossings, the branch cut correction is zero
  -- (both arguments stay in the same half-plane).
  have h := log_ratio_smooth_crossing_tendsto_pi_I γ t₀ hγ_diff hγ_zero hγ'_ne hγ_ne
  -- The key observation: for smooth crossings, γ(t₀-δ) ≈ -δL and γ(t₀+δ) ≈ δL,
  -- so their arguments differ by approximately π, and the branch cut correction
  -- in log(z/w) = log(z) - log(w) + 2πi·k is k=0 for this specific approach.
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  refine' ⟨ fun t => -t, 0, _, _, _, _, _ ⟩ <;> norm_num;
  · exact Complex.ofRealCLM.differentiableAt;
  · erw [ Complex.ofRealCLM.deriv ] ; norm_num;
  · exact Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => ne_of_gt hx;
  · constructor;
    · refine' tendsto_const_nhds.congr' _;
      filter_upwards [ self_mem_nhdsWithin ] with x hx using by rw [ div_neg_self ( by norm_cast; linarith [ hx.out ] ) ] ; rw [ Complex.log_neg_one ] ; ring;
    · -- Let's simplify the expression inside the limit.
      have h_simplify : ∀ δ : ℝ, δ > 0 → Complex.log (δ : ℂ) - Complex.log (-(δ : ℂ)) = -Complex.I * Real.pi := by
        intro δ hδ; rw [ Complex.log, Complex.log ] ; norm_num [ Complex.ext_iff, Complex.log_re, Complex.log_im, hδ.ne' ] ;
        norm_num [ Complex.arg ];
        grind;
      rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ h_simplify x hx ] ) ] ; norm_num [ Complex.ext_iff, Real.pi_ne_zero ];
      linarith [ Real.pi_pos ]

-/
/-- For a smooth crossing at t₀, the principal value integral of 1/z equals πI.

    This is the main result connecting smooth crossings to the half-residue theorem.

    PV ∫_{t₀-δ}^{t₀+δ} γ'(t)/γ(t) dt = log(γ(t₀+δ)) - log(γ(t₀-δ)) → -πI

    So the excluded contribution (what we would add to get the full integral) is +πI.
-/
theorem pv_smooth_crossing_contribution_eq_pi_I
    (γ : ℝ → ℂ) (t₀ : ℝ)
    (hγ_diff : DifferentiableAt ℝ γ t₀)
    (hγ_zero : γ t₀ = 0)
    (hγ'_ne : deriv γ t₀ ≠ 0)
    (hγ_ne : ∀ᶠ δ in 𝓝[>] 0, γ (t₀ - δ) ≠ 0 ∧ γ (t₀ + δ) ≠ 0) :
    Tendsto (fun δ => log (γ (t₀ - δ)) - log (γ (t₀ + δ))) (𝓝[>] 0) (𝓝 (I * Real.pi)) := by
  -- This follows from log_ratio_smooth_crossing_tendsto_pi_I combined with
  -- the fact that for smooth crossings, the branch cut correction is zero
  -- (both arguments stay in the same half-plane).
  have h := log_ratio_smooth_crossing_tendsto_pi_I γ t₀ hγ_diff hγ_zero hγ'_ne hγ_ne
  -- The key observation: for smooth crossings, γ(t₀-δ) ≈ -δL and γ(t₀+δ) ≈ δL,
  -- so their arguments differ by approximately π, and the branch cut correction
  -- in log(z/w) = log(z) - log(w) + 2πi·k is k=0 for this specific approach.
  sorry

end