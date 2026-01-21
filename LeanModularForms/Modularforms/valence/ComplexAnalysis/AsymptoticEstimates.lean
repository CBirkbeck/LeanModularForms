/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Infrastructure.LHopital
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.LHopital

/-!
# Asymptotic Estimates for Winding Number Integrand

This file proves that the winding number integrand is bounded for piecewise C^{1,1}
immersions. The key estimates show:

* Numerator x·ẏ - y·ẋ = O((t - t₀)²) near a zero t₀
* Denominator x² + y² = Θ((t - t₀)²) near a zero (by immersion condition)
* Hence integrand = O(1), i.e., bounded

These estimates are crucial for showing the principal value integral exists.

## Main Results

* `numerator_big_O_squared` - The numerator is O(t²)
* `denominator_Theta_squared` - The denominator is Θ(t²)
* `windingNumberIntegrand_bounded` - The integrand is bounded
* `windingNumberIntegrand_limit` - The limit at a zero (for C² curves)

## References

* Standard calculus/asymptotic analysis
* No direct Isabelle parallel (Isabelle avoids singularities)
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Real Interval

noncomputable section

variable (γ : PiecewiseC1Immersion)

/-! ## The Winding Number Integrand -/

/-- The real integrand for winding number computation:
    (x·ẏ - y·ẋ)/(x² + y²) where γ(t) = x(t) + i·y(t)
-/
def windingNumberIntegrand (γ : ℝ → ℂ) (t : ℝ) : ℝ :=
  let z := γ t
  let z' := deriv γ t
  (z.re * z'.im - z.im * z'.re) / (z.re ^ 2 + z.im ^ 2)

/-! ## Helper Lemmas for CLM Derivatives -/

/-- The derivative of a ContinuousLinearMap composed with a function.
    For a CLM L : E →L[ℝ] F and differentiable f : ℝ → E, we have
    deriv (L ∘ f) t = L (deriv f t).

    Proof: Use fderiv chain rule. For f : ℝ → E, deriv f t = fderiv ℝ f t 1.
    fderiv (L ∘ f) t = (fderiv L (f t)).comp (fderiv f t) = L.comp (fderiv f t)
    So deriv (L ∘ f) t = (L.comp (fderiv f t)) 1 = L (fderiv f t 1) = L (deriv f t) -/
theorem ContinuousLinearMap.deriv_comp' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : ℝ → E} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) :
    deriv (L ∘ f) t = L (deriv f t) := by
  have hL : DifferentiableAt ℝ L (f t) := L.differentiableAt
  -- Use fderiv chain rule
  have h_fderiv : fderiv ℝ (L ∘ f) t = (fderiv ℝ L (f t)).comp (fderiv ℝ f t) :=
    fderiv_comp t hL hf
  -- fderiv ℝ L (f t) = L
  have h_fderiv_L : fderiv ℝ L (f t) = L := L.fderiv
  -- Now use deriv = fderiv 1
  calc deriv (L ∘ f) t = fderiv ℝ (L ∘ f) t 1 := by rw [fderiv_deriv]
    _ = (fderiv ℝ L (f t)).comp (fderiv ℝ f t) 1 := by rw [h_fderiv]
    _ = L.comp (fderiv ℝ f t) 1 := by rw [h_fderiv_L]
    _ = L (fderiv ℝ f t 1) := rfl
    _ = L (deriv f t) := by rw [← fderiv_deriv]

/-- deriv (reCLM ∘ f) = (deriv f).re when f is differentiable. -/
theorem deriv_re_comp_of_differentiable {f : ℝ → ℂ} {t : ℝ} (hf : DifferentiableAt ℝ f t) :
    deriv (Complex.re ∘ f) t = (deriv f t).re := by
  have h := Complex.reCLM.deriv_comp' hf
  simp only [Complex.reCLM_apply] at h
  exact h

/-- deriv (imCLM ∘ f) = (deriv f).im when f is differentiable. -/
theorem deriv_im_comp_of_differentiable {f : ℝ → ℂ} {t : ℝ} (hf : DifferentiableAt ℝ f t) :
    deriv (Complex.im ∘ f) t = (deriv f t).im := by
  have h := Complex.imCLM.deriv_comp' hf
  simp only [Complex.imCLM_apply] at h
  exact h

/-! ## Numerator Estimate: O(t²) -/

noncomputable section AristotleLemmas

/-
For a piecewise C1 immersion with Lipschitz derivative, the fundamental theorem of calculus holds: the integral of the derivative equals the difference of the function values.
-/
theorem integral_deriv_eq_sub_of_lipschitz (γ : PiecewiseC1Immersion)
    {K : NNReal} (hLip : LipschitzOnWith K (deriv γ.toFun) (Icc γ.a γ.b))
    {t₀ t : ℝ} (ht₀ : t₀ ∈ Icc γ.a γ.b) (ht : t ∈ Icc γ.a γ.b) :
    ∫ s in t₀..t, deriv γ.toFun s = γ.toFun t - γ.toFun t₀ := by
  rw [ intervalIntegral.integral_eq_sub_of_hasDeriv_right ];
  · exact γ.continuous_toFun.mono ( Set.Icc_subset_Icc ( by aesop ) ( by aesop ) );
  · intro x hx;
    by_cases hx' : x ∈ γ.partition <;> simp_all +decide [ hasDerivWithinAt_univ ];
    · -- Since γ is a piecewise C1 immersion, its derivative exists everywhere except possibly at the partition points. But here, x is in the partition, so we need to use the fact that the derivative is continuous at x.
      have h_deriv_cont : ContinuousAt (deriv γ.toFun) x := by
        exact hLip.continuousOn.continuousAt ( Icc_mem_nhds ( by cases hx.1 <;> cases hx.2 <;> linarith ) ( by cases hx.1 <;> cases hx.2 <;> linarith ) );
      have h_deriv_exists : DifferentiableAt ℝ γ.toFun x := by
        have h_deriv_exists : ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv γ.toFun) (𝓝[<] x) (𝓝 L) := by
          have := γ.left_deriv_limit x hx';
          exact this ( lt_of_le_of_ne ( by cases hx.1 <;> cases hx.2 <;> linarith ) ( Ne.symm <| by cases hx.1 <;> cases hx.2 <;> rintro rfl <;> linarith ) );
        obtain ⟨ L, hL_ne_zero, hL_tendsto ⟩ := h_deriv_exists;
        have h_deriv_exists : Filter.Tendsto (deriv γ.toFun) (𝓝 x) (𝓝 L) := by
          convert h_deriv_cont.tendsto using 1;
          exact tendsto_nhds_unique hL_tendsto ( h_deriv_cont.mono_left inf_le_left ) ▸ rfl;
        have := h_deriv_exists.eventually_ne hL_ne_zero;
        exact differentiableAt_of_deriv_ne_zero ( this.self_of_nhds );
      exact h_deriv_exists.hasDerivAt.hasDerivWithinAt;
    · exact DifferentiableAt.hasDerivAt ( γ.smooth_off_partition x ⟨ by cases hx.1 <;> linarith, by cases hx.2 <;> linarith ⟩ hx' ) |> HasDerivAt.hasDerivWithinAt;
  · apply_rules [ ContinuousOn.intervalIntegrable ];
    exact hLip.continuousOn.mono ( by intro x hx; constructor <;> cases Set.mem_uIcc.mp hx <;> linarith [ ht₀.1, ht₀.2, ht.1, ht.2 ] )

/-
The absolute value of the integral of `|s - t₀|` from `t₀` to `t` is `(t - t₀)² / 2`.
-/
lemma abs_intervalIntegral_abs_sub_eq_sq_div_two (t₀ t : ℝ) :
    abs (∫ s in t₀..t, |s - t₀|) = (t - t₀) ^ 2 / 2 := by
  cases le_total t t₀ <;> simp_all +decide [ intervalIntegral.integral_comp_sub_right, sq_abs ];
  · rw [ intervalIntegral.integral_congr fun x hx => abs_of_nonpos ( by cases Set.mem_uIcc.mp hx <;> linarith ) ] ; ring;
    rw [ intervalIntegral.integral_neg ] ; norm_num ; ring;
    rw [ intervalIntegral.integral_symm ] ; norm_num ; ring;
    rw [ intervalIntegral.integral_of_le ] <;> norm_num ; ring ; norm_num [ abs_of_nonneg, ‹_› ];
    · rw [ ← intervalIntegral.integral_of_le ] <;> norm_num <;> try linarith;
      rw [ intervalIntegral.integral_deriv_eq_sub' ] ; ring;
      rotate_left;
      exacts [ fun x => x ^ 2 / 2, funext fun x => by norm_num, fun x hx => by norm_num, continuousOn_id, by norm_num; rw [ abs_of_nonneg ] <;> nlinarith ];
    · linarith;
  · rw [ intervalIntegral.integral_congr fun x hx => abs_of_nonneg ( by aesop ) ] ; ring;
    rw [ intervalIntegral.integral_deriv_eq_sub' ] <;> norm_num ; ring;
    rotate_left;
    exacts [ fun x => x ^ 2 / 2, funext fun x => by norm_num, fun x hx => by norm_num, continuousOn_id, by norm_num; rw [ abs_of_nonneg ] <;> nlinarith ]

/-
If the derivative of a piecewise C¹ curve is Lipschitz with constant K, then the error of the first-order Taylor approximation is bounded by (K/2)(t-t₀)².
-/
theorem norm_sub_sub_deriv_le_of_lipschitz_deriv (γ : PiecewiseC1Immersion)
    {K : NNReal} (hLip : LipschitzOnWith K (deriv γ.toFun) (Icc γ.a γ.b))
    {t₀ t : ℝ} (ht₀ : t₀ ∈ Icc γ.a γ.b) (ht : t ∈ Icc γ.a γ.b) :
    ‖γ.toFun t - γ.toFun t₀ - (t - t₀) • deriv γ.toFun t₀‖ ≤ K / 2 * (t - t₀) ^ 2 := by
  -- Use `integral_deriv_eq_sub_of_lipschitz` to replace `γ t - γ t₀` with `∫ s in t₀..t, deriv γ s`.
  have h_integral : ∫ s in t₀..t, deriv γ.toFun s = γ.toFun t - γ.toFun t₀ := by
    apply_rules [ integral_deriv_eq_sub_of_lipschitz ];
  -- Factor out `K`. The bound becomes `K * |∫ s in t₀..t, |s - t₀| ds|`.
  have h_factor : ‖∫ s in t₀..t, (deriv γ.toFun s - deriv γ.toFun t₀)‖ ≤ K * abs (∫ s in t₀..t, |s - t₀|) := by
    have h_factor : ∀ s ∈ Set.Icc (min t₀ t) (max t₀ t), ‖deriv γ.toFun s - deriv γ.toFun t₀‖ ≤ K * |s - t₀| := by
      intro s hs;
      exact hLip.norm_sub_le ( show s ∈ Set.Icc γ.a γ.b from by cases max_cases t₀ t <;> cases min_cases t₀ t <;> constructor <;> linarith [ hs.1, hs.2, ht₀.1, ht₀.2, ht.1, ht.2 ] ) ( show t₀ ∈ Set.Icc γ.a γ.b from by cases max_cases t₀ t <;> cases min_cases t₀ t <;> constructor <;> linarith [ hs.1, hs.2, ht₀.1, ht₀.2, ht.1, ht.2 ] );
    cases le_total t₀ t <;> simp_all +decide [ intervalIntegral ];
    · refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
      refine' fun x => K * |x - t₀|;
      · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
      · exact Continuous.integrableOn_Ioc ( by continuity );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using h_factor x hx.1.le hx.2;
      · rw [ MeasureTheory.integral_const_mul, abs_of_nonneg ( MeasureTheory.integral_nonneg fun x => abs_nonneg _ ) ];
    · refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
      refine' fun x => K * |x - t₀|;
      · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
      · exact Continuous.integrableOn_Ioc ( by continuity );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using h_factor x hx.1.le hx.2;
      · rw [ MeasureTheory.integral_const_mul, abs_of_nonneg ( MeasureTheory.integral_nonneg fun x => abs_nonneg _ ) ];
  convert h_factor using 1;
  · rw [ intervalIntegral.integral_sub ] <;> norm_num [ h_integral ];
    apply_rules [ ContinuousOn.intervalIntegrable ];
    exact hLip.continuousOn.mono ( Set.Icc_subset_Icc ( by aesop ) ( by aesop ) );
  · rw [ abs_intervalIntegral_abs_sub_eq_sq_div_two ] ; ring

end AristotleLemmas

theorem numerator_big_O_squared (t₀ : ℝ)
    (hγ_zero : γ.toFun t₀ = 0)
    (hLip : LipschitzOnWith 1 (deriv γ.toFun) (Icc γ.a γ.b)) :
    ∃ C > 0, ∀ t, |t - t₀| < 1 → t ∈ Icc γ.a γ.b →
      |(γ.toFun t).re * (deriv γ.toFun t).im -
       (γ.toFun t).im * (deriv γ.toFun t).re| ≤ C * (t - t₀)^2 := by
  -- The key insight is that x*y' - y*x' is O(h^2) due to cancellation of leading terms.
  -- Writing gamma(t) = h*v + e where v = gamma'(t0), h = t - t0, and |e| = O(h^2),
  -- and gamma'(t) = v + d where |d| = O(h), we get:
  -- x*y' - y*x' = h*(vx*dy - vy*dx) + ex*vy - ey*vx + ex*dy - ey*dx
  -- All remaining terms are O(h^2) since vx*vy - vy*vx = 0 cancels the leading h term.
  by_cases ht₀ : t₀ ∈ Icc γ.a γ.b
  · -- Get bound M on derivative norm
    have h_deriv_bdd : ∃ M > 0, ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M := by
      use ‖deriv γ.toFun t₀‖ + (γ.b - γ.a) + 1
      constructor
      · have h1 := norm_nonneg (deriv γ.toFun t₀); have h2 := γ.hab; linarith
      intro t ht
      have hLip_sub := hLip.norm_sub_le ht₀ ht
      simp only [NNReal.coe_one, one_mul] at hLip_sub
      have h_dist : ‖t₀ - t‖ ≤ γ.b - γ.a := by
        simp only [Real.norm_eq_abs]
        cases abs_cases (t₀ - t) <;> linarith [ht.1, ht.2, ht₀.1, ht₀.2]
      calc ‖deriv γ.toFun t‖
          = ‖deriv γ.toFun t - deriv γ.toFun t₀ + deriv γ.toFun t₀‖ := by ring_nf
        _ ≤ ‖deriv γ.toFun t - deriv γ.toFun t₀‖ + ‖deriv γ.toFun t₀‖ := norm_add_le _ _
        _ = ‖deriv γ.toFun t₀ - deriv γ.toFun t‖ + ‖deriv γ.toFun t₀‖ := by rw [norm_sub_rev]
        _ ≤ ‖t₀ - t‖ + ‖deriv γ.toFun t₀‖ := by linarith
        _ ≤ (γ.b - γ.a) + ‖deriv γ.toFun t₀‖ := by linarith
        _ ≤ ‖deriv γ.toFun t₀‖ + (γ.b - γ.a) + 1 := by linarith
    obtain ⟨M, hM_pos, hM⟩ := h_deriv_bdd
    -- Use C = 3*M + 1 as constant
    use 3 * M + 1
    constructor; linarith
    intro t ht_small ht_interval
    by_cases ht : t = t₀
    · -- At t = t0, both sides are 0
      subst ht
      simp only [hγ_zero, Complex.zero_re, Complex.zero_im, zero_mul, mul_zero,
                 sub_self, abs_zero, sq, mul_zero, le_refl]
    · -- For t ≠ t0, we use the Taylor expansion argument.
      --
      -- Mathematical outline (from comments above):
      -- Let h = t - t₀, v = γ'(t₀).
      -- By Lipschitz on γ' and FTC:
      --   γ(t) = ∫_{t₀}^t γ'(s) ds = h·v + ∫_{t₀}^t (γ'(s) - v) ds
      --   |∫_{t₀}^t (γ'(s) - v) ds| ≤ ∫_{t₀}^t |s - t₀| ds = h²/2
      --
      -- So γ(t) = h·v + e where |e| ≤ h²/2.
      -- Also γ'(t) = v + d where |d| ≤ |h| by Lipschitz.
      --
      -- Then x*y' - y*x' = Im((h·v + e) * conj(v + d))
      --                  = h·Im(v*conj(d)) + Im(e*conj(v)) + Im(e*conj(d))
      -- (since Im(h·|v|²) = 0 as h*|v|² is real)
      --
      -- Bounds:
      -- |h·Im(v*conj(d))| ≤ |h|·M·|h| = M·h²
      -- |Im(e*conj(v))| ≤ M·h²/2
      -- |Im(e*conj(d))| ≤ (h²/2)·|h| ≤ h²/2 (for |h| < 1)
      --
      -- Total: ≤ M·h² + M·h²/2 + h²/2 ≤ (3M/2 + 1/2)·h² ≤ (3M+1)·h²
      --
      -- The formalization of this argument requires:
      -- 1. FTC to express γ(t) as an integral
      -- 2. Integral bounds using Lipschitz condition
      -- 3. Algebraic manipulation of cross products
      --
      -- This is complex but mathematically straightforward. For now, we defer
      -- the full integration machinery.
      --
      -- Alternative direct approach: Use simple bounds without explicit integration.
      -- We bound the cross product x*y' - y*x' directly using:
      -- 1. |γ(t)| ≤ M*|t - t₀| (from Lipschitz on γ via bound on γ')
      -- 2. |γ'(t) - γ'(t₀)| ≤ |t - t₀| (from Lipschitz on γ')
      -- 3. The cross product structure allows quadratic cancellation
      --
      -- Key observation: x*y' - y*x' = Im(γ * conj(γ'))
      -- For γ = h*v + e (h = t-t₀, v = γ'(t₀), |e| ≤ M*h²) and γ' = v + d (|d| ≤ h):
      -- γ * conj(γ') = (h*v + e) * conj(v + d)
      --              = h*|v|² + h*v*conj(d) + e*conj(v) + e*conj(d)
      -- Since h*|v|² is real, its imaginary part is 0.
      -- So Im(γ * conj(γ')) = Im(h*v*conj(d)) + Im(e*conj(v)) + Im(e*conj(d))
      --
      -- We'll use simpler direct bounds instead.
      -- Step 1: Bound |γ(t)| using continuity from 0
      have h_gamma_bdd : ‖γ.toFun t‖ ≤ M * |t - t₀| := by
        -- Use FTC: γ(t) - γ(t₀) = ∫_{t₀}^t γ'(s) ds
        -- Since ‖γ'(s)‖ ≤ M for all s, we get ‖γ(t) - γ(t₀)‖ ≤ M * |t - t₀|
        -- For piecewise C¹ curves, the derivative is bounded a.e. and FTC applies.
        -- The bound follows from Lipschitz property induced by bounded derivative.
        calc ‖γ.toFun t‖ = ‖γ.toFun t - 0‖ := by rw [sub_zero]
          _ = ‖γ.toFun t - γ.toFun t₀‖ := by rw [hγ_zero]
          _ ≤ M * ‖t - t₀‖ := by
              -- Lipschitz bound from bounded derivative: needs FTC for piecewise C¹
              -- Full proof requires showing ∫_{t₀}^t γ'(s) ds = γ(t) - γ(t₀) and bounding the integral
              have := integral_deriv_eq_sub_of_lipschitz γ hLip ht₀ ht_interval;
              cases le_total t t₀ <;> simp_all +decide [ intervalIntegral, abs_of_nonneg ];
              · rw [ ← this, neg_eq_neg_one_mul, norm_mul ];
                refine' le_trans ( mul_le_mul_of_nonneg_left ( MeasureTheory.norm_integral_le_integral_norm _ ) ( by norm_num ) ) _;
                exact le_trans ( mul_le_mul_of_nonneg_left ( MeasureTheory.setIntegral_mono_on ( by exact ContinuousOn.integrableOn_Icc ( by exact ContinuousOn.norm ( by exact hLip.continuousOn.mono ( Set.Icc_subset_Icc ( by linarith ) ( by linarith ) ) ) ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self ) ( by exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self ) measurableSet_Ioc fun x hx => hM x ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ) ) ( by positivity ) ) ( by simp +decide [ *, abs_of_nonpos, mul_comm ] );
              · rw [ ← this, ← intervalIntegral.integral_of_le ( by linarith ) ];
                refine' le_trans ( intervalIntegral.norm_integral_le_of_norm_le_const _ ) _;
                exacts [ M, fun x hx => hM x ( by cases Set.mem_uIoc.mp hx <;> linarith ) ( by cases Set.mem_uIoc.mp hx <;> linarith ), by rw [ abs_of_nonneg ( by linarith ) ] ]
          _ = M * |t - t₀| := by rw [Real.norm_eq_abs]
      -- Step 2: Bound |γ'(t) - γ'(t₀)| using Lipschitz
      have h_deriv_diff : ‖deriv γ.toFun t - deriv γ.toFun t₀‖ ≤ |t - t₀| := by
        have h_dist := hLip.dist_le_mul t ht_interval t₀ ht₀
        simp only [NNReal.coe_one, one_mul, dist_eq_norm] at h_dist
        calc ‖deriv γ.toFun t - deriv γ.toFun t₀‖
            ≤ ‖t - t₀‖ := h_dist
          _ = |t - t₀| := Real.norm_eq_abs _
      -- Step 3: Decompose the cross product
      -- x*y' - y*x' = (γ(t).re * (γ'(t)).im - γ(t).im * (γ'(t)).re)
      -- = (γ(t).re * ((γ'(t) - γ'(t₀)).im + γ'(t₀).im) - γ(t).im * ((γ'(t) - γ'(t₀)).re + γ'(t₀).re))
      -- = (γ(t).re * (γ'(t) - γ'(t₀)).im - γ(t).im * (γ'(t) - γ'(t₀)).re)
      --   + (γ(t).re * γ'(t₀).im - γ(t).im * γ'(t₀).re)
      set v := deriv γ.toFun t₀ with hv_def
      set d := deriv γ.toFun t - v with hd_def
      have h_decomp : deriv γ.toFun t = v + d := by simp [hd_def]
      -- The cross product can be written as sum of two terms
      have h_cross_eq : (γ.toFun t).re * (deriv γ.toFun t).im - (γ.toFun t).im * (deriv γ.toFun t).re =
          ((γ.toFun t).re * d.im - (γ.toFun t).im * d.re) +
          ((γ.toFun t).re * v.im - (γ.toFun t).im * v.re) := by
        rw [h_decomp]
        simp only [Complex.add_re, Complex.add_im]
        ring
      -- Bound term 1: |γ(t).re * d.im - γ(t).im * d.re| ≤ 2*‖γ(t)‖*‖d‖
      have h_term1 : |(γ.toFun t).re * d.im - (γ.toFun t).im * d.re| ≤ 2 * ‖γ.toFun t‖ * ‖d‖ := by
        calc |(γ.toFun t).re * d.im - (γ.toFun t).im * d.re|
            ≤ |(γ.toFun t).re * d.im| + |(γ.toFun t).im * d.re| := abs_sub _ _
          _ = |(γ.toFun t).re| * |d.im| + |(γ.toFun t).im| * |d.re| := by
              simp only [abs_mul]
          _ ≤ ‖γ.toFun t‖ * ‖d‖ + ‖γ.toFun t‖ * ‖d‖ := by
              apply add_le_add
              · exact mul_le_mul (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
                  (abs_nonneg _) (norm_nonneg _)
              · exact mul_le_mul (Complex.abs_im_le_norm _) (Complex.abs_re_le_norm _)
                  (abs_nonneg _) (norm_nonneg _)
          _ = 2 * ‖γ.toFun t‖ * ‖d‖ := by ring
      -- Bound term 2: |γ(t).re * v.im - γ(t).im * v.re| ≤ 2*‖γ(t)‖*‖v‖
      have h_term2 : |(γ.toFun t).re * v.im - (γ.toFun t).im * v.re| ≤ 2 * ‖γ.toFun t‖ * ‖v‖ := by
        calc |(γ.toFun t).re * v.im - (γ.toFun t).im * v.re|
            ≤ |(γ.toFun t).re * v.im| + |(γ.toFun t).im * v.re| := abs_sub _ _
          _ = |(γ.toFun t).re| * |v.im| + |(γ.toFun t).im| * |v.re| := by
              simp only [abs_mul]
          _ ≤ ‖γ.toFun t‖ * ‖v‖ + ‖γ.toFun t‖ * ‖v‖ := by
              apply add_le_add
              · exact mul_le_mul (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
                  (abs_nonneg _) (norm_nonneg _)
              · exact mul_le_mul (Complex.abs_im_le_norm _) (Complex.abs_re_le_norm _)
                  (abs_nonneg _) (norm_nonneg _)
          _ = 2 * ‖γ.toFun t‖ * ‖v‖ := by ring
      -- Now combine: need |cross| ≤ C * (t - t₀)²
      -- |cross| ≤ |term1| + |term2| ≤ 2*‖γ(t)‖*(‖d‖ + ‖v‖)
      -- ≤ 2 * M * |t-t₀| * (|t-t₀| + M) using h_gamma_bdd and h_deriv_diff
      -- For |t-t₀| < 1: ≤ 2*M*|t-t₀| * (|t-t₀| + M) ≤ 2*M*(1 + M)*|t-t₀|²
      -- This is ≤ (3M+1)*|t-t₀|² if 2*M*(1+M) ≤ 3M+1 which holds for M ≥ 0
      --
      -- Actually we need a tighter bound. Let's use:
      -- |cross| ≤ 2*‖γ(t)‖*‖d‖ + 2*‖γ(t)‖*‖v‖
      -- ≤ 2*M*|h|*|h| + 2*M*|h|*M = 2*M*h² + 2*M²*|h|
      -- This is not O(h²)! We need the cancellation.
      --
      -- The issue is term2 is O(h), not O(h²). The cancellation in the cross product
      -- x*y' - y*x' comes from the fact that for the leading term:
      -- γ ≈ h*v means x ≈ h*vx, y ≈ h*vy
      -- So x*vy - y*vx = h*vx*vy - h*vy*vx = 0
      --
      -- We need to be more careful. Let's write γ = h*v + e where e is O(h²).
      -- Then term2 = (h*v + e).re * v.im - (h*v + e).im * v.re
      --            = h*(v.re*v.im - v.im*v.re) + e.re*v.im - e.im*v.re
      --            = 0 + e.re*v.im - e.im*v.re
      -- So |term2| ≤ 2*‖e‖*‖v‖ which is O(h²) if ‖e‖ is O(h²).
      --
      -- We need: ‖γ(t) - (t-t₀)*v‖ ≤ C*|t-t₀|² (the error term is O(h²))
      -- This requires the second derivative bound or explicit integration.
      --
      -- For a simpler approach, let's just use a cruder bound that still works:
      -- Since we're proving existence of SOME constant C, we can be generous.
      -- The bound 2*M*|h|*(|h| + M) works if we allow C to depend on M.
      -- But we already chose C = 3*M + 1, so let's verify this works for |h| < 1.
      --
      -- Actually wait - let me reconsider the term2 bound more carefully.
      -- We have h_gamma_bdd: ‖γ(t)‖ ≤ M*|h| where h = t - t₀
      -- We have hM: ‖v‖ = ‖γ'(t₀)‖ ≤ M
      -- So |term2| ≤ 2*M*|h|*M = 2*M²*|h|
      -- This is NOT O(h²), it's only O(h).
      --
      -- The mathematical argument requires the CANCELLATION in term2.
      -- Without explicit integration or Taylor expansion, we can't get O(h²) from term2.
      --
      -- Let me try a different approach: use that the function is C¹ so we can
      -- use a mean value type argument.
      --
      -- Actually, since the bound 3*M+1 was chosen, let's check what bound we actually get.
      -- For |h| < 1:
      -- |cross| ≤ |term1| + |term2|
      --         ≤ 2*M*|h|*|h| + 2*M*|h|*M  (using ‖d‖ ≤ |h| and ‖γ‖ ≤ M*|h|)
      --         = 2*M*h² + 2*M²*|h|
      --         = 2*M*|h|*(|h| + M)
      --         ≤ 2*M*|h|*(1 + M)    (since |h| < 1)
      --
      -- Hmm, this is |h| not h². The approach needs the cross-product cancellation.
      --
      -- ALTERNATIVE: Use that term2 has the cross-product structure which vanishes for γ ∝ v.
      -- Write γ(t) = (t-t₀)*γ'(t₀) + err where err = γ(t) - (t-t₀)*γ'(t₀).
      -- Then term2 = (h*v + err).re * v.im - (h*v + err).im * v.re
      --            = h*(v.re*v.im - v.im*v.re) + err.re*v.im - err.im*v.re
      --            = err.re*v.im - err.im*v.re
      -- So |term2| ≤ 2*‖err‖*‖v‖ ≤ 2*M*‖err‖
      --
      -- Now we need ‖err‖ = ‖γ(t) - h*v‖ = O(h²).
      -- By FTC: γ(t) - γ(t₀) = ∫_{t₀}^t γ'(s) ds
      -- So err = γ(t) - h*v = ∫_{t₀}^t γ'(s) ds - h*v = ∫_{t₀}^t (γ'(s) - v) ds
      -- Using Lipschitz: ‖γ'(s) - v‖ ≤ |s - t₀|
      -- So ‖err‖ ≤ ∫_{t₀}^t |s - t₀| ds = h²/2
      --
      -- This requires proving the integral bound. Let me use a different approach that
      -- avoids explicit integrals by using an available lemma.
      --
      -- Key insight: The direct bound 2*M*|h|² + 2*M²*|h| gives O(h), not O(h²).
      -- To get O(h²), we need to use the CANCELLATION in term2.
      --
      -- Correct proof strategy:
      -- 1. Define err = γ(t) - h*v where h = t - t₀, v = γ'(t₀)
      -- 2. By FTC: err = ∫_{t₀}^t (γ'(s) - γ'(t₀)) ds, so ‖err‖ ≤ h²/2 (Lipschitz on γ')
      -- 3. Then term2 = (h*v + err).re * v.im - (h*v + err).im * v.re
      --             = h*(v.re*v.im - v.im*v.re) + (err.re*v.im - err.im*v.re)
      --             = 0 + (err.re*v.im - err.im*v.re)  -- CANCELLATION!
      -- 4. So |term2| ≤ 2*‖err‖*‖v‖ ≤ 2*(h²/2)*M = M*h²
      --
      -- Full implementation requires Taylor remainder bounds via FTC.
      -- For now, we use the correct final bound with a placeholder.
      have h_d_bdd : ‖d‖ ≤ |t - t₀| := by
        simp only [hd_def]
        exact h_deriv_diff
      -- The correct bound uses cancellation in term2.
      -- Define error = γ(t) - (t-t₀)*v
      -- We need ‖error‖ ≤ C*|t-t₀|² by the integral bound on γ' - v
      -- For now, we use a workaround: observe that h_gamma_bdd gives ‖γ(t)‖ ≤ M*|t-t₀|
      -- and we can bound the cross-product using the structure.
      --
      -- Key identity: for term2, write γ = h*v + err where err = γ - h*v
      -- term2 = (h*v + err).re * v.im - (h*v + err).im * v.re
      --       = h*(v.re*v.im - v.im*v.re) + err.re*v.im - err.im*v.re
      --       = 0 + err.re*v.im - err.im*v.re
      -- So |term2| ≤ 2*‖err‖*‖v‖
      --
      -- The bound on ‖err‖ = ‖γ(t) - h*v‖:
      -- By FTC intuition: γ(t) - γ(t₀) = ∫ γ'(s) ds, so
      -- err = ∫_{t₀}^t γ'(s) ds - h*v = ∫_{t₀}^t (γ'(s) - v) ds
      -- Using hLip: ‖γ'(s) - v‖ ≤ |s - t₀|
      -- So ‖err‖ ≤ ∫_{t₀}^t |s-t₀| ds = |t-t₀|²/2
      --
      -- This gives |term2| ≤ 2 * (|t-t₀|²/2) * M = M * |t-t₀|²
      -- Combined with |term1| ≤ 2 * M * |t-t₀| * |t-t₀| = 2M * |t-t₀|²
      -- Total: ≤ (2M + M) * |t-t₀|² = 3M * |t-t₀|² ≤ (3M+1) * (t-t₀)²
      --
      -- The FTC argument requires more infrastructure. For now we use a direct bound.
      -- Note: The cross product x*y' - y*x' = Im(γ * conj(γ'))
      -- We have |Im(z)| ≤ |z| ≤ ‖γ‖ * ‖γ'‖ ≤ M*|h| * (M + |h|)
      -- For |h| < 1: ≤ M*|h| * (M+1) = O(|h|), which is NOT O(h²)
      --
      -- The O(h²) bound requires the cancellation structure.
      -- Since h_gamma_bdd is assumed via sorry, we cannot complete this rigorously.
      -- We provide the bound assuming the FTC machinery is available.
      --
      -- Using the established bounds:
      -- |term1| ≤ 2*M*|h|*|h| = 2M*h² (by h_gamma_bdd, h_d_bdd, h_term1)
      -- For term2, we need the cancellation argument.
      --
      -- WORKAROUND: Since we have h_gamma_bdd : ‖γ‖ ≤ M*|h|, use it directly.
      -- Define err := γ(t) - (t - t₀) • v
      set h := t - t₀ with hh_def
      set err := γ.toFun t - h • v with herr_def
      -- Express γ in terms of err
      have h_gamma_decomp : γ.toFun t = h • v + err := by simp [herr_def]
      -- The cross product term2 using the decomposition
      have h_term2_alt : (γ.toFun t).re * v.im - (γ.toFun t).im * v.re =
          err.re * v.im - err.im * v.re := by
        rw [h_gamma_decomp]
        simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
        -- Now h * v.re * v.im - h * v.im * v.re = 0, leaving err terms
        ring
      -- Bound on term2 using err
      have h_term2_err : |(γ.toFun t).re * v.im - (γ.toFun t).im * v.re| ≤ 2 * ‖err‖ * ‖v‖ := by
        rw [h_term2_alt]
        calc |err.re * v.im - err.im * v.re|
            ≤ |err.re * v.im| + |err.im * v.re| := abs_sub _ _
          _ = |err.re| * |v.im| + |err.im| * |v.re| := by simp [abs_mul]
          _ ≤ ‖err‖ * ‖v‖ + ‖err‖ * ‖v‖ := by
              apply add_le_add
              · exact mul_le_mul (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
                  (abs_nonneg _) (norm_nonneg _)
              · exact mul_le_mul (Complex.abs_im_le_norm _) (Complex.abs_re_le_norm _)
                  (abs_nonneg _) (norm_nonneg _)
          _ = 2 * ‖err‖ * ‖v‖ := by ring
      -- Now we need to bound ‖err‖. This is the key step requiring FTC.
      -- err = γ(t) - γ(t₀) - h*v = ∫_{t₀}^t (γ'(s) - v) ds
      -- Using Lipschitz: ‖γ'(s) - v‖ ≤ |s - t₀|
      -- So ‖err‖ ≤ ∫ |s - t₀| ds ≤ h²/2
      -- Suggested helper lemma (FTC + Lipschitz derivative):
      -- lemma norm_sub_sub_deriv_le_of_lipschitz_deriv
      --     (γ : ℝ → ℂ) (hLip : LipschitzOnWith 1 (deriv γ) (Icc (t₀ - δ) (t₀ + δ)))
      --     (ht : t ∈ Icc (t₀ - δ) (t₀ + δ)) :
      --     ‖γ t - γ t₀ - (t - t₀) • deriv γ t₀‖ ≤ |t - t₀|^2 / 2
      -- Proof: write γ(t) - γ(t₀) = ∫ γ'(s) ds, expand, and apply norm_integral_le_integral_norm.
      --
      -- For the formal proof, we need FTC machinery. Using h_gamma_bdd as a fallback:
      -- ‖err‖ = ‖γ(t) - h*v‖ ≤ ‖γ(t)‖ + |h|*‖v‖ ≤ M*|h| + |h|*M = 2M*|h|
      -- This gives |term2| ≤ 2 * 2M*|h| * M = 4M²*|h| which is O(|h|), not O(h²).
      --
      -- The O(h²) bound truly requires the integral/FTC argument.
      -- We assume the FTC bound on err is available (matching the mathematical argument).
      have h_err_bdd : ‖err‖ ≤ |t - t₀|^2 / 2 := by
        -- This requires FTC: err = ∫_{t₀}^t (γ'(s) - v) ds
        -- With ‖γ'(s) - v‖ ≤ |s - t₀| (from hLip), we get ‖err‖ ≤ |t-t₀|²/2
        -- The full proof would use:
        -- 1. γ(t) - γ(t₀) = ∫_{t₀}^t γ'(s) ds (FTC for piecewise C¹)
        -- 2. err = ∫_{t₀}^t (γ'(s) - v) ds
        -- 3. ‖∫ f ds‖ ≤ ∫ ‖f‖ ds ≤ ∫ |s-t₀| ds = |t-t₀|²/2
        --
        -- This needs additional infrastructure for piecewise C¹ FTC.
        -- For now, we use this as the key lemma.
        have h_norm_sub_sub_deriv_le : ‖γ.toFun t - γ.toFun t₀ - (t - t₀) • deriv γ.toFun t₀‖ ≤ |t - t₀| ^ 2 / 2 := by
          convert norm_sub_sub_deriv_le_of_lipschitz_deriv γ hLip ht₀ ht_interval using 1;
          norm_num ; ring;
        simpa only [ hγ_zero, sub_zero ] using h_norm_sub_sub_deriv_le
      -- Now we can complete the proof
      have h_abs := abs_nonneg (t - t₀)
      have h_sq_eq : (t - t₀)^2 = |t - t₀|^2 := by
        rw [sq_abs]
      rw [h_cross_eq]
      calc |(γ.toFun t).re * d.im - (γ.toFun t).im * d.re +
            ((γ.toFun t).re * v.im - (γ.toFun t).im * v.re)|
          ≤ |(γ.toFun t).re * d.im - (γ.toFun t).im * d.re| +
            |(γ.toFun t).re * v.im - (γ.toFun t).im * v.re| := abs_add_le _ _
        _ ≤ 2 * ‖γ.toFun t‖ * ‖d‖ + 2 * ‖err‖ * ‖v‖ := add_le_add h_term1 h_term2_err
        _ ≤ 2 * (M * |t - t₀|) * |t - t₀| + 2 * (|t - t₀|^2 / 2) * M := by
            have hv_bdd : ‖v‖ ≤ M := hM t₀ ht₀
            have hd_bdd' : ‖d‖ ≤ |t - t₀| := h_d_bdd
            nlinarith [h_gamma_bdd, h_err_bdd, hv_bdd, hd_bdd', norm_nonneg (γ.toFun t),
                       norm_nonneg d, norm_nonneg err, norm_nonneg v, h_abs]
        _ = 2 * M * |t - t₀|^2 + M * |t - t₀|^2 := by ring
        _ = 3 * M * |t - t₀|^2 := by ring
        _ ≤ (3 * M + 1) * |t - t₀|^2 := by nlinarith [sq_nonneg (|t - t₀|), hM_pos]
        _ = (3 * M + 1) * (t - t₀)^2 := by rw [h_sq_eq]
  · -- Case: t0 not in [a,b]
    -- The distance |t - t0| is bounded below for t in [a,b]
    have h_t0_outside : t₀ < γ.a ∨ t₀ > γ.b := by
      simp only [Icc, mem_setOf, not_and_or, not_le] at ht₀
      exact ht₀
    -- Get minimum distance
    have h_dist_pos : ∃ δ > 0, ∀ t ∈ Icc γ.a γ.b, |t - t₀| ≥ δ := by
      cases h_t0_outside with
      | inl h => exact ⟨γ.a - t₀, by linarith, fun t ht => by
          calc |t - t₀| ≥ t - t₀ := le_abs_self _
            _ ≥ γ.a - t₀ := by linarith [ht.1]⟩
      | inr h => exact ⟨t₀ - γ.b, by linarith, fun t ht => by
          calc |t - t₀| ≥ -(t - t₀) := neg_le_abs _
            _ = t₀ - t := by ring
            _ ≥ t₀ - γ.b := by linarith [ht.2]⟩
    obtain ⟨δ, hδ_pos, hδ⟩ := h_dist_pos
    -- Bound on numerator using boundedness of gamma and gamma' on compact [a,b]
    have h_num_bdd : ∃ B > 0, ∀ t ∈ Icc γ.a γ.b,
        |(γ.toFun t).re * (deriv γ.toFun t).im - (γ.toFun t).im * (deriv γ.toFun t).re| ≤ B := by
      have h_gamma_bdd := IsCompact.exists_bound_of_continuousOn isCompact_Icc γ.continuous_toFun
      obtain ⟨Bg, hBg⟩ := h_gamma_bdd
      have h_deriv_bdd : ∃ Bd, ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Bd := by
        use ‖deriv γ.toFun γ.a‖ + (γ.b - γ.a) + 1
        intro t ht
        have ha : γ.a ∈ Icc γ.a γ.b := ⟨le_refl _, γ.hab.le⟩
        have hLip_sub := hLip.norm_sub_le ha ht
        simp only [NNReal.coe_one, one_mul] at hLip_sub
        have h_dist : ‖γ.a - t‖ ≤ γ.b - γ.a := by
          simp only [Real.norm_eq_abs]; cases abs_cases (γ.a - t) <;> linarith [ht.1, ht.2]
        calc ‖deriv γ.toFun t‖
            = ‖deriv γ.toFun t - deriv γ.toFun γ.a + deriv γ.toFun γ.a‖ := by ring_nf
          _ ≤ ‖deriv γ.toFun t - deriv γ.toFun γ.a‖ + ‖deriv γ.toFun γ.a‖ := norm_add_le _ _
          _ = ‖deriv γ.toFun γ.a - deriv γ.toFun t‖ + ‖deriv γ.toFun γ.a‖ := by rw [norm_sub_rev]
          _ ≤ ‖γ.a - t‖ + ‖deriv γ.toFun γ.a‖ := by linarith
          _ ≤ (γ.b - γ.a) + ‖deriv γ.toFun γ.a‖ := by linarith
          _ ≤ ‖deriv γ.toFun γ.a‖ + (γ.b - γ.a) + 1 := by linarith
      obtain ⟨Bd, hBd⟩ := h_deriv_bdd
      -- Use 2*Bg*Bd + 1 as the bound
      use 2 * Bg * Bd + 1
      constructor
      · have h1 := hBg γ.a ⟨le_refl _, γ.hab.le⟩
        have h2 := hBd γ.a ⟨le_refl _, γ.hab.le⟩
        have hBg_nn : 0 ≤ Bg := le_trans (norm_nonneg _) h1
        have hBd_nn : 0 ≤ Bd := le_trans (norm_nonneg _) h2
        linarith [mul_nonneg hBg_nn hBd_nn]
      intro t ht
      -- Cross product bound: |ad - bc| ≤ |a||d| + |b||c| ≤ 2*|z1|*|z2|
      have h1 : ‖γ.toFun t‖ ≤ Bg := hBg t ht
      have h2 : ‖deriv γ.toFun t‖ ≤ Bd := hBd t ht
      have h_cross : |(γ.toFun t).re * (deriv γ.toFun t).im - (γ.toFun t).im * (deriv γ.toFun t).re|
          ≤ |(γ.toFun t).re * (deriv γ.toFun t).im| + |(γ.toFun t).im * (deriv γ.toFun t).re| := by
        -- |a - b| ≤ |a| + |b| follows from triangle inequality
        set a := (γ.toFun t).re * (deriv γ.toFun t).im
        set b := (γ.toFun t).im * (deriv γ.toFun t).re
        calc |a - b| = |a + (-b)| := by ring_nf
          _ ≤ |a| + |-b| := abs_add_le _ _
          _ = |a| + |b| := by rw [abs_neg]
      calc |(γ.toFun t).re * (deriv γ.toFun t).im - (γ.toFun t).im * (deriv γ.toFun t).re|
          ≤ |(γ.toFun t).re * (deriv γ.toFun t).im| + |(γ.toFun t).im * (deriv γ.toFun t).re| := h_cross
        _ = |(γ.toFun t).re| * |(deriv γ.toFun t).im| + |(γ.toFun t).im| * |(deriv γ.toFun t).re| := by
            rw [abs_mul, abs_mul]
        _ ≤ ‖γ.toFun t‖ * ‖deriv γ.toFun t‖ + ‖γ.toFun t‖ * ‖deriv γ.toFun t‖ := by
            apply add_le_add
            · apply mul_le_mul (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _) (abs_nonneg _) (norm_nonneg _)
            · apply mul_le_mul (Complex.abs_im_le_norm _) (Complex.abs_re_le_norm _) (abs_nonneg _) (norm_nonneg _)
        _ = 2 * ‖γ.toFun t‖ * ‖deriv γ.toFun t‖ := by ring
        _ ≤ 2 * Bg * Bd := by nlinarith [norm_nonneg (γ.toFun t), norm_nonneg (deriv γ.toFun t)]
        _ ≤ 2 * Bg * Bd + 1 := by linarith
    obtain ⟨B, hB_pos, hB⟩ := h_num_bdd
    use B / δ^2 + 1
    constructor; positivity
    intro t ht_small ht_interval
    have h_t_dist := hδ t ht_interval
    calc |(γ.toFun t).re * (deriv γ.toFun t).im - (γ.toFun t).im * (deriv γ.toFun t).re|
        ≤ B := hB t ht_interval
      _ = B / δ^2 * δ^2 := by field_simp
      _ ≤ B / δ^2 * (t - t₀)^2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc δ^2 ≤ |t - t₀|^2 := by nlinarith [h_t_dist]
            _ = (t - t₀)^2 := sq_abs _
      _ ≤ (B / δ^2 + 1) * (t - t₀)^2 := by nlinarith [sq_nonneg (t - t₀)]

/-- Alternative formulation using Asymptotics.IsBigO, restricted to the interval [a,b].
    This is the natural setting since gamma is only well-controlled on this interval. -/
theorem numerator_isBigO_squared (t₀ : ℝ)
    (hγ_zero : γ.toFun t₀ = 0)
    (hLip : LipschitzOnWith 1 (deriv γ.toFun) (Icc γ.a γ.b)) :
    (fun t => (γ.toFun t).re * (deriv γ.toFun t).im -
              (γ.toFun t).im * (deriv γ.toFun t).re) =O[𝓝[Icc γ.a γ.b] t₀]
    (fun t => (t - t₀)^2) := by
  -- Convert from existential bound to IsBigO
  obtain ⟨C, hC_pos, hC⟩ := numerator_big_O_squared γ t₀ hγ_zero hLip
  rw [Asymptotics.isBigO_iff']
  refine ⟨C, hC_pos, ?_⟩
  -- Filter by the ball intersected with [a,b]
  have h_mem : Icc γ.a γ.b ∩ Metric.ball t₀ 1 ∈ 𝓝[Icc γ.a γ.b] t₀ := by
    apply inter_mem_nhdsWithin
    exact Metric.ball_mem_nhds t₀ (by norm_num : (1 : ℝ) > 0)
  filter_upwards [h_mem] with t ht
  have ht_interval : t ∈ Icc γ.a γ.b := ht.1
  have ht_ball : t ∈ Metric.ball t₀ 1 := ht.2
  have ht_small : |t - t₀| < 1 := by
    rw [Metric.mem_ball, Real.dist_eq] at ht_ball
    exact ht_ball
  have h := hC t ht_small ht_interval
  calc ‖(γ.toFun t).re * (deriv γ.toFun t).im - (γ.toFun t).im * (deriv γ.toFun t).re‖
      = |(γ.toFun t).re * (deriv γ.toFun t).im - (γ.toFun t).im * (deriv γ.toFun t).re| := Real.norm_eq_abs _
    _ ≤ C * (t - t₀)^2 := h
    _ = C * |(t - t₀)^2| := by rw [abs_of_nonneg (sq_nonneg _)]
    _ = C * ‖(t - t₀)^2‖ := by rw [Real.norm_eq_abs]

/-! ## Denominator Estimate: Θ(t²) -/

/-! ### Helper Lemmas for Denominator Bounds -/

section AristotleLemmas

/-
If a function has a non-zero derivative at a zero, its squared norm is bounded by quadratic terms locally.
-/
lemma normSq_bound_of_hasDerivWithinAt {f : ℝ → ℂ} {s : Set ℝ} {t₀ : ℝ} {L : ℂ}
    (hdiff : HasDerivWithinAt f L s t₀) (hL : L ≠ 0) (hzero : f t₀ = 0) :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
      ∃ δ > 0, ∀ t ∈ s, |t - t₀| < δ → t ≠ t₀ →
        c * (t - t₀)^2 ≤ (f t).re^2 + (f t).im^2 ∧
        (f t).re^2 + (f t).im^2 ≤ C * (t - t₀)^2 := by
  have h_deriv_nonzero : Filter.Tendsto (fun t => ((f t).re^2 + (f t).im^2) / (t - t₀)^2) (nhdsWithin t₀ (s \ {t₀})) (nhds (Complex.normSq L)) := by
    have h_deriv_nonzero : Filter.Tendsto (fun t => (f t - f t₀) / (t - t₀)) (nhdsWithin t₀ (s \ {t₀})) (nhds L) := by
      rw [ hasDerivWithinAt_iff_tendsto_slope ] at hdiff
      convert hdiff using 1
      funext t; simp [slope]
      ring
    have h_deriv_nonzero : Filter.Tendsto (fun t => Complex.normSq ((f t - f t₀) / (t - t₀))) (nhdsWithin t₀ (s \ {t₀})) (nhds (Complex.normSq L)) := by
      exact Complex.continuous_normSq.continuousAt.tendsto.comp h_deriv_nonzero
    simp_all +decide [ Complex.normSq, sq ]
  have := Metric.tendsto_nhdsWithin_nhds.mp h_deriv_nonzero ( Complex.normSq L / 2 ) ( half_pos <| Complex.normSq_pos.mpr hL )
  obtain ⟨ δ, hδ, H ⟩ := this
  exact ⟨ Complex.normSq L / 2, Complex.normSq L + Complex.normSq L, half_pos <| Complex.normSq_pos.mpr hL, add_pos_of_pos_of_nonneg ( Complex.normSq_pos.mpr hL ) <| Complex.normSq_nonneg _, δ, hδ, fun t ht ht' ht'' ↦ ⟨ by nlinarith [ abs_lt.mp <| H ⟨ ht, ht'' ⟩ ht', mul_div_cancel₀ ( ( f t |> Complex.re ) ^ 2 + ( f t |> Complex.im ) ^ 2 ) ( pow_ne_zero 2 <| sub_ne_zero.mpr ht'' ) ], by nlinarith [ abs_lt.mp <| H ⟨ ht, ht'' ⟩ ht', mul_div_cancel₀ ( ( f t |> Complex.re ) ^ 2 + ( f t |> Complex.im ) ^ 2 ) ( pow_ne_zero 2 <| sub_ne_zero.mpr ht'' ) ] ⟩ ⟩

/-
If a function is continuous on a closed interval and differentiable on the interior, and its derivative has a limit at the left endpoint, then the function has a right derivative at that endpoint equal to the limit.
-/
lemma hasDerivWithinAt_of_tendsto_deriv_right_of_Ioo {f : ℝ → ℂ} {a b : ℝ} {L : ℂ}
    (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (hlim : Filter.Tendsto (deriv f) (𝓝[>] a) (𝓝 L)) :
    HasDerivWithinAt f L (Ici a) a := by
  refine' hasDerivWithinAt_iff_tendsto.mpr _
  have h_mean_val : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Set.Ioo a (a + δ), ‖f x - f a - (x - a) • L‖ ≤ ε * (x - a) := by
    have h_mean_val : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Set.Ioo a (a + δ), ‖deriv f x - L‖ ≤ ε := by
      rw [ Metric.tendsto_nhdsWithin_nhds ] at hlim
      exact fun ε hε => by obtain ⟨ δ, hδ, H ⟩ := hlim ε hε; exact ⟨ δ, hδ, fun x hx => le_of_lt ( H hx.1 ( abs_lt.mpr ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩ ) ) ⟩
    intro ε hε_pos
    obtain ⟨δ, hδ_pos, hδ⟩ := h_mean_val ε hε_pos
    use min δ (b - a)
    have h_mean_val : ∀ x ∈ Set.Ioo a (a + min δ (b - a)), ‖f x - f a - (x - a) • L‖ ≤ ∫ t in a..x, ‖deriv f t - L‖ := by
      intros x hx
      have h_mean_val : f x - f a - (x - a) • L = ∫ t in a..x, (deriv f t - L) := by
        rw [ intervalIntegral.integral_eq_sub_of_hasDeriv_right ]
        rotate_right
        use fun t => f t - t • L
        · norm_num ; ring
        · exact ContinuousOn.sub ( hcont.mono ( by rw [ Set.uIcc_of_le hx.1.le ] ; exact Set.Icc_subset_Icc le_rfl ( by linarith [ hx.2, min_le_left δ ( b - a ), min_le_right δ ( b - a ) ] ) ) ) ( continuousOn_id.smul continuousOn_const )
        · simp +zetaDelta at *
          intro t ht₁ ht₂
          convert HasDerivAt.hasDerivWithinAt ( HasDerivAt.sub ( hdiff.hasDerivAt ( Ioo_mem_nhds ( show a < t by cases ht₁ <;> linarith ) ( show t < b by cases ht₂ <;> linarith [ min_le_right δ ( b - a ) ] ) ) ) ( HasDerivAt.mul ( HasDerivAt.ofReal_comp ( hasDerivAt_id t ) ) ( hasDerivAt_const _ _ ) ) ) using 1 ; norm_num
        · rw [ intervalIntegrable_iff_integrableOn_Ioo_of_le hx.1.le ]
          refine' MeasureTheory.Integrable.mono' _ _ _
          exacts [ fun _ => ε, by norm_num, by exact ( measurable_deriv f |> Measurable.aestronglyMeasurable ) |> fun h => h.sub ( measurable_const.aestronglyMeasurable ), Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioo ) fun t ht => hδ t ⟨ by linarith [ ht.1 ], by linarith [ ht.2, hx.2, min_le_left δ ( b - a ), min_le_right δ ( b - a ) ] ⟩ ]
      simpa only [ h_mean_val ] using by simpa only [ intervalIntegral.integral_of_le hx.1.le ] using MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℂ )
    have h_integral_bound : ∀ x ∈ Set.Ioo a (a + min δ (b - a)), ∫ t in a..x, ‖deriv f t - L‖ ≤ ∫ t in a..x, ε := by
      intro x hx
      rw [ intervalIntegral.integral_of_le hx.1.le, intervalIntegral.integral_of_le hx.1.le ]
      refine' MeasureTheory.integral_mono_of_nonneg _ _ _
      · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
      · norm_num
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using hδ t ⟨ by linarith [ ht.1 ], by linarith [ ht.2, hx.2, min_le_left δ ( b - a ), min_le_right δ ( b - a ) ] ⟩
    exact ⟨ lt_min hδ_pos ( sub_pos.mpr hab ), fun x hx => le_trans ( h_mean_val x hx ) ( le_trans ( h_integral_bound x hx ) ( by norm_num [ mul_comm ] ) ) ⟩
  rw [ Metric.tendsto_nhdsWithin_nhds ]
  intro ε hε; rcases h_mean_val ( ε / 2 ) ( half_pos hε ) with ⟨ δ, hδ, H ⟩ ; refine' ⟨ δ, hδ, fun x hx₁ hx₂ => _ ⟩ ; cases eq_or_lt_of_le hx₁.out <;> simp_all +decide [ mul_comm ]
  rw [ inv_mul_eq_div, div_lt_iff₀ ] <;> cases abs_cases ( x - a ) <;> nlinarith [ H x ‹_› ( by linarith [ abs_lt.mp hx₂ ] ), abs_lt.mp hx₂ ]

/-
If a function is continuous on a closed interval and differentiable on the interior, and its derivative has a limit at the right endpoint, then the function has a left derivative at that endpoint equal to the limit.
-/
lemma hasDerivWithinAt_of_tendsto_deriv_left_of_Ioo {f : ℝ → ℂ} {a b : ℝ} {L : ℂ}
    (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (hlim : Filter.Tendsto (deriv f) (𝓝[<] b) (𝓝 L)) :
    HasDerivWithinAt f L (Iic b) b := by
  rw [ hasDerivWithinAt_iff_tendsto ]
  rw [ Metric.tendsto_nhdsWithin_nhds ] at *
  intro ε ε_pos ; obtain ⟨ δ, δ_pos, H ⟩ := hlim ( ε := ε / 2 ) ( half_pos ε_pos ) ; refine' ⟨ Min.min δ ( b - a ), lt_min δ_pos ( sub_pos.mpr hab ), fun x hx₁ hx₂ => _ ⟩ ; rcases eq_or_lt_of_le hx₁.out with rfl | hx₁' <;> simp_all +decide [ dist_eq_norm ]
  -- By the properties of the derivative and the definition of $g$, we have:
  have h_ftc : ∫ y in (x : ℝ)..b, deriv f y = f b - f x := by
    rw [ intervalIntegral.integral_eq_sub_of_hasDeriv_right ]
    · exact hcont.mono ( by rw [ Set.uIcc_of_le hx₁ ] ; exact Set.Icc_subset_Icc ( by linarith [ abs_lt.mp hx₂.2 ] ) le_rfl )
    · simp +zetaDelta at *
      exact fun y hy₁ hy₂ => DifferentiableAt.hasDerivAt ( hdiff.differentiableAt ( Ioo_mem_nhds ( by cases hy₁ <;> cases hy₂ <;> linarith [ abs_lt.mp hx₂.1, abs_lt.mp hx₂.2 ] ) ( by cases hy₁ <;> cases hy₂ <;> linarith [ abs_lt.mp hx₂.1, abs_lt.mp hx₂.2 ] ) ) ) |> HasDerivAt.hasDerivWithinAt
    · rw [ intervalIntegrable_iff_integrableOn_Ioo_of_le hx₁ ]
      refine' MeasureTheory.Integrable.mono' _ _ _
      refine' fun t => ε / 2 + ‖L‖
      · norm_num
      · exact (measurable_deriv f).aestronglyMeasurable
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with t ht using by simpa using norm_add_le ( deriv f t - L ) L |> le_trans <| add_le_add_right ( le_of_lt <| H ht.2 <| abs_lt.mpr ⟨ by linarith [ ht.1, abs_lt.mp hx₂.1 ], by linarith [ ht.2, abs_lt.mp hx₂.1 ] ⟩ ) _
  -- Using the fact that the derivative of $f$ is close to $L$ on $(x, b)$, we can bound the integral.
  have h_integral_bound : ‖∫ y in (x : ℝ)..b, deriv f y - L‖ ≤ ε / 2 * (b - x) := by
    rw [ intervalIntegral.integral_of_le hx₁ ]
    refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ )
    refine' fun y => ε / 2
    · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
    · norm_num
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc, MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton b ) ] with y hy₁ hy₂ using le_of_lt ( H ( lt_of_le_of_ne hy₁.2 hy₂ ) ( abs_lt.mpr ⟨ by linarith [ hy₁.1, hy₁.2, abs_lt.mp hx₂.1, abs_lt.mp hx₂.2 ], by linarith [ hy₁.1, hy₁.2, abs_lt.mp hx₂.1, abs_lt.mp hx₂.2 ] ⟩ ) )
    · norm_num [ mul_comm, hx₁ ]
  rw [ intervalIntegral.integral_sub ] at h_integral_bound <;> norm_num at *
  · rw [ inv_mul_eq_div, div_lt_iff₀ ] <;> simp_all +decide [ norm_sub_rev ]
    · rw [ show f x - f b - ( x - b ) * L = - ( f b - f x - ( b - x ) * L ) by ring, norm_neg ] ; cases abs_cases ( x - b ) <;> nlinarith [ abs_lt.mp hx₂.1, abs_lt.mp hx₂.2 ]
    · linarith
  · rw [ intervalIntegrable_iff_integrableOn_Ioo_of_le hx₁ ]
    refine' MeasureTheory.Integrable.mono' _ _ _
    refine' fun y => ε / 2 + ‖L‖
    · norm_num
    · exact (measurable_deriv f).aestronglyMeasurable
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with y hy using by have := H hy.2 ( abs_lt.mpr ⟨ by linarith [ hy.1, hy.2, abs_lt.mp hx₂.1 ], by linarith [ hy.1, hy.2, abs_lt.mp hx₂.1 ] ⟩ ) ; exact le_trans ( norm_le_of_mem_closedBall <| by simpa using this.le ) ( by linarith )

/-
For a piecewise C1 immersion, at any point t < b, there exists a non-zero right derivative.
-/
lemma PiecewiseC1Immersion.exists_right_deriv (γ : PiecewiseC1Immersion) (t : ℝ) (ht : t ∈ Ico γ.a γ.b) :
    ∃ L : ℂ, L ≠ 0 ∧ HasDerivWithinAt γ.toFun L (Ici t) t := by
  by_cases h : t ∈ γ.partition
  · -- By definition of `right_deriv_limit`, there exists a non-zero right derivative at `t`.
    obtain ⟨L, hL_ne_zero, hL⟩ : ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv γ.toFun) (𝓝[>] t) (𝓝 L) := by
      exact γ.right_deriv_limit t h ht.2
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ Set.Ioo t (t + δ), x ∉ γ.partition := by
      have h_finite : Set.Finite (γ.partition \ {t}) := by
        exact Set.Finite.subset ( Finset.finite_toSet γ.partition ) fun x hx => hx.1
      obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ Set.Ioo t (t + δ), x ∉ (γ.partition \ {t}) := by
        have := Metric.isOpen_iff.mp ( isOpen_compl_iff.mpr h_finite.isClosed ) t
        simp_all +decide [ Set.subset_def ]
        exact ⟨ this.choose, this.choose_spec.1, fun x hx₁ hx₂ hx₃ => this.choose_spec.2 x ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) hx₃ ⟩
      grind
    have h_cont_diff : ContinuousOn γ.toFun (Set.Icc t (min γ.b (t + δ))) ∧ DifferentiableOn ℝ γ.toFun (Set.Ioo t (min γ.b (t + δ))) := by
      refine' ⟨ γ.continuous_toFun.mono _, _ ⟩
      · exact Set.Icc_subset_Icc ht.1 ( min_le_left _ _ )
      · intro x hx
        exact DifferentiableAt.differentiableWithinAt ( γ.smooth_off_partition x ⟨ by linarith [ hx.1, hx.2, ht.1 ], by linarith [ hx.1, hx.2, ht.2, min_le_left γ.b ( t + δ ), min_le_right γ.b ( t + δ ) ] ⟩ ( hδ x ⟨ by linarith [ hx.1, hx.2, ht.1 ], by linarith [ hx.1, hx.2, ht.2, min_le_left γ.b ( t + δ ), min_le_right γ.b ( t + δ ) ] ⟩ ) )
    have := hasDerivWithinAt_of_tendsto_deriv_right_of_Ioo ( show t < Min.min γ.b ( t + δ ) from lt_min ht.2 ( by linarith ) ) h_cont_diff.1 h_cont_diff.2 hL; aesop
  · have := γ.smooth_off_partition t ⟨ ht.1, ht.2.le ⟩ h
    exact ⟨ deriv γ.toFun t, γ.deriv_ne_zero t ⟨ ht.1, ht.2.le ⟩ h, this.hasDerivAt.hasDerivWithinAt ⟩

/-
For a piecewise C1 immersion, at any point t > a, there exists a non-zero left derivative.
-/
lemma PiecewiseC1Immersion.exists_left_deriv (γ : PiecewiseC1Immersion) (t : ℝ) (ht : t ∈ Ioc γ.a γ.b) :
    ∃ L : ℂ, L ≠ 0 ∧ HasDerivWithinAt γ.toFun L (Iic t) t := by
  have := γ.left_deriv_limit t
  by_cases h : t ∈ γ.partition <;> simp_all +decide
  · obtain ⟨ L, hL₁, hL₂ ⟩ := this
    -- Since $t$ is in the partition, we can find a small interval $(t-\delta, t)$ with no partition points.
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ Set.Ioo (t - δ) t, x ∉ γ.partition := by
      have h_finite : Set.Finite (γ.partition \ {t}) := by
        exact Set.Finite.subset ( γ.partition.finite_toSet ) fun x hx => hx.1
      obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ Set.Ioo (t - δ) t, x ∉ (γ.partition \ {t}) := by
        have := Metric.isOpen_iff.mp ( isOpen_compl_iff.mpr h_finite.isClosed ) t
        simp +zetaDelta at *
        exact ⟨ this.choose, this.choose_spec.1, fun x hx₁ hx₂ hx₃ => Classical.not_not.1 fun hx₄ => this.choose_spec.2 ( Metric.mem_ball.2 <| abs_lt.2 ⟨ by linarith, by linarith ⟩ ) ⟨ hx₃, hx₄ ⟩ ⟩
      exact ⟨ δ, hδ_pos, fun x hx hx' => hδ x hx <| by aesop ⟩
    -- On $[t-\delta, t]$, $\gamma$ is continuous and differentiable on the interior.
    have h_cont_diff : ContinuousOn γ.toFun (Set.Icc (t - δ) t) ∧ DifferentiableOn ℝ γ.toFun (Set.Ioo (t - δ) t) := by
      have h_cont_diff : ContinuousOn γ.toFun (Set.Icc γ.a γ.b) ∧ DifferentiableOn ℝ γ.toFun (Set.Ioo γ.a γ.b \ γ.partition) := by
        exact ⟨ γ.continuous_toFun, fun x hx => DifferentiableAt.differentiableWithinAt <| γ.smooth_off_partition x ⟨ hx.1.1.le, hx.1.2.le ⟩ hx.2 ⟩
      refine' ⟨ h_cont_diff.1.mono _, h_cont_diff.2.mono _ ⟩
      · intro x hx
        constructor <;> contrapose! hδ
        · exact ⟨ γ.a, ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩, γ.endpoints_in_partition.1 ⟩
        · linarith [ hx.1, hx.2 ]
      · intro x hx
        simp +zetaDelta at *
        exact ⟨ ⟨ by linarith [ show γ.a ≤ t - δ by exact le_of_not_gt fun h => hδ ( γ.a ) ( by linarith ) ( by linarith ) ( by have := γ.endpoints_in_partition; aesop ) ], by linarith ⟩, hδ x hx.1 hx.2 ⟩
    have := hasDerivWithinAt_of_tendsto_deriv_left_of_Ioo ( show t - δ < t by linarith ) h_cont_diff.1 h_cont_diff.2 hL₂
    exact ⟨ L, hL₁, this ⟩
  · -- Since $t$ is not in the partition, $\gamma$ is differentiable at $t$ with non-zero derivative.
    obtain ⟨L, hL⟩ : ∃ L : ℂ, HasDerivAt γ.toFun L t := by
      exact ⟨ _, γ.smooth_off_partition t ⟨ by linarith, by linarith ⟩ h |> DifferentiableAt.hasDerivAt ⟩
    have := γ.deriv_ne_zero t ⟨ by linarith, by linarith ⟩ h
    exact ⟨ L, by simpa [ hL.deriv ] using this, hL.hasDerivWithinAt ⟩

end AristotleLemmas

/-- The denominator x² + y² near a zero.

    For an immersion γ with γ(t₀) = 0:
    c·(t - t₀)² ≤ x(t)² + y(t)² ≤ C·(t - t₀)²

    **Proof**:
    By Taylor: γ(t) = (t - t₀)·γ'(t₀) + O((t-t₀)²)

    Upper bound: |γ(t)|² ≤ (|t-t₀|·|γ'(t₀)| + C(t-t₀)²)² ≤ C'(t-t₀)²

    Lower bound: Using |γ'(t₀)| > 0 (immersion condition)
    |γ(t)| ≥ |t-t₀|·|γ'(t₀)| - C(t-t₀)² ≥ (|γ'(t₀)| - C|t-t₀|)|t-t₀|
    For small |t-t₀|, this is ≥ (|γ'(t₀)|/2)|t-t₀|
    Hence |γ(t)|² ≥ c(t-t₀)²
-/
theorem denominator_Theta_squared (t₀ : ℝ) (ht₀ : t₀ ∈ Icc γ.a γ.b)
    (hγ_zero : γ.toFun t₀ = 0) :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
      ∃ δ > 0, ∀ t, |t - t₀| < δ → t ∈ Icc γ.a γ.b →
        c * (t - t₀)^2 ≤ (γ.toFun t).re^2 + (γ.toFun t).im^2 ∧
        (γ.toFun t).re^2 + (γ.toFun t).im^2 ≤ C * (t - t₀)^2 := by
  -- The immersion condition gives |γ'(t₀)| > 0
  -- Need to handle the case t₀ ∈ partition vs t₀ ∉ partition
  by_cases h_part : t₀ ∈ γ.toPiecewiseC1Curve.partition
  · -- At partition point: use one-sided limits
    by_cases h_left : t₀ > γ.a
    · by_cases h_right : t₀ < γ.b
      · -- By definition of $γ$, we know that $γ$ is differentiable at $t₀$ with non-zero derivative.
        obtain ⟨L, hL_ne_zero, hL_deriv⟩ : ∃ L : ℂ, L ≠ 0 ∧ HasDerivWithinAt γ.toFun L (Ici t₀) t₀ := by
          exact γ.exists_right_deriv t₀ ⟨ h_left.le, h_right ⟩
        have := normSq_bound_of_hasDerivWithinAt hL_deriv hL_ne_zero hγ_zero
        simp +zetaDelta at *
        obtain ⟨ c, hc, x, hx, δ, hδ, H ⟩ := this
        obtain ⟨ L', hL'_ne_zero, hL'_deriv ⟩ := γ.exists_left_deriv t₀ ⟨ by linarith, by linarith ⟩
        obtain ⟨ c', hc', x', hx', δ', hδ', H' ⟩ := normSq_bound_of_hasDerivWithinAt hL'_deriv hL'_ne_zero hγ_zero
        refine' ⟨ Min.min c c', lt_min hc x', Max.max x hc', lt_max_of_lt_left hx, Min.min δ δ', lt_min hδ hδ', fun t ht₁ ht₂ ht₃ => _ ⟩
        cases lt_or_ge t t₀ <;> simp_all +decide [ abs_lt ]
        · exact ⟨ by nlinarith [ H' t ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ), min_le_left c c', min_le_right c c' ], by nlinarith [ H' t ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ), le_max_left x hc', le_max_right x hc' ] ⟩
        · cases eq_or_ne t t₀ <;> simp_all +decide [ min_mul_of_nonneg, max_mul_of_nonneg ]
      · -- Since t₀ is not less than γ.b and t₀ is in the interval [γ.a, γ.b], it must be that t₀ = γ.b.
        have h_t0_eq_b : t₀ = γ.b := by
          linarith [ ht₀.2 ]
        -- Apply the lemma `PiecewiseC1Immersion.exists_left_deriv` to find a non-zero left derivative at `t₀`.
        obtain ⟨L, hL_ne_zero, hL_deriv⟩ : ∃ L : ℂ, L ≠ 0 ∧ HasDerivWithinAt γ.toFun L (Iic t₀) t₀ := by
          exact γ.exists_left_deriv t₀ ⟨ by linarith, by linarith ⟩
        obtain ⟨ c, C, hc, hC, δ, hδ, H ⟩ := normSq_bound_of_hasDerivWithinAt hL_deriv hL_ne_zero hγ_zero
        refine' ⟨ c, C, hc, hC, Min.min δ ( t₀ - γ.a ), lt_min hδ ( sub_pos.mpr h_left ), fun t ht₁ ht₂ => _ ⟩ ; cases eq_or_ne t t₀ <;> simp_all +decide
    · have h_right : ∃ L : ℂ, L ≠ 0 ∧ HasDerivWithinAt γ.toFun L (Ici t₀) t₀ := by
        have h_right : t₀ < γ.b := by
          linarith [ ht₀.1, ht₀.2, γ.hab ]
        exact γ.exists_right_deriv t₀ ⟨ by linarith [ ht₀.1 ], by linarith [ ht₀.2 ] ⟩
      obtain ⟨ L, hL_ne_zero, hL_deriv ⟩ := h_right
      have := normSq_bound_of_hasDerivWithinAt hL_deriv hL_ne_zero hγ_zero
      obtain ⟨ c, C, hc, hC, δ, hδ, H ⟩ := this; use c, C, hc, hC, δ, hδ; intro t ht₁ ht₂; cases eq_or_ne t t₀ <;> simp_all +decide
      exact H t ( by linarith ) ht₁ ‹_›
  · -- At smooth point: use continuity of derivative
    have h_deriv_ne : deriv γ.toFun t₀ ≠ 0 := γ.deriv_ne_zero t₀ ht₀ h_part
    have := normSq_bound_of_hasDerivWithinAt ( show HasDerivWithinAt γ.toFun ( deriv γ.toFun t₀ ) ( Set.Icc γ.a γ.b ) t₀ from ?_ ) h_deriv_ne hγ_zero
    · obtain ⟨ c, C, hc, hC, δ, hδ, H ⟩ := this; use c, C, hc, hC, δ, hδ; intro t ht₁ ht₂; by_cases h : t = t₀ <;> aesop
    · exact DifferentiableAt.hasDerivAt ( γ.smooth_off_partition t₀ ht₀ h_part ) |> HasDerivAt.hasDerivWithinAt

/-! ## Bounded Integrand -/

/-- The winding number integrand is bounded near a zero.

    Combining numerator = O(t²) and denominator = Θ(t²):
    (x·ẏ - y·ẋ)/(x² + y²) = O(t²)/Θ(t²) = O(1)
-/
theorem windingNumberIntegrand_bounded_near_zero (t₀ : ℝ)
    (hγ_zero : γ.toFun t₀ = 0)
    (hLip : LipschitzOnWith 1 (deriv γ.toFun) (Icc γ.a γ.b)) :
    ∃ M : ℝ, ∃ δ > 0, ∀ t, |t - t₀| < δ → t ∈ Icc γ.a γ.b →
      |windingNumberIntegrand γ.toFun t| ≤ M := by
  -- Combine the numerator and denominator estimates
  -- numerator = O(t²), denominator = Θ(t²), so ratio = O(1)
  -- Use the fact that $|f/g| \leq |f| \cdot |1/g|$ and apply the big O and big Ω results to each term.
  obtain ⟨c, hc_pos, hc_Θ⟩ : ∃ c > 0, ∃ δ > 0, ∀ t, |t - t₀| < δ → t ∈ Set.Icc γ.a γ.b → c * (t - t₀) ^ 2 ≤ (γ.toFun t).re ^ 2 + (γ.toFun t).im ^ 2 ∧ (γ.toFun t).re ^ 2 + (γ.toFun t).im ^ 2 ≤ (1 / c) * (t - t₀) ^ 2 := by
    field_simp
    obtain ⟨c, hc_pos, hc_θ⟩ : ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ δ > 0, ∀ t, |t - t₀| < δ → t ∈ Set.Icc γ.a γ.b → c * (t - t₀) ^ 2 ≤ (γ.toFun t).re ^ 2 + (γ.toFun t).im ^ 2 ∧ (γ.toFun t).re ^ 2 + (γ.toFun t).im ^ 2 ≤ C * (t - t₀) ^ 2 := by
      have := denominator_Theta_squared γ t₀
      by_cases ht₀ : t₀ ∈ Set.Icc γ.a γ.b
      · exact this ht₀ hγ_zero
      · obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ t, |t - t₀| < δ → t ∉ Set.Icc γ.a γ.b := by
          exact Metric.mem_nhds_iff.mp ( IsOpen.mem_nhds ( isOpen_compl_iff.mpr <| isClosed_Icc ) ht₀ )
        exact ⟨ 1, 1, by norm_num, by norm_num, δ, hδ_pos, fun t ht ht' => False.elim <| hδ t ht ht' ⟩
    use min c ( hc_pos⁻¹ ), lt_min hc_θ.left ( inv_pos.mpr hc_θ.right.left ), hc_θ.right.right.choose, hc_θ.right.right.choose_spec.left
    intro t ht ht'; constructor <;> cases min_cases c hc_pos⁻¹ <;> nlinarith [ hc_θ.2.2.choose_spec.2 t ht ht', inv_pos.2 hc_θ.2.1, mul_inv_cancel₀ ( ne_of_gt hc_θ.2.1 ), mul_div_cancel₀ ( ( t - t₀ ) ^ 2 ) ( ne_of_gt ( lt_min hc_θ.1 ( inv_pos.2 hc_θ.2.1 ) ) ) ]
  obtain ⟨ δ, hδ_pos, hδ ⟩ := hc_Θ
  obtain ⟨ C, hC_pos, hC ⟩ : ∃ C > 0, ∀ t, |t - t₀| < 1 → t ∈ Set.Icc γ.a γ.b → |(γ.toFun t).re * (deriv γ.toFun t).im - (γ.toFun t).im * (deriv γ.toFun t).re| ≤ C * (t - t₀)^2 := by
    exact numerator_big_O_squared γ t₀ hγ_zero hLip
  refine' ⟨ C / c, Min.min δ 1, lt_min hδ_pos zero_lt_one, fun t ht ht' => _ ⟩
  by_cases h : t = t₀ <;> simp_all +decide [ windingNumberIntegrand ]
  · positivity
  · rw [ abs_div ]
    rw [ div_le_div_iff₀ ] <;> try positivity
    · cases abs_cases ( ( γ.toFun t |> Complex.re ) ^ 2 + ( γ.toFun t |> Complex.im ) ^ 2 ) <;> nlinarith [ hC t ht.2 ht'.1 ht'.2, hδ t ht.1 ht'.1 ht'.2, mul_inv_cancel₀ ( ne_of_gt hc_pos ) ]
    · exact abs_pos.mpr ( by nlinarith [ hδ t ht.1 ht'.1 ht'.2, mul_self_pos.mpr ( sub_ne_zero.mpr h ) ] )

/-- Global boundedness of the integrand on [a,b]. -/
theorem windingNumberIntegrand_bounded_global
    (hLip : LipschitzOnWith 1 (deriv γ.toFun) (Icc γ.a γ.b)) :
    ∃ M : ℝ, ∀ t ∈ Icc γ.a γ.b, |windingNumberIntegrand γ.toFun t| ≤ M := by
  -- Combine:
  -- 1. Near each zero: use windingNumberIntegrand_bounded_near_zero
  -- 2. Away from zeros: γ ≠ 0 so denominator is bounded away from 0
  -- 3. Finitely many zeros (by finiteness theorem)
  have h_bounded : ∀ t₀ ∈ Set.Icc γ.a γ.b, ∃ δ > 0, ∃ M : ℝ, ∀ t, |t - t₀| < δ ∧ t ∈ Set.Icc γ.a γ.b → |windingNumberIntegrand γ.toFun t| ≤ M := by
    intros t₀ ht₀
    by_cases hγ_zero : γ.toFun t₀ = 0
    · have := windingNumberIntegrand_bounded_near_zero γ t₀ hγ_zero hLip
      aesop
    · -- Since γ is continuous at t₀ and γ(t₀) ≠ 0, there exists a neighborhood around t₀ where γ(t) is bounded away from zero.
      obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ t, |t - t₀| < δ → t ∈ Set.Icc γ.a γ.b → ‖γ.toFun t‖ ≥ ‖γ.toFun t₀‖ / 2 := by
        have := Metric.continuousOn_iff.mp ( show ContinuousOn ( fun t => ‖γ.toFun t‖ ) ( Set.Icc γ.a γ.b ) from ContinuousOn.norm ( γ.continuous_toFun ) ) t₀ ht₀
        exact Exists.elim ( this ( ‖γ.toFun t₀‖ / 2 ) ( half_pos ( norm_pos_iff.mpr hγ_zero ) ) ) fun δ hδ => ⟨ δ, hδ.1, fun t ht₁ ht₂ => by linarith [ abs_lt.mp ( hδ.2 t ht₂ ht₁ ) ] ⟩
      -- Since γ is continuous at t₀ and γ(t₀) ≠ 0, the derivative of γ is bounded near t₀.
      obtain ⟨M, hM⟩ : ∃ M > 0, ∀ t, |t - t₀| < δ → t ∈ Set.Icc γ.a γ.b → ‖deriv γ.toFun t‖ ≤ M := by
        have := hLip.norm_sub_le
        use ‖deriv γ.toFun t₀‖ + δ + 1
        exact ⟨ by positivity, fun t ht₁ ht₂ => by have := this ht₂ ht₀; norm_num at *; linarith [ norm_sub_norm_le ( deriv γ.toFun t ) ( deriv γ.toFun t₀ ), abs_lt.mp ht₁ ] ⟩
      refine' ⟨ δ, hδ_pos, 2 * M / ‖γ.toFun t₀‖, fun t ht => _ ⟩
      -- Using the bounds on the numerator and denominator, we can show that the integrand is bounded.
      have h_integrand_bound : |(γ.toFun t).re * (deriv γ.toFun t).im - (γ.toFun t).im * (deriv γ.toFun t).re| ≤ M * ‖γ.toFun t‖ := by
        have h_integrand_bound : |(γ.toFun t).re * (deriv γ.toFun t).im - (γ.toFun t).im * (deriv γ.toFun t).re| ≤ ‖γ.toFun t‖ * ‖deriv γ.toFun t‖ := by
          norm_num [ Complex.normSq, Complex.norm_def ]
          rw [ ← Real.sqrt_mul <| by nlinarith ] ; exact Real.abs_le_sqrt <| by linarith [ sq_nonneg ( ( γ.toFun t |> Complex.re ) * ( deriv γ.toFun t |> Complex.re ) + ( γ.toFun t |> Complex.im ) * ( deriv γ.toFun t |> Complex.im ) ) ]
        nlinarith [ hM.2 t ht.1 ht.2, norm_nonneg ( γ.toFun t ) ]
      rw [ windingNumberIntegrand, abs_div ]
      rw [ div_le_div_iff₀ ] <;> norm_num [ Complex.normSq, Complex.norm_def ] at *
      · rw [ abs_of_nonneg ( by nlinarith : 0 ≤ ( γ.toFun t |> Complex.re ) ^ 2 + ( γ.toFun t |> Complex.im ) ^ 2 ) ]
        have := hδ t ht.1 ht.2.1 ht.2.2
        nlinarith [ abs_nonneg ( ( γ.toFun t |> Complex.re ) * ( deriv γ.toFun t |> Complex.im ) - ( γ.toFun t |> Complex.im ) * ( deriv γ.toFun t |> Complex.re ) ), Real.sqrt_nonneg ( ( γ.toFun t |> Complex.re ) * ( γ.toFun t |> Complex.re ) + ( γ.toFun t |> Complex.im ) * ( γ.toFun t |> Complex.im ) ), Real.mul_self_sqrt ( add_nonneg ( mul_self_nonneg ( γ.toFun t |> Complex.re ) ) ( mul_self_nonneg ( γ.toFun t |> Complex.im ) ) ) ]
      · contrapose! hδ
        exact ⟨ t, ht.1, ht.2.1, ht.2.2, by rw [ Real.sqrt_eq_zero_of_nonpos ( by nlinarith ) ] ; exact div_pos ( Real.sqrt_pos.mpr ( by exact not_le.mp fun h => hγ_zero <| by refine' Complex.ext _ _ <;> norm_num <;> nlinarith ) ) zero_lt_two ⟩
      · exact not_le.mp fun h => hγ_zero <| by refine' Complex.ext _ _ <;> norm_num <;> nlinarith
  choose! δ hδ M hM using fun t ht => h_bounded t ht
  have h_compact : IsCompact (Set.Icc γ.a γ.b) := by
    exact CompactIccSpace.isCompact_Icc
  have := h_compact.elim_nhds_subcover ( fun t => Metric.ball t ( δ t ) ) ( fun t ht => Metric.ball_mem_nhds t ( hδ t ht ) )
  obtain ⟨ t, ht₁, ht₂ ⟩ := this; exact ⟨ ∑ x ∈ t, |M x| + 1, fun x hx => by rcases Set.mem_iUnion₂.mp ( ht₂ hx ) with ⟨ y, hy₁, hy₂ ⟩ ; exact le_trans ( hM y ( ht₁ y hy₁ ) x ⟨ hy₂, hx ⟩ ) ( by linarith [ Finset.single_le_sum ( fun x _ => abs_nonneg ( M x ) ) hy₁, abs_le.mp ( Finset.single_le_sum ( fun x _ => abs_nonneg ( M x ) ) hy₁ ) ] ) ⟩

/-! ## Limit at a Zero (for C² curves) -/

/-- The signed curvature of a complex-valued curve at a point.
    This is the complex version of signedCurvature from LHopital.lean -/
def signedCurvatureComplex (γ : ℝ → ℂ) (t : ℝ) : ℝ :=
  let v := deriv γ t
  let a := deriv (deriv γ) t
  (v.re * a.im - v.im * a.re) / (v.re^2 + v.im^2)^(3/2 : ℝ)


/-- For a C² curve with nonzero derivative, the winding number integrand has a limit at a zero.

    **Theorem**: If γ is C² near t₀ with γ(t₀) = 0 and γ'(t₀) ≠ 0, then
    lim_{t→t₀} (x·ẏ - y·ẋ)/(x² + y²) = (1/2)·κ_γ(t₀)·|γ'(t₀)|

    where κ_γ is the signed curvature.

    **Proof**: Using Taylor expansion to second order:
    x(t) = (t-t₀)·ẋ(t₀) + (1/2)(t-t₀)²·ẍ(t₀) + o((t-t₀)²)
    y(t) = (t-t₀)·ẏ(t₀) + (1/2)(t-t₀)²·ÿ(t₀) + o((t-t₀)²)

    Then:
    x·ẏ - y·ẋ = (1/2)(t-t₀)²(ẋ(t₀)·ÿ(t₀) - ẏ(t₀)·ẍ(t₀)) + o((t-t₀)²)
    x² + y² = (t-t₀)²(ẋ(t₀)² + ẏ(t₀)²) + o((t-t₀)²)

    The limit is (ẋ·ÿ - ẏ·ẍ)/(2(ẋ² + ẏ²)) = (1/2)·κ·|γ'|.

    Note: This theorem requires γ'(t₀) ≠ 0. When γ'(t₀) = 0, the limit formula
    (1/2)*κ*|γ'| = 0 may not capture the actual limiting behavior, which depends
    on higher-order derivatives. For immersions, γ'(t₀) ≠ 0 always holds.
-/
theorem windingNumberIntegrand_limit_at_zero (t₀ : ℝ)
    (hγ_zero : γ.toFun t₀ = 0)
    (hC2 : ContDiffAt ℝ 2 γ.toFun t₀)
    (hv_ne : deriv γ.toFun t₀ ≠ 0) :
    let κ := signedCurvatureComplex γ.toFun t₀
    let v := ‖deriv γ.toFun t₀‖
    Tendsto (windingNumberIntegrand γ.toFun) (𝓝[≠] t₀) (𝓝 ((1/2) * κ * v)) := by
  -- With hv_ne : deriv γ.toFun t₀ ≠ 0, we can proceed directly.
  -- Second-order Taylor expansion gives:
  -- γ(t) = (t-t₀)·γ'(t₀) + (t-t₀)²/2·γ''(t₀) + o((t-t₀)²)
  -- since γ(t₀) = 0.
  --
  -- Setting h = t - t₀, v = γ'(t₀), a = γ''(t₀):
  -- Numerator x·y' - y·x' = h²/2·(vx·ay - vy·ax) + o(h²)
  -- Denominator x² + y² = h²·(vx² + vy²) + o(h²)
  --
  -- The limit as h → 0 is:
  -- (vx·ay - vy·ax)/(2(vx² + vy²))
  --
  -- This equals (1/2)·κ·|γ'| where κ = signedCurvatureComplex γ t₀.
  intro κ v_norm
  -- We use L'Hopital's rule twice since both numerator and denominator vanish at t₀,
  -- and their first derivatives also vanish at t₀.
  --
  -- Define:
  -- f(t) = x(t)·y'(t) - y(t)·x'(t)  (numerator)
  -- g(t) = x(t)² + y(t)²  (denominator)
  --
  -- At t₀ where γ(t₀) = 0: f(t₀) = 0, g(t₀) = 0
  -- f'(t) = x'·y' + x·y'' - y'·x' - y·x'' = x·y'' - y·x''
  -- g'(t) = 2x·x' + 2y·y'
  -- At t₀: f'(t₀) = 0, g'(t₀) = 0
  --
  -- f''(t) = x'·y'' + x·y''' - y'·x'' - y·x'''
  -- g''(t) = 2(x')² + 2x·x'' + 2(y')² + 2y·y''
  -- At t₀: f''(t₀) = x'·y'' - y'·x'', g''(t₀) = 2((x')² + (y')²) = 2|v|²
  --
  -- By L'Hopital (applied twice):
  -- lim f/g = lim f'/g' = lim f''/g'' = (x'·y'' - y'·x'') / (2|v|²)
  --
  -- This equals (1/2)·κ·|v| by the definition of signed curvature:
  -- κ = (v.re * a.im - v.im * a.re) / |v|³
  -- So (1/2)·κ·|v| = (v.re * a.im - v.im * a.re) / (2|v|²)
  --                = (x'(t₀)·y''(t₀) - y'(t₀)·x''(t₀)) / (2|v|²)
  --                = f''(t₀) / g''(t₀)
  --
  -- The full proof requires:
  -- 1. Extract differentiability from ContDiffAt 2
  -- 2. Apply L'Hopital's rule (HasDerivAt.lhopital_zero_nhdsNE from Mathlib)
  -- 3. Show the derivative ratio also has a 0/0 form requiring second application
  -- 4. Verify the algebraic identity
  --
  -- This is technically complex but mathematically straightforward.
  --
  -- The proof uses L'Hopital's rule twice. Let:
  --   f(t) = x(t)*y'(t) - y(t)*x'(t)  (numerator of windingNumberIntegrand)
  --   g(t) = x(t)^2 + y(t)^2          (denominator)
  -- where x = Re(gamma), y = Im(gamma).
  --
  -- At t₀ where gamma(t₀) = 0:
  --   f(t₀) = 0, g(t₀) = 0  (0/0 form)
  --
  -- First derivatives:
  --   f'(t) = x*y'' - y*x''  (since x'*y' - y'*x' = 0)
  --   g'(t) = 2*x*x' + 2*y*y'
  -- At t₀: f'(t₀) = 0, g'(t₀) = 0 (still 0/0)
  --
  -- Second derivatives at t₀:
  --   f''(t₀) = x'(t₀)*y''(t₀) - y'(t₀)*x''(t₀)
  --   g''(t₀) = 2*(x'(t₀)^2 + y'(t₀)^2) = 2*|gamma'(t₀)|^2 != 0
  --
  -- By L'Hopital applied twice:
  --   lim f/g = f''(t₀)/g''(t₀)
  --           = (x'*y'' - y'*x'') / (2*(x'^2 + y'^2))
  --           = (v.re * a.im - v.im * a.re) / (2*|v|^2)
  -- where v = gamma'(t₀), a = gamma''(t₀).
  --
  -- This equals (1/2)*kappa*|v| since:
  --   kappa = (v.re * a.im - v.im * a.re) / |v|^3
  -- so (1/2)*kappa*|v| = (v.re * a.im - v.im * a.re) / (2*|v|^2)
  --
  -- The formal proof requires:
  -- 1. Extract differentiability from ContDiffAt 2
  -- 2. Apply deriv.lhopital_zero_nhdsNE twice
  -- 3. Verify the algebraic identity
  --
  -- This requires careful composition of real projections with derivatives.
  --
  -- Strategy: Use the fact that for C² functions with nonzero first derivative at a zero,
  -- the Taylor expansion gives:
  --   gamma(t) = (t - t₀) * gamma'(t₀) + O((t - t₀)²)
  --   gamma'(t) = gamma'(t₀) + O(t - t₀)
  --
  -- Numerator: x*y' - y*x' ≈ (t-t₀)*v.re * v.im - (t-t₀)*v.im * v.re + O((t-t₀)²)
  --                        = 0 + O((t-t₀)²)   (leading terms cancel!)
  --
  -- For the O((t-t₀)²) term, using second-order Taylor:
  --   x(t) ≈ (t-t₀)*v.re + (t-t₀)²/2 * a.re
  --   y(t) ≈ (t-t₀)*v.im + (t-t₀)²/2 * a.im
  --   x'(t) ≈ v.re + (t-t₀) * a.re
  --   y'(t) ≈ v.im + (t-t₀) * a.im
  --
  -- Numerator expanded to O((t-t₀)²):
  --   x*y' - y*x' = ((t-t₀)*v.re + (t-t₀)²/2*a.re) * (v.im + (t-t₀)*a.im)
  --               - ((t-t₀)*v.im + (t-t₀)²/2*a.im) * (v.re + (t-t₀)*a.re)
  --               = (t-t₀)*v.re*v.im + (t-t₀)²*v.re*a.im + (t-t₀)²/2*a.re*v.im
  --               - (t-t₀)*v.im*v.re - (t-t₀)²*v.im*a.re - (t-t₀)²/2*a.im*v.re + O((t-t₀)³)
  --               = (t-t₀)²*(v.re*a.im - v.im*a.re) + O((t-t₀)²)/2 terms
  --               = (t-t₀)²/2 * (v.re*a.im - v.im*a.re) + O((t-t₀)³)
  --
  -- Denominator: x² + y² = (t-t₀)²*(v.re² + v.im²) + O((t-t₀)³)
  --
  -- Ratio: [(t-t₀)²/2 * (v.re*a.im - v.im*a.re)] / [(t-t₀)²*(v.re² + v.im²)]
  --      = (v.re*a.im - v.im*a.re) / (2*(v.re² + v.im²))
  --      = (1/2) * kappa * |v|   (by definition of kappa)
  --
  -- This calculation shows the limit equals (1/2) * κ * v_norm.
  -- The formal proof uses L'Hopital twice or direct Taylor expansion.
  --
  -- For the full formal proof, we would need to:
  -- 1. Show the derivatives of the numerator and denominator functions
  -- 2. Verify the L'Hopital conditions (non-vanishing derivative of denominator's derivative)
  -- 3. Complete the algebraic verification
  --
  -- The mathematical content is complete in the comments above.
  -- The Lean formalization requires careful manipulation of ContDiffAt derivatives.
  --
  -- Attempt using direct limit argument:
  -- We show that the function approaches the limit using the Taylor expansion structure.
  --
  -- From ContDiffAt ℝ 2 γ t₀, we have:
  -- 1. γ is differentiable with continuous derivative
  -- 2. deriv γ is differentiable at t₀
  --
  -- The numerator f(t) = x(t)*y'(t) - y(t)*x'(t) and denominator g(t) = x(t)² + y(t)²
  -- both have f(t₀) = g(t₀) = 0.
  --
  -- For the limit, we use that f(t)/g(t) → L when:
  -- - f(t) = α(t-t₀)² + o((t-t₀)²)
  -- - g(t) = β(t-t₀)² + o((t-t₀)²) with β ≠ 0
  -- - Then f/g → α/β
  --
  -- Here:
  -- - α = (v.re * a.im - v.im * a.re) / 2
  -- - β = v.re² + v.im² = |γ'(t₀)|² > 0
  -- - α/β = (v.re * a.im - v.im * a.re) / (2 * (v.re² + v.im²)) = (1/2) * κ * |γ'(t₀)|
  --
  -- We use Filter.Tendsto and the algebraic structure.
  -- Define the limit value
  let L := (1/2 : ℝ) * κ * v_norm
  -- The main estimate: near t₀, the integrand is close to L
  -- This follows from the Taylor expansion structure.
  -- We use the fact that for C² functions, the ratio converges.
  --
  -- Full proof would use:
  -- 1. Taylor expansion of γ around t₀
  -- 2. Algebraic manipulation of the resulting expressions
  -- 3. Standard limit theorems
  --
  -- Due to the technical complexity of formalizing Taylor expansions and
  -- the careful algebra needed, we provide a structured proof outline.
  --
  -- Key steps:
  -- 1. Show f, g are C¹ near t₀ (from γ being C²)
  -- 2. Compute f'(t₀), g'(t₀) and show both are 0
  -- 3. Show f', g' are differentiable near t₀ with g''(t₀) ≠ 0
  -- 4. Apply L'Hopital twice
  --
  -- Define the numerator and denominator
  let num := fun t => (γ.toFun t).re * (deriv γ.toFun t).im - (γ.toFun t).im * (deriv γ.toFun t).re
  let den := fun t => (γ.toFun t).re ^ 2 + (γ.toFun t).im ^ 2
  -- Rewrite the goal in terms of num/den
  have h_eq : windingNumberIntegrand γ.toFun = fun t => num t / den t := by
    ext t
    simp only [windingNumberIntegrand, num, den]
  rw [h_eq]
  -- The limit value is (1/2) * κ * v_norm
  -- For the formal proof, we would apply L'Hopital twice.
  -- The key steps are:
  -- 1. num(t₀) = 0, den(t₀) = 0 (first 0/0 form)
  -- 2. (deriv num)(t₀) = 0, (deriv den)(t₀) = 0 (second 0/0 form)
  -- 3. (deriv (deriv num))(t₀) / (deriv (deriv den))(t₀) = (1/2) * κ * v_norm
  --
  -- The L'Hopital rule application requires showing:
  -- - num, den are differentiable near t₀
  -- - deriv den ≠ 0 near t₀ (except at t₀)
  -- - deriv (deriv den)(t₀) ≠ 0
  --
  -- For the second application:
  -- - deriv num, deriv den are differentiable near t₀
  -- - deriv (deriv den) ≠ 0 near t₀
  --
  -- These conditions follow from ContDiffAt ℝ 2 and the nonzero derivative hypothesis.
  --
  -- We prove this using the Taylor expansion structure and limit computation.
  -- First, extract the key properties from ContDiffAt ℝ 2
  have hγ_diff : DifferentiableAt ℝ γ.toFun t₀ := hC2.differentiableAt one_le_two
  -- Get the C¹ hypothesis on γ
  have hγ_C1 : ContDiffAt ℝ 1 γ.toFun t₀ := hC2.of_le one_le_two
  -- The derivative of γ at t₀ is nonzero, which means |γ'(t₀)|² > 0
  have h_normSq_pos : (deriv γ.toFun t₀).re ^ 2 + (deriv γ.toFun t₀).im ^ 2 > 0 := by
    have h1 : (deriv γ.toFun t₀).re ^ 2 + (deriv γ.toFun t₀).im ^ 2 = Complex.normSq (deriv γ.toFun t₀) := by
      rw [Complex.normSq_apply]; ring
    rw [h1]
    exact Complex.normSq_pos.mpr hv_ne
  -- Define shorthand for key values
  let v := deriv γ.toFun t₀  -- velocity
  let a := iteratedDeriv 2 γ.toFun t₀  -- acceleration (second derivative)
  -- The target limit value
  let target := (1/2 : ℝ) * κ * v_norm
  -- We need to show: Tendsto (fun t => num t / den t) (𝓝[≠] t₀) (𝓝 target)
  -- First show den t₀ = 0 and num t₀ = 0
  have h_den_zero : den t₀ = 0 := by
    simp only [den, hγ_zero, Complex.zero_re, Complex.zero_im, sq, mul_zero, add_zero]
  have h_num_zero : num t₀ = 0 := by
    simp only [num, hγ_zero, Complex.zero_re, Complex.zero_im, zero_mul, mul_zero, sub_self]
  -- The mathematical argument:
  -- For C² functions, γ(t) = (t-t₀)·v + (t-t₀)²/2·a + o((t-t₀)²)
  -- and γ'(t) = v + (t-t₀)·a + o(t-t₀)
  --
  -- The numerator x·y' - y·x' = (t-t₀)²/2 · (v.re·a.im - v.im·a.re) + o((t-t₀)²)
  -- The denominator x² + y² = (t-t₀)² · (v.re² + v.im²) + o((t-t₀)²)
  --
  -- So the ratio tends to:
  -- (v.re·a.im - v.im·a.re) / (2·(v.re² + v.im²))
  -- = (1/2) · κ · |v|
  --
  -- The proof uses Filter.Tendsto with L'Hopital's rule applied twice.
  -- For a complete formal proof, we would:
  -- 1. Apply L'Hopital to get f/g → f'/g' (both f(t₀) = g(t₀) = 0)
  -- 2. Show f'(t₀) = g'(t₀) = 0 (first derivatives also vanish)
  -- 3. Apply L'Hopital again to get f'/g' → f''/g''
  -- 4. Compute f''(t₀)/g''(t₀) = target
  --
  -- The key observation is that:
  -- - num(t₀) = 0 (since γ(t₀) = 0)
  -- - (deriv num)(t₀) = 0 (cross terms cancel: x'·y' - y'·x' = 0)
  -- - den(t₀) = 0 (since γ(t₀) = 0)
  -- - (deriv den)(t₀) = 0 (since x(t₀) = y(t₀) = 0)
  -- - (iteratedDeriv 2 den)(t₀) = 2(v.re² + v.im²) ≠ 0 (by hv_ne)
  --
  -- The ratio f''(t₀)/g''(t₀) equals (v.re·a.im - v.im·a.re)/(2·(v.re² + v.im²))
  -- which is exactly (1/2) * κ * v_norm by definition of signedCurvatureComplex.
  --
  -- The proof strategy is to use the infrastructure lemma windingNumberIntegrand_limit_at_zero'
  -- which handles the double L'Hopital application for real-valued x and y functions.
  -- We would:
  -- 1. Define x' = Complex.re ∘ γ and y' = Complex.im ∘ γ
  -- 2. Show x'(t₀) = y'(t₀) = 0 (from hγ_zero)
  -- 3. Show deriv x' t₀ ≠ 0 or deriv y' t₀ ≠ 0 (from hv_ne)
  -- 4. Show (x', y') is C² at t₀ (from hC2)
  -- 5. Apply windingNumberIntegrand_limit_at_zero' to get the limit
  -- 6. Verify the limit formulas match (algebraic identity)
  --
  -- The key algebraic identity is that for complex z = x + iy:
  -- windingNumberIntegrand z = (x * (deriv z).im - y * (deriv z).re) / (x² + y²)
  --                         = (x * deriv y - y * deriv x) / (x² + y²)
  -- where deriv y = (deriv z).im and deriv x = (deriv z).re for the component functions.
  --
  -- The curvature formulas also match via the identity relating
  -- signedCurvatureComplex to signedCurvature on components.
  --
  -- This is a standard but technical verification; the infrastructure handles the
  -- core L'Hopital argument via windingNumberIntegrand_limit_at_zero'.
  --
  -- Define the real component functions
  let x' := Complex.re ∘ γ.toFun
  let y' := Complex.im ∘ γ.toFun
  -- Show the hypotheses of windingNumberIntegrand_limit_at_zero'
  have hx_zero : x' t₀ = 0 := by simp only [x', Function.comp_apply, hγ_zero, Complex.zero_re]
  have hy_zero : y' t₀ = 0 := by simp only [y', Function.comp_apply, hγ_zero, Complex.zero_im]
  -- Derivative nonzero condition
  have h_deriv_ne : deriv x' t₀ ≠ 0 ∨ deriv y' t₀ ≠ 0 := by
    -- deriv (Complex.re ∘ γ) = (deriv γ).re (for differentiable γ)
    have hx'_deriv : deriv x' t₀ = (deriv γ.toFun t₀).re := by
      simp only [x']
      exact deriv_re_comp_of_differentiable hγ_diff
    have hy'_deriv : deriv y' t₀ = (deriv γ.toFun t₀).im := by
      simp only [y']
      exact deriv_im_comp_of_differentiable hγ_diff
    rw [hx'_deriv, hy'_deriv]
    by_contra h
    push_neg at h
    have h_eq_zero : deriv γ.toFun t₀ = 0 := Complex.ext h.1 h.2
    exact hv_ne h_eq_zero
  -- C² condition for the pair (x', y')
  have hC2_pair : ContDiffAt ℝ 2 (fun t => (x' t, y' t)) t₀ := by
    -- (x', y') = (Complex.re ∘ γ, Complex.im ∘ γ)
    -- This is C² since γ is C² and re, im are smooth (linear)
    -- reCLM : ℂ →L[ℝ] ℝ is a smooth map (linear), so re ∘ γ is C² when γ is C²
    have h1 : ContDiffAt ℝ 2 (fun t => (γ.toFun t).re) t₀ := by
      have hRe : ContDiff ℝ 2 (fun z : ℂ => z.re) :=
        Complex.reCLM.contDiff
      exact hRe.comp_contDiffAt hC2
    have h2 : ContDiffAt ℝ 2 (fun t => (γ.toFun t).im) t₀ := by
      have hIm : ContDiff ℝ 2 (fun z : ℂ => z.im) :=
        Complex.imCLM.contDiff
      exact hIm.comp_contDiffAt hC2
    simp only [x', y', Function.comp_apply]
    exact h1.prodMk h2
  -- Apply the infrastructure lemma
  have h_limit := windingNumberIntegrand_limit_at_zero' hC2_pair hx_zero hy_zero h_deriv_ne
  -- Now we need to show that the limit formula matches
  -- The infrastructure gives us limit of (x * deriv y - y * deriv x) / (x² + y²)
  -- We need to show this equals our num/den and the limit values match
  -- First, show the integrand formulas match
  have h_integrand_eq : ∀ t, num t / den t =
      (x' t * deriv y' t - y' t * deriv x' t) / (x' t^2 + y' t^2) := by
    intro t
    simp only [num, den, x', y', Function.comp_apply]
    -- Need to show: (γ t).re * (deriv γ t).im - (γ t).im * (deriv γ t).re
    --             = (γ t).re * deriv (Im ∘ γ) t - (γ t).im * deriv (Re ∘ γ) t
    -- For this we need deriv (Im ∘ γ) t = (deriv γ t).im when γ is differentiable
    by_cases hγ_diff_t : DifferentiableAt ℝ γ.toFun t
    · have h_re_deriv : deriv (Complex.re ∘ γ.toFun) t = (deriv γ.toFun t).re :=
        deriv_re_comp_of_differentiable hγ_diff_t
      have h_im_deriv : deriv (Complex.im ∘ γ.toFun) t = (deriv γ.toFun t).im :=
        deriv_im_comp_of_differentiable hγ_diff_t
      rw [h_re_deriv, h_im_deriv]
    · -- If γ is not differentiable at t, both sides are 0 (or numerator is 0)
      have h_deriv_zero : deriv γ.toFun t = 0 := deriv_zero_of_not_differentiableAt hγ_diff_t
      -- For the non-differentiable case, we need to be careful.
      -- The composed functions re ∘ γ and im ∘ γ might still be differentiable.
      -- However, we can show directly that both expressions equal 0.
      simp [h_deriv_zero]
  -- Show the limit values match
  -- Infrastructure limit: (1/2) * κ_infra * v_norm_infra where
  --   κ_infra = (deriv x' t₀ * iteratedDeriv 2 y' t₀ - deriv y' t₀ * iteratedDeriv 2 x' t₀) /
  --             (deriv x' t₀^2 + deriv y' t₀^2)^(3/2)
  --   v_norm_infra = sqrt(deriv x' t₀^2 + deriv y' t₀^2)
  -- Our limit: (1/2) * κ * v_norm where
  --   κ = signedCurvatureComplex γ t₀
  --   v_norm = ‖deriv γ t₀‖
  -- Need to show these are equal
  have h_limit_eq : (1 / 2 : ℝ) * κ * v_norm =
      (1 / 2) * ((deriv x' t₀ * iteratedDeriv 2 y' t₀ - deriv y' t₀ * iteratedDeriv 2 x' t₀) /
                 (deriv x' t₀^2 + deriv y' t₀^2)^(3/2 : ℝ)) *
      Real.sqrt (deriv x' t₀^2 + deriv y' t₀^2) := by
    -- Expand κ and v_norm definitions
    simp only [κ, v_norm, signedCurvatureComplex]
    -- deriv x' t₀ = v.re, deriv y' t₀ = v.im
    have hx'_deriv : deriv x' t₀ = v.re := by
      simp only [x', v]
      exact deriv_re_comp_of_differentiable hγ_diff
    have hy'_deriv : deriv y' t₀ = v.im := by
      simp only [y', v]
      exact deriv_im_comp_of_differentiable hγ_diff
    -- iteratedDeriv 2 x' t₀ = a.re, iteratedDeriv 2 y' t₀ = a.im
    -- For a CLM L and C^n function f: iteratedDeriv n (L ∘ f) = L (iteratedDeriv n f)
    have hx'_second : iteratedDeriv 2 x' t₀ = a.re := by
      simp only [x', a]
      -- iteratedDeriv 2 (re ∘ γ) = re (iteratedDeriv 2 γ) (for C² γ)
      have h_C2_deriv : ContDiffAt ℝ 1 (deriv γ.toFun) t₀ := by
        have := hC2.contDiffAt_iteratedDeriv (m := 1) one_le_two
        simp only [iteratedDeriv_one] at this
        exact this
      have h_deriv_diff : DifferentiableAt ℝ (deriv γ.toFun) t₀ :=
        h_C2_deriv.differentiableAt le_rfl
      -- iteratedDeriv 2 = deriv ∘ deriv, so iteratedDeriv 2 (re ∘ γ) = deriv (deriv (re ∘ γ))
      -- = deriv (re ∘ deriv γ) = re (deriv (deriv γ)) = re (iteratedDeriv 2 γ)
      calc iteratedDeriv 2 (Complex.re ∘ γ.toFun) t₀
          = deriv (deriv (Complex.re ∘ γ.toFun)) t₀ := by simp [iteratedDeriv_succ]
        _ = deriv (fun t => (deriv γ.toFun t).re) t₀ := by
            congr 1
            ext t
            by_cases ht : DifferentiableAt ℝ γ.toFun t
            · exact deriv_re_comp_of_differentiable ht
            · simp [deriv_zero_of_not_differentiableAt ht,
                    deriv_zero_of_not_differentiableAt (fun h => ht (Complex.reCLM.differentiableAt.comp t h |>.of_comp_right_of_surjective (fun _ => ⟨_, rfl⟩) |> fun _ => ht h))]
        _ = (deriv (deriv γ.toFun) t₀).re := by
            exact deriv_re_comp_of_differentiable h_deriv_diff
        _ = (iteratedDeriv 2 γ.toFun t₀).re := by simp [iteratedDeriv_succ]
    have hy'_second : iteratedDeriv 2 y' t₀ = a.im := by
      simp only [y', a]
      have h_C2_deriv : ContDiffAt ℝ 1 (deriv γ.toFun) t₀ := by
        have := hC2.contDiffAt_iteratedDeriv (m := 1) one_le_two
        simp only [iteratedDeriv_one] at this
        exact this
      have h_deriv_diff : DifferentiableAt ℝ (deriv γ.toFun) t₀ :=
        h_C2_deriv.differentiableAt le_rfl
      calc iteratedDeriv 2 (Complex.im ∘ γ.toFun) t₀
          = deriv (deriv (Complex.im ∘ γ.toFun)) t₀ := by simp [iteratedDeriv_succ]
        _ = deriv (fun t => (deriv γ.toFun t).im) t₀ := by
            congr 1
            ext t
            by_cases ht : DifferentiableAt ℝ γ.toFun t
            · exact deriv_im_comp_of_differentiable ht
            · simp [deriv_zero_of_not_differentiableAt ht,
                    deriv_zero_of_not_differentiableAt (fun h => ht (Complex.imCLM.differentiableAt.comp t h |>.of_comp_right_of_surjective (fun _ => ⟨_, rfl⟩) |> fun _ => ht h))]
        _ = (deriv (deriv γ.toFun) t₀).im := by
            exact deriv_im_comp_of_differentiable h_deriv_diff
        _ = (iteratedDeriv 2 γ.toFun t₀).im := by simp [iteratedDeriv_succ]
    rw [hx'_deriv, hy'_deriv, hx'_second, hy'_second]
    -- v_norm = ‖v‖ = sqrt(v.re² + v.im²)
    have h_norm_eq : ‖deriv γ.toFun t₀‖ = Real.sqrt (v.re^2 + v.im^2) := by
      simp only [v]
      rw [Complex.norm_eq_abs, Complex.abs_apply, Real.sqrt_sq_eq_abs, abs_of_nonneg]
      · rfl
      · exact Complex.normSq_nonneg _
    rw [h_norm_eq]
  rw [h_limit_eq]
  -- Convert the goal using the integrand equality
  have h_tendsto_rewrite : Tendsto (fun t => num t / den t) (𝓝[≠] t₀)
      (𝓝 ((1 / 2) * ((deriv x' t₀ * iteratedDeriv 2 y' t₀ - deriv y' t₀ * iteratedDeriv 2 x' t₀) /
           (deriv x' t₀ ^ 2 + deriv y' t₀ ^ 2) ^ (3 / 2 : ℝ)) *
       Real.sqrt (deriv x' t₀ ^ 2 + deriv y' t₀ ^ 2))) := by
    have h_eq_fun : (fun t => num t / den t) = (fun t => (x' t * deriv y' t - y' t * deriv x' t) / (x' t^2 + y' t^2)) := by
      ext t; exact h_integrand_eq t
    rw [h_eq_fun]
    exact h_limit
  exact h_tendsto_rewrite

/-! ## Flatness Conditions -/

/-- A curve is flat of order n at t₀ if γ and its first n-1 derivatives vanish at t₀. -/
def FlatOfOrder (γ : ℝ → ℂ) (t₀ : ℝ) (n : ℕ) : Prop :=
  ∀ k < n, iteratedDeriv k γ t₀ = 0

/-- Note: The statement "FlatOfOrder γ t 1" means γ(t) = 0, NOT that γ can have zeros.
    This theorem as originally stated is FALSE - it would claim γ(t) = 0 for all t,
    which is not true for general piecewise C¹ curves.

    The correct statement would be about the maximum *possible* flatness order,
    not that every point has that flatness. -/
theorem piecewiseC1_flat_order_at_most_one (γ : PiecewiseC1Curve) (t : ℝ)
    (hγt_zero : γ.toFun t = 0) :
    FlatOfOrder γ.toFun t 1 := by
  intro k hk
  interval_cases k
  simp only [iteratedDeriv_zero]
  exact hγt_zero

/-- For immersions at a zero, the derivative is nonzero, so flatness order is exactly 1.

    Note: The first part now requires the hypothesis that γ(t₀) = 0. -/
theorem immersion_flat_order_one (γ : PiecewiseC1Immersion) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Icc γ.a γ.b) (ht₀_smooth : t₀ ∉ γ.toPiecewiseC1Curve.partition)
    (hγ_zero : γ.toFun t₀ = 0) :
    FlatOfOrder γ.toFun t₀ 1 ∧ ¬FlatOfOrder γ.toFun t₀ 2 := by
  constructor
  · -- Order 1: γ(t₀) = 0 by hypothesis
    intro k hk
    interval_cases k
    simp only [iteratedDeriv_zero]
    exact hγ_zero
  · -- Not order 2: derivative is nonzero
    intro h_flat_2
    have h_deriv_zero : deriv γ.toFun t₀ = 0 := by
      have := h_flat_2 1 (by norm_num)
      simp only [iteratedDeriv_one] at this
      exact this
    exact γ.deriv_ne_zero t₀ ht₀ ht₀_smooth h_deriv_zero

end
