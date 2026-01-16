/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import Mathlib.Analysis.Calculus.Taylor

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

/-! ## Numerator Estimate: O(t²) -/

/-- The numerator x·ẏ - y·ẋ near a zero.

    For γ with γ(t₀) = 0 and Lipschitz derivative:
    |x(t)·ẏ(t) - y(t)·ẋ(t)| ≤ C·(t - t₀)²

    **Proof**:
    Using x(t) = ∫_{t₀}^t ẋ(s) ds and y(t) = ∫_{t₀}^t ẏ(s) ds:

    x·ẏ - y·ẋ = (∫ẋ)·ẏ - (∫ẏ)·ẋ
              = ∫(ẋ(s) - ẋ(t))·ẏ(t) ds + ∫ẋ(t)·(ẏ(t) - ẏ(s)) ds

    Using Lipschitz: |ẋ(s) - ẋ(t)| ≤ L|s - t|
    The integral gives O((t - t₀)²).
-/
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
      sorry
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

/-- The signed curvature of a curve at a point. -/
def signedCurvature (γ : ℝ → ℂ) (t : ℝ) : ℝ :=
  let v := deriv γ t
  let a := deriv (deriv γ) t
  (v.re * a.im - v.im * a.re) / (v.re^2 + v.im^2)^(3/2 : ℝ)

/-- For a C² curve, the winding number integrand has a limit at a zero.

    **Theorem**: If γ is C² near t₀ with γ(t₀) = 0, then
    lim_{t→t₀} (x·ẏ - y·ẋ)/(x² + y²) = (1/2)·κ_γ(t₀)·|γ'(t₀)|

    where κ_γ is the signed curvature.

    **Proof**: Using Taylor expansion to second order:
    x(t) = (t-t₀)·ẋ(t₀) + (1/2)(t-t₀)²·ẍ(t₀) + o((t-t₀)²)
    y(t) = (t-t₀)·ẏ(t₀) + (1/2)(t-t₀)²·ÿ(t₀) + o((t-t₀)²)

    Then:
    x·ẏ - y·ẋ = (1/2)(t-t₀)²(ẋ(t₀)·ÿ(t₀) - ẏ(t₀)·ẍ(t₀)) + o((t-t₀)²)
    x² + y² = (t-t₀)²(ẋ(t₀)² + ẏ(t₀)²) + o((t-t₀)²)

    The limit is (ẋ·ÿ - ẏ·ẍ)/(2(ẋ² + ẏ²)) = (1/2)·κ·|γ'|.
-/
theorem windingNumberIntegrand_limit_at_zero (t₀ : ℝ)
    (hγ_zero : γ.toFun t₀ = 0)
    (hC2 : ContDiffAt ℝ 2 γ.toFun t₀) :
    let κ := signedCurvature γ.toFun t₀
    let v := ‖deriv γ.toFun t₀‖
    Tendsto (windingNumberIntegrand γ.toFun) (𝓝 t₀) (𝓝 ((1/2) * κ * v)) := by
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
  -- This equals (1/2)·κ·|γ'| where κ = signedCurvature γ t₀.
  --
  -- The proof requires:
  -- 1. Taylor expansion from ContDiffAt
  -- 2. Limit computation for the ratio
  -- 3. Algebraic simplification to the curvature formula
  --
  -- This is a standard calculus limit that follows from Taylor's theorem.
  intro κ v_norm
  -- The key is to show that near t₀, the integrand is close to the limit.
  -- For C² curves, we use the second-order Taylor expansion.
  --
  -- From hC2, we have γ(t) = γ(t₀) + (t-t₀)·γ'(t₀) + (t-t₀)²/2·γ''(t₀) + o((t-t₀)²)
  -- Since γ(t₀) = 0, this simplifies.
  --
  -- The full proof requires Taylor remainder bounds which involve significant machinery.
  -- The mathematical argument is outlined in the theorem documentation above.
  sorry

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
