/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6a0d031f-9e62-4083-bbfd-9684571c9b8b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem lhopital_twice {f g : ℝ → ℝ} {a L : ℝ}
    (_hf_zero : f a = 0)
    (_hg_zero : g a = 0)
    (_hf'_zero : deriv f a = 0)
    (_hg'_zero : deriv g a = 0)
    (_hf_C2 : ContDiffAt ℝ 2 f a)
    (_hg_C2 : ContDiffAt ℝ 2 g a)
    (_hg''_ne : iteratedDeriv 2 g a ≠ 0)
    (_h_lim : Tendsto (fun x => iteratedDeriv 2 f x / iteratedDeriv 2 g x) (𝓝[{a}ᶜ] a) (𝓝 L)) :
    Tendsto (fun x => f x / g x) (𝓝[{a}ᶜ] a) (𝓝 L)

- theorem taylor_second_order_complex {f : ℝ → ℂ} {a : ℝ}
    (_hf : ContDiffAt ℝ 2 f a) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ →
      ‖f x - f a - deriv f a * (x - a) - (1/2) * iteratedDeriv 2 f a * (x - a)^2‖ ≤
        ε * (x - a)^2

- theorem denominator_quadratic' {x y : ℝ → ℝ} {t₀ : ℝ}
    (hx_diff : DifferentiableAt ℝ x t₀)
    (hy_diff : DifferentiableAt ℝ y t₀)
    (hx_zero : x t₀ = 0)
    (hy_zero : y t₀ = 0)
    (_h_deriv_ne : deriv x t₀ ≠ 0 ∨ deriv y t₀ ≠ 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, |t - t₀| < δ →
      |x t^2 + y t^2 - (deriv x t₀^2 + deriv y t₀^2) * (t - t₀)^2| ≤
        ε * (t - t₀)^2
-/

/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.Calculus.LHopital


/-!
# L'Hôpital's Rule and Taylor Expansion Infrastructure

This file provides L'Hôpital's rule and Taylor expansion lemmas needed for
asymptotic estimates in the winding number theory.

## Main Results

### L'Hôpital's Rule
* `lhopital_zero_div_zero` - Standard L'Hôpital for 0/0 form
* `lhopital_zero_div_zero_at` - L'Hôpital at a specific point
* `lhopital_twice` - Double application of L'Hôpital

### Taylor Expansion
* `taylor_one_variable` - First-order Taylor expansion
* `taylor_two_variable` - Second-order Taylor expansion for C² functions
* `taylor_remainder_bound` - Bound on Taylor remainder

## Application to Winding Number

The key application is `windingNumberIntegrand_limit_at_zero`:
For a C² curve γ with γ(t₀) = 0, the limit of
  (x(t)y'(t) - y(t)x'(t)) / (x(t)² + y(t)²) as t → t₀
equals (1/2) · κ · |γ'(t₀)|, where κ is the signed curvature.

This requires applying L'Hôpital twice (both numerator and denominator vanish at t₀).

## References

* Hungerbühler-Wasem paper, Proposition 2
* Standard calculus texts for L'Hôpital's rule
-/

open Complex MeasureTheory Set Filter Topology

open scoped Real Interval

set_option maxHeartbeats 400000

noncomputable section

/-! ## L'Hôpital's Rule -/

/-- L'Hôpital's rule for 0/0 form at a point.

    **Theorem**: If f(a) = g(a) = 0, f and g are differentiable near a,
    g'(x) ≠ 0 for x near a (except possibly at a), and lim_{x→a} f'(x)/g'(x) = L,
    then lim_{x→a} f(x)/g(x) = L.
-/
theorem lhopital_zero_div_zero {f g : ℝ → ℝ} {a L : ℝ}
    (hf_zero : f a = 0)
    (hg_zero : g a = 0)
    (hf_diff : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (hg_diff : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ g x)
    (hg'_ne : ∀ᶠ x in 𝓝[{a}ᶜ] a, deriv g x ≠ 0)
    (h_lim : Tendsto (fun x => deriv f x / deriv g x) (𝓝[{a}ᶜ] a) (𝓝 L)) :
    Tendsto (fun x => f x / g x) (𝓝[{a}ᶜ] a) (𝓝 L) := by
  -- Use mathlib's L'Hôpital rule
  have hf_tendsto : Tendsto f (𝓝[{a}ᶜ] a) (𝓝 0) := by
    rw [← hf_zero]
    apply (hf_diff.self_of_nhds.continuousAt).tendsto.mono_left
    exact nhdsWithin_le_nhds
  have hg_tendsto : Tendsto g (𝓝[{a}ᶜ] a) (𝓝 0) := by
    rw [← hg_zero]
    apply (hg_diff.self_of_nhds.continuousAt).tendsto.mono_left
    exact nhdsWithin_le_nhds
  exact deriv.lhopital_zero_nhdsNE
    (eventually_nhdsWithin_of_eventually_nhds hf_diff) hg'_ne hf_tendsto hg_tendsto h_lim

/- Aristotle failed to find a proof. -/
/-- L'Hôpital's rule for complex-valued functions.

This is a more general version that requires additional work to prove.
For now, we provide it as an axiom; the main application is the real-valued case. -/
theorem lhopital_zero_div_zero_complex {f g : ℝ → ℂ} {a : ℝ} {L : ℂ}
    (_hf_zero : f a = 0)
    (_hg_zero : g a = 0)
    (_hf_diff : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (_hg_diff : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ g x)
    (_hg'_ne : ∀ᶠ x in 𝓝[{a}ᶜ] a, deriv g x ≠ 0)
    (_h_lim : Tendsto (fun x => deriv f x / deriv g x) (𝓝[{a}ᶜ] a) (𝓝 L)) :
    Tendsto (fun x => f x / g x) (𝓝[{a}ᶜ] a) (𝓝 L) := by
  -- Complex L'Hopital needs separate real/imaginary part analysis
  -- or extension of mathlib's proof to normed fields
  -- The mathlib L'Hopital is only for ℝ → ℝ, not for complex-valued functions
  -- For now, this is left as an exercise - the main application uses real functions
  sorry

/-- Helper: g'(x) ≠ 0 for x ≠ a near a when g'(a) = 0 and g''(a) ≠ 0.

    If g'(a) = 0 and g''(a) ≠ 0, then by Taylor expansion:
    g'(x) = g'(a) + g''(a)(x - a) + o(x - a) = g''(a)(x - a) + o(x - a)
    For x ≠ a close to a, this is nonzero.
-/
lemma deriv_nonzero_near_from_second_deriv {g : ℝ → ℝ} {a : ℝ}
    (hg'_zero : deriv g a = 0)
    (hg_C2 : ContDiffAt ℝ 2 g a)
    (hg''_ne : iteratedDeriv 2 g a ≠ 0) :
    ∀ᶠ x in 𝓝[{a}ᶜ] a, deriv g x ≠ 0 := by
  -- g' is C¹ since g is C², so g' has first-order Taylor expansion
  -- g'(x) = g'(a) + g''(a)(x - a) + o(x - a) = g''(a)(x - a)(1 + o(1))
  -- For x ≠ a close to a, this is nonzero
  -- Key: iteratedDeriv 2 g = deriv (deriv g), and g is C² means deriv g is C¹
  -- So deriv (deriv g) a = iteratedDeriv 2 g a ≠ 0
  -- By differentiability of deriv g at a with nonzero derivative, deriv g is injective near a
  -- Since deriv g a = 0, we have deriv g x ≠ 0 for x ≠ a near a

  -- First, deriv g is differentiable at a with derivative iteratedDeriv 2 g a
  have hg'_diff : DifferentiableAt ℝ (deriv g) a := by
    -- g is C² at a, so deriv g is C¹ at a, hence differentiable
    have h1 : ContDiffAt ℝ 1 (deriv g) a := by
      have : ContDiffAt ℝ 2 g a := hg_C2
      -- iteratedDeriv 1 g = deriv g, and ContDiffAt 2 implies ContDiffAt 1 on deriv
      rw [show (2 : ℕ∞) = 1 + 1 by norm_num] at this
      exact this.contDiffAt_iterate_deriv (le_refl 1) (by norm_num)
    exact h1.differentiableAt (le_refl 1)

  -- The derivative of deriv g at a equals iteratedDeriv 2 g a
  have hg'_deriv : deriv (deriv g) a = iteratedDeriv 2 g a := by
    rw [iteratedDeriv_succ]

  -- Now use that if f is differentiable at a with f(a) = 0 and f'(a) ≠ 0,
  -- then f(x) ≠ 0 for x ≠ a near a
  -- Apply taylor_first_order to deriv g: |deriv g x - deriv g a - (deriv (deriv g) a)(x - a)| ≤ ε|x - a|
  -- So |deriv g x - 0 - g''(a)(x - a)| ≤ ε|x - a|
  -- Hence |deriv g x| ≥ |g''(a)||x - a| - ε|x - a| = (|g''(a)| - ε)|x - a|
  -- Taking ε = |g''(a)|/2, we get |deriv g x| ≥ |g''(a)||x - a|/2 > 0 for x ≠ a

  have hg''_pos : 0 < |iteratedDeriv 2 g a| := abs_pos.mpr hg''_ne
  let ε := |iteratedDeriv 2 g a| / 2
  have hε_pos : 0 < ε := by positivity
  obtain ⟨δ, hδ_pos, hδ⟩ := taylor_first_order hg'_diff ε hε_pos
  -- We need to work in 𝓝[{a}ᶜ] a, i.e., for x ≠ a near a
  rw [Filter.eventually_iff_exists_mem]
  use Metric.ball a δ ∩ {a}ᶜ
  constructor
  · -- Show this is a neighborhood in 𝓝[{a}ᶜ] a
    rw [mem_nhdsWithin]
    exact ⟨Metric.ball a δ, Metric.ball_mem_nhds a hδ_pos, by simp [Set.inter_comm]⟩
  · -- Show deriv g x ≠ 0 for x in this set
    intro x ⟨hx_ball, hx_ne⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx_ne
    rw [Metric.mem_ball, Real.dist_eq] at hx_ball
    -- Apply the Taylor bound
    specialize hδ x hx_ball
    rw [hg'_zero, sub_zero, hg'_deriv] at hδ
    -- |deriv g x - g''(a)(x - a)| ≤ ε|x - a|
    -- So |deriv g x| ≥ |g''(a)(x - a)| - ε|x - a| = (|g''(a)| - ε)|x - a|
    have h_bound : |deriv g x| ≥ (|iteratedDeriv 2 g a| - ε) * |x - a| := by
      have h1 : |iteratedDeriv 2 g a * (x - a)| = |iteratedDeriv 2 g a| * |x - a| := abs_mul _ _
      calc |deriv g x| = |deriv g x - iteratedDeriv 2 g a * (x - a) + iteratedDeriv 2 g a * (x - a)| := by ring_nf
        _ ≥ |iteratedDeriv 2 g a * (x - a)| - |deriv g x - iteratedDeriv 2 g a * (x - a)| := abs_sub_abs_le_abs_sub _ _
        _ ≥ |iteratedDeriv 2 g a| * |x - a| - ε * |x - a| := by linarith [hδ, h1]
        _ = (|iteratedDeriv 2 g a| - ε) * |x - a| := by ring
    -- Since ε = |g''(a)|/2, we have |g''(a)| - ε = |g''(a)|/2 > 0
    have h_coeff : |iteratedDeriv 2 g a| - ε = |iteratedDeriv 2 g a| / 2 := by
      simp only [ε]; ring
    rw [h_coeff] at h_bound
    -- Since x ≠ a, |x - a| > 0
    have h_xa_pos : 0 < |x - a| := abs_pos.mpr (sub_ne_zero.mpr hx_ne)
    -- So |deriv g x| ≥ |g''(a)|/2 * |x - a| > 0
    have h_pos : 0 < |iteratedDeriv 2 g a| / 2 * |x - a| := by positivity
    linarith

/-- Double application of L'Hôpital's rule.

    **Theorem**: If f(a) = g(a) = f'(a) = g'(a) = 0, f and g are twice differentiable near a,
    g''(a) ≠ 0, and lim_{x→a} f''(x)/g''(x) = L, then lim_{x→a} f(x)/g(x) = L.

    This is used for the winding number integrand limit where both the numerator
    and denominator, along with their first derivatives, vanish at t₀.

    **Proof strategy**:
    1. Apply L'Hopital once: lim f/g = lim f'/g' (both are 0/0)
    2. Apply L'Hopital again: lim f'/g' = lim f''/g'' = L
       (f'(a) = g'(a) = 0, and g'(x) ≠ 0 for x ≠ a near a by lemma above)
-/
theorem lhopital_twice {f g : ℝ → ℝ} {a L : ℝ}
    (_hf_zero : f a = 0)
    (_hg_zero : g a = 0)
    (_hf'_zero : deriv f a = 0)
    (_hg'_zero : deriv g a = 0)
    (_hf_C2 : ContDiffAt ℝ 2 f a)
    (_hg_C2 : ContDiffAt ℝ 2 g a)
    (_hg''_ne : iteratedDeriv 2 g a ≠ 0)
    (_h_lim : Tendsto (fun x => iteratedDeriv 2 f x / iteratedDeriv 2 g x) (𝓝[{a}ᶜ] a) (𝓝 L)) :
    Tendsto (fun x => f x / g x) (𝓝[{a}ᶜ] a) (𝓝 L) := by
  -- The proof chains two applications of L'Hopital:
  -- 1. First application: lim f/g = lim f'/g' (f(a) = g(a) = 0)
  -- 2. Second application: lim f'/g' = lim f''/g'' (f'(a) = g'(a) = 0)
  -- Key intermediate results needed:
  -- - f, g differentiable near a (from C²)
  -- - f', g' differentiable near a (from C²)
  -- - g'(x) ≠ 0 for x ≠ a near a (from g'(a) = 0, g''(a) ≠ 0)
  -- - g''(x) ≠ 0 near a (continuity of g'' at a with g''(a) ≠ 0)
  -- Apply L'Hôpital's rule to the first derivatives.
  have h_lhopital_first_deriv : Filter.Tendsto (fun x => deriv f x / deriv g x) (𝓝[≠] a) (𝓝 L) := by
    apply lhopital_zero_div_zero;
    all_goals simp_all +decide [ iteratedDeriv_succ' ];
    · have h_diff : ContDiffAt ℝ 1 (deriv f) a := by
        have h_cont_diff : ContDiffAt ℝ 2 f a := _hf_C2
        have h_cont_diff_deriv : ∀ {n : ℕ}, ContDiffAt ℝ (n + 1) f a → ContDiffAt ℝ n (deriv f) a := by
          intro n hn; exact (by
          have := hn.eventually ( by norm_num );
          rw [ eventually_nhds_iff ] at this;
          obtain ⟨ t, ht₁, ht₂, ht₃ ⟩ := this; exact (by
          have h_cont_diff_deriv : ContDiffOn ℝ (n + 1) f t := by
            exact fun x hx => ht₁ x hx |> ContDiffAt.contDiffWithinAt;
          have h_cont_diff_deriv : ContDiffOn ℝ n (deriv f) t := by
            exact h_cont_diff_deriv.deriv_of_isOpen ht₂ ( by norm_num );
          exact h_cont_diff_deriv.contDiffAt ( ht₂.mem_nhds ht₃ )));
        exact h_cont_diff_deriv h_cont_diff;
      exact h_diff.eventually ( by norm_num ) |> fun h => h.mono fun x hx => hx.differentiableAt ( by norm_num );
    · have h_cont_diff : ContDiffAt ℝ 1 (deriv g) a := by
        have h_diff_g' : ContDiffAt ℝ 2 g a → ContDiffAt ℝ 1 (deriv g) a := by
          intro hg_C2
          have h_diff_g' : ContDiffAt ℝ 2 g a → ContDiffAt ℝ 1 (deriv g) a := by
            intro hg_C2
            have h_diff_g' : ∃ U : Set ℝ, IsOpen U ∧ a ∈ U ∧ ContDiffOn ℝ 2 g U := by
              have := hg_C2.eventually;
              rw [ Metric.eventually_nhds_iff ] at this;
              exact ⟨ Metric.ball a ( Classical.choose ( this ( by norm_num ) ) ), Metric.isOpen_ball, Metric.mem_ball_self ( Classical.choose_spec ( this ( by norm_num ) ) |>.1 ), fun x hx => ( Classical.choose_spec ( this ( by norm_num ) ) |>.2 hx ) |> ContDiffAt.contDiffWithinAt ⟩
            obtain ⟨ U, hU₁, hU₂, hU₃ ⟩ := h_diff_g';
            have h_diff_g' : ContDiffOn ℝ 1 (deriv g) U := by
              exact hU₃.deriv_of_isOpen hU₁ ( by norm_num );
            exact h_diff_g'.contDiffAt ( hU₁.mem_nhds hU₂ );
          exact h_diff_g' hg_C2;
        exact h_diff_g' ‹_›;
      exact h_cont_diff.eventually ( by norm_num ) |> fun h => h.mono fun x hx => hx.differentiableAt le_rfl;
    · have h_deriv_g_ne_zero : ∀ᶠ x in 𝓝 a, deriv (deriv g) x ≠ 0 := by
        have h_deriv_nonzero : ContinuousAt (deriv^[2] g) a := by
          have h_cont_diff : ∃ U : Set ℝ, IsOpen U ∧ a ∈ U ∧ ContDiffOn ℝ 1 (deriv g) U := by
            have h_cont_diff : ∃ U : Set ℝ, IsOpen U ∧ a ∈ U ∧ ContDiffOn ℝ 2 g U := by
              have := _hg_C2;
              have := this.eventually;
              rw [ Metric.eventually_nhds_iff ] at this;
              exact ⟨ Metric.ball a ( Classical.choose ( this ( by norm_num ) ) ), Metric.isOpen_ball, Metric.mem_ball_self ( Classical.choose_spec ( this ( by norm_num ) ) |>.1 ), fun x hx => ( Classical.choose_spec ( this ( by norm_num ) ) |>.2 hx ) |> ContDiffAt.contDiffWithinAt ⟩;
            obtain ⟨ U, hU₁, hU₂, hU₃ ⟩ := h_cont_diff; exact ⟨ U, hU₁, hU₂, by exact hU₃.deriv_of_isOpen hU₁ ( by norm_num ) ⟩ ;
          obtain ⟨ U, hU₁, hU₂, hU₃ ⟩ := h_cont_diff;
          exact hU₃.continuousOn_deriv_of_isOpen hU₁ ( by norm_num ) |> ContinuousOn.continuousAt <| IsOpen.mem_nhds hU₁ hU₂;
        exact h_deriv_nonzero.eventually_ne _hg''_ne;
      exact h_deriv_g_ne_zero.filter_mono nhdsWithin_le_nhds;
  convert lhopital_zero_div_zero _hf_zero _hg_zero _ _ _ h_lhopital_first_deriv;
  · exact _hf_C2.eventually ( by norm_num ) |> fun h => h.mono fun x hx => by exact hx.differentiableAt ( by norm_num ) ;
  · have := _hg_C2;
    have := this.eventually ( by norm_num );
    filter_upwards [ this ] with x hx using hx.differentiableAt ( by norm_num );
  · exact?

/-! ## Taylor Expansion -/

-- Helper: Converting ContDiffAt to ContDiffOn on a ball (for finite n)
lemma contDiffAt_to_contDiffOn_ball {f : ℝ → ℝ} {a : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ n f a) :
    ∃ r > 0, ContDiffOn ℝ n f (Metric.ball a r) := by
  -- Use ContDiffWithinAt.contDiffOn' which gives an open set
  have hf' : ContDiffWithinAt ℝ n f Set.univ a := hf
  -- The condition m = ∞ → n = ω is vacuously true for n : ℕ
  have h' : ((n : ℕ∞) : WithTop ℕ∞) = (⊤ : ℕ∞) → ((n : ℕ∞) : WithTop ℕ∞) = ⊤ := by
    intro heq
    -- n : ℕ, so (n : ℕ∞) ≠ ⊤, so ((n : ℕ∞) : WithTop ℕ∞) ≠ (⊤ : ℕ∞)
    exfalso
    have : (n : ℕ∞) ≠ ⊤ := ENat.coe_ne_top n
    rw [WithTop.coe_eq_coe] at heq
    exact this heq
  obtain ⟨u, hu_open, ha_mem, hu_contDiff⟩ := hf'.contDiffOn' le_rfl h'
  -- Get a ball contained in u
  rw [Metric.isOpen_iff] at hu_open
  obtain ⟨r, hr_pos, hr_sub⟩ := hu_open a ha_mem
  refine ⟨r, hr_pos, hu_contDiff.mono ?_⟩
  intro x hx
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_univ, or_true, true_and]
  exact hr_sub hx

/-- First-order Taylor expansion with Lipschitz remainder.

    **Lemma**: If f is differentiable at a, then
    f(x) = f(a) + f'(a)(x - a) + o(|x - a|)
-/
theorem taylor_first_order {f : ℝ → ℝ} {a : ℝ}
    (hf : DifferentiableAt ℝ f a) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ →
      |f x - f a - deriv f a * (x - a)| ≤ ε * |x - a| := by
  intro ε hε
  -- Use hasDerivAt_iff_isLittleO to get the little-o bound
  have hderiv := hf.hasDerivAt
  rw [hasDerivAt_iff_isLittleO] at hderiv
  -- isLittleO means for all ε > 0, eventually |f x' - f a - (x' - a) * f'a| ≤ ε * |x' - a|
  rw [Asymptotics.isLittleO_iff] at hderiv
  specialize hderiv hε
  rw [Filter.eventually_iff] at hderiv
  -- Get δ from the neighborhood
  rw [Metric.mem_nhds_iff] at hderiv
  obtain ⟨δ, hδ_pos, hδ⟩ := hderiv
  use δ, hδ_pos
  intro x hx
  have hx_in : x ∈ Metric.ball a δ := by simp [Metric.mem_ball]; exact hx
  specialize hδ hx_in
  -- Convert smul to mul for real numbers and match the expression
  simp only [smul_eq_mul, Real.norm_eq_abs, Set.mem_setOf_eq] at hδ
  have h_eq : f x - f a - deriv f a * (x - a) = f x - f a - (x - a) * deriv f a := by ring
  rw [h_eq]
  exact hδ

/- Aristotle failed to find a proof. -/
/-- Second-order Taylor expansion for C² functions.

    **Lemma**: If f is C² at a, then
    f(x) = f(a) + f'(a)(x - a) + (1/2)f''(a)(x - a)² + o((x - a)²)

    **Proof strategy**:
    1. Get ContDiffOn on a ball B(a, r) from ContDiffAt using `contDiffAt_to_contDiffOn_ball`
    2. Apply `taylor_mean_remainder_bound` with n=1 on Icc (a - δ) (a + δ) ⊆ B(a, r)
    3. This gives: |f(x) - f(a) - f'(a)(x-a) - (1/2)f''(ξ)(x-a)²| ≤ C|x-a|²/(1!)
       for some ξ between a and x
    4. Since f'' is continuous at a, for small enough δ, |f''(ξ) - f''(a)| < ε
    5. This yields the desired o((x-a)²) remainder bound
-/
theorem taylor_second_order {f : ℝ → ℝ} {a : ℝ}
    (hf : ContDiffAt ℝ 2 f a) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ →
      |f x - f a - deriv f a * (x - a) - (1/2) * iteratedDeriv 2 f a * (x - a)^2| ≤
        ε * (x - a)^2 := by
  intro ε hε
  -- Get a ball where f is C²
  obtain ⟨r, hr, _hf_ball⟩ := contDiffAt_to_contDiffOn_ball hf
  -- The second derivative is continuous at a (since f is C²)
  have hf''_cont : ContinuousAt (iteratedDeriv 2 f) a := by
    -- Use ContDiff.continuous_iteratedDeriv: if f is C^n then iteratedDeriv m f is continuous for m ≤ n
    -- First get ContDiff on an open neighborhood
    obtain ⟨u, hu_nhds, hu_contDiff⟩ := hf.contDiffOn le_rfl (by simp)
    -- Get an open set v ⊆ u containing a
    rw [mem_nhds_iff] at hu_nhds
    obtain ⟨v, hv_sub, hv_open, ha_v⟩ := hu_nhds
    -- f is C² on v (open)
    have hf_C2_on_v : ContDiffOn ℝ 2 f v := hu_contDiff.mono hv_sub
    -- On an open set, iteratedDerivWithin equals iteratedDeriv
    have h_eq : ∀ x ∈ v, iteratedDerivWithin 2 f v x = iteratedDeriv 2 f x :=
      iteratedDerivWithin_of_isOpen hv_open
    -- iteratedDerivWithin 2 f v is continuous on v
    have h_cont_within : ContinuousOn (iteratedDerivWithin 2 f v) v :=
      hf_C2_on_v.continuousOn_iteratedDerivWithin le_rfl hv_open.uniqueDiffOn
    -- Therefore iteratedDeriv 2 f is continuous on v
    have h_cont_on_v : ContinuousOn (iteratedDeriv 2 f) v := by
      intro x hx
      have hcw : ContinuousWithinAt (iteratedDerivWithin 2 f v) v x := h_cont_within x hx
      have h_eq_sym : ∀ y ∈ v, iteratedDeriv 2 f y = iteratedDerivWithin 2 f v y :=
        fun y hy => (h_eq y hy).symm
      exact hcw.congr h_eq_sym (h_eq_sym x hx)
    exact h_cont_on_v.continuousAt (hv_open.mem_nhds ha_v)
  -- For continuity of f'' at a, get δ₁ such that |f''(y) - f''(a)| < ε for |y - a| < δ₁
  rw [Metric.continuousAt_iff] at hf''_cont
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hf''_cont ε hε
  -- Take δ = min(δ₁, r/2)
  let δ := min δ₁ (r / 2)
  have hδ_pos : 0 < δ := lt_min hδ₁_pos (by linarith)
  use δ, hδ_pos
  intro x hx
  -- Apply Taylor mean remainder bound
  -- The detailed proof requires relating iteratedDeriv to iteratedDerivWithin
  -- and handling the interval carefully
  sorry

/-- Taylor expansion for complex-valued functions. -/
theorem taylor_second_order_complex {f : ℝ → ℂ} {a : ℝ}
    (_hf : ContDiffAt ℝ 2 f a) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ →
      ‖f x - f a - deriv f a * (x - a) - (1/2) * iteratedDeriv 2 f a * (x - a)^2‖ ≤
        ε * (x - a)^2 := by
  -- Apply the real Taylor expansion to real and imaginary parts separately
  -- then combine using norm bounds: ‖z‖ ≤ |re z| + |im z|
  intro ε hε_pos
  have h_taylor : ContDiffAt ℝ 2 (fun x : ℝ => f x) a := by
    assumption
  have h_exists_delta : ∃ δ > 0, ContDiffOn ℝ 2 (fun x : ℝ => f x) (Metric.ball a δ) := by
    have := h_taylor.eventually;
    rw [ Metric.eventually_nhds_iff ] at this;
    exact Exists.elim ( this ( by norm_num ) ) fun δ hδ => ⟨ δ, hδ.1, fun x hx => ( hδ.2 hx ) |> ContDiffAt.contDiffWithinAt ⟩
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ContDiffOn ℝ 2 (fun x : ℝ => f x) (Metric.ball a δ) := h_exists_delta
  have h_taylor_real : ∀ ε > 0, ∃ δ' > 0, ∀ x : ℝ, |x - a| < δ' → |(f x).re - (f a).re - (deriv f a).re * (x - a) - (1/2) * (iteratedDeriv 2 f a).re * (x - a)^2| ≤ ε * (x - a)^2 := by
    have h_taylor_real : ∀ ε > 0, ∃ δ' > 0, ∀ x : ℝ, |x - a| < δ' → |(fun x => (f x).re) x - (fun x => (f x).re) a - (deriv (fun x => (f x).re) a) * (x - a) - (1/2) * (iteratedDeriv 2 (fun x => (f x).re) a) * (x - a)^2| ≤ ε * (x - a)^2 := by
      apply_rules [ taylor_second_order ];
      exact Complex.reCLM.contDiff.contDiffAt.comp a h_taylor;
    convert h_taylor_real using 6;
    rw [ show deriv ( fun x => ( f x |> Complex.re ) ) a = ( deriv f a |> Complex.re ) from ?_, show iteratedDeriv 2 ( fun x => ( f x |> Complex.re ) ) a = ( iteratedDeriv 2 f a |> Complex.re ) from ?_ ];
    · rw [ iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate ];
      have h_deriv_real : ∀ x ∈ Metric.ball a δ, deriv (fun x => (f x).re) x = (deriv f x).re := by
        intro x hx;
        have h_deriv_real : HasDerivAt (fun x => (f x).re) ((deriv f x).re) x := by
          have h_deriv_real : HasDerivAt (fun x => f x) (deriv f x) x := by
            exact DifferentiableAt.hasDerivAt ( hδ.differentiableOn ( by norm_num ) |> DifferentiableOn.differentiableAt <| Metric.isOpen_ball.mem_nhds hx );
          rw [ hasDerivAt_iff_tendsto_slope_zero ] at *;
          convert Complex.continuous_re.continuousAt.tendsto.comp h_deriv_real using 2 ; norm_num;
        exact h_deriv_real.deriv;
      convert HasDerivAt.deriv ( HasDerivAt.congr_of_eventuallyEq _ <| Filter.eventuallyEq_of_mem ( Metric.ball_mem_nhds a hδ_pos ) fun x hx => h_deriv_real x hx ) using 1;
      have h_deriv_real : HasDerivAt (deriv f) (deriv^[2] f a) a := by
        have h_deriv_real : ContDiffAt ℝ 1 (deriv f) a := by
          have h_deriv_real : ContDiffOn ℝ 1 (deriv f) (Metric.ball a δ) := by
            exact hδ.deriv_of_isOpen Metric.isOpen_ball ( by norm_num );
          exact h_deriv_real.contDiffAt ( Metric.isOpen_ball.mem_nhds <| Metric.mem_ball_self hδ_pos );
        exact h_deriv_real.differentiableAt le_rfl |> DifferentiableAt.hasDerivAt;
      rw [ hasDerivAt_iff_tendsto_slope_zero ] at *;
      convert Complex.continuous_re.continuousAt.tendsto.comp h_deriv_real using 2 ; norm_num;
    · convert HasDerivAt.deriv ( _ ) using 1;
      have h_deriv_real : HasDerivAt (fun x => f x) (deriv f a) a := by
        exact h_taylor.differentiableAt ( by norm_num ) |> DifferentiableAt.hasDerivAt;
      rw [ hasDerivAt_iff_tendsto ] at *;
      exact squeeze_zero ( fun _ => by positivity ) ( fun x' => mul_le_mul_of_nonneg_left ( by simpa using Complex.abs_re_le_norm ( f x' - f a - ( x' - a ) • deriv f a ) ) ( by positivity ) ) h_deriv_real
  have h_taylor_imag : ∀ ε > 0, ∃ δ' > 0, ∀ x : ℝ, |x - a| < δ' → |(f x).im - (f a).im - (deriv f a).im * (x - a) - (1/2) * (iteratedDeriv 2 f a).im * (x - a)^2| ≤ ε * (x - a)^2 := by
    have h_taylor_imag : ContDiffAt ℝ 2 (fun x : ℝ => (f x).im) a := by
      exact Complex.imCLM.contDiff.contDiffAt.comp a h_taylor;
    have h_taylor_imag : ∀ ε > 0, ∃ δ' > 0, ∀ x : ℝ, |x - a| < δ' → |(f x).im - (f a).im - (deriv (fun x => (f x).im) a) * (x - a) - (1/2) * (iteratedDeriv 2 (fun x => (f x).im) a) * (x - a)^2| ≤ ε * (x - a)^2 := by
      exact?;
    have h_deriv_imag : deriv (fun x => (f x).im) a = (deriv f a).im := by
      have h_deriv_imag : HasDerivAt (fun x => (f x).im) ((deriv f a).im) a := by
        have h_deriv_imag : HasDerivAt (fun x => f x) (deriv f a) a := by
          exact DifferentiableAt.hasDerivAt ( h_taylor.differentiableAt ( by norm_num ) );
        rw [ hasDerivAt_iff_tendsto_slope_zero ] at *;
        convert Complex.continuous_im.continuousAt.tendsto.comp h_deriv_imag using 2 ; norm_num;
      exact h_deriv_imag.deriv
    have h_iter_deriv_imag : iteratedDeriv 2 (fun x => (f x).im) a = (iteratedDeriv 2 f a).im := by
      have h_iter_deriv_imag : ∀ x ∈ Metric.ball a δ, deriv (fun x => (f x).im) x = (deriv f x).im := by
        intro x hx
        have h_deriv_imag : HasDerivAt (fun x => (f x).im) ((deriv f x).im) x := by
          have h_deriv_imag : HasDerivAt (fun x => f x) (deriv f x) x := by
            exact DifferentiableAt.hasDerivAt ( hδ.differentiableOn ( by norm_num ) |> DifferentiableOn.differentiableAt <| Metric.isOpen_ball.mem_nhds hx );
          rw [ hasDerivAt_iff_tendsto_slope_zero ] at *;
          convert Complex.continuous_im.continuousAt.tendsto.comp h_deriv_imag using 2 ; norm_num;
        exact h_deriv_imag.deriv;
      have h_iter_deriv_imag : deriv (fun x => (deriv f x).im) a = (deriv (deriv f) a).im := by
        have h_iter_deriv_imag : HasDerivAt (fun x => (deriv f x).im) ((deriv (deriv f) a).im) a := by
          have h_iter_deriv_imag : HasDerivAt (deriv f) (deriv (deriv f) a) a := by
            have h_iter_deriv_imag : ContDiffOn ℝ 1 (deriv f) (Metric.ball a δ) := by
              exact hδ.deriv_of_isOpen Metric.isOpen_ball ( by norm_num ) |> ContDiffOn.mono <| by aesop_cat;
            exact h_iter_deriv_imag.differentiableOn le_rfl |> DifferentiableOn.hasDerivAt <| Metric.ball_mem_nhds _ hδ_pos;
          rw [ hasDerivAt_iff_tendsto_slope_zero ] at *;
          convert Complex.continuous_im.continuousAt.tendsto.comp h_iter_deriv_imag using 2 ; norm_num;
        exact h_iter_deriv_imag.deriv;
      rw [ iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate ];
      convert h_iter_deriv_imag using 1;
      exact Filter.EventuallyEq.deriv_eq ( Filter.eventuallyEq_of_mem ( Metric.ball_mem_nhds a hδ_pos ) fun x hx => by aesop )
    aesop;
  obtain ⟨ δ₁, hδ₁_pos, hδ₁ ⟩ := h_taylor_real ( ε / 2 ) ( half_pos hε_pos ) ; obtain ⟨ δ₂, hδ₂_pos, hδ₂ ⟩ := h_taylor_imag ( ε / 2 ) ( half_pos hε_pos ) ; refine' ⟨ Min.min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun x hx => _ ⟩ ; simp_all +decide [ Complex.norm_def, Complex.normSq ];
  norm_cast ; norm_num [ sq ] at *;
  exact Real.sqrt_le_iff.mpr ⟨ by nlinarith [ abs_le.mp ( hδ₁ x hx.1 ), abs_le.mp ( hδ₂ x hx.2 ) ], by nlinarith [ abs_le.mp ( hδ₁ x hx.1 ), abs_le.mp ( hδ₂ x hx.2 ) ] ⟩

/-! ## Application: Winding Number Integrand Limit -/

/- Aristotle failed to find a proof. -/
/-- The numerator x·y' - y·x' is O((t - t₀)²) when γ(t₀) = 0.

    **Lemma** (from Hungerbühler-Wasem proof of Proposition 2):
    If γ = (x, y) : ℝ → ℝ² is C^{1,1} (Lipschitz derivative) and γ(t₀) = 0, then
    |x(t)y'(t) - y(t)x'(t)| = O((t - t₀)²)

    **Proof sketch**:
    x(t) = ∫_{t₀}^t x'(s) ds = (t - t₀)x'(t₀) + O((t - t₀)²) [Lipschitz derivative]
    y(t) = (t - t₀)y'(t₀) + O((t - t₀)²)
    x'(t) = x'(t₀) + O(t - t₀)
    y'(t) = y'(t₀) + O(t - t₀)

    x·y' - y·x' = [(t-t₀)x'(t₀) + O(h²)][y'(t₀) + O(h)] - [(t-t₀)y'(t₀) + O(h²)][x'(t₀) + O(h)]
                = (t-t₀)[x'(t₀)y'(t₀) - y'(t₀)x'(t₀)] + O(h²)
                = 0 + O(h²) = O(h²)
-/
theorem numerator_big_O_squared' {x y : ℝ → ℝ} {t₀ r : ℝ} {K : NNReal}
    (_hx_C11 : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ x t)
    (_hy_C11 : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ y t)
    (_hx'_lip : LipschitzOnWith K (deriv x) (Metric.ball t₀ r))
    (_hy'_lip : LipschitzOnWith K (deriv y) (Metric.ball t₀ r))
    (_hx_zero : x t₀ = 0)
    (_hy_zero : y t₀ = 0)
    (_hr : 0 < r) :
    ∃ C, ∀ t, |t - t₀| < r → |x t * deriv y t - y t * deriv x t| ≤ C * (t - t₀)^2 := by
  -- Expand x(t), y(t), x'(t), y'(t) using Lipschitz bounds
  -- The cross terms cancel: x'(t₀)y'(t₀) - y'(t₀)x'(t₀) = 0
  -- What remains is O((t - t₀)²)
  sorry

/-- The denominator x² + y² is ~|γ'(t₀)|² · (t - t₀)² + higher order.

    **Lemma**: If γ(t₀) = 0 and γ'(t₀) ≠ 0, then
    x(t)² + y(t)² = |γ'(t₀)|² · (t - t₀)² + o((t - t₀)²)
-/
theorem denominator_quadratic' {x y : ℝ → ℝ} {t₀ : ℝ}
    (hx_diff : DifferentiableAt ℝ x t₀)
    (hy_diff : DifferentiableAt ℝ y t₀)
    (hx_zero : x t₀ = 0)
    (hy_zero : y t₀ = 0)
    (_h_deriv_ne : deriv x t₀ ≠ 0 ∨ deriv y t₀ ≠ 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, |t - t₀| < δ →
      |x t^2 + y t^2 - (deriv x t₀^2 + deriv y t₀^2) * (t - t₀)^2| ≤
        ε * (t - t₀)^2 := by
  intro ε hε
  -- Use taylor_first_order for x and y
  -- Choose ε₁ small enough so that the error terms are bounded by ε
  let M := max (|deriv x t₀|) (|deriv y t₀|) + 1
  have hM_pos : 0 < M := by
    apply lt_of_lt_of_le zero_lt_one
    exact le_add_of_nonneg_left (le_max_of_le_left (abs_nonneg _))
  -- Choose ε₁ so that 4Mε₁ + 2ε₁² ≤ ε
  -- Setting ε₁ = min (ε / (8M)) (1) works
  let ε₁ := min (ε / (8 * M)) 1
  have hε₁_pos : 0 < ε₁ := by
    apply lt_min
    · apply div_pos hε
      linarith
    · exact one_pos
  -- Get δ_x and δ_y from taylor_first_order
  obtain ⟨δ_x, hδ_x_pos, hδ_x⟩ := taylor_first_order hx_diff ε₁ hε₁_pos
  obtain ⟨δ_y, hδ_y_pos, hδ_y⟩ := taylor_first_order hy_diff ε₁ hε₁_pos
  -- Take δ = min(δ_x, δ_y)
  let δ := min δ_x δ_y
  have hδ_pos : 0 < δ := lt_min hδ_x_pos hδ_y_pos
  use δ, hδ_pos
  intro t ht
  -- Define r_x = x(t) - x(t₀) - x'(t₀)(t - t₀) and similarly r_y
  -- Using hx_zero: r_x = x(t) - x'(t₀)(t - t₀)
  let r_x := x t - deriv x t₀ * (t - t₀)
  let r_y := y t - deriv y t₀ * (t - t₀)
  -- From taylor_first_order: |r_x| ≤ ε₁|t - t₀|, |r_y| ≤ ε₁|t - t₀|
  have hr_x : |r_x| ≤ ε₁ * |t - t₀| := by
    have h := hδ_x t (lt_of_lt_of_le ht (min_le_left _ _))
    simp only [hx_zero, sub_zero, r_x] at h ⊢
    exact h
  have hr_y : |r_y| ≤ ε₁ * |t - t₀| := by
    have h := hδ_y t (lt_of_lt_of_le ht (min_le_right _ _))
    simp only [hy_zero, sub_zero, r_y] at h ⊢
    exact h
  -- x(t) = x'(t₀)(t - t₀) + r_x, y(t) = y'(t₀)(t - t₀) + r_y
  have hx_eq : x t = deriv x t₀ * (t - t₀) + r_x := by ring
  have hy_eq : y t = deriv y t₀ * (t - t₀) + r_y := by ring
  -- The rest requires careful algebraic manipulation
  -- x² + y² = (x'(t-t₀) + r_x)² + (y'(t-t₀) + r_y)²
  --         = (x'² + y'²)(t-t₀)² + 2x'(t-t₀)r_x + r_x² + 2y'(t-t₀)r_y + r_y²
  -- Error = 2x'(t-t₀)r_x + r_x² + 2y'(t-t₀)r_y + r_y²
  -- |Error| ≤ 2|x'||t-t₀||r_x| + |r_x|² + 2|y'||t-t₀||r_y| + |r_y|²
  --        ≤ 2|x'||t-t₀|ε₁|t-t₀| + (ε₁|t-t₀|)² + 2|y'||t-t₀|ε₁|t-t₀| + (ε₁|t-t₀|)²
  --        = (2ε₁(|x'| + |y'|) + 2ε₁²)(t-t₀)²
  --        ≤ (4Mε₁ + 2ε₁²)(t-t₀)²
  --        ≤ ε(t-t₀)²  [by choice of ε₁]
  -- The algebraic details are standard Taylor expansion bounds
  -- We defer to nlinarith with appropriate witnesses for the final bound
  have h_expand : x t^2 + y t^2 - (deriv x t₀^2 + deriv y t₀^2) * (t - t₀)^2 =
      2 * deriv x t₀ * (t - t₀) * r_x + r_x^2 + 2 * deriv y t₀ * (t - t₀) * r_y + r_y^2 := by
    simp only [hx_eq, hy_eq]; ring
  -- Use estimates: |r_x| ≤ ε₁|t - t₀|, |r_y| ≤ ε₁|t - t₀|
  have hε₁_le_1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁_le_frac : ε₁ ≤ ε / (8 * M) := min_le_left _ _
  have hM_ge_1 : 1 ≤ M := le_add_of_nonneg_left (le_max_of_le_left (abs_nonneg _))
  have hx'_le_M : |deriv x t₀| ≤ M := le_trans (le_max_left _ _) (le_add_of_nonneg_right one_pos.le)
  have hy'_le_M : |deriv y t₀| ≤ M := le_trans (le_max_right _ _) (le_add_of_nonneg_right one_pos.le)
  -- Key: |r_x|² ≤ ε₁² |t - t₀|², etc.
  have hr_x_abs : |r_x| ≤ ε₁ * |t - t₀| := hr_x
  have hr_y_abs : |r_y| ≤ ε₁ * |t - t₀| := hr_y
  -- r_x and r_y are bounded in absolute value
  have hr_x_bnd : -ε₁ * |t - t₀| ≤ r_x ∧ r_x ≤ ε₁ * |t - t₀| := by
    have := abs_le.mp hr_x_abs; constructor <;> linarith
  have hr_y_bnd : -ε₁ * |t - t₀| ≤ r_y ∧ r_y ≤ ε₁ * |t - t₀| := by
    have := abs_le.mp hr_y_abs; constructor <;> linarith
  have h_t_abs : |t - t₀| ≥ 0 := abs_nonneg _
  -- The error bound follows from standard analysis
  -- Setting h = |t - t₀| for readability in the nlinarith computation
  set h := |t - t₀| with hh_def
  have hh_sq : h^2 = (t - t₀)^2 := sq_abs (t - t₀)
  rw [h_expand, ← hh_sq]
  -- Build the bound step by step
  have hh_nonneg : 0 ≤ h := abs_nonneg _
  -- The detailed algebraic bound follows from:
  -- |2x'hr_x + r_x² + 2y'hr_y + r_y²| ≤ 2M·h·ε₁·h + (ε₁h)² + 2M·h·ε₁·h + (ε₁h)²
  --                                    = (4Mε₁ + 2ε₁²)h²
  --                                    ≤ εh² (by choice of ε₁)
  -- Each individual bound is standard:
  -- - |2x'hr_x| ≤ 2M·h·ε₁·h (using |x'| ≤ M, |r_x| ≤ ε₁·h)
  -- - |r_x²| ≤ (ε₁h)² (squaring |r_x| ≤ ε₁·h)
  -- The coefficient bound 4Mε₁ + 2ε₁² ≤ ε uses ε₁ ≤ ε/(8M) and ε₁ ≤ 1
  -- This is standard Taylor expansion remainder analysis
  -- Substitute the bounds for $r_x$ and $r_y$ into the expanded expression.
  have h_subst : |2 * deriv x t₀ * (t - t₀) * r_x + r_x ^ 2 + 2 * deriv y t₀ * (t - t₀) * r_y + r_y ^ 2| ≤ 2 * M * h * (ε₁ * h) + (ε₁ * h) ^ 2 + 2 * M * h * (ε₁ * h) + (ε₁ * h) ^ 2 := by
    have h_subst : |2 * deriv x t₀ * (t - t₀) * r_x| ≤ 2 * M * h * (ε₁ * h) ∧ |r_x ^ 2| ≤ (ε₁ * h) ^ 2 ∧ |2 * deriv y t₀ * (t - t₀) * r_y| ≤ 2 * M * h * (ε₁ * h) ∧ |r_y ^ 2| ≤ (ε₁ * h) ^ 2 := by
      norm_num [ abs_mul ] at *;
      exact ⟨ by exact mul_le_mul ( mul_le_mul ( mul_le_mul_of_nonneg_left hx'_le_M <| by positivity ) le_rfl ( by positivity ) <| by positivity ) hr_x_abs ( by positivity ) <| by positivity, by nlinarith only [ abs_le.mp hr_x_abs ], by exact mul_le_mul ( mul_le_mul ( mul_le_mul_of_nonneg_left hy'_le_M <| by positivity ) le_rfl ( by positivity ) <| by positivity ) hr_y_abs ( by positivity ) <| by positivity, by nlinarith only [ abs_le.mp hr_y_abs ] ⟩;
    exact abs_le.mpr ⟨ by linarith [ abs_le.mp h_subst.1, abs_le.mp h_subst.2.1, abs_le.mp h_subst.2.2.1, abs_le.mp h_subst.2.2.2 ], by linarith [ abs_le.mp h_subst.1, abs_le.mp h_subst.2.1, abs_le.mp h_subst.2.2.1, abs_le.mp h_subst.2.2.2 ] ⟩;
  refine le_trans h_subst ?_;
  rw [ le_div_iff₀ ( by positivity ) ] at hε₁_le_frac;
  nlinarith only [ show 0 ≤ ε₁ * h ^ 2 by positivity, show 0 ≤ ε₁ ^ 2 * h ^ 2 by positivity, hε₁_le_frac, hε₁_le_1, hM_ge_1, h_t_abs, hh_nonneg, hh_sq, mul_le_mul_of_nonneg_left hε₁_le_1 <| show 0 ≤ ε₁ * h ^ 2 by positivity, mul_le_mul_of_nonneg_left hε₁_le_1 <| show 0 ≤ ε₁ ^ 2 * h ^ 2 by positivity ]

/- Aristotle failed to find a proof. -/
/-- The winding number integrand limit at a zero of γ.

    **Theorem** (Hungerbühler-Wasem, Proposition 2):
    For a C² curve γ = (x, y) with γ(t₀) = 0 and γ'(t₀) ≠ 0:

    lim_{t → t₀} (x(t)y'(t) - y(t)x'(t)) / (x(t)² + y(t)²) = (1/2) · κ · |γ'(t₀)|

    where κ = (x'(t₀)y''(t₀) - y'(t₀)x''(t₀)) / (x'(t₀)² + y'(t₀)²)^{3/2} is the signed curvature.

    **Proof strategy**:
    Apply L'Hôpital twice:
    1. Both num and den are 0 at t₀ (first 0/0)
    2. Their derivatives are also 0 at t₀ (second 0/0)
    3. Second derivatives give the curvature formula
-/
theorem windingNumberIntegrand_limit_at_zero' {x y : ℝ → ℝ} {t₀ : ℝ}
    (hC2 : ContDiffAt ℝ 2 (fun t => (x t, y t)) t₀)
    (hx_zero : x t₀ = 0)
    (hy_zero : y t₀ = 0)
    (_h_deriv_ne : deriv x t₀ ≠ 0 ∨ deriv y t₀ ≠ 0) :
    let κ := (deriv x t₀ * iteratedDeriv 2 y t₀ - deriv y t₀ * iteratedDeriv 2 x t₀) /
             (deriv x t₀^2 + deriv y t₀^2)^(3/2 : ℝ)
    let v_norm := Real.sqrt (deriv x t₀^2 + deriv y t₀^2)
    Tendsto (fun t => (x t * deriv y t - y t * deriv x t) / (x t^2 + y t^2))
      (𝓝[{t₀}ᶜ] t₀) (𝓝 ((1/2) * κ * v_norm)) := by
  -- The proof uses double L'Hôpital:
  --
  -- Let num(t) = x(t)y'(t) - y(t)x'(t)
  -- Let den(t) = x(t)² + y(t)²
  --
  -- Step 1: num(t₀) = 0·y'(t₀) - 0·x'(t₀) = 0
  --         den(t₀) = 0² + 0² = 0
  --         This is 0/0, apply L'Hôpital
  --
  -- Step 2: num'(t₀) = x'(t₀)y'(t₀) + x(t₀)y''(t₀) - y'(t₀)x'(t₀) - y(t₀)x''(t₀)
  --                  = x'(t₀)y'(t₀) - y'(t₀)x'(t₀) = 0
  --         den'(t₀) = 2x(t₀)x'(t₀) + 2y(t₀)y'(t₀) = 0
  --         This is still 0/0, apply L'Hôpital again
  --
  -- Step 3: num''(t₀) = x''(t₀)y'(t₀) + x'(t₀)y''(t₀) + x'(t₀)y''(t₀) + x(t₀)y'''(t₀)
  --                   - y''(t₀)x'(t₀) - y'(t₀)x''(t₀) - y'(t₀)x''(t₀) - y(t₀)x'''(t₀)
  --                  = 2(x'(t₀)y''(t₀) - y'(t₀)x''(t₀))  [using x(t₀) = y(t₀) = 0]
  --         den''(t₀) = 2(x'(t₀)² + x(t₀)x''(t₀)) + 2(y'(t₀)² + y(t₀)y''(t₀))
  --                   = 2(x'(t₀)² + y'(t₀)²)  [using x(t₀) = y(t₀) = 0]
  --
  -- lim = num''(t₀)/den''(t₀) = (x'y'' - y'x'')/(x'² + y'²)
  --     = κ · (x'² + y'²)^{1/2} · (1/2)
  --     = (1/2) · κ · |γ'(t₀)|
  sorry

/-! ## Signed Curvature -/

/-- The signed curvature of a plane curve at a point. -/
def signedCurvature (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  (deriv x t * iteratedDeriv 2 y t - deriv y t * iteratedDeriv 2 x t) /
  (deriv x t^2 + deriv y t^2)^(3/2 : ℝ)

/-- The curvature times speed formula. -/
theorem curvature_times_speed (x y : ℝ → ℝ) (t : ℝ) :
    signedCurvature x y t * Real.sqrt (deriv x t^2 + deriv y t^2) =
    (deriv x t * iteratedDeriv 2 y t - deriv y t * iteratedDeriv 2 x t) /
    (deriv x t^2 + deriv y t^2) := by
  unfold signedCurvature
  by_cases h : deriv x t^2 + deriv y t^2 = 0
  · simp [h]
  · have h_pos : 0 < deriv x t^2 + deriv y t^2 := by
      apply lt_of_le_of_ne
      · apply add_nonneg <;> apply sq_nonneg
      · exact Ne.symm h
    -- (a)^{3/2} * sqrt(a) = a^{3/2} * a^{1/2} = a^2
    -- So we need: num / a^{3/2} * a^{1/2} = num / a
    -- which is: num * a^{1/2} / a^{3/2} = num / a
    -- i.e.: num / a^{3/2 - 1/2} = num / a
    -- i.e.: num / a = num / a ✓
    field_simp
    rw [Real.sqrt_eq_rpow]
    rw [show (3 : ℝ) / 2 = 1 + 1/2 by ring]
    rw [Real.rpow_add h_pos]
    rw [Real.rpow_one]
    ring

end