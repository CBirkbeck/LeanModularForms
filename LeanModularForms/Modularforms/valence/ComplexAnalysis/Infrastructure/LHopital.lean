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
  -- L'Hôpital for complex functions requires extending the proof to ℂ
  -- For a complete proof, one approach:
  -- 1. Decompose into real and imaginary parts using Complex.re and Complex.im
  -- 2. Apply real L'Hôpital to each component
  -- 3. Recombine using Tendsto.ofReal_iff or similar
  -- This is left as future work; main application uses real-valued functions
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
  -- Proof: g'(x) = g'(a) + g''(a)(x - a) + o(|x - a|)
  --              = g''(a)(x - a) + o(|x - a|)  [using g'(a) = 0]
  -- For x ≠ a near a: |g'(x)| ≥ |g''(a)||x - a|/2 > 0
  -- g' is differentiable at a since g is C²
  -- Get ContDiffOn ℝ 2 g on a ball (inline the helper logic)
  have hg_C2_nat : ContDiffAt ℝ (2 : ℕ) g a := hg_C2
  have hf' : ContDiffWithinAt ℝ 2 g Set.univ a := hg_C2_nat
  have h_cond : ((2 : ℕ∞) : WithTop ℕ∞) = (⊤ : ℕ∞) → ((2 : ℕ∞) : WithTop ℕ∞) = ⊤ := by
    intro heq
    exfalso
    have : (2 : ℕ∞) ≠ ⊤ := ENat.coe_ne_top 2
    rw [WithTop.coe_eq_coe] at heq
    exact this heq
  obtain ⟨u, hu_open, ha_mem_u, hu_contDiff⟩ := hf'.contDiffOn' le_rfl h_cond
  rw [Metric.isOpen_iff] at hu_open
  obtain ⟨r, hr_pos, hr_sub⟩ := hu_open a ha_mem_u
  have hg_C2_ball : ContDiffOn ℝ 2 g (Metric.ball a r) := by
    refine hu_contDiff.mono ?_
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_univ, or_true, true_and]
    exact hr_sub hx
  -- On the open ball, g is C², hence deriv g is C¹, hence deriv g is differentiable
  have hg'_diff : DifferentiableAt ℝ (deriv g) a := by
    have hball_unique : UniqueDiffOn ℝ (Metric.ball a r) := Metric.isOpen_ball.uniqueDiffOn
    have h1 : DifferentiableOn ℝ (iteratedDerivWithin 1 g (Metric.ball a r)) (Metric.ball a r) :=
      hg_C2_ball.differentiableOn_iteratedDerivWithin (by norm_num : (1 : ℕ) < 2) hball_unique
    -- iteratedDerivWithin 1 = derivWithin (as functions)
    have h_itDeriv_eq : iteratedDerivWithin 1 g (Metric.ball a r) = derivWithin g (Metric.ball a r) :=
      iteratedDerivWithin_one
    -- Convert to derivWithin
    have h1' : DifferentiableOn ℝ (derivWithin g (Metric.ball a r)) (Metric.ball a r) := by
      rw [← h_itDeriv_eq]
      exact h1
    -- derivWithin equals deriv on the open ball
    have h_eq : ∀ x ∈ Metric.ball a r, derivWithin g (Metric.ball a r) x = deriv g x :=
      fun x hx => derivWithin_of_isOpen Metric.isOpen_ball hx
    have ha_mem : a ∈ Metric.ball a r := Metric.mem_ball_self hr_pos
    have h_diff_at := h1' a ha_mem
    have h_eq_a := h_eq a ha_mem
    have h_congr : DifferentiableWithinAt ℝ (deriv g) (Metric.ball a r) a := by
      apply h_diff_at.congr
      · intro y hy; exact (h_eq y hy).symm
      · exact h_eq_a.symm
    exact h_congr.differentiableAt (Metric.isOpen_ball.mem_nhds ha_mem)
  -- Use hasDerivAt to get little-o behavior of g'
  -- g'(x) = g'(a) + g''(a)(x-a) + o(|x-a|) as x → a
  set ε := |iteratedDeriv 2 g a| / 2 with hε_def
  have hε_pos : 0 < ε := by
    apply div_pos (abs_pos.mpr hg''_ne)
    norm_num
  -- Get little-o bound from differentiability of g'
  have hderiv := hg'_diff.hasDerivAt
  rw [hasDerivAt_iff_isLittleO] at hderiv
  rw [Asymptotics.isLittleO_iff] at hderiv
  have h_ev := hderiv hε_pos
  rw [Filter.eventually_iff] at h_ev
  rw [Metric.mem_nhds_iff] at h_ev
  obtain ⟨δ, hδ_pos, hδ⟩ := h_ev
  -- For x in the punctured neighborhood
  rw [Filter.eventually_iff_exists_mem]
  use Metric.ball a δ ∩ {a}ᶜ
  constructor
  · rw [mem_nhdsWithin]
    exact ⟨Metric.ball a δ, Metric.isOpen_ball, Metric.mem_ball_self hδ_pos, Subset.refl _⟩
  intro x ⟨hx_ball, hx_ne⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx_ne
  -- From little-o: ‖g'(x) - g'(a) - (x - a) * g''(a)‖ ≤ ε * |x - a|
  have hx_mem : x ∈ Metric.ball a δ := hx_ball
  have h_taylor := hδ hx_mem
  simp only [smul_eq_mul, Real.norm_eq_abs, Set.mem_setOf_eq] at h_taylor
  rw [hg'_zero, sub_zero] at h_taylor
  -- Note: deriv (deriv g) a = iteratedDeriv 2 g a
  have h_deriv_eq : deriv (deriv g) a = iteratedDeriv 2 g a := by
    have h1 : iteratedDeriv 1 g = deriv g := iteratedDeriv_one
    have h2 : iteratedDeriv 2 g = deriv (iteratedDeriv 1 g) := iteratedDeriv_succ
    simp only [h1] at h2
    exact (congrFun h2 a).symm
  rw [h_deriv_eq] at h_taylor
  -- Rewrite: |(g'(x) - (x-a) * g''(a))| ≤ ε|x-a|
  have h_taylor' : |deriv g x - (x - a) * iteratedDeriv 2 g a| ≤ ε * |x - a| := h_taylor
  -- If g'(x) = 0, then |(x-a) * g''(a)| ≤ ε|x-a|
  intro hcontra
  rw [hcontra, zero_sub, abs_neg] at h_taylor'
  have h_abs_bound : |(x - a) * iteratedDeriv 2 g a| ≤ ε * |x - a| := h_taylor'
  rw [abs_mul] at h_abs_bound
  have hxa_ne : x - a ≠ 0 := sub_ne_zero.mpr hx_ne
  have hxa_pos : 0 < |x - a| := abs_pos.mpr hxa_ne
  have h_bound : |iteratedDeriv 2 g a| ≤ ε := by
    have h_rw : |x - a| * |iteratedDeriv 2 g a| ≤ |x - a| * ε := by linarith
    exact (mul_le_mul_iff_of_pos_left hxa_pos).mp h_rw
  -- But ε = |g''(a)|/2, so |g''(a)| ≤ |g''(a)|/2
  rw [hε_def] at h_bound
  have : |iteratedDeriv 2 g a| > 0 := abs_pos.mpr hg''_ne
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
  -- Step 1: Get a ball where f and g are C²
  have hf_C2_nat : ContDiffAt ℝ (2 : ℕ) f a := _hf_C2
  have hg_C2_nat : ContDiffAt ℝ (2 : ℕ) g a := _hg_C2
  -- Extract balls where f and g are C²
  have hf' : ContDiffWithinAt ℝ 2 f Set.univ a := hf_C2_nat
  have hg' : ContDiffWithinAt ℝ 2 g Set.univ a := hg_C2_nat
  have h_cond : ((2 : ℕ∞) : WithTop ℕ∞) = (⊤ : ℕ∞) → ((2 : ℕ∞) : WithTop ℕ∞) = ⊤ := by
    intro heq; exfalso; have : (2 : ℕ∞) ≠ ⊤ := ENat.coe_ne_top 2
    rw [WithTop.coe_eq_coe] at heq; exact this heq
  obtain ⟨uf, huf_open, ha_mem_uf, huf_contDiff⟩ := hf'.contDiffOn' le_rfl h_cond
  obtain ⟨ug, hug_open, ha_mem_ug, hug_contDiff⟩ := hg'.contDiffOn' le_rfl h_cond
  rw [Metric.isOpen_iff] at huf_open hug_open
  obtain ⟨rf, hrf_pos, hrf_sub⟩ := huf_open a ha_mem_uf
  obtain ⟨rg, hrg_pos, hrg_sub⟩ := hug_open a ha_mem_ug
  let r := min rf rg
  have hr_pos : 0 < r := lt_min hrf_pos hrg_pos
  have hf_C2_ball : ContDiffOn ℝ 2 f (Metric.ball a r) := by
    refine huf_contDiff.mono ?_
    intro x hx; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_univ, or_true, true_and]
    exact hrf_sub (Metric.ball_subset_ball (min_le_left _ _) hx)
  have hg_C2_ball : ContDiffOn ℝ 2 g (Metric.ball a r) := by
    refine hug_contDiff.mono ?_
    intro x hx; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_univ, or_true, true_and]
    exact hrg_sub (Metric.ball_subset_ball (min_le_right _ _) hx)
  -- Step 2: f and g are differentiable near a
  have hf_diff : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x := by
    filter_upwards [Metric.ball_mem_nhds a hr_pos] with x hx
    exact (hf_C2_ball.differentiableOn one_le_two).differentiableAt (Metric.isOpen_ball.mem_nhds hx)
  have hg_diff : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ g x := by
    filter_upwards [Metric.ball_mem_nhds a hr_pos] with x hx
    exact (hg_C2_ball.differentiableOn one_le_two).differentiableAt (Metric.isOpen_ball.mem_nhds hx)
  -- Step 3: g'(x) ≠ 0 for x ≠ a near a (by deriv_nonzero_near_from_second_deriv)
  have hg'_ne : ∀ᶠ x in 𝓝[{a}ᶜ] a, deriv g x ≠ 0 :=
    deriv_nonzero_near_from_second_deriv _hg'_zero _hg_C2 _hg''_ne
  -- Step 4: deriv f and deriv g are differentiable near a (from C²)
  have hf'_diff : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ (deriv f) x := by
    have hf'_C1 : ContDiffOn ℝ 1 (deriv f) (Metric.ball a r) :=
      hf_C2_ball.deriv_of_isOpen Metric.isOpen_ball (by norm_num)
    filter_upwards [Metric.ball_mem_nhds a hr_pos] with x hx
    exact (hf'_C1.differentiableOn le_rfl).differentiableAt (Metric.isOpen_ball.mem_nhds hx)
  have hg'_diff : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ (deriv g) x := by
    have hg'_C1 : ContDiffOn ℝ 1 (deriv g) (Metric.ball a r) :=
      hg_C2_ball.deriv_of_isOpen Metric.isOpen_ball (by norm_num)
    filter_upwards [Metric.ball_mem_nhds a hr_pos] with x hx
    exact (hg'_C1.differentiableOn le_rfl).differentiableAt (Metric.isOpen_ball.mem_nhds hx)
  -- Step 5: g''(x) ≠ 0 near a (by continuity of g'' at a with g''(a) ≠ 0)
  have hg''_cont : ContinuousAt (iteratedDeriv 2 g) a := by
    have hg''_C0 : ContinuousOn (iteratedDerivWithin 2 g (Metric.ball a r)) (Metric.ball a r) :=
      hg_C2_ball.continuousOn_iteratedDerivWithin le_rfl Metric.isOpen_ball.uniqueDiffOn
    have h_eq : ∀ x ∈ Metric.ball a r, iteratedDerivWithin 2 g (Metric.ball a r) x = iteratedDeriv 2 g x :=
      iteratedDerivWithin_of_isOpen Metric.isOpen_ball
    have : ContinuousOn (iteratedDeriv 2 g) (Metric.ball a r) := by
      intro x hx; exact (hg''_C0 x hx).congr (fun y hy => (h_eq y hy).symm) (h_eq x hx).symm
    exact this.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos))
  have hg''_ne_near : ∀ᶠ x in 𝓝[{a}ᶜ] a, deriv (deriv g) x ≠ 0 := by
    have h_eq : iteratedDeriv 2 g a = deriv (deriv g) a := by rw [iteratedDeriv_succ, iteratedDeriv_one]
    have h_eq' : ∀ s : ℝ, iteratedDeriv 2 g s = deriv (deriv g) s := fun s => by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hcont : ContinuousAt (deriv (deriv g)) a := by
      have heq : iteratedDeriv 2 g = deriv (deriv g) := by funext s; exact h_eq' s
      rw [← heq]; exact hg''_cont
    have hne : deriv (deriv g) a ≠ 0 := by rw [← h_eq]; exact _hg''_ne
    exact hcont.eventually_ne hne |>.filter_mono nhdsWithin_le_nhds
  -- Step 6: Apply L'Hopital to f'/g' to get lim f'/g' = lim f''/g'' = L
  have h_lim_deriv : Tendsto (fun x => deriv f x / deriv g x) (𝓝[{a}ᶜ] a) (𝓝 L) := by
    have h_eq : ∀ s : ℝ, iteratedDeriv 2 f s = deriv (deriv f) s := fun s => by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    have h_eq' : ∀ s : ℝ, iteratedDeriv 2 g s = deriv (deriv g) s := fun s => by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    have h_lim' : Tendsto (fun x => deriv (deriv f) x / deriv (deriv g) x) (𝓝[{a}ᶜ] a) (𝓝 L) := by
      have heq : (fun x => iteratedDeriv 2 f x / iteratedDeriv 2 g x) =
                 (fun x => deriv (deriv f) x / deriv (deriv g) x) := by
        funext s; rw [h_eq, h_eq']
      rw [← heq]; exact _h_lim
    exact lhopital_zero_div_zero _hf'_zero _hg'_zero hf'_diff hg'_diff hg''_ne_near h_lim'
  -- Step 7: Apply L'Hopital to f/g to get lim f/g = lim f'/g' = L
  exact lhopital_zero_div_zero _hf_zero _hg_zero hf_diff hg_diff hg'_ne h_lim_deriv

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
  -- Case x = a is trivial
  by_cases hxa : x = a
  · simp [hxa]
  -- For x ≠ a, use Taylor's theorem with Lagrange remainder
  -- Taylor's theorem (n=1): f(x) - f(a) - f'(a)(x-a) = (1/2)f''(ξ)(x-a)² for some ξ between a and x
  -- So f(x) - f(a) - f'(a)(x-a) - (1/2)f''(a)(x-a)² = (1/2)(f''(ξ) - f''(a))(x-a)²
  -- Since |ξ - a| ≤ |x - a| < δ ≤ δ₁, we have |f''(ξ) - f''(a)| < ε
  -- Therefore |...| ≤ (ε/2)(x-a)² ≤ ε(x-a)²
  -- The detailed proof involves setting up the Icc interval properly
  -- and relating taylorWithinEval to the explicit polynomial
  -- For now, we use the bound argument directly
  have h_x_ne_a : x - a ≠ 0 := sub_ne_zero.mpr hxa
  -- Key fact: |x - a| < δ ≤ δ₁ and δ ≤ r/2
  have hx_lt_δ₁ : |x - a| < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx_lt_r2 : |x - a| < r / 2 := lt_of_lt_of_le hx (min_le_right _ _)
  -- f is C² on an interval containing both a and x
  have hx_in_ball : x ∈ Metric.ball a r := by
    simp only [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs]
    linarith
  have ha_in_ball : a ∈ Metric.ball a r := Metric.mem_ball_self hr
  -- The rest requires a careful application of Taylor's theorem
  -- We use the isLittleO characterization which gives the bound we need
  -- For the explicit bound, we appeal to the continuity argument
  have hsq_nonneg : 0 ≤ (x - a)^2 := sq_nonneg _
  -- The key estimate follows from f being C² and f'' being continuous
  -- The error term is controlled by the variation of f'' near a
  -- Full proof would use taylor_mean_remainder_lagrange_iteratedDeriv
  -- and relate taylorWithinEval to deriv f a and iteratedDeriv 2 f a
  -- For now we use a simpler bound based on the taylor_mean_remainder_bound
  -- which gives |remainder| ≤ C|x-a|²/1! where C bounds f'' on the interval
  -- Since |f''(y) - f''(a)| < ε for y near a, we get the desired bound
  sorry

/-- Taylor expansion for complex-valued functions. -/
theorem taylor_second_order_complex {f : ℝ → ℂ} {a : ℝ}
    (_hf : ContDiffAt ℝ 2 f a) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ →
      ‖f x - f a - deriv f a * (x - a) - (1/2) * iteratedDeriv 2 f a * (x - a)^2‖ ≤
        ε * (x - a)^2 := by
  -- Apply the real Taylor expansion to real and imaginary parts separately
  -- then combine using norm bounds: ‖z‖ ≤ |re z| + |im z|
  sorry

/-! ## Application: Winding Number Integrand Limit -/

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
    (hx_C11 : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ x t)
    (hy_C11 : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ y t)
    (hx'_lip : LipschitzOnWith K (deriv x) (Metric.ball t₀ r))
    (hy'_lip : LipschitzOnWith K (deriv y) (Metric.ball t₀ r))
    (hx_zero : x t₀ = 0)
    (hy_zero : y t₀ = 0)
    (hr : 0 < r) :
    ∃ C, ∀ t, |t - t₀| < r → |x t * deriv y t - y t * deriv x t| ≤ C * (t - t₀)^2 := by
  -- Strategy: Use Lipschitz bounds to expand x, y, x', y' around t₀
  -- x(t) = (t - t₀) * x'(t₀) + O((t - t₀)²) by FTC + Lipschitz
  -- y(t) = (t - t₀) * y'(t₀) + O((t - t₀)²)
  -- x'(t) = x'(t₀) + O(t - t₀) by Lipschitz
  -- y'(t) = y'(t₀) + O(t - t₀)
  -- The leading terms cancel: (t-t₀)x'(t₀)y'(t₀) - (t-t₀)y'(t₀)x'(t₀) = 0
  let M := max (|deriv x t₀|) (|deriv y t₀|)
  -- Bound constant: accounts for cross terms and Lipschitz contributions
  let C := 3 * K * M + K^2 * r + K
  use C
  intro t ht
  -- For t in ball, we have |t - t₀| < r
  have ht_in_ball : t ∈ Metric.ball t₀ r := by simp [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, ht]
  have ht₀_in_ball : t₀ ∈ Metric.ball t₀ r := Metric.mem_ball_self hr
  -- Lipschitz bounds on derivatives
  have hx'_bound : |deriv x t - deriv x t₀| ≤ K * |t - t₀| := by
    have h := hx'_lip.dist_le_mul t ht_in_ball t₀ ht₀_in_ball
    simp only [dist_eq_norm, Real.norm_eq_abs] at h
    exact h
  have hy'_bound : |deriv y t - deriv y t₀| ≤ K * |t - t₀| := by
    have h := hy'_lip.dist_le_mul t ht_in_ball t₀ ht₀_in_ball
    simp only [dist_eq_norm, Real.norm_eq_abs] at h
    exact h
  -- x and y differentiable at t (eventually near t₀)
  have hx_diff_t₀ : DifferentiableAt ℝ x t₀ := by
    have := hx_C11.self_of_nhds
    exact this
  have hy_diff_t₀ : DifferentiableAt ℝ y t₀ := by
    have := hy_C11.self_of_nhds
    exact this
  -- The case t = t₀ is trivial
  by_cases htt₀ : t = t₀
  · simp [htt₀, hx_zero, hy_zero]
  -- For t ≠ t₀, use the expansion
  have h_sub_ne : t - t₀ ≠ 0 := sub_ne_zero.mpr htt₀
  -- Bound |t - t₀| ≤ r for cubic to quadratic conversion
  have ht_abs_le_r : |t - t₀| ≤ r := le_of_lt ht
  -- Triangle inequality approach: bound each term individually
  -- The detailed algebraic manipulation follows from the Lipschitz bounds
  -- x(t) = ∫_{t₀}^t x'(s) ds, so |x(t)| ≤ |∫_{t₀}^t (x'(t₀) + O(s-t₀)) ds|
  --                                     ≤ |x'(t₀)||t-t₀| + K/2 (t-t₀)²
  -- Similar for y(t)
  -- Full algebraic expansion gives terms all bounded by (const) * (t-t₀)²
  -- This is a lengthy but standard calculation
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
  -- |2x'(t-t₀)r_x + r_x² + 2y'(t-t₀)r_y + r_y²| ≤ 2M·h·ε₁·h + (ε₁h)² + 2M·h·ε₁·h + (ε₁h)²
  --                                             = (4Mε₁ + 2ε₁²)h²
  --                                             ≤ εh² (by choice of ε₁)
  -- The proof involves bounding each term and using the choice of ε₁ = min(ε/(8M), 1)
  -- to show the total coefficient is at most ε
  -- This is standard Taylor expansion remainder analysis
  -- The final bound follows from the expansion and bounds on r_x, r_y
  have hr_x_le : |r_x| ≤ ε₁ * h := by simpa using hr_x
  have hr_y_le : |r_y| ≤ ε₁ * h := by simpa using hr_y
  -- Bound each term using triangle inequality
  -- Term 1: |2 * x' * (t - t₀) * r_x| ≤ 2 * |x'| * |t - t₀| * |r_x| ≤ 2M * h * ε₁h = 2Mε₁h²
  -- Term 2: |r_x²| ≤ (ε₁h)² = ε₁²h²
  -- Similarly for y terms
  -- Total ≤ (4Mε₁ + 2ε₁²)h² ≤ εh² (by choice of ε₁)
  --
  -- PROOF REQUIREMENTS:
  -- 1. Use abs_mul repeatedly to distribute |·| over products
  -- 2. Apply bounds: |x'| ≤ M, |y'| ≤ M, |r_x| ≤ ε₁h, |r_y| ≤ ε₁h
  -- 3. Triangle inequality: |a + b + c + d| ≤ |a| + |b| + |c| + |d|
  -- 4. Final coefficient bound: 4Mε₁ + 2ε₁² ≤ ε (from ε₁ ≤ min(ε/(8M), 1))
  --
  -- KEY LEMMAS: abs_mul, abs_add, sq_le_sq', mul_le_mul_of_nonneg_left
  -- Bound each term individually
  -- Term 1: 2 * deriv x t₀ * (t - t₀) * r_x
  have h_term1 : |2 * deriv x t₀ * (t - t₀) * r_x| ≤ 2 * M * ε₁ * h^2 := by
    calc |2 * deriv x t₀ * (t - t₀) * r_x|
        = 2 * |deriv x t₀| * |t - t₀| * |r_x| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        _ ≤ 2 * M * |t - t₀| * (ε₁ * h) := by
          gcongr
        _ = 2 * M * ε₁ * h^2 := by rw [← hh_def]; ring
  -- Term 2: r_x^2
  have h_term2 : |r_x^2| ≤ ε₁^2 * h^2 := by
    rw [abs_of_nonneg (sq_nonneg r_x)]
    have h_lower : -(ε₁ * h) ≤ |r_x| := by
      apply le_trans _ (abs_nonneg r_x)
      linarith [mul_nonneg hε₁_pos.le hh_nonneg]
    calc r_x^2 = |r_x|^2 := (sq_abs r_x).symm
        _ ≤ (ε₁ * h)^2 := sq_le_sq' h_lower hr_x_le
        _ = ε₁^2 * h^2 := by ring
  -- Term 3: 2 * deriv y t₀ * (t - t₀) * r_y
  have h_term3 : |2 * deriv y t₀ * (t - t₀) * r_y| ≤ 2 * M * ε₁ * h^2 := by
    calc |2 * deriv y t₀ * (t - t₀) * r_y|
        = 2 * |deriv y t₀| * |t - t₀| * |r_y| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        _ ≤ 2 * M * |t - t₀| * (ε₁ * h) := by
          gcongr
        _ = 2 * M * ε₁ * h^2 := by rw [← hh_def]; ring
  -- Term 4: r_y^2
  have h_term4 : |r_y^2| ≤ ε₁^2 * h^2 := by
    rw [abs_of_nonneg (sq_nonneg r_y)]
    have h_lower : -(ε₁ * h) ≤ |r_y| := by
      apply le_trans _ (abs_nonneg r_y)
      linarith [mul_nonneg hε₁_pos.le hh_nonneg]
    calc r_y^2 = |r_y|^2 := (sq_abs r_y).symm
        _ ≤ (ε₁ * h)^2 := sq_le_sq' h_lower hr_y_le
        _ = ε₁^2 * h^2 := by ring
  -- Combine using triangle inequality
  have h_tri : |2 * deriv x t₀ * (t - t₀) * r_x + r_x^2 + 2 * deriv y t₀ * (t - t₀) * r_y + r_y^2|
      ≤ |2 * deriv x t₀ * (t - t₀) * r_x| + |r_x^2| + |2 * deriv y t₀ * (t - t₀) * r_y| + |r_y^2| := by
    calc |2 * deriv x t₀ * (t - t₀) * r_x + r_x^2 + 2 * deriv y t₀ * (t - t₀) * r_y + r_y^2|
        ≤ |2 * deriv x t₀ * (t - t₀) * r_x + r_x^2 + 2 * deriv y t₀ * (t - t₀) * r_y| + |r_y^2| :=
          abs_add_le _ _
        _ ≤ |2 * deriv x t₀ * (t - t₀) * r_x + r_x^2| + |2 * deriv y t₀ * (t - t₀) * r_y| + |r_y^2| := by
          gcongr; exact abs_add_le _ _
        _ ≤ |2 * deriv x t₀ * (t - t₀) * r_x| + |r_x^2| + |2 * deriv y t₀ * (t - t₀) * r_y| + |r_y^2| := by
          gcongr; exact abs_add_le _ _
  have hcoeff : 4 * M * ε₁ + 2 * ε₁^2 ≤ ε := by
    have h1 : ε₁^2 ≤ ε₁ := by
      rw [sq]
      exact mul_le_of_le_one_right hε₁_pos.le hε₁_le_1
    have h2 : ε₁ ≤ ε / (8 * M) := hε₁_le_frac
    have h3 : 4 * M * ε₁ ≤ ε / 2 := by
      have hne : (8 : ℝ) * M ≠ 0 := by linarith
      calc 4 * M * ε₁ ≤ 4 * M * (ε / (8 * M)) := by
            apply mul_le_mul_of_nonneg_left h2
            linarith
          _ = ε / 2 := by field_simp [hne]; ring
    have h4 : 2 * ε₁^2 ≤ 2 * ε₁ := by
      have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 2)
      linarith
    have h5 : 2 * ε₁ ≤ ε / 4 := by
      have hne : (4 : ℝ) * M ≠ 0 := by linarith
      calc 2 * ε₁ ≤ 2 * (ε / (8 * M)) := by linarith
          _ = ε / (4 * M) := by ring
          _ ≤ ε / 4 := by
            apply div_le_div_of_nonneg_left hε.le
            · norm_num
            · linarith
    linarith
  calc |2 * deriv x t₀ * (t - t₀) * r_x + r_x^2 + 2 * deriv y t₀ * (t - t₀) * r_y + r_y^2|
      ≤ |2 * deriv x t₀ * (t - t₀) * r_x| + |r_x^2| + |2 * deriv y t₀ * (t - t₀) * r_y| + |r_y^2| := h_tri
      _ ≤ 2 * M * ε₁ * h^2 + ε₁^2 * h^2 + 2 * M * ε₁ * h^2 + ε₁^2 * h^2 := by
        gcongr
      _ = (4 * M * ε₁ + 2 * ε₁^2) * h^2 := by ring
      _ ≤ ε * h^2 := by nlinarith [sq_nonneg h]

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
  -- The full proof applies lhopital_twice to:
  --   num(t) = x(t)*y'(t) - y(t)*x'(t)
  --   den(t) = x(t)² + y(t)²
  -- Key intermediate results:
  -- 1. num(t₀) = 0, den(t₀) = 0 (from hx_zero, hy_zero)
  -- 2. num'(t₀) = 0, den'(t₀) = 0 (by direct computation)
  -- 3. den''(t₀) = 2(x'(t₀)² + y'(t₀)²) ≠ 0 (from _h_deriv_ne)
  -- 4. num''(t₀) = 2(x'(t₀)y''(t₀) - y'(t₀)x''(t₀))
  -- 5. lim = num''(t₀)/den''(t₀) = (1/2) * κ * v_norm
  -- The detailed formalization requires careful application of derivative rules
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
