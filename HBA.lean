/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 35875906-8695-427f-b519-5a04520112af
-/

/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Topology.Homotopy.Path
import Mathlib.MeasureTheory.Integral.CircleIntegral


/-!
# Bridge Lemmas: Connecting to Mathlib's Homotopy and Contour Integration

This file establishes the connection between our principal value definitions and
mathlib's proven results for contour integration and homotopy invariance.

## Strategy

Isabelle's `Cauchy_theorem_homotopic_paths` states that if two paths are homotopic
within a domain where f is holomorphic, their contour integrals are equal.

Mathlib provides:
* `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable` - Cauchy's theorem
* `Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable` -
   Circle integrals agree on annulus (essentially homotopy for concentric circles)
* `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` - Rectangle version
* `Path.Homotopic` - Definition of path homotopy

## Main Lemmas

* `contourIntegral_eq_of_homotopic` - Contour integrals agree for homotopic paths
* `windingNumber_eq_of_homotopic` - Winding numbers agree for homotopic paths
* `circleIntegral_eq_interval_integral` - Connect circle and interval integrals

## Key Mathlib References

The following mathlib lemmas are the building blocks for proving homotopy invariance:

1. **Cauchy's theorem for circles**:
   `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`:
   For f continuous on closed ball and holomorphic on interior, ∮ f = 0.

2. **Cauchy's theorem for rectangles**:
   `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`:
   The boundary integral of a holomorphic function on a rectangle is zero.

3. **Winding number for circles**:
   `circleIntegral.integral_sub_inv_of_mem_ball`:
   For w inside the circle, ∮ (z-w)⁻¹ dz = 2πi.

   `circleIntegral.integral_sub_center_inv`:
   For circle centered at c, ∮ (z-c)⁻¹ dz = 2πi (R ≠ 0).

4. **Homotopy for concentric circles**:
   `Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable`:
   Circle integrals agree when the integrand is holomorphic on the annulus.

## Isabelle References

* `Cauchy_Integral_Theorem.thy` - `Cauchy_theorem_homotopic_paths`
* `Winding_Numbers.thy` - `winding_number_homotopy_paths`
-/

open Complex MeasureTheory Set Filter Topology

open scoped Real Interval

noncomputable section

/-! ## Cauchy's Theorem Bridge Lemmas -/

/-- Cauchy's theorem for a circle: the integral of a holomorphic function is zero.

    **Proof**: Direct application of `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`
    with empty exceptional set.
-/
theorem cauchyTheorem_circle' (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hf_cont : ContinuousOn f (Metric.closedBall c R))
    (hf_diff : DifferentiableOn ℂ f (Metric.ball c R)) :
    circleIntegral (fun z => f z) c R = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty hf_cont
  intro z hz
  exact hf_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz.1)

/-- Cauchy's theorem for rectangles. -/
theorem cauchyTheorem_rectangle' (f : ℂ → ℂ) (z w : ℂ)
    (hf_cont : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im))
    (hf_diff : DifferentiableOn ℂ f
      (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ Set.Ioo (min z.im w.im) (max z.im w.im))) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
    (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
    I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w hf_cont hf_diff

/-! ## Winding Number Key Formulas -/

/-- The integral of 1/(z - w) around a circle containing w equals 2πi.

    **Mathlib**: `circleIntegral.integral_sub_inv_of_mem_ball`
-/
theorem windingNumber_circle_one' (c w : ℂ) (R : ℝ) (hw : w ∈ Metric.ball c R) :
    circleIntegral (fun z => (z - w)⁻¹) c R = 2 * Real.pi * I :=
  circleIntegral.integral_sub_inv_of_mem_ball hw

/-- The integral of 1/(z - c) around a circle centered at c equals 2πi (for R ≠ 0).

    **Mathlib**: `circleIntegral.integral_sub_center_inv`
-/
theorem windingNumber_circle_center' (c : ℂ) (R : ℝ) (hR : R ≠ 0) :
    circleIntegral (fun z => (z - c)⁻¹) c R = 2 * Real.pi * I :=
  circleIntegral.integral_sub_center_inv c hR

/-- Circle integrals are equal on concentric circles if the integrand is holomorphic
    on the annulus. This is homotopy invariance for circular paths.

    **Mathlib**: `Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable`
-/
theorem circleIntegral_eq_on_annulus' (f : ℂ → ℂ) (c : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r ≤ R)
    (hf_cont : ContinuousOn f (Metric.closedBall c R \ Metric.ball c r))
    (hf_diff : DifferentiableOn ℂ f (Metric.ball c R \ Metric.closedBall c r)) :
    circleIntegral (fun z => (z - c)⁻¹ • f z) c R =
    circleIntegral (fun z => (z - c)⁻¹ • f z) c r := by
  apply Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
    hr hrR countable_empty hf_cont
  intro z hz
  have hopen : IsOpen (Metric.ball c R \ Metric.closedBall c r) :=
    Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  exact hf_diff.differentiableAt (hopen.mem_nhds hz.1)

/-! ## Helper Lemmas for Limits -/

/-- When the cutoff condition is eventually always satisfied, the PV integral
    equals the classical integral. This is the key step for
    `generalizedWindingNumber_eq_classical_away`.

    **Isabelle parallel**: Part of the proof of `winding_number_valid_path`
-/
theorem limUnder_eventually_eq_const {α : Type*} [TopologicalSpace α]
    {f : α → ℂ} {l : Filter α} {c : ℂ} [l.NeBot] (hf : ∀ᶠ x in l, f x = c) :
    limUnder l f = c := by
  have heq : f =ᶠ[l] fun _ => c := hf
  have htends : Tendsto f l (𝓝 c) := Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  exact Filter.Tendsto.limUnder_eq htends

/-- The PV integrand equals the classical integrand when the curve is bounded away
    from the singularity.
-/
theorem cauchyPrincipalValueIntegrand_eq_classical
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (z₀ : ℂ) (ε δ : ℝ) (t : ℝ)
    (hεδ : ε < δ) (hδ : δ ≤ ‖γ t - z₀‖) :
    cauchyPrincipalValueIntegrand' f γ z₀ ε t = f (γ t) * deriv γ t := by
  unfold cauchyPrincipalValueIntegrand'
  simp only [ite_eq_left_iff, not_lt]
  intro h
  linarith

/-! ## Helper Lemmas for Parametric Integrals -/

/-- Interval integral is continuous in a parameter when the integrand is continuous.

    **Isabelle parallel**: `contour_integral_uniform_limit` and related lemmas
    in `Contour_Integration.thy`
-/
theorem intervalIntegral_continuous_on_param
    (f : ℝ → ℝ → ℂ) (a b : ℝ) (S : Set ℝ) (hab : a ≤ b)
    (hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hf_int : ∀ s ∈ S, IntervalIntegrable (f · s) volume a b) :
    ContinuousOn (fun s => ∫ t in a..b, f t s) S := by
  -- Use continuousAt_of_dominated_interval at each point
  intro s₀ hs₀
  apply ContinuousAt.continuousWithinAt
  -- Need: ae-measurable, bounded, bound integrable, pointwise continuity
  have hmeas : ∀ s, AEStronglyMeasurable (f · s) (volume.restrict (Set.uIoc a b)) := by
    intro s
    apply Continuous.aestronglyMeasurable
    exact hf_cont.comp (continuous_id.prodMk continuous_const)
  -- The key is showing there's a uniform bound near s₀
  -- Since we only have integrability (not a bound), use a local bound argument
  -- For now, use the simpler approach when f is continuous on compact [a,b] × [s₀-1, s₀+1]
  have hcont_pt : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → ContinuousAt (f t) s₀ := by
    filter_upwards with t _
    exact (hf_cont.comp (continuous_const.prodMk continuous_id)).continuousAt
  -- Use local compactness: f is bounded on compact [a,b] × [s₀-1, s₀+1]
  -- Then apply dominated convergence
  have hcompact : IsCompact (Icc a b ×ˢ Icc (s₀ - 1) (s₀ + 1)) :=
    isCompact_Icc.prod isCompact_Icc
  have hbound : ∃ M : ℝ, ∀ p ∈ Icc a b ×ˢ Icc (s₀ - 1) (s₀ + 1), ‖(fun p => f p.1 p.2) p‖ ≤ M :=
    hcompact.exists_bound_of_continuousOn hf_cont.continuousOn
  obtain ⟨M, hM⟩ := hbound
  -- Apply continuousAt_of_dominated_interval with bound = M
  apply intervalIntegral.continuousAt_of_dominated_interval
  · -- AEStronglyMeasurable for s near s₀
    filter_upwards with s
    exact hmeas s
  · -- Uniform bound near s₀
    have h_nhd : Ioo (s₀ - 1) (s₀ + 1) ∈ 𝓝 s₀ := by
      apply Ioo_mem_nhds <;> linarith
    filter_upwards [h_nhd] with s hs
    filter_upwards with t
    intro ht
    by_cases htab : t ∈ Icc a b
    · have hp : (t, s) ∈ Icc a b ×ˢ Icc (s₀ - 1) (s₀ + 1) := by
        constructor
        · exact htab
        · exact ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      exact hM (t, s) hp
    · -- t ∉ [a,b] means t ∉ uIoc a b anyway (for a ≤ b)
      rw [Set.uIoc_of_le hab] at ht
      exact absurd (Ioc_subset_Icc_self ht) htab
  · -- Bound integrable
    exact intervalIntegrable_const
  · -- Pointwise continuity
    exact hcont_pt

/-- Stronger version: uniform bound implies integrability and continuity.

    **Isabelle parallel**: `contour_integral_continuous_on_linepath_param`
-/
theorem intervalIntegral_continuous_on_param_of_bound
    (f : ℝ → ℝ → ℂ) (a b : ℝ) (S : Set ℝ) (hab : a ≤ b)
    (hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (M : ℝ) (hM : ∀ t ∈ Icc a b, ∀ s ∈ S, ‖f t s‖ ≤ M) :
    ContinuousOn (fun s => ∫ t in a..b, f t s) S := by
  -- The proof uses dominated convergence theorem with the uniform bound M
  intro s₀ hs₀
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
  · -- AEStronglyMeasurable for all s near s₀
    filter_upwards with s
    apply Continuous.aestronglyMeasurable
    exact hf_cont.comp (continuous_id.prodMk continuous_const)
  · -- Uniform bound: ‖f t s‖ ≤ M for all s ∈ S and t ∈ [a,b]
    apply eventually_of_mem self_mem_nhdsWithin
    intro s hs
    filter_upwards with t
    intro ht
    rw [Set.uIoc_of_le hab] at ht
    have ht' : t ∈ Icc a b := Ioc_subset_Icc_self ht
    exact hM t ht' s hs
  · -- Bound integrable: M is integrable on [a,b]
    exact intervalIntegrable_const
  · -- Pointwise continuity: f(t, ·) is continuous at s₀ for each t
    filter_upwards with t _
    apply ContinuousAt.continuousWithinAt
    exact (hf_cont.comp (continuous_const.prodMk continuous_id)).continuousAt

/-! ## Helper Lemmas for Winding Number Integrality -/

/-- The exponential of the integral of γ'/(γ - z₀) equals the ratio of endpoints.

    This is the key lemma for showing winding numbers are integers.
    exp(∫_a^b γ'(t)/(γ(t) - z₀) dt) = (γ(b) - z₀)/(γ(a) - z₀)

    **Isabelle parallel**: Related to `winding_number_exp_2pi` in `Winding_Numbers.thy`
-/
theorem exp_integral_eq_endpoint_ratio
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    Complex.exp (∫ t in a..b, deriv γ t / (γ t - z₀)) = (γ b - z₀) / (γ a - z₀) := by
  -- Strategy: Define F(t) = ∫_a^t γ'/(γ-z₀), then show (γ-z₀)·exp(-F) is constant
  -- using that d/dt[(γ-z₀)·exp(-F)] = γ'·exp(-F) - (γ-z₀)·exp(-F)·γ'/(γ-z₀) = 0
  -- Conclude: (γ(b)-z₀)·exp(-F(b)) = (γ(a)-z₀)·1, so exp(F(b)) = (γ(b)-z₀)/(γ(a)-z₀)
  --
  -- First, show the integrand is continuous on [a,b]
  have h_integrand_cont : ContinuousOn (fun t => deriv γ t / (γ t - z₀)) (Icc a b) := by
    apply ContinuousOn.div hγ'_cont
    · exact hγ_cont.sub continuousOn_const
    · intro t ht
      exact sub_ne_zero.mpr (hγ_avoid t ht)
  -- The integrand is integrable
  have h_int : IntervalIntegrable (fun t => deriv γ t / (γ t - z₀)) volume a b :=
    h_integrand_cont.intervalIntegrable_of_Icc (le_of_lt hab)
  -- Define F(t) = ∫_a^t integrand
  let F : ℝ → ℂ := fun t => ∫ s in a..t, deriv γ s / (γ s - z₀)
  -- F is differentiable with F'(t) = integrand(t) at interior points
  -- Define G(t) = (γ(t) - z₀) * exp(-F(t))
  let G : ℝ → ℂ := fun t => (γ t - z₀) * Complex.exp (-F t)
  -- Step 1: Show G has derivative 0 on (a,b)
  -- Step 2: Apply constant_of_derivWithin_zero to conclude G(a) = G(b)
  -- Step 3: G(a) = (γ(a) - z₀) * 1, G(b) = (γ(b) - z₀) * exp(-F(b))
  -- Step 4: Conclude exp(F(b)) = (γ(b) - z₀) / (γ(a) - z₀)
  --
  -- For G(a): F(a) = ∫_a^a ... = 0
  have hFa : F a = 0 := intervalIntegral.integral_same
  have hGa : G a = γ a - z₀ := by
    simp only [G, hFa, neg_zero, Complex.exp_zero, mul_one]
  -- For G(b): relate to the goal
  have hFb : F b = ∫ t in a..b, deriv γ t / (γ t - z₀) := rfl
  have hGb : G b = (γ b - z₀) * Complex.exp (-(∫ t in a..b, deriv γ t / (γ t - z₀))) := rfl
  -- Show G is constant by proving G' = 0 (using FTC and product rule)
  -- This requires proving: γ' * exp(-F) + (γ - z₀) * exp(-F) * (-γ'/(γ - z₀)) = 0
  -- which simplifies to: γ' * exp(-F) - γ' * exp(-F) = 0
  have hG_const : ∀ t ∈ Icc a b, G t = G a := by
    -- Strategy: Apply constant_of_has_deriv_right_zero
    -- This only requires: G continuous on [a,b] and has right derivative 0 on [a,b)
    --
    -- Key facts:
    -- 1. F is differentiable with F'(t) = γ'(t)/(γ(t)-z₀) by FTC
    -- 2. G = (γ - z₀) * exp(-F), by product rule:
    --    G' = γ' * exp(-F) - (γ - z₀) * (γ'/(γ-z₀)) * exp(-F) = 0
    --
    -- First show G is continuous on [a,b]
    have hG_cont : ContinuousOn G (Icc a b) := by
      -- G = (γ - z₀) * exp(-F)
      -- γ - z₀ is continuous on [a,b]
      have h1 : ContinuousOn (fun t => γ t - z₀) (Icc a b) := hγ_cont.sub continuousOn_const
      -- F is continuous on [a,b] (integral of continuous function)
      have hF_cont : ContinuousOn F (Icc a b) := by
        have huIcc : Set.uIcc a b = Icc a b := Set.uIcc_of_le (le_of_lt hab)
        have ha_mem : a ∈ Set.uIcc a b := left_mem_uIcc
        have := intervalIntegral.continuousOn_primitive_interval' h_int ha_mem
        rw [huIcc] at this
        exact this
      -- exp(-F) is continuous
      have h2 : ContinuousOn (fun t => Complex.exp (-F t)) (Icc a b) :=
        Complex.continuous_exp.comp_continuousOn hF_cont.neg
      exact h1.mul h2
    -- Show F has derivative at each point in (a, b)
    have hF_hasDerivAt : ∀ t ∈ Ioo a b, HasDerivAt F (deriv γ t / (γ t - z₀)) t := by
      intro t ht
      have huIcc_at : Set.uIcc a t ⊆ Set.uIcc a b := by
        rw [Set.uIcc_of_le (le_of_lt ht.1), Set.uIcc_of_le (le_of_lt hab)]
        exact Icc_subset_Icc le_rfl (le_of_lt ht.2)
      have h_int_at : IntervalIntegrable (fun s => deriv γ s / (γ s - z₀)) volume a t :=
        h_int.mono_set huIcc_at
      have h_cont_at : ContinuousAt (fun s => deriv γ s / (γ s - z₀)) t :=
        h_integrand_cont.continuousAt (Icc_mem_nhds ht.1 ht.2)
      have h_meas : StronglyMeasurableAtFilter (fun s => deriv γ s / (γ s - z₀)) (𝓝 t) := by
        have hopen : IsOpen (Ioo a b) := isOpen_Ioo
        have hcont_on : ∀ x ∈ Ioo a b, ContinuousAt (fun s => deriv γ s / (γ s - z₀)) x :=
          fun x hx => h_integrand_cont.continuousAt (Icc_mem_nhds hx.1 hx.2)
        exact ContinuousAt.stronglyMeasurableAtFilter hopen hcont_on t ht
      exact intervalIntegral.integral_hasDerivAt_right h_int_at h_meas h_cont_at
    -- Show G has right derivative 0 on [a,b)
    have hG_deriv_right : ∀ t ∈ Ico a b, HasDerivWithinAt G 0 (Ici t) t := by
      intro t ht
      -- For t ∈ [a, b), we need t ∈ (a,b) for hγ_diff, but we have a ≤ t
      -- The issue is that hγ_diff only gives differentiability on (a,b), not [a,b)
      -- We need to handle the case t = a separately, or extend the hypothesis
      --
      -- However, for this proof, since γ is continuous and γ' is continuous on [a,b],
      -- and the derivative γ' is the one from hγ'_cont, we actually have that
      -- γ has a derivative at all points of (a,b) that extends continuously to a.
      --
      -- For now, we use a simple approach: note that constant_of_has_deriv_right_zero
      -- needs derivative on Ico, but we only have it on Ioo. The gap is at t = a.
      -- Let's verify this works when a < t < b:
      by_cases ha_eq : t = a
      · -- Case t = a: need to show HasDerivWithinAt G 0 (Ici a) a
        -- This is the right derivative at the left endpoint
        -- Since γ' is continuous at a and γ is differentiable near a (on the right),
        -- we need to show G' → 0 from the right
        --
        -- F(a) = 0, and F is differentiable from the right at a with F'(a+) = γ'(a)/(γ(a)-z₀)
        -- G = (γ - z₀) * exp(-F), so G'(a+) = γ'(a) * 1 + (γ(a) - z₀) * 1 * (-γ'(a)/(γ(a)-z₀)) = 0
        -- We prove this by computing the limit of the difference quotient
        have hne_a : γ a - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoid a (left_mem_Icc.mpr (le_of_lt hab)))
        -- This case needs more careful handling using continuity at the boundary
        -- For simplicity, we use the fact that deriv γ is continuous on [a,b] and γ is differentiable on (a,b)
        -- This implies γ is right-differentiable at a with derivative (deriv γ a)
        -- Similarly for F
        rw [ha_eq]
        -- Use hasDerivWithinAt_Ici_of_tendsto_deriv: need to show deriv G → 0 as t → a+
        -- First, show G is differentiable on (a,b)
        -- The derivative of G is 0 on (a,b), so it converges to 0
        have h_Ioo_mem : Ioo a b ∈ nhdsWithin a (Ioi a) := by
          rw [mem_nhdsWithin]
          exact ⟨Iio b, isOpen_Iio, mem_Iio.mpr hab, fun x ⟨hxb, hxa⟩ => ⟨hxa, hxb⟩⟩
        apply hasDerivWithinAt_Ici_of_tendsto_deriv
        · -- DifferentiableOn G (Ioo a b)
          intro t ht
          have hγ_t : DifferentiableAt ℝ γ t := hγ_diff t ht
          have hF_t : HasDerivAt F (deriv γ t / (γ t - z₀)) t := hF_hasDerivAt t ht
          have hexpF : DifferentiableAt ℝ (fun s => Complex.exp (-F s)) t :=
            (Complex.differentiable_exp.differentiableAt).comp t hF_t.differentiableAt.neg
          exact ((hγ_t.sub_const z₀).mul hexpF).differentiableWithinAt
        · -- ContinuousWithinAt G (Ioo a b) a
          exact hG_cont.continuousWithinAt (left_mem_Icc.mpr (le_of_lt hab)) |>.mono Ioo_subset_Icc_self
        · -- Ioo a b ∈ nhdsWithin a (Ioi a)
          exact h_Ioo_mem
        · -- Tendsto (deriv G) (nhdsWithin a (Ioi a)) (nhds 0)
          -- deriv G = 0 on (a,b), so we show it converges to 0
          -- Key: use that for t in (a,b), deriv G t = 0
          have h_deriv_zero : ∀ t ∈ Ioo a b, deriv G t = 0 := by
            intro t ht
            have hγ_t : DifferentiableAt ℝ γ t := hγ_diff t ht
            have hF_t : HasDerivAt F (deriv γ t / (γ t - z₀)) t := hF_hasDerivAt t ht
            have hexpF : HasDerivAt (fun s => Complex.exp (-F s))
                (Complex.exp (-F t) * (-(deriv γ t / (γ t - z₀)))) t := hF_t.neg.cexp
            have h1 : HasDerivAt (fun s => γ s - z₀) (deriv γ t) t := hγ_t.hasDerivAt.sub_const z₀
            have hne_t : γ t - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoid t (Ioo_subset_Icc_self ht))
            have hprod : HasDerivAt G (deriv γ t * Complex.exp (-F t) +
                (γ t - z₀) * (Complex.exp (-F t) * (-(deriv γ t / (γ t - z₀))))) t := h1.mul hexpF
            have hderiv_eq : deriv γ t * Complex.exp (-F t) +
                (γ t - z₀) * (Complex.exp (-F t) * (-(deriv γ t / (γ t - z₀)))) = 0 := by
              field_simp; ring
            exact hprod.deriv.trans hderiv_eq
          apply Filter.Tendsto.congr'
          · filter_upwards [h_Ioo_mem] with t ht
            exact (h_deriv_zero t ht).symm
          · exact tendsto_const_nhds
      · -- Case a < t < b: both γ and F are differentiable at t
        have ht' : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm ha_eq), ht.2⟩
        have hγ_t : DifferentiableAt ℝ γ t := hγ_diff t ht'
        have hF_t : HasDerivAt F (deriv γ t / (γ t - z₀)) t := hF_hasDerivAt t ht'
        have hexpF : HasDerivAt (fun s => Complex.exp (-F s)) (Complex.exp (-F t) * (-(deriv γ t / (γ t - z₀)))) t :=
          hF_t.neg.cexp
        have hG_hasDerivAt : HasDerivAt G 0 t := by
          have h1 : HasDerivAt (fun s => γ s - z₀) (deriv γ t) t :=
            (hγ_t.hasDerivAt.sub_const z₀)
          have hprod := h1.mul hexpF
          convert hprod using 1
          have hne_t : γ t - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoid t (Ioo_subset_Icc_self ht'))
          field_simp
          ring
        exact hG_hasDerivAt.hasDerivWithinAt
    -- Apply constant_of_has_deriv_right_zero
    exact constant_of_has_deriv_right_zero hG_cont hG_deriv_right
  -- Apply constancy at b
  have hGeq : G b = G a := hG_const b (right_mem_Icc.mpr (le_of_lt hab))
  -- Unpack: (γ b - z₀) * exp(-∫...) = γ a - z₀
  rw [hGa, hGb] at hGeq
  -- Solve for exp(∫...)
  have hne : γ b - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoid b (right_mem_Icc.mpr (le_of_lt hab)))
  have hne' : γ a - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoid a (left_mem_Icc.mpr (le_of_lt hab)))
  -- From hGeq: (γ b - z₀) * exp(-∫) = γ a - z₀
  -- So: exp(-∫) = (γ a - z₀) / (γ b - z₀)
  have h1 : Complex.exp (-(∫ t in a..b, deriv γ t / (γ t - z₀))) = (γ a - z₀) / (γ b - z₀) := by
    field_simp at hGeq ⊢
    exact hGeq
  -- Take reciprocal: exp(∫) = (γ b - z₀) / (γ a - z₀)
  -- From h1: exp(-∫) = (γ a - z₀) / (γ b - z₀)
  -- So: exp(∫) = (exp(-∫))⁻¹ = ((γ a - z₀) / (γ b - z₀))⁻¹ = (γ b - z₀) / (γ a - z₀)
  have hexp_pos : Complex.exp (∫ t in a..b, deriv γ t / (γ t - z₀)) =
      (Complex.exp (-(∫ t in a..b, deriv γ t / (γ t - z₀))))⁻¹ := by
    rw [Complex.exp_neg, inv_inv]
  rw [hexp_pos, h1, inv_div]

/-- For closed curves, the ratio equals 1, so the integral is 2πi times an integer.

    **Isabelle parallel**: `winding_number_valid_path` combined with
    `valid_path_imp_closed`
-/
theorem integral_closed_curve_eq_two_pi_int
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    ∃ n : ℤ, ∫ t in a..b, deriv γ t / (γ t - z₀) = 2 * Real.pi * I * n := by
  -- From exp_integral_eq_endpoint_ratio:
  -- exp(∫ γ'/(γ-z₀)) = (γ(b) - z₀)/(γ(a) - z₀) = 1 (since γ(a) = γ(b))
  -- Therefore ∫ γ'/(γ-z₀) = 2πi·n for some integer n
  have hexp : Complex.exp (∫ t in a..b, deriv γ t / (γ t - z₀)) = 1 := by
    rw [exp_integral_eq_endpoint_ratio γ a b z₀ hab hγ_cont hγ_diff hγ_avoid hγ'_cont]
    rw [hγ_closed]
    have hne : γ b - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoid b (right_mem_Icc.mpr (le_of_lt hab)))
    exact div_self hne
  -- exp(w) = 1 implies w = 2πi·n for some integer n
  rw [Complex.exp_eq_one_iff] at hexp
  obtain ⟨n, hn⟩ := hexp
  exact ⟨n, by rw [hn]; ring⟩

/-! ## Helper Lemmas for Homotopy -/

/-- The infimum distance from a compact set to a point outside it is positive.

    **Isabelle parallel**: `setdist_gt_0_compact_closed` in various files
-/
theorem infDist_pos_of_compact_of_notMem {X : Type*} [MetricSpace X]
    (K : Set X) (z : X) (hK : IsCompact K) (hK_ne : K.Nonempty) (hz : z ∉ K) :
    0 < Metric.infDist z K :=
  (hK.isClosed.notMem_iff_infDist_pos hK_ne).mp hz

/-- Uniform distance bound for continuous homotopy on compact domain.

    If H : [a,b] × [0,1] → ℂ is continuous and avoids z₀, there exists δ > 0
    such that ‖H(t,s) - z₀‖ ≥ δ for all (t,s).

    **Isabelle parallel**: Used implicitly in `winding_number_homotopy_paths`
-/
theorem homotopy_uniform_avoidance
    (H : ℝ × ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀) :
    ∃ δ > 0, ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, δ ≤ ‖H (t, s) - z₀‖ := by
  -- The image H(Icc a b × Icc 0 1) is compact (continuous image of compact)
  -- and avoids z₀, so infDist > 0
  have hcompact : IsCompact (H '' (Icc a b ×ˢ Icc (0:ℝ) 1)) := by
    exact (isCompact_Icc.prod isCompact_Icc).image hH_cont
  have hnonempty : (H '' (Icc a b ×ˢ Icc (0:ℝ) 1)).Nonempty := by
    use H (a, 0)
    exact ⟨(a, 0), ⟨left_mem_Icc.mpr (le_of_lt hab), left_mem_Icc.mpr zero_le_one⟩, rfl⟩
  have hz_notin : z₀ ∉ H '' (Icc a b ×ˢ Icc (0:ℝ) 1) := by
    intro ⟨⟨t, s⟩, ⟨ht, hs⟩, heq⟩
    exact hH_avoid t ht s hs heq
  have hδ := infDist_pos_of_compact_of_notMem _ z₀ hcompact hnonempty hz_notin
  refine ⟨Metric.infDist z₀ (H '' (Icc a b ×ˢ Icc (0:ℝ) 1)), hδ, fun t ht s hs => ?_⟩
  have hmem : H (t, s) ∈ H '' (Icc a b ×ˢ Icc (0:ℝ) 1) := ⟨(t, s), ⟨ht, hs⟩, rfl⟩
  calc Metric.infDist z₀ (H '' (Icc a b ×ˢ Icc (0:ℝ) 1))
      ≤ dist z₀ (H (t, s)) := Metric.infDist_le_dist_of_mem hmem
    _ = ‖H (t, s) - z₀‖ := by rw [Complex.dist_eq, norm_sub_rev]

/-! ## Homotopy Bridge Lemmas -/

/-- Combining continuity and integrality: a continuous integer-valued
    function on a connected set is constant.

    This is a key lemma for showing homotopy invariance of winding numbers.
-/
theorem continuous_integer_valued_constant
    (f : ℝ → ℂ) (hf_cont : ContinuousOn f (Icc (0:ℝ) 1))
    (hf_int : ∀ s ∈ Icc (0:ℝ) 1, ∃ n : ℤ, f s = n) :
    f 0 = f 1 := by
  -- Strategy: f is locally constant because integers are isolated in ℂ.
  -- A locally constant function on a connected set is constant.
  -- Define g as the restriction of f to [0,1]
  let g : Icc (0:ℝ) 1 → ℂ := fun x => f x.val
  have hg_loc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    -- The fiber g⁻¹{y} is open because integers are isolated
    by_cases hy : ∃ n : ℤ, y = n
    · -- If y is an integer, use continuity and the fact that f only takes integer values
      obtain ⟨n, rfl⟩ := hy
      have heq : g ⁻¹' {↑n} = g ⁻¹' (Metric.ball (n : ℂ) 1) := by
        ext ⟨x, hx⟩
        simp only [g, mem_preimage, mem_singleton_iff, Metric.mem_ball]
        constructor
        · intro heq
          rw [heq]
          simp only [dist_self, zero_lt_one]
        · intro hdist
          obtain ⟨m, hm⟩ := hf_int x hx
          rw [hm] at hdist ⊢
          -- Use the isometry: dist between different integers is ≥ 1
          have h1 : dist (m : ℂ) (n : ℂ) < 1 := hdist
          rw [Complex.dist_eq] at h1
          -- ‖(m : ℂ) - (n : ℂ)‖ = ‖((m - n : ℤ) : ℂ)‖ = |(m - n : ℝ)| = (|m-n| : ℝ)
          rw [show (m : ℂ) - (n : ℂ) = ((m - n : ℤ) : ℂ) by push_cast; ring] at h1
          rw [Complex.norm_intCast, ← Int.cast_abs] at h1
          -- Now h1 : (|m - n| : ℝ) < 1
          have h2 : |m - n| < 1 := by exact_mod_cast h1
          have hmn : m - n = 0 := Int.abs_lt_one_iff.mp h2
          simp only [sub_eq_zero] at hmn
          rw [hmn]
      rw [heq]
      have hcont_g : Continuous g := hf_cont.restrict
      exact hcont_g.isOpen_preimage _ Metric.isOpen_ball
    · -- If y is not an integer, the fiber is empty (hence open)
      convert isOpen_empty
      ext ⟨x, hx⟩
      simp only [g, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro heq
      obtain ⟨n, hn⟩ := hf_int x hx
      exact hy ⟨n, heq.symm.trans hn⟩
  -- Apply the locally constant property on the connected set [0,1]
  have h01 : (⟨0, left_mem_Icc.mpr (by norm_num : (0:ℝ) ≤ 1)⟩ : Icc (0:ℝ) 1) ∈ (Set.univ : Set (Icc (0:ℝ) 1)) := trivial
  have h11 : (⟨1, right_mem_Icc.mpr (by norm_num : (0:ℝ) ≤ 1)⟩ : Icc (0:ℝ) 1) ∈ (Set.univ : Set (Icc (0:ℝ) 1)) := trivial
  have hconn : IsPreconnected (Set.univ : Set (Icc (0:ℝ) 1)) := isPreconnected_univ
  exact hg_loc.apply_eq_of_isPreconnected hconn h01 h11

/- Aristotle failed to find a proof. -/
/-- The key property that makes winding numbers vary continuously with
    parameters: if γ_s is a family of curves depending continuously on s,
    then s ↦ n_{z₀}(γ_s) is continuous.

    **Proof Strategy**:
    The winding number for a continuous closed curve avoiding z₀ is an integer.
    Integers are isolated in ℂ, so a continuous function to integers on a connected
    domain must be locally constant. A locally constant function is continuous.
-/
theorem windingNumber_continuous_in_param
    (γ : ℝ × ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hγ_cont : Continuous γ)
    (hγ_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, γ (t, s) ≠ z₀) :
    ContinuousOn (fun s => generalizedWindingNumber' (fun t => γ (t, s)) a b z₀) (Icc 0 1) := by
  -- Get uniform lower bound on distance to z₀
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := homotopy_uniform_avoidance γ a b z₀ hab hγ_cont hγ_avoid
  -- **Proof Strategy**:
  -- 1. Since γ avoids z₀ with uniform separation δ > 0, for any ε < δ,
  --    the cutoff condition ‖γ(t,s) - z₀‖ > ε is always satisfied.
  -- 2. Therefore the PV integral equals the ordinary integral for all ε < δ.
  -- 3. The generalized winding number equals (2πi)⁻¹ times this ordinary integral.
  -- 4. To show continuity in s, we use that the integrand is continuous in (t,s)
  --    and bounded (since ‖γ - z₀‖ ≥ δ > 0 gives ‖(γ-z₀)⁻¹‖ ≤ δ⁻¹).
  --
  -- **Key obstacle**: The integral involves deriv(γ(·,s)), the derivative with respect
  -- to t. Without assuming γ is differentiable in t, this derivative may not exist
  -- or may not be continuous.
  --
  -- **Resolution approaches**:
  -- A. If γ is C¹ in t uniformly in s, use dominated convergence on the integrand.
  -- B. Use the topological definition of winding number via argument/exponential lift.
  -- C. For the specific use case (homotopy), note that the winding number is
  --    integer-valued for closed curves, so it must be locally constant.
  --
  -- We use approach C: The winding number for closed curves avoiding z₀ is an integer.
  -- A continuous function from connected [0,1] to the discrete set ℤ ⊂ ℂ must be constant.
  -- However, this requires proving the winding number IS integer-valued first.
  --
  -- For a complete proof using approach A (assuming smooth homotopy):
  -- The integrand is f(t,s) = (γ(t,s) - z₀)⁻¹ * ∂ₜγ(t,s)
  -- Bound: |f(t,s)| ≤ δ⁻¹ * sup|∂ₜγ| which is integrable if ∂ₜγ is bounded
  -- Continuity: f is continuous in s if γ and ∂ₜγ are jointly continuous
  -- Apply dominated convergence to get continuity of ∫f(t,s)dt in s.
  --
  -- Admitted for now - requires either:
  -- (1) Additional differentiability assumptions on γ, or
  -- (2) Topological winding number theory (covering space arguments)
  sorry

/-- Two closed curves are homotopic in ℂ \ {z₀} if there exists a continuous
    deformation avoiding z₀.
-/
def ClosedCurvesHomotopicAvoiding (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    Continuous H ∧
    (∀ t ∈ Icc a b, H (t, 0) = γ₀ t) ∧
    (∀ t ∈ Icc a b, H (t, 1) = γ₁ t) ∧
    (∀ s ∈ Icc (0:ℝ) 1, H (a, s) = H (b, s)) ∧  -- Closed at each stage
    (∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀)

-- Avoids z₀

/-- Helper: if two functions agree on [a,b] and their derivatives agree a.e.,
    they have the same generalized winding number.

    The proof shows that for each ε > 0, the cutoff integrals are equal,
    hence the limits (winding numbers) are equal.
-/
theorem generalizedWindingNumber'_eq_of_eq_on
    (f g : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (heq_val : ∀ t ∈ Icc a b, f t = g t)
    (heq_deriv : ∀ᵐ t ∂volume.restrict (Set.uIoc a b), deriv f t = deriv g t) :
    generalizedWindingNumber' f a b z₀ = generalizedWindingNumber' g a b z₀ := by
  -- Both winding numbers are limits of integrals, and the integrands agree a.e.
  -- Strategy: Show the limit functions are pointwise equal, then limUnder gives same result.
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  simp only [sub_zero, deriv_sub_const]
  -- Show the functions inside limUnder are equal
  -- The integrands agree a.e. because f = g on [a,b] and deriv f = deriv g a.e.
  -- Therefore the integrals are equal for all ε, hence the limits are equal.
  have h_fun_eq : (fun ε => ∫ t in a..b, if ‖f t - z₀‖ > ε then (f t - z₀)⁻¹ * deriv f t else 0) =
                  (fun ε => ∫ t in a..b, if ‖g t - z₀‖ > ε then (g t - z₀)⁻¹ * deriv g t else 0) := by
    funext ε
    apply intervalIntegral.integral_congr_ae
    -- The goal is ∀ᵐ x, x ∈ uIoc a b → (integrand f) = (integrand g)
    -- Use heq_val and heq_deriv to show this
    have h_uIoc : Set.uIoc a b = Ioc a b := Set.uIoc_of_le (le_of_lt hab)
    rw [h_uIoc]
    rw [h_uIoc] at heq_deriv
    -- Need to convert from ae (volume.restrict (Ioc a b)) to the goal form
    -- This is straightforward: the set where deriv f = deriv g has full measure
    -- and on that set the integrands are equal (using heq_val for function values)
    have h_ae : ∀ᵐ t ∂volume.restrict (Ioc a b), deriv f t = deriv g t := heq_deriv
    rw [ae_restrict_iff' measurableSet_Ioc] at h_ae
    filter_upwards [h_ae] with t ht
    intro ht_mem
    have hderiv_eq : deriv f t = deriv g t := ht ht_mem
    have hval_eq : f t = g t := heq_val t (Ioc_subset_Icc_self ht_mem)
    simp only [hval_eq, hderiv_eq]
  rw [h_fun_eq]

/-- Smooth version: Two closed curves are homotopic in ℂ \ {z₀} via a smooth homotopy.
    This stronger hypothesis makes the proofs tractable via integral arguments.
-/
def SmoothClosedCurvesHomotopicAvoiding (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    Continuous H ∧
    (∀ t ∈ Icc a b, H (t, 0) = γ₀ t) ∧
    (∀ t ∈ Icc a b, H (t, 1) = γ₁ t) ∧
    (∀ s ∈ Icc (0:ℝ) 1, H (a, s) = H (b, s)) ∧  -- Closed at each stage
    (∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀) ∧  -- Avoids z₀
    -- Differentiability in t (needed for winding number integrality)
    (∀ t ∈ Ioo a b, ∀ s ∈ Icc (0:ℝ) 1, DifferentiableAt ℝ (fun t' => H (t', s)) t) ∧
    -- The t-derivative is jointly continuous (needed for dominated convergence)
    (Continuous (fun p : ℝ × ℝ => deriv (fun t' => H (t', p.2)) p.1))

/- Aristotle failed to find a proof. -/
/-- Key lemma: If two closed curves are homotopic avoiding z₀, their winding
    numbers around z₀ are equal.

    **Proof strategy** (from Isabelle's `winding_number_homotopy_paths`):
    1. The function s ↦ n_{z₀}(H(·, s)) is continuous in s
    2. It takes values in ℤ (since each H(·, s) avoids z₀)
    3. Continuous + integer-valued on [0,1] → constant
    4. Hence n_{z₀}(γ₀) = n_{z₀}(γ₁)

    The key mathlib ingredient is showing the circle integral ∮ (z-z₀)⁻¹ dz
    varies continuously with parameters and is always 2πi times an integer.
-/
theorem windingNumber_eq_of_homotopic_closed
    (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hγ₀_cont : ContinuousOn γ₀ (Icc a b))
    (hγ₁_cont : ContinuousOn γ₁ (Icc a b))
    (hhom : ClosedCurvesHomotopicAvoiding γ₀ γ₁ a b z₀) :
    generalizedWindingNumber' γ₀ a b z₀ = generalizedWindingNumber' γ₁ a b z₀ := by
  -- Get the homotopy
  obtain ⟨H, hH_cont, hH0, hH1, hH_closed, hH_avoid⟩ := hhom
  -- **Proof Strategy** (from Isabelle's `winding_number_homotopy_paths`):
  -- 1. Define n(s) := winding_number(H(·, s), z₀) for s ∈ [0,1]
  -- 2. Show n is integer-valued (each H(·,s) is a closed curve avoiding z₀)
  -- 3. Show n is continuous on [0,1]
  -- 4. Apply continuous_integer_valued_constant: n(0) = n(1)
  -- 5. n(0) = winding_number(γ₀), n(1) = winding_number(γ₁)
  --
  -- Define the winding number function
  let n : ℝ → ℂ := fun s => generalizedWindingNumber' (fun t => H (t, s)) a b z₀
  -- Step 1: Show n is continuous on [0,1]
  have hn_cont : ContinuousOn n (Icc 0 1) :=
    windingNumber_continuous_in_param H a b z₀ hab hH_cont hH_avoid
  -- Step 2: Show n takes integer values on [0,1]
  -- Each curve H(·, s) is closed (by hH_closed) and avoids z₀ (by hH_avoid)
  -- The winding number of such a curve is an integer
  have hn_int : ∀ s ∈ Icc (0:ℝ) 1, ∃ m : ℤ, n s = m := by
    intro s hs
    -- **Mathematical content**: For closed curves avoiding z₀, the winding number is an integer.
    --
    -- **Proof approaches**:
    -- 1. **Exponential covering space**: exp(2πi · n(γ)) = (γ(b) - z₀)/(γ(a) - z₀) = 1
    --    Hence 2πi · n(γ) = 2πi · m for some integer m (from `integral_closed_curve_eq_two_pi_int`)
    --
    -- 2. **Topological degree theory**: The winding number is the degree of the normalized
    --    curve γ/|γ| : S¹ → S¹, which is always an integer.
    --
    -- **Current gap**: `ClosedCurvesHomotopicAvoiding` only requires continuity of H,
    -- not differentiability in t. The theorem `windingNumber_integer_of_closed_avoiding`
    -- requires differentiability in t and continuous derivative.
    --
    -- **For smooth homotopy** (using `SmoothClosedCurvesHomotopicAvoiding`):
    -- We would have ∀ t ∈ Ioo a b, DifferentiableAt ℝ (fun t' => H (t', s)) t
    -- and Continuous (fun p => deriv (fun t' => H (t', p.2)) p.1)
    -- Then apply `windingNumber_integer_of_closed_avoiding` to H(·, s).
    --
    -- **Admitted**: Requires either smooth homotopy or topological degree theory infrastructure.
    sorry
  -- Step 3: Apply continuous_integer_valued_constant to get n(0) = n(1)
  have heq : n 0 = n 1 := continuous_integer_valued_constant n hn_cont hn_int
  -- Step 4: Relate n(0) and n(1) to the original winding numbers
  -- n(0) = generalizedWindingNumber'(H(·,0)) and H(·,0) = γ₀ on [a,b]
  -- n(1) = generalizedWindingNumber'(H(·,1)) and H(·,1) = γ₁ on [a,b]
  --
  -- For the winding number definitions to match, we need the functions to agree
  -- on [a,b] (which they do by hH0 and hH1), and their derivatives to agree
  -- (which follows if the functions are equal on a neighborhood of [a,b])
  --
  -- The key insight: generalizedWindingNumber' only depends on γ restricted to [a,b]
  -- and its derivative on (a,b). If H(·,0) = γ₀ on [a,b], then the winding numbers agree.
  have hn0_eq : n 0 = generalizedWindingNumber' γ₀ a b z₀ := by
    -- **Goal**: Show n(0) = generalizedWindingNumber' γ₀ a b z₀
    -- where n(s) = generalizedWindingNumber' (fun t => H(t,s)) a b z₀
    --
    -- **Issue**: We have H(t, 0) = γ₀(t) for t ∈ [a,b], but the winding number
    -- depends on both curve values AND derivatives.
    --
    -- **Key facts**:
    -- 1. Function values: H(·, 0) = γ₀ on [a,b] (from hH0)
    -- 2. Derivatives: If f = g on [a,b] and both are differentiable at t ∈ (a,b),
    --    then deriv f t = deriv g t (since the limit defining the derivative
    --    uses only values in a neighborhood of t, which is contained in [a,b]).
    --
    -- **Gap**: `ClosedCurvesHomotopicAvoiding` only guarantees continuity of H,
    -- not differentiability in t. If H is not differentiable, deriv (fun t => H(t,0))
    -- may be 0 or undefined, making the integral-based winding number ill-defined.
    --
    -- **Resolution**: For smooth homotopy (see `SmoothClosedCurvesHomotopicAvoiding`),
    -- we have differentiability in t, and the derivatives agree on (a,b).
    -- Then `generalizedWindingNumber'_eq_of_eq_on` gives the result.
    --
    -- **Admitted**: Requires either smooth homotopy or topological degree definition.
    sorry
  have hn1_eq : n 1 = generalizedWindingNumber' γ₁ a b z₀ := by
    -- Same argument as hn0_eq (using hH1 : H(·,1) = γ₁ on [a,b])
    sorry
  rw [← hn0_eq, ← hn1_eq, heq]

/-- The winding number of a closed curve avoiding z₀ is an integer.
    This follows from the fact that the integral of 1/(z-z₀) along a closed
    path is 2πi times an integer.
-/
theorem windingNumber_integer_of_closed_avoiding
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b))
    (hγ_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀) :
    ∃ n : ℤ, generalizedWindingNumber' γ a b z₀ = n := by
  -- Use integral_closed_curve_eq_two_pi_int
  -- First, show the integrand γ'/(γ-z₀) satisfies the hypotheses
  -- For the shifted curve τ(t) = γ(t) - z₀:
  let τ := fun t => γ t - z₀
  have hτ_closed : τ a = τ b := by simp only [τ]; rw [hγ_closed]
  have hτ_cont : ContinuousOn τ (Icc a b) := hγ_cont.sub continuousOn_const
  have hτ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ τ t := fun t ht =>
    (hγ_diff t ht).sub (differentiableAt_const z₀)
  have hτ_avoid : ∀ t ∈ Icc a b, τ t ≠ 0 := fun t ht => sub_ne_zero.mpr (hγ_avoid t ht)
  have hτ'_eq : ∀ t, deriv τ t = deriv γ t := fun t => by simp only [τ, deriv_sub_const]
  have hτ'_cont : ContinuousOn (deriv τ) (Icc a b) := by
    have h : deriv τ = deriv γ := funext hτ'_eq
    rw [h]; exact hγ'_cont
  -- Apply integral_closed_curve_eq_two_pi_int to get integrality
  obtain ⟨n, hn⟩ := integral_closed_curve_eq_two_pi_int τ a b 0 hab hτ_closed hτ_cont
    hτ_diff hτ_avoid hτ'_cont
  -- Now relate this to the generalized winding number
  -- The key is showing generalizedWindingNumber' γ a b z₀ equals (2πi)⁻¹ * ∫ γ'/(γ-z₀)
  -- when γ avoids z₀
  use n
  -- Unfold the definition
  unfold generalizedWindingNumber'
  -- The shifted integral τ'(t)/τ(t) = γ'(t)/(γ(t) - z₀)
  have h_integrand_eq : (fun t => deriv τ t / (τ t - 0)) = (fun t => deriv γ t / (γ t - z₀)) := by
    ext t; simp only [τ, sub_zero, deriv_sub_const]
  rw [h_integrand_eq] at hn
  -- Now show cauchyPrincipalValue' equals the integral when avoiding singularity
  -- Key: since γ avoids z₀, there exists δ > 0 such that for ε < δ, the cutoff has no effect
  -- First find the minimum distance
  have h_compact : IsCompact (γ '' Icc a b) := isCompact_Icc.image_of_continuousOn hγ_cont
  have h_nonempty : (γ '' Icc a b).Nonempty := Set.image_nonempty.mpr (nonempty_Icc.mpr (le_of_lt hab))
  have hz₀_notin : z₀ ∉ γ '' Icc a b := by
    intro ⟨t, ht, heq⟩
    exact hγ_avoid t ht heq
  have hδ : 0 < Metric.infDist z₀ (γ '' Icc a b) :=
    (h_compact.isClosed.notMem_iff_infDist_pos h_nonempty).mp hz₀_notin
  -- For ε < δ, the condition ‖γ t - z₀‖ > ε is always satisfied
  have h_cutoff_trivial : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t ∈ Icc a b, ε < ‖γ t - z₀‖ := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε t ht
    have hmem : γ t ∈ γ '' Icc a b := mem_image_of_mem γ ht
    calc ε < Metric.infDist z₀ (γ '' Icc a b) := (mem_Ioo.mp hε).2
      _ ≤ dist z₀ (γ t) := Metric.infDist_le_dist_of_mem hmem
      _ = ‖γ t - z₀‖ := by rw [Complex.dist_eq, norm_sub_rev]
  -- The PV integral equals the classical integral for small ε
  have h_pv_eq : cauchyPrincipalValue' (·⁻¹) (fun t => γ t - z₀) a b 0 =
      ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t := by
    unfold cauchyPrincipalValue'
    apply limUnder_eventually_eq_const
    filter_upwards [h_cutoff_trivial] with ε hε
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t
    intro ht
    simp only [sub_zero]
    -- ht : t ∈ Ι a b = uIoc a b = Ioc (min a b) (max a b)
    have ht' : t ∈ Icc a b := by
      rw [Set.uIoc_of_le (le_of_lt hab)] at ht
      exact Ioc_subset_Icc_self ht
    have h_cond : ε < ‖γ t - z₀‖ := hε t ht'
    simp only [h_cond, ↓reduceIte, deriv_sub_const]
  -- Relate the integrand forms: (γ t - z₀)⁻¹ * deriv γ t = deriv γ t / (γ t - z₀)
  have h_integrand_eq2 : ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t =
      ∫ t in a..b, deriv γ t / (γ t - z₀) := by
    congr 1; ext t; rw [mul_comm, div_eq_mul_inv]
  rw [h_pv_eq, h_integrand_eq2, hn]
  -- Now: (2πi)⁻¹ * (2πi * n) = n
  field_simp

/-- **Smooth homotopy version**: If two closed curves are smoothly homotopic avoiding z₀,
    their winding numbers are equal.

    This version uses `SmoothClosedCurvesHomotopicAvoiding` which provides the
    differentiability assumptions needed for the proof.

    **Proof strategy**:
    1. Define n(s) = winding number of H(·, s)
    2. Each n(s) is an integer by `windingNumber_integer_of_closed_avoiding`
       (using the differentiability from `SmoothClosedCurvesHomotopicAvoiding`)
    3. n is continuous by dominated convergence (using joint continuity of ∂ₜH)
    4. Continuous integer-valued function on [0,1] is constant
    5. n(0) = n(1) gives the result

    **Note**: This theorem references `windingNumber_integer_of_closed_avoiding` and
    `windingNumber_continuous_in_param` which handle the key steps.
-/
theorem windingNumber_eq_of_smooth_homotopic_closed
    (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hγ₀_cont : ContinuousOn γ₀ (Icc a b))
    (hγ₁_cont : ContinuousOn γ₁ (Icc a b))
    (hγ₀_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ₀ t)
    (hγ₁_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ₁ t)
    (hγ₀'_cont : ContinuousOn (deriv γ₀) (Icc a b))
    (hγ₁'_cont : ContinuousOn (deriv γ₁) (Icc a b))
    (hγ₀_closed : γ₀ a = γ₀ b)
    (hγ₁_closed : γ₁ a = γ₁ b)
    (hhom : SmoothClosedCurvesHomotopicAvoiding γ₀ γ₁ a b z₀) :
    generalizedWindingNumber' γ₀ a b z₀ = generalizedWindingNumber' γ₁ a b z₀ := by
  -- Unpack the smooth homotopy
  obtain ⟨H, hH_cont, hH0, hH1, hH_closed, hH_avoid, hH_diff_t, hH_deriv_cont⟩ := hhom
  -- Define the winding number function
  let n : ℝ → ℂ := fun s => generalizedWindingNumber' (fun t => H (t, s)) a b z₀
  -- Step 1: Each n(s) is an integer (uses windingNumber_integer_of_closed_avoiding)
  have hn_int : ∀ s ∈ Icc (0:ℝ) 1, ∃ m : ℤ, n s = m := by
    intro s hs
    -- For each s, H(·, s) is a closed curve avoiding z₀ with differentiability
    -- The winding number is an integer by windingNumber_integer_of_closed_avoiding
    apply windingNumber_integer_of_closed_avoiding (fun t => H (t, s)) a b z₀ hab
    · -- Closedness: H(a, s) = H(b, s)
      exact hH_closed s hs
    · -- Continuity: H(·, s) is continuous on [a,b]
      exact hH_cont.comp (continuous_id.prodMk continuous_const) |>.continuousOn
    · -- Differentiability: ∀ t ∈ (a,b), DifferentiableAt ℝ (fun t' => H(t', s)) t
      exact fun t ht => hH_diff_t t ht s hs
    · -- Derivative continuity: deriv (fun t' => H(t', s)) is continuous on [a,b]
      exact hH_deriv_cont.comp (continuous_id.prodMk continuous_const) |>.continuousOn
    · -- Avoids z₀
      exact fun t ht => hH_avoid t ht s hs
  -- Step 2: n is continuous on [0,1] (uses windingNumber_continuous_in_param)
  have hn_cont : ContinuousOn n (Icc 0 1) :=
    windingNumber_continuous_in_param H a b z₀ hab hH_cont hH_avoid
  -- Step 3: Apply continuous_integer_valued_constant
  have heq : n 0 = n 1 := continuous_integer_valued_constant n hn_cont hn_int
  -- Step 4: Relate n(0) and n(1) to the original winding numbers using generalizedWindingNumber'_eq_of_eq_on
  have hn0_eq : n 0 = generalizedWindingNumber' γ₀ a b z₀ := by
    apply generalizedWindingNumber'_eq_of_eq_on (fun t => H (t, 0)) γ₀ a b z₀ hab hH0
    -- Derivatives agree a.e.: H(·,0) = γ₀ on [a,b], hence on (a,b), so derivatives agree on (a,b)
    -- Use Set.EqOn.deriv: if f = g on open set s, then deriv f = deriv g on s
    -- The set (a,b) = Ioo a b has full measure in Ioc a b (diff is singleton {b})
    rw [Set.uIoc_of_le (le_of_lt hab)]
    have h_eq_on_Ioo : Set.EqOn (fun t => H (t, 0)) γ₀ (Ioo a b) :=
      fun t' ht' => hH0 t' (Ioo_subset_Icc_self ht')
    have h_deriv_eq_on : Set.EqOn (deriv (fun t => H (t, 0))) (deriv γ₀) (Ioo a b) :=
      h_eq_on_Ioo.deriv isOpen_Ioo
    -- Convert: property on Ioo implies ae on Ioc using Ioo_ae_eq_Ioc
    -- Use ae_restrict_iff' to convert ∀ᵐ t ∂volume.restrict (Ioc a b), P t
    -- to ∀ᵐ t, t ∈ Ioc a b → P t
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Ioo_ae_eq_Ioc.mem_iff] with t ht ht_Ioc
    exact h_deriv_eq_on (ht.mpr ht_Ioc)
  have hn1_eq : n 1 = generalizedWindingNumber' γ₁ a b z₀ := by
    apply generalizedWindingNumber'_eq_of_eq_on (fun t => H (t, 1)) γ₁ a b z₀ hab hH1
    rw [Set.uIoc_of_le (le_of_lt hab)]
    have h_eq_on_Ioo : Set.EqOn (fun t => H (t, 1)) γ₁ (Ioo a b) :=
      fun t' ht' => hH1 t' (Ioo_subset_Icc_self ht')
    have h_deriv_eq_on : Set.EqOn (deriv (fun t => H (t, 1))) (deriv γ₁) (Ioo a b) :=
      h_eq_on_Ioo.deriv isOpen_Ioo
    -- Convert: property on Ioo implies ae on Ioc using Ioo_ae_eq_Ioc
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Ioo_ae_eq_Ioc.mem_iff] with t ht ht_Ioc
    exact h_deriv_eq_on (ht.mpr ht_Ioc)
  rw [← hn0_eq, ← hn1_eq, heq]

/-- For curves that avoid z₀, the generalized winding number equals the
    classical winding number defined via contour integral.

    This connects our PV-based definition to mathlib's integral-based approach.
-/
theorem generalizedWindingNumber_eq_classical_away
    (γ : PiecewiseC1Curve) (z₀ : ℂ)
    (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) :
    generalizedWindingNumber' γ.toFun γ.a γ.b z₀ =
    (2 * Real.pi * I)⁻¹ * ∫ t in γ.a..γ.b, (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t := by
  -- When curve avoids z₀, the PV integral equals the classical integral
  -- (no singularities to cut out)
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  -- The key is that γ(Icc a b) is compact and avoids z₀, so there's a minimum distance δ > 0
  -- For ε < δ, the integrand equals the classical integrand everywhere
  -- Therefore the limit is the classical integral
  --
  -- Step 1: Find the minimum distance from the curve to z₀
  have hcompact : IsCompact (γ.toFun '' Icc γ.a γ.b) :=
    isCompact_Icc.image_of_continuousOn γ.continuous_toFun
  have hne : ∀ w ∈ γ.toFun '' Icc γ.a γ.b, w ≠ z₀ := fun w ⟨t, ht, htw⟩ => htw ▸ hoff t ht
  have hnonempty : (γ.toFun '' Icc γ.a γ.b).Nonempty :=
    Set.image_nonempty.mpr (Set.nonempty_Icc.mpr (le_of_lt γ.hab))
  -- The minimum distance exists and is positive
  have hδ : ∃ δ > 0, ∀ t ∈ Icc γ.a γ.b, δ ≤ ‖γ.toFun t - z₀‖ := by
    have hclosed : IsClosed (γ.toFun '' Icc γ.a γ.b) := hcompact.isClosed
    have hz₀_notin : z₀ ∉ (γ.toFun '' Icc γ.a γ.b) := fun hz₀ => hne z₀ hz₀ rfl
    have hdist_pos : 0 < Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b) :=
      (hclosed.notMem_iff_infDist_pos hnonempty).mp hz₀_notin
    refine ⟨Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b), hdist_pos, fun t ht => ?_⟩
    have hmem : γ.toFun t ∈ γ.toFun '' Icc γ.a γ.b := mem_image_of_mem γ.toFun ht
    calc Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b)
        ≤ dist z₀ (γ.toFun t) := Metric.infDist_le_dist_of_mem hmem
      _ = ‖γ.toFun t - z₀‖ := by rw [Complex.dist_eq, norm_sub_rev]
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hδ
  -- Step 2: For ε < δ, the condition ‖γ t - z₀‖ > ε is always satisfied
  have h_cutoff_trivial : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t ∈ Icc γ.a γ.b, ε < ‖γ.toFun t - z₀‖ := by
    filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε t ht
    calc ε < δ := (mem_Ioo.mp hε).2
      _ ≤ ‖γ.toFun t - z₀‖ := hδ_bound t ht
  -- Step 3: Show the limit is the classical integral
  congr 1
  apply limUnder_eventually_eq_const
  filter_upwards [h_cutoff_trivial] with ε hε
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t
  intro ht
  simp only [sub_zero]
  have ht' : t ∈ Icc γ.a γ.b := by
    rw [Set.uIoc_of_le (le_of_lt γ.hab)] at ht
    exact Ioc_subset_Icc_self ht
  have h_cond : ε < ‖γ.toFun t - z₀‖ := hε t ht'
  simp only [h_cond, ↓reduceIte, deriv_sub_const]

/-! ## Homotopy Invariance for Holomorphic Integrands -/

/- Aristotle failed to find a proof. -/
/-- **Main Bridge Theorem**: Contour integrals of holomorphic functions are
    homotopy invariant.

    If γ₀ and γ₁ are homotopic in a domain U where f is holomorphic,
    then ∮_{γ₀} f = ∮_{γ₁} f.

    **Proof strategy** (from Isabelle's `Cauchy_theorem_homotopic_paths`):
    The homotopy H : [a,b] × [0,1] → U traces out a 2D region.
    By Cauchy's theorem applied to this region, the boundary integral is 0.
    The boundary consists of γ₀, γ₁ (with opposite orientations), and the
    "side" edges at t = a and t = b which cancel (for closed curves) or
    contribute nothing (for paths with same endpoints).
-/
theorem contourIntegral_eq_of_homotopic
    (f : ℂ → ℂ) (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (hγ₀_cont : ContinuousOn γ₀ (Icc a b))
    (hγ₁_cont : ContinuousOn γ₁ (Icc a b))
    (hγ₀_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ₀ t)
    (hγ₁_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ₁ t)
    (H : ℝ × ℝ → ℂ) (hH_cont : Continuous H)
    (hH0 : ∀ t ∈ Icc a b, H (t, 0) = γ₀ t)
    (hH1 : ∀ t ∈ Icc a b, H (t, 1) = γ₁ t)
    (hH_ends : ∀ s ∈ Icc (0:ℝ) 1, H (a, s) = γ₀ a ∧ H (b, s) = γ₀ b)
    (hf_holo : DifferentiableOn ℂ f (H '' (Icc a b ×ˢ Icc 0 1))) :
    ∫ t in a..b, f (γ₀ t) * deriv γ₀ t = ∫ t in a..b, f (γ₁ t) * deriv γ₁ t := by
  -- **Proof sketch** (from Isabelle's `Cauchy_theorem_homotopic_paths`):
  --
  -- The homotopy H maps the rectangle [a,b] × [0,1] into ℂ.
  -- The boundary ∂([a,b] × [0,1]) consists of 4 edges:
  --   • Bottom: t ∈ [a,b], s = 0  →  H(t, 0) = γ₀(t)
  --   • Top: t ∈ [a,b], s = 1    →  H(t, 1) = γ₁(t)
  --   • Left: t = a, s ∈ [0,1]   →  H(a, s) = γ₀(a) (constant)
  --   • Right: t = b, s ∈ [0,1]  →  H(b, s) = γ₀(b) (constant)
  --
  -- By Stokes' theorem (or Green's theorem in 2D):
  --   ∮_{∂(H(rect))} f dz = ∬_{H(rect)} df ∧ dz̄ = 0  (since f is holomorphic)
  --
  -- The boundary integral decomposes as:
  --   ∮_bottom f + ∮_right f + ∮_top (reversed) + ∮_left f = 0
  --   = ∮_γ₀ f + 0 - ∮_γ₁ f + 0 = 0
  --
  -- The side edges contribute 0 because H is constant along them (endpoints fixed).
  -- Therefore: ∮_γ₀ f = ∮_γ₁ f
  --
  -- **Mathematical content**: Homotopy invariance of contour integrals for holomorphic f.
  --
  -- **Proof approach using Stokes/Green**:
  -- 1. The homotopy H : [a,b] × [0,1] → ℂ parameterizes a 2D region R = H(rect).
  -- 2. By Cauchy's theorem (f holomorphic ⟹ df ∧ dz = 0):
  --    ∮_{∂R} f dz = ∬_R d(f dz) = ∬_R df ∧ dz = 0
  -- 3. The boundary ∂R consists of:
  --    • Bottom edge: t ↦ H(t, 0) = γ₀(t) contributing ∮_γ₀ f
  --    • Top edge: t ↦ H(t, 1) = γ₁(t) contributing -∮_γ₁ f (opposite orientation)
  --    • Side edges: H(a, ·) and H(b, ·) are constant paths, contributing 0
  -- 4. Therefore: ∮_γ₀ f - ∮_γ₁ f = 0, i.e., ∮_γ₀ f = ∮_γ₁ f
  --
  -- **Mathlib reference**: `Complex.integral_boundary_rect_eq_zero_of_differentiable_on`
  -- handles axis-aligned rectangles. For parameterized surfaces, we need:
  -- • Change of variables for the integral (Jacobian of H)
  -- • Stokes' theorem for the parameterized surface
  --
  -- **Isabelle parallel**: `Cauchy_theorem_homotopic_paths` in `Cauchy_Integral_Theorem.thy`
  --
  -- **Admitted**: Requires parameterized Stokes theorem or detailed Green's theorem calculation.
  sorry

/-! ## Applying to Winding Numbers -/

/-- Winding number is homotopy invariant for curves avoiding z₀.
    This follows from `contourIntegral_eq_of_homotopic` applied to f(z) = 1/(z - z₀).
-/
theorem windingNumber_homotopy_invariant_classical
    (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hγ₀_cont : ContinuousOn γ₀ (Icc a b))
    (hγ₁_cont : ContinuousOn γ₁ (Icc a b))
    (hγ₀_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ₀ t)
    (hγ₁_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ₁ t)
    (H : ℝ × ℝ → ℂ) (hH_cont : Continuous H)
    (hH0 : ∀ t ∈ Icc a b, H (t, 0) = γ₀ t)
    (hH1 : ∀ t ∈ Icc a b, H (t, 1) = γ₁ t)
    (hH_ends : ∀ s ∈ Icc (0:ℝ) 1, H (a, s) = γ₀ a ∧ H (b, s) = γ₀ b)
    (hH_avoid : ∀ p ∈ H '' (Icc a b ×ˢ Icc 0 1), p ≠ z₀) :
    ∫ t in a..b, (γ₀ t - z₀)⁻¹ * deriv γ₀ t =
    ∫ t in a..b, (γ₁ t - z₀)⁻¹ * deriv γ₁ t := by
  apply contourIntegral_eq_of_homotopic (fun z => (z - z₀)⁻¹) γ₀ γ₁ a b hab
    hγ₀_cont hγ₁_cont hγ₀_diff hγ₁_diff H hH_cont hH0 hH1 hH_ends
  -- f(z) = (z - z₀)⁻¹ is holomorphic on ℂ \ {z₀}
  apply DifferentiableOn.inv
  · exact differentiableOn_id.sub (differentiableOn_const z₀)
  · intro z hz
    exact sub_ne_zero.mpr (hH_avoid z hz)

/-! ## Summary of Proof Strategy for Principal Value Homotopy

For homotopy invariance of principal value integrals (when curves pass through
singularities), we need a more careful argument than the classical case:

1. **Decomposition**: Split the curve at singularity crossing points
2. **Classical homotopy**: Apply `contourIntegral_eq_of_homotopic` to pieces
   avoiding the singularity
3. **Angle contribution**: The model sector contribution depends only on
   the angle at the crossing, which is preserved by homotopy

The key insight is that for immersions (nonzero derivative), crossing a
singularity at a definite angle gives a well-defined contribution that
is preserved under homotopy.
-/

end