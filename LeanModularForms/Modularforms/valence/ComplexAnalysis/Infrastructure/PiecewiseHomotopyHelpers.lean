/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import LeanModularForms.Modularforms.valence.ComplexAnalysis.HomotopyBridge
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Infrastructure for Piecewise C¹ Homotopies

This file provides infrastructure lemmas for working with piecewise C¹ curves and homotopies,
specifically for proving homotopy invariance of winding numbers.

## Main Results

* `intervalIntegrable_of_piecewise_continuousOn_bounded` - Integrability for bounded piecewise continuous functions
* `continuousWithinAt_integral_of_dominated_piecewise` - Dominated convergence for parametric integrals
* `piecewise_homotopy_deriv_bounded` - Derivative bounds for piecewise smooth homotopies
* `homotopy_slice_deriv_intervalIntegrable` - Integrability for homotopy slices

## Technical Notes

The main challenges for piecewise C¹ homotopies are:
1. The derivative exists only off a finite partition set P
2. The derivative is continuous on each piece but may have jumps at partition points
3. We need to show integrability and measurability despite the discontinuities

Key insight: Functions that are continuous off a finite set are:
- AEStronglyMeasurable (finite sets have measure zero)
- Integrable on bounded intervals if bounded (using IntegrableOn.of_bound)
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

/-! ## AEStronglyMeasurable for Piecewise Continuous Functions -/

/-- A function continuous off a finite set is AEStronglyMeasurable.

    This is because finite sets have measure zero, so the function is continuous a.e.
-/
theorem aestronglyMeasurable_of_continuousOn_off_finite
    {f : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ}
    (hf_cont : ContinuousOn f ((Icc a b) \ P)) :
    AEStronglyMeasurable f (volume.restrict (Icc a b)) := by
  -- Strategy: Write Icc a b = (Icc a b \ P) ∪ (P ∩ Icc a b)
  -- Use aestronglyMeasurable_union_iff to handle each piece separately
  have h_union : Icc a b = (Icc a b \ (P : Set ℝ)) ∪ ((P : Set ℝ) ∩ Icc a b) := by
    ext x; simp [and_comm]; tauto
  have h_meas_diff : MeasurableSet ((Icc a b) \ (P : Set ℝ)) :=
    measurableSet_Icc.diff (Finset.measurableSet P)
  have h_null : volume ((P : Set ℝ) ∩ Icc a b) = 0 := by
    apply Set.Finite.measure_zero
    exact Finset.finite_toSet P |>.inter_of_left (Icc a b)
  -- Rewrite using the union
  rw [h_union]
  rw [aestronglyMeasurable_union_iff]
  constructor
  -- Part 1: AEStronglyMeasurable on (Icc a b \ P) by continuity
  · exact hf_cont.aestronglyMeasurable h_meas_diff
  -- Part 2: AEStronglyMeasurable on (P ∩ Icc a b), which has measure zero
  · rw [Measure.restrict_zero_set h_null]
    exact aestronglyMeasurable_zero_measure f

/-! ## Integrability for Piecewise Continuous Functions -/

/-- A piecewise continuous bounded function is interval integrable.

    This is the key lemma for filling the integrability sorries in PiecewiseHomotopy.lean.
-/
theorem intervalIntegrable_of_piecewise_continuousOn_bounded
    {f : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ} (M : ℝ)
    (hab : a ≤ b)
    (hf_cont : ContinuousOn f ((Icc a b) \ P))
    (hf_bound : ∀ t ∈ Icc a b, ‖f t‖ ≤ M) :
    IntervalIntegrable f volume a b := by
  -- Step 1: Show f is AEStronglyMeasurable on [a,b]
  have hf_meas : AEStronglyMeasurable f (volume.restrict (Icc a b)) :=
    aestronglyMeasurable_of_continuousOn_off_finite hf_cont
  -- Step 2: Show IntegrableOn f (Icc a b) directly
  have h_finite : volume (Icc a b) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have h_bound_ae : ∀ᵐ t ∂volume.restrict (Icc a b), ‖f t‖ ≤ M := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    exact hf_bound t ht
  have hf_int : IntegrableOn f (Icc a b) volume := by
    refine ⟨hf_meas, ?_⟩
    exact MeasureTheory.HasFiniteIntegral.restrict_of_bounded M h_finite h_bound_ae
  -- Step 3: Convert IntegrableOn to IntervalIntegrable
  have h_uIcc : [[a, b]] = Icc a b := uIcc_of_le hab
  rw [← h_uIcc] at hf_int
  exact hf_int.intervalIntegrable

/-! ## Dominated Convergence for Parametric Integrals -/

/-- Continuity of integral in parameter for piecewise continuous integrand.

    This is the key lemma for `windingNumber_continuous_in_param_piecewise`.
-/
theorem continuousWithinAt_integral_of_dominated_piecewise
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {F : X → ℝ → ℂ} {x₀ : X} {a b : ℝ} {S : Set X} {M : ℝ}
    (hab : a ≤ b)
    (hF_meas : ∀ x ∈ S, AEStronglyMeasurable (F x) (volume.restrict (Icc a b)))
    (hF_bound : ∀ x ∈ S, ∀ t ∈ Icc a b, ‖F x t‖ ≤ M)
    (hF_cont : ∀ᵐ t ∂volume.restrict (Icc a b), ContinuousWithinAt (fun x => F x t) S x₀) :
    ContinuousWithinAt (fun x => ∫ t in a..b, F x t) S x₀ := by
  -- Use constant bound function
  let bound : ℝ → ℝ := fun _ => M
  -- The uIoc a b ⊆ Icc a b when a ≤ b
  have h_uIoc_sub : Set.uIoc a b ⊆ Icc a b := by
    rw [uIoc_of_le hab]
    exact Ioc_subset_Icc_self
  -- Apply dominated convergence
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := bound)
  · -- AEStronglyMeasurable condition
    apply Filter.eventually_of_mem (self_mem_nhdsWithin (s := S))
    intro x hx
    exact (hF_meas x hx).mono_set h_uIoc_sub
  · -- Bound condition
    apply Filter.eventually_of_mem (self_mem_nhdsWithin (s := S))
    intro x hx
    apply Filter.Eventually.of_forall
    intro t ht
    exact hF_bound x hx t (h_uIoc_sub ht)
  · -- Bound is integrable
    exact intervalIntegrable_const
  · -- Continuity in x for a.e. t
    -- We need: ∀ᵐ t ∂volume, t ∈ uIoc a b → ContinuousWithinAt (fun x => F x t) S x₀
    -- We have: ∀ᵐ t ∂volume.restrict (Icc a b), ContinuousWithinAt (fun x => F x t) S x₀
    -- First restrict to uIoc, then use ae_imp_of_ae_restrict
    have h_ae_uIoc : ∀ᵐ t ∂volume.restrict (uIoc a b), ContinuousWithinAt (fun x => F x t) S x₀ :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset h_uIoc_sub hF_cont
    exact MeasureTheory.ae_imp_of_ae_restrict h_ae_uIoc


/-! ## Derivative Bounds -/

/-- Uniform bound for winding number integrand from homotopy avoidance. -/
theorem winding_integrand_bounded_of_uniform_avoidance
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {δ M : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, δ ≤ ‖H (t, s) - z₀‖)
    (hM_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, ‖deriv (fun t' => H (t', s)) t‖ ≤ M) :
    ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1,
      ‖(H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t‖ ≤ M / δ := by
  intro t ht s hs
  have h_ne : H (t, s) - z₀ ≠ 0 := by
    intro heq
    have h := hδ_bound t ht s hs
    simp only [heq, norm_zero] at h
    linarith
  have h_inv_bound : ‖(H (t, s) - z₀)⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv, inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hδ_pos (hδ_bound t ht s hs)
  calc ‖(H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t‖
      ≤ ‖(H (t, s) - z₀)⁻¹‖ * ‖deriv (fun t' => H (t', s)) t‖ := norm_mul_le _ _
    _ ≤ δ⁻¹ * M := mul_le_mul h_inv_bound (hM_bound t ht s hs)
        (norm_nonneg _) (le_of_lt (inv_pos.mpr hδ_pos))
    _ = M / δ := by ring


/-! ## Continuity of Derivative Slices -/

/-- For t ∈ (Icc a b) \ P, the derivative of the s-slice is continuous at t.

    This follows from hH_deriv_cont by finding an open neighborhood of t
    that doesn't intersect P.

    Note: We assume P contains the endpoints a and b, which is the case for
    piecewise smooth homotopies. This ensures the boundary case is handled.
-/
lemma deriv_slice_continuousWithinAt_off_partition
    {H : ℝ × ℝ → ℂ} {a b s t : ℝ} {P : Finset ℝ}
    (hs : s ∈ Icc 0 1) (_ht_Icc : t ∈ Icc a b) (ht_notP : t ∉ P) (_hab : a < b)
    (hP_endpoints : a ∈ P ∧ b ∈ P)
    (hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t' ∈ Ioo p₁ p₂, t' ∉ P) →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t'' => H (t'', p.2)) p.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1)) :
    ContinuousWithinAt (deriv (fun t' => H (t', s))) ((Icc a b) \ P) t := by
  -- Helper: get joint continuity and extract slice at any point x
  have h_get_slice : ∀ p₁ p₂ x, p₁ < p₂ → x ∈ Ioo p₁ p₂ →
      (∀ t' ∈ Ioo p₁ p₂, t' ∉ P) →
      ContinuousAt (deriv (fun t' => H (t', s))) x := by
    intro p₁ p₂ x hp₁p₂ hx_in h_avoid
    have h_joint_cont := hH_deriv_cont p₁ p₂ hp₁p₂ h_avoid
    have h_embed : ContinuousOn (fun t' => (t', s)) (Ioo p₁ p₂) :=
      (continuous_id.prodMk continuous_const).continuousOn
    have h_maps : MapsTo (fun t' => (t', s)) (Ioo p₁ p₂) (Ioo p₁ p₂ ×ˢ Icc 0 1) :=
      fun t' ht' => ⟨ht', hs⟩
    have h_comp := h_joint_cont.comp h_embed h_maps
    exact (h_comp x hx_in).continuousAt (Ioo_mem_nhds hx_in.1 hx_in.2)
  -- Since P is finite and t ∉ P, find ε > 0 such that (t - ε, t + ε) ∩ P = ∅
  have h_finite : (P : Set ℝ).Finite := Finset.finite_toSet P
  have h_dist : 0 < Metric.infDist t P ∨ P = ∅ := by
    by_cases hP_empty : (P : Set ℝ) = ∅
    · right; exact Finset.coe_eq_empty.mp hP_empty
    · left
      have : (P : Set ℝ).Nonempty := Set.nonempty_iff_ne_empty.mpr hP_empty
      exact (h_finite.isClosed.notMem_iff_infDist_pos this).mp ht_notP
  rcases h_dist with hε_pos | hP_empty
  · -- P is nonempty, use positive distance
    set ε := Metric.infDist t P with hε_def
    have hε'_pos : 0 < ε / 2 := div_pos hε_pos (by norm_num)
    have h_avoid : ∀ t' ∈ Ioo (t - ε / 2) (t + ε / 2), t' ∉ P := by
      intro t' ht' hp'
      have h_dist_bound : ε ≤ dist t t' := by
        calc ε = Metric.infDist t P := hε_def
          _ ≤ dist t t' := Metric.infDist_le_dist_of_mem hp'
      have h_dist_small : dist t t' < ε := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [ht'.1, ht'.2]
      linarith
    have hp₁p₂ : t - ε / 2 < t + ε / 2 := by linarith
    have ht_in : t ∈ Ioo (t - ε / 2) (t + ε / 2) := ⟨by linarith, by linarith⟩
    exact (h_get_slice _ _ t hp₁p₂ ht_in h_avoid).continuousWithinAt
  · -- P is empty: contradicts hP_endpoints (a ∈ P and b ∈ P)
    exfalso
    rw [hP_empty] at hP_endpoints
    exact Finset.notMem_empty a hP_endpoints.1

/-- The derivative of a homotopy slice is continuous on (Icc a b) \ P.

    This aggregates `deriv_slice_continuousWithinAt_off_partition` over all points.
-/
lemma deriv_slice_continuousOn_off_partition
    {H : ℝ × ℝ → ℂ} {a b s : ℝ} {P : Finset ℝ}
    (hs : s ∈ Icc 0 1) (hab : a < b)
    (hP_endpoints : a ∈ P ∧ b ∈ P)
    (hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P) →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1)) :
    ContinuousOn (deriv (fun t => H (t, s))) ((Icc a b) \ P) := by
  intro t ⟨ht_Icc, ht_notP⟩
  exact deriv_slice_continuousWithinAt_off_partition hs ht_Icc ht_notP hab hP_endpoints hH_deriv_cont

/-! ## Derivative Bound for Piecewise Smooth Homotopies -/

/-- Helper lemma: Given an explicit bound on the derivative, we can use it directly.

    Note: The bound M must be provided as a hypothesis. While in principle one could
    derive a bound from continuity on compact closures of the partition pieces, this
    requires additional regularity hypotheses (extension to closure). In practice,
    the bound is readily available from the construction of the homotopy.
-/
theorem piecewise_homotopy_deriv_bounded
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {P : Finset ℝ} {M : ℝ} (_hab : a < b)
    (hM_pos : 0 < M)
    (_hH_cont : Continuous H)
    (_hH_diff : ∀ t ∈ Ioo a b, t ∉ P → ∀ s ∈ Icc (0:ℝ) 1,
      DifferentiableAt ℝ (fun t' => H (t', s)) t)
    (hH_deriv_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1,
      ‖deriv (fun t' => H (t', s)) t‖ ≤ M)
    (_hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P) →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1)) :
    ∃ M' : ℝ, 0 < M' ∧ ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1,
      ‖deriv (fun t' => H (t', s)) t‖ ≤ M' := by
  exact ⟨M, hM_pos, hH_deriv_bound⟩

/-! ## Integrability for Homotopy Slices -/

/-- For a piecewise smooth homotopy, each slice H(·, s) has integrable derivative.

    This combines:
    1. Boundedness of derivative (provided as hypothesis)
    2. Measurability (from aestronglyMeasurable_of_continuousOn_off_finite)
    3. Integrability (from intervalIntegrable_of_piecewise_continuousOn_bounded)
-/
theorem homotopy_slice_deriv_intervalIntegrable
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {P : Finset ℝ} {s : ℝ} {M : ℝ} (hab : a < b)
    (hs : s ∈ Icc (0:ℝ) 1)
    (_hH_cont : Continuous H)
    (hP_endpoints : a ∈ P ∧ b ∈ P)
    (_hH_diff : ∀ t ∈ Ioo a b, t ∉ P → ∀ s' ∈ Icc (0:ℝ) 1,
      DifferentiableAt ℝ (fun t' => H (t', s')) t)
    (hH_deriv_bound : ∀ t ∈ Icc a b, ∀ s' ∈ Icc (0:ℝ) 1,
      ‖deriv (fun t' => H (t', s')) t‖ ≤ M)
    (hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P) →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1)) :
    IntervalIntegrable (deriv (fun t => H (t, s))) volume a b := by
  -- The derivative is piecewise continuous
  have hγ'_cont : ContinuousOn (deriv (fun t => H (t, s))) ((Icc a b) \ P) :=
    deriv_slice_continuousOn_off_partition hs hab hP_endpoints hH_deriv_cont
  -- Apply the integrability lemma
  exact intervalIntegrable_of_piecewise_continuousOn_bounded M (le_of_lt hab) hγ'_cont
    (fun t ht => hH_deriv_bound t ht s hs)

/-! ## Continuity of Winding Number in Homotopy Parameter -/

/-- Winding number is continuous in the homotopy parameter for piecewise C¹ homotopies.

    This version requires an explicit derivative bound M, which is the practical approach
    for dominated convergence arguments.
-/
theorem windingNumber_continuousOn_param_piecewise_with_bound
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ} {M : ℝ} (hab : a < b)
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀)
    (_hH_diff : ∀ t ∈ Ioo a b, t ∉ P → ∀ s ∈ Icc (0:ℝ) 1,
      DifferentiableAt ℝ (fun t' => H (t', s)) t)
    (hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1))
    (hM_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1,
      ‖deriv (fun t' => H (t', s)) t‖ ≤ M) :
    ContinuousOn (fun s => generalizedWindingNumber' (fun t => H (t, s)) a b z₀) (Icc 0 1) := by
  -- Step 1: Get uniform avoidance bound δ > 0
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := homotopy_uniform_avoidance H a b z₀ hab hH_cont hH_avoid
  -- Step 2: Define the integrand
  let f : ℝ → ℝ → ℂ := fun t s => (H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t
  -- Step 3: Bound on the integrand
  have hf_bound : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc a b, ‖f t s‖ ≤ M / δ := by
    intro s hs t ht
    exact winding_integrand_bounded_of_uniform_avoidance hδ_pos hδ_bound hM_bound t ht s hs
  -- Step 4: For s ∈ [0,1], PV integral equals classical integral
  have h_pv_eq_integral : ∀ s ∈ Icc (0:ℝ) 1,
      generalizedWindingNumber' (fun t => H (t, s)) a b z₀ =
      (2 * Real.pi * I)⁻¹ * ∫ t in a..b, f t s := by
    intro s hs
    unfold generalizedWindingNumber' cauchyPrincipalValue'
    simp only [sub_zero]
    congr 1
    have h_cutoff : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t ∈ Icc a b, ε < ‖H (t, s) - z₀‖ := by
      filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε t ht
      calc ε < δ := (mem_Ioo.mp hε).2
        _ ≤ ‖H (t, s) - z₀‖ := hδ_bound t ht s hs
    apply limUnder_eventually_eq_const
    filter_upwards [h_cutoff] with ε hε
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht' : t ∈ Icc a b := by
      rw [Set.uIoc_of_le (le_of_lt hab)] at ht
      exact Ioc_subset_Icc_self ht
    simp only [f, hε t ht', ↓reduceIte, deriv_sub_const]
  -- Step 5: Show the integral is continuous in s using dominated convergence
  intro s₀ hs₀
  have heq_near : ∀ᶠ s in 𝓝[Icc 0 1] s₀, generalizedWindingNumber' (fun t => H (t, s)) a b z₀ =
      (2 * Real.pi * I)⁻¹ * ∫ t in a..b, f t s := by
    apply eventually_of_mem self_mem_nhdsWithin
    exact h_pv_eq_integral
  apply ContinuousWithinAt.congr_of_eventuallyEq _ heq_near (h_pv_eq_integral s₀ hs₀)
  apply continuousWithinAt_const.mul
  -- Apply dominated convergence
  apply continuousWithinAt_integral_of_dominated_piecewise (M := M / δ) (le_of_lt hab)
  · -- AEStronglyMeasurable for each s
    -- The integrand f(·, s) is bounded and continuous off a finite set, hence AEStronglyMeasurable
    intro s hs
    -- f(·, s) is continuous on (Icc a b) \ (P ∪ {a, b})
    -- This is a full measure set (finite complement)
    -- Strategy: Use aestronglyMeasurable_of_continuousOn_off_finite with extended partition
    let P' : Finset ℝ := P ∪ {a, b}
    have hf_cont_off_P' : ContinuousOn (fun t => f t s) ((Icc a b) \ P') := by
      intro t ⟨ht_Icc, ht_notP'⟩
      simp only [P', Finset.coe_union, Finset.coe_pair, Set.mem_union, Set.mem_insert_iff,
        not_or] at ht_notP'
      have ht_notP : t ∉ P := ht_notP'.1
      have ht_ne_a : t ≠ a := ht_notP'.2.1
      have ht_ne_b : t ≠ b := ht_notP'.2.2
      -- So t ∈ Ioo a b
      have ht_Ioo : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht_Icc.1 (Ne.symm ht_ne_a),
        lt_of_le_of_ne ht_Icc.2 ht_ne_b⟩
      -- Find an interval (p₁, p₂) containing t with no partition points
      have h_finite : (P : Set ℝ).Finite := Finset.finite_toSet P
      have h_dist_pos : 0 < Metric.infDist t P ∨ (P : Set ℝ) = ∅ := by
        by_cases hP_empty : (P : Set ℝ) = ∅
        · right; exact hP_empty
        · left
          have hP_nonempty : (P : Set ℝ).Nonempty := Set.nonempty_iff_ne_empty.mpr hP_empty
          exact (h_finite.isClosed.notMem_iff_infDist_pos hP_nonempty).mp ht_notP
      rcases h_dist_pos with hε_pos | hP_empty
      · -- P is nonempty, use distance from t to P
        set ε := min (Metric.infDist t P / 2) (min (t - a) (b - t)) with hε_def
        have hε_pos' : 0 < ε := by
          simp only [hε_def, lt_min_iff]
          exact ⟨div_pos hε_pos (by norm_num), sub_pos.mpr ht_Ioo.1, sub_pos.mpr ht_Ioo.2⟩
        have h_avoid_P : ∀ t' ∈ Ioo (t - ε) (t + ε), t' ∉ P := by
          intro t' ht' hp'
          have h_dist : Metric.infDist t P ≤ dist t t' := Metric.infDist_le_dist_of_mem hp'
          have h_small : dist t t' < Metric.infDist t P / 2 := by
            rw [Real.dist_eq, abs_lt]
            have hmin := min_le_left (Metric.infDist t P / 2) (min (t - a) (b - t))
            constructor <;> linarith [ht'.1, ht'.2, hmin]
          linarith
        have hp₁p₂ : t - ε < t + ε := by linarith
        have ht_in : t ∈ Ioo (t - ε) (t + ε) := ⟨by linarith, by linarith⟩
        -- Prove Ioo (t - ε) (t + ε) ⊆ Ioo a b
        have h_sub_ab : Ioo (t - ε) (t + ε) ⊆ Ioo a b := by
          intro x ⟨hxl, hxr⟩
          -- ε = min (infDist t P / 2) (min (t - a) (b - t))
          -- So ε ≤ min (t - a) (b - t), and thus ε ≤ (t - a) and ε ≤ (b - t)
          have hε_le_min := min_le_right (Metric.infDist t P / 2) (min (t - a) (b - t))
          have h_ta := hε_le_min.trans (min_le_left (t - a) (b - t))
          have h_bt := hε_le_min.trans (min_le_right (t - a) (b - t))
          constructor <;> linarith
        -- Now use hH_deriv_cont to get continuity of the derivative
        have h_deriv_joint := hH_deriv_cont (t - ε) (t + ε) hp₁p₂ h_avoid_P h_sub_ab
        -- The integrand f t s = (H(t,s) - z₀)⁻¹ * deriv(...) is continuous
        -- because both factors are continuous
        apply ContinuousWithinAt.mono _ (Set.diff_subset_diff_right (Finset.coe_subset.mpr
          (Finset.subset_union_left (s₂ := {a, b}))))
        apply ContinuousWithinAt.mul
        · -- (H(·, s) - z₀)⁻¹ is continuous
          apply ContinuousAt.continuousWithinAt
          apply ContinuousAt.inv₀
          · exact (hH_cont.comp (continuous_id.prodMk continuous_const)).continuousAt.sub
              continuousAt_const
          · exact sub_ne_zero.mpr (hH_avoid t ht_Icc s hs)
        · -- deriv (fun t' => H(t', s)) is continuous at t
          -- We need to extract from the joint continuity
          have h_embed : ContinuousOn (fun t' => (t', s)) (Ioo (t - ε) (t + ε)) :=
            (continuous_id.prodMk continuous_const).continuousOn
          have h_maps : MapsTo (fun t' => (t', s)) (Ioo (t - ε) (t + ε))
              (Ioo (t - ε) (t + ε) ×ˢ Icc 0 1) := fun t' ht' => ⟨ht', hs⟩
          have h_comp := h_deriv_joint.comp h_embed h_maps
          have h_at : ContinuousAt (deriv (fun t' => H (t', s))) t :=
            (h_comp t ht_in).continuousAt (Ioo_mem_nhds ht_in.1 ht_in.2)
          exact h_at.continuousWithinAt
      · -- P is empty
        apply ContinuousWithinAt.mono _ Set.diff_subset
        apply ContinuousWithinAt.mul
        · apply ContinuousAt.continuousWithinAt
          apply ContinuousAt.inv₀
          · exact (hH_cont.comp (continuous_id.prodMk continuous_const)).continuousAt.sub
              continuousAt_const
          · exact sub_ne_zero.mpr (hH_avoid t ht_Icc s hs)
        · -- For empty P, use any interval
          have h_avoid_empty : ∀ t' ∈ Ioo a b, t' ∉ P := fun t' _ hp' =>
            Set.eq_empty_iff_forall_notMem.mp hP_empty t' hp'
          have h_sub_refl : Ioo a b ⊆ Ioo a b := Subset.rfl
          have h_deriv_joint := hH_deriv_cont a b hab h_avoid_empty h_sub_refl
          have h_embed : ContinuousOn (fun t' => (t', s)) (Ioo a b) :=
            (continuous_id.prodMk continuous_const).continuousOn
          have h_maps : MapsTo (fun t' => (t', s)) (Ioo a b) (Ioo a b ×ˢ Icc 0 1) :=
            fun t' ht' => ⟨ht', hs⟩
          have h_comp := h_deriv_joint.comp h_embed h_maps
          exact (h_comp t ht_Ioo).continuousAt (Ioo_mem_nhds ht_Ioo.1 ht_Ioo.2) |>.continuousWithinAt
    -- Apply the measurability lemma with P' instead of P
    exact aestronglyMeasurable_of_continuousOn_off_finite hf_cont_off_P'
  · -- Bound
    intro s hs t ht
    exact hf_bound s hs t ht
  · -- Pointwise continuity a.e.
    -- For a.e. t ∈ [a,b], f(t, ·) is continuous on [0,1]
    -- This holds for t ∈ (Ioo a b) \ P, which has full measure (complement is finite)
    -- Define the bad set B = {a, b} ∪ P
    let B : Set ℝ := {a, b} ∪ (P : Set ℝ)
    -- B is finite
    have hB_finite : B.Finite := by
      refine Set.Finite.union ?_ (Finset.finite_toSet P)
      exact Set.finite_insert.mpr (Set.finite_singleton b)
    -- B has measure zero (finite sets have measure zero for volume on ℝ)
    have hB_null : volume B = 0 := hB_finite.measure_zero volume
    -- For t ∉ B, we have continuity
    have h_cont_off_B : ∀ t ∈ Icc a b, t ∉ B → ContinuousWithinAt (fun s => f t s) (Icc 0 1) s₀ := by
      intro t ht_Icc ht_notB
      simp only [B, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_notB
      have ht_notP : t ∉ P := ht_notB.2
      have ht_ne_a : t ≠ a := ht_notB.1.1
      have ht_ne_b : t ≠ b := ht_notB.1.2
      -- t ∈ (a, b) since t ∈ [a,b] and t ≠ a, b
      have ht_Ioo : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht_Icc.1 (Ne.symm ht_ne_a),
        lt_of_le_of_ne ht_Icc.2 ht_ne_b⟩
      -- Find an interval (p₁, p₂) containing t with no partition points
      have h_finite : (P : Set ℝ).Finite := Finset.finite_toSet P
      have h_dist_pos : 0 < Metric.infDist t P ∨ (P : Set ℝ) = ∅ := by
        by_cases hP_empty : (P : Set ℝ) = ∅
        · right; exact hP_empty
        · left
          have hP_nonempty : (P : Set ℝ).Nonempty := Set.nonempty_iff_ne_empty.mpr hP_empty
          exact (h_finite.isClosed.notMem_iff_infDist_pos hP_nonempty).mp ht_notP
      rcases h_dist_pos with hε_pos | hP_empty
      · -- P is nonempty
        set ε := min (Metric.infDist t P / 2) (min (t - a) (b - t)) with hε_def
        have hε_pos' : 0 < ε := by
          simp only [hε_def, lt_min_iff]
          exact ⟨div_pos hε_pos (by norm_num), sub_pos.mpr ht_Ioo.1, sub_pos.mpr ht_Ioo.2⟩
        have h_avoid_P : ∀ t' ∈ Ioo (t - ε) (t + ε), t' ∉ P := by
          intro t' ht' hp'
          have h_dist : Metric.infDist t P ≤ dist t t' := Metric.infDist_le_dist_of_mem hp'
          have h_small : dist t t' < Metric.infDist t P / 2 := by
            rw [Real.dist_eq, abs_lt]
            have hmin := min_le_left (Metric.infDist t P / 2) (min (t - a) (b - t))
            constructor <;> linarith [ht'.1, ht'.2, hmin]
          linarith
        have hp₁p₂ : t - ε < t + ε := by linarith
        have ht_in : t ∈ Ioo (t - ε) (t + ε) := ⟨by linarith, by linarith⟩
        -- Prove Ioo (t - ε) (t + ε) ⊆ Ioo a b
        have h_sub_ab : Ioo (t - ε) (t + ε) ⊆ Ioo a b := by
          intro x ⟨hxl, hxr⟩
          -- ε = min (infDist t P / 2) (min (t - a) (b - t))
          -- So ε ≤ min (t - a) (b - t), and thus ε ≤ (t - a) and ε ≤ (b - t)
          have hε_le_min := min_le_right (Metric.infDist t P / 2) (min (t - a) (b - t))
          have h_ta := hε_le_min.trans (min_le_left (t - a) (b - t))
          have h_bt := hε_le_min.trans (min_le_right (t - a) (b - t))
          constructor <;> linarith
        have h_deriv_joint := hH_deriv_cont (t - ε) (t + ε) hp₁p₂ h_avoid_P h_sub_ab
        apply ContinuousWithinAt.mul
        · apply ContinuousAt.continuousWithinAt
          apply ContinuousAt.inv₀
          · exact (hH_cont.comp (continuous_const.prodMk continuous_id)).continuousAt.sub
              continuousAt_const
          · exact sub_ne_zero.mpr (hH_avoid t ht_Icc s₀ hs₀)
        · -- Derivative is continuous in s at fixed t
          have h_embed : ContinuousOn (fun s : ℝ => (t, s)) (Icc 0 1) :=
            (continuous_const.prodMk continuous_id).continuousOn
          have h_maps : MapsTo (fun s : ℝ => (t, s)) (Icc 0 1) (Ioo (t - ε) (t + ε) ×ˢ Icc 0 1) :=
            fun s hs => ⟨ht_in, hs⟩
          exact (h_deriv_joint.comp h_embed h_maps) s₀ hs₀
      · -- P is empty
        have h_avoid_empty : ∀ t' ∈ Ioo a b, t' ∉ P := fun t' _ hp' =>
          Set.eq_empty_iff_forall_notMem.mp hP_empty t' hp'
        have h_sub_refl : Ioo a b ⊆ Ioo a b := Subset.rfl
        have h_deriv_joint := hH_deriv_cont a b hab h_avoid_empty h_sub_refl
        apply ContinuousWithinAt.mul
        · apply ContinuousAt.continuousWithinAt
          apply ContinuousAt.inv₀
          · exact (hH_cont.comp (continuous_const.prodMk continuous_id)).continuousAt.sub
              continuousAt_const
          · exact sub_ne_zero.mpr (hH_avoid t ht_Icc s₀ hs₀)
        · have h_embed : ContinuousOn (fun s : ℝ => (t, s)) (Icc 0 1) :=
            (continuous_const.prodMk continuous_id).continuousOn
          have h_maps : MapsTo (fun s : ℝ => (t, s)) (Icc 0 1) (Ioo a b ×ˢ Icc 0 1) :=
            fun s hs => ⟨ht_Ioo, hs⟩
          exact (h_deriv_joint.comp h_embed h_maps) s₀ hs₀
    -- Convert to a.e. statement: t ∉ B for a.e. t
    -- Since B has measure zero, t ∈ Bᶜ for a.e. t
    have h_ae_not_B : ∀ᵐ t ∂(volume.restrict (Icc a b)), t ∉ B := by
      have h_sub : (Icc a b) ∩ B ⊆ B := Set.inter_subset_right
      have h_null_inter : volume ((Icc a b) ∩ B) = 0 := measure_mono_null h_sub hB_null
      rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
      simp only [Set.setOf_and, Classical.not_imp, not_not]
      exact h_null_inter
    -- Also need t ∈ Icc a b ae
    have h_ae_mem : ∀ᵐ t ∂(volume.restrict (Icc a b)), t ∈ Icc a b :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [h_ae_not_B, h_ae_mem] with t ht_notB ht_Icc
    exact h_cont_off_B t ht_Icc ht_notB

/-- Winding number is continuous in the homotopy parameter for piecewise C¹ homotopies.

    This is the version without explicit bound. The proof uses a.e. boundedness from
    the piecewise continuity structure.

    **Mathematical justification**:
    The integrand F(t, s) = (H(t,s) - z₀)⁻¹ · ∂ₜH(t,s) satisfies:
    1. F is bounded a.e. on [a,b] × [0,1] since:
       - |H(t,s) - z₀| ≥ δ > 0 for some δ (uniform avoidance from compactness)
       - |∂ₜH| is bounded a.e. (continuous off a null set)
    2. F is continuous in s for a.e. t (continuous off partition points)
    3. By dominated convergence, ∫ₐᵇ F(t,s) dt is continuous in s

    **Technical gap**: Deriving the a.e. bound from `hH_deriv_cont` requires showing
    the derivative is bounded on the closure of each piece, which needs additional
    work on extending the continuity hypothesis.
-/
theorem windingNumber_continuousOn_param_piecewise
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ} (hab : a < b)
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀)
    (hH_diff : ∀ t ∈ Ioo a b, t ∉ P → ∀ s ∈ Icc (0:ℝ) 1,
      DifferentiableAt ℝ (fun t' => H (t', s)) t)
    (hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1))
    (hH_deriv_bound_ex : ∃ M, ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1,
      ‖deriv (fun t' => H (t', s)) t‖ ≤ M) :
    ContinuousOn (fun s => generalizedWindingNumber' (fun t => H (t, s)) a b z₀) (Icc 0 1) := by
  obtain ⟨M, hM⟩ := hH_deriv_bound_ex
  exact windingNumber_continuousOn_param_piecewise_with_bound hab hH_cont hH_avoid hH_diff
    hH_deriv_cont hM

end
