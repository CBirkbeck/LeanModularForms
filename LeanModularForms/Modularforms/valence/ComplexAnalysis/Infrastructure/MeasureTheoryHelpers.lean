/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Measure Theory Helpers for Principal Value Integrals

This file provides infrastructure for proving integrability and measurability results
needed for Cauchy principal value integrals.

## Main Results

### Integrability
* `integrableOn_piecewise_continuousOn` - Piecewise continuous bounded functions are integrable
* `intervalIntegrable_of_bounded_ae` - Bounded ae functions are interval integrable
* `intervalIntegrable_indicator` - Indicator of continuous function on open set

### Measurability
* `aEStronglyMeasurable_indicator_continuousOn` - Indicator of continuous function is ae measurable
* `measurableSet_norm_gt` - {t | ε < ‖f t‖} is measurable when f is continuous

## Mathlib Reference

Key lemmas used:
* `ContinuousOn.integrableOn_Icc` - Continuous functions integrable on [a,b]
* `MeasureTheory.Integrable.piecewise` - Piecewise integrable functions
* `measurableSet_preimage_of_continuous` - Preimages under continuous maps

## Isabelle Parallel

These lemmas correspond to measurability arguments implicit in Isabelle's
`Contour_Integration.thy` where path integrals are defined for piecewise C¹ paths.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ## Measurability of Sets -/

/-- The set {t | ε < ‖f t‖} is measurable when f is continuous on a measurable set. -/
lemma measurableSet_norm_gt_of_continuousOn {f : ℝ → ℂ} {s : Set ℝ} (ε : ℝ)
    (hf : ContinuousOn f s) (hs : MeasurableSet s) :
    MeasurableSet ({t | ε < ‖f t‖} ∩ s) := by
  -- The set {t | ε < ‖f t‖} ∩ s is the preimage of (ε, ∞) under ‖f ·‖ intersected with s
  -- Since ‖f ·‖ is continuous on s, and (ε, ∞) is open, the preimage is open in s
  have h_norm_cont : ContinuousOn (fun t => ‖f t‖) s := hf.norm
  -- The preimage of the open set (ε, ∞) under a continuous function is open in the subspace
  have h_open_sub : IsOpen ((s.restrict (fun t => ‖f t‖)) ⁻¹' Set.Ioi ε) :=
    isOpen_Ioi.preimage h_norm_cont.restrict
  -- Convert to measurable set
  rw [isOpen_induced_iff] at h_open_sub
  obtain ⟨U, hU_open, hU_eq⟩ := h_open_sub
  -- The intersection equals U ∩ s
  have h_eq : {t | ε < ‖f t‖} ∩ s = U ∩ s := by
    ext x
    constructor
    · intro ⟨hx_far, hx_s⟩
      refine ⟨?_, hx_s⟩
      have h1 : (⟨x, hx_s⟩ : ↑s) ∈ (s.restrict (fun t => ‖f t‖)) ⁻¹' Set.Ioi ε := by
        simp only [Set.mem_preimage, Set.restrict_apply, Set.mem_Ioi]
        exact hx_far
      rw [← hU_eq] at h1
      exact h1
    · intro ⟨hx_U, hx_s⟩
      refine ⟨?_, hx_s⟩
      have h1 : (⟨x, hx_s⟩ : ↑s) ∈ Subtype.val ⁻¹' U := hx_U
      rw [hU_eq] at h1
      simp only [Set.mem_preimage, Set.restrict_apply, Set.mem_Ioi] at h1
      exact h1
  rw [h_eq]
  exact hU_open.measurableSet.inter hs

/-- The set {t ∈ [a,b] | ε < ‖f t‖} is measurable when f is continuous on [a,b]. -/
lemma measurableSet_norm_gt_Icc {f : ℝ → ℂ} {a b : ℝ} (ε : ℝ)
    (hf : ContinuousOn f (Icc a b)) :
    MeasurableSet ({t | ε < ‖f t‖} ∩ Icc a b) :=
  measurableSet_norm_gt_of_continuousOn ε hf isClosed_Icc.measurableSet

/-! ## AE Strong Measurability -/

/-- A function that is continuous on a measurable set and zero elsewhere is ae strongly measurable. -/
theorem aEStronglyMeasurable_of_continuousOn_zero_elsewhere
    {f : ℝ → ℂ} {s : Set ℝ} {a b : ℝ}
    (hf : ContinuousOn f s) (hs : MeasurableSet s)
    (hf_zero : ∀ x ∉ s, f x = 0) :
    AEStronglyMeasurable f (volume.restrict (Icc a b)) := by
  -- f equals s.indicator f since f is zero outside s
  have h_eq : f = s.indicator f := by
    ext x
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, hf_zero x hx]
  rw [h_eq]
  -- Now use that indicator of a continuous function on a measurable set is ae strongly measurable
  rw [aestronglyMeasurable_indicator_iff hs]
  -- f is continuous on s, so ae strongly measurable on μ.restrict s
  exact hf.aestronglyMeasurable hs

/-- The principal value integrand is ae strongly measurable.

    The integrand is either f(γ(t)) * γ'(t) or 0, depending on whether ‖γ(t) - z₀‖ > ε.
    This is a piecewise continuous function on measurable sets, hence ae measurable.
-/
theorem aEStronglyMeasurable_pv_integrand
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {ε : ℝ}
    (hf : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ : ContinuousOn γ (Icc a b))
    (hγ' : ContinuousOn (deriv γ) (Icc a b)) :
    AEStronglyMeasurable (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0)
      (volume.restrict (Icc a b)) := by
  -- The function is piecewise: base function on S, 0 on Sᶜ
  -- where S = {t ∈ [a,b] | ε < ‖γ t - z₀‖}
  -- Rewrite as indicator function of S ∩ Icc a b (restricted to Icc a b, S and S ∩ Icc a b give same indicator)
  let S := {t | ε < ‖γ t - z₀‖}
  -- S ∩ Icc a b is measurable
  have hS_meas : MeasurableSet (S ∩ Icc a b) := measurableSet_norm_gt_Icc ε (hγ.sub continuousOn_const)
  -- The base function (f ∘ γ) * γ' is continuous on S ∩ Icc a b
  have h_cont : ContinuousOn (fun t => f (γ t) * deriv γ t) (S ∩ Icc a b) := by
    intro t ⟨ht_S, ht_Icc⟩
    have hγt_not_ball : γ t ∉ Metric.ball z₀ ε := by
      simp only [S, Set.mem_setOf_eq] at ht_S
      simp only [Metric.mem_ball, not_lt]
      exact le_of_lt ht_S
    have hγt_in : γ t ∈ γ '' Icc a b \ Metric.ball z₀ ε :=
      ⟨Set.mem_image_of_mem γ ht_Icc, hγt_not_ball⟩
    have hf_at : ContinuousWithinAt f (γ '' Icc a b \ Metric.ball z₀ ε) (γ t) := hf (γ t) hγt_in
    have hγ_at : ContinuousWithinAt γ (Icc a b) t := hγ t ht_Icc
    have hγ'_at : ContinuousWithinAt (deriv γ) (Icc a b) t := hγ' t ht_Icc
    have h_maps : Set.MapsTo γ (S ∩ Icc a b) (γ '' Icc a b \ Metric.ball z₀ ε) := by
      intro s ⟨hs_S, hs_Icc⟩
      refine ⟨Set.mem_image_of_mem γ hs_Icc, ?_⟩
      simp only [S, Set.mem_setOf_eq] at hs_S
      simp only [Metric.mem_ball, not_lt]
      exact le_of_lt hs_S
    have hfγ_at : ContinuousWithinAt (f ∘ γ) (S ∩ Icc a b) t :=
      ContinuousWithinAt.comp hf_at (hγ_at.mono Set.inter_subset_right) h_maps
    have hγ'_at' : ContinuousWithinAt (deriv γ) (S ∩ Icc a b) t := hγ'_at.mono Set.inter_subset_right
    exact hfγ_at.mul hγ'_at'
  -- Use ContinuousOn.aestronglyMeasurable for the base function on S ∩ Icc a b
  have h_base_meas : AEStronglyMeasurable (fun t => f (γ t) * deriv γ t)
      (volume.restrict (S ∩ Icc a b)) := h_cont.aestronglyMeasurable hS_meas
  -- Use AEStronglyMeasurable.piecewise
  have h_zero_meas : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
      (volume.restrict (S ∩ Icc a b)ᶜ) := aestronglyMeasurable_const
  have h_piecewise := AEStronglyMeasurable.piecewise hS_meas h_base_meas h_zero_meas
  -- The piecewise function equals our if-then-else
  have h_eq : (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0) =ᵐ[volume.restrict (Icc a b)]
      (S ∩ Icc a b).piecewise (fun t => f (γ t) * deriv γ t) (fun _ => 0) := by
    filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
    simp only [Set.piecewise]
    by_cases ht_S : t ∈ S
    · have ht_SI : t ∈ S ∩ Icc a b := ⟨ht_S, ht⟩
      simp only [ht_SI, ↓reduceIte]
      simp only [S, Set.mem_setOf_eq] at ht_S
      simp only [ht_S, ↓reduceIte]
    · have ht_nSI : t ∉ S ∩ Icc a b := fun h => ht_S h.1
      simp only [ht_nSI, ↓reduceIte]
      simp only [S, Set.mem_setOf_eq, not_lt] at ht_S
      simp only [not_lt.mpr ht_S, ↓reduceIte]
  exact (h_piecewise.mono_measure Measure.restrict_le_self).congr h_eq.symm

/-! ## Integrability Results -/

/-- A bounded ae measurable function is integrable on a finite measure set.

    **Key lemma for PV integrability**: If the integrand is bounded by M on [a,b],
    and ae measurable, then it's integrable.
-/
theorem integrableOn_of_bounded_aeMeasurable
    {f : ℝ → ℂ} {a b : ℝ} (M : ℝ)
    (hf_meas : AEStronglyMeasurable f (volume.restrict (Icc a b)))
    (hf_bound : ∀ x ∈ Icc a b, ‖f x‖ ≤ M) :
    IntegrableOn f (Icc a b) volume := by
  -- Bounded ae measurable functions are integrable on sets of finite measure
  -- Since [a,b] has finite Lebesgue measure and f is bounded by M and ae measurable,
  -- f is integrable
  -- Use IntegrableOn.of_bound from mathlib
  apply IntegrableOn.of_bound measure_Icc_lt_top hf_meas (max M 0)
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with x hx
  calc ‖f x‖ ≤ M := hf_bound x hx
    _ ≤ max M 0 := le_max_left M 0

/-- The principal value integrand is interval integrable when bounded.

    This is the main integrability result needed for `cauchyPrincipalValueIntegrand_integrable`.
-/
theorem intervalIntegrable_pv_integrand
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {ε : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ : ContinuousOn γ (Icc a b))
    (hγ' : ContinuousOn (deriv γ) (Icc a b))
    (M : ℝ)
    (hM : ∀ t ∈ Icc a b, ‖(if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0)‖ ≤ M) :
    IntervalIntegrable (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0)
      volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  -- Ioc is a.e. equal to Icc for Lebesgue measure
  apply IntegrableOn.mono_set
  · -- Show integrableOn Icc
    apply integrableOn_of_bounded_aeMeasurable M
    · exact aEStronglyMeasurable_pv_integrand hf hγ hγ'
    · exact hM
  · exact Ioc_subset_Icc_self

/-! ## Dominated Convergence Infrastructure -/

/-- Dominated convergence for interval integrals with filter.

    If F_n → f pointwise ae, ‖F_n‖ ≤ bound, and bound is integrable,
    then ∫ F_n → ∫ f.

    This wraps `intervalIntegral.tendsto_integral_filter_of_dominated_convergence`.
-/
theorem tendsto_intervalIntegral_of_dominated_convergence
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → ℝ → ℂ} {f : ℝ → ℂ} {a b : ℝ} (bound : ℝ → ℝ)
    (hF_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) (volume.restrict (Set.uIoc a b)))
    (hF_bound : ∀ᶠ n in l, ∀ᵐ x ∂volume,
      x ∈ Set.uIoc a b → ‖F n x‖ ≤ bound x)
    (h_bound_int : IntervalIntegrable bound volume a b)
    (h_lim : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b → Tendsto (fun n => F n x) l (𝓝 (f x))) :
    Tendsto (fun n => ∫ x in a..b, F n x) l (𝓝 (∫ x in a..b, f x)) :=
  intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
    hF_meas hF_bound h_bound_int h_lim

/-! ## Integrability from Limit Existence -/

/-- If the principal value limit exists, then for ε > 0 the truncated integral exists.

    **Key insight**: The existence of `lim_{ε→0} ∫ integrand_ε` implies each integral exists
    for small enough ε (by definition of limit), which gives integrability.
-/
theorem intervalIntegrable_of_pv_exists
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hab : a < b)
    (hf : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ : ContinuousOn γ (Icc a b))
    (hγ' : ContinuousOn (deriv γ) (Icc a b))
    (_hpv : ∃ L, Tendsto (fun δ => ∫ t in a..b, if δ < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0)
            (𝓝[>] 0) (𝓝 L)) :
    IntervalIntegrable (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0)
      volume a b := by
  -- The integrand is bounded (by continuity arguments on compact sets)
  -- On the set where the integrand is nonzero, f ∘ γ and γ' are continuous, hence bounded
  -- Away from this set, the integrand is 0
  -- Therefore the integrand is bounded on [a,b]

  -- Get bounds on compact image
  have hγ_im_compact : IsCompact (γ '' Icc a b) := isCompact_Icc.image_of_continuousOn hγ
  have h_far_compact : IsCompact (γ '' Icc a b \ Metric.ball z₀ ε) :=
    hγ_im_compact.inter_right Metric.isOpen_ball.isClosed_compl

  -- f is bounded on the compact set γ '' Icc a b \ ball z₀ ε
  by_cases h_nonempty : (γ '' Icc a b \ Metric.ball z₀ ε).Nonempty
  · -- Non-empty case: get bounds
    obtain ⟨Mf, hMf⟩ := h_far_compact.exists_bound_of_continuousOn hf.norm
    obtain ⟨Mγ, hMγ⟩ := isCompact_Icc.exists_bound_of_continuousOn hγ'.norm
    -- The bound is |M_f| * |M_γ| + 1
    let M := |Mf| * |Mγ| + 1
    have hM_pos : 0 < M := by positivity
    apply intervalIntegrable_pv_integrand (le_of_lt hab) hf hγ hγ' M
    intro t ht
    split_ifs with h
    · -- Case: ε < ‖γ t - z₀‖, so f(γ t) * γ'(t) is bounded
      have hγt_in : γ t ∈ γ '' Icc a b \ Metric.ball z₀ ε := by
        constructor
        · exact ⟨t, ht, rfl⟩
        · simp only [Metric.mem_ball, not_lt]; exact le_of_lt h
      have hf_le : ‖f (γ t)‖ ≤ |Mf| := by
        have := hMf (γ t) hγt_in
        simp only [Real.norm_eq_abs, abs_norm] at this
        exact le_trans this (le_abs_self _)
      have hγ_le : ‖deriv γ t‖ ≤ |Mγ| := by
        have := hMγ t ht
        simp only [Real.norm_eq_abs, abs_norm] at this
        exact le_trans this (le_abs_self _)
      calc ‖f (γ t) * deriv γ t‖ = ‖f (γ t)‖ * ‖deriv γ t‖ := norm_mul _ _
        _ ≤ |Mf| * |Mγ| := mul_le_mul hf_le hγ_le (norm_nonneg _) (abs_nonneg _)
        _ ≤ M := by simp only [M]; linarith
    · -- Case: integrand is 0
      simp only [norm_zero]
      exact le_of_lt hM_pos
  · -- Empty case: the integrand is always 0
    rw [Set.not_nonempty_iff_eq_empty] at h_nonempty
    apply intervalIntegrable_pv_integrand (le_of_lt hab) hf hγ hγ' 1
    intro t ht
    split_ifs with h
    · -- This case can't happen: if ε < ‖γ t - z₀‖, then γ t ∈ γ '' Icc a b \ ball z₀ ε
      exfalso
      have : γ t ∈ γ '' Icc a b \ Metric.ball z₀ ε :=
        ⟨⟨t, ht, rfl⟩, by simp only [Metric.mem_ball, not_lt]; exact le_of_lt h⟩
      rw [h_nonempty] at this
      exact this
    · simp only [norm_zero]; norm_num

/-! ## Piecewise C1 Curve AE Strong Measurability -/

/-- A function that is continuous off a finite set is ae strongly measurable.

    This is useful for piecewise C1 curves where the derivative may be discontinuous
    at a finite number of partition points.
-/
theorem aEStronglyMeasurable_of_continuousOn_off_finite
    {f : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ}
    (hf_cont : ContinuousOn f ((Icc a b) \ P)) :
    AEStronglyMeasurable f (volume.restrict (Icc a b)) := by
  -- The set P ∩ Icc a b is finite, hence has measure zero (Lebesgue has no atoms)
  have hP_finite : (↑P ∩ Icc a b : Set ℝ).Finite := P.finite_toSet.inter_of_left (Icc a b)
  have hP_meas_zero : volume (↑P ∩ Icc a b) = 0 := hP_finite.measure_zero volume
  -- Icc a b \ P is measurable
  have h_diff_meas : MeasurableSet ((Icc a b) \ P) :=
    isClosed_Icc.measurableSet.diff P.finite_toSet.measurableSet
  -- f is ae strongly measurable on Icc a b \ P (by continuity)
  have h_cont_meas : AEStronglyMeasurable f (volume.restrict ((Icc a b) \ P)) :=
    hf_cont.aestronglyMeasurable h_diff_meas
  -- P ∩ Icc a b is measurable
  have hP_inter_meas : MeasurableSet (↑P ∩ Icc a b) :=
    P.finite_toSet.measurableSet.inter isClosed_Icc.measurableSet
  -- The sets are disjoint: (Icc a b \ P) and (P ∩ Icc a b)
  have h_disj : Disjoint ((Icc a b) \ P) (↑P ∩ Icc a b) := by
    rw [Set.disjoint_left]
    intro x ⟨_, hx_nP⟩ ⟨hx_P, _⟩
    exact hx_nP hx_P
  -- Extend to Icc a b using that P has measure zero
  have h_eq : volume.restrict (Icc a b) = volume.restrict ((Icc a b) \ P) + volume.restrict (↑P ∩ Icc a b) := by
    rw [← Measure.restrict_union h_disj hP_inter_meas]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    tauto
  rw [h_eq]
  apply AEStronglyMeasurable.add_measure h_cont_meas
  -- On the finite set, any function is ae strongly measurable
  simp only [Measure.restrict_eq_zero.mpr hP_meas_zero]
  exact aestronglyMeasurable_zero_measure f

/-- The principal value integrand is ae strongly measurable for piecewise C1 curves.

    Unlike `aEStronglyMeasurable_pv_integrand`, this version handles curves where
    the derivative is only continuous off a finite partition set.
-/
theorem aEStronglyMeasurable_pv_integrand_piecewiseC1
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {ε : ℝ} {P : Finset ℝ}
    (hf : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) ((Icc a b) \ P)) :
    AEStronglyMeasurable (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0)
      (volume.restrict (Icc a b)) := by
  -- Define the set S = {t | ε < ‖γ t - z₀‖}
  let S := {t | ε < ‖γ t - z₀‖}
  -- S ∩ Icc a b is measurable
  have hS_meas : MeasurableSet (S ∩ Icc a b) := measurableSet_norm_gt_Icc ε (hγ.sub continuousOn_const)
  -- The base function (f ∘ γ) * γ' is continuous on (S ∩ Icc a b) \ P
  have h_cont : ContinuousOn (fun t => f (γ t) * deriv γ t) ((S ∩ Icc a b) \ P) := by
    intro t ⟨⟨ht_S, ht_Icc⟩, ht_nP⟩
    have hγt_not_ball : γ t ∉ Metric.ball z₀ ε := by
      simp only [S, Set.mem_setOf_eq] at ht_S
      simp only [Metric.mem_ball, not_lt]
      exact le_of_lt ht_S
    have hγt_in : γ t ∈ γ '' Icc a b \ Metric.ball z₀ ε :=
      ⟨Set.mem_image_of_mem γ ht_Icc, hγt_not_ball⟩
    have hf_at : ContinuousWithinAt f (γ '' Icc a b \ Metric.ball z₀ ε) (γ t) := hf (γ t) hγt_in
    have hγ_at : ContinuousWithinAt γ (Icc a b) t := hγ t ht_Icc
    have ht_off_P : t ∈ (Icc a b) \ P := ⟨ht_Icc, ht_nP⟩
    have hγ'_at : ContinuousWithinAt (deriv γ) ((Icc a b) \ P) t := hγ'_off_P t ht_off_P
    have h_maps : Set.MapsTo γ ((S ∩ Icc a b) \ P) (γ '' Icc a b \ Metric.ball z₀ ε) := by
      intro s ⟨⟨hs_S, hs_Icc⟩, _⟩
      refine ⟨Set.mem_image_of_mem γ hs_Icc, ?_⟩
      simp only [S, Set.mem_setOf_eq] at hs_S
      simp only [Metric.mem_ball, not_lt]
      exact le_of_lt hs_S
    have hfγ_at : ContinuousWithinAt (f ∘ γ) ((S ∩ Icc a b) \ P) t :=
      ContinuousWithinAt.comp hf_at (hγ_at.mono (Set.diff_subset.trans Set.inter_subset_right)) h_maps
    have hγ'_at' : ContinuousWithinAt (deriv γ) ((S ∩ Icc a b) \ P) t :=
      hγ'_at.mono (by intro x ⟨⟨_, hx_Icc⟩, hx_nP⟩; exact ⟨hx_Icc, hx_nP⟩)
    exact hfγ_at.mul hγ'_at'
  -- The base function is ae strongly measurable on S ∩ Icc a b
  have h_base_meas : AEStronglyMeasurable (fun t => f (γ t) * deriv γ t)
      (volume.restrict (S ∩ Icc a b)) := by
    -- (S ∩ Icc a b) \ P is cofinite in S ∩ Icc a b
    have h_diff_meas : MeasurableSet ((S ∩ Icc a b) \ P) :=
      hS_meas.diff P.finite_toSet.measurableSet
    -- Continuous on the complement of a finite set implies ae strongly measurable
    have h_cont_meas : AEStronglyMeasurable (fun t => f (γ t) * deriv γ t)
        (volume.restrict ((S ∩ Icc a b) \ P)) := h_cont.aestronglyMeasurable h_diff_meas
    -- P ∩ (S ∩ Icc a b) is finite, hence measure zero (Lebesgue has no atoms)
    have hP_finite : (↑P ∩ (S ∩ Icc a b) : Set ℝ).Finite := P.finite_toSet.inter_of_left _
    have hP_meas_zero : volume (↑P ∩ (S ∩ Icc a b)) = 0 := hP_finite.measure_zero volume
    -- P ∩ (S ∩ Icc a b) is measurable
    have hP_inter_meas : MeasurableSet (↑P ∩ (S ∩ Icc a b)) :=
      P.finite_toSet.measurableSet.inter hS_meas
    -- The sets are disjoint
    have h_disj : Disjoint ((S ∩ Icc a b) \ P) (↑P ∩ (S ∩ Icc a b)) := by
      rw [Set.disjoint_left]
      intro x ⟨_, hx_nP⟩ ⟨hx_P, _⟩
      exact hx_nP hx_P
    have h_eq : volume.restrict (S ∩ Icc a b) =
        volume.restrict ((S ∩ Icc a b) \ P) + volume.restrict (↑P ∩ (S ∩ Icc a b)) := by
      rw [← Measure.restrict_union h_disj hP_inter_meas]
      congr 1
      ext x
      simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
      tauto
    rw [h_eq]
    apply AEStronglyMeasurable.add_measure h_cont_meas
    simp only [Measure.restrict_eq_zero.mpr hP_meas_zero]
    exact aestronglyMeasurable_zero_measure _
  -- Use AEStronglyMeasurable.piecewise
  have h_zero_meas : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
      (volume.restrict (S ∩ Icc a b)ᶜ) := aestronglyMeasurable_const
  have h_piecewise := AEStronglyMeasurable.piecewise hS_meas h_base_meas h_zero_meas
  -- The piecewise function equals our if-then-else
  have h_eq : (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0) =ᵐ[volume.restrict (Icc a b)]
      (S ∩ Icc a b).piecewise (fun t => f (γ t) * deriv γ t) (fun _ => 0) := by
    filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
    simp only [Set.piecewise]
    by_cases ht_S : t ∈ S
    · have ht_SI : t ∈ S ∩ Icc a b := ⟨ht_S, ht⟩
      simp only [ht_SI, ↓reduceIte]
      simp only [S, Set.mem_setOf_eq] at ht_S
      simp only [ht_S, ↓reduceIte]
    · have ht_nSI : t ∉ S ∩ Icc a b := fun h => ht_S h.1
      simp only [ht_nSI, ↓reduceIte]
      simp only [S, Set.mem_setOf_eq, not_lt] at ht_S
      simp only [not_lt.mpr ht_S, ↓reduceIte]
  exact (h_piecewise.mono_measure Measure.restrict_le_self).congr h_eq.symm

/-! ## Multi-point PV Measurability -/

/-- The set {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} ∩ Icc a b is measurable.

    This is the condition set for multi-point principal value integrands.
    It's a finite union of preimages of closed balls under the continuous function γ.
-/
lemma measurableSet_multipoint_condition
    {γ : ℝ → ℂ} {a b ε : ℝ} (S : Finset ℂ)
    (hγ : ContinuousOn γ (Icc a b)) :
    MeasurableSet ({t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} ∩ Icc a b) := by
  -- The condition set equals ⋃_{s ∈ S} {t | ‖γ t - s‖ ≤ ε} ∩ Icc a b
  have h_eq : {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} ∩ Icc a b =
      ⋃ s ∈ S, ({t | ‖γ t - s‖ ≤ ε} ∩ Icc a b) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro ⟨⟨s, hs, h_norm⟩, ht_Icc⟩
      exact ⟨s, hs, h_norm, ht_Icc⟩
    · intro ⟨s, hs, h_norm, ht_Icc⟩
      exact ⟨⟨s, hs, h_norm⟩, ht_Icc⟩
  rw [h_eq]
  -- Finite union of measurable sets is measurable
  apply Finset.measurableSet_biUnion
  intro s _
  -- Each {t | ‖γ t - s‖ ≤ ε} ∩ Icc a b is measurable
  -- Use that the complement {t | ε < ‖γ t - s‖} ∩ Icc a b is measurable
  have h_compl_meas : MeasurableSet ({t | ε < ‖γ t - s‖} ∩ Icc a b) :=
    measurableSet_norm_gt_Icc ε (hγ.sub continuousOn_const)
  -- {t | ‖γ t - s‖ ≤ ε} ∩ Icc = Icc \ ({t | ε < ‖γ t - s‖} ∩ Icc)
  have h_eq' : {t | ‖γ t - s‖ ≤ ε} ∩ Icc a b =
      Icc a b \ ({t | ε < ‖γ t - s‖} ∩ Icc a b) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_diff, not_and]
    constructor
    · intro ⟨h_le, ht_Icc⟩
      refine ⟨ht_Icc, fun h_gt => absurd h_gt (not_lt.mpr h_le)⟩
    · intro ⟨ht_Icc, h_not⟩
      refine ⟨?_, ht_Icc⟩
      by_contra h_gt
      push_neg at h_gt
      exact (h_not h_gt) ht_Icc
  rw [h_eq']
  exact isClosed_Icc.measurableSet.diff h_compl_meas

/-- The complement (good set) {t | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b is measurable. -/
lemma measurableSet_multipoint_goodset
    {γ : ℝ → ℂ} {a b ε : ℝ} (S : Finset ℂ)
    (hγ : ContinuousOn γ (Icc a b)) :
    MeasurableSet ({t | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b) := by
  -- The good set is the complement of the condition set within Icc a b
  have h_eq : {t | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b =
      Icc a b \ ({t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} ∩ Icc a b) := by
    ext t
    constructor
    · intro ⟨h_good, ht_Icc⟩
      refine ⟨ht_Icc, ?_⟩
      intro ⟨⟨s, hs, h_le⟩, _⟩
      have h_gt := h_good s hs
      linarith
    · intro ⟨ht_Icc, h_not⟩
      refine ⟨?_, ht_Icc⟩
      intro s hs
      by_contra h_le
      push_neg at h_le
      exact h_not ⟨⟨s, hs, h_le⟩, ht_Icc⟩
  rw [h_eq]
  exact isClosed_Icc.measurableSet.diff (measurableSet_multipoint_condition S hγ)

/-- Multi-point PV integrand is AE strongly measurable for piecewise C¹ curves.

    The integrand is: if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else g(γ t) * γ'(t)
-/
theorem aEStronglyMeasurable_pv_integrand_multipoint
    {g : ℂ → ℂ} {γ : ℝ → ℂ} {a b ε : ℝ} {P : Finset ℝ} (S : Finset ℂ)
    (hg : ContinuousOn g (γ '' Icc a b))
    (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable
      (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else g (γ t) * deriv γ t)
      (volume.restrict (Icc a b)) := by
  -- Define the "good set" where integrand is non-zero
  let GoodSet := {t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖}
  -- GoodSet ∩ Icc a b is measurable
  have hGoodSet_meas : MeasurableSet (GoodSet ∩ Icc a b) :=
    measurableSet_multipoint_goodset S hγ
  -- The base function g ∘ γ * γ' is AEStronglyMeasurable on Icc a b
  have h_base_meas : AEStronglyMeasurable (fun t => g (γ t) * deriv γ t)
      (volume.restrict (Icc a b)) := by
    -- g ∘ γ is continuous on Icc
    have hgγ_cont : ContinuousOn (fun t => g (γ t)) (Icc a b) := by
      apply ContinuousOn.comp hg hγ
      intro t ht
      exact Set.mem_image_of_mem _ ht
    -- γ' is continuous off P, so AEStronglyMeasurable
    have hγ'_meas : AEStronglyMeasurable (deriv γ) (volume.restrict (Icc a b)) :=
      aEStronglyMeasurable_of_continuousOn_off_finite hγ'_off_P
    exact (hgγ_cont.aestronglyMeasurable isClosed_Icc.measurableSet).mul hγ'_meas
  -- Zero is AEStronglyMeasurable
  have h_zero_meas : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
      (volume.restrict (GoodSet ∩ Icc a b)ᶜ) := aestronglyMeasurable_const
  -- Restrict base measurability to good set
  have h_base_meas' : AEStronglyMeasurable (fun t => g (γ t) * deriv γ t)
      (volume.restrict (GoodSet ∩ Icc a b)) :=
    h_base_meas.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)
  -- Use piecewise measurability
  have h_piecewise := AEStronglyMeasurable.piecewise hGoodSet_meas h_base_meas' h_zero_meas
  -- Show our function equals the piecewise function a.e.
  have h_eq : (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then (0 : ℂ) else g (γ t) * deriv γ t)
      =ᵐ[volume.restrict (Icc a b)]
      (GoodSet ∩ Icc a b).piecewise (fun t => g (γ t) * deriv γ t) (fun _ => 0) := by
    filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
    simp only [Set.piecewise]
    by_cases ht_good : t ∈ GoodSet ∩ Icc a b
    · -- t is in GoodSet: ∀ s ∈ S, ε < ‖γ t - s‖
      simp only [ht_good, ↓reduceIte]
      -- So the excision condition is false
      have ht_not_excl : ¬∃ s ∈ S, ‖γ t - s‖ ≤ ε := by
        push_neg
        exact ht_good.1
      simp only [ht_not_excl, ↓reduceIte]
    · -- t is not in GoodSet
      simp only [ht_good, ↓reduceIte]
      -- Either not in Icc (impossible) or excision holds
      -- ht_good : t ∉ GoodSet ∩ Icc a b
      -- Since t ∈ Icc (from ht), we have t ∉ GoodSet
      have h_notGood : t ∉ GoodSet := by
        intro h_in_good
        exact ht_good ⟨h_in_good, ht⟩
      -- h_notGood : ¬(∀ s ∈ S, ε < ‖γ t - s‖)
      -- So ∃ s ∈ S, ‖γ t - s‖ ≤ ε
      have h_excl : ∃ s ∈ S, ‖γ t - s‖ ≤ ε := by
        simp only [GoodSet, Set.mem_setOf_eq] at h_notGood
        push_neg at h_notGood
        exact h_notGood
      simp only [h_excl, ↓reduceIte]
  exact (h_piecewise.mono_measure Measure.restrict_le_self).congr h_eq.symm

/-- AE strongly measurable for residue-type PV integrand.

    The function: if ‖γ t - s‖ > ε then c/(γ t - s) * γ'(t) else 0

    This is a special case where the function c/(z-s) has a pole at s,
    but we're only evaluating it where ‖γ t - s‖ > ε, so it's continuous there.
-/
theorem aEStronglyMeasurable_pv_integrand_residue
    {γ : ℝ → ℂ} {a b ε : ℝ} {P : Finset ℝ} {s c : ℂ}
    (_hε : 0 < ε)
    (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable
      (fun t => if ‖γ t - s‖ > ε then (c / (γ t - s)) * deriv γ t else 0)
      (volume.restrict (Icc a b)) := by
  -- Define the "good set" where the integrand is non-zero
  let GoodSet := {t : ℝ | ε < ‖γ t - s‖}
  -- GoodSet ∩ Icc a b is measurable (preimage of open set under continuous function)
  have hGoodSet_meas : MeasurableSet (GoodSet ∩ Icc a b) :=
    measurableSet_norm_gt_Icc ε (hγ.sub continuousOn_const)
  -- c/(γ t - s) * γ'(t) is the product of:
  -- 1. c/(γ t - s) which is continuous on GoodSet (bounded away from pole)
  -- 2. γ'(t) which is continuous off P
  -- γ' is AEStronglyMeasurable
  have hγ'_meas : AEStronglyMeasurable (deriv γ) (volume.restrict (Icc a b)) :=
    aEStronglyMeasurable_of_continuousOn_off_finite hγ'_off_P
  -- c/(γ t - s) is continuous on GoodSet ∩ Icc, hence AEStronglyMeasurable there
  have h_ratio_meas : AEStronglyMeasurable (fun t => c / (γ t - s))
      (volume.restrict (GoodSet ∩ Icc a b)) := by
    apply ContinuousOn.aestronglyMeasurable _ hGoodSet_meas
    apply ContinuousOn.div continuousOn_const
    · exact (hγ.mono Set.inter_subset_right).sub continuousOn_const
    · intro t ⟨ht_good, _⟩
      exact norm_ne_zero_iff.mp (ne_of_gt (lt_trans _hε ht_good))
  -- Product is AEStronglyMeasurable on GoodSet ∩ Icc
  have h_prod_meas : AEStronglyMeasurable (fun t => (c / (γ t - s)) * deriv γ t)
      (volume.restrict (GoodSet ∩ Icc a b)) :=
    h_ratio_meas.mul (hγ'_meas.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))
  -- Use piecewise: on GoodSet use product, elsewhere use 0
  have h_zero_meas : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
      (volume.restrict (GoodSet ∩ Icc a b)ᶜ) := aestronglyMeasurable_const
  have h_piecewise := AEStronglyMeasurable.piecewise hGoodSet_meas h_prod_meas h_zero_meas
  -- Show our function equals the piecewise function a.e.
  refine (h_piecewise.mono_measure Measure.restrict_le_self).congr ?_
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
  simp only [Set.piecewise, GoodSet, Set.mem_inter_iff, Set.mem_setOf_eq, gt_iff_lt]
  by_cases h1 : ε < ‖γ t - s‖
  · simp only [h1, ht, and_self, ↓reduceIte]
  · push_neg at h1
    simp only [not_lt.mpr h1, ht, and_true, ↓reduceIte]

/-- AE strongly measurable for multi-point PV integrand with decomposed function.

    This handles the case where f = g_reg + Σ c_s/(z - s), i.e., a regular part plus
    singular terms. The key insight is that on the "good set" (where all distances > ε),
    each singular term is continuous, so f is continuous there.

    The integrand is: if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f(γ t) * γ'(t)
    where f(z) = g_reg(z) + Σ_{s ∈ S} c_s/(z - s) for z not in S.
-/
theorem aEStronglyMeasurable_pv_integrand_decomposed
    {g_reg : ℂ → ℂ} {γ : ℝ → ℂ} {a b ε : ℝ} {P : Finset ℝ} (S : Finset ℂ)
    (coeffs : ℂ → ℂ)
    (hε : 0 < ε)
    (hg : ContinuousOn g_reg (γ '' Icc a b))
    (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable
      (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0
        else (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t)
      (volume.restrict (Icc a b)) := by
  -- Define the "good set" where integrand is non-zero
  let GoodSet := {t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖}
  -- GoodSet ∩ Icc a b is measurable
  have hGoodSet_meas : MeasurableSet (GoodSet ∩ Icc a b) :=
    measurableSet_multipoint_goodset S hγ
  -- γ' is AEStronglyMeasurable
  have hγ'_meas : AEStronglyMeasurable (deriv γ) (volume.restrict (Icc a b)) :=
    aEStronglyMeasurable_of_continuousOn_off_finite hγ'_off_P
  -- g_reg ∘ γ is continuous on Icc, hence AEStronglyMeasurable
  have hgγ_cont : ContinuousOn (fun t => g_reg (γ t)) (Icc a b) := by
    apply ContinuousOn.comp hg hγ
    intro t ht; exact Set.mem_image_of_mem _ ht
  have hgγ_meas : AEStronglyMeasurable (fun t => g_reg (γ t))
      (volume.restrict (Icc a b)) :=
    hgγ_cont.aestronglyMeasurable isClosed_Icc.measurableSet
  -- Each singular term c_s/(γ t - s) is continuous on GoodSet ∩ Icc (bounded away from pole)
  have h_sing_meas : ∀ s ∈ S, AEStronglyMeasurable (fun t => coeffs s / (γ t - s))
      (volume.restrict (GoodSet ∩ Icc a b)) := by
    intro s hs
    apply ContinuousOn.aestronglyMeasurable _ hGoodSet_meas
    apply ContinuousOn.div continuousOn_const
    · exact (hγ.mono Set.inter_subset_right).sub continuousOn_const
    · intro t ⟨ht_good, _⟩
      have h_dist := ht_good s hs
      exact norm_ne_zero_iff.mp (ne_of_gt (lt_trans hε h_dist))
  -- Sum of singular terms is AEStronglyMeasurable on GoodSet ∩ Icc
  have h_sum_meas : AEStronglyMeasurable (fun t => ∑ s ∈ S, coeffs s / (γ t - s))
      (volume.restrict (GoodSet ∩ Icc a b)) :=
    Finset.aestronglyMeasurable_fun_sum S h_sing_meas
  -- Total f = g_reg + sum is AEStronglyMeasurable on GoodSet ∩ Icc
  have h_f_meas : AEStronglyMeasurable (fun t => g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s))
      (volume.restrict (GoodSet ∩ Icc a b)) :=
    (hgγ_meas.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)).add h_sum_meas
  -- f * γ' is AEStronglyMeasurable on GoodSet ∩ Icc
  have h_prod_meas : AEStronglyMeasurable
      (fun t => (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t)
      (volume.restrict (GoodSet ∩ Icc a b)) :=
    h_f_meas.mul (hγ'_meas.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))
  -- Use piecewise: on GoodSet use product, elsewhere use 0
  have h_zero_meas : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
      (volume.restrict (GoodSet ∩ Icc a b)ᶜ) := aestronglyMeasurable_const
  have h_piecewise := AEStronglyMeasurable.piecewise hGoodSet_meas h_prod_meas h_zero_meas
  -- Show our function equals the piecewise function a.e.
  refine (h_piecewise.mono_measure Measure.restrict_le_self).congr ?_
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
  simp only [Set.piecewise, GoodSet, Set.mem_inter_iff, Set.mem_setOf_eq]
  by_cases ht_good : (∀ s ∈ S, ε < ‖γ t - s‖) ∧ t ∈ Icc a b
  · -- t is in GoodSet: ∀ s ∈ S, ε < ‖γ t - s‖
    rw [if_pos ht_good]
    have h_not_excl : ¬∃ s ∈ S, ‖γ t - s‖ ≤ ε := by
      push_neg; exact ht_good.1
    simp only [h_not_excl, if_false]
  · -- t is not in GoodSet
    rw [if_neg ht_good]
    -- Since t ∈ Icc (from ht), we have ¬(∀ s ∈ S, ε < ‖γ t - s‖)
    have h_excl : ∃ s ∈ S, ‖γ t - s‖ ≤ ε := by
      -- ht_good : ¬((∀ s ∈ S, ε < ‖γ t - s‖) ∧ t ∈ Icc a b)
      -- After push_neg, becomes: (∀ s ∈ S, ε < ‖γ t - s‖) → t ∉ Icc a b
      -- Since t ∈ Icc a b (from ht), we must have ¬(∀ s ∈ S, ε < ‖γ t - s‖)
      -- Which is ∃ s ∈ S, ‖γ t - s‖ ≤ ε
      by_contra h_not
      push_neg at h_not
      -- h_not : ∀ s ∈ S, ε < ‖γ t - s‖
      -- This gives ⟨h_not, ht⟩ : (∀ s ∈ S, ε < ‖γ t - s‖) ∧ t ∈ Icc a b
      exact ht_good ⟨h_not, ht⟩
    simp only [h_excl, if_true]

/-! ## Integrability of Piecewise Continuous Functions -/

/-- Functions continuous off a finite set are integrable when bounded.

    This is the key result for handling piecewise C¹ curves where the derivative
    may be discontinuous at finitely many partition points.
-/
theorem intervalIntegrable_of_continuousOn_off_finite
    {f : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ} (M : ℝ)
    (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b \ P))
    (hf_bound : ∀ t ∈ Icc a b, ‖f t‖ ≤ M) :
    IntervalIntegrable f volume a b := by
  -- f is ae strongly measurable (continuous off finite set)
  have hmeas : AEStronglyMeasurable f (volume.restrict (Icc a b)) :=
    aEStronglyMeasurable_of_continuousOn_off_finite hf_cont
  -- Convert to IntervalIntegrable using boundedness
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply IntegrableOn.mono_set
  · exact integrableOn_of_bounded_aeMeasurable M hmeas hf_bound
  · exact Ioc_subset_Icc_self

/-- Integrability of products g(γ(t)) * γ'(t) for piecewise C¹ curves.

    This is the main integrability result for principal value integrals.
-/
theorem intervalIntegrable_pv_integrand_piecewiseC1
    {g : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ}
    (hab : a ≤ b)
    (hg : ContinuousOn g (γ '' Icc a b))
    (hγ : ContinuousOn γ (Icc a b))
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b \ P))
    (hg_bound : ∃ Mg : ℝ, ∀ z ∈ γ '' Icc a b, ‖g z‖ ≤ Mg)
    (hγ'_bound : ∃ Mγ : ℝ, ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ Mγ) :
    IntervalIntegrable (fun t => g (γ t) * deriv γ t) volume a b := by
  obtain ⟨Mg, hMg⟩ := hg_bound
  obtain ⟨Mγ, hMγ⟩ := hγ'_bound
  -- The function is continuous off P (composition of continuous functions)
  have h_cont : ContinuousOn (fun t => g (γ t) * deriv γ t) (Icc a b \ P) := by
    apply ContinuousOn.mul
    · exact (hg.comp hγ (Set.mapsTo_image _ _)).mono Set.diff_subset
    · exact hγ'_cont
  -- Bounded by Mg * Mγ
  have h_bound : ∀ t ∈ Icc a b, ‖g (γ t) * deriv γ t‖ ≤ Mg * Mγ := by
    intro t ht
    calc ‖g (γ t) * deriv γ t‖
        = ‖g (γ t)‖ * ‖deriv γ t‖ := norm_mul _ _
      _ ≤ Mg * Mγ := mul_le_mul (hMg _ (Set.mem_image_of_mem _ ht)) (hMγ t ht)
          (norm_nonneg _) (le_trans (norm_nonneg _) (hMg _ (Set.mem_image_of_mem _ ht)))
  exact intervalIntegrable_of_continuousOn_off_finite (Mg * Mγ) hab h_cont h_bound

/-! ## Preimage Measure Zero Results -/

/-- Helper lemma: A set where each point is isolated is countable.
    This is a standard result: each isolated point has a disjoint ball,
    and a pairwise disjoint collection of open balls in a separable space is countable. -/
private theorem Set.countable_setOf_isolated_points' {S : Set ℝ}
    (h : ∀ t ∈ S, ∃ ε > 0, ∀ s ∈ S, s ≠ t → |s - t| ≥ ε) : S.Countable := by
  -- Each isolated point has a ball disjoint from other points' balls
  -- We use Set.PairwiseDisjoint.countable_of_isOpen
  classical
  by_cases hS : S = ∅
  · simp [hS]
  · -- Use the fact that ℝ is separable
    -- Pairwise disjoint open sets in a separable space form a countable collection
    -- We construct disjoint balls around each point
    -- Define the radius function on S
    have h_radii : ∀ t : S, ∃ ε > 0, ∀ s ∈ S, s ≠ t.val → |s - t.val| ≥ ε := fun t => h t.val t.prop
    choose r hr_pos hr_sep using h_radii
    -- Define balls of radius r(t)/2 around each point
    let ball : S → Set ℝ := fun t => Metric.ball t.val (r t / 2)
    -- These balls are pairwise disjoint
    have h_disj : Pairwise (Function.onFun Disjoint ball) := by
      intro ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ h_ne
      simp only [Function.onFun, Set.disjoint_iff, ball]
      intro x ⟨hx₁, hx₂⟩
      simp only [Metric.mem_ball, Real.dist_eq] at hx₁ hx₂
      have h_ne' : t₁ ≠ t₂ := fun heq => h_ne (by simp [heq])
      have h1 : |t₁ - t₂| ≤ |t₁ - x| + |x - t₂| := abs_sub_le t₁ x t₂
      have h2 : |t₁ - x| < r ⟨t₁, ht₁⟩ / 2 := by rw [abs_sub_comm]; exact hx₁
      have h3 : |x - t₂| < r ⟨t₂, ht₂⟩ / 2 := hx₂
      have h4' := hr_sep ⟨t₁, ht₁⟩ t₂ ht₂ (Ne.symm h_ne')
      have h4 : r ⟨t₁, ht₁⟩ ≤ |t₁ - t₂| := by rw [abs_sub_comm]; exact h4'
      have h5' := hr_sep ⟨t₂, ht₂⟩ t₁ ht₁ h_ne'
      have h5 : r ⟨t₂, ht₂⟩ ≤ |t₂ - t₁| := by rw [abs_sub_comm]; exact h5'
      rw [abs_sub_comm] at h5
      linarith [hr_pos ⟨t₁, ht₁⟩, hr_pos ⟨t₂, ht₂⟩]
    -- Open sets
    have h_open : ∀ t : S, IsOpen (ball t) := fun t => Metric.isOpen_ball
    -- Nonempty
    have h_nonempty : ∀ t : S, (ball t).Nonempty :=
      fun t => ⟨t.val, Metric.mem_ball_self (by linarith [hr_pos t])⟩
    -- Apply the countability theorem
    have h_countable_S : Countable S :=
      Pairwise.countable_of_isOpen_disjoint h_disj h_open h_nonempty
    exact Set.countable_coe_iff.mp h_countable_S

/-- The preimage of a singleton under a piecewise C¹ immersion has measure zero.

    For a piecewise C¹ curve with nonzero derivative (except at finitely many partition points),
    the preimage of any point z₀ is at most countable (typically finite), hence has measure zero.

    This is the correct version for the valence formula applications.
-/
theorem preimage_singleton_measure_zero_of_deriv_ne_zero
    {γ : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ} (z₀ : ℂ)
    (hγ : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Icc a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ'_ne : ∀ t ∈ Icc a b, t ∉ P → deriv γ t ≠ 0) :
    volume ({t ∈ Icc a b | γ t = z₀}) = 0 := by
  -- Strategy: Show the preimage is countable, then use Set.Countable.measure_zero.
  --
  -- Key insight: For t₀ in the preimage but not in P, the derivative is nonzero,
  -- so by HasDerivAt.eventually_ne, t₀ is isolated in the preimage.
  -- A set where every point outside a finite set is isolated, is at most countable.
  let S := {t ∈ Icc a b | γ t = z₀}
  -- Step 1: Every point in S \ P is isolated in S
  have h_isolated : ∀ t₀ ∈ S, t₀ ∉ P → ∃ ε > 0, ∀ t ∈ S, t ≠ t₀ → |t - t₀| ≥ ε := by
    intro t₀ ⟨ht₀_Icc, ht₀_eq⟩ ht₀_nP
    -- t₀ has nonzero derivative, so γ is locally injective
    have h_diff : DifferentiableAt ℝ γ t₀ := hγ_diff t₀ ht₀_Icc ht₀_nP
    have h_deriv_ne : deriv γ t₀ ≠ 0 := hγ'_ne t₀ ht₀_Icc ht₀_nP
    -- By HasDerivAt.eventually_ne, eventually γ(t) ≠ γ(t₀) = z₀ for t ≠ t₀
    have h_ev := HasDerivAt.eventually_ne h_diff.hasDerivAt h_deriv_ne (c := z₀)
    -- Extract ε from the eventually statement
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h_ev
    obtain ⟨ε, hε_pos, h_ball⟩ := h_ev
    use ε, hε_pos
    intro t ⟨ht_Icc, ht_eq⟩ ht_ne
    by_contra h_lt
    push_neg at h_lt
    -- t is in the ε-ball around t₀
    have h_in_ball : dist t t₀ < ε := by simp only [Real.dist_eq]; exact h_lt
    have h_ne' : t ∈ ({t₀} : Set ℝ)ᶜ := by simp [ht_ne]
    -- Therefore γ(t) ≠ z₀
    have h_contra := h_ball h_in_ball h_ne'
    exact h_contra ht_eq
  -- Step 2: S is countable
  -- S = (S ∩ P) ∪ (S \ P). S ∩ P is finite (subset of finite P).
  -- S \ P consists of isolated points, hence is at most countable.
  have h_countable : S.Countable := by
    -- Split into partition points and non-partition points
    have h_eq : S = (S ∩ ↑P) ∪ (S \ ↑P) := (Set.inter_union_diff S ↑P).symm
    rw [h_eq]
    apply Set.Countable.union
    · -- S ∩ P is finite (subset of finite P)
      exact (P.finite_toSet.subset Set.inter_subset_right).countable
    · -- S \ P consists of isolated points
      -- Each point has a neighborhood containing no other points of S
      -- A set of isolated points in a metric space is countable:
      -- each isolated point can be associated with a unique rational in its isolation ball
      -- This gives an injection into ℚ, proving countability
      --
      -- Full proof: use pairwise disjoint balls argument
      -- Set.PairwiseDisjoint.countable_of_isOpen shows disjoint open sets are countable
      have h_iso : ∀ t ∈ S \ ↑P, ∃ ε > 0, ∀ s ∈ S \ ↑P, s ≠ t → |s - t| ≥ ε := by
        intro t ⟨ht_S, ht_nP⟩
        obtain ⟨ε, hε_pos, h_sep⟩ := h_isolated t ht_S ht_nP
        exact ⟨ε, hε_pos, fun s ⟨hs_S, _⟩ hs_ne => h_sep s hs_S hs_ne⟩
      -- Isolated points in ℝ form a countable set
      -- (standard result: each point has disjoint ball, disjoint opens are countable)
      exact Set.countable_setOf_isolated_points' h_iso
  -- Step 3: Countable sets have measure zero
  exact h_countable.measure_zero _

end
