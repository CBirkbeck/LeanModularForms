/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ClassicalCPV

/-!
# Cauchy Principal Value Theory

Theory of Cauchy principal value integrals for piecewise C¹ contour integration.
The principal value approach allows contours to pass through singularities.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- The integrand for the Cauchy principal value is uniformly bounded on `Icc a b`. -/
theorem cauchyPrincipalValueIntegrand_bounded (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (ε : ℝ) (_hε : 0 < ε) (hf_cont : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ_cont : ContinuousOn γ (Icc a b)) (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    ∃ M : ℝ, ∀ t ∈ Icc a b, ‖cauchyPrincipalValueIntegrand' f γ z₀ ε t‖ ≤ M := by
  by_cases h_empty : (γ '' Icc a b \ Metric.ball z₀ ε).Nonempty
  · obtain ⟨Mf, hMf⟩ := ((isCompact_Icc.image_of_continuousOn hγ_cont).inter_right
      Metric.isOpen_ball.isClosed_compl).exists_bound_of_continuousOn hf_cont.norm
    obtain ⟨Mγ, hMγ⟩ := isCompact_Icc.exists_bound_of_continuousOn hγ'_cont.norm
    have hMf' : ∀ x ∈ γ '' Icc a b \ Metric.ball z₀ ε, ‖f x‖ ≤ Mf := fun x hx => by
      simpa using hMf x hx
    have hMγ' : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ Mγ := fun t ht => by
      simpa using hMγ t ht
    obtain ⟨x₀, hx₀_img, hx₀_far⟩ := h_empty
    obtain ⟨t₀, ht₀, rfl⟩ := hx₀_img
    have hMf_nn : (0 : ℝ) ≤ Mf := (norm_nonneg _).trans (hMf' _ ⟨⟨t₀, ht₀, rfl⟩, hx₀_far⟩)
    have hMγ_nn : (0 : ℝ) ≤ Mγ := (norm_nonneg _).trans (hMγ' _ ht₀)
    refine ⟨Mf * Mγ + 1, fun t ht => ?_⟩
    unfold cauchyPrincipalValueIntegrand'
    split_ifs with h
    · have hmem : γ t ∈ γ '' Icc a b \ Metric.ball z₀ ε :=
        ⟨⟨t, ht, rfl⟩, by simp only [Metric.mem_ball, not_lt, dist_eq_norm]; exact h.le⟩
      calc ‖f (γ t) * deriv γ t‖
          = ‖f (γ t)‖ * ‖deriv γ t‖ := norm_mul _ _
        _ ≤ Mf * Mγ := mul_le_mul (hMf' _ hmem) (hMγ' t ht) (norm_nonneg _) hMf_nn
        _ ≤ Mf * Mγ + 1 := by linarith
    · simp only [norm_zero]
      linarith [mul_nonneg hMf_nn hMγ_nn]
  · refine ⟨0, fun t ht => ?_⟩
    unfold cauchyPrincipalValueIntegrand'
    split_ifs with h
    · exact absurd ⟨γ t, ⟨t, ht, rfl⟩, by
        simp only [Metric.mem_ball, not_lt, dist_eq_norm]; exact h.le⟩ h_empty
    · simp

/-- The principal value support set `{t | ε < ‖γ t - z₀‖} ∩ Icc a b` is measurable. -/
lemma measurableSet_pv_support (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (ε : ℝ)
    (hγ_cont : ContinuousOn γ (Icc a b)) :
    MeasurableSet ({t | ε < ‖γ t - z₀‖} ∩ Icc a b) := by
  have h_norm_cont : ContinuousOn (fun t => ‖γ t - z₀‖) (Icc a b) :=
    (hγ_cont.sub continuousOn_const).norm
  obtain ⟨U, hU_open, hU_eq⟩ := continuousOn_iff'.mp h_norm_cont (Ioi ε) isOpen_Ioi
  rw [show {t | ε < ‖γ t - z₀‖} ∩ Icc a b = U ∩ Icc a b from hU_eq]
  exact hU_open.measurableSet.inter isClosed_Icc.measurableSet

/-- The integrand `f ∘ γ * γ'` is continuous on the principal-value support set. -/
lemma continuousOn_pv_base (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (ε : ℝ)
    (hf_cont : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ_cont : ContinuousOn γ (Icc a b)) (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    ContinuousOn (fun t => f (γ t) * deriv γ t) ({t | ε < ‖γ t - z₀‖} ∩ Icc a b) := by
  have h_maps : MapsTo γ ({t | ε < ‖γ t - z₀‖} ∩ Icc a b)
      (γ '' Icc a b \ Metric.ball z₀ ε) := fun s ⟨hs_far, hs_Icc⟩ =>
    ⟨mem_image_of_mem γ hs_Icc, by
      simp only [Metric.mem_ball, not_lt, dist_eq_norm]; exact hs_far.le⟩
  intro t ht
  refine (ContinuousWithinAt.comp (hf_cont _ (h_maps ht))
    ((hγ_cont t ht.2).mono inter_subset_right) h_maps).mul ?_
  exact (hγ'_cont t ht.2).mono inter_subset_right

private theorem aEStronglyMeasurable_pv_integrand {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    {ε : ℝ} (hf : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ : ContinuousOn γ (Icc a b)) (hγ' : ContinuousOn (deriv γ) (Icc a b)) :
    AEStronglyMeasurable (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0)
      (volume.restrict (Icc a b)) := by
  set S := {t | ε < ‖γ t - z₀‖} with hS
  have hS_meas : MeasurableSet (S ∩ Icc a b) := measurableSet_pv_support γ a b z₀ ε hγ
  have h_piecewise := AEStronglyMeasurable.piecewise hS_meas
    ((continuousOn_pv_base f γ a b z₀ ε hf hγ hγ').aestronglyMeasurable hS_meas)
    (aestronglyMeasurable_const :
      AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ)) (volume.restrict (S ∩ Icc a b)ᶜ))
  refine (h_piecewise.mono_measure Measure.restrict_le_self).congr ?_
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
  by_cases ht_S : ε < ‖γ t - z₀‖ <;>
    simp [Set.piecewise, hS, ht, ht_S]

/-- The Cauchy principal value integrand is interval-integrable on `[a, b]`. -/
theorem cauchyPrincipalValueIntegrand_integrable (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (ε : ℝ) (hε : 0 < ε) (hab : a < b)
    (hf_cont : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ_cont : ContinuousOn γ (Icc a b)) (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' f γ z₀ ε) volume a b := by
  obtain ⟨M, hM⟩ :=
    cauchyPrincipalValueIntegrand_bounded f γ a b z₀ ε hε hf_cont hγ_cont hγ'_cont
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
  refine (IntegrableOn.of_bound measure_Icc_lt_top
    (aEStronglyMeasurable_pv_integrand hf_cont hγ_cont hγ'_cont) (max M 0) ?_).mono_set
    Ioc_subset_Icc_self
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with x hx
  exact (hM x hx).trans (le_max_left M 0)

/-- Dominated convergence for principal value integrals. -/
theorem cauchyPrincipalValue_of_dominated (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (hab : a < b) (M : ℝ) (_hM : 0 < M)
    (h_bound : ∀ ε > 0, ∀ t ∈ Icc a b, ‖cauchyPrincipalValueIntegrand' f γ z₀ ε t‖ ≤ M)
    (h_ae_limit : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∃ L, Tendsto (fun ε => cauchyPrincipalValueIntegrand' f γ z₀ ε t) (𝓝[>] 0) (𝓝 L))
    (hF_meas : ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (cauchyPrincipalValueIntegrand' f γ z₀ ε) (volume.restrict (uIoc a b))) :
    CauchyPrincipalValueExists' f γ a b z₀ := by
  have h_bound_ae : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ t ∂volume,
      t ∈ uIoc a b → ‖cauchyPrincipalValueIntegrand' f γ z₀ ε t‖ ≤ M := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Eventually.of_forall fun t ht =>
      h_bound ε hε t (Ioc_subset_Icc_self (uIoc_of_le hab.le ▸ ht))
  rw [ae_restrict_iff' isClosed_Icc.measurableSet] at h_ae_limit
  let g : ℝ → ℂ := fun t => Filter.limUnder (𝓝[>] (0 : ℝ))
    (fun ε => cauchyPrincipalValueIntegrand' f γ z₀ ε t)
  have h_lim_conv : ∀ᵐ t ∂volume, t ∈ uIoc a b →
      Tendsto (fun ε => cauchyPrincipalValueIntegrand' f γ z₀ ε t) (𝓝[>] 0) (𝓝 (g t)) := by
    filter_upwards [h_ae_limit] with t ht ht_mem
    obtain ⟨L, hL⟩ := ht (Ioc_subset_Icc_self (uIoc_of_le hab.le ▸ ht_mem))
    rwa [show g t = L from hL.limUnder_eq]
  exact ⟨∫ t in a..b, g t, intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => M) hF_meas h_bound_ae intervalIntegrable_const h_lim_conv⟩

private theorem pv_uniform_bound_of_continuous_aux (g : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (hab : a < b) (hg : ContinuousOn g (γ '' Icc a b)) (hγ : ContinuousOn γ (Icc a b))
    (hγ' : ContinuousOn (deriv γ) (Icc a b)) :
    ∃ M > 0, ∀ ε > 0, ∀ t ∈ Icc a b, ‖cauchyPrincipalValueIntegrand' g γ z₀ ε t‖ ≤ M := by
  obtain ⟨Mg, hMg⟩ :=
    (isCompact_Icc.image_of_continuousOn hγ).exists_bound_of_continuousOn hg.norm
  obtain ⟨Mγ', hMγ'⟩ := isCompact_Icc.exists_bound_of_continuousOn hγ'.norm
  have hMg' : ∀ z ∈ γ '' Icc a b, ‖g z‖ ≤ Mg := fun z hz => by
    simpa using hMg z hz
  have hMγ'' : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ Mγ' := fun t ht => by
    simpa using hMγ' t ht
  have hMg_nn : (0 : ℝ) ≤ Mg :=
    (norm_nonneg _).trans (hMg' _ ⟨a, left_mem_Icc.mpr hab.le, rfl⟩)
  have hMγ_nn : (0 : ℝ) ≤ Mγ' :=
    (norm_nonneg _).trans (hMγ'' a (left_mem_Icc.mpr hab.le))
  refine ⟨Mg * Mγ' + 1, by linarith [mul_nonneg hMg_nn hMγ_nn], fun ε _ t ht => ?_⟩
  unfold cauchyPrincipalValueIntegrand'
  split_ifs with h
  · calc ‖g (γ t) * deriv γ t‖
        = ‖g (γ t)‖ * ‖deriv γ t‖ := norm_mul _ _
      _ ≤ Mg * Mγ' := mul_le_mul (hMg' _ ⟨t, ht, rfl⟩) (hMγ'' t ht) (norm_nonneg _) hMg_nn
      _ ≤ Mg * Mγ' + 1 := by linarith
  · simp only [norm_zero]
    linarith [mul_nonneg hMg_nn hMγ_nn]

/-- PV exists for continuous integrands on C¹ curves. -/
theorem cauchyPrincipalValueExists_of_continuous (g : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (hab : a < b) (hg : ContinuousOn g (γ '' Icc a b)) (hγ : ContinuousOn γ (Icc a b))
    (hγ' : ContinuousOn (deriv γ) (Icc a b)) : CauchyPrincipalValueExists' g γ a b z₀ := by
  obtain ⟨M, hM_pos, h_bound⟩ :=
    pv_uniform_bound_of_continuous_aux g γ a b z₀ hab hg hγ hγ'
  refine cauchyPrincipalValue_of_dominated g γ a b z₀ hab M hM_pos h_bound ?_ ?_
  · refine Eventually.of_forall fun t => ?_
    by_cases h : γ t = z₀
    · exact ⟨0, Tendsto.congr' (Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Ioi 0, self_mem_nhdsWithin, fun ε hε => by
          simp [cauchyPrincipalValueIntegrand', h, not_lt.mpr (mem_Ioi.mp hε).le]⟩)
        tendsto_const_nhds⟩
    · exact ⟨g (γ t) * deriv γ t, Tendsto.congr' (Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Ioo 0 ‖γ t - z₀‖, Ioo_mem_nhdsGT (norm_pos_iff.mpr (sub_ne_zero.mpr h)),
          fun ε hε => by simp [cauchyPrincipalValueIntegrand', hε.2]⟩)
        tendsto_const_nhds⟩
  · filter_upwards [self_mem_nhdsWithin] with ε _
    exact (aEStronglyMeasurable_pv_integrand (hg.mono diff_subset) hγ hγ').mono_measure
      (Measure.restrict_mono (by rw [uIoc_of_le hab.le]; exact Ioc_subset_Icc_self) le_rfl)

/-- PV exists for singular 1/(z-z₀) integrands on C¹ immersions. -/
theorem cauchyPrincipalValueExists_of_singular_inv (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (h_crossing_cauchy : (∃ t ∈ Icc γ.a γ.b, γ.toFun t = z₀) →
      Cauchy (Filter.map (fun ε => ∫ t in γ.a..γ.b,
        if ε < ‖γ.toFun t - z₀‖ then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0)
        (𝓝[>] 0))) :
    CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun γ.a γ.b z₀ := by
  by_cases h_cross : ∃ t ∈ Icc γ.a γ.b, γ.toFun t = z₀
  · exact CompleteSpace.complete (h_crossing_cauchy h_cross)
  · push Not at h_cross
    have h_cont : ContinuousOn (fun t => ‖γ.toFun t - z₀‖) (Icc γ.a γ.b) :=
      (γ.continuous_toFun.sub continuousOn_const).norm
    obtain ⟨t₀, ht₀, ht₀_min⟩ :=
      isCompact_Icc.exists_isMinOn ⟨γ.a, left_mem_Icc.mpr γ.hab.le⟩ h_cont
    have hδ : 0 < ‖γ.toFun t₀ - z₀‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (h_cross t₀ ht₀))
    refine ⟨∫ t in γ.a..γ.b, (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t,
      tendsto_const_nhds.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    refine (intervalIntegral.integral_congr fun t ht => ?_).symm
    rw [uIcc_of_le γ.hab.le] at ht
    simp only [show ε < ‖γ.toFun t - z₀‖ from
      hε.2.trans_le (Filter.eventually_principal.mp ht₀_min t ht), ite_true]

/-- Uniform avoidance on compact sets. -/
theorem uniform_avoidance_on_compact (γ : ℝ → ℂ) (K : Set ℝ) (z₀ : ℂ) (hK_compact : IsCompact K)
    (hK_nonempty : K.Nonempty) (hγ_cont : ContinuousOn γ K) (h_avoid : ∀ t ∈ K, γ t ≠ z₀) :
    ∃ δ > 0, ∀ t ∈ K, δ ≤ ‖γ t - z₀‖ := by
  obtain ⟨t₀, ht₀, h_min⟩ :=
    hK_compact.exists_isMinOn hK_nonempty (hγ_cont.sub continuousOn_const).norm
  exact ⟨‖γ t₀ - z₀‖, norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoid t₀ ht₀)),
    Filter.eventually_principal.mp h_min⟩

end
