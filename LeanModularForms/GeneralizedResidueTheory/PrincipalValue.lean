/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Basic

/-!
# Cauchy Principal Value Theory

Theory of Cauchy principal value integrals for piecewise C¹ contour integration.
The principal value approach allows contours to pass through singularities.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

theorem cauchyPrincipalValueIntegrand_add'
    (f g : ℂ → ℂ) (γ : ℝ → ℂ) (z₀ : ℂ) (ε : ℝ) (t : ℝ) :
    cauchyPrincipalValueIntegrand' (f + g) γ z₀ ε t =
    cauchyPrincipalValueIntegrand' f γ z₀ ε t +
    cauchyPrincipalValueIntegrand' g γ z₀ ε t := by
  simp only [cauchyPrincipalValueIntegrand', Pi.add_apply]
  split_ifs <;> ring

theorem cauchyPrincipalValueIntegrand_smul'
    (c : ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (z₀ : ℂ) (ε : ℝ) (t : ℝ) :
    cauchyPrincipalValueIntegrand' (fun z => c * f z) γ z₀ ε t =
    c * cauchyPrincipalValueIntegrand' f γ z₀ ε t := by
  simp only [cauchyPrincipalValueIntegrand']
  split_ifs <;> ring

theorem cauchyPrincipalValueIntegrand_bounded
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (ε : ℝ)
    (_hε : 0 < ε)
    (hf_cont : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    ∃ M : ℝ, ∀ t ∈ Icc a b,
      ‖cauchyPrincipalValueIntegrand' f γ z₀ ε t‖ ≤ M := by
  by_cases h_empty :
      (γ '' Icc a b \ Metric.ball z₀ ε).Nonempty
  · have hγ_im_compact : IsCompact (γ '' Icc a b) :=
      isCompact_Icc.image_of_continuousOn hγ_cont
    have hcompact_domain :
        IsCompact (γ '' Icc a b \ Metric.ball z₀ ε) :=
      hγ_im_compact.inter_right Metric.isOpen_ball.isClosed_compl
    obtain ⟨Mf, hMf⟩ :=
      hcompact_domain.exists_bound_of_continuousOn hf_cont.norm
    obtain ⟨Mγ, hMγ⟩ :=
      isCompact_Icc.exists_bound_of_continuousOn hγ'_cont.norm
    have hMf' : ∀ x ∈ γ '' Icc a b \ Metric.ball z₀ ε, ‖f x‖ ≤ Mf :=
      fun x hx => by
        have := hMf x hx; simp only [Real.norm_eq_abs, abs_norm] at this; exact this
    have hMγ' : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ Mγ := fun t ht => by
      have := hMγ t ht; simp only [Real.norm_eq_abs, abs_norm] at this; exact this
    refine ⟨Mf * Mγ + 1, fun t ht => ?_⟩
    unfold cauchyPrincipalValueIntegrand'; split_ifs with h
    · have hγt_in : γ t ∈ γ '' Icc a b \ Metric.ball z₀ ε :=
        ⟨⟨t, ht, rfl⟩, by simp only [Metric.mem_ball, not_lt]; exact h.le⟩
      calc ‖f (γ t) * deriv γ t‖
          = ‖f (γ t)‖ * ‖deriv γ t‖ := norm_mul _ _
        _ ≤ Mf * Mγ := mul_le_mul (hMf' _ hγt_in) (hMγ' t ht)
            (norm_nonneg _) (le_trans (norm_nonneg _) (hMf' _ hγt_in))
        _ ≤ Mf * Mγ + 1 := by linarith
    · simp only [norm_zero]
      exact add_nonneg (mul_nonneg
        (le_trans (norm_nonneg _) (hMf' _ h_empty.some_mem))
        (by obtain ⟨_, ⟨t', ht', _⟩, _⟩ := h_empty
            exact le_trans (norm_nonneg _) (hMγ' _ ht'))) (by norm_num)
  · exact ⟨0, fun t ht => by
      unfold cauchyPrincipalValueIntegrand'
      split_ifs with h
      · exact absurd ⟨γ t, ⟨t, ht, rfl⟩, by
          simp only [Metric.mem_ball, not_lt]
          exact le_of_lt h⟩ h_empty
      · simp⟩

lemma cauchyPrincipalValueIntegrand_eq_indicator
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (z₀ : ℂ) (ε : ℝ) :
    cauchyPrincipalValueIntegrand' f γ z₀ ε =
      {t | ε < ‖γ t - z₀‖}.indicator
        (fun t => f (γ t) * deriv γ t) := by
  ext t
  unfold cauchyPrincipalValueIntegrand'
  simp only [indicator, mem_setOf_eq]

lemma measurableSet_pv_support (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (ε : ℝ) (hγ_cont : ContinuousOn γ (Icc a b)) :
    MeasurableSet ({t | ε < ‖γ t - z₀‖} ∩ Icc a b) := by
  have h_norm_cont : ContinuousOn (fun t => ‖γ t - z₀‖) (Icc a b) :=
    (hγ_cont.sub continuousOn_const).norm
  have h_open_sub :
      IsOpen ((Icc a b).restrict (fun t => ‖γ t - z₀‖) ⁻¹' Ioi ε) :=
    isOpen_Ioi.preimage h_norm_cont.restrict
  rw [isOpen_induced_iff] at h_open_sub
  obtain ⟨U, hU_open, hU_eq⟩ := h_open_sub
  have h_eq : {t | ε < ‖γ t - z₀‖} ∩ Icc a b = U ∩ Icc a b := by
    ext x; constructor
    · intro ⟨hx_far, hx_Icc⟩
      exact ⟨by
        have : (⟨x, hx_Icc⟩ : ↑(Icc a b)) ∈
            (Icc a b).restrict (fun t => ‖γ t - z₀‖) ⁻¹' Ioi ε := by
          simp only [mem_preimage, restrict_apply, mem_Ioi]; exact hx_far
        rwa [← hU_eq] at this, hx_Icc⟩
    · intro ⟨hx_U, hx_Icc⟩
      exact ⟨by
        have : (⟨x, hx_Icc⟩ : ↑(Icc a b)) ∈ Subtype.val ⁻¹' U := hx_U
        rw [hU_eq] at this
        simp only [mem_preimage, restrict_apply, mem_Ioi] at this
        exact this, hx_Icc⟩
  rw [h_eq]
  exact hU_open.measurableSet.inter isClosed_Icc.measurableSet

lemma continuousOn_pv_base (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (a b : ℝ) (z₀ : ℂ) (ε : ℝ)
    (hf_cont : ContinuousOn f
      (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    ContinuousOn (fun t => f (γ t) * deriv γ t)
      ({t | ε < ‖γ t - z₀‖} ∩ Icc a b) := by
  intro t ⟨ht_far, ht_Icc⟩
  have hγt_in : γ t ∈ γ '' Icc a b \ Metric.ball z₀ ε :=
    ⟨mem_image_of_mem γ ht_Icc, by
      simp only [Metric.mem_ball, not_lt]; exact le_of_lt ht_far⟩
  have h_maps :
      MapsTo γ ({t | ε < ‖γ t - z₀‖} ∩ Icc a b)
        (γ '' Icc a b \ Metric.ball z₀ ε) := by
    intro s ⟨hs_far, hs_Icc⟩
    exact ⟨mem_image_of_mem γ hs_Icc, by
      simp only [Metric.mem_ball, not_lt]; exact le_of_lt hs_far⟩
  have hfγ_at : ContinuousWithinAt (f ∘ γ)
      ({t | ε < ‖γ t - z₀‖} ∩ Icc a b) t :=
    ContinuousWithinAt.comp (hf_cont _ hγt_in)
      ((hγ_cont t ht_Icc).mono inter_subset_right) h_maps
  exact hfγ_at.mul ((hγ'_cont t ht_Icc).mono inter_subset_right)

theorem limUnder_eventually_eq {α : Type*}
    [TopologicalSpace α] [Nonempty α]
    {f g : ℝ → α} {l : Filter ℝ} [l.NeBot]
    (h : ∀ᶠ x in l, f x = g x) :
    limUnder l f = limUnder l g := by
  unfold limUnder; congr 1; exact Filter.map_congr h

theorem limUnder_eventually_eq'
    {f g : ℝ → ℂ}
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε = g ε) :
    limUnder (𝓝[>] (0 : ℝ)) f =
    limUnder (𝓝[>] (0 : ℝ)) g :=
  limUnder_eventually_eq h

private theorem aEStronglyMeasurable_pv_integrand
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {ε : ℝ}
    (hf : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ : ContinuousOn γ (Icc a b))
    (hγ' : ContinuousOn (deriv γ) (Icc a b)) :
    AEStronglyMeasurable
      (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t
        else 0) (volume.restrict (Icc a b)) := by
  let S := {t | ε < ‖γ t - z₀‖}
  have hS_meas : MeasurableSet (S ∩ Icc a b) :=
    measurableSet_pv_support γ a b z₀ ε hγ
  have h_cont : ContinuousOn (fun t => f (γ t) * deriv γ t)
      (S ∩ Icc a b) :=
    continuousOn_pv_base f γ a b z₀ ε hf hγ hγ'
  have h_base_meas : AEStronglyMeasurable
      (fun t => f (γ t) * deriv γ t)
      (volume.restrict (S ∩ Icc a b)) :=
    h_cont.aestronglyMeasurable hS_meas
  have h_piecewise := AEStronglyMeasurable.piecewise
    hS_meas h_base_meas
    (aestronglyMeasurable_const :
      AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
        (volume.restrict (S ∩ Icc a b)ᶜ))
  have h_eq : (fun t => if ε < ‖γ t - z₀‖
      then f (γ t) * deriv γ t else 0) =ᵐ[
        volume.restrict (Icc a b)]
      (S ∩ Icc a b).piecewise
        (fun t => f (γ t) * deriv γ t) (fun _ => 0) := by
    filter_upwards [ae_restrict_mem
      isClosed_Icc.measurableSet] with t ht
    simp only [piecewise]
    by_cases ht_S : t ∈ S
    · simp only [show t ∈ S ∩ Icc a b from ⟨ht_S, ht⟩,
        ↓reduceIte, show ε < ‖γ t - z₀‖ from ht_S, ↓reduceIte]
    · simp only [show t ∉ S ∩ Icc a b from fun h => ht_S h.1,
        ↓reduceIte, show ¬(ε < ‖γ t - z₀‖) from ht_S,
        ↓reduceIte]
  exact (h_piecewise.mono_measure
    Measure.restrict_le_self).congr h_eq.symm

theorem cauchyPrincipalValueIntegrand_integrable
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (ε : ℝ) (hε : 0 < ε) (hab : a < b)
    (hf_cont : ContinuousOn f
      (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    IntervalIntegrable
      (cauchyPrincipalValueIntegrand' f γ z₀ ε) volume a b := by
  obtain ⟨M, hM⟩ := cauchyPrincipalValueIntegrand_bounded
    f γ a b z₀ ε hε hf_cont hγ_cont hγ'_cont
  have h_eq : cauchyPrincipalValueIntegrand' f γ z₀ ε =
      fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t
        else 0 := by ext t; rfl
  rw [h_eq, intervalIntegrable_iff_integrableOn_Ioc_of_le
    (le_of_lt hab)]
  apply IntegrableOn.mono_set
  · apply IntegrableOn.of_bound measure_Icc_lt_top
      (aEStronglyMeasurable_pv_integrand hf_cont hγ_cont
        hγ'_cont)
      (max M 0)
    filter_upwards [ae_restrict_mem
      isClosed_Icc.measurableSet] with x hx
    calc ‖if ε < ‖γ x - z₀‖ then f (γ x) * deriv γ x
        else 0‖
        ≤ M := by
          simp only [cauchyPrincipalValueIntegrand'] at hM
          exact hM x hx
      _ ≤ max M 0 := le_max_left M 0
  · exact Ioc_subset_Icc_self

/-- Dominated convergence for principal value integrals. -/
theorem cauchyPrincipalValue_of_dominated
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (hab : a < b) (M : ℝ) (_hM : 0 < M)
    (h_bound : ∀ ε > 0, ∀ t ∈ Icc a b,
      ‖cauchyPrincipalValueIntegrand' f γ z₀ ε t‖ ≤ M)
    (h_ae_limit : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∃ L, Tendsto
        (fun ε => cauchyPrincipalValueIntegrand' f γ z₀ ε t)
        (𝓝[>] 0) (𝓝 L))
    (hF_meas : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable
        (cauchyPrincipalValueIntegrand' f γ z₀ ε)
        (volume.restrict (uIoc a b))) :
    CauchyPrincipalValueExists' f γ a b z₀ := by
  have hab' := le_of_lt hab
  have h_bound_ae : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ t ∂volume,
      t ∈ uIoc a b →
        ‖cauchyPrincipalValueIntegrand' f γ z₀ ε t‖ ≤ M := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply Eventually.of_forall
    intro t ht
    exact h_bound ε hε t
      (Ioc_subset_Icc_self (uIoc_of_le hab' ▸ ht))
  have h_ae_unr : ∀ᵐ t ∂volume, t ∈ Icc a b →
      ∃ L, Tendsto
        (fun ε => cauchyPrincipalValueIntegrand' f γ z₀ ε t)
        (𝓝[>] 0) (𝓝 L) := by
    rwa [ae_restrict_iff' isClosed_Icc.measurableSet]
      at h_ae_limit
  have h_limit_ae : ∀ᵐ t ∂volume, t ∈ uIoc a b →
      ∃ L, Tendsto
        (fun ε => cauchyPrincipalValueIntegrand' f γ z₀ ε t)
        (𝓝[>] 0) (𝓝 L) := by
    filter_upwards [h_ae_unr] with t ht ht_mem
    exact ht (Ioc_subset_Icc_self (uIoc_of_le hab' ▸ ht_mem))
  let g : ℝ → ℂ := fun t => _root_.limUnder (𝓝[>] (0 : ℝ))
    (fun ε => cauchyPrincipalValueIntegrand' f γ z₀ ε t)
  have h_lim_conv : ∀ᵐ t ∂volume, t ∈ uIoc a b →
      Tendsto
        (fun ε => cauchyPrincipalValueIntegrand' f γ z₀ ε t)
        (𝓝[>] 0) (𝓝 (g t)) := by
    filter_upwards [h_limit_ae] with t ht ht_mem
    obtain ⟨L, hL⟩ := ht ht_mem
    rwa [show g t = L from Tendsto.limUnder_eq hL]
  exact ⟨∫ t in a..b, g t,
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M) hF_meas h_bound_ae
      intervalIntegrable_const h_lim_conv⟩

private theorem pv_uniform_bound_of_continuous_aux
    (g : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hg : ContinuousOn g (γ '' Icc a b))
    (hγ : ContinuousOn γ (Icc a b))
    (hγ' : ContinuousOn (deriv γ) (Icc a b)) :
    ∃ M > 0, ∀ ε > 0, ∀ t ∈ Icc a b,
      ‖cauchyPrincipalValueIntegrand' g γ z₀ ε t‖ ≤ M := by
  obtain ⟨Mg, hMg⟩ :=
    (isCompact_Icc.image_of_continuousOn hγ).exists_bound_of_continuousOn hg.norm
  obtain ⟨Mγ', hMγ'⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hγ'.norm
  have hMg' : ∀ z ∈ γ '' Icc a b, ‖g z‖ ≤ Mg := fun z hz => by
    have := hMg z hz; simp only [Real.norm_eq_abs, abs_norm] at this; exact this
  have hMγ'' : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ Mγ' := fun t ht => by
    have := hMγ' t ht; simp only [Real.norm_eq_abs, abs_norm] at this; exact this
  have hMg_nn : (0 : ℝ) ≤ Mg :=
    le_trans (norm_nonneg _) (hMg' _ ⟨a, left_mem_Icc.mpr hab.le, rfl⟩)
  have hMγ_nn : (0 : ℝ) ≤ Mγ' :=
    le_trans (norm_nonneg _) (hMγ'' a (left_mem_Icc.mpr hab.le))
  refine ⟨Mg * Mγ' + 1, by linarith [mul_nonneg hMg_nn hMγ_nn],
    fun ε _ t ht => ?_⟩
  unfold cauchyPrincipalValueIntegrand'; split_ifs with h
  · calc ‖g (γ t) * deriv γ t‖
        = ‖g (γ t)‖ * ‖deriv γ t‖ := norm_mul _ _
      _ ≤ Mg * Mγ' := mul_le_mul (hMg' _ ⟨t, ht, rfl⟩) (hMγ'' t ht)
          (norm_nonneg _) hMg_nn
      _ ≤ Mg * Mγ' + 1 := by linarith
  · simp only [norm_zero]; linarith [mul_nonneg hMg_nn hMγ_nn]

/-- PV exists for continuous integrands on C¹ curves. -/
theorem cauchyPrincipalValueExists_of_continuous
    (g : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hg : ContinuousOn g (γ '' Icc a b))
    (hγ : ContinuousOn γ (Icc a b))
    (hγ' : ContinuousOn (deriv γ) (Icc a b)) :
    CauchyPrincipalValueExists' g γ a b z₀ := by
  obtain ⟨M, hM_pos, h_bound⟩ :=
    pv_uniform_bound_of_continuous_aux g γ a b z₀ hab hg hγ hγ'
  refine cauchyPrincipalValue_of_dominated g γ a b z₀ hab M hM_pos
    h_bound ?_ ?_
  · apply Eventually.of_forall; intro t
    by_cases h : γ t = z₀
    · exact ⟨0, Tendsto.congr' (by
        rw [EventuallyEq, eventually_iff_exists_mem]
        exact ⟨Ioi 0, self_mem_nhdsWithin, fun ε hε => by
          simp only [cauchyPrincipalValueIntegrand', h, sub_self,
            norm_zero, not_lt.mpr (le_of_lt (mem_Ioi.mp hε)),
            ite_false]⟩) tendsto_const_nhds⟩
    · exact ⟨g (γ t) * deriv γ t, Tendsto.congr' (by
        rw [EventuallyEq, eventually_iff_exists_mem]
        exact ⟨Ioo 0 ‖γ t - z₀‖,
          Ioo_mem_nhdsGT (norm_pos_iff.mpr (sub_ne_zero.mpr h)),
          fun ε hε => by
            simp only [cauchyPrincipalValueIntegrand',
              hε.2, ite_true]⟩) tendsto_const_nhds⟩
  · filter_upwards [self_mem_nhdsWithin] with ε _
    have h_eq : cauchyPrincipalValueIntegrand' g γ z₀ ε =
        fun t => if ε < ‖γ t - z₀‖ then g (γ t) * deriv γ t
          else 0 := funext fun _ => rfl
    rw [h_eq]
    exact (aEStronglyMeasurable_pv_integrand
      (hg.mono diff_subset) hγ hγ').mono_measure
      (Measure.restrict_mono
        (by rw [uIoc_of_le hab.le]; exact Ioc_subset_Icc_self)
        le_rfl)

/-- PV is additive when both limits exist. -/
theorem cauchyPrincipalValue_add'
    (f g : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (hf : CauchyPrincipalValueExists' f γ a b z₀)
    (hg : CauchyPrincipalValueExists' g γ a b z₀)
    (hf_int : ∀ᶠ ε in 𝓝[>] 0, IntervalIntegrable
      (cauchyPrincipalValueIntegrand' f γ z₀ ε) volume a b)
    (hg_int : ∀ᶠ ε in 𝓝[>] 0, IntervalIntegrable
      (cauchyPrincipalValueIntegrand' g γ z₀ ε) volume a b) :
    cauchyPrincipalValue' (f + g) γ a b z₀ =
    cauchyPrincipalValue' f γ a b z₀ +
      cauchyPrincipalValue' g γ a b z₀ := by
  obtain ⟨Lf, hLf⟩ := hf
  obtain ⟨Lg, hLg⟩ := hg
  have h_sum_tendsto : Tendsto (fun ε =>
      ∫ t in a..b, cauchyPrincipalValueIntegrand'
        (f + g) γ z₀ ε t)
      (𝓝[>] 0) (𝓝 (Lf + Lg)) := by
    refine Tendsto.congr' ?_ (hLf.add hLg)
    filter_upwards [hf_int, hg_int] with ε hfε hgε
    simp_rw [cauchyPrincipalValueIntegrand_add']
    exact (intervalIntegral.integral_add hfε hgε).symm
  have hLf' : Tendsto (fun ε => ∫ t in a..b,
      cauchyPrincipalValueIntegrand' f γ z₀ ε t)
      (𝓝[>] 0) (𝓝 Lf) := hLf
  have hLg' : Tendsto (fun ε => ∫ t in a..b,
      cauchyPrincipalValueIntegrand' g γ z₀ ε t)
      (𝓝[>] 0) (𝓝 Lg) := hLg
  change limUnder (𝓝[>] 0)
      (fun ε => ∫ t in a..b,
        cauchyPrincipalValueIntegrand' (f + g) γ z₀ ε t) =
    limUnder (𝓝[>] 0)
      (fun ε => ∫ t in a..b,
        cauchyPrincipalValueIntegrand' f γ z₀ ε t) +
    limUnder (𝓝[>] 0)
      (fun ε => ∫ t in a..b,
        cauchyPrincipalValueIntegrand' g γ z₀ ε t)
  rw [Tendsto.limUnder_eq h_sum_tendsto,
    Tendsto.limUnder_eq hLf', Tendsto.limUnder_eq hLg']

/-- PV is homogeneous. -/
theorem cauchyPrincipalValue_smul'
    (c : ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (hf : CauchyPrincipalValueExists' f γ a b z₀) :
    cauchyPrincipalValue' (fun z => c * f z) γ a b z₀ =
    c * cauchyPrincipalValue' f γ a b z₀ := by
  obtain ⟨Lf, hLf⟩ := hf
  have h_tendsto : Tendsto (fun ε =>
      ∫ t in a..b, cauchyPrincipalValueIntegrand'
        (fun z => c * f z) γ z₀ ε t)
      (𝓝[>] 0) (𝓝 (c * Lf)) := by
    simp_rw [cauchyPrincipalValueIntegrand_smul',
      intervalIntegral.integral_const_mul]
    exact hLf.const_mul c
  have hLf' : Tendsto (fun ε => ∫ t in a..b,
      cauchyPrincipalValueIntegrand' f γ z₀ ε t)
      (𝓝[>] 0) (𝓝 Lf) := hLf
  change limUnder (𝓝[>] 0)
      (fun ε => ∫ t in a..b,
        cauchyPrincipalValueIntegrand'
          (fun z => c * f z) γ z₀ ε t) =
    c * limUnder (𝓝[>] 0)
      (fun ε => ∫ t in a..b,
        cauchyPrincipalValueIntegrand' f γ z₀ ε t)
  rw [Tendsto.limUnder_eq h_tendsto,
    Tendsto.limUnder_eq hLf']

/-- PV exists for singular 1/(z-z₀) integrands on C¹ immersions. -/
theorem cauchyPrincipalValueExists_of_singular_inv
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (h_crossing_cauchy :
      (∃ t ∈ Icc γ.a γ.b, γ.toFun t = z₀) →
        Cauchy (Filter.map (fun ε =>
          ∫ t in γ.a..γ.b,
            if ε < ‖γ.toFun t - z₀‖
            then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t
            else 0) (𝓝[>] 0))) :
    CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹)
      γ.toFun γ.a γ.b z₀ := by
  by_cases h_cross : ∃ t ∈ Icc γ.a γ.b, γ.toFun t = z₀
  · exact CompleteSpace.complete (h_crossing_cauchy h_cross)
  · push_neg at h_cross
    have h_cont : ContinuousOn
        (fun t => ‖γ.toFun t - z₀‖) (Icc γ.a γ.b) :=
      (γ.continuous_toFun.sub continuousOn_const).norm
    obtain ⟨t₀, ht₀, ht₀_min⟩ :=
      IsCompact.exists_isMinOn isCompact_Icc
        ⟨γ.a, left_mem_Icc.mpr γ.hab.le⟩ h_cont
    have hδ : 0 < ‖γ.toFun t₀ - z₀‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (h_cross t₀ ht₀))
    have hδ_le : ∀ t ∈ Icc γ.a γ.b,
        ‖γ.toFun t₀ - z₀‖ ≤ ‖γ.toFun t - z₀‖ :=
      Filter.eventually_principal.mp ht₀_min
    refine ⟨∫ t in γ.a..γ.b,
        (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t, ?_⟩
    exact tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
      symm
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le γ.hab.le] at ht
      simp only [gt_iff_lt, show ε < ‖γ.toFun t - z₀‖ from
        lt_of_lt_of_le hε.2 (hδ_le t ht), ite_true])

/-- Homotopy invariance of PV integrals. -/
theorem homotopy_pv_integral_eq'
    (f : ℂ → ℂ) (Γ γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (_hab : a < b)
    (_H : ℝ × ℝ → ℂ) (_hH_cont : Continuous _H)
    (_hH0 : ∀ t ∈ Icc a b, _H (t, 0) = Γ t)
    (_hH1 : ∀ t ∈ Icc a b, _H (t, 1) = γ t)
    (_hH_endpoints :
      ∀ s ∈ Icc (0:ℝ) 1, _H (a, s) = z₀ ∧ _H (b, s) = z₀)
    (_hH_nonzero :
      ∀ t ∈ Ioo a b, ∀ s ∈ Icc (0:ℝ) 1, _H (t, s) ≠ z₀)
    (h_cutoff_eq : ∀ ε > 0,
      (∫ t in a..b, if ‖Γ t - z₀‖ > ε
        then f (Γ t) * deriv Γ t else 0) =
      (∫ t in a..b, if ‖γ t - z₀‖ > ε
        then f (γ t) * deriv γ t else 0)) :
    cauchyPrincipalValue' f Γ a b z₀ =
    cauchyPrincipalValue' f γ a b z₀ := by
  unfold cauchyPrincipalValue'
  exact limUnder_eventually_eq (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact h_cutoff_eq ε (mem_Ioi.mp hε))

/-- Homotopy invariance of winding numbers. -/
theorem windingNumber_homotopy_invariant'
    (Γ γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (H : ℝ × ℝ → ℂ) (hH_cont : Continuous H)
    (hH0 : ∀ t ∈ Icc a b, H (t, 0) = Γ t)
    (hH1 : ∀ t ∈ Icc a b, H (t, 1) = γ t)
    (hH_endpoints :
      ∀ s ∈ Icc (0:ℝ) 1, H (a, s) = z₀ ∧ H (b, s) = z₀)
    (hH_nonzero :
      ∀ t ∈ Ioo a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀)
    (h_cutoff_eq : ∀ ε > 0,
      (∫ t in a..b, if ε < ‖(Γ t - z₀) - 0‖
        then (Γ t - z₀)⁻¹ * deriv (fun t => Γ t - z₀) t
        else 0) =
      (∫ t in a..b, if ε < ‖(γ t - z₀) - 0‖
        then (γ t - z₀)⁻¹ * deriv (fun t => γ t - z₀) t
        else 0)) :
    generalizedWindingNumber' Γ a b z₀ =
    generalizedWindingNumber' γ a b z₀ := by
  unfold generalizedWindingNumber'
  congr 1
  exact homotopy_pv_integral_eq' (·⁻¹)
    (fun t => Γ t - z₀) (fun t => γ t - z₀) a b 0 hab
    (fun p => H p - z₀)
    (hH_cont.sub continuous_const)
    (fun t ht => by simp only [hH0 t ht])
    (fun t ht => by simp only [hH1 t ht])
    (fun s hs => by
      obtain ⟨h1, h2⟩ := hH_endpoints s hs
      exact ⟨by simp [h1], by simp [h2]⟩)
    (fun t ht s hs =>
      sub_ne_zero.mpr (hH_nonzero t ht s hs))
    h_cutoff_eq

/-- PV exists for c/(z-z₀) integrands on C¹ immersions. -/
theorem cauchyPrincipalValueExists_of_singular_pole
    (γ : PiecewiseC1Immersion) (z₀ c : ℂ)
    (h_crossing_cauchy :
      (∃ t ∈ Icc γ.a γ.b, γ.toFun t = z₀) →
        Cauchy (Filter.map (fun ε =>
          ∫ t in γ.a..γ.b,
            if ε < ‖γ.toFun t - z₀‖
            then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t
            else 0) (𝓝[>] 0))) :
    CauchyPrincipalValueExists'
      (fun z => c / (z - z₀)) γ.toFun γ.a γ.b z₀ := by
  have h_eq : (fun z => c / (z - z₀)) =
      (fun z => c * (z - z₀)⁻¹) := by ext z; ring
  obtain ⟨L, hL⟩ := cauchyPrincipalValueExists_of_singular_inv
    γ z₀ h_crossing_cauchy
  refine ⟨c * L, ?_⟩
  have h_eq' : ∀ ε, (fun t =>
      if ε < ‖γ.toFun t - z₀‖
      then c * (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t
      else 0) = (fun t => c *
        (if ε < ‖γ.toFun t - z₀‖
        then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t
        else 0)) := by
    intro ε; ext t; split_ifs <;> ring
  have h_tendsto : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      if ε < ‖γ.toFun t - z₀‖
      then c * (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t
      else 0) (𝓝[>] 0) (𝓝 (c * L)) := by
    simp_rw [h_eq']
    simp_rw [intervalIntegral.integral_const_mul]
    exact Tendsto.const_mul c hL
  have h_eq'' : ∀ ε, (∫ t in γ.a..γ.b,
      if ε < ‖γ.toFun t - z₀‖
      then c / (γ.toFun t - z₀) * deriv γ.toFun t
      else 0) = (∫ t in γ.a..γ.b,
      if ε < ‖γ.toFun t - z₀‖
      then c * (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t
      else 0) := by
    intro ε
    apply intervalIntegral.integral_congr
    intro t _; simp only []; split_ifs <;> ring
  simp_rw [h_eq'']; exact h_tendsto

/-- Uniform avoidance on compact sets. -/
theorem uniform_avoidance_on_compact
    (γ : ℝ → ℂ) (K : Set ℝ) (z₀ : ℂ)
    (hK_compact : IsCompact K) (hK_nonempty : K.Nonempty)
    (hγ_cont : ContinuousOn γ K)
    (h_avoid : ∀ t ∈ K, γ t ≠ z₀) :
    ∃ δ > 0, ∀ t ∈ K, δ ≤ ‖γ t - z₀‖ := by
  obtain ⟨t₀, ht₀, h_min⟩ := hK_compact.exists_isMinOn
    hK_nonempty (hγ_cont.sub continuousOn_const).norm
  exact ⟨‖γ t₀ - z₀‖,
    norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoid t₀ ht₀)),
    Filter.eventually_principal.mp h_min⟩

/-- For ε below the avoidance bound, the cutoff is trivial. -/
theorem epsilon_cutoff_trivial_on_compact
    (γ : ℝ → ℂ) (K : Set ℝ) (z₀ : ℂ) (ε δ : ℝ)
    (hε : ε < δ) (h_avoid : ∀ t ∈ K, δ ≤ ‖γ t - z₀‖) :
    ∀ t ∈ K, ε < ‖γ t - z₀‖ :=
  fun t ht => lt_of_lt_of_le hε (h_avoid t ht)

private theorem pv_piecewise_measurable
    (g : ℂ → ℂ) (γ : PiecewiseC1Curve) (z₀ : ℂ)
    (h_integrable : IntervalIntegrable
      (fun t => g (γ.toFun t) * deriv γ.toFun t)
      volume γ.a γ.b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun t => if ε < ‖γ.toFun t - z₀‖
        then g (γ.toFun t) * deriv γ.toFun t else 0)
      (volume.restrict (Ι γ.a γ.b)) := by
  filter_upwards [self_mem_nhdsWithin] with ε _
  rw [show Ι γ.a γ.b = Ioc γ.a γ.b from uIoc_of_le γ.hab.le]
  exact (h_integrable.aestronglyMeasurable.indicator
    (measurableSet_pv_support γ.toFun γ.a γ.b z₀ ε
      γ.continuous_toFun)).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    by_cases h : ε < ‖γ.toFun t - z₀‖
    · rw [indicator_of_mem (show t ∈ {t | ε < ‖γ.toFun t - z₀‖} ∩
        Icc γ.a γ.b from ⟨h, Ioc_subset_Icc_self ht⟩), if_pos h]
    · rw [indicator_of_notMem (fun hmem => h hmem.1), if_neg h])

private theorem pv_piecewise_bound (γ : PiecewiseC1Curve) (z₀ : ℂ)
    (g : ℂ → ℂ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b →
      ‖(if ε < ‖γ.toFun t - z₀‖
        then g (γ.toFun t) * deriv γ.toFun t else 0)‖ ≤
      ‖g (γ.toFun t) * deriv γ.toFun t‖ := by
  filter_upwards [self_mem_nhdsWithin] with ε _
  exact Eventually.of_forall fun t _ => by
    split_ifs with h
    · exact le_refl _
    · simp only [norm_zero]; exact norm_nonneg _

private theorem pv_piecewise_pointwise
    (γ : PiecewiseC1Curve) (z₀ : ℂ) (g : ℂ → ℂ)
    (h_finite_preimage :
      Set.Finite {t ∈ Icc γ.a γ.b | γ.toFun t = z₀}) :
    ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b →
      Tendsto (fun ε => if ε < ‖γ.toFun t - z₀‖
        then g (γ.toFun t) * deriv γ.toFun t else 0)
        (𝓝[>] 0) (𝓝 (g (γ.toFun t) * deriv γ.toFun t)) := by
  filter_upwards [h_finite_preimage.countable.ae_notMem _]
      with t ht ht_uIoc
  have h_ne : γ.toFun t ≠ z₀ := fun heq =>
    ht ⟨Ioc_subset_Icc_self (uIoc_of_le γ.hab.le ▸ ht_uIoc), heq⟩
  exact tendsto_const_nhds.congr' (by
    filter_upwards [Ioo_mem_nhdsGT
      (norm_pos_iff.mpr (sub_ne_zero.mpr h_ne))] with ε hε
    simp only [gt_iff_lt, hε.2, ite_true])

/-- PV exists for continuous integrands when the full integrand is integrable
and the preimage of z₀ is finite. -/
theorem cauchyPrincipalValueExists_of_continuous_piecewise
    (g : ℂ → ℂ) (γ : PiecewiseC1Curve) (z₀ : ℂ)
    (h_integrable : IntervalIntegrable
      (fun t => g (γ.toFun t) * deriv γ.toFun t)
      volume γ.a γ.b)
    (h_finite_preimage :
      Set.Finite {t ∈ Icc γ.a γ.b | γ.toFun t = z₀}) :
    CauchyPrincipalValueExists' g γ.toFun γ.a γ.b z₀ := by
  by_cases h_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀
  · obtain ⟨δ, hδ, hδ_le⟩ := uniform_avoidance_on_compact
      γ.toFun (Icc γ.a γ.b) z₀ isCompact_Icc
      ⟨γ.a, left_mem_Icc.mpr γ.hab.le⟩
      γ.continuous_toFun h_avoids
    refine ⟨∫ t in γ.a..γ.b,
        g (γ.toFun t) * deriv γ.toFun t, ?_⟩
    exact tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
      symm; apply intervalIntegral.integral_congr
      intro t ht; rw [uIcc_of_le γ.hab.le] at ht
      simp only [gt_iff_lt, lt_of_lt_of_le hε.2 (hδ_le t ht), ite_true])
  · exact ⟨∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t,
      intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun t => ‖g (γ.toFun t) * deriv γ.toFun t‖)
        (pv_piecewise_measurable g γ z₀ h_integrable)
        (pv_piecewise_bound γ z₀ g)
        h_integrable.norm
        (pv_piecewise_pointwise γ z₀ g h_finite_preimage)⟩

private theorem pv_simple_pole_integrand_split
    (γ_fun : ℝ → ℂ) (z₀ c : ℂ) (g : ℂ → ℂ) (ε : ℝ) (t : ℝ) :
    (if ε < ‖γ_fun t - z₀‖
    then (c / (γ_fun t - z₀) + g (γ_fun t)) *
      deriv γ_fun t else 0) =
    (if ε < ‖γ_fun t - z₀‖
    then c / (γ_fun t - z₀) * deriv γ_fun t else 0) +
    (if ε < ‖γ_fun t - z₀‖
    then g (γ_fun t) * deriv γ_fun t else 0) := by
  split_ifs <;> ring

private theorem pv_simple_pole_tendsto
    (γ : PiecewiseC1Immersion) (z₀ c : ℂ) (g : ℂ → ℂ)
    (Ls Lg : ℂ)
    (hLs : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      if ε < ‖γ.toFun t - z₀‖
      then c / (γ.toFun t - z₀) * deriv γ.toFun t
      else 0) (𝓝[>] 0) (𝓝 Ls))
    (hLg : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      if ε < ‖γ.toFun t - z₀‖
      then g (γ.toFun t) * deriv γ.toFun t
      else 0) (𝓝[>] 0) (𝓝 Lg))
    (h_int : ∀ ε > 0,
      IntervalIntegrable (fun t =>
        if ε < ‖γ.toFun t - z₀‖
        then c / (γ.toFun t - z₀) * deriv γ.toFun t
        else 0) volume γ.a γ.b ∧
      IntervalIntegrable (fun t =>
        if ε < ‖γ.toFun t - z₀‖
        then g (γ.toFun t) * deriv γ.toFun t
        else 0) volume γ.a γ.b) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      (if ε < ‖γ.toFun t - z₀‖
      then c / (γ.toFun t - z₀) * deriv γ.toFun t
      else 0) + (if ε < ‖γ.toFun t - z₀‖
      then g (γ.toFun t) * deriv γ.toFun t
      else 0)) (𝓝[>] 0) (𝓝 (Ls + Lg)) := by
  refine Tendsto.congr' ?_ (Tendsto.add hLs hLg)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  symm
  exact intervalIntegral.integral_add
    (h_int ε (mem_Ioi.mp hε)).1 (h_int ε (mem_Ioi.mp hε)).2

/-- PV exists for c/(z-z₀) + g(z) when the regular part g has PV. -/
theorem cauchyPrincipalValueExists_of_simple_pole
    (γ : PiecewiseC1Immersion) (z₀ : ℂ) (c : ℂ)
    (g : ℂ → ℂ)
    (h_crossing_cauchy :
      (∃ t ∈ Icc γ.a γ.b, γ.toFun t = z₀) →
        Cauchy (Filter.map (fun ε =>
          ∫ t in γ.a..γ.b,
            if ε < ‖γ.toFun t - z₀‖
            then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t
            else 0) (𝓝[>] 0)))
    (h_g_exists :
      CauchyPrincipalValueExists' g γ.toFun γ.a γ.b z₀)
    (h_int : ∀ ε > 0,
      IntervalIntegrable (fun t =>
        if ε < ‖γ.toFun t - z₀‖
        then c / (γ.toFun t - z₀) * deriv γ.toFun t
        else 0) volume γ.a γ.b ∧
      IntervalIntegrable (fun t =>
        if ε < ‖γ.toFun t - z₀‖
        then g (γ.toFun t) * deriv γ.toFun t
        else 0) volume γ.a γ.b) :
    CauchyPrincipalValueExists'
      (fun z => c / (z - z₀) + g z)
      γ.toFun γ.a γ.b z₀ := by
  obtain ⟨Ls, hLs⟩ :=
    cauchyPrincipalValueExists_of_singular_pole
      γ z₀ c h_crossing_cauchy
  obtain ⟨Lg, hLg⟩ := h_g_exists
  refine ⟨Ls + Lg, ?_⟩
  simp_rw [pv_simple_pole_integrand_split]
  exact pv_simple_pole_tendsto γ z₀ c g Ls Lg hLs hLg h_int

end
