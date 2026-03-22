/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Residue.MeasureHelpers
import LeanModularForms.GeneralizedResidueTheory.Residue

/-!
# Multi-point Principal Value Infrastructure

Lemmas for multi-point Cauchy principal values: minimum separation,
disjoint balls, boundedness, integrability, measurability, and the
dominated convergence argument for decomposing multi-point PVs into
sums of single-point PVs.

## Main Results

* `finset_discrete_min_sep` — positive minimum separation in a
  finite set
* `disjoint_balls_of_small_epsilon` — disjoint balls for small ε
* `dominated_convergence_multipoint_helper` — dominated convergence
  for multi-point PV decomposition
* `multipointPV_diff_tendsto` — difference integrand converges
* `multipointPV_eq_sum_of_integral_zero` — multi-point PV equals
  sum of single-point PVs when regular integral vanishes
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

/-! ## Measurability Infrastructure -/

private lemma measurableSet_norm_gt_of_continuousOn {f : ℝ → ℂ} {s : Set ℝ} (ε : ℝ)
    (hf : ContinuousOn f s) (hs : MeasurableSet s) :
    MeasurableSet ({t | ε < ‖f t‖} ∩ s) := by
  have h_norm_cont : ContinuousOn (fun t => ‖f t‖) s := hf.norm
  have h_open_sub : IsOpen ((s.restrict (fun t => ‖f t‖)) ⁻¹' Set.Ioi ε) :=
    isOpen_Ioi.preimage h_norm_cont.restrict
  rw [isOpen_induced_iff] at h_open_sub
  obtain ⟨U, hU_open, hU_eq⟩ := h_open_sub
  have h_eq : {t | ε < ‖f t‖} ∩ s = U ∩ s := by
    ext x; constructor
    · intro ⟨hx_far, hx_s⟩; refine ⟨?_, hx_s⟩
      have h1 : (⟨x, hx_s⟩ : ↑s) ∈
          (s.restrict (fun t => ‖f t‖)) ⁻¹' Set.Ioi ε := by
        simp only [Set.mem_preimage, Set.restrict_apply, Set.mem_Ioi]; exact hx_far
      rw [← hU_eq] at h1; exact h1
    · intro ⟨hx_U, hx_s⟩; refine ⟨?_, hx_s⟩
      have h1 : (⟨x, hx_s⟩ : ↑s) ∈ Subtype.val ⁻¹' U := hx_U
      rw [hU_eq] at h1
      simp only [Set.mem_preimage, Set.restrict_apply, Set.mem_Ioi] at h1; exact h1
  rw [h_eq]; exact hU_open.measurableSet.inter hs

private lemma measurableSet_norm_gt_Icc {f : ℝ → ℂ} {a b : ℝ} (ε : ℝ)
    (hf : ContinuousOn f (Icc a b)) :
    MeasurableSet ({t | ε < ‖f t‖} ∩ Icc a b) :=
  measurableSet_norm_gt_of_continuousOn ε hf isClosed_Icc.measurableSet

theorem aEStronglyMeasurable_of_continuousOn_off_finite {f : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ}
    (hf_cont : ContinuousOn f (Icc a b \ P)) :
    AEStronglyMeasurable f (volume.restrict (Icc a b)) := by
  have hP_finite : (↑P ∩ Icc a b : Set ℝ).Finite := P.finite_toSet.inter_of_left (Icc a b)
  have hP_meas_zero : volume (↑P ∩ Icc a b) = 0 := hP_finite.measure_zero volume
  have h_diff_meas : MeasurableSet (Icc a b \ P) :=
    isClosed_Icc.measurableSet.diff P.finite_toSet.measurableSet
  have h_cont_meas : AEStronglyMeasurable f (volume.restrict (Icc a b \ P)) :=
    hf_cont.aestronglyMeasurable h_diff_meas
  have hP_inter_meas : MeasurableSet (↑P ∩ Icc a b) :=
    P.finite_toSet.measurableSet.inter isClosed_Icc.measurableSet
  have h_disj : Disjoint (Icc a b \ P) (↑P ∩ Icc a b) := by
    rw [Set.disjoint_left]; intro x ⟨_, hx_nP⟩ ⟨hx_P, _⟩; exact hx_nP hx_P
  have h_eq : volume.restrict (Icc a b) =
      volume.restrict (Icc a b \ P) + volume.restrict (↑P ∩ Icc a b) := by
    rw [← Measure.restrict_union h_disj hP_inter_meas]; congr 1; ext x
    simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]; tauto
  rw [h_eq]; apply AEStronglyMeasurable.add_measure h_cont_meas
  simp only [Measure.restrict_eq_zero.mpr hP_meas_zero]
  exact aestronglyMeasurable_zero_measure f

private lemma measurableSet_multipoint_condition {γ : ℝ → ℂ} {a b ε : ℝ} (S : Finset ℂ)
    (hγ : ContinuousOn γ (Icc a b)) :
    MeasurableSet ({t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} ∩ Icc a b) := by
  have h_eq : {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} ∩ Icc a b =
      ⋃ s ∈ S, ({t | ‖γ t - s‖ ≤ ε} ∩ Icc a b) := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro ⟨⟨s, hs, h_norm⟩, ht_Icc⟩; exact ⟨s, hs, h_norm, ht_Icc⟩
    · intro ⟨s, hs, h_norm, ht_Icc⟩; exact ⟨⟨s, hs, h_norm⟩, ht_Icc⟩
  rw [h_eq]; apply Finset.measurableSet_biUnion; intro s _
  have h_compl_meas : MeasurableSet ({t | ε < ‖γ t - s‖} ∩ Icc a b) :=
    measurableSet_norm_gt_Icc ε (hγ.sub continuousOn_const)
  have h_eq' : {t | ‖γ t - s‖ ≤ ε} ∩ Icc a b =
      Icc a b \ ({t | ε < ‖γ t - s‖} ∩ Icc a b) := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_diff, not_and]
    constructor
    · intro ⟨h_le, ht_Icc⟩; exact ⟨ht_Icc, fun h_gt => absurd h_gt (not_lt.mpr h_le)⟩
    · intro ⟨ht_Icc, h_not⟩; refine ⟨?_, ht_Icc⟩
      by_contra h_gt; push_neg at h_gt; exact (h_not h_gt) ht_Icc
  rw [h_eq']; exact isClosed_Icc.measurableSet.diff h_compl_meas

private lemma measurableSet_multipoint_goodset {γ : ℝ → ℂ} {a b ε : ℝ} (S : Finset ℂ)
    (hγ : ContinuousOn γ (Icc a b)) :
    MeasurableSet ({t | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b) := by
  have h_eq : {t | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b =
      Icc a b \ ({t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} ∩ Icc a b) := by
    ext t; constructor
    · intro ⟨h_good, ht_Icc⟩; refine ⟨ht_Icc, ?_⟩
      intro ⟨⟨s, hs, h_le⟩, _⟩; linarith [h_good s hs]
    · intro ⟨ht_Icc, h_not⟩; refine ⟨?_, ht_Icc⟩; intro s hs
      by_contra h_le; push_neg at h_le; exact h_not ⟨⟨s, hs, h_le⟩, ht_Icc⟩
  rw [h_eq]; exact isClosed_Icc.measurableSet.diff (measurableSet_multipoint_condition S hγ)

private lemma goodset_piecewise_ae_eq_multipoint {g : ℂ → ℂ} {γ : ℝ → ℂ} {a b ε : ℝ}
    (S : Finset ℂ) :
    (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then (0 : ℂ) else g (γ t) * deriv γ t)
      =ᵐ[volume.restrict (Icc a b)]
    ({t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b).piecewise
      (fun t => g (γ t) * deriv γ t) (fun _ => 0) := by
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
  simp only [Set.piecewise, Set.mem_inter_iff, Set.mem_setOf_eq]
  by_cases ht_good : (∀ s ∈ S, ε < ‖γ t - s‖) ∧ t ∈ Icc a b
  · rw [if_pos ht_good]
    have : ¬∃ s ∈ S, ‖γ t - s‖ ≤ ε := by push_neg; exact ht_good.1
    simp only [this, ↓reduceIte]
  · rw [if_neg ht_good]
    have : ∃ s ∈ S, ‖γ t - s‖ ≤ ε := by
      by_contra h_not; push_neg at h_not; exact ht_good ⟨h_not, ht⟩
    simp only [this, ↓reduceIte]

private theorem aEStronglyMeasurable_pv_integrand_multipoint {g : ℂ → ℂ} {γ : ℝ → ℂ}
    {a b ε : ℝ} {P : Finset ℝ} (S : Finset ℂ) (hg : ContinuousOn g (γ '' Icc a b))
    (hγ : ContinuousOn γ (Icc a b)) (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0
      else g (γ t) * deriv γ t) (volume.restrict (Icc a b)) := by
  have h_base_meas : AEStronglyMeasurable (fun t => g (γ t) * deriv γ t)
      (volume.restrict (Icc a b)) :=
    ((hg.comp hγ fun t ht => Set.mem_image_of_mem _ ht).aestronglyMeasurable
      isClosed_Icc.measurableSet).mul
      (aEStronglyMeasurable_of_continuousOn_off_finite hγ'_off_P)
  have h_zero_meas : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
      (volume.restrict ({t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b)ᶜ) :=
    aestronglyMeasurable_const
  have h_piecewise := AEStronglyMeasurable.piecewise (measurableSet_multipoint_goodset S hγ)
    (h_base_meas.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))
    h_zero_meas
  exact (h_piecewise.mono_measure Measure.restrict_le_self).congr
    (goodset_piecewise_ae_eq_multipoint S).symm

private lemma aEStronglyMeasurable_residueProd_on_goodset {γ : ℝ → ℂ} {a b ε : ℝ}
    {P : Finset ℝ} {s c : ℂ} (hε : 0 < ε) (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable (fun t => (c / (γ t - s)) * deriv γ t)
      (volume.restrict ({t : ℝ | ε < ‖γ t - s‖} ∩ Icc a b)) := by
  have h_ratio : AEStronglyMeasurable (fun t => c / (γ t - s))
      (volume.restrict ({t : ℝ | ε < ‖γ t - s‖} ∩ Icc a b)) := by
    apply ContinuousOn.aestronglyMeasurable _
      (measurableSet_norm_gt_Icc ε (hγ.sub continuousOn_const))
    apply ContinuousOn.div continuousOn_const
    · exact (hγ.mono Set.inter_subset_right).sub continuousOn_const
    · intro t ⟨ht_good, _⟩; exact norm_ne_zero_iff.mp (ne_of_gt (lt_trans hε ht_good))
  exact h_ratio.mul ((aEStronglyMeasurable_of_continuousOn_off_finite
    hγ'_off_P).mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))

private theorem
    aEStronglyMeasurable_pv_integrand_residue
    {γ : ℝ → ℂ} {a b ε : ℝ} {P : Finset ℝ}
    {s c : ℂ}
    (_hε : 0 < ε)
    (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ)
      (Icc a b \ P)) :
    AEStronglyMeasurable
      (fun t => if ‖γ t - s‖ > ε
        then (c / (γ t - s)) * deriv γ t
        else 0)
      (volume.restrict (Icc a b)) := by
  have hGoodSet_meas :
      MeasurableSet
        ({t | ε < ‖γ t - s‖} ∩ Icc a b) :=
    measurableSet_norm_gt_Icc ε
      (hγ.sub continuousOn_const)
  have h_zero_meas :
      AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
        (volume.restrict
          ({t : ℝ | ε < ‖γ t - s‖} ∩
            Icc a b)ᶜ) :=
    aestronglyMeasurable_const
  have h_prod_meas :
      AEStronglyMeasurable
        (fun t => (c / (γ t - s)) * deriv γ t)
        (volume.restrict
          ({t | ε < ‖γ t - s‖} ∩ Icc a b)) :=
    aEStronglyMeasurable_residueProd_on_goodset
      _hε hγ hγ'_off_P
  have h_piecewise :=
    AEStronglyMeasurable.piecewise hGoodSet_meas
      h_prod_meas h_zero_meas
  refine (h_piecewise.mono_measure
    Measure.restrict_le_self).congr ?_
  filter_upwards [ae_restrict_mem
    isClosed_Icc.measurableSet] with t ht
  simp only [Set.piecewise, Set.mem_inter_iff,
    Set.mem_setOf_eq, gt_iff_lt]
  by_cases h1 : ε < ‖γ t - s‖
  · simp only [h1, ht, and_self, ↓reduceIte]
  · push_neg at h1
    simp only [not_lt.mpr h1, ht, and_true,
      ↓reduceIte]

private lemma aEStronglyMeasurable_singularSum_on_goodset
    {γ : ℝ → ℂ} {a b ε : ℝ}
    (S : Finset ℂ) (coeffs : ℂ → ℂ)
    (hε : 0 < ε)
    (hγ : ContinuousOn γ (Icc a b)) :
    AEStronglyMeasurable
      (fun t => ∑ s ∈ S, coeffs s / (γ t - s))
      (volume.restrict
        ({t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖} ∩
          Icc a b)) := by
  apply Finset.aestronglyMeasurable_fun_sum S
  intro s hs
  apply ContinuousOn.aestronglyMeasurable _
    (measurableSet_multipoint_goodset S hγ)
  apply ContinuousOn.div continuousOn_const
  · exact (hγ.mono Set.inter_subset_right).sub
      continuousOn_const
  · intro t ⟨ht_good, _⟩
    exact norm_ne_zero_iff.mp
      (ne_of_gt (lt_trans hε (ht_good s hs)))

private lemma aEStronglyMeasurable_decomposed_on_goodset {g_reg : ℂ → ℂ} {γ : ℝ → ℂ}
    {a b ε : ℝ} {P : Finset ℝ} (S : Finset ℂ) (coeffs : ℂ → ℂ) (hε : 0 < ε)
    (hg : ContinuousOn g_reg (γ '' Icc a b)) (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable (fun t => (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t)
      (volume.restrict ({t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b)) := by
  have hgγ_cont : ContinuousOn (fun t => g_reg (γ t)) (Icc a b) :=
    hg.comp hγ fun t ht => Set.mem_image_of_mem _ ht
  have hgγ_meas : AEStronglyMeasurable (fun t => g_reg (γ t))
      (volume.restrict (Icc a b)) :=
    hgγ_cont.aestronglyMeasurable isClosed_Icc.measurableSet
  have h_f_meas := (hgγ_meas.mono_measure
    (Measure.restrict_mono Set.inter_subset_right le_rfl)).add
    (aEStronglyMeasurable_singularSum_on_goodset S coeffs hε hγ)
  exact h_f_meas.mul ((aEStronglyMeasurable_of_continuousOn_off_finite
    hγ'_off_P).mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))

private lemma goodset_piecewise_ae_eq_decomposed {g_reg : ℂ → ℂ} {γ : ℝ → ℂ} {a b ε : ℝ}
    (S : Finset ℂ) (coeffs : ℂ → ℂ) :
    (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0
      else (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t)
      =ᵐ[volume.restrict (Icc a b)]
    ({t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b).piecewise
      (fun t => (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t)
      (fun _ => 0) := by
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
  simp only [Set.piecewise, Set.mem_inter_iff, Set.mem_setOf_eq]
  by_cases ht_good : (∀ s ∈ S, ε < ‖γ t - s‖) ∧ t ∈ Icc a b
  · rw [if_pos ht_good]
    have : ¬∃ s ∈ S, ‖γ t - s‖ ≤ ε := by push_neg; exact ht_good.1
    simp only [this, if_false]
  · rw [if_neg ht_good]
    have : ∃ s ∈ S, ‖γ t - s‖ ≤ ε := by
      by_contra h_not; push_neg at h_not; exact ht_good ⟨h_not, ht⟩
    simp only [this, if_true]

theorem aEStronglyMeasurable_pv_integrand_decomposed {g_reg : ℂ → ℂ} {γ : ℝ → ℂ}
    {a b ε : ℝ} {P : Finset ℝ} (S : Finset ℂ) (coeffs : ℂ → ℂ) (hε : 0 < ε)
    (hg : ContinuousOn g_reg (γ '' Icc a b)) (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0
      else (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t)
      (volume.restrict (Icc a b)) := by
  have h_prod_meas := aEStronglyMeasurable_decomposed_on_goodset
    S coeffs hε hg hγ hγ'_off_P
  have h_zero_meas : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
      (volume.restrict ({t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b)ᶜ) :=
    aestronglyMeasurable_const
  have h_piecewise := AEStronglyMeasurable.piecewise
    (measurableSet_multipoint_goodset S hγ) h_prod_meas h_zero_meas
  exact (h_piecewise.mono_measure
    Measure.restrict_le_self).congr
    (goodset_piecewise_ae_eq_decomposed
      S coeffs).symm

theorem integrableOn_of_bounded_aeMeasurable
    {f : ℝ → ℂ} {a b : ℝ} (M : ℝ)
    (hf_meas : AEStronglyMeasurable f
      (volume.restrict (Icc a b)))
    (hf_bound : ∀ x ∈ Icc a b, ‖f x‖ ≤ M) :
    IntegrableOn f (Icc a b) volume := by
  apply IntegrableOn.of_bound measure_Icc_lt_top
    hf_meas (max M 0)
  filter_upwards [ae_restrict_mem
    isClosed_Icc.measurableSet] with x hx
  calc ‖f x‖ ≤ M := hf_bound x hx
    _ ≤ max M 0 := le_max_left M 0

private theorem tendsto_integral_of_dominated' {a b : ℝ} {F : ℝ → ℝ → ℂ} {f : ℝ → ℂ}
    {g : ℝ → ℝ} (hF_meas : ∀ ε > 0,
      AEStronglyMeasurable (F ε) (volume.restrict (Ι a b)))
    (hF_le : ∀ ε > 0, ∀ᵐ t ∂volume, t ∈ Ι a b → ‖F ε t‖ ≤ g t)
    (hg_int : IntervalIntegrable g volume a b)
    (hF_lim : ∀ᵐ t ∂volume, t ∈ Ι a b →
      Tendsto (fun ε => F ε t) (𝓝[>] 0) (𝓝 (f t))) :
    Tendsto (fun ε => ∫ t in a..b, F ε t) (𝓝[>] 0) (𝓝 (∫ t in a..b, f t)) :=
  intervalIntegral.tendsto_integral_filter_of_dominated_convergence g
    (by filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε); exact hF_meas ε hε)
    (by filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε); exact hF_le ε hε)
    hg_int hF_lim

/-! ## Finite Set Separation -/

/-- Positive minimum separation in a finite set. -/
lemma finset_discrete_min_sep (S0 : Finset ℂ) (hS0_nonempty : S0.Nonempty)
    (hS0_discrete : ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → 0 < ‖s' - s‖) :
    ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖ := by
  by_cases h_singleton : S0.card ≤ 1
  · refine ⟨1, one_pos, fun s hs s' hs' hne => ?_⟩
    have h_card_eq : S0.card = 1 := by have := hS0_nonempty.card_pos; omega
    obtain ⟨x, hS0_eq⟩ := Finset.card_eq_one.mp h_card_eq
    have hs_eq : s = x := by rw [hS0_eq] at hs; exact Finset.mem_singleton.mp hs
    have hs'_eq : s' = x := by rw [hS0_eq] at hs'; exact Finset.mem_singleton.mp hs'
    exact (hne (hs_eq.trans hs'_eq.symm)).elim
  · push_neg at h_singleton
    classical
    let dists : Finset ℝ := S0.biUnion (fun s =>
      S0.filter (· ≠ s) |>.image (fun s' => ‖s' - s‖))
    have h_nonempty : dists.Nonempty := by
      obtain ⟨x, hx⟩ := hS0_nonempty
      have h_exists_y : ∃ y ∈ S0, y ≠ x := by
        by_contra h_all; push_neg at h_all
        have : S0.card ≤ 1 := (Finset.card_le_card
          (fun z hz => Finset.mem_singleton.mpr (h_all z hz))).trans (by simp)
        omega
      obtain ⟨y, hy, hne⟩ := h_exists_y; refine ⟨‖y - x‖, ?_⟩
      simp only [dists, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
      exact ⟨x, hx, y, ⟨hy, hne⟩, rfl⟩
    let δ := dists.min' h_nonempty
    have hδ_pos : 0 < δ := by
      have h_mem := Finset.min'_mem dists h_nonempty
      simp only [dists, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at h_mem
      obtain ⟨s, hs, s', ⟨hs', hne⟩, heq⟩ := h_mem
      have h_pos : 0 < ‖s' - s‖ := hS0_discrete s hs s' hs' hne.symm
      calc δ = ‖s' - s‖ := heq.symm
        _ > 0 := h_pos
    refine ⟨δ, hδ_pos, fun s hs s' hs' hne => ?_⟩
    have h_in : ‖s' - s‖ ∈ dists := by
      simp only [dists, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
      exact ⟨s, hs, s', ⟨hs', hne.symm⟩, rfl⟩
    exact Finset.min'_le dists _ h_in

/-- Disjoint balls for small epsilon. -/
lemma disjoint_balls_of_small_epsilon (S0 : Finset ℂ) (ε : ℝ) (_hε : 0 < ε) (δ : ℝ)
    (_hδ : 0 < δ) (hε_small : ε < δ / 2)
    (h_sep : ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖) :
    ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' →
      Disjoint (Metric.ball s ε) (Metric.ball s' ε) := by
  intro s hs s' hs' hne; apply Metric.ball_disjoint_ball
  have h_sep' := h_sep s hs s' hs' hne
  have h2 : δ ≤ dist s s' := by rw [dist_eq_norm, norm_sub_rev]; exact h_sep'
  linarith

/-! ## Boundedness Lemmas -/

/-- Continuous functions on a compact image are bounded. -/
lemma continuousOn_image_bounded {g : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hγ_cont : ContinuousOn γ (Icc a b)) (hg_cont : ContinuousOn g (γ '' Icc a b)) :
    ∃ Mg : ℝ, ∀ z ∈ γ '' Icc a b, ‖g z‖ ≤ Mg :=
  (isCompact_Icc.image_of_continuousOn hγ_cont).exists_bound_of_continuousOn hg_cont

/-- Piecewise if-then-else is bounded when the active branch is bounded. -/
lemma piecewise_if_bounded {f : ℝ → ℂ} {a b M : ℝ} {cond : ℝ → Prop} [DecidablePred cond]
    (hf_bound : ∀ t ∈ Icc a b, cond t → ‖f t‖ ≤ M) (hM : 0 ≤ M) :
    ∀ t ∈ Icc a b, ‖if cond t then f t else 0‖ ≤ M := by
  intro t ht; by_cases hcond : cond t
  · simp only [hcond, ↓reduceIte]; exact hf_bound t ht hcond
  · simp only [hcond, ↓reduceIte, norm_zero]; exact hM

/-- Residue term is bounded when separated from the singularity. -/
lemma residue_term_bounded_when_separated {γ : ℝ → ℂ} {s c : ℂ} {a b ε : ℝ}
    (hε : 0 < ε) (h_sep : ∀ t ∈ Icc a b, ε < ‖γ t - s‖) :
    ∀ t ∈ Icc a b, ‖c / (γ t - s)‖ ≤ ‖c‖ / ε := by
  intro t ht
  have h_ne : γ t - s ≠ 0 := by
    intro h_eq; have := h_sep t ht; simp only [h_eq, norm_zero] at this; linarith
  rw [norm_div]; exact div_le_div_of_nonneg_left (norm_nonneg c) hε (le_of_lt (h_sep t ht))

def residueNormSum (f : ℂ → ℂ) (S : Finset ℂ) : ℝ := ∑ s ∈ S, ‖residueSimplePole f s‖

lemma A_int_bound_good_set {S0 : Finset ℂ} {f g_reg : ℂ → ℂ} {γ : ℝ → ℂ}
    {a b ε Mg Mγ : ℝ} (hε : 0 < ε) (hMg : 0 ≤ Mg) (_hMγ : 0 ≤ Mγ)
    (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s))
    (hg_bound : ∀ t ∈ Icc a b, ‖g_reg (γ t)‖ ≤ Mg)
    (hγ'_bound : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ Mγ)
    (h_all_far : ∀ t ∈ Icc a b, ∀ s ∈ S0, ε < ‖γ t - s‖) :
    ∀ t ∈ Icc a b,
      ‖(cauchyPrincipalValueIntegrandOn S0 f γ ε t -
        ∑ s ∈ S0, if ‖γ t - s‖ > ε then residueSimplePole f s / (γ t - s) * deriv γ t
          else 0)‖ ≤ Mg * Mγ := by
  intro t ht
  have h_no_excl : ¬∃ s ∈ S0, ‖γ t - s‖ ≤ ε := by
    push_neg; exact fun s hs => h_all_far t ht s hs
  simp only [cauchyPrincipalValueIntegrandOn, h_no_excl, ↓reduceIte]
  have h_sum_active : ∑ s ∈ S0, (if ε < ‖γ t - s‖
      then residueSimplePole f s / (γ t - s) * deriv γ t else 0) =
      (∑ s ∈ S0, residueSimplePole f s / (γ t - s)) * deriv γ t := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl
    intro s hs; simp only [h_all_far t ht s hs, ↓reduceIte]
  rw [h_sum_active]
  have h_factor : f (γ t) * deriv γ t -
      (∑ s ∈ S0, residueSimplePole f s / (γ t - s)) * deriv γ t =
      (f (γ t) - ∑ s ∈ S0, residueSimplePole f s / (γ t - s)) * deriv γ t := by ring
  rw [h_factor]
  have h_not_in_S0 : γ t ∉ (S0 : Set ℂ) := by
    intro h_in; simp only [Finset.mem_coe] at h_in
    have := h_all_far t ht (γ t) h_in; simp only [sub_self, norm_zero] at this; linarith
  rw [show f (γ t) - ∑ s ∈ S0, residueSimplePole f s / (γ t - s) = g_reg (γ t) from by
    rw [hg_decomp (γ t) h_not_in_S0]; ring]
  calc ‖g_reg (γ t) * deriv γ t‖ = ‖g_reg (γ t)‖ * ‖deriv γ t‖ := norm_mul _ _
    _ ≤ Mg * Mγ := mul_le_mul (hg_bound t ht) (hγ'_bound t ht) (norm_nonneg _) hMg

/-! ## Integrability Lemmas -/

/-- Multi-point PV integrand is interval integrable. -/
lemma intervalIntegrable_cauchyPrincipalValueIntegrandOn {S0 : Finset ℂ} {f : ℂ → ℂ}
    {γ : PiecewiseC1Immersion} {ε : ℝ} (_hε : 0 < ε)
    (hf_cont : ContinuousOn f (γ.toFun '' Icc γ.a γ.b)) :
    IntervalIntegrable (cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε) volume γ.a γ.b := by
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  obtain ⟨Mf, hMf⟩ := continuousOn_image_bounded hγ_cont hf_cont
  obtain ⟨Mγ', hMγ'⟩ := piecewiseC1Immersion_deriv_bounded γ
  have _h_bound : ∀ t ∈ Icc γ.a γ.b,
      ‖cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t‖ ≤ |Mf| * |Mγ'| + 1 := by
    intro t ht; simp only [cauchyPrincipalValueIntegrandOn]; split_ifs with h
    · simp only [norm_zero]; positivity
    · calc ‖f (γ.toFun t) * deriv γ.toFun t‖
          = ‖f (γ.toFun t)‖ * ‖deriv γ.toFun t‖ := norm_mul _ _
        _ ≤ |Mf| * |Mγ'| := by
            apply mul_le_mul
            · exact le_trans (hMf _ (Set.mem_image_of_mem _ ht)) (le_abs_self _)
            · exact le_trans (hMγ' t ht) (le_abs_self _)
            · exact norm_nonneg _
            · positivity
        _ ≤ |Mf| * |Mγ'| + 1 := by linarith
  let M := |Mf| * |Mγ'| + 1
  have h_meas :
      AEStronglyMeasurable
        (cauchyPrincipalValueIntegrandOn S0 f
          γ.toFun ε)
        (volume.restrict (Icc γ.a γ.b)) := by
    have hγ'_off_P :
        ContinuousOn (deriv γ.toFun)
          (Icc γ.a γ.b \ γ.partition) := by
      intro t ⟨ht_Icc, ht_notP⟩
      by_cases ht_Ioo : t ∈ Ioo γ.a γ.b
      · exact (γ.toPiecewiseC1Curve.deriv_continuous_off_partition
            t ht_Ioo ht_notP).continuousWithinAt
      · have ha_in_P :=
          γ.toPiecewiseC1Curve.endpoints_in_partition.1
        have hb_in_P :=
          γ.toPiecewiseC1Curve.endpoints_in_partition.2
        have ht_endpoint : t = γ.a ∨ t = γ.b := by
          simp only [Set.mem_Ioo, not_and,
            not_lt] at ht_Ioo
          rcases ht_Icc.1.lt_or_eq with h | h
          · right
            exact le_antisymm ht_Icc.2 (ht_Ioo h)
          · left; exact h.symm
        rcases ht_endpoint with rfl | rfl
        · exact (ht_notP ha_in_P).elim
        · exact (ht_notP hb_in_P).elim
    exact aEStronglyMeasurable_pv_integrand_multipoint
      S0 hf_cont hγ_cont hγ'_off_P
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (le_of_lt γ.hab)]
  apply IntegrableOn.mono_set
  · exact integrableOn_of_bounded_aeMeasurable M
      h_meas _h_bound
  · exact Ioc_subset_Icc_self

/-- Residue term integrand is interval integrable. -/
lemma intervalIntegrable_residueTerm
    {γ : PiecewiseC1Immersion} {s c : ℂ} {ε : ℝ}
    (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => if ‖γ.toFun t - s‖ > ε
        then (c / (γ.toFun t - s)) *
          deriv γ.toFun t
        else 0)
      volume γ.a γ.b := by
  have h_γ'_bound :=
    piecewiseC1Immersion_deriv_bounded γ
  obtain ⟨Mγ', hMγ'⟩ := h_γ'_bound
  let M := ‖c‖ / ε * |Mγ'| + 1
  have _h_bound :
      ∀ t ∈ Icc γ.a γ.b,
        ‖if ‖γ.toFun t - s‖ > ε
          then (c / (γ.toFun t - s)) *
            deriv γ.toFun t
          else 0‖ ≤ M := by
    intro t ht
    split_ifs with h
    · calc ‖(c / (γ.toFun t - s)) *
            deriv γ.toFun t‖
          = ‖c / (γ.toFun t - s)‖ *
            ‖deriv γ.toFun t‖ := norm_mul _ _
        _ ≤ (‖c‖ / ε) * |Mγ'| := by
            apply mul_le_mul
            · rw [norm_div]
              apply div_le_div_of_nonneg_left
                (norm_nonneg c) hε
              exact le_of_lt h
            · exact le_trans (hMγ' t ht)
                (le_abs_self _)
            · exact norm_nonneg _
            · positivity
        _ ≤ M := by simp only [M]; linarith
    · simp only [norm_zero, M]; positivity
  have hγ_cont :=
    γ.toPiecewiseC1Curve.continuous_toFun
  have hγ'_off_P :
      ContinuousOn (deriv γ.toFun)
        (Icc γ.a γ.b \ γ.partition) := by
    intro t ⟨ht_Icc, ht_notP⟩
    by_cases ht_Ioo : t ∈ Ioo γ.a γ.b
    · exact (γ.toPiecewiseC1Curve.deriv_continuous_off_partition
          t ht_Ioo ht_notP).continuousWithinAt
    · have ha_in_P :=
        γ.toPiecewiseC1Curve.endpoints_in_partition.1
      have hb_in_P :=
        γ.toPiecewiseC1Curve.endpoints_in_partition.2
      have ht_endpoint : t = γ.a ∨ t = γ.b := by
        simp only [Set.mem_Ioo, not_and,
          not_lt] at ht_Ioo
        rcases ht_Icc.1.lt_or_eq with h | h
        · right
          exact le_antisymm ht_Icc.2 (ht_Ioo h)
        · left; exact h.symm
      rcases ht_endpoint with rfl | rfl
      <;> exact (ht_notP (by assumption)).elim
  have h_meas :
      AEStronglyMeasurable
        (fun t => if ‖γ.toFun t - s‖ > ε
          then (c / (γ.toFun t - s)) *
            deriv γ.toFun t
          else 0)
        (volume.restrict (Icc γ.a γ.b)) :=
    aEStronglyMeasurable_pv_integrand_residue
      hε hγ_cont hγ'_off_P
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (le_of_lt γ.hab)]
  apply IntegrableOn.mono_set
  · exact integrableOn_of_bounded_aeMeasurable M
      h_meas _h_bound
  · exact Ioc_subset_Icc_self

/-! ## Measurability Lemmas -/

private lemma aEStronglyMeasurable_pv_sum_residue
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (ε : ℝ) (hε : 0 < ε) (a b : ℝ)
    {P : Finset ℝ}
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ)
      (Icc a b \ P)) :
    AEStronglyMeasurable
      (fun t => ∑ s ∈ S,
        if ‖γ t - s‖ > ε
        then residueSimplePole f s / (γ t - s) *
          deriv γ t
        else 0)
      (volume.restrict (Icc a b)) := by
  induction S using Finset.induction_on with
  | empty => exact aestronglyMeasurable_const
  | @insert x S' hx ih =>
    have hterm :=
      aEStronglyMeasurable_pv_integrand_residue
        (s := x)
        (c := residueSimplePole f x)
        hε hγ_cont hγ'_off_P
    refine AEStronglyMeasurable.add hterm ih
      |>.congr ?_
    refine ae_of_all _ (fun t => ?_)
    simp only [Pi.add_apply, Finset.sum_insert hx]

lemma aEStronglyMeasurable_multipointPV_diff
    (S0 : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (ε : ℝ) (hε : 0 < ε) (a b : ℝ)
    {P : Finset ℝ}
    (hf_cont : ContinuousOn f
      (γ '' Set.uIcc a b))
    (hγ_cont : ContinuousOn γ
      (Set.uIcc a b))
    (hγ'_off_P : ContinuousOn (deriv γ)
      (Set.uIcc a b \ P)) :
    AEStronglyMeasurable
      (fun t =>
        cauchyPrincipalValueIntegrandOn S0 f γ ε t -
          ∑ s ∈ S0,
            if ‖γ t - s‖ > ε
            then residueSimplePole f s / (γ t - s) *
              deriv γ t
            else 0)
      (volume.restrict (Ι a b)) := by
  rcases le_or_gt a b with hab | hab
  case inl =>
    have huIcc : Set.uIcc a b = Icc a b :=
      Set.uIcc_of_le hab
    rw [huIcc] at hf_cont hγ_cont hγ'_off_P
    have h1 :=
      aEStronglyMeasurable_pv_integrand_multipoint
        (ε := ε) S0 hf_cont hγ_cont hγ'_off_P
    have h3 :=
      aEStronglyMeasurable_pv_sum_residue S0 f γ ε
        hε a b hγ_cont hγ'_off_P
    have h4 := h1.sub h3
    have h_subset : Ι a b ⊆ Icc a b :=
      Set.uIoc_of_le hab ▸ Set.Ioc_subset_Icc_self
    exact h4.mono_measure
      (Measure.restrict_mono h_subset le_rfl)
  case inr =>
    have hba : b ≤ a := hab.le
    have huIcc : Set.uIcc a b = Icc b a :=
      Set.uIcc_of_ge hba
    rw [huIcc] at hf_cont hγ_cont hγ'_off_P
    have h1 :=
      aEStronglyMeasurable_pv_integrand_multipoint
        (ε := ε) S0 hf_cont hγ_cont hγ'_off_P
    have h3 :=
      aEStronglyMeasurable_pv_sum_residue S0 f γ ε
        hε b a hγ_cont hγ'_off_P
    have h4 := h1.sub h3
    have h_subset : Ι a b ⊆ Icc b a :=
      Set.uIoc_comm a b ▸
        Set.uIoc_of_le hba ▸
          Set.Ioc_subset_Icc_self
    exact h4.mono_measure
      (Measure.restrict_mono h_subset le_rfl)

/-! ## Dominated Convergence -/

/-- Core dominated convergence for multi-point PV
decomposition. -/
lemma dominated_convergence_multipoint_helper
    (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (g_reg : ℂ → ℂ)
    (_h_crossing_null : MeasureTheory.volume
      {t | t ∈ Icc γ.a γ.b ∧
        γ.toFun t ∈ (S0 : Set ℂ)} = 0)
    (_hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z +
        ∑ s ∈ S0,
          residueSimplePole f s / (z - s))
    (_hg_cont : ContinuousOn g_reg
      (γ.toFun '' Icc γ.a γ.b))
    (hS0_sep : ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0,
      s ≠ s' → δ ≤ ‖s' - s‖) :
    let M := fun ε =>
      ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 f
          γ.toFun ε t
    let S' := fun ε =>
      ∑ s ∈ S0.attach,
        ∫ t in γ.a..γ.b,
          if ‖γ.toFun t - s.val‖ > ε
          then (residueSimplePole f s.val /
            (γ.toFun t - s.val)) *
              deriv γ.toFun t
          else 0
    let A := fun ε => M ε - S' ε
    let G := ∫ t in γ.a..γ.b,
      g_reg (γ.toFun t) * deriv γ.toFun t
    Tendsto A (𝓝[>] 0) (𝓝 G) := by
  intro M S' A G
  by_cases hS0_empty : S0 = ∅
  case pos =>
    subst hS0_empty
    have hA_eq_M : ∀ ε, A ε = M ε := by
      intro ε
      simp only [A, S', Finset.attach_empty,
        Finset.sum_empty, sub_zero]
    have hM_eq :
        ∀ ε > 0, M ε =
          ∫ t in γ.a..γ.b,
            f (γ.toFun t) * deriv γ.toFun t := by
      intro ε _hε
      apply intervalIntegral.integral_congr
      intro t _
      simp only [cauchyPrincipalValueIntegrandOn,
        Finset.notMem_empty, false_and,
        exists_false, ↓reduceIte]
    have hf_eq_g : ∀ z, f z = g_reg z := by
      intro z
      have h := _hg_decomp z (Finset.notMem_empty z)
      simp only [Finset.sum_empty, add_zero] at h
      exact h
    have hM_eq_G : ∀ ε > 0, M ε = G := by
      intro ε hε
      rw [hM_eq ε hε]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [hf_eq_g (γ.toFun t)]
    apply Filter.Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin]
        with ε hε
      rw [hA_eq_M, hM_eq_G ε hε]
    · exact tendsto_const_nhds
  case neg =>
    let A_int : ℝ → ℝ → ℂ := fun ε t =>
      cauchyPrincipalValueIntegrandOn S0 f
        γ.toFun ε t -
        ∑ s ∈ S0,
          if ‖γ.toFun t - s‖ > ε
          then (residueSimplePole f s /
            (γ.toFun t - s)) * deriv γ.toFun t
          else 0
    let f_lim : ℝ → ℂ := fun t =>
      g_reg (γ.toFun t) * deriv γ.toFun t
    have h_S'_eq :
        ∀ ε, S' ε =
          ∑ s ∈ S0,
            ∫ t in γ.a..γ.b,
              if ‖γ.toFun t - s‖ > ε
              then (residueSimplePole f s /
                (γ.toFun t - s)) * deriv γ.toFun t
              else 0 := by
      intro ε
      simp only [S']
      rw [Finset.sum_attach S0
        (fun s => ∫ t in γ.a..γ.b,
          if ‖γ.toFun t - s‖ > ε
          then (residueSimplePole f s /
            (γ.toFun t - s)) * deriv γ.toFun t
          else 0)]
    have h_A_eq_int :
        ∀ ε > 0, A ε =
          ∫ t in γ.a..γ.b, A_int ε t := by
      intro ε _hε
      simp only [A, M, h_S'_eq, A_int]
      let S_int_fun : ℂ → ℝ → ℂ := fun s t =>
        if ‖γ.toFun t - s‖ > ε
        then (residueSimplePole f s /
          (γ.toFun t - s)) * deriv γ.toFun t
        else 0
      have hM_int :
          IntervalIntegrable
            (cauchyPrincipalValueIntegrandOn
              S0 f γ.toFun ε)
            volume γ.a γ.b := by
        have hγ_cont :=
          γ.toPiecewiseC1Curve.continuous_toFun
        have h_γ'_bound :=
          piecewiseC1Immersion_deriv_bounded γ
        obtain ⟨Mγ', hMγ'⟩ := h_γ'_bound
        have h_g_bound :=
          continuousOn_image_bounded hγ_cont
            _hg_cont
        obtain ⟨Mg, hMg⟩ := h_g_bound
        have hS0_nonempty : S0.Nonempty :=
          Finset.nonempty_of_ne_empty hS0_empty
        let res_bound :=
          S0.sup' hS0_nonempty
            (fun s => ‖residueSimplePole f s‖)
        have h_res_nonneg : 0 ≤ res_bound := by
          simp only [res_bound]
          have hs := hS0_nonempty.choose_spec
          exact le_trans (norm_nonneg _)
            (Finset.le_sup'
              (fun s => ‖residueSimplePole f s‖)
              hs)
        let Mb :=
          (|Mg| + S0.card * res_bound / ε) *
            |Mγ'| + 1
        have hMb_pos : 0 < Mb := by
          simp only [Mb]; positivity
        have h_bound :
            ∀ t ∈ Icc γ.a γ.b,
              ‖cauchyPrincipalValueIntegrandOn
                S0 f γ.toFun ε t‖ ≤ Mb := by
          intro t ht
          simp only [
            cauchyPrincipalValueIntegrandOn]
          split_ifs with h
          · simp only [norm_zero]; linarith
          · push_neg at h
            have hγt_notin :
                γ.toFun t ∉ (S0 : Set ℂ) := by
              intro hmem
              simp only [Finset.mem_coe] at hmem
              have hdist := h (γ.toFun t) hmem
              simp only [sub_self,
                norm_zero] at hdist
              linarith
            have hf_decomp_t :=
              _hg_decomp (γ.toFun t) hγt_notin
            have h_f_bound :
                ‖f (γ.toFun t)‖ ≤
                  |Mg| +
                    S0.card * res_bound / ε := by
              rw [hf_decomp_t]
              calc ‖g_reg (γ.toFun t) +
                    ∑ s ∈ S0,
                      residueSimplePole f s /
                        (γ.toFun t - s)‖
                  ≤ ‖g_reg (γ.toFun t)‖ +
                    ‖∑ s ∈ S0,
                      residueSimplePole f s /
                        (γ.toFun t - s)‖ :=
                    norm_add_le _ _
                _ ≤ |Mg| +
                    ∑ s ∈ S0,
                      ‖residueSimplePole f s /
                        (γ.toFun t - s)‖ := by
                    gcongr
                    · exact le_trans
                        (hMg _ (Set.mem_image_of_mem
                          _ ht))
                        (le_abs_self _)
                    · exact norm_sum_le _ _
                _ ≤ |Mg| +
                    ∑ _s ∈ S0,
                      res_bound / ε := by
                    gcongr with s hs
                    rw [norm_div]
                    have h_res_le :
                        ‖residueSimplePole f s‖ ≤
                          res_bound :=
                      Finset.le_sup'
                        (fun s =>
                          ‖residueSimplePole f s‖)
                        hs
                    have h_dist_pos :
                        0 < ‖γ.toFun t - s‖ :=
                      lt_trans _hε (h s hs)
                    calc ‖residueSimplePole f s‖ /
                          ‖γ.toFun t - s‖
                        ≤ res_bound /
                          ‖γ.toFun t - s‖ := by
                          gcongr
                      _ ≤ res_bound / ε := by
                          gcongr
                          exact le_of_lt (h s hs)
                _ = |Mg| +
                    S0.card * res_bound / ε := by
                    simp only [Finset.sum_const]
                    ring
            calc ‖f (γ.toFun t) *
                  deriv γ.toFun t‖
                = ‖f (γ.toFun t)‖ *
                  ‖deriv γ.toFun t‖ :=
                    norm_mul _ _
              _ ≤ (|Mg| +
                  S0.card * res_bound / ε) *
                    |Mγ'| := by
                  gcongr
                  exact le_trans (hMγ' t ht)
                    (le_abs_self _)
              _ ≤ Mb := by
                  simp only [Mb]; linarith
        have hγ'_off_P :
            ContinuousOn (deriv γ.toFun)
              (Icc γ.a γ.b \ γ.partition) := by
          intro t ⟨ht_Icc, ht_notP⟩
          by_cases ht_Ioo : t ∈ Ioo γ.a γ.b
          · exact (γ.toPiecewiseC1Curve.deriv_continuous_off_partition
                t ht_Ioo ht_notP).continuousWithinAt
          · have ha_in_P :=
              γ.toPiecewiseC1Curve.endpoints_in_partition.1
            have hb_in_P :=
              γ.toPiecewiseC1Curve.endpoints_in_partition.2
            have ht_endpoint :
                t = γ.a ∨ t = γ.b := by
              simp only [Set.mem_Ioo, not_and,
                not_lt] at ht_Ioo
              rcases ht_Icc.1.lt_or_eq with h | h
              · right
                exact le_antisymm ht_Icc.2
                  (ht_Ioo h)
              · left; exact h.symm
            rcases ht_endpoint with rfl | rfl
            · exact (ht_notP ha_in_P).elim
            · exact (ht_notP hb_in_P).elim
        have h_meas_decomposed :
            AEStronglyMeasurable
              (fun t =>
                if ∃ s ∈ S0, ‖γ.toFun t - s‖ ≤ ε
                then (0 : ℂ)
                else (g_reg (γ.toFun t) +
                  ∑ s ∈ S0,
                    residueSimplePole f s /
                      (γ.toFun t - s)) *
                    deriv γ.toFun t)
              (volume.restrict (Icc γ.a γ.b)) :=
          aEStronglyMeasurable_pv_integrand_decomposed
            S0 (residueSimplePole f) _hε _hg_cont
            hγ_cont hγ'_off_P
        have h_eq_ae :
            (fun t =>
              cauchyPrincipalValueIntegrandOn S0 f
                γ.toFun ε t)
            =ᵐ[volume.restrict (Icc γ.a γ.b)]
            (fun t =>
              if ∃ s ∈ S0, ‖γ.toFun t - s‖ ≤ ε
              then (0 : ℂ)
              else (g_reg (γ.toFun t) +
                ∑ s ∈ S0,
                  residueSimplePole f s /
                    (γ.toFun t - s)) *
                  deriv γ.toFun t) := by
          filter_upwards [ae_restrict_mem
            isClosed_Icc.measurableSet] with t _
          simp only [
            cauchyPrincipalValueIntegrandOn]
          split_ifs with h
          · rfl
          · push_neg at h
            have hγt_notin :
                γ.toFun t ∉ (S0 : Set ℂ) := by
              intro hmem
              simp only [Finset.mem_coe] at hmem
              have hdist := h (γ.toFun t) hmem
              simp only [sub_self,
                norm_zero] at hdist
              linarith
            rw [_hg_decomp (γ.toFun t) hγt_notin]
        have h_meas :
            AEStronglyMeasurable
              (fun t =>
                cauchyPrincipalValueIntegrandOn
                  S0 f γ.toFun ε t)
              (volume.restrict (Icc γ.a γ.b)) :=
          h_meas_decomposed.congr h_eq_ae.symm
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
          (le_of_lt γ.hab)]
        apply IntegrableOn.mono_set
        · exact integrableOn_of_bounded_aeMeasurable
            Mb h_meas h_bound
        · exact Ioc_subset_Icc_self
      have hS_int :
          ∀ s ∈ S0,
            IntervalIntegrable (S_int_fun s)
              volume γ.a γ.b := by
        intro s _hs
        exact intervalIntegrable_residueTerm _hε
      have h_sum_eq :
          ∑ s ∈ S0,
            ∫ t in γ.a..γ.b, S_int_fun s t =
          ∫ t in γ.a..γ.b,
            ∑ s ∈ S0, S_int_fun s t :=
        (intervalIntegral.integral_finset_sum
          hS_int).symm
      have hSum_int :
          IntervalIntegrable
            (fun t => ∑ s ∈ S0, S_int_fun s t)
            volume γ.a γ.b := by
        have : ∀ (S : Finset ℂ),
            (∀ s ∈ S,
              IntervalIntegrable (S_int_fun s)
                volume γ.a γ.b) →
            IntervalIntegrable
              (fun t => ∑ s ∈ S, S_int_fun s t)
              volume γ.a γ.b := by
          intro S
          induction S using Finset.induction_on with
          | empty =>
            intro _
            simp only [Finset.sum_empty]
            exact intervalIntegrable_const
          | insert s' S'' hs'' ih =>
            intro h_all
            simp only [Finset.sum_insert hs'']
            apply IntervalIntegrable.add
            · exact h_all s'
                (Finset.mem_insert_self s' S'')
            · exact ih (fun s hs =>
                h_all s
                  (Finset.mem_insert_of_mem hs))
        exact this S0 hS_int
      rw [h_sum_eq,
        ← intervalIntegral.integral_sub hM_int
          hSum_int]
    have hG_eq : G = ∫ t in γ.a..γ.b, f_lim t :=
      rfl
    have h_ae_lim :
        ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b →
          Tendsto (fun ε => A_int ε t) (𝓝[>] 0)
            (𝓝 (f_lim t)) := by
      have hC_null :
          volume {t | t ∈ Icc γ.a γ.b ∧
            γ.toFun t ∈ (S0 : Set ℂ)} = 0 :=
        _h_crossing_null
      rw [ae_iff]
      apply le_antisymm _ (zero_le _)
      calc volume {t | ¬(t ∈ Ι γ.a γ.b →
              Tendsto (fun ε => A_int ε t) (𝓝[>] 0)
                (𝓝 (f_lim t)))}
          ≤ volume {t | t ∈ Icc γ.a γ.b ∧
              γ.toFun t ∈ (S0 : Set ℂ)} := by
            apply MeasureTheory.measure_mono
            intro t ht
            simp only [Set.mem_setOf_eq] at ht
            rw [Classical.not_imp] at ht
            obtain ⟨ht_in, ht_not_tendsto⟩ := ht
            constructor
            · have h1 : t ∈ Set.uIcc γ.a γ.b :=
                Set.uIoc_subset_uIcc ht_in
              rw [Set.uIcc_of_le
                (le_of_lt γ.hab)] at h1
              exact h1
            · by_contra ht_not_in_S0
              apply ht_not_tendsto
              have hγt_not_in_S0 :
                  γ.toFun t ∉ (S0 : Set ℂ) :=
                ht_not_in_S0
              have hS0_nonempty : S0.Nonempty :=
                Finset.nonempty_iff_ne_empty.mpr
                  hS0_empty
              have hdist_pos :
                  ∀ s ∈ S0,
                    (0 : ℝ) < ‖γ.toFun t - s‖ := by
                intro s hs
                simp only [norm_pos_iff,
                  sub_ne_zero]
                intro heq
                exact hγt_not_in_S0 (heq ▸ hs)
              let δ := S0.inf' hS0_nonempty
                (fun s => ‖γ.toFun t - s‖)
              have hδ_pos : 0 < δ := by
                simp only [δ,
                  Finset.lt_inf'_iff]
                intro s hs
                exact hdist_pos s hs
              apply Filter.Tendsto.congr' _
                tendsto_const_nhds
              filter_upwards [Ioo_mem_nhdsGT hδ_pos]
                with ε ⟨hε_pos, hε_small⟩
              simp only [A_int, f_lim]
              have hall_far :
                  ∀ s ∈ S0,
                    ε < ‖γ.toFun t - s‖ := by
                intro s hs
                calc ε < δ := hε_small
                  _ ≤ ‖γ.toFun t - s‖ :=
                    Finset.inf'_le _ hs
              have hM_eval :
                  cauchyPrincipalValueIntegrandOn
                    S0 f γ.toFun ε t =
                    f (γ.toFun t) *
                      deriv γ.toFun t := by
                simp only [
                  cauchyPrincipalValueIntegrandOn]
                rw [if_neg]
                push_neg
                intro s hs
                exact hall_far s hs
              have hS_eval :
                  ∑ s ∈ S0,
                    (if ‖γ.toFun t - s‖ > ε
                      then residueSimplePole f s /
                        (γ.toFun t - s) *
                          deriv γ.toFun t
                      else 0) =
                    (∑ s ∈ S0,
                      residueSimplePole f s /
                        (γ.toFun t - s)) *
                      deriv γ.toFun t := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro s hs
                rw [if_pos (hall_far s hs)]
              rw [hM_eval, hS_eval, ← sub_mul]
              have hdecomp :=
                _hg_decomp (γ.toFun t)
                  hγt_not_in_S0
              have :
                  f (γ.toFun t) -
                    ∑ s ∈ S0,
                      residueSimplePole f s /
                        (γ.toFun t - s) =
                    g_reg (γ.toFun t) := by
                rw [hdecomp]; ring
              rw [this]
        _ = 0 := hC_null
    have hγ_cont :=
      γ.toPiecewiseC1Curve.continuous_toFun
    have h_Mg :
        ∃ Mg : ℝ,
          ∀ z ∈ γ.toFun '' Icc γ.a γ.b,
            ‖g_reg z‖ ≤ Mg :=
      continuousOn_image_bounded hγ_cont _hg_cont
    have h_Mγ' :
        ∃ Mγ' : ℝ,
          ∀ t ∈ Icc γ.a γ.b,
            ‖deriv γ.toFun t‖ ≤ Mγ' :=
      piecewiseC1Immersion_deriv_bounded γ
    obtain ⟨Mg, hMg⟩ := h_Mg
    obtain ⟨Mγ', hMγ'⟩ := h_Mγ'
    obtain ⟨δ, hδ_pos, hδ_sep⟩ := hS0_sep
    have h_Mc :
        ∃ Mc : ℝ,
          ∀ s ∈ S0,
            ‖residueSimplePole f s‖ ≤ Mc := by
      by_cases hS0_empty' : S0 = ∅
      · use 0; intro s hs
        simp [hS0_empty'] at hs
      · have hS0_nonempty : S0.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr
            hS0_empty'
        use S0.sup' hS0_nonempty
          (fun s => ‖residueSimplePole f s‖)
        intro s hs
        exact Finset.le_sup'
          (fun s => ‖residueSimplePole f s‖) hs
    obtain ⟨Mc, hMc⟩ := h_Mc
    let singularBound :=
      2 * (S0.card : ℝ) * Mc / δ
    let B := max 1
      (max (max 0 Mg) (max 0 singularBound) *
        max 0 Mγ')
    have _hB_pos : 0 < B :=
      lt_max_of_lt_left one_pos
    have h_bound :
        ∀ ε > 0, ∀ᵐ t ∂volume,
          t ∈ Ι γ.a γ.b → ‖A_int ε t‖ ≤ B := by
      intro ε _hε
      apply ae_of_all
      intro t ht
      by_cases hall :
          ∀ s ∈ S0, ε < ‖γ.toFun t - s‖
      case pos =>
        simp only [A_int,
          cauchyPrincipalValueIntegrandOn]
        have h_neg : ¬∃ s ∈ S0,
            ‖γ.toFun t - s‖ ≤ ε := by
          push_neg; exact fun s hs => hall s hs
        rw [if_neg h_neg]
        have hsum_eq :
            ∑ s ∈ S0,
              (if ‖γ.toFun t - s‖ > ε
                then residueSimplePole f s /
                  (γ.toFun t - s) *
                    deriv γ.toFun t
                else 0) =
              (∑ s ∈ S0,
                residueSimplePole f s /
                  (γ.toFun t - s)) *
                deriv γ.toFun t := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s hs
          rw [if_pos (hall s hs)]
        rw [hsum_eq, ← sub_mul]
        have ht_not_in_S0 :
            γ.toFun t ∉ (S0 : Set ℂ) := by
          intro hcontra
          have := hall (γ.toFun t) hcontra
          simp only [sub_self,
            norm_zero] at this
          linarith
        have hdecomp :=
          _hg_decomp (γ.toFun t) ht_not_in_S0
        have h_eq_greg :
            f (γ.toFun t) -
              ∑ s ∈ S0,
                residueSimplePole f s /
                  (γ.toFun t - s) =
              g_reg (γ.toFun t) := by
          rw [hdecomp]; ring
        rw [h_eq_greg]
        have ht_Icc : t ∈ Icc γ.a γ.b := by
          have h1 : t ∈ Set.uIoc γ.a γ.b := ht
          have h2 :
              Set.uIoc γ.a γ.b ⊆
                Icc γ.a γ.b := by
            rw [Set.uIoc_of_le
              (le_of_lt γ.hab)]
            exact Set.Ioc_subset_Icc_self
          exact h2 h1
        have h_g_bound :
            ‖g_reg (γ.toFun t)‖ ≤ Mg :=
          hMg (γ.toFun t) ⟨t, ht_Icc, rfl⟩
        have h_γ'_bound :
            ‖deriv γ.toFun t‖ ≤ Mγ' :=
          hMγ' t ht_Icc
        calc ‖g_reg (γ.toFun t) *
              deriv γ.toFun t‖
            ≤ ‖g_reg (γ.toFun t)‖ *
              ‖deriv γ.toFun t‖ :=
                norm_mul_le _ _
          _ ≤ Mg * Mγ' := by
              apply mul_le_mul h_g_bound h_γ'_bound
                (norm_nonneg _)
                (le_trans (norm_nonneg _) h_g_bound)
          _ ≤ max 0 Mg * max 0 Mγ' := by
              have h0_le_Mγ' : 0 ≤ Mγ' :=
                le_trans (norm_nonneg _) h_γ'_bound
              have h0_le_Mg : 0 ≤ Mg :=
                le_trans (norm_nonneg _) h_g_bound
              apply mul_le_mul (le_max_right 0 Mg)
                (le_max_right 0 Mγ')
                h0_le_Mγ' (le_max_left 0 Mg)
          _ ≤ max (max 0 Mg) (max 0 singularBound) *
              max 0 Mγ' := by
              apply mul_le_mul_of_nonneg_right
                (le_max_left _ _)
                (le_max_left 0 Mγ')
          _ ≤ B := le_max_right _ _
      case neg =>
        push_neg at hall
        obtain ⟨s₀, hs₀, hs₀_near⟩ := hall
        simp only [A_int,
          cauchyPrincipalValueIntegrandOn]
        rw [if_pos ⟨s₀, hs₀, hs₀_near⟩]
        simp only [zero_sub, norm_neg]
        have ht_Icc : t ∈ Icc γ.a γ.b := by
          have h1 : t ∈ Set.uIoc γ.a γ.b := ht
          have h2 :
              Set.uIoc γ.a γ.b ⊆
                Icc γ.a γ.b := by
            rw [Set.uIoc_of_le
              (le_of_lt γ.hab)]
            exact Set.Ioc_subset_Icc_self
          exact h2 h1
        have h_γ'_bound :
            ‖deriv γ.toFun t‖ ≤ Mγ' :=
          hMγ' t ht_Icc
        have h_factor :
            ∑ s ∈ S0,
              (if ‖γ.toFun t - s‖ > ε
                then residueSimplePole f s /
                  (γ.toFun t - s) *
                    deriv γ.toFun t
                else 0) =
              (∑ s ∈ S0,
                if ‖γ.toFun t - s‖ > ε
                then residueSimplePole f s /
                  (γ.toFun t - s)
                else 0) * deriv γ.toFun t := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          by_cases h : ‖γ.toFun t - s‖ > ε
          · simp only [h, ↓reduceIte]
          · simp only [h, ↓reduceIte, zero_mul]
        rw [h_factor]
        calc ‖(∑ s ∈ S0,
              if ‖γ.toFun t - s‖ > ε
              then residueSimplePole f s /
                (γ.toFun t - s)
              else 0) * deriv γ.toFun t‖
            ≤ ‖∑ s ∈ S0,
              if ‖γ.toFun t - s‖ > ε
              then residueSimplePole f s /
                (γ.toFun t - s)
              else 0‖ * ‖deriv γ.toFun t‖ :=
                norm_mul_le _ _
          _ ≤ singularBound * Mγ' := by
              apply mul_le_mul _ h_γ'_bound
                (norm_nonneg _) _
              · calc ‖∑ s ∈ S0,
                    if ‖γ.toFun t - s‖ > ε
                    then residueSimplePole f s /
                      (γ.toFun t - s)
                    else 0‖
                    ≤ ∑ s ∈ S0,
                      ‖if ‖γ.toFun t - s‖ > ε
                        then
                          residueSimplePole f s /
                            (γ.toFun t - s)
                        else 0‖ :=
                      norm_sum_le _ _
                  _ ≤ ∑ _s ∈ S0,
                      (2 * Mc / δ) := by
                    apply Finset.sum_le_sum
                    intro s hs
                    by_cases h_inc :
                        ‖γ.toFun t - s‖ > ε
                    · simp only [h_inc, ↓reduceIte]
                      have h_dist :
                          δ / 2 ≤
                            ‖γ.toFun t - s‖ := by
                        by_cases hs_eq : s = s₀
                        · subst hs_eq
                          exact absurd h_inc
                            (not_lt.mpr hs₀_near)
                        · have h_sep :
                              δ ≤ ‖s - s₀‖ := by
                            have := hδ_sep s hs s₀
                              hs₀ hs_eq
                            rw [norm_sub_rev] at this
                            exact this
                          have h_tri :
                              ‖s - s₀‖ -
                                ‖γ.toFun t - s₀‖ ≤
                                ‖γ.toFun t - s‖ := by
                            have := norm_sub_norm_le
                              (s - s₀)
                              (γ.toFun t - s₀)
                            calc ‖s - s₀‖ -
                                  ‖γ.toFun t - s₀‖
                                ≤ ‖(s - s₀) -
                                  (γ.toFun t - s₀)‖ :=
                                    this
                              _ = ‖s - γ.toFun t‖ :=
                                    by ring_nf
                              _ = ‖γ.toFun t - s‖ :=
                                    norm_sub_rev _ _
                          by_cases hε_small' :
                              ε ≤ δ / 2
                          · calc δ / 2 ≤ δ - ε := by
                                  linarith
                              _ ≤ ‖s - s₀‖ -
                                  ‖γ.toFun t - s₀‖ :=
                                  by linarith
                                    [h_sep, hs₀_near]
                              _ ≤ ‖γ.toFun t - s‖ :=
                                  h_tri
                          · push_neg at hε_small'
                            linarith [h_inc]
                      have h_δ_half_pos :
                          0 < δ / 2 := by
                        linarith [hδ_pos]
                      have hMc_nonneg :
                          0 ≤ Mc :=
                        le_trans (norm_nonneg _)
                          (hMc s hs)
                      calc ‖residueSimplePole f s /
                            (γ.toFun t - s)‖
                          = ‖residueSimplePole f s‖ /
                            ‖γ.toFun t - s‖ :=
                              norm_div _ _
                        _ ≤ Mc /
                            ‖γ.toFun t - s‖ :=
                          div_le_div_of_nonneg_right
                            (hMc s hs) (norm_nonneg _)
                        _ ≤ Mc / (δ / 2) :=
                          div_le_div_of_nonneg_left
                            hMc_nonneg h_δ_half_pos
                            h_dist
                        _ = 2 * Mc / δ := by ring
                    · simp only [h_inc, ↓reduceIte,
                        norm_zero]
                      apply div_nonneg
                      · apply mul_nonneg; linarith
                        exact le_trans (norm_nonneg _)
                          (hMc s₀ hs₀)
                      · linarith [hδ_pos]
                  _ = singularBound := by
                    simp only [Finset.sum_const]
                    ring
              · apply div_nonneg
                apply mul_nonneg
                apply mul_nonneg; linarith
                exact Nat.cast_nonneg _
                exact le_trans (norm_nonneg _)
                  (hMc s₀ hs₀)
                linarith [hδ_pos]
          _ ≤ max 0 singularBound * max 0 Mγ' := by
              have h0_le_Mγ' : 0 ≤ Mγ' :=
                le_trans (norm_nonneg _) h_γ'_bound
              apply mul_le_mul
                (le_max_right 0 singularBound)
                (le_max_right 0 Mγ')
                h0_le_Mγ'
                (le_max_left 0 singularBound)
          _ ≤ max (max 0 Mg)
              (max 0 singularBound) *
                max 0 Mγ' := by
              apply mul_le_mul_of_nonneg_right
                (le_max_right _ _)
                (le_max_left 0 Mγ')
          _ ≤ B := le_max_right _ _
    have h_bound_int :
        IntervalIntegrable (fun _ => B) volume
          γ.a γ.b :=
      intervalIntegrable_const
    have h_meas :
        ∀ ε > 0,
          AEStronglyMeasurable (A_int ε)
            (volume.restrict (Ι γ.a γ.b)) := by
      intro ε hε
      have hγ_cont' :=
        γ.toPiecewiseC1Curve.continuous_toFun
      have hγ'_off_P :
          ContinuousOn (deriv γ.toFun)
            (Icc γ.a γ.b \ γ.partition) := by
        intro t ⟨ht_Icc, ht_notP⟩
        by_cases ht_Ioo : t ∈ Ioo γ.a γ.b
        · exact (γ.toPiecewiseC1Curve.deriv_continuous_off_partition
              t ht_Ioo ht_notP).continuousWithinAt
        · have ha_in_P :=
            γ.toPiecewiseC1Curve.endpoints_in_partition.1
          have hb_in_P :=
            γ.toPiecewiseC1Curve.endpoints_in_partition.2
          have ht_endpoint :
              t = γ.a ∨ t = γ.b := by
            simp only [Set.mem_Ioo, not_and,
              not_lt] at ht_Ioo
            rcases ht_Icc.1.lt_or_eq with h | h
            · right
              exact le_antisymm ht_Icc.2 (ht_Ioo h)
            · left; exact h.symm
          rcases ht_endpoint with rfl | rfl
          <;> exact (ht_notP (by assumption)).elim
      have huIcc :
          Set.uIcc γ.a γ.b = Icc γ.a γ.b :=
        Set.uIcc_of_le (le_of_lt γ.hab)
      have hγ_cont_Icc :
          ContinuousOn γ.toFun (Icc γ.a γ.b) :=
        hγ_cont'
      have hγ'_off_P_Icc :
          ContinuousOn (deriv γ.toFun)
            (Icc γ.a γ.b \ γ.partition) :=
        hγ'_off_P
      rw [← huIcc] at hγ_cont' hγ'_off_P
      have h_eq_decomposed :
          ∀ t,
            cauchyPrincipalValueIntegrandOn S0 f
              γ.toFun ε t =
            (if ∃ s ∈ S0, ‖γ.toFun t - s‖ ≤ ε
              then 0
              else (g_reg (γ.toFun t) +
                ∑ s ∈ S0,
                  residueSimplePole f s /
                    (γ.toFun t - s)) *
                  deriv γ.toFun t) := by
        intro t
        simp only [
          cauchyPrincipalValueIntegrandOn]
        split_ifs with h_near
        · rfl
        · push_neg at h_near
          have h_not_in_S0 :
              γ.toFun t ∉ (S0 : Set ℂ) := by
            intro h_in
            have := h_near (γ.toFun t) h_in
            simp only [sub_self,
              norm_zero] at this
            linarith
          rw [_hg_decomp (γ.toFun t) h_not_in_S0]
      have h_meas1 :
          AEStronglyMeasurable
            (fun t =>
              if ∃ s ∈ S0, ‖γ.toFun t - s‖ ≤ ε
              then 0
              else (g_reg (γ.toFun t) +
                ∑ s ∈ S0,
                  residueSimplePole f s /
                    (γ.toFun t - s)) *
                  deriv γ.toFun t)
            (volume.restrict (Icc γ.a γ.b)) :=
        aEStronglyMeasurable_pv_integrand_decomposed
          S0 (residueSimplePole f)
          hε _hg_cont hγ_cont_Icc hγ'_off_P_Icc
      have h_meas_pv :
          AEStronglyMeasurable
            (cauchyPrincipalValueIntegrandOn
              S0 f γ.toFun ε)
            (volume.restrict (Icc γ.a γ.b)) :=
        h_meas1.congr (ae_of_all _ (fun t =>
          (h_eq_decomposed t).symm))
      have h_meas_sum :
          AEStronglyMeasurable
            (fun t => ∑ s ∈ S0,
              if ‖γ.toFun t - s‖ > ε
              then (residueSimplePole f s /
                (γ.toFun t - s)) *
                  deriv γ.toFun t
              else 0)
            (volume.restrict (Icc γ.a γ.b)) :=
        aEStronglyMeasurable_pv_sum_residue S0 f
          γ.toFun ε hε γ.a γ.b hγ_cont_Icc
          hγ'_off_P_Icc
      have h_meas_diff := h_meas_pv.sub h_meas_sum
      have h_subset : Ι γ.a γ.b ⊆ Icc γ.a γ.b :=
        Set.uIoc_of_le (le_of_lt γ.hab) ▸
          Set.Ioc_subset_Icc_self
      exact h_meas_diff.mono_measure
        (Measure.restrict_mono h_subset le_rfl)
    rw [hG_eq]
    apply Filter.Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin]
        with ε hε
      exact (h_A_eq_int ε hε).symm
    · exact tendsto_integral_of_dominated' h_meas
        h_bound h_bound_int h_ae_lim

/-- Difference integrand converges to regular
part integral. -/
lemma multipointPV_diff_tendsto
    (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion)
    (_h_crossing_null : MeasureTheory.volume
      {t | t ∈ Icc γ.a γ.b ∧
        γ.toFun t ∈ (S0 : Set ℂ)} = 0)
    (g_reg : ℂ → ℂ)
    (_hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z +
        ∑ s ∈ S0,
          residueSimplePole f s / (z - s))
    (hg_cont : ContinuousOn g_reg
      (γ.toFun '' Icc γ.a γ.b))
    (hS0_sep : ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0,
      s ≠ s' → δ ≤ ‖s' - s‖) :
    let M := fun ε =>
      ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 f
          γ.toFun ε t
    let S' := fun ε =>
      ∑ s ∈ S0.attach,
        ∫ t in γ.a..γ.b,
          if ‖γ.toFun t - s.val‖ > ε
          then (residueSimplePole f s.val /
            (γ.toFun t - s.val)) *
              deriv γ.toFun t
          else 0
    let A := fun ε => M ε - S' ε
    let G := ∫ t in γ.a..γ.b,
      g_reg (γ.toFun t) * deriv γ.toFun t
    Tendsto A (𝓝[>] 0) (𝓝 G) := by
  intro M S' A G
  have h_S'_eq :
      S' = fun ε =>
        ∑ s ∈ S0,
          ∫ t in γ.a..γ.b,
            if ‖γ.toFun t - s‖ > ε
            then (residueSimplePole f s /
              (γ.toFun t - s)) *
                deriv γ.toFun t
            else 0 := by
    ext ε
    simp only [S']
    rw [Finset.sum_attach S0
      (fun s => ∫ t in γ.a..γ.b,
        if ‖γ.toFun t - s‖ > ε
        then (residueSimplePole f s /
          (γ.toFun t - s)) * deriv γ.toFun t
        else 0)]
  exact
    dominated_convergence_multipoint_helper S0 f γ
      g_reg _h_crossing_null _hg_decomp hg_cont
      hS0_sep

/-- Multi-point PV equals sum of single-point PVs
when the regular part integral vanishes. -/
lemma multipointPV_eq_sum_of_integral_zero
    (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion)
    (_h_crossing_null : MeasureTheory.volume
      {t | t ∈ Icc γ.a γ.b ∧
        γ.toFun t ∈ (S0 : Set ℂ)} = 0)
    (_g_reg : ℂ → ℂ)
    (_hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = _g_reg z +
        ∑ s ∈ S0,
          residueSimplePole f s / (z - s))
    (_hg_cont : ContinuousOn _g_reg
      (γ.toFun '' Icc γ.a γ.b))
    (_hS0_sep : ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0,
      s ≠ s' → δ ≤ ‖s' - s‖)
    (_hg_zero : ∫ t in γ.a..γ.b,
      _g_reg (γ.toFun t) * deriv γ.toFun t = 0)
    (_hPV_exists : CauchyPrincipalValueExistsOn
      S0 f γ.toFun γ.a γ.b)
    (_hPV_each_tendsto : Tendsto
      (fun ε => ∑ s ∈ S0,
        ∫ t in γ.a..γ.b,
          if ‖γ.toFun t - s‖ > ε
          then (residueSimplePole f s /
            (γ.toFun t - s)) * deriv γ.toFun t
          else 0)
      (𝓝[>] 0)
      (𝓝 (∑ s ∈ S0,
        cauchyPrincipalValue'
          (fun z =>
            residueSimplePole f s / (z - s))
          γ.toFun γ.a γ.b s))) :
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      ∑ s ∈ S0,
        cauchyPrincipalValue'
          (fun z =>
            residueSimplePole f s / (z - s))
          γ.toFun γ.a γ.b s := by
  obtain ⟨L, hL⟩ := _hPV_exists
  have h_pv_eq_L :
      cauchyPrincipalValueOn S0 f γ.toFun
        γ.a γ.b = L :=
    hL.limUnder_eq
  have h_G_zero :
      ∫ t in γ.a..γ.b,
        _g_reg (γ.toFun t) *
          deriv γ.toFun t = 0 :=
    _hg_zero
  have h_A_tendsto :=
    multipointPV_diff_tendsto S0 f γ
      _h_crossing_null _g_reg _hg_decomp _hg_cont
      _hS0_sep
  simp only [h_G_zero] at h_A_tendsto
  let S'_attach := fun ε =>
    ∑ s ∈ S0.attach,
      ∫ t in γ.a..γ.b,
        if ‖γ.toFun t - s.val‖ > ε
        then (residueSimplePole f s.val /
          (γ.toFun t - s.val)) * deriv γ.toFun t
        else 0
  let S' := fun ε =>
    ∑ s ∈ S0,
      ∫ t in γ.a..γ.b,
        if ‖γ.toFun t - s‖ > ε
        then (residueSimplePole f s /
          (γ.toFun t - s)) * deriv γ.toFun t
        else 0
  have h_S'_eq : S' = S'_attach := by
    ext ε
    simp only [S', S'_attach]
    rw [Finset.sum_attach S0
      (fun s => ∫ t in γ.a..γ.b,
        if ‖γ.toFun t - s‖ > ε
        then (residueSimplePole f s /
          (γ.toFun t - s)) * deriv γ.toFun t
        else 0)]
  let Mf := fun ε =>
    ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 f
        γ.toFun ε t
  let Af := fun ε => Mf ε - S'_attach ε
  have h_S'_attach_tendsto :
      Tendsto S'_attach (𝓝[>] 0) (𝓝 L) := by
    have h_eq : S'_attach =
        fun ε => Mf ε - Af ε := by
      ext ε
      simp only [Mf, Af, S'_attach]
      ring
    have h_sub :
        Tendsto (fun ε => Mf ε - Af ε) (𝓝[>] 0)
          (𝓝 (L - 0)) :=
      hL.sub h_A_tendsto
    simp only [sub_zero] at h_sub
    rw [h_eq]
    exact h_sub
  have h_S'_tendsto :
      Tendsto S' (𝓝[>] 0) (𝓝 L) := by
    rw [h_S'_eq]
    exact h_S'_attach_tendsto
  have h_L_eq_sum :
      L = ∑ s ∈ S0,
        cauchyPrincipalValue'
          (fun z =>
            residueSimplePole f s / (z - s))
          γ.toFun γ.a γ.b s :=
    tendsto_nhds_unique h_S'_tendsto
      _hPV_each_tendsto
  rw [h_pv_eq_L, h_L_eq_sum]

end
