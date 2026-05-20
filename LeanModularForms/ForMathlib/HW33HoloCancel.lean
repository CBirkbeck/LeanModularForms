/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import LeanModularForms.ForMathlib.HW33LaurentPolarPart
import LeanModularForms.ForMathlib.HigherOrderAssembly
import LeanModularForms.ForMathlib.PaperPwC1Immersion

/-!
# HW Theorem 3.3 — discharge `h_holo_cancel` under (B) + null-homology + simple poles

This file discharges the `h_holo_cancel` oracle in `hw_3_3_paper`/`hw_3_3_tight` for
the simple-pole case under condition (B) and null-homology, given a countable
preimage hypothesis for `γ⁻¹(S) ∩ [0,1]`.

## Strategy

1. **Local analytic extension** at each `s ∈ S` (Phase 3.3, file
   `HW33LaurentPolarPart`): the remainder is eventually equal to an analytic
   function in a punctured neighbourhood.
2. **Global analytic correction** via Riemann removable singularity: define
   `laurentHolomorphicRemainderCorrection` by setting it equal to
   `laurentHolomorphicRemainder` off `S` and to the limit at each `s ∈ S`.
3. **Cauchy via Dixon**: `correction` analytic on `U` and `γ` null-homologous in
   `U` give `γ.contourIntegral correction = 0`.
4. **CPV→contour bridge** via dominated convergence: under countable preimage
   along `γ`, the ε-truncated CPV integrand for `correction` converges to its
   contour integral as `ε → 0⁺`.
5. **Integrand equality**: the CPV integrand of `laurentHolomorphicRemainder`
   coincides with that of `correction` pointwise (the cutoff zeroes out the
   only difference), transferring the CPV vanishing.

## Main result

* `h_holo_cancel_of_conditionB` — discharges `h_holo_cancel` under (B) +
  null-homology + simple poles + countable preimage of `S` along `γ`.
-/

open Set Filter Topology Complex MeasureTheory
open scoped Real Interval

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-- The "limit-corrected" remainder: equal to `laurentHolomorphicRemainder` away
from `S`, and to the limit at each `s ∈ S`. Mirrors `MeromorphicCauchy.correction`
for simple poles but routes through
`laurentHolomorphicRemainder_eventuallyEq_analyticAt`. -/
noncomputable def laurentHolomorphicRemainderCorrection
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (z : ℂ) : ℂ :=
  open Classical in
  if z ∈ (↑S : Set ℂ) then limUnder (𝓝[≠] z) (laurentHolomorphicRemainder hCondB)
  else laurentHolomorphicRemainder hCondB z

private lemma laurentHolomorphicRemainderCorrection_eventuallyEq_analyticExt
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {z : ℂ} (g_z : ℂ → ℂ)
    (hzS : z ∈ (↑S : Set ℂ)) (hg_z_an : AnalyticAt ℂ g_z z)
    (hg_z_eq : (laurentHolomorphicRemainder hCondB) =ᶠ[𝓝[≠] z] g_z) :
    laurentHolomorphicRemainderCorrection hCondB =ᶠ[𝓝 z] g_z := by
  have h_lim_eq : limUnder (𝓝[≠] z) (laurentHolomorphicRemainder hCondB) = g_z z :=
    (hg_z_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      |>.congr' hg_z_eq.symm).limUnder_eq
  have h_at_z : laurentHolomorphicRemainderCorrection hCondB z = g_z z := by
    simp only [laurentHolomorphicRemainderCorrection, hzS, ↓reduceIte, h_lim_eq]
  have hz_not_erase : z ∉ (↑(S.erase z) : Set ℂ) := by simp
  obtain ⟨V, hV_open, hz_V, hV_eq⟩ := mem_nhdsWithin.mp hg_z_eq
  have h_erase_away : (↑(S.erase z) : Set ℂ)ᶜ ∈ 𝓝 z :=
    (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds hz_not_erase
  apply Filter.mem_of_superset (Filter.inter_mem (hV_open.mem_nhds hz_V) h_erase_away)
  intro w ⟨hw_V, hw_erase⟩
  by_cases hwz : w = z
  · exact hwz ▸ h_at_z
  · have hw_not_S : w ∉ (↑S : Set ℂ) := fun hmem =>
      hw_erase <| Finset.mem_coe.mpr <| Finset.mem_erase.mpr ⟨hwz, hmem⟩
    change laurentHolomorphicRemainderCorrection hCondB w = g_z w
    simp only [laurentHolomorphicRemainderCorrection, hw_not_S, ↓reduceIte]
    exact hV_eq ⟨hw_V, hwz⟩

private lemma laurentHolomorphicRemainderCorrection_eventuallyEq_rem
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {z : ℂ} (hzS : z ∉ (↑S : Set ℂ)) :
    laurentHolomorphicRemainderCorrection hCondB =ᶠ[𝓝 z]
      laurentHolomorphicRemainder hCondB := by
  apply Filter.mem_of_superset (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hzS)
  intro w (hw_not : w ∉ (↑S : Set ℂ))
  change laurentHolomorphicRemainderCorrection hCondB w = laurentHolomorphicRemainder hCondB w
  simp only [laurentHolomorphicRemainderCorrection, hw_not, ↓reduceIte]

/-- **Phase 4 / Step 2**: the corrected remainder is differentiable on all of
`U`. Riemann removable-singularity bridge. -/
theorem laurentHolomorphicRemainder_correction_differentiableOn
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ ↑S)) :
    DifferentiableOn ℂ (laurentHolomorphicRemainderCorrection hCondB) U := by
  intro z hz
  by_cases hzS : z ∈ (↑S : Set ℂ)
  · obtain ⟨g_z, hg_z_an, hg_z_eq⟩ :=
      laurentHolomorphicRemainder_eventuallyEq_analyticAt hCondB hSimple
        (Finset.mem_coe.mp hzS)
    have h_evEq :=
      laurentHolomorphicRemainderCorrection_eventuallyEq_analyticExt hCondB g_z hzS
        hg_z_an hg_z_eq
    exact (hg_z_an.differentiableAt.congr_of_eventuallyEq h_evEq).differentiableWithinAt
  · have h_rem_diff : DifferentiableAt ℂ (laurentHolomorphicRemainder hCondB) z :=
      ((laurentHolomorphicRemainder_differentiableOn hCondB hU hf z ⟨hz, hzS⟩).differentiableAt
        ((hU.sdiff S.finite_toSet.isClosed).mem_nhds ⟨hz, hzS⟩))
    exact (h_rem_diff.congr_of_eventuallyEq
      (laurentHolomorphicRemainderCorrection_eventuallyEq_rem hCondB hzS)).differentiableWithinAt

/-- For a null-homologous closed piecewise-`C¹` immersion `γ` and a function `g`
differentiable on an open `U`, the contour integral of `g` along `γ` is zero. -/
theorem contourIntegral_analytic_eq_zero_of_nullHomologous
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    {K : NNReal} (hLip : LipschitzWith K γ.toPiecewiseC1Path.toPath.extend) :
    γ.toPiecewiseC1Path.contourIntegral g = 0 := by
  set γP : PiecewiseC1Path x x := γ.toPiecewiseC1Path
  obtain ⟨w₀, hw₀_in_U, hw₀_off⟩ :=
    ForMathlib.exists_mem_not_mem_path_image_of_isOpen γP hU_open hU_ne hLip
  obtain ⟨δ', hδ'_pos, hδ'_bound⟩ := avoids_delta_bound γP w₀ hw₀_off
  have hG_diff : DifferentiableOn ℂ (fun z => (z - w₀) * g z) U :=
    fun z hz => ((differentiableAt_id.sub_const w₀).differentiableWithinAt).mul
      (hg z hz)
  have h_dixon_G : ∀ w,
      dixonFunction (fun z => (z - w₀) * g z) U γP w = 0 :=
    dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded hU_open hG_diff
      γ h_null hLip
      (fun w hw_notin h_avoid_local =>
        h_null.winding_zero_nhds_of_not_mem_of_closed hw_notin h_avoid_local hLip)
  have h_deriv_int : IntervalIntegrable (deriv γP.toPath.extend)
      MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
    refine MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (stronglyMeasurable_deriv _).aestronglyMeasurable
      (ae_restrict_of_ae (Filter.Eventually.of_forall
        (fun _ => norm_deriv_le_of_lipschitz hLip)))
  have h_inv_cont : ContinuousOn
      (fun t => (γP t - w₀)⁻¹) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (zero_le_one' ℝ)]
    refine ContinuousOn.inv₀
      (γP.toPath.continuous_extend.continuousOn.sub continuousOn_const) ?_
    intro t ht heq
    have := hδ'_bound t ht
    rw [heq, norm_zero] at this
    linarith
  have h_base_int : IntervalIntegrable
      (fun t => (γP t - w₀)⁻¹ * deriv γP.toPath.extend t)
      MeasureTheory.volume 0 1 :=
    h_deriv_int.continuousOn_mul h_inv_cont
  have h_g_curve_cont : ContinuousOn (fun t => g (γP t)) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (zero_le_one' ℝ)]
    exact hg.continuousOn.comp γP.toPath.continuous_extend.continuousOn
      h_null.image_subset
  have h_g_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand g γP)
      MeasureTheory.volume 0 1 :=
    h_deriv_int.continuousOn_mul h_g_curve_cont
  have h_cauchy_int : IntervalIntegrable
      (fun t => (γP t - w₀) * g (γP t) / (γP t - w₀) *
        deriv γP.toPath.extend t) MeasureTheory.volume 0 1 := by
    refine h_g_int.congr fun t ht => ?_
    rw [uIoc_of_le (zero_le_one' ℝ)] at ht
    have h : γP t - w₀ ≠ 0 := sub_ne_zero.mpr (hw₀_off t (Ioc_subset_Icc_self ht))
    show PiecewiseC1Path.contourIntegrand g γP t = _
    unfold PiecewiseC1Path.contourIntegrand
    rw [show (γP t - w₀) * g (γP t) / (γP t - w₀) = g (γP t) from by field_simp]
  exact contourIntegral_eq_zero_of_nullHomologous_at w₀ hw₀_in_U hw₀_off
    (h_dixon_G w₀) h_cauchy_int h_base_int

private lemma cpvCutoff_isClosed {γE : ℝ → ℂ} (hγE : Continuous γE) (S : Finset ℂ)
    (ε : ℝ) :
    IsClosed {t : ℝ | ∃ s ∈ S, ‖γE t - s‖ ≤ ε} := by
  have hset_eq : {t : ℝ | ∃ s ∈ S, ‖γE t - s‖ ≤ ε} =
      ⋃ s ∈ S, {t : ℝ | ‖γE t - s‖ ≤ ε} := by ext; simp
  rw [hset_eq]
  exact S.finite_toSet.isClosed_biUnion fun s _ =>
    isClosed_le (continuous_norm.comp (hγE.sub continuous_const)) continuous_const

private lemma cpvCutoff_measurableSet {γE : ℝ → ℂ} (hγE : Continuous γE) (S : Finset ℂ)
    (ε : ℝ) :
    MeasurableSet {t : ℝ | ∃ s ∈ S, ‖γE t - s‖ ≤ ε} :=
  (cpvCutoff_isClosed hγE S ε).measurableSet

private lemma cpvIntegrandOn_tendsto_pointwise_of_not_mem
    {γE : ℝ → ℂ} {S : Finset ℂ} {g : ℂ → ℂ} {t : ℝ}
    (h_not_mem : γE t ∉ (↑S : Set ℂ)) :
    Tendsto (fun ε => cpvIntegrandOn S g γE ε t) (𝓝[>] 0)
      (𝓝 (g (γE t) * deriv γE t)) := by
  by_cases hS : S.Nonempty
  · set δ : ℝ := S.inf' hS (fun s => ‖γE t - s‖)
    have hδ_pos : 0 < δ :=
      (Finset.lt_inf'_iff _).2 fun s hs => norm_pos_iff.mpr fun h_eq =>
        h_not_mem (sub_eq_zero.mp h_eq ▸ Finset.mem_coe.mpr hs)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
    simp only [mem_Ioo] at hε
    exact (cpvIntegrandOn_of_forall_gt fun s hs => hε.2.trans_le (Finset.inf'_le _ hs)).symm
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hS
    exact Tendsto.congr (fun _ => cpvIntegrandOn_empty.symm) tendsto_const_nhds

private lemma norm_cpvIntegrandOn_le {S : Finset ℂ} {g : ℂ → ℂ} {γE : ℝ → ℂ}
    {ε : ℝ} {t : ℝ} :
    ‖cpvIntegrandOn S g γE ε t‖ ≤ ‖g (γE t)‖ * ‖deriv γE t‖ := by
  rw [cpvIntegrandOn]; split_ifs <;> simp [mul_nonneg, norm_nonneg]

/-- **DCT-based CPV→contour bridge** for continuous `g` on the curve image,
under the hypothesis that `γ⁻¹(S) ∩ [0,1]` is at most countable. The ε-truncated
CPV integral converges to the contour integral. -/
theorem hasCauchyPVOn_continuousOn_of_countable_preimage
    {γ : PiecewiseC1Path x x} (S : Finset ℂ) {g : ℂ → ℂ}
    (h_g_cont : ContinuousOn g (γ.toPath.extend '' Icc (0 : ℝ) 1))
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend)
    (h_preimage : Set.Countable {t ∈ Icc (0 : ℝ) 1 | γ t ∈ (↑S : Set ℂ)}) :
    HasCauchyPVOn S g γ (γ.contourIntegral g) := by
  set γE := γ.toPath.extend
  have hγE_cont : Continuous γE := γ.toPath.continuous_extend
  have h_compact : IsCompact (γE '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image hγE_cont
  obtain ⟨M, hM⟩ := h_compact.bddAbove_image h_g_cont.norm
  set M' : ℝ := max M 0
  have hM_bound : ∀ t ∈ Icc (0 : ℝ) 1, ‖g (γE t)‖ ≤ M' := fun t ht =>
    le_max_of_le_left (hM ⟨γE t, ⟨t, ht, rfl⟩, rfl⟩)
  have h_deriv_bd : ∀ t, ‖deriv γE t‖ ≤ (K : ℝ) :=
    fun _ => norm_deriv_le_of_lipschitz hLip
  set bound : ℝ → ℝ := fun _ => M' * (K : ℝ)
  have h_bound_int : IntervalIntegrable bound volume 0 1 :=
    intervalIntegrable_const
  have h_gγE_cont_Icc : ContinuousOn (fun t => g (γE t)) (Icc (0 : ℝ) 1) :=
    h_g_cont.comp hγE_cont.continuousOn (fun t ht => ⟨t, ht, rfl⟩)
  have h_gγE_aem : AEStronglyMeasurable (fun t => g (γE t))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (h_gγE_cont_Icc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have h_cutoff_aem : ∀ ε,
      AEStronglyMeasurable (cpvIntegrandOn S g γE ε) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    intro ε
    have hA_meas : MeasurableSet {t : ℝ | ∃ s ∈ S, ‖γE t - s‖ ≤ ε} :=
      cpvCutoff_measurableSet hγE_cont S ε
    have h_full : AEStronglyMeasurable (fun t => g (γE t) * deriv γE t)
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      h_gγE_aem.mul (stronglyMeasurable_deriv γE).aestronglyMeasurable
    have h_piecewise : AEStronglyMeasurable
        (Set.piecewise {t : ℝ | ∃ s ∈ S, ‖γE t - s‖ ≤ ε} (fun _ => (0 : ℂ))
          (fun t => g (γE t) * deriv γE t))
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      AEStronglyMeasurable.piecewise hA_meas
        aestronglyMeasurable_zero.restrict h_full.restrict
    exact h_piecewise.congr (ae_of_all _ fun t => by simp [cpvIntegrandOn, Set.piecewise])
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    bound ?_ ?_ h_bound_int ?_
  · filter_upwards [self_mem_nhdsWithin] with ε _
    rw [show Ι (0 : ℝ) 1 = Ioc 0 1 from uIoc_of_le (zero_le_one' ℝ)]
    exact h_cutoff_aem ε
  · filter_upwards [self_mem_nhdsWithin] with ε _
    refine ae_of_all _ fun t ht_uIoc => ?_
    have ht_Ioc : t ∈ Ioc (0 : ℝ) 1 := by rwa [uIoc_of_le (zero_le_one' ℝ)] at ht_uIoc
    have ht_Icc : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht_Ioc
    calc ‖cpvIntegrandOn S g γE ε t‖
        ≤ ‖g (γE t)‖ * ‖deriv γE t‖ := norm_cpvIntegrandOn_le
      _ ≤ M' * (K : ℝ) := by
          gcongr
          · exact hM_bound t ht_Icc
          · exact h_deriv_bd t
  · filter_upwards [h_preimage.ae_notMem volume] with t ht_notmem ht_uIoc
    have ht_Ioc : t ∈ Ioc (0 : ℝ) 1 := by rwa [uIoc_of_le (zero_le_one' ℝ)] at ht_uIoc
    have ht_Icc : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht_Ioc
    exact cpvIntegrandOn_tendsto_pointwise_of_not_mem
      fun h_in => ht_notmem ⟨ht_Icc, h_in⟩

/-- **Phase 4 main theorem**: discharge the `h_holo_cancel` oracle in
`hw_3_3_paper` / `hw_3_3_tight` for the simple-pole case under condition (B),
null-homology, and simple poles.

The countable-preimage condition on `γ⁻¹(S) ∩ [0,1]` is discharged automatically
via `ClosedPwC1Immersion.preimage_countable`: a paper-faithful piecewise `C¹`
immersion has only finitely many crossings of any finite set `S`, hence the
preimage is countable (in fact finite).

The proof routes through three steps:
1. The remainder admits a global analytic correction on `U`
   (`laurentHolomorphicRemainder_correction_differentiableOn`).
2. The correction's contour integral along `γ` is zero by Dixon
   (`contourIntegral_analytic_eq_zero_of_nullHomologous`).
3. The CPV of the correction equals its contour integral by dominated
   convergence (`hasCauchyPVOn_continuousOn_of_countable_preimage`).
4. The CPV of the original remainder equals that of the correction because the
   cutoff integrands coincide pointwise on `[0,1]`. -/
theorem h_holo_cancel_of_conditionB
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S) :
    HasCauchyPVOn S (laurentHolomorphicRemainder hCondB)
      γ.toPwC1Immersion.toPiecewiseC1Path 0 := by
  set γP := γ.toPwC1Immersion.toPiecewiseC1Path
  set γE := γP.toPath.extend
  set corr := laurentHolomorphicRemainderCorrection hCondB
  set rem := laurentHolomorphicRemainder hCondB
  have h_preimage : Set.Countable
      {t ∈ Icc (0 : ℝ) 1 | γ.toPwC1Immersion.toPiecewiseC1Path t ∈ (↑S : Set ℂ)} :=
    γ.preimage_countable S
  have hcorr_diff : DifferentiableOn ℂ corr U :=
    laurentHolomorphicRemainder_correction_differentiableOn hCondB hSimple hU_open hf
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  have h_corr_zero : γP.contourIntegral corr = 0 :=
    contourIntegral_analytic_eq_zero_of_nullHomologous hU_open hU_ne hcorr_diff
      γ.toPwC1Immersion h_null hLip
  have hcorr_cont : ContinuousOn corr (γE '' Icc (0 : ℝ) 1) :=
    hcorr_diff.continuousOn.mono (Set.image_subset_iff.mpr h_null.image_subset)
  have h_cpv_corr : HasCauchyPVOn S corr γP (γP.contourIntegral corr) :=
    hasCauchyPVOn_continuousOn_of_countable_preimage S hcorr_cont hLip h_preimage
  rw [← h_corr_zero]
  refine h_cpv_corr.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε_pos
  apply intervalIntegral.integral_congr
  intro t _
  by_cases h_cutoff : ∃ s ∈ S, ‖γP.toPath.extend t - s‖ ≤ ε
  · simp only [cpvIntegrandOn, if_pos h_cutoff]
  · have h_not : γP.toPath.extend t ∉ (↑S : Set ℂ) := fun h_in =>
      h_cutoff ⟨γP.toPath.extend t, Finset.mem_coe.mp h_in, by simpa using hε_pos.le⟩
    have h_rem_corr : corr (γP.toPath.extend t) = rem (γP.toPath.extend t) := by
      change laurentHolomorphicRemainderCorrection hCondB _ =
        laurentHolomorphicRemainder hCondB _
      simp only [laurentHolomorphicRemainderCorrection, h_not, ↓reduceIte]
    simp only [cpvIntegrandOn, if_neg h_cutoff, h_rem_corr]

end LeanModularForms

end
