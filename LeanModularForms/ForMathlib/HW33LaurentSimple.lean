/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HW33LaurentPolarPart
import LeanModularForms.ForMathlib.HW33HoloCancel
import LeanModularForms.ForMathlib.HW33HigherOrderAuto
import LeanModularForms.ForMathlib.HW33SimpleClean
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Auto-discharge of `h_polar_cancel`, `hI_polar`, `hI_holo` under simple poles

This file uses the same analytic-correction strategy from
`HW33HoloCancel.h_holo_cancel_of_conditionB` to discharge the three remaining
oracle hypotheses of `hw_3_3_simple_with_crossData`:

* `h_polar_cancel` — `HasCauchyPVOn S (laurentHigherOrderPolar hCondB) γ 0`;
* `hI_polar` — interval-integrability of the cutoff polar-part integrand;
* `hI_holo` — interval-integrability of the cutoff holo-remainder integrand.

## Strategy

For the simple-pole case, at each pole `s ∈ S`:

* `laurentHigherOrderPolarAt s` is eventually equal to the analytic combination
  `regularPart - analyticPart` in the punctured nhd of `s`
  (`laurentHigherOrderPolarAt_eventuallyEq_analytic_of_crossed`).
* Hence `laurentHigherOrderPolar` (a finite sum over `S`) is also eventually
  equal to an analytic function at each `s ∈ S`.

Define `laurentHigherOrderPolarCorrection` mirroring
`laurentHolomorphicRemainderCorrection`: equal to `laurentHigherOrderPolar`
off `S`, and to the analytic limit at each `s ∈ S`. By the same Riemann
removable-singularity argument, the correction is differentiable on `U`.

Dixon ⟹ contour integral of correction along `γ` is zero. DCT then gives
`HasCauchyPVOn S correction γ 0`. Since `cpvIntegrandOn S original γ ε =
cpvIntegrandOn S correction γ ε` pointwise (the cutoff zeros out poles, and
off-poles the two functions agree), we conclude
`HasCauchyPVOn S original γ 0`.

The integrabilities `hI_polar`, `hI_holo` follow from the continuity of the
respective corrections via `cpvIntegrandOn_intervalIntegrable_of_contourIntegrand`.

## Main results

* `laurentHigherOrderPolar_eventuallyEq_analyticAt` — `laurentHigherOrderPolar`
  is eventually equal to an analytic function at every `s ∈ S`.
* `laurentHigherOrderPolarCorrection` — global analytic extension of
  `laurentHigherOrderPolar`.
* `laurentHigherOrderPolar_correction_differentiableOn` — the correction is
  differentiable on `U`.
* `h_polar_cancel_of_conditionB_simple` — discharges `h_polar_cancel`.
* `hI_polar_of_conditionB_simple` — discharges `hI_polar`.
* `hI_holo_of_conditionB_simple` — discharges `hI_holo`.
* `hw_3_3_simple_with_crossData_no_laurent_oracles` — the simple-pole HW
  Theorem 3.3 with all three Laurent oracles auto-discharged.
-/

open Set Filter Topology Complex MeasureTheory
open scoped Real Interval

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-! ## Step 1: `laurentHigherOrderPolar` is eventually analytic at each `s ∈ S` -/

/-- At any pole `s ∈ S` (whether crossed or not), the per-pole higher-order
polar contribution `laurentHigherOrderPolarAt s` is eventually equal to an
analytic function in the punctured nhd of `s`, given the simple-pole
hypothesis on `f`. -/
theorem laurentHigherOrderPolarAt_eventuallyEq_analyticAt
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s) {s : ℂ} (hs : s ∈ S) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧
      (laurentHigherOrderPolarAt hCondB s hs) =ᶠ[𝓝[≠] s] g := by
  classical
  by_cases h_cross : IsCrossed γ s
  · -- Crossed: polarPart - residue/(z-s) =ᶠ regularPart - analyticPart (analytic).
    refine ⟨fun z => (hSimple s hs).regularPart z - laurentAnalyticPartAt hCondB s hs z,
      (hSimple s hs).regularPart_analyticAt.sub
        (laurentAnalyticPartAt_analyticAt hCondB hs h_cross), ?_⟩
    have h_pole_eq := (hSimple s hs).eventually_eq
    have h_coeff_eq : (hSimple s hs).coeff = residue f s :=
      (residue_eq_coeff (hSimple s hs)).symm
    have h_laurent_eq := f_eq_analyticPart_plus_polarPart_eventually hCondB hs h_cross
    filter_upwards [h_pole_eq, h_laurent_eq] with z hz_pole hz_laurent
    have h_higher_eq : laurentHigherOrderPolarAt hCondB s hs z =
        laurentPolarPartAt hCondB s hs z - residue f s / (z - s) := by
      unfold laurentHigherOrderPolarAt
      rw [if_pos h_cross]
    rw [h_higher_eq, ← h_coeff_eq]
    linear_combination hz_pole - hz_laurent
  · -- Uncrossed: laurentHigherOrderPolarAt = 0 (trivially analytic).
    refine ⟨fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z _
    show laurentHigherOrderPolarAt hCondB s hs z = 0
    unfold laurentHigherOrderPolarAt
    rw [if_neg h_cross]

/-- `laurentHigherOrderPolar` (sum over `S`) is eventually equal to an analytic
function at every `s ∈ S`. -/
theorem laurentHigherOrderPolar_eventuallyEq_analyticAt
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s) {s : ℂ} (hs : s ∈ S) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧
      (laurentHigherOrderPolar hCondB) =ᶠ[𝓝[≠] s] g := by
  classical
  -- For each t ∈ S, get an analytic extension g_t of laurentHigherOrderPolarAt t.
  -- For t ≠ s, laurentHigherOrderPolarAt t is itself analytic at s (its singularity is at t ≠ s).
  -- For t = s, we use the simple-pole-derived extension.
  -- Sum these to get the analytic extension at s.
  -- The s-term: get g_s analytic and =ᶠ.
  obtain ⟨g_s, g_s_an, g_s_eq⟩ :=
    laurentHigherOrderPolarAt_eventuallyEq_analyticAt hCondB hSimple hs
  -- The rest of the sum (over t ∈ S.attach with t.1 ≠ s) is analytic at s.
  set rest : ℂ → ℂ :=
    fun z => ∑ t ∈ S.attach.filter (fun t => t.1 ≠ s),
      laurentHigherOrderPolarAt hCondB t.1 t.2 z with rest_def
  have rest_an : AnalyticAt ℂ rest s := by
    apply Finset.analyticAt_fun_sum
    intro t ht
    have h_ne : t.1 ≠ s := (Finset.mem_filter.mp ht).2
    -- laurentHigherOrderPolarAt t.1 is analytic at s when t.1 ≠ s (its singularity is at t.1).
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have h_open : IsOpen ({t.1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have h_mem : s ∈ ({t.1}ᶜ : Set ℂ) := mem_compl_singleton_iff.mpr h_ne.symm
    filter_upwards [h_open.mem_nhds h_mem] with z hz
    exact laurentHigherOrderPolarAt_differentiableAt hCondB t.2 (mem_compl_singleton_iff.mp hz)
  refine ⟨g_s + rest, g_s_an.add rest_an, ?_⟩
  -- laurentHigherOrderPolar = laurentHigherOrderPolarAt s + rest
  filter_upwards [g_s_eq] with z hz_eq
  show laurentHigherOrderPolar hCondB z = g_s z + rest z
  unfold laurentHigherOrderPolar
  rw [← Finset.sum_filter_add_sum_filter_not S.attach (fun t : {x // x ∈ S} => t.1 = s)
    (fun t => laurentHigherOrderPolarAt hCondB t.1 t.2 z)]
  have h_filter_eq : S.attach.filter (fun t : {x // x ∈ S} => t.1 = s) = {⟨s, hs⟩} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_attach, true_and, Finset.mem_singleton]
    exact ⟨fun h => Subtype.ext h, fun h => h ▸ rfl⟩
  rw [h_filter_eq, Finset.sum_singleton]
  show laurentHigherOrderPolarAt hCondB s hs z + _ = g_s z + rest z
  rw [hz_eq]

/-! ## Step 2: Global analytic correction of `laurentHigherOrderPolar` -/

/-- The "limit-corrected" higher-order polar part: equal to
`laurentHigherOrderPolar` away from `S`, and to the limit at each `s ∈ S`.
Mirrors `laurentHolomorphicRemainderCorrection`. -/
noncomputable def laurentHigherOrderPolarCorrection
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (z : ℂ) : ℂ :=
  open Classical in
  if z ∈ (↑S : Set ℂ) then limUnder (𝓝[≠] z) (laurentHigherOrderPolar hCondB)
  else laurentHigherOrderPolar hCondB z

/-- At a pole `z ∈ S`, the correction agrees with the analytic extension `g_z`
in a *full* neighbourhood of `z`. -/
private lemma laurentHigherOrderPolarCorrection_eventuallyEq_analyticExt
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {z : ℂ} (g_z : ℂ → ℂ)
    (hzS : z ∈ (↑S : Set ℂ)) (hg_z_an : AnalyticAt ℂ g_z z)
    (hg_z_eq : (laurentHigherOrderPolar hCondB) =ᶠ[𝓝[≠] z] g_z) :
    laurentHigherOrderPolarCorrection hCondB =ᶠ[𝓝 z] g_z := by
  classical
  have h_lim_eq : limUnder (𝓝[≠] z) (laurentHigherOrderPolar hCondB) = g_z z :=
    (hg_z_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      |>.congr' (hg_z_eq.mono fun _ h => h.symm)).limUnder_eq
  have h_at_z : laurentHigherOrderPolarCorrection hCondB z = g_z z := by
    simp only [laurentHigherOrderPolarCorrection, hzS, ↓reduceIte, h_lim_eq]
  have hz_not_erase : z ∉ (↑(S.erase z) : Set ℂ) := by
    simp only [Finset.mem_coe, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
      not_false_eq_true]
  obtain ⟨V, hV_open, hz_V, hV_eq⟩ := mem_nhdsWithin.mp hg_z_eq
  have h_erase_away : (↑(S.erase z) : Set ℂ)ᶜ ∈ 𝓝 z :=
    (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds hz_not_erase
  apply Filter.mem_of_superset (Filter.inter_mem (hV_open.mem_nhds hz_V) h_erase_away)
  intro w ⟨hw_V, hw_erase⟩
  by_cases hwz : w = z
  · rw [hwz]; exact h_at_z
  · have hw_not_S : w ∉ (↑S : Set ℂ) := by
      intro hmem
      exact hw_erase
        (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hwz, Finset.mem_coe.mp hmem⟩))
    have hcorr : laurentHigherOrderPolarCorrection hCondB w =
        laurentHigherOrderPolar hCondB w := by
      simp only [laurentHigherOrderPolarCorrection, hw_not_S, ↓reduceIte]
    show laurentHigherOrderPolarCorrection hCondB w = g_z w
    rw [hcorr]
    exact hV_eq ⟨hw_V, hwz⟩

/-- Away from `S`, the correction agrees with the polar in a full neighbourhood. -/
private lemma laurentHigherOrderPolarCorrection_eventuallyEq_polar
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {z : ℂ} (hzS : z ∉ (↑S : Set ℂ)) :
    laurentHigherOrderPolarCorrection hCondB =ᶠ[𝓝 z]
      laurentHigherOrderPolar hCondB := by
  apply Filter.mem_of_superset (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hzS)
  intro w hw
  have hw_not : w ∉ (↑S : Set ℂ) := hw
  show laurentHigherOrderPolarCorrection hCondB w = laurentHigherOrderPolar hCondB w
  simp only [laurentHigherOrderPolarCorrection, hw_not, ↓reduceIte]

/-- The corrected higher-order polar part is differentiable on all of `U`.
Riemann removable-singularity bridge. -/
theorem laurentHigherOrderPolar_correction_differentiableOn
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    {U : Set ℂ} (hU : IsOpen U) (hS_in_U : ↑S ⊆ U) :
    DifferentiableOn ℂ (laurentHigherOrderPolarCorrection hCondB) U := by
  intro z hz
  by_cases hzS : z ∈ (↑S : Set ℂ)
  · obtain ⟨g_z, hg_z_an, hg_z_eq⟩ :=
      laurentHigherOrderPolar_eventuallyEq_analyticAt hCondB hSimple
        (Finset.mem_coe.mp hzS)
    have h_evEq :=
      laurentHigherOrderPolarCorrection_eventuallyEq_analyticExt hCondB g_z hzS
        hg_z_an hg_z_eq
    exact (hg_z_an.differentiableAt.congr_of_eventuallyEq
      h_evEq).differentiableWithinAt
  · have h_polar_diff : DifferentiableAt ℂ (laurentHigherOrderPolar hCondB) z :=
      laurentHigherOrderPolar_differentiableAt hCondB hzS
    exact (h_polar_diff.congr_of_eventuallyEq
      (laurentHigherOrderPolarCorrection_eventuallyEq_polar hCondB hzS)).differentiableWithinAt

/-! ## Step 3: cpvIntegrandOn pointwise equality between original and correction -/

/-- For any `ε > 0`, the cpv integrand for `laurentHigherOrderPolar` equals
the cpv integrand for its correction pointwise. The cutoff zeros out poles
(where the two functions differ), and off-poles they agree. -/
private lemma cpvIntegrandOn_polar_eq_correction
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {ε : ℝ} (hε_pos : 0 < ε) (t : ℝ) :
    cpvIntegrandOn S (laurentHigherOrderPolar hCondB)
        γ.toPiecewiseC1Path.toPath.extend ε t =
      cpvIntegrandOn S (laurentHigherOrderPolarCorrection hCondB)
        γ.toPiecewiseC1Path.toPath.extend ε t := by
  by_cases h_cutoff :
      ∃ s ∈ S, ‖γ.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε
  · simp only [cpvIntegrandOn, if_pos h_cutoff]
  · simp only [cpvIntegrandOn, if_neg h_cutoff]
    have h_not : γ.toPiecewiseC1Path.toPath.extend t ∉ (↑S : Set ℂ) := by
      intro h_in
      apply h_cutoff
      refine ⟨γ.toPiecewiseC1Path.toPath.extend t, Finset.mem_coe.mp h_in, ?_⟩
      simp only [sub_self, norm_zero]
      exact le_of_lt hε_pos
    have h_eq : laurentHigherOrderPolarCorrection hCondB
        (γ.toPiecewiseC1Path.toPath.extend t) =
          laurentHigherOrderPolar hCondB (γ.toPiecewiseC1Path.toPath.extend t) := by
      simp only [laurentHigherOrderPolarCorrection, h_not, ↓reduceIte]
    rw [h_eq]

/-- Likewise for `laurentHolomorphicRemainder` and its correction. -/
private lemma cpvIntegrandOn_holo_eq_correction
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {ε : ℝ} (hε_pos : 0 < ε) (t : ℝ) :
    cpvIntegrandOn S (laurentHolomorphicRemainder hCondB)
        γ.toPiecewiseC1Path.toPath.extend ε t =
      cpvIntegrandOn S (laurentHolomorphicRemainderCorrection hCondB)
        γ.toPiecewiseC1Path.toPath.extend ε t := by
  by_cases h_cutoff :
      ∃ s ∈ S, ‖γ.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε
  · simp only [cpvIntegrandOn, if_pos h_cutoff]
  · simp only [cpvIntegrandOn, if_neg h_cutoff]
    have h_not : γ.toPiecewiseC1Path.toPath.extend t ∉ (↑S : Set ℂ) := by
      intro h_in
      apply h_cutoff
      refine ⟨γ.toPiecewiseC1Path.toPath.extend t, Finset.mem_coe.mp h_in, ?_⟩
      simp only [sub_self, norm_zero]
      exact le_of_lt hε_pos
    have h_eq : laurentHolomorphicRemainderCorrection hCondB
        (γ.toPiecewiseC1Path.toPath.extend t) =
          laurentHolomorphicRemainder hCondB (γ.toPiecewiseC1Path.toPath.extend t) := by
      simp only [laurentHolomorphicRemainderCorrection, h_not, ↓reduceIte]
    rw [h_eq]

/-! ## Step 4: Discharge `h_polar_cancel` via Dixon-on-correction + integrand equality -/

/-- **Auto-discharge of `h_polar_cancel`** under simple-pole hypothesis and
condition (B), via the analytic correction trick. -/
theorem h_polar_cancel_of_conditionB_simple
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ}
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S) :
    HasCauchyPVOn S (laurentHigherOrderPolar hCondB)
      γ.toPwC1Immersion.toPiecewiseC1Path 0 := by
  classical
  set γP := γ.toPwC1Immersion.toPiecewiseC1Path with hγP_def
  set γE := γP.toPath.extend with hγE_def
  set corr := laurentHigherOrderPolarCorrection hCondB with hcorr_def
  set polar := laurentHigherOrderPolar hCondB with hpolar_def
  have h_preimage : Set.Countable
      {t ∈ Icc (0 : ℝ) 1 | γ.toPwC1Immersion.toPiecewiseC1Path t ∈ (↑S : Set ℂ)} :=
    γ.preimage_countable S
  have hcorr_diff : DifferentiableOn ℂ corr U :=
    laurentHigherOrderPolar_correction_differentiableOn hCondB hSimple hU_open hS_in_U
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  have h_corr_zero : γP.contourIntegral corr = 0 :=
    contourIntegral_analytic_eq_zero_of_nullHomologous hU_open hU_ne hcorr_diff
      γ.toPwC1Immersion h_null hLip
  have hcorr_cont : ContinuousOn corr (γE '' Icc (0 : ℝ) 1) := by
    have hγE_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γE t ∈ U := h_null.image_subset
    refine hcorr_diff.continuousOn.mono ?_
    intro z hz
    obtain ⟨t, ht, hzeq⟩ := hz
    rw [← hzeq]
    exact hγE_in_U t ht
  have h_cpv_corr : HasCauchyPVOn S corr γP (γP.contourIntegral corr) :=
    hasCauchyPVOn_continuousOn_of_countable_preimage S hcorr_cont hLip h_preimage
  have h_cpv_polar : HasCauchyPVOn S polar γP 0 := by
    have h_target_eq : (0 : ℂ) = γP.contourIntegral corr := h_corr_zero.symm
    rw [h_target_eq]
    refine h_cpv_corr.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    apply intervalIntegral.integral_congr
    intro t _
    exact (cpvIntegrandOn_polar_eq_correction hCondB hε_pos t).symm
  exact h_cpv_polar

/-! ## Step 5: Discharge `hI_polar` and `hI_holo` -/

/-- **Auto-discharge of `hI_polar`** under simple-pole hypothesis and condition (B). -/
theorem hI_polar_of_conditionB_simple
    {U : Set ℂ} (hU_open : IsOpen U)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ}
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S) :
    ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (laurentHigherOrderPolar hCondB)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1 := by
  classical
  intro ε hε_pos
  set γP := γ.toPwC1Immersion.toPiecewiseC1Path with hγP_def
  set γE := γP.toPath.extend with hγE_def
  set corr := laurentHigherOrderPolarCorrection hCondB with hcorr_def
  have hcorr_diff : DifferentiableOn ℂ corr U :=
    laurentHigherOrderPolar_correction_differentiableOn hCondB hSimple hU_open hS_in_U
  have hcorr_cont_image : ContinuousOn corr (γE '' Icc (0 : ℝ) 1) := by
    have hγE_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γE t ∈ U := h_null.image_subset
    refine hcorr_diff.continuousOn.mono ?_
    intro z hz
    obtain ⟨t, ht, hzeq⟩ := hz
    rw [← hzeq]
    exact hγE_in_U t ht
  -- contour integrand `corr(γE t) · γE'(t)` is interval-integrable
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  have h_deriv_int : IntervalIntegrable (deriv γE) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
    refine MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (stronglyMeasurable_deriv _).aestronglyMeasurable
      (ae_restrict_of_ae (Filter.Eventually.of_forall
        (fun _ => norm_deriv_le_of_lipschitz hLip)))
  have h_corr_γE_cont : ContinuousOn (fun t => corr (γE t)) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (zero_le_one' ℝ)]
    exact hcorr_cont_image.comp γP.toPath.continuous_extend.continuousOn
      (fun t ht => ⟨t, ht, rfl⟩)
  have h_contour_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand corr γP) volume 0 1 :=
    h_deriv_int.continuousOn_mul h_corr_γE_cont
  have h_corr_intIntegrable :
      IntervalIntegrable (fun t => cpvIntegrandOn S corr γE ε t) volume 0 1 :=
    cpvIntegrandOn_intervalIntegrable_of_contourIntegrand S corr γP ε h_contour_int
  -- Now use the pointwise equality of integrands.
  refine h_corr_intIntegrable.congr ?_
  intro t _
  exact (cpvIntegrandOn_polar_eq_correction hCondB hε_pos t).symm

/-- **Auto-discharge of `hI_holo`** under simple-pole hypothesis and condition (B). -/
theorem hI_holo_of_conditionB_simple
    {U : Set ℂ} (hU_open : IsOpen U)
    {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S) :
    ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (laurentHolomorphicRemainder hCondB)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1 := by
  classical
  intro ε hε_pos
  set γP := γ.toPwC1Immersion.toPiecewiseC1Path with hγP_def
  set γE := γP.toPath.extend with hγE_def
  set corr := laurentHolomorphicRemainderCorrection hCondB with hcorr_def
  have hcorr_diff : DifferentiableOn ℂ corr U :=
    laurentHolomorphicRemainder_correction_differentiableOn hCondB hSimple hU_open hf
  have hcorr_cont_image : ContinuousOn corr (γE '' Icc (0 : ℝ) 1) := by
    have hγE_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γE t ∈ U := h_null.image_subset
    refine hcorr_diff.continuousOn.mono ?_
    intro z hz
    obtain ⟨t, ht, hzeq⟩ := hz
    rw [← hzeq]
    exact hγE_in_U t ht
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  have h_deriv_int : IntervalIntegrable (deriv γE) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
    refine MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (stronglyMeasurable_deriv _).aestronglyMeasurable
      (ae_restrict_of_ae (Filter.Eventually.of_forall
        (fun _ => norm_deriv_le_of_lipschitz hLip)))
  have h_corr_γE_cont : ContinuousOn (fun t => corr (γE t)) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (zero_le_one' ℝ)]
    exact hcorr_cont_image.comp γP.toPath.continuous_extend.continuousOn
      (fun t ht => ⟨t, ht, rfl⟩)
  have h_contour_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand corr γP) volume 0 1 :=
    h_deriv_int.continuousOn_mul h_corr_γE_cont
  have h_corr_intIntegrable :
      IntervalIntegrable (fun t => cpvIntegrandOn S corr γE ε t) volume 0 1 :=
    cpvIntegrandOn_intervalIntegrable_of_contourIntegrand S corr γP ε h_contour_int
  refine h_corr_intIntegrable.congr ?_
  intro t _
  exact (cpvIntegrandOn_holo_eq_correction hCondB hε_pos t).symm

/-! ## Final: HW Theorem 3.3 with all three Laurent oracles auto-discharged -/

/-- **HW Theorem 3.3 — simple-pole case with crossings, all Laurent oracles auto-discharged.**

Compared to `hw_3_3_simple_with_crossData`, this theorem drops the three Laurent
oracle hypotheses `h_polar_cancel`, `hI_polar`, `hI_holo` and instead derives
them from `hCondB` + the simple-pole hypothesis `hSimple` via the analytic
correction trick (`laurentHigherOrderPolarCorrection`).

Remaining hypotheses:
* `hCondA` — Condition (A') for the curve.
* `hCondB` — Condition (B) for the Laurent decomposition.
* `crossData` — per-pole `SingleCrossingData γ s` for the geometric crossings.
* `hδ_pos`, `h_avoid_pairs` — pairwise avoidance margins.
* `h_int_perpole` — per-pole CPV-integrand integrability for `residue / (z - s)`. -/
theorem hw_3_3_simple_with_crossData_no_laurent_oracles
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (crossData : ∀ s ∈ S,
      SingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (h_avoid_pairs : ∀ s ∈ S, ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc (0 : ℝ) 1,
      δ ≤ ‖γ.toPwC1Immersion.toPiecewiseC1Path t - s'‖)
    (h_int_perpole : ∀ s ∈ S, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => residue f s / (z - s))
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  -- Discharge the three Laurent oracles, then call `hw_3_3_simple_with_crossData`.
  have h_polar_cancel := h_polar_cancel_of_conditionB_simple hU_open hU_ne hS_in_U γ
    h_null hSimple hCondB
  have hI_polar := hI_polar_of_conditionB_simple hU_open hS_in_U γ h_null hSimple hCondB
  have hI_holo := hI_holo_of_conditionB_simple hU_open hS_in_U hf γ h_null hSimple hCondB
  exact hw_3_3_simple_with_crossData hU_open hU_ne S hS_in_U f hf γ h_null
    hSimple hCondA hCondB h_polar_cancel hI_polar hI_holo crossData hδ_pos
    h_avoid_pairs h_int_perpole

end LeanModularForms

end
