/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.RemovableSingularity
import LeanModularForms.ForMathlib.HW33HigherOrder
import LeanModularForms.ForMathlib.HW33HoloCancel
import LeanModularForms.ForMathlib.HW33LaurentPolarPart
import LeanModularForms.ForMathlib.HW33SimpleClean

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
  · refine ⟨fun z => (hSimple s hs).regularPart z - laurentAnalyticPartAt hCondB s hs z,
      (hSimple s hs).regularPart_analyticAt.sub
        (laurentAnalyticPartAt_analyticAt hCondB hs h_cross), ?_⟩
    filter_upwards [(hSimple s hs).eventually_eq,
      f_eq_analyticPart_plus_polarPart_eventually hCondB hs h_cross] with z hz_pole hz_laurent
    simp only [laurentHigherOrderPolarAt, if_pos h_cross, residue_eq_coeff (hSimple s hs)]
    linear_combination hz_pole - hz_laurent
  · refine ⟨fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z _
    simp only [laurentHigherOrderPolarAt, if_neg h_cross]

/-- `laurentHigherOrderPolar` (sum over `S`) is eventually equal to an analytic
function at every `s ∈ S`. -/
theorem laurentHigherOrderPolar_eventuallyEq_analyticAt
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s) {s : ℂ} (hs : s ∈ S) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧
      (laurentHigherOrderPolar hCondB) =ᶠ[𝓝[≠] s] g := by
  classical
  obtain ⟨g_s, g_s_an, g_s_eq⟩ :=
    laurentHigherOrderPolarAt_eventuallyEq_analyticAt hCondB hSimple hs
  set rest : ℂ → ℂ :=
    fun z => ∑ t ∈ S.attach.filter (fun t => t.1 ≠ s),
      laurentHigherOrderPolarAt hCondB t.1 t.2 z
  have rest_an : AnalyticAt ℂ rest s := by
    refine Finset.analyticAt_fun_sum _ fun t ht => ?_
    have h_ne : t.1 ≠ s := (Finset.mem_filter.mp ht).2
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_compl_singleton.mem_nhds (mem_compl_singleton_iff.mpr h_ne.symm)]
      with z hz
    exact laurentHigherOrderPolarAt_differentiableAt hCondB t.2 (mem_compl_singleton_iff.mp hz)
  refine ⟨g_s + rest, g_s_an.add rest_an, ?_⟩
  filter_upwards [g_s_eq] with z hz_eq
  show laurentHigherOrderPolar hCondB z = g_s z + rest z
  unfold laurentHigherOrderPolar
  rw [← Finset.sum_filter_add_sum_filter_not S.attach (fun t : {x // x ∈ S} => t.1 = s)
    (fun t => laurentHigherOrderPolarAt hCondB t.1 t.2 z)]
  have h_filter_eq : S.attach.filter (fun t : {x // x ∈ S} => t.1 = s) = {⟨s, hs⟩} := by
    ext t; simp only [Finset.mem_filter, Finset.mem_attach, true_and, Finset.mem_singleton]; grind
  rw [h_filter_eq, Finset.sum_singleton]
  show laurentHigherOrderPolarAt hCondB s hs z + _ = g_s z + rest z
  rw [hz_eq]

/-- The "limit-corrected" higher-order polar part: equal to
`laurentHigherOrderPolar` away from `S`, and to the limit at each `s ∈ S`.
Mirrors `laurentHolomorphicRemainderCorrection`. -/
noncomputable def laurentHigherOrderPolarCorrection
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (z : ℂ) : ℂ :=
  open Classical in
  if z ∈ (↑S : Set ℂ) then limUnder (𝓝[≠] z) (laurentHigherOrderPolar hCondB)
  else laurentHigherOrderPolar hCondB z

private lemma laurentHigherOrderPolarCorrection_eventuallyEq_analyticExt
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {z : ℂ} (g_z : ℂ → ℂ)
    (hzS : z ∈ (↑S : Set ℂ)) (hg_z_an : AnalyticAt ℂ g_z z)
    (hg_z_eq : (laurentHigherOrderPolar hCondB) =ᶠ[𝓝[≠] z] g_z) :
    laurentHigherOrderPolarCorrection hCondB =ᶠ[𝓝 z] g_z := by
  classical
  have h_at_z : laurentHigherOrderPolarCorrection hCondB z = g_z z := by
    have h_lim_eq : limUnder (𝓝[≠] z) (laurentHigherOrderPolar hCondB) = g_z z :=
      (hg_z_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        |>.congr' (hg_z_eq.mono fun _ h => h.symm)).limUnder_eq
    simp only [laurentHigherOrderPolarCorrection, hzS, ↓reduceIte, h_lim_eq]
  obtain ⟨V, hV_open, hz_V, hV_eq⟩ := mem_nhdsWithin.mp hg_z_eq
  apply mem_of_superset (inter_mem (hV_open.mem_nhds hz_V)
    ((S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)))
  intro w ⟨hw_V, hw_erase⟩
  by_cases hwz : w = z
  · rw [hwz]; exact h_at_z
  · have hw_not_S : w ∉ (↑S : Set ℂ) := fun hmem => hw_erase
      (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hwz, Finset.mem_coe.mp hmem⟩))
    show laurentHigherOrderPolarCorrection hCondB w = g_z w
    simp only [laurentHigherOrderPolarCorrection, hw_not_S, ↓reduceIte]
    exact hV_eq ⟨hw_V, hwz⟩

private lemma laurentHigherOrderPolarCorrection_eventuallyEq_polar
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {z : ℂ} (hzS : z ∉ (↑S : Set ℂ)) :
    laurentHigherOrderPolarCorrection hCondB =ᶠ[𝓝 z]
      laurentHigherOrderPolar hCondB := by
  apply mem_of_superset (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hzS)
  intro w hw
  show laurentHigherOrderPolarCorrection hCondB w = laurentHigherOrderPolar hCondB w
  simp only [laurentHigherOrderPolarCorrection, show w ∉ (↑S : Set ℂ) from hw, ↓reduceIte]

/-- The corrected higher-order polar part is differentiable on all of `U`.
Riemann removable-singularity bridge. -/
theorem laurentHigherOrderPolar_correction_differentiableOn
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    {U : Set ℂ} (_hU : IsOpen U) (_hS_in_U : ↑S ⊆ U) :
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

private lemma cpvIntegrandOn_eq_of_eqOn_compl
    {γE : ℝ → ℂ} {S : Finset ℂ} {f g : ℂ → ℂ} {ε : ℝ} (hε_pos : 0 < ε) (t : ℝ)
    (h_eq : ∀ z ∉ (↑S : Set ℂ), f z = g z) :
    cpvIntegrandOn S f γE ε t = cpvIntegrandOn S g γE ε t := by
  by_cases h_cutoff : ∃ s ∈ S, ‖γE t - s‖ ≤ ε
  · simp only [cpvIntegrandOn, if_pos h_cutoff]
  · have h_not : γE t ∉ (↑S : Set ℂ) := fun h_in =>
      h_cutoff ⟨γE t, Finset.mem_coe.mp h_in, by simp [hε_pos.le]⟩
    simp only [cpvIntegrandOn, if_neg h_cutoff, h_eq _ h_not]

/-- Generic helper: from an analytic correction `corr` differentiable on `U`, which agrees
with the original function `g` off `S`, build the cpv-integrand interval-integrability for
`g`. Shared skeleton for `hI_polar_of_conditionB_simple` and `hI_holo_of_conditionB_simple`. -/
private lemma cpvIntegrandOn_intervalIntegrable_of_correction
    {U : Set ℂ} {S : Finset ℂ} {g corr : ℂ → ℂ}
    (γ : ClosedPwC1Immersion x) (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hcorr_diff : DifferentiableOn ℂ corr U)
    (h_eq_off : ∀ z ∉ (↑S : Set ℂ), g z = corr z) {ε : ℝ} (hε_pos : 0 < ε) :
    IntervalIntegrable
      (fun t => cpvIntegrandOn S g γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t)
      volume 0 1 := by
  classical
  set γP := γ.toPwC1Immersion.toPiecewiseC1Path
  set γE := γP.toPath.extend
  have hcorr_cont_image : ContinuousOn corr (γE '' Icc (0 : ℝ) 1) := by
    refine hcorr_diff.continuousOn.mono ?_
    rintro _ ⟨t, ht, rfl⟩
    exact h_null.image_subset t ht
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  have h_deriv_int : IntervalIntegrable (deriv γE) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
    exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (stronglyMeasurable_deriv _).aestronglyMeasurable
      (ae_restrict_of_ae (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hLip))
  have h_corr_γE_cont : ContinuousOn (fun t => corr (γE t)) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (zero_le_one' ℝ)]
    exact hcorr_cont_image.comp γP.toPath.continuous_extend.continuousOn
      (fun t ht => ⟨t, ht, rfl⟩)
  have h_contour_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand corr γP) volume 0 1 :=
    h_deriv_int.continuousOn_mul h_corr_γE_cont
  refine (cpvIntegrandOn_intervalIntegrable_of_contourIntegrand S corr γP ε h_contour_int).congr
    fun t _ => (cpvIntegrandOn_eq_of_eqOn_compl hε_pos t h_eq_off).symm

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
  set γP := γ.toPwC1Immersion.toPiecewiseC1Path
  set corr := laurentHigherOrderPolarCorrection hCondB
  have hcorr_diff : DifferentiableOn ℂ corr U :=
    laurentHigherOrderPolar_correction_differentiableOn hCondB hSimple hU_open hS_in_U
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  have h_corr_zero : γP.contourIntegral corr = 0 :=
    contourIntegral_analytic_eq_zero_of_nullHomologous hU_open hU_ne hcorr_diff
      γ.toPwC1Immersion h_null hLip
  have hcorr_cont : ContinuousOn corr (γP.toPath.extend '' Icc (0 : ℝ) 1) := by
    refine hcorr_diff.continuousOn.mono ?_
    rintro _ ⟨t, ht, rfl⟩
    exact h_null.image_subset t ht
  have h_cpv_corr : HasCauchyPVOn S corr γP (γP.contourIntegral corr) :=
    hasCauchyPVOn_continuousOn_of_countable_preimage S hcorr_cont hLip (γ.preimage_countable S)
  rw [← h_corr_zero]
  refine h_cpv_corr.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε_pos
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact (cpvIntegrandOn_eq_of_eqOn_compl (S := S) (f := laurentHigherOrderPolar hCondB)
    (g := corr) hε_pos t fun _ h_not => by
      simp only [corr, laurentHigherOrderPolarCorrection, h_not, ↓reduceIte]).symm

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
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1 := fun ε hε_pos =>
  cpvIntegrandOn_intervalIntegrable_of_correction γ h_null
    (laurentHigherOrderPolar_correction_differentiableOn hCondB hSimple hU_open hS_in_U)
    (fun _ h_not => by simp only [laurentHigherOrderPolarCorrection, h_not, ↓reduceIte]) hε_pos

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
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1 := fun ε hε_pos =>
  cpvIntegrandOn_intervalIntegrable_of_correction γ h_null
    (laurentHolomorphicRemainder_correction_differentiableOn hCondB hSimple hU_open hf)
    (fun _ h_not => by simp only [laurentHolomorphicRemainderCorrection, h_not, ↓reduceIte])
    hε_pos

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
          residue f s) :=
  hw_3_3_simple_with_crossData hU_open hU_ne S hS_in_U f hf γ h_null hSimple hCondA hCondB
    (h_polar_cancel_of_conditionB_simple hU_open hU_ne hS_in_U γ h_null hSimple hCondB)
    (hI_polar_of_conditionB_simple hU_open hS_in_U γ h_null hSimple hCondB)
    (hI_holo_of_conditionB_simple hU_open hS_in_U hf γ h_null hSimple hCondB)
    crossData hδ_pos h_avoid_pairs h_int_perpole

end LeanModularForms

end
