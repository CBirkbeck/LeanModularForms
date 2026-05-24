/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue.SectorCurve

/-!
# Sector Curve PV Lemmas

Higher-order PV computations and the generalized winding number for the
model sector-curve defined in `SectorCurve.lean`.

## Main Results

* `pv_sector_higher_power` -- for n >= 1, `PV int z^{n-1} dz = 0` (angle condition)
* `cauchyPV_sectorCurve_simplePole` -- Lemma 3.1 for simple poles: PV = `I * alpha * residue`
* `cauchyPV_sectorCurve_eq_mul_residueSimplePole` -- variant for arbitrary `f = c/z + g`
* `pv_sector_negative_power` -- Equation (3.4): PV of `z^{-n}` is 0 under angle condition
* `generalizedWindingNumber_sectorCurve` -- winding number equals `alpha / (2 * pi)`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

private theorem sectorCurve_differentiableAt_off_knots (r : ℝ) (α : ℝ)
    (t : ℝ) (_ht : t ∈ Ioo (0 : ℝ) 3) (ht_not : t ∉ ({1, 2} : Set ℝ)) :
    DifferentiableAt ℝ (sectorCurve r α) t := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_not
  rcases lt_or_gt_of_ne ht_not.1 with h1 | h1
  · have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => (↑(s * r) : ℂ) := by
      filter_upwards [Iio_mem_nhds h1] with s hs
      simp only [sectorCurve, if_pos (mem_Iio.mp hs).le]
    exact h_eq.differentiableAt_iff.mpr
      ((hasDerivAt_id t).mul_const r).ofReal_comp.differentiableAt
  · rcases lt_or_gt_of_ne ht_not.2 with h2 | h2
    · have h_eq : sectorCurve r α =ᶠ[𝓝 t]
          fun s => (↑r : ℂ) * exp (I * ↑((s - 1) * α)) := by
        filter_upwards [isOpen_Ioo.mem_nhds ⟨h1, h2⟩] with s hs
        exact sectorCurve_seg2 r α s ⟨hs.1.le, hs.2.le⟩
      refine h_eq.differentiableAt_iff.mpr ?_
      apply DifferentiableAt.const_mul
      apply DifferentiableAt.cexp
      apply DifferentiableAt.const_mul
      exact (((hasDerivAt_id t).sub
        (hasDerivAt_const t (1 : ℝ))).mul_const α).ofReal_comp.differentiableAt
    · have h_eq : sectorCurve r α =ᶠ[𝓝 t]
          fun s => (↑((3 - s) * r) : ℂ) * exp (I * ↑α) := by
        filter_upwards [Ioi_mem_nhds h2] with s hs
        simp only [sectorCurve,
          if_neg (not_le.mpr (lt_trans one_lt_two (mem_Ioi.mp hs))),
          if_neg (not_le.mpr (mem_Ioi.mp hs))]
      refine h_eq.differentiableAt_iff.mpr ?_
      apply DifferentiableAt.mul_const
      exact (((hasDerivAt_const t (3 : ℝ)).sub
        (hasDerivAt_id t)).mul_const r).ofReal_comp.differentiableAt

private theorem sectorCurve_mem_ball (r : ℝ) (hr : 0 < r) (α : ℝ) :
    ∀ t ∈ Icc (0 : ℝ) 3, sectorCurve r α t ∈ Metric.ball (0 : ℂ) (↑r + 1) := by
  have norm_exp_I : ∀ x : ℝ, ‖Complex.exp (I * ↑x)‖ = 1 := fun x => by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  intro t ⟨ht0, ht3⟩
  simp only [Metric.mem_ball, dist_zero_right]
  rcases le_or_gt t 1 with h1 | h1
  · rw [sectorCurve_seg1 r α t ⟨ht0, h1⟩, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 hr.le)]
    nlinarith
  · rcases le_or_gt t 2 with h2 | h2
    · rw [sectorCurve_seg2 r α t ⟨h1.le, h2⟩, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        norm_exp_I, mul_one]
      linarith
    · rw [sectorCurve_seg3 r α t ⟨h2.le, ht3⟩, norm_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by linarith) hr.le),
        norm_exp_I, mul_one]
      nlinarith

private theorem φ_sectorCurve_integrableOn_01 (r : ℝ) (hr : 0 < r) (α : ℝ)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    IntervalIntegrable (fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t)
      volume 0 1 := by
  have hγ_in_ball := sectorCurve_mem_ball r hr α
  have hc : ContinuousOn (fun t : ℝ => g ((t * r : ℝ) : ℂ) * (r : ℂ)) (Icc 0 1) :=
    (hg.continuousOn.comp
      ((continuous_ofReal.comp (continuous_id.mul continuous_const)).continuousOn)
      (fun t ht => by
        have := hγ_in_ball t ⟨ht.1, by linarith [ht.2]⟩
        rwa [sectorCurve_seg1 r α t ht] at this)).mul continuousOn_const
  exact (hc.intervalIntegrable_of_Icc (by norm_num)).congr_ae (by
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg1 r α t ⟨ht.1.le, ht.2.le⟩,
      deriv_sectorCurve_seg1 r α t ht])

private theorem φ_sectorCurve_integrableOn_12 (r : ℝ) (hr : 0 < r) (α : ℝ)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    IntervalIntegrable (fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t)
      volume 1 2 := by
  have hγ_in_ball := sectorCurve_mem_ball r hr α
  have hc : ContinuousOn (fun t : ℝ => g ((r : ℂ) * exp (I * ((t - 1) * α : ℝ))) *
      ((r : ℂ) * (I * (α : ℂ)) * exp (I * ((t - 1) * α : ℝ)))) (Icc 1 2) := by
    apply ContinuousOn.mul
    · exact hg.continuousOn.comp
        ((continuous_const.mul (continuous_exp.comp
          (continuous_const.mul (continuous_ofReal.comp
            ((continuous_id.sub continuous_const).mul continuous_const))))).continuousOn)
        (fun t ht => by
          have := hγ_in_ball t ⟨by linarith [ht.1], by linarith [ht.2]⟩
          rwa [sectorCurve_seg2 r α t ht] at this)
    · exact (continuous_const.mul (continuous_exp.comp
        (continuous_const.mul (continuous_ofReal.comp
          ((continuous_id.sub continuous_const).mul continuous_const))))).continuousOn
  exact (hc.intervalIntegrable_of_Icc (by norm_num)).congr_ae (by
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 2),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg2 r α t ⟨ht.1.le, ht.2.le⟩,
      deriv_sectorCurve_seg2 r α t ht])

private theorem φ_sectorCurve_integrableOn_23 (r : ℝ) (hr : 0 < r) (α : ℝ)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    IntervalIntegrable (fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t)
      volume 2 3 := by
  have hγ_in_ball := sectorCurve_mem_ball r hr α
  have hc : ContinuousOn (fun t : ℝ => g (((3 - t) * r : ℝ) * exp (I * (α : ℂ))) *
      (-(r : ℂ) * exp (I * (α : ℂ)))) (Icc 2 3) :=
    (hg.continuousOn.comp
      ((continuous_ofReal.comp ((continuous_const.sub continuous_id).mul
        continuous_const)).mul continuous_const).continuousOn
      (fun t ht => by
        have := hγ_in_ball t ⟨by linarith [ht.1], ht.2⟩
        rwa [sectorCurve_seg3 r α t ht] at this)).mul continuousOn_const
  exact (hc.intervalIntegrable_of_Icc (by norm_num)).congr_ae (by
    rw [Set.uIoc_of_le (by norm_num : (2:ℝ) ≤ 3),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg3 r α t ⟨ht.1.le, ht.2.le⟩,
      deriv_sectorCurve_seg3 r α t ht])

private theorem φ_sectorCurve_intervalIntegrable (r : ℝ) (hr : 0 < r) (α : ℝ)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    IntervalIntegrable (fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t)
      volume 0 3 :=
  (φ_sectorCurve_integrableOn_01 r hr α g hg).trans
    (φ_sectorCurve_integrableOn_12 r hr α g hg) |>.trans
    (φ_sectorCurve_integrableOn_23 r hr α g hg)

/-- The integral of an analytic function along the sector curve is zero,
because the sector starts and ends at 0, and analytic functions on
a convex open set have primitives. -/
private theorem integral_analytic_sectorCurve_eq_zero (r : ℝ) (hr : 0 < r) (α : ℝ)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    ∫ t in (0 : ℝ)..3, g (sectorCurve r α t) * deriv (sectorCurve r α) t = 0 := by
  have hγ_in_ball := sectorCurve_mem_ball r hr α
  obtain ⟨F, hF⟩ := holomorphic_convex_primitive (convex_ball 0 _) Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self (by positivity)⟩ hg.differentiableOn
  have hF_contOn : ContinuousOn F (Metric.ball (0 : ℂ) (↑r + 1)) :=
    fun z hz => (hF z hz).continuousAt.continuousWithinAt
  have hF_deriv : ∀ t ∈ Ioo (0 : ℝ) 3 \ ({1, 2} ∩ Ioo 0 3),
      HasDerivAt (F ∘ sectorCurve r α)
        (g (sectorCurve r α t) * deriv (sectorCurve r α) t) t := fun t ⟨ht, ht_not⟩ =>
    (hF _ (hγ_in_ball t (Ioo_subset_Icc_self ht))).comp_of_eq t
      (sectorCurve_differentiableAt_off_knots r α t ht
        (fun h => ht_not ⟨h, ht⟩)).hasDerivAt rfl
  rw [MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (F ∘ sectorCurve r α) _ (by norm_num : (0 : ℝ) ≤ 3)
    ((Set.Finite.inter_of_left (Set.toFinite {1, 2}) _).countable)
    (hF_contOn.comp (sectorCurve_continuousOn r α) hγ_in_ball) hF_deriv
    (φ_sectorCurve_intervalIntegrable r hr α g hg),
    Function.comp_apply, Function.comp_apply,
    sectorCurve_zero, sectorCurve_three, sub_self]

private theorem cauchyPV_g_aestronglyMeasurable (r : ℝ) (α : ℝ)
    (g : ℂ → ℂ) (ε : ℝ)
    (h_int_g : IntervalIntegrable (fun t => g (sectorCurve r α t) *
      deriv (sectorCurve r α) t) volume 0 3) :
    AEStronglyMeasurable
      (cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε)
      (volume.restrict (Ioc 0 3)) :=
  (h_int_g.aestronglyMeasurable.indicator
    (measurableSet_pv_support (sectorCurve r α) 0 3 0 ε
      (sectorCurve_continuousOn r α))).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [cauchyPrincipalValueIntegrand', Set.indicator_apply]
    by_cases h : ‖sectorCurve r α t - 0‖ > ε
    · rw [if_pos ⟨h, Ioc_subset_Icc_self ht⟩, if_pos h]
    · rw [if_neg fun ⟨hm, _⟩ => h hm, if_neg h])

private theorem cauchyPV_g_norm_le (r : ℝ) (α : ℝ)
    (g : ℂ → ℂ) (ε : ℝ) (t : ℝ) :
    ‖cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε t‖ ≤
    ‖g (sectorCurve r α t) * deriv (sectorCurve r α) t‖ := by
  simp only [cauchyPrincipalValueIntegrand', sub_zero]
  split_ifs
  · exact le_refl _
  · simp [norm_nonneg, mul_nonneg]

private theorem sectorCurve_zero_set_finite (r : ℝ) (hr : 0 < r) (α : ℝ) :
    Set.Finite ({t ∈ Icc (0:ℝ) 3 | sectorCurve r α t = 0}) := by
  apply Set.Finite.subset (Set.toFinite {(0:ℝ), 3})
  intro t ⟨⟨ht0, ht3⟩, h0⟩
  rcases le_or_gt t 1 with h1 | h1
  · rw [sectorCurve_seg1 r α t ⟨ht0, h1⟩] at h0
    simp only [Complex.ofReal_eq_zero] at h0
    simp [(mul_eq_zero.mp h0).resolve_right hr.ne']
  · rcases le_or_gt t 2 with h2 | h2
    · exfalso
      rw [sectorCurve_seg2 r α t ⟨h1.le, h2⟩] at h0
      simp only [mul_eq_zero, Complex.ofReal_eq_zero] at h0
      exact h0.elim (fun h => by linarith) (Complex.exp_ne_zero _)
    · rw [sectorCurve_seg3 r α t ⟨h2.le, ht3⟩] at h0
      simp only [mul_eq_zero, Complex.ofReal_eq_zero] at h0
      rcases h0 with (h | h) | h
      · simp [show t = 3 from by linarith]
      · exact absurd h hr.ne'
      · exact absurd h (Complex.exp_ne_zero _)

private theorem cauchyPV_g_intervalIntegrable (r : ℝ) (hr : 0 < r) (α : ℝ)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) (ε : ℝ) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε)
      volume 0 3 := by
  have h_int_g := φ_sectorCurve_intervalIntegrable r hr α g hg
  refine h_int_g.mono_fun ?_ (Filter.Eventually.of_forall (cauchyPV_g_norm_le r α g ε))
  rw [show Ι (0:ℝ) 3 = Ioc 0 3 from uIoc_of_le (by norm_num)]
  exact cauchyPV_g_aestronglyMeasurable r α g ε h_int_g

private theorem cauchyPV_inv_integrableOn_0δ (r : ℝ) (hr : 0 < r) (α : ℝ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
      (sectorCurve r α) 0 ε) volume 0 (ε / r) :=
  (intervalIntegrable_const (c := (0 : ℂ))).congr (fun t ht => by
    rw [Set.uIoc_of_le (div_pos hε_pos hr).le] at ht
    simp only [cauchyPrincipalValueIntegrand', sub_zero]
    rw [if_neg (not_lt.mpr _)]
    rw [sectorCurve_norm_seg1 r hr α t ⟨ht.1.le,
      ht.2.trans (by rwa [div_lt_one hr] : ε / r < 1).le⟩]
    nlinarith [mul_le_mul_of_nonneg_right ht.2 hr.le, div_mul_cancel₀ ε hr.ne'])

private theorem cauchyPV_inv_integrableOn_3δ3 (r : ℝ) (hr : 0 < r) (α : ℝ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
      (sectorCurve r α) 0 ε) volume (3 - ε / r) 3 :=
  (intervalIntegrable_const (c := (0 : ℂ))).congr (fun t ht => by
    have hεr_pos : 0 < ε / r := div_pos hε_pos hr
    have hεr_lt_one : ε / r < 1 := (div_lt_one hr).mpr hε_lt_r
    rw [Set.uIoc_of_le (by linarith : 3 - ε / r ≤ 3)] at ht
    simp only [cauchyPrincipalValueIntegrand', sub_zero]
    rw [if_neg (not_lt.mpr _)]
    rw [sectorCurve_norm_seg3' r hr α t ⟨by linarith [ht.1], ht.2⟩]
    nlinarith [mul_le_mul_of_nonneg_right (by linarith [ht.1] : 3 - t ≤ ε / r) hr.le,
      div_mul_cancel₀ ε hr.ne'])

private theorem cauchyPV_inv_integrableOn_δ1 (r : ℝ) (hr : 0 < r) (α : ℝ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
      (sectorCurve r α) 0 ε) volume (ε / r) 1 := by
  set δ := ε / r
  have hδ : 0 < δ := div_pos hε_pos hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  have hcont : ContinuousOn (fun t : ℝ => (↑(t⁻¹) : ℂ)) (Set.uIcc δ 1) := by
    intro t ht
    rw [Set.uIcc_of_le hδ1.le] at ht
    exact (Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_inv₀ (hδ.trans_le ht.1).ne')).continuousWithinAt
  rw [intervalIntegrable_iff, Set.uIoc_of_le hδ1.le]
  have h_eq : ∀ t ∈ Ioo δ (1 : ℝ),
      cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t =
      (↑(t⁻¹) : ℂ) := fun t ⟨htδ, ht1⟩ => by
    simp only [cauchyPrincipalValueIntegrand', sub_zero]
    rw [if_pos]
    · exact pv_integrand_seg1 r hr α t ⟨lt_trans hδ htδ, ht1⟩
    · rw [sectorCurve_norm_seg1 r hr α t ⟨(hδ.trans htδ).le, ht1.le⟩]
      nlinarith [div_mul_cancel₀ ε hr.ne']
  have h1 : ∀ᵐ t ∂(volume.restrict (Ioo δ 1)),
      (fun t : ℝ => (↑(t⁻¹) : ℂ)) t =
      cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t :=
    (ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h1
  refine Integrable.congr ?_ h1
  rw [show (Ioc δ 1) = Set.uIoc δ 1 from (Set.uIoc_of_le hδ1.le).symm]
  exact intervalIntegrable_iff.mp hcont.intervalIntegrable

private theorem cauchyPV_inv_integrableOn_12 (r : ℝ) (hr : 0 < r) (α : ℝ)
    (ε : ℝ) (hε_lt_r : ε < r) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
      (sectorCurve r α) 0 ε) volume 1 2 := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  have h_eq : ∀ t ∈ Ioo (1 : ℝ) 2,
      cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t =
      I * ↑α := fun t ⟨ht1, ht2⟩ => by
    simp only [cauchyPrincipalValueIntegrand', sub_zero]
    rw [if_pos]
    · exact pv_integrand_seg2 r hr α t ⟨ht1, ht2⟩
    · rw [sectorCurve_seg2 r α t ⟨ht1.le, ht2.le⟩]
      simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
        Complex.norm_of_nonneg hr.le]
      exact hε_lt_r
  have h1 : ∀ᵐ t ∂(volume.restrict (Ioo (1:ℝ) 2)),
      (fun _ => I * (↑α : ℂ)) t =
      cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t :=
    (ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h1
  exact Integrable.congr (integrableOn_const (hs := measure_Ioc_lt_top.ne)) h1

private theorem cauchyPV_inv_integrableOn_2_3δ (r : ℝ) (hr : 0 < r) (α : ℝ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
      (sectorCurve r α) 0 ε) volume 2 (3 - ε / r) := by
  set δ := ε / r
  have hδ : 0 < δ := div_pos hε_pos hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  have h3δ : 2 < 3 - δ := by linarith
  have hcont : ContinuousOn (fun t : ℝ => -(↑((3 - t)⁻¹) : ℂ))
      (Set.uIcc 2 (3 - δ)) := by
    rw [Set.uIcc_of_le h3δ.le]
    intro t ht
    exact (continuous_neg.continuousAt.comp
      (Complex.continuous_ofReal.continuousAt.comp
        ((continuousAt_inv₀ (ne_of_gt (by linarith [ht.2] : (0:ℝ) < 3 - t))).comp
         (continuousAt_const.sub continuousAt_id)))).continuousWithinAt
  rw [intervalIntegrable_iff, Set.uIoc_of_le h3δ.le]
  have h_eq : ∀ t ∈ Ioo (2 : ℝ) (3 - δ),
      cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t =
      -(↑((3 - t)⁻¹) : ℂ) := fun t ⟨ht2, ht3δ⟩ => by
    simp only [cauchyPrincipalValueIntegrand', sub_zero]
    rw [if_pos]
    · rw [sectorCurve_seg3 r α t ⟨ht2.le, by linarith⟩,
          deriv_sectorCurve_seg3 r α t ⟨ht2, by linarith⟩]
      have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
      have h3t : (3 - t : ℝ) ≠ 0 := by linarith
      push_cast
      field_simp
    · rw [sectorCurve_norm_seg3' r hr α t ⟨ht2.le, by linarith⟩]
      nlinarith [div_mul_cancel₀ ε hr.ne']
  have h1 : ∀ᵐ t ∂(volume.restrict (Ioo (2:ℝ) (3 - δ))),
      (fun t : ℝ => -(↑((3 - t)⁻¹) : ℂ)) t =
      cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t :=
    (ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h1
  refine Integrable.congr ?_ h1
  rw [show Ioc 2 (3 - δ) = Set.uIoc 2 (3 - δ) from (Set.uIoc_of_le h3δ.le).symm]
  exact intervalIntegrable_iff.mp hcont.intervalIntegrable

private theorem cauchyPV_inv_intervalIntegrable (r : ℝ) (hr : 0 < r) (α : ℝ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
      (sectorCurve r α) 0 ε) volume 0 3 :=
  ((cauchyPV_inv_integrableOn_0δ r hr α ε hε_pos hε_lt_r).trans
    (cauchyPV_inv_integrableOn_δ1 r hr α ε hε_pos hε_lt_r)).trans
    (cauchyPV_inv_integrableOn_12 r hr α ε hε_lt_r) |>.trans
    (cauchyPV_inv_integrableOn_2_3δ r hr α ε hε_pos hε_lt_r) |>.trans
    (cauchyPV_inv_integrableOn_3δ3 r hr α ε hε_pos hε_lt_r)

private theorem cauchyPV_g_tendsto_zero (r : ℝ) (hr : 0 < r) (α : ℝ)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    Tendsto (fun ε => ∫ t in (0:ℝ)..3,
      cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε t)
      (𝓝[>] 0) (𝓝 0) := by
  have h_int_g := φ_sectorCurve_intervalIntegrable r hr α g hg
  suffices h : Tendsto (fun ε => ∫ t in (0:ℝ)..3,
      cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε t)
      (𝓝[>] 0) (𝓝 (∫ t in (0:ℝ)..3,
        (fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t) t)) by
    rwa [integral_analytic_sectorCurve_eq_zero r hr α g hg] at h
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖g (sectorCurve r α t) * deriv (sectorCurve r α) t‖)
    (Filter.Eventually.of_forall fun ε => by
      rw [show Ι (0:ℝ) 3 = Ioc 0 3 from uIoc_of_le (by norm_num)]
      exact cauchyPV_g_aestronglyMeasurable r α g ε h_int_g)
    (Filter.Eventually.of_forall fun ε =>
      Eventually.of_forall fun t _ => cauchyPV_g_norm_le r α g ε t)
    h_int_g.norm ?_
  filter_upwards [(sectorCurve_zero_set_finite r hr α).countable.ae_notMem _]
    with t ht ht_uIoc
  have h_ne : sectorCurve r α t ≠ 0 := fun heq =>
    ht ⟨Ioc_subset_Icc_self (uIoc_of_le (by norm_num : (0:ℝ) ≤ 3) ▸ ht_uIoc), heq⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (norm_pos_iff.mpr (sub_ne_zero.mpr h_ne))] with ε hε
  simp only [cauchyPrincipalValueIntegrand', sub_zero, gt_iff_lt]
  rw [sub_zero] at hε
  rw [if_pos hε.2]

private theorem cauchyPV_simplePole_integral_split (r : ℝ) (hr : 0 < r) (α : ℝ)
    (c : ℂ) (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    ∀ᶠ ε in 𝓝[>] 0,
      (∫ t in (0:ℝ)..3, cauchyPrincipalValueIntegrand' (fun z => c / z + g z)
        (sectorCurve r α) 0 ε t) =
      c * (∫ t in (0:ℝ)..3, cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
        (sectorCurve r α) 0 ε t) +
      (∫ t in (0:ℝ)..3, cauchyPrincipalValueIntegrand' g
        (sectorCurve r α) 0 ε t) := by
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds hr] with ε hε_lt_r hε_pos
  simp only [mem_Ioi] at hε_pos
  rw [intervalIntegral.integral_congr (g := fun t =>
      c * cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t +
      cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε t)
      (fun t _ => by
        simp only [cauchyPrincipalValueIntegrand', sub_zero, div_eq_mul_inv]
        split_ifs <;> ring),
    intervalIntegral.integral_add
      ((cauchyPV_inv_intervalIntegrable r hr α ε hε_pos hε_lt_r).const_mul c)
      (cauchyPV_g_intervalIntegrable r hr α g hg ε)]
  congr 1
  exact intervalIntegral.integral_const_mul c _

private theorem sectorCurve_ne_zero_of_Icc_δ (r : ℝ) (hr : 0 < r) (α : ℝ)
    (δ : ℝ) (hδ_pos : 0 < δ) (_hδ_lt_1 : δ < 1) :
    ∀ t ∈ Icc δ (3 - δ), sectorCurve r α t ≠ 0 := by
  intro t ht h0
  rcases le_or_gt t 1 with h1 | h1
  · rw [sectorCurve_seg1 r α t ⟨le_trans hδ_pos.le ht.1, h1⟩] at h0
    rcases mul_eq_zero.mp (Complex.ofReal_eq_zero.mp h0) with ht0 | hr0
    · linarith [ht.1]
    · linarith
  · rcases le_or_gt t 2 with h2 | h2
    · rw [sectorCurve_seg2 r α t ⟨h1.le, h2⟩] at h0
      rcases mul_eq_zero.mp h0 with hr0 | hexp0
      · exact absurd (Complex.ofReal_eq_zero.mp hr0) hr.ne'
      · exact absurd hexp0 (Complex.exp_ne_zero _)
    · rw [sectorCurve_seg3 r α t ⟨h2.le, by linarith [ht.2]⟩] at h0
      rcases mul_eq_zero.mp h0 with h3t | hexp0
      · rcases mul_eq_zero.mp (Complex.ofReal_eq_zero.mp h3t) with ht3 | hr0
        · linarith [ht.2]
        · linarith
      · exact absurd hexp0 (Complex.exp_ne_zero _)

private theorem sectorCurve_norm_le_near_zero (r : ℝ) (hr : 0 < r) (α : ℝ)
    (δ : ℝ) (_hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) (ε : ℝ) (hδr_eq : δ * r = ε) :
    ∀ t ∈ Icc 0 δ, ‖sectorCurve r α t‖ ≤ ε := fun t ht => by
  rw [sectorCurve_norm_seg1 r hr α t ⟨ht.1, ht.2.trans hδ_lt_1.le⟩]
  nlinarith [mul_le_mul_of_nonneg_right ht.2 hr.le]

private theorem sectorCurve_norm_le_near_three (r : ℝ) (hr : 0 < r) (α : ℝ)
    (δ : ℝ) (hδ_lt_1 : δ < 1) (ε : ℝ) (hδr_eq : δ * r = ε) :
    ∀ t ∈ Icc (3 - δ) 3, ‖sectorCurve r α t‖ ≤ ε := fun t ht => by
  rw [sectorCurve_norm_seg3' r hr α t ⟨(by linarith : 2 ≤ 3 - δ).trans ht.1, ht.2⟩]
  nlinarith [mul_le_mul_of_nonneg_right (by linarith [ht.1] : 3 - t ≤ δ) hr.le]

private theorem sectorCurve_norm_gt_mid (r : ℝ) (hr : 0 < r) (α : ℝ)
    (δ : ℝ) (hδ_pos : 0 < δ) (_hδ_lt_1 : δ < 1) (ε : ℝ) (hε_lt_r : ε < r)
    (hδr_eq : δ * r = ε) :
    ∀ t ∈ Ioo δ (3 - δ), ε < ‖sectorCurve r α t‖ := by
  intro t ht
  rcases le_or_gt t 1 with h1 | h1
  · rw [sectorCurve_norm_seg1 r hr α t ⟨(hδ_pos.trans ht.1).le, h1⟩]
    nlinarith [mul_lt_mul_of_pos_right ht.1 hr]
  · rcases le_or_gt t 2 with h2 | h2
    · rw [sectorCurve_norm_on_arc r hr α t ⟨h1.le, h2⟩]; exact hε_lt_r
    · rw [sectorCurve_norm_seg3' r hr α t ⟨h2.le, by linarith [ht.2]⟩]
      nlinarith [mul_lt_mul_of_pos_right (by linarith [ht.2] : δ < 3 - t) hr]

private theorem zpow_integrableOn_δ1 (r : ℝ) (hr : 0 < r) (α : ℝ)
    (n : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) :
    IntervalIntegrable (fun t => (sectorCurve r α t) ^ (-(↑n : ℤ)) *
      deriv (sectorCurve r α) t) volume δ 1 := by
  have hcont : ContinuousOn (fun t => (↑(t * r) : ℂ) ^ (-(↑n : ℤ)) * (↑r : ℂ))
      (Icc δ 1) :=
    (ContinuousOn.zpow₀ (by fun_prop) _ fun t ht => Or.inl
      (Complex.ofReal_ne_zero.mpr (mul_pos (hδ_pos.trans_le ht.1) hr).ne')).mul
      continuousOn_const
  exact (hcont.intervalIntegrable_of_Icc hδ_lt_1.le).congr_ae (by
    rw [Set.uIoc_of_le hδ_lt_1.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg1 r α t ⟨(hδ_pos.trans ht.1).le, ht.2.le⟩,
      deriv_sectorCurve_seg1 r α t ⟨lt_trans hδ_pos ht.1, ht.2⟩])

private theorem zpow_integrableOn_12 (r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ) :
    IntervalIntegrable (fun t => (sectorCurve r α t) ^ (-(↑n : ℤ)) *
      deriv (sectorCurve r α) t) volume 1 2 := by
  have hcont : ContinuousOn (fun t => (↑r * exp (I * ↑((t - 1) * α))) ^ (-(↑n : ℤ)) *
      (↑r * (I * ↑α) * exp (I * ↑((t - 1) * α)))) (Icc 1 2) :=
    (ContinuousOn.zpow₀ (by fun_prop) _ fun t _ =>
      Or.inl (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')
        (Complex.exp_ne_zero _))).mul (by fun_prop)
  exact (hcont.intervalIntegrable_of_Icc (by norm_num)).congr_ae (by
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 2),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg2 r α t ⟨ht.1.le, ht.2.le⟩,
      deriv_sectorCurve_seg2 r α t ht])

private theorem zpow_integrableOn_23δ (r : ℝ) (hr : 0 < r) (α : ℝ)
    (n : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) :
    IntervalIntegrable (fun t => (sectorCurve r α t) ^ (-(↑n : ℤ)) *
      deriv (sectorCurve r α) t) volume 2 (3 - δ) := by
  have h3δ_gt_2 : 2 < 3 - δ := by linarith
  have hcont : ContinuousOn (fun t => (↑((3 - t) * r) * exp (I * ↑α)) ^ (-(↑n : ℤ)) *
      (-(↑r) * exp (I * ↑α))) (Icc 2 (3 - δ)) :=
    (ContinuousOn.zpow₀ (by fun_prop) _ fun t ht => Or.inl
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos (by linarith [ht.2]) hr).ne')
        (Complex.exp_ne_zero _))).mul continuousOn_const
  exact (hcont.intervalIntegrable_of_Icc h3δ_gt_2.le).congr_ae (by
    rw [Set.uIoc_of_le h3δ_gt_2.le,
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg3 r α t ⟨ht.1.le, by linarith [ht.2]⟩,
      deriv_sectorCurve_seg3 r α t ⟨ht.1, by linarith [ht.2]⟩])

end
