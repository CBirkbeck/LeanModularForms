/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.PVInfrastructure.AnnulusBounds

/-!
# PV Infrastructure: Singular Annulus Bounds

Bounds on singular annular integrals, including the linearized model,
symmetric cancellation, measurability, and the explicit epsilon-independent
bound used in the dyadic PV convergence proof.

## Main Results

* `singular_tAnnLin_cancel` — linearized annular integrand cancels symmetrically
* `singular_annulus_lin_integral_zero` — linearized annular integral vanishes
* `singular_annulus_bound_explicit` — epsilon-independent bound on singular integral
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

private instance : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass

noncomputable section

lemma singular_tAnnLin_inside_interval
    {t₀ a b : ℝ} (hat₀ : t₀ ∈ Set.Ioo a b)
    {L : ℂ} (hL_pos : 0 < ‖L‖) {ε₁ : ℝ}
    (hε₁_small :
      ε₁ < ‖L‖ * min (t₀ - a) (b - t₀))
    {t : ℝ} (ht_bound : ‖L‖ * |t - t₀| ≤ ε₁) :
    t ∈ Set.Icc a b := by
  have ht₀_mem := Set.mem_Ioo.mp hat₀
  have h_abs_lt :
      |t - t₀| < min (t₀ - a) (b - t₀) := by
    have h1 :
        ‖L‖ * |t - t₀| <
        ‖L‖ * min (t₀ - a) (b - t₀) :=
      lt_of_le_of_lt ht_bound hε₁_small
    exact lt_of_mul_lt_mul_left h1 (le_of_lt hL_pos)
  have h1 : |t - t₀| < t₀ - a :=
    lt_of_lt_of_le h_abs_lt (min_le_left _ _)
  have h2 : |t - t₀| < b - t₀ :=
    lt_of_lt_of_le h_abs_lt (min_le_right _ _)
  rw [abs_lt] at h1 h2
  exact Set.mem_Icc.mpr
    ⟨by linarith [h1.1], by linarith [h2.2]⟩

lemma singular_tAnnLin_cancel (t₀ : ℝ)
    {L : ℂ} (hL_pos : 0 < ‖L‖)
    (ε₁ ε₂ : ℝ) (hε₂_pos : 0 < ε₂)
    (hε₂_le : ε₂ ≤ ε₁) :
    let c₁ := ε₂ / ‖L‖
    let c₂ := ε₁ / ‖L‖
    (∫ t in (t₀ - c₂)..(t₀ - c₁),
      (↑(t - t₀) : ℂ)⁻¹) +
    (∫ t in (t₀ + c₁)..(t₀ + c₂),
      (↑(t - t₀) : ℂ)⁻¹) = 0 := by
  intro c₁ c₂
  exact integral_inv_symm t₀ c₁ c₂
    (div_pos hε₂_pos hL_pos)
    (div_pos (lt_of_lt_of_le hε₂_pos hε₂_le) hL_pos)
    (div_le_div_of_nonneg_right hε₂_le
      (le_of_lt hL_pos))

lemma singular_symmDiff_sup_bound
    {t₀ c : ℝ} (hc_pos : 0 < c)
    {t : ℝ} (ht_lower : c ≤ |t - t₀|) :
    ‖(↑(t - t₀) : ℂ)⁻¹‖ ≤ 1 / c := by
  have ht_pos : (0 : ℝ) < |t - t₀| :=
    lt_of_lt_of_le hc_pos ht_lower
  rw [norm_inv, Complex.norm_real,
    Real.norm_eq_abs, one_div]
  exact inv_anti₀ hc_pos ht_lower

/-! ### Helper: linearized annular integral vanishes by symmetric cancellation -/

private lemma singular_annulus_lin_integral_zero
    {a b t₀ : ℝ} {L : ℂ} {ε₁ ε₂ : ℝ}
    (hL_pos : 0 < ‖L‖)
    (hε₁_pos : 0 < ε₁) (hε₂_pos : 0 < ε₂)
    (hε₂_le : ε₂ ≤ ε₁)
    (hε₁_lt_Ldist :
      ε₁ < ‖L‖ * min (t₀ - a) (b - t₀))
    (_hat₀ : t₀ ∈ Set.Ioo a b) :
    (∫ t in a..b,
      if ε₂ < ‖L‖ * |t - t₀| ∧
        ‖L‖ * |t - t₀| ≤ ε₁
      then (↑(t - t₀) : ℂ)⁻¹ else 0) = 0 := by
  set c₁ := ε₂ / ‖L‖ with hc₁_def
  set c₂ := ε₁ / ‖L‖ with hc₂_def
  have hc₁_pos : 0 < c₁ := div_pos hε₂_pos hL_pos
  have hc₂_pos : 0 < c₂ := div_pos hε₁_pos hL_pos
  have hc₁_le_c₂ : c₁ ≤ c₂ :=
    div_le_div_of_nonneg_right hε₂_le
      (le_of_lt hL_pos)
  have hc₂_lt_dist :
      c₂ < min (t₀ - a) (b - t₀) := by
    rw [hc₂_def, div_lt_iff₀ hL_pos]
    linarith [mul_comm ‖L‖ (min (t₀ - a) (b - t₀))]
  have ha_lt_mc₂ : a < t₀ - c₂ := by
    linarith [lt_of_lt_of_le hc₂_lt_dist
      (min_le_left _ _)]
  have hmc₂_le_mc₁ : t₀ - c₂ ≤ t₀ - c₁ := by
    linarith [hc₁_le_c₂]
  have hmc₁_le_pc₁ : t₀ - c₁ ≤ t₀ + c₁ := by
    linarith [hc₁_pos]
  have hpc₁_le_pc₂ : t₀ + c₁ ≤ t₀ + c₂ := by
    linarith [hc₁_le_c₂]
  have hpc₂_lt_b : t₀ + c₂ < b := by
    linarith [lt_of_lt_of_le hc₂_lt_dist
      (min_le_right _ _)]
  have h_cond_iff : ∀ t : ℝ,
      (ε₂ < ‖L‖ * |t - t₀| ∧
       ‖L‖ * |t - t₀| ≤ ε₁) ↔
      (c₁ < |t - t₀| ∧ |t - t₀| ≤ c₂) := by
    intro t
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [hc₁_def, div_lt_iff₀ hL_pos,
                 mul_comm],
             by rwa [hc₂_def, le_div_iff₀ hL_pos,
                 mul_comm]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [hc₁_def, div_lt_iff₀ hL_pos,
                 mul_comm] at h1,
             by rwa [hc₂_def, le_div_iff₀ hL_pos,
                 mul_comm] at h2⟩
  set φ : ℝ → ℂ := fun t =>
    if ε₂ < ‖L‖ * |t - t₀| ∧
      ‖L‖ * |t - t₀| ≤ ε₁
    then (↑(t - t₀) : ℂ)⁻¹ else 0
    with hφ_def
  have hφ_bound : ∀ t : ℝ, ‖φ t‖ ≤ 1 / c₁ := by
    intro t
    simp only [hφ_def]
    by_cases hcond :
        ε₂ < ‖L‖ * |t - t₀| ∧
        ‖L‖ * |t - t₀| ≤ ε₁
    · rw [if_pos hcond]
      exact singular_symmDiff_sup_bound hc₁_pos
        (le_of_lt ((h_cond_iff t).mp hcond).1)
    · rw [if_neg hcond, norm_zero]; positivity
  have hφ_meas : Measurable φ := by
    simp only [hφ_def]
    apply Measurable.ite
    · apply MeasurableSet.inter
      · exact (isOpen_lt continuous_const
          (continuous_const.mul
            (continuous_abs.comp
              (continuous_id.sub
                continuous_const)))).measurableSet
      · exact (isClosed_le
          (continuous_const.mul
            (continuous_abs.comp
              (continuous_id.sub
                continuous_const)))
          continuous_const).measurableSet
    · exact (Complex.measurable_ofReal.comp
        (measurable_id.sub_const t₀)).inv
    · exact measurable_const
  have hφ_integrable :
      ∀ u v : ℝ,
      IntervalIntegrable φ
        MeasureTheory.volume u v := by
    intro u v
    rw [intervalIntegrable_iff]
    exact MeasureTheory.IntegrableOn.of_bound
      measure_Ioc_lt_top
      hφ_meas.aestronglyMeasurable.restrict
      (1 / c₁)
      (Filter.Eventually.of_forall
        (fun x => hφ_bound x))
  have hφ_zero :
      ∀ t, ¬(c₁ < |t - t₀| ∧ |t - t₀| ≤ c₂) →
      φ t = 0 :=
    fun t hnt => by
      simp only [hφ_def,
        if_neg (mt (h_cond_iff t).mp hnt)]
  have hφ_val :
      ∀ t, c₁ < |t - t₀| ∧ |t - t₀| ≤ c₂ →
      φ t = (↑(t - t₀) : ℂ)⁻¹ :=
    fun t ht => by
      simp only [hφ_def,
        if_pos ((h_cond_iff t).mpr ht)]
  have hI₁ := hφ_integrable a (t₀ - c₂)
  have hI₂ := hφ_integrable (t₀ - c₂) (t₀ - c₁)
  have hI₃ := hφ_integrable (t₀ - c₁) (t₀ + c₁)
  have hI₄ := hφ_integrable (t₀ + c₁) (t₀ + c₂)
  have hI₅ := hφ_integrable (t₀ + c₂) b
  have h_split : ∫ t in a..b, φ t =
      (∫ t in a..(t₀ - c₂), φ t) +
      (∫ t in (t₀ - c₂)..(t₀ - c₁), φ t) +
      (∫ t in (t₀ - c₁)..(t₀ + c₁), φ t) +
      (∫ t in (t₀ + c₁)..(t₀ + c₂), φ t) +
      (∫ t in (t₀ + c₂)..b, φ t) := by
    rw [show (∫ t in a..b, φ t) =
        (∫ t in a..(t₀ + c₂), φ t) +
        (∫ t in (t₀ + c₂)..b, φ t) from
      (intervalIntegral.integral_add_adjacent_intervals
        (hI₁.trans hI₂ |>.trans hI₃ |>.trans hI₄)
        hI₅).symm,
      show (∫ t in a..(t₀ + c₂), φ t) =
        (∫ t in a..(t₀ + c₁), φ t) +
        (∫ t in (t₀ + c₁)..(t₀ + c₂), φ t) from
      (intervalIntegral.integral_add_adjacent_intervals
        (hI₁.trans hI₂ |>.trans hI₃) hI₄).symm,
      show (∫ t in a..(t₀ + c₁), φ t) =
        (∫ t in a..(t₀ - c₁), φ t) +
        (∫ t in (t₀ - c₁)..(t₀ + c₁), φ t) from
      (intervalIntegral.integral_add_adjacent_intervals
        (hI₁.trans hI₂) hI₃).symm,
      show (∫ t in a..(t₀ - c₁), φ t) =
        (∫ t in a..(t₀ - c₂), φ t) +
        (∫ t in (t₀ - c₂)..(t₀ - c₁), φ t) from
      (intervalIntegral.integral_add_adjacent_intervals
        hI₁ hI₂).symm]
  have hφ_zero_left :
      ∫ t in a..(t₀ - c₂), φ t = 0 := by
    rw [show (∫ t in a..(t₀ - c₂), φ t) =
        ∫ t in a..(t₀ - c₂), (0 : ℂ) from by
      apply intervalIntegral.integral_congr_ae
      have h_ae :
          ({t₀ - c₂} : Set ℝ)ᶜ ∈
          MeasureTheory.ae MeasureTheory.volume :=
        MeasureTheory.compl_mem_ae_iff.mpr
          (MeasureTheory.measure_singleton _)
      filter_upwards [h_ae] with t ht_ne ht_mem
      rw [Set.uIoc_of_le
        (le_of_lt ha_lt_mc₂)] at ht_mem
      have ht_lt : t < t₀ - c₂ :=
        lt_of_le_of_ne ht_mem.2 ht_ne
      exact hφ_zero t
        (fun ⟨_, hle⟩ => absurd hle
          (not_le.mpr (by
            rw [abs_of_nonpos
              (by linarith : t - t₀ ≤ 0)]
            linarith)))]
    exact intervalIntegral.integral_zero
  have hφ_zero_right :
      ∫ t in (t₀ + c₂)..b, φ t = 0 := by
    rw [show (∫ t in (t₀ + c₂)..b, φ t) =
        ∫ t in (t₀ + c₂)..b, (0 : ℂ) from by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht_mem
      rw [Set.uIoc_of_le
        (le_of_lt hpc₂_lt_b)] at ht_mem
      exact hφ_zero t
        (fun ⟨_, hle⟩ => absurd hle
          (not_le.mpr (by
            rw [abs_of_nonneg
              (by linarith [ht_mem.1] :
                0 ≤ t - t₀)]
            linarith [ht_mem.1])))]
    exact intervalIntegral.integral_zero
  have hφ_zero_middle :
      ∫ t in (t₀ - c₁)..(t₀ + c₁), φ t = 0 := by
    rw [show (∫ t in (t₀ - c₁)..(t₀ + c₁), φ t) =
        ∫ t in (t₀ - c₁)..(t₀ + c₁), (0 : ℂ) from
      intervalIntegral.integral_congr
        (fun t ht => by
          rw [Set.uIcc_of_le hmc₁_le_pc₁] at ht
          exact hφ_zero t
            (fun ⟨hgt, _⟩ => absurd
              (abs_le.mpr
                ⟨by linarith [ht.1],
                 by linarith [ht.2]⟩)
              (not_le.mpr hgt)))]
    exact intervalIntegral.integral_zero
  have hφ_eq_left :
      ∫ t in (t₀ - c₂)..(t₀ - c₁), φ t =
      ∫ t in (t₀ - c₂)..(t₀ - c₁),
        (↑(t - t₀) : ℂ)⁻¹ := by
    apply intervalIntegral.integral_congr_ae
    have h_ne :
        ({t₀ - c₁} : Set ℝ)ᶜ ∈
        MeasureTheory.ae MeasureTheory.volume :=
      MeasureTheory.compl_mem_ae_iff.mpr
        (MeasureTheory.measure_singleton _)
    filter_upwards [h_ne] with t ht_ne ht_mem
    rw [Set.uIoc_of_le hmc₂_le_mc₁] at ht_mem
    have h1 : t₀ - c₂ < t := ht_mem.1
    have h2 : t < t₀ - c₁ :=
      lt_of_le_of_ne ht_mem.2 ht_ne
    exact hφ_val t
      ⟨by rw [abs_of_nonpos
            (by linarith : t - t₀ ≤ 0)]; linarith,
       by rw [abs_of_nonpos
            (by linarith : t - t₀ ≤ 0)]; linarith⟩
  have hφ_eq_right :
      ∫ t in (t₀ + c₁)..(t₀ + c₂), φ t =
      ∫ t in (t₀ + c₁)..(t₀ + c₂),
        (↑(t - t₀) : ℂ)⁻¹ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht_mem
    rw [Set.uIoc_of_le hpc₁_le_pc₂] at ht_mem
    have h1 : t₀ + c₁ < t := ht_mem.1
    have h2 : t ≤ t₀ + c₂ := ht_mem.2
    exact hφ_val t
      ⟨by rw [abs_of_nonneg
            (by linarith : 0 ≤ t - t₀)]; linarith,
       by rw [abs_of_nonneg
            (by linarith : 0 ≤ t - t₀)]; linarith⟩
  rw [h_split, hφ_zero_left, hφ_zero_right,
    hφ_zero_middle, hφ_eq_left, hφ_eq_right]
  simp only [zero_add, add_zero]
  exact singular_tAnnLin_cancel t₀ hL_pos
    ε₁ ε₂ hε₂_pos hε₂_le

/-! ### Helper: pointwise bound on difference between gamma and linearized indicators -/

private lemma singular_annulus_diff_pointwise_bound
    {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    {ε₁ ε₂ : ℝ} {δ₁ δ_up : ℝ}
    (hL_pos : 0 < ‖L‖) (hε₂_pos : 0 < ε₂)
    (h_localize : ∀ t ∈ Set.Icc a b,
      ‖γ t - γ t₀‖ ≤ ε₁ →
      |t - t₀| < δ₁)
    (hδ₁_le_δ_up : δ₁ ≤ δ_up)
    (h_upper : ∀ t, 0 < |t - t₀| →
      |t - t₀| < δ_up →
      ‖γ t - γ t₀‖ ≤ 2 * ‖L‖ * |t - t₀|)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ‖(if ε₂ < ‖γ t - γ t₀‖ ∧
        ‖γ t - γ t₀‖ ≤ ε₁
      then (↑(t - t₀) : ℂ)⁻¹ else 0) -
     (if ε₂ < ‖L‖ * |t - t₀| ∧
        ‖L‖ * |t - t₀| ≤ ε₁
      then (↑(t - t₀) : ℂ)⁻¹ else 0)‖ ≤
    2 * ‖L‖ / ε₂ := by
  have hbound_pos : 0 < 2 * ‖L‖ / ε₂ := by positivity
  by_cases hγ :
      ε₂ < ‖γ t - γ t₀‖ ∧
      ‖γ t - γ t₀‖ ≤ ε₁ <;>
    by_cases hlin :
      ε₂ < ‖L‖ * |t - t₀| ∧
      ‖L‖ * |t - t₀| ≤ ε₁
  · simp [hγ, hlin, sub_self]
    exact le_of_lt hbound_pos
  · simp only [hγ, hlin, ↓reduceIte, sub_zero]
    have ht_ne : t ≠ t₀ := by
      intro heq; simp [heq] at hγ; linarith
    have ht_pos : 0 < |t - t₀| :=
      abs_pos.mpr (sub_ne_zero.mpr ht_ne)
    have ht_loc := h_localize t ht hγ.2
    have ht_lt_δ_up : |t - t₀| < δ_up :=
      lt_of_lt_of_le ht_loc hδ₁_le_δ_up
    have h_lo :
        ε₂ / (2 * ‖L‖) ≤ |t - t₀| :=
      le_of_lt (by
        rw [div_lt_iff₀
          (by positivity : (0:ℝ) < 2 * ‖L‖)]
        linarith [h_upper t ht_pos ht_lt_δ_up])
    exact le_trans
      (singular_symmDiff_sup_bound
        (by positivity) h_lo)
      (by rw [one_div, inv_div])
  · simp only [hγ, hlin, ↓reduceIte,
      zero_sub, norm_neg]
    have h_lo :
        ε₂ / (2 * ‖L‖) ≤ |t - t₀| :=
      le_of_lt (by
        calc ε₂ / (2 * ‖L‖) < ε₂ / ‖L‖ :=
              div_lt_div_of_pos_left hε₂_pos
                hL_pos (by linarith)
          _ ≤ |t - t₀| := by
              rw [div_le_iff₀ hL_pos, mul_comm]
              exact le_of_lt hlin.1)
    exact le_trans
      (singular_symmDiff_sup_bound
        (by positivity) h_lo)
      (by rw [one_div, inv_div])
  · simp [hγ, hlin]
    exact le_of_lt hbound_pos

/-! ### Helper: measurability and pointwise bound for the linearized indicator -/

private lemma singular_annulus_f_lin_measurable
    {t₀ : ℝ} {L : ℂ} {ε₁ ε₂ : ℝ} :
    Measurable (fun t : ℝ =>
      if ε₂ < ‖L‖ * |t - t₀| ∧
        ‖L‖ * |t - t₀| ≤ ε₁
      then (↑(t - t₀) : ℂ)⁻¹ else 0) := by
  apply Measurable.ite
  · apply MeasurableSet.inter
    · exact (isOpen_lt continuous_const
        (continuous_const.mul
          (continuous_abs.comp
            (continuous_id.sub
              continuous_const)))).measurableSet
    · exact (isClosed_le
        (continuous_const.mul
          (continuous_abs.comp
            (continuous_id.sub
              continuous_const)))
        continuous_const).measurableSet
  · exact (Complex.measurable_ofReal.comp
      (measurable_id.sub_const t₀)).inv
  · exact measurable_const

private lemma singular_annulus_f_lin_bound
    {t₀ : ℝ} {L : ℂ} {ε₁ ε₂ : ℝ}
    (hL_pos : 0 < ‖L‖) (hε₂_pos : 0 < ε₂)
    (t : ℝ) :
    ‖(if ε₂ < ‖L‖ * |t - t₀| ∧
        ‖L‖ * |t - t₀| ≤ ε₁
      then (↑(t - t₀) : ℂ)⁻¹ else (0 : ℂ))‖ ≤
    2 * ‖L‖ / ε₂ := by
  by_cases hcond :
      ε₂ < ‖L‖ * |t - t₀| ∧
      ‖L‖ * |t - t₀| ≤ ε₁
  · rw [if_pos hcond]
    have h_lo :
        ε₂ / (2 * ‖L‖) ≤ |t - t₀| :=
      le_of_lt (by
        calc ε₂ / (2 * ‖L‖) < ε₂ / ‖L‖ :=
              div_lt_div_of_pos_left hε₂_pos
                hL_pos (by linarith)
          _ ≤ |t - t₀| := by
              rw [div_le_iff₀ hL_pos, mul_comm]
              exact le_of_lt hcond.1)
    exact le_trans
      (singular_symmDiff_sup_bound
        (by positivity) h_lo)
      (by rw [one_div, inv_div])
  · simp only [hcond, ite_false, norm_zero]
    positivity

/-! ### Helper: symmetric difference volume bound via a.e. correction -/

private lemma singular_annulus_symmDiff_vol_via_ae
    {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    {ε₁ ε₂ : ℝ} {δ₀' δ_meas Kmeas : ℝ}
    (hε₂_pos : 0 < ε₂) (hε₂_le : ε₂ ≤ ε₁)
    (hε₁_lt_δ_meas : ε₁ < δ_meas)
    (h_meas : ∀ ε₁' ε₂' : ℝ,
      0 < ε₂' → ε₂' ≤ ε₁' → ε₁' < δ_meas →
      volume (symmDiff
        {t | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
          ε₂' < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁'}
        {t | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
          ε₂' < ‖L‖ * |t - t₀| ∧
          ‖L‖ * |t - t₀| ≤ ε₁'}) ≤
      ENNReal.ofReal (Kmeas * ε₁' ^ 2 / ‖L‖ ^ 3))
    (h' : ℝ → ℝ)
    (hh'_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc a b)), ‖γ t - γ t₀‖ = h' t) :
    volume (symmDiff
      {t | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
        ε₂ < h' t ∧ h' t ≤ ε₁}
      {t | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
        ε₂ < ‖L‖ * |t - t₀| ∧
        ‖L‖ * |t - t₀| ≤ ε₁}) ≤
    ENNReal.ofReal (Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3) := by
  set γAnn' := {t : ℝ |
    t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
    ε₂ < h' t ∧ h' t ≤ ε₁}
  set γAnn := {t : ℝ |
    t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
    ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁}
  set tAnnLin_loc := {t : ℝ |
    t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
    ε₂ < ‖L‖ * |t - t₀| ∧
    ‖L‖ * |t - t₀| ≤ ε₁}
  have h_sd_subset :
      symmDiff γAnn' γAnn ⊆
      {t : ℝ |
        t ∈ Set.Icc a b ∧
        h' t ≠ ‖γ t - γ t₀‖} := by
    intro t ht
    simp only [Set.mem_symmDiff,
      Set.mem_setOf_eq] at ht ⊢
    rcases ht with ⟨h_in, h_not⟩ |
      ⟨h_in, h_not⟩
    · refine ⟨h_in.1, fun heq => h_not ?_⟩
      exact ⟨h_in.1, h_in.2.1,
        heq ▸ h_in.2.2.1, heq ▸ h_in.2.2.2⟩
    · refine ⟨h_in.1, fun heq => h_not ?_⟩
      exact ⟨h_in.1, h_in.2.1,
        heq.symm ▸ h_in.2.2.1,
        heq.symm ▸ h_in.2.2.2⟩
  have h_null_set :
      volume {t : ℝ |
        t ∈ Set.Icc a b ∧
        h' t ≠ ‖γ t - γ t₀‖} = 0 := by
    have h_ae_not :
        (volume.restrict (Set.Icc a b))
          {t | ¬(‖γ t - γ t₀‖ = h' t)} = 0 :=
      MeasureTheory.ae_iff.mp hh'_ae
    rw [show {t | t ∈ Set.Icc a b ∧
          h' t ≠ ‖γ t - γ t₀‖} =
        {t | ¬(‖γ t - γ t₀‖ = h' t)} ∩
        Set.Icc a b from by
      ext t
      simp only [Set.mem_setOf_eq,
        Set.mem_inter_iff, Set.mem_Icc,
        ne_eq, eq_comm]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩,
             fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩]
    rw [← MeasureTheory.Measure.restrict_apply'
      measurableSet_Icc]
    exact h_ae_not
  have h_sd_zero :
      volume (symmDiff γAnn' γAnn) = 0 :=
    le_antisymm
      (le_of_le_of_eq
        (MeasureTheory.measure_mono h_sd_subset)
        h_null_set)
      (zero_le _)
  calc volume (symmDiff γAnn' tAnnLin_loc)
      ≤ volume (symmDiff γAnn' γAnn) +
          volume (symmDiff γAnn tAnnLin_loc) :=
          MeasureTheory.measure_symmDiff_le
            γAnn' γAnn tAnnLin_loc
    _ = 0 +
          volume (symmDiff γAnn tAnnLin_loc) := by
          rw [h_sd_zero]
    _ = volume (symmDiff γAnn tAnnLin_loc) := by
          simp only [zero_add]
    _ ≤ ENNReal.ofReal
            (Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3) :=
          h_meas ε₁ ε₂ hε₂_pos hε₂_le
            hε₁_lt_δ_meas

lemma singular_annulus_bound_explicit
    {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    (hab : a < b) (hat₀ : t₀ ∈ Set.Ioo a b)
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀)
    (hγ_deriv : deriv γ t₀ = L) (hL : L ≠ 0)
    (hγ_cont : ContinuousOn γ (Set.Icc a b))
    (h_inj : ∀ t ∈ Set.Icc a b,
      γ t = γ t₀ → t = t₀) :
    ∃ Csing > 0, ∃ δ > 0,
    ∀ ε₁ ε₂ : ℝ,
    0 < ε₂ → ε₂ ≤ ε₁ → ε₁ ≤ 2 * ε₂ → ε₁ < δ →
    ‖∫ t in a..b,
      if ε₂ < ‖γ t - γ t₀‖ ∧
        ‖γ t - γ t₀‖ ≤ ε₁
      then (↑(t - t₀) : ℂ)⁻¹ else 0‖ ≤
      Csing * ε₁ := by
  -- Step 1: Set up constants from prerequisites
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  obtain ⟨Kmeas, hKmeas_pos, δ₀', hδ₀'_pos,
      δ_meas, hδ_meas_pos, h_meas⟩ :=
    annulus_symmDiff_measure_bound hab hat₀
      hγ_C2 hγ_deriv hL
  have hγ_diff : DifferentiableAt ℝ γ t₀ :=
    hγ_C2.differentiableAt two_ne_zero
  have hγ_hasderiv : HasDerivAt γ L t₀ := by
    rw [← hγ_deriv]; exact hγ_diff.hasDerivAt
  obtain ⟨δ_lo, hδ_lo_pos, h_lower⟩ :=
    gamma_lower_bound_of_hasDerivAt hL hγ_hasderiv
  obtain ⟨δ_up, hδ_up_pos, h_upper⟩ :=
    gamma_upper_bound_of_hasDerivAt hL hγ_hasderiv
  let δ₁ := min δ₀' (min δ_lo δ_up)
  have hδ₁_pos : 0 < δ₁ :=
    lt_min hδ₀'_pos (lt_min hδ_lo_pos hδ_up_pos)
  obtain ⟨ρ, hρ_pos, h_far_bound⟩ :=
    no_return_of_inj_continuous hδ₁_pos hγ_cont h_inj
  have ht₀_mem := Set.mem_Ioo.mp hat₀
  have h_dist_pos :
      0 < min (t₀ - a) (b - t₀) := by
    simp only [lt_min_iff]
    constructor <;> linarith
  let δ := min (min δ_meas ρ)
    (min (‖L‖ * min (t₀ - a) (b - t₀)) (‖L‖ * δ₀'))
  have hδ_pos : 0 < δ :=
    lt_min (lt_min hδ_meas_pos hρ_pos)
      (lt_min (mul_pos hL_pos h_dist_pos)
              (mul_pos hL_pos hδ₀'_pos))
  let Csing := 4 * Kmeas / ‖L‖^2
  have hCsing_pos : 0 < Csing := by positivity
  use Csing, hCsing_pos, δ, hδ_pos
  intro ε₁ ε₂ hε₂_pos hε₂_le h_ratio hε₁_lt
  have hε₁_pos : 0 < ε₁ :=
    lt_of_lt_of_le hε₂_pos hε₂_le
  have hε₁_lt_δ_meas : ε₁ < δ_meas :=
    calc ε₁ < δ := hε₁_lt
      _ ≤ min δ_meas ρ := min_le_left _ _
      _ ≤ δ_meas := min_le_left _ _
  have hε₁_lt_ρ : ε₁ < ρ :=
    calc ε₁ < δ := hε₁_lt
      _ ≤ min δ_meas ρ := min_le_left _ _
      _ ≤ ρ := min_le_right _ _
  have hε₁_lt_Ldist :
      ε₁ < ‖L‖ * min (t₀ - a) (b - t₀) :=
    calc ε₁ < δ := hε₁_lt
      _ ≤ min (‖L‖ * min (t₀ - a) (b - t₀))
              (‖L‖ * δ₀') := min_le_right _ _
      _ ≤ ‖L‖ * min (t₀ - a) (b - t₀) :=
          min_le_left _ _
  have hε₁_lt_Lδ₀' : ε₁ < ‖L‖ * δ₀' :=
    calc ε₁ < δ := hε₁_lt
      _ ≤ min (‖L‖ * min (t₀ - a) (b - t₀))
              (‖L‖ * δ₀') := min_le_right _ _
      _ ≤ ‖L‖ * δ₀' := min_le_right _ _
  have h_localize :
      ∀ t ∈ Set.Icc a b,
      ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < δ₁ := by
    intro t ht hγt
    by_contra h_not_lt
    push_neg at h_not_lt
    have h_far := h_far_bound t ht h_not_lt
    linarith
  -- Step 2: The linearized integral vanishes (extracted helper)
  have hJ_lin_zero :
      (∫ t in a..b,
        if ε₂ < ‖L‖ * |t - t₀| ∧
          ‖L‖ * |t - t₀| ≤ ε₁
        then (↑(t - t₀) : ℂ)⁻¹ else 0) = 0 :=
    singular_annulus_lin_integral_zero hL_pos
      hε₁_pos hε₂_pos hε₂_le hε₁_lt_Ldist hat₀
  -- Step 3: Set up difference integrand with extracted helpers
  set f_γ : ℝ → ℂ := fun t =>
    if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
    then (↑(t - t₀) : ℂ)⁻¹ else 0 with hf_γ_def
  set f_lin : ℝ → ℂ := fun t =>
    if ε₂ < ‖L‖ * |t - t₀| ∧
      ‖L‖ * |t - t₀| ≤ ε₁
    then (↑(t - t₀) : ℂ)⁻¹ else 0 with hf_lin_def
  set d : ℝ → ℂ := fun t => f_γ t - f_lin t
    with hd_def
  set bound := 2 * ‖L‖ / ε₂ with hbound_def
  have hbound_pos : 0 < bound := by positivity
  have hd_bound_on_Icc :
      ∀ t ∈ Set.Icc a b, ‖d t‖ ≤ bound := by
    intro t ht; simp only [hd_def, hf_γ_def, hf_lin_def]
    exact singular_annulus_diff_pointwise_bound
      hL_pos hε₂_pos h_localize
      (le_trans (min_le_right _ _) (min_le_right _ _))
      h_upper t ht
  have hf_lin_meas : Measurable f_lin := by
    simp only [hf_lin_def]; exact singular_annulus_f_lin_measurable
  have hf_lin_bound :
      ∀ t : ℝ, ‖f_lin t‖ ≤ bound := by
    intro t; simp only [hf_lin_def]
    exact singular_annulus_f_lin_bound hL_pos hε₂_pos t
  have hf_lin_int :
      IntervalIntegrable f_lin MeasureTheory.volume a b := by
    rw [intervalIntegrable_iff]
    exact MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
      hf_lin_meas.aestronglyMeasurable.restrict bound
      (Filter.Eventually.of_forall (fun x => hf_lin_bound x))
  have hf_γ_eq : ∀ t, f_γ t = d t + f_lin t := by
    intro t; simp only [hd_def]; ring
  -- AE measurable version of the gamma norm
  have h_norm_cont :
      ContinuousOn (fun t => ‖γ t - γ t₀‖)
        (Set.Icc a b) :=
    (hγ_cont.sub continuousOn_const).norm
  have h_norm_aesm :
      AEStronglyMeasurable
        (fun t => ‖γ t - γ t₀‖)
        (MeasureTheory.volume.restrict
          (Set.Icc a b)) :=
    h_norm_cont.aestronglyMeasurable
      measurableSet_Icc
  set h' := h_norm_aesm.mk (fun t => ‖γ t - γ t₀‖)
    with hh'_def
  have hh'_sm : StronglyMeasurable h' :=
    h_norm_aesm.stronglyMeasurable_mk
  have hh'_ae :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict
        (Set.Icc a b)),
      ‖γ t - γ t₀‖ = h' t :=
    h_norm_aesm.ae_eq_mk
  set f_γ' : ℝ → ℂ := fun t =>
    if ε₂ < h' t ∧ h' t ≤ ε₁
    then (↑(t - t₀) : ℂ)⁻¹ else 0 with hf_γ'_def
  have hf_γ'_meas : Measurable f_γ' := by
    simp only [hf_γ'_def]; apply Measurable.ite
    · exact (hh'_sm.measurable measurableSet_Ioi).inter
        (hh'_sm.measurable measurableSet_Iic)
    · exact (Complex.measurable_ofReal.comp (measurable_id.sub_const t₀)).inv
    · exact measurable_const
  have hf_γ_ae_eq :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
      f_γ t = f_γ' t := by
    filter_upwards [hh'_ae] with t ht_eq
    simp only [hf_γ_def, hf_γ'_def, ht_eq]
  have hf_γ_aesm :
      AEStronglyMeasurable f_γ
        (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (hf_γ'_meas.aestronglyMeasurable.congr
      (Filter.EventuallyEq.symm hf_γ_ae_eq)).mono_measure
      (MeasureTheory.Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
  have hd_int : IntervalIntegrable d MeasureTheory.volume a b := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hab.le]
    exact MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
      (hf_γ_aesm.sub hf_lin_meas.aestronglyMeasurable.restrict) bound
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall
          (fun t ht => hd_bound_on_Icc t (Set.Ioc_subset_Icc_self ht))))
  -- Decompose integral and reduce to Ioc integral of d'
  rw [show (∫ t in a..b, f_γ t) = ∫ t in a..b, f_γ t from rfl,
    show (∫ t in a..b, f_γ t) = (∫ t in a..b, d t) + (∫ t in a..b, f_lin t) from by
      rw [← intervalIntegral.integral_add hd_int hf_lin_int]
      exact intervalIntegral.integral_congr (fun t _ => hf_γ_eq t),
    hJ_lin_zero, add_zero, intervalIntegral.integral_of_le hab.le]
  -- Step 4: Symmetric difference and measurability setup
  set γAnn' := {t : ℝ | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
    ε₂ < h' t ∧ h' t ≤ ε₁}
  set tAnnLin_loc := {t : ℝ | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
    ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁}
  set S' := symmDiff γAnn' tAnnLin_loc with hS'_def
  have hγAnn'_meas : MeasurableSet γAnn' := by
    apply MeasurableSet.inter; · exact measurableSet_Icc
    apply MeasurableSet.inter
    · exact (isOpen_lt (continuous_abs.comp
        (continuous_id.sub continuous_const)) continuous_const).measurableSet
    · exact (hh'_sm.measurable measurableSet_Ioi).inter
        (hh'_sm.measurable measurableSet_Iic)
  have htAnnLin_meas : MeasurableSet tAnnLin_loc := by
    apply MeasurableSet.inter; · exact measurableSet_Icc
    apply MeasurableSet.inter
    · exact (isOpen_lt (continuous_abs.comp
        (continuous_id.sub continuous_const)) continuous_const).measurableSet
    · apply MeasurableSet.inter
      · exact (isOpen_lt continuous_const (continuous_const.mul
          (continuous_abs.comp (continuous_id.sub continuous_const)))).measurableSet
      · exact (isClosed_le (continuous_const.mul
          (continuous_abs.comp (continuous_id.sub continuous_const)))
          continuous_const).measurableSet
  have hS'_meas : MeasurableSet S' := hγAnn'_meas.symmDiff htAnnLin_meas
  set d' : ℝ → ℂ := fun t => f_γ' t - f_lin t with hd'_def
  have hd_ae_eq :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a b)), d t = d' t := by
    filter_upwards [hf_γ_ae_eq] with t ht_eq
    simp only [hd_def, hd'_def, ht_eq]
  have h_int_eq :
      (∫ t in Set.Ioc a b, d t ∂volume) = ∫ t in Set.Ioc a b, d' t ∂volume := by
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioc
    filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hd_ae_eq]
      with t h_eq ht_Ioc
    exact h_eq (Set.Ioc_subset_Icc_self ht_Ioc)
  rw [h_int_eq]
  -- Step 5: Indicator bound and final calc
  set g_comp : ℝ → ℝ := S'.indicator (fun _ => bound) with hg_comp_def
  have hS'_finite : volume S' < ⊤ := by
    calc volume S' ≤ volume (Set.Icc a b) := by
          apply MeasureTheory.measure_mono
          intro t ht; rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h.1
      _ < ⊤ := measure_Icc_lt_top
  have hS'_vol_bound :
      volume S' ≤ ENNReal.ofReal (Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3) :=
    singular_annulus_symmDiff_vol_via_ae hε₂_pos hε₂_le hε₁_lt_δ_meas h_meas h' hh'_ae
  have hg_int_Ioc :
      MeasureTheory.Integrable g_comp (volume.restrict (Set.Ioc a b)) :=
    ((by constructor <;> exact (MeasureTheory.integrableOn_const
      (hs := measure_Ioc_lt_top.ne)).indicator hS'_meas :
      IntervalIntegrable g_comp volume a b)).1
  have h_pw_le_restrict :
      ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖d' t‖ ≤ g_comp t := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{t | t ∈ Set.Icc a b → d t = d' t},
      (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hd_ae_eq, ?_⟩
    intro t ht ht_Ioc
    simp only [g_comp, hg_comp_def, S', Set.indicator]
    by_cases ht_S : t ∈ symmDiff γAnn' tAnnLin_loc
    · simp only [ht_S, ↓reduceIte]
      rw [← ht (Set.Ioc_subset_Icc_self ht_Ioc)]
      exact hd_bound_on_Icc t (Set.Ioc_subset_Icc_self ht_Ioc)
    · simp only [ht_S, ↓reduceIte]
      have ht_Icc := Set.Ioc_subset_Icc_self ht_Ioc
      suffices h_dt_zero : d t = 0 by
        rw [(ht ht_Icc).symm, h_dt_zero, norm_zero]
      simp only [hd_def, hf_γ_def, hf_lin_def]
      by_cases hδ : |t - t₀| < δ₀'
      · have h_agree :
            (ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁) ↔
            (ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁) := by
          have hfγ_eq : f_γ t = f_γ' t := by
            have h := ht ht_Icc
            have hd_t : d t = f_γ t - f_lin t := rfl
            have hd'_t : d' t = f_γ' t - f_lin t := rfl
            rw [hd_t, hd'_t] at h
            have := congr_arg (· + f_lin t) h
            simp [sub_add_cancel] at this
            exact this
          have h_not_sd := ht_S; rw [Set.mem_symmDiff] at h_not_sd; push_neg at h_not_sd
          have h'_iff_lin :
              (ε₂ < h' t ∧ h' t ≤ ε₁) ↔
              (ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁) := by
            constructor
            · intro ⟨h1, h2⟩; exact (h_not_sd.1 ⟨ht_Icc, hδ, h1, h2⟩).2.2
            · intro ⟨h1, h2⟩; exact (h_not_sd.2 ⟨ht_Icc, hδ, h1, h2⟩).2.2
          by_cases ht_eq : t = t₀
          · subst ht_eq; simp only [sub_self, norm_zero, abs_zero, mul_zero]
          · have hinv_ne : (↑(t - t₀) : ℂ)⁻¹ ≠ 0 :=
              inv_ne_zero (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr ht_eq))
            constructor
            · intro hγ_cond
              have hfγ_t : f_γ t = (↑(t - t₀) : ℂ)⁻¹ := if_pos hγ_cond
              rw [hfγ_t] at hfγ_eq
              by_contra h_neg
              have hfγ'_t : f_γ' t = 0 := by
                show (if ε₂ < h' t ∧ h' t ≤ ε₁
                  then (↑(t - t₀) : ℂ)⁻¹ else 0) = 0
                exact if_neg (mt h'_iff_lin.mp h_neg)
              rw [hfγ'_t] at hfγ_eq
              exact hinv_ne hfγ_eq
            · intro hlin_cond
              have hh'_cond := h'_iff_lin.mpr hlin_cond
              have hfγ'_t : f_γ' t = (↑(t - t₀) : ℂ)⁻¹ := if_pos hh'_cond
              rw [hfγ'_t] at hfγ_eq
              by_contra h_neg
              have hfγ_t : f_γ t = 0 := if_neg h_neg
              rw [hfγ_t] at hfγ_eq
              exact hinv_ne hfγ_eq.symm
        by_cases hcond : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
        · simp [hcond, h_agree.mp hcond, sub_self]
        · simp [hcond, mt h_agree.mpr hcond]
      · have hγ_fail : ¬(ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁) := by
          intro ⟨_, h_up⟩
          have := h_localize t ht_Icc h_up
          have : |t - t₀| < δ₀' := lt_of_lt_of_le this (min_le_left _ _)
          linarith [not_lt.mp hδ]
        have hlin_fail : ¬(ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁) := by
          intro ⟨_, h_le⟩
          linarith [mul_le_mul_of_nonneg_left (not_lt.mp hδ) (le_of_lt hL_pos)]
        simp [hγ_fail, hlin_fail]
  calc ‖∫ t in Set.Ioc a b, d' t‖
      ≤ ∫ t in Set.Ioc a b, g_comp t :=
        MeasureTheory.norm_integral_le_of_norm_le hg_int_Ioc h_pw_le_restrict
    _ = ∫ t in (Set.Ioc a b) ∩ S', (fun _ => bound) t := by
        rw [MeasureTheory.setIntegral_indicator hS'_meas]
    _ = volume.real ((Set.Ioc a b) ∩ S') * bound := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul]
    _ ≤ volume.real S' * bound := by
        exact mul_le_mul_of_nonneg_right
          (measureReal_mono Set.inter_subset_right hS'_finite.ne) (le_of_lt hbound_pos)
    _ ≤ (Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3) * bound := by
        exact mul_le_mul_of_nonneg_right
          (ENNReal.toReal_le_of_le_ofReal (by positivity) hS'_vol_bound) (le_of_lt hbound_pos)
    _ ≤ Csing * ε₁ := by
        suffices h :
            Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3 * bound ≤
            Csing * ε₁ by exact h
        change Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3 *
          (2 * ‖L‖ / ε₂) ≤
          4 * Kmeas / ‖L‖ ^ 2 * ε₁
        have h1 :
            Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3 *
            (2 * ‖L‖ / ε₂) =
            2 * Kmeas * ε₁ ^ 2 * ‖L‖ /
            (‖L‖ ^ 3 * ε₂) := by ring
        have h2 :
            4 * Kmeas / ‖L‖ ^ 2 * ε₁ =
            4 * Kmeas * ε₁ / ‖L‖ ^ 2 := by ring
        rw [h1, h2]
        rw [div_le_div_iff₀
          (mul_pos
            (by positivity : (0:ℝ) < ‖L‖ ^ 3)
            hε₂_pos)
          (by positivity : (0:ℝ) < ‖L‖ ^ 2)]
        have key : ε₁ ^ 2 ≤ ε₁ * (2 * ε₂) := by
          rw [sq]
          exact mul_le_mul_of_nonneg_left h_ratio
            (le_of_lt hε₁_pos)
        nlinarith [mul_pos hKmeas_pos
          (pow_pos hL_pos 3)]


end
