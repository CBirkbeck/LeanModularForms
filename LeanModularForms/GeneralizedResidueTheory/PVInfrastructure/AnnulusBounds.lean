/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.PVInfrastructure.GammaAnalysis
import LeanModularForms.GeneralizedResidueTheory.PVInfrastructure.RemainderAnalysis
import LeanModularForms.GeneralizedResidueTheory.PVInfrastructure.StepBounds

/-!
# PV Infrastructure: Annulus Bounds

Measure-theoretic and analytic bounds on annular regions around
crossing points, used in the dyadic PV convergence proof.

## Main Results

* `annulus_t_measure_bound` — t-measure of gamma-annulus
* `remainder_integral_bound_on_annulus` — remainder integral
    over annulus is O(epsilon)
* `annulus_symmDiff_measure_bound` — symmetric difference
    between gamma-annulus and linear-model annulus
* `singular_annulus_bound_explicit` — epsilon-independent
    bound on singular annulus integral
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

lemma annulus_t_measure_bound {γ : ℝ → ℂ}
    {a b t₀ : ℝ} {L : ℂ} {ε₁ ε₂ δ₁ : ℝ}
    (hL : L ≠ 0) (hε₁_pos : 0 < ε₁)
    (h_lower : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₁ →
      ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀|)
    (h_localize : ∀ t ∈ Set.Icc a b,
      ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₁ δ₁)
    (t : ℝ) (ht_ab : t ∈ Set.Icc a b)
    (ht_ne : t ≠ t₀)
    (_hγ_lower : ε₂ < ‖γ t - γ t₀‖)
    (hγ_upper : ‖γ t - γ t₀‖ ≤ ε₁) :
    |t - t₀| ≤ 2 * ε₁ / ‖L‖ := by
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have ht_local := h_localize t ht_ab hγ_upper
  have ht_pos : 0 < |t - t₀| :=
    abs_pos.mpr (sub_ne_zero.mpr ht_ne)
  have ht_lt_δ₁ : |t - t₀| < δ₁ :=
    lt_of_lt_of_le ht_local (min_le_right _ _)
  exact t_bound_from_gamma_annulus hL hε₁_pos
    h_lower t ht_pos ht_lt_δ₁ hγ_upper

lemma remainder_integral_bound_on_annulus
    {γ : ℝ → ℂ} {a b t₀ : ℝ}
    {C δ₀ δ₁ ε₁ ε₂ : ℝ} {L : ℂ}
    (hL : L ≠ 0) (hε₁_pos : 0 < ε₁)
    (hε₂_pos : 0 < ε₂)
    (hr_bounded : ∀ t, 0 < |t - t₀| →
      |t - t₀| < δ₀ →
      ‖(γ t - γ t₀)⁻¹ * deriv γ t -
        (↑(t - t₀))⁻¹‖ ≤ C)
    (h_lower : ∀ t, 0 < |t - t₀| →
      |t - t₀| < δ₁ →
      ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀|)
    (h_localize : ∀ t ∈ Set.Icc a b,
      ‖γ t - γ t₀‖ ≤ ε₁ →
      |t - t₀| < min δ₀ δ₁)
    (hat₀ : t₀ ∈ Set.Ioo a b) :
    let r := fun t =>
      (γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹
    ‖∫ t in a..b,
      if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
        then r t else 0‖ ≤
      max 0 C * (4 * ε₁ / ‖L‖) := by
  intro r
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hab : a < b :=
    (Set.mem_Ioo.mp hat₀).1.trans_le
      (le_of_lt (Set.mem_Ioo.mp hat₀).2)
  have h_pw_bound :
      ∀ t ∈ Set.uIoc a b,
      ‖if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
        then r t else 0‖ ≤ max 0 C := by
    intro t ht
    by_cases hcond :
        ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
    · rw [if_pos hcond]
      have ht_in_Icc : t ∈ Set.Icc a b := by
        rw [Set.uIoc_eq_union] at ht
        rcases ht with ht_ab | ht_ba
        · exact Set.Ioc_subset_Icc_self ht_ab
        · rw [Set.Ioc_eq_empty_of_le hab.le] at ht_ba
          exact absurd ht_ba (Set.notMem_empty t)
      have ht_loc := h_localize t ht_in_Icc hcond.2
      by_cases ht_eq : t = t₀
      · simp only [ht_eq, sub_self, norm_zero] at hcond
        exact absurd hcond.1 (not_lt.mpr hε₂_pos.le)
      have ht_pos : 0 < |t - t₀| :=
        abs_pos.mpr (sub_ne_zero.mpr ht_eq)
      have ht_lt_δ₀ : |t - t₀| < δ₀ :=
        lt_of_lt_of_le ht_loc (min_le_left _ _)
      have hr_t := hr_bounded t ht_pos ht_lt_δ₀
      simp only [r] at hr_t ⊢
      exact le_trans hr_t (le_max_right 0 C)
    · simp only [hcond, ↓reduceIte, norm_zero,
        le_max_iff, le_refl, true_or]
  let S := {t ∈ Set.Icc a b |
    ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁}
  have hS_subset : S ⊆
      Set.Icc (t₀ - 2 * ε₁ / ‖L‖)
              (t₀ + 2 * ε₁ / ‖L‖) := by
    intro t ht
    obtain ⟨ht_ab, hε_lower, hε_upper⟩ := ht
    have h_loc_adapted :
        ∀ t ∈ Set.Icc a b,
        ‖γ t - γ t₀‖ ≤ ε₁ →
        |t - t₀| < min δ₁ δ₁ := by
      intro s hs hγs
      simp only [min_self]
      exact lt_of_lt_of_le (h_localize s hs hγs)
        (min_le_right _ _)
    by_cases ht_eq : t = t₀
    · rw [ht_eq, Set.mem_Icc]
      have h_term_pos : 0 < 2 * ε₁ / ‖L‖ := by
        positivity
      constructor
      · linarith [h_term_pos]
      · linarith [h_term_pos]
    have ht_bound :=
      annulus_t_measure_bound hL hε₁_pos h_lower
        h_loc_adapted t ht_ab ht_eq hε_lower hε_upper
    rw [abs_le] at ht_bound
    exact Set.mem_Icc.mpr
      ⟨by linarith [ht_bound.1],
       by linarith [ht_bound.2]⟩
  have hS_measure :
      MeasureTheory.volume S ≤
      ENNReal.ofReal (4 * ε₁ / ‖L‖) := by
    have h_width :
        (t₀ + 2 * ε₁ / ‖L‖) -
        (t₀ - 2 * ε₁ / ‖L‖) = 4 * ε₁ / ‖L‖ := by
      ring
    calc MeasureTheory.volume S
        ≤ MeasureTheory.volume
          (Set.Icc (t₀ - 2 * ε₁ / ‖L‖)
                   (t₀ + 2 * ε₁ / ‖L‖)) :=
          MeasureTheory.measure_mono hS_subset
      _ = ENNReal.ofReal
          ((t₀ + 2 * ε₁ / ‖L‖) -
           (t₀ - 2 * ε₁ / ‖L‖)) :=
          Real.volume_Icc
      _ = ENNReal.ofReal (4 * ε₁ / ‖L‖) := by
          rw [h_width]
  have hr_bound_on_S :
      ∀ t ∈ S, ‖r t‖ ≤ max 0 C := by
    intro t ⟨ht_ab, hε_lower, hε_upper⟩
    by_cases ht_eq : t = t₀
    · simp only [ht_eq, sub_self, norm_zero]
        at hε_lower
      exact absurd hε_lower (not_lt.mpr hε₂_pos.le)
    have ht_loc := h_localize t ht_ab hε_upper
    have ht_pos : 0 < |t - t₀| :=
      abs_pos.mpr (sub_ne_zero.mpr ht_eq)
    have ht_lt_δ₀ : |t - t₀| < δ₀ :=
      lt_of_lt_of_le ht_loc (min_le_left _ _)
    have hr_t := hr_bounded t ht_pos ht_lt_δ₀
    simp only [r] at hr_t ⊢
    exact le_trans hr_t (le_max_right 0 C)
  have h_zero_of_far :
      ∀ t ∈ Set.uIoc a b,
      2 * ε₁ / ‖L‖ < |t - t₀| →
      (if ε₂ < ‖γ t - γ t₀‖ ∧
          ‖γ t - γ t₀‖ ≤ ε₁
        then r t else 0) = 0 := by
    intro t ht h_far
    by_cases hcond :
        ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
    · exfalso
      have ht_in_Icc : t ∈ Set.Icc a b := by
        rw [Set.uIoc_eq_union] at ht
        rcases ht with ht_ab | ht_ba
        · exact Set.Ioc_subset_Icc_self ht_ab
        · rw [Set.Ioc_eq_empty_of_le hab.le] at ht_ba
          exact absurd ht_ba (Set.notMem_empty t)
      by_cases ht_eq : t = t₀
      · simp only [ht_eq, sub_self, norm_zero]
          at hcond
        exact absurd hcond.1
          (not_lt.mpr hε₂_pos.le)
      have h_loc_adapted :
          ∀ s ∈ Set.Icc a b,
          ‖γ s - γ t₀‖ ≤ ε₁ →
          |s - t₀| < min δ₁ δ₁ := by
        intro s hs hγs; simp only [min_self]
        exact lt_of_lt_of_le (h_localize s hs hγs)
          (min_le_right _ _)
      have ht_bound :=
        annulus_t_measure_bound hL hε₁_pos h_lower
          h_loc_adapted t ht_in_Icc ht_eq hcond.1
          hcond.2
      exact not_lt.mpr ht_bound h_far
    · simp only [hcond, ↓reduceIte]
  set R := 2 * ε₁ / ‖L‖ with hR_def
  have hR_pos : 0 < R := by positivity
  set Icontain :=
    Set.Icc (t₀ - R) (t₀ + R) with hI_def
  set g_comp : ℝ → ℝ :=
    Icontain.indicator (fun _ => max 0 C)
    with hg_comp_def
  have hg_int :
      IntervalIntegrable g_comp volume a b := by
    constructor <;>
      exact (MeasureTheory.integrableOn_const
        (hs := measure_Ioc_lt_top.ne)).indicator
        measurableSet_Icc
  have h_pw_le :
      ∀ᵐ t ∂volume, t ∈ Set.Ioc a b →
      ‖if ε₂ < ‖γ t - γ t₀‖ ∧
          ‖γ t - γ t₀‖ ≤ ε₁
        then r t else 0‖ ≤ g_comp t := by
    apply Filter.Eventually.of_forall
    intro t ht
    simp only [g_comp, Set.indicator]
    by_cases ht_in : t ∈ Icontain
    · simp only [ht_in, ↓reduceIte]
      have ht_uIoc : t ∈ Ι a b := by
        rw [Set.uIoc_of_le hab.le]; exact ht
      exact h_pw_bound t ht_uIoc
    · simp only [ht_in, ↓reduceIte]
      have h_far : 2 * ε₁ / ‖L‖ < |t - t₀| := by
        simp only [Icontain, Set.mem_Icc,
          not_and_or, not_le] at ht_in
        rcases ht_in with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have ht_uIoc : t ∈ Ι a b := by
        rw [Set.uIoc_of_le hab.le]; exact ht
      rw [h_zero_of_far t ht_uIoc h_far, norm_zero]
  calc ‖∫ t in a..b,
      if ε₂ < ‖γ t - γ t₀‖ ∧
          ‖γ t - γ t₀‖ ≤ ε₁
        then r t else 0‖
      ≤ ∫ t in a..b, g_comp t :=
        intervalIntegral.norm_integral_le_of_norm_le
          hab.le h_pw_le hg_int
    _ ≤ max 0 C * (4 * ε₁ / ‖L‖) := by
        rw [intervalIntegral.integral_of_le hab.le,
          MeasureTheory.integral_indicator
            measurableSet_Icc,
          MeasureTheory.setIntegral_const,
          smul_eq_mul, mul_comm]
        apply mul_le_mul_of_nonneg_left _
          (le_max_left 0 C)
        unfold MeasureTheory.Measure.real
        apply ENNReal.toReal_le_of_le_ofReal
          (by positivity)
        calc (volume.restrict (Set.Ioc a b))
              Icontain
            ≤ volume Icontain :=
              MeasureTheory.Measure.restrict_apply_le
                _ _
          _ = ENNReal.ofReal
              ((t₀ + R) - (t₀ - R)) :=
              Real.volume_Icc
          _ = ENNReal.ofReal (4 * ε₁ / ‖L‖) := by
              simp only [R]; ring_nf

lemma norm_linear_approx_bound {γ : ℝ → ℂ}
    {t₀ : ℝ} {L : ℂ} {K₀ δ₀ : ℝ}
    (h_quad : ∀ t, |t - t₀| < δ₀ →
      ‖γ t - γ t₀ - (t - t₀) • L‖ ≤
        K₀ * |t - t₀|^2)
    {t : ℝ} (ht : |t - t₀| < δ₀) :
    abs (‖γ t - γ t₀‖ - ‖L‖ * |t - t₀|) ≤
      K₀ * |t - t₀|^2 := by
  have h1 :
    ‖γ t - γ t₀ - (t - t₀) • L‖ ≤
      K₀ * |t - t₀|^2 := h_quad t ht
  have h2 :
    |‖γ t - γ t₀‖ - ‖(t - t₀) • L‖| ≤
      ‖γ t - γ t₀ - (t - t₀) • L‖ :=
    abs_norm_sub_norm_le _ _
  have h3 : ‖(t - t₀) • L‖ = |t - t₀| * ‖L‖ :=
    norm_smul (t - t₀) L
  rw [h3, mul_comm] at h2
  exact le_trans h2 h1

lemma volume_shell_le {t₀ r₁ r₂ : ℝ}
    (hr : r₁ ≤ r₂) :
    volume {t : ℝ |
      r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} ≤
      ENNReal.ofReal (2 * (r₂ - r₁)) := by
  have h_sub :
      {t : ℝ |
        r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} ⊆
      Set.Ico (t₀ - r₂) (t₀ - r₁) ∪
      Set.Ioc (t₀ + r₁) (t₀ + r₂) := by
    intro t ⟨h_lower, h_upper⟩
    by_cases ht : t ≥ t₀
    · right
      have habs : |t - t₀| = t - t₀ :=
        abs_of_nonneg (sub_nonneg.mpr ht)
      rw [habs] at h_lower h_upper
      exact ⟨by linarith, by linarith⟩
    · left
      push_neg at ht
      have habs : |t - t₀| = -(t - t₀) :=
        abs_of_neg (sub_neg.mpr ht)
      rw [habs] at h_lower h_upper
      exact ⟨by linarith, by linarith⟩
  calc volume {t : ℝ |
      r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂}
      ≤ volume (Set.Ico (t₀ - r₂) (t₀ - r₁) ∪
          Set.Ioc (t₀ + r₁) (t₀ + r₂)) :=
        MeasureTheory.measure_mono h_sub
    _ ≤ volume (Set.Ico (t₀ - r₂) (t₀ - r₁)) +
        volume (Set.Ioc (t₀ + r₁) (t₀ + r₂)) :=
        MeasureTheory.measure_union_le _ _
    _ = ENNReal.ofReal (r₂ - r₁) +
        ENNReal.ofReal (r₂ - r₁) := by
        simp only [Real.volume_Ico,
          Real.volume_Ioc]; ring_nf
    _ = ENNReal.ofReal (2 * (r₂ - r₁)) := by
        rw [← ENNReal.ofReal_add
          (by linarith) (by linarith)]; ring_nf

lemma symmDiff_subset_boundaryLayers
    {g x e ε₁ ε₂ : ℝ}
    (h_approx : |g - x| ≤ e)
    (h_xor :
      Xor' (ε₂ < g ∧ g ≤ ε₁)
           (ε₂ < x ∧ x ≤ ε₁)) :
    |x - ε₂| ≤ e ∨ |x - ε₁| ≤ e := by
  rcases h_xor with
    ⟨⟨hg_lower, hg_upper⟩, hnotB⟩ |
    ⟨⟨hx_lower, hx_upper⟩, hnotA⟩
  · by_cases hx_le_ε₂ : x ≤ ε₂
    · left
      have h1 : ε₂ - x ≤ g - x := by linarith
      have h2 : g - x ≤ |g - x| := le_abs_self _
      have hle : x - ε₂ ≤ 0 := by linarith
      calc |x - ε₂|
          = ε₂ - x := by rw [abs_of_nonpos hle]; ring
        _ ≤ g - x := h1
        _ ≤ |g - x| := h2
        _ ≤ e := h_approx
    · push_neg at hx_le_ε₂
      have hx_gt_ε₁ : ε₁ < x := by
        by_contra h_not
        push_neg at h_not
        exact hnotB ⟨hx_le_ε₂, h_not⟩
      right
      have h1 : x - ε₁ ≤ x - g := by linarith
      have h2 : x - g ≤ |g - x| := by
        rw [abs_sub_comm]; exact le_abs_self _
      calc |x - ε₁|
          = x - ε₁ := abs_of_pos (by linarith)
        _ ≤ x - g := h1
        _ ≤ |g - x| := h2
        _ ≤ e := h_approx
  · by_cases hg_le_ε₂ : g ≤ ε₂
    · left
      have h1 : x - ε₂ ≤ x - g := by linarith
      have h2 : x - g ≤ |g - x| := by
        rw [abs_sub_comm]; exact le_abs_self _
      calc |x - ε₂|
          = x - ε₂ := abs_of_pos (by linarith)
        _ ≤ x - g := h1
        _ ≤ |g - x| := h2
        _ ≤ e := h_approx
    · push_neg at hg_le_ε₂
      have hg_gt_ε₁ : ε₁ < g := by
        by_contra h_not
        push_neg at h_not
        exact hnotA ⟨hg_le_ε₂, h_not⟩
      right
      have h1 : ε₁ - x ≤ g - x := by linarith
      have h2 : g - x ≤ |g - x| := le_abs_self _
      have hle : x - ε₁ ≤ 0 := by linarith
      calc |x - ε₁|
          = ε₁ - x := by rw [abs_of_nonpos hle]; ring
        _ ≤ g - x := h1
        _ ≤ |g - x| := h2
        _ ≤ e := h_approx

lemma tAnnLin_implies_r_le
    {L_norm r ε₁ : ℝ} (hL_pos : 0 < L_norm)
    (h_in : L_norm * r ≤ ε₁) :
    r ≤ ε₁ / L_norm := by
  rw [le_div_iff₀ hL_pos, mul_comm]; exact h_in

lemma near_threshold_implies_r_in_shell
    {L_norm r ε K₀ R_max : ℝ}
    (hL_pos : 0 < L_norm)
    (hK₀_nonneg : 0 ≤ K₀)
    (hR_max_nonneg : 0 ≤ R_max)
    (hr_le : r ≤ R_max) (hr_nonneg : 0 ≤ r)
    (h_near : |L_norm * r - ε| ≤ K₀ * r^2) :
    (ε - K₀ * R_max^2) / L_norm ≤ r ∧
    r ≤ (ε + K₀ * R_max^2) / L_norm := by
  have h_abs := abs_le.mp h_near
  have h_lower : ε - K₀ * r^2 ≤ L_norm * r := by
    linarith [h_abs.1]
  have h_upper : L_norm * r ≤ ε + K₀ * r^2 := by
    linarith [h_abs.2]
  have hr2_le : r^2 ≤ R_max^2 :=
    sq_le_sq' (by linarith) hr_le
  have hK_r2_le : K₀ * r^2 ≤ K₀ * R_max^2 :=
    mul_le_mul_of_nonneg_left hr2_le hK₀_nonneg
  constructor
  · rw [div_le_iff₀ hL_pos]
    have h1 : ε - K₀ * R_max^2 ≤ ε - K₀ * r^2 := by
      linarith
    have h2 : ε - K₀ * r^2 ≤ L_norm * r := h_lower
    have h3 : L_norm * r = r * L_norm :=
      mul_comm _ _
    linarith
  · rw [le_div_iff₀ hL_pos]
    have h1 :
      ε + K₀ * r^2 ≤ ε + K₀ * R_max^2 := by
      linarith
    have h2 :
      L_norm * r ≤ ε + K₀ * r^2 := h_upper
    have h3 : L_norm * r = r * L_norm :=
      mul_comm _ _
    linarith

lemma shell_vol_le {t₀ ε Δ L_norm : ℝ}
    (hL_pos : 0 < L_norm)
    (hΔ_nonneg : 0 ≤ Δ) (_hε_pos : 0 < ε) :
    volume {t : ℝ |
      |L_norm * |t - t₀| - ε| ≤ Δ} ≤
      ENNReal.ofReal (4 * Δ / L_norm) := by
  by_cases h : ε ≤ Δ
  · have h_sub :
        {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ⊆
        {t : ℝ |
          |t - t₀| ≤ (ε + Δ) / L_norm} := by
      intro t ht
      simp only [Set.mem_setOf_eq] at ht ⊢
      have h_abs := abs_le.mp ht
      have h_upper :
        L_norm * |t - t₀| ≤ ε + Δ := by
        linarith [h_abs.2]
      calc |t - t₀|
          = (L_norm * |t - t₀|) / L_norm := by
            field_simp
        _ ≤ (ε + Δ) / L_norm := by
            apply div_le_div_of_nonneg_right
              h_upper hL_pos.le
    have h_ball :
        {t : ℝ |
          |t - t₀| ≤ (ε + Δ) / L_norm} =
        Set.Icc (t₀ - (ε + Δ) / L_norm)
                (t₀ + (ε + Δ) / L_norm) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Icc,
        abs_le]
      constructor <;> intro ⟨h1, h2⟩ <;>
        constructor <;> linarith
    have h_vol :
        volume (Set.Icc
          (t₀ - (ε + Δ) / L_norm)
          (t₀ + (ε + Δ) / L_norm)) =
        ENNReal.ofReal
          (2 * (ε + Δ) / L_norm) := by
      rw [Real.volume_Icc]; ring_nf
    calc volume {t : ℝ |
        |L_norm * |t - t₀| - ε| ≤ Δ}
        ≤ volume {t : ℝ |
            |t - t₀| ≤ (ε + Δ) / L_norm} :=
          MeasureTheory.measure_mono h_sub
      _ = volume (Set.Icc
            (t₀ - (ε + Δ) / L_norm)
            (t₀ + (ε + Δ) / L_norm)) := by
          rw [h_ball]
      _ = ENNReal.ofReal
            (2 * (ε + Δ) / L_norm) := h_vol
      _ ≤ ENNReal.ofReal
            (4 * Δ / L_norm) := by
          apply ENNReal.ofReal_le_ofReal
          have : ε + Δ ≤ 2 * Δ := by linarith
          calc 2 * (ε + Δ) / L_norm
              ≤ 2 * (2 * Δ) / L_norm := by
                apply div_le_div_of_nonneg_right _
                  hL_pos.le; linarith
            _ = 4 * Δ / L_norm := by ring
  · push_neg at h
    let r₁ := (ε - Δ) / L_norm
    let r₂ := (ε + Δ) / L_norm
    have hr₁_pos : 0 < r₁ := by
      simp only [r₁]
      apply div_pos; linarith; exact hL_pos
    have hr₁_le_r₂ : r₁ ≤ r₂ := by
      simp only [r₁, r₂]
      apply div_le_div_of_nonneg_right _ hL_pos.le
      linarith
    have h_sub :
        {t : ℝ |
          |L_norm * |t - t₀| - ε| ≤ Δ} ⊆
        {t : ℝ |
          r₁ ≤ |t - t₀| ∧
          |t - t₀| ≤ r₂} := by
      intro t ht
      simp only [Set.mem_setOf_eq] at ht
      have h_abs := abs_le.mp ht
      simp only [r₁, r₂, Set.mem_setOf_eq]
      constructor
      · calc (ε - Δ) / L_norm
            ≤ (L_norm * |t - t₀|) / L_norm := by
              apply div_le_div_of_nonneg_right _
                hL_pos.le; linarith [h_abs.1]
          _ = |t - t₀| := by field_simp
      · calc |t - t₀|
            = (L_norm * |t - t₀|) / L_norm := by
              field_simp
          _ ≤ (ε + Δ) / L_norm := by
              apply div_le_div_of_nonneg_right _
                hL_pos.le; linarith [h_abs.2]
    have h_sub_strict :
        {t : ℝ |
          r₁ ≤ |t - t₀| ∧ |t - t₀| ≤ r₂} ⊆
        {t : ℝ |
          r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} ∪
        {t : ℝ | |t - t₀| = r₁} := by
      intro t ⟨h1, h2⟩
      by_cases heq : |t - t₀| = r₁
      · right; exact heq
      · left
        exact ⟨lt_of_le_of_ne h1 (Ne.symm heq), h2⟩
    have h_singleton_null :
        volume {t : ℝ | |t - t₀| = r₁} = 0 := by
      have h_sub :
          {t : ℝ | |t - t₀| = r₁} ⊆
          {t₀ - r₁, t₀ + r₁} := by
        intro t ht
        simp only [Set.mem_setOf_eq] at ht
        simp only [Set.mem_insert_iff,
          Set.mem_singleton_iff]
        rcases (abs_eq hr₁_pos.le).mp ht with h1 | h1
        · right; linarith
        · left; linarith
      have h_finite :
          (({t₀ - r₁, t₀ + r₁} : Set ℝ)).Finite :=
        Set.toFinite _
      have h_pair_null :
          volume ({t₀ - r₁, t₀ + r₁} : Set ℝ) = 0 :=
        h_finite.measure_zero volume
      have h_le :
          volume {t : ℝ | |t - t₀| = r₁} ≤
          volume ({t₀ - r₁, t₀ + r₁} : Set ℝ) :=
        MeasureTheory.measure_mono h_sub
      simp only [h_pair_null, nonpos_iff_eq_zero]
        at h_le
      exact h_le
    have h_width :
        r₂ - r₁ = 2 * Δ / L_norm := by
      simp only [r₁, r₂]; field_simp; ring
    calc volume {t : ℝ |
        |L_norm * |t - t₀| - ε| ≤ Δ}
        ≤ volume {t : ℝ |
            r₁ ≤ |t - t₀| ∧ |t - t₀| ≤ r₂} :=
          MeasureTheory.measure_mono h_sub
      _ ≤ volume ({t : ℝ |
            r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} ∪
          {t : ℝ | |t - t₀| = r₁}) :=
          MeasureTheory.measure_mono h_sub_strict
      _ ≤ volume {t : ℝ |
            r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} +
          volume {t : ℝ | |t - t₀| = r₁} :=
          MeasureTheory.measure_union_le _ _
      _ = volume {t : ℝ |
            r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} +
          0 := by rw [h_singleton_null]
      _ = volume {t : ℝ |
            r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} := by
          ring
      _ ≤ ENNReal.ofReal (2 * (r₂ - r₁)) :=
          volume_shell_le hr₁_le_r₂
      _ = ENNReal.ofReal (2 * (2 * Δ / L_norm)) := by
          rw [h_width]
      _ = ENNReal.ofReal (4 * Δ / L_norm) := by
          ring_nf

lemma annulus_symmDiff_measure_bound
    {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    (_hab : a < b) (ht₀ : t₀ ∈ Set.Ioo a b)
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀)
    (hγ_deriv : deriv γ t₀ = L) (hL : L ≠ 0) :
    ∃ K > 0, ∃ δ₀' > 0, ∃ δ > 0,
    ∀ ε₁ ε₂ : ℝ,
    0 < ε₂ → ε₂ ≤ ε₁ → ε₁ < δ →
    let γAnn := {t : ℝ |
      t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
      ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁}
    let tAnnLin := {t : ℝ |
      t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
      ε₂ < ‖L‖ * |t - t₀| ∧
      ‖L‖ * |t - t₀| ≤ ε₁}
    volume (symmDiff γAnn tAnnLin) ≤
      ENNReal.ofReal (K * ε₁^2 / ‖L‖^3) := by
  obtain ⟨K₀, δ₀, hδ₀_pos, hK₀_pos, h_quad⟩ :=
    quadratic_approx_of_contDiffAt_two hγ_C2
      hγ_deriv
  have ht₀_dist_pos :
      0 < min (t₀ - a) (b - t₀) := by
    simp only [lt_min_iff, Set.mem_Ioo] at ht₀ ⊢
    constructor <;> linarith
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  let δ₁ := min δ₀ (‖L‖ / (4 * K₀))
  have hδ₁_pos : 0 < δ₁ :=
    lt_min hδ₀_pos
      (div_pos hL_norm_pos (by linarith))
  have hδ₁_le_δ₀ : δ₁ ≤ δ₀ := min_le_left _ _
  have hδ₁_le_L_over_4K : δ₁ ≤ ‖L‖ / (4 * K₀) :=
    min_le_right _ _
  have hδ₁_le_L_over_2K :
      δ₁ ≤ ‖L‖ / (2 * K₀) := by
    calc δ₁ ≤ ‖L‖ / (4 * K₀) := hδ₁_le_L_over_4K
      _ ≤ ‖L‖ / (2 * K₀) := by
          apply div_le_div_of_nonneg_left
            (le_of_lt hL_norm_pos) (by linarith)
          linarith
  have h_quad_small :
      ∀ r, r < δ₁ → K₀ * r ≤ ‖L‖ / 4 := by
    intro r hr
    calc K₀ * r
        ≤ K₀ * δ₁ := mul_le_mul_of_nonneg_left
          (le_of_lt hr) (le_of_lt hK₀_pos)
      _ ≤ K₀ * (‖L‖ / (4 * K₀)) :=
          mul_le_mul_of_nonneg_left
            hδ₁_le_L_over_4K (le_of_lt hK₀_pos)
      _ = ‖L‖ / 4 := by field_simp
  let δ := ‖L‖ * δ₁ / 2
  have hδ_pos : 0 < δ := by
    simp only [δ]; positivity
  use 32 * K₀, by linarith, δ₁, hδ₁_pos, δ, hδ_pos
  intro ε₁ ε₂ hε₂_pos hε₂_le hε₁_lt γAnn tAnnLin
  have hε₁_pos : 0 < ε₁ :=
    lt_of_lt_of_le hε₂_pos hε₂_le
  have hK₀_nonneg : 0 ≤ K₀ := le_of_lt hK₀_pos
  have hε₁_over_L_lt_δ₁ : ε₁ / ‖L‖ < δ₁ := by
    calc ε₁ / ‖L‖
        < (‖L‖ * δ₁ / 2) / ‖L‖ :=
          div_lt_div_of_pos_right hε₁_lt hL_norm_pos
      _ = δ₁ / 2 := by field_simp
      _ < δ₁ := by linarith [hδ₁_pos]
  have hε₁_over_L_lt_δ₀ : ε₁ / ‖L‖ < δ₀ :=
    lt_of_lt_of_le hε₁_over_L_lt_δ₁ hδ₁_le_δ₀
  have h2ε₁_over_L_lt_δ₁ :
      2 * ε₁ / ‖L‖ < δ₁ := by
    have h2 : 2 * ε₁ < ‖L‖ * δ₁ := by
      have : ε₁ < ‖L‖ * δ₁ / 2 := hε₁_lt
      linarith
    linarith [div_lt_div_of_pos_right h2 hL_norm_pos,
      show ‖L‖ * δ₁ / ‖L‖ = δ₁ from by field_simp]
  have h2ε₁_over_L_lt_δ₀ : 2 * ε₁ / ‖L‖ < δ₀ :=
    lt_of_lt_of_le h2ε₁_over_L_lt_δ₁ hδ₁_le_δ₀
  have h_lower_bound :
      ∀ t, |t - t₀| < δ₁ →
      ‖γ t - γ t₀‖ ≥ ‖L‖ / 2 * |t - t₀| := by
    intro t ht_lt
    have ht_lt_δ₀ : |t - t₀| < δ₀ :=
      lt_of_lt_of_le ht_lt hδ₁_le_δ₀
    have ht_lt_L_over_2K : |t - t₀| < ‖L‖ / (2 * K₀) :=
      lt_of_lt_of_le ht_lt hδ₁_le_L_over_2K
    have h_approx := h_quad t ht_lt_δ₀
    have h_smul_norm :
        ‖(t - t₀) • L‖ = |t - t₀| * ‖L‖ :=
      norm_smul (t - t₀) L
    have h_rev_tri :=
      norm_sub_norm_le (γ t - γ t₀) ((t - t₀) • L)
    have h1 :
        ‖γ t - γ t₀‖ ≥
        ‖(t - t₀) • L‖ -
        ‖γ t - γ t₀ - (t - t₀) • L‖ := by
      have := abs_norm_sub_norm_le
        (γ t - γ t₀) ((t - t₀) • L)
      linarith [abs_le.mp this]
    have h2 :
        ‖γ t - γ t₀‖ ≥
        |t - t₀| * ‖L‖ - K₀ * |t - t₀|^2 := by
      calc ‖γ t - γ t₀‖
          ≥ ‖(t - t₀) • L‖ -
            ‖γ t - γ t₀ - (t - t₀) • L‖ := h1
        _ = |t - t₀| * ‖L‖ -
            ‖γ t - γ t₀ - (t - t₀) • L‖ := by
            rw [h_smul_norm]
        _ ≥ |t - t₀| * ‖L‖ -
            K₀ * |t - t₀|^2 := by
            linarith [h_approx]
    have h3 :
        |t - t₀| * ‖L‖ - K₀ * |t - t₀|^2 =
        |t - t₀| * (‖L‖ - K₀ * |t - t₀|) := by ring
    rw [h3] at h2
    have h4 : K₀ * |t - t₀| < ‖L‖ / 2 := by
      have h4a : |t - t₀| < ‖L‖ / (2 * K₀) :=
        ht_lt_L_over_2K
      have h4b :
          K₀ * |t - t₀| < K₀ * (‖L‖ / (2 * K₀)) :=
        mul_lt_mul_of_pos_left h4a hK₀_pos
      have h4c : K₀ * (‖L‖ / (2 * K₀)) = ‖L‖ / 2 :=
        by field_simp
      linarith
    have h5 : ‖L‖ - K₀ * |t - t₀| > ‖L‖ / 2 := by
      linarith
    have h6 :
        |t - t₀| * (‖L‖ - K₀ * |t - t₀|) ≥
        |t - t₀| * (‖L‖ / 2) := by
      apply mul_le_mul_of_nonneg_left
        (le_of_lt h5) (abs_nonneg _)
    calc ‖γ t - γ t₀‖
        ≥ |t - t₀| * (‖L‖ - K₀ * |t - t₀|) := h2
      _ ≥ |t - t₀| * (‖L‖ / 2) := h6
      _ = ‖L‖ / 2 * |t - t₀| := by ring
  have h_localize_γAnn :
      ∀ t, t ∈ γAnn → |t - t₀| < δ₁ := by
    intro t ⟨_, ht_local, _, _⟩
    exact ht_local
  have h_localize_tAnnLin :
      ∀ t, t ∈ tAnnLin → |t - t₀| < δ₁ := by
    intro t ⟨_, ht_local, _, _⟩
    exact ht_local
  let R_max := 2 * ε₁ / ‖L‖
  let Δ := K₀ * R_max^2
  have hR_max_pos : 0 < R_max := by
    simp only [R_max]; positivity
  have hΔ_nonneg : 0 ≤ Δ :=
    mul_nonneg hK₀_nonneg (sq_nonneg _)
  let shell₁_lo := (ε₁ - Δ) / ‖L‖
  let shell₁_hi := (ε₁ + Δ) / ‖L‖
  let shell₂_lo := (ε₂ - Δ) / ‖L‖
  let shell₂_hi := (ε₂ + Δ) / ‖L‖
  let g : ℝ → ℝ := fun t => ‖γ t - γ t₀‖
  let x : ℝ → ℝ := fun t => ‖L‖ * |t - t₀|
  let e : ℝ → ℝ := fun t => K₀ * |t - t₀|^2
  let shell₁ := {t : ℝ | |x t - ε₁| ≤ Δ}
  let shell₂ := {t : ℝ | |x t - ε₂| ≤ Δ}
  have h_subset :
      symmDiff γAnn tAnnLin ⊆ shell₁ ∪ shell₂ := by
    intro t ht
    rw [Set.mem_symmDiff] at ht
    have hxor : Xor' (t ∈ γAnn) (t ∈ tAnnLin) := ht
    have ht_localized : |t - t₀| < δ₁ := by
      rcases hxor with ⟨ht_γAnn, _⟩ | ⟨ht_tAnn, _⟩
      · exact h_localize_γAnn t ht_γAnn
      · exact h_localize_tAnnLin t ht_tAnn
    have ht_lt_δ₀ : |t - t₀| < δ₀ :=
      lt_of_lt_of_le ht_localized (min_le_left _ _)
    have h_gx_bound : |g t - x t| ≤ e t := by
      convert norm_linear_approx_bound h_quad ht_lt_δ₀ using 2
    have ht_Icc : t ∈ Set.Icc a b := by
      rcases hxor with
        ⟨⟨ht_Icc, _, _, _⟩, _⟩ |
        ⟨⟨ht_Icc, _, _, _⟩, _⟩ <;>
        exact ht_Icc
    have hxor' :
        Xor' (ε₂ < g t ∧ g t ≤ ε₁)
             (ε₂ < x t ∧ x t ≤ ε₁) := by
      rcases hxor with
        ⟨⟨_, _, hγ_lo, hγ_hi⟩, ht_not_tAnn⟩ |
        ⟨⟨_, _, ht_lo, ht_hi⟩, ht_not_γAnn⟩
      · left; constructor
        · exact ⟨hγ_lo, hγ_hi⟩
        · intro ⟨ht_lo', ht_hi'⟩
          exact ht_not_tAnn
            ⟨ht_Icc, ht_localized, ht_lo', ht_hi'⟩
      · right; constructor
        · exact ⟨ht_lo, ht_hi⟩
        · intro ⟨hγ_lo', hγ_hi'⟩
          exact ht_not_γAnn
            ⟨ht_Icc, ht_localized, hγ_lo', hγ_hi'⟩
    have hR_bound : |t - t₀| ≤ R_max := by
      rcases hxor with ⟨ht_γAnn, _⟩ | ⟨ht_tAnn, _⟩
      · have h_lb := h_lower_bound t ht_localized
        have ⟨_, _, _, ht_upper⟩ := ht_γAnn
        have h1 : |t - t₀| * (‖L‖ / 2) ≤ ε₁ := by
          rw [mul_comm]; exact le_trans h_lb ht_upper
        have hL2_pos : 0 < ‖L‖ / 2 := by linarith
        have h2 : |t - t₀| ≤ ε₁ / (‖L‖ / 2) := (le_div_iff₀ hL2_pos).mpr h1
        simp only [R_max, show ε₁ / (‖L‖ / 2) = 2 * ε₁ / ‖L‖ from by field_simp] at h2 ⊢
        exact h2
      · have ⟨_, _, _, ht_upper⟩ := ht_tAnn
        have h1 : ‖L‖ * |t - t₀| ≤ ε₁ := ht_upper
        have h1' :
            |t - t₀| * ‖L‖ ≤ ε₁ := by
          rw [mul_comm]; exact h1
        have hL_nonneg : 0 ≤ ‖L‖ :=
          le_of_lt hL_norm_pos
        calc |t - t₀|
            ≤ ε₁ / ‖L‖ := by
              rw [le_div_iff₀ hL_norm_pos]; exact h1'
          _ ≤ 2 * ε₁ / ‖L‖ := by
              apply div_le_div_of_nonneg_right _
                hL_nonneg; linarith
    have he_le_Δ : e t ≤ Δ := by
      simp only [e, Δ, R_max]
      apply mul_le_mul_of_nonneg_left _ hK₀_nonneg
      exact sq_le_sq'
        (by linarith [abs_nonneg (t - t₀)]) hR_bound
    rcases symmDiff_subset_boundaryLayers h_gx_bound hxor' with h_near₂ | h_near₁
    · right
      change |x t - ε₂| ≤ Δ
      exact le_trans h_near₂ he_le_Δ
    · left
      change |x t - ε₁| ≤ Δ
      exact le_trans h_near₁ he_le_Δ
  have h_shell₁_eq : shell₁ = {t : ℝ | |‖L‖ * |t - t₀| - ε₁| ≤ Δ} := by
    simp only [shell₁, x]
  have h_shell₂_eq : shell₂ = {t : ℝ | |‖L‖ * |t - t₀| - ε₂| ≤ Δ} := by
    simp only [shell₂, x]
  have h_shell₁_vol : volume shell₁ ≤ ENNReal.ofReal (4 * Δ / ‖L‖) := by
    rw [h_shell₁_eq]; exact shell_vol_le hL_norm_pos hΔ_nonneg hε₁_pos
  have h_shell₂_vol : volume shell₂ ≤ ENNReal.ofReal (4 * Δ / ‖L‖) := by
    rw [h_shell₂_eq]; exact shell_vol_le hL_norm_pos hΔ_nonneg hε₂_pos
  have h_total_vol :
      volume (shell₁ ∪ shell₂) ≤
      ENNReal.ofReal (8 * Δ / ‖L‖) :=
    calc volume (shell₁ ∪ shell₂)
        ≤ volume shell₁ + volume shell₂ :=
          MeasureTheory.measure_union_le _ _
      _ ≤ ENNReal.ofReal (4 * Δ / ‖L‖) +
          ENNReal.ofReal (4 * Δ / ‖L‖) :=
          add_le_add h_shell₁_vol h_shell₂_vol
      _ = ENNReal.ofReal
            (4 * Δ / ‖L‖ + 4 * Δ / ‖L‖) := by
          rw [← ENNReal.ofReal_add] <;> positivity
      _ = ENNReal.ofReal (8 * Δ / ‖L‖) := by ring_nf
  calc volume (symmDiff γAnn tAnnLin)
      ≤ volume (shell₁ ∪ shell₂) :=
        MeasureTheory.measure_mono h_subset
    _ ≤ ENNReal.ofReal (8 * Δ / ‖L‖) := h_total_vol
    _ = ENNReal.ofReal (32 * K₀ * ε₁^2 / ‖L‖^3) := by
        congr 1; simp only [Δ, R_max]; field_simp; ring

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
  let J_lin := ∫ t in a..b,
    if ε₂ < ‖L‖ * |t - t₀| ∧
      ‖L‖ * |t - t₀| ≤ ε₁
    then (↑(t - t₀) : ℂ)⁻¹ else 0
  have hJ_lin_zero : J_lin = 0 := by
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
    change (∫ t in a..b, φ t) = 0
    rw [h_split, hφ_zero_left, hφ_zero_right,
      hφ_zero_middle, hφ_eq_left, hφ_eq_right]
    simp only [zero_add, add_zero]
    exact singular_tAnnLin_cancel t₀ hL_pos
      ε₁ ε₂ hε₂_pos hε₂_le
  have h_diff_bound :
      ‖(∫ t in a..b,
        if ε₂ < ‖γ t - γ t₀‖ ∧
          ‖γ t - γ t₀‖ ≤ ε₁
        then (↑(t - t₀) : ℂ)⁻¹ else 0) -
        J_lin‖ ≤ Csing * ε₁ := by
    rw [hJ_lin_zero, sub_zero]
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
      intro t ht
      simp only [hd_def, hf_γ_def, hf_lin_def]
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
          lt_of_lt_of_le ht_loc
            (le_trans (min_le_right _ _)
              (min_le_right _ _))
        have hγ_up := h_upper t ht_pos ht_lt_δ_up
        have h_lo :
            ε₂ / (2 * ‖L‖) ≤ |t - t₀| :=
          le_of_lt (by
            rw [div_lt_iff₀
              (by positivity : (0:ℝ) < 2 * ‖L‖)]
            linarith)
        exact le_trans
          (singular_symmDiff_sup_bound
            (by positivity) h_lo)
          (by rw [hbound_def, one_div, inv_div])
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
          (by rw [hbound_def, one_div, inv_div])
      · simp [hγ, hlin]
        exact le_of_lt hbound_pos
    have hf_lin_meas : Measurable f_lin := by
      simp only [hf_lin_def]
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
    have hf_lin_bound :
        ∀ t : ℝ, ‖f_lin t‖ ≤ bound := by
      intro t; simp only [hf_lin_def]
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
          (by rw [hbound_def, one_div, inv_div])
      · simp only [hcond, ite_false, norm_zero]
        positivity
    have hf_lin_int :
        IntervalIntegrable f_lin
          MeasureTheory.volume a b := by
      rw [intervalIntegrable_iff]
      exact MeasureTheory.IntegrableOn.of_bound
        measure_Ioc_lt_top
        hf_lin_meas.aestronglyMeasurable.restrict
        bound
        (Filter.Eventually.of_forall
          (fun x => hf_lin_bound x))
    have hf_γ_eq :
        ∀ t, f_γ t = d t + f_lin t := by
      intro t; simp only [hd_def]; ring
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
      simp only [hf_γ'_def]
      apply Measurable.ite
      · apply MeasurableSet.inter
        · exact hh'_sm.measurable measurableSet_Ioi
        · exact hh'_sm.measurable measurableSet_Iic
      · exact (Complex.measurable_ofReal.comp
          (measurable_id.sub_const t₀)).inv
      · exact measurable_const
    have hf_γ_ae_eq :
        ∀ᵐ t ∂(MeasureTheory.volume.restrict
          (Set.Icc a b)),
        f_γ t = f_γ' t := by
      filter_upwards [hh'_ae] with t ht_eq
      simp only [hf_γ_def, hf_γ'_def, ht_eq]
    have hf_γ_aesm :
        AEStronglyMeasurable f_γ
          (MeasureTheory.volume.restrict
            (Set.Ioc a b)) :=
      (hf_γ'_meas.aestronglyMeasurable.congr
        (Filter.EventuallyEq.symm
          hf_γ_ae_eq)).mono_measure
        (MeasureTheory.Measure.restrict_mono
          Set.Ioc_subset_Icc_self le_rfl)
    have hd_int :
        IntervalIntegrable d
          MeasureTheory.volume a b := by
      rw [intervalIntegrable_iff,
        Set.uIoc_of_le hab.le]
      exact MeasureTheory.IntegrableOn.of_bound
        measure_Ioc_lt_top
        (hf_γ_aesm.sub
          hf_lin_meas.aestronglyMeasurable.restrict)
        bound
        ((MeasureTheory.ae_restrict_iff'
          measurableSet_Ioc).mpr
          (Filter.Eventually.of_forall
            (fun t ht =>
              hd_bound_on_Icc t
                (Set.Ioc_subset_Icc_self ht))))
    have hf_γ_eq_d_add_lin :
        (∫ t in a..b, f_γ t) =
        (∫ t in a..b, d t) + J_lin := by
      rw [show J_lin = ∫ t in a..b, f_lin t from rfl]
      rw [← intervalIntegral.integral_add
        hd_int hf_lin_int]
      exact intervalIntegral.integral_congr
        (fun t _ => hf_γ_eq t)
    rw [show (∫ t in a..b, f_γ t) =
          ∫ t in a..b, f_γ t from rfl,
      hf_γ_eq_d_add_lin, hJ_lin_zero, add_zero]
    rw [intervalIntegral.integral_of_le hab.le]
    set γAnn' := {t : ℝ |
      t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
      ε₂ < h' t ∧ h' t ≤ ε₁}
    set tAnnLin_loc := {t : ℝ |
      t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
      ε₂ < ‖L‖ * |t - t₀| ∧
      ‖L‖ * |t - t₀| ≤ ε₁}
    set S' := symmDiff γAnn' tAnnLin_loc with hS'_def
    have hγAnn'_meas : MeasurableSet γAnn' := by
      apply MeasurableSet.inter
      · exact measurableSet_Icc
      · apply MeasurableSet.inter
        · exact (isOpen_lt
            (continuous_abs.comp
              (continuous_id.sub continuous_const))
            continuous_const).measurableSet
        · apply MeasurableSet.inter
          · exact hh'_sm.measurable measurableSet_Ioi
          · exact hh'_sm.measurable measurableSet_Iic
    have htAnnLin_meas :
        MeasurableSet tAnnLin_loc := by
      apply MeasurableSet.inter
      · exact measurableSet_Icc
      · apply MeasurableSet.inter
        · exact (isOpen_lt
            (continuous_abs.comp
              (continuous_id.sub continuous_const))
            continuous_const).measurableSet
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
    have hS'_meas : MeasurableSet S' :=
      hγAnn'_meas.symmDiff htAnnLin_meas
    set d' : ℝ → ℂ := fun t => f_γ' t - f_lin t
      with hd'_def
    have hd_ae_eq :
        ∀ᵐ t ∂(MeasureTheory.volume.restrict
          (Set.Icc a b)),
        d t = d' t := by
      filter_upwards [hf_γ_ae_eq] with t ht_eq
      simp only [hd_def, hd'_def, ht_eq]
    have hd'_meas : Measurable d' :=
      hf_γ'_meas.sub hf_lin_meas
    have h_int_eq :
        (∫ t in Set.Ioc a b, d t ∂volume) =
        ∫ t in Set.Ioc a b, d' t ∂volume := by
      apply MeasureTheory.setIntegral_congr_ae
        measurableSet_Ioc
      filter_upwards
        [(MeasureTheory.ae_restrict_iff'
          measurableSet_Icc).mp hd_ae_eq]
        with t h_eq ht_Ioc
      exact h_eq (Set.Ioc_subset_Icc_self ht_Ioc)
    rw [h_int_eq]
    set g_comp : ℝ → ℝ :=
      S'.indicator (fun _ => bound) with hg_comp_def
    have hS'_finite : volume S' < ⊤ := by
      calc volume S'
          ≤ volume (Set.Icc a b) := by
            apply MeasureTheory.measure_mono
            intro t ht
            rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;>
              exact h.1
        _ < ⊤ := measure_Icc_lt_top
    have hg_int :
        IntervalIntegrable g_comp volume a b := by
      constructor <;>
        exact (MeasureTheory.integrableOn_const
          (hs := measure_Ioc_lt_top.ne)).indicator
          hS'_meas
    have h_pw_le :
        ∀ᵐ t ∂volume,
        t ∈ Set.Ioc a b → ‖d' t‖ ≤ g_comp t := by
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨{t | t ∈ Set.Icc a b → d t = d' t},
        ?_, ?_⟩
      · exact (MeasureTheory.ae_restrict_iff'
          measurableSet_Icc).mp hd_ae_eq
      · intro t ht ht_Ioc
        simp only [g_comp, hg_comp_def, S',
          Set.indicator]
        by_cases ht_S :
            t ∈ symmDiff γAnn' tAnnLin_loc
        · simp only [ht_S, ↓reduceIte]
          have ht_Icc :=
            Set.Ioc_subset_Icc_self ht_Ioc
          rw [← ht ht_Icc]
          exact hd_bound_on_Icc t ht_Icc
        · simp only [ht_S, ↓reduceIte]
          have ht_Icc :=
            Set.Ioc_subset_Icc_self ht_Ioc
          suffices h_dt_zero : d t = 0 by
            have hd_eq : d' t = d t :=
              (ht ht_Icc).symm
            rw [hd_eq, h_dt_zero, norm_zero]
          simp only [hd_def, hf_γ_def, hf_lin_def]
          by_cases hδ : |t - t₀| < δ₀'
          · have h_agree :
                (ε₂ < ‖γ t - γ t₀‖ ∧
                  ‖γ t - γ t₀‖ ≤ ε₁) ↔
                (ε₂ < ‖L‖ * |t - t₀| ∧
                  ‖L‖ * |t - t₀| ≤ ε₁) := by
              have hd_eq_at := ht ht_Icc
              have hfγ_eq : f_γ t = f_γ' t := by
                have hd_t : d t = f_γ t - f_lin t :=
                  rfl
                have hd'_t :
                    d' t = f_γ' t - f_lin t := rfl
                have h := hd_eq_at
                rw [hd_t, hd'_t] at h
                have := congr_arg (· + f_lin t) h
                simp [sub_add_cancel] at this
                exact this
              have h_not_sd := ht_S
              rw [Set.mem_symmDiff] at h_not_sd
              push_neg at h_not_sd
              have h'_iff_lin :
                  (ε₂ < h' t ∧ h' t ≤ ε₁) ↔
                  (ε₂ < ‖L‖ * |t - t₀| ∧
                    ‖L‖ * |t - t₀| ≤ ε₁) := by
                constructor
                · intro ⟨h1, h2⟩
                  have hmem : t ∈ γAnn' :=
                    ⟨ht_Icc, hδ, h1, h2⟩
                  exact (h_not_sd.1 hmem).2.2
                · intro ⟨h1, h2⟩
                  have hmem : t ∈ tAnnLin_loc :=
                    ⟨ht_Icc, hδ, h1, h2⟩
                  exact (h_not_sd.2 hmem).2.2
              by_cases ht_eq : t = t₀
              · subst ht_eq
                simp only [sub_self, norm_zero, abs_zero, mul_zero]
              · have hinv_ne :
                    (↑(t - t₀) : ℂ)⁻¹ ≠ 0 :=
                  inv_ne_zero
                    (Complex.ofReal_ne_zero.mpr
                      (sub_ne_zero.mpr ht_eq))
                constructor
                · intro hγ_cond
                  have : f_γ t =
                      (↑(t - t₀) : ℂ)⁻¹ :=
                    if_pos hγ_cond
                  rw [this] at hfγ_eq
                  by_contra h_neg
                  have : f_γ' t = 0 := by
                    simp only [hf_γ'_def]
                    exact if_neg
                      (mt h'_iff_lin.mp h_neg)
                  rw [this] at hfγ_eq
                  exact hinv_ne hfγ_eq
                · intro hlin_cond
                  have hh'_cond :=
                    h'_iff_lin.mpr hlin_cond
                  have : f_γ' t =
                      (↑(t - t₀) : ℂ)⁻¹ :=
                    if_pos hh'_cond
                  rw [this] at hfγ_eq
                  by_contra h_neg
                  have : f_γ t = 0 := if_neg h_neg
                  rw [this] at hfγ_eq
                  exact hinv_ne hfγ_eq.symm
            by_cases hcond :
                ε₂ < ‖γ t - γ t₀‖ ∧
                ‖γ t - γ t₀‖ ≤ ε₁
            · simp [hcond, h_agree.mp hcond, sub_self]
            · simp [hcond, mt h_agree.mpr hcond]
          · have hγ_fail :
                ¬(ε₂ < ‖γ t - γ t₀‖ ∧
                  ‖γ t - γ t₀‖ ≤ ε₁) := by
              intro ⟨_, h_up⟩
              have := h_localize t ht_Icc h_up
              have : |t - t₀| < δ₀' :=
                lt_of_lt_of_le this
                  (min_le_left _ _)
              linarith [not_lt.mp hδ]
            have hlin_fail :
                ¬(ε₂ < ‖L‖ * |t - t₀| ∧
                  ‖L‖ * |t - t₀| ≤ ε₁) := by
              intro ⟨_, h_le⟩
              have :
                  ‖L‖ * |t - t₀| ≥ ‖L‖ * δ₀' := by
                apply mul_le_mul_of_nonneg_left
                  (not_lt.mp hδ) (le_of_lt hL_pos)
              linarith
            simp [hγ_fail, hlin_fail]
    have h_pw_le_restrict :
        ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        ‖d' t‖ ≤ g_comp t := by
      rw [MeasureTheory.ae_restrict_iff'
        measurableSet_Ioc]
      exact h_pw_le
    have hg_int_Ioc :
        MeasureTheory.Integrable g_comp
          (volume.restrict (Set.Ioc a b)) :=
      hg_int.1
    have hS'_vol_bound :
        volume S' ≤
        ENNReal.ofReal
          (Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3) := by
      set γAnn := {t : ℝ |
        t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
        ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁}
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
          volume (symmDiff γAnn' γAnn) = 0 := by
        exact le_antisymm
          (le_of_le_of_eq
            (MeasureTheory.measure_mono h_sd_subset)
            h_null_set)
          (zero_le _)
      calc volume S'
          = volume (symmDiff γAnn' tAnnLin_loc) := rfl
        _ ≤ volume (symmDiff γAnn' γAnn) +
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
    have hIoc_finite :
        volume (Set.Ioc a b) < ⊤ :=
      measure_Ioc_lt_top
    calc ‖∫ t in Set.Ioc a b, d' t‖
        ≤ ∫ t in Set.Ioc a b, g_comp t :=
          MeasureTheory.norm_integral_le_of_norm_le
            hg_int_Ioc h_pw_le_restrict
      _ = ∫ t in (Set.Ioc a b) ∩ S',
            (fun _ => bound) t := by
          rw [MeasureTheory.setIntegral_indicator
            hS'_meas]
      _ = volume.real ((Set.Ioc a b) ∩ S') *
          bound := by
          rw [MeasureTheory.setIntegral_const,
            smul_eq_mul]
      _ ≤ volume.real S' * bound := by
          apply mul_le_mul_of_nonneg_right _
            (le_of_lt hbound_pos)
          exact measureReal_mono
            Set.inter_subset_right hS'_finite.ne
      _ ≤ (Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3) * bound := by
          apply mul_le_mul_of_nonneg_right _
            (le_of_lt hbound_pos)
          unfold MeasureTheory.Measure.real
          exact ENNReal.toReal_le_of_le_ofReal
            (by positivity) hS'_vol_bound
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
  calc ‖∫ t in a..b,
      if ε₂ < ‖γ t - γ t₀‖ ∧
        ‖γ t - γ t₀‖ ≤ ε₁
      then (↑(t - t₀) : ℂ)⁻¹ else 0‖
      = ‖(∫ t in a..b,
          if ε₂ < ‖γ t - γ t₀‖ ∧
            ‖γ t - γ t₀‖ ≤ ε₁
          then (↑(t - t₀) : ℂ)⁻¹ else 0) -
          J_lin‖ := by rw [hJ_lin_zero, sub_zero]
    _ ≤ Csing * ε₁ := h_diff_bound


end
