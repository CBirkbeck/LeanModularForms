/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.PVInfrastructure.GammaAnalysis
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.PVInfrastructure.RemainderAnalysis

/-!
# PV Infrastructure: Step Bounds

Dyadic step bounds and subsequence selection for principal value
convergence. These combine the gamma analysis (lower/upper bounds)
with the remainder analysis (C² bounded remainder) to show that
cutoff integrals converge along dyadic subsequences.

## Main Results

* `remainder_integral_O_eps` — O(ε) step bound from bounded
    remainder
* `integral_inv_symm` — symmetric cancellation of 1/(t-t₀)
* `remainder_annulus_bound` — integral of remainder over annulus
    is O(log ratio)
* `exists_summable_subseq` — summable subsequence construction
* `cutoff_integrand_intervalIntegrable` — integrability of cutoff
* `cutoff_diff_eq_annulus_integral` — difference equals annulus
    integral
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- O(ε) step bound from bounded remainder. -/
lemma remainder_integral_O_eps {r : ℝ → ℂ} {t₀ ε C : ℝ} (hε_pos : 0 < ε) (_hC_pos : 0 < C)
    (hr_bound : ∀ t, 0 < |t - t₀| → |t - t₀| ≤ 2 * ε → ‖r t‖ ≤ C) :
    ‖∫ t in (t₀ - 2 * ε)..(t₀ - ε), r t‖ + ‖∫ t in (t₀ + ε)..(t₀ + 2 * ε), r t‖ ≤
      2 * C * ε := by
  have h_left : ‖∫ t in (t₀ - 2 * ε)..(t₀ - ε), r t‖ ≤ C * ε := by
    have hb : ∀ t ∈ Set.uIoc (t₀ - 2 * ε) (t₀ - ε), ‖r t‖ ≤ C := fun t ht => by
      obtain ⟨h1, h2⟩ :=
        (Set.uIoc_of_le (by linarith : t₀ - 2 * ε ≤ t₀ - ε) ▸ ht : t ∈ Set.Ioc _ _)
      refine hr_bound t (abs_pos.mpr (by linarith)) ?_
      rw [abs_of_neg (by linarith : t - t₀ < 0)]
      linarith
    calc ‖∫ t in (t₀ - 2 * ε)..(t₀ - ε), r t‖
        ≤ C * |(t₀ - ε) - (t₀ - 2 * ε)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ = C * ε := by
          rw [show (t₀ - ε) - (t₀ - 2 * ε) = ε by ring, abs_of_pos hε_pos]
  have h_right : ‖∫ t in (t₀ + ε)..(t₀ + 2 * ε), r t‖ ≤ C * ε := by
    have hb : ∀ t ∈ Set.uIoc (t₀ + ε) (t₀ + 2 * ε), ‖r t‖ ≤ C := fun t ht => by
      obtain ⟨h1, h2⟩ :=
        (Set.uIoc_of_le (by linarith : t₀ + ε ≤ t₀ + 2 * ε) ▸ ht : t ∈ Set.Ioc _ _)
      refine hr_bound t (abs_pos.mpr (by linarith)) ?_
      rw [abs_of_pos (by linarith : t - t₀ > 0)]
      linarith
    calc ‖∫ t in (t₀ + ε)..(t₀ + 2 * ε), r t‖
        ≤ C * |(t₀ + 2 * ε) - (t₀ + ε)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ = C * ε := by
          rw [show (t₀ + 2 * ε) - (t₀ + ε) = ε by ring, abs_of_pos hε_pos]
  linarith

/-- Symmetric cancellation of 1/(t-t₀). -/
lemma integral_inv_symm (t₀ ε₁ ε₂ : ℝ) (_hε₁ : 0 < ε₁) (_hε₂ : 0 < ε₂) (_hε₁₂ : ε₁ ≤ ε₂) :
    (∫ t in (t₀ - ε₂)..(t₀ - ε₁), (↑(t - t₀) : ℂ)⁻¹) +
      (∫ t in (t₀ + ε₁)..(t₀ + ε₂), (↑(t - t₀) : ℂ)⁻¹) = 0 := by
  have h_odd : ∀ u : ℝ, (↑(-u) : ℂ)⁻¹ = -((↑u : ℂ)⁻¹) := by
    intro u
    simp only [ofReal_neg, neg_inv]
  have h_reflect : ∫ t in (t₀ - ε₂)..(t₀ - ε₁), (↑(t - t₀) : ℂ)⁻¹ =
      -(∫ t in (t₀ + ε₁)..(t₀ + ε₂), (↑(t - t₀) : ℂ)⁻¹) := by
    have h1 := intervalIntegral.integral_comp_sub_left
      (f := fun x => (↑(x - t₀) : ℂ)⁻¹) (d := 2 * t₀) (a := t₀ + ε₁) (b := t₀ + ε₂)
    simp only [show 2 * t₀ - (t₀ + ε₂) = t₀ - ε₂ by ring,
      show 2 * t₀ - (t₀ + ε₁) = t₀ - ε₁ by ring,
      show ∀ x, 2 * t₀ - x - t₀ = -(x - t₀) from fun x => by ring, h_odd] at h1
    rw [intervalIntegral.integral_neg] at h1
    exact h1.symm
  rw [h_reflect, neg_add_cancel]

/-- Remainder annulus bound: O(log ratio). -/
lemma remainder_annulus_bound {r : ℝ → ℂ} {t₀ c₁ c₂ η : ℝ} (hc₁_pos : 0 < c₁)
    (hc₂_pos : 0 < c₂) (hc₁₂ : c₁ < c₂) (_hη_pos : 0 < η)
    (hr_bound : ∀ t, c₁ < |t - t₀| → |t - t₀| < c₂ → ‖r t‖ ≤ η / |t - t₀|) :
    ‖∫ t in (t₀ - c₂)..(t₀ - c₁), r t‖ + ‖∫ t in (t₀ + c₁)..(t₀ + c₂), r t‖ ≤
      2 * η * Real.log (c₂ / c₁) := by
  have h_left : ‖∫ t in (t₀ - c₂)..(t₀ - c₁), r t‖ ≤ η * Real.log (c₂ / c₁) := by
    have hab : t₀ - c₂ ≤ t₀ - c₁ := by linarith
    let g : ℝ → ℝ := fun t => η / (t₀ - t)
    have h_norm_le : ∀ t ∈ Set.Ioo (t₀ - c₂) (t₀ - c₁), ‖r t‖ ≤ g t := by
      intro t ⟨ht_lo, ht_hi⟩
      have h_t_minus : t - t₀ < 0 := by linarith
      have h_abs : |t - t₀| = t₀ - t := by
        rw [abs_of_neg h_t_minus]
        ring
      have h_abs_lo : c₁ < |t - t₀| := by
        rw [h_abs]
        linarith
      have h_abs_hi : |t - t₀| < c₂ := by
        rw [h_abs]
        linarith
      have h_bound := hr_bound t h_abs_lo h_abs_hi
      simp only [g]
      rwa [h_abs] at h_bound
    have h_norm_le_ae : ∀ᵐ t, t ∈ Set.Ioc (t₀ - c₂) (t₀ - c₁) → ‖r t‖ ≤ g t := by
      have h_meas_zero : MeasureTheory.volume {t₀ - c₁} = 0 := Real.volume_singleton
      have h_compl : ∀ᵐ t, t ∉ ({t₀ - c₁} : Set ℝ) := by
        rw [MeasureTheory.ae_iff]
        convert h_meas_zero using 2
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, not_not]
      filter_upwards [h_compl] with t ht_ne ht_mem
      have h_in_open : t ∈ Set.Ioo (t₀ - c₂) (t₀ - c₁) := by
        simp only [Set.mem_Ioo, Set.mem_Ioc] at ht_mem ⊢
        refine ⟨ht_mem.1, ?_⟩
        simp only [Set.mem_singleton_iff] at ht_ne
        exact lt_of_le_of_ne ht_mem.2 ht_ne
      exact h_norm_le t h_in_open
    have h_g_integrable :
        IntervalIntegrable g MeasureTheory.volume (t₀ - c₂) (t₀ - c₁) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const
      · exact continuousOn_const.sub continuousOn_id
      · intro t ht
        simp only [Set.uIcc_of_le hab, Set.mem_Icc] at ht
        linarith
    have h_bound :=
      intervalIntegral.norm_integral_le_of_norm_le hab h_norm_le_ae h_g_integrable
    have h_g_eq : ∫ t in (t₀ - c₂)..(t₀ - c₁), g t = η * Real.log (c₂ / c₁) := by
      simp only [g]
      have h_subst : ∫ t in (t₀ - c₂)..(t₀ - c₁), η / (t₀ - t) = ∫ u in c₁..c₂, η / u := by
        simpa only [sub_sub_cancel] using intervalIntegral.integral_comp_sub_left
          (fun u => η / u) t₀ (a := t₀ - c₂) (b := t₀ - c₁)
      rw [h_subst]
      have h_factor : ∫ u in c₁..c₂, η / u = η * ∫ u in c₁..c₂, u⁻¹ := by
        rw [← intervalIntegral.integral_const_mul]
        simp only [div_eq_mul_inv]
      rw [h_factor, integral_inv_of_pos hc₁_pos hc₂_pos]
    rw [h_g_eq] at h_bound
    exact h_bound
  have h_right : ‖∫ t in (t₀ + c₁)..(t₀ + c₂), r t‖ ≤ η * Real.log (c₂ / c₁) := by
    have hab : t₀ + c₁ ≤ t₀ + c₂ := by linarith
    let g : ℝ → ℝ := fun t => η / (t - t₀)
    have h_norm_le : ∀ t ∈ Set.Ioo (t₀ + c₁) (t₀ + c₂), ‖r t‖ ≤ g t := by
      intro t ⟨ht_lo, ht_hi⟩
      have h_t_minus : t - t₀ > 0 := by linarith
      have h_abs : |t - t₀| = t - t₀ := abs_of_pos h_t_minus
      have h_abs_lo : c₁ < |t - t₀| := by
        rw [h_abs]
        linarith
      have h_abs_hi : |t - t₀| < c₂ := by
        rw [h_abs]
        linarith
      have h_bound := hr_bound t h_abs_lo h_abs_hi
      simp only [g]
      rwa [h_abs] at h_bound
    have h_norm_le_ae : ∀ᵐ t, t ∈ Set.Ioc (t₀ + c₁) (t₀ + c₂) → ‖r t‖ ≤ g t := by
      have h_meas_zero : MeasureTheory.volume {t₀ + c₂} = 0 := Real.volume_singleton
      have h_compl : ∀ᵐ t, t ∉ ({t₀ + c₂} : Set ℝ) := by
        rw [MeasureTheory.ae_iff]
        convert h_meas_zero using 2
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, not_not]
      filter_upwards [h_compl] with t ht_ne ht_mem
      have h_in_open : t ∈ Set.Ioo (t₀ + c₁) (t₀ + c₂) := by
        simp only [Set.mem_Ioo, Set.mem_Ioc] at ht_mem ⊢
        refine ⟨ht_mem.1, ?_⟩
        simp only [Set.mem_singleton_iff] at ht_ne
        exact lt_of_le_of_ne ht_mem.2 ht_ne
      exact h_norm_le t h_in_open
    have h_g_integrable :
        IntervalIntegrable g MeasureTheory.volume (t₀ + c₁) (t₀ + c₂) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const
      · exact continuousOn_id.sub continuousOn_const
      · intro t ht
        simp only [Set.uIcc_of_le hab, Set.mem_Icc] at ht
        linarith
    have h_bound :=
      intervalIntegral.norm_integral_le_of_norm_le hab h_norm_le_ae h_g_integrable
    have h_g_eq : ∫ t in (t₀ + c₁)..(t₀ + c₂), g t = η * Real.log (c₂ / c₁) := by
      simp only [g]
      have h_subst : ∫ t in (t₀ + c₁)..(t₀ + c₂), η / (t - t₀) = ∫ u in c₁..c₂, η / u := by
        simpa only [add_sub_cancel_left] using intervalIntegral.integral_comp_sub_right
          (fun u => η / u) t₀ (a := t₀ + c₁) (b := t₀ + c₂)
      rw [h_subst]
      have h_factor : ∫ u in c₁..c₂, η / u = η * ∫ u in c₁..c₂, u⁻¹ := by
        rw [← intervalIntegral.integral_const_mul]
        simp only [div_eq_mul_inv]
      rw [h_factor, integral_inv_of_pos hc₁_pos hc₂_pos]
    rw [h_g_eq] at h_bound
    exact h_bound
  calc ‖∫ t in (t₀ - c₂)..(t₀ - c₁), r t‖ + ‖∫ t in (t₀ + c₁)..(t₀ + c₂), r t‖
      ≤ η * Real.log (c₂ / c₁) + η * Real.log (c₂ / c₁) := add_le_add h_left h_right
    _ = 2 * η * Real.log (c₂ / c₁) := by ring

/-- Scale-dependent η from asymptotic control. -/
lemma exists_eta_delta {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ t, 0 < |t - t₀| → |t - t₀| < δ →
      ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ η / |t - t₀| :=
  integrand_asymptotic γ t₀
    (integrand_times_t_tendsto_one γ t₀ L hL hγ_hasderiv hγ_cont_deriv) η hη

/-- Dyadic step [ε/2, ε] contributes ≤ 2η*log(2). -/
lemma step_bound_with_eta {r : ℝ → ℂ} {t₀ ε η : ℝ} (hε_pos : 0 < ε) (hη_pos : 0 < η)
    (hr_bound : ∀ t, 0 < |t - t₀| → |t - t₀| ≤ ε → ‖r t‖ ≤ η / |t - t₀|) :
    ‖∫ t in (t₀ - ε)..(t₀ - ε / 2), r t‖ + ‖∫ t in (t₀ + ε / 2)..(t₀ + ε), r t‖ ≤
      2 * η * Real.log 2 := by
  calc ‖∫ t in (t₀ - ε)..(t₀ - ε / 2), r t‖ + ‖∫ t in (t₀ + ε / 2)..(t₀ + ε), r t‖
      ≤ 2 * η * Real.log (ε / (ε / 2)) :=
        remainder_annulus_bound (by linarith) hε_pos (by linarith) hη_pos
          (fun t ht_lo ht_hi => hr_bound t (by linarith) ht_hi.le)
    _ = 2 * η * Real.log 2 := by rw [show ε / (ε / 2) = 2 by field_simp]

/-- Error bound extends to smaller scales. -/
lemma error_at_smaller_scale {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀) :
    ∀ η' > 0, ∃ δ > 0, ∀ ε, 0 < ε → ε < δ →
      (∀ t, 0 < |t - t₀| → |t - t₀| ≤ ε →
        ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ η' / |t - t₀|) := by
  intro η' hη'
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := exists_eta_delta hL hγ_hasderiv hγ_cont_deriv η' hη'
  refine ⟨δ, hδ_pos, fun ε _hε_pos hε_lt t ht_pos ht_le => ?_⟩
  exact hδ_bound t ht_pos (ht_le.trans_lt hε_lt)

/-- Cutoff integral I(ε). -/
abbrev cutoffIntegral (γ : ℝ → ℂ) (a b t₀ ε : ℝ) : ℂ :=
  ∫ t in a..b, if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0

/-- δ giving error bound (1/2)^n at scale ε < δ. -/
lemma exists_delta_for_error_bound {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (n : ℕ) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ →
      (∀ t, 0 < |t - t₀| → |t - t₀| ≤ ε →
        ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ (1 / 2) ^ n / |t - t₀|) :=
  error_at_smaller_scale hL hγ_hasderiv hγ_cont_deriv ((1 / 2) ^ n) (by positivity)

def summableSubseqAux {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) : ℕ → ℝ :=
  let δ := fun n => (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv n).choose
  fun n => Nat.rec (min δ₀ (δ 0) / 2) (fun m ε_m => min (ε_m / 2) (δ (m + 1)) / 2) n

lemma summableSubseqAux_zero {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) :
    summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ 0 =
      min δ₀ ((exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv 0).choose) / 2 :=
  rfl

lemma summableSubseqAux_succ {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (n : ℕ) :
    let ε := summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀
    let δ := fun m => (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv m).choose
    ε (n + 1) = min (ε n / 2) (δ (n + 1)) / 2 := rfl

lemma summableSubseqAux_pos {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (n : ℕ) :
    0 < summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ n := by
  let ε := summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀
  let δ := fun m => (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv m).choose
  have hδ_pos : ∀ m, 0 < δ m := fun m =>
    (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv m).choose_spec.1
  induction n with
  | zero =>
    simp only [summableSubseqAux_zero]
    have h_min_pos : 0 < min δ₀ (δ 0) := lt_min hδ₀_pos (hδ_pos 0)
    positivity
  | succ m ih =>
    simp only [summableSubseqAux_succ]
    have h_min_pos : 0 < min (ε m / 2) (δ (m + 1)) :=
      lt_min (by linarith) (hδ_pos (m + 1))
    positivity

lemma summableSubseqAux_halving {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (n : ℕ) :
    summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ (n + 1) ≤
      summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ n / 2 := by
  let ε := summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀
  simp only [summableSubseqAux_succ]
  have h_min_le :
      min (ε n / 2)
        ((exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv (n + 1)).choose) / 2 ≤
        (ε n / 2) / 2 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 2)
  rw [show (ε n / 2) / 2 = ε n / 4 by ring] at h_min_le
  have hε_pos := summableSubseqAux_pos hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n
  linarith

lemma summableSubseqAux_lt_delta {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (_hδ₀_pos : 0 < δ₀) (n : ℕ) :
    let δ := fun m => (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv m).choose
    summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ n < δ n := by
  intro δ
  let ε := summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀
  have hδ_pos : ∀ m, 0 < δ m := fun m =>
    (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv m).choose_spec.1
  induction n with
  | zero =>
    simp only [summableSubseqAux_zero]
    exact (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num : (0 : ℝ) < 2).le).trans_lt
      (half_lt_self (hδ_pos 0))
  | succ m _ =>
    simp only [summableSubseqAux_succ]
    exact (div_le_div_of_nonneg_right (min_le_right _ _)
      (by norm_num : (0 : ℝ) < 2).le).trans_lt (half_lt_self (hδ_pos (m + 1)))

lemma summableSubseqAux_error_bound {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (n : ℕ) :
    let ε_n := summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ n
    ∀ t, 0 < |t - t₀| → |t - t₀| ≤ ε_n →
      ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ (1 / 2) ^ n / |t - t₀| := by
  intro ε_n t ht_pos ht_le
  have hδ_bound := fun m =>
    (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv m).choose_spec.2
  have hε_pos := summableSubseqAux_pos hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n
  have hε_lt_δ := summableSubseqAux_lt_delta hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n
  exact hδ_bound n ε_n hε_pos hε_lt_δ t ht_pos ht_le

lemma exists_summable_subseq {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ (∀ n, ε (n + 1) ≤ ε n / 2) ∧
      (∀ n, ∀ t, 0 < |t - t₀| → |t - t₀| ≤ ε n →
        ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ (1 / 2) ^ n / |t - t₀|) := by
  refine ⟨summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀, ?_, ?_, ?_⟩
  · exact fun n => summableSubseqAux_pos hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n
  · exact fun n => summableSubseqAux_halving hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n
  · exact fun n => summableSubseqAux_error_bound hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n

/-- ε_n ≤ ε_0 / 2^n for the summable subsequence. -/
lemma summableSubseqAux_le_geometric {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (n : ℕ) :
    summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ n ≤
      summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ 0 / 2 ^ n := by
  let ε := summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀
  induction n with
  | zero => simp only [pow_zero, div_one, le_refl]
  | succ m ih =>
    calc ε (m + 1)
        ≤ ε m / 2 := summableSubseqAux_halving hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos m
      _ ≤ (ε 0 / 2 ^ m) / 2 :=
          div_le_div_of_nonneg_right ih (by norm_num : (0 : ℝ) ≤ 2)
      _ = ε 0 / 2 ^ (m + 1) := by
          rw [pow_succ]
          ring

/-- The summable subsequence tends to 0. -/
lemma summableSubseqAux_tendsto_zero {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) :
    Tendsto (summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀) atTop (𝓝 0) := by
  let ε := summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀
  have h_squeeze : ∀ n, ε n ≤ ε 0 * (1 / 2) ^ n := fun n => by
    have h1 := summableSubseqAux_le_geometric hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n
    have h2 : ε 0 / 2 ^ n = ε 0 * (1 / 2) ^ n := by
      rw [one_div, inv_pow, ← div_eq_mul_inv]
    linarith
  have h_geom_tendsto : Tendsto (fun n => ε 0 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using Tendsto.const_mul (ε 0)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  have h_pos : ∀ n, 0 ≤ ε n := fun n =>
    (summableSubseqAux_pos hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n).le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds h_geom_tendsto h_pos h_squeeze

/-- Cutoff integrand is interval integrable. -/
lemma cutoff_integrand_intervalIntegrable {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    (hat₀ : t₀ ∈ Set.Ioo a b) (_hL : L ≠ 0) (hγ_meas : Measurable γ)
    (hγ_cont_deriv : ContinuousOn (deriv γ) (Set.Icc a b)) (ε : ℝ) (hε_pos : 0 < ε) :
    IntervalIntegrable
      (fun t => if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0)
      MeasureTheory.volume a b := by
  have h_deriv_bdd : ∃ M > 0, ∀ t ∈ Set.Icc a b, ‖deriv γ t‖ ≤ M := by
    obtain ⟨x_max, _, hx_max⟩ := isCompact_Icc.exists_isMaxOn
      ⟨t₀, Set.Ioo_subset_Icc_self hat₀⟩ (continuous_norm.comp_continuousOn hγ_cont_deriv)
    exact ⟨max (‖deriv γ x_max‖) 1, lt_max_of_lt_right one_pos,
      fun t ht => le_max_of_le_left (hx_max ht)⟩
  obtain ⟨M_deriv, hM_pos, hM_deriv⟩ := h_deriv_bdd
  have hM_bound_pos : 0 < M_deriv / ε := div_pos hM_pos hε_pos
  have h_norm_bound_ae : ∀ t ∈ Set.uIoc a b,
      ‖(if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0)‖ ≤ M_deriv / ε := by
    intro t ht_uIoc
    have ht : t ∈ Set.Icc a b := by
      rw [Set.uIoc_of_le (hat₀.1.trans hat₀.2).le] at ht_uIoc
      exact Set.Ioc_subset_Icc_self ht_uIoc
    by_cases h_in : ε < ‖γ t - γ t₀‖
    · simp only [h_in, ↓reduceIte]
      have h_bound : ‖(γ t - γ t₀)⁻¹‖ ≤ 1 / ε := by
        rw [norm_inv, one_div]
        exact inv_anti₀ hε_pos h_in.le
      calc ‖(γ t - γ t₀)⁻¹ * deriv γ t‖
          = ‖(γ t - γ t₀)⁻¹‖ * ‖deriv γ t‖ := norm_mul _ _
        _ ≤ (1 / ε) * M_deriv :=
            mul_le_mul h_bound (hM_deriv t ht) (norm_nonneg _)
              (one_div_pos.mpr hε_pos).le
        _ = M_deriv / ε := by ring
    · simp only [h_in, ↓reduceIte, norm_zero, hM_bound_pos.le]
  rw [intervalIntegrable_iff]
  apply MeasureTheory.IntegrableOn.of_bound
  · exact measure_Ioc_lt_top
  · apply AEStronglyMeasurable.indicator
    · apply Measurable.aestronglyMeasurable
      exact ((hγ_meas.sub_const (γ t₀)).inv.mul (measurable_deriv γ))
    · exact (measurable_norm.comp (hγ_meas.sub_const (γ t₀))) measurableSet_Ioi
  · rw [MeasureTheory.ae_restrict_iff']
    · filter_upwards with t ht using h_norm_bound_ae t ht
    · exact measurableSet_uIoc

/-- Cutoff difference equals annulus integral. -/
lemma cutoff_diff_eq_annulus_integral {f : ℝ → ℂ} {γ : ℝ → ℂ} {a b t₀ : ℝ} {ε₁ ε₂ : ℝ}
    (h_le : ε₁ ≤ ε₂)
    (h_int₁ : IntervalIntegrable (fun t => if ε₁ < ‖γ t - γ t₀‖ then f t else 0)
      MeasureTheory.volume a b)
    (h_int₂ : IntervalIntegrable (fun t => if ε₂ < ‖γ t - γ t₀‖ then f t else 0)
      MeasureTheory.volume a b) :
    (∫ t in a..b, if ε₁ < ‖γ t - γ t₀‖ then f t else 0) -
      (∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ then f t else 0) =
        ∫ t in a..b, if ε₁ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₂ then f t else 0 := by
  rw [← intervalIntegral.integral_sub h_int₁ h_int₂]
  congr 1
  ext t
  grind

/-- Singular part cancellation via odd symmetry. -/
lemma pv_singular_cancels (t₀ ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) (hεδ : ε < δ) :
    (∫ t in (t₀ - δ)..(t₀ - ε), (↑(t - t₀) : ℂ)⁻¹) +
      (∫ t in (t₀ + ε)..(t₀ + δ), (↑(t - t₀) : ℂ)⁻¹) = 0 :=
  integral_inv_symm t₀ ε δ hε_pos hδ_pos hεδ.le

/-- Remainder step bound for dyadic step. -/
lemma remainder_step_bound {r : ℝ → ℂ} {t₀ ε η : ℝ} (hε_pos : 0 < ε) (_hη_pos : 0 < η)
    (hr_bound : ∀ t, ε / 2 < |t - t₀| → |t - t₀| < ε → ‖r t‖ ≤ η / |t - t₀|) :
    ‖∫ t in (t₀ - ε)..(t₀ - ε / 2), r t‖ + ‖∫ t in (t₀ + ε / 2)..(t₀ + ε), r t‖ ≤
      2 * η * Real.log 2 := by
  calc ‖∫ t in (t₀ - ε)..(t₀ - ε / 2), r t‖ + ‖∫ t in (t₀ + ε / 2)..(t₀ + ε), r t‖
      ≤ 2 * η * Real.log (ε / (ε / 2)) :=
        remainder_annulus_bound (by linarith) hε_pos (by linarith) (by linarith) hr_bound
    _ = 2 * η * Real.log 2 := by rw [show ε / (ε / 2) = 2 by field_simp]

/-- Remainder bounded ratio for annuli. -/
lemma remainder_bounded_ratio {r : ℝ → ℂ} {t₀ ε₁ ε₂ η K : ℝ} (hε₁_pos : 0 < ε₁)
    (hε₁₂ : ε₁ < ε₂) (hη_pos : 0 < η) (_hK : 1 < K) (h_ratio : ε₂ / ε₁ ≤ K)
    (hr_bound : ∀ t, ε₁ < |t - t₀| → |t - t₀| < ε₂ → ‖r t‖ ≤ η / |t - t₀|) :
    ‖∫ t in (t₀ - ε₂)..(t₀ - ε₁), r t‖ + ‖∫ t in (t₀ + ε₁)..(t₀ + ε₂), r t‖ ≤
      2 * η * Real.log K := by
  calc ‖∫ t in (t₀ - ε₂)..(t₀ - ε₁), r t‖ + ‖∫ t in (t₀ + ε₁)..(t₀ + ε₂), r t‖
      ≤ 2 * η * Real.log (ε₂ / ε₁) :=
        remainder_annulus_bound hε₁_pos (lt_trans hε₁_pos hε₁₂) hε₁₂ hη_pos hr_bound
    _ ≤ 2 * η * Real.log K := by
        nlinarith [Real.log_pos _hK,
          Real.log_le_log (div_pos (lt_trans hε₁_pos hε₁₂) hε₁_pos) h_ratio]

/-- Dyadic step bound for remainder. -/
lemma remainder_dyadic_step {r : ℝ → ℂ} {t₀ ε₀ η : ℝ} (n : ℕ) (hε₀_pos : 0 < ε₀)
    (hη_pos : 0 < η)
    (hr_bound : ∀ t, 0 < |t - t₀| → |t - t₀| < ε₀ → ‖r t‖ ≤ η / |t - t₀|) :
    ‖∫ t in (t₀ - ε₀ / 2 ^ n)..(t₀ - ε₀ / 2 ^ (n + 1)), r t‖ +
      ‖∫ t in (t₀ + ε₀ / 2 ^ (n + 1))..(t₀ + ε₀ / 2 ^ n), r t‖ ≤
        2 * η * Real.log 2 := by
  have h_pow_pos : (0 : ℝ) < 2 ^ n := by positivity
  have h_pow1_pos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have hε_n_pos : 0 < ε₀ / 2 ^ n := div_pos hε₀_pos h_pow_pos
  have hε_n1_pos : 0 < ε₀ / 2 ^ (n + 1) := div_pos hε₀_pos h_pow1_pos
  have h_lt : ε₀ / 2 ^ (n + 1) < ε₀ / 2 ^ n :=
    div_lt_div_of_pos_left hε₀_pos h_pow_pos
      (pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self n))
  have h_ratio : (ε₀ / 2 ^ n) / (ε₀ / 2 ^ (n + 1)) = 2 := by
    field_simp
    ring
  have hr_restricted : ∀ t, ε₀ / 2 ^ (n + 1) < |t - t₀| → |t - t₀| < ε₀ / 2 ^ n →
      ‖r t‖ ≤ η / |t - t₀| := fun t ht_lo ht_hi =>
    hr_bound t (lt_trans hε_n1_pos ht_lo)
      (ht_hi.trans_le (div_le_self hε₀_pos.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))))
  convert remainder_bounded_ratio hε_n1_pos h_lt hη_pos (by norm_num : (1 : ℝ) < 2)
    (by rw [h_ratio]) hr_restricted using 2

/-- Dyadic step O(ε) with bounded remainder. -/
lemma pv_dyadic_step_O_eps {r : ℝ → ℂ} {t₀ δ₀ C : ℝ} (n : ℕ) (hδ₀_pos : 0 < δ₀)
    (_hC_pos : 0 < C) (hr_bounded : ∀ t, 0 < |t - t₀| → |t - t₀| ≤ δ₀ → ‖r t‖ ≤ C) :
    let ε_n := δ₀ / 2 ^ n
    ‖∫ t in (t₀ - ε_n)..(t₀ - ε_n / 2), r t‖ +
      ‖∫ t in (t₀ + ε_n / 2)..(t₀ + ε_n), r t‖ ≤ C * ε_n := by
  intro ε_n
  have h_pow_pos : (0 : ℝ) < 2 ^ n := by positivity
  have hε_n_pos : 0 < ε_n := div_pos hδ₀_pos h_pow_pos
  have hε_n_half_pos : 0 < ε_n / 2 := by positivity
  have hε_n_le_δ₀ : ε_n ≤ δ₀ :=
    div_le_self hδ₀_pos.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have h_left : ‖∫ t in (t₀ - ε_n)..(t₀ - ε_n / 2), r t‖ ≤ C * (ε_n / 2) := by
    have hb : ∀ t ∈ Set.uIoc (t₀ - ε_n) (t₀ - ε_n / 2), ‖r t‖ ≤ C := fun t ht => by
      have hle : t₀ - ε_n ≤ t₀ - ε_n / 2 := by linarith
      obtain ⟨h1, h2⟩ := (Set.uIoc_of_le hle ▸ ht : t ∈ Set.Ioc _ _)
      refine hr_bounded t (abs_pos.mpr (by linarith)) ?_
      rw [abs_of_neg (by linarith : t - t₀ < 0)]
      linarith
    calc ‖∫ t in (t₀ - ε_n)..(t₀ - ε_n / 2), r t‖
        ≤ C * |(t₀ - ε_n / 2) - (t₀ - ε_n)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ = C * (ε_n / 2) := by
          rw [show (t₀ - ε_n / 2) - (t₀ - ε_n) = ε_n / 2 by ring,
            abs_of_pos hε_n_half_pos]
  have h_right : ‖∫ t in (t₀ + ε_n / 2)..(t₀ + ε_n), r t‖ ≤ C * (ε_n / 2) := by
    have hb : ∀ t ∈ Set.uIoc (t₀ + ε_n / 2) (t₀ + ε_n), ‖r t‖ ≤ C := fun t ht => by
      have hle : t₀ + ε_n / 2 ≤ t₀ + ε_n := by linarith
      obtain ⟨h1, h2⟩ := (Set.uIoc_of_le hle ▸ ht : t ∈ Set.Ioc _ _)
      refine hr_bounded t (abs_pos.mpr (by linarith)) ?_
      rw [abs_of_pos (by linarith : t - t₀ > 0)]
      linarith
    calc ‖∫ t in (t₀ + ε_n / 2)..(t₀ + ε_n), r t‖
        ≤ C * |(t₀ + ε_n) - (t₀ + ε_n / 2)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ = C * (ε_n / 2) := by
          rw [show (t₀ + ε_n) - (t₀ + ε_n / 2) = ε_n / 2 by ring,
            abs_of_pos hε_n_half_pos]
  linarith

/-- Dyadic sequence is Cauchy with bounded remainder. -/
lemma cauchySeq_pv_dyadic {I : ℝ → ℂ} {δ₀ C : ℝ} (_hδ₀_pos : 0 < δ₀) (_hC_pos : 0 < C)
    (h_step : ∀ n, ‖I (δ₀ / 2 ^ (n + 1)) - I (δ₀ / 2 ^ n)‖ ≤ C * δ₀ / 2 ^ n) :
    CauchySeq (fun n => I (δ₀ / 2 ^ n)) := by
  refine cauchySeq_of_le_geometric (1 / 2) (C * δ₀) (by norm_num) (fun n => ?_)
  rw [dist_comm, dist_eq_norm]
  calc ‖I (δ₀ / 2 ^ (n + 1)) - I (δ₀ / 2 ^ n)‖
      ≤ C * δ₀ / 2 ^ n := h_step n
    _ = C * δ₀ * (1 / 2) ^ n := by rw [one_div, inv_pow, ← div_eq_mul_inv]

/-- t-space bound from γ-annulus. -/
lemma t_bound_from_gamma_annulus {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {δ₁ ε : ℝ} (hL : L ≠ 0)
    (_hε_pos : 0 < ε)
    (h_lower : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₁ → ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀|)
    (t : ℝ) (ht_pos : 0 < |t - t₀|) (ht_lt : |t - t₀| < δ₁)
    (hγ_bound : ‖γ t - γ t₀‖ ≤ ε) :
    |t - t₀| ≤ 2 * ε / ‖L‖ := by
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  calc |t - t₀|
      = 2 * ((‖L‖ / 2) * |t - t₀|) / ‖L‖ := by field_simp
    _ ≤ 2 * ‖γ t - γ t₀‖ / ‖L‖ :=
        div_le_div_of_nonneg_right (by linarith [h_lower t ht_pos ht_lt]) hL_norm_pos.le
    _ ≤ 2 * ε / ‖L‖ :=
        div_le_div_of_nonneg_right (by linarith) hL_norm_pos.le

/-- Integrand bound on γ-annulus. -/
lemma integrand_bound_on_annulus {γ : ℝ → ℂ} {t₀ : ℝ} {C δ₀ : ℝ}
    (hr_bounded : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₀ →
      ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ C)
    (t : ℝ) (ht_pos : 0 < |t - t₀|) (ht_lt : |t - t₀| < δ₀) :
    ‖(γ t - γ t₀)⁻¹ * deriv γ t‖ ≤ |t - t₀|⁻¹ + C := by
  have h_inv_norm : ‖(↑(t - t₀) : ℂ)⁻¹‖ = |t - t₀|⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
  calc ‖(γ t - γ t₀)⁻¹ * deriv γ t‖
      ≤ ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ + ‖(↑(t - t₀) : ℂ)⁻¹‖ := by
          linarith [norm_sub_norm_le ((γ t - γ t₀)⁻¹ * deriv γ t) (↑(t - t₀))⁻¹]
    _ ≤ C + |t - t₀|⁻¹ := by
        rw [h_inv_norm]
        linarith [hr_bounded t ht_pos ht_lt]
    _ = |t - t₀|⁻¹ + C := by ring

/-- Annulus localization: γ-annulus points are local. -/
lemma annulus_implies_t_local {γ : ℝ → ℂ} {a b t₀ : ℝ} {ε₁ δ₀ δ₁ : ℝ}
    (h_localize : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₀ δ₁)
    (t : ℝ) (ht_ab : t ∈ Set.Icc a b) (hγ_bound : ‖γ t - γ t₀‖ ≤ ε₁) :
    |t - t₀| < δ₀ ∧ |t - t₀| < δ₁ := by
  have h := h_localize t ht_ab hγ_bound
  exact ⟨h.trans_le (min_le_left _ _), h.trans_le (min_le_right _ _)⟩

/-- Bracket ε between dyadic points: for ε ∈ (0, δ], find n with δ/2^(n+1) < ε ≤ δ/2^n. -/
lemma exists_dyadic_bracket {δ ε : ℝ} (hδ_pos : 0 < δ) (hε_pos : 0 < ε) (hε_le : ε ≤ δ) :
    ∃ n : ℕ, δ / 2 ^ (n + 1) < ε ∧ ε ≤ δ / 2 ^ n := by
  have h_tendsto : Tendsto (fun n : ℕ => δ / 2 ^ n) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
    have hi : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
      simp_rw [one_div]
      exact tendsto_inv_atTop_zero.comp hp
    have h_eq : (fun n : ℕ => δ / 2 ^ n) = (fun n => δ * (1 / 2 ^ n)) := by
      ext n
      ring
    rw [h_eq, show (0 : ℝ) = δ * 0 by ring]
    exact Tendsto.const_mul δ hi
  rw [Metric.tendsto_atTop] at h_tendsto
  obtain ⟨N, hN⟩ := h_tendsto ε hε_pos
  have h_exists : ∃ n : ℕ, δ / 2 ^ n < ε := by
    use N
    specialize hN N le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos hδ_pos (by positivity))] at hN
    exact hN
  let m := Nat.find h_exists
  have hm_lt : δ / 2 ^ m < ε := Nat.find_spec h_exists
  by_cases hm_zero : m = 0
  · simp only [hm_zero, pow_zero, div_one] at hm_lt
    exact absurd hε_le (not_le.mpr hm_lt)
  · obtain ⟨n, hn_eq⟩ := Nat.exists_eq_succ_of_ne_zero hm_zero
    use n
    refine ⟨?_, ?_⟩
    · rw [show n + 1 = m from hn_eq.symm]
      exact hm_lt
    · by_contra h_not
      push Not at h_not
      exact Nat.find_min h_exists (by omega : n < m) h_not

/-- Telescoping sum bound for geometric step bounds. -/
lemma telescoping_sum_bound {X : Type*} [SeminormedAddCommGroup X] {I : ℕ → X} {K δ : ℝ}
    (_hK_pos : 0 < K) (_hδ_pos : 0 < δ)
    (h_step : ∀ n, ‖I (n + 1) - I n‖ ≤ K * δ / 2 ^ n) (N : ℕ) :
    ∀ M, M > N → ‖I M - I N‖ ≤ 2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ M := by
  intro M hM_gt_N
  obtain ⟨d, hd_eq⟩ : ∃ d, M = N + d + 1 := by
    use M - N - 1
    omega
  subst hd_eq
  induction d with
  | zero =>
    calc ‖I (N + 0 + 1) - I N‖
        = ‖I (N + 1) - I N‖ := by ring_nf
      _ ≤ K * δ / 2 ^ N := h_step N
      _ = 2 * K * δ / 2 ^ N - K * δ / 2 ^ N := by ring
      _ = 2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ (N + 1) := by
          rw [pow_succ]
          ring
      _ = 2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ (N + 0 + 1) := by ring_nf
  | succ d' ih =>
    have ih' := ih (by omega : N + d' + 1 > N)
    change ‖I (N + (d' + 1) + 1) - I N‖ ≤
      2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ (N + (d' + 1) + 1)
    simp only [show N + (d' + 1) + 1 = N + d' + 2 by omega]
    rw [(sub_add_sub_cancel (I (N + d' + 2)) (I (N + d' + 1)) (I N)).symm]
    have h_step_d' : ‖I (N + d' + 2) - I (N + d' + 1)‖ ≤ K * δ / 2 ^ (N + d' + 1) := by
      conv_lhs => rw [show N + d' + 2 = (N + d' + 1) + 1 by omega]
      exact h_step (N + d' + 1)
    calc ‖(I (N + d' + 2) - I (N + d' + 1)) + (I (N + d' + 1) - I N)‖
        ≤ ‖I (N + d' + 2) - I (N + d' + 1)‖ + ‖I (N + d' + 1) - I N‖ :=
          norm_add_le _ _
      _ ≤ K * δ / 2 ^ (N + d' + 1) +
          (2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ (N + d' + 1)) := by
            linarith [h_step_d', ih']
      _ = 2 * K * δ / 2 ^ N - K * δ / 2 ^ (N + d' + 1) := by ring
      _ = 2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ (N + d' + 2) := by
          have h_pow : (2 : ℝ) ^ (N + d' + 2) = 2 * 2 ^ (N + d' + 1) := by
            rw [pow_succ]
            ring
          field_simp [h_pow]
          ring

end
