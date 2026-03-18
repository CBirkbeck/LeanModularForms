/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer.HigherOrderAssembly

/-!
# Generalized Residue Theorem (Theorem 3.3)

CPV existence for `(z-z₀)⁻¹` along piecewise C¹ immersions, PV residue
convergence, and the final Theorem 3.3 from Hungerbühler-Wasem.

## Main results

* `cpv_exists_inv_sub_of_closed_unique`: CPV of `(z-z₀)⁻¹` exists for closed curves
* `generalizedResidueTheorem_3_3`: the generalized residue theorem with conditions (A')+(B)
-/

open Complex MeasureTheory Set Filter Topology Finset Real
open scoped Interval

noncomputable section

namespace GeneralizedResidueTheory

/-! ## Theorem 3.3 with paper's conditions (A')+(B)

The final theorem, using the bridge lemma to replace `hHigherOrderCancel`
with the paper's actual hypotheses. Uses `SatisfiesConditionA'` with
`poleOrderAt f` for proper variable-order flatness. -/

set_option maxHeartbeats 1600000 in
private lemma continuousOn_cutoff_integral
    (γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ)
    (_ht₀ : t₀ ∈ Set.Ioo γ.a γ.b)
    (_hcross : γ.toFun t₀ = z₀)
    (_honly : ∀ t ∈ Set.Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀)
    (δ : ℝ) (_hδ : δ > 0)
    (hbnd : ∀ ε ∈ Set.Ioo 0 δ, ∃ σ₁ σ₂,
      γ.a ≤ σ₁ ∧ σ₁ < t₀ ∧ t₀ < σ₂ ∧ σ₂ ≤ γ.b ∧
      ‖γ.toFun σ₁ - z₀‖ = ε ∧ ‖γ.toFun σ₂ - z₀‖ = ε ∧
      (∀ t ∈ Set.Ico γ.a σ₁, ε < ‖γ.toFun t - z₀‖) ∧
      (∀ t ∈ Set.Ioc σ₂ γ.b, ε < ‖γ.toFun t - z₀‖) ∧
      ∀ t ∈ Set.Icc σ₁ σ₂, ‖γ.toFun t - z₀‖ ≤ ε)
    (l r : ℝ) (hl_lt : l < t₀) (hr_gt : t₀ < r)
    (_hl_ge_a : γ.a ≤ l) (_hr_le_b : r ≤ γ.b)
    (hg_anti : StrictAntiOn (fun t => ‖γ.toFun t - z₀‖) (Set.Icc l t₀))
    (hg_mono : StrictMonoOn (fun t => ‖γ.toFun t - z₀‖) (Set.Icc t₀ r))
    (hδ_le_l : δ ≤ ‖γ.toFun l - z₀‖) (hδ_le_r : δ ≤ ‖γ.toFun r - z₀‖) :
    ContinuousOn (fun ε => ∫ t in γ.a..γ.b,
      if ‖γ.toFun t - z₀‖ > ε then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0)
      (Set.Ioo 0 δ) := by
  intro ε₀ hε₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := piecewiseC1Immersion_deriv_bounded γ
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM γ.a (left_mem_Icc.mpr γ.hab.le))
  have hε₀_pos : (0 : ℝ) < ε₀ := hε₀.1
  have hε₀_half : (0 : ℝ) < ε₀ / 2 := by linarith
  have h_level_null : volume {t ∈ Icc γ.a γ.b | ‖γ.toFun t - z₀‖ = ε₀} = 0 := by
    obtain ⟨σ₁, σ₂, hσ₁_ge, hσ₁_lt, hσ₂_gt, hσ₂_le,
      hσ₁_val, hσ₂_val, h_left, h_right, h_mid⟩ := hbnd ε₀ hε₀
    have hσ₁_ge_l : l ≤ σ₁ := by
      by_contra h_lt; push_neg at h_lt
      have hl_in : l ∈ Icc σ₁ σ₂ := ⟨h_lt.le, le_trans hl_lt.le hσ₂_gt.le⟩
      exact absurd (h_mid l hl_in) (not_le.mpr (by linarith [hδ_le_l, hε₀.2]))
    have hσ₂_le_r : σ₂ ≤ r := by
      by_contra h_gt; push_neg at h_gt
      have hr_in : r ∈ Icc σ₁ σ₂ :=
        ⟨le_trans hσ₁_lt.le (le_trans (le_of_lt hr_gt) (le_refl r)), h_gt.le⟩
      exact absurd (h_mid r hr_in) (not_le.mpr (by linarith [hδ_le_r, hε₀.2]))
    apply measure_mono_null (t := ({σ₁, σ₂} : Set ℝ))
    · intro t ⟨ht_Icc, ht_eq⟩
      have ht_σ : t ∈ Icc σ₁ σ₂ := by
        refine ⟨?_, ?_⟩
        · by_contra h; push_neg at h; linarith [h_left t ⟨ht_Icc.1, h⟩]
        · by_contra h; push_neg at h; linarith [h_right t ⟨h, ht_Icc.2⟩]
      rcases le_or_gt t t₀ with htt₀ | ht₀t
      · left; exact hg_anti.injOn ⟨le_trans hσ₁_ge_l ht_σ.1, htt₀⟩
          ⟨hσ₁_ge_l, hσ₁_lt.le⟩ (ht_eq ▸ hσ₁_val.symm)
      · right; exact hg_mono.injOn ⟨ht₀t.le, le_trans ht_σ.2 hσ₂_le_r⟩
          ⟨hσ₂_gt.le, hσ₂_le_r⟩ (ht_eq ▸ hσ₂_val.symm)
    · exact (Set.toFinite {σ₁, σ₂}).measure_zero _
  apply intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => (ε₀ / 2)⁻¹ * M)
  · have hε₀_lt_δ := hε₀.2
    filter_upwards [Ioo_mem_nhds (by linarith : ε₀ / 2 < ε₀)
      (show ε₀ < min (ε₀ + 1) δ from lt_min (by linarith) hε₀_lt_δ)] with ε hε
    have hε_pos : 0 < ε := lt_trans (by linarith : (0:ℝ) < ε₀ / 2) hε.1
    have hε_lt_δ : ε < δ := lt_of_lt_of_le hε.2 (min_le_right _ _)
    obtain ⟨σ₁, σ₂, hσ₁_ge, hσ₁_lt, hσ₂_gt, hσ₂_le,
      hσ₁_val, hσ₂_val, h_left, h_right, h_mid⟩ := hbnd ε ⟨hε_pos, hε_lt_δ⟩
    set Q : Finset ℝ := γ.partition ∪ {σ₁, σ₂}
    have h_cont_off : ContinuousOn
        (fun t => if ‖γ.toFun t - z₀‖ > ε then
          (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0) (Icc γ.a γ.b \ ↑Q) := by
      intro t ⟨ht_Icc, ht_nQ⟩
      have ht_nP : t ∉ (↑γ.partition : Set ℝ) := by
        intro h; exact ht_nQ (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_coe.mp h)))
      have ht_ne_σ₁ : t ≠ σ₁ := by
        intro h; exact ht_nQ (Finset.mem_coe.mpr (Finset.mem_union_right _
          (Finset.mem_insert_self σ₁ {σ₂}) |> (h ▸ ·)))
      have ht_ne_σ₂ : t ≠ σ₂ := by
        intro h; exact ht_nQ (Finset.mem_coe.mpr (Finset.mem_union_right _
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self σ₂)) |> (h ▸ ·)))
      have ht_Ioo : t ∈ Ioo γ.a γ.b :=
        ⟨lt_of_le_of_ne ht_Icc.1 (fun h =>
          ht_nP (h ▸ γ.toPiecewiseC1Curve.endpoints_in_partition.1)),
         lt_of_le_of_ne ht_Icc.2 (fun h =>
          ht_nP (h.symm ▸ γ.toPiecewiseC1Curve.endpoints_in_partition.2))⟩
      by_cases h₁ : t < σ₁
      · have h_gt : ε < ‖γ.toFun t - z₀‖ := h_left t ⟨ht_Icc.1, h₁⟩
        have hne : γ.toFun t - z₀ ≠ 0 := by intro h; rw [h, norm_zero] at h_gt; linarith
        exact (ContinuousAt.mul
          ((γ.continuous_toFun.continuousAt (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2) |>.sub
            continuousAt_const).inv₀ hne)
          (γ.toPiecewiseC1Curve.deriv_continuous_off_partition t ht_Ioo ht_nP)
          ).congr (by
            filter_upwards [(continuous_norm.continuousAt.comp
              (γ.continuous_toFun.continuousAt (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2) |>.sub
                continuousAt_const)).eventually (isOpen_Ioi.mem_nhds h_gt)]
              with s hs; exact (if_pos hs).symm) |>.continuousWithinAt
      · by_cases h₂ : σ₂ < t
        · have h_gt : ε < ‖γ.toFun t - z₀‖ := h_right t ⟨h₂, ht_Icc.2⟩
          have hne : γ.toFun t - z₀ ≠ 0 := by intro h; rw [h, norm_zero] at h_gt; linarith
          exact (ContinuousAt.mul
            ((γ.continuous_toFun.continuousAt (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2) |>.sub
              continuousAt_const).inv₀ hne)
            (γ.toPiecewiseC1Curve.deriv_continuous_off_partition t ht_Ioo ht_nP)
            ).congr (by
              filter_upwards [(continuous_norm.continuousAt.comp
                (γ.continuous_toFun.continuousAt (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2) |>.sub
                  continuousAt_const)).eventually (isOpen_Ioi.mem_nhds h_gt)]
                with s hs; exact (if_pos hs).symm) |>.continuousWithinAt
        · have ht_mid : t ∈ Ioo σ₁ σ₂ :=
            ⟨lt_of_le_of_ne (not_lt.mp h₁) (Ne.symm ht_ne_σ₁),
             lt_of_le_of_ne (not_lt.mp h₂) ht_ne_σ₂⟩
          exact continuousAt_const.congr (by
            filter_upwards [Ioo_mem_nhds ht_mid.1 ht_mid.2] with s hs
            exact (if_neg (not_lt.mpr (h_mid s ⟨hs.1.le, hs.2.le⟩))).symm
            ) |>.continuousWithinAt
    exact (intervalIntegrable_of_piecewise_continuousOn_bounded
      ((ε₀ / 2)⁻¹ * M) γ.hab.le h_cont_off
      (fun t ht => by
        split_ifs with h
        · rw [norm_mul, norm_inv]
          exact mul_le_mul (inv_anti₀ hε₀_half (le_of_lt (lt_trans hε.1 h)))
            (hM t ht) (norm_nonneg _) (inv_nonneg.mpr hε₀_half.le)
        · simp only [norm_zero]
          exact mul_nonneg (inv_nonneg.mpr hε₀_half.le) hM_nn)
      ).aestronglyMeasurable.mono_measure (by
        rw [Set.uIoc_of_le γ.hab.le])
  · filter_upwards [Ioo_mem_nhds (by linarith : ε₀ / 2 < ε₀)
      (by linarith [hε₀.2] : ε₀ < ε₀ + 1)] with ε hε
    filter_upwards with t ht
    split_ifs with h
    · rw [Set.uIoc_of_le γ.hab.le] at ht
      rw [norm_mul, norm_inv]
      exact mul_le_mul (inv_anti₀ hε₀_half (le_of_lt (lt_trans hε.1 h)))
        (hM t (Ioc_subset_Icc_self ht)) (norm_nonneg _) (inv_nonneg.mpr hε₀_half.le)
    · simp only [norm_zero]
      exact mul_nonneg (inv_nonneg.mpr hε₀_half.le) hM_nn
  · exact intervalIntegrable_const
  · rw [Set.uIoc_of_le γ.hab.le]
    have h_ae : ∀ᵐ t ∂volume,
        ¬(t ∈ Icc γ.a γ.b ∧ ‖γ.toFun t - z₀‖ = ε₀) :=
      compl_mem_ae_iff.mpr h_level_null
    filter_upwards [h_ae] with t ht_not_level ht_Ioc
    have ht_Icc := Ioc_subset_Icc_self ht_Ioc
    have h_ne : ‖γ.toFun t - z₀‖ ≠ ε₀ := fun h => ht_not_level ⟨ht_Icc, h⟩
    rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
    · have h_ev : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝 ε₀]
          (fun ε => if ‖γ.toFun t - z₀‖ > ε then
            (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0) := by
        filter_upwards [Ioi_mem_nhds h_lt] with ε hε
        exact (if_neg (not_lt.mpr (mem_Ioi.mp hε).le)).symm
      exact continuousAt_const.congr h_ev
    · have h_ev : (fun _ : ℝ => (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t) =ᶠ[𝓝 ε₀]
          (fun ε => if ‖γ.toFun t - z₀‖ > ε then
            (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0) := by
        filter_upwards [Iio_mem_nhds h_gt] with ε hε
        exact (if_pos (mem_Iio.mp hε)).symm
      exact continuousAt_const.congr h_ev

/-- PV of `(z-z₀)⁻¹` exists along a closed PiecewiseC1Immersion with unique crossing.
This is the C²-free version of `cpv_exists_inv_sub`: it uses the exp-convergence
from `tendsto_exp_cutoff_integral_crossing` (which doesn't need C²) together with
a Cauchy transfer argument to extract convergence of the integral itself. -/
lemma cpv_exists_inv_sub_of_closed_unique
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (hclosed : γ.toPiecewiseC1Curve.IsClosed)
    (_h_no_endpt : γ.toFun γ.a ≠ z₀ ∧ γ.toFun γ.b ≠ z₀)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo γ.a γ.b) (hcross : γ.toFun t₀ = z₀)
    (honly : ∀ t ∈ Set.Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀) :
    CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun γ.a γ.b z₀ := by
  set R : ℝ → ℂ := fun ε => ∫ t in γ.a..γ.b,
    if ‖γ.toFun t - z₀‖ > ε then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0
  have h_exp := tendsto_exp_cutoff_integral_crossing γ hclosed z₀ t₀ ht₀ hcross honly
  obtain ⟨δ, hδ, l, r, hl_lt, hr_gt, hl_ge_a, hr_le_b, hg_anti, hg_mono,
    hδ_le_l, hδ_le_r, hbnd⟩ :=
    exists_cutoff_boundary_times_with_mono γ z₀ t₀ ht₀ hcross honly
  have h_re_zero : ∀ᶠ ε in 𝓝[>] (0:ℝ), (R ε).re = 0 := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    obtain ⟨σ₁, σ₂, ha, hlt₁, hlt₂, hb, hnorm₁, hnorm₂, _, _, _⟩ :=
      hbnd ε hε
    have h_ftc := exp_cutoff_integral_eq_ratio γ hclosed z₀ σ₁ σ₂ ε
      ha (lt_trans hlt₁ hlt₂) hb hε.1 hnorm₁ hnorm₂ ‹_› ‹_› ‹_›
    have h_norm : ‖Complex.exp (R ε)‖ = 1 := by
      rw [h_ftc, norm_div, hnorm₁, hnorm₂]
      exact div_self (ne_of_gt hε.1)
    rw [Complex.norm_exp] at h_norm
    exact (Real.exp_eq_one_iff _).mp h_norm
  set L₀ : ℂ := Complex.exp (-(I * ↑(angleAtCrossing γ t₀ ht₀)))
  have hL₀_ne : L₀ ≠ 0 := Complex.exp_ne_zero _
  have hR_cont : ContinuousOn R (Ioo 0 δ) :=
    continuousOn_cutoff_integral γ z₀ t₀ ht₀ hcross honly δ hδ hbnd
      l r hl_lt hr_gt hl_ge_a hr_le_b hg_anti hg_mono hδ_le_l hδ_le_r
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hL₀_ne with hsp | hsp
  · exact cpv_of_exp_tendsto_slitPlane R L₀ δ hδ hsp h_exp hR_cont
  · exact cpv_of_exp_tendsto_neg_slitPlane R L₀ δ hδ hsp h_exp hR_cont
  where
  cpv_of_exp_tendsto_slitPlane (R : ℝ → ℂ) (L₀ : ℂ) (δ : ℝ) (hδ : 0 < δ)
      (hsp : L₀ ∈ Complex.slitPlane)
      (h_exp : Tendsto (fun ε => Complex.exp (R ε)) (𝓝[>] 0) (𝓝 L₀))
      (hR_cont : ContinuousOn R (Ioo 0 δ)) :
      ∃ L, Tendsto R (𝓝[>] 0) (𝓝 L) := by
    have h_log : Tendsto (fun ε => Complex.log (Complex.exp (R ε))) (𝓝[>] 0)
        (𝓝 (Complex.log L₀)) := h_exp.clog hsp
    have h_sp_ev := h_exp.eventually (Complex.isOpen_slitPlane.mem_nhds hsp)
    obtain ⟨η, hη, hη_le_δ, hη_sp⟩ : ∃ η > 0, η ≤ δ ∧ ∀ ε ∈ Ioo (0:ℝ) η,
        Complex.exp (R ε) ∈ Complex.slitPlane := by
      rw [Filter.Eventually, mem_nhdsWithin] at h_sp_ev
      obtain ⟨U, hU_open, h0_mem, hU_sub⟩ := h_sp_ev
      obtain ⟨r, hr, hr_ball⟩ := Metric.isOpen_iff.mp hU_open 0 h0_mem
      exact ⟨min r δ, by positivity, min_le_right _ _, fun ε hε => hU_sub ⟨hr_ball (by
        simp only [Metric.mem_ball, Real.dist_eq]
        rw [sub_zero, abs_of_pos hε.1]
        exact lt_of_lt_of_le hε.2 (min_le_left _ _)), hε.1⟩⟩
    have h_logexp_cont : ContinuousOn (fun ε => Complex.log (Complex.exp (R ε))) (Ioo 0 η) :=
      (Complex.continuous_exp.comp_continuousOn
        (hR_cont.mono fun ε hε => ⟨(Set.mem_Ioo.mp hε).1,
          lt_of_lt_of_le (Set.mem_Ioo.mp hε).2 hη_le_δ⟩)).clog fun ε hε => hη_sp ε hε
    have h_phi_cont : ContinuousOn (fun ε => R ε - Complex.log (Complex.exp (R ε))) (Ioo 0 η) :=
      (hR_cont.mono fun ε hε => ⟨(Set.mem_Ioo.mp hε).1,
        lt_of_lt_of_le (Set.mem_Ioo.mp hε).2 hη_le_δ⟩).sub h_logexp_cont
    have h_phi_const : ∀ ε₁ ∈ Ioo (0:ℝ) η, ∀ ε₂ ∈ Ioo (0:ℝ) η,
        R ε₁ - Complex.log (Complex.exp (R ε₁)) =
        R ε₂ - Complex.log (Complex.exp (R ε₂)) := by
      set T : Set ℂ := Set.range (fun n : ℤ => ↑n * (2 * ↑Real.pi * I)) with hT_def
      have h_maps : Set.MapsTo
          (fun ε => R ε - Complex.log (Complex.exp (R ε))) (Ioo 0 η) T := by
        intro ε hε
        have h_exp_eq : Complex.exp (R ε - Complex.log (Complex.exp (R ε))) = 1 := by
          rw [Complex.exp_sub, Complex.exp_log (Complex.exp_ne_zero _), div_self
            (Complex.exp_ne_zero _)]
        rw [Complex.exp_eq_one_iff] at h_exp_eq
        obtain ⟨n, hn⟩ := h_exp_eq
        exact ⟨n, hn.symm⟩
      have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
      have hT_disc : DiscreteTopology T := by
        rw [discreteTopology_subtype_iff']
        intro y hy
        refine ⟨Metric.ball y (2 * Real.pi), Metric.isOpen_ball, ?_⟩
        ext z
        simp only [Set.mem_inter_iff, Metric.mem_ball, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hz_ball, hz_mem⟩
          obtain ⟨m, rfl⟩ := hy
          obtain ⟨n, rfl⟩ := hz_mem
          by_contra h_ne
          have hmn : m ≠ n := by intro heq; exact h_ne (by rw [heq])
          have h_sub : (↑n : ℂ) * (2 * ↑Real.pi * I) - ↑m * (2 * ↑Real.pi * I) =
              ↑(n - m) * (2 * ↑Real.pi * I) := by push_cast; ring
          have h_norm_2piI : ‖(2 * ↑Real.pi * I : ℂ)‖ = 2 * Real.pi := by
            simp only [norm_mul, Complex.norm_ofNat,
              Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
              Complex.norm_I, mul_one]
          have h_dist : dist (↑n * (2 * ↑Real.pi * I)) (↑m * (2 * ↑Real.pi * I)) =
              ‖(↑(n - m) : ℂ)‖ * (2 * Real.pi) := by
            rw [dist_eq_norm, h_sub, norm_mul, h_norm_2piI]
          rw [h_dist, Complex.norm_intCast] at hz_ball
          have h_int_pos : (1 : ℝ) ≤ |(↑(n - m) : ℝ)| := by
            have h1 := Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hmn))
            rw [← Int.cast_abs] at hz_ball ⊢
            exact_mod_cast h1
          linarith [mul_le_mul_of_nonneg_right h_int_pos (le_of_lt h2pi_pos)]
        · intro heq
          exact ⟨by rw [heq]; exact Metric.mem_ball_self h2pi_pos,
            by rw [heq]; exact hy⟩
      intro ε₁ hε₁ ε₂ hε₂
      exact isPreconnected_Ioo.constant_of_mapsTo h_phi_cont h_maps hε₁ hε₂
    have hη2 : η / 2 ∈ Ioo (0:ℝ) η := ⟨by linarith, by linarith⟩
    set k := R (η / 2) - Complex.log (Complex.exp (R (η / 2)))
    have hR_eq : ∀ᶠ ε in 𝓝[>] (0:ℝ), R ε = Complex.log (Complex.exp (R ε)) + k := by
      filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
      have := h_phi_const ε hε (η / 2) hη2; linear_combination this
    exact ⟨Complex.log L₀ + k, Filter.Tendsto.congr'
      (by filter_upwards [hR_eq] with ε hε; exact hε.symm)
      (h_log.add tendsto_const_nhds)⟩
  cpv_of_exp_tendsto_neg_slitPlane (R : ℝ → ℂ) (L₀ : ℂ) (δ : ℝ) (hδ : 0 < δ)
      (hsp : -L₀ ∈ Complex.slitPlane)
      (h_exp : Tendsto (fun ε => Complex.exp (R ε)) (𝓝[>] 0) (𝓝 L₀))
      (hR_cont : ContinuousOn R (Ioo 0 δ)) :
      ∃ L, Tendsto R (𝓝[>] 0) (𝓝 L) := by
    have h_shift : Tendsto (fun ε => Complex.exp (R ε + ↑Real.pi * I))
        (𝓝[>] 0) (𝓝 (-L₀)) := by
      have : (fun ε => Complex.exp (R ε + ↑Real.pi * I)) =
          (fun ε => -(Complex.exp (R ε))) := by
        ext ε; rw [Complex.exp_add, Complex.exp_pi_mul_I]; ring
      rw [this]; exact h_exp.neg
    have hR'_cont : ContinuousOn (fun ε => R ε + ↑Real.pi * I) (Ioo 0 δ) :=
      hR_cont.add continuousOn_const
    obtain ⟨L', hL'⟩ := cpv_of_exp_tendsto_slitPlane
      (fun ε => R ε + ↑Real.pi * I) (-L₀) δ hδ hsp h_shift hR'_cont
    exact ⟨L' - ↑Real.pi * I, by
      have : R = fun ε => (R ε + ↑Real.pi * I) - ↑Real.pi * I := by ext; ring
      rw [this]; exact hL'.sub tendsto_const_nhds⟩

/-- PV convergence of the pure residue function for closed PiecewiseC1Immersion curves. -/
lemma pv_res_tendsto_of_immersion
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S)
    (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (_hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t)
      (𝓝[>] 0) (𝓝 (2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s)) := by
  set f_res := fun z => ∑ s ∈ S0, residueAt f s / (z - s) with hf_res_def
  have hSimple_res : ∀ s ∈ S0, HasSimplePoleAt f_res s :=
    fun s hs => hasSimplePoleAt_sum_div_sub S0 (residueAt f) s hs
  have hf_res_diff : DifferentiableOn ℂ f_res (U \ ↑S0) :=
    differentiableOn_sum_div_sub S0 (residueAt f) U
  have hf_ext_res : ∀ s ∈ S0, ContinuousAt
      (fun z => f_res z - residueSimplePole f_res s / (z - s)) s :=
    fun s hs => continuousAt_sum_remainder S0 (residueAt f) s hs
  have h_res_eq : ∀ s ∈ S0,
      residueSimplePole f_res s = residueAt f s :=
    fun s hs => residueSimplePole_sum_div_sub S0 (residueAt f) s hs
  have hPV_singular : ∀ s ∈ S0, CauchyPrincipalValueExists'
      (fun z => residueSimplePole f_res s / (z - s)) γ.toFun γ.a γ.b s := by
    intro s hs
    have h_eq : (fun z => residueSimplePole f_res s / (z - s)) =
        (fun z => residueSimplePole f_res s * (fun z => (z - s)⁻¹) z) := by
      ext z; simp only [div_eq_mul_inv]
    rw [h_eq]
    apply CauchyPrincipalValueExists'.const_mul
    apply cauchyPrincipalValueExists_of_singular_inv γ s
    intro ⟨t₀, ht₀, hcross⟩
    have h_fin := finite_crossings γ s
    have ht₀_Ioo : t₀ ∈ Ioo γ.a γ.b := by
      refine ⟨lt_of_le_of_ne ht₀.1 (fun h => ?_), lt_of_le_of_ne ht₀.2 (fun h => ?_)⟩
      · exact (h_no_endpt_cross s hs).1 (h ▸ hcross)
      · exact (h_no_endpt_cross s hs).2 (h ▸ hcross)
    obtain ⟨a', b', ha't₀, ht₀b', ha'b'_sub, honly', _⟩ :=
      exists_isolated_crossing_interval γ s t₀ ht₀_Ioo hcross
    have honly : ∀ t ∈ Set.Icc γ.a γ.b, γ.toFun t = s → t = t₀ :=
      fun t ht hgt => h_unique_cross s hs t ht t₀ ht₀ hgt hcross
    have h_exp := tendsto_exp_cutoff_integral_crossing γ hγ_closed s t₀ ht₀_Ioo hcross honly
    suffices ∃ M, Tendsto (fun ε => ∫ (t : ℝ) in γ.a..γ.b,
        if ε < ‖γ.toFun t - s‖ then (γ.toFun t - s)⁻¹ * deriv γ.toFun t else 0)
        (𝓝[>] 0) (𝓝 M) from this.choose_spec.cauchy_map
    exact cpv_exists_inv_sub_of_closed_unique γ s hγ_closed
      (h_no_endpt_cross s hs) t₀ ht₀_Ioo hcross honly
  have h_thm := generalizedResidueTheorem' U hU hU_convex S hS_in_U hS_discrete
    hS_closed S0 hS0_subset f_res hf_res_diff γ hγ_closed hγ_in_U hS_on_curve
    hSimple_res hf_ext_res hPV_singular
  obtain ⟨h_exists, h_value⟩ := h_thm
  obtain ⟨L, hL⟩ := h_exists
  have h_limit_eq : L = 2 * Real.pi * I * ∑ s ∈ S0,
      generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s := by
    have hL_eq : L = cauchyPrincipalValueOn S0 f_res γ.toFun γ.a γ.b :=
      (hL.limUnder_eq).symm
    rw [hL_eq, h_value]
    congr 1; apply Finset.sum_congr rfl
    intro s hs; rw [h_res_eq s hs]
  rw [← h_limit_eq]
  exact hL

/-- **Theorem 3.3 (Hungerbühler-Wasem)**: Generalized residue theorem with the paper's
actual conditions (A') and (B), matching arXiv:1808.00997v2 Theorem 3.3.

Uses `Tendsto` formulation and does not require C² regularity at crossings.

- **Condition (A')**: At each crossing point where `f` has a pole of order `n`,
  the curve is flat of order `n` (Definition 3.2). Uses `SatisfiesConditionA'`
  with `poleOrderAt f` to capture the variable-order flatness requirement.
- **Condition (B)**: At each crossing point, the angle `α` is a rational multiple
  of `π`, and each nonzero Laurent coefficient `a_{-k}` with `k ≥ 2` satisfies
  `(k-1)·α ∈ 2πℤ`.

These conditions ensure that the PV contributions from higher-order polar terms
vanish, so the full PV integral reduces to the simple-pole case.

For simple poles, `poleOrderAt f s = 1` and `IsFlatOfOrder γ t₀ 1` is automatic
(see `isFlatOfOrder_one`), so condition (A') reduces to condition (A). -/
theorem generalizedResidueTheorem_3_3
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S)
    (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0)
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t)
      (𝓝[>] 0) (𝓝 (2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s)) :=
  generalizedResidueTheorem_higher_order_tendsto S0 f γ
    (conditionsAB_imply_higherOrderCancel U hU hU_convex S0 f hf γ hγ_closed hγ_in_U
      hMero hCondA hCondB hγ_meas h_no_endpt_cross h_unique_cross
      (fun s hs => hS_in_U s (hS0_subset s hs)))
    (pv_res_tendsto_of_immersion U hU hU_convex S hS_in_U hS_discrete hS_closed
      S0 hS0_subset f γ hγ_closed hγ_in_U hS_on_curve hγ_meas h_no_endpt_cross
      h_unique_cross)

end GeneralizedResidueTheory
