/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_WindingWeights
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Core

/-!
# On-Curve PV Provider

Proves that Cauchy principal value integrals of `(z - s)⁻¹` exist along the
parameterized fundamental domain boundary `fdBoundary_H H` for any on-curve point `s`.

## Main Results

* `fdBoundary_H_cpv_exists_of_onCurve` -- For any `H > sqrt(3)/2` and any `s` on the curve,
  `CauchyPrincipalValueExists' (fun z => (z - s)^{-1}) (fdBoundary_H H) 0 5 s`.
* `fdBoundary_H_OnCurvePVProvider` -- The `OnCurvePVProvider` instance.

## Strategy

1. Elliptic points (rho, rho+1, i): Bridge existing `pv_integral_at_*_tendsto` results.
2. General crossing points: Use `pv_limit_via_dyadic` on smooth sub-intervals,
   then combine with avoidance on the rest via `cpv_exists_of_sub_interval`.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-! ## Section 1: Bridge Infrastructure -/

private lemma indicator_integrand_deriv_eq (γ : ℝ → ℂ) (c : ℂ) (ε : ℝ) (t : ℝ) :
    (if ‖γ t - c‖ > ε then (γ t - c)⁻¹ * deriv (fun s => γ s - c) t else 0) =
    (if ‖γ t - c‖ > ε then (γ t - c)⁻¹ * deriv γ t else 0) := by
  split_ifs with h
  · congr 1; exact deriv_sub_const c
  · rfl

private lemma cpv_exists_from_shifted_tendsto (γ : ℝ → ℂ) (a b : ℝ) (c : ℂ) (L : ℂ)
    (h : Tendsto (fun ε => ∫ t in a..b, if ‖γ t - c‖ > ε
      then (γ t - c)⁻¹ * deriv (fun s => γ s - c) t else 0) (𝓝[>] 0) (𝓝 L)) :
    CauchyPrincipalValueExists' (fun z => (z - c)⁻¹) γ a b c := by
  refine ⟨L, h.congr (fun ε => intervalIntegral.integral_congr (fun t _ => ?_))⟩
  simp only [deriv_sub_const]

/-! ## Section 2: Elliptic Point CPV -/

/-- CPV of `(z - rho)^{-1}` exists along `fdBoundary_H H` for `H > sqrt(3)/2`. -/
theorem cpv_exists_at_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    CauchyPrincipalValueExists' (fun z => (z - ellipticPoint_rho)⁻¹)
      (fdBoundary_H H) 0 5 ellipticPoint_rho :=
  cpv_exists_from_shifted_tendsto (fdBoundary_H H) 0 5 _ _ (pv_integral_at_rho_tendsto H hH)

/-- CPV of `(z - rho')^{-1}` exists along `fdBoundary_H H` for `H > sqrt(3)/2`. -/
theorem cpv_exists_at_rho_plus_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    CauchyPrincipalValueExists' (fun z => (z - ellipticPoint_rho_plus_one)⁻¹)
      (fdBoundary_H H) 0 5 ellipticPoint_rho_plus_one :=
  cpv_exists_from_shifted_tendsto (fdBoundary_H H) 0 5 _ _
    (pv_integral_at_rho_plus_one_tendsto H hH)

/-- CPV of `(z - I)^{-1}` exists along `fdBoundary_H H` for `H > 1`. -/
theorem cpv_exists_at_i (H : ℝ) (hH : 1 < H) :
    CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
      (fdBoundary_H H) 0 5 I :=
  cpv_exists_from_shifted_tendsto (fdBoundary_H H) 0 5 _ _ (pv_integral_at_i_tendsto H hH)

/-! ## Section 3: Crossing Cauchy Lemmas -/

/-- The crossing Cauchy hypothesis at rho. -/
private lemma crossing_cauchy_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    Cauchy (Filter.map (fun eps =>
      ∫ t in (0:ℝ)..5, if eps < ‖fdBoundary_H H t - ellipticPoint_rho‖
        then (fdBoundary_H H t - ellipticPoint_rho)⁻¹ * deriv (fdBoundary_H H) t
        else 0) (𝓝[>] 0)) := by
  obtain ⟨L, hL⟩ := cpv_exists_at_rho H hH
  exact hL.cauchy_map

/-- The crossing Cauchy hypothesis at rho+1. -/
private lemma crossing_cauchy_rho_plus_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    Cauchy (Filter.map (fun eps =>
      ∫ t in (0:ℝ)..5, if eps < ‖fdBoundary_H H t - ellipticPoint_rho_plus_one‖
        then (fdBoundary_H H t - ellipticPoint_rho_plus_one)⁻¹ * deriv (fdBoundary_H H) t
        else 0) (𝓝[>] 0)) := by
  obtain ⟨L, hL⟩ := cpv_exists_at_rho_plus_one H hH
  exact hL.cauchy_map

/-- The crossing Cauchy hypothesis at I (needs H > 1). -/
private lemma crossing_cauchy_i (H : ℝ) (hH : 1 < H) :
    Cauchy (Filter.map (fun eps =>
      ∫ t in (0:ℝ)..5, if eps < ‖fdBoundary_H H t - I‖
        then (fdBoundary_H H t - I)⁻¹ * deriv (fdBoundary_H H) t
        else 0) (𝓝[>] 0)) := by
  obtain ⟨L, hL⟩ := cpv_exists_at_i H hH
  exact hL.cauchy_map

/-! ## Section 4: Segment Geometry Helpers -/

private lemma fdBoundary_H_seg1_re' (H : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (fdBoundary_H H t).re = 1/2 := by
  rw [fdBoundary_H_eq_seg1_H ht1]
  simp [fdBoundary_seg1_H, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im]

private lemma fdBoundary_H_seg4_re' (H : ℝ) {t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) :
    (fdBoundary_H H t).re = -1/2 := by
  rw [fdBoundary_H_eq_seg4_H (by linarith : ¬(t ≤ 1)) (by linarith : ¬(t ≤ 2))
    (by linarith : ¬(t ≤ 3)) ht4]
  simp [fdBoundary_seg4_H, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.div_ofNat]

private lemma fdBoundary_H_seg5_re' (H : ℝ) {t : ℝ} (ht4 : 4 < t) (ht5 : t ≤ 5) :
    (fdBoundary_H H t).re = t - 9/2 := by
  rw [fdBoundary_H_eq_seg5_H (by linarith : ¬(t ≤ 1)) (by linarith : ¬(t ≤ 2))
    (by linarith : ¬(t ≤ 3)) (by linarith : ¬(t ≤ 4))]
  simp [fdBoundary_seg5_H, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]

private lemma fdBoundary_H_seg5_im' (H : ℝ) {t : ℝ} (ht4 : 4 < t) (ht5 : t ≤ 5) :
    (fdBoundary_H H t).im = H := by
  rw [fdBoundary_H_eq_seg5_H (by linarith : ¬(t ≤ 1)) (by linarith : ¬(t ≤ 2))
    (by linarith : ¬(t ≤ 3)) (by linarith : ¬(t ≤ 4))]
  simp [fdBoundary_seg5_H, Complex.add_im, Complex.sub_im, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]

private lemma fdBoundary_H_arc_re' (H : ℝ) {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    (fdBoundary_H H t).re = Real.cos (Real.pi * (1 + t) / 6) := by
  rw [fdBoundary_H_eq_arc ht1 ht3, Complex.exp_ofReal_mul_I_re]

private lemma fdBoundary_H_arc_im' (H : ℝ) {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    (fdBoundary_H H t).im = Real.sin (Real.pi * (1 + t) / 6) := by
  rw [fdBoundary_H_eq_arc ht1 ht3, Complex.exp_ofReal_mul_I_im]

/-! ## Section 5: Arc Injectivity -/

private lemma arc_angle_injective {t t' : ℝ}
    (ht : t ∈ Set.Ioo (1:ℝ) 3) (ht' : t' ∈ Set.Ioo (1:ℝ) 3)
    (h_eq : Complex.exp (↑(Real.pi * (1 + t) / 6) * I) =
            Complex.exp (↑(Real.pi * (1 + t') / 6) * I)) :
    t = t' := by
  rw [Complex.exp_eq_exp_iff_exists_int] at h_eq
  obtain ⟨n, hn⟩ := h_eq
  -- hn : ↑(π*(1+t)/6) * I = ↑(π*(1+t')/6) * I + ↑n * (2 * ↑π * I)
  -- Rearrange: (π*(1+t)/6 - π*(1+t')/6) * I = n * (2π) * I
  have h_vals : Real.pi * (1 + t) / 6 - Real.pi * (1 + t') / 6 = 2 * Real.pi * ↑n := by
    have : (↑(Real.pi * (1 + t) / 6) : ℂ) * I - ↑(Real.pi * (1 + t') / 6) * I =
        ↑(2 * Real.pi * ↑n) * I := by
      rw [hn]; push_cast; ring
    have h2 : (↑(Real.pi * (1 + t) / 6 - Real.pi * (1 + t') / 6) : ℂ) * I =
        ↑(2 * Real.pi * ↑n) * I := by
      rw [show (↑(Real.pi * (1 + t) / 6 - Real.pi * (1 + t') / 6) : ℂ) * I =
          ↑(Real.pi * (1 + t) / 6) * I - ↑(Real.pi * (1 + t') / 6) * I from by push_cast; ring]
      exact this
    exact_mod_cast Complex.ofReal_injective (mul_right_cancel₀ I_ne_zero h2)
  have h_diff_small : |Real.pi * (1 + t) / 6 - Real.pi * (1 + t') / 6| < Real.pi := by
    rw [abs_lt]; constructor <;> nlinarith [Real.pi_pos, ht.1, ht.2, ht'.1, ht'.2]
  have hn0 : n = 0 := by
    by_contra h_ne
    have h1 : |(n : ℝ)| ≥ 1 := by exact_mod_cast Int.one_le_abs h_ne
    have h2 : 2 * Real.pi ≤ |2 * Real.pi * (n : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      exact le_mul_of_one_le_right (by positivity) h1
    have h3 : |2 * Real.pi * (n : ℝ)| < Real.pi := by rwa [h_vals] at h_diff_small
    linarith [Real.pi_pos]
  rw [hn0] at h_vals; simp at h_vals
  -- h_vals : π * (1+t) / 6 = π * (1+t') / 6
  nlinarith [Real.pi_ne_zero, Real.pi_pos]

/-! ## Section 6: CPV on Smooth Sub-intervals -/

private lemma cpv_exists_on_smooth_subinterval (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {t₀ : ℝ} {a' b' : ℝ} (s : ℂ)
    (hat₀ : t₀ ∈ Set.Ioo a' b')
    (hs : fdBoundary_H H t₀ = s)
    (hγ_C2 : ContDiffAt ℝ 2 (fdBoundary_H H) t₀)
    (hL_ne : deriv (fdBoundary_H H) t₀ ≠ 0)
    (hγ_cont_deriv : ContinuousOn (deriv (fdBoundary_H H)) (Set.Icc a' b'))
    (h_inj : ∀ t ∈ Set.Icc a' b', fdBoundary_H H t = fdBoundary_H H t₀ → t = t₀) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) a' b' s := by
  have hγ_meas : Measurable (fdBoundary_H H) := (fdBoundary_H_continuous H).measurable
  have hγ_cont : ContinuousOn (fdBoundary_H H) (Set.Icc a' b') :=
    (fdBoundary_H_continuous H).continuousOn
  obtain ⟨limit, h_limit⟩ := pv_limit_via_dyadic hat₀ hL_ne hγ_C2
    (show deriv (fdBoundary_H H) t₀ = deriv (fdBoundary_H H) t₀ from rfl)
    hγ_cont_deriv hγ_meas hγ_cont h_inj
  exact ⟨limit, h_limit.congr (fun ε => intervalIntegral.integral_congr
    (fun t _ => by rw [hs]))⟩

/-! ## Section 7: CPV Avoidance -/

/-- When the curve avoids `z₀` on `[a, b]`, CPV trivially exists (integral eventually constant). -/
private lemma cpv_avoidance (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (h_cont : ContinuousOn γ (Set.Icc a b)) (hab : a ≤ b)
    (h_avoid : ∀ t ∈ Set.Icc a b, γ t ≠ z₀) :
    CauchyPrincipalValueExists' f γ a b z₀ := by
  -- The continuous function t ↦ ‖γ(t) - z₀‖ attains min on compact [a,b]
  have h_cont_norm : ContinuousOn (fun t => ‖γ t - z₀‖) (Set.Icc a b) :=
    (h_cont.sub continuousOn_const).norm
  obtain ⟨t₀, ht₀, ht₀_min⟩ := isCompact_Icc.exists_isMinOn
    ⟨a, Set.left_mem_Icc.mpr hab⟩ h_cont_norm
  have hδ : 0 < ‖γ t₀ - z₀‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoid t₀ ht₀))
  -- For ε < δ, the indicator is always 1, so the integral is constant
  set C := ∫ t in a..b, f (γ t) * deriv γ t
  refine ⟨C, ?_⟩
  apply Tendsto.congr' _ tendsto_const_nhds
  rw [Filter.EventuallyEq, Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioo 0 ‖γ t₀ - z₀‖, Ioo_mem_nhdsGT hδ, fun ε hε => ?_⟩
  simp only [Set.mem_Ioo] at hε
  exact intervalIntegral.integral_congr (fun t ht => by
    rw [Set.uIcc_of_le hab] at ht
    exact (if_pos (lt_of_lt_of_le hε.2 (ht₀_min ht))).symm)

/-! ## Section 8: CPV Concatenation -/

/-- CPV on adjacent intervals can be concatenated (when `a ≤ b ≤ c`). -/
private lemma cpv_concat (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b c : ℝ) (z₀ : ℂ)
    (h_ab : CauchyPrincipalValueExists' f γ a b z₀)
    (h_bc : CauchyPrincipalValueExists' f γ b c z₀)
    (hab : a ≤ b) (hbc : b ≤ c)
    (h_int : ∀ ε > 0, IntervalIntegrable
        (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0) volume a c) :
    CauchyPrincipalValueExists' f γ a c z₀ := by
  obtain ⟨L₁, hL₁⟩ := h_ab
  obtain ⟨L₂, hL₂⟩ := h_bc
  refine ⟨L₁ + L₂, ?_⟩
  have h_sum := hL₁.add hL₂
  apply Tendsto.congr' _ h_sum
  rw [Filter.EventuallyEq]
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Set.mem_Ioi] at hε
  have hII := h_int ε hε
  have hac := hab.trans hbc
  have hII_ab := hII.mono_set (by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hac]; exact Set.Icc_subset_Icc_right hbc)
  have hII_bc := hII.mono_set (by
    rw [Set.uIcc_of_le hbc, Set.uIcc_of_le hac]; exact Set.Icc_subset_Icc_left hab)
  exact intervalIntegral.integral_add_adjacent_intervals hII_ab hII_bc

/-! ## Section 9: Derivative ContinuousOn Off Partition -/

/-- `deriv (fdBoundary_H H)` is continuous on `Icc 0 5 \ fdBoundary_H_partition`. -/
private lemma fdBoundary_H_deriv_continuousOn_off_partition (H : ℝ) :
    ContinuousOn (deriv (fdBoundary_H H)) (Set.Icc 0 5 \ ↑fdBoundary_H_partition) := by
  intro t ht
  have ht_icc := ht.1
  have ht_part : t ∉ (fdBoundary_H_partition : Set ℝ) := ht.2
  simp only [fdBoundary_H_partition, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_part
  obtain ⟨h1, h3, h4⟩ := ht_part
  -- Case split on which segment t belongs to
  by_cases ht0 : t = 0
  · subst ht0
    -- At t = 0: deriv equals constant on (-∞, 1), hence continuous
    have hev : deriv (fdBoundary_H H) =ᶠ[𝓝 (0:ℝ)]
        (fun _ => -(↑(H - Real.sqrt 3 / 2) : ℂ) * I) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Iio 1, Iio_mem_nhds (by norm_num : (0:ℝ) < 1),
        fun t ht => (fdBoundary_H_hasDerivAt_seg1 H ht).deriv⟩
    exact (continuousAt_const.congr hev.symm).continuousWithinAt
  by_cases ht5 : t = 5
  · subst ht5
    -- At t = 5: deriv equals constant 1 on (4, +∞), hence continuous
    have hev : deriv (fdBoundary_H H) =ᶠ[𝓝 (5:ℝ)] (fun _ => (1:ℂ)) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioi 4, Ioi_mem_nhds (by norm_num : (4:ℝ) < 5),
        fun t ht => (fdBoundary_H_hasDerivAt_seg5 H ht).deriv⟩
    exact (continuousAt_const.congr hev.symm).continuousWithinAt
  -- For t ∈ (0, 5) \ {1, 3, 4}: use segment-wise ContinuousOn
  have ht_ioo : t ∈ Set.Ioo (0:ℝ) 5 :=
    ⟨lt_of_le_of_ne ht_icc.1 (Ne.symm ht0), lt_of_le_of_ne ht_icc.2 ht5⟩
  by_cases ht1 : t < 1
  · exact ((fdBoundary_H_deriv_continuousOn_Ioo_01 H).continuousAt
      (Ioo_mem_nhds ht_ioo.1 ht1)).continuousWithinAt
  · push_neg at ht1
    by_cases ht3' : t < 3
    · exact ((fdBoundary_H_deriv_continuousOn_Ioo_13 H).continuousAt
        (Ioo_mem_nhds (lt_of_le_of_ne ht1 (fun h => h1 h.symm)) ht3')).continuousWithinAt
    · push_neg at ht3'
      by_cases ht4' : t < 4
      · exact ((fdBoundary_H_deriv_continuousOn_Ioo_34 H).continuousAt
          (Ioo_mem_nhds (lt_of_le_of_ne ht3' (fun h => h3 h.symm)) ht4')).continuousWithinAt
      · push_neg at ht4'
        exact ((fdBoundary_H_deriv_continuousOn_Ioo_45 H).continuousAt
          (Ioo_mem_nhds (lt_of_le_of_ne ht4' (fun h => h4 h.symm)) ht_ioo.2)).continuousWithinAt

/-! ## Section 10: IntervalIntegrable of Cutout Integrand -/

private lemma fdBoundary_H_cutout_cont_inv (s : ℂ) (H : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ContinuousOn (fun z => (z - s)⁻¹)
      ((fdBoundary_H H) '' Set.Icc 0 5 \ Metric.ball s ε) := by
  apply ContinuousOn.inv₀
  · exact continuousOn_id.sub continuousOn_const
  · intro z ⟨_, hz_ball⟩
    simp only [Metric.mem_ball, not_lt] at hz_ball
    exact sub_ne_zero.mpr (fun heq => by subst heq; simp [dist_self] at hz_ball; linarith)

set_option maxHeartbeats 4000000 in
private lemma fdBoundary_H_cutout_bound (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    (s : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (0:ℝ) 5,
      ‖(fun t => if ε < ‖fdBoundary_H H t - s‖ then (fdBoundary_H H t - s)⁻¹ *
        deriv (fdBoundary_H H) t else 0) t‖ ≤ C := by
  obtain ⟨M, hM_pos, hM_bound⟩ := fdBoundary_H_deriv_bound_ex hH
  refine ⟨ε⁻¹ * M, fun t _ht => ?_⟩
  simp only
  split_ifs with h
  · calc ‖(fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t‖
        = ‖(fdBoundary_H H t - s)⁻¹‖ * ‖deriv (fdBoundary_H H) t‖ := norm_mul _ _
      _ ≤ ε⁻¹ * M := by
        apply mul_le_mul
        · rw [norm_inv]
          exact inv_anti₀ hε (le_of_lt h)
        · by_cases htp : t ∈ fdBoundary_H_partition
          · simp only [fdBoundary_H_partition, Finset.mem_insert, Finset.mem_singleton] at htp
            have : ¬DifferentiableAt ℝ (fdBoundary_H H) t := by
              rcases htp with rfl | rfl | rfl
              · exact fdBoundary_H_not_differentiableAt_1 hH
              · exact fdBoundary_H_not_differentiableAt_3 hH
              · exact fdBoundary_H_not_differentiableAt_4 hH
            rw [deriv_zero_of_not_differentiableAt this]; simp [le_of_lt hM_pos]
          · exact hM_bound t htp
        · exact norm_nonneg _
        · exact le_of_lt (inv_pos_of_pos hε)
  · simp only [norm_zero]; exact mul_nonneg (le_of_lt (inv_pos_of_pos hε)) (le_of_lt hM_pos)

set_option maxHeartbeats 4000000 in
private lemma fdBoundary_H_cutout_meas (H : ℝ) (s : ℂ) (ε : ℝ) (hε : 0 < ε) :
    AEStronglyMeasurable
      (fun t => if ε < ‖fdBoundary_H H t - s‖ then
        (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0)
      (volume.restrict (Set.Icc 0 5)) :=
  aEStronglyMeasurable_pv_integrand_piecewiseC1
    (f := fun z => (z - s)⁻¹) (γ := fdBoundary_H H) (a := 0) (b := 5)
    (z₀ := s) (ε := ε) (P := fdBoundary_H_partition)
    (fdBoundary_H_cutout_cont_inv s H ε hε)
    (fdBoundary_H_continuous H).continuousOn
    (fdBoundary_H_deriv_continuousOn_off_partition H)

/-- The cutout integrand for `(z - s)⁻¹` along `fdBoundary_H H` is interval-integrable
on `[0, 5]`. Uses ae-measurability from piecewise C1 structure + uniform bound. -/
private lemma fdBoundary_H_cutout_ii (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    (s : ℂ) (ε : ℝ) (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => if ε < ‖fdBoundary_H H t - s‖ then (fdBoundary_H H t - s)⁻¹ *
        deriv (fdBoundary_H H) t else 0)
      volume 0 5 := by
  obtain ⟨C, hC⟩ := fdBoundary_H_cutout_bound H hH s ε hε
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 5)]
  exact (integrableOn_of_bounded_aeMeasurable C (fdBoundary_H_cutout_meas H s ε hε) hC).mono_set
    Set.Ioc_subset_Icc_self

/-! ## Section 11: Sub-interval CPV Extension to [0, 5] -/

/-- If CPV exists on a sub-interval `[a', b'] ⊆ [0, 5]` containing the sole crossing point,
and the curve avoids `s` on `[0, a']` and `[b', 5]`, then CPV exists on `[0, 5]`.
This combines `cpv_avoidance` on the complement and `cpv_concat` to glue. -/
private lemma cpv_extend_to_full_interval (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    (s : ℂ) (a' b' : ℝ) (ha' : 0 ≤ a') (hb' : b' ≤ 5) (hab' : a' < b')
    (h_sub : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) a' b' s)
    (h_avoid_left : ∀ t ∈ Set.Icc 0 a', fdBoundary_H H t ≠ s)
    (h_avoid_right : ∀ t ∈ Set.Icc b' 5, fdBoundary_H H t ≠ s) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s := by
  have hγ_cont : ContinuousOn (fdBoundary_H H) (Set.Icc 0 5) :=
    (fdBoundary_H_continuous H).continuousOn
  -- CPV on [0, a'] by avoidance
  have h_cpv_left : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) 0 a' s :=
    cpv_avoidance _ _ _ _ _ (hγ_cont.mono (Set.Icc_subset_Icc_right (le_trans (le_of_lt hab') hb')))
      ha' h_avoid_left
  -- CPV on [b', 5] by avoidance
  have h_cpv_right : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) b' 5 s :=
    cpv_avoidance _ _ _ _ _ (hγ_cont.mono (Set.Icc_subset_Icc_left (le_trans ha' (le_of_lt hab'))))
      hb' h_avoid_right
  -- Concat: [0, a'] + [a', b'] → [0, b']
  have h_cpv_0b' : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) 0 b' s := by
    apply cpv_concat _ _ 0 a' b' s h_cpv_left h_sub ha' (le_of_lt hab')
    intro ε hε
    exact (fdBoundary_H_cutout_ii H hH s ε hε).mono_set (by
      rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ b'), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc_right hb')
  -- Concat: [0, b'] + [b', 5] → [0, 5]
  apply cpv_concat _ _ 0 b' 5 s h_cpv_0b' h_cpv_right (le_trans ha' (le_of_lt hab')) hb'
  intro ε hε
  exact fdBoundary_H_cutout_ii H hH s ε hε

/-! ## Section 11.5: Corner and Endpoint CPV -/

set_option maxHeartbeats 32000000 in
private lemma cpv_at_endpoint (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    CauchyPrincipalValueExists' (fun z => (z - ((1/2 : ℂ) + ↑H * I))⁻¹)
      (fdBoundary_H H) 0 5 ((1/2 : ℂ) + ↑H * I) := by
  set s := (1/2 : ℂ) + ↑H * I with hs_def
  set c := H - Real.sqrt 3 / 2 with hc_def
  have hc : 0 < c := sub_pos.mpr hH
  have hc_ne : c ≠ 0 := hc.ne'
  -- γ avoids s on [1, 4]: arc has ‖γ‖ = 1 < ‖s‖, seg4 has re = -1/2 ≠ 1/2 = re(s)
  have h_avoid_14 : ∀ t ∈ Set.Icc (1:ℝ) 4, fdBoundary_H H t ≠ s := by
    intro t ht habs
    rw [Set.mem_Icc] at ht
    by_cases ht3 : t ≤ 3
    · by_cases ht1 : t = 1
      · rw [ht1, fdBoundary_H_at_one, fdBoundary_at_one] at habs
        have him := congr_arg Complex.im habs
        simp [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one',
          UpperHalfPlane.coe_mk_subtype, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, hs_def] at him
        linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 from by norm_num)]
      · have ht1' : 1 < t := lt_of_le_of_ne ht.1 (Ne.symm ht1)
        have h_norm : ‖fdBoundary_H H t‖ = 1 :=
          fdBoundary_H_eq_arc ht1' (lt_of_le_of_ne ht3 (by
            intro h; rw [h, fdBoundary_H_at_three, fdBoundary_at_three] at habs
            have him := congr_arg Complex.im habs
            simp [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype,
              Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
              Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.div_ofNat, hs_def] at him
            linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 from by norm_num)])) |>.symm ▸
          Complex.norm_exp_ofReal_mul_I _
        rw [habs] at h_norm
        have : 1 < ‖s‖ := by
          have h_nsq : 1 < Complex.normSq s := by
            simp only [hs_def, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
              Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
              Complex.add_im, Complex.mul_im, Complex.one_re, Complex.one_im,
              Complex.div_ofNat]
            have hH0 : 0 < H := by
              linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 from by norm_num)]
            nlinarith [mul_lt_mul hH hH.le (by positivity : (0:ℝ) < Real.sqrt 3 / 2) hH0.le,
                       Real.mul_self_sqrt (show (0:ℝ) ≤ 3 from by norm_num)]
          calc (1:ℝ) = Real.sqrt 1 := by simp
            _ < Real.sqrt (Complex.normSq s) := Real.sqrt_lt_sqrt (by norm_num) h_nsq
            _ = ‖s‖ := rfl
        linarith
    · push_neg at ht3
      have h_re_t := fdBoundary_H_seg4_re' H ht3 ht.2
      rw [habs] at h_re_t
      simp [hs_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im] at h_re_t
      norm_num at h_re_t
  -- Minimum distance δ > 0 on [1, 4]
  have h_cont_norm : ContinuousOn (fun t => ‖fdBoundary_H H t - s‖)
      (Set.Icc (1:ℝ) 4) :=
    ((fdBoundary_H_continuous H).continuousOn.sub continuousOn_const).norm.mono
      (Set.Icc_subset_Icc (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (4:ℝ) ≤ 5))
  have h_pos_norm : ∀ t ∈ Set.Icc (1:ℝ) 4, 0 < ‖fdBoundary_H H t - s‖ :=
    fun t ht => norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoid_14 t ht))
  obtain ⟨δ, hδ_pos, hδ_bound⟩ : ∃ δ > 0, ∀ t ∈ Set.Icc (1:ℝ) 4,
      δ ≤ ‖fdBoundary_H H t - s‖ :=
    isCompact_Icc.exists_forall_le' h_cont_norm h_pos_norm
  -- Set up eventually-constant argument
  set ε₀ := min c (min 1 δ) with hε₀_def
  have hε₀ : 0 < ε₀ := lt_min hc (lt_min one_pos hδ_pos)
  set F := fun ε => ∫ t in (0:ℝ)..5,
    if ε < ‖fdBoundary_H H t - s‖ then (fdBoundary_H H t - s)⁻¹ *
      deriv (fdBoundary_H H) t else 0
  -- F is eventually constant: F(η) = ↑(Real.log c) + ∫_1^4 g(t) for all small η
  set C := ∫ t in (1:ℝ)..4, (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t
  suffices h_ev : ∀ ε, 0 < ε → ε < ε₀ → F ε = F (ε₀ / 2) from
    ⟨F (ε₀ / 2), tendsto_const_nhds.congr'
      (Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioo 0 ε₀, Ioo_mem_nhdsGT hε₀,
        fun ε ⟨hε_pos, hε_lt⟩ => (h_ev ε hε_pos hε_lt).symm⟩)⟩
  intro ε hε hε_lt
  have hε_c : ε < c := lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hε_1 : ε < 1 := by have := min_le_right c (min 1 δ); have := min_le_left 1 δ; linarith
  have hε_δ : ε < δ := by have := min_le_right c (min 1 δ); have := min_le_right 1 δ; linarith
  have hε₀2_pos : 0 < ε₀ / 2 := by positivity
  have hε₀2_c : ε₀ / 2 < c := by have := min_le_left c (min 1 δ); linarith
  have hε₀2_1 : ε₀ / 2 < 1 := by
    have := min_le_right c (min 1 δ); have := min_le_left 1 δ; linarith
  have hε₀2_δ : ε₀ / 2 < δ := by
    have := min_le_right c (min 1 δ); have := min_le_right 1 δ; linarith
  suffices h_formula : ∀ η, 0 < η → η < c → η < 1 → η < δ →
      F η = ↑(Real.log c) + C by
    rw [h_formula ε hε hε_c hε_1 hε_δ, h_formula (ε₀/2) hε₀2_pos hε₀2_c hε₀2_1 hε₀2_δ]
  -- Prove the formula: F(η) = ↑(Real.log c) + C
  intro η hη hη_c hη_1 hη_δ
  have hη_div_c_pos : 0 < η / c := div_pos hη hc
  have hη_div_c_lt_1 : η / c < 1 := (div_lt_one hc).mpr hη_c
  -- On seg1 (t ∈ [0,1]): γ(t) - s = ↑((-t)*c) * I
  have h_diff_seg1 : ∀ t, 0 ≤ t → t ≤ 1 →
      fdBoundary_H H t - s = ↑((-t) * c) * I := by
    intro t ht0 ht1
    rw [fdBoundary_H_eq_seg1_H ht1, hs_def]
    simp only [fdBoundary_seg1_H, hc_def]
    push_cast; ring
  -- On seg5 (t ∈ (4,5]): γ(t) - s = ↑(t-5)
  have h_diff_seg5 : ∀ t, 4 < t →
      fdBoundary_H H t - s = ↑(t - 5) := by
    intro t ht4
    rw [fdBoundary_H_eq_seg5_H (by linarith : ¬(t ≤ 1)) (by linarith : ¬(t ≤ 2))
      (by linarith : ¬(t ≤ 3)) (by linarith : ¬(t ≤ 4)), hs_def]
    simp only [fdBoundary_seg5_H]
    push_cast; ring
  -- Norms
  have h_norm_seg1 : ∀ t, 0 ≤ t → t ≤ 1 →
      ‖fdBoundary_H H t - s‖ = t * c := by
    intro t ht0 ht1
    rw [h_diff_seg1 t ht0 ht1, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_nonpos (by nlinarith : (-t) * c ≤ 0)]
    ring
  have h_norm_seg5 : ∀ t, 4 < t → t ≤ 5 →
      ‖fdBoundary_H H t - s‖ = 5 - t := by
    intro t ht4 ht5
    rw [h_diff_seg5 t ht4, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  -- Integrand on seg1 = (↑t)⁻¹
  have h_integrand_seg1 : ∀ t, 0 < t → t < 1 →
      (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t = (↑t : ℂ)⁻¹ := by
    intro t ht0 ht1
    rw [h_diff_seg1 t ht0.le ht1.le, (fdBoundary_H_hasDerivAt_seg1 H ht1).deriv]
    rw [show (↑(H - Real.sqrt 3 / 2) : ℂ) = (↑c : ℂ) from rfl]
    -- (↑((-t)*c) * I)⁻¹ * (-(↑c) * I) = (↑t)⁻¹
    have ht_ne : (↑t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht0)
    have hcC_ne : (↑c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc_ne
    rw [Complex.ofReal_mul, Complex.ofReal_neg]; field_simp
  -- Integrand on seg5 = (↑(t-5))⁻¹
  have h_integrand_seg5 : ∀ t, 4 < t →
      (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t = (↑(t - 5) : ℂ)⁻¹ := by
    intro t ht4
    rw [h_diff_seg5 t ht4, (fdBoundary_H_hasDerivAt_seg5 H ht4).deriv, mul_one]
  -- Helper: integrability on sub-intervals
  have hii := fdBoundary_H_cutout_ii H hH s η hη
  -- Split F(η) = ∫₀¹ + ∫₁⁵
  have h_01_15 : (∫ t in (0:ℝ)..5, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) =
    (∫ t in (0:ℝ)..1, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) +
    (∫ t in (1:ℝ)..5, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hii.mono_set (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1),
        Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]; exact Set.Icc_subset_Icc_right (by norm_num)))
      (hii.mono_set (by rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 5),
        Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]; exact Set.Icc_subset_Icc_left (by norm_num)))).symm
  -- Split ∫₁⁵ = ∫₁⁴ + ∫₄⁵
  have h_14_45 : (∫ t in (1:ℝ)..5, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) =
    (∫ t in (1:ℝ)..4, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) +
    (∫ t in (4:ℝ)..5, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hii.mono_set (by rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 4),
        Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]; exact Set.Icc_subset_Icc (by norm_num) (by norm_num)))
      (hii.mono_set (by rw [Set.uIcc_of_le (by norm_num : (4:ℝ) ≤ 5),
        Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]; exact Set.Icc_subset_Icc_left (by norm_num)))).symm
  have h_split : F η = (∫ t in (0:ℝ)..1, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) +
    (∫ t in (1:ℝ)..4, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) +
    (∫ t in (4:ℝ)..5, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) := by
    show (∫ t in (0:ℝ)..5, _) = _
    rw [h_01_15, h_14_45, add_assoc]
  -- Middle integral [1, 4]: indicator always on (η < δ ≤ ‖γ(t)-s‖)
  have h_I14 : (∫ t in (1:ℝ)..4, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) = C := by
    apply intervalIntegral.integral_congr
    intro t ht; rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 4)] at ht
    dsimp only; rw [if_pos (lt_of_lt_of_le hη_δ (hδ_bound t ht))]
  -- Integral on [0, 1]: split [0, η/c] (off) + [η/c, 1] (on)
  have h_I01 : (∫ t in (0:ℝ)..1, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) =
    ∫ t in (η / c)..1, (↑t : ℂ)⁻¹ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hii.mono_set (by rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ η / c),
        Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]; exact Set.Icc_subset_Icc_right (by linarith)))
      (hii.mono_set (by rw [Set.uIcc_of_le (by linarith : η / c ≤ 1),
        Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]; exact Set.Icc_subset_Icc (by linarith) (by norm_num)))]
    -- [0, η/c]: indicator off
    have h_zero : (∫ t in (0:ℝ)..(η / c),
        if η < ‖fdBoundary_H H t - s‖
        then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) = 0 := by
      have : (∫ t in (0:ℝ)..(η / c), if η < ‖fdBoundary_H H t - s‖
          then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) =
          ∫ _ in (0:ℝ)..(η / c), (0 : ℂ) :=
        intervalIntegral.integral_congr (fun t ht => by
          rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ η / c)] at ht
          rw [if_neg]; push_neg
          rw [h_norm_seg1 t ht.1 (by linarith [ht.2])]
          calc t * c ≤ (η / c) * c := mul_le_mul_of_nonneg_right ht.2 hc.le
            _ = η := by field_simp)
      rw [this, intervalIntegral.integral_zero]
    rw [h_zero, zero_add]
    -- [η/c, 1]: integrand = (↑t)⁻¹ (ae, excluding endpoints)
    refine intervalIntegral.integral_congr_ae' ?_ (by
      filter_upwards with t ht; exfalso; linarith [ht.1, ht.2])
    filter_upwards [compl_mem_ae_iff.mpr (show volume {η / c} = 0 by simp),
                    compl_mem_ae_iff.mpr (show volume {(1:ℝ)} = 0 by simp)]
      with t ht_ne_low ht_ne_high
    intro ht
    have ht_low : η / c < t := ht.1
    have ht_high : t < 1 := lt_of_le_of_ne ht.2
      (fun h => ht_ne_high (Set.mem_singleton_iff.mpr h))
    have ht_pos : 0 < t := lt_of_lt_of_le hη_div_c_pos ht_low.le
    rw [if_pos, h_integrand_seg1 t ht_pos ht_high]
    rw [h_norm_seg1 t ht_pos.le ht_high.le]
    calc η = (η / c) * c := by field_simp
      _ < t * c := mul_lt_mul_of_pos_right ht_low hc
  -- Integral on [4, 5]: split [4, 5-η] (on) + [5-η, 5] (off)
  have h_I45 : (∫ t in (4:ℝ)..5, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) =
    ∫ t in (4:ℝ)..(5 - η), (↑(t - 5) : ℂ)⁻¹ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hii.mono_set (by rw [Set.uIcc_of_le (by linarith : (4:ℝ) ≤ 5 - η),
        Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]; exact Set.Icc_subset_Icc (by norm_num) (by linarith)))
      (hii.mono_set (by rw [Set.uIcc_of_le (by linarith : 5 - η ≤ 5),
        Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]; exact Set.Icc_subset_Icc_left (by linarith)))]
    -- [5-η, 5]: indicator off
    have h_zero : (∫ t in (5 - η)..5,
        if η < ‖fdBoundary_H H t - s‖
        then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) = 0 := by
      have : (∫ t in (5 - η)..5, if η < ‖fdBoundary_H H t - s‖
          then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) =
          ∫ _ in (5 - η)..5, (0 : ℂ) :=
        intervalIntegral.integral_congr (fun t ht => by
          rw [Set.uIcc_of_le (by linarith : 5 - η ≤ 5)] at ht
          rw [if_neg]; push_neg
          by_cases ht5 : t = 5
          · rw [ht5, fdBoundary_H_at_five, hs_def, sub_self, norm_zero]; exact hη.le
          · have ht5' : t < 5 := lt_of_le_of_ne ht.2 ht5
            by_cases ht4 : t ≤ 4
            · linarith [ht.1]
            · push_neg at ht4
              rw [h_norm_seg5 t ht4 ht.2]; linarith [ht.1])
      rw [this, intervalIntegral.integral_zero]
    rw [h_zero, add_zero]
    -- [4, 5-η]: integrand = (↑(t-5))⁻¹ (ae, excluding endpoint)
    refine intervalIntegral.integral_congr_ae' ?_ (by
      filter_upwards with t ht; exfalso; linarith [ht.1, ht.2])
    filter_upwards [compl_mem_ae_iff.mpr (show volume {5 - η} = 0 by simp)]
      with t ht_ne_high
    intro ht
    have ht4 : 4 < t := ht.1
    have ht_strict : t < 5 - η := lt_of_le_of_ne ht.2
      (fun h => ht_ne_high (Set.mem_singleton_iff.mpr h))
    rw [if_pos, h_integrand_seg5 t ht4]
    rw [h_norm_seg5 t ht4 (by linarith)]; linarith
  -- Compute ∫_{η/c}^1 (↑t)⁻¹ using integral_inv_real_axis
  have h_int1 : ∫ t in (η / c)..1, (↑t : ℂ)⁻¹ =
      Complex.log ↑(1:ℝ) - Complex.log ↑(η / c) :=
    integral_inv_real_axis 1 (η / c) one_pos hη_div_c_pos hη_div_c_lt_1
  -- Compute ∫_4^{5-η} (↑(t-5))⁻¹ via substitution u = t - 5 and FTC
  have h_int2 : ∫ t in (4:ℝ)..(5 - η), (↑(t - 5) : ℂ)⁻¹ = ↑(Real.log η) := by
    simp_rw [← Complex.ofReal_inv]
    rw [intervalIntegral.integral_ofReal]
    congr 1
    have h5η : (4:ℝ) ≤ 5 - η := by linarith
    have hderiv : ∀ t ∈ Set.uIcc 4 (5 - η),
        HasDerivAt (fun t => Real.log (t - 5)) ((t - 5)⁻¹) t := by
      intro t ht; rw [Set.uIcc_of_le h5η] at ht
      have : t - 5 ≠ 0 := ne_of_lt (by linarith [ht.2])
      have h1 := (Real.hasDerivAt_log this).comp t ((hasDerivAt_id t).sub_const 5)
      simp only [Function.comp_def, mul_one] at h1; convert h1 using 1
    have hint : IntervalIntegrable (fun t => (t - 5)⁻¹) MeasureTheory.volume 4 (5 - η) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
      intro t ht; rw [Set.uIcc_of_le h5η, Set.mem_Icc] at ht
      simp only [id]; exact ne_of_lt (by linarith [ht.2])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp only [show 5 - η - 5 = -η from by ring, show (4:ℝ) - 5 = -(1:ℝ) from by ring]
    rw [Real.log_neg_eq_log, Real.log_neg_eq_log, Real.log_one, sub_zero]
  -- Combine
  rw [h_split, h_I14, h_I01, h_I45, h_int1, h_int2]
  rw [Complex.ofReal_one, Complex.log_one, ← Complex.ofReal_log hη_div_c_pos.le,
    Real.log_div hη.ne' hc_ne, Complex.ofReal_sub]
  push_cast; ring

set_option maxHeartbeats 16000000 in
private lemma cpv_at_corner (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    CauchyPrincipalValueExists' (fun z => (z - (-(1/2 : ℂ) + ↑H * I))⁻¹)
      (fdBoundary_H H) 0 5 (-(1/2 : ℂ) + ↑H * I) := by
  set s := -(1/2 : ℂ) + ↑H * I with hs_def
  set c := H - Real.sqrt 3 / 2 with hc_def
  have hc : 0 < c := sub_pos.mpr hH
  -- A) CPV on [0, 3] by avoidance
  have h_cpv_03 : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) 0 3 s := by
    apply cpv_avoidance _ _ _ _ _ ((fdBoundary_H_continuous H).continuousOn.mono
      (Set.Icc_subset_Icc_right (by norm_num : (3:ℝ) ≤ 5))) (by norm_num)
    intro t ht habs
    rw [Set.mem_Icc] at ht
    by_cases ht1 : t ≤ 1
    · -- seg1: re = 1/2, but re(s) = -1/2
      have hre := fdBoundary_H_seg1_re' H ht.1 ht1
      rw [habs, hs_def] at hre
      simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.one_re, Complex.div_ofNat] at hre
      linarith
    · push_neg at ht1
      by_cases ht3 : t < 3
      · -- arc: on unit circle (norm = 1), but s has norm > 1
        have h_norm : ‖fdBoundary_H H t‖ = 1 := by
          rw [fdBoundary_H_eq_arc (H := H) ht1 ht3, Complex.norm_exp_ofReal_mul_I]
        rw [habs] at h_norm
        -- ‖s‖ > 1 since ‖s‖² = 1/4 + H² > 1
        have : 1 < ‖s‖ := by
          have h_nsq : 1 < Complex.normSq s := by
            simp only [hs_def, Complex.normSq_apply, Complex.add_re, Complex.neg_re,
              Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
              Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.one_re, Complex.one_im,
              Complex.div_ofNat]
            have hH0 : 0 < H := by
              linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 from by norm_num)]
            nlinarith [mul_lt_mul hH hH.le (by positivity : (0:ℝ) < Real.sqrt 3 / 2) hH0.le,
                       Real.mul_self_sqrt (show (0:ℝ) ≤ 3 from by norm_num)]
          calc (1:ℝ) = Real.sqrt 1 := by simp
            _ < Real.sqrt (Complex.normSq s) := Real.sqrt_lt_sqrt (by norm_num) h_nsq
            _ = ‖s‖ := rfl
        linarith
      · -- t = 3: γ(3) = ρ, which has im = √3/2 < H = im(s)
        have ht3_eq : t = 3 := le_antisymm ht.2 (by linarith)
        subst ht3_eq
        rw [fdBoundary_H_at_three, fdBoundary_at_three] at habs
        have him_s : s.im = H := by
          simp [hs_def, Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
            Complex.I_re, Complex.I_im, Complex.ofReal_re]
        rw [← habs] at him_s
        have him_rho : (ellipticPoint_rho : ℂ).im = Real.sqrt 3 / 2 := by
          simp [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype,
            Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
            Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.div_ofNat]
        linarith [him_rho]
  -- B) CPV on [3, 5] by eventual constancy
  have h_cpv_35 : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) 3 5 s := by
    -- For small ε, both seg4 and seg5 contribute (↑(t-4))⁻¹,
    -- and the cutout integral evaluates (via real FTC) to -↑(Real.log c), independent of ε.
    set ε₀ := min c 1 with hε₀_def
    have hε₀ : 0 < ε₀ := lt_min hc one_pos
    set F := fun ε => ∫ t in (3:ℝ)..5,
      if ε < ‖fdBoundary_H H t - s‖ then (fdBoundary_H H t - s)⁻¹ *
        deriv (fdBoundary_H H) t else 0
    -- F is eventually constant
    suffices h_ev : ∀ ε, 0 < ε → ε < ε₀ → F ε = F (ε₀ / 2) from
      ⟨F (ε₀ / 2), tendsto_const_nhds.congr'
        (Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioo 0 ε₀, Ioo_mem_nhdsGT hε₀,
          fun ε ⟨hε_pos, hε_lt⟩ => (h_ev ε hε_pos hε_lt).symm⟩)⟩
    intro ε hε hε_lt
    have hε_c : ε < c := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hε_1 : ε < 1 := lt_of_lt_of_le hε_lt (min_le_right _ _)
    have hε₀2_pos : 0 < ε₀ / 2 := by positivity
    have hε₀2_c : ε₀ / 2 < c := by
      calc ε₀ / 2 < ε₀ := by linarith
        _ ≤ c := min_le_left _ _
    have hε₀2_1 : ε₀ / 2 < 1 := by
      calc ε₀ / 2 < ε₀ := by linarith
        _ ≤ 1 := min_le_right _ _
    -- Step 1: F(η) = ∫ active_on_seg4 + ∫ active_on_seg5  (for small η)
    -- Step 2: Both reduce to -↑(Real.log c) via real FTC
    -- Combined: F(ε) = F(ε₀/2)
    suffices h_formula : ∀ η, 0 < η → η < c → η < 1 →
        F η = -↑(Real.log c) by
      rw [h_formula ε hε hε_c hε_1, h_formula (ε₀/2) hε₀2_pos hε₀2_c hε₀2_1]
    -- Prove the formula: F(η) = -↑(Real.log c)
    intro η hη hη_c hη_1
    -- Key geometric computations
    have hη_div_c_pos : 0 < η / c := div_pos hη hc
    have hη_div_c_lt_1 : η / c < 1 := (div_lt_one hc).mpr hη_c
    have hc_ne : c ≠ 0 := hc.ne'
    -- On seg4 (t ∈ (3,4)): γ(t) - s = ↑((t-4)*c) * I
    have h_diff_seg4 : ∀ t, 3 < t → t ≤ 4 →
        fdBoundary_H H t - s = ↑((t - 4) * c) * I := by
      intro t ht3 ht4
      rw [fdBoundary_H_eq_seg4_H (by linarith : ¬(t ≤ 1)) (by linarith : ¬(t ≤ 2))
        (by linarith : ¬(t ≤ 3)) ht4, hs_def]
      simp only [fdBoundary_seg4_H, hc_def]
      push_cast; ring
    -- On seg5 (t ∈ (4,5)): γ(t) - s = ↑(t-4)
    have h_diff_seg5 : ∀ t, 4 < t →
        fdBoundary_H H t - s = ↑(t - 4) := by
      intro t ht4
      rw [fdBoundary_H_eq_seg5_H (by linarith : ¬(t ≤ 1)) (by linarith : ¬(t ≤ 2))
        (by linarith : ¬(t ≤ 3)) (by linarith : ¬(t ≤ 4)), hs_def]
      simp only [fdBoundary_seg5_H]
      push_cast; ring
    -- Norms
    have h_norm_seg4 : ∀ t, 3 < t → t ≤ 4 →
        ‖fdBoundary_H H t - s‖ = (4 - t) * c := by
      intro t ht3 ht4
      rw [h_diff_seg4 t ht3 ht4, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_nonpos (by nlinarith : (t - 4) * c ≤ 0)]
      ring
    have h_norm_seg5 : ∀ t, 4 < t →
        ‖fdBoundary_H H t - s‖ = t - 4 := by
      intro t ht4
      rw [h_diff_seg5 t ht4, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    -- On seg4, integrand = (↑(t-4))⁻¹ when active
    have h_integrand_seg4 : ∀ t, 3 < t → t < 4 →
        (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t = (↑(t - 4) : ℂ)⁻¹ := by
      intro t ht3 ht4
      rw [h_diff_seg4 t ht3 ht4.le, (fdBoundary_H_hasDerivAt_seg4 H ht3 ht4).deriv]
      rw [show (↑(H - Real.sqrt 3 / 2) : ℂ) = (↑c : ℂ) from rfl]
      -- Goal: (↑((t-4)*c) * I)⁻¹ * (↑c * I) = (↑(t-4))⁻¹
      have h_t4_ne : (↑(t - 4) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
      have hcC_ne : (↑c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc_ne
      rw [Complex.ofReal_mul]
      field_simp
    -- On seg5, integrand = (↑(t-4))⁻¹ when active
    have h_integrand_seg5 : ∀ t, 4 < t →
        (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t = (↑(t - 4) : ℂ)⁻¹ := by
      intro t ht4
      rw [h_diff_seg5 t ht4, (fdBoundary_H_hasDerivAt_seg5 H ht4).deriv, mul_one]
    -- Split F(η) = ∫₃⁴ + ∫₄⁵
    have h_split : F η = (∫ t in (3:ℝ)..4, if η < ‖fdBoundary_H H t - s‖
        then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) +
      (∫ t in (4:ℝ)..5, if η < ‖fdBoundary_H H t - s‖
        then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) := by
      show (∫ t in (3:ℝ)..5, _) = _
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (IntervalIntegrable.mono_set (fdBoundary_H_cutout_ii H hH s η hη)
          (by rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 4),
                   Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
              exact Set.Icc_subset_Icc (by norm_num) (by norm_num)))
        (IntervalIntegrable.mono_set (fdBoundary_H_cutout_ii H hH s η hη)
          (by rw [Set.uIcc_of_le (by norm_num : (4:ℝ) ≤ 5),
                   Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
              exact Set.Icc_subset_Icc (by norm_num) (by norm_num)))]
    -- Simplify integral on [3, 4]
    have h_I34 : (∫ t in (3:ℝ)..4, if η < ‖fdBoundary_H H t - s‖
        then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) =
      ∫ t in (3:ℝ)..(4 - η / c), (↑(t - 4) : ℂ)⁻¹ := by
      -- The indicator is 1 on [3, 4-η/c) and 0 on (4-η/c, 4]
      have h_4mc : 3 < 4 - η / c := by linarith [hη_div_c_lt_1]
      have h_4mc_le : 4 - η / c ≤ 4 := by linarith [hη_div_c_pos]
      -- Split [3, 4] = [3, 4-η/c] + [4-η/c, 4]
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (IntervalIntegrable.mono_set (fdBoundary_H_cutout_ii H hH s η hη)
          (by rw [Set.uIcc_of_le (by linarith : (3:ℝ) ≤ 4 - η / c),
                   Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
              exact Set.Icc_subset_Icc (by norm_num) (by linarith)))
        (IntervalIntegrable.mono_set (fdBoundary_H_cutout_ii H hH s η hη)
          (by rw [Set.uIcc_of_le (by linarith : 4 - η / c ≤ 4),
                   Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
              exact Set.Icc_subset_Icc (by linarith) (by norm_num)))]
      -- The integral on [4-η/c, 4] is 0
      have h_zero : (∫ t in (4 - η / c)..4,
          if η < ‖fdBoundary_H H t - s‖
          then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) = 0 := by
        have : (∫ t in (4 - η / c)..4,
            if η < ‖fdBoundary_H H t - s‖
            then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) =
            ∫ _ in (4 - η / c)..4, (0 : ℂ) :=
          intervalIntegral.integral_congr (fun t ht => by
            rw [Set.uIcc_of_le h_4mc_le] at ht
            rw [if_neg]; push_neg
            rw [h_norm_seg4 t (by linarith [ht.1]) ht.2]
            -- Need: (4 - t) * c ≤ η. From ht.1: 4 - η/c ≤ t, so 4-t ≤ η/c.
            have h1 : 4 - t ≤ η / c := by linarith [ht.1]
            calc (4 - t) * c ≤ (η / c) * c := by
                  apply mul_le_mul_of_nonneg_right h1 hc.le
              _ = η := by field_simp)
        rw [this, intervalIntegral.integral_zero]
      rw [h_zero, add_zero]
      -- The integral on [3, 4-η/c] simplifies (ae, avoiding endpoint t=4-η/c)
      have h_le : (3:ℝ) ≤ 4 - η / c := by linarith [hη_div_c_lt_1]
      refine intervalIntegral.integral_congr_ae' ?_ (by
        filter_upwards with t ht; exfalso; linarith [ht.1, ht.2])
      -- Main direction: ∀ᵐ x, x ∈ Ioc 3 (4-η/c) → integrand = (↑(x-4))⁻¹
      filter_upwards [compl_mem_ae_iff.mpr (show volume {4 - η / c} = 0 by simp)]
        with t ht_ne
      intro ht
      have ht3 : 3 < t := ht.1
      have ht4_le : t ≤ 4 - η / c := ht.2
      have ht_ne' : t ≠ 4 - η / c := fun h => ht_ne (Set.mem_singleton_iff.mpr h)
      have ht4_strict : t < 4 - η / c := lt_of_le_of_ne ht4_le ht_ne'
      have ht4 : t < 4 := by linarith [hη_div_c_pos]
      rw [if_pos, h_integrand_seg4 t ht3 ht4]
      rw [h_norm_seg4 t ht3 ht4.le]
      have : η / c < 4 - t := by linarith
      calc η = (η / c) * c := by field_simp
        _ < (4 - t) * c := mul_lt_mul_of_pos_right this hc
    -- Simplify integral on [4, 5]
    have h_I45 : (∫ t in (4:ℝ)..5, if η < ‖fdBoundary_H H t - s‖
        then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) =
      ∫ t in (4 + η)..5, (↑(t - 4) : ℂ)⁻¹ := by
      -- The indicator is 0 on [4, 4+η) and 1 on (4+η, 5]
      have h_4ph : 4 + η ≤ 5 := by linarith
      -- Split [4, 5] = [4, 4+η] + [4+η, 5]
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (IntervalIntegrable.mono_set (fdBoundary_H_cutout_ii H hH s η hη)
          (by rw [Set.uIcc_of_le (by linarith : (4:ℝ) ≤ 4 + η),
                   Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
              exact Set.Icc_subset_Icc (by norm_num) (by linarith)))
        (IntervalIntegrable.mono_set (fdBoundary_H_cutout_ii H hH s η hη)
          (by rw [Set.uIcc_of_le h_4ph,
                   Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
              exact Set.Icc_subset_Icc (by linarith) (by norm_num)))]
      -- The integral on [4, 4+η] is 0
      have h_zero : (∫ t in (4:ℝ)..(4 + η),
          if η < ‖fdBoundary_H H t - s‖
          then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) = 0 := by
        have : (∫ t in (4:ℝ)..(4 + η),
            if η < ‖fdBoundary_H H t - s‖
            then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) =
            ∫ _ in (4:ℝ)..(4 + η), (0 : ℂ) :=
          intervalIntegral.integral_congr (fun t ht => by
            rw [Set.uIcc_of_le (by linarith : (4:ℝ) ≤ 4 + η)] at ht
            rw [if_neg]; push_neg
            by_cases ht4 : t = 4
            · rw [ht4, fdBoundary_H_at_four, hs_def, sub_self, norm_zero]; exact hη.le
            · have ht4' : 4 < t := lt_of_le_of_ne ht.1 (Ne.symm ht4)
              rw [h_norm_seg5 t ht4']; linarith [ht.2])
        rw [this, intervalIntegral.integral_zero]
      rw [h_zero, zero_add]
      -- The integral on [4+η, 5] simplifies
      -- Ioc already excludes left endpoint 4+η, so no ae trick needed
      refine intervalIntegral.integral_congr_ae' ?_ (by
        filter_upwards with t ht; exfalso; linarith [ht.1, ht.2])
      -- Main direction: ∀ᵐ x, x ∈ Ioc (4+η) 5 → integrand = (↑(x-4))⁻¹
      filter_upwards with t ht
      have ht4 : 4 < t := by linarith [ht.1]
      rw [if_pos, h_integrand_seg5 t ht4]
      rw [h_norm_seg5 t ht4]; linarith [ht.1]
    -- Compute ∫₃^{4-η/c} (↑(t-4))⁻¹ via substitution u = t - 4
    -- Use real integrals to avoid normed space diamond
    have h_sub34 : (∫ t in (3:ℝ)..(4 - η / c), (↑(t - 4) : ℂ)⁻¹) =
        ∫ u in (-1:ℝ)..(-η / c), (↑u : ℂ)⁻¹ := by
      simp_rw [← Complex.ofReal_inv]
      rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
      congr 1
      have key := intervalIntegral.integral_comp_sub_right
        (fun u : ℝ => u⁻¹) (4 : ℝ)
        (a := (3:ℝ)) (b := 4 - η / c)
      simp only [show (3:ℝ) - 4 = -1 from by ring,
        show (4 - η / c) - 4 = -(η / c) from by ring] at key
      rw [show (-η / c : ℝ) = -(η / c) from by ring]
      exact key
    -- Compute ∫_{4+η}^5 (↑(t-4))⁻¹ via substitution u = t - 4
    have h_sub45 : (∫ t in (4 + η)..5, (↑(t - 4) : ℂ)⁻¹) =
        ∫ u in η..1, (↑u : ℂ)⁻¹ := by
      simp_rw [← Complex.ofReal_inv]
      rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
      congr 1
      have key := intervalIntegral.integral_comp_sub_right
        (fun u : ℝ => u⁻¹) (4 : ℝ)
        (a := 4 + η) (b := (5:ℝ))
      simp only [show (4 + η) - 4 = η from by ring,
        show (5:ℝ) - 4 = 1 from by ring] at key
      exact key
    -- Compute ∫_{-1}^{-η/c} (↑u)⁻¹ via negation: = -∫_{η/c}^{1} (↑u)⁻¹
    have h_neg_axis : (∫ u in (-1:ℝ)..(-η / c), (↑u : ℂ)⁻¹) =
        -(∫ u in (η / c)..1, (↑u : ℂ)⁻¹) := by
      -- Lift to real integrals
      simp_rw [← Complex.ofReal_inv]
      rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
        ← Complex.ofReal_neg, Complex.ofReal_inj]
      -- Need: ∫ u in -1..(-η/c), u⁻¹ = -(∫ u in η/c..1, u⁻¹)
      rw [show (-η / c : ℝ) = -(η / c) from by ring]
      -- ∫ x in η/c..1, (-x)⁻¹ = ∫ x in -1..-(η/c), x⁻¹
      have key : (∫ x in (η / c)..(1:ℝ), (-x)⁻¹) =
          ∫ x in (-1:ℝ)..-(η / c), x⁻¹ :=
        intervalIntegral.integral_comp_neg (fun u : ℝ => u⁻¹) (a := η / c) (b := 1)
      -- Rewrite (-x)⁻¹ = -(x⁻¹) using neg_inv.symm
      rw [show (∫ x in (η / c)..(1:ℝ), (-x)⁻¹) =
          ∫ x in (η / c)..(1:ℝ), -(x⁻¹) from by
          apply intervalIntegral.integral_congr; intro x _; exact neg_inv.symm] at key
      rw [intervalIntegral.integral_neg] at key
      linarith
    -- Compute ∫_{η/c}^{1} (↑u)⁻¹ = Complex.log 1 - Complex.log (η/c)
    have h_pos_int1 : ∫ u in (η / c)..1, (↑u : ℂ)⁻¹ =
        Complex.log ↑(1:ℝ) - Complex.log ↑(η / c) :=
      integral_inv_real_axis 1 (η / c) one_pos hη_div_c_pos hη_div_c_lt_1
    -- Compute ∫_{η}^{1} (↑u)⁻¹ = Complex.log 1 - Complex.log η
    have h_pos_int2 : ∫ u in η..1, (↑u : ℂ)⁻¹ =
        Complex.log ↑(1:ℝ) - Complex.log ↑η :=
      integral_inv_real_axis 1 η one_pos hη (by linarith)
    -- Combine
    rw [h_split, h_I34, h_I45, h_sub34, h_sub45, h_neg_axis, h_pos_int1, h_pos_int2,
      Complex.ofReal_one, Complex.log_one,
      ← Complex.ofReal_log hη.le, ← Complex.ofReal_log hη_div_c_pos.le,
      Real.log_div hη.ne' hc_ne, Complex.ofReal_sub]
    ring
  -- C) Glue [0, 3] + [3, 5] → [0, 5]
  exact cpv_concat _ _ 0 3 5 s h_cpv_03 h_cpv_35 (by norm_num) (by norm_num)
    (fun ε hε => fdBoundary_H_cutout_ii H hH s ε hε)

/-! ## Section 12: Main Theorem -/

set_option maxHeartbeats 8000000 in
/-- For any point on `fdBoundary_H H`, the CPV integral of `(z - s)⁻¹` exists.

The proof handles:
- Elliptic points (rho, rho+1, I for H > 1) directly via proven CPV existence
- I with H ≤ 1: sub-interval CPV on arc, then extend via avoidance
- Non-elliptic points: sub-interval CPV on the containing smooth segment, then extend -/
theorem fdBoundary_H_cpv_exists_of_onCurve (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (h_on : ∃ t ∈ Set.Icc (0:ℝ) 5, fdBoundary_H H t = s) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s := by
  -- Handle elliptic points directly (avoid expensive immersion unification)
  by_cases hs_rho : s = ellipticPoint_rho
  · subst hs_rho
    obtain ⟨L, hL⟩ := cpv_exists_at_rho H hH
    exact ⟨L, hL.congr (fun ε => rfl)⟩
  by_cases hs_rho' : s = ellipticPoint_rho_plus_one
  · subst hs_rho'
    obtain ⟨L, hL⟩ := cpv_exists_at_rho_plus_one H hH
    exact ⟨L, hL.congr (fun ε => rfl)⟩
  by_cases hs_i : s = I
  · subst hs_i
    by_cases hH1 : 1 < H
    · obtain ⟨L, hL⟩ := cpv_exists_at_i H hH1
      exact ⟨L, hL.congr (fun ε => rfl)⟩
    · -- sqrt(3)/2 < H ≤ 1: I is on the arc at t=2.
      push_neg at hH1
      -- I = exp(π/2 * I) = fdBoundary_H H 2
      have hγ2 : fdBoundary_H H 2 = I := by
        rw [fdBoundary_H_eq_arc (by norm_num : (1:ℝ) < 2) (by norm_num : (2:ℝ) < 3)]
        have : Real.pi * (1 + 2) / 6 = Real.pi / 2 := by ring
        rw [this, show (↑(Real.pi / 2) : ℂ) * I = ↑Real.pi / 2 * I from by push_cast; ring]
        exact Complex.exp_pi_div_two_mul_I
      -- Sub-interval CPV on [3/2, 5/2] around t=2
      have h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
          (fdBoundary_H H) (3/2) (5/2) I := by
        apply cpv_exists_on_smooth_subinterval H hH I
          (show (2:ℝ) ∈ Set.Ioo (3/2:ℝ) (5/2) from ⟨by norm_num, by norm_num⟩) hγ2
        · -- ContDiffAt: arc is smooth near t = 2
          have heq : fdBoundary_H H =ᶠ[𝓝 2]
              (fun s => Complex.exp (↑(Real.pi * (1 + s) / 6) * I)) :=
            Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 1 3,
              Ioo_mem_nhds (by norm_num) (by norm_num),
              fun s hs => fdBoundary_H_eq_arc hs.1 hs.2⟩
          apply ContDiffAt.congr_of_eventuallyEq _ heq
          exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp (2:ℝ)
            (by fun_prop : ContDiffAt ℝ 2 (fun s : ℝ => Real.pi * (1 + s) / 6) (2:ℝ))).mul
              contDiffAt_const).cexp
        · -- deriv ≠ 0 at t = 2
          have hd := fdBoundary_H_hasDerivAt_arc H
            (show (1:ℝ) < 2 from by norm_num) (show (2:ℝ) < 3 from by norm_num)
          rw [hd.deriv]
          apply mul_ne_zero (mul_ne_zero _ I_ne_zero) (exp_ne_zero _)
          exact Complex.ofReal_ne_zero.mpr (by positivity)
        · -- ContinuousOn deriv on [3/2, 5/2]
          apply (fdBoundary_H_deriv_continuousOn_Ioo_13 H).mono
          intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
        · -- Injectivity on [3/2, 5/2]
          intro t ht hγt
          have ht' : t ∈ Set.Ioo (1:ℝ) 3 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
          have h2' : (2:ℝ) ∈ Set.Ioo (1:ℝ) 3 := ⟨by norm_num, by norm_num⟩
          rw [fdBoundary_H_eq_arc ht'.1 ht'.2, fdBoundary_H_eq_arc h2'.1 h2'.2] at hγt
          exact arc_angle_injective ht' h2' hγt
      -- Helper: γ(t) = I on arc iff t = 2
      have h_arc_I_iff {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
          fdBoundary_H H t = I ↔ t = 2 := by
        constructor
        · intro h_eq
          have h1 := fdBoundary_H_eq_arc (H := H) ht1 ht3
          have h2 := fdBoundary_H_eq_arc (H := H) (by norm_num : (1:ℝ) < 2) (by norm_num : (2:ℝ) < 3)
          exact arc_angle_injective ⟨ht1, ht3⟩ ⟨by norm_num, by norm_num⟩
            ((h1.symm.trans h_eq).trans (h2.symm.trans hγ2).symm)
        · rintro rfl; exact hγ2
      -- Helper: γ on seg5 ≠ I when H < 1
      have h_seg5_ne_I (hH_lt : H < 1) {t : ℝ} (ht4 : 4 < t) (ht5 : t ≤ 5) :
          fdBoundary_H H t ≠ I := by
        intro h_eq
        have := fdBoundary_H_seg5_im' H ht4 ht5
        rw [h_eq] at this; simp at this; linarith
      -- Helper: fdBoundary_H H 3 = ρ ≠ I
      have hγ3_ne_I : fdBoundary_H H 3 ≠ I := by
        rw [fdBoundary_H_at_three H, fdBoundary_at_three]; exact hs_rho ∘ Eq.symm
      -- Helper: fdBoundary_H H 4 = -1/2 + H*I ≠ I
      have hγ4_ne_I : fdBoundary_H H 4 ≠ I := by
        rw [fdBoundary_H_at_four H]
        intro h_eq; have h_re := congr_arg Complex.re h_eq
        simp at h_re
      -- Case split: H < 1 or H = 1
      rcases lt_or_eq_of_le hH1 with hH_lt | hH_eq
      · -- H < 1: I only at t=2. Avoidance on [0, 3/2] and [5/2, 5].
        apply cpv_extend_to_full_interval H hH I (3/2) (5/2) (by norm_num) (by norm_num)
          (by norm_num) h_arc_cpv
        · -- Avoidance on [0, 3/2]
          intro t ht h_eq
          by_cases ht1 : t ≤ 1
          · have := fdBoundary_H_seg1_re' H ht.1 ht1; rw [h_eq] at this; simp at this
          · push_neg at ht1
            rw [(h_arc_I_iff ht1 (by linarith [ht.2])).mp h_eq] at ht; linarith [ht.2]
        · -- Avoidance on [5/2, 5]
          intro t ht h_eq
          by_cases ht3 : t < 3
          · have ht1 : 1 < t := by linarith [ht.1]
            rw [(h_arc_I_iff ht1 ht3).mp h_eq] at ht; linarith [ht.1]
          · push_neg at ht3
            by_cases ht4 : t ≤ 4
            · rcases eq_or_lt_of_le ht3 with rfl | ht3'
              · exact hγ3_ne_I h_eq
              · have := fdBoundary_H_seg4_re' H ht3' ht4; rw [h_eq] at this; norm_num at this
            · push_neg at ht4
              exact h_seg5_ne_I hH_lt ht4 ht.2 h_eq
      · -- H = 1: I at t=2 AND t=9/2. Need two-crossing approach.
        subst hH_eq
        -- Sub-interval CPV on [17/4, 19/4] around t=9/2 on seg5
        have hγ92 : fdBoundary_H 1 (9/2) = I := by
          rw [fdBoundary_H_eq_seg5_H (by norm_num : ¬(9/2 : ℝ) ≤ 1) (by norm_num : ¬(9/2 : ℝ) ≤ 2)
            (by norm_num : ¬(9/2 : ℝ) ≤ 3) (by norm_num : ¬(9/2 : ℝ) ≤ 4)]
          simp [fdBoundary_seg5_H]
        have h_seg5_cpv : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
            (fdBoundary_H 1) (17/4) (19/4) I := by
          apply cpv_exists_on_smooth_subinterval 1 hH I
            (show (9/2:ℝ) ∈ Set.Ioo (17/4:ℝ) (19/4) from ⟨by norm_num, by norm_num⟩) hγ92
          · -- ContDiffAt: seg5 is affine (C^∞)
            have heq : fdBoundary_H 1 =ᶠ[𝓝 (9/2:ℝ)] fdBoundary_seg5_H 1 :=
              Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioi 4, Ioi_mem_nhds (by norm_num : (4:ℝ) < 9/2),
                fun s (hs : 4 < s) => fdBoundary_H_eq_seg5_H (by linarith) (by linarith)
                  (by linarith) (by linarith)⟩
            apply ContDiffAt.congr_of_eventuallyEq _ heq
            show ContDiffAt ℝ 2 (fdBoundary_seg5_H 1) (9/2 : ℝ)
            unfold fdBoundary_seg5_H
            apply ContDiffAt.add
            · exact Complex.ofRealCLM.contDiff.contDiffAt.sub contDiffAt_const
            · exact contDiffAt_const
          · -- deriv ≠ 0: deriv of seg5 = 1
            have hd := fdBoundary_H_hasDerivAt_seg5 1 (show (4:ℝ) < 9/2 from by norm_num)
            rw [hd.deriv]; exact one_ne_zero
          · -- ContinuousOn deriv on [17/4, 19/4]
            apply (fdBoundary_H_deriv_continuousOn_Ioo_45 1).mono
            intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
          · -- Injectivity: seg5 is t ↦ (t-9/2) + I, injective
            intro t ht hγt
            rw [fdBoundary_H_eq_seg5_H (by linarith [ht.1] : ¬(t:ℝ) ≤ 1)
              (by linarith [ht.1] : ¬(t:ℝ) ≤ 2) (by linarith [ht.1] : ¬(t:ℝ) ≤ 3)
              (by linarith [ht.1] : ¬(t:ℝ) ≤ 4)] at hγt
            rw [fdBoundary_H_eq_seg5_H (by norm_num : ¬(9/2:ℝ) ≤ 1) (by norm_num : ¬(9/2:ℝ) ≤ 2)
              (by norm_num : ¬(9/2:ℝ) ≤ 3) (by norm_num : ¬(9/2:ℝ) ≤ 4)] at hγt
            simp only [fdBoundary_seg5_H] at hγt
            have h_re := congr_arg Complex.re hγt
            simp at h_re; linarith
        -- Now glue: [0, 3/2] avoid, [3/2, 5/2] arc CPV, [5/2, 17/4] avoid,
        --           [17/4, 19/4] seg5 CPV, [19/4, 5] avoid.
        -- Step 1: CPV on [0, 5/2] (avoidance [0, 3/2] + arc CPV [3/2, 5/2])
        have h_cpv_0_52 : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
            (fdBoundary_H 1) 0 (5/2) I := by
          apply cpv_concat _ _ 0 (3/2) (5/2) I
          · apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous 1).continuousOn (by norm_num)
            intro t ht h_eq
            by_cases ht1 : t ≤ 1
            · have := fdBoundary_H_seg1_re' 1 ht.1 ht1; rw [h_eq] at this; simp at this
            · push_neg at ht1
              rw [(h_arc_I_iff ht1 (by linarith [ht.2])).mp h_eq] at ht; linarith [ht.2]
          · exact h_arc_cpv
          · norm_num
          · norm_num
          · intro ε hε; exact (fdBoundary_H_cutout_ii 1 hH I ε hε).mono_set (by
              rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5/2), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
              exact Set.Icc_subset_Icc_right (by norm_num : (5/2:ℝ) ≤ 5))
        -- Step 2: CPV on [5/2, 19/4] (avoidance [5/2, 17/4] + seg5 CPV [17/4, 19/4])
        have h_cpv_52_194 : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
            (fdBoundary_H 1) (5/2) (19/4) I := by
          apply cpv_concat _ _ (5/2) (17/4) (19/4) I
          · apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous 1).continuousOn (by norm_num)
            intro t ht h_eq
            by_cases ht3 : t < 3
            · have ht1 : 1 < t := by linarith [ht.1]
              rw [(h_arc_I_iff ht1 ht3).mp h_eq] at ht; linarith [ht.1]
            · push_neg at ht3
              by_cases ht4 : t ≤ 4
              · rcases eq_or_lt_of_le ht3 with rfl | ht3'
                · exact hγ3_ne_I h_eq
                · have := fdBoundary_H_seg4_re' 1 ht3' ht4; rw [h_eq] at this; norm_num at this
              · push_neg at ht4
                -- seg5 with t ∈ (4, 17/4]: re = t - 9/2 ≠ 0 since t ≤ 17/4 < 9/2
                have := fdBoundary_H_seg5_re' 1 ht4 (by linarith [ht.2])
                rw [h_eq] at this; simp at this; linarith [ht.2]
          · exact h_seg5_cpv
          · norm_num
          · norm_num
          · intro ε hε; exact (fdBoundary_H_cutout_ii 1 hH I ε hε).mono_set (by
              rw [Set.uIcc_of_le (by norm_num : (5/2:ℝ) ≤ 19/4), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
              exact Set.Icc_subset_Icc (by norm_num) (by norm_num))
        -- Step 3: CPV on [0, 19/4]
        have h_cpv_0_194 : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
            (fdBoundary_H 1) 0 (19/4) I := by
          apply cpv_concat _ _ 0 (5/2) (19/4) I h_cpv_0_52 h_cpv_52_194
            (by norm_num) (by norm_num)
          intro ε hε; exact (fdBoundary_H_cutout_ii 1 hH I ε hε).mono_set (by
            rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 19/4), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
            exact Set.Icc_subset_Icc_right (by norm_num : (19/4:ℝ) ≤ 5))
        -- Step 4: Avoidance on [19/4, 5]
        have h_cpv_194_5 : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
            (fdBoundary_H 1) (19/4) 5 I := by
          apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous 1).continuousOn (by norm_num)
          intro t ht h_eq
          -- seg5 with t ∈ [19/4, 5]: re = t - 9/2 ≠ 0 since t ≥ 19/4 > 9/2
          have ht4 : 4 < t := by linarith [ht.1]
          have := fdBoundary_H_seg5_re' 1 ht4 ht.2
          rw [h_eq] at this; simp at this; linarith [ht.1]
        -- Step 5: CPV on [0, 5]
        apply cpv_concat _ _ 0 (19/4) 5 I h_cpv_0_194 h_cpv_194_5
          (by norm_num) (by norm_num)
        intro ε hε; exact fdBoundary_H_cutout_ii 1 hH I ε hε
  · -- Non-elliptic: s is not rho, rho+1, or I.
    obtain ⟨t₀, ht₀_mem, hγt₀⟩ := h_on
    -- Eliminate special crossing values
    by_cases hs_endpoint : s = (1/2 : ℂ) + ↑H * I
    · -- Endpoint crossing: s = γ(0) = γ(5). Integral is eventually constant.
      subst hs_endpoint
      exact cpv_at_endpoint H hH
    by_cases hs_corner : s = -(1/2 : ℂ) + ↑H * I
    · -- Corner crossing at t=4. Integral is eventually constant.
      subst hs_corner
      exact cpv_at_corner H hH
    · -- Generic interior crossing: t₀ is in the smooth interior of a segment.
      -- Eliminate partition points and endpoints
      have ht₀_ne_0 : t₀ ≠ 0 := by
        intro h; subst h; exact hs_endpoint (by rw [← hγt₀, fdBoundary_H_at_zero])
      have ht₀_ne_1 : t₀ ≠ 1 := by
        intro h; subst h
        exact hs_rho' (by rw [← hγt₀, fdBoundary_H_at_one, fdBoundary_at_one])
      have ht₀_ne_3 : t₀ ≠ 3 := by
        intro h; subst h
        exact hs_rho (by rw [← hγt₀, fdBoundary_H_at_three, fdBoundary_at_three])
      have ht₀_ne_4 : t₀ ≠ 4 := by
        intro h; subst h; exact hs_corner (by rw [← hγt₀, fdBoundary_H_at_four])
      have ht₀_ne_5 : t₀ ≠ 5 := by
        intro h; subst h; exact hs_endpoint (by rw [← hγt₀, fdBoundary_H_at_five])
      rw [Set.mem_Icc] at ht₀_mem
      -- t₀ ∈ (0, 1) ∪ (1, 3) ∪ (3, 4) ∪ (4, 5)
      have hh₀ : (0 : ℝ) < H - Real.sqrt 3 / 2 := by linarith
      by_cases ht₀_lt_1 : t₀ < 1
      · -- seg1: t₀ ∈ (0, 1), affine vertical segment
        have ht₀_gt_0 : 0 < t₀ := lt_of_le_of_ne ht₀_mem.1 (Ne.symm ht₀_ne_0)
        apply cpv_extend_to_full_interval H hH s (t₀ / 2) ((t₀ + 1) / 2)
          (by linarith) (by linarith) (by linarith)
        · -- CPV on sub-interval [t₀/2, (t₀+1)/2]
          apply cpv_exists_on_smooth_subinterval H hH s
            ⟨by linarith, by linarith⟩ hγt₀
          · -- ContDiffAt: seg1 is affine, hence C^∞
            have heq : fdBoundary_H H =ᶠ[𝓝 t₀]
                (fun t => (1/2 : ℂ) + ↑(H - t * (H - Real.sqrt 3 / 2)) * I) :=
              Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Iio 1, Iio_mem_nhds ht₀_lt_1,
                fun t ht => by rw [fdBoundary_H_eq_seg1_H (le_of_lt ht)]; simp [fdBoundary_seg1_H]⟩
            apply ContDiffAt.congr_of_eventuallyEq _ heq
            exact contDiffAt_const.add
              ((Complex.ofRealCLM.contDiff.contDiffAt.comp t₀
                (contDiffAt_const.sub (contDiffAt_id.mul contDiffAt_const))).mul contDiffAt_const)
          · -- deriv ≠ 0: derivative is -(H - √3/2) * I ≠ 0
            rw [(fdBoundary_H_hasDerivAt_seg1 H ht₀_lt_1).deriv]
            exact mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (ne_of_gt hh₀))) I_ne_zero
          · -- ContinuousOn deriv on sub-interval ⊂ (0, 1)
            apply (fdBoundary_H_deriv_continuousOn_Ioo_01 H).mono
            intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
          · -- Injectivity: seg1 imaginary part is strictly monotone
            intro t ht hγt
            have ht1 : t ≤ 1 := by linarith [ht.2]
            rw [fdBoundary_H_eq_seg1_H ht1,
                fdBoundary_H_eq_seg1_H (le_of_lt ht₀_lt_1)] at hγt
            simp only [fdBoundary_seg1_H] at hγt
            have h_im := congr_arg Complex.im hγt
            simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re] at h_im
            rcases h_im with rfl | h_abs
            · rfl
            · linarith
        · -- Avoidance on [0, t₀/2]
          intro t ht h_eq
          have ht1 : t ≤ 1 := by linarith [ht.2]
          rw [fdBoundary_H_eq_seg1_H ht1,
              ← hγt₀, fdBoundary_H_eq_seg1_H (le_of_lt ht₀_lt_1)] at h_eq
          simp only [fdBoundary_seg1_H] at h_eq
          have h_im := congr_arg Complex.im h_eq
          simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re] at h_im
          rcases h_im with rfl | h_abs
          · linarith [ht.2]
          · linarith
        · -- Avoidance on [(t₀+1)/2, 5]
          -- Key facts about s (from seg1):
          have h_re_s : s.re = 1/2 := by
            rw [← hγt₀]; exact fdBoundary_H_seg1_re' H (le_of_lt ht₀_gt_0) (le_of_lt ht₀_lt_1)
          have h_im_s_lt : s.im < H := by
            rw [← hγt₀, fdBoundary_H_eq_seg1_H (le_of_lt ht₀_lt_1)]
            simp [fdBoundary_seg1_H, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
              Complex.I_re, Complex.I_im, Complex.ofReal_re]
            nlinarith
          have h_norm_s_gt : 1 < Complex.normSq s := by
            rw [Complex.normSq_apply, h_re_s]
            have h_im_s_gt : Real.sqrt 3 / 2 < s.im := by
              rw [← hγt₀, fdBoundary_H_eq_seg1_H (le_of_lt ht₀_lt_1)]
              simp [fdBoundary_seg1_H, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
                Complex.I_re, Complex.I_im, Complex.ofReal_re]
              nlinarith
            nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 3 from by norm_num),
              mul_self_lt_mul_self (by positivity : (0:ℝ) ≤ Real.sqrt 3 / 2) h_im_s_gt]
          intro t ht h_eq
          by_cases ht1 : t ≤ 1
          · -- Still on seg1: im differs since t > t₀
            rw [fdBoundary_H_eq_seg1_H ht1,
                ← hγt₀, fdBoundary_H_eq_seg1_H (le_of_lt ht₀_lt_1)] at h_eq
            simp only [fdBoundary_seg1_H] at h_eq
            have h_im := congr_arg Complex.im h_eq
            simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re] at h_im
            rcases h_im with rfl | h_abs
            · linarith [ht.1]
            · linarith
          · push_neg at ht1
            by_cases ht3 : t < 3
            · -- Arc: ‖γ(t)‖² = 1 but ‖s‖² > 1
              have h_norm_arc : Complex.normSq (fdBoundary_H H t) = 1 := by
                rw [fdBoundary_H_eq_arc ht1 ht3, Complex.normSq_apply,
                  Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
                linarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t) / 6)]
              rw [h_eq] at h_norm_arc; linarith
            · push_neg at ht3
              by_cases ht4 : t ≤ 4
              · -- seg4: re = -1/2 ≠ 1/2 = re(s)
                rcases eq_or_lt_of_le ht3 with rfl | ht3'
                · rw [fdBoundary_H_at_three, fdBoundary_at_three] at h_eq
                  exact hs_rho h_eq.symm
                · have h_re_t := fdBoundary_H_seg4_re' H ht3' ht4
                  rw [h_eq] at h_re_t; linarith
              · push_neg at ht4
                -- seg5: im = H but im(s) < H
                have h_im_t := fdBoundary_H_seg5_im' H ht4 ht.2
                rw [h_eq] at h_im_t; linarith
      · -- t₀ ≥ 1
        push_neg at ht₀_lt_1
        have ht₀_gt_1 : 1 < t₀ := lt_of_le_of_ne ht₀_lt_1 (Ne.symm ht₀_ne_1)
        by_cases ht₀_lt_3 : t₀ < 3
        · -- arc: t₀ ∈ (1, 3). s is on the unit circle.
          -- Key properties of s
          have h_re_s : s.re = Real.cos (Real.pi * (1 + t₀) / 6) := by
            rw [← hγt₀]; exact fdBoundary_H_arc_re' H ht₀_gt_1 ht₀_lt_3
          have h_im_s_arc : s.im = Real.sin (Real.pi * (1 + t₀) / 6) := by
            rw [← hγt₀]; exact fdBoundary_H_arc_im' H ht₀_gt_1 ht₀_lt_3
          have h_normSq_s : Complex.normSq s = 1 := by
            rw [Complex.normSq_apply, h_re_s, h_im_s_arc]
            linarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t₀) / 6)]
          -- s.re ∈ (-1/2, 1/2) from cos being strictly decreasing on [0, π]
          have h_re_s_lt : s.re < 1/2 := by
            rw [h_re_s]
            have h1 : Real.pi * (1 + t₀) / 6 ∈ Set.Icc 0 Real.pi :=
              ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
            have h2 : Real.pi / 3 ∈ Set.Icc 0 Real.pi :=
              ⟨by positivity, by linarith [Real.pi_pos]⟩
            have := Real.strictAntiOn_cos h2 h1 (by nlinarith [Real.pi_pos])
            linarith [Real.cos_pi_div_three]
          have h_re_s_gt : -(1:ℝ)/2 < s.re := by
            rw [h_re_s]
            have h1 : Real.pi * (1 + t₀) / 6 ∈ Set.Icc 0 Real.pi :=
              ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
            have h2 : Real.pi * 2 / 3 ∈ Set.Icc 0 Real.pi :=
              ⟨by positivity, by nlinarith [Real.pi_pos]⟩
            have := Real.strictAntiOn_cos h1 h2 (by nlinarith [Real.pi_pos])
            have h_cos23 : Real.cos (Real.pi * 2 / 3) = -(1:ℝ)/2 := by
              rw [show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 from by ring,
                Real.cos_pi_sub, Real.cos_pi_div_three]; ring
            linarith
          -- Sub-interval CPV on arc [(t₀+1)/2, (t₀+3)/2]
          have h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
              (fdBoundary_H H) ((t₀ + 1) / 2) ((t₀ + 3) / 2) s := by
            apply cpv_exists_on_smooth_subinterval H hH s
              ⟨by linarith, by linarith⟩ hγt₀
            · -- ContDiffAt: arc is smooth
              have heq : fdBoundary_H H =ᶠ[𝓝 t₀]
                  (fun u => Complex.exp (↑(Real.pi * (1 + u) / 6) * I)) :=
                Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 1 3,
                  Ioo_mem_nhds ht₀_gt_1 ht₀_lt_3,
                  fun u hu => fdBoundary_H_eq_arc hu.1 hu.2⟩
              apply ContDiffAt.congr_of_eventuallyEq _ heq
              exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp t₀
                (by fun_prop : ContDiffAt ℝ 2 (fun u : ℝ => Real.pi * (1 + u) / 6) t₀)).mul
                  contDiffAt_const).cexp
            · -- deriv ≠ 0
              rw [(fdBoundary_H_hasDerivAt_arc H ht₀_gt_1 ht₀_lt_3).deriv]
              apply mul_ne_zero (mul_ne_zero _ I_ne_zero) (exp_ne_zero _)
              exact Complex.ofReal_ne_zero.mpr (by positivity)
            · -- ContinuousOn deriv on sub-interval ⊂ (1, 3)
              apply (fdBoundary_H_deriv_continuousOn_Ioo_13 H).mono
              intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
            · -- Injectivity on sub-interval
              intro t ht hγt
              have ht' : t ∈ Set.Ioo (1:ℝ) 3 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
              exact arc_angle_injective ht' ⟨ht₀_gt_1, ht₀_lt_3⟩
                (by rw [fdBoundary_H_eq_arc ht'.1 ht'.2,
                    fdBoundary_H_eq_arc ht₀_gt_1 ht₀_lt_3] at hγt; exact hγt)
          -- Case split: seg5 crossing when s.im = H
          by_cases h_seg5_cross : s.im = H
          · -- Double crossing with seg5. s on arc at t₀ and on seg5 (since s.im = H).
            -- Find the seg5 crossing point: t₁ = s.re + 9/2
            set t₁ := s.re + 9/2 with ht₁_def
            have ht₁_gt4 : 4 < t₁ := by simp [ht₁_def]; linarith [h_re_s_gt]
            have ht₁_lt5 : t₁ < 5 := by simp [ht₁_def]; linarith [h_re_s_lt]
            have hγt₁ : fdBoundary_H H t₁ = s := by
              rw [fdBoundary_H_eq_seg5_H (by linarith : ¬t₁ ≤ 1)
                (by linarith : ¬t₁ ≤ 2) (by linarith : ¬t₁ ≤ 3) (by linarith : ¬t₁ ≤ 4)]
              apply Complex.ext
              · simp [fdBoundary_seg5_H, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
                  Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, ht₁_def]
              · simp [fdBoundary_seg5_H, Complex.add_im, Complex.sub_im, Complex.ofReal_im,
                  Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
                  h_seg5_cross]
            -- Build seg5 sub-interval CPV on [(t₁+4)/2, (t₁+5)/2]
            have h_seg5_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
                (fdBoundary_H H) ((t₁ + 4) / 2) ((t₁ + 5) / 2) s := by
              apply cpv_exists_on_smooth_subinterval H hH s
                ⟨by linarith, by linarith⟩ hγt₁
              · -- ContDiffAt: seg5 is affine
                have heq_fn : ∀ u ∈ Set.Ioi (4:ℝ), fdBoundary_H H u =
                    (↑(u - 9/2) : ℂ) + ↑H * I := by
                  intro u (hu : 4 < u)
                  rw [fdBoundary_H_eq_seg5_H (by linarith) (by linarith)
                    (by linarith) (by linarith)]
                  simp [fdBoundary_seg5_H]
                have heq : fdBoundary_H H =ᶠ[𝓝 t₁]
                    (fun t => (↑(t - 9/2) : ℂ) + ↑H * I) :=
                  Filter.eventuallyEq_iff_exists_mem.mpr
                    ⟨Set.Ioi 4, Ioi_mem_nhds ht₁_gt4, heq_fn⟩
                apply ContDiffAt.congr_of_eventuallyEq _ heq
                exact (Complex.ofRealCLM.contDiff.contDiffAt.comp t₁
                  (contDiffAt_id.sub contDiffAt_const)).add contDiffAt_const
              · -- deriv ≠ 0
                rw [(fdBoundary_H_hasDerivAt_seg5 H ht₁_gt4).deriv]; exact one_ne_zero
              · -- ContinuousOn deriv
                apply (fdBoundary_H_deriv_continuousOn_Ioo_45 H).mono
                intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
              · -- Injectivity
                intro t ht hγt
                rw [fdBoundary_H_eq_seg5_H (by linarith [ht.1] : ¬t ≤ 1)
                    (by linarith [ht.1] : ¬t ≤ 2) (by linarith [ht.1] : ¬t ≤ 3)
                    (by linarith [ht.1] : ¬t ≤ 4),
                    fdBoundary_H_eq_seg5_H (by linarith : ¬t₁ ≤ 1)
                    (by linarith : ¬t₁ ≤ 2) (by linarith : ¬t₁ ≤ 3)
                    (by linarith : ¬t₁ ≤ 4)] at hγt
                simp only [fdBoundary_seg5_H] at hγt
                have h_re := congr_arg Complex.re hγt
                simp [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
                  Complex.I_re, Complex.I_im, Complex.ofReal_im] at h_re
                linarith
            -- Step 1: CPV on [0, (t₀+3)/2] = avoidance [0, (t₀+1)/2] + arc CPV
            have h_cpv_0_t0h : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
                (fdBoundary_H H) 0 ((t₀ + 3) / 2) s := by
              apply cpv_concat _ _ 0 ((t₀ + 1) / 2) ((t₀ + 3) / 2) s
              · apply cpv_avoidance _ _ _ _ _
                  (fdBoundary_H_continuous H).continuousOn (by linarith)
                intro t ht h_eq
                by_cases ht1 : t ≤ 1
                · have := fdBoundary_H_seg1_re' H ht.1 ht1
                  rw [h_eq] at this; linarith
                · push_neg at ht1
                  have ht3 : t < 3 := by linarith [ht.2]
                  have h_ne : t ≠ t₀ := by linarith [ht.2]
                  exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₀_gt_1, ht₀_lt_3⟩
                    (by have := h_eq.trans hγt₀.symm
                        rwa [fdBoundary_H_eq_arc ht1 ht3,
                          fdBoundary_H_eq_arc ht₀_gt_1 ht₀_lt_3] at this))
              · exact h_arc_cpv
              · linarith
              · linarith
              · intro ε hε; exact (fdBoundary_H_cutout_ii H hH s ε hε).mono_set (by
                  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ (t₀ + 3) / 2),
                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
                  exact Set.Icc_subset_Icc_right (by linarith))
            -- Step 2: Avoidance on [(t₀+3)/2, (t₁+4)/2]
            have h_cpv_mid_avoid : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
                (fdBoundary_H H) ((t₀ + 3) / 2) ((t₁ + 4) / 2) s := by
              apply cpv_avoidance _ _ _ _ _
                (fdBoundary_H_continuous H).continuousOn (by linarith)
              intro t ht h_eq
              by_cases ht3 : t < 3
              · have ht1 : 1 < t := by linarith [ht.1]
                have h_ne : t ≠ t₀ := by linarith [ht.1]
                exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₀_gt_1, ht₀_lt_3⟩
                  (by have := h_eq.trans hγt₀.symm
                      rwa [fdBoundary_H_eq_arc ht1 ht3,
                        fdBoundary_H_eq_arc ht₀_gt_1 ht₀_lt_3] at this))
              · push_neg at ht3
                by_cases ht4 : t ≤ 4
                · rcases eq_or_lt_of_le ht3 with rfl | ht3'
                  · rw [fdBoundary_H_at_three, fdBoundary_at_three] at h_eq
                    exact hs_rho h_eq.symm
                  · have := fdBoundary_H_seg4_re' H ht3' ht4
                    rw [h_eq] at this; linarith
                · push_neg at ht4
                  have := fdBoundary_H_seg5_re' H ht4 (by linarith [ht.2])
                  rw [h_eq] at this
                  -- t - 9/2 = s.re but t < t₁ = s.re + 9/2, contradiction
                  simp [ht₁_def] at *; linarith [ht.2]
            -- Step 3: CPV on [(t₀+3)/2, (t₁+5)/2] = avoidance + seg5 CPV
            have h_cpv_mid : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
                (fdBoundary_H H) ((t₀ + 3) / 2) ((t₁ + 5) / 2) s := by
              apply cpv_concat _ _ ((t₀ + 3) / 2) ((t₁ + 4) / 2) ((t₁ + 5) / 2) s
                h_cpv_mid_avoid h_seg5_cpv (by linarith) (by linarith)
              intro ε hε; exact (fdBoundary_H_cutout_ii H hH s ε hε).mono_set (by
                rw [Set.uIcc_of_le (by linarith : (t₀ + 3) / 2 ≤ (t₁ + 5) / 2),
                  Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
                exact Set.Icc_subset_Icc (by linarith) (by linarith))
            -- Step 4: CPV on [0, (t₁+5)/2]
            have h_cpv_0_t1h : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
                (fdBoundary_H H) 0 ((t₁ + 5) / 2) s := by
              apply cpv_concat _ _ 0 ((t₀ + 3) / 2) ((t₁ + 5) / 2) s
                h_cpv_0_t0h h_cpv_mid (by linarith) (by linarith)
              intro ε hε; exact (fdBoundary_H_cutout_ii H hH s ε hε).mono_set (by
                rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ (t₁ + 5) / 2),
                  Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
                exact Set.Icc_subset_Icc_right (by linarith))
            -- Step 5: Avoidance on [(t₁+5)/2, 5]
            have h_cpv_end : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
                (fdBoundary_H H) ((t₁ + 5) / 2) 5 s := by
              apply cpv_avoidance _ _ _ _ _
                (fdBoundary_H_continuous H).continuousOn (by linarith)
              intro t ht h_eq
              have ht4 : 4 < t := by linarith [ht.1]
              have := fdBoundary_H_seg5_re' H ht4 ht.2
              rw [h_eq] at this
              simp [ht₁_def] at *; linarith [ht.1]
            -- Step 6: CPV on [0, 5]
            exact cpv_concat _ _ 0 ((t₁ + 5) / 2) 5 s h_cpv_0_t1h h_cpv_end
              (by linarith) (by linarith)
              (fun ε hε => fdBoundary_H_cutout_ii H hH s ε hε)
          · -- No seg5 crossing: simple extension
            apply cpv_extend_to_full_interval H hH s ((t₀ + 1) / 2) ((t₀ + 3) / 2)
              (by linarith) (by linarith) (by linarith) h_arc_cpv
            · -- Avoidance on [0, (t₀+1)/2]
              intro t ht h_eq
              by_cases ht1 : t ≤ 1
              · -- seg1: re = 1/2 ≠ re(s)
                have := fdBoundary_H_seg1_re' H ht.1 ht1; rw [h_eq] at this; linarith
              · push_neg at ht1
                -- arc: t ∈ (1, (t₀+1)/2), injectivity → t = t₀, contradiction
                have ht3 : t < 3 := by linarith [ht.2]
                have h_ne : t ≠ t₀ := by linarith [ht.2]
                exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₀_gt_1, ht₀_lt_3⟩
                  (by have := h_eq.trans hγt₀.symm
                      rwa [fdBoundary_H_eq_arc ht1 ht3,
                        fdBoundary_H_eq_arc ht₀_gt_1 ht₀_lt_3] at this))
            · -- Avoidance on [(t₀+3)/2, 5]
              intro t ht h_eq
              by_cases ht3 : t < 3
              · -- arc: t > t₀, injectivity
                have ht1 : 1 < t := by linarith [ht.1]
                have h_ne : t ≠ t₀ := by linarith [ht.1]
                exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₀_gt_1, ht₀_lt_3⟩
                  (by have := h_eq.trans hγt₀.symm
                      rwa [fdBoundary_H_eq_arc ht1 ht3,
                        fdBoundary_H_eq_arc ht₀_gt_1 ht₀_lt_3] at this))
              · push_neg at ht3
                by_cases ht4 : t ≤ 4
                · rcases eq_or_lt_of_le ht3 with rfl | ht3'
                  · rw [fdBoundary_H_at_three, fdBoundary_at_three] at h_eq
                    exact hs_rho h_eq.symm
                  · -- seg4: re = -1/2 ≠ re(s)
                    have := fdBoundary_H_seg4_re' H ht3' ht4
                    rw [h_eq] at this; linarith
                · push_neg at ht4
                  -- seg5: im = H ≠ s.im
                  have := fdBoundary_H_seg5_im' H ht4 ht.2
                  rw [h_eq] at this; exact h_seg5_cross this
        · -- t₀ ≥ 3
          push_neg at ht₀_lt_3
          have ht₀_gt_3 : 3 < t₀ := lt_of_le_of_ne ht₀_lt_3 (Ne.symm ht₀_ne_3)
          by_cases ht₀_lt_4 : t₀ < 4
          · -- seg4: t₀ ∈ (3, 4), affine vertical segment
            apply cpv_extend_to_full_interval H hH s ((t₀ + 3) / 2) ((t₀ + 4) / 2)
              (by linarith) (by linarith) (by linarith)
            · -- CPV on sub-interval
              apply cpv_exists_on_smooth_subinterval H hH s
                ⟨by linarith, by linarith⟩ hγt₀
              · -- ContDiffAt: seg4 is affine
                have heq_fn : ∀ u ∈ Set.Ioo (3:ℝ) 4, fdBoundary_H H u =
                    (-(1/2 : ℂ) + ↑(Real.sqrt 3 / 2 + (u - 3) * (H - Real.sqrt 3 / 2)) * I) := by
                  intro u hu
                  rw [fdBoundary_H_eq_seg4_H (by linarith [hu.1] : ¬u ≤ 1)
                    (by linarith [hu.1] : ¬u ≤ 2) (by linarith [hu.1] : ¬u ≤ 3) (le_of_lt hu.2)]
                  simp [fdBoundary_seg4_H]; norm_num
                have heq : fdBoundary_H H =ᶠ[𝓝 t₀]
                    (fun t => -(1/2 : ℂ) + ↑(Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2)) * I) :=
                  Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 3 4,
                    Ioo_mem_nhds ht₀_gt_3 ht₀_lt_4, heq_fn⟩
                apply ContDiffAt.congr_of_eventuallyEq _ heq
                exact contDiffAt_const.add
                  ((Complex.ofRealCLM.contDiff.contDiffAt.comp t₀
                    (contDiffAt_const.add ((contDiffAt_id.sub contDiffAt_const).mul
                      contDiffAt_const))).mul contDiffAt_const)
              · -- deriv ≠ 0
                rw [(fdBoundary_H_hasDerivAt_seg4 H ht₀_gt_3 ht₀_lt_4).deriv]
                exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hh₀)) I_ne_zero
              · -- ContinuousOn deriv
                apply (fdBoundary_H_deriv_continuousOn_Ioo_34 H).mono
                intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
              · -- Injectivity: seg4 im is strictly monotone
                intro t ht hγt
                rw [fdBoundary_H_eq_seg4_H (by linarith [ht.1] : ¬t ≤ 1)
                    (by linarith [ht.1] : ¬t ≤ 2) (by linarith [ht.1] : ¬t ≤ 3)
                    (by linarith [ht.2] : t ≤ 4),
                    fdBoundary_H_eq_seg4_H (by linarith : ¬t₀ ≤ 1)
                    (by linarith : ¬t₀ ≤ 2) (by linarith : ¬t₀ ≤ 3)
                    (le_of_lt ht₀_lt_4)] at hγt
                simp only [fdBoundary_seg4_H] at hγt
                have h_im := congr_arg Complex.im hγt
                simp [Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
                  Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.div_ofNat] at h_im
                rcases h_im with rfl | h_abs
                · rfl
                · linarith
            · -- Avoidance on [0, (t₀+3)/2]
              have h_re_s : s.re = -1/2 := by
                rw [← hγt₀]; exact fdBoundary_H_seg4_re' H ht₀_gt_3 (le_of_lt ht₀_lt_4)
              have h_norm_s_gt : 1 < Complex.normSq s := by
                rw [Complex.normSq_apply, h_re_s]
                have h_im_s_gt : Real.sqrt 3 / 2 < s.im := by
                  rw [← hγt₀, fdBoundary_H_eq_seg4_H (by linarith : ¬t₀ ≤ 1)
                    (by linarith : ¬t₀ ≤ 2) (by linarith : ¬t₀ ≤ 3) (le_of_lt ht₀_lt_4)]
                  simp [fdBoundary_seg4_H, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
                    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
                  nlinarith
                nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 3 from by norm_num),
                  mul_self_lt_mul_self (by positivity : (0:ℝ) ≤ Real.sqrt 3 / 2) h_im_s_gt]
              intro t ht h_eq
              by_cases ht1 : t ≤ 1
              · have := fdBoundary_H_seg1_re' H ht.1 ht1; rw [h_eq] at this; linarith
              · push_neg at ht1
                by_cases ht3 : t < 3
                · -- arc: normSq = 1 < normSq(s)
                  have h_norm_arc : Complex.normSq (fdBoundary_H H t) = 1 := by
                    rw [fdBoundary_H_eq_arc ht1 ht3, Complex.normSq_apply,
                      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
                    linarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t) / 6)]
                  rw [h_eq] at h_norm_arc; linarith
                · push_neg at ht3
                  by_cases ht4 : t ≤ 4
                  · rcases eq_or_lt_of_le ht3 with rfl | ht3'
                    · rw [fdBoundary_H_at_three, fdBoundary_at_three] at h_eq
                      exact hs_rho h_eq.symm
                    · -- seg4: im differs since t < t₀
                      rw [fdBoundary_H_eq_seg4_H (by linarith : ¬t ≤ 1) (by linarith : ¬t ≤ 2)
                          (by linarith : ¬t ≤ 3) ht4,
                          ← hγt₀, fdBoundary_H_eq_seg4_H (by linarith : ¬t₀ ≤ 1)
                          (by linarith : ¬t₀ ≤ 2) (by linarith : ¬t₀ ≤ 3)
                          (le_of_lt ht₀_lt_4)] at h_eq
                      simp only [fdBoundary_seg4_H] at h_eq
                      have h_im := congr_arg Complex.im h_eq
                      simp [Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
                        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.div_ofNat] at h_im
                      rcases h_im with rfl | h_abs
                      · linarith [ht.2]
                      · linarith
                  · push_neg at ht4; linarith [ht.2]
            · -- Avoidance on [(t₀+4)/2, 5]
              have h_re_s : s.re = -1/2 := by
                rw [← hγt₀]; exact fdBoundary_H_seg4_re' H ht₀_gt_3 (le_of_lt ht₀_lt_4)
              intro t ht h_eq
              by_cases ht4' : 4 < t
              · -- seg5: re differs
                have := fdBoundary_H_seg5_re' H ht4' ht.2
                rw [h_eq] at this; linarith
              · push_neg at ht4'
                have ht3' : 3 < t := by linarith [ht.1]
                by_cases ht4_eq : t = 4
                · subst ht4_eq; rw [fdBoundary_H_at_four] at h_eq; exact hs_corner h_eq.symm
                · -- seg4: im differs since t > t₀
                  rw [fdBoundary_H_eq_seg4_H (by linarith : ¬t ≤ 1) (by linarith : ¬t ≤ 2)
                      (by linarith : ¬t ≤ 3) (by linarith : t ≤ 4),
                      ← hγt₀, fdBoundary_H_eq_seg4_H (by linarith : ¬t₀ ≤ 1)
                      (by linarith : ¬t₀ ≤ 2) (by linarith : ¬t₀ ≤ 3)
                      (le_of_lt ht₀_lt_4)] at h_eq
                  simp only [fdBoundary_seg4_H] at h_eq
                  have h_im := congr_arg Complex.im h_eq
                  simp [Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
                    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.div_ofNat] at h_im
                  rcases h_im with rfl | h_abs
                  · linarith [ht.1]
                  · linarith
          · -- seg5: t₀ ∈ (4, 5), affine horizontal segment
            push_neg at ht₀_lt_4
            have ht₀_gt_4 : 4 < t₀ := lt_of_le_of_ne ht₀_lt_4 (Ne.symm ht₀_ne_4)
            have ht₀_lt_5 : t₀ < 5 := lt_of_le_of_ne ht₀_mem.2 ht₀_ne_5
            have h_im_s : s.im = H := by
              rw [← hγt₀]; exact fdBoundary_H_seg5_im' H ht₀_gt_4 (le_of_lt ht₀_lt_5)
            have h_re_s : s.re = t₀ - 9/2 := by
              rw [← hγt₀]; exact fdBoundary_H_seg5_re' H ht₀_gt_4 (le_of_lt ht₀_lt_5)
            -- Sub-interval CPV
            have h_seg5_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
                (fdBoundary_H H) ((t₀ + 4) / 2) ((t₀ + 5) / 2) s := by
              apply cpv_exists_on_smooth_subinterval H hH s
                ⟨by linarith, by linarith⟩ hγt₀
              · -- ContDiffAt: seg5 is affine
                have heq_fn : ∀ u ∈ Set.Ioi (4:ℝ), fdBoundary_H H u =
                    (↑(u - 9/2) : ℂ) + ↑H * I := by
                  intro u (hu : 4 < u)
                  rw [fdBoundary_H_eq_seg5_H (by linarith) (by linarith) (by linarith) (by linarith)]
                  simp [fdBoundary_seg5_H]
                have heq : fdBoundary_H H =ᶠ[𝓝 t₀] (fun t => (↑(t - 9/2) : ℂ) + ↑H * I) :=
                  Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioi 4, Ioi_mem_nhds ht₀_gt_4, heq_fn⟩
                apply ContDiffAt.congr_of_eventuallyEq _ heq
                exact (Complex.ofRealCLM.contDiff.contDiffAt.comp t₀
                  (contDiffAt_id.sub contDiffAt_const)).add contDiffAt_const
              · -- deriv ≠ 0: deriv = 1
                rw [(fdBoundary_H_hasDerivAt_seg5 H ht₀_gt_4).deriv]; exact one_ne_zero
              · -- ContinuousOn deriv
                apply (fdBoundary_H_deriv_continuousOn_Ioo_45 H).mono
                intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
              · -- Injectivity: seg5 re is strictly monotone
                intro t ht hγt
                rw [fdBoundary_H_eq_seg5_H (by linarith [ht.1] : ¬t ≤ 1)
                    (by linarith [ht.1] : ¬t ≤ 2) (by linarith [ht.1] : ¬t ≤ 3)
                    (by linarith [ht.1] : ¬t ≤ 4),
                    fdBoundary_H_eq_seg5_H (by linarith : ¬t₀ ≤ 1)
                    (by linarith : ¬t₀ ≤ 2) (by linarith : ¬t₀ ≤ 3)
                    (by linarith : ¬t₀ ≤ 4)] at hγt
                simp only [fdBoundary_seg5_H] at hγt
                have h_re := congr_arg Complex.re hγt
                simp [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
                  Complex.I_re, Complex.I_im, Complex.ofReal_im] at h_re
                linarith
            -- Now handle avoidance. Case split on whether s is on the arc (normSq = 1).
            by_cases h_normSq : Complex.normSq s = 1
            · -- normSq(s) = 1: double crossing with arc.
              -- s is on the unit circle and on seg5.
              have h_re_s_lt : s.re < 1/2 := by linarith [h_re_s]
              have h_re_s_gt : -(1:ℝ)/2 < s.re := by linarith [h_re_s]
              -- Use IVT to find arc crossing t₁
              have h_ivt : s.re ∈ (fun t => Real.cos (Real.pi * (1 + t) / 6)) ''
                  Set.Icc (1:ℝ) 3 := by
                apply intermediate_value_Icc' (by norm_num : (1:ℝ) ≤ 3)
                · exact (Real.continuous_cos.comp
                    (by fun_prop : Continuous (fun t => Real.pi * (1 + t) / 6))).continuousOn
                · constructor
                  · rw [show Real.pi * (1 + 3) / 6 = Real.pi - Real.pi / 3 from by ring,
                      Real.cos_pi_sub, Real.cos_pi_div_three]; linarith
                  · rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
                      Real.cos_pi_div_three]; linarith
              obtain ⟨t₁, ht₁_mem, ht₁_cos⟩ := h_ivt
              simp only [] at ht₁_cos  -- beta-reduce lambda application
              have ht₁_gt1 : 1 < t₁ := by
                rcases eq_or_lt_of_le ht₁_mem.1 with rfl | h
                · rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
                    Real.cos_pi_div_three] at ht₁_cos; linarith
                · exact h
              have ht₁_lt3 : t₁ < 3 := by
                rcases eq_or_lt_of_le ht₁_mem.2 with rfl | h
                · rw [show Real.pi * (1 + 3) / 6 = Real.pi - Real.pi / 3 from by ring,
                    Real.cos_pi_sub, Real.cos_pi_div_three] at ht₁_cos; linarith
                · exact h
              -- γ(t₁) = s: re matches by construction, im matches by normSq = 1
              have hγt₁ : fdBoundary_H H t₁ = s := by
                rw [fdBoundary_H_eq_arc ht₁_gt1 ht₁_lt3]
                apply Complex.ext
                · rw [Complex.exp_ofReal_mul_I_re]; exact ht₁_cos
                · rw [Complex.exp_ofReal_mul_I_im]
                  have h_sin_pos : 0 < Real.sin (Real.pi * (1 + t₁) / 6) :=
                    Real.sin_pos_of_pos_of_lt_pi
                      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
                  exact (sq_eq_sq₀ (le_of_lt h_sin_pos)
                    (by rw [h_im_s]; linarith [hH, Real.sqrt_nonneg 3] : (0:ℝ) ≤ s.im)).mp (by
                    have h1 := Real.sin_sq_add_cos_sq (Real.pi * (1 + t₁) / 6)
                    rw [ht₁_cos] at h1
                    rw [Complex.normSq_apply] at h_normSq
                    nlinarith)
              -- Build arc sub-interval CPV on [(t₁+1)/2, (t₁+3)/2]
              have h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
                  (fdBoundary_H H) ((t₁ + 1) / 2) ((t₁ + 3) / 2) s := by
                apply cpv_exists_on_smooth_subinterval H hH s
                  ⟨by linarith, by linarith⟩ hγt₁
                · -- ContDiffAt: arc is smooth
                  have heq : fdBoundary_H H =ᶠ[𝓝 t₁]
                      (fun u => Complex.exp (↑(Real.pi * (1 + u) / 6) * I)) :=
                    Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 1 3,
                      Ioo_mem_nhds ht₁_gt1 ht₁_lt3,
                      fun u hu => fdBoundary_H_eq_arc hu.1 hu.2⟩
                  apply ContDiffAt.congr_of_eventuallyEq _ heq
                  exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp t₁
                    (by fun_prop : ContDiffAt ℝ 2 (fun u : ℝ => Real.pi * (1 + u) / 6) t₁)).mul
                      contDiffAt_const).cexp
                · -- deriv ≠ 0
                  rw [(fdBoundary_H_hasDerivAt_arc H ht₁_gt1 ht₁_lt3).deriv]
                  apply mul_ne_zero (mul_ne_zero _ I_ne_zero) (exp_ne_zero _)
                  exact Complex.ofReal_ne_zero.mpr (by positivity)
                · -- ContinuousOn deriv
                  apply (fdBoundary_H_deriv_continuousOn_Ioo_13 H).mono
                  intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
                · -- Injectivity
                  intro t ht hγt
                  have ht' : t ∈ Set.Ioo (1:ℝ) 3 :=
                    ⟨by linarith [ht.1], by linarith [ht.2]⟩
                  exact arc_angle_injective ht' ⟨ht₁_gt1, ht₁_lt3⟩
                    (by rw [fdBoundary_H_eq_arc ht'.1 ht'.2,
                        fdBoundary_H_eq_arc ht₁_gt1 ht₁_lt3] at hγt; exact hγt)
              -- Multi-concat: [0,(t₁+1)/2] + arc_cpv + [(t₁+3)/2,(t₀+4)/2] +
              --               seg5_cpv + [(t₀+5)/2, 5]
              -- Step 1: Avoidance on [0, (t₁+1)/2]
              have h_avoid_start : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
                  (fdBoundary_H H) 0 ((t₁ + 1) / 2) s := by
                apply cpv_avoidance _ _ _ _ _
                  (fdBoundary_H_continuous H).continuousOn (by linarith)
                intro t ht h_eq
                by_cases ht0 : t = 0
                · subst ht0; exact hs_endpoint (by rw [← h_eq, fdBoundary_H_at_zero])
                · by_cases ht1 : t ≤ 1
                  · have h_im_t : (fdBoundary_H H t).im < H := by
                      rw [fdBoundary_H_eq_seg1_H ht1]
                      simp [fdBoundary_seg1_H, Complex.add_im, Complex.ofReal_im,
                        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
                      nlinarith [ht.1, lt_of_le_of_ne ht.1 (Ne.symm ht0)]
                    rw [h_eq] at h_im_t; linarith [h_im_s]
                  · push_neg at ht1
                    have ht3 : t < 3 := by linarith [ht.2]
                    have h_ne : t ≠ t₁ := by linarith [ht.2]
                    exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₁_gt1, ht₁_lt3⟩
                      (by have := h_eq.trans hγt₁.symm
                          rwa [fdBoundary_H_eq_arc ht1 ht3,
                            fdBoundary_H_eq_arc ht₁_gt1 ht₁_lt3] at this))
              -- Step 2: CPV on [0, (t₁+3)/2]
              have h_cpv_0_t1h : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
                  (fdBoundary_H H) 0 ((t₁ + 3) / 2) s := by
                apply cpv_concat _ _ 0 ((t₁ + 1) / 2) ((t₁ + 3) / 2) s
                  h_avoid_start h_arc_cpv (by linarith) (by linarith)
                intro ε hε; exact (fdBoundary_H_cutout_ii H hH s ε hε).mono_set (by
                  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ (t₁ + 3) / 2),
                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
                  exact Set.Icc_subset_Icc_right (by linarith))
              -- Step 3: Avoidance on [(t₁+3)/2, (t₀+4)/2]
              have h_avoid_mid : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
                  (fdBoundary_H H) ((t₁ + 3) / 2) ((t₀ + 4) / 2) s := by
                apply cpv_avoidance _ _ _ _ _
                  (fdBoundary_H_continuous H).continuousOn (by linarith)
                intro t ht h_eq
                by_cases ht3 : t < 3
                · have ht1 : 1 < t := by linarith [ht.1]
                  have h_ne : t ≠ t₁ := by linarith [ht.1]
                  exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₁_gt1, ht₁_lt3⟩
                    (by have := h_eq.trans hγt₁.symm
                        rwa [fdBoundary_H_eq_arc ht1 ht3,
                          fdBoundary_H_eq_arc ht₁_gt1 ht₁_lt3] at this))
                · push_neg at ht3
                  by_cases ht4 : t ≤ 4
                  · rcases eq_or_lt_of_le ht3 with rfl | ht3'
                    · rw [fdBoundary_H_at_three, fdBoundary_at_three] at h_eq
                      exact hs_rho h_eq.symm
                    · have := fdBoundary_H_seg4_re' H ht3' ht4
                      rw [h_eq] at this; linarith [h_re_s]
                  · push_neg at ht4
                    have := fdBoundary_H_seg5_re' H ht4 (by linarith [ht.2])
                    rw [h_eq] at this; linarith [h_re_s, ht.2]
              -- Step 4: CPV on [(t₁+3)/2, (t₀+5)/2] = avoidance + seg5 CPV
              have h_cpv_mid : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
                  (fdBoundary_H H) ((t₁ + 3) / 2) ((t₀ + 5) / 2) s := by
                apply cpv_concat _ _ ((t₁ + 3) / 2) ((t₀ + 4) / 2) ((t₀ + 5) / 2) s
                  h_avoid_mid h_seg5_cpv (by linarith) (by linarith)
                intro ε hε; exact (fdBoundary_H_cutout_ii H hH s ε hε).mono_set (by
                  rw [Set.uIcc_of_le (by linarith : (t₁ + 3) / 2 ≤ (t₀ + 5) / 2),
                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
                  exact Set.Icc_subset_Icc (by linarith) (by linarith))
              -- Step 5: CPV on [0, (t₀+5)/2]
              have h_cpv_0_t0h : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
                  (fdBoundary_H H) 0 ((t₀ + 5) / 2) s := by
                apply cpv_concat _ _ 0 ((t₁ + 3) / 2) ((t₀ + 5) / 2) s
                  h_cpv_0_t1h h_cpv_mid (by linarith) (by linarith)
                intro ε hε; exact (fdBoundary_H_cutout_ii H hH s ε hε).mono_set (by
                  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ (t₀ + 5) / 2),
                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
                  exact Set.Icc_subset_Icc_right (by linarith))
              -- Step 6: Avoidance on [(t₀+5)/2, 5]
              have h_cpv_end : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
                  (fdBoundary_H H) ((t₀ + 5) / 2) 5 s := by
                apply cpv_avoidance _ _ _ _ _
                  (fdBoundary_H_continuous H).continuousOn (by linarith)
                intro t ht h_eq
                have ht4 : 4 < t := by linarith [ht.1]
                have := fdBoundary_H_seg5_re' H ht4 ht.2
                rw [h_eq] at this; linarith [h_re_s, ht.1]
              -- Step 7: CPV on [0, 5]
              exact cpv_concat _ _ 0 ((t₀ + 5) / 2) 5 s h_cpv_0_t0h h_cpv_end
                (by linarith) (by linarith)
                (fun ε hε => fdBoundary_H_cutout_ii H hH s ε hε)
            · -- normSq(s) ≠ 1: no arc crossing, simple extension.
              apply cpv_extend_to_full_interval H hH s ((t₀ + 4) / 2) ((t₀ + 5) / 2)
                (by linarith) (by linarith) (by linarith) h_seg5_cpv
              · -- Avoidance on [0, (t₀+4)/2]
                intro t ht h_eq
                by_cases ht0 : t = 0
                · subst ht0; exact hs_endpoint (by rw [← h_eq, fdBoundary_H_at_zero])
                · by_cases ht1 : t ≤ 1
                  · -- seg1: im < H = s.im (for t > 0)
                    have h_im_t : (fdBoundary_H H t).im < H := by
                      rw [fdBoundary_H_eq_seg1_H ht1]
                      simp [fdBoundary_seg1_H, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
                        Complex.I_re, Complex.I_im, Complex.ofReal_re]
                      nlinarith [ht.1, lt_of_le_of_ne ht.1 (Ne.symm ht0)]
                    rw [h_eq] at h_im_t; linarith [h_im_s]
                  · push_neg at ht1
                    by_cases ht3 : t < 3
                    · -- arc: normSq = 1 ≠ normSq(s)
                      have h_norm_arc : Complex.normSq (fdBoundary_H H t) = 1 := by
                        rw [fdBoundary_H_eq_arc ht1 ht3, Complex.normSq_apply,
                          Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
                        linarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t) / 6)]
                      rw [h_eq] at h_norm_arc; exact h_normSq h_norm_arc
                    · push_neg at ht3
                      by_cases ht4 : t ≤ 4
                      · rcases eq_or_lt_of_le ht3 with rfl | ht3'
                        · rw [fdBoundary_H_at_three, fdBoundary_at_three] at h_eq
                          exact hs_rho h_eq.symm
                        · -- seg4: re = -1/2 ≠ s.re
                          have := fdBoundary_H_seg4_re' H ht3' ht4
                          rw [h_eq] at this; linarith [h_re_s]
                      · push_neg at ht4
                        -- seg5 with t < t₀: re differs
                        have := fdBoundary_H_seg5_re' H ht4 (by linarith [ht.2])
                        rw [h_eq] at this; linarith [h_re_s, ht.2]
              · -- Avoidance on [(t₀+5)/2, 5]
                intro t ht h_eq
                have ht4 : 4 < t := by linarith [ht.1]
                have := fdBoundary_H_seg5_re' H ht4 ht.2
                rw [h_eq] at this; linarith [h_re_s, ht.1]

/-! ## Section 13: OnCurvePVProvider Wrapper -/

theorem fdBoundary_H_OnCurvePVProvider (hf : f ≠ 0) (S : Finset ℍ) :
    OnCurvePVProvider f S := by
  intro H hH s hs h_on
  exact fdBoundary_H_cpv_exists_of_onCurve H hH s h_on

end
