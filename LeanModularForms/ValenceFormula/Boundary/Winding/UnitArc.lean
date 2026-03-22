/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ValenceFormula.Boundary.Winding.UnitArcHelpers

/-!
# Unit Arc Winding Number

Proves `generalizedWindingNumber' (fdBoundary_H H) 0 5 s = -1/2` for points `s`
on the unit circle arc (`‖s‖ = 1`, `|s.re| < 1/2`, `s.im > 0`).

Uses the helper lemmas from `UnitArcHelpers` together with log ratio/diff tendsto
and strict norm monotonicity on the arc.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

private lemma unitArc_log_ratio_tendsto (s : ℂ)
    (_hs_norm : ‖s‖ = 1) (_hs_re : |s.re| < 1/2) (_hs_im_pos : 0 < s.im)
    (t₀ : ℝ) (_ht₀_Ioo : t₀ ∈ Ioo (1:ℝ) 3) (_h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I)) :
    Tendsto (fun δ => Complex.log ( (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) /
      (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s))))
    (𝓝[>] 0) (𝓝 0) := by
  have h_ev : ∀ᶠ δ in nhdsWithin (0:ℝ) (Ioi 0), 0 < δ ∧ δ < 6 := by
    apply inter_mem self_mem_nhdsWithin
    exact nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 6))
  have h_log_exp : Tendsto (fun δ : ℝ => Complex.log (cexp (↑(-(Real.pi * δ / 6)) * I)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    rw [show (0 : ℂ) = Complex.log 1 from by simp]
    apply (continuousAt_clog (by simp [slitPlane])).tendsto.comp
    rw [show (1 : ℂ) = cexp (↑(-(Real.pi * 0 / 6)) * I) from by simp]
    exact Tendsto.mono_left (by fun_prop : Continuous _).continuousAt.tendsto nhdsWithin_le_nhds
  have h_agree : ∀ᶠ δ in nhdsWithin (0:ℝ) (Ioi 0),
      Complex.log (cexp (↑(-(Real.pi * δ / 6)) * I)) =
      Complex.log ( (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) /
        (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s))) := by
    apply h_ev.mono
    intro δ ⟨hδ_pos, hδ_small⟩
    rw [_h_s_arc]
    congr 1
    exact (unitArc_ratio_eq t₀ δ hδ_pos hδ_small).symm
  exact h_log_exp.congr' h_agree

private lemma unitArc_log_diff_tendsto (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1/2) (hs_im_pos : 0 < s.im)
    (t₀ : ℝ) (ht₀_Ioo : t₀ ∈ Ioo (1:ℝ) 3) (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I)) :
    Tendsto (fun δ =>
      Complex.log (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) -
      Complex.log (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s)))
    (𝓝[>] 0) (𝓝 0) := by
  have h_ratio := unitArc_log_ratio_tendsto s hs_norm hs_re hs_im_pos t₀ ht₀_Ioo h_s_arc
  have h_ev_agree : ∀ᶠ δ in nhdsWithin (0:ℝ) (Ioi 0),
      Complex.log (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) -
      Complex.log (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s)) =
      Complex.log ((exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) /
        (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s))) := by
    have h_ev : ∀ᶠ δ in nhdsWithin (0:ℝ) (Ioi 0),
        0 < δ ∧ δ < min (t₀ - 1) (3 - t₀) := by
      apply inter_mem self_mem_nhdsWithin
      exact nhdsWithin_le_nhds
        (Iio_mem_nhds (lt_min (by linarith [ht₀_Ioo.1]) (by linarith [ht₀_Ioo.2])))
    apply h_ev.mono; intro δ ⟨hδ_pos, hδ_small⟩
    have hδ_lt1 : δ < t₀ - 1 := lt_of_lt_of_le hδ_small (min_le_left _ _)
    have hδ_lt2 : δ < 3 - t₀ := lt_of_lt_of_le hδ_small (min_le_right _ _)
    set θ_m := Real.pi * (1 + (t₀ - δ)) / 6
    set θ₀' := Real.pi * (1 + t₀) / 6
    have hθ_lt : θ_m < θ₀' := by simp [θ_m, θ₀']; nlinarith [Real.pi_pos]
    have hθ_m_nn : 0 ≤ θ_m := by simp [θ_m]; nlinarith [Real.pi_pos, ht₀_Ioo.1]
    have hθ₀_le_pi : θ₀' ≤ Real.pi := by simp [θ₀']; nlinarith [Real.pi_pos, ht₀_Ioo.2]
    have hcos_m : Real.cos θ₀' < Real.cos θ_m :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hθ_m_nn hθ₀_le_pi hθ_lt
    have h_re_a : 0 < (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s).re := by
      rw [h_s_arc, exp_real_angle_I, exp_real_angle_I]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero, Complex.sub_re]
      show 0 < Real.cos θ_m - Real.cos θ₀'; linarith
    set θ_p := Real.pi * (1 + (t₀ + δ)) / 6
    have hθ_gt : θ₀' < θ_p := by simp [θ₀', θ_p]; nlinarith [Real.pi_pos]
    have hθ₀_nn : 0 ≤ θ₀' := by simp [θ₀']; nlinarith [Real.pi_pos, ht₀_Ioo.1]
    have hθ_p_le_pi : θ_p ≤ Real.pi := by simp [θ_p]; nlinarith [Real.pi_pos, ht₀_Ioo.2]
    have hcos_p : Real.cos θ_p < Real.cos θ₀' :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hθ₀_nn hθ_p_le_pi hθ_gt
    have h_re_b : 0 < (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s)).re := by
      rw [h_s_arc, exp_real_angle_I, exp_real_angle_I]
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_self, add_zero, neg_sub]
      show 0 < Real.cos θ₀' - Real.cos θ_p; linarith
    exact (log_div_of_re_pos h_re_a h_re_b).symm
  exact h_ratio.congr' (h_ev_agree.mono fun _ h => h.symm)

private lemma normSq_exp_sub (α β : ℝ) :
    Complex.normSq (exp (↑α * I) - exp (↑β * I)) = 2 - 2 * Real.cos (α - β) := by
  rw [Complex.normSq_apply]
  rw [exp_real_angle_I, exp_real_angle_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_self, add_zero,
    Complex.sub_re, Complex.add_im, Complex.mul_im, mul_one, Complex.sub_im]
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β,
    sq_nonneg (Real.sin α - Real.sin β), sq_nonneg (Real.cos α - Real.cos β)]

private lemma unitArc_normSq_at_offset (s : ℂ) (H : ℝ) (t₀ δ : ℝ)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (h_in_arc : 1 < t₀ + δ) (h_in_arc' : t₀ + δ < 3) :
    Complex.normSq (fdBoundary_H H (t₀ + δ) - s) = 2 - 2 * Real.cos (Real.pi * δ / 6) := by
  rw [fdBoundary_H_eq_arc h_in_arc h_in_arc', h_s_arc]
  rw [normSq_exp_sub]
  congr 1; congr 1; congr 1; ring

private lemma unitArc_norm_offset_symm (s : ℂ) (H : ℝ) (t₀ δ : ℝ)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (h_left_arc : 1 < t₀ - δ) (h_left_arc' : t₀ - δ < 3)
    (h_right_arc : 1 < t₀ + δ) (h_right_arc' : t₀ + δ < 3) :
    ‖fdBoundary_H H (t₀ - δ) - s‖ = ‖fdBoundary_H H (t₀ + δ) - s‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  rw [show t₀ - δ = t₀ + (-δ) from sub_eq_add_neg t₀ δ]
  rw [unitArc_normSq_at_offset s H t₀ (-δ) h_s_arc (by linarith) (by linarith)]
  rw [unitArc_normSq_at_offset s H t₀ δ h_s_arc h_right_arc h_right_arc']
  congr 1; congr 1; rw [show Real.pi * (-δ) / 6 = -(Real.pi * δ / 6) from by ring, Real.cos_neg]

private lemma unitArc_norm_strict_mono (s : ℂ) (H : ℝ) (t₀ : ℝ)
    (_ht₀_Ioo : t₀ ∈ Ioo (1:ℝ) 3) (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (δ₁ δ₂ : ℝ) (hδ₁_nn : 0 ≤ δ₁) (hδ₁₂ : δ₁ < δ₂) (hδ₂ : δ₂ < min (t₀ - 1) (3 - t₀)) :
    ‖fdBoundary_H H (t₀ + δ₁) - s‖ < ‖fdBoundary_H H (t₀ + δ₂) - s‖ := by
  have hδ₂_left : δ₂ < t₀ - 1 := lt_of_lt_of_le hδ₂ (min_le_left _ _)
  have hδ₂_right : δ₂ < 3 - t₀ := lt_of_lt_of_le hδ₂ (min_le_right _ _)
  have h1a : 1 < t₀ + δ₁ := by linarith [_ht₀_Ioo.1]
  have h3a : t₀ + δ₁ < 3 := by linarith
  have h1b : 1 < t₀ + δ₂ := by linarith [_ht₀_Ioo.1]
  have h3b : t₀ + δ₂ < 3 := by linarith
  have hns₁ := unitArc_normSq_at_offset s H t₀ δ₁ h_s_arc h1a h3a
  have hns₂ := unitArc_normSq_at_offset s H t₀ δ₂ h_s_arc h1b h3b
  have hφ₁_nn : 0 ≤ Real.pi * δ₁ / 6 := by positivity
  have hφ₂_le_pi : Real.pi * δ₂ / 6 ≤ Real.pi := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 6)]
    nlinarith [Real.pi_pos, _ht₀_Ioo.2]
  have hφ_lt : Real.pi * δ₁ / 6 < Real.pi * δ₂ / 6 := by nlinarith [Real.pi_pos]
  have hcos_lt : Real.cos (Real.pi * δ₂ / 6) < Real.cos (Real.pi * δ₁ / 6) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hφ₁_nn hφ₂_le_pi hφ_lt
  have hns_lt : Complex.normSq (fdBoundary_H H (t₀ + δ₁) - s) <
      Complex.normSq (fdBoundary_H H (t₀ + δ₂) - s) := by rw [hns₁, hns₂]; linarith
  rw [Complex.norm_def, Complex.norm_def]
  exact Real.sqrt_lt_sqrt (Complex.normSq_nonneg _) hns_lt

private lemma unitArc_norm_lt_of_abs_lt (s : ℂ) (H : ℝ) (t₀ : ℝ)
    (ht₀_Ioo : t₀ ∈ Ioo (1:ℝ) 3) (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (t₁ t₂ : ℝ) (ht₁_arc : 1 < t₁) (ht₁_arc' : t₁ < 3) (ht₂_arc : 1 < t₂) (ht₂_arc' : t₂ < 3)
    (habs : |t₁ - t₀| < |t₂ - t₀|) :
    ‖fdBoundary_H H t₁ - s‖ < ‖fdBoundary_H H t₂ - s‖ := by
  rw [show t₁ = t₀ + (t₁ - t₀) from by ring, show t₂ = t₀ + (t₂ - t₀) from by ring]
  have hns₁ := unitArc_normSq_at_offset s H t₀ (t₁ - t₀) h_s_arc (by linarith) (by linarith)
  have hns₂ := unitArc_normSq_at_offset s H t₀ (t₂ - t₀) h_s_arc (by linarith) (by linarith)
  have hcos₁ : Real.cos (Real.pi * (t₁ - t₀) / 6) =
      Real.cos (Real.pi * |t₁ - t₀| / 6) := by
    rcases le_or_gt (t₁ - t₀) 0 with h | h
    · rw [abs_of_nonpos h,
        show Real.pi * (t₁ - t₀) / 6 = -(Real.pi * (-(t₁ - t₀)) / 6) from by ring,
        Real.cos_neg]
    · rw [abs_of_pos h]
  have hcos₂ : Real.cos (Real.pi * (t₂ - t₀) / 6) =
      Real.cos (Real.pi * |t₂ - t₀| / 6) := by
    rcases le_or_gt (t₂ - t₀) 0 with h | h
    · rw [abs_of_nonpos h,
        show Real.pi * (t₂ - t₀) / 6 = -(Real.pi * (-(t₂ - t₀)) / 6) from by ring,
        Real.cos_neg]
    · rw [abs_of_pos h]
  have h_abs_bound : |t₂ - t₀| < 2 := by
    rw [abs_lt]; constructor <;> linarith [ht₀_Ioo.1, ht₀_Ioo.2]
  have hφ₁_nn : 0 ≤ Real.pi * |t₁ - t₀| / 6 := by positivity
  have hφ₂_le_pi : Real.pi * |t₂ - t₀| / 6 ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hφ_lt : Real.pi * |t₁ - t₀| / 6 < Real.pi * |t₂ - t₀| / 6 := by
    nlinarith [Real.pi_pos]
  have hcos_lt := Real.cos_lt_cos_of_nonneg_of_le_pi hφ₁_nn hφ₂_le_pi hφ_lt
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_lt_sqrt (Complex.normSq_nonneg _)
  rw [hns₁, hns₂, hcos₁, hcos₂]; linarith

private lemma unitArc_norm_pos_at_offset (s : ℂ) (H : ℝ) (t₀ δ : ℝ)
    (ht₀_Ioo : t₀ ∈ Ioo (1:ℝ) 3) (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (hδ_pos : 0 < δ) (hδ_small : δ < min (t₀ - 1) (3 - t₀)) :
    0 < ‖fdBoundary_H H (t₀ + δ) - s‖ := by
  have h0 : ‖fdBoundary_H H (t₀ + 0) - s‖ = 0 := by
    simp only [add_zero]
    rw [fdBoundary_H_eq_arc ht₀_Ioo.1 ht₀_Ioo.2, h_s_arc, sub_self, norm_zero]
  calc 0 = ‖fdBoundary_H H (t₀ + 0) - s‖ := h0.symm
    _ < ‖fdBoundary_H H (t₀ + δ) - s‖ :=
        unitArc_norm_strict_mono s H t₀ ht₀_Ioo h_s_arc 0 δ le_rfl hδ_pos hδ_small

private lemma unitArc_norm_continuous (s : ℂ) (H : ℝ) (t₀ : ℝ) :
    Continuous (fun δ : ℝ => ‖fdBoundary_H H (t₀ + δ) - s‖) :=
  continuous_norm.comp (((fdBoundary_H_continuous H).comp (continuous_const.add continuous_id')).sub
    continuous_const)

set_option maxHeartbeats 8000000 in
private lemma unitArc_winding_tendsto (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1/2) (hs_im_pos : 0 < s.im) :
    Tendsto (fun ε => ∫ t in (0:ℝ)..5, if ‖fdBoundary_H H t - s‖ > ε then
      (fdBoundary_H H t - s)⁻¹ * deriv (fun u => fdBoundary_H H u - s) t else 0)
    (𝓝[>] 0) (𝓝 (-(↑Real.pi * I))) := by
  set t₀ := 6 * Real.arccos s.re / Real.pi - 1 with ht₀_def
  have ht₀_Ioo := unitArc_t₀_mem_Ioo s hs_re hs_im_pos
  have ht₀_gt1 : 1 < t₀ := ht₀_Ioo.1
  have ht₀_lt3 : t₀ < 3 := ht₀_Ioo.2
  have hg_at_t₀ := unitArc_fdBoundary_eq H s hs_norm hs_re hs_im_pos
  have h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I) := by
    rw [← fdBoundary_H_eq_arc ht₀_Ioo.1 ht₀_Ioo.2]; exact hg_at_t₀.symm
  set g : ℝ → ℂ := fun t => fdBoundary_H H t - s with hg_def
  set d_min := min (min (1/2 - s.re) (s.re + 1/2)) (H - 1) with hd_min_def
  have hd_min_pos : 0 < d_min := unitArc_min_dist_pos s hs_norm hs_re hs_im_pos H hH
  set hw := min (t₀ - 1) (3 - t₀) with hhw_def
  have hhw_pos : 0 < hw := lt_min (by linarith [ht₀_Ioo.1]) (by linarith [ht₀_Ioo.2])
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro r hr
  have h_log_tends := unitArc_log_diff_tendsto s hs_norm hs_re hs_im_pos t₀ ht₀_Ioo h_s_arc
  rw [Metric.tendsto_nhdsWithin_nhds] at h_log_tends
  obtain ⟨δ₀, hδ₀_pos, hδ₀_spec⟩ := h_log_tends r hr
  set δ₁ := min δ₀ hw / 2 with hδ₁_def
  have hδ₁_pos : 0 < δ₁ := by positivity
  have hδ₁_lt_δ₀ : δ₁ < δ₀ := by
    simp only [hδ₁_def]; linarith [min_le_left δ₀ hw]
  have hδ₁_lt_hw : δ₁ < hw := by
    simp only [hδ₁_def]; linarith [min_le_right δ₀ hw]
  have hδ₁_left : 1 < t₀ - δ₁ := by linarith [lt_of_lt_of_le hδ₁_lt_hw (min_le_left _ _)]
  have hδ₁_right : t₀ + δ₁ < 3 := by
    linarith [lt_of_lt_of_le hδ₁_lt_hw (min_le_right _ _)]
  set ε₀ := ‖g (t₀ + δ₁)‖ with hε₀_def
  have hε₀_pos : 0 < ε₀ := by
    simp only [hε₀_def, hg_def]
    exact unitArc_norm_pos_at_offset s H t₀ δ₁ ht₀_Ioo h_s_arc hδ₁_pos hδ₁_lt_hw
  set ε₁ := min ε₀ d_min with hε₁_def
  have hε₁_pos : 0 < ε₁ := lt_min hε₀_pos hd_min_pos
  refine ⟨ε₁, hε₁_pos, fun {ε} hε_mem hε_dist => ?_⟩
  have hε_pos : 0 < ε := hε_mem
  have hε_lt : ε < ε₁ := by rwa [Real.dist_eq, sub_zero, abs_of_pos hε_pos] at hε_dist
  have hε_lt_ε₀ : ε < ε₀ := lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hε_lt_d : ε < d_min := lt_of_lt_of_le hε_lt (min_le_right _ _)
  have hφ_zero : ‖g (t₀ + 0)‖ = 0 := by
    simp only [add_zero, hg_def]; rw [hg_at_t₀]; simp
  have hφ_cont : Continuous (fun δ : ℝ => ‖g (t₀ + δ)‖) := by
    simp only [hg_def]; exact unitArc_norm_continuous s H t₀
  have h_ivt : ε ∈ (fun δ : ℝ => ‖g (t₀ + δ)‖) '' Icc 0 δ₁ := by
    apply intermediate_value_Icc (le_of_lt hδ₁_pos) hφ_cont.continuousOn
    constructor
    · rw [hφ_zero]; exact le_of_lt hε_pos
    · exact le_of_lt hε_lt_ε₀
  obtain ⟨δ', ⟨hδ'_nn, hδ'_le⟩, hδ'_eq⟩ := h_ivt
  have hδ'_pos : 0 < δ' := by
    rcases eq_or_lt_of_le hδ'_nn with h0 | h0
    · exfalso; rw [← h0] at hδ'_eq; dsimp only at hδ'_eq; rw [hφ_zero] at hδ'_eq; linarith
    · exact h0
  have hδ'_lt_hw : δ' < hw := lt_of_le_of_lt hδ'_le hδ₁_lt_hw
  have hδ'_lt_δ₀ : δ' < δ₀ := lt_of_le_of_lt hδ'_le hδ₁_lt_δ₀
  have h_sym : ‖g (t₀ - δ')‖ = ε := by
    rw [hg_def] at hδ'_eq ⊢
    rw [unitArc_norm_offset_symm s H t₀ δ' h_s_arc
      (by linarith [lt_of_lt_of_le hδ'_lt_hw (min_le_left _ _)])
      (by linarith [lt_of_lt_of_le hδ'_lt_hw (min_le_right _ _)])
      (by linarith [ht₀_Ioo.1]) (by linarith [lt_of_lt_of_le hδ'_lt_hw (min_le_right _ _)])]
    exact hδ'_eq
  have hδ'_left : 1 < t₀ - δ' := by linarith [lt_of_lt_of_le hδ'_lt_hw (min_le_left _ _)]
  have hδ'_right : t₀ + δ' < 3 := by linarith [lt_of_lt_of_le hδ'_lt_hw (min_le_right _ _)]
  have h_integrand_eq : (∫ t in (0:ℝ)..5, if ‖fdBoundary_H H t - s‖ > ε then
      (fdBoundary_H H t - s)⁻¹ * deriv g t else 0) =
    ∫ t in (0:ℝ)..5, if ‖g t‖ > ε then
      deriv g t / g t else 0 := by
    congr 1; ext t
    show (if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) =
      if ‖g t‖ > ε then deriv g t / g t else 0
    split_ifs with h
    · rw [mul_comm, div_eq_mul_inv]
    · rfl
  rw [h_integrand_eq]
  have h_arc_outside : ∀ t, 1 < t → t < 3 → δ' < |t - t₀| → ‖g t‖ > ε := by
    intro t ht1 ht3 habs
    show ε < ‖g t‖
    have hε_eq : ε = ‖g (t₀ + δ')‖ := by
      change _ = ‖g (t₀ + δ')‖; exact hδ'_eq.symm
    rw [hε_eq]; simp only [hg_def]
    exact unitArc_norm_lt_of_abs_lt s H t₀ ht₀_Ioo h_s_arc (t₀ + δ') t
      (by linarith) hδ'_right ht1 ht3
      (by rw [show t₀ + δ' - t₀ = δ' from by ring, abs_of_pos hδ'_pos]; exact habs)
  have h_arc_inside : ∀ t, 1 < t → t < 3 → |t - t₀| ≤ δ' → ‖g t‖ ≤ ε := by
    intro t ht1 ht3 habs
    rcases eq_or_lt_of_le habs with heq | hlt
    · have hε_eq : ε = ‖g (t₀ + δ')‖ := by
        change _ = ‖g (t₀ + δ')‖; exact hδ'_eq.symm
      rw [hε_eq]; simp only [hg_def]
      rw [show t = t₀ + (t - t₀) from by ring, Complex.norm_def, Complex.norm_def]
      apply le_of_eq; congr 1
      rw [unitArc_normSq_at_offset s H t₀ (t - t₀) h_s_arc (by linarith) (by linarith),
          unitArc_normSq_at_offset s H t₀ δ' h_s_arc (by linarith) hδ'_right]
      congr 1; congr 1
      rcases le_or_gt (t - t₀) 0 with h | h
      · have h_neg : t - t₀ = -δ' := by rw [abs_of_nonpos h] at heq; linarith
        rw [h_neg, show Real.pi * (-δ') / 6 = -(Real.pi * δ' / 6) from by ring, Real.cos_neg]
      · rw [abs_of_pos h] at heq; rw [heq]
    · have hε_eq : ε = ‖g (t₀ + δ')‖ := by
        change _ = ‖g (t₀ + δ')‖; exact hδ'_eq.symm
      rw [hε_eq]; simp only [hg_def]
      exact le_of_lt (unitArc_norm_lt_of_abs_lt s H t₀ ht₀_Ioo h_s_arc t (t₀ + δ')
        ht1 ht3 (by linarith) hδ'_right
        (by rw [show t₀ + δ' - t₀ = δ' from by ring, abs_of_pos hδ'_pos]; exact hlt))
  have h_off_arc_seg1 : ∀ t, t ≤ 1 → ‖g t‖ ≥ d_min := by
    intro t ht; simp only [hg_def, hd_min_def, ge_iff_le]
    calc min (min (1/2 - s.re) (s.re + 1/2)) (H - 1)
        ≤ 1/2 - s.re := le_trans (min_le_left _ _) (min_le_left _ _)
      _ ≤ ‖fdBoundary_H H t - s‖ := unitArc_min_dist_from_seg1 H s hs_re t ht
  have h_off_arc_right : ∀ t, 3 ≤ t → t ≤ 5 → ‖g t‖ ≥ d_min := by
    intro t ht3 ht5; simp only [hg_def, hd_min_def, ge_iff_le]
    exact unitArc_min_dist_from_non_arc H hH s hs_norm hs_re hs_im_pos t ht3 ht5
  have h_ftc := unitArc_ftc_value H hH s hs_norm hs_re hs_im_pos δ' hδ'_pos t₀ ht₀_Ioo
    h_s_arc hδ'_left hδ'_right
  set F := fun t => if ‖g t‖ > ε then deriv g t / g t else (0 : ℂ) with hF_def
  have hF_left : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 (t₀ - δ') → F t = deriv g t / g t := by
    have h_excl : ({t₀ - δ'} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite _).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ t₀ - δ')] at ht_mem
    have ht_lt : t < t₀ - δ' := lt_of_le_of_ne ht_mem.2
      (fun h => ht_ne (Set.mem_singleton_iff.mpr h))
    simp only [hF_def]
    have hgt : ‖g t‖ > ε := by
      by_cases h1 : t ≤ 1
      · calc ε < d_min := hε_lt_d
          _ ≤ ‖g t‖ := h_off_arc_seg1 t h1
      · push_neg at h1
        exact h_arc_outside t h1 (by linarith) (by rw [abs_of_nonpos (by linarith)]; linarith)
    simp only [if_pos hgt]
  have hF_right : ∀ᵐ t ∂volume, t ∈ Set.uIoc (t₀ + δ') 5 → F t = deriv g t / g t := by
    have h_excl : ({t₀ + δ'} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite _).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by linarith : t₀ + δ' ≤ 5)] at ht_mem
    have ht_gt : t₀ + δ' < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (Set.mem_singleton_iff.mpr (by linarith))
      · exact h
    simp only [hF_def]
    have hgt : ‖g t‖ > ε := by
      by_cases h3 : t < 3
      · exact h_arc_outside t (by linarith) h3 (by rw [abs_of_pos (by linarith)]; linarith)
      · push_neg at h3
        calc ε < d_min := hε_lt_d
          _ ≤ ‖g t‖ := h_off_arc_right t h3 ht_mem.2
    simp only [if_pos hgt]
  have hF_mid_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (t₀ - δ') (t₀ + δ') → F t = 0 := by
    apply Filter.Eventually.of_forall; intro t ht_mem
    rw [Set.uIoc_of_le (by linarith : t₀ - δ' ≤ t₀ + δ')] at ht_mem
    simp only [hF_def]
    rw [if_neg]; push_neg
    exact h_arc_inside t (by linarith [ht_mem.1]) (by linarith [ht_mem.2])
      (by rw [abs_le]; constructor <;> linarith [ht_mem.1, ht_mem.2])
  obtain ⟨hint_left, hint_right, h_ftc_eq⟩ := h_ftc
  have hF_int_left : IntervalIntegrable F volume 0 (t₀ - δ') :=
    hint_left.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_left.mono (fun t ht hm => (ht hm).symm)))
  have hF_int_mid : IntervalIntegrable F volume (t₀ - δ') (t₀ + δ') := by
    have hF_mid : ∀ t ∈ Set.uIoc (t₀ - δ') (t₀ + δ'), F t = 0 := by
      intro t ht_mem
      rw [Set.uIoc_of_le (by linarith : t₀ - δ' ≤ t₀ + δ')] at ht_mem
      simp only [hF_def]
      rw [if_neg]; push_neg
      exact h_arc_inside t (by linarith [ht_mem.1]) (by linarith [ht_mem.2])
        (by rw [abs_le]; constructor <;> linarith [ht_mem.1, ht_mem.2])
    exact (IntervalIntegrable.zero (μ := volume) (a := t₀ - δ') (b := t₀ + δ')).congr
      (fun t ht => (hF_mid t ht).symm)
  have hF_int_right : IntervalIntegrable F volume (t₀ + δ') 5 :=
    hint_right.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_right.mono (fun t ht hm => (ht hm).symm)))
  have h_split : ∫ t in (0:ℝ)..5, F t =
      (∫ t in (0:ℝ)..(t₀ - δ'), F t) + (∫ t in (t₀ - δ')..(t₀ + δ'), F t) +
      (∫ t in (t₀ + δ')..(5:ℝ), F t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hF_int_left.trans hF_int_mid) hF_int_right,
        ← intervalIntegral.integral_add_adjacent_intervals hF_int_left hF_int_mid]
  have h_mid_zero : ∫ t in (t₀ - δ')..(t₀ + δ'), F t = 0 := by
    rw [intervalIntegral.integral_congr_ae hF_mid_ae]
    simp [intervalIntegral.integral_zero]
  have h_eq_left : ∫ t in (0:ℝ)..(t₀ - δ'), F t =
      ∫ t in (0:ℝ)..(t₀ - δ'), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_left
  have h_eq_right : ∫ t in (t₀ + δ')..(5:ℝ), F t =
      ∫ t in (t₀ + δ')..(5:ℝ), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_right
  have h_integral_eq : ∫ t in (0:ℝ)..5, F t =
      Complex.log ((fdBoundary_H H (t₀ - δ') - s) / (-(fdBoundary_H H (t₀ + δ') - s))) -
      ↑Real.pi * I := by
    rw [h_split, h_mid_zero, add_zero, h_eq_left, h_eq_right]
    exact h_ftc_eq
  show dist (∫ t in (0:ℝ)..5, F t) (-(↑Real.pi * I)) < r
  rw [h_integral_eq, dist_comm, dist_eq_norm]
  rw [show -(↑Real.pi * I) -
    (Complex.log ((fdBoundary_H H (t₀ - δ') - s) / (-(fdBoundary_H H (t₀ + δ') - s))) -
    ↑Real.pi * I) =
    -Complex.log ((fdBoundary_H H (t₀ - δ') - s) / (-(fdBoundary_H H (t₀ + δ') - s)))
    from by ring, norm_neg]
  rw [fdBoundary_H_eq_arc hδ'_left (by linarith : t₀ - δ' < 3),
      fdBoundary_H_eq_arc (by linarith : 1 < t₀ + δ') hδ'_right]
  set θ_m := Real.pi * (1 + (t₀ - δ')) / 6
  set θ₀' := Real.pi * (1 + t₀) / 6
  set θ_p := Real.pi * (1 + (t₀ + δ')) / 6
  have h_re_before : 0 < (exp (↑θ_m * I) - s).re := by
    rw [h_s_arc, exp_real_angle_I, exp_real_angle_I]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_self, add_zero]
    show 0 < Real.cos θ_m - Real.cos θ₀'
    have hθ_m_lt : θ_m < θ₀' := by simp [θ_m, θ₀']; nlinarith [Real.pi_pos]
    have hθ_m_nn : 0 ≤ θ_m := by simp [θ_m]; nlinarith [Real.pi_pos, ht₀_Ioo.1]
    have hθ₀_le_pi : θ₀' ≤ Real.pi := by simp [θ₀']; nlinarith [Real.pi_pos, ht₀_Ioo.2]
    linarith [Real.cos_lt_cos_of_nonneg_of_le_pi hθ_m_nn hθ₀_le_pi hθ_m_lt]
  have h_re_after : 0 < (-(exp (↑θ_p * I) - s)).re := by
    rw [h_s_arc, exp_real_angle_I, exp_real_angle_I]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_self, add_zero, neg_sub]
    show 0 < Real.cos θ₀' - Real.cos θ_p
    have hθ_gt : θ₀' < θ_p := by simp [θ₀', θ_p]; nlinarith [Real.pi_pos]
    have hθ₀_nn : 0 ≤ θ₀' := by simp [θ₀']; nlinarith [Real.pi_pos, ht₀_Ioo.1]
    have hθ_p_le_pi : θ_p ≤ Real.pi := by simp [θ_p]; nlinarith [Real.pi_pos, ht₀_Ioo.2]
    linarith [Real.cos_lt_cos_of_nonneg_of_le_pi hθ₀_nn hθ_p_le_pi hθ_gt]
  rw [log_div_of_re_pos h_re_before h_re_after]
  have hδ'_in_Ioi : δ' ∈ Ioi (0:ℝ) := hδ'_pos
  have hδ'_dist : dist δ' 0 < δ₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ'_pos]; exact hδ'_lt_δ₀
  have h_log_small := hδ₀_spec hδ'_in_Ioi hδ'_dist
  rw [dist_zero_right] at h_log_small
  convert h_log_small using 2

/-- **Main theorem**: gWN = −1/2 at smooth arc points. -/
theorem gWN_fdBoundary_H_eq_neg_half_of_unitArc (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1/2) (hs_im_pos : 0 < s.im) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 s = -1/2 := by
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  dsimp only []; simp only [sub_zero]
  have h_tendsto := unitArc_winding_tendsto H hH s hs_norm hs_re hs_im_pos
  rw [h_tendsto.limUnder_eq]
  field_simp [Real.pi_ne_zero, I_ne_zero]
