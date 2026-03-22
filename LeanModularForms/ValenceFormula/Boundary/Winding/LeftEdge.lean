/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ValenceFormula.Boundary.Winding.RightEdge

/-!
# Generalized Winding Number at Left Edge Points

Proves `generalizedWindingNumber' (fdBoundary_H H) 0 5 s = -1/2` for points `s`
on the left vertical edge of the fundamental domain (`s.re = -1/2`, `√3/2 < s.im < H`).
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

private lemma leftEdge_t₀_mem_Ioo (H : ℝ) (_hH_sqrt : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    3 + (s.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) ∈ Ioo (3 : ℝ) 4 := by
  have hα_pos : 0 < H - Real.sqrt 3 / 2 := by linarith
  constructor
  · linarith [div_pos (by linarith : (0:ℝ) < s.im - Real.sqrt 3 / 2) hα_pos]
  · have : (s.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) < 1 :=
      (div_lt_one hα_pos).mpr (by linarith)
    linarith

private lemma leftEdge_h₃_eq {H : ℝ} {s : ℂ} (hs_re : s.re = -1/2) (t : ℝ) :
    fdBoundary_seg4_H H t - s =
      ↑(Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2) - s.im) * I := by
  simp only [fdBoundary_seg4_H]
  apply Complex.ext <;>
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, hs_re]

private lemma leftEdge_dist_from_rightVertical (s : ℂ) (hs_re : s.re = -1/2)
    (z : ℂ) (hz_re : z.re = 1/2) : 1 ≤ ‖z - s‖ := by
  have hre : (z - s).re = 1 := by simp [Complex.sub_re, hz_re, hs_re]; ring
  calc 1 = |(z - s).re| := by rw [hre]; norm_num
    _ ≤ ‖z - s‖ := abs_re_le_norm (z - s)

private lemma leftEdge_min_dist_pos (s : ℂ) (hs_norm : ‖s‖ > 1) (hs_im : s.im < H) :
    0 < min (min (‖s‖ - 1) 1) (H - s.im) :=
  lt_min (lt_min (by linarith) one_pos) (by linarith)

private lemma leftEdge_min_dist_from_non_seg4 (H : ℝ) (s : ℂ) (hs_re : s.re = -1/2)
    (_hs_norm : ‖s‖ > 1) (_hs_im : s.im < H) (t : ℝ) (ht_seg4_left : t ≤ 3)
    (_ht_upper : t ≤ 5) :
    min (min (‖s‖ - 1) 1) (H - s.im) ≤ ‖fdBoundary_H H t - s‖ := by
  set d := min (min (‖s‖ - 1) 1) (H - s.im)
  by_cases h1 : t ≤ 1
  · rw [fdBoundary_H_eq_seg1_H h1]
    have hre : (fdBoundary_seg1_H H t).re = 1/2 := by
      simp [fdBoundary_seg1_H, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    calc d ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
      _ ≤ _ := leftEdge_dist_from_rightVertical s hs_re _ hre
  · push_neg at h1
    by_cases h3 : t ≤ 3
    · have h_on_arc : ‖fdBoundary_H H t‖ = 1 := by
        by_cases h2 : t ≤ 2
        · rw [fdBoundary_H_eq_seg2_H H h1 h2]
          simp only [fdBoundary_seg2_H, fdBoundary_seg2]
          rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
              ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I from by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
        · push_neg at h2
          rw [fdBoundary_H_eq_seg3_H H h2 h3]
          simp only [fdBoundary_seg3_H, fdBoundary_seg3]
          rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
              ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I
              from by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
      calc d ≤ ‖s‖ - 1 := le_trans (min_le_left _ _) (min_le_left _ _)
        _ ≤ _ := rightEdge_dist_from_arc s _ h_on_arc
    · exact absurd ht_seg4_left h3

private lemma leftEdge_min_dist_from_non_seg4_right (H : ℝ) (s : ℂ) (_hs_re : s.re = -1/2)
    (_hs_norm : ‖s‖ > 1) (hs_im : s.im < H) (t : ℝ) (ht4 : 4 < t) (_ht5 : t ≤ 5) :
    min (min (‖s‖ - 1) 1) (H - s.im) ≤ ‖fdBoundary_H H t - s‖ := by
  rw [fdBoundary_H_eq_seg5_H ht4]
  have him : (fdBoundary_seg5_H H t - s).im = H - s.im := by
    simp [fdBoundary_seg5_H, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  calc min (min (‖s‖ - 1) 1) (H - s.im)
      ≤ H - s.im := min_le_right _ _
    _ = |(fdBoundary_seg5_H H t - s).im| := by rw [him]; exact (abs_of_pos (by linarith)).symm
    _ ≤ ‖fdBoundary_seg5_H H t - s‖ := Complex.abs_im_le_norm _

set_option maxHeartbeats 8000000 in
private lemma leftEdge_winding_aux (H : ℝ) (hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = -1/2) (hs_norm : ‖s‖ > 1)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∫ t in (0:ℝ)..5, if ‖fdBoundary_H H t - s‖ > ε then
        (fdBoundary_H H t - s)⁻¹ * deriv (fun u => fdBoundary_H H u - s) t else 0) =
      -(↑Real.pi * I) := by
  set g : ℝ → ℂ := fun t => fdBoundary_H H t - s with hg_def
  set α := H - Real.sqrt 3 / 2 with hα_def
  set t₀ := 3 + (s.im - Real.sqrt 3 / 2) / α with ht₀_def
  have hα_pos : 0 < α := by rw [hα_def]; linarith
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  have ht₀_Ioo := leftEdge_t₀_mem_Ioo H hH_sqrt s hs_im_lower hs_im
  have ht₀_gt3 : 3 < t₀ := ht₀_Ioo.1
  have ht₀_lt4 : t₀ < 4 := ht₀_Ioo.2
  have ht₀_sub3_pos : 0 < t₀ - 3 := by linarith
  have ht₀_sub3_lt1 : t₀ - 3 < 1 := by linarith
  have ht₀_mul : (t₀ - 3) * α = s.im - Real.sqrt 3 / 2 := by
    simp only [ht₀_def, add_sub_cancel_left]
    exact div_mul_cancel₀ _ hα_ne
  set h₀ : ℝ → ℂ := fun t => fdBoundary_seg1_H H t - s
  set h_arc : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - s
  set h₃ : ℝ → ℂ := fun t => fdBoundary_seg4_H H t - s
  set h₅ : ℝ → ℂ := fun t => fdBoundary_seg5_H H t - s
  have hd₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑α : ℂ) * I) t := by
    intro t; exact (hasDerivAt_fdBoundary_seg1_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp [hα_def])
  have hd_arc : ∀ t : ℝ, HasDerivAt h_arc
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t :=
    hasDerivAt_arc_rep s
  have hd₃ : ∀ t : ℝ, HasDerivAt h₃ ((↑α : ℂ) * I) t := by
    intro t; exact (hasDerivAt_fdBoundary_seg4_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp [hα_def])
  have hd₅ : ∀ t : ℝ, HasDerivAt h₅ 1 t := by
    intro t; exact (hasDerivAt_fdBoundary_seg5_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp)
  have hg_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := by
    intro t ht; simp only [hg_def, h₀]; rw [fdBoundary_H_eq_seg1_H ht]
  have hg_arc : ∀ t, 1 < t → t < 3 → g t = h_arc t := by
    intro t ht1 ht3; simp only [hg_def, h_arc]; rw [fdBoundary_H_eq_arc ht1 ht3]
  have hg_h₃ : ∀ t, 3 < t → t ≤ 4 → g t = h₃ t := by
    intro t ht3 ht4; simp only [hg_def, h₃]
    rw [fdBoundary_H_eq_seg4_H ht3 ht4]
  have hg_h₅ : ∀ t, 4 < t → g t = h₅ t := by
    intro t ht4; simp only [hg_def, h₅]
    rw [fdBoundary_H_eq_seg5_H ht4]
  have hep_01 : h₀ 0 = h₅ 5 := by
    simp only [h₀, h₅, fdBoundary_seg1_H, fdBoundary_seg5_H]; push_cast; ring
  have hep_1 : h₀ 1 = h_arc 1 := by
    simp only [h₀, h_arc, fdBoundary_seg1_H]
    rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
        exp_real_angle_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  have hep_3 : h_arc 3 = h₃ 3 := by
    simp only [h_arc, h₃, fdBoundary_seg4_H]
    rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 from by ring,
        exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
    push_cast; ring
  have hep_4 : h₃ 4 = h₅ 4 := by
    simp only [h₃, h₅, fdBoundary_seg4_H, fdBoundary_seg5_H]; push_cast; ring
  have hderiv_01 : ∀ t ∈ Ioo (0:ℝ) 1, deriv g t = deriv h₀ t := by
    intro t ⟨_, ht1⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Iio_mem_nhds ht1) (fun s hs => hg_h₀ s (le_of_lt hs)))
  have hderiv_arc : ∀ t ∈ Ioo (1:ℝ) 3, deriv g t = deriv h_arc t := by
    intro t ⟨ht1, ht3⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds ht1 ht3) (fun s hs => hg_arc s hs.1 hs.2))
  have hderiv_3 : ∀ t ∈ Ioo (3:ℝ) 4, deriv g t = deriv h₃ t := by
    intro t ⟨ht3, ht4⟩
    exact Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Ioo_mem_nhds ht3 ht4)
        (fun s hs => hg_h₃ s hs.1 (le_of_lt hs.2)))
  have hderiv_5 : ∀ t ∈ Ioo (4:ℝ) 5, deriv g t = deriv h₅ t := by
    intro t ⟨ht4, _⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioi_mem_nhds ht4) (fun s hs => hg_h₅ s hs))
  have hslit₀ : ∀ t ∈ Icc (0:ℝ) 1, h₀ t ∈ Complex.slitPlane := by
    intro t _
    rw [Complex.mem_slitPlane_iff]; left
    simp only [h₀, fdBoundary_seg1_H, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero]
    rw [hs_re]; norm_num
  have hslit_arc : ∀ t ∈ Icc (1:ℝ) 3, h_arc t ∈ Complex.slitPlane := by
    intro t ⟨ht1, ht3⟩
    rw [Complex.mem_slitPlane_iff]
    simp only [h_arc]
    set θ := Real.pi * (1 + t) / 6 with hθ_def
    have hθ_lower : Real.pi / 3 ≤ θ := by simp only [hθ_def]; nlinarith [Real.pi_pos]
    have hθ_upper : θ ≤ 2 * Real.pi / 3 := by simp only [hθ_def]; nlinarith [Real.pi_pos]
    by_cases h3_eq : t = 3
    · right
      subst h3_eq
      show (cexp (↑(Real.pi * (1 + 3) / 6) * I) - s).im ≠ 0
      rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 from by ring,
          exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
      linarith [hs_im_lower]
    · left
      have ht3_strict : t < 3 := lt_of_le_of_ne ht3 h3_eq
      have hθ_strict : θ < 2 * Real.pi / 3 := by simp only [hθ_def]; nlinarith [Real.pi_pos]
      show 0 < (cexp (↑θ * I) - s).re
      simp only [Complex.sub_re, exp_ofReal_mul_I_re]
      rw [hs_re]
      have hcos_gt : Real.cos θ > -(1 / 2) := by
        have h := Real.cos_lt_cos_of_nonneg_of_le_pi
          (le_of_lt (by nlinarith [Real.pi_pos])) (by nlinarith [Real.pi_pos]) hθ_strict
        rw [cos_two_pi_div_three] at h; linarith
      linarith
  have hslit₃_left : ∀ δ', 0 < δ' → δ' < t₀ - 3 →
      ∀ t ∈ Icc (3:ℝ) (t₀ - δ'), h₃ t ∈ Complex.slitPlane := by
    intro δ' hδ' hδ't₀ t ⟨ht3, htd⟩
    rw [Complex.mem_slitPlane_iff]; right
    show (fdBoundary_seg4_H H t - s).im ≠ 0
    rw [leftEdge_h₃_eq hs_re]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
    have : (t - 3) * α < s.im - Real.sqrt 3 / 2 := by
      calc (t - 3) * α ≤ (t₀ - δ' - 3) * α := by nlinarith
        _ = (t₀ - 3) * α - δ' * α := by ring
        _ = (s.im - Real.sqrt 3 / 2) - δ' * α := by rw [ht₀_mul]
        _ < s.im - Real.sqrt 3 / 2 := by nlinarith
    rw [hα_def] at this; intro h; linarith
  have hslit₃_right : ∀ δ', 0 < δ' → δ' < 4 - t₀ →
      ∀ t ∈ Icc (t₀ + δ') 4, h₃ t ∈ Complex.slitPlane := by
    intro δ' hδ' hδ'4 t ⟨htd, ht4⟩
    rw [Complex.mem_slitPlane_iff]; right
    show (fdBoundary_seg4_H H t - s).im ≠ 0
    rw [leftEdge_h₃_eq hs_re]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
    have : (t - 3) * α > s.im - Real.sqrt 3 / 2 := by
      calc (t - 3) * α ≥ (t₀ + δ' - 3) * α := by nlinarith
        _ = (t₀ - 3) * α + δ' * α := by ring
        _ = (s.im - Real.sqrt 3 / 2) + δ' * α := by rw [ht₀_mul]
        _ > s.im - Real.sqrt 3 / 2 := by nlinarith
    rw [hα_def] at this; intro h; linarith
  have hslit₅ : ∀ t ∈ Icc (4:ℝ) 5, h₅ t ∈ Complex.slitPlane := by
    intro t ⟨ht4, ht5⟩
    rw [Complex.mem_slitPlane_iff]
    simp only [h₅, fdBoundary_seg5_H]
    by_cases ht4_eq : t = 4
    · right
      subst ht4_eq
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      linarith
    · left
      have : 4 < t := lt_of_le_of_ne ht4 (Ne.symm ht4_eq)
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      rw [hs_re]; linarith
  set d := min (min (‖s‖ - 1) 1) (H - s.im)
  have hd_pos : 0 < d := leftEdge_min_dist_pos s hs_norm hs_im
  set ε₀ := min d (min (d * α) (min ((t₀ - 3) * α) ((4 - t₀) * α)))
  have hε₀_pos : 0 < ε₀ := by
    refine lt_min hd_pos (lt_min (mul_pos hd_pos hα_pos)
      (lt_min (mul_pos ht₀_sub3_pos hα_pos) (mul_pos (by linarith) hα_pos)))
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Ioo 0 ε₀, Ioo_mem_nhdsGT hε₀_pos, fun ε hε => ?_⟩
  obtain ⟨hε_pos, hε_lt⟩ := hε
  have hε_lt_d : ε < d := calc ε < ε₀ := hε_lt
      _ ≤ d := min_le_left _ _
  have hεα_lt_d : ε / α < d := by
    rw [div_lt_iff₀ hα_pos]
    calc ε < ε₀ := hε_lt
      _ ≤ min (d * α) (min ((t₀ - 3) * α) ((4 - t₀) * α)) := min_le_right _ _
      _ ≤ d * α := min_le_left _ _
  have hεα_lt_t₀m3 : ε / α < t₀ - 3 := by
    rw [div_lt_iff₀ hα_pos]
    calc ε < ε₀ := hε_lt
      _ ≤ min (d * α) (min ((t₀ - 3) * α) ((4 - t₀) * α)) := min_le_right _ _
      _ ≤ min ((t₀ - 3) * α) ((4 - t₀) * α) := min_le_right _ _
      _ ≤ (t₀ - 3) * α := min_le_left _ _
  have hεα_lt_4mt₀ : ε / α < 4 - t₀ := by
    rw [div_lt_iff₀ hα_pos]
    calc ε < ε₀ := hε_lt
      _ ≤ min (d * α) (min ((t₀ - 3) * α) ((4 - t₀) * α)) := min_le_right _ _
      _ ≤ min ((t₀ - 3) * α) ((4 - t₀) * α) := min_le_right _ _
      _ ≤ (4 - t₀) * α := min_le_right _ _
  set δ := ε / α with hδ_def
  have hδ_pos : 0 < δ := div_pos hε_pos hα_pos
  have hderiv_eq : deriv (fun u => fdBoundary_H H u - s) = deriv g := rfl
  rw [show (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ *
    deriv (fun u => fdBoundary_H H u - s) t else 0) =
    (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) from rfl]
  have piece₀ := ftc_log (by norm_num : (0:ℝ) ≤ 1)
    ((continuous_fdBoundary_seg1_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₀ t).differentiableAt)
    (by rw [show deriv h₀ = fun _ => -(↑α : ℂ) * I from funext fun t => (hd₀ t).deriv]
        exact continuousOn_const)
    hslit₀
  have h_arc_cont : Continuous h_arc := by
    simp only [h_arc]; exact (Continuous.cexp (by fun_prop)).sub continuous_const
  have piece₁ := ftc_log (by norm_num : (1:ℝ) ≤ 3)
    h_arc_cont.continuousOn (fun t _ => (hd_arc t).differentiableAt)
    (by rw [show deriv h_arc = fun t => ↑(Real.pi / 6) * I *
          exp (↑(Real.pi * (1 + t) / 6) * I) from funext fun t => (hd_arc t).deriv]
        exact (Continuous.mul continuous_const (Continuous.cexp (by fun_prop))).continuousOn)
    hslit_arc
  have piece₂ := ftc_log (by linarith : (3:ℝ) ≤ t₀ - δ)
    ((continuous_fdBoundary_seg4_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₃ t).differentiableAt)
    (by rw [show deriv h₃ = fun _ => (↑α : ℂ) * I from funext fun t => (hd₃ t).deriv]
        exact continuousOn_const)
    (hslit₃_left δ hδ_pos hεα_lt_t₀m3)
  have piece₃ := ftc_log (by linarith : t₀ + δ ≤ 4)
    ((continuous_fdBoundary_seg4_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₃ t).differentiableAt)
    (by rw [show deriv h₃ = fun _ => (↑α : ℂ) * I from funext fun t => (hd₃ t).deriv]
        exact continuousOn_const)
    (hslit₃_right δ hδ_pos hεα_lt_4mt₀)
  have piece₄ := ftc_log (by norm_num : (4:ℝ) ≤ 5)
    ((continuous_fdBoundary_seg5_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₅ t).differentiableAt)
    (by rw [show deriv h₅ = fun _ => (1 : ℂ) from funext fun t => (hd₅ t).deriv]
        exact continuousOn_const)
    hslit₅
  have h_ae₀ : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 1 →
      deriv h₀ t / h₀ t = deriv g t / g t := by
    have h_excl : ({0, 1} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr
        (by rw [compl_compl]; exact (Set.toFinite ({0, 1} : Set ℝ)).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht_mem
    have ht0 : 0 < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff]; left; linarith)
      · exact h
    have ht1 : t < 1 := by
      rcases eq_or_lt_of_le ht_mem.2 with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; right; linarith)
      · exact h
    rw [hg_h₀ t (le_of_lt ht1), hderiv_01 t ⟨ht0, ht1⟩]
  have h_ae_arc : ∀ᵐ t ∂volume, t ∈ Set.uIoc 1 3 →
      deriv h_arc t / h_arc t = deriv g t / g t := by
    have : ({1, 3} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr
        (by rw [compl_compl]; exact (Set.toFinite ({1, 3} : Set ℝ)).measure_zero volume)
    filter_upwards [this] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 3)] at ht_mem
    have ht1 : 1 < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; left; linarith)
      · exact h
    have ht3 : t < 3 := by
      rcases eq_or_lt_of_le ht_mem.2 with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; right; linarith)
      · exact h
    rw [hg_arc t ht1 ht3, hderiv_arc t ⟨ht1, ht3⟩]
  have h_ae₃ : ∀ a b : ℝ, 3 ≤ a → a < b → b ≤ 4 →
      ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → deriv h₃ t / h₃ t = deriv g t / g t := by
    intro a b ha_ge hab hb4
    have h_excl : ({a, b} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr
        (by rw [compl_compl]; exact (Set.toFinite ({a, b} : Set ℝ)).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht
    rw [Set.uIoc_of_le (le_of_lt hab)] at ht
    have ht_gt_a : a < t := by
      rcases eq_or_lt_of_le (le_of_lt ht.1) with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff]; left; linarith)
      · exact h
    have ht_lt_b : t < b := by
      rcases eq_or_lt_of_le ht.2 with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; right; linarith)
      · exact h
    have ht3 : 3 < t := by linarith
    have ht4 : t < 4 := by linarith
    rw [hg_h₃ t ht3 (le_of_lt ht4), hderiv_3 t ⟨ht3, ht4⟩]
  have h_ae₅ : ∀ᵐ t ∂volume, t ∈ Set.uIoc 4 5 →
      deriv h₅ t / h₅ t = deriv g t / g t := by
    have : ({4, 5} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr
        (by rw [compl_compl]; exact (Set.toFinite ({4, 5} : Set ℝ)).measure_zero volume)
    filter_upwards [this] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by norm_num : (4:ℝ) ≤ 5)] at ht_mem
    have ht4 : 4 < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; left; linarith)
      · exact h
    have ht5 : t < 5 := by
      rcases eq_or_lt_of_le ht_mem.2 with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; right; linarith)
      · exact h
    rw [hg_h₅ t ht4, hderiv_5 t ⟨ht4, ht5⟩]
  have hint₀ : IntervalIntegrable (fun t => deriv g t / g t) volume 0 1 :=
    piece₀.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae₀.mono (fun t ht hm => ht hm)))
  have hint_arc : IntervalIntegrable (fun t => deriv g t / g t) volume 1 3 :=
    piece₁.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae_arc.mono (fun t ht hm => ht hm)))
  have hint₃_left : IntervalIntegrable (fun t => deriv g t / g t) volume 3 (t₀ - δ) :=
    piece₂.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((h_ae₃ 3 (t₀ - δ) le_rfl (by linarith) (by linarith)).mono
        (fun t ht hm => ht hm)))
  have hint₃_right : IntervalIntegrable (fun t => deriv g t / g t) volume (t₀ + δ) 4 :=
    piece₃.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((h_ae₃ (t₀ + δ) 4 (by linarith) (by linarith) le_rfl).mono
        (fun t ht hm => ht hm)))
  have hint₅ : IntervalIntegrable (fun t => deriv g t / g t) volume 4 5 :=
    piece₄.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae₅.mono (fun t ht hm => ht hm)))
  have hint_left : IntervalIntegrable (fun t => deriv g t / g t) volume 0 (t₀ - δ) :=
    hint₀.trans hint_arc |>.trans hint₃_left
  have hint_right : IntervalIntegrable (fun t => deriv g t / g t) volume (t₀ + δ) 5 :=
    hint₃_right.trans hint₅
  set F := fun t => if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else (0 : ℂ)
  have hF_left : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 (t₀ - δ) →
      F t = deriv g t / g t := by
    have h_excl : ({0, t₀ - δ} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr
        (by rw [compl_compl]; exact (Set.toFinite ({0, t₀ - δ} : Set ℝ)).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ t₀ - δ)] at ht_mem
    have h_norm_gt : ‖g t‖ > ε := by
      by_cases ht3 : t ≤ 3
      · have ht5 : t ≤ 5 := by linarith
        have : d ≤ ‖g t‖ := by
          show d ≤ ‖fdBoundary_H H t - s‖
          exact leftEdge_min_dist_from_non_seg4 H s hs_re hs_norm hs_im t ht3 ht5
        linarith [hε_lt_d]
      · push_neg at ht3
        have ht4 : t ≤ 4 := by linarith [ht_mem.2]
        show ‖fdBoundary_H H t - s‖ > ε
        rw [fdBoundary_H_eq_seg4_H ht3 ht4]
        rw [leftEdge_h₃_eq hs_re]
        rw [norm_mul, Complex.norm_real, Complex.norm_I,
          mul_one, Real.norm_eq_abs]
        have ht_lt_t₀mδ : t < t₀ - δ := by
          rcases eq_or_lt_of_le ht_mem.2 with h | h
          · exfalso; exact ht_ne (by
              simp [Set.mem_insert_iff,
                Set.mem_singleton_iff]; right; exact h)
          · exact h
        have h_im_neg : Real.sqrt 3 / 2 + (t - 3) * α - s.im < 0 := by
          have : (t - 3) * α < (t₀ - δ - 3) * α :=
            mul_lt_mul_of_pos_right (by linarith) hα_pos
          have : (t₀ - δ - 3) * α = (t₀ - 3) * α - δ * α := by ring
          have := mul_pos hδ_pos hα_pos; linarith [ht₀_mul]
        rw [abs_of_neg h_im_neg]
        have hε_eq : ε = δ * α := by rw [hδ_def]; field_simp
        have : (t - 3) * α < (t₀ - δ - 3) * α := mul_lt_mul_of_pos_right (by linarith) hα_pos
        have : (t₀ - δ - 3) * α = (t₀ - 3) * α - δ * α := by ring
        linarith [ht₀_mul]
    show F t = deriv g t / g t
    simp only [F, if_pos h_norm_gt]
    rw [div_eq_mul_inv, mul_comm]
  have hF_right : ∀ᵐ t ∂volume, t ∈ Set.uIoc (t₀ + δ) 5 →
      F t = deriv g t / g t := by
    have h_boundary : ({t₀ + δ, 5} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr
        (by rw [compl_compl]; exact (Set.toFinite ({t₀ + δ, 5} : Set ℝ)).measure_zero volume)
    filter_upwards [h_boundary] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by linarith : t₀ + δ ≤ 5)] at ht_mem
    have h_norm_gt : ‖g t‖ > ε := by
      by_cases ht4 : t ≤ 4
      · show ‖fdBoundary_H H t - s‖ > ε
        rw [fdBoundary_H_eq_seg4_H (by linarith [ht_mem.1]) ht4]
        rw [leftEdge_h₃_eq hs_re]
        rw [norm_mul, Complex.norm_real, Complex.norm_I,
          mul_one, Real.norm_eq_abs]
        have h_tα : (t₀ + δ - 3) * α < (t - 3) * α :=
          mul_lt_mul_of_pos_right (by linarith [ht_mem.1]) hα_pos
        have h_expand : (t₀ + δ - 3) * α = (t₀ - 3) * α + δ * α := by ring
        have hε_eq : ε = δ * α := by rw [hδ_def]; field_simp
        have h_im_pos : Real.sqrt 3 / 2 + (t - 3) * α - s.im > 0 := by linarith [ht₀_mul]
        rw [abs_of_pos h_im_pos]; linarith [ht₀_mul]
      · push_neg at ht4
        have : d ≤ ‖g t‖ := by
          show d ≤ ‖fdBoundary_H H t - s‖
          exact leftEdge_min_dist_from_non_seg4_right H s hs_re hs_norm hs_im t ht4 ht_mem.2
        linarith [hε_lt_d]
    show F t = deriv g t / g t
    simp only [F, if_pos h_norm_gt]
    rw [div_eq_mul_inv, mul_comm]
  have hF_mid : ∀ t ∈ Set.uIoc (t₀ - δ) (t₀ + δ), F t = 0 := by
    intro t ht_mem
    rw [Set.uIoc_of_le (by linarith : t₀ - δ ≤ t₀ + δ)] at ht_mem
    simp only [F]
    have h_norm : ‖g t‖ ≤ ε := by
      show ‖fdBoundary_H H t - s‖ ≤ ε
      rw [fdBoundary_H_eq_seg4_H (by linarith [ht_mem.1])
          (by linarith [ht_mem.2, hεα_lt_4mt₀])]
      rw [leftEdge_h₃_eq hs_re]
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_le]
      have hε_eq : ε = δ * α := by rw [hδ_def]; field_simp
      have h_upper : (t₀ + δ - 3) * α = (t₀ - 3) * α + δ * α := by ring
      have h_lower : (t₀ - δ - 3) * α = (t₀ - 3) * α - δ * α := by ring
      have h_tα_upper : (t - 3) * α ≤ (t₀ + δ - 3) * α :=
        mul_le_mul_of_nonneg_right (by linarith [ht_mem.2]) (le_of_lt hα_pos)
      have h_tα_lower : (t₀ - δ - 3) * α < (t - 3) * α :=
        mul_lt_mul_of_pos_right (by linarith [ht_mem.1]) hα_pos
      have h_conv : (t - 3) * (H - Real.sqrt 3 / 2) = (t - 3) * α := by rw [hα_def]
      constructor <;> linarith [ht₀_mul, h_conv]
    simp [if_neg (not_lt.mpr h_norm)]
  have hF_int₀ : IntervalIntegrable F volume 0 (t₀ - δ) :=
    hint_left.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_left.mono (fun t ht hm => (ht hm).symm)))
  have hF_int_mid : IntervalIntegrable F volume (t₀ - δ) (t₀ + δ) :=
    (IntervalIntegrable.zero (μ := volume) (a := t₀ - δ) (b := t₀ + δ)).congr
      (fun t ht => (hF_mid t ht).symm)
  have hF_int_right : IntervalIntegrable F volume (t₀ + δ) 5 :=
    hint_right.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_right.mono (fun t ht hm => (ht hm).symm)))
  have h_split : ∫ t in (0:ℝ)..5, F t =
      (∫ t in (0:ℝ)..(t₀ - δ), F t) + (∫ t in (t₀ - δ)..(t₀ + δ), F t) +
      (∫ t in (t₀ + δ)..(5:ℝ), F t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hF_int₀.trans hF_int_mid) hF_int_right,
        ← intervalIntegral.integral_add_adjacent_intervals hF_int₀ hF_int_mid]
  have h_mid_zero : ∫ t in (t₀ - δ)..(t₀ + δ), F t = 0 := by
    rw [intervalIntegral.integral_congr_ae (ae_of_all _ (fun t ht => hF_mid t ht))]
    simp [intervalIntegral.integral_zero]
  have h_eq_left : ∫ t in (0:ℝ)..(t₀ - δ), F t =
      ∫ t in (0:ℝ)..(t₀ - δ), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_left
  have h_eq_right : ∫ t in (t₀ + δ)..(5:ℝ), F t =
      ∫ t in (t₀ + δ)..(5:ℝ), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_right
  have h_ftc₀ : ∫ t in (0:ℝ)..(1:ℝ), deriv g t / g t =
      Complex.log (h₀ 1) - Complex.log (h₀ 0) := by
    rw [← piece₀.2, intervalIntegral.integral_congr_ae (h_ae₀.mono (fun t ht hm => ht hm))]
  have h_ftc_arc : ∫ t in (1:ℝ)..(3:ℝ), deriv g t / g t =
      Complex.log (h_arc 3) - Complex.log (h_arc 1) := by
    rw [← piece₁.2, intervalIntegral.integral_congr_ae (h_ae_arc.mono (fun t ht hm => ht hm))]
  have h_ftc₃_left : ∫ t in (3:ℝ)..(t₀ - δ), deriv g t / g t =
      Complex.log (h₃ (t₀ - δ)) - Complex.log (h₃ 3) := by
    rw [← piece₂.2, intervalIntegral.integral_congr_ae
      ((h_ae₃ 3 (t₀ - δ) le_rfl (by linarith) (by linarith)).mono (fun t ht hm => ht hm))]
  have h_ftc₃_right : ∫ t in (t₀ + δ)..(4:ℝ), deriv g t / g t =
      Complex.log (h₃ 4) - Complex.log (h₃ (t₀ + δ)) := by
    rw [← piece₃.2, intervalIntegral.integral_congr_ae
      ((h_ae₃ (t₀ + δ) 4 (by linarith) (by linarith) le_rfl).mono (fun t ht hm => ht hm))]
  have h_ftc₅ : ∫ t in (4:ℝ)..(5:ℝ), deriv g t / g t =
      Complex.log (h₅ 5) - Complex.log (h₅ 4) := by
    rw [← piece₄.2, intervalIntegral.integral_congr_ae (h_ae₅.mono (fun t ht hm => ht hm))]
  have h_left_total : ∫ t in (0:ℝ)..(t₀ - δ), deriv g t / g t =
      Complex.log (h₀ 1) - Complex.log (h₀ 0) + (Complex.log (h_arc 3) - Complex.log (h_arc 1)) +
      (Complex.log (h₃ (t₀ - δ)) - Complex.log (h₃ 3)) := by
    have h_split_left : (∫ t in (0:ℝ)..(t₀ - δ), deriv g t / g t) =
      (∫ t in (0:ℝ)..(1:ℝ), deriv g t / g t) + (∫ t in (1:ℝ)..(3:ℝ), deriv g t / g t) +
      (∫ t in (3:ℝ)..(t₀ - δ), deriv g t / g t) := by
        have h1 : (∫ t in (0:ℝ)..(1:ℝ), deriv g t / g t) + (∫ t in (1:ℝ)..(3:ℝ), deriv g t / g t) =
            ∫ t in (0:ℝ)..(3:ℝ), deriv g t / g t := by
          rw [← intervalIntegral.integral_add_adjacent_intervals hint₀ hint_arc]
        have h2 : (∫ t in (0:ℝ)..(3:ℝ), deriv g t / g t) +
            (∫ t in (3:ℝ)..(t₀ - δ), deriv g t / g t) =
            ∫ t in (0:ℝ)..(t₀ - δ), deriv g t / g t := by
          rw [← intervalIntegral.integral_add_adjacent_intervals
            (hint₀.trans hint_arc) hint₃_left]
        rw [← h2, ← h1]
    rw [h_split_left, h_ftc₀, h_ftc_arc, h_ftc₃_left]
  have h_right_total : ∫ t in (t₀ + δ)..(5:ℝ), deriv g t / g t =
      Complex.log (h₃ 4) - Complex.log (h₃ (t₀ + δ)) +
      (Complex.log (h₅ 5) - Complex.log (h₅ 4)) := by
    have h_split_right : (∫ t in (t₀ + δ)..(5:ℝ), deriv g t / g t) =
      (∫ t in (t₀ + δ)..(4:ℝ), deriv g t / g t) + (∫ t in (4:ℝ)..(5:ℝ), deriv g t / g t) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals hint₃_right hint₅]
    rw [h_split_right, h_ftc₃_right, h_ftc₅]
  have h_telescope : Complex.log (h₀ 1) - Complex.log (h₀ 0) +
      (Complex.log (h_arc 3) - Complex.log (h_arc 1)) +
      (Complex.log (h₃ (t₀ - δ)) - Complex.log (h₃ 3)) +
      (Complex.log (h₃ 4) - Complex.log (h₃ (t₀ + δ)) + (Complex.log (h₅ 5) - Complex.log (h₅ 4))) =
      Complex.log (h₃ (t₀ - δ)) - Complex.log (h₃ (t₀ + δ)) := by
    rw [hep_1, hep_3, hep_4, hep_01]; ring
  show ∫ t in (0:ℝ)..5, (if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) =
      -(↑Real.pi * I)
  have h_step1 : ∫ t in (0:ℝ)..5, (if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) =
      (∫ t in (0:ℝ)..(t₀ - δ), deriv g t / g t) + (∫ t in (t₀ + δ)..(5:ℝ), deriv g t / g t) := by
    calc ∫ t in (0:ℝ)..5, (if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0)
        = ∫ t in (0:ℝ)..5, F t := rfl
      _ = _ + _ + _ := h_split
      _ = _ + 0 + _ := by rw [h_mid_zero]
      _ = _ := by rw [add_zero, h_eq_left, h_eq_right]
  rw [h_step1, h_left_total, h_right_total, h_telescope]
  have hval_minus : h₃ (t₀ - δ) = ↑(-(δ * α)) * I := by
    show fdBoundary_seg4_H H (t₀ - δ) - s = _
    rw [leftEdge_h₃_eq hs_re]
    have h_expand : (t₀ - δ - 3) * (H - Real.sqrt 3 / 2) = (t₀ - 3) * α - δ * α := by
      rw [hα_def]; ring
    have h_eq' : Real.sqrt 3 / 2 + (t₀ - δ - 3) * (H - Real.sqrt 3 / 2) - s.im = -(δ * α) := by
      rw [h_expand]; linarith [ht₀_mul]
    rw [h_eq']
  have hval_plus : h₃ (t₀ + δ) = ↑(δ * α) * I := by
    show fdBoundary_seg4_H H (t₀ + δ) - s = _
    rw [leftEdge_h₃_eq hs_re]
    have h_expand : (t₀ + δ - 3) * (H - Real.sqrt 3 / 2) = (t₀ - 3) * α + δ * α := by
      rw [hα_def]; ring
    have h_eq' : Real.sqrt 3 / 2 + (t₀ + δ - 3) * (H - Real.sqrt 3 / 2) - s.im = δ * α := by
      rw [h_expand]; linarith [ht₀_mul]
    rw [h_eq']
  rw [hval_minus, hval_plus]
  rw [show (↑(-(δ * α)) * I : ℂ) = -(↑(δ * α) * I) from by push_cast; ring]
  exact log_neg_rI_sub_log_rI (mul_pos hδ_pos hα_pos)

theorem gWN_fdBoundary_H_eq_neg_half_of_leftEdge (H : ℝ) (hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = -1/2) (hs_norm : ‖s‖ > 1)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 s = -1/2 := by
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  dsimp only []; simp only [sub_zero]
  have h_ev := leftEdge_winding_aux H hH_sqrt s hs_re hs_norm hs_im_lower hs_im
  have h_tendsto : Filter.Tendsto (fun ε => ∫ t in (0:ℝ)..5,
        if ‖(fdBoundary_H H t - s)‖ > ε then
          (fdBoundary_H H t - s)⁻¹ * deriv (fun u => fdBoundary_H H u - s) t else 0)
    (𝓝[>] 0) (𝓝 (-(↑Real.pi * I))) :=
    tendsto_const_nhds.congr' (h_ev.mono (fun _ h => h.symm))
  rw [h_tendsto.limUnder_eq]
  field_simp [Real.pi_ne_zero, I_ne_zero]

end
