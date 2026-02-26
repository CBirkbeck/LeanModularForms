/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_InteriorWinding
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_Boundary_Param
import LeanModularForms.Modularforms.valence.ComplexAnalysis.HomotopyBridge

/-!
# Interior Winding Number for Height-Parameterized FD Boundary

Extends the base result `generalizedWindingNumber_fdBoundary_eq_neg_one` (which works at
canonical height `H_height`) to `fdBoundary_H H` for arbitrary `H ≥ H_height`.

## Main Result

* `gWN_fdBoundary_H_eq_neg_one_of_interior`:
  For `p` in the strict interior of the fundamental domain
  (`‖p‖ > 1`, `|p.re| < 1/2`, `0 < p.im`, `p.im < H_height`),
  and any height `H ≥ H_height`, we have
  `generalizedWindingNumber' (fdBoundary_H H) 0 5 p = -1`.

## Proof Strategy

We construct a linear homotopy `H(t,s) = fdBoundary_H(H_height + s*(H - H_height))(t)` from
`fdBoundary_H H_height` (at `s = 0`) to `fdBoundary_H H` (at `s = 1`),
and apply `windingNumber_eq_of_piecewise_homotopic` with partition `P = {1, 3, 4}`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval UpperHalfPlane

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Avoidance Lemma -/

/-- The FD boundary at height `H` avoids any interior point `p` with the given properties. -/
theorem fdBoundary_H_avoids_interior (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2)
    (_hp_im_pos : 0 < p.im) {H : ℝ} (hp_im : p.im < H) :
    ∀ t ∈ Icc (0:ℝ) 5, fdBoundary_H H t ≠ p := by
  intro t ht habs
  simp only [Icc, mem_setOf_eq] at ht
  by_cases h1 : t ≤ 1
  · -- seg1: re = 1/2, but |p.re| < 1/2
    have hre : (fdBoundary_H H t).re = 1/2 := by
      rw [fdBoundary_H_eq_seg1_H h1, fdBoundary_seg1_H]
      simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, div_ofNat, one_re]
      norm_num
    rw [habs] at hre
    have : |p.re| = |(1/2 : ℝ)| := by rw [hre]
    simp at this; linarith
  · push_neg at h1
    by_cases h2 : t ≤ 3
    · -- arc (t ∈ (1,3]): ‖z‖ = 1, but ‖p‖ > 1
      rcases eq_or_lt_of_le h2 with rfl | h2'
      · -- t = 3: fdBoundary_H H 3 = fdBoundary 3 which is on the unit circle
        rw [fdBoundary_H_at_three H] at habs
        have h3norm : ‖fdBoundary 3‖ = 1 := by
          unfold fdBoundary
          simp only [show ¬((3:ℝ) ≤ 1) from by norm_num, show ¬((3:ℝ) ≤ 2) from by norm_num,
            show (3:ℝ) ≤ 3 from le_refl 3, ↓reduceIte]
          have : (↑Real.pi / 2 + (↑(3:ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
            ↑(2 * Real.pi / 3) * I := by push_cast; ring
          rw [this, norm_exp_ofReal_mul_I]
        rw [habs] at h3norm; linarith
      · -- t ∈ (1, 3): on the arc, norm = 1
        have hnorm : ‖fdBoundary_H H t‖ = 1 :=
          (fdBoundary_H_eq_arc h1 h2').symm ▸ norm_exp_ofReal_mul_I _
        rw [habs] at hnorm; linarith
    · push_neg at h2
      by_cases h3 : t ≤ 4
      · -- seg4: re = -1/2, but |p.re| < 1/2
        have hre : (fdBoundary_H H t).re = -1/2 := by
          rw [fdBoundary_H_eq_seg4_H (show ¬(t ≤ 1) from by linarith) (show ¬(t ≤ 2) from by linarith)
            (show ¬(t ≤ 3) from by linarith) h3, fdBoundary_seg4_H]
          simp only [add_re, neg_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, div_ofNat, one_re]
          norm_num
        rw [habs] at hre
        have : |p.re| = |(-1/2 : ℝ)| := by rw [hre]
        simp at this; linarith
      · -- seg5: im = H, but p.im < H
        push_neg at h3
        have him : (fdBoundary_H H t).im = H := by
          rw [fdBoundary_H_eq_seg5_H (show ¬(t ≤ 1) from by linarith) (show ¬(t ≤ 2) from by linarith)
            (show ¬(t ≤ 3) from by linarith) (show ¬(t ≤ 4) from by linarith), fdBoundary_seg5_H]
          simp only [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, div_ofNat]
          norm_num
        rw [habs] at him; linarith

/-! ## Height Homotopy Infrastructure -/

/-- Height sensitivity: how `fdBoundary_H` changes with height. -/
private def heightSens : ℝ → ℂ := fun t =>
  if t ≤ 1 then ↑(1 - t) * I
  else if t ≤ 3 then 0
  else if t ≤ 4 then ↑(t - 3) * I
  else I

private lemma heightSens_continuous : Continuous heightSens := by
  unfold heightSens
  apply Continuous.if
  · intro t ht; rw [show {t : ℝ | t ≤ 1} = Set.Iic 1 from rfl, frontier_Iic] at ht
    simp only [mem_singleton_iff] at ht; subst ht
    simp only [show (1:ℝ) ≤ 3 from by norm_num, ↓reduceIte]; push_cast; ring
  · exact (continuous_ofReal.comp (by fun_prop)).mul continuous_const
  · apply Continuous.if
    · intro t ht; rw [show {t : ℝ | t ≤ 3} = Set.Iic 3 from rfl, frontier_Iic] at ht
      simp only [mem_singleton_iff] at ht; subst ht
      simp only [show (3:ℝ) ≤ 4 from by norm_num, ↓reduceIte]; push_cast; ring
    · exact continuous_const
    · apply Continuous.if
      · intro t ht; rw [show {t : ℝ | t ≤ 4} = Set.Iic 4 from rfl, frontier_Iic] at ht
        simp only [mem_singleton_iff] at ht; subst ht; push_cast; ring
      · exact (continuous_ofReal.comp (by fun_prop)).mul continuous_const
      · exact continuous_const

private lemma fdBoundary_H_decomp (H₀ H' : ℝ) (t : ℝ) :
    fdBoundary_H H' t = fdBoundary_H H₀ t + ↑(H' - H₀) * heightSens t := by
  unfold fdBoundary_H heightSens
  by_cases h1 : t ≤ 1
  · simp only [h1, ↓reduceIte]; push_cast; ring
  · push_neg at h1; by_cases h2 : t ≤ 2
    · simp only [not_le.mpr h1, h2, ↓reduceIte, show t ≤ 3 from by linarith]; ring
    · push_neg at h2; by_cases h3 : t ≤ 3
      · simp only [not_le.mpr h1, not_le.mpr h2, h3, ↓reduceIte]; ring
      · push_neg at h3; by_cases h4 : t ≤ 4
        · simp only [not_le.mpr h1, not_le.mpr h2, not_le.mpr h3, h4, ↓reduceIte]; push_cast; ring
        · simp only [not_le.mpr h1, not_le.mpr h2, not_le.mpr h3, h4, ↓reduceIte]; push_cast; ring

/-- Joint continuity of the height homotopy `(t, s) ↦ fdBoundary_H(H₀ + s*(H₁-H₀))(t)`. -/
private lemma fdHomot_continuous (H₀ H₁ : ℝ) :
    Continuous (fun (q : ℝ × ℝ) => fdBoundary_H (H₀ + q.2 * (H₁ - H₀)) q.1) := by
  have h_eq : (fun (q : ℝ × ℝ) => fdBoundary_H (H₀ + q.2 * (H₁ - H₀)) q.1) =
    fun q => fdBoundary_H H₀ q.1 + ↑(q.2 * (H₁ - H₀)) * heightSens q.1 := by
    ext q; rw [fdBoundary_H_decomp H₀]; ring_nf
  rw [h_eq]
  exact ((fdBoundary_H_continuous H₀).comp continuous_fst).add
    ((continuous_ofReal.comp (continuous_snd.mul continuous_const)).mul
      (heightSens_continuous.comp continuous_fst))

/-! ## Derivative Helpers for Homotopy -/

set_option maxHeartbeats 400000 in
private lemma fdHomot_deriv_continuousOn_piece (H₀ H₁ : ℝ) (p₁ p₂ : ℝ)
    (hfree : ∀ x ∈ Ioo p₁ p₂, x ∉ fdBoundary_H_partition) :
    ContinuousOn (fun q : ℝ × ℝ =>
      deriv (fun t => fdBoundary_H (H₀ + q.2 * (H₁ - H₀)) t) q.1)
      (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
  by_cases h_le1 : p₂ ≤ 1
  · apply ContinuousOn.congr
      (f := fun q : ℝ × ℝ =>
        -(↑(H₀ + q.2 * (H₁ - H₀) - Real.sqrt 3 / 2) : ℂ) * I)
    · exact ((continuous_ofReal.comp (by fun_prop :
        Continuous (fun q : ℝ × ℝ => H₀ + q.2 * (H₁ - H₀) - Real.sqrt 3 / 2))).neg.mul
        continuous_const).continuousOn
    · intro q hq
      exact (fdBoundary_H_hasDerivAt_seg1 _ (lt_of_lt_of_le hq.1.2 h_le1)).deriv
  · push_neg at h_le1
    have hp1_ge1 : 1 ≤ p₁ := by
      by_contra h; push_neg at h
      exact hfree 1 ⟨h, h_le1⟩ (by simp [fdBoundary_H_partition, Finset.mem_insert])
    by_cases h_le3 : p₂ ≤ 3
    · apply ContinuousOn.congr
        (f := fun q : ℝ × ℝ =>
          ↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * (1 + q.1) / 6) * I))
      · apply Continuous.continuousOn
        apply Continuous.mul continuous_const
        exact (continuous_ofReal.comp (by fun_prop)).mul continuous_const |>.cexp
      · intro q hq
        exact (fdBoundary_H_hasDerivAt_arc _
          (lt_of_le_of_lt hp1_ge1 hq.1.1)
          (lt_of_lt_of_le hq.1.2 h_le3)).deriv
    · push_neg at h_le3
      have hp1_ge3 : 3 ≤ p₁ := by
        by_contra h; push_neg at h
        exact hfree 3 ⟨by linarith, h_le3⟩
          (by simp [fdBoundary_H_partition, Finset.mem_insert, Finset.mem_singleton])
      by_cases h_le4 : p₂ ≤ 4
      · apply ContinuousOn.congr
          (f := fun q : ℝ × ℝ =>
            (↑(H₀ + q.2 * (H₁ - H₀) - Real.sqrt 3 / 2) : ℂ) * I)
        · exact ((continuous_ofReal.comp (by fun_prop :
            Continuous (fun q : ℝ × ℝ => H₀ + q.2 * (H₁ - H₀) - Real.sqrt 3 / 2))).mul
            continuous_const).continuousOn
        · intro q hq
          exact (fdBoundary_H_hasDerivAt_seg4 _
            (lt_of_le_of_lt hp1_ge3 hq.1.1)
            (lt_of_lt_of_le hq.1.2 h_le4)).deriv
      · push_neg at h_le4
        have hp1_ge4 : 4 ≤ p₁ := by
          by_contra h; push_neg at h
          exact hfree 4 ⟨by linarith, h_le4⟩
            (by simp [fdBoundary_H_partition, Finset.mem_insert, Finset.mem_singleton])
        apply ContinuousOn.congr (f := fun _ => (1 : ℂ))
        · exact continuousOn_const
        · intro q hq
          exact (fdBoundary_H_hasDerivAt_seg5 _
            (lt_of_le_of_lt hp1_ge4 hq.1.1)).deriv

set_option maxHeartbeats 400000 in
private lemma fdHomot_deriv_bound (H : ℝ) (hH : H_height ≤ H) :
    ∃ M, ∀ t ∈ Icc (0:ℝ) 5, ∀ s ∈ Icc (0:ℝ) 1,
      ‖deriv (fun t' => fdBoundary_H (H_height + s * (H - H_height)) t') t‖ ≤ M := by
  refine ⟨max (H - Real.sqrt 3 / 2) 1, fun t _ht s hs => ?_⟩
  set H_s := H_height + s * (H - H_height) with hH_s_def
  have hH_s_sqrt : Real.sqrt 3 / 2 < H_s := by
    nlinarith [H_height_gt_rho_height, hs.1, hs.2]
  have hH_s_le : H_s ≤ H := by nlinarith [hs.2]
  by_cases htp : t ∈ fdBoundary_H_partition
  · have hnd : ¬DifferentiableAt ℝ (fdBoundary_H H_s) t := by
      simp only [fdBoundary_H_partition, Finset.mem_insert, Finset.mem_singleton] at htp
      rcases htp with rfl | rfl | rfl
      · exact fdBoundary_H_not_differentiableAt_1 hH_s_sqrt
      · exact fdBoundary_H_not_differentiableAt_3 hH_s_sqrt
      · exact fdBoundary_H_not_differentiableAt_4 hH_s_sqrt
    rw [show (fun t' => fdBoundary_H H_s t') = fdBoundary_H H_s from rfl,
        deriv_zero_of_not_differentiableAt hnd, norm_zero]
    exact le_trans zero_le_one (le_max_right _ _)
  · simp only [fdBoundary_H_partition, Finset.mem_insert, Finset.mem_singleton] at htp
    push_neg at htp; obtain ⟨h1, h3, h4⟩ := htp
    rw [show (fun t' => fdBoundary_H H_s t') = fdBoundary_H H_s from rfl]
    by_cases ht1 : t < 1
    · rw [(fdBoundary_H_hasDerivAt_seg1 H_s ht1).deriv, neg_mul, norm_neg, norm_mul,
          Complex.norm_of_nonneg (le_of_lt (sub_pos.mpr hH_s_sqrt)),
          Complex.norm_I, mul_one]
      exact le_trans (by linarith) (le_max_left _ _)
    · push_neg at ht1
      have ht1' : 1 < t := lt_of_le_of_ne ht1 (Ne.symm h1)
      by_cases ht3 : t < 3
      · rw [(fdBoundary_H_hasDerivAt_arc H_s ht1' ht3).deriv, norm_mul, norm_mul,
            Complex.norm_of_nonneg (le_of_lt (by positivity : (0:ℝ) < Real.pi / 6)),
            Complex.norm_I, mul_one, Complex.norm_exp_ofReal_mul_I, mul_one]
        exact le_trans (by have := Real.pi_le_four; linarith) (le_max_right _ _)
      · push_neg at ht3
        have ht3' : 3 < t := lt_of_le_of_ne ht3 (Ne.symm h3)
        by_cases ht4 : t < 4
        · rw [(fdBoundary_H_hasDerivAt_seg4 H_s ht3' ht4).deriv, norm_mul,
              Complex.norm_of_nonneg (le_of_lt (sub_pos.mpr hH_s_sqrt)),
              Complex.norm_I, mul_one]
          exact le_trans (by linarith) (le_max_left _ _)
        · push_neg at ht4
          have ht4' : 4 < t := lt_of_le_of_ne ht4 (Ne.symm h4)
          rw [(fdBoundary_H_hasDerivAt_seg5 H_s ht4').deriv, norm_one]
          exact le_max_right _ _

/-! ## Piecewise Homotopy Construction -/

set_option maxHeartbeats 1600000 in
private lemma fdBoundary_H_piecewise_homotopic (p : ℂ)
    (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2)
    (hp_im_pos : 0 < p.im) (hp_im : p.im < H_height)
    {H : ℝ} (hH : H_height ≤ H) :
    PiecewiseCurvesHomotopicAvoiding (fdBoundary_H H_height) (fdBoundary_H H)
      0 5 p fdBoundary_H_partition := by
  refine ⟨fun q => fdBoundary_H (H_height + q.2 * (H - H_height)) q.1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fdHomot_continuous H_height H
  · intro t _; simp only [zero_mul, add_zero]
  · intro t _
    show fdBoundary_H (H_height + 1 * (H - H_height)) t = fdBoundary_H H t
    congr 1; ring
  · intro s _; exact fdBoundary_H_closed _
  · intro t ht s hs
    exact fdBoundary_H_avoids_interior p hp_norm hp_re hp_im_pos
      (lt_of_lt_of_le hp_im (by nlinarith [hs.1] : H_height ≤ _)) t ht
  · exact fun t _ ht_not_P s _ =>
      fdBoundary_H_differentiableAt_off_partition (H_height + s * (H - H_height)) ht_not_P
  · exact fun p₁ p₂ _ hfree _ =>
      fdHomot_deriv_continuousOn_piece H_height H p₁ p₂ hfree
  · exact fdHomot_deriv_bound H hH

/-! ## Main Theorem -/

/-- For interior points with `p.im < H_height`, the winding number of `fdBoundary_H H`
around `p` is `-1` for any `H ≥ H_height`.

This extends `generalizedWindingNumber_fdBoundary_eq_neg_one` from the canonical height
`H_height` to any `H ≥ H_height`, using piecewise homotopy invariance of winding numbers. -/
theorem gWN_fdBoundary_H_eq_neg_one_of_interior
    (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2)
    (hp_im_pos : 0 < p.im) (hp_im : p.im < H_height)
    {H : ℝ} (hH : H_height ≤ H) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 p = -1 := by
  have hbase := generalizedWindingNumber_fdBoundary_eq_neg_one p hp_norm hp_re hp_im_pos hp_im
  rw [← fdBoundary_H_eq_fdBoundary] at hbase
  rcases eq_or_lt_of_le hH with rfl | hH_gt
  · exact hbase
  · have h_eq := windingNumber_eq_of_piecewise_homotopic _ _ 0 5 p fdBoundary_H_partition
        (by norm_num : (0:ℝ) < 5)
        (fdBoundary_H_piecewise_homotopic p hp_norm hp_re hp_im_pos hp_im hH)
    exact h_eq.symm.trans hbase

/-! ## Point Translation Lemma -/

/-- Translation identity: winding number of `γ - p` around `0` equals winding number of `γ`
around `p`. This is immediate from the definition of `generalizedWindingNumber'`. -/
private lemma gWN_translate (γ : ℝ → ℂ) (a b : ℝ) (p : ℂ) :
    generalizedWindingNumber' (fun t => γ t - p) a b 0 =
    generalizedWindingNumber' γ a b p := by
  unfold generalizedWindingNumber'
  simp only [sub_zero]

/-! ## Strict Interior Theorem -/

set_option maxHeartbeats 1600000 in
/-- For interior points with `p.im < H` (not just `p.im < H_height`), the winding number
of `fdBoundary_H H` around `p` is `-1`.

This extends `gWN_fdBoundary_H_eq_neg_one_of_interior` by removing the `p.im < H_height`
restriction. When `p.im ≥ H_height`, we pick a reference point `q` with the same real part
but `q.im < H_height`, get `gWN(q) = -1` from the existing theorem, then show `gWN(p) = gWN(q)`
via a point-translation homotopy (vertical path from `q` to `p` stays in the avoidance region). -/
theorem gWN_fdBoundary_H_eq_neg_one_of_strictInterior
    (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2)
    (hp_im_pos : 0 < p.im) {H : ℝ} (hH : H_height ≤ H) (hp_im : p.im < H) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 p = -1 := by
  -- Easy case: p.im < H_height — use existing theorem directly
  by_cases hp_low : p.im < H_height
  · exact gWN_fdBoundary_H_eq_neg_one_of_interior p hp_norm hp_re hp_im_pos hp_low hH
  push_neg at hp_low
  -- Define reference point q with im < H_height
  set Hmid := (1 + H_height) / 2 with hHmid_def
  have hHmid_gt1 : 1 < Hmid := by simp only [hHmid_def]; linarith [H_height_gt_one]
  have hHmid_lt : Hmid < H_height := by simp only [hHmid_def]; linarith
  set q : ℂ := ↑p.re + ↑Hmid * I with hq_def
  have hq_re : q.re = p.re := by
    simp only [hq_def, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]; ring
  have hq_im : q.im = Hmid := by
    simp only [hq_def, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]; ring
  have hq_im_pos : 0 < q.im := by rw [hq_im]; linarith
  have hq_norm : ‖q‖ > 1 := by
    linarith [Complex.abs_im_le_norm q, abs_of_pos hq_im_pos]
  have hq_re_bound : |q.re| < 1/2 := by rw [hq_re]; exact hp_re
  have hq_im_lt : q.im < H_height := by rw [hq_im]; exact hHmid_lt
  -- gWN(fdBoundary_H H, q) = -1
  have hq_wn := gWN_fdBoundary_H_eq_neg_one_of_interior q hq_norm hq_re_bound hq_im_pos
    hq_im_lt hH
  -- Path of observation points: zPath(s) = p.re + ((1-s)*Hmid + s*p.im)*I
  set zPath : ℝ → ℂ := fun s => ↑p.re + ↑((1 - s) * Hmid + s * p.im) * I with hzPath_def
  have hzs_re : ∀ s, (zPath s).re = p.re := fun s => by
    simp only [hzPath_def, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]; ring
  have hzs_im : ∀ s, (zPath s).im = (1 - s) * Hmid + s * p.im := fun s => by
    simp only [hzPath_def, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]; ring
  have hH_sqrt : Real.sqrt 3 / 2 < H := by linarith [H_height_gt_rho_height]
  -- Build homotopy between γ-q and γ-p, avoiding 0
  have hhom : PiecewiseCurvesHomotopicAvoiding
      (fun t => fdBoundary_H H t - q) (fun t => fdBoundary_H H t - p)
      0 5 0 fdBoundary_H_partition := by
    refine ⟨fun r => fdBoundary_H H r.1 - zPath r.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- 1: Continuous
      exact ((fdBoundary_H_continuous H).comp continuous_fst).sub
        ((continuous_const.add ((continuous_ofReal.comp (by fun_prop :
          Continuous (fun s => (1 - s) * Hmid + s * p.im))).mul continuous_const)).comp
          continuous_snd)
    · -- 2: At s=0, zPath 0 = q
      intro t _
      show fdBoundary_H H t - zPath 0 = fdBoundary_H H t - q
      congr 1; simp only [hzPath_def, hq_def]; push_cast; ring
    · -- 3: At s=1, zPath 1 = p
      intro t _
      show fdBoundary_H H t - zPath 1 = fdBoundary_H H t - p
      congr 1; simp only [hzPath_def]; push_cast; ring_nf
      exact Complex.re_add_im p
    · -- 4: Closed
      intro s _; simp only [sub_left_inj]; exact fdBoundary_H_closed H
    · -- 5: Avoids 0 (fdBoundary_H H t ≠ zPath s)
      intro t ht s hs
      simp only [sub_ne_zero]
      have hzs_im_ge : Hmid ≤ (zPath s).im := by
        rw [hzs_im]; nlinarith [hs.1, hs.2, hp_low, hHmid_lt]
      exact fdBoundary_H_avoids_interior (zPath s)
        (by linarith [Complex.abs_im_le_norm (zPath s),
            abs_of_pos (show 0 < (zPath s).im by linarith)])
        (by rw [hzs_re]; exact hp_re)
        (by linarith)
        (by rw [hzs_im]; nlinarith [hs.1, hs.2, hp_im, hHmid_lt, hH])
        t ht
    · -- 6: DifferentiableAt in t off partition
      intro t _ ht_not_P s _
      show DifferentiableAt ℝ (fun t' => fdBoundary_H H t' - zPath s) t
      exact (fdBoundary_H_differentiableAt_off_partition H ht_not_P).sub
        (differentiableAt_const _)
    · -- 7: Derivative continuity on pieces
      intro p₁ p₂ _ hfree _
      -- Beta-reduce: (fun r => ...) (t', r.2) → fdBoundary_H H t' - zPath r.2
      show ContinuousOn (fun r : ℝ × ℝ => deriv (fun t' => fdBoundary_H H t' - zPath r.2) r.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1)
      have hc : ContinuousOn (fun r : ℝ × ℝ => deriv (fdBoundary_H H) r.1)
          (Ioo p₁ p₂ ×ˢ Icc 0 1) :=
        (fdHomot_deriv_continuousOn_piece H H p₁ p₂ hfree).congr (fun r _ => by
          congr 1; ext t; congr 1; ring)
      exact hc.congr (fun r hr => by
        have hd := fdBoundary_H_differentiableAt_off_partition H (hfree r.1 hr.1)
        rw [show (fun t' => fdBoundary_H H t' - zPath r.2) =
            fdBoundary_H H - fun _ => zPath r.2 from funext fun _ => rfl,
          deriv_sub hd (differentiableAt_const _), deriv_const, sub_zero])
    · -- 8: Derivative bound
      obtain ⟨M, hM⟩ := fdHomot_deriv_bound H hH
      refine ⟨M, fun t ht s _ => ?_⟩
      -- Beta-reduce the lambda application
      show ‖deriv (fun t' => fdBoundary_H H t' - zPath s) t‖ ≤ M
      by_cases htp : t ∈ fdBoundary_H_partition
      · have hnd : ¬DifferentiableAt ℝ (fdBoundary_H H) t := by
          simp only [fdBoundary_H_partition, Finset.mem_insert, Finset.mem_singleton] at htp
          rcases htp with rfl | rfl | rfl
          · exact fdBoundary_H_not_differentiableAt_1 hH_sqrt
          · exact fdBoundary_H_not_differentiableAt_3 hH_sqrt
          · exact fdBoundary_H_not_differentiableAt_4 hH_sqrt
        have hnd' : ¬DifferentiableAt ℝ (fun t' => fdBoundary_H H t' - zPath s) t := by
          rw [show (fun t' => fdBoundary_H H t' - zPath s) =
              fun t' => fdBoundary_H H t' + (-zPath s) from by ext; ring,
            differentiableAt_add_const_iff]
          exact hnd
        rw [deriv_zero_of_not_differentiableAt hnd', norm_zero]
        exact le_trans (norm_nonneg _) (hM t ht 0 ⟨le_refl 0, zero_le_one⟩)
      · have hd := fdBoundary_H_differentiableAt_off_partition H htp
        rw [show (fun t' => fdBoundary_H H t' - zPath s) =
            fdBoundary_H H - fun _ => zPath s from funext fun _ => rfl,
          deriv_sub hd (differentiableAt_const _), deriv_const, sub_zero]
        have hM1 := hM t ht 1 (by constructor <;> norm_num)
        rw [show (fun t' => fdBoundary_H (H_height + 1 * (H - H_height)) t') = fdBoundary_H H
            from by ext t'; congr 1; ring] at hM1
        exact hM1
  -- Apply homotopy invariance + translation
  have h_eq := windingNumber_eq_of_piecewise_homotopic _ _ 0 5 0 fdBoundary_H_partition
    (by norm_num : (0:ℝ) < 5) hhom
  rw [gWN_translate, gWN_translate] at h_eq
  exact h_eq.symm.trans hq_wn

end
