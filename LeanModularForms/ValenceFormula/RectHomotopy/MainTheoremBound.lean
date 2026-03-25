import LeanModularForms.ValenceFormula.RectHomotopy.BoundaryHomotopyDerivBounds
import LeanModularForms.ValenceFormula.RectHomotopy.BoundaryHomotopyDiff
import LeanModularForms.ValenceFormula.RectHomotopy.BoundaryHomotopySmooth

/-!
# Uniform derivative bound for the homotopy

Proves a uniform bound `‖deriv_t H(t,s)‖ ≤ 5` for all `(t,s) ∈ [0,5] × [0,1]`,
handling each segment case and the non-differentiable fallback.
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

lemma fdBoundaryToPolygonHomotopy_deriv_bound :
    ∃ M : ℝ, ∀ t ∈ Icc 0 5,
      ∀ s ∈ Icc (0:ℝ) 1,
        ‖deriv (fun t' =>
          fdBoundaryToPolygonHomotopy (t', s)) t‖ ≤ M := by
  use 5
  intro t ht s hs
  by_cases hd :
      DifferentiableAt ℝ (fun t' =>
          fdBoundaryToPolygonHomotopy (t', s))
        t
  · by_cases h1 : t < 1
    · have heq : (fun t' =>
            fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
          (fun t' : ℝ => (1/2 : ℂ) +
              (H_height - (↑t' : ℂ) * (H_height -
                  Real.sqrt 3 / 2)) * I) := by
        filter_upwards [
          eventually_lt_nhds h1] with t' ht'
        simp only [fdBoundaryToPolygonHomotopy,
          le_of_lt ht', ite_true]
      rw [heq.deriv_eq]
      exact norm_deriv_H_seg1_le t s
    · by_cases h2 : t < 2
      · by_cases h1' : t = 1
        · exfalso
          subst h1'
          exact
            fdBoundaryToPolygonHomotopy_not_diffAt_134
              s hs 1 (Set.mem_insert 1 _) hd
        · have ht2' : t ∈ Ioo 1 2 :=
            ⟨lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h1'), h2⟩
          have heq : (fun t' =>
                fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
              (fun t' : ℝ =>
                let arc_point :=
                  Complex.exp ((Real.pi / 3 +
                      (t' - 1) * (Real.pi / 2 -
                          Real.pi / 3)) *
                      I)
                let chord_point :=
                  chordSegment rho' i_point (t' - 1)
                (1 - s) • arc_point +
                  s • chord_point) := by
            filter_upwards [
              eventually_gt_nhds ht2'.1,
              eventually_lt_nhds ht2'.2]
              with t' ht1' ht2''
            simp only
              [fdBoundaryToPolygonHomotopy]
            simp only [not_le.mpr ht1',
              ite_false, le_of_lt ht2'',
              ite_true]
          rw [heq.deriv_eq]
          exact
            fdBoundaryToPolygonHomotopy_seg2_deriv_bound
              t ht2' s hs
      · by_cases h3 : t < 3
        · have ht2_ge : t ≥ 2 := not_lt.mp h2
          by_cases h2' : t = 2
          · subst h2'
            by_cases hs0 : s = 0
            · subst hs0
              have heq : (fun t' =>
                    fdBoundaryToPolygonHomotopy (t', 0)) =ᶠ[𝓝 2]
                  (fun t' : ℝ =>
                    Complex.exp ((Real.pi / 3 +
                        (t' - 1) * (Real.pi / 6)) *
                        I)) := by
                filter_upwards [
                  eventually_gt_nhds (by norm_num : (1:ℝ) < 2),
                  eventually_lt_nhds (by norm_num : (2:ℝ) < 3)]
                  with t' ht1' ht2'
                simp only
                  [fdBoundaryToPolygonHomotopy]
                by_cases ht'_le2 : t' ≤ 2
                · simp only [
                    not_le.mpr ht1',
                    ht'_le2, ite_false,
                    ite_true, zero_smul,
                    add_zero, sub_zero,
                    one_smul]
                  congr 1; ring
                · simp only [
                    not_le.mpr ht1',
                    not_le.mpr (lt_of_not_ge ht'_le2),
                    le_of_lt ht2', ite_false,
                    ite_true, zero_smul,
                    add_zero, sub_zero,
                    one_smul]
                  congr 1
                  ring
              rw [heq.deriv_eq]
              have h_deriv :
                  HasDerivAt (fun t' : ℝ =>
                      Complex.exp ((Real.pi / 3 +
                          (t' - 1) * (Real.pi / 6)) *
                          I))
                    ((Real.pi / 6) * I *
                      Complex.exp ((Real.pi / 2) * I))
                    2 := by
                have h_ofReal :
                    HasDerivAt (fun t' : ℝ =>
                        (t' : ℂ))
                      1 2 :=
                  Complex.ofRealCLM.hasDerivAt
                have h_inner :
                    HasDerivAt (fun t' : ℝ =>
                        (Real.pi : ℂ) / 3 + ((t' : ℂ) - 1) *
                            ((Real.pi : ℂ) / 6))
                      ((Real.pi : ℂ) / 6)
                      2 := by
                  have h_shift :
                      HasDerivAt (fun t' : ℝ =>
                          (t' : ℂ) - 1)
                        1 2 :=
                    h_ofReal.sub_const 1
                  have h_mul :
                      HasDerivAt (fun t' : ℝ =>
                          ((t' : ℂ) - 1) * ((Real.pi : ℂ) /
                              6))
                        ((Real.pi : ℂ) / 6)
                        2 := by
                    have :=
                      h_shift.mul_const ((Real.pi : ℂ) / 6)
                    simp only [one_mul] at this
                    exact this
                  have :=
                    h_mul.const_add ((Real.pi : ℂ) / 3)
                  simp only at this
                  exact this
                have h_times_I :
                    HasDerivAt (fun t' : ℝ =>
                        ((Real.pi : ℂ) / 3 + ((t' : ℂ) - 1) *
                            ((Real.pi : ℂ) /
                              6)) * I)
                      (((Real.pi : ℂ) / 6) *
                        I)
                      2 :=
                  h_inner.mul_const I
                have h_at_2 : ((Real.pi : ℂ) / 3 +
                      ((2 : ℂ) - 1) * ((Real.pi : ℂ) / 6)) *
                      I =
                    (Real.pi / 2) * I := by
                  ring
                have h_exp :=
                  Complex.hasDerivAt_exp (((Real.pi : ℂ) / 3 +
                      ((2 : ℂ) - 1) * ((Real.pi : ℂ) / 6)) *
                      I)
                have h_comp :=
                  h_exp.comp 2 h_times_I
                simp only [
                  mul_comm (Complex.exp _)]
                  at h_comp
                convert h_comp using 2
                rw [h_at_2]
              rw [h_deriv.deriv]
              calc ‖(Real.pi / 6) * I *
                  Complex.exp ((Real.pi / 2) * I)‖
                  = ‖(Real.pi / 6 : ℂ)‖ *
                      ‖I‖ *
                      ‖Complex.exp ((Real.pi / 2) *
                          I)‖ := by
                    rw [norm_mul, norm_mul]
                _ = (Real.pi / 6) *
                    1 * 1 := by
                    have h1 :
                        ‖(Real.pi / 6 : ℂ)‖ =
                          Real.pi / 6 := by
                      have hpi :
                          ‖(Real.pi : ℂ)‖ =
                            Real.pi := by
                        rw [Complex.norm_real]
                        exact abs_of_pos
                          Real.pi_pos
                      have h6 :
                          ‖(6 : ℂ)‖ = 6 := by
                        norm_num
                      rw [norm_div, hpi, h6]
                    have h2 :
                        ‖(I : ℂ)‖ = 1 :=
                      Complex.norm_I
                    have h3 :
                        ‖Complex.exp ((Real.pi / 2) *
                            I)‖ = 1 := by
                      have : ((Real.pi / 2) *
                            I : ℂ) =
                          (Real.pi / 2 : ℝ) *
                            I := by
                        push_cast; ring
                      rw [this,
                        Complex.norm_exp_ofReal_mul_I]
                    rw [h1, h2, h3]
                _ = Real.pi / 6 := by ring
                _ ≤ 1 := by
                    have := Real.pi_le_four
                    linarith
                _ ≤ 5 := by norm_num
            · exfalso
              have h_not_diff :
                  ¬DifferentiableAt ℝ (fun t' ↦
                      fdBoundaryToPolygonHomotopy (t', s))
                    2 := by
                intro hd_inner
                have h_slope_inner :=
                  hasDerivAt_iff_tendsto_slope.mp
                    hd_inner.hasDerivAt
                let g_left : ℝ → ℂ :=
                  fun t' => (1 - s) •
                      Complex.exp (((Real.pi : ℝ) / 3 +
                          (t' - 1) * ((Real.pi : ℝ) /
                              6)) * I) +
                    s • chordSegment rho'
                      i_point (t' - 1)
                have h_arc_left :
                    HasDerivAt (fun t' : ℝ =>
                        Complex.exp (((Real.pi : ℝ) / 3 +
                            (t' - 1) * ((Real.pi : ℝ) /
                                6)) * I))
                      (((Real.pi : ℝ) / 6) *
                        I *
                        Complex.exp (((Real.pi : ℝ) / 3 +
                            ((2 : ℝ) - 1) * ((Real.pi : ℝ) /
                                6)) * I))
                      (2 : ℝ) := by
                  have h_inner :
                      HasDerivAt (fun t' : ℝ =>
                          (Real.pi : ℂ) / 3 + ((t' : ℂ) - 1) *
                              ((Real.pi : ℂ) /
                                6))
                        ((Real.pi : ℂ) / 6) (2 : ℝ) := by
                    have h_shift :
                        HasDerivAt (fun t' : ℝ =>
                            (t' : ℂ) - 1)
                          1 (2 : ℝ) :=
                      (Complex.ofRealCLM.hasDerivAt (x := 2)).sub_const 1
                    have h_mul :
                        HasDerivAt (fun t' : ℝ =>
                            ((t' : ℂ) - 1) * ((Real.pi : ℂ) /
                                6))
                          ((Real.pi : ℂ) / 6) (2 : ℝ) := by
                      have :=
                        h_shift.mul_const ((Real.pi : ℂ) / 6)
                      simp only [one_mul]
                        at this
                      exact this
                    have :=
                      h_mul.const_add ((Real.pi : ℂ) / 3)
                    simp only at this
                    exact this
                  have h_comp := (Complex.hasDerivAt_exp
                      (((Real.pi : ℂ) / 3 + (((2 : ℝ) : ℂ) - 1) *
                          ((Real.pi : ℂ) /
                            6)) * I)).comp
                      (2 : ℝ) (h_inner.mul_const I)
                  simp only [
                    mul_comm (Complex.exp _)]
                    at h_comp
                  exact h_comp
                have h_simp_arc_left : ((Real.pi : ℂ) / 3 +
                      (((2 : ℝ) : ℂ) - 1) * ((Real.pi : ℂ) / 6)) *
                      I =
                    ↑(Real.pi / 2) * I := by
                  push_cast; ring
                rw [h_simp_arc_left,
                  exp_pi_div_two_eq_I]
                  at h_arc_left
                have h_chord_left :
                    HasDerivAt (fun t' : ℝ =>
                        chordSegment rho'
                          i_point (t' - 1))
                      (i_point - rho') (2 : ℝ) := by
                  simp only [chordSegment]
                  have h_shift := (hasDerivAt_id
                      (2 : ℝ)).sub_const 1
                  have h1 :
                      HasDerivAt (fun t' : ℝ =>
                          (1 - (t' - 1)) •
                            rho')
                        (-rho') (2 : ℝ) := by
                    have h_coef :
                        HasDerivAt (fun t' : ℝ =>
                            (1 - (t' - 1) : ℝ))
                          (-1 : ℝ) (2 : ℝ) := by
                      have := (hasDerivAt_const
                          (2 : ℝ) (1 : ℝ)).sub h_shift
                      simp only [zero_sub]
                        at this
                      convert this using 1
                    have :=
                      h_coef.smul_const rho'
                    simp only [neg_one_smul]
                      at this
                    exact this
                  have h2 :
                      HasDerivAt (fun t' : ℝ =>
                          (t' - 1) • i_point)
                        i_point (2 : ℝ) := by
                    have :=
                      h_shift.smul_const
                        i_point
                    simp only [one_smul]
                      at this
                    exact this
                  convert h1.add h2 using 1
                  ring
                have h_combined_left :
                    HasDerivAt g_left ((1 - s) •
                        (((Real.pi : ℝ) / 6) *
                          I * I) +
                        s • (i_point - rho'))
                      (2 : ℝ) :=
                  (h_arc_left.const_smul (1 - s)).add
                    (h_chord_left.const_smul s)
                have h_slope_left_iio := (hasDerivAt_iff_tendsto_slope.mp
                    h_combined_left).mono_left (nhdsWithin_mono (2 : ℝ)
                      (fun y (hy : y < _) =>
                        ne_of_lt hy))
                have h_mem_left :
                    Ioo 1 2 ∈
                      𝓝[<] (2 : ℝ) :=
                  Ioo_mem_nhdsLT (by norm_num : (1 : ℝ) < 2)
                have h_left_val :
                    Tendsto (slope
                        (fun t' =>
                          fdBoundaryToPolygonHomotopy (t', s))
                        2)
                      (𝓝[<] 2) (𝓝 ((1 - s) •
                        (((Real.pi : ℝ) / 6) *
                          I * I) +
                        s • (i_point -
                            rho'))) := by
                  refine
                    h_slope_left_iio.congr' ?_
                  filter_upwards [h_mem_left]
                    with t' ht'
                  simp only [slope_def_module]
                  congr 1
                  have h_at_2 :
                      fdBoundaryToPolygonHomotopy (2, s) =
                      g_left 2 := by
                    simp only [
                      fdBoundaryToPolygonHomotopy,
                      show (2 : ℝ) ≤ 2
                        from le_refl 2,
                      show ¬(2 : ℝ) ≤ 1
                        from by norm_num,
                      ite_false, ite_true]
                    congr 1; congr 1
                    congr 1; ring
                  have h_at_t' :
                      fdBoundaryToPolygonHomotopy (t', s) =
                      g_left t' := by
                    simp only [
                      fdBoundaryToPolygonHomotopy,
                      not_le.mpr ht'.1,
                      ite_false,
                      le_of_lt ht'.2,
                      ite_true]
                    congr 1; congr 1
                    congr 1; ring
                  rw [h_at_t', h_at_2]
                let g_right : ℝ → ℂ :=
                  fun t' => (1 - s) •
                      Complex.exp (((Real.pi : ℝ) / 2 +
                          (t' - 2) * ((Real.pi : ℝ) /
                              6)) * I) +
                    s • chordSegment i_point
                      rho (t' - 2)
                have h_arc_right :
                    HasDerivAt (fun t' : ℝ =>
                        Complex.exp (((Real.pi : ℝ) / 2 +
                            (t' - 2) * ((Real.pi : ℝ) /
                                6)) * I))
                      (((Real.pi : ℝ) / 6) *
                        I *
                        Complex.exp (((Real.pi : ℝ) / 2 +
                            ((2 : ℝ) - 2) * ((Real.pi : ℝ) /
                                6)) * I))
                      (2 : ℝ) := by
                  have h_inner :
                      HasDerivAt (fun t' : ℝ =>
                          (Real.pi : ℂ) / 2 + ((t' : ℂ) - 2) *
                              ((Real.pi : ℂ) /
                                6))
                        ((Real.pi : ℂ) / 6) (2 : ℝ) := by
                    have h_shift :
                        HasDerivAt (fun t' : ℝ =>
                            (t' : ℂ) - 2)
                          1 (2 : ℝ) :=
                      (Complex.ofRealCLM.hasDerivAt (x := 2)).sub_const 2
                    have h_mul :
                        HasDerivAt (fun t' : ℝ =>
                            ((t' : ℂ) - 2) * ((Real.pi : ℂ) /
                                6))
                          ((Real.pi : ℂ) / 6) (2 : ℝ) := by
                      have :=
                        h_shift.mul_const ((Real.pi : ℂ) / 6)
                      simp only [one_mul]
                        at this
                      exact this
                    have :=
                      h_mul.const_add ((Real.pi : ℂ) / 2)
                    simp only at this
                    exact this
                  have h_comp := (Complex.hasDerivAt_exp
                      (((Real.pi : ℂ) / 2 + (((2 : ℝ) : ℂ) - 2) *
                          ((Real.pi : ℂ) /
                            6)) * I)).comp
                      (2 : ℝ) (h_inner.mul_const I)
                  simp only [
                    mul_comm (Complex.exp _)]
                    at h_comp
                  exact h_comp
                have h_simp_arc_right : ((Real.pi : ℂ) / 2 +
                      (((2 : ℝ) : ℂ) - 2) * ((Real.pi : ℂ) / 6)) *
                      I =
                    ↑(Real.pi / 2) * I := by
                  push_cast; ring
                rw [h_simp_arc_right,
                  exp_pi_div_two_eq_I]
                  at h_arc_right
                have h_chord_right :
                    HasDerivAt (fun t' : ℝ =>
                        chordSegment i_point
                          rho (t' - 2))
                      (rho - i_point) (2 : ℝ) := by
                  simp only [chordSegment]
                  have h_shift := (hasDerivAt_id
                      (2 : ℝ)).sub_const 2
                  have h1 :
                      HasDerivAt (fun t' : ℝ =>
                          (1 - (t' - 2)) •
                            i_point)
                        (-i_point) (2 : ℝ) := by
                    have h_coef :
                        HasDerivAt (fun t' : ℝ =>
                            (1 - (t' - 2) : ℝ))
                          (-1 : ℝ) (2 : ℝ) := by
                      have := (hasDerivAt_const
                          (2 : ℝ) (1 : ℝ)).sub h_shift
                      simp only [zero_sub]
                        at this
                      convert this using 1
                    have :=
                      h_coef.smul_const i_point
                    simp only [neg_one_smul]
                      at this
                    exact this
                  have h2 :
                      HasDerivAt (fun t' : ℝ =>
                          (t' - 2) • rho)
                        rho (2 : ℝ) := by
                    have :=
                      h_shift.smul_const rho
                    simp only [one_smul]
                      at this
                    exact this
                  convert h1.add h2 using 1
                  ring
                have h_combined_right :
                    HasDerivAt g_right ((1 - s) •
                        (((Real.pi : ℝ) / 6) *
                          I * I) +
                        s • (rho - i_point))
                      (2 : ℝ) :=
                  (h_arc_right.const_smul (1 - s)).add
                    (h_chord_right.const_smul s)
                have h_slope_right_ioi := (hasDerivAt_iff_tendsto_slope.mp
                    h_combined_right).mono_left (nhdsWithin_mono (2 : ℝ)
                      (fun y (hy : _ < y) =>
                        ne_of_gt hy))
                have h_mem_right :
                    Ioo 2 3 ∈
                      𝓝[>] (2 : ℝ) :=
                  Ioo_mem_nhdsGT (by norm_num : (2 : ℝ) < 3)
                have h_right_val :
                    Tendsto (slope
                        (fun t' =>
                          fdBoundaryToPolygonHomotopy (t', s))
                        2)
                      (𝓝[>] 2) (𝓝 ((1 - s) •
                        (((Real.pi : ℝ) / 6) *
                          I * I) +
                        s • (rho -
                            i_point))) := by
                  refine
                    h_slope_right_ioi.congr' ?_
                  filter_upwards [h_mem_right]
                    with t' ht'
                  simp only [slope_def_module]
                  congr 1
                  have h_at_2r :
                      fdBoundaryToPolygonHomotopy (2, s) =
                      g_right 2 := by
                    simp only [
                      fdBoundaryToPolygonHomotopy,
                      show (2 : ℝ) ≤ 2
                        from le_refl 2,
                      show ¬(2 : ℝ) ≤ 1
                        from by norm_num,
                      ite_false, ite_true,
                      chordSegment]
                    congr 1
                    · congr 1
                      push_cast; ring_nf
                    · have h1 : (2 : ℝ) - 1 = 1 := by
                        norm_num
                      have h2 : (2 : ℝ) - 2 = 0 := by
                        norm_num
                      rw [h1, h2]
                      simp [chordSegment]
                  have h_at_t'r :
                      fdBoundaryToPolygonHomotopy (t', s) =
                      g_right t' := by
                    simp only [
                      fdBoundaryToPolygonHomotopy,
                      not_le.mpr (show (1 : ℝ) < t' by
                          linarith [ht'.1]),
                      not_le.mpr ht'.1,
                      ite_false,
                      le_of_lt ht'.2,
                      ite_true]
                    congr 1; congr 1
                    congr 1; ring
                  rw [h_at_t'r, h_at_2r]
                have h_eq_left :=
                  tendsto_nhds_unique (h_slope_inner.mono_left
                      (nhdsLT_le_nhdsNE 2))
                    h_left_val
                have h_eq_right :=
                  tendsto_nhds_unique (h_slope_inner.mono_left
                      (nhdsGT_le_nhdsNE 2))
                    h_right_val
                rw [h_eq_left] at h_eq_right
                have h_pts_eq :
                    i_point - rho' =
                      rho - i_point := by
                  have h_smul_eq :
                      s • (i_point - rho') =
                        s • (rho - i_point) :=
                    add_left_cancel h_eq_right
                  exact (smul_right_injective
                    ℂ hs0).eq_iff.mp h_smul_eq
                have h_im_left :
                    Complex.im (i_point - rho') =
                    1 - Real.sqrt 3 / 2 := by
                  simp only [i_point, rho']
                  simp [Complex.add_im,
                    Complex.sub_im,
                    Complex.mul_im,
                    Complex.ofReal_im,
                    Complex.ofReal_re,
                    Complex.I_im,
                    Complex.I_re,
                    Complex.div_ofNat_im,
                    Complex.div_ofNat_re]
                have h_im_right :
                    Complex.im (rho - i_point) =
                    Real.sqrt 3 / 2 - 1 := by
                  simp only [rho, i_point]
                  simp [Complex.add_im,
                    Complex.sub_im,
                    Complex.mul_im,
                    Complex.ofReal_im,
                    Complex.ofReal_re,
                    Complex.I_im,
                    Complex.I_re,
                    Complex.neg_im,
                    Complex.div_ofNat_im,
                    Complex.div_ofNat_re,
                    Complex.one_im]
                have h_im_eq :=
                  congr_arg Complex.im
                    h_pts_eq
                rw [h_im_left, h_im_right]
                  at h_im_eq
                have h_sqrt3_eq :
                    Real.sqrt 3 = 2 := by
                  linarith
                have h_sq : (Real.sqrt 3) ^ 2 = 3 :=
                  Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)
                rw [h_sqrt3_eq] at h_sq
                norm_num at h_sq
              exact h_not_diff hd
          · have ht3' : t ∈ Ioo 2 3 :=
              ⟨lt_of_le_of_ne ht2_ge (Ne.symm h2'), h3⟩
            have heq : (fun t' =>
                  fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
                (fun t' : ℝ =>
                  let arc_point :=
                    Complex.exp ((Real.pi / 2 +
                        (t' - 2) * (2 * Real.pi / 3 -
                            Real.pi / 2)) *
                        I)
                  let chord_point :=
                    chordSegment i_point rho (t' - 2)
                  (1 - s) • arc_point +
                    s • chord_point) := by
              filter_upwards [
                eventually_gt_nhds ht3'.1,
                eventually_lt_nhds ht3'.2]
                with t' ht2'' ht3''
              simp only
                [fdBoundaryToPolygonHomotopy]
              simp only [
                not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 2)
                  ht2''),
                ite_false,
                not_le.mpr ht2'',
                le_of_lt ht3'', ite_true]
            rw [heq.deriv_eq]
            exact
              fdBoundaryToPolygonHomotopy_seg3_deriv_bound
                t ht3' s hs
        · by_cases h4 : t < 4
          · by_cases h3' : t = 3
            · exfalso
              subst h3'
              exact
                fdBoundaryToPolygonHomotopy_not_diffAt_134
                  s hs 3 (Set.mem_insert_of_mem 1 (Set.mem_insert 3 _)) hd
            · have ht4' : t ∈ Ioo 3 4 :=
                ⟨lt_of_le_of_ne (not_lt.mp h3)
                  (Ne.symm h3'), h4⟩
              have heq : (fun t' =>
                    fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
                  (fun t' : ℝ => (-1/2 : ℂ) +
                      ((Real.sqrt 3 / 2 : ℂ) + ((↑t' : ℂ) - 3) *
                          ((H_height : ℂ) -
                            Real.sqrt 3 / 2)) *
                        I) := by
                filter_upwards [
                  eventually_gt_nhds ht4'.1,
                  eventually_lt_nhds ht4'.2]
                  with t' ht3' ht4''
                simp only
                  [fdBoundaryToPolygonHomotopy]
                have h1' : ¬(t' ≤ 1) :=
                  not_le.mpr (by linarith : 1 < t')
                have h2' : ¬(t' ≤ 2) :=
                  not_le.mpr (by linarith : 2 < t')
                have h3'' : ¬(t' ≤ 3) :=
                  not_le.mpr ht3'
                have h4''' : t' ≤ 4 :=
                  le_of_lt ht4''
                simp only [h1', h2', h3'',
                  h4''', ite_false, ite_true]
              rw [heq.deriv_eq]
              exact norm_deriv_H_seg4_le t s
          · by_cases h4' : t = 4
            · exfalso
              subst h4'
              exact
                fdBoundaryToPolygonHomotopy_not_diffAt_134
                  s hs 4 (Set.mem_insert_of_mem 1 (Set.mem_insert_of_mem 3
                    (Set.mem_singleton_iff.mpr rfl))) hd
            · have ht5' : t > 4 :=
                lt_of_le_of_ne (not_lt.mp h4)
                  (Ne.symm h4')
              have heq : (fun t' =>
                    fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
                  (fun t' : ℝ => ((↑t' : ℂ) - 9/2) +
                      (H_height : ℂ) * I) := by
                filter_upwards [
                  eventually_gt_nhds ht5']
                  with t' ht4'
                simp only
                  [fdBoundaryToPolygonHomotopy]
                have h1' : ¬(t' ≤ 1) :=
                  not_le.mpr (by linarith : 1 < t')
                have h2' : ¬(t' ≤ 2) :=
                  not_le.mpr (by linarith : 2 < t')
                have h3' : ¬(t' ≤ 3) :=
                  not_le.mpr (by linarith : 3 < t')
                have h4'' : ¬(t' ≤ 4) :=
                  not_le.mpr ht4'
                simp only [h1', h2', h3',
                  h4'', ite_false]
              rw [heq.deriv_eq]
              exact norm_deriv_H_seg5_le t s
  · simp only [
      deriv_zero_of_not_differentiableAt hd,
      norm_zero]
    norm_num

end RectHomotopyProof
