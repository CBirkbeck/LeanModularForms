/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ValenceFormula.RectHomotopy.HomotopyDef

/-!
# Derivative norm bounds for the homotopy segments

Proves that the derivative norm of each segment of
`fdBoundaryToPolygonHomotopy` is bounded by 5.
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

/-- Norm bound for segment 2 derivative. -/
lemma norm_deriv_H_seg2_le
    (t s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    ‖deriv (fun t' : ℝ =>
      let arc_point :=
        Complex.exp
          ((Real.pi / 3 +
            (t' - 1) *
              (Real.pi / 2 -
                Real.pi / 3)) * I)
      let chord_point :=
        chordSegment rho' i_point (t' - 1)
      (1 - s) • arc_point +
        s • chord_point) t‖ ≤ 5 := by
  have h1s : |1 - s| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hs' : |s| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hpi6 : Real.pi / 6 ≤ 1 := by
    have := Real.pi_le_four; linarith
  have hi_rho : ‖i_point - rho'‖ ≤ 2 := by
    calc ‖i_point - rho'‖
        ≤ ‖i_point‖ + ‖rho'‖ :=
          norm_sub_le _ _
      _ = 1 + 1 := by
          rw [i_point_norm, rho'_norm]
      _ = 2 := by norm_num
  by_cases hd : DifferentiableAt ℝ
      (fun t' : ℝ =>
        let arc_point :=
          Complex.exp
            ((Real.pi / 3 +
              (t' - 1) *
                (Real.pi / 2 -
                  Real.pi / 3)) * I)
        let chord_point :=
          chordSegment rho' i_point (t' - 1)
        (1 - s) • arc_point +
          s • chord_point) t
  · have h_bound : ‖deriv (fun t' : ℝ =>
        let arc_point :=
          Complex.exp
            ((Real.pi / 3 +
              (t' - 1) *
                (Real.pi / 2 -
                  Real.pi / 3)) * I)
        let chord_point :=
          chordSegment rho' i_point (t' - 1)
        (1 - s) • arc_point +
          s • chord_point) t‖ ≤
        |1 - s| * 1 + |s| * 2 := by
      have hpi :
          (Real.pi / 2 - Real.pi / 3 : ℂ) =
            Real.pi / 6 := by
        ring
      have func_eq : (fun t' : ℝ =>
            let arc_point :=
              Complex.exp
                ((Real.pi / 3 +
                  (t' - 1) *
                    (Real.pi / 2 -
                      Real.pi / 3)) * I)
            let chord_point :=
              chordSegment rho' i_point
                (t' - 1)
            (1 - s) • arc_point +
              s • chord_point) =
          (fun t' : ℝ =>
            let arc_point :=
              Complex.exp
                ((Real.pi / 3 +
                  (t' - 1) *
                    (Real.pi / 6)) * I)
            let chord_point :=
              chordSegment rho' i_point
                (t' - 1)
            (1 - s) • arc_point +
              s • chord_point) := by
        ext t'; simp only [hpi]
      rw [func_eq]
      have h_arc : HasDerivAt
          (fun t' : ℝ =>
            Complex.exp
              (((Real.pi : ℝ) / 3 +
                (t' - 1) *
                  ((Real.pi : ℝ) / 6)) * I))
          (((Real.pi : ℝ) / 6) * I *
            Complex.exp
              (((Real.pi : ℝ) / 3 +
                (t - 1) *
                  ((Real.pi : ℝ) / 6)) *
                I))
          t := by
        have h_inner : HasDerivAt
            (fun t' : ℝ =>
              (Real.pi : ℂ) / 3 +
                ((t' : ℂ) - 1) *
                  ((Real.pi : ℂ) / 6))
            ((Real.pi : ℂ) / 6) t := by
          have h_shift :
              HasDerivAt
                (fun t' : ℝ =>
                  (t' : ℂ) - 1) 1 t := by
            have h :=
              @ContinuousLinearMap.hasDerivAt
                ℝ _ ℂ _ _ t
                Complex.ofRealCLM
            simp only [
              Complex.ofRealCLM_apply] at h
            exact h.sub_const 1
          have h_mul : HasDerivAt
              (fun t' : ℝ =>
                ((t' : ℂ) - 1) *
                  ((Real.pi : ℂ) / 6))
              ((Real.pi : ℂ) / 6) t := by
            have :=
              h_shift.mul_const
                ((Real.pi : ℂ) / 6)
            simp only [one_mul] at this
            exact this
          have :=
            h_mul.const_add
              ((Real.pi : ℂ) / 3)
          exact this
        have h_times_I : HasDerivAt
            (fun t' : ℝ =>
              ((Real.pi : ℂ) / 3 +
                ((t' : ℂ) - 1) *
                  ((Real.pi : ℂ) / 6)) * I)
            (((Real.pi : ℂ) / 6) * I) t :=
          h_inner.mul_const I
        have h_exp : HasDerivAt Complex.exp
            (Complex.exp
              (((Real.pi : ℂ) / 3 +
                ((t : ℂ) - 1) *
                  ((Real.pi : ℂ) / 6)) * I))
            (((Real.pi : ℂ) / 3 +
              ((t : ℂ) - 1) *
                ((Real.pi : ℂ) / 6)) *
              I) :=
          Complex.hasDerivAt_exp _
        have := h_exp.comp t h_times_I
        simp only [
          mul_comm (Complex.exp _)] at this
        exact this
      have h_chord : HasDerivAt
          (fun t' : ℝ =>
            chordSegment rho' i_point
              (t' - 1))
          (i_point - rho') t := by
        simp only [chordSegment]
        have h_shift :
            HasDerivAt
              (fun t' : ℝ => t' - 1)
              (1 : ℝ) t :=
          (hasDerivAt_id t).sub_const 1
        have h1 : HasDerivAt
            (fun t' : ℝ =>
              (1 - (t' - 1)) • rho')
            (-rho') t := by
          have h_coef : HasDerivAt
              (fun t' : ℝ =>
                (1 - (t' - 1) : ℝ))
              (-1 : ℝ) t := by
            have :=
              (hasDerivAt_const t (1 : ℝ)).sub
                h_shift
            simp only [zero_sub] at this
            convert this using 1
          have := h_coef.smul_const rho'
          simp only [neg_one_smul] at this
          exact this
        have h2 : HasDerivAt
            (fun t' : ℝ =>
              (t' - 1) • i_point)
            i_point t := by
          have := h_shift.smul_const i_point
          simp only [one_smul] at this
          exact this
        convert h1.add h2 using 1
        ring
      have h_combined : HasDerivAt
          (fun t' : ℝ =>
            let arc_point :=
              Complex.exp
                ((Real.pi / 3 +
                  (t' - 1) *
                    (Real.pi / 6)) * I)
            let chord_point :=
              chordSegment rho' i_point
                (t' - 1)
            (1 - s) • arc_point +
              s • chord_point)
          ((1 - s) •
            (((Real.pi : ℝ) / 6) * I *
              Complex.exp
                (((Real.pi : ℝ) / 3 +
                  (t - 1) *
                    ((Real.pi : ℝ) / 6)) *
                  I)) +
           s • (i_point - rho')) t := by
        have h1 := h_arc.const_smul (1 - s)
        have h2 := h_chord.const_smul s
        have := h1.add h2
        convert this
      rw [h_combined.deriv]
      calc ‖(1 - s) •
              (((Real.pi : ℝ) / 6) * I *
                Complex.exp
                  (((Real.pi : ℝ) / 3 +
                    (t - 1) *
                      ((Real.pi : ℝ) / 6)) *
                    I)) +
             s • (i_point - rho')‖
          ≤ ‖(1 - s) •
              (((Real.pi : ℝ) / 6) * I *
                Complex.exp
                  (((Real.pi : ℝ) / 3 +
                    (t - 1) *
                      ((Real.pi : ℝ) / 6)) *
                    I))‖ +
            ‖s • (i_point - rho')‖ :=
          norm_add_le _ _
        _ = |1 - s| *
              ‖((Real.pi : ℝ) / 6) * I *
                Complex.exp
                  (((Real.pi : ℝ) / 3 +
                    (t - 1) *
                      ((Real.pi : ℝ) / 6)) *
                    I)‖ +
            |s| * ‖i_point - rho'‖ := by
          rw [norm_smul, norm_smul,
            Real.norm_eq_abs,
            Real.norm_eq_abs]
        _ = |1 - s| *
              ((Real.pi / 6) *
                ‖Complex.exp
                  (((Real.pi : ℝ) / 3 +
                    (t - 1) *
                      ((Real.pi : ℝ) / 6)) *
                    I)‖) +
            |s| * ‖i_point - rho'‖ := by
              congr 1
              rw [mul_assoc, norm_mul,
                norm_mul]
              have hpi_norm :
                  ‖(Real.pi : ℂ) / 6‖ =
                    Real.pi / 6 := by
                have h1 :
                    ‖(Real.pi : ℂ)‖ =
                      Real.pi := by
                  rw [Complex.norm_real]
                  exact abs_of_pos
                    Real.pi_pos
                have h2 :
                    ‖(6 : ℂ)‖ = 6 := by
                  norm_num
                rw [norm_div, h1, h2]
              rw [hpi_norm,
                Complex.norm_I, one_mul]
        _ = |1 - s| *
              ((Real.pi / 6) * 1) +
            |s| * ‖i_point - rho'‖ := by
              congr 2
              have :
                  ((Real.pi : ℝ) / 3 +
                    (t - 1) *
                      ((Real.pi : ℝ) / 6)) *
                    I =
                  ((Real.pi / 3 +
                    (t - 1) *
                      (Real.pi / 6)) : ℝ) *
                    I := by
                push_cast; ring
              rw [this,
                Complex.norm_exp_ofReal_mul_I]
        _ = |1 - s| * Real.pi / 6 +
            |s| * ‖i_point - rho'‖ := by
          ring
        _ ≤ |1 - s| * 1 + |s| * 2 := by
            have h1 :
                |1 - s| * Real.pi / 6 ≤
                  |1 - s| * 1 := by
              have hpos :
                  (0 : ℝ) ≤ |1 - s| :=
                abs_nonneg _
              calc |1 - s| * Real.pi / 6
                    = |1 - s| *
                        (Real.pi / 6) := by
                      ring
                  _ ≤ |1 - s| * 1 :=
                    mul_le_mul_of_nonneg_left
                      hpi6 hpos
            have h2 :
                |s| * ‖i_point - rho'‖ ≤
                  |s| * 2 :=
              mul_le_mul_of_nonneg_left
                hi_rho (abs_nonneg _)
            linarith
    calc ‖deriv (fun t' : ℝ =>
          let arc_point :=
            Complex.exp
              ((Real.pi / 3 +
                (t' - 1) *
                  (Real.pi / 2 -
                    Real.pi / 3)) * I)
          let chord_point :=
            chordSegment rho' i_point
              (t' - 1)
          (1 - s) • arc_point +
            s • chord_point) t‖
        ≤ |1 - s| * 1 + |s| * 2 :=
          h_bound
      _ ≤ 1 * 1 + 1 * 2 := by
          nlinarith [h1s, hs']
      _ = 3 := by norm_num
      _ ≤ 5 := by norm_num
  · simp only [
      deriv_zero_of_not_differentiableAt hd,
      norm_zero]
    norm_num

/-- Norm bound for segment 3 derivative. -/
lemma norm_deriv_H_seg3_le
    (t s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    ‖deriv (fun t' : ℝ =>
      let arc_point :=
        Complex.exp
          ((Real.pi / 2 +
            (t' - 2) *
              (2 * Real.pi / 3 -
                Real.pi / 2)) * I)
      let chord_point :=
        chordSegment i_point rho (t' - 2)
      (1 - s) • arc_point +
        s • chord_point) t‖ ≤ 5 := by
  have h1s : |1 - s| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hs' : |s| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hpi6 : Real.pi / 6 ≤ 1 := by
    have := Real.pi_le_four; linarith
  have hrho_i : ‖rho - i_point‖ ≤ 2 := by
    calc ‖rho - i_point‖
        ≤ ‖rho‖ + ‖i_point‖ :=
          norm_sub_le _ _
      _ = 1 + 1 := by
          rw [rho_norm, i_point_norm]
      _ = 2 := by norm_num
  by_cases hd : DifferentiableAt ℝ
      (fun t' : ℝ =>
        let arc_point :=
          Complex.exp
            ((Real.pi / 2 +
              (t' - 2) *
                (2 * Real.pi / 3 -
                  Real.pi / 2)) * I)
        let chord_point :=
          chordSegment i_point rho (t' - 2)
        (1 - s) • arc_point +
          s • chord_point) t
  · have h_bound : ‖deriv (fun t' : ℝ =>
        let arc_point :=
          Complex.exp
            ((Real.pi / 2 +
              (t' - 2) *
                (2 * Real.pi / 3 -
                  Real.pi / 2)) * I)
        let chord_point :=
          chordSegment i_point rho (t' - 2)
        (1 - s) • arc_point +
          s • chord_point) t‖ ≤
        |1 - s| * 1 + |s| * 2 := by
      have hpi :
          (2 * Real.pi / 3 -
            Real.pi / 2 : ℂ) =
            Real.pi / 6 := by
        ring
      have func_eq : (fun t' : ℝ =>
            let arc_point :=
              Complex.exp
                ((Real.pi / 2 +
                  (t' - 2) *
                    (2 * Real.pi / 3 -
                      Real.pi / 2)) * I)
            let chord_point :=
              chordSegment i_point rho
                (t' - 2)
            (1 - s) • arc_point +
              s • chord_point) =
          (fun t' : ℝ =>
            let arc_point :=
              Complex.exp
                ((Real.pi / 2 +
                  (t' - 2) *
                    (Real.pi / 6)) * I)
            let chord_point :=
              chordSegment i_point rho
                (t' - 2)
            (1 - s) • arc_point +
              s • chord_point) := by
        ext t'; simp only [hpi]
      rw [func_eq]
      have h_ofReal :
          ∀ x : ℝ, HasDerivAt
            (fun t' : ℝ => (t' : ℂ))
            1 x := fun x => by
        have h :=
          @ContinuousLinearMap.hasDerivAt
            ℝ _ ℂ _ _ x Complex.ofRealCLM
        simp only [
          Complex.ofRealCLM_apply] at h
        exact h
      have h_arc : HasDerivAt
          (fun t' : ℝ =>
            Complex.exp
              (((Real.pi : ℝ) / 2 +
                (t' - 2) *
                  ((Real.pi : ℝ) / 6)) *
                I))
          (((Real.pi : ℝ) / 6) * I *
            Complex.exp
              (((Real.pi : ℝ) / 2 +
                (t - 2) *
                  ((Real.pi : ℝ) / 6)) *
                I))
          t := by
        have h_inner : HasDerivAt
            (fun t' : ℝ =>
              (Real.pi : ℂ) / 2 +
                ((t' : ℂ) - 2) *
                  ((Real.pi : ℂ) / 6))
            ((Real.pi : ℂ) / 6) t := by
          have h_shift :
              HasDerivAt
                (fun t' : ℝ =>
                  (t' : ℂ) - 2)
                1 t :=
            (h_ofReal t).sub_const 2
          have h_mul : HasDerivAt
              (fun t' : ℝ =>
                ((t' : ℂ) - 2) *
                  ((Real.pi : ℂ) / 6))
              ((Real.pi : ℂ) / 6) t := by
            have :=
              h_shift.mul_const
                ((Real.pi : ℂ) / 6)
            simp only [one_mul] at this
            exact this
          have :=
            h_mul.const_add
              ((Real.pi : ℂ) / 2)
          simp only at this
          exact this
        have h_times_I : HasDerivAt
            (fun t' : ℝ =>
              ((Real.pi : ℂ) / 2 +
                ((t' : ℂ) - 2) *
                  ((Real.pi : ℂ) / 6)) * I)
            (((Real.pi : ℂ) / 6) * I) t :=
          h_inner.mul_const I
        have h_exp :
            HasDerivAt Complex.exp
              (Complex.exp
                (((Real.pi : ℂ) / 2 +
                  ((t : ℂ) - 2) *
                    ((Real.pi : ℂ) / 6)) *
                  I))
              (((Real.pi : ℂ) / 2 +
                ((t : ℂ) - 2) *
                  ((Real.pi : ℂ) / 6)) *
                I) :=
          Complex.hasDerivAt_exp _
        have := h_exp.comp t h_times_I
        simp only [
          mul_comm (Complex.exp _)] at this
        exact this
      have h_chord : HasDerivAt
          (fun t' : ℝ =>
            chordSegment i_point rho
              (t' - 2))
          (rho - i_point) t := by
        simp only [chordSegment]
        have h_shift :
            HasDerivAt
              (fun t' : ℝ => t' - 2)
              (1 : ℝ) t :=
          (hasDerivAt_id t).sub_const 2
        have h1 : HasDerivAt
            (fun t' : ℝ =>
              (1 - (t' - 2)) • i_point)
            (-i_point) t := by
          have h_coef : HasDerivAt
              (fun t' : ℝ =>
                (1 - (t' - 2) : ℝ))
              (-1 : ℝ) t := by
            have :=
              (hasDerivAt_const t (1 : ℝ)).sub
                h_shift
            simp only [zero_sub] at this
            convert this using 1
          have :=
            h_coef.smul_const i_point
          simp only [neg_one_smul] at this
          exact this
        have h2 : HasDerivAt
            (fun t' : ℝ =>
              (t' - 2) • rho)
            rho t := by
          have := h_shift.smul_const rho
          simp only [one_smul] at this
          exact this
        convert h1.add h2 using 1
        ring
      have h_combined : HasDerivAt
          (fun t' : ℝ =>
            let arc_point :=
              Complex.exp
                ((Real.pi / 2 +
                  (t' - 2) *
                    (Real.pi / 6)) * I)
            let chord_point :=
              chordSegment i_point rho
                (t' - 2)
            (1 - s) • arc_point +
              s • chord_point)
          ((1 - s) •
            (((Real.pi : ℝ) / 6) * I *
              Complex.exp
                (((Real.pi : ℝ) / 2 +
                  (t - 2) *
                    ((Real.pi : ℝ) / 6)) *
                  I)) +
           s • (rho - i_point)) t := by
        have h1 := h_arc.const_smul (1 - s)
        have h2 := h_chord.const_smul s
        convert h1.add h2
      rw [h_combined.deriv]
      calc ‖(1 - s) •
              (((Real.pi : ℝ) / 6) * I *
                Complex.exp
                  (((Real.pi : ℝ) / 2 +
                    (t - 2) *
                      ((Real.pi : ℝ) / 6)) *
                    I)) +
             s • (rho - i_point)‖
          ≤ ‖(1 - s) •
              (((Real.pi : ℝ) / 6) * I *
                Complex.exp
                  (((Real.pi : ℝ) / 2 +
                    (t - 2) *
                      ((Real.pi : ℝ) / 6)) *
                    I))‖ +
            ‖s • (rho - i_point)‖ :=
          norm_add_le _ _
        _ = |1 - s| *
              ‖((Real.pi : ℝ) / 6) * I *
                Complex.exp
                  (((Real.pi : ℝ) / 2 +
                    (t - 2) *
                      ((Real.pi : ℝ) / 6)) *
                    I)‖ +
            |s| * ‖rho - i_point‖ := by
          rw [norm_smul, norm_smul,
            Real.norm_eq_abs,
            Real.norm_eq_abs]
        _ = |1 - s| *
              ((Real.pi / 6) *
                ‖Complex.exp
                  (((Real.pi : ℝ) / 2 +
                    (t - 2) *
                      ((Real.pi : ℝ) / 6)) *
                    I)‖) +
            |s| * ‖rho - i_point‖ := by
              congr 1
              rw [mul_assoc, norm_mul,
                norm_mul]
              have hpi_norm :
                  ‖(Real.pi : ℂ) / 6‖ =
                    Real.pi / 6 := by
                have h1 :
                    ‖(Real.pi : ℂ)‖ =
                      Real.pi := by
                  rw [Complex.norm_real]
                  exact abs_of_pos
                    Real.pi_pos
                have h2 :
                    ‖(6 : ℂ)‖ = 6 := by
                  norm_num
                rw [norm_div, h1, h2]
              rw [hpi_norm,
                Complex.norm_I, one_mul]
        _ = |1 - s| *
              ((Real.pi / 6) * 1) +
            |s| * ‖rho - i_point‖ := by
              congr 2
              have :
                  ((Real.pi : ℝ) / 2 +
                    (t - 2) *
                      ((Real.pi : ℝ) / 6)) *
                    I =
                  ((Real.pi / 2 +
                    (t - 2) *
                      (Real.pi / 6)) : ℝ) *
                    I := by
                push_cast; ring
              rw [this,
                Complex.norm_exp_ofReal_mul_I]
        _ = |1 - s| * Real.pi / 6 +
            |s| * ‖rho - i_point‖ := by
          ring
        _ ≤ |1 - s| * 1 + |s| * 2 := by
            have h1 :
                |1 - s| * Real.pi / 6 ≤
                  |1 - s| * 1 := by
              have hpos :
                  (0 : ℝ) ≤ |1 - s| :=
                abs_nonneg _
              calc |1 - s| * Real.pi / 6
                    = |1 - s| *
                        (Real.pi / 6) := by
                      ring
                  _ ≤ |1 - s| * 1 :=
                    mul_le_mul_of_nonneg_left
                      hpi6 hpos
            have h2 :
                |s| * ‖rho - i_point‖ ≤
                  |s| * 2 :=
              mul_le_mul_of_nonneg_left
                hrho_i (abs_nonneg _)
            linarith
    calc ‖deriv (fun t' : ℝ =>
          let arc_point :=
            Complex.exp
              ((Real.pi / 2 +
                (t' - 2) *
                  (2 * Real.pi / 3 -
                    Real.pi / 2)) * I)
          let chord_point :=
            chordSegment i_point rho
              (t' - 2)
          (1 - s) • arc_point +
            s • chord_point) t‖
        ≤ |1 - s| * 1 + |s| * 2 :=
          h_bound
      _ ≤ 1 * 1 + 1 * 2 := by
          nlinarith [h1s, hs']
      _ = 3 := by norm_num
      _ ≤ 5 := by norm_num
  · simp only [
      deriv_zero_of_not_differentiableAt hd,
      norm_zero]
    norm_num

/-- Segment 2 derivative bound for t in (1,2). -/
lemma fdBoundaryToPolygonHomotopy_seg2_deriv_bound
    (t : ℝ) (_ht : t ∈ Ioo 1 2)
    (s : ℝ) (hs : s ∈ Icc 0 1) :
    ‖deriv (fun t' : ℝ =>
      let arc_point :=
        Complex.exp
          ((Real.pi / 3 +
            (t' - 1) *
              (Real.pi / 2 -
                Real.pi / 3)) * I)
      let chord_point :=
        chordSegment rho' i_point (t' - 1)
      (1 - s) • arc_point +
        s • chord_point) t‖ ≤ 5 :=
  norm_deriv_H_seg2_le t s hs

/-- Segment 3 derivative bound for t in (2,3). -/
lemma fdBoundaryToPolygonHomotopy_seg3_deriv_bound
    (t : ℝ) (_ht : t ∈ Ioo 2 3)
    (s : ℝ) (hs : s ∈ Icc 0 1) :
    ‖deriv (fun t' : ℝ =>
      let arc_point :=
        Complex.exp
          ((Real.pi / 2 +
            (t' - 2) *
              (2 * Real.pi / 3 -
                Real.pi / 2)) * I)
      let chord_point :=
        chordSegment i_point rho (t' - 2)
      (1 - s) • arc_point +
        s • chord_point) t‖ ≤ 5 :=
  norm_deriv_H_seg3_le t s hs

/-- Segment 1 derivative bound. -/
lemma norm_deriv_H_seg1_le
    (t : ℝ) (_s : ℝ) :
    ‖deriv (fun t' : ℝ =>
      (1/2 : ℂ) +
        (H_height - (↑t' : ℂ) *
          (H_height - Real.sqrt 3 / 2)) *
          I) t‖ ≤ 5 := by
  have h_height :
      (H_height : ℂ) - Real.sqrt 3 / 2 =
        1 := by
    simp only [H_height]
    push_cast
    ring
  have h_deriv : HasDerivAt
      (fun t' : ℝ =>
        (1/2 : ℂ) +
          ((H_height : ℂ) - (↑t' : ℂ) *
            ((H_height : ℂ) -
              Real.sqrt 3 / 2)) * I)
      (-((H_height : ℂ) -
        Real.sqrt 3 / 2) * I) t := by
    have h1 :
        HasDerivAt
          (fun t' : ℝ => (↑t' : ℂ))
          1 t :=
      Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt
        (fun t' : ℝ =>
          (↑t' : ℂ) *
            ((H_height : ℂ) -
              Real.sqrt 3 / 2))
        ((H_height : ℂ) -
          Real.sqrt 3 / 2) t := by
      have :=
        h1.mul_const
          ((H_height : ℂ) -
            Real.sqrt 3 / 2)
      simp only [one_mul] at this
      exact this
    have h3 : HasDerivAt
        (fun t' : ℝ =>
          (H_height : ℂ) - (↑t' : ℂ) *
            ((H_height : ℂ) -
              Real.sqrt 3 / 2))
        (-((H_height : ℂ) -
          Real.sqrt 3 / 2)) t := by
      have :=
        (hasDerivAt_const t
          (H_height : ℂ)).sub h2
      simp only [zero_sub] at this
      exact this
    have h4 : HasDerivAt
        (fun t' : ℝ =>
          ((H_height : ℂ) - (↑t' : ℂ) *
            ((H_height : ℂ) -
              Real.sqrt 3 / 2)) * I)
        (-((H_height : ℂ) -
          Real.sqrt 3 / 2) * I) t :=
      h3.mul_const I
    have :=
      (hasDerivAt_const t ((1/2 : ℂ))).add
        h4
    simp only [zero_add] at this
    exact this
  rw [h_deriv.deriv, h_height]
  simp only [neg_one_mul, norm_neg,
    Complex.norm_I]
  norm_num

/-- Segment 4 derivative bound. -/
lemma norm_deriv_H_seg4_le
    (t : ℝ) (_s : ℝ) :
    ‖deriv (fun t' : ℝ =>
      (-1/2 : ℂ) +
        ((Real.sqrt 3 / 2 : ℂ) +
          ((↑t' : ℂ) - 3) *
            ((H_height : ℂ) -
              Real.sqrt 3 / 2)) * I)
      t‖ ≤ 5 := by
  have h_height :
      (H_height : ℂ) - Real.sqrt 3 / 2 =
        1 := by
    simp only [H_height]
    push_cast
    ring
  have h_deriv : HasDerivAt
      (fun t' : ℝ =>
        (-1/2 : ℂ) +
          ((Real.sqrt 3 / 2 : ℂ) +
            ((↑t' : ℂ) - 3) *
              ((H_height : ℂ) -
                Real.sqrt 3 / 2)) * I)
      (((H_height : ℂ) -
        Real.sqrt 3 / 2) * I) t := by
    have h1 :
        HasDerivAt
          (fun t' : ℝ => (↑t' : ℂ))
          1 t :=
      Complex.ofRealCLM.hasDerivAt
    have h2 :
        HasDerivAt
          (fun t' : ℝ => (↑t' : ℂ) - 3)
          1 t :=
      h1.sub_const 3
    have h3 : HasDerivAt
        (fun t' : ℝ =>
          ((↑t' : ℂ) - 3) *
            ((H_height : ℂ) -
              Real.sqrt 3 / 2))
        ((H_height : ℂ) -
          Real.sqrt 3 / 2) t := by
      have :=
        h2.mul_const
          ((H_height : ℂ) -
            Real.sqrt 3 / 2)
      simp only [one_mul] at this
      exact this
    have h4 : HasDerivAt
        (fun t' : ℝ =>
          (Real.sqrt 3 / 2 : ℂ) +
            ((↑t' : ℂ) - 3) *
              ((H_height : ℂ) -
                Real.sqrt 3 / 2))
        ((H_height : ℂ) -
          Real.sqrt 3 / 2) t := by
      have :=
        (hasDerivAt_const t
          (Real.sqrt 3 / 2 : ℂ)).add h3
      simp only [zero_add] at this
      exact this
    have h5 : HasDerivAt
        (fun t' : ℝ =>
          ((Real.sqrt 3 / 2 : ℂ) +
            ((↑t' : ℂ) - 3) *
              ((H_height : ℂ) -
                Real.sqrt 3 / 2)) * I)
        (((H_height : ℂ) -
          Real.sqrt 3 / 2) * I) t :=
      h4.mul_const I
    have :=
      (hasDerivAt_const t ((-1/2 : ℂ))).add
        h5
    simp only [zero_add] at this
    exact this
  rw [h_deriv.deriv, h_height]
  simp only [one_mul, Complex.norm_I]
  norm_num

/-- Segment 5 derivative bound. -/
lemma norm_deriv_H_seg5_le
    (t : ℝ) (_s : ℝ) :
    ‖deriv (fun t' : ℝ =>
      ((↑t' : ℂ) - 9/2) +
        (H_height : ℂ) * I) t‖ ≤ 5 := by
  have h_deriv : HasDerivAt
      (fun t' : ℝ =>
        ((↑t' : ℂ) - 9/2) +
          (H_height : ℂ) * I) 1 t := by
    have h1 :
        HasDerivAt
          (fun t' : ℝ => (↑t' : ℂ))
          1 t :=
      Complex.ofRealCLM.hasDerivAt
    have h2 :
        HasDerivAt
          (fun t' : ℝ =>
            (↑t' : ℂ) - 9/2) 1 t :=
      h1.sub_const (9/2)
    have := h2.add_const ((H_height : ℂ) * I)
    convert this using 1
  rw [h_deriv.deriv]
  norm_num

end RectHomotopyProof
