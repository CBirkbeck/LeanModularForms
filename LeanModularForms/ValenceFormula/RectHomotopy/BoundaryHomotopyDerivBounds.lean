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

/-! ### Shared arc-chord homotopy derivative bound

The segments 2 and 3 of the homotopy both interpolate between an arc of the unit circle
and a chord between two unit-norm points. The derivative bound is identical in both cases:
`|1-s| * pi/6 + |s| * 2 <= 3 <= 5`.
-/

/-- Generic norm bound for the derivative of a homotopy between an arc segment of the
unit circle and a chord between two points of norm 1. The arc has angular speed `pi/6`
and the chord has length at most 2, giving bound `|1-s| * pi/6 + |s| * 2 <= 3 <= 5`.

Parameters:
- `θ₀` : starting angle of the arc
- `n` : offset (the function is `t' ↦ arc(t'-n), chord(t'-n)`)
- `p q` : chord endpoints with `‖p‖ = 1`, `‖q‖ = 1`
- `hpq_diff` : the angular difference `θ_end - θ₀` simplifies to `pi/6` -/
lemma norm_deriv_homotopy_arc_chord_le (t s : ℝ) (hs : s ∈ Icc (0:ℝ) 1)
    (θ₀ : ℝ) (n : ℝ) (p q : ℂ) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (_hfunc_eq : ∀ t' : ℝ,
      (1 - s) • Complex.exp ((↑θ₀ + (↑(t' - n)) * (↑(Real.pi / 6))) * I) +
        s • chordSegment p q (t' - n) =
      (1 - s) • Complex.exp ((↑θ₀ + (↑(t' - n)) * (↑(Real.pi / 6))) * I) +
        s • chordSegment p q (t' - n)) :
    ‖deriv (fun t' : ℝ =>
      (1 - s) • Complex.exp ((↑θ₀ + (↑(t' - n)) * (↑(Real.pi / 6))) * I) +
        s • chordSegment p q (t' - n)) t‖ ≤ 5 := by
  have h1s : |1 - s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have hs' : |s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have hpi6 : Real.pi / 6 ≤ 1 := by have := Real.pi_le_four; linarith
  have hpq : ‖q - p‖ ≤ 2 := by
    calc ‖q - p‖ ≤ ‖q‖ + ‖p‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [hp, hq]
      _ = 2 := by norm_num
  by_cases hd : DifferentiableAt ℝ (fun t' : ℝ =>
      (1 - s) • Complex.exp ((↑θ₀ + (↑(t' - n)) * (↑(Real.pi / 6))) * I) +
        s • chordSegment p q (t' - n)) t
  · -- Compute HasDerivAt for the arc component
    have h_arc : HasDerivAt (fun t' : ℝ =>
          Complex.exp ((↑θ₀ + (↑(t' - n)) * (↑(Real.pi / 6))) * I))
        ((↑(Real.pi / 6)) * I *
          Complex.exp ((↑θ₀ + (↑(t - n)) * (↑(Real.pi / 6))) * I)) t := by
      have h_inner : HasDerivAt (fun t' : ℝ =>
            (↑θ₀ : ℂ) + ((↑t' : ℂ) - ↑n) * (↑(Real.pi / 6)))
          ((↑(Real.pi / 6) : ℂ)) t := by
        have h_shift : HasDerivAt (fun t' : ℝ => (↑t' : ℂ) - ↑n) 1 t :=
          Complex.ofRealCLM.hasDerivAt.sub_const ↑n
        have h_mul := h_shift.mul_const (↑(Real.pi / 6) : ℂ)
        simp only [one_mul] at h_mul
        exact h_mul.const_add (↑θ₀ : ℂ)
      have h_timesI := h_inner.mul_const I
      have h_comp := (Complex.hasDerivAt_exp _).comp t h_timesI
      convert h_comp using 1
      · ext t'; simp only [Function.comp]; push_cast; ring
      · push_cast; ring
    -- Compute HasDerivAt for the chord component
    have h_chord : HasDerivAt (fun t' : ℝ => chordSegment p q (t' - n)) (q - p) t := by
      simp only [chordSegment]
      have h_shift : HasDerivAt (fun t' : ℝ => t' - n) (1 : ℝ) t := (hasDerivAt_id t).sub_const n
      have h1 : HasDerivAt (fun t' : ℝ => (1 - (t' - n)) • p) (-p) t := by
        have h_coef : HasDerivAt (fun t' : ℝ => (1 - (t' - n) : ℝ)) (-1 : ℝ) t := by
          have := (hasDerivAt_const t (1 : ℝ)).sub h_shift
          simp only [zero_sub] at this; convert this using 1
        exact (h_coef.smul_const p).congr_deriv (by simp only [neg_one_smul])
      have h2 : HasDerivAt (fun t' : ℝ => (t' - n) • q) q t := by
        exact (h_shift.smul_const q).congr_deriv (by simp only [one_smul])
      exact (h1.add h2).congr_deriv (by ring)
    -- Combined HasDerivAt
    have h_combined : HasDerivAt (fun t' : ℝ =>
          (1 - s) • Complex.exp ((↑θ₀ + (↑(t' - n)) * (↑(Real.pi / 6))) * I) +
            s • chordSegment p q (t' - n))
        ((1 - s) • ((↑(Real.pi / 6)) * I *
            Complex.exp ((↑θ₀ + (↑(t - n)) * (↑(Real.pi / 6))) * I)) +
         s • (q - p)) t :=
      (h_arc.const_smul (1 - s)).add (h_chord.const_smul s)
    rw [h_combined.deriv]
    calc ‖(1 - s) • ((↑(Real.pi / 6)) * I *
              Complex.exp ((↑θ₀ + (↑(t - n)) * (↑(Real.pi / 6))) * I)) +
           s • (q - p)‖
        ≤ ‖(1 - s) • ((↑(Real.pi / 6)) * I *
              Complex.exp ((↑θ₀ + (↑(t - n)) * (↑(Real.pi / 6))) * I))‖ +
          ‖s • (q - p)‖ := norm_add_le _ _
      _ = |1 - s| * ‖(↑(Real.pi / 6)) * I *
              Complex.exp ((↑θ₀ + (↑(t - n)) * (↑(Real.pi / 6))) * I)‖ +
          |s| * ‖q - p‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ = |1 - s| * ((Real.pi / 6) * 1) + |s| * ‖q - p‖ := by
            congr 2
            rw [mul_assoc, norm_mul, norm_mul]
            rw [show ‖(↑(Real.pi / 6) : ℂ)‖ = Real.pi / 6 from by
              rw [Complex.norm_real]; exact abs_of_pos (by positivity)]
            rw [Complex.norm_I, one_mul]
            congr 1
            rw [show (↑θ₀ + (↑(t - n)) * (↑(Real.pi / 6))) * I =
              ((θ₀ + (t - n) * (Real.pi / 6)) : ℝ) * I from by push_cast; ring]
            exact Complex.norm_exp_ofReal_mul_I _
      _ = |1 - s| * Real.pi / 6 + |s| * ‖q - p‖ := by ring
      _ ≤ |1 - s| * 1 + |s| * 2 := by
            nlinarith [abs_nonneg (1 - s), abs_nonneg s]
      _ ≤ 1 * 1 + 1 * 2 := by nlinarith [h1s, hs']
      _ = 3 := by norm_num
      _ ≤ 5 := by norm_num
  · simp only [deriv_zero_of_not_differentiableAt hd, norm_zero]; norm_num

/-- Norm bound for segment 2 derivative. -/
lemma norm_deriv_H_seg2_le (t s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    ‖deriv (fun t' : ℝ =>
      let arc_point :=
        Complex.exp ((Real.pi / 3 +
            (t' - 1) * (Real.pi / 2 -
                Real.pi / 3)) * I)
      let chord_point :=
        chordSegment rho' i_point (t' - 1)
      (1 - s) • arc_point +
        s • chord_point) t‖ ≤ 5 := by
  -- Simplify angular difference to pi/6
  have func_eq : (fun t' : ℝ =>
        let arc_point := Complex.exp ((Real.pi / 3 + (t' - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
        let chord_point := chordSegment rho' i_point (t' - 1)
        (1 - s) • arc_point + s • chord_point) =
      (fun t' : ℝ =>
        (1 - s) • Complex.exp ((↑(Real.pi / 3) + ↑(t' - 1) * ↑(Real.pi / 6)) * I) +
          s • chordSegment rho' i_point (t' - 1)) := by
    ext t'; dsimp only; congr 2; congr 1; congr 1; push_cast; ring
  rw [func_eq]
  exact norm_deriv_homotopy_arc_chord_le t s hs (Real.pi / 3) 1 rho' i_point
    rho'_norm i_point_norm (fun _ => rfl)

/-- Norm bound for segment 3 derivative. -/
lemma norm_deriv_H_seg3_le (t s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    ‖deriv (fun t' : ℝ =>
      let arc_point :=
        Complex.exp ((Real.pi / 2 +
            (t' - 2) * (2 * Real.pi / 3 -
                Real.pi / 2)) * I)
      let chord_point :=
        chordSegment i_point rho (t' - 2)
      (1 - s) • arc_point +
        s • chord_point) t‖ ≤ 5 := by
  -- Simplify angular difference to pi/6
  have func_eq : (fun t' : ℝ =>
        let arc_point := Complex.exp ((Real.pi / 2 + (t' - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
        let chord_point := chordSegment i_point rho (t' - 2)
        (1 - s) • arc_point + s • chord_point) =
      (fun t' : ℝ =>
        (1 - s) • Complex.exp ((↑(Real.pi / 2) + ↑(t' - 2) * ↑(Real.pi / 6)) * I) +
          s • chordSegment i_point rho (t' - 2)) := by
    ext t'; dsimp only; congr 2; congr 1; congr 1; push_cast; ring
  rw [func_eq]
  exact norm_deriv_homotopy_arc_chord_le t s hs (Real.pi / 2) 2 i_point rho
    i_point_norm rho_norm (fun _ => rfl)

/-- Segment 2 derivative bound for t in (1,2). -/
lemma fdBoundaryToPolygonHomotopy_seg2_deriv_bound (t : ℝ) (_ht : t ∈ Ioo 1 2)
    (s : ℝ) (hs : s ∈ Icc 0 1) :
    ‖deriv (fun t' : ℝ =>
      let arc_point :=
        Complex.exp ((Real.pi / 3 +
            (t' - 1) * (Real.pi / 2 -
                Real.pi / 3)) * I)
      let chord_point :=
        chordSegment rho' i_point (t' - 1)
      (1 - s) • arc_point +
        s • chord_point) t‖ ≤ 5 :=
  norm_deriv_H_seg2_le t s hs

/-- Segment 3 derivative bound for t in (2,3). -/
lemma fdBoundaryToPolygonHomotopy_seg3_deriv_bound (t : ℝ) (_ht : t ∈ Ioo 2 3)
    (s : ℝ) (hs : s ∈ Icc 0 1) :
    ‖deriv (fun t' : ℝ =>
      let arc_point :=
        Complex.exp ((Real.pi / 2 +
            (t' - 2) * (2 * Real.pi / 3 -
                Real.pi / 2)) * I)
      let chord_point :=
        chordSegment i_point rho (t' - 2)
      (1 - s) • arc_point +
        s • chord_point) t‖ ≤ 5 :=
  norm_deriv_H_seg3_le t s hs

/-- Segment 1 derivative bound. -/
lemma norm_deriv_H_seg1_le (t : ℝ) (_s : ℝ) :
    ‖deriv (fun t' : ℝ => (1/2 : ℂ) +
        (H_height - (↑t' : ℂ) * (H_height - Real.sqrt 3 / 2)) *
          I) t‖ ≤ 5 := by
  have h_height : (H_height : ℂ) - Real.sqrt 3 / 2 =
        1 := by
    simp only [H_height]
    push_cast
    ring
  have h_deriv : HasDerivAt (fun t' : ℝ =>
        (1/2 : ℂ) + ((H_height : ℂ) - (↑t' : ℂ) *
            ((H_height : ℂ) -
              Real.sqrt 3 / 2)) * I)
      (-((H_height : ℂ) -
        Real.sqrt 3 / 2) * I) t := by
    have h1 :
        HasDerivAt (fun t' : ℝ => (↑t' : ℂ))
          1 t :=
      Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun t' : ℝ =>
          (↑t' : ℂ) * ((H_height : ℂ) -
              Real.sqrt 3 / 2))
        ((H_height : ℂ) -
          Real.sqrt 3 / 2) t := by
      have :=
        h1.mul_const ((H_height : ℂ) -
            Real.sqrt 3 / 2)
      simp only [one_mul] at this
      exact this
    have h3 : HasDerivAt (fun t' : ℝ =>
          (H_height : ℂ) - (↑t' : ℂ) * ((H_height : ℂ) -
              Real.sqrt 3 / 2))
        (-((H_height : ℂ) -
          Real.sqrt 3 / 2)) t := by
      have := (hasDerivAt_const t
          (H_height : ℂ)).sub h2
      simp only [zero_sub] at this
      exact this
    have h4 : HasDerivAt (fun t' : ℝ =>
          ((H_height : ℂ) - (↑t' : ℂ) * ((H_height : ℂ) -
              Real.sqrt 3 / 2)) * I)
        (-((H_height : ℂ) -
          Real.sqrt 3 / 2) * I) t :=
      h3.mul_const I
    have := (hasDerivAt_const t ((1/2 : ℂ))).add
        h4
    simp only [zero_add] at this
    exact this
  rw [h_deriv.deriv, h_height]
  simp only [neg_one_mul, norm_neg,
    Complex.norm_I]
  norm_num

/-- Segment 4 derivative bound. -/
lemma norm_deriv_H_seg4_le (t : ℝ) (_s : ℝ) :
    ‖deriv (fun t' : ℝ => (-1/2 : ℂ) +
        ((Real.sqrt 3 / 2 : ℂ) + ((↑t' : ℂ) - 3) *
            ((H_height : ℂ) -
              Real.sqrt 3 / 2)) * I)
      t‖ ≤ 5 := by
  have h_height : (H_height : ℂ) - Real.sqrt 3 / 2 =
        1 := by
    simp only [H_height]
    push_cast
    ring
  have h_deriv : HasDerivAt (fun t' : ℝ =>
        (-1/2 : ℂ) + ((Real.sqrt 3 / 2 : ℂ) +
            ((↑t' : ℂ) - 3) * ((H_height : ℂ) -
                Real.sqrt 3 / 2)) * I)
      (((H_height : ℂ) -
        Real.sqrt 3 / 2) * I) t := by
    have h1 :
        HasDerivAt (fun t' : ℝ => (↑t' : ℂ))
          1 t :=
      Complex.ofRealCLM.hasDerivAt
    have h2 :
        HasDerivAt (fun t' : ℝ => (↑t' : ℂ) - 3)
          1 t :=
      h1.sub_const 3
    have h3 : HasDerivAt (fun t' : ℝ =>
          ((↑t' : ℂ) - 3) * ((H_height : ℂ) -
              Real.sqrt 3 / 2))
        ((H_height : ℂ) -
          Real.sqrt 3 / 2) t := by
      have :=
        h2.mul_const ((H_height : ℂ) -
            Real.sqrt 3 / 2)
      simp only [one_mul] at this
      exact this
    have h4 : HasDerivAt (fun t' : ℝ =>
          (Real.sqrt 3 / 2 : ℂ) + ((↑t' : ℂ) - 3) *
              ((H_height : ℂ) -
                Real.sqrt 3 / 2))
        ((H_height : ℂ) -
          Real.sqrt 3 / 2) t := by
      have := (hasDerivAt_const t
          (Real.sqrt 3 / 2 : ℂ)).add h3
      simp only [zero_add] at this
      exact this
    have h5 : HasDerivAt (fun t' : ℝ =>
          ((Real.sqrt 3 / 2 : ℂ) + ((↑t' : ℂ) - 3) *
              ((H_height : ℂ) -
                Real.sqrt 3 / 2)) * I)
        (((H_height : ℂ) -
          Real.sqrt 3 / 2) * I) t :=
      h4.mul_const I
    have := (hasDerivAt_const t ((-1/2 : ℂ))).add
        h5
    simp only [zero_add] at this
    exact this
  rw [h_deriv.deriv, h_height]
  simp only [one_mul, Complex.norm_I]
  norm_num

/-- Segment 5 derivative bound. -/
lemma norm_deriv_H_seg5_le (t : ℝ) (_s : ℝ) :
    ‖deriv (fun t' : ℝ => ((↑t' : ℂ) - 9/2) +
        (H_height : ℂ) * I) t‖ ≤ 5 := by
  have h_deriv : HasDerivAt (fun t' : ℝ =>
        ((↑t' : ℂ) - 9/2) + (H_height : ℂ) * I) 1 t := by
    have h1 :
        HasDerivAt (fun t' : ℝ => (↑t' : ℂ))
          1 t :=
      Complex.ofRealCLM.hasDerivAt
    have h2 :
        HasDerivAt (fun t' : ℝ =>
            (↑t' : ℂ) - 9/2) 1 t :=
      h1.sub_const (9/2)
    have := h2.add_const ((H_height : ℂ) * I)
    convert this using 1
  rw [h_deriv.deriv]
  norm_num

end RectHomotopyProof
