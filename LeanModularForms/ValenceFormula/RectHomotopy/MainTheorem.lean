import LeanModularForms.GeneralizedResidueTheory.Homotopy.CircleParam
import LeanModularForms.ValenceFormula.RectHomotopy.BoundaryHomotopyDiff
import LeanModularForms.ValenceFormula.RectHomotopy.MainTheoremBound
import LeanModularForms.ValenceFormula.RectHomotopy.MainTheoremDerivCont
import LeanModularForms.ValenceFormula.RectHomotopy.WindingProof

/-!
# Main winding number theorem for the fundamental domain boundary

The generalized winding number of `fdBoundary` around
interior points equals -1 (clockwise).
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

private lemma fdBoundaryToPolygonHomotopy_diffAt_off_partition
    (t : ℝ) (ht : t ∈ Ioo 0 5)
    (ht_not_P : t ∉ ({1, 2, 3, 4} : Finset ℝ))
    (s : ℝ) (_hs : s ∈ Icc (0:ℝ) 1) :
    DifferentiableAt ℝ
      (fun t' => fdBoundaryToPolygonHomotopy (t', s)) t := by
  simp only [Finset.mem_insert,
    Finset.mem_singleton, not_or] at ht_not_P
  obtain ⟨hne1, hne2, hne3, hne4⟩ := ht_not_P
  by_cases h1 : t < 1
  · have heq :
        (fun t' : ℝ =>
          fdBoundaryToPolygonHomotopy (t', s))
          =ᶠ[𝓝 t]
        (fun t' : ℝ =>
          (1/2 : ℂ) +
            (H_height - (↑t' : ℂ) *
              (H_height -
                Real.sqrt 3 / 2)) * I) := by
      filter_upwards [eventually_lt_nhds h1]
        with t' ht'
      simp only [fdBoundaryToPolygonHomotopy,
        le_of_lt ht', ite_true]
    exact heq.differentiableAt_iff.mpr
      (fdBoundaryToPolygonHomotopy_seg1_differentiable
        t s)
  · push_neg at h1
    by_cases h2 : t < 2
    · have ht1 : t > 1 :=
        lt_of_le_of_ne h1 (Ne.symm hne1)
      have heq :
          (fun t' : ℝ =>
            fdBoundaryToPolygonHomotopy (t', s))
            =ᶠ[𝓝 t]
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
              s • chord_point) := by
        filter_upwards [
          eventually_gt_nhds ht1,
          eventually_lt_nhds h2]
          with t' ht1' ht2'
        simp only [fdBoundaryToPolygonHomotopy]
        simp only [not_le.mpr ht1', ite_false,
          le_of_lt ht2', ite_true]
      exact heq.differentiableAt_iff.mpr
        (fdBoundaryToPolygonHomotopy_seg2_differentiable
          t s)
    · push_neg at h2
      by_cases h3 : t < 3
      · have ht2 : t > 2 :=
          lt_of_le_of_ne h2 (Ne.symm hne2)
        have heq :
            (fun t' : ℝ =>
              fdBoundaryToPolygonHomotopy (t', s))
              =ᶠ[𝓝 t]
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
                s • chord_point) := by
          filter_upwards [
            eventually_gt_nhds ht2,
            eventually_lt_nhds h3]
            with t' ht2' ht3'
          simp only [fdBoundaryToPolygonHomotopy]
          simp only [
            not_le.mpr (lt_trans
              (by norm_num : (1:ℝ) < 2) ht2'),
            ite_false, not_le.mpr ht2',
            le_of_lt ht3', ite_true]
        exact heq.differentiableAt_iff.mpr
          (fdBoundaryToPolygonHomotopy_seg3_differentiable
            t s)
      · push_neg at h3
        by_cases h4 : t < 4
        · have ht3 : t > 3 :=
            lt_of_le_of_ne h3 (Ne.symm hne3)
          have heq :
              (fun t' : ℝ =>
                fdBoundaryToPolygonHomotopy
                  (t', s)) =ᶠ[𝓝 t]
              (fun t' : ℝ =>
                (-1/2 : ℂ) +
                  (Real.sqrt 3 / 2 +
                    ((↑t' : ℂ) - 3) *
                      (H_height -
                        Real.sqrt 3 / 2)) *
                    I) := by
            filter_upwards [
              eventually_gt_nhds ht3,
              eventually_lt_nhds h4]
              with t' ht3' ht4'
            simp only
              [fdBoundaryToPolygonHomotopy]
            simp only [
              not_le.mpr (lt_trans
                (by norm_num : (1:ℝ) < 3)
                ht3'),
              ite_false,
              not_le.mpr (lt_trans
                (by norm_num : (2:ℝ) < 3)
                ht3'),
              not_le.mpr ht3',
              le_of_lt ht4', ite_true]
          exact heq.differentiableAt_iff.mpr
            (fdBoundaryToPolygonHomotopy_seg4_differentiable
              t s)
        · push_neg at h4
          have ht4 : t > 4 :=
            lt_of_le_of_ne h4 (Ne.symm hne4)
          have ht5 : t < 5 := ht.2
          have heq :
              (fun t' : ℝ =>
                fdBoundaryToPolygonHomotopy
                  (t', s)) =ᶠ[𝓝 t]
              (fun t' : ℝ =>
                ((↑t' : ℂ) - 9/2) +
                  H_height * I) := by
            filter_upwards [
              eventually_gt_nhds ht4,
              eventually_lt_nhds ht5]
              with t' ht4' _ht5'
            simp only
              [fdBoundaryToPolygonHomotopy]
            simp only [
              not_le.mpr (lt_trans
                (by norm_num : (1:ℝ) < 4)
                ht4'),
              ite_false,
              not_le.mpr (lt_trans
                (by norm_num : (2:ℝ) < 4)
                ht4'),
              not_le.mpr (lt_trans
                (by norm_num : (3:ℝ) < 4)
                ht4'),
              not_le.mpr ht4']
          exact heq.differentiableAt_iff.mpr
            (fdBoundaryToPolygonHomotopy_seg5_differentiable
              t s)

/-- For interior points p in the fundamental domain,
    the generalized winding number of the FD boundary
    around p equals -1 (clockwise orientation). -/
theorem generalizedWindingNumber_fdBoundary_eq_neg_one
    (p : ℂ) (hp_norm : ‖p‖ > 1)
    (hp_re : |p.re| < 1/2)
    (hp_im_pos : 0 < p.im)
    (hp_im : p.im < H_height) :
    generalizedWindingNumber' fdBoundary 0 5 p
      = -1 := by
  have hab : (0 : ℝ) < 5 := by norm_num
  have hγ_cont :
      ContinuousOn fdBoundary (Icc 0 5) := by
    have hcomp : Continuous
        (fun t : ℝ =>
          fdBoundaryToPolygonHomotopy (t, 0)) := by
      exact fdBoundaryToPolygonHomotopy_continuous.comp
        (continuous_id.prodMk continuous_const)
    apply hcomp.continuousOn.congr
    intro t ht
    exact (fdBoundaryToPolygonHomotopy_at_zero
      t ht).symm
  have hγ_ne :
      ∀ t ∈ Icc 0 5, fdBoundary t ≠ p := by
    intro t ht
    have hs : (0 : ℝ) ∈ Icc 0 1 :=
      ⟨le_refl _, by norm_num⟩
    have h :=
      fdBoundaryToPolygonHomotopy_avoids p
        hp_norm hp_re hp_im t ht 0 hs
    rw [fdBoundaryToPolygonHomotopy_at_zero
      t ht] at h
    exact h
  have hγ_closed :
      fdBoundary 0 = fdBoundary 5 :=
    fdBoundary_at_zero.trans
      fdBoundary_at_five.symm
  let P : Finset ℝ := {1, 2, 3, 4}
  have hP_subset : (P : Set ℝ) ⊆ Icc 0 5 := by
    intro t ht
    simp only [P, Finset.coe_insert,
      Finset.coe_singleton,
      Set.mem_insert_iff,
      Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl
      <;> constructor <;> norm_num
  have hH1_diff :
      ∀ t ∈ Ioo 0 5, t ∉ P →
        ∀ s ∈ Icc (0:ℝ) 1,
          DifferentiableAt ℝ
            (fun t' =>
              fdBoundaryToPolygonHomotopy (t', s))
            t := by
    intro t ht ht_not_P s hs
    exact fdBoundaryToPolygonHomotopy_diffAt_off_partition
      t ht ht_not_P s hs
  have hH1_deriv_cont :
      ∀ p₁ p₂ : ℝ, p₁ < p₂ →
        (∀ t ∈ Ioo p₁ p₂, t ∉ P) →
        Ioo p₁ p₂ ⊆ Ioo 0 5 →
      ContinuousOn
        (fun (q : ℝ × ℝ) =>
          deriv (fun t' =>
            fdBoundaryToPolygonHomotopy
              (t', q.2)) q.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1) :=
    fun p₁ p₂ hp hpiece hsub =>
      fdBoundaryToPolygonHomotopy_deriv_continuousOn_pieces
        p₁ p₂ hp hpiece hsub
  have hH1_bound :
      ∃ M : ℝ, ∀ t ∈ Icc 0 5,
        ∀ s ∈ Icc (0:ℝ) 1,
          ‖deriv (fun t' =>
            fdBoundaryToPolygonHomotopy
              (t', s)) t‖ ≤ M :=
    fdBoundaryToPolygonHomotopy_deriv_bound
  have hhom₁ :
      PiecewiseCurvesHomotopicAvoiding
        fdBoundary fdPolygon 0 5 p P :=
    ⟨fdBoundaryToPolygonHomotopy,
     fdBoundaryToPolygonHomotopy_continuous,
     fun t ht =>
      fdBoundaryToPolygonHomotopy_at_zero t ht,
     fun t ht =>
      fdBoundaryToPolygonHomotopy_at_one t ht,
     fun s hs =>
      fdBoundaryToPolygonHomotopy_closed s hs,
     fun t ht s hs =>
      fdBoundaryToPolygonHomotopy_avoids p
        hp_norm hp_re hp_im t ht s hs,
     hH1_diff,
     hH1_deriv_cont,
     hH1_bound⟩
  have h_wind_eq1 :
      generalizedWindingNumber' fdBoundary
        0 5 p =
      generalizedWindingNumber' fdPolygon
        0 5 p :=
    windingNumber_eq_of_piecewise_homotopic
      fdBoundary fdPolygon 0 5 p P hab hhom₁
  have h_wind_eq2 :
      generalizedWindingNumber' fdPolygon
        0 5 p =
      generalizedWindingNumber'
        (circleParamCW p 1 0 5) 0 5 p :=
    winding_fdPolygon_eq_circleParamCW p
      hp_norm hp_re hp_im_pos hp_im
  have h_circle :
      generalizedWindingNumber'
        (circleParamCW p 1 0 5) 0 5 p = -1 :=
    circleParamCW_winding_eq_neg_one p 1
      (by norm_num : (0:ℝ) < 1) 0 5 hab
  rw [h_wind_eq1, h_wind_eq2, h_circle]

end RectHomotopyProof
