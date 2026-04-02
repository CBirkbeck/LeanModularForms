import LeanModularForms.ValenceFormula.RectHomotopy.BoundaryHomotopySmooth

/-!
# Derivative continuity for the homotopy on partition pieces

Proves that the t-derivative of `fdBoundaryToPolygonHomotopy` is continuous
on each partition piece `(p₁, p₂) × [0, 1]`, where `(p₁, p₂)` avoids the
partition points `{1, 2, 3, 4}`.
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

lemma fdBoundaryToPolygonHomotopy_deriv_continuousOn_pieces (p₁ p₂ : ℝ) (hp₁p₂ : p₁ < p₂)
    (hpiece : ∀ t ∈ Ioo p₁ p₂,
      t ∉ ({1, 2, 3, 4} : Finset ℝ))
    (h_sub : Ioo p₁ p₂ ⊆ Ioo 0 5) :
    ContinuousOn (fun (q : ℝ × ℝ) =>
        deriv (fun t' =>
          fdBoundaryToPolygonHomotopy (t', q.2)) q.1)
      (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
  have hseg :=
    interval_in_segment p₁ p₂ hp₁p₂ hpiece h_sub
  rcases hseg with
    h_seg1 | ⟨h_seg2_lo, h_seg2_hi⟩ |
    ⟨h_seg3_lo, h_seg3_hi⟩ |
    ⟨h_seg4_lo, h_seg4_hi⟩ | h_seg5
  · have hconst :
        ∀ q ∈ Ioo p₁ p₂ ×ˢ Icc (0:ℝ) 1,
          deriv (fun t' =>
            fdBoundaryToPolygonHomotopy (t', q.2)) q.1 =
          -((H_height : ℂ) -
            Real.sqrt 3 / 2) * I := by
      intro q ⟨hq1, _hq2⟩
      have ht_lt1 : q.1 < 1 :=
        lt_of_lt_of_le hq1.2 h_seg1
      have heq : (fun t' =>
            fdBoundaryToPolygonHomotopy (t', q.2)) =ᶠ[𝓝 q.1]
          (fun t' : ℝ => (1/2 : ℂ) +
              (H_height - (↑t' : ℂ) * (H_height -
                  Real.sqrt 3 / 2)) * I) := by
        filter_upwards [
          eventually_lt_nhds ht_lt1] with t' ht'
        simp only [fdBoundaryToPolygonHomotopy,
          le_of_lt ht', ite_true]
      rw [heq.deriv_eq]
      have h1 :
          HasDerivAt (fun t' : ℝ => (↑t' : ℂ))
            1 q.1 :=
        Complex.ofRealCLM.hasDerivAt
      have h2 :
          HasDerivAt (fun t' : ℝ => (↑t' : ℂ) *
              ((H_height : ℂ) -
                Real.sqrt 3 / 2))
            ((H_height : ℂ) -
              Real.sqrt 3 / 2) q.1 := by
        have := h1.mul_const ((H_height : ℂ) - Real.sqrt 3 / 2)
        simp only [one_mul] at this; exact this
      have h3 :
          HasDerivAt (fun t' : ℝ =>
              (H_height : ℂ) - (↑t' : ℂ) * ((H_height : ℂ) -
                  Real.sqrt 3 / 2))
            (-((H_height : ℂ) -
              Real.sqrt 3 / 2)) q.1 := by
        have := (hasDerivAt_const q.1
            (H_height : ℂ)).sub h2
        simp only [zero_sub] at this
        exact this
      have h4 :
          HasDerivAt (fun t' : ℝ =>
              ((H_height : ℂ) - (↑t' : ℂ) * ((H_height : ℂ) -
                  Real.sqrt 3 / 2)) * I)
            (-((H_height : ℂ) -
              Real.sqrt 3 / 2) * I)
            q.1 :=
        h3.mul_const I
      have h5 := (hasDerivAt_const q.1
          ((1/2 : ℂ))).add h4
      simp only [zero_add] at h5
      convert h5.deriv using 2
    apply ContinuousOn.congr
      continuousOn_const hconst
  · apply continuousOn_of_forall_continuousAt
    intro q ⟨hq1, hq2⟩
    have ht_gt1 : q.1 > 1 :=
      lt_of_le_of_lt h_seg2_lo hq1.1
    have ht_lt2 : q.1 < 2 :=
      lt_of_lt_of_le hq1.2 h_seg2_hi
    have hderiv_eq :
        deriv (fun t' =>
          fdBoundaryToPolygonHomotopy (t', q.2)) q.1 =
        (1 - q.2) • ((Real.pi / 6) * I *
            Complex.exp ((Real.pi / 3 +
                (q.1 - 1) * (Real.pi / 6)) * I)) +
        q.2 • (i_point - rho') := by
      have heq : (fun t' =>
            fdBoundaryToPolygonHomotopy (t', q.2)) =ᶠ[𝓝 q.1]
          (fun t' : ℝ =>
            let arc_point :=
              Complex.exp ((Real.pi / 3 +
                  (t' - 1) * (Real.pi / 6)) * I)
            let chord_point :=
              chordSegment rho' i_point (t' - 1)
            (1 - q.2) • arc_point +
              q.2 • chord_point) := by
        filter_upwards [
          eventually_gt_nhds ht_gt1,
          eventually_lt_nhds ht_lt2]
          with t' ht1' ht2'
        simp only [fdBoundaryToPolygonHomotopy]
        simp only [not_le.mpr ht1',
          le_of_lt ht2', ite_false, ite_true]
        congr 2; ring_nf
      rw [heq.deriv_eq]
      have h_ofReal :
          HasDerivAt (fun t' : ℝ => (t' : ℂ)) 1 q.1 :=
        Complex.ofRealCLM.hasDerivAt
      have h_inner :
          HasDerivAt (fun t' : ℝ =>
              (Real.pi : ℂ) / 3 + ((t' : ℂ) - 1) *
                  ((Real.pi : ℂ) / 6))
            ((Real.pi : ℂ) / 6) q.1 := by
        have h_shift :
            HasDerivAt (fun t' : ℝ => (t' : ℂ) - 1)
              1 q.1 :=
          h_ofReal.sub_const 1
        have h_mul :
            HasDerivAt (fun t' : ℝ =>
                ((t' : ℂ) - 1) * ((Real.pi : ℂ) / 6))
              ((Real.pi : ℂ) / 6) q.1 := by
          have := h_shift.mul_const ((Real.pi : ℂ) / 6)
          simp only [one_mul] at this
          exact this
        have := h_mul.const_add ((Real.pi : ℂ) / 3)
        simp only at this; exact this
      have h_times_I :
          HasDerivAt (fun t' : ℝ =>
              ((Real.pi : ℂ) / 3 + ((t' : ℂ) - 1) *
                  ((Real.pi : ℂ) / 6)) * I)
            (((Real.pi : ℂ) / 6) * I) q.1 :=
        h_inner.mul_const I
      have h_arc :
          HasDerivAt (fun t' : ℝ =>
              Complex.exp ((Real.pi / 3 +
                  (t' - 1) * (Real.pi / 6)) * I))
            ((Real.pi / 6) * I *
              Complex.exp ((Real.pi / 3 +
                  (q.1 - 1) * (Real.pi / 6)) * I))
            q.1 := by
        have h_exp :=
          Complex.hasDerivAt_exp (((Real.pi : ℂ) / 3 +
              ((q.1 : ℂ) - 1) * ((Real.pi : ℂ) / 6)) * I)
        have h_comp :=
          h_exp.comp q.1 h_times_I
        simp only [mul_comm (Complex.exp _)]
          at h_comp
        exact h_comp
      have h_chord :
          HasDerivAt (fun t' : ℝ =>
              chordSegment rho' i_point (t' - 1))
            (i_point - rho') q.1 := by
        simp only [chordSegment]
        have h_shift :
            HasDerivAt (fun t' : ℝ => t' - 1)
              (1 : ℝ) q.1 :=
          (hasDerivAt_id q.1).sub_const 1
        have h1 :
            HasDerivAt (fun t' : ℝ =>
                (1 - (t' - 1)) • rho')
              (-rho') q.1 := by
          have h_coef :
              HasDerivAt (fun t' : ℝ =>
                  (1 - (t' - 1) : ℝ))
                (-1 : ℝ) q.1 := by
            have := (hasDerivAt_const q.1
                (1 : ℝ)).sub h_shift
            simp only [zero_sub]
              at this
            convert this using 1
          have := h_coef.smul_const rho'
          simp only [neg_one_smul] at this
          exact this
        have h2 :
            HasDerivAt (fun t' : ℝ =>
                (t' - 1) • i_point)
              i_point q.1 := by
          have := h_shift.smul_const i_point
          simp only [one_smul] at this
          exact this
        convert h1.add h2 using 1; ring
      have h_combined :
          HasDerivAt (fun t' : ℝ =>
            let arc_point :=
              Complex.exp ((Real.pi / 3 +
                  (t' - 1) * (Real.pi / 6)) * I)
            let chord_point :=
              chordSegment rho' i_point (t' - 1)
            (1 - q.2) • arc_point +
              q.2 • chord_point)
          ((1 - q.2) • ((Real.pi / 6) * I *
              Complex.exp ((Real.pi / 3 +
                  (q.1 - 1) * (Real.pi / 6)) * I)) +
           q.2 • (i_point - rho')) q.1 := by
        have h1 :=
          h_arc.const_smul (1 - q.2)
        have h2 :=
          h_chord.const_smul q.2
        exact h1.add h2
      exact h_combined.deriv
    have h_formula_cont :
        ContinuousAt (fun r : ℝ × ℝ => (1 - r.2) •
            ((Real.pi / 6) * I *
              Complex.exp ((Real.pi / 3 +
                  (r.1 - 1) * (Real.pi / 6)) * I)) +
          r.2 • (i_point - rho')) q := by
      apply ContinuousAt.add
      · apply ContinuousAt.smul
        · exact (continuous_const.sub
            continuous_snd).continuousAt
        · apply ContinuousAt.mul
          apply ContinuousAt.mul
          · exact continuousAt_const
          · exact continuousAt_const
          · apply Complex.continuous_exp.continuousAt.comp
            apply ContinuousAt.mul
            · apply ContinuousAt.add
              · exact continuousAt_const
              · apply ContinuousAt.mul
                · have h1 : Continuous (fun r : ℝ × ℝ =>
                        (r.1 : ℂ)) :=
                    Complex.continuous_ofReal.comp
                      continuous_fst
                  have h2 : Continuous (fun _ : ℝ × ℝ =>
                        (1 : ℂ)) :=
                    continuous_const
                  exact (h1.sub h2).continuousAt
                · exact continuousAt_const
            · exact continuousAt_const
      · apply ContinuousAt.smul
        · exact continuous_snd.continuousAt
        · exact continuousAt_const
    apply h_formula_cont.congr
    rw [nhds_prod_eq]
    have h_mem1 : Ioo p₁ p₂ ∈ 𝓝 q.1 :=
      Ioo_mem_nhds hq1.1 hq1.2
    filter_upwards [
      prod_mem_prod h_mem1 univ_mem]
      with r hr
    have hr1 : r.1 ∈ Ioo p₁ p₂ := hr.1
    have ht_gt1' : r.1 > 1 :=
      lt_of_le_of_lt h_seg2_lo hr1.1
    have ht_lt2' : r.1 < 2 :=
      lt_of_lt_of_le hr1.2 h_seg2_hi
    have heq : (fun t' =>
          fdBoundaryToPolygonHomotopy (t', r.2)) =ᶠ[𝓝 r.1]
        (fun t' : ℝ =>
          let arc_point :=
            Complex.exp ((Real.pi / 3 +
                (t' - 1) * (Real.pi / 6)) * I)
          let chord_point :=
            chordSegment rho' i_point (t' - 1)
          (1 - r.2) • arc_point +
            r.2 • chord_point) := by
      filter_upwards [
        eventually_gt_nhds ht_gt1',
        eventually_lt_nhds ht_lt2']
        with t' ht1'' ht2''
      simp only [fdBoundaryToPolygonHomotopy]
      simp only [not_le.mpr ht1'',
        le_of_lt ht2'', ite_false, ite_true]
      congr 2; ring_nf
    rw [heq.deriv_eq]
    have h_ofReal :
        HasDerivAt (fun t' : ℝ => (t' : ℂ)) 1 r.1 :=
      Complex.ofRealCLM.hasDerivAt
    have h_inner :
        HasDerivAt (fun t' : ℝ =>
            (Real.pi : ℂ) / 3 + ((t' : ℂ) - 1) *
                ((Real.pi : ℂ) / 6))
          ((Real.pi : ℂ) / 6) r.1 := by
      have h_shift :
          HasDerivAt (fun t' : ℝ => (t' : ℂ) - 1)
            1 r.1 :=
        h_ofReal.sub_const 1
      have h_mul :
          HasDerivAt (fun t' : ℝ =>
              ((t' : ℂ) - 1) * ((Real.pi : ℂ) / 6))
            ((Real.pi : ℂ) / 6) r.1 := by
        have := h_shift.mul_const ((Real.pi : ℂ) / 6)
        simp only [one_mul] at this
        exact this
      have := h_mul.const_add ((Real.pi : ℂ) / 3)
      simp only at this; exact this
    have h_times_I :
        HasDerivAt (fun t' : ℝ =>
            ((Real.pi : ℂ) / 3 + ((t' : ℂ) - 1) *
                ((Real.pi : ℂ) / 6)) * I)
          (((Real.pi : ℂ) / 6) * I) r.1 :=
      h_inner.mul_const I
    have h_arc :
        HasDerivAt (fun t' : ℝ =>
            Complex.exp ((Real.pi / 3 +
                (t' - 1) * (Real.pi / 6)) * I))
          ((Real.pi / 6) * I *
            Complex.exp ((Real.pi / 3 +
                (r.1 - 1) * (Real.pi / 6)) * I))
          r.1 := by
      have h_exp :=
        Complex.hasDerivAt_exp (((Real.pi : ℂ) / 3 +
            ((r.1 : ℂ) - 1) * ((Real.pi : ℂ) / 6)) * I)
      have h_comp :=
        h_exp.comp r.1 h_times_I
      simp only [mul_comm (Complex.exp _)]
        at h_comp
      exact h_comp
    have h_chord :
        HasDerivAt (fun t' : ℝ =>
            chordSegment rho' i_point (t' - 1))
          (i_point - rho') r.1 := by
      simp only [chordSegment]
      have h_shift :
          HasDerivAt (fun t' : ℝ => t' - 1)
            (1 : ℝ) r.1 :=
        (hasDerivAt_id r.1).sub_const 1
      have h1 :
          HasDerivAt (fun t' : ℝ =>
              (1 - (t' - 1)) • rho')
            (-rho') r.1 := by
        have h_coef :
            HasDerivAt (fun t' : ℝ =>
                (1 - (t' - 1) : ℝ))
              (-1 : ℝ) r.1 := by
          have := (hasDerivAt_const r.1
              (1 : ℝ)).sub h_shift
          simp only [zero_sub]
            at this
          convert this using 1
        have := h_coef.smul_const rho'
        simp only [neg_one_smul] at this
        exact this
      have h2 :
          HasDerivAt (fun t' : ℝ =>
              (t' - 1) • i_point)
            i_point r.1 := by
        have := h_shift.smul_const i_point
        simp only [one_smul] at this
        exact this
      convert h1.add h2 using 1; ring
    have h_combined :
        HasDerivAt (fun t' : ℝ =>
          let arc_point :=
            Complex.exp ((Real.pi / 3 +
                (t' - 1) * (Real.pi / 6)) * I)
          let chord_point :=
            chordSegment rho' i_point (t' - 1)
          (1 - r.2) • arc_point +
            r.2 • chord_point)
        ((1 - r.2) • ((Real.pi / 6) * I *
            Complex.exp ((Real.pi / 3 +
                (r.1 - 1) * (Real.pi / 6)) * I)) +
         r.2 • (i_point - rho')) r.1 := by
      have h1 :=
        h_arc.const_smul (1 - r.2)
      have h2 :=
        h_chord.const_smul r.2
      exact h1.add h2
    exact h_combined.deriv.symm
  · apply continuousOn_of_forall_continuousAt
    intro q ⟨hq1, hq2⟩
    have ht_gt2 : q.1 > 2 :=
      lt_of_le_of_lt h_seg3_lo hq1.1
    have ht_lt3 : q.1 < 3 :=
      lt_of_lt_of_le hq1.2 h_seg3_hi
    have h_formula_cont :
        ContinuousAt (fun r : ℝ × ℝ => (1 - r.2) •
            ((Real.pi / 6) * I *
              Complex.exp ((Real.pi / 2 +
                  (r.1 - 2) * (Real.pi / 6)) * I)) +
          r.2 • (rho - i_point)) q := by
      apply ContinuousAt.add
      · apply ContinuousAt.smul
        · exact (continuous_const.sub
            continuous_snd).continuousAt
        · apply ContinuousAt.mul
          apply ContinuousAt.mul
          · exact continuousAt_const
          · exact continuousAt_const
          · apply Complex.continuous_exp.continuousAt.comp
            apply ContinuousAt.mul
            · apply ContinuousAt.add
              · exact continuousAt_const
              · apply ContinuousAt.mul
                · have h1 : Continuous (fun r : ℝ × ℝ =>
                        (r.1 : ℂ)) :=
                    Complex.continuous_ofReal.comp
                      continuous_fst
                  have h2 : Continuous (fun _ : ℝ × ℝ =>
                        (2 : ℂ)) :=
                    continuous_const
                  exact (h1.sub h2).continuousAt
                · exact continuousAt_const
            · exact continuousAt_const
      · apply ContinuousAt.smul
        · exact continuous_snd.continuousAt
        · exact continuousAt_const
    apply h_formula_cont.congr
    rw [nhds_prod_eq]
    have h_mem1 : Ioo p₁ p₂ ∈ 𝓝 q.1 :=
      Ioo_mem_nhds hq1.1 hq1.2
    filter_upwards [
      prod_mem_prod h_mem1 univ_mem] with r hr
    have hr1 : r.1 ∈ Ioo p₁ p₂ := hr.1
    have ht_gt2' : r.1 > 2 :=
      lt_of_le_of_lt h_seg3_lo hr1.1
    have ht_lt3' : r.1 < 3 :=
      lt_of_lt_of_le hr1.2 h_seg3_hi
    have heq : (fun t' =>
          fdBoundaryToPolygonHomotopy (t', r.2)) =ᶠ[𝓝 r.1]
        (fun t' : ℝ =>
          let arc_point :=
            Complex.exp ((Real.pi / 2 +
                (t' - 2) * (Real.pi / 6)) * I)
          let chord_point :=
            chordSegment i_point rho (t' - 2)
          (1 - r.2) • arc_point +
            r.2 • chord_point) := by
      filter_upwards [
        eventually_gt_nhds ht_gt2',
        eventually_lt_nhds ht_lt3']
        with t' ht2'' ht3''
      simp only [fdBoundaryToPolygonHomotopy]
      simp only [
        not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 2) ht2''),
        not_le.mpr ht2'',
        le_of_lt ht3'', ite_false, ite_true]
      congr 2; ring_nf
    rw [heq.deriv_eq]
    have h_ofReal :
        HasDerivAt (fun t' : ℝ => (t' : ℂ)) 1 r.1 :=
      Complex.ofRealCLM.hasDerivAt
    have h_inner :
        HasDerivAt (fun t' : ℝ =>
            (Real.pi : ℂ) / 2 + ((t' : ℂ) - 2) *
                ((Real.pi : ℂ) / 6))
          ((Real.pi : ℂ) / 6) r.1 := by
      have h_shift :
          HasDerivAt (fun t' : ℝ => (t' : ℂ) - 2)
            1 r.1 :=
        h_ofReal.sub_const 2
      have h_mul :
          HasDerivAt (fun t' : ℝ =>
              ((t' : ℂ) - 2) * ((Real.pi : ℂ) / 6))
            ((Real.pi : ℂ) / 6) r.1 := by
        have := h_shift.mul_const ((Real.pi : ℂ) / 6)
        simp only [one_mul] at this
        exact this
      have := h_mul.const_add ((Real.pi : ℂ) / 2)
      simp only at this; exact this
    have h_times_I :
        HasDerivAt (fun t' : ℝ =>
            ((Real.pi : ℂ) / 2 + ((t' : ℂ) - 2) *
                ((Real.pi : ℂ) / 6)) * I)
          (((Real.pi : ℂ) / 6) * I) r.1 :=
      h_inner.mul_const I
    have h_arc :
        HasDerivAt (fun t' : ℝ =>
            Complex.exp ((Real.pi / 2 +
                (t' - 2) * (Real.pi / 6)) * I))
          ((Real.pi / 6) * I *
            Complex.exp ((Real.pi / 2 +
                (r.1 - 2) * (Real.pi / 6)) * I))
          r.1 := by
      have h_exp :=
        Complex.hasDerivAt_exp (((Real.pi : ℂ) / 2 +
            ((r.1 : ℂ) - 2) * ((Real.pi : ℂ) / 6)) * I)
      have h_comp :=
        h_exp.comp r.1 h_times_I
      simp only [mul_comm (Complex.exp _)]
        at h_comp
      exact h_comp
    have h_chord :
        HasDerivAt (fun t' : ℝ =>
            chordSegment i_point rho (t' - 2))
          (rho - i_point) r.1 := by
      simp only [chordSegment]
      have h_shift :
          HasDerivAt (fun t' : ℝ => t' - 2)
            (1 : ℝ) r.1 :=
        (hasDerivAt_id r.1).sub_const 2
      have h1 :
          HasDerivAt (fun t' : ℝ =>
              (1 - (t' - 2)) • i_point)
            (-i_point) r.1 := by
        have h_coef :
            HasDerivAt (fun t' : ℝ =>
                (1 - (t' - 2) : ℝ))
              (-1 : ℝ) r.1 := by
          have := (hasDerivAt_const r.1
              (1 : ℝ)).sub h_shift
          simp only [zero_sub]
            at this
          convert this using 1
        have := h_coef.smul_const i_point
        simp only [neg_one_smul] at this
        exact this
      have h2 :
          HasDerivAt (fun t' : ℝ =>
              (t' - 2) • rho)
            rho r.1 := by
        have := h_shift.smul_const rho
        simp only [one_smul] at this
        exact this
      convert h1.add h2 using 1; ring
    have h_combined :
        HasDerivAt (fun t' : ℝ =>
          let arc_point :=
            Complex.exp ((Real.pi / 2 +
                (t' - 2) * (Real.pi / 6)) * I)
          let chord_point :=
            chordSegment i_point rho (t' - 2)
          (1 - r.2) • arc_point +
            r.2 • chord_point)
        ((1 - r.2) • ((Real.pi / 6) * I *
            Complex.exp ((Real.pi / 2 +
                (r.1 - 2) * (Real.pi / 6)) * I)) +
         r.2 • (rho - i_point)) r.1 := by
      have h1 :=
        h_arc.const_smul (1 - r.2)
      have h2 :=
        h_chord.const_smul r.2
      exact h1.add h2
    exact h_combined.deriv.symm
  · have hconst :
        ∀ q ∈ Ioo p₁ p₂ ×ˢ Icc (0:ℝ) 1,
          deriv (fun t' =>
            fdBoundaryToPolygonHomotopy (t', q.2)) q.1 =
          (((H_height : ℂ) -
            Real.sqrt 3 / 2) * I) := by
      intro q ⟨hq1, _hq2⟩
      have ht_gt3 : q.1 > 3 :=
        lt_of_le_of_lt h_seg4_lo hq1.1
      have ht_lt4 : q.1 < 4 :=
        lt_of_lt_of_le hq1.2 h_seg4_hi
      have heq : (fun t' =>
            fdBoundaryToPolygonHomotopy (t', q.2)) =ᶠ[𝓝 q.1]
          (fun t' : ℝ => (-1/2 : ℂ) +
              ((Real.sqrt 3 / 2 : ℂ) + ((↑t' : ℂ) - 3) *
                  ((H_height : ℂ) -
                    Real.sqrt 3 / 2)) *
                I) := by
        filter_upwards [
          eventually_gt_nhds ht_gt3,
          eventually_lt_nhds ht_lt4]
          with t' ht3' ht4'
        simp only [fdBoundaryToPolygonHomotopy]
        have h1' : ¬(t' ≤ 1) :=
          not_le.mpr (by linarith : 1 < t')
        have h2' : ¬(t' ≤ 2) :=
          not_le.mpr (by linarith : 2 < t')
        have h3' : ¬(t' ≤ 3) :=
          not_le.mpr ht3'
        have h4' : t' ≤ 4 :=
          le_of_lt ht4'
        simp only [h1', h2', h3', h4',
          ite_false, ite_true]
      rw [heq.deriv_eq]
      have h1 :
          HasDerivAt (fun t' : ℝ => (↑t' : ℂ))
            1 q.1 :=
        Complex.ofRealCLM.hasDerivAt
      have h2 :
          HasDerivAt (fun t' : ℝ => (↑t' : ℂ) - 3)
            1 q.1 :=
        h1.sub_const 3
      have h3 :
          HasDerivAt (fun t' : ℝ =>
              ((↑t' : ℂ) - 3) * ((H_height : ℂ) -
                  Real.sqrt 3 / 2))
            ((H_height : ℂ) -
              Real.sqrt 3 / 2) q.1 := by
        have := h2.mul_const ((H_height : ℂ) - Real.sqrt 3 / 2)
        simp only [one_mul] at this
        exact this
      have h4 :
          HasDerivAt (fun t' : ℝ =>
              (Real.sqrt 3 / 2 : ℂ) + ((↑t' : ℂ) - 3) *
                  ((H_height : ℂ) -
                    Real.sqrt 3 / 2))
            ((H_height : ℂ) -
              Real.sqrt 3 / 2) q.1 := by
        have := (hasDerivAt_const q.1
            (Real.sqrt 3 / 2 : ℂ)).add h3
        simp only [zero_add] at this
        exact this
      have h5 :
          HasDerivAt (fun t' : ℝ =>
              ((Real.sqrt 3 / 2 : ℂ) + ((↑t' : ℂ) - 3) *
                  ((H_height : ℂ) -
                    Real.sqrt 3 / 2)) * I)
            (((H_height : ℂ) -
              Real.sqrt 3 / 2) * I)
            q.1 :=
        h4.mul_const I
      have h6 := (hasDerivAt_const q.1
          ((-1/2 : ℂ))).add h5
      simp only [zero_add] at h6
      exact h6.deriv
    apply ContinuousOn.congr
      continuousOn_const hconst
  · have hconst :
        ∀ q ∈ Ioo p₁ p₂ ×ˢ Icc (0:ℝ) 1,
          deriv (fun t' =>
            fdBoundaryToPolygonHomotopy (t', q.2)) q.1 =
          (1 : ℂ) := by
      intro q ⟨hq1, _hq2⟩
      have ht_gt4 : q.1 > 4 :=
        lt_of_le_of_lt h_seg5 hq1.1
      have heq : (fun t' =>
            fdBoundaryToPolygonHomotopy (t', q.2)) =ᶠ[𝓝 q.1]
          (fun t' : ℝ => ((↑t' : ℂ) - 9/2) +
              (H_height : ℂ) * I) := by
        filter_upwards [
          eventually_gt_nhds ht_gt4]
          with t' ht4'
        simp only [fdBoundaryToPolygonHomotopy]
        have h1' : ¬(t' ≤ 1) :=
          not_le.mpr (by linarith : 1 < t')
        have h2' : ¬(t' ≤ 2) :=
          not_le.mpr (by linarith : 2 < t')
        have h3' : ¬(t' ≤ 3) :=
          not_le.mpr (by linarith : 3 < t')
        have h4' : ¬(t' ≤ 4) :=
          not_le.mpr ht4'
        simp only [h1', h2', h3', h4',
          ite_false]
      rw [heq.deriv_eq]
      have h1 :
          HasDerivAt (fun t' : ℝ => (↑t' : ℂ))
            1 q.1 :=
        Complex.ofRealCLM.hasDerivAt
      have h2 :
          HasDerivAt (fun t' : ℝ => (↑t' : ℂ) - 9/2)
            1 q.1 :=
        h1.sub_const (9/2)
      have h3 :=
        h2.add_const ((H_height : ℂ) * I)
      convert h3.deriv using 1
    apply ContinuousOn.congr
      continuousOn_const hconst

end RectHomotopyProof
