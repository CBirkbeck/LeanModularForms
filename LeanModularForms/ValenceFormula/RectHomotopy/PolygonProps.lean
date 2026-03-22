/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ValenceFormula.RectHomotopy.HomotopyDef

/-!
# Polygon properties: values, segment functions, derivatives, differentiability

Defines per-segment functions `fdPolygon_seg1`..`fdPolygon_seg5` and proves:

* Values at key points (`fdPolygon_at_t1` .. `fdPolygon_at_t4`)
* Segment continuity and matching at breakpoints
* `fdPolygon_continuous` and `fdPolygon_closed`
* Derivative computation helpers and segment derivatives
* Segment differentiability and `fdPolygon_differentiableAt_off_partition`
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

lemma fdPolygon_at_t1 : fdPolygon 1 = rho' := by
  simp only [fdPolygon,
    show (1:ℝ) ≤ 1 from le_refl 1, ↓reduceIte]
  simp only [H_height, rho']; push_cast; ring

lemma fdPolygon_at_t2 : fdPolygon 2 = i_point := by
  simp only [fdPolygon,
    show ¬(2:ℝ) ≤ 1 from by norm_num,
    show (2:ℝ) ≤ 2 from le_refl 2, ↓reduceIte]
  simp only [chordSegment, i_point]
  simp only [show (2:ℝ) - 1 = 1 by ring]
  simp only [sub_self, zero_smul, zero_add, one_smul]

lemma fdPolygon_at_t3 : fdPolygon 3 = rho := by
  simp only [fdPolygon,
    show ¬(3:ℝ) ≤ 1 from by norm_num,
    show ¬(3:ℝ) ≤ 2 from by norm_num,
    show (3:ℝ) ≤ 3 from le_refl 3, ↓reduceIte]
  simp only [chordSegment, rho]
  simp only [show (3:ℝ) - 2 = 1 by ring]
  simp only [sub_self, zero_smul, zero_add, one_smul]

lemma fdPolygon_at_t4 :
    fdPolygon 4 = -1/2 + H_height * I := by
  simp only [fdPolygon,
    show ¬(4:ℝ) ≤ 1 from by norm_num,
    show ¬(4:ℝ) ≤ 2 from by norm_num,
    show ¬(4:ℝ) ≤ 3 from by norm_num,
    show (4:ℝ) ≤ 4 from le_refl 4, ↓reduceIte]
  simp only [H_height]; push_cast; ring

noncomputable def fdPolygon_seg1 : ℝ → ℂ := fun t =>
  1/2 + (H_height - t * (H_height - Real.sqrt 3 / 2)) * I

noncomputable def fdPolygon_seg2 : ℝ → ℂ := fun t =>
  chordSegment rho' i_point (t - 1)

noncomputable def fdPolygon_seg3 : ℝ → ℂ := fun t =>
  chordSegment i_point rho (t - 2)

noncomputable def fdPolygon_seg4 : ℝ → ℂ := fun t =>
  -1/2 + (Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2)) * I

noncomputable def fdPolygon_seg5 : ℝ → ℂ := fun t => (t - 9/2) + H_height * I

lemma fdPolygon_seg1_continuous :
    Continuous fdPolygon_seg1 := by
  unfold fdPolygon_seg1; continuity

lemma fdPolygon_seg2_continuous :
    Continuous fdPolygon_seg2 := by
  unfold fdPolygon_seg2 chordSegment; continuity

lemma fdPolygon_seg3_continuous :
    Continuous fdPolygon_seg3 := by
  unfold fdPolygon_seg3 chordSegment; continuity

lemma fdPolygon_seg4_continuous :
    Continuous fdPolygon_seg4 := by
  unfold fdPolygon_seg4; continuity

lemma fdPolygon_seg5_continuous :
    Continuous fdPolygon_seg5 := by
  unfold fdPolygon_seg5; continuity

lemma fdPolygon_match_t1 :
    fdPolygon_seg1 1 = fdPolygon_seg2 1 := by
  simp only [fdPolygon_seg1, fdPolygon_seg2,
    chordSegment, H_height, rho']
  simp only [sub_self, zero_smul, sub_zero, one_smul]
  push_cast; ring

lemma fdPolygon_match_t2 :
    fdPolygon_seg2 2 = fdPolygon_seg3 2 := by
  simp only [fdPolygon_seg2, fdPolygon_seg3,
    chordSegment, i_point]
  simp only [show (2:ℝ) - 1 = 1 by ring,
    show (2:ℝ) - 2 = 0 by ring]
  simp only [sub_self, zero_smul, zero_add,
    one_smul, sub_zero, add_zero]

lemma fdPolygon_match_t3 :
    fdPolygon_seg3 3 = fdPolygon_seg4 3 := by
  simp only [fdPolygon_seg3, fdPolygon_seg4,
    chordSegment, rho, H_height]
  simp only [show (3:ℝ) - 2 = 1 by ring]
  simp only [sub_self, zero_smul, zero_add, one_smul]
  push_cast; ring

lemma fdPolygon_match_t4 :
    fdPolygon_seg4 4 = fdPolygon_seg5 4 := by
  simp only [fdPolygon_seg4, fdPolygon_seg5, H_height]
  push_cast; ring

lemma fdPolygon_continuous : Continuous fdPolygon := by
  have hf1 : frontier {x : ℝ | x ≤ 1} = {1} :=
    frontier_Iic
  have hf2 : frontier {x : ℝ | x ≤ 2} = {2} :=
    frontier_Iic
  have hf3 : frontier {x : ℝ | x ≤ 3} = {3} :=
    frontier_Iic
  have hf4 : frontier {x : ℝ | x ≤ 4} = {4} :=
    frontier_Iic
  have h12 : Continuous (fun t =>
      if t ≤ 1 then fdPolygon_seg1 t
      else fdPolygon_seg2 t) := by
    apply Continuous.if
    · intro t ht; rw [hf1] at ht
      simp only [mem_singleton_iff] at ht; rw [ht]
      exact fdPolygon_match_t1
    · exact fdPolygon_seg1_continuous
    · exact fdPolygon_seg2_continuous
  have h123 : Continuous (fun t =>
      if t ≤ 1 then fdPolygon_seg1 t
      else if t ≤ 2 then fdPolygon_seg2 t
      else fdPolygon_seg3 t) := by
    apply Continuous.if
    · intro t ht; rw [hf1] at ht
      simp only [mem_singleton_iff] at ht; rw [ht]
      simp only [show (1:ℝ) ≤ 2 from by norm_num,
        ↓reduceIte]
      exact fdPolygon_match_t1
    · exact fdPolygon_seg1_continuous
    · apply Continuous.if
      · intro t ht; rw [hf2] at ht
        simp only [mem_singleton_iff] at ht; rw [ht]
        exact fdPolygon_match_t2
      · exact fdPolygon_seg2_continuous
      · exact fdPolygon_seg3_continuous
  have h1234 : Continuous (fun t =>
      if t ≤ 1 then fdPolygon_seg1 t
      else if t ≤ 2 then fdPolygon_seg2 t
      else if t ≤ 3 then fdPolygon_seg3 t
      else fdPolygon_seg4 t) := by
    apply Continuous.if
    · intro t ht; rw [hf1] at ht
      simp only [mem_singleton_iff] at ht; rw [ht]
      simp only [show (1:ℝ) ≤ 2 from by norm_num,
        ↓reduceIte]
      exact fdPolygon_match_t1
    · exact fdPolygon_seg1_continuous
    · apply Continuous.if
      · intro t ht; rw [hf2] at ht
        simp only [mem_singleton_iff] at ht; rw [ht]
        simp only [show (2:ℝ) ≤ 3 from by norm_num,
          ↓reduceIte]
        exact fdPolygon_match_t2
      · exact fdPolygon_seg2_continuous
      · apply Continuous.if
        · intro t ht; rw [hf3] at ht
          simp only [mem_singleton_iff] at ht; rw [ht]
          exact fdPolygon_match_t3
        · exact fdPolygon_seg3_continuous
        · exact fdPolygon_seg4_continuous
  have h_full : Continuous (fun t =>
      if t ≤ 1 then fdPolygon_seg1 t
      else if t ≤ 2 then fdPolygon_seg2 t
      else if t ≤ 3 then fdPolygon_seg3 t
      else if t ≤ 4 then fdPolygon_seg4 t
      else fdPolygon_seg5 t) := by
    apply Continuous.if
    · intro t ht; rw [hf1] at ht
      simp only [mem_singleton_iff] at ht; rw [ht]
      simp only [show (1:ℝ) ≤ 2 from by norm_num,
        ↓reduceIte]
      exact fdPolygon_match_t1
    · exact fdPolygon_seg1_continuous
    · apply Continuous.if
      · intro t ht; rw [hf2] at ht
        simp only [mem_singleton_iff] at ht; rw [ht]
        simp only [show (2:ℝ) ≤ 3 from by norm_num,
          ↓reduceIte]
        exact fdPolygon_match_t2
      · exact fdPolygon_seg2_continuous
      · apply Continuous.if
        · intro t ht; rw [hf3] at ht
          simp only [mem_singleton_iff] at ht; rw [ht]
          simp only [show (3:ℝ) ≤ 4 from by norm_num,
            ↓reduceIte]
          exact fdPolygon_match_t3
        · exact fdPolygon_seg3_continuous
        · apply Continuous.if
          · intro t ht; rw [hf4] at ht
            simp only [mem_singleton_iff] at ht; rw [ht]
            exact fdPolygon_match_t4
          · exact fdPolygon_seg4_continuous
          · exact fdPolygon_seg5_continuous
  convert h_full using 1

lemma fdPolygon_closed : fdPolygon 0 = fdPolygon 5 := by
  simp only [fdPolygon]
  simp only [show ¬(5:ℝ) ≤ 1 from by norm_num,
    show ¬(5:ℝ) ≤ 2 from by norm_num,
    show ¬(5:ℝ) ≤ 3 from by norm_num,
    show ¬(5:ℝ) ≤ 4 from by norm_num,
    show (0:ℝ) ≤ 1 from by norm_num, ↓reduceIte]
  simp only [H_height]; push_cast; ring

lemma Complex.deriv_ofReal' :
    deriv (fun t : ℝ => (↑t : ℂ)) = fun _ => 1 := by
  ext t
  exact (Complex.ofRealCLM.hasDerivAt (x := t)).deriv

lemma deriv_affine_mul (a b : ℂ) :
    deriv (fun t : ℝ => a + ↑t * b) = fun _ => b := by
  ext t
  have h_id : HasDerivAt (fun t : ℝ => (↑t : ℂ)) 1 t :=
    Complex.ofRealCLM.hasDerivAt
  have h_mul : HasDerivAt (fun t : ℝ => (↑t : ℂ) * b) (1 * b) t := h_id.mul_const b
  have h_add : HasDerivAt (fun t : ℝ => a + ↑t * b) (0 + 1 * b) t :=
    (hasDerivAt_const t a).add h_mul
  simp only [zero_add, one_mul] at h_add
  exact h_add.deriv

lemma deriv_affine_shifted_mul (a b : ℂ) (c : ℝ) :
    deriv (fun t : ℝ => a + (↑t - ↑c) * b) =
      fun _ => b := by
  ext t
  have h_id : HasDerivAt (fun t : ℝ => (↑t : ℂ)) 1 t :=
    Complex.ofRealCLM.hasDerivAt
  have h_sub : HasDerivAt (fun t : ℝ => (↑t : ℂ) - ↑c) (1 - 0) t :=
    h_id.sub (hasDerivAt_const t (↑c : ℂ))
  simp only [sub_zero] at h_sub
  have h_mul : HasDerivAt (fun t : ℝ => ((↑t : ℂ) - ↑c) * b)
      (1 * b) t := h_sub.mul_const b
  have h_add : HasDerivAt (fun t : ℝ => a + (↑t - ↑c) * b) (0 + 1 * b) t :=
    (hasDerivAt_const t a).add h_mul
  simp only [zero_add, one_mul] at h_add
  exact h_add.deriv

lemma fdPolygon_deriv_seg1 :
    deriv fdPolygon_seg1 =
      fun _ => -(H_height - Real.sqrt 3 / 2) * I := by
  have hrw : fdPolygon_seg1 = fun (t : ℝ) => ((1:ℂ)/2 + H_height * I) + ↑t *
        (-(H_height - Real.sqrt 3 / 2) * I) := by
    ext t; simp only [fdPolygon_seg1]; ring
  rw [hrw, deriv_affine_mul]

lemma fdPolygon_deriv_seg2 :
    deriv fdPolygon_seg2 = fun _ => i_point - rho' := by
  have hrw : fdPolygon_seg2 = fun (t : ℝ) =>
      rho' + (↑t - ↑(1:ℝ)) * (i_point - rho') := by
    ext t
    simp only [fdPolygon_seg2, chordSegment, rho',
      i_point, Complex.real_smul, Complex.ofReal_sub,
      Complex.ofReal_one]
    ring
  rw [hrw, deriv_affine_shifted_mul]

lemma fdPolygon_deriv_seg3 :
    deriv fdPolygon_seg3 = fun _ => rho - i_point := by
  have hrw : fdPolygon_seg3 = fun (t : ℝ) =>
      i_point + (↑t - ↑(2:ℝ)) * (rho - i_point) := by
    ext t
    simp only [fdPolygon_seg3, chordSegment, rho,
      i_point, Complex.real_smul, Complex.ofReal_sub,
      Complex.ofReal_ofNat]
    push_cast; ring
  rw [hrw, deriv_affine_shifted_mul]

lemma fdPolygon_deriv_seg4 :
    deriv fdPolygon_seg4 =
      fun _ => (H_height - Real.sqrt 3 / 2) * I := by
  have hrw : fdPolygon_seg4 = fun (t : ℝ) => (-(1:ℂ)/2 + (Real.sqrt 3 / 2) * I) + (↑t - ↑(3:ℝ)) *
        ((H_height - Real.sqrt 3 / 2) * I) := by
    ext t; simp only [fdPolygon_seg4, H_height]
    push_cast; ring
  rw [hrw, deriv_affine_shifted_mul]

lemma fdPolygon_deriv_seg5 :
    deriv fdPolygon_seg5 = fun _ => 1 := by
  have hrw : fdPolygon_seg5 = fun (t : ℝ) => (-(9:ℂ)/2 + H_height * I) + ↑t * (1:ℂ) := by
    ext t; simp only [fdPolygon_seg5, H_height]
    push_cast; ring
  rw [hrw, deriv_affine_mul]

lemma fdPolygon_seg1_differentiable :
    Differentiable ℝ fdPolygon_seg1 := by
  have h : fdPolygon_seg1 = fun (t : ℝ) => ((1:ℂ)/2 + H_height * I) + ↑t *
        (-(H_height - Real.sqrt 3 / 2) * I) := by
    ext t; simp only [fdPolygon_seg1]; ring
  rw [h]
  exact (differentiable_const _).add (Complex.ofRealCLM.differentiable.mul
      (differentiable_const _))

lemma fdPolygon_seg2_differentiable :
    Differentiable ℝ fdPolygon_seg2 := by
  have h : fdPolygon_seg2 = fun (t : ℝ) =>
      rho' + (↑t - (1:ℂ)) * (i_point - rho') := by
    ext t
    simp only [fdPolygon_seg2, chordSegment, rho',
      i_point, Complex.real_smul, Complex.ofReal_sub,
      Complex.ofReal_one]
    ring
  rw [h]
  exact (differentiable_const _).add ((Complex.ofRealCLM.differentiable.sub
        (differentiable_const _)).mul
      (differentiable_const _))

lemma fdPolygon_seg3_differentiable :
    Differentiable ℝ fdPolygon_seg3 := by
  have h : fdPolygon_seg3 = fun (t : ℝ) =>
      i_point + (↑t - (2:ℂ)) * (rho - i_point) := by
    ext t
    simp only [fdPolygon_seg3, chordSegment, rho,
      i_point, Complex.real_smul, Complex.ofReal_sub,
      Complex.ofReal_ofNat, Complex.ofReal_one]
    ring
  rw [h]
  exact (differentiable_const _).add ((Complex.ofRealCLM.differentiable.sub
        (differentiable_const _)).mul
      (differentiable_const _))

lemma fdPolygon_seg4_differentiable :
    Differentiable ℝ fdPolygon_seg4 := by
  have h : fdPolygon_seg4 = fun (t : ℝ) => (-(1:ℂ)/2 + (Real.sqrt 3 / 2) * I) + (↑t - (3:ℂ)) *
        ((H_height - Real.sqrt 3 / 2) * I) := by
    ext t; simp only [fdPolygon_seg4, H_height]
    push_cast; ring
  rw [h]
  exact (differentiable_const _).add ((Complex.ofRealCLM.differentiable.sub
        (differentiable_const _)).mul
      (differentiable_const _))

lemma fdPolygon_seg5_differentiable :
    Differentiable ℝ fdPolygon_seg5 := by
  have h : fdPolygon_seg5 = fun (t : ℝ) => (-(9:ℂ)/2 + H_height * I) + ↑t * (1:ℂ) := by
    ext t; simp only [fdPolygon_seg5, H_height]
    push_cast; ring
  rw [h]
  exact (differentiable_const _).add (Complex.ofRealCLM.differentiable.mul
      (differentiable_const _))

lemma fdPolygon_differentiableAt_off_partition (t : ℝ) (ht : t ∈ Ioo 0 5)
    (ht_not_P : t ∉ ({1, 2, 3, 4} : Finset ℝ)) :
    DifferentiableAt ℝ fdPolygon t := by
  simp only [Finset.mem_insert, Finset.mem_singleton,
    not_or] at ht_not_P
  obtain ⟨ht_ne1, ht_ne2, ht_ne3, ht_ne4⟩ := ht_not_P
  by_cases h1 : t < 1
  · have heq : fdPolygon =ᶠ[𝓝 t] fdPolygon_seg1 := by
      filter_upwards [eventually_lt_nhds h1,
        eventually_gt_nhds ht.1] with s hs1 hs2
      simp only [fdPolygon,
        show s ≤ 1 from le_of_lt hs1, if_true,
        fdPolygon_seg1]
    exact fdPolygon_seg1_differentiable.differentiableAt.congr_of_eventuallyEq heq
  · push_neg at h1
    by_cases h2 : t < 2
    · have h1' : t > 1 :=
        lt_of_le_of_ne h1 (Ne.symm ht_ne1)
      have heq : fdPolygon =ᶠ[𝓝 t] fdPolygon_seg2 := by
        filter_upwards [eventually_gt_nhds h1',
          eventually_lt_nhds h2] with s hs1 hs2
        simp only [fdPolygon,
          show ¬s ≤ 1 from not_le.mpr hs1,
          show s ≤ 2 from le_of_lt hs2,
          if_true, if_false, fdPolygon_seg2]
      exact fdPolygon_seg2_differentiable.differentiableAt.congr_of_eventuallyEq heq
    · push_neg at h2
      by_cases h3 : t < 3
      · have h2' : t > 2 :=
          lt_of_le_of_ne h2 (Ne.symm ht_ne2)
        have heq : fdPolygon =ᶠ[𝓝 t] fdPolygon_seg3 := by
          filter_upwards [eventually_gt_nhds h2',
            eventually_lt_nhds h3] with s hs1 hs2
          simp only [fdPolygon,
            show ¬s ≤ 1 from not_le.mpr (lt_of_lt_of_le (by norm_num : (1:ℝ) < 2)
                (le_of_lt hs1)),
            show ¬s ≤ 2 from not_le.mpr hs1,
            show s ≤ 3 from le_of_lt hs2,
            if_true, if_false, fdPolygon_seg3]
        exact fdPolygon_seg3_differentiable.differentiableAt.congr_of_eventuallyEq heq
      · push_neg at h3
        by_cases h4 : t < 4
        · have h3' : t > 3 :=
            lt_of_le_of_ne h3 (Ne.symm ht_ne3)
          have heq : fdPolygon =ᶠ[𝓝 t] fdPolygon_seg4 := by
            filter_upwards [eventually_gt_nhds h3',
              eventually_lt_nhds h4] with s hs1 hs2
            simp only [fdPolygon,
              show ¬s ≤ 1 from not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 3) hs1),
              show ¬s ≤ 2 from not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 3) hs1),
              show ¬s ≤ 3 from not_le.mpr hs1,
              show s ≤ 4 from le_of_lt hs2,
              if_true, if_false, fdPolygon_seg4]
          exact fdPolygon_seg4_differentiable.differentiableAt.congr_of_eventuallyEq heq
        · push_neg at h4
          have h4' : t > 4 :=
            lt_of_le_of_ne h4 (Ne.symm ht_ne4)
          have heq : fdPolygon =ᶠ[𝓝 t] fdPolygon_seg5 := by
            filter_upwards [eventually_gt_nhds h4',
              eventually_lt_nhds ht.2] with s hs1 hs2
            simp only [fdPolygon,
              show ¬s ≤ 1 from not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 4) hs1),
              show ¬s ≤ 2 from not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 4) hs1),
              show ¬s ≤ 3 from not_le.mpr (lt_trans (by norm_num : (3:ℝ) < 4) hs1),
              show ¬s ≤ 4 from not_le.mpr hs1,
              if_false, fdPolygon_seg5]
          exact fdPolygon_seg5_differentiable.differentiableAt.congr_of_eventuallyEq heq

lemma fdPolygon_seg1_deriv_val :
    -(H_height - Real.sqrt 3 / 2) * I = -I := by
  simp only [H_height]; push_cast; ring

lemma fdPolygon_seg4_deriv_val : (H_height - Real.sqrt 3 / 2) * I = I := by
  simp only [H_height]; push_cast; ring

end RectHomotopyProof
