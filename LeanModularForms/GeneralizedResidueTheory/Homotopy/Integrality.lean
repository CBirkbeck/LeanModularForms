/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Basic
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Winding Number Integrality

Definitions for piecewise and smooth homotopies, plus the exp trick proof
that winding numbers of closed curves avoiding a point are integers.

## Main Definitions

* `PiecewiseCurvesHomotopicAvoiding` — piecewise C¹ homotopy avoiding z₀
* `ClosedCurvesHomotopicAvoiding` — smooth closed homotopy avoiding z₀

## Main Results

* `windingNumber_integer_of_piecewise_closed_avoiding` — winding number is
    an integer for piecewise C¹ closed curves
* `windingNumber_integer_of_closed_avoiding` — winding number is an integer
    for smooth closed curves
* `exp_integral_eq_endpoint_ratio` — exponential of the log-derivative
    integral equals endpoint ratio
* `integral_closed_curve_eq_two_pi_int` — closed curve integral is 2πi times
    an integer
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Piecewise C¹ homotopy between closed curves avoiding z₀. -/
def PiecewiseCurvesHomotopicAvoiding (γ₀ γ₁ : ℝ → ℂ)
    (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    Continuous H ∧
    (∀ t ∈ Icc a b, H (t, 0) = γ₀ t) ∧
    (∀ t ∈ Icc a b, H (t, 1) = γ₁ t) ∧
    (∀ s ∈ Icc (0:ℝ) 1, H (a, s) = H (b, s)) ∧
    (∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1,
      H (t, s) ≠ z₀) ∧
    (∀ t ∈ Ioo a b, t ∉ P →
      ∀ s ∈ Icc (0:ℝ) 1,
        DifferentiableAt ℝ (fun t' => H (t', s)) t) ∧
    (∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) →
        Ioo p₁ p₂ ⊆ Ioo a b →
          ContinuousOn
            (fun (p : ℝ × ℝ) =>
              deriv (fun t' => H (t', p.2)) p.1)
            (Ioo p₁ p₂ ×ˢ Icc 0 1)) ∧
    (∃ M : ℝ, ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1,
      ‖deriv (fun t' => H (t', s)) t‖ ≤ M)

/-- Smooth closed homotopy between curves avoiding z₀. -/
def ClosedCurvesHomotopicAvoiding (γ₀ γ₁ : ℝ → ℂ)
    (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    Continuous H ∧
    (∀ t ∈ Icc a b, H (t, 0) = γ₀ t) ∧
    (∀ t ∈ Icc a b, H (t, 1) = γ₁ t) ∧
    (∀ s ∈ Icc (0:ℝ) 1, H (a, s) = H (b, s)) ∧
    (∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1,
      H (t, s) ≠ z₀) ∧
    (∀ t ∈ Ioo a b, ∀ s ∈ Icc (0:ℝ) 1,
      DifferentiableAt ℝ (fun t' => H (t', s)) t) ∧
    (Continuous (fun p : ℝ × ℝ =>
      deriv (fun t' => H (t', p.2)) p.1))

/-- If f is eventually equal to a constant along a filter,
then the limit equals that constant. -/
theorem limUnder_eventually_eq_const {α : Type*}
    [TopologicalSpace α] {f : α → ℂ} {l : Filter α}
    {c : ℂ} [l.NeBot] (hf : ∀ᶠ x in l, f x = c) :
    limUnder l f = c := by
  apply Filter.Tendsto.limUnder_eq
  rw [Filter.tendsto_def]
  intro s hs
  filter_upwards [hf] with x hx
  show f x ∈ s; rw [hx]; exact mem_of_mem_nhds hs

private lemma windingNumber_integer_of_piecewise_with_bound
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ)
    (M : ℝ) (hab : a < b)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_deriv_bound : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M)
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀) :
    ∃ n : ℤ, generalizedWindingNumber' γ a b z₀ = n := by
  have h_bound_away : ∃ δ > 0, ∀ t ∈ Icc a b, δ ≤ ‖γ t - z₀‖ := by
    have h_compact : IsCompact (γ '' Icc a b) := isCompact_Icc.image_of_continuousOn hγ_cont
    have h_nonempty : (γ '' Icc a b).Nonempty :=
      Set.image_nonempty.mpr (nonempty_Icc.mpr (le_of_lt hab))
    have hz₀_notin : z₀ ∉ γ '' Icc a b := fun ⟨t, ht, heq⟩ => hγ_avoids t ht heq
    have hδ : 0 < Metric.infDist z₀ (γ '' Icc a b) :=
      (h_compact.isClosed.notMem_iff_infDist_pos h_nonempty).mp hz₀_notin
    exact ⟨Metric.infDist z₀ (γ '' Icc a b), hδ, fun t ht => by
      calc Metric.infDist z₀ (γ '' Icc a b) ≤ dist z₀ (γ t) :=
            Metric.infDist_le_dist_of_mem (mem_image_of_mem γ ht)
        _ = ‖γ t - z₀‖ := by rw [Complex.dist_eq, norm_sub_rev]⟩
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := h_bound_away
  let integrand : ℝ → ℂ := fun t => deriv γ t / (γ t - z₀)
  have h_integrand_bound : ∀ t ∈ Icc a b, ‖integrand t‖ ≤ M / δ := by
    intro t ht
    simp only [integrand, norm_div]
    calc ‖deriv γ t‖ / ‖γ t - z₀‖ ≤ ‖deriv γ t‖ / δ :=
            div_le_div_of_nonneg_left (norm_nonneg _) hδ_pos (hδ_bound t ht)
      _ ≤ M / δ := div_le_div_of_nonneg_right (hγ_deriv_bound t ht) (le_of_lt hδ_pos)
  let P' : Finset ℝ := P ∪ {a, b}
  have h_integrand_cont : ContinuousOn integrand ((Icc a b) \ P') := by
    intro t ⟨ht_Icc, ht_notP'⟩
    simp only [P', Finset.coe_union, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_notP'
    have ht_Ioo : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht_Icc.1 (Ne.symm ht_notP'.2.1),
                                   lt_of_le_of_ne ht_Icc.2 ht_notP'.2.2⟩
    have ht_notP : t ∉ P := ht_notP'.1
    have hne : γ t - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoids t ht_Icc)
    apply ContinuousWithinAt.div
    · have h_away : ∃ ε > 0, ∀ x ∈ Ioo (t - ε) (t + ε), x ∉ P := by
        by_cases hP_empty : P = ∅
        · exact ⟨1, one_pos, fun x _ => by simp [hP_empty]⟩
        · have hP_ne : P.Nonempty := Finset.nonempty_of_ne_empty hP_empty
          have h_ne_mem : ∀ p ∈ P, p ≠ t := fun p hp => ne_of_mem_of_not_mem hp ht_notP
          let d := Finset.inf' P hP_ne (fun p => |p - t|)
          have hd_pos : 0 < d := by
            rw [Finset.lt_inf'_iff]
            exact fun p hp => abs_pos.mpr (sub_ne_zero.mpr (h_ne_mem p hp))
          exact ⟨d / 2, by linarith, fun x hx hxP => by
            have h_dist : d ≤ |x - t| := Finset.inf'_le (fun p => |p - t|) hxP
            have hx_dist : |x - t| < d := by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
            linarith⟩
      obtain ⟨ε, hε_pos, hε_avoid⟩ := h_away
      let p₁ := max a (t - ε / 2)
      let p₂ := min b (t + ε / 2)
      have hp₁p₂ : p₁ < p₂ := by
        simp only [p₁, p₂, lt_min_iff, max_lt_iff]
        exact ⟨⟨lt_trans ht_Ioo.1 ht_Ioo.2, by linarith [ht_Ioo.2, hε_pos]⟩,
               ⟨by linarith [ht_Ioo.1, hε_pos], by linarith⟩⟩
      have h_piece_avoid : ∀ s ∈ Ioo p₁ p₂, s ∉ P := by
        intro s hs; apply hε_avoid
        simp only [p₁, p₂, mem_Ioo] at hs
        exact ⟨by linarith [le_max_right a (t - ε / 2), hs.1],
               by linarith [min_le_right b (t + ε / 2), hs.2]⟩
      have h_sub : Ioo p₁ p₂ ⊆ Ioo a b := fun x hx => by
        simp only [p₁, p₂, mem_Ioo] at hx ⊢
        exact ⟨lt_of_le_of_lt (le_max_left a _) hx.1, lt_of_lt_of_le hx.2 (min_le_left b _)⟩
      have ht_in : t ∈ Ioo p₁ p₂ := by
        simp only [p₁, p₂, mem_Ioo, lt_min_iff, max_lt_iff]
        exact ⟨⟨ht_Ioo.1, by linarith [hε_pos]⟩, ⟨ht_Ioo.2, by linarith [hε_pos]⟩⟩
      exact ((hγ_deriv_cont p₁ p₂ hp₁p₂ h_piece_avoid h_sub).continuousAt
        (Ioo_mem_nhds ht_in.1 ht_in.2)).continuousWithinAt
    · exact (hγ_cont.sub continuousOn_const).continuousWithinAt ht_Icc |>.mono diff_subset
    · exact hne
  have h_int : IntervalIntegrable integrand MeasureTheory.volume a b :=
    intervalIntegrable_of_piecewise_continuousOn_bounded (M / δ) (le_of_lt hab)
      h_integrand_cont h_integrand_bound
  let F : ℝ → ℂ := fun t => ∫ s in a..t, integrand s
  let G : ℝ → ℂ := fun t => (γ t - z₀) * Complex.exp (-F t)
  have hFa : F a = 0 := intervalIntegral.integral_same
  have hGa : G a = γ a - z₀ := by simp only [G, hFa, neg_zero, Complex.exp_zero, mul_one]
  have hG_const : ∀ t ∈ Icc a b, G t = G a := by
    have hG_cont : ContinuousOn G (Icc a b) := by
      apply ContinuousOn.mul
      · exact hγ_cont.sub continuousOn_const
      · apply Continuous.comp_continuousOn Complex.continuous_exp
        apply ContinuousOn.neg
        have h_prim := intervalIntegral.continuousOn_primitive_interval' h_int
          (left_mem_uIcc (a := a) (b := b))
        rwa [Set.uIcc_of_le (le_of_lt hab)] at h_prim
    have hG_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ G t := by
      intro t ht ht_not_P
      apply DifferentiableAt.mul
      · exact (hγ_diff t ht ht_not_P).sub (differentiableAt_const z₀)
      · apply DifferentiableAt.cexp; apply DifferentiableAt.neg
        have h_away : ∃ ε > 0, ∀ x ∈ Ioo (t - ε) (t + ε), x ∉ P := by
          by_cases hP_empty : P = ∅
          · exact ⟨1, one_pos, fun x _ => by simp [hP_empty]⟩
          · have hP_ne : P.Nonempty := Finset.nonempty_of_ne_empty hP_empty
            have h_ne_mem : ∀ p ∈ P, p ≠ t := fun p hp => ne_of_mem_of_not_mem hp ht_not_P
            let d := Finset.inf' P hP_ne (fun p => |p - t|)
            have hd_pos : 0 < d := by
              rw [Finset.lt_inf'_iff]
              exact fun p hp => abs_pos.mpr (sub_ne_zero.mpr (h_ne_mem p hp))
            exact ⟨d / 2, by linarith, fun x hx hxP => by
              have h_dist : d ≤ |x - t| := Finset.inf'_le (fun p => |p - t|) hxP
              have hx_dist : |x - t| < d := by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
              linarith⟩
        obtain ⟨ε, hε_pos, hε_avoid⟩ := h_away
        let p₁ := max a (t - ε / 2)
        let p₂ := min b (t + ε / 2)
        have hp₁p₂ : p₁ < p₂ := by
          simp only [p₁, p₂, lt_min_iff, max_lt_iff]
          exact ⟨⟨lt_trans ht.1 ht.2, by linarith [ht.2, hε_pos]⟩,
                 ⟨by linarith [ht.1, hε_pos], by linarith⟩⟩
        have h_piece_avoid : ∀ s ∈ Ioo p₁ p₂, s ∉ P := by
          intro s hs; apply hε_avoid
          simp only [p₁, p₂, mem_Ioo] at hs
          exact ⟨by linarith [le_max_right a (t - ε / 2), hs.1],
                 by linarith [min_le_right b (t + ε / 2), hs.2]⟩
        have h_sub : Ioo p₁ p₂ ⊆ Ioo a b := fun x hx => by
          simp only [p₁, p₂, mem_Ioo] at hx ⊢
          exact ⟨lt_of_le_of_lt (le_max_left a _) hx.1, lt_of_lt_of_le hx.2 (min_le_left b _)⟩
        have h_deriv_cont := hγ_deriv_cont p₁ p₂ hp₁p₂ h_piece_avoid h_sub
        have ht_in : t ∈ Ioo p₁ p₂ := by
          simp only [p₁, p₂, mem_Ioo, lt_min_iff, max_lt_iff]
          exact ⟨⟨ht.1, by linarith [hε_pos]⟩, ⟨ht.2, by linarith [hε_pos]⟩⟩
        have hne : γ t - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoids t (Ioo_subset_Icc_self ht))
        have h_cont_at : ContinuousAt integrand t :=
          ContinuousAt.div (h_deriv_cont.continuousAt (Ioo_mem_nhds ht_in.1 ht_in.2))
            (hγ_cont.continuousAt (Icc_mem_nhds ht.1 ht.2) |>.sub continuousAt_const) hne
        have h_integrand_cont_ioo : ContinuousOn integrand (Ioo p₁ p₂) := by
          intro x hx
          have hx_Ioo_ab : x ∈ Ioo a b := h_sub hx
          have hx_ne : γ x - z₀ ≠ 0 :=
            sub_ne_zero.mpr (hγ_avoids x (Ioo_subset_Icc_self hx_Ioo_ab))
          exact ContinuousWithinAt.div (h_deriv_cont.continuousWithinAt hx)
            (((hγ_cont.sub continuousOn_const).continuousWithinAt
              (Ioo_subset_Icc_self hx_Ioo_ab)).mono
              ((Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)).trans Ioo_subset_Icc_self))
            hx_ne
        have h_meas : StronglyMeasurableAtFilter integrand (𝓝 t) volume :=
          ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
            (fun x hx => h_integrand_cont_ioo.continuousAt (Ioo_mem_nhds hx.1 hx.2)) t ht_in
        have ht_in_uIcc : t ∈ Set.uIcc a b := by
          rw [Set.uIcc_of_le (le_of_lt hab)]; exact Ioo_subset_Icc_self ht
        exact (intervalIntegral.integral_hasDerivAt_right
          (h_int.mono_set (Set.uIcc_subset_uIcc_left ht_in_uIcc))
          h_meas h_cont_at).differentiableAt
    have hG_deriv : ∀ t ∈ Ioo a b, t ∉ P → deriv G t = 0 := by
      intro t ht ht_not_P
      have hne : γ t - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoids t (Ioo_subset_Icc_self ht))
      have h_away : ∃ ε > 0, ∀ x ∈ Ioo (t - ε) (t + ε), x ∉ P := by
        by_cases hP_empty : P = ∅
        · exact ⟨1, one_pos, fun x _ => by simp [hP_empty]⟩
        · have hP_ne : P.Nonempty := Finset.nonempty_of_ne_empty hP_empty
          have h_ne_mem : ∀ p ∈ P, p ≠ t := fun p hp => ne_of_mem_of_not_mem hp ht_not_P
          let d := Finset.inf' P hP_ne (fun p => |p - t|)
          have hd_pos : 0 < d := by
            rw [Finset.lt_inf'_iff]
            exact fun p hp => abs_pos.mpr (sub_ne_zero.mpr (h_ne_mem p hp))
          exact ⟨d / 2, by linarith, fun x hx hxP => by
            have h_dist : d ≤ |x - t| := Finset.inf'_le (fun p => |p - t|) hxP
            have hx_dist : |x - t| < d := by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
            linarith⟩
      obtain ⟨ε, hε_pos, hε_avoid⟩ := h_away
      let p₁ := max a (t - ε / 2)
      let p₂ := min b (t + ε / 2)
      have hp₁p₂ : p₁ < p₂ := by
        simp only [p₁, p₂, lt_min_iff, max_lt_iff]
        exact ⟨⟨lt_trans ht.1 ht.2, by linarith [ht.2, hε_pos]⟩,
               ⟨by linarith [ht.1, hε_pos], by linarith⟩⟩
      have h_piece_avoid : ∀ s ∈ Ioo p₁ p₂, s ∉ P := by
        intro s hs; apply hε_avoid
        simp only [p₁, p₂, mem_Ioo] at hs
        exact ⟨by linarith [le_max_right a (t - ε / 2), hs.1],
               by linarith [min_le_right b (t + ε / 2), hs.2]⟩
      have h_sub : Ioo p₁ p₂ ⊆ Ioo a b := fun x hx => by
        simp only [p₁, p₂, mem_Ioo] at hx ⊢
        exact ⟨lt_of_le_of_lt (le_max_left a _) hx.1, lt_of_lt_of_le hx.2 (min_le_left b _)⟩
      have h_deriv_cont := hγ_deriv_cont p₁ p₂ hp₁p₂ h_piece_avoid h_sub
      have ht_in : t ∈ Ioo p₁ p₂ := by
        simp only [p₁, p₂, mem_Ioo, lt_min_iff, max_lt_iff]
        exact ⟨⟨ht.1, by linarith [hε_pos]⟩, ⟨ht.2, by linarith [hε_pos]⟩⟩
      have h_cont_at : ContinuousAt integrand t :=
        ContinuousAt.div (h_deriv_cont.continuousAt (Ioo_mem_nhds ht_in.1 ht_in.2))
          (hγ_cont.continuousAt (Icc_mem_nhds ht.1 ht.2) |>.sub continuousAt_const) hne
      have h_integrand_cont_ioo : ContinuousOn integrand (Ioo p₁ p₂) := by
        intro x hx
        have hx_Ioo_ab : x ∈ Ioo a b := h_sub hx
        have hx_ne : γ x - z₀ ≠ 0 :=
          sub_ne_zero.mpr (hγ_avoids x (Ioo_subset_Icc_self hx_Ioo_ab))
        exact ContinuousWithinAt.div (h_deriv_cont.continuousWithinAt hx)
          (((hγ_cont.sub continuousOn_const).continuousWithinAt
            (Ioo_subset_Icc_self hx_Ioo_ab)).mono
            ((Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)).trans Ioo_subset_Icc_self))
          hx_ne
      have h_meas : StronglyMeasurableAtFilter integrand (𝓝 t) volume :=
        ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
          (fun x hx => h_integrand_cont_ioo.continuousAt (Ioo_mem_nhds hx.1 hx.2)) t ht_in
      have ht_in_uIcc : t ∈ Set.uIcc a b := by
        rw [Set.uIcc_of_le (le_of_lt hab)]; exact Ioo_subset_Icc_self ht
      have hF_deriv : HasDerivAt F (integrand t) t :=
        intervalIntegral.integral_hasDerivAt_right
          (h_int.mono_set (Set.uIcc_subset_uIcc_left ht_in_uIcc)) h_meas h_cont_at
      have hc : HasDerivAt (fun t => γ t - z₀) (deriv γ t) t :=
        (hγ_diff t ht ht_not_P).hasDerivAt.sub_const z₀
      have hd : HasDerivAt (fun t => Complex.exp (-F t))
          (Complex.exp (-F t) * (-integrand t)) t := HasDerivAt.cexp hF_deriv.neg
      have hG_at : HasDerivAt G (deriv γ t * Complex.exp (-F t) +
          (γ t - z₀) * (Complex.exp (-F t) * (-integrand t))) t := hc.mul hd
      have h_zero : deriv γ t * Complex.exp (-F t) +
          (γ t - z₀) * (Complex.exp (-F t) * (-integrand t)) = 0 := by
        simp only [integrand]; field_simp [hne]; ring
      rw [hG_at.deriv]; exact h_zero
    exact constant_of_has_deriv_right_zero hG_cont
      (hasDerivWithinAt_zero_of_deriv_zero_off_finite G a b P hab hG_cont hG_diff hG_deriv)
  have hne_a : γ a - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoids a (left_mem_Icc.mpr (le_of_lt hab)))
  have h_exp_neg : Complex.exp (-F b) = 1 := by
    have h1 : (γ a - z₀) * Complex.exp (-F b) = γ a - z₀ := by
      calc (γ a - z₀) * Complex.exp (-F b)
          = (γ b - z₀) * Complex.exp (-F b) := by rw [hγ_closed]
        _ = G b := rfl
        _ = G a := hG_const b (right_mem_Icc.mpr (le_of_lt hab))
        _ = γ a - z₀ := hGa
    have h2 : (γ a - z₀) * Complex.exp (-F b) = (γ a - z₀) * 1 := by rw [h1, mul_one]
    exact mul_left_cancel₀ hne_a h2
  rw [Complex.exp_eq_one_iff] at h_exp_neg
  obtain ⟨n, hn⟩ := h_exp_neg
  use -n
  unfold generalizedWindingNumber'
  have h_pv_eq : cauchyPrincipalValue' (·⁻¹) (fun t => γ t - z₀) a b 0 =
      ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t := by
    unfold cauchyPrincipalValue'
    apply limUnder_eventually_eq_const
    filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    simp only [sub_zero]
    have ht' : t ∈ Icc a b := Ioc_subset_Icc_self (Set.uIoc_of_le (le_of_lt hab) ▸ ht)
    simp only [(mem_Ioo.mp hε).2.trans_le (hδ_bound t ht'), ↓reduceIte, deriv_sub_const]
  rw [h_pv_eq]
  have h_int_eq : ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t = F b := by
    simp only [F, integrand]; congr 1; ext t; rw [mul_comm, div_eq_mul_inv]
  rw [h_int_eq]
  have hFb : F b = -(↑n * (2 * Real.pi * I)) := by
    calc F b = -(-F b) := by ring
      _ = -(↑n * (2 * Real.pi * I)) := by rw [hn]
  calc (2 * Real.pi * I)⁻¹ * F b
      = (2 * Real.pi * I)⁻¹ * (-(↑n * (2 * Real.pi * I))) := by rw [hFb]
    _ = -(↑n : ℂ) := by
        have hne : (2 : ℂ) * Real.pi * I ≠ 0 := by
          simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero,
            Real.pi_ne_zero, Complex.I_ne_zero, or_self, not_false_eq_true]
        field_simp
    _ = ↑(-n) := by simp only [Int.cast_neg]

lemma windingNumber_integer_of_piecewise_closed_avoiding
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ) (hab : a < b)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (hγ_deriv_bound_ex : ∃ M, ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M) :
    ∃ n : ℤ, generalizedWindingNumber' γ a b z₀ = n := by
  obtain ⟨M, hM⟩ := hγ_deriv_bound_ex
  exact windingNumber_integer_of_piecewise_with_bound
    γ a b z₀ P M hab hγ_closed hγ_cont hγ_diff hγ_deriv_cont hM hγ_avoids

/-- Uniform bound for winding number integrand from homotopy avoidance. -/
theorem winding_integrand_bounded_of_uniform_avoidance
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {δ M : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, δ ≤ ‖H (t, s) - z₀‖)
    (hM_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1,
      ‖deriv (fun t' => H (t', s)) t‖ ≤ M) :
    ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1,
      ‖(H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t‖ ≤ M / δ := by
  intro t ht s hs
  have h_ne : H (t, s) - z₀ ≠ 0 := by
    intro heq
    have h := hδ_bound t ht s hs
    simp only [heq, norm_zero] at h
    linarith
  have h_inv_bound : ‖(H (t, s) - z₀)⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv, inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hδ_pos (hδ_bound t ht s hs)
  calc ‖(H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t‖
      ≤ ‖(H (t, s) - z₀)⁻¹‖ * ‖deriv (fun t' => H (t', s)) t‖ := norm_mul_le _ _
    _ ≤ δ⁻¹ * M := mul_le_mul h_inv_bound (hM_bound t ht s hs)
        (norm_nonneg _) (le_of_lt (inv_pos.mpr hδ_pos))
    _ = M / δ := by ring

theorem exp_integral_eq_endpoint_ratio
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    Complex.exp (∫ t in a..b, deriv γ t / (γ t - z₀)) =
      (γ b - z₀) / (γ a - z₀) := by
  have h_integrand_cont :
      ContinuousOn (fun t => deriv γ t / (γ t - z₀)) (Icc a b) :=
    hγ'_cont.div (hγ_cont.sub continuousOn_const)
      fun t ht => sub_ne_zero.mpr (hγ_avoid t ht)
  have h_int :
      IntervalIntegrable (fun t => deriv γ t / (γ t - z₀))
        volume a b :=
    h_integrand_cont.intervalIntegrable_of_Icc (le_of_lt hab)
  let F : ℝ → ℂ := fun t =>
    ∫ s in a..t, deriv γ s / (γ s - z₀)
  let G : ℝ → ℂ := fun t =>
    (γ t - z₀) * Complex.exp (-F t)
  have hFa : F a = 0 := intervalIntegral.integral_same
  have hGa : G a = γ a - z₀ := by
    simp only [G, hFa, neg_zero, Complex.exp_zero, mul_one]
  have hG_const : ∀ t ∈ Icc a b, G t = G a := by
    have hG_cont : ContinuousOn G (Icc a b) := by
      have hF_cont : ContinuousOn F (Icc a b) := by
        have huIcc : Set.uIcc a b = Icc a b :=
          Set.uIcc_of_le (le_of_lt hab)
        have := intervalIntegral.continuousOn_primitive_interval'
          h_int left_mem_uIcc
        rwa [huIcc] at this
      exact (hγ_cont.sub continuousOn_const).mul
        (Complex.continuous_exp.comp_continuousOn hF_cont.neg)
    have hF_hasDerivAt :
        ∀ t ∈ Ioo a b,
          HasDerivAt F (deriv γ t / (γ t - z₀)) t := by
      intro t ht
      have huIcc_at : Set.uIcc a t ⊆ Set.uIcc a b := by
        rw [Set.uIcc_of_le (le_of_lt ht.1),
          Set.uIcc_of_le (le_of_lt hab)]
        exact Icc_subset_Icc le_rfl (le_of_lt ht.2)
      exact intervalIntegral.integral_hasDerivAt_right
        (h_int.mono_set huIcc_at)
        (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
          (fun x hx => h_integrand_cont.continuousAt
            (Icc_mem_nhds hx.1 hx.2)) t ht)
        (h_integrand_cont.continuousAt
          (Icc_mem_nhds ht.1 ht.2))
    have hG_deriv_right :
        ∀ t ∈ Ico a b,
          HasDerivWithinAt G 0 (Ici t) t := by
      intro t ht
      by_cases ha_eq : t = a
      · rw [ha_eq]
        have h_Ioo_mem :
            Ioo a b ∈ nhdsWithin a (Ioi a) := by
          rw [mem_nhdsWithin]
          exact ⟨Iio b, isOpen_Iio, mem_Iio.mpr hab,
            fun x ⟨hxb, hxa⟩ => ⟨hxa, hxb⟩⟩
        apply hasDerivWithinAt_Ici_of_tendsto_deriv
        · intro t ht
          exact ((hγ_diff t ht).sub_const z₀).mul
            (Complex.differentiable_exp.differentiableAt.comp
              t (hF_hasDerivAt t ht).differentiableAt.neg)
            |>.differentiableWithinAt
        · exact hG_cont.continuousWithinAt
            (left_mem_Icc.mpr (le_of_lt hab))
            |>.mono Ioo_subset_Icc_self
        · exact h_Ioo_mem
        · have h_deriv_zero :
              ∀ t ∈ Ioo a b, deriv G t = 0 := by
            intro t ht
            have hF_t := hF_hasDerivAt t ht
            have hprod := ((hγ_diff t ht).hasDerivAt.sub_const
              z₀).mul hF_t.neg.cexp
            exact hprod.deriv.trans (by
              have := sub_ne_zero.mpr
                (hγ_avoid t (Ioo_subset_Icc_self ht))
              field_simp; ring)
          exact tendsto_const_nhds.congr' (by
            filter_upwards [h_Ioo_mem] with t ht
            exact (h_deriv_zero t ht).symm)
      · have ht' : t ∈ Ioo a b :=
          ⟨lt_of_le_of_ne ht.1 (Ne.symm ha_eq), ht.2⟩
        have hG_hasDerivAt : HasDerivAt G 0 t := by
          convert ((hγ_diff t ht').hasDerivAt.sub_const
            z₀).mul (hF_hasDerivAt t ht').neg.cexp using 1
          have := sub_ne_zero.mpr
            (hγ_avoid t (Ioo_subset_Icc_self ht'))
          field_simp; ring
        exact hG_hasDerivAt.hasDerivWithinAt
    exact constant_of_has_deriv_right_zero hG_cont
      hG_deriv_right
  have hGeq : G b = G a :=
    hG_const b (right_mem_Icc.mpr (le_of_lt hab))
  rw [hGa, show G b = (γ b - z₀) *
    Complex.exp (-(∫ t in a..b,
      deriv γ t / (γ t - z₀))) from rfl] at hGeq
  have hne := sub_ne_zero.mpr
    (hγ_avoid b (right_mem_Icc.mpr (le_of_lt hab)))
  have h1 : Complex.exp
      (-(∫ t in a..b, deriv γ t / (γ t - z₀))) =
      (γ a - z₀) / (γ b - z₀) := by
    field_simp at hGeq ⊢; exact hGeq
  rw [show Complex.exp
      (∫ t in a..b, deriv γ t / (γ t - z₀)) =
      (Complex.exp (-(∫ t in a..b,
        deriv γ t / (γ t - z₀))))⁻¹ from by
    rw [Complex.exp_neg, inv_inv],
    h1, inv_div]

private theorem integral_closed_curve_eq_two_pi_int
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    ∃ n : ℤ, ∫ t in a..b, deriv γ t / (γ t - z₀) =
      2 * Real.pi * I * n := by
  have hexp : Complex.exp
      (∫ t in a..b, deriv γ t / (γ t - z₀)) = 1 := by
    rw [exp_integral_eq_endpoint_ratio γ a b z₀ hab
      hγ_cont hγ_diff hγ_avoid hγ'_cont, hγ_closed]
    exact div_self (sub_ne_zero.mpr
      (hγ_avoid b (right_mem_Icc.mpr (le_of_lt hab))))
  rw [Complex.exp_eq_one_iff] at hexp
  obtain ⟨n, hn⟩ := hexp
  exact ⟨n, by rw [hn]; ring⟩

/-- The winding number of a smooth closed curve avoiding z₀
is an integer. -/
theorem windingNumber_integer_of_closed_avoiding
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b,
      DifferentiableAt ℝ γ t)
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b))
    (hγ_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀) :
    ∃ n : ℤ,
    generalizedWindingNumber' γ a b z₀ = n := by
  let τ := fun t => γ t - z₀
  have hτ_closed : τ a = τ b := by
    simp only [τ]; rw [hγ_closed]
  have hτ_cont : ContinuousOn τ (Icc a b) :=
    hγ_cont.sub continuousOn_const
  have hτ_diff : ∀ t ∈ Ioo a b,
      DifferentiableAt ℝ τ t := fun t ht =>
    (hγ_diff t ht).sub (differentiableAt_const z₀)
  have hτ_avoid : ∀ t ∈ Icc a b, τ t ≠ 0 :=
    fun t ht => sub_ne_zero.mpr (hγ_avoid t ht)
  have hτ'_cont : ContinuousOn (deriv τ) (Icc a b) := by
    rw [show deriv τ = deriv γ from
      funext fun t => deriv_sub_const z₀]
    exact hγ'_cont
  obtain ⟨n, hn⟩ := integral_closed_curve_eq_two_pi_int
    τ a b 0 hab hτ_closed hτ_cont hτ_diff hτ_avoid
    hτ'_cont
  use n
  unfold generalizedWindingNumber'
  have h_integrand_eq :
      (fun t => deriv τ t / (τ t - 0)) =
      (fun t => deriv γ t / (γ t - z₀)) := by
    ext t; simp only [τ, sub_zero, deriv_sub_const]
  rw [h_integrand_eq] at hn
  have h_compact : IsCompact (γ '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn hγ_cont
  have h_nonempty : (γ '' Icc a b).Nonempty :=
    Set.image_nonempty.mpr
      (nonempty_Icc.mpr (le_of_lt hab))
  have hz₀_notin : z₀ ∉ γ '' Icc a b :=
    fun ⟨t, ht, heq⟩ => hγ_avoid t ht heq
  have hδ : 0 < Metric.infDist z₀ (γ '' Icc a b) :=
    (h_compact.isClosed.notMem_iff_infDist_pos
      h_nonempty).mp hz₀_notin
  have h_cutoff_trivial :
      ∀ᶠ ε in 𝓝[>] (0:ℝ),
        ∀ t ∈ Icc a b, ε < ‖γ t - z₀‖ := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε t ht
    calc ε < Metric.infDist z₀ (γ '' Icc a b) :=
          (mem_Ioo.mp hε).2
      _ ≤ dist z₀ (γ t) :=
          Metric.infDist_le_dist_of_mem
            (mem_image_of_mem γ ht)
      _ = ‖γ t - z₀‖ := by
          rw [Complex.dist_eq, norm_sub_rev]
  have h_pv_eq :
      cauchyPrincipalValue' (·⁻¹) (fun t => γ t - z₀)
        a b 0 =
      ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t := by
    unfold cauchyPrincipalValue'
    apply limUnder_eventually_eq_const
    filter_upwards [h_cutoff_trivial] with ε hε
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t
    intro ht
    simp only [sub_zero]
    have ht' : t ∈ Icc a b := by
      rw [Set.uIoc_of_le (le_of_lt hab)] at ht
      exact Ioc_subset_Icc_self ht
    simp only [hε t ht', ↓reduceIte, deriv_sub_const]
  rw [h_pv_eq, show ∫ t in a..b,
    (γ t - z₀)⁻¹ * deriv γ t =
    ∫ t in a..b, deriv γ t / (γ t - z₀) from by
      congr 1; ext t; rw [mul_comm, div_eq_mul_inv],
    hn]
  field_simp

end
