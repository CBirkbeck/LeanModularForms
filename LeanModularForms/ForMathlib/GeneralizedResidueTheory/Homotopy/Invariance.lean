/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Homotopy.Integrality
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Homotopy.ParametricDiff

/-!
# Homotopy Invariance of Winding Numbers

Homotopy invariance for generalized winding numbers (both piecewise C¹ and
smooth), plus the classical winding number formula for curves avoiding a point.

## Main Results

* `windingNumber_eq_of_piecewise_homotopic` — winding number invariant
    under piecewise homotopy
* `windingNumber_eq_of_homotopic_closed` — winding number invariant
    under smooth homotopy
* `generalizedWindingNumber_eq_classical_away` — PV winding number
    equals classical integral when curve avoids z₀
* `contourIntegral_eq_of_homotopic` — contour integrals equal under
    homotopy for holomorphic integrands
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

private theorem homotopy_uniform_avoidance
    (H : ℝ × ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b) (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀) :
    ∃ δ > 0, ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, δ ≤ ‖H (t, s) - z₀‖ := by
  have hcompact : IsCompact (H '' (Icc a b ×ˢ Icc (0:ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image hH_cont
  have hnonempty : (H '' (Icc a b ×ˢ Icc (0:ℝ) 1)).Nonempty :=
    ⟨H (a, 0), (a, 0), ⟨left_mem_Icc.mpr hab.le, left_mem_Icc.mpr zero_le_one⟩, rfl⟩
  have hz_notin : z₀ ∉ H '' (Icc a b ×ˢ Icc (0:ℝ) 1) :=
    fun ⟨⟨t, s⟩, ⟨ht, hs⟩, heq⟩ => hH_avoid t ht s hs heq
  refine ⟨_, (hcompact.isClosed.notMem_iff_infDist_pos hnonempty).mp hz_notin,
    fun t ht s hs => ?_⟩
  have hmem : H (t, s) ∈ H '' (Icc a b ×ˢ Icc (0:ℝ) 1) := ⟨(t, s), ⟨ht, hs⟩, rfl⟩
  calc Metric.infDist z₀ _ ≤ dist z₀ (H (t, s)) := Metric.infDist_le_dist_of_mem hmem
    _ = ‖H (t, s) - z₀‖ := by rw [Complex.dist_eq, norm_sub_rev]

private lemma homotopy_integrand_continuousOn_t
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ}
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀)
    (hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1))
    {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    let f := fun t s => (H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t
    let P' : Finset ℝ := P ∪ {a, b}
    ContinuousOn (fun t => f t s) ((Icc a b) \ P') := by
  intro f P' t ⟨ht_Icc, ht_notP'⟩
  simp only [P', Finset.coe_union, Finset.coe_pair, Set.mem_union,
    Set.mem_insert_iff, not_or] at ht_notP'
  have ht_Ioo : t ∈ Ioo a b :=
    ⟨lt_of_le_of_ne ht_Icc.1 (Ne.symm ht_notP'.2.1),
     lt_of_le_of_ne ht_Icc.2 ht_notP'.2.2⟩
  obtain ⟨p₁, p₂, hp, ht_in, h_avoid_P, h_sub_ab⟩ :=
    exists_subinterval_avoiding_finset ht_Ioo ht_notP'.1
  apply ContinuousWithinAt.mono _ (Set.diff_subset_diff_right (Finset.coe_subset.mpr
    (Finset.subset_union_left (s₂ := {a, b}))))
  exact ContinuousWithinAt.mul
    ((hH_cont.comp (continuous_id.prodMk continuous_const)).continuousAt.sub
      continuousAt_const |>.inv₀ (sub_ne_zero.mpr (hH_avoid t ht_Icc s hs)) |>.continuousWithinAt)
    (((hH_deriv_cont _ _ hp h_avoid_P h_sub_ab).comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun t' ht' => ⟨ht', hs⟩) t ht_in).continuousAt
      (Ioo_mem_nhds ht_in.1 ht_in.2) |>.continuousWithinAt)

private lemma homotopy_integrand_continuousWithinAt_s
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ}
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀)
    (hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1))
    {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0:ℝ) 1)
    {t : ℝ} (ht_Icc : t ∈ Icc a b) (ht_Ioo : t ∈ Ioo a b) (ht_notP : t ∉ P) :
    let f := fun t s => (H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t
    ContinuousWithinAt (fun s => f t s) (Icc 0 1) s₀ := by
  intro f
  obtain ⟨p₁, p₂, hp, ht_in, h_avoid_P, h_sub_ab⟩ :=
    exists_subinterval_avoiding_finset ht_Ioo ht_notP
  exact ContinuousWithinAt.mul
    ((hH_cont.comp (continuous_const.prodMk continuous_id)).continuousAt.sub
      continuousAt_const |>.inv₀
        (sub_ne_zero.mpr (hH_avoid t ht_Icc s₀ hs₀))
      |>.continuousWithinAt)
    (((hH_deriv_cont _ _ hp h_avoid_P h_sub_ab).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨ht_in, hs⟩)) s₀ hs₀)

private lemma homotopy_pv_eq_integral
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {δ : ℝ}
    (hab : a < b) (hδ_pos : 0 < δ)
    (hδ_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, δ ≤ ‖H (t, s) - z₀‖)
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    let f := fun t s => (H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t
    generalizedWindingNumber' (fun t => H (t, s)) a b z₀ =
    (2 * Real.pi * I)⁻¹ * ∫ t in a..b, f t s := by
  intro f
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  simp only [sub_zero]
  congr 1
  apply limUnder_eventually_eq_const
  filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t ht
  rw [Set.uIoc_of_le hab.le] at ht
  simp only [f, ((mem_Ioo.mp hε).2.trans_le (hδ_bound t (Ioc_subset_Icc_self ht) s hs)),
    ↓reduceIte, deriv_sub_const]

private lemma homotopy_piecewise_aestronglyMeasurable
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ}
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀)
    (hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1))
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    let f := fun t s => (H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t
    AEStronglyMeasurable (fun t => f t s) (volume.restrict (Icc a b)) := by
  intro f
  let P' : Finset ℝ := P ∪ {a, b}
  rw [show Icc a b = (Icc a b \ (P' : Set ℝ)) ∪ ((P' : Set ℝ) ∩ Icc a b) by
      rw [Set.inter_comm, Set.diff_union_inter],
    aestronglyMeasurable_union_iff]
  refine ⟨(homotopy_integrand_continuousOn_t hH_cont hH_avoid hH_deriv_cont hs).aestronglyMeasurable
    (measurableSet_Icc.diff (Finset.measurableSet P')), ?_⟩
  rw [Measure.restrict_zero_set
    (((Finset.finite_toSet P').inter_of_left (Icc a b)).measure_zero volume)]
  exact aestronglyMeasurable_zero_measure _

private theorem generalizedWindingNumber'_eq_of_eq_on
    (f g : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (heq_val : ∀ t ∈ Icc a b, f t = g t)
    (heq_deriv : ∀ᵐ t ∂volume.restrict (Set.uIoc a b),
      deriv f t = deriv g t) :
    generalizedWindingNumber' f a b z₀ =
    generalizedWindingNumber' g a b z₀ := by
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  simp only [sub_zero, deriv_sub_const]
  refine congrArg ((2 * Real.pi * I)⁻¹ * limUnder (𝓝[>] 0) ·) (funext fun ε => ?_)
  apply intervalIntegral.integral_congr_ae
  rw [Set.uIoc_of_le hab.le] at heq_deriv ⊢
  rw [ae_restrict_iff' measurableSet_Ioc] at heq_deriv
  filter_upwards [heq_deriv] with t ht ht_mem
  simp only [ht ht_mem, heq_val t (Ioc_subset_Icc_self ht_mem)]

private lemma smooth_winding_integral_continuousOn
    {γ : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {M : ℝ}
    (hab : a < b)
    (hγ_cont : Continuous γ)
    (hγ_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, γ (t, s) ≠ z₀)
    (hγ_deriv_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t' => γ (t', p.2)) p.1))
    (hM : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1,
      ‖(γ (t, s) - z₀)⁻¹ * deriv (fun t' => γ (t', s)) t‖ ≤ M) :
    let f := fun t s => (γ (t, s) - z₀)⁻¹ * deriv (fun t' => γ (t', s)) t
    ContinuousOn (fun s => ∫ t in a..b, f t s) (Icc 0 1) := by
  intro f s₁ hs₁
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hab' : Icc a b = Icc (min a b) (max a b) := by
      simp [min_eq_left hab.le, max_eq_right hab.le]
    refine (ContinuousOn.mul
      (((hγ_cont.comp (continuous_id.prodMk continuous_const)).sub continuous_const).continuousOn
        |>.inv₀ (fun t ht => sub_ne_zero.mpr (hγ_avoid t (hab' ▸ ht) s hs)))
      (hγ_deriv_cont.comp (continuous_id.prodMk continuous_const)).continuousOn
      |>.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards with t ht
    rw [Set.uIoc_of_le hab.le] at ht
    exact hM t (Ioc_subset_Icc_self ht) s hs
  · exact intervalIntegrable_const
  · filter_upwards with t ht
    refine (ContinuousAt.mul (((hγ_cont.comp (continuous_const.prodMk continuous_id)).sub
      continuous_const).continuousAt |>.inv₀ ?_)
      (hγ_deriv_cont.comp (continuous_const.prodMk continuous_id) |>.continuousAt)).continuousWithinAt
    rw [Set.uIoc_of_le hab.le] at ht
    exact sub_ne_zero.mpr (hγ_avoid t (Ioc_subset_Icc_self ht) s₁ hs₁)

/-- When γ avoids z₀, the PV winding number equals the classical contour integral. -/
theorem generalizedWindingNumber_eq_classical_away
    (γ : PiecewiseC1Curve) (z₀ : ℂ) (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) :
    generalizedWindingNumber' γ.toFun γ.a γ.b z₀ =
    (2 * Real.pi * I)⁻¹ * ∫ t in γ.a..γ.b, (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t := by
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  have hδ : 0 < Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b) :=
    ((isCompact_Icc.image_of_continuousOn γ.continuous_toFun).isClosed.notMem_iff_infDist_pos
      (Set.image_nonempty.mpr (Set.nonempty_Icc.mpr γ.hab.le))).mp
      (fun ⟨t, ht, htw⟩ => hoff t ht htw)
  congr 1
  apply limUnder_eventually_eq_const
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t ht
  simp only [sub_zero]
  rw [Set.uIoc_of_le γ.hab.le] at ht
  have ht' : t ∈ Icc γ.a γ.b := Ioc_subset_Icc_self ht
  have hbound : ε < ‖γ.toFun t - z₀‖ := by
    calc ε < Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b) := (mem_Ioo.mp hε).2
      _ ≤ dist z₀ (γ.toFun t) :=
            Metric.infDist_le_dist_of_mem (mem_image_of_mem γ.toFun ht')
      _ = ‖γ.toFun t - z₀‖ := by rw [Complex.dist_eq, norm_sub_rev]
  simp only [hbound, ↓reduceIte, deriv_sub_const]

end
