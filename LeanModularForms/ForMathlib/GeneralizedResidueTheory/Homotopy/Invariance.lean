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

private theorem windingNumber_continuousOn_param_piecewise_with_bound
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ} {M : ℝ} (hab : a < b)
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀)
    (hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1))
    (hM_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1,
      ‖deriv (fun t' => H (t', s)) t‖ ≤ M) :
    ContinuousOn (fun s => generalizedWindingNumber' (fun t => H (t, s)) a b z₀) (Icc 0 1) := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := homotopy_uniform_avoidance H a b z₀ hab hH_cont hH_avoid
  have h_pv := fun s hs => homotopy_pv_eq_integral hab hδ_pos hδ_bound s hs
  intro s₀ hs₀
  apply ContinuousWithinAt.congr_of_eventuallyEq _
    (eventually_of_mem self_mem_nhdsWithin h_pv) (h_pv s₀ hs₀)
  apply continuousWithinAt_const.mul
  apply continuousWithinAt_integral_of_dominated_piecewise (M := M / δ) hab.le
  · exact fun s hs => homotopy_piecewise_aestronglyMeasurable hH_cont hH_avoid hH_deriv_cont s hs
  · exact fun s hs t ht =>
      winding_integrand_bounded_of_uniform_avoidance hδ_pos hδ_bound hM_bound t ht s hs
  · have h_ae_not_B : ∀ᵐ t ∂(volume.restrict (Icc a b)),
        t ∉ (({a, b} ∪ (P : Set ℝ)) : Set ℝ) := by
      rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
      simp only [Set.setOf_and, Classical.not_imp, not_not]
      exact measure_mono_null Set.inter_subset_right
        (((Set.finite_insert.mpr (Set.finite_singleton b)).union
          (Finset.finite_toSet P)).measure_zero _)
    filter_upwards [h_ae_not_B, ae_restrict_mem measurableSet_Icc] with t ht_notB ht_Icc
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_notB
    exact homotopy_integrand_continuousWithinAt_s hH_cont hH_avoid hH_deriv_cont hs₀ ht_Icc
      ⟨lt_of_le_of_ne ht_Icc.1 (Ne.symm ht_notB.1.1),
       lt_of_le_of_ne ht_Icc.2 ht_notB.1.2⟩ ht_notB.2

private theorem continuous_integer_valued_constant
    (f : ℝ → ℂ) (hf_cont : ContinuousOn f (Icc (0:ℝ) 1))
    (hf_int : ∀ s ∈ Icc (0:ℝ) 1, ∃ n : ℤ, f s = n) :
    f 0 = f 1 := by
  let g : Icc (0:ℝ) 1 → ℂ := fun x => f x.val
  have hg_loc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    by_cases hy : ∃ n : ℤ, y = n
    · obtain ⟨n, rfl⟩ := hy
      have heq : g ⁻¹' {↑n} = g ⁻¹' (Metric.ball (n : ℂ) 1) := by
        ext ⟨x, hx⟩
        simp only [g, mem_preimage, mem_singleton_iff, Metric.mem_ball]
        refine ⟨fun h => h ▸ by simp, fun hdist => ?_⟩
        obtain ⟨m, hm⟩ := hf_int x hx
        rw [hm, Complex.dist_eq, ← Int.cast_sub, Complex.norm_intCast, ← Int.cast_abs] at hdist
        rw [hm]
        exact_mod_cast sub_eq_zero.mp (Int.abs_lt_one_iff.mp (by exact_mod_cast hdist))
      rw [heq]
      exact hf_cont.restrict.isOpen_preimage _ Metric.isOpen_ball
    · convert isOpen_empty
      ext ⟨x, hx⟩
      simp only [g, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact fun heq => hy ⟨_, heq.symm.trans (hf_int x hx).choose_spec⟩
  exact hg_loc.apply_eq_of_isPreconnected (x := ⟨0, by norm_num⟩) (y := ⟨1, by norm_num⟩)
    isPreconnected_univ trivial trivial

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

/-- If `H (·, s₀) = γ` on `Icc a b`, then the generalized winding number along
`(t ↦ H (t, s₀))` equals that along `γ`. -/
private lemma generalizedWindingNumber'_eq_of_homotopy_slice
    (H : ℝ × ℝ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (s₀ : ℝ) (hab : a < b)
    (hHs : ∀ t ∈ Icc a b, H (t, s₀) = γ t) :
    generalizedWindingNumber' (fun t => H (t, s₀)) a b z₀ =
    generalizedWindingNumber' γ a b z₀ := by
  apply generalizedWindingNumber'_eq_of_eq_on (fun t => H (t, s₀)) γ a b z₀ hab hHs
  rw [Set.uIoc_of_le hab.le, ae_restrict_iff' measurableSet_Ioc]
  have h_eq_on_Ioo : Set.EqOn (fun t => H (t, s₀)) γ (Ioo a b) :=
    fun t' ht' => hHs t' (Ioo_subset_Icc_self ht')
  filter_upwards [Ioo_ae_eq_Ioc.mem_iff] with t ht ht_Ioc
  exact (h_eq_on_Ioo.deriv isOpen_Ioo) (ht.mpr ht_Ioc)

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

private theorem windingNumber_continuous_in_param
    (γ : ℝ × ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b) (hγ_cont : Continuous γ)
    (hγ_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, γ (t, s) ≠ z₀)
    (hγ_deriv_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t' => γ (t', p.2)) p.1)) :
    ContinuousOn (fun s => generalizedWindingNumber' (fun t => γ (t, s)) a b z₀) (Icc 0 1) := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := homotopy_uniform_avoidance γ a b z₀ hab hγ_cont hγ_avoid
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn <|
    ContinuousOn.mul
      (ContinuousOn.inv₀ (hγ_cont.sub continuous_const).continuousOn
        (fun ⟨t, s⟩ ⟨ht, hs⟩ => sub_ne_zero.mpr (hγ_avoid t ht s hs)))
      hγ_deriv_cont.continuousOn
  have h_pv := fun s hs => homotopy_pv_eq_integral hab hδ_pos hδ_bound s hs
  intro s₀ hs₀
  apply ContinuousWithinAt.congr_of_eventuallyEq _
    (eventually_of_mem self_mem_nhdsWithin h_pv) (h_pv s₀ hs₀)
  exact continuousWithinAt_const.mul
    ((smooth_winding_integral_continuousOn hab hγ_cont hγ_avoid hγ_deriv_cont
      (fun t ht s hs => hM (t, s) ⟨ht, hs⟩)).continuousWithinAt hs₀)

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

private lemma integral_congr_homotopy_endpoint
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {H : ℝ × ℝ → ℂ} {a b : ℝ} {s : ℝ}
    (hab : a < b)
    (hHs : ∀ t ∈ Icc a b, H (t, s) = γ t) :
    ∫ t in a..b, f (γ t) * deriv γ t =
    ∫ t in a..b, f (H (t, s)) * deriv (fun t => H (t, s)) t := by
  apply intervalIntegral.integral_congr_ae
  have h_eq : Set.EqOn (fun t => H (t, s)) γ (Ioo a b) :=
    fun t' ht' => hHs t' (Ioo_subset_Icc_self ht')
  simp only [Set.uIoc_of_le hab.le]
  filter_upwards [Ioo_ae_eq_Ioc.mem_iff] with t ht ht_Ioc
  have ht_Ioo : t ∈ Ioo a b := ht.mpr ht_Ioc
  rw [hHs t (Ioo_subset_Icc_self ht_Ioo), (h_eq.deriv isOpen_Ioo) ht_Ioo]

end
