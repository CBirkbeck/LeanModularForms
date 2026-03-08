/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Residue.MultipointPV

/-!
# Generalized Residue Theorem

Multi-point PV existence and the generalized residue theorem for
piecewise C¹ immersions passing through simple poles.

## Main Results

* `cauchyPrincipalValueOn_singular_sum` — multi-point PV exists when
  each singular term has PV
* `generalizedResidueTheorem'` — CPV equals `2πi · Σ winding · residue`
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

private lemma cpv_crossing_null
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) :
    MeasureTheory.volume
      {t | t ∈ Icc γ.a γ.b ∧
        γ.toFun t ∈ (S0 : Set ℂ)} = 0 := by
  have h_single_null : ∀ s ∈ S0,
      MeasureTheory.volume
        {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t = s} = 0 := by
    intro s _
    exact preimage_singleton_measure_zero_of_deriv_ne_zero
      (P := γ.partition) s
      γ.continuous_toFun γ.smooth_off_partition γ.deriv_ne_zero
  have h_eq :
      {t | t ∈ Icc γ.a γ.b ∧
        γ.toFun t ∈ (S0 : Set ℂ)} =
      ⋃ s ∈ (↑S0 : Set ℂ),
        {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t = s} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion,
      Finset.mem_coe]
    constructor
    · intro ⟨hin, hmem⟩
      exact ⟨γ.toFun t, hmem, hin, rfl⟩
    · intro ⟨s, hs, hin, heq⟩
      exact ⟨hin, heq ▸ hs⟩
  rw [h_eq, MeasureTheory.measure_biUnion_null_iff
    (Set.Finite.countable (Finset.finite_toSet S0))]
  intro s hs
  exact h_single_null s hs

private lemma finset_min_sep (S0 : Finset ℂ)
    (hS0_nonempty : S0.Nonempty) :
    ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0,
      s ≠ s' → δ ≤ ‖s' - s‖ := by
  by_cases h_card_one : S0.card = 1
  · use 1, one_pos
    intro s hs s' hs' hne
    obtain ⟨s₀, hs₀⟩ := Finset.card_eq_one.mp h_card_one
    subst hs₀
    simp only [Finset.mem_singleton] at hs hs'
    rw [hs, hs'] at hne
    exact (hne rfl).elim
  · have h_pos : ∀ s ∈ S0, ∀ s' ∈ S0,
        s ≠ s' → (0 : ℝ) < ‖s' - s‖ :=
      fun _ _ _ _ hne =>
        norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
    have h_exists_pair : ∃ s ∈ S0, ∃ s' ∈ S0, s ≠ s' := by
      obtain ⟨s, hs⟩ := hS0_nonempty
      by_contra h_all_eq
      push_neg at h_all_eq
      have hsub : S0 ⊆ {s} := fun x hx =>
        Finset.mem_singleton.mpr (h_all_eq x hx s hs)
      have h0 : 0 < S0.card :=
        Finset.card_pos.mpr ⟨s, hs⟩
      have := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at this; omega
    obtain ⟨s₁, hs₁, s₂, hs₂, hne₁₂⟩ := h_exists_pair
    have h_finite : (S0 ×ˢ S0 |>.filter
        (fun p => p.1 ≠ p.2) |>.image
          (fun p => ‖p.2 - p.1‖)).Nonempty := by
      refine Finset.Nonempty.image ?_ _
      exact ⟨(s₁, s₂), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hs₁, hs₂⟩, hne₁₂⟩⟩
    obtain ⟨δ, hδ_mem, hδ_min⟩ :=
      Finset.exists_min_image _ id h_finite
    simp only [id] at hδ_min
    have hδ_mem' := Finset.mem_image.mp hδ_mem
    obtain ⟨⟨a, b⟩, hab_mem, hab_eq⟩ := hδ_mem'
    simp only [Finset.mem_filter, Finset.mem_product]
      at hab_mem
    refine ⟨δ, ?_, ?_⟩
    · rw [← hab_eq]
      exact h_pos a hab_mem.1.1 b hab_mem.1.2 hab_mem.2
    · intro s hs s' hs' hne
      exact hδ_min ‖s' - s‖
        (Finset.mem_image.mpr ⟨(s, s'),
          Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hs, hs'⟩, hne⟩,
          rfl⟩)

/-- Multi-point PV exists when each singular term has PV. -/
lemma cauchyPrincipalValueOn_singular_sum
    (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion)
    (_hSimplePoles : ∀ s ∈ S0,
      HasSimplePoleAt f s)
    (hPV_each : ∀ s ∈ S0,
      CauchyPrincipalValueExists'
        (fun z => residueSimplePole f s / (z - s))
        γ.toFun γ.a γ.b s)
    (hg_reg_cont : ContinuousOn
      (fun z => f z - ∑ s ∈ S0,
        residueSimplePole f s / (z - s))
      (γ.toFun '' Icc γ.a γ.b)) :
    CauchyPrincipalValueExistsOn S0 f
      γ.toFun γ.a γ.b := by
  by_cases hS0_empty : S0 = ∅
  · subst hS0_empty
    unfold CauchyPrincipalValueExistsOn
      cauchyPrincipalValueIntegrandOn
    use ∫ t in γ.a..γ.b, f (γ.toFun t) *
      deriv γ.toFun t
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq]
    filter_upwards [self_mem_nhdsWithin] with ε _
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Finset.notMem_empty, false_and,
      exists_false, ↓reduceIte]
  · have hS0_nonempty : S0.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hS0_empty
    obtain ⟨δ, hδ_pos, hδ_sep⟩ :=
      finset_min_sep S0 hS0_nonempty
    unfold CauchyPrincipalValueExistsOn
    have h_limits : ∀ s ∈ S0, ∃ L : ℂ,
        Tendsto (fun ε => ∫ t in γ.a..γ.b,
          if ‖γ.toFun t - s‖ > ε then
            (residueSimplePole f s /
              (γ.toFun t - s)) *
                deriv γ.toFun t
          else 0)
          (𝓝[>] 0) (𝓝 L) :=
      fun s hs => hPV_each s hs
    choose L_fn hL_fn using h_limits
    let L : ℂ := ∑ s ∈ S0.attach,
      L_fn s.val s.property
    have h_sum_tendsto :
        Tendsto (fun ε => ∑ s ∈ S0.attach,
          ∫ t in γ.a..γ.b,
            if ‖γ.toFun t - s.val‖ > ε then
              (residueSimplePole f s.val /
                (γ.toFun t - s.val)) *
                  deriv γ.toFun t
            else 0)
          (𝓝[>] 0) (𝓝 L) := by
      apply tendsto_finset_sum
      intro ⟨s, hs⟩ _
      exact hL_fn s hs
    have h_cauchy :
        Cauchy (Filter.map (fun ε =>
          ∫ t in γ.a..γ.b,
            cauchyPrincipalValueIntegrandOn S0 f
              γ.toFun ε t) (𝓝[>] 0)) := by
      let M := fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 f
          γ.toFun ε t
      let S' := fun ε => ∑ s ∈ S0.attach,
        ∫ t in γ.a..γ.b,
          if ‖γ.toFun t - s.val‖ > ε then
            (residueSimplePole f s.val /
              (γ.toFun t - s.val)) *
                deriv γ.toFun t
          else 0
      let A := fun ε => M ε - S' ε
      let g_reg := fun z => f z - ∑ s ∈ S0,
        residueSimplePole f s / (z - s)
      let G := ∫ t in γ.a..γ.b,
        g_reg (γ.toFun t) * deriv γ.toFun t
      have h_A_tendsto :
          Tendsto A (𝓝[>] 0) (𝓝 G) := by
        have h_crossing_null :=
          cpv_crossing_null S0 γ
        have hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
            f z = g_reg z + ∑ s ∈ S0,
              residueSimplePole f s / (z - s) := by
          intro z _; simp only [g_reg]; ring
        have hS0_sep :
            ∃ δ' > 0, ∀ s ∈ S0, ∀ s' ∈ S0,
              s ≠ s' → δ' ≤ ‖s' - s‖ :=
          ⟨δ, hδ_pos, hδ_sep⟩
        exact multipointPV_diff_tendsto S0 f γ
          h_crossing_null g_reg hg_decomp
          hg_reg_cont hS0_sep
      have h_M_tendsto :
          Tendsto M (𝓝[>] 0) (𝓝 (L + G)) := by
        have h_eq : M = fun ε => S' ε + A ε := by
          ext ε; simp [M, A, S']
        rw [h_eq]
        exact h_sum_tendsto.add h_A_tendsto
      exact h_M_tendsto.cauchy_map
    exact CompleteSpace.complete h_cauchy

/-- Generalized residue theorem: CPV equals `2πi · Σ winding ·
residue` even when γ crosses poles. -/
theorem generalizedResidueTheorem'
    (U : Set ℂ) (hU : IsOpen U)
    (hU_convex : Convex ℝ U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0,
      ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (_hS_closed : IsClosed S)
    (S0 : Finset ℂ)
    (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (_hS_on_curve : ∀ t ∈ Icc γ.a γ.b,
      γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hSimplePoles : ∀ s ∈ S0,
      HasSimplePoleAt f s)
    (hf_ext : ∀ s ∈ S0, ContinuousAt
      (fun z =>
        f z - residueSimplePole f s / (z - s))
      s)
    (hPV_singular : ∀ s ∈ S0,
      CauchyPrincipalValueExists'
        (fun z =>
          residueSimplePole f s / (z - s))
        γ.toFun γ.a γ.b s) :
    CauchyPrincipalValueExistsOn S0 f
      γ.toFun γ.a γ.b ∧
    cauchyPrincipalValueOn S0 f
      γ.toFun γ.a γ.b =
      2 * Real.pi * I *
        ∑ s ∈ S0,
          generalizedWindingNumber' γ.toFun
            γ.a γ.b s *
            residueSimplePole f s := by
  have hS0_in_U : ∀ s ∈ S0, s ∈ U :=
    fun s hs => hS_in_U s (hS0_subset s hs)
  have hS0_discrete' :
      ∀ s ∈ S0, ∀ s' ∈ S0,
        s ≠ s' → 0 < ‖s' - s‖ := by
    intro s hs s' hs' hne
    obtain ⟨ε, hε_pos, hε_sep⟩ :=
      hS_discrete s (hS0_subset s hs)
    exact lt_of_lt_of_le hε_pos
      (hε_sep s' (hS0_subset s' hs') (Ne.symm hne))
  have h_decomp :=
    simple_poles_decomposition U hU S0 hS0_in_U f
      hf hSimplePoles hf_ext
  let g := fun z => f z - ∑ s ∈ S0,
    residueSimplePole f s / (z - s)
  have hg_diff : DifferentiableOn ℂ g U := h_decomp.1
  have hg_cont_on_image :
      ContinuousOn g
        (γ.toFun '' Icc γ.a γ.b) := by
    apply hg_diff.continuousOn.mono
    intro z ⟨t, ht, htz⟩
    rw [← htz]; exact hγ_in_U t ht
  constructor
  · by_cases h_avoids :
        ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b,
          γ.toFun t ≠ s
    · exact cauchyPrincipalValueExistsOn_avoids S0 f
        γ.toPiecewiseC1Curve h_avoids
    · push_neg at h_avoids
      exact cauchyPrincipalValueOn_singular_sum S0 f
        γ hSimplePoles hPV_singular hg_cont_on_image
  · by_cases h_avoids :
        ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b,
          γ.toFun t ≠ s
    · rw [cauchyPrincipalValueOn_avoids S0 f
        γ.toPiecewiseC1Curve h_avoids]
      exact integral_eq_sum_residues_of_avoids U hU
        hU_convex S0 hS0_in_U f hf
        γ.toPiecewiseC1Curve hγ_closed hγ_in_U
        h_avoids hSimplePoles hf_ext
        (piecewiseC1Immersion_deriv_bounded γ)
    · push_neg at h_avoids
      have hg_integral_zero :
          ∫ t in γ.a..γ.b,
            g (γ.toFun t) * deriv γ.toFun t = 0 := by
        have hU_ne : U.Nonempty :=
          ⟨γ.toFun γ.a, hγ_in_U γ.a
            (left_mem_Icc.mpr (le_of_lt γ.hab))⟩
        obtain ⟨F, hF⟩ :=
          holomorphic_convex_primitive hU_convex hU
            hU_ne hg_diff
        have h_Fγ_cont :
            ContinuousOn (F ∘ γ.toFun)
              (Icc γ.a γ.b) := by
          intro t ht
          have hFcont : ContinuousAt F (γ.toFun t) :=
            (hF (γ.toFun t) (hγ_in_U t ht)).continuousAt
          exact hFcont.continuousWithinAt.comp
            (γ.continuous_toFun t ht)
            (mapsTo_image γ.toFun _)
        have h_deriv :
            ∀ t ∈ Ioo γ.a γ.b,
              t ∉ γ.partition →
                HasDerivAt (F ∘ γ.toFun)
                  (g (γ.toFun t) *
                    deriv γ.toFun t) t := by
          intro t ht hp
          have ht' : t ∈ Icc γ.a γ.b :=
            Ioo_subset_Icc_self ht
          exact (hF (γ.toFun t)
            (hγ_in_U t ht')).comp_of_eq t
              ((γ.smooth_off_partition t ht' hp).hasDerivAt)
              rfl
        have h_countable :
            (↑γ.partition ∩ Ioo γ.a γ.b :
              Set ℝ).Countable :=
          (γ.partition.finite_toSet.inter_of_left
            _).countable
        have h_deriv' :
            ∀ t ∈ Ioo γ.a γ.b \
              (↑γ.partition ∩ Ioo γ.a γ.b),
                HasDerivAt (F ∘ γ.toFun)
                  (g (γ.toFun t) *
                    deriv γ.toFun t) t := by
          intro t ⟨ht, hp⟩
          exact h_deriv t ht (fun h => hp ⟨h, ht⟩)
        have h_int :
            IntervalIntegrable
              (fun t => g (γ.toFun t) *
                deriv γ.toFun t)
              MeasureTheory.volume γ.a γ.b := by
          have hgγ_cont :
              ContinuousOn (fun t => g (γ.toFun t))
                (Set.uIcc γ.a γ.b) := by
            rw [Set.uIcc_of_le (le_of_lt γ.hab)]
            exact hg_cont_on_image.comp
              γ.continuous_toFun
              (Set.mapsTo_image γ.toFun (Icc γ.a γ.b))
          exact IntervalIntegrable.continuousOn_mul
            (piecewiseC1_deriv_intervalIntegrable
              γ.toPiecewiseC1Curve
              (piecewiseC1Immersion_deriv_bounded γ))
            hgγ_cont
        have h_ftc :=
          MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
            (F ∘ γ.toFun)
            (fun t => g (γ.toFun t) *
              deriv γ.toFun t)
            (le_of_lt γ.hab)
            h_countable h_Fγ_cont h_deriv' h_int
        rw [h_ftc, Function.comp_apply,
          Function.comp_apply,
          (hγ_closed : γ.toFun γ.a = γ.toFun γ.b),
          sub_self]
      have h_single_pole_formula : ∀ s ∈ S0,
          cauchyPrincipalValue'
            (fun z =>
              residueSimplePole f s / (z - s))
            γ.toFun γ.a γ.b s =
          2 * Real.pi * I *
            generalizedWindingNumber' γ.toFun
              γ.a γ.b s *
            residueSimplePole f s := by
        intro s hs
        by_cases hc : residueSimplePole f s = 0
        · simp only [hc, zero_div, mul_zero]
          unfold cauchyPrincipalValue'
          simp only [zero_mul]
          apply limUnder_eventually_eq_const
          filter_upwards with ε
          have h_zero : ∀ t,
              (if ‖γ.toFun t - s‖ > ε
                then (0 : ℂ) else 0) = 0 := by
            intro t; split_ifs <;> rfl
          simp_rw [h_zero]
          simp only [intervalIntegral.integral_const,
            smul_zero]
        · have hPV_s := hPV_singular s hs
          obtain ⟨L, hL⟩ := hPV_s
          have h_base_pv_exists :
              ∃ L', Tendsto (fun ε =>
                ∫ t in γ.a..γ.b,
                  if ‖(fun t' => γ.toFun t' - s)
                      t - 0‖ > ε
                  then (·⁻¹)
                    ((fun t' => γ.toFun t' - s) t) *
                      deriv
                        (fun t' => γ.toFun t' - s) t
                  else 0)
                (𝓝[>] 0) (𝓝 L') := by
            use L / residueSimplePole f s
            have h_simp_deriv : ∀ t,
                deriv (fun t' => γ.toFun t' - s) t =
                  deriv γ.toFun t := by
              intro t; simp only [deriv_sub_const]
            have h_simp_norm : ∀ t,
                ‖(fun t' => γ.toFun t' - s) t - 0‖ =
                  ‖γ.toFun t - s‖ := by
              intro t; simp
            have h_int_eq : ∀ ε,
                (∫ t in γ.a..γ.b,
                  if ‖(fun t' => γ.toFun t' - s)
                      t - 0‖ > ε
                  then (·⁻¹)
                    ((fun t' => γ.toFun t' - s) t) *
                      deriv
                        (fun t' => γ.toFun t' - s) t
                  else 0) =
                (∫ t in γ.a..γ.b,
                  if ‖γ.toFun t - s‖ > ε
                  then (γ.toFun t - s)⁻¹ *
                    deriv γ.toFun t
                  else 0) := by
              intro ε
              apply intervalIntegral.integral_congr
              intro t _
              simp only [h_simp_norm, h_simp_deriv]
            simp only [h_int_eq]
            let c := residueSimplePole f s
            have h_int_factor : ∀ ε,
                (∫ t in γ.a..γ.b,
                  if ‖γ.toFun t - s‖ > ε
                  then (c / (γ.toFun t - s)) *
                    deriv γ.toFun t
                  else 0) =
                c * (∫ t in γ.a..γ.b,
                  if ‖γ.toFun t - s‖ > ε
                  then (γ.toFun t - s)⁻¹ *
                    deriv γ.toFun t
                  else 0) := by
              intro ε
              rw [← smul_eq_mul,
                ← intervalIntegral.integral_smul]
              apply intervalIntegral.integral_congr
              intro t _
              simp only [smul_ite, smul_zero]
              congr 1
              simp only [smul_eq_mul, div_eq_mul_inv,
                mul_comm c, mul_assoc]
            have hL' :
                Tendsto (fun ε => c * ∫ t in γ.a..γ.b,
                  if ‖γ.toFun t - s‖ > ε
                  then (γ.toFun t - s)⁻¹ *
                    deriv γ.toFun t
                  else 0) (𝓝[>] 0) (𝓝 L) := by
              convert hL using 1
              ext ε; exact (h_int_factor ε).symm
            have hc' : c ≠ 0 := hc
            have h_scaled := hL'.const_mul c⁻¹
            convert h_scaled using 1
            · ext ε
              simp only [inv_mul_cancel_left₀ hc']
            · congr 1; field_simp [hc']; rfl
          exact pv_integral_simple_pole
            γ.toPiecewiseC1Curve s
            (residueSimplePole f s)
            h_base_pv_exists
      have h_multipoint_eq_sum :
          cauchyPrincipalValueOn S0 f
            γ.toFun γ.a γ.b =
          ∑ s ∈ S0,
            cauchyPrincipalValue'
              (fun z =>
                residueSimplePole f s / (z - s))
              γ.toFun γ.a γ.b s := by
        have h_crossing_null := cpv_crossing_null S0 γ
        have hPV_exists :
            CauchyPrincipalValueExistsOn S0 f
              γ.toFun γ.a γ.b :=
          cauchyPrincipalValueOn_singular_sum S0 f γ
            hSimplePoles hPV_singular
            hg_cont_on_image
        have hPV_each_tendsto :
            Tendsto (fun ε => ∑ s ∈ S0,
              ∫ t in γ.a..γ.b,
                if ‖γ.toFun t - s‖ > ε
                then (residueSimplePole f s /
                  (γ.toFun t - s)) *
                    deriv γ.toFun t
                else 0)
              (𝓝[>] 0)
              (𝓝 (∑ s ∈ S0,
                cauchyPrincipalValue'
                  (fun z =>
                    residueSimplePole f s / (z - s))
                  γ.toFun γ.a γ.b s)) := by
          apply tendsto_finset_sum
          intro s hs
          obtain ⟨Ls, hLs⟩ := hPV_singular s hs
          have h_eq_L :
              cauchyPrincipalValue'
                (fun z =>
                  residueSimplePole f s / (z - s))
                γ.toFun γ.a γ.b s = Ls := by
            unfold cauchyPrincipalValue'
            exact hLs.limUnder_eq
          rw [h_eq_L]; exact hLs
        have hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
            f z = g z + ∑ s ∈ S0,
              residueSimplePole f s / (z - s) := by
          intro z _; simp only [g]; ring
        have hS0_sep :
            ∃ δ' > 0, ∀ s ∈ S0, ∀ s' ∈ S0,
              s ≠ s' → δ' ≤ ‖s' - s‖ := by
          by_cases hS0_card : S0.card ≤ 1
          · use 1, one_pos
            intro s hs s' hs' hne
            exact absurd
              (Finset.card_le_one_iff.mp hS0_card
                hs hs') hne
          · push_neg at hS0_card
            exact finset_min_sep S0
              (Finset.card_pos.mp (by omega))
        exact multipointPV_eq_sum_of_integral_zero
          S0 f γ h_crossing_null g hg_decomp
          hg_cont_on_image hS0_sep hg_integral_zero
          hPV_exists hPV_each_tendsto
      calc cauchyPrincipalValueOn S0 f
            γ.toFun γ.a γ.b
          = ∑ s ∈ S0, cauchyPrincipalValue'
              (fun z =>
                residueSimplePole f s / (z - s))
              γ.toFun γ.a γ.b s :=
            h_multipoint_eq_sum
        _ = ∑ s ∈ S0, (2 * Real.pi * I *
              generalizedWindingNumber' γ.toFun
                γ.a γ.b s *
              residueSimplePole f s) := by
            apply Finset.sum_congr rfl
            intro s hs
            exact h_single_pole_formula s hs
        _ = 2 * Real.pi * I *
              ∑ s ∈ S0,
                generalizedWindingNumber' γ.toFun
                  γ.a γ.b s *
                residueSimplePole f s := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s _; ring

end
