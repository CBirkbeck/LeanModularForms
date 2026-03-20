/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Residue.MultipointPV
import LeanModularForms.GeneralizedResidueTheory.Residue.Flatness
import LeanModularForms.GeneralizedResidueTheory.Residue.SectorCurveLemma
import LeanModularForms.GeneralizedResidueTheory.WindingNumber.Proposition2_2
import Mathlib.Analysis.Meromorphic.Order

/-!
# Generalized Residue Theorem

Multi-point PV existence and the generalized residue theorem for
piecewise C¹ immersions passing through poles.

## Main Results

* `cauchyPrincipalValueOn_singular_sum` — multi-point PV exists when
  each singular term has PV
* `generalizedResidueTheorem'` — CPV equals `2πi · Σ winding · residue`
* `generalizedResidueTheorem` — clean version for simple poles (no PV hypothesis)
* `generalizedResidueTheorem_higher_order` — full generality with `MeromorphicAt`
  and conditions (A)/(B) for higher-order poles
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

/-- If PV of f exists, then PV of c * f exists (scaling by constant). -/
lemma CauchyPrincipalValueExists'.const_mul
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} (c : ℂ)
    (h : CauchyPrincipalValueExists' f γ a b z₀) :
    CauchyPrincipalValueExists' (fun z => c * f z) γ a b z₀ := by
  obtain ⟨L, hL⟩ := h
  refine ⟨c * L, ?_⟩
  have h_eq : ∀ ε, (∫ t in a..b, if ‖γ t - z₀‖ > ε then (c * f (γ t)) * deriv γ t else 0) =
      c * (∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) := by
    intro ε
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext t
    split_ifs <;> ring
  exact (hL.const_mul c).congr (fun ε => (h_eq ε).symm)

/-- **Generalized Residue Theorem** (Hungerbühler-Wasem, Theorem 3.3).

CPV of `f` along a piecewise C¹ immersion equals `2πi · Σ winding · residue`,
even when the curve passes through simple poles. Unlike `generalizedResidueTheorem'`,
this version does NOT require `CauchyPrincipalValueExists'` as a hypothesis —
PV existence is proved from the immersion structure + C² regularity at crossings.

The hypotheses `hγ_meas`, `h_no_endpt_cross`, `hC2_cross`, and `h_cont_deriv_cross`
replace the old `hPV_singular`. These are satisfied by any "reasonable" curve:
- Measurability follows from global continuity
- No endpoint crossings holds when poles are interior to the curve
- C² at crossings holds for piecewise smooth curves
- Continuous derivative near crossings follows from C² -/
theorem generalizedResidueTheorem
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S)
    (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hf_ext : ∀ s ∈ S0, ContinuousAt (fun z => f z - residueSimplePole f s / (z - s)) s)
    -- New regularity hypotheses (replace hPV_singular):
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (hC2_cross : ∀ s ∈ S0, ∀ t ∈ Ioo γ.a γ.b, γ.toFun t = s →
      ContDiffAt ℝ 2 γ.toFun t)
    (h_cont_deriv_cross : ∀ s ∈ S0, ∀ t ∈ Ioo γ.a γ.b, γ.toFun t = s →
      ∃ a' b', t ∈ Ioo a' b' ∧ Icc a' b' ⊆ Icc γ.a γ.b ∧
        ContinuousOn (deriv γ.toFun) (Icc a' b')) :
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueSimplePole f s := by
  -- Derive hPV_singular: PV of c/(z-s) exists for each s ∈ S0
  have hPV_singular : ∀ s ∈ S0, CauchyPrincipalValueExists'
      (fun z => residueSimplePole f s / (z - s)) γ.toFun γ.a γ.b s := by
    intro s hs
    have h_inv := cpv_exists_inv_sub γ s hγ_meas
      (h_no_endpt_cross s hs) (hC2_cross s hs) (h_cont_deriv_cross s hs)
    have h_eq : (fun z => residueSimplePole f s / (z - s)) =
        (fun z => residueSimplePole f s * (fun z => (z - s)⁻¹) z) := by
      ext z; simp [div_eq_mul_inv]
    rw [h_eq]; exact h_inv.const_mul (residueSimplePole f s)
  exact (generalizedResidueTheorem' U hU hU_convex S hS_in_U hS_discrete hS_closed
    S0 hS0_subset f hf γ hγ_closed hγ_in_U hS_on_curve hSimplePoles hf_ext hPV_singular).2

/-! ### General residue and the higher-order theorem -/

/-- Residue of `f` at `z₀` via contour integral:
`Res(f, z₀) = lim_{r→0⁺} (2πi)⁻¹ ∮_{|z-z₀|=r} f(z) dz`.

This is well-defined for meromorphic functions and agrees with
`residueSimplePole` when `f` has a simple pole at `z₀`. -/
def residueAt (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun r =>
    (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(z₀, r), f z

/-- If `f` has a simple pole at `z₀` with decomposition `c / (z - z₀) + g`,
then `residueSimplePole f z₀ = c`. -/
theorem residueSimplePole_eq_of_decomposition (f : ℂ → ℂ) (z₀ c : ℂ) (g : ℂ → ℂ)
    (hg : AnalyticAt ℂ g z₀)
    (hf_eq : ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z) :
    residueSimplePole f z₀ = c := by
  unfold residueSimplePole
  apply Filter.Tendsto.limUnder_eq
  have h_sub : Tendsto (fun z => z - z₀) (𝓝[≠] z₀) (𝓝 0) := by
    rw [show (0 : ℂ) = z₀ - z₀ from (sub_self z₀).symm]
    exact tendsto_nhdsWithin_of_tendsto_nhds
      (continuous_id.sub continuous_const).continuousAt.tendsto
  have h_g : Tendsto g (𝓝[≠] z₀) (𝓝 (g z₀)) :=
    hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h_prod : Tendsto (fun z => (z - z₀) * g z) (𝓝[≠] z₀) (𝓝 0) := by
    have := h_sub.mul h_g; simp only [zero_mul] at this; exact this
  have h_ev : ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) * f z = c + (z - z₀) * g z := by
    filter_upwards [hf_eq, self_mem_nhdsWithin] with z hz hne
    rw [hz, mul_add, mul_div_cancel₀ _ (sub_ne_zero.mpr hne)]
  have h_tend : Tendsto (fun z => c + (z - z₀) * g z) (𝓝[≠] z₀) (𝓝 c) := by
    have := (tendsto_const_nhds (x := c)).add h_prod; rwa [add_zero] at this
  exact h_tend.congr' (h_ev.mono fun _ hz => hz.symm)

/-- For simple poles, `residueAt` agrees with `residueSimplePole`. -/
theorem residueAt_eq_residueSimplePole (f : ℂ → ℂ) (z₀ : ℂ)
    (hf : HasSimplePoleAt f z₀) :
    residueAt f z₀ = residueSimplePole f z₀ := by
  obtain ⟨c, g, hg_analytic, hf_eq⟩ := hf
  have h_simple : residueSimplePole f z₀ = c :=
    residueSimplePole_eq_of_decomposition f z₀ c g hg_analytic hf_eq
  have h_contour : residueAt f z₀ = c := by
    unfold residueAt
    apply Filter.Tendsto.limUnder_eq
    -- Get a ball where g is analytic (hence differentiable and continuous)
    obtain ⟨rg, hrg_pos, hg_ball⟩ := hg_analytic.exists_ball_analyticOnNhd
    -- Get a punctured ball where f = c/(z-z₀) + g
    rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hf_eq
    obtain ⟨rf, hrf_pos, hrf_eq⟩ := hf_eq
    -- For r < min(rg, rf), the circle is inside both balls
    have hr₀_pos : 0 < min rg rf := lt_min hrg_pos hrf_pos
    apply tendsto_nhds_of_eventually_eq
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hr₀_pos] with r hr_lt hr_pos
    simp only [Set.mem_Ioi] at hr_pos
    simp only [Set.mem_Iio] at hr_lt
    have hr_lt_rg : r < rg := lt_of_lt_of_le hr_lt (min_le_left _ _)
    have hr_lt_rf : r < rf := lt_of_lt_of_le hr_lt (min_le_right _ _)
    have hr_ne : r ≠ 0 := ne_of_gt hr_pos
    -- f = c/(z-z₀) + g on sphere z₀ r (all points ≠ z₀)
    have h_eq_on : Set.EqOn f (fun z => c * (z - z₀)⁻¹ + g z) (Metric.sphere z₀ r) := by
      intro z hz
      have h_ne : z ≠ z₀ := by
        intro heq; rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
      have h_in : dist z z₀ < rf := by
        rw [Metric.mem_sphere.mp hz]; exact hr_lt_rf
      have h_mem : z ∈ Metric.ball z₀ rf ∩ {z₀}ᶜ :=
        ⟨Metric.mem_ball.mpr h_in, Set.mem_compl_singleton_iff.mpr h_ne⟩
      have := hrf_eq h_mem
      simp only [Set.mem_setOf_eq] at this
      rw [this, div_eq_mul_inv]
    -- CircleIntegrable for each term
    have h_g_cont : ContinuousOn g (Metric.closedBall z₀ r) :=
      hg_ball.continuousOn.mono (Metric.closedBall_subset_ball hr_lt_rg)
    have h_ci_g : CircleIntegrable g z₀ r :=
      (h_g_cont.mono Metric.sphere_subset_closedBall).circleIntegrable hr_pos.le
    have h_ci_inv : CircleIntegrable (fun z => (z - z₀)⁻¹) z₀ r :=
      circleIntegrable_sub_inv_iff.mpr (Or.inr (by
        rw [Metric.mem_sphere, dist_self, abs_of_pos hr_pos]; exact hr_ne.symm))
    have h_ci_cinv : CircleIntegrable (fun z => c * (z - z₀)⁻¹) z₀ r :=
      h_ci_inv.const_fun_smul
    -- ∮ f = c * ∮ (z-z₀)⁻¹ + ∮ g
    have h_int_eq : (∮ z in C(z₀, r), f z) =
        c * (∮ z in C(z₀, r), (z - z₀)⁻¹) + (∮ z in C(z₀, r), g z) := by
      rw [circleIntegral.integral_congr hr_pos.le h_eq_on,
        circleIntegral.integral_add h_ci_cinv h_ci_g,
        circleIntegral.integral_const_mul]
    -- ∮ (z-z₀)⁻¹ = 2πi, ∮ g = 0
    rw [h_int_eq,
      circleIntegral.integral_sub_center_inv z₀ hr_ne,
      circleIntegral_eq_zero_of_differentiable_on_off_countable hr_pos.le
        Set.countable_empty h_g_cont
        (fun z ⟨hz, _⟩ => (hg_ball z (Metric.ball_subset_ball hr_lt_rg.le hz)).differentiableAt),
      add_zero]
    have h2pi_ne : (2 : ℂ) * ↑Real.pi * I ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    field_simp
  rw [h_simple, h_contour]

/-! ### Helper lemmas for the higher-order theorem

These lemmas establish properties of the "pure residue function"
`f_res(z) = Σ_{s ∈ S0} c(s) / (z - s)`, which is used to reduce the
higher-order residue theorem to the simple-pole case. -/

/-- The sum `∑ s ∈ S0, c(s) / (z - s)` has a simple pole at each `s ∈ S0`,
with coefficient `c(s)` and analytic remainder `∑ s' ∈ S0.erase s, c(s') / (z - s')`. -/
lemma hasSimplePoleAt_sum_div_sub (S0 : Finset ℂ) (c : ℂ → ℂ)
    (s : ℂ) (hs : s ∈ S0) :
    HasSimplePoleAt (fun z => ∑ s' ∈ S0, c s' / (z - s')) s := by
  refine ⟨c s, fun z => ∑ s' ∈ S0.erase s, c s' / (z - s'), ?_, ?_⟩
  · -- Remainder is analytic at s: each c(s')/(z-s') with s' ≠ s is analytic at s
    exact (S0.erase s).analyticAt_fun_sum fun s' hs' =>
      analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hs')))
  · -- Decomposition: Σ_{S0} = c(s)/(z-s) + Σ_{S0.erase s}
    filter_upwards [self_mem_nhdsWithin] with z _hz
    exact (Finset.add_sum_erase S0 (fun s' => c s' / (z - s')) hs).symm

/-- The sum `∑ s ∈ S0, c(s) / (z - s)` is differentiable on `U \ S0`. -/
lemma differentiableOn_sum_div_sub (S0 : Finset ℂ) (c : ℂ → ℂ) (U : Set ℂ) :
    DifferentiableOn ℂ (fun z => ∑ s ∈ S0, c s / (z - s)) (U \ ↑S0) := by
  apply DifferentiableOn.fun_sum
  intro s hs
  exact DifferentiableOn.div (differentiableOn_const _)
    (differentiableOn_id.sub (differentiableOn_const s))
    (fun z ⟨_, hz⟩ => sub_ne_zero.mpr (ne_of_mem_of_not_mem (Finset.mem_coe.mpr hs) hz).symm)

/-- The residue of `∑ s ∈ S0, c(s) / (z - s)` at `s` equals `c(s)`.
This follows from the HasSimplePoleAt decomposition. -/
lemma residueSimplePole_sum_div_sub (S0 : Finset ℂ) (c : ℂ → ℂ)
    (s : ℂ) (hs : s ∈ S0) :
    residueSimplePole (fun z => ∑ s' ∈ S0, c s' / (z - s')) s = c s := by
  apply residueSimplePole_eq_of_decomposition _ s (c s)
    (fun z => ∑ s' ∈ S0.erase s, c s' / (z - s'))
  · exact (S0.erase s).analyticAt_fun_sum fun s' hs' =>
      analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hs')))
  · filter_upwards [self_mem_nhdsWithin] with z _hz
    exact (Finset.add_sum_erase S0 (fun s' => c s' / (z - s')) hs).symm

/-- `ContinuousAt` of the remainder `(∑ c(s')/(z-s')) - c(s)/(z-s)` at `s`.
This is the `hf_ext` condition needed by the simple-pole theorem. -/
lemma continuousAt_sum_remainder (S0 : Finset ℂ) (c : ℂ → ℂ)
    (s : ℂ) (hs : s ∈ S0) :
    ContinuousAt (fun z => (∑ s' ∈ S0, c s' / (z - s')) -
      residueSimplePole (fun z => ∑ s' ∈ S0, c s' / (z - s')) s / (z - s)) s := by
  rw [residueSimplePole_sum_div_sub S0 c s hs]
  -- Need: ContinuousAt (fun z => Σ_{full} - c(s)/(z-s)) s
  -- This equals ContinuousAt (fun z => Σ_{S0.erase s} c(s')/(z-s')) s
  have h_rem : (fun z => (∑ s' ∈ S0, c s' / (z - s')) - c s / (z - s)) =
      (fun z => ∑ s' ∈ S0.erase s, c s' / (z - s')) := by
    funext z; rw [← Finset.add_sum_erase S0 (fun s' => c s' / (z - s')) hs]; ring
  rw [h_rem]
  exact ((S0.erase s).analyticAt_fun_sum (𝕜 := ℂ) fun s' hs' =>
    analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hs')))).continuousAt

set_option maxHeartbeats 400000 in
/-- **Generalized Residue Theorem for higher-order poles**
(Hungerbühler-Wasem, Theorem 3.3, full generality).

For a meromorphic function `f` with poles of arbitrary order on a closed
piecewise C¹ immersion, the Cauchy principal value equals
`2πi · Σ n(γ, zₗ) · Res(f, zₗ)`, provided the higher-order cancellation
hypothesis holds: the multi-point PV of `f` and its pure residue function
`f_res(z) = Σ Res(f,s)/(z-s)` agree in the limit.

This cancellation is the mathematical consequence of conditions (A) (flatness)
and (B) (angle/Laurent compatibility) from the paper:
- **(A)** At each pole `s` of order `n` on the curve, γ is flat of order `n`.
- **(B)** The crossing angle `α = pπ/q`, and Laurent coefficients satisfy
  compatibility with the angle.

For simple poles, the cancellation is automatic since `f - f_res` extends
holomorphically, recovering `generalizedResidueTheorem` as a special case. -/
theorem generalizedResidueTheorem_higher_order
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S)
    (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    -- Meromorphic at each pole (replaces HasSimplePoleAt):
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    -- Higher-order cancellation: the multi-point PV difference between f and its
    -- pure residue function f_res(z) = Σ Res(f,s)/(z-s) tends to 0.
    -- This is the consequence of conditions (A) (flatness) and (B) (angle/Laurent
    -- compatibility) from Hungerbühler-Wasem Theorem 3.3: flatness ensures the
    -- radial PV contributions cancel, angle/Laurent compatibility ensures the
    -- arc contributions vanish for higher-order singular terms.
    (hHigherOrderCancel : Tendsto
      (fun ε =>
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t))
      (𝓝[>] 0) (𝓝 0))
    -- Regularity:
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    -- C² regularity at crossing points (needed for PV existence):
    (hC2_cross : ∀ s ∈ S0, ∀ t ∈ Ioo γ.a γ.b, γ.toFun t = s →
      ContDiffAt ℝ 2 γ.toFun t)
    (h_cont_deriv_cross : ∀ s ∈ S0, ∀ t ∈ Ioo γ.a γ.b, γ.toFun t = s →
      ∃ a' b', t ∈ Ioo a' b' ∧ Icc a' b' ⊆ Icc γ.a γ.b ∧
        ContinuousOn (deriv γ.toFun) (Icc a' b')) :
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s := by
  /- Proof strategy (Path B): reduce to the simple-pole theorem via pure residue
     decomposition + limit arithmetic.

     Define f_res(z) = Σ_{s ∈ S0} Res(f,s)/(z-s)  [pure residue function].
     Then:
     (1) f_res has simple poles at each s ∈ S0
     (2) f_res is holomorphic on U \ S0
     (3) The simple-pole theorem gives: CPV(f_res) = 2πi Σ n(γ,s) · Res(f_res,s)
     (4) Res_simple(f_res, s) = Res(f, s) = residueAt(f, s)
     (5) CPV(f) = CPV(f_res) by limit argument:
         M_f(ε) = M_res(ε) + (M_f(ε) - M_res(ε))
         M_res → L_res (PV of f_res exists by simple-pole theorem)
         M_f - M_res → 0 (hHigherOrderCancel hypothesis)
         Therefore M_f → L_res, so limUnder M_f = limUnder M_res.
     (6) Combining: CPV(f) = 2πi Σ n(γ,s) · Res(f,s) -/
  -- Define the pure residue function
  set f_res := fun z => ∑ s ∈ S0, residueAt f s / (z - s) with hf_res_def
  -- Step 1: f_res has simple poles at each s ∈ S0
  have hSimple_res : ∀ s ∈ S0, HasSimplePoleAt f_res s :=
    fun s hs => hasSimplePoleAt_sum_div_sub S0 (residueAt f) s hs
  -- Step 2: f_res is holomorphic on U \ S0
  have hf_res_diff : DifferentiableOn ℂ f_res (U \ ↑S0) :=
    differentiableOn_sum_div_sub S0 (residueAt f) U
  -- Step 3: The remainder f_res - c_s/(z-s) is continuous at s (hf_ext condition)
  have hf_ext_res : ∀ s ∈ S0, ContinuousAt
      (fun z => f_res z - residueSimplePole f_res s / (z - s)) s :=
    fun s hs => continuousAt_sum_remainder S0 (residueAt f) s hs
  -- Step 4: residueSimplePole of f_res at s equals residueAt f s
  have h_res_eq : ∀ s ∈ S0,
      residueSimplePole f_res s = residueAt f s :=
    fun s hs => residueSimplePole_sum_div_sub S0 (residueAt f) s hs
  -- Step 5: Apply the simple-pole theorem to f_res
  have h_simple_thm := generalizedResidueTheorem U hU hU_convex S hS_in_U hS_discrete
    hS_closed S0 hS0_subset f_res hf_res_diff γ hγ_closed hγ_in_U hS_on_curve
    hSimple_res hf_ext_res hγ_meas h_no_endpt_cross hC2_cross h_cont_deriv_cross
  -- h_simple_thm : CPV(f_res) = 2πi Σ n(γ,s) · residueSimplePole(f_res, s)
  -- Step 6: Rewrite residueSimplePole to residueAt
  have h_res_formula : cauchyPrincipalValueOn S0 f_res γ.toFun γ.a γ.b =
      2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s := by
    rw [h_simple_thm]; congr 1; apply Finset.sum_congr rfl
    intro s hs; rw [h_res_eq s hs]
  -- Step 7: CPV(f) = CPV(f_res) via Path B (linearity approach)
  -- Write M_f(ε) = M_res(ε) + (M_f(ε) - M_res(ε)).
  -- Since M_res → L_res (PV of f_res exists) and M_f - M_res → 0
  -- (hHigherOrderCancel), we get M_f → L_res, hence limUnder M_f = limUnder M_res.
  have h_cpv_eq : cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      cauchyPrincipalValueOn S0 f_res γ.toFun γ.a γ.b := by
    -- Get PV existence for f_res (it has simple poles, so the simple-pole
    -- theorem applies and gives both existence and value)
    have hPV_singular_res : ∀ s ∈ S0, CauchyPrincipalValueExists'
        (fun z => residueSimplePole f_res s / (z - s)) γ.toFun γ.a γ.b s := by
      intro s hs
      have h_inv := cpv_exists_inv_sub γ s hγ_meas
        (h_no_endpt_cross s hs) (hC2_cross s hs) (h_cont_deriv_cross s hs)
      have h_eq : (fun z => residueSimplePole f_res s / (z - s)) =
          (fun z => residueSimplePole f_res s * (fun z => (z - s)⁻¹) z) := by
        ext z; simp [div_eq_mul_inv]
      rw [h_eq]; exact h_inv.const_mul (residueSimplePole f_res s)
    -- Apply the simple-pole theorem to f_res to get PV existence
    have h_res_exists : CauchyPrincipalValueExistsOn S0 f_res γ.toFun γ.a γ.b :=
      (generalizedResidueTheorem' U hU hU_convex S hS_in_U hS_discrete
        hS_closed S0 hS0_subset f_res hf_res_diff γ hγ_closed hγ_in_U hS_on_curve
        hSimple_res hf_ext_res hPV_singular_res).1
    obtain ⟨L_res, hL_res⟩ := h_res_exists
    -- Key limit argument: (M_f - M_res) → 0 and M_res → L_res, so M_f → L_res.
    -- Convert hHigherOrderCancel to use f_res (definitionally equal via let)
    have hCancel' : Tendsto
        (fun ε =>
          (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
          (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f_res γ.toFun ε t))
        (𝓝[>] 0) (𝓝 0) := hHigherOrderCancel
    -- Rewrite target function as (f - f_res) + f_res
    have h_eq : (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) =
      (fun ε =>
        ((∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
         (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f_res γ.toFun ε t)) +
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f_res γ.toFun ε t)) := by
      ext ε; ring
    have h_f_tendsto : Tendsto
        (fun ε => ∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t)
        (𝓝[>] 0) (𝓝 L_res) := by
      rw [h_eq, show L_res = 0 + L_res from (zero_add _).symm]
      exact hCancel'.add hL_res
    show limUnder (𝓝[>] 0) _ = limUnder (𝓝[>] 0) _
    rw [h_f_tendsto.limUnder_eq, hL_res.limUnder_eq]
  rw [h_cpv_eq, h_res_formula]

/-- **Theorem (Higher-order, Tendsto formulation)**: Variant of
`generalizedResidueTheorem_higher_order` with a `Tendsto` conclusion, taking PV
convergence of the pure residue function as a hypothesis rather than deriving it
from C² regularity. This avoids the `hC2_cross` and `h_cont_deriv_cross` hypotheses.

**Proof**: Write `M_f(ε) = (M_f(ε) - M_res(ε)) + M_res(ε)`. The first summand tends
to 0 by `hHigherOrderCancel`, the second to the residue sum by `hPV_res_tendsto`. -/
theorem generalizedResidueTheorem_higher_order_tendsto
    (S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hHigherOrderCancel : Tendsto
      (fun ε =>
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t))
      (𝓝[>] 0) (𝓝 0))
    (hPV_res_tendsto : Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t)
      (𝓝[>] 0) (𝓝 (2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s))) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t)
      (𝓝[>] 0) (𝓝 (2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s)) := by
  have h_eq : (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) =
    (fun ε =>
      ((∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
       (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
         (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t)) +
      (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
         (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t)) := by
    ext ε; ring
  rw [h_eq, show (2 * Real.pi * I * ∑ s ∈ S0,
      generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s) =
    0 + (2 * Real.pi * I * ∑ s ∈ S0,
      generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s)
    from (zero_add _).symm]
  exact hHigherOrderCancel.add hPV_res_tendsto

/-- **Corollary**: The simple-pole theorem is a special case of the higher-order theorem.
When all singularities are simple poles, `generalizedResidueTheorem_higher_order`
reduces to `generalizedResidueTheorem` (conditions A and B are automatic,
and `residueAt = residueSimplePole`). -/
theorem generalizedResidueTheorem_higher_order_simple
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S)
    (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hf_ext : ∀ s ∈ S0, ContinuousAt (fun z => f z - residueSimplePole f s / (z - s)) s)
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (hC2_cross : ∀ s ∈ S0, ∀ t ∈ Ioo γ.a γ.b, γ.toFun t = s →
      ContDiffAt ℝ 2 γ.toFun t)
    (h_cont_deriv_cross : ∀ s ∈ S0, ∀ t ∈ Ioo γ.a γ.b, γ.toFun t = s →
      ∃ a' b', t ∈ Ioo a' b' ∧ Icc a' b' ⊆ Icc γ.a γ.b ∧
        ContinuousOn (deriv γ.toFun) (Icc a' b')) :
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s := by
  have h_base := generalizedResidueTheorem U hU hU_convex S hS_in_U hS_discrete hS_closed
    S0 hS0_subset f hf γ hγ_closed hγ_in_U hS_on_curve hSimplePoles hf_ext
    hγ_meas h_no_endpt_cross hC2_cross h_cont_deriv_cross
  rw [h_base]
  congr 1; apply Finset.sum_congr rfl
  intro s hs
  rw [residueAt_eq_residueSimplePole f s (hSimplePoles s hs)]

-- Theorem 3.3 with paper's (A)+(B) hypotheses is in
-- `GeneralizedResidueTheory/Residue/FlatnessTransfer.lean` as
-- `generalizedResidueTheorem_3_3`, which combines `conditionsAB_imply_higherOrderCancel`
-- with `pv_res_tendsto_of_immersion` via `generalizedResidueTheorem_higher_order_tendsto`
-- to avoid C² hypotheses and give a `Tendsto` conclusion.

end
