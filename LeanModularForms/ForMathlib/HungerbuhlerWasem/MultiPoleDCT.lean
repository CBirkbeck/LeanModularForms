/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem

/-!
# Multi-pole DCT lift for the polar-part Cauchy principal value (T-BR-Y5)

When `γ` crosses **multiple** poles in `S`, a singleton-CPV
`HasCauchyPV (decomp.polarPart s) γ s L` at one pole `s ∈ S` can be lifted to
the multi-point form `HasCauchyPVOn S (decomp.polarPart s) γ L`
**without** requiring `γ` to avoid the other poles in `S \ {s}`.

This eliminates the `h_avoid_others_per_pole` restriction in
`residueTheorem_crossing_*`.

## Strategy

The integrand `cpvIntegrandOn S f γ ε t` differs from the singleton-form
`cpvIntegrand f γ s ε t` exactly on the set

  `D(ε) := { t : (∃ s' ∈ S \ {s}, ‖γ(t) - s'‖ ≤ ε) ∧ ε < ‖γ(t) - s‖ }`

For `f = decomp.polarPart s`:
- the Laurent expression of `f` is bounded uniformly by some `M_polar` on
  `D(ε)` (when ε is small enough);
- `‖γ'(t)‖ ≤ K` (the Lipschitz constant);
- `vol(D(ε)) ≤ vol(badSet for S \ {s})(ε) → 0` as ε → 0+ (immersion → preimage
  of finite set has measure zero).

## Main results

* `MultiPoleDCT.badSet_volume_tendsto_zero` — `vol(badSet γ T ε) → 0` as
  `ε → 0+` when `γ` is an immersion and `T` is finite.
* `MultiPoleDCT.cpvIntegrand_polarPart_intervalIntegrable` — singleton
  cutoff integrand for the polar part is interval-integrable.
* `MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole` — the
  singleton-to-multipole CPV lift (the headline T-BR-Y5 result).

-/

open Set Filter Topology Complex MeasureTheory Metric
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

namespace MultiPoleDCT

variable {x : ℂ}

/-! ## Bad-set volume tends to zero -/

/-- The "bad set" for a finite set `T` of pole candidates: parameters `t ∈ [0,1]`
where `γ(t)` is within `ε` of some `s' ∈ T`. As `ε → 0+`, the bad sets shrink
to `γ⁻¹(T) ∩ [0,1]`. -/
def badSetIcc (γP : PiecewiseC1Path x x) (T : Finset ℂ) (ε : ℝ) : Set ℝ :=
  {t ∈ Icc (0 : ℝ) 1 | ∃ s' ∈ T, ‖γP.toPath.extend t - s'‖ ≤ ε}

theorem badSetIcc_measurableSet (γP : PiecewiseC1Path x x) (T : Finset ℂ)
    (ε : ℝ) : MeasurableSet (badSetIcc γP T ε) := by
  classical
  unfold badSetIcc
  have h_eq : {t ∈ Icc (0 : ℝ) 1 | ∃ s' ∈ T, ‖γP.toPath.extend t - s'‖ ≤ ε} =
      Icc (0 : ℝ) 1 ∩ ⋃ s' ∈ T, {t : ℝ | ‖γP.toPath.extend t - s'‖ ≤ ε} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion]
    tauto
  rw [h_eq]
  refine measurableSet_Icc.inter ?_
  refine MeasurableSet.biUnion T.countable_toSet fun s' _ => ?_
  exact (isClosed_le ((γP.toPath.continuous_extend.sub continuous_const).norm)
    continuous_const).measurableSet

theorem badSetIcc_mono (γP : PiecewiseC1Path x x) (T : Finset ℂ) :
    Monotone (badSetIcc γP T) := by
  intro ε₁ ε₂ hε t ht
  obtain ⟨ht_Icc, s', hs'T, h_le⟩ := ht
  exact ⟨ht_Icc, s', hs'T, h_le.trans hε⟩

theorem badSetIcc_subset_Icc (γP : PiecewiseC1Path x x) (T : Finset ℂ) (ε : ℝ) :
    badSetIcc γP T ε ⊆ Icc (0 : ℝ) 1 := fun _ ht => ht.1

theorem badSetIcc_volume_ne_top (γP : PiecewiseC1Path x x) (T : Finset ℂ) (ε : ℝ) :
    volume (badSetIcc γP T ε) ≠ ⊤ :=
  ((measure_mono (badSetIcc_subset_Icc γP T ε)).trans_lt measure_Icc_lt_top).ne

/-- Intersection of all bad sets (over ε > 0) equals the preimage of `T` in `[0,1]`. -/
theorem badSetIcc_iInter_pos (γP : PiecewiseC1Path x x) (T : Finset ℂ) :
    (⋂ ε ∈ Set.Ioi (0 : ℝ), badSetIcc γP T ε) =
      {t ∈ Icc (0 : ℝ) 1 | γP.toPath.extend t ∈ (↑T : Set ℂ)} := by
  classical
  ext t
  simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_Ioi]
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : t ∈ Icc (0 : ℝ) 1 := (h 1 zero_lt_one).1
    refine ⟨h1, ?_⟩
    by_contra h_notin
    by_cases hT_ne : T.Nonempty
    · have h_pos : ∀ s' ∈ T, 0 < ‖γP.toPath.extend t - s'‖ := by
        intro s' hs'
        refine norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
        intro heq
        exact h_notin (heq ▸ Finset.mem_coe.mpr hs')
      obtain ⟨s_min, hs_min_mem, hs_min⟩ := Finset.exists_min_image T
        (fun s' => ‖γP.toPath.extend t - s'‖) hT_ne
      have h_min_pos : 0 < ‖γP.toPath.extend t - s_min‖ := h_pos s_min hs_min_mem
      set ε₀ : ℝ := ‖γP.toPath.extend t - s_min‖ / 2 with hε₀_def
      have hε₀_pos : 0 < ε₀ := by rw [hε₀_def]; linarith
      obtain ⟨_, s', hs'T, h_close⟩ := h ε₀ hε₀_pos
      have h_min_bound : ‖γP.toPath.extend t - s_min‖ ≤
          ‖γP.toPath.extend t - s'‖ := hs_min s' hs'T
      have h_too_close : ‖γP.toPath.extend t - s_min‖ ≤ ε₀ :=
        h_min_bound.trans h_close
      have : ‖γP.toPath.extend t - s_min‖ ≤
          ‖γP.toPath.extend t - s_min‖ / 2 := h_too_close
      linarith
    · have hT_empty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT_ne
      obtain ⟨_, s', hs'T, _⟩ := h 1 zero_lt_one
      subst hT_empty
      exact absurd hs'T (Finset.notMem_empty s')
  · intro ⟨ht_Icc, ht_in_T⟩ ε hε_pos
    have ⟨s', hs'T, h_eq⟩ : ∃ s' ∈ T, γP.toPath.extend t = s' :=
      ⟨γP.toPath.extend t, Finset.mem_coe.mp ht_in_T, rfl⟩
    refine ⟨ht_Icc, s', hs'T, ?_⟩
    rw [h_eq, sub_self, norm_zero]
    exact hε_pos.le

/-- The volume of the bad set tends to zero as `ε → 0+` for a closed piecewise-`C¹`
immersion `γ`. -/
theorem badSet_volume_tendsto_zero (γ : ClosedPwC1Immersion x) (T : Finset ℂ) :
    Tendsto (fun ε : ℝ => volume (badSetIcc γ.toPwC1Immersion.toPiecewiseC1Path T ε))
      (𝓝[>] 0) (𝓝 0) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have h_meas : ∀ r > (0 : ℝ), NullMeasurableSet (badSetIcc γP T r) volume := fun r _ =>
    (badSetIcc_measurableSet γP T r).nullMeasurableSet
  have h_mono : ∀ i j : ℝ, (0 : ℝ) < i → i ≤ j →
      badSetIcc γP T i ⊆ badSetIcc γP T j := fun i j _ hij =>
    badSetIcc_mono γP T hij
  have h_finite : ∃ r > (0 : ℝ), volume (badSetIcc γP T r) ≠ ⊤ :=
    ⟨1, zero_lt_one, badSetIcc_volume_ne_top γP T 1⟩
  have h_lim := MeasureTheory.tendsto_measure_biInter_gt
    (μ := MeasureTheory.volume) (s := badSetIcc γP T) (a := (0 : ℝ))
    h_meas h_mono h_finite
  have h_iInter_eq : volume (⋂ r, ⋂ (_ : r > (0 : ℝ)), badSetIcc γP T r) = 0 := by
    have h_set_eq : (⋂ r, ⋂ (_ : r > (0 : ℝ)), badSetIcc γP T r) =
        {t ∈ Icc (0 : ℝ) 1 | γP.toPath.extend t ∈ (↑T : Set ℂ)} := by
      have hp := badSetIcc_iInter_pos γP T
      -- hp : (⋂ ε ∈ Set.Ioi 0, badSetIcc γP T ε) = ...
      -- The notation `⋂ r, ⋂ (_ : r > 0), …` is the same as `⋂ r ∈ Ioi 0, …`.
      convert hp using 1
    rw [h_set_eq]
    exact volume_preimage_finset_in_Icc01_zero γ T
  rw [h_iInter_eq] at h_lim
  exact h_lim

/-! ## Polar-part bounded singleton-CPV integrand -/

/-- The singleton-CPV cutoff integrand for the polar part `decomp.polarPart s`
is interval-integrable on `[0, 1]` for every `ε > 0`. Mirrors
`cpvIntegrandOn_polarPart_intervalIntegrable` but for the singleton form. -/
theorem cpvIntegrand_polarPart_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {U : Set ℂ} {S : Finset ℂ}
    {f : ℂ → ℂ} (decomp : PolarPartDecomposition f S U) {s : ℂ} (hs : s ∈ S)
    {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => cpvIntegrand (decomp.polarPart s)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε t)
      MeasureTheory.volume 0 1 := by
  classical
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  set N : ℕ := decomp.order s
  set a : Fin N → ℂ := decomp.coeff s
  set laurentSum : ℂ → ℂ := fun z => ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)
  set h_curve : ℝ → ℂ := fun t =>
    laurentSum (γP.toPath.extend t) * deriv γP.toPath.extend t
  have h_indicator_eq :
      (fun t => cpvIntegrand (decomp.polarPart s) γP.toPath.extend s ε t) =
      {t : ℝ | ε < ‖γP.toPath.extend t - s‖}.indicator h_curve := by
    funext t
    unfold cpvIntegrand
    by_cases h : ε < ‖γP.toPath.extend t - s‖
    · simp only [h, ite_true]
      have ht_in : t ∈ {t : ℝ | ε < ‖γP.toPath.extend t - s‖} := h
      rw [Set.indicator_of_mem ht_in]
      have h_ne : γP.toPath.extend t ≠ s := by
        intro heq
        rw [heq, sub_self, norm_zero] at h; linarith
      change decomp.polarPart s (γP.toPath.extend t) * deriv γP.toPath.extend t =
        laurentSum (γP.toPath.extend t) * deriv γP.toPath.extend t
      rw [decomp.polarPart_eq s hs _ h_ne]
    · simp only [h, ite_false]
      have ht_nin : t ∉ {t : ℝ | ε < ‖γP.toPath.extend t - s‖} := h
      rw [Set.indicator_of_notMem ht_nin]
  have h_meas_set : MeasurableSet {t : ℝ | ε < ‖γP.toPath.extend t - s‖} := by
    refine (isOpen_lt continuous_const ?_).measurableSet
    exact (γP.toPath.continuous_extend.sub continuous_const).norm
  set M_polar : ℝ := ∑ k : Fin N, ‖a k‖ / ε ^ (k.val + 1)
  set M : ℝ := M_polar * K
  have h_M_polar_nonneg : 0 ≤ M_polar :=
    Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hε.le _)
  have h_M_nonneg : 0 ≤ M := mul_nonneg h_M_polar_nonneg K.coe_nonneg
  have h_bound_on_set : ∀ t ∈ {t : ℝ | ε < ‖γP.toPath.extend t - s‖},
      ‖h_curve t‖ ≤ M := by
    intro t h
    have h_far_s : ε < ‖γP.toPath.extend t - s‖ := h
    have h_lap_bound : ‖laurentSum (γP.toPath.extend t)‖ ≤ M_polar := by
      change ‖∑ k : Fin N, a k / (γP.toPath.extend t - s) ^ (k.val + 1)‖ ≤ M_polar
      refine (norm_sum_le _ _).trans ?_
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_div, norm_pow]
      apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hε _)
      exact pow_le_pow_left₀ hε.le h_far_s.le _
    have h_deriv_bound : ‖deriv γP.toPath.extend t‖ ≤ K :=
      norm_deriv_le_of_lipschitz hLip
    calc ‖h_curve t‖ = ‖laurentSum (γP.toPath.extend t)‖ *
          ‖deriv γP.toPath.extend t‖ := norm_mul _ _
      _ ≤ M_polar * K := by
          exact mul_le_mul h_lap_bound h_deriv_bound (norm_nonneg _) h_M_polar_nonneg
  have h_bound_indicator : ∀ t,
      ‖{t : ℝ | ε < ‖γP.toPath.extend t - s‖}.indicator h_curve t‖ ≤ M := by
    intro t
    by_cases ht_in : t ∈ {t : ℝ | ε < ‖γP.toPath.extend t - s‖}
    · rw [Set.indicator_of_mem ht_in]
      exact h_bound_on_set t ht_in
    · rw [Set.indicator_of_notMem ht_in]
      simp only [norm_zero]
      exact h_M_nonneg
  have h_γ_meas : Measurable γP.toPath.extend :=
    γP.toPath.continuous_extend.measurable
  have h_γ'_meas : Measurable (deriv γP.toPath.extend) := measurable_deriv _
  have h_laurentSum_meas : Measurable (fun t => laurentSum (γP.toPath.extend t)) := by
    refine Finset.measurable_sum (Finset.univ : Finset (Fin N)) (fun k _ => ?_)
    refine Measurable.const_div ?_ _
    refine Measurable.pow_const ?_ _
    exact h_γ_meas.sub_const s
  have h_curve_meas : Measurable h_curve :=
    h_laurentSum_meas.mul h_γ'_meas
  have h_aemeas : AEStronglyMeasurable
      ({t : ℝ | ε < ‖γP.toPath.extend t - s‖}.indicator h_curve)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    refine (h_curve_meas.aestronglyMeasurable).indicator h_meas_set
  rw [intervalIntegrable_iff, h_indicator_eq]
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top h_aemeas M ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t _
  exact h_bound_indicator t

/-! ## Headline lift -/

variable {U : Set ℂ}

/-- **T-BR-Y5 — Multi-pole DCT lift for the polar part.**

Given `decomp : PolarPartDecomposition f S U`, a closed piecewise-`C¹`
immersion `γ`, `s ∈ S`, and a singleton CPV
`HasCauchyPV (decomp.polarPart s) γ s L`, the multi-point CPV
`HasCauchyPVOn S (decomp.polarPart s) γ L` follows **without** requiring
γ to avoid the other poles in `S \ {s}`. -/
theorem hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole
    {S : Finset ℂ} {f : ℂ → ℂ} (hS_in_U : ↑S ⊆ U)
    (decomp : PolarPartDecomposition f S U)
    (γ : ClosedPwC1Immersion x) {s : ℂ} (hs : s ∈ S) {L : ℂ}
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (h : HasCauchyPV (decomp.polarPart s)
      γ.toPwC1Immersion.toPiecewiseC1Path s L) :
    HasCauchyPVOn S (decomp.polarPart s)
      γ.toPwC1Immersion.toPiecewiseC1Path L := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  set T : Finset ℂ := S.erase s
  set N : ℕ := decomp.order s
  set a : Fin N → ℂ := decomp.coeff s
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  have h_deriv_le : ∀ t, ‖deriv γP.toPath.extend t‖ ≤ K := fun _ =>
    norm_deriv_le_of_lipschitz hLip
  by_cases hT_ne : T.Nonempty
  swap
  · -- T = ∅: S = {s}.
    have hT_empty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT_ne
    have hS_eq : S = {s} := by
      ext s'
      simp only [Finset.mem_singleton]
      refine ⟨fun hs' => ?_, fun hs' => hs' ▸ hs⟩
      by_contra h_ne
      have h_mem : s' ∈ S.erase s := Finset.mem_erase.mpr ⟨h_ne, hs'⟩
      have h_T_eq : T = S.erase s := rfl
      rw [← h_T_eq] at h_mem
      rw [hT_empty] at h_mem
      exact absurd h_mem (Finset.notMem_empty _)
    -- Since S = {s}, multipoint integrand on S equals singleton integrand at s.
    simp only [HasCauchyPVOn, HasCauchyPV] at h ⊢
    refine h.congr ?_
    intro ε
    apply intervalIntegral.integral_congr
    intro t _
    -- Goal: cpvIntegrand ... s ε t = cpvIntegrandOn S ... ε t.
    -- Using S = {s}: cpvIntegrandOn {s} = cpvIntegrand.
    unfold cpvIntegrand cpvIntegrandOn
    by_cases h_far : ε < ‖γP.toPath.extend t - s‖
    · rw [if_pos h_far]
      rw [if_neg]
      push Not
      intro s' hs'
      rw [hS_eq, Finset.mem_singleton] at hs'
      subst hs'
      exact h_far
    · push Not at h_far
      rw [if_neg (not_lt.mpr h_far)]
      rw [if_pos]
      refine ⟨s, ?_, h_far⟩
      rw [hS_eq, Finset.mem_singleton]
  -- Generic multi-pole case.
  obtain ⟨s'_min, hs'_min_mem, hs'_min⟩ := Finset.exists_min_image T
    (fun s' => ‖s - s'‖) hT_ne
  have h_s'_min_ne_s : s'_min ≠ s := Finset.ne_of_mem_erase hs'_min_mem
  have h_pos_min : 0 < ‖s - s'_min‖ := by
    refine norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
    intro heq
    exact h_s'_min_ne_s heq.symm
  set R : ℝ := ‖s - s'_min‖ / 4 with hR_def
  have hR_pos : 0 < R := by rw [hR_def]; linarith
  have h_3R_pos : 0 < 3 * R := by linarith
  have h_dist_ge : ∀ s' ∈ T, 4 * R ≤ ‖s - s'‖ := fun s' hs'_mem => by
    have h1 : ‖s - s'_min‖ ≤ ‖s - s'‖ := hs'_min s' hs'_mem
    have h2 : 4 * R = ‖s - s'_min‖ := by rw [hR_def]; ring
    linarith
  set M_polar : ℝ := ∑ k : Fin N, ‖a k‖ / (3 * R) ^ (k.val + 1)
  set M : ℝ := M_polar * K
  have hM_polar_nonneg : 0 ≤ M_polar :=
    Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _)
      (pow_nonneg h_3R_pos.le _)
  have hM_nonneg : 0 ≤ M := mul_nonneg hM_polar_nonneg K.coe_nonneg
  -- Pointwise difference of integrands.
  have h_diff_pt : ∀ ε > (0 : ℝ), ∀ t,
      cpvIntegrand (decomp.polarPart s) γP.toPath.extend s ε t -
        cpvIntegrandOn S (decomp.polarPart s) γP.toPath.extend ε t =
      if (∃ s' ∈ T, ‖γP.toPath.extend t - s'‖ ≤ ε) ∧
          ε < ‖γP.toPath.extend t - s‖
        then decomp.polarPart s (γP.toPath.extend t) * deriv γP.toPath.extend t
        else 0 := by
    intro ε _hε_pos t
    unfold cpvIntegrand cpvIntegrandOn
    by_cases h_far_s : ε < ‖γP.toPath.extend t - s‖
    · rw [if_pos h_far_s]
      by_cases h_S : ∃ s'' ∈ S, ‖γP.toPath.extend t - s''‖ ≤ ε
      · rw [if_pos h_S]
        obtain ⟨s'', hs''_mem, h_close⟩ := h_S
        have hs''_ne_s : s'' ≠ s := by
          intro heq; rw [heq] at h_close; linarith
        have hs''_in_T : s'' ∈ T := Finset.mem_erase.mpr ⟨hs''_ne_s, hs''_mem⟩
        rw [if_pos ⟨⟨s'', hs''_in_T, h_close⟩, h_far_s⟩]
        ring
      · rw [if_neg h_S]
        have h_T_far : ¬ ∃ s' ∈ T, ‖γP.toPath.extend t - s'‖ ≤ ε := by
          intro ⟨s', hs'_mem, h_close⟩
          exact h_S ⟨s', Finset.mem_of_mem_erase hs'_mem, h_close⟩
        rw [if_neg (fun hT' => h_T_far hT'.1)]
        ring
    · push Not at h_far_s
      rw [if_neg (not_lt.mpr h_far_s)]
      have h_S : ∃ s'' ∈ S, ‖γP.toPath.extend t - s''‖ ≤ ε := ⟨s, hs, h_far_s⟩
      rw [if_pos h_S]
      rw [if_neg (fun ⟨_, hh⟩ => absurd hh (not_lt.mpr h_far_s))]
      ring
  -- Bound on difference for t ∈ Icc 0 1: bounded by M·𝟙_{badSet T ε}.
  have h_diff_norm_bound_on_Icc : ∀ ε ∈ Set.Ioo (0 : ℝ) R, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖cpvIntegrand (decomp.polarPart s) γP.toPath.extend s ε t -
        cpvIntegrandOn S (decomp.polarPart s) γP.toPath.extend ε t‖ ≤
      (badSetIcc γP T ε).indicator (fun _ : ℝ => M) t := by
    intro ε ⟨hε_pos, hε_lt_R⟩ t ht_Icc
    rw [h_diff_pt ε hε_pos t]
    by_cases h_cond : (∃ s' ∈ T, ‖γP.toPath.extend t - s'‖ ≤ ε) ∧
        ε < ‖γP.toPath.extend t - s‖
    · rw [if_pos h_cond]
      obtain ⟨⟨s', hs'_mem, h_close_s'⟩, h_far_s⟩ := h_cond
      have h_dist_far : 3 * R ≤ ‖γP.toPath.extend t - s‖ := by
        have h_tri : ‖s - s'‖ ≤ ‖γP.toPath.extend t - s‖ +
            ‖γP.toPath.extend t - s'‖ := by
          calc ‖s - s'‖ = ‖(γP.toPath.extend t - s') - (γP.toPath.extend t - s)‖ := by
                congr 1; ring
            _ ≤ ‖γP.toPath.extend t - s'‖ + ‖γP.toPath.extend t - s‖ :=
                norm_sub_le _ _
            _ = ‖γP.toPath.extend t - s‖ + ‖γP.toPath.extend t - s'‖ := by ring
        have h_s_far : 4 * R ≤ ‖s - s'‖ := h_dist_ge s' hs'_mem
        have h_close_s'_R : ‖γP.toPath.extend t - s'‖ ≤ R :=
          h_close_s'.trans hε_lt_R.le
        linarith
      have h_polarPart_eq : decomp.polarPart s (γP.toPath.extend t) =
          ∑ k : Fin N, a k / (γP.toPath.extend t - s) ^ (k.val + 1) := by
        refine decomp.polarPart_eq s hs _ ?_
        intro heq; rw [heq, sub_self, norm_zero] at h_far_s; linarith
      rw [h_polarPart_eq]
      have h_norm_poly : ‖∑ k : Fin N,
          a k / (γP.toPath.extend t - s) ^ (k.val + 1)‖ ≤ M_polar := by
        refine (norm_sum_le _ _).trans ?_
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_div, norm_pow]
        apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos h_3R_pos _)
        exact pow_le_pow_left₀ h_3R_pos.le h_dist_far _
      have h_bound_M : ‖(∑ k : Fin N, a k / (γP.toPath.extend t - s) ^ (k.val + 1)) *
            deriv γP.toPath.extend t‖ ≤ M := by
        calc ‖(∑ k : Fin N, a k / (γP.toPath.extend t - s) ^ (k.val + 1)) *
            deriv γP.toPath.extend t‖
            = ‖∑ k : Fin N, a k / (γP.toPath.extend t - s) ^ (k.val + 1)‖ *
              ‖deriv γP.toPath.extend t‖ := norm_mul _ _
          _ ≤ M_polar * K := mul_le_mul h_norm_poly (h_deriv_le t)
              (norm_nonneg _) hM_polar_nonneg
      have ht_in_bad : t ∈ badSetIcc γP T ε :=
        ⟨ht_Icc, s', hs'_mem, h_close_s'⟩
      rw [Set.indicator_of_mem ht_in_bad]
      exact h_bound_M
    · rw [if_neg h_cond]
      simp only [norm_zero]
      by_cases h_t_bad : t ∈ badSetIcc γP T ε
      · rw [Set.indicator_of_mem h_t_bad]; exact hM_nonneg
      · rw [Set.indicator_of_notMem h_t_bad]
  -- Integral bound: ‖∫(cpv - cpvOn)‖ ≤ M * vol(badSet T ε).
  have h_int_bound : ∀ ε ∈ Set.Ioo (0 : ℝ) R,
      ‖(∫ t in (0 : ℝ)..1, cpvIntegrand (decomp.polarPart s)
          γP.toPath.extend s ε t) -
        (∫ t in (0 : ℝ)..1, cpvIntegrandOn S (decomp.polarPart s)
          γP.toPath.extend ε t)‖ ≤
      M * (volume (badSetIcc γP T ε)).toReal := by
    intro ε hε_in
    obtain ⟨hε_pos, hε_lt_R⟩ := hε_in
    have h_int_cpv : IntervalIntegrable
        (fun t => cpvIntegrand (decomp.polarPart s) γP.toPath.extend s ε t)
        MeasureTheory.volume 0 1 :=
      cpvIntegrand_polarPart_intervalIntegrable γ decomp hs hε_pos
    have h_int_cpvOn : IntervalIntegrable
        (fun t => cpvIntegrandOn S (decomp.polarPart s) γP.toPath.extend ε t)
        MeasureTheory.volume 0 1 :=
      cpvIntegrandOn_polarPart_intervalIntegrable γ hS_in_U decomp hs h_null hε_pos
    -- Combine integrals: ∫a - ∫b = ∫(a - b).
    rw [← intervalIntegral.integral_sub h_int_cpv h_int_cpvOn]
    -- Bound using norm_integral_le_of_norm_le.
    have h_bound_aux :
        ‖∫ t in (0 : ℝ)..1, (cpvIntegrand (decomp.polarPart s)
              γP.toPath.extend s ε t -
            cpvIntegrandOn S (decomp.polarPart s) γP.toPath.extend ε t)‖ ≤
        ∫ t in (0 : ℝ)..1,
          (badSetIcc γP T ε).indicator (fun _ : ℝ => M) t := by
      refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ ?_
      · refine MeasureTheory.ae_of_all _ ?_
        intro t ht
        have ht_Icc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
        exact h_diff_norm_bound_on_Icc ε ⟨hε_pos, hε_lt_R⟩ t ht_Icc
      · -- Indicator function with constant M on measurable set is integrable on [0,1].
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
        refine (MeasureTheory.integrable_indicator_iff
          (badSetIcc_measurableSet γP T ε)).mpr ?_
        refine MeasureTheory.integrableOn_const (μ := volume.restrict (Set.Ioc 0 1))
          (s := badSetIcc γP T ε) (C := M) ?_
        rw [MeasureTheory.Measure.restrict_apply (badSetIcc_measurableSet γP T ε)]
        exact ((measure_mono (Set.inter_subset_right :
          badSetIcc γP T ε ∩ Set.Ioc 0 1 ⊆ Set.Ioc 0 1)).trans_lt measure_Ioc_lt_top).ne
    -- Compute ∫ indicator (badSetIcc) M.
    have h_ind_int :
        ∫ t in (0 : ℝ)..1, (badSetIcc γP T ε).indicator (fun _ : ℝ => M) t =
          M * (volume (badSetIcc γP T ε ∩ Set.Ioc 0 1)).toReal := by
      rw [intervalIntegral.integral_of_le zero_le_one,
          MeasureTheory.integral_indicator (badSetIcc_measurableSet γP T ε),
          MeasureTheory.setIntegral_const]
      simp only [smul_eq_mul, mul_comm]
      congr 1
      simp only [MeasureTheory.Measure.real,
        MeasureTheory.Measure.restrict_apply (badSetIcc_measurableSet γP T ε)]
    rw [h_ind_int] at h_bound_aux
    -- The intersection's measure ≤ measure of badSet.
    have h_le_vol : (volume (badSetIcc γP T ε ∩ Set.Ioc 0 1)).toReal ≤
        (volume (badSetIcc γP T ε)).toReal := by
      refine ENNReal.toReal_mono (badSetIcc_volume_ne_top γP T ε) ?_
      exact measure_mono Set.inter_subset_left
    linarith [mul_le_mul_of_nonneg_left h_le_vol hM_nonneg]
  -- Convergence of integral bound to 0.
  have h_vol_lim : Tendsto (fun ε => (volume (badSetIcc γP T ε)).toReal)
      (𝓝[>] 0) (𝓝 0) := by
    have h_lim_ennreal := badSet_volume_tendsto_zero γ T
    have h_continuous := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto
    have h_comp : Tendsto (fun ε => (volume (badSetIcc γP T ε)).toReal) (𝓝[>] 0)
        (𝓝 (ENNReal.toReal 0)) := h_continuous.comp h_lim_ennreal
    simpa using h_comp
  have h_bound_tendsto : Tendsto (fun ε => M * (volume (badSetIcc γP T ε)).toReal)
      (𝓝[>] 0) (𝓝 0) := by
    have := h_vol_lim.const_mul M
    simpa using this
  -- Squeeze difference to 0.
  have h_diff_tendsto :
      Tendsto (fun ε => (∫ t in (0 : ℝ)..1, cpvIntegrand (decomp.polarPart s)
          γP.toPath.extend s ε t) -
        (∫ t in (0 : ℝ)..1, cpvIntegrandOn S (decomp.polarPart s)
          γP.toPath.extend ε t)) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h_bound_tendsto
    filter_upwards [Ioo_mem_nhdsGT hR_pos] with ε hε
    exact h_int_bound ε hε
  -- Apply to multipole.
  unfold HasCauchyPVOn
  unfold HasCauchyPV at h
  have h_multi_eq :
      (fun ε => ∫ t in (0 : ℝ)..1, cpvIntegrandOn S (decomp.polarPart s)
        γP.toPath.extend ε t) =
      (fun ε => (∫ t in (0 : ℝ)..1, cpvIntegrand (decomp.polarPart s)
        γP.toPath.extend s ε t) -
        ((∫ t in (0 : ℝ)..1, cpvIntegrand (decomp.polarPart s)
          γP.toPath.extend s ε t) -
          (∫ t in (0 : ℝ)..1, cpvIntegrandOn S (decomp.polarPart s)
            γP.toPath.extend ε t))) := by
    funext ε; ring
  rw [h_multi_eq]
  have : Tendsto (fun ε => (∫ t in (0 : ℝ)..1, cpvIntegrand (decomp.polarPart s)
        γP.toPath.extend s ε t) -
        ((∫ t in (0 : ℝ)..1, cpvIntegrand (decomp.polarPart s)
          γP.toPath.extend s ε t) -
          (∫ t in (0 : ℝ)..1, cpvIntegrandOn S (decomp.polarPart s)
            γP.toPath.extend ε t)))
      (𝓝[>] 0) (𝓝 (L - 0)) := h.sub h_diff_tendsto
  simpa using this

end MultiPoleDCT

end HungerbuhlerWasem

end
