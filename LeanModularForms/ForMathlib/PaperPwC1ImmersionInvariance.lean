/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.PaperPwC1Immersion
import LeanModularForms.ForMathlib.NullHomologous
import LeanModularForms.ForMathlib.CauchyPrincipalValue
import LeanModularForms.ForMathlib.FlatnessConditions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Cyclic-shift invariance lemmas for `ClosedPwC1Immersion`

This file provides the four headline invariance lemmas for the cyclic shift
constructor `ClosedPwC1Immersion.cyclicShift`:

* `hasCauchyPVOn_cyclicShift` — `HasCauchyPVOn` is invariant under cyclic shift.
* `generalizedWindingNumber_cyclicShift` — `generalizedWindingNumber` is invariant
  under cyclic shift.
* `cyclicShift_image_eq` — the path image is preserved.
* `isNullHomologous_cyclicShift` — `IsNullHomologous` is invariant under cyclic
  shift.

These are the bookkeeping facts needed to discharge `hx_notin_S` in the
HW3.3 spec theorem chain.

## Proof strategy

The integral identity is established via a **periodic-extension trick**: define
`G u := cpvIntegrandOn S f γ.extend ε (Int.fract u)`, the periodic extension
(period 1) of the cutoff integrand. Then:

* `cpvIntegrandOn S f γ_τ.extend ε t = G(t + τ)` for a.e. `t ∈ [0, 1]` (by the
  parameter-level eq-on lemmas for `cyclicShift`).
* `∫_0^1 G(t + τ) dt = ∫_τ^(1+τ) G(u) du` by `integral_comp_add_right`.
* `∫_τ^(1+τ) G(u) du = ∫_0^1 G(u) du` by `Function.Periodic.intervalIntegral_add_eq`.
* `∫_0^1 G(u) du = ∫_0^1 cpvIntegrandOn S f γ.extend ε u du` (a.e. equality on
  `[0, 1)`).

The crucial advantage of this approach: `Function.Periodic.intervalIntegral_add_eq`
does **not** require integrability. So the integral identity holds for any `f`,
independent of integrability assumptions.

## References

* K. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized
  Residue Theorem*, arXiv:1808.00997v2
-/

open Set Filter Topology MeasureTheory Complex

noncomputable section

namespace ClosedPwC1Immersion

variable {x : ℂ}

private def cpvIntegrandOnPer (γ : ClosedPwC1Immersion x) (S : Finset ℂ)
    (f : ℂ → ℂ) (ε : ℝ) (u : ℝ) : ℂ :=
  cpvIntegrandOn S f γ.toPath.extend ε (Int.fract u)

private lemma cpvIntegrandOnPer_periodic (γ : ClosedPwC1Immersion x) (S : Finset ℂ)
    (f : ℂ → ℂ) (ε : ℝ) :
    Function.Periodic (cpvIntegrandOnPer γ S f ε) 1 := by
  intro u
  simp only [cpvIntegrandOnPer]
  rw [Int.fract_add_one u]

private lemma cpvIntegrandOnPer_eq_on_Ico (γ : ClosedPwC1Immersion x) (S : Finset ℂ)
    (f : ℂ → ℂ) (ε : ℝ) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    cpvIntegrandOnPer γ S f ε u = cpvIntegrandOn S f γ.toPath.extend ε u := by
  simp only [cpvIntegrandOnPer]
  congr 1
  exact Int.fract_eq_self.mpr hu

private lemma cpvIntegrandOnPer_eq_on_Ico_one_two (γ : ClosedPwC1Immersion x)
    (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) {u : ℝ} (hu : u ∈ Ico (1 : ℝ) 2) :
    cpvIntegrandOnPer γ S f ε u = cpvIntegrandOn S f γ.toPath.extend ε (u - 1) := by
  have h_sub : u - 1 ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  conv_lhs => rw [show u = (u - 1) + 1 from by ring]
  rw [cpvIntegrandOnPer_periodic γ S f ε (u - 1)]
  exact cpvIntegrandOnPer_eq_on_Ico γ S f ε h_sub

private lemma cpvIntegrandOn_cyclicShift_eq_per_ae (γ : ClosedPwC1Immersion x)
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 1 →
      cpvIntegrandOn S f (γ.cyclicShift hτ).toPath.extend ε t =
        cpvIntegrandOnPer γ S f ε (t + τ) := by
  classical
  have hP_nmem : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∉ ((γ.cyclicShift hτ).closedPartition : Set ℝ) :=
    MeasureTheory.compl_mem_ae_iff.mpr (Finset.measure_zero _ _)
  filter_upwards [hP_nmem] with t ht_nmem ht_in
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht_in
  obtain ⟨ht_pos, ht_le⟩ := ht_in
  have h_contra : ∀ {c : ℝ}, t = c → c ∈ cyclicShiftPartitionExt γ.closedPartition τ → False :=
    fun ht_eq hc => ht_nmem (show t ∈ ((γ.cyclicShift hτ).closedPartition : Set ℝ) by
      rw [ht_eq]; exact_mod_cast hc)
  by_cases ht_le_oneSubTau : t ≤ 1 - τ
  · have ht_Ioo : t ∈ Ioo (0 : ℝ) (1 - τ) := by
      refine ⟨ht_pos, ?_⟩
      rcases lt_or_eq_of_le ht_le_oneSubTau with ht_lt | ht_eq
      · exact ht_lt
      · exact absurd (oneSubTau_mem_cyclicShiftPartitionExt γ.closedPartition τ)
          (h_contra ht_eq)
    have h_extend : (γ.cyclicShift hτ).toPath.extend t = γ.toPath.extend (t + τ) :=
      γ.cyclicShift_extend_eq_no_wrap hτ ⟨ht_pos.le, ht_le_oneSubTau⟩
    have h_per : cpvIntegrandOnPer γ S f ε (t + τ) =
        cpvIntegrandOn S f γ.toPath.extend ε (t + τ) :=
      cpvIntegrandOnPer_eq_on_Ico γ S f ε ⟨by linarith [hτ.1], by linarith [ht_Ioo.2]⟩
    rw [h_per]
    have h_deriv : deriv (γ.cyclicShift hτ).toPath.extend t =
        deriv γ.toPath.extend (t + τ) :=
      γ.cyclicShift_deriv_eq_no_wrap hτ ht_Ioo ht_nmem
    simp only [cpvIntegrandOn, h_extend, h_deriv]
  · push Not at ht_le_oneSubTau
    have h_t_lt_1 : t < 1 :=
      lt_or_eq_of_le ht_le |>.resolve_right fun h_eq =>
        h_contra h_eq (one_mem_cyclicShiftPartitionExt γ.closedPartition τ)
    have ht_Ioo : t ∈ Ioo (1 - τ) 1 := ⟨ht_le_oneSubTau, h_t_lt_1⟩
    have h_extend : (γ.cyclicShift hτ).toPath.extend t = γ.toPath.extend (t + τ - 1) :=
      γ.cyclicShift_extend_eq_wrap hτ ⟨ht_le_oneSubTau.le, ht_le⟩
    have h_per : cpvIntegrandOnPer γ S f ε (t + τ) =
        cpvIntegrandOn S f γ.toPath.extend ε ((t + τ) - 1) :=
      cpvIntegrandOnPer_eq_on_Ico_one_two γ S f ε
        ⟨by linarith, by linarith [hτ.2]⟩
    rw [h_per]
    have h_deriv : deriv (γ.cyclicShift hτ).toPath.extend t =
        deriv γ.toPath.extend (t + τ - 1) :=
      γ.cyclicShift_deriv_eq_wrap hτ ht_Ioo ht_nmem
    simp only [cpvIntegrandOn, h_extend, h_deriv]

private lemma cpvIntegrandOn_cyclicShift_integral_eq (γ : ClosedPwC1Immersion x)
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) :
    (∫ t in (0:ℝ)..1, cpvIntegrandOn S f (γ.cyclicShift hτ).toPath.extend ε t) =
      (∫ t in (0:ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t) := by
  classical
  have h_step1 : (∫ t in (0:ℝ)..1, cpvIntegrandOn S f (γ.cyclicShift hτ).toPath.extend ε t) =
      ∫ t in (0:ℝ)..1, cpvIntegrandOnPer γ S f ε (t + τ) :=
    intervalIntegral.integral_congr_ae (γ.cpvIntegrandOn_cyclicShift_eq_per_ae hτ S f ε)
  have h_step2 : (∫ t in (0:ℝ)..1, cpvIntegrandOnPer γ S f ε (t + τ)) =
      ∫ u in (0 + τ)..(1 + τ), cpvIntegrandOnPer γ S f ε u :=
    intervalIntegral.integral_comp_add_right (cpvIntegrandOnPer γ S f ε) τ
  have h_step3 : (∫ u in (0 + τ)..(1 + τ), cpvIntegrandOnPer γ S f ε u) =
      ∫ u in (0 : ℝ)..(0 + 1), cpvIntegrandOnPer γ S f ε u := by
    have h_shifted := (cpvIntegrandOnPer_periodic γ S f ε).intervalIntegral_add_eq τ 0
    simpa [zero_add, add_comm 1 τ] using h_shifted
  have h_step4 : (∫ u in (0 : ℝ)..(0 + 1), cpvIntegrandOnPer γ S f ε u) =
      ∫ u in (0:ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε u := by
    rw [zero_add]
    refine intervalIntegral.integral_congr_ae ?_
    have h_ae_not_one : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 1 :=
      MeasureTheory.ae_iff.mpr (by simp)
    filter_upwards [h_ae_not_one] with u h_u_ne h_u_in
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h_u_in
    exact cpvIntegrandOnPer_eq_on_Ico γ S f ε
      ⟨h_u_in.1.le, lt_of_le_of_ne h_u_in.2 h_u_ne⟩
  rw [h_step1, h_step2, h_step3, h_step4]

private lemma limUnder_congr_eventually_local {α β : Type*} [Nonempty β] [TopologicalSpace β]
    {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) : limUnder l f = limUnder l g := by
  unfold limUnder
  congr 1
  exact Filter.map_congr h

private lemma cauchyPV_cyclicShift {γ : ClosedPwC1Immersion x} {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (z₀ : ℂ) (f : ℂ → ℂ) :
    cauchyPV f (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path z₀ =
      cauchyPV f γ.toPwC1Immersion.toPiecewiseC1Path z₀ := by
  unfold cauchyPV
  apply limUnder_congr_eventually_local
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Set.univ, Filter.univ_mem, fun ε _ => ?_⟩
  have h_lhs : (∫ t in (0:ℝ)..1, cpvIntegrand f
        (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path.toPath.extend z₀ ε t) =
      ∫ t in (0:ℝ)..1, cpvIntegrandOn {z₀} f
        (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t :=
    intervalIntegral.integral_congr fun _ _ => cpvIntegrand_eq_cpvIntegrandOn_singleton
  have h_rhs : (∫ t in (0:ℝ)..1, cpvIntegrand f
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend z₀ ε t) =
      ∫ t in (0:ℝ)..1, cpvIntegrandOn {z₀} f
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t :=
    intervalIntegral.integral_congr fun _ _ => cpvIntegrand_eq_cpvIntegrandOn_singleton
  show (∫ t in (0:ℝ)..1, cpvIntegrand f
        (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path.toPath.extend z₀ ε t) =
      ∫ t in (0:ℝ)..1, cpvIntegrand f
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend z₀ ε t
  rw [h_lhs, h_rhs]
  exact γ.cpvIntegrandOn_cyclicShift_integral_eq hτ {z₀} f ε

private lemma deriv_eventuallyEq_of_shift {f g : ℝ → ℂ} {t₀ c : ℝ}
    (h_eq : ∀ᶠ t in 𝓝 t₀, f t = g (t + c)) :
    ∀ᶠ t in 𝓝 t₀, deriv f t = deriv g (t + c) := by
  filter_upwards [eventually_eventually_nhds.mpr h_eq] with t ht
  rw [Filter.EventuallyEq.deriv_eq (ht : f =ᶠ[𝓝 t] _)]
  exact deriv_comp_add_const g c t

private lemma tendsto_add_const_nhdsGT (t₀ c : ℝ) :
    Tendsto (fun t : ℝ => t + c) (𝓝[>] t₀) (𝓝[>] (t₀ + c)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨((continuous_add_const c).tendsto t₀).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht using (add_lt_add_iff_right c).mpr ht

private lemma tendsto_add_const_nhdsLT (t₀ c : ℝ) :
    Tendsto (fun t : ℝ => t + c) (𝓝[<] t₀) (𝓝[<] (t₀ + c)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨((continuous_add_const c).tendsto t₀).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht using (add_lt_add_iff_right c).mpr ht

private lemma tendsto_sub_const_nhdsGT (t₀ c : ℝ) :
    Tendsto (fun t : ℝ => t - c) (𝓝[>] (t₀ + c)) (𝓝[>] t₀) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h_cont : Tendsto (fun t : ℝ => t - c) (𝓝 (t₀ + c)) (𝓝 ((t₀ + c) - c)) :=
      Continuous.tendsto (by fun_prop) _
    simpa using h_cont.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht using by
      change t₀ < t - c; linarith [show t₀ + c < t from ht]

private lemma tendsto_sub_const_nhdsLT (t₀ c : ℝ) :
    Tendsto (fun t : ℝ => t - c) (𝓝[<] (t₀ + c)) (𝓝[<] t₀) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h_cont : Tendsto (fun t : ℝ => t - c) (𝓝 (t₀ + c)) (𝓝 ((t₀ + c) - c)) :=
      Continuous.tendsto (by fun_prop) _
    simpa using h_cont.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht using by
      change t - c < t₀; linarith [show t < t₀ + c from ht]

private theorem mem_cyclicShift_partition_no_wrap_iff
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (0 : ℝ) (1 - τ)) :
    t₀' ∈ (γ.cyclicShift hτ).closedPartition ↔ t₀' + τ ∈ γ.closedPartition := by
  show t₀' ∈ cyclicShiftPartitionExt γ.closedPartition τ ↔ t₀' + τ ∈ γ.closedPartition
  rw [mem_cyclicShiftPartitionExt_iff]
  constructor
  · rintro (h0 | h1 | h1τ | hcs)
    · exact absurd h0 (ne_of_gt ht₀'.1)
    · exact absurd h1 (ne_of_lt (by linarith [ht₀'.2, hτ.1]))
    · exact absurd h1τ (ne_of_lt ht₀'.2)
    · rcases (mem_cyclicShiftPartition_iff γ.closedPartition τ t₀').mp hcs with
        ⟨_, h_in_partition⟩
      rcases h_in_partition with hp | hp
      · exact hp
      · exfalso
        have h_in_Icc : (t₀' + τ - 1 : ℝ) ∈ Icc (0 : ℝ) 1 := γ.closedPartition_subset hp
        linarith [h_in_Icc.1, ht₀'.2]
  · intro hp
    right; right; right
    rw [mem_cyclicShiftPartition_iff]
    exact ⟨⟨ht₀'.1.le, by linarith [ht₀'.2, hτ.1]⟩, Or.inl hp⟩

private theorem mem_cyclicShift_partition_wrap_iff
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (1 - τ) 1) :
    t₀' ∈ (γ.cyclicShift hτ).closedPartition ↔ t₀' + τ - 1 ∈ γ.closedPartition := by
  show t₀' ∈ cyclicShiftPartitionExt γ.closedPartition τ ↔ t₀' + τ - 1 ∈ γ.closedPartition
  rw [mem_cyclicShiftPartitionExt_iff]
  constructor
  · rintro (h0 | h1 | h1τ | hcs)
    · exact absurd h0.symm (ne_of_gt (by linarith [ht₀'.1, hτ.2]))
    · exact absurd h1 (ne_of_lt ht₀'.2)
    · exact absurd h1τ (ne_of_gt ht₀'.1)
    · rcases (mem_cyclicShiftPartition_iff γ.closedPartition τ t₀').mp hcs with
        ⟨_, h_in_partition⟩
      rcases h_in_partition with hp | hp
      · exfalso
        have h_in_Icc : (t₀' + τ : ℝ) ∈ Icc (0 : ℝ) 1 := γ.closedPartition_subset hp
        linarith [h_in_Icc.2, ht₀'.1]
      · exact hp
  · intro hp
    right; right; right
    rw [mem_cyclicShiftPartition_iff]
    exact ⟨⟨by linarith [ht₀'.1, hτ.2], ht₀'.2.le⟩, Or.inr hp⟩

private lemma exists_partition_isolating_nhd_no_wrap
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (0 : ℝ) (1 - τ)) :
    ∃ a b : ℝ, a < t₀' ∧ t₀' < b ∧ Ioo a b ⊆ Ioo (0 : ℝ) (1 - τ) ∧
      ((↑(γ.cyclicShift hτ).closedPartition : Set ℝ) ∩ Ioo a b) ⊆ {t₀'} := by
  classical
  set P : Finset ℝ := (γ.cyclicShift hτ).closedPartition
  set P' : Finset ℝ := P.erase t₀'
  set δ_box : ℝ := min t₀' (1 - τ - t₀')
  have hδ_box_pos : 0 < δ_box := lt_min ht₀'.1 (by linarith [ht₀'.2])
  by_cases hP'_empty : P'.Nonempty
  · have h_min_pos : ∀ p ∈ P', |t₀' - p| > 0 := fun p hp =>
      abs_pos.mpr (sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hp).1))
    set δ_pre : ℝ := P'.inf' hP'_empty (fun p => |t₀' - p|)
    have hδ_pre_pos : 0 < δ_pre := (Finset.lt_inf'_iff hP'_empty).mpr h_min_pos
    set δ : ℝ := min δ_box δ_pre
    have hδ_pos : 0 < δ := lt_min hδ_box_pos hδ_pre_pos
    have hδ_le_box : δ ≤ δ_box := min_le_left _ _
    have hδ_le_pre : δ ≤ δ_pre := min_le_right _ _
    refine ⟨t₀' - δ, t₀' + δ, by linarith, by linarith, ?_, ?_⟩
    · intro u hu
      exact ⟨by linarith [hu.1, hδ_le_box.trans (min_le_left _ _ : δ_box ≤ t₀')],
        by linarith [hu.2, hδ_le_box.trans (min_le_right _ _ : δ_box ≤ 1 - τ - t₀')]⟩
    · intro p ⟨hp_in_P, hp_Ioo⟩
      by_contra h_ne_t
      have h_abs : |t₀' - p| ≥ δ_pre :=
        Finset.inf'_le _ (Finset.mem_erase.mpr ⟨h_ne_t, hp_in_P⟩)
      have h_abs_lt_δ : |t₀' - p| < δ :=
        abs_lt.mpr ⟨by linarith [hp_Ioo.2], by linarith [hp_Ioo.1]⟩
      linarith
  · refine ⟨t₀' - δ_box, t₀' + δ_box, by linarith, by linarith, ?_, ?_⟩
    · intro u hu
      exact ⟨by linarith [hu.1, (min_le_left _ _ : δ_box ≤ t₀')],
        by linarith [hu.2, (min_le_right _ _ : δ_box ≤ 1 - τ - t₀')]⟩
    · intro p ⟨hp_in_P, _⟩
      by_contra h_ne
      exact absurd ((Finset.not_nonempty_iff_eq_empty.mp hP'_empty) ▸
        Finset.mem_erase.mpr ⟨h_ne, hp_in_P⟩) (Finset.notMem_empty p)

private lemma exists_partition_isolating_nhd_wrap
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (1 - τ) 1) :
    ∃ a b : ℝ, a < t₀' ∧ t₀' < b ∧ Ioo a b ⊆ Ioo (1 - τ) 1 ∧
      ((↑(γ.cyclicShift hτ).closedPartition : Set ℝ) ∩ Ioo a b) ⊆ {t₀'} := by
  classical
  set P : Finset ℝ := (γ.cyclicShift hτ).closedPartition
  set P' : Finset ℝ := P.erase t₀'
  set δ_box : ℝ := min (t₀' - (1 - τ)) (1 - t₀')
  have hδ_box_pos : 0 < δ_box := lt_min (by linarith [ht₀'.1]) (by linarith [ht₀'.2])
  by_cases hP'_empty : P'.Nonempty
  · have h_min_pos : ∀ p ∈ P', |t₀' - p| > 0 := fun p hp =>
      abs_pos.mpr (sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hp).1))
    set δ_pre : ℝ := P'.inf' hP'_empty (fun p => |t₀' - p|)
    have hδ_pre_pos : 0 < δ_pre := (Finset.lt_inf'_iff hP'_empty).mpr h_min_pos
    set δ : ℝ := min δ_box δ_pre
    have hδ_pos : 0 < δ := lt_min hδ_box_pos hδ_pre_pos
    have hδ_le_box : δ ≤ δ_box := min_le_left _ _
    have hδ_le_pre : δ ≤ δ_pre := min_le_right _ _
    refine ⟨t₀' - δ, t₀' + δ, by linarith, by linarith, ?_, ?_⟩
    · intro u hu
      exact ⟨by linarith [hu.1, hδ_le_box.trans (min_le_left _ _ : δ_box ≤ t₀' - (1 - τ))],
        by linarith [hu.2, hδ_le_box.trans (min_le_right _ _ : δ_box ≤ 1 - t₀')]⟩
    · intro p ⟨hp_in_P, hp_Ioo⟩
      by_contra h_ne_t
      have h_abs : |t₀' - p| ≥ δ_pre :=
        Finset.inf'_le _ (Finset.mem_erase.mpr ⟨h_ne_t, hp_in_P⟩)
      have h_abs_lt_δ : |t₀' - p| < δ :=
        abs_lt.mpr ⟨by linarith [hp_Ioo.2], by linarith [hp_Ioo.1]⟩
      linarith
  · refine ⟨t₀' - δ_box, t₀' + δ_box, by linarith, by linarith, ?_, ?_⟩
    · intro u hu
      exact ⟨by linarith [hu.1, (min_le_left _ _ : δ_box ≤ t₀' - (1 - τ))],
        by linarith [hu.2, (min_le_right _ _ : δ_box ≤ 1 - t₀')]⟩
    · intro p ⟨hp_in_P, _⟩
      by_contra h_ne
      exact absurd ((Finset.not_nonempty_iff_eq_empty.mp hP'_empty) ▸
        Finset.mem_erase.mpr ⟨h_ne, hp_in_P⟩) (Finset.notMem_empty p)

private lemma deriv_cyclicShift_eventuallyEq_left_no_wrap
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (0 : ℝ) (1 - τ)) :
    ∀ᶠ t in 𝓝[<] t₀', deriv (γ.cyclicShift hτ).toPath.extend t =
      deriv γ.toPath.extend (t + τ) := by
  obtain ⟨a, b, ha, hb, hab_sub, hP_iso⟩ :=
    γ.exists_partition_isolating_nhd_no_wrap hτ ht₀'
  filter_upwards [inter_mem_nhdsWithin _ (Ioo_mem_nhds ha hb)] with t ⟨ht_lt, ht_Ioo⟩
  refine γ.cyclicShift_deriv_eq_no_wrap hτ (hab_sub ht_Ioo) fun h_in => ?_
  exact (ne_of_lt ht_lt) (mem_singleton_iff.mp (hP_iso ⟨h_in, ht_Ioo⟩))

private lemma deriv_cyclicShift_eventuallyEq_right_no_wrap
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (0 : ℝ) (1 - τ)) :
    ∀ᶠ t in 𝓝[>] t₀', deriv (γ.cyclicShift hτ).toPath.extend t =
      deriv γ.toPath.extend (t + τ) := by
  obtain ⟨a, b, ha, hb, hab_sub, hP_iso⟩ :=
    γ.exists_partition_isolating_nhd_no_wrap hτ ht₀'
  filter_upwards [inter_mem_nhdsWithin _ (Ioo_mem_nhds ha hb)] with t ⟨ht_gt, ht_Ioo⟩
  refine γ.cyclicShift_deriv_eq_no_wrap hτ (hab_sub ht_Ioo) fun h_in => ?_
  exact (ne_of_gt ht_gt) (mem_singleton_iff.mp (hP_iso ⟨h_in, ht_Ioo⟩))

private lemma deriv_cyclicShift_eventuallyEq_left_wrap
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (1 - τ) 1) :
    ∀ᶠ t in 𝓝[<] t₀', deriv (γ.cyclicShift hτ).toPath.extend t =
      deriv γ.toPath.extend (t + τ - 1) := by
  obtain ⟨a, b, ha, hb, hab_sub, hP_iso⟩ :=
    γ.exists_partition_isolating_nhd_wrap hτ ht₀'
  filter_upwards [inter_mem_nhdsWithin _ (Ioo_mem_nhds ha hb)] with t ⟨ht_lt, ht_Ioo⟩
  refine γ.cyclicShift_deriv_eq_wrap hτ (hab_sub ht_Ioo) fun h_in => ?_
  exact (ne_of_lt ht_lt) (mem_singleton_iff.mp (hP_iso ⟨h_in, ht_Ioo⟩))

private lemma deriv_cyclicShift_eventuallyEq_right_wrap
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (1 - τ) 1) :
    ∀ᶠ t in 𝓝[>] t₀', deriv (γ.cyclicShift hτ).toPath.extend t =
      deriv γ.toPath.extend (t + τ - 1) := by
  obtain ⟨a, b, ha, hb, hab_sub, hP_iso⟩ :=
    γ.exists_partition_isolating_nhd_wrap hτ ht₀'
  filter_upwards [inter_mem_nhdsWithin _ (Ioo_mem_nhds ha hb)] with t ⟨ht_gt, ht_Ioo⟩
  refine γ.cyclicShift_deriv_eq_wrap hτ (hab_sub ht_Ioo) fun h_in => ?_
  exact (ne_of_gt ht_gt) (mem_singleton_iff.mp (hP_iso ⟨h_in, ht_Ioo⟩))

end ClosedPwC1Immersion

end
