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
      t ∉ ((γ.cyclicShift hτ).partition : Set ℝ) :=
    MeasureTheory.compl_mem_ae_iff.mpr (Finset.measure_zero _ _)
  filter_upwards [hP_nmem] with t ht_nmem ht_in
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht_in
  obtain ⟨ht_pos, ht_le⟩ := ht_in
  have h_contra : ∀ {c : ℝ}, t = c → c ∈ cyclicShiftPartitionExt γ.partition τ → False :=
    fun ht_eq hc => ht_nmem (show t ∈ ((γ.cyclicShift hτ).partition : Set ℝ) by
      rw [ht_eq]; exact_mod_cast hc)
  by_cases ht_le_oneSubTau : t ≤ 1 - τ
  · have ht_Ioo : t ∈ Ioo (0 : ℝ) (1 - τ) := by
      refine ⟨ht_pos, ?_⟩
      rcases lt_or_eq_of_le ht_le_oneSubTau with ht_lt | ht_eq
      · exact ht_lt
      · exact absurd (oneSubTau_mem_cyclicShiftPartitionExt γ.partition τ) (h_contra ht_eq)
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
        h_contra h_eq (one_mem_cyclicShiftPartitionExt γ.partition τ)
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

/-- **Invariance of `HasCauchyPVOn` under cyclic shift.** -/
theorem hasCauchyPVOn_cyclicShift {γ : ClosedPwC1Immersion x} {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (S : Finset ℂ) (f : ℂ → ℂ) (L : ℂ) :
    HasCauchyPVOn S f (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path L ↔
      HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path L := by
  unfold HasCauchyPVOn
  exact ⟨fun h => h.congr fun ε => γ.cpvIntegrandOn_cyclicShift_integral_eq hτ S f ε,
    fun h => h.congr fun ε => (γ.cpvIntegrandOn_cyclicShift_integral_eq hτ S f ε).symm⟩

private lemma limUnder_congr_eventually_local {α β : Type*} [Nonempty β] [TopologicalSpace β]
    {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) : limUnder l f = limUnder l g := by
  unfold limUnder
  congr 1
  exact Filter.map_congr h

/-- The Cauchy principal value (extracted as a value, not a Tendsto witness) is
invariant under cyclic shift. -/
theorem cauchyPVOn_cyclicShift {γ : ClosedPwC1Immersion x} {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (S : Finset ℂ) (f : ℂ → ℂ) :
    cauchyPVOn S f (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path =
      cauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path := by
  unfold cauchyPVOn
  apply limUnder_congr_eventually_local
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Set.univ, univ_mem, fun ε _ => ?_⟩
  exact γ.cpvIntegrandOn_cyclicShift_integral_eq hτ S f ε

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

/-- **Invariance of `generalizedWindingNumber` under cyclic shift.** -/
theorem generalizedWindingNumber_cyclicShift {γ : ClosedPwC1Immersion x} {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (s : ℂ) :
    generalizedWindingNumber
        (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path s =
      generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s := by
  simp only [generalizedWindingNumber, cauchyPV_cyclicShift hτ s]

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

private lemma isFlatOfOrder_of_eventuallyEq_shift {f g : ℝ → ℂ} {t₀ c : ℝ} {n : ℕ}
    (h_eq : ∀ᶠ t in 𝓝 t₀, f t = g (t + c))
    (h_g : IsFlatOfOrder g (t₀ + c) n) :
    IsFlatOfOrder f t₀ n := by
  have h_val : f t₀ = g (t₀ + c) := h_eq.self_of_nhds
  have h_eq_right : f =ᶠ[𝓝[>] t₀] (fun t => g (t + c)) := h_eq.filter_mono nhdsWithin_le_nhds
  have h_eq_left : f =ᶠ[𝓝[<] t₀] (fun t => g (t + c)) := h_eq.filter_mono nhdsWithin_le_nhds
  have h_deriv := deriv_eventuallyEq_of_shift h_eq
  have h_deriv_right : (deriv f) =ᶠ[𝓝[>] t₀] (fun t => deriv g (t + c)) :=
    h_deriv.filter_mono nhdsWithin_le_nhds
  have h_deriv_left : (deriv f) =ᶠ[𝓝[<] t₀] (fun t => deriv g (t + c)) :=
    h_deriv.filter_mono nhdsWithin_le_nhds
  refine ⟨?_, ?_⟩
  · intro L hL hL_lim
    have h_shift_to_g : Tendsto (fun t => deriv g (t + c)) (𝓝[>] t₀) (𝓝 L) :=
      hL_lim.congr' h_deriv_right
    have hL_lim_g : Tendsto (deriv g) (𝓝[>] (t₀ + c)) (𝓝 L) :=
      (h_shift_to_g.comp (tendsto_sub_const_nhdsGT t₀ c)).congr
        fun t => by simp [sub_add_cancel]
    have h_comp := (h_g.right_flat L hL hL_lim_g).comp_tendsto
      (tendsto_add_const_nhdsGT t₀ c)
    refine h_comp.congr' ?_ ?_ <;>
      (filter_upwards [h_eq_right] with t ht; simp only [Function.comp_apply];
        rw [← ht, ← h_val])
  · intro L hL hL_lim
    have h_shift_to_g : Tendsto (fun t => deriv g (t + c)) (𝓝[<] t₀) (𝓝 L) :=
      hL_lim.congr' h_deriv_left
    have hL_lim_g : Tendsto (deriv g) (𝓝[<] (t₀ + c)) (𝓝 L) :=
      (h_shift_to_g.comp (tendsto_sub_const_nhdsLT t₀ c)).congr
        fun t => by simp [sub_add_cancel]
    have h_comp := (h_g.left_flat L hL hL_lim_g).comp_tendsto
      (tendsto_add_const_nhdsLT t₀ c)
    refine h_comp.congr' ?_ ?_ <;>
      (filter_upwards [h_eq_left] with t ht; simp only [Function.comp_apply];
        rw [← ht, ← h_val])

/-- The image of the cyclic-shifted path is contained in the image of the original path. -/
theorem cyclicShift_image_subset {γ : ClosedPwC1Immersion x} {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∃ u ∈ Icc (0 : ℝ) 1,
      (γ.cyclicShift hτ).toPath.extend t = γ.toPath.extend u := by
  intro t ht
  by_cases ht_le : t ≤ 1 - τ
  · refine ⟨t + τ, ⟨?_, ?_⟩, ?_⟩
    · linarith [ht.1, hτ.1]
    · linarith
    · exact γ.cyclicShift_extend_eq_no_wrap hτ ⟨ht.1, ht_le⟩
  · push Not at ht_le
    refine ⟨t + τ - 1, ⟨?_, ?_⟩, ?_⟩
    · linarith
    · linarith [ht.2, hτ.2]
    · exact γ.cyclicShift_extend_eq_wrap hτ ⟨ht_le.le, ht.2⟩

/-- **Invariance of `IsNullHomologous` under cyclic shift.** -/
theorem isNullHomologous_cyclicShift {γ : ClosedPwC1Immersion x} {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) {U : Set ℂ}
    (h : IsNullHomologous γ.toPwC1Immersion U) :
    IsNullHomologous (γ.cyclicShift hτ).toPwC1Immersion U where
  image_subset := by
    intro t ht
    obtain ⟨u, hu, heq⟩ := γ.cyclicShift_image_subset hτ t ht
    rw [show (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path t =
      (γ.cyclicShift hτ).toPath.extend t from rfl, heq]
    exact h.image_subset u hu
  winding_zero := by
    intro z hz
    rw [γ.generalizedWindingNumber_cyclicShift hτ z]
    exact h.winding_zero z hz

/-- **Cyclic-shift invariance of `SatisfiesConditionA'`** (T-BR-Y9h-A).

The pole orders `ord s` for `s ∈ S` are transported along the cyclic shift via
affine parameter substitution.  At the breakpoint `1 - τ` (corresponding to the
old basepoint `x`), the conclusion is the automatic order-1 flatness of
piecewise `C¹` curves; for callers with `ord s ≤ 1` at the breakpoint, the
proof goes through directly via `IsFlatOfOrder.of_le`.

**Hypothesis `h_basepoint_ord`**: for `s ∈ S` with `γ(0) = s` (i.e., `s` is the
basepoint), the pole order `ord s` is at most 1.  This is satisfied in typical
applications where the basepoint is either outside `S` (vacuous premise) or has
a simple pole. -/
theorem satisfiesConditionA'_cyclicShift
    {γ : ClosedPwC1Immersion x} {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1)
    {S : Finset ℂ} {f : ℂ → ℂ} {ord : ℂ → ℕ}
    (h_basepoint_ord : ∀ s ∈ S, γ.toPath.extend 1 = s → ord s ≤ 1)
    (h : SatisfiesConditionA' γ.toPwC1Immersion f S ord) :
    SatisfiesConditionA' (γ.cyclicShift hτ).toPwC1Immersion f S ord := by
  intro s hs t₀' ht_Icc h_at ht_Ioo
  rcases lt_trichotomy t₀' (1 - τ) with ht_lt | ht_eq | ht_gt
  · have ht_Ioo_nw : t₀' ∈ Ioo (0 : ℝ) (1 - τ) := ⟨ht_Ioo.1, ht_lt⟩
    set t₀ := t₀' + τ
    have ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1 :=
      ⟨by linarith [hτ.1, ht_Ioo.1], by linarith [ht_lt]⟩
    have ht₀_Icc : t₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht₀_Ioo
    have h_γt₀_eq_s : (γ.toPwC1Immersion : ℝ → ℂ) t₀ = s := by
      show γ.toPath.extend t₀ = s
      rw [← γ.cyclicShift_extend_eq_no_wrap hτ ⟨ht_Ioo.1.le, ht_lt.le⟩]
      exact h_at
    have h_flat_γ : IsFlatOfOrder (γ.toPwC1Immersion : ℝ → ℂ) t₀ (ord s) :=
      h s hs t₀ ht₀_Icc h_γt₀_eq_s ht₀_Ioo
    have h_eq_nbhd : ∀ᶠ t in 𝓝 t₀',
        ((γ.cyclicShift hτ).toPwC1Immersion : ℝ → ℂ) t = γ.toPath.extend (t + τ) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht_Ioo_nw] with t ht
      exact γ.cyclicShift_extend_eq_no_wrap hτ ⟨ht.1.le, ht.2.le⟩
    exact isFlatOfOrder_of_eventuallyEq_shift h_eq_nbhd (h_flat_γ : IsFlatOfOrder _ (t₀' + τ) _)
  · have h_s_eq : γ.toPath.extend 1 = s := by
      have h_step : (γ.cyclicShift hτ).toPath.extend t₀' = γ.toPath.extend 1 := by
        rw [γ.cyclicShift_extend_eq_no_wrap hτ ⟨ht_Ioo.1.le, ht_eq.le⟩]
        congr 1; linarith [ht_eq]
      rw [← h_step]; exact h_at
    have h_cont : ContinuousAt ((γ.cyclicShift hτ).toPwC1Immersion : ℝ → ℂ) t₀' :=
      (γ.cyclicShift hτ).toPwC1Immersion.continuous.continuousAt
    exact (isFlatOfOrder_one (γ.cyclicShift hτ).toPwC1Immersion t₀' ht_Ioo).of_le
      (h_basepoint_ord s hs h_s_eq) h_cont
  · have ht_Ioo_w : t₀' ∈ Ioo (1 - τ) 1 := ⟨ht_gt, ht_Ioo.2⟩
    set t₀ := t₀' + τ - 1
    have ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1 :=
      ⟨by linarith [ht_gt], by linarith [hτ.2, ht_Ioo.2]⟩
    have ht₀_Icc : t₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht₀_Ioo
    have h_γt₀_eq_s : (γ.toPwC1Immersion : ℝ → ℂ) t₀ = s := by
      show γ.toPath.extend t₀ = s
      rw [← γ.cyclicShift_extend_eq_wrap hτ ⟨ht_gt.le, ht_Ioo.2.le⟩]
      exact h_at
    have h_flat_γ : IsFlatOfOrder (γ.toPwC1Immersion : ℝ → ℂ) t₀ (ord s) :=
      h s hs t₀ ht₀_Icc h_γt₀_eq_s ht₀_Ioo
    have h_eq_nbhd : ∀ᶠ t in 𝓝 t₀',
        ((γ.cyclicShift hτ).toPwC1Immersion : ℝ → ℂ) t = γ.toPath.extend (t + (τ - 1)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht_Ioo_w] with t ht
      show (γ.cyclicShift hτ).toPath.extend t = γ.toPath.extend (t + (τ - 1))
      have h_eq : γ.toPath.extend (t + τ - 1) = γ.toPath.extend (t + (τ - 1)) := by
        congr 1; ring
      rw [← h_eq]
      exact γ.cyclicShift_extend_eq_wrap hτ ⟨ht.1.le, ht.2.le⟩
    have h_flat_γ' : IsFlatOfOrder γ.toPath.extend (t₀' + (τ - 1)) (ord s) := by
      have h_pt : t₀' + (τ - 1) = t₀ := by show t₀' + (τ - 1) = t₀' + τ - 1; ring
      rw [h_pt]; exact h_flat_γ
    exact isFlatOfOrder_of_eventuallyEq_shift h_eq_nbhd h_flat_γ'

private theorem mem_cyclicShift_partition_no_wrap_iff
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (0 : ℝ) (1 - τ)) :
    t₀' ∈ (γ.cyclicShift hτ).partition ↔ t₀' + τ ∈ γ.partition := by
  show t₀' ∈ cyclicShiftPartitionExt γ.partition τ ↔ t₀' + τ ∈ γ.partition
  rw [mem_cyclicShiftPartitionExt_iff]
  constructor
  · rintro (h0 | h1 | h1τ | hcs)
    · exact absurd h0 (ne_of_gt ht₀'.1)
    · exact absurd h1 (ne_of_lt (by linarith [ht₀'.2, hτ.1]))
    · exact absurd h1τ (ne_of_lt ht₀'.2)
    · rcases (mem_cyclicShiftPartition_iff γ.partition τ t₀').mp hcs with ⟨_, h_in_partition⟩
      rcases h_in_partition with hp | hp
      · exact hp
      · exfalso
        have h_in_Icc : (t₀' + τ - 1 : ℝ) ∈ Icc (0 : ℝ) 1 := γ.partition_subset hp
        linarith [h_in_Icc.1, ht₀'.2]
  · intro hp
    right; right; right
    rw [mem_cyclicShiftPartition_iff]
    exact ⟨⟨ht₀'.1.le, by linarith [ht₀'.2, hτ.1]⟩, Or.inl hp⟩

private theorem mem_cyclicShift_partition_wrap_iff
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (1 - τ) 1) :
    t₀' ∈ (γ.cyclicShift hτ).partition ↔ t₀' + τ - 1 ∈ γ.partition := by
  show t₀' ∈ cyclicShiftPartitionExt γ.partition τ ↔ t₀' + τ - 1 ∈ γ.partition
  rw [mem_cyclicShiftPartitionExt_iff]
  constructor
  · rintro (h0 | h1 | h1τ | hcs)
    · exact absurd h0.symm (ne_of_gt (by linarith [ht₀'.1, hτ.2]))
    · exact absurd h1 (ne_of_lt ht₀'.2)
    · exact absurd h1τ (ne_of_gt ht₀'.1)
    · rcases (mem_cyclicShiftPartition_iff γ.partition τ t₀').mp hcs with ⟨_, h_in_partition⟩
      rcases h_in_partition with hp | hp
      · exfalso
        have h_in_Icc : (t₀' + τ : ℝ) ∈ Icc (0 : ℝ) 1 := γ.partition_subset hp
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
      ((↑(γ.cyclicShift hτ).partition : Set ℝ) ∩ Ioo a b) ⊆ {t₀'} := by
  classical
  set P : Finset ℝ := (γ.cyclicShift hτ).partition
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
      ((↑(γ.cyclicShift hτ).partition : Set ℝ) ∩ Ioo a b) ⊆ {t₀'} := by
  classical
  set P : Finset ℝ := (γ.cyclicShift hτ).partition
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

private theorem angleAtCrossing_cyclicShift_no_wrap
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (0 : ℝ) (1 - τ))
    (ht₀'_Ioo : t₀' ∈ Ioo (0 : ℝ) 1)
    (ht₀_Ioo : t₀' + τ ∈ Ioo (0 : ℝ) 1) :
    angleAtCrossing (γ.cyclicShift hτ).toPwC1Immersion t₀' ht₀'_Ioo =
      angleAtCrossing γ.toPwC1Immersion (t₀' + τ) ht₀_Ioo := by
  classical
  by_cases h_part : t₀' ∈ (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path.partition
  · have h_part_orig : t₀' ∈ (γ.cyclicShift hτ).partition := by
      change t₀' ∈ ((γ.cyclicShift hτ).partition.erase 0).erase 1 at h_part
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp h_part).2).2
    have h_partγ : (t₀' + τ) ∈ γ.partition :=
      (γ.mem_cyclicShift_partition_no_wrap_iff hτ ht₀').mp h_part_orig
    have h_partγ_legacy : (t₀' + τ) ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition := by
      change (t₀' + τ) ∈ (γ.partition.erase 0).erase 1
      exact Finset.mem_erase.mpr ⟨ne_of_lt (by linarith [ht₀'.2]),
        Finset.mem_erase.mpr ⟨ne_of_gt (by linarith [ht₀'.1, hτ.1]), h_partγ⟩⟩
    simp only [angleAtCrossing, h_part, h_partγ_legacy, dite_true]
    set Lγ'_left := Classical.choose
      ((γ.cyclicShift hτ).toPwC1Immersion.left_deriv_limit t₀' h_part)
    set Lγ'_right := Classical.choose
      ((γ.cyclicShift hτ).toPwC1Immersion.right_deriv_limit t₀' h_part)
    set Lγ_left := Classical.choose
      (γ.toPwC1Immersion.left_deriv_limit (t₀' + τ) h_partγ_legacy)
    set Lγ_right := Classical.choose
      (γ.toPwC1Immersion.right_deriv_limit (t₀' + τ) h_partγ_legacy)
    have hLγ'_left_spec := Classical.choose_spec
      ((γ.cyclicShift hτ).toPwC1Immersion.left_deriv_limit t₀' h_part)
    have hLγ'_right_spec := Classical.choose_spec
      ((γ.cyclicShift hτ).toPwC1Immersion.right_deriv_limit t₀' h_part)
    have hLγ_left_spec := Classical.choose_spec
      (γ.toPwC1Immersion.left_deriv_limit (t₀' + τ) h_partγ_legacy)
    have hLγ_right_spec := Classical.choose_spec
      (γ.toPwC1Immersion.right_deriv_limit (t₀' + τ) h_partγ_legacy)
    have h_tend_shifted_left : Tendsto (fun t => deriv γ.toPath.extend (t + τ))
        (𝓝[<] t₀') (𝓝 Lγ'_left) :=
      hLγ'_left_spec.2.congr' (γ.deriv_cyclicShift_eventuallyEq_left_no_wrap hτ ht₀')
    have h_tend_shifted_right : Tendsto (fun t => deriv γ.toPath.extend (t + τ))
        (𝓝[>] t₀') (𝓝 Lγ'_right) :=
      hLγ'_right_spec.2.congr' (γ.deriv_cyclicShift_eventuallyEq_right_no_wrap hτ ht₀')
    have h_tend_γ_left' : Tendsto (deriv γ.toPath.extend)
        (𝓝[<] (t₀' + τ)) (𝓝 Lγ'_left) :=
      (h_tend_shifted_left.comp (tendsto_sub_const_nhdsLT t₀' τ)).congr
        fun t => by simp [sub_add_cancel]
    have h_tend_γ_right' : Tendsto (deriv γ.toPath.extend)
        (𝓝[>] (t₀' + τ)) (𝓝 Lγ'_right) :=
      (h_tend_shifted_right.comp (tendsto_sub_const_nhdsGT t₀' τ)).congr
        fun t => by simp [sub_add_cancel]
    rw [tendsto_nhds_unique h_tend_γ_left' hLγ_left_spec.2,
      tendsto_nhds_unique h_tend_γ_right' hLγ_right_spec.2]
  · have h_part_orig : t₀' ∉ (γ.cyclicShift hτ).partition := fun h_in =>
      h_part (Finset.mem_erase.mpr ⟨ne_of_lt ht₀'_Ioo.2,
        Finset.mem_erase.mpr ⟨ne_of_gt ht₀'_Ioo.1, h_in⟩⟩)
    have h_partγ_nope : (t₀' + τ) ∉ γ.partition := fun h =>
      h_part_orig ((γ.mem_cyclicShift_partition_no_wrap_iff hτ ht₀').mpr h)
    have h_partγ_legacy : (t₀' + τ) ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition := fun h_in =>
      h_partγ_nope (Finset.mem_erase.mp (Finset.mem_erase.mp h_in).2).2
    rw [angleAtCrossing_smooth _ _ ht₀'_Ioo h_part,
      angleAtCrossing_smooth _ _ ht₀_Ioo h_partγ_legacy]

private theorem angleAtCrossing_cyclicShift_wrap
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (1 - τ) 1)
    (ht₀'_Ioo : t₀' ∈ Ioo (0 : ℝ) 1)
    (ht₀_Ioo : t₀' + τ - 1 ∈ Ioo (0 : ℝ) 1) :
    angleAtCrossing (γ.cyclicShift hτ).toPwC1Immersion t₀' ht₀'_Ioo =
      angleAtCrossing γ.toPwC1Immersion (t₀' + τ - 1) ht₀_Ioo := by
  classical
  by_cases h_part : t₀' ∈ (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path.partition
  · have h_part_orig : t₀' ∈ (γ.cyclicShift hτ).partition := by
      change t₀' ∈ ((γ.cyclicShift hτ).partition.erase 0).erase 1 at h_part
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp h_part).2).2
    have h_partγ : (t₀' + τ - 1) ∈ γ.partition :=
      (γ.mem_cyclicShift_partition_wrap_iff hτ ht₀').mp h_part_orig
    have h_partγ_legacy : (t₀' + τ - 1) ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition := by
      change (t₀' + τ - 1) ∈ (γ.partition.erase 0).erase 1
      exact Finset.mem_erase.mpr ⟨ne_of_lt (by linarith [ht₀'.2, hτ.2]),
        Finset.mem_erase.mpr ⟨ne_of_gt (by linarith [ht₀'.1]), h_partγ⟩⟩
    simp only [angleAtCrossing, h_part, h_partγ_legacy, dite_true]
    set Lγ'_left := Classical.choose
      ((γ.cyclicShift hτ).toPwC1Immersion.left_deriv_limit t₀' h_part)
    set Lγ'_right := Classical.choose
      ((γ.cyclicShift hτ).toPwC1Immersion.right_deriv_limit t₀' h_part)
    set Lγ_left := Classical.choose
      (γ.toPwC1Immersion.left_deriv_limit (t₀' + τ - 1) h_partγ_legacy)
    set Lγ_right := Classical.choose
      (γ.toPwC1Immersion.right_deriv_limit (t₀' + τ - 1) h_partγ_legacy)
    have hLγ'_left_spec := Classical.choose_spec
      ((γ.cyclicShift hτ).toPwC1Immersion.left_deriv_limit t₀' h_part)
    have hLγ'_right_spec := Classical.choose_spec
      ((γ.cyclicShift hτ).toPwC1Immersion.right_deriv_limit t₀' h_part)
    have hLγ_left_spec := Classical.choose_spec
      (γ.toPwC1Immersion.left_deriv_limit (t₀' + τ - 1) h_partγ_legacy)
    have hLγ_right_spec := Classical.choose_spec
      (γ.toPwC1Immersion.right_deriv_limit (t₀' + τ - 1) h_partγ_legacy)
    have h_tend_shifted_left : Tendsto (fun t => deriv γ.toPath.extend (t + τ - 1))
        (𝓝[<] t₀') (𝓝 Lγ'_left) :=
      hLγ'_left_spec.2.congr' (γ.deriv_cyclicShift_eventuallyEq_left_wrap hτ ht₀')
    have h_tend_shifted_right : Tendsto (fun t => deriv γ.toPath.extend (t + τ - 1))
        (𝓝[>] t₀') (𝓝 Lγ'_right) :=
      hLγ'_right_spec.2.congr' (γ.deriv_cyclicShift_eventuallyEq_right_wrap hτ ht₀')
    have h_shift_back_left : Tendsto (fun u : ℝ => u - (τ - 1))
        (𝓝[<] (t₀' + τ - 1)) (𝓝[<] t₀') := by
      have h_pt : (t₀' + (τ - 1)) = (t₀' + τ - 1) := by ring
      rw [← h_pt]; exact tendsto_sub_const_nhdsLT t₀' (τ - 1)
    have h_shift_back_right : Tendsto (fun u : ℝ => u - (τ - 1))
        (𝓝[>] (t₀' + τ - 1)) (𝓝[>] t₀') := by
      have h_pt : (t₀' + (τ - 1)) = (t₀' + τ - 1) := by ring
      rw [← h_pt]; exact tendsto_sub_const_nhdsGT t₀' (τ - 1)
    have h_tend_γ_left' : Tendsto (deriv γ.toPath.extend)
        (𝓝[<] (t₀' + τ - 1)) (𝓝 Lγ'_left) :=
      (h_tend_shifted_left.comp h_shift_back_left).congr fun u => by
        show deriv γ.toPath.extend ((u - (τ - 1)) + τ - 1) = deriv γ.toPath.extend u
        congr 1; ring
    have h_tend_γ_right' : Tendsto (deriv γ.toPath.extend)
        (𝓝[>] (t₀' + τ - 1)) (𝓝 Lγ'_right) :=
      (h_tend_shifted_right.comp h_shift_back_right).congr fun u => by
        show deriv γ.toPath.extend ((u - (τ - 1)) + τ - 1) = deriv γ.toPath.extend u
        congr 1; ring
    rw [tendsto_nhds_unique h_tend_γ_left' hLγ_left_spec.2,
      tendsto_nhds_unique h_tend_γ_right' hLγ_right_spec.2]
  · have h_part_orig : t₀' ∉ (γ.cyclicShift hτ).partition := fun h_in =>
      h_part (Finset.mem_erase.mpr ⟨ne_of_lt ht₀'_Ioo.2,
        Finset.mem_erase.mpr ⟨ne_of_gt ht₀'_Ioo.1, h_in⟩⟩)
    have h_partγ_nope : (t₀' + τ - 1) ∉ γ.partition := fun h =>
      h_part_orig ((γ.mem_cyclicShift_partition_wrap_iff hτ ht₀').mpr h)
    have h_partγ_legacy : (t₀' + τ - 1) ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition :=
      fun h_in => h_partγ_nope (Finset.mem_erase.mp (Finset.mem_erase.mp h_in).2).2
    rw [angleAtCrossing_smooth _ _ ht₀'_Ioo h_part,
      angleAtCrossing_smooth _ _ ht₀_Ioo h_partγ_legacy]

/-- **Cyclic-shift invariance of `SatisfiesConditionB`** (T-BR-Y9h-B).

The angle rationality and Laurent compatibility conditions transport along the
cyclic shift. For non-breakpoint crossings, this uses
`angleAtCrossing_cyclicShift_{no_wrap,wrap}` for invariance of the crossing angle.

At the breakpoint `1 - τ` (corresponding to the old basepoint `x`), the
conclusion is supplied by the basepoint hypotheses, which are vacuous when
`x ∉ S`. -/
theorem satisfiesConditionB_cyclicShift
    {γ : ClosedPwC1Immersion x} {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1)
    {S : Finset ℂ} {f : ℂ → ℂ}
    (h_basepoint_angleB : ∀ s ∈ S, γ.toPath.extend 1 = s →
      ∀ ht_oneSubTau : (1 - τ) ∈ Ioo (0 : ℝ) 1,
        ∃ p q : ℕ, q ≠ 0 ∧ Nat.Coprime p q ∧
          angleAtCrossing (γ.cyclicShift hτ).toPwC1Immersion (1 - τ) ht_oneSubTau =
            ↑p * Real.pi / ↑q)
    (h_basepoint_laurentB : ∀ s ∈ S, γ.toPath.extend 1 = s →
      ∀ ht_oneSubTau : (1 - τ) ∈ Ioo (0 : ℝ) 1,
        ∃ (N : ℕ) (a : Fin N → ℂ) (g : ℂ → ℂ),
          AnalyticAt ℂ g s ∧
          (∀ᶠ z in 𝓝[≠] s, f z = g z +
            ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) ∧
          (∀ k : Fin N, a k ≠ 0 → k.val ≥ 1 →
            ∃ m : ℤ, (↑k.val : ℝ) *
              angleAtCrossing (γ.cyclicShift hτ).toPwC1Immersion (1 - τ) ht_oneSubTau =
              ↑m * (2 * Real.pi)))
    (h : SatisfiesConditionB γ.toPwC1Immersion f S) :
    SatisfiesConditionB (γ.cyclicShift hτ).toPwC1Immersion f S := by
  refine ⟨?_, ?_⟩
  · intro s hs t₀' ht_Icc h_at ht_Ioo
    rcases lt_trichotomy t₀' (1 - τ) with ht_lt | ht_eq | ht_gt
    · have ht_Ioo_nw : t₀' ∈ Ioo (0 : ℝ) (1 - τ) := ⟨ht_Ioo.1, ht_lt⟩
      set t₀ := t₀' + τ
      have ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1 :=
        ⟨by linarith [hτ.1, ht_Ioo.1], by linarith [ht_lt]⟩
      have h_γt₀_eq_s : (γ.toPwC1Immersion : ℝ → ℂ) t₀ = s := by
        show γ.toPath.extend t₀ = s
        rw [← γ.cyclicShift_extend_eq_no_wrap hτ ⟨ht_Ioo.1.le, ht_lt.le⟩]; exact h_at
      obtain ⟨p, q, hq_ne, hpq_coprime, h_angle⟩ :=
        h.angle_rational s hs t₀ (Ioo_subset_Icc_self ht₀_Ioo) h_γt₀_eq_s ht₀_Ioo
      refine ⟨p, q, hq_ne, hpq_coprime, ?_⟩
      rw [γ.angleAtCrossing_cyclicShift_no_wrap hτ ht_Ioo_nw ht_Ioo ht₀_Ioo, h_angle]
    · have h_s_eq : γ.toPath.extend 1 = s := by
        have h_step : (γ.cyclicShift hτ).toPath.extend t₀' = γ.toPath.extend 1 := by
          rw [γ.cyclicShift_extend_eq_no_wrap hτ ⟨ht_Ioo.1.le, ht_eq.le⟩]
          congr 1; linarith [ht_eq]
        rw [← h_step]; exact h_at
      subst ht_eq
      exact h_basepoint_angleB s hs h_s_eq ht_Ioo
    · have ht_Ioo_w : t₀' ∈ Ioo (1 - τ) 1 := ⟨ht_gt, ht_Ioo.2⟩
      set t₀ := t₀' + τ - 1
      have ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1 :=
        ⟨by linarith [ht_gt], by linarith [hτ.2, ht_Ioo.2]⟩
      have h_γt₀_eq_s : (γ.toPwC1Immersion : ℝ → ℂ) t₀ = s := by
        show γ.toPath.extend t₀ = s
        rw [← γ.cyclicShift_extend_eq_wrap hτ ⟨ht_gt.le, ht_Ioo.2.le⟩]; exact h_at
      obtain ⟨p, q, hq_ne, hpq_coprime, h_angle⟩ :=
        h.angle_rational s hs t₀ (Ioo_subset_Icc_self ht₀_Ioo) h_γt₀_eq_s ht₀_Ioo
      refine ⟨p, q, hq_ne, hpq_coprime, ?_⟩
      rw [γ.angleAtCrossing_cyclicShift_wrap hτ ht_Ioo_w ht_Ioo ht₀_Ioo, h_angle]
  · intro s hs t₀' ht_Icc h_at ht_Ioo
    rcases lt_trichotomy t₀' (1 - τ) with ht_lt | ht_eq | ht_gt
    · have ht_Ioo_nw : t₀' ∈ Ioo (0 : ℝ) (1 - τ) := ⟨ht_Ioo.1, ht_lt⟩
      set t₀ := t₀' + τ
      have ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1 :=
        ⟨by linarith [hτ.1, ht_Ioo.1], by linarith [ht_lt]⟩
      have h_γt₀_eq_s : (γ.toPwC1Immersion : ℝ → ℂ) t₀ = s := by
        show γ.toPath.extend t₀ = s
        rw [← γ.cyclicShift_extend_eq_no_wrap hτ ⟨ht_Ioo.1.le, ht_lt.le⟩]; exact h_at
      obtain ⟨N, a, g, hg_analytic, hf_eq, h_angle_cond⟩ :=
        h.laurent_compatible s hs t₀ (Ioo_subset_Icc_self ht₀_Ioo) h_γt₀_eq_s ht₀_Ioo
      refine ⟨N, a, g, hg_analytic, hf_eq, fun k hk_ne hk_ge => ?_⟩
      obtain ⟨m, hm⟩ := h_angle_cond k hk_ne hk_ge
      exact ⟨m, by rw [γ.angleAtCrossing_cyclicShift_no_wrap hτ ht_Ioo_nw ht_Ioo ht₀_Ioo]; exact hm⟩
    · have h_s_eq : γ.toPath.extend 1 = s := by
        have h_step : (γ.cyclicShift hτ).toPath.extend t₀' = γ.toPath.extend 1 := by
          rw [γ.cyclicShift_extend_eq_no_wrap hτ ⟨ht_Ioo.1.le, ht_eq.le⟩]
          congr 1; linarith [ht_eq]
        rw [← h_step]; exact h_at
      subst ht_eq
      exact h_basepoint_laurentB s hs h_s_eq ht_Ioo
    · have ht_Ioo_w : t₀' ∈ Ioo (1 - τ) 1 := ⟨ht_gt, ht_Ioo.2⟩
      set t₀ := t₀' + τ - 1
      have ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1 :=
        ⟨by linarith [ht_gt], by linarith [hτ.2, ht_Ioo.2]⟩
      have h_γt₀_eq_s : (γ.toPwC1Immersion : ℝ → ℂ) t₀ = s := by
        show γ.toPath.extend t₀ = s
        rw [← γ.cyclicShift_extend_eq_wrap hτ ⟨ht_gt.le, ht_Ioo.2.le⟩]; exact h_at
      obtain ⟨N, a, g, hg_analytic, hf_eq, h_angle_cond⟩ :=
        h.laurent_compatible s hs t₀ (Ioo_subset_Icc_self ht₀_Ioo) h_γt₀_eq_s ht₀_Ioo
      refine ⟨N, a, g, hg_analytic, hf_eq, fun k hk_ne hk_ge => ?_⟩
      obtain ⟨m, hm⟩ := h_angle_cond k hk_ne hk_ge
      exact ⟨m, by rw [γ.angleAtCrossing_cyclicShift_wrap hτ ht_Ioo_w ht_Ioo ht₀_Ioo]; exact hm⟩

end ClosedPwC1Immersion

end
