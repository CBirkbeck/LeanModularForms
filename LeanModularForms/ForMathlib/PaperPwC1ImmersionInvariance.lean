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

/-! ### Periodic extension of the cutoff integrand -/

/-- The 1-periodic extension of the cutoff integrand
`cpvIntegrandOn S f γ.extend ε` to all of `ℝ`. -/
private def cpvIntegrandOnPer (γ : ClosedPwC1Immersion x) (S : Finset ℂ)
    (f : ℂ → ℂ) (ε : ℝ) (u : ℝ) : ℂ :=
  cpvIntegrandOn S f γ.toPath.extend ε (Int.fract u)

/-- The periodic extension is periodic with period 1. -/
private lemma cpvIntegrandOnPer_periodic (γ : ClosedPwC1Immersion x) (S : Finset ℂ)
    (f : ℂ → ℂ) (ε : ℝ) :
    Function.Periodic (cpvIntegrandOnPer γ S f ε) 1 := by
  intro u
  simp only [cpvIntegrandOnPer]
  rw [Int.fract_add_one u]

/-- On `[0, 1)`, the periodic extension equals the original cutoff integrand. -/
private lemma cpvIntegrandOnPer_eq_on_Ico (γ : ClosedPwC1Immersion x) (S : Finset ℂ)
    (f : ℂ → ℂ) (ε : ℝ) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    cpvIntegrandOnPer γ S f ε u = cpvIntegrandOn S f γ.toPath.extend ε u := by
  simp only [cpvIntegrandOnPer]
  congr 1
  exact Int.fract_eq_self.mpr hu

/-- On `[1, 2)`, the periodic extension equals the original cutoff integrand
shifted by `-1`. -/
private lemma cpvIntegrandOnPer_eq_on_Ico_one_two (γ : ClosedPwC1Immersion x)
    (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) {u : ℝ} (hu : u ∈ Ico (1 : ℝ) 2) :
    cpvIntegrandOnPer γ S f ε u = cpvIntegrandOn S f γ.toPath.extend ε (u - 1) := by
  -- u - 1 ∈ [0, 1).
  have h_sub : u - 1 ∈ Ico (0 : ℝ) 1 := by
    constructor
    · linarith [hu.1]
    · linarith [hu.2]
  -- u = (u - 1) + 1, so G(u) = G(u - 1) by periodicity.
  have h_per := cpvIntegrandOnPer_periodic γ S f ε (u - 1)
  -- h_per : G((u - 1) + 1) = G(u - 1). Rewrite u to (u - 1) + 1.
  have h_u_eq : u = (u - 1) + 1 := by ring
  conv_lhs => rw [h_u_eq]
  rw [h_per]
  exact cpvIntegrandOnPer_eq_on_Ico γ S f ε h_sub

/-- The cutoff integrand for the cyclic-shifted curve equals
`G(t + τ)` for a.e. `t ∈ uIoc 0 1`, where `G` is the periodic extension.

This is the key technical lemma combining both no-wrap and wrap regions. -/
private lemma cpvIntegrandOn_cyclicShift_eq_per_ae (γ : ClosedPwC1Immersion x)
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 1 →
      cpvIntegrandOn S f (γ.cyclicShift hτ).toPath.extend ε t =
        cpvIntegrandOnPer γ S f ε (t + τ) := by
  classical
  -- The "bad" set: cyclicShift partition points (finite, hence measure-zero).
  set P : Set ℝ := ((γ.cyclicShift hτ).partition : Set ℝ)
  have hP_zero : volume P = 0 := Finset.measure_zero _ _
  have hP_nmem : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ P :=
    MeasureTheory.compl_mem_ae_iff.mpr hP_zero
  filter_upwards [hP_nmem] with t ht_nmem ht_in
  have h_t_Ioc : t ∈ Ioc (0 : ℝ) 1 := by
    rwa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht_in
  have ht_pos : 0 < t := h_t_Ioc.1
  have ht_le : t ≤ 1 := h_t_Ioc.2
  -- Case-split on t ≤ 1 - τ or t > 1 - τ.
  by_cases ht_le_oneSubTau : t ≤ 1 - τ
  · -- No-wrap case: t ∈ Icc 0 (1-τ).
    have ht_Icc : t ∈ Icc (0 : ℝ) (1 - τ) := ⟨ht_pos.le, ht_le_oneSubTau⟩
    -- (γ_τ)(t) = γ(t + τ).
    have h_extend : (γ.cyclicShift hτ).toPath.extend t = γ.toPath.extend (t + τ) :=
      γ.cyclicShift_extend_eq_no_wrap hτ ht_Icc
    -- (t + τ) ∈ [τ, 1] ⊆ [0, 1). When = 1, t = 1 - τ; this is a partition pt.
    have h_tτ_lt_1 : t + τ < 1 := by
      -- If t = 1 - τ, then t + τ = 1 and t ∈ partition (1 - τ ∈ cyclicShiftPartitionExt).
      rcases lt_or_eq_of_le ht_le_oneSubTau with ht_lt | ht_eq
      · linarith
      · -- t = 1 - τ but we have ht_nmem : t ∉ partition, contradiction.
        exfalso
        apply ht_nmem
        have h_mem : (1 - τ : ℝ) ∈ cyclicShiftPartitionExt γ.partition τ :=
          oneSubTau_mem_cyclicShiftPartitionExt γ.partition τ
        show t ∈ ((γ.cyclicShift hτ).partition : Set ℝ)
        rw [ht_eq]
        exact_mod_cast h_mem
    have h_tτ_pos : 0 < t + τ := by linarith [hτ.1]
    -- t + τ ∈ Ico 0 1, so G(t + τ) = cpvIntegrandOn (t + τ).
    have h_per : cpvIntegrandOnPer γ S f ε (t + τ) =
        cpvIntegrandOn S f γ.toPath.extend ε (t + τ) :=
      cpvIntegrandOnPer_eq_on_Ico γ S f ε ⟨h_tτ_pos.le, h_tτ_lt_1⟩
    rw [h_per]
    -- Derivatives match on the open interior.
    have ht_Ioo : t ∈ Ioo (0 : ℝ) (1 - τ) := by
      refine ⟨ht_pos, ?_⟩
      rcases lt_or_eq_of_le ht_le_oneSubTau with ht_lt | ht_eq
      · exact ht_lt
      · -- t = 1 - τ: contradicted as above
        exfalso
        apply ht_nmem
        have h_mem : (1 - τ : ℝ) ∈ cyclicShiftPartitionExt γ.partition τ :=
          oneSubTau_mem_cyclicShiftPartitionExt γ.partition τ
        show t ∈ ((γ.cyclicShift hτ).partition : Set ℝ)
        rw [ht_eq]
        exact_mod_cast h_mem
    have h_deriv : deriv (γ.cyclicShift hτ).toPath.extend t =
        deriv γ.toPath.extend (t + τ) :=
      γ.cyclicShift_deriv_eq_no_wrap hτ ht_Ioo ht_nmem
    simp only [cpvIntegrandOn, h_extend, h_deriv]
  · -- Wrap case: 1 - τ < t ≤ 1, so t ∈ Ioo (1-τ) 1 (need t < 1 from partition).
    push Not at ht_le_oneSubTau
    -- (γ_τ)(t) = γ(t + τ - 1).
    have h_t_lt_1 : t < 1 := by
      rcases lt_or_eq_of_le ht_le with h_lt | h_eq
      · exact h_lt
      · exfalso
        apply ht_nmem
        have h_mem : (1 : ℝ) ∈ cyclicShiftPartitionExt γ.partition τ :=
          one_mem_cyclicShiftPartitionExt γ.partition τ
        show t ∈ ((γ.cyclicShift hτ).partition : Set ℝ)
        rw [h_eq]
        exact_mod_cast h_mem
    have ht_Icc : t ∈ Icc (1 - τ) 1 := ⟨ht_le_oneSubTau.le, ht_le⟩
    have h_extend : (γ.cyclicShift hτ).toPath.extend t = γ.toPath.extend (t + τ - 1) :=
      γ.cyclicShift_extend_eq_wrap hτ ht_Icc
    -- (t + τ) ∈ (1, 1+τ) ⊆ [1, 2). So G(t + τ) = cpvIntegrandOn (t + τ - 1).
    have h_tτ_ge_1 : 1 ≤ t + τ := by linarith
    have h_tτ_lt_2 : t + τ < 2 := by linarith [hτ.2]
    have h_per : cpvIntegrandOnPer γ S f ε (t + τ) =
        cpvIntegrandOn S f γ.toPath.extend ε ((t + τ) - 1) :=
      cpvIntegrandOnPer_eq_on_Ico_one_two γ S f ε ⟨h_tτ_ge_1, h_tτ_lt_2⟩
    rw [h_per]
    -- Derivatives match on the open interior.
    have ht_Ioo : t ∈ Ioo (1 - τ) 1 := ⟨ht_le_oneSubTau, h_t_lt_1⟩
    have h_deriv : deriv (γ.cyclicShift hτ).toPath.extend t =
        deriv γ.toPath.extend (t + τ - 1) :=
      γ.cyclicShift_deriv_eq_wrap hτ ht_Ioo ht_nmem
    simp only [cpvIntegrandOn, h_extend, h_deriv]

/-! ### Cyclic-shift invariance of `HasCauchyPVOn`

The Cauchy principal value of `∮_γ f(z) dz` excluding ε-neighborhoods of `S` is
unchanged by a cyclic reparametrization of `γ`. -/

/-- For each `ε`, the cutoff integrals over `γ_τ` and `γ` are equal. -/
private lemma cpvIntegrandOn_cyclicShift_integral_eq (γ : ClosedPwC1Immersion x)
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) :
    (∫ t in (0:ℝ)..1, cpvIntegrandOn S f (γ.cyclicShift hτ).toPath.extend ε t) =
      (∫ t in (0:ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t) := by
  classical
  -- Step 1: rewrite the LHS as ∫_0^1 G(t + τ) dt by a.e. equality.
  have h_ae_eq := γ.cpvIntegrandOn_cyclicShift_eq_per_ae hτ S f ε
  have h_step1 : (∫ t in (0:ℝ)..1, cpvIntegrandOn S f (γ.cyclicShift hτ).toPath.extend ε t) =
      ∫ t in (0:ℝ)..1, cpvIntegrandOnPer γ S f ε (t + τ) :=
    intervalIntegral.integral_congr_ae h_ae_eq
  -- Step 2: substitute u = t + τ.
  have h_step2 : (∫ t in (0:ℝ)..1, cpvIntegrandOnPer γ S f ε (t + τ)) =
      ∫ u in (0 + τ)..(1 + τ), cpvIntegrandOnPer γ S f ε u :=
    intervalIntegral.integral_comp_add_right (cpvIntegrandOnPer γ S f ε) τ
  -- Step 3: use periodicity to shift the interval.
  have h_per := cpvIntegrandOnPer_periodic γ S f ε
  have h_step3 : (∫ u in (0 + τ)..(1 + τ), cpvIntegrandOnPer γ S f ε u) =
      ∫ u in (0 : ℝ)..(0 + 1), cpvIntegrandOnPer γ S f ε u := by
    -- intervalIntegral_add_eq: ∫_t^(t+T) = ∫_s^(s+T). Here T = 1, t = τ, s = 0.
    have h_shifted : (∫ u in τ..(τ + 1), cpvIntegrandOnPer γ S f ε u) =
        ∫ u in (0 : ℝ)..(0 + 1), cpvIntegrandOnPer γ S f ε u :=
      h_per.intervalIntegral_add_eq τ 0
    have h_τ_eq : (0 + τ : ℝ) = τ := zero_add τ
    have h_1τ_eq : (1 + τ : ℝ) = τ + 1 := add_comm 1 τ
    rw [h_τ_eq, h_1τ_eq, h_shifted]
  -- Step 4: relate G back to cpvIntegrandOn on [0, 1].
  have h_step4 : (∫ u in (0 : ℝ)..(0 + 1), cpvIntegrandOnPer γ S f ε u) =
      ∫ u in (0:ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε u := by
    rw [zero_add]
    apply intervalIntegral.integral_congr_ae
    -- a.e. wrt volume: if u ∈ uIoc 0 1 and u ≠ 1, then u ∈ Ico 0 1 and G(u) = cpvIntegrandOn(u).
    have h_ae_not_one : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 1 := by
      rw [MeasureTheory.ae_iff]
      simp only [ne_eq, not_not]
      exact Real.volume_singleton
    filter_upwards [h_ae_not_one] with u h_u_ne h_u_in
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h_u_in
    have h_u_Ico : u ∈ Ico (0:ℝ) 1 := ⟨h_u_in.1.le, lt_of_le_of_ne h_u_in.2 h_u_ne⟩
    exact cpvIntegrandOnPer_eq_on_Ico γ S f ε h_u_Ico
  rw [h_step1, h_step2, h_step3, h_step4]

/-- **Invariance of `HasCauchyPVOn` under cyclic shift.** -/
theorem hasCauchyPVOn_cyclicShift {γ : ClosedPwC1Immersion x} {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (S : Finset ℂ) (f : ℂ → ℂ) (L : ℂ) :
    HasCauchyPVOn S f (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path L ↔
      HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path L := by
  -- The two cutoff integrals agree for each ε (by `cpvIntegrandOn_cyclicShift_integral_eq`).
  unfold HasCauchyPVOn
  -- (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path.toPath.extend equals
  -- (γ.cyclicShift hτ).toPath.extend definitionally.
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · refine Tendsto.congr (fun ε => ?_) h
    exact γ.cpvIntegrandOn_cyclicShift_integral_eq hτ S f ε
  · refine Tendsto.congr (fun ε => ?_) h
    exact (γ.cpvIntegrandOn_cyclicShift_integral_eq hτ S f ε).symm

/-! ### Cyclic-shift invariance of `cauchyPVOn` and `generalizedWindingNumber` -/

/-- Helper: `limUnder` is congruent under `eventuallyEq`. -/
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

/-- The CPV (single-pole form) is invariant under cyclic shift. -/
private lemma cauchyPV_cyclicShift {γ : ClosedPwC1Immersion x} {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (z₀ : ℂ) (f : ℂ → ℂ) :
    cauchyPV f (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path z₀ =
      cauchyPV f γ.toPwC1Immersion.toPiecewiseC1Path z₀ := by
  -- For each ε, the integrals via cpvIntegrand equal the integrals via cpvIntegrandOn {z₀}.
  -- Then both sides reduce to the same value via cpvIntegrandOn_cyclicShift_integral_eq.
  unfold cauchyPV
  apply limUnder_congr_eventually_local
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Set.univ, Filter.univ_mem, fun ε _ => ?_⟩
  -- Goal: ∫_0^1 cpvIntegrand f γ_τ.extend z₀ ε t = ∫_0^1 cpvIntegrand f γ.extend z₀ ε t.
  have h_lhs : (∫ t in (0:ℝ)..1, cpvIntegrand f
        (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path.toPath.extend z₀ ε t) =
      ∫ t in (0:ℝ)..1, cpvIntegrandOn {z₀} f
        (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact cpvIntegrand_eq_cpvIntegrandOn_singleton
  have h_rhs : (∫ t in (0:ℝ)..1, cpvIntegrand f
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend z₀ ε t) =
      ∫ t in (0:ℝ)..1, cpvIntegrandOn {z₀} f
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact cpvIntegrand_eq_cpvIntegrandOn_singleton
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

/-! ### Affine-shift transport helper for `IsFlatOfOrder`

For an affine shift `t ↦ t + c`, flatness of `g` at `t₀ + c` transports to
flatness of `f` at `t₀` whenever `f` agrees with `g ∘ (·+c)` on a neighborhood
of `t₀`. This handles the no-wrap region (`Ioo 0 (1-τ)`) where the shift is
`(·+τ)`, and the wrap region (`Ioo (1-τ) 1`) where the shift is `(·+τ-1)`. -/

/-- Derivative of `g ∘ (·+c)` equals `(deriv g) ∘ (·+c)` whenever `g` is
differentiable at `t + c`, or when neither side is. -/
private lemma deriv_comp_add_const (g : ℝ → ℂ) (c t : ℝ) :
    deriv (fun s : ℝ => g (s + c)) t = deriv g (t + c) := by
  by_cases hg : DifferentiableAt ℝ g (t + c)
  · have h_shift : HasDerivAt (fun s : ℝ => s + c) 1 t :=
      (hasDerivAt_id t).add_const c
    -- Apply HasDerivAt.scomp (g₁ : ℝ → ℂ, h : ℝ → ℝ).
    have hg_at : HasDerivAt g (deriv g (t + c)) ((fun s : ℝ => s + c) t) := hg.hasDerivAt
    have h_comp : HasDerivAt (g ∘ (fun s : ℝ => s + c)) ((1 : ℝ) • deriv g (t + c)) t :=
      hg_at.scomp t h_shift
    have h_eq : (g ∘ (fun s : ℝ => s + c)) = (fun s : ℝ => g (s + c)) := rfl
    rw [h_eq] at h_comp
    have hd := h_comp.deriv
    simpa using hd
  · rw [deriv_zero_of_not_differentiableAt, deriv_zero_of_not_differentiableAt hg]
    intro h_comp_diff
    apply hg
    have h_inv : DifferentiableAt ℝ (fun u : ℝ => u - c) (t + c) :=
      ((hasDerivAt_id (t + c)).sub_const c).differentiableAt
    have h_id_eq : (fun u : ℝ => (fun s : ℝ => g (s + c)) (u - c)) = g := by
      funext u; show g (u - c + c) = g u; ring_nf
    have h_pt_eq : (t + c) - c = t := by ring
    have h_comp_diff' : DifferentiableAt ℝ (fun s : ℝ => g (s + c)) ((t + c) - c) := by
      rw [h_pt_eq]; exact h_comp_diff
    -- Compose: differentiableAt (h ∘ k) x ↔ differentiableAt h (k x) ∧ ...
    -- Here h = (fun s => g (s + c)), k = (fun u => u - c), x = t + c, k x = (t+c) - c.
    have hcomp : DifferentiableAt ℝ
        ((fun s : ℝ => g (s + c)) ∘ (fun u : ℝ => u - c)) (t + c) :=
      h_comp_diff'.comp (t + c) h_inv
    have h_id_eq' : (fun s : ℝ => g (s + c)) ∘ (fun u : ℝ => u - c) = g := by
      ext u; show g (u - c + c) = g u; ring_nf
    rw [h_id_eq'] at hcomp
    exact hcomp

/-- Eventual derivative agreement: if `f =ᶠ[𝓝 t₀] g ∘ (·+c)`, then on a neighborhood
of `t₀`, `deriv f = (deriv g) ∘ (·+c)`. -/
private lemma deriv_eventuallyEq_of_shift {f g : ℝ → ℂ} {t₀ c : ℝ}
    (h_eq : ∀ᶠ t in 𝓝 t₀, f t = g (t + c)) :
    ∀ᶠ t in 𝓝 t₀, deriv f t = deriv g (t + c) := by
  have h_self_nhd : ∀ᶠ t in 𝓝 t₀, ∀ᶠ s in 𝓝 t, f s = g (s + c) :=
    eventually_eventually_nhds.mpr h_eq
  filter_upwards [h_self_nhd] with t ht
  have hf : f =ᶠ[𝓝 t] (fun s => g (s + c)) := ht
  rw [Filter.EventuallyEq.deriv_eq hf]
  exact deriv_comp_add_const g c t

/-- `(·+c)` tends from `𝓝[>] t₀` to `𝓝[>] (t₀+c)`. -/
private lemma tendsto_add_const_nhdsGT (t₀ c : ℝ) :
    Tendsto (fun t : ℝ => t + c) (𝓝[>] t₀) (𝓝[>] (t₀ + c)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h_cont : Continuous (fun t : ℝ => t + c) :=
      Continuous.add continuous_id continuous_const
    exact (h_cont.continuousAt.tendsto (x := t₀)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (add_lt_add_iff_right c).mpr ht

/-- `(·+c)` tends from `𝓝[<] t₀` to `𝓝[<] (t₀+c)`. -/
private lemma tendsto_add_const_nhdsLT (t₀ c : ℝ) :
    Tendsto (fun t : ℝ => t + c) (𝓝[<] t₀) (𝓝[<] (t₀ + c)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h_cont : Continuous (fun t : ℝ => t + c) :=
      Continuous.add continuous_id continuous_const
    exact (h_cont.continuousAt.tendsto (x := t₀)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (add_lt_add_iff_right c).mpr ht

/-- `(·-c)` tends from `𝓝[>] (t₀+c)` to `𝓝[>] t₀`. -/
private lemma tendsto_sub_const_nhdsGT (t₀ c : ℝ) :
    Tendsto (fun t : ℝ => t - c) (𝓝[>] (t₀ + c)) (𝓝[>] t₀) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · -- (·-c) is continuous, and at t₀+c, equals t₀.
    have h_eq_pt : (t₀ + c) - c = t₀ := by ring
    have h_cont : Tendsto (fun t : ℝ => t - c) (𝓝 (t₀ + c)) (𝓝 ((t₀ + c) - c)) :=
      ((continuous_id).sub continuous_const).continuousAt.tendsto
    rw [h_eq_pt] at h_cont
    exact h_cont.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    show t₀ < t - c
    have : t₀ + c < t := ht
    linarith

/-- `(·-c)` tends from `𝓝[<] (t₀+c)` to `𝓝[<] t₀`. -/
private lemma tendsto_sub_const_nhdsLT (t₀ c : ℝ) :
    Tendsto (fun t : ℝ => t - c) (𝓝[<] (t₀ + c)) (𝓝[<] t₀) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h_eq_pt : (t₀ + c) - c = t₀ := by ring
    have h_cont : Tendsto (fun t : ℝ => t - c) (𝓝 (t₀ + c)) (𝓝 ((t₀ + c) - c)) :=
      ((continuous_id).sub continuous_const).continuousAt.tendsto
    rw [h_eq_pt] at h_cont
    exact h_cont.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    show t - c < t₀
    have : t < t₀ + c := ht
    linarith

/-- Affine-shift transport of `IsFlatOfOrder`. -/
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
  · -- right_flat: transport via (·+c) on 𝓝[>] t₀.
    intro L hL hL_lim
    -- From `deriv f → L`, get `(deriv g) ∘ (·+c) → L` on `𝓝[>] t₀`.
    have h_shift_to_g : Tendsto (fun t => deriv g (t + c)) (𝓝[>] t₀) (𝓝 L) :=
      hL_lim.congr' h_deriv_right
    -- Compose with `(·-c) : 𝓝[>] (t₀+c) → 𝓝[>] t₀` to get `deriv g → L` on `𝓝[>] (t₀+c)`.
    have hL_lim_g : Tendsto (deriv g) (𝓝[>] (t₀ + c)) (𝓝 L) := by
      have h_comp_back := h_shift_to_g.comp (tendsto_sub_const_nhdsGT t₀ c)
      -- `(deriv g ∘ (·+c)) ∘ (·-c)` t = deriv g ((t-c)+c) = deriv g t.
      exact h_comp_back.congr (fun t => by simp [sub_add_cancel])
    have h_g_flat := h_g.right_flat L hL hL_lim_g
    -- Push the `=o` back through the shift `(·+c) : 𝓝[>] t₀ → 𝓝[>] (t₀+c)`.
    have h_comp := h_g_flat.comp_tendsto (tendsto_add_const_nhdsGT t₀ c)
    -- The composition gives `(... ∘ (·+c))(t)` which is `(deriv g and friends) (t+c)`.
    -- We need to substitute `g(t+c) = f(t)` from `h_eq_right`.
    refine h_comp.congr' ?_ ?_
    · filter_upwards [h_eq_right] with t ht
      simp only [Function.comp_apply]
      rw [← ht, ← h_val]
    · filter_upwards [h_eq_right] with t ht
      simp only [Function.comp_apply]
      rw [← ht, ← h_val]
  · -- left_flat: same proof structure with `𝓝[<]`.
    intro L hL hL_lim
    have h_shift_to_g : Tendsto (fun t => deriv g (t + c)) (𝓝[<] t₀) (𝓝 L) :=
      hL_lim.congr' h_deriv_left
    have hL_lim_g : Tendsto (deriv g) (𝓝[<] (t₀ + c)) (𝓝 L) := by
      have h_comp_back := h_shift_to_g.comp (tendsto_sub_const_nhdsLT t₀ c)
      exact h_comp_back.congr (fun t => by simp [sub_add_cancel])
    have h_g_flat := h_g.left_flat L hL hL_lim_g
    have h_comp := h_g_flat.comp_tendsto (tendsto_add_const_nhdsLT t₀ c)
    refine h_comp.congr' ?_ ?_
    · filter_upwards [h_eq_left] with t ht
      simp only [Function.comp_apply]
      rw [← ht, ← h_val]
    · filter_upwards [h_eq_left] with t ht
      simp only [Function.comp_apply]
      rw [← ht, ← h_val]

/-- The image of the cyclic-shifted path equals the image of the original path. -/
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

/-! ### Cyclic-shift transport of `SatisfiesConditionA'`

The cyclic shift moves the basepoint of `γ` from `γ(0) = γ(1) = x` to `γ(τ)`.
Interior crossings of `γ_τ` correspond to:
- **No-wrap region** (`t₀' ∈ Ioo 0 (1 - τ)`): parameters `t₀' = t₀ - τ` for
  interior `t₀ ∈ Ioo τ 1` of `γ` — transported via affine shift.
- **Wrap region** (`t₀' ∈ Ioo (1 - τ) 1`): parameters `t₀' = t₀ - τ + 1` for
  interior `t₀ ∈ Ioo 0 τ` of `γ` — transported via affine shift.
- **Breakpoint** `t₀' = 1 - τ`: corresponds to `γ(0) = γ(1) = x`, the old
  basepoint. Flatness at this point is the `isFlatOfOrder_one` automatic for
  piecewise `C¹` immersions; downstream callers must restrict pole orders at
  `x` to `≤ 1` (typical when `x ∉ S` or the basepoint pole is simple). -/

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
  -- Case-split on t₀' vs (1 - τ).
  rcases lt_trichotomy t₀' (1 - τ) with ht_lt | ht_eq | ht_gt
  · -- No-wrap case: t₀' < 1 - τ.
    have ht_Ioo_nw : t₀' ∈ Ioo (0 : ℝ) (1 - τ) := ⟨ht_Ioo.1, ht_lt⟩
    -- Pull back to γ at t₀ = t₀' + τ ∈ Ioo τ 1 ⊆ Ioo 0 1.
    set t₀ := t₀' + τ with ht₀_def
    have ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · linarith [hτ.1, ht_Ioo.1]
      · linarith [ht_lt]
    have ht₀_Icc : t₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht₀_Ioo
    -- γ(t₀) = γ_τ(t₀') = s by the no-wrap equation.
    have h_γt₀_eq_s : (γ.toPwC1Immersion : ℝ → ℂ) t₀ = s := by
      have h_step1 : (γ.cyclicShift hτ).toPath.extend t₀' = γ.toPath.extend t₀ :=
        γ.cyclicShift_extend_eq_no_wrap hτ ⟨ht_Ioo.1.le, ht_lt.le⟩
      show γ.toPath.extend t₀ = s
      rw [← h_step1]
      exact h_at
    -- Apply `h` to get flatness of γ at t₀.
    have h_flat_γ : IsFlatOfOrder (γ.toPwC1Immersion : ℝ → ℂ) t₀ (ord s) :=
      h s hs t₀ ht₀_Icc h_γt₀_eq_s ht₀_Ioo
    -- Transport via affine shift on the no-wrap region.
    have h_eq_nbhd : ∀ᶠ t in 𝓝 t₀',
        ((γ.cyclicShift hτ).toPwC1Immersion : ℝ → ℂ) t = γ.toPath.extend (t + τ) := by
      have h_mem : Ioo (0 : ℝ) (1 - τ) ∈ 𝓝 t₀' := isOpen_Ioo.mem_nhds ht_Ioo_nw
      filter_upwards [h_mem] with t ht
      show (γ.cyclicShift hτ).toPath.extend t = γ.toPath.extend (t + τ)
      exact γ.cyclicShift_extend_eq_no_wrap hτ ⟨ht.1.le, ht.2.le⟩
    have h_flat_γ' : IsFlatOfOrder γ.toPath.extend (t₀' + τ) (ord s) := h_flat_γ
    exact isFlatOfOrder_of_eventuallyEq_shift h_eq_nbhd h_flat_γ'
  · -- Breakpoint case: t₀' = 1 - τ.
    -- The breakpoint corresponds to γ_τ(1-τ) = γ(1) = x. Use the basepoint
    -- order bound: ord s ≤ 1 at the basepoint. Then `isFlatOfOrder_one + of_le`.
    -- First establish that s = γ.extend(1).
    have h_s_eq : γ.toPath.extend 1 = s := by
      have h_step : (γ.cyclicShift hτ).toPath.extend t₀' = γ.toPath.extend 1 := by
        have ht_Icc' : t₀' ∈ Icc (0 : ℝ) (1 - τ) := ⟨ht_Ioo.1.le, ht_eq.le⟩
        rw [γ.cyclicShift_extend_eq_no_wrap hτ ht_Icc']
        congr 1
        linarith [ht_eq]
      show γ.toPath.extend 1 = s
      rw [← h_step]
      exact h_at
    have hle : ord s ≤ 1 := h_basepoint_ord s hs h_s_eq
    -- Automatic order-1 flatness at any interior parameter of a PwC¹ immersion.
    have h_flat_one : IsFlatOfOrder ((γ.cyclicShift hτ).toPwC1Immersion : ℝ → ℂ) t₀' 1 :=
      isFlatOfOrder_one (γ.cyclicShift hτ).toPwC1Immersion t₀' ht_Ioo
    -- Drop from order 1 to ord s via of_le.
    have h_cont : ContinuousAt ((γ.cyclicShift hτ).toPwC1Immersion : ℝ → ℂ) t₀' :=
      (γ.cyclicShift hτ).toPwC1Immersion.continuous.continuousAt
    exact h_flat_one.of_le hle h_cont
  · -- Wrap case: t₀' > 1 - τ.
    have ht_Ioo_w : t₀' ∈ Ioo (1 - τ) 1 := ⟨ht_gt, ht_Ioo.2⟩
    -- Pull back to γ at t₀ = t₀' + τ - 1 ∈ Ioo 0 τ ⊆ Ioo 0 1.
    set t₀ := t₀' + τ - 1 with ht₀_def
    have ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · linarith [ht_gt]
      · linarith [hτ.2, ht_Ioo.2]
    have ht₀_Icc : t₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht₀_Ioo
    -- γ(t₀) = γ_τ(t₀') = s by the wrap equation.
    have h_γt₀_eq_s : (γ.toPwC1Immersion : ℝ → ℂ) t₀ = s := by
      have h_step1 : (γ.cyclicShift hτ).toPath.extend t₀' = γ.toPath.extend t₀ :=
        γ.cyclicShift_extend_eq_wrap hτ ⟨ht_gt.le, ht_Ioo.2.le⟩
      show γ.toPath.extend t₀ = s
      rw [← h_step1]
      exact h_at
    have h_flat_γ : IsFlatOfOrder (γ.toPwC1Immersion : ℝ → ℂ) t₀ (ord s) :=
      h s hs t₀ ht₀_Icc h_γt₀_eq_s ht₀_Ioo
    -- Transport via affine shift on the wrap region (shift by τ - 1).
    have h_eq_nbhd : ∀ᶠ t in 𝓝 t₀',
        ((γ.cyclicShift hτ).toPwC1Immersion : ℝ → ℂ) t = γ.toPath.extend (t + (τ - 1)) := by
      have h_mem : Ioo (1 - τ) 1 ∈ 𝓝 t₀' := isOpen_Ioo.mem_nhds ht_Ioo_w
      filter_upwards [h_mem] with t ht
      show (γ.cyclicShift hτ).toPath.extend t = γ.toPath.extend (t + (τ - 1))
      have h_eq : γ.toPath.extend (t + τ - 1) = γ.toPath.extend (t + (τ - 1)) := by
        congr 1; ring
      rw [← h_eq]
      exact γ.cyclicShift_extend_eq_wrap hτ ⟨ht.1.le, ht.2.le⟩
    -- Note t₀' + (τ - 1) = t₀.
    have h_flat_γ' : IsFlatOfOrder γ.toPath.extend (t₀' + (τ - 1)) (ord s) := by
      have h_pt : t₀' + (τ - 1) = t₀ := by show t₀' + (τ - 1) = t₀' + τ - 1; ring
      rw [h_pt]
      exact h_flat_γ
    exact isFlatOfOrder_of_eventuallyEq_shift h_eq_nbhd h_flat_γ'

/-! ### Cyclic-shift transport of `SatisfiesConditionB`

`SatisfiesConditionB γ f S` packages two conditions at each crossing `t₀ ∈ Ioo 0 1`
with `γ(t₀) = s ∈ S`:

* `angle_rational` — `angleAtCrossing γ t₀ ht₀ = p · π / q` for some `p, q`.
* `laurent_compatible` — a Laurent decomposition of `f` near `s` with the angle
  condition `k · α ∈ 2π ℤ`.

Both fields depend on `angleAtCrossing γ t₀ ht₀`, which is parametrization-invariant
in the sense that for `γ' := γ.cyclicShift hτ`, a non-breakpoint crossing `t₀'`
of `γ'` corresponds to an interior crossing `t₀ = t₀' + τ` (no-wrap) or
`t₀ = t₀' + τ - 1` (wrap) of `γ`, and the chosen derivative limits coincide.

The breakpoint `t₀' = 1 - τ` is handled via a basepoint hypothesis. -/

/-- A point `t₀'` strictly inside `Ioo 0 (1 - τ)` belongs to the shifted partition
iff `t₀' + τ` belongs to the original partition.

This uses `cyclicShiftPartitionExt = insert 0 (insert 1 (insert (1-τ) (cyclicShiftPartition _ _)))`
together with the disjointness of `t₀'` from `{0, 1, 1-τ}` and the fact that
`t₀' + τ ∈ Ioo τ 1 ⊆ Icc 0 1` with `t₀' + τ - 1 < 0`. -/
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
      · -- t₀' + τ - 1 ∈ γ.partition, but t₀' + τ - 1 < 0, contradiction.
        exfalso
        have h_neg : t₀' + τ - 1 < 0 := by linarith [ht₀'.2]
        have h_in_Icc : (t₀' + τ - 1 : ℝ) ∈ Icc (0 : ℝ) 1 := γ.partition_subset hp
        linarith [h_in_Icc.1]
  · intro hp
    right; right; right
    rw [mem_cyclicShiftPartition_iff]
    refine ⟨⟨ht₀'.1.le, by linarith [ht₀'.2, hτ.1]⟩, Or.inl hp⟩

/-- Analogue of `mem_cyclicShift_partition_no_wrap_iff` for the wrap region
`Ioo (1 - τ) 1`. -/
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
      · -- t₀' + τ ∈ γ.partition, but t₀' + τ > 1, contradiction.
        exfalso
        have h_gt : t₀' + τ > 1 := by linarith [ht₀'.1]
        have h_in_Icc : (t₀' + τ : ℝ) ∈ Icc (0 : ℝ) 1 := γ.partition_subset hp
        linarith [h_in_Icc.2]
      · exact hp
  · intro hp
    right; right; right
    rw [mem_cyclicShiftPartition_iff]
    refine ⟨⟨by linarith [ht₀'.1, hτ.2], ht₀'.2.le⟩, Or.inr hp⟩

/-- A `Ioo`-neighborhood of `t₀' ∈ Ioo 0 (1 - τ)` whose intersection with
`γ'.partition` reduces to at most `{t₀'}`. -/
private lemma exists_partition_isolating_nhd_no_wrap
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (0 : ℝ) (1 - τ)) :
    ∃ a b : ℝ, a < t₀' ∧ t₀' < b ∧ Ioo a b ⊆ Ioo (0 : ℝ) (1 - τ) ∧
      ((↑(γ.cyclicShift hτ).partition : Set ℝ) ∩ Ioo a b) ⊆ {t₀'} := by
  classical
  set P : Finset ℝ := (γ.cyclicShift hτ).partition with hP_def
  set P' : Finset ℝ := P.erase t₀' with hP'_def
  -- Baseline radius from "stay inside (0, 1-τ)": min(t₀', 1-τ-t₀').
  set δ_box : ℝ := min t₀' (1 - τ - t₀') with hδ_box_def
  have hδ_box_pos : 0 < δ_box := lt_min ht₀'.1 (by linarith [ht₀'.2])
  -- Refine with partition-isolation radius if P' nonempty.
  by_cases hP'_empty : P'.Nonempty
  · -- δ_pre = min p∈P', |t₀'-p| > 0.
    have h_min_pos : ∀ p ∈ P', |t₀' - p| > 0 := fun p hp =>
      abs_pos.mpr (sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hp).1))
    set δ_pre : ℝ := P'.inf' hP'_empty (fun p => |t₀' - p|) with hδ_pre_def
    have hδ_pre_pos : 0 < δ_pre := by
      rw [hδ_pre_def]
      exact (Finset.lt_inf'_iff hP'_empty).mpr h_min_pos
    set δ : ℝ := min δ_box δ_pre with hδ_def
    have hδ_pos : 0 < δ := lt_min hδ_box_pos hδ_pre_pos
    have hδ_le_box : δ ≤ δ_box := min_le_left _ _
    have hδ_le_pre : δ ≤ δ_pre := min_le_right _ _
    refine ⟨t₀' - δ, t₀' + δ, by linarith, by linarith, ?_, ?_⟩
    · intro u hu
      refine ⟨?_, ?_⟩
      · have hδ_le_t₀ : δ ≤ t₀' := hδ_le_box.trans (min_le_left _ _)
        linarith [hu.1]
      · have hδ_le_rem : δ ≤ 1 - τ - t₀' := hδ_le_box.trans (min_le_right _ _)
        linarith [hu.2]
    · intro p hp
      rcases hp with ⟨hp_in_P, hp_Ioo⟩
      by_contra h_ne_t
      have hp_in_P' : p ∈ P' := Finset.mem_erase.mpr ⟨h_ne_t, hp_in_P⟩
      have h_abs : |t₀' - p| ≥ δ_pre := Finset.inf'_le _ hp_in_P'
      have h_abs_lt_δ : |t₀' - p| < δ := by
        rw [abs_lt]
        refine ⟨by linarith [hp_Ioo.2], by linarith [hp_Ioo.1]⟩
      linarith
  · -- P' is empty: no partition points other than t₀'.
    refine ⟨t₀' - δ_box, t₀' + δ_box, by linarith, by linarith, ?_, ?_⟩
    · intro u hu
      refine ⟨?_, ?_⟩
      · have hδ_le_t₀ : δ_box ≤ t₀' := min_le_left _ _
        linarith [hu.1]
      · have hδ_le_rem : δ_box ≤ 1 - τ - t₀' := min_le_right _ _
        linarith [hu.2]
    · intro p hp
      rcases hp with ⟨hp_in_P, _⟩
      by_contra h_ne
      have hp_in_P' : p ∈ P' := Finset.mem_erase.mpr ⟨h_ne, hp_in_P⟩
      have h_empty : P' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP'_empty
      rw [h_empty] at hp_in_P'
      exact absurd hp_in_P' (Finset.notMem_empty p)

/-- Symmetric: a `Ioo`-neighborhood of `t₀' ∈ Ioo (1 - τ) 1` whose intersection
with `γ'.partition` reduces to at most `{t₀'}`. -/
private lemma exists_partition_isolating_nhd_wrap
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (1 - τ) 1) :
    ∃ a b : ℝ, a < t₀' ∧ t₀' < b ∧ Ioo a b ⊆ Ioo (1 - τ) 1 ∧
      ((↑(γ.cyclicShift hτ).partition : Set ℝ) ∩ Ioo a b) ⊆ {t₀'} := by
  classical
  set P : Finset ℝ := (γ.cyclicShift hτ).partition with hP_def
  set P' : Finset ℝ := P.erase t₀' with hP'_def
  set δ_box : ℝ := min (t₀' - (1 - τ)) (1 - t₀') with hδ_box_def
  have hδ_box_pos : 0 < δ_box := lt_min (by linarith [ht₀'.1]) (by linarith [ht₀'.2])
  by_cases hP'_empty : P'.Nonempty
  · have h_min_pos : ∀ p ∈ P', |t₀' - p| > 0 := fun p hp =>
      abs_pos.mpr (sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hp).1))
    set δ_pre : ℝ := P'.inf' hP'_empty (fun p => |t₀' - p|) with hδ_pre_def
    have hδ_pre_pos : 0 < δ_pre := by
      rw [hδ_pre_def]
      exact (Finset.lt_inf'_iff hP'_empty).mpr h_min_pos
    set δ : ℝ := min δ_box δ_pre with hδ_def
    have hδ_pos : 0 < δ := lt_min hδ_box_pos hδ_pre_pos
    have hδ_le_box : δ ≤ δ_box := min_le_left _ _
    have hδ_le_pre : δ ≤ δ_pre := min_le_right _ _
    refine ⟨t₀' - δ, t₀' + δ, by linarith, by linarith, ?_, ?_⟩
    · intro u hu
      refine ⟨?_, ?_⟩
      · have hδ_le_left : δ ≤ t₀' - (1 - τ) := hδ_le_box.trans (min_le_left _ _)
        linarith [hu.1]
      · have hδ_le_right : δ ≤ 1 - t₀' := hδ_le_box.trans (min_le_right _ _)
        linarith [hu.2]
    · intro p hp
      rcases hp with ⟨hp_in_P, hp_Ioo⟩
      by_contra h_ne_t
      have hp_in_P' : p ∈ P' := Finset.mem_erase.mpr ⟨h_ne_t, hp_in_P⟩
      have h_abs : |t₀' - p| ≥ δ_pre := Finset.inf'_le _ hp_in_P'
      have h_abs_lt_δ : |t₀' - p| < δ := by
        rw [abs_lt]
        refine ⟨by linarith [hp_Ioo.2], by linarith [hp_Ioo.1]⟩
      linarith
  · refine ⟨t₀' - δ_box, t₀' + δ_box, by linarith, by linarith, ?_, ?_⟩
    · intro u hu
      refine ⟨?_, ?_⟩
      · have hδ_le_left : δ_box ≤ t₀' - (1 - τ) := min_le_left _ _
        linarith [hu.1]
      · have hδ_le_right : δ_box ≤ 1 - t₀' := min_le_right _ _
        linarith [hu.2]
    · intro p hp
      rcases hp with ⟨hp_in_P, _⟩
      by_contra h_ne
      have hp_in_P' : p ∈ P' := Finset.mem_erase.mpr ⟨h_ne, hp_in_P⟩
      have h_empty : P' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP'_empty
      rw [h_empty] at hp_in_P'
      exact absurd hp_in_P' (Finset.notMem_empty p)

/-! ### `Classical.choose` equality for derivative limits under cyclic shift -/

/-- For `t₀' ∈ Ioo 0 (1 - τ)` and `t₀' + τ ∈ Ioo 0 1`, eventually on `𝓝[<] t₀'`,
the derivative `deriv γ'.toPath.extend t = deriv γ.toPath.extend (t + τ)`. -/
private lemma deriv_cyclicShift_eventuallyEq_left_no_wrap
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (0 : ℝ) (1 - τ)) :
    ∀ᶠ t in 𝓝[<] t₀', deriv (γ.cyclicShift hτ).toPath.extend t =
      deriv γ.toPath.extend (t + τ) := by
  obtain ⟨a, b, ha, hb, hab_sub, hP_iso⟩ :=
    γ.exists_partition_isolating_nhd_no_wrap hτ ht₀'
  have h_Iio : Iio t₀' ∩ Ioo a b ∈ 𝓝[<] t₀' := by
    refine inter_mem_nhdsWithin _ ?_
    exact Ioo_mem_nhds ha hb
  filter_upwards [h_Iio] with t ht
  rcases ht with ⟨ht_lt, ht_Ioo⟩
  have ht_Ioo_no_wrap : t ∈ Ioo (0 : ℝ) (1 - τ) := hab_sub ht_Ioo
  have ht_ne : t ≠ t₀' := ne_of_lt ht_lt
  have ht_nmem : t ∉ (γ.cyclicShift hτ).partition := by
    intro h_in
    have : t ∈ {t₀'} := hP_iso ⟨h_in, ht_Ioo⟩
    exact ht_ne (mem_singleton_iff.mp this)
  exact γ.cyclicShift_deriv_eq_no_wrap hτ ht_Ioo_no_wrap ht_nmem

/-- Right-side variant of the previous lemma. -/
private lemma deriv_cyclicShift_eventuallyEq_right_no_wrap
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (0 : ℝ) (1 - τ)) :
    ∀ᶠ t in 𝓝[>] t₀', deriv (γ.cyclicShift hτ).toPath.extend t =
      deriv γ.toPath.extend (t + τ) := by
  obtain ⟨a, b, ha, hb, hab_sub, hP_iso⟩ :=
    γ.exists_partition_isolating_nhd_no_wrap hτ ht₀'
  have h_Ioi : Ioi t₀' ∩ Ioo a b ∈ 𝓝[>] t₀' := by
    refine inter_mem_nhdsWithin _ ?_
    exact Ioo_mem_nhds ha hb
  filter_upwards [h_Ioi] with t ht
  rcases ht with ⟨ht_gt, ht_Ioo⟩
  have ht_Ioo_no_wrap : t ∈ Ioo (0 : ℝ) (1 - τ) := hab_sub ht_Ioo
  have ht_ne : t ≠ t₀' := ne_of_gt ht_gt
  have ht_nmem : t ∉ (γ.cyclicShift hτ).partition := by
    intro h_in
    have : t ∈ {t₀'} := hP_iso ⟨h_in, ht_Ioo⟩
    exact ht_ne (mem_singleton_iff.mp this)
  exact γ.cyclicShift_deriv_eq_no_wrap hτ ht_Ioo_no_wrap ht_nmem

/-- For `t₀' ∈ Ioo (1 - τ) 1`, eventually on `𝓝[<] t₀'`,
the derivative `deriv γ'.toPath.extend t = deriv γ.toPath.extend (t + τ - 1)`. -/
private lemma deriv_cyclicShift_eventuallyEq_left_wrap
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (1 - τ) 1) :
    ∀ᶠ t in 𝓝[<] t₀', deriv (γ.cyclicShift hτ).toPath.extend t =
      deriv γ.toPath.extend (t + τ - 1) := by
  obtain ⟨a, b, ha, hb, hab_sub, hP_iso⟩ :=
    γ.exists_partition_isolating_nhd_wrap hτ ht₀'
  have h_Iio : Iio t₀' ∩ Ioo a b ∈ 𝓝[<] t₀' := by
    refine inter_mem_nhdsWithin _ ?_
    exact Ioo_mem_nhds ha hb
  filter_upwards [h_Iio] with t ht
  rcases ht with ⟨ht_lt, ht_Ioo⟩
  have ht_Ioo_wrap : t ∈ Ioo (1 - τ) 1 := hab_sub ht_Ioo
  have ht_ne : t ≠ t₀' := ne_of_lt ht_lt
  have ht_nmem : t ∉ (γ.cyclicShift hτ).partition := by
    intro h_in
    have : t ∈ {t₀'} := hP_iso ⟨h_in, ht_Ioo⟩
    exact ht_ne (mem_singleton_iff.mp this)
  exact γ.cyclicShift_deriv_eq_wrap hτ ht_Ioo_wrap ht_nmem

/-- Right-side variant for the wrap region. -/
private lemma deriv_cyclicShift_eventuallyEq_right_wrap
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (1 - τ) 1) :
    ∀ᶠ t in 𝓝[>] t₀', deriv (γ.cyclicShift hτ).toPath.extend t =
      deriv γ.toPath.extend (t + τ - 1) := by
  obtain ⟨a, b, ha, hb, hab_sub, hP_iso⟩ :=
    γ.exists_partition_isolating_nhd_wrap hτ ht₀'
  have h_Ioi : Ioi t₀' ∩ Ioo a b ∈ 𝓝[>] t₀' := by
    refine inter_mem_nhdsWithin _ ?_
    exact Ioo_mem_nhds ha hb
  filter_upwards [h_Ioi] with t ht
  rcases ht with ⟨ht_gt, ht_Ioo⟩
  have ht_Ioo_wrap : t ∈ Ioo (1 - τ) 1 := hab_sub ht_Ioo
  have ht_ne : t ≠ t₀' := ne_of_gt ht_gt
  have ht_nmem : t ∉ (γ.cyclicShift hτ).partition := by
    intro h_in
    have : t ∈ {t₀'} := hP_iso ⟨h_in, ht_Ioo⟩
    exact ht_ne (mem_singleton_iff.mp this)
  exact γ.cyclicShift_deriv_eq_wrap hτ ht_Ioo_wrap ht_nmem

/-- `angleAtCrossing` is invariant under cyclic shift for crossings in the
no-wrap region: if `t₀' ∈ Ioo 0 (1 - τ)` then the angle at `γ' := γ.cyclicShift hτ`
at parameter `t₀'` equals the angle at `γ` at parameter `t₀' + τ`. -/
private theorem angleAtCrossing_cyclicShift_no_wrap
    (γ : ClosedPwC1Immersion x) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {t₀' : ℝ} (ht₀' : t₀' ∈ Ioo (0 : ℝ) (1 - τ))
    (ht₀'_Ioo : t₀' ∈ Ioo (0 : ℝ) 1)
    (ht₀_Ioo : t₀' + τ ∈ Ioo (0 : ℝ) 1) :
    angleAtCrossing (γ.cyclicShift hτ).toPwC1Immersion t₀' ht₀'_Ioo =
      angleAtCrossing γ.toPwC1Immersion (t₀' + τ) ht₀_Ioo := by
  classical
  -- Determine partition membership simultaneously.
  -- Note: γ'.toPwC1Immersion.toPiecewiseC1Path.partition = (γ'.partition.erase 0).erase 1.
  -- Similarly for γ.
  by_cases h_part : t₀' ∈ (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path.partition
  · -- Both are corner crossings.
    -- t₀' ∈ legacy partition ↔ t₀' ∈ γ'.partition ∧ t₀' ≠ 0 ∧ t₀' ≠ 1.
    have h_part_orig : t₀' ∈ (γ.cyclicShift hτ).partition := by
      change t₀' ∈ ((γ.cyclicShift hτ).partition.erase 0).erase 1 at h_part
      have h_in_erase0 := (Finset.mem_erase.mp h_part).2
      exact (Finset.mem_erase.mp h_in_erase0).2
    have h_partγ : (t₀' + τ) ∈ γ.partition :=
      (γ.mem_cyclicShift_partition_no_wrap_iff hτ ht₀').mp h_part_orig
    have h_partγ_legacy : (t₀' + τ) ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition := by
      change (t₀' + τ) ∈ (γ.partition.erase 0).erase 1
      have h_ne_0 : (t₀' + τ) ≠ 0 := ne_of_gt (by linarith [ht₀'.1, hτ.1])
      have h_ne_1 : (t₀' + τ) ≠ 1 := ne_of_lt (by linarith [ht₀'.2])
      exact Finset.mem_erase.mpr ⟨h_ne_1, Finset.mem_erase.mpr ⟨h_ne_0, h_partγ⟩⟩
    -- Both angles are arg(L_right) - arg(-L_left) for their respective sides.
    simp only [angleAtCrossing, h_part, h_partγ_legacy, dite_true]
    -- Now we need to equate the Classical.choose values.
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
    -- Tendsto for γ' at t₀'.
    have h_tendsto_γ'_left : Tendsto
        (deriv (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[<] t₀') (𝓝 Lγ'_left) := hLγ'_left_spec.2
    have h_tendsto_γ'_right : Tendsto
        (deriv (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[>] t₀') (𝓝 Lγ'_right) := hLγ'_right_spec.2
    -- Tendsto for γ at t₀' + τ.
    have h_tendsto_γ_left : Tendsto
        (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[<] (t₀' + τ)) (𝓝 Lγ_left) := hLγ_left_spec.2
    have h_tendsto_γ_right : Tendsto
        (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[>] (t₀' + τ)) (𝓝 Lγ_right) := hLγ_right_spec.2
    -- Transport γ' Tendsto via deriv-equality to (·+τ)-shifted form on γ.
    have h_left_eq : ∀ᶠ t in 𝓝[<] t₀',
        deriv (γ.cyclicShift hτ).toPath.extend t =
          deriv γ.toPath.extend (t + τ) :=
      γ.deriv_cyclicShift_eventuallyEq_left_no_wrap hτ ht₀'
    have h_right_eq : ∀ᶠ t in 𝓝[>] t₀',
        deriv (γ.cyclicShift hτ).toPath.extend t =
          deriv γ.toPath.extend (t + τ) :=
      γ.deriv_cyclicShift_eventuallyEq_right_no_wrap hτ ht₀'
    have h_tend_shifted_left : Tendsto (fun t => deriv γ.toPath.extend (t + τ))
        (𝓝[<] t₀') (𝓝 Lγ'_left) := h_tendsto_γ'_left.congr' h_left_eq
    have h_tend_shifted_right : Tendsto (fun t => deriv γ.toPath.extend (t + τ))
        (𝓝[>] t₀') (𝓝 Lγ'_right) := h_tendsto_γ'_right.congr' h_right_eq
    -- Compose with substitution to get a Tendsto at (t₀' + τ).
    have h_tend_γ_left' : Tendsto (deriv γ.toPath.extend)
        (𝓝[<] (t₀' + τ)) (𝓝 Lγ'_left) := by
      have h_comp := h_tend_shifted_left.comp (tendsto_sub_const_nhdsLT t₀' τ)
      exact h_comp.congr (fun t => by simp [sub_add_cancel])
    have h_tend_γ_right' : Tendsto (deriv γ.toPath.extend)
        (𝓝[>] (t₀' + τ)) (𝓝 Lγ'_right) := by
      have h_comp := h_tend_shifted_right.comp (tendsto_sub_const_nhdsGT t₀' τ)
      exact h_comp.congr (fun t => by simp [sub_add_cancel])
    -- Apply Tendsto unique limit. `𝓝[<]` and `𝓝[>]` of an interior point on ℝ are NeBot
    -- via the global instances `nhdsLT_neBot` and `nhdsGT_neBot`.
    have hL_left_eq : Lγ'_left = Lγ_left :=
      tendsto_nhds_unique h_tend_γ_left' h_tendsto_γ_left
    have hL_right_eq : Lγ'_right = Lγ_right :=
      tendsto_nhds_unique h_tend_γ_right' h_tendsto_γ_right
    rw [hL_left_eq, hL_right_eq]
  · -- Smooth case: t₀' ∉ legacy partition.
    -- t₀' ∉ legacy ↔ t₀' ∉ γ'.partition ∨ t₀' = 0 ∨ t₀' = 1.
    -- Since t₀' ∈ Ioo 0 1, t₀' ∉ legacy ↔ t₀' ∉ γ'.partition.
    have h_part_orig : t₀' ∉ (γ.cyclicShift hτ).partition := by
      intro h_in
      apply h_part
      change t₀' ∈ ((γ.cyclicShift hτ).partition.erase 0).erase 1
      have h_ne_0 : t₀' ≠ 0 := ne_of_gt ht₀'_Ioo.1
      have h_ne_1 : t₀' ≠ 1 := ne_of_lt ht₀'_Ioo.2
      exact Finset.mem_erase.mpr ⟨h_ne_1, Finset.mem_erase.mpr ⟨h_ne_0, h_in⟩⟩
    have h_partγ_nope : (t₀' + τ) ∉ γ.partition := fun h =>
      h_part_orig ((γ.mem_cyclicShift_partition_no_wrap_iff hτ ht₀').mpr h)
    have h_partγ_legacy : (t₀' + τ) ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition := by
      change (t₀' + τ) ∉ (γ.partition.erase 0).erase 1
      intro h_in
      apply h_partγ_nope
      have h := (Finset.mem_erase.mp h_in).2
      exact (Finset.mem_erase.mp h).2
    rw [angleAtCrossing_smooth _ _ ht₀'_Ioo h_part,
      angleAtCrossing_smooth _ _ ht₀_Ioo h_partγ_legacy]

/-- `angleAtCrossing` is invariant under cyclic shift for crossings in the
wrap region. -/
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
      have h_in_erase0 := (Finset.mem_erase.mp h_part).2
      exact (Finset.mem_erase.mp h_in_erase0).2
    have h_partγ : (t₀' + τ - 1) ∈ γ.partition :=
      (γ.mem_cyclicShift_partition_wrap_iff hτ ht₀').mp h_part_orig
    have h_partγ_legacy : (t₀' + τ - 1) ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition := by
      change (t₀' + τ - 1) ∈ (γ.partition.erase 0).erase 1
      have h_ne_0 : (t₀' + τ - 1) ≠ 0 := ne_of_gt (by linarith [ht₀'.1])
      have h_ne_1 : (t₀' + τ - 1) ≠ 1 := ne_of_lt (by linarith [ht₀'.2, hτ.2])
      exact Finset.mem_erase.mpr ⟨h_ne_1, Finset.mem_erase.mpr ⟨h_ne_0, h_partγ⟩⟩
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
    have h_tendsto_γ'_left : Tendsto
        (deriv (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[<] t₀') (𝓝 Lγ'_left) := hLγ'_left_spec.2
    have h_tendsto_γ'_right : Tendsto
        (deriv (γ.cyclicShift hτ).toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[>] t₀') (𝓝 Lγ'_right) := hLγ'_right_spec.2
    have h_tendsto_γ_left : Tendsto
        (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[<] (t₀' + τ - 1)) (𝓝 Lγ_left) := hLγ_left_spec.2
    have h_tendsto_γ_right : Tendsto
        (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[>] (t₀' + τ - 1)) (𝓝 Lγ_right) := hLγ_right_spec.2
    have h_left_eq : ∀ᶠ t in 𝓝[<] t₀',
        deriv (γ.cyclicShift hτ).toPath.extend t =
          deriv γ.toPath.extend (t + τ - 1) :=
      γ.deriv_cyclicShift_eventuallyEq_left_wrap hτ ht₀'
    have h_right_eq : ∀ᶠ t in 𝓝[>] t₀',
        deriv (γ.cyclicShift hτ).toPath.extend t =
          deriv γ.toPath.extend (t + τ - 1) :=
      γ.deriv_cyclicShift_eventuallyEq_right_wrap hτ ht₀'
    have h_tend_shifted_left : Tendsto (fun t => deriv γ.toPath.extend (t + τ - 1))
        (𝓝[<] t₀') (𝓝 Lγ'_left) := h_tendsto_γ'_left.congr' h_left_eq
    have h_tend_shifted_right : Tendsto (fun t => deriv γ.toPath.extend (t + τ - 1))
        (𝓝[>] t₀') (𝓝 Lγ'_right) := h_tendsto_γ'_right.congr' h_right_eq
    -- Compose with `(·-τ+1)` to get a Tendsto at `t₀' + τ - 1`.
    -- The map `(t : ℝ) ↦ t - (τ - 1) = t - τ + 1` sends `𝓝[<] (t₀'+τ-1)` to `𝓝[<] t₀'`.
    have h_shift_back_left : Tendsto (fun u : ℝ => u - (τ - 1))
        (𝓝[<] (t₀' + τ - 1)) (𝓝[<] t₀') := by
      have h_pt_eq : (t₀' + τ - 1) - (τ - 1) = t₀' := by ring
      have h := tendsto_sub_const_nhdsLT t₀' (τ - 1)
      have h_pt : (t₀' + (τ - 1)) = (t₀' + τ - 1) := by ring
      rw [← h_pt]
      exact h
    have h_shift_back_right : Tendsto (fun u : ℝ => u - (τ - 1))
        (𝓝[>] (t₀' + τ - 1)) (𝓝[>] t₀') := by
      have h := tendsto_sub_const_nhdsGT t₀' (τ - 1)
      have h_pt : (t₀' + (τ - 1)) = (t₀' + τ - 1) := by ring
      rw [← h_pt]
      exact h
    have h_tend_γ_left' : Tendsto (deriv γ.toPath.extend)
        (𝓝[<] (t₀' + τ - 1)) (𝓝 Lγ'_left) := by
      have h_comp := h_tend_shifted_left.comp h_shift_back_left
      refine h_comp.congr (fun u => ?_)
      show deriv γ.toPath.extend ((u - (τ - 1)) + τ - 1) = deriv γ.toPath.extend u
      congr 1; ring
    have h_tend_γ_right' : Tendsto (deriv γ.toPath.extend)
        (𝓝[>] (t₀' + τ - 1)) (𝓝 Lγ'_right) := by
      have h_comp := h_tend_shifted_right.comp h_shift_back_right
      refine h_comp.congr (fun u => ?_)
      show deriv γ.toPath.extend ((u - (τ - 1)) + τ - 1) = deriv γ.toPath.extend u
      congr 1; ring
    have hL_left_eq : Lγ'_left = Lγ_left :=
      tendsto_nhds_unique h_tend_γ_left' h_tendsto_γ_left
    have hL_right_eq : Lγ'_right = Lγ_right :=
      tendsto_nhds_unique h_tend_γ_right' h_tendsto_γ_right
    rw [hL_left_eq, hL_right_eq]
  · have h_part_orig : t₀' ∉ (γ.cyclicShift hτ).partition := by
      intro h_in
      apply h_part
      change t₀' ∈ ((γ.cyclicShift hτ).partition.erase 0).erase 1
      have h_ne_0 : t₀' ≠ 0 := ne_of_gt ht₀'_Ioo.1
      have h_ne_1 : t₀' ≠ 1 := ne_of_lt ht₀'_Ioo.2
      exact Finset.mem_erase.mpr ⟨h_ne_1, Finset.mem_erase.mpr ⟨h_ne_0, h_in⟩⟩
    have h_partγ_nope : (t₀' + τ - 1) ∉ γ.partition := fun h =>
      h_part_orig ((γ.mem_cyclicShift_partition_wrap_iff hτ ht₀').mpr h)
    have h_partγ_legacy : (t₀' + τ - 1) ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition := by
      change (t₀' + τ - 1) ∉ (γ.partition.erase 0).erase 1
      intro h_in
      apply h_partγ_nope
      have h := (Finset.mem_erase.mp h_in).2
      exact (Finset.mem_erase.mp h).2
    rw [angleAtCrossing_smooth _ _ ht₀'_Ioo h_part,
      angleAtCrossing_smooth _ _ ht₀_Ioo h_partγ_legacy]

/-! ### Main theorem: cyclic-shift invariance of `SatisfiesConditionB`

The hypotheses `h_basepoint_angleB` and `h_basepoint_laurentB` encode the
breakpoint case `t₀' = 1 - τ` corresponding to the old basepoint `γ(1) = x`.
Both are vacuous when `x ∉ S`. -/

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
  · -- angle_rational
    intro s hs t₀' ht_Icc h_at ht_Ioo
    rcases lt_trichotomy t₀' (1 - τ) with ht_lt | ht_eq | ht_gt
    · -- No-wrap case.
      have ht_Ioo_nw : t₀' ∈ Ioo (0 : ℝ) (1 - τ) := ⟨ht_Ioo.1, ht_lt⟩
      set t₀ := t₀' + τ with ht₀_def
      have ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1 :=
        ⟨by linarith [hτ.1, ht_Ioo.1], by linarith [ht_lt]⟩
      have ht₀_Icc : t₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht₀_Ioo
      have h_γt₀_eq_s : (γ.toPwC1Immersion : ℝ → ℂ) t₀ = s := by
        have h_step1 : (γ.cyclicShift hτ).toPath.extend t₀' = γ.toPath.extend t₀ :=
          γ.cyclicShift_extend_eq_no_wrap hτ ⟨ht_Ioo.1.le, ht_lt.le⟩
        show γ.toPath.extend t₀ = s
        rw [← h_step1]; exact h_at
      obtain ⟨p, q, hq_ne, hpq_coprime, h_angle⟩ :=
        h.angle_rational s hs t₀ ht₀_Icc h_γt₀_eq_s ht₀_Ioo
      refine ⟨p, q, hq_ne, hpq_coprime, ?_⟩
      rw [γ.angleAtCrossing_cyclicShift_no_wrap hτ ht_Ioo_nw ht_Ioo ht₀_Ioo, h_angle]
    · -- Breakpoint case: t₀' = 1 - τ.
      have h_s_eq : γ.toPath.extend 1 = s := by
        have h_step : (γ.cyclicShift hτ).toPath.extend t₀' = γ.toPath.extend 1 := by
          have ht_Icc' : t₀' ∈ Icc (0 : ℝ) (1 - τ) := ⟨ht_Ioo.1.le, ht_eq.le⟩
          rw [γ.cyclicShift_extend_eq_no_wrap hτ ht_Icc']
          congr 1; linarith [ht_eq]
        show γ.toPath.extend 1 = s
        rw [← h_step]; exact h_at
      have ht₀'_eq : t₀' = 1 - τ := ht_eq
      subst ht₀'_eq
      exact h_basepoint_angleB s hs h_s_eq ht_Ioo
    · -- Wrap case: t₀' > 1 - τ.
      have ht_Ioo_w : t₀' ∈ Ioo (1 - τ) 1 := ⟨ht_gt, ht_Ioo.2⟩
      set t₀ := t₀' + τ - 1 with ht₀_def
      have ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1 :=
        ⟨by linarith [ht_gt], by linarith [hτ.2, ht_Ioo.2]⟩
      have ht₀_Icc : t₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht₀_Ioo
      have h_γt₀_eq_s : (γ.toPwC1Immersion : ℝ → ℂ) t₀ = s := by
        have h_step1 : (γ.cyclicShift hτ).toPath.extend t₀' = γ.toPath.extend t₀ :=
          γ.cyclicShift_extend_eq_wrap hτ ⟨ht_gt.le, ht_Ioo.2.le⟩
        show γ.toPath.extend t₀ = s
        rw [← h_step1]; exact h_at
      obtain ⟨p, q, hq_ne, hpq_coprime, h_angle⟩ :=
        h.angle_rational s hs t₀ ht₀_Icc h_γt₀_eq_s ht₀_Ioo
      refine ⟨p, q, hq_ne, hpq_coprime, ?_⟩
      rw [γ.angleAtCrossing_cyclicShift_wrap hτ ht_Ioo_w ht_Ioo ht₀_Ioo, h_angle]
  · -- laurent_compatible
    intro s hs t₀' ht_Icc h_at ht_Ioo
    rcases lt_trichotomy t₀' (1 - τ) with ht_lt | ht_eq | ht_gt
    · -- No-wrap case.
      have ht_Ioo_nw : t₀' ∈ Ioo (0 : ℝ) (1 - τ) := ⟨ht_Ioo.1, ht_lt⟩
      set t₀ := t₀' + τ with ht₀_def
      have ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1 :=
        ⟨by linarith [hτ.1, ht_Ioo.1], by linarith [ht_lt]⟩
      have ht₀_Icc : t₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht₀_Ioo
      have h_γt₀_eq_s : (γ.toPwC1Immersion : ℝ → ℂ) t₀ = s := by
        have h_step1 : (γ.cyclicShift hτ).toPath.extend t₀' = γ.toPath.extend t₀ :=
          γ.cyclicShift_extend_eq_no_wrap hτ ⟨ht_Ioo.1.le, ht_lt.le⟩
        show γ.toPath.extend t₀ = s
        rw [← h_step1]; exact h_at
      obtain ⟨N, a, g, hg_analytic, hf_eq, h_angle_cond⟩ :=
        h.laurent_compatible s hs t₀ ht₀_Icc h_γt₀_eq_s ht₀_Ioo
      refine ⟨N, a, g, hg_analytic, hf_eq, ?_⟩
      intro k hk_ne hk_ge
      obtain ⟨m, hm⟩ := h_angle_cond k hk_ne hk_ge
      refine ⟨m, ?_⟩
      rw [γ.angleAtCrossing_cyclicShift_no_wrap hτ ht_Ioo_nw ht_Ioo ht₀_Ioo]
      exact hm
    · -- Breakpoint case.
      have h_s_eq : γ.toPath.extend 1 = s := by
        have h_step : (γ.cyclicShift hτ).toPath.extend t₀' = γ.toPath.extend 1 := by
          have ht_Icc' : t₀' ∈ Icc (0 : ℝ) (1 - τ) := ⟨ht_Ioo.1.le, ht_eq.le⟩
          rw [γ.cyclicShift_extend_eq_no_wrap hτ ht_Icc']
          congr 1; linarith [ht_eq]
        show γ.toPath.extend 1 = s
        rw [← h_step]; exact h_at
      have ht₀'_eq : t₀' = 1 - τ := ht_eq
      subst ht₀'_eq
      exact h_basepoint_laurentB s hs h_s_eq ht_Ioo
    · -- Wrap case.
      have ht_Ioo_w : t₀' ∈ Ioo (1 - τ) 1 := ⟨ht_gt, ht_Ioo.2⟩
      set t₀ := t₀' + τ - 1 with ht₀_def
      have ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1 :=
        ⟨by linarith [ht_gt], by linarith [hτ.2, ht_Ioo.2]⟩
      have ht₀_Icc : t₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht₀_Ioo
      have h_γt₀_eq_s : (γ.toPwC1Immersion : ℝ → ℂ) t₀ = s := by
        have h_step1 : (γ.cyclicShift hτ).toPath.extend t₀' = γ.toPath.extend t₀ :=
          γ.cyclicShift_extend_eq_wrap hτ ⟨ht_gt.le, ht_Ioo.2.le⟩
        show γ.toPath.extend t₀ = s
        rw [← h_step1]; exact h_at
      obtain ⟨N, a, g, hg_analytic, hf_eq, h_angle_cond⟩ :=
        h.laurent_compatible s hs t₀ ht₀_Icc h_γt₀_eq_s ht₀_Ioo
      refine ⟨N, a, g, hg_analytic, hf_eq, ?_⟩
      intro k hk_ne hk_ge
      obtain ⟨m, hm⟩ := h_angle_cond k hk_ne hk_ge
      refine ⟨m, ?_⟩
      rw [γ.angleAtCrossing_cyclicShift_wrap hτ ht_Ioo_w ht_Ioo ht₀_Ioo]
      exact hm

end ClosedPwC1Immersion

end
