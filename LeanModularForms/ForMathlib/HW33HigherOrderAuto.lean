/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HW33HigherOrderC4

/-!
# Auto-discharge wrappers for the higher-order avoidance theorems

This file provides user-friendly wrappers around `HW33HigherOrderC3.lean` that
auto-discharge the integrability hypotheses when `γ` is Lipschitz and avoids
the pole `s` with positive margin.

## Main results

* `intervalIntegrable_pow_inv_mul_deriv_of_avoids`: integrability of
  `1/(γ - s)^k · γ'` for Lipschitz γ avoiding `s` with positive margin.
-/

open Filter Topology MeasureTheory Set Complex
open scoped Classical Real Interval

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-! ## Integrability helpers (Lipschitz + avoidance) -/

/-- **Integrability of `1/(γ - s)^k · γ'` from Lipschitz + avoidance.** When `γ`
is Lipschitz and avoids `s` with positive margin `δ > 0`, the integrand
`1/(γ(t) - s)^k · γ'(t)` is interval-integrable on `[0, 1]`.

Proof: `1/(γ - s)^k` is `ContinuousOn (Icc 0 1)` (since `γ - s` is continuous and
nonzero by avoidance) hence essentially bounded by `1/δ^k`. The Lipschitz
hypothesis gives integrability of `deriv γ` on `Ioc 0 1` (via the Lipschitz
norm bound `K`). Combining via `Integrable.bdd_mul`. -/
theorem intervalIntegrable_pow_inv_mul_deriv_of_avoids
    (γ : PiecewiseC1Path x x) (s : ℂ) (k : ℕ) {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_bd : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ.toPath.extend t - s‖)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    IntervalIntegrable
      (fun t => 1 / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t)
      volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
  -- deriv γ is integrable on Ioc 0 1 (Lipschitz ⇒ bounded by K)
  have h_deriv_int : IntegrableOn (deriv γ.toPath.extend) (Ioc (0 : ℝ) 1) volume :=
    MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (stronglyMeasurable_deriv _).aestronglyMeasurable
      (ae_restrict_of_ae (Filter.Eventually.of_forall
        (fun _ => norm_deriv_le_of_lipschitz hLip)))
  -- The factor 1/(γ - s)^k is continuous on Icc 0 1 with the right bound
  have h_ne : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t - s ≠ 0 := fun t ht hzero => by
    have := hδ_bd t ht
    rw [hzero, norm_zero] at this; linarith
  have h_cont : ContinuousOn
      (fun t => (1 : ℂ) / (γ.toPath.extend t - s) ^ k) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div
      ((γ.toPath.continuous_extend.continuousOn.sub continuousOn_const).pow k)
      (fun t ht => pow_ne_zero _ (h_ne t ht))
  have h_meas : AEStronglyMeasurable
      (fun t => (1 : ℂ) / (γ.toPath.extend t - s) ^ k)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (h_cont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have h_bound_ae : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖(1 : ℂ) / (γ.toPath.extend t - s) ^ k‖ ≤ 1 / δ ^ k := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr <| .of_forall fun t ht => ?_
    rw [norm_div, norm_one, norm_pow]
    exact div_le_div_of_nonneg_left zero_le_one (pow_pos hδ_pos k)
      (pow_le_pow_left₀ hδ_pos.le (hδ_bd t (Ioc_subset_Icc_self ht)) k)
  exact h_deriv_int.bdd_mul h_meas h_bound_ae

/-! ## Measurability of the "ε-ball" set -/

/-- The "ε-ball" set `{t | ∃ s ∈ S, ‖γ(t) - s‖ ≤ ε}` is measurable. -/
theorem measurableSet_cpvIntegrandOn_zero
    {y : ℂ} (S : Finset ℂ) (γ : PiecewiseC1Path x y) (ε : ℝ) :
    MeasurableSet {t : ℝ | ∃ s ∈ S, ‖γ.toPath.extend t - s‖ ≤ ε} := by
  classical
  suffices {t : ℝ | ∃ s ∈ S, ‖γ.toPath.extend t - s‖ ≤ ε} =
      ⋃ s ∈ (S : Set ℂ), {t | ‖γ.toPath.extend t - s‖ ≤ ε} by
    rw [this]
    exact S.finite_toSet.measurableSet_biUnion fun s _ =>
      (γ.toPath.continuous_extend.measurable.sub_const s).norm measurableSet_Iic
  ext t; simp

/-! ## CPV integrand norm bound -/

/-- **CPV integrand is dominated by the contour integrand.** Pointwise:
`‖cpvIntegrandOn S f γ ε t‖ ≤ ‖contourIntegrand f γ t‖`, since the CPV integrand
is either 0 or equal to the contour integrand. This is the pointwise step
toward dominated-convergence integrability arguments for `cpvIntegrandOn`. -/
theorem norm_cpvIntegrandOn_le_norm_contourIntegrand
    {y : ℂ} (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (ε : ℝ) (t : ℝ) :
    ‖cpvIntegrandOn S f γ.toPath.extend ε t‖ ≤
      ‖PiecewiseC1Path.contourIntegrand f γ t‖ := by
  simp only [cpvIntegrandOn, PiecewiseC1Path.contourIntegrand,
    PiecewiseC1Path.extendedPath_eq]
  split_ifs <;>
  first | (rw [norm_zero]; exact norm_nonneg _) | rfl

/-! ## CPV integrand interval-integrability from contour integrand -/

/-- **CPV integrand AEStronglyMeasurable from contour integrand AEStronglyMeasurable.**
The CPV integrand `cpvIntegrandOn S f γ ε` is `Set.piecewise A 0 (contourIntegrand f γ)`
where `A = {t | ∃ s ∈ S, ‖γ(t) - s‖ ≤ ε}` is measurable. -/
theorem aestronglyMeasurable_cpvIntegrandOn
    {y : ℂ} (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (ε : ℝ)
    {μ : MeasureTheory.Measure ℝ}
    (h_contour_meas : AEStronglyMeasurable
      (PiecewiseC1Path.contourIntegrand f γ) μ) :
    AEStronglyMeasurable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) μ := by
  have h_meas : MeasurableSet
      {t : ℝ | ∃ s ∈ S, ‖γ.toPath.extend t - s‖ ≤ ε} :=
    measurableSet_cpvIntegrandOn_zero S γ ε
  suffices (fun t : ℝ => cpvIntegrandOn S f γ.toPath.extend ε t) =
      ({t : ℝ | ∃ s ∈ S, ‖γ.toPath.extend t - s‖ ≤ ε}).piecewise
        (fun _ => 0) (PiecewiseC1Path.contourIntegrand f γ) by
    rw [this]
    exact AEStronglyMeasurable.piecewise h_meas
      aestronglyMeasurable_const
      (h_contour_meas.mono_measure Measure.restrict_le_self)
  funext t
  simp only [cpvIntegrandOn, Set.piecewise, PiecewiseC1Path.contourIntegrand,
    PiecewiseC1Path.extendedPath_eq, Set.mem_setOf_eq]

/-- **CPV integrand interval-integrability from contour integrand integrability.**
For any `ε`, if the contour integrand `f(γ(t)) · γ'(t)` is interval-integrable
on `[0, 1]`, so is the CPV integrand `cpvIntegrandOn S f γ ε`. The proof uses
the pointwise norm bound (`norm_cpvIntegrandOn_le_norm_contourIntegrand`)
and `IntervalIntegrable.mono_fun`. -/
theorem cpvIntegrandOn_intervalIntegrable_of_contourIntegrand
    {y : ℂ} (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (ε : ℝ)
    (h_contour_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand f γ) volume 0 1) :
    IntervalIntegrable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1 := by
  refine h_contour_int.mono_fun ?_ ?_
  · have h := h_contour_int.aestronglyMeasurable
    rw [show Ioc (0 : ℝ) 1 = Ι (0 : ℝ) 1 from (uIoc_of_le (zero_le_one' ℝ)).symm] at h
    exact aestronglyMeasurable_cpvIntegrandOn S f γ ε h
  · exact ae_of_all _ fun t => norm_cpvIntegrandOn_le_norm_contourIntegrand S f γ ε t

/-! ## Auto-discharge wrappers for the higher-order avoidance theorems -/

/-- **C-3 single-power avoidance, integrability auto-derived (Lipschitz form).**
For `γ` Lipschitz avoiding `S` with positive margin, the higher-order polar sum
`∑ s ∈ S, c s / (z - s)^k` (`k ≥ 2`) has CPV zero. The interval-integrability
hypothesis of `hasCauchyPVOn_finset_pow_inv_of_avoids` is auto-discharged via
`intervalIntegrable_pow_inv_mul_deriv_of_avoids`. -/
theorem hasCauchyPVOn_finset_pow_inv_of_avoids_lip
    (S : Finset ℂ) (k : ℕ) (hk : 2 ≤ k) (c : ℂ → ℂ)
    (γ : PiecewiseC1Path x x) {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_bd : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S
      (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ 0 := by
  refine hasCauchyPVOn_finset_pow_inv_of_avoids S k hk c γ ⟨δ, hδ_pos, hδ_bd⟩ fun s hs => ?_
  refine intervalIntegrable_pow_inv_mul_deriv_of_avoids γ s k hδ_pos
    (fun t ht => ?_) hLip
  have := hδ_bd s hs t ht
  rwa [PiecewiseC1Path.extendedPath_eq] at this

/-- **C-3 single-power avoidance, δ-free + Lipschitz form.** Same as
`hasCauchyPVOn_finset_pow_inv_of_avoids_lip` but with the positive margin
auto-derived from pointwise avoidance via `avoids_finset_delta_bound`. -/
theorem hasCauchyPVOn_finset_pow_inv_of_avoids_lip_avoids
    (S : Finset ℂ) (k : ℕ) (hk : 2 ≤ k) (c : ℂ → ℂ)
    (γ : PiecewiseC1Path x x)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S
      (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ 0 := by
  obtain ⟨δ, hδ_pos, hδ_bd⟩ := avoids_finset_delta_bound γ S hγ_avoids
  exact hasCauchyPVOn_finset_pow_inv_of_avoids_lip S k hk c γ hδ_pos hδ_bd hLip

/-! ## Auto-discharge: contour integrability for the higher-order polar sum -/

/-- **Contour integrand integrability for the higher-order polar sum.** When `γ`
is Lipschitz and avoids `S` with positive margin, the contour integrand
`(∑ s ∈ S, c s / (γ(t) - s)^k) · γ'(t)` is interval-integrable on `[0, 1]`. -/
theorem contourIntegrand_finset_pow_inv_intervalIntegrable_of_avoids_lip
    (S : Finset ℂ) (k : ℕ) (c : ℂ → ℂ)
    (γ : PiecewiseC1Path x x) {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_bd : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ) volume 0 1 := by
  have h_each : ∀ s ∈ S, IntervalIntegrable
      (fun t => c s / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t)
      volume 0 1 := fun s hs => by
    have hδ_bd_extend : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ.toPath.extend t - s‖ :=
      fun t ht => by
        have := hδ_bd s hs t ht
        rwa [PiecewiseC1Path.extendedPath_eq] at this
    rw [show (fun t : ℝ =>
        c s / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t) =
        fun t => c s *
          (1 / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t) by
      funext t; ring]
    exact (intervalIntegrable_pow_inv_mul_deriv_of_avoids γ s k hδ_pos
      hδ_bd_extend hLip).const_mul (c s)
  have heq : PiecewiseC1Path.contourIntegrand
      (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ =
      fun t => ∑ s ∈ S,
        c s / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t := by
    funext t
    simp only [PiecewiseC1Path.contourIntegrand, PiecewiseC1Path.extendedPath_eq,
      Finset.sum_mul]
  rw [heq]
  have h_sum := IntervalIntegrable.sum S h_each
  have hfun : (∑ i ∈ S, fun t : ℝ =>
      c i / (γ.toPath.extend t - i) ^ k * deriv γ.toPath.extend t) =
      fun t => ∑ i ∈ S,
        c i / (γ.toPath.extend t - i) ^ k * deriv γ.toPath.extend t := by
    funext t; rw [Finset.sum_apply]
  rwa [hfun] at h_sum

/-! ## Auto-discharged C-3/C-4 add forms -/

/-- **`hasCauchyPVOn_add_higherOrderPolar_of_avoids` with all integrability
auto-discharged from Lipschitz + avoidance.** -/
theorem hasCauchyPVOn_add_higherOrderPolar_of_avoids_lip
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) {L : ℂ}
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_bd : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_f : HasCauchyPVOn S f γ L)
    (h_f_int : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1)
    (k : ℕ) (hk : 2 ≤ k) (c : ℂ → ℂ)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S
      (fun z => f z + ∑ s ∈ S, c s / (z - s) ^ k) γ L := by
  have h_int_HO : ∀ s ∈ S, IntervalIntegrable
      (fun t => (1 / (γ.toPath.extend t - s) ^ k) * deriv γ.toPath.extend t)
      volume 0 1 := fun s hs => by
    have hδ_bd_extend : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ.toPath.extend t - s‖ :=
      fun t ht => by
        have := hδ_bd s hs t ht
        rwa [PiecewiseC1Path.extendedPath_eq] at this
    exact intervalIntegrable_pow_inv_mul_deriv_of_avoids γ s k hδ_pos
      hδ_bd_extend hLip
  exact hasCauchyPVOn_add_higherOrderPolar_of_avoids S f γ
    ⟨δ, hδ_pos, hδ_bd⟩ h_f h_f_int k hk c h_int_HO
    (fun ε _ =>
      cpvIntegrandOn_intervalIntegrable_of_contourIntegrand S _ γ ε
        (contourIntegrand_finset_pow_inv_intervalIntegrable_of_avoids_lip
          S k c γ hδ_pos hδ_bd hLip))

/-- **`hasCauchyPVOn_add_higherOrderPolarSum_of_avoids` with all integrability
auto-discharged from Lipschitz + avoidance (multi-power version).** -/
theorem hasCauchyPVOn_add_higherOrderPolarSum_of_avoids_lip
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) {L : ℂ}
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_bd : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_f : HasCauchyPVOn S f γ L)
    (h_f_int : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1)
    (M : ℕ) (c_HO : ℕ → ℂ → ℂ)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S
      (fun z => f z +
        ∑ k ∈ Finset.Ico 2 (M + 1), ∑ s ∈ S, c_HO k s / (z - s) ^ k) γ L := by
  have h_int_HO : ∀ k ∈ Finset.Ico 2 (M + 1), ∀ s ∈ S, IntervalIntegrable
      (fun t => (1 / (γ.toPath.extend t - s) ^ k) * deriv γ.toPath.extend t)
      volume 0 1 := fun k _ s hs => by
    have hδ_bd_extend : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ.toPath.extend t - s‖ :=
      fun t ht => by
        have := hδ_bd s hs t ht
        rwa [PiecewiseC1Path.extendedPath_eq] at this
    exact intervalIntegrable_pow_inv_mul_deriv_of_avoids γ s k hδ_pos
      hδ_bd_extend hLip
  exact hasCauchyPVOn_add_higherOrderPolarSum_of_avoids S f γ
    ⟨δ, hδ_pos, hδ_bd⟩ h_f h_f_int M c_HO h_int_HO
    (fun k _ ε _ =>
      cpvIntegrandOn_intervalIntegrable_of_contourIntegrand S _ γ ε
        (contourIntegrand_finset_pow_inv_intervalIntegrable_of_avoids_lip
          S k (c_HO k) γ hδ_pos hδ_bd hLip))

/-! ## Fully auto-discharged C-4 closed form -/

/-- **C-4 closed avoidance form, fully auto-discharged.** Same as
`generalizedResidueTheorem_higherOrder_avoids_closed` but with the higher-order
integrability hypotheses (`h_int_HO` and `h_HO_int`) auto-discharged from the
Lipschitz + avoidance assumptions already present.

The user supplies only:
* `f_simple` differentiable with simple poles at `S`,
* the higher-order coefficients `c_HO`,
* `f_simple`'s CPV-integrand integrability (a single hypothesis on f_simple
  alone — much smaller than the original four),
* γ closed null-homologous Lipschitz avoiding `S`.

The conclusion is the same residue formula as the simple-pole case:
the higher-order terms contribute zero. -/
theorem generalizedResidueTheorem_higherOrder_avoids_closed_lip
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (hU_bounded : Bornology.IsBounded U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    (f_simple : ℂ → ℂ) (hf_simple : DifferentiableOn ℂ f_simple (U \ ↑S))
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f_simple s)
    (M : ℕ) (c_HO : ℕ → ℂ → ℂ)
    (h_simple_int : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S f_simple
        γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ s)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S
      (fun z => f_simple z +
        ∑ k ∈ Finset.Ico 2 (M + 1), ∑ s ∈ S, c_HO k s / (z - s) ^ k)
      γ.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f_simple s) := by
  obtain ⟨δ, hδ_pos, hδ_bd⟩ :=
    avoids_finset_delta_bound γ.toPiecewiseC1Path S hγ_avoids
  exact hasCauchyPVOn_add_higherOrderPolarSum_of_avoids_lip
    S f_simple γ.toPiecewiseC1Path hδ_pos hδ_bd
    (generalizedResidueTheorem_simplePoles_nullHomologous_closed hU_open hU_ne
      hU_bounded S hS_in_U f_simple hf_simple γ h_null hSimplePoles hγ_avoids
      ⟨δ, hδ_pos, hδ_bd⟩ hLip)
    h_simple_int M c_HO hLip

end LeanModularForms

end
