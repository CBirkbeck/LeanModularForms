/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HW33Paper
import LeanModularForms.ForMathlib.HW33HoloCancel
import LeanModularForms.ForMathlib.HW33PVSing
import LeanModularForms.ForMathlib.HW33HigherOrder
import LeanModularForms.ForMathlib.MeromorphicBridge

/-!
# HW Theorem 3.3 — paper-faithful curve form, simple-pole case with crossings

This file composes the discharged oracles from Phases 3.3 / 3.5 / 4 / 5 / 5b / 5c
into the cleanest paper-faithful statement for the **simple-pole case** of HW
Theorem 3.3 that can be assembled today.

Compared to `hw_3_3_paper`, which exposes six oracle hypotheses
(`h_polar_cancel`, `h_holo_cancel`, `hI_polar`, `hI_holo`, `hPV_sing`,
`hI_sing`), this theorem absorbs four of them — `hMero`, `h_holo_cancel`,
`hPV_sing`, `hI_sing` — using the simple-pole hypothesis `hSimple`, the
Phase 4 `h_holo_cancel_of_conditionB` discharger, the Phase 5c
`hPV_sing_of_conditionB_singleCrossing` discharger, and the
`cpvIntegrandOn_finset_sum_intervalIntegrable` sum lemma. The remaining
hypotheses — `h_polar_cancel`, `hI_polar`, `hI_holo`, plus the geometric
crossing data — are not yet auto-derivable: the Laurent decomposition in
`hCondB` is extracted by `Classical.choose`, so `laurentHigherOrderPolar`
and `laurentHolomorphicRemainder` are *not* pointwise zero even for simple
poles, and their CPV-vanishing / integrability has to be supplied as data.

## Main results

* `hw_3_3_simple_with_crossData` — HW Theorem 3.3 for the simple-pole case,
  paper-faithful curve type, with crossings handled via `SingleCrossingData`.
  (Note: as written, `h_avoid_pairs` is unsatisfiable when γ actually crosses
  a pole; see `hw_3_3_simple_with_perPoleCPV` for the corrected paper-faithful
  formulation.)
* `hw_3_3_simple_with_perPoleCPV` — corrected paper-faithful theorem: replaces
  the inconsistent `h_avoid_pairs` + `crossData` block by per-pole CPV
  witnesses, with per-pole integrability auto-discharged.
* `hw_3_3_simple_with_perPoleCPV_avoids` — avoidance specialization with the
  per-pole CPV auto-discharged.

## Strategy

1. Derive `hMero` from `hSimple` via `HasSimplePoleAt.meromorphicAt`.
2. Discharge `h_holo_cancel` via `h_holo_cancel_of_conditionB` (Phase 4).
3. Discharge `hPV_sing` via `hPV_sing_of_conditionB_singleCrossing` (Phase 5c),
   feeding per-pole `SingleCrossingData` witnesses + geometric avoidance.
4. Derive the sum-form `hI_sing` from per-pole CPV-integrand integrability
   via `cpvIntegrandOn_finset_sum_intervalIntegrable` and unfolding the
   `principalPartSum` definition.
5. Apply `hw_3_3_paper` to combine everything.
-/

open Set Filter Topology Complex MeasureTheory
open scoped Real Interval

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-- **HW Theorem 3.3 — simple-pole case with crossings, paper-faithful curve.**

For a paper-faithful closed piecewise-`C¹` immersion `γ` null-homologous in
an open `U`, with `f` having simple poles at `S ⊆ U`, and conditions
(A')+(B), the CPV residue formula holds.

Compared to `hw_3_3_paper`, this theorem absorbs four oracle hypotheses
(`hMero`, `h_holo_cancel`, `hPV_sing`, `hI_sing`) and replaces them with:

* `hSimple` — every pole is simple (stronger than `MeromorphicAt`);
* `crossData` — per-pole `SingleCrossingData γ s` witness, supplying the
  geometric structure (unique crossing parameter `t₀`, far/near bounds,
  FTC expression, limit) needed to derive the generalized winding number
  at each `s`;
* `hδ_pos` and `h_avoid_pairs` — pairwise avoidance margin separating γ
  from every pole `s'` other than the current `s`;
* `h_int_perpole` — per-pole integrability of the CPV integrand for
  `residue f s / (z - s)`.

The remaining four hypotheses — `h_polar_cancel`, `hI_polar`, `hI_holo`,
`hCondA` — are kept because they are not yet auto-derivable: the Laurent
decomposition supplied by `hCondB.laurent_compatible` is extracted via
`Classical.choose`, so the polar-part / holomorphic-remainder functions
are not pointwise zero / continuous on the curve image without further
analysis. -/
theorem hw_3_3_simple_with_crossData
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (h_polar_cancel : HasCauchyPVOn S
      (laurentHigherOrderPolar hCondB)
      γ.toPwC1Immersion.toPiecewiseC1Path 0)
    (hI_polar : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (laurentHigherOrderPolar hCondB)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (hI_holo : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (laurentHolomorphicRemainder hCondB)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (crossData : ∀ s ∈ S,
      SingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (h_avoid_pairs : ∀ s ∈ S, ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc (0 : ℝ) 1,
      δ ≤ ‖γ.toPwC1Immersion.toPiecewiseC1Path t - s'‖)
    (h_int_perpole : ∀ s ∈ S, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => residue f s / (z - s))
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  -- 1. Derive `hMero` from `hSimple`.
  have hMero : ∀ s ∈ S, MeromorphicAt f s :=
    fun s hs => (hSimple s hs).meromorphicAt
  -- 2. Discharge `h_holo_cancel` via Phase 4.
  have h_holo_cancel : HasCauchyPVOn S (laurentHolomorphicRemainder hCondB) γP 0 :=
    h_holo_cancel_of_conditionB hU_open hU_ne hS_in_U hf γ h_null hSimple hCondB
  -- 3. Discharge `hPV_sing` via Phase 5c.
  have hPV_sing : HasCauchyPVOn S (principalPartSum S (fun s => residue f s)) γP
      (∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γP s * residue f s) :=
    hPV_sing_of_conditionB_singleCrossing hU_open hS_in_U γ hSimple hCondB
      crossData hδ_pos h_avoid_pairs h_int_perpole
  -- 4. Derive sum-form `hI_sing` from per-pole `h_int_perpole` (rfl-unfolding
  -- of `principalPartSum`).
  have hI_sing : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (principalPartSum S (fun s => residue f s))
        γP.toPath.extend ε t) volume 0 1 := fun ε hε =>
    cpvIntegrandOn_finset_sum_intervalIntegrable
      (ι_set := S) (S := S) (γ := γP) (ε := ε)
      (f := fun s z => residue f s / (z - s))
      (fun s hs => h_int_perpole s hs ε hε)
  -- 5. Compose via `hw_3_3_paper`.
  exact hw_3_3_paper hU_open S hS_in_U f hf γ h_null hMero hCondA hCondB
    h_polar_cancel h_holo_cancel hI_polar hI_holo hPV_sing hI_sing

/-- **CPV integrand integrability for the term `c / (z - s)`, `s ∈ S`.**

For a paper-faithful `γ : ClosedPwC1Immersion` and a pole `s ∈ S`, the CPV
integrand `cpvIntegrandOn S (c / (z - s)) γ.extend ε` is interval-integrable
on `[0, 1]` for every `ε > 0`. No avoidance hypothesis on `γ` is needed.

The cutoff `‖γ(t) - s‖ ≤ ε` (which fires inside the union over all poles in `S`,
hence at `s` in particular when γ approaches `s`) zeros the integrand exactly
where the singularity would occur. Outside the cutoff, the integrand is bounded
by `|c| / ε · ‖γ'(t)‖`, which is integrable since `γ'` is interval-integrable
on `[0, 1]` (TIGHT-6, `ClosedPwC1Curve.deriv_extend_intervalIntegrable`). -/
theorem cpvIntegrandOn_div_sub_intervalIntegrable_of_mem
    (γ : ClosedPwC1Immersion x) (S : Finset ℂ) {s : ℂ} (hs : s ∈ S) (c : ℂ)
    {ε : ℝ} (hε_pos : 0 < ε) :
    IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => c / (z - s))
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1 := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  set γE := γP.toPath.extend
  -- Pointwise norm bound `‖cpvIntegrandOn‖ ≤ |c|/ε · ‖γ'‖`.
  have h_norm_bound : ∀ t,
      ‖cpvIntegrandOn S (fun z => c / (z - s)) γE ε t‖ ≤
        ‖c‖ / ε * ‖deriv γE t‖ := by
    intro t
    simp only [cpvIntegrandOn]
    split_ifs with h
    · rw [norm_zero]
      exact mul_nonneg (div_nonneg (norm_nonneg _) hε_pos.le) (norm_nonneg _)
    · push Not at h
      rw [norm_mul, norm_div]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (norm_nonneg _) hε_pos (h s hs).le) (norm_nonneg _)
  -- γ' is interval-integrable on [0,1]; combine into the dominating bound.
  have h_bound_int : IntervalIntegrable
      (fun t => (‖c‖ / ε * ‖deriv γE t‖ : ℝ)) volume 0 1 :=
    (γ.toClosedPwC1Curve.deriv_extend_intervalIntegrable.norm).const_mul _
  -- Measurability of the CPV integrand.
  have h_meas : AEStronglyMeasurable
      (fun t => cpvIntegrandOn S (fun z => c / (z - s)) γE ε t)
      (volume.restrict (Ι (0 : ℝ) 1)) :=
    aestronglyMeasurable_cpvIntegrandOn S _ γP ε <|
      (measurable_const.div (γP.toPath.continuous_extend.measurable.sub
        measurable_const)).aestronglyMeasurable.mul
        (stronglyMeasurable_deriv _).aestronglyMeasurable
  refine IntervalIntegrable.mono_fun h_bound_int h_meas
    (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (div_nonneg (norm_nonneg _) hε_pos.le) (norm_nonneg _))]
  exact h_norm_bound t

/-- **HW Theorem 3.3 — simple poles, per-pole CPV witnesses (paper-faithful).**

A corrected paper-faithful formulation that **eliminates** the unsatisfiable
`crossData / hδ_pos / h_avoid_pairs / h_int_perpole` block of
`hw_3_3_simple_with_crossData` by demanding per-pole CPV witnesses directly:

* `h_per_pole_cpv s hs` — for each pole `s ∈ S`, the multi-pole CPV of
  `residue f s / (z - s)` along γ, with value `2πi · w_s · residue f s` where
  `w_s := generalizedWindingNumber γ s`.

The per-pole CPV integrand integrability is auto-discharged via
`cpvIntegrandOn_div_sub_intervalIntegrable_of_mem`.

The four Phase-3-style hypotheses (`h_polar_cancel`, `hI_polar`, `hI_holo`,
`hCondA`) remain because they are not yet auto-derivable (TIGHT-3 / TIGHT-4
project tickets). -/
theorem hw_3_3_simple_with_perPoleCPV
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (h_polar_cancel : HasCauchyPVOn S
      (laurentHigherOrderPolar hCondB)
      γ.toPwC1Immersion.toPiecewiseC1Path 0)
    (hI_polar : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (laurentHigherOrderPolar hCondB)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (hI_holo : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (laurentHolomorphicRemainder hCondB)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (h_per_pole_cpv : ∀ s ∈ S, HasCauchyPVOn S
      (fun z => residue f s / (z - s))
      γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s)) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  -- 1. Derive `hMero` from `hSimple`.
  have hMero : ∀ s ∈ S, MeromorphicAt f s :=
    fun s hs => (hSimple s hs).meromorphicAt
  -- 2. Discharge `h_holo_cancel` via Phase 4.
  have h_holo_cancel : HasCauchyPVOn S (laurentHolomorphicRemainder hCondB) γP 0 :=
    h_holo_cancel_of_conditionB hU_open hU_ne hS_in_U hf γ h_null hSimple hCondB
  -- 3. Auto-discharge per-pole integrability.
  have h_per_pole_int : ∀ s ∈ S, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => residue f s / (z - s))
        γP.toPath.extend ε t) volume 0 1 := fun s hs ε hε_pos =>
    cpvIntegrandOn_div_sub_intervalIntegrable_of_mem γ S hs (residue f s) hε_pos
  -- 4. Assemble `hPV_sing` via per-pole CPV finset sum.
  have hPV_sing : HasCauchyPVOn S (principalPartSum S (fun s => residue f s)) γP
      (∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γP s * residue f s) :=
    HasCauchyPVOn.finset_sum S h_per_pole_cpv h_per_pole_int
  -- 5. Derive sum-form `hI_sing`.
  have hI_sing : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (principalPartSum S (fun s => residue f s))
        γP.toPath.extend ε t) volume 0 1 := fun ε hε =>
    cpvIntegrandOn_finset_sum_intervalIntegrable
      (ι_set := S) (S := S) (γ := γP) (ε := ε)
      (f := fun s z => residue f s / (z - s))
      (fun s hs => h_per_pole_int s hs ε hε)
  -- 6. Compose via `hw_3_3_paper`.
  exact hw_3_3_paper hU_open S hS_in_U f hf γ h_null hMero hCondA hCondB
    h_polar_cancel h_holo_cancel hI_polar hI_holo hPV_sing hI_sing

/-- **HW Theorem 3.3 — simple-pole avoidance, paper-faithful curve, per-pole
CPV auto-discharge.** -/
theorem hw_3_3_simple_with_perPoleCPV_avoids
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (h_polar_cancel : HasCauchyPVOn S
      (laurentHigherOrderPolar hCondB)
      γ.toPwC1Immersion.toPiecewiseC1Path 0)
    (hI_polar : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (laurentHigherOrderPolar hCondB)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (hI_holo : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (laurentHolomorphicRemainder hCondB)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  -- Uniform avoidance margin `δ > 0`.
  obtain ⟨δ, hδ_pos, hδ_bd⟩ := avoids_finset_delta_bound γP S hγ_avoids
  -- Per-pole generalized winding number witnesses (existence via avoidance).
  have hw : ∀ s ∈ S, HasGeneralizedWindingNumber γP s
      (generalizedWindingNumber γP s) := fun s hs => by
    have hgw := hasGeneralizedWindingNumber_of_avoids
      ⟨δ, hδ_pos, fun t ht => hδ_bd s hs t ht⟩
    rw [hgw.eq]; exact hgw
  -- Per-pole CPV witnesses via singleton-plus-avoidance lift.
  have h_per_pole_cpv : ∀ s ∈ S, HasCauchyPVOn S
      (fun z => residue f s / (z - s)) γP
      (2 * ↑Real.pi * I * generalizedWindingNumber γP s * residue f s) :=
    fun s hs => hasCauchyPVOn_div_sub_of_singleton_and_avoid_others S hs (hw s hs)
      hδ_pos (fun s' hs' _ t ht => hδ_bd s' hs' t ht)
  exact hw_3_3_simple_with_perPoleCPV hU_open hU_ne S hS_in_U f hf γ h_null
    hSimple hCondA hCondB h_polar_cancel hI_polar hI_holo h_per_pole_cpv

/-- **HW Theorem 3.3 — simple poles, at most one pole crossed (paper-faithful).**

Replaces the inconsistent `crossData / hδ_pos / h_avoid_pairs` block of
`hw_3_3_simple_with_crossData` by the geometrically meaningful "at most one
crossing" hypothesis:

* `s_star : ℂ` and `hs_star_in : s_star ∈ S` — the distinguished pole;
* `hγ_avoids_others` — γ avoids every OTHER pole `s ∈ S \ {s*}`;
* `hw_star_singleton` — singleton CPV witness for `c / (z - s*)` at `s*`, of
  value `2πi · w_{s*} · c`. This may be built from a `SingleCrossingData γ s*`
  via `(D.hasCauchyPV.smul c)` after appropriate rescaling, or trivially from
  `hasCauchyPVOn_singleton_div_sub` if γ also happens to avoid `s*`.

Per-pole integrability is auto-discharged via
`cpvIntegrandOn_div_sub_intervalIntegrable_of_mem`. The Phase-3 oracles
(`h_polar_cancel`, `hI_polar`, `hI_holo`) remain. -/
theorem hw_3_3_simple_one_crossing_paper
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (h_polar_cancel : HasCauchyPVOn S
      (laurentHigherOrderPolar hCondB)
      γ.toPwC1Immersion.toPiecewiseC1Path 0)
    (hI_polar : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (laurentHigherOrderPolar hCondB)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (hI_holo : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (laurentHolomorphicRemainder hCondB)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (s_star : ℂ) (hs_star_in : s_star ∈ S)
    (hγ_avoids_others : ∀ s ∈ S, s ≠ s_star → ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s)
    (hw_star : HasGeneralizedWindingNumber
      γ.toPwC1Immersion.toPiecewiseC1Path s_star
      (generalizedWindingNumber
        γ.toPwC1Immersion.toPiecewiseC1Path s_star)) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  -- Get the avoidance margin `δ > 0` for the OTHER poles.
  have hT_avoids : ∀ s' ∈ (S.erase s_star), ∀ t ∈ Icc (0 : ℝ) 1, γP t ≠ s' :=
    fun s' hs' t ht =>
      hγ_avoids_others s' (Finset.mem_erase.mp hs').2 (Finset.mem_erase.mp hs').1 t ht
  obtain ⟨δ, hδ_pos, hδ_bd⟩ :=
    avoids_finset_delta_bound γP (S.erase s_star) hT_avoids
  -- Per-pole CPV at each `s ∈ S`:
  --   * `s = s_star`: combine `hw_star` with avoidance of `S \ {s_star}` via
  --     `hasCauchyPVOn_div_sub_of_singleton_and_avoid_others`.
  --   * `s ≠ s_star`: γ avoids `s` with margin δ, so the integrand
  --     `residue f s / (z - s)` is continuous on the image of γ. The CPV cutoff at
  --     `s_star` (where γ may cross) shrinks to a finite set as `ε → 0`, so dominated
  --     convergence via `hasCauchyPVOn_continuousOn_of_countable_preimage` yields the
  --     contour integral, which equals `2πi · w_s · residue f s`.
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  -- Finite preimage of S under γ (TIGHT-6 extension).
  have h_preimage : Set.Countable
      {t ∈ Icc (0 : ℝ) 1 | γP t ∈ (↑S : Set ℂ)} :=
    γ.preimage_countable S
  -- Per-pole CPV at s ∈ S: split into s = s_star and s ≠ s_star.
  have h_per_pole_cpv : ∀ s ∈ S, HasCauchyPVOn S
      (fun z => residue f s / (z - s)) γP
      (2 * ↑Real.pi * I * generalizedWindingNumber γP s * residue f s) := by
    intro s hs
    by_cases hs_eq : s = s_star
    · -- Case 1: s = s_star, use hw_star + avoidance of others.
      subst hs_eq
      exact hasCauchyPVOn_div_sub_of_singleton_and_avoid_others S hs hw_star hδ_pos
        fun s' hs' hs'_ne t ht => hδ_bd s' (Finset.mem_erase.mpr ⟨hs'_ne, hs'⟩) t ht
    · -- Case 2: s ≠ s_star. γ avoids s with margin δ.
      have h_avoid_s : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γP t - s‖ :=
        fun t ht => hδ_bd s (Finset.mem_erase.mpr ⟨hs_eq, hs⟩) t ht
      -- The integrand `residue f s / (z - s)` is continuous on the image of γ
      -- (γ avoids s); combine with the countable-preimage CPV machinery.
      have h_cont_on : ContinuousOn (fun z => residue f s / (z - s))
          (γP.toPath.extend '' Icc (0 : ℝ) 1) := by
        refine continuousOn_const.div
          (continuousOn_id.sub continuousOn_const) ?_
        rintro _ ⟨t, ht, rfl⟩ h_eq
        have h_p := h_avoid_s t ht
        rw [PiecewiseC1Path.extendedPath_eq, sub_eq_zero.mp h_eq, sub_self,
          norm_zero] at h_p
        linarith
      -- CPV via continuous + countable preimage; contour integral equals
      -- `2πi · w_s · residue f s` (γ avoids s).
      rw [← integral_simple_pole_eq_winding (c := residue f s) (s := s)
        ⟨δ, hδ_pos, h_avoid_s⟩]
      exact hasCauchyPVOn_continuousOn_of_countable_preimage S h_cont_on hLip h_preimage
  exact hw_3_3_simple_with_perPoleCPV hU_open hU_ne S hS_in_U f hf γ h_null
    hSimple hCondA hCondB h_polar_cancel hI_polar hI_holo h_per_pole_cpv

end LeanModularForms

end
