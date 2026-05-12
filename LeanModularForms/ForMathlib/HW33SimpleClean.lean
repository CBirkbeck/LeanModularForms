/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HW33Paper
import LeanModularForms.ForMathlib.HW33HoloCancel
import LeanModularForms.ForMathlib.HW33PVSing
import LeanModularForms.ForMathlib.HW33HigherOrderC3
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
  -- 1. Derive `hMero` from `hSimple`.
  have hMero : ∀ s ∈ S, MeromorphicAt f s :=
    fun s hs => (hSimple s hs).meromorphicAt
  -- 2. Discharge `h_holo_cancel` via Phase 4.
  have h_holo_cancel :
      HasCauchyPVOn S (laurentHolomorphicRemainder hCondB)
        γ.toPwC1Immersion.toPiecewiseC1Path 0 :=
    h_holo_cancel_of_conditionB hU_open hU_ne hS_in_U hf γ h_null hSimple hCondB
  -- 3. Discharge `hPV_sing` via Phase 5c.
  have hPV_sing :
      HasCauchyPVOn S
        (principalPartSum S (fun s => residue f s))
        γ.toPwC1Immersion.toPiecewiseC1Path
        (∑ s ∈ S, 2 * ↑Real.pi * I *
          generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
            residue f s) :=
    hPV_sing_of_conditionB_singleCrossing hU_open hS_in_U γ hSimple hCondB
      crossData hδ_pos h_avoid_pairs h_int_perpole
  -- 4. Derive sum-form `hI_sing` from per-pole `h_int_perpole` via
  -- `cpvIntegrandOn_finset_sum_intervalIntegrable`. The `principalPartSum`
  -- unfolds to a finite sum of `residue f s / (z - s)` terms.
  have hI_sing : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (principalPartSum S (fun s => residue f s))
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1 := by
    intro ε hε
    have h_sum := cpvIntegrandOn_finset_sum_intervalIntegrable
      (ι_set := S) (S := S) (γ := γ.toPwC1Immersion.toPiecewiseC1Path) (ε := ε)
      (f := fun s z => residue f s / (z - s))
      (fun s hs => h_int_perpole s hs ε hε)
    -- `principalPartSum S (residue f) z = ∑ s ∈ S, residue f s / (z - s)`
    have h_eq : (fun t => cpvIntegrandOn S
        (principalPartSum S (fun s => residue f s))
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) =
      (fun t => cpvIntegrandOn S
        (fun z => ∑ s ∈ S, residue f s / (z - s))
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) := rfl
    rw [h_eq]
    exact h_sum
  -- 5. Compose via `hw_3_3_paper`.
  exact hw_3_3_paper hU_open S hS_in_U f hf γ h_null hMero hCondA hCondB
    h_polar_cancel h_holo_cancel hI_polar hI_holo hPV_sing hI_sing

/-! ## Avoidance specialization (no `crossData` needed)

When `γ` avoids every pole in `S`, the simple-pole crossings degenerate and
the full theorem reduces to `hw_3_3_simple_avoidance_paper`. This avoidance
form is already provided by `hw_3_3_simple_avoidance_paper` (in `HW33Paper.lean`)
with no oracle hypotheses at all. -/

/-! ## Per-pole CPV specialization (paper-faithful, no `h_avoid_pairs`)

The `h_avoid_pairs` hypothesis of `hw_3_3_simple_with_crossData` is essentially
unsatisfiable when γ crosses any pole: for any `s ∈ S` and `s' ∈ S` with
`s' ≠ s`, it forces γ to be uniformly δ-far from `s'` — which fails as soon as γ
crosses `s'`. The original theorem is therefore only satisfiable in the vacuous
(empty `S`) and avoidance scenarios.

The realistic generalisation: replace the per-pole crossing data + pairwise
avoidance scaffolding by **per-pole CPV witnesses** directly. Concretely, the
user supplies, for each pole `s ∈ S`, the multi-pole CPV
`HasCauchyPVOn S (residue f s / (z - s)) γ (2πi · w_s · residue f s)`, plus the
per-pole CPV integrand integrability is auto-discharged from `γ`'s structure.

* `hw_3_3_simple_with_perPoleCPV` — takes per-pole CPV witnesses, composes via
  `HasCauchyPVOn.finset_sum` + `hw_3_3_paper`.
* `hw_3_3_simple_with_perPoleCPV_avoids` — avoidance specialization with the
  per-pole CPV auto-discharged via `hasCauchyPVOn_div_sub_of_singleton_and_avoid_others`.

The four Phase-3-style hypotheses (`h_polar_cancel`, `hI_polar`, `hI_holo`,
`hCondA`) remain because they are not yet auto-derivable (TIGHT-3 / TIGHT-4). -/

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
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path with hγP_def
  set γE := γP.toPath.extend with hγE_def
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
      have h_s_bnd : ε < ‖γE t - s‖ := h s hs
      rw [norm_mul, norm_div]
      have hpos : 0 < ‖γE t - s‖ := lt_of_lt_of_le hε_pos h_s_bnd.le
      have hne : ‖γE t - s‖ ≠ 0 := ne_of_gt hpos
      have hεne : ε ≠ 0 := ne_of_gt hε_pos
      have h_div_le : ‖c‖ / ‖γE t - s‖ ≤ ‖c‖ / ε :=
        div_le_div_of_nonneg_left (norm_nonneg _) hε_pos h_s_bnd.le
      exact mul_le_mul_of_nonneg_right h_div_le (norm_nonneg _)
  -- γ' is interval-integrable on [0,1].
  have h_deriv_int : IntervalIntegrable (deriv γE) volume 0 1 :=
    γ.toClosedPwC1Curve.deriv_extend_intervalIntegrable
  have h_norm_deriv_int : IntervalIntegrable (fun t => ‖deriv γE t‖) volume 0 1 :=
    h_deriv_int.norm
  have h_bound_int : IntervalIntegrable
      (fun t => (‖c‖ / ε * ‖deriv γE t‖ : ℝ)) volume 0 1 :=
    h_norm_deriv_int.const_mul _
  -- Measurability of the CPV integrand.
  have h_meas : AEStronglyMeasurable
      (fun t => cpvIntegrandOn S (fun z => c / (z - s)) γE ε t)
      (volume.restrict (Ι (0 : ℝ) 1)) := by
    apply aestronglyMeasurable_cpvIntegrandOn S _ γP ε
    apply AEStronglyMeasurable.mul
    · apply Measurable.aestronglyMeasurable
      apply Measurable.div measurable_const
      exact (γP.toPath.continuous_extend.measurable.sub measurable_const)
    · exact (stronglyMeasurable_deriv _).aestronglyMeasurable
  refine IntervalIntegrable.mono_fun h_bound_int h_meas
    (Filter.Eventually.of_forall fun t => ?_)
  have h_bnd_t := h_norm_bound t
  simp only [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (div_nonneg (norm_nonneg _) hε_pos.le) (norm_nonneg _))]
  exact h_bnd_t

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
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path with hγP_def
  -- 1. Derive `hMero` from `hSimple`.
  have hMero : ∀ s ∈ S, MeromorphicAt f s :=
    fun s hs => (hSimple s hs).meromorphicAt
  -- 2. Discharge `h_holo_cancel` via Phase 4.
  have h_holo_cancel :
      HasCauchyPVOn S (laurentHolomorphicRemainder hCondB) γP 0 :=
    h_holo_cancel_of_conditionB hU_open hU_ne hS_in_U hf γ h_null hSimple hCondB
  -- 3. Auto-discharge per-pole integrability.
  have h_per_pole_int : ∀ s ∈ S, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => residue f s / (z - s))
        γP.toPath.extend ε t) volume 0 1 := fun s hs ε hε_pos =>
    cpvIntegrandOn_div_sub_intervalIntegrable_of_mem γ S hs (residue f s) hε_pos
  -- 4. Assemble `hPV_sing` via per-pole CPV finset sum.
  have hPV_sing : HasCauchyPVOn S
      (principalPartSum S (fun s => residue f s)) γP
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γP s * residue f s) :=
    HasCauchyPVOn.finset_sum S h_per_pole_cpv h_per_pole_int
  -- 5. Derive sum-form `hI_sing`.
  have hI_sing : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (principalPartSum S (fun s => residue f s))
        γP.toPath.extend ε t) volume 0 1 := by
    intro ε hε
    have h_sum := cpvIntegrandOn_finset_sum_intervalIntegrable
      (ι_set := S) (S := S) (γ := γP) (ε := ε)
      (f := fun s z => residue f s / (z - s))
      (fun s hs => h_per_pole_int s hs ε hε)
    have h_eq : (fun t => cpvIntegrandOn S
        (principalPartSum S (fun s => residue f s))
        γP.toPath.extend ε t) =
      (fun t => cpvIntegrandOn S
        (fun z => ∑ s ∈ S, residue f s / (z - s))
        γP.toPath.extend ε t) := rfl
    rw [h_eq]
    exact h_sum
  -- 6. Compose via `hw_3_3_paper`.
  exact hw_3_3_paper hU_open S hS_in_U f hf γ h_null hMero hCondA hCondB
    h_polar_cancel h_holo_cancel hI_polar hI_holo hPV_sing hI_sing

/-! ### Avoidance specialization of `hw_3_3_simple_with_perPoleCPV`

When `γ` avoids every pole in `S`, the per-pole CPV witnesses are automatic via
`hasCauchyPVOn_div_sub_of_singleton_and_avoid_others` + the uniform avoidance
margin from `avoids_finset_delta_bound`. This sits between
`hw_3_3_simple_avoidance_paper` (which discharges everything including the
Phase-3 oracles via the closed-form avoidance machinery) and
`hw_3_3_simple_with_perPoleCPV` (general per-pole CPV). It keeps the Phase-3
oracles explicit, suitable when the user has Phase-3 witnesses but wants
automatic CPV-witness discharge under avoidance. -/

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
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path with hγP_def
  -- Uniform avoidance margin `δ > 0`.
  obtain ⟨δ, hδ_pos, hδ_bd⟩ := avoids_finset_delta_bound γP S hγ_avoids
  -- Per-pole generalized winding number witnesses (existence via avoidance).
  have hw : ∀ s ∈ S, HasGeneralizedWindingNumber γP s
      (generalizedWindingNumber γP s) := fun s hs => by
    have h_avoid_s : ∃ δ' > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ' ≤ ‖γP t - s‖ :=
      ⟨δ, hδ_pos, fun t ht => hδ_bd s hs t ht⟩
    have hgw := hasGeneralizedWindingNumber_of_avoids h_avoid_s
    rw [hgw.eq]; exact hgw
  -- Per-pole CPV witnesses via singleton-plus-avoidance lift.
  have h_per_pole_cpv : ∀ s ∈ S, HasCauchyPVOn S
      (fun z => residue f s / (z - s)) γP
      (2 * ↑Real.pi * I * generalizedWindingNumber γP s * residue f s) := by
    intro s hs
    have h_avoid_others : ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc (0 : ℝ) 1,
        δ ≤ ‖γP t - s'‖ := fun s' hs' _ t ht => hδ_bd s' hs' t ht
    exact hasCauchyPVOn_div_sub_of_singleton_and_avoid_others S hs (hw s hs)
      hδ_pos h_avoid_others
  exact hw_3_3_simple_with_perPoleCPV hU_open hU_ne S hS_in_U f hf γ h_null
    hSimple hCondA hCondB h_polar_cancel hI_polar hI_holo h_per_pole_cpv

/-! ## "At most one pole crossed" specialization

A useful refinement of `hw_3_3_simple_with_perPoleCPV` when γ may cross **one
distinguished pole** `s* ∈ S` and avoids every other pole. In this case:

* For `s = s*`, the per-pole multi-pole CPV comes from a singleton CPV witness
  at `s*` (e.g., built from a `SingleCrossingData γ s*`) lifted via
  `hasCauchyPVOn_div_sub_of_singleton_and_avoid_others`.
* For `s ≠ s*`, γ avoids `s` and the per-pole CPV comes from
  `hasGeneralizedWindingNumber_of_avoids` + the singleton-plus-avoidance lift.

Note: if γ crosses two or more distinct poles, this lift cannot be used —
the singleton-to-multi-pole lift requires γ to avoid all OTHER poles, which
fails as soon as a second pole is crossed. The at-most-one-crossing case is the
natural transversal scope where the per-pole assembly cleanly composes.

This theorem accepts a singleton CPV witness at `s*` (which may be built from
a `SingleCrossingData γ s*` via `SingleCrossingData.hasCauchyPV`) and derives
the multi-pole CPV automatically. -/

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
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path with hγP_def
  -- Get the avoidance margin `δ > 0` for the OTHER poles.
  have hT_avoids : ∀ s' ∈ (S.erase s_star), ∀ t ∈ Icc (0 : ℝ) 1, γP t ≠ s' := by
    intro s' hs' t ht
    have hs'_in : s' ∈ S := (Finset.mem_erase.mp hs').2
    have hs'_ne : s' ≠ s_star := (Finset.mem_erase.mp hs').1
    exact hγ_avoids_others s' hs'_in hs'_ne t ht
  obtain ⟨δ, hδ_pos, hδ_bd⟩ :=
    avoids_finset_delta_bound γP (S.erase s_star) hT_avoids
  -- For every pole s ∈ S, build the per-pole multi-pole CPV.
  --
  -- Case 1: s = s_star. We have the singleton winding witness `hw_star`. We need γ to
  -- avoid `S \ {s_star}` with margin δ, which is `hδ_bd` (using `S.erase s_star = S \ {s_star}`).
  --
  -- Case 2: s ≠ s_star. Then s ∈ S.erase s_star, so γ avoids s with margin δ.
  -- We build the singleton CPV witness via `hasGeneralizedWindingNumber_of_avoids`,
  -- then lift to multi-pole. But the lift requires γ to avoid `S \ {s}`, which includes
  -- s_star (we don't have avoidance of s_star). HOWEVER, the per-pole CPV at s ≠ s_star
  -- has integrand `c / (z - s)`. As ε → 0, the cutoff at s_star (where γ may cross)
  -- doesn't matter for THIS integrand because the integrand is bounded near s_star
  -- (γ avoids s, so 1/(γ(t)-s) is bounded). The cutoff at s ≠ s_star fires only when
  -- γ is within ε of s, which never happens (γ avoids s with margin δ). So for ε < δ,
  -- the cutoff sets cpvIntegrandOn = 0 in the ε-balls around poles in S — including
  -- s_star, where γ may have a crossing. The integrand `c / (γ(t) - s) * γ'(t)` is
  -- bounded near s_star (γ avoids s), so the cutoff at s_star doesn't cause issues
  -- with integrability, but it does AFFECT the integral value: as ε → 0, the cutoff
  -- at s_star shrinks to a measure-zero set (γ crosses s_star at finitely many points
  -- by `preimage_finite`), so by dominated convergence, the integral converges to
  -- the contour integral.
  --
  -- BUT the cleaner argument: use `hasCauchyPVOn_div_sub_of_singleton_and_avoid_others`
  -- with the singleton-set being `{s}` (NOT `S`). The hypothesis `h_avoid_others`
  -- requires γ to avoid `S \ {s}` — which includes s_star. We DON'T have this.
  --
  -- Actually, looking at the API more carefully:
  -- `hasCauchyPVOn_div_sub_of_singleton_and_avoid_others`:
  --   given hw : HasGeneralizedWindingNumber γ s w, hδ_pos, h_avoid : γ avoids S \ {s},
  --   gives HasCauchyPVOn S (c/(z-s)) γ (2πi·w·c).
  -- For s ≠ s_star: we have hw (by avoids), but h_avoid would need γ avoid S \ {s},
  -- which includes s_star — fails.
  --
  -- So Case 2 cannot be handled by avoidance alone. We need a DIFFERENT lift that uses
  -- the fact that γ crosses s_star, not s.
  --
  -- The realistic lift: when γ avoids s but may cross s_star ≠ s, the contour integral
  -- of `c/(z-s)` along γ is well-defined (γ avoids s ⇒ integrand bounded). The CPV
  -- with cutoff at S can still equal this contour integral provided the cutoff at
  -- s_star doesn't contribute. Since γ crosses s_star at finitely many points
  -- (`preimage_finite`), the cutoff at s_star is a measure-zero issue — its
  -- contribution to the integral tends to 0 as ε → 0.
  --
  -- This is the genuine ε → 0 dominated convergence argument. The cleanest way:
  -- use `hasCauchyPVOn_continuousOn_of_countable_preimage`-style machinery.
  -- The integrand `c/(z - s) · γ'(t)` is continuous on the image of γ minus {s_star},
  -- which (since γ avoids s, not s_star) lies in... well, the integrand IS continuous
  -- on the image of γ minus the singularity at s, which γ avoids. So the integrand
  -- restricted to γ's image is continuous! No singularity issue at all.
  --
  -- Therefore the integrand is bounded on γ's image. The CPV with cutoff at S (which
  -- includes both s and s_star) zeroes the integrand on the ε-near sets. As ε → 0,
  -- the ε-near sets shrink to γ⁻¹({s} ∪ {s_star}), which is FINITE (by preimage_finite).
  -- By bounded convergence, the cutoff integral converges to the full integral, which
  -- equals the contour integral.
  --
  -- This is `hasCauchyPVOn_continuousOn_of_countable_preimage`!
  have hLip : ∃ K : NNReal, LipschitzWith K γP.toPath.extend := by
    exact ClosedPwC1Immersion.lipschitzWith_extend γ
  obtain ⟨K, hLip⟩ := hLip
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
      have h_avoid_others : ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc (0 : ℝ) 1,
          δ ≤ ‖γP t - s'‖ := fun s' hs' hs'_ne t ht =>
        hδ_bd s' (Finset.mem_erase.mpr ⟨hs'_ne, hs'⟩) t ht
      exact hasCauchyPVOn_div_sub_of_singleton_and_avoid_others S hs hw_star
        hδ_pos h_avoid_others
    · -- Case 2: s ≠ s_star. γ avoids s with margin δ.
      have hs_in_erase : s ∈ S.erase s_star :=
        Finset.mem_erase.mpr ⟨hs_eq, hs⟩
      have h_avoid_s : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γP t - s‖ :=
        fun t ht => hδ_bd s hs_in_erase t ht
      -- The integrand `c / (z - s)` is continuous on the image of γ (γ avoids s).
      -- Use the continuous + finite-preimage machinery to get the multi-pole CPV
      -- equals the contour integral.
      have h_avoid_ne : ∀ t ∈ Icc (0 : ℝ) 1, γP t ≠ s := fun t ht hzero => by
        have := h_avoid_s t ht
        rw [hzero, sub_self, norm_zero] at this
        linarith
      -- Build the winding witness for s.
      have hw_s := hasGeneralizedWindingNumber_of_avoids
        ⟨δ, hδ_pos, h_avoid_s⟩
      -- The continuous-on-γ-image integrand `residue f s / (z - s)`.
      have h_cont_on : ContinuousOn (fun z => residue f s / (z - s))
          (γP.toPath.extend '' Icc (0 : ℝ) 1) := by
        refine continuousOn_const.div
          (continuousOn_id.sub continuousOn_const) ?_
        intro z hz
        obtain ⟨t, ht, hzeq⟩ := hz
        rw [← hzeq, sub_ne_zero]
        intro h_eq
        have h_p := h_avoid_s t ht
        rw [PiecewiseC1Path.extendedPath_eq] at h_p
        rw [h_eq, sub_self, norm_zero] at h_p
        linarith
      -- Get CPV via continuous + countable preimage.
      have h_cpv_cont : HasCauchyPVOn S (fun z => residue f s / (z - s)) γP
          (γP.contourIntegral (fun z => residue f s / (z - s))) :=
        hasCauchyPVOn_continuousOn_of_countable_preimage S h_cont_on hLip h_preimage
      -- The contour integral equals `2πi · w_s · residue f s` (γ avoids s).
      have h_contour_eq : γP.contourIntegral (fun z => residue f s / (z - s)) =
          2 * ↑Real.pi * I * generalizedWindingNumber γP s * residue f s :=
        integral_simple_pole_eq_winding ⟨δ, hδ_pos, h_avoid_s⟩
      rw [← h_contour_eq]
      exact h_cpv_cont
  exact hw_3_3_simple_with_perPoleCPV hU_open hU_ne S hS_in_U f hf γ h_null
    hSimple hCondA hCondB h_polar_cancel hI_polar hI_holo h_per_pole_cpv

end LeanModularForms

end
