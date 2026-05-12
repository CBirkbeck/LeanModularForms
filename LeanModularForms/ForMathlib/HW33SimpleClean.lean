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

## Main result

* `hw_3_3_simple_with_crossData` — HW Theorem 3.3 for the simple-pole case,
  paper-faithful curve type, with crossings handled via `SingleCrossingData`.

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

end LeanModularForms

end
