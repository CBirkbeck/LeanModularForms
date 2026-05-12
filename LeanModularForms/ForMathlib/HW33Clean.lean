/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HW33SimpleClean
import LeanModularForms.ForMathlib.HW33LaurentSimple

/-!
# HW Theorem 3.3 — final paper-faithful clean form

This file composes the **fully discharged paper-faithful** statement of
Hungerbühler–Wasem Theorem 3.3 for the simple-pole case with crossings.

Compared to `hw_3_3_paper`, which exposes six oracle hypotheses
(`h_polar_cancel`, `h_holo_cancel`, `hI_polar`, `hI_holo`, `hPV_sing`,
`hI_sing`) plus `hMero`, this final form discharges all of them:

* `h_polar_cancel` via Laurent uniqueness (TIGHT-3-Simple,
  `h_polar_cancel_of_conditionB_simple`).
* `h_holo_cancel` via Phase 4 (`h_holo_cancel_of_conditionB`).
* `hI_polar` via Laurent uniqueness (`hI_polar_of_conditionB_simple`).
* `hI_holo` via Laurent uniqueness (`hI_holo_of_conditionB_simple`).
* `hPV_sing` via Phase 5c +
  `hasCauchyPVOn_continuousOn_of_countable_preimage`.
* `hI_sing` via per-pole integrability + `cpvIntegrandOn_finset_sum`.
* `hMero` via `HasSimplePoleAt.meromorphicAt`.

## Main results

* `hw_3_3_clean` — single-crossing paper-faithful form. Takes the 8 paper
  hypotheses + 4 single-crossing hypotheses (`s_star`, `hs_star_in`,
  `hγ_avoids_others`, `hw_star`).

* `hw_3_3_clean_avoids` — full avoidance specialization. Takes only the
  8 paper hypotheses + `hγ_avoids` + `hs_ne`. The single-crossing data
  is constructed automatically from avoidance.
-/

noncomputable section

namespace LeanModularForms

open Set Filter Topology Complex MeasureTheory
open scoped Real Interval

variable {x : ℂ}

/-- **HW Theorem 3.3 — paper-faithful, simple poles, single crossing, clean form.**

This is the **cleanest paper-faithful** statement of HW Theorem 3.3 currently
achievable for the simple-pole case with crossings. Compared to
`hw_3_3_paper`, six oracle hypotheses are discharged automatically; only the
single-crossing geometric input remains.

**Paper hypotheses** (8): `hU_open, hU_ne, hS_in_U, hf, h_null, hSimple, hCondA, hCondB`.

**Single-crossing input** (4): `s_star ∈ S`, γ avoids every other pole, and the
generalized winding number at `s_star` exists. The latter is the irreducible
CPV-existence condition at the crossing; for the avoidance specialization
(`hw_3_3_clean_avoids`) this is automatic.

**Internally discharged** (7 oracles):
* `h_holo_cancel` via Phase 4 (`h_holo_cancel_of_conditionB`).
* `hPV_sing` via Phase 5c (`hPV_sing_of_conditionB_singleCrossing` →
  `hasCauchyPVOn_continuousOn_of_countable_preimage` for non-s* poles).
* `hI_sing` from per-pole integrability + finset sum.
* `h_polar_cancel` via Laurent uniqueness (`h_polar_cancel_of_conditionB_simple`).
* `hI_polar` via Laurent uniqueness (`hI_polar_of_conditionB_simple`).
* `hI_holo` via Laurent uniqueness (`hI_holo_of_conditionB_simple`).
* `hMero` via `HasSimplePoleAt.meromorphicAt`. -/
theorem hw_3_3_clean
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
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
  have h_polar_cancel := h_polar_cancel_of_conditionB_simple hU_open hU_ne hS_in_U γ
    h_null hSimple hCondB
  have hI_polar := hI_polar_of_conditionB_simple hU_open hS_in_U γ h_null hSimple hCondB
  have hI_holo := hI_holo_of_conditionB_simple hU_open hS_in_U hf γ h_null hSimple hCondB
  exact hw_3_3_simple_one_crossing_paper hU_open hU_ne S hS_in_U f hf γ h_null
    hSimple hCondA hCondB h_polar_cancel hI_polar hI_holo s_star hs_star_in
    hγ_avoids_others hw_star

/-- **HW Theorem 3.3 — paper-faithful, simple poles, full avoidance, clean form.**

The 8-hypothesis paper-faithful HW 3.3 statement when γ avoids every pole. All
conditions reduce to their natural avoidance forms. Compared to
`hw_3_3_simple_avoidance_paper`, this version exposes the Condition (A')/(B)
hypotheses explicitly (vacuous under full avoidance), giving a uniform
interface with the crossing case `hw_3_3_clean`. -/
theorem hw_3_3_clean_avoids
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s)
    (hs_ne : S.Nonempty) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  obtain ⟨s_star, hs_star_in⟩ := hs_ne
  have hγ_avoids_others : ∀ s ∈ S, s ≠ s_star → ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s :=
    fun s hs _ t ht => hγ_avoids s hs t ht
  obtain ⟨δ, hδ_pos, hδ_bd⟩ :=
    avoids_finset_delta_bound γ.toPwC1Immersion.toPiecewiseC1Path S hγ_avoids
  have hw_raw := hasGeneralizedWindingNumber_of_avoids
    ⟨δ, hδ_pos, hδ_bd s_star hs_star_in⟩
  have hw_star : HasGeneralizedWindingNumber
      γ.toPwC1Immersion.toPiecewiseC1Path s_star
      (generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s_star) :=
    hw_raw.eq.symm ▸ hw_raw
  exact hw_3_3_clean hU_open hU_ne S hS_in_U f hf γ h_null hSimple hCondA
    hCondB s_star hs_star_in hγ_avoids_others hw_star

end LeanModularForms

end
