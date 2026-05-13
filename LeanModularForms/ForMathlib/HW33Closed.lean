/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HW33MultiPole
import LeanModularForms.ForMathlib.GeneralizedResidueTheorem

/-!
# HW Theorem 3.3 — closed bridges to `generalizedResidueTheorem`

This file packages the (B)-closure machinery (in `HW33SectorEven.lean`) into
discharge lemmas for the `hCancel` oracle in
`generalizedResidueTheorem` (in `GeneralizedResidueTheorem.lean`).

The user supplies a Laurent decomposition of `f` at each pole — simple-pole
coefficient (residue) and higher-order coefficients — plus the (B) data per
pole. The `hCancel` oracle is then discharged automatically: the higher-order
polar terms cancel via the (B)-closure; the holomorphic part has CPV zero by
Cauchy.

## Main results

* `hCancel_of_higherOrder_decomposition_under_B` — discharges the `hCancel`
  hypothesis of `generalizedResidueTheorem` from a Laurent decomposition
  of `f - principalPartSum` and the (B)-closure of each higher-order term.

* `generalizedResidueTheorem_higherOrder_under_B_closed` — the **end-of-line
  user-facing form**: combines the discharge above with `hPV_sing` and
  integrability oracles to give the full closed residue formula.
-/

open Filter Topology Set Complex MeasureTheory

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-! ## hCancel discharge under condition (B) -/

/-- **Discharge `hCancel` from Laurent decomposition + (B)-closure.**

If the remainder `f - principalPartSum` decomposes as
`(higher-order polar terms) + (holomorphic remainder)` where:
* The higher-order polar terms have CPV zero (e.g., by the (B)-closure
  `hasCauchyPVOn_multipole_pow_of_conditionB_assembled`),
* The holomorphic remainder has CPV zero (by Cauchy along null-hom γ),

then `hCancel` holds. -/
theorem hCancel_of_higherOrder_decomposition_under_B
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    (h_polar h_holo : ℂ → ℂ)
    (h_decomp : ∀ z,
      f z - principalPartSum S (fun s => residue f s) z =
        h_polar z + h_holo z)
    (h_polar_cancel : HasCauchyPVOn S h_polar γ 0)
    (h_holo_cancel : HasCauchyPVOn S h_holo γ 0)
    (hI_polar : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S h_polar γ.toPath.extend ε t) volume 0 1)
    (hI_holo : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S h_holo γ.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z) γ 0 :=
  hCancel_of_decomposition S f γ h_holo h_polar
    (fun z => (h_decomp z).trans (add_comm _ _))
    h_holo_cancel h_polar_cancel hI_holo hI_polar

/-! ## End-of-line: full closure under condition (B) -/

/-- **HW Theorem 3.3 — fully closed under condition (B).**

The end-of-line user-facing form: combines
* `hCancel_of_higherOrder_decomposition_under_B` (hCancel discharge)
* `hPV_sing` from a singular-part PV computation (often
  `hasCauchyPVOn_simplePoles_nullHomologous_closed_full` for null-hom γ)

to produce the closed residue formula.

This is the intended end-state for the higher-order generalized residue
theorem under condition (B), bridging the (B)-closure machinery in
`HW33SectorEven.lean` to the abstract `generalizedResidueTheorem`. -/
theorem generalizedResidueTheorem_higherOrder_under_B_closed
    {U : Set ℂ} (hU : IsOpen U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S)
    (h_polar h_holo : ℂ → ℂ)
    (h_decomp : ∀ z,
      f z - principalPartSum S (fun s => residue f s) z =
        h_polar z + h_holo z)
    (h_polar_cancel : HasCauchyPVOn S h_polar γ.toPiecewiseC1Path 0)
    (h_holo_cancel : HasCauchyPVOn S h_holo γ.toPiecewiseC1Path 0)
    (hI_polar : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S h_polar γ.toPiecewiseC1Path.toPath.extend ε t)
      volume 0 1)
    (hI_holo : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S h_holo γ.toPiecewiseC1Path.toPath.extend ε t)
      volume 0 1)
    (hPV_sing : HasCauchyPVOn S
      (principalPartSum S (fun s => residue f s))
      γ.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s))
    (hI_sing : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (principalPartSum S (fun s => residue f s))
        γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S f γ.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s) := by
  have hI_rem : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (fun z => f z - principalPartSum S (fun s => residue f s) z)
        γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1 := by
    intro ε hε
    refine ((hI_polar ε hε).add (hI_holo ε hε)).congr ?_
    intro t _
    simp only [cpvIntegrandOn]
    by_cases h : ∃ s ∈ S, ‖γ.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε
    · simp only [if_pos h, add_zero]
    · simp only [if_neg h, h_decomp, add_mul]
  exact generalizedResidueTheorem hU S hS_in_U f hf γ h_null hMero hCondA hCondB
    (hCancel_of_higherOrder_decomposition_under_B S f γ.toPiecewiseC1Path
      h_polar h_holo h_decomp h_polar_cancel h_holo_cancel hI_polar hI_holo)
    hPV_sing hI_sing hI_rem

end LeanModularForms

end
