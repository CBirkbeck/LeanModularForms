/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HW33LaurentPolarPart
import LeanModularForms.ForMathlib.HW33Closed
import LeanModularForms.ForMathlib.ResidueLinearity

/-!
# HW Theorem 3.3 — tight (paper-style) form

The tight `hw_3_3` theorem using the Laurent polar-part extraction from
`HW33LaurentPolarPart.lean`. Compared to
`generalizedResidueTheorem_higherOrder_under_B_closed` in `HW33Closed.lean`,
the user no longer supplies `h_decomp`, `h_polar`, `h_holo` — these are
extracted from condition (B)'s `laurent_compatible` data.

The user still supplies:
* The CPV-vanishing of the higher-order polar part (`h_polar_cancel`):
  derivable from per-pole `hasCauchyPVOn_singleton_pow_of_conditionB_assembled`
  + multi-pole composition.
* The CPV-vanishing of the holomorphic remainder (`h_holo_cancel`):
  derivable from Cauchy along null-homologous γ for analytic functions.
* Integrability hypotheses.
* The simple-pole `hPV_sing` (typically from `B-6` closure).

Compared to the original `generalizedResidueTheorem`, we eliminate:
- 4 functions (`h_polar`, `h_holo`, plus the implicit residue function args)
- 1 decomposition equation hypothesis (`h_decomp` — now definitional)

## Main result

* `hw_3_3_tight`: the paper-style form of HW Theorem 3.3, using the
  Laurent polar-part extraction. This is closer to the paper's statement
  than `generalizedResidueTheorem_higherOrder_under_B_closed`.
-/

open Filter Topology Set Complex MeasureTheory

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-- **HW Theorem 3.3 — tight (paper-style) form.**

For meromorphic `f` on `U` with poles at `S`, closed null-homologous
piecewise-C¹ immersion `γ` in `U`, conditions (A')+(B), the CPV equals
the winding-number-weighted residue formula.

Compared to `generalizedResidueTheorem_higherOrder_under_B_closed`, the
Laurent decomposition is **definitional** (extracted from condition (B)),
so the user need not supply `h_decomp`, `h_polar`, `h_holo` separately.

The hypotheses still required (until full automation):
* `h_polar_cancel`: the higher-order polar part `laurentHigherOrderPolar`
  has CPV zero. Discharged via per-pole (B)-closure + multi-pole composition.
* `h_holo_cancel`: the holomorphic remainder has CPV zero. Discharged via
  Cauchy + null-homology for the now-analytic `f - laurentPolarPartTotal`.
* Standard integrability conditions on the cpvIntegrandOn at each ε.
* `hPV_sing` for the simple-pole part (typically from `B-6`). -/
theorem hw_3_3_tight {U : Set ℂ} (hU : IsOpen U) (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S)) (γ : PwC1Immersion x x)
    (h_null : IsNullHomologous γ U) (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S)
    (h_polar_cancel : HasCauchyPVOn S (laurentHigherOrderPolar hCondB) γ.toPiecewiseC1Path 0)
    (h_holo_cancel : HasCauchyPVOn S (laurentHolomorphicRemainder hCondB) γ.toPiecewiseC1Path 0)
    (hI_polar : ∀ ε > 0, IntervalIntegrable (fun t => cpvIntegrandOn S
      (laurentHigherOrderPolar hCondB) γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (hI_holo : ∀ ε > 0, IntervalIntegrable (fun t => cpvIntegrandOn S
      (laurentHolomorphicRemainder hCondB) γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (hPV_sing : HasCauchyPVOn S (principalPartSum S (fun s => residue f s)) γ.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s))
    (hI_sing : ∀ ε > 0, IntervalIntegrable (fun t => cpvIntegrandOn S
      (principalPartSum S (fun s => residue f s))
      γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S f γ.toPiecewiseC1Path (2 * ↑Real.pi * I *
      ∑ s ∈ S, generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s) :=
  generalizedResidueTheorem_higherOrder_under_B_closed hU S hS_in_U f hf γ h_null hMero hCondA
    hCondB (laurentHigherOrderPolar hCondB) (laurentHolomorphicRemainder hCondB)
    (f_minus_pp_eq_higherOrder_plus_holo hCondB) h_polar_cancel h_holo_cancel hI_polar hI_holo
    hPV_sing hI_sing

end LeanModularForms

end
