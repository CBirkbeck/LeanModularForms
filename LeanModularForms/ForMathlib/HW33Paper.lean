/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HW33Tight
import LeanModularForms.ForMathlib.HigherOrderAssembly
import LeanModularForms.ForMathlib.PaperPwC1Immersion

/-!
# HW Theorem 3.3 — paper-faithful curve form

A wrapper of `hw_3_3_tight` (`HW33Tight.lean`) that takes the paper-faithful
`ClosedPwC1Immersion` (defined in `PaperPwC1Immersion.lean`) instead of the
legacy `PwC1Immersion`. The conversion is via the canonical bridge
`ClosedPwC1Immersion.toPwC1Immersion`.

Compared to `hw_3_3_tight`, the *curve type* matches the paper (Hungerbühler–
Wasem, arXiv:1808.00997v2, page 3) verbatim:

* the partition includes the global endpoints `0` and `1`;
* the path is `C¹` on every closed sub-interval `[aₖ, aₖ₊₁]`;
* the within-derivative is non-vanishing on every closed piece.

The cancellation and integrability hypotheses are unchanged from `hw_3_3_tight`
— their auto-discharge belongs to TIGHT-3 / TIGHT-4 / B-6 closure and is
orthogonal to the curve formalization.

## Main result

* `hw_3_3_paper`: the paper-faithful curve-type version of HW Theorem 3.3.
-/

open Set Filter Topology Complex MeasureTheory

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-- **HW Theorem 3.3 — paper-faithful curve form.**

Same conclusion as `hw_3_3_tight`, but the curve `γ` is a paper-faithful
`ClosedPwC1Immersion` (partition includes endpoints, `C¹` on closed pieces,
within-derivative non-vanishing on closed pieces). Routes through the legacy
form via the bridge `ClosedPwC1Immersion.toPwC1Immersion`. -/
theorem hw_3_3_paper
    {U : Set ℂ} (hU : IsOpen U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (h_polar_cancel : HasCauchyPVOn S
      (laurentHigherOrderPolar hCondB)
      γ.toPwC1Immersion.toPiecewiseC1Path 0)
    (h_holo_cancel : HasCauchyPVOn S
      (laurentHolomorphicRemainder hCondB)
      γ.toPwC1Immersion.toPiecewiseC1Path 0)
    (hI_polar : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (laurentHigherOrderPolar hCondB)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (hI_holo : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (laurentHolomorphicRemainder hCondB)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (hPV_sing : HasCauchyPVOn S
      (principalPartSum S (fun s => residue f s))
      γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s))
    (hI_sing : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (principalPartSum S (fun s => residue f s))
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) :=
  hw_3_3_tight hU S hS_in_U f hf γ.toPwC1Immersion h_null hMero hCondA hCondB
    h_polar_cancel h_holo_cancel hI_polar hI_holo hPV_sing hI_sing

/-! ## Simple-pole avoidance specialization (clean, no oracle hypotheses)

Specialization to **simple poles** with `γ` *avoiding* every pole. In this case
conditions (A) and (B) of the paper are vacuously satisfied — there are no
crossings — and the theorem reduces to the classical residue formula. Cancellation
and integrability hypotheses are fully discharged via the B-6 / null-homologous
closure machinery. -/

/-- **HW Theorem 3.3 — simple-pole avoidance, paper-faithful curve, fully closed.**

For a paper-faithful closed piecewise `C¹` immersion `γ` null-homologous in
an open `U`, with `f` having simple poles at `S ⊆ U` *avoided* by `γ`, the
CPV residue formula holds with **no auxiliary cancellation, integrability,
`δ`-bound, Lipschitz, or boundedness hypotheses** — Lipschitz is auto-derived
from the piecewise-`C¹` closed-piece structure
(`ClosedPwC1Curve.lipschitzWith_extend`), and `hU_bounded` is lifted via
`winding_eventually_zero_cocompact_of_lipschitz` (TIGHT-12).

This is the **paper-faithful HW Theorem 3.3** for the simple-pole avoidance
case: every hypothesis matches the paper exactly. -/
theorem hw_3_3_simple_avoidance_paper
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  exact hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids_unbounded
    hU_open hU_ne S hS_in_U f hf γ.toPwC1Immersion h_null hSimplePoles
    hγ_avoids hLip

end LeanModularForms

end
