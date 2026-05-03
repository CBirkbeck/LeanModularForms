/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HW33ExitTimeWrapper

/-!
# Bridge: parametric symmetric-excision PV ↔ `HasCauchyPVOn`

This file provides infrastructure for bridging between the parametric
symmetric-excision PV form (used by `hw_theorem_3_3_odd_transverse_parametric`)
and the `HasCauchyPVOn` form used in the rest of the residue-theorem framework.

## Strategy

The single-pole `cpvIntegrandOn {s} f γ ε t` is `0` if `‖γ(t) - s‖ ≤ ε`,
else `f(γ(t)) · γ'(t)`. If for fixed `ε`, the set
`{t ∈ [0, 1] : ‖γ(t) - s‖ ≤ ε}` equals `[α, β]` (with
`0 ≤ α ≤ β ≤ 1`), then the cpvIntegrandOn integral on `[0, 1]`
equals `∫_0^α + ∫_β^1` (the symmetric-excision form).

Combined with the parametric Tendsto for the excision integral, this gives
`HasCauchyPVOn {s} f γ 0`.

This file provides the **pointwise step** of the bridge: identifying when
`cpvIntegrandOn {s}` equals the contour integrand or zero based on γ's
distance from `s`.

## Main results

* `cpvIntegrandOn_singleton_eq_contour_of_far`: `cpvIntegrandOn {s} f γ ε t`
  equals the contour integrand when `ε < ‖γ(t) - s‖`.

* `cpvIntegrandOn_singleton_eq_zero_of_close`: `cpvIntegrandOn {s} f γ ε t = 0`
  when `‖γ(t) - s‖ ≤ ε`.

* `cpvIntegrandOn_singleton_eq_indicator`: `cpvIntegrandOn {s} f γ ε t` equals
  `Set.indicator {t | ε < ‖γ(t) - s‖} (contourIntegrand f γ) t`.

These give the pointwise/measurable identification needed to bridge to
`HasCauchyPVOn`. The full integral splitting under a "shape" hypothesis
(set-equals-bracket form) builds on these.
-/

open Filter Topology MeasureTheory Set Complex
open scoped Classical Real Interval

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-- **CPV integrand for a singleton equals the contour integrand when γ is far
from `s`.** -/
theorem cpvIntegrandOn_singleton_eq_contour_of_far
    (γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε : ℝ}
    {t : ℝ} (h_far : ε < ‖γ.toPath.extend t - s‖) :
    cpvIntegrandOn {s} f γ.toPath.extend ε t =
      f (γ.toPath.extend t) * deriv γ.toPath.extend t := by
  apply cpvIntegrandOn_of_forall_gt
  intro s' hs'
  rw [Finset.mem_singleton] at hs'
  rw [hs']
  exact h_far

/-- **CPV integrand for a singleton is zero when γ is close to `s`.** -/
theorem cpvIntegrandOn_singleton_eq_zero_of_close
    (γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε : ℝ}
    {t : ℝ} (h_close : ‖γ.toPath.extend t - s‖ ≤ ε) :
    cpvIntegrandOn {s} f γ.toPath.extend ε t = 0 :=
  cpvIntegrandOn_of_exists_le ⟨s, Finset.mem_singleton_self s, h_close⟩

/-- **CPV integrand for a singleton as indicator.** Pointwise:

  `cpvIntegrandOn {s} f γ ε t = (Set.indicator A) (f(γ t) · γ'(t)) t`

where `A = {t | ε < ‖γ(t) - s‖}` is the "far from s" set. -/
theorem cpvIntegrandOn_singleton_eq_indicator
    (γ : PiecewiseC1Path x x) (s : ℂ) (f : ℂ → ℂ) (ε : ℝ) (t : ℝ) :
    cpvIntegrandOn {s} f γ.toPath.extend ε t =
      ({t | ε < ‖γ.toPath.extend t - s‖}.indicator
        (fun t => f (γ.toPath.extend t) * deriv γ.toPath.extend t)) t := by
  by_cases h : ε < ‖γ.toPath.extend t - s‖
  · have h_mem : t ∈ {t | ε < ‖γ.toPath.extend t - s‖} := h
    rw [Set.indicator_of_mem h_mem]
    exact cpvIntegrandOn_singleton_eq_contour_of_far γ h
  · have h_notmem : t ∉ {t | ε < ‖γ.toPath.extend t - s‖} := h
    rw [Set.indicator_of_notMem h_notmem]
    push Not at h
    exact cpvIntegrandOn_singleton_eq_zero_of_close γ h

end LeanModularForms

end
