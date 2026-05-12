/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HW33LaurentPolarPart
import LeanModularForms.ForMathlib.HW33HoloCancel
import LeanModularForms.ForMathlib.SimplePoleIntegral

/-!
# HW Theorem 3.3 — discharge `hPV_sing` (singular CPV)

This file discharges the `hPV_sing` oracle in `hw_3_3_paper` / `hw_3_3_tight`.
The strategy:

1. **Per-pole CPV witness (input)**: for each `s ∈ S`, the caller supplies
   `HasCauchyPVOn S (fun z => c s / (z - s)) γ (2πi · w · c s)`. This isolates
   the genuinely analytic content (existence of CPV at each potential crossing).

2. **Multi-pole assembly (this file)**: sum the per-pole CPVs via
   `HasCauchyPVOn.finset_sum`, given per-pole integrability of the CPV integrand.

3. **Recognize principal-part-sum**: `principalPartSum S c z = ∑ s, c s / (z - s)`.

## Main results

* `hPV_sing_from_per_pole_cpv` — assemble `hPV_sing` from per-pole CPV witnesses
  and per-pole integrability. The most flexible form.

* `hasCauchyPVOn_div_sub_of_singleton_and_avoid_others` — build a per-pole CPV
  witness when γ has a single crossing among `S` (avoidance of the other poles
  via a global margin `δ > 0`).

* `hPV_sing_of_winding_and_avoid_others` — combine the per-pole witness builder
  with the sum assembly; closed form when γ has at most one crossing per pole.

* `hPV_sing_of_conditionB` — wrap with the master-template hypotheses
  (`SatisfiesConditionB`, `HasSimplePoleAt`, etc.) for direct plug-in into
  `hw_3_3_paper`.

## Why per-pole CPV is taken as input

For γ that **crosses** a simple pole `s`, the CPV of `1/(z - s)` along γ requires
geometric data beyond what `SatisfiesConditionB` exposes for `k = 0`. One needs
the path γ to have well-defined left/right tangents at the crossing parameter
(provided by `ClosedPwC1Immersion.toPwC1Immersion` via `left_deriv_limit` /
`right_deriv_limit`), strict (anti-)monotonicity of `‖γ - s‖` near the crossing,
and an avoidance margin on the outer regions. Assembling all this into a
`HasGeneralizedWindingNumber γ s w` witness is Phase 6.1 of the master plan;
here we accept it as input.

## Note on hypothesis weakening

`hCondB`, `hSimple` are NOT used to derive the conclusion. They are kept in
`hPV_sing_of_conditionB` for **signature consistency** with the master template.
-/

open Set Filter Topology Complex MeasureTheory
open scoped Real Interval

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-! ## Per-pole CPV witness — singleton-to-multi-pole lift under avoidance -/

/-- **Per-pole CPV from singleton plus avoidance of other poles.** If `s ∈ S`,
γ has generalized winding number `w` at `s`, and γ avoids the other poles
`S \ {s}` with positive margin `δ`, then the CPV of `c / (z - s)` over the full
pole set `S` equals `2πi · w · c`.

This is the case when γ has at most a single crossing among `S`, namely at `s`.
The avoidance margin ensures the cutoff at `S \ {s}` doesn't fire for small ε. -/
theorem hasCauchyPVOn_div_sub_of_singleton_and_avoid_others
    {γ : PiecewiseC1Path x x} (S : Finset ℂ) {s : ℂ} {c w : ℂ} (hs : s ∈ S)
    (hw : HasGeneralizedWindingNumber γ s w)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (h_avoid : ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s'‖) :
    HasCauchyPVOn S (fun z => c / (z - s)) γ (2 * ↑Real.pi * I * w * c) := by
  refine hasCauchyPVOn_extend_of_avoid {s} S
    (Finset.singleton_subset_iff.mpr hs) _ γ hδ_pos ?_
    (hasCauchyPVOn_singleton_div_sub hw)
  intro s' hs' t ht
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hs'
  exact h_avoid s' hs'.1 hs'.2 t ht

/-! ## Multi-pole assembly: principal-part-sum CPV -/

/-- **Discharge of `hPV_sing` from per-pole CPV witnesses.** Given for each pole
`s ∈ S` a per-pole CPV witness (with respect to the full pole set `S`) and
per-pole integrability of the CPV integrand, the CPV of the principal-part sum
exists and equals the winding-number-weighted residue formula. -/
theorem hPV_sing_from_per_pole_cpv
    {γ : PiecewiseC1Path x x} (S : Finset ℂ) (c w : ℂ → ℂ)
    (h_per_pole : ∀ s ∈ S, HasCauchyPVOn S (fun z => c s / (z - s)) γ
      (2 * ↑Real.pi * I * w s * c s))
    (h_per_pole_int : ∀ s ∈ S, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => c s / (z - s)) γ.toPath.extend ε t)
      volume 0 1) :
    HasCauchyPVOn S (principalPartSum S c) γ
      (∑ s ∈ S, 2 * ↑Real.pi * I * w s * c s) := by
  -- Apply `HasCauchyPVOn.finset_sum` to get CPV of `fun z => ∑ s ∈ S, c s / (z - s)`,
  -- which is `principalPartSum S c` by unfolding the def.
  have h_sum := HasCauchyPVOn.finset_sum (ι_set := S) h_per_pole h_per_pole_int
  exact h_sum

/-- **Closed form of `hPV_sing` discharge — single-crossing case.** Given for each
pole `s ∈ S`:
* `hw s`: a generalized-winding-number witness at `s`;
* `h_avoid_pairs`: every pole `s' ≠ s` is avoided by γ with margin `δ > 0`;
* `h_int`: per-pole CPV-integrand integrability;

discharges the `hPV_sing` oracle. -/
theorem hPV_sing_of_winding_and_avoid_others
    {γ : PiecewiseC1Path x x} (S : Finset ℂ) (c w : ℂ → ℂ)
    (hw : ∀ s ∈ S, HasGeneralizedWindingNumber γ s (w s))
    {δ : ℝ} (hδ_pos : 0 < δ)
    (h_avoid_pairs : ∀ s ∈ S, ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s'‖)
    (h_int : ∀ s ∈ S, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => c s / (z - s)) γ.toPath.extend ε t)
      volume 0 1) :
    HasCauchyPVOn S (principalPartSum S c) γ
      (∑ s ∈ S, 2 * ↑Real.pi * I * w s * c s) :=
  hPV_sing_from_per_pole_cpv S c w
    (fun s hs => hasCauchyPVOn_div_sub_of_singleton_and_avoid_others
      S hs (hw s hs) hδ_pos (h_avoid_pairs s hs))
    h_int

/-- **Phase 5 main theorem — `hPV_sing_of_conditionB`.** Discharges the
`hPV_sing` oracle in the master template form. The signature matches the
hypothesis name `hPV_sing` in `hw_3_3_paper` (with `c = residue f`).

Hypothesis structure:
* `hw` — per-pole generalized winding number existence (the "matches def"
  form: `w = generalizedWindingNumber γ s`, the def value).
* `hδ_pos`, `h_avoid_pairs` — γ has at most one crossing per pole, with margin
  `δ > 0` separating γ from the OTHER poles.
* `h_int` — per-pole CPV-integrand integrability.

The unused hypotheses `_hU_open`, `_hS_in_U`, `_hSimple`, `_hCondB` are kept
for signature consistency with `hw_3_3_paper`. -/
theorem hPV_sing_of_conditionB
    {U : Set ℂ} (_hU_open : IsOpen U) {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ}
    (γ : ClosedPwC1Immersion x)
    (_hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (_hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (hw : ∀ s ∈ S,
      HasGeneralizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s
        (generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s))
    {δ : ℝ} (hδ_pos : 0 < δ)
    (h_avoid_pairs : ∀ s ∈ S, ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc (0 : ℝ) 1,
      δ ≤ ‖γ.toPwC1Immersion.toPiecewiseC1Path t - s'‖)
    (h_int : ∀ s ∈ S, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => residue f s / (z - s))
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S
      (principalPartSum S (fun s => residue f s))
      γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) :=
  hPV_sing_of_winding_and_avoid_others S (fun s => residue f s)
    (fun s => generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s)
    hw hδ_pos h_avoid_pairs h_int

end LeanModularForms

end
