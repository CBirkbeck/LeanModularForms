/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem.LaurentExtraction
import LeanModularForms.ForMathlib.HW33HoloCancel
import LeanModularForms.ForMathlib.HW33HigherOrderAuto
import LeanModularForms.ForMathlib.PaperPwC1Immersion
import LeanModularForms.ForMathlib.SimplePoleIntegral
import LeanModularForms.ForMathlib.SingleCrossing

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

* `hPV_sing_of_conditionB_avoids` (**Phase 5b**) — full discharge of all three
  residuals (`hw`, `h_avoid_pairs`, `h_int`) for the case when `γ` *avoids*
  every pole in `S`. The resulting signature carries only paper-faithful
  hypotheses (`hSimple`, `hCondB`, `hγ_avoids`).

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

/-! ## Phase 5b — full discharge of residuals under avoidance

For γ that **avoids every pole** in `S`, the three residual hypotheses of
`hPV_sing_of_conditionB` (`hw`, `h_avoid_pairs`, `h_int`) all discharge
automatically from the paper structure (`ClosedPwC1Immersion` + avoidance),
yielding a clean paper-faithful form.
-/

/-- **Integrability of the CPV integrand for a single simple-pole term under
avoidance.** For `γ` a `ClosedPwC1Immersion` avoiding a single pole `s ∈ S`
with positive margin `δ`, the integrand `cpvIntegrandOn S (c / (z - s)) γ ε`
is interval-integrable on `[0, 1]` for every `ε > 0`.

The proof bounds the CPV integrand pointwise by the contour integrand
`c / (γ(t) - s) · γ'(t)`, which is integrable by
`intervalIntegrable_pow_inv_mul_deriv_of_avoids` (with `k = 1`). -/
theorem cpvIntegrandOn_div_sub_intervalIntegrable_of_avoids
    (γ : ClosedPwC1Immersion x) (S : Finset ℂ) (s : ℂ) (c : ℂ) {δ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_bd : ∀ t ∈ Icc (0 : ℝ) 1,
      δ ≤ ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖)
    {K : NNReal}
    (hLip : LipschitzWith K γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
    (ε : ℝ) :
    IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => c / (z - s))
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t) volume 0 1 := by
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  -- The contour integrand of `c / (z - s)` is `c / (γ(t) - s) · γ'(t)`, which
  -- rewrites to `c * (1 / (γ(t) - s)^1 · γ'(t))`. Integrability follows from
  -- `intervalIntegrable_pow_inv_mul_deriv_of_avoids` with `k = 1`.
  have h_pow1 :=
    intervalIntegrable_pow_inv_mul_deriv_of_avoids γP s 1 hδ_pos hδ_bd hLip
  have h_const_mul : IntervalIntegrable
      (fun t => c *
        (1 / (γP.toPath.extend t - s) ^ 1 * deriv γP.toPath.extend t))
      volume 0 1 := h_pow1.const_mul c
  have h_contour_eq :
      (fun t => c *
        (1 / (γP.toPath.extend t - s) ^ 1 * deriv γP.toPath.extend t)) =
      PiecewiseC1Path.contourIntegrand (fun z => c / (z - s)) γP := by
    funext t
    simp only [PiecewiseC1Path.contourIntegrand, PiecewiseC1Path.extendedPath_eq,
      pow_one, one_div]
    ring
  rw [h_contour_eq] at h_const_mul
  exact cpvIntegrandOn_intervalIntegrable_of_contourIntegrand S _ γP ε h_const_mul

/-- **Phase 5b — full discharge of `hPV_sing` residuals under avoidance.**

For γ a paper-faithful closed piecewise-`C¹` immersion **avoiding every pole**
in `S`, the three residual hypotheses (`hw`, `h_avoid_pairs`, `h_int`) of
`hPV_sing_of_conditionB` all discharge from the paper structure alone. The
result is a clean paper-faithful `hPV_sing` discharge requiring only:

* `γ : ClosedPwC1Immersion x` — the curve structure;
* `hSimple` — simple poles at `S` (kept for signature consistency);
* `hCondB` — condition (B) (kept for signature consistency);
* `hγ_avoids` — γ avoids every pole in `S` (the paper-faithful avoidance
  hypothesis).

The three residuals discharge as follows:
* **`hw`**: by avoidance, each pole has a winding number via
  `hasGeneralizedWindingNumber_of_avoids`.
* **`h_avoid_pairs`**: trivial — `h_avoid_pairs s s' h t ht` is just
  `hδ_bd s' h.in_S t ht`, the global avoidance margin.
* **`h_int`**: integrability of `cpvIntegrandOn` for the simple-pole integrand,
  by `cpvIntegrandOn_div_sub_intervalIntegrable_of_avoids`.

The unused hypotheses `_hU_open`, `_hS_in_U`, `_hSimple`, `_hCondB` are kept
for signature consistency with `hw_3_3_paper`. -/
theorem hPV_sing_of_conditionB_avoids
    {U : Set ℂ} (_hU_open : IsOpen U) {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ}
    (γ : ClosedPwC1Immersion x)
    (_hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (_hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s) :
    HasCauchyPVOn S
      (principalPartSum S (fun s => residue f s))
      γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  -- Lipschitz of the extended path from `ClosedPwC1Immersion`.
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  -- Uniform avoidance margin `δ > 0` from finite-set avoidance.
  obtain ⟨δ, hδ_pos, hδ_bd⟩ := avoids_finset_delta_bound γP S hγ_avoids
  -- Each pole has a generalized winding number (existence via avoidance).
  have hw : ∀ s ∈ S, HasGeneralizedWindingNumber γP s
      (generalizedWindingNumber γP s) := fun s hs => by
    have h_avoid_s : ∃ δ' > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ' ≤ ‖γP t - s‖ :=
      ⟨δ, hδ_pos, fun t ht => hδ_bd s hs t ht⟩
    have hgw := hasGeneralizedWindingNumber_of_avoids h_avoid_s
    -- `hgw` gives a witness with value `(2πi)⁻¹ * ∮`, which by `.eq` agrees
    -- with `generalizedWindingNumber γP s`.
    have heq : (2 * ↑Real.pi * I)⁻¹ * γP.contourIntegral (fun z => (z - s)⁻¹) =
        generalizedWindingNumber γP s := hgw.eq.symm
    rw [← heq]; exact hgw
  -- Pairwise avoidance from the uniform margin (trivial restriction).
  have h_avoid_pairs : ∀ s ∈ S, ∀ s' ∈ S, s' ≠ s →
      ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γP t - s'‖ :=
    fun _ _ s' hs' _ t ht => hδ_bd s' hs' t ht
  -- Per-pole CPV integrand integrability via the Lipschitz + avoidance bound.
  have h_int : ∀ s ∈ S, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => residue f s / (z - s))
        γP.toPath.extend ε t) volume 0 1 := fun s hs ε _ => by
    have hδ_bd_extend : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γP.toPath.extend t - s‖ :=
      fun t ht => by
        have := hδ_bd s hs t ht
        rwa [PiecewiseC1Path.extendedPath_eq] at this
    exact cpvIntegrandOn_div_sub_intervalIntegrable_of_avoids γ S s (residue f s)
      hδ_pos hδ_bd_extend hLip ε
  exact hPV_sing_of_winding_and_avoid_others S (fun s => residue f s)
    (fun s => generalizedWindingNumber γP s) hw hδ_pos h_avoid_pairs h_int

/-! ## Phase 6.1 — `hPV_sing` from `SingleCrossingData` (per-pole crossing CPV)

When γ **crosses** a pole `s ∈ S` at a unique parameter `t₀ ∈ (0, 1)`, the
generalized winding number `HasGeneralizedWindingNumber γ s w` at the crossing is
not derivable from avoidance. Instead, it is derived from a `SingleCrossingData γ s`
witness (in `ForMathlib/SingleCrossing.lean`), which packages:

* the unique crossing parameter `t₀`;
* far/near bounds (curve is ε-far / ε-close outside / inside a δ-window);
* integrability of `(γ t - s)⁻¹ * γ'(t)` on each outer segment;
* a closed-form FTC expression `E(ε)` for the sum of the outer-segment integrals;
* a limit `E(ε) → L` as `ε → 0⁺`.

The framework lemma `SingleCrossingData.hasWindingNumber` lifts this to
`HasGeneralizedWindingNumber γ s (L / (2πi))`.

This file's contribution is the **composition with `hPV_sing_of_conditionB`**: given
per-pole `SingleCrossingData` witnesses, discharge the `hw` hypothesis automatically
and produce the full `HasCauchyPVOn` conclusion. -/

/-- **Bridge: `SingleCrossingData` to the canonical-value form.** If
`D : SingleCrossingData γ s`, the generalized winding number `w := D.L / (2πi)` is
realized as both `HasGeneralizedWindingNumber γ s w` and as
`generalizedWindingNumber γ s` (by `.eq`). This bridge produces the canonical form
needed by `hPV_sing_of_conditionB`:
`HasGeneralizedWindingNumber γ s (generalizedWindingNumber γ s)`. -/
theorem hasGeneralizedWindingNumber_canonical_of_singleCrossingData
    {γ : PiecewiseC1Path x x} {s : ℂ} (D : SingleCrossingData γ s) :
    HasGeneralizedWindingNumber γ s (generalizedWindingNumber γ s) := by
  have hD := D.hasWindingNumber
  -- `hD : HasGeneralizedWindingNumber γ s (D.L / (2πi))`
  -- `hD.eq : generalizedWindingNumber γ s = D.L / (2πi)`
  rw [hD.eq]
  exact hD

/-- **Bridge: `HasGeneralizedWindingNumber` to its canonical form.** If
`hw : HasGeneralizedWindingNumber γ s w`, then it also realizes the
`HasGeneralizedWindingNumber γ s (generalizedWindingNumber γ s)` form
needed by `hPV_sing_of_conditionB`. -/
theorem hasGeneralizedWindingNumber_canonical_of_value
    {γ : PiecewiseC1Path x x} {s w : ℂ} (hw : HasGeneralizedWindingNumber γ s w) :
    HasGeneralizedWindingNumber γ s (generalizedWindingNumber γ s) := by
  rw [hw.eq]
  exact hw

/-- **`hPV_sing` discharge via `SingleCrossingData`.** Compose the per-pole
crossing winding-number witnesses (provided as `SingleCrossingData`) with
the `hPV_sing_of_conditionB` template.

Hypotheses:
* `γ : ClosedPwC1Immersion x` — the paper-faithful curve type.
* `hSimple`, `hCondB` — kept for signature consistency.
* `Dat s hs` — `SingleCrossingData` at the crossing of γ with pole `s`. This
  encapsulates a unique transverse crossing at some `t₀ ∈ (0, 1)`, far/near
  bounds, integrability, an FTC expression, and a limit `L`. The
  generalized winding number value at `s` is then `(Dat s hs).L / (2πi)`.
* `hδ_pos`, `h_avoid_pairs`, `h_int` — pairwise avoidance and integrability.

Output: `HasCauchyPVOn` for the principal-part sum, with explicit values
matching the canonical winding-number form. -/
theorem hPV_sing_of_conditionB_singleCrossing
    {U : Set ℂ} (hU_open : IsOpen U) {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ}
    (γ : ClosedPwC1Immersion x)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (Dat : ∀ s ∈ S,
      SingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s)
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
          residue f s) := by
  have hw : ∀ s ∈ S, HasGeneralizedWindingNumber
      γ.toPwC1Immersion.toPiecewiseC1Path s
      (generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s) :=
    fun s hs => hasGeneralizedWindingNumber_canonical_of_singleCrossingData (Dat s hs)
  exact hPV_sing_of_conditionB hU_open hS_in_U γ hSimple hCondB hw hδ_pos
    h_avoid_pairs h_int

/-- **`hPV_sing` discharge via per-pole `HasGeneralizedWindingNumber` (general
hypothesis form).** Variant of `hPV_sing_of_conditionB_singleCrossing` that
accepts arbitrary `HasGeneralizedWindingNumber` witnesses at each pole
(values unrestricted — the user may supply any value, not just
`(SingleCrossingData.L) / (2πi)`). The conclusion uses the canonical
`generalizedWindingNumber γ s` value, automatically extracted via `.eq`. -/
theorem hPV_sing_of_conditionB_pointwise_winding
    {U : Set ℂ} (hU_open : IsOpen U) {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ}
    (γ : ClosedPwC1Immersion x)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (hw_val : ∀ s ∈ S, ∃ w : ℂ, HasGeneralizedWindingNumber
      γ.toPwC1Immersion.toPiecewiseC1Path s w)
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
          residue f s) := by
  classical
  have hw : ∀ s ∈ S, HasGeneralizedWindingNumber
      γ.toPwC1Immersion.toPiecewiseC1Path s
      (generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s) := by
    intro s hs
    obtain ⟨w, hwval⟩ := hw_val s hs
    exact hasGeneralizedWindingNumber_canonical_of_value hwval
  exact hPV_sing_of_conditionB hU_open hS_in_U γ hSimple hCondB hw hδ_pos
    h_avoid_pairs h_int

end LeanModularForms

end
