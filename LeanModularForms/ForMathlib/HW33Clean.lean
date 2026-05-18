/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.CrossingDataConstruction
import LeanModularForms.ForMathlib.HW33LaurentSimple
import LeanModularForms.ForMathlib.HW33SimpleClean
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CPVExistence
import LeanModularForms.ForMathlib.HungerbuhlerWasem.MultiCrossingCPV
import LeanModularForms.ForMathlib.SingleCrossing

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

* `hw_3_3_clean_with_scd` — single-crossing form taking a bundled
  `SingleCrossingData γ s_star` instead of the raw `hw_star` existence
  hypothesis. The CPV-existence at the crossing follows from
  `SingleCrossingData.hasWindingNumber`.

* `hw_3_3_clean_full` — final paper-faithful form. Takes only the 8 paper
  hypotheses plus, for the distinguished pole `s_star`, either an avoidance
  proof (γ avoids `s_star`) or a `SingleCrossingData` witness. The other
  poles in `S` must be avoided by γ (`hγ_avoids_others`).
-/

noncomputable section

namespace LeanModularForms

open Set Complex
open scoped Real

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
          residue f s) :=
  hw_3_3_simple_one_crossing_paper hU_open hU_ne S hS_in_U f hf γ h_null
    hSimple hCondA hCondB
    (h_polar_cancel_of_conditionB_simple hU_open hU_ne hS_in_U γ h_null hSimple hCondB)
    (hI_polar_of_conditionB_simple hU_open hS_in_U γ h_null hSimple hCondB)
    (hI_holo_of_conditionB_simple hU_open hS_in_U hf γ h_null hSimple hCondB)
    s_star hs_star_in hγ_avoids_others hw_star

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
  obtain ⟨δ, hδ_pos, hδ_bd⟩ :=
    avoids_finset_delta_bound γ.toPwC1Immersion.toPiecewiseC1Path S hγ_avoids
  have hw_raw := hasGeneralizedWindingNumber_of_avoids
    ⟨δ, hδ_pos, hδ_bd s_star hs_star_in⟩
  exact hw_3_3_clean hU_open hU_ne S hS_in_U f hf γ h_null hSimple hCondA hCondB
    s_star hs_star_in (fun s hs _ t ht => hγ_avoids s hs t ht)
    (hw_raw.eq.symm ▸ hw_raw)

/-- **HW Theorem 3.3 — single crossing with `SingleCrossingData` witness.**

Variant of `hw_3_3_clean` taking a bundled `SingleCrossingData` for the
distinguished pole `s_star` instead of the raw `hw_star` existence hypothesis.
The CPV-existence at the crossing follows from `SingleCrossingData.hasWindingNumber`.

This is the most ergonomic interface when the geometric+analytic data at the
crossing is naturally bundled — e.g. when built via `mkSingleCrossingData_smooth`,
`mkSingleCrossingData_atI`, `mkSingleCrossingData_atRho`,
`mkSingleCrossingData_atRhoPlusOne`, or any custom constructor satisfying
`SingleCrossingData`'s contract. -/
theorem hw_3_3_clean_with_scd
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
    (D : SingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s_star) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) :=
  hw_3_3_clean hU_open hU_ne S hS_in_U f hf γ h_null hSimple hCondA hCondB
    s_star hs_star_in hγ_avoids_others (D.hasWindingNumber.eq.symm ▸ D.hasWindingNumber)

/-- **HW Theorem 3.3 — final paper-faithful form.**

The 8 paper hypotheses plus, for the distinguished pole `s_star`, EITHER
γ avoids `s_star` OR a `SingleCrossingData γ s_star` witness is given. The
other poles in `S` must be avoided by γ (`hγ_avoids_others`).

This unifies the avoidance and single-crossing scenarios under a single
disjunction. The constructor for the crossing case is the user's choice:
`mkSingleCrossingData_smooth`, the specialized FD-boundary constructors,
or any custom witness. -/
theorem hw_3_3_clean_full
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
    (h_at_star :
      (∀ t ∈ Icc (0 : ℝ) 1, γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s_star) ∨
      Nonempty
        (SingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s_star)) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  rcases h_at_star with hγ_avoid_star | ⟨D⟩
  · refine hw_3_3_clean_avoids hU_open hU_ne S hS_in_U f hf γ h_null hSimple
      hCondA hCondB (fun s hs t ht => ?_) ⟨s_star, hs_star_in⟩
    by_cases hs_eq : s = s_star
    · subst hs_eq
      exact hγ_avoid_star t ht
    · exact hγ_avoids_others s hs hs_eq t ht
  · exact hw_3_3_clean_with_scd hU_open hU_ne S hS_in_U f hf γ h_null hSimple
      hCondA hCondB s_star hs_star_in hγ_avoids_others D.some

/-- **HW Theorem 3.3 — single crossing from `CrossingGeometry`.**

A higher-level entry point taking the 8 paper hypotheses + `s_star ∈ S` +
`hγ_avoids_others` + `CrossingGeometry γ s_star` + user-supplied δ-data +
`ArcFTCHyp`, in place of a fully-assembled `SingleCrossingData`. The geometric
structure provides `t₀`/`ht₀`, the user supplies the cutoff bounds, and the
analytic FTC piece provides the limit. The `SingleCrossingData` is assembled
internally via `SingleCrossingData.ofGeometryAndFTC`. -/
theorem hw_3_3_clean_from_crossingGeometry
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
    (G : CrossingGeometry γ s_star)
    (L : ℂ) (δ : ℝ → ℝ) (threshold : ℝ) (hthresh : 0 < threshold)
    (hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε)
    (hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min G.t₀ (1 - G.t₀))
    (h_far : ∀ ε, 0 < ε → ε < threshold → ∀ t ∈ Icc (0 : ℝ) 1, δ ε < |t - G.t₀| →
      ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path t - s_star‖)
    (h_near : ∀ ε, 0 < ε → ε < threshold → ∀ t, |t - G.t₀| ≤ δ ε →
      ‖γ.toPwC1Immersion.toPiecewiseC1Path t - s_star‖ ≤ ε)
    (ftcHyp : ArcFTCHyp γ.toPwC1Immersion.toPiecewiseC1Path s_star G.t₀
      δ threshold L) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) :=
  hw_3_3_clean_with_scd hU_open hU_ne S hS_in_U f hf γ h_null hSimple hCondA
    hCondB s_star hs_star_in hγ_avoids_others
    (SingleCrossingData.ofGeometryAndFTC γ s_star G L δ threshold hthresh
      hδ_pos hδ_small h_far h_near ftcHyp)

/-- **HW Theorem 3.3 — truly paper-faithful single-crossing form.**

The **paper-faithful endpoint** of the HW 3.3 chain. Compared to
`hw_3_3_clean_full`, the disjunctive `h_at_star` residual (avoidance OR
`SingleCrossingData`) is replaced by a single structural single-crossing
witness: a unique transverse crossing parameter `t₀ ∈ Ioo 0 1` with
`IsFlatOfOrder γ t₀ 1` (flatness/transversality of order 1).

CPV-existence at the crossing is discharged via
`HungerbuhlerWasem.hasCauchyPV_inv_sub_of_flat_one_full`, which proves
the Cauchy principal value of `(z - s_star)⁻¹` exists at any transverse
simple-pole crossing.

Hypotheses: the 8 paper hypotheses, `s_star ∈ S`, `hγ_avoids_others` (γ
avoids every pole except possibly `s_star`), and the structural crossing
data `t₀ ∈ Ioo 0 1`, `h_at`, `h_unique`, `h_flat`. **No remaining oracle.** -/
theorem hw_3_3_clean_truly_full
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
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s_star)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t = s_star → t = t₀)
    (h_flat : IsFlatOfOrder
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ 1) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  obtain ⟨L, hL⟩ :=
    HungerbuhlerWasem.hasCauchyPV_inv_sub_of_flat_one_full γ ht₀ h_at h_unique h_flat
  rw [show L = 2 * ↑Real.pi * I * (L / (2 * ↑Real.pi * I)) by field_simp] at hL
  have hw_raw : HasGeneralizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path
      s_star (L / (2 * ↑Real.pi * I)) := hL
  exact hw_3_3_clean hU_open hU_ne S hS_in_U f hf γ h_null hSimple hCondA hCondB
    s_star hs_star_in hγ_avoids_others (hw_raw.eq.symm ▸ hw_raw)

/-- **HW Theorem 3.3 — paper-faithful, simple poles, multi-crossing, clean form.**

The maximally general statement of HW Theorem 3.3 for **simple poles** with
arbitrary transverse multi-pole multi-crossing. Compared to
`hw_3_3_clean_truly_full` (single distinguished crossing only), γ may cross
**any subset** of `S` at any number of parameters, provided:

* `hx_notin_S` — the basepoint is off the singular set;
* `h_no_corner_crossings` — crossings happen at smooth interior points (not at
  piecewise-`C¹` partition corners).

For a genuine `C¹` curve, `h_no_corner_crossings` is automatic (no partition
interior points to begin with). For a piecewise-`C¹` curve, it can be ensured
by choosing the partition to avoid the crossing parameters.

**Hypotheses** (8 paper + 2 structural):

* `hU_open, hU_ne, hS_in_U, hf, h_null, hSimple, hCondA, hCondB` — the 8
  paper-faithful hypotheses.
* `hx_notin_S, h_no_corner_crossings` — structural transversality/regularity.

All cancellation, integrability, CPV-existence, and multi-pole aggregation
oracles are discharged internally via the ported
`HungerbuhlerWasem.residueTheorem_crossing_full_spec` machinery. -/
theorem hw_3_3_clean_multi
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s =>
        (HungerbuhlerWasem.PolarPartDecomposition.ofMeromorphicWithCondB
          hU_open hS_in_U hf
          (γ := γ.toPwC1Immersion) (fun s hs => (hSimple s hs).meromorphicAt)
          hCondB).order s))
    (hx_notin_S : x ∉ (↑S : Set ℂ))
    (h_no_corner_crossings : ∀ s ∈ S, ∀ t₀ ∈ Set.Ioo (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s →
      t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) :=
  HungerbuhlerWasem.residueTheorem_crossing_full_spec hU_open hU_ne hS_in_U hf γ
    h_null (fun s hs => (hSimple s hs).meromorphicAt) hCondB hCondA hx_notin_S
    h_no_corner_crossings

/-- **HW Theorem 3.3 — fully general, multi-crossing, meromorphic, clean form.**

The maximally general paper-faithful HW 3.3 in the project. Compared to
`hw_3_3_clean_multi`, `f` may have **higher-order** meromorphic poles at each
point of `S` — not just simple poles.

Hypotheses (8 paper + 1 structural):

* `hU_open, hU_ne, hS_in_U, hf, h_null, hMero, hCondA, hCondB` — the 8 paper
  hypotheses, exactly matching Hungerbühler–Wasem Theorem 3.3.
* `hx_notin_S` — basepoint off `S`. The only Lean-formalization residual:
  `ClosedPwC1Immersion x` carries a typed basepoint, while the paper's "cycle"
  formulation has no basepoint. Every practical caller satisfies it.

All cancellation, integrability, CPV-existence (at crossings AND at avoided
poles), multi-pole aggregation, polar-part decomposition, higher-order Laurent
vanishing under condition (B), and corner-crossing avoidance are discharged
internally via `HungerbuhlerWasem.residueTheorem_crossing_paper_faithful_clean`.

The formal elimination of `hx_notin_S` is provided by the `cyclicShift`
infrastructure in `PaperPwC1Immersion.lean` and `PaperPwC1ImmersionInvariance.lean`
(specifically `hasCauchyPVOn_cyclicShift`, `generalizedWindingNumber_cyclicShift`,
`isNullHomologous_cyclicShift`, `satisfiesConditionA'_cyclicShift`,
`satisfiesConditionB_cyclicShift`): if `x ∈ S`, pick `τ ∈ Ioo 0 1` with
`γ(τ) ∉ S` (exists by `preimage_finite`), apply the theorem to `γ.cyclicShift τ`
whose basepoint is `γ(τ) ∉ S`, and lift back via invariance. -/
theorem hw_3_3_clean_full_mero
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s =>
        (HungerbuhlerWasem.PolarPartDecomposition.ofMeromorphicWithCondB
          hU_open hS_in_U hf
          (γ := γ.toPwC1Immersion) hMero hCondB).order s))
    (hx_notin_S : x ∉ (↑S : Set ℂ)) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) :=
  HungerbuhlerWasem.residueTheorem_crossing_paper_faithful_clean hU_open hU_ne
    hS_in_U hf γ h_null hMero hCondB hCondA hx_notin_S
