/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HW33SimpleClean
import LeanModularForms.ForMathlib.HW33LaurentSimple
import LeanModularForms.ForMathlib.SingleCrossing
import LeanModularForms.ForMathlib.CrossingDataConstruction
import LeanModularForms.ForMathlib.HungerbuhlerWasem.MultiCrossingCPV
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CPVExistence

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
          residue f s) := by
  have hw_raw := D.hasWindingNumber
  have hw_star : HasGeneralizedWindingNumber
      γ.toPwC1Immersion.toPiecewiseC1Path s_star
      (generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s_star) :=
    hw_raw.eq.symm ▸ hw_raw
  exact hw_3_3_clean hU_open hU_ne S hS_in_U f hf γ h_null hSimple hCondA
    hCondB s_star hs_star_in hγ_avoids_others hw_star

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
  · -- Full avoidance: derive `hγ_avoids` from `hγ_avoids_others` + `hγ_avoid_star`.
    have hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
        γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s := by
      intro s hs t ht
      by_cases hs_eq : s = s_star
      · subst hs_eq; exact hγ_avoid_star t ht
      · exact hγ_avoids_others s hs hs_eq t ht
    exact hw_3_3_clean_avoids hU_open hU_ne S hS_in_U f hf γ h_null hSimple
      hCondA hCondB hγ_avoids ⟨s_star, hs_star_in⟩
  · -- Single-crossing case: extract the bundled `SingleCrossingData` and apply.
    exact hw_3_3_clean_with_scd hU_open hU_ne S hS_in_U f hf γ h_null hSimple
      hCondA hCondB s_star hs_star_in hγ_avoids_others D.some

/-! ### `hw_3_3_clean_from_crossingGeometry`

A higher-level entry point that takes `CrossingGeometry` + `ArcFTCHyp` +
user-supplied δ-data instead of a fully-assembled `SingleCrossingData`. The
geometric structure provides the `t₀`/`ht₀` automatically, the user supplies
the cutoff bounds, and the analytic FTC piece provides the limit. -/

/-- **HW Theorem 3.3 — single crossing from `CrossingGeometry`.**

Takes the 8 paper hypotheses + `s_star ∈ S` + `hγ_avoids_others` +
`CrossingGeometry γ s_star` + user-supplied δ-data + `ArcFTCHyp`. The
`SingleCrossingData` is assembled automatically via
`SingleCrossingData.ofGeometryAndFTC`. -/
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

/-! ### `hw_3_3_clean_truly_full` — minimal structural hypotheses

This is the **paper-faithful endpoint** of the HW 3.3 chain. Compared to
`hw_3_3_clean_full`, the disjunctive `h_at_star` residual (avoidance OR
`SingleCrossingData`) is replaced by a single **structural single-crossing**
witness: a unique transverse crossing parameter `t₀ ∈ Ioo 0 1` with
`IsFlatOfOrder γ t₀ 1` (flatness/transversality of order 1).

The CPV-existence at the crossing is discharged automatically via
`HungerbuhlerWasem.hasCauchyPV_inv_sub_of_flat_one_full`, which proves
that the Cauchy principal value of `(z - s_star)⁻¹` exists at any
transverse simple-pole crossing.

Hypotheses (8 paper + 4 structural):

* `hU_open, hU_ne, hS_in_U, hf, h_null, hSimple, hCondA, hCondB` — paper.
* `s_star ∈ S` — distinguished crossing pole.
* `hγ_avoids_others` — γ avoids every pole except possibly `s_star`.
* `t₀ ∈ Ioo 0 1`, `h_at : γ(t₀) = s_star`, `h_unique`, `h_flat` —
  paper-faithful transverse crossing data.
-/

/-- **HW Theorem 3.3 — truly paper-faithful single-crossing form.**

Compared to `hw_3_3_clean_full`, the `h_at_star` disjunction is dropped:
instead of either avoidance or a `SingleCrossingData` witness, the user
supplies only the **structural geometric data** — a unique transverse
crossing parameter `t₀`. The CPV-existence at the crossing is proved
internally via `HungerbuhlerWasem.hasCauchyPV_inv_sub_of_flat_one_full`.

This is the paper-faithful endpoint: **8 paper hypotheses + minimal
single-crossing structural data**, with no remaining oracle. -/
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
  -- Discharge CPV existence at the crossing via the headline theorem.
  -- Note: `γ.toPwC1Immersion.toPiecewiseC1Path t = γ...toPath.extend t` definitionally
  -- via the `CoeFun` instance, so `h_at` and `h_unique` lift transparently.
  obtain ⟨L, hL⟩ :=
    HungerbuhlerWasem.hasCauchyPV_inv_sub_of_flat_one_full γ ht₀ h_at h_unique h_flat
  -- Repackage as `HasGeneralizedWindingNumber γ s_star (L / (2πi))`.
  set w : ℂ := L / (2 * ↑Real.pi * I) with hw_def
  have hpi : (2 * ↑Real.pi * I) ≠ 0 := Complex.two_pi_I_ne_zero
  have hL' : L = 2 * ↑Real.pi * I * w := by
    rw [hw_def]; field_simp
  rw [hL'] at hL
  -- `hL : HasGeneralizedWindingNumber γ s_star w`.
  have hw_star_raw : HasGeneralizedWindingNumber
      γ.toPwC1Immersion.toPiecewiseC1Path s_star w := hL
  have hw_star : HasGeneralizedWindingNumber
      γ.toPwC1Immersion.toPiecewiseC1Path s_star
      (generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s_star) :=
    hw_star_raw.eq.symm ▸ hw_star_raw
  -- Apply `hw_3_3_clean`.
  exact hw_3_3_clean hU_open hU_ne S hS_in_U f hf γ h_null hSimple hCondA hCondB
    s_star hs_star_in hγ_avoids_others hw_star

/-! ## Multi-crossing form

The fully general paper-faithful multi-crossing form: γ may cross **any
number** of poles in S, each transversely (at smooth interior partition
points). This routes through the ported
`HungerbuhlerWasem.residueTheorem_crossing_full_spec`, which handles arbitrary
multi-pole multi-crossing structure under conditions (A')+(B). -/

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
          residue f s) := by
  have hMero : ∀ s ∈ S, MeromorphicAt f s :=
    fun s hs => (hSimple s hs).meromorphicAt
  exact HungerbuhlerWasem.residueTheorem_crossing_full_spec hU_open hU_ne hS_in_U
    hf γ h_null hMero hCondB hCondA hx_notin_S h_no_corner_crossings

/-! ## Fully general meromorphic multi-crossing form (`hw_3_3_clean_full_mero`)

The maximally general statement of Hungerbühler–Wasem Theorem 3.3 in this
project: **arbitrary-order meromorphic poles + multi-crossing**. γ may cross
any subset of `S` at any number of parameters, each transversely, and the
function `f` may have meromorphic poles of any order at each point of `S`.

This is `hw_3_3_clean_multi` with `hSimple` weakened to `hMero` (i.e., the
hypotheses of `residueTheorem_crossing_full_spec` exposed at the
paper-faithful level). All paper hypotheses (8) + 2 structural residuals. -/

/-- **HW Theorem 3.3 — fully general, multi-crossing, meromorphic, clean form.**

The maximally general paper-faithful HW 3.3 in the project. Compared to
`hw_3_3_clean_multi`, `f` may have **higher-order** meromorphic poles at each
point of `S` — not just simple poles.

Hypotheses (8 paper + 1 structural):

* `hU_open, hU_ne, hS_in_U, hf, h_null, hMero, hCondA, hCondB` — the 8 paper
  hypotheses, exactly matching Hungerbühler–Wasem Theorem 3.3.
* `hx_notin_S` — basepoint off `S`. The only Lean-formalization residual:
  `ClosedPwC1Immersion x` carries a typed basepoint, while the paper's "cycle"
  formulation has no basepoint. Every practical caller satisfies this; see the
  note below for the cyclic-shift infrastructure that formally discharges it.

All cancellation, integrability, CPV-existence (at crossings AND at avoided
poles), multi-pole aggregation, polar-part decomposition, higher-order Laurent
vanishing under condition (B), and corner-crossing avoidance are discharged
internally via the ported
`HungerbuhlerWasem.residueTheorem_crossing_paper_faithful_clean`. -/
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

/-! ## Note on the basepoint residual `hx_notin_S`

`hx_notin_S` is a **Lean-formalization artifact**, not a paper hypothesis.
The paper's Theorem 3.3 uses a *cycle* (an integer combination of closed
curves) which has no typed basepoint. In Lean, `ClosedPwC1Immersion x` carries
a typed basepoint `x`, and we require `x ∉ S` to avoid the basepoint landing
on a pole.

In any practical application the basepoint is chosen off the singular set, so
this is satisfied by definition. The formal elimination of `hx_notin_S` via
cyclic-shift reparametrization is provided by the `cyclicShift` infrastructure
in `PaperPwC1Immersion.lean` and `PaperPwC1ImmersionInvariance.lean`
(specifically `hasCauchyPVOn_cyclicShift`, `generalizedWindingNumber_cyclicShift`,
`isNullHomologous_cyclicShift`, `satisfiesConditionA'_cyclicShift`,
`satisfiesConditionB_cyclicShift`): if `x ∈ S`, pick `τ ∈ Ioo 0 1` with
`γ(τ) ∉ S` (exists by `preimage_finite`), apply the theorem to `γ.cyclicShift τ`
whose basepoint is `γ(τ) ∉ S`, and lift back via invariance. -/
