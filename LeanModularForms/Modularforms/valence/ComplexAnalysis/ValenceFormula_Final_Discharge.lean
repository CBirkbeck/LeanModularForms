/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Core

/-!
# Discharge Helpers for the Valence Formula Public API

This file provides helper lemmas for converting the internal (ℂ-typed, data-heavy)
valence formula theorems into the canonical public API (ℚ-typed, minimal hypotheses).

## Current Blockers (2 remaining)

The canonical public API requires discharging 2 hypotheses from `hf : f ≠ 0`:

1. `hint : IntervalIntegrable (logDeriv f' · fdBoundary * deriv fdBoundary) volume 0 5`
   **Status**: FALSE when `f` has zeros at elliptic points on `∂𝒟`.
   Fix: parameterize boundary height existentially (see `ValenceFormula_CuspHeight.lean`).

2. `hcusp_nonvan : ∀ q ∈ closedBall(0, seg5_q_radius), q ≠ 0 → cuspFunction 1 f q ≠ 0`
   **Status**: Cannot discharge with fixed `seg5_q_radius`. Fix: existential height.

## Available Lemmas

### No-`hclass` versions (synced with Session 83 Core API)
* `valence_formula_base_identity_rat` — ℚ cast of the base identity (effectiveWinding)
* `valence_formula_rearranged_rat` — rearranged: `ord_∞ + Σ ew · ord = k/12`
* `valence_formula_classical_form_rat` — ℚ cast of the unconditional classical form

### Larger-radius variants (accept `closedBall(0, r)` with `r ≥ seg5_q_radius`)
* `valence_formula_base_identity_of_larger_radius_rat` — base identity with larger radius
* `valence_formula_classical_form_of_larger_radius_rat` — classical form with larger radius

### Bridge lemmas (require `hclass` for algebraic reasons)
* `sum_effectiveWinding_eq_windingNumberCoeff` — effectiveWinding ↔ windingNumberCoeff'
* `valence_formula_windingCoeff_rat` — windingNumberCoeff' form
* `valence_formula_windingCoeff_of_larger_radius_rat` — windingNumberCoeff' with larger radius
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-! ## ℂ-to-ℚ Conversion (no `hclass`, no `h_winding`, no `h_integral_residue`) -/

/-- The base identity cast to ℚ: the ℂ equation implies the ℚ equation by injectivity
of the canonical embedding `ℚ ↪ ℂ`. -/
theorem valence_formula_base_identity_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 - (orderAtCusp' f : ℚ) := by
  have h_base := valence_formula_base_identity f hf zeros hzeros hzeros_fd
    hzeros_complete hint hcusp_nonvan
  exact_mod_cast h_base

/-- The rearranged base identity in ℚ:
  `ord_∞ + Σ ew(p) · ord_p = k/12`. -/
theorem valence_formula_rearranged_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
  have h := valence_formula_base_identity_rat f hf zeros hzeros hzeros_fd
    hzeros_complete hint hcusp_nonvan
  linarith

/-- The unconditional classical form cast to ℚ.

This does NOT require `hclass`: boundary (non-interior, non-elliptic) zeros
contribute 0 via `effectiveWinding = 0`. The sum is over `zeros.filter isInteriorPoint`.

The `if` branches handle `ellipticPoint_i'` and `ellipticPoint_rho'` membership. -/
theorem valence_formula_classical_form_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
  have h_base := valence_formula_classical_form f hf zeros hzeros hzeros_fd
    hzeros_complete hint hcusp_nonvan
  apply_fun (Rat.cast : ℚ → ℂ) using Rat.cast_injective
  push_cast [apply_ite (Rat.cast : ℚ → ℂ)]
  exact h_base

/-! ## Larger-Radius ℚ Variants

These accept nonvanishing on `closedBall(0, r)` with `r ≥ seg5_q_radius`,
forwarding to `Core.valence_formula_*_of_larger_radius`. -/

theorem valence_formula_base_identity_of_larger_radius_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 - (orderAtCusp' f : ℚ) := by
  have h_base := valence_formula_base_identity_of_larger_radius f hf zeros hzeros hzeros_fd
    hzeros_complete hint hr hcusp_nonvan
  exact_mod_cast h_base

theorem valence_formula_classical_form_of_larger_radius_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
  have h_base := valence_formula_classical_form_of_larger_radius f hf zeros hzeros hzeros_fd
    hzeros_complete hint hr hcusp_nonvan
  apply_fun (Rat.cast : ℚ → ℂ) using Rat.cast_injective
  push_cast [apply_ite (Rat.cast : ℚ → ℂ)]
  exact h_base

/-! ## effectiveWinding → windingNumberCoeff' Bridge

These lemmas require `hclass` because `effectiveWinding` and `windingNumberCoeff'`
disagree on boundary (non-interior, non-elliptic) points:
- `effectiveWinding` gives 0 for boundary points
- `windingNumberCoeff'` gives 1 for all non-elliptic points

The bridge is valid when all zeros are classified (interior/i'/ρ'). -/

/-- For classified zeros, `effectiveWinding = windingNumberCoeff'`, so the sum
using `effectiveWinding` equals the sum using `windingNumberCoeff'`. -/
theorem sum_effectiveWinding_eq_windingNumberCoeff
    (zeros : Finset ℍ)
    (hclass : ∀ s ∈ zeros,
      isInteriorPoint s ∨ s = ellipticPoint_i' ∨ s = ellipticPoint_rho') :
    ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      ∑ s ∈ zeros, windingNumberCoeff' s * (orderOfVanishingAt' f s : ℚ) := by
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  exact effectiveWinding_eq_windingCoeff_of_classified s (hclass s hs)

/-- The base identity using `windingNumberCoeff'` (ℚ-typed, rearranged).

Requires `hclass` for the effectiveWinding → windingNumberCoeff' conversion.
See `valence_formula_classical_form_rat` for a `hclass`-free alternative. -/
theorem valence_formula_windingCoeff_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hclass : ∀ s ∈ zeros,
      isInteriorPoint s ∨ s = ellipticPoint_i' ∨ s = ellipticPoint_rho')
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ s ∈ zeros, windingNumberCoeff' s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
  rw [← sum_effectiveWinding_eq_windingNumberCoeff f zeros hclass]
  exact valence_formula_rearranged_rat f hf zeros hzeros hzeros_fd
    hzeros_complete hint hcusp_nonvan

/-- The windingNumberCoeff' form with larger nonvanishing radius (ℚ-typed).

Requires `hclass` for the effectiveWinding → windingNumberCoeff' conversion.
Accepts `closedBall(0, r)` with `r ≥ seg5_q_radius`. -/
theorem valence_formula_windingCoeff_of_larger_radius_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hclass : ∀ s ∈ zeros,
      isInteriorPoint s ∨ s = ellipticPoint_i' ∨ s = ellipticPoint_rho')
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ s ∈ zeros, windingNumberCoeff' s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
  rw [← sum_effectiveWinding_eq_windingNumberCoeff f zeros hclass]
  have h := valence_formula_base_identity_of_larger_radius_rat f hf zeros hzeros hzeros_fd
    hzeros_complete hint hr hcusp_nonvan
  linarith

end
