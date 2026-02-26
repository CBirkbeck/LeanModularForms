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

/-! ## Nonvanishing-Parameterized ℚ Variants

These accept `h_nv` (boundary nonvanishing) instead of `hint` (integrability),
forwarding to the `_of_nonvanishing` Core theorems. Integrability is derived from
nonvanishing via `intervalIntegrable_logDeriv_fdBoundary_of_nonvanishing`. -/

/-- Base identity with `h_nv` instead of `hint`, cast to ℚ. -/
theorem valence_formula_base_identity_of_nonvanishing_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 - (orderAtCusp' f : ℚ) := by
  have h_base := valence_formula_base_identity_of_nonvanishing f hf zeros hzeros hzeros_fd
    hzeros_complete h_nv hcusp_nonvan
  exact_mod_cast h_base

/-- Classical form with `h_nv` instead of `hint`, cast to ℚ. -/
theorem valence_formula_classical_form_of_nonvanishing_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
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
  have h_base := valence_formula_classical_form_of_nonvanishing f hf zeros hzeros hzeros_fd
    hzeros_complete h_nv hcusp_nonvan
  apply_fun (Rat.cast : ℚ → ℂ) using Rat.cast_injective
  push_cast [apply_ite (Rat.cast : ℚ → ℂ)]
  exact h_base

/-! ## Crossing-Cauchy ℚ Variants

These accept `h_pv_eq_residue` (the pre-composed residue-side result from M8's
`pv_equals_residue_sum_of_crossingCauchy`) instead of `h_nv` (boundary nonvanishing)
or `hint` alone. The zero data (`hzeros`, `hzeros_fd`, `hzeros_complete`) is absorbed
into `h_pv_eq_residue` at the ResidueSide level. -/

/-- Base identity via crossing-Cauchy, cast to ℚ. -/
theorem valence_formula_base_identity_of_crossingCauchy_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_pv_eq_residue : pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 - (orderAtCusp' f : ℚ) := by
  have h_base := valence_formula_base_identity_of_crossingCauchy f hf zeros hint
    hcusp_nonvan h_pv_eq_residue
  exact_mod_cast h_base

/-- Classical form via crossing-Cauchy, cast to ℚ. -/
theorem valence_formula_classical_form_of_crossingCauchy_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_pv_eq_residue : pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
  have h_base := valence_formula_classical_form_of_crossingCauchy f hf zeros hint
    hcusp_nonvan h_pv_eq_residue
  apply_fun (Rat.cast : ℚ → ℂ) using Rat.cast_injective
  push_cast [apply_ite (Rat.cast : ℚ → ℂ)]
  exact h_base

/-! ## Crossing-Cauchy-of-Integrable ℚ Variants

These accept `hint` (integrability) + `h_cc` (crossing-Cauchy condition on `S_onCurve`),
forwarding to Core's `_of_crossingCauchy_of_integrable` theorems. Nonvanishing (`h_nv`)
is derived from `hint` internally at the ResidueSide level. -/

/-- M16-T1a: Base identity via auto integrability, cast to ℚ. No `h_cc` needed. -/
theorem valence_formula_base_identity_of_crossingCauchy_auto_of_integrable_rat (hf : f ≠ 0)
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
  have h_base := valence_formula_base_identity_of_crossingCauchy_auto_of_integrable f hf zeros
    hzeros hzeros_fd hzeros_complete hint hcusp_nonvan
  exact_mod_cast h_base

/-- M16-T1b: Classical form via auto integrability, cast to ℚ. No `h_cc` needed. -/
theorem valence_formula_classical_form_of_crossingCauchy_auto_of_integrable_rat (hf : f ≠ 0)
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
  have h_base := valence_formula_classical_form_of_crossingCauchy_auto_of_integrable f hf zeros
    hzeros hzeros_fd hzeros_complete hint hcusp_nonvan
  apply_fun (Rat.cast : ℚ → ℂ) using Rat.cast_injective
  push_cast [apply_ite (Rat.cast : ℚ → ℂ)]
  exact h_base

/-- M13-T1a: Compatibility wrapper — base identity with `h_cc` (now ignored, forwards to auto). -/
theorem valence_formula_base_identity_of_crossingCauchy_of_integrable_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (_h_cc : ∀ s ∈ S_onCurve f hf zeros,
      (∃ t ∈ Icc (0:ℝ) 5, fdBoundary t = s) →
        Cauchy (Filter.map (fun ε =>
          ∫ t in (0:ℝ)..5,
            if ε < ‖fdBoundary t - s‖ then
              (fdBoundary t - s)⁻¹ * deriv fdBoundary t
            else 0)
          (𝓝[>] 0))) :
    ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 - (orderAtCusp' f : ℚ) :=
  valence_formula_base_identity_of_crossingCauchy_auto_of_integrable_rat f hf zeros
    hzeros hzeros_fd hzeros_complete hint hcusp_nonvan

/-- M13-T1b: Compatibility wrapper — classical form with `h_cc` (now ignored, forwards to auto). -/
theorem valence_formula_classical_form_of_crossingCauchy_of_integrable_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (_h_cc : ∀ s ∈ S_onCurve f hf zeros,
      (∃ t ∈ Icc (0:ℝ) 5, fdBoundary t = s) →
        Cauchy (Filter.map (fun ε =>
          ∫ t in (0:ℝ)..5,
            if ε < ‖fdBoundary t - s‖ then
              (fdBoundary t - s)⁻¹ * deriv fdBoundary t
            else 0)
          (𝓝[>] 0))) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valence_formula_classical_form_of_crossingCauchy_auto_of_integrable_rat f hf zeros
    hzeros hzeros_fd hzeros_complete hint hcusp_nonvan

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

/-! ## Auto-Cusp Generalized PV ℚ Variants

These are ℚ-cast wrappers for the generalized PV Core theorems that use
`pv_integral_logDeriv` with `fdBoundaryArcSingularSet` instead of `pv_integral`. -/

/-- Base identity via auto-cusp generalized PV, cast to ℚ. -/
theorem valence_formula_base_identity_auto_cusp_generalizedPV_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ∑ s ∈ zeros,
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) →
        ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
          (k : ℚ) / 12 - (orderAtCusp' f : ℚ) := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ :=
    valence_formula_base_identity_auto_cusp_generalizedPV f hf zeros h_arc_nv
  refine ⟨H₀, hH₀_gt, fun {H} hH h_vert_nv h_cpv => ?_⟩
  exact_mod_cast h_auto hH h_vert_nv h_cpv

/-- Rearranged base identity via auto-cusp generalized PV: `ord_∞ + Σ ew·ord = k/12`, in ℚ. -/
theorem valence_formula_rearranged_auto_cusp_generalizedPV_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ∑ s ∈ zeros,
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) →
        (orderAtCusp' f : ℚ) +
          ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
          (k : ℚ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ :=
    valence_formula_base_identity_auto_cusp_generalizedPV_rat f hf zeros h_arc_nv
  refine ⟨H₀, hH₀_gt, fun {H} hH h_vert_nv h_cpv => ?_⟩
  linarith [h_auto hH h_vert_nv h_cpv]

/-- Classical form via auto-cusp generalized PV, cast to ℚ. -/
theorem valence_formula_classical_form_auto_cusp_generalizedPV_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ∑ s ∈ zeros,
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) →
        (orderAtCusp' f : ℚ) +
          (1/2 : ℚ) * (if ellipticPoint_i' ∈ zeros
            then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
          (1/3 : ℚ) * (if ellipticPoint_rho' ∈ zeros
            then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
          ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
              (orderOfVanishingAt' f s : ℚ) =
          (k : ℚ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ :=
    valence_formula_classical_form_auto_cusp_generalizedPV f hf zeros h_arc_nv
  refine ⟨H₀, hH₀_gt, fun {H} hH h_vert_nv h_cpv => ?_⟩
  have h_base := h_auto hH h_vert_nv h_cpv
  apply_fun (Rat.cast : ℚ → ℂ) using Rat.cast_injective
  push_cast [apply_ite (Rat.cast : ℚ → ℂ)]
  exact h_base

/-! ## Auto-Cusp Generalized PV + Residue-Auto ℚ Variants

These compose the modular-side with a residue-auto provider, removing
`h_cpv_eq_residue` from the per-height API. -/

/-- Base identity with residue-auto provider, cast to ℚ. -/
theorem valence_formula_base_identity_auto_cusp_generalizedPV_of_residue_auto_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (h_residue_auto : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ∑ s ∈ zeros,
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
          (k : ℚ) / 12 - (orderAtCusp' f : ℚ) := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ :=
    valence_formula_base_identity_auto_cusp_generalizedPV_of_residue_auto f hf zeros
      h_arc_nv h_residue_auto
  refine ⟨H₀, hH₀_gt, fun {H} hH h_vert_nv => ?_⟩
  exact_mod_cast h_auto hH h_vert_nv

/-- Rearranged base identity with residue-auto provider: `ord_∞ + Σ ew·ord = k/12`, in ℚ. -/
theorem valence_formula_rearranged_auto_cusp_generalizedPV_of_residue_auto_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (h_residue_auto : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ∑ s ∈ zeros,
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        (orderAtCusp' f : ℚ) +
          ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
          (k : ℚ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ :=
    valence_formula_base_identity_auto_cusp_generalizedPV_of_residue_auto_rat f hf zeros
      h_arc_nv h_residue_auto
  refine ⟨H₀, hH₀_gt, fun {H} hH h_vert_nv => ?_⟩
  linarith [h_auto hH h_vert_nv]

/-- Classical form with residue-auto provider, cast to ℚ. -/
theorem valence_formula_classical_form_auto_cusp_generalizedPV_of_residue_auto_rat (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (h_residue_auto : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ∑ s ∈ zeros,
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        (orderAtCusp' f : ℚ) +
          (1/2 : ℚ) * (if ellipticPoint_i' ∈ zeros
            then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
          (1/3 : ℚ) * (if ellipticPoint_rho' ∈ zeros
            then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
          ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
              (orderOfVanishingAt' f s : ℚ) =
          (k : ℚ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ :=
    valence_formula_classical_form_auto_cusp_generalizedPV_of_residue_auto f hf zeros
      h_arc_nv h_residue_auto
  refine ⟨H₀, hH₀_gt, fun {H} hH h_vert_nv => ?_⟩
  have h_base := h_auto hH h_vert_nv
  apply_fun (Rat.cast : ℚ → ℂ) using Rat.cast_injective
  push_cast [apply_ite (Rat.cast : ℚ → ℂ)]
  exact h_base

end
