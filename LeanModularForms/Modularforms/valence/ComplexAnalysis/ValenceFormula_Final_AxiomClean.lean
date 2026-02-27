/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Final_Split
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_WindingWeights
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_OnCurvePVProvider
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Interior_H
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_OrbitPairing
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_SmoothBoundaryWeights

/-!
# The Valence Formula — Axiom-Clean Public API

This file is the **axiom-clean** entrypoint for the valence formula. All theorems here
depend only on `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

Import this file (not `ValenceFormula_Final`) to get axiom-clean valence formula theorems.

The legacy `ValenceFormula_Final.lean` forwards to the monolithic `ValenceFormula.lean`
and inherits `sorryAx`. It cannot import this file due to a name collision between
`ValenceFormula.lean` and `ValenceFormulaDefinitions.lean` (both define
`orbifoldCoeff_at_i`, `fundamentalDomain`, `ellipticPoint_i'`, etc.).

## Main Theorems

### Superset forms (fixed radius)
* `valenceFormula_axiomClean_from_S` — orbifold form with `S ⊇ {zeros in 𝒟'}`
* `valenceFormula_classical_axiomClean_from_S` — classical form with explicit coefficients

### Superset forms (variable radius)
* `valenceFormula_axiomClean_from_S_of_larger_radius` — orbifold form with `r ≥ seg5_q_radius`
* `valenceFormula_classical_axiomClean_from_S_of_larger_radius` — classical form with variable radius

### Explicit-zeros forms (nonvanishing boundary, fixed radius)
* `valenceFormula_axiomClean_with_data_of_nonvanishing` — orbifold form with `h_nv` instead of `hint`
* `valenceFormula_classical_axiomClean_with_data_of_nonvanishing` — classical form with `h_nv`

### Explicit-zeros forms (nonvanishing boundary, variable radius)
* `valenceFormula_axiomClean_with_data_of_nonvanishing_of_larger_radius` — orbifold, `r ≥ seg5_q_radius`
* `valenceFormula_classical_axiomClean_with_data_of_nonvanishing_of_larger_radius` — classical, variable radius

### Explicit-zeros forms (crossing-Cauchy, fixed radius)
* `valenceFormula_axiomClean_with_data_of_crossingCauchy` — orbifold form with `h_pv_eq_residue`
* `valenceFormula_classical_axiomClean_with_data_of_crossingCauchy` — classical form with `h_pv_eq_residue`

### Explicit-zeros forms (crossing-Cauchy, variable radius)
* `valenceFormula_axiomClean_with_data_of_crossingCauchy_of_larger_radius` — orbifold, `r ≥ seg5_q_radius`
* `valenceFormula_classical_axiomClean_with_data_of_crossingCauchy_of_larger_radius` — classical, variable radius

### Explicit-zeros forms (auto integrability, no h_cc, fixed radius)
* `valenceFormula_axiomClean_with_data_of_crossingCauchy_auto_of_integrable` — orbifold, `hint` only
* `valenceFormula_classical_axiomClean_with_data_of_crossingCauchy_auto_of_integrable` — classical, `hint` only

### Explicit-zeros forms (auto integrability, no h_cc, variable radius)
* `valenceFormula_axiomClean_with_data_of_crossingCauchy_auto_of_integrable_of_larger_radius` — orbifold, `hint`, `r ≥ seg5_q_radius`
* `valenceFormula_classical_axiomClean_with_data_of_crossingCauchy_auto_of_integrable_of_larger_radius` — classical, `hint`, variable radius

### Compatibility wrappers (crossing-Cauchy + integrability, accept but ignore h_cc)
* `valenceFormula_axiomClean_with_data_of_crossingCauchy_of_integrable` — orbifold, compatibility
* `valenceFormula_classical_axiomClean_with_data_of_crossingCauchy_of_integrable` — classical, compatibility
* `valenceFormula_axiomClean_with_data_of_crossingCauchy_of_integrable_of_larger_radius` — orbifold, variable radius, compatibility
* `valenceFormula_classical_axiomClean_with_data_of_crossingCauchy_of_integrable_of_larger_radius` — classical, variable radius, compatibility

### Superset forms (nonvanishing boundary, fixed radius)
* `valenceFormula_axiomClean_from_S_of_nonvanishing` — orbifold form with `h_nv`
* `valenceFormula_classical_axiomClean_from_S_of_nonvanishing` — classical form with `h_nv`

### Superset forms (nonvanishing boundary, variable radius)
* `valenceFormula_axiomClean_from_S_of_nonvanishing_of_larger_radius` — orbifold, `h_nv`, `r ≥ seg5_q_radius`
* `valenceFormula_classical_axiomClean_from_S_of_nonvanishing_of_larger_radius` — classical, `h_nv`, variable radius

### Superset forms (crossing-Cauchy, variable radius)
* `valenceFormula_axiomClean_from_S_of_crossingCauchy_of_larger_radius` — orbifold, `h_pv_eq_residue`, `r ≥ seg5_q_radius`
* `valenceFormula_classical_axiomClean_from_S_of_crossingCauchy_of_larger_radius` — classical, `h_pv_eq_residue`, variable radius

### Superset forms (crossing-Cauchy, fixed radius)
* `valenceFormula_axiomClean_from_S_of_crossingCauchy` — orbifold, `h_pv_eq_residue`
* `valenceFormula_classical_axiomClean_from_S_of_crossingCauchy` — classical, `h_pv_eq_residue`

## References

* [Serre, *A Course in Arithmetic*], Chapter VII
* [Miyake, *Modular Forms*], Section 2.4
* [Diamond-Shurman, *A First Course in Modular Forms*], Section 3.5
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Axiom-Clean Valence Formula — Fixed Radius -/

/-- **The Valence Formula** (axiom-clean, orbifold form, fixed radius).

For a nonzero modular form `f` of weight `k` for SL₂(ℤ), and any finset `S`
of points in the fundamental domain `𝒟'` that contains all zeros of `f`:

  `ord_∞(f) + Σ_{p ∈ S} effectiveWinding(p) · ord_p(f) = k/12`

Non-zero points in `S` contribute 0 since `orderOfVanishingAt'` vanishes there. -/
theorem valenceFormula_axiomClean_from_S {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_split_from_S f hf S hS hS_complete hint hcusp_nonvan

/-- **The Classical Valence Formula** (axiom-clean, fixed radius).

  `ord_∞(f) + (1/2)·(if i ∈ S then ord_i else 0) + (1/3)·(if ρ ∈ S then ord_ρ else 0)
     + Σ_{interior p ∈ S} ord_p = k/12` -/
theorem valenceFormula_classical_axiomClean_from_S {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ S.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_classical_split_from_S f hf S hS hS_complete hint hcusp_nonvan

/-! ## Axiom-Clean Valence Formula — Variable Radius -/

/-- **The Valence Formula** (axiom-clean, orbifold form, variable cusp radius).

Most general orbifold form: accepts `S ⊇ {zeros in 𝒟'}` and
`closedBall(0, r)` with `r ≥ seg5_q_radius`. -/
theorem valenceFormula_axiomClean_from_S_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_split_from_S_of_larger_radius f hf S hS hS_complete hint hr hcusp_nonvan

/-- **The Classical Valence Formula** (axiom-clean, variable cusp radius).

Most general classical form: accepts `S ⊇ {zeros in 𝒟'}` and
`closedBall(0, r)` with `r ≥ seg5_q_radius`. -/
theorem valenceFormula_classical_axiomClean_from_S_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ S.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_classical_split_from_S_of_larger_radius f hf S hS hS_complete hint
    hr hcusp_nonvan

/-! ## Axiom-Clean Valence Formula — Explicit Zeros, Nonvanishing Boundary -/

/-- **The Valence Formula** (axiom-clean, orbifold form, explicit zeros, nonvanishing boundary).

Takes explicit zero data (`zeros/hzeros/...`) and boundary nonvanishing (`h_nv`)
instead of integrability (`hint`). -/
theorem valenceFormula_axiomClean_with_data_of_nonvanishing {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟')
    (hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
  have h := valence_formula_base_identity_of_nonvanishing_rat f hf zeros hzeros hzeros_fd
    hzeros_complete h_nv hcusp_nonvan
  linarith

/-- **The Classical Valence Formula** (axiom-clean, explicit zeros, nonvanishing boundary).

Takes explicit zero data and boundary nonvanishing (`h_nv`). -/
theorem valenceFormula_classical_axiomClean_with_data_of_nonvanishing {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟')
    (hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros)
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
      (k : ℚ) / 12 :=
  valence_formula_classical_form_of_nonvanishing_rat f hf zeros hzeros hzeros_fd
    hzeros_complete h_nv hcusp_nonvan

/-! ## Axiom-Clean Valence Formula — Explicit Zeros, Nonvanishing Boundary, Variable Radius -/

/-- **The Valence Formula** (axiom-clean, orbifold form, explicit zeros, nonvanishing boundary,
variable cusp radius).

Most general explicit-zeros orbifold form: accepts `closedBall(0, r)` with `r ≥ seg5_q_radius`. -/
theorem valenceFormula_axiomClean_with_data_of_nonvanishing_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟')
    (hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_axiomClean_with_data_of_nonvanishing f hf zeros hzeros hzeros_fd
    hzeros_complete h_nv
    (fun q hq hq0 => hcusp_nonvan q (Metric.closedBall_subset_closedBall hr hq) hq0)

/-- **The Classical Valence Formula** (axiom-clean, explicit zeros, nonvanishing boundary,
variable cusp radius).

Most general explicit-zeros classical form: accepts `closedBall(0, r)` with `r ≥ seg5_q_radius`. -/
theorem valenceFormula_classical_axiomClean_with_data_of_nonvanishing_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟')
    (hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
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
      (k : ℚ) / 12 :=
  valenceFormula_classical_axiomClean_with_data_of_nonvanishing f hf zeros hzeros hzeros_fd
    hzeros_complete h_nv
    (fun q hq hq0 => hcusp_nonvan q (Metric.closedBall_subset_closedBall hr hq) hq0)

/-! ## Axiom-Clean Valence Formula — Explicit Zeros, Crossing-Cauchy, Fixed Radius -/

/-- **The Valence Formula** (axiom-clean, orbifold form, explicit zeros, crossing-Cauchy).

Takes explicit zero data (`zeros`) and `h_pv_eq_residue` (the pre-composed
residue-side result from `pv_equals_residue_sum_of_crossingCauchy`).
Zero-data hypotheses (`hzeros`, `hzeros_fd`, `hzeros_complete`) are absorbed
into `h_pv_eq_residue` at the ResidueSide level. -/
theorem valenceFormula_axiomClean_with_data_of_crossingCauchy {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_pv_eq_residue : pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    (orderAtCusp' f : ℚ) +
      ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
  have h := valence_formula_base_identity_of_crossingCauchy_rat f hf zeros hint
    hcusp_nonvan h_pv_eq_residue
  linarith

/-- **The Classical Valence Formula** (axiom-clean, explicit zeros, crossing-Cauchy). -/
theorem valenceFormula_classical_axiomClean_with_data_of_crossingCauchy {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
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
      (k : ℚ) / 12 :=
  valence_formula_classical_form_of_crossingCauchy_rat f hf zeros hint
    hcusp_nonvan h_pv_eq_residue

/-! ## Axiom-Clean Valence Formula — Explicit Zeros, Crossing-Cauchy, Variable Radius -/

/-- **The Valence Formula** (axiom-clean, orbifold form, explicit zeros, crossing-Cauchy,
variable cusp radius).

Accepts `closedBall(0, r)` with `r ≥ seg5_q_radius`. -/
theorem valenceFormula_axiomClean_with_data_of_crossingCauchy_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_pv_eq_residue : pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    (orderAtCusp' f : ℚ) +
      ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_axiomClean_with_data_of_crossingCauchy f hf zeros hint
    (fun q hq hq0 => hcusp_nonvan q (Metric.closedBall_subset_closedBall hr hq) hq0)
    h_pv_eq_residue

/-- **The Classical Valence Formula** (axiom-clean, explicit zeros, crossing-Cauchy,
variable cusp radius).

Accepts `closedBall(0, r)` with `r ≥ seg5_q_radius`. -/
theorem valenceFormula_classical_axiomClean_with_data_of_crossingCauchy_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
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
      (k : ℚ) / 12 :=
  valenceFormula_classical_axiomClean_with_data_of_crossingCauchy f hf zeros hint
    (fun q hq hq0 => hcusp_nonvan q (Metric.closedBall_subset_closedBall hr hq) hq0)
    h_pv_eq_residue

/-! ## Axiom-Clean Valence Formula — Explicit Zeros, Auto Integrability (No h_cc) -/

/-- **The Valence Formula** (axiom-clean, orbifold form, explicit zeros, auto integrability).

Takes only `hint` and cusp nonvanishing — no `h_cc` needed. When `hint` holds, the boundary
avoids all zeros, so crossing-Cauchy is vacuously satisfied. -/
theorem valenceFormula_axiomClean_with_data_of_crossingCauchy_auto_of_integrable {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟')
    (hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
  have h := valence_formula_base_identity_of_crossingCauchy_auto_of_integrable_rat f hf zeros
    hzeros hzeros_fd hzeros_complete hint hcusp_nonvan
  linarith

/-- **The Classical Valence Formula** (axiom-clean, explicit zeros, auto integrability, no `h_cc`). -/
theorem valenceFormula_classical_axiomClean_with_data_of_crossingCauchy_auto_of_integrable {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟')
    (hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros)
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
      (k : ℚ) / 12 :=
  valence_formula_classical_form_of_crossingCauchy_auto_of_integrable_rat f hf zeros
    hzeros hzeros_fd hzeros_complete hint hcusp_nonvan

/-! ## Axiom-Clean Valence Formula — Explicit Zeros, Auto Integrability, Variable Radius -/

/-- **The Valence Formula** (axiom-clean, orbifold form, explicit zeros, auto integrability,
variable cusp radius, no `h_cc`).

Accepts `closedBall(0, r)` with `r ≥ seg5_q_radius`. -/
theorem valenceFormula_axiomClean_with_data_of_crossingCauchy_auto_of_integrable_of_larger_radius
    {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟')
    (hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_axiomClean_with_data_of_crossingCauchy_auto_of_integrable f hf zeros
    hzeros hzeros_fd hzeros_complete hint
    (fun q hq hq0 => hcusp_nonvan q (Metric.closedBall_subset_closedBall hr hq) hq0)

/-- **The Classical Valence Formula** (axiom-clean, explicit zeros, auto integrability,
variable cusp radius, no `h_cc`). -/
theorem valenceFormula_classical_axiomClean_with_data_of_crossingCauchy_auto_of_integrable_of_larger_radius
    {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟')
    (hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros)
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
      (k : ℚ) / 12 :=
  valenceFormula_classical_axiomClean_with_data_of_crossingCauchy_auto_of_integrable f hf zeros
    hzeros hzeros_fd hzeros_complete hint
    (fun q hq hq0 => hcusp_nonvan q (Metric.closedBall_subset_closedBall hr hq) hq0)

/-! ## Axiom-Clean Valence Formula — Explicit Zeros, Crossing-Cauchy-of-Integrable, Fixed Radius

Compatibility wrappers: these accept `h_cc` but ignore it, forwarding to the auto variants above. -/

/-- Compatibility wrapper — orbifold form with `h_cc` (now ignored, forwards to auto). -/
theorem valenceFormula_axiomClean_with_data_of_crossingCauchy_of_integrable {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟')
    (hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros)
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
      ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_axiomClean_with_data_of_crossingCauchy_auto_of_integrable f hf zeros
    hzeros hzeros_fd hzeros_complete hint hcusp_nonvan

/-- Compatibility wrapper — classical form with `h_cc` (now ignored, forwards to auto). -/
theorem valenceFormula_classical_axiomClean_with_data_of_crossingCauchy_of_integrable {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟')
    (hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros)
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
  valenceFormula_classical_axiomClean_with_data_of_crossingCauchy_auto_of_integrable f hf zeros
    hzeros hzeros_fd hzeros_complete hint hcusp_nonvan

/-! ## Axiom-Clean Valence Formula — Explicit Zeros, Crossing-Cauchy-of-Integrable, Variable Radius

Compatibility wrappers: these accept `h_cc` but ignore it, forwarding to the auto variants. -/

/-- Compatibility wrapper — orbifold form, variable radius, with `h_cc` (now ignored). -/
theorem valenceFormula_axiomClean_with_data_of_crossingCauchy_of_integrable_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟')
    (hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
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
      ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_axiomClean_with_data_of_crossingCauchy_auto_of_integrable_of_larger_radius f hf
    zeros hzeros hzeros_fd hzeros_complete hint hr hcusp_nonvan

/-- Compatibility wrapper — classical form, variable radius, with `h_cc` (now ignored). -/
theorem valenceFormula_classical_axiomClean_with_data_of_crossingCauchy_of_integrable_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟')
    (hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
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
  valenceFormula_classical_axiomClean_with_data_of_crossingCauchy_auto_of_integrable_of_larger_radius
    f hf zeros hzeros hzeros_fd hzeros_complete hint hr hcusp_nonvan

/-! ## Axiom-Clean Valence Formula — Superset, Nonvanishing Boundary, Fixed Radius -/

/-- **The Valence Formula** (axiom-clean, orbifold form, superset, nonvanishing boundary, fixed radius).

Takes `S ⊇ {zeros in 𝒟'}` and boundary nonvanishing (`h_nv`) instead of integrability (`hint`). -/
theorem valenceFormula_axiomClean_from_S_of_nonvanishing {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_split_from_S_of_nonvanishing f hf S hS hS_complete h_nv hcusp_nonvan

/-- **The Classical Valence Formula** (axiom-clean, superset, nonvanishing boundary, fixed radius). -/
theorem valenceFormula_classical_axiomClean_from_S_of_nonvanishing {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ S.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_classical_split_from_S_of_nonvanishing f hf S hS hS_complete h_nv hcusp_nonvan

/-! ## Axiom-Clean Valence Formula — Superset, Nonvanishing Boundary, Variable Radius -/

/-- **The Valence Formula** (axiom-clean, orbifold form, superset, nonvanishing boundary, variable radius).

Most general nonvanishing orbifold form: accepts `S ⊇ {zeros in 𝒟'}`,
`h_nv` (boundary nonvanishing), and `closedBall(0, r)` with `r ≥ seg5_q_radius`. -/
theorem valenceFormula_axiomClean_from_S_of_nonvanishing_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_split_from_S_of_nonvanishing_of_larger_radius f hf S hS hS_complete
    h_nv hr hcusp_nonvan

/-- **The Classical Valence Formula** (axiom-clean, superset, nonvanishing boundary, variable radius).

Most general nonvanishing classical form: accepts `S ⊇ {zeros in 𝒟'}`,
`h_nv` (boundary nonvanishing), and `closedBall(0, r)` with `r ≥ seg5_q_radius`. -/
theorem valenceFormula_classical_axiomClean_from_S_of_nonvanishing_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ S.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_classical_split_from_S_of_nonvanishing_of_larger_radius f hf S hS hS_complete
    h_nv hr hcusp_nonvan

/-! ## Axiom-Clean Valence Formula — Superset, Crossing-Cauchy, Variable Radius -/

/-- **The Valence Formula** (axiom-clean, orbifold form, superset, crossing-Cauchy, variable radius).

Most general crossing-Cauchy orbifold form: accepts `S ⊇ {zeros in 𝒟'}`,
`h_pv_eq_residue`, and `closedBall(0, r)` with `r ≥ seg5_q_radius`. -/
theorem valenceFormula_axiomClean_from_S_of_crossingCauchy_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_pv_eq_residue : pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ∑ s ∈ S.filter (fun p => f p = 0),
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    (orderAtCusp' f : ℚ) +
      ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_split_from_S_of_crossingCauchy_of_larger_radius f hf S hS hS_complete hint
    hr hcusp_nonvan h_pv_eq_residue

/-- **The Classical Valence Formula** (axiom-clean, superset, crossing-Cauchy, variable radius).

Most general crossing-Cauchy classical form: accepts `S ⊇ {zeros in 𝒟'}`,
`h_pv_eq_residue`, and `closedBall(0, r)` with `r ≥ seg5_q_radius`. -/
theorem valenceFormula_classical_axiomClean_from_S_of_crossingCauchy_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_pv_eq_residue : pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ∑ s ∈ S.filter (fun p => f p = 0),
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ S.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_classical_split_from_S_of_crossingCauchy_of_larger_radius f hf S hS hS_complete
    hint hr hcusp_nonvan h_pv_eq_residue

/-! ## Axiom-Clean Valence Formula — Superset, Crossing-Cauchy, Fixed Radius -/

/-- **The Valence Formula** (axiom-clean, orbifold form, superset, crossing-Cauchy, fixed radius).

Specialization of `valenceFormula_axiomClean_from_S_of_crossingCauchy_of_larger_radius`
with `r := seg5_q_radius`. -/
theorem valenceFormula_axiomClean_from_S_of_crossingCauchy {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_pv_eq_residue : pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ∑ s ∈ S.filter (fun p => f p = 0),
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    (orderAtCusp' f : ℚ) +
      ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_split_from_S_of_crossingCauchy f hf S hS hS_complete hint hcusp_nonvan
    h_pv_eq_residue

/-- **The Classical Valence Formula** (axiom-clean, superset, crossing-Cauchy, fixed radius).

Specialization of `valenceFormula_classical_axiomClean_from_S_of_crossingCauchy_of_larger_radius`
with `r := seg5_q_radius`. -/
theorem valenceFormula_classical_axiomClean_from_S_of_crossingCauchy {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_pv_eq_residue : pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ∑ s ∈ S.filter (fun p => f p = 0),
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ S.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_classical_split_from_S_of_crossingCauchy f hf S hS hS_complete hint hcusp_nonvan
    h_pv_eq_residue

/-! ## Axiom-Clean Valence Formula — Auto-Cusp (No `hcusp_nonvan`)

These variants derive cusp nonvanishing from `hf : f ≠ 0`, eliminating the
`hcusp_nonvan` parameter entirely. The result is existential: `∃ H₀ > √3/2`,
for `H ≥ H₀`, given integrability and the residue-side result at height H,
the valence formula identity holds.

The caller provides `h_pv_eq_residue` at height H (over `S.filter (f = 0)`),
but does not need to provide cusp nonvanishing — this is derived from `hf`. -/

/-- **The Valence Formula** (axiom-clean, orbifold form, superset, auto-cusp).

From `hf : f ≠ 0`, cusp nonvanishing is derived automatically for heights `H ≥ H₀`.
No `hcusp_nonvan` parameter needed. -/
theorem valenceFormula_axiomClean_from_S_auto_cusp {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
          (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5 →
        pv_integral f (fdBoundary_H H) 0 5 =
          -(2 * Real.pi * I * ∑ s ∈ S.filter (fun p => f p = 0),
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) →
        (orderAtCusp' f : ℚ) +
          ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
          (k : ℚ) / 12 :=
  valenceFormula_split_from_S_auto_cusp f hf S hS hS_complete

/-- **The Classical Valence Formula** (axiom-clean, superset, auto-cusp).

From `hf : f ≠ 0`, cusp nonvanishing is derived automatically for heights `H ≥ H₀`.
No `hcusp_nonvan` parameter needed. -/
theorem valenceFormula_classical_axiomClean_from_S_auto_cusp {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
          (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5 →
        pv_integral f (fdBoundary_H H) 0 5 =
          -(2 * Real.pi * I * ∑ s ∈ S.filter (fun p => f p = 0),
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) →
        (orderAtCusp' f : ℚ) +
          (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
            then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
          (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
            then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
          ∑ s ∈ S.filter (fun s => isInteriorPoint s),
              (orderOfVanishingAt' f s : ℚ) =
          (k : ℚ) / 12 :=
  valenceFormula_classical_split_from_S_auto_cusp f hf S hS hS_complete

/-! ## Auto-Cusp Generalized PV Public API

These use `pv_integral_logDeriv` with `fdBoundaryArcSingularSet`, replacing
`IntervalIntegrable` with local nonvanishing hypotheses. -/

/-- **The Valence Formula** (axiom-clean, orbifold form, superset, auto-cusp, generalized PV).

No `hcusp_nonvan` or `IntervalIntegrable` needed. Takes arc and vertical nonvanishing
plus the CPV residue-side equality. -/
theorem valenceFormula_axiomClean_from_S_auto_cusp_generalizedPV {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ∑ s ∈ S.filter (fun p => f p = 0),
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) →
        (orderAtCusp' f : ℚ) +
          ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
          (k : ℚ) / 12 :=
  valenceFormula_split_from_S_auto_cusp_generalizedPV f hf S hS hS_complete h_arc_nv

/-- **The Classical Valence Formula** (axiom-clean, superset, auto-cusp, generalized PV).

No `hcusp_nonvan` or `IntervalIntegrable` needed. -/
theorem valenceFormula_classical_axiomClean_from_S_auto_cusp_generalizedPV {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ∑ s ∈ S.filter (fun p => f p = 0),
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) →
        (orderAtCusp' f : ℚ) +
          (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
            then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
          (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
            then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
          ∑ s ∈ S.filter (fun s => isInteriorPoint s),
              (orderOfVanishingAt' f s : ℚ) =
          (k : ℚ) / 12 :=
  valenceFormula_classical_split_from_S_auto_cusp_generalizedPV f hf S hS hS_complete h_arc_nv

/-! ## Auto-Cusp Generalized PV + Residue-Auto Public API

These compose the modular-side with a residue-auto provider, removing
`h_cpv_eq_residue` from the per-height API entirely. -/

/-- **The Valence Formula** (axiom-clean, orbifold, superset, auto-cusp, generalizedPV, residue-auto).

No `h_cpv_eq_residue` or `IntervalIntegrable` at each height. -/
theorem valenceFormula_axiomClean_from_S_auto_cusp_generalizedPV_of_residue_auto {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (h_residue_auto : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ∑ s ∈ S.filter (fun p => f p = 0),
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        (orderAtCusp' f : ℚ) +
          ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
          (k : ℚ) / 12 :=
  valenceFormula_split_from_S_auto_cusp_generalizedPV_of_residue_auto
    f hf S hS hS_complete h_arc_nv h_residue_auto

/-- **The Classical Valence Formula** (axiom-clean, superset, auto-cusp, generalizedPV, residue-auto).

No `h_cpv_eq_residue` or `IntervalIntegrable` at each height. -/
theorem valenceFormula_classical_axiomClean_from_S_auto_cusp_generalizedPV_of_residue_auto {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (h_residue_auto : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ∑ s ∈ S.filter (fun p => f p = 0),
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        (orderAtCusp' f : ℚ) +
          (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
            then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
          (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
            then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
          ∑ s ∈ S.filter (fun s => isInteriorPoint s),
              (orderOfVanishingAt' f s : ℚ) =
          (k : ℚ) / 12 :=
  valenceFormula_classical_split_from_S_auto_cusp_generalizedPV_of_residue_auto
    f hf S hS hS_complete h_arc_nv h_residue_auto

/-! ## Generalized Winding Number Valence Formula via CPV (Axiom-Clean) -/

/-- **Generalized Winding Number Valence Formula via CPV** (axiom-clean).

Axiom-clean forwarding of `valenceFormula_split_gWN_cpv_from_S`. -/
theorem valenceFormula_axiomClean_gWN_cpv_from_S {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_oncurve_arc : ∀ t ∈ Set.Ioo (1:ℝ) 3,
        modularFormCompOfComplex f (fdBoundary_H 1 t) = 0 →
        fdBoundary_H 1 t ∈ (↑(S_arc_of_S S) : Set ℂ))
    (h_oncurve_vert : ∀ (H' : ℝ), Real.sqrt 3 / 2 < H' → ∀ t ∈ Set.Ioo (0:ℝ) 1,
        modularFormCompOfComplex f (fdBoundary_H H' t) = 0 →
        (fdBoundary_H H' t : ℂ) ∈ (↑(S_vert_of_S S) : Set ℂ))
    (h_residue_provider : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 (S_arc_of_S S ∪ S_vert_of_S S) =
          2 * ↑Real.pi * Complex.I * ∑ s ∈ S.filter (fun p => f p = 0),
            generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
              (orderOfVanishingAt' f s : ℂ)) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        ∑ s ∈ S,
          generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
            (orderOfVanishingAt' f s : ℂ) =
          -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) :=
  valenceFormula_split_gWN_cpv_from_S f hf S hS hS_complete
    h_oncurve_arc h_oncurve_vert h_residue_provider

/-- **Generalized Winding Number Valence Formula via CPV — Auto Capture** (axiom-clean).

Axiom-clean forwarding of `valenceFormula_split_gWN_cpv_from_S_auto_capture`.
No `h_oncurve_arc` or `h_oncurve_vert` needed — derived from `hS_complete`. -/
theorem valenceFormula_axiomClean_gWN_cpv_from_S_auto_capture {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_residue_provider : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 (S_arc_of_S S ∪ S_vert_of_S S) =
          2 * ↑Real.pi * Complex.I * ∑ s ∈ S.filter (fun p => f p = 0),
            generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
              (orderOfVanishingAt' f s : ℂ)) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        ∑ s ∈ S,
          generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
            (orderOfVanishingAt' f s : ℂ) =
          -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) :=
  valenceFormula_split_gWN_cpv_from_S_auto_capture f hf S hS hS_complete h_residue_provider

/-- **Generalized Winding Number Valence Formula — OnCurvePVProvider** (axiom-clean).

Axiom-clean forwarding of
`valenceFormula_split_gWN_cpv_from_S_auto_capture_of_OnCurvePVProvider`.
Takes `OnCurvePVProvider` instead of `h_residue_provider`. -/
theorem valenceFormula_axiomClean_gWN_cpv_from_S_auto_capture_of_OnCurvePVProvider {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hPV : OnCurvePVProvider f S) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        ∑ s ∈ S,
          generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
            (orderOfVanishingAt' f s : ℂ) =
          -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) :=
  valenceFormula_split_gWN_cpv_from_S_auto_capture_of_OnCurvePVProvider f hf S hS hS_complete hPV

/-! ### B2 — Explicit Coefficient Formulas

These theorems substitute the proven generalized winding number values at the three
elliptic points into the sum identity, yielding explicit fractional coefficients:
- `1/2` for the elliptic point `i`
- `1/6` for `ρ` and `ρ+1`

The remaining (non-elliptic) summands retain `generalizedWindingNumber'` in the
intermediate version. A full explicit version adds a hypothesis `h_non_elliptic`
that specifies `gWN = -1` at all non-elliptic points, eliminating all
`generalizedWindingNumber'` from the conclusion.
-/

open Classical in
/-- ρ+1 ∈ 𝒟' (|Re| = 1/2 ≤ 1/2, ‖ρ+1‖ = 1 ≥ 1). -/
private lemma ellipticPoint_rho_plus_one_mem_fd :
    ellipticPoint_rho_plus_one' ∈ 𝒟' := by
  refine ⟨?_, ?_⟩
  · show |ellipticPoint_rho_plus_one'.re| ≤ 1 / 2
    simp only [ellipticPoint_rho_plus_one', UpperHalfPlane.re]; norm_num
  · show 1 ≤ ‖(↑ellipticPoint_rho_plus_one' : ℂ)‖
    have : ‖ellipticPoint_rho_plus_one‖ = 1 := ellipticPoint_rho_plus_one_norm
    linarith

/-- Three elliptic points are pairwise distinct. -/
private lemma ellipticPoints_distinct :
    ellipticPoint_i' ≠ ellipticPoint_rho' ∧
    ellipticPoint_i' ≠ ellipticPoint_rho_plus_one' ∧
    ellipticPoint_rho' ≠ ellipticPoint_rho_plus_one' := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; have := congr_arg (fun z : UpperHalfPlane => (z : ℂ).re) h
    simp [ellipticPoint_i', ellipticPoint_rho'] at this; norm_num at this
  · intro h; have := congr_arg (fun z : UpperHalfPlane => (z : ℂ).re) h
    simp [ellipticPoint_i', ellipticPoint_rho_plus_one'] at this
  · intro h; have := congr_arg (fun z : UpperHalfPlane => (z : ℂ).re) h
    simp [ellipticPoint_rho', ellipticPoint_rho_plus_one'] at this; norm_num at this

open Classical in
/-- **Explicit Coefficient Valence Formula — Elliptic Split** (axiom-clean).

Substitutes the proven generalized winding number values
`gWN(i) = -1/2`, `gWN(ρ) = -1/6`, `gWN(ρ+1) = -1/6` into the gWN sum identity.
The result has explicit fractional coefficients `1/2`, `1/6`, `1/6` for the three
elliptic points. Non-elliptic points retain `generalizedWindingNumber'`. -/
theorem valenceFormula_explicit_coefficients_of_OnCurvePVProvider {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hPV : OnCurvePVProvider f S) :
    ∃ H₀ : ℝ, 1 < H₀ ∧ ∀ {H : ℝ}, H₀ ≤ H →
      (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_i') +
      (1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho') +
      (1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho_plus_one') +
      ∑ s ∈ S.filter (fun p =>
          p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧ p ≠ ellipticPoint_rho_plus_one'),
        (-generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ)) *
          ↑(orderOfVanishingAt' (⇑f) s) =
      (k : ℂ) / 12 := by
  -- Get the gWN identity from the OnCurvePVProvider chain
  obtain ⟨H₀, hH₀_gt, h_identity⟩ :=
    valenceFormula_axiomClean_gWN_cpv_from_S_auto_capture_of_OnCurvePVProvider
      f hf S hS hS_complete hPV
  -- Take H₁ large enough: > 1 (for gWN at i) and ≥ H₀
  refine ⟨max H₀ 2, by linarith [le_max_right H₀ 2], fun {H} hH => ?_⟩
  have hH_ge_H₀ : H₀ ≤ H := le_trans (le_max_left H₀ 2) hH
  have hH_gt_1 : 1 < H := by linarith [le_max_right H₀ 2]
  have hH_gt_sqrt3 : Real.sqrt 3 / 2 < H := by
    have h_sqrt3_lt_2 : Real.sqrt 3 < 2 := by
      nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num), sq_nonneg (Real.sqrt 3 - 2)]
    linarith
  -- Get the sum identity at this H
  have h_sum := h_identity hH_ge_H₀
  -- h_sum : ∑ s ∈ S, gWN(s) * ord(s) = -(k/12 - ord∞)
  -- Abbreviation for the sum function
  set g := fun (s : UpperHalfPlane) =>
    generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
      (orderOfVanishingAt' (⇑f) s : ℂ) with hg_def
  -- Helper: if p ∈ 𝒟' but p ∉ S, then ord_p = 0
  have h_ord_zero : ∀ p, p ∈ 𝒟' → p ∉ S → orderOfVanishingAt' (⇑f) p = 0 :=
    fun p hp hp_not => by_contra fun h_ne => hp_not (hS_complete _ hp h_ne)
  -- Distinctness of elliptic points
  obtain ⟨h_ne_iρ, h_ne_iρ1, h_ne_ρρ1⟩ := ellipticPoints_distinct
  -- Step 1: Split sum into elliptic and rest
  set P := fun (p : UpperHalfPlane) =>
    p = ellipticPoint_i' ∨ p = ellipticPoint_rho' ∨ p = ellipticPoint_rho_plus_one'
  have h_split := (Finset.sum_filter_add_sum_filter_not S P g).symm
  -- h_split : ∑_S g = ∑_{S ∩ elliptic} g + ∑_{rest} g
  -- Step 2: Show ∑_{S ∩ elliptic} g = g(i) + g(ρ) + g(ρ+1)
  -- 2a: S.filter P ⊆ {i, ρ, ρ+1}
  have h_ell_sub : S.filter P ⊆
      ({ellipticPoint_i', ellipticPoint_rho', ellipticPoint_rho_plus_one'} : Finset UpperHalfPlane) := by
    intro x hx
    have := (Finset.mem_filter.mp hx).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact this
  -- 2b: Elements of {i,ρ,ρ+1} not in S have g = 0
  have h_zero_outside : ∀ x ∈
      ({ellipticPoint_i', ellipticPoint_rho', ellipticPoint_rho_plus_one'} : Finset UpperHalfPlane),
      x ∉ S.filter P → g x = 0 := by
    intro x hx hx_not
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hx_not_S : x ∉ S := by
      intro hx_S; exact hx_not (Finset.mem_filter.mpr ⟨hx_S, hx⟩)
    have hx_fd : x ∈ 𝒟' := by
      rcases hx with rfl | rfl | rfl
      · exact ellipticPoint_i_mem_fd'
      · exact ellipticPoint_rho_mem_fd'
      · exact ellipticPoint_rho_plus_one_mem_fd
    simp [hg_def, h_ord_zero x hx_fd hx_not_S, Int.cast_zero, mul_zero]
  -- 2c: ∑_{S ∩ elliptic} g = ∑_{{i,ρ,ρ+1}} g = g(i) + g(ρ) + g(ρ+1)
  have h_ell_sum : ∑ s ∈ S.filter P, g s =
      g ellipticPoint_i' + g ellipticPoint_rho' + g ellipticPoint_rho_plus_one' := by
    rw [Finset.sum_subset h_ell_sub h_zero_outside]
    rw [Finset.sum_insert (by simp [h_ne_iρ, h_ne_iρ1]),
        Finset.sum_insert (by simp [h_ne_ρρ1]),
        Finset.sum_singleton]
    ring
  -- Step 3: Substitute gWN values at elliptic points
  have h_gWN_i := gWN_fdBoundary_H_at_i H hH_gt_1
  have h_gWN_ρ := gWN_fdBoundary_H_at_rho H hH_gt_sqrt3
  have h_gWN_ρ1 := gWN_fdBoundary_H_at_rho_plus_one H hH_gt_sqrt3
  -- Compute g at each elliptic point
  have hg_i : g ellipticPoint_i' = (-1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_i') := by
    show generalizedWindingNumber' (fdBoundary_H H) 0 5 I *
      ↑(orderOfVanishingAt' (⇑f) ellipticPoint_i') = _
    rw [h_gWN_i]
  have hg_ρ : g ellipticPoint_rho' = (-1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho') := by
    show generalizedWindingNumber' (fdBoundary_H H) 0 5 ellipticPoint_rho *
      ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho') = _
    rw [h_gWN_ρ]
  have hg_ρ1 : g ellipticPoint_rho_plus_one' =
      (-1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho_plus_one') := by
    show generalizedWindingNumber' (fdBoundary_H H) 0 5 ellipticPoint_rho_plus_one *
      ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho_plus_one') = _
    rw [h_gWN_ρ1]
  -- Step 4: Show the rest filter matches
  have h_filter_eq : S.filter (fun p => ¬P p) =
      S.filter (fun p =>
        p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧ p ≠ ellipticPoint_rho_plus_one') := by
    ext x; simp only [Finset.mem_filter, P, not_or]
  -- Step 5: Convert goal's negated sum
  set R := ∑ s ∈ S.filter (fun p => ¬P p), g s with hR_def
  have h_neg_R : ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧ p ≠ ellipticPoint_rho_plus_one'),
      (-generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ)) *
        ↑(orderOfVanishingAt' (⇑f) s) = -R := by
    rw [hR_def, h_filter_eq]
    simp only [neg_mul, Finset.sum_neg_distrib, hg_def]
  -- Step 6: Final algebra
  rw [h_neg_R]
  -- Now goal: ord∞ + (1/2)*ord_i + (1/6)*ord_ρ + (1/6)*ord_{ρ+1} - R = k/12
  -- h_sum: ∑_S g = -(k/12 - ord∞)
  rw [h_split, h_ell_sum, hg_i, hg_ρ, hg_ρ1] at h_sum
  -- h_sum: (-1/2)*ord_i + (-1/6)*ord_ρ + (-1/6)*ord_{ρ+1} + R = -(k/12 - ord∞)
  linear_combination -h_sum

open Classical in
/-- **Explicit Coefficient Valence Formula — Collapsed ρ** (axiom-clean).

Combines the `1/6` coefficients for `ρ` and `ρ+1` into a single `1/3` coefficient
for `ρ`, using T-invariance: `ord(f, ρ+1) = ord(f, ρ)`.
This is the standard form of the valence formula. -/
theorem valenceFormula_collapsed_rho_of_OnCurvePVProvider {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hPV : OnCurvePVProvider f S)
    (h_T_inv : orderOfVanishingAt' (⇑f) ellipticPoint_rho_plus_one' =
      orderOfVanishingAt' (⇑f) ellipticPoint_rho') :
    ∃ H₀ : ℝ, 1 < H₀ ∧ ∀ {H : ℝ}, H₀ ≤ H →
      (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_i') +
      (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho') +
      ∑ s ∈ S.filter (fun p =>
          p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧ p ≠ ellipticPoint_rho_plus_one'),
        (-generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ)) *
          ↑(orderOfVanishingAt' (⇑f) s) =
      (k : ℂ) / 12 := by
  obtain ⟨H₀, hH₀, h_explicit⟩ :=
    valenceFormula_explicit_coefficients_of_OnCurvePVProvider f hf S hS hS_complete hPV
  refine ⟨H₀, hH₀, fun {H} hH => ?_⟩
  have := h_explicit hH
  -- Substitute ord(ρ+1) = ord(ρ) and combine 1/6 + 1/6 = 1/3
  rw [h_T_inv] at this
  linear_combination this

open Classical in
/-- **Full Explicit Valence Formula** (axiom-clean).

Takes an additional hypothesis `h_non_elliptic` giving `gWN = -1` at all
non-elliptic points in S (i.e., interior points of 𝒟'). This eliminates all
`generalizedWindingNumber'` from the conclusion, yielding the classical form:

  `ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + Σ_{interior} ord_p(f) = k/12`
-/
theorem valenceFormula_full_explicit_of_OnCurvePVProvider {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hPV : OnCurvePVProvider f S)
    (h_T_inv : orderOfVanishingAt' (⇑f) ellipticPoint_rho_plus_one' =
      orderOfVanishingAt' (⇑f) ellipticPoint_rho')
    (h_non_elliptic : ∃ H₁ : ℝ, 1 < H₁ ∧ ∀ {H : ℝ}, H₁ ≤ H →
      ∀ s ∈ S, s ≠ ellipticPoint_i' → s ≠ ellipticPoint_rho' →
        s ≠ ellipticPoint_rho_plus_one' →
        generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) = -1) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_i') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho') +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧ p ≠ ellipticPoint_rho_plus_one'),
      ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 := by
  obtain ⟨H₀, hH₀, h_collapsed⟩ :=
    valenceFormula_collapsed_rho_of_OnCurvePVProvider f hf S hS hS_complete hPV h_T_inv
  obtain ⟨H₁, hH₁, h_ne⟩ := h_non_elliptic
  -- Take H large enough for both
  set H := max H₀ H₁ with hH_def
  have hH_ge_H₀ : H₀ ≤ H := le_max_left H₀ H₁
  have hH_ge_H₁ : H₁ ≤ H := le_max_right H₀ H₁
  have h_formula := h_collapsed hH_ge_H₀
  -- Substitute gWN = -1 for all non-elliptic points
  have h_sum_eq : ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧ p ≠ ellipticPoint_rho_plus_one'),
      (-generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ)) *
        ↑(orderOfVanishingAt' (⇑f) s) =
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧ p ≠ ellipticPoint_rho_plus_one'),
      ↑(orderOfVanishingAt' (⇑f) s) := by
    apply Finset.sum_congr rfl
    intro s hs
    simp only [Finset.mem_filter] at hs
    rw [h_ne hH_ge_H₁ s hs.1 hs.2.1 hs.2.2.1 hs.2.2.2]
    simp
  rw [h_sum_eq] at h_formula
  exact h_formula

/-! ### B5 — Auto wrappers (no OnCurvePVProvider / h_T_inv hypotheses)

These wrappers internally supply `OnCurvePVProvider f S` via
`fdBoundary_H_OnCurvePVProvider` and `h_T_inv` via `ord_rho_plus_one_eq_ord_rho`,
so callers only need `(f hf S hS hS_complete)`.
-/

/-- **gWN Valence Formula — fully automatic** (axiom-clean).

Same as `valenceFormula_axiomClean_gWN_cpv_from_S_auto_capture_of_OnCurvePVProvider`
but without the `OnCurvePVProvider` hypothesis. -/
theorem valenceFormula_axiomClean_gWN_cpv_from_S_auto_capture_auto {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        ∑ s ∈ S,
          generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
            (orderOfVanishingAt' f s : ℂ) =
          -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) :=
  valenceFormula_axiomClean_gWN_cpv_from_S_auto_capture_of_OnCurvePVProvider
    f hf S hS hS_complete (fdBoundary_H_OnCurvePVProvider f hf S)

open Classical in
/-- **Explicit Coefficient Valence Formula — fully automatic** (axiom-clean).

Same as `valenceFormula_explicit_coefficients_of_OnCurvePVProvider`
but without the `OnCurvePVProvider` hypothesis. -/
theorem valenceFormula_explicit_coefficients_auto {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∃ H₀ : ℝ, 1 < H₀ ∧ ∀ {H : ℝ}, H₀ ≤ H →
      (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_i') +
      (1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho') +
      (1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho_plus_one') +
      ∑ s ∈ S.filter (fun p =>
          p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧ p ≠ ellipticPoint_rho_plus_one'),
        (-generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ)) *
          ↑(orderOfVanishingAt' (⇑f) s) =
      (k : ℂ) / 12 :=
  valenceFormula_explicit_coefficients_of_OnCurvePVProvider
    f hf S hS hS_complete (fdBoundary_H_OnCurvePVProvider f hf S)

open Classical in
/-- **Collapsed ρ Valence Formula — fully automatic** (axiom-clean).

Same as `valenceFormula_collapsed_rho_of_OnCurvePVProvider` but without the
`OnCurvePVProvider` or `h_T_inv` hypotheses. The T-invariance
`ord(f, ρ+1) = ord(f, ρ)` is supplied via `ord_rho_plus_one_eq_ord_rho`. -/
theorem valenceFormula_collapsed_rho_auto {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∃ H₀ : ℝ, 1 < H₀ ∧ ∀ {H : ℝ}, H₀ ≤ H →
      (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_i') +
      (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho') +
      ∑ s ∈ S.filter (fun p =>
          p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧ p ≠ ellipticPoint_rho_plus_one'),
        (-generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ)) *
          ↑(orderOfVanishingAt' (⇑f) s) =
      (k : ℂ) / 12 :=
  valenceFormula_collapsed_rho_of_OnCurvePVProvider
    f hf S hS hS_complete (fdBoundary_H_OnCurvePVProvider f hf S)
    (_root_.ord_rho_plus_one_eq_ord_rho f)

open Classical in
/-- **Full Explicit Valence Formula — fully automatic** (axiom-clean).

Same as `valenceFormula_full_explicit_of_OnCurvePVProvider` but without the
`OnCurvePVProvider` or `h_T_inv` hypotheses. The only remaining hypothesis is
`h_non_elliptic`, providing `gWN = -1` at non-elliptic points for large H.

Conclusion (H-free):
  `ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + Σ_{non-ell s ∈ S} ord(s) = k/12`
-/
theorem valenceFormula_full_explicit_auto {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_non_elliptic : ∃ H₁ : ℝ, 1 < H₁ ∧ ∀ {H : ℝ}, H₁ ≤ H →
      ∀ s ∈ S, s ≠ ellipticPoint_i' → s ≠ ellipticPoint_rho' →
        s ≠ ellipticPoint_rho_plus_one' →
        generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) = -1) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_i') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho') +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧ p ≠ ellipticPoint_rho_plus_one'),
      ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 :=
  valenceFormula_full_explicit_of_OnCurvePVProvider
    f hf S hS hS_complete (fdBoundary_H_OnCurvePVProvider f hf S)
    (_root_.ord_rho_plus_one_eq_ord_rho f) h_non_elliptic

open Classical in
/-- **Full Explicit Valence Formula — strict interior, fully automatic** (axiom-clean).

Eliminates the `h_non_elliptic` hypothesis from `valenceFormula_full_explicit_auto` by
using `gWN_fdBoundary_H_eq_neg_one_of_strictInterior`: non-elliptic points that are
in the strict interior of 𝒟' (i.e., `‖p‖ > 1` and `|p.re| < 1/2`) automatically
get `gWN = -1`.

The hypothesis `h_strict` asserts that every non-elliptic point in S lies in the strict
interior. This holds for generic modular forms whose zeros avoid the boundary of 𝒟'.

Conclusion (no `generalizedWindingNumber'`, no `H`):
  `ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + Σ_{non-ell s ∈ S} ord(s) = k/12`
-/
theorem valenceFormula_full_explicit_strict_interior_auto {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_strict : ∀ s ∈ S, s ≠ ellipticPoint_i' → s ≠ ellipticPoint_rho' →
      s ≠ ellipticPoint_rho_plus_one' → ‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_i') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho') +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧ p ≠ ellipticPoint_rho_plus_one'),
      ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 := by
  -- Build h_non_elliptic from h_strict and gWN_fdBoundary_H_eq_neg_one_of_strictInterior
  have h_non_elliptic : ∃ H₁ : ℝ, 1 < H₁ ∧ ∀ {H : ℝ}, H₁ ≤ H →
      ∀ s ∈ S, s ≠ ellipticPoint_i' → s ≠ ellipticPoint_rho' →
        s ≠ ellipticPoint_rho_plus_one' →
        generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) = -1 := by
    -- Find a height bound above all points in S
    set M := S.sum (fun s : UpperHalfPlane => (s : ℂ).im) with hM_def
    refine ⟨max H_height M + 1, by linarith [H_height_gt_one, le_max_left H_height M],
      fun {H} hH s hs hsi hsρ hsρ1 => ?_⟩
    obtain ⟨hnorm, hre⟩ := h_strict s hs hsi hsρ hsρ1
    have him_pos : 0 < (s : ℂ).im := s.2
    have hH_ge : H_height ≤ H := by linarith [le_max_left H_height M]
    have him_le_M : (s : ℂ).im ≤ M :=
      Finset.single_le_sum (fun x _ => le_of_lt x.2) hs
    have him_lt : (s : ℂ).im < H := by linarith [le_max_right H_height M]
    exact gWN_fdBoundary_H_eq_neg_one_of_strictInterior _ hnorm hre him_pos hH_ge him_lt
  exact valenceFormula_full_explicit_auto f hf S hS hS_complete h_non_elliptic

/-! ## Orbit-Sum Valence Formula -/

/-- On the upper half-plane, the only point on the unit circle with real part 0 is i. -/
private lemma unit_circle_re_zero_eq_i (s : ℍ) (hs_norm : ‖(s : ℂ)‖ = 1)
    (hs_re : (s : ℂ).re = 0) : s = ellipticPoint_i' := by
  apply Subtype.ext; show (s : ℂ) = (ellipticPoint_i' : ℂ)
  have h_nsq : Complex.normSq (s : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hs_norm, one_pow]
  rw [Complex.normSq_apply, hs_re, mul_zero, zero_add] at h_nsq
  -- h_nsq : (↑s).im * (↑s).im = 1
  have h_pos : (0 : ℝ) < (s : ℂ).im := s.2
  have h_le : (s : ℂ).im ≤ 1 := by
    have := mul_self_nonneg ((s : ℂ).im - 1)
    nlinarith [h_nsq]
  have h_ge : 1 ≤ (s : ℂ).im := by
    nlinarith [mul_le_of_le_one_right h_pos.le h_le, h_nsq]
  apply Complex.ext
  · exact hs_re.trans Complex.I_re.symm
  · exact (le_antisymm h_le h_ge).trans Complex.I_im.symm

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Textbook Orbit-Sum Valence Formula** (axiom-clean, modulo boundary weight).

For a nonzero modular form `f` of weight `k` for SL₂(ℤ), the valence formula in orbit-sum form:
```
ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + Σ_{int} ord_p(f) + Σ_{leftVert} ord_p(f)
    + Σ_{leftArc} ord_p(f) = k/12
```

The interior sum runs over strictly interior points (`‖p‖ > 1`, `|re| < 1/2`).
The left-vert sum runs over left-edge points (`re = -1/2`, `‖p‖ > 1`), which represent
the T-orbit class of vertical boundary zeros.
The left-arc sum runs over left-arc points (`‖p‖ = 1`, `re < 0`), which represent
the S-orbit class of arc boundary zeros.

The `h_boundary_weight` hypothesis provides `gWN = -1/2` for all non-elliptic boundary points
(vert edges and arc). This is a single hypothesis that will be eliminated when the boundary
gWN lemmas (edge + arc) are all available. -/
theorem valenceFormula_orbit_sum {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_boundary_weight : ∃ H₁ : ℝ, 1 < H₁ ∧ ∀ {H : ℝ}, H₁ ≤ H →
      ∀ s ∈ S, s ≠ ellipticPoint_i' → s ≠ ellipticPoint_rho' →
        s ≠ ellipticPoint_rho_plus_one' →
        ¬(‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2) →
        generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) = -1/2) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_i') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho') +
    ∑ s ∈ S.filter (fun p => p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧
        p ≠ ellipticPoint_rho_plus_one' ∧ ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
      ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S_leftVert S, ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S.filter (fun p => p ≠ ellipticPoint_rho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
      ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 := by
  -- Step 1: Fix H large enough for everything
  obtain ⟨H₀, hH₀, h_base⟩ := valenceFormula_collapsed_rho_auto f hf S hS hS_complete
  obtain ⟨H₁, hH₁, h_bdry⟩ := h_boundary_weight
  set M := S.sum (fun s : UpperHalfPlane => (s : ℂ).im) with hM_def
  set H := max (max H₀ H₁) (max H_height M + 1)
  have hH0_le : H₀ ≤ H := le_trans (le_max_left _ _) (le_max_left _ _)
  have hH1_le : H₁ ≤ H := le_trans (le_max_right _ _) (le_max_left _ _)
  have hH_height : H_height ≤ H := by
    have h1 : H_height ≤ max H_height M := le_max_left H_height M
    have h2 : max H_height M + 1 ≤ H := le_max_right (max H₀ H₁) (max H_height M + 1)
    linarith
  have hH_above : ∀ s ∈ S, (s : ℂ).im < H := fun s hs => by
    have h1 : (s : ℂ).im ≤ M := Finset.single_le_sum (fun x _ => le_of_lt x.2) hs
    have h2 : M ≤ max H_height M := le_max_right H_height M
    have h3 : max H_height M + 1 ≤ H := le_max_right (max H₀ H₁) (max H_height M + 1)
    linarith
  -- Step 2: Get the base formula at H
  have h_formula := h_base hH0_le
  -- Step 3: Suffices to show NE sum equals orbit sum
  set S_NE := S.filter (fun p =>
    p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧ p ≠ ellipticPoint_rho_plus_one')
    with hS_NE_def
  set INT := S.filter (fun p => p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧
    p ≠ ellipticPoint_rho_plus_one' ∧ ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2)
  suffices h_eq :
      ∑ s ∈ S_NE, (-generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ)) *
          ↑(orderOfVanishingAt' (⇑f) s) =
      ∑ s ∈ INT, ↑(orderOfVanishingAt' (⇑f) s) +
      ∑ s ∈ S_leftVert S, ↑(orderOfVanishingAt' (⇑f) s) +
      ∑ s ∈ S.filter (fun p => p ≠ ellipticPoint_rho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
        ↑(orderOfVanishingAt' (⇑f) s) by
    have h := h_formula; rw [h_eq] at h; linear_combination h
  -- Step 4: For each s in S_NE, (-gWN) is 1 (interior) or 1/2 (boundary)
  have h_gWN_val : ∀ s ∈ S_NE,
      (-generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ)) *
        ↑(orderOfVanishingAt' (⇑f) s) =
      (if ‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2 then (1 : ℂ) else 1/2) *
        ↑(orderOfVanishingAt' (⇑f) s) := by
    intro s hs
    simp only [hS_NE_def, Finset.mem_filter] at hs
    obtain ⟨hs_S, hsi, hsρ, hsρ1⟩ := hs
    split_ifs with h_int
    · -- Interior: -gWN = 1
      obtain ⟨hnorm, hre⟩ := h_int
      have him_pos : 0 < (s : ℂ).im := s.2
      have him_lt := hH_above s hs_S
      rw [gWN_fdBoundary_H_eq_neg_one_of_strictInterior _ hnorm hre him_pos hH_height him_lt]
      ring
    · -- Boundary: -gWN = 1/2
      rw [h_bdry hH1_le s hs_S hsi hsρ hsρ1 h_int]; ring
  rw [Finset.sum_congr rfl h_gWN_val]
  -- Step 5: Reduce to boundary identity
  set LA_ne := S.filter (fun p => p ≠ ellipticPoint_rho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)
    with hLA_ne_def
  set RA_ne := S.filter (fun p => p ≠ ellipticPoint_rho_plus_one' ∧ ‖(p : ℂ)‖ = 1 ∧
    (p : ℂ).re > 0) with hRA_ne_def
  set BDRY := S_NE.filter (fun (p : ℍ) => ¬(‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2))
    with hBDRY_def
  -- S_NE.filter(interior) = INT
  have h_ne_int : S_NE.filter (fun (p : ℍ) =>
      ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2) = INT := by
    ext s; simp only [hS_NE_def, INT, Finset.mem_filter]; tauto
  -- Split S_NE sum and simplify coefficients → reduce to boundary identity
  suffices h_bdry_identity :
      (1/2 : ℂ) * ∑ s ∈ BDRY, (orderOfVanishingAt' (⇑f) s : ℂ) =
      ∑ s ∈ S_leftVert S, (orderOfVanishingAt' (⇑f) s : ℂ) +
      ∑ s ∈ LA_ne, (orderOfVanishingAt' (⇑f) s : ℂ) by
    -- Split S_NE into INT + BDRY, simplify if-then-else coefficients
    have h_split := Finset.sum_filter_add_sum_filter_not S_NE
      (fun (p : ℍ) => ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2)
      (fun s => (if ‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2 then (1:ℂ) else 1/2) *
        ↑(orderOfVanishingAt' (⇑f) s))
    have h_int_sum : ∑ x ∈ S_NE.filter (fun (p : ℍ) =>
          ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
        (if ‖(x : ℂ)‖ > 1 ∧ |(x : ℂ).re| < 1/2 then (1:ℂ) else 1/2) *
          ↑(orderOfVanishingAt' (⇑f) x) =
        ∑ x ∈ INT, ↑(orderOfVanishingAt' (⇑f) x) := by
      rw [h_ne_int]; apply Finset.sum_congr rfl; intro s hs
      simp only [INT, Finset.mem_filter] at hs
      rw [if_pos ⟨hs.2.2.2.2.1, hs.2.2.2.2.2⟩, one_mul]
    have h_bdry_sum : ∑ x ∈ BDRY,
        (if ‖(x : ℂ)‖ > 1 ∧ |(x : ℂ).re| < 1/2 then (1:ℂ) else 1/2) *
          ↑(orderOfVanishingAt' (⇑f) x) =
        (1/2 : ℂ) * ∑ x ∈ BDRY, (orderOfVanishingAt' (⇑f) x : ℂ) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s hs
      rw [if_neg (show ¬(‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2) from
        (Finset.mem_filter.mp hs).2)]
    linear_combination h_int_sum + h_bdry_sum + h_bdry_identity - h_split
  -- Step 6: Prove (1/2) * Σ_BDRY = Σ_LV + Σ_LA_ne
  -- Strategy: BDRY = LV ∪ RV ∪ LA_ne ∪ RA_ne, pairing gives RV=LV and RA_ne=LA_ne
  -- Helper: ‖ρ‖ = 1
  have h_rho_norm : ‖(ellipticPoint_rho' : ℂ)‖ = 1 := by
    have h_normSq : Complex.normSq (ellipticPoint_rho' : ℂ) = 1 := by
      show Complex.normSq (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
      have h1 : (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) =
          ((-1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
      rw [h1, Complex.normSq_add_mul_I]
      have h2 : (-1/2 : ℝ)^2 = 1/4 := by ring
      have h3 : (Real.sqrt 3 / 2)^2 = 3/4 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
      rw [h2, h3]; ring
    show Real.sqrt (Complex.normSq _) = 1; rw [h_normSq, Real.sqrt_one]
  -- Helper: re(ρ) < 0
  have h_rho_re_neg : (ellipticPoint_rho' : ℂ).re < 0 := by
    show (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).re < 0
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one]
    norm_num
  -- Helper: ‖ρ+1‖ = 1
  have h_rho1_norm : ‖(ellipticPoint_rho_plus_one' : ℂ)‖ = 1 := by
    have : (ellipticPoint_rho_plus_one' : ℂ) = ellipticPoint_rho_plus_one := rfl
    rw [this]; exact ellipticPoint_rho_plus_one_norm
  -- Helper: re(ρ+1) > 0
  have h_rho1_re_pos : (ellipticPoint_rho_plus_one' : ℂ).re > 0 := by
    show (1/2 + (Real.sqrt 3 / 2) * I : ℂ).re > 0
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one]
    norm_num
  -- Vertical pairing: Σ_RV = Σ_LV
  have h_vert := sum_ord_rightVert_eq_sum_ord_leftVert f S hS hS_complete
  -- Full arc pairing: Σ_rightArc = Σ_leftArc
  have h_arc := sum_ord_rightArc_eq_sum_ord_leftArc f S hS hS_complete
  -- NE arc pairing: Σ_RA_ne = Σ_LA_ne (derived from full pairing + ord(ρ+1)=ord(ρ))
  have h_ne_arc : ∑ p ∈ RA_ne, (orderOfVanishingAt' (⇑f) p : ℂ) =
      ∑ p ∈ LA_ne, (orderOfVanishingAt' (⇑f) p : ℂ) := by
    -- Relate RA_ne/LA_ne to S_rightArc/S_leftArc minus elliptic singletons
    have h_ra_ne : RA_ne = (S_rightArc S).filter (· ≠ ellipticPoint_rho_plus_one') := by
      ext s; simp only [hRA_ne_def, S_rightArc, Finset.mem_filter]; tauto
    have h_la_ne : LA_ne = (S_leftArc S).filter (· ≠ ellipticPoint_rho') := by
      ext s; simp only [hLA_ne_def, S_leftArc, Finset.mem_filter]; tauto
    rw [h_ra_ne, h_la_ne]
    set f_ord := fun s : ℍ => (orderOfVanishingAt' (⇑f) s : ℂ) with hf_ord_def
    -- Split each arc sum: (filter ≠ ell) + (filter = ell) = full
    have h_ra_split := Finset.sum_filter_add_sum_filter_not (S_rightArc S)
      (· ≠ ellipticPoint_rho_plus_one') f_ord
    have h_la_split := Finset.sum_filter_add_sum_filter_not (S_leftArc S)
      (· ≠ ellipticPoint_rho') f_ord
    -- Suffices: singleton sums are equal
    suffices h_sing :
        ∑ p ∈ (S_rightArc S).filter (fun x => ¬(x ≠ ellipticPoint_rho_plus_one')), f_ord p =
        ∑ p ∈ (S_leftArc S).filter (fun x => ¬(x ≠ ellipticPoint_rho')), f_ord p by
      linear_combination h_arc + h_ra_split - h_la_split - h_sing
    simp_rw [not_not]
    conv_lhs => rw [Finset.filter_eq' (S_rightArc S) ellipticPoint_rho_plus_one']
    conv_rhs => rw [Finset.filter_eq' (S_leftArc S) ellipticPoint_rho']
    by_cases h_ord : orderOfVanishingAt' (⇑f) ellipticPoint_rho' = 0
    · -- ord(ρ) = 0, so both singleton contributions are 0
      have h_ord' : orderOfVanishingAt' (⇑f) ellipticPoint_rho_plus_one' = 0 :=
        ord_rho_plus_one_eq_ord_rho_via_vAdd f ▸ h_ord
      have hf1 : f_ord ellipticPoint_rho' = 0 := by
        simp [hf_ord_def, h_ord]
      have hf2 : f_ord ellipticPoint_rho_plus_one' = 0 := by
        simp [hf_ord_def, h_ord']
      split_ifs <;> simp [Finset.sum_singleton, Finset.sum_empty, hf1, hf2]
    · -- ord(ρ) ≠ 0: both ρ ∈ S and ρ+1 ∈ S, hence in their arcs
      have hρ_in_S := hS_complete _ ellipticPoint_rho_mem_fd' h_ord
      have hρ1_in_S := hS_complete _ ellipticPoint_rho_plus_one_mem_fd'
        (by rwa [ord_rho_plus_one_eq_ord_rho_via_vAdd])
      have hρ_in_LA : ellipticPoint_rho' ∈ S_leftArc S := by
        simp only [S_leftArc, Finset.mem_filter]
        exact ⟨hρ_in_S, h_rho_norm, h_rho_re_neg⟩
      have hρ1_in_RA : ellipticPoint_rho_plus_one' ∈ S_rightArc S := by
        simp only [S_rightArc, Finset.mem_filter]
        exact ⟨hρ1_in_S, h_rho1_norm, h_rho1_re_pos⟩
      rw [if_pos hρ1_in_RA, if_pos hρ_in_LA, Finset.sum_singleton, Finset.sum_singleton]
      simp only [hf_ord_def]
      exact_mod_cast congr_arg (Int.cast (R := ℂ)) (ord_rho_plus_one_eq_ord_rho_via_vAdd f)
  -- BDRY decomposition: BDRY = S_rightVert S ∪ S_leftVert S ∪ RA_ne ∪ LA_ne
  have h_bdry_decomp : BDRY =
      (S_rightVert S) ∪ (S_leftVert S) ∪ RA_ne ∪ LA_ne := by
    ext s; simp only [hBDRY_def, hS_NE_def, hRA_ne_def, hLA_ne_def,
      S_rightVert, S_leftVert, Finset.mem_union, Finset.mem_filter]
    constructor
    · -- s ∈ BDRY → s ∈ one of the 4 parts
      intro ⟨⟨hs_S, hsi, hsρ, hsρ1⟩, h_not_int⟩
      have hs_fd := hS s hs_S
      obtain ⟨habs_re, hnorm_ge⟩ := hs_fd
      -- Case split: ‖s‖ > 1 or ‖s‖ = 1
      rcases eq_or_lt_of_le hnorm_ge with h_eq | h_gt
      · -- ‖s‖ = 1: on the unit circle
        rcases lt_trichotomy (s : ℂ).re 0 with hre_neg | hre_zero | hre_pos
        · right; exact ⟨hs_S, hsρ, h_eq.symm, hre_neg⟩
        · exact absurd (unit_circle_re_zero_eq_i s h_eq.symm hre_zero) hsi
        · left; right; exact ⟨hs_S, hsρ1, h_eq.symm, hre_pos⟩
      · -- ‖s‖ > 1: on vert edge (|re| = 1/2 since ¬interior)
        have h_abs_eq : |(s : ℂ).re| = 1/2 := by
          by_contra h_ne
          exact h_not_int ⟨h_gt, lt_of_le_of_ne habs_re h_ne⟩
        rcases abs_cases (s : ℂ).re with ⟨_, h_sign⟩ | ⟨_, h_sign⟩
        · left; left; left; exact ⟨hs_S, by linarith, h_gt⟩
        · left; left; right; exact ⟨hs_S, by linarith, h_gt⟩
    · -- s ∈ one of 4 → s ∈ BDRY (h is already Or/And from simp)
      intro h
      rcases h with ((⟨hs, hre, hn⟩ | ⟨hs, hre, hn⟩) | ⟨hs, hne, hn_eq, hre⟩) |
          ⟨hs, hne, hn_eq, hre⟩
      · -- rightVert (re = 1/2)
        refine ⟨⟨hs, ?_, ?_, ?_⟩, fun ⟨_, h⟩ => by have := (abs_lt.mp h).2; linarith⟩
        · intro h; rw [h] at hre; norm_num [ellipticPoint_i'] at hre
        · intro h; rw [h] at hn; linarith [h_rho_norm]
        · intro h; rw [h] at hn; linarith [h_rho1_norm]
      · -- leftVert (re = -1/2)
        refine ⟨⟨hs, ?_, ?_, ?_⟩, fun ⟨_, h⟩ => by have := (abs_lt.mp h).1; linarith⟩
        · intro h; rw [h] at hre; norm_num [ellipticPoint_i'] at hre
        · intro h; rw [h] at hn; linarith [h_rho_norm]
        · intro h; rw [h] at hn; linarith [h_rho1_norm]
      · -- RA_ne
        refine ⟨⟨hs, ?_, ?_, hne⟩, fun ⟨h, _⟩ => by linarith⟩
        · intro h; rw [h] at hre; simp [ellipticPoint_i'] at hre
        · intro h; rw [h] at hre; linarith [h_rho_re_neg]
      · -- LA_ne
        refine ⟨⟨hs, ?_, hne, ?_⟩, fun ⟨h, _⟩ => by linarith⟩
        · intro h; rw [h] at hre; simp [ellipticPoint_i'] at hre
        · intro h; rw [h] at hre; linarith [h_rho1_re_pos]
  -- Pairwise disjointness of the 4 parts
  have h_disj_RV_LV : Disjoint (S_rightVert S) (S_leftVert S) :=
    Finset.disjoint_filter.mpr fun s _ ⟨hre1, _⟩ ⟨hre2, _⟩ => by linarith
  have h_disj_RV_RA : Disjoint (S_rightVert S) RA_ne :=
    Finset.disjoint_filter.mpr fun s _ ⟨_, hn⟩ ⟨_, hn_eq, _⟩ => by linarith
  have h_disj_RV_LA : Disjoint (S_rightVert S) LA_ne :=
    Finset.disjoint_filter.mpr fun s _ ⟨hre, _⟩ ⟨_, _, hre2⟩ => by linarith
  have h_disj_LV_RA : Disjoint (S_leftVert S) RA_ne :=
    Finset.disjoint_filter.mpr fun s _ ⟨hre, _⟩ ⟨_, _, hre2⟩ => by linarith
  have h_disj_LV_LA : Disjoint (S_leftVert S) LA_ne :=
    Finset.disjoint_filter.mpr fun s _ ⟨_, hn⟩ ⟨_, hn_eq, _⟩ => by linarith
  have h_disj_RA_LA : Disjoint RA_ne LA_ne :=
    Finset.disjoint_filter.mpr fun s _ ⟨_, _, hre1⟩ ⟨_, _, hre2⟩ => by linarith
  -- Sum decomposition
  have h_sum_decomp : ∑ s ∈ BDRY, (orderOfVanishingAt' (⇑f) s : ℂ) =
      ∑ s ∈ S_rightVert S, (orderOfVanishingAt' (⇑f) s : ℂ) +
      ∑ s ∈ S_leftVert S, (orderOfVanishingAt' (⇑f) s : ℂ) +
      ∑ s ∈ RA_ne, (orderOfVanishingAt' (⇑f) s : ℂ) +
      ∑ s ∈ LA_ne, (orderOfVanishingAt' (⇑f) s : ℂ) := by
    rw [h_bdry_decomp]
    have h12 : Disjoint (S_rightVert S ∪ S_leftVert S) RA_ne :=
      Finset.disjoint_union_left.mpr ⟨h_disj_RV_RA, h_disj_LV_RA⟩
    have h123 : Disjoint (S_rightVert S ∪ S_leftVert S ∪ RA_ne) LA_ne :=
      Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr ⟨h_disj_RV_LA, h_disj_LV_LA⟩, h_disj_RA_LA⟩
    rw [Finset.sum_union h123, Finset.sum_union h12, Finset.sum_union h_disj_RV_LV]
  -- Combine: (1/2) * (Σ_RV + Σ_LV + Σ_RA_ne + Σ_LA_ne) = Σ_LV + Σ_LA_ne
  rw [h_sum_decomp, h_vert, h_ne_arc]; ring

/-! ## Boundary Weight Automation -/

/-- On the upper half-plane, the only point on the unit circle with re = -1/2 is ρ. -/
private lemma unit_circle_re_neg_half_eq_rho (s : ℍ) (hs_norm : ‖(s : ℂ)‖ = 1)
    (hs_re : (s : ℂ).re = -1/2) : s = ellipticPoint_rho' := by
  apply Subtype.ext
  show (s : ℂ) = (ellipticPoint_rho' : ℂ)
  have h_nsq : Complex.normSq (s : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hs_norm, one_pow]
  rw [Complex.normSq_apply, hs_re] at h_nsq
  have h_im : (s : ℂ).im = Real.sqrt 3 / 2 := by
    have h_im_sq : (s : ℂ).im * (s : ℂ).im = 3/4 := by nlinarith
    have h3 := Real.mul_self_sqrt (show (3:ℝ) ≥ 0 by norm_num)
    have h_prod : ((s : ℂ).im - Real.sqrt 3 / 2) * ((s : ℂ).im + Real.sqrt 3 / 2) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp h_prod with h | h
    · linarith
    · exact absurd h (ne_of_gt (add_pos s.2 (by positivity)))
  have h_rho_re : (ellipticPoint_rho' : ℂ).re = -1/2 := by
    show (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = -1/2
    simp only [add_re, mul_re, I_re, I_im, mul_zero, mul_one]; norm_num
  have h_rho_im : (ellipticPoint_rho' : ℂ).im = Real.sqrt 3 / 2 := by
    show (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).im = Real.sqrt 3 / 2
    simp only [add_im, mul_im, I_re, I_im, mul_one, neg_im, one_im, div_ofNat_im,
      ofReal_im, mul_zero, add_zero, neg_zero, zero_div, ofReal_re, div_ofNat_re, zero_add]
  apply Complex.ext
  · exact hs_re.trans h_rho_re.symm
  · exact h_im.trans h_rho_im.symm

/-- On the upper half-plane, the only point on the unit circle with re = 1/2 is ρ + 1. -/
private lemma unit_circle_re_pos_half_eq_rho_plus_one (s : ℍ) (hs_norm : ‖(s : ℂ)‖ = 1)
    (hs_re : (s : ℂ).re = 1/2) : s = ellipticPoint_rho_plus_one' := by
  apply Subtype.ext
  show (s : ℂ) = (ellipticPoint_rho_plus_one' : ℂ)
  have h_nsq : Complex.normSq (s : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hs_norm, one_pow]
  rw [Complex.normSq_apply, hs_re] at h_nsq
  have h_im : (s : ℂ).im = Real.sqrt 3 / 2 := by
    have h_im_sq : (s : ℂ).im * (s : ℂ).im = 3/4 := by nlinarith
    have h3 := Real.mul_self_sqrt (show (3:ℝ) ≥ 0 by norm_num)
    have h_prod : ((s : ℂ).im - Real.sqrt 3 / 2) * ((s : ℂ).im + Real.sqrt 3 / 2) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp h_prod with h | h
    · linarith
    · exact absurd h (ne_of_gt (add_pos s.2 (by positivity)))
  have h_rho1_re : (ellipticPoint_rho_plus_one' : ℂ).re = 1/2 := by
    show (1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = 1/2
    simp only [add_re, mul_re, I_re, I_im, mul_zero, mul_one]; norm_num
  have h_rho1_im : (ellipticPoint_rho_plus_one' : ℂ).im = Real.sqrt 3 / 2 := by
    show (1/2 + (Real.sqrt 3 / 2) * I : ℂ).im = Real.sqrt 3 / 2
    simp only [add_im, mul_im, I_re, I_im, mul_one, one_im, div_ofNat_im,
      ofReal_im, mul_zero, add_zero, zero_div, ofReal_re, div_ofNat_re, zero_add]
  apply Complex.ext
  · exact hs_re.trans h_rho1_re.symm
  · exact h_im.trans h_rho1_im.symm

/-- On a vert edge (|re| = 1/2, ‖s‖ > 1), the imaginary part exceeds √3/2. -/
private lemma vert_edge_im_gt_sqrt3_half (s : ℍ)
    (hs_norm : ‖(s : ℂ)‖ > 1) (hs_abs_re : |(s : ℂ).re| = 1/2) :
    Real.sqrt 3 / 2 < (s : ℂ).im := by
  by_contra h_le
  push_neg at h_le
  have h3 := Real.mul_self_sqrt (show (3:ℝ) ≥ 0 by norm_num)
  have h_nsq_gt : Complex.normSq (s : ℂ) > 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [hs_norm, sq_nonneg (‖(s : ℂ)‖ - 1)]
  have h_nsq_eq : Complex.normSq (s : ℂ) =
      (s : ℂ).re * (s : ℂ).re + (s : ℂ).im * (s : ℂ).im := Complex.normSq_apply _
  have h_re_sq : (s : ℂ).re * (s : ℂ).re ≤ 1/4 := by
    rcases (abs_eq (by norm_num : (1:ℝ)/2 ≥ 0)).mp hs_abs_re with h | h <;> rw [h] <;> norm_num
  have h_im_sq : (s : ℂ).im * (s : ℂ).im ≤ 3/4 := by
    have h_bound : Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 3/4 := by nlinarith
    have h1 : (s : ℂ).im * (s : ℂ).im ≤ Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) :=
      mul_self_le_mul_self s.2.le h_le
    linarith
  linarith

set_option maxHeartbeats 400000 in
/-- Constructs the boundary weight hypothesis from `hS : ∀ p ∈ S, p ∈ 𝒟'`.
For every non-elliptic, non-interior point of S, the generalized winding number
equals -1/2, using the right-edge, left-edge, and unit-arc weight lemmas. -/
private lemma boundary_weight_auto
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟') :
    ∃ H₁ : ℝ, 1 < H₁ ∧ ∀ {H : ℝ}, H₁ ≤ H →
      ∀ s ∈ S, s ≠ ellipticPoint_i' → s ≠ ellipticPoint_rho' →
        s ≠ ellipticPoint_rho_plus_one' →
        ¬(‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2) →
        generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) = -1/2 := by
  set M := S.sum (fun s : UpperHalfPlane => (s : ℂ).im) with hM_def
  refine ⟨max 2 (M + 1), by linarith [le_max_left (2 : ℝ) (M + 1)], ?_⟩
  intro H hH s hs hsi hsρ hsρ1 h_not_int
  have hs_fd := hS s hs
  have habs_re := hs_fd.1
  have hnorm_ge := hs_fd.2
  have h_im_pos : 0 < (s : ℂ).im := s.2
  have hH_ge2 : (2 : ℝ) ≤ H := le_trans (le_max_left 2 (M + 1)) hH
  have h_im_lt_H : (s : ℂ).im < H := by
    have h1 : (s : ℂ).im ≤ M := Finset.single_le_sum (fun x _ => le_of_lt x.2) hs
    linarith [le_max_right (2 : ℝ) (M + 1)]
  have hH_sqrt : Real.sqrt 3 / 2 < H := by
    have h3 := Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num)
    nlinarith [sq_nonneg (Real.sqrt 3 - 2)]
  rcases eq_or_lt_of_le hnorm_ge with h_eq | h_gt
  · -- ‖s‖ = 1: on the unit circle, must have |re| < 1/2
    have h_re_lt : |(s : ℂ).re| < 1/2 := by
      by_contra h_ge
      push_neg at h_ge
      have h_abs_eq : |(s : ℂ).re| = 1/2 := le_antisymm habs_re h_ge
      rcases abs_cases (s : ℂ).re with ⟨h_eq_abs, _⟩ | ⟨h_eq_abs, _⟩
      · exact hsρ1 (unit_circle_re_pos_half_eq_rho_plus_one s h_eq.symm (by linarith))
      · exact hsρ (unit_circle_re_neg_half_eq_rho s h_eq.symm (by linarith))
    exact gWN_fdBoundary_H_eq_neg_half_of_unitArc H (by linarith) (↑s) h_eq.symm h_re_lt h_im_pos
  · -- ‖s‖ > 1: on a vertical edge, |re| = 1/2
    have h_abs_eq : |(s : ℂ).re| = 1/2 := by
      by_contra h_ne
      exact h_not_int ⟨h_gt, lt_of_le_of_ne habs_re h_ne⟩
    have h_im_sqrt := vert_edge_im_gt_sqrt3_half s h_gt h_abs_eq
    rcases abs_cases (s : ℂ).re with ⟨h_eq_abs, _⟩ | ⟨h_eq_abs, _⟩
    · exact gWN_fdBoundary_H_eq_neg_half_of_rightEdge H hH_sqrt (↑s) (by linarith) h_gt
        h_im_sqrt h_im_lt_H
    · exact gWN_fdBoundary_H_eq_neg_half_of_leftEdge H hH_sqrt (↑s) (by linarith) h_gt
        h_im_sqrt h_im_lt_H

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Textbook Orbit-Sum Valence Formula** (fully automated, no extra hypotheses).

Eliminates the `h_boundary_weight` hypothesis from `valenceFormula_orbit_sum`
by automatically constructing the boundary weights from `hS : ∀ p ∈ S, p ∈ 𝒟'`. -/
theorem valenceFormula_orbit_sum_auto {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_i') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho') +
    ∑ s ∈ S.filter (fun p => p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧
        p ≠ ellipticPoint_rho_plus_one' ∧ ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
      ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S_leftVert S, ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S.filter (fun p => p ≠ ellipticPoint_rho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
      ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 :=
  valenceFormula_orbit_sum f hf S hS hS_complete (boundary_weight_auto S hS)

end
