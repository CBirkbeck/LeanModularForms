/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Final_Split
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_WindingWeights
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_OnCurvePVProvider
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Interior_H

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

end
