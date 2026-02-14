/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Final_Split

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

end
