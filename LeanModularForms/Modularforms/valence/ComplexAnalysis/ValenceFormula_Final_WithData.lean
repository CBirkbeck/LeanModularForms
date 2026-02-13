/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Core

/-!
# Valence Formula — Internal "With Data" Wrappers

These are the ℂ-typed internal wrappers that expose all data hypotheses
(`zeros`, `hzeros`, `hint`, `hcusp_nonvan`, etc.) from the split-file Core proof.

The canonical public API lives in `ValenceFormula_Final.lean` and forwards to
the legacy monolithic proof in `ValenceFormula.lean`.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Internal: base identity with all data explicit (ℂ-typed). -/
theorem valenceFormula_with_data {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 - (orderAtCusp' f : ℂ) :=
  valence_formula_base_identity f hf zeros hzeros hzeros_fd hzeros_complete hint hcusp_nonvan

/-- Internal: classical form with all data explicit (ℂ-typed).

Uses the unconditional decomposition — no `hclass` or `hno_rpo` needed.
Boundary points (high-altitude, edge, arc non-elliptic) have `effectiveWinding = 0`
and contribute nothing to the sum. -/
theorem valenceFormula_classical_with_data {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℂ) else 0) +
      (1/3 : ℂ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 :=
  valence_formula_classical_form_unconditional f hf zeros hzeros hzeros_fd hzeros_complete
    hint hcusp_nonvan

/-- Internal: base identity with larger nonvanishing radius (ℂ-typed).

Accepts `closedBall(0, r)` with `r ≥ seg5_q_radius`, forwarding to
`valence_formula_base_identity_of_larger_radius` from Core. -/
theorem valenceFormula_with_data_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 - (orderAtCusp' f : ℂ) :=
  valence_formula_base_identity_of_larger_radius f hf zeros hzeros hzeros_fd
    hzeros_complete hint hr hcusp_nonvan

/-- Internal: classical form with larger nonvanishing radius (ℂ-typed).

Accepts `closedBall(0, r)` with `r ≥ seg5_q_radius`, forwarding to
`valence_formula_classical_form_of_larger_radius` from Core. -/
theorem valenceFormula_classical_with_data_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℂ) else 0) +
      (1/3 : ℂ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 :=
  valence_formula_classical_form_of_larger_radius f hf zeros hzeros hzeros_fd
    hzeros_complete hint hr hcusp_nonvan

end
