/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Infrastructure.MeasureTheoryHelpers
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Infrastructure.PiecewiseIntegration
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Infrastructure.CauchyTheorem
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Infrastructure.LHopital

/-!
# Infrastructure for Complex Analysis

This module provides the foundational infrastructure needed to complete the proofs
in the generalized residue theorem and valence formula.

## Module Structure

* `MeasureTheoryHelpers` - Measurability and integrability for PV integrands
* `PiecewiseIntegration` - Splitting integrals at partition points
* `CauchyTheorem` - Cauchy's theorem for piecewise C¹ curves
* `LHopital` - L'Hôpital's rule and Taylor expansion lemmas

## Key Results Summary

### Measure Theory (MeasureTheoryHelpers)
- `aEStronglyMeasurable_pv_integrand` - PV integrand is ae measurable
- `intervalIntegrable_pv_integrand` - PV integrand is interval integrable when bounded
- `intervalIntegrable_of_pv_exists` - Integrability from PV limit existence

### Piecewise Integration (PiecewiseIntegration)
- `intervalIntegral_eq_sum_adjacent` - Integral splits at partition points
- `generalizedWindingNumber_eq_classical_piecewiseC1` - Winding number extension

### Cauchy Theorem (CauchyTheorem)
- `cauchyTheorem_piecewiseC1` - Cauchy for piecewise C¹ curves
- `cauchyTheorem_homotopic` - Homotopy invariance
- `generalizedResidueTheorem` - Generalized residue theorem with PV

### L'Hôpital (LHopital)
- `lhopital_twice` - Double L'Hôpital application
- `windingNumberIntegrand_limit_at_zero'` - Limit formula with curvature

## Dependencies

This infrastructure enables completion of sorries in:
- `PrincipalValue.lean` (integrability and dominated convergence)
- `WindingNumber.lean` (piecewise C¹ extension)
- `ResidueTheory.lean` (Cauchy theorem and residue formula)
- `AsymptoticEstimates.lean` (L'Hôpital for curvature limit)
- `ValenceFormula.lean` (combining everything)

## References

- Isabelle `HOL-Complex_Analysis` library
- Hungerbühler-Wasem: "Non-integer valued winding numbers"
- Mathlib measure theory and complex analysis
-/
