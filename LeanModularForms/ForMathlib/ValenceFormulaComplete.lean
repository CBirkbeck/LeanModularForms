/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ValenceFormula.TextbookForm

/-!
# The Completely Unconditional Valence Formula

This file provides the final, completely unconditional valence formula for
weight-`k` modular forms on `SL₂(ℤ)`:

$$\operatorname{ord}_\infty(f) + \tfrac{1}{2}\operatorname{ord}_i(f)
  + \tfrac{1}{3}\operatorname{ord}_\rho(f)
  + \sum_{q\;\text{non-ell}} \operatorname{ord}_q(f) = \frac{k}{12}$$

The only hypothesis is `hf : f ≠ 0`.

## Note on imports

This file imports from `ValenceFormula.TextbookForm` (the existing project code)
which already contains the fully proved theorem. The ForMathlib files in this
directory provide the clean reorganized API for eventual mathlib submission.

The `PiecewiseC1Immersion` name collision between ForMathlib and the existing
project code prevents importing both simultaneously. When the project code is
fully migrated to the ForMathlib type system, this file will import only from
ForMathlib.

## Main results

* `valence_formula_textbook_orbit_finsum_complete` -- the valence formula with
  no hypotheses beyond `hf : f ≠ 0`

## References

* Diamond--Shurman, *A First Course in Modular Forms*, Theorem 3.1.1
* Hungerbühler--Wasem, *A generalized notion of winding numbers*, arXiv:1808.00997v2
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

noncomputable section

/-- **The Valence Formula** for weight-`k` modular forms on `SL₂(ℤ)` --
completely unconditional.

For any nonzero modular form `f` of weight `k` for `SL₂(ℤ)`:

$$\operatorname{ord}_\infty(f) + \tfrac{1}{2}\operatorname{ord}_i(f)
  + \tfrac{1}{3}\operatorname{ord}_\rho(f)
  + \sum_{q\;\text{non-ell}} \operatorname{ord}_q(f) = \frac{k}{12}$$

where the sum runs over all non-elliptic `SL₂(ℤ)`-orbits in the upper
half-plane. -/
theorem valence_formula_textbook_orbit_finsum_complete
    {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbit), ordOrbitQ f q =
    (k : ℂ) / 12 :=
  valence_formula_textbook_orbit_finsum f hf

end
