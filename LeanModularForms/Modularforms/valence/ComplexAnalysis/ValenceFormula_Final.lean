/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula

/-!
# The Valence Formula — Canonical Public API (Legacy Route)

This file provides the canonical user-facing theorems of the valence formula for
modular forms of level 1. The signatures use `ℚ`-typed coefficients, the orbifold
winding number `windingNumberCoeff'`, and require only the minimal set of hypotheses:
`f ≠ 0`, a finset `S ⊆ 𝒟'`, and completeness of `S`.

These forward to the monolithic `ValenceFormula.lean` and inherit its `sorryAx`.
For axiom-clean versions, see `ValenceFormula_Final_Split.lean`.

## Main Theorems

* `valenceFormula` — The general (orbifold) form:
    `ord_∞(f) + Σ_{p ∈ S} windingNumberCoeff'(p) · ord_p(f) = k/12`
* `valenceFormula_classical` — The classical form with explicit coefficients:
    `ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + Σ_{p ∈ S} ord_p(f) = k/12`

## References

* [Serre, *A Course in Arithmetic*], Chapter VII
* [Miyake, *Modular Forms*], Section 2.4
* [Diamond-Shurman, *A First Course in Modular Forms*], Section 3.5
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

noncomputable section

/-! ## The Valence Formula — Canonical Public Theorems -/

/-- **The Valence Formula** (orbifold form).

For a nonzero modular form `f` of weight `k` for SL₂(ℤ), and any finset `S`
of points in the fundamental domain `𝒟'` that contains all zeros of `f`:

  `ord_∞(f) + Σ_{p ∈ S} windingNumberCoeff'(p) · ord_p(f) = k/12`

where `windingNumberCoeff'` is `1` at interior points, `1/2` at `i`, `1/3` at `ρ`. -/
theorem valenceFormula {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    (orderAtCusp' f : ℚ) +
    ∑ p ∈ S, windingNumberCoeff' p * (orderOfVanishingAt' (⇑f) p : ℚ) = k / 12 :=
  valenceFormula' k f hf S hS hS_complete



/-- **The Classical Valence Formula**.

For a nonzero modular form `f` of weight `k` for SL₂(ℤ):

  `ord_∞(f) + (1/2) · ord_i(f) + (1/3) · ord_ρ(f) + Σ_{p ∈ S} ord_p(f) = k/12`

where the sum is over non-elliptic zeros in the fundamental domain.
The coefficients `1/2` and `1/3` arise because `i` and `ρ` are elliptic points
of order 2 and 3 respectively in SL₂(ℤ)\ℍ. -/
theorem valenceFormula_classical {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟' ∧ p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho')
    (hS_complete : ∀ p, p ∈ 𝒟' → p ≠ ellipticPoint_i' → p ≠ ellipticPoint_rho' →
                    orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    (orderAtCusp' f : ℚ) +
    (1/2 : ℚ) * orderOfVanishingAt' (⇑f) ellipticPoint_i' +
    (1/3 : ℚ) * orderOfVanishingAt' (⇑f) ellipticPoint_rho' +
    ∑ p ∈ S, (orderOfVanishingAt' (⇑f) p : ℚ) = k / 12 :=
  valenceFormula_classical' k f hf S hS hS_complete

end
