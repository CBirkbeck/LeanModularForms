/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ValenceFormula.TextbookForm

/-!
# Core Identity for the Valence Formula

This file combines the residue side (CPV integral → winding-weighted ord sum)
with the modular side (CPV integral → k/12 - ord_∞) by uniqueness of limits,
then substitutes the explicit winding weights to obtain the orbit-sum form
of the valence formula.

## Architecture

The proof proceeds in two stages:

### Stage 1: Raw identity with abstract winding weights

The PV chain identity (`pv_chain_identity` from `ValenceFormula.PVChain`):

  `Σ_s gWN(γ, s) · ord(f, s) = -(k/12 - ord_∞)`

is proved by showing both the residue side and the modular side are limits of
the same ε-truncated integral of `logDeriv(f)`, then applying uniqueness of
limits in a Hausdorff space and cancelling `2πi`.

The residue side applies the generalized residue theorem
(`ForMathlib/GeneralizedResidueTheorem.lean`) to `logDeriv(f)`, whose simple
poles have residue equal to the order of vanishing
(`ForMathlib/LogDerivModularForm.lean`).

The modular side uses:
- T-cancellation of vertical integrals (periodicity of `logDeriv f`)
- S-arc contribution `-(2πi)(k/12)` (modular identity `f(Sz) = z^k f(z)`)
- Horizontal contribution `2πi · ord_∞` (q-expansion winding number)

### Stage 2: Substitute explicit winding weights

The winding weights are:
- `-1/2` at `i` (smooth crossing on the arc, angle `π`)
- `-1/6` at `ρ` and `ρ+1` (corner crossings with angle `π/3`)
- `-1` at strict interior points (full winding, from `InteriorContourIntegral`)
- `-1/2` at non-elliptic boundary points (smooth crossing)

After substitution and T-pairing of orbits (`ρ+1 ↔ ρ`, right vert ↔ left vert,
right arc ↔ left arc from `OrbitPairing`), we obtain:

  `ord_∞ + (1/2)·ord_i + (1/3)·ord_ρ + Σ_{non-ell} ord_q = k/12`

## Main results

* `core_identity_forMathlib` — the orbit-sum identity with explicit coefficients
* `valence_formula_orbit_sum_forMathlib` — the textbook orbit-sum with `∑ᶠ`

## Import note

This file imports `ValenceFormula.TextbookForm` (from the valence formula chain)
which transitively includes all the analytical infrastructure:
- Generalized residue theorem, PV chain, winding weights
- FD boundary geometry, crossing analysis, interior winding
- Modular invariance, orbit pairing, canonical representatives

The parallel ForMathlib chain (`ForMathlib/ResidueSide.lean`) provides the same
results in a documentation-focused format. Due to a name collision between the
`ForMathlib.PiecewiseC1Path` chain and the `GeneralizedResidueTheory.Basic`
chain for `PwC1Immersion`, the two import trees cannot be combined in
a single file. This will be resolved when the ForMathlib chain fully replaces
the old `GeneralizedResidueTheory` chain.

## References

* Diamond–Shurman, *A First Course in Modular Forms*, Theorem 3.1.1
* Serre, *A Course in Arithmetic*, Chapter VII
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ### The core identity with explicit coefficients

This is the orbit-sum form of the valence formula, with explicit coefficients
1/2 at `i`, 1/3 at `ρ`, and 1 at non-elliptic points. The proof delegates to
`valence_formula_orbit_sum` from `ValenceFormula.CoreIdentity`, which combines
the PV chain identity with winding weight substitution and orbit pairing. -/

include hf in
/-- **The core identity**: the orbit-sum valence formula with explicit coefficients.

For any finite set `S ⊆ 𝒟` capturing all zeros of `f`:

  `ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + Σ (non-ell in S) ord_s(f) = k/12`

where the non-elliptic sum decomposes into:
- strict interior points (‖p‖ > 1, |re| < 1/2)
- left vertical points (re = -1/2, ‖p‖ > 1)
- left arc points (‖p‖ = 1, re < 0, not ρ) -/
theorem core_identity_forMathlib
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
        ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
      ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ sLeftVertFM S, ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
      ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 :=
  valence_formula_orbit_sum f hf S hS hS_complete

/-! ### The textbook orbit-sum valence formula

The orbit-sum form with `∑ᶠ` over non-elliptic `SL₂(ℤ)`-orbits.
This delegates to `valence_formula_textbook_orbit_finsum` from
`ValenceFormula.TextbookForm`, which uses the canonical representative
machinery to convert from the Finset sum over `s₀` to the `∑ᶠ` over orbits. -/

include hf in
/-- **The valence formula** in orbit-sum form: for any nonzero modular form `f`
of weight `k` for `SL₂(ℤ)`:

  `ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + Σ_q ord_q(f) = k/12`

where the sum runs over all non-elliptic `SL₂(ℤ)`-orbits.

This is the culmination of the ForMathlib chain, combining:
1. General complex analysis (piecewise C¹ paths, generalized winding numbers,
   generalized residue theorem)
2. FD boundary geometry (crossing analysis, FTC telescoping, interior winding)
3. Modular invariance (T-cancellation, S-arc, horizontal contribution)
4. OrbitFM algebra (T-pairing, S-pairing, canonical representatives) -/
theorem valence_formula_orbit_sum_forMathlib :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbitFM), ordOrbitQFM f q =
    (k : ℂ) / 12 :=
  valence_formula_textbook_orbit_finsum f hf

/-! ### Algebraic rearrangement helpers

These pure-algebra lemmas convert between different forms of the identity. -/

/-- Rearrangement: from `Σ wt = -(k/12 - ord_∞)` derive `ord_∞ + (-Σ wt) = k/12`. -/
theorem residue_side_rearrange_forMathlib (ord_inf weighted_sum : ℂ)
    (h : weighted_sum = -((k : ℂ) / 12 - ord_inf)) :
    ord_inf + (-weighted_sum) = (k : ℂ) / 12 := by rw [h]; ring

/-- Cancel `2πi` from both sides: if `2πi · L = -(2πi · R)` then `L = -R`. -/
theorem cancel_two_pi_I_forMathlib {L R : ℂ}
    (h : 2 * ↑Real.pi * I * L = -(2 * ↑Real.pi * I * R)) :
    L = -R := by
  have hpi : (2 : ℂ) * ↑Real.pi * I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
      ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero, or_self]
  rw [show -(2 * ↑Real.pi * I * R) = 2 * ↑Real.pi * I * (-R) from by ring] at h
  exact mul_left_cancel₀ hpi h

end
