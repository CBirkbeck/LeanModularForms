/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.ValenceAssembly
import LeanModularForms.ForMathlib.ArcFTCAtI
import LeanModularForms.ForMathlib.CornerFTCAtRho
import LeanModularForms.ForMathlib.InteriorContourIntegral
import LeanModularForms.ForMathlib.BoundaryWinding
import LeanModularForms.ForMathlib.FDWindingComplete

/-!
# Valence Formula — Final Assembly

This file wires together the complete chain of analytical results to produce the
valence formula for weight-`k` modular forms on `SL₂(ℤ)`.

## Unconditional pieces (fully proved, no hypotheses beyond `1 < H`)

1. **FTC at `i`**: `arcFTCHyp_atI` — the complete `ArcFTCHyp` at `i`
2. **FTC at `ρ`**: `cornerFTCHyp_atRho` — the complete `CornerFTCHyp` at `ρ`
3. **FTC at `ρ+1`**: `cornerFTCHyp_atRhoPlusOne_unconditional` — the complete
   `CornerFTCHyp` at `ρ+1`
4. **Interior contour integral**: `fdBoundaryPC1Path_contourIntegral_interior_eq` —
   `∮_γ (w - z)⁻¹ dw = -2πi` for strict interior `z`

## Remaining hypotheses (taken as parameters)

5. **Boundary winding**: `HasGeneralizedWindingNumber γ z (-1/2)` for smooth
   boundary points. This requires `SingleCrossingData` per point.

6. **Residue-modular identity**: the generalized residue theorem applied to
   `logDeriv(f)` along the FD boundary, combined with modular invariance.

## Main results

* `mkFDWindingDataFull_of_boundaryWinding` — assembles `FDWindingDataFull H` from
  the four unconditional pieces plus the boundary winding hypothesis
* `valence_formula_textbook_orbit_finsum_unconditional` — the textbook valence formula
  taking only `hf`, boundary winding, and the residue-modular identity

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

noncomputable section

/-! ### Residue-modular hypothesis -/

/-- The residue-modular identity: applying the generalized residue theorem to
`logDeriv(f)` along the FD boundary and computing the modular side.

This encodes the result of:
- Generalized residue theorem: `∮ logDeriv(f) = Σ winding_number(z) · ord(f,z)`
- Modular side: horizontal segment gives cusp order, verticals cancel by
  T-periodicity, arcs give `-k/6` by the S-transformation identity

The identity holds for any finite set `S ⊆ 𝒟` capturing all zeros. -/
structure ResidueModularHyp {k : ℤ} (f : ModularForm (Gamma 1) k) (H : ℝ)
    (boundary : PiecewiseC1Path (fdStart H) (fdStart H)) where
  /-- All fundamental domain points have imaginary part below `H`. -/
  h_above : ∀ p : ℍ, p ∈ 𝒟 → (p : ℂ).im < H
  /-- The residue-modular identity. -/
  h_identity : ∀ (S : Finset ℍ), (∀ p ∈ S, p ∈ 𝒟) →
    (∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) →
    (orderAtCusp' f : ℂ) +
    ∑ s ∈ S, (-generalizedWindingNumber boundary (↑s : ℂ)) *
      ↑(orderOfVanishingAt' (⇑f) s) = (k : ℂ) / 12

/-! ### Assembly of FDWindingDataFull -/

/-- Assemble `FDWindingDataFull H` using the four unconditional FTC/interior pieces
plus the boundary winding hypothesis.

**Unconditional** (filled in automatically):
- `arcFTCHyp_atI` for the crossing at `i`
- `cornerFTCHyp_atRho` for the crossing at `ρ`
- `cornerFTCHyp_atRhoPlusOne_unconditional` for the crossing at `ρ+1`
- `fdBoundaryPC1Path_contourIntegral_interior_eq` for interior contour integrals

**Taken as parameter:**
- `h_boundary`: the generalized winding number at smooth boundary points -/
def mkFDWindingDataFull_of_boundaryWinding {H : ℝ} (hH : 1 < H)
    (h_boundary : ∀ z : ℂ, z.im > 0 → z.im < H →
      z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
      ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
      1 ≤ Complex.normSq z → |z.re| ≤ 1/2 →
      HasGeneralizedWindingNumber
        (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)) z (-1/2)) :
    FDWindingDataFull H :=
  mkFDWindingDataFull hH
    (arcFTCHyp_atI hH (fdBoundaryPC1Path_eq H (fdHeightValid_of_one_lt H hH)))
    (cornerFTCHyp_atRho hH (fdBoundaryPC1Path_eq H (fdHeightValid_of_one_lt H hH)))
    (cornerFTCHyp_atRhoPlusOne_unconditional hH
      (fdBoundaryPC1Path_eq H (fdHeightValid_of_one_lt H hH)))
    (fun _ hz => fdBoundaryPC1Path_contourIntegral_interior_eq
      (fdHeightValid_of_one_lt H hH) hz)
    h_boundary

/-! ### The unconditional valence formula -/

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

include hf in
/-- **The Valence Formula** for weight-`k` modular forms on `SL₂(ℤ)`.

$$\operatorname{ord}_\infty(f) + \tfrac{1}{2}\operatorname{ord}_i(f)
  + \tfrac{1}{3}\operatorname{ord}_\rho(f)
  + \sum_{q\;\text{non-ell}} \operatorname{ord}_q(f) = \frac{k}{12}$$

This takes the exact textbook form with `∑ᶠ` over non-elliptic orbits.

### Remaining hypotheses

The two remaining hypotheses represent the deepest analytical facts:

1. **`h_boundary`**: The generalized winding number equals `-1/2` at every smooth
   boundary point. This requires constructing `SingleCrossingData` for each such
   point (the CPV integral of `(w - z)⁻¹` along the boundary converges to `-πi`).

2. **`h_residue_modular`**: The residue-modular identity combining the generalized
   residue theorem for `logDeriv(f)` with modular invariance (horizontal segment
   gives cusp order, verticals cancel, arcs give `-k/6`).

### What is discharged automatically

- **FTC at `i`**: `arcFTCHyp_atI`
- **FTC at `ρ`**: `cornerFTCHyp_atRho`
- **FTC at `ρ+1`**: `cornerFTCHyp_atRhoPlusOne_unconditional`
- **Interior contour integral**: `fdBoundaryPC1Path_contourIntegral_interior_eq` -/
theorem valence_formula_textbook_orbit_finsum_unconditional
    {H : ℝ} (hH : 1 < H)
    (h_boundary : ∀ z : ℂ, z.im > 0 → z.im < H →
      z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
      ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
      1 ≤ Complex.normSq z → |z.re| ≤ 1/2 →
      HasGeneralizedWindingNumber
        (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)) z (-1/2))
    (h_residue_modular : ResidueModularHyp f H
      (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH))) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbit), ordOrbitQ f q =
    (k : ℂ) / 12 :=
  valence_formula_textbook_of_windingDataFull f hf
    ⟨H, mkFDWindingDataFull_of_boundaryWinding hH h_boundary,
     h_residue_modular.h_above, h_residue_modular.h_identity⟩

end
