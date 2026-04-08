/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.CrossingAtI
import LeanModularForms.ForMathlib.CrossingAtRho
import LeanModularForms.ForMathlib.InteriorWindingProof
import LeanModularForms.ForMathlib.SegmentAnalysis
import LeanModularForms.ForMathlib.ValenceAssembly

/-!
# Complete FDWindingDataFull Assembly

This file assembles `FDWindingDataFull H` from five analytical hypotheses, using all
previously proved geometric infrastructure (near/far bounds, avoidance, integrability).

## Hypotheses taken as parameters

1. `ArcFTCHyp` at `i` — FTC telescoping + integrability + limit for the crossing at `i`
2. `CornerFTCHyp` at `ρ` — asymmetric FTC for the crossing at `ρ`
3. `CornerFTCHyp` at `ρ+1` — asymmetric FTC for the crossing at `ρ+1`
4. Interior contour integral — `∮_γ (w - z)⁻¹ dw = -2πi` for strict interior `z`
5. Boundary winding — `HasGeneralizedWindingNumber γ z (-1/2)` for smooth boundary `z`

## What is proved unconditionally (from T1–T8)

- `fdBoundaryPC1Path` and `fdBoundaryPC1Path_eq` — the `PiecewiseC1Path` (T1)
- `arcsinDelta` cutoff + `arc_near/far_at_I_arcsin` — geometry at `i` (T2)
- `vertDelta`, `arc_near/far_at_rho_arcsin`, `vert_near/far_at_rho` — geometry at `ρ` (T3)
- Same for `ρ+1` (T4)
- `fdBoundary_avoids_interior` + reduction to contour integral (T5)
- `gamma_integrable_left/right_of_I` — integrability at `i` (T8)

## Main results

* `mkFDWindingDataFull` — full `FDWindingDataFull H` from the 5 hypotheses
* `mkFDWindingData_of_analytical` — `FDWindingData H` from the first 4 hypotheses

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ### FDWindingData from analytical hypotheses -/

/-- Construct `FDWindingData H` from the four analytical hypotheses:
`ArcFTCHyp` at `i`, `CornerFTCHyp` at `ρ` and `ρ+1`, and the interior contour
integral identity.

This uses:
- `fdBoundaryPC1Path` for the path (T1)
- `singleCrossingData_atI_of_ftcHyp` for the crossing at `i` (T2)
- `hasWindingNumber_atRho_of_cornerFtcHyp` for the crossing at `ρ` (T3)
- `hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp` for the crossing at `ρ+1` (T4)
- `fdBoundary_interior_winding_neg_one` for interior winding (T5) -/
def mkFDWindingData_of_analytical {H : ℝ} (hH : 1 < H)
    (h_ftc_i : ArcFTCHyp (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH))
      I (2/5) arcsinDelta (min (1/3) (H - 1)) (-(↑Real.pi * I)))
    (h_ftc_rho : CornerFTCHyp (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH))
      ellipticPointRho (3/5) arcsinDelta (vertDelta H)
      (min (1/3) (H - Real.sqrt 3 / 2)) (-(↑Real.pi / 3 * I)))
    (h_ftc_rho1 : CornerFTCHyp (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH))
      ellipticPointRhoPlusOne (1/5) (vertDelta H) arcsinDelta
      (min (1/3) (H - Real.sqrt 3 / 2)) (-(↑Real.pi / 3 * I)))
    (h_interior : ∀ z : ℂ, FDStrictInterior z H →
      (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)).contourIntegral
        (fun w => (w - z)⁻¹) = -(2 * ↑Real.pi * I)) :
    FDWindingData H where
  boundary := fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)
  boundary_eq := fdBoundaryPC1Path_eq H (fdHeightValid_of_one_lt H hH)
  interior_winding := fun z hz_norm hz_re hz_im_pos hz_im_lt => by
    have hz : FDStrictInterior z H := ⟨hz_norm, hz_re, hz_im_pos, hz_im_lt⟩
    exact fdBoundary_interior_winding_neg_one (fdHeightValid_of_one_lt H hH) hz
      (h_interior z hz)
  winding_at_i := by
    let D_i := singleCrossingData_atI_of_ftcHyp hH
      (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH))
      (fdBoundaryPC1Path_eq H (fdHeightValid_of_one_lt H hH))
      h_ftc_i
    have := D_i.hasWindingNumber
    rwa [show D_i.L = -(↑Real.pi * I) from rfl,
      show -(↑Real.pi * I) / (2 * ↑Real.pi * I) = (-1 : ℂ) / 2 from by
        have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        have hI : (I : ℂ) ≠ 0 := I_ne_zero
        field_simp] at this
  winding_at_rho :=
    hasWindingNumber_atRho_of_cornerFtcHyp hH
      (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH))
      (fdBoundaryPC1Path_eq H (fdHeightValid_of_one_lt H hH))
      h_ftc_rho
  winding_at_rho_plus_one :=
    hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp hH
      (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH))
      (fdBoundaryPC1Path_eq H (fdHeightValid_of_one_lt H hH))
      h_ftc_rho1

/-! ### Full FDWindingDataFull from all analytical hypotheses -/

/-- Construct `FDWindingDataFull H` from all five analytical hypotheses.

This is the complete assembly: it bundles the path, all three crossing winding numbers,
the interior winding, and the smooth boundary winding into a single `FDWindingDataFull`.

The five hypotheses are the minimal analytical inputs that cannot be derived from pure
geometry:

1. **FTC at `i`**: `ArcFTCHyp` provides the E function, integrals-equal-E identity,
   integrability on left/right segments, and `E(ε) → -πi` limit.

2. **FTC at `ρ`**: `CornerFTCHyp` provides the same for the asymmetric corner crossing
   at `ρ` (left delta = arcsinDelta for arc side, right delta = vertDelta for vertical).

3. **FTC at `ρ+1`**: `CornerFTCHyp` for the mirror crossing at `ρ+1` (left delta =
   vertDelta for vertical, right delta = arcsinDelta for arc side).

4. **Interior contour integral**: for every strict interior point `z`, the contour
   integral `∮_γ (w - z)⁻¹ dw = -2πi`.

5. **Boundary winding**: for every smooth boundary point `z` (not interior, not elliptic),
   the generalized winding number is `-1/2`. -/
def mkFDWindingDataFull {H : ℝ} (hH : 1 < H)
    (h_ftc_i : ArcFTCHyp (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH))
      I (2/5) arcsinDelta (min (1/3) (H - 1)) (-(↑Real.pi * I)))
    (h_ftc_rho : CornerFTCHyp (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH))
      ellipticPointRho (3/5) arcsinDelta (vertDelta H)
      (min (1/3) (H - Real.sqrt 3 / 2)) (-(↑Real.pi / 3 * I)))
    (h_ftc_rho1 : CornerFTCHyp (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH))
      ellipticPointRhoPlusOne (1/5) (vertDelta H) arcsinDelta
      (min (1/3) (H - Real.sqrt 3 / 2)) (-(↑Real.pi / 3 * I)))
    (h_interior : ∀ z : ℂ, FDStrictInterior z H →
      (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)).contourIntegral
        (fun w => (w - z)⁻¹) = -(2 * ↑Real.pi * I))
    (h_boundary : ∀ z : ℂ, z.im > 0 → z.im < H →
      z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
      ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
      1 ≤ Complex.normSq z → |z.re| ≤ 1/2 →
      HasGeneralizedWindingNumber
        (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)) z (-1/2)) :
    FDWindingDataFull H where
  toFDWindingData := mkFDWindingData_of_analytical hH h_ftc_i h_ftc_rho h_ftc_rho1 h_interior
  boundary_winding := h_boundary

/-! ### Variant: take only the PV limits as hypotheses

For users who have already proved integrability and FTC on segments, the PV limits
(the `Tendsto E (nhdsWithin 0 (Ioi 0)) (nhds L)` parts) are the essential content.
This variant packs the integrability and FTC into a structure, then takes the limits
as separate hypotheses.

This is NOT provided here because it would require spelling out the E functions explicitly,
which depends on the specific branch-cut choices for Complex.log on each segment.
The `ArcFTCHyp` / `CornerFTCHyp` structures are the right level of abstraction. -/

/-! ### Convenience: extract the winding number equalities -/

/-- The winding number at `i` is `-1/2`, given the analytical hypotheses. -/
theorem windingNumber_atI_eq {H : ℝ} (hH : 1 < H)
    (h_ftc_i : ArcFTCHyp (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH))
      I (2/5) arcsinDelta (min (1/3) (H - 1)) (-(↑Real.pi * I))) :
    generalizedWindingNumber (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)) I =
      -1/2 :=
  windingNumber_atI_of_ftcHyp hH
    (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH))
    (fdBoundaryPC1Path_eq H (fdHeightValid_of_one_lt H hH))
    h_ftc_i

/-- The interior winding number is `-1`, given the contour integral identity. -/
theorem windingNumber_interior_eq {H : ℝ} (hH : 1 < H) {z : ℂ}
    (hz : FDStrictInterior z H)
    (h_integral : (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)).contourIntegral
      (fun w => (w - z)⁻¹) = -(2 * ↑Real.pi * I)) :
    generalizedWindingNumber (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)) z = -1 :=
  (fdBoundary_interior_winding_neg_one (fdHeightValid_of_one_lt H hH) hz h_integral).eq

/-! ### Summary of what remains to fill the hypotheses

To construct `FDWindingDataFull` unconditionally (with no hypotheses beyond `1 < H`),
one must provide:

1. **`ArcFTCHyp` at `i`**: This requires:
   - An `E` function (the FTC expression for far-segment integrals)
   - `h_ftc`: `∫₀^{2/5-δ} + ∫_{2/5+δ}^1 = E(ε)` (FTC on segments 1,3,4,5 + branch)
   - `hint_left/right`: integrability (available from `gamma_integrable_left/right_of_I`)
   - `h_limit`: `E(ε) → -πi` (requires FTC with Complex.log + telescoping + branch)

2. **`CornerFTCHyp` at `ρ`**: Similar, with asymmetric deltas (arcsin left, vert right).

3. **`CornerFTCHyp` at `ρ+1`**: Mirror of ρ (vert left, arcsin right).

4. **Interior contour integral**: `∮_γ (w-z)⁻¹ = -2πi` for strict interior `z`.
   This requires: FTC on each of the 5 segments with `log(γ(t)-z)` as primitive,
   telescoping of the 5 log differences, and the total branch correction = `-2πi`.

5. **Boundary winding**: `HasGeneralizedWindingNumber γ z (-1/2)` for smooth boundary `z`.
   This requires: the CPV integral at smooth on-curve points (single crossing, angle π).

The geometric infrastructure (near/far bounds, cutoffs, avoidance, integrability) is
fully proved. The remaining work is purely analytical: computing contour integrals via FTC
with the correct branch of `Complex.log`.
-/

end
