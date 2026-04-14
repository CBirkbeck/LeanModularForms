/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.ArcFTCAtI
import LeanModularForms.ForMathlib.ArcGenericFTCProvider
import LeanModularForms.ForMathlib.CornerFTCAtRho
import LeanModularForms.ForMathlib.CrossingAtI
import LeanModularForms.ForMathlib.CrossingAtRho
import LeanModularForms.ForMathlib.FDWindingDataFullAssembly
import LeanModularForms.ForMathlib.InteriorContourIntegral
import LeanModularForms.ForMathlib.PVChainProof
import LeanModularForms.ForMathlib.Seg1FTCProvider
import LeanModularForms.ForMathlib.Seg4FTCProvider
import LeanModularForms.ForMathlib.WindingWeightsUnconditional

/-!
# `FDWindingDataFull` from all three FTC providers (fully unconditional)

This file plugs the now-unconditional seg1, seg4, and arc FTC providers into
`mkFDWindingDataFull_of_ftcProviders`, yielding a fully unconditional
`FDWindingDataFull` constructor from just a `FDWindingData`.

## Main results

* `mkFDWindingDataFull_unconditional` — `FDWindingDataFull` from
  `FDWindingData` alone; all three FTC providers (seg1, seg4, arc) are
  filled in from the unconditional constructors.
* `mkFDWindingDataFull_seg1seg4_unconditional` — legacy version still
  taking an arc FTC provider as hypothesis.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- `FDWindingDataFull H` constructor where seg1 and seg4 FTC providers are
filled in unconditionally; only the arc FTC provider is required. -/
def mkFDWindingDataFull_seg1seg4_unconditional {H : ℝ} (hH : 1 < H)
    (D : FDWindingData H)
    (ftc_arc : ∀ θ₀ : ℝ, Real.pi / 3 < θ₀ → θ₀ < 2 * Real.pi / 3 →
      ArcFTCHyp D.boundary (exp (↑θ₀ * I)) (arcT₀ θ₀) arcsinDelta
        (arcThreshold H θ₀) (-(↑Real.pi * I))) :
    FDWindingDataFull H := by
  have hH_sqrt3 : Real.sqrt 3 / 2 < H := by
    have h_sqrt3_lt : Real.sqrt 3 < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_nonneg 3]
    linarith
  exact mkFDWindingDataFull_of_ftcProviders hH D
    (fun z₀ hz_re hi_lo hi_hi =>
      arcFTCHyp_seg1 hH_sqrt3 D.boundary D.boundary_eq hz_re hi_lo hi_hi)
    (fun z₀ hz_re hi_lo hi_hi =>
      arcFTCHyp_seg4 hH_sqrt3 D.boundary D.boundary_eq hz_re hi_lo hi_hi)
    ftc_arc

/-- `FDWindingDataFull H` constructor from `FDWindingData H` alone.
All three FTC providers (seg1, seg4, arc) are supplied unconditionally. -/
def mkFDWindingDataFull_unconditional {H : ℝ} (hH : 1 < H)
    (D : FDWindingData H) :
    FDWindingDataFull H := by
  have hH_sqrt3 : Real.sqrt 3 / 2 < H := by
    have h_sqrt3_lt : Real.sqrt 3 < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_nonneg 3]
    linarith
  exact mkFDWindingDataFull_of_ftcProviders hH D
    (fun z₀ hz_re hi_lo hi_hi =>
      arcFTCHyp_seg1 hH_sqrt3 D.boundary D.boundary_eq hz_re hi_lo hi_hi)
    (fun z₀ hz_re hi_lo hi_hi =>
      arcFTCHyp_seg4 hH_sqrt3 D.boundary D.boundary_eq hz_re hi_lo hi_hi)
    (fun θ₀ h_lo h_hi =>
      arcFTCHyp_arc_generic hH D.boundary D.boundary_eq h_lo h_hi)

/-! ### Fully unconditional FDWindingData from the FD boundary path -/

/-- Unconditional `FDWindingData H` using the canonical `fdBoundaryPC1Path`
and the three unconditional elliptic-point FTC providers. -/
def fdWindingData_unconditional {H : ℝ} (hH : 1 < H) : FDWindingData H := by
  have hH_sqrt3 : Real.sqrt 3 / 2 < H := by
    have h_sqrt3_lt : Real.sqrt 3 < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_nonneg 3]
    linarith
  let γ : PiecewiseC1Path (fdStart H) (fdStart H) := fdBoundaryPC1Path H hH_sqrt3
  have hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t :=
    fdBoundaryPC1Path_eq H hH_sqrt3
  refine {
    boundary := γ
    boundary_eq := hγ
    interior_winding := ?_
    winding_at_i := ?_
    winding_at_rho := ?_
    winding_at_rho_plus_one := ?_ }
  · intro z hz_norm hz_re hz_im_pos hz_im_lt
    exact fdBoundary_interior_winding_complete hH_sqrt3
      ⟨hz_norm, hz_re, hz_im_pos, hz_im_lt⟩ hγ
  · exact hasWindingNumber_atI_of_scd
      (singleCrossingData_atI_of_ftcHyp hH γ hγ (arcFTCHyp_atI hH hγ)) rfl
  · exact hasWindingNumber_atRho_of_cornerFtcHyp hH γ hγ
      (cornerFTCHyp_atRho hH hγ)
  · exact hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp hH γ hγ
      (cornerFTCHyp_atRhoPlusOne_unconditional hH hγ)

/-- Fully unconditional `FDWindingDataFull H` — no hypotheses beyond `1 < H`. -/
def fdWindingDataFull_unconditional {H : ℝ} (hH : 1 < H) : FDWindingDataFull H :=
  mkFDWindingDataFull_unconditional hH (fdWindingData_unconditional hH)

end
