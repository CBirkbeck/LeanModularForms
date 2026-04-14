/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDWindingDataFullAssembly
import LeanModularForms.ForMathlib.Seg1FTCProvider
import LeanModularForms.ForMathlib.Seg4FTCProvider

/-!
# `FDWindingDataFull` from seg1 and seg4 FTC providers (arc still as hypothesis)

This file plugs the now-unconditional seg1 and seg4 FTC providers into
`mkFDWindingDataFull_of_ftcProviders`, leaving only the arc FTC provider
as a hypothesis. Once `arcFTCHyp_arc` is also unconditional, this becomes
a fully unconditional `FDWindingDataFull` constructor.

## Main results

* `mkFDWindingDataFull_seg1seg4_unconditional` — `FDWindingDataFull` from
  `FDWindingData` and an arc FTC provider; seg1 and seg4 are filled in
  from the unconditional constructors.
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

end
