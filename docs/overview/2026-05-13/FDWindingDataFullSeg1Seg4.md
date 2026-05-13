# FDWindingDataFullSeg1Seg4.lean — Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/FDWindingDataFullSeg1Seg4.lean`
Lines: 140

## lemma/`sqrt_three_div_two_lt_of_one_lt` (private)
- **Type**: `{H : ℝ} → 1 < H → Real.sqrt 3 / 2 < H`
- **What**: Numeric helper: `√3/2 < H` whenever `1 < H`.
- **How**: `nlinarith` with `Real.sq_sqrt` (`0 ≤ 3`) and `Real.sqrt_nonneg`.
- **Hypotheses**: `1 < H`.
- **Uses-from-project**: None (mathlib only).
- **Used by**: `mkFDWindingDataFull_seg1seg4_unconditional`, `mkFDWindingDataFull_unconditional`, `fdWindingData_unconditional` (this file).
- **Visibility**: private
- **Lines**: 42–43

## def/`mkFDWindingDataFull_seg1seg4_unconditional`
- **Type**: `{H : ℝ} → 1 < H → (D : FDWindingData H) → (ftc_arc : ∀ θ₀, π/3 < θ₀ < 2π/3 → ArcFTCHyp …) → FDWindingDataFull H`
- **What**: Legacy constructor — fills the seg1 and seg4 arc FTC providers unconditionally; user must still supply the generic arc FTC provider.
- **How**: Calls `mkFDWindingDataFull_of_ftcProviders` with `arcFTCHyp_seg1` and `arcFTCHyp_seg4` (from `Seg1FTCProvider`/`Seg4FTCProvider`); arc FTC is passed through as the supplied hypothesis.
- **Hypotheses**: `1 < H`; supplied `ftc_arc`.
- **Uses-from-project**: `FDWindingData`, `FDWindingDataFull`, `mkFDWindingDataFull_of_ftcProviders`, `arcFTCHyp_seg1`, `arcFTCHyp_seg4`, `ArcFTCHyp`, `arcT₀`, `arcsinDelta`, `arcThreshold`.
- **Used by**: User-facing legacy callers needing custom arc FTC.
- **Visibility**: public
- **Lines**: 47–59

## def/`mkFDWindingDataFull_unconditional`
- **Type**: `{H : ℝ} → 1 < H → (D : FDWindingData H) → FDWindingDataFull H`
- **What**: Constructor where all three FTC providers (seg1, seg4, arc) are filled in unconditionally; user supplies only `D : FDWindingData H`.
- **How**: `mkFDWindingDataFull_of_ftcProviders` with `arcFTCHyp_seg1`, `arcFTCHyp_seg4`, and `arcFTCHyp_arc_generic`; the `√3/2 < H` precondition is derived via `sqrt_three_div_two_lt_of_one_lt`.
- **Hypotheses**: `1 < H` only.
- **Uses-from-project**: `FDWindingData`, `FDWindingDataFull`, `mkFDWindingDataFull_of_ftcProviders`, `arcFTCHyp_seg1`, `arcFTCHyp_seg4`, `arcFTCHyp_arc_generic`.
- **Used by**: `fdWindingDataFull_unconditional` (this file).
- **Visibility**: public
- **Lines**: 63–72

## def/`fdWindingData_unconditional`
- **Type**: `{H : ℝ} → 1 < H → FDWindingData H`
- **What**: Builds the geometric `FDWindingData H` record from scratch (no externally supplied path) using the canonical `fdBoundaryPC1Path`.
- **How**: Record literal: `boundary := fdBoundaryPC1Path H hH_sqrt3`; `interior_winding := fdBoundary_interior_winding_complete`; the three crossing fields are filled with `hasWindingNumber_atI_of_scd` (with `arcFTCHyp_atI`+`singleCrossingData_atI_of_ftcHyp`), `hasWindingNumber_atRho_of_cornerFtcHyp` (with `cornerFTCHyp_atRho`), and `hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp` (with `cornerFTCHyp_atRhoPlusOne_unconditional`).
- **Hypotheses**: `1 < H` only.
- **Uses-from-project**: `fdBoundaryPC1Path`, `fdBoundaryPC1Path_eq`, `fdBoundary_interior_winding_complete`, `hasWindingNumber_atI_of_scd`, `singleCrossingData_atI_of_ftcHyp`, `arcFTCHyp_atI`, `hasWindingNumber_atRho_of_cornerFtcHyp`, `cornerFTCHyp_atRho`, `hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp`, `cornerFTCHyp_atRhoPlusOne_unconditional`, `FDWindingData`.
- **Used by**: `fdWindingDataFull_unconditional`, `valence_formula_unconditional_mkD` (this file).
- **Visibility**: public
- **Lines**: 78–93

## def/`fdWindingDataFull_unconditional`
- **Type**: `{H : ℝ} → 1 < H → FDWindingDataFull H`
- **What**: Top-level unconditional FD winding data record; combines `fdWindingData_unconditional` with all three FTC providers.
- **How**: `mkFDWindingDataFull_unconditional hH (fdWindingData_unconditional hH)`.
- **Hypotheses**: `1 < H`.
- **Uses-from-project**: `mkFDWindingDataFull_unconditional`, `fdWindingData_unconditional`, `FDWindingDataFull`.
- **Used by**: `valence_formula_unconditional_mkD` (this file).
- **Visibility**: public
- **Lines**: 96–97

## theorem/`valence_formula_unconditional_mkD`
- **Type**: For `f : ModularForm (Gamma 1) k`, `S : Finset UpperHalfPlane` with completeness, plus residue-side and modular-side `Tendsto` hypotheses, concludes the valence formula `orderAtCusp' f + (1/2)·ord(f,i) + (1/3)·ord(f,ρ) + Σ (other orbit terms) = k/12`.
- **What**: Top-level **fully unconditional in `mkD`** valence formula — `fdWindingDataFull` is supplied by `fdWindingDataFull_unconditional`, leaving only residue-side and modular-side Tendsto hypotheses.
- **How**: Direct call to `valence_formula_of_two_sides_Hgt1` with `mkD := (fun _ => fdWindingDataFull_unconditional)`.
- **Hypotheses**: `f` is a level-one weight-`k` modular form; `S ⊆ 𝒟`; `S` is complete in the sense `orderOfVanishingAt' f p ≠ 0 → p ∈ S`; height bound `∀ s ∈ S, (s : ℂ).im < H_S`; residue-side Tendsto on `[H_res, ∞)`; modular-side Tendsto on `[H_mod, ∞)`.
- **Uses-from-project**: `valence_formula_of_two_sides_Hgt1`, `fdWindingDataFull_unconditional`, `orderAtCusp'`, `orderOfVanishingAt'`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `sLeftVertFM`, `generalizedWindingNumber`, `𝒟`.
- **Used by**: Top-level callers (none in this file — this is the public API endpoint).
- **Visibility**: public
- **Lines**: 107–138

## File Summary
Top-level "fully unconditional" assembly for the valence formula. Builds `FDWindingData H` and `FDWindingDataFull H` directly from `1 < H` by plugging in three unconditional FTC providers (seg1, seg4, arc-generic) and three unconditional corner/arc FTC packages for the elliptic crossings. The headline result `valence_formula_unconditional_mkD` instantiates `valence_formula_of_two_sides_Hgt1` with these providers, leaving only the residue-side and modular-side Tendsto hypotheses for the user.
