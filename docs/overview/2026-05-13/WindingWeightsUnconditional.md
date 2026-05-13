# WindingWeightsUnconditional.lean — Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/WindingWeightsUnconditional.lean`
Lines: 147

## def/`arcDelta`
- **Type**: `ℝ → ℝ`
- **What**: Cutoff function `δ(ε) = 6ε/(5π)` inverting the half-angle formula for the arc near bound at `i`.
- **How**: Direct definition `6 * ε / (5 * Real.pi)`.
- **Hypotheses**: None (totalised).
- **Uses-from-project**: None.
- **Used by**: `arcDelta_pos`, `arcDelta_lt_one_fifth`, `half_angle_factor`, `arc_near_at_I` (this file); arc FTC providers downstream.
- **Visibility**: public
- **Lines**: 44
- **Notes**: For the *far* bound the exact delta is `12·arcsin(ε/2)/(5π)`; this near-bound version uses `|sin x| ≤ |x|`.

## theorem/`arcDelta_pos`
- **Type**: `{ε : ℝ} → 0 < ε → 0 < arcDelta ε`
- **What**: Positivity of the cutoff.
- **How**: `unfold arcDelta; positivity`.
- **Hypotheses**: `0 < ε`.
- **Uses-from-project**: `arcDelta`.
- **Used by**: arc FTC providers downstream.
- **Visibility**: public
- **Lines**: 46–48

## theorem/`arcDelta_lt_one_fifth`
- **Type**: `{ε : ℝ} → ε < 1/2 → arcDelta ε < 1/5`
- **What**: Quantitative bound — for small ε the cutoff is below `1/5` (keeping `t` away from segment-1/segment-3 endpoints).
- **How**: `unfold arcDelta`; rewrite `1/5 = π/(5π)` and divide using `Real.pi_gt_three`.
- **Hypotheses**: `ε < 1/2`.
- **Uses-from-project**: `arcDelta`.
- **Used by**: `arc_near_at_I` (this file).
- **Visibility**: public
- **Lines**: 50–55

## theorem/`half_angle_factor`
- **Type**: `(ε : ℝ) → 5 * π / 12 * arcDelta ε = ε / 2`
- **What**: Algebraic identity used to convert the angle bound into a half-distance bound for the arc.
- **How**: `unfold arcDelta; field_simp; ring`.
- **Hypotheses**: None.
- **Uses-from-project**: `arcDelta`.
- **Used by**: `arc_near_at_I` (this file).
- **Visibility**: public
- **Lines**: 57–61

## theorem/`arc_near_at_I`
- **Type**: `(H : ℝ) {ε : ℝ} → ε < 1/2 → {t : ℝ} → |t - 2/5| ≤ arcDelta ε → ‖fdBoundaryFun H t - I‖ ≤ ε`
- **What**: Near bound: on the unit-circle arc the distance to `i` is at most `ε` when `t` lies within `arcDelta ε` of `2/5`.
- **How**: Combines `fdBoundaryFun_arc_dist_I` (half-angle distance formula) with `Real.abs_sin_le_abs` and `half_angle_factor`; uses `arcDelta_lt_one_fifth` to stay inside seg2.
- **Hypotheses**: `ε < 1/2`, `|t - 2/5| ≤ arcDelta ε`.
- **Uses-from-project**: `fdBoundaryFun`, `fdBoundaryFun_arc_dist_I`, `fdArcAngle`, `arcDelta`, `arcDelta_lt_one_fifth`, `half_angle_factor`.
- **Used by**: arc FTC provider machinery for `i` crossing.
- **Visibility**: public
- **Lines**: 67–90

## theorem/`hasWindingNumber_atI_of_scd`
- **Type**: `{γ : PiecewiseC1Path x y} → (D : SingleCrossingData γ I) → D.L = -(↑π * I) → HasGeneralizedWindingNumber γ I (-1/2)`
- **What**: Converts a `SingleCrossingData` at `i` with limit `-(πi)` into a winding number of `-1/2`.
- **How**: `convert D.hasWindingNumber using 1`; rewrite `hL`; `field_simp`.
- **Hypotheses**: `D.L = -(↑π * I)`.
- **Uses-from-project**: `SingleCrossingData`, `HasGeneralizedWindingNumber`.
- **Used by**: `fdWindingData_of_singleCrossingData` (this file); `fdWindingData_unconditional` (`FDWindingDataFullSeg1Seg4.lean`).
- **Visibility**: public
- **Lines**: 95–101

## theorem/`hasWindingNumber_atRho_of_scd`
- **Type**: `{γ : PiecewiseC1Path x y} → (D : SingleCrossingData γ ellipticPointRho) → D.L = -(↑π / 3 * I) → HasGeneralizedWindingNumber γ ellipticPointRho (-1/6)`
- **What**: Converts a `SingleCrossingData` at `ρ` with limit `-(πi/3)` into a winding number of `-1/6`.
- **How**: `convert D.hasWindingNumber using 1`; `rw [hL]; field_simp; ring`.
- **Hypotheses**: `D.L = -(↑π / 3 * I)`.
- **Uses-from-project**: `SingleCrossingData`, `ellipticPointRho`, `HasGeneralizedWindingNumber`.
- **Used by**: `fdWindingData_of_singleCrossingData` (this file).
- **Visibility**: public
- **Lines**: 104–111

## theorem/`hasWindingNumber_atRhoPlusOne_of_scd`
- **Type**: `{γ : PiecewiseC1Path x y} → (D : SingleCrossingData γ ellipticPointRhoPlusOne) → D.L = -(↑π / 3 * I) → HasGeneralizedWindingNumber γ ellipticPointRhoPlusOne (-1/6)`
- **What**: Same as the `ρ` case but at the T-translate `ρ+1`.
- **How**: `convert D.hasWindingNumber using 1`; `rw [hL]; field_simp; ring`.
- **Hypotheses**: `D.L = -(↑π / 3 * I)`.
- **Uses-from-project**: `SingleCrossingData`, `ellipticPointRhoPlusOne`, `HasGeneralizedWindingNumber`.
- **Used by**: `fdWindingData_of_singleCrossingData` (this file).
- **Visibility**: public
- **Lines**: 114–121

## def/`fdWindingData_of_singleCrossingData`
- **Type**: `{H : ℝ} → (γ : PiecewiseC1Path (fdStart H) (fdStart H)) → … → SingleCrossingData γ I → … → SingleCrossingData γ ellipticPointRho → … → SingleCrossingData γ ellipticPointRhoPlusOne → … → FDWindingData H`
- **What**: Assembles the full `FDWindingData H` record from three `SingleCrossingData` instances (i, ρ, ρ+1) plus the interior winding hypothesis.
- **How**: Record literal; each `winding_at_*` field is filled by the corresponding `hasWindingNumber_at*_of_scd` lemma; `interior_winding` is the supplied hypothesis.
- **Hypotheses**: `γ` agrees with `fdBoundaryFun H` on `Icc 0 1`; `h_int` (interior winding `-1`); three `SingleCrossingData` + `L` equality hypotheses.
- **Uses-from-project**: `FDWindingData`, `fdStart`, `fdBoundaryFun`, `SingleCrossingData`, `hasWindingNumber_atI_of_scd`, `hasWindingNumber_atRho_of_scd`, `hasWindingNumber_atRhoPlusOne_of_scd`.
- **Used by**: `FDWindingDataFullSeg1Seg4.lean` (downstream unconditional assembly).
- **Visibility**: public
- **Lines**: 131–145

## File Summary
Top-level assembler converting three `SingleCrossingData` packages into `FDWindingData H`. Provides the cutoff function `arcDelta` and the near distance bound `arc_near_at_I` used by the arc FTC provider at `i`. Three thin wrappers compute winding numbers `-1/2` at `i` and `-1/6` at `ρ`, `ρ+1` from a single limit value. The constructor `fdWindingData_of_singleCrossingData` is consumed by the fully-unconditional pipeline in `FDWindingDataFullSeg1Seg4.lean`.
