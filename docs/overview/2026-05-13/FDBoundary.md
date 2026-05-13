# FDBoundary.lean — Inventory

### `def fdStart`
- **Type**: `(H : ℝ) : ℂ`
- **What**: The starting (and ending) point of the FD boundary contour at height `H`, namely `1/2 + Hi`.
- **How**: `1 / 2 + ↑H * I`.
- **Hypotheses**: real height `H`
- **Uses from project**: []
- **Used by**: `fdBoundaryFun_at_zero`, `fdBoundaryFun_at_one`, `fdBoundaryFun_closed`, `fdBoundaryPath`, `FDWindingData`, `FDWindingData.mk_of_crossing`
- **Visibility**: public
- **Lines**: 44
- **Notes**: noncomputable

### `def fdBoundaryFun`
- **Type**: `(H : ℝ) : ℝ → ℂ`
- **What**: The five-segment FD boundary as a function `ℝ → ℂ`, parameterized on `[0, 1]` with breakpoints at `1/5, 2/5, 3/5, 4/5`. Segments: right vertical, arc ρ+1 → i, arc i → ρ, left vertical, top horizontal.
- **How**: Iterated `if t ≤ k/5 then ... else ...` for `k = 1, 2, 3, 4`.
- **Hypotheses**: real height `H`
- **Uses from project**: []
- **Used by**: `fdBoundaryFun_at_zero/one_fifth/two_fifths/three_fifths/four_fifths/one`, `fdBoundaryFun_closed`, `fdBoundaryFun_eq_layered`, `fdBoundaryFun_continuous`, `fdBoundaryPath`, `FDWindingData.boundary_eq`, `fdBoundaryFun_seg1_re/im`, `fdBoundaryFun_seg4_re`, `fdBoundaryFun_seg5_im`, `fdBoundaryFun_arc_norm`, `FDWindingData.mk_of_crossing`
- **Visibility**: public
- **Lines**: 52-62
- **Notes**: noncomputable

### `theorem fdBoundaryFun_at_zero`
- **Type**: `(H : ℝ) : fdBoundaryFun H 0 = fdStart H`
- **What**: At `t = 0`, the boundary is at `1/2 + Hi`.
- **How**: Unfold via `simp only` with `(0 : ℝ) ≤ 1/5` then `push_cast; ring`.
- **Hypotheses**: real height `H`
- **Uses from project**: `fdBoundaryFun`, `fdStart`
- **Used by**: `fdBoundaryFun_closed`, `fdBoundaryPath`
- **Visibility**: public
- **Lines**: 66-70
- **Notes**: none

### `theorem fdBoundaryFun_at_one_fifth`
- **Type**: `(H : ℝ) : fdBoundaryFun H (1/5) = ellipticPointRhoPlusOne`
- **What**: At `t = 1/5`, the boundary is at `ρ+1`.
- **How**: `simp only` with `(1/5 : ℝ) ≤ 1/5` plus `ellipticPointRhoPlusOne` unfold and `push_cast; ring`.
- **Hypotheses**: real height `H`
- **Uses from project**: `fdBoundaryFun`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`, `UpperHalfPlane.coe_mk`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 72-77
- **Notes**: none

### `theorem fdBoundaryFun_at_two_fifths`
- **Type**: `(H : ℝ) : fdBoundaryFun H (2/5) = ellipticPointI`
- **What**: At `t = 2/5`, the boundary is at `i`.
- **How**: `simp only` to land in the `seg2` branch; rewrite the exponent as `↑(π/2) * I`; use `exp_mul_I`, `ofReal_cos/sin`, `Real.cos_pi_div_two`, `Real.sin_pi_div_two`; close with `norm_num`.
- **Hypotheses**: real height `H`
- **Uses from project**: `fdBoundaryFun`, `ellipticPointI`, `ellipticPointI'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 79-90
- **Notes**: none

### `theorem fdBoundaryFun_at_three_fifths`
- **Type**: `(H : ℝ) : fdBoundaryFun H (3/5) = ellipticPointRho`
- **What**: At `t = 3/5`, the boundary is at `ρ`.
- **How**: `simp only` to enter `seg3` branch; rewrite exponent as `↑(2π/3) * I`; expand `cos(π - π/3)` and `sin(π - π/3)`; close via `Real.cos_pi_sub/sin_pi_sub`, `cos/sin_pi_div_three`, `norm_num`.
- **Hypotheses**: real height `H`
- **Uses from project**: `fdBoundaryFun`, `ellipticPointRho`, `ellipticPointRho'`, `UpperHalfPlane.coe_mk`
- **Used by**: unused in file (matched by `fdBoundaryFun_inner345_cont` proof structurally)
- **Visibility**: public
- **Lines**: 92-106
- **Notes**: none

### `theorem fdBoundaryFun_at_four_fifths`
- **Type**: `(H : ℝ) : fdBoundaryFun H (4/5) = -1/2 + ↑H * I`
- **What**: At `t = 4/5`, the boundary is at `-1/2 + Hi`.
- **How**: `simp only` to enter seg 4 branch, `push_cast; ring`.
- **Hypotheses**: real height `H`
- **Uses from project**: `fdBoundaryFun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 108-115
- **Notes**: none

### `theorem fdBoundaryFun_at_one`
- **Type**: `(H : ℝ) : fdBoundaryFun H 1 = fdStart H`
- **What**: At `t = 1`, the boundary returns to `1/2 + Hi`.
- **How**: `simp only` excluding all early branches to land in seg 5; `push_cast; ring`.
- **Hypotheses**: real height `H`
- **Uses from project**: `fdBoundaryFun`, `fdStart`
- **Used by**: `fdBoundaryFun_closed`, `fdBoundaryPath`
- **Visibility**: public
- **Lines**: 117-124
- **Notes**: none

### `theorem fdBoundaryFun_closed`
- **Type**: `(H : ℝ) : fdBoundaryFun H 0 = fdBoundaryFun H 1`
- **What**: The boundary contour is closed (matches at endpoints).
- **How**: `fdBoundaryFun_at_zero` and `fdBoundaryFun_at_one` both equal `fdStart H`.
- **Hypotheses**: real height `H`
- **Uses from project**: `fdBoundaryFun_at_zero`, `fdBoundaryFun_at_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 127-129
- **Notes**: none

### `private lemma fdBoundaryFun_seg1_cont`
- **Type**: `(H : ℝ) : Continuous (fun t : ℝ => (1 : ℂ) / 2 + (↑H - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I)`
- **What**: Segment 1 (right vertical) as a function of `t` is continuous.
- **How**: Composition of `continuous_const`, `Complex.continuous_ofReal`, `.add/.sub/.mul`.
- **Hypotheses**: real height `H`
- **Uses from project**: []
- **Used by**: `fdBoundaryFun_continuous`
- **Visibility**: private
- **Lines**: 134-140
- **Notes**: none

### `private lemma fdBoundaryFun_seg2_cont`
- **Type**: `Continuous (fun t : ℝ => exp ((↑Real.pi / 3 + (5 * ↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I))`
- **What**: Segment 2 (arc ρ+1 → i) is continuous.
- **How**: `Complex.continuous_exp.comp` of a continuous polynomial in `↑t`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `fdBoundaryFun_inner2345_cont`
- **Visibility**: private
- **Lines**: 143-150
- **Notes**: none

### `private lemma fdBoundaryFun_seg3_cont`
- **Type**: `Continuous (fun t : ℝ => exp ((↑Real.pi / 2 + (5 * ↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I))`
- **What**: Segment 3 (arc i → ρ) is continuous.
- **How**: `Complex.continuous_exp.comp` of a continuous polynomial in `↑t`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `fdBoundaryFun_inner345_cont`
- **Visibility**: private
- **Lines**: 153-160
- **Notes**: none

### `private lemma fdBoundaryFun_seg4_cont`
- **Type**: `(H : ℝ) : Continuous (fun t : ℝ => (-1 : ℂ) / 2 + (↑(Real.sqrt 3) / 2 + (5 * ↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I)`
- **What**: Segment 4 (left vertical) is continuous.
- **How**: Composition of `continuous_const`, `Complex.continuous_ofReal`, `.add/.sub/.mul`.
- **Hypotheses**: real height `H`
- **Uses from project**: []
- **Used by**: `fdBoundaryFun_inner45_cont`
- **Visibility**: private
- **Lines**: 163-170
- **Notes**: none

### `private lemma fdBoundaryFun_seg5_cont`
- **Type**: `(H : ℝ) : Continuous (fun t : ℝ => (5 * ↑t - 9 / 2 : ℂ) + ↑H * I)`
- **What**: Segment 5 (top horizontal) is continuous.
- **How**: `((continuous_const.mul Complex.continuous_ofReal).sub continuous_const).add continuous_const`.
- **Hypotheses**: real height `H`
- **Uses from project**: []
- **Used by**: `fdBoundaryFun_inner45_cont`
- **Visibility**: private
- **Lines**: 173-175
- **Notes**: none

### `private def fdBoundaryFun_inner45`
- **Type**: `(H : ℝ) : ℝ → ℂ`
- **What**: Inner layering combining segments 4 and 5 of the boundary as one if-then-else expression.
- **How**: `if t ≤ 4/5 then ... else ...`.
- **Hypotheses**: real height `H`
- **Uses from project**: []
- **Used by**: `fdBoundaryFun_inner45_cont`, `fdBoundaryFun_inner345`, `fdBoundaryFun_eq_layered`
- **Visibility**: private
- **Lines**: 178-181
- **Notes**: none

### `private lemma fdBoundaryFun_inner45_cont`
- **Type**: `(H : ℝ) : Continuous (fdBoundaryFun_inner45 H)`
- **What**: The inner segments-4-5 layer is continuous.
- **How**: `Continuous.if_le` with `fdBoundaryFun_seg4_cont`, `fdBoundaryFun_seg5_cont`, plus a matching-at-`t = 4/5` step done by `subst ht; push_cast; ring`.
- **Hypotheses**: real height `H`
- **Uses from project**: `fdBoundaryFun_seg4_cont`, `fdBoundaryFun_seg5_cont`
- **Used by**: `fdBoundaryFun_inner345_cont`
- **Visibility**: private
- **Lines**: 183-189
- **Notes**: none

### `private def fdBoundaryFun_inner345`
- **Type**: `(H : ℝ) : ℝ → ℂ`
- **What**: Inner layering combining segments 3, 4, 5.
- **How**: `if t ≤ 3/5 then exp(...) else fdBoundaryFun_inner45 H t`.
- **Hypotheses**: real height `H`
- **Uses from project**: `fdBoundaryFun_inner45`
- **Used by**: `fdBoundaryFun_inner345_cont`, `fdBoundaryFun_inner2345`, `fdBoundaryFun_eq_layered`
- **Visibility**: private
- **Lines**: 192-195
- **Notes**: none

### `private lemma fdBoundaryFun_inner345_cont`
- **Type**: `(H : ℝ) : Continuous (fdBoundaryFun_inner345 H)`
- **What**: The inner segments-3-4-5 layer is continuous.
- **How**: `Continuous.if_le` with `fdBoundaryFun_seg3_cont` and `fdBoundaryFun_inner45_cont`, plus matching at `t = 3/5` via `exp(↑(2π/3) * I) = exp_mul_I` and `Real.cos_pi_sub/sin_pi_sub/cos_pi_div_three/sin_pi_div_three`, closed with `push_cast; ring`. 18-line proof; key lemmas `Continuous.if_le`, `exp_mul_I`, `Real.cos_pi_sub`, `Real.sin_pi_sub`.
- **Hypotheses**: real height `H`
- **Uses from project**: `fdBoundaryFun_seg3_cont`, `fdBoundaryFun_inner45_cont`, `fdBoundaryFun_inner45`
- **Used by**: `fdBoundaryFun_inner2345_cont`
- **Visibility**: private
- **Lines**: 197-216
- **Notes**: 20 lines

### `private def fdBoundaryFun_inner2345`
- **Type**: `(H : ℝ) : ℝ → ℂ`
- **What**: Inner layering combining segments 2, 3, 4, 5.
- **How**: `if t ≤ 2/5 then exp(...) else fdBoundaryFun_inner345 H t`.
- **Hypotheses**: real height `H`
- **Uses from project**: `fdBoundaryFun_inner345`
- **Used by**: `fdBoundaryFun_inner2345_cont`, `fdBoundaryFun_eq_layered`, `fdBoundaryFun_continuous`
- **Visibility**: private
- **Lines**: 219-222
- **Notes**: none

### `private lemma fdBoundaryFun_inner2345_cont`
- **Type**: `(H : ℝ) : Continuous (fdBoundaryFun_inner2345 H)`
- **What**: The inner segments-2-3-4-5 layer is continuous.
- **How**: `Continuous.if_le` with `fdBoundaryFun_seg2_cont` and `fdBoundaryFun_inner345_cont`; matching at `t = 2/5` by rewriting both exponents as `↑(π/2) * I` so they're equal. 19-line proof; key lemma `Continuous.if_le`.
- **Hypotheses**: real height `H`
- **Uses from project**: `fdBoundaryFun_seg2_cont`, `fdBoundaryFun_inner345_cont`, `fdBoundaryFun_inner345`, `fdBoundaryFun_inner2345`
- **Used by**: `fdBoundaryFun_eq_layered`, `fdBoundaryFun_continuous`
- **Visibility**: private
- **Lines**: 224-242
- **Notes**: 19 lines

### `private lemma fdBoundaryFun_eq_layered`
- **Type**: `(H : ℝ) (t : ℝ) : fdBoundaryFun H t = if t ≤ 1/5 then 1/2 + (↑H - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I else fdBoundaryFun_inner2345 H t`
- **What**: The boundary function can be rewritten as the seg-1 piece else the inner-2345 layer.
- **How**: `unfold` the four innermost definitions then `split_ifs <;> rfl`.
- **Hypotheses**: real height `H`, real `t`
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_inner2345`, `fdBoundaryFun_inner345`, `fdBoundaryFun_inner45`
- **Used by**: `fdBoundaryFun_continuous`
- **Visibility**: private
- **Lines**: 244-251
- **Notes**: none

### `theorem fdBoundaryFun_continuous`
- **Type**: `(H : ℝ) : Continuous (fdBoundaryFun H)`
- **What**: The full FD boundary `fdBoundaryFun H` is continuous as a function `ℝ → ℂ`.
- **How**: `funext` and apply `fdBoundaryFun_eq_layered`, then `Continuous.if_le` with `fdBoundaryFun_seg1_cont` and `fdBoundaryFun_inner2345_cont`; matching at `t = 1/5` rewrites the exponent as `↑(π/3) * I` and applies `exp_mul_I`, `Real.cos_pi_div_three`, `Real.sin_pi_div_three`, closed with `push_cast; ring`. 23-line proof.
- **Hypotheses**: real height `H`
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_eq_layered`, `fdBoundaryFun_seg1_cont`, `fdBoundaryFun_inner2345_cont`, `fdBoundaryFun_inner2345`
- **Used by**: `fdBoundaryPath`
- **Visibility**: public
- **Lines**: 254-277
- **Notes**: 24-line proof

### `def fdBoundaryPath`
- **Type**: `(H : ℝ) : Path (fdStart H) (fdStart H)`
- **What**: The FD boundary as a `Path` from `fdStart H` to itself.
- **How**: `toFun = fdBoundaryFun H`; continuity from `fdBoundaryFun_continuous`; `source'`/`target'` from `fdBoundaryFun_at_zero/one`.
- **Hypotheses**: real height `H`
- **Uses from project**: `fdStart`, `fdBoundaryFun`, `fdBoundaryFun_continuous`, `fdBoundaryFun_at_zero`, `fdBoundaryFun_at_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 282-290
- **Notes**: none

### `def fdBoundaryPartition`
- **Type**: `Finset ℝ`
- **What**: The four segment junction points `{1/5, 2/5, 3/5, 4/5}`.
- **How**: `{1/5, 2/5, 3/5, 4/5}`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `fdBoundaryPartition_subset_Ioo`
- **Visibility**: public
- **Lines**: 295
- **Notes**: none

### `theorem fdBoundaryPartition_subset_Ioo`
- **Type**: `(fdBoundaryPartition : Set ℝ) ⊆ Ioo 0 1`
- **What**: All partition points are in the open interval `(0, 1)`.
- **How**: `simp only` reductions, case-split on membership, `subst` and `norm_num`.
- **Hypotheses**: none
- **Uses from project**: `fdBoundaryPartition`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 297-304
- **Notes**: none

### `structure FDWindingData`
- **Type**: `(H : ℝ)`
- **What**: Bundle for the valence formula: the FD boundary as `PiecewiseC1Path`, agreement with `fdBoundaryFun`, and four winding-number certificates — `-1` interior, `-1/2` at `i`, `-1/6` at `ρ` and at `ρ+1`.
- **How**: structure with fields `boundary`, `boundary_eq`, `interior_winding`, `winding_at_i`, `winding_at_rho`, `winding_at_rho_plus_one`.
- **Hypotheses**: real height `H`
- **Uses from project**: `fdStart`, `fdBoundaryFun`, `HasGeneralizedWindingNumber`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, `PiecewiseC1Path`
- **Used by**: `FDWindingData.mk_of_crossing`
- **Visibility**: public
- **Lines**: 316-330
- **Notes**: none

### `theorem fdBoundaryFun_seg1_re`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ≤ 1/5) : (fdBoundaryFun H t).re = 1/2`
- **What**: On segment 1, the real part is constant `1/2`.
- **How**: `simp only [fdBoundaryFun, ht, ite_true]` then `simp` over component projections.
- **Hypotheses**: `t ≤ 1/5`
- **Uses from project**: `fdBoundaryFun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 335-338
- **Notes**: none

### `theorem fdBoundaryFun_seg4_re`
- **Type**: `(H : ℝ) (t : ℝ) (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) : (fdBoundaryFun H t).re = -1/2`
- **What**: On segment 4, the real part is constant `-1/2`.
- **How**: Excluded earlier branches via `linarith`, then `simp` over component projections.
- **Hypotheses**: `3/5 < t ≤ 4/5`
- **Uses from project**: `fdBoundaryFun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 341-347
- **Notes**: none

### `theorem fdBoundaryFun_seg5_im`
- **Type**: `(H : ℝ) (t : ℝ) (ht : 4/5 < t) : (fdBoundaryFun H t).im = H`
- **What**: On segment 5, the imaginary part is constant `H`.
- **How**: Excluded earlier branches, `simp` over component projections.
- **Hypotheses**: `4/5 < t`
- **Uses from project**: `fdBoundaryFun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 350-355
- **Notes**: none

### `theorem fdBoundaryFun_arc_norm`
- **Type**: `(H : ℝ) (t : ℝ) (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) : ‖fdBoundaryFun H t‖ = 1`
- **What**: Both arc segments (2 and 3) lie on the unit circle.
- **How**: Case `t ≤ 2/5` or not. In each case, rewrite the exponent as `↑(real polynomial) * I` and apply `Complex.norm_exp_ofReal_mul_I _`.
- **Hypotheses**: `1/5 < t ≤ 3/5`
- **Uses from project**: `fdBoundaryFun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 358-376
- **Notes**: 19 lines

### `theorem fdBoundaryFun_seg1_im`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ≤ 1/5) : (fdBoundaryFun H t).im = H - 5 * t * (H - Real.sqrt 3 / 2)`
- **What**: On segment 1, the imaginary part interpolates linearly between `H` and `√3/2`.
- **How**: `simp only [fdBoundaryFun, ht, ite_true]` then `simp` over component projections.
- **Hypotheses**: `t ≤ 1/5`
- **Uses from project**: `fdBoundaryFun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 379-382
- **Notes**: none

### `def fdHeightValid`
- **Type**: `(H : ℝ) : Prop`
- **What**: A height `H` is valid (for a well-formed FD boundary) iff `√3/2 < H`.
- **How**: `Real.sqrt 3 / 2 < H`.
- **Hypotheses**: real height `H`
- **Uses from project**: []
- **Used by**: `fdHeightValid_of_one_lt`
- **Visibility**: public
- **Lines**: 385
- **Notes**: none

### `theorem fdHeightValid_of_one_lt`
- **Type**: `(H : ℝ) (hH : 1 < H) : fdHeightValid H`
- **What**: If `H > 1` then `H` is a valid height for the FD boundary.
- **How**: `Real.sqrt 3 < 2` from `Real.sqrt_lt'`, then `linarith`.
- **Hypotheses**: `1 < H`
- **Uses from project**: `fdHeightValid`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 387-390
- **Notes**: none

### `private lemma pi_div_two_pi`
- **Type**: `-(↑Real.pi * I) / (2 * ↑Real.pi * I) = (-1 : ℂ) / 2`
- **What**: The complex identity `-πi / (2πi) = -1/2`.
- **How**: `field_simp` after establishing `π ≠ 0` and `I ≠ 0`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `FDWindingData.mk_of_crossing`
- **Visibility**: private
- **Lines**: 401-404
- **Notes**: none

### `private lemma pi_third_div_two_pi`
- **Type**: `-(↑Real.pi / 3 * I) / (2 * ↑Real.pi * I) = (-1 : ℂ) / 6`
- **What**: The complex identity `-(π/3)i / (2πi) = -1/6`.
- **How**: `field_simp` after establishing `π ≠ 0` and `I ≠ 0`, then `ring`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `FDWindingData.mk_of_crossing`
- **Visibility**: private
- **Lines**: 406-411
- **Notes**: none

### `def FDWindingData.mk_of_crossing`
- **Type**: `{H : ℝ} (boundary : PiecewiseC1Path (fdStart H) (fdStart H)) (hbdy : ∀ t ∈ Icc 0 1, boundary.toPath.extend t = fdBoundaryFun H t) (h_int : ∀ z, ‖z‖ > 1 → |z.re| < 1/2 → z.im > 0 → z.im < H → HasGeneralizedWindingNumber boundary z (-1)) (D_i : SingleCrossingData boundary I) (hL_i : D_i.L = -(↑Real.pi * I)) (D_rho : SingleCrossingData boundary ellipticPointRho) (hL_rho : D_rho.L = -(↑Real.pi / 3 * I)) (D_rho1 : SingleCrossingData boundary ellipticPointRhoPlusOne) (hL_rho1 : D_rho1.L = -(↑Real.pi / 3 * I)) : FDWindingData H`
- **What**: Constructor for `FDWindingData` from `SingleCrossingData` instances at `i`, `ρ`, `ρ+1`, plus an interior winding hypothesis. Combines each crossing's `hasWindingNumber` with the appropriate `L`-to-winding identity (`pi_div_two_pi` or `pi_third_div_two_pi`).
- **How**: Each `winding_at_*` field is filled by taking `D_*.hasWindingNumber`, rewriting `D_*.L = ...` and applying `pi_div_two_pi` or `pi_third_div_two_pi` via `rwa`.
- **Hypotheses**: `boundary` (piecewise-C1 closed path), agreement with `fdBoundaryFun`, interior winding hypothesis, three `SingleCrossingData` instances with prescribed `L` values
- **Uses from project**: `FDWindingData`, `fdStart`, `fdBoundaryFun`, `HasGeneralizedWindingNumber`, `SingleCrossingData`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, `pi_div_two_pi`, `pi_third_div_two_pi`, `PiecewiseC1Path`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 423-446
- **Notes**: 24 lines

## File Summary

- **Total declarations**: 32 (3 defs, 1 structure, 18 theorems, 10 private lemmas/defs)
- **Purpose**: Defines the **standard 5-segment FD boundary contour** `fdBoundaryFun` at height `H`, proves it is continuous and closed, packages it as a `Path`, and provides the `FDWindingData` structure plus a constructor from single-crossing data. Also computes geometric facts about each segment (real/imaginary parts, unit-circle norm).
- **Imports used**: `SingleCrossing` (for `SingleCrossingData`), `EllipticPoints` (for `ellipticPointI/Rho/RhoPlusOne` and their primed UHP versions)
- **External dependencies**: `Path`, `PiecewiseC1Path`, `HasGeneralizedWindingNumber`, `Complex.continuous_ofReal`, `Complex.continuous_exp`, `Continuous.if_le`, `exp_mul_I`, `Real.cos_pi_div_*`, `Real.sin_pi_div_*`
- **No sorries, no axioms, no `set_option`**.
- **Architecture**: The boundary is defined as a 4-fold nested `if-then-else`; continuity is established by a layered approach (`inner45 → inner345 → inner2345 → full`) using `Continuous.if_le` and matching of trigonometric values at each junction. Then `fdBoundaryPath` packages the path; geometric lemmas extract per-segment properties; `FDWindingData` and its constructor bridge winding data to the valence formula.
