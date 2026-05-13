# BoundaryWindingSeg1Proof.lean Inventory

### `def seg1Speed`
- **Type**: `(H : ℝ) : ℝ`
- **What**: Vertical speed on seg1 (right vertical edge): `K = 5·(H - √3/2)`.
- **How**: Direct definition.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `seg1Speed_pos`, `seg1T₀`, `fdBoundaryFun_seg1_im_speed`, `fdBoundaryFun_seg1_dist_eq`, `seg1Speed_mul_t₀`, `seg1Speed_mul_one_fifth_sub_t₀`, `seg1_near_of_linDelta`, `seg1_far_on_seg1`, `seg1_far_bound`, `smoothBoundaryData_seg1_of_ftcHyp`, plus all of `BoundaryWindingSeg4Proof.lean`
- **Visibility**: public
- **Lines**: 38-38
- **Notes**: None.

### `theorem seg1Speed_pos`
- **Type**: `{H} (hH : √3/2 < H) : 0 < seg1Speed H`
- **What**: Positivity of seg1 speed for valid heights.
- **How**: Unfold and `linarith`.
- **Hypotheses**: `√3/2 < H`.
- **Uses from project**: [`seg1Speed`]
- **Used by**: `seg1T₀_pos`, `fdBoundaryFun_seg1_dist_eq`, `seg1Speed_mul_t₀`, `seg1_near_of_linDelta`, `seg1_far_on_seg1`, `smoothBoundaryData_seg1_of_ftcHyp`
- **Visibility**: public
- **Lines**: 40-41
- **Notes**: None.

### `def seg1T₀`
- **Type**: `(H c : ℝ) : ℝ`
- **What**: Crossing parameter on seg1 for the point `1/2 + c·I`: `t₀ = (H - c) / seg1Speed H`.
- **How**: Direct definition.
- **Hypotheses**: None.
- **Uses from project**: [`seg1Speed`]
- **Used by**: `seg1T₀_pos`, `seg1T₀_lt_one_fifth`, `seg1T₀_mem_Ioo`, `fdBoundaryFun_seg1_dist_eq`, `seg1Speed_mul_t₀`, `seg1Speed_mul_one_fifth_sub_t₀`, `seg1_near_of_linDelta`, `seg1_far_on_seg1`, `seg1_far_bound`, `smoothBoundaryData_seg1_of_ftcHyp`
- **Visibility**: public
- **Lines**: 45-45
- **Notes**: None.

### `theorem seg1T₀_pos`
- **Type**: `{H c} (hH : √3/2 < H) (hc : c < H) : 0 < seg1T₀ H c`
- **What**: The seg1 crossing parameter is positive.
- **How**: `div_pos` with `seg1Speed_pos`.
- **Hypotheses**: `√3/2 < H`, `c < H`.
- **Uses from project**: [`seg1T₀`, `seg1Speed_pos`]
- **Used by**: `seg1T₀_mem_Ioo`, `smoothBoundaryData_seg1_of_ftcHyp`
- **Visibility**: public
- **Lines**: 47-49
- **Notes**: None.

### `theorem seg1T₀_lt_one_fifth`
- **Type**: `{H c} (hH : √3/2 < H) (hc : √3/2 < c) : seg1T₀ H c < 1/5`
- **What**: The seg1 crossing parameter lies strictly below `1/5`.
- **How**: `div_lt_iff₀` with positive denominator, then `linarith`.
- **Hypotheses**: `√3/2 < H`, `√3/2 < c`.
- **Uses from project**: [`seg1T₀`, `seg1Speed`]
- **Used by**: `seg1T₀_mem_Ioo`, `smoothBoundaryData_seg1_of_ftcHyp`
- **Visibility**: public
- **Lines**: 51-56
- **Notes**: None.

### `theorem seg1T₀_mem_Ioo`
- **Type**: `{H c} (hH) (hc_lo : √3/2 < c) (hc_hi : c < H) : seg1T₀ H c ∈ Ioo 0 1`
- **What**: Crossing parameter is strictly in `(0, 1)`.
- **How**: Combine `seg1T₀_pos` and `seg1T₀_lt_one_fifth` (which transits `<1`).
- **Hypotheses**: `√3/2 < H`, `√3/2 < c`, `c < H`.
- **Uses from project**: [`seg1T₀`, `seg1T₀_pos`, `seg1T₀_lt_one_fifth`]
- **Used by**: `smoothBoundaryData_seg1_of_ftcHyp`
- **Visibility**: public
- **Lines**: 58-62
- **Notes**: None.

### `private theorem fdBoundaryFun_seg1_im_speed`
- **Type**: `(H t) (ht : t ≤ 1/5) : (fdBoundaryFun H t).im = H - seg1Speed H · t`
- **What**: Imaginary-part formula for the FD boundary on seg1.
- **How**: Rewrite via `fdBoundaryFun_seg1_im`, then unfold `seg1Speed` and `ring`.
- **Hypotheses**: `t ≤ 1/5`.
- **Uses from project**: [`fdBoundaryFun`, `fdBoundaryFun_seg1_im`, `seg1Speed`]
- **Used by**: `fdBoundaryFun_seg1_dist_eq`
- **Visibility**: private
- **Lines**: 67-69
- **Notes**: None.

### `theorem fdBoundaryFun_seg1_dist_eq`
- **Type**: `{H} (hH) {z₀} (hz_re : z₀.re = 1/2) (t) (ht : t ≤ 1/5) : ‖fdBoundaryFun H t - z₀‖ = seg1Speed H · |t - seg1T₀ H z₀.im|`
- **What**: Distance from `fdBoundaryFun H t` to a seg1 point equals `seg1Speed H · |t - t₀|`.
- **How**: Real part vanishes via `fdBoundaryFun_seg1_re`; imaginary part is `seg1Speed H · (t₀ - t)` (via `seg1T₀` unfold and `field_simp`/`ring`); compute norm with `Complex.norm_def`+`normSq_apply`, then `Real.sqrt_sq_eq_abs`, `abs_mul`, and `abs_sub_comm`.
- **Hypotheses**: `√3/2 < H`, `z₀.re = 1/2`, `t ≤ 1/5`.
- **Uses from project**: [`fdBoundaryFun_seg1_re`, `fdBoundaryFun_seg1_im_speed`, `seg1Speed`, `seg1Speed_pos`, `seg1T₀`]
- **Used by**: `seg1_near_of_linDelta`, `seg1_far_on_seg1`
- **Visibility**: public
- **Lines**: 73-83
- **Notes**: 11 lines.

### `theorem seg1Speed_mul_t₀`
- **Type**: `{H c} (hH : √3/2 < H) : seg1Speed H · seg1T₀ H c = H - c`
- **What**: Algebraic identity recovering the height offset.
- **How**: `simp [seg1T₀, mul_div_cancel₀]` with `seg1Speed_pos.ne'`.
- **Hypotheses**: `√3/2 < H`.
- **Uses from project**: [`seg1T₀`, `seg1Speed_pos`]
- **Used by**: `seg1Speed_mul_one_fifth_sub_t₀`, `smoothBoundaryData_seg1_of_ftcHyp`
- **Visibility**: public
- **Lines**: 88-90
- **Notes**: None.

### `theorem seg1Speed_mul_one_fifth_sub_t₀`
- **Type**: `{H c} (hH : √3/2 < H) : seg1Speed H · (1/5 - seg1T₀ H c) = c - √3/2`
- **What**: Algebraic identity for the remaining seg1 span.
- **How**: `mul_sub`, then `seg1Speed_mul_t₀`, then `simp [seg1Speed]; ring`.
- **Hypotheses**: `√3/2 < H`.
- **Uses from project**: [`seg1Speed`, `seg1T₀`, `seg1Speed_mul_t₀`]
- **Used by**: `seg1_near_of_linDelta`, `smoothBoundaryData_seg1_of_ftcHyp`
- **Visibility**: public
- **Lines**: 93-95
- **Notes**: None.

### `theorem seg1_near_of_linDelta`
- **Type**: `{H} (hH) {z₀} (hz_re : z₀.re = 1/2) {ε} (hε_lo : ε < z₀.im - √3/2) {t} (ht : |t - seg1T₀ H z₀.im| ≤ ε / seg1Speed H) : ‖fdBoundaryFun H t - z₀‖ ≤ ε`
- **What**: Near bound: within ε/K of t₀ keeps the distance under ε.
- **How**: Derive `t ≤ 1/5` via `seg1Speed_mul_one_fifth_sub_t₀`, apply `fdBoundaryFun_seg1_dist_eq`, then `gcongr` + `field_simp`.
- **Hypotheses**: `√3/2 < H`, `z₀.re = 1/2`, `ε < z₀.im - √3/2`, param-distance bound.
- **Uses from project**: [`seg1Speed`, `seg1Speed_pos`, `seg1T₀`, `seg1Speed_mul_one_fifth_sub_t₀`, `fdBoundaryFun_seg1_dist_eq`]
- **Used by**: `smoothBoundaryData_seg1_of_ftcHyp`
- **Visibility**: public
- **Lines**: 99-110
- **Notes**: 12 lines.

### `theorem norm_gt_one_of_seg1_interior`
- **Type**: `{z₀} (hz_re : z₀.re = 1/2) (hc_lo : √3/2 < z₀.im) : 1 < ‖z₀‖`
- **What**: Seg1 interior point lies outside the unit disk.
- **How**: Expand `Complex.normSq` and use `Real.mul_self_sqrt`, finish with `nlinarith` using `Complex.normSq_eq_norm_sq` and norm nonnegativity.
- **Hypotheses**: `z₀.re = 1/2`, `√3/2 < z₀.im`.
- **Uses from project**: []
- **Used by**: `seg1_dist_arc`, `seg1Threshold_pos`
- **Visibility**: public
- **Lines**: 115-122
- **Notes**: None.

### `theorem seg1_dist_arc`
- **Type**: `{z₀} (hz_re) (hc_lo) {H t} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) : ‖z₀‖ - 1 ≤ ‖fdBoundaryFun H t - z₀‖`
- **What**: Distance from seg1 interior point to seg2/seg3 (arcs) is at least `‖z₀‖ - 1`.
- **How**: `fdBoundaryFun_arc_dist` combined with `norm_gt_one_of_seg1_interior`.
- **Hypotheses**: `z₀.re = 1/2`, `√3/2 < z₀.im`, `t ∈ (1/5, 3/5]`.
- **Uses from project**: [`fdBoundaryFun_arc_dist`, `norm_gt_one_of_seg1_interior`]
- **Used by**: `seg1_far_bound`
- **Visibility**: public
- **Lines**: 126-130
- **Notes**: None.

### `theorem seg1_dist_seg4`
- **Type**: `{z₀} (hz_re : z₀.re = 1/2) {H t} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) : 1 ≤ ‖fdBoundaryFun H t - z₀‖`
- **What**: Distance from a seg1 point to seg4 is at least 1.
- **How**: Real part of the difference is `-1`, so `Complex.abs_re_le_norm` gives the bound.
- **Hypotheses**: `z₀.re = 1/2`, `t ∈ (3/5, 4/5]`.
- **Uses from project**: [`fdBoundaryFun_seg4_re`]
- **Used by**: `seg1_far_bound`
- **Visibility**: public
- **Lines**: 133-139
- **Notes**: None.

### `theorem seg1_dist_seg5`
- **Type**: `{z₀} (hz_hi : z₀.im < H) {t} (ht : 4/5 < t) : H - z₀.im ≤ ‖fdBoundaryFun H t - z₀‖`
- **What**: Distance from a seg1 interior point to seg5 (top horizontal) is at least `H - z₀.im`.
- **How**: Delegates to `fdBoundaryFun_seg5_im_dist`.
- **Hypotheses**: `z₀.im < H`, `4/5 < t`.
- **Uses from project**: [`fdBoundaryFun_seg5_im_dist`]
- **Used by**: `seg1_far_bound`
- **Visibility**: public
- **Lines**: 142-144
- **Notes**: None.

### `theorem seg1_far_on_seg1`
- **Type**: `{H} (hH) {z₀} (hz_re) {ε t} (ht : t ≤ 1/5) (hδt : ε/seg1Speed H < |t - seg1T₀ H z₀.im|) : ε < ‖fdBoundaryFun H t - z₀‖`
- **What**: Far bound restricted to seg1: outside the δ-window, distance exceeds ε.
- **How**: `fdBoundaryFun_seg1_dist_eq` + `field_simp` + `gcongr` with `seg1Speed_pos`.
- **Hypotheses**: `√3/2 < H`, `z₀.re = 1/2`, `t ≤ 1/5`, δ-gap.
- **Uses from project**: [`seg1Speed`, `seg1Speed_pos`, `seg1T₀`, `fdBoundaryFun_seg1_dist_eq`]
- **Used by**: `seg1_far_bound`
- **Visibility**: public
- **Lines**: 150-157
- **Notes**: None.

### `theorem norm_sub_one_le_im_sub_sqrt3`
- **Type**: `{z₀} (hz_re : z₀.re = 1/2) (hc_lo : √3/2 ≤ z₀.im) : ‖z₀‖ - 1 ≤ z₀.im - √3/2`
- **What**: Arc-distance bound dominates the vertical-width bound on seg1.
- **How**: Show `‖z₀‖² ≤ (z₀.im + 1 - √3/2)²` via `normSq_apply` + `nlinarith`, then take square roots using `Real.sqrt_le_sqrt`/`Real.sqrt_sq`.
- **Hypotheses**: `z₀.re = 1/2`, `√3/2 ≤ z₀.im`.
- **Uses from project**: []
- **Used by**: `smoothBoundaryData_seg1_of_ftcHyp`
- **Visibility**: public
- **Lines**: 164-178
- **Notes**: 15 lines.

### `def seg1Threshold`
- **Type**: `(H : ℝ) (z₀ : ℂ) : ℝ`
- **What**: ε-threshold for seg1: `min(‖z₀‖ - 1, 1, H - z₀.im)`.
- **How**: Nested `min`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `seg1Threshold_pos`, `seg1_far_bound`, `smoothBoundaryData_seg1_of_ftcHyp`
- **Visibility**: public
- **Lines**: 186-187
- **Notes**: None.

### `theorem seg1Threshold_pos`
- **Type**: `{H z₀} (hz_re) (hc_lo) (hc_hi) : 0 < seg1Threshold H z₀`
- **What**: Threshold is positive at seg1 interior points.
- **How**: `lt_min` twice, using `norm_gt_one_of_seg1_interior` for the arc bound.
- **Hypotheses**: `z₀.re = 1/2`, `√3/2 < z₀.im < H`.
- **Uses from project**: [`seg1Threshold`, `norm_gt_one_of_seg1_interior`]
- **Used by**: `smoothBoundaryData_seg1_of_ftcHyp`
- **Visibility**: public
- **Lines**: 189-194
- **Notes**: None.

### `theorem seg1_far_bound`
- **Type**: `{H} (hH) {z₀} (hz_re) (hc_lo) (hc_hi) {ε} (hε_lt) {t} (_ht_mem : t ∈ Icc 0 1) (hδt) : ε < ‖fdBoundaryFun H t - z₀‖`
- **What**: Far bound across all five FD-boundary sub-segments.
- **How**: Extract three ε-comparisons from `seg1Threshold`, then `rcases` on `t` against `1/5, 3/5, 4/5` and dispatch to `seg1_far_on_seg1`, `seg1_dist_arc`, `seg1_dist_seg4`, `seg1_dist_seg5`.
- **Hypotheses**: Full seg1-interior assumptions, ε-threshold, δ-gap.
- **Uses from project**: [`seg1Threshold`, `seg1Speed`, `seg1T₀`, `seg1_far_on_seg1`, `seg1_dist_arc`, `seg1_dist_seg4`, `seg1_dist_seg5`]
- **Used by**: `smoothBoundaryData_seg1_of_ftcHyp`
- **Visibility**: public
- **Lines**: 200-218
- **Notes**: 19 lines.

### `def smoothBoundaryData_seg1_of_ftcHyp`
- **Type**: `{H} (hH) (γ) (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) {z₀} (hz_re : z₀.re = 1/2) (hc_lo) (hc_hi) (ftcHyp : ArcFTCHyp γ z₀ (seg1T₀ H z₀.im) (linDelta (seg1Speed H)) (seg1Threshold H z₀) (-(↑π·I))) : SmoothBoundaryWindingData γ z₀`
- **What**: Constructs `SmoothBoundaryWindingData` at a generic smooth seg1 point from an externally-supplied `ArcFTCHyp`.
- **How**: Assemble structure: `t₀ := seg1T₀`, `δ := linDelta (seg1Speed H)`, threshold via `seg1Threshold`; thresholds from `seg1Threshold_pos`/`linDelta_pos`; small-δ via `seg1Speed_mul_t₀`/`seg1Speed_mul_one_fifth_sub_t₀`; far bound via `seg1_far_bound`; near bound via `seg1_near_of_linDelta`; `ftcHyp` threaded through.
- **Hypotheses**: `√3/2 < H`, γ-extend equals `fdBoundaryFun` on `[0,1]`, seg1 interior conditions, external `ArcFTCHyp`.
- **Uses from project**: [`fdStart`, `PiecewiseC1Path`, `fdBoundaryFun`, `seg1T₀`, `seg1T₀_pos`, `seg1T₀_lt_one_fifth`, `seg1T₀_mem_Ioo`, `linDelta`, `linDelta_pos`, `seg1Speed`, `seg1Speed_pos`, `seg1Threshold`, `seg1Threshold_pos`, `seg1Speed_mul_t₀`, `seg1Speed_mul_one_fifth_sub_t₀`, `seg1_far_bound`, `seg1_near_of_linDelta`, `norm_sub_one_le_im_sub_sqrt3`, `ArcFTCHyp`, `SmoothBoundaryWindingData`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 224-266
- **Notes**: 43 lines; structure builder with many inline field proofs.

## File Summary
Provides the seg1 (right vertical edge) analogue of the seg4 setup: defines `seg1Speed`, crossing parameter `seg1T₀`, and the exact distance formula `‖γ(t) - z₀‖ = K|t - t₀|` on the seg1 portion of the FD boundary, then proves uniform off-seg1 distance bounds (arcs, seg4, seg5) and the combined `seg1_far_bound`. The main constructor `smoothBoundaryData_seg1_of_ftcHyp` packages everything into `SmoothBoundaryWindingData` for use by the smooth boundary winding proof, given the external `ArcFTCHyp` analytical input. Also supplies key reusable lemmas (`seg1Speed`, `seg1Speed_pos`, etc.) consumed by the symmetric seg4 file. No sorries, no axioms.
