# BoundaryWindingSeg4Proof.lean Inventory

### `def seg4T₀`
- **Type**: `(H c : ℝ) : ℝ`
- **What**: Crossing parameter on seg4 (left vertical edge) for the point `-1/2 + c·I`: `t₀ = 3/5 + (c - √3/2)/seg1Speed H`.
- **How**: Arithmetic definition.
- **Hypotheses**: None.
- **Uses from project**: [`seg1Speed`]
- **Used by**: `seg4T₀_gt_three_fifths`, `seg4T₀_lt_four_fifths`, `seg4T₀_mem_Ioo`, `fdBoundaryFun_seg4_dist_eq`, `seg1Speed_mul_t₀_sub_three_fifths`, `seg1Speed_mul_four_fifths_sub_t₀`, `seg4_near_of_linDelta`, `seg4_far_on_seg4`, `seg4_far_bound`, `smoothBoundaryData_seg4_of_ftcHyp`
- **Visibility**: public
- **Lines**: 30-30
- **Notes**: None.

### `theorem seg4T₀_gt_three_fifths`
- **Type**: `{H c} (hH : √3/2 < H) (hc : √3/2 < c) : 3/5 < seg4T₀ H c`
- **What**: For interior `c > √3/2`, the crossing parameter strictly exceeds `3/5`.
- **How**: `div_pos` + `linarith` after unfolding.
- **Hypotheses**: `√3/2 < H`, `√3/2 < c`.
- **Uses from project**: [`seg4T₀`, `seg1Speed_pos`]
- **Used by**: `seg4T₀_mem_Ioo`
- **Visibility**: public
- **Lines**: 32-37
- **Notes**: None.

### `theorem seg4T₀_lt_four_fifths`
- **Type**: `{H c} (hH : √3/2 < H) (hc : c < H) : seg4T₀ H c < 4/5`
- **What**: For `c < H`, the crossing parameter is below `4/5`.
- **How**: `div_lt_iff₀ seg1Speed_pos` reduces to a `linarith` after unfolding `seg1Speed`.
- **Hypotheses**: `√3/2 < H`, `c < H`.
- **Uses from project**: [`seg4T₀`, `seg1Speed`, `seg1Speed_pos`]
- **Used by**: `seg4T₀_mem_Ioo`, `smoothBoundaryData_seg4_of_ftcHyp`
- **Visibility**: public
- **Lines**: 39-46
- **Notes**: None.

### `theorem seg4T₀_mem_Ioo`
- **Type**: `{H c} (hH : √3/2 < H) (hc_lo : √3/2 < c) (hc_hi : c < H) : seg4T₀ H c ∈ Ioo 0 1`
- **What**: The seg4 crossing parameter is strictly in `(0,1)`.
- **How**: Combines `seg4T₀_gt_three_fifths` and `seg4T₀_lt_four_fifths`.
- **Hypotheses**: `√3/2 < H`, `√3/2 < c`, `c < H`.
- **Uses from project**: [`seg4T₀`, `seg4T₀_gt_three_fifths`, `seg4T₀_lt_four_fifths`]
- **Used by**: `smoothBoundaryData_seg4_of_ftcHyp`
- **Visibility**: public
- **Lines**: 48-52
- **Notes**: None.

### `private theorem fdBoundaryFun_seg4_im_speed`
- **Type**: `(H t : ℝ) (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) : (fdBoundaryFun H t).im = √3/2 + seg1Speed H · (t - 3/5)`
- **What**: Imaginary-part formula for the FD boundary curve on seg4.
- **How**: Unfolds `fdBoundaryFun` via the matching `if` branch (showing the prior branches fail by `linarith`), then `simp` reduces complex arithmetic, finishes with `ring`.
- **Hypotheses**: `3/5 < t`, `t ≤ 4/5`.
- **Uses from project**: [`fdBoundaryFun`, `seg1Speed`]
- **Used by**: `fdBoundaryFun_seg4_dist_eq`
- **Visibility**: private
- **Lines**: 58-68
- **Notes**: 11 lines.

### `theorem fdBoundaryFun_seg4_dist_eq`
- **Type**: `{H} (hH : √3/2 < H) {z₀} (hz_re : z₀.re = -1/2) {t} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) : ‖fdBoundaryFun H t - z₀‖ = seg1Speed H · |t - seg4T₀ H z₀.im|`
- **What**: Distance from `fdBoundaryFun H t` to a seg4 point `z₀` equals `seg1Speed H` times the absolute parameter offset.
- **How**: Reduce real part to zero via `fdBoundaryFun_seg4_re`, express imaginary part using `fdBoundaryFun_seg4_im_speed`, then compute the norm by `Complex.norm_def`+`Complex.normSq_apply`, finally `Real.sqrt_sq_eq_abs` + `abs_mul`.
- **Hypotheses**: `√3/2 < H`, `z₀.re = -1/2`, `3/5 < t ≤ 4/5`.
- **Uses from project**: [`fdBoundaryFun_seg4_re`, `fdBoundaryFun_seg4_im_speed`, `seg1Speed`, `seg1Speed_pos`, `seg4T₀`]
- **Used by**: `seg4_near_of_linDelta`, `seg4_far_on_seg4`
- **Visibility**: public
- **Lines**: 72-83
- **Notes**: 12 lines.

### `theorem seg1Speed_mul_t₀_sub_three_fifths`
- **Type**: `{H c} (hH : √3/2 < H) : seg1Speed H · (seg4T₀ H c - 3/5) = c - √3/2`
- **What**: Algebraic identity: vertical speed times distance past `3/5` equals the height offset.
- **How**: Unfold `seg4T₀`, `field_simp` with `seg1Speed_pos.ne'`, then `ring`.
- **Hypotheses**: `√3/2 < H`.
- **Uses from project**: [`seg1Speed`, `seg1Speed_pos`, `seg4T₀`]
- **Used by**: `seg4_near_of_linDelta`, `smoothBoundaryData_seg4_of_ftcHyp`
- **Visibility**: public
- **Lines**: 86-90
- **Notes**: None.

### `theorem seg1Speed_mul_four_fifths_sub_t₀`
- **Type**: `{H c} (hH : √3/2 < H) : seg1Speed H · (4/5 - seg4T₀ H c) = H - c`
- **What**: Algebraic identity: speed times distance to `4/5` equals the remaining vertical span.
- **How**: Unfold `seg4T₀` and `seg1Speed`, `field_simp` + `ring`.
- **Hypotheses**: `√3/2 < H`.
- **Uses from project**: [`seg1Speed`, `seg1Speed_pos`, `seg4T₀`]
- **Used by**: `seg4_near_of_linDelta`, `smoothBoundaryData_seg4_of_ftcHyp`
- **Visibility**: public
- **Lines**: 93-98
- **Notes**: None.

### `theorem seg4_near_of_linDelta`
- **Type**: `{H} (hH) {z₀} (hz_re) {ε} (hε_hi : ε < H - z₀.im) (hε_lo : ε < z₀.im - √3/2) {t} (ht : |t - seg4T₀ H z₀.im| ≤ ε / seg1Speed H) : ‖fdBoundaryFun H t - z₀‖ ≤ ε`
- **What**: Near bound: parameter within `ε/K` of `t₀` gives spatial distance at most `ε`.
- **How**: Derive `h_lo_gap`/`h_hi_gap` from `seg1Speed_mul_*` identities to obtain `t ∈ (3/5, 4/5]`, then `fdBoundaryFun_seg4_dist_eq` + `gcongr` + `field_simp`.
- **Hypotheses**: `√3/2 < H`, `z₀.re = -1/2`, `ε < H - z₀.im`, `ε < z₀.im - √3/2`, parameter-distance bound.
- **Uses from project**: [`seg1Speed`, `seg1Speed_pos`, `seg4T₀`, `seg1Speed_mul_t₀_sub_three_fifths`, `seg1Speed_mul_four_fifths_sub_t₀`, `fdBoundaryFun_seg4_dist_eq`]
- **Used by**: `smoothBoundaryData_seg4_of_ftcHyp`
- **Visibility**: public
- **Lines**: 104-121
- **Notes**: 18 lines.

### `theorem seg4_far_on_seg4`
- **Type**: `{H} (hH) {z₀} (hz_re) {ε t} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) (hδt : ε/seg1Speed H < |t - seg4T₀ H z₀.im|) : ε < ‖fdBoundaryFun H t - z₀‖`
- **What**: Far bound restricted to seg4 itself: outside the δ-window, distance strictly exceeds `ε`.
- **How**: `fdBoundaryFun_seg4_dist_eq` + `mul_div_cancel₀` + `gcongr` with `seg1Speed_pos`.
- **Hypotheses**: `√3/2 < H`, `z₀.re = -1/2`, `3/5 < t ≤ 4/5`, δ-gap.
- **Uses from project**: [`seg1Speed`, `seg1Speed_pos`, `seg4T₀`, `fdBoundaryFun_seg4_dist_eq`]
- **Used by**: `seg4_far_bound`
- **Visibility**: public
- **Lines**: 126-135
- **Notes**: None.

### `theorem norm_gt_one_of_seg4_interior`
- **Type**: `{z₀} (hz_re : z₀.re = -1/2) (hc_lo : √3/2 < z₀.im) : 1 < ‖z₀‖`
- **What**: A seg4 interior point lies strictly outside the unit circle.
- **How**: Expand `Complex.normSq` and use `Real.mul_self_sqrt` + `nlinarith` with `normSq_eq_norm_sq`.
- **Hypotheses**: `z₀.re = -1/2`, `√3/2 < z₀.im`.
- **Uses from project**: []
- **Used by**: `seg4_dist_arc`, `seg4Threshold_pos`
- **Visibility**: public
- **Lines**: 140-147
- **Notes**: None.

### `theorem norm_sub_one_le_im_sub_sqrt3_seg4`
- **Type**: `{z₀} (hz_re : z₀.re = -1/2) (hc_lo : √3/2 ≤ z₀.im) : ‖z₀‖ - 1 ≤ z₀.im - √3/2`
- **What**: On seg4 the arc bound `‖z₀‖-1` dominates the vertical-width bound.
- **How**: Show `‖z₀‖² ≤ (z₀.im + 1 - √3/2)²` via `Complex.normSq_apply` with `hz_re`, then `Real.sqrt_le_sqrt`/`Real.sqrt_sq` extract the linear inequality.
- **Hypotheses**: `z₀.re = -1/2`, `√3/2 ≤ z₀.im`.
- **Uses from project**: []
- **Used by**: `smoothBoundaryData_seg4_of_ftcHyp`
- **Visibility**: public
- **Lines**: 151-166
- **Notes**: 16 lines.

### `theorem seg4_dist_arc`
- **Type**: `{z₀} (hz_re) (hc_lo) {H t} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) : ‖z₀‖ - 1 ≤ ‖fdBoundaryFun H t - z₀‖`
- **What**: Distance from seg4 interior point to the arc segments (seg2/seg3) is at least `‖z₀‖ - 1`.
- **How**: `fdBoundaryFun_arc_dist` together with `norm_gt_one_of_seg4_interior`.
- **Hypotheses**: `z₀.re = -1/2`, `√3/2 < z₀.im`, `t ∈ (1/5, 3/5]`.
- **Uses from project**: [`fdBoundaryFun_arc_dist`, `norm_gt_one_of_seg4_interior`]
- **Used by**: `seg4_far_bound`
- **Visibility**: public
- **Lines**: 169-173
- **Notes**: None.

### `theorem seg4_dist_seg1`
- **Type**: `{z₀} (hz_re : z₀.re = -1/2) {H t} (ht : t ≤ 1/5) : 1 ≤ ‖fdBoundaryFun H t - z₀‖`
- **What**: Distance from a seg4 point to seg1 (right vertical) is at least 1.
- **How**: Real part of the difference is `1`; bound via `Complex.abs_re_le_norm`.
- **Hypotheses**: `z₀.re = -1/2`, `t ≤ 1/5`.
- **Uses from project**: [`fdBoundaryFun_seg1_re`]
- **Used by**: `seg4_far_bound`
- **Visibility**: public
- **Lines**: 176-184
- **Notes**: None.

### `theorem seg4_dist_seg5`
- **Type**: `{z₀} (hz_hi : z₀.im < H) {t} (ht : 4/5 < t) : H - z₀.im ≤ ‖fdBoundaryFun H t - z₀‖`
- **What**: Distance from a seg4 point to seg5 (top horizontal) is at least `H - z₀.im`.
- **How**: Delegates to `fdBoundaryFun_seg5_im_dist`.
- **Hypotheses**: `z₀.im < H`, `4/5 < t`.
- **Uses from project**: [`fdBoundaryFun_seg5_im_dist`]
- **Used by**: `seg4_far_bound`
- **Visibility**: public
- **Lines**: 187-189
- **Notes**: None.

### `def seg4Threshold`
- **Type**: `(H : ℝ) (z₀ : ℂ) : ℝ`
- **What**: ε-threshold for seg4: `min(‖z₀‖ - 1, 1, H - z₀.im)`, identical shape to seg1.
- **How**: Direct definition by nested `min`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `seg4Threshold_pos`, `seg4_far_bound`, `smoothBoundaryData_seg4_of_ftcHyp`
- **Visibility**: public
- **Lines**: 194-195
- **Notes**: None.

### `theorem seg4Threshold_pos`
- **Type**: `{H z₀} (hz_re) (hc_lo) (hc_hi) : 0 < seg4Threshold H z₀`
- **What**: The seg4 threshold is positive for interior seg4 points.
- **How**: `lt_min` twice, using `norm_gt_one_of_seg4_interior` for the arc factor.
- **Hypotheses**: `z₀.re = -1/2`, `√3/2 < z₀.im < H`.
- **Uses from project**: [`seg4Threshold`, `norm_gt_one_of_seg4_interior`]
- **Used by**: `smoothBoundaryData_seg4_of_ftcHyp`
- **Visibility**: public
- **Lines**: 197-202
- **Notes**: None.

### `theorem seg4_far_bound`
- **Type**: `{H} (hH) {z₀} (hz_re) (hc_lo) (hc_hi) {ε} (hε_lt : ε < seg4Threshold H z₀) {t} (_ht_mem : t ∈ Icc 0 1) (hδt : ε/seg1Speed H < |t - seg4T₀ H z₀.im|) : ε < ‖fdBoundaryFun H t - z₀‖`
- **What**: Far bound across all five sub-segments of the boundary path.
- **How**: Extract three ε-comparisons from `seg4Threshold`, then `rcases` on the position of `t` against `1/5, 3/5, 4/5`, dispatching each sub-arc to `seg4_dist_seg1`, `seg4_dist_arc`, `seg4_far_on_seg4`, `seg4_dist_seg5`.
- **Hypotheses**: full seg4 interior assumptions and δ-gap.
- **Uses from project**: [`seg4Threshold`, `seg1Speed`, `seg4T₀`, `seg4_dist_seg1`, `seg4_dist_arc`, `seg4_far_on_seg4`, `seg4_dist_seg5`]
- **Used by**: `smoothBoundaryData_seg4_of_ftcHyp`
- **Visibility**: public
- **Lines**: 208-226
- **Notes**: 19 lines.

### `def smoothBoundaryData_seg4_of_ftcHyp`
- **Type**: `{H} (hH) (γ) (hγ) {z₀} (hz_re) (hc_lo) (hc_hi) (ftcHyp : ArcFTCHyp γ z₀ (seg4T₀ H z₀.im) (linDelta (seg1Speed H)) (seg4Threshold H z₀) (-(↑π * I))) : SmoothBoundaryWindingData γ z₀`
- **What**: Constructs `SmoothBoundaryWindingData` at a generic smooth seg4 point from an external `ArcFTCHyp`.
- **How**: Assemble structure fields: `t₀ := seg4T₀`, `δ := linDelta (seg1Speed H)`, threshold via `seg4Threshold`; positivity from `seg4Threshold_pos` and `linDelta_pos`; small-δ from `seg1Speed_mul_t₀_sub_three_fifths`/`seg1Speed_mul_four_fifths_sub_t₀`; far bound from `seg4_far_bound`; near bound from `seg4_near_of_linDelta`; ftcHyp threaded through.
- **Hypotheses**: `√3/2 < H`, `γ.extend = fdBoundaryFun` on `[0,1]`, seg4-interior conditions, external `ArcFTCHyp`.
- **Uses from project**: [`fdStart`, `PiecewiseC1Path`, `fdBoundaryFun`, `seg4T₀`, `seg4T₀_lt_four_fifths`, `seg4T₀_mem_Ioo`, `linDelta`, `linDelta_pos`, `seg1Speed`, `seg1Speed_pos`, `seg4Threshold`, `seg4Threshold_pos`, `seg1Speed_mul_t₀_sub_three_fifths`, `seg1Speed_mul_four_fifths_sub_t₀`, `seg4_far_bound`, `seg4_near_of_linDelta`, `norm_sub_one_le_im_sub_sqrt3_seg4`, `ArcFTCHyp`, `SmoothBoundaryWindingData`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 232-284
- **Notes**: 53 lines; structure definition with many fields proved inline.

## File Summary
Symmetric to seg1, this file constructs `SmoothBoundaryWindingData` for points strictly inside the left vertical edge of the FD boundary (`z₀.re = -1/2`, `z₀.im ∈ (√3/2, H)`). It establishes the linear distance formula on seg4 (`‖γ(t) - z₀‖ = K|t - t₀|` with `K = seg1Speed H`), derives crossing-parameter inequalities, and combines arc/vertical/horizontal off-seg4 distance lemmas into a unified `seg4_far_bound`. The main constructor `smoothBoundaryData_seg4_of_ftcHyp` packages all these geometric ingredients into the structure required by the boundary winding machinery, given an externally-supplied `ArcFTCHyp` analytical hypothesis. No sorries, no axioms.
