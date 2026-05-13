# Inventory: BoundaryWindingArcProof.lean

### `def arcT₀`
- **Type**: `(θ₀ : ℝ) → ℝ`
- **What**: Crossing parameter on the arc for angle θ₀: `t₀ = (6θ₀ - π)/(5π)`. Inverse of `fdArcAngle`.
- **How**: Definitional.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `arcT₀_gt_one_fifth`, `arcT₀_lt_three_fifths`, `arcT₀_mem_Ioo`, `fdArcAngle_arcT₀`, `arc_dist_eq`, `arc_half_angle_abs`, `arc_near_generic`, `arc_far_on_arc`, `arcGap`, `arcGap_pos`, `arcGap_le_one_fifth`, `arc_far_bound`, `smoothBoundaryData_arc_of_ftcHyp`
- **Visibility**: public
- **Lines**: 35
- **Notes**: none

### `theorem arcT₀_gt_one_fifth`
- **Type**: `π/3 < θ₀ → 1/5 < arcT₀ θ₀`
- **What**: Lower-edge bound: `t₀ > 1/5` when `θ₀ > π/3`.
- **How**: `rw [arcT₀, lt_div_iff₀]`, `nlinarith [Real.pi_pos]`.
- **Hypotheses**: `π/3 < θ₀`
- **Uses from project**: `arcT₀`
- **Used by**: `arcT₀_mem_Ioo`, `arcGap_pos`, `arc_far_bound`, `smoothBoundaryData_arc_of_ftcHyp`
- **Visibility**: public
- **Lines**: 37-39
- **Notes**: none

### `theorem arcT₀_lt_three_fifths`
- **Type**: `θ₀ < 2π/3 → arcT₀ θ₀ < 3/5`
- **What**: Upper-edge bound: `t₀ < 3/5` when `θ₀ < 2π/3`.
- **How**: `rw [arcT₀, div_lt_iff₀]`, `nlinarith [Real.pi_pos]`.
- **Hypotheses**: `θ₀ < 2π/3`
- **Uses from project**: `arcT₀`
- **Used by**: `arcT₀_mem_Ioo`, `arcGap_pos`, `arc_far_bound`, `smoothBoundaryData_arc_of_ftcHyp`
- **Visibility**: public
- **Lines**: 41-43
- **Notes**: none

### `theorem arcT₀_mem_Ioo`
- **Type**: `π/3 < θ₀ < 2π/3 → arcT₀ θ₀ ∈ Ioo 0 1`
- **What**: `t₀ ∈ (0,1)` for arc angles.
- **How**: Chain `(0 < 1/5).trans arcT₀_gt_one_fifth` and `arcT₀_lt_three_fifths.trans (3/5 < 1)`.
- **Hypotheses**: `π/3 < θ₀`, `θ₀ < 2π/3`
- **Uses from project**: `arcT₀`, `arcT₀_gt_one_fifth`, `arcT₀_lt_three_fifths`
- **Used by**: `smoothBoundaryData_arc_of_ftcHyp`
- **Visibility**: public
- **Lines**: 45-48
- **Notes**: none

### `theorem fdArcAngle_arcT₀`
- **Type**: `(θ₀ : ℝ) → fdArcAngle (arcT₀ θ₀) = θ₀`
- **What**: `arcT₀` is the inverse of `fdArcAngle`.
- **How**: `rw [fdArcAngle, arcT₀]`, `field_simp; ring`.
- **Hypotheses**: none
- **Uses from project**: `fdArcAngle`, `arcT₀`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 51-54
- **Notes**: none

### `theorem arc_dist_eq`
- **Type**: `(H θ₀ t : ℝ) → 1/5 < t → t ≤ 3/5 → ‖fdBoundaryFun H t - exp(iθ₀)‖ = 2|sin(5(t-t₀)π/12)|`
- **What**: Half-angle distance formula on the FD arc.
- **How**: Reduce angle difference via `fdArcAngle, arcT₀, field_simp, ring`; apply `fdBoundaryFun_arc_eq_exp` and `norm_exp_sub_exp`.
- **Hypotheses**: `1/5 < t`, `t ≤ 3/5`
- **Uses from project**: `fdBoundaryFun`, `fdArcAngle`, `arcT₀`, `fdBoundaryFun_arc_eq_exp`
- **Used by**: `arc_near_generic`, `arc_far_on_arc`
- **Visibility**: public
- **Lines**: 60-67
- **Notes**: key lemma `Complex.norm_exp_sub_exp`

### `lemma arc_half_angle_abs`
- **Type**: `|5(t-t₀)π/12| = 5π/12 · |t-t₀|`
- **What**: Factored form of the half-angle absolute value.
- **How**: `ring` rewrite to `(5π/12)·(t-t₀)`, then `abs_mul, abs_of_pos`.
- **Hypotheses**: none
- **Uses from project**: `arcT₀`
- **Used by**: `arc_near_generic`, `arc_far_on_arc`
- **Visibility**: private
- **Lines**: 72-76
- **Notes**: none

### `theorem arc_near_generic`
- **Type**: `0 < ε < 1/3 → 1/5 < t ≤ 3/5 → |t - t₀| ≤ arcsinDelta ε → ‖fdBoundaryFun H t - exp(iθ₀)‖ ≤ ε`
- **What**: Near bound: when `|t - t₀|` is small (≤ `arcsinDelta ε`), the distance is ≤ ε.
- **How**: 17 lines — apply `arc_dist_eq` then bound `|α| ≤ arcsin(ε/2)` via `arc_half_angle_abs` and `half_angle_arcsinDelta`; bound `arcsin(ε/2) ≤ π/2`, hence `|α| ≤ π`; use `Real.abs_sin_eq_sin_abs_of_abs_le_pi` and `Real.sin_le_sin_of_le_of_le_pi_div_two`; conclude with `linarith`.
- **Hypotheses**: `0 < ε`, `ε < 1/3`, `1/5 < t`, `t ≤ 3/5`, `|t - arcT₀ θ₀| ≤ arcsinDelta ε`
- **Uses from project**: `fdBoundaryFun`, `arcT₀`, `arcsinDelta`, `arc_dist_eq`, `arc_half_angle_abs`, `half_angle_arcsinDelta`
- **Used by**: `smoothBoundaryData_arc_of_ftcHyp`
- **Visibility**: public
- **Lines**: 80-99
- **Notes**: >10 lines; key lemma `Real.sin_le_sin_of_le_of_le_pi_div_two`, `Real.arcsin_le_pi_div_two`

### `theorem arc_far_on_arc`
- **Type**: `0 < ε < 1/3 → 1/5 < t ≤ 3/5 → 1/5 ≤ t₀ ≤ 3/5 → arcsinDelta ε < |t-t₀| → ε < ‖fdBoundaryFun H t - exp(iθ₀)‖`
- **What**: Far bound on the arc segment.
- **How**: 22 lines — by `arc_dist_eq` and `arc_half_angle_abs` show `|α| ≤ π/6 ≤ π` (using `|t-t₀| ≤ 2/5`); rewrite `arcsin(ε/2) < |α|` via `half_angle_arcsinDelta`; apply `Real.abs_sin_eq_sin_abs_of_abs_le_pi` and `Real.sin_lt_sin_of_lt_of_le_pi_div_two`.
- **Hypotheses**: `0 < ε`, `ε < 1/3`, `t ∈ (1/5, 3/5]`, `t₀ ∈ [1/5, 3/5]`, `arcsinDelta ε < |t - t₀|`
- **Uses from project**: `fdBoundaryFun`, `arcT₀`, `arcsinDelta`, `arc_dist_eq`, `arc_half_angle_abs`, `half_angle_arcsinDelta`
- **Used by**: `arc_far_bound`
- **Visibility**: public
- **Lines**: 106-131
- **Notes**: >10 lines; key lemma `Real.sin_lt_sin_of_lt_of_le_pi_div_two`

### `theorem arcZ₀_re_eq`
- **Type**: `(θ₀ : ℝ) → (exp(iθ₀)).re = cos θ₀`
- **What**: Real part of `exp(iθ₀)`.
- **How**: `Complex.exp_ofReal_mul_I_re`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `arcZ₀_abs_re_lt`
- **Visibility**: public
- **Lines**: 136-137
- **Notes**: none

### `theorem arcZ₀_im_eq`
- **Type**: `(θ₀ : ℝ) → (exp(iθ₀)).im = sin θ₀`
- **What**: Imaginary part of `exp(iθ₀)`.
- **How**: `Complex.exp_ofReal_mul_I_im`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `arcZ₀_im_le_one`, `arcZ₀_im_pos`
- **Visibility**: public
- **Lines**: 140-141
- **Notes**: none

### `theorem arcZ₀_abs_re_lt`
- **Type**: `π/3 < θ₀ < 2π/3 → |(exp(iθ₀)).re| < 1/2`
- **What**: Strict interior of arc lies in `|Re| < 1/2`.
- **How**: 15 lines — `rw [arcZ₀_re_eq, abs_lt]`; both bounds via `Real.strictAntiOn_cos` with `cos(2π/3) = -1/2` and `cos(π/3) = 1/2` (using `cos_pi_sub` and `cos_pi_div_three`).
- **Hypotheses**: `π/3 < θ₀`, `θ₀ < 2π/3`
- **Uses from project**: `arcZ₀_re_eq`
- **Used by**: `arc_dist_seg1`, `arc_dist_seg4`, `arcThreshold_pos`, `arc_far_bound`
- **Visibility**: public
- **Lines**: 144-162
- **Notes**: >10 lines; key lemma `Real.strictAntiOn_cos`, `Real.cos_pi_div_three`, `Real.cos_pi_sub`

### `theorem arcZ₀_im_le_one`
- **Type**: `(θ₀ : ℝ) → (exp(iθ₀)).im ≤ 1`
- **What**: `sin θ₀ ≤ 1`.
- **How**: `simpa [arcZ₀_im_eq] using Real.sin_le_one θ₀`.
- **Hypotheses**: none
- **Uses from project**: `arcZ₀_im_eq`
- **Used by**: `arc_dist_seg5`
- **Visibility**: public
- **Lines**: 165-166
- **Notes**: none

### `theorem arcZ₀_im_pos`
- **Type**: `π/3 < θ₀ < 2π/3 → 0 < (exp(iθ₀)).im`
- **What**: Positivity of arc point imaginary part.
- **How**: `rw [arcZ₀_im_eq]`, apply `Real.sin_pos_of_pos_of_lt_pi` with `linarith` bounds.
- **Hypotheses**: `π/3 < θ₀`, `θ₀ < 2π/3`
- **Uses from project**: `arcZ₀_im_eq`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 168-172
- **Notes**: none

### `theorem arc_dist_seg1`
- **Type**: `π/3 < θ₀ < 2π/3 → t ≤ 1/5 → 1/2 - |z₀.re| ≤ ‖fdBoundaryFun H t - exp(iθ₀)‖`
- **What**: Distance from arc point to seg1 (right vertical).
- **How**: Apply `fdBoundaryFun_seg1_re_dist` with `arcZ₀_abs_re_lt`.
- **Hypotheses**: `π/3 < θ₀`, `θ₀ < 2π/3`, `t ≤ 1/5`
- **Uses from project**: `fdBoundaryFun`, `arcZ₀_abs_re_lt`, `fdBoundaryFun_seg1_re_dist`
- **Used by**: `arc_far_bound`
- **Visibility**: public
- **Lines**: 175-178
- **Notes**: none

### `theorem arc_dist_seg4`
- **Type**: `π/3 < θ₀ < 2π/3 → 3/5 < t ≤ 4/5 → 1/2 - |z₀.re| ≤ ‖fdBoundaryFun H t - exp(iθ₀)‖`
- **What**: Distance from arc point to seg4 (left vertical).
- **How**: `fdBoundaryFun_seg4_re_dist` with `arcZ₀_abs_re_lt`.
- **Hypotheses**: `π/3 < θ₀`, `θ₀ < 2π/3`, `3/5 < t`, `t ≤ 4/5`
- **Uses from project**: `fdBoundaryFun`, `arcZ₀_abs_re_lt`, `fdBoundaryFun_seg4_re_dist`
- **Used by**: `arc_far_bound`
- **Visibility**: public
- **Lines**: 181-184
- **Notes**: none

### `theorem arc_dist_seg5`
- **Type**: `1 < H → 4/5 < t → H - 1 ≤ ‖fdBoundaryFun H t - exp(iθ₀)‖`
- **What**: Distance from arc point to seg5 (top horizontal).
- **How**: Chain `H - 1 ≤ H - z₀.im` (via `arcZ₀_im_le_one`) `.trans` `fdBoundaryFun_seg5_im_dist`.
- **Hypotheses**: `1 < H`, `4/5 < t`
- **Uses from project**: `fdBoundaryFun`, `arcZ₀_im_le_one`, `fdBoundaryFun_seg5_im_dist`
- **Used by**: `arc_far_bound`
- **Visibility**: public
- **Lines**: 187-191
- **Notes**: none

### `def arcGap`
- **Type**: `(θ₀ : ℝ) → ℝ`
- **What**: Gap from `t₀` to arc boundaries: `min(t₀ - 1/5, 3/5 - t₀)`.
- **How**: Definitional.
- **Hypotheses**: none
- **Uses from project**: `arcT₀`
- **Used by**: `arcGap_pos`, `arcThreshold`, `arcThreshold_pos`, `arcThreshold_lt_gap`, `arcGap_le_one_fifth`, `arcsinDelta_lt_arcGap`, `smoothBoundaryData_arc_of_ftcHyp`
- **Visibility**: public
- **Lines**: 197
- **Notes**: none

### `theorem arcGap_pos`
- **Type**: `π/3 < θ₀ < 2π/3 → 0 < arcGap θ₀`
- **What**: Strict positivity of the arc gap.
- **How**: `unfold arcGap; lt_min` with `arcT₀_gt_one_fifth`, `arcT₀_lt_three_fifths`.
- **Hypotheses**: `π/3 < θ₀`, `θ₀ < 2π/3`
- **Uses from project**: `arcGap`, `arcT₀_gt_one_fifth`, `arcT₀_lt_three_fifths`
- **Used by**: `arcThreshold_pos`, `arcsinDelta_lt_arcGap`
- **Visibility**: public
- **Lines**: 199-204
- **Notes**: none

### `theorem arcsinDelta_le_three_fifths_eps`
- **Type**: `0 < ε ≤ 2/3 → arcsinDelta ε ≤ 3ε/5`
- **What**: Linear upper bound on `arcsinDelta` via Jordan's inequality.
- **How**: 10 lines — Unfold `arcsinDelta`; apply `arcsin_le_pi_half_mul`; close with `calc … = 3ε/5 := by field_simp; ring`.
- **Hypotheses**: `0 < ε`, `ε ≤ 2/3`
- **Uses from project**: `arcsinDelta`, `arcsin_le_pi_half_mul`
- **Used by**: `arcsinDelta_lt_of_gap`
- **Visibility**: public
- **Lines**: 207-218
- **Notes**: none

### `theorem arcsinDelta_lt_of_gap`
- **Type**: `0 < g ≤ 1/5 → 0 < ε < 5g/3 → arcsinDelta ε < g`
- **What**: For small ε, `arcsinDelta ε` is below a positive gap `g`.
- **How**: `calc arcsinDelta ε ≤ 3ε/5 < 3·(5g/3)/5 = g`.
- **Hypotheses**: `0 < g`, `g ≤ 1/5`, `0 < ε`, `ε < 5g/3`
- **Uses from project**: `arcsinDelta`, `arcsinDelta_le_three_fifths_eps`
- **Used by**: `arcsinDelta_lt_arcGap`
- **Visibility**: public
- **Lines**: 221-227
- **Notes**: none

### `def arcThreshold`
- **Type**: `(H θ₀ : ℝ) → ℝ`
- **What**: Threshold for arc constructor: `min(min(1/2 - |z₀.re|, H - 1), min(1/3, 5·arcGap/3))`.
- **How**: Definitional.
- **Hypotheses**: none
- **Uses from project**: `arcGap`
- **Used by**: `arcThreshold_pos`, `arcThreshold_lt_re`, `arcThreshold_lt_top`, `arcThreshold_lt_third`, `arcThreshold_lt_gap`, `arcsinDelta_lt_arcGap`, `arc_far_bound`, `smoothBoundaryData_arc_of_ftcHyp`
- **Visibility**: public
- **Lines**: 234-236
- **Notes**: none

### `theorem arcThreshold_pos`
- **Type**: `1 < H → π/3 < θ₀ < 2π/3 → 0 < arcThreshold H θ₀`
- **What**: All four `min` arguments are positive.
- **How**: `unfold arcThreshold; lt_min × 3`; close each via `arcZ₀_abs_re_lt`, `linarith` (for `H-1`), `norm_num` (for `1/3`), `arcGap_pos`.
- **Hypotheses**: `1 < H`, `π/3 < θ₀`, `θ₀ < 2π/3`
- **Uses from project**: `arcThreshold`, `arcGap`, `arcZ₀_abs_re_lt`, `arcGap_pos`
- **Used by**: `smoothBoundaryData_arc_of_ftcHyp`
- **Visibility**: public
- **Lines**: 238-245
- **Notes**: none

### `theorem arcThreshold_lt_re`
- **Type**: `ε < arcThreshold H θ₀ → ε < 1/2 - |z₀.re|`
- **What**: First component of the threshold dominates.
- **How**: `lt_of_lt_of_le` chained with `min_le_left × 2`.
- **Hypotheses**: `ε < arcThreshold H θ₀`
- **Uses from project**: `arcThreshold`
- **Used by**: `arc_far_bound`
- **Visibility**: public
- **Lines**: 247-249
- **Notes**: none

### `theorem arcThreshold_lt_top`
- **Type**: `ε < arcThreshold H θ₀ → ε < H - 1`
- **What**: Second component dominates.
- **How**: `lt_of_lt_of_le (min_le_left, min_le_right)`.
- **Hypotheses**: `ε < arcThreshold H θ₀`
- **Uses from project**: `arcThreshold`
- **Used by**: `arc_far_bound`
- **Visibility**: public
- **Lines**: 251-253
- **Notes**: none

### `theorem arcThreshold_lt_third`
- **Type**: `ε < arcThreshold H θ₀ → ε < 1/3`
- **What**: Third component dominates.
- **How**: `lt_of_lt_of_le (min_le_right, min_le_left)`.
- **Hypotheses**: `ε < arcThreshold H θ₀`
- **Uses from project**: `arcThreshold`
- **Used by**: `arc_far_bound`, `smoothBoundaryData_arc_of_ftcHyp`
- **Visibility**: public
- **Lines**: 255-257
- **Notes**: none

### `theorem arcThreshold_lt_gap`
- **Type**: `ε < arcThreshold H θ₀ → ε < 5·arcGap θ₀ / 3`
- **What**: Fourth component dominates.
- **How**: `lt_of_lt_of_le (min_le_right, min_le_right)`.
- **Hypotheses**: `ε < arcThreshold H θ₀`
- **Uses from project**: `arcThreshold`, `arcGap`
- **Used by**: `arcsinDelta_lt_arcGap`
- **Visibility**: public
- **Lines**: 259-261
- **Notes**: none

### `theorem arcGap_le_one_fifth`
- **Type**: `(θ₀ : ℝ) → arcGap θ₀ ≤ 1/5`
- **What**: The arc gap is at most `1/5` (max attained at `t₀ = 2/5`).
- **How**: `by_cases arcT₀ θ₀ ≤ 2/5`; in each branch use `min_le_*` and `linarith`.
- **Hypotheses**: none
- **Uses from project**: `arcGap`, `arcT₀`
- **Used by**: `arcsinDelta_lt_arcGap`
- **Visibility**: public
- **Lines**: 264-273
- **Notes**: none

### `theorem arcsinDelta_lt_arcGap`
- **Type**: `π/3 < θ₀ < 2π/3 → 0 < ε < arcThreshold H θ₀ → arcsinDelta ε < arcGap θ₀`
- **What**: For ε under threshold, `arcsinDelta ε` is below the arc gap.
- **How**: Apply `arcsinDelta_lt_of_gap` with `arcGap_pos`, `arcGap_le_one_fifth`, `arcThreshold_lt_gap`.
- **Hypotheses**: `π/3 < θ₀`, `θ₀ < 2π/3`, `0 < ε`, `ε < arcThreshold H θ₀`
- **Uses from project**: `arcsinDelta`, `arcGap`, `arcThreshold`, `arcsinDelta_lt_of_gap`, `arcGap_pos`, `arcGap_le_one_fifth`, `arcThreshold_lt_gap`
- **Used by**: `smoothBoundaryData_arc_of_ftcHyp`
- **Visibility**: public
- **Lines**: 276-280
- **Notes**: none

### `theorem arc_far_bound`
- **Type**: `1 < H → π/3 < θ₀ < 2π/3 → 0 < ε < arcThreshold H θ₀ → t ∈ Icc 0 1 → arcsinDelta ε < |t - t₀| → ε < ‖fdBoundaryFun H t - exp(iθ₀)‖`
- **What**: Combined far bound dispatching over the five segments of `fdBoundaryFun`.
- **How**: 19 lines — extract bounds via `arcThreshold_lt_third`, `arcThreshold_lt_re`, `arcThreshold_lt_top`; nested `by_cases t ≤ 1/5, 3/5, 4/5`; segments 1/4 use `arc_dist_seg1`/`arc_dist_seg4`, segment 2-3 (arc) uses `arc_far_on_arc`, segment 5 uses `arc_dist_seg5`.
- **Hypotheses**: `1 < H`, `π/3 < θ₀`, `θ₀ < 2π/3`, `0 < ε < arcThreshold H θ₀`, `t ∈ Icc 0 1`, `arcsinDelta ε < |t - arcT₀ θ₀|`
- **Uses from project**: `fdBoundaryFun`, `arcT₀`, `arcsinDelta`, `arcThreshold`, `arcThreshold_lt_third`, `arcThreshold_lt_re`, `arcThreshold_lt_top`, `arc_dist_seg1`, `arc_dist_seg4`, `arc_dist_seg5`, `arc_far_on_arc`, `arcT₀_gt_one_fifth`, `arcT₀_lt_three_fifths`
- **Used by**: `smoothBoundaryData_arc_of_ftcHyp`
- **Visibility**: public
- **Lines**: 283-305
- **Notes**: >10 lines; dispatches over piecewise structure

### `def smoothBoundaryData_arc_of_ftcHyp`
- **Type**: From `H, γ, hγ, θ₀, h_lo, h_hi`, and an `ArcFTCHyp` for `(exp(iθ₀), arcT₀ θ₀, arcsinDelta, arcThreshold H θ₀, -πI)`, produces `SmoothBoundaryWindingData γ (exp(iθ₀))`.
- **What**: Main constructor: builds the `SmoothBoundaryWindingData` structure at a smooth arc point.
- **How**: 38 lines — populate fields: `t₀ = arcT₀ θ₀`, `δ = arcsinDelta`, `threshold = arcThreshold H θ₀`; positivity via `arcsinDelta_pos`; `hδ_small`: `arcsinDelta_lt_arcGap` then `lt_min` with `linarith`-from `min_le_left`/`min_le_right` of `arcGap`; `h_far`: rewrite via `hγ` then `arc_far_bound`; `h_near`: extract bounds from `arcsinDelta_lt_arcGap`, rewrite via `hγ`, apply `arc_near_generic`.
- **Hypotheses**: `1 < H`, `γ : PiecewiseC1Path (fdStart H) (fdStart H)` agreeing with `fdBoundaryFun H` on `Icc 0 1`, `π/3 < θ₀ < 2π/3`, `ArcFTCHyp γ (exp(iθ₀)) (arcT₀ θ₀) arcsinDelta (arcThreshold H θ₀) (-πI)`
- **Uses from project**: `SmoothBoundaryWindingData`, `ArcFTCHyp`, `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `arcT₀`, `arcT₀_mem_Ioo`, `arcsinDelta`, `arcsinDelta_pos`, `arcThreshold`, `arcThreshold_pos`, `arcThreshold_lt_third`, `arcsinDelta_lt_arcGap`, `arcGap`, `arcT₀_gt_one_fifth`, `arcT₀_lt_three_fifths`, `arc_far_bound`, `arc_near_generic`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 311-352
- **Notes**: >10 lines; structure constructor; key field `ftcHyp` is taken externally

## File Summary
- 26 declarations: 3 definitions (`arcT₀`, `arcGap`, `arcThreshold`) + 1 structure constructor (`smoothBoundaryData_arc_of_ftcHyp`) + 1 private helper + 21 public theorems.
- Provides the arc-point analogue of `SmoothBoundaryWindingData`: distance formula `2|sin α|`, near/far bounds via `arcsinDelta`, off-arc segment dispatches, threshold management.
- Builds on `CrossingAtI` (for `arcsinDelta`, `arcsinDelta_pos`, `half_angle_arcsinDelta`, `arcsin_le_pi_half_mul`), `InteriorWinding`, `SmoothBoundaryWindingProof` (for `SmoothBoundaryWindingData`, `ArcFTCHyp`, `fdArcAngle`, `fdBoundaryFun_arc_eq_exp`, `fdBoundaryFun_seg{1,4,5}_*_dist`, `fdBoundaryFun`), `WindingWeightProofs`.
- No sorries, no axioms, no `set_option`. `noncomputable section`.
