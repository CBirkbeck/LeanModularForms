# ArcFTCLimit.lean Inventory

### `theorem fdBoundaryFun_sub_i_slitPlane_seg1`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ≤ 1/5) : fdBoundaryFun H t - I ∈ Complex.slitPlane`
- **What**: On segment 1 (right vertical edge, Re = 1/2), the value `γ(t) - i` lies in the slit plane.
- **How**: Use `Complex.mem_slitPlane_iff`, take the left disjunct (Re > 0), rewrite via `fdBoundaryFun_seg1_re`, conclude with `norm_num` (Re = 1/2 > 0).
- **Hypotheses**: `t ≤ 1/5` (places `t` on segment 1).
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg1_re`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 38-43
- **Notes**: none

### `theorem fdBoundaryFun_sub_i_slitPlane_seg2`
- **Type**: `(H : ℝ) (t : ℝ) (ht1 : 1/5 < t) (ht2 : t < 2/5) : fdBoundaryFun H t - I ∈ Complex.slitPlane`
- **What**: On segment 2 (arc before `i`, angle in (-π/2, π/2)), `γ(t) - i ∈ slitPlane`.
- **How**: Reduce to Re > 0 via `mem_slitPlane_iff`, compute via `fdBoundaryFun_arc_eq_exp`, `exp_mul_I` to express Re as `cos(fdArcAngle t)`, show `cos > 0` using `Real.cos_pos_of_mem_Ioo` with bounds from `nlinarith` on `Real.pi_pos`.
- **Hypotheses**: `1/5 < t`, `t < 2/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_arc_eq_exp`, `fdArcAngle`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 46-58
- **Notes**: none

### `theorem fdBoundaryFun_sub_i_ne_zero_seg3`
- **Type**: `(H : ℝ) (t : ℝ) (ht2 : 2/5 < t) (ht3 : t ≤ 3/5) : fdBoundaryFun H t - I ≠ 0`
- **What**: On segment 3 (arc after `i`), `γ(t) - i ≠ 0`.
- **How**: Suppose equal to zero; take real part; show Re = cos(fdArcAngle t) = 0 contradicts `Real.cos_neg_of_pi_div_two_lt_of_lt` (angle is strictly in (π/2, 3π/2)) via `nlinarith` bounds.
- **Hypotheses**: `2/5 < t`, `t ≤ 3/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_arc_eq_exp`, `fdArcAngle`
- **Used by**: `fdBoundaryFun_log_diff_core_tendsto`
- **Visibility**: public
- **Lines**: 61-75
- **Notes**: none

### `theorem fdBoundaryFun_sub_i_neg_slitPlane_seg3`
- **Type**: `(H : ℝ) (t : ℝ) (ht2 : 2/5 < t) (ht3 : t ≤ 3/5) : -(fdBoundaryFun H t - I) ∈ Complex.slitPlane`
- **What**: On segment 3, the negated `γ(t) - i` lies in the slit plane (since the original has Re < 0).
- **How**: `mem_slitPlane_iff`, take left disjunct (Re > 0 after negation), simplify Re to `-cos(fdArcAngle t)`, use `Real.cos_neg_of_pi_div_two_lt_of_lt` with the same angle bounds.
- **Hypotheses**: `2/5 < t`, `t ≤ 3/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_arc_eq_exp`, `fdArcAngle`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 78-92
- **Notes**: none

### `theorem fdBoundaryFun_sub_i_slitPlane_seg5`
- **Type**: `(H : ℝ) (hH : 1 < H) (t : ℝ) (ht : 4/5 < t) : fdBoundaryFun H t - I ∈ Complex.slitPlane`
- **What**: On segment 5 (top horizontal at height `H > 1`), `γ(t) - i ∈ slitPlane` via Im > 0.
- **How**: `mem_slitPlane_iff`, take right disjunct (Im ≠ 0 or specifically Im > 0); simplify Im via `fdBoundaryFun_seg5_im`; `linarith`.
- **Hypotheses**: `H > 1`, `t > 4/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg5_im`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 95-100
- **Notes**: none

### `theorem fdBoundaryFun_sub_i_norm_left`
- **Type**: `(H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) : ‖fdBoundaryFun H (2/5 - δ) - I‖ = 2 * |Real.sin (5 * δ * Real.pi / 12)|`
- **What**: Norm of `γ(2/5 - δ) - i` equals `2|sin(5δπ/12)|`.
- **How**: Rewrite via `fdBoundaryFun_arc_dist_I`, show `fdArcAngle(2/5-δ) - π/2 = -(5δπ/6)`, divide by 2 inside `sin`, use `Real.sin_neg` and `abs_neg`.
- **Hypotheses**: `0 < δ < 1/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_arc_dist_I`, `fdArcAngle`
- **Used by**: `fdBoundaryFun_sub_i_norm_symm`
- **Visibility**: public
- **Lines**: 105-113
- **Notes**: none

### `theorem fdBoundaryFun_sub_i_norm_right`
- **Type**: `(H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) : ‖fdBoundaryFun H (2/5 + δ) - I‖ = 2 * |Real.sin (5 * δ * Real.pi / 12)|`
- **What**: Norm of `γ(2/5 + δ) - i` equals `2|sin(5δπ/12)|`.
- **How**: Rewrite via `fdBoundaryFun_arc_dist_I`, identify `fdArcAngle(2/5+δ) - π/2 = 5δπ/6`, then divide by 2 inside `sin`.
- **Hypotheses**: `0 < δ < 1/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_arc_dist_I`, `fdArcAngle`
- **Used by**: `fdBoundaryFun_sub_i_norm_symm`
- **Visibility**: public
- **Lines**: 116-123
- **Notes**: none

### `theorem fdBoundaryFun_sub_i_norm_symm`
- **Type**: `(H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) : ‖fdBoundaryFun H (2/5 - δ) - I‖ = ‖fdBoundaryFun H (2/5 + δ) - I‖`
- **What**: Norms of `γ(2/5-δ) - i` and `γ(2/5+δ) - i` are equal.
- **How**: Rewrite both sides using `fdBoundaryFun_sub_i_norm_left` and `_right`.
- **Hypotheses**: `0 < δ < 1/5`.
- **Uses from project**: `fdBoundaryFun_sub_i_norm_left`, `fdBoundaryFun_sub_i_norm_right`
- **Used by**: `fdBoundaryFun_log_diff_core_tendsto`
- **Visibility**: public
- **Lines**: 126-129
- **Notes**: none

### `theorem log_sub_eq_of_equal_norm`
- **Type**: `{z w : ℂ} (_hz : z ≠ 0) (_hw : w ≠ 0) (hnorm : ‖z‖ = ‖w‖) : Complex.log z - Complex.log w = ↑(z.arg - w.arg) * I`
- **What**: For two equal-norm nonzero complex numbers, the difference of logs equals `i·(arg z - arg w)`.
- **How**: `Complex.ext`: real part difference cancels via `Complex.log_re` and `hnorm`; imaginary part is `arg z - arg w` via `Complex.log_im`. Both with `simp` cleanup.
- **Hypotheses**: `z ≠ 0`, `w ≠ 0`, `‖z‖ = ‖w‖`.
- **Uses from project**: []
- **Used by**: `fdBoundaryFun_log_diff_core_tendsto`
- **Visibility**: public
- **Lines**: 135-142
- **Notes**: none

### `theorem fdBoundaryFun_arg_left`
- **Type**: `(H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) : (fdBoundaryFun H (2/5 - δ) - I).arg = -(5 * δ * Real.pi / 12)`
- **What**: Arg of left approach point `γ(2/5 - δ) - i` equals `-5δπ/12`.
- **How**: 40-line proof. Sets `α = 5δπ/12`, shows `α ∈ (0, π)` so `sin α > 0`; using `Real.cos_pi_div_two_sub`/`sin_pi_div_two_sub`, `sin_two_mul`, `cos_two_mul`, and `sin_sq_add_cos_sq`, factors `γ - i = 2 sin α · (cos α + (-sin α)i)` via `Complex.ext`. Concludes with `Complex.arg_mul_cos_add_sin_mul_I` giving `arg = -α`. Specific lemma: `Complex.arg_mul_cos_add_sin_mul_I`.
- **Hypotheses**: `0 < δ < 1/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_arc_eq_exp`, `fdArcAngle`
- **Used by**: `fdBoundaryFun_arg_diff`
- **Visibility**: public
- **Lines**: 150-194
- **Notes**: >30 lines proof (~45 lines).

### `theorem fdBoundaryFun_arg_right`
- **Type**: `(H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) : (fdBoundaryFun H (2/5 + δ) - I).arg = 5 * δ * Real.pi / 12 - Real.pi`
- **What**: Arg of right approach point `γ(2/5 + δ) - i` equals `5δπ/12 - π` (negative since im < 0).
- **How**: 50-line proof analogous to `_arg_left` but with factorization `γ(2/5+δ) - i = -(2 sin α · (cos α + sin α i))`; uses `Real.cos_add`/`sin_add`, `sin_two_mul`, `cos_two_mul`. Concludes by `Complex.arg_neg_eq_arg_sub_pi_of_im_pos` since the inner product has positive imaginary part (`nlinarith` on `sin α > 0`). Specific lemma: `Complex.arg_neg_eq_arg_sub_pi_of_im_pos`.
- **Hypotheses**: `0 < δ < 1/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_arc_eq_exp`, `fdArcAngle`
- **Used by**: `fdBoundaryFun_arg_diff`
- **Visibility**: public
- **Lines**: 200-252
- **Notes**: >30 lines proof (~53 lines).

### `theorem fdBoundaryFun_arg_diff`
- **Type**: `(H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) : (fdBoundaryFun H (2/5 - δ) - I).arg - (fdBoundaryFun H (2/5 + δ) - I).arg = Real.pi - 5 * δ * Real.pi / 6`
- **What**: Difference of args equals `π - 5δπ/6`.
- **How**: Rewrite both args via `fdBoundaryFun_arg_left`, `_right`; finish with `ring`.
- **Hypotheses**: `0 < δ < 1/5`.
- **Uses from project**: `fdBoundaryFun_arg_left`, `fdBoundaryFun_arg_right`
- **Used by**: `fdBoundaryFun_log_diff_core_tendsto`
- **Visibility**: public
- **Lines**: 255-259
- **Notes**: none

### `theorem fdBoundaryFun_log_diff_core_tendsto`
- **Type**: `(H : ℝ) : Tendsto (fun δ => Complex.log (fdBoundaryFun H (2/5 - δ) - I) - Complex.log (fdBoundaryFun H (2/5 + δ) - I)) (𝓝[>] 0) (𝓝 (↑Real.pi * I))`
- **What**: `log(γ(2/5-δ) - i) - log(γ(2/5+δ) - i) → πi` as `δ → 0⁺`.
- **How**: 40-line proof. Eventually rewrites the log difference to `↑(π - 5δπ/6) * I` using `log_sub_eq_of_equal_norm` (with norm equality from `fdBoundaryFun_sub_i_norm_symm` and nonzero from `arc_eq_exp + cos > 0` for left and `fdBoundaryFun_sub_i_ne_zero_seg3` for right), then `fdBoundaryFun_arg_diff`. Then uses a `ContinuousAt` argument with `Filter.Tendsto.mul_const`, `Filter.Tendsto.ofReal`, `mono_left nhdsWithin_le_nhds`. Specific lemmas: `log_sub_eq_of_equal_norm`, `fdBoundaryFun_arg_diff`.
- **Hypotheses**: none beyond a real `H`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_arc_eq_exp`, `fdArcAngle`, `fdBoundaryFun_sub_i_ne_zero_seg3`, `fdBoundaryFun_sub_i_norm_symm`, `fdBoundaryFun_arg_diff`, `log_sub_eq_of_equal_norm`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 265-306
- **Notes**: >30 lines proof (~42 lines).

## File Summary

**File**: `LeanModularForms/ForMathlib/ArcFTCLimit.lean` (308 lines)

Five-part trigonometric/analytic analysis of the `fdBoundaryFun H` arc-and-edge curve near the corner point `i = γ(2/5)`, imported by ArcFTC machinery:
1. **Slit-plane membership** on each segment (`_slitPlane_seg1`, `_seg2`, `_neg_slitPlane_seg3`, `_seg5`) ensures principal-branch logs work.
2. **Norm symmetry** at the corner: `‖γ(2/5 ± δ) - i‖ = 2|sin(5δπ/12)|` via `fdBoundaryFun_arc_dist_I`.
3. **Log-difference identity** for equal-norm complex numbers (`log_sub_eq_of_equal_norm`).
4. **Arg computations** at the approach points: `-(5δπ/12)` on the left, `5δπ/12 - π` on the right — two ~50-line `Complex.ext` proofs using half-angle/double-angle identities and `arg_mul_cos_add_sin_mul_I`/`arg_neg_eq_arg_sub_pi_of_im_pos`.
5. **Limit**: the log difference tends to `πi` as `δ → 0⁺`, the key input for FTC-based winding number computation around `i`.

No `sorry`, no axioms, no `set_option`. Heavy use of `nlinarith [Real.pi_pos]` for angle-range bounds.
