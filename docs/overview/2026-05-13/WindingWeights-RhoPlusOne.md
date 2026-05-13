# Inventory: WindingWeights/RhoPlusOne.lean

File: `LeanModularForms/ForMathlib/ValenceFormula/WindingWeights/RhoPlusOne.lean` (980 lines, 26 declarations)

Imports: `WindingWeights.Common`, `ContourIntegral.WindingNumber`, `ContourIntegral.CrossingLimit`.

Top-level `attribute [local instance] Classical.propDecidable` and `noncomputable section` (lines 25–27, closed line 980).

---

### `private lemma g_rho'_seg0_value`
- **Type**: `{t : ℝ} (ht : t ≤ 1) → fdBoundary_H H t - ellipticPointRhoPlusOne = ↑((1 - t) * (H - Real.sqrt 3 / 2)) * I`
- **What**: Closed-form for the difference between the boundary's left vertical segment and the elliptic point `ρ+1`.
- **How**: `rw [fdBoundary_H_seg0]`, unfold `ellipticPointRhoPlusOne`, push casts, `ring`.
- **Hypotheses**: `t ≤ 1`.
- **Uses from project**: `fdBoundary_H_seg0`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`.
- **Used by**: `g_rho'_norm_seg0`, `g_rho'_im_nonneg`, `g_rho'_ne_zero`, `g_rho'_slitPlane`, `arg_approach_rho'_left`, `g_rho'_norm_seg0_at`, `ftc_logDeriv_telescope_rho_plus_one` (indirectly via `hg_eq_h₀`).
- **Visibility**: private
- **Lines**: 29-35
- **Notes**: none.

### `private lemma g_rho'_norm_seg0`
- **Type**: `(hH : Real.sqrt 3 / 2 < H) {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t < 1) → ‖fdBoundary_H H t - ellipticPointRhoPlusOne‖ = (1 - t) * (H - Real.sqrt 3 / 2)`
- **What**: Norm formula on the open left vertical segment.
- **How**: Substitute via `g_rho'_seg0_value`, then `norm_mul`, `Complex.norm_real`, `Complex.norm_I`, `Real.norm_of_nonneg`.
- **Hypotheses**: `√3/2 < H`, `0 ≤ t`, `t < 1`.
- **Uses from project**: `g_rho'_seg0_value`.
- **Used by**: `norm_le_middle_rho_plus_one`, `pv_integral_at_rho_plus_one_tendsto` (clause `h_far_left`).
- **Visibility**: private
- **Lines**: 37-40
- **Notes**: none.

### `private lemma g_rho'_arc_value`
- **Type**: `{t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) → fdBoundary_H H t - ellipticPointRhoPlusOne = Complex.exp (↑(Real.pi * (1 + t) / 6) * I) - (↑(1/2) + ↑(Real.sqrt 3 / 2) * I)`
- **What**: Closed-form for the arc segment difference from `ρ+1`.
- **How**: `rw [fdBoundary_H_eq_arc]`, unfold `ellipticPointRhoPlusOne`, push casts, `ring`.
- **Hypotheses**: `1 < t < 3`.
- **Uses from project**: `fdBoundary_H_eq_arc`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`.
- **Used by**: `g_rho'_im_nonneg`, `g_rho'_ne_zero`, `g_rho'_slitPlane`, `arg_approach_rho'_right_helper`, `g_rho'_norm_arc`, `ftc_logDeriv_telescope_rho_plus_one`.
- **Visibility**: private
- **Lines**: 42-48
- **Notes**: none.

### `private lemma g_rho'_seg3_value`
- **Type**: `{t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) → fdBoundary_H H t - ellipticPointRhoPlusOne = -1 + ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I`
- **What**: Closed-form for the right vertical segment difference from `ρ+1`.
- **How**: `rw [fdBoundary_H_seg3]`, unfold `ellipticPointRhoPlusOne`, push casts, `ring`.
- **Hypotheses**: `3 < t ≤ 4`.
- **Uses from project**: `fdBoundary_H_seg3`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`.
- **Used by**: `g_rho'_im_nonneg`, `g_rho'_ne_zero`, `g_rho'_slitPlane`, `g_rho'_norm_ge_one_seg3`, `ftc_logDeriv_telescope_rho_plus_one`.
- **Visibility**: private
- **Lines**: 50-56
- **Notes**: none.

### `private lemma g_rho'_seg4_value`
- **Type**: `{t : ℝ} (ht4 : 4 < t) → fdBoundary_H H t - ellipticPointRhoPlusOne = ↑(t - 5) + ↑(H - Real.sqrt 3 / 2) * I`
- **What**: Closed-form for the top horizontal segment difference from `ρ+1`.
- **How**: `rw [fdBoundary_H_seg4]`, unfold `ellipticPointRhoPlusOne`, push casts, `ring`.
- **Hypotheses**: `4 < t`.
- **Uses from project**: `fdBoundary_H_seg4`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`.
- **Used by**: `g_rho'_im_nonneg`, `g_rho'_ne_zero`, `g_rho'_slitPlane`, `g_rho'_norm_ge_seg4`, `ftc_logDeriv_telescope_rho_plus_one`.
- **Visibility**: private
- **Lines**: 58-64
- **Notes**: none.

### `private lemma sin_ge_sqrt3_div_2_of_mem`
- **Type**: `{θ : ℝ} (hlo : Real.pi / 3 ≤ θ) (hhi : θ ≤ 2 * Real.pi / 3) → Real.sqrt 3 / 2 ≤ Real.sin θ`
- **What**: `sin θ ≥ √3/2` for `θ ∈ [π/3, 2π/3]`.
- **How**: Rewrite RHS as `sin(π/3)`; split at `θ ≤ π/2` using `Real.sin_le_sin_of_le_of_le_pi_div_two` (upper half) and reflection via `sin_pi_sub` for the other half.
- **Hypotheses**: `π/3 ≤ θ ≤ 2π/3`.
- **Uses from project**: [] (only mathlib).
- **Used by**: `g_rho'_im_nonneg`.
- **Visibility**: private
- **Lines**: 66-75
- **Notes**: none.

### `private lemma sin_gt_sqrt3_div_2_of_mem`
- **Type**: `{θ : ℝ} (hlo : Real.pi / 3 < θ) (hhi : θ < 2 * Real.pi / 3) → Real.sqrt 3 / 2 < Real.sin θ`
- **What**: Strict version of the previous lemma.
- **How**: Same as above with `Real.sin_lt_sin_of_lt_of_le_pi_div_two`.
- **Hypotheses**: `π/3 < θ < 2π/3`.
- **Uses from project**: [] (only mathlib).
- **Used by**: `g_rho'_ne_zero`, `g_rho'_slitPlane`.
- **Visibility**: private
- **Lines**: 77-86
- **Notes**: none.

### `private lemma g_rho'_im_nonneg`
- **Type**: `(hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht : t ∈ Icc 0 5) (hne : t ≠ 1) → 0 ≤ (fdBoundary_H H t - ellipticPointRhoPlusOne).im` (40 lines)
- **What**: The imaginary part of `γ(t) - (ρ+1)` is non-negative everywhere on the boundary except possibly `t = 1`.
- **How**: Case-split on `t ≤ 1`, `1 < t < 3` (arc), `t = 3`, `3 < t ≤ 4`, `t > 4`, using the segment value lemmas `g_rho'_seg0_value`, `g_rho'_arc_value`, `g_rho'_seg3_value`, `g_rho'_seg4_value`, plus `sin_ge_sqrt3_div_2_of_mem` for the arc; closed by `linarith` after simp rewrites of imaginary parts.
- **Hypotheses**: `√3/2 < H`, `t ∈ [0,5]`, `t ≠ 1`.
- **Uses from project**: `g_rho'_seg0_value`, `g_rho'_arc_value`, `g_rho'_seg3_value`, `g_rho'_seg4_value`, `fdBoundary_H_at_three_eq_rho`, `sin_ge_sqrt3_div_2_of_mem`, `ellipticPointRhoPlusOne`, `ellipticPointRho`.
- **Used by**: `ftc_logDeriv_telescope_rho_plus_one` (via `hh₁_im_nn`, `hh₂_im_nn`).
- **Visibility**: private
- **Lines**: 88-126
- **Notes**: >30 lines.

### `private lemma g_rho'_ne_zero`
- **Type**: `(hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht : t ∈ Icc 0 5) (hne : t ≠ 1) → fdBoundary_H H t - ellipticPointRhoPlusOne ≠ 0` (47 lines)
- **What**: The shifted boundary never vanishes except at `t = 1` (where it lands at `ρ+1`).
- **How**: Case-split as in `g_rho'_im_nonneg`; in each branch, derive a contradiction from the corresponding segment value formula (e.g. arc branch uses `sin_gt_sqrt3_div_2_of_mem` to get strictly positive imaginary part).
- **Hypotheses**: `√3/2 < H`, `t ∈ [0,5]`, `t ≠ 1`.
- **Uses from project**: `g_rho'_seg0_value`, `g_rho'_arc_value`, `g_rho'_seg3_value`, `g_rho'_seg4_value`, `fdBoundary_H_at_three_eq_rho`, `sin_gt_sqrt3_div_2_of_mem`, `ellipticPointRhoPlusOne`, `ellipticPointRho`.
- **Used by**: `ftc_logDeriv_telescope_rho_plus_one` (via `hh₁_ne`, `hh₂_ne`).
- **Visibility**: private
- **Lines**: 128-174
- **Notes**: >30 lines.

### `private lemma g_rho'_slitPlane`
- **Type**: `(hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht : t ∈ Icc 0 5) (hne1 : t ≠ 1) (hne3 : t ≠ 3) → fdBoundary_H H t - ellipticPointRhoPlusOne ∈ slitPlane`
- **What**: The shifted boundary lies in the slit plane (i.e., not on `(-∞, 0]`) when `t ≠ 1, 3`. (34 lines)
- **How**: Show the imaginary part is strictly positive on each piece by case-splitting on segments, using `g_rho'_seg0_value`, `g_rho'_arc_value`, `g_rho'_seg3_value`, `g_rho'_seg4_value` and `sin_gt_sqrt3_div_2_of_mem`. Closes via `ne_of_gt` after `Complex.mem_slitPlane_iff`.
- **Hypotheses**: `√3/2 < H`, `t ∈ [0,5]`, `t ≠ 1`, `t ≠ 3`.
- **Uses from project**: `g_rho'_seg0_value`, `g_rho'_arc_value`, `g_rho'_seg3_value`, `g_rho'_seg4_value`, `sin_gt_sqrt3_div_2_of_mem`, `ellipticPointRhoPlusOne`.
- **Used by**: `ftc_logDeriv_telescope_rho_plus_one` (via `hh₀_slit`, `hh₁_slit_interior`, `hh₂_slit_interior`, `hh₃_slit`).
- **Visibility**: private
- **Lines**: 176-209
- **Notes**: >30 lines.

### `private theorem arg_approach_rho'_left`
- **Type**: `(hH : Real.sqrt 3 / 2 < H) {δ : ℝ} (hδ : 0 < δ) (_hδ1 : δ ≤ 1) → (fdBoundary_H H (1 - δ) - ellipticPointRhoPlusOne).arg = Real.pi / 2`
- **What**: Approaching `ρ+1` from the left vertical segment, the difference has argument `π/2` (pure positive imaginary).
- **How**: Apply `g_rho'_seg0_value` at `1 - δ`, then `Complex.arg_eq_pi_div_two_iff`; close by computing real part `= 0` and imaginary part `> 0`.
- **Hypotheses**: `√3/2 < H`, `0 < δ ≤ 1`.
- **Uses from project**: `g_rho'_seg0_value`.
- **Used by**: `pv_integral_at_rho_plus_one_tendsto` (the `h_limit` clause via `hzL_arg`).
- **Visibility**: private (theorem)
- **Lines**: 211-220
- **Notes**: none.

### `private lemma g_rho'_norm_seg0_at`
- **Type**: `(hH : Real.sqrt 3 / 2 < H) {δ : ℝ} (hδ : 0 < δ) (_hδ1 : δ ≤ 1) → ‖fdBoundary_H H (1 - δ) - ellipticPointRhoPlusOne‖ = δ * (H - Real.sqrt 3 / 2)`
- **What**: Norm at parameterized distance `δ` to the left of `t = 1`.
- **How**: Substitute via `g_rho'_seg0_value`, simplify `1 - (1 - δ) = δ`, then `norm_mul`, `Complex.norm_real`, `Complex.norm_I`, `Real.norm_of_nonneg`.
- **Hypotheses**: `√3/2 < H`, `0 < δ ≤ 1`.
- **Uses from project**: `g_rho'_seg0_value`.
- **Used by**: `norm_le_middle_rho_plus_one`, `pv_integral_at_rho_plus_one_tendsto` (clauses `h_near`, `h_limit`).
- **Visibility**: private
- **Lines**: 222-227
- **Notes**: none.

### `private lemma arg_approach_rho'_right_helper`
- **Type**: `(hδ : 0 < δ) (hδ_small : δ < 2) → (fdBoundary_H H (1 + δ) - ellipticPointRhoPlusOne).arg = 5 * Real.pi / 6 + δ * Real.pi / 12` (60 lines)
- **What**: On the arc, the argument of `γ(1+δ) - (ρ+1)` is `5π/6 + δπ/12`.
- **How**: Apply `g_rho'_arc_value`, then use sum-to-product identities `Real.cos_sub_cos`, `Real.sin_sub_sin` to express `exp(iθ) - (1/2 + (√3/2)i)` as `2 sin(δπ/12)·exp(i(5π/6 + δπ/12))`; conclude via `Complex.arg_mul_cos_add_sin_mul_I` after auxiliary positivity facts (`ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`).
- **Hypotheses**: `0 < δ < 2`.
- **Uses from project**: `g_rho'_arc_value`, `exp_real_angle_I`, `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`.
- **Used by**: `pv_integral_at_rho_plus_one_tendsto` (the `h_limit` clause via `hzR_arg`).
- **Visibility**: private
- **Lines**: 229-286
- **Notes**: >30 lines.

### `private lemma g_rho'_norm_arc`
- **Type**: `{δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 2) → ‖fdBoundary_H H (1 + δ) - ellipticPointRhoPlusOne‖ = 2 * Real.sin (δ * Real.pi / 12)` (49 lines)
- **What**: Norm on the arc at parameterized distance `δ` to the right of `t = 1`.
- **How**: Mirror of `arg_approach_rho'_right_helper`. Uses `g_rho'_arc_value` plus `Real.cos_sub_cos`/`Real.sin_sub_sin` to factor out `2 sin(δπ/12)·exp(i·angle)`; then `norm_mul`, `Complex.norm_real`, `Complex.norm_exp_ofReal_mul_I`.
- **Hypotheses**: `0 < δ < 2`.
- **Uses from project**: `g_rho'_arc_value`, `exp_real_angle_I`, `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`.
- **Used by**: `g_rho'_norm_arc_full`, `norm_le_middle_rho_plus_one`, `rho'_norm_gt_right_of_arc`, `arc_angle_lt_epsilon`, `pv_integral_at_rho_plus_one_tendsto` (multiple clauses).
- **Visibility**: private
- **Lines**: 288-336
- **Notes**: >30 lines.

### `private lemma g_rho'_norm_arc_full`
- **Type**: `{t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) → ‖fdBoundary_H H t - ellipticPointRhoPlusOne‖ = 2 * Real.sin ((t - 1) * Real.pi / 12)`
- **What**: Same formula as `g_rho'_norm_arc` reparameterized in `t`.
- **How**: `convert g_rho'_norm_arc (δ := t - 1) ... using 2 <;> ring_nf`.
- **Hypotheses**: `1 < t < 3`.
- **Uses from project**: `g_rho'_norm_arc`.
- **Used by**: `norm_le_middle_rho_plus_one`, `rho'_norm_gt_right_of_arc`.
- **Visibility**: private
- **Lines**: 338-342
- **Notes**: none.

### `private lemma g_rho'_norm_ge_seg4`
- **Type**: `(hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht4 : 4 ≤ t) (ht5 : t ≤ 5) → H - Real.sqrt 3 / 2 ≤ ‖fdBoundary_H H t - ellipticPointRhoPlusOne‖`
- **What**: On the top segment, norm is at least the gap `H - √3/2`.
- **How**: Compute `(γ t - (ρ+1)).im = H - √3/2` (case-splitting on `t = 4` vs `t > 4`), then `|im| ≤ ‖·‖` (`Complex.abs_im_le_norm`).
- **Hypotheses**: `√3/2 < H`, `4 ≤ t ≤ 5`.
- **Uses from project**: `g_rho'_seg4_value`, `fdBoundary_H_at_four`, `ellipticPointRhoPlusOne`.
- **Used by**: `rho'_norm_gt_right_of_arc`, `pv_integral_at_rho_plus_one_tendsto` (`h_far_right` and `h_limit`).
- **Visibility**: private
- **Lines**: 344-363
- **Notes**: none.

### `private lemma g_rho'_norm_ge_one_seg3`
- **Type**: `{t : ℝ} (ht3 : 3 ≤ t) (ht4 : t ≤ 4) → 1 ≤ ‖fdBoundary_H H t - ellipticPointRhoPlusOne‖`
- **What**: On the right vertical segment, the norm is at least `1`.
- **How**: At `t = 3` use `fdBoundary_H_at_three_eq_rho` and direct ring; for `3 < t ≤ 4` use `g_rho'_seg3_value` to extract `re = -1` and `|re| ≤ ‖·‖` via `Complex.abs_re_le_norm`.
- **Hypotheses**: `3 ≤ t ≤ 4`.
- **Uses from project**: `g_rho'_seg3_value`, `fdBoundary_H_at_three_eq_rho`, `ellipticPointRhoPlusOne`, `ellipticPointRho`.
- **Used by**: `rho'_norm_gt_right_of_arc`.
- **Visibility**: private
- **Lines**: 365-380
- **Notes**: none.

### `private lemma ftc_logDeriv_telescope_rho_plus_one`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) {δ_L δ_R : ℝ} (hδ_L : 0 < δ_L) (hδ_L1 : δ_L < 1) (hδ_R : 0 < δ_R) (hδ_R1 : δ_R < 1) → IntervalIntegrable .. 0 (1-δ_L) ∧ IntervalIntegrable .. (1+δ_R) 5 ∧ ((∫ .. 0..(1-δ_L)) + (∫ .. (1+δ_R)..5) = log(g(1-δ_L)) - log(g(1+δ_R)))` (230 lines)
- **What**: Fundamental Theorem of Calculus telescoping: the two `logDeriv`-style integrals around the elliptic point `ρ+1` (excluding a symmetric ε-neighborhood `[1-δ_L, 1+δ_R]`) equal the difference of complex logs at the endpoints.
- **How**: Defines four piecewise representations `h₀, h₁, h₂, h₃` matching `g = γ - ρ'` on the four pieces (segments 0, arc, segment 3, segment 4); proves each has the correct `HasDerivAt`; chains four pieces via `ftc_log_pieceFM` (for slit-plane pieces 0, 4) and `ftc_log_piece_upper` (for upper-half-plane pieces arc, 3); finally combines integrals using `intervalIntegral.integral_add_adjacent_intervals` and closes via `fdBoundary_H_closed`.
- **Hypotheses**: `√3/2 < H`, small positive `δ_L, δ_R`.
- **Uses from project**: `fdBoundary_H_seg0`, `fdBoundary_H_eq_arc`, `fdBoundary_H_seg3`, `fdBoundary_H_seg4`, `fdBoundary_H_at_three_eq_rho`, `fdBoundary_H_at_four`, `fdBoundary_H_closed`, `g_rho'_seg0_value`, `g_rho'_arc_value`, `g_rho'_seg3_value`, `g_rho'_seg4_value`, `g_rho'_slitPlane`, `g_rho'_im_nonneg`, `g_rho'_ne_zero`, `ftc_log_pieceFM`, `ftc_log_piece_upper`, `exp_real_angle_I`, `ellipticPointRhoPlusOne`, `ellipticPointRho`.
- **Used by**: `pv_integral_at_rho_plus_one_tendsto` (the `h_ftc`, `hint_left`, `hint_right` clauses).
- **Visibility**: private
- **Lines**: 382-611
- **Notes**: >30 lines (much larger, ~230 lines).

### `private lemma norm_le_middle_rho_plus_one`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) {ε δ_L δ_R : ℝ} (...) → ∀ t, 1-δ_L ≤ t → t ≤ 1+δ_R → ¬(‖fdBoundary_H H t - ρ+1‖ > ε)` (25 lines)
- **What**: Inside the symmetric ε-neighborhood the norm is `≤ ε` (no point inside has norm strictly above `ε`).
- **How**: Case-split on `t ≤ 1` vs `1 < t`. Use `g_rho'_norm_seg0` + `g_rho'_norm_seg0_at` (left), then `g_rho'_norm_arc_full` + `g_rho'_norm_arc` (right). In each case use monotonicity of `sin` on `[0, π/2]` via `Real.sin_le_sin_of_le_of_le_pi_div_two`.
- **Hypotheses**: `√3/2 < H`, positive small `δ_L, δ_R`, two norm equalities at endpoints, gap positivity.
- **Uses from project**: `fdBoundary_H_at_one_eq_rho_plus_one`, `g_rho'_norm_seg0`, `g_rho'_norm_seg0_at`, `g_rho'_norm_arc_full`, `g_rho'_norm_arc`.
- **Used by**: `pv_integral_at_rho_plus_one_tendsto` (`h_near` clause).
- **Visibility**: private
- **Lines**: 613-636
- **Notes**: >10 lines.

### `private lemma rho'_norm_gt_right_of_arc`
- **Type**: `(H : ℝ) (hH : √3/2 < H) {ε δ_R : ℝ} (...) → ∀ t ∈ Ioo (1 + δ_R) 5, ‖γ t - (ρ+1)‖ > ε` (22 lines)
- **What**: Beyond `1 + δ_R` (on the right of the elliptic point), the norm exceeds `ε`.
- **How**: Case-split on `t ≤ 3` (arc, using `g_rho'_norm_arc_full` + `g_rho'_norm_arc` + strict monotonicity of sin), `3 ≤ t ≤ 4` (norm `≥ 1 > ε` via `g_rho'_norm_ge_one_seg3`), `t > 4` (norm `≥ H - √3/2 > ε` via `g_rho'_norm_ge_seg4`).
- **Hypotheses**: `√3/2 < H`, `ε < 1`, `ε < H - √3/2`, positive small `δ_R`, right-side norm equality `= ε`.
- **Uses from project**: `g_rho'_norm_arc_full`, `g_rho'_norm_arc`, `g_rho'_norm_ge_one_seg3`, `g_rho'_norm_ge_seg4`.
- **Used by**: `pv_integral_at_rho_plus_one_tendsto` (`h_far_right` clause).
- **Visibility**: private
- **Lines**: 638-660
- **Notes**: >10 lines.

### `private lemma arc_angle_lt_epsilon`
- **Type**: `{δ_R ε : ℝ} (hδ_R_pos : 0 < δ_R) (hδ_R_lt_one : δ_R < 1) (h_norm_R : ‖fdBoundary_H H (1+δ_R) - ρ+1‖ = ε) → δ_R * Real.pi / 12 < ε`
- **What**: The geometric angle `δ_R π / 12` is below the radial `ε`, since `2 sin x < ε ⇒ x < ε`.
- **How**: From `h_norm_R` and `g_rho'_norm_arc`: `sin(δ_R π/12) = ε/2`. Then `nlinarith [Real.sin_gt_sub_cube hx_pos hx_le_one, …]` (with `x ≤ 1` from `Real.pi_le_four`).
- **Hypotheses**: `0 < δ_R < 1`, the norm equality at the right endpoint.
- **Uses from project**: `g_rho'_norm_arc`.
- **Used by**: `pv_integral_at_rho_plus_one_tendsto` (`h_limit` final clause).
- **Visibility**: private
- **Lines**: 662-671
- **Notes**: none.

### `private lemma δ_right_lt_one_aux`
- **Type**: `{ε : ℝ} (hε_half_neg : -1 ≤ ε / 2) (hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12)) → 12 / Real.pi * Real.arcsin (ε / 2) < 1`
- **What**: Sufficient bound `δ_right(ε) < 1` when `ε < 2 sin(π/12)`.
- **How**: From `ε/2 < sin(π/12)`, get `arcsin(ε/2) < π/12` via strict monotonicity of `Real.arcsin`; multiply by `12/π`, then field arithmetic.
- **Hypotheses**: `-1 ≤ ε/2`, `ε < 2 sin(π/12)`.
- **Uses from project**: [] (only mathlib).
- **Used by**: `pv_integral_at_rho_plus_one_tendsto` (used in `hδR_small` and downstream `hδR_lt_one`).
- **Visibility**: private
- **Lines**: 673-687
- **Notes**: none.

### `private lemma inv_mul_deriv_eq_logDeriv_sub`
- **Type**: `(H : ℝ) (c : ℂ) → (fun t => (fdBoundary_H H t - c)⁻¹ * deriv (fdBoundary_H H) t) = (fun t => deriv (fun s => fdBoundary_H H s - c) t / (fdBoundary_H H t - c))`
- **What**: Equality of functions: `(γ - c)⁻¹ · γ'` equals `(γ - c)' / (γ - c)`.
- **How**: `funext`; use `deriv_sub_const`; rewrite `div_eq_mul_inv` and commute.
- **Hypotheses**: None.
- **Uses from project**: [] (only mathlib).
- **Used by**: `pv_integral_at_rho_plus_one_tendsto` (`h_ftc`, `hint_left`, `hint_right`).
- **Visibility**: private
- **Lines**: 689-695
- **Notes**: none.

### `theorem pv_integral_at_rho_plus_one_tendsto`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) → Tendsto (fun ε => ∫ t in 0..5, if ‖γ t - ρ+1‖ > ε then (γ t - ρ+1)⁻¹ * deriv (...) t else 0) (𝓝[>] 0) (𝓝 (-(I * π/3)))` (273 lines)
- **What**: The Cauchy principal value of `1/(γ - (ρ+1))` along the H-boundary tends to `-iπ/3` as the cutoff `ε ↘ 0`.
- **How**: Applies `ContourIntegral.pv_tendsto_of_crossing_limit_asymmetric` with parameters `δ_left(ε) := ε / (H - √3/2)` (vertical segment) and `δ_right(ε) := (12/π) arcsin(ε/2)` (arc), threshold = `min (H - √3/2) (2 sin(π/12))`, antiderivative-difference `E(ε) := log(g(1-δ_L)) - log(g(1+δ_R))`. Discharges 14 obligations: positivity/smallness of the two `δ`'s, the "far" bounds on each side (norm > ε outside `[1-δ_L, 1+δ_R]`), the "near" bound (norm ≤ ε inside), the FTC identity via `ftc_logDeriv_telescope_rho_plus_one`, integrability on each side, and finally the limit `E(ε) → -iπ/3` using `arg_approach_rho'_left = π/2`, `arg_approach_rho'_right_helper = 5π/6 + δ_R π/12`, and `arc_angle_lt_epsilon` for the convergence rate.
- **Hypotheses**: `√3/2 < H`.
- **Uses from project**: `ContourIntegral.pv_tendsto_of_crossing_limit_asymmetric`, `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`, `g_rho'_norm_seg0`, `g_rho'_norm_seg0_at`, `g_rho'_norm_arc`, `g_rho'_norm_ge_seg4`, `δ_right_lt_one_aux`, `rho'_norm_gt_right_of_arc`, `norm_le_middle_rho_plus_one`, `ftc_logDeriv_telescope_rho_plus_one`, `inv_mul_deriv_eq_logDeriv_sub`, `arg_approach_rho'_left`, `arg_approach_rho'_right_helper`, `arc_angle_lt_epsilon`, `ellipticPointRhoPlusOne`.
- **Used by**: `gWN_fdBoundary_H_at_rho_plus_one`.
- **Visibility**: public
- **Lines**: 697-970
- **Notes**: >30 lines (top-level main theorem, 273 lines).

### `theorem gWN_fdBoundary_H_at_rho_plus_one`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) → generalizedWindingNumber' (fdBoundary_H H) 0 5 ellipticPointRhoPlusOne = -1/6`
- **What**: The generalized winding number of the H-boundary contour around `ρ+1 = e^{πi/3}` equals `-1/6` (corner contribution: the boundary encloses one-sixth of a full clockwise loop around the elliptic point with orbifold index 3, hence weight `1/6` and sign `-`).
- **How**: Apply `ContourIntegral.gWN_eq_neg_sixth_of_pv_tendsto`, then `convert pv_integral_at_rho_plus_one_tendsto H hH using 2`; minor `simp`/`ring`.
- **Hypotheses**: `√3/2 < H`.
- **Uses from project**: `ContourIntegral.gWN_eq_neg_sixth_of_pv_tendsto`, `pv_integral_at_rho_plus_one_tendsto`, `ellipticPointRhoPlusOne`.
- **Used by**: unused in file (public consumer outside).
- **Visibility**: public
- **Lines**: 972-978
- **Notes**: none.

---

## File Summary

- **Total declarations**: 26 (24 private auxiliary lemmas + 2 public theorems). Plus 1 attribute and 1 `noncomputable section` framing.
- **Key public API**: `pv_integral_at_rho_plus_one_tendsto` (CPV → -iπ/3 around `ρ+1`), `gWN_fdBoundary_H_at_rho_plus_one` (generalized winding number = -1/6 at `ρ+1`).
- **Unused in file**: only `gWN_fdBoundary_H_at_rho_plus_one` (the final theorem) has no in-file consumer; everything else feeds the main FTC/PV chain.
- **Sorries**: none.
- **set_options**: none.
- **Long proofs (>30 lines)**: `g_rho'_im_nonneg` (~40), `g_rho'_ne_zero` (~47), `g_rho'_slitPlane` (~34), `arg_approach_rho'_right_helper` (~60), `g_rho'_norm_arc` (~49), `ftc_logDeriv_telescope_rho_plus_one` (~230), `pv_integral_at_rho_plus_one_tendsto` (~273).
- **Purpose**: This module computes the corner weight of the generalized winding number of the fundamental-domain boundary contour `fdBoundary_H H : [0,5] → ℂ` at the elliptic point `ρ+1 = e^{iπ/3}`. It establishes the four piecewise closed-form expressions of `γ(t) - (ρ+1)`, derives sign and slit-plane membership on each piece, sets up a left-side ε-band (vertical segment, linear in `δ`) and a right-side ε-band (arc, `2 sin(δπ/12)`), telescopes the principal-value integral via FTC into a difference of two `Complex.log` values, and analyzes the boundary arguments (left → `π/2`, right → `5π/6 + δπ/12`) to show convergence to `-iπ/3`. The final theorem converts this CPV limit into the generalized winding number `-1/6`, which is exactly the orbifold corner weight at `ρ+1` used in the valence formula proof.
