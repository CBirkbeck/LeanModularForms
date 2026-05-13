# Inventory: `LeanModularForms/ForMathlib/ValenceFormula/WindingWeights/I.lean`

### `private lemma arg_approach_i_left`
- **Type**: `(hδ : 0 < δ) (hδ_small : δ < 1) : (fdBoundary_H H (2 - δ) - I).arg = -(δ * Real.pi / 12)`
- **What**: Argument of `γ(2-δ) - i` (left of the i-crossing on the arc) equals `-δπ/12`.
- **How**: Substitutes `fdBoundary_H_eq_arc`, sets `θ = π/2 - δπ/6`, uses double-angle: factors `cos θ + i sin θ - i` as `2 sin(δπ/12) · (cos(-δπ/12) + i sin(-δπ/12))`, then `Complex.arg_mul_cos_add_sin_mul_I`.
- **Hypotheses**: `0 < δ < 1`, `H` arbitrary.
- **Uses from project**: `fdBoundary_H_eq_arc`, `exp_real_angle_I`, `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`.
- **Used by**: `i_E_tendsto`.
- **Visibility**: private
- **Lines**: 29-66
- **Notes**: >30 lines.

### `private lemma arg_approach_i_right`
- **Type**: `(hδ : 0 < δ) (hδ_small : δ < 1) : (fdBoundary_H H (2 + δ) - I).arg = δ * Real.pi / 12 - Real.pi`
- **What**: Argument of `γ(2+δ) - i` (right of the i-crossing) equals `δπ/12 - π`.
- **How**: As left version with `θ = π/2 + δπ/6`; factors out `-1` times a unit-modulus complex of arg `δπ/12`, applies `Complex.arg_neg_eq_arg_sub_pi_of_im_pos`.
- **Hypotheses**: `0 < δ < 1`, `H` arbitrary.
- **Uses from project**: `fdBoundary_H_eq_arc`, `exp_real_angle_I`, `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`.
- **Used by**: `i_E_tendsto`.
- **Visibility**: private
- **Lines**: 68-118
- **Notes**: >30 lines.

### `private lemma g_i_norm_left`
- **Type**: `{δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : ‖fdBoundary_H H (2 - δ) - I‖ = 2 * Real.sin (δ * Real.pi / 12)`
- **What**: Distance from `γ(2-δ)` to `i` is `2 sin(δπ/12)` (chord length on the unit arc).
- **How**: Substitutes `fdBoundary_H_eq_arc`, expresses `γ(2-δ) - i` as scalar multiple of `exp(-iδπ/12)` via sum-to-product, then `norm_smul`.
- **Hypotheses**: `0 < δ < 1`.
- **Uses from project**: `fdBoundary_H_eq_arc`, `exp_real_angle_I`, `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`.
- **Used by**: `g_i_norm_arc_left`, `i_h_far`, `i_angle_bound`, `i_E_tendsto`.
- **Visibility**: private
- **Lines**: 120-148
- **Notes**: >30 lines.

### `private lemma g_i_norm_right`
- **Type**: `{δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : ‖fdBoundary_H H (2 + δ) - I‖ = 2 * Real.sin (δ * Real.pi / 12)`
- **What**: Distance from `γ(2+δ)` to `i` is `2 sin(δπ/12)`.
- **How**: Mirror of `g_i_norm_left`, factors as `-2sin(δπ/12)·exp(iδπ/12)`, `norm_smul`, `abs_neg`.
- **Hypotheses**: `0 < δ < 1`.
- **Uses from project**: `fdBoundary_H_eq_arc`, `exp_real_angle_I`, `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`.
- **Used by**: `g_i_norm_arc_right`, `i_h_far`, `i_E_tendsto`.
- **Visibility**: private
- **Lines**: 150-179
- **Notes**: >30 lines.

### `private lemma g_i_norm_ge_seg0`
- **Type**: `{t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 1 / 2 ≤ ‖fdBoundary_H H t - I‖`
- **What**: On the right vertical edge (`t ∈ [0,1]`), distance to `i` is at least `1/2`.
- **How**: Compute Re-part `= 1/2` via `fdBoundary_H_seg0`, then `|Re| ≤ ‖·‖`.
- **Hypotheses**: `0 ≤ t ≤ 1`.
- **Uses from project**: `fdBoundary_H_seg0`.
- **Used by**: `i_h_far`.
- **Visibility**: private
- **Lines**: 181-191

### `private lemma g_i_norm_ge_seg4`
- **Type**: `(H : ℝ) (hH : 1 < H) {t : ℝ} (ht4 : 4 ≤ t) (ht5 : t ≤ 5) : H - 1 ≤ ‖fdBoundary_H H t - I‖`
- **What**: On the top edge (seg5, `t ∈ [4,5]`), distance to `i` is at least `H - 1`.
- **How**: Imaginary part equals `H - 1` (via `fdBoundary_H_at_four`/`fdBoundary_H_seg4`), then `|Im| ≤ ‖·‖`.
- **Hypotheses**: `1 < H`, `4 ≤ t ≤ 5`.
- **Uses from project**: `fdBoundary_H_at_four`, `fdBoundary_H_seg4`.
- **Used by**: `i_h_far`.
- **Visibility**: private
- **Lines**: 193-208

### `private lemma g_i_slitPlane_left`
- **Type**: `{t : ℝ} (_ht0 : 0 ≤ t) (ht2 : t < 2) : fdBoundary_H H t - I ∈ slitPlane`
- **What**: For `t < 2` (before the i-crossing), `γ(t) - i` lies in the slit plane (Re > 0).
- **How**: Case `t ≤ 1`: Re = 1/2; case `1 < t < 2`: angle `θ` lies in open `(π/3, π/2)` so `cos θ > 0` via `Real.cos_pos_of_mem_Ioo`.
- **Hypotheses**: `0 ≤ t < 2`.
- **Uses from project**: `fdBoundary_H_seg0`, `fdBoundary_H_seg1`, `exp_real_angle_I`.
- **Used by**: `ftc_logDeriv_telescope_i` (slit-plane conditions on h₀, h₁).
- **Visibility**: private
- **Lines**: 210-229

### `private lemma g_i_seg3_value`
- **Type**: `{t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) : fdBoundary_H H t - I = -1/2 + ↑(Real.sqrt 3 / 2 - 1 + (t - 3) * (H - Real.sqrt 3 / 2)) * I`
- **What**: Explicit form of `γ(t) - i` on seg3 (`t ∈ (3,4]`).
- **How**: Unfold `fdBoundary_H_seg3`, push_cast, ring.
- **Hypotheses**: `3 < t ≤ 4`.
- **Uses from project**: `fdBoundary_H_seg3`.
- **Used by**: `g_i_norm_ge_seg3`, `g_i_at_t₀`, `g_i_seg3_im_neg`, `g_i_seg3_im_pos`, `g_i_ne_zero_seg3`, `ftc_logDeriv_telescope_i`.
- **Visibility**: private
- **Lines**: 231-236

### `private lemma g_i_seg4_value`
- **Type**: `{t : ℝ} (ht4 : 4 < t) : fdBoundary_H H t - I = ↑(t - 9/2) + ↑(H - 1) * I`
- **What**: Explicit form of `γ(t) - i` on seg5 (top horizontal, `t > 4`).
- **How**: Unfold `fdBoundary_H_seg4` (segment numbering), push_cast, ring.
- **Hypotheses**: `4 < t`.
- **Uses from project**: `fdBoundary_H_seg4`.
- **Used by**: `ftc_logDeriv_telescope_i`.
- **Visibility**: private
- **Lines**: 238-242

### `private lemma g_i_norm_ge_seg3`
- **Type**: `{t : ℝ} (ht3 : 3 ≤ t) (ht4 : t ≤ 4) : 1 / 2 ≤ ‖fdBoundary_H H t - I‖`
- **What**: On seg3 (left vertical, `t ∈ [3,4]`), distance to `i` is at least `1/2`.
- **How**: Re-part equals `-1/2` at `t = 3` (via `fdBoundary_H_at_three_eq_rho`) and for `t > 3` (via `g_i_seg3_value`), then `|Re| ≤ ‖·‖`.
- **Hypotheses**: `3 ≤ t ≤ 4`.
- **Uses from project**: `fdBoundary_H_at_three_eq_rho`, `ellipticPointRho`, `g_i_seg3_value`.
- **Used by**: `i_h_far`.
- **Visibility**: private
- **Lines**: 244-260
- **Notes**: 17 lines.

### `private lemma g_i_slitPlane_arc_right`
- **Type**: `{t : ℝ} (ht2 : 2 < t) (ht3 : t ≤ 3) : fdBoundary_H H t - I ∈ slitPlane`
- **What**: For `t ∈ (2,3]` (right of i-crossing on arc), `γ(t) - i` lies in slit plane (Im ≠ 0).
- **How**: At `t = 3`: Im < 0 by sqrt-3 algebra; for `2 < t < 3`: angle in `(π/2, π)`, so `cos θ < 0` (via `Real.cos_neg_of_pi_div_two_lt_of_lt`) and `sin θ < 1`.
- **Hypotheses**: `2 < t ≤ 3`.
- **Uses from project**: `fdBoundary_H_at_three_eq_rho`, `fdBoundary_H_eq_arc`, `exp_real_angle_I`, `ellipticPointRho`.
- **Used by**: `ftc_logDeriv_telescope_i`.
- **Visibility**: private
- **Lines**: 262-284
- **Notes**: >20 lines; uses `push Not`.

### `private lemma g_i_norm_arc_right`
- **Type**: `{t : ℝ} (ht2 : 2 < t) (ht3 : t < 3) : ‖fdBoundary_H H t - I‖ = 2 * Real.sin ((t - 2) * Real.pi / 12)`
- **What**: Norm formula on arc right of crossing: `2 sin((t-2)π/12)`.
- **How**: Reparametrize `δ = t - 2` and apply `g_i_norm_right`.
- **Hypotheses**: `2 < t < 3`.
- **Uses from project**: `g_i_norm_right`.
- **Used by**: `i_h_far`, `i_h_near`.
- **Visibility**: private
- **Lines**: 286-289

### `private lemma g_i_norm_arc_left`
- **Type**: `{t : ℝ} (ht1 : 1 < t) (ht2 : t < 2) : ‖fdBoundary_H H t - I‖ = 2 * Real.sin ((2 - t) * Real.pi / 12)`
- **What**: Norm formula on arc left of crossing: `2 sin((2-t)π/12)`.
- **How**: Reparametrize `δ = 2 - t` and apply `g_i_norm_left`.
- **Hypotheses**: `1 < t < 2`.
- **Uses from project**: `g_i_norm_left`.
- **Used by**: `i_h_far`, `i_h_near`.
- **Visibility**: private
- **Lines**: 291-294

### `private noncomputable def t₀_i`
- **Type**: `(H : ℝ) : ℝ := 3 + (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2)`
- **What**: Parameter `t` along seg3 at which `γ(t) - i` is real (Im = 0), i.e., the branch-cut crossing time.
- **How**: Definition (linear-affine inversion to solve for Im of `g_i_seg3_value` = 0).
- **Hypotheses**: None (formal definition).
- **Uses from project**: []
- **Used by**: `t₀_i_gt_three`, `t₀_i_lt_four`, `g_i_at_t₀`, `g_i_seg3_im_neg`, `g_i_seg3_im_pos`, `ftc_logDeriv_telescope_i`.
- **Visibility**: private
- **Lines**: 296-297

### `private lemma t₀_i_gt_three`
- **Type**: `(hH : 1 < H) : 3 < t₀_i H`
- **What**: The branch-cut crossing time satisfies `t₀ > 3`.
- **How**: Numerator `1 - √3/2 > 0` and denominator `H - √3/2 > 0` give positive ratio.
- **Hypotheses**: `1 < H`.
- **Uses from project**: `t₀_i`.
- **Used by**: `g_i_at_t₀`, `g_i_seg3_im_pos`, `ftc_logDeriv_telescope_i`.
- **Visibility**: private
- **Lines**: 299-305

### `private lemma t₀_i_lt_four`
- **Type**: `(hH : 1 < H) : t₀_i H < 4`
- **What**: The branch-cut crossing time satisfies `t₀ < 4`.
- **How**: `(1 - √3/2) / (H - √3/2) < 1` because `1 - √3/2 < H - √3/2` (from `H > 1`).
- **Hypotheses**: `1 < H`.
- **Uses from project**: `t₀_i`.
- **Used by**: `g_i_at_t₀`, `g_i_seg3_im_neg`, `ftc_logDeriv_telescope_i`.
- **Visibility**: private
- **Lines**: 307-315

### `private lemma g_i_at_t₀`
- **Type**: `(hH : 1 < H) : fdBoundary_H H (t₀_i H) - I = -1/2`
- **What**: At the crossing parameter `t₀`, `γ(t₀) - i = -1/2` (real, negative).
- **How**: `g_i_seg3_value` at `t = t₀`; the imaginary linear-affine term vanishes by definition of `t₀_i` (`div_mul_cancel₀`).
- **Hypotheses**: `1 < H`.
- **Uses from project**: `t₀_i`, `t₀_i_gt_three`, `t₀_i_lt_four`, `g_i_seg3_value`.
- **Used by**: `ftc_logDeriv_telescope_i`.
- **Visibility**: private
- **Lines**: 317-330

### `private lemma g_i_seg3_im_neg`
- **Type**: `{t : ℝ} (ht3 : 3 < t) (ht_t0 : t < t₀_i H) (hH : 1 < H) : (fdBoundary_H H t - I).im < 0`
- **What**: On seg3 before `t₀`, the imaginary part of `γ(t) - i` is negative.
- **How**: From `g_i_seg3_value`, `(t - 3)(H - √3/2)` increases linearly; at `t₀` equals `1 - √3/2`, so for `t < t₀` the sum `√3/2 - 1 + …` is negative.
- **Hypotheses**: `3 < t < t₀_i H`, `1 < H`.
- **Uses from project**: `t₀_i`, `g_i_seg3_value`, `t₀_i_lt_four`.
- **Used by**: `ftc_logDeriv_telescope_i` (im-neg interior).
- **Visibility**: private
- **Lines**: 332-347
- **Notes**: 16 lines.

### `private lemma g_i_seg3_im_pos`
- **Type**: `{t : ℝ} (ht_t0 : t₀_i H < t) (ht4 : t ≤ 4) (hH : 1 < H) : 0 < (fdBoundary_H H t - I).im`
- **What**: On seg3 after `t₀`, the imaginary part is positive.
- **How**: Mirror of `g_i_seg3_im_neg`.
- **Hypotheses**: `t₀_i H < t ≤ 4`, `1 < H`.
- **Uses from project**: `t₀_i`, `g_i_seg3_value`, `t₀_i_gt_three`.
- **Used by**: `ftc_logDeriv_telescope_i`.
- **Visibility**: private
- **Lines**: 349-364
- **Notes**: 16 lines.

### `private lemma g_i_ne_zero_seg3`
- **Type**: `{t : ℝ} (ht3 : 3 ≤ t) (ht4 : t ≤ 4) : fdBoundary_H H t - I ≠ 0`
- **What**: `γ(t) ≠ i` for `t ∈ [3,4]`.
- **How**: Real-part `= -1/2 ≠ 0` (at `t = 3` via `fdBoundary_H_at_three_eq_rho`; for `t > 3` via `g_i_seg3_value`).
- **Hypotheses**: `3 ≤ t ≤ 4`.
- **Uses from project**: `fdBoundary_H_at_three_eq_rho`, `ellipticPointRho`, `g_i_seg3_value`.
- **Used by**: `ftc_logDeriv_telescope_i`.
- **Visibility**: private
- **Lines**: 366-382
- **Notes**: 17 lines.

### `private lemma log_neg_eq_add_pi_I`
- **Type**: `{z : ℂ} (_hz_ne : z ≠ 0) (hz_im : z.im < 0) : Complex.log (-z) = Complex.log z + ↑Real.pi * I`
- **What**: Branch jump: `log(-z) = log(z) + iπ` when `Im z < 0`.
- **How**: Expand `Complex.log` definition, use `Complex.arg_neg_eq_arg_add_pi_of_im_neg`, simplify.
- **Hypotheses**: `z ≠ 0`, `Im z < 0`.
- **Uses from project**: []
- **Used by**: `ftc_logDeriv_telescope_i`.
- **Visibility**: private
- **Lines**: 384-391

### `private lemma ftc_logDeriv_telescope_i`
- **Type**: `(H : ℝ) (hH : 1 < H) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : <triple: integrability on [0, 2-δ], integrability on [2+δ, 5], and ∫_0^{2-δ} g'/g + ∫_{2+δ}^5 g'/g = log(g(2-δ)) - log(g(2+δ)) - 2πi>`
- **What**: FTC telescope for `g(t) = γ(t) - i` punching out the i-crossing at `t = 2`, with branch correction `-2πi` from crossing the cut on seg3 at `t₀`.
- **How**: Decompose `g` piecewise into smooth pieces `h₀, h₁, h₂, h₃` on `[0,1], [1,3], [3,4], [4,5]`; apply `ftc_log_pieceFM` / `ftc_log_piece_lower` / `ftc_log_piece_upper` to each; the branch jump at `t = 3` adds `+iπ` (via `log_neg_eq_add_pi_I`) and at `t₀` adds another `-iπ` (since `g(t₀) = -1/2`); together sum to `-2πi`. Uses `intervalIntegral.integral_add_adjacent_intervals` to concatenate, closes via `g(0) = g(5)`.
- **Hypotheses**: `1 < H`, `0 < δ < 1`.
- **Uses from project**: `fdBoundary_H_seg0`, `fdBoundary_H_eq_arc`, `fdBoundary_H_at_one_eq_rho_plus_one`, `ellipticPointRhoPlusOne`, `fdBoundary_H_at_three_eq_rho`, `ellipticPointRho`, `g_i_seg3_value`, `g_i_seg4_value`, `t₀_i`, `t₀_i_gt_three`, `t₀_i_lt_four`, `g_i_at_t₀`, `g_i_slitPlane_left`, `g_i_slitPlane_arc_right`, `g_i_seg3_im_neg`, `g_i_seg3_im_pos`, `g_i_ne_zero_seg3`, `exp_real_angle_I`, `cos_two_pi_div_three`, `sin_two_pi_div_three`, `ftc_log_pieceFM`, `ftc_log_piece_lower`, `ftc_log_piece_upper`, `fdBoundary_H_closed`, `fdBoundary_H_at_four`, `log_neg_eq_add_pi_I`.
- **Used by**: `i_ftc_integrability`.
- **Visibility**: private
- **Lines**: 393-695
- **Notes**: 303 lines, very long FTC telescope; main mathematical core. Key lemmas: `ftc_log_pieceFM`, `ftc_log_piece_lower`, `ftc_log_piece_upper` (from project), `intervalIntegral.integral_add_adjacent_intervals`, `log_neg_eq_add_pi_I`.

### `private lemma i_h_far`
- **Type**: `(H : ℝ) (hH : 1 < H) : let threshold := min(min(min(1/2, H-1), 2sin(π/12)), 1); ∀ ε ∈ (0, threshold), ∀ t ∈ [0,5], (12/π · arcsin(ε/2) < |t - 2|) → ε < ‖γ(t) - i‖`
- **What**: Far estimate: if `t` is more than `δ(ε) = 12/π · arcsin(ε/2)` away from `t = 2`, then the distance from `γ(t)` to `i` exceeds `ε`.
- **How**: Split into segments. On seg0 and seg3: bound by `1/2 > ε`. On seg4: bound by `H - 1 > ε`. On arcs: use `Real.sin_lt_sin_of_lt_of_le_pi_div_two` against `g_i_norm_left`/`g_i_norm_right`.
- **Hypotheses**: `1 < H`.
- **Uses from project**: `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`, `g_i_norm_left`, `g_i_norm_right`, `g_i_norm_ge_seg0`, `g_i_norm_arc_left`, `g_i_norm_arc_right`, `g_i_norm_ge_seg3`, `g_i_norm_ge_seg4`.
- **Used by**: `pv_integral_at_i_tendsto`.
- **Visibility**: private
- **Lines**: 697-776
- **Notes**: >70 lines; structural case split.

### `private lemma i_h_near`
- **Type**: `(H : ℝ) : let threshold := min(min(min(1/2, H-1), 2sin(π/12)), 1); ∀ ε ∈ (0, threshold), ∀ t, |t - 2| ≤ 12/π · arcsin(ε/2) → ‖γ(t) - i‖ ≤ ε`
- **What**: Near estimate: if `t` is within `δ(ε)` of `2`, then `‖γ(t) - i‖ ≤ ε`.
- **How**: At `t = 2`: `γ(2) = i` (via `fdBoundary_H_at_two_eq_I`), so norm = 0. Otherwise reduces to monotonicity of `Real.sin` on `[0, π/2]` via `g_i_norm_arc_left`/`g_i_norm_arc_right` and `Real.sin_le_sin_of_le_of_le_pi_div_two`.
- **Hypotheses**: `H` arbitrary.
- **Uses from project**: `fdBoundary_H_at_two_eq_I`, `g_i_norm_arc_left`, `g_i_norm_arc_right`.
- **Used by**: `pv_integral_at_i_tendsto`.
- **Visibility**: private
- **Lines**: 778-843
- **Notes**: >60 lines, monotonicity case split.

### `private lemma i_angle_bound`
- **Type**: `{δ ε : ℝ} (H : ℝ) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (h_norm_L : ‖γ(2-δ) - i‖ = ε) : δ * Real.pi / 12 < ε`
- **What**: When the norm at `2-δ` equals `ε`, the angle parameter `δπ/12` is bounded by `ε`.
- **How**: From `2 sin(x) = ε` (via `g_i_norm_left`) and `sin x > x - x³/4 > x/2` for `0 < x ≤ 1` (`Real.sin_gt_sub_cube`), so `ε > 2 · x/2 = x = δπ/12`.
- **Hypotheses**: `0 < δ < 1`, norm equation holds.
- **Uses from project**: `g_i_norm_left`.
- **Used by**: `i_E_tendsto`.
- **Visibility**: private
- **Lines**: 845-857
- **Notes**: 13 lines.

### `private lemma i_delta_lt_one`
- **Type**: `{ε : ℝ} (hε_pos : 0 < ε) (hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12)) : 12 / Real.pi * Real.arcsin (ε / 2) < 1`
- **What**: For `ε < 2 sin(π/12)`, the inverse-radius `δ(ε) = 12/π · arcsin(ε/2)` is less than 1.
- **How**: `arcsin(ε/2) < arcsin(sin(π/12)) = π/12` via monotonicity (`Real.arcsin_lt_arcsin`), then multiply by `12/π`.
- **Hypotheses**: `0 < ε < 2 sin(π/12)`.
- **Uses from project**: `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`.
- **Used by**: `i_ftc_integrability`, `i_E_tendsto`, `pv_integral_at_i_tendsto`.
- **Visibility**: private
- **Lines**: 861-878

### `private lemma i_ftc_integrability`
- **Type**: `(H : ℝ) (hH : 1 < H) {ε : ℝ} (hε_pos : 0 < ε) (hε_lt_2sin : ε < 2 sin(π/12)) : let δ := 12 / Real.pi * Real.arcsin (ε / 2); <triple: integrability on [0, 2-δ] and [2+δ, 5], plus sum = log(γ(2-δ)-i) - log(γ(2+δ)-i) - 2πi> for the integrand (γ-i)⁻¹·γ'`
- **What**: Recast `ftc_logDeriv_telescope_i` with integrand `(γ-i)⁻¹·γ'` instead of `γ'/γ` (so the FTC fits the form expected by `pv_tendsto_of_crossing_limit`).
- **How**: Show pointwise equality `(γ-i)⁻¹·γ' = (deriv(s ↦ γ(s)-i))/(γ-i)` via `deriv_sub_const` and `div_eq_mul_inv`, then transport `ftc_logDeriv_telescope_i` through `intervalIntegrable_congr`.
- **Hypotheses**: `1 < H`, `0 < ε < 2 sin(π/12)`.
- **Uses from project**: `i_delta_lt_one`, `ftc_logDeriv_telescope_i`.
- **Used by**: `pv_integral_at_i_tendsto`.
- **Visibility**: private
- **Lines**: 882-907

### `private lemma i_E_tendsto`
- **Type**: `(H : ℝ) (_ : 1 < H) (threshold : ℝ) (hthresh_pos : 0 < threshold) (hthresh_le_2sin : threshold ≤ 2 sin(π/12)) (hthresh_le_one : threshold ≤ 1) : Tendsto (E ε := log(γ(2-δ(ε))-i) - log(γ(2+δ(ε))-i) - 2πi) (𝓝[>] 0) (𝓝 (-(I·π)))`
- **What**: The log-difference correction `E(ε) → -iπ` as `ε ↓ 0` (because the two args approach `0` and `-π` respectively).
- **How**: Compute `E(ε) - (-iπ)` explicitly as `-((δπ/6) i)` using `arg_approach_i_left/right` and `log_re`/`log_im`; bound `|·| ≤ ε`-style via `i_angle_bound`, conclude via `Metric.tendsto_nhdsWithin_nhds`.
- **Hypotheses**: `1 < H`, threshold bounds.
- **Uses from project**: `i_delta_lt_one`, `g_i_norm_left`, `g_i_norm_right`, `i_angle_bound`, `arg_approach_i_left`, `arg_approach_i_right`.
- **Used by**: `pv_integral_at_i_tendsto`.
- **Visibility**: private
- **Lines**: 910-973
- **Notes**: >60 lines.

### `theorem pv_integral_at_i_tendsto`
- **Type**: `(H : ℝ) (hH : 1 < H) : Tendsto (fun ε => ∫ t in 0..5, if ‖γ(t) - i‖ > ε then (γ(t) - i)⁻¹ * deriv(s ↦ γ(s) - i) t else 0) (𝓝[>] 0) (𝓝 (-(I · π)))`
- **What**: The Cauchy principal value integral of `1/(γ - i) · γ'` on the contour `γ = fdBoundary_H H` (cut out by `ε`-balls around `i`) tends to `-iπ`.
- **How**: Wires through `ContourIntegral.pv_tendsto_of_crossing_limit` at `t₀ = 2`, `δ(ε) = 12/π · arcsin(ε/2)`, `E(ε) =` log-difference; supplies the eight hypotheses (`δ > 0`, `δ < min(2, 3)`, far/near norm estimates `i_h_far`/`i_h_near`, FTC integrability/identity from `i_ftc_integrability`, and limit from `i_E_tendsto`); a tiny `deriv_sub_const` rewrite swaps `γ'` for `(γ-I)'`.
- **Hypotheses**: `1 < H`.
- **Uses from project**: `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`, `i_delta_lt_one`, `i_h_far`, `i_h_near`, `i_ftc_integrability`, `i_E_tendsto`, `ContourIntegral.pv_tendsto_of_crossing_limit`.
- **Used by**: `gWN_fdBoundary_H_at_i`.
- **Visibility**: public
- **Lines**: 982-1061
- **Notes**: >70 lines.

### `theorem gWN_fdBoundary_H_at_i`
- **Type**: `(H : ℝ) (hH : 1 < H) : generalizedWindingNumber' (fdBoundary_H H) 0 5 I = -1/2`
- **What**: The generalized winding number of `fdBoundary_H H` around `i` is `-1/2` (since `i` sits on the arc, contributing half-residue weight, with sign convention for clockwise contour and `H > 1`).
- **How**: `ContourIntegral.gWN_eq_neg_half_of_pv_tendsto` applied to `pv_integral_at_i_tendsto`; the convert rewrites the cut-out condition.
- **Hypotheses**: `1 < H`.
- **Uses from project**: `ContourIntegral.gWN_eq_neg_half_of_pv_tendsto`, `pv_integral_at_i_tendsto`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 1068-1073

## File Summary

- **Total declarations**: 25 (1 noncomputable def, 22 private lemmas, 2 public theorems).
- **Key API**: `pv_integral_at_i_tendsto` and `gWN_fdBoundary_H_at_i` — public Main theorems showing PV integral of `(z - i)⁻¹` along the rectangular fundamental-domain boundary (height `H`) tends to `-iπ`, hence `gWN = -1/2` at `i`.
- **Unused in file**: `gWN_fdBoundary_H_at_i` is the public consumer-facing API (used elsewhere in the project).
- **Sorries**: none.
- **set_options**: none (only `attribute [local instance] Classical.propDecidable`).
- **Long proofs (>30 lines)**: `arg_approach_i_left` (~38 lines), `arg_approach_i_right` (~50 lines), `g_i_norm_left` (~28), `g_i_norm_right` (~29), `g_i_slitPlane_arc_right` (23), `ftc_logDeriv_telescope_i` (303 — file's main mathematical core), `i_h_far` (80), `i_h_near` (66), `i_E_tendsto` (64), `pv_integral_at_i_tendsto` (80).
- **Purpose**: Computes the contribution of the elliptic fixed point `i` to the winding-number side of the valence formula on `SL₂(ℤ)`. The contour `fdBoundary_H H` (a closed piecewise-smooth rectangle with the arc `|z| = 1` on the bottom) passes through `i` at parameter `t = 2`. The file establishes that the Cauchy principal value `lim_{ε → 0} ∮_{|γ - i| > ε} (γ - i)⁻¹ γ' dt` equals `-iπ`, which (with the project's sign convention) translates to a generalized winding number of `-1/2` at `i`. The proof packages a piecewise FTC for `log(γ(t) - i)` accounting for the branch-cut crossing on seg3 at the parameter `t₀_i` (where the imaginary part of `γ - i` vanishes); it then deploys `ContourIntegral.pv_tendsto_of_crossing_limit` from the project's crossing-limit infrastructure with `δ(ε) = (12/π) arcsin(ε/2)` (the arc-length inverse of the chord-norm formula `2 sin(δπ/12)`).
