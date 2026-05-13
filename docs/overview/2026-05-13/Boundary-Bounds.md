# Inventory: Boundary/Bounds.lean

### `lemma fdBoundary_H_eq_seg1_H`
- **Type**: `{H t : ℝ} (ht : t ≤ 1) : fdBoundary_H H t = fdBoundary_seg1_H H t`
- **What**: On `t ≤ 1`, the piecewise FD boundary equals segment 1.
- **How**: `simp only` unfolds `fdBoundary_H`, applies `ite_true` for `ht`, unfolds `fdBoundary_seg1_H`.
- **Hypotheses**: `t ≤ 1`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_seg1_H`.
- **Used by**: `fdBoundary_H_im_pos`, `fdBoundary_H_im_ge_sqrt3_div_2`, `fdBoundary_H_re_abs_le_half`, `fdBoundary_H_im_le_H`, `fdBoundary_im_le_heightCutoff`.
- **Visibility**: public
- **Lines**: 30–32
- **Notes**: none

### `lemma fdBoundary_H_eq_seg2_H`
- **Type**: `{t : ℝ} (H : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 2) : fdBoundary_H H t = fdBoundary_seg2_H t`
- **What**: On `(1, 2]`, FD boundary equals segment 2 (arc through ρ+1, i, ρ).
- **How**: `simp only` discharges `¬t ≤ 1` and applies `ite_true` for `ht2`, unfolds `fdBoundary_seg2_H`/`fdBoundary_seg2`.
- **Hypotheses**: `1 < t`, `t ≤ 2`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_seg2_H`, `fdBoundary_seg2`.
- **Used by**: `fdBoundary_H_im_pos`, `fdBoundary_H_im_ge_sqrt3_div_2`, `fdBoundary_H_re_abs_le_half`, `fdBoundary_H_im_le_H`, `fdBoundary_im_le_heightCutoff`.
- **Visibility**: public
- **Lines**: 34–38
- **Notes**: none

### `lemma fdBoundary_H_eq_seg3_H`
- **Type**: `{t : ℝ} (H : ℝ) (ht2 : 2 < t) (ht3 : t ≤ 3) : fdBoundary_H H t = fdBoundary_seg3_H t`
- **What**: On `(2, 3]`, FD boundary equals segment 3 of the arc.
- **How**: `simp only` discharges `¬t ≤ 1`, `¬t ≤ 2`, applies `ite_true` for `ht3`, unfolds `fdBoundary_seg3_H`/`fdBoundary_seg3`.
- **Hypotheses**: `2 < t`, `t ≤ 3`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_seg3_H`, `fdBoundary_seg3`.
- **Used by**: `fdBoundary_H_im_pos`, `fdBoundary_H_im_ge_sqrt3_div_2`, `fdBoundary_H_re_abs_le_half`, `fdBoundary_H_im_le_H`, `fdBoundary_im_le_heightCutoff`.
- **Visibility**: public
- **Lines**: 40–45
- **Notes**: none

### `lemma fdBoundary_H_eq_seg4_H`
- **Type**: `{H t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) : fdBoundary_H H t = fdBoundary_seg4_H H t`
- **What**: On `(3, 4]`, FD boundary equals segment 4 (left vertical edge).
- **How**: `simp only` discharges `¬t ≤ 1/2/3`, applies `ite_true` for `ht4`, unfolds `fdBoundary_seg4_H`.
- **Hypotheses**: `3 < t`, `t ≤ 4`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_seg4_H`.
- **Used by**: `fdBoundary_H_im_pos`, `fdBoundary_H_im_ge_sqrt3_div_2`, `fdBoundary_H_re_abs_le_half`, `fdBoundary_H_im_le_H`, `fdBoundary_im_le_heightCutoff`.
- **Visibility**: public
- **Lines**: 47–52
- **Notes**: none

### `lemma fdBoundary_H_eq_seg5_H`
- **Type**: `{H t : ℝ} (ht4 : 4 < t) : fdBoundary_H H t = fdBoundary_seg5_H H t`
- **What**: For `t > 4`, FD boundary equals segment 5 (top horizontal edge).
- **How**: `simp only` discharges `¬t ≤ 1/2/3/4`, applies `ite_false`, unfolds `fdBoundary_seg5_H`.
- **Hypotheses**: `4 < t`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_seg5_H`.
- **Used by**: `fdBoundary_H_im_pos`, `fdBoundary_H_im_ge_sqrt3_div_2`, `fdBoundary_H_re_abs_le_half`, `fdBoundary_H_im_le_H`, `fdBoundary_im_le_heightCutoff`.
- **Visibility**: public
- **Lines**: 54–58
- **Notes**: none

### `private lemma seg2_angle_in_range`
- **Type**: `{t : ℝ} (ht1 : 1 ≤ t) (ht2 : t ≤ 2) : π/3 ≤ π/3 + (t-1)*(π/2 - π/3) ∧ π/3 + (t-1)*(π/2 - π/3) ≤ 2π/3`
- **What**: The arc parameter on segment 2 lies in `[π/3, 2π/3]`.
- **How**: `nlinarith` with positivity facts `Real.pi_pos`, products bounded by `mul_nonneg`/`mul_le_mul_of_nonneg_right`.
- **Hypotheses**: `1 ≤ t ≤ 2`.
- **Uses from project**: []
- **Used by**: `fdBoundary_H_im_pos`, `fdBoundary_H_im_ge_sqrt3_div_2`, `fdBoundary_H_re_abs_le_half`.
- **Visibility**: private
- **Lines**: 60–68
- **Notes**: none

### `private lemma seg3_angle_in_range`
- **Type**: `{t : ℝ} (ht2 : 2 ≤ t) (ht3 : t ≤ 3) : π/3 ≤ π/2 + (t-2)*(2π/3 - π/2) ∧ ... ≤ 2π/3`
- **What**: The arc parameter on segment 3 lies in `[π/3, 2π/3]`.
- **How**: `nlinarith` after establishing nonnegativity of the linear interpolation term.
- **Hypotheses**: `2 ≤ t ≤ 3`.
- **Uses from project**: []
- **Used by**: `fdBoundary_H_im_pos`, `fdBoundary_H_im_ge_sqrt3_div_2`, `fdBoundary_H_re_abs_le_half`.
- **Visibility**: private
- **Lines**: 70–78
- **Notes**: none

### `private lemma sin_pos_of_angle_in_range`
- **Type**: `{θ : ℝ} (h1 : π/3 ≤ θ) (h2 : θ ≤ 2π/3) : 0 < sin θ`
- **What**: `sin θ` is strictly positive on `[π/3, 2π/3]`.
- **How**: Reduces to membership in `(0, π)` and invokes `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`.
- **Hypotheses**: `π/3 ≤ θ ≤ 2π/3`.
- **Uses from project**: `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`.
- **Used by**: `fdBoundary_H_im_pos`.
- **Visibility**: private
- **Lines**: 80–82
- **Notes**: none

### `private lemma sin_ge_sqrt3_div_2_of_angle_in_range`
- **Type**: `{θ : ℝ} (h1 : π/3 ≤ θ) (h2 : θ ≤ 2π/3) : √3/2 ≤ sin θ`
- **What**: `sin θ ≥ √3/2` on `[π/3, 2π/3]`.
- **How**: Rewrites `√3/2 = sin (π/3)` (via `Real.sin_pi_div_three.symm`); case-splits on `θ ≤ π/2` and uses `Real.sin_le_sin_of_le_of_le_pi_div_two`. For `θ > π/2`, uses `sin θ = sin (π - θ)`.
- **Hypotheses**: `π/3 ≤ θ ≤ 2π/3`.
- **Uses from project**: []
- **Used by**: `fdBoundary_H_im_ge_sqrt3_div_2`.
- **Visibility**: private
- **Lines**: 84–92
- **Notes**: none

### `private lemma abs_cos_le_half_of_angle_in_range`
- **Type**: `{θ : ℝ} (h1 : π/3 ≤ θ) (h2 : θ ≤ 2π/3) : |cos θ| ≤ 1/2`
- **What**: `|cos θ| ≤ 1/2` on the arc interval.
- **How**: Direct call to `ArcCalculus.abs_cos_le_half_of_mem_Icc`.
- **Hypotheses**: `π/3 ≤ θ ≤ 2π/3`.
- **Uses from project**: `ArcCalculus.abs_cos_le_half_of_mem_Icc`.
- **Used by**: `fdBoundary_H_re_abs_le_half`.
- **Visibility**: private
- **Lines**: 94–96
- **Notes**: none

### `private lemma seg1_H_im`
- **Type**: `{H t : ℝ} (_ht0 : 0 ≤ t) (_ht1 : t ≤ 1) : (fdBoundary_seg1_H H t).im = H - t*(H - √3/2)`
- **What**: Imaginary part of seg1 (right vertical descent from H to √3/2).
- **How**: `simp` with imaginary-part lemmas for `add_im`, `ofReal_im`, `mul_im`, `I_re`, `I_im`.
- **Hypotheses**: `0 ≤ t`, `t ≤ 1` (unused).
- **Uses from project**: `fdBoundary_seg1_H`.
- **Used by**: `fdBoundary_H_im_pos`, `fdBoundary_H_im_ge_sqrt3_div_2`, `fdBoundary_H_im_le_H`, `fdBoundary_im_le_heightCutoff`.
- **Visibility**: private
- **Lines**: 98–100
- **Notes**: none

### `private lemma seg4_H_im`
- **Type**: `{H t : ℝ} : (fdBoundary_seg4_H H t).im = √3/2 + (t-3)*(H - √3/2)`
- **What**: Imaginary part of seg4 (left vertical ascent).
- **How**: `simp` with `add_im`, `ofReal_im`, `mul_im`, `I_re`, `I_im`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg4_H`.
- **Used by**: `fdBoundary_H_im_pos`, `fdBoundary_H_im_ge_sqrt3_div_2`, `fdBoundary_H_im_le_H`, `fdBoundary_im_le_heightCutoff`.
- **Visibility**: private
- **Lines**: 102–105
- **Notes**: none

### `private lemma seg5_H_im`
- **Type**: `{H t : ℝ} : (fdBoundary_seg5_H H t).im = H`
- **What**: Top horizontal edge has constant imaginary part `H`.
- **How**: `simp` with imaginary-part unfolds.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg5_H`.
- **Used by**: `fdBoundary_H_im_pos`, `fdBoundary_H_im_ge_sqrt3_div_2`, `fdBoundary_H_im_le_H`, `fdBoundary_im_le_heightCutoff`.
- **Visibility**: private
- **Lines**: 107–108
- **Notes**: none

### `private lemma seg2_as_trig`
- **Type**: `(t : ℝ) : fdBoundary_seg2 t = ↑(cos (π/3 + (t-1)*(π/2 - π/3))) + ↑(sin ...) * I`
- **What**: Rewrites the unit-arc complex exponential parameterisation of seg2 in real cos/sin form.
- **How**: Unfolds `fdBoundary_seg2`, casts the angle via `push_cast`+`ring`, then `exp_mul_I`, `ofReal_cos`, `ofReal_sin`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg2`.
- **Used by**: `seg2_im`, `seg2_re`.
- **Visibility**: private
- **Lines**: 110–118
- **Notes**: none

### `private lemma seg3_as_trig`
- **Type**: `(t : ℝ) : fdBoundary_seg3 t = ↑(cos (π/2 + (t-2)*(2π/3 - π/2))) + ↑(sin ...) * I`
- **What**: Real cos/sin form of seg3.
- **How**: Unfold `fdBoundary_seg3`, cast angle, apply `exp_mul_I` + `ofReal_cos`/`ofReal_sin`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg3`.
- **Used by**: `seg3_im`, `seg3_re`.
- **Visibility**: private
- **Lines**: 120–130
- **Notes**: none

### `private lemma seg2_im`
- **Type**: `{t : ℝ} : (fdBoundary_seg2 t).im = sin (π/3 + (t-1)*(π/2 - π/3))`
- **What**: Imaginary part of seg2 in `sin`-form.
- **How**: Apply `seg2_as_trig`, then real/imag projection via `add_im`, `mul_im`, ring.
- **Hypotheses**: none.
- **Uses from project**: `seg2_as_trig`.
- **Used by**: `fdBoundary_H_im_pos`, `fdBoundary_H_im_ge_sqrt3_div_2`, `fdBoundary_H_im_le_H`, `fdBoundary_im_le_heightCutoff`.
- **Visibility**: private
- **Lines**: 132–135
- **Notes**: none

### `private lemma seg3_im`
- **Type**: `{t : ℝ} : (fdBoundary_seg3 t).im = sin (π/2 + (t-2)*(2π/3 - π/2))`
- **What**: Imaginary part of seg3 in `sin`-form.
- **How**: `seg3_as_trig` then projection + ring.
- **Hypotheses**: none.
- **Uses from project**: `seg3_as_trig`.
- **Used by**: `fdBoundary_H_im_pos`, `fdBoundary_H_im_ge_sqrt3_div_2`, `fdBoundary_H_im_le_H`, `fdBoundary_im_le_heightCutoff`.
- **Visibility**: private
- **Lines**: 137–142
- **Notes**: none

### `private lemma seg2_re`
- **Type**: `{t : ℝ} : (fdBoundary_seg2 t).re = cos (π/3 + (t-1)*(π/2 - π/3))`
- **What**: Real part of seg2 in `cos`-form.
- **How**: `seg2_as_trig` then real-part projection + ring.
- **Hypotheses**: none.
- **Uses from project**: `seg2_as_trig`.
- **Used by**: `fdBoundary_H_re_abs_le_half`.
- **Visibility**: private
- **Lines**: 144–147
- **Notes**: none

### `private lemma seg3_re`
- **Type**: `{t : ℝ} : (fdBoundary_seg3 t).re = cos (π/2 + (t-2)*(2π/3 - π/2))`
- **What**: Real part of seg3 in `cos`-form.
- **How**: `seg3_as_trig` then real-part projection + ring.
- **Hypotheses**: none.
- **Uses from project**: `seg3_as_trig`.
- **Used by**: `fdBoundary_H_re_abs_le_half`.
- **Visibility**: private
- **Lines**: 149–154
- **Notes**: none

### `lemma fdBoundary_H_im_pos`
- **Type**: `(H : ℝ) (hH : √3/2 < H) : ∀ t ∈ Icc 0 5, 0 < (fdBoundary_H H t).im`
- **What**: At height `H > √3/2`, the entire fixed-height FD boundary has positive imaginary part.
- **How**: Case-split on `t ≤ 1/2/3/4` and for each segment rewrite via `fdBoundary_H_eq_segK_H` and the segment imaginary-part lemma. Seg1: `nlinarith`. Seg2/Seg3: `sin_pos_of_angle_in_range` + `seg2/3_angle_in_range`. Seg4: `nlinarith`. Seg5: `linarith` from `hH`. (~25 lines.)
- **Hypotheses**: `√3/2 < H`, `t ∈ [0,5]`.
- **Uses from project**: `fdBoundary_H_eq_seg1_H` through `fdBoundary_H_eq_seg5_H`, `seg1_H_im`, `seg4_H_im`, `seg5_H_im`, `seg2_im`, `seg3_im`, `fdBoundary_seg2_H`, `fdBoundary_seg3_H`, `seg2_angle_in_range`, `seg3_angle_in_range`, `sin_pos_of_angle_in_range`.
- **Used by**: `fdBoundary_im_pos`.
- **Visibility**: public
- **Lines**: 156–179
- **Notes**: >10 lines, case split

### `lemma fdBoundary_H_im_ge_sqrt3_div_2`
- **Type**: `(H : ℝ) (hH : √3/2 ≤ H) : ∀ t ∈ Icc 0 5, √3/2 ≤ (fdBoundary_H H t).im`
- **What**: At height `H ≥ √3/2`, FD boundary imaginary part is bounded below by `√3/2`.
- **How**: Case-split on segments; Seg1/Seg4: `nlinarith`; Seg2/Seg3: `sin_ge_sqrt3_div_2_of_angle_in_range` with `seg2/3_angle_in_range`; Seg5: `hH`. (~22 lines.)
- **Hypotheses**: `√3/2 ≤ H`, `t ∈ [0,5]`.
- **Uses from project**: segment equation/imaginary lemmas, `seg2/3_angle_in_range`, `sin_ge_sqrt3_div_2_of_angle_in_range`.
- **Used by**: `fdBoundary_im_ge_sqrt3_div_2`.
- **Visibility**: public
- **Lines**: 181–203
- **Notes**: >10 lines, case split

### `private lemma seg1_H_re`
- **Type**: `{H t : ℝ} : (fdBoundary_seg1_H H t).re = 1/2`
- **What**: Real part on seg1 is constant `1/2`.
- **How**: `simp` with real-part lemmas.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg1_H`.
- **Used by**: `fdBoundary_H_re_abs_le_half`.
- **Visibility**: private
- **Lines**: 205–206
- **Notes**: none

### `private lemma seg4_H_re`
- **Type**: `{H t : ℝ} : (fdBoundary_seg4_H H t).re = -1/2`
- **What**: Real part on seg4 is constant `-1/2`.
- **How**: `simp` with real-part lemmas.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg4_H`.
- **Used by**: `fdBoundary_H_re_abs_le_half`.
- **Visibility**: private
- **Lines**: 208–209
- **Notes**: none

### `private lemma seg5_H_re`
- **Type**: `{H t : ℝ} : (fdBoundary_seg5_H H t).re = t - 9/2`
- **What**: Top edge: real part is `t - 9/2` (decreases from 1/2 to −1/2 over `t ∈ [4,5]`).
- **How**: `simp` with real-part lemmas.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg5_H`.
- **Used by**: `fdBoundary_H_re_abs_le_half`.
- **Visibility**: private
- **Lines**: 211–212
- **Notes**: none

### `lemma fdBoundary_H_re_abs_le_half`
- **Type**: `(H : ℝ) : ∀ t ∈ Icc 0 5, |Complex.re (fdBoundary_H H t)| ≤ 1/2`
- **What**: FD boundary real part is bounded by `1/2` in absolute value.
- **How**: Case-split on segments; Seg1/Seg4: `norm_num`; Seg2/Seg3: `abs_cos_le_half_of_angle_in_range`; Seg5: `abs_le` + `linarith`. (~22 lines.)
- **Hypotheses**: `t ∈ [0,5]`.
- **Uses from project**: segment equation/real lemmas, `seg2/3_angle_in_range`, `abs_cos_le_half_of_angle_in_range`.
- **Used by**: `fdBoundary_re_abs_le_half`.
- **Visibility**: public
- **Lines**: 214–236
- **Notes**: >10 lines, case split

### `lemma fdBoundary_eq_seg1`
- **Type**: `{t : ℝ} (ht : t ≤ 1) : fdBoundary t = fdBoundary_seg1 t`
- **What**: Cutoff-height-fixed FD boundary equals seg1 on `t ≤ 1`.
- **How**: `simp only` on `fdBoundary` + `ite_true`, unfold `fdBoundary_seg1`.
- **Hypotheses**: `t ≤ 1`.
- **Uses from project**: `fdBoundary`, `fdBoundary_seg1`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 238–240
- **Notes**: none

### `lemma fdBoundary_eq_seg2`
- **Type**: `{t : ℝ} (ht1 : 1 < t) (ht2 : t ≤ 2) : fdBoundary t = fdBoundary_seg2 t`
- **What**: FD boundary equals seg2 on `(1,2]`.
- **How**: `simp only` discharging `¬t ≤ 1` and `t ≤ 2`.
- **Hypotheses**: `1 < t`, `t ≤ 2`.
- **Uses from project**: `fdBoundary`, `fdBoundary_seg2`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 242–245
- **Notes**: none

### `lemma fdBoundary_eq_seg3`
- **Type**: `{t : ℝ} (ht2 : 2 < t) (ht3 : t ≤ 3) : fdBoundary t = fdBoundary_seg3 t`
- **What**: FD boundary equals seg3 on `(2,3]`.
- **How**: `simp only` discharging earlier branches via `not_le.mpr`.
- **Hypotheses**: `2 < t`, `t ≤ 3`.
- **Uses from project**: `fdBoundary`, `fdBoundary_seg3`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 247–251
- **Notes**: none

### `lemma fdBoundary_eq_seg4`
- **Type**: `{t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) : fdBoundary t = fdBoundary_seg4 t`
- **What**: FD boundary equals seg4 on `(3,4]`.
- **How**: `simp only` discharging earlier branches.
- **Hypotheses**: `3 < t`, `t ≤ 4`.
- **Uses from project**: `fdBoundary`, `fdBoundary_seg4`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 253–257
- **Notes**: none

### `lemma fdBoundary_eq_seg5`
- **Type**: `{t : ℝ} (ht4 : 4 < t) : fdBoundary t = fdBoundary_seg5 t`
- **What**: FD boundary equals seg5 on `t > 4`.
- **How**: `simp only` discharging all earlier branches.
- **Hypotheses**: `4 < t`.
- **Uses from project**: `fdBoundary`, `fdBoundary_seg5`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 259–263
- **Notes**: none

### `theorem fdBoundary_continuous`
- **Type**: `Continuous fdBoundary`
- **What**: The closed FD boundary curve is continuous on `ℝ`.
- **How**: Rewrites `fdBoundary` as `fdBoundary_H heightCutoff` via `fdBoundary_eq_fdBoundary_H` and uses the fixed-height continuity `fdBoundary_H_continuous`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_eq_fdBoundary_H`, `fdBoundary_H_continuous`, `heightCutoff`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 265–267
- **Notes**: none

### `lemma fdBoundary_im_pos`
- **Type**: `∀ t ∈ Icc 0 5, 0 < (fdBoundary t).im`
- **What**: FD boundary imaginary part is positive on `[0,5]`.
- **How**: Rewrite to `fdBoundary_H` form and apply `fdBoundary_H_im_pos` with `sqrt3_div2_lt_heightCutoff`.
- **Hypotheses**: `t ∈ [0,5]`.
- **Uses from project**: `fdBoundary_eq_fdBoundary_H`, `fdBoundary_H_im_pos`, `heightCutoff`, `sqrt3_div2_lt_heightCutoff`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 269–272
- **Notes**: none

### `lemma fdBoundary_H_im_le_H`
- **Type**: `{H : ℝ} (hH : 1 ≤ H) : ∀ t ∈ Icc 0 5, (fdBoundary_H H t).im ≤ H`
- **What**: Imaginary part of fixed-height FD boundary is bounded above by `H`.
- **How**: Case-split segments; Seg1: `nlinarith` (uses `√3/2 < H` derived via `Real.sq_sqrt`); Seg2/3: `Real.sin_le_one` then `hH`; Seg4: `nlinarith`; Seg5: rewrite to constant `H`. (~24 lines.)
- **Hypotheses**: `1 ≤ H`, `t ∈ [0,5]`.
- **Uses from project**: segment equation/imaginary lemmas, `fdBoundary_seg2_H`, `fdBoundary_seg3_H`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 274–297
- **Notes**: >10 lines, case split

### `lemma fdBoundary_im_le_heightCutoff`
- **Type**: `∀ t ∈ Icc 0 5, (fdBoundary t).im ≤ heightCutoff`
- **What**: FD boundary imaginary part bounded by the global `heightCutoff`.
- **How**: Rewrite to `fdBoundary_H`; case-split segments; use `sin_le_one + one_lt_heightCutoff` for arcs, `nlinarith` for verticals, equality for seg5. (~22 lines.)
- **Hypotheses**: `t ∈ [0,5]`.
- **Uses from project**: `fdBoundary_eq_fdBoundary_H`, segment-equation/imaginary lemmas, `heightCutoff`, `sqrt3_div2_lt_heightCutoff`, `one_lt_heightCutoff`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 299–322
- **Notes**: >10 lines, case split

### `lemma fdBoundary_re_abs_le_half`
- **Type**: `∀ t ∈ Icc 0 5, |Complex.re (fdBoundary t)| ≤ 1/2`
- **What**: FD boundary real part bounded by `1/2` in absolute value.
- **How**: Rewrites to `fdBoundary_H` and applies `fdBoundary_H_re_abs_le_half` at `heightCutoff`.
- **Hypotheses**: `t ∈ [0,5]`.
- **Uses from project**: `fdBoundary_eq_fdBoundary_H`, `fdBoundary_H_re_abs_le_half`, `heightCutoff`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 324–327
- **Notes**: none

### `lemma fdBoundary_im_ge_sqrt3_div_2`
- **Type**: `∀ t ∈ Icc 0 5, √3/2 ≤ (fdBoundary t).im`
- **What**: FD boundary imaginary part bounded below by `√3/2`.
- **How**: Rewrites to `fdBoundary_H`; applies `fdBoundary_H_im_ge_sqrt3_div_2` with `le_of_lt sqrt3_div2_lt_heightCutoff`.
- **Hypotheses**: `t ∈ [0,5]`.
- **Uses from project**: `fdBoundary_eq_fdBoundary_H`, `fdBoundary_H_im_ge_sqrt3_div_2`, `heightCutoff`, `sqrt3_div2_lt_heightCutoff`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 329–332
- **Notes**: none

### `lemma fdBoundary_passes_through_i`
- **Type**: `∃ t ∈ Icc 0 5, fdBoundary t = ellipticPointI`
- **What**: FD boundary visits the elliptic point `i` at `t = 2`.
- **How**: Witness `t = 2` and apply `fdBoundary_at_two`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary`, `ellipticPointI`, `fdBoundary_at_two`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 334–336
- **Notes**: none

### `lemma fdBoundary_passes_through_rho`
- **Type**: `∃ t ∈ Icc 0 5, fdBoundary t = ellipticPointRho`
- **What**: FD boundary visits `ρ` at `t = 3`.
- **How**: Witness `t = 3` and apply `fdBoundary_at_three`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary`, `ellipticPointRho`, `fdBoundary_at_three`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 338–340
- **Notes**: none

### `lemma fdBoundary_passes_through_rho_plus_one`
- **Type**: `∃ t ∈ Icc 0 5, fdBoundary t = ellipticPointRhoPlusOne`
- **What**: FD boundary visits `ρ + 1` at `t = 1`.
- **How**: Witness `t = 1` and apply `fdBoundary_at_one`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary`, `ellipticPointRhoPlusOne`, `fdBoundary_at_one`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 342–344
- **Notes**: none

## File Summary
- 27 declarations: 5 segment selectors `fdBoundary_H_eq_segK_H`, 5 corresponding `fdBoundary_eq_segK`, 12 private helpers, 3 main bounds (`im_pos`, `im_ge_sqrt3_div_2`, `re_abs_le_half`), `fdBoundary_continuous`, 4 cutoff-height variants (`im_pos`, `im_le_heightCutoff`, `re_abs_le_half`, `im_ge_sqrt3_div_2`, `im_le_H`), 3 "passes through" lemmas for elliptic points.
- All proofs sorry-free; no axioms beyond defaults; no `set_option`; no `TODO`.
- File entirely in `noncomputable section`.
- Five large case-split lemmas (>10 lines) handle the 5 boundary segments uniformly.
