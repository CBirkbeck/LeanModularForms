# Inventory: `WindingWeights/Rho.lean`

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ValenceFormula/WindingWeights/Rho.lean`

Imports:
- `LeanModularForms.ForMathlib.ValenceFormula.WindingWeights.Common` (gives `fdBoundary_H`, `fdBoundary_H_seg0`–`seg4`, `fdBoundary_H_eq_arc`, `fdBoundary_H_at_three_eq_rho`, `fdBoundary_H_at_four`, `fdBoundary_H_at_one_eq_rho_plus_one`, `fdBoundary_H_closed`, `ellipticPointRho`, `ellipticPointRho'`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`, `exp_real_angle_I`, `cos_two_pi_div_three`, `sin_two_pi_div_three`, `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`, `ftc_log_pieceFM`).
- `LeanModularForms.ForMathlib.ContourIntegral.WindingNumber` (gives `generalizedWindingNumber'`, `ContourIntegral.gWN_eq_neg_sixth_of_pv_tendsto`).
- `LeanModularForms.ForMathlib.ContourIntegral.CrossingLimit` (gives `ContourIntegral.pv_tendsto_of_crossing_limit_asymmetric`).

Header sets `attribute [local instance] Classical.propDecidable` and declares `noncomputable section` (closed at line 1136). No `set_option`, no `axiom`, no `sorry`, no `TODO` strings.

---

### `theorem fdBoundary_H_sub_rho_seg0_re`
- **Type**: `(H : ℝ) {t : ℝ} (ht : t ≤ 1) : (fdBoundary_H H t - ellipticPointRho).re = 1`
- **What**: On segment 0 (the descent `t ∈ [0,1]`), the real part of `γ(t) − ρ` equals 1.
- **How**: Rewrite `fdBoundary_H H t` using `fdBoundary_H_seg0`, unfold `ellipticPointRho`/`ellipticPointRho'`, then `simp` the algebra of `Complex.re` and `ring`.
- **Hypotheses**: `t ≤ 1`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_seg0`, `ellipticPointRho`, `ellipticPointRho'`.
- **Used by**: `fdBoundary_H_sub_rho_seg0_slitPlane`, `g_norm_ge_one_seg0`.
- **Visibility**: public.
- **Lines**: 29–37.

### `theorem fdBoundary_H_sub_rho_seg0_slitPlane`
- **Type**: `(H : ℝ) {t : ℝ} (ht : t ≤ 1) : fdBoundary_H H t - ellipticPointRho ∈ slitPlane`
- **What**: On segment 0, `γ(t) − ρ` avoids the negative real axis (so `Complex.log` is well-defined there).
- **How**: From `Complex.mem_slitPlane_iff` it suffices to show real part is positive; use `fdBoundary_H_sub_rho_seg0_re` to reduce to `1 > 0`.
- **Hypotheses**: `t ≤ 1`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_sub_rho_seg0_re`, `ellipticPointRho`.
- **Used by**: `fdBoundary_H_sub_rho_slitPlane`.
- **Visibility**: public.
- **Lines**: 39–44.

### `theorem fdBoundary_H_sub_rho_seg1_re`
- **Type**: `(H : ℝ) {t : ℝ} (ht1 : 1 < t) (ht2 : t ≤ 2) : (fdBoundary_H H t - ellipticPointRho).re > 0`
- **What**: On segment 1 (arc from `i` to `i·e^{iπ/2}`, parameterized by `θ ∈ [π/3, π/2]`), the real part `cos θ + 1/2` is in `[1/2, 1]`, hence positive.
- **How**: Rewrite with `fdBoundary_H_seg1`, `exp_real_angle_I`. Substitute `θ := π/3 + (t−1)(π/2 − π/3)` and use `Real.cos_nonneg_of_mem_Icc` to bound `cos θ ≥ 0`, then `linarith`.
- **Hypotheses**: `1 < t ≤ 2`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_seg1`, `ellipticPointRho`, `ellipticPointRho'`, `exp_real_angle_I`.
- **Used by**: `fdBoundary_H_sub_rho_slitPlane`.
- **Visibility**: public.
- **Lines**: 48–61.

### `theorem fdBoundary_H_sub_rho_seg2_re`
- **Type**: `(H : ℝ) {t : ℝ} (ht2 : 2 < t) (ht3 : t < 3) : (fdBoundary_H H t - ellipticPointRho).re > 0`
- **What**: On segment 2 (arc, `θ ∈ (π/2, 2π/3)`), `cos θ ∈ (−1/2, 0)`, so the real part `cos θ + 1/2 ∈ (0, 1/2)` is positive.
- **How**: Rewrite via `fdBoundary_H_seg2`, set `θ := π/2 + (t−2)(2π/3 − π/2)`, push `exp_real_angle_I`. Use `Real.cos_lt_cos_of_nonneg_of_le_pi` with `cos(2π/3) = −1/2` and `θ < 2π/3` to conclude `cos θ > −1/2`, then `linarith`.
- **Hypotheses**: `2 < t < 3`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_seg2`, `ellipticPointRho`, `ellipticPointRho'`, `exp_real_angle_I`.
- **Used by**: `fdBoundary_H_sub_rho_slitPlane`.
- **Visibility**: public.
- **Lines**: 65–87.

### `theorem fdBoundary_H_sub_rho_seg3_slitPlane`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) : fdBoundary_H H t - ellipticPointRho ∈ slitPlane`
- **What**: On segment 3 (vertical from `ρ` up), `γ(t) − ρ = (t − 3)(H − √3/2)·i` is purely imaginary with positive imaginary part, hence in slit plane.
- **How**: Rewrite via `fdBoundary_H_seg3`, push casts, compute the imaginary part with `nlinarith` using `hH`.
- **Hypotheses**: `H > √3/2`, `3 < t ≤ 4`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_seg3`, `ellipticPointRho`, `ellipticPointRho'`.
- **Used by**: `fdBoundary_H_sub_rho_slitPlane`.
- **Visibility**: public.
- **Lines**: 90–104.

### `theorem fdBoundary_H_sub_rho_seg4_slitPlane`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht4 : 4 < t) (_ht5 : t ≤ 5) : fdBoundary_H H t - ellipticPointRho ∈ slitPlane`
- **What**: On segment 4 (horizontal at height `H`), `γ(t) − ρ = (t − 4) + (H − √3/2)·i` has imaginary part `H − √3/2 > 0`.
- **How**: Rewrite via `fdBoundary_H_seg4`, then take the imaginary side of `Complex.mem_slitPlane_iff` and conclude by `linarith` from `hH`.
- **Hypotheses**: `H > √3/2`, `4 < t ≤ 5`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_seg4`, `ellipticPointRho`, `ellipticPointRho'`.
- **Used by**: `fdBoundary_H_sub_rho_slitPlane`.
- **Visibility**: public.
- **Lines**: 107–123.

### `theorem fdBoundary_H_sub_rho_slitPlane`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 5) (hne : t ≠ 3) : fdBoundary_H H t - ellipticPointRho ∈ slitPlane`
- **What**: Combined statement: `γ(t) − ρ` lies in the slit plane for every `t ∈ [0,5]` except `t = 3` (where the curve passes through `ρ`).
- **How**: Case-splits on `t ≤ 1`, `t ≤ 2`, `t < 3`, `t > 3`, `t ≤ 4`. Uses `fdBoundary_H_sub_rho_seg0_slitPlane`, `fdBoundary_H_sub_rho_seg1_re`, `fdBoundary_H_sub_rho_seg2_re`, `fdBoundary_H_sub_rho_seg3_slitPlane`, `fdBoundary_H_sub_rho_seg4_slitPlane`; the `t = 3` case contradicts `hne`.
- **Hypotheses**: `H > √3/2`, `t ∈ [0,5]`, `t ≠ 3`.
- **Uses from project**: `fdBoundary_H`, `ellipticPointRho`, `fdBoundary_H_sub_rho_seg0_slitPlane`, `fdBoundary_H_sub_rho_seg1_re`, `fdBoundary_H_sub_rho_seg2_re`, `fdBoundary_H_sub_rho_seg3_slitPlane`, `fdBoundary_H_sub_rho_seg4_slitPlane`.
- **Used by**: `fdBoundary_H_eq_rho_iff`, `ftc_logDeriv_telescope_rho` (in slit-plane premises for each piece).
- **Visibility**: public.
- **Lines**: 126–139.

### `theorem fdBoundary_H_eq_rho_iff`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 5) : fdBoundary_H H t = ellipticPointRho ↔ t = 3`
- **What**: `ρ` is hit by `γ` exactly at `t = 3` on the parameter interval `[0,5]`.
- **How**: `←` uses `fdBoundary_H_at_three_eq_rho`. `→` contrapositive: if `γ(t) = ρ` and `t ≠ 3`, then `0 ∈ slitPlane` by `fdBoundary_H_sub_rho_slitPlane`, contradicting `Complex.zero_notMem_slitPlane`.
- **Hypotheses**: `H > √3/2`, `t ∈ [0,5]`.
- **Uses from project**: `fdBoundary_H`, `ellipticPointRho`, `fdBoundary_H_sub_rho_slitPlane`, `fdBoundary_H_at_three_eq_rho`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 142–152.

### `private lemma arg_approach_rho_left_helper`
- **Type**: `(hδ : 0 < δ) (hδ_small : δ < 1) : (fdBoundary_H H (3 - δ) - ellipticPointRho).arg = Real.pi / 6 - δ * Real.pi / 12`
- **What**: On the left approach to `ρ` along segment 2, the argument of `γ(3 − δ) − ρ` equals `π/6 − δπ/12` exactly.
- **How**: Substitute the seg2 parameterisation with `θ := 2π/3 − δπ/6`. Rewrite `cos θ`, `sin θ` using the shifts `cos(π/2 + x) = −sin x`, `sin(π/2 + x) = cos x`. Combine via sum-to-product identities `Real.sin_sub_sin`, `Real.cos_sub_cos` and `nlinarith` to factor `(γ(3 − δ) − ρ) = 2·sin(δπ/12)·(cos(π/6 − δπ/12) + sin(π/6 − δπ/12)·I)`. Finally apply `Complex.arg_mul_cos_add_sin_mul_I` with positivity from `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi` and `nlinarith` bounds.
- **Hypotheses**: `0 < δ < 1` (so `3 − δ` lies on segment 2).
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_seg2`, `ellipticPointRho`, `ellipticPointRho'`, `exp_real_angle_I`, `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`.
- **Used by**: `arg_approach_rho_left`, `pv_log_limit_at_rho`.
- **Visibility**: private.
- **Lines**: 154–209.
- **Notes**: 56-line proof; the sum-to-product chain is reused inside `g_norm_seg2` and `g_norm_arc`.

### `theorem arg_approach_rho_left`
- **Type**: `Tendsto (fun δ => (fdBoundary_H H (3 - δ) - ellipticPointRho).arg) (𝓝[>] 0) (𝓝 (Real.pi / 6))`
- **What**: As `δ → 0⁺`, the argument of `γ(3 − δ) − ρ` (the seg2 approach) tends to `π/6`.
- **How**: `Metric.tendsto_nhdsWithin_nhds`. Pick `min 1 ε` as the witness. Use `arg_approach_rho_left_helper` to evaluate the argument, then `nlinarith` with `Real.pi_le_four` to bound `|−x·π/12| < ε`.
- **Hypotheses**: none beyond ambient `H : ℝ` (declared at section level).
- **Uses from project**: `fdBoundary_H`, `ellipticPointRho`, `arg_approach_rho_left_helper`.
- **Used by**: unused in file (exposed as public API).
- **Visibility**: public.
- **Lines**: 213–230.

### `theorem arg_approach_rho_right`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1) : (fdBoundary_H H (3 + δ) - ellipticPointRho).arg = Real.pi / 2`
- **What**: The right-approach argument at `ρ` (along the vertical segment 3) equals `π/2` exactly, not just as a limit.
- **How**: Substitute seg3 to get `γ(3 + δ) − ρ = δ(H − √3/2)·I`, then `Complex.arg_eq_pi_div_two_iff` reduces to two `ring`/`nlinarith` checks on real/imaginary parts.
- **Hypotheses**: `H > √3/2`, `0 < δ ≤ 1`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_seg3`, `ellipticPointRho`, `ellipticPointRho'`.
- **Used by**: `pv_log_limit_at_rho`.
- **Visibility**: public.
- **Lines**: 234–251.

### `private lemma g_seg3_value`
- **Type**: `(H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : fdBoundary_H H (3 + δ) - ellipticPointRho = ↑(δ * (H - Real.sqrt 3 / 2)) * I`
- **What**: Explicit formula `γ(3 + δ) − ρ = δ(H − √3/2)·I` on segment 3.
- **How**: `fdBoundary_H_seg3` + `push_cast; ring`.
- **Hypotheses**: `0 < δ ≤ 1`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_seg3`, `ellipticPointRho`, `ellipticPointRho'`.
- **Used by**: `g_norm_seg3`.
- **Visibility**: private.
- **Lines**: 253–260.

### `private lemma g_norm_seg3`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : ‖fdBoundary_H H (3 + δ) - ellipticPointRho‖ = δ * (H - Real.sqrt 3 / 2)`
- **What**: Right-cutoff norm: `‖γ(3 + δ) − ρ‖ = δ(H − √3/2)`.
- **How**: `g_seg3_value`, `norm_mul`, `Complex.norm_I`, `Complex.norm_real`, `Real.norm_of_nonneg` via `nlinarith`.
- **Hypotheses**: `H > √3/2`, `0 < δ ≤ 1`.
- **Uses from project**: `fdBoundary_H`, `ellipticPointRho`, `g_seg3_value`.
- **Used by**: `norm_le_middle_rho`, `cutoff_integral_eq_ftc`, `pv_norm_bounds_rho`, `pv_log_limit_at_rho`.
- **Visibility**: private.
- **Lines**: 262–266.

### `private lemma g_norm_seg2`
- **Type**: `{δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : ‖fdBoundary_H H (3 - δ) - ellipticPointRho‖ = 2 * Real.sin (δ * Real.pi / 12)`
- **What**: Left-cutoff norm: `‖γ(3 − δ) − ρ‖ = 2 sin(δπ/12)` on segment 2.
- **How**: Same sum-to-product factorisation as `arg_approach_rho_left_helper`; once factored as `(2 sin(δπ/12))·exp((π/6 − δπ/12)·I)`, take norms via `norm_mul`, `Complex.norm_real`, `Real.norm_of_nonneg` (sin nonneg by `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`), `Complex.norm_exp_ofReal_mul_I`.
- **Hypotheses**: `0 < δ < 1`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_seg2`, `ellipticPointRho`, `ellipticPointRho'`, `exp_real_angle_I`, `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`.
- **Used by**: `norm_le_middle_rho`, `cutoff_integral_eq_ftc`, `pv_norm_bounds_rho`, `pv_log_limit_at_rho`.
- **Visibility**: private.
- **Lines**: 268–316.
- **Notes**: 49-line proof, mirroring `arg_approach_rho_left_helper`.

### `private lemma g_norm_arc`
- **Type**: `{t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) : ‖fdBoundary_H H t - ellipticPointRho‖ = 2 * Real.sin ((3 - t) * Real.pi / 12)`
- **What**: General arc-side formula: `‖γ(t) − ρ‖ = 2 sin((3−t)π/12)` for `t ∈ (1, 3)`.
- **How**: Rewrite via `fdBoundary_H_eq_arc` (which gives the angle `π(1+t)/6`), introduce `δ := 3 − t`, then repeat the sum-to-product factorisation as in `g_norm_seg2` to factor the displacement as `(2 sin(δπ/12)) · exp((π/6 − δπ/12)·I)` and take norms.
- **Hypotheses**: `1 < t < 3`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_eq_arc`, `ellipticPointRho`, `ellipticPointRho'`, `exp_real_angle_I`, `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`.
- **Used by**: `norm_le_middle_rho`, `cutoff_integral_eq_ftc`, `pv_norm_bounds_rho`.
- **Visibility**: private.
- **Lines**: 318–367.
- **Notes**: 50-line proof.

### `private lemma g_norm_ge_one_seg0`
- **Type**: `{t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 1 ≤ ‖fdBoundary_H H t - ellipticPointRho‖`
- **What**: Lower bound `1 ≤ ‖γ(t) − ρ‖` on segment 0.
- **How**: `Complex.abs_re_le_norm` with `fdBoundary_H_sub_rho_seg0_re` and `(abs_of_pos one_pos).symm`.
- **Hypotheses**: `0 ≤ t ≤ 1`.
- **Uses from project**: `fdBoundary_H`, `ellipticPointRho`, `fdBoundary_H_sub_rho_seg0_re`.
- **Used by**: `cutoff_integral_eq_ftc`, `pv_norm_bounds_rho`.
- **Visibility**: private.
- **Lines**: 369–373.

### `private lemma g_norm_ge_seg4`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht4 : 4 ≤ t) (ht5 : t ≤ 5) : H - Real.sqrt 3 / 2 ≤ ‖fdBoundary_H H t - ellipticPointRho‖`
- **What**: Lower bound `‖γ(t) − ρ‖ ≥ H − √3/2` on segment 4 (including `t = 4`).
- **How**: Case split on `t = 4` vs `t > 4`. At `t = 4` use `fdBoundary_H_at_four`; otherwise `fdBoundary_H_seg4`. In both cases get imaginary part equal to `H − √3/2`, then `Complex.abs_im_le_norm`.
- **Hypotheses**: `H > √3/2`, `4 ≤ t ≤ 5`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_at_four`, `fdBoundary_H_seg4`, `ellipticPointRho`, `ellipticPointRho'`.
- **Used by**: `cutoff_integral_eq_ftc`, `pv_norm_bounds_rho`.
- **Visibility**: private.
- **Lines**: 375–394.

### `private lemma ftc_logDeriv_telescope_rho`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) {δ_L δ_R : ℝ} (hδ_L : 0 < δ_L) (hδ_L1 : δ_L < 1) (hδ_R : 0 < δ_R) (hδ_R1 : δ_R < 1) : let g := fun t => fdBoundary_H H t - (ellipticPointRho : ℂ); IntervalIntegrable (fun t => deriv g t / g t) volume 0 (3 - δ_L) ∧ IntervalIntegrable (fun t => deriv g t / g t) volume (3 + δ_R) 5 ∧ ((∫ t in (0:ℝ)..(3 - δ_L), deriv g t / g t) + (∫ t in (3 + δ_R)..(5:ℝ), deriv g t / g t) = Complex.log (g (3 - δ_L)) - Complex.log (g (3 + δ_R)))`
- **What**: Piecewise FTC for `log(g(t))` on the two far segments `[0, 3 − δ_L]` and `[3 + δ_R, 5]`. Gives integrability of `g'/g` on each, plus the telescoped log-difference value (using `γ(0) = γ(5)`).
- **How**: Define four smooth "piece" extensions `h₀, h₁, h₂, h₃` agreeing with `g` on `[0,1]`, `[1, 3 − δ_L]`, `[3 + δ_R, 4]`, `[4, 5]` respectively. Derive explicit `HasDerivAt` formulas (`hd_h₀, hd_h₁, hd_h₂, hd_h₃`) and continuous-derivative facts. Show each piece lands in `slitPlane` using `fdBoundary_H_sub_rho_slitPlane` (and the boundary-case identity at `t = 1` via `fdBoundary_H_at_one_eq_rho_plus_one`, at `t = 4` via `fdBoundary_H_at_four`). Invoke `ftc_log_pieceFM` (from `Common.lean`) on each piece, then concatenate via `intervalIntegral.integral_add_adjacent_intervals` and close using `fdBoundary_H_closed H : γ(0) = γ(5)` followed by `ring`.
- **Hypotheses**: `H > √3/2`, both cutoff widths in `(0,1)`.
- **Uses from project**: `fdBoundary_H`, `ellipticPointRho`, `ellipticPointRho'`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`, `fdBoundary_H_seg0`–`seg4`, `fdBoundary_H_eq_arc`, `fdBoundary_H_at_one_eq_rho_plus_one`, `fdBoundary_H_at_four`, `fdBoundary_H_closed`, `fdBoundary_H_sub_rho_seg0_slitPlane`, `fdBoundary_H_sub_rho_slitPlane`, `ftc_log_pieceFM`, `exp_real_angle_I`.
- **Used by**: `cutoff_integral_eq_ftc`, `pv_integrals_rho`.
- **Visibility**: private.
- **Lines**: 396–573.
- **Notes**: 178-line proof; the dominant routine of the file's analytic side.

### `private lemma norm_le_middle_rho`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) {ε δ_L δ_R : ℝ} (hε : 0 < ε) (hδ_L_pos : 0 < δ_L) (hδ_L_lt_one : δ_L < 1) (hδ_R_pos : 0 < δ_R) (hδ_R_lt_one : δ_R < 1) (h_norm_L : ‖fdBoundary_H H (3 - δ_L) - ellipticPointRho‖ = ε) (h_norm_R : ‖fdBoundary_H H (3 + δ_R) - ellipticPointRho‖ = ε) (hH_gap : 0 < H - Real.sqrt 3 / 2) : ∀ t, 3 - δ_L ≤ t → t ≤ 3 + δ_R → ¬(‖fdBoundary_H H t - (ellipticPointRho : ℂ)‖ > ε)`
- **What**: On the middle band `[3 − δ_L, 3 + δ_R]`, the norm `‖γ(t) − ρ‖` is `≤ ε` (negated formulation `¬ > ε`).
- **How**: Case-splits at `t = 3` (where the norm is `0`). For `t < 3` use `g_norm_arc` then bound via monotonicity of `sin` on `[0, π/2]` (`Real.sin_le_sin_of_le_of_le_pi_div_two`) and the matched left-cutoff identity from `g_norm_seg2`. For `t > 3` use `g_norm_seg3` linearly with `mul_le_mul_of_nonneg_right`.
- **Hypotheses**: standard cutoff data with matched norms at the boundary.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_at_three_eq_rho`, `ellipticPointRho`, `g_norm_arc`, `g_norm_seg2`, `g_norm_seg3`.
- **Used by**: `cutoff_integral_eq_ftc`, `pv_norm_bounds_rho`.
- **Visibility**: private.
- **Lines**: 575–603.

### `private lemma cutoff_integral_eq_ftc`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) {ε : ℝ} (hε : 0 < ε) (hε_small : ε < H - Real.sqrt 3 / 2) (hε_small2 : ε < 2 * Real.sin (Real.pi / 12)) : let g := fun t => fdBoundary_H H t - (ellipticPointRho : ℂ); ∃ δ_L ∈ Set.Ioo (0:ℝ) 1, ∃ δ_R ∈ Set.Ioo (0:ℝ) 1, ‖g (3 - δ_L)‖ = ε ∧ ‖g (3 + δ_R)‖ = ε ∧ (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) = (∫ t in (0:ℝ)..(3 - δ_L), deriv g t / g t) + (∫ t in (3 + δ_R)..(5:ℝ), deriv g t / g t)`
- **What**: Given an explicit small `ε`, constructs cutoff widths `δ_L = 12/π · arcsin(ε/2)` (from inverting the arc-side norm) and `δ_R = ε / (H − √3/2)` (from the seg3 linear formula), proves both achieve norm exactly `ε`, and reduces the indicator cutoff integral on `[0,5]` to the sum of two FTC-style integrals.
- **How**: Build `δ_L`, `δ_R` from the inverses. Verify the matched-norm identities `‖g(3 − δ_L)‖ = ε` and `‖g(3 + δ_R)‖ = ε` via `g_norm_seg2` + `Real.sin_arcsin` and `g_norm_seg3` + `div_self`. Define `F t = if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0`. Show the indicator agrees with `deriv g / g` ae on the left and right far segments, and `0` exactly on the middle band (using `norm_le_middle_rho` for the middle, `g_norm_ge_one_seg0`/`g_norm_ge_seg4` + `mul_lt_mul_of_pos_left/right` and `Real.sin_lt_sin_of_lt_of_le_pi_div_two` for the far segments). Use `ftc_logDeriv_telescope_rho` for integrability and `intervalIntegral.integral_congr_ae`/`integral_add_adjacent_intervals` to split the indicator integral as `(∫₀^{3−δ_L} F) + (∫_{3−δ_L}^{3+δ_R} F) + (∫_{3+δ_R}^5 F)` with the middle piece zero.
- **Hypotheses**: `H > √3/2`, `ε` strictly below both `H − √3/2` and `2 sin(π/12)`.
- **Uses from project**: `fdBoundary_H`, `ellipticPointRho`, `g_norm_seg2`, `g_norm_seg3`, `g_norm_arc`, `g_norm_ge_one_seg0`, `g_norm_ge_seg4`, `norm_le_middle_rho`, `ftc_logDeriv_telescope_rho`.
- **Used by**: unused in file. (Kept as a public-style FTC packaging; the actual route to `pv_integral_at_rho_tendsto` uses `pv_norm_bounds_rho` + `pv_integrals_rho`.)
- **Visibility**: private.
- **Lines**: 605–755.
- **Notes**: 151-line proof.

### `private def δ_L_rho`
- **Type**: `ℝ → ℝ := fun ε => 12 / Real.pi * Real.arcsin (ε / 2)`
- **What**: Left cutoff width on the arc side: invert `‖γ(3 − δ) − ρ‖ = 2 sin(δπ/12) = ε`, i.e. `δ = 12/π · arcsin(ε/2)`.
- **How**: pure definition.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `pv_norm_bounds_rho`, `pv_integrals_rho`, `pv_log_limit_at_rho`, `pv_integral_at_rho_tendsto`.
- **Visibility**: private.
- **Lines**: 758.

### `private def δ_R_rho`
- **Type**: `(H : ℝ) : ℝ → ℝ := fun ε => ε / (H - Real.sqrt 3 / 2)`
- **What**: Right cutoff width on the vertical seg3 side: invert `‖γ(3 + δ) − ρ‖ = δ(H − √3/2) = ε`.
- **How**: pure definition.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `pv_norm_bounds_rho`, `pv_integrals_rho`, `pv_log_limit_at_rho`, `pv_integral_at_rho_tendsto`.
- **Visibility**: private.
- **Lines**: 761.

### `private lemma pv_norm_bounds_rho`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) : let g := fun t => fdBoundary_H H t - (ellipticPointRho : ℂ); let threshold := min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12)); (∀ ε, 0 < ε → ε < threshold → ∀ t ∈ Ico (0 : ℝ) (3 - δ_L_rho ε), ε < ‖g t - 0‖) ∧ (∀ ε, 0 < ε → ε < threshold → ∀ t ∈ Ioc (3 + δ_R_rho H ε) (5 : ℝ), ε < ‖g t - 0‖) ∧ (∀ ε, 0 < ε → ε < threshold → ∀ t ∈ Icc (3 - δ_L_rho ε) (3 + δ_R_rho H ε), ‖g t - 0‖ ≤ ε)`
- **What**: Three-part norm bookkeeping: outside the cutoff interval `[3 − δ_L_rho ε, 3 + δ_R_rho H ε]` we have `‖γ(t) − ρ‖ > ε`; inside, `‖γ(t) − ρ‖ ≤ ε`.
- **How**: Build auxiliary `hε_aux` recording `arcsin(ε/2) ∈ (0, π/12)` and that `δ_L_rho ε ∈ (0, 1)`, `δ_R_rho H ε ∈ (0, 1)`. The two "far" bounds use `g_norm_ge_one_seg0`, `g_norm_seg2`, `Real.sin_lt_sin_of_lt_of_le_pi_div_two`, `g_norm_seg3`, `g_norm_ge_seg4`, `mul_lt_mul_of_pos_left/right`. The "near" bound is exactly `norm_le_middle_rho`.
- **Hypotheses**: `H > √3/2`.
- **Uses from project**: `fdBoundary_H`, `ellipticPointRho`, `δ_L_rho`, `δ_R_rho`, `g_norm_ge_one_seg0`, `g_norm_seg2`, `g_norm_seg3`, `g_norm_arc`, `g_norm_ge_seg4`, `norm_le_middle_rho`, `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`.
- **Used by**: `pv_integral_at_rho_tendsto`.
- **Visibility**: private.
- **Lines**: 764–880.
- **Notes**: 117-line proof.

### `private lemma pv_integrals_rho`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) : let g := fun t => fdBoundary_H H t - (ellipticPointRho : ℂ); let threshold := min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12)); (∀ ε, 0 < ε → ε < threshold → (∫ t in (0:ℝ)..(3 - δ_L_rho ε), (g t - 0)⁻¹ * deriv g t) + (∫ t in (3 + δ_R_rho H ε)..(5:ℝ), (g t - 0)⁻¹ * deriv g t) = Complex.log (g (3 - δ_L_rho ε)) - Complex.log (g (3 + δ_R_rho H ε))) ∧ (∀ ε, 0 < ε → ε < threshold → IntervalIntegrable (fun t => (g t - 0)⁻¹ * deriv g t) volume 0 (3 - δ_L_rho ε)) ∧ (∀ ε, 0 < ε → ε < threshold → IntervalIntegrable (fun t => (g t - 0)⁻¹ * deriv g t) volume (3 + δ_R_rho H ε) 5)`
- **What**: For small `ε`, packages the FTC log-telescope identity plus integrability of `(g − 0)⁻¹ · g'` on the two far segments.
- **How**: Rewrites `(g − 0)⁻¹ * g' = g'/g` via `sub_zero`/`div_eq_mul_inv`/`mul_comm`. Then for each clause, invokes `ftc_logDeriv_telescope_rho` with `δ_L`, `δ_R` (or with the "throwaway" widths `1/2`) and projects to the relevant conjunct.
- **Hypotheses**: `H > √3/2`.
- **Uses from project**: `fdBoundary_H`, `ellipticPointRho`, `δ_L_rho`, `δ_R_rho`, `ftc_logDeriv_telescope_rho`, `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi` (implicitly via threshold positivity).
- **Used by**: `pv_integral_at_rho_tendsto`.
- **Visibility**: private.
- **Lines**: 883–951.
- **Notes**: 69-line proof.

### `private lemma pv_log_limit_at_rho`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) : let g := fun t => fdBoundary_H H t - (ellipticPointRho : ℂ); let δ_L : ℝ → ℝ := δ_L_rho; let δ_R : ℝ → ℝ := δ_R_rho H; Tendsto (fun ε => Complex.log (g (3 - δ_L ε)) - Complex.log (g (3 + δ_R ε))) (nhdsWithin 0 (Ioi 0)) (nhds (-(I * ↑Real.pi / 3)))`
- **What**: As `ε → 0⁺`, the difference of complex logs `log(g(3 − δ_L ε)) − log(g(3 + δ_R ε))` tends to `−iπ/3`.
- **How**: Decompose `log z = log ‖z‖ + i·arg z`. The norms cancel (`h_norm_L = ε = h_norm_R`), and the arguments are `π/6 − δ_L ε · π/12` (left, via `arg_approach_rho_left_helper`) and `π/2` (right, via `arg_approach_rho_right`). The residual is `↑(−δ_L ε · π/12) · I`, whose norm is `δ_L ε · π/12`. Bound this by `ε` using `Real.sin_gt_sub_cube` (gives `δ_L ε · π/12 ≤ ε`) after `set x := δ_L ε · π/12`; finish with `nlinarith`.
- **Hypotheses**: `H > √3/2`.
- **Uses from project**: `fdBoundary_H`, `ellipticPointRho`, `δ_L_rho`, `δ_R_rho`, `g_norm_seg2`, `g_norm_seg3`, `arg_approach_rho_left_helper`, `arg_approach_rho_right`, `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`.
- **Used by**: `pv_integral_at_rho_tendsto`.
- **Visibility**: private.
- **Lines**: 954–1049.
- **Notes**: 96-line proof.

### `theorem pv_integral_at_rho_tendsto`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) : Tendsto (fun ε => ∫ t in (0:ℝ)..5, if ‖fdBoundary_H H t - ellipticPointRho‖ > ε then (fdBoundary_H H t - ellipticPointRho)⁻¹ * deriv (fun s => fdBoundary_H H s - ellipticPointRho) t else 0) (𝓝[>] 0) (𝓝 (-(I * ↑Real.pi / 3)))`
- **What**: The Cauchy principal value of `∫_0^5 (γ − ρ)⁻¹ γ' dt` (computed with the standard ε-ball cutoff) converges to `−iπ/3`.
- **How**: Combine `pv_norm_bounds_rho` (three-part norm bookkeeping), `pv_integrals_rho` (FTC + integrability), and `pv_log_limit_at_rho` (log limit). Feed them to the master combinator `ContourIntegral.pv_tendsto_of_crossing_limit_asymmetric` with `t₀ = 3`, `δ_left = δ_L_rho`, `δ_right = δ_R_rho H`, `L = −iπ/3`, `E = (log_L − log_R)`. The smallness conditions `δ_L_rho ε < 3 − 0` and `δ_R_rho H ε < 5 − 3` are verified separately. A final `simp` strips the trivial `s − 0` to match the user-facing integrand.
- **Hypotheses**: `H > √3/2`.
- **Uses from project**: `fdBoundary_H`, `ellipticPointRho`, `δ_L_rho`, `δ_R_rho`, `pv_norm_bounds_rho`, `pv_integrals_rho`, `pv_log_limit_at_rho`, `ContourIntegral.pv_tendsto_of_crossing_limit_asymmetric`, `ArcCalculus.sin_pos_of_mem_Ioo_zero_pi`.
- **Used by**: `gWN_fdBoundary_H_at_rho`.
- **Visibility**: public.
- **Lines**: 1052–1126.
- **Notes**: 75-line proof.

### `theorem gWN_fdBoundary_H_at_rho`
- **Type**: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) : generalizedWindingNumber' (fdBoundary_H H) 0 5 ellipticPointRho = -1/6`
- **What**: The generalized winding number of the fundamental-domain boundary `fdBoundary_H H` around the elliptic point `ρ` equals `−1/6` — the orbifold weight at `ρ` (3-fold elliptic, half-turn at corner).
- **How**: Apply `ContourIntegral.gWN_eq_neg_sixth_of_pv_tendsto`, converting via the previous theorem `pv_integral_at_rho_tendsto`. A minor `simp` `[sub_zero, gt_iff_lt]` + `ring` step matches the integrand and conclusion shape expected by the combinator.
- **Hypotheses**: `H > √3/2`.
- **Uses from project**: `fdBoundary_H`, `ellipticPointRho`, `generalizedWindingNumber'`, `ContourIntegral.gWN_eq_neg_sixth_of_pv_tendsto`, `pv_integral_at_rho_tendsto`.
- **Used by**: unused in file (public payload).
- **Visibility**: public.
- **Lines**: 1129–1134.

---

## File Summary

- **Total declarations**: 23 (10 `theorem`, 11 `lemma`, 2 `def`; 13 of these are `private`).
- **Key API (public payload)**:
  - `gWN_fdBoundary_H_at_rho` — final result: gWN = −1/6 at `ρ`.
  - `pv_integral_at_rho_tendsto` — CPV equals `−iπ/3`.
  - `fdBoundary_H_sub_rho_slitPlane`, `fdBoundary_H_eq_rho_iff` — slit-plane / unique-crossing facts.
  - `arg_approach_rho_left`, `arg_approach_rho_right` — exact / limit argument data on the two sides.
- **Unused (within this file)**: `fdBoundary_H_eq_rho_iff`, `arg_approach_rho_left`, `gWN_fdBoundary_H_at_rho`, and `cutoff_integral_eq_ftc` (an alternative FTC packaging not consumed by the final route, which uses the `pv_norm_bounds_rho`/`pv_integrals_rho` split). All other declarations have an in-file consumer.
- **Sorries**: 0.
- **`set_option`**: 0.
- **Local attributes**: `attribute [local instance] Classical.propDecidable` (line 25).
- **Custom axioms**: 0.
- **Long proofs (> 30 lines)**: 11 — `arg_approach_rho_left_helper` (~56), `g_norm_seg2` (~49), `g_norm_arc` (~50), `ftc_logDeriv_telescope_rho` (~178, dominant), `cutoff_integral_eq_ftc` (~151), `pv_norm_bounds_rho` (~117), `pv_integrals_rho` (~69), `pv_log_limit_at_rho` (~96), `pv_integral_at_rho_tendsto` (~75); plus `fdBoundary_H_sub_rho_seg2_re` (~23) and the (much shorter) seg-by-seg slit-plane lemmas which sit at ≤ 20 lines each.
- **Purpose**: Compute the contribution of the elliptic point `ρ = e^{2πi/3}` to the generalized winding number of the explicit fundamental-domain boundary `fdBoundary_H H` of `SL₂(ℤ)`. The file (i) shows `ρ` is hit exactly once at `t = 3` and computes exact / limiting arguments of `γ − ρ` on both sides; (ii) computes pointwise norms `‖γ(t) − ρ‖` on segments 2, 3 and arc; (iii) inverts these to define cutoff widths `δ_L_rho ε` (arc side) and `δ_R_rho H ε` (vertical side); (iv) sets up a piecewise-smooth log-derivative FTC telescope `ftc_logDeriv_telescope_rho` over the two far segments, working through `slitPlane` membership in five pieces; (v) packages a three-part norm-bound + integrability + log-limit toolkit and feeds it into `ContourIntegral.pv_tendsto_of_crossing_limit_asymmetric` to obtain `pv_integral_at_rho_tendsto = −iπ/3`; and (vi) wraps the gWN formula through `ContourIntegral.gWN_eq_neg_sixth_of_pv_tendsto` to conclude `gWN(fdBoundary_H H, 0, 5, ρ) = −1/6`. This is the dedicated `ρ`-corner companion to the `i`- and `ρ+1`-corner files in the `WindingWeights` directory.
