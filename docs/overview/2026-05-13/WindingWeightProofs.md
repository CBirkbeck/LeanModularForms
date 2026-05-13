# Inventory: WindingWeightProofs.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/WindingWeightProofs.lean`

Imports: `FDBoundary`, `SingleCrossing`, `SegmentFTC`.

### `def fdArcAngle`
- **Type**: `(t : ℝ) → ℝ`
- **What**: Parametrization of the arc segment angle on the FD boundary, linear in `t` with `fdArcAngle(1/5) = π/3`, `fdArcAngle(2/5) = π/2`, `fdArcAngle(3/5) = 2π/3`.
- **How**: Direct definition `Real.pi / 3 + (5*t - 1) * (Real.pi / 6)`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `fdArcAngle_at_one_fifth`, `fdArcAngle_at_two_fifths`, `fdArcAngle_at_three_fifths`, `fdArcAngle_deriv`, `fdArcAngle_continuous`, `fdArcAngle_offset`, `fdArcAngle_offset_one_fifth`, `fdArcAngle_offset_three_fifths`, `fdArcAngle_mem_Ioo`, `fdBoundaryFun_arc_eq_exp`, `fdBoundaryFun_arc_dist_I`, `fdBoundaryFun_arc_dist_rho`, `fdBoundaryFun_arc_dist_rhoPlusOne`
- **Visibility**: public
- **Lines**: 65
- **Notes**: none

### `theorem fdArcAngle_at_one_fifth`
- **Type**: `fdArcAngle (1/5) = Real.pi / 3`
- **What**: Value at `t = 1/5` (the `rho+1` corner).
- **How**: `unfold fdArcAngle; ring`.
- **Hypotheses**: none.
- **Uses from project**: `fdArcAngle`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 67-69
- **Notes**: none

### `theorem fdArcAngle_at_two_fifths`
- **Type**: `fdArcAngle (2/5) = Real.pi / 2`
- **What**: Value at `t = 2/5` (the `i` crossing).
- **How**: `unfold fdArcAngle; ring`.
- **Hypotheses**: none.
- **Uses from project**: `fdArcAngle`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 71-73
- **Notes**: none

### `theorem fdArcAngle_at_three_fifths`
- **Type**: `fdArcAngle (3/5) = 2 * Real.pi / 3`
- **What**: Value at `t = 3/5` (the `rho` corner).
- **How**: `unfold fdArcAngle; ring`.
- **Hypotheses**: none.
- **Uses from project**: `fdArcAngle`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 75-77
- **Notes**: none

### `theorem fdArcAngle_deriv`
- **Type**: `(t : ℝ) → deriv fdArcAngle t = 5 * Real.pi / 6`
- **What**: Derivative of the arc angle is constant `5π/6`.
- **How**: Unfold definition and `simp [mul_comm]; ring`.
- **Hypotheses**: none.
- **Uses from project**: `fdArcAngle`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 79-83
- **Notes**: none

### `theorem fdArcAngle_continuous`
- **Type**: `Continuous fdArcAngle`
- **What**: Continuity (in fact polynomial in `t`).
- **How**: `unfold fdArcAngle; fun_prop`.
- **Hypotheses**: none.
- **Uses from project**: `fdArcAngle`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 85-87
- **Notes**: none

### `theorem fdArcAngle_offset`
- **Type**: `(s : ℝ) → fdArcAngle (2/5 + s) - Real.pi / 2 = s * (5 * Real.pi / 6)`
- **What**: Local linear behavior of the arc angle near `t = 2/5`.
- **How**: `unfold fdArcAngle; ring`.
- **Hypotheses**: none.
- **Uses from project**: `fdArcAngle`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 90-93
- **Notes**: none

### `theorem fdArcAngle_offset_one_fifth`
- **Type**: `(s : ℝ) → fdArcAngle (1/5 + s) - Real.pi / 3 = s * (5 * Real.pi / 6)`
- **What**: Local linear behavior near `t = 1/5` (the `rho+1` crossing).
- **How**: `unfold fdArcAngle; ring`.
- **Hypotheses**: none.
- **Uses from project**: `fdArcAngle`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 96-99
- **Notes**: none

### `theorem fdArcAngle_offset_three_fifths`
- **Type**: `(s : ℝ) → fdArcAngle (3/5 + s) - 2 * Real.pi / 3 = s * (5 * Real.pi / 6)`
- **What**: Local linear behavior near `t = 3/5` (the `rho` crossing).
- **How**: `unfold fdArcAngle; ring`.
- **Hypotheses**: none.
- **Uses from project**: `fdArcAngle`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 102-105
- **Notes**: none

### `theorem fdArcAngle_mem_Ioo`
- **Type**: `(t : ℝ) (ht1 : 1/5 < t) (ht2 : t < 3/5) → fdArcAngle t ∈ Ioo 0 Real.pi`
- **What**: Arc angle strictly in `(0, π)` on the open arc interval.
- **How**: Two `nlinarith [Real.pi_pos]` calls after `unfold fdArcAngle`.
- **Hypotheses**: `1/5 < t < 3/5`.
- **Uses from project**: `fdArcAngle`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 108-114
- **Notes**: none

### `theorem norm_exp_sub_exp`
- **Type**: `(θ φ : ℝ) → ‖exp (↑θ * I) - exp (↑φ * I)‖ = 2 * |Real.sin ((θ - φ) / 2)|`
- **What**: Distance between two unit-circle exponentials equals `2|sin((θ-φ)/2)|`.
- **How**: KEY: rewrite each `exp(iθ)` via `exp_mul_I` as `cos θ + i sin θ`; apply `norm_add_mul_I` to get the real-part-and-imaginary-part norm; use the identity `(cos θ - cos φ)² + (sin θ - sin φ)² = (2|sin((θ-φ)/2)|)²` (proved with `Real.sin_sq_add_cos_sq`, `Real.cos_sq`, `Real.cos_sub` via `nlinarith`); take `Real.sqrt_sq`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 122-142
- **Notes**: >10 lines

### `private theorem norm_trig_sub_I`
- **Type**: `(θ : ℝ) → ‖(↑(Real.cos θ) + ↑(Real.sin θ) * I) - I‖ = 2 * |Real.sin ((θ - Real.pi / 2) / 2)|`
- **What**: Distance from the unit-circle point `(cos θ, sin θ)` to `I`, expressed via half-angle.
- **How**: Recognize `I = cos(π/2) + i sin(π/2)`; apply `norm_add_mul_I` to the difference; identity `(cos θ - cos φ)² + (sin θ - sin φ)² = (2|sin((θ-φ)/2)|)²` (φ = π/2) via `Real.cos_sub` and `nlinarith`; take `Real.sqrt_sq`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `fdBoundaryFun_arc_dist_I`
- **Visibility**: private
- **Lines**: 150-176
- **Notes**: >10 lines

### `private theorem norm_trig_sub_rho`
- **Type**: `(θ : ℝ) → ‖(↑(Real.cos θ) + ↑(Real.sin θ) * I) - ellipticPointRho‖ = 2 * |Real.sin ((θ - 2 * Real.pi / 3) / 2)|`
- **What**: Distance to `rho` (which equals `cos(2π/3) + i sin(2π/3)`).
- **How**: Express `rho` via `cos(2π/3) = cos(π - π/3) = -cos(π/3)` and `sin(2π/3) = sin(π - π/3) = sin(π/3)`; same `(cos - cos)² + (sin - sin)²` trick using `Real.cos_sub` and `nlinarith`; `Real.sqrt_sq`.
- **Hypotheses**: none.
- **Uses from project**: `ellipticPointRho`, `ellipticPointRho'`.
- **Used by**: `fdBoundaryFun_arc_dist_rho`
- **Visibility**: private
- **Lines**: 179-202
- **Notes**: >10 lines

### `private theorem norm_trig_sub_rhoPlusOne`
- **Type**: `(θ : ℝ) → ‖(↑(Real.cos θ) + ↑(Real.sin θ) * I) - ellipticPointRhoPlusOne‖ = 2 * |Real.sin ((θ - Real.pi / 3) / 2)|`
- **What**: Distance to `rho+1` (which equals `cos(π/3) + i sin(π/3)`).
- **How**: `rho+1` decomposes as `cos(π/3) + i sin(π/3)`; same `(cos - cos)² + (sin - sin)²` trick using `Real.cos_sub` and `nlinarith`; `Real.sqrt_sq`.
- **Hypotheses**: none.
- **Uses from project**: `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`.
- **Used by**: `fdBoundaryFun_arc_dist_rhoPlusOne`
- **Visibility**: private
- **Lines**: 205-227
- **Notes**: >10 lines

### `theorem fdBoundaryFun_arc_eq_exp`
- **Type**: `(H t : ℝ) (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) → fdBoundaryFun H t = exp (↑(fdArcAngle t) * I)`
- **What**: On segments 2-3, the FD-boundary function equals the unit-circle exponential `exp(i · fdArcAngle t)`.
- **How**: Case split `t ≤ 2/5` vs not; in each case simplify `fdBoundaryFun` to the relevant arc piece and verify the angle matches `fdArcAngle t` via `push_cast` and `ring`.
- **Hypotheses**: `1/5 < t ≤ 3/5`.
- **Uses from project**: `fdBoundaryFun`, `fdArcAngle`.
- **Used by**: `fdBoundaryFun_arc_dist_I`, `fdBoundaryFun_arc_dist_rho`, `fdBoundaryFun_arc_dist_rhoPlusOne`
- **Visibility**: public
- **Lines**: 232-246
- **Notes**: none

### `theorem fdBoundaryFun_arc_dist_I`
- **Type**: `(H t : ℝ) (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) → ‖fdBoundaryFun H t - I‖ = 2 * |Real.sin ((fdArcAngle t - Real.pi / 2) / 2)|`
- **What**: Distance from the arc to `I`.
- **How**: Rewrite via `fdBoundaryFun_arc_eq_exp`, then apply `norm_trig_sub_I`.
- **Hypotheses**: `1/5 < t ≤ 3/5`.
- **Uses from project**: `fdBoundaryFun_arc_eq_exp`, `norm_trig_sub_I`, `fdArcAngle`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 250-253
- **Notes**: none

### `theorem fdBoundaryFun_arc_dist_rho`
- **Type**: `(H t : ℝ) (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) → ‖fdBoundaryFun H t - ellipticPointRho‖ = 2 * |Real.sin ((fdArcAngle t - 2 * Real.pi / 3) / 2)|`
- **What**: Distance from the arc to `rho`.
- **How**: Rewrite via `fdBoundaryFun_arc_eq_exp`, apply `norm_trig_sub_rho`.
- **Hypotheses**: `1/5 < t ≤ 3/5`.
- **Uses from project**: `fdBoundaryFun_arc_eq_exp`, `norm_trig_sub_rho`, `fdArcAngle`, `ellipticPointRho`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 257-261
- **Notes**: none

### `theorem fdBoundaryFun_arc_dist_rhoPlusOne`
- **Type**: `(H t : ℝ) (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) → ‖fdBoundaryFun H t - ellipticPointRhoPlusOne‖ = 2 * |Real.sin ((fdArcAngle t - Real.pi / 3) / 2)|`
- **What**: Distance from the arc to `rho+1`.
- **How**: Rewrite via `fdBoundaryFun_arc_eq_exp`, apply `norm_trig_sub_rhoPlusOne`.
- **Hypotheses**: `1/5 < t ≤ 3/5`.
- **Uses from project**: `fdBoundaryFun_arc_eq_exp`, `norm_trig_sub_rhoPlusOne`, `fdArcAngle`, `ellipticPointRhoPlusOne`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 265-270
- **Notes**: none

### `theorem fdBoundaryFun_seg1_dist_I_lower`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ≤ 1/5) → 1/2 ≤ ‖fdBoundaryFun H t - I‖`
- **What**: On segment 1 (`Re = 1/2`), distance to `I` is at least `1/2`.
- **How**: `Re(fdBoundaryFun H t - I) = 1/2`; bound `|Re| ≤ ‖·‖` via `Complex.abs_re_le_norm`.
- **Hypotheses**: `t ≤ 1/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg1_re`.
- **Used by**: `fdBoundary_far_atI`
- **Visibility**: public
- **Lines**: 281-289
- **Notes**: none

### `theorem fdBoundaryFun_seg4_dist_I_lower`
- **Type**: `(H : ℝ) (t : ℝ) (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) → 1/2 ≤ ‖fdBoundaryFun H t - I‖`
- **What**: On segment 4 (`Re = -1/2`), distance to `I` is at least `1/2`.
- **How**: Same as `seg1`, but `Re = -1/2`; `|Re| ≤ ‖·‖`.
- **Hypotheses**: `3/5 < t ≤ 4/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg4_re`.
- **Used by**: `fdBoundary_far_atI`
- **Visibility**: public
- **Lines**: 292-300
- **Notes**: none

### `theorem fdBoundaryFun_seg5_dist_I_lower`
- **Type**: `(H : ℝ) (hH : 1 < H) (t : ℝ) (ht : 4/5 < t) → H - 1 ≤ ‖fdBoundaryFun H t - I‖`
- **What**: On segment 5 (`Im = H`), distance to `I` is at least `H - 1` (using `H > 1`).
- **How**: `Im(fdBoundaryFun H t - I) = H - 1 > 0`; bound `|Im| ≤ ‖·‖` via `Complex.abs_im_le_norm`.
- **Hypotheses**: `1 < H`, `4/5 < t`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg5_im`.
- **Used by**: `fdBoundary_far_atI`
- **Visibility**: public
- **Lines**: 303-311
- **Notes**: none

### `theorem fdBoundaryFun_seg1_dist_rho_lower`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ≤ 1/5) → 1 ≤ ‖fdBoundaryFun H t - ellipticPointRho‖`
- **What**: On segment 1 (`Re = 1/2`), distance to `rho` (`Re = -1/2`) is at least `1`.
- **How**: `Re(fdBoundaryFun - rho) = 1`; `Complex.abs_re_le_norm`.
- **Hypotheses**: `t ≤ 1/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg1_re`, `ellipticPointRho`, `ellipticPointRho'`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 316-327
- **Notes**: none

### `theorem fdBoundaryFun_seg5_dist_rho_lower`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) (t : ℝ) (ht : 4/5 < t) → H - Real.sqrt 3 / 2 ≤ ‖fdBoundaryFun H t - ellipticPointRho‖`
- **What**: On segment 5, distance to `rho` is at least `H - √3/2` (`rho.im = √3/2`).
- **How**: `Im(fdBoundaryFun - rho) = H - √3/2 > 0` (using `fdHeightValid`); `Complex.abs_im_le_norm`.
- **Hypotheses**: `fdHeightValid H`, `4/5 < t`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg5_im`, `ellipticPointRho`, `ellipticPointRho'`, `fdHeightValid`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 330-342
- **Notes**: none

### `theorem fdBoundaryFun_seg4_dist_rhoPlusOne_lower`
- **Type**: `(H : ℝ) (t : ℝ) (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) → 1 ≤ ‖fdBoundaryFun H t - ellipticPointRhoPlusOne‖`
- **What**: On segment 4 (`Re = -1/2`), distance to `rho+1` (`Re = 1/2`) is at least `1`.
- **How**: `Re(fdBoundaryFun - (rho+1)) = -1`; `Complex.abs_re_le_norm`.
- **Hypotheses**: `3/5 < t ≤ 4/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg4_re`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 347-358
- **Notes**: none

### `theorem fdBoundaryFun_seg5_dist_rhoPlusOne_lower`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) (t : ℝ) (ht : 4/5 < t) → H - Real.sqrt 3 / 2 ≤ ‖fdBoundaryFun H t - ellipticPointRhoPlusOne‖`
- **What**: On segment 5, distance to `rho+1` is at least `H - √3/2`.
- **How**: `Im(fdBoundaryFun - (rho+1)) = H - √3/2 > 0` (using `fdHeightValid`); `Complex.abs_im_le_norm`.
- **Hypotheses**: `fdHeightValid H`, `4/5 < t`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg5_im`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`, `fdHeightValid`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 361-374
- **Notes**: none

### `structure ArcFTCHyp`
- **Type**: `{x y : ℂ} (γ : PiecewiseC1Path x y) (z₀ : ℂ) (t₀ : ℝ) (δ : ℝ → ℝ) (threshold : ℝ) (L : ℂ)` — bundle of `E`, `h_ftc`, `hint_left`, `hint_right`, `h_limit`.
- **What**: Analytic-hypotheses bundle for an FTC telescope at a crossing: an FTC expression `E ε`, the FTC equality `(∫₀^{t₀-δε} + ∫_{t₀+δε}^1) (γ-z₀)⁻¹·γ' = E ε`, integrability on both subintervals, and `E ε → L` as `ε → 0⁺`.
- **How**: Direct structure declaration.
- **Hypotheses**: structural fields.
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.toPath`.
- **Used by**: `mkSingleCrossingData_atI`, `mkSingleCrossingData_atRho`, `mkSingleCrossingData_atRhoPlusOne`
- **Visibility**: public
- **Lines**: 385-406
- **Notes**: none

### `private lemma fdBoundary_far_atI`
- **Type**: `{H : ℝ} (hH : 1 < H) {ε : ℝ} (hε_half : ε < 1/2) (hε_Hm1 : ε < H - 1) {δε : ℝ} (h_arc_far : ∀ t ∈ Icc 1/5 3/5, δε < |t - 2/5| → ε < ‖fdBoundaryFun H t - I‖) {t : ℝ} (hδt : δε < |t - 2/5|) → ε < ‖fdBoundaryFun H t - I‖`
- **What**: Stitch the per-segment lower bounds at `I` (segments 1, 2-3 arc, 4, 5) into a uniform `ε`-far statement once `δε < |t - 2/5|`.
- **How**: Case split on `t ≤ 1/5`, `t ≤ 3/5`, `t ≤ 4/5`, otherwise; on each segment use `fdBoundaryFun_seg{1,4}_dist_I_lower` (with `linarith` via `ε < 1/2`) or `fdBoundaryFun_seg5_dist_I_lower` (with `ε < H - 1`); on the arc use `h_arc_far`.
- **Hypotheses**: `1 < H`, `ε < 1/2`, `ε < H - 1`, arc-far hypothesis.
- **Uses from project**: `fdBoundaryFun_seg1_dist_I_lower`, `fdBoundaryFun_seg4_dist_I_lower`, `fdBoundaryFun_seg5_dist_I_lower`.
- **Used by**: `mkSingleCrossingData_atI`
- **Visibility**: private
- **Lines**: 412-427
- **Notes**: none

### `def mkSingleCrossingData_atI`
- **Type**: `{H : ℝ} (hH : 1 < H) (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : agrees with fdBoundaryFun) (δ : ℝ → ℝ) (threshold : ℝ) (hthresh : 0 < threshold) (hthresh_le : ≤ min (1/2) (H - 1)) (hδ_pos) (hδ_small) (h_arc_far) (h_arc_near) (ftcHyp : ArcFTCHyp γ I (2/5) δ threshold (-(↑Real.pi * I))) → SingleCrossingData γ I`
- **What**: Constructor: assemble a `SingleCrossingData γ I` with `t₀ = 2/5`, `L = -π·I` from geometric data and `ArcFTCHyp`.
- **How**: Direct field-by-field construction. KEY: the `h_far` field stitches arc and per-segment bounds via `fdBoundary_far_atI` after rewriting `γ.toPath.extend` to `fdBoundaryFun` (via `hγ`). The `h_near` field uses `hγ` after deriving `t ∈ [0,1]` from `|t - 2/5| ≤ δ ε < 1/5`. FTC fields forwarded from `ftcHyp`.
- **Hypotheses**: stated structurally.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `fdBoundary_far_atI`, `ArcFTCHyp`, `SingleCrossingData`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 429-472
- **Notes**: >30 lines

### `def mkSingleCrossingData_atRho`
- **Type**: `{H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ) (δ) (threshold) (hthresh) (hδ_pos) (hδ_small) (h_far) (h_near) (ftcHyp : ArcFTCHyp γ ellipticPointRho (3/5) δ threshold (-(↑Real.pi / 3 * I))) → SingleCrossingData γ ellipticPointRho`
- **What**: Constructor at `rho` with `t₀ = 3/5` and `L = -π/3 · I`.
- **How**: Same shape as `mkSingleCrossingData_atI` but rho-specific; takes a pre-stitched `h_far` instead of using a `fdBoundary_far_atRho` helper.
- **Hypotheses**: stated structurally.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `ellipticPointRho`, `ArcFTCHyp`, `SingleCrossingData`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 477-517
- **Notes**: >30 lines

### `def mkSingleCrossingData_atRhoPlusOne`
- **Type**: `{H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ) (δ) (threshold) (hthresh) (hδ_pos) (hδ_small) (h_far) (h_near) (ftcHyp : ArcFTCHyp γ ellipticPointRhoPlusOne (1/5) δ threshold (-(↑Real.pi / 3 * I))) → SingleCrossingData γ ellipticPointRhoPlusOne`
- **What**: Constructor at `rho+1` with `t₀ = 1/5` and `L = -π/3 · I`.
- **How**: Same shape as `mkSingleCrossingData_atRho`, with the crossing at `1/5`.
- **Hypotheses**: stated structurally.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`, `ArcFTCHyp`, `SingleCrossingData`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 522-563
- **Notes**: >30 lines

### `def mkFDWindingData`
- **Type**: `{H : ℝ} (boundary : PiecewiseC1Path (fdStart H) (fdStart H)) (hbdy) (h_int : interior winding = -1) (D_i : SingleCrossingData boundary I) (hL_i : D_i.L = -(↑Real.pi * I)) (D_rho) (hL_rho : D_rho.L = -(↑Real.pi / 3 * I)) (D_rho1) (hL_rho1) → FDWindingData H`
- **What**: Assemble `FDWindingData` from boundary + interior winding numbers + three `SingleCrossingData` at the elliptic points.
- **How**: One-liner: delegate to `FDWindingData.mk_of_crossing`.
- **Hypotheses**: structural.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `HasGeneralizedWindingNumber`, `SingleCrossingData`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, `FDWindingData`, `FDWindingData.mk_of_crossing`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 572-584
- **Notes**: none

### `theorem windingNumber_at_I_eq`
- **Type**: `{H : ℝ} {γ : PiecewiseC1Path (fdStart H) (fdStart H)} (D : SingleCrossingData γ I) (hL : D.L = -(↑Real.pi * I)) → generalizedWindingNumber γ I = -1/2`
- **What**: Generalized winding number at `i` equals `-1/2` from `SingleCrossingData` with limit `-π·I`.
- **How**: One-liner: `D.windingNumber_neg_half hL`.
- **Hypotheses**: `D.L = -π·I`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `SingleCrossingData`, `SingleCrossingData.windingNumber_neg_half`, `generalizedWindingNumber`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 587-591
- **Notes**: none

### `theorem windingNumber_at_rho_eq`
- **Type**: `{H : ℝ} {γ : PiecewiseC1Path (fdStart H) (fdStart H)} (D : SingleCrossingData γ ellipticPointRho) (hL : D.L = -(↑Real.pi / 3 * I)) → generalizedWindingNumber γ ellipticPointRho = -1/6`
- **What**: Generalized winding number at `rho` equals `-1/6`.
- **How**: One-liner: `D.windingNumber_neg_sixth hL`.
- **Hypotheses**: `D.L = -π/3·I`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `SingleCrossingData`, `SingleCrossingData.windingNumber_neg_sixth`, `generalizedWindingNumber`, `ellipticPointRho`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 594-599
- **Notes**: none

### `theorem windingNumber_at_rhoPlusOne_eq`
- **Type**: `{H : ℝ} {γ : PiecewiseC1Path (fdStart H) (fdStart H)} (D : SingleCrossingData γ ellipticPointRhoPlusOne) (hL : D.L = -(↑Real.pi / 3 * I)) → generalizedWindingNumber γ ellipticPointRhoPlusOne = -1/6`
- **What**: Generalized winding number at `rho+1` equals `-1/6`.
- **How**: One-liner: `D.windingNumber_neg_sixth hL`.
- **Hypotheses**: `D.L = -π/3·I`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `SingleCrossingData`, `SingleCrossingData.windingNumber_neg_sixth`, `generalizedWindingNumber`, `ellipticPointRhoPlusOne`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 602-607
- **Notes**: none

### `theorem fdBoundary_crosses_I_at`
- **Type**: `(H : ℝ) → fdBoundaryFun H (2/5) = I`
- **What**: Boundary crosses `I` at parameter `t₀ = 2/5`.
- **How**: `fdBoundaryFun_at_two_fifths` returns `ellipticPointI`, which is defeq to `I`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun_at_two_fifths`, `ellipticPointI`, `fdBoundaryFun`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 612-615
- **Notes**: none

### `theorem fdBoundary_crosses_rhoPlusOne_at`
- **Type**: `(H : ℝ) → fdBoundaryFun H (1/5) = ellipticPointRhoPlusOne`
- **What**: Boundary crosses `rho+1` at parameter `t₀ = 1/5`.
- **How**: Direct from `fdBoundaryFun_at_one_fifth`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_one_fifth`, `ellipticPointRhoPlusOne`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 618-620
- **Notes**: none

### `theorem fdBoundary_crosses_rho_at`
- **Type**: `(H : ℝ) → fdBoundaryFun H (3/5) = ellipticPointRho`
- **What**: Boundary crosses `rho` at parameter `t₀ = 3/5`.
- **How**: Direct from `fdBoundaryFun_at_three_fifths`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_three_fifths`, `ellipticPointRho`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 623-625
- **Notes**: none

### `theorem ellipticPointRhoPlusOne_eq_exp`
- **Type**: `ellipticPointRhoPlusOne = exp (↑(Real.pi / 3) * I)`
- **What**: `rho+1` expressed as a unit-circle exponential at angle `π/3`.
- **How**: Expand `exp(iπ/3) = cos(π/3) + i sin(π/3)`; substitute `Real.cos_pi_div_three`, `Real.sin_pi_div_three`; `push_cast; ring`.
- **Hypotheses**: none.
- **Uses from project**: `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 628-634
- **Notes**: none

### `theorem ellipticPointRho_eq_exp`
- **Type**: `ellipticPointRho = exp (↑(2 * Real.pi / 3) * I)`
- **What**: `rho` expressed as a unit-circle exponential at angle `2π/3`.
- **How**: Expand `exp(i·2π/3) = cos(2π/3) + i sin(2π/3) = -cos(π/3) + i sin(π/3)`; `push_cast; ring`.
- **Hypotheses**: none.
- **Uses from project**: `ellipticPointRho`, `ellipticPointRho'`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 637-644
- **Notes**: none

## File Summary

- **Total declarations**: 33 (definitions + theorems + private helpers).
- **Key public API**:
  - `fdArcAngle` — arc-angle parametrization, with values at the three corners and offset identities.
  - `norm_exp_sub_exp` — unit-circle distance via half-angle.
  - `fdBoundaryFun_arc_eq_exp` and three arc-distance lemmas (`fdBoundaryFun_arc_dist_{I,rho,rhoPlusOne}`).
  - Six per-segment distance lower bounds for segments 1, 4, 5 vs `{I, rho, rho+1}`.
  - `ArcFTCHyp` — analytic-hypothesis bundle for FTC at a crossing.
  - Three `SingleCrossingData` constructors at `I`, `rho`, `rho+1` (`mkSingleCrossingData_at*`).
  - `mkFDWindingData` — top-level assembler for `FDWindingData`.
  - Three winding-number theorems (`windingNumber_at_*_eq`).
  - Three crossing identities (`fdBoundary_crosses_*_at`) and two elliptic-point/exp identities.
- **Unused (within this file)**: most public theorems are leaf API for downstream consumers — every theorem from line 67 (`fdArcAngle_at_one_fifth`) through line 644 (`ellipticPointRho_eq_exp`) is marked unused inside this file (this file's role is to expose them). The only internally-consumed declarations are: `fdArcAngle` (consumed by many lemmas in the file), `norm_trig_sub_{I,rho,rhoPlusOne}` (private, consumed by arc-distance lemmas), `fdBoundaryFun_arc_eq_exp` (consumed by arc-distance lemmas), `fdBoundaryFun_seg{1,4,5}_dist_I_lower` (consumed by `fdBoundary_far_atI`), `fdBoundary_far_atI` (consumed by `mkSingleCrossingData_atI`), and `ArcFTCHyp` (consumed by the three constructors).
- **Sorries**: none.
- **set_options**: none.
- **Long proofs** (>30 lines): `mkSingleCrossingData_atI`, `mkSingleCrossingData_atRho`, `mkSingleCrossingData_atRhoPlusOne`.
- **Purpose**: Builds the geometric and assembly infrastructure for computing the generalized winding numbers at the three elliptic/on-curve points (`i`, `rho`, `rho+1`) of the standard SL₂(ℤ) fundamental-domain boundary. The file provides (i) the explicit arc-angle parametrization, (ii) trigonometric distance identities `2|sin(half-angle)|` to each crossing, (iii) per-segment lower bounds on distances along the non-arc segments, (iv) an `ArcFTCHyp` bundle for the analytic input (FTC + integrability + limit), and (v) three constructors for `SingleCrossingData` at each crossing plus a top-level `mkFDWindingData` assembler. Together with the three closed-form winding-number theorems (`-1/2` at `i`, `-1/6` at `rho`, `-1/6` at `rho+1`), this is the assembly used downstream in the valence-formula proof.
