# Inventory: CrossingAtRho.lean

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/CrossingAtRho.lean`

(No namespace declaration; declarations live in root scope.) `noncomputable section`.

### `def vertDelta`
- **Type**: `(H : ℝ) (ε : ℝ) : ℝ`
- **What**: Vertical cutoff function `δ_vert(H,ε) = ε / (5 (H − √3/2))`. Used as the on-vertical-segment near-side δ for the corner crossings at ρ and ρ+1.
- **How**: Direct definition.
- **Hypotheses**: None (definition).
- **Uses from project**: [].
- **Used by**: `vertDelta_pos`, `vertDelta_lt_one_fifth`, `fdBoundaryFun_seg4_dist_rho` (in usage range), `vert_near_at_rho`, `vert_far_at_rho`, `vert_near_at_rhoPlusOne`, `vert_far_at_rhoPlusOne`, `rho_far_right`, `rho_near`, `rhoPlusOne_far_left`, `rhoPlusOne_near`, `hasWindingNumber_atRho_of_cornerFtcHyp`, `hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp`.
- **Visibility**: public.
- **Lines**: 36.
- **Notes**: none.

### `theorem vertDelta_pos`
- **Type**: `{H ε : ℝ} (hH : fdHeightValid H) (hε : 0 < ε) : 0 < vertDelta H ε`
- **What**: The vertical cutoff δ(H,ε) is strictly positive when ε > 0 and H is a valid FD height.
- **How**: Unfold `vertDelta`; use `div_pos hε` with `positivity` on the denominator (after `linarith` from `fdHeightValid`).
- **Hypotheses**: H is a valid FD height (so H > √3/2); ε > 0.
- **Uses from project**: `vertDelta`, `fdHeightValid`.
- **Used by**: `vert_near_at_rho`, `vert_far_at_rho`, `vert_near_at_rhoPlusOne`, `vert_far_at_rhoPlusOne`, `rho_far_right`, `rho_near`, `rhoPlusOne_far_left`, `rhoPlusOne_near`, `hasWindingNumber_atRho_of_cornerFtcHyp`, `hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp`.
- **Visibility**: public.
- **Lines**: 38–45.
- **Notes**: none.

### `theorem vertDelta_lt_one_fifth`
- **Type**: `{H ε : ℝ} (hH : fdHeightValid H) (hε_lt : ε < H − √3/2) : vertDelta H ε < 1/5`
- **What**: For ε strictly less than the FD-vertical extent `H − √3/2`, the cutoff δ(H,ε) is < 1/5, ensuring the cutoff stays inside the relevant arc/vertical interval.
- **How**: Unfold `vertDelta`; positivity gives `0 < 5 (H − √3/2)`; reduce `ε / (5(H−√3/2)) < 1/5` via `div_lt_div_iff₀` then close by `linarith`.
- **Hypotheses**: valid FD height; ε smaller than vertical extent.
- **Uses from project**: `vertDelta`, `fdHeightValid`.
- **Used by**: `rho_near`, `rhoPlusOne_far_left` (indirectly via callers), `rhoPlusOne_near`, `hasWindingNumber_atRho_of_cornerFtcHyp`, `hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp`.
- **Visibility**: public.
- **Lines**: 47–56.
- **Notes**: none.

### `private theorem norm_ofReal_mul_I_eq`
- **Type**: `(r : ℝ) (hr : 0 ≤ r) : ‖(↑r : ℂ) * I‖ = r`
- **What**: For a non-negative real r, `‖r · I‖ = r` in ℂ.
- **How**: Rewrite via `norm_mul`, `Complex.norm_I = 1`, `Complex.norm_real`, and `Real.norm_of_nonneg`.
- **Hypotheses**: `0 ≤ r`.
- **Uses from project**: [].
- **Used by**: `fdBoundaryFun_seg4_dist_rho`, `fdBoundaryFun_seg1_dist_rhoPlusOne`.
- **Visibility**: private.
- **Lines**: 60–62.
- **Notes**: none.

### `theorem arc_near_at_rho_arcsin`
- **Type**: `(H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) {t : ℝ} (ht2 : t ≤ 3/5) (ht : |t − 3/5| ≤ arcsinDelta ε) : ‖fdBoundaryFun H t − ellipticPointRho‖ ≤ ε`
- **What**: On the arc segment (parameter `t ∈ (1/5, 3/5]`), if t is within `arcsinDelta ε` of `3/5`, then γ is within ε of ρ.
- **How**: >10 lines, key lemmas: extract `1/5 < t` via `arcsinDelta_lt_one_fifth`; rewrite arc distance with `fdBoundaryFun_arc_dist_rho`; identify the half-angle as `α = 5(t−3/5)π/12`; show `|α| ≤ arcsin(ε/2)` via `half_angle_arcsinDelta`; apply `Real.abs_sin_eq_sin_abs_of_abs_le_pi` and `Real.sin_le_sin_of_le_of_le_pi_div_two`, then `linarith` against `2 sin(|α|) ≤ ε`.
- **Hypotheses**: H is the FD-height parameter (no validity needed at this point); ε ∈ (0, 1/3); t ≤ 3/5; t within `arcsinDelta ε` of 3/5.
- **Uses from project**: `fdBoundaryFun`, `ellipticPointRho`, `arcsinDelta`, `arcsinDelta_lt_one_fifth`, `fdBoundaryFun_arc_dist_rho`, `fdArcAngle`, `half_angle_arcsinDelta`.
- **Used by**: `rho_near`.
- **Visibility**: public.
- **Lines**: 72–96.
- **Notes**: >10 lines (≈25 lines proof).

### `theorem arc_far_at_rho_arcsin`
- **Type**: `(H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) {t : ℝ} (ht_arc : t ∈ Icc (1/5) (3/5)) (hδt : arcsinDelta ε < |t − 3/5|) : ε < ‖fdBoundaryFun H t − ellipticPointRho‖`
- **What**: On the arc, if t is *farther* than `arcsinDelta ε` from 3/5, then the arc point is strictly more than ε away from ρ.
- **How**: >10 lines, key lemmas: split `t = 1/5` via `fdBoundaryFun_seg1_dist_rho_lower`; in the generic case rewrite distance via `fdBoundaryFun_arc_dist_rho`, get `arcsin(ε/2) < |α|` via `half_angle_arcsinDelta`, bound `|α| ≤ π/6` via `nlinarith`, apply `Real.abs_sin_eq_sin_abs_of_abs_le_pi` and `Real.sin_lt_sin_of_lt_of_le_pi_div_two` to deduce `ε/2 < sin|α|`, conclude by `linarith`.
- **Hypotheses**: H is the FD-height parameter; ε ∈ (0, 1/3); t in arc; t at distance > `arcsinDelta ε` from 3/5.
- **Uses from project**: `arcsinDelta`, `arcsinDelta_pos`, `fdBoundaryFun`, `fdBoundaryFun_seg1_dist_rho_lower`, `fdBoundaryFun_arc_dist_rho`, `fdArcAngle`, `half_angle_arcsinDelta`, `ellipticPointRho`.
- **Used by**: `rho_far_left`.
- **Visibility**: public.
- **Lines**: 99–140.
- **Notes**: >30 lines.

### `theorem fdBoundaryFun_seg4_dist_rho`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) (t : ℝ) (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) : ‖fdBoundaryFun H t − ellipticPointRho‖ = 5(t−3/5)(H−√3/2)`
- **What**: Closed-form distance on the left vertical segment (segment 4) from γ(t) to ρ.
- **How**: >10 lines: extract `0 < H − √3/2` from validity; `simp only` unfolds `fdBoundaryFun` on segment 4 and selects the `ite_true` branch; algebraic identity `push_cast; ring` to put the difference in `r · I` form; apply `norm_ofReal_mul_I_eq` with non-negativity proven by `mul_nonneg`/`linarith`.
- **Hypotheses**: valid FD height; t in (3/5, 4/5].
- **Uses from project**: `fdBoundaryFun`, `ellipticPointRho`, `ellipticPointRho'`, `fdHeightValid`, `norm_ofReal_mul_I_eq`.
- **Used by**: `vert_near_at_rho`, `vert_far_at_rho`.
- **Visibility**: public.
- **Lines**: 143–165.
- **Notes**: >10 lines.

### `theorem vert_near_at_rho`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {ε : ℝ} {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) (hδ : t − 3/5 ≤ vertDelta H ε) : ‖fdBoundaryFun H t − ellipticPointRho‖ ≤ ε`
- **What**: On the left vertical segment, t within `vertDelta H ε` to the right of 3/5 gives distance to ρ ≤ ε.
- **How**: >10 lines: substitute via `fdBoundaryFun_seg4_dist_rho`; multiply `hδ` by `5(H−√3/2)`; show `5 · vertDelta H ε · (H − √3/2) = ε` by `field_simp` and `mul_div_cancel_right₀`; conclude by `linarith`.
- **Hypotheses**: valid FD height; t in (3/5, 4/5]; t within `vertDelta H ε` of 3/5.
- **Uses from project**: `fdBoundaryFun_seg4_dist_rho`, `vertDelta`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRho`.
- **Used by**: `rho_near`.
- **Visibility**: public.
- **Lines**: 168–184.
- **Notes**: >10 lines.

### `theorem vert_far_at_rho`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {ε : ℝ} {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) (hδt : vertDelta H ε < t − 3/5) : ε < ‖fdBoundaryFun H t − ellipticPointRho‖`
- **What**: On the left vertical, t past `3/5 + vertDelta H ε` gives distance to ρ > ε.
- **How**: >10 lines: substitute distance via `fdBoundaryFun_seg4_dist_rho`; identify `5·vertDelta·(H−√3/2) = ε` via `field_simp`/`mul_div_cancel_right₀`; multiply `hδt` by `5(H−√3/2)` (via `mul_lt_mul_of_pos_right` and `mul_lt_mul_of_pos_left`) and `linarith` to conclude.
- **Hypotheses**: valid FD height; t in (3/5, 4/5]; t past 3/5 by more than `vertDelta H ε`.
- **Uses from project**: `fdBoundaryFun_seg4_dist_rho`, `vertDelta`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRho`.
- **Used by**: `rho_far_right`.
- **Visibility**: public.
- **Lines**: 187–199.
- **Notes**: >10 lines.

### `theorem arc_near_at_rhoPlusOne_arcsin`
- **Type**: `(H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) {t : ℝ} (ht1 : 1/5 ≤ t) (ht : |t − 1/5| ≤ arcsinDelta ε) : ‖fdBoundaryFun H t − ellipticPointRhoPlusOne‖ ≤ ε`
- **What**: Arc-side near bound at ρ+1: t within `arcsinDelta ε` of 1/5 forces γ within ε of ρ+1.
- **How**: >10 lines, key lemmas: handle `t = 1/5` exactly (use `fdBoundaryFun_at_one_fifth`); else use `arcsinDelta_lt_one_fifth` to get `t ≤ 3/5`, rewrite arc distance via `fdBoundaryFun_arc_dist_rhoPlusOne`, identify half-angle `α = 5(t−1/5)π/12`, bound `|α| ≤ arcsin(ε/2)` via `half_angle_arcsinDelta`, apply `Real.abs_sin_eq_sin_abs_of_abs_le_pi`, then `Real.sin_le_sin_of_le_of_le_pi_div_two`, conclude by `linarith`.
- **Hypotheses**: ε ∈ (0, 1/3); t ≥ 1/5; t within `arcsinDelta ε` of 1/5.
- **Uses from project**: `fdBoundaryFun`, `ellipticPointRhoPlusOne`, `arcsinDelta`, `arcsinDelta_lt_one_fifth`, `fdBoundaryFun_at_one_fifth`, `fdBoundaryFun_arc_dist_rhoPlusOne`, `fdArcAngle`, `half_angle_arcsinDelta`.
- **Used by**: `rhoPlusOne_near`.
- **Visibility**: public.
- **Lines**: 210–237.
- **Notes**: >10 lines.

### `theorem arc_far_at_rhoPlusOne_arcsin`
- **Type**: `(H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) {t : ℝ} (ht_arc : t ∈ Icc (1/5) (3/5)) (hδt : arcsinDelta ε < |t − 1/5|) : ε < ‖fdBoundaryFun H t − ellipticPointRhoPlusOne‖`
- **What**: Arc-side far bound at ρ+1: t farther than `arcsinDelta ε` from 1/5 forces γ farther than ε from ρ+1.
- **How**: >10 lines, key lemmas: by contradiction rule out `t = 1/5`; rewrite distance via `fdBoundaryFun_arc_dist_rhoPlusOne`; identify half-angle `α`; bound `arcsin(ε/2) < |α|` via `half_angle_arcsinDelta`; bound `|α| ≤ π/6` via `nlinarith`; apply `Real.abs_sin_eq_sin_abs_of_abs_le_pi` and `Real.sin_lt_sin_of_lt_of_le_pi_div_two`; close by `linarith`.
- **Hypotheses**: ε ∈ (0, 1/3); t in arc; t farther than `arcsinDelta ε` from 1/5.
- **Uses from project**: `arcsinDelta`, `arcsinDelta_pos`, `fdBoundaryFun`, `fdBoundaryFun_arc_dist_rhoPlusOne`, `fdArcAngle`, `half_angle_arcsinDelta`, `ellipticPointRhoPlusOne`.
- **Used by**: `rhoPlusOne_far_right`.
- **Visibility**: public.
- **Lines**: 240–277.
- **Notes**: >30 lines.

### `theorem fdBoundaryFun_seg1_dist_rhoPlusOne`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) (t : ℝ) (_ht0 : 0 ≤ t) (ht1 : t < 1/5) : ‖fdBoundaryFun H t − ellipticPointRhoPlusOne‖ = 5(1/5 − t)(H − √3/2)`
- **What**: Closed-form distance on the right vertical segment (segment 1) from γ(t) to ρ+1.
- **How**: >10 lines: extract `0 < H − √3/2`; `simp only` unfolds `fdBoundaryFun` on segment 1; algebraic identity `push_cast; ring` puts difference in `r · I` form; apply `norm_ofReal_mul_I_eq` with non-negativity via `mul_nonneg`/`linarith`.
- **Hypotheses**: valid FD height; t ∈ [0, 1/5).
- **Uses from project**: `fdBoundaryFun`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`, `fdHeightValid`, `norm_ofReal_mul_I_eq`.
- **Used by**: `vert_near_at_rhoPlusOne`, `vert_far_at_rhoPlusOne`.
- **Visibility**: public.
- **Lines**: 280–300.
- **Notes**: >10 lines.

### `theorem vert_near_at_rhoPlusOne`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {ε : ℝ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1/5) (hδ : 1/5 − t ≤ vertDelta H ε) : ‖fdBoundaryFun H t − ellipticPointRhoPlusOne‖ ≤ ε`
- **What**: On the right vertical, t within `vertDelta H ε` to the left of 1/5 gives distance to ρ+1 ≤ ε.
- **How**: >10 lines: substitute via `fdBoundaryFun_seg1_dist_rhoPlusOne`; multiply `hδ` by `5(H−√3/2)`; identify `5·vertDelta·(H−√3/2) = ε` via `field_simp`/`mul_div_cancel_right₀`; `linarith`.
- **Hypotheses**: valid FD height; t ∈ [0,1/5); 1/5 − t ≤ `vertDelta H ε`.
- **Uses from project**: `fdBoundaryFun_seg1_dist_rhoPlusOne`, `vertDelta`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`.
- **Used by**: `rhoPlusOne_near`.
- **Visibility**: public.
- **Lines**: 303–319.
- **Notes**: >10 lines.

### `theorem vert_far_at_rhoPlusOne`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {ε : ℝ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1/5) (hδt : vertDelta H ε < 1/5 − t) : ε < ‖fdBoundaryFun H t − ellipticPointRhoPlusOne‖`
- **What**: On the right vertical, t farther than `vertDelta H ε` left of 1/5 gives distance to ρ+1 > ε.
- **How**: >10 lines: substitute via `fdBoundaryFun_seg1_dist_rhoPlusOne`; identify `ε = 5·vertDelta·(H−√3/2)` via `field_simp`/`mul_div_cancel_right₀`.symm; multiply `hδt` by `5(H−√3/2)` via `mul_lt_mul_of_pos_left/right`; close by `linarith`.
- **Hypotheses**: valid FD height; t ∈ [0, 1/5); 1/5 − t > `vertDelta H ε`.
- **Uses from project**: `fdBoundaryFun_seg1_dist_rhoPlusOne`, `vertDelta`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`.
- **Used by**: `rhoPlusOne_far_left`.
- **Visibility**: public.
- **Lines**: 322–334.
- **Notes**: >10 lines.

### `structure CornerFTCHyp`
- **Type**: `{x y : ℂ} (γ : PiecewiseC1Path x y) (z₀ : ℂ) (t₀ : ℝ) (δ_left δ_right : ℝ → ℝ) (threshold : ℝ) (L : ℂ)`
- **What**: Bundle of analytic FTC hypotheses needed by the asymmetric crossing-limit theorem: an FTC expression `E(ε)` for the far-segment integrals on the left `[0, t₀ − δ_left ε]` and right `[t₀ + δ_right ε, 1]` of the crossing, integrability on both pieces, and `E(ε) → L` as ε → 0⁺.
- **How**: Inductive record with five fields: `E : ℝ → ℂ`, `h_ftc`, `hint_left`, `hint_right`, `h_limit`.
- **Hypotheses**: Stored as fields rather than assumed (the structure is the bundle).
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.toPath`.
- **Used by**: `hasWindingNumber_atRho_of_cornerFtcHyp`, `hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp`.
- **Visibility**: public.
- **Lines**: 341–362.
- **Notes**: none.

### `private theorem rho_far_left`
- **Type**: `{H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) {ε : ℝ} (hε : 0 < ε) (hε_13 : ε < 1/3) {t : ℝ} (ht : t ∈ Ico 0 (3/5 − arcsinDelta ε)) : ε < ‖γ.toPath.extend t − ellipticPointRho‖`
- **What**: Far-side bound for the rho crossing on the LEFT of t₀ = 3/5 (the arc/seg1 side): for t in `[0, 3/5 − arcsinDelta ε)`, γ is more than ε from ρ.
- **How**: >10 lines: case split on `t ≤ 1/5` (use `fdBoundaryFun_seg1_dist_rho_lower` to bound by 1) versus arc case (use `arc_far_at_rho_arcsin` after rewriting `t − 3/5 = −(3/5 − t)`).
- **Hypotheses**: γ matches `fdBoundaryFun H`; ε ∈ (0, 1/3); t left of `3/5 − arcsinDelta ε`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `fdBoundaryFun_seg1_dist_rho_lower`, `arc_far_at_rho_arcsin`, `arcsinDelta`, `arcsinDelta_pos`, `ellipticPointRho`.
- **Used by**: `hasWindingNumber_atRho_of_cornerFtcHyp`.
- **Visibility**: private.
- **Lines**: 367–385.
- **Notes**: >10 lines.

### `private theorem rho_far_right`
- **Type**: `{H : ℝ} (hH : 1 < H) (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) {ε : ℝ} (hε : 0 < ε) (hε_H : ε < H − √3/2) {t : ℝ} (ht : t ∈ Ioc (3/5 + vertDelta H ε) 1) : ε < ‖γ.toPath.extend t − ellipticPointRho‖`
- **What**: Far-side bound for the rho crossing on the RIGHT of t₀ = 3/5 (seg4/seg5 side): for t in `(3/5 + vertDelta H ε, 1]`, γ is more than ε from ρ.
- **How**: >10 lines: derive `fdHeightValid` via `fdHeightValid_of_one_lt`; case split on `t ≤ 4/5` (use `vert_far_at_rho`) versus segment 5 case (use `fdBoundaryFun_seg5_dist_rho_lower`).
- **Hypotheses**: H > 1; γ matches `fdBoundaryFun H`; ε ∈ (0, H − √3/2); t right of `3/5 + vertDelta H ε`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `fdHeightValid_of_one_lt`, `vertDelta`, `vertDelta_pos`, `vert_far_at_rho`, `fdBoundaryFun_seg5_dist_rho_lower`, `ellipticPointRho`.
- **Used by**: `hasWindingNumber_atRho_of_cornerFtcHyp`.
- **Visibility**: private.
- **Lines**: 388–403.
- **Notes**: >10 lines.

### `private theorem rho_near`
- **Type**: `{H : ℝ} (hH : 1 < H) (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) {ε : ℝ} (hε : 0 < ε) (hε_13 : ε < 1/3) (hε_H : ε < H − √3/2) {t : ℝ} (ht : t ∈ Icc (3/5 − arcsinDelta ε) (3/5 + vertDelta H ε)) : ‖γ.toPath.extend t − ellipticPointRho‖ ≤ ε`
- **What**: Near-side bound at the rho crossing: for t in `[3/5 − arcsinDelta ε, 3/5 + vertDelta H ε]`, γ is within ε of ρ.
- **How**: >10 lines: case split on `t ≤ 3/5` (use `arc_near_at_rho_arcsin`) versus vertical case (use `vert_near_at_rho` with `vertDelta_lt_one_fifth` to control t ≤ 4/5).
- **Hypotheses**: H > 1; γ matches `fdBoundaryFun H`; ε ∈ (0, 1/3) and < H−√3/2; t in the near-window.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `arcsinDelta`, `vertDelta`, `arcsinDelta_lt_one_fifth`, `vertDelta_lt_one_fifth`, `arc_near_at_rho_arcsin`, `vert_near_at_rho`, `fdHeightValid_of_one_lt`, `ellipticPointRho`.
- **Used by**: `hasWindingNumber_atRho_of_cornerFtcHyp`.
- **Visibility**: private.
- **Lines**: 406–427.
- **Notes**: >10 lines.

### `private theorem rhoPlusOne_far_left`
- **Type**: `{H : ℝ} (hH : 1 < H) (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : …) {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t ∈ Ico 0 (1/5 − vertDelta H ε)) : ε < ‖γ.toPath.extend t − ellipticPointRhoPlusOne‖`
- **What**: Far-side bound on the LEFT of t₀ = 1/5 for the ρ+1 crossing (the right-vertical segment 1 side): for t in `[0, 1/5 − vertDelta H ε)`, γ is more than ε from ρ+1.
- **How**: >10 lines: derive valid FD height; bound `t < 1/5` via `vertDelta_pos`; close by `vert_far_at_rhoPlusOne`.
- **Hypotheses**: H > 1; γ matches `fdBoundaryFun H`; ε > 0; t in left window of ρ+1.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdHeightValid_of_one_lt`, `vertDelta`, `vertDelta_pos`, `vert_far_at_rhoPlusOne`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`.
- **Used by**: `hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp`.
- **Visibility**: private.
- **Lines**: 432–443.
- **Notes**: >10 lines.

### `private theorem rhoPlusOne_far_right`
- **Type**: `{H : ℝ} (hH : 1 < H) (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : …) {ε : ℝ} (hε : 0 < ε) (hε_13 : ε < 1/3) (hε_H : ε < H − √3/2) {t : ℝ} (ht : t ∈ Ioc (1/5 + arcsinDelta ε) 1) : ε < ‖γ.toPath.extend t − ellipticPointRhoPlusOne‖`
- **What**: Far-side bound on the RIGHT of t₀ = 1/5 for the ρ+1 crossing (arc/seg4/seg5 side): for t in `(1/5 + arcsinDelta ε, 1]`, γ is more than ε from ρ+1.
- **How**: >10 lines: case split on `t ≤ 3/5` (use `arc_far_at_rhoPlusOne_arcsin`), then on `t ≤ 4/5` (use `fdBoundaryFun_seg4_dist_rhoPlusOne_lower`), else use `fdBoundaryFun_seg5_dist_rhoPlusOne_lower`.
- **Hypotheses**: H > 1; γ matches `fdBoundaryFun H`; ε ∈ (0, 1/3) and < H − √3/2; t in right window of ρ+1.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `arcsinDelta`, `arcsinDelta_pos`, `arc_far_at_rhoPlusOne_arcsin`, `fdBoundaryFun_seg4_dist_rhoPlusOne_lower`, `fdBoundaryFun_seg5_dist_rhoPlusOne_lower`, `fdHeightValid_of_one_lt`, `ellipticPointRhoPlusOne`.
- **Used by**: `hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp`.
- **Visibility**: private.
- **Lines**: 446–469.
- **Notes**: >10 lines.

### `private theorem rhoPlusOne_near`
- **Type**: `{H : ℝ} (hH : 1 < H) (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : …) {ε : ℝ} (hε : 0 < ε) (hε_13 : ε < 1/3) (hε_H : ε < H − √3/2) {t : ℝ} (ht : t ∈ Icc (1/5 − vertDelta H ε) (1/5 + arcsinDelta ε)) : ‖γ.toPath.extend t − ellipticPointRhoPlusOne‖ ≤ ε`
- **What**: Near-side bound at the ρ+1 crossing: for t in `[1/5 − vertDelta H ε, 1/5 + arcsinDelta ε]`, γ is within ε of ρ+1.
- **How**: >10 lines: case split on `1/5 ≤ t` (use `arc_near_at_rhoPlusOne_arcsin`) versus vertical case (use `vert_near_at_rhoPlusOne`, with `vertDelta_lt_one_fifth` controlling `0 ≤ t`).
- **Hypotheses**: H > 1; γ matches `fdBoundaryFun H`; ε ∈ (0, 1/3) and < H−√3/2; t in the near-window of ρ+1.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `arcsinDelta`, `vertDelta`, `arcsinDelta_lt_one_fifth`, `vertDelta_lt_one_fifth`, `arc_near_at_rhoPlusOne_arcsin`, `vert_near_at_rhoPlusOne`, `fdHeightValid_of_one_lt`, `ellipticPointRhoPlusOne`.
- **Used by**: `hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp`.
- **Visibility**: private.
- **Lines**: 472–492.
- **Notes**: >10 lines.

### `theorem hasWindingNumber_atRho_of_cornerFtcHyp`
- **Type**: `{H : ℝ} (hH : 1 < H) (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) (ftcHyp : CornerFTCHyp γ ellipticPointRho (3/5) arcsinDelta (vertDelta H) (min (1/3) (H − √3/2)) (−(π/3 · I))) : HasGeneralizedWindingNumber γ ellipticPointRho (−1/6)`
- **What**: The generalized winding number of γ around ρ equals −1/6, constructed via the asymmetric crossing-limit theorem with arc-side δ = `arcsinDelta` and vertical-side δ = `vertDelta H`.
- **How**: >30 lines, key lemma: build `HasCauchyPV (z ↦ (z − ρ)⁻¹) γ ρ (−(π/3 · I))` by invoking `PVSplitting.pv_tendsto_of_crossing_limit_asymmetric` with parameters `t₀ = 3/5`, asymmetric deltas, threshold `min(1/3, H−√3/2)`, and dischargers from `vertDelta_pos`, `arcsinDelta_pos`, `vertDelta_lt_one_fifth`, `arcsinDelta_lt_one_fifth`, plus `rho_far_left`, `rho_far_right`, `rho_near` and the FTC fields of `ftcHyp`; convert via `hasGeneralizedWindingNumber_of_hasCauchyPV` and finish with `field_simp; ring` using `(Real.pi : ℂ) ≠ 0`.
- **Hypotheses**: H > 1 (so FD height valid); γ matches the FD boundary parametrization; corner FTC hypothesis at ρ with the prescribed asymmetric δ's and limit value.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdHeightValid`, `fdHeightValid_of_one_lt`, `arcsinDelta`, `vertDelta`, `vertDelta_pos`, `vertDelta_lt_one_fifth`, `arcsinDelta_pos`, `arcsinDelta_lt_one_fifth`, `rho_far_left`, `rho_far_right`, `rho_near`, `CornerFTCHyp`, `PVSplitting.pv_tendsto_of_crossing_limit_asymmetric`, `HasCauchyPV`, `HasGeneralizedWindingNumber`, `hasGeneralizedWindingNumber_of_hasCauchyPV`, `fdBoundaryFun`, `ellipticPointRho`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 498–540.
- **Notes**: >30 lines.

### `theorem hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp`
- **Type**: `{H : ℝ} (hH : 1 < H) (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) (ftcHyp : CornerFTCHyp γ ellipticPointRhoPlusOne (1/5) (vertDelta H) arcsinDelta (min (1/3) (H − √3/2)) (−(π/3 · I))) : HasGeneralizedWindingNumber γ ellipticPointRhoPlusOne (−1/6)`
- **What**: The generalized winding number of γ around ρ+1 equals −1/6, constructed via the asymmetric crossing-limit theorem with vertical-side δ = `vertDelta H` and arc-side δ = `arcsinDelta` (deltas swapped relative to ρ).
- **How**: >30 lines, key lemma: build `HasCauchyPV (z ↦ (z − (ρ+1))⁻¹) γ (ρ+1) (−(π/3 · I))` via `PVSplitting.pv_tendsto_of_crossing_limit_asymmetric` with `t₀ = 1/5`, swapped δ's, the same threshold, and dischargers from `vertDelta_pos`, `arcsinDelta_pos`, `vertDelta_lt_one_fifth`, `arcsinDelta_lt_one_fifth`, plus `rhoPlusOne_far_left`, `rhoPlusOne_far_right`, `rhoPlusOne_near`, and the FTC fields of `ftcHyp`; convert via `hasGeneralizedWindingNumber_of_hasCauchyPV` and finish with `field_simp; ring`.
- **Hypotheses**: H > 1; γ matches FD boundary; corner FTC hypothesis at ρ+1.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdHeightValid`, `fdHeightValid_of_one_lt`, `arcsinDelta`, `vertDelta`, `vertDelta_pos`, `vertDelta_lt_one_fifth`, `arcsinDelta_pos`, `arcsinDelta_lt_one_fifth`, `rhoPlusOne_far_left`, `rhoPlusOne_far_right`, `rhoPlusOne_near`, `CornerFTCHyp`, `PVSplitting.pv_tendsto_of_crossing_limit_asymmetric`, `HasCauchyPV`, `HasGeneralizedWindingNumber`, `hasGeneralizedWindingNumber_of_hasCauchyPV`, `ellipticPointRhoPlusOne`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 544–586.
- **Notes**: >30 lines.

## File Summary

- 1 `def` (`vertDelta`), 1 `structure` (`CornerFTCHyp`), 20 `theorem`s (of which 7 are `private` helpers: `norm_ofReal_mul_I_eq`, `rho_far_left/right/near`, `rhoPlusOne_far_left/right/near`).
- Imports `CrossingAtI` and `PVSplitting`. No namespace; no `set_option`; no sorry / TODO / axiom.
- Mathematical content: builds the corner δ-cutoffs (`vertDelta`, with comparisons to `arcsinDelta`), near/far distance bounds on each of the two sides of ρ (arc-side via `arc_*_at_rho_arcsin`, vertical-side via `vert_*_at_rho` from `fdBoundaryFun_seg4_dist_rho`) and of ρ+1 (vertical-side via `vert_*_at_rhoPlusOne` from `fdBoundaryFun_seg1_dist_rhoPlusOne`, arc-side via `arc_*_at_rhoPlusOne_arcsin`), bundles the analytic FTC hypotheses (`CornerFTCHyp`), and combines all the pieces through `PVSplitting.pv_tendsto_of_crossing_limit_asymmetric` to extract `HasGeneralizedWindingNumber γ ρ (−1/6)` and `HasGeneralizedWindingNumber γ (ρ+1) (−1/6)`.
- Total declarations: 22. (N2 = 22.)
