# CornerFTCAtRho.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/CornerFTCAtRho.lean`
Total lines: 1194
Namespace: (top-level `noncomputable section`, no namespace declared)

### `private def arcRef_rho`
- **Type**: `(t : ℝ) → ℂ` defined as `exp (↑(fdArcAngle t) * I) - ellipticPointRho`
- **What**: Reference function for the arc segment of the fundamental-domain boundary, subtracting the elliptic point ρ.
- **How**: Direct definition via `Complex.exp`, `fdArcAngle`, and `ellipticPointRho`.
- **Hypotheses**: none (just a function).
- **Uses from project**: `fdArcAngle`, `ellipticPointRho`
- **Used by**: `arcRef_rho_contDiff`, `arcRef_rho_eq`, `arcRef_rho_slitPlane`, `arcRef_rho_eventuallyEq`, `arc_ftc_rho`, `arc_arg_at_rho`
- **Visibility**: private
- **Lines**: 27
- **Notes**: none

### `private lemma fdArcAngle_contDiff`
- **Type**: `ContDiff ℝ ⊤ fdArcAngle`
- **What**: The arc-angle parameterization `fdArcAngle` is smooth.
- **How**: `unfold fdArcAngle` then `fun_prop`.
- **Hypotheses**: none.
- **Uses from project**: `fdArcAngle`
- **Used by**: `arcRef_rho_contDiff`, `arcRef_rp1_contDiff`
- **Visibility**: private
- **Lines**: 29-31
- **Notes**: none

### `private lemma arcRef_rho_contDiff`
- **Type**: `ContDiff ℝ ⊤ arcRef_rho`
- **What**: `arcRef_rho` is C∞.
- **How**: Composition of `Complex.contDiff_exp`, `ofRealCLM.contDiff`, `fdArcAngle_contDiff`, and `contDiff_const`.
- **Hypotheses**: none.
- **Uses from project**: `arcRef_rho`, `fdArcAngle_contDiff`
- **Used by**: `arc_ftc_rho`
- **Visibility**: private
- **Lines**: 33-37
- **Notes**: none

### `private lemma arcRef_rho_eq`
- **Type**: `(H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) → fdBoundaryFun H t - ellipticPointRho = arcRef_rho t`
- **What**: On the arc parameter range (1/5, 3/5], the boundary function minus ρ equals `arcRef_rho`.
- **How**: Direct unfolding via `fdBoundaryFun_arc_eq_exp`.
- **Hypotheses**: t in arc range.
- **Uses from project**: `arcRef_rho`, `fdBoundaryFun`, `fdBoundaryFun_arc_eq_exp`, `ellipticPointRho`
- **Used by**: `arcRef_rho_eventuallyEq`, `arc_ftc_rho`
- **Visibility**: private
- **Lines**: 39-42
- **Notes**: none

### `private lemma arcRef_rho_slitPlane`
- **Type**: `{t : ℝ} (ht1 : 1/5 ≤ t) (ht2 : t < 3/5) → arcRef_rho t ∈ Complex.slitPlane`
- **What**: On the arc range [1/5, 3/5), `arcRef_rho t` lies in the slit plane (positive real part).
- **How**: Rewrites via `exp_mul_I` to real cos/sin, uses `Real.cos_lt_cos_of_nonneg_of_le_pi` against `cos(2π/3) = -1/2` to show the real part is positive.
- **Hypotheses**: t ∈ [1/5, 3/5).
- **Uses from project**: `arcRef_rho`, `fdArcAngle`, `ellipticPointRho`
- **Used by**: `arc_ftc_rho`
- **Visibility**: private
- **Lines**: 44-60
- **Notes**: none

### `private lemma arcRef_rho_eventuallyEq`
- **Type**: `(H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t < 3/5) → (fun s => fdBoundaryFun H s - ellipticPointRho) =ᶠ[𝓝 t] arcRef_rho`
- **What**: Near each interior arc point, `fdBoundaryFun - ρ` agrees with `arcRef_rho` eventually.
- **How**: Constructs the eventual neighborhood via `Filter.eventually_of_mem` and `Filter.inter_mem (Ioi_mem_nhds _) (Iio_mem_nhds _)`, applies `arcRef_rho_eq`.
- **Hypotheses**: t in open arc range (1/5, 3/5).
- **Uses from project**: `arcRef_rho`, `arcRef_rho_eq`, `fdBoundaryFun`, `ellipticPointRho`
- **Used by**: `arc_ftc_rho`
- **Visibility**: private
- **Lines**: 62-69
- **Notes**: none

### `private def ref_seg1_rho`
- **Type**: `(H : ℝ) (t : ℝ) → ℂ` defined as `1 + (↑H - ↑(Real.sqrt 3) / 2 - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I`
- **What**: Reference function for seg1 (vertical right edge) minus ρ.
- **How**: Direct definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `ref_seg1_rho_contDiff`, `ref_seg1_rho_slitPlane`, `fdBoundary_sub_rho_eq_ref_seg1`, `seg1_ftc_rho`
- **Visibility**: private
- **Lines**: 71-72
- **Notes**: none

### `private lemma ref_seg1_rho_contDiff`
- **Type**: `(H : ℝ) → ContDiff ℝ ⊤ (ref_seg1_rho H)`
- **What**: `ref_seg1_rho H` is C∞ in t.
- **How**: Composition of `contDiff_const`, `Complex.ofRealCLM.contDiff`, etc.
- **Hypotheses**: none.
- **Uses from project**: `ref_seg1_rho`
- **Used by**: `seg1_ftc_rho`
- **Visibility**: private
- **Lines**: 74-77
- **Notes**: none

### `private lemma ref_seg1_rho_slitPlane`
- **Type**: `(H t : ℝ) → ref_seg1_rho H t ∈ Complex.slitPlane`
- **What**: `ref_seg1_rho H t` lies in slit plane (real part = 1 > 0).
- **How**: Real part is `1`, hence positive; `norm_num`.
- **Hypotheses**: none.
- **Uses from project**: `ref_seg1_rho`
- **Used by**: `seg1_ftc_rho`
- **Visibility**: private
- **Lines**: 79-85
- **Notes**: none

### `private lemma fdBoundary_sub_rho_eq_ref_seg1`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ≤ 1/5) → fdBoundaryFun H t - ellipticPointRho = ref_seg1_rho H t`
- **What**: On seg1 ([0, 1/5]), `fdBoundaryFun - ρ` equals `ref_seg1_rho`.
- **How**: `simp` on `fdBoundaryFun` definition (ite branches) plus `ring`.
- **Hypotheses**: t ≤ 1/5.
- **Uses from project**: `fdBoundaryFun`, `ellipticPointRho`, `ref_seg1_rho`
- **Used by**: `fdBoundary_sub_rho_eeq_ref_seg1`, `seg1_ftc_rho`
- **Visibility**: private
- **Lines**: 87-91
- **Notes**: none

### `private lemma fdBoundary_sub_rho_eeq_ref_seg1`
- **Type**: `(H : ℝ) {t : ℝ} (ht : t < 1/5) → (fun s => fdBoundaryFun H s - ellipticPointRho) =ᶠ[𝓝 t] ref_seg1_rho H`
- **What**: Near interior seg1 points, the boundary-minus-ρ agrees eventually with `ref_seg1_rho`.
- **How**: `Filter.eventually_of_mem (Iio_mem_nhds ht)` + `fdBoundary_sub_rho_eq_ref_seg1`.
- **Hypotheses**: t < 1/5.
- **Uses from project**: `fdBoundary_sub_rho_eq_ref_seg1`, `fdBoundaryFun`, `ellipticPointRho`, `ref_seg1_rho`
- **Used by**: `seg1_ftc_rho`
- **Visibility**: private
- **Lines**: 93-96
- **Notes**: none

### `private def ref_seg4_rho`
- **Type**: `(H : ℝ) (t : ℝ) → ℂ` defined as `↑(5 * (t - 3/5) * (H - Real.sqrt 3 / 2)) * I`
- **What**: Reference function for seg4 (vertical right edge above ρ) minus ρ.
- **How**: Direct definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `ref_seg4_rho_contDiff`, `ref_seg4_rho_slitPlane`, `fdBoundary_sub_rho_eq_ref_seg4`, `seg4_ftc_rho`, `vert_arg_at_rho`
- **Visibility**: private
- **Lines**: 98-99
- **Notes**: none

### `private lemma ref_seg4_rho_contDiff`
- **Type**: `(H : ℝ) → ContDiff ℝ ⊤ (ref_seg4_rho H)`
- **What**: `ref_seg4_rho H` is C∞.
- **How**: Composition of basic smooth pieces.
- **Hypotheses**: none.
- **Uses from project**: `ref_seg4_rho`
- **Used by**: `seg4_ftc_rho`
- **Visibility**: private
- **Lines**: 101-105
- **Notes**: none

### `private lemma ref_seg4_rho_slitPlane`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {t : ℝ} (ht3 : 3/5 < t) (_ht4 : t ≤ 4/5) → ref_seg4_rho H t ∈ Complex.slitPlane`
- **What**: For valid heights H and t ∈ (3/5, 4/5], `ref_seg4_rho H t` lies in slit plane (imaginary part > 0).
- **How**: Unfolds `fdHeightValid` to get `H > √3/2`, then `nlinarith` on imaginary part.
- **Hypotheses**: H > √3/2; t ∈ (3/5, 4/5].
- **Uses from project**: `ref_seg4_rho`, `fdHeightValid`
- **Used by**: `seg4_ftc_rho`
- **Visibility**: private
- **Lines**: 107-117
- **Notes**: none

### `private lemma fdBoundary_sub_rho_eq_ref_seg4`
- **Type**: `(H : ℝ) {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) → fdBoundaryFun H t - ellipticPointRho = ref_seg4_rho H t`
- **What**: On seg4 (3/5, 4/5], `fdBoundaryFun - ρ` equals `ref_seg4_rho`.
- **How**: `simp` on ite branches + `push_cast; ring`.
- **Hypotheses**: t ∈ (3/5, 4/5].
- **Uses from project**: `fdBoundaryFun`, `ellipticPointRho`, `ref_seg4_rho`
- **Used by**: `fdBoundary_sub_rho_eeq_ref_seg4`, `seg4_ftc_rho`, `vert_arg_at_rho`
- **Visibility**: private
- **Lines**: 119-127
- **Notes**: none

### `private lemma fdBoundary_sub_rho_eeq_ref_seg4`
- **Type**: `(H : ℝ) {t : ℝ} (ht3 : 3/5 < t) (ht4 : t < 4/5) → (fun s => fdBoundaryFun H s - ellipticPointRho) =ᶠ[𝓝 t] ref_seg4_rho H`
- **What**: Near each interior seg4 point, agreement of boundary-minus-ρ with `ref_seg4_rho`.
- **How**: Standard `Filter.eventually_of_mem` neighborhood construction.
- **Hypotheses**: t ∈ (3/5, 4/5) open.
- **Uses from project**: `fdBoundary_sub_rho_eq_ref_seg4`, `fdBoundaryFun`, `ellipticPointRho`, `ref_seg4_rho`
- **Used by**: `seg4_ftc_rho`
- **Visibility**: private
- **Lines**: 129-137
- **Notes**: none

### `private def ref_seg5_rho`
- **Type**: `(H : ℝ) (t : ℝ) → ℂ` defined as `(5 * ↑t - 4) + (↑H - ↑(Real.sqrt 3) / 2) * I`
- **What**: Reference function for seg5 (horizontal top) minus ρ.
- **How**: Direct definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `ref_seg5_rho_contDiff`, `ref_seg5_rho_slitPlane`, `fdBoundary_sub_rho_eq_ref_seg5`, `seg5_ftc_rho`
- **Visibility**: private
- **Lines**: 139-140
- **Notes**: none

### `private lemma ref_seg5_rho_contDiff`
- **Type**: `(H : ℝ) → ContDiff ℝ ⊤ (ref_seg5_rho H)`
- **What**: `ref_seg5_rho H` is C∞.
- **How**: Standard composition of C∞ pieces.
- **Hypotheses**: none.
- **Uses from project**: `ref_seg5_rho`
- **Used by**: `seg5_ftc_rho`
- **Visibility**: private
- **Lines**: 142-144
- **Notes**: none

### `private lemma ref_seg5_rho_slitPlane`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) (t : ℝ) → ref_seg5_rho H t ∈ Complex.slitPlane`
- **What**: For valid heights, `ref_seg5_rho H t` always lies in slit plane (im = H - √3/2 > 0).
- **How**: Unfolds `fdHeightValid`, computes imaginary part = H - √3/2 > 0.
- **Hypotheses**: H > √3/2.
- **Uses from project**: `ref_seg5_rho`, `fdHeightValid`
- **Used by**: `seg5_ftc_rho`
- **Visibility**: private
- **Lines**: 146-158
- **Notes**: none

### `private lemma fdBoundary_sub_rho_eq_ref_seg5`
- **Type**: `(H : ℝ) {t : ℝ} (ht : 4/5 < t) → fdBoundaryFun H t - ellipticPointRho = ref_seg5_rho H t`
- **What**: On seg5 (4/5, ∞), `fdBoundaryFun - ρ` equals `ref_seg5_rho`.
- **How**: `simp` on ite branches + `ring`.
- **Hypotheses**: t > 4/5.
- **Uses from project**: `fdBoundaryFun`, `ellipticPointRho`, `ref_seg5_rho`
- **Used by**: `fdBoundary_sub_rho_eeq_ref_seg5`, `seg5_ftc_rho`
- **Visibility**: private
- **Lines**: 160-166
- **Notes**: none

### `private lemma fdBoundary_sub_rho_eeq_ref_seg5`
- **Type**: `(H : ℝ) {t : ℝ} (ht : 4/5 < t) → (fun s => fdBoundaryFun H s - ellipticPointRho) =ᶠ[𝓝 t] ref_seg5_rho H`
- **What**: Near each seg5 point, eventual agreement.
- **How**: Standard `Filter.eventually_of_mem (Ioi_mem_nhds ht)`.
- **Hypotheses**: t > 4/5.
- **Uses from project**: `fdBoundary_sub_rho_eq_ref_seg5`, `fdBoundaryFun`, `ellipticPointRho`, `ref_seg5_rho`
- **Used by**: `seg5_ftc_rho`
- **Visibility**: private
- **Lines**: 168-171
- **Notes**: none

### `private lemma integrand_form_eq'`
- **Type**: `(f : ℝ → ℂ) (z : ℂ) (t : ℝ) → (f t - z)⁻¹ * deriv f t = deriv (fun s => f s - z) t / (f t - z)`
- **What**: Algebraic identity converting `(f-z)⁻¹ · f'` into `deriv(f - z) / (f - z)` (the log-derivative form needed for FTC).
- **How**: Uses `deriv_add_const` (treating z subtraction as adding -z) and `div_eq_mul_inv` plus `mul_comm`.
- **Hypotheses**: none (purely algebraic).
- **Uses from project**: []
- **Used by**: `fdBoundary_ftc_telescope_rho`, `fdBoundary_integrable_left_of_rho`, `fdBoundary_integrable_right_of_rho`, `fdBoundary_ftc_telescope_rp1`, `fdBoundary_integrable_left_of_rp1`, `fdBoundary_integrable_right_of_rp1`
- **Visibility**: private
- **Lines**: 173-176
- **Notes**: none

### `private theorem seg1_ftc_rho`
- **Type**: `(H : ℝ) → IntervalIntegrable ... volume 0 (1/5) ∧ ∫ t in 0..(1/5), ... = log(...(1/5)...) - log(...0...)`
- **What**: FTC on seg1 [0, 1/5]: integrability and integral value of the log-derivative for `fdBoundaryFun - ρ`.
- **How**: `LogDerivFTC.ftc_log_pieceFM` with: `ref_seg1_rho_contDiff` continuity/differentiability/deriv-continuity, `ref_seg1_rho_slitPlane` for log-branch, agreement on segment.
- **Hypotheses**: just H.
- **Uses from project**: `LogDerivFTC.ftc_log_pieceFM`, `ref_seg1_rho_contDiff`, `ref_seg1_rho_slitPlane`, `fdBoundary_sub_rho_eq_ref_seg1`, `fdBoundary_sub_rho_eeq_ref_seg1`, `fdBoundaryFun`, `ellipticPointRho`
- **Used by**: `fdBoundary_ftc_telescope_rho`, `fdBoundary_integrable_left_of_rho`
- **Visibility**: private
- **Lines**: 178-193
- **Notes**: none

### `private theorem arc_ftc_rho`
- **Type**: `(H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2/5) → IntervalIntegrable ... volume (1/5) (3/5 - δ) ∧ ∫ t in 1/5..(3/5-δ), ... = log(...) - log(...)`
- **What**: FTC on the arc [1/5, 3/5 - δ]: integrability and value.
- **How**: `LogDerivFTC.ftc_log_pieceFM` applied to `arcRef_rho`. Endpoint at 1/5 uses `fdBoundaryFun_at_one_fifth` and `fdArcAngle_at_one_fifth` to bridge `arcRef_rho (1/5) = fdBoundaryFun H (1/5) - ρ`.
- **Hypotheses**: 0 < δ < 2/5.
- **Uses from project**: `LogDerivFTC.ftc_log_pieceFM`, `arcRef_rho_contDiff`, `arcRef_rho_slitPlane`, `arcRef_rho_eq`, `arcRef_rho_eventuallyEq`, `fdBoundaryFun_at_one_fifth`, `fdArcAngle_at_one_fifth`, `arcRef_rho`, `ellipticPointRho`, `ellipticPointRhoPlusOne`
- **Used by**: `fdBoundary_ftc_telescope_rho`, `fdBoundary_integrable_left_of_rho`
- **Visibility**: private
- **Lines**: 195-218
- **Notes**: none

### `private theorem seg4_ftc_rho`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) → IntervalIntegrable ... volume (3/5+δ) (4/5) ∧ ∫ ... = log(...) - log(...)`
- **What**: FTC on seg4 [3/5 + δ, 4/5].
- **How**: `LogDerivFTC.ftc_log_pieceFM` with `ref_seg4_rho` pieces.
- **Hypotheses**: valid height; 0 < δ < 1/5.
- **Uses from project**: `LogDerivFTC.ftc_log_pieceFM`, `ref_seg4_rho_contDiff`, `ref_seg4_rho_slitPlane`, `fdBoundary_sub_rho_eq_ref_seg4`, `fdBoundary_sub_rho_eeq_ref_seg4`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRho`
- **Used by**: `fdBoundary_ftc_telescope_rho`, `fdBoundary_integrable_right_of_rho`
- **Visibility**: private
- **Lines**: 220-236
- **Notes**: none

### `private theorem seg5_ftc_rho`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) → IntervalIntegrable ... volume (4/5) 1 ∧ ∫ ... = log(...) - log(...)`
- **What**: FTC on seg5 [4/5, 1].
- **How**: `LogDerivFTC.ftc_log_pieceFM` with `ref_seg5_rho` pieces, plus endpoint matching via `fdBoundaryFun_at_four_fifths` and `fdBoundaryFun_at_one`.
- **Hypotheses**: valid height.
- **Uses from project**: `LogDerivFTC.ftc_log_pieceFM`, `ref_seg5_rho_contDiff`, `ref_seg5_rho_slitPlane`, `fdBoundary_sub_rho_eq_ref_seg5`, `fdBoundary_sub_rho_eeq_ref_seg5`, `fdBoundaryFun_at_four_fifths`, `fdBoundaryFun_at_one`, `fdHeightValid`, `fdStart`, `ellipticPointRho`
- **Used by**: `fdBoundary_ftc_telescope_rho`, `fdBoundary_integrable_right_of_rho`
- **Visibility**: private
- **Lines**: 238-260
- **Notes**: none

### `private theorem fdBoundary_ftc_telescope_rho`
- **Type**: `(H : ℝ) (hH : 1 < H) {δL δR : ℝ} (hδL : 0 < δL) (hδL' : δL < 2/5) (hδR : 0 < δR) (hδR' : δR < 1/5) → (∫ t in 0..(3/5-δL), ...) + (∫ t in (3/5+δR)..1, ...) = log(...) - log(...)`
- **What**: Telescoping of seg1+arc and seg4+seg5 FTC pieces around ρ, summing the four FTC pieces (with ε-excised intervals on the arc/seg4 side around ρ at t = 3/5).
- **How**: Combines `seg1_ftc_rho`, `arc_ftc_rho`, `seg4_ftc_rho`, `seg5_ftc_rho` via `intervalIntegral.integral_add_adjacent_intervals` on each side, then closes via `fdBoundaryFun_closed H`.
- **Hypotheses**: H > 1; 0 < δL < 2/5; 0 < δR < 1/5.
- **Uses from project**: `seg1_ftc_rho`, `arc_ftc_rho`, `seg4_ftc_rho`, `seg5_ftc_rho`, `fdBoundaryFun_closed`, `fdHeightValid_of_one_lt`, `integrand_form_eq'`, `fdBoundaryFun`, `ellipticPointRho`
- **Used by**: `cornerFTCHyp_atRho`
- **Visibility**: private
- **Lines**: 262-297
- **Notes**: proof >30 lines

### `private theorem fdBoundary_integrable_left_of_rho`
- **Type**: `(H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2/5) → IntervalIntegrable (fun t => (fdBoundaryFun H t - ρ)⁻¹ · deriv (fdBoundaryFun H) t) volume 0 (3/5 - δ)`
- **What**: Left-of-ρ integrability of the log-derivative integrand on [0, 3/5 - δ].
- **How**: Converts to log-derivative form via `integrand_form_eq'`, then `(seg1_ftc_rho ...).1.trans (arc_ftc_rho ...).1`.
- **Hypotheses**: 0 < δ < 2/5.
- **Uses from project**: `integrand_form_eq'`, `seg1_ftc_rho`, `arc_ftc_rho`, `fdBoundaryFun`, `ellipticPointRho`
- **Used by**: `cornerFTCHyp_atRho`
- **Visibility**: private
- **Lines**: 299-304
- **Notes**: none

### `private theorem fdBoundary_integrable_right_of_rho`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) → IntervalIntegrable (fun t => (fdBoundaryFun H t - ρ)⁻¹ · deriv (fdBoundaryFun H) t) volume (3/5 + δ) 1`
- **What**: Right-of-ρ integrability of the log-derivative integrand on [3/5 + δ, 1].
- **How**: Converts to log-derivative form via `integrand_form_eq'`, then `(seg4_ftc_rho ...).1.trans (seg5_ftc_rho ...).1`.
- **Hypotheses**: valid height; 0 < δ < 1/5.
- **Uses from project**: `integrand_form_eq'`, `seg4_ftc_rho`, `seg5_ftc_rho`, `fdBoundaryFun`, `ellipticPointRho`, `fdHeightValid`
- **Used by**: `cornerFTCHyp_atRho`
- **Visibility**: private
- **Lines**: 306-312
- **Notes**: none

### `private theorem arc_norm_at_rho`
- **Type**: `(H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) → ‖fdBoundaryFun H (3/5 - arcsinDelta ε) - ellipticPointRho‖ = ε`
- **What**: At parameter `t = 3/5 - arcsinDelta ε` (the arc-side ε-radius excision point near ρ), the distance from the boundary to ρ equals ε.
- **How**: Uses `fdBoundaryFun_arc_dist_rho` to reduce to a sine, then simplifies via `Real.sin_neg`, `Real.sin_arcsin`, and `half_angle_arcsinDelta`.
- **Hypotheses**: 0 < ε < 1/3.
- **Uses from project**: `arcsinDelta`, `arcsinDelta_pos`, `arcsinDelta_lt_one_fifth`, `fdBoundaryFun_arc_dist_rho`, `fdArcAngle`, `half_angle_arcsinDelta`, `fdBoundaryFun`, `ellipticPointRho`
- **Used by**: `E_atRho_eq`, `arc_arg_at_rho` (via h_ne)
- **Visibility**: private
- **Lines**: 314-328
- **Notes**: none

### `private theorem vert_norm_at_rho`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < H - Real.sqrt 3 / 2) → ‖fdBoundaryFun H (3/5 + vertDelta H ε) - ellipticPointRho‖ = ε`
- **What**: At `t = 3/5 + vertDelta H ε` (the seg4-side ε-radius excision), distance to ρ equals ε.
- **How**: Uses `fdBoundaryFun_seg4_dist_rho` and `vertDelta` definition (= ε/(5(H - √3/2))), then `div_mul_cancel₀`.
- **Hypotheses**: valid height; 0 < ε < H - √3/2.
- **Uses from project**: `vertDelta`, `vertDelta_pos`, `vertDelta_lt_one_fifth`, `fdBoundaryFun_seg4_dist_rho`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRho`
- **Used by**: `E_atRho_eq`
- **Visibility**: private
- **Lines**: 330-342
- **Notes**: none

### `private lemma cos_theta_rho_identity`
- **Type**: `{α : ℝ} → Real.cos (2 * Real.pi / 3 - 2 * α) + 1/2 = 2 * Real.sin α * Real.cos (Real.pi / 6 - α)`
- **What**: Trigonometric identity relating cos(2π/3 - 2α) + 1/2 to a product of sines/cosines.
- **How**: Reduces `2π/3` to `π - π/3`, applies `Real.cos_pi_sub`, double-angle formulas, and `nlinarith` using `sin² + cos² = 1`.
- **Hypotheses**: α real.
- **Uses from project**: []
- **Used by**: `arcRef_sub_rho_decomp`
- **Visibility**: private
- **Lines**: 344-354
- **Notes**: none

### `private lemma sin_theta_rho_identity`
- **Type**: `{α : ℝ} → Real.sin (2 * Real.pi / 3 - 2 * α) - Real.sqrt 3 / 2 = 2 * Real.sin α * Real.sin (Real.pi / 6 - α)`
- **What**: Sin analog of `cos_theta_rho_identity`.
- **How**: Same pattern: π - π/3 reduction, double-angle, `linarith` after multiplying by `sin² + cos² = 1`.
- **Hypotheses**: α real.
- **Uses from project**: []
- **Used by**: `arcRef_sub_rho_decomp`
- **Visibility**: private
- **Lines**: 356-370
- **Notes**: none

### `private lemma arcRef_sub_rho_decomp`
- **Type**: `{θ α : ℝ} (hθ : θ = 2 * Real.pi / 3 - 2 * α) → (↑(Real.cos θ) + ↑(Real.sin θ) * I : ℂ) - ellipticPointRho = ↑(2 * Real.sin α) * (↑(Real.cos (π/6 - α)) + ↑(Real.sin (π/6 - α)) * I)`
- **What**: Polar decomposition: when θ = 2π/3 - 2α, the complex number `(cos θ + i sin θ) - ρ` factors as `2 sin α · (cos(π/6 - α) + i sin(π/6 - α))`.
- **How**: Component-wise `Complex.ext`, using `cos_theta_rho_identity` and `sin_theta_rho_identity`.
- **Hypotheses**: θ = 2π/3 - 2α.
- **Uses from project**: `cos_theta_rho_identity`, `sin_theta_rho_identity`, `ellipticPointRho`
- **Used by**: `arc_arg_at_rho`
- **Visibility**: private
- **Lines**: 372-383
- **Notes**: none

### `private theorem arc_arg_at_rho`
- **Type**: `(H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) → (fdBoundaryFun H (3/5 - arcsinDelta ε) - ellipticPointRho).arg = Real.pi / 6 - 5 * arcsinDelta ε * Real.pi / 12`
- **What**: The complex argument of the arc-side ε-excised boundary minus ρ equals `π/6 - 5·arcsinDelta(ε)·π/12`.
- **How**: Uses `fdBoundaryFun_arc_eq_exp`, then `arcRef_sub_rho_decomp` with α = 5·arcsinDelta(ε)·π/12, then `Complex.arg_mul_cos_add_sin_mul_I`.
- **Hypotheses**: 0 < ε < 1/3.
- **Uses from project**: `arcsinDelta`, `arcsinDelta_pos`, `arcsinDelta_lt_one_fifth`, `fdBoundaryFun_arc_eq_exp`, `fdArcAngle`, `arcRef_sub_rho_decomp`, `fdBoundaryFun`, `ellipticPointRho`
- **Used by**: `E_atRho_eq`
- **Visibility**: private
- **Lines**: 385-410
- **Notes**: none

### `private theorem vert_arg_at_rho`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < H - Real.sqrt 3 / 2) → (fdBoundaryFun H (3/5 + vertDelta H ε) - ellipticPointRho).arg = Real.pi / 2`
- **What**: Argument of the seg4-side ε-excised boundary minus ρ is π/2 (purely imaginary, positive im).
- **How**: Rewrites via `fdBoundary_sub_rho_eq_ref_seg4`, expresses the result as `(positive real) · I`, applies `arg_ofReal_mul_I`.
- **Hypotheses**: valid height; 0 < ε < H - √3/2.
- **Uses from project**: `fdBoundary_sub_rho_eq_ref_seg4`, `vertDelta`, `vertDelta_pos`, `vertDelta_lt_one_fifth`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRho`
- **Used by**: `E_atRho_eq`
- **Visibility**: private
- **Lines**: 412-423
- **Notes**: none

### `private def E_atRho`
- **Type**: `(H : ℝ) (ε : ℝ) → ℂ` defined as `Complex.log (... arc side ...) - Complex.log (... seg4 side ...)`
- **What**: The ε-parameterized log-difference at ρ: difference of log evaluations at the two ε-excised endpoints (arc-side and seg4-side) flanking ρ.
- **How**: Direct definition.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `ellipticPointRho`, `arcsinDelta`, `vertDelta`
- **Used by**: `E_atRho_eq`, `E_atRho_tendsto`, `cornerFTCHyp_atRho`
- **Visibility**: private
- **Lines**: 425-427
- **Notes**: none

### `private theorem E_atRho_eq`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < min (1/3) (H - Real.sqrt 3 / 2)) → E_atRho H ε = ↑(Real.pi / 6 - 5 * arcsinDelta ε * Real.pi / 12 - Real.pi / 2) * I`
- **What**: Explicit closed form of `E_atRho H ε`: pure imaginary, equal to `i · (π/6 - 5·arcsinDelta(ε)·π/12 - π/2)`.
- **How**: Uses `log_sub_eq_of_equal_norm` (since both norms equal ε by `arc_norm_at_rho` and `vert_norm_at_rho`), then plugs in `arc_arg_at_rho` and `vert_arg_at_rho`.
- **Hypotheses**: valid height; ε > 0 and ε < min(1/3, H - √3/2).
- **Uses from project**: `E_atRho`, `arc_norm_at_rho`, `vert_norm_at_rho`, `log_sub_eq_of_equal_norm`, `arc_arg_at_rho`, `vert_arg_at_rho`, `arcsinDelta`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRho`
- **Used by**: `E_atRho_tendsto`
- **Visibility**: private
- **Lines**: 429-447
- **Notes**: none

### `private theorem E_atRho_tendsto`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) → Tendsto (E_atRho H) (𝓝[>] 0) (𝓝 (-(↑Real.pi / 3 * I)))`
- **What**: As ε → 0⁺, `E_atRho H ε → -π·i/3` (the corner-angle limit at ρ, with the π/3 reflecting the 60-degree corner).
- **How**: Eventually-equal to the closed form from `E_atRho_eq`, then ε → 0 gives arcsinDelta(0) = 0, so the closed form tends to π/6 - 0 - π/2 = -π/3, times I.
- **Hypotheses**: valid height.
- **Uses from project**: `E_atRho`, `E_atRho_eq`, `arcsinDelta`, `fdHeightValid`
- **Used by**: `cornerFTCHyp_atRho`
- **Visibility**: private
- **Lines**: 449-475
- **Notes**: none

### `def cornerFTCHyp_atRho`
- **Type**: `{H : ℝ} (hH : 1 < H) {γ : PiecewiseC1Path (fdStart H) (fdStart H)} (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) → CornerFTCHyp γ ellipticPointRho (3/5) arcsinDelta (vertDelta H) (min (1/3) (H - Real.sqrt 3 / 2)) (-(↑Real.pi / 3 * I))`
- **What**: The complete `CornerFTCHyp` instance at ρ: packages the FTC telescope, left/right integrability, and limit of E_atRho.
- **How**: Structure assembly: `E := E_atRho H`; `h_ftc` uses `transfer_integral` to lift the boundary-function FTC to the abstract path γ, then `fdBoundary_ftc_telescope_rho`; `hint_left/right` lift integrability via `transfer_integrability` from `fdBoundary_integrable_left/right_of_rho`; `h_limit` is `E_atRho_tendsto`.
- **Hypotheses**: H > 1; γ piecewise-C¹ path agreeing with `fdBoundaryFun H` on [0,1].
- **Uses from project**: `CornerFTCHyp`, `E_atRho`, `fdBoundary_ftc_telescope_rho`, `fdBoundary_integrable_left_of_rho`, `fdBoundary_integrable_right_of_rho`, `E_atRho_tendsto`, `arcsinDelta`, `arcsinDelta_pos`, `arcsinDelta_lt_one_fifth`, `vertDelta`, `vertDelta_pos`, `vertDelta_lt_one_fifth`, `transfer_integral`, `transfer_integrability`, `fdHeightValid_of_one_lt`, `ellipticPointRho`, `fdBoundaryFun`, `fdStart`, `PiecewiseC1Path`
- **Used by**: unused in file (consumed downstream)
- **Visibility**: public
- **Lines**: 478-513
- **Notes**: headline at ρ; structure constructor

### `private def ref_seg1_rp1`
- **Type**: `(H : ℝ) (t : ℝ) → ℂ` defined as `↑(5 * (1/5 - t) * (H - Real.sqrt 3 / 2)) * I`
- **What**: Reference function for seg1 minus ρ+1.
- **How**: Direct definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `ref_seg1_rp1_contDiff`, `ref_seg1_rp1_slitPlane`, `fdBoundary_sub_rp1_eq_ref_seg1`, `seg1_ftc_rp1`, `vert_arg_at_rp1`
- **Visibility**: private
- **Lines**: 515-516
- **Notes**: none

### `private lemma ref_seg1_rp1_contDiff`
- **Type**: `(H : ℝ) → ContDiff ℝ ⊤ (ref_seg1_rp1 H)`
- **What**: `ref_seg1_rp1 H` is C∞.
- **How**: Composition of C∞ pieces.
- **Hypotheses**: none.
- **Uses from project**: `ref_seg1_rp1`
- **Used by**: `seg1_ftc_rp1`
- **Visibility**: private
- **Lines**: 518-522
- **Notes**: none

### `private lemma ref_seg1_rp1_slitPlane`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t < 1/5) → ref_seg1_rp1 H t ∈ Complex.slitPlane`
- **What**: For valid heights and t ∈ [0, 1/5), `ref_seg1_rp1 H t` is in slit plane (im > 0).
- **How**: Unfolds `fdHeightValid`, computes imaginary part > 0 via `nlinarith`.
- **Hypotheses**: valid height; 0 ≤ t < 1/5.
- **Uses from project**: `ref_seg1_rp1`, `fdHeightValid`
- **Used by**: `seg1_ftc_rp1`
- **Visibility**: private
- **Lines**: 524-534
- **Notes**: none

### `private lemma fdBoundary_sub_rp1_eq_ref_seg1`
- **Type**: `(H : ℝ) {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1/5) → fdBoundaryFun H t - ellipticPointRhoPlusOne = ref_seg1_rp1 H t`
- **What**: On seg1, boundary-minus-(ρ+1) equals `ref_seg1_rp1`.
- **How**: `simp` on ite branches + `push_cast; ring`.
- **Hypotheses**: t ∈ [0, 1/5].
- **Uses from project**: `fdBoundaryFun`, `ellipticPointRhoPlusOne`, `ref_seg1_rp1`
- **Used by**: `fdBoundary_sub_rp1_eeq_ref_seg1`, `seg1_ftc_rp1`, `vert_arg_at_rp1`
- **Visibility**: private
- **Lines**: 536-542
- **Notes**: none

### `private lemma fdBoundary_sub_rp1_eeq_ref_seg1`
- **Type**: `(H : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1/5) → (fun s => fdBoundaryFun H s - ellipticPointRhoPlusOne) =ᶠ[𝓝 t] ref_seg1_rp1 H`
- **What**: Eventual agreement near interior seg1 points.
- **How**: Standard `Filter.eventually_of_mem` + `fdBoundary_sub_rp1_eq_ref_seg1`.
- **Hypotheses**: t ∈ (0, 1/5) open.
- **Uses from project**: `fdBoundary_sub_rp1_eq_ref_seg1`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`, `ref_seg1_rp1`
- **Used by**: `seg1_ftc_rp1`
- **Visibility**: private
- **Lines**: 544-551
- **Notes**: none

### `private def arcRef_rp1`
- **Type**: `(t : ℝ) → ℂ` defined as `exp (↑(fdArcAngle t) * I) - ellipticPointRhoPlusOne`
- **What**: Arc reference, minus ρ+1.
- **How**: Direct definition.
- **Hypotheses**: none.
- **Uses from project**: `fdArcAngle`, `ellipticPointRhoPlusOne`
- **Used by**: `arcRef_rp1_contDiff`, `arcRef_rp1_eq`, `arcRef_rp1_eventuallyEq`, `arcRef_rp1_neg_slitPlane`, `arc_ftc_neg_rp1`, `arcRef_rp1_im_pos`, `branch_correction_arc_rp1`, `arc_arg_at_rp1`
- **Visibility**: private
- **Lines**: 553
- **Notes**: none

### `private lemma arcRef_rp1_contDiff`
- **Type**: `ContDiff ℝ ⊤ arcRef_rp1`
- **What**: `arcRef_rp1` is C∞.
- **How**: Standard composition.
- **Hypotheses**: none.
- **Uses from project**: `arcRef_rp1`, `fdArcAngle_contDiff`
- **Used by**: `arc_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 555-559
- **Notes**: none

### `private lemma arcRef_rp1_eq`
- **Type**: `(H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) → fdBoundaryFun H t - ellipticPointRhoPlusOne = arcRef_rp1 t`
- **What**: On the arc range (1/5, 3/5], boundary-minus-(ρ+1) equals `arcRef_rp1`.
- **How**: Via `fdBoundaryFun_arc_eq_exp`.
- **Hypotheses**: t ∈ (1/5, 3/5].
- **Uses from project**: `arcRef_rp1`, `fdBoundaryFun`, `fdBoundaryFun_arc_eq_exp`, `ellipticPointRhoPlusOne`
- **Used by**: `arcRef_rp1_eventuallyEq`, `arc_ftc_neg_rp1`, `branch_correction_arc_rp1`
- **Visibility**: private
- **Lines**: 561-564
- **Notes**: none

### `private lemma arcRef_rp1_eventuallyEq`
- **Type**: `(H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t < 3/5) → (fun s => fdBoundaryFun H s - ellipticPointRhoPlusOne) =ᶠ[𝓝 t] arcRef_rp1`
- **What**: Eventual agreement near interior arc points.
- **How**: Standard.
- **Hypotheses**: t ∈ (1/5, 3/5) open.
- **Uses from project**: `arcRef_rp1`, `arcRef_rp1_eq`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `arc_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 566-573
- **Notes**: none

### `private lemma arcRef_rp1_neg_slitPlane`
- **Type**: `{t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) → -(arcRef_rp1 t) ∈ Complex.slitPlane`
- **What**: For t ∈ (1/5, 3/5], the negation `-(arcRef_rp1 t)` lies in slit plane (positive re for negated).
- **How**: Uses `Real.cos_le_cos_of_nonneg_of_le_pi` against `cos(π/3) = 1/2`, then case-splits at the endpoint t = 3/5 via `eq_or_lt_of_le ht2` and `fdArcAngle_at_three_fifths`.
- **Hypotheses**: t ∈ (1/5, 3/5].
- **Uses from project**: `arcRef_rp1`, `fdArcAngle`, `fdArcAngle_at_three_fifths`, `ellipticPointRhoPlusOne`
- **Used by**: `arc_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 575-599
- **Notes**: none

### `private theorem seg1_ftc_rp1`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) → IntervalIntegrable ... volume 0 (1/5 - δ) ∧ ∫ ... = log(...) - log(...)`
- **What**: FTC on seg1 [0, 1/5 - δ] for `fdBoundaryFun - ρ+1`.
- **How**: `LogDerivFTC.ftc_log_pieceFM` with `ref_seg1_rp1` pieces.
- **Hypotheses**: valid height; 0 < δ < 1/5.
- **Uses from project**: `LogDerivFTC.ftc_log_pieceFM`, `ref_seg1_rp1_contDiff`, `ref_seg1_rp1_slitPlane`, `fdBoundary_sub_rp1_eq_ref_seg1`, `fdBoundary_sub_rp1_eeq_ref_seg1`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `fdBoundary_ftc_telescope_rp1`, `fdBoundary_integrable_left_of_rp1`
- **Visibility**: private
- **Lines**: 601-618
- **Notes**: none

### `private theorem arc_ftc_neg_rp1`
- **Type**: `(H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2/5) → IntervalIntegrable ... volume (1/5+δ) (3/5) ∧ ∫ ... = log(-(...3/5...)) - log(-(...1/5+δ...))`
- **What**: FTC on the arc [1/5 + δ, 3/5], using the negated-form log (because for ρ+1 the arc is in the wrong half-plane).
- **How**: Uses `LogDerivFTC.ftc_log_neg_on_segment` (the negated-form FTC), then patches the ae-agreement via `intervalIntegral.integral_congr_ae` and a measure-zero exclusion of the endpoint 3/5.
- **Hypotheses**: 0 < δ < 2/5.
- **Uses from project**: `LogDerivFTC.ftc_log_neg_on_segment`, `arcRef_rp1`, `arcRef_rp1_contDiff`, `arcRef_rp1_eq`, `arcRef_rp1_eventuallyEq`, `arcRef_rp1_neg_slitPlane`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `ftc_right_neg_log_rp1`, `branch_correction_arc_rp1`, `fdBoundary_integrable_right_of_rp1`
- **Visibility**: private
- **Lines**: 620-649
- **Notes**: none

### `private theorem vert_norm_at_rp1`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < H - Real.sqrt 3 / 2) → ‖fdBoundaryFun H (1/5 - vertDelta H ε) - ellipticPointRhoPlusOne‖ = ε`
- **What**: At `t = 1/5 - vertDelta H ε`, distance to ρ+1 equals ε.
- **How**: `fdBoundaryFun_seg1_dist_rhoPlusOne` + `div_mul_cancel₀`.
- **Hypotheses**: valid height; 0 < ε < H - √3/2.
- **Uses from project**: `vertDelta`, `vertDelta_pos`, `vertDelta_lt_one_fifth`, `fdBoundaryFun_seg1_dist_rhoPlusOne`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `E_atRhoPlusOne_eq`
- **Visibility**: private
- **Lines**: 651-664
- **Notes**: none

### `private theorem arc_norm_at_rp1`
- **Type**: `(H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) → ‖fdBoundaryFun H (1/5 + arcsinDelta ε) - ellipticPointRhoPlusOne‖ = ε`
- **What**: At `t = 1/5 + arcsinDelta ε`, distance to ρ+1 equals ε.
- **How**: `fdBoundaryFun_arc_dist_rhoPlusOne` + `half_angle_arcsinDelta` + `Real.sin_arcsin`.
- **Hypotheses**: 0 < ε < 1/3.
- **Uses from project**: `arcsinDelta`, `arcsinDelta_pos`, `arcsinDelta_lt_one_fifth`, `fdBoundaryFun_arc_dist_rhoPlusOne`, `fdArcAngle`, `half_angle_arcsinDelta`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `E_atRhoPlusOne_eq`
- **Visibility**: private
- **Lines**: 666-680
- **Notes**: none

### `private theorem vert_arg_at_rp1`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < H - Real.sqrt 3 / 2) → (fdBoundaryFun H (1/5 - vertDelta H ε) - ellipticPointRhoPlusOne).arg = Real.pi / 2`
- **What**: Argument of seg1-side ε-excised boundary minus (ρ+1) is π/2 (purely imaginary, positive).
- **How**: Rewrites via `fdBoundary_sub_rp1_eq_ref_seg1`, then `arg_ofReal_mul_I` (positive real times I).
- **Hypotheses**: valid height; 0 < ε < H - √3/2.
- **Uses from project**: `fdBoundary_sub_rp1_eq_ref_seg1`, `vertDelta`, `vertDelta_pos`, `vertDelta_lt_one_fifth`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `E_atRhoPlusOne_eq`
- **Visibility**: private
- **Lines**: 682-694
- **Notes**: none

### `private lemma cos_theta_rp1_identity`
- **Type**: `{α : ℝ} → Real.cos (Real.pi / 3 + 2 * α) - 1/2 = 2 * Real.sin α * Real.cos (5 * Real.pi / 6 + α)`
- **What**: Trig identity relating cos(π/3 + 2α) - 1/2 to a sine-cosine product.
- **How**: Reduces 5π/6 to π - π/6, computes `Real.cos_pi_sub`, double-angle, `nlinarith`.
- **Hypotheses**: α real.
- **Uses from project**: []
- **Used by**: `arcRef_sub_rp1_decomp`
- **Visibility**: private
- **Lines**: 696-708
- **Notes**: none

### `private lemma sin_theta_rp1_identity`
- **Type**: `{α : ℝ} → Real.sin (Real.pi / 3 + 2 * α) - Real.sqrt 3 / 2 = 2 * Real.sin α * Real.sin (5 * Real.pi / 6 + α)`
- **What**: Sin analog of `cos_theta_rp1_identity`.
- **How**: Same pattern with sin double-angle.
- **Hypotheses**: α real.
- **Uses from project**: []
- **Used by**: `arcRef_sub_rp1_decomp`
- **Visibility**: private
- **Lines**: 710-725
- **Notes**: none

### `private lemma arcRef_sub_rp1_decomp`
- **Type**: `{θ α : ℝ} (hθ : θ = Real.pi / 3 + 2 * α) → (↑(Real.cos θ) + ↑(Real.sin θ) * I : ℂ) - ellipticPointRhoPlusOne = ↑(2 * Real.sin α) * (↑(Real.cos (5π/6 + α)) + ↑(Real.sin (5π/6 + α)) * I)`
- **What**: Polar decomposition of `(cos θ + i sin θ) - (ρ+1)` when θ = π/3 + 2α.
- **How**: Component-wise via `Complex.ext` using the two trig identities.
- **Hypotheses**: θ = π/3 + 2α.
- **Uses from project**: `cos_theta_rp1_identity`, `sin_theta_rp1_identity`, `ellipticPointRhoPlusOne`
- **Used by**: `arc_arg_at_rp1`
- **Visibility**: private
- **Lines**: 727-738
- **Notes**: none

### `private theorem arc_arg_at_rp1`
- **Type**: `(H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) → (fdBoundaryFun H (1/5 + arcsinDelta ε) - ellipticPointRhoPlusOne).arg = 5 * Real.pi / 6 + 5 * arcsinDelta ε * Real.pi / 12`
- **What**: Argument of the arc-side ε-excised boundary minus (ρ+1).
- **How**: Uses `fdBoundaryFun_arc_eq_exp`, then `arcRef_sub_rp1_decomp` with α = 5·arcsinDelta(ε)·π/12, then `Complex.arg_mul_cos_add_sin_mul_I`.
- **Hypotheses**: 0 < ε < 1/3.
- **Uses from project**: `arcsinDelta`, `arcsinDelta_pos`, `arcsinDelta_lt_one_fifth`, `fdBoundaryFun_arc_eq_exp`, `fdArcAngle`, `arcRef_sub_rp1_decomp`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `E_atRhoPlusOne_eq`
- **Visibility**: private
- **Lines**: 740-766
- **Notes**: none

### `private def E_atRhoPlusOne`
- **Type**: `(H : ℝ) (ε : ℝ) → ℂ` defined as `Complex.log (... seg1 side ...) - Complex.log (... arc side ...)`
- **What**: ε-parameterized log-difference at ρ+1.
- **How**: Direct definition.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `ellipticPointRhoPlusOne`, `vertDelta`, `arcsinDelta`
- **Used by**: `E_atRhoPlusOne_eq`, `E_atRhoPlusOne_tendsto`, `cornerFTCHyp_atRhoPlusOne`
- **Visibility**: private
- **Lines**: 768-770
- **Notes**: none

### `private theorem E_atRhoPlusOne_eq`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < min (1/3) (H - Real.sqrt 3 / 2)) → E_atRhoPlusOne H ε = ↑(Real.pi / 2 - (5π/6 + 5·arcsinDelta(ε)·π/12)) * I`
- **What**: Explicit closed form of `E_atRhoPlusOne H ε` as a purely imaginary number.
- **How**: `log_sub_eq_of_equal_norm` (norms equal via `vert_norm_at_rp1` and `arc_norm_at_rp1`), then `vert_arg_at_rp1` and `arc_arg_at_rp1` for the args.
- **Hypotheses**: valid height; ε > 0 and ε < min(1/3, H - √3/2).
- **Uses from project**: `E_atRhoPlusOne`, `vert_norm_at_rp1`, `arc_norm_at_rp1`, `log_sub_eq_of_equal_norm`, `vert_arg_at_rp1`, `arc_arg_at_rp1`, `arcsinDelta`, `fdHeightValid`
- **Used by**: `E_atRhoPlusOne_tendsto`
- **Visibility**: private
- **Lines**: 772-791
- **Notes**: none

### `private theorem E_atRhoPlusOne_tendsto`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) → Tendsto (E_atRhoPlusOne H) (𝓝[>] 0) (𝓝 (-(↑Real.pi / 3 * I)))`
- **What**: As ε → 0⁺, `E_atRhoPlusOne H ε → -π·i/3`.
- **How**: Eventual closed form via `E_atRhoPlusOne_eq`, then ε → 0 gives arcsinDelta(0) = 0, so π/2 - (5π/6 + 0) = -π/3.
- **Hypotheses**: valid height.
- **Uses from project**: `E_atRhoPlusOne`, `E_atRhoPlusOne_eq`, `arcsinDelta`, `fdHeightValid`
- **Used by**: `cornerFTCHyp_atRhoPlusOne`
- **Visibility**: private
- **Lines**: 793-820
- **Notes**: none

### `private def cornerFTCHyp_atRhoPlusOne`
- **Type**: `{H : ℝ} (hH : 1 < H) {γ : PiecewiseC1Path (fdStart H) (fdStart H)} (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) (h_ftc_hyp : ...) (h_int_left : ...) (h_int_right : ...) → CornerFTCHyp γ ellipticPointRhoPlusOne (1/5) (vertDelta H) arcsinDelta (min (1/3) (H - Real.sqrt 3 / 2)) (-(↑Real.pi / 3 * I))`
- **What**: Parameterized `CornerFTCHyp` instance at ρ+1, accepting the FTC and integrability hypotheses as inputs.
- **How**: Lifts pre-supplied `h_ftc_hyp`, `h_int_left`, `h_int_right` to the abstract path γ via `transfer_integral` and `transfer_integrability`. The `h_limit` comes from `E_atRhoPlusOne_tendsto`.
- **Hypotheses**: H > 1; γ agrees with `fdBoundaryFun H`; pre-cooked FTC and integrability data.
- **Uses from project**: `CornerFTCHyp`, `E_atRhoPlusOne`, `vertDelta`, `vertDelta_pos`, `vertDelta_lt_one_fifth`, `arcsinDelta`, `arcsinDelta_pos`, `arcsinDelta_lt_one_fifth`, `transfer_integral`, `transfer_integrability`, `fdHeightValid_of_one_lt`, `E_atRhoPlusOne_tendsto`, `ellipticPointRhoPlusOne`, `fdBoundaryFun`, `fdStart`, `PiecewiseC1Path`
- **Used by**: `cornerFTCHyp_atRhoPlusOne_unconditional`
- **Visibility**: private
- **Lines**: 822-869
- **Notes**: structure constructor

### `private def seg4Ref_rp1`
- **Type**: `(H : ℝ) (t : ℝ) → ℂ` defined as `-1 + ↑((5 * t - 3) * (H - Real.sqrt 3 / 2)) * I`
- **What**: Reference function for seg4 minus (ρ+1).
- **How**: Direct definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `seg4Ref_rp1_contDiff`, `seg4Ref_rp1_neg_slitPlane`, `seg4Ref_rp1_eq`, `seg4Ref_rp1_eq_35`, `seg4Ref_rp1_eq_45`, `seg4Ref_rp1_eventuallyEq`, `seg4_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 871-872
- **Notes**: none

### `private lemma seg4Ref_rp1_contDiff`
- **Type**: `(H : ℝ) → ContDiff ℝ ⊤ (seg4Ref_rp1 H)`
- **What**: `seg4Ref_rp1 H` is C∞.
- **How**: Standard composition.
- **Hypotheses**: none.
- **Uses from project**: `seg4Ref_rp1`
- **Used by**: `seg4_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 874-879
- **Notes**: none

### `private lemma seg4Ref_rp1_neg_slitPlane`
- **Type**: `(H : ℝ) (t : ℝ) → -(seg4Ref_rp1 H t) ∈ Complex.slitPlane`
- **What**: `-(seg4Ref_rp1 H t)` always lies in slit plane (real part is `1`).
- **How**: Reduces to `0 < 1` by `simp`.
- **Hypotheses**: none.
- **Uses from project**: `seg4Ref_rp1`
- **Used by**: `seg4_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 881-887
- **Notes**: none

### `private lemma seg4Ref_rp1_eq`
- **Type**: `(H : ℝ) {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) → fdBoundaryFun H t - ellipticPointRhoPlusOne = seg4Ref_rp1 H t`
- **What**: On seg4, boundary-minus-(ρ+1) equals `seg4Ref_rp1`.
- **How**: `simp` on ite branches + `push_cast; ring`.
- **Hypotheses**: t ∈ (3/5, 4/5].
- **Uses from project**: `fdBoundaryFun`, `ellipticPointRhoPlusOne`, `seg4Ref_rp1`
- **Used by**: `seg4Ref_rp1_eventuallyEq`, `seg4_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 889-896
- **Notes**: none

### `private lemma seg4Ref_rp1_eventuallyEq`
- **Type**: `(H : ℝ) {t : ℝ} (ht3 : 3/5 < t) (ht4 : t < 4/5) → (fun s => fdBoundaryFun H s - ellipticPointRhoPlusOne) =ᶠ[𝓝 t] seg4Ref_rp1 H`
- **What**: Eventual agreement at interior seg4 points.
- **How**: Standard `Filter.eventually_of_mem`.
- **Hypotheses**: t ∈ (3/5, 4/5) open.
- **Uses from project**: `seg4Ref_rp1`, `seg4Ref_rp1_eq`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `seg4_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 898-905
- **Notes**: none

### `private lemma seg4Ref_rp1_eq_35`
- **Type**: `(H : ℝ) → fdBoundaryFun H (3/5) - ellipticPointRhoPlusOne = seg4Ref_rp1 H (3/5)`
- **What**: Endpoint match at t = 3/5.
- **How**: Uses `fdBoundaryFun_at_three_fifths` + `push_cast; ring`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_three_fifths`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, `seg4Ref_rp1`
- **Used by**: `seg4_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 907-913
- **Notes**: none

### `private lemma seg4Ref_rp1_eq_45`
- **Type**: `(H : ℝ) → fdBoundaryFun H (4/5) - ellipticPointRhoPlusOne = seg4Ref_rp1 H (4/5)`
- **What**: Endpoint match at t = 4/5.
- **How**: Uses `fdBoundaryFun_at_four_fifths` + `push_cast; ring`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_four_fifths`, `ellipticPointRhoPlusOne`, `seg4Ref_rp1`
- **Used by**: `seg4_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 915-921
- **Notes**: none

### `private theorem seg4_ftc_neg_rp1`
- **Type**: `(H : ℝ) → IntervalIntegrable ... volume (3/5) (4/5) ∧ ∫ ... = log(-(...4/5...)) - log(-(...3/5...))`
- **What**: FTC on seg4 [3/5, 4/5] for boundary-minus-(ρ+1), using negated log (the negated value is in slit plane).
- **How**: `LogDerivFTC.ftc_log_neg_on_segment`, then ae-agreement via `integral_congr_ae` with measure-zero exclusion of the endpoint 4/5.
- **Hypotheses**: just H.
- **Uses from project**: `LogDerivFTC.ftc_log_neg_on_segment`, `seg4Ref_rp1`, `seg4Ref_rp1_contDiff`, `seg4Ref_rp1_neg_slitPlane`, `seg4Ref_rp1_eq`, `seg4Ref_rp1_eventuallyEq`, `seg4Ref_rp1_eq_35`, `seg4Ref_rp1_eq_45`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `ftc_right_neg_log_rp1`, `fdBoundary_integrable_right_of_rp1`
- **Visibility**: private
- **Lines**: 923-950
- **Notes**: none

### `private def seg5Ref_rp1`
- **Type**: `(H : ℝ) (t : ℝ) → ℂ` defined as `(5 * ↑t - 5) + (↑H - ↑(Real.sqrt 3) / 2) * I`
- **What**: Reference function for seg5 minus (ρ+1).
- **How**: Direct definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `seg5Ref_rp1_contDiff`, `seg5Ref_rp1_neg_slitPlane`, `seg5Ref_rp1_eq`, `seg5Ref_rp1_eq_45`, `seg5Ref_rp1_eq_1`, `seg5Ref_rp1_eventuallyEq`, `seg5_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 952-953
- **Notes**: none

### `private lemma seg5Ref_rp1_contDiff`
- **Type**: `(H : ℝ) → ContDiff ℝ ⊤ (seg5Ref_rp1 H)`
- **What**: `seg5Ref_rp1 H` is C∞.
- **How**: Standard composition.
- **Hypotheses**: none.
- **Uses from project**: `seg5Ref_rp1`
- **Used by**: `seg5_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 955-957
- **Notes**: none

### `private lemma seg5Ref_rp1_neg_slitPlane`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) (t : ℝ) → -(seg5Ref_rp1 H t) ∈ Complex.slitPlane`
- **What**: For valid heights, the negated `seg5Ref_rp1 H t` is in slit plane (imaginary part is `-(H - √3/2) < 0` so the negation has positive im... actually they use the negative-im branch).
- **How**: Computes `(seg5Ref_rp1 H t).im = H - √3/2 > 0`, so `(-seg5Ref_rp1 H t).im < 0` makes it nonzero (slit plane uses Im ≠ 0 or positive Re).
- **Hypotheses**: valid height.
- **Uses from project**: `seg5Ref_rp1`, `fdHeightValid`
- **Used by**: `seg5_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 959-971
- **Notes**: none

### `private lemma seg5Ref_rp1_eq`
- **Type**: `(H : ℝ) {t : ℝ} (ht : 4/5 < t) → fdBoundaryFun H t - ellipticPointRhoPlusOne = seg5Ref_rp1 H t`
- **What**: On seg5, boundary-minus-(ρ+1) equals `seg5Ref_rp1`.
- **How**: `simp` on ite branches + `ring`.
- **Hypotheses**: t > 4/5.
- **Uses from project**: `fdBoundaryFun`, `seg5Ref_rp1`, `ellipticPointRhoPlusOne`
- **Used by**: `seg5Ref_rp1_eventuallyEq`, `seg5_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 973-979
- **Notes**: none

### `private lemma seg5Ref_rp1_eventuallyEq`
- **Type**: `(H : ℝ) {t : ℝ} (ht : 4/5 < t) → (fun s => fdBoundaryFun H s - ellipticPointRhoPlusOne) =ᶠ[𝓝 t] seg5Ref_rp1 H`
- **What**: Eventual agreement near seg5 points.
- **How**: `Filter.eventually_of_mem (Ioi_mem_nhds ht)`.
- **Hypotheses**: t > 4/5.
- **Uses from project**: `seg5Ref_rp1`, `seg5Ref_rp1_eq`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `seg5_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 981-983
- **Notes**: none

### `private lemma seg5Ref_rp1_eq_45`
- **Type**: `(H : ℝ) → fdBoundaryFun H (4/5) - ellipticPointRhoPlusOne = seg5Ref_rp1 H (4/5)`
- **What**: Endpoint match at t = 4/5.
- **How**: Uses `fdBoundaryFun_at_four_fifths` + `push_cast; ring`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_four_fifths`, `ellipticPointRhoPlusOne`, `seg5Ref_rp1`
- **Used by**: `seg5_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 985-991
- **Notes**: none

### `private lemma seg5Ref_rp1_eq_1`
- **Type**: `(H : ℝ) → fdBoundaryFun H 1 - ellipticPointRhoPlusOne = seg5Ref_rp1 H 1`
- **What**: Endpoint match at t = 1.
- **How**: Uses `fdBoundaryFun_at_one` + `push_cast; ring`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_one`, `fdStart`, `ellipticPointRhoPlusOne`, `seg5Ref_rp1`
- **Used by**: `seg5_ftc_neg_rp1`
- **Visibility**: private
- **Lines**: 993-999
- **Notes**: none

### `private theorem seg5_ftc_neg_rp1`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) → IntervalIntegrable ... volume (4/5) 1 ∧ ∫ ... = log(-(...1...)) - log(-(...4/5...))`
- **What**: FTC on seg5 [4/5, 1] for boundary-minus-(ρ+1) using the negated-log form.
- **How**: `LogDerivFTC.ftc_log_neg_on_segment` + ae-agreement via `integral_congr_ae` with endpoint 1 excluded.
- **Hypotheses**: valid height.
- **Uses from project**: `LogDerivFTC.ftc_log_neg_on_segment`, `seg5Ref_rp1`, `seg5Ref_rp1_contDiff`, `seg5Ref_rp1_neg_slitPlane`, `seg5Ref_rp1_eq`, `seg5Ref_rp1_eventuallyEq`, `seg5Ref_rp1_eq_45`, `seg5Ref_rp1_eq_1`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `ftc_right_neg_log_rp1`, `fdBoundary_integrable_right_of_rp1`
- **Visibility**: private
- **Lines**: 1001-1028
- **Notes**: none

### `private lemma log_neg_eq_sub_pi_I_rp1`
- **Type**: `{z : ℂ} (_hz_ne : z ≠ 0) (hz_im : 0 < z.im) → Complex.log (-z) = Complex.log z - ↑Real.pi * I`
- **What**: Branch-correction identity: for `z` with positive imaginary part, `log(-z) = log(z) - π·i`.
- **How**: Direct computation using `norm_neg` and `Complex.arg_neg_eq_arg_sub_pi_of_im_pos`, then `push_cast; ring`.
- **Hypotheses**: z ≠ 0; 0 < z.im.
- **Uses from project**: []
- **Used by**: `branch_correction_arc_rp1`, `branch_correction_start_rp1`
- **Visibility**: private
- **Lines**: 1030-1037
- **Notes**: none

### `private lemma fdBoundary_sub_rp1_at_start_im_pos`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) → 0 < (fdBoundaryFun H 0 - ellipticPointRhoPlusOne).im`
- **What**: At the start parameter t = 0, the imaginary part of boundary-minus-(ρ+1) is positive.
- **How**: Uses `fdBoundaryFun_at_zero` and the fact that H > √3/2 (from `fdHeightValid`).
- **Hypotheses**: valid height.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_zero`, `fdStart`, `ellipticPointRhoPlusOne`, `fdHeightValid`
- **Used by**: `branch_correction_start_rp1`
- **Visibility**: private
- **Lines**: 1039-1046
- **Notes**: none

### `private lemma arcRef_rp1_im_pos`
- **Type**: `{δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2/5) → 0 < (arcRef_rp1 (1/5 + δ)).im`
- **What**: On the arc range (1/5, 3/5), the imaginary part of `arcRef_rp1` is positive.
- **How**: Uses `exp_mul_I` to reduce to `sin(fdArcAngle ...) > √3/2`, then case-splits on whether `fdArcAngle ≤ π/2` and uses `Real.sin_lt_sin_of_lt_of_le_pi_div_two` against `sin(π/3) = √3/2`.
- **Hypotheses**: 0 < δ < 2/5.
- **Uses from project**: `arcRef_rp1`, `fdArcAngle`, `ellipticPointRhoPlusOne`
- **Used by**: `branch_correction_arc_rp1`
- **Visibility**: private
- **Lines**: 1048-1069
- **Notes**: none

### `private theorem ftc_right_neg_log_rp1`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {δR : ℝ} (hδR : 0 < δR) (hδR' : δR < 2/5) → ∫ t in (1/5+δR)..1, ... = log(-(...1...)) - log(-(...1/5+δR...))`
- **What**: Combined arc + seg4 + seg5 FTC pieces on the right of ρ+1, all using the negated-log form.
- **How**: Combines `arc_ftc_neg_rp1`, `seg4_ftc_neg_rp1`, `seg5_ftc_neg_rp1` via `intervalIntegral.integral_add_adjacent_intervals` (twice).
- **Hypotheses**: valid height; 0 < δR < 2/5.
- **Uses from project**: `arc_ftc_neg_rp1`, `seg4_ftc_neg_rp1`, `seg5_ftc_neg_rp1`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `fdBoundary_ftc_telescope_rp1`
- **Visibility**: private
- **Lines**: 1071-1092
- **Notes**: none

### `private lemma branch_correction_arc_rp1`
- **Type**: `(H : ℝ) {δR : ℝ} (hδR : 0 < δR) (hδR' : δR < 2/5) → Complex.log (-(fdBoundaryFun H (1/5 + δR) - ellipticPointRhoPlusOne)) = Complex.log (fdBoundaryFun H (1/5 + δR) - ellipticPointRhoPlusOne) - ↑Real.pi * I`
- **What**: At the arc-side ε-excised point, the negated-log equals the unnegated log minus π·i.
- **How**: Uses `arcRef_rp1_eq` to switch to `arcRef_rp1`, then `arcRef_rp1_im_pos` to get positive im, then `log_neg_eq_sub_pi_I_rp1`.
- **Hypotheses**: 0 < δR < 2/5.
- **Uses from project**: `arcRef_rp1`, `arcRef_rp1_eq`, `arcRef_rp1_im_pos`, `log_neg_eq_sub_pi_I_rp1`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `fdBoundary_ftc_telescope_rp1`
- **Visibility**: private
- **Lines**: 1094-1105
- **Notes**: none

### `private lemma branch_correction_start_rp1`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) → Complex.log (-(fdBoundaryFun H 0 - ellipticPointRhoPlusOne)) = Complex.log (fdBoundaryFun H 0 - ellipticPointRhoPlusOne) - ↑Real.pi * I`
- **What**: At t = 0 (start), the negated-log equals the unnegated log minus π·i.
- **How**: `fdBoundary_sub_rp1_at_start_im_pos` + `log_neg_eq_sub_pi_I_rp1`.
- **Hypotheses**: valid height.
- **Uses from project**: `fdBoundary_sub_rp1_at_start_im_pos`, `log_neg_eq_sub_pi_I_rp1`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `fdBoundary_ftc_telescope_rp1`
- **Visibility**: private
- **Lines**: 1107-1115
- **Notes**: none

### `private theorem fdBoundary_ftc_telescope_rp1`
- **Type**: `(H : ℝ) (hH : 1 < H) {δL δR : ℝ} (hδL : 0 < δL) (hδL' : δL < 1/5) (hδR : 0 < δR) (hδR' : δR < 2/5) → (∫ t in 0..(1/5-δL), ...) + (∫ t in (1/5+δR)..1, ...) = log(fdBoundaryFun H (1/5 - δL) - (ρ+1)) - log(fdBoundaryFun H (1/5 + δR) - (ρ+1))`
- **What**: Telescoping at ρ+1: sums seg1 FTC and the right-of-(ρ+1) FTC (arc + seg4 + seg5), with branch corrections to recover the unnegated log form (since the right side crosses through the negative-real-part region).
- **How**: Combines `seg1_ftc_rp1` with `ftc_right_neg_log_rp1`, then applies `branch_correction_arc_rp1`, `branch_correction_start_rp1`, and `fdBoundaryFun_closed` to cancel the boundary value at the closed-curve endpoint.
- **Hypotheses**: H > 1; 0 < δL < 1/5; 0 < δR < 2/5.
- **Uses from project**: `seg1_ftc_rp1`, `ftc_right_neg_log_rp1`, `branch_correction_arc_rp1`, `branch_correction_start_rp1`, `fdBoundaryFun_closed`, `fdHeightValid_of_one_lt`, `integrand_form_eq'`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `cornerFTCHyp_atRhoPlusOne_unconditional`
- **Visibility**: private
- **Lines**: 1117-1146
- **Notes**: proof >30 lines

### `private theorem fdBoundary_integrable_left_of_rp1`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) → IntervalIntegrable (fun t => (fdBoundaryFun H t - (ρ+1))⁻¹ * deriv (fdBoundaryFun H) t) volume 0 (1/5 - δ)`
- **What**: Left-of-(ρ+1) integrability of the log-derivative on [0, 1/5 - δ].
- **How**: Converts via `integrand_form_eq'`, then `(seg1_ftc_rp1 H hH hδ hδ').1`.
- **Hypotheses**: valid height; 0 < δ < 1/5.
- **Uses from project**: `integrand_form_eq'`, `seg1_ftc_rp1`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `cornerFTCHyp_atRhoPlusOne_unconditional`
- **Visibility**: private
- **Lines**: 1148-1154
- **Notes**: none

### `private theorem fdBoundary_integrable_right_of_rp1`
- **Type**: `(H : ℝ) (hH : fdHeightValid H) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2/5) → IntervalIntegrable (fun t => (fdBoundaryFun H t - (ρ+1))⁻¹ * deriv (fdBoundaryFun H) t) volume (1/5 + δ) 1`
- **What**: Right-of-(ρ+1) integrability of the log-derivative on [1/5 + δ, 1].
- **How**: Converts via `integrand_form_eq'`, then chains `arc_ftc_neg_rp1`, `seg4_ftc_neg_rp1`, `seg5_ftc_neg_rp1` integrability via `.trans`.
- **Hypotheses**: valid height; 0 < δ < 2/5.
- **Uses from project**: `integrand_form_eq'`, `arc_ftc_neg_rp1`, `seg4_ftc_neg_rp1`, `seg5_ftc_neg_rp1`, `fdHeightValid`, `fdBoundaryFun`, `ellipticPointRhoPlusOne`
- **Used by**: `cornerFTCHyp_atRhoPlusOne_unconditional`
- **Visibility**: private
- **Lines**: 1156-1163
- **Notes**: none

### `def cornerFTCHyp_atRhoPlusOne_unconditional`
- **Type**: `{H : ℝ} (hH : 1 < H) {γ : PiecewiseC1Path (fdStart H) (fdStart H)} (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) → CornerFTCHyp γ ellipticPointRhoPlusOne (1/5) (vertDelta H) arcsinDelta (min (1/3) (H - Real.sqrt 3 / 2)) (-(↑Real.pi / 3 * I))`
- **What**: Complete (unconditional) `CornerFTCHyp` at ρ+1: instantiates `cornerFTCHyp_atRhoPlusOne` with the proven FTC and integrability data.
- **How**: Specializes `cornerFTCHyp_atRhoPlusOne` by providing `fdBoundary_ftc_telescope_rp1`, `fdBoundary_integrable_left_of_rp1`, `fdBoundary_integrable_right_of_rp1` as the three input lemmas, derived from `arcsinDelta`/`vertDelta` bounds.
- **Hypotheses**: H > 1; γ piecewise-C¹ path agreeing with `fdBoundaryFun H` on [0,1].
- **Uses from project**: `cornerFTCHyp_atRhoPlusOne`, `fdBoundary_ftc_telescope_rp1`, `fdBoundary_integrable_left_of_rp1`, `fdBoundary_integrable_right_of_rp1`, `arcsinDelta_pos`, `arcsinDelta_lt_one_fifth`, `vertDelta_pos`, `vertDelta_lt_one_fifth`, `fdHeightValid_of_one_lt`, `CornerFTCHyp`, `ellipticPointRhoPlusOne`, `vertDelta`, `arcsinDelta`, `fdBoundaryFun`, `fdStart`, `PiecewiseC1Path`
- **Used by**: unused in file (consumed downstream)
- **Visibility**: public
- **Lines**: 1166-1192
- **Notes**: final headline at ρ+1

## File Summary

- **Total declarations**: 73 (1 trig-identity helper used by file's polar decompositions, ~30 segment reference functions/lemmas, ~10 FTC pieces, ~6 norm/arg lemmas, ~4 branch corrections, 4 telescope/integrability theorems, 2 `CornerFTCHyp` constructors at ρ, 2 at ρ+1).
- **Key API (used by 3+ in file)**: `integrand_form_eq'` (6 uses); `fdHeightValid_of_one_lt` (4); `arcsinDelta_pos`/`arcsinDelta_lt_one_fifth`/`vertDelta_pos`/`vertDelta_lt_one_fifth` (each 3+); `LogDerivFTC.ftc_log_pieceFM` / `LogDerivFTC.ftc_log_neg_on_segment` (4+ each); `transfer_integral`/`transfer_integrability` (2 each); `arcRef_rp1` and `seg4Ref_rp1`/`seg5Ref_rp1` (each used by 6+ companion lemmas).
- **Unused in file**: `cornerFTCHyp_atRho`, `cornerFTCHyp_atRhoPlusOne_unconditional` (these are the public headline API).
- **Sorries**: 0
- **set_option**: none
- **Proofs >30 lines**: `fdBoundary_ftc_telescope_rho` (≈36 lines), `fdBoundary_ftc_telescope_rp1` (≈30 lines). All other proofs are ≤30 lines.
- **One-paragraph purpose**: Builds two complete `CornerFTCHyp` instances — one for the elliptic point ρ at corner time t₀ = 3/5 (arc on left, vertical seg4 on right, 60-degree corner) and one for ρ+1 at corner time t₀ = 1/5 (vertical seg1 on left, arc on right, 60-degree corner). Both reach the same limit `-π·i/3` (the 60-degree corner contribution). The construction is segment-by-segment: for each of seg1, arc, seg4, seg5, a reference function `(ref_seg*_rho/_rp1)` matching `fdBoundaryFun H t - (ρ or ρ+1)` is defined, shown to be C∞, shown to lie in `Complex.slitPlane` (or its negation does), and used with `LogDerivFTC.ftc_log_pieceFM` (or `ftc_log_neg_on_segment` for ρ+1's right side, which crosses the negative-real-part region) to give a piecewise FTC. The pieces are then telescoped via `intervalIntegral.integral_add_adjacent_intervals`, with branch corrections (`log_neg_eq_sub_pi_I_rp1`) on the ρ+1 side to convert negated-form back to standard form, using `fdBoundaryFun_closed H` to cancel the boundary value at the closed-curve endpoint. Norm and argument analyses at the ε-excised points use `arcsinDelta` (arc-side excision) and `vertDelta` (vertical-side excision), polar decomposition via custom `arcRef_sub_*_decomp` identities, and `Complex.arg_mul_cos_add_sin_mul_I` to extract the angles. The final `E_atRho` and `E_atRhoPlusOne` functions assemble the two log values into a single ε-parameterized quantity, shown to converge to `-π·i/3` as ε → 0⁺.
