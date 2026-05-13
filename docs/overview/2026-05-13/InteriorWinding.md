# InteriorWinding.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/InteriorWinding.lean`
Imports: `FDBoundary`, `CurveUtilities`

### `def FDStrictInterior`
- **Type**: `(z : ℂ) (H : ℝ) → Prop`
- **What**: Predicate for `z` being a strict interior point of the FD at height `H`: `‖z‖ > 1`, `|z.re| < 1/2`, `0 < z.im`, `z.im < H`.
- **How**: Conjunction `1 < ‖z‖ ∧ |z.re| < 1/2 ∧ 0 < z.im ∧ z.im < H`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `FDStrictInterior.norm_gt`, `FDStrictInterior.re_abs_lt`, `FDStrictInterior.im_pos`, `FDStrictInterior.im_lt`, `fdBoundaryFun_ne_of_strictInterior`, `fdBoundaryFun_minDist_of_strictInterior`
- **Visibility**: public
- **Lines**: 65-66
- **Notes**: none

### `theorem FDStrictInterior.norm_gt`
- **Type**: `{z : ℂ} {H : ℝ} (h : FDStrictInterior z H) → 1 < ‖z‖`
- **What**: First field of `FDStrictInterior`: norm exceeds 1.
- **How**: Projection `h.1`.
- **Hypotheses**: `FDStrictInterior z H`.
- **Uses from project**: `FDStrictInterior`
- **Used by**: `fdBoundaryFun_ne_of_strictInterior`, `fdBoundaryFun_minDist_of_strictInterior`
- **Visibility**: public
- **Lines**: 68-69
- **Notes**: none

### `theorem FDStrictInterior.re_abs_lt`
- **Type**: `{z : ℂ} {H : ℝ} (h : FDStrictInterior z H) → |z.re| < 1/2`
- **What**: Second field: `|z.re| < 1/2`.
- **How**: Projection `h.2.1`.
- **Hypotheses**: `FDStrictInterior z H`.
- **Uses from project**: `FDStrictInterior`
- **Used by**: `fdBoundaryFun_ne_of_strictInterior`, `fdBoundaryFun_minDist_of_strictInterior`
- **Visibility**: public
- **Lines**: 71-72
- **Notes**: none

### `theorem FDStrictInterior.im_pos`
- **Type**: `{z : ℂ} {H : ℝ} (h : FDStrictInterior z H) → 0 < z.im`
- **What**: Third field: `0 < z.im`.
- **How**: Projection `h.2.2.1`.
- **Hypotheses**: `FDStrictInterior z H`.
- **Uses from project**: `FDStrictInterior`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 74-75
- **Notes**: none

### `theorem FDStrictInterior.im_lt`
- **Type**: `{z : ℂ} {H : ℝ} (h : FDStrictInterior z H) → z.im < H`
- **What**: Fourth field: `z.im < H`.
- **How**: Projection `h.2.2.2`.
- **Hypotheses**: `FDStrictInterior z H`.
- **Uses from project**: `FDStrictInterior`
- **Used by**: `fdBoundaryFun_ne_of_strictInterior`, `fdBoundaryFun_minDist_of_strictInterior`
- **Visibility**: public
- **Lines**: 77-78
- **Notes**: none

### `theorem fdBoundaryFun_avoids_seg1`
- **Type**: `{z : ℂ} (hz_re : |z.re| < 1/2) {H : ℝ} {t : ℝ} (ht : t ≤ 1/5) → fdBoundaryFun H t ≠ z`
- **What**: Segment 1 (right vertical) avoids any `z` with `|z.re| < 1/2`.
- **How**: Assume `=`, rewrite using `fdBoundaryFun_seg1_re H t ht` to get `z.re = 1/2`, contradicting `|z.re| < 1/2` via `norm_num`.
- **Hypotheses**: `|z.re| < 1/2`; `t ≤ 1/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg1_re`
- **Used by**: `fdBoundaryFun_avoids_interior`
- **Visibility**: public
- **Lines**: 83-90
- **Notes**: none

### `theorem fdBoundaryFun_avoids_arc`
- **Type**: `{z : ℂ} (hz_norm : 1 < ‖z‖) {H : ℝ} {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) → fdBoundaryFun H t ≠ z`
- **What**: Arc segments (segs 2-3) avoid any `z` with `‖z‖ > 1`.
- **How**: Suppose `=`, use `fdBoundaryFun_arc_norm` to get `‖fdBoundaryFun H t‖ = 1`, then `linarith`.
- **Hypotheses**: `‖z‖ > 1`; `1/5 < t ≤ 3/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_arc_norm`
- **Used by**: `fdBoundaryFun_avoids_interior`
- **Visibility**: public
- **Lines**: 95-101
- **Notes**: none

### `theorem fdBoundaryFun_avoids_seg4`
- **Type**: `{z : ℂ} (hz_re : |z.re| < 1/2) {H : ℝ} {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) → fdBoundaryFun H t ≠ z`
- **What**: Segment 4 (left vertical) avoids any `z` with `|z.re| < 1/2`.
- **How**: Identical pattern to `_avoids_seg1` using `fdBoundaryFun_seg4_re`; `norm_num`.
- **Hypotheses**: `|z.re| < 1/2`; `3/5 < t ≤ 4/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg4_re`
- **Used by**: `fdBoundaryFun_avoids_interior`
- **Visibility**: public
- **Lines**: 106-113
- **Notes**: none

### `theorem fdBoundaryFun_avoids_seg5`
- **Type**: `{z : ℂ} (hz_im : z.im < H) {t : ℝ} (ht : 4/5 < t) → fdBoundaryFun H t ≠ z`
- **What**: Segment 5 (horizontal at `im = H`) avoids any `z` with `z.im < H`.
- **How**: From `fdBoundaryFun_seg5_im`, `linarith`.
- **Hypotheses**: `z.im < H`; `4/5 < t`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg5_im`
- **Used by**: `fdBoundaryFun_avoids_interior`
- **Visibility**: public
- **Lines**: 118-124
- **Notes**: none

### `theorem fdBoundaryFun_avoids_interior`
- **Type**: `{z : ℂ} {H : ℝ} (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : z.im < H) → ∀ t ∈ Icc 0 1, fdBoundaryFun H t ≠ z`
- **What**: The full FD boundary avoids every strict interior point.
- **How**: Case-split on `t ≤ 1/5`, `t ≤ 3/5`, `t ≤ 4/5` using `by_cases`/`push Not`; dispatch to `fdBoundaryFun_avoids_seg1/_arc/_seg4/_seg5` respectively.
- **Hypotheses**: Strict interior conditions on `z`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_avoids_seg1`, `fdBoundaryFun_avoids_arc`, `fdBoundaryFun_avoids_seg4`, `fdBoundaryFun_avoids_seg5`
- **Used by**: `fdBoundaryFun_minDist_interior_pos`, `fdBoundaryFun_ne_of_strictInterior`
- **Visibility**: public
- **Lines**: 130-143
- **Notes**: none

### `theorem fdBoundaryFun_minDist_interior_pos`
- **Type**: `{z : ℂ} {H : ℝ} (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : z.im < H) → ∃ δ > 0, ∀ t ∈ Icc 0 1, δ ≤ ‖fdBoundaryFun H t - z‖`
- **What**: For strict-interior `z`, the minimum distance to the FD boundary on `[0,1]` is strictly positive.
- **How**: Image `fdBoundaryFun H '' Icc 0 1` is compact (`isCompact_Icc.image`), hence closed; nonempty via `mem_image_of_mem` at `0`; `z` not in image by `fdBoundaryFun_avoids_interior`; thus `Metric.infDist z ... > 0` via `IsClosed.notMem_iff_infDist_pos`; finally `Metric.infDist_le_dist_of_mem` together with `dist_comm`.
- **Hypotheses**: Strict interior bounds on `z`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_continuous`, `fdBoundaryFun_avoids_interior`
- **Used by**: `piecewiseC1Path_avoids_interior`, `fdBoundaryFun_minDist_of_strictInterior`
- **Visibility**: public
- **Lines**: 149-169
- **Notes**: none

### `theorem piecewiseC1Path_avoids_interior`
- **Type**: `{H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) {z : ℂ} (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : z.im < H) → ∃ δ > 0, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - z‖`
- **What**: A path agreeing with `fdBoundaryFun` on `[0,1]` inherits the positive minimum-distance property.
- **How**: Take `δ` from `fdBoundaryFun_minDist_interior_pos`; rewrite `‖γ t - z‖` to `‖γ.extend t - z‖`, use `hγ t ht` to substitute, conclude with `hδ_bound t ht`.
- **Hypotheses**: Path agreement; strict interior on `z`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `fdBoundaryFun_minDist_interior_pos`
- **Used by**: `hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral`
- **Visibility**: public
- **Lines**: 175-184
- **Notes**: none

### `theorem hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral`
- **Type**: `{H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : agreement) {z : ℂ} (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (_hz_im_pos : 0 < z.im) (hz_im_lt : z.im < H) (h_integral : γ.contourIntegral (fun w => (w - z)⁻¹) = -(2πI)) → HasGeneralizedWindingNumber γ z (-1)`
- **What**: Reduces "interior winding number = -1" to a contour integral identity.
- **How**: From `piecewiseC1Path_avoids_interior` get `hδ`. Apply `hasGeneralizedWindingNumber_of_avoids` to get `HasGeneralizedWindingNumber γ z ((2πI)⁻¹ * contourIntegral ...)`. `convert h_gWN using 1`; rewrite with `h_integral`; verify `2πI ≠ 0` (via `mul_eq_zero`, `Complex.ofReal_eq_zero`, `Real.pi_ne_zero`, `I_ne_zero`); close with `field_simp`.
- **Hypotheses**: Path agreement; strict interior; contour integral = `-2πi`.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `HasGeneralizedWindingNumber`, `hasGeneralizedWindingNumber_of_avoids`, `piecewiseC1Path_avoids_interior`, `PiecewiseC1Path.contourIntegral`
- **Used by**: `hasGeneralizedWindingNumber_fdBoundary_interior_of_contourIntegral`
- **Visibility**: public
- **Lines**: 194-213
- **Notes**: none

### `theorem hasGeneralizedWindingNumber_fdBoundary_interior_of_contourIntegral`
- **Type**: `{H : ℝ} (γ : ...) (hγ : agreement) (h_int : ∀ z, strict interior → contour integral = -(2πI)) → ∀ z, strict interior → HasGeneralizedWindingNumber γ z (-1)`
- **What**: All-quantified version: produces the interior winding hypothesis for every strict interior point.
- **How**: Introduce `z` and four strict-interior facts; apply `hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral` with `h_int z ...`.
- **Hypotheses**: Path agreement; universal integral identity.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `HasGeneralizedWindingNumber`, `hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral`
- **Used by**: `FDWindingData.mk_of_interior_contourIntegral`
- **Visibility**: public
- **Lines**: 220-229
- **Notes**: none

### `def FDWindingData.mk_of_interior_contourIntegral`
- **Type**: `{H : ℝ} (boundary : PiecewiseC1Path (fdStart H) (fdStart H)) (hbdy : agreement) (h_int : ∀ strict interior z, contour integral = -(2πI)) (D_i : SingleCrossingData boundary I) (hL_i : D_i.L = -(πI)) (D_rho : SingleCrossingData boundary ellipticPointRho) (hL_rho : D_rho.L = -(π/3 · I)) (D_rho1 : SingleCrossingData boundary ellipticPointRhoPlusOne) (hL_rho1 : D_rho1.L = -(π/3 · I)) → FDWindingData H`
- **What**: Constructor for `FDWindingData H` using the interior contour integral hypothesis plus three elliptic single-crossing data.
- **How**: Delegate to `FDWindingData.mk_of_crossing`, supplying the per-point winding hypothesis via `hasGeneralizedWindingNumber_fdBoundary_interior_of_contourIntegral`.
- **Hypotheses**: As in type; D_i/D_rho/D_rho1 with the prescribed CPV values.
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `SingleCrossingData`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, `FDWindingData`, `FDWindingData.mk_of_crossing`, `hasGeneralizedWindingNumber_fdBoundary_interior_of_contourIntegral`
- **Used by**: unused in file (called from `InteriorWindingProof`)
- **Visibility**: public
- **Lines**: 242-257
- **Notes**: none

### `theorem fdBoundaryFun_ne_of_strictInterior`
- **Type**: `{z : ℂ} {H : ℝ} (hz : FDStrictInterior z H) → ∀ t ∈ Icc 0 1, fdBoundaryFun H t ≠ z`
- **What**: Convenience packaging of `fdBoundaryFun_avoids_interior` from a `FDStrictInterior` predicate.
- **How**: Forward each projection (`hz.norm_gt`, `hz.re_abs_lt`, `hz.im_lt`) into `fdBoundaryFun_avoids_interior`.
- **Hypotheses**: `FDStrictInterior z H`.
- **Uses from project**: `FDStrictInterior`, `FDStrictInterior.norm_gt`, `FDStrictInterior.re_abs_lt`, `FDStrictInterior.im_lt`, `fdBoundaryFun`, `fdBoundaryFun_avoids_interior`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 263-266
- **Notes**: none

### `theorem fdBoundaryFun_minDist_of_strictInterior`
- **Type**: `{z : ℂ} {H : ℝ} (hz : FDStrictInterior z H) → ∃ δ > 0, ∀ t ∈ Icc 0 1, δ ≤ ‖fdBoundaryFun H t - z‖`
- **What**: Convenience packaging of `fdBoundaryFun_minDist_interior_pos` from a `FDStrictInterior` predicate.
- **How**: Forward projections into `fdBoundaryFun_minDist_interior_pos`.
- **Hypotheses**: `FDStrictInterior z H`.
- **Uses from project**: `FDStrictInterior`, `FDStrictInterior.norm_gt`, `FDStrictInterior.re_abs_lt`, `FDStrictInterior.im_lt`, `fdBoundaryFun`, `fdBoundaryFun_minDist_interior_pos`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 269-272
- **Notes**: none

### `theorem fdBoundaryFun_seg1_re_dist`
- **Type**: `{z : ℂ} (_hz_re : |z.re| < 1/2) {H : ℝ} {t : ℝ} (ht : t ≤ 1/5) → 1/2 - |z.re| ≤ ‖fdBoundaryFun H t - z‖`
- **What**: Lower bound `1/2 - |z.re|` on the distance from `z` to segment 1.
- **How**: `fdBoundaryFun_seg1_re` gives `(γ - z).re = 1/2 - z.re`; use `abs_sub_abs_le_abs_sub` to get `1/2 - |z.re| ≤ |1/2 - z.re|`; bound `|.re|` by norm via `Complex.abs_re_le_norm`.
- **Hypotheses**: `|z.re| < 1/2`; `t ≤ 1/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg1_re`
- **Used by**: `fdBoundaryFun_minDist_explicit`
- **Visibility**: public
- **Lines**: 278-289
- **Notes**: none

### `theorem fdBoundaryFun_arc_dist`
- **Type**: `{z : ℂ} (_hz_norm : 1 < ‖z‖) {H : ℝ} {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) → ‖z‖ - 1 ≤ ‖fdBoundaryFun H t - z‖`
- **What**: Lower bound `‖z‖ - 1` on the distance from `z` to the arc segments.
- **How**: `fdBoundaryFun_arc_norm` gives `‖γ‖ = 1`; use reverse triangle inequality `norm_sub_norm_le`; reorient with `norm_sub_rev`.
- **Hypotheses**: `‖z‖ > 1`; `1/5 < t ≤ 3/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_arc_norm`
- **Used by**: `fdBoundaryFun_minDist_explicit`
- **Visibility**: public
- **Lines**: 293-299
- **Notes**: none

### `theorem fdBoundaryFun_seg4_re_dist`
- **Type**: `{z : ℂ} (_hz_re : |z.re| < 1/2) {H : ℝ} {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) → 1/2 - |z.re| ≤ ‖fdBoundaryFun H t - z‖`
- **What**: Lower bound `1/2 - |z.re|` on distance to segment 4.
- **How**: Analogous to seg1: `fdBoundaryFun_seg4_re` gives `(γ - z).re = -1/2 - z.re`; `abs_sub_abs_le_abs_sub (-1/2) z.re` produces `1/2 - |z.re| ≤ |-1/2 - z.re|`; bound by norm.
- **Hypotheses**: `|z.re| < 1/2`; `3/5 < t ≤ 4/5`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg4_re`
- **Used by**: `fdBoundaryFun_minDist_explicit`
- **Visibility**: public
- **Lines**: 303-314
- **Notes**: none

### `theorem fdBoundaryFun_seg5_im_dist`
- **Type**: `{z : ℂ} (hz_im : z.im < H) {t : ℝ} (ht : 4/5 < t) → H - z.im ≤ ‖fdBoundaryFun H t - z‖`
- **What**: Lower bound `H - z.im` on distance to segment 5.
- **How**: `fdBoundaryFun_seg5_im` and `abs_of_pos`; bound by `Complex.abs_im_le_norm`.
- **Hypotheses**: `z.im < H`; `4/5 < t`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg5_im`
- **Used by**: `fdBoundaryFun_minDist_explicit`
- **Visibility**: public
- **Lines**: 318-324
- **Notes**: none

### `theorem fdBoundaryFun_minDist_explicit`
- **Type**: `{z : ℂ} {H : ℝ} (hz_norm) (hz_re) (hz_im) → ∀ t ∈ Icc 0 1, min (min (1/2 - |z.re|) (‖z‖ - 1)) (H - z.im) ≤ ‖fdBoundaryFun H t - z‖`
- **What**: Provides an explicit `min(1/2 - |z.re|, ‖z‖ - 1, H - z.im)` lower bound across all segments.
- **How**: Case-split on `t ≤ 1/5`, `t ≤ 3/5`, `t ≤ 4/5` with `by_cases`/`push Not`; in each case bound `min` by appropriate corner and conclude via `fdBoundaryFun_seg1_re_dist`/`_arc_dist`/`_seg4_re_dist`/`_seg5_im_dist`.
- **Hypotheses**: Strict interior conditions on `z`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg1_re_dist`, `fdBoundaryFun_arc_dist`, `fdBoundaryFun_seg4_re_dist`, `fdBoundaryFun_seg5_im_dist`
- **Used by**: `fdBoundaryFun_avoids_with_explicit_bound`
- **Visibility**: public
- **Lines**: 330-353
- **Notes**: none

### `theorem fdBoundaryFun_minDist_explicit_pos`
- **Type**: `{z : ℂ} {H : ℝ} (hz_norm) (hz_re) (hz_im) → 0 < min (min (1/2 - |z.re|) (‖z‖ - 1)) (H - z.im)`
- **What**: The explicit `min` lower bound is strictly positive under strict interior hypotheses.
- **How**: `lt_min (lt_min (linarith) (linarith)) (linarith)`.
- **Hypotheses**: Strict interior conditions on `z`.
- **Uses from project**: []
- **Used by**: `fdBoundaryFun_avoids_with_explicit_bound`
- **Visibility**: public
- **Lines**: 356-359
- **Notes**: none

### `theorem fdBoundaryFun_avoids_with_explicit_bound`
- **Type**: `{z : ℂ} {H : ℝ} (hz_norm) (hz_re) (hz_im) (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : agreement) → ∃ δ > 0, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - z‖`
- **What**: Packaged existential lower bound directly usable for `hasGeneralizedWindingNumber_of_avoids`, with `δ` being the explicit `min` from above.
- **How**: Use `fdBoundaryFun_minDist_explicit_pos` for positivity; bound `‖γ t - z‖` by `‖fdBoundaryFun H t - z‖` via the path agreement, then `fdBoundaryFun_minDist_explicit`.
- **Hypotheses**: Strict interior bounds; path agreement.
- **Uses from project**: `fdBoundaryFun`, `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun_minDist_explicit_pos`, `fdBoundaryFun_minDist_explicit`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 363-372
- **Notes**: none

## File Summary
- Total declarations: 21 (1 `def` predicate, 1 `def` constructor `FDWindingData.mk_of_interior_contourIntegral`, 19 public theorems including 4 projection lemmas for `FDStrictInterior`).
- Theme: Strict interior of the SL₂(ℤ) fundamental domain (predicate `FDStrictInterior`), proof that the 5-segment FD boundary avoids every strict interior point, positivity of the minimum distance (both implicit via compactness and explicit `min` formula), reduction of "interior generalized winding = -1" to a single contour integral identity, and a clean `FDWindingData` constructor.
- Key dependencies: `FDBoundary` (`fdBoundaryFun`, `fdBoundaryFun_continuous`, segment `re`/`im` and arc `norm` characterizations); `CurveUtilities` (`PiecewiseC1Path`, `fdStart`, `HasGeneralizedWindingNumber`, `hasGeneralizedWindingNumber_of_avoids`, `SingleCrossingData`, `FDWindingData[.mk_of_crossing]`, elliptic points).
- No `sorry`, no `axiom`, no `set_option` directives.
- No declaration exceeds 30 lines materially (`fdBoundaryFun_minDist_explicit` at 24 lines is the longest).
