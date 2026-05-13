# SmoothBoundaryWindingProof.lean

**Path**: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/SmoothBoundaryWindingProof.lean
**Lines**: 219
**Imports**: `CoreIdentityProof`, `BoundaryWinding`
**Namespace**: none (top-level under `noncomputable section`)

---

## lemma `ellipticPointRho_re`
- **Type**: `(ellipticPointRho : ℂ).re = -1/2`
- **What**: Real coordinate of the elliptic point ρ.
- **How**: `simp [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]`.
- **Hypotheses**: none.
- **Uses-from-project**: `ellipticPointRho`, `ellipticPointRho'` (from `BoundaryWinding`).
- **Used by**: `smooth_boundary_classification`.
- **Visibility**: `private`.
- **Lines**: 56-57.
- **Notes**: Coordinate extraction lemma for ρ.

## lemma `ellipticPointRho_im`
- **Type**: `(ellipticPointRho : ℂ).im = Real.sqrt 3 / 2`
- **What**: Imaginary coordinate of the elliptic point ρ.
- **How**: `simp [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]`.
- **Hypotheses**: none.
- **Uses-from-project**: `ellipticPointRho`, `ellipticPointRho'`.
- **Used by**: `smooth_boundary_classification`.
- **Visibility**: `private`.
- **Lines**: 59-60.
- **Notes**: Coordinate extraction lemma for ρ.

## lemma `ellipticPointRhoPlusOne_re`
- **Type**: `(ellipticPointRhoPlusOne : ℂ).re = 1/2`
- **What**: Real coordinate of the elliptic point ρ+1.
- **How**: `simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]`.
- **Hypotheses**: none.
- **Uses-from-project**: `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`.
- **Used by**: `smooth_boundary_classification`.
- **Visibility**: `private`.
- **Lines**: 62-63.
- **Notes**: Coordinate extraction lemma for ρ+1.

## lemma `ellipticPointRhoPlusOne_im`
- **Type**: `(ellipticPointRhoPlusOne : ℂ).im = Real.sqrt 3 / 2`
- **What**: Imaginary coordinate of the elliptic point ρ+1.
- **How**: `simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]`.
- **Hypotheses**: none.
- **Uses-from-project**: `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`.
- **Used by**: `smooth_boundary_classification`.
- **Visibility**: `private`.
- **Lines**: 65-67.
- **Notes**: Coordinate extraction lemma for ρ+1.

## def `BoundaryWindingHyp`
- **Type**: `{H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H)) : Prop`
- **What**: Predicate that at every non-elliptic, non-strict-interior FD boundary point below height H, gWN(γ, z) = -1/2.
- **How**: ∀-quantification over z ∈ ℂ with positive imaginary part, height bound, exclusions of i, ρ, ρ+1, exclusion of strict interior `‖z‖ > 1 ∧ |z.re| < 1/2`, plus boundary conditions `Complex.normSq z ≥ 1` and `|z.re| ≤ 1/2`, asserting `HasGeneralizedWindingNumber γ z (-1/2)`.
- **Hypotheses**: H : ℝ, γ : PiecewiseC1Path.
- **Uses-from-project**: `PiecewiseC1Path`, `fdStart`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, `HasGeneralizedWindingNumber`.
- **Used by**: `mkFDWindingDataFull`, `boundaryWindingHyp_of_smoothData`, `boundaryWindingHyp_of_fdWindingDataFull`, `fdWindingDataFull_iff_windingData_and_boundary`.
- **Visibility**: public.
- **Lines**: 75-81.
- **Notes**: Core predicate isolating the boundary winding obligation.

## def `mkFDWindingDataFull`
- **Type**: `{H : ℝ} (D : FDWindingData H) (h_bdy : BoundaryWindingHyp D.boundary) : FDWindingDataFull H`
- **What**: Minimal assembler producing `FDWindingDataFull` from `FDWindingData` plus the boundary hypothesis.
- **How**: Structure literal `{ toFDWindingData := D, boundary_winding := h_bdy }`.
- **Hypotheses**: `D : FDWindingData H`, `h_bdy : BoundaryWindingHyp D.boundary`.
- **Uses-from-project**: `FDWindingData`, `FDWindingDataFull`, `BoundaryWindingHyp`.
- **Used by**: `mkFDWindingDataFull_of_smoothData`, `fdWindingDataFull_iff_windingData_and_boundary`.
- **Visibility**: public.
- **Lines**: 88-91.
- **Notes**: Pathway-1 constructor.

## theorem `boundaryWindingHyp_of_smoothData`
- **Type**: `{H : ℝ} {γ : PiecewiseC1Path (fdStart H) (fdStart H)} (h_data : ∀ z, ... → SmoothBoundaryWindingData γ z) : BoundaryWindingHyp γ`
- **What**: Build `BoundaryWindingHyp` by invoking the smooth-boundary-data oracle pointwise.
- **How**: `fun z h1 ... h8 => (h_data z h1 ... h8).hasWindingNumber`.
- **Hypotheses**: An oracle giving `SmoothBoundaryWindingData γ z` at each non-elliptic, non-interior FD boundary point.
- **Uses-from-project**: `SmoothBoundaryWindingData`, `BoundaryWindingHyp`, `PiecewiseC1Path`, `fdStart`, elliptic points.
- **Used by**: `mkFDWindingDataFull_of_smoothData`.
- **Visibility**: public.
- **Lines**: 97-106.
- **Notes**: Bridge from per-point smooth data to the global predicate.

## def `mkFDWindingDataFull_of_smoothData`
- **Type**: `{H : ℝ} (D : FDWindingData H) (h_data : ...) : FDWindingDataFull H`
- **What**: Full assembler combining `FDWindingData` and a `SmoothBoundaryWindingData` oracle into `FDWindingDataFull`.
- **How**: `mkFDWindingDataFull D (boundaryWindingHyp_of_smoothData h_data)`.
- **Hypotheses**: `D : FDWindingData H`, smooth-data oracle.
- **Uses-from-project**: `mkFDWindingDataFull`, `boundaryWindingHyp_of_smoothData`, `FDWindingData`, `FDWindingDataFull`, `SmoothBoundaryWindingData`.
- **Used by**: external (constructing `FDWindingDataFull`).
- **Visibility**: public.
- **Lines**: 110-117.
- **Notes**: Pathway-2 constructor.

## lemma `im_eq_sqrt3_half_of_normSq_one_of_absRe_half`
- **Type**: `{z : ℂ} (h_nsq : Complex.normSq z = 1) (hz_im : z.im > 0) (h_re_sq : z.re * z.re = 1/4) : z.im = Real.sqrt 3 / 2`
- **What**: On the unit circle with positive imaginary part and `re² = 1/4`, the imaginary part equals √3/2.
- **How**: Expand `Complex.normSq_apply`, derive `(z.im - √3/2)(z.im + √3/2) = 0` via `nlinarith` using `Real.mul_self_sqrt`, eliminate the negative root via `ne_of_gt (add_pos hz_im (by positivity))`.
- **Hypotheses**: unit-circle constraint, positive imaginary part, `re² = 1/4`.
- **Uses-from-project**: none directly; uses mathlib `Complex.normSq_apply`, `Real.mul_self_sqrt`.
- **Used by**: `smooth_boundary_classification`.
- **Visibility**: `private`.
- **Lines**: 123-132.
- **Notes**: Coordinate forcing for elliptic corners.

## theorem `smooth_boundary_classification`
- **Type**: `(z : ℂ) (hz_im : z.im > 0) (hz_ne_I) (hz_ne_rho) (hz_ne_rho1) (hz_not_int) (hz_nsq) (hz_re) : (|z.re| = 1/2 ∧ ‖z‖ > 1) ∨ (‖z‖ = 1 ∧ z.re ≠ 0 ∧ |z.re| ≠ 1/2)`
- **What**: Geometric dichotomy: a non-elliptic, non-interior FD boundary point lies either on a vertical edge or on the smooth part of the unit circle arc.
- **How** (>10 lines): Derive `1 ≤ ‖z‖` via `Real.one_le_sqrt`; case-split via `hnorm_ge.eq_or_lt`. In the `‖z‖ = 1` branch, use `im_eq_sqrt3_half_of_normSq_one_of_absRe_half` and `abs_eq` to rule out z = I, z = ρ, z = ρ+1 via the elliptic-point coordinate lemmas. In the `‖z‖ > 1` branch, force `|z.re| = 1/2` by contradiction with `hz_not_int`.
- **Hypotheses**: positive imaginary part, three elliptic-point exclusions, non-strict-interior, FD boundary norm/re bounds.
- **Uses-from-project**: `ellipticPointRho_re`, `ellipticPointRho_im`, `ellipticPointRhoPlusOne_re`, `ellipticPointRhoPlusOne_im`, `im_eq_sqrt3_half_of_normSq_one_of_absRe_half`.
- **Used by**: external (case-splitting for `SmoothBoundaryWindingData`).
- **Visibility**: public.
- **Lines**: 137-174.
- **Notes**: Core geometric content of pathway-3.

## theorem `boundary_point_on_vert_edge`
- **Type**: `{z : ℂ} (hz_im : 0 < z.im) (hz_re_half : |z.re| = 1/2) (hz_norm_gt : 1 < ‖z‖) : Real.sqrt 3 / 2 < z.im`
- **What**: On a vertical FD edge above the unit circle, `z.im > √3/2`.
- **How**: Single `nlinarith` invocation with hints `Complex.normSq_apply z`, `Complex.normSq_eq_norm_sq`, `sq_abs z.re`, `sq_nonneg (‖z‖ - 1)`, `Real.sq_sqrt (3 ≥ 0)`, `mul_self_nonneg (z.im - √3/2)`.
- **Hypotheses**: positive imaginary part, `|re| = 1/2`, `‖z‖ > 1`.
- **Uses-from-project**: none directly.
- **Used by**: external (vertical-edge case).
- **Visibility**: public.
- **Lines**: 180-186.
- **Notes**: Geometric refinement above the corners.

## theorem `boundary_point_on_arc_range`
- **Type**: `{z : ℂ} (hz_re_ne : z.re ≠ 0) (hz_re_half : |z.re| ≠ 1/2) : 0 < z.re * z.re ∧ z.re * z.re < 1/4 ∨ 0 < z.re * z.re ∧ 1/4 < z.re * z.re`
- **What**: On the unit-circle arc away from `i`, `ρ`, `ρ+1`, `re²` is in `(0, 1/4) ∪ (1/4, ∞)`.
- **How**: `mul_self_pos.mpr hz_re_ne` for positivity, then `lt_or_gt_of_ne` on `re² ≠ 1/4` (derived from `|re| ≠ 1/2` via `sq_abs` and `sq_eq_sq₀`).
- **Hypotheses**: `re ≠ 0`, `|re| ≠ 1/2`.
- **Uses-from-project**: none directly.
- **Used by**: external (arc case).
- **Visibility**: public.
- **Lines**: 191-200.
- **Notes**: Geometric refinement of the smooth-arc case.

## theorem `boundaryWindingHyp_of_fdWindingDataFull`
- **Type**: `{H : ℝ} (D : FDWindingDataFull H) : BoundaryWindingHyp D.boundary`
- **What**: Extract `BoundaryWindingHyp` from `FDWindingDataFull` (converse to `mkFDWindingDataFull`).
- **How**: `D.boundary_winding` (field projection).
- **Hypotheses**: `D : FDWindingDataFull H`.
- **Uses-from-project**: `FDWindingDataFull`, `BoundaryWindingHyp`.
- **Used by**: `fdWindingDataFull_iff_windingData_and_boundary`.
- **Visibility**: public.
- **Lines**: 207-209.
- **Notes**: Round-trip projection.

## theorem `fdWindingDataFull_iff_windingData_and_boundary`
- **Type**: `{H : ℝ} : (∃ _ : FDWindingDataFull H, True) ↔ ∃ D : FDWindingData H, BoundaryWindingHyp D.boundary`
- **What**: Existential equivalence: an `FDWindingDataFull` exists iff a winding-data pair satisfying the boundary hypothesis exists.
- **How**: `⟨fun ⟨D, _⟩ => ⟨D.toFDWindingData, D.boundary_winding⟩, fun ⟨D, h⟩ => ⟨mkFDWindingDataFull D h, trivial⟩⟩`.
- **Hypotheses**: none.
- **Uses-from-project**: `FDWindingData`, `FDWindingDataFull`, `BoundaryWindingHyp`, `mkFDWindingDataFull`.
- **Used by**: external (characterising the full-data obligation).
- **Visibility**: public.
- **Lines**: 213-217.
- **Notes**: Closes the API loop.

---

## File Summary

Three pathways turn `FDWindingData H` into `FDWindingDataFull H`. The predicate `BoundaryWindingHyp γ` captures the missing boundary winding condition (gWN = -1/2 at every non-elliptic, non-strict-interior FD boundary point); `mkFDWindingDataFull` and `mkFDWindingDataFull_of_smoothData` assemble the full data from a direct hypothesis or a per-point `SmoothBoundaryWindingData` oracle. The geometric core is `smooth_boundary_classification`, which dichotomises FD boundary points into "vertical edge" (`|re| = 1/2`, `‖z‖ > 1`) and "smooth arc" (`‖z‖ = 1`, `re ≠ 0`, `|re| ≠ 1/2`), backed by private elliptic-point coordinate lemmas. `boundary_point_on_vert_edge` and `boundary_point_on_arc_range` further refine each case. `boundaryWindingHyp_of_fdWindingDataFull` and `fdWindingDataFull_iff_windingData_and_boundary` close the round-trip API.
