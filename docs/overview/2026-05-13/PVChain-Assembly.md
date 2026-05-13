# PVChain/Assembly.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ValenceFormula/PVChain/Assembly.lean` (863 lines)

Imports: `OnCurveCapture`, `Seg5CuspIntegral`, `ArcContribution`, `ResidueSideInfra` (all `LeanModularForms.ForMathlib.ValenceFormula.PVChain.*`), `LeanModularForms.ForMathlib.ModularInvariance`.

Opens: `Complex MeasureTheory Set Filter Topology CongruenceSubgroup`; scoped `Real Interval UpperHalfPlane ModularForm Modular MatrixGroups`. Sets `[local instance] Classical.propDecidable`.

File-level variables: `{k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)`.

### `private lemma norm_sub_one_le`
- **Type**: `{z s : ℂ} (hz : z.re = 1/2) (hs : s.re = -1/2) : ‖(z - 1) - s‖ ≤ ‖z - s‖`
- **What**: For `z` on right vertical edge (re=1/2) and `s` on left edge (re=-1/2), translating `z` by `-1` shrinks the distance to `s`.
- **How**: Compute squared norms via `Complex.sq_norm` and `Complex.normSq_apply`: `‖(z-1)-s‖² = (z.im-s.im)²` and `‖z-s‖² = 1 + (z.im-s.im)²`, then `Real.sqrt_le_sqrt` + `Real.sqrt_sq`.
- **Hypotheses**: `z.re=1/2`, `s.re=-1/2`.
- **Uses from project**: [].
- **Used by**: `truncation_iff_shift`.
- **Visibility**: private (omit f hf).
- **Lines**: 45–66.
- **Notes**: 22 lines.

### `private lemma norm_sub_le_sub_one`
- **Type**: `{z s : ℂ} (hz : z.re = 1/2) (hs : s.re = 1/2) : ‖z - s‖ ≤ ‖(z - 1) - s‖`
- **What**: For `z` and `s` both on right edge (re=1/2), translating `z` by `-1` increases the distance.
- **How**: Same approach as `norm_sub_one_le`: squared norms `‖z-s‖²=(z.im-s.im)²` vs `‖(z-1)-s‖²=1+(z.im-s.im)²`, then sqrt monotonicity.
- **Hypotheses**: `z.re=s.re=1/2`.
- **Uses from project**: [].
- **Used by**: `truncation_iff_shift`.
- **Visibility**: private (omit f hf).
- **Lines**: 69–90.
- **Notes**: 22 lines.

### `private lemma truncation_iff_shift`
- **Type**: `(S : Finset UpperHalfPlane) (z : ℂ) (hz_re : z.re = 1/2) (ε : ℝ) : (∃ s ∈ sVertOfS S, ‖z - s‖ ≤ ε) ↔ (∃ s ∈ sVertOfS S, ‖(z-1) - s‖ ≤ ε)`
- **What**: ε-truncation predicates against the set of vertical singularity points are unchanged by the shift `z ↦ z-1` (used to identify seg1 and seg4 truncation regions).
- **How**: Cases on `s.re = ±1/2` via `sVertOfS_re`: when `s` is on left edge use shift `s↦s-1` (member by `sVertOfS_pair_left`); when on right use `norm_sub_one_le` / `norm_sub_le_sub_one` inequalities directly.
- **Hypotheses**: `z.re=1/2`.
- **Uses from project**: `sVertOfS`, `sVertOfS_re`, `sVertOfS_pair_left`, `sVertOfS_pair_right`, `norm_sub_one_le`, `norm_sub_le_sub_one`.
- **Used by**: `truncation_iff_shift_union`, `pvIntegral_vertical_cancel`.
- **Visibility**: private (omit f hf).
- **Lines**: 93–107.
- **Notes**: none.

### `private lemma norm_shift_neg_inv_eq`
- **Type**: `{z s : ℂ} (hz_re : z.re = 1/2) (hs_unit : ‖s‖ = 1) : ‖(z - 1) - (-(1:ℂ)/s)‖ = ‖z - s‖`
- **What**: For `z` on right edge and unit-modulus `s`, the shift `z↦z-1` followed by `s↦-1/s` (S-action on the arc) preserves the distance.
- **How**: Reduce both squared norms to `(z.re - s.re ± δ)² + (z.im - s.im)²` via `normSq_apply`; use `hz_re=1/2`, unit-circle identity `s.re²+s.im²=1`, and componentwise computation of `(-1/s).re=-s.re`, `(-1/s).im=s.im` (using `Complex.div_re/im` with `normSq=1`).
- **Hypotheses**: `z.re=1/2`, `‖s‖=1`.
- **Uses from project**: [].
- **Used by**: `truncation_iff_shift_union`.
- **Visibility**: private (omit f hf).
- **Lines**: 110–147.
- **Notes**: 38 lines.

### `private lemma neg_inv_involution`
- **Type**: `{s : ℂ} (hs_unit : ‖s‖ = 1) : -(1:ℂ) / (-(1:ℂ) / s) = s`
- **What**: The map `s ↦ -1/s` is an involution on the unit circle.
- **How**: `s ≠ 0` from `‖s‖=1`, then `field_simp`.
- **Hypotheses**: `‖s‖=1`.
- **Uses from project**: [].
- **Used by**: `truncation_iff_shift_union`.
- **Visibility**: private (omit f hf).
- **Lines**: 150–156.
- **Notes**: none.

### `private lemma norm_neg_inv_of_norm_one`
- **Type**: `{s : ℂ} (hs : ‖s‖ = 1) : ‖-(1:ℂ)/s‖ = 1`
- **What**: `s↦-1/s` preserves unit modulus.
- **How**: `norm_div`, `norm_neg`, `norm_one`, `hs`, `div_one`.
- **Hypotheses**: `‖s‖=1`.
- **Uses from project**: [].
- **Used by**: `truncation_iff_shift_union`.
- **Visibility**: private (omit f hf).
- **Lines**: 159–161.
- **Notes**: none.

### `private lemma truncation_iff_shift_union`
- **Type**: `(S : Finset UpperHalfPlane) (z : ℂ) (hz_re : z.re = 1/2) (ε : ℝ) : (∃ s ∈ sArcOfS S ∪ sVertOfS S, ‖z-s‖ ≤ ε) ↔ (∃ s ∈ sArcOfS S ∪ sVertOfS S, ‖(z-1)-s‖ ≤ ε)`
- **What**: Shift-invariance of ε-truncation against the combined arc+vert singularity set on the right vertical edge.
- **How**: Case on `s ∈ sArcOfS S` (use `-1/s` via `sArcOfS_closed`, `norm_shift_neg_inv_eq`, `neg_inv_involution`) or `s ∈ sVertOfS S` (use `truncation_iff_shift`).
- **Hypotheses**: `z.re=1/2`.
- **Uses from project**: `sArcOfS`, `sVertOfS`, `sArcOfS_closed`, `sArcOfS_unit`, `norm_shift_neg_inv_eq`, `neg_inv_involution`, `norm_neg_inv_of_norm_one`, `truncation_iff_shift`.
- **Used by**: `pvIntegral_vertical_cancel_union`.
- **Visibility**: private (omit f hf).
- **Lines**: 164–183.
- **Notes**: none.

### `private lemma logDeriv_modFormComp_periodic`
- **Type**: `Function.Periodic (logDeriv (modularFormCompOfComplex f)) (1 : ℂ)`
- **What**: The logarithmic derivative of `f∘complex` (a modular form lifted from `ℍ` to `ℂ`) has period 1 (T-invariance).
- **How**: Uses `SlashInvariantFormClass.periodic_comp_ofComplex` + `ModularFormClass.one_mem_strictPeriods_SL2Z`; then shows `deriv(g(z+1)) = deriv(g(z))` via `deriv_comp_add_const`; quotient is periodic.
- **Hypotheses**: `f : ModularForm (Gamma 1) k`.
- **Uses from project**: `modularFormCompOfComplex`.
- **Used by**: `pvIntegrand_seg4_eq_neg_seg1`, `modular_side_h_capture`.
- **Visibility**: private (omit hf).
- **Lines**: 186–198.
- **Notes**: none.

### `private lemma deriv_fdBoundary_H_on_seg1`
- **Type**: `(H : ℝ) (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) : deriv (fdBoundary_H H) u = -↑(H - √3/2) * I`
- **What**: On the seg1 piece `0 < u < 1`, the derivative of the H-boundary parametrization is `-(H - √3/2)·I` (pointing down).
- **How**: Use `fdBoundary_H =ᶠ[𝓝 u] fdBoundary_seg1_H` (eventually) via `fdBoundary_H_eq_seg1_H`; apply `Filter.EventuallyEq.deriv_eq` and `hasDerivAt_fdBoundary_seg1_H`.
- **Hypotheses**: `u ∈ Ioo 0 1`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_seg1_H`, `fdBoundary_H_eq_seg1_H`, `hasDerivAt_fdBoundary_seg1_H`.
- **Used by**: `pvIntegrand_seg4_eq_neg_seg1`.
- **Visibility**: private (omit f hf).
- **Lines**: 201–207.
- **Notes**: none.

### `private lemma deriv_fdBoundary_H_on_seg4`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ∈ Ioo (3:ℝ) 4) : deriv (fdBoundary_H H) t = ↑(H - √3/2) * I`
- **What**: On seg4 (`3 < t < 4`), the derivative is `(H - √3/2)·I` (pointing up — reversed from seg1).
- **How**: Same pattern as seg1 with `fdBoundary_H_eq_seg4_H` and `hasDerivAt_fdBoundary_seg4_H`.
- **Hypotheses**: `t ∈ Ioo 3 4`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_seg4_H`, `fdBoundary_H_eq_seg4_H`, `hasDerivAt_fdBoundary_seg4_H`.
- **Used by**: `pvIntegrand_seg4_eq_neg_seg1`.
- **Visibility**: private (omit f hf).
- **Lines**: 210–215.
- **Notes**: none.

### `private lemma integral_seg4_cov`
- **Type**: `(G : ℝ → ℂ) : ∫ t in (3:ℝ)..4, G t = ∫ u in (0:ℝ)..1, G (4 - u)`
- **What**: Change of variables `t = 4 - u`: integrating G over seg4 [3,4] equals integrating `G(4-u)` over [0,1].
- **How**: `intervalIntegral.integral_comp_sub_left` with `c=4`, normalizing endpoints.
- **Hypotheses**: any `G : ℝ → ℂ`.
- **Uses from project**: [].
- **Used by**: `pvIntegral_vertical_cancel`, `pvIntegral_vertical_cancel_union`.
- **Visibility**: private (omit f hf).
- **Lines**: 218–223.
- **Notes**: none.

### `private lemma pvIntegrand_seg4_eq_neg_seg1`
- **Type**: `(_S Sx) {H ε} (h_trunc_iff) (u) (hu : u ∈ Ioo 0 1) : pvIntegrand f (fdBoundary_H H) Sx ε (4-u) = -(pvIntegrand f (fdBoundary_H H) Sx ε u)`
- **What**: Under the (provided) truncation equivalence, the pv-integrand on seg4 equals the negative of the corresponding pv-integrand on seg1. (Vertical-edge cancellation pointwise.)
- **How**: Case on `∃ s ∈ Sx, ‖fdBoundary_H H u - s‖ ≤ ε`: if yes, both pv-integrands are zero; if no, evaluate using `fdBoundary_H_eq_seg4_H`, `seg4_eq_seg1_minus_one_H`, `fdBoundary_H_eq_seg1_H` to get `γ(4-u)=γ(u)-1`; then `logDeriv_modFormComp_periodic` gives `logDeriv(γ(4-u))=logDeriv(γ(u))`; finally `deriv_fdBoundary_H_on_seg4 = -deriv_fdBoundary_H_on_seg1` provides the sign flip.
- **Hypotheses**: truncation equivalence `h_trunc_iff` on `Ioo 0 1`.
- **Uses from project**: `pvIntegrand`, `cauchyPrincipalValueIntegrandOn`, `fdBoundary_H`, `fdBoundary_H_eq_seg4_H`, `seg4_eq_seg1_minus_one_H`, `fdBoundary_H_eq_seg1_H`, `logDeriv_modFormComp_periodic`, `deriv_fdBoundary_H_on_seg4`, `deriv_fdBoundary_H_on_seg1`, `modularFormCompOfComplex`.
- **Used by**: `pvIntegral_vertical_cancel`, `pvIntegral_vertical_cancel_union`.
- **Visibility**: private (omit hf).
- **Lines**: 226–257.
- **Notes**: 32 lines.

### `private lemma integral_neg_of_pw_neg`
- **Type**: `(g : ℝ → ℂ) (h_pw : ∀ u ∈ Ioo 0 1, g(4-u) = -(g u)) : ∫ u in (0:ℝ)..1, g(4-u) = ∫ u in (0:ℝ)..1, -(g u)`
- **What**: Pointwise-negation equality (off the measure-zero endpoint set {1}) implies integral equality.
- **How**: `intervalIntegral.integral_congr_ae` with `measure_mono (t={1})` plus `measure_singleton` to discharge the a.e. constraint.
- **Hypotheses**: pointwise negation on `Ioo 0 1`.
- **Uses from project**: [].
- **Used by**: `pvIntegral_vertical_cancel`, `pvIntegral_vertical_cancel_union`.
- **Visibility**: private (omit hf).
- **Lines**: 260–273.
- **Notes**: 14 lines.

### `private theorem pvIntegral_vertical_cancel`
- **Type**: `(S) {H} (_hH _h_oncurve_vert) : ∀ ε>0, (∫₀¹ pvIntegrand f (fdBoundary_H H) (sVertOfS S) ε t) + (∫₃⁴ pvIntegrand ...) = 0`
- **What**: For sVert-truncation only, the seg1+seg4 integrals cancel (T-invariance of pv-integrand).
- **How**: Change variables `seg4 ↦ seg1` via `integral_seg4_cov`; establish `truncation_iff_shift` (via `fdBoundary_H_eq_seg1_H`, `fdBoundary_H_eq_seg4_H`, `seg4_eq_seg1_minus_one_H`, and pure-real computation of `γ(u).re=1/2`); apply `pvIntegrand_seg4_eq_neg_seg1` and `integral_neg_of_pw_neg`; conclude with `intervalIntegral.integral_neg` + `ring`.
- **Hypotheses**: H > √3/2, vertical on-curve capture (unused in body via underscore).
- **Uses from project**: `pvIntegrand`, `fdBoundary_H`, `sVertOfS`, `fdBoundary_H_eq_seg1_H`, `fdBoundary_H_eq_seg4_H`, `seg4_eq_seg1_minus_one_H`, `truncation_iff_shift`, `pvIntegrand_seg4_eq_neg_seg1`, `integral_seg4_cov`, `integral_neg_of_pw_neg`, `modularFormCompOfComplex`.
- **Used by**: unused in file.
- **Visibility**: private (omit hf).
- **Lines**: 276–303.
- **Notes**: 28 lines.

### `private theorem pvIntegral_vertical_cancel_union`
- **Type**: same as `pvIntegral_vertical_cancel` but with `sArcOfS S ∪ sVertOfS S` instead of just `sVertOfS S`.
- **What**: Seg1+seg4 cancellation extends to the union of arc and vertical singularity sets (used in the final modular-side composition).
- **How**: Same pattern as `pvIntegral_vertical_cancel`, but uses `truncation_iff_shift_union` instead of `truncation_iff_shift` to handle arc-side reflections via `s ↦ -1/s`.
- **Hypotheses**: as above.
- **Uses from project**: `pvIntegrand`, `fdBoundary_H`, `sArcOfS`, `sVertOfS`, `fdBoundary_H_eq_seg1_H`, `fdBoundary_H_eq_seg4_H`, `seg4_eq_seg1_minus_one_H`, `truncation_iff_shift_union`, `pvIntegrand_seg4_eq_neg_seg1`, `integral_seg4_cov`, `integral_neg_of_pw_neg`, `modularFormCompOfComplex`.
- **Used by**: `cpv_modular_side_tendsto`.
- **Visibility**: private (omit hf).
- **Lines**: 306–335.
- **Notes**: 30 lines.

### `private theorem tendsto_pvIntegral_arc`
- **Type**: `(S) {H} (_hH _h_oncurve_arc) : Tendsto (fun ε => ∫₁³ pvIntegrand f (fdBoundary_H H) (sArcOfS S ∪ sVertOfS S) ε t) (𝓝[>] 0) (𝓝 (-(2π·I·k/12)))`
- **What**: Arc piece (seg2+seg3) of the ε-truncated integral tends to `-(2πi·k/12)` as ε→0⁺ (S-transformation contribution).
- **How**: One-line delegation to `tendsto_pvIntegral_arc_bridge` (from `ArcContribution`).
- **Hypotheses**: H > √3/2, arc on-curve capture (passed through unused locally).
- **Uses from project**: `pvIntegrand`, `fdBoundary_H`, `sArcOfS`, `sVertOfS`, `tendsto_pvIntegral_arc_bridge`, `modularFormCompOfComplex`.
- **Used by**: `cpv_modular_side_tendsto`.
- **Visibility**: private (omit hf).
- **Lines**: 338–346.
- **Notes**: none.

### `private theorem seg5_logDeriv_integral_value`
- **Type**: `{H} (_hH _hcusp_nonvan) : ∫₄⁵ logDeriv (modularFormCompOfComplex f) (fdBoundary_H H t) · deriv (fdBoundary_H H) t = 2π·I·ord_∞(f)`
- **What**: Non-truncated horizontal-edge integral of `f'/f` equals `2πi·ord∞(f)` (from q-expansion winding).
- **How**: One-line delegation to `seg5_logDeriv_integral_value_bridge` (from `Seg5CuspIntegral`).
- **Hypotheses**: H > √3/2, cusp non-vanishing on the q-disk of radius `seg5_q_radius_H H`.
- **Uses from project**: `modularFormCompOfComplex`, `fdBoundary_H`, `seg5_q_radius_H`, `orderAtCusp'`, `seg5_logDeriv_integral_value_bridge`, `SlashInvariantFormClass.cuspFunction`.
- **Used by**: `tendsto_pvIntegral_seg5`.
- **Visibility**: private (include hf).
- **Lines**: 350–358.
- **Notes**: none.

### `private theorem tendsto_pvIntegral_seg5`
- **Type**: `(S) {H} (hH hcusp_nonvan h_vert_below_H h_arc_below_H) : Tendsto (fun ε => ∫₄⁵ pvIntegrand f ...) (𝓝[>] 0) (𝓝 (2π·I·ord_∞(f)))`
- **What**: Seg5 ε-truncated pv-integral tends to `2πi·ord_∞(f)` as ε→0⁺.
- **How**: All singularities lie below H, so for ε small (specifically `ε < δ = inf_{s∈S} (H - s.im)`) no truncation occurs on seg5; identify `pvIntegrand` with `logDeriv · deriv` via `intervalIntegral.integral_congr_ae'` on `Ioc 4 5` then apply `seg5_logDeriv_integral_value`. Key lemma: `Finset.inf'_le` for ε bound, and `Complex.abs_im_le_norm` for distance from `H` line. Concludes via `tendsto_const_nhds.congr'`.
- **Hypotheses**: H>√3/2, cusp nonvanishing, all `s.im < H` for s in arc/vert.
- **Uses from project**: `pvIntegrand`, `cauchyPrincipalValueIntegrandOn`, `fdBoundary_H`, `fdBoundary_H_eq_seg5_H`, `fdBoundary_seg5_H`, `sArcOfS`, `sVertOfS`, `modularFormCompOfComplex`, `seg5_logDeriv_integral_value`, `orderAtCusp'`, `seg5_q_radius_H`, `SlashInvariantFormClass.cuspFunction`.
- **Used by**: `cpv_modular_side_tendsto`.
- **Visibility**: private (include hf).
- **Lines**: 361–422.
- **Notes**: 62 lines. Key step: `δ := (sArcOfS S ∪ sVertOfS S).inf' h_ne (fun s => H - s.im)` and `Finset.inf'_le`.

### `private lemma norm_deriv_fdBoundary_H_le`
- **Type**: `{H} (hH) {t} (_ht : t ∈ Icc 0 5) (ht_ne1 ht_ne3 ht_ne4) : ‖deriv (fdBoundary_H H) t‖ ≤ max H 1`
- **What**: Uniform bound on the derivative of the H-boundary parametrization on `Icc 0 5 \ {1,3,4}`.
- **How**: Case-split on which segment t is in: seg1/seg4 give `|H - √3/2|·1`, arc gives `‖π/6‖·1·1=π/6 ≤ 4/6`, seg5 gives `1`. Use `hasDerivAt_*.deriv` for each segment and bound via `Real.pi_le_four`, `Real.sqrt_nonneg`, etc.
- **Hypotheses**: H>√3/2, t ∈ Icc 0 5, t ∉ {1,3,4}.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_hasDerivAt_seg1`, `fdBoundary_H_hasDerivAt_arc`, `fdBoundary_H_hasDerivAt_seg4`, `fdBoundary_H_hasDerivAt_seg5`.
- **Used by**: `integrableOn_logDeriv_mul_deriv_farSet`.
- **Visibility**: private (omit f hf).
- **Lines**: 425–470.
- **Notes**: 46 lines.

### `private lemma integrableOn_logDeriv_mul_deriv_farSet`
- **Type**: `(S) {H} (hH h_capture) {ε} (hε : 0<ε) : IntegrableOn (fun t => logDeriv g (γ t) · deriv γ t) K'` where `K' = {t ∈ Icc 0 5 | ∀ s ∈ S₀, ε ≤ ‖γ t - s‖}` (far from singular set).
- **What**: The non-truncated integrand `f'/f ∘ γ · γ'` is integrable on the closed "far set" `K'` (where no truncation kicks in).
- **How**: K' is compact (closed inside `Icc 0 5`, with closed condition `ε ≤ ‖γ t - s‖` for finitely many s). Use `h_capture` + far-from-S to show `g(γ t) ≠ 0` on K'; deduce `logDeriv g` continuous on K' via `AnalyticAt.div` of `f.holo'`; pick max of `‖logDeriv g (γ t)‖` on K'; bound `‖integrand‖ ≤ M·max(H,1)` via `norm_deriv_fdBoundary_H_le` (off measure-zero {1,3,4}); finish with `IntegrableOn.of_bound`.
- **Hypotheses**: H>√3/2, on-curve capture, ε>0.
- **Uses from project**: `fdBoundary_H`, `sArcOfS`, `sVertOfS`, `modularFormCompOfComplex`, `fdBoundary_H_continuous`, `fdBoundary_H_im_pos`, `UpperHalfPlane.mdifferentiable_iff`, `UpperHalfPlane.isOpen_upperHalfPlaneSet`, `norm_deriv_fdBoundary_H_le`.
- **Used by**: `pvIntegrand_intervalIntegrable`.
- **Visibility**: private (omit hf).
- **Lines**: 473–541.
- **Notes**: 69 lines.

### `private lemma pvIntegrand_intervalIntegrable`
- **Type**: `(S) {H} (hH) {ε} (hε h_capture) {a b} (ha hb : a,b ∈ Icc 0 5) : IntervalIntegrable (pvIntegrand f (fdBoundary_H H) (sArcOfS S ∪ sVertOfS S) ε) volume a b`
- **What**: The ε-truncated pv-integrand is interval-integrable on any subinterval of `Icc 0 5`.
- **How**: Split `uIoc a b = K ∪ (uIoc a b \ K)` where K is the "far set"; on K, `pvIntegrand = logDeriv · deriv` (integrable by `integrableOn_logDeriv_mul_deriv_farSet`); on `uIoc a b \ K`, `pvIntegrand = 0` (truncated). Combine via `IntegrableOn.union` after `union_diff_cancel`. K is measurable via `Finset.finite_toSet.isClosed_biUnion`.
- **Hypotheses**: H>√3/2, ε>0, on-curve capture, endpoints in Icc 0 5.
- **Uses from project**: `pvIntegrand`, `cauchyPrincipalValueIntegrandOn`, `fdBoundary_H`, `fdBoundary_H_continuous`, `sArcOfS`, `sVertOfS`, `modularFormCompOfComplex`, `integrableOn_logDeriv_mul_deriv_farSet`.
- **Used by**: `tendsto_pvIntegral_split`.
- **Visibility**: private (omit hf).
- **Lines**: 544–601.
- **Notes**: 58 lines. Sorry-flagged in MEMORY.md as one of the 3 remaining global sorries, but in this file's current version it is a fully-proved private lemma (the file MEMORY entry references Assembly.lean:461 — may refer to an older state).

### `private theorem tendsto_pvIntegral_split`
- **Type**: `(S) {H} (hH h_capture) : ∀ᶠ ε in 𝓝[>] 0, ∫₀⁵ pvIntegrand = (∫₀¹) + (∫₁³) + (∫₃⁴) + (∫₄⁵)`
- **What**: Eventually in ε, the seg-0..5 integral splits as the sum over [0,1], [1,3], [3,4], [4,5].
- **How**: Apply `intervalIntegral.integral_add_adjacent_intervals` three times using `pvIntegrand_intervalIntegrable` to bridge through 0→1, 1→3, 3→4, 4→5.
- **Hypotheses**: H>√3/2, on-curve capture.
- **Uses from project**: `pvIntegrand`, `fdBoundary_H`, `sArcOfS`, `sVertOfS`, `modularFormCompOfComplex`, `pvIntegrand_intervalIntegrable`.
- **Used by**: `cpv_modular_side_tendsto`.
- **Visibility**: private (omit hf).
- **Lines**: 604–636.
- **Notes**: 33 lines.

### `private lemma modFormComp_ne_zero_at_height`
- **Type**: `{H} (hH_pos : 0<H) (hcusp) {z} (hz_im : z.im = H) : modularFormCompOfComplex f z ≠ 0`
- **What**: If H is large enough for cusp-disk non-vanishing and `z.im = H`, then `f(z) ≠ 0`.
- **How**: `modularFormCompOfComplex f z = f ⟨z, ...⟩` via `UpperHalfPlane.ofComplex_apply_of_im_pos`; `q := exp(2πi·z)` has `‖q‖ = exp(-2π·H) ≤ seg5_q_radius_H H`; use `SlashInvariantFormClass.eq_cuspFunction` (relating f and cuspFunction at q) and `hcusp` rules out vanishing.
- **Hypotheses**: H>0, cusp non-vanishing on closedBall(0, seg5_q_radius_H H), z.im = H.
- **Uses from project**: `modularFormCompOfComplex`, `seg5_q_radius_H`, `SlashInvariantFormClass.cuspFunction`, `SlashInvariantFormClass.eq_cuspFunction`, `ModularFormClass.one_mem_strictPeriods_SL2Z`, `UpperHalfPlane.ofComplex_apply_of_im_pos`.
- **Used by**: `modular_side_h_capture`.
- **Visibility**: private (omit hf).
- **Lines**: 639–662.
- **Notes**: 24 lines.

### `private lemma modular_side_h_capture`
- **Type**: `(S) (_hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete hH_sqrt3 hH_gt_one _hH_bound hcusp) : ∀ t ∈ Icc 0 5, modularFormCompOfComplex f (fdBoundary_H H t) = 0 → fdBoundary_H H t ∈ ↑(sArcOfS S ∪ sVertOfS S)`
- **What**: On-curve capture for the entire boundary `fdBoundary_H`: any zero of `f` along the H-boundary lands either in `sArcOfS S` (arc piece) or in `sVertOfS S` (vertical pieces).
- **How**: Big case-split on `t ∈ [0,1) ∪ {1} ∪ (1,3) ∪ {3} ∪ (3,4) ∪ {4} ∪ (4,5]`: seg1/4/5 zeros at `im=H` are ruled out by `modFormComp_ne_zero_at_height`; interior arc zeros captured by `oncurve_arc_capture`; vertical zeros by `oncurve_vert_capture`; corners `t=1,3` give ρ+1, ρ via `fdBoundary_H_at_one_eq_rho_plus_one`, `fdBoundary_H_at_three_eq_rho`, then `sArcOfS_rho_plus_one_in`, `sArcOfS_rho_in`. Seg4 case `(3,4)` uses periodicity to reduce to a seg1 vertical zero shifted by `+1`.
- **Hypotheses**: S ⊂ 𝒟, S complete for zeros of order ≠ 0, H > √3/2, H > 1, all s.im<H, cusp non-vanishing.
- **Uses from project**: `fdBoundary_H`, `sArcOfS`, `sVertOfS`, `modularFormCompOfComplex`, `fdBoundary_H_eq_seg1_H`, `fdBoundary_H_eq_arc`, `fdBoundary_H_eq_seg4_H`, `fdBoundary_H_eq_seg5_H`, `fdBoundary_H_at_one_eq_rho_plus_one`, `fdBoundary_H_at_three_eq_rho`, `fdBoundary_H_at_four`, `seg4_eq_seg1_minus_one_H`, `sArcOfS_rho_plus_one_in`, `sArcOfS_rho_in`, `sVertOfS_pair_left`, `oncurve_arc_capture`, `oncurve_vert_capture`, `modFormComp_ne_zero_at_height`, `ModularFormClass.one_mem_strictPeriods_SL2Z`, `SlashInvariantFormClass.periodic_comp_ofComplex`, `orderOfVanishingAt'`, `𝒟`, `seg5_q_radius_H`.
- **Used by**: `cpv_modular_side_tendsto`.
- **Visibility**: private (include hf).
- **Lines**: 665–761.
- **Notes**: 97 lines.

### `theorem cpv_modular_side_tendsto`
- **Type**: `(S) (_hS hS_complete) : ∃ H₀ > √3/2, ∀ {H} (hH : H₀ ≤ H), Tendsto (fun ε => ∫₀⁵ pvIntegrand f (fdBoundary_H H) (sArcOfS S ∪ sVertOfS S) ε t) (𝓝[>] 0) (𝓝 (-(2πi·(k/12 - ord_∞(f)))))`
- **What**: **Main theorem**: the ε-truncated boundary integral of `f'/f` (CPV-style) tends to `-(2πi·(k/12 - ord_∞(f)))` as ε→0⁺, for all sufficiently large H.
- **How**: Compose: pick H₀ from `exists_height_cusp_nonvanishing` and `exists_height_bound_S`. For any H ≥ H₀: `tendsto_pvIntegral_split` lets us split into 4 pieces. The vertical pair (seg1+seg4) cancels via `pvIntegral_vertical_cancel_union` → tends to 0. The arc piece tends to `-(2πi·k/12)` via `tendsto_pvIntegral_arc`. The seg5 piece tends to `2πi·ord_∞(f)` via `tendsto_pvIntegral_seg5`. Combine via `Tendsto.add` after algebraic massaging.
- **Hypotheses**: S ⊂ 𝒟, S complete for non-zero-order points.
- **Uses from project**: `pvIntegrand`, `fdBoundary_H`, `sArcOfS`, `sVertOfS`, `sVertOfS_im_lt_height_bound`, `sArcOfS_unit`, `exists_height_cusp_nonvanishing`, `exists_height_bound_S`, `cusp_nonvanishing_height_mono`, `oncurve_arc_capture`, `oncurve_vert_capture`, `fdBoundary_H_eq_arc`, `tendsto_pvIntegral_split`, `modular_side_h_capture`, `tendsto_pvIntegral_arc`, `tendsto_pvIntegral_seg5`, `pvIntegral_vertical_cancel_union`, `modularFormCompOfComplex`, `orderOfVanishingAt'`, `orderAtCusp'`, `𝒟`, `seg5_q_radius_H`.
- **Used by**: unused in file (this is the file's exported main result).
- **Visibility**: public (include hf).
- **Lines**: 765–860.
- **Notes**: 96 lines.

## File Summary

- **Total declarations**: 22 (20 private + 2 public exports — `cpv_modular_side_tendsto`).
- **Key API**: `cpv_modular_side_tendsto` (main theorem). Supporting: `pvIntegrand_intervalIntegrable`, `tendsto_pvIntegral_split`, `tendsto_pvIntegral_arc`, `tendsto_pvIntegral_seg5`, `pvIntegral_vertical_cancel_union`, `modular_side_h_capture`.
- **Unused in file**: `pvIntegral_vertical_cancel` (subsumed by `_union` variant — kept as a documented intermediate). The main theorem itself is the public export consumed downstream.
- **Sorries**: 0 in current file. MEMORY.md lists `pvIntegrand_intervalIntegrable` and `cpv_residue_side_tendsto` (a separate theorem, declared in a different file) as remaining-sorry references, but neither corresponds to a `sorry` in this file's current text.
- **set_options**: none. Uses `attribute [local instance] Classical.propDecidable`.
- **Long proofs (>30 lines)**: `cpv_modular_side_tendsto` (96), `modular_side_h_capture` (97), `integrableOn_logDeriv_mul_deriv_farSet` (69), `tendsto_pvIntegral_seg5` (62), `pvIntegrand_intervalIntegrable` (58), `norm_deriv_fdBoundary_H_le` (46), `norm_shift_neg_inv_eq` (38), `tendsto_pvIntegral_split` (33), `pvIntegrand_seg4_eq_neg_seg1` (32), `pvIntegral_vertical_cancel_union` (30), `pvIntegral_vertical_cancel` (28), `modFormComp_ne_zero_at_height` (24), `norm_sub_one_le`/`norm_sub_le_sub_one` (22 each), `integral_neg_of_pw_neg` (14).
- **Purpose**: The "modular side" assembly file for the valence formula's principal-value chain: takes the four piece-wise contributions to the contour integral `∮_∂𝒟ₕ f'/f dz` (seg1 vertical down, arc, seg4 vertical up, seg5 horizontal at height H) and shows that the ε-truncated total tends to `-(2πi·(k/12 - ord_∞(f)))`. The vertical pieces cancel via T-invariance (S-shifted), the arc piece gives the elliptic/cusp orbifold contribution `-2πi·k/12`, and the horizontal piece gives `2πi·ord_∞(f)` from the q-expansion. Hierarchy: small lemmas (truncation/shift invariance) → per-segment integrability → finite split → final `Tendsto` composition.
