# ArcFTC.md — Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ArcFTC.lean` (246 lines)

## Entries

### theorem `arg_exp_mul_I`
- **Type**: `(θ : ℝ) (hθ : θ ∈ Ioc (-π) π) : arg (exp (↑θ * I)) = θ`
- **What**: Argument of `exp(iθ)` for principal-branch `θ`.
- **How**: `rw [exp_mul_I]`; apply `Complex.arg_cos_add_sin_mul_I hθ`.
- **Hypotheses**: `θ ∈ (-π, π]`.
- **Uses-from-project**: None (mathlib API).
- **Used by**: `arg_right_tangent_rhoPlusOne`, `arg_left_tangent_rho`.
- **Visibility**: public.
- **Lines**: 66–68.

### theorem `arg_ofReal_mul_I`
- **Type**: `(r : ℝ) (hr : 0 < r) : arg (↑r * I) = π/2`
- **What**: Argument of a positive real multiple of `I`.
- **How**: `Complex.arg_real_mul _ hr` then `Complex.arg_I`.
- **Hypotheses**: `0 < r`.
- **Uses-from-project**: None.
- **Used by**: `arg_neg_left_tangent_rhoPlusOne`.
- **Visibility**: public.
- **Lines**: 71–73.

### theorem `fdBoundary_arc_deriv_eq`
- **Type**: `(t : ℝ) : deriv (fun s => exp (↑(fdArcAngle s) * I)) t = ↑(5π/6) * I * exp (↑(fdArcAngle t) * I)`
- **What**: Derivative formula for the arc parametrization on the FD boundary.
- **How**: `simp [fdArcAngle]`; build `HasDerivAt (fun s => π/3 + (5s-1)·(π/6)) (5π/6) t` via `((hasDerivAt_id).const_mul 5).sub_const 1 .mul_const (π/6) .const_add (π/3)` with `convert … using 1; ring`; then `(hd.ofReal_comp.mul_const I).cexp.deriv`; `push_cast; ring`.
- **Hypotheses**: None.
- **Uses-from-project**: `fdArcAngle`.
- **Used by**: `fdBoundary_arc_deriv_at_two_fifths`, `fdBoundary_arc_deriv_at_one_fifth`, `fdBoundary_arc_deriv_at_three_fifths`.
- **Visibility**: public.
- **Lines**: 79–88.

### theorem `fdBoundary_arc_deriv_at_two_fifths`
- **Type**: `: deriv (fun s => exp (↑(fdArcAngle s) * I)) (2/5 : ℝ) = -(↑(5π/6) : ℂ)`
- **What**: Arc tangent at `i` is `-(5π/6)` (leftward).
- **How**: `rw [fdBoundary_arc_deriv_eq, fdArcAngle_at_two_fifths, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]`; `simp [mul_assoc]`.
- **Hypotheses**: None.
- **Uses-from-project**: `fdArcAngle`, `fdArcAngle_at_two_fifths`, `fdBoundary_arc_deriv_eq`.
- **Used by**: `fdBoundary_angle_at_I_partition` (indirectly via downstream).
- **Visibility**: public.
- **Lines**: 91–96.

### theorem `fdBoundary_arc_deriv_at_one_fifth`
- **Type**: `: deriv (fun s => exp (↑(fdArcAngle s) * I)) (1/5 : ℝ) = ↑(5π/6) * I * exp (↑(π/3) * I)`
- **What**: Right tangent at `ρ+1` on the arc.
- **How**: `rw [fdBoundary_arc_deriv_eq, fdArcAngle_at_one_fifth]`.
- **Hypotheses**: None.
- **Uses-from-project**: `fdArcAngle`, `fdArcAngle_at_one_fifth`, `fdBoundary_arc_deriv_eq`.
- **Used by**: `arg_right_tangent_rhoPlusOne` (indirectly).
- **Visibility**: public.
- **Lines**: 99–102.

### theorem `fdBoundary_arc_deriv_at_three_fifths`
- **Type**: `: deriv (fun s => exp (↑(fdArcAngle s) * I)) (3/5 : ℝ) = ↑(5π/6) * I * exp (↑(2π/3) * I)`
- **What**: Left tangent at `ρ` on the arc.
- **How**: `rw [fdBoundary_arc_deriv_eq, fdArcAngle_at_three_fifths]`.
- **Hypotheses**: None.
- **Uses-from-project**: `fdArcAngle`, `fdArcAngle_at_three_fifths`, `fdBoundary_arc_deriv_eq`.
- **Used by**: `arg_left_tangent_rho` (indirectly).
- **Visibility**: public.
- **Lines**: 105–108.

### theorem `fdBoundary_seg1_deriv`
- **Type**: `(H t : ℝ) : deriv (fun s => (1:ℂ)/2 + (↑H - 5↑s·(↑H - √3/2))·I) t = -(5·(↑H - √3/2))·I`
- **What**: Derivative on the right vertical segment.
- **How**: `HasDerivAt (·:ℝ→ℂ) 1 t` from `Complex.ofRealCLM.hasDerivAt`; build `HasDerivAt` for the linear-in-s part via `(h1.const_mul (5·(↑H - √3/2))).const_sub (↑H)`; `convert … using 1; funext s; ring; ring`; combine with `hasDerivAt_const (1/2)` then `.mul_const I`; `.deriv.trans (by ring)`.
- **Hypotheses**: None.
- **Uses-from-project**: None (mathlib derivative API).
- **Used by**: Downstream segment-1 tangent users.
- **Visibility**: public.
- **Lines**: 113–124.
- **Notes**: Proof >10 lines; key lemma `Complex.ofRealCLM.hasDerivAt`.

### theorem `fdBoundary_seg4_deriv`
- **Type**: `(H t : ℝ) : deriv (fun s => (-1:ℂ)/2 + (√3/2 + (5↑s - 3)·(↑H - √3/2))·I) t = 5·(↑H - √3/2)·I`
- **What**: Derivative on the left vertical segment (upward direction).
- **How**: Symmetric to `fdBoundary_seg1_deriv`: build HasDerivAt for the linear-in-s polynomial via `((h1.const_mul 5).sub_const 3).mul_const (↑H - √3/2) .const_add (√3/2)`; combine with `hasDerivAt_const (-1/2)`; `.deriv.trans (by ring)`.
- **Hypotheses**: None.
- **Uses-from-project**: None (mathlib derivative API).
- **Used by**: Downstream segment-4 tangent users.
- **Visibility**: public.
- **Lines**: 127–138.
- **Notes**: Proof >10 lines.

### theorem `I_mul_exp_pi_third`
- **Type**: `: I * exp (↑(π/3) * I) = exp (↑(5π/6) * I)`
- **What**: Multiplicative identity rotating by π/2.
- **How**: `rw` showing `((5π/6 : ℝ) : ℂ) * I = ↑π/2 * I + ↑(π/3) * I` via `push_cast; ring`; then `exp_add` and `Complex.exp_pi_div_two_mul_I`.
- **Hypotheses**: None.
- **Uses-from-project**: None (mathlib `Complex.exp_pi_div_two_mul_I`).
- **Used by**: `arg_right_tangent_rhoPlusOne`.
- **Visibility**: public.
- **Lines**: 143–146.

### theorem `arg_right_tangent_rhoPlusOne`
- **Type**: `: arg (I * exp (↑(π/3) * I)) = 5π/6`
- **What**: Arg of the right tangent at ρ+1.
- **How**: `rw [I_mul_exp_pi_third]`; apply `arg_exp_mul_I` with membership `(-π, π]` proved by two `linarith [Real.pi_pos]` calls.
- **Hypotheses**: None.
- **Uses-from-project**: `I_mul_exp_pi_third`, `arg_exp_mul_I`.
- **Used by**: `fdBoundary_crossing_angle_at_rhoPlusOne`.
- **Visibility**: public.
- **Lines**: 149–152.

### theorem `arg_neg_left_tangent_rhoPlusOne`
- **Type**: `(H) (hH : fdHeightValid H) : arg (5·(↑H - √3/2)·I) = π/2`
- **What**: Arg of negated left tangent at ρ+1 (a positive real multiple of `I`).
- **How**: Unfold `fdHeightValid`; rewrite to `↑(5·(H - √3/2)) * I` via `push_cast; ring`; apply `arg_ofReal_mul_I` with positivity from `linarith`.
- **Hypotheses**: `fdHeightValid H` (giving `H > √3/2`).
- **Uses-from-project**: `fdHeightValid`, `arg_ofReal_mul_I`.
- **Used by**: `fdBoundary_crossing_angle_at_rhoPlusOne`, `arg_right_tangent_rho`.
- **Visibility**: public.
- **Lines**: 155–160.

### theorem `fdBoundary_crossing_angle_at_rhoPlusOne`
- **Type**: `(H) (hH : fdHeightValid H) : arg (I·exp (↑(π/3)·I)) - arg (5·(↑H - √3/2)·I) = π/3`
- **What**: Crossing angle at ρ+1 is π/3.
- **How**: `rw [arg_right_tangent_rhoPlusOne, arg_neg_left_tangent_rhoPlusOne H hH]; ring`.
- **Hypotheses**: `fdHeightValid H`.
- **Uses-from-project**: `arg_right_tangent_rhoPlusOne`, `arg_neg_left_tangent_rhoPlusOne`, `fdHeightValid`.
- **Used by**: Winding-number/angle assembly at ρ+1.
- **Visibility**: public.
- **Lines**: 163–166.

### theorem `I_mul_exp_two_pi_third`
- **Type**: `: I * exp (↑(2π/3) * I) = exp (↑(-5π/6) * I)`
- **What**: Multiplicative identity (with 2π adjustment) for the ρ side.
- **How**: `rw` showing `(-5π/6 : ℝ : ℂ) * I = ↑π/2 * I + ↑(2π/3) * I - 2π * I` via `push_cast; ring`; then `exp_sub`, `exp_add`, `Complex.exp_two_pi_mul_I`, `div_one`, `Complex.exp_pi_div_two_mul_I`.
- **Hypotheses**: None.
- **Uses-from-project**: `Complex.exp_two_pi_mul_I`, `Complex.exp_pi_div_two_mul_I`.
- **Used by**: `arg_left_tangent_rho`, `arg_neg_left_tangent_rho`.
- **Visibility**: public.
- **Lines**: 169–173.

### theorem `arg_left_tangent_rho`
- **Type**: `: arg (I * exp (↑(2π/3) * I)) = -5π/6`
- **What**: Arg of left tangent at ρ.
- **How**: `rw [I_mul_exp_two_pi_third]`; apply `arg_exp_mul_I` with membership proved by `nlinarith [Real.pi_pos]` (lower) and `linarith [Real.pi_pos]` (upper).
- **Hypotheses**: None.
- **Uses-from-project**: `I_mul_exp_two_pi_third`, `arg_exp_mul_I`.
- **Used by**: `arg_neg_left_tangent_rho`.
- **Visibility**: public.
- **Lines**: 176–179.

### theorem `arg_neg_left_tangent_rho`
- **Type**: `: arg (-(I * exp (↑(2π/3) * I))) = π/6`
- **What**: Arg of the negated left tangent at ρ uses `arg(-z) = arg(z) + π` since `im(z) < 0`.
- **How**: Apply `Complex.arg_neg_eq_arg_add_pi_of_im_neg`; rewrite `arg_left_tangent_rho` and finish first goal with `ring`; for the side condition (im negative), `rw [I_mul_exp_two_pi_third, exp_mul_I, ← ofReal_cos, ← ofReal_sin]`; `simp`; recast `(-5π/6 : ℝ) = -(π - π/6)`, `Real.sin_neg`; show `Real.sin (π - π/6) > 0` via `Real.sin_pi_sub`, `Real.sin_pos_of_pos_of_lt_pi`; finish with `linarith`.
- **Hypotheses**: None.
- **Uses-from-project**: `I_mul_exp_two_pi_third`, `arg_left_tangent_rho`.
- **Used by**: `fdBoundary_crossing_angle_at_rho`.
- **Visibility**: public.
- **Lines**: 183–193.
- **Notes**: Proof >10 lines; key lemmas `Complex.arg_neg_eq_arg_add_pi_of_im_neg`, `Real.sin_pos_of_pos_of_lt_pi`.

### theorem `arg_right_tangent_rho`
- **Type**: `(H) (hH : fdHeightValid H) : arg (5·(↑H - √3/2)·I) = π/2`
- **What**: Right tangent at ρ is a positive real multiple of `I`.
- **How**: Alias of `arg_neg_left_tangent_rhoPlusOne` (same expression).
- **Hypotheses**: `fdHeightValid H`.
- **Uses-from-project**: `arg_neg_left_tangent_rhoPlusOne`.
- **Used by**: `fdBoundary_crossing_angle_at_rho`.
- **Visibility**: public.
- **Lines**: 196–198.

### theorem `fdBoundary_crossing_angle_at_rho`
- **Type**: `(H) (hH : fdHeightValid H) : arg (5·(↑H - √3/2)·I) - arg (-(I·exp (↑(2π/3)·I))) = π/3`
- **What**: Crossing angle at ρ is π/3.
- **How**: `rw [arg_right_tangent_rho H hH, arg_neg_left_tangent_rho]; ring`.
- **Hypotheses**: `fdHeightValid H`.
- **Uses-from-project**: `arg_right_tangent_rho`, `arg_neg_left_tangent_rho`, `fdHeightValid`.
- **Used by**: Winding-number/angle assembly at ρ.
- **Visibility**: public.
- **Lines**: 201–204.

### theorem `fdBoundary_angle_at_I_partition`
- **Type**: `: arg (-(↑(5π/6) : ℂ)) - arg (-(-(↑(5π/6) : ℂ))) = π`
- **What**: Crossing angle at `i` is π (both tangents collinear leftward).
- **How**: `rw [neg_neg, ← ofReal_neg, Complex.arg_ofReal_of_neg (by linarith [Real.pi_pos]), Complex.arg_ofReal_of_nonneg (by positivity)]; ring`.
- **Hypotheses**: None.
- **Uses-from-project**: None (mathlib `Complex.arg_ofReal_*`).
- **Used by**: Winding-number/angle assembly at `i`.
- **Visibility**: public.
- **Lines**: 209–213.

### theorem `arcFTC_limit_target_I`
- **Type**: `: -(↑π * I) / (2 * ↑π * I) = (-1/2 : ℂ)`
- **What**: Limit-target identity: `−(πi)/(2πi) = −1/2`.
- **How**: `field_simp [Real.pi_ne_zero]`.
- **Hypotheses**: None.
- **Uses-from-project**: None.
- **Used by**: ArcFTCHyp construction at `i`.
- **Visibility**: public.
- **Lines**: 218–220.

### theorem `arcFTC_limit_target_rho`
- **Type**: `: -(↑π/3 * I) / (2 * ↑π * I) = (-1/6 : ℂ)`
- **What**: Limit-target identity: `−(πi/3)/(2πi) = −1/6`.
- **How**: `field_simp [Real.pi_ne_zero]; ring`.
- **Hypotheses**: None.
- **Uses-from-project**: None.
- **Used by**: ArcFTCHyp construction at ρ, ρ+1.
- **Visibility**: public.
- **Lines**: 222–225.

### theorem `arcFTC_pv_target_I`
- **Type**: `: 2 * ↑π * I * (-1/2 : ℂ) = -(↑π * I)`
- **What**: Reverse direction of `arcFTC_limit_target_I`.
- **How**: `ring`.
- **Hypotheses**: None.
- **Uses-from-project**: None.
- **Used by**: PV-target conversions.
- **Visibility**: public.
- **Lines**: 228–229.

### theorem `arcFTC_pv_target_rho`
- **Type**: `: 2 * ↑π * I * (-1/6 : ℂ) = -(↑π/3 * I)`
- **What**: Reverse direction of `arcFTC_limit_target_rho`.
- **How**: `ring`.
- **Hypotheses**: None.
- **Uses-from-project**: None.
- **Used by**: PV-target conversions.
- **Visibility**: public.
- **Lines**: 232–233.

### theorem `two_fifths_mem_Ioo`
- **Type**: `: (2:ℝ)/5 ∈ Ioo (0:ℝ) 1`
- **What**: Crossing parameter for `i` lies in `(0,1)`.
- **How**: `constructor <;> norm_num`.
- **Hypotheses**: None.
- **Uses-from-project**: None.
- **Used by**: SingleCrossingData instances at `i`.
- **Visibility**: public.
- **Lines**: 238.

### theorem `one_fifth_mem_Ioo`
- **Type**: `: (1:ℝ)/5 ∈ Ioo (0:ℝ) 1`
- **What**: Crossing parameter for `ρ+1` lies in `(0,1)`.
- **How**: `constructor <;> norm_num`.
- **Hypotheses**: None.
- **Uses-from-project**: None.
- **Used by**: SingleCrossingData instances at `ρ+1`.
- **Visibility**: public.
- **Lines**: 241.

### theorem `three_fifths_mem_Ioo`
- **Type**: `: (3:ℝ)/5 ∈ Ioo (0:ℝ) 1`
- **What**: Crossing parameter for `ρ` lies in `(0,1)`.
- **How**: `constructor <;> norm_num`.
- **Hypotheses**: None.
- **Uses-from-project**: None.
- **Used by**: SingleCrossingData instances at `ρ`.
- **Visibility**: public.
- **Lines**: 244.

## File Summary
- **Total entries**: 24 public theorems (no defs, no private).
- **Key API**: tangent derivatives `fdBoundary_arc_deriv_eq`, `fdBoundary_arc_deriv_at_{one,two,three}_fifths`, `fdBoundary_seg1_deriv`, `fdBoundary_seg4_deriv`; crossing-angle identities `fdBoundary_crossing_angle_at_rho(PlusOne)`, `fdBoundary_angle_at_I_partition`; limit-target identities `arcFTC_limit_target_{I,rho}`, `arcFTC_pv_target_{I,rho}`; parameter memberships `{one,two,three}_fifths_mem_Ioo`.
- **Unused**: `arcFTC_pv_target_I/rho` and `arg_exp_mul_I` may be used only via re-export; nothing is obviously dead.
- **Sorries**: 0.
- **set_options**: None.
- **Long proofs (>10 lines)**: `fdBoundary_seg1_deriv`, `fdBoundary_seg4_deriv`, `arg_neg_left_tangent_rho`.
- **Purpose**: Provides the geometric input data for ArcFTCHyp / SingleCrossingData constructions at the three on-curve points (`i`, `ρ`, `ρ+1`) of the SL₂(ℤ) fundamental domain boundary. Computes tangent directions on the arc and two vertical segments, derives crossing angles at each special point (π at `i`, π/3 at ρ and ρ+1), and packages the FTC limit-target arithmetic identities (`−πi/(2πi) = −1/2`, `−πi/3 / (2πi) = −1/6`) plus elementary parameter-memberships used downstream when instantiating SingleCrossingData for the FD-boundary winding-number computation.
