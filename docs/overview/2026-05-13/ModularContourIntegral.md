# ModularContourIntegral.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ModularContourIntegral.lean`
Lines: 325

## Imports
- `LeanModularForms.ForMathlib.LogDerivModularForm`
- `LeanModularForms.ForMathlib.FDBoundaryPath`
- `LeanModularForms.ForMathlib.PiecewiseContourIntegral`
- `LeanModularForms.ForMathlib.ModularInvariance`

---

### `theorem deriv_fdBoundaryFun_seg1`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t < 1/5) → deriv (fdBoundaryFun H) t = -(5 * (↑H - ↑(Real.sqrt 3) / 2)) * I`
- **What**: On seg1 (right vertical, parameter `t < 1/5`), the derivative of the fundamental-domain boundary parameterization is constant `-5(H - √3/2)·i`.
- **How**: Sets up `EventuallyEq` of `fdBoundaryFun H` with the affine form `(1/2 + H·i) + (-5(H-√3/2)·i)·s` on `Iio (1/5)`; uses `EventuallyEq.deriv_eq` plus `Complex.ofRealCLM.hasDerivAt.const_mul _.const_add _`.
- **Hypotheses**: `t < 1/5`.
- **Uses from project**: `fdBoundaryFun` (from `FDBoundaryPath`).
- **Used by**: `deriv_seg4_eq_neg_seg1`.
- **Visibility**: public
- **Lines**: 73-82
- **Notes**: none.

### `theorem deriv_fdBoundaryFun_seg4`
- **Type**: `(H : ℝ) (t : ℝ) (ht3 : 3/5 < t) (ht4 : t < 4/5) → deriv (fdBoundaryFun H) t = (5 * (↑H - ↑(Real.sqrt 3) / 2)) * I`
- **What**: On seg4 (left vertical, `3/5 < t < 4/5`), the derivative is `+5(H-√3/2)·i` — opposite sign to seg1.
- **How**: Sets up `EventuallyEq` on `Ioo (3/5) (4/5)` with affine form; case-checks `split_ifs` on the piecewise definition (4 cases dismissed by `linarith`, last case is `ring`); applies `EventuallyEq.deriv_eq` and ofReal derivative composition.
- **Hypotheses**: `3/5 < t < 4/5`.
- **Uses from project**: `fdBoundaryFun`.
- **Used by**: `deriv_seg4_eq_neg_seg1`.
- **Visibility**: public
- **Lines**: 85-101
- **Notes**: >10 lines.

### `theorem deriv_seg4_eq_neg_seg1`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ∈ Ioo 0 (1/5)) → deriv (fdBoundaryFun H) (4/5 - t) = -(deriv (fdBoundaryFun H) t)`
- **What**: Derivative reflection: the seg4 derivative at `4/5 - t` is the negative of the seg1 derivative at `t`.
- **How**: Rewrites both sides via `deriv_fdBoundaryFun_seg1 H t ht.2` and `deriv_fdBoundaryFun_seg4 H (4/5 - t) (by linarith) (by linarith)`; closes with `ring`.
- **Hypotheses**: `t ∈ Ioo 0 (1/5)`.
- **Uses from project**: `deriv_fdBoundaryFun_seg1`, `deriv_fdBoundaryFun_seg4`, `fdBoundaryFun`.
- **Used by**: `logDeriv_integrand_seg4_neg_seg1`.
- **Visibility**: public
- **Lines**: 105-109
- **Notes**: none.

### `theorem fdBoundaryFun_seg4_eq_seg1_sub_one`
- **Type**: `(H : ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1/5) → fdBoundaryFun H (4/5 - t) = fdBoundaryFun H t - 1`
- **What**: T-translation identity: on `(0, 1/5)`, the seg4 point at `4/5 - t` equals the seg1 point at `t` minus 1.
- **How**: Unfolds `fdBoundaryFun`, discharges all five `if` branches with linear arithmetic (one is `le_of_lt ht1`, four are `linarith` contradictions), then `push_cast; ring`.
- **Hypotheses**: `0 ≤ t < 1/5`.
- **Uses from project**: `fdBoundaryFun`.
- **Used by**: `logDeriv_integrand_seg4_neg_seg1`.
- **Visibility**: public
- **Lines**: 115-125
- **Notes**: >10 lines.

### `theorem fdBoundaryFun_seg4_boundary_translate`
- **Type**: `(H : ℝ) → fdBoundaryFun H (3/5) = fdBoundaryFun H (1/5) - 1`
- **What**: Boundary case of T-translation at `t = 1/5`: `ρ = (ρ + 1) - 1`.
- **How**: Substitutes `fdBoundaryFun_at_three_fifths` and `fdBoundaryFun_at_one_fifth`; unfolds `ellipticPointRho`, `ellipticPointRho'`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`, `UpperHalfPlane.coe_mk`; `ring`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_three_fifths`, `fdBoundaryFun_at_one_fifth`, `ellipticPointRho`, `ellipticPointRho'`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 128-134
- **Notes**: none.

### `theorem logDeriv_integrand_seg4_neg_seg1`
- **Type**: `{f : ℂ → ℂ} (hf_periodic : ∀ z, f (z + 1) = f z) (H : ℝ) (t : ℝ) (ht : t ∈ Ioo 0 (1/5)) → logDeriv f (fdBoundaryFun H (4/5 - t)) * deriv (fdBoundaryFun H) (4/5 - t) = -(logDeriv f (fdBoundaryFun H t) * deriv (fdBoundaryFun H) t)`
- **What**: T-cancellation of `logDeriv f` integrand: for a 1-periodic `f`, the seg4 integrand at `4/5 - t` is the negative of the seg1 integrand at `t`.
- **How**: Uses T-translation `fdBoundaryFun_seg4_eq_seg1_sub_one`; `logDeriv f` is 1-periodic by `logDeriv_periodic` (applied to `f`'s 1-periodicity), so `logDeriv f (z - 1 + 1) = logDeriv f z` gives `h_period`; combines with `deriv_seg4_eq_neg_seg1` and `ring`.
- **Hypotheses**: `f(z+1) = f(z)`, `t ∈ Ioo 0 (1/5)`.
- **Uses from project**: `fdBoundaryFun_seg4_eq_seg1_sub_one`, `deriv_seg4_eq_neg_seg1`, `fdBoundaryFun`, `logDeriv`, `logDeriv_periodic` (from `LogDerivModularForm`).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 139-154
- **Notes**: >10 lines.

### `theorem neg_inv_exp_mul_I`
- **Type**: `(θ : ℂ) → -(1 : ℂ) / exp (θ * I) = exp ((↑Real.pi - θ) * I)`
- **What**: Identity `-1/e^{iθ} = e^{i(π - θ)}`, used for the S-involution on the unit circle.
- **How**: Rewrites `-1/exp(θ·i) = -(exp(θ·i))⁻¹ = -exp(-θ·i)`; uses `exp_pi_mul_I` to write `-1 = exp(π·i)`; combines exponentials via `exp_add`; finishes with `congr 1; ring`.
- **Hypotheses**: none.
- **Uses from project**: none.
- **Used by**: `fdBoundaryFun_S_arc`, `fdBoundaryFun_S_arc'`.
- **Visibility**: public
- **Lines**: 159-167
- **Notes**: none.

### `theorem fdBoundaryFun_S_arc`
- **Type**: `(H : ℝ) (t : ℝ) (ht1 : 1/5 < t) (ht2 : t < 2/5) → -(1 : ℂ) / fdBoundaryFun H t = fdBoundaryFun H (4/5 - t)`
- **What**: S-involution on the first half of the arc: for `t ∈ (1/5, 2/5)` (seg2), the S-image `-1/γ(t)` lies on seg3 at parameter `4/5 - t`.
- **How**: Unfolds `fdBoundaryFun` for seg2 and seg3 (via `split_ifs` and `linarith`) to get `exp` parameterizations; applies `neg_inv_exp_mul_I` to flip; `congr 1; push_cast; ring` matches the angle expressions.
- **Hypotheses**: `1/5 < t < 2/5`.
- **Uses from project**: `fdBoundaryFun`, `neg_inv_exp_mul_I`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 171-188
- **Notes**: >10 lines.

### `theorem fdBoundaryFun_S_arc'`
- **Type**: `(H : ℝ) (t : ℝ) (ht1 : 2/5 < t) (ht2 : t < 3/5) → -(1 : ℂ) / fdBoundaryFun H t = fdBoundaryFun H (4/5 - t)`
- **What**: S-involution on the second half of the arc: for `t ∈ (2/5, 3/5)` (seg3), the S-image lies on seg2 at parameter `4/5 - t`.
- **How**: Symmetric to `fdBoundaryFun_S_arc`: unfolds `fdBoundaryFun` for seg3 and seg2, applies `neg_inv_exp_mul_I`, then `congr 1; push_cast; ring`.
- **Hypotheses**: `2/5 < t < 3/5`.
- **Uses from project**: `fdBoundaryFun`, `neg_inv_exp_mul_I`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 192-210
- **Notes**: >10 lines.

### `theorem ellipticPointRho_eq_exp`
- **Type**: `(ellipticPointRho : ℂ) = exp (↑(2 * Real.pi / 3) * I)`
- **What**: The elliptic point `ρ` is the unit-circle point at angle `2π/3`.
- **How**: Rewrites `2π/3 = π - π/3`, distributes via `ofReal_sub` and `sub_mul`; uses `exp_pi_mul_I` and `exp_add` to split off the `-1` factor; collapses with `exp_mul_I`, `ofReal_cos`, `ofReal_sin`, `Real.cos_neg`, `Real.sin_neg`, `Real.cos_pi_div_three`, `Real.sin_pi_div_three`; finally unfolds `ellipticPointRho`/`ellipticPointRho'` and `push_cast; ring`.
- **Hypotheses**: none.
- **Uses from project**: `ellipticPointRho`, `ellipticPointRho'`.
- **Used by**: `log_ellipticPointRho`.
- **Visibility**: public
- **Lines**: 215-230
- **Notes**: >10 lines.

### `theorem ellipticPointRhoPlusOne_eq_exp`
- **Type**: `(ellipticPointRhoPlusOne : ℂ) = exp (↑(Real.pi / 3) * I)`
- **What**: `ρ + 1` is the unit-circle point at angle `π/3`.
- **How**: `exp_mul_I`, `ofReal_cos`, `ofReal_sin`, `Real.cos_pi_div_three`, `Real.sin_pi_div_three`; unfold `ellipticPointRhoPlusOne`/`ellipticPointRhoPlusOne'`; `push_cast; ring`.
- **Hypotheses**: none.
- **Uses from project**: `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`.
- **Used by**: `log_ellipticPointRhoPlusOne`.
- **Visibility**: public
- **Lines**: 233-239
- **Notes**: none.

### `theorem log_ellipticPointRho`
- **Type**: `Complex.log ellipticPointRho = ↑(2 * Real.pi / 3) * I`
- **What**: Principal-branch logarithm of `ρ` is `2πi/3`.
- **How**: Substitute `ellipticPointRho_eq_exp` and apply `Complex.log_exp`; the imaginary-part bounds `Im(2π/3·i) ∈ (-π, π]` come from `linarith [Real.pi_pos]`.
- **Hypotheses**: none.
- **Uses from project**: `ellipticPointRho_eq_exp`, `ellipticPointRho`.
- **Used by**: `arc_angle_computation`.
- **Visibility**: public
- **Lines**: 242-249
- **Notes**: none.

### `theorem log_ellipticPointRhoPlusOne`
- **Type**: `Complex.log ellipticPointRhoPlusOne = ↑(Real.pi / 3) * I`
- **What**: Principal-branch logarithm of `ρ + 1` is `πi/3`.
- **How**: Substitute `ellipticPointRhoPlusOne_eq_exp` and apply `Complex.log_exp`; imaginary-part bounds again from `linarith [Real.pi_pos]`.
- **Hypotheses**: none.
- **Uses from project**: `ellipticPointRhoPlusOne_eq_exp`, `ellipticPointRhoPlusOne`.
- **Used by**: `arc_angle_computation`.
- **Visibility**: public
- **Lines**: 252-259
- **Notes**: none.

### `theorem arc_angle_computation`
- **Type**: `Complex.log ellipticPointRho - Complex.log ellipticPointRhoPlusOne = ↑Real.pi / 3 * I`
- **What**: The angle subtended by the arc from `ρ + 1` to `ρ` (counterclockwise on the unit circle) is `π/3`.
- **How**: Rewrites with `log_ellipticPointRho` and `log_ellipticPointRhoPlusOne`, then `push_cast; ring`.
- **Hypotheses**: none.
- **Uses from project**: `log_ellipticPointRho`, `log_ellipticPointRhoPlusOne`, `ellipticPointRho`, `ellipticPointRhoPlusOne`.
- **Used by**: `arc_integral_k_over_z`.
- **Visibility**: public
- **Lines**: 265-269
- **Notes**: none.

### `theorem arc_integral_k_over_z`
- **Type**: `(k : ℤ) → (k : ℂ) * (Complex.log ellipticPointRho - Complex.log ellipticPointRhoPlusOne) = ↑k * ↑Real.pi / 3 * I`
- **What**: The contour integral of `k/z` along the arc from `ρ+1` to `ρ` equals `kπi/3`.
- **How**: Rewrites with `arc_angle_computation`, then `ring`.
- **Hypotheses**: none.
- **Uses from project**: `arc_angle_computation`, `ellipticPointRho`, `ellipticPointRhoPlusOne`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 272-276
- **Notes**: none.

### `theorem arc_contribution_eq_neg_k_over_12`
- **Type**: `(k : ℤ) → -(↑k * ↑Real.pi * I / 6) = -(2 * ↑Real.pi * I * ((k : ℂ) / 12))`
- **What**: The arc contribution `-kπi/6` rewrites to `-(2πi)·(k/12)` — extracts the `2πi` factor expected on the modular side.
- **How**: `ring`.
- **Hypotheses**: none.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 282-283
- **Notes**: trivial.

### `theorem modular_side_combination`
- **Type**: `(k : ℤ) (ord_inf : ℂ) → -(2 * ↑Real.pi * I * ((k : ℂ) / 12)) + (2 * ↑Real.pi * I * ord_inf) = -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - ord_inf))`
- **What**: Combines the arc contribution `-(2πi)(k/12)` and horizontal `2πi · ord_∞` into the full modular-side expression `-(2πi)(k/12 - ord_∞)`.
- **How**: `ring`.
- **Hypotheses**: none.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 287-289
- **Notes**: trivial.

### `theorem modular_side_cancel_two_pi_I`
- **Type**: `{L : ℂ} (k : ℤ) (ord_inf : ℂ) (h : 2 * ↑Real.pi * I * L = -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - ord_inf))) → L = -((k : ℂ) / 12 - ord_inf)`
- **What**: Divide both sides by `2πi` to recover the bare modular-side expression `L = -(k/12 - ord_∞)`.
- **How**: Show `2πi ≠ 0` via `Real.pi_ne_zero` and `I_ne_zero`; rewrite `-(2πi · X)` as `2πi · (-X)`; apply `mul_left_cancel₀`.
- **Hypotheses**: contour integral equation.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 293-301
- **Notes**: none.

### `theorem modular_side_rearrange`
- **Type**: `(k : ℤ) (ord_inf weighted_sum : ℂ) (h : weighted_sum = -((k : ℂ) / 12 - ord_inf)) → ord_inf + (-weighted_sum) = (k : ℂ) / 12`
- **What**: From `wt_sum = -(k/12 - ord_∞)` derive the textbook form `ord_∞ + (-wt_sum) = k/12`.
- **How**: `rw [h]; ring`.
- **Hypotheses**: shape of `weighted_sum`.
- **Uses from project**: none.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 305-309
- **Notes**: trivial.

### `theorem fdBoundaryFun_seg5_constant_height`
- **Type**: `(H : ℝ) (t : ℝ) (ht : 4/5 < t) → (fdBoundaryFun H t).im = H`
- **What**: Seg5 (top horizontal) has constant imaginary part `H`.
- **How**: Direct delegation to `fdBoundaryFun_seg5_im H t ht`.
- **Hypotheses**: `4/5 < t`.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_seg5_im` (from `FDBoundaryPath`).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 314-316
- **Notes**: none.

### `theorem fdBoundaryFun_seg5_one_period`
- **Type**: `(H : ℝ) → fdBoundaryFun H 1 - fdBoundaryFun H (4/5) = (1 : ℂ)`
- **What**: Seg5 covers one full T-period (length `1`) horizontally.
- **How**: Rewrites endpoints via `fdBoundaryFun_at_one` and `fdBoundaryFun_at_four_fifths`; `simp [fdStart]; ring`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryFun`, `fdBoundaryFun_at_one`, `fdBoundaryFun_at_four_fifths`, `fdStart` (from `FDBoundaryPath`).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 319-323
- **Notes**: none.

---

## File Summary
`ModularContourIntegral.lean` (325 lines, 0 sorries, 0 axioms) provides the three geometric building blocks for the contour-integral derivation of the valence formula along the fundamental-domain boundary `∂F`:
1. **T-cancellation (verticals)**: derivative reflection `deriv_seg4_eq_neg_seg1`, T-translation `fdBoundaryFun_seg4_eq_seg1_sub_one`, and integrand cancellation `logDeriv_integrand_seg4_neg_seg1` show the seg1/seg4 contributions cancel.
2. **S-arc contribution (arcs)**: S-involution identities `fdBoundaryFun_S_arc` and `fdBoundaryFun_S_arc'` plus arc-angle `arc_angle_computation` (`log ρ - log(ρ+1) = πi/3`) give the arc integral of `k/z` as `kπi/3`.
3. **Algebraic assembly**: `arc_contribution_eq_neg_k_over_12`, `modular_side_combination`, `modular_side_cancel_two_pi_I`, `modular_side_rearrange` assemble the arc and horizontal pieces into the full modular side `-(2πi)(k/12 - ord_∞)` and rearrange to the textbook form `ord_∞ + (-Σ ord(p)) = k/12`.
Also includes seg5 height/period geometry (`fdBoundaryFun_seg5_constant_height`, `fdBoundaryFun_seg5_one_period`) and elliptic-point exponential identities (`ellipticPointRho_eq_exp`, `ellipticPointRhoPlusOne_eq_exp`, `log_ellipticPointRho`, `log_ellipticPointRhoPlusOne`). Twenty-two public theorems total.
