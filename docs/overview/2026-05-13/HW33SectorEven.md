# Inventory: ForMathlib/HW33SectorEven.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HW33SectorEven.lean`
Namespace: `LeanModularForms`
Section: `noncomputable section`
Imports: `SectorCurve`, `HigherOrderCancel`, `HW33Final`, `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`, `Mathlib.Analysis.SpecialFunctions.Complex.Circle`

### `theorem exp_neg_I_eq_one_of_conditionB`
- **Type**: `(n : ℕ) (α : ℝ) (h_angle : ∃ k : ℤ, ((n - 1 : ℕ) : ℝ) * α = ↑k * (2 * Real.pi)) : Complex.exp (-(↑((n - 1 : ℕ) : ℝ) * α : ℂ) * Complex.I) = 1`
- **What**: Under condition (B) `(n-1)·α ∈ 2π·ℤ`, the complex exponential `exp(-i(n-1)α) = 1`.
- **How**: Extracts integer `k`, rewrites the exponent as `(-k) · (2π · I)` (via `push_cast; ring`), then applies `Complex.exp_int_mul` and `Complex.exp_two_pi_mul_I`, closing with `one_zpow`.
- **Hypotheses**: `n : ℕ`, `α : ℝ`, the integer-multiple condition.
- **Uses from project**: []
- **Used by**: `sector_pv_formula_vanishes_under_conditionB`, `sector_inv_pow_integral_vanishes_under_conditionB`
- **Visibility**: public
- **Lines**: 49-58

### `theorem sector_pv_formula_vanishes_under_conditionB`
- **Type**: `(n : ℕ) (_hn : 2 ≤ n) (α : ℝ) (h_angle : ∃ k : ℤ, ((n - 1 : ℕ) : ℝ) * α = ↑k * (2 * Real.pi)) : ∀ ε > 0, (1 - Complex.exp (-(↑((n - 1 : ℕ) : ℝ) * α : ℂ) * Complex.I)) / ((↑(n - 1) : ℂ) * (↑ε : ℂ) ^ (n - 1)) = 0`
- **What**: HW eq. 3.4 sector-PV formula is identically zero under (B) for every ε > 0.
- **How**: Pointwise: `exp_neg_I_eq_one_of_conditionB` reduces numerator to `1 - 1 = 0`; then `zero_div`.
- **Hypotheses**: `2 ≤ n`, condition (B).
- **Uses from project**: `exp_neg_I_eq_one_of_conditionB`
- **Used by**: `sector_pv_formula_tendsto_zero_under_conditionB`
- **Visibility**: public
- **Lines**: 66-72

### `theorem sector_pv_formula_tendsto_zero_under_conditionB`
- **Type**: `(n : ℕ) (_hn : 2 ≤ n) (α : ℝ) (h_angle) : Tendsto (fun ε : ℝ => (1 - Complex.exp ...)/((↑(n-1):ℂ) * (↑ε:ℂ)^(n-1))) (𝓝[>] 0) (𝓝 0)`
- **What**: Tendsto form of the previous theorem.
- **How**: `Tendsto.congr'` to the constant 0 function via the pointwise vanishing on `self_mem_nhdsWithin`.
- **Hypotheses**: `2 ≤ n`, condition (B).
- **Uses from project**: `sector_pv_formula_vanishes_under_conditionB`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 78-87

### `theorem real_ray_inv_pow_integral`
- **Type**: `(a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (n : ℕ) (hn : 2 ≤ n) : (∫ t in a..b, (1 / t ^ n : ℝ)) = (1 / (n - 1 : ℕ) : ℝ) * (1 / a ^ (n - 1) - 1 / b ^ (n - 1))`
- **What**: Closed form for `∫_a^b 1/t^n dt`.
- **How**: Rewrite as `∫ t^(-n)` via `intervalIntegral.integral_congr`; apply `integral_zpow` using `0 ∉ uIcc a b`; arithmetic finished by `field_simp; ring`.
- **Hypotheses**: `0 < a`, `a ≤ b`, `n ≥ 2`.
- **Uses from project**: []
- **Used by**: `complex_ray_inv_pow_integral`
- **Visibility**: public
- **Lines**: 98-114

### `theorem complex_ray_inv_pow_integral`
- **Type**: `(a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (c : ℂ) (n : ℕ) (hn : 2 ≤ n) : (∫ t in a..b, c / (↑t : ℂ) ^ n) = c * ((1 : ℂ) / (↑(n - 1 : ℕ) : ℂ)) * ((1 / (↑a : ℂ) ^ (n - 1)) - (1 / (↑b : ℂ) ^ (n - 1)))`
- **What**: Multiplies the real ray integral by a complex constant `c`.
- **How**: Convert integrand pointwise on `uIcc a b` to `c · ↑(1/t^n)`, factor `c` out via `integral_const_mul`, push to real integral via `integral_ofReal`, apply `real_ray_inv_pow_integral`, finish with `field_simp`.
- **Hypotheses**: `0 < a`, `a ≤ b`, `n ≥ 2`.
- **Uses from project**: `real_ray_inv_pow_integral`
- **Used by**: `sector_inv_pow_integral_combined`
- **Visibility**: public
- **Lines**: 120-142
- **Notes**: 23-line proof; key lemma `intervalIntegral.integral_ofReal`.

### `theorem arc_inv_pow_integral`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ) (hn : 2 ≤ n) : (∫ t in 0..α, ((↑r : ℂ) * Complex.I * Complex.exp ((↑t : ℂ) * Complex.I)) / ((↑r : ℂ) * Complex.exp ((↑t : ℂ) * Complex.I)) ^ n) = (1 - Complex.exp (-(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I))) / ((↑(n - 1 : ℕ) : ℂ) * (↑r : ℂ) ^ (n - 1))`
- **What**: Closed form for the arc integral `∫_arc dz/z^n` on `t ↦ r·e^{it}, t ∈ [0,α]` (γ_2 piece of HW eq. 3.4).
- **How**: Rewrite integrand using `mul_pow`, factor `r^n = r^{n-1} · r`, expand `exp((t)·I)^n` via `Complex.exp_nat_mul` and `Complex.exp_add`, apply `Complex.exp_neg`, factor constant via `integral_const_mul`, integrate by `integral_exp_mul_complex` (using `(n-1):ℂ ≠ 0` and `I ≠ 0`), finish with `field_simp; ring`.
- **Hypotheses**: `0 < r`, `n ≥ 2`.
- **Uses from project**: []
- **Used by**: `sector_inv_pow_integral_combined`
- **Visibility**: public
- **Lines**: 152-197
- **Notes**: 46-line proof; key lemma `integral_exp_mul_complex`.

### `theorem sector_inv_pow_integral_combined`
- **Type**: `(r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (α : ℝ) (n : ℕ) (hn : 2 ≤ n) : (∫ t in ε..r, (1 : ℂ) / (↑t : ℂ) ^ n) + arc - (∫ t in ε..r, exp(-(n-1)·α·I) / (↑t : ℂ) ^ n) = (1 - exp(...)) / ((n-1)·ε^{n-1})`
- **What**: Combined sector PV explicit formula (HW eq. 3.4).
- **How**: Rewrite the two ray pieces using `complex_ray_inv_pow_integral` and the arc using `arc_inv_pow_integral`; `field_simp; ring` finishes.
- **Hypotheses**: `0 < r`, `0 < ε ≤ r`, `n ≥ 2`.
- **Uses from project**: `complex_ray_inv_pow_integral`, `arc_inv_pow_integral`
- **Used by**: `sector_inv_pow_integral_vanishes_under_conditionB`
- **Visibility**: public
- **Lines**: 211-229

### `theorem sector_inv_pow_integral_vanishes_under_conditionB`
- **Type**: `(r ε α : ℝ) (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r) (n : ℕ) (hn : 2 ≤ n) (h_angle : ∃ k : ℤ, ((n-1):ℝ)*α = k*(2π)) : sector_excised_integral = 0`
- **What**: Full sector PV vanishes for every ε > 0 under (B).
- **How**: Apply `sector_inv_pow_integral_combined`, rewrite the angle factor (`push_cast; ring`), apply `exp_neg_I_eq_one_of_conditionB`, then `simp` finishes since numerator is `1 - 1 = 0`.
- **Hypotheses**: `0 < r`, `0 < ε ≤ r`, `n ≥ 2`, condition (B).
- **Uses from project**: `sector_inv_pow_integral_combined`, `exp_neg_I_eq_one_of_conditionB`
- **Used by**: `sector_inv_pow_integral_tendsto_zero_under_conditionB`
- **Visibility**: public
- **Lines**: 240-255

### `theorem sector_inv_pow_integral_tendsto_zero_under_conditionB`
- **Type**: `(r α : ℝ) (hr : 0 < r) (n : ℕ) (hn : 2 ≤ n) (h_angle) : Tendsto sector_excised_integral (𝓝[>] 0) (𝓝 0)`
- **What**: Tendsto form for the full sector PV under (B).
- **How**: `Tendsto.congr'` to the constant 0 function with eventual equality from `sector_inv_pow_integral_vanishes_under_conditionB` on `Ioo_mem_nhdsGT hr`.
- **Hypotheses**: `0 < r`, `n ≥ 2`, condition (B).
- **Uses from project**: `sector_inv_pow_integral_vanishes_under_conditionB`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 261-276

### `theorem F_line_diff_eq_zero_under_conditionB`
- **Type**: `(s : ℂ) (L_minus L_plus : ℂ) (k : ℕ) (_hk : 2 ≤ k) (hL_minus : L_minus ≠ 0) (hL_plus : L_plus ≠ 0) (h_B : (L_plus/‖L_plus‖)^(k-1) = ((-L_minus)/‖L_minus‖)^(k-1)) (ε : ℝ) : -((↑(k-1):ℂ))⁻¹ * (((s + (ε/‖L_plus‖) • L_plus) - s)^(k-1))⁻¹ = -((↑(k-1):ℂ))⁻¹ * (((s + (ε/‖L_minus‖) • (-L_minus)) - s)^(k-1))⁻¹`
- **What**: F-line difference vanishes (equality of two evaluated F's) under condition (B).
- **How**: `congr 2`; rewrite both `((s + smul) - s)^(k-1)` shifts using `add_sub_cancel_left`, `Complex.real_smul`, `push_cast`, `field_simp`, `mul_pow`; apply `h_B` to identify the two powers.
- **Hypotheses**: `k ≥ 2`, both `L_*` nonzero, condition (B).
- **Uses from project**: []
- **Used by**: `F_curve_diff_tendsto_zero_under_conditionB`
- **Visibility**: public
- **Lines**: 293-317
- **Notes**: 25-line proof; key lemmas `Complex.real_smul`, `mul_pow`.

### `theorem F_curve_diff_tendsto_zero_under_conditionB`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L_minus L_plus : ℂ} {n k : ℕ} (h_flat : IsFlatOfOrder γ t₀ n) (hL_minus hL_plus : ≠0) (h_deriv_right/left) (hL_right/left) (h_s : γ t₀ = s) (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n) (h_B) (t_eps_plus t_eps_minus : ℝ → ℝ) (h_*_to) (h_*_radius) : Tendsto (fun ε => ‖A - B‖) (𝓝[>] 0) (𝓝 0)`
- **What**: Curve-side F-difference tends to 0 under condition (B), general angle.
- **How**: Combine `F_diff_at_tangent_target_tendsto_zero_right/_left` (from `HigherOrderCancel`) via `(...comp h_*_to).add` to get sum of two F-differences tending to 0; rewrite the `‖-L_minus‖` shift back to `‖L_minus‖` via `norm_neg`. Use triangle inequality `‖A − B‖ ≤ ‖B − TR‖ + ‖A − TR‖` with the common tangent target `TR`, identified by `F_line_diff_eq_zero_under_conditionB`. Finishes via `tendsto_of_tendsto_of_tendsto_of_le_of_le'` (squeeze between const 0 and the vanishing sum).
- **Hypotheses**: γ flat of order n at t₀, both tangents nonzero with derivatives, condition (B), exit-time functions with radius behaviour.
- **Uses from project**: `F_diff_at_tangent_target_tendsto_zero_right`, `F_diff_at_tangent_target_tendsto_zero_left` (from `HigherOrderCancel`), `F_line_diff_eq_zero_under_conditionB`, `IsFlatOfOrder`
- **Used by**: `hw_theorem_3_3_under_conditionB_parametric`
- **Visibility**: public
- **Lines**: 338-398
- **Notes**: 61-line proof; key composites `F_diff_at_tangent_target_tendsto_zero_right/_left`, `tendsto_of_tendsto_of_tendsto_of_le_of_le'`.

### `theorem hw_theorem_3_3_under_conditionB_parametric`
- **Type**: Parametric form: given closed γ with corner at t₀, two tangents, condition (B), exit times, per-side smoothness/avoidance/integrability, concludes `Tendsto (fun ε => ∫_a^{t_eps_minus ε} γ'/(γ-s)^k + ∫_{t_eps_plus ε}^b γ'/(γ-s)^k) (𝓝[>] 0) (𝓝 0)`.
- **What**: HW 3.3 parametric form under (B).
- **How**: Term mode: applies `cpv_excised_tendsto_zero_of_F_diff_zero` (from `HigherOrderCancel` or `HW33Final`) with `F_curve_diff_tendsto_zero_under_conditionB` as the F-difference input.
- **Hypotheses**: All needed structural data (closedness, flatness, derivatives, condition (B), exit-time data, per-side smoothness/avoidance/integrability).
- **Uses from project**: `cpv_excised_tendsto_zero_of_F_diff_zero`, `F_curve_diff_tendsto_zero_under_conditionB`, `IsFlatOfOrder`
- **Used by**: `hasCauchyPVOn_singleton_pow_of_conditionB_assembled`
- **Visibility**: public
- **Lines**: 408-448

### `theorem hasCauchyPVOn_singleton_pow_of_conditionB_assembled`
- **Type**: Long: given closed `γ : PiecewiseC1Path x x` with corner crossing at `t₀ ∈ (0,1)`, two tangents `L_*`, condition (B), flatness `n ≥ k`, strict (anti)monotonicity of `‖γ−s‖` on each side, avoidance margins, per-side smoothness/avoidance/integrability and full-curve integrability eventually; concludes `HasCauchyPVOn {s} (fun z => 1/(z-s)^k) γ 0`.
- **What**: Fully assembled `HasCauchyPVOn` form of HW Theorem 3.3 for k-even/general angle under (B).
- **How**: Build the parametric statement via `hw_theorem_3_3_under_conditionB_parametric` plugging `firstExitTimeRight/Left` and their `_tendsto_t₀`/`_radius_eventually` lemmas. Convert via `hasCauchyPVOn_singleton_of_exitTime_excision` and `shape_eventually_of_strict_mono` (from project). Final integrand match uses `intervalIntegral.integral_congr` with a `change` plus `ring` step relating `γ'/(γ-s)^k` to `(1/(γ-s)^k) * γ'`.
- **Hypotheses**: Many (positivity, closedness, flatness, tangent derivatives, condition (B), continuity on side windows, leave conditions, strict monotonicity, avoidance lower bounds, per-side smoothness/avoidance/integrability, eventual full integrability).
- **Uses from project**: `hw_theorem_3_3_under_conditionB_parametric`, `firstExitTimeRight`, `firstExitTimeLeft`, `firstExitTimeRight_tendsto_t₀`, `firstExitTimeRight_radius_eventually`, `firstExitTimeLeft_tendsto_t₀`, `firstExitTimeLeft_radius_eventually`, `hasCauchyPVOn_singleton_of_exitTime_excision`, `shape_eventually_of_strict_mono`, `cpvIntegrandOn`, `HasCauchyPVOn`, `PiecewiseC1Path`, `IsFlatOfOrder`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 465-555
- **Notes**: 91-line proof; long hypothesis list (~30 hypotheses). Key composites: `hasCauchyPVOn_singleton_of_exitTime_excision`, `shape_eventually_of_strict_mono`.

## File Summary
12 declarations (all public theorems). Mirrors `HungerbuhlerWasem/SectorCancellation.lean` structurally — this is in fact its predecessor in namespace `LeanModularForms`, restored elsewhere into `HungerbuhlerWasem` namespace. Provides the explicit-formula vanishing for the k-even case of HW Theorem 3.3 under condition (B), in five layers: (1) algebraic vanishing `exp(-i(n-1)α) = 1`; (2) closed forms for real ray, complex ray, arc integrals; (3) combined sector PV formula and its vanishing/Tendsto; (4) F-line and F-curve difference tendsto-zero; (5) parametric and fully-assembled `HasCauchyPVOn` forms of HW 3.3. No `sorry`, no axioms, no `set_option`. Three proofs exceed 30 lines (`arc_inv_pow_integral`, `F_curve_diff_tendsto_zero_under_conditionB`, `hasCauchyPVOn_singleton_pow_of_conditionB_assembled`). Imports `SectorCurve`, `HigherOrderCancel`, `HW33Final` for the upstream API (`F_diff_at_tangent_target_tendsto_zero_*`, `cpv_excised_tendsto_zero_of_F_diff_zero`, `firstExitTime*`, `hasCauchyPVOn_singleton_of_exitTime_excision`, `shape_eventually_of_strict_mono`, `IsFlatOfOrder`).
