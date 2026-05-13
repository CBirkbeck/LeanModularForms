# Inventory: HungerbuhlerWasem/SectorCancellation.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HungerbuhlerWasem/SectorCancellation.lean`
Namespace: `HungerbuhlerWasem`
Section: `noncomputable section`
Imports: `HungerbuhlerWasem.HigherOrderAsymptotics`, `HungerbuhlerWasem.ExitTimeExcision`, `SectorCurve`, `FlatnessConditions`, `ConnectingArc`, `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`, `Mathlib.Analysis.SpecialFunctions.Complex.Circle`

### `theorem exp_neg_I_eq_one_of_conditionB`
- **Type**: `(n : ℕ) (α : ℝ) (h_angle : ∃ k : ℤ, ((n - 1 : ℕ) : ℝ) * α = ↑k * (2 * Real.pi)) : Complex.exp (-(↑((n - 1 : ℕ) : ℝ) * α : ℂ) * Complex.I) = 1`
- **What**: Under condition (B) i.e. `(n-1)·α ∈ 2π·ℤ`, the complex exponential `exp(-i(n-1)α)` equals one.
- **How**: Extracts the integer `k` from `h_angle`, rewrites the argument as `(-k)·(2π·I)`, then applies `Complex.exp_int_mul` and `Complex.exp_two_pi_mul_I` followed by `one_zpow`.
- **Hypotheses**: `n : ℕ`, `α : ℝ`, and an integer multiple condition `(n - 1)·α = k·2π`.
- **Uses from project**: []
- **Used by**: `sector_pv_formula_vanishes_under_conditionB`, `sector_inv_pow_integral_vanishes_under_conditionB`
- **Visibility**: public
- **Lines**: 60-72
- **Notes**: 13-line proof; pure mathlib.

### `theorem sector_pv_formula_vanishes_under_conditionB`
- **Type**: `(n : ℕ) (_hn : 2 ≤ n) (α : ℝ) (h_angle : ∃ k : ℤ, ((n - 1 : ℕ) : ℝ) * α = ↑k * (2 * Real.pi)) : ∀ ε > (0 : ℝ), (1 - Complex.exp (-(↑((n - 1 : ℕ) : ℝ) * α : ℂ) * Complex.I)) / ((↑(n - 1) : ℂ) * (↑ε : ℂ) ^ (n - 1)) = 0`
- **What**: The HW eq. 3.4 sector-PV explicit formula is identically zero for every ε > 0 under condition (B).
- **How**: For each ε, rewrite via `exp_neg_I_eq_one_of_conditionB` to get numerator `1 - 1`, then `sub_self` and `zero_div`.
- **Hypotheses**: `n : ℕ` with `2 ≤ n`, `α : ℝ`, condition (B).
- **Uses from project**: `exp_neg_I_eq_one_of_conditionB`
- **Used by**: `sector_pv_formula_tendsto_zero_under_conditionB`, `sector_inv_pow_integral_vanishes_under_conditionB` (indirect)
- **Visibility**: public
- **Lines**: 77-84

### `theorem sector_pv_formula_tendsto_zero_under_conditionB`
- **Type**: `(n : ℕ) (_hn : 2 ≤ n) (α : ℝ) (h_angle : ∃ k : ℤ, ((n - 1 : ℕ) : ℝ) * α = ↑k * (2 * Real.pi)) : Tendsto (fun ε : ℝ => (1 - Complex.exp (-(↑((n - 1 : ℕ) : ℝ) * α : ℂ) * Complex.I)) / ((↑(n - 1) : ℂ) * (↑ε : ℂ) ^ (n - 1))) (𝓝[>] 0) (𝓝 0)`
- **What**: Tendsto form: the explicit formula tends to 0 as ε → 0⁺ under (B).
- **How**: Uses `Tendsto.congr'` with constant 0; the eventual equality comes from the pointwise vanishing lemma.
- **Hypotheses**: `2 ≤ n`, condition (B).
- **Uses from project**: `sector_pv_formula_vanishes_under_conditionB`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 88-97

### `theorem real_ray_inv_pow_integral`
- **Type**: `(a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (n : ℕ) (hn : 2 ≤ n) : (∫ t in a..b, (1 / t ^ n : ℝ)) = (1 / (n - 1 : ℕ) : ℝ) * (1 / a ^ (n - 1) - 1 / b ^ (n - 1))`
- **What**: Closed form for real ray integral `∫_a^b 1/t^n dt = (1/(n-1))(1/a^{n-1} - 1/b^{n-1})`.
- **How**: Rewrite as `∫ t^(-n)` via `intervalIntegral.integral_congr`, apply `integral_zpow` (using `0 ∉ uIcc a b`), then arithmetic via `field_simp; ring`.
- **Hypotheses**: `0 < a`, `a ≤ b`, `n ≥ 2`.
- **Uses from project**: []
- **Used by**: `complex_ray_inv_pow_integral`
- **Visibility**: public
- **Lines**: 106-123

### `theorem complex_ray_inv_pow_integral`
- **Type**: `(a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (c : ℂ) (n : ℕ) (hn : 2 ≤ n) : (∫ t in a..b, c / (↑t : ℂ) ^ n) = c * ((1 : ℂ) / (↑(n - 1 : ℕ) : ℂ)) * ((1 / (↑a : ℂ) ^ (n - 1)) - (1 / (↑b : ℂ) ^ (n - 1)))`
- **What**: Multiplies the real ray integral by a complex constant `c`.
- **How**: Convert integrand to `c · ↑(1/t^n)` pointwise on `uIcc a b`, factor out `c` via `integral_const_mul`, push through `integral_ofReal`, then apply `real_ray_inv_pow_integral` and finish with `field_simp`.
- **Hypotheses**: `0 < a`, `a ≤ b`, `n ≥ 2`.
- **Uses from project**: `real_ray_inv_pow_integral`
- **Used by**: `sector_inv_pow_integral_combined`
- **Visibility**: public
- **Lines**: 129-151
- **Notes**: 23-line proof; key lemma is `intervalIntegral.integral_ofReal`.

### `theorem arc_inv_pow_integral`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ) (hn : 2 ≤ n) : (∫ t in (0 : ℝ)..α, ((↑r : ℂ) * Complex.I * Complex.exp ((↑t : ℂ) * Complex.I)) / ((↑r : ℂ) * Complex.exp ((↑t : ℂ) * Complex.I)) ^ n) = (1 - Complex.exp (-(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I))) / ((↑(n - 1 : ℕ) : ℂ) * (↑r : ℂ) ^ (n - 1))`
- **What**: Closed form for arc integral `∫_arc dz/z^n` on `t ↦ r·e^{it}, t ∈ [0,α]` — the γ_2 piece of HW eq. 3.4.
- **How**: Rewrite integrand using `mul_pow`, `Complex.exp_nat_mul`, `Complex.exp_add`, `Complex.exp_neg`, then factor constant via `integral_const_mul` and integrate by `integral_exp_mul_complex`; finishes with `field_simp; ring`.
- **Hypotheses**: `0 < r`, `n ≥ 2`.
- **Uses from project**: []
- **Used by**: `sector_inv_pow_integral_combined`
- **Visibility**: public
- **Lines**: 161-208
- **Notes**: 48-line proof; key lemmas `Complex.exp_nat_mul`, `integral_exp_mul_complex`.

### `theorem sector_inv_pow_integral_combined`
- **Type**: `(r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (α : ℝ) (n : ℕ) (hn : 2 ≤ n) : (∫ t in ε..r, (1 : ℂ) / (↑t : ℂ) ^ n) + (∫ t in 0..α, ((↑r : ℂ) * Complex.I * Complex.exp ((↑t : ℂ) * Complex.I)) / ((↑r : ℂ) * Complex.exp ((↑t : ℂ) * Complex.I)) ^ n) - (∫ t in ε..r, Complex.exp (-(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I)) / (↑t : ℂ) ^ n) = (1 - Complex.exp (-(↑(n - 1 : ℕ) : ℂ) * ((↑α : ℂ) * Complex.I))) / ((↑(n - 1 : ℕ) : ℂ) * (↑ε : ℂ) ^ (n - 1))`
- **What**: Combined sector PV formula (HW eq. 3.4): summing two ray pieces + arc gives the closed expression.
- **How**: Rewrite each ray with `complex_ray_inv_pow_integral` and the arc with `arc_inv_pow_integral`, then `field_simp; ring`.
- **Hypotheses**: `0 < r`, `0 < ε ≤ r`, `n ≥ 2`.
- **Uses from project**: `complex_ray_inv_pow_integral`, `arc_inv_pow_integral`
- **Used by**: `sector_inv_pow_integral_vanishes_under_conditionB`
- **Visibility**: public
- **Lines**: 218-236

### `theorem sector_inv_pow_integral_vanishes_under_conditionB`
- **Type**: `(r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r) (α : ℝ) (n : ℕ) (hn : 2 ≤ n) (h_angle : ∃ k, ((n-1):ℝ)*α = k*(2π)) : ...  = 0` (full sector excised integral equals zero)
- **What**: Full sector PV is identically zero for every ε > 0 under condition (B).
- **How**: Apply `sector_inv_pow_integral_combined`, swap an angle expression, then apply `exp_neg_I_eq_one_of_conditionB` to make the numerator zero; `simp` closes.
- **Hypotheses**: `0 < r`, `0 < ε ≤ r`, `n ≥ 2`, condition (B).
- **Uses from project**: `sector_inv_pow_integral_combined`, `exp_neg_I_eq_one_of_conditionB`
- **Used by**: `sector_inv_pow_integral_tendsto_zero_under_conditionB`
- **Visibility**: public
- **Lines**: 242-259

### `theorem sector_inv_pow_integral_tendsto_zero_under_conditionB`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ) (hn : 2 ≤ n) (h_angle : ∃ k : ℤ, ((n-1):ℝ)*α = k*(2π)) : Tendsto (fun ε => sector integral) (𝓝[>] 0) (𝓝 0)`
- **What**: Tendsto version of the sector PV vanishing.
- **How**: `Tendsto.congr'` with the constant 0 function; eventual equality from `sector_inv_pow_integral_vanishes_under_conditionB`.
- **Hypotheses**: `0 < r`, `n ≥ 2`, condition (B).
- **Uses from project**: `sector_inv_pow_integral_vanishes_under_conditionB`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 264-279

### `theorem F_line_diff_eq_zero_under_conditionB`
- **Type**: `(s : ℂ) (L_minus L_plus : ℂ) (k : ℕ) (_hk : 2 ≤ k) (hL_minus : L_minus ≠ 0) (hL_plus : L_plus ≠ 0) (h_B : (L_plus/‖L_plus‖)^(k-1) = ((-L_minus)/‖L_minus‖)^(k-1)) (ε : ℝ) : -((↑(k-1):ℂ))⁻¹ * (((s+(ε/‖L_plus‖) • L_plus)-s)^(k-1))⁻¹ = -((↑(k-1):ℂ))⁻¹ * (((s+(ε/‖L_minus‖) • (-L_minus))-s)^(k-1))⁻¹`
- **What**: Under condition (B), the antiderivative `F(z) = -1/((k-1)(z-s)^{k-1})` evaluated at the two chord targets coincides.
- **How**: `congr 2` on the outer factors; rewrite both smul-shifts using `Complex.real_smul` and `field_simp`, then power both shifts via `add_sub_cancel_left` and `mul_pow`, then apply `h_B`.
- **Hypotheses**: `k ≥ 2`, both tangent directions nonzero, condition (B).
- **Uses from project**: []
- **Used by**: `F_curve_diff_tendsto_zero_under_conditionB`
- **Visibility**: public
- **Lines**: 294-322
- **Notes**: 29-line proof; key lemmas `Complex.real_smul`, `add_sub_cancel_left`, `mul_pow`.

### `theorem F_curve_diff_tendsto_zero_under_conditionB`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s L_minus L_plus : ℂ} {n k : ℕ} (h_flat : IsFlatOfOrder γ t₀ n) (hL_minus hL_plus : ≠0) (h_deriv_right/left) (hL_right/left tendsto) (h_s : γ t₀ = s) (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n) (h_B) (t_eps_plus t_eps_minus : ℝ → ℝ) (h_*_to) (h_*_radius) : Tendsto (fun ε => ‖A - B‖) (𝓝[>] 0) (𝓝 0)`
- **What**: Combined curve F-difference tends to 0 under condition (B): the two-sided F evaluations on the curve close up.
- **How**: Triangle inequality `‖A − B‖ ≤ ‖B − TR‖ + ‖A − TR‖` with common tangent target TR. Both summands tend to 0 by `F_diff_at_tangent_target_tendsto_zero_right/_left` (from project); the two side targets are equal by `F_line_diff_eq_zero_under_conditionB`. Uses `tendsto_of_tendsto_of_tendsto_of_le_of_le'` to compare `‖A − B‖` to the (vanishing) sum bound.
- **Hypotheses**: γ flat of order n, tangents nonzero with one-sided derivatives, condition (B), exit-time functions with radius behaviour.
- **Uses from project**: `F_diff_at_tangent_target_tendsto_zero_right`, `F_diff_at_tangent_target_tendsto_zero_left` (from `HigherOrderAsymptotics`), `F_line_diff_eq_zero_under_conditionB`, `IsFlatOfOrder` (from `FlatnessConditions`)
- **Used by**: `hw_theorem_3_3_under_conditionB_parametric`
- **Visibility**: public
- **Lines**: 339-399
- **Notes**: 61-line proof; key lemmas `F_diff_at_tangent_target_tendsto_zero_right`/`_left`, `norm_sub_le`, `tendsto_of_tendsto_of_tendsto_of_le_of_le'`.

### `theorem hw_theorem_3_3_under_conditionB_parametric`
- **Type**: Long: parametric form. Given closed γ with single crossing at `t₀`, two tangent directions `L_minus, L_plus`, condition (B), exit times and per-side smoothness/avoidance/integrability data, concludes `Tendsto (fun ε => ∫_a^{t_eps_minus ε} + ∫_{t_eps_plus ε}^b) (𝓝[>] 0) (𝓝 0)`.
- **What**: HW Theorem 3.3 parametric statement: symmetric-excision PV vanishes under (B).
- **How**: Applies `cpv_excised_tendsto_zero_of_F_diff_zero` (from project) with all the per-side data and the F-difference tendsto from `F_curve_diff_tendsto_zero_under_conditionB`.
- **Hypotheses**: γ flat of order n at t₀, both tangents nonzero with derivatives, condition (B), exit-time data, smoothness/avoidance/integrability on each side.
- **Uses from project**: `cpv_excised_tendsto_zero_of_F_diff_zero` (from `HigherOrderAsymptotics` or related), `F_curve_diff_tendsto_zero_under_conditionB`, `IsFlatOfOrder`
- **Used by**: `hasCauchyPVOn_singleton_pow_of_conditionB_assembled`
- **Visibility**: public
- **Lines**: 409-449

### `theorem hasCauchyPVOn_singleton_pow_of_conditionB_assembled`
- **Type**: Long. Given closed `γ : PiecewiseC1Path x x` with corner crossing at `t₀ ∈ (0,1)`, two tangents, condition (B), flatness `n ≥ k`, strict (anti)monotonicity of `‖γ − s‖` on each side, avoidance margins, plus per-side smoothness/avoidance/integrability and a full-curve integrability eventually; concludes `HasCauchyPVOn {s} (fun z => 1/(z-s)^k) γ 0`.
- **What**: Fully assembled `HasCauchyPVOn` form of HW Theorem 3.3 for the general k under (B).
- **How**: Builds the parametric statement via `hw_theorem_3_3_under_conditionB_parametric` plugged with `firstExitTimeRight/Left` and their `_tendsto_t₀`/`_radius_eventually` lemmas, then converts to `HasCauchyPVOn` via `hasCauchyPVOn_singleton_of_exitTime_excision` and `shape_eventually_of_strict_mono`. Final integrand reconciliation uses `intervalIntegral.integral_congr` and a `ring` step matching `(1/(z-s)^k) * γ'(t)` to `γ'(t)/(γ t − s)^k`.
- **Hypotheses**: Many (positivity, closedness, flatness, derivative/tangent data, condition (B), continuity on side windows, avoidance/leave conditions, strict monotonicity, avoidance lower bounds, per-side smoothness/avoidance/integrability, eventual full integrability).
- **Uses from project**: `hw_theorem_3_3_under_conditionB_parametric`, `LeanModularForms.firstExitTimeRight`, `LeanModularForms.firstExitTimeLeft`, `LeanModularForms.firstExitTimeRight_tendsto_t₀`, `LeanModularForms.firstExitTimeRight_radius_eventually`, `LeanModularForms.firstExitTimeLeft_tendsto_t₀`, `LeanModularForms.firstExitTimeLeft_radius_eventually`, `hasCauchyPVOn_singleton_of_exitTime_excision`, `shape_eventually_of_strict_mono`, `cpvIntegrandOn`, `HasCauchyPVOn`, `PiecewiseC1Path`, `IsFlatOfOrder`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 462-558
- **Notes**: 97-line proof; very long hypothesis list (~63 hypotheses). Key combiners: `hasCauchyPVOn_singleton_of_exitTime_excision`, `shape_eventually_of_strict_mono`.

## File Summary
12 declarations (all `theorem`, all public). The file restores the deleted `HW33SectorEven.lean` content under `HungerbuhlerWasem` namespace, providing the sector-even/condition-(B) analog of HW Theorem 3.3. Structure: (1) algebraic vanishing of `exp(-i(n-1)α)` under (B); (2) closed-form computations for real ray, complex ray, and arc integrals; (3) combined sector formula and its vanishing/Tendsto forms; (4) F-line and F-curve difference tendsto-zero results; (5) parametric and fully-assembled `HasCauchyPVOn` forms of HW Theorem 3.3. No `sorry`, no axioms, no `set_option`. Three proofs exceed 30 lines (`arc_inv_pow_integral`, `F_curve_diff_tendsto_zero_under_conditionB`, `hasCauchyPVOn_singleton_pow_of_conditionB_assembled`). The headline theorems mirror the deleted-file API (this file is the namespace-renamed replacement of `HW33SectorEven.lean` and depends on the project's exit-time, higher-order asymptotics, sector-curve, flatness, and connecting-arc modules).
