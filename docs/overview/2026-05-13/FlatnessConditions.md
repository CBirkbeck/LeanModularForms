# FlatnessConditions.lean Inventory

### `def orthogonalProjectionComplex`
- **Type**: `(w L : ℂ) → ℂ`
- **What**: Orthogonal projection of `w` onto the real line spanned by `L` in `ℂ` viewed as `ℝ²`; computes `(Re(w * conj L) / ‖L‖²) • L`.
- **How**: Direct definitional expression as a scalar multiple of `L`.
- **Hypotheses**: None (definition).
- **Uses from project**: []
- **Used by**: `tangentDeviation`, `orthogonalProjectionComplex_zero_left`, `tangentDeviation_zero_left`, `tangentDeviation_zero_right`, `orthogonalProjectionComplex_smul`, `orthogonalProjectionComplex_real_smul_self`, `tangentDeviation_real_smul_self`, `tangentDeviation_add`, `norm_tangentDeviation_le`.
- **Visibility**: public
- **Lines**: 48-49
- **Notes**: none

### `def tangentDeviation`
- **Type**: `(w L : ℂ) → ℂ`
- **What**: Component of `w` orthogonal to direction `L`, defined as `w − orthogonalProjectionComplex w L`.
- **How**: Algebraic subtraction.
- **Hypotheses**: None.
- **Uses from project**: [`orthogonalProjectionComplex`]
- **Used by**: `tangentDeviation_zero_left`, `tangentDeviation_zero_right`, `tangentDeviation_real_smul_self`, `tangentDeviation_add`, `norm_tangentDeviation_le`, `IsFlatOfOrder`, downstream conditions.
- **Visibility**: public
- **Lines**: 52-53
- **Notes**: none

### `theorem orthogonalProjectionComplex_zero_left`
- **Type**: `(L : ℂ) → orthogonalProjectionComplex 0 L = 0`
- **What**: Projecting `0` onto any `L` gives `0`.
- **How**: `simp [orthogonalProjectionComplex]`.
- **Hypotheses**: None.
- **Uses from project**: [`orthogonalProjectionComplex`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 55-57
- **Notes**: none

### `theorem tangentDeviation_zero_left`
- **Type**: `(L : ℂ) → tangentDeviation 0 L = 0`
- **What**: Tangent deviation of `0` from any direction is `0`.
- **How**: `simp [tangentDeviation, orthogonalProjectionComplex]`.
- **Hypotheses**: None.
- **Uses from project**: [`tangentDeviation`, `orthogonalProjectionComplex`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 59-61
- **Notes**: none

### `theorem tangentDeviation_zero_right`
- **Type**: `(w : ℂ) → tangentDeviation w 0 = w`
- **What**: Tangent deviation against the zero direction is identity.
- **How**: `simp [tangentDeviation, orthogonalProjectionComplex]`.
- **Hypotheses**: None.
- **Uses from project**: [`tangentDeviation`, `orthogonalProjectionComplex`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 63-65
- **Notes**: none

### `theorem orthogonalProjectionComplex_smul`
- **Type**: `(w L : ℂ) → ∃ c : ℝ, orthogonalProjectionComplex w L = c • L`
- **What**: The projection is a real scalar multiple of the direction `L`.
- **How**: Exhibit `c := (w * conj L).re / Complex.normSq L`, conclude by `rfl`.
- **Hypotheses**: None.
- **Uses from project**: [`orthogonalProjectionComplex`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 68-70
- **Notes**: none

### `theorem orthogonalProjectionComplex_real_smul_self`
- **Type**: `(c : ℝ) (L : ℂ) (hL : L ≠ 0) → orthogonalProjectionComplex (c • L) L = c • L`
- **What**: Projecting `c • L` onto `L` returns `c • L` itself.
- **How**: Compute the coefficient as `c` via `Complex.mul_conj` and `mul_div_cancel_of_imp`.
- **Hypotheses**: `L ≠ 0`.
- **Uses from project**: [`orthogonalProjectionComplex`]
- **Used by**: `tangentDeviation_real_smul_self`
- **Visibility**: public
- **Lines**: 73-81
- **Notes**: none

### `theorem tangentDeviation_real_smul_self`
- **Type**: `(c : ℝ) (L : ℂ) (hL : L ≠ 0) → tangentDeviation (c • L) L = 0`
- **What**: A real scalar multiple of `L` has zero tangent deviation against `L`.
- **How**: Rewrite using `orthogonalProjectionComplex_real_smul_self` then `sub_self`.
- **Hypotheses**: `L ≠ 0`.
- **Uses from project**: [`tangentDeviation`, `orthogonalProjectionComplex_real_smul_self`]
- **Used by**: `tangentDeviation_isLittleO_right`, `tangentDeviation_isLittleO_left`
- **Visibility**: public
- **Lines**: 84-86
- **Notes**: none

### `theorem tangentDeviation_add`
- **Type**: `(w₁ w₂ L : ℂ) → tangentDeviation (w₁ + w₂) L = tangentDeviation w₁ L + tangentDeviation w₂ L`
- **What**: `tangentDeviation` is additive in the first argument.
- **How**: Unfold definitions, then `module`.
- **Hypotheses**: None.
- **Uses from project**: [`tangentDeviation`, `orthogonalProjectionComplex`]
- **Used by**: `tangentDeviation_isLittleO_right`, `tangentDeviation_isLittleO_left`
- **Visibility**: public
- **Lines**: 89-92
- **Notes**: none

### `theorem norm_tangentDeviation_le`
- **Type**: `(w L : ℂ) (hL : L ≠ 0) → ‖tangentDeviation w L‖ ≤ 2 * ‖w‖`
- **What**: Norm of tangent deviation is bounded by `2‖w‖`.
- **How** (~20 lines): Triangle inequality via `norm_sub_le`, then `‖proj‖ ≤ ‖w‖` via Cauchy–Schwarz; the projection norm bound uses `Complex.abs_re_le_norm`, `Complex.norm_mul_self_eq_normSq` and `div_self` of `Complex.normSq L`.
- **Hypotheses**: `L ≠ 0`.
- **Uses from project**: [`tangentDeviation`, `orthogonalProjectionComplex`]
- **Used by**: `isFlatOfOrder_zero`, `tangentDeviation_isLittleO_right`, `tangentDeviation_isLittleO_left`
- **Visibility**: public
- **Lines**: 95-114
- **Notes**: none

### `structure IsFlatOfOrder`
- **Type**: `(γ : ℝ → ℂ) (t₀ : ℝ) (n : ℕ) : Prop`
- **What**: Definition 3.2 from Hungerbuhler–Wasem: from the right and from the left, the orthogonal deviation `‖tangentDeviation (γ t − γ t₀) L‖` is `o(‖γ t − γ t₀‖ⁿ)` along `𝓝[>] t₀` and `𝓝[<] t₀` respectively, for any nonzero one-sided derivative limit `L`.
- **How**: Definition (two `Asymptotics.IsLittleO` fields keyed by one-sided derivative limits).
- **Hypotheses**: None (a structure).
- **Uses from project**: [`tangentDeviation`]
- **Used by**: `IsFlatOfOrder.of_le`, `isFlatOfOrder_zero`, `isFlatOfOrder_one`, `SatisfiesConditionA'`
- **Visibility**: public
- **Lines**: 128-136
- **Notes**: none

### `theorem IsFlatOfOrder.of_le`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {m n : ℕ} (h : IsFlatOfOrder γ t₀ m) (hmn : n ≤ m) (hγ_cont : ContinuousAt γ t₀) → IsFlatOfOrder γ t₀ n`
- **What**: Flatness of order `m` implies flatness of every smaller order `n ≤ m`, given continuity of `γ` at `t₀`.
- **How** (~20 lines): Eventually `‖γ t − γ t₀‖ ≤ 1` near `t₀` (by continuity), hence `‖·‖^m =O[·] ‖·‖^n` via `pow_le_pow_of_le_one`; chain `IsLittleO.trans_isBigO`.
- **Hypotheses**: `IsFlatOfOrder γ t₀ m`, `n ≤ m`, `ContinuousAt γ t₀`.
- **Uses from project**: [`IsFlatOfOrder`]
- **Used by**: `SatisfiesConditionA'.of_le_poleOrder`
- **Visibility**: public
- **Lines**: 140-159
- **Notes**: none

### `theorem isFlatOfOrder_zero`
- **Type**: `(γ : ℝ → ℂ) (t₀ : ℝ) (hγ_cont : ContinuousAt γ t₀) → IsFlatOfOrder γ t₀ 0`
- **What**: Order-0 flatness holds for any continuous `γ`.
- **How** (~35 lines): For each side, reduce to `IsLittleO_one` and bound `‖tangentDeviation‖ ≤ 2‖γ t − γ t₀‖ < ε` using `norm_tangentDeviation_le` and continuity.
- **Hypotheses**: `ContinuousAt γ t₀`.
- **Uses from project**: [`IsFlatOfOrder`, `tangentDeviation`, `norm_tangentDeviation_le`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 164-198
- **Notes**: > 30 lines

### `private theorem tangentDeviation_isLittleO_right`
- **Type**: `(γ : ℝ → ℂ) (t₀ : ℝ) (L : ℂ) (hL : L ≠ 0) (hγ_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)) (hγ_cont : ContinuousAt γ t₀) (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t) → (·) =o[𝓝[>] t₀] (·)`
- **What**: Right-sided order-1 flatness from right-derivative limit `L`.
- **How** (~40 lines): Build `HasDerivWithinAt γ L (Ioi t₀) t₀` via `hasDerivWithinAt_Ici_of_tendsto_deriv`; write `γ t − γ t₀ = (t − t₀) • L + r t`; tangent deviation reduces to deviation of `r`; `r` is `o(t − t₀)`; then `(t − t₀) =O[𝓝[>] t₀] (γ t − γ t₀)` via reverse triangle inequality.
- **Hypotheses**: `L ≠ 0`, right-derivative limit, continuity at `t₀`, eventual differentiability.
- **Uses from project**: [`tangentDeviation`, `tangentDeviation_add`, `tangentDeviation_real_smul_self`, `norm_tangentDeviation_le`]
- **Used by**: `isFlatOfOrder_one`
- **Visibility**: private
- **Lines**: 209-247
- **Notes**: > 30 lines

### `private theorem tangentDeviation_isLittleO_left`
- **Type**: same shape on `𝓝[<] t₀`
- **What**: Left-sided order-1 flatness from left-derivative limit `L`.
- **How** (~40 lines): Mirror of `tangentDeviation_isLittleO_right` using `hasDerivWithinAt_Iic_of_tendsto_deriv`.
- **Hypotheses**: `L ≠ 0`, left-derivative limit, continuity at `t₀`, eventual differentiability.
- **Uses from project**: [`tangentDeviation`, `tangentDeviation_add`, `tangentDeviation_real_smul_self`, `norm_tangentDeviation_le`]
- **Used by**: `isFlatOfOrder_one`
- **Visibility**: private
- **Lines**: 250-288
- **Notes**: > 30 lines

### `theorem isFlatOfOrder_one`
- **Type**: `(γ : PwC1Immersion x y) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) → IsFlatOfOrder (γ : ℝ → ℂ) t₀ 1`
- **What**: Every piecewise C¹ immersion is order-1 flat at every interior point.
- **How** (~28 lines): Continuity of `γ` from `γ.continuous`; eventual differentiability on each side using `differentiable_off` and the partition being a finite closed set; conclude via `tangentDeviation_isLittleO_right`/`_left`.
- **Hypotheses**: `t₀ ∈ Ioo 0 1`.
- **Uses from project**: [`PwC1Immersion`, `IsFlatOfOrder`, `tangentDeviation_isLittleO_right`, `tangentDeviation_isLittleO_left`]
- **Used by**: `satisfiesConditionA'_of_simplePoles`
- **Visibility**: public
- **Lines**: 293-320
- **Notes**: none

### `def SatisfiesConditionA'`
- **Type**: `(γ : PwC1Immersion x y) (_f : ℂ → ℂ) (S0 : Finset ℂ) (poleOrder : ℂ → ℕ) → Prop`
- **What**: Condition (A'): at every preimage `t₀ ∈ (0,1)` of every singular point `s ∈ S0`, the curve is flat of order `poleOrder s`.
- **How**: Definition (∀-quantified `IsFlatOfOrder`).
- **Hypotheses**: None (definition).
- **Uses from project**: [`PwC1Immersion`, `IsFlatOfOrder`]
- **Used by**: `satisfiesConditionA'_of_simplePoles`, `SatisfiesConditionA'.of_le_poleOrder`, `conditions_automatic_simple_poles`
- **Visibility**: public
- **Lines**: 327-331
- **Notes**: none

### `structure SatisfiesConditionB`
- **Type**: `(γ : PwC1Immersion x y) (f : ℂ → ℂ) (S0 : Finset ℂ) : Prop`
- **What**: Condition (B): the corner angle is a rational multiple of `π` at every crossing, and `f` has a local Laurent decomposition `g(z) + Σ_k a_k/(z−s)^(k+1)` with angle compatibility `k·α ∈ 2πℤ` for every nonzero coefficient with `k ≥ 1`.
- **How**: Two-field structure.
- **Hypotheses**: None (structure).
- **Uses from project**: [`PwC1Immersion`, `angleAtCrossing`]
- **Used by**: `satisfiesConditionB_of_simplePoles`, `conditions_automatic_simple_poles`
- **Visibility**: public
- **Lines**: 340-358
- **Notes**: none

### `theorem satisfiesConditionA'_of_simplePoles`
- **Type**: `(γ : PwC1Immersion x y) (f : ℂ → ℂ) (S0 : Finset ℂ) (_hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s) → SatisfiesConditionA' γ f S0 (fun _ => 1)`
- **What**: For simple poles, (A') with pole-order 1 follows from generic order-1 flatness of piecewise C¹ immersions.
- **How**: Apply `isFlatOfOrder_one`.
- **Hypotheses**: Hypothesis `HasSimplePoleAt` (used only via the pole-order = 1 convention; the witness is unused).
- **Uses from project**: [`SatisfiesConditionA'`, `isFlatOfOrder_one`, `HasSimplePoleAt`]
- **Used by**: `conditions_automatic_simple_poles`
- **Visibility**: public
- **Lines**: 374-378
- **Notes**: none

### `theorem satisfiesConditionB_of_simplePoles`
- **Type**: takes `(γ, f, S0, hSimplePoles, hAngles)` and returns `SatisfiesConditionB γ f S0`
- **What**: For simple poles, (B)'s Laurent compatibility is vacuous (only the residue term `k = 0` survives, so `k ≥ 1` is empty), and the angle condition reduces to angles being rational `pπ/q` (forced at corner partition points only — at smooth points the angle is `π`).
- **How** (~20 lines): For corner points, use `hAngles`; for smooth points, rewrite `angleAtCrossing_smooth` to `π = 1·π/1`. For Laurent, unfold `HasSimplePoleAt` to obtain `c, g, hg, hf_eq`, then provide a singleton `Fin 1 → ℂ` with vector `![c]`; the `k ≥ 1` constraint is dispatched by `omega`.
- **Hypotheses**: All poles simple; corner angles are rationals.
- **Uses from project**: [`SatisfiesConditionB`, `HasSimplePoleAt`, `angleAtCrossing`, `angleAtCrossing_smooth`, `PiecewiseC1Path.partition`]
- **Used by**: `conditions_automatic_simple_poles`
- **Visibility**: public
- **Lines**: 386-412
- **Notes**: none

### `theorem conditions_automatic_simple_poles`
- **Type**: `(γ, f, S0, hSimplePoles, hAngles) → SatisfiesConditionA' γ f S0 (fun _ => 1) ∧ SatisfiesConditionB γ f S0`
- **What**: Both (A') and (B) hold automatically for simple poles, modulo the corner-angle rationality hypothesis.
- **How**: Conjoin the previous two theorems.
- **Hypotheses**: As above.
- **Uses from project**: [`satisfiesConditionA'_of_simplePoles`, `satisfiesConditionB_of_simplePoles`, `SatisfiesConditionA'`, `SatisfiesConditionB`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 417-427
- **Notes**: none

### `theorem SatisfiesConditionA'.of_le_poleOrder`
- **Type**: `(γ, f, S0) {p q : ℂ → ℕ} (hpq : ∀ s ∈ S0, p s ≤ q s) (hA : SatisfiesConditionA' γ f S0 q) → SatisfiesConditionA' γ f S0 p`
- **What**: Monotonicity of condition (A') in the pole-order function.
- **How**: Pointwise application of `IsFlatOfOrder.of_le`, using `γ.continuous.continuousAt`.
- **Hypotheses**: `∀ s ∈ S0, p s ≤ q s`.
- **Uses from project**: [`SatisfiesConditionA'`, `IsFlatOfOrder.of_le`, `PwC1Immersion.continuous`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 433-439
- **Notes**: none

## File Summary

Builds the analytic prerequisites of Hungerbuhler–Wasem Theorem 3.3: orthogonal projection/`tangentDeviation` in `ℂ` viewed as `ℝ²`, the `IsFlatOfOrder` definition (Def. 3.2), and conditions `SatisfiesConditionA'` and `SatisfiesConditionB`. The headline theorem `isFlatOfOrder_one` shows every piecewise `C¹` immersion is order-1 flat, which in turn powers `satisfiesConditionA'_of_simplePoles` and `conditions_automatic_simple_poles`. Internal scaffolding consists of `norm_tangentDeviation_le`, two private one-sided `IsLittleO` lemmas, and the order-monotonicity helper `IsFlatOfOrder.of_le`.
