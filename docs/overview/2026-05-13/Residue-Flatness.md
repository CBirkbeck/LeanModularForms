# Inventory: Flatness.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/Residue/Flatness.lean`
Lines: 467

### `instance NormSMulClass ℝ ℂ` (anonymous)
- **Type**: `NormSMulClass ℝ ℂ`
- **What**: Provides `NormSMulClass` for real-scalar action on complex numbers
- **How**: `NormedSpace.toNormSMulClass`
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: implicit norm computations downstream
- **Visibility**: private instance
- **Lines**: 38

### `def orthogonalProjectionComplex`
- **Type**: `(w L : ℂ) : ℂ`
- **What**: Orthogonal projection of `w` onto the real line spanned by `L`, computed as `(Re(w · conj L) / |L|²) · L`
- **How**: definition `((w * starRingEnd ℂ L).re / normSq L) • L`
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `tangentDeviation`, `orthogonalProjectionComplex_zero_left`, `tangentDeviation_zero_left`, `tangentDeviation_zero_right`, `orthogonalProjectionComplex_smul`, `orthogonalProjectionComplex_real_smul_self`, `tangentDeviation_real_smul_self`, `tangentDeviation_add`, `norm_tangentDeviation_le`
- **Visibility**: public
- **Lines**: 46-47

### `def tangentDeviation`
- **Type**: `(w L : ℂ) : ℂ`
- **What**: The component of `w` orthogonal to direction `L`: `w − orthogonalProjectionComplex w L`
- **How**: definitional
- **Hypotheses**: none
- **Uses from project**: `orthogonalProjectionComplex`
- **Used by**: `tangentDeviation_zero_left/right`, `tangentDeviation_real_smul_self`, `tangentDeviation_add`, `norm_tangentDeviation_le`, `IsFlatOfOrder`, `tangentDeviation_isLittleO_*`, `isFlatOfOrder_one`
- **Visibility**: public
- **Lines**: 50-51

### `theorem orthogonalProjectionComplex_zero_left`
- **Type**: `(L : ℂ) : orthogonalProjectionComplex 0 L = 0`
- **What**: Projection of `0` onto any direction is `0`
- **How**: `simp [orthogonalProjectionComplex]`
- **Hypotheses**: none
- **Uses from project**: `orthogonalProjectionComplex`
- **Used by**: `tangentDeviation_zero_left`
- **Visibility**: public
- **Lines**: 53-55

### `theorem tangentDeviation_zero_left`
- **Type**: `(L : ℂ) : tangentDeviation 0 L = 0`
- **What**: Tangent deviation of zero vector is zero
- **How**: `simp [tangentDeviation, orthogonalProjectionComplex_zero_left]`
- **Hypotheses**: none
- **Uses from project**: `tangentDeviation`, `orthogonalProjectionComplex_zero_left`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 57-59

### `theorem tangentDeviation_zero_right`
- **Type**: `(w : ℂ) : tangentDeviation w 0 = w`
- **What**: When the direction is zero, the tangent deviation is `w` itself
- **How**: `simp` unfolds with `Complex.normSq_zero`
- **Hypotheses**: none
- **Uses from project**: `tangentDeviation`, `orthogonalProjectionComplex`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 61-63

### `theorem orthogonalProjectionComplex_smul`
- **Type**: `(w L : ℂ) : ∃ c : ℝ, orthogonalProjectionComplex w L = c • L`
- **What**: The projection is a real scalar multiple of `L`
- **How**: explicit witness `(w * conj L).re / normSq L`; `rfl`
- **Hypotheses**: none
- **Uses from project**: `orthogonalProjectionComplex`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 66-68

### `theorem orthogonalProjectionComplex_real_smul_self`
- **Type**: `(c : ℝ) (L : ℂ) (hL : L ≠ 0) : orthogonalProjectionComplex (c • L) L = c • L`
- **What**: Projecting `c • L` onto `L` returns `c • L`
- **How**: reduces the coefficient `(c•L · conj L).re / normSq L = c` using `Complex.mul_conj` and `mul_div_cancel_of_imp`
- **Hypotheses**: `L ≠ 0`
- **Uses from project**: `orthogonalProjectionComplex`
- **Used by**: `tangentDeviation_real_smul_self`
- **Visibility**: public
- **Lines**: 71-79

### `theorem tangentDeviation_real_smul_self`
- **Type**: `(c : ℝ) (L : ℂ) (hL : L ≠ 0) : tangentDeviation (c • L) L = 0`
- **What**: Tangent deviation of a scalar multiple of `L` from `L` is zero
- **How**: rewrites with `orthogonalProjectionComplex_real_smul_self`, then `sub_self`
- **Hypotheses**: `L ≠ 0`
- **Uses from project**: `tangentDeviation`, `orthogonalProjectionComplex_real_smul_self`
- **Used by**: `tangentDeviation_isLittleO_of_hasDerivAt`, `tangentDeviation_isLittleO_right`, `tangentDeviation_isLittleO_left`
- **Visibility**: public
- **Lines**: 82-84

### `theorem tangentDeviation_add`
- **Type**: `(w₁ w₂ L : ℂ) : tangentDeviation (w₁ + w₂) L = tangentDeviation w₁ L + tangentDeviation w₂ L`
- **What**: Additivity of tangent deviation in the first argument
- **How**: unfolds `tangentDeviation, orthogonalProjectionComplex`, simplifies real-part addition and division, closes by `module`
- **Hypotheses**: none
- **Uses from project**: `tangentDeviation`, `orthogonalProjectionComplex`
- **Used by**: `tangentDeviation_isLittleO_of_hasDerivAt`, `tangentDeviation_isLittleO_right`, `tangentDeviation_isLittleO_left`
- **Visibility**: public
- **Lines**: 87-91

### `theorem norm_tangentDeviation_le`
- **Type**: `(w L : ℂ) (hL : L ≠ 0) : ‖tangentDeviation w L‖ ≤ 2 * ‖w‖`
- **What**: Norm bound: tangent deviation is bounded by `2‖w‖`
- **How**: triangle inequality `norm_sub_le`; then bounds the projection by `‖w‖` using `Complex.abs_re_le_norm` and `Complex.norm_mul_self_eq_normSq` (proof >10 lines)
- **Hypotheses**: `L ≠ 0`
- **Uses from project**: `tangentDeviation`, `orthogonalProjectionComplex`
- **Used by**: `tangentDeviation_isLittleO_of_hasDerivAt`, `tangentDeviation_isLittleO_right`, `tangentDeviation_isLittleO_left`
- **Visibility**: public
- **Lines**: 94-113
- **Notes**: >10 lines

### `structure IsFlatOfOrder`
- **Type**: `(γ : ℝ → ℂ) (t₀ : ℝ) (n : ℕ) : Prop`
- **What**: Flatness of order `n`: from both sides, the tangent deviation from the one-sided derivative is `o(‖γ(t) - γ(t₀)‖^n)` as `t → t₀`
- **How**: structure with `right_flat` and `left_flat` fields, both quantified over nonzero direction `L` with derivative-limit hypothesis
- **Hypotheses**: per side, existence of `Tendsto (deriv γ)` to `L`
- **Uses from project**: `tangentDeviation`
- **Used by**: `IsFlatOfOrder.of_le`, `isFlatOfOrder_one`, `SatisfiesConditionA`, `SatisfiesConditionA'`, `satisfiesConditionA_of_simple_poles`
- **Visibility**: public
- **Lines**: 128-136

### `theorem IsFlatOfOrder.of_le`
- **Type**: `{γ t₀ m n} (h : IsFlatOfOrder γ t₀ m) (hmn : n ≤ m) (hγ_cont : ContinuousAt γ t₀) : IsFlatOfOrder γ t₀ n`
- **What**: Higher-order flatness implies lower-order: if `n ≤ m`, then `o(‖·‖^m) ⊆ o(‖·‖^n)` (since `‖·‖ → 0`)
- **How**: `h_le_one : ‖γ(t)-γ(t₀)‖ ≤ 1` eventually from continuity; then `h_big_O : (‖·‖^m) =O[l] (‖·‖^n)` by `pow_le_pow_of_le_one`; combines via `trans_isBigO` on each side (proof >10 lines)
- **Hypotheses**: flatness of order `m`; `n ≤ m`; `γ` continuous at `t₀`
- **Uses from project**: `IsFlatOfOrder`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 140-157
- **Notes**: >10 lines

### `theorem tangentDeviation_isLittleO_of_hasDerivAt`
- **Type**: `(γ t₀ L) (hL : L ≠ 0) (hγ : HasDerivAt γ L t₀) : (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝 t₀] (fun t => ‖γ t - γ t₀‖ ^ 1)`
- **What**: If `γ` has derivative `L` at `t₀`, tangent deviation from `L` is `o(‖γ(t) - γ(t₀)‖)`
- **How**: with `r(t) := γ(t) - γ(t₀) - (t-t₀)•L`, splits tangent deviation onto `r(t)` via `tangentDeviation_add` and `tangentDeviation_real_smul_self`; uses `hasDerivAt_iff_isLittleO` and `norm_tangentDeviation_le` for `=O[r]`, then bounds `t-t₀ =O[γ-γ₀]` by `2/‖L‖` using `‖(t-t₀)•L‖ ≤ ‖γ-γ₀‖ + ‖r‖` and `‖r‖ ≤ ‖L‖/2 · ‖t-t₀‖` (proof >10 lines)
- **Hypotheses**: `L ≠ 0`; `HasDerivAt γ L t₀`
- **Uses from project**: `tangentDeviation`, `tangentDeviation_add`, `tangentDeviation_real_smul_self`, `norm_tangentDeviation_le`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 173-203
- **Notes**: >10 lines

### `theorem tangentDeviation_isLittleO_right`
- **Type**: `(γ t₀ L) (hL : L ≠ 0) (hγ_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)) (hγ_cont) (hγ_diff) : (... =o[𝓝[>] t₀] ‖γ-γ₀‖^1)`
- **What**: Right-sided version of `tangentDeviation_isLittleO_of_hasDerivAt`: tangent deviation is `o(‖γ(t)-γ(t₀)‖)` as `t → t₀⁺`
- **How**: obtains `HasDerivWithinAt γ L (Ioi t₀) t₀` via `hasDerivWithinAt_Ioi_iff_Ici.mpr` and `hasDerivWithinAt_Ici_of_tendsto_deriv`; then mirrors the proof of the two-sided version with `r := γ(t) - γ(t₀) - (t-t₀)•L`, using `hasDerivWithinAt_iff_isLittleO` and `norm_tangentDeviation_le` (proof >10 lines)
- **Hypotheses**: `L ≠ 0`; right-deriv limit `L`; continuity at `t₀`; eventual differentiability on `𝓝[>] t₀`
- **Uses from project**: `tangentDeviation`, `tangentDeviation_add`, `tangentDeviation_real_smul_self`, `norm_tangentDeviation_le`
- **Used by**: `isFlatOfOrder_one`
- **Visibility**: public
- **Lines**: 207-245
- **Notes**: >10 lines

### `theorem tangentDeviation_isLittleO_left`
- **Type**: `(γ t₀ L) (hL : L ≠ 0) (hγ_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L)) (hγ_cont) (hγ_diff) : (... =o[𝓝[<] t₀] ‖γ-γ₀‖^1)`
- **What**: Left-sided version of `tangentDeviation_isLittleO_of_hasDerivAt`
- **How**: obtains `HasDerivWithinAt γ L (Iio t₀) t₀` via `hasDerivWithinAt_Iio_iff_Iic.mpr` and `hasDerivWithinAt_Iic_of_tendsto_deriv`; remainder argument mirrors the right-sided version (proof >10 lines)
- **Hypotheses**: `L ≠ 0`; left-deriv limit `L`; continuity at `t₀`; eventual differentiability on `𝓝[<] t₀`
- **Uses from project**: `tangentDeviation`, `tangentDeviation_add`, `tangentDeviation_real_smul_self`, `norm_tangentDeviation_le`
- **Used by**: `isFlatOfOrder_one`
- **Visibility**: public
- **Lines**: 249-287
- **Notes**: >10 lines

### `theorem isFlatOfOrder_one`
- **Type**: `(γ : PiecewiseC1Immersion) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) : IsFlatOfOrder γ.toFun t₀ 1`
- **What**: Every piecewise `C¹` immersion is flat of order 1 at every interior point
- **How**: derives continuity at `t₀` from `γ.continuous_toFun`; produces eventual differentiability away from `γ.partition` (closed set) by filtering on `𝓝[>] t₀` / `𝓝[<] t₀`, using `γ.smooth_off_partition`; then applies `tangentDeviation_isLittleO_right/left` (proof >10 lines)
- **Hypotheses**: `t₀` interior in `(γ.a, γ.b)`
- **Uses from project**: `IsFlatOfOrder`, `tangentDeviation_isLittleO_right`, `tangentDeviation_isLittleO_left`, `PiecewiseC1Immersion`, `PiecewiseC1Immersion.smooth_off_partition`, `PiecewiseC1Immersion.partition`, `PiecewiseC1Immersion.continuous_toFun`
- **Used by**: `satisfiesConditionA_of_simple_poles`
- **Visibility**: public
- **Lines**: 293-320
- **Notes**: >10 lines

### `def poleOrderAt`
- **Type**: `(f : ℂ → ℂ) (x : ℂ) : ℕ`
- **What**: Pole order of `f` at `x` as a natural number: `(-meromorphicOrderAt f x).untop₀.toNat` (returns `0` if `f` is analytic)
- **How**: definition via `WithTop.untop₀` and `Int.toNat`
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 327-328

### `def SatisfiesConditionA`
- **Type**: `(γ : PiecewiseC1Immersion) (_f : ℂ → ℂ) (S0 : Finset ℂ) : Prop`
- **What**: Hungerbuhler-Wasem Condition (A): at each crossing point `s ∈ S₀`, the curve is flat of order 1
- **How**: defined as `∀ s ∈ S0, ∀ t₀ ∈ Icc γ.a γ.b, γ.toFun t₀ = s → t₀ ∈ Ioo γ.a γ.b → IsFlatOfOrder γ.toFun t₀ 1`
- **Hypotheses**: none (definitional)
- **Uses from project**: `IsFlatOfOrder`, `PiecewiseC1Immersion`
- **Used by**: `satisfiesConditionA_of_simple_poles`, `conditions_automatic_simple_poles`
- **Visibility**: public
- **Lines**: 342-345

### `def SatisfiesConditionA'`
- **Type**: `(γ : PiecewiseC1Immersion) (_f : ℂ → ℂ) (S0 : Finset ℂ) (poleOrder : ℂ → ℕ) : Prop`
- **What**: Condition (A) with explicit pole-order: at each `s ∈ S₀`, the curve is flat of order `poleOrder s`
- **How**: as `SatisfiesConditionA` but `IsFlatOfOrder γ.toFun t₀ (poleOrder s)`
- **Hypotheses**: none (definitional)
- **Uses from project**: `IsFlatOfOrder`, `PiecewiseC1Immersion`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 350-354

### `structure SatisfiesConditionB`
- **Type**: `(γ : PiecewiseC1Immersion) (f : ℂ → ℂ) (S0 : Finset ℂ) : Prop`
- **What**: Hungerbuhler-Wasem Condition (B): at each crossing the angle is `pπ/q`, and the Laurent decomposition `f = g + Σ aₖ/(z-s)^{k+1}` has every nonzero coefficient `aₖ` (with `k ≥ 1`) compatible: `k · α ∈ 2πℤ`
- **How**: structure with `angle_rational` and `laurent_compatible` fields
- **Hypotheses**: none (definitional)
- **Uses from project**: `PiecewiseC1Immersion`, `angleAtCrossing`
- **Used by**: `satisfiesConditionB_of_simple_poles`, `conditions_automatic_simple_poles`
- **Visibility**: public
- **Lines**: 367-388

### `theorem satisfiesConditionA_of_simple_poles`
- **Type**: `(γ : PiecewiseC1Immersion) (f : ℂ → ℂ) (S0 : Finset ℂ) (_hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s) : SatisfiesConditionA γ f S0`
- **What**: Condition (A) is automatic for simple poles
- **How**: invokes `isFlatOfOrder_one γ t₀ ht₀_Ioo` for every interior crossing parameter
- **Hypotheses**: every pole in `S₀` is simple (unused — flatness of order 1 is automatic anyway)
- **Uses from project**: `SatisfiesConditionA`, `isFlatOfOrder_one`, `HasSimplePoleAt`
- **Used by**: `conditions_automatic_simple_poles`
- **Visibility**: public
- **Lines**: 404-409

### `theorem satisfiesConditionB_of_simple_poles`
- **Type**: `(γ : PiecewiseC1Immersion) (f : ℂ → ℂ) (S0 : Finset ℂ) (_hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s) (hAngles : ∀ s ∈ S₀, ∀ t₀ ∈ partition: rational angle) : SatisfiesConditionB γ f S0`
- **What**: Condition (B) for simple poles, given angle rationality at corner crossings
- **How**: angle rationality: uses `hAngles` at corner points; at smooth crossings uses `angleAtCrossing_smooth = π = 1·π/1`. Laurent compatibility: writes Laurent series via `HasSimplePoleAt` data `⟨c, g, hg, hf_eq⟩`, takes `N=1` with vector `![c]`; the secondary higher-order coefficient condition is vacuously discharged (`k.val ≥ 1` and `N=1` force `k=0`, contradiction via `omega`)
- **Hypotheses**: simple poles; corner-crossing angles are rational multiples of `π`
- **Uses from project**: `SatisfiesConditionB`, `HasSimplePoleAt`, `PiecewiseC1Immersion`, `angleAtCrossing`, `angleAtCrossing_smooth`
- **Used by**: `conditions_automatic_simple_poles`
- **Visibility**: public
- **Lines**: 422-447
- **Notes**: >10 lines; uses `open Classical in`

### `theorem conditions_automatic_simple_poles`
- **Type**: `(γ : PiecewiseC1Immersion) (f : ℂ → ℂ) (S0 : Finset ℂ) (hSimplePoles, hAngles) : SatisfiesConditionA γ f S0 ∧ SatisfiesConditionB γ f S0`
- **What**: Both Hungerbuhler-Wasem conditions are automatic for simple poles (given corner-angle rationality)
- **How**: pairs `satisfiesConditionA_of_simple_poles` and `satisfiesConditionB_of_simple_poles`
- **Hypotheses**: simple poles; corner-angle rationality
- **Uses from project**: `SatisfiesConditionA`, `SatisfiesConditionB`, `satisfiesConditionA_of_simple_poles`, `satisfiesConditionB_of_simple_poles`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 455-465

## File Summary

Flatness.lean implements Definition 3.2 from Hungerbuhler-Wasem (arXiv:1808.00997v2): the orthogonal-tangent-deviation calculus for piecewise `C¹` curves and the conditions (A) and (B) needed by the generalized residue theorem with higher-order poles. The file builds linearly: (i) `orthogonalProjectionComplex` and `tangentDeviation` definitions with elementary algebraic identities (`_zero_left/right`, `_real_smul_self`, `_add`, `norm_le`); (ii) the predicate `IsFlatOfOrder γ t₀ n` together with monotonicity in `n` (`of_le`); (iii) the three workhorse lemmas `tangentDeviation_isLittleO_*` (two-sided, right, left) showing the deviation from any directional derivative is `o(‖γ(t)-γ(t₀)‖)`; (iv) the headline `isFlatOfOrder_one` saying every piecewise `C¹` immersion is order-1 flat at interior points; (v) `poleOrderAt`, the conditions `SatisfiesConditionA[']` and `SatisfiesConditionB`, and the automaticity theorems `satisfiesConditionA_of_simple_poles`, `satisfiesConditionB_of_simple_poles`, `conditions_automatic_simple_poles` showing both conditions hold for simple poles (B only requires rational angles at corners). No sorries; depends on `ClassicalCPV`, `Residue`, `WindingNumber`, and `Mathlib.Analysis.Meromorphic.Order`.
