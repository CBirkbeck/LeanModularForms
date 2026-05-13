# HigherOrderCancel.lean — Declaration Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HigherOrderCancel.lean` (1515 lines).

No namespace; all declarations at top level.

---

### `theorem hCancel_of_contourIntegral_zero`
- **Type**: `(S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s‖) (h_zero : γ.contourIntegral f = 0) → HasCauchyPVOn S f γ 0`
- **What**: When γ avoids `S` with positive margin and `f`'s contour integral is 0, the CPV of `f` is 0.
- **How**: Direct application of `hasCauchyPVOn_of_avoids` after rewriting `0` using `h_zero`.
- **Hypotheses**: positive margin from γ to `S`; contour integral vanishes.
- **Uses from project**: `HasCauchyPVOn`, `hasCauchyPVOn_of_avoids`, `PiecewiseC1Path.contourIntegral`, `PiecewiseC1Path`.
- **Used by**: `hCancel_of_avoids`.
- **Visibility**: public
- **Lines**: 74–79

### `theorem hCancel_of_avoids`
- **Type**: As above, for the remainder `fun z => f z - principalPartSum S (residue f) z`.
- **What**: Avoidance-case cancellation for general poles: CPV of the remainder is 0 if its contour integral vanishes and γ avoids `S` with positive margin.
- **How**: Apply `hCancel_of_contourIntegral_zero` to the remainder.
- **Hypotheses**: as above.
- **Uses from project**: `principalPartSum`, `residue`, `hCancel_of_contourIntegral_zero`, `HasCauchyPVOn`, `PiecewiseC1Path`.
- **Used by**: `hCancel_of_holomorphic_agree`, `hCancel_of_simplePoles_avoids`.
- **Visibility**: public
- **Lines**: 88–95

### `theorem hCancel_of_holomorphic_agree`
- **Type**: `... (g : ℂ → ℂ) (hg_zero : γ.contourIntegral g = 0) (hg_agree : ∀ t ∈ Icc 0 1, g (γ t) = f (γ t) - principalPartSum S (residue f) (γ t)) → HasCauchyPVOn S (remainder) γ 0`
- **What**: Bridge lemma: if a function `g` agrees with the remainder along γ and its contour integral is 0, then the remainder's CPV is 0.
- **How**: Use `intervalIntegral.integral_congr` to show that the contour integrand of the remainder agrees with the contour integrand of `g` on `uIcc 0 1`, so their contour integrals agree. Combine with `hCancel_of_avoids`.
- **Hypotheses**: γ avoids `S` with margin, `g`'s contour integral is 0, `g` agrees with remainder pointwise on γ.
- **Uses from project**: `principalPartSum`, `residue`, `PiecewiseC1Path.contourIntegral`, `PiecewiseC1Path.extendedPath_eq`, `hCancel_of_avoids`, `HasCauchyPVOn`, `PiecewiseC1Path`.
- **Used by**: `hCancel_of_holomorphic_convex`.
- **Visibility**: public
- **Lines**: 105–125

### `theorem hCancel_of_holomorphic_convex`
- **Type**: `{U} (hU_convex) (hU_open) (hU_ne) (S f γ) (hδ) (hγ_in_U) (g : ℂ → ℂ) (hg_diff : DifferentiableOn ℂ g U) (hg_agree : ∀ z ∈ U \ ↑S, g z = remainder z) (hγ_avoids) (h_g_int : IntervalIntegrable ... volume 0 1) → HasCauchyPVOn S (remainder) γ 0`
- **What**: Convex-domain cancellation: if a holomorphic `g` on convex open `U` agrees with the remainder on the curve and γ stays in `U` avoiding `S`, the remainder's CPV is 0.
- **How**: Apply `contourIntegral_eq_zero_of_differentiableOn_convex_aux` (convex Cauchy) to get `γ.contourIntegral g = 0`, then `hCancel_of_holomorphic_agree`.
- **Hypotheses**: as in signature.
- **Uses from project**: `PiecewiseC1Path.contourIntegral_eq_zero_of_differentiableOn_convex_aux`, `hCancel_of_holomorphic_agree`, `principalPartSum`, `residue`, `HasCauchyPVOn`, `PiecewiseC1Path`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 132–153

### `theorem hCancel_of_decomposition`
- **Type**: `(S f γ h₁ h₂) (h_decomp : ∀ z, remainder z = h₁ z + h₂ z) (hh₁ : HasCauchyPVOn S h₁ γ 0) (hh₂ : HasCauchyPVOn S h₂ γ 0) (hI₁ hI₂) → HasCauchyPVOn S (remainder) γ 0`
- **What**: Structural decomposition: if the remainder splits as `h₁ + h₂` with both having vanishing CPV, the full remainder has vanishing CPV.
- **How**: Use `HasCauchyPVOn.add` to combine `hh₁` and `hh₂`, then a `congr`/`split_ifs` argument to identify the CPV of `h₁ + h₂` with the CPV of the remainder via pointwise equality.
- **Hypotheses**: `h_decomp` pointwise; integrability of each cpv integrand.
- **Uses from project**: `principalPartSum`, `residue`, `HasCauchyPVOn`, `HasCauchyPVOn.add`, `cpvIntegrandOn`, `PiecewiseC1Path`.
- **Used by**: `hCancel_structural_gateway`.
- **Visibility**: public
- **Lines**: 164–193
- **Notes**: proof >10 lines

### `theorem hCancel_of_simplePoles_avoids`
- **Type**: `(S f γ) (hδ) (_hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s) (h_rem_vanishes : γ.contourIntegral (remainder) = 0) → HasCauchyPVOn S (remainder) γ 0`
- **What**: Simple-pole avoidance cancellation: the simple-pole hypothesis is moot (unused); just an alias of `hCancel_of_avoids`.
- **How**: Direct application of `hCancel_of_avoids`.
- **Hypotheses**: as in signature.
- **Uses from project**: `HasSimplePoleAt`, `principalPartSum`, `residue`, `hCancel_of_avoids`, `HasCauchyPVOn`, `PiecewiseC1Path`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 204–212

### `theorem higherOrder_sector_cancel_odd`
- **Type**: `(r : ℝ) (hr : 0 < r) (α : ℝ) (k : ℕ) (hk : 2 ≤ k) (hk_odd : Odd k) (_h_angle : ∃ m : ℤ, k·α = m·2π) → Tendsto (fun ε => (∫ t in -1..(-ε), (lineCurve r α t)⁻¹^k * deriv (lineCurve r α) t) + ∫ t in ε..1, ...) (𝓝[>] 0) (𝓝 0)`
- **What**: Odd-power sector cancellation: PV integral of `lineCurve^(-k)·deriv` vanishes for odd `k ≥ 2`.
- **How**: Direct application of `SectorCurve.cpv_lineCurve_inv_pow_odd`.
- **Hypotheses**: `r > 0`, `k ≥ 2` odd, angle condition (unused in proof).
- **Uses from project**: `SectorCurve.lineCurve`, `SectorCurve.cpv_lineCurve_inv_pow_odd`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 224–234

### `theorem higherOrder_sector_cancel_even_of_flat`
- **Type**: `(r α) (_hr) (k : ℕ) (_hk : 2 ≤ k) (_hk_even : Even k) (h_angle : k·α ∈ 2π·ℤ) → SectorCurve.higherOrderFactor r α k = ↑(r⁻¹^k)`
- **What**: Even-power case: angle condition `k·α ∈ 2πℤ` makes `higherOrderFactor` reduce to `r⁻¹^k`.
- **How**: Direct application of `SectorCurve.higherOrderFactor_eq_of_angle_condition`.
- **Hypotheses**: angle condition; even `k`.
- **Uses from project**: `SectorCurve.higherOrderFactor`, `SectorCurve.higherOrderFactor_eq_of_angle_condition`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 246–251

### `theorem hCancel_simplePoles_convex'`
- **Type**: Full-API variant of `hCancel_of_simplePoles_convex`: identical signature, identical body (just calls it).
- **What**: Convenience alias for `hCancel_of_simplePoles_convex`.
- **How**: Direct delegation.
- **Hypotheses**: as in signature (lengthy: convex `U`, simple poles, γ in `U`, avoidance with margin, integrability).
- **Uses from project**: `hCancel_of_simplePoles_convex`, `HasSimplePoleAt`, `principalPartSum`, `residue`, `HasCauchyPVOn`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 262–278

### `theorem conditionB_higherOrder_factor_eq`
- **Type**: `(r α : ℝ) (k : ℕ) (_hk : 1 ≤ k) (h_angle : k·α ∈ 2π·ℤ) → SectorCurve.higherOrderFactor r α k = ↑(r⁻¹^k)`
- **What**: Condition (B) bridge: angle condition implies higher-order factor equals pure power.
- **How**: Direct application of `SectorCurve.higherOrderFactor_eq_of_angle_condition`.
- **Hypotheses**: angle condition.
- **Uses from project**: `SectorCurve.higherOrderFactor`, `SectorCurve.higherOrderFactor_eq_of_angle_condition`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 286–290

### `theorem odd_power_pv_vanishes`
- **Type**: `(k : ℕ) (hk : 1 ≤ k) (hk_odd : Odd k) → Tendsto (fun ε => (∫ t in -1..(-ε), (t:ℂ)⁻¹^k) + ∫ t in ε..1, (t:ℂ)⁻¹^k) (𝓝[>] 0) (𝓝 0)`
- **What**: Odd-power PV vanishes on symmetric interval by symmetry, independent of any angle condition.
- **How**: Direct application of `SectorCurve.pv_odd_power_vanishes`.
- **Hypotheses**: `k ≥ 1`, `k` odd.
- **Uses from project**: `SectorCurve.pv_odd_power_vanishes`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 296–301

### `theorem hCancel_of_simplePoles_convex_full`
- **Type**: Same as `hCancel_simplePoles_convex'` (delegating to `hCancel_of_simplePoles_convex`).
- **What**: Preferred entry-point alias; signature/body duplicate of `hCancel_simplePoles_convex'`.
- **How**: Direct delegation.
- **Hypotheses**: as in signature.
- **Uses from project**: same as `hCancel_simplePoles_convex'`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 316–332

### `theorem hCancel_structural_gateway`
- **Type**: `(S f γ h_holo r_polar) (h_decomp : ∀ z, remainder z = h_holo z + r_polar z) (h_holo_cancel : HasCauchyPVOn S h_holo γ 0) (h_polar_cancel : HasCauchyPVOn S r_polar γ 0) (hI_holo hI_polar) → HasCauchyPVOn S (remainder) γ 0`
- **What**: Structural gateway: factor the remainder into "holomorphic" + "polar" parts each with vanishing CPV.
- **How**: Direct application of `hCancel_of_decomposition`.
- **Hypotheses**: decomposition exists, each side has vanishing CPV, each side is integrable.
- **Uses from project**: `hCancel_of_decomposition`, `principalPartSum`, `residue`, `HasCauchyPVOn`, `cpvIntegrandOn`, `PiecewiseC1Path`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 357–372

### `theorem generalizedResidueTheorem_with_hCancel`
- **Type**: `(S f γ) (hCancel : HasCauchyPVOn S (remainder) γ 0) (hδ) (hI hI_cpv_rem hI_cpv_sing) → HasCauchyPVOn S f γ (∑ s ∈ S, 2πi · gWN γ s · residue f s)`
- **What**: Assembles the generalized residue theorem from an explicit `hCancel` discharge plus integrability conditions.
- **How**: Direct application of `generalizedResidueTheorem_composed` (with `hPV_sing_of_avoids` constructing the singular CPV existence from `hδ`).
- **Hypotheses**: cancellation hypothesis, avoidance margin, integrability of various pieces.
- **Uses from project**: `generalizedResidueTheorem_composed`, `hPV_sing_of_avoids`, `principalPartSum`, `residue`, `generalizedWindingNumber`, `HasCauchyPVOn`, `cpvIntegrandOn`, `PiecewiseC1Path`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 386–406

### `theorem hasCauchyPVOn_empty_eq`
- **Type**: `(f γ) → HasCauchyPVOn ∅ f γ (γ.contourIntegral f)`
- **What**: For empty pole set, CPV equals contour integral (because the integrand is always the non-excised one).
- **How**: Direct application of `hasCauchyPVOn_of_avoids` with witness `δ = 1` (since `∅` has no points).
- **Hypotheses**: none.
- **Uses from project**: `HasCauchyPVOn`, `hasCauchyPVOn_of_avoids`, `PiecewiseC1Path.contourIntegral`, `PiecewiseC1Path`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 412–414

### `theorem hCancel_of_empty_convex`
- **Type**: `{U} (hU_convex hU_open hU_ne) (f hf γ) (hγ_in_U) (h_int) → HasCauchyPVOn ∅ f γ 0`
- **What**: Holomorphic-on-convex `f` with empty pole set has CPV 0.
- **How**: Apply `contourIntegral_eq_zero_of_differentiableOn_convex_aux` to get `γ.contourIntegral f = 0`, then `hasCauchyPVOn_of_avoids`.
- **Hypotheses**: `U` convex open nonempty, `f` differentiable on `U`, γ in `U`, integrability.
- **Uses from project**: `PiecewiseC1Path.contourIntegral_eq_zero_of_differentiableOn_convex_aux`, `HasCauchyPVOn`, `hasCauchyPVOn_of_avoids`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 418–429

### `theorem hCancel_congr`
- **Type**: `(S f g γ) (h_eq : ∀ z, f z = g z) (hf : HasCauchyPVOn S f γ 0) → HasCauchyPVOn S g γ 0`
- **What**: Pointwise-equality transfer of `HasCauchyPVOn` on the same γ.
- **How**: Rewrite the CPV integral via `congr`/`split_ifs` and `h_eq`, then transfer the conclusion.
- **Hypotheses**: pointwise equality of `f` and `g`.
- **Uses from project**: `HasCauchyPVOn`, `cpvIntegrandOn`, `PiecewiseC1Path`.
- **Used by**: `hCancel_of_remainder_eq`.
- **Visibility**: public
- **Lines**: 435–453

### `theorem hCancel_of_remainder_eq`
- **Type**: `(S f₁ f₂ γ c₁ c₂) (h_eq : ∀ z, f₁ z - principalPartSum S c₁ z = f₂ z - principalPartSum S c₂ z) (hf₁ : HasCauchyPVOn S (rem₁) γ 0) → HasCauchyPVOn S (rem₂) γ 0`
- **What**: Transfer `hCancel` along pointwise equality of remainders (allowing different coefficient functions).
- **How**: Direct application of `hCancel_congr`.
- **Hypotheses**: pointwise equality of the two remainders.
- **Uses from project**: `hCancel_congr`, `principalPartSum`, `HasCauchyPVOn`, `PiecewiseC1Path`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 458–464

### `theorem tangentApproximation_of_isFlatOfOrder_right`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {n : ℕ} (h_flat : IsFlatOfOrder γ t₀ n) {L} (hL : L ≠ 0) (hL_right) (hγ_diff) (hγ_cont) → (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[>] t₀] (fun t => |t - t₀| ^ n)`
- **What**: From right-side flatness order `n`, tangent deviation is `o(|t-t₀|^n)` from the right.
- **How**: Use `IsFlatOfOrder.right_flat` to get `o(‖γ-γ₀‖^n)`; use `DifferentiableWithinAt.isBigO_sub` to get `γ-γ₀ = O(t-t₀)`; raise to `n`-th power via `IsBigO.pow`; transport norms and combine via `IsLittleO.trans_isBigO`.
- **Hypotheses**: γ flat of order `n` at `t₀`; right derivative limit `L ≠ 0`; eventually differentiable on the right; continuous at `t₀`.
- **Uses from project**: `IsFlatOfOrder`, `IsFlatOfOrder.right_flat`, `tangentDeviation`.
- **Used by**: `chord_to_tangent_isLittleO_right`.
- **Visibility**: public
- **Lines**: 477–510
- **Notes**: proof >30 lines

### `theorem tangentApproximation_of_isFlatOfOrder_left`
- **Type**: Symmetric to `_right`, for `𝓝[<] t₀`.
- **What**: Left-side version: tangent deviation is `o(|t-t₀|^n)` from the left.
- **How**: Same as `_right` with `hasDerivWithinAt_Iio_iff_Iic`/`hasDerivWithinAt_Iic_of_tendsto_deriv` for the left side.
- **Hypotheses**: symmetric.
- **Uses from project**: `IsFlatOfOrder`, `IsFlatOfOrder.left_flat`, `tangentDeviation`.
- **Used by**: `chord_to_tangent_isLittleO_left`.
- **Visibility**: public
- **Lines**: 514–542
- **Notes**: proof >30 lines

### `theorem hasDerivAt_antiderivative_pow_inv`
- **Type**: `{γ : ℝ → ℂ} {γ' s : ℂ} {t : ℝ} {k : ℕ} (hk : 2 ≤ k) (hγ : HasDerivAt γ γ' t) (h_ne : γ t - s ≠ 0) → HasDerivAt (fun u => -(↑(k-1):ℂ)⁻¹ * ((γ u - s)^(k-1))⁻¹) (γ' / (γ t - s)^k) t`
- **What**: Real-parameter chain rule: `F(u) := -1/((k-1)(γ(u)-s)^(k-1))` has derivative `γ'/(γ(t)-s)^k` at `t`.
- **How**: Compose `HasDerivAt.sub_const` (γ - s), `HasDerivAt.pow` for `(γ-s)^(k-1)`, `hasDerivAt_inv` for the inverse, then `HasDerivAt.const_mul`; finish with `field_simp` after observing `((γ-s)^(k-1))^2 = (γ-s)^k · (γ-s)^(k-2)`.
- **Hypotheses**: `k ≥ 2`, γ differentiable at `t`, `γ(t) ≠ s`.
- **Uses from project**: []
- **Used by**: `integral_pow_inv_eq_FTC`.
- **Visibility**: public
- **Lines**: 559–583
- **Notes**: proof >10 lines

### `theorem integral_pow_inv_eq_FTC`
- **Type**: `{γ γ' s k a b} (hk : 2 ≤ k) (hγ : ∀ t ∈ uIcc a b, HasDerivAt γ (γ' t) t) (h_avoids : ∀ t ∈ uIcc a b, γ t ≠ s) (h_int : IntervalIntegrable ... volume a b) → ∫ t in a..b, γ' t / (γ t - s)^k = (boundary diff)`
- **What**: FTC on a smooth piece: integral of `γ'/(γ-s)^k` equals the antiderivative endpoint difference.
- **How**: `intervalIntegral.integral_eq_sub_of_hasDerivAt` with the antiderivative from `hasDerivAt_antiderivative_pow_inv` at each point in `uIcc a b`.
- **Hypotheses**: differentiability and avoidance on `uIcc a b`, integrability.
- **Uses from project**: `hasDerivAt_antiderivative_pow_inv`.
- **Used by**: `closed_excised_integral_eq_antideriv_diff`.
- **Visibility**: public
- **Lines**: 591–603

### `theorem hasDerivAt_antiderivative_pow_inv_complex`
- **Type**: `{s : ℂ} {k} (hk : 2 ≤ k) {z : ℂ} (hz : z ≠ s) → HasDerivAt (fun w => -(↑(k-1):ℂ)⁻¹ * ((w - s)^(k-1))⁻¹) (1 / (z - s)^k) z`
- **What**: Complex form: `F(w) := -1/((k-1)(w-s)^(k-1))` has complex derivative `1/(z-s)^k` at any `z ≠ s`.
- **How**: Compose `HasDerivAt.sub_const`, `HasDerivAt.pow`, `HasDerivAt.inv`, `HasDerivAt.const_mul`; finish with `field_simp`.
- **Hypotheses**: `k ≥ 2`, `z ≠ s`.
- **Uses from project**: []
- **Used by**: `PiecewiseC1Path.contourIntegral_pow_inv_eq_zero`, `norm_F_diff_le_segment_bound`.
- **Visibility**: public
- **Lines**: 615–637
- **Notes**: proof >10 lines

### `theorem PiecewiseC1Path.contourIntegral_pow_inv_eq_zero`
- **Type**: `{x} (γ : PiecewiseC1Path x x) {s k} (hk : 2 ≤ k) (h_avoids : ∀ t ∈ Icc 0 1, γ t ≠ s) (h_int) → γ.contourIntegral (fun z => 1 / (z - s)^k) = 0`
- **What**: For closed γ avoiding `s`, the contour integral of `1/(z-s)^k` is 0 for `k ≥ 2` (single-valued antiderivative).
- **How**: Direct application of `contourIntegral_eq_zero_of_hasDerivAt_of_closed` with the antiderivative from `hasDerivAt_antiderivative_pow_inv_complex` on `U = {z | z ≠ s}`.
- **Hypotheses**: γ avoids `s` on `[0,1]`, integrability.
- **Uses from project**: `PiecewiseC1Path.contourIntegral_eq_zero_of_hasDerivAt_of_closed`, `hasDerivAt_antiderivative_pow_inv_complex`, `PiecewiseC1Path`.
- **Used by**: `hasCauchyPVOn_pow_inv_of_avoids`.
- **Visibility**: public
- **Lines**: 655–666

### `theorem closed_excised_integral_eq_antideriv_diff`
- **Type**: `{γ γ' s k a t_minus t_plus b} (hk : 2 ≤ k) (h_close : γ a = γ b) (smoothness, avoidance, integrability on the two pieces) → integral sum equals antiderivative difference at the excision points`
- **What**: For closed γ with smooth pieces flanking a crossing of `s`, the excised integral sum equals `F(γ(t_minus)) - F(γ(t_plus))` (closure eliminates boundary).
- **How**: Apply `integral_pow_inv_eq_FTC` on each piece; use `h_close` to cancel the endpoint contributions at `a, b`; finish with `ring`.
- **Hypotheses**: closed curve, two smooth pieces with avoidance and integrability.
- **Uses from project**: `integral_pow_inv_eq_FTC`.
- **Used by**: `cpv_excised_tendsto_zero_of_F_diff_zero`.
- **Visibility**: public
- **Lines**: 684–701

### `theorem hasCauchyPVOn_pow_inv_of_avoids`
- **Type**: `{x} (γ : PiecewiseC1Path x x) {s k} (hk : 2 ≤ k) (hδ : ∃ δ > 0, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s‖) (h_int) → HasCauchyPVOn {s} (fun z => 1 / (z-s)^k) γ 0`
- **What**: Higher-order avoidance CPV: for `k ≥ 2` and γ avoiding `s` with margin, CPV of `1/(z-s)^k` is 0.
- **How**: Combine `PiecewiseC1Path.contourIntegral_pow_inv_eq_zero` with `hasCauchyPVOn_of_avoids` (specialised to singleton `{s}`).
- **Hypotheses**: as in signature.
- **Uses from project**: `PiecewiseC1Path.contourIntegral_pow_inv_eq_zero`, `HasCauchyPVOn`, `hasCauchyPVOn_of_avoids`, `PiecewiseC1Path`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 706–727

### `theorem norm_F_diff_le_segment_bound`
- **Type**: `{z₁ z₂ s k ε} (hk : 2 ≤ k) (hε : 0 < ε) (h_seg_avoids : ∀ z ∈ segment ℝ z₁ z₂, ε ≤ ‖z - s‖) → ‖F(z₂) - F(z₁)‖ ≤ (1/ε^k) · ‖z₂ - z₁‖`
- **What**: F-difference Lipschitz bound: if the segment `[z₁, z₂]` stays at distance `≥ ε` from `s`, then `‖F(z₂) - F(z₁)‖ ≤ ‖z₂ - z₁‖ / ε^k`.
- **How**: Use `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` on `segment ℝ z₁ z₂`, with the antiderivative from `hasDerivAt_antiderivative_pow_inv_complex` and the modulus bound `‖1/(z-s)^k‖ ≤ 1/ε^k`.
- **Hypotheses**: `k ≥ 2`, `ε > 0`, segment avoidance.
- **Uses from project**: `hasDerivAt_antiderivative_pow_inv_complex`.
- **Used by**: `norm_F_diff_at_tangent_target_le`.
- **Visibility**: public
- **Lines**: 741–765
- **Notes**: proof >10 lines

### `theorem eventually_re_pos_right`
- **Type**: `{γ t₀ s L} (hL : L ≠ 0) (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_s : γ t₀ = s) → ∀ᶠ t in 𝓝[>] t₀, 0 ≤ ((γ t - s) * conj L).re`
- **What**: Eventually `Re((γ(t)−s)·conj L) ≥ 0` from the right (γ stays in the `+L`-hemisphere).
- **How**: From `HasDerivWithinAt.isLittleO`, bound the chord remainder by `‖L‖/2 · (t-t₀)`. Decompose `γ-s = (t-t₀)•L + R`; the leading term gives `(t-t₀)·‖L‖²`, and the remainder contribution is bounded by `‖L‖/2·(t-t₀)·‖L‖ = (t-t₀)·‖L‖²/2`. Use `nlinarith`.
- **Hypotheses**: `L ≠ 0`, right derivative `L` at `t₀`, `γ(t₀)=s`.
- **Uses from project**: []
- **Used by**: `chord_to_tangent_isLittleO_right`, `F_diff_at_tangent_target_tendsto_zero_right` (indirectly).
- **Visibility**: public
- **Lines**: 783–815
- **Notes**: proof >30 lines

### `theorem eventually_re_neg_left`
- **Type**: Symmetric to `eventually_re_pos_right` for `𝓝[<] t₀` with `≤ 0`.
- **What**: Eventually `Re((γ(t)−s)·conj L) ≤ 0` from the left.
- **How**: Symmetric: leading term `(t-t₀)·‖L‖²` is negative because `t-t₀ < 0`; remainder bounded similarly.
- **Hypotheses**: symmetric.
- **Uses from project**: []
- **Used by**: `chord_to_tangent_isLittleO_left`.
- **Visibility**: public
- **Lines**: 822–854
- **Notes**: proof >30 lines

### `theorem eventually_ne_right`
- **Type**: `{γ t₀ s L} (hL : L ≠ 0) (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_s : γ t₀ = s) → ∀ᶠ t in 𝓝[>] t₀, γ t ≠ s`
- **What**: Eventually `γ(t) ≠ s` from the right with right-derivative `L ≠ 0` at `t₀` (γ does not stay at `s`).
- **How**: If `γ(t) = s = γ(t₀)`, then `γ(t) - γ(t₀) = 0`, so the chord remainder `γ(t) - γ(t₀) - (t-t₀)•L = -(t-t₀)•L` has norm `(t-t₀)·‖L‖`; but the o(t-t₀) bound gives `‖L‖/2 · (t-t₀)`, contradiction by `nlinarith`.
- **Hypotheses**: as in signature.
- **Uses from project**: []
- **Used by**: `chord_to_tangent_isLittleO_right`, `F_diff_at_tangent_target_tendsto_zero_right`.
- **Visibility**: public
- **Lines**: 864–886
- **Notes**: proof >10 lines

### `theorem eventually_ne_left`
- **Type**: Symmetric of `eventually_ne_right` for `𝓝[<] t₀`.
- **What**: Eventually `γ(t) ≠ s` from the left.
- **How**: Symmetric chord-remainder contradiction.
- **Hypotheses**: symmetric.
- **Uses from project**: []
- **Used by**: `chord_to_tangent_isLittleO_left`, `F_diff_at_tangent_target_tendsto_zero_left`.
- **Visibility**: public
- **Lines**: 889–911
- **Notes**: proof >10 lines

### `theorem chord_to_tangent_isLittleO_right`
- **Type**: `{γ t₀ s L n} (h_flat : IsFlatOfOrder γ t₀ n) (hL) (h_deriv) (hL_right) (h_s) → (fun t => ‖γ t - s - (‖γ t - s‖/‖L‖) • L‖) =o[𝓝[>] t₀] (fun t => ‖γ t - s‖^n)`
- **What**: Asymptotic chord-to-tangent: the chord from γ(t) to the natural tangent target on the `+L` ray is `o(‖γ(t)-s‖^n)`.
- **How**: Use `LeanModularForms.orthogonal_deviation_at_radius_right` (orthogonal deviation `o(‖γ-s‖^n)`) and `LeanModularForms.norm_chord_to_tangent_target_le` (pointwise chord bound). Apply `eventually_re_pos_right`/`eventually_ne_right` for the hypotheses of the chord bound. Combine via `IsBigO.trans_isLittleO`.
- **Hypotheses**: flatness, derivative limit, continuous, `γ(t₀)=s`.
- **Uses from project**: `IsFlatOfOrder`, `LeanModularForms.orthogonal_deviation_at_radius_right`, `LeanModularForms.norm_chord_to_tangent_target_le`, `tangentDeviation`, `norm_tangentDeviation_le`, `eventually_re_pos_right`, `eventually_ne_right`.
- **Used by**: `F_diff_at_tangent_target_tendsto_zero_right`.
- **Visibility**: public
- **Lines**: 924–961
- **Notes**: proof >30 lines

### `theorem chord_to_tangent_isLittleO_left`
- **Type**: Symmetric to `_right` for `𝓝[<] t₀` with tangent target on the `-L` ray.
- **What**: Left-side chord-to-tangent asymptotic.
- **How**: Mirror of `_right`, using `_left` variants of orthogonality and chord bound; handle `tangentDeviation _ (-L) = tangentDeviation _ L` via direct unfolding through `normSq_neg` and `Complex.neg_re`.
- **Hypotheses**: symmetric.
- **Uses from project**: `IsFlatOfOrder`, `LeanModularForms.orthogonal_deviation_at_radius_left`, `LeanModularForms.norm_chord_to_tangent_target_le`, `tangentDeviation`, `orthogonalProjectionComplex`, `norm_tangentDeviation_le`, `eventually_re_neg_left`, `eventually_ne_left`.
- **Used by**: `F_diff_at_tangent_target_tendsto_zero_left`.
- **Visibility**: public
- **Lines**: 965–1031
- **Notes**: proof >30 lines

### `theorem norm_sq_segment_to_pole_lower_bound`
- **Type**: `{z₁ z₂ s d} (h₁ : ‖z₁ - s‖ = d) (h₂ : ‖z₂ - s‖ = d) {z} (hz : z ∈ segment ℝ z₁ z₂) → d^2 - ‖z₁ - z₂‖^2 / 4 ≤ ‖z - s‖^2`
- **What**: Segment distance to pole: if z₁, z₂ are equidistant from `s` (distance `d`), every point on segment `[z₁, z₂]` is at distance ≥ `√(d² - ‖z₁-z₂‖²/4)` from `s`.
- **How**: Convex combination `z = α z₁ + β z₂` with `α + β = 1`; expand `‖z-s‖²` via `Complex.normSq_add`/`normSq_mul`; use `Complex.normSq_sub` to get `cross term = (d² + d² - ‖z₁-z₂‖²)/2`. AM-GM `αβ ≤ 1/4` from `(α-β)² ≥ 0`. Finish with `nlinarith`.
- **Hypotheses**: `‖z₁ - s‖ = ‖z₂ - s‖ = d`.
- **Uses from project**: []
- **Used by**: `norm_segment_to_pole_lower_bound_half`.
- **Visibility**: public
- **Lines**: 1049–1093
- **Notes**: proof >30 lines

### `theorem norm_segment_to_pole_lower_bound_half`
- **Type**: `{z₁ z₂ s d} (_hd_pos) (h₁) (h₂) (h_chord : ‖z₁ - z₂‖ ≤ d) {z} (hz) → d / 2 ≤ ‖z - s‖`
- **What**: Corollary: if `‖z₁-z₂‖ ≤ d`, every segment point is at distance ≥ `d/2` from `s`.
- **How**: Apply `norm_sq_segment_to_pole_lower_bound`; derive `(d/2)² ≤ ‖z-s‖²` via `mul_self_le_mul_self`; take square root via `abs_le_of_sq_le_sq'`.
- **Hypotheses**: equidistance, chord short.
- **Uses from project**: `norm_sq_segment_to_pole_lower_bound`.
- **Used by**: `norm_F_diff_at_tangent_target_le`.
- **Visibility**: public
- **Lines**: 1097–1106

### `theorem norm_F_diff_at_tangent_target_le`
- **Type**: `{γ t s L k} (hk : 2 ≤ k) (hL) (hw_ne : γ t ≠ s) (h_chord_le) → ‖F(γ t) - F(target)‖ ≤ (1/(‖γ t - s‖/2)^k) · ‖chord‖`
- **What**: F-difference bound between γ(t) and the tangent target `s + (‖γ t - s‖/‖L‖)•L`: uses the segment-distance lower bound and the segment Lipschitz bound.
- **How**: Set `d := ‖γ t - s‖`; verify the tangent target has `‖tgt - s‖ = d`; apply `norm_segment_to_pole_lower_bound_half` and `norm_F_diff_le_segment_bound`.
- **Hypotheses**: γ(t) ≠ s, chord short.
- **Uses from project**: `norm_segment_to_pole_lower_bound_half`, `norm_F_diff_le_segment_bound`.
- **Used by**: `F_diff_at_tangent_target_tendsto_zero_right`, `F_diff_at_tangent_target_tendsto_zero_left`.
- **Visibility**: public
- **Lines**: 1116–1140
- **Notes**: proof >10 lines

### `theorem tendsto_div_pow_zero_of_isLittleO`
- **Type**: `{chord d : ℝ → ℝ} {l n k} (h_chord : chord =o[l] (fun t => d t ^ n)) (h_d : Tendsto d l (𝓝 0)) (h_d_pos : ∀ᶠ t in l, 0 < d t) (hkn : k ≤ n) → Tendsto (fun t => chord t / d t ^ k) l (𝓝 0)`
- **What**: Abstract asymptotic ratio: if `chord = o(d^n)` and `d → 0⁺`, then `chord/d^k → 0` for `k ≤ n`.
- **How**: For each `ε > 0`, the chord bound gives `|chord| ≤ ε/2 · d^n`; for `d < 1` eventually, `d^(n-k) ≤ 1`; combine to get `|chord|/d^k ≤ ε/2 · d^(n-k) ≤ ε/2 < ε`.
- **Hypotheses**: littleO, `d → 0`, eventually `d > 0`, `k ≤ n`.
- **Uses from project**: []
- **Used by**: `F_diff_at_tangent_target_tendsto_zero_right`, `F_diff_at_tangent_target_tendsto_zero_left`.
- **Visibility**: public
- **Lines**: 1147–1175
- **Notes**: proof >10 lines

### `theorem F_diff_at_tangent_target_tendsto_zero_right`
- **Type**: `{γ t₀ s L n k} (h_flat : IsFlatOfOrder γ t₀ n) (hL) (h_deriv) (hL_right) (h_s) (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n) → Tendsto (fun t => ‖F(γ t) - F(tangent target on +L)‖) (𝓝[>] t₀) (𝓝 0)`
- **What**: Main asymptotic theorem: F-difference at the tangent target tends to 0 from the right under HW's flatness `n ≥ k ≥ 2`.
- **How**: Combine `chord_to_tangent_isLittleO_right` (chord = o(d^n)), `tendsto_div_pow_zero_of_isLittleO` (chord/d^k → 0), `norm_F_diff_at_tangent_target_le` (F-diff ≤ 2^k · chord/d^k), and the squeeze theorem `tendsto_of_tendsto_of_tendsto_of_le_of_le'`.
- **Hypotheses**: flatness order `n`, right derivative `L ≠ 0`, `k ∈ [2, n]`, `n ≥ 1`.
- **Uses from project**: `IsFlatOfOrder`, `chord_to_tangent_isLittleO_right`, `tendsto_div_pow_zero_of_isLittleO`, `norm_F_diff_at_tangent_target_le`, `eventually_ne_right`.
- **Used by**: `F_curve_diff_tendsto_zero_odd`.
- **Visibility**: public
- **Lines**: 1192–1247
- **Notes**: proof >30 lines

### `theorem F_diff_at_tangent_target_tendsto_zero_left`
- **Type**: Symmetric to `_right` for `𝓝[<] t₀` with tangent target on `-L`.
- **What**: Same asymptotic theorem on the left side.
- **How**: Mirror of `_right`.
- **Hypotheses**: symmetric.
- **Uses from project**: `IsFlatOfOrder`, `chord_to_tangent_isLittleO_left`, `tendsto_div_pow_zero_of_isLittleO`, `norm_F_diff_at_tangent_target_le`, `eventually_ne_left`.
- **Used by**: `F_curve_diff_tendsto_zero_odd`.
- **Visibility**: public
- **Lines**: 1253–1311
- **Notes**: proof >30 lines

### `theorem F_line_diff_eq_zero_of_odd`
- **Type**: `(s L : ℂ) (k : ℕ) (hk : 2 ≤ k) (hk_odd : Odd k) (ε : ℝ) → F(s - (ε/‖L‖)•L) = F(s + (ε/‖L‖)•L)`
- **What**: For odd `k`, the line-model F-values at the two symmetric exit-points are equal (line PV = 0 by symmetry).
- **How**: `(k - 1)` is even for odd `k`; rewrite `(-x)^(k-1) = x^(k-1)` via `neg_pow` and `Even.neg_one_pow`.
- **Hypotheses**: odd `k ≥ 2`.
- **Uses from project**: []
- **Used by**: `F_curve_diff_tendsto_zero_odd`.
- **Visibility**: public
- **Lines**: 1324–1337

### `theorem F_curve_diff_tendsto_zero_odd`
- **Type**: `{γ t₀ s L n k} (h_flat) (hL) (h_deriv_right) (h_deriv_left) (hL_right) (hL_left) (h_s) (hk : 2 ≤ k) (hk_odd : Odd k) (hkn : k ≤ n) (hn1) (t_eps_plus t_eps_minus : ℝ → ℝ) (h_plus_to) (h_plus_radius) (h_minus_to) (h_minus_radius) → Tendsto (fun ε => ‖F(γ(t_eps_minus ε)) - F(γ(t_eps_plus ε))‖) (𝓝[>] 0) (𝓝 0)`
- **What**: Combined curve F-difference → 0 for odd `k`: with both-side F-diff tending to 0 (via `_left`/`_right` versions) and the line F-diff being 0 (odd-power symmetry), the curve F-diff at the exit points tends to 0.
- **How**: Compose `F_diff_at_tangent_target_tendsto_zero_{right,left}` with the exit-time maps; sum the two via `Tendsto.add`; use triangle inequality through the common line target (where `F_line_diff_eq_zero_of_odd` gives the line F-diff = 0).
- **Hypotheses**: flat γ, both-side derivative limits, exit-time functions parametrizing γ at radius ε.
- **Uses from project**: `IsFlatOfOrder`, `F_diff_at_tangent_target_tendsto_zero_right`, `F_diff_at_tangent_target_tendsto_zero_left`, `F_line_diff_eq_zero_of_odd`.
- **Used by**: `hw_theorem_3_3_odd_transverse_parametric`.
- **Visibility**: public
- **Lines**: 1361–1413
- **Notes**: proof >30 lines

### `theorem cpv_excised_tendsto_zero_of_F_diff_zero`
- **Type**: `{γ γ' a b s k} (h_close : γ a = γ b) (hk : 2 ≤ k) (t_eps_plus t_eps_minus : ℝ → ℝ) (smoothness, avoidance, integrability hypotheses on both pieces) (h_F_diff_to_zero) → Tendsto (excised integral) (𝓝[>] 0) (𝓝 0)`
- **What**: If the curve F-difference at the excision boundaries tends to 0, the parameter-excised integral tends to 0.
- **How**: Rewrite `Tendsto _ 0` as norm `→ 0`; use `closed_excised_integral_eq_antideriv_diff` to identify the integral with the F-difference; then use the hypothesis `h_F_diff_to_zero` via `Tendsto.congr'`.
- **Hypotheses**: closed γ, smooth + avoidance + integrability on each piece, F-diff hypothesis.
- **Uses from project**: `closed_excised_integral_eq_antideriv_diff`.
- **Used by**: `hw_theorem_3_3_odd_transverse_parametric`.
- **Visibility**: public
- **Lines**: 1425–1456
- **Notes**: proof >10 lines

### `theorem hw_theorem_3_3_odd_transverse_parametric`
- **Type**: Full HW Theorem 3.3 (k-odd transverse): closed γ flat of order `n ≥ k` (odd), crossing `s` transversely at `t₀`, with exit-time functions and the integrability hypotheses, has excised integral tending to 0.
- **What**: The headline HW eq. (3.4) formalisation for k-odd transverse, fully proven from `F_curve_diff_tendsto_zero_odd` and `cpv_excised_tendsto_zero_of_F_diff_zero`.
- **How**: Direct composition of `cpv_excised_tendsto_zero_of_F_diff_zero` (using the smoothness/avoidance hypotheses) with `F_curve_diff_tendsto_zero_odd` (giving the F-diff → 0 conclusion).
- **Hypotheses**: closed flat γ with both-side derivatives, exit-time functions parametrizing γ at radius ε, smoothness/avoidance/integrability of both pieces.
- **Uses from project**: `IsFlatOfOrder`, `F_curve_diff_tendsto_zero_odd`, `cpv_excised_tendsto_zero_of_F_diff_zero`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1481–1513

---

### File Summary
- **Total declarations**: 38 theorems.
- **Key API (used by 3+ others in this file)**: `hCancel_of_avoids` (used by `hCancel_of_holomorphic_agree`, `hCancel_of_simplePoles_avoids`, `hCancel_of_contourIntegral_zero` chain); `IsFlatOfOrder`-based asymptotic chain (`chord_to_tangent_isLittleO_*` → `F_diff_at_tangent_target_tendsto_zero_*` → `F_curve_diff_tendsto_zero_odd` → `hw_theorem_3_3_odd_transverse_parametric`); `hasDerivAt_antiderivative_pow_inv_complex` (used by `PiecewiseC1Path.contourIntegral_pow_inv_eq_zero` and `norm_F_diff_le_segment_bound`); `eventually_ne_right`/`eventually_ne_left` (each used twice). No single declaration is used 3+ times within the file; the API is structured as a near-linear chain of phase steps.
- **Unused in this file**: `hCancel_of_holomorphic_convex`, `hCancel_of_simplePoles_avoids`, `higherOrder_sector_cancel_odd`, `higherOrder_sector_cancel_even_of_flat`, `hCancel_simplePoles_convex'`, `conditionB_higherOrder_factor_eq`, `odd_power_pv_vanishes`, `hCancel_of_simplePoles_convex_full`, `hCancel_structural_gateway`, `generalizedResidueTheorem_with_hCancel`, `hasCauchyPVOn_empty_eq`, `hCancel_of_empty_convex`, `hCancel_of_remainder_eq`, `hasCauchyPVOn_pow_inv_of_avoids`, `hw_theorem_3_3_odd_transverse_parametric` (this is the terminal public API; consumed by downstream files).
- **Declarations with sorry**: none.
- **Declarations with set_option**: none.
- **Proofs >30 lines**: `tangentApproximation_of_isFlatOfOrder_right`, `tangentApproximation_of_isFlatOfOrder_left`, `eventually_re_pos_right`, `eventually_re_neg_left`, `chord_to_tangent_isLittleO_right`, `chord_to_tangent_isLittleO_left`, `norm_sq_segment_to_pole_lower_bound`, `F_diff_at_tangent_target_tendsto_zero_right`, `F_diff_at_tangent_target_tendsto_zero_left`, `F_curve_diff_tendsto_zero_odd`.
- **File purpose**: This file assembles the discharge of `hCancel` for the generalized residue theorem under Hungerbühler–Wasem conditions (A')+(B). It contains three layers: (1) a family of avoidance/decomposition/holomorphic-agreement lemmas (`hCancel_of_avoids`, `hCancel_of_holomorphic_convex`, `hCancel_of_decomposition`, `hCancel_structural_gateway`) that show how `HasCauchyPVOn` of a remainder reduces to vanishing of an associated contour integral; (2) the Phase 3 analytical kernel — antiderivative formula `F = -1/((k-1)(z-s)^(k-1))` for `k ≥ 2`, with the Phase 3.5/3.6/3.7/3.8 chain culminating in `F_diff_at_tangent_target_tendsto_zero_{right,left}` (chord-to-tangent + segment-distance + segment Lipschitz + squeeze) and `F_curve_diff_tendsto_zero_odd` (combining both sides with the line-symmetric cancellation for odd `k`); (3) the headline theorem `hw_theorem_3_3_odd_transverse_parametric`, which combines these into the full HW eq. (3.4) "excised integral → 0 as ε → 0⁺" statement for k-odd transverse crossings with flatness order `n ≥ k`. There is significant duplicate API between `hCancel_simplePoles_convex'` and `hCancel_of_simplePoles_convex_full`.
