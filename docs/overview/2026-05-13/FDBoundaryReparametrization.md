# Inventory: FDBoundaryReparametrization.lean

### `theorem fdBoundaryFun_eq_fdBoundary_H_scaled`
- **Type**: `(H t : ℝ) → fdBoundaryFun H t = fdBoundary_H H (5*t)`
- **What**: Reparametrization identity: the `[0,1]`-parametrized FD boundary equals the `[0,5]`-parametrized version composed with `t ↦ 5t`.
- **How**: 27 lines — unfold both, four nested `by_cases` matching the five piecewise pieces `t ≤ 1/5, 2/5, 3/5, 4/5`; each branch applies `if_pos`/`if_neg` with `linarith` on `5*t`, then `push_cast; ring`.
- **Hypotheses**: none
- **Uses from project**: `fdBoundaryFun`, `fdBoundary_H`
- **Used by**: `fdBoundaryFun_eq_comp`, `cpvIntegrand_fdBoundaryFun_eq_smul_cpvIntegrand_fdBoundary_H`, `cpvIntegrandOn_fdBoundaryFun_eq_smul_fdBoundary_H`
- **Visibility**: public
- **Lines**: 38-64
- **Notes**: >10 lines

### `theorem fdBoundaryFun_eq_comp`
- **Type**: `(H : ℝ) → fdBoundaryFun H = fun t => fdBoundary_H H (5*t)`
- **What**: Same identity as a function-extensional composition.
- **How**: `funext` then apply `fdBoundaryFun_eq_fdBoundary_H_scaled`.
- **Hypotheses**: none
- **Uses from project**: `fdBoundaryFun`, `fdBoundary_H`, `fdBoundaryFun_eq_fdBoundary_H_scaled`
- **Used by**: `deriv_fdBoundaryFun_eq_five_deriv_fdBoundary_H`
- **Visibility**: public
- **Lines**: 67-69
- **Notes**: none

### `theorem integral_zero_to_five_eq_five_smul_zero_to_one`
- **Type**: `(F : ℝ → ℂ) → ∫ u in 0..5, F u = (5 : ℝ) • ∫ t in 0..1, F (5*t)`
- **What**: Linear change of variable: `∫₀⁵ F = 5 · ∫₀¹ F(5·)`.
- **How**: Specialize `intervalIntegral.smul_integral_comp_mul_add` with `c=5, d=0, a=0, b=1`, then `simpa`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun`, `integral_cpvIntegrandOn_fdBoundary_H_eq_fdBoundaryFun`
- **Visibility**: public
- **Lines**: 78-81
- **Notes**: none

### `theorem deriv_fdBoundaryFun_eq_five_deriv_fdBoundary_H`
- **Type**: `(H t : ℝ) → deriv (fdBoundaryFun H) t = (5 : ℝ) • deriv (fdBoundary_H H) (5*t)`
- **What**: Chain-rule version of reparametrization at the level of derivatives (ℝ-scalar).
- **How**: `rw [fdBoundaryFun_eq_comp]` then `deriv_comp_mul_left`.
- **Hypotheses**: none
- **Uses from project**: `fdBoundaryFun_eq_comp`, `fdBoundary_H`
- **Used by**: `deriv_fdBoundaryFun_eq`
- **Visibility**: public
- **Lines**: 89-92
- **Notes**: relies on `deriv_comp_mul_left` for non-diff case uniformly

### `theorem deriv_fdBoundaryFun_eq`
- **Type**: `(H t : ℝ) → deriv (fdBoundaryFun H) t = (5 : ℂ) * deriv (fdBoundary_H H) (5*t)`
- **What**: Complex version of the derivative reparametrization.
- **How**: `rw [deriv_fdBoundaryFun_eq_five_deriv_fdBoundary_H, Complex.real_smul]; push_cast; ring`.
- **Hypotheses**: none
- **Uses from project**: `deriv_fdBoundaryFun_eq_five_deriv_fdBoundary_H`, `fdBoundary_H`
- **Used by**: `cpvIntegrand_fdBoundaryFun_eq_smul_cpvIntegrand_fdBoundary_H`, `cpvIntegrandOn_fdBoundaryFun_eq_smul_fdBoundary_H`
- **Visibility**: public
- **Lines**: 95-99
- **Notes**: none

### `theorem cpvIntegrand_fdBoundaryFun_eq_smul_cpvIntegrand_fdBoundary_H`
- **Type**: `cpvIntegrand f (fdBoundaryFun H) z₀ ε t = 5 · (if … then f(fdBoundary_H H (5t)) · deriv(fdBoundary_H H)(5t) else 0)`
- **What**: New-chain CPV integrand at `t` equals 5 times the old-chain integrand at `5t`.
- **How**: Unfold `cpvIntegrand`; rewrite via `fdBoundaryFun_eq_fdBoundary_H_scaled` and `deriv_fdBoundaryFun_eq`; `split_ifs <;> ring`.
- **Hypotheses**: none
- **Uses from project**: `cpvIntegrand`, `fdBoundaryFun`, `fdBoundary_H`, `fdBoundaryFun_eq_fdBoundary_H_scaled`, `deriv_fdBoundaryFun_eq`
- **Used by**: `integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun`
- **Visibility**: public
- **Lines**: 109-116
- **Notes**: none

### `theorem integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun`
- **Type**: `∫_{0}^{5} (old integrand) = ∫_{0}^{1} cpvIntegrand f (fdBoundaryFun H) z₀ ε`
- **What**: Integral change of variables: the old-chain `[0,5]` CPV integral equals the new-chain `[0,1]` CPV integral.
- **How**: 12 lines — rewrite LHS via `integral_zero_to_five_eq_five_smul_zero_to_one`, pull constant out via `intervalIntegral.integral_const_mul`; close with `integral_congr` and `cpvIntegrand_fdBoundaryFun_eq_smul_cpvIntegrand_fdBoundary_H`.
- **Hypotheses**: none
- **Uses from project**: `cpvIntegrand`, `fdBoundaryFun`, `fdBoundary_H`, `integral_zero_to_five_eq_five_smul_zero_to_one`, `cpvIntegrand_fdBoundaryFun_eq_smul_cpvIntegrand_fdBoundary_H`
- **Used by**: `hasCauchyPV_of_cauchyPV'_tendsto`, `generalizedWindingNumberPrime_eq_of_hasGeneralizedWindingNumber`
- **Visibility**: public
- **Lines**: 120-137
- **Notes**: >10 lines

### `lemma extend_eventuallyEq_fdBoundaryFun`
- **Type**: `(γ ext)(s) = fdBoundaryFun H s` on a punctured nbhd of `t ∈ Ioo 0 1`
- **What**: A `PiecewiseC1Path` agreeing with `fdBoundaryFun H` on `[0,1]` is eventually equal to it at interior points.
- **How**: `filter_upwards [Ioo_mem_nhds ht.1 ht.2]`; apply `hγ` using `Ioo_subset_Icc_self`.
- **Hypotheses**: `γ : PiecewiseC1Path (fdStart H) (fdStart H)`, agreement on `Icc 0 1`, `t ∈ Ioo 0 1`
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`
- **Used by**: `hasCauchyPV_of_cauchyPV'_tendsto`, `hasCauchyPVOn_of_cauchyPVOn'_tendsto`, `generalizedWindingNumberPrime_eq_of_hasGeneralizedWindingNumber`
- **Visibility**: private
- **Lines**: 143-149
- **Notes**: none

### `theorem hasCauchyPV_of_cauchyPV'_tendsto`
- **Type**: from old-chain `Tendsto` of CPV-of-(z-z₀)⁻¹ integral on `[0,5]` to new-chain `HasCauchyPV (·-z₀)⁻¹ γ z₀ L`
- **What**: Bridges old-chain `cauchyPrincipalValueExists'` to new-chain `HasCauchyPV` for the Cauchy kernel.
- **How**: 18 lines — for each `ε`, rewrite old integral as new integrand integral via `integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun`; use `integral_congr_ae` filtering off `{1}`; on `Ioo 0 1` use `hγ`, `cpvIntegrand` simp and `extend_eventuallyEq_fdBoundaryFun ... .deriv_eq`; conclude via `h_old.congr h_eq`.
- **Hypotheses**: `γ` agrees with `fdBoundaryFun H` on `[0,1]`, old-chain CPV tendsto `L`
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `fdBoundary_H`, `HasCauchyPV`, `cpvIntegrand`, `integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun`, `extend_eventuallyEq_fdBoundaryFun`
- **Used by**: `hasGeneralizedWindingNumber_of_cauchyPrincipalValueExists'_tendsto`
- **Visibility**: public
- **Lines**: 158-185
- **Notes**: >10 lines; key lemma `intervalIntegral.integral_congr_ae`, `Filter.Tendsto.congr`

### `theorem cpvIntegrandOn_fdBoundaryFun_eq_smul_fdBoundary_H`
- **Type**: `cpvIntegrandOn S f (fdBoundaryFun H) ε t = 5 · (if ∃ s ∈ S, ‖...-s‖ ≤ ε then 0 else ...)`
- **What**: Multi-point analogue of `cpvIntegrand_fdBoundaryFun_eq_smul_cpvIntegrand_fdBoundary_H`.
- **How**: Unfold `cpvIntegrandOn`; rewrite via reparametrization; `split_ifs <;> ring`.
- **Hypotheses**: none
- **Uses from project**: `cpvIntegrandOn`, `fdBoundaryFun`, `fdBoundary_H`, `fdBoundaryFun_eq_fdBoundary_H_scaled`, `deriv_fdBoundaryFun_eq`
- **Used by**: `integral_cpvIntegrandOn_fdBoundary_H_eq_fdBoundaryFun`
- **Visibility**: public
- **Lines**: 191-198
- **Notes**: none

### `theorem integral_cpvIntegrandOn_fdBoundary_H_eq_fdBoundaryFun`
- **Type**: `∫₀⁵ (multi-pt old integrand) = ∫₀¹ cpvIntegrandOn S f (fdBoundaryFun H) ε`
- **What**: Multi-point integral change of variables.
- **How**: 13 lines — same pattern as `integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun` using `cpvIntegrandOn_fdBoundaryFun_eq_smul_fdBoundary_H`.
- **Hypotheses**: none
- **Uses from project**: `cpvIntegrandOn`, `fdBoundaryFun`, `fdBoundary_H`, `integral_zero_to_five_eq_five_smul_zero_to_one`, `cpvIntegrandOn_fdBoundaryFun_eq_smul_fdBoundary_H`
- **Used by**: `hasCauchyPVOn_of_cauchyPVOn'_tendsto`
- **Visibility**: public
- **Lines**: 203-220
- **Notes**: >10 lines

### `theorem hasCauchyPVOn_of_cauchyPVOn'_tendsto`
- **Type**: from old-chain multi-point CPV `Tendsto` on `[0,5]` to new-chain `HasCauchyPVOn S f γ L`
- **What**: Multi-point analogue of `hasCauchyPV_of_cauchyPV'_tendsto`.
- **How**: 18 lines — for each `ε` rewrite old integral as new `cpvIntegrandOn` integral; `integral_congr_ae` filter off `{1}`; on `Ioo 0 1` use `hγ` + `extend_eventuallyEq_fdBoundaryFun ... .deriv_eq`.
- **Hypotheses**: `γ` agrees with `fdBoundaryFun H` on `[0,1]`, old-chain multi-point CPV tendsto `L`
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `fdBoundary_H`, `HasCauchyPVOn`, `cpvIntegrandOn`, `integral_cpvIntegrandOn_fdBoundary_H_eq_fdBoundaryFun`, `extend_eventuallyEq_fdBoundaryFun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 225-251
- **Notes**: >10 lines; same pattern as single-point case

### `theorem hasGeneralizedWindingNumber_of_cauchyPrincipalValueExists'_tendsto`
- **Type**: from old-chain `Tendsto` to `2πi·w` infer new-chain `HasGeneralizedWindingNumber γ z₀ w`
- **What**: Bridge from old-chain CPV-tendsto-to-`2πi·w` directly to new-chain `HasGeneralizedWindingNumber`.
- **How**: Unfold `HasGeneralizedWindingNumber`; apply `hasCauchyPV_of_cauchyPV'_tendsto`.
- **Hypotheses**: `γ` agrees with `fdBoundaryFun H`, old-chain limit is `2πi·w`
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `fdBoundary_H`, `HasGeneralizedWindingNumber`, `hasCauchyPV_of_cauchyPV'_tendsto`
- **Used by**: `generalizedWindingNumber_eq_of_agreement`
- **Visibility**: public
- **Lines**: 257-269
- **Notes**: none

### `theorem generalizedWindingNumber_eq_of_agreement`
- **Type**: same setup → `generalizedWindingNumber γ z₀ = w`
- **What**: Specializes the previous bridge to extract `generalizedWindingNumber γ z₀ = w`.
- **How**: Apply `hasGeneralizedWindingNumber_of_cauchyPrincipalValueExists'_tendsto`, then take `.eq`.
- **Hypotheses**: same as above
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `fdBoundary_H`, `generalizedWindingNumber`, `hasGeneralizedWindingNumber_of_cauchyPrincipalValueExists'_tendsto`
- **Used by**: `generalizedWindingNumber_eq_generalizedWindingNumber'`
- **Visibility**: public
- **Lines**: 273-286
- **Notes**: none

### `theorem generalizedWindingNumberPrime_eq_of_hasGeneralizedWindingNumber`
- **Type**: from new-chain `HasGeneralizedWindingNumber γ z₀ w` to `generalizedWindingNumber' (fdBoundary_H H) 0 5 z₀ = w`
- **What**: Reverse bridge: a new-chain winding-number value implies the old-chain parametrization gives the same value.
- **How**: 23 lines — unfold `HasGeneralizedWindingNumber, HasCauchyPV`; show ∀ε, the new-chain `cpvIntegrand` integral equals the old-chain integral by `integral_congr_ae` + `extend_eventuallyEq_fdBoundaryFun.symm.deriv_eq` + `integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun`; conclude `cauchyPrincipalValue' (·⁻¹)` equals `2πi·w` via `Tendsto.limUnder_eq`; deduce `generalizedWindingNumber' = w` via `field_simp [two_pi_I_ne_zero]`.
- **Hypotheses**: `γ` agrees with `fdBoundaryFun H` on `[0,1]`, `HasGeneralizedWindingNumber γ z₀ w`
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `fdBoundary_H`, `HasGeneralizedWindingNumber`, `HasCauchyPV`, `cpvIntegrand`, `generalizedWindingNumber'`, `cauchyPrincipalValue'`, `integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun`, `extend_eventuallyEq_fdBoundaryFun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 293-327
- **Notes**: >10 lines; key tactic `Tendsto.limUnder_eq`, `field_simp [Complex.two_pi_I_ne_zero]`

### `theorem generalizedWindingNumber_eq_generalizedWindingNumber'`
- **Type**: `cauchyPrincipalValueExists'` → `generalizedWindingNumber γ z₀ = generalizedWindingNumber' (fdBoundary_H H) 0 5 z₀`
- **What**: When the old chain's CPV exists, the new-chain winding number equals the old-chain `generalizedWindingNumber'`.
- **How**: 18 lines — extract `L` from old CPV existence; set `w := (2πI)⁻¹·L`; obtain old-chain `Tendsto _ (𝓝 (2πI·w))` via `congr'` on `deriv_sub_const`; old-chain `generalizedWindingNumber' = w` by `Tendsto.limUnder_eq`; apply `generalizedWindingNumber_eq_of_agreement`.
- **Hypotheses**: `γ` agrees with `fdBoundaryFun H` on `[0,1]`, `CauchyPrincipalValueExists' (·⁻¹) (· - z₀) 0 5 0`
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `fdBoundary_H`, `generalizedWindingNumber`, `generalizedWindingNumber'`, `CauchyPrincipalValueExists'`, `cauchyPrincipalValue'`, `generalizedWindingNumber_eq_of_agreement`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 332-358
- **Notes**: >10 lines; key tactic `Tendsto.limUnder_eq`, `field_simp [Complex.two_pi_I_ne_zero]`

## File Summary
- 16 declarations: 15 public theorems + 1 private helper lemma. All concern the linear reparametrization `t ↦ 5t` bridging `[0,1]` (`fdBoundaryFun`) and `[0,5]` (`fdBoundary_H`) parametrizations.
- Layered API: base reparametrization (function, derivative, integral CoV) → single-point CPV bridge → multi-point CPV bridge → winding-number equivalence (both directions).
- No sorries, no axioms, no `set_option`. `noncomputable section`.
