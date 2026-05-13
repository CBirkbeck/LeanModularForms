# Inventory: Residue/GeneralizedTheoremBase.lean

### `private lemma cpv_crossing_null`
- **Type**: `(S0 : Finset ℂ) (γ : PiecewiseC1Immersion) : volume {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t ∈ (S0 : Set ℂ)} = 0`
- **What**: The preimage of a finite singular set under a piecewise-C¹ immersion has Lebesgue measure zero.
- **How**: Write the preimage as `⋃ s ∈ S0, {t | t ∈ [a,b] ∧ γ t = s}`. Each fiber has measure zero by `preimage_singleton_measure_zero_of_deriv_ne_zero` (since `γ.deriv_ne_zero`). Apply `measure_biUnion_null_iff`.
- **Hypotheses**: piecewise-C¹ immersion (i.e. nonzero derivative off partition).
- **Uses from project**: `PiecewiseC1Immersion`, `preimage_singleton_measure_zero_of_deriv_ne_zero`
- **Used by**: `cpv_cauchy_of_sum_and_regular`, `cauchyPrincipalValueOn_singular_sum`, `cpv_eq_sum_single_pole_cpvs`.
- **Visibility**: private
- **Lines**: 43–65
- **Notes**: >10 lines (~23); key lemma `measure_biUnion_null_iff`.

### `private lemma finset_min_sep`
- **Type**: `(S0 : Finset ℂ) (hS0_nonempty : S0.Nonempty) : ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖`
- **What**: A finite set of points in ℂ admits a uniform minimum pairwise separation.
- **How**: Case `card = 1`: take `δ = 1` (vacuously holds). Else exhibit `(s₁, s₂)` distinct. Take `δ := Finset.exists_min_image` over `(S0 ×ˢ S0).filter (·.1 ≠ ·.2) |>.image (‖·.2 - ·.1‖)`. Positivity from `h_pos`, lower-bound from `hδ_min`.
- **Hypotheses**: `S0` nonempty.
- **Uses from project**: []
- **Used by**: `cpv_cauchy_of_sum_and_regular`, `cpv_eq_sum_single_pole_cpvs`.
- **Visibility**: private
- **Lines**: 67–111
- **Notes**: >10 lines (~45); key lemma `Finset.exists_min_image`.

### `private lemma cpv_cauchy_of_sum_and_regular`
- **Type**: `(S0) (f) (γ) (hS0_nonempty) (hPV_each : ∀ s ∈ S0, CauchyPrincipalValueExists' (c_s/(z-s)) γ.toFun a b s) (hg_reg_cont : ContinuousOn (regular part) (γ '' Icc a b)) : Cauchy (map (∫ … cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) (𝓝[>] 0))`
- **What**: The full multi-point CPV filter is Cauchy: the sum of individual CPV terms plus the regular-part integral provides convergence.
- **How**: Choose `L_fn` for each singular pole CPV. Sum to `L`. Apply `tendsto_finset_sum` for the sum. The "regular minus singular" difference tends to the integral of the regular part by `multipointPV_diff_tendsto` (using `cpv_crossing_null`, `finset_min_sep`). Add the two limits; `Tendsto.cauchy_map` concludes.
- **Hypotheses**: `S0` nonempty, each singular CPV exists, regular part continuous on the image.
- **Uses from project**: `cpv_crossing_null`, `finset_min_sep`, `multipointPV_diff_tendsto`, `CauchyPrincipalValueExists'`, `cauchyPrincipalValueIntegrandOn`, `residueSimplePole`, `PiecewiseC1Immersion`
- **Used by**: `cauchyPrincipalValueOn_singular_sum`.
- **Visibility**: private
- **Lines**: 115–167
- **Notes**: >10 lines (~53); key lemma `multipointPV_diff_tendsto`.

### `lemma cauchyPrincipalValueOn_singular_sum`
- **Type**: `(S0) (f) (γ) (_hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s) (hPV_each) (hg_reg_cont) : CauchyPrincipalValueExistsOn S0 f γ.toFun γ.a γ.b`
- **What**: Multi-point CPV exists when each singular contribution has its own CPV.
- **How**: Case `S0 = ∅`: CPV reduces to the constant integral. Case `S0` nonempty: invoke `cpv_cauchy_of_sum_and_regular` and use `CompleteSpace.complete` to extract a limit.
- **Hypotheses**: simple poles, each pole has CPV, regular part continuous on image.
- **Uses from project**: `CauchyPrincipalValueExistsOn`, `cauchyPrincipalValueIntegrandOn`, `cpv_cauchy_of_sum_and_regular`, `HasSimplePoleAt`, `CauchyPrincipalValueExists'`, `PiecewiseC1Immersion`, `residueSimplePole`
- **Used by**: `generalizedResidueTheorem'`, `cpv_eq_sum_single_pole_cpvs`.
- **Visibility**: public
- **Lines**: 170–193

### `private lemma holomorphic_closed_integral_zero`
- **Type**: `(U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U) (g : ℂ → ℂ) (hg_diff : DifferentiableOn ℂ g U) (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) (hg_cont_on_image : ContinuousOn g (γ.toFun '' Icc γ.a γ.b)) : ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0`
- **What**: The integral of a holomorphic function on `U` along a closed piecewise-C¹ immersion vanishes (Cauchy's theorem on a convex domain).
- **How**: Take `F` a holomorphic primitive of `g` on `U` (`holomorphic_convex_primitive`). `F ∘ γ` is continuous on `[a,b]` and has derivative `g(γ(t)) · γ'(t)` off the partition (via composition `(hF).comp_of_eq` with `γ.smooth_off_partition.hasDerivAt`). `IntervalIntegrable` via `piecewiseC1_deriv_intervalIntegrable`. FTC `integral_eq_of_hasDerivAt_off_countable_of_le` gives `F(γ b) - F(γ a) = 0` since `γ` is closed.
- **Hypotheses**: convex open `U`, holomorphic `g`, closed PC1 immersion in `U`.
- **Uses from project**: `PiecewiseC1Immersion`, `PiecewiseC1Curve.IsClosed`, `holomorphic_convex_primitive`, `piecewiseC1_deriv_intervalIntegrable`, `piecewiseC1Immersion_deriv_bounded`
- **Used by**: `generalizedResidueTheorem'`.
- **Visibility**: private
- **Lines**: 195–240
- **Notes**: >10 lines (~46); key lemmas `holomorphic_convex_primitive`, `integral_eq_of_hasDerivAt_off_countable_of_le`.

### `private lemma cpv_integral_factor_const`
- **Type**: `(γ : PiecewiseC1Immersion) (s c : ℂ) : ∀ ε, (∫ t in γ.a..γ.b, if ‖γ.toFun t - s‖ > ε then (c/(γ.toFun t - s)) · deriv γ.toFun t else 0) = c · (∫ t in γ.a..γ.b, if ‖γ.toFun t - s‖ > ε then (γ.toFun t - s)⁻¹ · deriv γ.toFun t else 0)`
- **What**: The CPV integral of `c/(z-s)` factors as `c` times the integral of `1/(z-s)`.
- **How**: `intervalIntegral.integral_smul` (used via `← smul_eq_mul, ← integral_smul`). `integral_congr` with branch arithmetic.
- **Hypotheses**: none.
- **Uses from project**: `PiecewiseC1Immersion`
- **Used by**: `single_pole_pv_base_exists`.
- **Visibility**: private
- **Lines**: 244–260

### `private lemma single_pole_pv_base_exists`
- **Type**: `(γ) (s c) (hc : c ≠ 0) (hPV : CauchyPrincipalValueExists' (c/(z-s)) γ.toFun γ.a γ.b s) : ∃ L', Tendsto (fun ε => ∫ t in γ.a..γ.b, if ‖γ.toFun t - s‖ > ε then (γ.toFun t - s)⁻¹ · γ'(t) else 0) (𝓝[>] 0) (𝓝 L')`
- **What**: From `c/(z-s)` CPV existence, extract base-case CPV of `1/(z-s)` (i.e. for unit residue).
- **How**: Destructure `hPV` to get limit `L`. Define `L' = L/c`. Show the integral equals `c · ∫ (γ-s)⁻¹·γ'` (via `cpv_integral_factor_const`). Then `Tendsto.const_mul c⁻¹` cancels the factor (using `inv_mul_cancel_left₀` and `field_simp`).
- **Hypotheses**: `c ≠ 0`, base CPV exists.
- **Uses from project**: `CauchyPrincipalValueExists'`, `cpv_integral_factor_const`, `PiecewiseC1Immersion`
- **Used by**: `generalizedResidueTheorem'_crossing_formula`.
- **Visibility**: private
- **Lines**: 262–299
- **Notes**: >10 lines (~38).

### `private lemma cpv_eq_sum_single_pole_cpvs`
- **Type**: `(S0) (f) (γ) (hSimplePoles) (hPV_singular) (hg_cont_on_image) (hg_integral_zero : ∫ … = 0) : cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b = ∑ s ∈ S0, cauchyPrincipalValue' (c_s/(z-s)) γ.toFun γ.a γ.b s`
- **What**: Multi-point CPV equals the sum of individual single-pole CPVs, given the regular part has vanishing integral.
- **How**: `cauchyPrincipalValueOn_singular_sum` gives existence. Each `cauchyPrincipalValue' = L_s`. The sum-tendsto follows from `tendsto_finset_sum`. Provide `hS0_sep` via `finset_min_sep`. Apply `multipointPV_eq_sum_of_integral_zero`.
- **Hypotheses**: simple poles, singular CPVs exist, regular part continuous, regular integral vanishes.
- **Uses from project**: `cauchyPrincipalValueOn`, `cauchyPrincipalValue'`, `cauchyPrincipalValueOn_singular_sum`, `multipointPV_eq_sum_of_integral_zero`, `cpv_crossing_null`, `finset_min_sep`, `HasSimplePoleAt`, `CauchyPrincipalValueExists'`, `residueSimplePole`, `PiecewiseC1Immersion`
- **Used by**: `generalizedResidueTheorem'_crossing_formula`.
- **Visibility**: private
- **Lines**: 302–357
- **Notes**: >10 lines (~56); key lemma `multipointPV_eq_sum_of_integral_zero`.

### `private lemma generalizedResidueTheorem'_crossing_formula`
- **Type**: `(S0) (f) (γ) (hSimplePoles) (hPV_singular) (hg_cont_on_image) (hg_integral_zero) : cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b = 2 · π · I · ∑ s ∈ S0, generalizedWindingNumber' γ.toFun γ.a γ.b s · residueSimplePole f s`
- **What**: When `γ` crosses some poles, CPV equals `2πi · Σ winding · residue`.
- **How**: For each pole `s`, single-pole formula: if `residueSimplePole f s = 0`, CPV is trivially 0 (constant zero integrand). Else `pv_integral_simple_pole` gives `cauchyPrincipalValue' = 2πi · winding · residue`, using `single_pole_pv_base_exists` to get the base-1 CPV. Sum via `cpv_eq_sum_single_pole_cpvs`. Final `Finset.mul_sum`/`ring`.
- **Hypotheses**: as above.
- **Uses from project**: `cauchyPrincipalValueOn`, `cauchyPrincipalValue'`, `generalizedWindingNumber'`, `residueSimplePole`, `single_pole_pv_base_exists`, `cpv_eq_sum_single_pole_cpvs`, `pv_integral_simple_pole`, `HasSimplePoleAt`, `CauchyPrincipalValueExists'`, `PiecewiseC1Immersion`
- **Used by**: `generalizedResidueTheorem'`.
- **Visibility**: private
- **Lines**: 363–419
- **Notes**: >10 lines (~57); key lemma `pv_integral_simple_pole`.

### `theorem generalizedResidueTheorem'`
- **Type**: `(U : Set ℂ) (hU) (hU_convex) (S) (hS_in_U) (_hS_discrete) (_hS_closed) (S0) (hS0_subset) (f) (hf : DifferentiableOn ℂ f (U \ S0)) (γ : PiecewiseC1Immersion) (hγ_closed) (hγ_in_U) (_hS_on_curve) (hSimplePoles) (hf_ext) (hPV_singular) : CauchyPrincipalValueExistsOn S0 f γ.toFun γ.a γ.b ∧ cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b = 2 · π · I · ∑ s ∈ S0, generalizedWindingNumber' γ.toFun γ.a γ.b s · residueSimplePole f s`
- **What**: Generalized residue theorem on a convex open domain, allowing the contour to cross poles (via CPV).
- **How**: Use `simple_poles_decomposition` to express `f` as `(∑ c_s/(z-s)) + g` with `g` holomorphic on `U`. The continuity of `g` on `γ '' [a,b]` follows from `hf_ext`/`hγ_in_U`. Split: (1) Existence — if `γ` avoids all poles, `cauchyPrincipalValueExistsOn_avoids`; else `cauchyPrincipalValueOn_singular_sum`. (2) Equation — if avoidance, `integral_eq_sum_residues_of_avoids`; else `generalizedResidueTheorem'_crossing_formula` using `holomorphic_closed_integral_zero` to discharge the regular-integral-zero hypothesis.
- **Hypotheses**: convex open `U`, discrete closed `S ⊂ U`, finite `S0 ⊂ S`, `f` holomorphic off `S0`, `γ` PC1 immersion closed in `U`, simple poles on `S0`, continuity of remainder, CPV of each singular term.
- **Uses from project**: `CauchyPrincipalValueExistsOn`, `cauchyPrincipalValueOn`, `generalizedWindingNumber'`, `residueSimplePole`, `simple_poles_decomposition`, `cauchyPrincipalValueExistsOn_avoids`, `cauchyPrincipalValueOn_avoids`, `integral_eq_sum_residues_of_avoids`, `cauchyPrincipalValueOn_singular_sum`, `generalizedResidueTheorem'_crossing_formula`, `holomorphic_closed_integral_zero`, `PiecewiseC1Immersion`, `PiecewiseC1Curve.IsClosed`, `HasSimplePoleAt`, `CauchyPrincipalValueExists'`
- **Used by**: unused in file (main public theorem).
- **Visibility**: public
- **Lines**: 423–469
- **Notes**: >10 lines (~47); main theorem; key lemma `simple_poles_decomposition`.

### `lemma CauchyPrincipalValueExists'.const_mul`
- **Type**: `{f γ a b z₀} (c : ℂ) (h : CauchyPrincipalValueExists' f γ a b z₀) : CauchyPrincipalValueExists' (fun z => c * f z) γ a b z₀`
- **What**: CPV scaling: if `f` has a CPV, so does `c · f`, with limit `c · L`.
- **How**: Extract `L`. Show indicator integral of `(c·f)·γ'` equals `c · (indicator integral of `f·γ'`) via `intervalIntegral.integral_const_mul` (`erw`) and `split_ifs <;> ring`. Apply `Tendsto.const_mul` then `Tendsto.congr`.
- **Hypotheses**: base CPV exists.
- **Uses from project**: `CauchyPrincipalValueExists'`
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 472–488

### `def residueAt`
- **Type**: `(f : ℂ → ℂ) (z₀ : ℂ) : ℂ`
- **What**: Residue of `f` at `z₀` via the contour integral definition: `lim_{r→0⁺} (2πi)⁻¹ ∮_{|z-z₀|=r} f(z) dz`.
- **How**: `limUnder (𝓝[>] 0) (fun r => (2πi)⁻¹ · ∮ z in C(z₀, r), f z)`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `residueAt_eq_of_simple_pole_decomp`, `residueAt_eq_residueSimplePole`, `generalizedResidueTheorem_higher_order_tendsto`.
- **Visibility**: public
- **Lines**: 497–499

### `theorem residueSimplePole_eq_of_decomposition`
- **Type**: `(f z₀ c g) (hg : AnalyticAt ℂ g z₀) (hf_eq : ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z) : residueSimplePole f z₀ = c`
- **What**: For an explicit Laurent decomposition `f = c/(z-z₀) + g`, the simple-pole residue is `c`.
- **How**: Apply `Tendsto.limUnder_eq`. Compute `(z - z₀) · f z = c + (z - z₀) · g z` near `z₀`; both factors tend cleanly, giving limit `c`.
- **Hypotheses**: `g` analytic, Laurent germ.
- **Uses from project**: `residueSimplePole`
- **Used by**: `residueAt_eq_residueSimplePole`, `residueSimplePole_sum_div_sub`.
- **Visibility**: public
- **Lines**: 503–525
- **Notes**: >10 lines (~23).

### `private lemma residueAt_eq_of_simple_pole_decomp`
- **Type**: `(f z₀ c g) (hg_analytic) (hf_eq : ∀ᶠ z in 𝓝[≠] z₀, f z = c/(z-z₀) + g z) : residueAt f z₀ = c`
- **What**: For an explicit decomposition, the contour residue `residueAt` equals `c`.
- **How**: For small enough `r > 0`, `f = c·(z-z₀)⁻¹ + g` on the sphere (using local analyticity ball). Then `∮ f = c · ∮(z-z₀)⁻¹ + ∮ g = c · (2πi) + 0` via `circleIntegral.integral_sub_center_inv` and `circleIntegral_eq_zero_of_differentiable_on_off_countable` for the analytic part. Divide by `2πi`.
- **Hypotheses**: `g` analytic, Laurent germ.
- **Uses from project**: `residueAt`
- **Used by**: `residueAt_eq_residueSimplePole`.
- **Visibility**: private
- **Lines**: 529–584
- **Notes**: >10 lines (~56); key lemmas `circleIntegral.integral_sub_center_inv`, `circleIntegral_eq_zero_of_differentiable_on_off_countable`.

### `theorem residueAt_eq_residueSimplePole`
- **Type**: `(f : ℂ → ℂ) (z₀ : ℂ) (hf : HasSimplePoleAt f z₀) : residueAt f z₀ = residueSimplePole f z₀`
- **What**: For a simple pole, the contour residue agrees with the simple-pole-limit residue.
- **How**: Destructure `hf` into `(c, g, hg_analytic, hf_eq)`. Apply `residueSimplePole_eq_of_decomposition` (gives `c`) and `residueAt_eq_of_simple_pole_decomp` (also gives `c`).
- **Hypotheses**: `HasSimplePoleAt f z₀`.
- **Uses from project**: `residueAt`, `residueSimplePole`, `HasSimplePoleAt`, `residueSimplePole_eq_of_decomposition`, `residueAt_eq_of_simple_pole_decomp`
- **Used by**: unused in file (public).
- **Visibility**: public
- **Lines**: 587–595

### `lemma hasSimplePoleAt_sum_div_sub`
- **Type**: `(S0 : Finset ℂ) (c : ℂ → ℂ) (s : ℂ) (hs : s ∈ S0) : HasSimplePoleAt (fun z => ∑ s' ∈ S0, c s' / (z - s')) s`
- **What**: The "pure residue sum" `∑ c(s')/(z-s')` has a simple pole at every `s ∈ S0`, with coefficient `c(s)`.
- **How**: Provide witness `⟨c s, ∑ s' ∈ S0.erase s, c s' / (z - s'), …⟩`. Analyticity of remainder via `analyticAt_const.div ...` for each `s' ≠ s`. Germ equality via `Finset.add_sum_erase`.
- **Hypotheses**: `s ∈ S0`.
- **Uses from project**: `HasSimplePoleAt`
- **Used by**: unused in file (downstream consumer in higher-order chain).
- **Visibility**: public
- **Lines**: 605–612

### `lemma differentiableOn_sum_div_sub`
- **Type**: `(S0 : Finset ℂ) (c : ℂ → ℂ) (U : Set ℂ) : DifferentiableOn ℂ (fun z => ∑ s ∈ S0, c s / (z - s)) (U \ ↑S0)`
- **What**: The pure residue sum is holomorphic on `U \ S0`.
- **How**: `DifferentiableOn.fun_sum` over `S0`, each term `c(s) / (z - s)` differentiable since `z - s ≠ 0` on `U \ S0`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file (downstream).
- **Visibility**: public
- **Lines**: 615–621

### `lemma residueSimplePole_sum_div_sub`
- **Type**: `(S0) (c) (s : ℂ) (hs : s ∈ S0) : residueSimplePole (fun z => ∑ s' ∈ S0, c s' / (z - s')) s = c s`
- **What**: The residue of the pure residue sum at `s` equals `c(s)`.
- **How**: Apply `residueSimplePole_eq_of_decomposition` with the explicit Laurent decomposition (analyticity of remainder + germ equality via `Finset.add_sum_erase`).
- **Hypotheses**: `s ∈ S0`.
- **Uses from project**: `residueSimplePole`, `residueSimplePole_eq_of_decomposition`
- **Used by**: `continuousAt_sum_remainder`.
- **Visibility**: public
- **Lines**: 625–633

### `lemma continuousAt_sum_remainder`
- **Type**: `(S0) (c) (s : ℂ) (hs : s ∈ S0) : ContinuousAt (fun z => (∑ s' ∈ S0, c s' / (z - s')) - residueSimplePole (…) s / (z - s)) s`
- **What**: The remainder of the pure residue sum (after subtracting its own residue/(z-s) at `s`) is continuous at `s` — the `hf_ext` hypothesis for `generalizedResidueTheorem'`.
- **How**: Rewrite the residue as `c s` via `residueSimplePole_sum_div_sub`. Then the remainder equals `∑ s' ∈ S0.erase s, c s' / (z - s')`, which is `AnalyticAt` (so continuous) at `s`.
- **Hypotheses**: `s ∈ S0`.
- **Uses from project**: `residueSimplePole`, `residueSimplePole_sum_div_sub`
- **Used by**: unused in file (downstream).
- **Visibility**: public
- **Lines**: 637–649

### `lemma cpv_eq_of_cancel_and_exists`
- **Type**: `(S0) (f f_res) (γ) (hCancel : Tendsto (M_f(ε) - M_res(ε)) (𝓝[>] 0) (𝓝 0)) (h_res_exists : CauchyPrincipalValueExistsOn S0 f_res γ.toFun γ.a γ.b) : cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b = cauchyPrincipalValueOn S0 f_res γ.toFun γ.a γ.b`
- **What**: The "limit arithmetic core" of the higher-order reduction: if `M_f(ε) - M_res(ε) → 0` and `M_res` converges, then `cauchyPrincipalValueOn` of `f` and `f_res` agree.
- **How**: Destructure `h_res_exists` to get `L_res`. Write `M_f(ε) = (M_f - M_res)(ε) + M_res(ε)`; the sum tends to `0 + L_res = L_res`. Both `cauchyPrincipalValueOn` values equal `L_res` via `Tendsto.limUnder_eq`.
- **Hypotheses**: cancellation + existence of `M_res` limit.
- **Uses from project**: `CauchyPrincipalValueExistsOn`, `cauchyPrincipalValueOn`, `cauchyPrincipalValueIntegrandOn`, `PiecewiseC1Immersion`
- **Used by**: unused in file (downstream higher-order reduction).
- **Visibility**: public
- **Lines**: 653–678
- **Notes**: >10 lines (~26).

### `theorem generalizedResidueTheorem_higher_order_tendsto`
- **Type**: `(S0) (f) (γ) (hHigherOrderCancel : Tendsto (M_f(ε) - M_res(ε)) (𝓝[>] 0) (𝓝 0)) (hPV_res_tendsto : Tendsto M_res (𝓝[>] 0) (𝓝 (2πi · Σ winding · residueAt))) : Tendsto M_f (𝓝[>] 0) (𝓝 (2πi · Σ winding · residueAt))`
- **What**: Higher-order generalized residue theorem in Tendsto form: `f` has CPV converging to the residue sum, given cancellation of the difference and convergence of the pure-residue model.
- **How**: Write `M_f(ε) = (M_f(ε) - M_res(ε)) + M_res(ε)`. Use `Tendsto.add` of the two hypotheses (with explicit `0 + Σ = Σ`).
- **Hypotheses**: as above.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`, `residueAt`, `generalizedWindingNumber'`, `PiecewiseC1Immersion`
- **Used by**: unused in file (top-level higher-order theorem).
- **Visibility**: public
- **Lines**: 687–719
- **Notes**: >10 lines (~33).

## File Summary

- **Total declarations**: 19 (1 def, 18 lemmas/theorems).
- **Key API**: `cauchyPrincipalValueOn_singular_sum`, `generalizedResidueTheorem'`, `CauchyPrincipalValueExists'.const_mul`, `residueAt`, `residueSimplePole_eq_of_decomposition`, `residueAt_eq_residueSimplePole`, `hasSimplePoleAt_sum_div_sub`, `differentiableOn_sum_div_sub`, `residueSimplePole_sum_div_sub`, `continuousAt_sum_remainder`, `cpv_eq_of_cancel_and_exists`, `generalizedResidueTheorem_higher_order_tendsto`.
- **Unused in file** (downstream-consumed): `generalizedResidueTheorem'`, `CauchyPrincipalValueExists'.const_mul`, `residueAt_eq_residueSimplePole`, `hasSimplePoleAt_sum_div_sub`, `differentiableOn_sum_div_sub`, `continuousAt_sum_remainder`, `cpv_eq_of_cancel_and_exists`, `generalizedResidueTheorem_higher_order_tendsto`.
- **Sorries**: none.
- **set_options**: none.
- **Long proofs** (>10 lines): `cpv_crossing_null` (~23), `finset_min_sep` (~45), `cpv_cauchy_of_sum_and_regular` (~53), `holomorphic_closed_integral_zero` (~46), `single_pole_pv_base_exists` (~38), `cpv_eq_sum_single_pole_cpvs` (~56), `generalizedResidueTheorem'_crossing_formula` (~57), `generalizedResidueTheorem'` (~47), `residueSimplePole_eq_of_decomposition` (~23), `residueAt_eq_of_simple_pole_decomp` (~56), `cpv_eq_of_cancel_and_exists` (~26), `generalizedResidueTheorem_higher_order_tendsto` (~33).
- **One-paragraph purpose**: This file is the base infrastructure for the generalized residue theorem applicable to piecewise-C¹ immersions that may cross poles. It builds the multi-point Cauchy-principal-value (`cauchyPrincipalValueOn_singular_sum`) by combining individual singular CPVs with the integral of the holomorphic remainder; it proves the convex-domain version `generalizedResidueTheorem'` (CPV = `2πi · Σ winding · residue`) by reducing to either an avoidance case (Cauchy's theorem) or a crossing case (`generalizedResidueTheorem'_crossing_formula` via `pv_integral_simple_pole`). It also introduces an alternative contour-integral definition `residueAt`, shows it agrees with `residueSimplePole`, and provides the "pure residue function" helper lemmas (`hasSimplePoleAt_sum_div_sub`, `differentiableOn_sum_div_sub`, `residueSimplePole_sum_div_sub`, `continuousAt_sum_remainder`) plus the limit-arithmetic core `cpv_eq_of_cancel_and_exists` used by the higher-order theorem `generalizedResidueTheorem_higher_order_tendsto`.
