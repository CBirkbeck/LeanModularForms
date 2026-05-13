# Inventory: `CrossingAnalysis.lean`

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/WindingNumber/CrossingAnalysis.lean`

Imports:
- `LeanModularForms.ForMathlib.GeneralizedResidueTheory.WindingNumber.Defs` (gives `PiecewiseC1Immersion`, `PiecewiseC1Curve`, `angleAtCrossing`, `piecewiseC1Immersion_deriv_bounded`, `hasDerivWithinAt_zero_of_deriv_zero_off_finite`, `intervalIntegrable_of_piecewise_continuousOn_bounded`, `PiecewiseC1Curve.IsClosed`).
- `Mathlib.Analysis.InnerProductSpace.Calculus`, `Mathlib.Analysis.Calculus.Deriv.MeanValue`, `Mathlib.Analysis.SpecialFunctions.Pow.Deriv`, `Mathlib.Analysis.Calculus.FDeriv.Extend`.

Header declares `noncomputable section` (closed at line 1151). No `set_option`, no `axiom`, no `sorry`, no `TODO` strings.

---

### `lemma immersion_one_sided_setup`
- **Type**: `(γ : PiecewiseC1Immersion) (_z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (_hcross : γ.toFun t₀ = _z₀) : ∃ (L_R L_L : ℂ), L_R ≠ 0 ∧ L_L ≠ 0 ∧ HasDerivWithinAt γ.toFun L_R (Set.Ici t₀) t₀ ∧ HasDerivWithinAt γ.toFun L_L (Set.Iic t₀) t₀ ∧ Filter.Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L_R) ∧ Filter.Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L_L)`
- **What**: At an interior point `t₀` of a piecewise-C¹ immersion `γ`, extracts nonzero left/right derivative limits `L_L, L_R`, the corresponding one-sided `HasDerivWithinAt` statements on `Ici t₀` and `Iic t₀`, plus the punctured-neighborhood `tendsto` statements.
- **How**: Case on whether `t₀ ∈ γ.partition`. If yes use `γ.right_deriv_limit`/`γ.left_deriv_limit`; otherwise use `γ.deriv_continuous_off_partition` together with `γ.deriv_ne_zero`. Extracts partition-free neighborhoods to the right and left by inspecting `γ.partition.filter (t₀ < ·)` and its `min'`/`max'`, then applies `hasDerivWithinAt_Ici_of_tendsto_deriv` and `hasDerivWithinAt_Iic_of_tendsto_deriv` with `γ.smooth_off_partition`, `γ.continuous_toFun` to upgrade the tendsto facts to `HasDerivWithinAt`.
- **Hypotheses**: `γ` is a `PiecewiseC1Immersion`, `t₀` is in the open interior `Ioo γ.a γ.b`. The `_z₀` and `_hcross` arguments are not used internally (placeholders).
- **Uses from project**: `PiecewiseC1Immersion.left_deriv_limit`, `PiecewiseC1Immersion.right_deriv_limit`, `PiecewiseC1Immersion.deriv_ne_zero`, `PiecewiseC1Immersion.deriv_continuous_off_partition`, `PiecewiseC1Immersion.partition_subset`, `PiecewiseC1Immersion.smooth_off_partition`, `PiecewiseC1Immersion.continuous_toFun`, `PiecewiseC1Immersion.partition`.
- **Used by**: `piecewiseC1Immersion_norm_strictMono_near_crossing`, `crossing_ratio_tendsto`.
- **Visibility**: public (no `private`).
- **Lines**: 39–102.
- **Notes**: 64-line proof; no `set_option`, no `sorry`.

### `lemma immersion_slope_tendsto_right`
- **Type**: `{γ : ℝ → ℂ} {z₀ : ℂ} {t₀ : ℝ} {L_R : ℂ} (hcross : γ t₀ = z₀) (hHDWA_R : HasDerivWithinAt γ L_R (Set.Ici t₀) t₀) : Filter.Tendsto (fun t => (γ t - z₀) / ((t - t₀ : ℝ) : ℂ)) (𝓝[>] t₀) (𝓝 L_R)`
- **What**: Converts a `HasDerivWithinAt` on `Ici t₀` into convergence of the slope `(γ(t) − γ(t₀)) / (t − t₀)` as `t → t₀⁺`.
- **How**: Rewrites `hasDerivWithinAt_iff_tendsto_slope` and `Set.Ici_diff_left`, then unfolds `slope` and matches the real-scalar `slope` with complex division via `Complex.real_smul`/`Complex.ofReal_inv`/`ring`.
- **Hypotheses**: `γ t₀ = z₀`, right-sided derivative `L_R`.
- **Uses from project**: [] (only mathlib).
- **Used by**: `piecewiseC1Immersion_norm_strictMono_near_crossing`, `crossing_ratio_tendsto`.
- **Visibility**: public.
- **Lines**: 105–116.

### `lemma immersion_slope_tendsto_left`
- **Type**: `{γ : ℝ → ℂ} {z₀ : ℂ} {t₀ : ℝ} {L_L : ℂ} (hcross : γ t₀ = z₀) (hHDWA_L : HasDerivWithinAt γ L_L (Set.Iic t₀) t₀) : Filter.Tendsto (fun t => (γ t - z₀) / ((t - t₀ : ℝ) : ℂ)) (𝓝[<] t₀) (𝓝 L_L)`
- **What**: Left-sided analogue of `immersion_slope_tendsto_right`: slope tends to the left derivative `L_L` as `t → t₀⁻`.
- **How**: Same recipe with `Set.Iic_diff_right` and `slope`/`Complex.real_smul`/`ring`.
- **Hypotheses**: `γ t₀ = z₀`, left-sided derivative `L_L`.
- **Uses from project**: [].
- **Used by**: `piecewiseC1Immersion_norm_strictMono_near_crossing`, `crossing_ratio_tendsto`.
- **Visibility**: public.
- **Lines**: 119–130.

### `lemma immersion_direction_tendsto_right`
- **Type**: `{γ : ℝ → ℂ} {z₀ : ℂ} {t₀ : ℝ} {L_R : ℂ} (hL_R_ne : L_R ≠ 0) (hslope_R : Filter.Tendsto (fun t => (γ t - z₀) / ((t - t₀ : ℝ) : ℂ)) (𝓝[>] t₀) (𝓝 L_R)) : Filter.Tendsto (fun t => (γ t - z₀) / ↑‖γ t - z₀‖) (𝓝[>] t₀) (𝓝 (L_R / ↑‖L_R‖))`
- **What**: From right-slope convergence and nonzero limit `L_R`, deduces convergence of the unit-direction vector to `L_R / ‖L_R‖`.
- **How**: Norms slope to obtain `‖slope‖ → ‖L_R‖`, then `Tendsto.div` of the slope by its norm, congr'ing the slope-over-norm-of-slope to the direction `(γ t - z₀) / ↑‖γ t - z₀‖` using `field_simp`, `norm_div`, `Complex.norm_real`, `Real.norm_of_nonneg`.
- **Hypotheses**: `L_R ≠ 0`; right-slope tendsto holds.
- **Uses from project**: [].
- **Used by**: `piecewiseC1Immersion_norm_strictMono_near_crossing`, `crossing_ratio_tendsto`.
- **Visibility**: public.
- **Lines**: 133–158.

### `lemma immersion_direction_tendsto_left`
- **Type**: `{γ : ℝ → ℂ} {z₀ : ℂ} {t₀ : ℝ} {L_L : ℂ} (hL_L_ne : L_L ≠ 0) (hslope_L : Filter.Tendsto (fun t => (γ t - z₀) / ((t - t₀ : ℝ) : ℂ)) (𝓝[<] t₀) (𝓝 L_L)) : Filter.Tendsto (fun t => (γ t - z₀) / ↑‖γ t - z₀‖) (𝓝[<] t₀) (𝓝 (-L_L / ↑‖L_L‖))`
- **What**: Left-sided direction limit: as `t → t₀⁻`, the unit direction tends to `−L_L / ‖L_L‖` (the negation appears because the slope denominator `t − t₀` is negative there).
- **How**: Same recipe as right version but with `Real.norm_of_nonpos` and an extra `Tendsto.neg`/`neg_div`.
- **Hypotheses**: `L_L ≠ 0`; left-slope tendsto holds.
- **Uses from project**: [].
- **Used by**: `piecewiseC1Immersion_norm_strictMono_near_crossing`, `crossing_ratio_tendsto`.
- **Visibility**: public.
- **Lines**: 161–187.

### `lemma piecewiseC1Immersion_norm_strictMono_near_crossing`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = z₀) : ∃ l r : ℝ, l < t₀ ∧ t₀ < r ∧ γ.a ≤ l ∧ r ≤ γ.b ∧ StrictAntiOn (fun t => ‖γ.toFun t - z₀‖) (Icc l t₀) ∧ StrictMonoOn (fun t => ‖γ.toFun t - z₀‖) (Icc t₀ r)`
- **What**: Local monotonicity of `g(t) = ‖γ(t) − z₀‖` at a crossing point: strictly decreasing on some `[l, t₀]` and strictly increasing on some `[t₀, r]`.
- **How**: Sets up the helper `hasDerivAt_norm_sub` (derivative of `t ↦ ‖f(t) − z₀‖` via `Real.hasDerivAt_sqrt ∘ HasDerivAt.norm_sq`). Calls `immersion_one_sided_setup` for one-sided derivative limits, `immersion_slope_tendsto_{left,right}`, `immersion_direction_tendsto_{left,right}`. Then shows `inner (γ t − z₀) (γ' t) / ‖γ t − z₀‖ → ‖L_R‖` from the right and `→ −‖L_L‖` from the left (using `inner_div_norm` rewriting and continuity of the inner product), giving eventually positive/negative inner-product ratio. Concrete radii `εR, εL` are extracted, intersected with partition-free neighborhoods, and the sign of the derivative of `g` on each subinterval gives strict monotonicity via `strictAntiOn_of_deriv_neg` and `strictMonoOn_of_deriv_pos`.
- **Hypotheses**: `γ` immersion, `t₀` interior, `γ(t₀) = z₀`.
- **Uses from project**: `immersion_one_sided_setup`, `immersion_slope_tendsto_right`, `immersion_slope_tendsto_left`, `immersion_direction_tendsto_right`, `immersion_direction_tendsto_left`, `PiecewiseC1Immersion.partition`, `PiecewiseC1Immersion.partition_subset`, `PiecewiseC1Immersion.continuous_toFun`, `PiecewiseC1Immersion.smooth_off_partition`.
- **Used by**: `exists_cutoff_boundary_times`, `exists_cutoff_boundary_times_with_mono`.
- **Visibility**: public.
- **Lines**: 192–359.
- **Notes**: 168-line proof (largest in the file alongside `exp_cutoff_integral_eq_ratio`).

### `lemma exists_cutoff_boundary_times`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = z₀) (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀) : ∃ δ > 0, ∀ ε ∈ Ioo 0 δ, ∃ σ₁ σ₂ : ℝ, γ.a ≤ σ₁ ∧ σ₁ < t₀ ∧ t₀ < σ₂ ∧ σ₂ ≤ γ.b ∧ ‖γ.toFun σ₁ - z₀‖ = ε ∧ ‖γ.toFun σ₂ - z₀‖ = ε ∧ (∀ t ∈ Ico γ.a σ₁, ε < ‖γ.toFun t - z₀‖) ∧ (∀ t ∈ Ioc σ₂ γ.b, ε < ‖γ.toFun t - z₀‖) ∧ (∀ t ∈ Icc σ₁ σ₂, ‖γ.toFun t - z₀‖ ≤ ε)`
- **What**: For an isolated crossing `t₀` (only zero of `g(t) = ‖γ(t) − z₀‖`), there is a threshold `δ > 0` so that for every `ε ∈ (0, δ)` the level set `{t : ‖γ(t) − z₀‖ ≤ ε}` is exactly one closed interval `[σ₁, σ₂]` containing `t₀`, with the two boundary times `σ₁, σ₂` carrying norm exactly `ε`.
- **How**: From `piecewiseC1Immersion_norm_strictMono_near_crossing` get `[l, t₀]`, `[t₀, r]` strict monotonicity. Take compact minima of `g` on `[γ.a, l]` and `[r, γ.b]` via `IsCompact.exists_isMinOn`; by `honly` these minima are strictly positive. Set `δ = min(g(xm₁), g(xm₂), g(l), g(r))`. For each `ε < δ`, apply `intermediate_value_Icc'` to `[l, t₀]` (decreasing) to get `σ₁`, `intermediate_value_Icc` to `[t₀, r]` (increasing) to get `σ₂`. Strict monotonicity then gives the comparison facts on `Ico l σ₁`, `Ioc σ₁ t₀`, `Ico t₀ σ₂`, `Ioc σ₂ r`; the outer regions `[a, l]` and `[r, b]` use the minima `xm₁`, `xm₂`.
- **Hypotheses**: `γ` immersion, `t₀` interior, `γ(t₀) = z₀`, `t₀` is the unique preimage of `z₀` under `γ` on `[γ.a, γ.b]`.
- **Uses from project**: `piecewiseC1Immersion_norm_strictMono_near_crossing`, `PiecewiseC1Immersion.continuous_toFun`.
- **Used by**: `exists_cutoff_boundary_times_with_mono`, `tendsto_exp_cutoff_integral_crossing`.
- **Visibility**: public.
- **Lines**: 361–522.
- **Notes**: 162-line proof.

### `lemma exists_cutoff_boundary_times_with_mono`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = z₀) (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀) : ∃ δ > 0, ∃ l r : ℝ, l < t₀ ∧ t₀ < r ∧ γ.a ≤ l ∧ r ≤ γ.b ∧ StrictAntiOn (fun t => ‖γ.toFun t - z₀‖) (Icc l t₀) ∧ StrictMonoOn (fun t => ‖γ.toFun t - z₀‖) (Icc t₀ r) ∧ δ ≤ ‖γ.toFun l - z₀‖ ∧ δ ≤ ‖γ.toFun r - z₀‖ ∧ ∀ ε ∈ Ioo 0 δ, ∃ σ₁ σ₂ : ℝ, γ.a ≤ σ₁ ∧ σ₁ < t₀ ∧ t₀ < σ₂ ∧ σ₂ ≤ γ.b ∧ ‖γ.toFun σ₁ - z₀‖ = ε ∧ ‖γ.toFun σ₂ - z₀‖ = ε ∧ (∀ t ∈ Ico γ.a σ₁, ε < ‖γ.toFun t - z₀‖) ∧ (∀ t ∈ Ioc σ₂ γ.b, ε < ‖γ.toFun t - z₀‖) ∧ (∀ t ∈ Icc σ₁ σ₂, ‖γ.toFun t - z₀‖ ≤ ε)`
- **What**: Extension of `exists_cutoff_boundary_times` that also exposes the strict-monotonicity interval endpoints `l, r` and the bounds `δ ≤ ‖γ(l) − z₀‖`, `δ ≤ ‖γ(r) − z₀‖`.
- **How**: Calls both `piecewiseC1Immersion_norm_strictMono_near_crossing` and `exists_cutoff_boundary_times`, takes `δ := min δ₁ (min ‖γ(l)−z₀‖ ‖γ(r)−z₀‖)`. The strict positivity of `‖γ(l)−z₀‖`/`‖γ(r)−z₀‖` follows from `honly` applied at `l, r` together with `hl_lt`, `hr_gt`, contradicting equality.
- **Hypotheses**: same as `exists_cutoff_boundary_times`.
- **Uses from project**: `piecewiseC1Immersion_norm_strictMono_near_crossing`, `exists_cutoff_boundary_times`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 527–563.

### `lemma exp_cutoff_integral_eq_ratio`
- **Type**: `(γ : PiecewiseC1Immersion) (hclosed : γ.toPiecewiseC1Curve.IsClosed) (z₀ : ℂ) (σ₁ σ₂ ε : ℝ) (hσ₁ : γ.a ≤ σ₁) (hσ₁₂ : σ₁ < σ₂) (hσ₂ : σ₂ ≤ γ.b) (hε : 0 < ε) (hσ₁_val : ‖γ.toFun σ₁ - z₀‖ = ε) (hσ₂_val : ‖γ.toFun σ₂ - z₀‖ = ε) (h_left : ∀ t ∈ Ico γ.a σ₁, ε < ‖γ.toFun t - z₀‖) (h_right : ∀ t ∈ Ioc σ₂ γ.b, ε < ‖γ.toFun t - z₀‖) (h_middle : ∀ t ∈ Icc σ₁ σ₂, ‖γ.toFun t - z₀‖ ≤ ε) : Complex.exp (∫ t in γ.a..γ.b, if ‖γ.toFun t - z₀‖ > ε then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0) = (γ.toFun σ₁ - z₀) / (γ.toFun σ₂ - z₀)`
- **What**: For a closed piecewise-C¹ immersion, the exponential of the cutoff log-derivative integral equals the ratio of "exit" to "entry" complex displacements at the cutoff boundary times.
- **How**: Defines `f(t) = 1_{‖γ−z₀‖>ε}(t) · (γ(t) − z₀)⁻¹ γ'(t)`. Shows the middle interval `[σ₁, σ₂]` integrates to `0` because `f = 0` there. Builds `F(t) = ∫_{γ.a}^t f`, `G(t) = (γ(t) − z₀) · exp(−F(t))`. Computes `G(γ.a) = γ(γ.a) − z₀`; off the partition `P` and where `‖γ−z₀‖ > ε`, FTC gives `HasDerivAt F (f t) t` (built using `intervalIntegral.integral_hasDerivAt_right` together with a partition-avoiding neighborhood). The product-rule derivative of `G` is zero on the smooth regions, so by `constant_of_has_deriv_right_zero` together with `hasDerivWithinAt_zero_of_deriv_zero_off_finite` we obtain `G` constant on `[γ.a, σ₁]` and on `[σ₂, γ.b]`. Closedness `γ(γ.a) = γ(γ.b)` (from `hclosed`) plus `F(σ₂) = F(σ₁)` (middle integral zero) then yields the ratio formula by algebra (`field_simp`, `mul_left_cancel₀`).
- **Hypotheses**: closed piecewise-C¹ immersion; cutoff times satisfying the standard interval data of `exists_cutoff_boundary_times`.
- **Uses from project**: `PiecewiseC1Immersion.partition`, `PiecewiseC1Immersion.endpoints_in_partition`, `PiecewiseC1Immersion.continuous_toFun`, `PiecewiseC1Immersion.smooth_off_partition`, `PiecewiseC1Immersion.deriv_continuous_off_partition`, `PiecewiseC1Immersion.toPiecewiseC1Curve`, `PiecewiseC1Curve.IsClosed`, `piecewiseC1Immersion_deriv_bounded`, `intervalIntegrable_of_piecewise_continuousOn_bounded`, `hasDerivWithinAt_zero_of_deriv_zero_off_finite`.
- **Used by**: `tendsto_exp_cutoff_integral_crossing`.
- **Visibility**: public.
- **Lines**: 568–875.
- **Notes**: 308-line proof — the largest in the file. Adapts the "G-function" technique used by `exp_integral_eq_endpoint_ratio_piecewise` (referenced in comments).

### `lemma crossing_ratio_tendsto`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = z₀) (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀) (σ₁ σ₂ : ℝ → ℝ) (hσ₁_lt : ∀ᶠ ε in 𝓝[>] (0:ℝ), σ₁ ε < t₀) (hσ₂_gt : ∀ᶠ ε in 𝓝[>] (0:ℝ), t₀ < σ₂ ε) (hσ₁_val : ∀ᶠ ε in 𝓝[>] (0:ℝ), ‖γ.toFun (σ₁ ε) - z₀‖ = ε) (hσ₂_val : ∀ᶠ ε in 𝓝[>] (0:ℝ), ‖γ.toFun (σ₂ ε) - z₀‖ = ε) (hσ₁_in : ∀ᶠ ε in 𝓝[>] (0:ℝ), γ.a ≤ σ₁ ε) (hσ₂_in : ∀ᶠ ε in 𝓝[>] (0:ℝ), σ₂ ε ≤ γ.b) : Tendsto (fun ε => (γ.toFun (σ₁ ε) - z₀) / (γ.toFun (σ₂ ε) - z₀)) (𝓝[>] 0) (𝓝 (Complex.exp (-(I * ↑(angleAtCrossing γ t₀ ht₀)))))`
- **What**: As `ε → 0⁺`, the ratio of complex displacements `(γ(σ₁) − z₀) / (γ(σ₂) − z₀)` converges to `exp(−i·angleAtCrossing γ t₀ ht₀)`.
- **How**: Get one-sided derivatives and direction limits via `immersion_one_sided_setup`, `immersion_{slope,direction}_tendsto_{left,right}`. Show `σ₁(ε) → t₀` and `σ₂(ε) → t₀` using a compactness argument (`IsCompact.exists_isMinOn`) on `Icc γ.a γ.b \ Metric.ball t₀ (δ/2)` together with `honly`. Promote those to `𝓝[<] t₀` / `𝓝[>] t₀` via `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`. Compose with `hdir_L`, `hdir_R` to obtain the directional limits `−L_L/‖L_L‖`, `L_R/‖L_R‖` along `σ₁`, `σ₂`. Algebraic identity step: case-split on whether `t₀ ∈ γ.partition`. In the corner case, polar decomposition `Complex.norm_mul_exp_arg_mul_I` rewrites `−L_L/‖L_L‖` as `exp(arg(−L_left)·I)` and `L_R/‖L_R‖` as `exp(arg(L_right)·I)`, hence the quotient equals `exp(i(arg(−L_left) − arg(L_right))) = exp(−i·α)` where `α = arg(L_right) − arg(−L_left) = angleAtCrossing γ t₀ ht₀`. In the smooth case, `L_L = L_R` so the ratio is `−1 = exp(−iπ)`. Finally, `Tendsto.congr'` uses `‖γ(σ₁)−z₀‖ = ε = ‖γ(σ₂)−z₀‖` to identify the actual ratio with the direction ratio.
- **Hypotheses**: standard cutoff-time data eventually as `ε → 0⁺`; isolated crossing.
- **Uses from project**: `immersion_one_sided_setup`, `immersion_slope_tendsto_right`, `immersion_slope_tendsto_left`, `immersion_direction_tendsto_right`, `immersion_direction_tendsto_left`, `PiecewiseC1Immersion.continuous_toFun`, `PiecewiseC1Immersion.left_deriv_limit`, `PiecewiseC1Immersion.right_deriv_limit`, `PiecewiseC1Immersion.toPiecewiseC1Curve`, `PiecewiseC1Curve.partition`, `angleAtCrossing`, `PiecewiseC1Immersion.deriv_continuous_off_partition`.
- **Used by**: `tendsto_exp_cutoff_integral_crossing`.
- **Visibility**: public.
- **Lines**: 884–1079.
- **Notes**: 196-line proof.

### `lemma tendsto_exp_cutoff_integral_crossing`
- **Type**: `(γ : PiecewiseC1Immersion) (hclosed : γ.toPiecewiseC1Curve.IsClosed) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = z₀) (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀) : Tendsto (fun ε => Complex.exp (∫ t in γ.a..γ.b, if ‖γ.toFun t - z₀‖ > ε then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0)) (𝓝[>] 0) (𝓝 (Complex.exp (-(I * ↑(angleAtCrossing γ t₀ ht₀)))))`
- **What**: Headline result — for a closed piecewise-C¹ immersion crossing `z₀` exactly once at `t₀`, the exponential of the cutoff log-derivative integral tends to `exp(−i·angleAtCrossing γ t₀ ht₀)` as `ε → 0⁺`. This is the H-W Proposition 2.2 statement.
- **How**: Obtain `δ` from `exists_cutoff_boundary_times`. Use `Classical.choose` to extract σ₁(ε), σ₂(ε) on the parameter range `Ioo 0 δ`, defaulting to `t₀` outside. Eventually as `ε → 0⁺`, `ε ∈ Ioo 0 δ` (via `Ioo_mem_nhdsGT`), and the chosen σ-properties hold. Use `exp_cutoff_integral_eq_ratio` to identify the exponential with `(γ(σ₁)−z₀)/(γ(σ₂)−z₀)` eventually, then `crossing_ratio_tendsto` to pass to the limit. Conclude with `Tendsto.congr'`.
- **Hypotheses**: closed immersion; isolated crossing.
- **Uses from project**: `exists_cutoff_boundary_times`, `exp_cutoff_integral_eq_ratio`, `crossing_ratio_tendsto`, `angleAtCrossing`, `PiecewiseC1Immersion.toPiecewiseC1Curve`, `PiecewiseC1Curve.IsClosed`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 1096–1148.

---

## File Summary

- **Total declarations**: 11 (all `lemma`; none `private`, no `def`).
- **Key API (downstream entry points)**:
  - `tendsto_exp_cutoff_integral_crossing` — main externally-facing theorem (H-W Prop 2.2).
  - `exists_cutoff_boundary_times`, `exists_cutoff_boundary_times_with_mono` — cutoff-interval existence.
  - `exp_cutoff_integral_eq_ratio` — exact formula at fixed `ε`.
  - `crossing_ratio_tendsto` — direction-limit identity used inside the main theorem.
  - `piecewiseC1Immersion_norm_strictMono_near_crossing` — local strict monotonicity of `‖γ − z₀‖`.
- **Unused (within this file)**: `exists_cutoff_boundary_times_with_mono` and `tendsto_exp_cutoff_integral_crossing` are not consumed inside the file (the latter is the public payload). All other lemmas have an in-file user.
- **Sorries**: 0.
- **`set_option`**: 0.
- **Custom axioms**: 0.
- **Long proofs (> 30 lines)**: 6 (immersion_one_sided_setup ~64; piecewiseC1Immersion_norm_strictMono_near_crossing ~168; exists_cutoff_boundary_times ~162; exists_cutoff_boundary_times_with_mono ~37; exp_cutoff_integral_eq_ratio ~308; crossing_ratio_tendsto ~196; tendsto_exp_cutoff_integral_crossing ~53).
- **Purpose**: Self-contained core analytic toolkit for understanding what happens when a closed piecewise-C¹ immersion `γ : [a,b] → ℂ` crosses through a singularity `z₀` at an interior time `t₀`. Provides: nonzero one-sided derivative limits at the crossing; strict monotonicity of `‖γ − z₀‖` on small neighborhoods; existence and IVT-built characterisation of cutoff times `σ₁(ε), σ₂(ε)`; an exact identity `exp(∫_{‖γ−z₀‖>ε} (γ−z₀)⁻¹ γ' dt) = (γ(σ₁) − z₀)/(γ(σ₂) − z₀)` via a G-function/FTC argument adapted from `exp_integral_eq_endpoint_ratio_piecewise`; and finally the limiting identity `exp(R(ε)) → exp(−i·angleAtCrossing γ t₀ ht₀)`. This is the Hungerbühler–Wasem Proposition 2.2 analytic engine that turns Cauchy principal value contour integrals into geometric angle data, and it underpins the generalized winding number `angleAtCrossing` in `Defs.lean`.
