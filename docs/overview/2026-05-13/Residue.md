# Residue.lean — Inventory

### `def cauchyPrincipalValueIntegrandOn`
- **Type**: `(S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (ε t : ℝ) : ℂ`
- **What**: Multi-point PV integrand: returns `0` near any pole in `S` (`‖γ t - s‖ ≤ ε`), else `f(γ t) · γ'(t)`.
- **How**: Direct definition via `if ∃ s ∈ S, ‖γ t - s‖ ≤ ε`.
- **Hypotheses**: None (definition).
- **Uses from project**: []
- **Used by**: `cauchyPrincipalValueOn`, `CauchyPrincipalValueExistsOn`, `cauchyPrincipalValueIntegrandOn_eq_of_far`, `cauchyPrincipalValueIntegrandOn_empty`, `cauchyPrincipalValueIntegrandOn_singleton`, `cauchyPrincipalValueOn_empty`, `cpv_eq_classical_eventually_of_avoids`, `cauchyPrincipalValueExistsOn_avoids`, `cauchyPrincipalValueOn_avoids`
- **Visibility**: public
- **Lines**: 38–42
- **Notes**: noncomputable.

### `def cauchyPrincipalValueOn`
- **Type**: `(S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) : ℂ`
- **What**: Multi-point CPV: `limUnder` as `ε → 0⁺` of `∫_a^b cauchyPrincipalValueIntegrandOn S f γ ε`.
- **How**: Direct definition via `limUnder (𝓝[>] 0)`.
- **Hypotheses**: None.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`
- **Used by**: `cauchyPrincipalValueOn_empty`, `cauchyPrincipalValueOn_avoids`
- **Visibility**: public
- **Lines**: 45–50
- **Notes**: noncomputable.

### `def CauchyPrincipalValueExistsOn`
- **Type**: `(S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) : Prop`
- **What**: Existence predicate: there is some `L` toward which the cutoff integrals converge as `ε → 0⁺`.
- **How**: `∃ L, Tendsto (fun ε => ∫_a^b ...) (𝓝[>] 0) (𝓝 L)`.
- **Hypotheses**: None.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`
- **Used by**: `cauchyPrincipalValueExistsOn_avoids`
- **Visibility**: public
- **Lines**: 53–59

### `def residueSimplePole`
- **Type**: `(f : ℂ → ℂ) (z₀ : ℂ) : ℂ`
- **What**: Residue of `f` at simple pole `z₀` via `lim_{z → z₀} (z - z₀) · f z`.
- **How**: `limUnder (𝓝[≠] z₀) fun z => (z - z₀) * f z`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `singular_term_intervalIntegrable`, `singular_sum_intervalIntegrable`, `residue_simple_pole_eq_laurent`, `integral_singular_term_eq_winding_times_coeff`, `differentiableAt_singular_sum`, `differentiableAt_g_off_poles`, `continuousAt_g_at_pole`, `diff_punctured_of_diff_off_poles`, `simple_poles_decomposition`, `singular_sum_eq_winding_residues`, `integral_eq_sum_residues_of_avoids`
- **Visibility**: public
- **Lines**: 63–64
- **Notes**: noncomputable.

### `def HasSimplePoleAt`
- **Type**: `(f : ℂ → ℂ) (z₀ : ℂ) : Prop`
- **What**: `f(z) = c/(z - z₀) + g(z)` near `z₀` with `g` analytic at `z₀`.
- **How**: `∃ c g, AnalyticAt ℂ g z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀, f z = c/(z-z₀) + g z`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `simple_poles_decomposition`, `integral_eq_sum_residues_of_avoids`
- **Visibility**: public
- **Lines**: 68–70

### `private lemma bounded_on_Ioo_of_continuousOn_with_limits`
- **Type**: `{f : ℝ → ℂ} {a b : ℝ} (_hab : a < b) (hf_cont : ContinuousOn f (Ioo a b)) (hf_left : ∃ L, Tendsto f (𝓝[>] a) (𝓝 L)) (hf_right : ∃ L, Tendsto f (𝓝[<] b) (𝓝 L)) : ∃ M, ∀ t ∈ Ioo a b, ‖f t‖ ≤ M`
- **What**: A continuous function on `Ioo a b` with one-sided limits at endpoints is bounded.
- **How**: Extend `f` to `Icc a b` via `extendFrom` using `continuousOn_Icc_extendFrom_Ioo`, then apply `isCompact_Icc.exists_bound_of_continuousOn`.
- **Hypotheses**: `a < b`, `f` continuous on `Ioo a b`, one-sided limits exist at both ends.
- **Uses from project**: []
- **Used by**: `deriv_bounded_on_consecutive_pair`
- **Visibility**: private
- **Lines**: 72–87

### `private lemma deriv_bounded_on_consecutive_pair`
- **Type**: `(γ : PiecewiseC1Immersion) {p q : ℝ} (hp : p ∈ γ.partition) (hq : q ∈ γ.partition) (hp_lt_q : p < q) (h_consec : ∀ r ∈ γ.partition, ¬(p < r ∧ r < q)) : ∃ M, ∀ t ∈ Ioo p q, ‖deriv γ.toFun t‖ ≤ M`
- **What**: Between two consecutive partition points of a piecewise C¹ immersion, the derivative is bounded.
- **How**: Use `γ.deriv_continuous_off_partition` for continuity on the interior, then `γ.right_deriv_limit p` and `γ.left_deriv_limit q` to get one-sided limits at the endpoints; chain into `bounded_on_Ioo_of_continuousOn_with_limits`.
- **Hypotheses**: `p, q ∈ γ.partition`, consecutive (no point strictly between).
- **Uses from project**: `PiecewiseC1Immersion`, `bounded_on_Ioo_of_continuousOn_with_limits`
- **Used by**: `piecewiseC1Immersion_deriv_bounded`
- **Visibility**: private
- **Lines**: 89–117
- **Notes**: >10 lines; uses `γ.toPiecewiseC1Curve.deriv_continuous_off_partition`, `γ.right_deriv_limit`, `γ.left_deriv_limit`.

### `private lemma off_partition_in_consecutive_pair`
- **Type**: `(γ : PiecewiseC1Immersion) (t : ℝ) (ht : t ∈ Icc γ.a γ.b) (ht_nP : t ∉ (↑γ.partition : Set ℝ)) : ∃ p q ∈ γ.partition, p < q ∧ (∀ r ∈ γ.partition, ¬(p < r ∧ r < q)) ∧ t ∈ Ioo p q`
- **What**: A point in `[a,b]` not in the partition lies in a maximal open subinterval between consecutive partition points.
- **How**: Take `p := max'` of `{partition < t}` and `q := min'` of `{partition > t}`; nonemptiness comes from `endpoints_in_partition`. Consecutivity verified by case split on `r < t`, `r = t`, `t < r` using `Finset.le_max'` / `Finset.min'_le`.
- **Hypotheses**: `t ∈ Icc γ.a γ.b`, `t ∉ partition`.
- **Uses from project**: `PiecewiseC1Immersion`
- **Used by**: `piecewiseC1Immersion_deriv_bounded`
- **Visibility**: private
- **Lines**: 119–154
- **Notes**: >10 lines; uses `Finset.max'_mem`, `Finset.min'_mem`.

### `lemma piecewiseC1Immersion_deriv_bounded`
- **Type**: `(γ : PiecewiseC1Immersion) : ∃ M, ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M`
- **What**: The derivative of a piecewise C¹ immersion is bounded on `[a,b]`.
- **How**: Split into partition points (use `Finset.sup'` over `‖deriv γ p‖`) and off-partition points (induct over the finite `pairs := (P ×ˢ P).filter consecutive` using `deriv_bounded_on_consecutive_pair`); take the max.
- **Hypotheses**: None beyond the structure.
- **Uses from project**: `PiecewiseC1Immersion`, `deriv_bounded_on_consecutive_pair`, `off_partition_in_consecutive_pair`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 157–202
- **Notes**: >10 lines; key lemma `Finset.induction` over consecutive pairs.

### `lemma piecewiseC1_deriv_intervalIntegrable`
- **Type**: `(γ : PiecewiseC1Curve) (h_bdd : ∃ M, ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M) : IntervalIntegrable (deriv γ.toFun) volume γ.a γ.b`
- **What**: A bounded a.e.-strongly-measurable derivative on `[γ.a, γ.b]` is interval integrable.
- **How**: `MeasureTheory.IntegrableOn.of_bound` with bound `M`, finite measure on `uIoc`, and the bound applied a.e. on `Icc`.
- **Hypotheses**: `γ : PiecewiseC1Curve`, bound `M` for `‖deriv γ.toFun‖` on `[γ.a, γ.b]`.
- **Uses from project**: `PiecewiseC1Curve`
- **Used by**: `singular_term_intervalIntegrable`, `singular_sum_intervalIntegrable`, `holomorphic_closed_integral_zero`, `singular_sum_eq_winding_residues`, `integral_eq_sum_residues_of_avoids`
- **Visibility**: public
- **Lines**: 205–221

### `lemma singular_term_intervalIntegrable`
- **Type**: `(f : ℂ → ℂ) (s : ℂ) (γ : PiecewiseC1Curve) (hγ_avoids_s : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) (hγ'_bdd : ...) : IntervalIntegrable (fun t => residueSimplePole f s / (γ.toFun t - s) * deriv γ.toFun t) volume γ.a γ.b`
- **What**: A single singular term `c/(γ - s) · γ'` is interval integrable when `γ` avoids `s`.
- **How**: Show `residueSimplePole f s / (γ - s)` is `ContinuousOn (uIcc γ.a γ.b)` via `ContinuousOn.div` (denominator nonzero by `sub_ne_zero.mpr hγ_avoids_s`), then `piecewiseC1_deriv_intervalIntegrable.continuousOn_mul`.
- **Hypotheses**: `γ` avoids `s` on `[γ.a, γ.b]`, deriv bounded.
- **Uses from project**: `PiecewiseC1Curve`, `residueSimplePole`, `piecewiseC1_deriv_intervalIntegrable`
- **Used by**: `singular_sum_intervalIntegrable`
- **Visibility**: public
- **Lines**: 224–239

### `lemma singular_sum_intervalIntegrable`
- **Type**: `(f : ℂ → ℂ) (S0 : Finset ℂ) (γ : PiecewiseC1Curve) (hγ_avoids : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) (hγ'_bdd : ...) : IntervalIntegrable (fun t => ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s) * deriv γ.toFun t) volume γ.a γ.b`
- **What**: The full singular sum `Σ c_s/(γ - s)·γ'` is interval integrable when `γ` avoids all poles.
- **How**: Induction on `S0` via `Finset.induction_on`; base case `intervalIntegrable_const`; inductive step uses `singular_term_intervalIntegrable` for the new term and adds it to the inductive hypothesis.
- **Hypotheses**: `γ` avoids every `s ∈ S0`, deriv bounded.
- **Uses from project**: `PiecewiseC1Curve`, `residueSimplePole`, `singular_term_intervalIntegrable`
- **Used by**: `integral_eq_sum_residues_of_avoids`
- **Visibility**: public
- **Lines**: 242–269

### `theorem residue_simple_pole_eq_laurent`
- **Type**: `(f : ℂ → ℂ) (z₀ c : ℂ) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g z₀) (hf : ∀ᶠ z in 𝓝[≠] z₀, f z = c/(z - z₀) + g z) : residueSimplePole f z₀ = c`
- **What**: For a simple-pole decomposition, the residue equals the Laurent coefficient `c`.
- **How**: Set up `(fun z => c + (z - z₀)·g z) =ᶠ[𝓝[≠] z₀] fun z => (z - z₀)·f z` via `field_simp`, show the LHS tends to `c` (using `hg.continuousAt.tendsto` and `tendsto.mul` with `(z - z₀) → 0`), then `tendsto.limUnder_eq`.
- **Hypotheses**: `g` analytic at `z₀`, eventual Laurent identity for `f`.
- **Uses from project**: `residueSimplePole`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 272–306
- **Notes**: >10 lines; key step `Tendsto.limUnder_eq`.

### `lemma integral_singular_term_eq_winding_times_coeff`
- **Type**: `(γ : PiecewiseC1Curve) (s c : ℂ) (h_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) : ∫ t in γ.a..γ.b, c / (γ.toFun t - s) * deriv γ.toFun t = 2πI · generalizedWindingNumber' γ.toFun γ.a γ.b s · c`
- **What**: The integral of a singular term equals `2πI · winding · c`.
- **How**: Rewrite via `generalizedWindingNumber_eq_classical_away` to turn `∫ (γ - s)⁻¹ · γ'` into `2πI · winding`; then factor out `c` using `intervalIntegral.integral_smul` and `ring`.
- **Hypotheses**: `γ` avoids `s` on `[γ.a, γ.b]`.
- **Uses from project**: `PiecewiseC1Curve`, `generalizedWindingNumber'`, `generalizedWindingNumber_eq_classical_away`
- **Used by**: `singular_sum_eq_winding_residues`
- **Visibility**: public
- **Lines**: 309–334

### `private lemma differentiableAt_singular_sum`
- **Type**: `(f : ℂ → ℂ) (S0 : Finset ℂ) (w : ℂ) (hw_not_in_S0 : w ∉ (S0 : Set ℂ)) : DifferentiableAt ℂ (fun v => ∑ s ∈ S0, residueSimplePole f s / (v - s)) w`
- **What**: The sum `Σ c_s/(v - s)` is differentiable at any `w` outside `S0`.
- **How**: Apply `DifferentiableAt.sum` over `S0`; each summand is `const.div ((id.sub const), sub_ne_zero.mpr (w ≠ s))`. Then `convert hh using 1; ext; simp` to massage `Finset.sum_apply`.
- **Hypotheses**: `w ∉ S0`.
- **Uses from project**: `residueSimplePole`
- **Used by**: `differentiableAt_g_off_poles`
- **Visibility**: private
- **Lines**: 336–350

### `private lemma differentiableAt_g_off_poles`
- **Type**: `(U : Set ℂ) (hU : IsOpen U) (S0 : Finset ℂ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0)) (w : ℂ) (hw_in_U : w ∈ U) (hw_not_in_S0 : w ∉ (S0 : Set ℂ)) : DifferentiableAt ℂ (fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s)) w`
- **What**: Off `S0`, the residue-subtracted function `g = f - singular_sum` is differentiable.
- **How**: Use `hf.differentiableAt` on `U \ S0` (which is a nbhd of `w` via `(hU.sdiff S0.finite_toSet.isClosed).mem_nhds`), then subtract `differentiableAt_singular_sum`.
- **Hypotheses**: `U` open, `f` differentiable off `S0`, `w ∈ U` and `w ∉ S0`.
- **Uses from project**: `residueSimplePole`, `differentiableAt_singular_sum`
- **Used by**: `diff_punctured_of_diff_off_poles`, `simple_poles_decomposition`
- **Visibility**: private
- **Lines**: 352–361

### `private lemma continuousAt_g_at_pole`
- **Type**: `(S0 : Finset ℂ) (f : ℂ → ℂ) (z : ℂ) (hs : z ∈ S0) (hf_ext : ContinuousAt (fun w => f w - residueSimplePole f z / (w - z)) z) : ContinuousAt (fun w => f w - ∑ s ∈ S0, residueSimplePole f s / (w - s)) z`
- **What**: At a pole `z ∈ S0`, removal of the `z`-term from the sum gives a function continuous at `z` via the regularization hypothesis.
- **How**: Split `Σ_{S0} = (Σ_{S0.filter (=z)}) + (Σ_{S0.filter (≠z)})`, recognize first as the singleton `c_z/(w - z)`, and observe other summands `c_s/(w - s)` (s ≠ z) are continuous at `z`. Combine with `hf_ext` via `funext` + `hf_ext.sub h2`.
- **Hypotheses**: `z ∈ S0`, removed-pole regularization continuous at `z`.
- **Uses from project**: `residueSimplePole`
- **Used by**: `simple_poles_decomposition`
- **Visibility**: private
- **Lines**: 363–396
- **Notes**: >10 lines; key step `Finset.sum_union` to split into singleton + rest.

### `private lemma diff_punctured_of_diff_off_poles`
- **Type**: `(U : Set ℂ) (hU : IsOpen U) (S0 : Finset ℂ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0)) (z : ℂ) (hz : z ∈ U) : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ (fun v => f v - ∑ s ∈ S0, residueSimplePole f s / (v - s)) w`
- **What**: `g = f - singular_sum` is differentiable on a punctured neighborhood of any `z ∈ U`.
- **How**: Take `ε₁` for `U`-neighborhood; if `S0 ⊆ {z}` we just need the `ε₁`-ball minus `{z}`; otherwise compute `δ := inf‖s - z‖` over `S0.filter (≠ z)` and use `min ε₁ δ` to ensure `w ∉ S0`. Apply `differentiableAt_g_off_poles`.
- **Hypotheses**: `U` open, `f` differentiable off `S0`, `z ∈ U`.
- **Uses from project**: `residueSimplePole`, `differentiableAt_g_off_poles`
- **Used by**: `simple_poles_decomposition`
- **Visibility**: private
- **Lines**: 398–432
- **Notes**: >10 lines; uses `Finset.inf'_le` and `Finset.lt_inf'_iff`.

### `lemma simple_poles_decomposition`
- **Type**: `(U : Set ℂ) (hU : IsOpen U) (S0 : Finset ℂ) (_hS0_in_U : ∀ s ∈ S0, s ∈ U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0)) (_hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s) (hf_ext : ∀ s ∈ S0, ContinuousAt (fun z => f z - residueSimplePole f s / (z - s)) s) : let g := fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s); DifferentiableOn ℂ g U ∧ ∀ z ∈ U \ S0, f z = (∑ s ∈ S0, residueSimplePole f s / (z - s)) + g z`
- **What**: With simple poles + a regularization hypothesis, `g = f - Σ c_s/(z - s)` is differentiable on all of `U`, and the decomposition holds off the poles.
- **How**: Off-poles case: `differentiableAt_g_off_poles`. At-poles case: `continuousAt_g_at_pole` + `diff_punctured_of_diff_off_poles` + `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`. Decomposition identity off poles is `ring`.
- **Hypotheses**: `U` open, `S0 ⊆ U`, `f` differentiable off `S0`, simple poles, regularization continuous at each pole.
- **Uses from project**: `residueSimplePole`, `HasSimplePoleAt`, `differentiableAt_g_off_poles`, `continuousAt_g_at_pole`, `diff_punctured_of_diff_off_poles`
- **Used by**: `integral_eq_sum_residues_of_avoids`
- **Visibility**: public (declared without `private`; intentionally non-private per memory note)
- **Lines**: 434–453

### `private lemma holomorphic_closed_integral_zero`
- **Type**: `(U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U) (g : ℂ → ℂ) (hg_diff : DifferentiableOn ℂ g U) (γ : PiecewiseC1Curve) (hγ_closed : γ.IsClosed) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) (hγ'_bdd : ...) : ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0`
- **What**: Cauchy's theorem on a convex open set for closed piecewise C¹ curves: integral of a holomorphic function vanishes.
- **How**: Get primitive `F` via `holomorphic_convex_primitive`; show `F ∘ γ` has the right derivative `g(γ)·γ'` off the (countable) partition; use `integral_eq_of_hasDerivAt_off_countable_of_le`; close via `hγ_closed` and `sub_self`.
- **Hypotheses**: `U` open convex, `g` differentiable on `U`, `γ` closed PWC1 curve in `U`, deriv bounded.
- **Uses from project**: `PiecewiseC1Curve`, `holomorphic_convex_primitive`, `piecewiseC1_deriv_intervalIntegrable`
- **Used by**: `integral_eq_sum_residues_of_avoids`
- **Visibility**: private
- **Lines**: 455–482
- **Notes**: >10 lines; key step `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`.

### `private lemma singular_sum_eq_winding_residues`
- **Type**: `(f : ℂ → ℂ) (S0 : Finset ℂ) (γ : PiecewiseC1Curve) (hγ_avoids : ...) (hγ'_bdd : ...) : ∫ t, Σ s ∈ S0, c_s/(γ - s) · γ' = Σ s ∈ S0, 2πI · winding · c_s`
- **What**: The integral of the singular sum equals the winding-weighted sum of residues.
- **How**: Swap sum and integral via `intervalIntegral.integral_finset_sum`; apply `integral_singular_term_eq_winding_times_coeff` to each term.
- **Hypotheses**: `γ` avoids every `s ∈ S0`, deriv bounded.
- **Uses from project**: `PiecewiseC1Curve`, `residueSimplePole`, `generalizedWindingNumber'`, `integral_singular_term_eq_winding_times_coeff`, `piecewiseC1_deriv_intervalIntegrable`
- **Used by**: `integral_eq_sum_residues_of_avoids`
- **Visibility**: private
- **Lines**: 484–505

### `theorem integral_eq_sum_residues_of_avoids`
- **Type**: `(U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U) (S0 : Finset ℂ) (hS0_in_U : ∀ s ∈ S0, s ∈ U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0)) (γ : PiecewiseC1Curve) (hγ_closed : γ.IsClosed) (hγ_in_U : ...) (hγ_avoids : ...) (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s) (hf_ext : ...) (hγ'_bdd : ...) : ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t = 2πI · Σ s ∈ S0, winding · residueSimplePole f s`
- **What**: Classical residue theorem (avoid form): contour integral equals `2πI · Σ winding · residue` when `γ` avoids all poles.
- **How**: Decompose `f = singular_sum + g` via `simple_poles_decomposition`, split the integral, apply `holomorphic_closed_integral_zero` to the `g` part, apply `singular_sum_eq_winding_residues` to the singular part, and finish with `Finset.mul_sum` + `ring`.
- **Hypotheses**: `U` open convex, `S0` ⊆ `U`, `f` differentiable off `S0`, `γ` closed in `U`, avoids poles, simple poles, regularization, deriv bounded.
- **Uses from project**: `PiecewiseC1Curve`, `residueSimplePole`, `HasSimplePoleAt`, `generalizedWindingNumber'`, `simple_poles_decomposition`, `singular_sum_intervalIntegrable`, `holomorphic_closed_integral_zero`, `singular_sum_eq_winding_residues`, `piecewiseC1_deriv_intervalIntegrable`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 509–555
- **Notes**: >10 lines; key combination step `intervalIntegral.integral_add` of singular + holomorphic.

### `lemma cauchyPrincipalValueIntegrandOn_eq_of_far`
- **Type**: `(S0 : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (ε t : ℝ) (h_far : ∀ s ∈ S0, ε < ‖γ t - s‖) : cauchyPrincipalValueIntegrandOn S0 f γ ε t = f (γ t) * deriv γ t`
- **What**: When `γ(t)` is strictly farther than `ε` from all poles, the cutoff integrand equals the raw integrand `f · γ'`.
- **How**: `unfold` and use `if_neg` via `push Not` + `linarith` on the `‖γ t - s‖ > ε` condition.
- **Hypotheses**: For every `s ∈ S0`, `ε < ‖γ t - s‖`.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`
- **Used by**: `cpv_eq_classical_eventually_of_avoids`
- **Visibility**: public
- **Lines**: 557–566

### `lemma cauchyPrincipalValueIntegrandOn_empty`
- **Type**: `(f : ℂ → ℂ) (γ : ℝ → ℂ) (ε t : ℝ) : cauchyPrincipalValueIntegrandOn ∅ f γ ε t = f (γ t) * deriv γ t`
- **What**: With no poles, the cutoff integrand reduces to `f · γ'`.
- **How**: `unfold`, `if_neg` via empty-quantifier `Finset.notMem_empty`.
- **Hypotheses**: None.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`
- **Used by**: `cauchyPrincipalValueOn_empty`, `cauchyPrincipalValueExistsOn_avoids`
- **Visibility**: public
- **Lines**: 568–576

### `lemma cauchyPrincipalValueIntegrandOn_singleton`
- **Type**: `(f : ℂ → ℂ) (γ : ℝ → ℂ) (z₀ : ℂ) (ε t : ℝ) : cauchyPrincipalValueIntegrandOn {z₀} f γ ε t = if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0`
- **What**: For a singleton pole set, the cutoff integrand is `f·γ'` outside the `ε`-disk and `0` inside.
- **How**: Case split on `‖γ t - z₀‖ ≤ ε`; in each branch reduce to the single-pole `if`.
- **Hypotheses**: None.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 578–593

### `lemma cauchyPrincipalValueOn_empty`
- **Type**: `(f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) : cauchyPrincipalValueOn ∅ f γ a b = ∫ t in a..b, f (γ t) * deriv γ t`
- **What**: With no poles, the multi-point CPV equals the classical integral.
- **How**: Recognize the integrand as eventually constant (in `ε`) via `cauchyPrincipalValueIntegrandOn_empty`, then `limUnder_eventually_eq_const`.
- **Hypotheses**: None.
- **Uses from project**: `cauchyPrincipalValueIntegrandOn_empty`, `cauchyPrincipalValueOn`
- **Used by**: `cauchyPrincipalValueOn_avoids`
- **Visibility**: public
- **Lines**: 595–607

### `private lemma cpv_eq_classical_eventually_of_avoids`
- **Type**: `(S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Curve) (h_avoids : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) (hS0_ne : S0.Nonempty) : ∃ δ > 0, ∀ ε ∈ Ioo 0 δ, ∀ t ∈ Set.uIcc γ.a γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t = f (γ.toFun t) * deriv γ.toFun t`
- **What**: When `γ` avoids all poles, the cutoff integrand equals the classical one for all small enough `ε`.
- **How**: Use `IsCompact.image_of_continuousOn` (image of `[a,b]` is compact) + `notMem_iff_infDist_pos` to get strictly positive `infDist`; take `δ := min'` over `S0.image (infDist s ·)`; apply `cauchyPrincipalValueIntegrandOn_eq_of_far`.
- **Hypotheses**: `γ` avoids every `s ∈ S0`, `S0` nonempty.
- **Uses from project**: `PiecewiseC1Curve`, `cauchyPrincipalValueIntegrandOn`, `cauchyPrincipalValueIntegrandOn_eq_of_far`
- **Used by**: `cauchyPrincipalValueExistsOn_avoids`, `cauchyPrincipalValueOn_avoids`
- **Visibility**: private
- **Lines**: 609–638
- **Notes**: >10 lines; key step `Metric.infDist_le_dist_of_mem`.

### `lemma cauchyPrincipalValueExistsOn_avoids`
- **Type**: `(S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Curve) (h_avoids : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) : CauchyPrincipalValueExistsOn S0 f γ.toFun γ.a γ.b`
- **What**: PV exists when curve avoids all singularities; limit is `∫_a^b f · γ'`.
- **How**: Witness `L := ∫_a^b f(γ t) · γ'(t)`. Case split on `S0 = ∅` (use `cauchyPrincipalValueIntegrandOn_empty`) vs `S0 ≠ ∅` (use `cpv_eq_classical_eventually_of_avoids`); apply `Tendsto.congr'` with `tendsto_const_nhds`.
- **Hypotheses**: `γ` avoids every `s ∈ S0`.
- **Uses from project**: `PiecewiseC1Curve`, `CauchyPrincipalValueExistsOn`, `cauchyPrincipalValueIntegrandOn_empty`, `cpv_eq_classical_eventually_of_avoids`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 641–660

### `lemma cauchyPrincipalValueOn_avoids`
- **Type**: `(S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Curve) (h_avoids : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) : cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b = ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t`
- **What**: When `γ` avoids all poles, the multi-point CPV equals the classical integral.
- **How**: Case split on `S0 = ∅` (reduce to `cauchyPrincipalValueOn_empty`) vs nonempty (use `cpv_eq_classical_eventually_of_avoids` + `limUnder_eventually_eq_const`).
- **Hypotheses**: `γ` avoids every `s ∈ S0`.
- **Uses from project**: `PiecewiseC1Curve`, `cauchyPrincipalValueOn`, `cauchyPrincipalValueOn_empty`, `cpv_eq_classical_eventually_of_avoids`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 663–678

### `theorem pv_integral_inverse`
- **Type**: `(γ : PiecewiseC1Curve) (z₀ : ℂ) : cauchyPrincipalValue' (·⁻¹) (fun t => γ.toFun t - z₀) γ.a γ.b 0 = 2πI · generalizedWindingNumber' γ.toFun γ.a γ.b z₀`
- **What**: The single-point CPV of `1/z` along `γ - z₀` equals `2πI · winding`.
- **How**: Unfold `generalizedWindingNumber'` and clear the `2πI ≠ 0` factor via `field_simp`.
- **Hypotheses**: None beyond `γ : PiecewiseC1Curve`.
- **Uses from project**: `PiecewiseC1Curve`, `cauchyPrincipalValue'`, `generalizedWindingNumber'`
- **Used by**: `pv_integral_simple_pole`
- **Visibility**: public
- **Lines**: 681–693

### `theorem pv_integral_simple_pole`
- **Type**: `(γ : PiecewiseC1Curve) (z₀ c : ℂ) (hPV : ∃ L, Tendsto (...cutoff integrand for inverse-of-shifted γ ...) (𝓝[>] 0) (𝓝 L)) : cauchyPrincipalValue' (fun z => c / (z - z₀)) γ.toFun γ.a γ.b z₀ = 2πI · winding · c`
- **What**: Single-point PV for a simple pole `c/(z - z₀)`: equals `2πI · winding · c`.
- **How**: Rewrite the new integrand as `c ·` the inverse integrand from `pv_integral_inverse` via per-`ε` `intervalIntegral.integral_mul_const`; use the extra existence hypothesis `hPV` to conclude both `limUnder` evaluations agree.
- **Hypotheses**: PV existence of the shifted `1/z` integral.
- **Uses from project**: `PiecewiseC1Curve`, `cauchyPrincipalValue'`, `generalizedWindingNumber'`, `pv_integral_inverse`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 696–758
- **Notes**: >10 lines; uses `intervalIntegral.integral_mul_const` + `intervalIntegral.integral_congr`.

---

## File Summary
- **Totals**: 24 declarations (5 defs, 11 lemmas, 8 theorems incl. `theorem residue_simple_pole_eq_laurent` and `pv_integral_inverse/_simple_pole`).
- **Key API**: definitions `cauchyPrincipalValueIntegrandOn`, `cauchyPrincipalValueOn`, `CauchyPrincipalValueExistsOn`, `residueSimplePole`, `HasSimplePoleAt`; the central residue theorem `integral_eq_sum_residues_of_avoids`; PV identities `pv_integral_inverse`, `pv_integral_simple_pole`; integrability infrastructure (`piecewiseC1Immersion_deriv_bounded`, `piecewiseC1_deriv_intervalIntegrable`, `singular_term/sum_intervalIntegrable`); the central decomposition `simple_poles_decomposition` (intentionally non-private per memory).
- **Unused in file**: `piecewiseC1Immersion_deriv_bounded`, `residue_simple_pole_eq_laurent`, `integral_eq_sum_residues_of_avoids`, `cauchyPrincipalValueIntegrandOn_singleton`, `cauchyPrincipalValueExistsOn_avoids`, `cauchyPrincipalValueOn_avoids`, `pv_integral_simple_pole` (these are external-API endpoints).
- **Sorries**: none.
- **`set_option`s**: none.
- **Long proofs (>10 lines)**: `deriv_bounded_on_consecutive_pair`, `off_partition_in_consecutive_pair`, `piecewiseC1Immersion_deriv_bounded`, `residue_simple_pole_eq_laurent`, `continuousAt_g_at_pole`, `diff_punctured_of_diff_off_poles`, `holomorphic_closed_integral_zero`, `integral_eq_sum_residues_of_avoids`, `cpv_eq_classical_eventually_of_avoids`, `pv_integral_simple_pole`.
- **Purpose**: Provides the multi-point Cauchy principal value (`CPV`) framework and a generalized classical residue theorem for piecewise C¹ immersions: defines the cutoff PV integrand and value, sets up residues at simple poles, develops integrability infrastructure for the curve and singular sums, and proves the classical residue identity `∫ f·γ' = 2πI · Σ winding · residue` (the "avoids form") plus its companion PV statements for `1/z` and `c/(z - z₀)`. Forms the analytic backbone connecting the homotopy-invariant winding number to residue calculus on the fundamental-domain contour.
