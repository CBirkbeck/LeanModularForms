# Inventory: Homotopy/Integrality.lean

### `def PiecewiseCurvesHomotopicAvoiding`
- **Type**: `(γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ) : Prop`
- **What**: Predicate: there is a piecewise-C¹ homotopy `H : ℝ × ℝ → ℂ` between closed curves `γ₀`, `γ₁` that avoids `z₀`, with derivative-discontinuity locus contained in the finite partition `P`.
- **How**: Existential bundle of 8 properties: continuity of `H`; boundary equalities `H(t,0) = γ₀ t`, `H(t,1) = γ₁ t`; closure `H(a,s) = H(b,s)`; avoidance `H(t,s) ≠ z₀`; off-`P` differentiability in `t`; continuity of `∂t H` on `Ioo p₁ p₂ ×ˢ Icc 0 1` away from `P`; uniform bound on `‖∂t H‖`.
- **Hypotheses**: none (it's a `def`).
- **Uses from project**: []
- **Used by**: `ClosedCurvesHomotopicAvoiding.toPiecewise`, `PiecewiseCurvesHomotopicAvoiding.toBasic`.
- **Visibility**: public
- **Lines**: 45–65
- **Notes**: structural definition.

### `def ClosedCurvesHomotopicAvoiding`
- **Type**: `(γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop`
- **What**: Predicate: there is a smooth (globally C¹) homotopy `H` between closed curves avoiding `z₀`, no partition needed.
- **How**: Existential bundle: continuity of `H`; boundary/closure/avoidance as above; pointwise differentiability everywhere in `Ioo a b`; global continuity of `(p ↦ deriv (fun t' => H (t', p.2)) p.1)`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `ClosedCurvesHomotopicAvoiding.toPiecewise`.
- **Visibility**: public
- **Lines**: 75–87
- **Notes**: structural definition.

### `theorem ClosedCurvesHomotopicAvoiding.toPiecewise`
- **Type**: `(h : ClosedCurvesHomotopicAvoiding γ₀ γ₁ a b z₀) : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ a b z₀ ∅`
- **What**: A smooth closed homotopy is a piecewise homotopy with empty partition.
- **How**: Destructure the smooth homotopy. The differentiability-off-`∅` condition is vacuous on points not in `∅`. The local continuity of the derivative follows from the global one. The uniform bound: `IsCompact (Icc a b ×ˢ Icc 0 1)` is compact (product of `isCompact_Icc`), and `‖∂t H‖` is continuous, so `IsCompact.exists_bound_of_continuousOn` provides `M`.
- **Hypotheses**: smooth closed homotopy `h`.
- **Uses from project**: `PiecewiseCurvesHomotopicAvoiding`, `ClosedCurvesHomotopicAvoiding`
- **Used by**: unused in file (consumer is downstream).
- **Visibility**: public
- **Lines**: 117–133

### `theorem PiecewiseCurvesHomotopicAvoiding.toBasic`
- **Type**: `(h : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ a b z₀ P) (hpts : … endpoint condition …) : CurvesHomotopicAvoiding γ₀ γ₁ a b z₀`
- **What**: A piecewise homotopy with an external endpoint hypothesis gives a basic `CurvesHomotopicAvoiding` homotopy.
- **How**: Destructure `h` and assemble `CurvesHomotopicAvoiding`: continuity, boundary values, the endpoint condition supplied externally via `hpts`, and avoidance restricted from `Icc` to `Ioo`.
- **Hypotheses**: piecewise homotopy plus external endpoint witness.
- **Uses from project**: `PiecewiseCurvesHomotopicAvoiding`, `CurvesHomotopicAvoiding`
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 142–154

### `theorem limUnder_eventually_eq_const`
- **Type**: `{α : Type*} [TopologicalSpace α] {f : α → ℂ} {l : Filter α} {c : ℂ} [l.NeBot] (hf : ∀ᶠ x in l, f x = c) : limUnder l f = c`
- **What**: If `f` is eventually constant `c` along filter `l`, then `limUnder l f = c`.
- **How**: `(tendsto_const_nhds.congr' (hf.mono ...)).limUnder_eq`.
- **Hypotheses**: filter `l` is non-trivial; `f` eventually equals `c`.
- **Uses from project**: []
- **Used by**: `pv_eq_integral_of_bound_away`.
- **Visibility**: public
- **Lines**: 157–159

### `lemma exists_ball_avoiding_finset`
- **Type**: `{P : Finset ℝ} {t : ℝ} (ht : t ∉ P) : ∃ ε > 0, ∀ x ∈ Ioo (t - ε) (t + ε), x ∉ P`
- **What**: A point not in a finite set has an open ball entirely disjoint from the set.
- **How**: Case `P = ∅` (use `ε = 1`). Otherwise `d := Finset.inf' P P_ne (fun p => |p - t|)` is positive (each `|p - t| > 0` since `p ≠ t`). Take `ε = d/2`.
- **Hypotheses**: `t ∉ P`.
- **Uses from project**: []
- **Used by**: `logDeriv_continuousOn_off_finset`, `logDeriv_continuousAt_off_finset`, `logDeriv_stronglyMeasurableAtFilter_off_finset`.
- **Visibility**: public
- **Lines**: 162–177

### `private lemma bound_away_from_z₀`
- **Type**: `(γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b) (hγ_cont : ContinuousOn γ (Icc a b)) (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀) : ∃ δ > 0, ∀ t ∈ Icc a b, δ ≤ ‖γ t - z₀‖`
- **What**: A continuous curve on a compact set avoiding `z₀` keeps a uniform distance from `z₀`.
- **How**: `γ '' Icc a b` is compact, nonempty, doesn't contain `z₀`. `IsClosed.notMem_iff_infDist_pos` gives `δ := Metric.infDist z₀ (γ '' Icc a b) > 0`. For each `t`, `infDist ≤ dist z₀ (γ t)`.
- **Hypotheses**: `a < b`, `γ` continuous and avoids `z₀`.
- **Uses from project**: []
- **Used by**: `windingNumber_integer_of_piecewise_with_bound`, `exp_integral_eq_endpoint_ratio_piecewise`, `windingNumber_integer_of_closed_avoiding`.
- **Visibility**: private
- **Lines**: 179–191

### `private lemma logDeriv_integrand_bound`
- **Type**: `{γ a b z₀ M δ} (hδ : 0 < δ) (hδ_bd : ∀ t ∈ Icc a b, δ ≤ ‖γ t - z₀‖) (hM : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M) (t : ℝ) (ht : t ∈ Icc a b) : ‖deriv γ t / (γ t - z₀)‖ ≤ M / δ`
- **What**: The log-derivative integrand is uniformly bounded by `M/δ`.
- **How**: `norm_div`, then `div_le_div_of_nonneg_left/right`.
- **Hypotheses**: `δ`-separation, `M`-bound on `deriv γ`.
- **Uses from project**: []
- **Used by**: `windingNumber_integer_of_piecewise_with_bound`, `exp_integral_eq_endpoint_ratio_piecewise`.
- **Visibility**: private
- **Lines**: 193–202

### `private lemma logDeriv_continuousOn_off_finset`
- **Type**: `(hγ_cont) (hγ_deriv_cont) (hγ_avoids) : ContinuousOn (fun t => deriv γ t / (γ t - z₀)) (Icc a b \ (P ∪ {a, b}))`
- **What**: The log-derivative integrand is continuous on `Icc a b` minus the finite set `P ∪ {a, b}`.
- **How**: For `t ∉ P ∪ {a,b}`, locate `t` in an `Ioo p₁ p₂ ⊆ Ioo a b` with `P ∩ Ioo p₁ p₂ = ∅` via `exists_ball_avoiding_finset`. Then `hγ_deriv_cont` gives `ContinuousAt (deriv γ) t`. `ContinuousWithinAt.div` of numerator and denominator.
- **Hypotheses**: continuity, local derivative-continuity off `P`, avoidance.
- **Uses from project**: `exists_ball_avoiding_finset`
- **Used by**: `windingNumber_integer_of_piecewise_with_bound`, `exp_integral_eq_endpoint_ratio_piecewise`.
- **Visibility**: private
- **Lines**: 204–239
- **Notes**: >10 lines (~36); key lemma `ContinuousWithinAt.div`.

### `private lemma logDeriv_continuousAt_off_finset`
- **Type**: `(hγ_cont) (hγ_deriv_cont) (hγ_avoids) {t : ℝ} (ht : t ∈ Ioo a b) (ht_notP : t ∉ P) : ContinuousAt (fun t => deriv γ t / (γ t - z₀)) t`
- **What**: At any interior point off `P`, the log-derivative integrand is continuous.
- **How**: Same local-shrinking technique with `exists_ball_avoiding_finset`; combine `ContinuousAt.div` of `deriv γ` (continuous by `hγ_deriv_cont` on a small `Ioo`) with `(γ - const)` continuity.
- **Hypotheses**: `t ∈ Ioo a b`, `t ∉ P`.
- **Uses from project**: `exists_ball_avoiding_finset`
- **Used by**: `logDeriv_integral_hasDerivAt_off_finset`.
- **Visibility**: private
- **Lines**: 241–272
- **Notes**: >10 lines (~32); key lemma `ContinuousAt.div`.

### `private lemma logDeriv_stronglyMeasurableAtFilter_off_finset`
- **Type**: `(hγ_cont) (hγ_deriv_cont) (hγ_avoids) {t} (ht : t ∈ Ioo a b) (ht_notP : t ∉ P) : StronglyMeasurableAtFilter (fun t => deriv γ t / (γ t - z₀)) (𝓝 t) volume`
- **What**: The integrand is strongly measurable at the filter `𝓝 t` (needed for FTC integral).
- **How**: Build a local `Ioo p₁ p₂` (same recipe), show `ContinuousOn` on it, apply `ContinuousAt.stronglyMeasurableAtFilter` for `isOpen_Ioo`.
- **Hypotheses**: same.
- **Uses from project**: `exists_ball_avoiding_finset`
- **Used by**: `logDeriv_integral_hasDerivAt_off_finset`.
- **Visibility**: private
- **Lines**: 274–310
- **Notes**: >10 lines (~37); key lemma `ContinuousAt.stronglyMeasurableAtFilter`.

### `private lemma logDeriv_integral_hasDerivAt_off_finset`
- **Type**: `(hab : a < b) (hγ_cont) (hγ_deriv_cont) (hγ_avoids) (h_int) {t} (ht : t ∈ Ioo a b) (ht_notP : t ∉ P) : HasDerivAt (fun t => ∫ s in a..t, deriv γ s / (γ s - z₀)) (deriv γ t / (γ t - z₀)) t`
- **What**: FTC on the punctured indefinite integral of the log-derivative integrand.
- **How**: `intervalIntegral.integral_hasDerivAt_right` with: integrability (mono'd to `uIcc a t ⊆ uIcc a b`), strongly-measurable-at-filter (from the previous lemma), continuity at `t` (from the previous lemma).
- **Hypotheses**: `a < b`, continuity, derivative-continuity, avoidance, interval integrability, `t ∈ Ioo a b` off `P`.
- **Uses from project**: `logDeriv_stronglyMeasurableAtFilter_off_finset`, `logDeriv_continuousAt_off_finset`
- **Used by**: `gFunc_deriv_zero_off_finset`, `gFunc_constant_piecewise`.
- **Visibility**: private
- **Lines**: 312–330

### `private lemma gFunc_deriv_zero_off_finset`
- **Type**: `(hab) (hγ_cont) (hγ_diff) (hγ_deriv_cont) (hγ_avoids) (h_int) {t} (ht : t ∈ Ioo a b) (ht_notP : t ∉ P) : let F := ...; let G := ...; deriv G t = 0`
- **What**: Define `F = primitive of γ'/(γ-z₀)`, `G(t) = (γ - z₀) · exp(-F)`. Then `G' = 0` off `P`.
- **How**: `HasDerivAt` of `G` is computed via product rule `(γ - z₀)' · exp(-F) + (γ - z₀) · exp(-F) · (-F')`. Use `hγ_diff` for `γ'`, and `logDeriv_integral_hasDerivAt_off_finset` for `F'`. Then `field_simp; ring` cancels.
- **Hypotheses**: as above.
- **Uses from project**: `logDeriv_integral_hasDerivAt_off_finset`
- **Used by**: `gFunc_constant_piecewise`.
- **Visibility**: private
- **Lines**: 332–356
- **Notes**: >10 lines (~25); key lemma `HasDerivAt.mul`.

### `private lemma gFunc_constant_piecewise`
- **Type**: `(hab) (hγ_cont) (hγ_diff) (hγ_deriv_cont) (hγ_avoids) (h_int) : ∀ t ∈ Icc a b, G t = G a`
- **What**: `G` is constant on `Icc a b` (for the piecewise setting).
- **How**: `G` is continuous (product of continuous parts and `exp ∘ -F`). `G` is differentiable off `P` with `G' = 0` by `gFunc_deriv_zero_off_finset`. Apply `constant_of_has_deriv_right_zero` via `hasDerivWithinAt_zero_of_deriv_zero_off_finite`.
- **Hypotheses**: as above.
- **Uses from project**: `gFunc_deriv_zero_off_finset`, `logDeriv_integral_hasDerivAt_off_finset`
- **Used by**: `exp_neg_integral_eq_one_of_closed`, `exp_integral_eq_endpoint_ratio_piecewise`.
- **Visibility**: private
- **Lines**: 358–388
- **Notes**: >10 lines (~31); key lemmas `constant_of_has_deriv_right_zero`, `hasDerivWithinAt_zero_of_deriv_zero_off_finite`.

### `private lemma pv_eq_integral_of_bound_away`
- **Type**: `(hab : a < b) (hδ : 0 < δ) (hδ_bd : ∀ t ∈ Icc a b, δ ≤ ‖γ t - z₀‖) : cauchyPrincipalValue' (·⁻¹) (fun t => γ t - z₀) a b 0 = ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t`
- **What**: When `γ` is bounded away from `z₀`, the CPV (with the curve translated to avoid 0) collapses to the plain integral.
- **How**: Unfold `cauchyPrincipalValue'`. For small `ε ∈ (0, δ)`, the indicator `‖γ t - z₀‖ > ε` is always true. `intervalIntegral.integral_congr_ae` and `limUnder_eventually_eq_const`.
- **Hypotheses**: separation `δ`.
- **Uses from project**: `cauchyPrincipalValue'`, `limUnder_eventually_eq_const`
- **Used by**: `winding_integer_from_exp_one`, `windingNumber_integer_of_closed_avoiding`.
- **Visibility**: private
- **Lines**: 390–403

### `private lemma exp_neg_integral_eq_one_of_closed`
- **Type**: `(hab) (hγ_closed : γ a = γ b) (hγ_cont) (hγ_diff) (hγ_deriv_cont) (hγ_avoids) (h_int) : Complex.exp (-(∫ t in a..b, deriv γ t / (γ t - z₀))) = 1`
- **What**: For a closed curve avoiding `z₀`, `exp(-∫ γ'/(γ-z₀)) = 1`.
- **How**: `gFunc_constant_piecewise` gives `G(b) = G(a)`. Substitute `γ b = γ a` and `∫_a^a = 0`. Cancel `γ a - z₀` (nonzero by avoidance).
- **Hypotheses**: as above.
- **Uses from project**: `gFunc_constant_piecewise`
- **Used by**: `windingNumber_integer_of_piecewise_with_bound`.
- **Visibility**: private
- **Lines**: 405–427
- **Notes**: >10 lines (~23).

### `private lemma winding_integer_from_exp_one`
- **Type**: `(hab) (hδ : 0 < δ) (hδ_bd) (hFb : ∃ n : ℤ, -(∫ t in a..b, deriv γ t / (γ t - z₀)) = ↑n * (2 * ↑Real.pi * I)) : ∃ n : ℤ, generalizedWindingNumber' γ a b z₀ = n`
- **What**: If the negative of the integral lies in `2πi · ℤ`, then the generalized winding number is `-n ∈ ℤ`.
- **How**: Extract `n` from `hFb`. Use `-n`. Convert generalized winding to ordinary integral via `pv_eq_integral_of_bound_away`. Rewrite `(γ t - z₀)⁻¹ · γ'(t) = γ'(t)/(γ t - z₀)`. Apply `field_simp` after solving for `n`.
- **Hypotheses**: bounded-away curve and `2πi ℤ` quantization.
- **Uses from project**: `pv_eq_integral_of_bound_away`, `generalizedWindingNumber'`
- **Used by**: `windingNumber_integer_of_piecewise_with_bound`.
- **Visibility**: private
- **Lines**: 429–453

### `private lemma windingNumber_integer_of_piecewise_with_bound`
- **Type**: `(γ a b z₀ P M) (hab) (hγ_closed) (hγ_cont) (hγ_diff) (hγ_deriv_cont) (hγ_deriv_bound : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M) (hγ_avoids) : ∃ n : ℤ, generalizedWindingNumber' γ a b z₀ = n`
- **What**: Integrality of winding number for piecewise-C¹ closed curves with an explicit derivative bound `M`.
- **How**: `bound_away_from_z₀` gives `δ`. Build `IntervalIntegrable` of `γ'/(γ-z₀)` from `intervalIntegrable_of_piecewise_continuousOn_bounded` using `logDeriv_continuousOn_off_finset` and `logDeriv_integrand_bound`. Apply `exp_neg_integral_eq_one_of_closed`, then `Complex.exp_eq_one_iff` to obtain the `2πiℤ` form, then `winding_integer_from_exp_one`.
- **Hypotheses**: closed curve, derivative bound, all above.
- **Uses from project**: `bound_away_from_z₀`, `logDeriv_continuousOn_off_finset`, `logDeriv_integrand_bound`, `exp_neg_integral_eq_one_of_closed`, `winding_integer_from_exp_one`, `generalizedWindingNumber'`, `intervalIntegrable_of_piecewise_continuousOn_bounded`
- **Used by**: `windingNumber_integer_of_piecewise_closed_avoiding`.
- **Visibility**: private
- **Lines**: 455–477
- **Notes**: >10 lines (~23).

### `lemma windingNumber_integer_of_piecewise_closed_avoiding`
- **Type**: `(γ a b z₀ P) (hab) (hγ_closed) (hγ_cont) (hγ_diff) (hγ_deriv_cont) (hγ_avoids) (hγ_deriv_bound_ex : ∃ M, ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M) : ∃ n : ℤ, generalizedWindingNumber' γ a b z₀ = n`
- **What**: Public form: piecewise-C¹ closed-curve winding numbers are integers, provided some uniform bound on `‖γ'‖` exists.
- **How**: Destructure `hγ_deriv_bound_ex` to get `M`, then `windingNumber_integer_of_piecewise_with_bound`.
- **Hypotheses**: as above.
- **Uses from project**: `windingNumber_integer_of_piecewise_with_bound`, `generalizedWindingNumber'`
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 479–492

### `theorem exp_integral_eq_endpoint_ratio_piecewise`
- **Type**: `(γ a b z₀ P) (hab) (hγ_cont) (hγ_diff) (hγ_deriv_cont) (hγ_avoids) (hγ_deriv_bound : ∃ M, …) : Complex.exp (∫ t in a..b, deriv γ t / (γ t - z₀)) = (γ b - z₀) / (γ a - z₀)`
- **What**: Endpoint-ratio formula in the piecewise-C¹ setting.
- **How**: Get `M`, `δ` and integrability. `gFunc_constant_piecewise` at `t = b` gives `(γ b - z₀) · exp(-F b) = γ a - z₀`, hence `exp(-F b) = (γ a - z₀)/(γ b - z₀)`. Invert (using `Complex.exp_neg`, `inv_inv`, `inv_div`) to flip the sign and get the ratio.
- **Hypotheses**: as above.
- **Uses from project**: `bound_away_from_z₀`, `logDeriv_continuousOn_off_finset`, `logDeriv_integrand_bound`, `gFunc_constant_piecewise`, `intervalIntegrable_of_piecewise_continuousOn_bounded`
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 494–530
- **Notes**: >10 lines (~37).

### `theorem winding_integrand_bounded_of_uniform_avoidance`
- **Type**: `{H a b z₀ δ M} (hδ_pos : 0 < δ) (hδ_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc 0 1, δ ≤ ‖H (t, s) - z₀‖) (hM_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc 0 1, ‖∂t H (t, s)‖ ≤ M) : ∀ t ∈ Icc a b, ∀ s ∈ Icc 0 1, ‖(H (t, s) - z₀)⁻¹ · ∂t H (t, s)‖ ≤ M / δ`
- **What**: Uniform bound for the winding-number integrand along a homotopy with uniform avoidance and uniform derivative bound.
- **How**: `norm_mul_le`, then `‖(H - z₀)⁻¹‖ ≤ δ⁻¹` from `one_div_le_one_div_of_le`, then arithmetic.
- **Hypotheses**: uniform avoidance and uniform derivative bound.
- **Uses from project**: []
- **Used by**: unused in file (public API for downstream homotopy stability).
- **Visibility**: public
- **Lines**: 533–554

### `private lemma gFunc_constant_smooth`
- **Type**: `(hab) (hγ_cont) (hγ_diff) (hγ_avoid) (h_integrand_cont) (h_int) : ∀ t ∈ Icc a b, G t = G a`
- **What**: The `G`-function constancy lemma for the smooth (no-partition) setting.
- **How**: `G` is continuous via product of `(γ - const)` and `exp ∘ -F`. `F` has derivative `γ'/(γ-z₀)` at any `t ∈ Ioo a b` (via `intervalIntegral.integral_hasDerivAt_right` with `h_integrand_cont`). On `[a, b)`, `HasDerivWithinAt G 0 (Ici t)`: at `t = a` use `hasDerivWithinAt_Ici_of_tendsto_deriv` and `tendsto_const_nhds.congr'`; at `t > a` use `HasDerivAt → HasDerivWithinAt`. `constant_of_has_deriv_right_zero` concludes.
- **Hypotheses**: as above.
- **Uses from project**: []
- **Used by**: `exp_integral_eq_endpoint_ratio`.
- **Visibility**: private
- **Lines**: 556–616
- **Notes**: >10 lines (~61); key lemmas `constant_of_has_deriv_right_zero`, `hasDerivWithinAt_Ici_of_tendsto_deriv`, `intervalIntegral.integral_hasDerivAt_right`.

### `private lemma exp_endpoint_ratio_from_gFunc`
- **Type**: `(hab) (hγ_avoid) (hG_const : ∀ t ∈ Icc a b, G t = G a) : Complex.exp (∫ t in a..b, deriv γ t / (γ t - z₀)) = (γ b - z₀) / (γ a - z₀)`
- **What**: Given constancy of `G`, deduce the endpoint-ratio formula.
- **How**: At `t = b`: `(γ b - z₀) · exp(-F b) = γ a - z₀`, so `exp(-F b) = (γ a - z₀)/(γ b - z₀)`. Use `Complex.exp_neg`, `inv_inv`, `inv_div` to flip.
- **Hypotheses**: avoidance, `G`-constancy.
- **Uses from project**: []
- **Used by**: `exp_integral_eq_endpoint_ratio`.
- **Visibility**: private
- **Lines**: 618–638

### `theorem exp_integral_eq_endpoint_ratio`
- **Type**: `(γ a b z₀) (hab) (hγ_cont) (hγ_diff) (hγ_avoid) (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) : Complex.exp (∫ t in a..b, deriv γ t / (γ t - z₀)) = (γ b - z₀) / (γ a - z₀)`
- **What**: Smooth-curve endpoint-ratio formula.
- **How**: `h_integrand_cont` from `hγ'_cont.div (hγ_cont.sub continuousOn_const)`. Get `h_int` from `intervalIntegrable_of_Icc`. Apply `exp_endpoint_ratio_from_gFunc` with `gFunc_constant_smooth`.
- **Hypotheses**: continuity, diff, avoidance, derivative-continuous.
- **Uses from project**: `gFunc_constant_smooth`, `exp_endpoint_ratio_from_gFunc`
- **Used by**: `integral_closed_curve_eq_two_pi_int`.
- **Visibility**: public
- **Lines**: 640–654

### `private theorem integral_closed_curve_eq_two_pi_int`
- **Type**: `(γ a b z₀) (hab) (hγ_closed) (hγ_cont) (hγ_diff) (hγ_avoid) (hγ'_cont) : ∃ n : ℤ, ∫ t in a..b, deriv γ t / (γ t - z₀) = 2 · π · I · n`
- **What**: For a smooth closed curve avoiding `z₀`, the integral lies in `2πi · ℤ`.
- **How**: `exp_integral_eq_endpoint_ratio` plus `hγ_closed` gives `exp(integral) = 1`. `Complex.exp_eq_one_iff` then exhibits `n`. Final `ring`.
- **Hypotheses**: closed curve, smooth, avoidance.
- **Uses from project**: `exp_integral_eq_endpoint_ratio`
- **Used by**: `windingNumber_integer_of_closed_avoiding`.
- **Visibility**: private
- **Lines**: 656–675
- **Notes**: >10 lines (~20).

### `theorem windingNumber_integer_of_closed_avoiding`
- **Type**: `(γ a b z₀) (hab) (hγ_closed) (hγ_cont) (hγ_diff) (hγ'_cont) (hγ_avoid) : ∃ n : ℤ, generalizedWindingNumber' γ a b z₀ = n`
- **What**: Smooth closed-curve winding number is integer-valued (public API).
- **How**: Translate to `τ t := γ t - z₀` (closed, smooth, avoids 0, derivative agrees with `γ'`). Apply `integral_closed_curve_eq_two_pi_int` to `τ` with `z₀ = 0`. Convert generalized winding to ordinary integral via `pv_eq_integral_of_bound_away` (using `bound_away_from_z₀`). Final `field_simp`.
- **Hypotheses**: smooth closed curve avoiding `z₀`.
- **Uses from project**: `integral_closed_curve_eq_two_pi_int`, `bound_away_from_z₀`, `pv_eq_integral_of_bound_away`, `generalizedWindingNumber'`
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 679–720
- **Notes**: >10 lines (~42); key lemma `integral_closed_curve_eq_two_pi_int`.

## File Summary

- **Total declarations**: 26 (2 defs, 24 theorems/lemmas).
- **Key API**: `PiecewiseCurvesHomotopicAvoiding`, `ClosedCurvesHomotopicAvoiding`, `ClosedCurvesHomotopicAvoiding.toPiecewise`, `PiecewiseCurvesHomotopicAvoiding.toBasic`, `windingNumber_integer_of_piecewise_closed_avoiding`, `windingNumber_integer_of_closed_avoiding`, `exp_integral_eq_endpoint_ratio`, `exp_integral_eq_endpoint_ratio_piecewise`, `winding_integrand_bounded_of_uniform_avoidance`, `limUnder_eventually_eq_const`, `exists_ball_avoiding_finset`.
- **Unused in file** (public-API endpoints consumed downstream): `ClosedCurvesHomotopicAvoiding.toPiecewise`, `PiecewiseCurvesHomotopicAvoiding.toBasic`, `windingNumber_integer_of_piecewise_closed_avoiding`, `exp_integral_eq_endpoint_ratio_piecewise`, `winding_integrand_bounded_of_uniform_avoidance`, `windingNumber_integer_of_closed_avoiding`.
- **Sorries**: none.
- **set_options**: none.
- **Long proofs** (>10 lines): `logDeriv_continuousOn_off_finset` (~36), `logDeriv_continuousAt_off_finset` (~32), `logDeriv_stronglyMeasurableAtFilter_off_finset` (~37), `gFunc_deriv_zero_off_finset` (~25), `gFunc_constant_piecewise` (~31), `exp_neg_integral_eq_one_of_closed` (~23), `windingNumber_integer_of_piecewise_with_bound` (~23), `exp_integral_eq_endpoint_ratio_piecewise` (~37), `gFunc_constant_smooth` (~61), `integral_closed_curve_eq_two_pi_int` (~20), `windingNumber_integer_of_closed_avoiding` (~42).
- **One-paragraph purpose**: This file develops the "exp trick" proof that winding numbers of closed curves avoiding a point are integers, in both a smooth and a piecewise-C¹ setting. It defines two homotopy notions (`PiecewiseCurvesHomotopicAvoiding`, `ClosedCurvesHomotopicAvoiding`) and provides conversions between them. The core technical tool is a `G(t) = (γ - z₀) · exp(-F(t))` function which is locally constant off the partition (`gFunc_constant_piecewise`/`gFunc_constant_smooth`); from this one derives the endpoint-ratio identity `exp(∫ γ'/(γ-z₀)) = (γ b - z₀)/(γ a - z₀)` and, in the closed case, integrality of the generalized winding number via `Complex.exp_eq_one_iff`. The public API serves as the integrality black box for the residue-theorem chain.
