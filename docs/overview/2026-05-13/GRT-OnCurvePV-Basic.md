# GRT/OnCurvePV/Basic.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/OnCurvePV/Basic.lean`
Imports: `PVInfrastructure.UniformStepBound`, `GeneralizedResidueTheory.Residue`

File-level: `attribute [local instance] Classical.propDecidable` (line 20).

### `lemma pv_limit_via_dyadic`
- **Type**: `{γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ} (hat₀ : t₀ ∈ Ioo a b) (hL : L ≠ 0) (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L) (hγ_cont_deriv : ContinuousOn (deriv γ) (Icc a b)) (hγ_meas : Measurable γ) (hγ_cont : ContinuousOn γ (Icc a b)) (h_inj : ∀ t ∈ Icc a b, γ t = γ t₀ → t = t₀) → ∃ limit, Tendsto (fun ε => ∫ t in a..b, if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0) (𝓝[>] 0) (𝓝 limit)`
- **What**: Cauchy principal value existence (one-sided limit as `ε → 0⁺`) for the curve PV integrand at an interior on-curve crossing `t₀`, via a dyadic-Cauchy argument.
- **How**: (1) Invoke `pv_step_bound_ratio_two_uniform` to obtain a uniform constant `K > 0` and threshold `δ_P1 > 0` so that for any `ε₁, ε₂` within ratio 2 below `δ_P1`, the PV-integral difference is bounded by `K · ε₁`. Set `δ := δ_P1 / 2`. (2) Define dyadic sequence `I(δ/2^n)` and prove `‖I(δ/2^(n+1)) - I(δ/2^n)‖ ≤ K · δ/2^n` using `h_step_uniform`. (3) Conclude Cauchy via `cauchySeq_pv_dyadic`; extract limit `limit_dyadic` from `CompleteSpace.complete`. (4) For arbitrary `ε > 0` small, dyadic-bracket via `exists_dyadic_bracket` to get `M` with `δ/2^(M+1) ≤ ε < δ/2^M`; show `M ≥ N` (else `δ/2^(M+1) ≥ δ/2^N` contradicts `ε < δ/2^N`). Use single-step bound for `‖I ε - I(δ/2^M)‖ ≤ K·δ/2^M` and `telescoping_sum_bound` for `‖I(δ/2^M) - I(δ/2^N)‖ ≤ 2Kδ/2^N - 2Kδ/2^M`. (5) Combine via triangle inequality; pick `N₂` so `K·δ/2^N₂ < η/4`, set `N := max N₁ N₂`, and verify `dist(I ε, limit_dyadic) < η`.
- **Hypotheses**: `t₀ ∈ Ioo a b`; `L ≠ 0`; `C²` regularity at `t₀`; derivative continuous on `[a,b]`; `γ` measurable + continuous on `[a,b]`; injectivity into `t₀` only.
- **Uses from project**: `pv_step_bound_ratio_two_uniform`, `cauchySeq_pv_dyadic`, `exists_dyadic_bracket`, `telescoping_sum_bound`
- **Used by**: unused in file (downstream theorem in PV infrastructure)
- **Visibility**: public
- **Lines**: 24-169
- **Notes**: >30 lines (>140-line proof); no `sorry`

### `lemma measurableSet_norm_gt_of_continuousOn`
- **Type**: `{f : ℝ → ℂ} {s : Set ℝ} (ε : ℝ) (hf : ContinuousOn f s) (hs : MeasurableSet s) → MeasurableSet ({t | ε < ‖f t‖} ∩ s)`
- **What**: `{t | ε < ‖f t‖} ∩ s` is measurable when `f` is continuous on a measurable set `s`.
- **How**: `ContinuousOn.norm` gives `ContinuousOn (‖f·‖) s`; preimage `(s.restrict ‖f·‖)⁻¹' Ioi ε` is open as `Ioi` is open; via `isOpen_induced_iff` get `U` open with `Subtype.val⁻¹' U = preimage`; show `{t | ε < ‖f t‖} ∩ s = U ∩ s` by mutual containment; conclude `MeasurableSet (U ∩ s)`.
- **Hypotheses**: `ContinuousOn f s`; `s` measurable.
- **Uses from project**: []
- **Used by**: `measurableSet_norm_gt_Icc`
- **Visibility**: public
- **Lines**: 171-196
- **Notes**: none

### `lemma measurableSet_norm_gt_Icc`
- **Type**: `{f : ℝ → ℂ} {a b : ℝ} (ε : ℝ) (hf : ContinuousOn f (Icc a b)) → MeasurableSet ({t | ε < ‖f t‖} ∩ Icc a b)`
- **What**: Specialization of `measurableSet_norm_gt_of_continuousOn` to `Icc a b`.
- **How**: Apply `measurableSet_norm_gt_of_continuousOn` with `isClosed_Icc.measurableSet`.
- **Hypotheses**: `ContinuousOn f (Icc a b)`.
- **Uses from project**: `measurableSet_norm_gt_of_continuousOn`
- **Used by**: `aEStronglyMeasurable_pv_integrand_piecewiseC1`
- **Visibility**: public
- **Lines**: 198-201
- **Notes**: none

### `theorem aEStronglyMeasurable_pv_integrand_piecewiseC1`
- **Type**: `{f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {ε : ℝ} {P : Finset ℝ} (hf : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε)) (hγ : ContinuousOn γ (Icc a b)) (hγ'_off_P : ContinuousOn (deriv γ) ((Icc a b) \ P)) → AEStronglyMeasurable (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0) (volume.restrict (Icc a b))`
- **What**: The PV cutout integrand is a.e. strongly measurable on `Icc a b` for piecewise C¹ curves with `P` excluding finitely many non-smooth points.
- **How**: Set `S := {t | ε < ‖γ t - z₀‖}`. `S ∩ Icc a b` is measurable via `measurableSet_norm_gt_Icc`. On `(S ∩ Icc a b) \ P`, `f ∘ γ` is continuous (compose `hf` on image excluding the open ball with `hγ.mono`; check `MapsTo`); multiply by `hγ'_off_P` for continuity of `f(γ t) · γ'(t)`. Decompose `volume.restrict (S ∩ Icc a b) = volume.restrict ((S ∩ Icc a b) \ P) + volume.restrict (P ∩ (S ∩ Icc a b))` (disjoint union); first part gets `AEStronglyMeasurable` from the continuous function; second part has measure zero (since `P` is finite). Then piecewise via `AEStronglyMeasurable.piecewise` with constant `0`; finally use `filter_upwards` over `ae_restrict_mem isClosed_Icc.measurableSet` to identify the `if-then-else` form with the piecewise form.
- **Hypotheses**: `f` continuous on the cutout image, `γ` continuous on `[a,b]`, `γ'` continuous on `[a,b] \ P`.
- **Uses from project**: `measurableSet_norm_gt_Icc`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 203-271
- **Notes**: >30 lines (~68-line proof)

### `lemma indicator_integrand_deriv_eq`
- **Type**: `(γ : ℝ → ℂ) (c : ℂ) (ε : ℝ) (t : ℝ) → (if ‖γ t - c‖ > ε then (γ t - c)⁻¹ * deriv (fun s => γ s - c) t else 0) = (if ‖γ t - c‖ > ε then (γ t - c)⁻¹ * deriv γ t else 0)`
- **What**: Replacing `deriv (γ - c)` by `deriv γ` inside the PV indicator integrand has no effect.
- **How**: `split_ifs`; in the true branch use `deriv_sub_const` to rewrite the derivative.
- **Hypotheses**: None beyond inputs.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 274-280
- **Notes**: none

### `lemma cpv_exists_from_shifted_tendsto`
- **Type**: `(γ : ℝ → ℂ) (a b : ℝ) (c : ℂ) (L : ℂ) (h : Tendsto (fun ε => ∫ t in a..b, if ‖γ t - c‖ > ε then (γ t - c)⁻¹ * deriv (fun s => γ s - c) t else 0) (𝓝[>] 0) (𝓝 L)) → CauchyPrincipalValueExists' (fun z => (z - c)⁻¹) γ a b c`
- **What**: Convergence of the shifted-derivative PV integral implies `CauchyPrincipalValueExists'` for the integrand `(z - c)⁻¹`.
- **How**: Witness `L`; congruence-rewrite via `h.congr` using `intervalIntegral.integral_congr` and `deriv_sub_const`.
- **Hypotheses**: `Tendsto` of the shifted PV integral.
- **Uses from project**: `CauchyPrincipalValueExists'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 282-287
- **Notes**: none

### `lemma arc_angle_injective`
- **Type**: `{t t' : ℝ} (ht : t ∈ Ioo 1 3) (ht' : t' ∈ Ioo 1 3) (h_eq : Complex.exp (↑(π · (1 + t)/6) · I) = Complex.exp (↑(π · (1 + t')/6) · I)) → t = t'`
- **What**: Injectivity of the angular parameterization `t ↦ exp(π(1+t)/6 · i)` on `(1,3)`.
- **How**: From `Complex.exp_eq_exp_iff_exists_int` get `n : ℤ` with `π(1+t)/6 · I - π(1+t')/6 · I = 2π n · I`; cancel `I` via `mul_right_cancel₀ I_ne_zero`; bound `|π(1+t)/6 - π(1+t')/6| < π` by `nlinarith` using `t, t' ∈ (1,3)`; if `n ≠ 0` then `|2π n| ≥ 2π > π`, contradiction; so `n = 0` and `π(1+t)/6 = π(1+t')/6`, then `nlinarith` with `Real.pi_ne_zero, Real.pi_pos`.
- **Hypotheses**: `t, t' ∈ (1,3)`; equal angular images.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 289-321
- **Notes**: >30 lines

### `lemma cpv_avoidance`
- **Type**: `(f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (h_cont : ContinuousOn γ (Icc a b)) (hab : a ≤ b) (h_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀) → CauchyPrincipalValueExists' f γ a b z₀`
- **What**: CPV trivially exists when `γ` avoids `z₀` on `[a, b]` — the limit is just the ordinary integral.
- **How**: Continuity gives `t ↦ ‖γ t - z₀‖` continuous; compact `Icc a b` admits a minimum `t₀` (via `isCompact_Icc.exists_isMinOn`); avoidance gives `‖γ t₀ - z₀‖ > 0`. Set `C := ∫ f(γ t) · γ'(t)` and witness with `C`. For all `ε ∈ (0, ‖γ t₀ - z₀‖)`, `ε < ‖γ t - z₀‖` everywhere on `[a,b]`, so the indicator integrand equals the unconstrained integrand; conclude via `Tendsto.congr'` against `tendsto_const_nhds` and `Ioo_mem_nhdsGT`.
- **Hypotheses**: `γ` continuous on `[a,b]`; `a ≤ b`; `γ` avoids `z₀`.
- **Uses from project**: `CauchyPrincipalValueExists'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 323-342
- **Notes**: none

### `lemma cpv_concat`
- **Type**: `(f : ℂ → ℂ) (γ : ℝ → ℂ) (a b c : ℝ) (z₀ : ℂ) (h_ab : CauchyPrincipalValueExists' f γ a b z₀) (h_bc : CauchyPrincipalValueExists' f γ b c z₀) (hab : a ≤ b) (hbc : b ≤ c) (h_int : ∀ ε > 0, IntervalIntegrable ... volume a c) → CauchyPrincipalValueExists' f γ a c z₀`
- **What**: Concatenation: if CPV exists on `[a,b]` and `[b,c]` (with `a ≤ b ≤ c`) and the cutout integrand is integrable on `[a,c]` for every `ε > 0`, then CPV exists on `[a,c]` with limit `L₁ + L₂`.
- **How**: Extract `L₁, L₂` from the two CPVs; witness `L₁ + L₂` and use `Tendsto.add` then `Tendsto.congr'`; via `self_mem_nhdsWithin`, for each `ε > 0` use `intervalIntegral.integral_add_adjacent_intervals` with integrability restrictions `hII.mono_set` on the two subintervals.
- **Hypotheses**: CPV existence on each piece; `a ≤ b ≤ c`; cutout-integrand integrability on `[a,c]` for every `ε > 0`.
- **Uses from project**: `CauchyPrincipalValueExists'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 344-367
- **Notes**: none

## File Summary
- Total declarations: 9 (3 public `lemma`s, 3 public `theorem`s with `lemma` style, 3 supporting public `lemma`s — `pv_limit_via_dyadic`, `measurableSet_norm_gt_of_continuousOn`, `measurableSet_norm_gt_Icc`, `aEStronglyMeasurable_pv_integrand_piecewiseC1`, `indicator_integrand_deriv_eq`, `cpv_exists_from_shifted_tendsto`, `arc_angle_injective`, `cpv_avoidance`, `cpv_concat`).
- Theme: General Cauchy-principal-value (CPV) infrastructure for piecewise C¹ curves: a dyadic-Cauchy proof of CPV existence at on-curve crossings (`pv_limit_via_dyadic`); a.e. strong measurability of the cutout integrand; arc-angle injectivity for the FD boundary arcs; CPV existence under avoidance (`cpv_avoidance`); CPV concatenation across adjacent intervals (`cpv_concat`).
- Key dependencies: `PVInfrastructure.UniformStepBound` (provides `pv_step_bound_ratio_two_uniform`, `cauchySeq_pv_dyadic`, `exists_dyadic_bracket`, `telescoping_sum_bound`); `Residue` (provides `CauchyPrincipalValueExists'`).
- 3 declarations exceed 30 lines: `pv_limit_via_dyadic` (~146 lines), `aEStronglyMeasurable_pv_integrand_piecewiseC1` (~69 lines), `arc_angle_injective` (~33 lines).
- File-level `attribute [local instance] Classical.propDecidable`.
- No `sorry`, no `axiom`, no `native_decide`, no other `set_option` directives.
