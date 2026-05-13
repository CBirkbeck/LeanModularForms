# Inventory: GeneralizedResidueTheory/Homotopy/Invariance.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/Homotopy/Invariance.lean`
Namespace: none (declarations live at root, but file is `noncomputable section`-wrapped)
Imports: `GeneralizedResidueTheory.Homotopy.Integrality`, `GeneralizedResidueTheory.Homotopy.ParametricDiff`

### `private theorem homotopy_uniform_avoidance`
- **Type**: `(H : ℝ × ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b) (hH_cont : Continuous H) (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc 0 1, H (t, s) ≠ z₀) : ∃ δ > 0, ∀ t ∈ Icc a b, ∀ s ∈ Icc 0 1, δ ≤ ‖H (t, s) - z₀‖`
- **What**: Uniform (in `s ∈ [0,1]`) lower bound on `‖H − z₀‖` for a homotopy avoiding `z₀`.
- **How**: The image of the compact box `[a,b] × [0,1]` under `H` is compact and closed, doesn't contain `z₀`, so `infDist z₀ (image)` is positive by `IsClosed.notMem_iff_infDist_pos`. The δ chosen is that infimum distance.
- **Hypotheses**: `a < b`, `H` continuous, avoids `z₀` on the box.
- **Uses from project**: []
- **Used by**: `windingNumber_continuousOn_param_piecewise_with_bound`, `windingNumber_continuous_in_param`
- **Visibility**: private
- **Lines**: 32-46

### `private lemma homotopy_integrand_continuousOn_t`
- **Type**: `{H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ} (hH_cont) (hH_avoid) (hH_deriv_cont : ∀ p₁ p₂, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b → ContinuousOn (fun p => deriv (fun t' => H (t', p.2)) p.1) (Ioo p₁ p₂ ×ˢ Icc 0 1)) {s : ℝ} (hs : s ∈ Icc 0 1) : ContinuousOn (fun t => (H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t) ((Icc a b) \ (P ∪ {a, b}))`
- **What**: The winding integrand `t ↦ (H(t,s) − z₀)⁻¹ · ∂_t H(t,s)` is continuous on `[a,b]` away from the piecewise breakpoints `P ∪ {a,b}`.
- **How**: For each `t ∈ Icc a b \ P'`, choose `ε'` so that the punctured neighborhood `Ioo (t-ε') (t+ε')` avoids `P` and stays in `Ioo a b`; uses `exists_ball_avoiding_finset` (from project). Continuity is then the product of (a) inverse of `H(·,s) − z₀` (nonzero by avoidance) and (b) `deriv` factor from `hH_deriv_cont`, both pulled back through `(t ↦ (t, s))`.
- **Hypotheses**: `H` continuous, avoids `z₀`, partial-`t` derivative continuous on piece-strips; `s ∈ Icc 0 1`.
- **Uses from project**: `exists_ball_avoiding_finset`
- **Used by**: `homotopy_piecewise_aestronglyMeasurable`
- **Visibility**: private
- **Lines**: 48-88
- **Notes**: 41-line proof; key lemma `exists_ball_avoiding_finset`.

### `private lemma homotopy_integrand_continuousWithinAt_s`
- **Type**: As in previous lemma, but for continuity in `s` at a fixed `t ∈ Ioo a b, t ∉ P`: `ContinuousWithinAt (fun s => f t s) (Icc 0 1) s₀`.
- **What**: Continuity of the integrand in the homotopy parameter `s` at a fixed interior `t`.
- **How**: Same `ε'`-shrinking pattern using `exists_ball_avoiding_finset`; then `ContinuousWithinAt.mul` of the `(H − z₀)⁻¹` factor (continuous in `s` by `inv₀`) with the `deriv` factor (continuous via `hH_deriv_cont` pulled back through `(s ↦ (t, s))`).
- **Hypotheses**: As above plus `t ∈ Icc a b`, `t ∈ Ioo a b`, `t ∉ P`.
- **Uses from project**: `exists_ball_avoiding_finset`
- **Used by**: `windingNumber_continuousOn_param_piecewise_with_bound`
- **Visibility**: private
- **Lines**: 90-124
- **Notes**: 35-line proof; key lemma `exists_ball_avoiding_finset`.

### `private lemma homotopy_pv_eq_integral`
- **Type**: `{H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {δ : ℝ} (hab) (hδ_pos) (hδ_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc 0 1, δ ≤ ‖H (t, s) - z₀‖) (s) (hs) : generalizedWindingNumber' (fun t => H (t, s)) a b z₀ = (2πI)⁻¹ * ∫ t in a..b, (H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t`
- **What**: Under a uniform avoidance bound δ, the PV winding number reduces to the ordinary winding integral.
- **How**: Unfolds `generalizedWindingNumber'`/`cauchyPrincipalValue'`, applies `limUnder_eventually_eq_const` to drop the limit (the cutoff predicate `ε < ‖H − z₀‖` holds for ε in `Ioo 0 δ`), then `intervalIntegral.integral_congr_ae` removes the indicator using `reduceIte`.
- **Hypotheses**: `a < b`, `δ > 0`, uniform bound, `s ∈ Icc 0 1`.
- **Uses from project**: `generalizedWindingNumber'`, `cauchyPrincipalValue'`, `limUnder_eventually_eq_const`
- **Used by**: `windingNumber_continuousOn_param_piecewise_with_bound`
- **Visibility**: private
- **Lines**: 126-145

### `private lemma homotopy_piecewise_aestronglyMeasurable`
- **Type**: Under continuity, avoidance, and piece-strip deriv continuity assumptions on `H, P`: `AEStronglyMeasurable (fun t => (H (t, s) - z₀)⁻¹ * deriv (·) t) (volume.restrict (Icc a b))`.
- **What**: AE-strongly-measurable on the restricted interval.
- **How**: Decomposes `Icc a b` as `(Icc a b \ P') ∪ (P' ∩ Icc a b)`. On the cofinite-measure piece, continuity from `homotopy_integrand_continuousOn_t` gives `aestronglyMeasurable`; the finite set has volume 0, so the restricted measure is zero and `aestronglyMeasurable_zero_measure` applies.
- **Hypotheses**: Same as the continuity lemma plus `s ∈ Icc 0 1`.
- **Uses from project**: `homotopy_integrand_continuousOn_t`
- **Used by**: `windingNumber_continuousOn_param_piecewise_with_bound`
- **Visibility**: private
- **Lines**: 147-171

### `private theorem windingNumber_continuousOn_param_piecewise_with_bound`
- **Type**: Under continuity/avoidance/piece-strip-deriv-continuity/uniform `M`-bound on `‖∂_t H‖`: `ContinuousOn (fun s => generalizedWindingNumber' (fun t => H (t, s)) a b z₀) (Icc 0 1)`.
- **What**: Generalized winding number is continuous in the homotopy parameter (piecewise version with uniform deriv bound).
- **How**: Extracts uniform avoidance δ from `homotopy_uniform_avoidance`. Combines `winding_integrand_bounded_of_uniform_avoidance` (from project) with `homotopy_pv_eq_integral` to express the winding number as a constant times the parametric integral. Continuity then follows from `continuousWithinAt_integral_of_dominated_piecewise` (from project) with bound `M/δ`, using `homotopy_piecewise_aestronglyMeasurable` for measurability and `homotopy_integrand_continuousWithinAt_s` for the `s`-continuity off a null set `B = {a,b} ∪ P`.
- **Hypotheses**: `a < b`; `H` continuous, avoids `z₀`; piece-strip deriv continuity; uniform `M`-bound on `‖∂_t H‖`.
- **Uses from project**: `homotopy_uniform_avoidance`, `homotopy_pv_eq_integral`, `homotopy_piecewise_aestronglyMeasurable`, `homotopy_integrand_continuousWithinAt_s`, `winding_integrand_bounded_of_uniform_avoidance`, `continuousWithinAt_integral_of_dominated_piecewise`, `generalizedWindingNumber'`
- **Used by**: `windingNumber_eq_of_piecewise_homotopic`
- **Visibility**: private
- **Lines**: 173-216
- **Notes**: 44-line proof; key composites `winding_integrand_bounded_of_uniform_avoidance`, `continuousWithinAt_integral_of_dominated_piecewise`.

### `private theorem continuous_integer_valued_constant`
- **Type**: `(f : ℝ → ℂ) (hf_cont : ContinuousOn f (Icc 0 1)) (hf_int : ∀ s ∈ Icc 0 1, ∃ n : ℤ, f s = n) : f 0 = f 1`
- **What**: A continuous integer-valued function on `[0,1]` is constant (so `f 0 = f 1`).
- **How**: Define `g : Icc 0 1 → ℂ`, prove `IsLocallyConstant g` via `iff_isOpen_fiber`. For each value `y`: if `y = n` is an integer, the fiber `g⁻¹{n}` equals `g⁻¹(ball n 1)` (since two distinct integer complex values differ by at least 1, using `Int.abs_lt_one_iff`), open by continuity; if `y` not an integer, the fiber is empty (open). Then `IsLocallyConstant.apply_eq_of_isPreconnected` on connected `Icc` closes.
- **Hypotheses**: `f` continuous on `[0,1]` and integer-valued.
- **Uses from project**: []
- **Used by**: `windingNumber_eq_of_piecewise_homotopic`, `windingNumber_eq_of_homotopic_closed`
- **Visibility**: private
- **Lines**: 218-258
- **Notes**: 41-line proof; key lemmas `IsLocallyConstant.iff_isOpen_fiber`, `Int.abs_lt_one_iff`, `IsLocallyConstant.apply_eq_of_isPreconnected`.

### `private theorem generalizedWindingNumber'_eq_of_eq_on`
- **Type**: `(f g : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b) (heq_val : ∀ t ∈ Icc a b, f t = g t) (heq_deriv : ∀ᵐ t ∂volume.restrict (uIoc a b), deriv f t = deriv g t) : generalizedWindingNumber' f a b z₀ = generalizedWindingNumber' g a b z₀`
- **What**: If `f = g` on `[a,b]` and `deriv f = deriv g` a.e. on `(a,b]`, their PV winding numbers agree.
- **How**: Unfolds both PVs and shows the integrand functions are equal as functions of ε via `intervalIntegral.integral_congr_ae`; converts `uIoc` to `Ioc`, then uses `ae_restrict_iff'` and `filter_upwards` with `heq_deriv` plus pointwise `heq_val`.
- **Hypotheses**: `a < b`; equality on `Icc` and a.e. equality of derivative on `uIoc`.
- **Uses from project**: `generalizedWindingNumber'`, `cauchyPrincipalValue'`
- **Used by**: `windingNumber_eq_of_piecewise_homotopic`, `windingNumber_eq_of_homotopic_closed`
- **Visibility**: private
- **Lines**: 260-288

### `theorem windingNumber_eq_of_piecewise_homotopic`
- **Type**: `(γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ) (hab : a < b) (hhom : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ a b z₀ P) : generalizedWindingNumber' γ₀ a b z₀ = generalizedWindingNumber' γ₁ a b z₀`
- **What**: Winding number invariance under piecewise C¹ homotopy avoiding `z₀`.
- **How**: Destructs `hhom` to get `H, hH_cont, hH0, hH1, hH_closed, hH_avoid, hH_diff, hH_deriv_cont, M, hM_bound`. Defines `n s := gWN' (·, s)`; uses `windingNumber_continuousOn_param_piecewise_with_bound` to make it continuous, and `windingNumber_integer_of_piecewise_closed_avoiding` (from project) to make it integer-valued for every `s`. Concludes `n 0 = n 1` via `continuous_integer_valued_constant`, then rewrites `n 0 = gWN' γ₀ ...` and `n 1 = gWN' γ₁ ...` via `generalizedWindingNumber'_eq_of_eq_on` (using the endpoint conditions on Icc and Ioo-Ioc a.e. equivalence for derivatives).
- **Hypotheses**: `a < b`; piecewise-curves-homotopic-avoiding witness.
- **Uses from project**: `PiecewiseCurvesHomotopicAvoiding`, `windingNumber_continuousOn_param_piecewise_with_bound`, `continuous_integer_valued_constant`, `windingNumber_integer_of_piecewise_closed_avoiding`, `generalizedWindingNumber'_eq_of_eq_on`, `generalizedWindingNumber'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 291-333
- **Notes**: 43-line proof; key composites `windingNumber_integer_of_piecewise_closed_avoiding`, `continuous_integer_valued_constant`.

### `private lemma smooth_winding_pv_eq_integral`
- **Type**: As `homotopy_pv_eq_integral`, restated for the smooth variant `γ : ℝ × ℝ → ℂ` (same statement modulo renaming `H` → `γ`).
- **What**: PV winding number reduces to the ordinary winding integral under uniform avoidance, smooth case.
- **How**: Identical to `homotopy_pv_eq_integral` (unfold PV, `limUnder_eventually_eq_const`, `integral_congr_ae`, `reduceIte`).
- **Hypotheses**: `a < b`, uniform δ bound, `s ∈ Icc 0 1`.
- **Uses from project**: `generalizedWindingNumber'`, `cauchyPrincipalValue'`, `limUnder_eventually_eq_const`
- **Used by**: `windingNumber_continuous_in_param`
- **Visibility**: private
- **Lines**: 335-354

### `private lemma smooth_winding_integral_continuousOn`
- **Type**: `(hab : a < b) (hγ_cont : Continuous γ) (hγ_avoid) (hγ_deriv_cont : Continuous (fun p => deriv (fun t' => γ (t', p.2)) p.1)) (hM : uniform bound) : ContinuousOn (fun s => ∫ t in a..b, (γ (t, s) − z₀)⁻¹ * deriv (·, s) t) (Icc 0 1)`
- **What**: Parametric integral is continuous in `s`, smooth-homotopy version.
- **How**: For each `s₁`, applies `intervalIntegral.continuousWithinAt_of_dominated_interval`: bounded by `M`, integrand is `ContinuousOn` in `t` (product of `(γ − z₀)⁻¹` and `deriv`), dominated by `M`, and continuous in `s` at each `t` via product continuity (`ContinuousAt.mul` of `inv₀` and `hγ_deriv_cont` composed with `prodMk`).
- **Hypotheses**: `a < b`; γ continuous on `ℝ × ℝ`; avoidance; continuous partial deriv; uniform bound `M`.
- **Uses from project**: []
- **Used by**: `windingNumber_continuous_in_param`
- **Visibility**: private
- **Lines**: 356-395
- **Notes**: 40-line proof; key lemma `intervalIntegral.continuousWithinAt_of_dominated_interval`.

### `private theorem windingNumber_continuous_in_param`
- **Type**: `(γ : ℝ × ℝ → ℂ) (a b z₀) (hab : a < b) (hγ_cont) (hγ_avoid) (hγ_deriv_cont) : ContinuousOn (fun s => gWN' (γ(·, s)) a b z₀) (Icc 0 1)`
- **What**: Generalized winding number continuous in the smooth-homotopy parameter.
- **How**: Same outline as the piecewise version: get δ from `homotopy_uniform_avoidance`, build the bounded integrand on the compact box, extract uniform `M` via `IsCompact.exists_bound_of_continuousOn`, then `homotopy_pv_eq_integral` collapses the PV to a constant-times-integral and `smooth_winding_integral_continuousOn` finishes.
- **Hypotheses**: γ continuous, avoidance, continuous partial-`t` deriv.
- **Uses from project**: `homotopy_uniform_avoidance`, `smooth_winding_pv_eq_integral`, `smooth_winding_integral_continuousOn`, `generalizedWindingNumber'`
- **Used by**: `windingNumber_eq_of_homotopic_closed`
- **Visibility**: private
- **Lines**: 397-421
- **Notes**: 25-line proof; key composites `IsCompact.exists_bound_of_continuousOn`, `smooth_winding_pv_eq_integral`.

### `theorem windingNumber_eq_of_homotopic_closed`
- **Type**: `(γ₀ γ₁ : ℝ → ℂ) (a b z₀) (hab) (hhom : ClosedCurvesHomotopicAvoiding γ₀ γ₁ a b z₀) : gWN' γ₀ a b z₀ = gWN' γ₁ a b z₀`
- **What**: Winding number invariance under smooth homotopy through closed avoiding curves.
- **How**: Same template as the piecewise version: destruct the homotopy, define `n s := gWN' (·, s)`; integer-valued via `windingNumber_integer_of_closed_avoiding`; continuous via `windingNumber_continuous_in_param`; conclude `n 0 = n 1` via `continuous_integer_valued_constant`, transport to γ₀/γ₁ via `generalizedWindingNumber'_eq_of_eq_on`.
- **Hypotheses**: `a < b`; smooth homotopy avoiding `z₀` witness.
- **Uses from project**: `ClosedCurvesHomotopicAvoiding`, `windingNumber_continuous_in_param`, `continuous_integer_valued_constant`, `windingNumber_integer_of_closed_avoiding`, `generalizedWindingNumber'_eq_of_eq_on`, `generalizedWindingNumber'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 424-457
- **Notes**: 34-line proof; key composites `windingNumber_integer_of_closed_avoiding`, `continuous_integer_valued_constant`.

### `theorem generalizedWindingNumber_eq_classical_away`
- **Type**: `(γ : PiecewiseC1Curve) (z₀ : ℂ) (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) : gWN' γ.toFun γ.a γ.b z₀ = (2πI)⁻¹ * ∫ t in γ.a..γ.b, (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t`
- **What**: When γ avoids `z₀`, the PV winding number equals the classical contour integral.
- **How**: Image of `Icc γ.a γ.b` under continuous γ.toFun is compact (and closed), doesn't contain `z₀`, so `Metric.infDist z₀ ...` is positive. Pick any ε in `(0, δ)`: then `ε < ‖γ.toFun t − z₀‖` for all `t ∈ Icc γ.a γ.b`. Apply `limUnder_eventually_eq_const` on the resulting eventual constancy, then `integral_congr_ae` to drop the `if`-predicate.
- **Hypotheses**: γ a piecewise C¹ curve, avoids `z₀` on `[γ.a, γ.b]`.
- **Uses from project**: `PiecewiseC1Curve`, `generalizedWindingNumber'`, `cauchyPrincipalValue'`, `limUnder_eventually_eq_const`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 460-489
- **Notes**: 30-line proof; key lemma `IsClosed.notMem_iff_infDist_pos`.

### `private lemma integral_congr_homotopy_endpoint`
- **Type**: `{f : ℂ → ℂ} {γ : ℝ → ℂ} {H : ℝ × ℝ → ℂ} {a b s : ℝ} (hab : a < b) (hHs : ∀ t ∈ Icc a b, H (t, s) = γ t) : ∫ t in a..b, f (γ t) * deriv γ t = ∫ t in a..b, f (H (t, s)) * deriv (fun t => H (t, s)) t`
- **What**: If `H(·, s) = γ` on `Icc`, then `∫ f(γ) γ' = ∫ f(H(·,s)) ∂_t H(·,s)`.
- **How**: `intervalIntegral.integral_congr_ae` using `Ioo_ae_eq_Ioc.mem_iff` and `EqOn.deriv` (open-set derivative equality from the function equality on the open subset `Ioo a b`).
- **Hypotheses**: `a < b`; pointwise equality on `[a,b]`.
- **Uses from project**: []
- **Used by**: `contourIntegral_eq_of_homotopic`
- **Visibility**: private
- **Lines**: 491-503

### `theorem contourIntegral_eq_of_homotopic`
- **Type**: `(f : ℂ → ℂ) (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (hab) (_continuity/diff hypotheses) (H : ℝ × ℝ → ℂ) (_hH_cont) (hH0, hH1) (_hH_ends) (hf_holo) (hfH_cont) (hH_smooth : ContDiff ℝ 2 H) (hH_deriv_s_zero_at_ends) (hf_differentiable) : ∫ t in a..b, f (γ₀ t) * deriv γ₀ t = ∫ t in a..b, f (γ₁ t) * deriv γ₁ t`
- **What**: Contour integrals of a holomorphic function are equal along homotopic curves (fixed endpoints).
- **How**: Reduces both contour integrals to the parametric form via `integral_congr_homotopy_endpoint` (using `hH0`/`hH1`); defines `I s := ∫ t in a..b, f (H(t,s)) ∂_t H(t,s)`. Continuity of `I` via `intervalIntegral_continuous_on_param` using `(contDiff_partialDeriv_fst_of_contDiff_two H hH_smooth).continuous` for `∂_t H` and `hfH_cont` for the `f ∘ H` factor. Right derivative of `I` is zero on `Ico 0 1` by `hasDerivAt_homotopy_integral_zero` (from project) plus the boundary `s'`-derivative-zero condition. `constant_of_has_deriv_right_zero` (from project) gives `I 0 = I 1`.
- **Hypotheses**: γ₀/γ₁ continuous and differentiable; `H` a `C^2` homotopy interpolating γ₀ and γ₁; `f` holomorphic; `H`'s `s`-derivative vanishes at endpoints `t = a, b`; etc.
- **Uses from project**: `integral_congr_homotopy_endpoint`, `contDiff_partialDeriv_fst_of_contDiff_two`, `intervalIntegral_continuous_on_param`, `hasDerivAt_homotopy_integral_zero`, `constant_of_has_deriv_right_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 507-558
- **Notes**: 52-line proof. Key composites: `contDiff_partialDeriv_fst_of_contDiff_two`, `hasDerivAt_homotopy_integral_zero`, `constant_of_has_deriv_right_zero`, `intervalIntegral_continuous_on_param`.

## File Summary
16 declarations: 11 private (helpers), 4 public theorems, 1 private lemma. The file proves homotopy invariance of generalized winding numbers in two settings — piecewise C¹ (`windingNumber_eq_of_piecewise_homotopic`) and smooth (`windingNumber_eq_of_homotopic_closed`) — plus two adjacent results: `generalizedWindingNumber_eq_classical_away` (PV equals classical integral when γ avoids `z₀`) and `contourIntegral_eq_of_homotopic` (holomorphic-integrand contour integral invariance). Common architectural pattern across both invariance theorems: (1) `homotopy_uniform_avoidance` gives uniform δ-bound on `‖H − z₀‖`; (2) `*_pv_eq_integral` lemmas collapse PV to ordinary integral; (3) `windingNumber_continuous*_in_param` proves continuity in `s`; (4) `windingNumber_integer_of_*_closed_avoiding` (from project) gives integer values; (5) `continuous_integer_valued_constant` finishes via local-constancy; (6) `generalizedWindingNumber'_eq_of_eq_on` transports to original curves. No `sorry`, no axioms, no `set_option`. Six proofs exceed 30 lines. Imports `Homotopy.Integrality` and `Homotopy.ParametricDiff` from the project.
