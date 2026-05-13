# CauchyPrimitive.md

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/CauchyPrimitive.lean` (422 lines)

Namespace: (none — top-level, in `noncomputable section`)

### `instance instNormSMulClassRealComplex`
- **Type**: `NormSMulClass ℝ ℂ`
- **What**: Local instance making `‖t • z‖ = ‖t‖ * ‖z‖` for `t : ℝ` and `z : ℂ` available (re-introduces an instance no longer auto-synthesized in mathlib v4.29).
- **How**: One-liner `NormedSpace.toNormSMulClass`.
- **Hypotheses**: none.
- **Uses from project**: none.
- **Used by**: all subsequent lemmas using `t • z` arithmetic on ℂ (indirectly via instance resolution).
- **Visibility**: private
- **Lines**: 30-31
- **Notes**: none

### `instance instIsBoundedSMulRealComplex`
- **Type**: `IsBoundedSMul ℝ ℂ`
- **What**: Local instance providing `IsBoundedSMul ℝ ℂ`, mathlib v4.29 compatibility.
- **How**: `NormSMulClass.toIsBoundedSMul`.
- **Hypotheses**: requires the previous `NormSMulClass` instance.
- **Uses from project**: `instNormSMulClassRealComplex` (instance chain).
- **Used by**: required for `ContinuousSMul ℝ ℂ` and follow-ons.
- **Visibility**: private
- **Lines**: 33-34
- **Notes**: none

### `instance instContinuousSMulRealComplex`
- **Type**: `ContinuousSMul ℝ ℂ`
- **What**: Local instance to upgrade `IsBoundedSMul` to `ContinuousSMul ℝ ℂ`.
- **How**: `IsBoundedSMul.continuousSMul`.
- **Hypotheses**: requires `IsBoundedSMul ℝ ℂ`.
- **Uses from project**: `instIsBoundedSMulRealComplex`.
- **Used by**: required for continuity arguments throughout (`continuous_ofReal.smul …`).
- **Visibility**: private
- **Lines**: 36-37
- **Notes**: none

### `lemma segment_subset_convex`
- **Type**: `{S : Set ℂ} (hS : Convex ℝ S) {c z : ℂ} (hc : c ∈ S) (hz : z ∈ S) : ∀ t ∈ Icc (0:ℝ) 1, c + t • (z - c) ∈ S`
- **What**: For convex S and two points c, z ∈ S, the parametric segment `c + t(z-c)` lies in S for `t ∈ [0,1]`.
- **How**: Rewrite `c + t • (z - c) = (1-t)•c + t•z` via `module`; apply `hS hc hz` with the standard convex combination weights.
- **Hypotheses**: S convex; c, z ∈ S.
- **Uses from project**: none.
- **Used by**: `integral_t_mul_deriv_eq`, `segmentIntegrand_lipschitzOnWith`, `hasDerivAt_segmentIntegral_aux`, `hasDerivAt_segmentIntegral`.
- **Visibility**: private
- **Lines**: 39-45
- **Notes**: none

### `lemma integral_t_mul_deriv_eq`
- **Type**: `{f : ℂ → ℂ} {S : Set ℂ} {c z : ℂ} (hS_open : IsOpen S) (hf : DifferentiableOn ℂ f S) (h_seg : ∀ t ∈ Icc 0 1, c + t • (z - c) ∈ S) : ∫ t in 0..1, t * (deriv f (c + t • (z - c)) * (z - c)) = f z - ∫ t in 0..1, f (c + t • (z - c))`
- **What**: Integration by parts identity: `∫₀¹ t · f'(γ(t)) (z - c) dt = f z - ∫₀¹ f(γ(t)) dt`, where γ(t) = c + t(z-c).
- **How**: Set up u(t)=t and v(t)=f(γ(t)) with derivatives u'=1, v' = f'(γ(t))(z-c). Apply `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`; chain rule uses `HasDerivAt.scomp` with γ' = z - c.
- **Hypotheses**: S open; f differentiable on S; segment lies in S.
- **Uses from project**: none (mathlib only).
- **Used by**: `hasDerivAt_segmentIntegral`.
- **Visibility**: private
- **Lines**: 47-120
- **Notes**: >30 lines (~74 lines); heavy `let`-binding pattern; uses `module` tactic.

### `lemma continuous_segmentMap`
- **Type**: `(c w : ℂ) : Continuous (fun t : ℝ => c + t • (w - c))`
- **What**: Continuity of the segment parametrization t ↦ c + t(w-c).
- **How**: `continuous_const.add (continuous_ofReal.smul continuous_const)`.
- **Hypotheses**: none.
- **Uses from project**: none.
- **Used by**: `segmentIntegrand_aestronglyMeasurable`, `segmentDerivIntegrand_aestronglyMeasurable`, `segmentIntegrand_intervalIntegrable`.
- **Visibility**: private
- **Lines**: 122-124
- **Notes**: none

### `lemma segmentIntegrand_aestronglyMeasurable`
- **Type**: `{f : ℂ → ℂ} {S : Set ℂ} {c w : ℂ} (hf : ContinuousOn f S) (h_seg : ∀ t ∈ Icc 0 1, c + t • (w - c) ∈ S) : AEStronglyMeasurable (fun t : ℝ => f (c + t • (w - c))) (volume.restrict (Ioc 0 1))`
- **What**: The composite `t ↦ f(c + t(w-c))` is AE strongly measurable on `(0,1]`.
- **How**: Continuity on `Icc 0 1` via `ContinuousOn.comp`; restrict to `Ioc` via `Ioc_subset_Icc_self` and `aestronglyMeasurable`.
- **Hypotheses**: f continuous on S; segment in S.
- **Uses from project**: `continuous_segmentMap`.
- **Used by**: `hasDerivAt_segmentIntegral_aux`.
- **Visibility**: private
- **Lines**: 126-137
- **Notes**: none

### `lemma segmentDerivIntegrand_aestronglyMeasurable`
- **Type**: `{f : ℂ → ℂ} {S : Set ℂ} {c z : ℂ} (hS_open : IsOpen S) (hf : DifferentiableOn ℂ f S) (h_seg : ∀ t ∈ Icc 0 1, c + t • (z - c) ∈ S) : AEStronglyMeasurable (fun t : ℝ => t • deriv f (c + t • (z - c))) (volume.restrict (Ioc 0 1))`
- **What**: AE strong measurability of `t ↦ t · f'(γ(t))`.
- **How**: Use `hf.contDiffOn.continuousOn_deriv_of_isOpen` to get `ContinuousOn (deriv f) S`; compose with continuous segment map; smul against `continuous_ofReal`; restrict to `Ioc`.
- **Hypotheses**: S open; f differentiable on S; segment in S.
- **Uses from project**: `continuous_segmentMap`.
- **Used by**: `hasDerivAt_segmentIntegral_aux`.
- **Visibility**: private
- **Lines**: 139-156
- **Notes**: none

### `lemma segmentIntegrand_intervalIntegrable`
- **Type**: `{f : ℂ → ℂ} {S : Set ℂ} {c z : ℂ} (hf : ContinuousOn f S) (h_seg : ∀ t ∈ Icc 0 1, c + t • (z - c) ∈ S) : IntervalIntegrable (fun t => f (c + t • (z - c))) volume 0 1`
- **What**: Interval-integrability of `t ↦ f(γ(t))` on `[0,1]`.
- **How**: `ContinuousOn.intervalIntegrable` via composition.
- **Hypotheses**: f continuous on S; segment in S.
- **Uses from project**: `continuous_segmentMap`.
- **Used by**: `hasDerivAt_segmentIntegral_aux`.
- **Visibility**: private
- **Lines**: 158-167
- **Notes**: none

### `lemma hasDerivAt_segmentIntegrand`
- **Type**: `{f : ℂ → ℂ} {S : Set ℂ} {c z : ℂ} {t : ℝ} (hS_open : IsOpen S) (hf : DifferentiableOn ℂ f S) (hpt : c + t • (z - c) ∈ S) : HasDerivAt (fun w => f (c + t • (w - c))) (t • deriv f (c + t • (z - c))) z`
- **What**: For fixed t, the map `w ↦ f(c + t(w-c))` has derivative `t · f'(γ(t))` at w = z.
- **How**: Chain rule: derivative of `w ↦ c + t(w-c)` is t (via `hasDerivAt_id.sub_const.const_smul`), then `hf.differentiableAt.hasDerivAt.comp`.
- **Hypotheses**: S open; f differentiable on S; γ(t) ∈ S.
- **Uses from project**: none.
- **Used by**: `hasDerivAt_segmentIntegral_aux`.
- **Visibility**: private
- **Lines**: 169-186
- **Notes**: none

### `lemma segmentIntegrand_lipschitzOnWith`
- **Type**: `{f : ℂ → ℂ} {S : Set ℂ} {c z : ℂ} {t : ℝ} {ε M : ℝ} (hS_open : IsOpen S) (hS_convex : Convex ℝ S) (hf : DifferentiableOn ℂ f S) (hc : c ∈ S) (hε_ball : Metric.ball z ε ⊆ S) (ht : t ∈ Icc 0 1) (hM_bound : ∀ w ∈ Metric.ball z ε, ‖deriv f (c + t • (w - c))‖ ≤ M) : LipschitzOnWith (Real.toNNReal (|t|*M)) (fun w => f (c + t • (w - c))) (Metric.ball z ε)`
- **What**: For fixed t, the map `w ↦ f(c + t(w-c))` is `|t|·M`-Lipschitz on `Metric.ball z ε`, with M an upper bound on `‖f'∘γ_t‖`.
- **How**: Bound `‖f(γ_t(x)) - f(γ_t(y))‖ ≤ M·‖γ_t(x) - γ_t(y)‖ = M·|t|·‖x-y‖` via `Convex.norm_image_sub_le_of_norm_deriv_le` on the convex segment between `γ_t(x)` and `γ_t(y)`; bound the derivative on this segment by parameterizing it through `convex_ball.add_smul_sub_mem`. Key lemma: `Convex.norm_image_sub_le_of_norm_deriv_le`.
- **Hypotheses**: S convex/open, c ∈ S, ball z ε ⊆ S, t ∈ [0,1], M dominates ‖f'∘γ_t‖.
- **Uses from project**: `segment_subset_convex`.
- **Used by**: `hasDerivAt_segmentIntegral_aux`.
- **Visibility**: private
- **Lines**: 188-252
- **Notes**: >30 lines (~65 lines); uses `module` tactic.

### `lemma hasDerivAt_segmentIntegral_aux`
- **Type**: `{f : ℂ → ℂ} {S : Set ℂ} {c z : ℂ} {ε : ℝ} (hε_pos : 0 < ε) (hS_convex : Convex ℝ S) (hS_open : IsOpen S) (hc : c ∈ S) (hz : z ∈ S) (hf : DifferentiableOn ℂ f S) (hε_ball : Metric.ball z ε ⊆ S) : HasDerivAt (fun w => ∫ t in 0..1, f (c + t • (w - c))) (∫ t in 0..1, t • deriv f (c + t • (z - c))) z`
- **What**: Differentiation under the integral sign for the parametric integral `H(w) = ∫₀¹ f(c + t(w-c)) dt`: H has derivative `∫₀¹ t·f'(γ(t)) dt` at z.
- **How**: Apply `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip`: requires (a) AE measurability eventually-near-z (via `segmentIntegrand_aestronglyMeasurable`), (b) integrability at z (via `segmentIntegrand_intervalIntegrable`), (c) AE measurability of derivative (`segmentDerivIntegrand_aestronglyMeasurable`), (d) AE Lipschitz domination (via `segmentIntegrand_lipschitzOnWith`), (e) integrable Lipschitz bound (`continuous_abs.intervalIntegrable.mul_const`), (f) AE pointwise HasDerivAt (`hasDerivAt_segmentIntegrand`). M is constructed compactness of `segmentMap '' (closedBall z ε' ×ˢ Icc 0 1)` via `IsCompact.image` and `IsCompact.bddAbove_image`. Key lemma: `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip`.
- **Hypotheses**: ε > 0; S convex/open; c, z ∈ S; f differentiable; ball z ε in S.
- **Uses from project**: `segment_subset_convex`, `segmentIntegrand_aestronglyMeasurable`, `segmentIntegrand_intervalIntegrable`, `segmentDerivIntegrand_aestronglyMeasurable`, `segmentIntegrand_lipschitzOnWith`, `hasDerivAt_segmentIntegrand`.
- **Used by**: `hasDerivAt_segmentIntegral`.
- **Visibility**: private
- **Lines**: 254-353
- **Notes**: >30 lines (~100 lines); core differentiation-under-integral argument.

### `lemma hasDerivAt_segmentIntegral`
- **Type**: `{f : ℂ → ℂ} {S : Set ℂ} {c z : ℂ} (hS_convex : Convex ℝ S) (hS_open : IsOpen S) (hc : c ∈ S) (hz : z ∈ S) (hf : DifferentiableOn ℂ f S) : HasDerivAt (fun w => ∫ t in 0..1, f (c + t • (w - c)) * (w - c)) (f z) z`
- **What**: The "convex primitive" candidate `F(w) = ∫₀¹ f(c + t(w-c))·(w-c) dt` satisfies F'(z) = f(z).
- **How**: Pull `(w - c)` out of the integral via `intervalIntegral.integral_mul_const`, reducing to `HasDerivAt (w ↦ H w · (w - c)) (f z) z` where H is the un-multiplied integral. Apply `HasDerivAt.mul` with H'(z) from `hasDerivAt_segmentIntegral_aux` and `(w↦w-c)'=1`; the key algebraic step `H'(z)·(z-c) = f z - H z` comes from `integral_t_mul_deriv_eq`. Key lemma: `integral_t_mul_deriv_eq` (the integration-by-parts identity).
- **Hypotheses**: S convex/open; c, z ∈ S; f differentiable on S.
- **Uses from project**: `segment_subset_convex`, `integral_t_mul_deriv_eq`, `hasDerivAt_segmentIntegral_aux`.
- **Used by**: `holomorphic_convex_primitive`.
- **Visibility**: private
- **Lines**: 355-404
- **Notes**: >30 lines (~50 lines).

### `theorem holomorphic_convex_primitive`
- **Type**: `{f : ℂ → ℂ} {S : Set ℂ} (hS_convex : Convex ℝ S) (hS_open : IsOpen S) (hS_ne : S.Nonempty) (hf : DifferentiableOn ℂ f S) : ∃ F : ℂ → ℂ, ∀ z ∈ S, HasDerivAt F (f z) z`
- **What**: Headline result: holomorphic functions on a nonempty convex open set have a primitive. The construction is `F(z) = ∫₀¹ f(c + t(z-c)) · (z - c) dt` for any base-point c ∈ S.
- **How**: Pick c ∈ S via `hS_ne`; apply `hasDerivAt_segmentIntegral` pointwise.
- **Hypotheses**: S convex, open, nonempty; f differentiable on S.
- **Uses from project**: `hasDerivAt_segmentIntegral`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 411-420
- **Notes**: none

## File Summary

`CauchyPrimitive.lean` constructs a holomorphic primitive on convex open subsets of ℂ via the segment integral `F(z) = ∫₀¹ f(c + t(z-c))·(z-c) dt`. The only public theorem is `holomorphic_convex_primitive`; everything else is private scaffolding.

The proof architecture splits into three layers:
1. Three local instances bridging mathlib v4.29 compatibility (`NormSMulClass ℝ ℂ` etc.).
2. Eight infrastructure lemmas: convex segment lies in S, continuity/measurability/integrability of the segment integrand and its derivative, pointwise HasDerivAt for the integrand at fixed t, Lipschitz domination, and the key integration-by-parts identity `integral_t_mul_deriv_eq`.
3. Two technical lemmas combining the infrastructure: `hasDerivAt_segmentIntegral_aux` (differentiation under the integral sign via `hasDerivAt_integral_of_dominated_loc_of_lip`) and `hasDerivAt_segmentIntegral` (multiply by `(w-c)` and use the IBP identity to deduce F' = f).

Total: 3 private instances + 11 private lemmas + 1 public theorem = 15 declarations. No sorries, no axioms. The 100-line `hasDerivAt_segmentIntegral_aux` is the longest single proof; the rest hover under 50 lines.
