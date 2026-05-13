# DslopeIntegral.lean Inventory

### `theorem dslope_eq_integral_deriv`
- **Type**: `{U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U) (hf : DifferentiableOn ℂ f U) {c w : ℂ} (hc : c ∈ U) (hw : w ∈ U) : dslope f c w = ∫ t in (0:ℝ)..1, deriv f (c + t • (w − c))`
- **What**: On a convex open set, `dslope f c w` equals the integral of `deriv f` along the segment from `c` to `w`.
- **How**: Segment `c + t•(w−c) = (1−t)•c + t•w ∈ U` by convexity; differentiability gives `HasDerivAt` pointwise; derivative continuous on `U` via `analyticOnNhd.deriv.continuousOn`; apply `integral_unitInterval_deriv_eq_sub`. Case-split on `w = c` (use `dslope_same` + `intervalIntegral.integral_const`) vs `w ≠ c` (rearrange via `slope_def_module`, `smul_eq_mul`, `inv_mul_cancel₀`).
- **Hypotheses**: `U` convex open, `f` differentiable on `U`, `c, w ∈ U`.
- **Uses from project**: []
- **Used by**: `continuousOn_dslope_first_arg`, `continuousOn_dslope_prod`
- **Visibility**: public
- **Lines**: 48–78
- **Notes**: `set_option backward.isDefEq.respectTransparency false`; >10 lines.

### `lemma exists_compact_tube`
- **Type**: `{U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U) {c₀ w₀ : ℂ} (hc₀ : c₀ ∈ U) (hw₀ : w₀ ∈ U) : ∃ ε > 0, ∃ K ⊆ U, IsCompact K ∧ ∀ c ∈ Metric.ball c₀ ε, ∀ t ∈ Icc 0 1, c + t • (w₀ − c) ∈ K`
- **What**: A compact tube `K ⊆ U` containing all segments `[c, w₀]` for `c` near `c₀`.
- **How**: Use `Metric.isOpen_iff` to get `ρ` with `closedBall c₀ ρ ⊆ U`; take `K = image` of `closedBall c₀ (ρ/2) × Icc 0 1` under `(c,t) ↦ (1−t)•c + t•w₀`; compactness via `isCompact_closedBall.prod isCompact_Icc` plus `IsCompact.image_of_continuousOn`.
- **Hypotheses**: `U` convex open, `c₀, w₀ ∈ U`.
- **Uses from project**: []
- **Used by**: `continuousOn_dslope_first_arg`
- **Visibility**: private
- **Lines**: 85–109
- **Notes**: >10 lines.

### `theorem continuousOn_dslope_first_arg`
- **Type**: `{U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U) (hf : DifferentiableOn ℂ f U) {w₀ : ℂ} (hw₀ : w₀ ∈ U) : ContinuousOn (fun c => dslope f c w₀) U`
- **What**: For fixed `w₀`, `c ↦ dslope f c w₀` is continuous on convex open `U`.
- **How**: Pointwise: use `exists_compact_tube` to get a tube `K`; bound `‖deriv f‖` on `K` by `M`; use `dslope_eq_integral_deriv` to rewrite as a parameter integral; apply `intervalIntegral.continuousAt_of_dominated_interval` with constant bound `max M 0`.
- **Hypotheses**: `U` convex open, `f` differentiable on `U`, `w₀ ∈ U`.
- **Uses from project**: [`exists_compact_tube`, `dslope_eq_integral_deriv`]
- **Used by**: `aestronglyMeasurable_deriv_dslope`
- **Visibility**: public
- **Lines**: 114–150
- **Notes**: >30 lines.

### `lemma exists_compact_tube_prod`
- **Type**: `{U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U) {c₀ w₀ : ℂ} (hc₀ : c₀ ∈ U) (hw₀ : w₀ ∈ U) : ∃ ε > 0, ∃ K ⊆ U, IsCompact K ∧ ∀ c ∈ ball c₀ ε, ∀ w ∈ ball w₀ ε, ∀ t ∈ Icc 0 1, c + t • (w − c) ∈ K`
- **What**: Joint version: compact tube `K ⊆ U` containing segments `[c, w]` for `c` near `c₀` and `w` near `w₀`.
- **How**: Take `ρ = min(ρ_c, ρ_w)/2`; image of `closedBall c₀ ρ × closedBall w₀ ρ × Icc 0 1` under `(c,w,t) ↦ (1−t)•c + t•w` is compact (product of compacts + continuous image), contained in `U` by convexity.
- **Hypotheses**: `U` convex open, `c₀, w₀ ∈ U`.
- **Uses from project**: []
- **Used by**: `continuousOn_dslope_prod`
- **Visibility**: private
- **Lines**: 158–196
- **Notes**: `set_option backward.isDefEq.respectTransparency false`; >30 lines.

### `theorem continuousOn_dslope_prod`
- **Type**: `{U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U) (hf : DifferentiableOn ℂ f U) : ContinuousOn (fun p : ℂ × ℂ => dslope f p.1 p.2) (U ×ˢ U)`
- **What**: Joint continuity of `(c, w) ↦ dslope f c w` on `U × U` for convex open `U`.
- **How**: Pointwise at `(c₀, w₀)`: use `exists_compact_tube_prod` for tube `K`, bound `‖deriv f‖` on `K`, rewrite via `dslope_eq_integral_deriv` and apply `continuousAt_of_dominated_interval`. Builds product-of-balls membership via `Prod.dist_eq` and `le_max_left/right`.
- **Hypotheses**: `U` convex open, `f` differentiable on `U`.
- **Uses from project**: [`exists_compact_tube_prod`, `dslope_eq_integral_deriv`]
- **Used by**: `continuousOn_dslope_prod_open`, `deriv_dslope_bounded_locally`, `deriv_dslope_bounded_on_compact`
- **Visibility**: public
- **Lines**: 200–257
- **Notes**: >50 lines.

### `theorem continuousOn_dslope_prod_open`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) (hf : DifferentiableOn ℂ f U) : ContinuousOn (fun p : ℂ × ℂ => dslope f p.1 p.2) (U ×ˢ U)`
- **What**: Non-convex variant of `continuousOn_dslope_prod`: joint continuity of `dslope` on any open set.
- **How**: Pointwise case split. Diagonal `c₀ = w₀`: any open ball around `c₀` in `U` is convex, apply `continuousOn_dslope_prod` on the ball. Off-diagonal `c₀ ≠ w₀`: `dslope f c w = (f w − f c)/(w − c)` eventually near `(c₀, w₀)` via `dslope_of_ne` + `slope_def_field`; continuity follows by `ContinuousAt.div` of continuous `f`.
- **Hypotheses**: `U` open, `f` differentiable on `U`.
- **Uses from project**: [`continuousOn_dslope_prod`]
- **Used by**: `continuousOn_dslope_first_arg_open`, `deriv_dslope_bounded_locally_open`, `deriv_dslope_bounded_on_compact_open`
- **Visibility**: public
- **Lines**: 273–309
- **Notes**: >30 lines.

### `theorem continuousOn_dslope_first_arg_open`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) (hf : DifferentiableOn ℂ f U) {w₀ : ℂ} (hw₀ : w₀ ∈ U) : ContinuousOn (fun c => dslope f c w₀) U`
- **What**: Non-convex variant of `continuousOn_dslope_first_arg`.
- **How**: Write `(fun c => dslope f c w₀) = (fun p => dslope f p.1 p.2) ∘ (fun c => (c, w₀))`; apply `continuousOn_dslope_prod_open` composed with `(continuous_id.prodMk continuous_const).continuousOn`.
- **Hypotheses**: `U` open, `f` differentiable on `U`, `w₀ ∈ U`.
- **Uses from project**: [`continuousOn_dslope_prod_open`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 314–323

### `theorem deriv_dslope_bounded_locally`
- **Type**: `{U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U) (hf : DifferentiableOn ℂ f U) {c₀ w₀ : ℂ} (hc₀ : c₀ ∈ U) (hw₀ : w₀ ∈ U) : ∃ C > 0, ∃ δ > 0, ∀ c ∈ ball c₀ δ, ∀ w ∈ ball w₀ δ, ‖deriv (dslope f c) w‖ ≤ C`
- **What**: Uniform Cauchy-estimate bound on `deriv (dslope f c) w` in a product neighborhood of `(c₀, w₀)`.
- **How**: Pick `ρ = min(ρ_c, ρ_w)/4` so `closedBall c₀ ρ, closedBall w₀ (3ρ/2) ⊆ U`. Bound `‖dslope f c z‖ ≤ M` on `closedBall c₀ ρ × closedBall w₀ (3ρ/2)` via `continuousOn_dslope_prod`. For `c ∈ ball c₀ (ρ/2)`, use `Complex.differentiableOn_dslope` + `DiffContOnCl` of `dslope f c` on `ball w (ρ/2)`. Apply `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` with sphere bound `max M 0`.
- **Hypotheses**: `U` convex open, `f` differentiable on `U`, `c₀, w₀ ∈ U`.
- **Uses from project**: [`continuousOn_dslope_prod`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 334–390
- **Notes**: >50 lines.

### `theorem deriv_dslope_bounded_locally_open`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) (hf : DifferentiableOn ℂ f U) {c₀ w₀ : ℂ} (hc₀ : c₀ ∈ U) (hw₀ : w₀ ∈ U) : ∃ C > 0, ∃ δ > 0, ∀ c ∈ ball c₀ δ, ∀ w ∈ ball w₀ δ, ‖deriv (dslope f c) w‖ ≤ C`
- **What**: Non-convex variant of `deriv_dslope_bounded_locally`.
- **How**: Same Cauchy-estimate scaffolding; uses `continuousOn_dslope_prod_open` in place of `continuousOn_dslope_prod`, otherwise identical to the convex version.
- **Hypotheses**: `U` open, `f` differentiable on `U`, `c₀, w₀ ∈ U`.
- **Uses from project**: [`continuousOn_dslope_prod_open`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 395–451
- **Notes**: >50 lines.

### `theorem deriv_dslope_bounded_on_compact`
- **Type**: `{U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U) (hf : DifferentiableOn ℂ f U) {K_c : Set ℂ} (hK_compact : IsCompact K_c) (hK_sub : K_c ⊆ U) {w₀ : ℂ} (hw₀ : w₀ ∈ U) : ∃ C > 0, ∃ δ > 0, ∀ c ∈ K_c, ∀ w ∈ ball w₀ δ, ‖deriv (dslope f c) w‖ ≤ C`
- **What**: Generalization of `deriv_dslope_bounded_locally`: first argument ranges over an arbitrary compact subset of `U` rather than a ball.
- **How**: Same Cauchy-estimate template with `ρ = ρ_w/4`. Bound `‖dslope‖` on `K_c × closedBall w₀ (3ρ/2)` via `continuousOn_dslope_prod`. Per-`c` argument identical to `deriv_dslope_bounded_locally`.
- **Hypotheses**: `U` convex open, `f` differentiable on `U`, `K_c ⊆ U` compact, `w₀ ∈ U`.
- **Uses from project**: [`continuousOn_dslope_prod`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 456–502
- **Notes**: >40 lines.

### `theorem deriv_dslope_bounded_on_compact_open`
- **Type**: same as `deriv_dslope_bounded_on_compact` but with only `IsOpen U`.
- **What**: Non-convex variant of `deriv_dslope_bounded_on_compact`.
- **How**: Same proof as above using `continuousOn_dslope_prod_open` instead of the convex version.
- **Hypotheses**: `U` open, `f` differentiable on `U`, `K_c ⊆ U` compact, `w₀ ∈ U`.
- **Uses from project**: [`continuousOn_dslope_prod_open`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 506–552
- **Notes**: >40 lines.

### `theorem aestronglyMeasurable_deriv_dslope`
- **Type**: `{U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U) (hf : DifferentiableOn ℂ f U) {w₀ : ℂ} (hw₀ : w₀ ∈ U) (μ : Measure ℂ) : AEStronglyMeasurable (fun c => deriv (dslope f c) w₀) (μ.restrict U)`
- **What**: `c ↦ deriv (dslope f c) w₀` is AE strongly measurable on `μ|_U`.
- **How**: Pointwise limit of continuous difference quotients. Use a real sequence `h_n = (ρ/2)/(n+1) → 0` so `w₀ + h_n ∈ U`. Each `q n c = (dslope f c (w₀ + h_n) − dslope f c w₀)/h_n` is AE-strongly-measurable via `continuousOn_dslope_first_arg`. For `c ∈ U`, `Tendsto (slope (dslope f c) w₀) (𝓝[≠] w₀) (𝓝 (deriv (dslope f c) w₀))` from `DifferentiableAt.hasDerivAt.tendsto_slope`. Conclude with `aestronglyMeasurable_of_tendsto_ae`.
- **Hypotheses**: `U` convex open, `f` differentiable on `U`, `w₀ ∈ U`, measure `μ`.
- **Uses from project**: [`continuousOn_dslope_first_arg`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 561–617
- **Notes**: >50 lines.

## File Summary
DslopeIntegral.lean develops the integral representation `dslope f c w = ∫₀¹ deriv f (c + t•(w − c))` for `f` holomorphic on a convex open set and propagates it to joint continuity of `dslope`, local boundedness of `deriv (dslope f c) w`, and AE measurability for fixed `w₀`. Each convex result is paired with a non-convex (`_open`) variant. The diagonal `c = w` case for the non-convex variant restricts to an inner ball and re-applies the convex theorem; the off-diagonal case uses `(f w − f c)/(w − c)` directly. The file is self-contained (only mathlib imports). 12 declarations total (2 private compact-tube helpers, 1 integral representation, 6 continuity/boundedness theorems, 1 first-arg+open variant, 1 measurability). No `sorry`, `axiom`. Two `set_option backward.isDefEq.respectTransparency false` annotations.

## N2 = 12
