# PiecewiseC1Path.lean Inventory

**Path**: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/PiecewiseC1Path.lean
**Lines**: 150
**Imports**: `Mathlib.Analysis.Calculus.Deriv.Add`, `Mathlib.Topology.Path`

## Entries

### structure `PiecewiseC1Path`
- **Type**: structure (extends `Path x y`)
- **What**: A piecewise C¹ path `x → y` in a normed space — a `Path x y` together with a finite partition in `Ioo 0 1`, plus differentiability and derivative continuity of `Path.extend` off the partition (on `(0,1)`).
- **How**: Records four fields: `partition : Finset ℝ`, `partition_subset : (partition : Set ℝ) ⊆ Ioo 0 1`, `differentiable_off : ∀ t ∈ Ioo 0 1, t ∉ partition → DifferentiableAt ℝ toPath.extend t`, `deriv_continuous_off : ∀ t ∈ Ioo 0 1, t ∉ partition → ContinuousAt (deriv toPath.extend) t`.
- **Hypotheses**: `x y : E` where `[NormedAddCommGroup E] [NormedSpace ℝ E]`.
- **Uses-from-project**: None (foundational definition).
- **Used by**: The entire ForMathlib ContourIntegral / ValenceFormula chain — `HasCauchyPV`, `HasGeneralizedWindingNumber`, `PwC1Immersion`, etc.
- **Visibility**: public
- **Lines**: 52–62
- **Notes**: Endpoints 0 and 1 are NOT partition points (partition lives in open `Ioo 0 1`). Differentiability statements use `Path.extend` (`C(ℝ, X)`) because `deriv` operates on `ℝ → E`.

### def `PiecewiseC1Path.extendedPath`
- **Type**: def (in `namespace PiecewiseC1Path`)
- **What**: The underlying `ℝ → E` function via `Path.extend`.
- **How**: `γ.toPath.extend`.
- **Hypotheses**: `γ : PiecewiseC1Path x y`.
- **Uses-from-project**: None (uses `Path.extend` from Mathlib).
- **Used by**: `instance CoeFun`, all `PiecewiseC1Path` lemmas.
- **Visibility**: public
- **Lines**: 67
- **Notes**: Used by the `CoeFun` instance to make `γ : PiecewiseC1Path x y` callable as `γ : ℝ → E`.

### instance `instCoeFun PiecewiseC1Path`
- **Type**: instance
- **What**: `CoeFun (PiecewiseC1Path x y) (fun _ => ℝ → E)` with `coe := extendedPath`.
- **How**: `coe := extendedPath`.
- **Hypotheses**: `x y : E`.
- **Uses-from-project**: `PiecewiseC1Path.extendedPath`.
- **Used by**: Any callsite using `γ t` syntax for `γ : PiecewiseC1Path`.
- **Visibility**: public
- **Lines**: 69–70
- **Notes**: Enables `γ t` notation.

### theorem `PiecewiseC1Path.extendedPath_eq`
- **Type**: theorem (`@[simp]`)
- **What**: `γ.extendedPath = γ.toPath.extend`.
- **How**: `rfl`.
- **Hypotheses**: `γ : PiecewiseC1Path x y`.
- **Uses-from-project**: None.
- **Used by**: `simp` rewrites in any caller.
- **Visibility**: public
- **Lines**: 72–74
- **Notes**: Tagged `@[simp]`.

### theorem `PiecewiseC1Path.apply_zero`
- **Type**: theorem (`@[simp]`)
- **What**: `γ 0 = x`.
- **How**: `γ.toPath.extend_zero`.
- **Hypotheses**: `γ : PiecewiseC1Path x y`.
- **Uses-from-project**: None.
- **Used by**: `simp` rewrites.
- **Visibility**: public
- **Lines**: 76–78
- **Notes**: Mathlib `Path.extend_zero` underneath.

### theorem `PiecewiseC1Path.apply_one`
- **Type**: theorem (`@[simp]`)
- **What**: `γ 1 = y`.
- **How**: `γ.toPath.extend_one`.
- **Hypotheses**: `γ : PiecewiseC1Path x y`.
- **Uses-from-project**: None.
- **Used by**: `simp` rewrites.
- **Visibility**: public
- **Lines**: 80–82
- **Notes**: Mathlib `Path.extend_one` underneath.

### def `PiecewiseC1Path.IsClosed`
- **Type**: def
- **What**: Predicate that a `PiecewiseC1Path x y` is closed (`x = y`).
- **How**: `:= x = y`.
- **Hypotheses**: `_γ : PiecewiseC1Path x y`.
- **Uses-from-project**: None.
- **Used by**: Closed-path lemmas (residue theorem, null-homologous, etc.).
- **Visibility**: public
- **Lines**: 85
- **Notes**: Argument `_γ` is unused; presence is for API ergonomics.

### theorem `PiecewiseC1Path.continuous`
- **Type**: theorem
- **What**: The underlying extended path is continuous as `ℝ → E`.
- **How**: `γ.toPath.continuous_extend`.
- **Hypotheses**: `γ : PiecewiseC1Path x y`.
- **Uses-from-project**: None.
- **Used by**: Any lemma requiring continuity of the path function.
- **Visibility**: public
- **Lines**: 88–89
- **Notes**: Trivial wrapper on Mathlib `Path.continuous_extend`.

### private def `PiecewiseC1Path.translatePath`
- **Type**: def (`private`, with `omit [NormedSpace ℝ E]`)
- **What**: Translates a `Path x y` by a constant `c`, producing a `Path (x + c) (y + c)`.
- **How**: Defines `toFun t := γ t + c`, `continuous_toFun := γ.continuous.add continuous_const`, `source' := by simp`, `target' := by simp`.
- **Hypotheses**: `γ : Path x y`, `c : E`.
- **Uses-from-project**: None.
- **Used by**: `PiecewiseC1Path.translate`.
- **Visibility**: private
- **Lines**: 93–97
- **Notes**: Translation only needs `NormedAddCommGroup`; `omit` strips the `NormedSpace ℝ E` typeclass.

### private theorem `PiecewiseC1Path.translatePath_extend`
- **Type**: theorem (`private`, with `omit [NormedSpace ℝ E]`)
- **What**: `(translatePath γ c).extend = fun t => γ.extend t + c`.
- **How**: `ext t; rfl`.
- **Hypotheses**: `γ : Path x y`, `c : E`.
- **Uses-from-project**: `translatePath`.
- **Used by**: `PiecewiseC1Path.translate`.
- **Visibility**: private
- **Lines**: 100–103
- **Notes**: Equational lemma for the translated extension.

### def `PiecewiseC1Path.translate`
- **Type**: def
- **What**: Translates a `PiecewiseC1Path x y` by a constant `c`, producing a `PiecewiseC1Path (x + c) (y + c)`. Partition is unchanged.
- **How**: `toPath := translatePath γ.toPath c`. `partition := γ.partition`, `partition_subset := γ.partition_subset`. `differentiable_off`: rewrite using `translatePath_extend`, then `(γ.differentiable_off t ht htp).add (differentiableAt_const c)`. `deriv_continuous_off`: use `congr_arg deriv (translatePath_extend γ.toPath c)` to rewrite `deriv`, then `deriv_add_const'`, and conclude with `γ.deriv_continuous_off t ht htp`.
- **Hypotheses**: `γ : PiecewiseC1Path x y`, `c : E`.
- **Uses-from-project**: `translatePath`, `translatePath_extend`.
- **Used by**: Reparametrization / translation lemmas across the chain.
- **Visibility**: public
- **Lines**: 106–116
- **Notes**: Preserves partition; only updates differentiability/continuity proofs via Mathlib `deriv_add_const'` and `(_).add (differentiableAt_const c)`.

### structure `PwC1Immersion`
- **Type**: structure (extends `PiecewiseC1Path x y`)
- **What**: A piecewise C¹ immersion: extends `PiecewiseC1Path x y` with the requirement that the derivative is nonzero off partition points and has nonzero one-sided limits at partition points.
- **How**: Three fields: `deriv_ne_zero : ∀ t ∈ Ioo 0 1, t ∉ partition → deriv toPiecewiseC1Path.toPath.extend t ≠ 0`, `left_deriv_limit : ∀ p ∈ partition, ∃ L : E, L ≠ 0 ∧ Tendsto (deriv ...) (𝓝[<] p) (𝓝 L)`, `right_deriv_limit : ∀ p ∈ partition, ∃ L : E, L ≠ 0 ∧ Tendsto (deriv ...) (𝓝[>] p) (𝓝 L)`.
- **Hypotheses**: `x y : E`.
- **Uses-from-project**: `PiecewiseC1Path`.
- **Used by**: `IsNullHomologous`, residue theorem for immersed curves (e.g. C-4 in `HW33HigherOrderC4`).
- **Visibility**: public
- **Lines**: 125–134
- **Notes**: The well-defined-tangent-direction assumption needed for transverse crossings and the chord-to-tangent bound in `SingleCrossingData`.

### instance `instCoeFun PwC1Immersion`
- **Type**: instance
- **What**: `CoeFun (PwC1Immersion x y) (fun _ => ℝ → E)` via the underlying `PiecewiseC1Path`'s `extendedPath`.
- **How**: `coe γ := γ.toPiecewiseC1Path.extendedPath`.
- **Hypotheses**: `x y : E`.
- **Uses-from-project**: `PiecewiseC1Path.extendedPath`.
- **Used by**: Callsites with `γ : PwC1Immersion` using `γ t`.
- **Visibility**: public
- **Lines**: 138–139
- **Notes**: Enables `γ t` notation on `PwC1Immersion`.

### def `PwC1Immersion.IsClosed`
- **Type**: def
- **What**: Predicate that a `PwC1Immersion x y` is closed (`x = y`).
- **How**: `:= x = y`.
- **Hypotheses**: `_γ : PwC1Immersion x y`.
- **Uses-from-project**: None.
- **Used by**: Closed-immersion lemmas in the residue chain.
- **Visibility**: public
- **Lines**: 142
- **Notes**: Companion of `PiecewiseC1Path.IsClosed` for immersions.

### theorem `PwC1Immersion.continuous`
- **Type**: theorem
- **What**: The underlying extended path is continuous as `ℝ → E`.
- **How**: `γ.toPiecewiseC1Path.continuous`.
- **Hypotheses**: `γ : PwC1Immersion x y`.
- **Uses-from-project**: `PiecewiseC1Path.continuous`.
- **Used by**: Continuity-of-path callsites.
- **Visibility**: public
- **Lines**: 144–146
- **Notes**: Trivial forwarder to the underlying piecewise C¹ continuity.

## File Summary

Two foundational structures (`PiecewiseC1Path`, `PwC1Immersion`) extending `Path x y` with piecewise C¹ smoothness conditions (and additionally, nonzero derivatives for immersions). Each comes with `CoeFun` instances for `γ t` syntax, an `IsClosed` predicate, a `continuous` lemma, and `@[simp]`-tagged extend-value and endpoint lemmas. Includes a `translate` operation on `PiecewiseC1Path` (translation by a constant, preserving partition) plus its two private helpers. These structures underpin the entire ForMathlib ContourIntegral / ValenceFormula chain: every `HasCauchyPV`, `HasGeneralizedWindingNumber`, and `IsNullHomologous` statement is parametrized by one of these. Defined in arbitrary normed `E`, with the main applications instantiating `E = ℂ`.
