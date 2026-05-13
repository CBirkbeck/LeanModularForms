# /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/CurveMeasureZero.lean

## theorem `ForMathlib.hausdorffMeasure_two_real_zero`
- **Type**: `(s : Set ℝ) → (μH[2] : Measure ℝ) s = 0`.
- **What**: The 2-dimensional Hausdorff measure on `ℝ` is identically zero
  on any set (since `dim ℝ = 1 < 2`).
- **How**: Apply `Real.hausdorffMeasure_of_finrank_lt` with `1 < 2`
  (`Module.finrank_self`) to show `(μH[2] : Measure ℝ) = 0` as measures,
  then `simp` finishes.
- **Hypotheses**: none beyond `s` itself.
- **Uses-from-project**: mathlib only.
- **Used by**: `hausdorffMeasure_two_lipschitz_image_zero` (locally), and any
  consumer needing 2-D Hausdorff vanishing on `ℝ`.
- **Visibility**: public; namespace `ForMathlib`.
- **Lines**: 34-37.

## theorem `ForMathlib.hausdorffMeasure_two_lipschitz_image_zero`
- **Type**: `{K : NNReal} {f : ℝ → ℂ} (hf : LipschitzWith K f) (s : Set ℝ)
  → μH[2] (f '' s) = 0`.
- **What**: A Lipschitz image of a subset of `ℝ` in `ℂ` has zero 2-D
  Hausdorff measure.
- **How**: Apply `LipschitzWith.hausdorffMeasure_image_le` with `d = 2`
  (and `0 ≤ 2`), substitute `hausdorffMeasure_two_real_zero` for the domain,
  and simplify.
- **Hypotheses**: `LipschitzWith K f`.
- **Uses-from-project**: `hausdorffMeasure_two_real_zero` (above).
- **Used by**: `volume_image_lipschitz_real_zero` (locally).
- **Visibility**: public; namespace `ForMathlib`.
- **Lines**: 41-45.

## theorem `ForMathlib.volume_image_lipschitz_real_zero`
- **Type**: `{K : NNReal} {f : ℝ → ℂ} (hf : LipschitzWith K f) (s : Set ℝ)
  → volume (f '' s) = 0`.
- **What**: The Lebesgue volume in `ℂ` of a Lipschitz image of `s ⊆ ℝ` is
  zero — curve images have planar measure zero.
- **How**: Show `μH[2] : Measure ℂ` is `AddHaarMeasure` (via
  `isAddHaarMeasure_hausdorffMeasure` after rewriting `2 = finrank ℝ ℂ`
  by `Complex.finrank_real_complex`). Use
  `absolutelyContinuous_isAddHaarMeasure` to get
  `volume ≪ μH[2]`; conclude by applying it to
  `hausdorffMeasure_two_lipschitz_image_zero`.
- **Hypotheses**: `LipschitzWith K f`.
- **Uses-from-project**: `hausdorffMeasure_two_lipschitz_image_zero`.
- **Used by**: `exists_mem_not_mem_image_of_isOpen_of_lipschitz`,
  `exists_mem_not_mem_path_image_of_isOpen` (locally), and downstream
  null-homology consumers.
- **Visibility**: public; namespace `ForMathlib`.
- **Lines**: 53-62.

## theorem `ForMathlib.exists_mem_not_mem_image_of_isOpen_of_lipschitz`
- **Type**: For open nonempty `U ⊆ ℂ`, Lipschitz `f : ℝ → ℂ`, and any
  `s : Set ℝ`: `∃ w₀ ∈ U, w₀ ∉ f '' s`.
- **What**: For an open nonempty `U ⊆ ℂ` and a Lipschitz map
  `f : ℝ → ℂ`, there is a point of `U` outside `f '' s` — the Lipschitz
  image has measure 0 and `U` has positive measure.
- **How**: By contradiction. If `U ⊆ f '' s`, monotonicity of `volume`
  gives `volume U ≤ volume (f '' s) = 0` (via
  `volume_image_lipschitz_real_zero`); but `hU_open.measure_pos _ hU_ne`
  gives `volume U > 0`, contradiction.
- **Hypotheses**: `IsOpen U`, `U.Nonempty`, `LipschitzWith K f`.
- **Uses-from-project**: `volume_image_lipschitz_real_zero`.
- **Used by**: `exists_mem_not_mem_path_image_of_isOpen` (locally), and any
  consumer that picks a base-point off a Lipschitz curve.
- **Visibility**: public; namespace `ForMathlib`.
- **Lines**: 67-76.

## theorem `ForMathlib.lipschitzOnWith_of_nnnorm_deriv_le`
- **Type**: For convex `s ⊆ ℝ`, `f : ℝ → ℂ` differentiable on `s` with
  `‖deriv f x‖₊ ≤ C` on `s`: `LipschitzOnWith C f s`.
- **What**: Convex-set Lipschitz criterion from a bounded derivative — a
  `ℝ → ℂ` specialisation of the mathlib hasDerivWithin version.
- **How**: Apply `hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le` to
  the `HasDerivWithinAt` derived from `DifferentiableAt.hasDerivAt`.
- **Hypotheses**: `Convex ℝ s`; `DifferentiableAt ℝ f x` on `s`; nnnorm bound.
- **Uses-from-project**: mathlib only.
- **Used by**: Callers that want Lipschitz from a derivative bound; supplied
  for use in `PwC1Immersion` Lipschitz constructions.
- **Visibility**: public; namespace `ForMathlib`.
- **Lines**: 83-87.

## theorem `ForMathlib.exists_mem_not_mem_path_image_of_isOpen`
- **Type**: `{x y : ℂ} (γ : PiecewiseC1Path x y) {U : Set ℂ} (hU_open : IsOpen U)
  (hU_ne : U.Nonempty) {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend)
  → ∃ w₀ ∈ U, ∀ t ∈ Icc 0 1, γ.toPath.extend t ≠ w₀`.
- **What**: Specialisation of the previous existence result to a
  `PiecewiseC1Path`: an open nonempty set contains a point avoided by the
  path. Lipschitz hypothesis is supplied by the caller.
- **How**: Calls `exists_mem_not_mem_image_of_isOpen_of_lipschitz` with
  `s = Icc 0 1`, then repackages the "not in image" conclusion as a
  pointwise non-equality `∀ t ∈ Icc 0 1, γ.toPath.extend t ≠ w₀`.
- **Hypotheses**: open nonempty `U`, Lipschitz on the extended path.
- **Uses-from-project**: `PiecewiseC1Path` (and its `toPath.extend`);
  `exists_mem_not_mem_image_of_isOpen_of_lipschitz`.
- **Used by**: Null-homology / Cauchy-trick consumers that need a base-point
  off a given piecewise-C¹ curve.
- **Visibility**: public; namespace `ForMathlib`.
- **Lines**: 96-102.

## File Summary
Six public declarations, all in namespace `ForMathlib`. They establish:
(a) 2-D Hausdorff measure on `ℝ` is zero, (b) Lipschitz images of subsets
of `ℝ` in `ℂ` have zero 2-D Hausdorff and Lebesgue measure, (c) consequently
any open nonempty `U ⊆ ℂ` contains a point off such an image, and
(d) the same conclusion specialised to a `PiecewiseC1Path`. Includes a
small convenience lemma `lipschitzOnWith_of_nnnorm_deriv_le` (convex-set
Lipschitz from bounded derivative). Foundation for the Cauchy-formula trick
used to prove `contourIntegral_eq_zero_of_nullHomologous`. No `sorry`.
Imports: `Mathlib.MeasureTheory.Measure.Hausdorff`,
`Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls`,
`Mathlib.Topology.MetricSpace.HausdorffDimension`, plus the project's
`PiecewiseC1Path`.
