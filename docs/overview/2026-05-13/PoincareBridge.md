# PoincareBridge.lean — Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/PoincareBridge.lean`
Lines: 141

## theorem/`DifferentiableOn.hasPrimitive_of_convex`
- **Type**: `{f : ℂ → ℂ} {U : Set ℂ} → DifferentiableOn ℂ f U → Convex ℝ U → IsOpen U → U.Nonempty → ∃ F : ℂ → ℂ, ∀ z ∈ U, HasDerivAt F (f z) z`
- **What**: A holomorphic function on a convex open set has a holomorphic primitive (segment-integral construction).
- **How**: Applies mathlib's `Convex.exists_forall_hasDerivWithinAt` to `hf`, then upgrades `HasDerivWithinAt` to `HasDerivAt` via openness (`hUo.mem_nhds`).
- **Hypotheses**: holomorphy on `U`; `U` convex, open, nonempty.
- **Uses-from-project**: None (uses only mathlib).
- **Used by**: `DifferentiableOn.isExactOn_convex`, `DifferentiableOn.primitive_differentiableOn`, `contourIntegral_eq_zero_of_differentiableOn_convex_aux`, `contourIntegral_eq_sub_of_differentiableOn_convex` (this file).
- **Visibility**: public
- **Lines**: 45–50
- **Notes**: Cited reference: Ash–Novinger Thm 2.6.2.

## theorem/`DifferentiableOn.isExactOn_convex`
- **Type**: `{f : ℂ → ℂ} {U : Set ℂ} → DifferentiableOn ℂ f U → Convex ℝ U → IsOpen U → U.Nonempty → Complex.IsExactOn f U`
- **What**: Same primitive existence stated in mathlib's `Complex.IsExactOn` form.
- **How**: Direct call `hf.hasPrimitive_of_convex hU hUo hUne` (definitional repackaging).
- **Hypotheses**: as `hasPrimitive_of_convex`.
- **Uses-from-project**: `DifferentiableOn.hasPrimitive_of_convex`.
- **Used by**: Downstream Cauchy theorems via the `IsExactOn`-API.
- **Visibility**: public
- **Lines**: 54–58

## theorem/`DifferentiableOn.primitive_differentiableOn`
- **Type**: same context as above, conclusion `∃ F, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, HasDerivAt F (f z) z`
- **What**: The primitive itself is differentiable on `U`.
- **How**: Destructure `hasPrimitive_of_convex`; each `HasDerivAt` yields a `DifferentiableAt`, which gives `DifferentiableWithinAt`.
- **Hypotheses**: as `hasPrimitive_of_convex`.
- **Uses-from-project**: `DifferentiableOn.hasPrimitive_of_convex`.
- **Used by**: None in this file (callers of `Complex.IsExactOn` chain).
- **Visibility**: public
- **Lines**: 61–66

## theorem/`PiecewiseC1Path.contourIntegral_eq_zero_of_differentiableOn_convex_aux`
- **Type**: `{f : ℂ → ℂ} {U : Set ℂ} → (γ : PiecewiseC1Path x y) → x = y → Convex ℝ U → IsOpen U → U.Nonempty → DifferentiableOn ℂ f U → (∀ t ∈ Icc 0 1, γ t ∈ U) → IntervalIntegrable … 0 1 → γ.contourIntegral f = 0`
- **What**: Cauchy's theorem for closed piecewise C¹ paths in a convex open set (integrability supplied).
- **How**: Obtain primitive `F` via `hasPrimitive_of_convex`; apply `contourIntegral_eq_zero_of_hasDerivAt_of_closed`.
- **Hypotheses**: closed path `x = y`; path lies in `U`; integrand `f(γ(t)) · γ'(t)` interval-integrable; `U` convex, open, nonempty; `f` holomorphic on `U`.
- **Uses-from-project**: `PiecewiseC1Path`, `contourIntegral_eq_zero_of_hasDerivAt_of_closed`, `DifferentiableOn.hasPrimitive_of_convex`.
- **Used by**: Top-level Cauchy theorems (callers needing integrability supplied).
- **Visibility**: public
- **Lines**: 82–91

## theorem/`PiecewiseC1Path.contourIntegral_eq_sub_of_differentiableOn_convex`
- **Type**: same setup but non-closed; conclusion `∃ F, γ.contourIntegral f = F y - F x ∧ ∀ z ∈ U, HasDerivAt F (f z) z`
- **What**: FTC formulation — primitive evaluates contour integral on convex open set.
- **How**: Obtain `F` via `hasPrimitive_of_convex`; package with `contourIntegral_eq_sub_of_hasDerivAt`.
- **Hypotheses**: as aux but no `hclosed`; integrability supplied.
- **Uses-from-project**: `PiecewiseC1Path`, `contourIntegral_eq_sub_of_hasDerivAt`, `DifferentiableOn.hasPrimitive_of_convex`.
- **Used by**: `Complex.IsExactOn.contourIntegral_eq_sub` (this file).
- **Visibility**: public
- **Lines**: 100–110

## theorem/`Complex.IsExactOn.contourIntegral_eq_sub`
- **Type**: `{f : ℂ → ℂ} {U : Set ℂ} → Complex.IsExactOn f U → (γ : PiecewiseC1Path x y) → (∀ t ∈ Icc 0 1, γ t ∈ U) → IntervalIntegrable … 0 1 → ∃ F, γ.contourIntegral f = F y - F x ∧ ∀ z ∈ U, HasDerivAt F (f z) z`
- **What**: Path-free FTC: any `IsExactOn` primitive evaluates the contour integral.
- **How**: Destructure `IsExactOn`; apply `γ.contourIntegral_eq_sub_of_hasDerivAt`.
- **Hypotheses**: `f` exact on `U`; path lies in `U`; interval integrability.
- **Uses-from-project**: `PiecewiseC1Path`, `contourIntegral_eq_sub_of_hasDerivAt`.
- **Used by**: Downstream consumers of `IsExactOn`.
- **Visibility**: public
- **Lines**: 118–127

## theorem/`Complex.IsExactOn.contourIntegral_eq_zero_of_closed`
- **Type**: `{f : ℂ → ℂ} {U : Set ℂ} {x : ℂ} → Complex.IsExactOn f U → (γ : PiecewiseC1Path x x) → (∀ t ∈ Icc 0 1, γ t ∈ U) → IntervalIntegrable … 0 1 → γ.contourIntegral f = 0`
- **What**: Path-free Cauchy: contour integral of an exact function on `U` over a closed path in `U` is zero.
- **How**: Destructure `IsExactOn`; apply `γ.contourIntegral_eq_zero_of_hasDerivAt_of_closed` with reflexive endpoint equality.
- **Hypotheses**: `f` exact; closed path in `U`; interval integrability.
- **Uses-from-project**: `PiecewiseC1Path`, `contourIntegral_eq_zero_of_hasDerivAt_of_closed`.
- **Used by**: Cauchy applications throughout the chain.
- **Visibility**: public
- **Lines**: 131–139

## File Summary
Glue between mathlib's `Complex.IsExactOn` / `Convex.exists_forall_hasDerivWithinAt` and the project's `PiecewiseC1Path.contourIntegral`. Provides primitive existence on convex open sets and the resulting Cauchy/FTC statements for piecewise C¹ paths. All proofs are short and reduce to mathlib lemmas plus the project's `contourIntegral_eq_*_of_hasDerivAt*` family; this file is the convex-domain "Poincaré lemma" bridge layer.
