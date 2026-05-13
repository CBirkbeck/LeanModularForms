# DixonDef.lean

**Path**: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/DixonDef.lean
**Lines**: 212
**Imports**: `SimplePoleIntegral`, `Mathlib.Analysis.Calculus.DSlope`
**Namespace**: none (top-level under `noncomputable section`); variable `{x : ℂ}`

---

## def `dixonH1`
- **Type**: `(f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (w : ℂ) : ℂ`
- **What**: Dixon h₁ integral: `∮_γ dslope(f, w, γ(t)) · γ'(t) dt`, well-defined for all `w` (including on-curve points).
- **How**: `∫ t in (0 : ℝ)..1, dslope f w (γ t) * deriv γ.toPath.extend t`.
- **Hypotheses**: f : ℂ → ℂ, γ closed piecewise-C¹ path, w : ℂ.
- **Uses-from-project**: `PiecewiseC1Path` (and `.toPath.extend` projection).
- **Used by**: `dixonFunction`, `dixonH1_eq_dixonH2_sub_winding_f`, `dixonFunction_eq_dixonH1`, `dixonH1_eq_contourIntegral'`.
- **Visibility**: public.
- **Lines**: 57-58.
- **Notes**: Continuous in evaluation point even at w because `dslope f w w = deriv f w`.

## def `dixonH2`
- **Type**: `(f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (w : ℂ) : ℂ`
- **What**: Dixon h₂ Cauchy-type integral `∮_γ f(γ(t))/(γ(t) - w) · γ'(t) dt`, well-defined for w off the curve.
- **How**: `∫ t in (0 : ℝ)..1, f (γ t) / (γ t - w) * deriv γ.toPath.extend t`.
- **Hypotheses**: f, γ closed path, w : ℂ.
- **Uses-from-project**: `PiecewiseC1Path`.
- **Used by**: `dixonFunction`, `dixonH1_eq_dixonH2_sub_winding_f`, `dixonFunction_eq_dixonH2`, `dixonH2_eq_contourIntegral'`.
- **Visibility**: public.
- **Lines**: 63-64.
- **Notes**: Standard Cauchy kernel form.

## def `dixonFunction`
- **Type**: `(f : ℂ → ℂ) (U : Set ℂ) (γ : PiecewiseC1Path x x) (w : ℂ) : ℂ`
- **What**: Piecewise Dixon function: `dixonH1 f γ w` on `U`, `dixonH2 f γ w` off `U`.
- **How**: `if w ∈ U then dixonH1 f γ w else dixonH2 f γ w`.
- **Hypotheses**: f, U, γ, w.
- **Uses-from-project**: `dixonH1`, `dixonH2`.
- **Used by**: `dixonFunction_eq_dixonH1`, `dixonFunction_eq_dixonH2`.
- **Visibility**: public.
- **Lines**: 71-73.
- **Notes**: Key construction for Dixon's brief proof of Cauchy's theorem.

## lemma `dslope_integrand_eq`
- **Type**: `{f : ℂ → ℂ} {γ : PiecewiseC1Path x x} {w : ℂ} (hoff : ∀ t ∈ Icc 0 1, γ t ≠ w) : ∀ t ∈ uIcc 0 1, dslope f w (γ t) * deriv γ.toPath.extend t = f (γ t) / (γ t - w) * deriv γ.toPath.extend t - f w / (γ t - w) * deriv γ.toPath.extend t`
- **What**: Pointwise on `[0,1]`, the dslope integrand splits as Cauchy integrand minus winding integrand.
- **How**: `dslope_of_ne _ hne` (using `hoff`) followed by `slope_def_field` and `ring`.
- **Hypotheses**: `γ` avoids `w` on the parameter interval.
- **Uses-from-project**: `PiecewiseC1Path`.
- **Used by**: `dixonH1_eq_dixonH2_sub_winding_f`.
- **Visibility**: `private`.
- **Lines**: 81-91.
- **Notes**: Algebraic identity, no integral.

## lemma `winding_integrand_eq_const_mul`
- **Type**: `(f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (w : ℂ) : (fun t => f w / (γ t - w) * deriv γ.toPath.extend t) = (fun t => f w * ((γ t - w)⁻¹ * deriv γ.toPath.extend t))`
- **What**: Reshape the winding integrand to expose the scalar constant `f w`.
- **How**: `funext t; rw [div_eq_mul_inv]; ring`.
- **Hypotheses**: none beyond inputs.
- **Uses-from-project**: `PiecewiseC1Path`.
- **Used by**: `contourIntegral_fw_div_eq`, `winding_integrand_intervalIntegrable`.
- **Visibility**: `private`.
- **Lines**: 95-101.
- **Notes**: Pure algebra preparation.

## lemma `contourIntegral_fw_div_eq`
- **Type**: `(f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (w : ℂ) : ∫ t in (0 : ℝ)..1, f w / (γ t - w) * deriv γ.toPath.extend t = f w * γ.contourIntegral (fun z => (z - w)⁻¹)`
- **What**: Pull out the constant `f w` from the winding integral.
- **How**: Unfold `PiecewiseC1Path.contourIntegral`, rewrite with `winding_integrand_eq_const_mul`, apply `intervalIntegral.integral_const_mul`.
- **Hypotheses**: none.
- **Uses-from-project**: `PiecewiseC1Path.contourIntegral`, `winding_integrand_eq_const_mul`.
- **Used by**: `dixonH1_eq_dixonH2_sub_winding_f`.
- **Visibility**: `private`.
- **Lines**: 105-111.
- **Notes**: Scalar extraction.

## lemma `winding_integrand_intervalIntegrable`
- **Type**: `(f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (w : ℂ) (h_base : IntervalIntegrable (fun t => (γ t - w)⁻¹ * deriv γ.toPath.extend t) volume 0 1) : IntervalIntegrable (fun t => f w / (γ t - w) * deriv γ.toPath.extend t) volume 0 1`
- **What**: Transfer integrability from `(γ - w)⁻¹ · γ'` to `f(w)/(γ - w) · γ'`.
- **How**: `rw [winding_integrand_eq_const_mul f γ w]; exact h_base.const_mul _`.
- **Hypotheses**: base integrability.
- **Uses-from-project**: `winding_integrand_eq_const_mul`, `PiecewiseC1Path`.
- **Used by**: `dixonH1_eq_dixonH2_sub_winding_f`.
- **Visibility**: `private`.
- **Lines**: 115-122.
- **Notes**: Integrability transfer via `IntervalIntegrable.const_mul`.

## theorem `avoids_delta_bound`
- **Type**: `(γ : PiecewiseC1Path x x) (w : ℂ) (hoff : ∀ t ∈ Icc 0 1, γ t ≠ w) : ∃ δ > 0, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - w‖`
- **What**: If γ avoids w on `[0,1]`, there is a strict positive distance bound.
- **How** (>10 lines): Compactness of `γ.toPath.extend '' Icc 0 1` (`isCompact_Icc.image γ.toPath.continuous_extend`), nonemptiness via `mem_image_of_mem` at 0, `w ∉ image` from `hoff`, conclude positivity of `Metric.infDist` via `IsClosed.notMem_iff_infDist_pos`, then use `Metric.infDist_le_dist_of_mem` and `Complex.dist_eq` / `norm_sub_rev` to express as the desired norm bound.
- **Hypotheses**: avoidance on `[0,1]`.
- **Uses-from-project**: `PiecewiseC1Path` (and `.toPath.continuous_extend`).
- **Used by**: `dixonH1_eq_dixonH2_sub_winding_f`.
- **Visibility**: `private`.
- **Lines**: 125-139.
- **Notes**: Distance-positivity from compactness.

## theorem `dixonH1_eq_dixonH2_sub_winding_f`
- **Type**: `{f : ℂ → ℂ} {γ : PiecewiseC1Path x x} (w : ℂ) (hoff : ∀ t ∈ Icc 0 1, γ t ≠ w) (h_cauchy_int : IntervalIntegrable ... volume 0 1) (h_base_int : IntervalIntegrable ... volume 0 1) : dixonH1 f γ w = dixonH2 f γ w - 2 * ↑Real.pi * I * generalizedWindingNumber γ w * f w`
- **What**: Fundamental h1/h2 identity: `h₁(w) = h₂(w) − 2πi · n(γ,w) · f(w)`.
- **How** (>10 lines): Unfold `dixonH1`, `dixonH2`; use `intervalIntegral.integral_congr (dslope_integrand_eq hoff)` to substitute the pointwise split, then `intervalIntegral.integral_sub h_cauchy_int (winding_integrand_intervalIntegrable f γ w h_base_int)`; reduce the second integral via `contourIntegral_fw_div_eq f γ w`; obtain the delta-positivity via `avoids_delta_bound γ w hoff` and apply `integral_inv_sub_eq_winding`; close with `ring`.
- **Hypotheses**: avoidance, Cauchy integrand integrability, base `(γ-w)⁻¹` integrability.
- **Uses-from-project**: `dixonH1`, `dixonH2`, `dslope_integrand_eq`, `winding_integrand_intervalIntegrable`, `contourIntegral_fw_div_eq`, `avoids_delta_bound`, `integral_inv_sub_eq_winding` (from SimplePoleIntegral), `generalizedWindingNumber`.
- **Used by**: `dixonH2_eq_dixonH1_add_winding_f`.
- **Visibility**: public.
- **Lines**: 152-169.
- **Notes**: Main theorem of the file.

## theorem `dixonH2_eq_dixonH1_add_winding_f`
- **Type**: `(...) : dixonH2 f γ w = dixonH1 f γ w + 2 * ↑Real.pi * I * generalizedWindingNumber γ w * f w`
- **What**: Algebraic rearrangement of the main identity (winding on the other side).
- **How**: `have h := dixonH1_eq_dixonH2_sub_winding_f ...; linear_combination -h`.
- **Hypotheses**: same as `dixonH1_eq_dixonH2_sub_winding_f`.
- **Uses-from-project**: `dixonH1_eq_dixonH2_sub_winding_f`, `dixonH1`, `dixonH2`, `generalizedWindingNumber`.
- **Used by**: external (downstream Dixon proof).
- **Visibility**: public.
- **Lines**: 172-182.
- **Notes**: Symmetric variant.

## theorem `dixonFunction_eq_dixonH1`
- **Type**: `{f} {U} {γ} {w} (hw : w ∈ U) : dixonFunction f U γ w = dixonH1 f γ w`
- **What**: On `U`, the Dixon function equals `h₁`.
- **How**: `if_pos hw`.
- **Hypotheses**: `w ∈ U`.
- **Uses-from-project**: `dixonFunction`, `dixonH1`.
- **Used by**: external.
- **Visibility**: public.
- **Lines**: 187-190.
- **Notes**: Trivial unfold of the piecewise.

## theorem `dixonFunction_eq_dixonH2`
- **Type**: `{f} {U} {γ} {w} (hw : w ∉ U) : dixonFunction f U γ w = dixonH2 f γ w`
- **What**: Off `U`, the Dixon function equals `h₂`.
- **How**: `if_neg hw`.
- **Hypotheses**: `w ∉ U`.
- **Uses-from-project**: `dixonFunction`, `dixonH2`.
- **Used by**: external.
- **Visibility**: public.
- **Lines**: 193-196.
- **Notes**: Trivial unfold.

## theorem `dixonH2_eq_contourIntegral'`
- **Type**: `{f} {γ} {w} : dixonH2 f γ w = γ.contourIntegral (fun z => f z / (z - w))`
- **What**: Rewrite `dixonH2` via the `PiecewiseC1Path.contourIntegral` API.
- **How**: `simp only [dixonH2, PiecewiseC1Path.contourIntegral]`.
- **Hypotheses**: none.
- **Uses-from-project**: `dixonH2`, `PiecewiseC1Path.contourIntegral`.
- **Used by**: external.
- **Visibility**: public.
- **Lines**: 201-204.
- **Notes**: Notation bridge.

## theorem `dixonH1_eq_contourIntegral'`
- **Type**: `{f} {γ} {w} : dixonH1 f γ w = γ.contourIntegral (fun z => dslope f w z)`
- **What**: Rewrite `dixonH1` via `contourIntegral`.
- **How**: `simp only [dixonH1, PiecewiseC1Path.contourIntegral]`.
- **Hypotheses**: none.
- **Uses-from-project**: `dixonH1`, `PiecewiseC1Path.contourIntegral`.
- **Used by**: external.
- **Visibility**: public.
- **Lines**: 207-210.
- **Notes**: Notation bridge.

---

## File Summary

Definitions of Dixon's h₁ (`dixonH1`), h₂ (`dixonH2`), and piecewise `dixonFunction` over closed `PiecewiseC1Path x x`, plus the fundamental identity `dixonH1 = dixonH2 - 2πi · n(γ,w) · f(w)` and its mirror. The identity is proved by combining a pointwise dslope split, scalar extraction, and `integral_inv_sub_eq_winding` (imported from `SimplePoleIntegral`). Supporting private lemmas isolate the algebraic and analytic ingredients: `dslope_integrand_eq` for the pointwise split, `winding_integrand_eq_const_mul` / `contourIntegral_fw_div_eq` / `winding_integrand_intervalIntegrable` for scalar-extraction and integrability transfer, and `avoids_delta_bound` for the compactness-based distance-positivity. Final theorems convert `dixonH1`/`dixonH2` to the `contourIntegral` notation. The file is the core algebraic kernel of Dixon's proof of Cauchy's integral theorem (Dixon 1971).
