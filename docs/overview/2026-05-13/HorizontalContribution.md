# HorizontalContribution.lean — Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HorizontalContribution.lean`
Lines: 131

## theorem/`fdBoundaryFun_eventuallyEq_affine_seg5` (private)
- **Type**: `(H t : ℝ) → 4/5 < t → fdBoundaryFun H =ᶠ[𝓝 t] (fun s ↦ (5·s - 9/2) + H·I)`
- **What**: On seg5 (the horizontal top edge), `fdBoundaryFun H` coincides locally with the affine map `s ↦ (5s - 9/2) + Hi`.
- **How**: `Filter.eventually_of_mem (Ioi_mem_nhds ht)` plus four `show ¬s ≤ k/5` `linarith` reductions of the `fdBoundaryFun` definition's `if`-cases.
- **Hypotheses**: `4/5 < t`.
- **Uses-from-project**: `fdBoundaryFun`.
- **Used by**: `deriv_fdBoundaryFun_seg5` (this file).
- **Visibility**: private
- **Lines**: 57–62

## theorem/`hasDerivAt_seg5_affine` (private)
- **Type**: `(H t : ℝ) → HasDerivAt (fun s ↦ (5·s - 9/2) + H·I) 5 t`
- **What**: The affine seg5 function has derivative `5`.
- **How**: Start with `Complex.ofRealCLM.hasDerivAt`, then `.const_mul (5 : ℂ)`, `.sub_const (9/2)`, `.add_const (H·I)`; close with `simpa`.
- **Hypotheses**: None.
- **Uses-from-project**: None.
- **Used by**: `deriv_fdBoundaryFun_seg5` (this file).
- **Visibility**: private
- **Lines**: 65–68

## theorem/`deriv_fdBoundaryFun_seg5`
- **Type**: `(H t : ℝ) → 4/5 < t → deriv (fdBoundaryFun H) t = 5`
- **What**: The derivative of `fdBoundaryFun H` along seg5 equals `5`.
- **How**: `EventuallyEq.deriv_eq` from `fdBoundaryFun_eventuallyEq_affine_seg5`; close with `hasDerivAt_seg5_affine`'s `.deriv`.
- **Hypotheses**: `4/5 < t`.
- **Uses-from-project**: `fdBoundaryFun`, `fdBoundaryFun_eventuallyEq_affine_seg5`, `hasDerivAt_seg5_affine`.
- **Used by**: Downstream seg5 / `HorizontalContributionData` users.
- **Visibility**: public
- **Lines**: 71–74

## theorem/`fdBoundaryFun_seg5_eq`
- **Type**: `(H t : ℝ) → 4/5 < t → fdBoundaryFun H t = (5·↑t - 9/2) + ↑H·I`
- **What**: Pointwise value of `fdBoundaryFun` on seg5: a horizontal line from `-1/2 + Hi` to `1/2 + Hi`.
- **How**: Unfold `fdBoundaryFun` and discharge four `¬t ≤ k/5` via `linarith`, closing the residual `ite_false` chain.
- **Hypotheses**: `4/5 < t`.
- **Uses-from-project**: `fdBoundaryFun`.
- **Used by**: Downstream seg5 callers.
- **Visibility**: public
- **Lines**: 78–82

## theorem/`horizontalContribution_eq`
- **Type**: For modular form `f`, `√3/2 < H` (unused, name with underscore), `γ : PiecewiseC1Path (fdStart H) (fdStart H)` agreeing with `fdBoundaryFun H` on `Icc 0 1`, and the seg5 integral equation `∫_{4/5}^1 logDeriv(modularFormCompOfComplex f) (fdBoundaryFun H t) · deriv (fdBoundaryFun H) t = 2πi · orderAtCusp' f`, concludes the same integral with `fdBoundaryFun` replaced by `γ` and `logDeriv (⇑f ∘ ofComplex)`.
- **What**: Transfer the seg5 integral from `fdBoundaryFun H` to a path `γ` that agrees on `[0,1]`.
- **How**: `intervalIntegral.integral_congr_ae` to discard the measure-zero singleton `{1}` (`(volume) {1} = 0`); on the complement, derive a neighborhood `Ioo (4/5) 1` of `t`, use `hγ` and `EventuallyEq.deriv_eq` to identify both `γ.toPath.extend t` and `deriv γ.toPath.extend t` with the `fdBoundaryFun` versions.
- **Hypotheses**: `γ = fdBoundaryFun H` pointwise on `Icc 0 1`; seg5 integral equation `h_seg5` for `fdBoundaryFun`.
- **Uses-from-project**: `fdBoundaryFun`, `fdStart`, `PiecewiseC1Path`, `logDeriv`, `modularFormCompOfComplex`, `orderAtCusp'`, `UpperHalfPlane.ofComplex`.
- **Used by**: `horizontalContributionData_of_seg5_eq` (this file).
- **Visibility**: public
- **Lines**: 89–117

## theorem/`horizontalContributionData_of_seg5_eq`
- **Type**: `(f) (hH : √3/2 < H) (γ : …) (hγ : …) (h_seg5 : …) → HorizontalContributionData f γ`
- **What**: Bundles `horizontalContribution_eq` into the project-level record `HorizontalContributionData`.
- **How**: Record literal `{ seg5_integral_eq := horizontalContribution_eq f hH γ hγ h_seg5 }`.
- **Hypotheses**: as in `horizontalContribution_eq`.
- **Uses-from-project**: `HorizontalContributionData`, `horizontalContribution_eq`.
- **Used by**: Higher-level valence-formula assembly.
- **Visibility**: public
- **Lines**: 120–129

## File Summary
Computes the contribution of the horizontal top edge (seg5 of the FD boundary, `t ∈ (4/5, 1]`) to the boundary integral of `logDeriv(f)`. On seg5, `fdBoundaryFun H t = (5t − 9/2) + Hi` and `deriv = 5`; given the seg5 integral equation `∫ logDeriv f · 5 = 2πi · orderAtCusp' f` (proved elsewhere via q-expansion factorization `F(q) = q^m g(q)`), the file transfers it to an arbitrary path `γ` agreeing with `fdBoundaryFun` on `[0,1]` and packages the result as `HorizontalContributionData`. References Diamond–Shurman Thm 3.1.1 and Serre Chapter VII.
