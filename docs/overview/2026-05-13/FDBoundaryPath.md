# FDBoundaryPath.lean Inventory

### `private lemma fdBoundaryPath_extend_eq`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ∈ Icc 0 1) : (fdBoundaryPath H).extend t = fdBoundaryFun H t`
- **What**: `Path.extend` of `fdBoundaryPath H` agrees pointwise with `fdBoundaryFun H` on `[0,1]`.
- **How**: `rw [Path.extend_apply _ ht]` then `rfl`.
- **Hypotheses**: `t ∈ Icc 0 1`.
- **Uses from project**: `fdBoundaryPath`, `fdBoundaryFun` (from `FDBoundary`).
- **Used by**: `fdBoundaryPath_extend_eventuallyEq`, `fdBoundaryPC1Path_eq`.
- **Visibility**: `private`.
- **Lines**: 31-34.
- **Notes**: Punctures the `Path.extend` wrapper to expose the raw piecewise function.

### `private lemma fdBoundaryPath_extend_eventuallyEq`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ∈ Ioo 0 1) : (fdBoundaryPath H).extend =ᶠ[𝓝 t] fdBoundaryFun H`
- **What**: Near any `t ∈ (0,1)`, `Path.extend` of `fdBoundaryPath H` is eventually equal to `fdBoundaryFun H`.
- **How**: `Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2)` applied with `fdBoundaryPath_extend_eq` on `Ioo_subset_Icc_self`.
- **Hypotheses**: `t ∈ Ioo 0 1`.
- **Uses from project**: `fdBoundaryPath`, `fdBoundaryFun`; `fdBoundaryPath_extend_eq` (this file).
- **Used by**: `fdBoundaryPath_differentiableAt_off`, `fdBoundaryPath_deriv_continuousAt_off`.
- **Visibility**: `private`.
- **Lines**: 36-39.
- **Notes**: Promotes pointwise equality to a `𝓝 t` equality for derivative arguments.

### `private def seg1Fun`
- **Type**: `(H : ℝ) : ℝ → ℂ`
- **What**: Segment 1 (vertical descent at re = 1/2): `t ↦ 1/2 + (H - 5t(H - √3/2)) i`.
- **How**: Direct lambda.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `seg1Fun_differentiableAt`, `seg1Fun_contDiff`, `fdBoundaryFun_eventuallyEq_seg1`.
- **Visibility**: `private def`.
- **Lines**: 43-44.
- **Notes**: Parametrises the down-stroke on the right vertical edge for `t ∈ [0, 1/5]`.

### `private def seg2Fun`
- **Type**: `ℝ → ℂ`
- **What**: Segment 2 (arc from angle π/3 to π/2): `t ↦ exp ((π/3 + (5t-1)(π/2 - π/3)) i)`.
- **How**: Direct lambda.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `seg2Fun_differentiableAt`, `seg2Fun_contDiff`, `fdBoundaryFun_eventuallyEq_seg2`.
- **Visibility**: `private def`.
- **Lines**: 46-47.
- **Notes**: Unit circle arc for `t ∈ [1/5, 2/5]` (right half of the bottom arc).

### `private def seg3Fun`
- **Type**: `ℝ → ℂ`
- **What**: Segment 3 (arc from angle π/2 to 2π/3): `t ↦ exp ((π/2 + (5t-2)(2π/3 - π/2)) i)`.
- **How**: Direct lambda.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `seg3Fun_differentiableAt`, `seg3Fun_contDiff`, `fdBoundaryFun_eventuallyEq_seg3`.
- **Visibility**: `private def`.
- **Lines**: 49-50.
- **Notes**: Unit circle arc for `t ∈ [2/5, 3/5]` (left half of the bottom arc).

### `private def seg4Fun`
- **Type**: `(H : ℝ) : ℝ → ℂ`
- **What**: Segment 4 (vertical ascent at re = -1/2): `t ↦ -1/2 + (√3/2 + (5t-3)(H - √3/2)) i`.
- **How**: Direct lambda.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `seg4Fun_differentiableAt`, `seg4Fun_contDiff`, `fdBoundaryFun_eventuallyEq_seg4`.
- **Visibility**: `private def`.
- **Lines**: 52-53.
- **Notes**: Parametrises the up-stroke on the left vertical edge for `t ∈ [3/5, 4/5]`.

### `private def seg5Fun`
- **Type**: `(H : ℝ) : ℝ → ℂ`
- **What**: Segment 5 (top horizontal at im = H): `t ↦ (5t - 9/2) + H i`.
- **How**: Direct lambda.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `seg5Fun_differentiableAt`, `seg5Fun_contDiff`, `fdBoundaryFun_eventuallyEq_seg5`.
- **Visibility**: `private def`.
- **Lines**: 55-56.
- **Notes**: Top edge return for `t ∈ [4/5, 1]`.

### `private lemma seg1Fun_differentiableAt`
- **Type**: `(H : ℝ) (t : ℝ) : DifferentiableAt ℝ (seg1Fun H) t`
- **What**: `seg1Fun H` is differentiable at every real `t`.
- **How**: Direct term-mode build from `differentiableAt_const`, `Complex.ofRealCLM.differentiable.differentiableAt`, and additive/multiplicative combinators.
- **Hypotheses**: none.
- **Uses from project**: `seg1Fun` (this file).
- **Used by**: `fdBoundaryFun_differentiableAt_off`.
- **Visibility**: `private`.
- **Lines**: 60-65.
- **Notes**: One of five segment differentiability lemmas.

### `private lemma seg2Fun_differentiableAt`
- **Type**: `(t : ℝ) : DifferentiableAt ℝ seg2Fun t`
- **What**: `seg2Fun` is differentiable everywhere.
- **How**: `Complex.differentiable_exp.differentiableAt.comp` with constant/`ofRealCLM` differentiability and `(differentiableAt_const _).mul`.
- **Hypotheses**: none.
- **Uses from project**: `seg2Fun` (this file).
- **Used by**: `fdBoundaryFun_differentiableAt_off`.
- **Visibility**: `private`.
- **Lines**: 67-73.
- **Notes**: Differentiability of `exp` composed with affine real argument.

### `private lemma seg3Fun_differentiableAt`
- **Type**: `(t : ℝ) : DifferentiableAt ℝ seg3Fun t`
- **What**: `seg3Fun` is differentiable everywhere.
- **How**: Same recipe as `seg2Fun_differentiableAt` (exp ∘ affine).
- **Hypotheses**: none.
- **Uses from project**: `seg3Fun` (this file).
- **Used by**: `fdBoundaryFun_differentiableAt_off`.
- **Visibility**: `private`.
- **Lines**: 75-81.
- **Notes**: Structural mirror of `seg2Fun_differentiableAt`.

### `private lemma seg4Fun_differentiableAt`
- **Type**: `(H : ℝ) (t : ℝ) : DifferentiableAt ℝ (seg4Fun H) t`
- **What**: `seg4Fun H` is differentiable everywhere.
- **How**: Affine combinators on constants and `Complex.ofRealCLM.differentiable.differentiableAt`.
- **Hypotheses**: none.
- **Uses from project**: `seg4Fun` (this file).
- **Used by**: `fdBoundaryFun_differentiableAt_off`.
- **Visibility**: `private`.
- **Lines**: 83-89.
- **Notes**: Mirrors `seg1Fun_differentiableAt`.

### `private lemma seg5Fun_differentiableAt`
- **Type**: `(H : ℝ) (t : ℝ) : DifferentiableAt ℝ (seg5Fun H) t`
- **What**: `seg5Fun H` is differentiable everywhere.
- **How**: Compositional differentiability of affine `ℝ → ℂ`.
- **Hypotheses**: none.
- **Uses from project**: `seg5Fun` (this file).
- **Used by**: `fdBoundaryFun_differentiableAt_off`.
- **Visibility**: `private`.
- **Lines**: 91-94.
- **Notes**: Simplest of the five — pure affine.

### `private lemma seg1Fun_contDiff`
- **Type**: `(H : ℝ) : ContDiff ℝ ⊤ (seg1Fun H)`
- **What**: `seg1Fun H` is smooth (`ContDiff ℝ ⊤`).
- **How**: `contDiff_const.add` chained with `(contDiff_const.mul Complex.ofRealCLM.contDiff)` etc.
- **Hypotheses**: none.
- **Uses from project**: `seg1Fun` (this file).
- **Used by**: `fdBoundaryFun_deriv_continuousAt_off`.
- **Visibility**: `private`.
- **Lines**: 98-102.
- **Notes**: Smoothness needed to extract continuous derivative.

### `private lemma seg2Fun_contDiff`
- **Type**: `ContDiff ℝ ⊤ seg2Fun`
- **What**: `seg2Fun` is smooth.
- **How**: `Complex.contDiff_exp.comp` on affine `ℝ → ℂ`.
- **Hypotheses**: none.
- **Uses from project**: `seg2Fun` (this file).
- **Used by**: `fdBoundaryFun_deriv_continuousAt_off`.
- **Visibility**: `private`.
- **Lines**: 104-108.
- **Notes**: Smoothness of `exp ∘ affine`.

### `private lemma seg3Fun_contDiff`
- **Type**: `ContDiff ℝ ⊤ seg3Fun`
- **What**: `seg3Fun` is smooth.
- **How**: `Complex.contDiff_exp.comp` on affine `ℝ → ℂ`.
- **Hypotheses**: none.
- **Uses from project**: `seg3Fun` (this file).
- **Used by**: `fdBoundaryFun_deriv_continuousAt_off`.
- **Visibility**: `private`.
- **Lines**: 110-114.
- **Notes**: Mirror of `seg2Fun_contDiff`.

### `private lemma seg4Fun_contDiff`
- **Type**: `(H : ℝ) : ContDiff ℝ ⊤ (seg4Fun H)`
- **What**: `seg4Fun H` is smooth.
- **How**: Combinator recipe of `contDiff_const.add` and `contDiff_const.mul Complex.ofRealCLM.contDiff`.
- **Hypotheses**: none.
- **Uses from project**: `seg4Fun` (this file).
- **Used by**: `fdBoundaryFun_deriv_continuousAt_off`.
- **Visibility**: `private`.
- **Lines**: 116-120.
- **Notes**: Mirror of `seg1Fun_contDiff`.

### `private lemma seg5Fun_contDiff`
- **Type**: `(H : ℝ) : ContDiff ℝ ⊤ (seg5Fun H)`
- **What**: `seg5Fun H` is smooth.
- **How**: `((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).add contDiff_const`.
- **Hypotheses**: none.
- **Uses from project**: `seg5Fun` (this file).
- **Used by**: `fdBoundaryFun_deriv_continuousAt_off`.
- **Visibility**: `private`.
- **Lines**: 122-123.
- **Notes**: Affine smooth.

### `private lemma fdBoundaryFun_eventuallyEq_seg1`
- **Type**: `(H : ℝ) (t : ℝ) (ht1 : t < 1/5) : fdBoundaryFun H =ᶠ[𝓝 t] seg1Fun H`
- **What**: On the left of `t = 1/5`, `fdBoundaryFun H` is eventually equal to `seg1Fun H`.
- **How**: `Filter.eventually_of_mem (Iio_mem_nhds ht1)`, then `simp only [fdBoundaryFun, seg1Fun, show s ≤ 1/5 from le_of_lt hs, ite_true]` to collapse the chained ite.
- **Hypotheses**: `t < 1/5`.
- **Uses from project**: `fdBoundaryFun`; `seg1Fun` (this file).
- **Used by**: `fdBoundaryFun_differentiableAt_off`, `fdBoundaryFun_deriv_continuousAt_off`.
- **Visibility**: `private`.
- **Lines**: 127-131.
- **Notes**: Pulls open the ite-cascade in `fdBoundaryFun`.

### `private lemma fdBoundaryFun_eventuallyEq_seg2`
- **Type**: `(H : ℝ) (t : ℝ) (ht1 : 1/5 < t) (ht2 : t < 2/5) : fdBoundaryFun H =ᶠ[𝓝 t] seg2Fun`
- **What**: On `(1/5, 2/5)`, `fdBoundaryFun H` is eventually equal to `seg2Fun`.
- **How**: `Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht2))`, then `simp only` with `not_le.mpr hs1` and `le_of_lt hs2` to select the second branch.
- **Hypotheses**: `1/5 < t < 2/5`.
- **Uses from project**: `fdBoundaryFun`; `seg2Fun` (this file).
- **Used by**: `fdBoundaryFun_differentiableAt_off`, `fdBoundaryFun_deriv_continuousAt_off`.
- **Visibility**: `private`.
- **Lines**: 133-141.
- **Notes**: Two-sided neighborhood.

### `private lemma fdBoundaryFun_eventuallyEq_seg3`
- **Type**: `(H : ℝ) (t : ℝ) (ht2 : 2/5 < t) (ht3 : t < 3/5) : fdBoundaryFun H =ᶠ[𝓝 t] seg3Fun`
- **What**: On `(2/5, 3/5)`, `fdBoundaryFun H` is eventually equal to `seg3Fun`.
- **How**: Inter `Ioi_mem_nhds ht2` and `Iio_mem_nhds ht3`, then `simp only` with chained `not_le.mpr` using `lt_trans (by norm_num : (1:ℝ)/5 < 2/5) hs2` to discharge `¬ s ≤ 1/5`.
- **Hypotheses**: `2/5 < t < 3/5`.
- **Uses from project**: `fdBoundaryFun`; `seg3Fun` (this file).
- **Used by**: `fdBoundaryFun_differentiableAt_off`, `fdBoundaryFun_deriv_continuousAt_off`.
- **Visibility**: `private`.
- **Lines**: 143-152.
- **Notes**: Three `not_le.mpr` clauses peel away earlier branches.

### `private lemma fdBoundaryFun_eventuallyEq_seg4`
- **Type**: `(H : ℝ) (t : ℝ) (ht3 : 3/5 < t) (ht4 : t < 4/5) : fdBoundaryFun H =ᶠ[𝓝 t] seg4Fun H`
- **What**: On `(3/5, 4/5)`, `fdBoundaryFun H` is eventually equal to `seg4Fun H`.
- **How**: Inter `Ioi_mem_nhds ht3` and `Iio_mem_nhds ht4`, plus four `not_le.mpr` clauses chained by `lt_trans`.
- **Hypotheses**: `3/5 < t < 4/5`.
- **Uses from project**: `fdBoundaryFun`; `seg4Fun` (this file).
- **Used by**: `fdBoundaryFun_differentiableAt_off`, `fdBoundaryFun_deriv_continuousAt_off`.
- **Visibility**: `private`.
- **Lines**: 154-164.
- **Notes**: Symmetric to seg2 but on the upper segment.

### `private lemma fdBoundaryFun_eventuallyEq_seg5`
- **Type**: `(H : ℝ) (t : ℝ) (ht4 : 4/5 < t) : fdBoundaryFun H =ᶠ[𝓝 t] seg5Fun H`
- **What**: To the right of `t = 4/5`, `fdBoundaryFun H` is eventually equal to `seg5Fun H`.
- **How**: `Filter.eventually_of_mem (Ioi_mem_nhds ht4)`, then `simp only` with four chained `not_le.mpr (lt_trans …)`.
- **Hypotheses**: `4/5 < t`.
- **Uses from project**: `fdBoundaryFun`; `seg5Fun` (this file).
- **Used by**: `fdBoundaryFun_differentiableAt_off`, `fdBoundaryFun_deriv_continuousAt_off`.
- **Visibility**: `private`.
- **Lines**: 166-174.
- **Notes**: Final `else` branch of the ite-cascade.

### `private lemma fdBoundaryFun_differentiableAt_off`
- **Type**: `(H : ℝ) (t : ℝ) (_ht : t ∈ Ioo 0 1) (htp : t ∉ fdBoundaryPartition) : DifferentiableAt ℝ (fdBoundaryFun H) t`
- **What**: `fdBoundaryFun H` is real-differentiable at every `t ∈ (0,1)` away from the partition `{1/5, 2/5, 3/5, 4/5}`.
- **How**: Unfolds `fdBoundaryPartition` (with `Finset.mem_insert`/`Finset.mem_singleton`), `push Not at htp` to obtain four neqs `ht1..ht4`. Cascading `by_cases` on `t < 1/5`, `t < 2/5`, `t < 3/5`, `t < 4/5`: each branch combines `(segiFun_differentiableAt _).congr_of_eventuallyEq (fdBoundaryFun_eventuallyEq_segi …)`, using `lt_of_le_of_ne` against the corresponding `hti`.
- **Hypotheses**: `t ∈ Ioo 0 1`, `t ∉ fdBoundaryPartition`.
- **Uses from project**: `fdBoundaryPartition` (from `FDBoundary`); all five segment differentiability lemmas and eventually-equal lemmas (this file).
- **Used by**: `fdBoundaryPath_differentiableAt_off`.
- **Visibility**: `private`.
- **Lines**: 178-201.
- **Notes**: Proof ≈24 lines; `push Not at htp` is critical to expose the four neqs from negated `Finset.mem`.

### `private lemma fdBoundaryFun_deriv_continuousAt_off`
- **Type**: `(H : ℝ) (t : ℝ) (_ht : t ∈ Ioo 0 1) (htp : t ∉ fdBoundaryPartition) : ContinuousAt (deriv (fdBoundaryFun H)) t`
- **What**: The derivative of `fdBoundaryFun H` is continuous at every `t ∈ (0,1) \ partition`.
- **How**: Same `push Not at htp` + four-way `by_cases` structure as `fdBoundaryFun_differentiableAt_off`. Each branch uses `continuousAt_congr (fdBoundaryFun_eventuallyEq_segi …).deriv` to transfer continuity of `deriv (segiFun)` (obtained from `(segiFun_contDiff …).continuous_deriv le_top |>.continuousAt`) along the eventually-equal derivatives.
- **Hypotheses**: `t ∈ Ioo 0 1`, `t ∉ fdBoundaryPartition`.
- **Uses from project**: `fdBoundaryPartition`; all five segment `_contDiff` and eventually-equal lemmas (this file).
- **Used by**: `fdBoundaryPath_deriv_continuousAt_off`.
- **Visibility**: `private`.
- **Lines**: 205-232.
- **Notes**: Proof ≈28 lines; structurally parallel to differentiability lemma.

### `private lemma fdBoundaryPath_differentiableAt_off`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ∈ Ioo 0 1) (htp : t ∉ fdBoundaryPartition) : DifferentiableAt ℝ (fdBoundaryPath H).extend t`
- **What**: `(fdBoundaryPath H).extend` is differentiable at every `t ∈ (0,1)` off the partition.
- **How**: `(fdBoundaryFun_differentiableAt_off H t ht htp).congr_of_eventuallyEq (fdBoundaryPath_extend_eventuallyEq H t ht)`.
- **Hypotheses**: `t ∈ Ioo 0 1`, `t ∉ fdBoundaryPartition`.
- **Uses from project**: `fdBoundaryPath`, `fdBoundaryPartition`; `fdBoundaryFun_differentiableAt_off`, `fdBoundaryPath_extend_eventuallyEq` (this file).
- **Used by**: `fdBoundaryPC1Path`.
- **Visibility**: `private`.
- **Lines**: 236-240.
- **Notes**: Transfers the `fdBoundaryFun` result to `Path.extend` via the eventually-equal relation.

### `private lemma fdBoundaryPath_deriv_continuousAt_off`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ∈ Ioo 0 1) (htp : t ∉ fdBoundaryPartition) : ContinuousAt (deriv (fdBoundaryPath H).extend) t`
- **What**: Derivative of `(fdBoundaryPath H).extend` is continuous on `(0,1)` off the partition.
- **How**: `(continuousAt_congr (fdBoundaryPath_extend_eventuallyEq H t ht).deriv).mpr (fdBoundaryFun_deriv_continuousAt_off H t ht htp)`.
- **Hypotheses**: `t ∈ Ioo 0 1`, `t ∉ fdBoundaryPartition`.
- **Uses from project**: `fdBoundaryPath`, `fdBoundaryPartition`; `fdBoundaryPath_extend_eventuallyEq`, `fdBoundaryFun_deriv_continuousAt_off` (this file).
- **Used by**: `fdBoundaryPC1Path`.
- **Visibility**: `private`.
- **Lines**: 242-246.
- **Notes**: Same transfer pattern as the differentiability lemma.

### `def fdBoundaryPC1Path`
- **Type**: `(H : ℝ) (_hH : H > Real.sqrt 3 / 2) : PiecewiseC1Path (fdStart H) (fdStart H)`
- **What**: The fundamental-domain boundary packaged as a closed `PiecewiseC1Path` with partition `fdBoundaryPartition`.
- **How**: Structure literal — `toPath := fdBoundaryPath H`, `partition := fdBoundaryPartition`, `partition_subset := fdBoundaryPartition_subset_Ioo`, `differentiable_off := fdBoundaryPath_differentiableAt_off H`, `deriv_continuous_off := fdBoundaryPath_deriv_continuousAt_off H`.
- **Hypotheses**: `H > √3/2` (placeholder underscore, ensures FD non-degeneracy).
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `fdBoundaryPath`, `fdBoundaryPartition`, `fdBoundaryPartition_subset_Ioo`; `fdBoundaryPath_differentiableAt_off`, `fdBoundaryPath_deriv_continuousAt_off` (this file).
- **Used by**: `fdBoundaryPC1Path_eq`; downstream FD boundary clients.
- **Visibility**: public.
- **Lines**: 251-257.
- **Notes**: Main public construction of the file.

### `theorem fdBoundaryPC1Path_eq`
- **Type**: `(H : ℝ) (hH : H > Real.sqrt 3 / 2) (t : ℝ) (ht : t ∈ Icc 0 1) : (fdBoundaryPC1Path H hH).toPath.extend t = fdBoundaryFun H t`
- **What**: The packaged `PiecewiseC1Path` agrees with `fdBoundaryFun H` pointwise on `[0,1]`.
- **How**: Direct delegation to `fdBoundaryPath_extend_eq H t ht`.
- **Hypotheses**: `H > √3/2`, `t ∈ Icc 0 1`.
- **Uses from project**: `fdBoundaryFun`; `fdBoundaryPC1Path`, `fdBoundaryPath_extend_eq` (this file).
- **Used by**: Downstream callers needing to identify path values with the explicit boundary function.
- **Visibility**: public.
- **Lines**: 260-263.
- **Notes**: Public bridge from the structured `PiecewiseC1Path` to the explicit piecewise formula.

## File Summary

- **Total decls**: 22 (5 private defs, 15 private lemmas, 1 public def, 1 public theorem).
- **Key API** (used 3+ in this file): each `segiFun` is used by 3 lemmas (own diff, own contDiff, own eventuallyEq); each eventually-equal lemma feeds 2 callers; `fdBoundaryPath_extend_eq` (used by `fdBoundaryPath_extend_eventuallyEq` and `fdBoundaryPC1Path_eq`); `fdBoundaryPath_extend_eventuallyEq` (used by both transfer lemmas).
- **Unused in file**: none — every private lemma feeds the next layer.
- **Sorries**: 0.
- **set_options**: none.
- **Proofs >30 lines**: none (largest are `fdBoundaryFun_differentiableAt_off` ≈24 lines and `fdBoundaryFun_deriv_continuousAt_off` ≈28 lines).
- **One-paragraph file purpose**: Constructs the fundamental-domain boundary contour `fdBoundaryPC1Path H` as a `PiecewiseC1Path (fdStart H) (fdStart H)`. The boundary is the standard 5-segment closed loop around the SL₂(ℤ) fundamental domain truncated at height `H > √3/2`: right vertical (seg1), right arc (seg2), left arc (seg3), left vertical (seg4), top horizontal (seg5), with partition points `{1/5, 2/5, 3/5, 4/5}`. The file proves differentiability and continuity of the derivative on each segment by writing each segment as a closed-form `ℝ → ℂ` function (`segiFun`), proving each is `ContDiff ℝ ⊤`, then transferring via `=ᶠ[𝓝 t]` equalities between `fdBoundaryFun H` and the appropriate segment function. A final `Path.extend` transfer step packages everything into the public `fdBoundaryPC1Path` definition plus the agreement theorem `fdBoundaryPC1Path_eq` between the path and the explicit piecewise formula.
