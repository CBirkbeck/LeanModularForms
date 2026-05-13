# Inventory: Boundary/Smooth.lean

File: `LeanModularForms/ForMathlib/ValenceFormula/Boundary/Smooth.lean` (951 lines, 50 declarations).

Imports: `Boundary.Bounds`.

Top-level `noncomputable section` (lines 25–951).

---

### `private instance : NormSMulClass ℝ ℂ`
- **Type**: `NormSMulClass ℝ ℂ`
- **What**: Instance: ℝ-scalar mult on ℂ is norm-multiplicative.
- **How**: `NormedSpace.toNormSMulClass`.
- **Hypotheses**: none.
- **Uses from project**: [] (only mathlib).
- **Used by**: unused in file (provides instance for `fun_prop`/automation).
- **Visibility**: private (instance)
- **Lines**: 27
- **Notes**: none.

### `private instance : IsBoundedSMul ℝ ℂ`
- **Type**: `IsBoundedSMul ℝ ℂ`
- **What**: Instance: ℝ-scalar mult on ℂ is bounded.
- **How**: `NormSMulClass.toIsBoundedSMul`.
- **Hypotheses**: none.
- **Uses from project**: [] (only mathlib).
- **Used by**: unused in file (provides instance).
- **Visibility**: private (instance)
- **Lines**: 28
- **Notes**: none.

### `private instance : ContinuousSMul ℝ ℂ`
- **Type**: `ContinuousSMul ℝ ℂ`
- **What**: Instance: ℝ-scalar mult on ℂ is continuous.
- **How**: `IsBoundedSMul.continuousSMul`.
- **Hypotheses**: none.
- **Uses from project**: [] (only mathlib).
- **Used by**: unused in file (provides instance).
- **Visibility**: private (instance)
- **Lines**: 29
- **Notes**: none.

### `private lemma arc_hasDerivAt`
- **Type**: `(s : ℝ) → HasDerivAt (fun s' : ℝ => exp ((↑Real.pi * (↑s' + 1) / 6) * I)) (exp ((↑Real.pi * (↑s + 1) / 6) * I) * (↑Real.pi / 6 * I)) s`
- **What**: The arc parameterization `exp(iπ(s+1)/6)` has the expected derivative.
- **How**: Identifies the arc with `ArcCalculus.unitArc (π/3) (2π/3) 1 3` and applies `ArcCalculus.unitArc_hasDerivAt`; reconciles via `funext`, `push_cast`, `ring_nf`.
- **Hypotheses**: none.
- **Uses from project**: `ArcCalculus.unitArc`, `ArcCalculus.unitArc_hasDerivAt`.
- **Used by**: `fdBoundary_H_differentiableAt_off_partition`, `fdBoundary_H_deriv_ne_zero_off_fullPartition`, `fdBoundary_H_deriv_continuousAt_off_fullPartition`, `arc_tendsto_left`, `arc_tendsto_right`, `fdBoundary_H_not_differentiableAt_3`, `fdBoundary_H_not_differentiableAt_1`, `fdBoundary_H_hasDerivAt_arc`, `fdBoundary_H_deriv_continuousOn_Ioo_13`.
- **Visibility**: private
- **Lines**: 32-48
- **Notes**: >10 lines.

### `private lemma fdBoundary_H_eq_arc_near`
- **Type**: `{H : ℝ} {s : ℝ} (hs1 : 1 < s) (hs3 : s < 3) → fdBoundary_H H =ᶠ[𝓝 s] fun s' => exp ((↑Real.pi * (↑s' + 1) / 6) * I)`
- **What**: Locally around any interior point of `(1, 3)`, the boundary equals the arc.
- **How**: `filter_upwards [Ioi_mem_nhds hs1, Iio_mem_nhds hs3]`; unfold `fdBoundary_H`; case-split on the `≤ 2` and `≤ 3` branches, both reduce to `congr 1; ring`.
- **Hypotheses**: `1 < s < 3`.
- **Uses from project**: `fdBoundary_H`.
- **Used by**: `fdBoundary_H_differentiableAt_off_partition`, `fdBoundary_H_deriv_ne_zero_off_fullPartition`, `fdBoundary_H_deriv_continuousAt_off_fullPartition`, `arc_tendsto_left`, `arc_tendsto_right`, `fdBoundary_H_hasDerivAt_arc`, `fdBoundary_H_deriv_continuousOn_Ioo_13`.
- **Visibility**: private
- **Lines**: 50-64
- **Notes**: none.

### `private lemma arc_deriv_continuous`
- **Type**: `Continuous (fun s : ℝ => exp ((↑Real.pi * (↑s + 1) / 6) * I) * (↑Real.pi / 6 * I))`
- **What**: The arc's derivative function is continuous.
- **How**: Composition: `Complex.continuous_exp` on a continuous polynomial in `s`, times constant.
- **Hypotheses**: none.
- **Uses from project**: [] (only mathlib).
- **Used by**: `fdBoundary_H_deriv_continuousAt_off_fullPartition`, `arc_tendsto_left`, `arc_tendsto_right`, `fdBoundary_H_deriv_continuousOn_Ioo_13`.
- **Visibility**: private
- **Lines**: 66-73
- **Notes**: none.

### `private lemma arc_limit_ne_zero`
- **Type**: `(c : ℝ) → exp ((↑Real.pi * (↑c + 1) / 6) * I) * (↑Real.pi / 6 * I) ≠ 0`
- **What**: The arc derivative limit is non-zero at every point.
- **How**: `mul_ne_zero` on `exp_ne_zero`, `div_ne_zero` (π ≠ 0 since `π > 0`), and `I_ne_zero`.
- **Hypotheses**: none.
- **Uses from project**: [] (only mathlib).
- **Used by**: `fdBoundary_H_deriv_ne_zero_off_fullPartition`, `fdBoundary_H_left_deriv_limit`, `fdBoundary_H_right_deriv_limit`.
- **Visibility**: private
- **Lines**: 75-80
- **Notes**: none.

### `lemma fdBoundary_H_differentiableAt_off_partition`
- **Type**: `(H : ℝ) (t : ℝ) (htp : t ∉ fdBoundary_H_partition) → DifferentiableAt ℝ (fdBoundary_H H) t`
- **What**: Off the smaller partition `{1, 3, 4}`, the boundary is differentiable. (39 lines)
- **How**: Case-split on `t < 1`, `1 < t < 3`, `3 < t < 4`, `t > 4`; in each case display a local representation via `Filter.EventuallyEq`, and assemble differentiability from `ofRealCLM` composed with constants (`DifferentiableAt.add`, `DifferentiableAt.sub`, `DifferentiableAt.mul`); arc branch uses `arc_hasDerivAt` and `fdBoundary_H_eq_arc_near`.
- **Hypotheses**: `t ∉ fdBoundary_H_partition`.
- **Uses from project**: `fdBoundary_H_partition`, `fdBoundary_H`, `arc_hasDerivAt`, `fdBoundary_H_eq_arc_near`.
- **Used by**: `fdBoundary_HCurve` (smooth_off_partition), `fdBoundary_differentiableAt_off_partition`.
- **Visibility**: public
- **Lines**: 82-120
- **Notes**: >30 lines.

### `lemma fdBoundary_H_hasDerivAt_seg1'`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ∈ Ioo 0 1) → HasDerivAt (fdBoundary_H H) (-(H - Real.sqrt 3 / 2) * I) t`
- **What**: On the open seg1 `t ∈ (0,1)`, the boundary has derivative `-(H-√3/2)·i`.
- **How**: Show `fdBoundary_H H =ᶠ[𝓝 t] s ↦ 1/2 + (H - s·(H - √3/2))·i`; assemble `HasDerivAt` of this affine function (`HasDerivAt.mul_const`, `HasDerivAt.sub`, `HasDerivAt.ofReal_comp`); transport via `congr_of_eventuallyEq`.
- **Hypotheses**: `t ∈ Ioo 0 1`.
- **Uses from project**: `fdBoundary_H`.
- **Used by**: `fdBoundary_H_deriv_ne_zero_off_fullPartition`, `fdBoundary_H_deriv_continuousAt_off_fullPartition`, `fdBoundary_H_left_deriv_limit`, `fdBoundary_H_right_deriv_limit`.
- **Visibility**: public
- **Lines**: 122-141
- **Notes**: >10 lines.

### `lemma fdBoundary_H_hasDerivAt_seg4'`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ∈ Ioo 3 4) → HasDerivAt (fdBoundary_H H) ((H - Real.sqrt 3 / 2) * I) t`
- **What**: On the open seg4 `(3,4)`, the boundary has derivative `(H-√3/2)·i`. (31 lines)
- **How**: Show `fdBoundary_H H =ᶠ[𝓝 t] s ↦ -1/2 + (√3/2 + (s - 3)(H - √3/2))·i`; assemble `HasDerivAt` via `HasDerivAt.ofReal_comp`, `HasDerivAt.sub`, `HasDerivAt.mul_const`, `HasDerivAt.add`; transport via `congr_of_eventuallyEq`.
- **Hypotheses**: `t ∈ Ioo 3 4`.
- **Uses from project**: `fdBoundary_H`.
- **Used by**: `fdBoundary_H_deriv_ne_zero_off_fullPartition`, `fdBoundary_H_deriv_continuousAt_off_fullPartition`, `fdBoundary_H_left_deriv_limit`, `fdBoundary_H_right_deriv_limit`, `fdBoundary_H_hasDerivAt_seg4`.
- **Visibility**: public
- **Lines**: 143-173
- **Notes**: >30 lines.

### `lemma fdBoundary_H_hasDerivAt_seg5'`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ∈ Ioo 4 5) → HasDerivAt (fdBoundary_H H) 1 t`
- **What**: On the open seg5 `(4,5)`, the boundary has derivative `1`.
- **How**: Show `fdBoundary_H H =ᶠ[𝓝 t] s ↦ (s - 9/2) + H·i`; differentiate this affine function (`HasDerivAt.ofReal_comp`, `HasDerivAt.sub`, `HasDerivAt.add (const)`).
- **Hypotheses**: `t ∈ Ioo 4 5`.
- **Uses from project**: `fdBoundary_H`.
- **Used by**: `fdBoundary_H_deriv_ne_zero_off_fullPartition`, `fdBoundary_H_deriv_continuousAt_off_fullPartition`, `fdBoundary_H_left_deriv_limit`, `fdBoundary_H_right_deriv_limit`, `fdBoundary_H_deriv_continuousOn_Ioo_45`.
- **Visibility**: public
- **Lines**: 175-187
- **Notes**: >10 lines.

### `lemma fdBoundary_H_deriv_ne_zero_off_fullPartition`
- **Type**: `(H : ℝ) (hH : √3/2 < H) (t : ℝ) (ht : t ∈ Icc 0 5) (htp : t ∉ fdBoundaryFullPartition) → deriv (fdBoundary_H H) t ≠ 0` (39 lines)
- **What**: Off the full partition `{0,1,2,3,4,5}`, the boundary derivative is non-zero (immersion condition).
- **How**: Case-split as in `fdBoundary_H_differentiableAt_off_partition`; in each branch compute `deriv` via the corresponding `hasDerivAt_seg*'`/`arc_hasDerivAt`, then show non-zero: vertical segments use `H > √3/2`, arc uses `arc_limit_ne_zero`, seg5 uses `one_ne_zero`. Closes vertical/horizontal cases by passing to `Complex.re`.
- **Hypotheses**: `√3/2 < H`, `t ∈ [0,5]`, `t` outside the full partition.
- **Uses from project**: `fdBoundaryFullPartition`, `fdBoundary_H_hasDerivAt_seg1'`, `arc_hasDerivAt`, `fdBoundary_H_eq_arc_near`, `arc_limit_ne_zero`, `fdBoundary_H_hasDerivAt_seg4'`, `fdBoundary_H_hasDerivAt_seg5'`.
- **Used by**: `fdBoundary_HImmersion` (deriv_ne_zero), `fdBoundary_deriv_ne_zero_off_partition`.
- **Visibility**: public
- **Lines**: 189-227
- **Notes**: >30 lines.

### `lemma fdBoundary_H_deriv_continuousAt_off_fullPartition`
- **Type**: `(H : ℝ) (t : ℝ) (ht : t ∈ Ioo 0 5) (htp : t ∉ fdBoundaryFullPartition) → ContinuousAt (deriv (fdBoundary_H H)) t` (33 lines)
- **What**: Off the full partition, the boundary's derivative is continuous.
- **How**: On vertical/horizontal segments, derivative is locally constant, so `ContinuousAt.congr continuousAt_const`. On the arc, use that `deriv` agrees locally with `arc_hasDerivAt`'s formula and conclude via `arc_deriv_continuous`.
- **Hypotheses**: `t ∈ Ioo 0 5`, `t ∉ fdBoundaryFullPartition`.
- **Uses from project**: `fdBoundaryFullPartition`, `fdBoundary_H_hasDerivAt_seg1'`, `fdBoundary_H_eq_arc_near`, `arc_hasDerivAt`, `arc_deriv_continuous`, `fdBoundary_H_hasDerivAt_seg4'`, `fdBoundary_H_hasDerivAt_seg5'`.
- **Used by**: `fdBoundary_HCurve` (deriv_continuous_off_partition), `fdBoundary_deriv_continuousAt_off_partition`, `fdBoundary_H_deriv_continuousOn_Ioo_01`, `fdBoundary_H_deriv_continuousOn_Ioo_34`, `fdBoundary_H_deriv_continuousOn_off_partition`.
- **Visibility**: public
- **Lines**: 229-261
- **Notes**: >30 lines.

### `private lemma tendsto_of_eventually_const_left`
- **Type**: `{c : ℂ} {p : ℝ} {f : ℝ → ℂ} {a : ℝ} (ha : a < p) (hf : ∀ s ∈ Ioo a p, f s = c) → Tendsto f (𝓝[<] p) (𝓝 c)`
- **What**: If `f` is eventually constant `c` on the left of `p`, then `f → c` as approached from the left.
- **How**: `tendsto_const_nhds.congr'` using `Ioo_mem_nhdsLT` to ensure the hypothesis applies.
- **Hypotheses**: `a < p`, `f` equals `c` on `Ioo a p`.
- **Uses from project**: [] (only mathlib).
- **Used by**: `fdBoundary_H_left_deriv_limit`.
- **Visibility**: private
- **Lines**: 263-268
- **Notes**: none.

### `private lemma tendsto_of_eventually_const_right`
- **Type**: `{c : ℂ} {p : ℝ} {f : ℝ → ℂ} {b : ℝ} (hb : p < b) (hf : ∀ s ∈ Ioo p b, f s = c) → Tendsto f (𝓝[>] p) (𝓝 c)`
- **What**: Mirror of `tendsto_of_eventually_const_left` for the right-hand approach.
- **How**: `tendsto_const_nhds.congr'` using `Ioo_mem_nhdsGT`.
- **Hypotheses**: `p < b`, `f` equals `c` on `Ioo p b`.
- **Uses from project**: [] (only mathlib).
- **Used by**: `fdBoundary_H_right_deriv_limit`.
- **Visibility**: private
- **Lines**: 270-275
- **Notes**: none.

### `private lemma seg_vertical_deriv_ne_zero`
- **Type**: `{H : ℝ} (hH : √3/2 < H) → (↑H - ↑(Real.sqrt 3) / 2) * I ≠ 0`
- **What**: The vertical segment derivative `(H - √3/2)·i` is non-zero.
- **How**: `mul_ne_zero _ I_ne_zero`; for the real factor, apply `re` and use `linarith` from `H > √3/2`.
- **Hypotheses**: `√3/2 < H`.
- **Uses from project**: [] (only mathlib).
- **Used by**: `fdBoundary_H_left_deriv_limit`, `fdBoundary_H_right_deriv_limit`.
- **Visibility**: private
- **Lines**: 277-283
- **Notes**: none.

### `private lemma arc_tendsto_left`
- **Type**: `{H : ℝ} (p : ℝ) (h1p : 1 < p) (hp3 : p ≤ 3) → Tendsto (deriv (fdBoundary_H H)) (𝓝[<] p) (𝓝 (exp ((↑π * (↑p + 1) / 6) * I) * (↑π / 6 * I)))`
- **What**: As `t ↗ p` from the left within the arc, the boundary derivative tends to the arc-formula value.
- **How**: Apply `arc_deriv_continuous.continuousAt.tendsto.mono_left` then `congr'` using `Ioo_mem_nhdsLT h1p`; on each `s ∈ Ioo (something) p`, derivative agrees with arc formula by `fdBoundary_H_eq_arc_near` + `arc_hasDerivAt`.
- **Hypotheses**: `1 < p ≤ 3`.
- **Uses from project**: `arc_deriv_continuous`, `fdBoundary_H_eq_arc_near`, `arc_hasDerivAt`.
- **Used by**: `fdBoundary_H_left_deriv_limit`.
- **Visibility**: private
- **Lines**: 285-294
- **Notes**: none.

### `private lemma arc_tendsto_right`
- **Type**: `{H : ℝ} (p : ℝ) (hp1 : 1 ≤ p) (hp3 : p < 3) → Tendsto (deriv (fdBoundary_H H)) (𝓝[>] p) (𝓝 (exp ((↑π * (↑p + 1) / 6) * I) * (↑π / 6 * I)))`
- **What**: Mirror of `arc_tendsto_left` for approach from the right.
- **How**: Same scheme as `arc_tendsto_left` with `Ioo_mem_nhdsGT hp3`.
- **Hypotheses**: `1 ≤ p < 3`.
- **Uses from project**: `arc_deriv_continuous`, `fdBoundary_H_eq_arc_near`, `arc_hasDerivAt`.
- **Used by**: `fdBoundary_H_right_deriv_limit`.
- **Visibility**: private
- **Lines**: 296-305
- **Notes**: none.

### `lemma fdBoundary_H_left_deriv_limit`
- **Type**: `(H : ℝ) (hH : √3/2 < H) (p : ℝ) (hp : p ∈ fdBoundaryFullPartition) (hp' : 0 < p) → ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv (fdBoundary_H H)) (𝓝[<] p) (𝓝 L)`
- **What**: One-sided limit (from the left) of the boundary derivative exists and is non-zero at every interior partition point.
- **How**: Case-split via `rcases hp with rfl | rfl | rfl | rfl | rfl | rfl`. `p = 0` is excluded by `hp'`. At `p = 1, 4, 5`, use `tendsto_of_eventually_const_left` with the corresponding `hasDerivAt_seg*'`. At `p = 2, 3`, use `arc_tendsto_left` with `arc_limit_ne_zero`.
- **Hypotheses**: `√3/2 < H`, `p ∈ {0,1,2,3,4,5}`, `0 < p`.
- **Uses from project**: `fdBoundaryFullPartition`, `seg_vertical_deriv_ne_zero`, `tendsto_of_eventually_const_left`, `fdBoundary_H_hasDerivAt_seg1'`, `arc_limit_ne_zero`, `arc_tendsto_left`, `fdBoundary_H_hasDerivAt_seg4'`, `fdBoundary_H_hasDerivAt_seg5'`.
- **Used by**: `fdBoundary_HImmersion` (left_deriv_limit), `fdBoundary_left_deriv_limit`.
- **Visibility**: public
- **Lines**: 307-325
- **Notes**: >10 lines.

### `lemma fdBoundary_H_hasDerivAt_seg1`
- **Type**: `(H : ℝ) {t : ℝ} (ht : t < 1) → HasDerivAt (fdBoundary_H H) (-(H - Real.sqrt 3 / 2) * I) t`
- **What**: Has-derivative form of `seg1'` for `t < 1` (handles `t ≤ 0` too).
- **How**: Same as `fdBoundary_H_hasDerivAt_seg1'` but using `Iio_mem_nhds ht` instead of `Ioo_mem_nhds`.
- **Hypotheses**: `t < 1`.
- **Uses from project**: `fdBoundary_H`.
- **Used by**: `fdBoundary_H_deriv_bound_ex`, `fdBoundary_H_deriv_continuousOn_off_partition`.
- **Visibility**: public
- **Lines**: 327-346
- **Notes**: >10 lines.

### `lemma fdBoundary_H_hasDerivAt_seg4`
- **Type**: `(H : ℝ) {t : ℝ} (h3 : 3 < t) (h4 : t < 4) → HasDerivAt (fdBoundary_H H) ((H - Real.sqrt 3 / 2) * I) t`
- **What**: Has-derivative on `(3,4)`, equivalent restatement of `seg4'`.
- **How**: `fdBoundary_H_hasDerivAt_seg4' H t ⟨h3, h4⟩`.
- **Hypotheses**: `3 < t < 4`.
- **Uses from project**: `fdBoundary_H_hasDerivAt_seg4'`.
- **Used by**: `fdBoundary_H_deriv_bound_ex`.
- **Visibility**: public
- **Lines**: 348-350
- **Notes**: none.

### `lemma fdBoundary_H_hasDerivAt_seg5`
- **Type**: `(H : ℝ) {t : ℝ} (h4 : 4 < t) → HasDerivAt (fdBoundary_H H) 1 t`
- **What**: Has-derivative form of `seg5'` extended for `t ≥ 5` (here just `4 < t`).
- **How**: Show `fdBoundary_H H =ᶠ[𝓝 t] s ↦ (s - 9/2) + H·i`; assemble `HasDerivAt` from real comp and constant.
- **Hypotheses**: `4 < t`.
- **Uses from project**: `fdBoundary_H`.
- **Used by**: `fdBoundary_H_deriv_bound_ex`, `fdBoundary_H_deriv_continuousOn_off_partition`.
- **Visibility**: public
- **Lines**: 352-367
- **Notes**: >10 lines.

### `theorem continuous_fdBoundary_seg1_H`
- **Type**: `(H : ℝ) → Continuous (fdBoundary_seg1_H H)`
- **What**: The closed-form seg1 affine map is continuous.
- **How**: `unfold fdBoundary_seg1_H; fun_prop`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg1_H`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 369-372
- **Notes**: none.

### `theorem continuous_fdBoundary_seg4_H`
- **Type**: `(H : ℝ) → Continuous (fdBoundary_seg4_H H)`
- **What**: The closed-form seg4 affine map is continuous.
- **How**: `unfold fdBoundary_seg4_H; fun_prop`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg4_H`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 374-377
- **Notes**: none.

### `theorem continuous_fdBoundary_seg5_H`
- **Type**: `(H : ℝ) → Continuous (fdBoundary_seg5_H H)`
- **What**: The closed-form seg5 affine map is continuous.
- **How**: `unfold fdBoundary_seg5_H; fun_prop`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg5_H`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 379-382
- **Notes**: none.

### `lemma hasDerivAt_fdBoundary_seg1_H`
- **Type**: `(H t : ℝ) → HasDerivAt (fdBoundary_seg1_H H) (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t`
- **What**: Derivative of the closed-form seg1 affine parameterization.
- **How**: Rewrite `fdBoundary_seg1_H` as `s ↦ (1/2 + H·i) + s · (-(H-√3/2)·i)`; differentiate `((id).ofReal_comp.mul_const _).const_add` with `congr_deriv`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg1_H`.
- **Used by**: `fdBoundary_H_not_differentiableAt_1`.
- **Visibility**: public
- **Lines**: 384-396
- **Notes**: >10 lines.

### `lemma hasDerivAt_fdBoundary_seg4_H`
- **Type**: `(H t : ℝ) → HasDerivAt (fdBoundary_seg4_H H) ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t`
- **What**: Derivative of the closed-form seg4 affine parameterization.
- **How**: Rewrite as `s ↦ (-1/2 + (√3/2)·i) + (s-3) · ((H-√3/2)·i)`; use `(hasDerivAt_id.sub const).ofReal_comp.mul_const`, then `const_add` and `congr_deriv`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg4_H`.
- **Used by**: `fdBoundary_H_not_differentiableAt_4`, `fdBoundary_H_not_differentiableAt_3`.
- **Visibility**: public
- **Lines**: 398-414
- **Notes**: >10 lines.

### `lemma hasDerivAt_fdBoundary_seg5_H`
- **Type**: `(H t : ℝ) → HasDerivAt (fdBoundary_seg5_H H) 1 t`
- **What**: Derivative of the closed-form seg5 affine parameterization.
- **How**: Rewrite as `s ↦ ((-9/2) + H·i) + s · 1`; differentiate via `id.ofReal_comp.mul_const`, then `const_add`, `congr_deriv` closed by `norm_cast`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg5_H`.
- **Used by**: `fdBoundary_H_not_differentiableAt_4`.
- **Visibility**: public
- **Lines**: 416-425
- **Notes**: none.

### `private lemma seg4_eventuallyEq_left_4`
- **Type**: `(H : ℝ) → fdBoundary_seg4_H H =ᶠ[𝓝[≤] 4] fdBoundary_H H`
- **What**: Locally to the left of `t = 4`, the closed-form seg4 affine map matches `fdBoundary_H`.
- **How**: `Filter.eventuallyEq_iff_exists_mem` with set `Ioo 3 5 ∩ Iic 4`; at `t = 4` use `fdBoundary_H_at_four`, else use `fdBoundary_H_eq_seg4_H`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg4_H`, `fdBoundary_H_at_four`, `fdBoundary_H_eq_seg4_H`.
- **Used by**: `fdBoundary_H_not_differentiableAt_4`.
- **Visibility**: private
- **Lines**: 427-437
- **Notes**: none.

### `private lemma seg5_eventuallyEq_right_4`
- **Type**: `(H : ℝ) → fdBoundary_seg5_H H =ᶠ[𝓝[≥] 4] fdBoundary_H H`
- **What**: Locally to the right of `t = 4`, the closed-form seg5 affine map matches `fdBoundary_H`.
- **How**: Similar to `seg4_eventuallyEq_left_4`, using `fdBoundary_H_eq_seg5_H`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg5_H`, `fdBoundary_H_at_four`, `fdBoundary_H_eq_seg5_H`.
- **Used by**: `fdBoundary_H_not_differentiableAt_4`.
- **Visibility**: private
- **Lines**: 439-450
- **Notes**: none.

### `lemma fdBoundary_H_not_differentiableAt_4`
- **Type**: `{H : ℝ} (hH : √3/2 < H) → ¬DifferentiableAt ℝ (fdBoundary_H H) 4` (23 lines)
- **What**: The boundary has a corner at `t = 4`: not differentiable.
- **How**: Suppose differentiable; derive that left/right derivatives must agree. The left derivative (from seg4) is `(H-√3/2)·i` (via `seg4_eventuallyEq_left_4`, `hasDerivAt_fdBoundary_seg4_H`) while the right derivative (from seg5) is `1` (via `seg5_eventuallyEq_right_4`, `hasDerivAt_fdBoundary_seg5_H`); these have different imaginary parts (`H - √3/2 > 0` vs `0`), contradiction by `(uniqueDiffWithinAt_Iic ...).eq_deriv` + `(uniqueDiffWithinAt_Ici ...).eq_deriv` followed by `congr_arg Complex.im` and `linarith`.
- **Hypotheses**: `√3/2 < H`.
- **Uses from project**: `seg4_eventuallyEq_left_4`, `fdBoundary_seg4_H`, `fdBoundary_H_at_four`, `hasDerivAt_fdBoundary_seg4_H`, `seg5_eventuallyEq_right_4`, `fdBoundary_seg5_H`, `hasDerivAt_fdBoundary_seg5_H`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 452-473
- **Notes**: >10 lines.

### `private lemma arc_eventuallyEq_left_3`
- **Type**: `(H : ℝ) → (fun s => exp ((↑Real.pi * (↑s + 1) / 6) * I)) =ᶠ[𝓝[≤] 3] fdBoundary_H H`
- **What**: Locally to the left of `t = 3`, the arc parameterization matches `fdBoundary_H`.
- **How**: `Filter.eventuallyEq_iff_exists_mem` on `Ioo 2 4 ∩ Iic 3`; at `t = 3` reduce via `fdBoundary_H_at_three` and `fdBoundary_at_three`, otherwise use `fdBoundary_H_eq_arc_near`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_H_at_three`, `fdBoundary_at_three`, `fdBoundary`, `fdBoundary_H_eq_arc_near`.
- **Used by**: `fdBoundary_H_not_differentiableAt_3`.
- **Visibility**: private
- **Lines**: 475-491
- **Notes**: >10 lines.

### `private lemma seg4_eventuallyEq_right_3`
- **Type**: `(H : ℝ) → fdBoundary_seg4_H H =ᶠ[𝓝[≥] 3] fdBoundary_H H`
- **What**: Locally to the right of `t = 3`, the seg4 closed form matches `fdBoundary_H`.
- **How**: `Filter.eventuallyEq_iff_exists_mem` on `Ioo 2 4 ∩ Ici 3`; at `t = 3` reduce via `fdBoundary_H_at_three`/`fdBoundary_at_three`/`ellipticPointRho`, otherwise use `fdBoundary_H_eq_seg4_H`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg4_H`, `fdBoundary_H_at_three`, `fdBoundary_at_three`, `ellipticPointRho`, `ellipticPointRho'`, `fdBoundary_H_eq_seg4_H`.
- **Used by**: `fdBoundary_H_not_differentiableAt_3`.
- **Visibility**: private
- **Lines**: 493-507
- **Notes**: >10 lines.

### `lemma fdBoundary_H_not_differentiableAt_3`
- **Type**: `{H : ℝ} (_hH : √3/2 < H) → ¬DifferentiableAt ℝ (fdBoundary_H H) 3` (53 lines)
- **What**: The boundary has a corner at `t = 3` (the elliptic point ρ): not differentiable.
- **How**: Suppose differentiable. Left derivative from the arc is `(π/6)·i · exp((π·4/6)·i)` (via `arc_eventuallyEq_left_3` + `arc_hasDerivAt`); right derivative from seg4 is `(H - √3/2)·i` (via `seg4_eventuallyEq_right_3` + `hasDerivAt_fdBoundary_seg4_H`). Comparing real parts: LHS `= -(π/6)·sin(2π/3) = -(π·√3)/12 < 0` while RHS `= 0`, contradiction via `nlinarith [Real.pi_pos, Real.sqrt_pos]`. Uses `Real.sin_pi_sub` and `Real.sin_pi_div_three`.
- **Hypotheses**: `√3/2 < H` (unused, hence `_hH`).
- **Uses from project**: `fdBoundary_H_at_three`, `fdBoundary_at_three`, `arc_eventuallyEq_left_3`, `arc_hasDerivAt`, `fdBoundary_seg4_H`, `ellipticPointRho`, `ellipticPointRho'`, `seg4_eventuallyEq_right_3`, `hasDerivAt_fdBoundary_seg4_H`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 509-561
- **Notes**: >30 lines.

### `private lemma seg1_eventuallyEq_left_1`
- **Type**: `(H : ℝ) → fdBoundary_seg1_H H =ᶠ[𝓝[≤] 1] fdBoundary_H H`
- **What**: Locally to the left of `t = 1`, the seg1 closed form matches `fdBoundary_H`.
- **How**: `Filter.eventuallyEq_iff_exists_mem` with `Ioo 0 2 ∩ Iic 1`; use `fdBoundary_H_eq_seg1_H`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_seg1_H`, `fdBoundary_H_eq_seg1_H`.
- **Used by**: `fdBoundary_H_not_differentiableAt_1`.
- **Visibility**: private
- **Lines**: 563-569
- **Notes**: none.

### `private lemma arc_eventuallyEq_right_1`
- **Type**: `(H : ℝ) → (fun s => exp ((↑Real.pi * (↑s + 1) / 6) * I)) =ᶠ[𝓝[≥] 1] fdBoundary_H H`
- **What**: Locally to the right of `t = 1`, the arc parameterization matches `fdBoundary_H`.
- **How**: `Filter.eventuallyEq_iff_exists_mem` with `Ioo 0 2 ∩ Ici 1`; at `t = 1`, unfold `fdBoundary_H` (`s ≤ 1` branch) and `exp_mul_I`, then `Real.cos_pi_div_three`, `Real.sin_pi_div_three`; else use `fdBoundary_H_eq_arc_near`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_eq_arc_near`.
- **Used by**: `fdBoundary_H_not_differentiableAt_1`.
- **Visibility**: private
- **Lines**: 571-587
- **Notes**: >10 lines.

### `lemma fdBoundary_H_not_differentiableAt_1`
- **Type**: `{H : ℝ} (_hH : √3/2 < H) → ¬DifferentiableAt ℝ (fdBoundary_H H) 1` (49 lines)
- **What**: The boundary has a corner at `t = 1` (the elliptic point ρ+1): not differentiable.
- **How**: Analogous to `fdBoundary_H_not_differentiableAt_3`. Left derivative from seg1 is `-(H-√3/2)·i`; right derivative from arc is `(π/6)·i · exp((π·2/6)·i)`. Real parts: LHS = 0, RHS = `-(π/6) · sin(π/3) = -(π·√3)/12 < 0`; contradiction by `nlinarith`.
- **Hypotheses**: `√3/2 < H` (unused).
- **Uses from project**: `fdBoundary_seg1_H`, `fdBoundary_H_eq_seg1_H`, `fdBoundary_H`, `seg1_eventuallyEq_left_1`, `hasDerivAt_fdBoundary_seg1_H`, `arc_eventuallyEq_right_1`, `arc_hasDerivAt`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 589-637
- **Notes**: >30 lines.

### `lemma fdBoundary_H_right_deriv_limit`
- **Type**: `(H : ℝ) (hH : √3/2 < H) (p : ℝ) (hp : p ∈ fdBoundaryFullPartition) (hp' : p < 5) → ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv (fdBoundary_H H)) (𝓝[>] p) (𝓝 L)`
- **What**: Mirror of `fdBoundary_H_left_deriv_limit` for the right-hand approach.
- **How**: `rcases hp` over the six partition points. `p = 5` excluded by `hp'`. At `p = 0, 3, 4`, use `tendsto_of_eventually_const_right` with vertical/horizontal seg derivatives. At `p = 1, 2`, use `arc_tendsto_right` with `arc_limit_ne_zero`.
- **Hypotheses**: `√3/2 < H`, `p ∈ {0,1,2,3,4,5}`, `p < 5`.
- **Uses from project**: `fdBoundaryFullPartition`, `seg_vertical_deriv_ne_zero`, `tendsto_of_eventually_const_right`, `fdBoundary_H_hasDerivAt_seg1'`, `arc_limit_ne_zero`, `arc_tendsto_right`, `fdBoundary_H_hasDerivAt_seg4'`, `fdBoundary_H_hasDerivAt_seg5'`.
- **Used by**: `fdBoundary_HImmersion` (right_deriv_limit), `fdBoundary_right_deriv_limit`.
- **Visibility**: public
- **Lines**: 639-657
- **Notes**: >10 lines.

### `noncomputable def fdBoundary_HCurve`
- **Type**: `(H : ℝ) → PiecewiseC1Curve`
- **What**: Packages `fdBoundary_H H` as a `PiecewiseC1Curve` on `[0, 5]` with the six-point partition `{0,1,2,3,4,5}`. (29 lines)
- **How**: Anonymous-constructor definition: sets `toFun := fdBoundary_H H`, `a := 0`, `b := 5`, `partition := fdBoundaryFullPartition`; each obligation discharged by referring to existing lemmas: `partition_subset` via `rcases` over the six points; `endpoints_in_partition` by `simp`; `continuous_toFun` via `fdBoundary_H_continuous.continuousOn`; `smooth_off_partition` reduces full-partition exclusion to small-partition exclusion and invokes `fdBoundary_H_differentiableAt_off_partition`; `deriv_continuous_off_partition` invokes `fdBoundary_H_deriv_continuousAt_off_fullPartition`.
- **Hypotheses**: none.
- **Uses from project**: `PiecewiseC1Curve`, `fdBoundary_H`, `fdBoundaryFullPartition`, `fdBoundary_H_partition`, `fdBoundary_H_continuous`, `fdBoundary_H_differentiableAt_off_partition`, `fdBoundary_H_deriv_continuousAt_off_fullPartition`.
- **Used by**: `fdBoundary_HImmersion`, `fdBoundary_HCurve_closed`.
- **Visibility**: public
- **Lines**: 659-687
- **Notes**: >10 lines (structural definition).

### `noncomputable def fdBoundary_HImmersion`
- **Type**: `(H : ℝ) (hH : √3/2 < H) → PiecewiseC1Immersion`
- **What**: Promotes `fdBoundary_HCurve H` to a `PiecewiseC1Immersion` using the non-vanishing derivative and one-sided derivative limits.
- **How**: Inherit `toPiecewiseC1Curve := fdBoundary_HCurve H`; populate `deriv_ne_zero` via `fdBoundary_H_deriv_ne_zero_off_fullPartition`; `left_deriv_limit` and `right_deriv_limit` via the corresponding lemmas.
- **Hypotheses**: `√3/2 < H`.
- **Uses from project**: `PiecewiseC1Immersion`, `fdBoundary_HCurve`, `fdBoundary_H_deriv_ne_zero_off_fullPartition`, `fdBoundary_H_left_deriv_limit`, `fdBoundary_H_right_deriv_limit`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 689-702
- **Notes**: >10 lines (structural definition).

### `lemma fdBoundary_HCurve_closed`
- **Type**: `(H : ℝ) → (fdBoundary_HCurve H).IsClosed`
- **What**: The H-curve is closed: `γ(0) = γ(5)`.
- **How**: Unfold `IsClosed` to `fdBoundary_H H 0 = fdBoundary_H H 5`; apply `fdBoundary_H_closed`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_HCurve`, `fdBoundary_H`, `fdBoundary_H_closed`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 704-707
- **Notes**: none.

### `lemma fdBoundary_differentiableAt_off_partition`
- **Type**: `(t : ℝ) (htp : t ∉ fdPartition) → DifferentiableAt ℝ fdBoundary t`
- **What**: Off the standard partition `fdPartition`, `fdBoundary` (at the fixed height `heightCutoff`) is differentiable.
- **How**: Rewrite `fdBoundary = fdBoundary_H heightCutoff` via `fdBoundary_eq_fdBoundary_H`, then invoke `fdBoundary_H_differentiableAt_off_partition` after upgrading `t ∉ fdPartition` to `t ∉ fdBoundary_H_partition`.
- **Hypotheses**: `t ∉ fdPartition`.
- **Uses from project**: `fdPartition`, `fdBoundary`, `fdBoundary_eq_fdBoundary_H`, `heightCutoff`, `fdBoundary_H_partition`, `fdBoundary_H_differentiableAt_off_partition`.
- **Used by**: `fdBoundaryCurve` (smooth_off_partition).
- **Visibility**: public
- **Lines**: 709-716
- **Notes**: none.

### `lemma fdBoundary_deriv_continuousAt_off_partition`
- **Type**: `(t : ℝ) (ht : t ∈ Ioo 0 5) (htp : t ∉ fdBoundaryFullPartition) → ContinuousAt (deriv fdBoundary) t`
- **What**: Off the full partition, `deriv fdBoundary` is continuous at `t`.
- **How**: Same reduction technique as above via `fdBoundary_eq_fdBoundary_H` and `congr_arg deriv`, then `fdBoundary_H_deriv_continuousAt_off_fullPartition`.
- **Hypotheses**: `t ∈ Ioo 0 5`, `t ∉ fdBoundaryFullPartition`.
- **Uses from project**: `fdBoundary`, `fdBoundary_eq_fdBoundary_H`, `heightCutoff`, `fdBoundary_H_deriv_continuousAt_off_fullPartition`.
- **Used by**: `fdBoundaryCurve` (deriv_continuous_off_partition).
- **Visibility**: public
- **Lines**: 718-722
- **Notes**: none.

### `lemma fdBoundary_deriv_ne_zero_off_partition`
- **Type**: `(t : ℝ) (ht : t ∈ Icc 0 5) (htp : t ∉ fdBoundaryFullPartition) → deriv fdBoundary t ≠ 0`
- **What**: Off the full partition, `deriv fdBoundary` is non-zero.
- **How**: Reduce via `fdBoundary_eq_fdBoundary_H`, then `fdBoundary_H_deriv_ne_zero_off_fullPartition` with `sqrt3_div2_lt_heightCutoff`.
- **Hypotheses**: `t ∈ Icc 0 5`, `t ∉ fdBoundaryFullPartition`.
- **Uses from project**: `fdBoundary`, `fdBoundary_eq_fdBoundary_H`, `heightCutoff`, `sqrt3_div2_lt_heightCutoff`, `fdBoundary_H_deriv_ne_zero_off_fullPartition`.
- **Used by**: `fdBoundaryImmersion` (deriv_ne_zero).
- **Visibility**: public
- **Lines**: 724-729
- **Notes**: none.

### `lemma fdBoundary_left_deriv_limit`
- **Type**: `(p : ℝ) (hp : p ∈ fdBoundaryFullPartition) (hp' : 0 < p) → ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv fdBoundary) (𝓝[<] p) (𝓝 L)`
- **What**: One-sided left-derivative limit of `fdBoundary` at partition points.
- **How**: Reduce via `fdBoundary_eq_fdBoundary_H`, then `fdBoundary_H_left_deriv_limit`.
- **Hypotheses**: `p ∈ fdBoundaryFullPartition`, `0 < p`.
- **Uses from project**: `fdBoundary`, `fdBoundary_eq_fdBoundary_H`, `heightCutoff`, `sqrt3_div2_lt_heightCutoff`, `fdBoundary_H_left_deriv_limit`.
- **Used by**: `fdBoundaryImmersion` (left_deriv_limit).
- **Visibility**: public
- **Lines**: 731-736
- **Notes**: none.

### `lemma fdBoundary_right_deriv_limit`
- **Type**: `(p : ℝ) (hp : p ∈ fdBoundaryFullPartition) (hp' : p < 5) → ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv fdBoundary) (𝓝[>] p) (𝓝 L)`
- **What**: One-sided right-derivative limit of `fdBoundary` at partition points.
- **How**: Reduce via `fdBoundary_eq_fdBoundary_H`, then `fdBoundary_H_right_deriv_limit`.
- **Hypotheses**: `p ∈ fdBoundaryFullPartition`, `p < 5`.
- **Uses from project**: `fdBoundary`, `fdBoundary_eq_fdBoundary_H`, `heightCutoff`, `sqrt3_div2_lt_heightCutoff`, `fdBoundary_H_right_deriv_limit`.
- **Used by**: `fdBoundaryImmersion` (right_deriv_limit).
- **Visibility**: public
- **Lines**: 738-743
- **Notes**: none.

### `noncomputable def fdBoundaryCurve`
- **Type**: `PiecewiseC1Curve`
- **What**: Packages `fdBoundary` (at the fixed height) as a `PiecewiseC1Curve`. (37 lines)
- **How**: Anonymous-constructor definition: `toFun := fdBoundary`, `a := 0`, `b := 5`, `partition := fdBoundaryFullPartition`. Obligations: `continuous_toFun` via `fdBoundary_continuous.continuousOn`; `smooth_off_partition` reduces to `fdBoundary_differentiableAt_off_partition` after promoting `t ∉ fdBoundaryFullPartition` to `t ∉ fdPartition`; `deriv_continuous_off_partition` via `fdBoundary_deriv_continuousAt_off_partition`.
- **Hypotheses**: none.
- **Uses from project**: `PiecewiseC1Curve`, `fdBoundary`, `fdBoundaryFullPartition`, `fdPartition`, `fdBoundary_continuous`, `fdBoundary_differentiableAt_off_partition`, `fdBoundary_deriv_continuousAt_off_partition`.
- **Used by**: `fdBoundaryImmersion`, `fdBoundaryImmersion_closed`.
- **Visibility**: public
- **Lines**: 745-779
- **Notes**: >30 lines.

### `noncomputable def fdBoundaryImmersion`
- **Type**: `PiecewiseC1Immersion`
- **What**: Promotes `fdBoundaryCurve` to a `PiecewiseC1Immersion`.
- **How**: `toPiecewiseC1Curve := fdBoundaryCurve`; obligations from `fdBoundary_deriv_ne_zero_off_partition`, `fdBoundary_left_deriv_limit`, `fdBoundary_right_deriv_limit`.
- **Hypotheses**: none.
- **Uses from project**: `PiecewiseC1Immersion`, `fdBoundaryCurve`, `fdBoundary_deriv_ne_zero_off_partition`, `fdBoundary_left_deriv_limit`, `fdBoundary_right_deriv_limit`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 781-793
- **Notes**: >10 lines (structural definition).

### `lemma fdBoundaryImmersion_closed`
- **Type**: `fdBoundaryCurve.IsClosed`
- **What**: The fixed-height boundary is closed: `fdBoundary 0 = fdBoundary 5`.
- **How**: Change goal and apply `fdBoundary_closed`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundaryCurve`, `fdBoundary`, `fdBoundary_closed`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 795-798
- **Notes**: none.

### `lemma fdBoundary_H_hasDerivAt_arc`
- **Type**: `(H : ℝ) {t : ℝ} (h1 : 1 < t) (h3 : t < 3) → HasDerivAt (fdBoundary_H H) (exp ((↑π * (↑t + 1) / 6) * I) * (↑π / 6 * I)) t`
- **What**: On the open arc `(1, 3)`, the boundary has the arc derivative.
- **How**: `(arc_hasDerivAt t).congr_of_eventuallyEq (fdBoundary_H_eq_arc_near h1 h3)`.
- **Hypotheses**: `1 < t < 3`.
- **Uses from project**: `arc_hasDerivAt`, `fdBoundary_H_eq_arc_near`.
- **Used by**: `fdBoundary_H_deriv_bound_ex`.
- **Visibility**: public
- **Lines**: 800-804
- **Notes**: none.

### `lemma fdBoundary_H_deriv_continuousOn_Ioo_01`
- **Type**: `(H : ℝ) → ContinuousOn (deriv (fdBoundary_H H)) (Ioo 0 1)`
- **What**: Derivative is continuous on the open seg1 interval.
- **How**: Pointwise: invoke `fdBoundary_H_deriv_continuousAt_off_fullPartition` with the explicit verification that the point lies outside the full partition (six `linarith` cases via `Finset.mem_*`).
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_H_deriv_continuousAt_off_fullPartition`, `fdBoundaryFullPartition`.
- **Used by**: `fdBoundary_H_deriv_continuousOn_off_partition`.
- **Visibility**: public
- **Lines**: 806-816
- **Notes**: >10 lines.

### `lemma fdBoundary_H_deriv_continuousOn_Ioo_13`
- **Type**: `(H : ℝ) → ContinuousOn (deriv (fdBoundary_H H)) (Ioo 1 3)`
- **What**: Derivative is continuous on the open arc interval.
- **How**: Locally `deriv (fdBoundary_H H) =ᶠ[𝓝 t]` the closed-form arc derivative (via `fdBoundary_H_eq_arc_near` + `arc_hasDerivAt`); combine `continuousAt_congr` and `arc_deriv_continuous.continuousAt`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_H_eq_arc_near`, `arc_hasDerivAt`, `arc_deriv_continuous`.
- **Used by**: `fdBoundary_H_deriv_continuousOn_off_partition`.
- **Visibility**: public
- **Lines**: 818-829
- **Notes**: >10 lines.

### `lemma fdBoundary_H_deriv_continuousOn_Ioo_34`
- **Type**: `(H : ℝ) → ContinuousOn (deriv (fdBoundary_H H)) (Ioo 3 4)`
- **What**: Derivative is continuous on the open seg4 interval.
- **How**: Pointwise via `fdBoundary_H_deriv_continuousAt_off_fullPartition`, analogous to `Ioo_01`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_H_deriv_continuousAt_off_fullPartition`, `fdBoundaryFullPartition`.
- **Used by**: `fdBoundary_H_deriv_continuousOn_off_partition`.
- **Visibility**: public
- **Lines**: 831-843
- **Notes**: >10 lines.

### `lemma fdBoundary_H_deriv_continuousOn_Ioo_45`
- **Type**: `(H : ℝ) → ContinuousOn (deriv (fdBoundary_H H)) (Ioo 4 5)`
- **What**: Derivative is continuous on the open seg5 interval.
- **How**: Locally `deriv (fdBoundary_H H) =ᶠ[𝓝 t] (fun _ => 1)` via `fdBoundary_H_hasDerivAt_seg5'`; continuity is then `continuousAt_const`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_H_hasDerivAt_seg5'`.
- **Used by**: `fdBoundary_H_deriv_continuousOn_off_partition`.
- **Visibility**: public
- **Lines**: 845-852
- **Notes**: none.

### `private lemma norm_cast_sub_eq`
- **Type**: `{H : ℝ} (hH : √3/2 < H) → ‖(↑H - ↑(Real.sqrt 3) / 2 : ℂ)‖ = H - Real.sqrt 3 / 2`
- **What**: Norm of the real complex number `H - √3/2` equals itself (it is positive).
- **How**: Show `(↑H - ↑√3 / 2 : ℂ) = ↑(H - √3/2)` via `push_cast`/`ring`, then `Complex.norm_real` + `Real.norm_of_nonneg`.
- **Hypotheses**: `√3/2 < H`.
- **Uses from project**: [] (only mathlib).
- **Used by**: `fdBoundary_H_deriv_bound_ex`.
- **Visibility**: private
- **Lines**: 854-859
- **Notes**: none.

### `lemma fdBoundary_H_deriv_bound_ex`
- **Type**: `{H : ℝ} (hH : √3/2 < H) → ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, t ∉ fdBoundary_H_partition → ‖deriv (fdBoundary_H H) t‖ ≤ M` (46 lines)
- **What**: Existence of a uniform norm bound for the derivative off the partition.
- **How**: Choose `M := max (H - √3/2) 1`. Case-split on the segment containing `t` (seg1/arc/seg4/seg5); compute the derivative explicitly via `fdBoundary_H_hasDerivAt_seg1`/`fdBoundary_H_hasDerivAt_arc`/`fdBoundary_H_hasDerivAt_seg4`/`fdBoundary_H_hasDerivAt_seg5`, then take norm: vertical segments give `H - √3/2` (using `norm_cast_sub_eq`), arc gives `π/6 ≤ 1` (via `Real.pi_le_four`), seg5 gives `1`; all bounded by `max`.
- **Hypotheses**: `√3/2 < H`.
- **Uses from project**: `fdBoundary_H_partition`, `fdBoundary_H_hasDerivAt_seg1`, `fdBoundary_H_hasDerivAt_arc`, `fdBoundary_H_hasDerivAt_seg4`, `fdBoundary_H_hasDerivAt_seg5`, `norm_cast_sub_eq`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 861-905
- **Notes**: >30 lines.

### `lemma fdBoundary_H_deriv_continuousOn_off_partition`
- **Type**: `(H : ℝ) → ContinuousOn (deriv (fdBoundary_H H)) (Icc 0 5 \ ↑fdBoundary_H_partition)` (44 lines)
- **What**: Aggregate continuity statement: derivative is continuous on `[0,5]` minus the three corners `{1,3,4}`.
- **How**: Case-split on `t = 0`, `t = 5`, then `t < 1`, `1 < t < 3`, `3 < t < 4`, `4 < t < 5`; endpoints reduce to constant-derivative via `fdBoundary_H_hasDerivAt_seg1`/`seg5`, intermediate cases pull from `fdBoundary_H_deriv_continuousOn_Ioo_01/13/34/45` via `continuousAt` and `continuousWithinAt`.
- **Hypotheses**: none.
- **Uses from project**: `fdBoundary_H_partition`, `fdBoundary_H_hasDerivAt_seg1`, `fdBoundary_H_hasDerivAt_seg5`, `fdBoundary_H_deriv_continuousOn_Ioo_01`, `fdBoundary_H_deriv_continuousOn_Ioo_13`, `fdBoundary_H_deriv_continuousOn_Ioo_34`, `fdBoundary_H_deriv_continuousOn_Ioo_45`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 907-949
- **Notes**: >30 lines.

---

## File Summary

- **Total declarations**: 50 (3 anonymous private instances + 47 named lemmas/theorems/defs), spread across 951 lines.
- **Key public API**:
  - Differentiability/derivative on each segment: `fdBoundary_H_differentiableAt_off_partition`, `fdBoundary_H_hasDerivAt_seg1`/`seg1'`/`seg4`/`seg4'`/`seg5`/`seg5'`/`arc`.
  - Non-differentiability at corners: `fdBoundary_H_not_differentiableAt_1`/`_3`/`_4`.
  - Derivative is non-zero / continuous off the partition: `fdBoundary_H_deriv_ne_zero_off_fullPartition`, `fdBoundary_H_deriv_continuousAt_off_fullPartition`, `fdBoundary_H_deriv_continuousOn_Ioo_01/13/34/45`, `fdBoundary_H_deriv_continuousOn_off_partition`, `fdBoundary_H_deriv_bound_ex`.
  - One-sided derivative limits at corners: `fdBoundary_H_left_deriv_limit`, `fdBoundary_H_right_deriv_limit`.
  - Closed-form seg parameterizations: `continuous_fdBoundary_seg1_H`/`seg4_H`/`seg5_H`, `hasDerivAt_fdBoundary_seg1_H`/`seg4_H`/`seg5_H`.
  - Fixed-height counterparts (specializing `H := heightCutoff`): `fdBoundary_differentiableAt_off_partition`, `fdBoundary_deriv_continuousAt_off_partition`, `fdBoundary_deriv_ne_zero_off_partition`, `fdBoundary_left_deriv_limit`, `fdBoundary_right_deriv_limit`.
  - Packaged structures: `fdBoundary_HCurve`, `fdBoundary_HImmersion`, `fdBoundaryCurve`, `fdBoundaryImmersion`; closure: `fdBoundary_HCurve_closed`, `fdBoundaryImmersion_closed`.
- **Unused in file**: `continuous_fdBoundary_seg1_H`/`seg4_H`/`seg5_H`, `fdBoundary_H_not_differentiableAt_1`/`_3`/`_4`, `fdBoundary_HImmersion`, `fdBoundary_HCurve_closed`, `fdBoundaryImmersion`, `fdBoundaryImmersion_closed`, `fdBoundary_H_deriv_bound_ex`, `fdBoundary_H_deriv_continuousOn_off_partition` — all exported as the main public API. The three private instances are silent helpers.
- **Sorries**: none.
- **set_options**: none.
- **Long proofs (>30 lines)**: `fdBoundary_H_differentiableAt_off_partition` (~39), `fdBoundary_H_hasDerivAt_seg4'` (~31), `fdBoundary_H_deriv_ne_zero_off_fullPartition` (~39), `fdBoundary_H_deriv_continuousAt_off_fullPartition` (~33), `fdBoundary_H_not_differentiableAt_3` (~53), `fdBoundary_H_not_differentiableAt_1` (~49), `fdBoundaryCurve` (~37), `fdBoundary_H_deriv_bound_ex` (~46), `fdBoundary_H_deriv_continuousOn_off_partition` (~44).
- **Purpose**: This module establishes the analytic infrastructure for treating the closed contour `fdBoundary_H : [0, 5] → ℂ` of the standard fundamental domain of `SL(2, ℤ)` (at variable upper-cutoff height `H`, and at the fixed default `heightCutoff`) as a piecewise-C¹ immersion. It proves: pointwise differentiability with explicit derivative formulas on each of the four smooth pieces (left vertical, lower arc, right vertical, top horizontal); non-differentiability at the corners `t = 1, 3, 4`; non-vanishing and continuity of the derivative off the corner partition `{0,1,2,3,4,5}`; one-sided derivative limits at every corner (essential for an "immersion with corners"); a uniform norm bound on the derivative. The penultimate section bundles all this into the four `PiecewiseC1Curve`/`PiecewiseC1Immersion` objects (`fdBoundary_HCurve`, `fdBoundary_HImmersion`, `fdBoundaryCurve`, `fdBoundaryImmersion`) which form the structured input to the contour-integration machinery used downstream by the valence formula. The closed-form per-segment lemmas (`continuous_fdBoundary_seg*_H`, `hasDerivAt_fdBoundary_seg*_H`) make these closed forms first-class objects usable independently of the global piecewise definition.
