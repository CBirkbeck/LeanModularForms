# CrossingAnalysis.lean Inventory

### `def PwC1Immersion.crossingSet`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : E) : Set ℝ`
- **What**: The set of parameter values `t ∈ [0,1]` at which the path `γ` passes through `z₀`.
- **How**: Set-builder `{t ∈ Icc 0 1 | (γ : ℝ → E) t = z₀}`.
- **Hypotheses**: `γ : PwC1Immersion x y`, `z₀ : E`.
- **Uses from project**: `PwC1Immersion` (from `CurveUtilities`).
- **Used by**: `crossingSet_subset_Icc`, `crossingSet_isClosed`, `crossing_not_accPt`, `crossingSet_finite`.
- **Visibility**: public (`def`, in `namespace PwC1Immersion`).
- **Lines**: 49-50.
- **Notes**: Central object of the file.

### `theorem PwC1Immersion.crossingSet_subset_Icc`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : E) : γ.crossingSet z₀ ⊆ Icc 0 1`
- **What**: The crossing set is a subset of `[0,1]`.
- **How**: `fun _ ht => ht.1` — projects out the membership component of the set-builder.
- **Hypotheses**: none beyond the data.
- **Uses from project**: `crossingSet` (this file).
- **Used by**: `crossingSet_finite`.
- **Visibility**: public.
- **Lines**: 52-54.
- **Notes**: Trivial trivial sub-`[0,1]` containment.

### `theorem PwC1Immersion.crossingSet_isClosed`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : E) : _root_.IsClosed (γ.crossingSet z₀)`
- **What**: The crossing set is closed.
- **How**: Rewrites `γ.crossingSet z₀ = Icc 0 1 ∩ (γ : ℝ → E) ⁻¹' {z₀}` via `ext t; simp only [crossingSet, mem_sep_iff, mem_inter_iff, mem_preimage, mem_singleton_iff]`. Then closes by `isClosed_Icc.inter (isClosed_singleton.preimage γ.toPiecewiseC1Path.continuous)`.
- **Hypotheses**: none beyond the data.
- **Uses from project**: `crossingSet` (this file); `PwC1Immersion.toPiecewiseC1Path.continuous` (from `CurveUtilities`).
- **Used by**: `crossingSet_finite`.
- **Visibility**: public.
- **Lines**: 59-65.
- **Notes**: Standard closed-from-continuous-preimage argument.

### `private theorem eventually_not_in_partition_left`
- **Type**: `(γ : PwC1Immersion x y) (p : ℝ) : ∀ᶠ t in 𝓝[<] p, t ∉ γ.toPiecewiseC1Path.partition`
- **What**: From the left of any point `p`, points are eventually not in the partition.
- **How**: Defines `(↑partition \ {p} : Set ℝ)`; it is closed (finite, via `Finset.finite_toSet.subset diff_subset |>.isClosed`) and does not contain `p`. Hence its complement is an open neighborhood. Combines with `t < p` from `eventually_nhdsWithin_of_forall` and concludes by `(h1.and h2).mono` ruling out `t ∈ partition`.
- **Hypotheses**: none beyond the data.
- **Uses from project**: `PwC1Immersion`, `PiecewiseC1Path.partition` (from `CurveUtilities`).
- **Used by**: `crossing_isolated_left`.
- **Visibility**: `private`.
- **Lines**: 70-80.
- **Notes**: Localises "off partition" to one-sided neighborhoods around partition points.

### `private theorem eventually_not_in_partition_right`
- **Type**: `(γ : PwC1Immersion x y) (p : ℝ) : ∀ᶠ t in 𝓝[>] p, t ∉ γ.toPiecewiseC1Path.partition`
- **What**: From the right of any point `p`, points are eventually not in the partition.
- **How**: Same recipe as the left version using `(↑partition \ {p}).isClosed` and `eventually_nhdsWithin_of_forall fun t ht => ht` (for `p < t`).
- **Hypotheses**: none beyond the data.
- **Uses from project**: `PwC1Immersion`, `PiecewiseC1Path.partition`.
- **Used by**: `crossing_isolated_right`.
- **Visibility**: `private`.
- **Lines**: 83-93.
- **Notes**: Mirror of the left version.

### `private theorem Icc_subset_of_Ioo_subset`
- **Type**: `{q p : ℝ} (hqp : q < p) (h : Ioo q p ⊆ Ioo 0 1) : Icc q p ⊆ Icc 0 1`
- **What**: Promotes an open-interval subset relation to a closed-interval subset relation when the endpoints are distinct.
- **How**: Takes closures: `closure_mono h` plus `closure_Ioo (ne_of_lt hqp)` and `closure_Ioo (by norm_num : (0:ℝ) ≠ 1)`.
- **Hypotheses**: `q < p`.
- **Uses from project**: []
- **Used by**: `crossing_isolated_left`, `crossing_isolated_right`.
- **Visibility**: `private`.
- **Lines**: 96-99.
- **Notes**: Three-line topology utility.

### `theorem PwC1Immersion.crossing_isolated_smooth`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : E) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1) (hcross : (γ : ℝ → E) t₀ = z₀) (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) : ∀ᶠ t in 𝓝[≠] t₀, (γ : ℝ → E) t ≠ z₀`
- **What**: At a smooth crossing point, the crossing is isolated in the full punctured neighborhood.
- **How**: Rewrites the target via `← hcross`, then uses `(γ.toPiecewiseC1Path.differentiable_off t₀ ht₀ hsmooth).hasDerivAt.eventually_ne` against `γ.deriv_ne_zero t₀ ht₀ hsmooth`.
- **Hypotheses**: `t₀ ∈ Ioo 0 1`, `γ t₀ = z₀`, `t₀` off partition.
- **Uses from project**: `PwC1Immersion`, `PiecewiseC1Path.differentiable_off`, `PwC1Immersion.deriv_ne_zero` (from `CurveUtilities`).
- **Used by**: `crossing_isolated`.
- **Visibility**: public.
- **Lines**: 105-111.
- **Notes**: Pure-immersion case: nonzero derivative blocks return to the crossing value.

### `theorem PwC1Immersion.crossing_isolated_left`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : E) (p : ℝ) (hp_part : p ∈ γ.toPiecewiseC1Path.partition) (hp_pos : 0 < p) (hcross : (γ : ℝ → E) p = z₀) : ∀ᶠ t in 𝓝[<] p, (γ : ℝ → E) t ≠ z₀`
- **What**: At a partition point `p > 0`, the crossing is isolated from the left.
- **How**: Extracts left-derivative limit `(L, hL_ne, hL_tendsto) ← γ.left_deriv_limit p hp_part`. By `exists_dual_vector ℝ L (norm_ne_zero_iff.mpr hL_ne)` picks a dual `f` with `‖f‖ = 1` and `f L = ‖L‖ > 0`. Defines `h(t) := f (γ t - z₀)`, observes `h p = 0`. Combines `eventually_not_in_partition_left`, `Ioo 0 1`-membership of nearby points (from `hp_Ioo`, `Ioi_mem_nhds hp_pos`, and `eventually_nhdsWithin_of_forall`), and continuity of `f ∘ deriv γ` against `hL_tendsto` to get a window `(q, p)` on which `t ∉ partition`, `t ∈ Ioo 0 1`, and `f (deriv γ t) > 0`. Promotes `h` to `ContinuousOn (Icc q p)` via `f.continuous.comp_continuousOn ((γ.toPiecewiseC1Path.continuous.continuousOn.mono ...).sub continuousOn_const)`, and `0 < deriv h s` on `interior (Icc q p)` from `(f.hasFDerivAt.comp_hasDerivAt s h_sub).deriv ▸ hs_dpos`. Concludes by `strictMonoOn_of_deriv_pos`: `h t = 0 = h p` would force `h t < h p` strictly, contradicting `hh_mono`.
- **Hypotheses**: `p ∈ partition`, `0 < p`, `γ p = z₀`.
- **Uses from project**: `PwC1Immersion`, `PiecewiseC1Path.partition_subset`, `PiecewiseC1Path.differentiable_off`, `PiecewiseC1Path.continuous`, `PwC1Immersion.left_deriv_limit`; `eventually_not_in_partition_left`, `Icc_subset_of_Ioo_subset` (this file).
- **Used by**: `crossing_isolated`.
- **Visibility**: public.
- **Lines**: 117-162.
- **Notes**: Proof >30 lines (~46). Uses `exists_dual_vector`, MVT (`strictMonoOn_of_deriv_pos`), and the directional structure of the left derivative limit.

### `theorem PwC1Immersion.crossing_isolated_right`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : E) (p : ℝ) (hp_part : p ∈ γ.toPiecewiseC1Path.partition) (hp_lt_one : p < 1) (hcross : (γ : ℝ → E) p = z₀) : ∀ᶠ t in 𝓝[>] p, (γ : ℝ → E) t ≠ z₀`
- **What**: At a partition point `p < 1`, the crossing is isolated from the right.
- **How**: Mirror of `crossing_isolated_left`: extracts `γ.right_deriv_limit`, picks `f` via `exists_dual_vector`, defines `h(t) := f (γ t - z₀)`, combines `eventually_not_in_partition_right`, `Iio_mem_nhds hp_lt_one`, and right-tendsto of `f ∘ deriv γ` to find window `(p, r)`. Builds `ContinuousOn h (Icc p r)`, `0 < deriv h s` on `interior (Icc p r)` via `f.hasFDerivAt.comp_hasDerivAt`, and concludes with `strictMonoOn_of_deriv_pos`: `h t = 0 = h p` contradicts `h p < h t`.
- **Hypotheses**: `p ∈ partition`, `p < 1`, `γ p = z₀`.
- **Uses from project**: `PwC1Immersion`, `PiecewiseC1Path.partition_subset`, `PiecewiseC1Path.differentiable_off`, `PiecewiseC1Path.continuous`, `PwC1Immersion.right_deriv_limit`; `eventually_not_in_partition_right`, `Icc_subset_of_Ioo_subset` (this file).
- **Used by**: `crossing_isolated`.
- **Visibility**: public.
- **Lines**: 166-211.
- **Notes**: Proof >30 lines (~46). Structural mirror of `crossing_isolated_left`.

### `theorem PwC1Immersion.crossing_isolated`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : E) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1) (hcross : (γ : ℝ → E) t₀ = z₀) : ∀ᶠ t in 𝓝[≠] t₀, (γ : ℝ → E) t ≠ z₀ ∨ t ∉ Icc 0 1`
- **What**: Every crossing in `(0, 1)` is isolated (combining smooth-point and partition-point cases).
- **How**: `by_cases t₀ ∈ partition`. Partition case: rewrites the punctured neighborhood as `𝓝[<] t₀ ⊔ 𝓝[>] t₀` via `punctured_nhds_eq_nhdsWithin_sup_nhdsWithin` and `Filter.eventually_sup`, then combines `crossing_isolated_left` and `crossing_isolated_right`. Smooth case: applies `crossing_isolated_smooth`; the `Or.inl` injection drops the (always-false here) second disjunct.
- **Hypotheses**: `t₀ ∈ Ioo 0 1`, `γ t₀ = z₀`.
- **Uses from project**: `PwC1Immersion`, `PiecewiseC1Path.partition`; `crossing_isolated_smooth`, `crossing_isolated_left`, `crossing_isolated_right` (this file).
- **Used by**: `crossing_not_accPt`.
- **Visibility**: public.
- **Lines**: 217-224.
- **Notes**: The `Or` allows for a uniform statement absorbing the boundary case.

### `theorem PwC1Immersion.crossing_not_accPt`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : E) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1) (hcross : (γ : ℝ → E) t₀ = z₀) : ¬AccPt t₀ (𝓟 (γ.crossingSet z₀))`
- **What**: No point of the crossing set in `(0, 1)` is an accumulation point of the crossing set.
- **How**: `rw [accPt_iff_frequently_nhdsNE, Filter.not_frequently]`. Applies `crossing_isolated` and `.mono`: if `t` is in the crossing set and either `γ t ≠ z₀` or `t ∉ Icc 0 1`, contradiction via `ht_mem.1` (membership in `Icc 0 1`) or `ht_mem.2` (`γ t = z₀`).
- **Hypotheses**: `t₀ ∈ Ioo 0 1`, `γ t₀ = z₀`.
- **Uses from project**: `crossingSet`, `crossing_isolated` (this file).
- **Used by**: `crossingSet_finite`.
- **Visibility**: public.
- **Lines**: 229-235.
- **Notes**: Translates "isolated" into "not accumulating" in filter language.

### `theorem PwC1Immersion.crossingSet_finite`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : E) (h0 : (γ : ℝ → E) 0 ≠ z₀) (h1 : (γ : ℝ → E) 1 ≠ z₀) : Set.Finite (γ.crossingSet z₀)`
- **What**: **Proposition 2.2 (Hungerbühler–Wasem)**: the crossing set is finite, provided the endpoints avoid `z₀`.
- **How**: `by_contra hS_inf`; an infinite subset of compact `Icc 0 1` has an accumulation point (`(Set.not_finite.mp hS_inf).exists_accPt_of_subset_isCompact isCompact_Icc (crossingSet_subset_Icc γ z₀)`). The accumulation point `a` is in the (closed) crossing set: `(γ.crossingSet_isClosed z₀).closure_eq ▸ mem_closure_iff_clusterPt.mpr ha_acc.clusterPt`. Then `a ∈ Ioo 0 1` follows from `lt_of_le_of_ne ha_S.1.1 (Ne.symm (fun h => h0 (h ▸ ha_S.2)))` and the symmetric upper-end argument (using `h1`). Contradicts `crossing_not_accPt`.
- **Hypotheses**: endpoint avoidance `γ 0 ≠ z₀`, `γ 1 ≠ z₀`.
- **Uses from project**: `crossingSet`, `crossingSet_isClosed`, `crossingSet_subset_Icc`, `crossing_not_accPt` (this file).
- **Used by**: External downstream (winding number theory).
- **Visibility**: public.
- **Lines**: 241-252.
- **Notes**: Combines compactness, closedness, and the no-accumulation-point lemma — classical Bolzano-Weierstrass style argument.

## File Summary

- **Total decls**: 12 (1 def, 8 public theorems, 3 private theorems).
- **Key API** (used 3+ in this file): `crossingSet` (used by `crossingSet_subset_Icc`, `crossingSet_isClosed`, `crossing_not_accPt`, `crossingSet_finite` — 4 uses); `Icc_subset_of_Ioo_subset` (used by `crossing_isolated_left`, `crossing_isolated_right` — 2 uses, borderline).
- **Unused in file**: none — every private lemma is consumed downstream.
- **Sorries**: 0.
- **set_options**: none.
- **Proofs >30 lines**: `crossing_isolated_left` (~46 lines), `crossing_isolated_right` (~46 lines).
- **One-paragraph file purpose**: Proves Proposition 2.2 of Hungerbühler–Wasem: for any piecewise C¹ immersion `γ : [0,1] → E` (in a real normed space `E`) and any target point `z₀ ∈ E`, the crossing set `{t ∈ [0,1] | γ t = z₀}` is finite, provided the endpoints `γ 0, γ 1` avoid `z₀`. Establishes (a) closedness of the crossing set (preimage of singleton under continuous path), (b) isolation of crossings at smooth interior points (via nonzero derivative ⇒ `HasDerivAt.eventually_ne`), and (c) isolation at partition points (via one-sided derivative limits, Hahn-Banach `exists_dual_vector` to reduce to a real-valued function, and `strictMonoOn_of_deriv_pos`). The combined isolation result `crossing_isolated` is then dualised to "no accumulation point" via `accPt_iff_frequently_nhdsNE`, and finiteness follows from compactness of `[0,1]` plus the closed-isolated-set argument in `crossingSet_finite`. Endpoint avoidance is used to lift the accumulation point from `[0,1]` into `(0,1)`.
