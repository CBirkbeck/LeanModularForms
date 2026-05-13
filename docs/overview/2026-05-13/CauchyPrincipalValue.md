# CauchyPrincipalValue.lean Inventory

### `def cpvIntegrand`
- **Type**: `(f : ℂ → ℂ) (γ : ℝ → ℂ) (z₀ : ℂ) (ε : ℝ) (t : ℝ) : ℂ`
- **What**: The ε-cutoff integrand: equals `f(γ t) · γ'(t)` when `‖γ t - z₀‖ > ε`, and `0` otherwise.
- **How**: Definition by `if` test on `‖γ t - z₀‖ > ε`.
- **Hypotheses**: None (pure definition).
- **Uses from project**: []
- **Used by**: `cpvIntegrand_of_gt`, `cpvIntegrand_of_le`, `cpvIntegrand_nonneg_eps`, `HasCauchyPV`, `cauchyPV`, `HasCauchyPV.neg`, `HasCauchyPV.smul`, `hasCauchyPV_of_avoids`, `cpvIntegrand_eq_cpvIntegrandOn_singleton`
- **Visibility**: public
- **Lines**: 67-69
- **Notes**: None.

### `theorem cpvIntegrand_of_gt`
- **Type**: `{f γ z₀ ε t} (h : ε < ‖γ t - z₀‖) : cpvIntegrand f γ z₀ ε t = f (γ t) * deriv γ t`
- **What**: When the curve is far enough from `z₀`, the cutoff integrand equals the unmodified integrand.
- **How**: `simp` unfolds `cpvIntegrand` and reduces the `if` using the positive branch.
- **Hypotheses**: `ε < ‖γ t - z₀‖`.
- **Uses from project**: [`cpvIntegrand`]
- **Used by**: `hasCauchyPV_of_avoids`
- **Visibility**: public (`@[simp]`)
- **Lines**: 71-75
- **Notes**: None.

### `theorem cpvIntegrand_of_le`
- **Type**: `{f γ z₀ ε t} (h : ‖γ t - z₀‖ ≤ ε) : cpvIntegrand f γ z₀ ε t = 0`
- **What**: When `γ t` is within `ε` of `z₀`, the cutoff integrand vanishes.
- **How**: `simp` with the negative branch of the `if`.
- **Hypotheses**: `‖γ t - z₀‖ ≤ ε`.
- **Uses from project**: [`cpvIntegrand`]
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 77-81
- **Notes**: None.

### `theorem cpvIntegrand_nonneg_eps`
- **Type**: `{f γ z₀ ε₁ ε₂ t} (hε : ε₂ ≤ ε₁) (h : cpvIntegrand f γ z₀ ε₁ t ≠ 0) : cpvIntegrand f γ z₀ ε₂ t = cpvIntegrand f γ z₀ ε₁ t`
- **What**: Monotonicity: if the integrand is nonzero at `ε₁`, it equals the `ε₁`-version at any smaller `ε₂`.
- **How**: Case-splits on the `if` to extract `ε₁ < ‖γ t - z₀‖`, then propagates via `lt_of_le_of_lt`.
- **Hypotheses**: `ε₂ ≤ ε₁`, `cpvIntegrand f γ z₀ ε₁ t ≠ 0`.
- **Uses from project**: [`cpvIntegrand`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 83-89
- **Notes**: None.

### `def HasCauchyPV`
- **Type**: `(f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (z₀ : ℂ) (L : ℂ) : Prop`
- **What**: The Cauchy principal value of the contour integral exists and equals `L`, defined via `Tendsto` of the ε-cutoff integral as `ε → 0⁺`.
- **How**: `Tendsto (fun ε => ∫ t in 0..1, cpvIntegrand f γ.extend z₀ ε t) (𝓝[>] 0) (𝓝 L)`.
- **Hypotheses**: None (definition).
- **Uses from project**: [`cpvIntegrand`, `PiecewiseC1Path`]
- **Used by**: `cauchyPV`, `HasCauchyPV.cauchyPV_eq`, `HasCauchyPV.neg`, `HasCauchyPV.smul`, `hasCauchyPV_of_avoids`, `HasCauchyPV.unique`
- **Visibility**: public
- **Lines**: 97-99
- **Notes**: Primary API predicate.

### `def cauchyPV`
- **Type**: `(f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (z₀ : ℂ) : ℂ`
- **What**: The CPV value of `∮_γ f(z) dz` via `limUnder`; junk when the limit doesn't exist.
- **How**: `limUnder (𝓝[>] 0) (∫ t in 0..1, cpvIntegrand …)`.
- **Hypotheses**: None.
- **Uses from project**: [`cpvIntegrand`, `PiecewiseC1Path`]
- **Used by**: `HasCauchyPV.cauchyPV_eq`
- **Visibility**: public
- **Lines**: 103-105
- **Notes**: Secondary; use `HasCauchyPV` whenever possible.

### `theorem HasCauchyPV.cauchyPV_eq`
- **Type**: `{f γ z₀ L} (h : HasCauchyPV f γ z₀ L) : cauchyPV f γ z₀ = L`
- **What**: Bridge from `HasCauchyPV` predicate to `cauchyPV` value.
- **How**: `Tendsto.limUnder_eq` directly.
- **Hypotheses**: `HasCauchyPV f γ z₀ L`.
- **Uses from project**: [`HasCauchyPV`, `cauchyPV`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 108-110
- **Notes**: None.

### `theorem HasCauchyPV.neg`
- **Type**: `{f γ z₀ L} (h : HasCauchyPV f γ z₀ L) : HasCauchyPV (fun z => -f z) γ z₀ (-L)`
- **What**: Negation: replacing `f` with `-f` negates the CPV.
- **How**: Build `heq` showing the negated integrand equals the negated integral, via `intervalIntegral.integral_neg` and `split_ifs`, then apply `Tendsto.neg`.
- **Hypotheses**: `HasCauchyPV f γ z₀ L`.
- **Uses from project**: [`HasCauchyPV`, `cpvIntegrand`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 115-126
- **Notes**: None.

### `theorem HasCauchyPV.smul`
- **Type**: `{f γ z₀ L} (c : ℂ) (h : HasCauchyPV f γ z₀ L) : HasCauchyPV (fun z => c * f z) γ z₀ (c * L)`
- **What**: Scalar multiplication: scaling `f` by `c` scales the CPV by `c`.
- **How**: `heq` pulls `c` out of `cpvIntegrand` via `split_ifs <;> ring`, then `intervalIntegral.integral_const_mul`, finally `Tendsto.const_mul`.
- **Hypotheses**: `HasCauchyPV f γ z₀ L`.
- **Uses from project**: [`HasCauchyPV`, `cpvIntegrand`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 129-143
- **Notes**: 15 lines.

### `theorem hasCauchyPV_of_avoids`
- **Type**: `{f γ z₀} (hδ : ∃ δ > 0, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - z₀‖) : HasCauchyPV f γ z₀ (γ.contourIntegral f)`
- **What**: If `γ` keeps minimum distance `δ > 0` from `z₀`, the CPV equals the ordinary contour integral.
- **How**: `Tendsto.congr'` with `tendsto_const_nhds`; the eventually-equal set is `Ioo 0 δ` via `Ioo_mem_nhdsGT`, where `cpvIntegrand_of_gt` ensures the integrand matches.
- **Hypotheses**: existence of positive uniform distance bound on `[0,1]`.
- **Uses from project**: [`HasCauchyPV`, `PiecewiseC1Path.contourIntegral`, `cpvIntegrand_of_gt`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 147-160
- **Notes**: 14 lines.

### `def cpvIntegrandOn`
- **Type**: `(S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) : ℂ`
- **What**: Multi-point cutoff integrand: zero whenever `γ t` is within `ε` of some `s ∈ S`, else `f(γ t) · γ'(t)`.
- **How**: `if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `cpvIntegrandOn_of_forall_gt`, `cpvIntegrandOn_of_exists_le`, `cpvIntegrandOn_empty`, `cpvIntegrand_eq_cpvIntegrandOn_singleton`, `HasCauchyPVOn`, `cauchyPVOn`, `HasCauchyPVOn.neg`, `HasCauchyPVOn.smul`, `hasCauchyPVOn_of_avoids`, `hasCauchyPVOn_empty`
- **Visibility**: public
- **Lines**: 165-167
- **Notes**: None.

### `theorem cpvIntegrandOn_of_forall_gt`
- **Type**: `{S f γ ε t} (h : ∀ s ∈ S, ε < ‖γ t - s‖) : cpvIntegrandOn S f γ ε t = f (γ t) * deriv γ t`
- **What**: If `γ t` is more than `ε` away from every `s ∈ S`, the integrand is unmodified.
- **How**: Negate the existential via `push Not`, then `if_neg`.
- **Hypotheses**: `∀ s ∈ S, ε < ‖γ t - s‖`.
- **Uses from project**: [`cpvIntegrandOn`]
- **Used by**: `hasCauchyPVOn_of_avoids`
- **Visibility**: public (`@[simp]`)
- **Lines**: 169-176
- **Notes**: None.

### `theorem cpvIntegrandOn_of_exists_le`
- **Type**: `{S f γ ε t} (h : ∃ s ∈ S, ‖γ t - s‖ ≤ ε) : cpvIntegrandOn S f γ ε t = 0`
- **What**: When `γ t` is within `ε` of some `s ∈ S`, the integrand vanishes.
- **How**: `simp` with the positive branch.
- **Hypotheses**: `∃ s ∈ S, ‖γ t - s‖ ≤ ε`.
- **Uses from project**: [`cpvIntegrandOn`]
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 178-182
- **Notes**: None.

### `theorem cpvIntegrandOn_empty`
- **Type**: `{f γ ε t} : cpvIntegrandOn ∅ f γ ε t = f (γ t) * deriv γ t`
- **What**: With empty singular set, the integrand reduces to the standard one.
- **How**: `simp [cpvIntegrandOn]` — empty set has no member.
- **Hypotheses**: None.
- **Uses from project**: [`cpvIntegrandOn`]
- **Used by**: `hasCauchyPVOn_empty`
- **Visibility**: public
- **Lines**: 184-186
- **Notes**: None.

### `theorem cpvIntegrand_eq_cpvIntegrandOn_singleton`
- **Type**: `{f γ z₀ ε t} : cpvIntegrand f γ z₀ ε t = cpvIntegrandOn {z₀} f γ ε t`
- **What**: Single-point CPV integrand agrees with the multi-point version for the singleton set.
- **How**: Unfold both, simp through `Finset.mem_singleton`/`exists_eq_left`, then `split_ifs` resolves with `rfl`/`linarith`.
- **Hypotheses**: None.
- **Uses from project**: [`cpvIntegrand`, `cpvIntegrandOn`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 189-193
- **Notes**: None.

### `def HasCauchyPVOn`
- **Type**: `(S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (L : ℂ) : Prop`
- **What**: Multi-point CPV predicate: limit of ε-cutoff integral exists and equals `L` as `ε → 0⁺`.
- **How**: `Tendsto (fun ε => ∫ t in 0..1, cpvIntegrandOn S f γ.extend ε t) (𝓝[>] 0) (𝓝 L)`.
- **Hypotheses**: None.
- **Uses from project**: [`cpvIntegrandOn`, `PiecewiseC1Path`]
- **Used by**: `cauchyPVOn`, `HasCauchyPVOn.cauchyPVOn_eq`, `HasCauchyPVOn.neg`, `HasCauchyPVOn.smul`, `hasCauchyPVOn_of_avoids`, `hasCauchyPVOn_empty`, `HasCauchyPVOn.unique`
- **Visibility**: public
- **Lines**: 200-202
- **Notes**: None.

### `def cauchyPVOn`
- **Type**: `(S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) : ℂ`
- **What**: Multi-point CPV value via `limUnder`; junk when limit doesn't exist.
- **How**: `limUnder (𝓝[>] 0) (∫ … cpvIntegrandOn …)`.
- **Hypotheses**: None.
- **Uses from project**: [`cpvIntegrandOn`, `PiecewiseC1Path`]
- **Used by**: `HasCauchyPVOn.cauchyPVOn_eq`
- **Visibility**: public
- **Lines**: 206-208
- **Notes**: None.

### `theorem HasCauchyPVOn.cauchyPVOn_eq`
- **Type**: `{S f γ L} (h : HasCauchyPVOn S f γ L) : cauchyPVOn S f γ = L`
- **What**: Bridge: `HasCauchyPVOn` predicate determines `cauchyPVOn` value.
- **How**: `Tendsto.limUnder_eq`.
- **Hypotheses**: `HasCauchyPVOn S f γ L`.
- **Uses from project**: [`HasCauchyPVOn`, `cauchyPVOn`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 211-214
- **Notes**: None.

### `theorem HasCauchyPVOn.neg`
- **Type**: `{S f γ L} (h : HasCauchyPVOn S f γ L) : HasCauchyPVOn S (fun z => -f z) γ (-L)`
- **What**: Negation for multi-point CPV.
- **How**: `heq` rewrites the negated integral via `intervalIntegral.integral_neg` and `split_ifs`, then `Tendsto.neg`.
- **Hypotheses**: `HasCauchyPVOn S f γ L`.
- **Uses from project**: [`HasCauchyPVOn`, `cpvIntegrandOn`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 219-231
- **Notes**: 13 lines.

### `theorem HasCauchyPVOn.smul`
- **Type**: `{S f γ L} (c : ℂ) (h : HasCauchyPVOn S f γ L) : HasCauchyPVOn S (fun z => c * f z) γ (c * L)`
- **What**: Scalar multiplication for multi-point CPV.
- **How**: Pull `c` out of `cpvIntegrandOn` via `split_ifs <;> ring`, apply `integral_const_mul`, then `Tendsto.const_mul`.
- **Hypotheses**: `HasCauchyPVOn S f γ L`.
- **Uses from project**: [`HasCauchyPVOn`, `cpvIntegrandOn`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 234-248
- **Notes**: 15 lines.

### `theorem hasCauchyPVOn_of_avoids`
- **Type**: `{S f γ} (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s‖) : HasCauchyPVOn S f γ (γ.contourIntegral f)`
- **What**: If `γ` avoids every singularity in `S` uniformly, multi-point CPV equals the ordinary contour integral.
- **How**: `Tendsto.congr'` with `tendsto_const_nhds` and eventually-equal `Ioo 0 δ`; the integrand match uses `cpvIntegrandOn_of_forall_gt`.
- **Hypotheses**: uniform positive distance bound.
- **Uses from project**: [`HasCauchyPVOn`, `PiecewiseC1Path.contourIntegral`, `cpvIntegrandOn_of_forall_gt`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 252-266
- **Notes**: 15 lines.

### `theorem hasCauchyPVOn_empty`
- **Type**: `{f γ} : HasCauchyPVOn ∅ f γ (γ.contourIntegral f)`
- **What**: For empty `S`, multi-point CPV equals the ordinary contour integral.
- **How**: `Tendsto.congr` with `tendsto_const_nhds`; integrand match via `cpvIntegrandOn_empty.symm`.
- **Hypotheses**: None.
- **Uses from project**: [`HasCauchyPVOn`, `PiecewiseC1Path.contourIntegral`, `cpvIntegrandOn_empty`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 269-276
- **Notes**: None.

### `theorem HasCauchyPV.unique`
- **Type**: `{f γ z₀ L₁ L₂} (h₁ : HasCauchyPV f γ z₀ L₁) (h₂ : HasCauchyPV f γ z₀ L₂) : L₁ = L₂`
- **What**: Uniqueness of the CPV limit.
- **How**: `tendsto_nhds_unique`.
- **Hypotheses**: Two `HasCauchyPV` assertions.
- **Uses from project**: [`HasCauchyPV`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 281-284
- **Notes**: None.

### `theorem HasCauchyPVOn.unique`
- **Type**: `{S f γ L₁ L₂} (h₁ : HasCauchyPVOn S f γ L₁) (h₂ : HasCauchyPVOn S f γ L₂) : L₁ = L₂`
- **What**: Uniqueness of multi-point CPV limit.
- **How**: `tendsto_nhds_unique`.
- **Hypotheses**: Two `HasCauchyPVOn` assertions.
- **Uses from project**: [`HasCauchyPVOn`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 287-290
- **Notes**: None.

## File Summary
Defines Cauchy principal value contour integrals over `PiecewiseC1Path`, in both single-point (`HasCauchyPV`/`cauchyPV`) and multi-point (`HasCauchyPVOn`/`cauchyPVOn`) flavours. The `HasCauchyPV` Tendsto predicate is the primary API; `cauchyPV` (via `limUnder`) is secondary. Provides basic algebraic API (`neg`, `smul`, `unique`), a bridge from predicate to value (`cauchyPV_eq`), and "avoidance" theorems showing CPV equals the ordinary integral when the curve stays away from singularities. The singleton/multi-point equivalence and an `empty` lemma round out the file. No sorries, no axioms, no `set_option` overrides.
