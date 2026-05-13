# Inventory: ForMathlib/Bounds.lean

NOTE: The entire file is wrapped inside a block comment `/- /- ... -/` (a malformed nested-comment header followed by a closing `-/` at the end of the file). All declarations below are therefore **commented out** and do not contribute to compilation. The inventory still records each declaration as written.

### `def ModularGroup.truncatedFundamentalDomain`
- **Type**: `(y : ℝ) : Set ℍ`
- **What**: The standard modular fundamental domain `𝒟` intersected with `{τ : τ.im ≤ y}`.
- **How**: Set-builder `{ τ | τ ∈ 𝒟 ∧ τ.im ≤ y }`.
- **Hypotheses**: none.
- **Uses from project**: `𝒟` (scoped `Modular` notation, from Mathlib).
- **Used by**: `coe_truncatedFundamentalDomain`, `isCompact_truncatedFundamentalDomain`, `exists_bound_fundamental_domain_of_isBigO`.
- **Visibility**: public (in `namespace ModularGroup`)
- **Lines**: 29–30
- **Notes**: file body commented out

### `lemma ModularGroup.coe_truncatedFundamentalDomain`
- **Type**: `(y : ℝ) : Subtype.val '' truncatedFundamentalDomain y = {z | 0 ≤ z.im ∧ z.im ≤ y ∧ |z.re| ≤ 1/2 ∧ 1 ≤ ‖z‖}`
- **What**: Explicit coordinate description of the truncated fundamental domain in ℂ.
- **How**: Set extensionality + two-direction destructuring; uses `Complex.normSq_eq_norm_sq` and `sq_lt_one_iff₀` to convert between `‖z‖ ≥ 1` and `normSq z ≥ 1`. (~13 lines.)
- **Hypotheses**: none.
- **Uses from project**: `truncatedFundamentalDomain`.
- **Used by**: `isCompact_truncatedFundamentalDomain`.
- **Visibility**: public
- **Lines**: 34–47
- **Notes**: >10 lines; file body commented out

### `lemma ModularGroup.isCompact_truncatedFundamentalDomain`
- **Type**: `(y : ℝ) : IsCompact (truncatedFundamentalDomain y)`
- **What**: The truncated fundamental domain is compact in `ℍ`.
- **How**: `Subtype.isCompact_iff` + `coe_truncatedFundamentalDomain`; `Metric.isCompact_iff_isClosed_bounded` yields two goals. Closedness follows from finite intersection of `isClosed_le` with `Complex.continuous_im`, `continuous_abs.comp Complex.continuous_re`, `continuous_norm`. Boundedness via `Metric.isBounded_iff_subset_closedBall 0` and the radius `√((1/2)² + y²)`, with `Complex.norm_eq_sqrt_sq_add_sq` and case-by-case `sq_le_sq` bounds. (~17 lines.)
- **Hypotheses**: none.
- **Uses from project**: `truncatedFundamentalDomain`, `coe_truncatedFundamentalDomain`.
- **Used by**: `exists_bound_fundamental_domain_of_isBigO`.
- **Visibility**: public
- **Lines**: 50–69
- **Notes**: >10 lines; file body commented out

### `lemma ModularGroup.exists_bound_fundamental_domain_of_isBigO`
- **Type**: `{E : Type*} [SeminormedAddCommGroup E] {f : ℍ → E} (hf_cont : Continuous f) {t : ℝ} (hf_infinity : f =O[atImInfty] fun z ↦ z.im ^ t) : ∃ F, ∀ τ ∈ 𝒟, ‖f τ‖ ≤ F * τ.im ^ t`
- **What**: A continuous function on `ℍ` that's `O((im z)^t)` at the cusp is bounded by `F · (im τ)^t` on the fundamental domain.
- **How**: Extract a high-`im` constant `D` from `IsBigO.exists_pos`; rewrite `atImInfty` + `eventually_comap`/`atTop` to get an `y`-cutoff; bound `‖f τ‖/(im τ)^t` on `truncatedFundamentalDomain y` by compactness (`IsCompact.exists_bound_of_continuousOn`); take `max D E`. (~21 lines.)
- **Hypotheses**: `Continuous f`, `f =O[atImInfty] fun z ↦ z.im ^ t`.
- **Uses from project**: `truncatedFundamentalDomain`, `isCompact_truncatedFundamentalDomain`.
- **Used by**: `exists_bound_of_invariant_of_isBigO`.
- **Visibility**: public
- **Lines**: 71–93
- **Notes**: >10 lines; file body commented out

### `lemma ModularGroup.exists_bound_of_invariant_of_isBigO`
- **Type**: `{E} [SeminormedAddCommGroup E] {f : ℍ → E} (hf_cont : Continuous f) {t : ℝ} (ht : 0 ≤ t) (hf_infinity : f =O[atImInfty] fun z ↦ (im z) ^ t) (hf_inv : ∀ (g : SL(2,ℤ)) τ, f (g • τ) = f τ) : ∃ C, ∀ τ, ‖f τ‖ ≤ C * (max (im τ) (1/im τ)) ^ t`
- **What**: An `SL(2,ℤ)`-invariant function with controlled growth at `∞` is globally bounded by `(max im τ, 1/im τ)^t`.
- **How**: First obtain `F` via `exists_bound_fundamental_domain_of_isBigO`. Move `τ` into FD via `exists_smul_mem_fd`. Apply `hf_inv` to transport bound back to `τ`. Then bound `(g • τ).im ≤ max τ.im (1/τ.im)` via `im_smul_eq_div_normSq`, case-split on `g 1 0 = 0` (uses `Matrix.det_fin_two`, `Int.one_le_abs`, `normSq_denom_pos`) and `≠ 0`. (~38 lines.)
- **Hypotheses**: continuity, `IsBigO` at `∞`, `0 ≤ t`, `SL(2,ℤ)`-invariance.
- **Uses from project**: `exists_bound_fundamental_domain_of_isBigO`.
- **Used by**: `exists_bound_of_subgroup_invariant_of_isBigO`, `exists_bound_of_invariant`.
- **Visibility**: public
- **Lines**: 100–144
- **Notes**: >10 lines; file body commented out

### `lemma ModularGroup.exists_bound_of_subgroup_invariant_of_isBigO`
- **Type**: `{E} [SeminormedAddCommGroup E] {f : ℍ → E} (hf_cont : Continuous f) {t : ℝ} (ht : 0 ≤ t) (hf_infinity : ∀ (g : SL(2,ℤ)), (fun τ ↦ f (g • τ)) =O[atImInfty] fun z ↦ (im z) ^ t) {Γ : Subgroup SL(2,ℤ)} [Γ.FiniteIndex] (hf_inv : ∀ g ∈ Γ, ∀ τ, f (g • τ) = f τ) : ∃ C, ∀ τ, ‖f τ‖ ≤ C * max τ.im (1/τ.im) ^ t`
- **What**: Bound for functions invariant under a finite-index subgroup with controlled growth at all cusps.
- **How**: Define `f' : ℍ → SL(2,ℤ)/Γ → E` via `Quotient.lift`; prove continuity, invariance, and `IsBigO` for each `γ ∈ SL(2,ℤ)/Γ`. Sum over the finite quotient and apply `exists_bound_of_invariant_of_isBigO` to the sum. Pick out the coset `⟦1⟧` via `Finset.single_le_sum`. (~26 lines.)
- **Hypotheses**: as in the signature; `Γ.FiniteIndex`.
- **Uses from project**: `exists_bound_of_invariant_of_isBigO`.
- **Used by**: `exists_bound_of_subgroup_invariant`, `exists_petersson_le`.
- **Visibility**: public
- **Lines**: 149–175
- **Notes**: >10 lines; file body commented out

### `lemma ModularGroup.exists_bound_of_invariant`
- **Type**: `{E} [SeminormedAddCommGroup E] {f : ℍ → E} (hf_cont : Continuous f) (hf_infinity : IsBoundedAtImInfty f) (hf_inv : ∀ (g : SL(2,ℤ)) τ, f (g • τ) = f τ) : ∃ C, ∀ τ, ‖f τ‖ ≤ C`
- **What**: `SL(2,ℤ)`-invariant continuous function bounded at infinity is globally bounded.
- **How**: Apply `exists_bound_of_invariant_of_isBigO` with `t = 0`; uses `Real.rpow_zero`.
- **Hypotheses**: continuity, `IsBoundedAtImInfty`, `SL(2,ℤ)`-invariance.
- **Uses from project**: `exists_bound_of_invariant_of_isBigO`.
- **Used by**: `CuspFormClass.petersson_bounded_left`.
- **Visibility**: public
- **Lines**: 178–183
- **Notes**: file body commented out

### `lemma ModularGroup.exists_bound_of_subgroup_invariant`
- **Type**: `{E} [SeminormedAddCommGroup E] {f : ℍ → E} (hf_cont : Continuous f) (hf_infinity : ∀ (g : SL(2,ℤ)), IsBoundedAtImInfty fun τ ↦ f (g • τ)) {Γ : Subgroup SL(2,ℤ)} [Γ.FiniteIndex] (hf_inv : ∀ g ∈ Γ, ∀ τ, f (g • τ) = f τ) : ∃ C, ∀ τ, ‖f τ‖ ≤ C`
- **What**: Subgroup-invariant function bounded at all cusps is globally bounded.
- **How**: Apply `exists_bound_of_subgroup_invariant_of_isBigO` with `t = 0`.
- **Hypotheses**: continuity, `IsBoundedAtImInfty` at all cusps, finite-index invariance.
- **Uses from project**: `exists_bound_of_subgroup_invariant_of_isBigO`.
- **Used by**: `CuspFormClass.petersson_bounded_left`.
- **Visibility**: public
- **Lines**: 187–193
- **Notes**: file body commented out

### `lemma ModularFormClass.exists_petersson_le`
- **Type**: `{k : ℤ} (hk : 0 ≤ k) (Γ : Subgroup SL(2,ℤ)) [Γ.FiniteIndex] {F F'} (f : F) (f' : F') [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] [ModularFormClass F Γ k] [ModularFormClass F' Γ k] : ∃ C, ∀ τ, ‖petersson k f f' τ‖ ≤ C * max τ.im (1/τ.im) ^ k`
- **What**: Petersson product of two modular forms is bounded by `max τ.im (1/τ.im) ^ k`.
- **How**: Apply `ModularGroup.exists_bound_of_subgroup_invariant_of_isBigO` to the Petersson product. Continuity from `petersson_continuous`; `IsBigO` from `bdd_at_infty` of `f` and `f'` plus `isBigO_refl` on `τ.im^k`; invariance from `petersson_smul`. (~13 lines.)
- **Hypotheses**: `0 ≤ k`, modular form classes for `f, f'`, finite index of `Γ`.
- **Uses from project**: `ModularGroup.exists_bound_of_subgroup_invariant_of_isBigO`, `ModularFormClass.petersson_continuous`, `SlashInvariantFormClass.petersson_smul`, `petersson`.
- **Used by**: `ModularFormClass.exists_bound`.
- **Visibility**: public
- **Lines**: 199–213
- **Notes**: >10 lines; file body commented out

### `lemma CuspFormClass.petersson_bounded_left`
- **Type**: `(k : ℤ) (Γ : Subgroup SL(2,ℤ)) [Γ.FiniteIndex] {F F'} (f : F) (f' : F') [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] [CuspFormClass F Γ k] [ModularFormClass F' Γ k] : ∃ C, ∀ τ, ‖petersson k f f' τ‖ ≤ C`
- **What**: Petersson product with a cusp form on the left is globally bounded.
- **How**: `ModularGroup.exists_bound_of_subgroup_invariant` applied to the Petersson product. Zero-at-infty from `IsZeroAtImInfty.petersson_isZeroAtImInfty_left` on the conjugated subgroup `Γ' = Subgroup.map (MulAut.conj g⁻¹) Γ`; finite index transported via `Subgroup.index_map_of_bijective`. (~14 lines.)
- **Hypotheses**: cusp form for `f`, modular form for `f'`, finite-index `Γ`.
- **Uses from project**: `ModularGroup.exists_bound_of_subgroup_invariant`, `ModularFormClass.petersson_continuous`, `petersson`, `CuspForm.translate`, `ModularForm.translate`, `UpperHalfPlane.IsZeroAtImInfty.petersson_isZeroAtImInfty_left`, `SlashInvariantFormClass.petersson_smul`, `CuspFormClass.zero_at_infty`.
- **Used by**: `CuspFormClass.petersson_bounded_right`, `CuspFormClass.exists_bound`.
- **Visibility**: public
- **Lines**: 216–233
- **Notes**: >10 lines; file body commented out

### `lemma CuspFormClass.petersson_bounded_right`
- **Type**: `(k : ℤ) (Γ : Subgroup SL(2,ℤ)) [Γ.FiniteIndex] {F F'} (f : F) (f' : F') [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] [ModularFormClass F Γ k] [CuspFormClass F' Γ k] : ∃ C, ∀ τ, ‖petersson k f f' τ‖ ≤ C`
- **What**: Petersson product with a cusp form on the right is globally bounded.
- **How**: Reduce to `petersson_bounded_left k Γ f' f` by `mul_comm` inside `petersson`.
- **Hypotheses**: modular form for `f`, cusp form for `f'`, finite-index `Γ`.
- **Uses from project**: `CuspFormClass.petersson_bounded_left`, `petersson`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 236–240
- **Notes**: file body commented out

### `lemma CuspFormClass.exists_bound`
- **Type**: `{k : ℤ} {Γ : Subgroup SL(2,ℤ)} [Γ.FiniteIndex] {F} [FunLike F ℍ ℂ] [CuspFormClass F Γ k] (f : F) : ∃ C, ∀ τ, ‖f τ‖ ≤ C / τ.im ^ (k/2 : ℝ)`
- **What**: A weight-`k` cusp form is bounded by `C / (im τ)^(k/2)`.
- **How**: Apply `petersson_bounded_left k Γ f f`; take `√C`, divide by `τ.im^(k/2)`. Uses `Real.sqrt_le_sqrt_iff`, `Real.sqrt_mul_self`, `Real.sqrt_eq_rpow`, `Real.rpow_intCast_mul`. (~12 lines.)
- **Hypotheses**: cusp form for `f`, finite-index `Γ`.
- **Uses from project**: `CuspFormClass.petersson_bounded_left`, `petersson`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 243–255
- **Notes**: >10 lines; file body commented out

### `lemma ModularFormClass.exists_bound`
- **Type**: `{k : ℤ} (hk : 0 ≤ k) {Γ : Subgroup SL(2,ℤ)} [Γ.FiniteIndex] {F} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) : ∃ C, ∀ τ, ‖f τ‖ ≤ C * max 1 (1 / (τ.im)^k)`
- **What**: A weight-`k` modular form is bounded by `C · max(1, 1/(τ.im)^k)`.
- **How**: From `exists_petersson_le`, take `√C` and divide; manipulate `rpow`s, e.g., `1/τ.im^k * τ.im^(k/2) = (1/τ.im)^(k/2)` via `div_rpow`, `rpow_add`. Apply `MonotoneOn.map_max` for the final `max`. (~24 lines.)
- **Hypotheses**: `0 ≤ k`, modular form for `f`, finite-index `Γ`.
- **Uses from project**: `ModularFormClass.exists_petersson_le`, `petersson`.
- **Used by**: `ModularFormClass.qExpansion_isBigO`.
- **Visibility**: public
- **Lines**: 260–282
- **Notes**: >10 lines; file body commented out

### `lemma ModularFormClass.qExpansion_isBigO`
- **Type**: `{k : ℤ} (hk : 0 ≤ k) {Γ : Subgroup SL(2,ℤ)} [Γ.FiniteIndex] {F} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) : (fun n ↦ (ModularFormClass.qExpansion Γ.width f).coeff n) =O[atTop] fun n ↦ (n : ℝ) ^ k`
- **What**: q-expansion coefficients of a modular form are `O(n^k)` as `n → ∞`.
- **How**: Take bound `C` from `ModularFormClass.exists_bound`. Rewrite `qExpansion_coeff_eq_intervalIntegral` and bound the integrand pointwise using `Function.Periodic.norm_qParam`, `Real.exp_nat_mul`. Apply `intervalIntegral.norm_integral_le_integral_norm` + `intervalIntegral.integral_mono`. Continuity by `fun_prop`. (~48 lines.)
- **Hypotheses**: `0 ≤ k`, modular form, finite-index.
- **Uses from project**: `ModularFormClass.exists_bound`, `ModularFormClass.qExpansion`, `ModularFormClass.holo`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 287–339
- **Notes**: >30 lines; file body commented out; uses `local notation "𝕢" => Function.Periodic.qParam` (line 284)

## File Summary
- 13 declarations spanning compactness of the truncated FD, a 4-step bound hierarchy (`exists_bound_fundamental_domain_of_isBigO` → `exists_bound_of_invariant_of_isBigO` → `exists_bound_of_subgroup_invariant_of_isBigO` → `exists_bound[_of_invariant]`), Petersson bounds, modular- and cusp-form bounds, and a q-expansion `IsBigO` lemma.
- The ENTIRE file is wrapped in a block comment opened with `/- /-` on line 1 and closed with `-/` on line 340. None of the declarations actually compile. The file may be a scratch / archived copy of a Mathlib-bound contribution.
- Original (pre-comment) author David Loeffler; project import was `LeanModularForms.ForMathlib.Petersson`.
- No `sorry` / no `axiom`; comprehensive Mathlib-style proofs; one local notation `𝕢`.
- Notes: file body commented out — flag for cleanup or re-enabling.
