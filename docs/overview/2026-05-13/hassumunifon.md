# Inventory: hassumunifon.lean

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/hassumunifon.lean`
Top-level: 1 macro/elab + assorted theorems (no enclosing namespace, except `open EisensteinSeries` after l. 272 and `open ArithmeticFunction` after l. 692).
Lines: 1–1023.

**File-level note**: the file is wrapped in a single block comment `/- … -/` from line 1 (after the header `/-`) to line 1023. The leading `-/` at line 5 closes the docstring, then code resumes, and the entire file body ends with `-/` at line 1023. Lines 14 `import Mathlib`, line 1022 `#min_imports`. So the whole file content is currently commented out (every declaration is inert). Treating the declarations as if active (per the request's framing), inventory follows.

---

### `elab "my_sum_simp" : tactic`
- **Type**: tactic macro
- **What**: Tactic chain `simp_rw [← tsum_mul_left]; apply tsum_congr; field_simp; ring_nf; simp` for normalizing sums.
- **How**: `Lean.Elab.Tactic.evalTactic` sequencing.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public elab.
- **Lines**: 34–39.

### `theorem HasSumUniformlyOn_of_bounded`
- **Type**: `{f : α → β → F} (hu : Summable u) {s : Set β} (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) : HasSumUniformlyOn f (fun x ↦ ∑' n, f n x) {s}`
- **What**: A pointwise bound `‖f n x‖ ≤ u n` with summable `u` upgrades convergence to `HasSumUniformlyOn` on `s`.
- **How**: Rewrite via `hasSumUniformlyOn_iff_tendstoUniformlyOn`, apply `tendstoUniformlyOn_tsum hu hfu`.
- **Hypotheses**: `Summable u`, pointwise bound on `s`.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 42–44.

### `theorem HasSumUniformlyOn_of_cofinite_eventually`
- **Type**: `{ι : Type*} {f : ι → β → F} {u : ι → ℝ} (hu : Summable u) {s : Set β} (hfu : ∀ᶠ n in cofinite, ∀ x ∈ s, ‖f n x‖ ≤ u n) : HasSumUniformlyOn f (fun x ↦ ∑' n, f n x) {s}`
- **What**: Cofinite version: the bound only needs to hold off a finite set.
- **How**: Rewrite to tendstoUniformlyOn, apply `tendstoUniformlyOn_tsum_of_cofinite_eventually`.
- **Hypotheses**: summable bound, cofinite eventual bound.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 46–50.

### `lemma SummableLocallyUniformlyOn_of_locally_bounded_eventually`
- **Type**: `[TopologicalSpace β] [LocallyCompactSpace β] {f : α → β → F} {s : Set β} (hs : IsOpen s) (hu : ∀ K ⊆ s, IsCompact K → ∃ u, Summable u ∧ ∀ᶠ n in cofinite, ∀ k ∈ K, ‖f n k‖ ≤ u n) : SummableLocallyUniformlyOn f s`
- **What**: Locally-on-compacts cofinite bound implies `SummableLocallyUniformlyOn` on `s`.
- **How**: Use `HasSumLocallyUniformlyOn.summableLocallyUniformlyOn`; reduce to `tendstoUniformlyOn_tsum_of_cofinite_eventually` per compact `K ⊆ s`.
- **Hypotheses**: `s` open; per-compact bound.
- **Uses from project**: [].
- **Used by**: `SummableLocallyUniformlyOn_of_locally_bounded`.
- **Visibility**: public.
- **Lines**: 63–72.

### `lemma SummableLocallyUniformlyOn_of_locally_bounded`
- **Type**: same as above but `∀ n` (not cofinite).
- **What**: Same as previous, with the bound holding for all `n` (not eventually).
- **How**: Reduces to the cofinite version via `filter_upwards using hu2`.
- **Hypotheses**: as above.
- **Uses from project**: `SummableLocallyUniformlyOn_of_locally_bounded_eventually`.
- **Used by**: `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm`, `qExpansion_summableLocallyUniformlyOn`, `qExpansion_summableLocallyUniformlyOn2`.
- **Visibility**: public.
- **Lines**: 74–81.

### `theorem derivWithin_tsum`
- **Type**: `{F E : Type*} [NontriviallyNormedField E] [IsRCLikeNormedField E] [NormedAddCommGroup F] [NormedSpace E F] {f : α → E → F} {s : Set E} (hs : IsOpen s) {x : E} (hx : x ∈ s) (hf : ∀ y ∈ s, Summable fun n ↦ f n y) (h : SummableLocallyUniformlyOn (fun n ↦ derivWithin (fun z ↦ f n z) s) s) (hf2 : ∀ n r, r ∈ s → DifferentiableAt E (f n) r) : derivWithin (fun z ↦ ∑' n, f n z) s x = ∑' n, derivWithin (f n) s x`
- **What**: Derivative within `s` of a series of functions equals the series of derivatives, under absolute+local-uniform convergence and pointwise summability.
- **How**: Promote to `HasDerivWithinAt` via `IsOpen.uniqueDiffWithinAt`. Reduce to `hasDerivAt_of_tendstoLocallyUniformlyOn`, supplying partial sums of `derivWithin` as derivative approximations (from `SummableLocallyUniformlyOn`'s `g` value, tying via `hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn`). Discharge `HasDerivAt` of finite partial sums by `HasDerivAt.fun_sum` and per-term differentiability.
- **Hypotheses**: `s` open, pointwise summable, local uniform convergence of derivatives, each `f n` differentiable on `s`.
- **Uses from project**: [].
- **Used by**: `iteratedDerivWithin_tsum`.
- **Visibility**: public.
- **Lines**: 87–102.

### `lemma summableUniformlyOn_differentiableOn`
- **Type**: `{ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ι → ℂ → E} {s : Set ℂ} (hs : IsOpen s) (h : SummableLocallyUniformlyOn (fun n ↦ f n) s) (hf2 : ∀ n r, r ∈ s → DifferentiableAt ℂ (f n) r) : DifferentiableOn ℂ (fun z ↦ ∑' n, f n z) s`
- **What**: The pointwise sum of locally-uniformly-convergent complex-differentiable functions is differentiable on the open `s`.
- **How**: Obtain limit `g`, transfer `TendstoLocallyUniformlyOn` via `hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn`. Apply `TendstoLocallyUniformlyOn.differentiableOn`, then `congr` against partial-sum tsum value.
- **Hypotheses**: `s` open; local-uniform summability; per-term differentiability.
- **Uses from project**: [].
- **Used by**: `tsum_uexp_contDiffOn`.
- **Visibility**: public.
- **Lines**: 104–114.

### `lemma summable_of_tsum_ne_zero`
- **Type**: `{ι α : Type*} [AddCommMonoid α] [TopologicalSpace α] (g : ι → α) (h : ∑' n, g n ≠ 0) : Summable g`
- **What**: If the value of an infinite sum is nonzero, the family is summable.
- **How**: Contrapositive: `tsum_eq_zero_of_not_summable` then `aesop`.
- **Hypotheses**: tsum ≠ 0.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 117–121.

### `theorem eqOn_finsetProd` (`@[to_additive]`)
- **Type**: `{ι α β : Type*} [CommMonoid α] (s : Set β) {f f' : ι → β → α} (h : ∀ i, EqOn (f i) (f' i) s) (v : Finset ι) : EqOn (∏ i ∈ v, f i) (∏ i ∈ v, f' i) s`
- **What**: Pointwise equality of `f i` on `s` lifts to equality of finite products on `s`.
- **How**: `Finset.prod_apply` then `congr` + `funext` from pointwise hypothesis.
- **Hypotheses**: pointwise EqOn.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public; auto-generated additive twin via `to_additive`.
- **Lines**: 127–133.

### `theorem eqOn_fun_finsetProd` (`@[to_additive]`)
- **Type**: as above but stated for `fun b ↦ ∏ i ∈ v, f i b`.
- **What**: Same as `eqOn_finsetProd` but using the explicit lambda binding.
- **How**: same as above.
- **Hypotheses**: same.
- **Uses from project**: [].
- **Used by**: `MultipliableLocallyUniformlyOn_congr`.
- **Visibility**: public; additive twin.
- **Lines**: 136–142.

### `lemma MultipliableLocallyUniformlyOn_congr` (`@[to_additive]`)
- **Type**: `(f f' : ι → β → α) (h : ∀ i, s.EqOn (f i) (f' i)) (h2 : MultipliableLocallyUniformlyOn f s) : MultipliableLocallyUniformlyOn f' s`
- **What**: `MultipliableLocallyUniformlyOn` is invariant under pointwise equality on `s`.
- **How**: Use `HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn`; congr via `eqOn_fun_finsetProd`.
- **Hypotheses**: pointwise equality of families.
- **Uses from project**: `eqOn_fun_finsetProd`.
- **Used by**: unused in file.
- **Visibility**: public; additive twin.
- **Lines**: 145–148.

### `theorem iteratedDerivWithin_tsum`
- **Type**: `{F E : Type*} [NontriviallyNormedField E] [IsRCLikeNormedField E] [NormedField F] [NormedSpace E F] {f : ι → E → F} {s : Set E} (m : ℕ) (hs : IsOpen s) {x : E} (hx : x ∈ s) (hsum : ∀ t ∈ s, Summable (fun n : ι ↦ f n t)) (h : ∀ k, 1 ≤ k → k ≤ m → SummableLocallyUniformlyOn (fun n ↦ iteratedDerivWithin k (fun z ↦ f n z) s) s) (hf2 : ∀ n k r, k ≤ m → r ∈ s → DifferentiableAt E (iteratedDerivWithin k (fun z ↦ f n z) s) r) : iteratedDerivWithin m (fun z ↦ ∑' n, f n z) s x = ∑' n, iteratedDerivWithin m (f n) s x`
- **What**: Iterated within-derivative commutes with infinite summation, under iterated summability of derivatives.
- **How**: Induction on `m`. Base `m = 0` trivial. Step: unfold `iteratedDerivWithin_succ`, apply `derivWithin_tsum` with the hypothesis at level `m`. Inductive hypothesis at varying `x` discharges the `derivWithin` congruence. Pointwise summability at level `m > 0` comes from `(h m _ _).summable hr`.
- **Hypotheses**: `s` open, pointwise summable, summability of derivatives up to order `m`, per-order differentiability.
- **Uses from project**: `derivWithin_tsum`.
- **Used by**: `aux_iteratedDeriv_tsum_cotTerm`, `exp_deriv'`.
- **Visibility**: public.
- **Lines**: 150–169.
- **Notes**: 20-line inductive proof.

### `theorem iteratedDerivWithin_fun_add`
- **Type**: `(hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : iteratedDerivWithin n (fun z ↦ f z + g z) s x = iteratedDerivWithin n f s x + iteratedDerivWithin n g s x`
- **What**: Iterated within-derivative distributes over addition for two `ContDiffWithinAt` functions.
- **How**: `simpa using iteratedDerivWithin_add hx h hf hg`.
- **Hypotheses**: `UniqueDiffOn 𝕜 s`, `x ∈ s`, both `ContDiffWithinAt 𝕜 n` at `x`.
- **Uses from project**: [].
- **Used by**: `cot_series_rep_deriv2`.
- **Visibility**: public.
- **Lines**: 180–184.

### `theorem iteratedDerivWithin_congr_of_isOpen`
- **Type**: `(f : 𝕜 → F) (n : ℕ) {s t : Set 𝕜} (hs : IsOpen s) (ht : IsOpen t) : (s ∩ t).EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n f t)`
- **What**: On the intersection of two open sets, the iterated within-derivative w.r.t. one open set equals that w.r.t. the other (because both equal `iteratedDeriv` near each point).
- **How**: `iteratedDerivWithin_of_isOpen` applied twice at each point of `s ∩ t`.
- **Hypotheses**: both sets open.
- **Uses from project**: [].
- **Used by**: `cotTerm_iteratedDerivWith'`.
- **Visibility**: public.
- **Lines**: 193–196.

### `theorem contDiffOn_inv_linear`
- **Type**: `(d : ℤ) (k : ℕ) : ContDiffOn ℂ k (fun z : ℂ ↦ 1 / (z + d)) ℂ_ℤ`
- **What**: `z ↦ 1/(z+d)` is `C^k`-smooth on the complement of `ℤ ⊂ ℂ`.
- **How**: `ContDiffOn.inv` with `fun_prop`; nonzero via `Complex.integerComplement_add_ne_zero`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `cotTerm_iteratedDeriv`.
- **Visibility**: public.
- **Lines**: 202–206.
- **Notes**: notation `ℂ_ℤ` from line 200.

### `theorem contDiffOn_inv_linear_sub`
- **Type**: `(d : ℤ) (k : ℕ) : ContDiffOn ℂ k (fun z : ℂ ↦ 1 / (z - d)) ℂ_ℤ`
- **What**: `z ↦ 1/(z-d)` is `C^k`-smooth on `ℂ_ℤ`.
- **How**: Reduce `z - d = z + (-d)` and reuse `contDiffOn_inv_linear (-d)`.
- **Hypotheses**: none.
- **Uses from project**: `contDiffOn_inv_linear`.
- **Used by**: `cotTerm_iteratedDeriv`.
- **Visibility**: public.
- **Lines**: 208–211.

### `lemma cotTerm_iteratedDeriv`
- **Type**: `(d k : ℕ) : EqOn (iteratedDeriv k (fun z ↦ cotTerm z d)) (fun z ↦ (-1)^k · k! · ((z + (d+1))^(-1-k:ℤ) + (z - (d+1))^(-1-k:ℤ))) ℂ_ℤ`
- **What**: Closed form for the `k`-th iterated derivative of `cotTerm z d = 1/(z-(d+1)) + 1/(z+(d+1))` on `ℂ_ℤ`.
- **How**: Split sum via `iteratedDeriv_add` (smoothness from `contDiffOn_inv_linear_sub`, `contDiffOn_inv_linear`); apply `iter_deriv_inv_linear_sub` and `iter_deriv_inv_linear`; finish with `ring`.
- **Hypotheses**: none.
- **Uses from project**: `cotTerm`, `contDiffOn_inv_linear`, `contDiffOn_inv_linear_sub`, `iter_deriv_inv_linear`, `iter_deriv_inv_linear_sub`.
- **Used by**: `cotTerm_iteratedDerivWith`.
- **Visibility**: public.
- **Lines**: 213–229.

### `lemma cotTerm_iteratedDerivWith`
- **Type**: same closed form for `iteratedDerivWithin … ℂ_ℤ` on `ℂ_ℤ`.
- **What**: Within-derivative version of `cotTerm_iteratedDeriv`.
- **How**: Compose `iteratedDerivWithin_of_isOpen Complex.isOpen_compl_range_intCast` with `cotTerm_iteratedDeriv`.
- **Hypotheses**: none.
- **Uses from project**: `cotTerm`, `cotTerm_iteratedDeriv`.
- **Used by**: `cotTerm_iteratedDerivWith'`.
- **Visibility**: public.
- **Lines**: 231–234.

### `lemma upperHalfPlane_inter_integerComplement`
- **Type**: `{z : ℂ | 0 < z.im} ∩ Complex.integerComplement = {z : ℂ | 0 < z.im}`
- **What**: The upper half plane is contained in `ℂ_ℤ` (no integer has positive imaginary part), so intersection equals the upper half plane.
- **How**: Extensionality; use `UpperHalfPlane.coe_mem_integerComplement` for the nontrivial inclusion.
- **Hypotheses**: none.
- **Uses from project**: `UpperHalfPlane.coe_mem_integerComplement`.
- **Used by**: `cotTerm_iteratedDerivWith'`.
- **Visibility**: public.
- **Lines**: 236–241.

### `lemma UpperHalPlane_isOpen`
- **Type**: `IsOpen {z : ℂ | 0 < z.im}`
- **What**: The upper half plane (as subset of ℂ) is open.
- **How**: `isOpen_lt continuous_const Complex.continuous_im`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `cotTerm_iteratedDerivWith'`, `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm`, `iteratedDeriv_cotTerm_DifferentiableOn`, `aux_iteratedDeriv_tsum_cotTerm`, `cot_series_rep_deriv2`, `cot_series_rep_iteratedDeriv`, `exp_iter_deriv_within`, `exp_iter_deriv_within2`, `qExpansion_summableLocallyUniformlyOn`, `qExpansion_summableLocallyUniformlyOn2`, `deriv_iterderivwithin`, `exp_deriv'`, `tsum_uexp_contDiffOn`, `exp_deriv`.
- **Visibility**: public.
- **Lines**: 243–244.

### `lemma cotTerm_iteratedDerivWith'`
- **Type**: `(d k : ℕ) : EqOn (iteratedDerivWithin k (fun z ↦ cotTerm z d) {z | 0 < z.im}) (fun z ↦ (-1)^k · k! · ((z + (d+1))^(-1-k:ℤ) + (z - (d+1))^(-1-k:ℤ))) {z | 0 < z.im}`
- **What**: Same closed form on the upper half plane (transferring from `ℂ_ℤ`).
- **How**: Combine `iteratedDerivWithin_congr_of_isOpen` (open-set within-deriv invariance) and `upperHalfPlane_inter_integerComplement` to reduce to `cotTerm_iteratedDerivWith`; close via `UpperHalfPlane.coe_mem_integerComplement`.
- **Hypotheses**: none.
- **Uses from project**: `cotTerm`, `cotTerm_iteratedDerivWith`, `iteratedDerivWithin_congr_of_isOpen`, `upperHalfPlane_inter_integerComplement`, `UpperHalfPlane.coe_mem_integerComplement`, `UpperHalPlane_isOpen`.
- **Used by**: `iteratedDeriv_CotTerm_bounded_uniformly`, `iteratedDeriv_cotTerm_DifferentiableOn`, `aux_iteratedDeriv_tsum_cotTerm`.
- **Visibility**: public.
- **Lines**: 246–255.

### `lemma abs_norm_eq_max_natAbs`
- **Type**: `(n : ℕ) : ‖![1, (n + 1 : ℤ)]‖ = n + 1`
- **What**: Eisenstein-style norm of the 2-vector `(1, n+1)` equals `n+1`.
- **How**: `simp [EisensteinSeries.norm_eq_max_natAbs, Int.natAbs_of_isUnit, …]; norm_cast; simp`.
- **Hypotheses**: none.
- **Uses from project**: `EisensteinSeries.norm_eq_max_natAbs`.
- **Used by**: `iteratedDeriv_CotTerm_bounded_uniformly`.
- **Visibility**: public.
- **Lines**: 257–263.

### `lemma abs_norm_eq_max_natAbs_neg`
- **Type**: `(n : ℕ) : ‖![1, -(n + 1 : ℤ)]‖ = n + 1`
- **What**: Same as above with negated second coordinate.
- **How**: Same as above with `Int.natAbs_neg`.
- **Hypotheses**: none.
- **Uses from project**: `EisensteinSeries.norm_eq_max_natAbs`.
- **Used by**: `iteratedDeriv_CotTerm_bounded_uniformly`.
- **Visibility**: public.
- **Lines**: 265–270.

### `private noncomputable abbrev cotTermUpperBound`
- **Type**: `(A B : ℝ) (hB : 0 < B) (k a : ℕ) : ℝ := k! * (2 * r(⟨A,B⟩)^(-1-k:ℤ) * ‖((a+1)^(-1-k:ℤ) : ℝ)‖)`
- **What**: Explicit upper bound for `‖iteratedDerivWithin k cotTerm‖` on a vertical strip.
- **How**: Abbreviation (private).
- **Hypotheses**: `0 < B`.
- **Uses from project**: `r` (from `EisensteinSeries`).
- **Used by**: `Summable_cotTermUpperBound`, `iteratedDeriv_CotTerm_bounded_uniformly`, `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm`.
- **Visibility**: private noncomputable abbrev.
- **Lines**: 274–275.

### `private lemma Summable_cotTermUpperBound`
- **Type**: `(A B : ℝ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k) : Summable fun a : ℕ ↦ cotTermUpperBound A B hB k a`
- **What**: The upper-bound sequence is summable in `a`.
- **How**: Strip constants via `Summable.mul_left`. Use `EisensteinSeries.linear_right_summable 0 1 (k := k+1)` and the int↔nat decomposition `summable_int_iff_summable_nat_and_neg`; apply `(summable_nat_add_iff 1).mpr`; conclude `.norm.congr`.
- **Hypotheses**: `1 ≤ k`.
- **Uses from project**: `EisensteinSeries.linear_right_summable`, `cotTermUpperBound`.
- **Used by**: `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm`.
- **Visibility**: private.
- **Lines**: 277–286.

### `private lemma iteratedDeriv_CotTerm_bounded_uniformly`
- **Type**: `{k : ℕ} (hk : 1 ≤ k) (K : Set ℂ) (hK : K ⊆ {z | 0 < z.im}) (A B : ℝ) (hB : 0 < B) (HABK : inclusion hK '' univ ⊆ verticalStrip A B) (n : ℕ) (a : ℂ) (ha : a ∈ K) : ‖iteratedDerivWithin k (fun z ↦ cotTerm z n) {z | 0 < z.im} a‖ ≤ cotTermUpperBound A B hB k n`
- **What**: Uniform bound on `‖iteratedDerivWithin k cotTerm‖` over a compact `K ⊂ ℍ` contained in a vertical strip.
- **How**: Substitute closed form via `cotTerm_iteratedDerivWith'`; bound `‖a + b‖ ≤ ‖a‖ + ‖b‖`; bound each `(z ± (n+1))^(-1-k:ℤ)` using `EisensteinSeries.summand_bound_of_mem_verticalStrip` for `(1, n+1)` and `(1, -(n+1))` respectively (norms via `abs_norm_eq_max_natAbs`/`_neg`); finish with `norm_cast`.
- **Hypotheses**: `1 ≤ k`, compactness of `K` in strip.
- **Uses from project**: `cotTerm`, `cotTerm_iteratedDerivWith'`, `cotTermUpperBound`, `EisensteinSeries.summand_bound_of_mem_verticalStrip`, `abs_norm_eq_max_natAbs`, `abs_norm_eq_max_natAbs_neg`.
- **Used by**: `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm`.
- **Visibility**: private.
- **Lines**: 288–311.

### `lemma summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm`
- **Type**: `(k : ℕ) (hk : 1 ≤ k) : SummableLocallyUniformlyOn (fun n : ℕ ↦ iteratedDerivWithin k (fun z : ℂ ↦ cotTerm z n) {z | 0 < z.im}) {z | 0 < z.im}`
- **What**: Sum of iterated derivatives of `cotTerm` is locally uniformly summable on the upper half plane.
- **How**: Use `SummableLocallyUniformlyOn_of_locally_bounded`. Each compact `K ⊆ ℍ` lies in a vertical strip by `subset_verticalStrip_of_isCompact`; produce the uniform bound `cotTermUpperBound` via `iteratedDeriv_CotTerm_bounded_uniformly`; summability via `Summable_cotTermUpperBound`.
- **Hypotheses**: `1 ≤ k`.
- **Uses from project**: `SummableLocallyUniformlyOn_of_locally_bounded`, `UpperHalPlane_isOpen`, `cotTerm`, `cotTermUpperBound`, `Summable_cotTermUpperBound`, `iteratedDeriv_CotTerm_bounded_uniformly`, `subset_verticalStrip_of_isCompact`.
- **Used by**: `aux_iteratedDeriv_tsum_cotTerm`.
- **Visibility**: public.
- **Lines**: 313–325.

### `theorem iteratedDeriv_cotTerm_DifferentiableOn`
- **Type**: `(n l : ℕ) : DifferentiableOn ℂ (iteratedDerivWithin l (fun z ↦ cotTerm z n) {z | 0 < z.im}) {z | 0 < z.im}`
- **What**: The `l`-th iterated derivative of `cotTerm` is differentiable on the upper half plane.
- **How**: Show the closed form is differentiable: `DifferentiableOn.const_mul` and `DifferentiableOn.add`/`DifferentiableOn.zpow`; nonzero `z ± (n+1)` from `UpperHalfPlane.ne_int`. Transfer via `cotTerm_iteratedDerivWith'`.
- **Hypotheses**: none.
- **Uses from project**: `cotTerm`, `cotTerm_iteratedDerivWith'`, `UpperHalfPlane.ne_int`.
- **Used by**: `aux_iteratedDeriv_tsum_cotTerm`.
- **Visibility**: public.
- **Lines**: 327–340.

### `private theorem aux_summable_add`
- **Type**: `(k : ℕ) (hk : 1 ≤ k) (x : ℍ) : Summable fun (n : ℕ) ↦ ((x : ℂ) + (n + 1))^(-1 - k : ℤ)`
- **What**: Summability of `1/(x + n + 1)^(k+1)` over naturals for `x ∈ ℍ`, `k ≥ 1`.
- **How**: Reduce via `EisensteinSeries.linear_right_summable x 1 (k := k+1)` and `summable_int_iff_summable_nat_and_neg.mp`; `summable_nat_add_iff 1` to shift.
- **Hypotheses**: `1 ≤ k`.
- **Uses from project**: `EisensteinSeries.linear_right_summable`.
- **Used by**: `aux_iteratedDeriv_tsum_cotTerm`.
- **Visibility**: private.
- **Lines**: 342–346.

### `private theorem aux_summable_neg`
- **Type**: same but with `(x : ℂ) - (n + 1)`.
- **What**: Symmetric summability statement with negative shift.
- **How**: Same as `aux_summable_add` using the other component of `summable_int_iff_summable_nat_and_neg`.
- **Hypotheses**: `1 ≤ k`.
- **Uses from project**: `EisensteinSeries.linear_right_summable`.
- **Used by**: `aux_iteratedDeriv_tsum_cotTerm`.
- **Visibility**: private.
- **Lines**: 348–352.

### `private theorem aux_iteratedDeriv_tsum_cotTerm`
- **Type**: `(k : ℕ) (hk : 1 ≤ k) (x : ℍ) : (-1)^k · k! · (x : ℂ)^(-1-k:ℤ) + iteratedDerivWithin k (fun z : ℂ ↦ ∑' n : ℕ, cotTerm z n) {z | 0 < z.im} x = (-1)^k · k! · ∑' n : ℤ, ((x : ℂ) + n)^(-1-k:ℤ)`
- **What**: Bridges the iterated derivative of `∑' n, cotTerm z n` to a closed-form Eisenstein-style sum over ℤ.
- **How**: Apply `iteratedDerivWithin_tsum` (using `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm` per order, summability via `Summable_cotTerm`, per-term differentiability via `iteratedDeriv_cotTerm_DifferentiableOn`). Rewrite each summand by `cotTerm_iteratedDerivWith'`. Use `tsum_of_add_one_of_neg_add_one` to split ℕ-sum into positive/negative branches; `Summable.tsum_add` to combine; finish with `ring`.
- **Hypotheses**: `1 ≤ k`.
- **Uses from project**: `cotTerm`, `Summable_cotTerm`, `iteratedDerivWithin_tsum`, `UpperHalPlane_isOpen`, `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm`, `iteratedDeriv_cotTerm_DifferentiableOn`, `cotTerm_iteratedDerivWith'`, `aux_summable_add`, `aux_summable_neg`, `coe_mem_integerComplement`.
- **Used by**: `cot_series_rep_deriv`.
- **Visibility**: private.
- **Lines**: 354–372.

### `theorem cot_series_rep_deriv`
- **Type**: `(k : ℕ) (hk : 1 ≤ k) (z : ℍ) : iteratedDerivWithin k (fun x ↦ π · Complex.cot (π · x) - 1/x) {z | 0 < z.im} z = -(-1)^k · k! · (z : ℂ)^(-1-k:ℤ) + (-1)^k · k! · ∑' n : ℤ, ((z : ℂ) + n)^(-1-k:ℤ)`
- **What**: The k-th iterated derivative of `π cot(πx) − 1/x` on the upper half plane equals the algebraic combination.
- **How**: Reduce via `aux_iteratedDeriv_tsum_cotTerm`; use `iteratedDerivWithin_congr` to replace `cotTerm` sum representation via `cot_series_rep'`.
- **Hypotheses**: `1 ≤ k`.
- **Uses from project**: `cotTerm`, `aux_iteratedDeriv_tsum_cotTerm`, `cot_series_rep'`, `UpperHalfPlane.coe_mem_integerComplement`.
- **Used by**: `cot_series_rep_iteratedDeriv`.
- **Visibility**: public.
- **Lines**: 375–383.

### `theorem cot_pi_z_contDiffWithinAt`
- **Type**: `(k : ℕ) (z : ℍ) : ContDiffWithinAt ℂ k (fun x ↦ (↑π * x).cot) {z | 0 < z.im} (z : ℂ)`
- **What**: `cot(πz)` is `C^k`-smooth on the upper half plane.
- **How**: Unfold `Complex.cot = cos/sin`, apply `ContDiffWithinAt.div`, use `fun_prop`; nonvanishing of `sin(πz)` via `sin_pi_z_ne_zero` and `UpperHalfPlane.coe_mem_integerComplement`.
- **Hypotheses**: none.
- **Uses from project**: `sin_pi_z_ne_zero`, `UpperHalfPlane.coe_mem_integerComplement`.
- **Used by**: `cot_series_rep_deriv2`.
- **Visibility**: public.
- **Lines**: 385–392.

### `theorem cot_series_rep_deriv2`
- **Type**: `(k : ℕ) (z : ℍ) : iteratedDerivWithin k (fun x ↦ π · cot(πx) − 1/x) {z | 0 < z.im} z = iteratedDerivWithin k (fun x ↦ π · cot(πx)) {z | 0 < z.im} z − (-1)^k · k! · (z : ℂ)^(-1-k:ℤ)`
- **What**: Splits the iterated derivative of `π cot(πx) − 1/x` into `iteratedDerivWithin k (πcot(πx))` minus the iterated derivative of `1/x`.
- **How**: Rewrite `−` as `+ −`; apply `iteratedDerivWithin_fun_add` (smoothness via `cot_pi_z_contDiffWithinAt` and `ContDiffWithinAt.inv` for `1/x`). Use `iteratedDerivWithin_one_div` for the closed form of derivative of `1/x`, and `iteratedDerivWithin_fun_neg` for the sign.
- **Hypotheses**: none.
- **Uses from project**: `iteratedDerivWithin_fun_add`, `cot_pi_z_contDiffWithinAt`, `iteratedDerivWithin_one_div`, `UpperHalPlane_isOpen`, `ne_zero`.
- **Used by**: `cot_series_rep_iteratedDeriv`.
- **Visibility**: public.
- **Lines**: 394–410.

### `theorem cot_series_rep_iteratedDeriv`
- **Type**: `(k : ℕ) (hk : 1 ≤ k) (z : ℍ) : iteratedDerivWithin k (fun x ↦ π · cot(πx)) {z | 0 < z.im} z = (-1)^k · k! · ∑' n : ℤ, ((z : ℂ) + n)^(-1-k:ℤ)`
- **What**: Closed form for the `k`-th iterated derivative of `π cot(πz)` on `ℍ`.
- **How**: Combine `cot_series_rep_deriv` (closed form of `π cot − 1/x`) with `cot_series_rep_deriv2` (separation), then `add_left_inj` against the `1/x` polar term to isolate the `π cot(πz)` derivative; `ring` finishes.
- **Hypotheses**: `1 ≤ k`.
- **Uses from project**: `cot_series_rep_deriv`, `cot_series_rep_deriv2`.
- **Used by**: `cot_series_rep_iteratedDeriv_one_div`.
- **Visibility**: public.
- **Lines**: 412–418.

### `theorem cot_series_rep_iteratedDeriv_one_div`
- **Type**: `(k : ℕ) (hk : 1 ≤ k) (z : ℍ) : iteratedDerivWithin k (fun x ↦ π · cot(πx)) {z | 0 < z.im} z = (-1)^k · k! · ∑' n : ℤ, 1 / ((z : ℂ) + n)^(k+1)`
- **What**: Same closed form, rewritten with `1/(·)^(k+1)` instead of zpow `(-1-k)`.
- **How**: `simp` with `cot_series_rep_iteratedDeriv` and the identity `−1 − (k : ℤ) = −(k + 1)` to swap zpow and reciprocal-of-positive-pow representations.
- **Hypotheses**: `1 ≤ k`.
- **Uses from project**: `cot_series_rep_iteratedDeriv`.
- **Used by**: `Eisenstein_qExpansion_identity`.
- **Visibility**: public.
- **Lines**: 420–426.

### `abbrev cup` and notation `ℍₒ`
- **Type**: `cup : Set ℂ := {z : ℂ | 0 < z.im}`; local notation `ℍₒ` for `cup`.
- **What**: Convenient abbreviation for the open upper half plane as a subset of ℂ.
- **How**: Plain abbrev plus local notation.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `exp_iter_deriv_within`, `exp_iter_deriv_within2`, `qExpansion_summableLocallyUniformlyOn`, `qExpansion_summableLocallyUniformlyOn2`, `cot_q_ext_summableLocallyUniformlyOn`, `exp_deriv4`.
- **Visibility**: public.
- **Lines**: 428–430.

### `lemma exp_iter_deriv_within`
- **Type**: `(k m : ℕ) (f : ℕ → ℂ) (p : ℝ) : EqOn (iteratedDerivWithin k (fun s : ℂ ↦ (f m) · exp(2πi · m · s / p)) ℍₒ) (fun s ↦ (f m) · (2πi · m / p)^k · exp(2πi · m · s / p)) ℍₒ`
- **What**: Iterated within-derivative of `(f m) · exp(λ s)` (with `λ = 2πi·m/p`) is `(f m) · λ^k · exp(λ s)`.
- **How**: `iteratedDerivWithin_of_isOpen` to pass to `iteratedDeriv`, then `iteratedDeriv_const_mul`, `iteratedDeriv_cexp_const_mul`; `ring_nf`.
- **Hypotheses**: none.
- **Uses from project**: `UpperHalPlane_isOpen`.
- **Used by**: `qExpansion_summableLocallyUniformlyOn`, `exp_deriv4`.
- **Visibility**: public.
- **Lines**: 432–444.

### `lemma exp_iter_deriv_within2`
- **Type**: `(k m : ℕ) (p : ℝ) : EqOn (iteratedDerivWithin k (fun s : ℂ ↦ exp(2πi · m · s / p)) ℍₒ) (fun s ↦ (2πi · m / p)^k · exp(2πi · m · s / p)) ℍₒ`
- **What**: Same as previous but without the leading scalar `f m`.
- **How**: Same as `exp_iter_deriv_within`.
- **Hypotheses**: none.
- **Uses from project**: `UpperHalPlane_isOpen`.
- **Used by**: `qExpansion_summableLocallyUniformlyOn2`.
- **Visibility**: public.
- **Lines**: 446–456.

### `theorem summable_norm_mul_geometric_of_norm_lt_one'`
- **Type**: `{F : Type*} [NormedRing F] [NormOneClass F] [NormMulClass F] {k : ℕ} {r : F} (hr : ‖r‖ < 1) {u : ℕ → F} (hu : u =O[atTop] (fun n ↦ ((n^k : ℕ) : F))) : Summable fun n : ℕ ↦ ‖u n * r ^ n‖`
- **What**: When `‖r‖ < 1` and `u n = O(n^k)`, the sum `∑ ‖u n · r^n‖` converges.
- **How**: Choose `r' ∈ (‖r‖, 1)` and use `summable_of_isBigO_nat` against `r'^n`. Chain `IsBigO`s: `‖u n · r^n‖ =O ‖u n‖ · ‖r‖^n =O n^k · ‖r‖^n =O r'^n` via `isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt`.
- **Hypotheses**: `‖r‖ < 1`, polynomial growth of `u`.
- **Uses from project**: [].
- **Used by**: `qExpansion_summableLocallyUniformlyOn`, `qExpansion_summableLocallyUniformlyOn2`.
- **Visibility**: public.
- **Lines**: 478–495.
- **Notes**: 18-line proof in `calc` style.

### `lemma aux_IsBigO_mul`
- **Type**: `(k : ℕ) (p : ℝ) {f : ℕ → ℂ} (hf : f =O[atTop] (fun n => (↑(n^k) : ℝ))) : (fun n => f n * (2πi · n / p)^k) =O[atTop] (fun n => (↑(n^(2*k)) : ℝ))`
- **What**: Polynomial growth product: `f(n) · (linear)^k = O(n^(2k))` given `f = O(n^k)`.
- **How**: Show `(2πi · n / p)^k =O n^k` by factoring constants and using `Asymptotics.isBigO_const_mul_self`. Multiply with `hf`; `ring` finishes.
- **Hypotheses**: polynomial growth of `f`.
- **Uses from project**: [].
- **Used by**: `qExpansion_summableLocallyUniformlyOn`.
- **Visibility**: public.
- **Lines**: 497–510.

### `lemma aux_IsBigO_mul2`
- **Type**: `(k l : ℕ) (p : ℝ) {f : ℕ → ℂ} (hf : f =O[atTop] (fun n => (↑(n^l) : ℝ))) : (fun n => f n * (2πi · n / p)^k) =O[atTop] (fun n => (↑(n^(l + k)) : ℝ))`
- **What**: Generalization of `aux_IsBigO_mul` with separate `l` and `k`.
- **How**: Same as `aux_IsBigO_mul`.
- **Hypotheses**: polynomial growth.
- **Uses from project**: [].
- **Used by**: `qExpansion_summableLocallyUniformlyOn2`.
- **Visibility**: public.
- **Lines**: 512–525.

### `lemma exp_nsmul'`
- **Type**: `(x a p : ℂ) (n : ℕ) : exp (a * n * x / p) = exp (a * x / p) ^ n`
- **What**: Power-law for complex exponential: `exp(a·n·x/p) = (exp(a·x/p))^n`.
- **How**: `Complex.exp_nsmul` rewrite, then `ring_nf`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `qExpansion_summableLocallyUniformlyOn`, `qExpansion_summableLocallyUniformlyOn2`, `exp_deriv4`.
- **Visibility**: public.
- **Lines**: 527–529.

### `theorem qExpansion_summableLocallyUniformlyOn`
- **Type**: `(k : ℕ) {f : ℕ → ℂ} {p : ℝ} (hp : 0 < p) (hf : f =O[atTop] (fun n => (↑(n^k) : ℝ))) : SummableLocallyUniformlyOn (fun n ↦ iteratedDerivWithin k (fun z ↦ f n * cexp(2πi · z / p)^n) ℍₒ) ℍₒ`
- **What**: q-expansion-style sum of `iteratedDerivWithin k (f n · exp(2πi z / p)^n)` is locally uniformly summable on `ℍ`.
- **How**: `SummableLocallyUniformlyOn_of_locally_bounded` on `K` compact in `ℍ`. Compactness + `norm_lt_iff_of_compact` + `norm_exp_two_pi_I_lt_one` for upper half plane gives `‖r‖ < 1` where `r` is the sup norm of `exp(2πi z / p)` over `K`. Combine `summable_norm_mul_geometric_of_norm_lt_one'` with `aux_IsBigO_mul`. Per-element bound via `exp_iter_deriv_within` and `pow_le_pow_left₀` of `mkOfCompact`.
- **Hypotheses**: `0 < p`, polynomial growth of `f`.
- **Uses from project**: `SummableLocallyUniformlyOn_of_locally_bounded`, `UpperHalPlane_isOpen`, `UpperHalfPlane.norm_exp_two_pi_I_lt_one`, `summable_norm_mul_geometric_of_norm_lt_one'`, `aux_IsBigO_mul`, `exp_iter_deriv_within`, `exp_nsmul'`, `cup`.
- **Used by**: `cot_q_ext_summableLocallyUniformlyOn`.
- **Visibility**: public.
- **Lines**: 532–558.
- **Notes**: 27 lines; opens `BoundedContinuousFunction`.

### `theorem qExpansion_summableLocallyUniformlyOn2`
- **Type**: `(k l : ℕ) {f : ℕ → ℂ} {p : ℝ} (hp : 0 < p) (hf : f =O[atTop] (fun n => (↑(n^l) : ℝ))) : SummableLocallyUniformlyOn (fun n ↦ (f n) • iteratedDerivWithin k (fun z ↦ cexp(2πi · z / p)^n) ℍₒ) ℍₒ`
- **What**: Variant where the coefficient `f n` is applied via `•` outside `iteratedDerivWithin`, allowing different power growth `l`.
- **How**: Same structure as `qExpansion_summableLocallyUniformlyOn`, using `aux_IsBigO_mul2` and `exp_iter_deriv_within2`.
- **Hypotheses**: same.
- **Uses from project**: `SummableLocallyUniformlyOn_of_locally_bounded`, `UpperHalPlane_isOpen`, `UpperHalfPlane.norm_exp_two_pi_I_lt_one`, `summable_norm_mul_geometric_of_norm_lt_one'`, `aux_IsBigO_mul2`, `exp_iter_deriv_within2`, `exp_nsmul'`, `cup`.
- **Used by**: `a3334`.
- **Visibility**: public.
- **Lines**: 561–589.
- **Notes**: 29 lines.

### `theorem cot_q_ext_summableLocallyUniformlyOn`
- **Type**: `(k : ℕ) : SummableLocallyUniformlyOn (fun n ↦ iteratedDerivWithin k (fun z ↦ cexp(2πi · z)^n) ℍₒ) ℍₒ`
- **What**: Special case of `qExpansion_summableLocallyUniformlyOn` with `f n = 1`, `p = 1`.
- **How**: `simpa using qExpansion_summableLocallyUniformlyOn k (p := 1) (by norm_num) h0` where `h0 : (fun _ : ℕ => 1) =O[atTop] (fun n => (↑(n^k) : ℝ))`.
- **Hypotheses**: none.
- **Uses from project**: `qExpansion_summableLocallyUniformlyOn`.
- **Used by**: `exp_deriv'`, `tsum_uexp_contDiffOn`.
- **Visibility**: public.
- **Lines**: 591–599.

### `theorem deriv_iterderivwithin`
- **Type**: `(n a : ℕ) {s : Set ℂ} (hs : IsOpen s) {r : ℂ} (hr : r ∈ s) : DifferentiableAt ℂ (iteratedDerivWithin a (fun z ↦ cexp(2πi · z)^n) s) r`
- **What**: Iterated within-derivative of `exp(2πi · z)^n` is differentiable at every point of an open set.
- **How**: Reduce to `iteratedDeriv` via `iteratedDerivWithin_of_isOpen`, then `fun_prop` plus `IsOpen.mem_nhds`.
- **Hypotheses**: `s` open, `r ∈ s`.
- **Uses from project**: [].
- **Used by**: `exp_deriv'`, `tsum_uexp_contDiffOn`.
- **Visibility**: public.
- **Lines**: 601–607.

### `lemma exp_deriv'`
- **Type**: `(k : ℕ) (z : ℍ) : iteratedDerivWithin k (fun z ↦ ∑' n : ℕ, exp(2πi · z)^n) {z | 0 < z.im} z = ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ ↦ exp(2πi · s)^n) {z | 0 < z.im} z`
- **What**: Iterated within-derivative commutes with `∑'` for the geometric `exp(2πi·z)^n` series.
- **How**: `iteratedDerivWithin_tsum k UpperHalPlane_isOpen` with summability from `summable_geometric_iff_norm_lt_one.mpr (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨x, hx⟩)`, derivative summability from `cot_q_ext_summableLocallyUniformlyOn`, and per-term differentiability from `deriv_iterderivwithin`.
- **Hypotheses**: none beyond `z : ℍ`.
- **Uses from project**: `iteratedDerivWithin_tsum`, `UpperHalPlane_isOpen`, `UpperHalfPlane.norm_exp_two_pi_I_lt_one`, `cot_q_ext_summableLocallyUniformlyOn`, `deriv_iterderivwithin`.
- **Used by**: `tsum_uexp_contDiffOn`, `exp_deriv`.
- **Visibility**: public.
- **Lines**: 609–617.

### `theorem tsum_uexp_contDiffOn`
- **Type**: `(k : ℕ) : ContDiffOn ℂ k (fun z : ℂ ↦ ∑' n : ℕ, exp(2πi · z)^n) ℍₒ`
- **What**: The function `∑' exp(2πi·z)^n = 1/(1 - q)` (geometric series in `q := exp(2πi z)`) is `C^k`-smooth on `ℍ`.
- **How**: Use `contDiffOn_of_differentiableOn_deriv`. For each order `m`, the partial-sum derivatives are differentiable by `summableUniformlyOn_differentiableOn` (using `cot_q_ext_summableLocallyUniformlyOn`) and the answer matches via `exp_deriv'`.
- **Hypotheses**: none.
- **Uses from project**: `summableUniformlyOn_differentiableOn`, `UpperHalPlane_isOpen`, `cot_q_ext_summableLocallyUniformlyOn`, `deriv_iterderivwithin`, `exp_deriv'`, `cup`.
- **Used by**: `exp_deriv`.
- **Visibility**: public.
- **Lines**: 619–625.

### `lemma exp_deriv`
- **Type**: `{k : ℕ} (hk : 1 ≤ k) (z : ℍ) : iteratedDerivWithin k (fun z ↦ (π · i) - (2π · i) · ∑' n : ℕ, exp(2π · i · z)^n) {z | 0 < z.im} z = -(2π · i) · ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ ↦ exp(2π · i · s)^n) {z | 0 < z.im} z`
- **What**: Iterated within-derivative of `π i − 2π i · ∑' exp(2π i z)^n` strips the constant, sign, and constant factor.
- **How**: Chain `iteratedDerivWithin_const_sub hk`, `iteratedDerivWithin_fun_neg`, `iteratedDerivWithin_const_mul` (passing the unique-diff and contDiffWithinAt hypotheses), then use `exp_deriv'`.
- **Hypotheses**: `1 ≤ k`.
- **Uses from project**: `exp_deriv'`, `tsum_uexp_contDiffOn`, `UpperHalPlane_isOpen`.
- **Used by**: `exp_deriv4`.
- **Visibility**: public.
- **Lines**: 627–637.

### `lemma exp_deriv4`
- **Type**: `{k : ℕ} (hk : 1 ≤ k) (z : ℍ) : iteratedDerivWithin k (fun z ↦ (π · i) − (2π · i) · ∑' n, exp(2π · i · z)^n) ℍₒ z = -(2π · i)^(k+1) · ∑' n : ℕ, n^k · exp(2π · i · z)^n`
- **What**: Closed form for the same iterated derivative, showing the result equals `−(2πi)^(k+1) · ∑' n^k · q^n`.
- **How**: Reduce via `exp_deriv hk z`; rewrite the constant prefactor `−(2πi · (2πi)^k) = −(2πi) · (2πi)^k` and use `exp_iter_deriv_within` (specialized to `f = 1`, `p = 1`) to evaluate per-term `iteratedDerivWithin`.
- **Hypotheses**: `1 ≤ k`.
- **Uses from project**: `exp_deriv`, `exp_iter_deriv_within`, `exp_nsmul'`, `cup`.
- **Used by**: `Eisenstein_qExpansion_identity`.
- **Visibility**: public.
- **Lines**: 639–659.
- **Notes**: 21 lines.

### `theorem Eisenstein_qExpansion_identity`
- **Type**: `{k : ℕ} (hk : 1 ≤ k) (z : ℍ) : (-1)^k · k! · ∑' n : ℤ, 1 / ((z : ℂ) + n)^(k+1) = -(2π · i)^(k+1) · ∑' n : ℕ, n^k · cexp(2π · i · z)^n`
- **What**: Eisenstein-style identity equating the Eisenstein lattice sum to a `q`-expansion sum.
- **How**: Cross-rewrite via `exp_deriv4 hk z` and `cot_series_rep_iteratedDeriv_one_div k hk z`; conclude with `iteratedDerivWithin_congr` and `pi_mul_cot_pi_q_exp` which equates `π cot(πz)` with the q-expansion expression.
- **Hypotheses**: `1 ≤ k`.
- **Uses from project**: `exp_deriv4`, `cot_series_rep_iteratedDeriv_one_div`, `pi_mul_cot_pi_q_exp`.
- **Used by**: `Eisenstein_qExpansion_identity'`.
- **Visibility**: public.
- **Lines**: 661–668.

### `theorem Eisenstein_qExpansion_identity'`
- **Type**: `{k : ℕ} (hk : 1 ≤ k) (z : ℍ) : ∑' n : ℤ, 1 / ((z : ℂ) + n)^(k+1) = ((-2π · i)^(k+1) / k!) · ∑' n : ℕ, n^k · cexp(2π · i · z)^n`
- **What**: Rearranged version: divide by `(-1)^k · k!` to clear coefficients on the lattice side.
- **How**: Invoke `Eisenstein_qExpansion_identity hk z`, use `eq_inv_mul_iff_mul_eq₀`; manipulate constants via `← neg_pow`, `field_simp`, `ring_nf`; finish with `Nat.mul_two`.
- **Hypotheses**: `1 ≤ k`.
- **Uses from project**: `Eisenstein_qExpansion_identity`.
- **Used by**: `Eisenstein_qExpansion_identity''`.
- **Visibility**: public.
- **Lines**: 670–685.

### `lemma tsum_pnat_eq_tsum_succ4`
- **Type**: `{α : Type*} [TopologicalSpace α] [AddCommGroup α] [IsTopologicalAddGroup α] [T2Space α] (f : ℕ → α) (hf : Summable f) : f 0 + ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f n`
- **What**: Reindex a ℕ-sum as `f 0` plus the sum over `ℕ+`.
- **How**: `Summable.tsum_eq_zero_add hf` plus `tsum_pnat_eq_tsum_succ`.
- **Hypotheses**: `Summable f`.
- **Uses from project**: [].
- **Used by**: `Eisenstein_qExpansion_identity''`.
- **Visibility**: public.
- **Lines**: 687–690.

### `def mapdiv`
- **Type**: `(n : ℕ+) : Nat.divisorsAntidiagonal n → ℕ+ × ℕ+`
- **What**: Maps a divisor-antidiagonal pair into `ℕ+ × ℕ+` by repackaging the divisor and quotient.
- **How**: `Nat.fst_mem_divisors_of_mem_antidiagonal` / `snd_mem_divisors_of_mem_antidiagonal` give positivity certificates.
- **Hypotheses**: `n : ℕ+`, pair from antidiagonal.
- **Uses from project**: [].
- **Used by**: `sigmaAntidiagonalEquivProd`, `as1`, `tsum_sigma_eqn22`.
- **Visibility**: public def.
- **Lines**: 694–698.

### `def sigmaAntidiagonalEquivProd`
- **Type**: `(Σ n : ℕ+, Nat.divisorsAntidiagonal n) ≃ ℕ+ × ℕ+`
- **What**: Equivalence: pairs `(n, (k,l))` with `kl = n, n > 0` correspond bijectively to `(k, l) ∈ ℕ+ × ℕ+`.
- **How**: `toFun = mapdiv x.1 x.2`; `invFun (k, l) = ⟨⟨k·l, _⟩, (k, l), _⟩`. Left/right inverses checked by `rintro`/`simp`/`Nat.mem_divisorsAntidiagonal`.
- **Hypotheses**: none.
- **Uses from project**: `mapdiv`.
- **Used by**: `tsum_sigma_eqn22`, `as1`.
- **Visibility**: public def.
- **Lines**: 700–716.

### `theorem sigma_eq_sum_div'`
- **Type**: `(k n : ℕ) : sigma k n = ∑ d ∈ Nat.divisors n, (n / d) ^ k`
- **What**: Sum-of-divisors function as a divisor-quotient sum.
- **How**: Unfold `sigma`; `ArithmeticFunction.coe_mk`; reverse-sum via `Nat.sum_div_divisors`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `tsum_sigma_eqn22`.
- **Visibility**: public.
- **Lines**: 718–719.

### `theorem a3334`
- **Type**: `(k : ℕ) (e : ℕ+) (z : ℍ) : Summable fun c : ℕ => (c : ℂ)^k · exp(2π · i · e · z)^c`
- **What**: For each `e ∈ ℕ+, k ∈ ℕ`, the series `∑ c^k · q^c` (with `q = exp(2π i e z)`) is summable.
- **How**: Apply `qExpansion_summableLocallyUniformlyOn2 0 k (p := 1)` with `f n = n^k`. Convert resulting `SummableLocallyUniformlyOn` to pointwise summability at `e · z` (whose imaginary part is `e · z.im > 0`) via `.summable he`; congruence via `Complex.exp_nsmul`, `iteratedDerivWithin_zero`, `Pi.smul_apply`, and `ring_nf`.
- **Hypotheses**: none.
- **Uses from project**: `qExpansion_summableLocallyUniformlyOn2`.
- **Used by**: `Eisenstein_qExpansion_identity''`, `summable_auxil_13`.
- **Visibility**: public.
- **Lines**: 721–732.

### `theorem Eisenstein_qExpansion_identity''`
- **Type**: `{k : ℕ} (hk : 1 ≤ k) (z : ℍ) : ∑' n : ℤ, 1 / ((z : ℂ) + n)^(k+1) = ((-2π · i)^(k+1) / k!) · ∑' n : ℕ+, n^k · cexp(2π · i · z)^(n : ℕ)`
- **What**: Same identity as `'`, now indexed by `ℕ+` (excluding `n = 0`).
- **How**: From `Eisenstein_qExpansion_identity'`, drop the `n = 0` term via `tsum_pnat_eq_tsum_succ4` (zeroth term is `0^k = 0` for `k ≠ 0`); summability via `a3334 k 1 z`.
- **Hypotheses**: `1 ≤ k`.
- **Uses from project**: `Eisenstein_qExpansion_identity'`, `tsum_pnat_eq_tsum_succ4`, `a3334`.
- **Used by**: `EQ1`.
- **Visibility**: public.
- **Lines**: 734–743.

### `theorem summable_auxil_13`
- **Type**: `(k : ℕ) (z : ℍ) : Summable fun c : (n : ℕ+) × { x // x ∈ (n : ℕ).divisorsAntidiagonal } ↦ (c.2.1).1 ^ k * cexp(2π · i · c.2.1.2 · z)^c.2.1.1`
- **What**: Auxiliary summability over the dependent Σ-type `Σ n, divisorsAntidiagonal n`.
- **How**: Use `summable_sigma_of_nonneg`. Fintype-sum over each fiber. Bound by `(b : ℕ).card_divisors · ‖exp(…)‖^b`, then dominate by `a3334 (k+1) 1 z` (via `Summable.of_nonneg_of_le`). Manipulations include `Finset.sum_attach`, `Nat.sum_divisorsAntidiagonal`, `Complex.exp_nsmul`, `Nat.le_of_dvd`, `Nat.card_divisors_le_self`.
- **Hypotheses**: none.
- **Uses from project**: `a3334`.
- **Used by**: `as1`, `tsum_sigma_eqn22`.
- **Visibility**: public.
- **Lines**: 745–771.
- **Notes**: 27 lines.

### `theorem as1`
- **Type**: `(k : ℕ) (z : ℍ) : Summable fun c : ℕ+ × ℕ+ ↦ (c.1^k : ℂ) · exp(2π · i · c.2 · z)^(c.1 : ℕ)`
- **What**: Two-index summability `∑ (a,b), a^k · exp(2π i b z)^a`.
- **How**: Use `sigmaAntidiagonalEquivProd.summable_iff.symm`; reduce to `summable_auxil_13`.
- **Hypotheses**: none.
- **Uses from project**: `sigmaAntidiagonalEquivProd`, `mapdiv`, `summable_auxil_13`.
- **Used by**: `tsum_sigma_eqn22`.
- **Visibility**: public.
- **Lines**: 773–777.

### `theorem tsum_sigma_eqn22`
- **Type**: `(k : ℕ) (z : ℍ) : ∑' d : ℕ+, ∑' c : ℕ+, (c^k : ℂ) · exp(2π · i · d · z)^(c : ℕ) = ∑' e : ℕ+, sigma k e · exp(2π · i · z)^(e : ℕ)`
- **What**: Reorganization of the double sum into a sigma-function-weighted q-expansion.
- **How**: Convert outer-sum `Summable.tsum_prod (as1 k z)` then `Summable.tsum_comm`; rewrite each fiber as `∑ over (n : ℕ).divisorsAntidiagonal` via `sigmaAntidiagonalEquivProd.tsum_eq`; identify `sigma k n = ∑ d∣n, (n/d)^k` (`sigma_eq_sum_div'`); collect exponentials via `Complex.exp_nsmul`, `Nat.div_mul_cancel`, and `Nat.sum_divisorsAntidiagonal'`.
- **Hypotheses**: none.
- **Uses from project**: `as1`, `sigmaAntidiagonalEquivProd`, `mapdiv`, `summable_auxil_13`, `sigma_eq_sum_div'`.
- **Used by**: `EQ1`.
- **Visibility**: public.
- **Lines**: 779–805.
- **Notes**: 27 lines.

### `theorem int_nat_sum`
- **Type**: `{α : Type*} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α] [CompleteSpace α] (f : ℤ → α) : Summable f → Summable fun x : ℕ => f x`
- **What**: ℤ-summability implies ℕ-summability (positive branch).
- **How**: `summable_int_iff_summable_nat_and_neg`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 807–812.

### `theorem pnat_multipliable_iff_multipliable_succ'`
- **Type**: `{α R : Type*} [AddMonoidWithOne R] [TopologicalSpace α] [CommMonoid α] {f : R → α} : Multipliable (fun x : ℕ+ => f x) ↔ Multipliable fun x : ℕ => f (x + 1)`
- **What**: `ℕ+`-multipliability iff multipliability indexed by `ℕ` with shift `x + 1`.
- **How**: `Equiv.pnatEquivNat.symm.multipliable_iff.symm`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 814–818.

### `theorem pnat_summable_iff_summable_succ'`
- **Type**: `{α R : Type*} [AddMonoidWithOne R] [TopologicalSpace α] [AddCommMonoid α] {f : R → α} : Summable (fun x : ℕ+ => f x) ↔ Summable fun x : ℕ => f (x + 1)`
- **What**: ℕ+-summability iff ℕ-summability with shift.
- **How**: `Equiv.pnatEquivNat.symm.summable_iff.symm`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 820–823.

### `theorem tprod_pnat_eq_tprod_succ2`
- **Type**: `{R α : Type*} [AddMonoidWithOne R] [TopologicalSpace α] [CommMonoid α] (f : R → α) : ∏' n : ℕ+, f n = ∏' n : ℕ, f (n + 1)`
- **What**: ℕ+-product equals ℕ-product with shift.
- **How**: `Equiv.pnatEquivNat.symm.tprod_eq`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 825–828.

### `theorem tsum_pnat_eq_tsum_succ2`
- **Type**: `{R α : Type*} [AddMonoidWithOne R] [TopologicalSpace α] [AddCommMonoid α] (f : R → α) : ∑' n : ℕ+, f n = ∑' n : ℕ, f (n + 1)`
- **What**: ℕ+-sum equals ℕ-sum with shift.
- **How**: `Equiv.pnatEquivNat.symm.tsum_eq`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `sum_int_even`, `tsum_int_inv_eq_two_riemannZeta`.
- **Visibility**: public.
- **Lines**: 830–833.

### `theorem sum_int_even`
- **Type**: `{α : Type*} [UniformSpace α] [Ring α] [IsUniformAddGroup α] [CompleteSpace α] [T2Space α] {f : ℤ → α} (hf : ∀ n : ℤ, f n = f (-n)) (hf2 : Summable f) : ∑' n, f n = f 0 + 2 * ∑' n : ℕ+, f n`
- **What**: Sum of an even ℤ-series equals `f(0) + 2 · ∑ f(n)` over positives.
- **How**: `tsum_of_add_one_of_neg_add_one`. Replace negative branch by positive via evenness `f n = f(-n)`. Reindex `(n+1)` ↔ `ℕ+` via `tsum_pnat_eq_tsum_succ2`; collect via `abel`.
- **Hypotheses**: evenness, summability.
- **Uses from project**: `tsum_pnat_eq_tsum_succ2`.
- **Used by**: `tsum_int_inv_eq_two_riemannZeta`, `EQ1`.
- **Visibility**: public.
- **Lines**: 835–846.

### `lemma tsum_int_inv_eq_two_riemannZeta`
- **Type**: `{k : ℕ} (hk : 2 ≤ k) (hk2 : Even k) : ∑' (n : ℤ), ((n : ℂ)^k)⁻¹ = 2 · riemannZeta k`
- **What**: Two-sided Riemann zeta identity: `∑_{n ∈ ℤ} 1/n^k = 2 ζ(k)` for even `k ≥ 2`.
- **How**: `sum_int_even` with evenness `((-n)^k)⁻¹ = (n^k)⁻¹` (using `Even.neg_pow`) and summability of `1/n^k` on ℤ (from `Summable.of_nat_of_neg`). Reduce to `zeta_eq_tsum_one_div_nat_add_one_cpow` via `tsum_pnat_eq_tsum_succ2`.
- **Hypotheses**: `2 ≤ k`, `Even k`.
- **Uses from project**: `sum_int_even`, `tsum_pnat_eq_tsum_succ2`.
- **Used by**: `EQ1`.
- **Visibility**: public lemma.
- **Lines**: 848–857.

### `theorem int_sum_neg`
- **Type**: `{α : Type*} [AddCommMonoid α] [TopologicalSpace α] (f : ℤ → α) : ∑' d, f (-d) = ∑' d, f d`
- **What**: Re-indexing `d ↦ -d` preserves the ℤ-sum.
- **How**: Apply `(Equiv.neg ℤ).tsum_eq`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `EQ1`.
- **Visibility**: public.
- **Lines**: 859–862.

### `theorem s1`
- **Type**: `(k : ℕ) (hk : 3 ≤ k) (z : ℍ) : Summable fun x : ℤ × ℤ ↦ 1 / (↑x.1 · (z : ℂ) + ↑x.2)^k`
- **What**: For `k ≥ 3`, the 2D lattice sum `∑_{(a,b)} 1/(a z + b)^k` is summable on the upper half plane.
- **How**: Reindex `ℤ × ℤ ≃ Fin 2 → ℤ` via `(piFinTwoEquiv _).summable_iff`. Apply `summable_norm_iff` and `EisensteinSeries.summable_norm_eisSummand`; congruence via `EisensteinSeries.eisSummand`.
- **Hypotheses**: `3 ≤ k`.
- **Uses from project**: `EisensteinSeries.summable_norm_eisSummand`, `EisensteinSeries.eisSummand`.
- **Used by**: `EQ1`.
- **Visibility**: public.
- **Lines**: 864–868.

### `lemma EQ1`
- **Type**: `(k : ℕ) (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) : ∑' (x : Fin 2 → ℤ), 1 / (x 0 · (z : ℂ) + x 1)^k = 2 · riemannZeta k + 2 · ((-2π · i)^k / (k-1)!) · ∑' (n : ℕ+), (σ (k-1) n : ℂ) · cexp(2π · i · z)^(n : ℕ)`
- **What**: Q-expansion of the holomorphic Eisenstein series `E_k`: lattice sum equals `2ζ(k) + 2 · (-2πi)^k/(k-1)! · ∑_n σ_{k-1}(n) q^n`.
- **How**: Reindex `Fin 2 → ℤ` via `piFinTwoEquiv`. Decompose `∑_{(a,b)}` as `∑_a ∑_b` via `Summable.tsum_prod` (using `s1 k hk`); use `sum_int_even` (evenness from `Even.neg_pow hk2`). The `a = 0` branch is `∑_{b ≠ 0} 1/b^k = 2ζ(k)` (via `tsum_int_inv_eq_two_riemannZeta`). The `a ≠ 0` branches are paired by `int_sum_neg` and rewritten via `Eisenstein_qExpansion_identity''` at `a · z`, then collected via `tsum_sigma_eqn22`.
- **Hypotheses**: `3 ≤ k`, even.
- **Uses from project**: `s1`, `sum_int_even`, `tsum_int_inv_eq_two_riemannZeta`, `int_sum_neg`, `Eisenstein_qExpansion_identity''`, `tsum_sigma_eqn22`.
- **Used by**: `E_k_q_expansion`.
- **Visibility**: public.
- **Lines**: 870–896.
- **Notes**: 27 lines. The central q-expansion identity.

### `def gammaSetN`
- **Type**: `(N : ℕ) : Set (Fin 2 → ℤ) := ({N} : Set ℕ) • gammaSet 1 0`
- **What**: The set of `(a,b)` of the form `N · (a', b')` with `(a', b')` coprime (in `gammaSet 1 0`).
- **How**: `Pointwise` scalar multiplication of `{N}` and `gammaSet 1 0`.
- **Hypotheses**: none.
- **Uses from project**: `gammaSet`.
- **Used by**: `gammaSetN_map`, `gammaSetN_map_eq`, `gammaSetN_Equiv`, `gammaSetN_eisSummand`, `fin_to_GammaSetN`, `GammaSet_one_Equiv`, `EQ22`.
- **Visibility**: public.
- **Lines**: 900.

### `noncomputable def gammaSetN_map`
- **Type**: `(N : ℕ) (v : gammaSetN N) : gammaSet 1 0`
- **What**: Given `v ∈ gammaSetN N`, recover the underlying coprime pair `(a', b') ∈ gammaSet 1 0` (so `v = N · (a', b')`).
- **How**: Pick from `mem_smul_set` via `Exists.choose`.
- **Hypotheses**: none.
- **Uses from project**: `gammaSetN`, `gammaSet`.
- **Used by**: `gammaSetN_map_eq`, `gammaSetN_Equiv`, `gammaSetN_eisSummand`, `EQ22`.
- **Visibility**: public.
- **Lines**: 902–905.

### `lemma gammaSet_top_mem`
- **Type**: `(v : Fin 2 → ℤ) : v ∈ gammaSet 1 0 ↔ IsCoprime (v 0) (v 1)`
- **What**: A pair lies in `gammaSet 1 0` iff its components are coprime.
- **How**: `simpa [gammaSet]`; `Subsingleton.eq_zero` resolves the ZMod 1 obligation.
- **Hypotheses**: none.
- **Uses from project**: `gammaSet`.
- **Used by**: `fin_to_GammaSetN`, `GammaSet_one_Equiv`.
- **Visibility**: public.
- **Lines**: 907–908.

### `lemma gammaSetN_map_eq`
- **Type**: `{N : ℕ} (v : gammaSetN N) : v.1 = N • gammaSetN_map N v`
- **What**: Recovers the equation `v = N · gammaSetN_map N v` (from `Exists.choose_spec`).
- **How**: Unfold via `singleton_smul, mem_smul_set, nsmul_eq_mul`; access `Exists.choose_spec.2`.
- **Hypotheses**: none.
- **Uses from project**: `gammaSetN`, `gammaSetN_map`.
- **Used by**: `gammaSetN_Equiv`, `gammaSetN_eisSummand`.
- **Visibility**: public.
- **Lines**: 910–913.

### `noncomputable def gammaSetN_Equiv`
- **Type**: `{N : ℕ} (hN : N ≠ 0) : gammaSetN N ≃ gammaSet 1 0`
- **What**: For `N ≠ 0`, scalar multiplication by `N` is a bijection between `gammaSet 1 0` and `gammaSetN N`.
- **How**: `toFun = gammaSetN_map`; `invFun v = N • v ∈ gammaSetN N`. Inverses: `gammaSetN_map_eq` for left; reproducing the `Exists.choose` for right.
- **Hypotheses**: `N ≠ 0`.
- **Uses from project**: `gammaSetN`, `gammaSet`, `gammaSetN_map`, `gammaSetN_map_eq`.
- **Used by**: `EQ22`.
- **Visibility**: public (noncomputable).
- **Lines**: 915–933.
- **Notes**: 19 lines.

### `lemma gammaSetN_eisSummand`
- **Type**: `(k : ℤ) (z : ℍ) {n : ℕ} (v : gammaSetN n) : eisSummand k v z = ((n : ℂ)^k)⁻¹ · eisSummand k (gammaSetN_map n v) z`
- **What**: Factorization of the Eisenstein summand at a vector of `gammaSetN n` into `n^{-k}` times the summand of the underlying coprime pair.
- **How**: Unfold `eisSummand`, substitute `gammaSetN_map_eq`; manipulate `Pi.smul_apply`, `nsmul_eq_mul`, `Int.cast_mul`; absorb constants into a single `zpow` via `← mul_inv, ← mul_zpow`; `ring_nf`.
- **Hypotheses**: none.
- **Uses from project**: `eisSummand`, `gammaSetN`, `gammaSetN_map`, `gammaSetN_map_eq`.
- **Used by**: `EQ22`.
- **Visibility**: public lemma.
- **Lines**: 935–939.

### `private def fin_to_GammaSetN`
- **Type**: `(v : Fin 2 → ℤ) : Σ n : ℕ, gammaSetN n`
- **What**: Each `(a, b) ∈ Fin 2 → ℤ` corresponds to its gcd `n` and a coprime divisor pair `(a/n, b/n) ∈ gammaSetN n`.
- **How**: For `(v 0).gcd (v 1) > 0`, use `Set.smul_mem_smul` and `Int.gcd_div_gcd_div_gcd`; for zero gcd, `(v 0, v 1) = (0, 0)`, send to `gammaSetN 0` with `![1, 1]`.
- **Hypotheses**: none.
- **Uses from project**: `gammaSetN`, `gammaSet_top_mem`.
- **Used by**: `GammaSet_one_Equiv`.
- **Visibility**: private.
- **Lines**: 941–949.

### `def GammaSet_one_Equiv`
- **Type**: `(Fin 2 → ℤ) ≃ Σ n : ℕ, gammaSetN n`
- **What**: Full ℤ²-lattice decomposes as the disjoint union, over gcds `n ∈ ℕ`, of `n · {(a',b') | gcd(a',b') = 1}`.
- **How**: `toFun = fin_to_GammaSetN`; `invFun = .2`. Right/left inverses via `Int.mul_ediv_cancel'` of `Int.gcd_dvd_left/right` and unwinding `Exists.choose`.
- **Hypotheses**: none.
- **Uses from project**: `gammaSetN`, `gammaSet_top_mem`, `fin_to_GammaSetN`.
- **Used by**: `EQ22`.
- **Visibility**: public def.
- **Lines**: 951–968.

### `lemma EQ22`
- **Type**: `{k : ℕ} (hk : 3 ≤ k) (z : ℍ) : ∑' (x : Fin 2 → ℤ), eisSummand k x z = riemannZeta k · ∑' (c : gammaSet 1 0), eisSummand k c z`
- **What**: Eisenstein lattice sum factors as `ζ(k)` times the sum over coprime pairs (the "normalized" series).
- **How**: Use `GammaSet_one_Equiv.symm.tsum_eq` to reindex over `Σ n, gammaSetN n`. `zeta_nat_eq_tsum_of_gt_one` writes `ζ(k) = ∑' n, 1/n^k`. `tsum_mul_tsum_of_summable_norm` factors the product. Use `gammaSetN_eisSummand` to identify per-fiber sums via `gammaSetN_Equiv hb`. The `b = 0` fiber vanishes since `(0^k)⁻¹ = 0`. Summability via `EisensteinSeries.summable_norm_eisSummand`.
- **Hypotheses**: `3 ≤ k`.
- **Uses from project**: `gammaSetN`, `gammaSetN_map`, `gammaSetN_eisSummand`, `gammaSetN_Equiv`, `GammaSet_one_Equiv`, `gammaSet`, `EisensteinSeries.summable_norm_eisSummand`, `eisSummand`.
- **Used by**: `E_k_q_expansion`.
- **Visibility**: public.
- **Lines**: 970–993.
- **Notes**: 24 lines.

### `def standardcongruencecondition`
- **Type**: `Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0`
- **What**: The zero congruence condition mod 1 — used as the default condition for the full modular group.
- **How**: Direct `0`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `ModularForm.E`, `E_k_q_expansion`.
- **Visibility**: public.
- **Lines**: 995.

### `noncomputable def ModularForm.E`
- **Type**: `(k : ℕ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma 1) k`
- **What**: Normalized Eisenstein series of weight `k` (factor `1/2` because we sum over coprime pairs).
- **How**: `(1/2 : ℂ) • eisensteinSeries_MF (by omega) standardcongruencecondition`.
- **Hypotheses**: `3 ≤ k`.
- **Uses from project**: `eisensteinSeries_MF`, `standardcongruencecondition`.
- **Used by**: `E_k_q_expansion`.
- **Visibility**: public noncomputable.
- **Lines**: 1000–1001.

### `lemma E_k_q_expansion`
- **Type**: `{k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) : (E k hk) z = 1 + (1 / riemannZeta k) · ((-2π · i)^k / (k-1)!) · ∑' n : ℕ+, σ (k-1) n · cexp(2π · i · z)^(n : ℤ)`
- **What**: The q-expansion of the normalized Eisenstein series: `E_k(z) = 1 + (1/ζ(k)) · (-2πi)^k/(k-1)! · ∑ σ_{k-1}(n) q^n`.
- **How**: Unfold `E`, `eisensteinSeries_MF`, `eisensteinSeries_SIF`, `eisensteinSeries`, `standardcongruencecondition`. Apply `EQ1 k _ hk2 z` for the lattice-sum side and `EQ22 _ z` for the factor-out-`ζ(k)` step; use `riemannZeta_ne_zero_of_one_lt_re` to divide; conclude with `field_simp` + `ring`.
- **Hypotheses**: `3 ≤ k`, even.
- **Uses from project**: `EQ1`, `EQ22`, `ModularForm.E`, `eisensteinSeries_MF`, `eisensteinSeries_SIF`, `eisensteinSeries`, `eisensteinSeries_SIF_apply`, `standardcongruencecondition`, `eisSummand`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 1003–1020.
- **Notes**: 18 lines.

---

## File Summary

- **Total declarations**: ~52 (1 tactic-elab + 16 lemmas + 26 theorems + 8 defs/abbrevs/notations; 7 private/abbrev-private).
- **Key API**:
  - Series-of-functions toolkit: `HasSumUniformlyOn_of_bounded`, `HasSumUniformlyOn_of_cofinite_eventually`, `SummableLocallyUniformlyOn_of_locally_bounded`(`_eventually`), `derivWithin_tsum`, `iteratedDerivWithin_tsum`, `summableUniformlyOn_differentiableOn`.
  - Cotangent–lattice closed-form bridge: `cotTerm_iteratedDeriv(With)(')`, `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm`, `iteratedDeriv_cotTerm_DifferentiableOn`, `cot_series_rep_deriv(2)`, `cot_series_rep_iteratedDeriv(_one_div)`.
  - q-expansion machinery: `qExpansion_summableLocallyUniformlyOn(2)`, `cot_q_ext_summableLocallyUniformlyOn`, `tsum_uexp_contDiffOn`, `exp_deriv(')(4)`, `summable_norm_mul_geometric_of_norm_lt_one'`.
  - Eisenstein identity: `Eisenstein_qExpansion_identity(')(`'')`, `tsum_sigma_eqn22`, `EQ1`, `EQ22`, `E_k_q_expansion`.
  - Combinatorial scaffolding: `mapdiv`, `sigmaAntidiagonalEquivProd`, `sigma_eq_sum_div'`, `gammaSetN`, `gammaSetN_map`, `gammaSetN_Equiv`, `GammaSet_one_Equiv`.
  - Sum manipulation utilities: `int_nat_sum`, `pnat_summable_iff_summable_succ'`, `tsum_pnat_eq_tsum_succ2(4)`, `sum_int_even`, `tsum_int_inv_eq_two_riemannZeta`, `int_sum_neg`, `eqOn_finsetProd`, `eqOn_fun_finsetProd`, `MultipliableLocallyUniformlyOn_congr`, `summable_of_tsum_ne_zero`.
- **Unused (in this file)**: `my_sum_simp`, `HasSumUniformlyOn_of_bounded`, `HasSumUniformlyOn_of_cofinite_eventually`, `summable_of_tsum_ne_zero`, `eqOn_finsetProd`, `MultipliableLocallyUniformlyOn_congr`, `int_nat_sum`, `pnat_multipliable_iff_multipliable_succ'`, `pnat_summable_iff_summable_succ'`, `tprod_pnat_eq_tprod_succ2`, `E_k_q_expansion`. (These are likely consumed by downstream files or are mathlib-port leftovers.)
- **Sorries**: 0.
- **`set_option`s**: 0.
- **Long proofs (>30 lines)**: none above 30 lines, but several in the 18–29 range: `derivWithin_tsum` (16), `iteratedDerivWithin_tsum` (20), `cotTerm_iteratedDeriv` (17), `iteratedDeriv_CotTerm_bounded_uniformly` (24), `summable_norm_mul_geometric_of_norm_lt_one'` (18), `qExpansion_summableLocallyUniformlyOn` (27), `qExpansion_summableLocallyUniformlyOn2` (29), `exp_deriv4` (21), `summable_auxil_13` (27), `tsum_sigma_eqn22` (27), `gammaSetN_Equiv` (19), `EQ1` (27), `EQ22` (24), `E_k_q_expansion` (18).
- **One-paragraph purpose**: A self-contained ForMathlib draft providing the analytic infrastructure for q-expansions of holomorphic Eisenstein series on the upper half plane. The file delivers (i) `HasSumUniformlyOn`/`SummableLocallyUniformlyOn` toolkit, (ii) commutation theorems `derivWithin_tsum`/`iteratedDerivWithin_tsum` that swap higher-order derivatives with infinite sums under local-uniform convergence, (iii) a closed-form bridge between Eisenstein lattice sums `∑_{n ∈ ℤ} 1/(z + n)^{k+1}` and the q-expansion `∑_{n ≥ 1} n^k q^n` derived from iterated derivatives of `π cot(πz)`, (iv) reorganization of double sums via the divisors-antidiagonal equivalence to identify `∑ d, c, c^k q^{dc}` with the sigma-function q-expansion `∑_n σ_k(n) q^n`, and (v) the assembly of the normalized Eisenstein series `E_k = (1/2) · eisensteinSeries_MF` together with its q-expansion identity `E_k(z) = 1 + (1/ζ(k))·(-2πi)^k/(k-1)! · ∑ σ_{k-1}(n) q^n` for even `k ≥ 4`. CAUTION: the entire file body is currently wrapped in a `/- … -/` block comment (`-/` at line 5 closes the docstring, `/-` at line 1 opens it; matching final `-/` at line 1023), so every declaration above is inert at present; the inventory treats them as if active per the request.
