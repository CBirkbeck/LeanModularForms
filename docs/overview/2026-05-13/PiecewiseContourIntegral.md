# PiecewiseContourIntegral.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/PiecewiseContourIntegral.lean`
Lines: 329

## Imports
- `LeanModularForms.ForMathlib.PiecewiseC1Path`
- `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`
- `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`

All declarations live in `namespace PiecewiseC1Path`.

---

### `def contourIntegral`
- **Type**: `(f : ℂ → ℂ) (γ : PiecewiseC1Path x y) : ℂ`
- **What**: Defines the contour integral of `f` along `γ` as `∫ t in 0..1, f(γ t) * deriv γ.toPath.extend t`.
- **How**: Single-line `intervalIntegral` definition.
- **Hypotheses**: none (untyped definition).
- **Uses from project**: `PiecewiseC1Path`, coercion `γ t = γ.toPath.extend t`.
- **Used by**: `contourIntegrand`, `contourIntegral_def`, `contourIntegral_neg`, `contourIntegral_add`, `contourIntegral_smul`, `contourIntegral_zero`, `contourIntegral_sub`, `contourIntegral_finset_sum`, `contourIntegral_eq_sub_of_hasDerivAt`, `contourIntegral_eq_zero_of_hasDerivAt_of_closed`.
- **Visibility**: public
- **Lines**: 52-55
- **Notes**: `noncomputable section`.

### `def contourIntegrand`
- **Type**: `(f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (t : ℝ) : ℂ`
- **What**: The contour integrand `t ↦ f(γ t) * deriv γ.toPath.extend t`, abstracted so integrability lemmas can be stated on it.
- **How**: Definition by `f (γ t) * deriv γ.toPath.extend t`.
- **Hypotheses**: none.
- **Uses from project**: `PiecewiseC1Path`.
- **Used by**: `contourIntegral_def`, `contourIntegral_add`, `contourIntegral_sub`, `contourIntegral_finset_sum`, `contourIntegrand_intervalIntegrable_of_continuousOn`.
- **Visibility**: public
- **Lines**: 57-59
- **Notes**: none.

### `theorem contourIntegral_def`
- **Type**: `(f : ℂ → ℂ) (γ : PiecewiseC1Path x y) → contourIntegral f γ = ∫ t in 0..1, contourIntegrand f γ t`
- **What**: Definitional unfolding bridging `contourIntegral` and `contourIntegrand`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `contourIntegral`, `contourIntegrand`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 61-62
- **Notes**: definitional.

### `theorem contourIntegral_neg`
- **Type**: `(f : ℂ → ℂ) (γ : PiecewiseC1Path x y) → contourIntegral (fun z => -f z) γ = -contourIntegral f γ`
- **What**: Negation rule for contour integral.
- **How**: `simp` with `neg_mul` and `intervalIntegral.integral_neg`.
- **Hypotheses**: none.
- **Uses from project**: `contourIntegral`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 67-69
- **Notes**: none.

### `theorem contourIntegral_add`
- **Type**: `(f g : ℂ → ℂ) (γ : PiecewiseC1Path x y) (hf : IntervalIntegrable (contourIntegrand f γ) volume 0 1) (hg : ... g ...) → contourIntegral (fun z => f z + g z) γ = contourIntegral f γ + contourIntegral g γ`
- **What**: Additivity of contour integral.
- **How**: `simp` distributes the `add_mul`, then `intervalIntegral.integral_add hf hg`.
- **Hypotheses**: both contour integrands integrable on `[0,1]`.
- **Uses from project**: `contourIntegral`, `contourIntegrand`.
- **Used by**: `contourIntegral_finset_sum`.
- **Visibility**: public
- **Lines**: 72-78
- **Notes**: none.

### `theorem contourIntegral_smul`
- **Type**: `(c : ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) → contourIntegral (fun z => c * f z) γ = c * contourIntegral f γ`
- **What**: Scalar-multiplication rule.
- **How**: `simp` with `mul_assoc`, then `intervalIntegral.integral_const_mul`.
- **Hypotheses**: none.
- **Uses from project**: `contourIntegral`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 81-84
- **Notes**: none.

### `theorem contourIntegral_zero`
- **Type**: `(γ : PiecewiseC1Path x y) → contourIntegral (fun _ => 0) γ = 0`
- **What**: Integral of the zero function is zero.
- **How**: `simp` with `zero_mul` and `intervalIntegral.integral_zero`.
- **Hypotheses**: none.
- **Uses from project**: `contourIntegral`.
- **Used by**: `contourIntegral_finset_sum`.
- **Visibility**: public
- **Lines**: 87-89
- **Notes**: none.

### `theorem contourIntegral_sub`
- **Type**: `(f g : ℂ → ℂ) (γ : PiecewiseC1Path x y) (hf hg : ...) → contourIntegral (fun z => f z - g z) γ = contourIntegral f γ - contourIntegral g γ`
- **What**: Subtraction rule.
- **How**: `simp` with `sub_mul`, then `intervalIntegral.integral_sub hf hg`.
- **Hypotheses**: both contour integrands integrable.
- **Uses from project**: `contourIntegral`, `contourIntegrand`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 92-98
- **Notes**: none.

### `theorem contourIntegral_finset_sum`
- **Type**: `{ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ → ℂ) (γ : PiecewiseC1Path x y) (hf : ∀ i ∈ s, IntervalIntegrable (contourIntegrand (f i) γ) volume 0 1) → contourIntegral (fun z => ∑ i ∈ s, f i z) γ = ∑ i ∈ s, contourIntegral (f i) γ`
- **What**: Finset-sum linearity of the contour integral when each summand integrand is integrable.
- **How**: Induction on `s` via `Finset.induction_on`. Empty case uses `contourIntegral_zero`. Inductive step `insert j t` shows the partial sum integrand is integrable (via `IntervalIntegrable.sum` and `Finset.sum_apply`), then applies `contourIntegral_add (f j) ...`.
- **Hypotheses**: per-summand interval-integrability.
- **Uses from project**: `contourIntegral`, `contourIntegrand`, `contourIntegral_zero`, `contourIntegral_add`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 103-140
- **Notes**: >10 lines; key lemma `IntervalIntegrable.sum`.

### `private lemma ftc_no_partition`
- **Type**: `{F f : ℂ → ℂ} (γ : PiecewiseC1Path x y) (a' b' : ℝ) (ha'b' : a' ≤ b') (hsub : Icc a' b' ⊆ Icc 0 1) (hFγ_cont : ContinuousOn (F ∘ γ.toPath.extend) (Icc 0 1)) (hFγ_deriv : ∀ t ∈ Ioo 0 1, t ∉ γ.partition → HasDerivAt ...) (h_int : ...) (hempty : γ.partition.filter (fun t => a' < t ∧ t < b') = ∅) → ∫ t in a'..b', f (γ t) * deriv γ.toPath.extend t = F (γ b') - F (γ a')`
- **What**: FTC on a sub-interval `[a',b']` containing no interior partition points: the integral telescopes to `F(γ b') - F(γ a')`.
- **How**: Applies `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`, using `hempty` (no partition point in the open interval) plus `hFγ_deriv` and an `mono_set` on `h_int`.
- **Hypotheses**: `a' ≤ b'`, sub-interval inside `[0,1]`, continuity of `F∘γ`, deriv off partition, integrability, empty partition filter.
- **Uses from project**: `PiecewiseC1Path.partition`, `PiecewiseC1Path`.
- **Used by**: `ftc_induction`.
- **Visibility**: private
- **Lines**: 152-172
- **Notes**: >10 lines; key lemma `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`.

### `private lemma partition_filter_card_lt_left`
- **Type**: `(P : Finset ℝ) {a' b' c : ℝ} (hc_part : c ∈ P) (hac : a' < c) (hcb : c < b') → (P.filter (fun t => a' < t ∧ t < c)).card < (P.filter (fun t => a' < t ∧ t < b')).card`
- **What**: Restricting the partition filter to a left sub-interval strictly decreases the filter cardinality (because `c` itself is dropped).
- **How**: `Finset.card_lt_card`, showing the left filter is a strict subset (uses `lt_trans` and excludes `c` via `lt_irrefl`).
- **Hypotheses**: `c ∈ P`, `a' < c < b'`.
- **Uses from project**: none.
- **Used by**: `ftc_induction`.
- **Visibility**: private
- **Lines**: 175-187
- **Notes**: >10 lines.

### `private lemma partition_filter_card_lt_right`
- **Type**: Same shape as above, for the right sub-interval `c < t < b'`.
- **What**: Symmetric to `partition_filter_card_lt_left`.
- **How**: Identical structure (Finset.card_lt_card, strict subset, `c` excluded).
- **Hypotheses**: `c ∈ P`, `a' < c < b'`.
- **Uses from project**: none.
- **Used by**: `ftc_induction`.
- **Visibility**: private
- **Lines**: 190-202
- **Notes**: >10 lines.

### `private lemma integrability_split`
- **Type**: `{f : ℂ → ℂ} (γ : PiecewiseC1Path x y) {a' b' c : ℝ} (ha'b' : a' ≤ b') (hsub : Icc a' b' ⊆ Icc 0 1) (hc_bds : c ∈ Icc 0 1) (h_int : ...) → IntervalIntegrable ... volume a' c ∧ IntervalIntegrable ... volume c b'`
- **What**: Splits interval-integrability from `[0,1]` to `[a',c]` and `[c,b']` using `uIcc_subset_uIcc`.
- **How**: Anonymous constructor with two `IntervalIntegrable.mono_set` calls, each using `Set.mem_uIcc_of_le`.
- **Hypotheses**: `a' ≤ b'`, sub-interval, `c` in `[0,1]`, global integrability.
- **Uses from project**: `PiecewiseC1Path`.
- **Used by**: `ftc_induction`.
- **Visibility**: private
- **Lines**: 205-219
- **Notes**: >10 lines.

### `private lemma ftc_induction`
- **Type**: `{F f : ℂ → ℂ} (γ : PiecewiseC1Path x y) (n : ℕ) (a' b' : ℝ) (hFγ_cont ...) (hFγ_deriv ...) (h_int ...) (hcard : (γ.partition.filter ...).card ≤ n) (ha'b' : a' ≤ b') (hsub : Icc a' b' ⊆ Icc 0 1) → ∫ t in a'..b', f (γ t) * deriv γ.toPath.extend t = F (γ b') - F (γ a')`
- **What**: FTC for piecewise-C1 paths by induction on the number of interior partition points: on any sub-interval with ≤ n interior partition points the integral telescopes.
- **How**: Induction on `n`. Base case `n=0`: `hcard ≤ 0` gives empty filter via `Finset.card_eq_zero`, then `ftc_no_partition`. Inductive step: case-split on whether the filter is empty (delegate to `ftc_no_partition`); otherwise pick `c` in the filter, split `[a',b'] = [a',c] ∪ [c,b']` using `integrability_split`, recurse with `partition_filter_card_lt_left/right`, combine via `intervalIntegral.integral_add_adjacent_intervals` and `ring`.
- **Hypotheses**: continuity of `F∘γ`; HasDerivAt off partition; integrability; partition-filter cardinality bound; sub-interval validity.
- **Uses from project**: `ftc_no_partition`, `integrability_split`, `partition_filter_card_lt_left`, `partition_filter_card_lt_right`, `PiecewiseC1Path.partition`.
- **Used by**: `contourIntegral_eq_sub_of_hasDerivAt`.
- **Visibility**: private
- **Lines**: 223-260
- **Notes**: >10 lines; core technical lemma; key lemma `intervalIntegral.integral_add_adjacent_intervals`.

### `theorem contourIntegral_eq_sub_of_hasDerivAt`
- **Type**: `{F f : ℂ → ℂ} (γ : PiecewiseC1Path x y) {U : Set ℂ} (hU : ∀ t ∈ Icc 0 1, γ t ∈ U) (hF : ∀ z ∈ U, HasDerivAt F (f z) z) (h_int : ...) → contourIntegral f γ = F y - F x`
- **What**: Fundamental theorem of calculus for piecewise-C1 contour integrals: if `F' = f` on the image of `γ`, the integral telescopes.
- **How**: Builds continuity of `F ∘ γ.toPath.extend` (composition) and `HasDerivAt` off the partition (via `γ.differentiable_off` + `HasDerivAt.comp_of_eq`); applies `ftc_induction γ _ 0 1` with cardinality bound `_ ≤ _.card` (existential `n`); rewrites with `γ.apply_one`, `γ.apply_zero`.
- **Hypotheses**: image of `γ` in `U`, derivative of `F` on `U`, integrability of the integrand.
- **Uses from project**: `ftc_induction`, `PiecewiseC1Path.differentiable_off`, `PiecewiseC1Path.apply_one`, `PiecewiseC1Path.apply_zero`, `contourIntegral`.
- **Used by**: `contourIntegral_eq_zero_of_hasDerivAt_of_closed`.
- **Visibility**: public
- **Lines**: 269-289
- **Notes**: >10 lines; main FTC theorem.

### `theorem contourIntegrand_intervalIntegrable_of_continuousOn`
- **Type**: `{f : ℂ → ℂ} (γ : PiecewiseC1Path x y) {K : Set ℂ} (hf_cont : ContinuousOn f K) (h_img : ∀ t ∈ Icc 0 1, γ t ∈ K) (h_deriv_int : IntervalIntegrable (deriv γ.toPath.extend) volume 0 1) → IntervalIntegrable (contourIntegrand f γ) volume 0 1`
- **What**: If `f` is continuous on a set containing the image of `γ` and `γ'` is interval-integrable, the contour integrand `f(γ t)·γ'(t)` is interval-integrable.
- **How**: Composition continuity (`hf_cont.comp γ.toPath.continuous_extend.continuousOn`) on `Icc` lifted to `uIcc` via `uIcc_of_le`, then `IntervalIntegrable.continuousOn_mul` combining continuous bounded factor with integrable derivative.
- **Hypotheses**: continuity on `K`, image in `K`, derivative integrability.
- **Uses from project**: `PiecewiseC1Path`, `contourIntegrand`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 301-315
- **Notes**: >10 lines.

### `theorem contourIntegral_eq_zero_of_hasDerivAt_of_closed`
- **Type**: `{F f : ℂ → ℂ} (γ : PiecewiseC1Path x y) (hclosed : x = y) {U : Set ℂ} (hU ...) (hF ...) (h_int ...) → contourIntegral f γ = 0`
- **What**: For a closed path (`x = y`), the FTC contour integral vanishes.
- **How**: `rw [contourIntegral_eq_sub_of_hasDerivAt γ hU hF h_int, hclosed, sub_self]`.
- **Hypotheses**: closed endpoints, image inside `U`, deriv of `F`, integrability.
- **Uses from project**: `contourIntegral_eq_sub_of_hasDerivAt`, `contourIntegral`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 318-325
- **Notes**: none.

---

## File Summary
`PiecewiseContourIntegral.lean` (329 lines, 0 sorries, 0 axioms) defines the contour integral `contourIntegral f γ := ∫₀¹ f(γ t)·γ'(t) dt` along a `PiecewiseC1Path` and proves its basic algebra (linearity, additivity, scalar multiplication, sub, Finset-sum) plus a piecewise FTC. The FTC `contourIntegral_eq_sub_of_hasDerivAt` is proven by inducting on the number of interior partition points (`ftc_induction`), splitting at each partition point and telescoping via `intervalIntegral.integral_add_adjacent_intervals`; the no-partition base case `ftc_no_partition` is standard. The closed-path corollary `contourIntegral_eq_zero_of_hasDerivAt_of_closed` plus the integrability lemma `contourIntegrand_intervalIntegrable_of_continuousOn` round out the file. Contains 2 definitions, 9 public theorems, and 5 private lemmas.
