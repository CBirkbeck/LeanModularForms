# PrincipalPart.lean Inventory

### `def poleOrderAt`
- **Type**: `(f : ℂ → ℂ) (z₀ : ℂ) : ℕ`
- **What**: Pole order at `z₀` as a natural number. Returns `n` when `meromorphicOrderAt f z₀ = -n` (n > 0), else `0` (analytic point, non-meromorphic, or zero of f).
- **How**: `if h : MeromorphicAt f z₀ then (-(meromorphicOrderAt f z₀).untop₀).toNat else 0`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `poleOrderAt_eq_zero_of_not_meromorphicAt`, `poleOrderAt_eq_zero_of_analyticAt`, `poleOrderAt_eq_one_of_order_neg_one`, `poleOrderAt_of_hasSimplePoleAt`
- **Visibility**: public, `noncomputable`
- **Lines**: 51-54
- **Notes**: none

### `theorem poleOrderAt_eq_zero_of_not_meromorphicAt`
- **Type**: `{f : ℂ → ℂ} {z₀ : ℂ} (h : ¬MeromorphicAt f z₀) : poleOrderAt f z₀ = 0`
- **What**: Pole order is `0` when `f` isn't meromorphic at `z₀`.
- **How**: Unfold; `dif_neg h`.
- **Hypotheses**: `¬MeromorphicAt f z₀`.
- **Uses from project**: `poleOrderAt`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 56-59
- **Notes**: none

### `theorem poleOrderAt_eq_zero_of_analyticAt`
- **Type**: `{f : ℂ → ℂ} {z₀ : ℂ} (h : AnalyticAt ℂ f z₀) : poleOrderAt f z₀ = 0`
- **What**: Analytic ⇒ pole order is 0.
- **How**: Unfold, use `dif_pos h.meromorphicAt`, then `meromorphicOrderAt_nonneg` to make `-untop₀(order)` nonpositive, so `Int.toNat` gives 0.
- **Hypotheses**: `AnalyticAt ℂ f z₀`.
- **Uses from project**: `poleOrderAt`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 61-66
- **Notes**: none

### `theorem poleOrderAt_eq_one_of_order_neg_one`
- **Type**: `{f : ℂ → ℂ} {z₀ : ℂ} (hf : MeromorphicAt f z₀) (hord : meromorphicOrderAt f z₀ = (-1 : ℤ)) : poleOrderAt f z₀ = 1`
- **What**: `meromorphicOrderAt = -1` gives pole order 1.
- **How**: Unfold, `dif_pos`, `rw [hord]`, `rfl`.
- **Hypotheses**: meromorphic at `z₀`; `meromorphicOrderAt = -1`.
- **Uses from project**: `poleOrderAt`
- **Used by**: `poleOrderAt_eq_one_of_hasSimplePoleAt`
- **Visibility**: public
- **Lines**: 68-73
- **Notes**: none

### `theorem poleOrderAt_eq_one_of_hasSimplePoleAt`
- **Type**: `{f : ℂ → ℂ} {z₀ : ℂ} (h : HasSimplePoleAt f z₀) (hc : h.coeff ≠ 0) : poleOrderAt f z₀ = 1`
- **What**: A simple pole with nonzero residue coefficient has pole order 1.
- **How**: `poleOrderAt_eq_one_of_order_neg_one h.meromorphicAt (meromorphicOrderAt_eq_neg_one_of_hasSimplePoleAt h hc)`.
- **Hypotheses**: `HasSimplePoleAt f z₀`; coefficient nonzero.
- **Uses from project**: `poleOrderAt_eq_one_of_order_neg_one`, `meromorphicOrderAt_eq_neg_one_of_hasSimplePoleAt`
- **Used by**: `poleOrderAt_of_hasSimplePoleAt`
- **Visibility**: public
- **Lines**: 75-79
- **Notes**: none

### `def principalPartSum`
- **Type**: `(S : Finset ℂ) (c : ℂ → ℂ) (z : ℂ) : ℂ`
- **What**: Principal-part sum `∑ s ∈ S, c(s) / (z - s)` for simple poles at the points of `S` with coefficients `c`.
- **How**: `∑ s ∈ S, c s / (z - s)`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `principalPartSum_empty`, `principalPartSum_singleton`, `principalPartSum_insert`, `principalPartSum_differentiableOn`, `principalPartSum_eq_term_add_rest`, `sub_principalPartSum_analyticAt`, `sub_principalPartSum_meromorphicOrderAt_nonneg`, `residue_principalPartSum`, `principalPartSum_analyticAt`, `principalPartSum_differentiableAt`, `principalPartSum_meromorphicAt`, `principalPartSum_hasSimplePoleAt`
- **Visibility**: public, `noncomputable`
- **Lines**: 88-89
- **Notes**: none

### `theorem principalPartSum_empty`
- **Type**: `(c : ℂ → ℂ) (z : ℂ) : principalPartSum ∅ c z = 0`
- **What**: Empty pole-set yields zero.
- **How**: `simp` with `Finset.sum_empty`.
- **Hypotheses**: none.
- **Uses from project**: `principalPartSum`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 91-93
- **Notes**: none

### `theorem principalPartSum_singleton`
- **Type**: `(s : ℂ) (c : ℂ → ℂ) (z : ℂ) : principalPartSum {s} c z = c s / (z - s)`
- **What**: Single-pole case reduces to the single term.
- **How**: `simp` with `Finset.sum_singleton`.
- **Hypotheses**: none.
- **Uses from project**: `principalPartSum`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 95-97
- **Notes**: none

### `theorem principalPartSum_insert`
- **Type**: `{S : Finset ℂ} {s : ℂ} (hs : s ∉ S) (c : ℂ → ℂ) (z : ℂ) : principalPartSum (insert s S) c z = c s / (z - s) + principalPartSum S c z`
- **What**: Recursion: inserting a new pole adds its principal-part term.
- **How**: `simp` with `Finset.sum_insert hs`.
- **Hypotheses**: `s ∉ S`.
- **Uses from project**: `principalPartSum`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 99-101
- **Notes**: none

### `theorem differentiableAt_div_sub`
- **Type**: `{s : ℂ} {c : ℂ} {z : ℂ} (hz : z ≠ s) : DifferentiableAt ℂ (fun w => c / (w - s)) z`
- **What**: `c/(z - s)` is differentiable away from `s`.
- **How**: `differentiableAt_const c |>.div (differentiableAt_id.sub (differentiableAt_const s)) (sub_ne_zero.mpr hz)`.
- **Hypotheses**: `z ≠ s`.
- **Uses from project**: []
- **Used by**: `differentiableOn_div_sub`, `principalPartSum_differentiableOn`
- **Visibility**: public
- **Lines**: 106-109
- **Notes**: none

### `theorem differentiableOn_div_sub`
- **Type**: `(s : ℂ) (c : ℂ) : DifferentiableOn ℂ (fun z => c / (z - s)) {s}ᶜ`
- **What**: The single-pole term is differentiable on `{s}ᶜ`.
- **How**: Pointwise from `differentiableAt_div_sub` via `mem_compl_singleton_iff`.
- **Hypotheses**: none.
- **Uses from project**: `differentiableAt_div_sub`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 112-114
- **Notes**: none

### `theorem principalPartSum_differentiableOn`
- **Type**: `(S : Finset ℂ) (c : ℂ → ℂ) : DifferentiableOn ℂ (principalPartSum S c) (↑S : Set ℂ)ᶜ`
- **What**: The full principal-part sum is differentiable away from `S`.
- **How**: Pointwise: `DifferentiableAt.differentiableWithinAt` after `DifferentiableAt.fun_sum`, each term by `differentiableAt_div_sub` (`heq ▸ hs` to invert).
- **Hypotheses**: none.
- **Uses from project**: `principalPartSum`, `differentiableAt_div_sub`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 117-123
- **Notes**: none

### `theorem sub_simplePole_analyticAt`
- **Type**: `{f : ℂ → ℂ} {z₀ : ℂ} {c : ℂ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g z₀) (hev : ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z) : ∃ h : ℂ → ℂ, AnalyticAt ℂ h z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀, f z - c / (z - z₀) = h z`
- **What**: Subtracting a simple-pole term `c/(z - z₀)` from `f` yields an analytic function (locally, near `z₀`).
- **How**: Take `h = g`; `filter_upwards [hev]` and rewrite with `ring`.
- **Hypotheses**: regular part `g` analytic; `f = c/(z-z₀) + g` near `z₀`.
- **Uses from project**: []
- **Used by**: `HasSimplePoleAt.sub_pole_analyticAt`
- **Visibility**: public
- **Lines**: 132-140
- **Notes**: none

### `theorem HasSimplePoleAt.sub_pole_analyticAt`
- **Type**: `{f : ℂ → ℂ} {z₀ : ℂ} (h : HasSimplePoleAt f z₀) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀, f z - h.coeff / (z - z₀) = g z`
- **What**: Specialization to `HasSimplePoleAt`: subtracting the simple-pole term gives an analytic remainder.
- **How**: Apply `sub_simplePole_analyticAt` with `h.regularPart_analyticAt` and `h.eventually_eq`.
- **Hypotheses**: `HasSimplePoleAt f z₀`.
- **Uses from project**: `sub_simplePole_analyticAt`
- **Used by**: `HasSimplePoleAt.sub_pole_term_meromorphicAt`
- **Visibility**: public
- **Lines**: 144-148
- **Notes**: none

### `theorem HasSimplePoleAt.sub_pole_term_meromorphicAt`
- **Type**: `{f : ℂ → ℂ} {z₀ : ℂ} (h : HasSimplePoleAt f z₀) : MeromorphicAt (fun z => f z - h.coeff / (z - z₀)) z₀`
- **What**: The function with its simple-pole term removed is meromorphic at `z₀`.
- **How**: Destruct `h.sub_pole_analyticAt`, congr from `hg_an.meromorphicAt`, finalize with `filter_upwards` and rewrite.
- **Hypotheses**: `HasSimplePoleAt f z₀`.
- **Uses from project**: `HasSimplePoleAt.sub_pole_analyticAt`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 151-157
- **Notes**: none

### `private theorem principalPartSum_rest_analyticAt`
- **Type**: `{S : Finset ℂ} {s : ℂ} (_hs : s ∈ S) (c : ℂ → ℂ) : AnalyticAt ℂ (fun z => ∑ t ∈ S.erase s, c t / (z - t)) s`
- **What**: The "other" terms (all `t ≠ s` in `S`) form a function analytic at `s`.
- **How**: `Finset.analyticAt_fun_sum`; each `t ∈ S.erase s` has `t ≠ s` (`Finset.ne_of_mem_erase`), so `analyticAt_const.div ...` with `sub_ne_zero.mpr hts.symm`.
- **Hypotheses**: `s ∈ S`.
- **Uses from project**: []
- **Used by**: `principalPartSum_eq_term_add_rest` (no), `sub_principalPartSum_analyticAt`, `residue_principalPartSum`, `principalPartSum_meromorphicAt`, `principalPartSum_hasSimplePoleAt`
- **Visibility**: private
- **Lines**: 162-168
- **Notes**: none

### `theorem principalPartSum_eq_term_add_rest`
- **Type**: `{S : Finset ℂ} {s : ℂ} (hs : s ∈ S) (c : ℂ → ℂ) (z : ℂ) : principalPartSum S c z = c s / (z - s) + ∑ t ∈ S.erase s, c t / (z - t)`
- **What**: Decomposition at a pole `s ∈ S`: principal-part-sum splits into the `s` term plus the rest.
- **How**: Unfold `principalPartSum`, apply `← Finset.add_sum_erase _ _ hs`.
- **Hypotheses**: `s ∈ S`.
- **Uses from project**: `principalPartSum`
- **Used by**: `sub_principalPartSum_analyticAt`, `residue_principalPartSum`, `principalPartSum_meromorphicAt`, `principalPartSum_hasSimplePoleAt`
- **Visibility**: public
- **Lines**: 172-176
- **Notes**: none

### `theorem sub_principalPartSum_analyticAt`
- **Type**: `{f : ℂ → ℂ} {S : Finset ℂ} {c : ℂ → ℂ} {s : ℂ} (hs : s ∈ S) (h_pole : HasSimplePoleAt f s) (h_coeff : h_pole.coeff = c s) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ ∀ᶠ z in 𝓝[≠] s, f z - principalPartSum S c z = g z`
- **What**: Subtracting the full principal-part sum from `f` is analytic at each pole `s ∈ S` when coefficients match.
- **How**: Let `rest z = ∑_{t ≠ s} c(t)/(z-t)`; analytic at `s` via `principalPartSum_rest_analyticAt`. Set `g_loc = h_pole.regularPart`. Take `g = g_loc - rest`; analytic via `hg_an.sub h_rest_an`. Eventually: `filter_upwards [h_pole.eventually_eq, self_mem_nhdsWithin]`, rewrite `principalPartSum` via `_eq_term_add_rest`, substitute `hf_eq` and `h_coeff`, finish with `ring`.
- **Hypotheses**: simple pole at `s`; coefficient match.
- **Uses from project**: `principalPartSum_rest_analyticAt`, `principalPartSum_eq_term_add_rest`, `principalPartSum`
- **Used by**: `sub_principalPartSum_meromorphicOrderAt_nonneg`
- **Visibility**: public
- **Lines**: 186-200
- **Notes**: none

### `theorem sub_principalPartSum_meromorphicOrderAt_nonneg`
- **Type**: `{f : ℂ → ℂ} {S : Finset ℂ} {c : ℂ → ℂ} {s : ℂ} (hs : s ∈ S) (h_pole : HasSimplePoleAt f s) (h_coeff : h_pole.coeff = c s) : (0 : ℤ) ≤ meromorphicOrderAt (fun z => f z - principalPartSum S c z) s`
- **What**: The remainder `f - principalPartSum` has non-negative meromorphic order at each `s ∈ S` (i.e. no pole).
- **How**: Obtain `g` analytic from `sub_principalPartSum_analyticAt`; rewrite via `meromorphicOrderAt_congr hg_eq`; finish with `hg_an.meromorphicOrderAt_nonneg`.
- **Hypotheses**: simple pole; coefficient match.
- **Uses from project**: `sub_principalPartSum_analyticAt`, `principalPartSum`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 204-211
- **Notes**: none

### `theorem residue_principalPartSum`
- **Type**: `{S : Finset ℂ} {c : ℂ → ℂ} {s : ℂ} (hs : s ∈ S) : residue (principalPartSum S c) s = c s`
- **What**: The residue of the principal-part sum at `s ∈ S` equals `c s`.
- **How**: From `principalPartSum_rest_analyticAt` get the analytic remainder; build the decomposition `principalPartSum S c z = c s / (z - s) + rest z` eventually via `filter_upwards [self_mem_nhdsWithin]` + `principalPartSum_eq_term_add_rest`; conclude with `residue_eq_of_simple_pole_decomp`.
- **Hypotheses**: `s ∈ S`.
- **Uses from project**: `principalPartSum`, `principalPartSum_rest_analyticAt`, `principalPartSum_eq_term_add_rest`, `residue_eq_of_simple_pole_decomp`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 216-224
- **Notes**: none

### `theorem residue_eq_coeff_of_hasSimplePoleAt`
- **Type**: `{f : ℂ → ℂ} {z₀ : ℂ} (h : HasSimplePoleAt f z₀) : residue f z₀ = h.coeff`
- **What**: For a simple pole, residue = coefficient.
- **How**: Forwards to `residue_eq_coeff h`.
- **Hypotheses**: `HasSimplePoleAt f z₀`.
- **Uses from project**: `residue_eq_coeff`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 227-230
- **Notes**: none

### `theorem poleOrderAt_of_hasSimplePoleAt`
- **Type**: `{f : ℂ → ℂ} {z₀ : ℂ} (h : HasSimplePoleAt f z₀) : poleOrderAt f z₀ = if h.coeff = 0 then 0 else 1`
- **What**: Simple pole: pole order is 1 if coefficient nonzero, else 0.
- **How**: `split_ifs` on coefficient. Coefficient zero: unfold `poleOrderAt`, `dif_pos`, use `meromorphicOrderAt_nonneg_of_hasSimplePoleAt_coeff_zero` and `Int.toNat_eq_zero` + `neg_nonpos_of_nonneg`. Coefficient nonzero: forwards to `poleOrderAt_eq_one_of_hasSimplePoleAt`.
- **Hypotheses**: simple pole.
- **Uses from project**: `poleOrderAt`, `poleOrderAt_eq_one_of_hasSimplePoleAt`, `meromorphicOrderAt_nonneg_of_hasSimplePoleAt_coeff_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 236-244
- **Notes**: none

### `theorem principalPartSum_analyticAt`
- **Type**: `{S : Finset ℂ} {c : ℂ → ℂ} {z : ℂ} (hz : z ∉ S) : AnalyticAt ℂ (principalPartSum S c) z`
- **What**: Principal-part sum is analytic away from `S`.
- **How**: `change` to expanded `Finset.sum` form, apply `Finset.analyticAt_fun_sum`; each summand by `analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr (heq ▸ hs))`.
- **Hypotheses**: `z ∉ S`.
- **Uses from project**: `principalPartSum`
- **Used by**: `principalPartSum_differentiableAt`, `principalPartSum_meromorphicAt`
- **Visibility**: public
- **Lines**: 249-256
- **Notes**: none

### `theorem principalPartSum_differentiableAt`
- **Type**: `{S : Finset ℂ} {c : ℂ → ℂ} {z : ℂ} (hz : z ∉ S) : DifferentiableAt ℂ (principalPartSum S c) z`
- **What**: Differentiable away from `S` (corollary of analyticity).
- **How**: `(principalPartSum_analyticAt hz).differentiableAt`.
- **Hypotheses**: `z ∉ S`.
- **Uses from project**: `principalPartSum_analyticAt`, `principalPartSum`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 259-262
- **Notes**: none

### `theorem principalPartSum_meromorphicAt`
- **Type**: `(S : Finset ℂ) (c : ℂ → ℂ) (z : ℂ) : MeromorphicAt (principalPartSum S c) z`
- **What**: Principal-part sum is meromorphic everywhere on ℂ.
- **How**: Case on `z ∈ S`. If yes: decompose as `c z / (· - z) + rest`; show first term meromorphic via `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt` with exponent `-1` (and `c z` as smul constant; `filter_upwards [self_mem_nhdsWithin]` and unfold `zpow_neg_one`, `smul_eq_mul`, `div_eq_mul_inv`, `mul_comm`); then use `h_pole.add h_rest_an.meromorphicAt` with `congr` and the eventual equality. If `z ∉ S`: `(principalPartSum_analyticAt hz).meromorphicAt`. Specific lemma: `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`.
- **Hypotheses**: none.
- **Uses from project**: `principalPartSum`, `principalPartSum_rest_analyticAt`, `principalPartSum_eq_term_add_rest`, `principalPartSum_analyticAt`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 267-285
- **Notes**: none

### `theorem principalPartSum_hasSimplePoleAt`
- **Type**: `{S : Finset ℂ} {c : ℂ → ℂ} {s : ℂ} (hs : s ∈ S) : HasSimplePoleAt (principalPartSum S c) s`
- **What**: The principal-part sum has a simple pole at every `s ∈ S`.
- **How**: Provide explicit witness `⟨c s, fun z => ∑_{t ≠ s} c t/(z-t), principalPartSum_rest_analyticAt hs c, ...⟩`; the eventual equality is `principalPartSum_eq_term_add_rest` via `filter_upwards [self_mem_nhdsWithin]`.
- **Hypotheses**: `s ∈ S`.
- **Uses from project**: `principalPartSum`, `principalPartSum_rest_analyticAt`, `principalPartSum_eq_term_add_rest`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 288-294
- **Notes**: none

## File Summary

**File**: `LeanModularForms/ForMathlib/PrincipalPart.lean` (296 lines)

Builds the **principal-part sum** infrastructure for simple poles: for a finite set `S ⊂ ℂ` of pole locations and coefficient function `c : ℂ → ℂ`, the rational function `principalPartSum S c z = ∑_{s ∈ S} c(s)/(z - s)` captures the singular part. Imports `MeromorphicBridge`. Key facts:
- `poleOrderAt` (pole order as ℕ) plus characterizations from `MeromorphicAt`/`AnalyticAt`/`HasSimplePoleAt`.
- Definition `principalPartSum`, with empty/singleton/insert recursions.
- Differentiability/analyticity away from `S` (`principalPartSum_differentiableOn`, `principalPartSum_analyticAt`).
- Subtraction theorems: at each `s ∈ S` (with matching coefficient) `f - principalPartSum` is analytic (`sub_principalPartSum_analyticAt`) and has non-negative meromorphic order (`_meromorphicOrderAt_nonneg`).
- Residue at each pole equals `c s` (`residue_principalPartSum`).
- Meromorphicity everywhere (`principalPartSum_meromorphicAt`) and explicit simple-pole structure at each `s ∈ S` (`principalPartSum_hasSimplePoleAt`).
- Bridge `residue_eq_coeff_of_hasSimplePoleAt` and pole-order classification by coefficient nonvanishing.

One private helper (`principalPartSum_rest_analyticAt`). No `sorry`, no axioms, no `set_option`. Two `noncomputable def`s.
