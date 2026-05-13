# MeromorphicBridge.lean Inventory

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/MeromorphicBridge.lean`

---

### theorem `HasSimplePoleAt.meromorphicAt`
- Type: `{f : ℂ → ℂ} {z₀ : ℂ} (h : HasSimplePoleAt f z₀) → MeromorphicAt f z₀`
- What: Forward bridge — a simple pole is `MeromorphicAt` (in Mathlib's sense).
- How: Destructures `HasSimplePoleAt` to coefficient `c` and regular part `g`; applies `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt` with witness `z ↦ c + (z - z₀)·g z` (analytic via `analyticAt_const.add`); on the punctured nhd rewrites `f` via `hf_eq`, uses `zpow_neg_one`, `field_simp`.
- Hypotheses: existence of additive decomposition `c/(z-z₀) + g(z)` near `z₀` with `g` analytic.
- Uses-from-project: `HasSimplePoleAt`, `HasSimplePoleAt.coeff`, `HasSimplePoleAt.regularPart` (implicit destructuring), `residue` (sibling theorems).
- Used by: `meromorphicOrderAt_eq_neg_one_of_hasSimplePoleAt`, `meromorphicOrderAt_nonneg_of_hasSimplePoleAt_coeff_zero`.
- Visibility: public.
- Lines: 54-64.
- Notes: Algebraic identity `c/(z-z₀) + g(z) = (z-z₀)⁻¹·(c + (z-z₀)·g(z))` underlies the proof.

### theorem `meromorphicOrderAt_eq_neg_one_of_hasSimplePoleAt`
- Type: `(h : HasSimplePoleAt f z₀) (hc : h.coeff ≠ 0) → meromorphicOrderAt f z₀ = (-1 : ℤ)`
- What: A simple pole with nonzero leading coefficient has Mathlib meromorphic order exactly `-1`.
- How: Applies `meromorphicOrderAt_eq_int_iff h.meromorphicAt`; supplies analytic witness `z ↦ h.coeff + (z - z₀)·h.regularPart z` with value `h.coeff ≠ 0` at `z₀`; on punctured nhd uses `h.eventually_eq`, `zpow_neg_one`, `field_simp`.
- Hypotheses: `HasSimplePoleAt f z₀`; `h.coeff ≠ 0`.
- Uses-from-project: `HasSimplePoleAt.meromorphicAt`, `HasSimplePoleAt.coeff`, `HasSimplePoleAt.regularPart`, `HasSimplePoleAt.regularPart_analyticAt`, `HasSimplePoleAt.eventually_eq`.
- Used by: `meromorphicOrderAt_eq_neg_one_iff_hasSimplePoleAt_nonzero`.
- Visibility: public.
- Lines: 72-84.

### theorem `meromorphicOrderAt_nonneg_of_hasSimplePoleAt_coeff_zero`
- Type: `(h : HasSimplePoleAt f z₀) (hc : h.coeff = 0) → (0 : ℤ) ≤ meromorphicOrderAt f z₀`
- What: A simple pole with zero coefficient has non-negative order (the function is effectively analytic).
- How: Establishes `f =ᶠ[𝓝[≠] z₀] h.regularPart` by zero-substitution; rewrites via `meromorphicOrderAt_congr`; applies `analyticAt_const.meromorphicOrderAt_nonneg` to the regular part.
- Hypotheses: simple pole structure; coefficient is zero.
- Uses-from-project: `HasSimplePoleAt.regularPart`, `HasSimplePoleAt.regularPart_analyticAt`, `HasSimplePoleAt.eventually_eq`.
- Used by: `meromorphicOrderAt_eq_neg_one_iff_hasSimplePoleAt_nonzero`.
- Visibility: public.
- Lines: 88-95.

### theorem `hasSimplePoleAt_of_meromorphicAt_order_neg_one`
- Type: `(hf : MeromorphicAt f z₀) (hord : meromorphicOrderAt f z₀ = (-1 : ℤ)) → HasSimplePoleAt f z₀`
- What: Converse — Mathlib order `-1` implies the project's `HasSimplePoleAt`.
- How: Uses `meromorphicOrderAt_eq_int_iff` to get analytic factor `g`; factors `g - g(z₀)` via `natCast_le_analyticOrderAt` (after showing `analyticOrderAt ≥ 1` via `ENat.lt_one_iff_eq_zero` + `analyticOrderAt_ne_zero`), giving `g z = g z₀ + (z-z₀)·h_fn z`; refines to `⟨g z₀, h_fn, ...⟩`; on punctured nhd uses `zpow_neg_one`, `linear_combination`, `field_simp`.
- Hypotheses: `MeromorphicAt f z₀`; meromorphic order is exactly `-1`.
- Uses-from-project: `HasSimplePoleAt` constructor.
- Used by: `residue_eq_leadingCoeff_of_order_neg_one`, `meromorphicOrderAt_eq_neg_one_iff_hasSimplePoleAt_nonzero`.
- Visibility: public.
- Lines: 105-123.

### theorem `residue_eq_leadingCoeff_of_order_neg_one`
- Type: `(_hf : MeromorphicAt f z₀) (_hord : meromorphicOrderAt f z₀ = (-1:ℤ)) {g} (hg_an : AnalyticAt ℂ g z₀) (_hg_ne : g z₀ ≠ 0) (hg_eq : ∀ᶠ z in 𝓝[≠] z₀, f z = (z-z₀)^(-1:ℤ) • g z) → residue f z₀ = g z₀`
- What: At order `-1`, the project's `residue` equals the value `g(z₀)` of Mathlib's analytic factor.
- How: Factors `g z - g z₀ = (z-z₀)·h_fn z` via `natCast_le_analyticOrderAt`; builds simple-pole decomposition `f = g(z₀)/(z-z₀) + h_fn` eventually on `𝓝[≠] z₀`; invokes `residue_eq_of_simple_pole_decomp`.
- Hypotheses: `MeromorphicAt` (unused), order `-1` (unused), analytic factor `g` with eventually-equal factorization.
- Uses-from-project: `residue`, `residue_eq_of_simple_pole_decomp`.
- Used by: nothing within file.
- Visibility: public.
- Lines: 132-153.

### theorem `HasSimplePoleAt.residue_eq_coeff_of_order_neg_one`
- Type: `(h : HasSimplePoleAt f z₀) → residue f z₀ = h.coeff`
- What: The residue at a simple pole equals the pole coefficient.
- How: Direct application of project's `residue_eq_coeff h`.
- Hypotheses: `HasSimplePoleAt f z₀`.
- Uses-from-project: `residue`, `residue_eq_coeff`.
- Used by: nothing within file.
- Visibility: public.
- Lines: 159-161.

### theorem `hasSimplePoleAt_of_analyticAt`
- Type: `(hf : AnalyticAt ℂ f z₀) → HasSimplePoleAt f z₀`
- What: Trivial simple-pole structure for an analytic function (coefficient `0`).
- How: Refines to `⟨0, f, hf, ...⟩`; uses `filter_upwards [self_mem_nhdsWithin]` and `simp [zero_div]` to show `f z = 0/(z-z₀) + f z` eventually.
- Hypotheses: `f` is analytic at `z₀`.
- Uses-from-project: `HasSimplePoleAt` constructor.
- Used by: nothing within file.
- Visibility: public.
- Lines: 166-170.

### theorem `meromorphicOrderAt_eq_neg_one_iff_hasSimplePoleAt_nonzero`
- Type: `(hf : MeromorphicAt f z₀) → meromorphicOrderAt f z₀ = (-1:ℤ) ↔ ∃ h : HasSimplePoleAt f z₀, h.coeff ≠ 0`
- What: Packages forward + converse into an iff for order `-1`.
- How: Forward via `hasSimplePoleAt_of_meromorphicAt_order_neg_one`; nonzeroness via contradiction with `meromorphicOrderAt_nonneg_of_hasSimplePoleAt_coeff_zero`; backward via `meromorphicOrderAt_eq_neg_one_of_hasSimplePoleAt`.
- Hypotheses: `MeromorphicAt f z₀`.
- Uses-from-project: all four core theorems above.
- Used by: nothing within file.
- Visibility: public.
- Lines: 178-191.

---

## File Summary
- Total declarations: 7 theorems.
- Key API: bridge between project's `HasSimplePoleAt` decomposition and Mathlib's `MeromorphicAt`/`meromorphicOrderAt`; residue value bridge.
- Unused declarations within file: `residue_eq_leadingCoeff_of_order_neg_one`, `HasSimplePoleAt.residue_eq_coeff_of_order_neg_one`, `hasSimplePoleAt_of_analyticAt`, `meromorphicOrderAt_eq_neg_one_iff_hasSimplePoleAt_nonzero` — these are public API.
- Sorries: none.
- `set_option`: none.
- Long proofs (>10 lines): `hasSimplePoleAt_of_meromorphicAt_order_neg_one` (~18 lines) uses `natCast_le_analyticOrderAt` + `linear_combination`; `residue_eq_leadingCoeff_of_order_neg_one` (~21 lines) uses `residue_eq_of_simple_pole_decomp`.
- Purpose: Establishes the algebraic identity `c/(z-z₀) + g(z) = (z-z₀)⁻¹·(c + (z-z₀)·g(z))` to convert the project's additive simple-pole decomposition to Mathlib's multiplicative `MeromorphicAt` factorization, and proves both directions plus an `iff` characterisation, together with a residue-value bridge tying `residue` to the leading coefficient.
