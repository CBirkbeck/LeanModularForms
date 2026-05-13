# LogDerivModularForm.lean Inventory

**Path**: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/LogDerivModularForm.lean
**Lines**: 167
**Imports**: `LeanModularForms.ForMathlib.MeromorphicBridge`, `LeanModularForms.ForMathlib.Residue`, `Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv`, `Mathlib.Analysis.Calculus.Deriv.Shift`

## Entries

### private lemma `nhdsNE_eventuallyEq_to_nhds`
- **Type**: lemma (private)
- **What**: Upgrades `f =ᶠ[𝓝[≠] z₀] g` to "eventually in 𝓝[≠] z₀, `f =ᶠ[𝓝 z] g`" — at each punctured-neighbourhood point `z`, the equality holds on a full open neighbourhood of `z`.
- **How**: `mem_nhdsWithin.mp hfg` gives open `s` with `z₀ ∈ s` and `s ∩ {z₀}ᶜ ⊆ {z | f z = g z}`. `mem_nhdsWithin.mpr ⟨s, ...⟩`. At each `z ∈ s, z ≠ z₀`, intersect `hs_open.mem_nhds hz_s` with `isOpen_compl_singleton.mem_nhds (mem_compl_singleton_iff.mpr hz_ne)` and apply `Filter.mem_of_superset`, restricting to `hs_sub`.
- **Hypotheses**: `hfg : f =ᶠ[𝓝[≠] z₀] g`.
- **Uses-from-project**: Mathlib `mem_nhdsWithin`, `isOpen_compl_singleton`, `Filter.mem_of_superset`.
- **Used by**: `logDeriv_eventually_eq_pole_decomp`.
- **Visibility**: private
- **Lines**: 57–64
- **Notes**: Standard topology lemma; the punctured-to-full neighbourhood upgrade.

### private lemma `logDeriv_zpow_mul_eq`
- **Type**: lemma (private)
- **What**: `logDeriv (fun w => (w - z₀)^n * g w) z = n / (z - z₀) + logDeriv g z` when `z ≠ z₀` and `g z ≠ 0`, `g` differentiable at `z`.
- **How**: `simp only [logDeriv_apply]`. Build `h_sub : HasDerivAt (· - z₀) 1 z` via `(hasDerivAt_id z).sub (hasDerivAt_const z z₀)` and `sub_zero`. Build `h_zpow : HasDerivAt (fun w => (w-z₀)^n) (↑n * (z-z₀)^(n-1)) z` via `(hasDerivAt_zpow n _ (Or.inl hzsub)).comp z h_sub` with `simpa`. Apply product rule: `(h_zpow.mul hgz_diff.hasDerivAt).deriv` gives `hderiv`. Then `rw [hderiv, add_div, mul_div_mul_right _ _ hgz_ne, mul_div_mul_left _ _ (zpow_ne_zero n hzsub), zpow_sub_one₀ hzsub n]`; `field_simp`.
- **Hypotheses**: `hzsub : z - z₀ ≠ 0`, `hgz_ne : g z ≠ 0`, `hgz_diff : DifferentiableAt ℂ g z`.
- **Uses-from-project**: Mathlib calculus (`logDeriv_apply`, `hasDerivAt_zpow`, `hasDerivAt_const`, `HasDerivAt.comp`, `HasDerivAt.mul`, `HasDerivAt.deriv`, `zpow_sub_one₀`, `zpow_ne_zero`).
- **Used by**: `logDeriv_eventually_eq_pole_decomp`.
- **Visibility**: private
- **Lines**: 70–84
- **Notes**: Pure calculus; product rule then field algebra.

### private lemma `logDeriv_eventually_eq_pole_decomp`
- **Type**: lemma (private)
- **What**: Near `z₀` (in `𝓝[≠] z₀`), `logDeriv f z = n / (z - z₀) + logDeriv g z`, given Mathlib's meromorphic factorization `f =ᶠ[𝓝[≠] z₀] (z - z₀)^n • g` with `g` analytic and `g z₀ ≠ 0`.
- **How**: Convert smul-form to mul-form: `hfmul : f =ᶠ[𝓝[≠] z₀] (z-z₀)^n * g z`. Upgrade with `nhdsNE_eventuallyEq_to_nhds hfmul` to get `hfmul_nhds`. Get `hg_ne_near` via `hg_an.continuousAt.eventually_ne hg_ne`. Get `hg_diff` via `hg_an.eventually_analyticAt.mono (·.differentiableAt)`. `filter_upwards` over four facts (`hfmul_nhds`, `hg_ne_near.filter_mono`, `hg_diff.filter_mono`, `self_mem_nhdsWithin`). Use `hfz_nhds.deriv_eq` and `hfz_nhds.self_of_nhds` (via `logDeriv_apply`) to substitute, then close with `logDeriv_zpow_mul_eq hzsub hgz_ne hgz_diff`.
- **Hypotheses**: `hg_an : AnalyticAt ℂ g z₀`, `hg_ne : g z₀ ≠ 0`, `hg_eq : ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀)^n • g z`.
- **Uses-from-project**: `nhdsNE_eventuallyEq_to_nhds`, `logDeriv_zpow_mul_eq`.
- **Used by**: `logDeriv_hasSimplePoleAt_of_order`, `logDeriv_residue_eq_order`.
- **Visibility**: private
- **Lines**: 89–106
- **Notes**: Mathlib's `meromorphicOrderAt_eq_int_iff` and `meromorphicOrderAt_ne_top_iff` produce factorizations in this form.

### theorem `logDeriv_hasSimplePoleAt_of_order`
- **Type**: theorem
- **What**: If `f` is meromorphic at `z₀` with finite nonzero order `n`, then `logDeriv f` has a simple pole at `z₀` with coefficient `↑n`.
- **How**: `obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hord`. Construct `HasSimplePoleAt` witness `⟨↑n, logDeriv g, hg_an.deriv.fun_div hg_an hg_ne, logDeriv_eventually_eq_pole_decomp hg_an hg_ne hg_eq⟩`.
- **Hypotheses**: `hf : MeromorphicAt f z₀`, `hord : meromorphicOrderAt f z₀ = (n : ℤ)`, `_hn : n ≠ 0` (unused in proof, kept for API).
- **Uses-from-project**: `HasSimplePoleAt`, `meromorphicOrderAt_eq_int_iff`, `logDeriv_eventually_eq_pole_decomp`.
- **Used by**: Residue side of valence formula (chain assembly).
- **Visibility**: public
- **Lines**: 116–121
- **Notes**: Direct application of the factorization. The `_hn` hypothesis is currently unused but kept in signature.

### theorem `logDeriv_residue_eq_order`
- **Type**: theorem
- **What**: `residue (logDeriv f) z₀ = ↑(meromorphicOrderAt f z₀).untop₀` when `f` is meromorphic at `z₀` with `meromorphicOrderAt f z₀ ≠ ⊤`.
- **How**: `obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_ne_top_iff hf).mp hord`. Conclude `residue_eq_of_simple_pole_decomp (hg_an.deriv.fun_div hg_an hg_ne) (logDeriv_eventually_eq_pole_decomp hg_an hg_ne hg_eq)`.
- **Hypotheses**: `hf : MeromorphicAt f z₀`, `hord : meromorphicOrderAt f z₀ ≠ ⊤`.
- **Uses-from-project**: `residue_eq_of_simple_pole_decomp`, `meromorphicOrderAt_ne_top_iff`, `logDeriv_eventually_eq_pole_decomp`.
- **Used by**: `logDeriv_residue_eq_int`; residue-side construction.
- **Visibility**: public
- **Lines**: 131–136
- **Notes**: Headline residue identity for log derivative of a meromorphic function.

### theorem `logDeriv_residue_eq_int`
- **Type**: theorem
- **What**: Variant of `logDeriv_residue_eq_order` with the order given as a concrete integer `n` — `residue (logDeriv f) z₀ = ↑n`.
- **How**: Derive `hne : meromorphicOrderAt f z₀ ≠ ⊤` from `hord : meromorphicOrderAt f z₀ = (n : ℤ)` via `WithTop.coe_ne_top`. Conclude with `logDeriv_residue_eq_order hf hne`, `hord`, and `simp` to handle `(↑n).untop₀ = n` (i.e., `WithTop.untop₀_coe`).
- **Hypotheses**: `hf : MeromorphicAt f z₀`, `hord : meromorphicOrderAt f z₀ = (n : ℤ)`.
- **Uses-from-project**: `logDeriv_residue_eq_order`.
- **Used by**: Residue computations needing the integer-form value.
- **Visibility**: public
- **Lines**: 139–146
- **Notes**: Convenience variant when order is explicitly an integer.

### theorem `logDeriv_periodic`
- **Type**: theorem
- **What**: If `f` is `c`-periodic (`f(z + c) = f z` for all `z`), then `logDeriv f` is too.
- **How**: `intro z`; `simp only [logDeriv_apply, ← deriv_comp_add_const f c z, show (fun w => f (w + c)) = f from funext hf, hf z]`.
- **Hypotheses**: `hf : ∀ z, f (z + c) = f z`.
- **Uses-from-project**: Mathlib `deriv_comp_add_const` (from `Mathlib.Analysis.Calculus.Deriv.Shift`), `logDeriv_apply`.
- **Used by**: `logDeriv_periodic_one`; T-cancellation in modular-side argument.
- **Visibility**: public
- **Lines**: 155–159
- **Notes**: One-line `simp` proof exploiting translation invariance of `deriv`.

### theorem `logDeriv_periodic_one`
- **Type**: theorem
- **What**: Specialization of `logDeriv_periodic` to period `1`: if `f(z + 1) = f z`, then `logDeriv f (z + 1) = logDeriv f z`.
- **How**: `logDeriv_periodic hf`.
- **Hypotheses**: `hf : ∀ z, f (z + (1 : ℂ)) = f z`.
- **Uses-from-project**: `logDeriv_periodic`.
- **Used by**: T-cancellation of vertical-segment integrals in the modular-side argument (level-1 modular forms).
- **Visibility**: public
- **Lines**: 163–165
- **Notes**: One-line specialization.

## File Summary

Three private helpers and five public theorems. The helpers establish the punctured-to-full-neighbourhood upgrade, the product-rule log-derivative identity for `(w - z₀)^n · g(w)`, and the eventual pole decomposition `logDeriv f z = n/(z - z₀) + logDeriv g z` from Mathlib's meromorphic factorization. The public theorems express the simple-pole structure of `logDeriv f` (`logDeriv_hasSimplePoleAt_of_order`), the residue identity `res(logDeriv f, z₀) = ord_{z₀} f` (`logDeriv_residue_eq_order` and integer variant), and periodicity inheritance from `f` to `logDeriv f` (`logDeriv_periodic`, `logDeriv_periodic_one`). These are the technical core of the residue side of the valence formula: residues of `logDeriv f` count zero-orders, and `logDeriv f` is `1`-periodic on modular forms of level 1.
