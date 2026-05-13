# WindingHomotopy.lean Inventory

### `def generalizedWindingNumber01`
- **Type**: `(γ : ℝ → ℂ) (z₀ : ℂ) : ℂ`
- **What**: The generalized winding number of `γ` around `z₀` on `[0,1]`, defined via the Cauchy principal value of the log-derivative integral.
- **How**: `(2πi)⁻¹ * limUnder (𝓝[>] 0) fun ε => ∫ t in 0..1, if ‖γ t - z₀‖ > ε then (γ t - z₀)⁻¹ * deriv γ t else 0`.
- **Hypotheses**: None (definition).
- **Uses from project**: []
- **Used by**: `generalizedWindingNumber01_eq_of_eq_on`, `gWN01_eq_of_homotopy_slice`, `windingNumber_eq_of_piecewise_homotopic_of_hyps`, `windingNumber_eq_of_piecewise_homotopic`, `WindingNumberHomotopyData`.
- **Visibility**: public (`def`).
- **Lines**: 64-66.
- **Notes**: Local `[0,1]`-specialization of `generalizedWindingNumber'` from `GeneralizedResidueTheory.Basic`, reproduced to avoid import conflict between `ForMathlib.PiecewiseC1Path` (via `HomotopyDefs`) and the basic theory file.

### `private theorem limUnder_eventually_eq_const`
- **Type**: `{f : ℝ → ℂ} {l : Filter ℝ} {c : ℂ} [l.NeBot] (h : ∀ᶠ x in l, f x = c) : l.limUnder f = c`
- **What**: If a function is eventually constant along a non-trivial filter, its `limUnder` equals that constant.
- **How**: Builds `Tendsto f l (nhds c)` by `tendsto_congr'` on `h.mono` plus `tendsto_const_nhds`; then concludes via `.limUnder_eq`.
- **Hypotheses**: `[l.NeBot]`, `h : ∀ᶠ x in l, f x = c`.
- **Uses from project**: []
- **Used by**: (unused in file — kept as auxiliary).
- **Visibility**: `private theorem`.
- **Lines**: 70-75.
- **Notes**: Self-contained utility lemma.

### `theorem continuous_integer_valued_constant`
- **Type**: `(f : ℝ → ℂ) (hf_cont : ContinuousOn f (Icc 0 1)) (hf_int : ∀ s ∈ Icc 0 1, ∃ n : ℤ, f s = n) : f 0 = f 1`
- **What**: A continuous integer-valued (in `ℂ`) function on `[0,1]` is constant; in particular agrees at the endpoints.
- **How**: Lifts `f` to `g : Icc 0 1 → ℂ`, proves `IsLocallyConstant g` by `IsLocallyConstant.iff_isOpen_fiber`: for integer-valued `y = n`, rewrites `g ⁻¹' {n} = g ⁻¹' Metric.ball n 1` using discreteness of `ℤ ↪ ℂ` (`Complex.dist_eq`, `Complex.norm_intCast`, `Int.abs_lt_one_iff`); for non-integer `y`, the fiber is empty. Concludes via `IsLocallyConstant.apply_eq_of_isPreconnected isPreconnected_univ`.
- **Hypotheses**: continuity and integer-valuedness on `[0,1]`.
- **Uses from project**: []
- **Used by**: `windingNumber_eq_of_piecewise_homotopic_of_hyps`.
- **Visibility**: public.
- **Lines**: 84-124.
- **Notes**: Proof >30 lines. Discrete-image-on-connected-set argument.

### `theorem generalizedWindingNumber01_eq_of_eq_on`
- **Type**: `(f g : ℝ → ℂ) (z₀ : ℂ) (heq_val : ∀ t ∈ Icc 0 1, f t = g t) (heq_deriv : ∀ᵐ t ∂volume.restrict (Set.uIoc 0 1), deriv f t = deriv g t) : generalizedWindingNumber01 f z₀ = generalizedWindingNumber01 g z₀`
- **What**: The generalized winding number on `[0,1]` depends only on values on `[0,1]` and derivatives a.e. on `(0,1]`.
- **How**: Unfolds the definition; `congr 1` twice reduces to integrand equality; uses `intervalIntegral.integral_congr_ae` with `Set.uIoc_of_le zero_le_one`, `ae_restrict_iff' measurableSet_Ioc`, `filter_upwards [heq_deriv]`, and rewrites by `heq_val` + the a.e. derivative equality on `Ioc 0 1 ⊆ Icc 0 1`.
- **Hypotheses**: pointwise equality on `Icc 0 1`; a.e. derivative equality on `uIoc 0 1`.
- **Uses from project**: `generalizedWindingNumber01` (this file).
- **Used by**: `gWN01_eq_of_homotopy_slice`.
- **Visibility**: public.
- **Lines**: 130-145.
- **Notes**: Underlies the homotopy slice identification.

### `structure WindingNumberHomotopyData`
- **Type**: `(z₀ : ℂ) (P : Finset ℝ) where parametric_continuity : ... ; integrality : ...`
- **What**: Bundle of the two substantial hypotheses for winding-number homotopy invariance: (1) for any continuous `H : ℝ × ℝ → ℂ` avoiding `z₀` with smooth-off-`P` slice derivatives, jointly continuous slice derivative on smooth boxes, and a uniform derivative bound `M`, the map `s ↦ gWN(H(·,s), z₀)` is `ContinuousOn (Icc 0 1)`; (2) the winding number of any closed continuous curve avoiding `z₀` is an integer.
- **How**: Structure declaration with two `Prop`-valued fields.
- **Hypotheses**: parameters `z₀ : ℂ`, `P : Finset ℝ`.
- **Uses from project**: `generalizedWindingNumber01` (this file).
- **Used by**: `windingNumber_eq_of_piecewise_homotopic`.
- **Visibility**: public (`structure`).
- **Lines**: 157-182.
- **Notes**: Hypothesis-level interface: parametric continuity comes from dominated convergence, integrality from the exponential trick.

### `private theorem gWN01_eq_of_homotopy_slice`
- **Type**: `(H : ℝ × ℝ → ℂ) (γ : ℝ → ℂ) (z₀ : ℂ) (s : ℝ) (heq : ∀ t ∈ Icc 0 1, H (t,s) = γ t) : generalizedWindingNumber01 (fun t => H (t,s)) z₀ = generalizedWindingNumber01 γ z₀`
- **What**: If slice `H(·,s)` equals `γ` on `[0,1]`, their winding numbers agree.
- **How**: Apply `generalizedWindingNumber01_eq_of_eq_on` with `heq` for values; for derivatives a.e., uses `Set.uIoc_of_le zero_le_one`, `EqOn.deriv isOpen_Ioo` on `Ioo 0 1`, and `ae_restrict_iff' measurableSet_Ioc` with `Ioo_ae_eq_Ioc`.
- **Hypotheses**: slice-pointwise equality `heq`.
- **Uses from project**: `generalizedWindingNumber01_eq_of_eq_on`, `generalizedWindingNumber01` (this file).
- **Used by**: `windingNumber_eq_of_piecewise_homotopic_of_hyps`.
- **Visibility**: `private`.
- **Lines**: 187-197.
- **Notes**: Bridges homotopy endpoint conditions to winding-number equality.

### `theorem windingNumber_eq_of_piecewise_homotopic_of_hyps`
- **Type**: `(γ₀ γ₁ : ℝ → ℂ) (z₀ : ℂ) (P : Finset ℝ) (hhom : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ z₀ P) (hn_cont : ...) (hn_int : ...) : generalizedWindingNumber01 γ₀ z₀ = generalizedWindingNumber01 γ₁ z₀`
- **What**: Winding-number homotopy invariance with explicit (unbundled) parametric-continuity and integrality hypotheses.
- **How**: Destructures `hhom` into `⟨H, hH_cont, hH0, hH1, hH_closed, hH_avoid, hH_diff, hH_deriv_cont, M, hM_bound⟩`. Sets `n s := generalizedWindingNumber01 (H(·,s)) z₀`. Derives continuity via `hn_cont`; integrality at each `s` from `hn_int`, requiring `Continuous (fun t => H (t,s))` produced by `hH_cont.comp (continuous_id.prodMk continuous_const)`. Applies `continuous_integer_valued_constant` to get `n 0 = n 1`, then `gWN01_eq_of_homotopy_slice` at `s = 0, 1` to identify endpoints with `γ₀, γ₁`.
- **Hypotheses**: piecewise-avoiding homotopy + parametric continuity + integrality.
- **Uses from project**: `PiecewiseCurvesHomotopicAvoiding` (from `HomotopyDefs`); `generalizedWindingNumber01`, `gWN01_eq_of_homotopy_slice`, `continuous_integer_valued_constant` (this file).
- **Used by**: `windingNumber_eq_of_piecewise_homotopic`.
- **Visibility**: public.
- **Lines**: 211-250.
- **Notes**: Proof >30 lines. Implements the three-step argument explicitly.

### `theorem windingNumber_eq_of_piecewise_homotopic`
- **Type**: `(γ₀ γ₁ : ℝ → ℂ) (z₀ : ℂ) (P : Finset ℝ) (hhom : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ z₀ P) (hdata : WindingNumberHomotopyData z₀ P) : generalizedWindingNumber01 γ₀ z₀ = generalizedWindingNumber01 γ₁ z₀`
- **What**: Main theorem: winding-number invariance under piecewise C¹ homotopy avoiding `z₀`, with hypotheses bundled in `WindingNumberHomotopyData`.
- **How**: Applies `windingNumber_eq_of_piecewise_homotopic_of_hyps` to `hdata.parametric_continuity` and `hdata.integrality`.
- **Hypotheses**: piecewise-avoiding homotopy + bundled data.
- **Uses from project**: `PiecewiseCurvesHomotopicAvoiding`; `windingNumber_eq_of_piecewise_homotopic_of_hyps`, `WindingNumberHomotopyData`, `generalizedWindingNumber01` (this file).
- **Used by**: (top-level public API; downstream).
- **Visibility**: public.
- **Lines**: 257-264.
- **Notes**: Clean wrapper around `_of_hyps` variant.

## File Summary

- **Total decls**: 8 (1 def, 1 structure, 6 theorems — 2 of which `private`).
- **Key API** (used 3+ in this file): `generalizedWindingNumber01` (used by every other declaration).
- **Unused in file**: `limUnder_eventually_eq_const` (private utility, unused here).
- **Sorries**: 0.
- **set_options**: none.
- **Proofs >30 lines**: `continuous_integer_valued_constant` (~40 lines), `windingNumber_eq_of_piecewise_homotopic_of_hyps` (~40 lines).
- **One-paragraph file purpose**: Establishes homotopy invariance of the generalized winding number for piecewise C¹ homotopies avoiding a base point `z₀`. Provides a local `[0,1]`-specialization of `generalizedWindingNumber'` (to dodge an import cycle with `GeneralizedResidueTheory.Basic`), a discrete-image-on-connected-domain lemma showing continuous integer-valued functions on `[0,1]` are constant, an equality-of-winding-numbers lemma under a.e.-equality of derivatives, and a bundled hypothesis structure `WindingNumberHomotopyData` packaging parametric continuity and integrality. The main theorem `windingNumber_eq_of_piecewise_homotopic` executes the standard three-step argument: `n(s)` is continuous (hypothesis), integer-valued (hypothesis), hence constant — so `n(0) = n(1)`, identified with `n(γ₀)` and `n(γ₁)` via `gWN01_eq_of_homotopy_slice`.
