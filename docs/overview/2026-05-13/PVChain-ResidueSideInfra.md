# Inventory: PVChain/ResidueSideInfra.lean

### `instance _ : IsScalarTower ℝ ℂ ℂ`
- **Type**: `IsScalarTower ℝ ℂ ℂ`
- **What**: Local instance of scalar tower ℝ → ℂ → ℂ via `inferInstance`.
- **How**: `inferInstance`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file (only as instance)
- **Visibility**: private
- **Lines**: 32
- **Notes**: one-line; `attribute [local instance] Classical.propDecidable` on line 30.

### `lemma fdBox_isOpen`
- **Type**: `(M : ℝ) : IsOpen (fdBox M)`
- **What**: The fundamental-domain box `fdBox M` (rectangle `|Re| < M`, `0 < Im < M`) is open.
- **How**: `IsOpen.inter` four times, each side an `isOpen_lt` between a constant and `Complex.continuous_re`/`continuous_im`.
- **Hypotheses**: none on `M`.
- **Uses from project**: `fdBox`
- **Used by**: unused in file (consumer is downstream).
- **Visibility**: public
- **Lines**: 40–45

### `private lemma strict_convex_comb_lb`
- **Type**: `{a b x y L : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hx : L < x) (hy : L < y) : L < a * x + b * y`
- **What**: A strict convex combination of two reals each `> L` is strictly `> L`.
- **How**: Case-split `a = 0` vs `0 < a`. If `a = 0`, then `b = 1` from `hab` and result reduces to `hy`. If `a > 0`, then `a * L < a * x` and `b * L ≤ b * y`, plus `a * L + b * L = L` from `hab`; `linarith`.
- **Hypotheses**: `0 ≤ a`, `0 ≤ b`, `a + b = 1`, `L < x`, `L < y`.
- **Uses from project**: []
- **Used by**: `fdBox_convex`.
- **Visibility**: private
- **Lines**: 47–57

### `private lemma strict_convex_comb_ub`
- **Type**: `{a b x y U : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hx : x < U) (hy : y < U) : a * x + b * y < U`
- **What**: A convex combination of two reals each `< U` is strictly `< U`.
- **How**: Symmetric to `strict_convex_comb_lb`; case-split `a = 0` vs `a > 0`, then `linarith`.
- **Hypotheses**: `0 ≤ a`, `0 ≤ b`, `a + b = 1`, `x < U`, `y < U`.
- **Uses from project**: []
- **Used by**: `fdBox_convex`.
- **Visibility**: private
- **Lines**: 59–69

### `lemma fdBox_convex`
- **Type**: `(M : ℝ) : Convex ℝ (fdBox M)`
- **What**: `fdBox M` is convex.
- **How**: Unfold `fdBox`, use `add_re`/`add_im` to express the convex combination componentwise, then apply `strict_convex_comb_lb`/`ub` to each of the four bounds.
- **Hypotheses**: none.
- **Uses from project**: `fdBox`, `strict_convex_comb_lb`, `strict_convex_comb_ub`
- **Used by**: unused in file (consumer is downstream).
- **Visibility**: public
- **Lines**: 71–79

### `private lemma fdBox_im_pos'`
- **Type**: `{M : ℝ} {z : ℂ} (hz : z ∈ fdBox M) : 0 < z.im`
- **What**: A point of `fdBox M` has positive imaginary part.
- **How**: From the third conjunct of `fdBox` (`1/2 < z.im`), `linarith`.
- **Hypotheses**: `z ∈ fdBox M`.
- **Uses from project**: `fdBox`
- **Used by**: `winding_zero_for_non_fd_point_H_geo`.
- **Visibility**: private
- **Lines**: 81–82

### `noncomputable def allZerosInFdBox`
- **Type**: `{M : ℝ} (hM : (1:ℝ)/2 < M) : Finset ℂ`
- **What**: Finite set of complex zeros of `modularFormCompOfComplex f` lying in `fdBox M`.
- **How**: `Set.Finite.toFinset` of `modularForm_finitely_many_zeros_in_fdBox f hf hM`.
- **Hypotheses**: `f : ModularForm (Gamma 1) k`, `f ≠ 0`, `1/2 < M`.
- **Uses from project**: `modularForm_finitely_many_zeros_in_fdBox`
- **Used by**: `mem_allZerosInFdBox_iff`, `winding_zero_for_non_fd_point_H_geo`.
- **Visibility**: public
- **Lines**: 86–87

### `lemma mem_allZerosInFdBox_iff`
- **Type**: `{M : ℝ} (hM : (1:ℝ)/2 < M) {z : ℂ} : z ∈ allZerosInFdBox f hf hM ↔ z ∈ fdBox M ∧ modularFormCompOfComplex f z = 0`
- **What**: Membership characterization for `allZerosInFdBox`.
- **How**: `simp` unfolding `allZerosInFdBox`, `Set.Finite.mem_toFinset`, `Set.mem_sep_iff`.
- **Hypotheses**: same as definition.
- **Uses from project**: `allZerosInFdBox`, `fdBox`, `modularFormCompOfComplex`
- **Used by**: `winding_zero_for_non_fd_point_H_geo`.
- **Visibility**: public
- **Lines**: 89–91

### `private lemma analyticAt_modform`
- **Type**: `(z : ℂ) (hz : 0 < z.im) : AnalyticAt ℂ (modularFormCompOfComplex f) z`
- **What**: `modularFormCompOfComplex f` is analytic at any complex `z` with positive imaginary part.
- **How**: Apply `UpperHalfPlane.mdifferentiable_iff` to `f.holo'` and combine with `UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz` to extract `analyticAt`.
- **Hypotheses**: `0 < z.im`.
- **Uses from project**: `modularFormCompOfComplex`, `UpperHalfPlane.mdifferentiable_iff`, `UpperHalfPlane.isOpen_upperHalfPlaneSet`
- **Used by**: `analyticAt_logDeriv_off_zeros'`, `hasSimplePoleAt_logDeriv_of_zero_full`, `orderOfVanishingAt'_eq_analyticOrderNatAt`.
- **Visibility**: private
- **Lines**: 95–98

### `lemma analyticAt_logDeriv_off_zeros'`
- **Type**: `(z : ℂ) (hz : 0 < z.im) (hfz : modularFormCompOfComplex f z ≠ 0) : AnalyticAt ℂ (logDeriv (modularFormCompOfComplex f)) z`
- **What**: `logDeriv` of a modular-form-comp is analytic at any non-zero in the upper half-plane.
- **How**: `(analyticAt_modform f z hz).deriv.fun_div (analyticAt_modform ...) hfz`.
- **Hypotheses**: `0 < z.im`, `modularFormCompOfComplex f z ≠ 0`.
- **Uses from project**: `analyticAt_modform`, `modularFormCompOfComplex`
- **Used by**: `hasSimplePoleAt_logDeriv_at_nonzero`, `residueSimplePole_logDeriv_eq_zero_at_nonzero`.
- **Visibility**: public
- **Lines**: 100–103

### `private lemma modform_not_locally_zero`
- **Type**: `(s : ℍ) : analyticOrderAt (modularFormCompOfComplex f) (s : ℂ) ≠ ⊤`
- **What**: A non-zero modular form is not locally zero at any upper-half-plane point.
- **How**: Suppose `analyticOrderAt = ⊤`. From `analyticOrderAt_eq_top`, `f` is locally zero. Use preconnectedness of upper half plane (`Complex.isConnected_of_upperHalfPlane`) and `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` to conclude `f ≡ 0` globally; contradict `hf`.
- **Hypotheses**: `hf : f ≠ 0`, `s : ℍ`.
- **Uses from project**: `modularFormCompOfComplex`, `UpperHalfPlane.mdifferentiable_iff`, `UpperHalfPlane.isOpen_upperHalfPlaneSet`, `Complex.isConnected_of_upperHalfPlane`, `UpperHalfPlane.ofComplex_apply`
- **Used by**: `hasSimplePoleAt_logDeriv_of_zero_full`, `orderOfVanishingAt'_eq_analyticOrderNatAt`.
- **Visibility**: private
- **Lines**: 105–121
- **Notes**: >10 lines; key lemma `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`.

### `theorem hasSimplePoleAt_logDeriv_of_zero_full`
- **Type**: `(s : ℍ) (hs : f s = 0) : ∃ (n : ℤ) (g : ℂ → ℂ), n > 0 ∧ AnalyticAt ℂ g (s : ℂ) ∧ g (s : ℂ) ≠ 0 ∧ n = analyticOrderNatAt (modularFormCompOfComplex f) (s : ℂ) ∧ ∀ᶠ z in 𝓝 (s : ℂ), z ≠ (s : ℂ) → logDeriv (modularFormCompOfComplex f) z = n / (z - (s : ℂ)) + logDeriv g z`
- **What**: At a zero `s` of `f`, the log-derivative has Laurent decomposition `logDeriv f(z) = n/(z-s) + logDeriv g(z)` for `n = analyticOrderNatAt` and `g` analytic non-vanishing.
- **How**: Extract `(g, hg_analytic, hg_ne_zero, hg_eq)` from `h_analytic.analyticOrderAt_ne_top.mp`. Set `n` = `analyticOrderNatAt`. Then `f(z) = (z-s)^n * g(z)` near `s` and `g(s) ≠ 0`. `logDeriv` of a product: `logDeriv_mul` splits into `logDeriv (z-s)^n + logDeriv g`. The first is `n/(z-s)` by `HasDerivAt` of polynomial.
- **Hypotheses**: `hf : f ≠ 0`, `f s = 0`.
- **Uses from project**: `analyticAt_modform`, `modform_not_locally_zero`, `modularFormCompOfComplex`, `UpperHalfPlane.ofComplex_apply`
- **Used by**: `hasSimplePoleAt_logDeriv_of_zero'`, `residueSimplePole_logDeriv_eq_order`.
- **Visibility**: public
- **Lines**: 123–192
- **Notes**: >10 lines (~70); key lemmas `logDeriv_mul`, `Filter.Eventually.deriv_eq`, `HasDerivAt.pow`.

### `theorem hasSimplePoleAt_logDeriv_of_zero'`
- **Type**: `(s : ℍ) (hs : f s = 0) : HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) (s : ℂ)`
- **What**: `logDeriv f` has a `HasSimplePoleAt` at each zero `s` of `f`.
- **How**: Use `hasSimplePoleAt_logDeriv_of_zero_full` to get decomposition; package via `⟨n, logDeriv g, AnalyticAt.deriv.fun_div, eventually_nhdsWithin_iff⟩`.
- **Hypotheses**: `hf : f ≠ 0`, `f s = 0`.
- **Uses from project**: `hasSimplePoleAt_logDeriv_of_zero_full`, `modularFormCompOfComplex`
- **Used by**: `hasSimplePoleAt_logDeriv_at_point`.
- **Visibility**: public
- **Lines**: 194–203

### `lemma hasSimplePoleAt_logDeriv_at_nonzero`
- **Type**: `(z : ℂ) (hz_im : 0 < z.im) (hz_nz : modularFormCompOfComplex f z ≠ 0) : HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) z`
- **What**: At a non-zero point, `logDeriv f` trivially has `HasSimplePoleAt` (with `c = 0`, `g = logDeriv f`).
- **How**: Direct witness: `⟨0, logDeriv (modularFormCompOfComplex f), analyticAt_logDeriv_off_zeros', simp⟩`.
- **Hypotheses**: `0 < z.im`, `modularFormCompOfComplex f z ≠ 0`.
- **Uses from project**: `analyticAt_logDeriv_off_zeros'`, `modularFormCompOfComplex`
- **Used by**: `hasSimplePoleAt_logDeriv_at_point`.
- **Visibility**: public
- **Lines**: 205–213
- **Notes**: `omit hf in`.

### `lemma hasSimplePoleAt_logDeriv_at_point`
- **Type**: `(z : ℂ) (hz_im : 0 < z.im) : HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) z`
- **What**: For any `z` with `0 < z.im`, `logDeriv f` has `HasSimplePoleAt z`.
- **How**: Case-split on `modularFormCompOfComplex f z = 0`. If yes, lift `z` to `⟨z, _⟩ : ℍ` and apply `hasSimplePoleAt_logDeriv_of_zero'`; if no, apply `hasSimplePoleAt_logDeriv_at_nonzero`.
- **Hypotheses**: `hf : f ≠ 0`, `0 < z.im`.
- **Uses from project**: `hasSimplePoleAt_logDeriv_of_zero'`, `hasSimplePoleAt_logDeriv_at_nonzero`, `modularFormCompOfComplex`, `UpperHalfPlane.ofComplex_apply_of_im_pos`
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 215–225

### `private lemma orderOfVanishingAt'_eq_analyticOrderNatAt`
- **Type**: `(s : ℍ) (_hs : f s = 0) : orderOfVanishingAt' (⇑f) s = (analyticOrderNatAt (modularFormCompOfComplex f) (s : ℂ) : ℤ)`
- **What**: For a modular form zero, `orderOfVanishingAt'` agrees with the analytic order.
- **How**: Unfold `orderOfVanishingAt'`. Show the local extension `g₁ z = if 0 < z.im then f ⟨z, _⟩ else 0` is `=ᶠ[𝓝[≠] s]` to `modularFormCompOfComplex f`. Rewrite using `meromorphicOrderAt_congr` and `analyticAt.meromorphicOrderAt_eq`, case on `⊤` (impossible by `modform_not_locally_zero`).
- **Hypotheses**: `hf : f ≠ 0`, `f s = 0`.
- **Uses from project**: `orderOfVanishingAt'`, `analyticAt_modform`, `modform_not_locally_zero`, `modularFormCompOfComplex`, `UpperHalfPlane.ofComplex_apply_of_im_pos`
- **Used by**: `residueSimplePole_logDeriv_eq_order`.
- **Visibility**: private
- **Lines**: 231–248

### `theorem residueSimplePole_logDeriv_eq_order`
- **Type**: `(s : ℍ) (hs : f s = 0) : residueSimplePole (logDeriv (modularFormCompOfComplex f)) (s : ℂ) = (orderOfVanishingAt' (⇑f) s : ℂ)`
- **What**: Residue of `logDeriv f` at a zero `s` equals the (complex-cast) vanishing order.
- **How**: Decompose `logDeriv f` via `hasSimplePoleAt_logDeriv_of_zero_full`. Apply `residue_simple_pole_eq_laurent` to read off `n` as the residue. Rewrite using `orderOfVanishingAt'_eq_analyticOrderNatAt`.
- **Hypotheses**: `hf : f ≠ 0`, `f s = 0`.
- **Uses from project**: `hasSimplePoleAt_logDeriv_of_zero_full`, `residue_simple_pole_eq_laurent`, `orderOfVanishingAt'_eq_analyticOrderNatAt`, `residueSimplePole`, `modularFormCompOfComplex`, `orderOfVanishingAt'`
- **Used by**: unused in file (downstream consumer).
- **Visibility**: public
- **Lines**: 252–268

### `lemma residueSimplePole_logDeriv_eq_zero_at_nonzero`
- **Type**: `(z : ℂ) (hz_im : 0 < z.im) (hz_nz : modularFormCompOfComplex f z ≠ 0) : residueSimplePole (logDeriv (modularFormCompOfComplex f)) z = 0`
- **What**: Residue of `logDeriv f` is zero at non-zeros of `f`.
- **How**: Compute `Tendsto ((w - z) * logDeriv f w)` in the punctured nhds. Both factors tend to zero or to a finite limit, so the product tends to `0`. `limUnder_eq` gives the conclusion.
- **Hypotheses**: `0 < z.im`, `modularFormCompOfComplex f z ≠ 0`.
- **Uses from project**: `residueSimplePole`, `analyticAt_logDeriv_off_zeros'`, `modularFormCompOfComplex`
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 270–282
- **Notes**: `omit hf in`.

### `lemma fdBoundary_H_mem_fdBox'`
- **Type**: `{H M : ℝ} (hH : 1 ≤ H) (hM : H < M) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 5) : fdBoundary_H H t ∈ fdBox M`
- **What**: For `1 ≤ H < M`, the truncated fundamental-domain curve `fdBoundary_H` lies in `fdBox M` at every parameter `t ∈ [0,5]`.
- **How**: Four conjuncts: `|re| ≤ 1/2` from `fdBoundary_H_re_abs_le_half`; `im ≥ √3/2 > 1/2` from `fdBoundary_H_im_ge_sqrt3_div_2` combined with `Real.sq_sqrt`; `im ≤ H < M` from `fdBoundary_H_im_le_H`. Each established by `linarith`/`nlinarith`.
- **Hypotheses**: `1 ≤ H`, `H < M`, `t ∈ Icc 0 5`.
- **Uses from project**: `fdBoundary_H`, `fdBox`, `fdBoundary_H_re_abs_le_half`, `fdBoundary_H_im_ge_sqrt3_div_2`, `fdBoundary_H_im_le_H`
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 287–302
- **Notes**: `omit f hf in`.

### `lemma finset_discrete`
- **Type**: `(S0 : Finset ℂ) : ∀ s ∈ (↑S0 : Set ℂ), ∃ ε > 0, ∀ s' ∈ (↑S0 : Set ℂ), s' ≠ s → ε ≤ ‖s' - s‖`
- **What**: Any finset in ℂ is discrete: for each `s ∈ S0`, there's a positive separation from other elements.
- **How**: Case-split `S0.erase s` empty (trivially `ε := 1`) or nonempty (take `min'` of `(S0.erase s).image (‖· - s‖)`). Use `Finset.min'_mem` and `Finset.min'_le`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file (consumer is downstream).
- **Visibility**: public
- **Lines**: 307–322
- **Notes**: `omit f hf in`.

### `lemma cpvExists_of_off_curve`
- **Type**: `(γ : ℝ → ℂ) (hγ_cont : Continuous γ) (a b : ℝ) (s : ℂ) (c : ℂ) (hab : a ≤ b) (h_off : ∀ t ∈ Icc a b, γ t ≠ s) : CauchyPrincipalValueExists' (fun z => c / (z - s)) γ a b s`
- **What**: When the curve avoids `s`, the Cauchy principal value of `c/(z-s)` along `γ` exists as a regular integral.
- **How**: Take `δ = ‖γ t₀ - s‖` for `t₀` minimizing `‖γ · - s‖` on compact `Icc a b`. Then for small `ε < δ`, the indicator `‖γ t - s‖ > ε` is always true. `intervalIntegral.integral_congr` against `tendsto_const_nhds`.
- **Hypotheses**: `Continuous γ`, `a ≤ b`, `γ` avoids `s` on `[a,b]`.
- **Uses from project**: `CauchyPrincipalValueExists'`
- **Used by**: unused in file (consumer is downstream).
- **Visibility**: public
- **Lines**: 327–345
- **Notes**: `omit f hf in`.

### `lemma cpvExists_scale`
- **Type**: `(γ : ℝ → ℂ) (a b : ℝ) (s c : ℂ) (h : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) γ a b s) : CauchyPrincipalValueExists' (fun z => c / (z - s)) γ a b s`
- **What**: Scale the existence of CPV from `(z-s)⁻¹` to `c/(z-s)`.
- **How**: From `h`, `L` is the limit; the new limit is `c * L`. Use `intervalIntegral.integral_const_mul` (`erw`) to pull the constant `c` out, then `Tendsto.const_mul`.
- **Hypotheses**: existence of CPV for the unit pole.
- **Uses from project**: `CauchyPrincipalValueExists'`
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 348–365
- **Notes**: `omit f hf in`.

### `private lemma residueSimplePole_congr_local`
- **Type**: `(F G : ℂ → ℂ) (z₀ : ℂ) (h : F =ᶠ[𝓝[≠] z₀] G) : residueSimplePole F z₀ = residueSimplePole G z₀`
- **What**: `residueSimplePole` is congruent under germ equality at the punctured nhds.
- **How**: Unfold `residueSimplePole`; both `lim` values agree under `Filter.map_congr`.
- **Hypotheses**: `F =ᶠ[𝓝[≠] z₀] G`.
- **Uses from project**: `residueSimplePole`
- **Used by**: `residue_logDerivPatched_eq_raw`.
- **Visibility**: private
- **Lines**: 377–381
- **Notes**: `omit f hf in`.

### `noncomputable def logDerivPatched`
- **Type**: `(F : ℂ → ℂ) (S0 : Finset ℂ) (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) : ℂ → ℂ`
- **What**: Patches `F` at each `s ∈ S0` to use the analytic remainder from the simple-pole decomposition (so the limit value is the correct "regular part" rather than `0/0`).
- **How**: `fun z => if z ∈ S0 then Classical.choose (Classical.choose_spec (hsp z h)) z else F z`.
- **Hypotheses**: each `s ∈ S0` is a `HasSimplePoleAt` of `F`.
- **Uses from project**: `HasSimplePoleAt`
- **Used by**: `logDerivPatched_eq_raw_off`, `logDerivPatched_eventuallyEq_raw_punctured`, `hasSimplePoleAt_logDerivPatched`, `residue_logDerivPatched_eq_raw`, `logDerivPatched_hf_ext`.
- **Visibility**: public
- **Lines**: 384–388
- **Notes**: `omit f hf in`; classical-choice patch.

### `lemma logDerivPatched_eq_raw_off`
- **Type**: `(F : ℂ → ℂ) (S0 : Finset ℂ) (hsp) {z : ℂ} (hz : z ∉ S0) : logDerivPatched F S0 hsp z = F z`
- **What**: Outside `S0`, the patch equals `F`.
- **How**: `dif_neg hz`.
- **Hypotheses**: `z ∉ S0`.
- **Uses from project**: `logDerivPatched`
- **Used by**: `logDerivPatched_hf_ext`.
- **Visibility**: public
- **Lines**: 391–394
- **Notes**: `omit f hf in`.

### `private lemma logDerivPatched_eventuallyEq_raw_punctured`
- **Type**: `(F : ℂ → ℂ) (S0 : Finset ℂ) (hsp) (s : ℂ) (_hs : s ∈ S0) : logDerivPatched F S0 hsp =ᶠ[𝓝[≠] s] F`
- **What**: Patched logDeriv agrees with `F` on a punctured neighborhood of each pole (other poles excluded).
- **How**: `(S0.erase s)ᶜ` is open and contains `s`; for `z` in it with `z ≠ s`, `z ∉ S0` so `dif_neg` returns `F z`.
- **Hypotheses**: `s ∈ S0`.
- **Uses from project**: `logDerivPatched`
- **Used by**: `hasSimplePoleAt_logDerivPatched`, `residue_logDerivPatched_eq_raw`.
- **Visibility**: private
- **Lines**: 397–405
- **Notes**: `omit f hf in`.

### `lemma hasSimplePoleAt_logDerivPatched`
- **Type**: `(F : ℂ → ℂ) (S0 : Finset ℂ) (hsp) (s : ℂ) (hs : s ∈ S0) : HasSimplePoleAt (logDerivPatched F S0 hsp) s`
- **What**: Patched logDeriv inherits `HasSimplePoleAt` at every pole.
- **How**: From `hsp s hs` extract `(c, g, hg_an, hF_eq)`. Combine the punctured-equality of the patch with `hF_eq` to get the Laurent germ.
- **Hypotheses**: `s ∈ S0`.
- **Uses from project**: `logDerivPatched`, `logDerivPatched_eventuallyEq_raw_punctured`, `HasSimplePoleAt`
- **Used by**: unused in file (consumer is downstream).
- **Visibility**: public
- **Lines**: 408–416
- **Notes**: `omit f hf in`.

### `lemma residue_logDerivPatched_eq_raw`
- **Type**: `(F : ℂ → ℂ) (S0 : Finset ℂ) (hsp) (s : ℂ) (hs : s ∈ S0) : residueSimplePole (logDerivPatched F S0 hsp) s = residueSimplePole F s`
- **What**: Patching does not alter the residue (punctured equality preserves it).
- **How**: Direct application of `residueSimplePole_congr_local` to the punctured-EventuallyEq.
- **Hypotheses**: `s ∈ S0`.
- **Uses from project**: `residueSimplePole_congr_local`, `logDerivPatched_eventuallyEq_raw_punctured`, `residueSimplePole`, `logDerivPatched`
- **Used by**: `logDerivPatched_hf_ext`.
- **Visibility**: public
- **Lines**: 419–422
- **Notes**: `omit f hf in`.

### `lemma logDerivPatched_hf_ext`
- **Type**: `(F : ℂ → ℂ) (S0 : Finset ℂ) (hsp) : ∀ s ∈ S0, ContinuousAt (fun z => logDerivPatched F S0 hsp z - residueSimplePole (logDerivPatched F S0 hsp) s / (z - s)) s`
- **What**: The `hf_ext` continuity hypothesis required by `generalizedResidueTheorem'` holds for the patched logDeriv.
- **How**: Use `Classical.choose` to access `c, g, hg_an, hF_eq`. Show residue equals `c` via `residueSimplePole_eq_of_decomposition`/`residue_simple_pole_eq_laurent`. Then `(F z - c/(z-s)) = g z` near `s`. `ContinuousAt.congr hg_an.continuousAt`. Case-split `z = s` (using `dif_pos`) vs `z ≠ s` (using `logDerivPatched_eq_raw_off` and `hF_eq`).
- **Hypotheses**: all `s ∈ S0` are simple poles.
- **Uses from project**: `logDerivPatched`, `residueSimplePole`, `residue_logDerivPatched_eq_raw`, `residue_simple_pole_eq_laurent`, `logDerivPatched_eq_raw_off`, `HasSimplePoleAt`
- **Used by**: unused in file (consumer is downstream).
- **Visibility**: public
- **Lines**: 425–456
- **Notes**: `omit f hf in`; >10 lines (~31); key lemmas `Classical.choose_spec`, `ContinuousAt.congr`.

### `private lemma fdBoundary_H_eq_fdBoundary_on_13`
- **Type**: `(H : ℝ) {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht3 : t ≤ 3) : fdBoundary_H H t = fdBoundary t`
- **What**: On the arc range `1 < t ≤ 3`, the truncated boundary equals the basic boundary.
- **How**: Unfold both, `simp only` with `ht1`, `ht3` to collapse if-branches.
- **Hypotheses**: `1 < t ≤ 3`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary`
- **Used by**: `fdBoundary_H_norm_ge_one`.
- **Visibility**: private
- **Lines**: 461–465
- **Notes**: `omit f hf in`.

### `lemma fdBoundary_H_norm_ge_one`
- **Type**: `{H : ℝ} (hH : 1 ≤ H) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 5) : ‖fdBoundary_H H t‖ ≥ 1`
- **What**: Every point on the truncated fundamental-domain boundary curve has norm ≥ 1.
- **How**: Case-split `t ≤ 1` (vertical edge seg1: `re = 1/2`, `im ≥ √3/2`, so `normSq ≥ 1`); `1 < t ≤ 3` (arc, `‖exp(iθ)‖ = 1`); `3 < t ≤ 4` (vertical seg4 symmetric to seg1); `t > 4` (top edge `im = H ≥ 1`). Each case: `normSq_apply`, `nlinarith`, then `Real.sqrt_le_sqrt`.
- **Hypotheses**: `1 ≤ H`, `t ∈ Icc 0 5`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary`, `fdBoundary_H_eq_seg1_H`, `fdBoundary_H_eq_fdBoundary_on_13`, `fdBoundary_H_eq_seg4_H`, `fdBoundary_H_eq_seg5_H`, `fdBoundary_H_im_ge_sqrt3_div_2`, `fdBoundary_seg1_H`, `fdBoundary_seg2`, `fdBoundary_seg3`, `fdBoundary_seg4_H`, `fdBoundary_seg5_H`
- **Used by**: `off_curve_of_not_in_fd_H`, `winding_zero_for_non_fd_point_H_geo`.
- **Visibility**: public
- **Lines**: 469–539
- **Notes**: `omit f hf in`; >10 lines (~70); key lemmas `Real.mul_self_sqrt`, `Complex.normSq_apply`, `Complex.norm_exp_ofReal_mul_I`.

### `lemma off_curve_of_not_in_fd_H`
- **Type**: `{H : ℝ} (hH : 1 ≤ H) (z₀ : ℂ) (hz₀_not_fd : ¬ (|z₀.re| ≤ 1/2 ∧ ‖z₀‖ ≥ 1)) : ∀ t ∈ Icc (0:ℝ) 5, fdBoundary_H H t ≠ z₀`
- **What**: The truncated boundary avoids any point not in the closed fundamental domain (norm < 1 or |Re| > 1/2).
- **How**: Suppose `fdBoundary_H H t = z₀`. Push the negation: either `|z₀.re| > 1/2` (then contradict `fdBoundary_H_re_abs_le_half`) or `‖z₀‖ < 1` (then contradict `fdBoundary_H_norm_ge_one`).
- **Hypotheses**: `1 ≤ H`, `z₀` not in the closed FD.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_re_abs_le_half`, `fdBoundary_H_norm_ge_one`
- **Used by**: `winding_zero_for_non_fd_point_H_geo`.
- **Visibility**: public
- **Lines**: 543–552
- **Notes**: `omit f hf in`.

### `lemma ftc_integral_zero_of_closed_slit`
- **Type**: `{γ : ℝ → ℂ} {z₀ : ℂ} {ω : ℂ} (hω : ω ≠ 0) (hγ_cont : Continuous γ) (hγ_closed : γ 0 = γ 5) (h_off : ∀ t ∈ Icc 0 5, γ t ≠ z₀) (h_slit : ∀ t ∈ Icc 0 5, ω * (γ t - z₀) ∈ Complex.slitPlane) (hγ_diff : ∀ t ∉ fdBoundaryFullPartition, DifferentiableAt ℝ γ t) (hγ_deriv_cont : ∀ t ∈ Ioo 0 5, t ∉ fdBoundaryFullPartition → ContinuousAt (deriv γ) t) (hγ_deriv_bdd : ∃ Mγ, ∀ t ∈ Icc 0 5, ‖deriv γ t‖ ≤ Mγ) : ∫ t in 0..5, (γ t - z₀)⁻¹ * deriv γ t = 0`
- **What**: For a closed curve avoiding `z₀` and lying in a slit plane (so a single-valued log exists), the integral of `1/(γ-z₀) · γ'` vanishes.
- **How**: Set `F t = Complex.log (ω · (γ t - z₀))`. Then `F' t = (γ t - z₀)⁻¹ · γ'(t)` by `Complex.hasDerivAt_log` composed with `HasDerivAt.const_mul`. Apply `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le` with the finite partition. `F 5 - F 0 = 0` by `hγ_closed`.
- **Hypotheses**: closed curve, off-curve avoidance, slit-plane condition, piecewise differentiability, bounded derivative.
- **Uses from project**: `fdBoundaryFullPartition`, `continuousOn_image_bounded`, `aEStronglyMeasurable_of_continuousOn_off_finite`, `integrableOn_of_bounded_aeMeasurable`
- **Used by**: `winding_zero_for_non_fd_point_H_geo`.
- **Visibility**: public
- **Lines**: 556–623
- **Notes**: `omit f hf in`; >10 lines (~68); key lemma `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`.

### `lemma winding_zero_for_non_fd_point_H_geo`
- **Type**: `(S : Finset UpperHalfPlane) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) {H : ℝ} (hH : 1 ≤ H) (z₀ : ℂ) (hz₀_zero : z₀ ∈ allZerosInFdBox f hf (...)) (hz₀_not_S : ∀ s ∈ S, (s : ℂ) ≠ z₀) : generalizedWindingNumber' (fdBoundary_H H) 0 5 z₀ = 0`
- **What**: If `z₀` is a zero in fdBox but not equivalent to any point of the registered `S` (e.g. obtained via `T`/`S` orbits), then its winding number around the truncated FD boundary vanishes — the residue side picks up only `S` itself.
- **How**: Show `z₀ ∉ 𝒟` (otherwise `orderOfVanishingAt' ≠ 0` forces `z₀ ∈ S`). Then `off_curve_of_not_in_fd_H` applies. Use `generalizedWindingNumber_eq_classical_away` to drop to classical form. The integral itself vanishes by `ftc_integral_zero_of_closed_slit` with three slit-plane choices (`ω = -I` for `‖z₀‖ < 1` case, `ω = -1` if `Re z₀ > 1/2`, `ω = 1` if `Re z₀ < -1/2`).
- **Hypotheses**: `hf : f ≠ 0`, completeness of `S` on `𝒟`, `1 ≤ H`, `z₀ ∈ allZerosInFdBox`, `z₀` not equivalent to any `S`.
- **Uses from project**: `mem_allZerosInFdBox_iff`, `fdBox_im_pos'`, `orderOfVanishingAt'_ne_zero_of_eq_zeroFM`, `off_curve_of_not_in_fd_H`, `generalizedWindingNumber_eq_classical_away`, `fdBoundary_HCurve`, `fdBoundary_H_partition`, `fdBoundary_H_differentiableAt_off_partition`, `fdBoundary_HCurve.deriv_continuous_off_partition`, `piecewiseC1Immersion_deriv_bounded`, `fdBoundary_HImmersion`, `fdBoundary_H_continuous`, `fdBoundary_H_closed`, `fdBoundary_H_re_abs_le_half`, `fdBoundary_H_im_pos`, `fdBoundary_H_norm_ge_one`, `ftc_integral_zero_of_closed_slit`, `fdBoundary_H`, `fdBoundaryFullPartition`, `generalizedWindingNumber'`
- **Used by**: unused in file (used by downstream callers).
- **Visibility**: public
- **Lines**: 626–739
- **Notes**: `include hf in`; >10 lines (~114); main API theorem; key lemmas `generalizedWindingNumber_eq_classical_away`, `ftc_integral_zero_of_closed_slit`, `fdBoundary_H_norm_ge_one`.

## File Summary

- **Total declarations**: 28 (1 instance, 1 def, 26 lemmas/theorems).
- **Key API**: `fdBox_isOpen`, `fdBox_convex`, `allZerosInFdBox`, `mem_allZerosInFdBox_iff`, `analyticAt_logDeriv_off_zeros'`, `hasSimplePoleAt_logDeriv_of_zero_full`, `hasSimplePoleAt_logDeriv_of_zero'`, `hasSimplePoleAt_logDeriv_at_nonzero`, `hasSimplePoleAt_logDeriv_at_point`, `residueSimplePole_logDeriv_eq_order`, `residueSimplePole_logDeriv_eq_zero_at_nonzero`, `fdBoundary_H_mem_fdBox'`, `finset_discrete`, `cpvExists_of_off_curve`, `cpvExists_scale`, `logDerivPatched`, `logDerivPatched_eq_raw_off`, `hasSimplePoleAt_logDerivPatched`, `residue_logDerivPatched_eq_raw`, `logDerivPatched_hf_ext`, `fdBoundary_H_norm_ge_one`, `off_curve_of_not_in_fd_H`, `ftc_integral_zero_of_closed_slit`, `winding_zero_for_non_fd_point_H_geo`.
- **Unused in file** (top-level API consumed downstream): `fdBox_isOpen`, `fdBox_convex`, `hasSimplePoleAt_logDeriv_at_point`, `residueSimplePole_logDeriv_eq_order`, `residueSimplePole_logDeriv_eq_zero_at_nonzero`, `fdBoundary_H_mem_fdBox'`, `finset_discrete`, `cpvExists_of_off_curve`, `cpvExists_scale`, `hasSimplePoleAt_logDerivPatched`, `logDerivPatched_hf_ext`, `winding_zero_for_non_fd_point_H_geo`.
- **Sorries**: none.
- **set_options**: none (uses `attribute [local instance] Classical.propDecidable`).
- **Long proofs** (>10 lines): `modform_not_locally_zero` (17), `hasSimplePoleAt_logDeriv_of_zero_full` (~70), `orderOfVanishingAt'_eq_analyticOrderNatAt` (~18), `logDerivPatched_hf_ext` (~31), `fdBoundary_H_norm_ge_one` (~70), `ftc_integral_zero_of_closed_slit` (~68), `winding_zero_for_non_fd_point_H_geo` (~114).
- **One-paragraph purpose**: This file builds the residue-side infrastructure for the PV chain: it shows that `logDeriv` of a non-zero modular form has simple poles at its zeros with residue equal to the vanishing order; it provides the `logDerivPatched` device curing the `div_zero` issue at zeros so that the `ContinuousAt` hypothesis of `generalizedResidueTheorem'` can be discharged; and it proves geometric properties of the truncated FD-boundary curve `fdBoundary_H` (membership in `fdBox`, lower-bounded norm, closed-curve FTC vanishing for points outside the FD orbit) culminating in the key lemma `winding_zero_for_non_fd_point_H_geo`, which kills spurious contributions to the residue side coming from non-`𝒟` zeros.
