# Inventory: HigherOrderAssembly.lean

**File**: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HigherOrderAssembly.lean`
**Lines**: 1136
**Imports**: `LeanModularForms.ForMathlib.GeneralizedResidueTheorem`, `LeanModularForms.ForMathlib.CurveMeasureZero`
**Namespace**: root (no namespace; `open Complex Set Filter Topology MeasureTheory Finset`)
**Section variable**: `{x : ℂ}`

---

### `theorem cpvIntegrandOn_eq_of_avoids`
- **Type**: `{S : Finset ℂ} {f : ℂ → ℂ} {γ : PiecewiseC1Path x x} {δ : ℝ} (hδ_bound : ∀ s ∈ S, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s‖) {ε : ℝ} (hε : ε < δ) (t : ℝ) (ht : t ∈ Icc 0 1) → cpvIntegrandOn S f γ.toPath.extend ε t = f (γ.toPath.extend t) * deriv γ.toPath.extend t`
- **What**: When `γ` avoids all poles in `S` by margin `δ` and `ε < δ`, the CPV integrand (with epsilon-balls excised around poles) coincides with the ordinary contour integrand at every parameter `t ∈ [0,1]`.
- **How**: Applies `cpvIntegrandOn_of_forall_gt`, showing each `‖γ t - s‖ > ε` via `lt_of_lt_of_le hε (hδ_bound s hs t ht)`.
- **Hypotheses**: pointwise distance bound `δ ≤ ‖γ t - s‖`, smallness `ε < δ`.
- **Uses from project**: `PiecewiseC1Path`, `cpvIntegrandOn`, `cpvIntegrandOn_of_forall_gt`.
- **Used by**: `cpvIntegrandOn_integrableOn_of_avoids`.
- **Visibility**: public
- **Lines**: 71-79

### `theorem cpvIntegrandOn_integrableOn_of_avoids`
- **Type**: `{S : Finset ℂ} {f : ℂ → ℂ} {γ : PiecewiseC1Path x x} {δ : ℝ} (_hδ_pos : 0 < δ) (hδ_bound : ...) {ε : ℝ} (_hε_pos : 0 < ε) (hε_lt : ε < δ) (hint : IntervalIntegrable (PiecewiseC1Path.contourIntegrand f γ) volume 0 1) → IntervalIntegrable (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1`
- **What**: For small `ε < δ`, the CPV integrand is interval-integrable on `[0,1]`, derived from contour integrand interval integrability.
- **How**: Calls `hint.congr` and uses `cpvIntegrandOn_eq_of_avoids` to identify the two integrands on `Ioc`.
- **Hypotheses**: positive avoidance margin, contour integrand interval-integrable.
- **Uses from project**: `cpvIntegrandOn`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path.extendedPath_eq`, `cpvIntegrandOn_eq_of_avoids`.
- **Used by**: `cpvIntegrandOn_integrableOn_eventually_of_avoids`, `cpvIntegrandOn_sum_eq_of_avoids`.
- **Visibility**: public
- **Lines**: 83-96

### `private theorem contourIntegral_remainder_eq_zero_of_simplePoles`
- **Type**: `{U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty) (S : Finset ℂ) (hS_in_U : ↑S ⊆ U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S)) (γ : PiecewiseC1Path x x) (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s) (hγ_in_U : ∀ t ∈ Icc 0 1, γ t ∈ U) (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc 0 1, γ t ≠ s) (h_rem_int : IntervalIntegrable (...) volume 0 1) → γ.contourIntegral (fun z => f z - principalPartSum S (residue f) z) = 0`
- **What**: For simple poles in a convex domain, the contour integral of the remainder `f - principalPartSum` vanishes.
- **How**: 5-step argument: (1) take holomorphic extension `g` via `remainder_differentiableOn_of_simplePoles`; (2) `g` agrees with the remainder along the curve; (3) `g`'s contour integral is 0 by `contourIntegral_eq_zero_of_differentiableOn_convex_aux` (Cauchy for convex); (4) the two integrals agree via `intervalIntegral.integral_congr`; (5) conclude.
- **Hypotheses**: convex open nonempty `U`, simple poles, `γ` avoids poles.
- **Uses from project**: `HasSimplePoleAt`, `residue`, `principalPartSum`, `PiecewiseC1Path.contourIntegrand`, `remainder_differentiableOn_of_simplePoles`, `PiecewiseC1Path.contourIntegral`, `PiecewiseC1Path.contourIntegral_eq_zero_of_differentiableOn_convex_aux`, `PiecewiseC1Path.extendedPath_eq`.
- **Used by**: `hCancel_of_simplePoles_convex`.
- **Visibility**: private
- **Lines**: 111-151
- **Notes**: proof ≈40 lines.

### `theorem hCancel_of_simplePoles_convex`
- **Type**: same hypotheses as above plus `(hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s‖)` → `HasCauchyPVOn S (fun z => f z - principalPartSum S (residue f) z) γ 0`
- **What**: CPV cancellation lemma for simple poles in convex domains: the CPV of the remainder is zero.
- **How**: Rewrites the target value `0` as `contourIntegral_remainder_eq_zero_of_simplePoles ...` then applies `hasCauchyPVOn_of_avoids`.
- **Hypotheses**: convex open nonempty `U`, simple poles, avoidance, distance margin `δ`.
- **Uses from project**: `HasCauchyPVOn`, `principalPartSum`, `residue`, `PiecewiseC1Path.contourIntegrand`, `contourIntegral_remainder_eq_zero_of_simplePoles`, `hasCauchyPVOn_of_avoids`.
- **Used by**: `hasCauchyPVOn_simplePoles_convex`, `hasCauchyPVOn_simplePoles_convex_auto`.
- **Visibility**: public
- **Lines**: 153-170

### `theorem hCancel_of_simplePoles_nullHomologous_at`
- **Type**: many hypotheses (null-hom case, pointwise Dixon-zero at `w₀`), returns `HasCauchyPVOn S (fun z => f z - principalPartSum ... z) γ 0`
- **What**: Pointwise null-homologous analog of `hCancel_of_simplePoles_convex`: only requires Dixon function to vanish at the chosen `w₀`.
- **How**: Calls `contourIntegral_eq_zero_of_nullHomologous_at` with the pointwise Dixon-zero, then `hasCauchyPVOn_of_avoids`.
- **Hypotheses**: open `U`, simple poles, avoidance, distance margin, plus `w₀ ∈ U` with `γ` avoiding `w₀` and pointwise Dixon-zero of `(z-w₀)(f-pp)`.
- **Uses from project**: `dixonFunction`, `principalPartSum`, `residue`, `HasSimplePoleAt`, `HasCauchyPVOn`, `contourIntegral_eq_zero_of_nullHomologous_at`, `hasCauchyPVOn_of_avoids`.
- **Used by**: `hCancel_of_simplePoles_nullHomologous`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_unbounded`.
- **Visibility**: public
- **Lines**: 177-204
- **Notes**: many `_h*` hypotheses ignored at proof level (the proof uses only `w₀`-related ones plus `hδ`).

### `theorem hCancel_of_simplePoles_nullHomologous`
- **Type**: as `_at` variant but with `∀ w, dixonFunction (...) U γ w = 0`
- **What**: Null-homologous cancellation lemma with the full identically-zero Dixon hypothesis.
- **How**: Reduces to `hCancel_of_simplePoles_nullHomologous_at` by instantiating `h_dixon_zero w₀`.
- **Hypotheses**: same as `_at` plus universally-zero Dixon function.
- **Uses from project**: `hCancel_of_simplePoles_nullHomologous_at`, `dixonFunction`, `principalPartSum`, `residue`, `HasCauchyPVOn`.
- **Used by**: `hasCauchyPVOn_simplePoles_nullHomologous_closed`.
- **Visibility**: public
- **Lines**: 206-230

### `theorem hPV_sing_of_avoids`
- **Type**: `(S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (hδ : ∃ δ > 0, ...) (hI : ∀ s ∈ S, IntervalIntegrable ((residue f s / (γ t - s)) * deriv γ ...) volume 0 1) → HasCauchyPVOn S (principalPartSum S (residue f)) γ (∑ s ∈ S, 2 * π * I * generalizedWindingNumber γ s * residue f s)`
- **What**: When `γ` avoids all poles, the CPV of the singular (principal-part) sum equals the winding-residue formula.
- **How**: Rewrites the formula as the contour integral via `contourIntegral_principalPartSum_eq`, then concludes by `hasCauchyPVOn_of_avoids`.
- **Hypotheses**: avoidance with positive margin, integrability of each summand of `pp`.
- **Uses from project**: `principalPartSum`, `residue`, `generalizedWindingNumber`, `HasCauchyPVOn`, `contourIntegral_principalPartSum_eq`, `hasCauchyPVOn_of_avoids`.
- **Used by**: `hasCauchyPVOn_simplePoles_convex`, `hasCauchyPVOn_simplePoles_convex_auto`, `hasCauchyPVOn_simplePoles_nullHomologous_closed`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_unbounded`.
- **Visibility**: public
- **Lines**: 234-246

### `theorem generalizedResidueTheorem_composed`
- **Type**: `(S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (hCancel : HasCauchyPVOn S (f - pp) γ 0) (hPV_sing : HasCauchyPVOn S pp γ formula) (hI_rem hI_sing : integrability) → HasCauchyPVOn S f γ formula`
- **What**: Composition theorem: cancellation + singular CPV ⇒ full CPV equals winding-residue formula.
- **How**: Direct application of `hasCauchyPVOn_of_tendsto_sub`.
- **Hypotheses**: cancellation, singular CPV, both CPV integrand integrabilities.
- **Uses from project**: `HasCauchyPVOn`, `principalPartSum`, `residue`, `generalizedWindingNumber`, `cpvIntegrandOn`, `hasCauchyPVOn_of_tendsto_sub`.
- **Used by**: `hasCauchyPVOn_simplePoles_convex`.
- **Visibility**: public
- **Lines**: 262-283
- **Notes**: TODO comment referencing legacy-port-plan Phase 1.

### `theorem hasCauchyPVOn_simplePoles_convex`
- **Type**: convex-domain assembly with explicit CPV integrability hypotheses, returns `HasCauchyPVOn S f γ formula`
- **What**: Fully assembled CPV residue theorem for simple poles on a convex domain.
- **How**: Composes `hCancel_of_simplePoles_convex`, `hPV_sing_of_avoids`, and `generalizedResidueTheorem_composed`.
- **Hypotheses**: convex open nonempty `U`, simple poles, avoidance with margin `δ`, integrabilities (contour + singular + CPV variants).
- **Uses from project**: `HasSimplePoleAt`, `HasCauchyPVOn`, `principalPartSum`, `residue`, `generalizedWindingNumber`, `PiecewiseC1Path.contourIntegrand`, `cpvIntegrandOn`, `hCancel_of_simplePoles_convex`, `hPV_sing_of_avoids`, `generalizedResidueTheorem_composed`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 297-331

### `theorem cpvIntegrandOn_integrableOn_eventually_of_avoids`
- **Type**: `{S} {f} {γ} {δ} (hδ_pos : 0 < δ) (hδ_bound) (hint) → ∀ᶠ ε in 𝓝[>] 0, IntervalIntegrable (cpvIntegrandOn S f γ.toPath.extend ε) volume 0 1`
- **What**: For small `ε > 0`, the CPV integrand is interval-integrable (eventually, near 0).
- **How**: Uses `Ioo_mem_nhdsGT hδ_pos` and `filter_upwards`, calls `cpvIntegrandOn_integrableOn_of_avoids`.
- **Hypotheses**: positive avoidance margin, contour integrand integrability.
- **Uses from project**: `cpvIntegrandOn`, `PiecewiseC1Path.contourIntegrand`, `cpvIntegrandOn_integrableOn_of_avoids`.
- **Used by**: unused in file (likely public corollary).
- **Visibility**: public
- **Lines**: 339-348

### `private theorem cpvIntegrandOn_sum_eq_of_avoids`
- **Type**: `(hδ_pos) (hδ_bound) (h_rem_int) (h_pp_int) → (fun ε => ∫ cpvIntegrandOn S f ...) =ᶠ[𝓝[>] 0] (fun ε => ∫ cpvIntegrandOn S (f-pp) ... + ∫ cpvIntegrandOn S pp ...)`
- **What**: Eventually (in `ε → 0⁺`), the CPV integral of `f` decomposes as the sum of the CPV integral of the remainder and the CPV integral of the principal part.
- **How**: Pointwise additivity via `cpvIntegrandOn_add` and `intervalIntegral.integral_add`, combined with integrability from `cpvIntegrandOn_integrableOn_of_avoids`.
- **Hypotheses**: positive avoidance margin, integrability of remainder and pp contour integrands.
- **Uses from project**: `cpvIntegrandOn`, `cpvIntegrandOn_add`, `principalPartSum`, `residue`, `PiecewiseC1Path.contourIntegrand`, `cpvIntegrandOn_integrableOn_of_avoids`.
- **Used by**: `hasCauchyPVOn_simplePoles_convex_auto`, `hasCauchyPVOn_simplePoles_nullHomologous_closed`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_unbounded`.
- **Visibility**: private
- **Lines**: 355-390
- **Notes**: proof ≈35 lines.

### `theorem hasCauchyPVOn_simplePoles_convex_auto`
- **Type**: like `hasCauchyPVOn_simplePoles_convex` but drops the `hI_cpv_rem`/`hI_cpv_sing` hypotheses
- **What**: Convex-domain CPV residue theorem with auto-derived CPV integrability.
- **How**: Destructures `hδ`, obtains cancellation via `hCancel_of_simplePoles_convex`, singular CPV via `hPV_sing_of_avoids`, adds them with `.add`, simplifies `zero_add`, and identifies with the original via `cpvIntegrandOn_sum_eq_of_avoids`.
- **Hypotheses**: convex open nonempty, simple poles, avoidance with margin, contour integrand and pp integrability, per-pole integrability.
- **Uses from project**: `HasSimplePoleAt`, `HasCauchyPVOn`, `principalPartSum`, `residue`, `generalizedWindingNumber`, `PiecewiseC1Path.contourIntegrand`, `hCancel_of_simplePoles_convex`, `hPV_sing_of_avoids`, `cpvIntegrandOn_sum_eq_of_avoids`.
- **Used by**: `hasCauchyPVOn_simplePoles_convex_closed`, `generalizedResidueTheorem_simplePoles_convex_fromGeneral`.
- **Visibility**: public
- **Lines**: 392-421

### `theorem generalizedResidueTheorem_of_cancel_oracle`
- **Type**: takes `U`, `S`, `f`, `γ : PwC1Immersion`, null-homologous, meromorphic, conditions A'+B, cancellation oracle, singular CPV oracle, two integrabilities, returns the full residue formula with `2πi` factored
- **What**: Bridge theorem: given conditions (A')+(B) plus oracles, applies `generalizedResidueTheorem`.
- **How**: Pure assembly — direct application of `generalizedResidueTheorem`.
- **Hypotheses**: open `U`, `S ⊆ U`, differentiability off `S`, null-homologous immersion, meromorphicity, condition A' and B, oracles for cancellation, singular CPV, and CPV integrabilities.
- **Uses from project**: `IsNullHomologous`, `MeromorphicAt`, `SatisfiesConditionA'`, `SatisfiesConditionB`, `poleOrderAt`, `PwC1Immersion`, `HasCauchyPVOn`, `principalPartSum`, `residue`, `generalizedWindingNumber`, `cpvIntegrandOn`, `generalizedResidueTheorem`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 431-458

### `theorem contourIntegral_eq_of_hasCauchyPVOn_avoids`
- **Type**: `{S} {f} {γ} {L} (hδ) (h_pvon : HasCauchyPVOn S f γ L) → γ.contourIntegral f = L`
- **What**: When `γ` avoids `S`, the value supplied to `HasCauchyPVOn` is the ordinary contour integral.
- **How**: Constructs the CPV using `hasCauchyPVOn_of_avoids` with value `γ.contourIntegral f`, then applies `HasCauchyPVOn.unique`.
- **Hypotheses**: avoidance with positive margin, supplied CPV equality.
- **Uses from project**: `HasCauchyPVOn`, `PiecewiseC1Path.contourIntegral`, `hasCauchyPVOn_of_avoids`, `HasCauchyPVOn.unique`.
- **Used by**: `contourIntegral_simplePoles_convex_closed`, `contourIntegral_simplePoles_nullHomologous_closed_full`, `generalizedResidueTheorem_simplePoles_convex_fromGeneral`.
- **Visibility**: public
- **Lines**: 465-472

### `theorem hasCauchyPVOn_simplePoles_convex_closed`
- **Type**: minimal-hypothesis form (no oracle hypotheses), only requires `(h_deriv_int : IntervalIntegrable (deriv γ.toPath.extend) ...)` plus geometry
- **What**: Cleanest form of HW 3.3 for the simple-pole convex case: only geometric/analytic data plus derivative integrability.
- **How**: Derives `h_pp_int`, `h_rem_int`, `hI` from continuity (using `principalPartSum_differentiableOn`, `differentiableOn_div_sub`, `PiecewiseC1Path.contourIntegrand_intervalIntegrable_of_continuousOn`); then applies `hasCauchyPVOn_simplePoles_convex_auto`.
- **Hypotheses**: convex open nonempty, simple poles, avoidance, distance margin, derivative integrability.
- **Uses from project**: `HasSimplePoleAt`, `HasCauchyPVOn`, `principalPartSum`, `principalPartSum_differentiableOn`, `residue`, `generalizedWindingNumber`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path.contourIntegrand_intervalIntegrable_of_continuousOn`, `differentiableOn_div_sub`, `hasCauchyPVOn_simplePoles_convex_auto`.
- **Used by**: `contourIntegral_simplePoles_convex_closed`.
- **Visibility**: public
- **Lines**: 487-538
- **Notes**: proof ≈52 lines.

### `theorem contourIntegral_simplePoles_convex_closed`
- **Type**: same hypotheses as `_convex_closed`, but states `γ.contourIntegral f = ∑ s ∈ S, 2πi · gWN γ s · residue f s`.
- **What**: Contour-integral form of HW 3.3 (simple poles, convex domain) with minimal hypotheses.
- **How**: Composes `hasCauchyPVOn_simplePoles_convex_closed` with `contourIntegral_eq_of_hasCauchyPVOn_avoids`.
- **Hypotheses**: as `_convex_closed`.
- **Uses from project**: `HasSimplePoleAt`, `PiecewiseC1Path.contourIntegral`, `residue`, `generalizedWindingNumber`, `contourIntegral_eq_of_hasCauchyPVOn_avoids`, `hasCauchyPVOn_simplePoles_convex_closed`.
- **Used by**: unused in file (public corollary).
- **Visibility**: public
- **Lines**: 542-557

### `theorem hasCauchyPVOn_simplePoles_nullHomologous_closed`
- **Type**: null-homologous closed form, takes `w₀` and Dixon-zero, plus integrabilities, returns the CPV residue formula
- **What**: HW 3.3 closed form for simple poles on null-homologous null-hom domains (with Dixon-zero oracle supplied).
- **How**: Destructures `hδ`, calls `hCancel_of_simplePoles_nullHomologous`, then `hPV_sing_of_avoids`, adds them, identifies via `cpvIntegrandOn_sum_eq_of_avoids`.
- **Hypotheses**: open `U`, `S ⊆ U`, differentiability off `S`, simple poles, `γ` in `U` and avoiding `S` with margin, choice of `w₀ ∈ U` avoided by `γ`, Dixon-zero for `(z-w₀)(f-pp)`, integrabilities.
- **Uses from project**: `HasSimplePoleAt`, `HasCauchyPVOn`, `dixonFunction`, `principalPartSum`, `residue`, `generalizedWindingNumber`, `PiecewiseC1Path.contourIntegrand`, `hCancel_of_simplePoles_nullHomologous`, `hPV_sing_of_avoids`, `cpvIntegrandOn_sum_eq_of_avoids`.
- **Used by**: `hasCauchyPVOn_simplePoles_nullHomologous_closed_of_lipschitz`.
- **Visibility**: public
- **Lines**: 568-609

### `theorem hasCauchyPVOn_simplePoles_nullHomologous_closed_of_lipschitz`
- **Type**: Lipschitz variant of `_nullHomologous_closed`; takes the Dixon/integrability data as a single packed `dixon_zero_for` hypothesis
- **What**: Null-hom closed form auto-deriving `w₀` from Lipschitz hypothesis via `ForMathlib.exists_mem_not_mem_path_image_of_isOpen`.
- **How**: Picks `w₀` via the existence lemma, then destructures `dixon_zero_for` and applies `hasCauchyPVOn_simplePoles_nullHomologous_closed`.
- **Hypotheses**: open `U`, nonempty, simple poles, avoidance with margin, Lipschitz `γ.toPath.extend`, packed Dixon-zero/integrability oracle, plus the standard integrabilities.
- **Uses from project**: `HasSimplePoleAt`, `HasCauchyPVOn`, `dixonFunction`, `principalPartSum`, `residue`, `generalizedWindingNumber`, `PiecewiseC1Path.contourIntegrand`, `ForMathlib.exists_mem_not_mem_path_image_of_isOpen`, `hasCauchyPVOn_simplePoles_nullHomologous_closed`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 619-659

### `theorem hasCauchyPVOn_simplePoles_nullHomologous_closed_full`
- **Type**: `(hU_open) (hU_ne) (hU_bounded) (S) (hS_in_U) (f) (hf) (γ : PwC1Immersion) (h_null) (hSimplePoles) (hγ_avoids) (hδ) {K} (hLip) → HasCauchyPVOn S f γ.toPiecewiseC1Path formula`
- **What**: **B-6 full closure**: HW 3.3 for simple poles in null-homologous bounded open `U`, no oracle hypotheses (Dixon zero auto-derived).
- **How**: Long proof (≈140 lines): derives `h_deriv_int` from Lipschitz via `norm_deriv_le_of_lipschitz`; obtains `w₀` via `ForMathlib.exists_mem_not_mem_path_image_of_isOpen`; constructs holomorphic extension `g` via `remainder_differentiableOn_of_simplePoles`; applies `dixonFunction_eq_zero_of_nullHomologous_open_full`; uses `dslope`-rewriting to align the twisted function with `g`; derives all integrabilities from continuity; finally composes via `hCancel_of_simplePoles_nullHomologous_at`, `hPV_sing_of_avoids`, `cpvIntegrandOn_sum_eq_of_avoids`.
- **Hypotheses**: open, nonempty, bounded `U`, `S ⊆ U`, differentiability off `S`, null-homologous `γ`, simple poles, avoidance, margin, Lipschitz `γ`.
- **Uses from project**: `IsNullHomologous`, `PwC1Immersion`, `IsNullHomologous.image_subset`, `norm_deriv_le_of_lipschitz`, `ForMathlib.exists_mem_not_mem_path_image_of_isOpen`, `remainder_differentiableOn_of_simplePoles`, `dixonFunction`, `dixonH1`, `dixonFunction_eq_zero_of_nullHomologous_open_full`, `IsNullHomologous.winding_zero_nhds_of_not_mem_of_closed`, `avoids_delta_bound`, `principalPartSum`, `principalPartSum_differentiableOn`, `residue`, `generalizedWindingNumber`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path.contourIntegrand_intervalIntegrable_of_continuousOn`, `differentiableOn_div_sub`, `hCancel_of_simplePoles_nullHomologous_at`, `hPV_sing_of_avoids`, `cpvIntegrandOn_sum_eq_of_avoids`, `HasSimplePoleAt`, `HasCauchyPVOn`.
- **Used by**: `contourIntegral_simplePoles_nullHomologous_closed_full`, `generalizedResidueTheorem_simplePoles_nullHomologous_closed`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids`.
- **Visibility**: public
- **Lines**: 673-817
- **Notes**: proof ≈145 lines.

### `theorem contourIntegral_simplePoles_nullHomologous_closed_full`
- **Type**: same hypotheses as `_closed_full`, states `γ.contourIntegral f = ...`
- **What**: Contour-integral form of B-6.
- **How**: Composes `hasCauchyPVOn_simplePoles_nullHomologous_closed_full` with `contourIntegral_eq_of_hasCauchyPVOn_avoids`.
- **Hypotheses**: as `_closed_full`.
- **Uses from project**: `IsNullHomologous`, `PwC1Immersion`, `PiecewiseC1Path.contourIntegral`, `HasSimplePoleAt`, `residue`, `generalizedWindingNumber`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full`, `contourIntegral_eq_of_hasCauchyPVOn_avoids`.
- **Used by**: `contourIntegral_simplePoles_nullHomologous_closed_full_avoids`.
- **Visibility**: public
- **Lines**: 824-840

### `theorem generalizedResidueTheorem_simplePoles_nullHomologous_closed`
- **Type**: `_closed_full` hypotheses, returns `HasCauchyPVOn S f γ.toPiecewiseC1Path (2πi · ∑ ...)` (with `2πi` factored to front)
- **What**: Closed null-hom form of `generalizedResidueTheorem` for simple poles, with formula matching abstract theorem's signature.
- **How**: Rewrites the target via `Finset.mul_sum`, then applies `hasCauchyPVOn_simplePoles_nullHomologous_closed_full`.
- **Hypotheses**: as `_closed_full`.
- **Uses from project**: `IsNullHomologous`, `PwC1Immersion`, `HasSimplePoleAt`, `HasCauchyPVOn`, `generalizedWindingNumber`, `residue`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full`.
- **Used by**: `generalizedResidueTheorem_simplePoles_nullHomologous_closed_avoids`.
- **Visibility**: public
- **Lines**: 848-870

### `theorem hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids`
- **Type**: δ-free variant of `_closed_full` (auto-derives the distance bound from pointwise avoidance)
- **What**: δ-free version: drops the explicit `hδ` since it is auto-derived from pointwise avoidance and finite `S` via `avoids_finset_delta_bound`.
- **How**: Direct application of `hasCauchyPVOn_simplePoles_nullHomologous_closed_full` with `avoids_finset_delta_bound` discharging `hδ`.
- **Hypotheses**: `_closed_full` minus `hδ`.
- **Uses from project**: `avoids_finset_delta_bound`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full`, `IsNullHomologous`, `PwC1Immersion`, `HasSimplePoleAt`, `HasCauchyPVOn`, `generalizedWindingNumber`, `residue`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 877-891

### `theorem contourIntegral_simplePoles_nullHomologous_closed_full_avoids`
- **Type**: δ-free variant of contour-integral form
- **What**: δ-free contour-integral form of B-6.
- **How**: Direct application of `contourIntegral_simplePoles_nullHomologous_closed_full` with `avoids_finset_delta_bound`.
- **Hypotheses**: as `_closed_full` minus `hδ`.
- **Uses from project**: `avoids_finset_delta_bound`, `contourIntegral_simplePoles_nullHomologous_closed_full`, `IsNullHomologous`, `PwC1Immersion`, `HasSimplePoleAt`, `PiecewiseC1Path.contourIntegral`, `generalizedWindingNumber`, `residue`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 894-908

### `theorem generalizedResidueTheorem_simplePoles_nullHomologous_closed_avoids`
- **Type**: δ-free generalized residue theorem statement form
- **What**: δ-free `generalizedResidueTheorem` form for simple poles.
- **How**: Direct application of `generalizedResidueTheorem_simplePoles_nullHomologous_closed` with `avoids_finset_delta_bound`.
- **Hypotheses**: as `_closed` minus `hδ`.
- **Uses from project**: `avoids_finset_delta_bound`, `generalizedResidueTheorem_simplePoles_nullHomologous_closed`, `IsNullHomologous`, `PwC1Immersion`, `HasSimplePoleAt`, `HasCauchyPVOn`, `generalizedWindingNumber`, `residue`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 911-925

### `theorem generalizedResidueTheorem_simplePoles_convex_fromGeneral`
- **Type**: `hasCauchyPVOn_simplePoles_convex_auto` hypotheses, states `γ.contourIntegral f = ∑ ...`
- **What**: Convex corollary of the general residue theorem (via `_auto`).
- **How**: Calls `hasCauchyPVOn_simplePoles_convex_auto` then `contourIntegral_eq_of_hasCauchyPVOn_avoids`.
- **Hypotheses**: as `_convex_auto`.
- **Uses from project**: `HasSimplePoleAt`, `HasCauchyPVOn`, `principalPartSum`, `residue`, `generalizedWindingNumber`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path.contourIntegral`, `hasCauchyPVOn_simplePoles_convex_auto`, `contourIntegral_eq_of_hasCauchyPVOn_avoids`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 937-961

### `theorem hasCauchyPVOn_simplePoles_nullHomologous_closed_full_unbounded`
- **Type**: same as `_closed_full` but **without** `hU_bounded`
- **What**: Unbounded `U` variant of B-6. Lipschitz hypothesis used to derive cocompact-winding-zero discharge for Dixon's theorem.
- **How**: Same proof structure as `_closed_full` (≈145 lines) but uses `dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded` instead of the bounded version.
- **Hypotheses**: open, nonempty `U`, `S ⊆ U`, differentiability off `S`, null-homologous `γ`, simple poles, avoidance, margin, Lipschitz `γ`.
- **Uses from project**: `IsNullHomologous`, `PwC1Immersion`, `IsNullHomologous.image_subset`, `IsNullHomologous.winding_zero_nhds_of_not_mem_of_closed`, `norm_deriv_le_of_lipschitz`, `ForMathlib.exists_mem_not_mem_path_image_of_isOpen`, `remainder_differentiableOn_of_simplePoles`, `dixonFunction`, `dixonH1`, `dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded`, `avoids_delta_bound`, `principalPartSum`, `principalPartSum_differentiableOn`, `residue`, `generalizedWindingNumber`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path.contourIntegrand_intervalIntegrable_of_continuousOn`, `differentiableOn_div_sub`, `hCancel_of_simplePoles_nullHomologous_at`, `hPV_sing_of_avoids`, `cpvIntegrandOn_sum_eq_of_avoids`, `HasSimplePoleAt`, `HasCauchyPVOn`.
- **Used by**: `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids_unbounded`.
- **Visibility**: public
- **Lines**: 974-1117
- **Notes**: proof ≈144 lines; near-clone of `_closed_full` but for unbounded `U`.

### `theorem hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids_unbounded`
- **Type**: δ-free unbounded variant
- **What**: δ-free + unbounded variant: combines `_closed_full_unbounded` with `avoids_finset_delta_bound`.
- **How**: Direct application chaining.
- **Hypotheses**: as `_closed_full_unbounded` minus `hδ`.
- **Uses from project**: `avoids_finset_delta_bound`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_unbounded`, `IsNullHomologous`, `PwC1Immersion`, `HasSimplePoleAt`, `HasCauchyPVOn`, `generalizedWindingNumber`, `residue`.
- **Used by**: unused in file (public API).
- **Visibility**: public
- **Lines**: 1121-1134

---

## File Summary

- **Total declarations**: 22 (20 theorems + 1 private theorem `contourIntegral_remainder_eq_zero_of_simplePoles` + 1 private theorem `cpvIntegrandOn_sum_eq_of_avoids`).
- **Public API surface**: `cpvIntegrandOn_eq_of_avoids`, `cpvIntegrandOn_integrableOn_of_avoids`, `cpvIntegrandOn_integrableOn_eventually_of_avoids`, `hCancel_of_simplePoles_convex`, `hCancel_of_simplePoles_nullHomologous_at`, `hCancel_of_simplePoles_nullHomologous`, `hPV_sing_of_avoids`, `generalizedResidueTheorem_composed`, `hasCauchyPVOn_simplePoles_convex`, `hasCauchyPVOn_simplePoles_convex_auto`, `generalizedResidueTheorem_of_cancel_oracle`, `contourIntegral_eq_of_hasCauchyPVOn_avoids`, `hasCauchyPVOn_simplePoles_convex_closed`, `contourIntegral_simplePoles_convex_closed`, `hasCauchyPVOn_simplePoles_nullHomologous_closed`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_of_lipschitz`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full`, `contourIntegral_simplePoles_nullHomologous_closed_full`, `generalizedResidueTheorem_simplePoles_nullHomologous_closed`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids`, `contourIntegral_simplePoles_nullHomologous_closed_full_avoids`, `generalizedResidueTheorem_simplePoles_nullHomologous_closed_avoids`, `generalizedResidueTheorem_simplePoles_convex_fromGeneral`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_unbounded`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids_unbounded`.
- **Private helpers**: `contourIntegral_remainder_eq_zero_of_simplePoles`, `cpvIntegrandOn_sum_eq_of_avoids`.
- **Unused in file** (likely public-API top-level): `hasCauchyPVOn_simplePoles_convex`, `cpvIntegrandOn_integrableOn_eventually_of_avoids`, `generalizedResidueTheorem_of_cancel_oracle`, `contourIntegral_simplePoles_convex_closed`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_of_lipschitz`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids`, `contourIntegral_simplePoles_nullHomologous_closed_full_avoids`, `generalizedResidueTheorem_simplePoles_nullHomologous_closed_avoids`, `generalizedResidueTheorem_simplePoles_convex_fromGeneral`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids_unbounded`.
- **Sorries**: 0.
- **Axioms / `native_decide` / TODOs**: One `TODO` comment on `generalizedResidueTheorem_composed` referencing the legacy-port-plan; no axioms or `native_decide`.
- **`set_option`**: none.
- **Long proofs (>30 lines)**: `contourIntegral_remainder_eq_zero_of_simplePoles` (~40), `cpvIntegrandOn_sum_eq_of_avoids` (~35), `hasCauchyPVOn_simplePoles_convex_closed` (~52), `hasCauchyPVOn_simplePoles_nullHomologous_closed_full` (~145), `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_unbounded` (~144).

**File purpose**: Assembly layer for the Hungerbuhler–Wasem generalized residue theorem (Theorem 3.3) specialized to simple poles. Provides the bridge from conditions (A')+(B) to the `hCancel` hypothesis required by the abstract generalized residue theorem, in three flavors: convex domains (elementary Cauchy), null-homologous Dixon-zero (oracle-supplied), and fully-closed null-homologous (Lipschitz + bounded/unbounded). Major closure theorems eliminate every oracle hypothesis and derive integrabilities from continuity, leaving only geometric/analytic data (avoidance, simple poles, Lipschitz immersion). Provides both `HasCauchyPVOn` and ordinary contour-integral statement forms, in both standard and δ-free variants.
