# MeromorphicCauchy.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/MeromorphicCauchy.lean`
Lines: 332

## Imports
- `LeanModularForms.ForMathlib.DixonTheorem`
- `LeanModularForms.ForMathlib.SimplePoleIntegral`
- `LeanModularForms.ForMathlib.PrincipalPart`

---

### `theorem contourIntegral_principalPartSum_eq`
- **Type**: `{S : Finset ℂ} {c : ℂ → ℂ} {γ : PiecewiseC1Path x x} (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s‖) (hI : ∀ s ∈ S, IntervalIntegrable (fun t => (c s / (γ.toPath.extend t - s)) * deriv γ.toPath.extend t) volume 0 1) → γ.contourIntegral (principalPartSum S c) = ∑ s ∈ S, 2*↑Real.pi*I * generalizedWindingNumber γ s * c s`
- **What**: The contour integral of the principal-part sum `∑ c(s)/(z - s)` over a finite pole set `S` along a closed piecewise-C1 path `γ` equals the sum of `2πi · winding(γ,s) · c(s)`.
- **How**: One-line delegation to `integral_sum_simple_poles_eq_winding hδ hI` from `SimplePoleIntegral`.
- **Hypotheses**: `γ` is a closed path avoiding `S` with positive separation `δ`; each pole-term integrand is interval-integrable.
- **Uses from project**: `principalPartSum`, `PiecewiseC1Path.contourIntegral`, `generalizedWindingNumber`, `integral_sum_simple_poles_eq_winding`.
- **Used by**: `contourIntegral_decomp_of_simple_poles`.
- **Visibility**: public
- **Lines**: 66-74
- **Notes**: trivial wrapper.

### `theorem contourIntegral_decomp_of_simple_poles`
- **Type**: `{f : ℂ → ℂ} {S : Finset ℂ} {c : ℂ → ℂ} {γ : PiecewiseC1Path x x} (hδ ...) (h_rem_int ...) (h_pp_int ...) (hI ...) → γ.contourIntegral f = γ.contourIntegral (fun z => f z - principalPartSum S c z) + ∑ s ∈ S, 2*↑Real.pi*I * generalizedWindingNumber γ s * c s`
- **What**: Pole-subtraction decomposition: the contour integral of `f` equals the integral of the holomorphic remainder `f - principalPartSum` plus the winding-number sum from the poles.
- **How**: Rewrites the sum via `contourIntegral_principalPartSum_eq` and uses `γ.contourIntegral_add` to combine the remainder and principal-part integrals; closes with `congr 1 with z; ring`.
- **Hypotheses**: positive separation `hδ`; interval-integrability of the remainder and principal-part contour integrands; per-pole integrability `hI`.
- **Uses from project**: `contourIntegral_principalPartSum_eq`, `PiecewiseC1Path.contourIntegral_add`, `principalPartSum`, `generalizedWindingNumber`.
- **Used by**: `contourIntegral_eq_sum_winding_coefficients_convex`.
- **Visibility**: public
- **Lines**: 84-101
- **Notes**: none.

### `theorem sub_principalPartSum_analyticAt_all`
- **Type**: `{f : ℂ → ℂ} {S : Finset ℂ} {c : ℂ → ℂ} (h_pole : ∀ s ∈ S, HasSimplePoleAt f s) (h_coeff : ∀ s (hs : s ∈ S), (h_pole s hs).coeff = c s) → ∀ s ∈ S, ∃ g, AnalyticAt ℂ g s ∧ ∀ᶠ z in 𝓝[≠] s, f z - principalPartSum S c z = g z`
- **What**: At every pole `s ∈ S`, the remainder `f - principalPartSum S c` is locally (on punctured neighborhood) equal to an analytic germ.
- **How**: Pointwise lambda invoking `sub_principalPartSum_analyticAt` (single-pole version) for each `s`.
- **Hypotheses**: `f` has simple poles at every `s ∈ S` with coefficients matching `c`.
- **Uses from project**: `sub_principalPartSum_analyticAt`, `HasSimplePoleAt`, `principalPartSum`.
- **Used by**: `sub_principalPartSum_corrected_differentiableOn`.
- **Visibility**: public
- **Lines**: 107-112
- **Notes**: none.

### `private lemma correction_eventuallyEq_analyticExt`
- **Type**: `{S : Finset ℂ} {z : ℂ} (rem g_z : ℂ → ℂ) (hzS : z ∈ ↑S) (hg_z_an : AnalyticAt ℂ g_z z) (hg_z_eq : ∀ᶠ w in 𝓝[≠] z, rem w = g_z w) → (fun w => if w ∈ ↑S then limUnder (𝓝[≠] w) rem else rem w) =ᶠ[𝓝 z] g_z`
- **What**: At a pole `z ∈ S`, the "limit-corrected" function (defined as `limUnder (𝓝[≠] w) rem` on `S`, else `rem`) coincides with the analytic extension `g_z` in a full neighborhood of `z`.
- **How**: 27-line proof — establishes `limUnder (𝓝[≠] z) rem = g_z z` via `continuousAt.tendsto.mono_left nhdsWithin_le_nhds` + `congr'` on `hg_z_eq`. Builds a neighborhood `V ∩ (S.erase z)ᶜ` using `S.erase z` being closed (`Finset.finite_toSet.isClosed`), and case-splits on `w = z` vs `w ≠ z` to discharge the indicator.
- **Hypotheses**: `z ∈ S`; `g_z` analytic at `z`; `rem =ᶠ g_z` on `𝓝[≠] z`.
- **Uses from project**: none (uses mathlib `Finset`, `limUnder`, `nhdsWithin` only).
- **Used by**: `sub_principalPartSum_corrected_differentiableOn`.
- **Visibility**: private
- **Lines**: 118-144
- **Notes**: >10 lines; the key lemma is `mem_nhdsWithin.mp` + `Finset.finite_toSet.isClosed.isOpen_compl.mem_nhds`.

### `private lemma correction_eventuallyEq_rem`
- **Type**: `{S : Finset ℂ} {z : ℂ} (rem : ℂ → ℂ) (hzS : z ∉ ↑S) → (fun w => if w ∈ ↑S then limUnder (𝓝[≠] w) rem else rem w) =ᶠ[𝓝 z] rem`
- **What**: Away from `S`, the limit-corrected function equals `rem` in a neighborhood (since `Sᶜ` is open).
- **How**: Uses `S.finite_toSet.isClosed.isOpen_compl.mem_nhds hzS` to get `Sᶜ ∈ 𝓝 z` and `if_neg`.
- **Hypotheses**: `z ∉ S`.
- **Uses from project**: none (uses mathlib `Finset.finite_toSet`).
- **Used by**: `sub_principalPartSum_corrected_differentiableOn`.
- **Visibility**: private
- **Lines**: 147-153
- **Notes**: none.

### `theorem sub_principalPartSum_corrected_differentiableOn`
- **Type**: `{f : ℂ → ℂ} {U : Set ℂ} {S : Finset ℂ} {c : ℂ → ℂ} (hU_open : IsOpen U) (hf_diff : DifferentiableOn ℂ f (U \ ↑S)) (_hS_sub : ↑S ⊆ U) (h_pole ...) (h_coeff ...) → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U \ ↑S, g z = f z - principalPartSum S c z`
- **What**: Constructs a corrected function `g` that fills in removable singularities at the poles `S` and is differentiable on all of `U`, agreeing with `f - principalPartSum` outside `S`.
- **How**: 30-line proof — defines `correction z = if z ∈ S then limUnder (𝓝[≠] z) rem else rem z`. Case-splits on `z ∈ S`: at poles uses `sub_principalPartSum_analyticAt_all` + `correction_eventuallyEq_analyticExt` to transfer differentiability from `g_z`; away from poles uses `hU_open.sdiff S.finite_toSet.isClosed` + `principalPartSum_differentiableAt` + `correction_eventuallyEq_rem`. Key lemma: `DifferentiableAt.congr_of_eventuallyEq`.
- **Hypotheses**: `U` open; `f` differentiable on `U \ S`; `S ⊆ U`; simple poles with matching coefficients.
- **Uses from project**: `sub_principalPartSum_analyticAt_all`, `principalPartSum_differentiableAt`, `principalPartSum`, `correction_eventuallyEq_analyticExt`, `correction_eventuallyEq_rem`, `HasSimplePoleAt`.
- **Used by**: `contourIntegral_eq_sum_winding_coefficients_convex`.
- **Visibility**: public
- **Lines**: 160-190
- **Notes**: >10 lines.

### `private lemma contourIntegral_corrected_eq_rem`
- **Type**: `{f : ℂ → ℂ} {S : Finset ℂ} {c : ℂ → ℂ} {γ : PiecewiseC1Path x x} {g : ℂ → ℂ} (h_g_on_curve : ∀ t ∈ Icc 0 1, g (γ t) = f (γ t) - principalPartSum S c (γ t)) → γ.contourIntegral g = γ.contourIntegral (fun z => f z - principalPartSum S c z)`
- **What**: If `g` equals the remainder on the path image, the two contour integrals coincide.
- **How**: Unfolds `contourIntegral` to `intervalIntegral`, applies `intervalIntegral.integral_congr`, and substitutes pointwise via `h_g_on_curve`.
- **Hypotheses**: pointwise agreement of `g` and the remainder on `γ(Icc 0 1)`.
- **Uses from project**: `PiecewiseC1Path.contourIntegral`, `PiecewiseC1Path.extendedPath_eq`, `principalPartSum`.
- **Used by**: `contourIntegral_eq_sum_winding_coefficients_convex`.
- **Visibility**: private
- **Lines**: 196-208
- **Notes**: none.

### `private lemma corrected_remainder_integrable`
- **Type**: `... (h_g_on_curve ...) (h_rem_int : IntervalIntegrable (contourIntegrand (fun z => f z - principalPartSum S c z) γ) volume 0 1) → IntervalIntegrable (contourIntegrand g γ) volume 0 1`
- **What**: The contour integrand of the corrected `g` is interval-integrable, by EqOn-transfer from the integrand of the remainder.
- **How**: Builds `EqOn` on `uIoc 0 1` using `h_g_on_curve` (subseted to `Ioc ⊆ Icc`) and closes with `h_rem_int.congr h_eqOn.symm`.
- **Hypotheses**: agreement on the curve + integrability of the remainder integrand.
- **Uses from project**: `PiecewiseC1Path.contourIntegrand`, `principalPartSum`.
- **Used by**: `contourIntegral_eq_sum_winding_coefficients_convex`.
- **Visibility**: private
- **Lines**: 212-227
- **Notes**: none.

### `theorem contourIntegral_eq_sum_winding_coefficients_convex`
- **Type**: `{f : ℂ → ℂ} {U : Set ℂ} {S : Finset ℂ} {c : ℂ → ℂ} (γ : PiecewiseC1Path x x) (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty) (hf_diff : DifferentiableOn ℂ f (U \ ↑S)) (hS_sub : ↑S ⊆ U) (h_pole ...) (h_coeff ...) (hγ : ∀ t ∈ Icc 0 1, γ t ∈ U) (hγ_avoids : ∀ s ∈ S, ∀ t, γ t ≠ s) (hδ ...) (h_rem_int ...) (h_pp_int ...) (hI ...) → γ.contourIntegral f = ∑ s ∈ S, 2*↑Real.pi*I * generalizedWindingNumber γ s * c s`
- **What**: Residue theorem for convex domains: contour integral of a meromorphic `f` (simple poles at `S`) equals the sum of `2πi · winding · coefficient`.
- **How**: Obtains corrected `g` via `sub_principalPartSum_corrected_differentiableOn`; shows `γ.contourIntegral g = 0` using `PiecewiseC1Path.contourIntegral_eq_zero_of_differentiableOn_convex_aux` (Cauchy for convex); then applies `contourIntegral_decomp_of_simple_poles` and rewrites the remainder integral to 0 via `contourIntegral_corrected_eq_rem`.
- **Hypotheses**: `U` convex/open/nonempty; `f` holomorphic on `U \ S`; `S ⊆ U`; matching simple poles; `γ` stays in `U`, avoids `S` with positive separation; standard integrability.
- **Uses from project**: `sub_principalPartSum_corrected_differentiableOn`, `PiecewiseC1Path.contourIntegral_eq_zero_of_differentiableOn_convex_aux`, `corrected_remainder_integrable`, `contourIntegral_decomp_of_simple_poles`, `contourIntegral_corrected_eq_rem`, `generalizedWindingNumber`, `HasSimplePoleAt`, `principalPartSum`.
- **Used by**: `contourIntegral_eq_zero_of_zero_coefficients_convex`, `contourIntegral_eq_sum_winding_residues_convex`.
- **Visibility**: public
- **Lines**: 234-267
- **Notes**: >10 lines; main theorem of the file.

### `theorem contourIntegral_eq_zero_of_zero_coefficients_convex`
- **Type**: Same hypothesis bundle as above plus `(hc_zero : ∀ s ∈ S, c s = 0)` → `γ.contourIntegral f = 0`.
- **What**: When all residues vanish, the contour integral of `f` is zero (special case of residue theorem).
- **How**: Rewrites with the residue theorem, then `Finset.sum_eq_zero` using `hc_zero` and `mul_zero`.
- **Hypotheses**: residue theorem hypotheses + `c s = 0` for all `s ∈ S`.
- **Uses from project**: `contourIntegral_eq_sum_winding_coefficients_convex`, `HasSimplePoleAt`, `principalPartSum`, `PiecewiseC1Path.contourIntegrand`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 275-300
- **Notes**: none.

### `theorem contourIntegral_eq_sum_winding_residues_convex`
- **Type**: Adds `(h_res : ∀ s ∈ S, residue f s = c s)` and concludes `γ.contourIntegral f = ∑ s ∈ S, 2*↑Real.pi*I * generalizedWindingNumber γ s * residue f s`.
- **What**: Same as `contourIntegral_eq_sum_winding_coefficients_convex` but stated using the `residue` function instead of raw coefficients.
- **How**: Rewrites via residue theorem; closes with `Finset.sum_congr rfl` substituting `c s = residue f s`.
- **Hypotheses**: same as residue theorem + `residue f s = c s` on `S`.
- **Uses from project**: `contourIntegral_eq_sum_winding_coefficients_convex`, `residue`, `HasSimplePoleAt`, `principalPartSum`, `PiecewiseC1Path.contourIntegrand`, `generalizedWindingNumber`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 306-330
- **Notes**: none.

---

## File Summary
`MeromorphicCauchy.lean` (332 lines, 0 sorries, 0 axioms) extends the Dixon-style Cauchy theorem for convex open domains to meromorphic functions with finitely many simple poles via pole subtraction. The core construction (`sub_principalPartSum_corrected_differentiableOn`) builds a differentiable correction that fills in removable singularities at each pole; combined with the principal-part winding-sum (`contourIntegral_principalPartSum_eq` from `SimplePoleIntegral`) this yields the convex-domain residue theorem `contourIntegral_eq_sum_winding_coefficients_convex` and its residue-function variant `contourIntegral_eq_sum_winding_residues_convex`. The file contains 7 public theorems and 4 private helpers; the `correction_*` lemmas glue together pointwise indicator equalities with `EventuallyEq` on `𝓝 z` to enable `DifferentiableAt.congr_of_eventuallyEq`.
