# ResidueCircleIntegral.lean Inventory

**Path**: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ResidueCircleIntegral.lean`
**Top-level**: `noncomputable section` (no namespace)
**Imports**: `LeanModularForms.ForMathlib.Residue`, `Mathlib.Analysis.Complex.CauchyIntegral`

---

### private lemma `limUnder_eq_of_eventuallyEq`
- **Type**: `(f =ᶠ[l] g) → l.limUnder f = l.limUnder g`.
- **What**: Two `limUnder`s coincide when their functions agree eventually.
- **How**: Unfolds `Filter.limUnder`, applies `congr 1`, then extensionality on filter neighborhoods: for each open set `s`, shows the preimage in `l` matches via `inter_mem ... h` and superset reasoning (using both directions, `h` and `h.symm`) — 13 tactic lines (>10 lines; key lemmas `mem_of_superset`, `inter_mem`).
- **Hypotheses**: eventual equality on a filter `l`.
- **Uses-from-project**: none beyond Mathlib (`Filter.limUnder`).
- **Used by**: `residue_congr`.
- **Visibility**: private
- **Lines**: 42–57
- **Notes**: Bypasses `Tendsto`-based reasoning to compare two `lim`s directly.

### private lemma `circleIntegral_eq_zero_of_analyticOnNhd_ball`
- **Type**: `0 < r → r < R → AnalyticOnNhd ℂ f (ball z₀ R) → ∮ z in C(z₀, r), f z = 0`.
- **What**: A circle integral inside a strictly larger analytic ball vanishes.
- **How**: Applies `circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty`, supplying `ContinuousOn` on the closed ball via `hf.continuousOn.mono (closedBall_subset_ball hrR)` and differentiability inside via `(hf z (ball_subset_ball hrR.le hz)).differentiableAt`.
- **Hypotheses**: `0 < r`; `r < R`; analyticity on `ball z₀ R`.
- **Uses-from-project**: none beyond Mathlib.
- **Used by**: `residue_eq_zero_of_analyticAt`, `circleIntegral_simple_pole_eq`.
- **Visibility**: private
- **Lines**: 61–66
- **Notes**: Empty exceptional set; uses Mathlib's Cauchy theorem.

### theorem `residue_eq_zero_of_analyticAt`
- **Type**: `AnalyticAt ℂ f z₀ → residue f z₀ = 0`.
- **What**: Analytic functions have zero residue.
- **How**: Unfolds `residue`, applies `Filter.Tendsto.limUnder_eq`, then uses `tendsto_nhds_of_eventually_eq` over a punctured neighborhood: filter on `Iio R` and rewrite the integral to zero by `circleIntegral_eq_zero_of_analyticOnNhd_ball` and `mul_zero`.
- **Hypotheses**: `AnalyticAt ℂ f z₀`.
- **Uses-from-project**: `circleIntegral_eq_zero_of_analyticOnNhd_ball`, `residue` (from `Residue`).
- **Used by**: `residue_eq_zero_of_eventually_differentiableAt`; downstream residue computations.
- **Visibility**: public
- **Lines**: 71–80
- **Notes**: 8-line proof.

### theorem `residue_eq_zero_of_eventually_differentiableAt`
- **Type**: `(∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ f z) → residue f z₀ = 0`.
- **What**: Eventually-differentiable functions have zero residue.
- **How**: `residue_eq_zero_of_analyticAt` after converting via `Complex.analyticAt_iff_eventually_differentiableAt.mpr`.
- **Hypotheses**: differentiability holds eventually on `𝓝 z₀`.
- **Uses-from-project**: `residue_eq_zero_of_analyticAt`.
- **Used by**: external callers wanting the differentiability-based formulation.
- **Visibility**: public
- **Lines**: 83–86
- **Notes**: 1-line term-mode proof.

### private lemma `simple_pole_eqOn_sphere`
- **Type**: on small spheres inside the punctured nhd, `f = c·(z-z₀)⁻¹ + g`.
- **What**: Reduces "agreement on a punctured neighborhood" to "agreement on a sphere of radius `r`" by excluding the center.
- **How**: For `z ∈ sphere z₀ r`, derive `z ≠ z₀` from `mem_sphere`, then `z ∈ ball z₀ rf` and `z ∈ ball z₀ rf ∩ {z₀}ᶜ`; apply the hypothesis and conclude with `div_eq_mul_inv`.
- **Hypotheses**: `0 < r`; `r < rf`; the decomposition holds on `ball z₀ rf ∩ {z₀}ᶜ`.
- **Uses-from-project**: none beyond Mathlib.
- **Used by**: `circleIntegral_simple_pole_eq`.
- **Visibility**: private
- **Lines**: 92–109
- **Notes**: Bridge from punctured nhd to sphere.

### theorem `circleIntegral_simple_pole_eq`
- **Type**: eventually-in-`r > 0`, `(2πi)⁻¹ · ∮ z in C(z₀, r), f z = c`.
- **What**: Normalized circle integral around a simple pole equals the polar coefficient `c`, for sufficiently small radii.
- **How**: Extracts `rg` (analytic radius for `g`) and `rf` (radius where the decomposition holds); for `r < min rg rf`, applies `simple_pole_eqOn_sphere` to get pointwise equality on the sphere; uses `CircleIntegrable g` (from `ContinuousOn.circleIntegrable`) and `CircleIntegrable (c · (z-z₀)⁻¹)` (from `circleIntegrable_sub_inv_iff.mpr` + `const_fun_smul`); applies `circleIntegral.integral_congr`, `integral_add`, `integral_const_mul`, `integral_sub_center_inv` (yields `2πi`), and `circleIntegral_eq_zero_of_analyticOnNhd_ball` for the `g` term; finishes with `field_simp` (proof spans lines 115–142; >10 lines; key lemmas `circleIntegral.integral_sub_center_inv`, `circleIntegral.integral_congr`, `circleIntegral_eq_zero_of_analyticOnNhd_ball`).
- **Hypotheses**: `AnalyticAt ℂ g z₀`; eventually `f = c/(z-z₀) + g` on `𝓝[≠] z₀`.
- **Uses-from-project**: `simple_pole_eqOn_sphere`, `circleIntegral_eq_zero_of_analyticOnNhd_ball`.
- **Used by**: `residue_eq_of_simple_pole_decomp`.
- **Visibility**: public
- **Lines**: 115–142
- **Notes**: Central computation of the file.

### theorem `residue_eq_of_simple_pole_decomp`
- **Type**: simple-pole decomposition → `residue f z₀ = c`.
- **What**: The residue of a function with a simple-pole decomposition equals the polar coefficient.
- **How**: Unfolds `residue`; uses `tendsto_nhds_of_eventually_eq` applied to `circleIntegral_simple_pole_eq hg hf_eq` and `.limUnder_eq`.
- **Hypotheses**: `AnalyticAt ℂ g z₀`; eventual decomposition on `𝓝[≠] z₀`.
- **Uses-from-project**: `residue`, `circleIntegral_simple_pole_eq`.
- **Used by**: `residue_eq_coeff`.
- **Visibility**: public
- **Lines**: 149–155
- **Notes**: 3-line proof.

### theorem `residue_eq_coeff`
- **Type**: `HasSimplePoleAt f z₀ → residue f z₀ = h.coeff`.
- **What**: Specializes the previous theorem to the `HasSimplePoleAt` predicate.
- **How**: `residue_eq_of_simple_pole_decomp h.regularPart_analyticAt h.eventually_eq`.
- **Hypotheses**: `HasSimplePoleAt f z₀`.
- **Uses-from-project**: `HasSimplePoleAt` (and its `.regularPart_analyticAt`, `.eventually_eq`, `.coeff` accessors), `residue_eq_of_simple_pole_decomp`.
- **Used by**: external uses of the `HasSimplePoleAt` API.
- **Visibility**: public
- **Lines**: 158–160
- **Notes**: 1-line term-mode proof.

### theorem `residue_congr`
- **Type**: `(f =ᶠ[𝓝[≠] z₀] g) → residue f z₀ = residue g z₀`.
- **What**: Residue depends only on the local behavior in a punctured neighborhood.
- **How**: Unfolds `residue`, uses `limUnder_eq_of_eventuallyEq`, expands the eventually condition via `Filter.Eventually` + `Metric.mem_nhdsWithin_iff` to get `ε > 0` and pointwise equality; filters on `Iio ε`, applies `circleIntegral.integral_congr hr_pos.le` on each sphere `sphere z₀ r ⊆ ball ∩ {z₀}ᶜ` (using `mem_sphere` to derive both `z ≠ z₀` and `dist z z₀ < ε`).
- **Hypotheses**: eventual equality on `𝓝[≠] z₀`.
- **Uses-from-project**: `limUnder_eq_of_eventuallyEq`, `residue`.
- **Used by**: downstream rewriting of residues by local replacements.
- **Visibility**: public
- **Lines**: 167–186
- **Notes**: 17-line proof (>10 lines; key lemmas `circleIntegral.integral_congr`, `mem_sphere`).

### theorem `norm_two_pi_i_inv_circleIntegral_tendsto_zero`
- **Type**: `ContinuousAt g z₀ → Tendsto (fun r => (2πi)⁻¹ · ∮ z in C(z₀, r), g z) (𝓝[>] 0) (𝓝 0)`.
- **What**: The normalized circle integral of a function continuous at `z₀` vanishes as `r → 0⁺`.
- **How**: ε-δ proof. From `Metric.continuousAt_iff hg` pick `R` so that `‖g z - g z₀‖ ≤ 1` on `dist z z₀ < R`; set `M := ‖g z₀‖ + 1` (positive); the witness radius is `min R (δ/M)`. For `r` smaller than this radius derive `r < R` and `r < δ/M` (via `hr_abs.symm.trans_lt`), bound `‖g z‖ ≤ M` on `sphere z₀ r` by triangle inequality, then invoke `circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr_pos.le h_bound` and finish with `mul_lt_mul_of_pos_right hr_lt_δM hM_pos` and `div_mul_cancel₀` (proof spans lines 193–227; >10 lines; key lemmas `circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const`, `Metric.continuousAt_iff`).
- **Hypotheses**: `ContinuousAt g z₀`.
- **Uses-from-project**: none beyond Mathlib (consumed downstream by residue calculations).
- **Used by**: downstream estimates for residue limits of continuous remainders.
- **Visibility**: public
- **Lines**: 193–227
- **Notes**: Combines local boundedness with the Mathlib circle-integral norm bound `‖(2πi)⁻¹·∮g‖ ≤ r · C`.

---

## File Summary

ResidueCircleIntegral.lean develops properties of the circle-integral-based `residue f z₀`. Two private helpers (`limUnder_eq_of_eventuallyEq` for comparing `lim`s under filter-equality, and `circleIntegral_eq_zero_of_analyticOnNhd_ball` for vanishing of analytic circle integrals) feed two zero-residue theorems for analytic and eventually-differentiable functions. A third private helper (`simple_pole_eqOn_sphere`) bridges the simple-pole decomposition to sphere-pointwise equality, enabling `circleIntegral_simple_pole_eq` to extract the polar coefficient `c` from `(2πi)⁻¹ · ∮ f`; this drives `residue_eq_of_simple_pole_decomp` and its `HasSimplePoleAt` corollary `residue_eq_coeff`. `residue_congr` shows that residues are local (depend only on `𝓝[≠] z₀`), and `norm_two_pi_i_inv_circleIntegral_tendsto_zero` provides the small-radius decay bound for continuous integrands.
