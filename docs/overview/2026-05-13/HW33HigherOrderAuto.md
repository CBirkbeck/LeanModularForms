# Inventory: HW33HigherOrderAuto.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HW33HigherOrderAuto.lean` (322 lines)

Purpose: Auto-discharge wrappers around the C3/C4 higher-order avoidance theorems in `HW33HigherOrderC4`. Given that γ is Lipschitz and avoids the pole set with a positive margin δ, every interval-integrability hypothesis required by the underlying C3/C4 theorems is automatically derived.

Imports: `LeanModularForms.ForMathlib.HW33HigherOrderC4`.

Namespace: `LeanModularForms` (entire file is in `noncomputable section`).

---

### `theorem intervalIntegrable_pow_inv_mul_deriv_of_avoids`
- **Type**: `(γ : PiecewiseC1Path x x) (s : ℂ) (k : ℕ) {δ : ℝ} (hδ_pos : 0 < δ) (hδ_bd : ∀ t ∈ Icc (0:ℝ) 1, δ ≤ ‖γ.toPath.extend t - s‖) {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) : IntervalIntegrable (fun t => 1 / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t) volume 0 1`
- **What**: Integrability on `[0,1]` of `1/(γ(t)-s)^k · γ'(t)` when γ is Lipschitz and stays at distance ≥ δ from s.
- **How**: `Measure.integrableOn_of_bounded` to bound `deriv γ` (via `norm_deriv_le_of_lipschitz`); `continuousOn_const.div` on `1/(γ-s)^k` since γ−s ≠ 0; combine with `Integrable.bdd_mul` using bound `1/δ^k`.
- **Hypotheses**: γ ∈ PiecewiseC1Path, δ > 0, distance bound, Lipschitz.
- **Uses from project**: `PiecewiseC1Path`, `norm_deriv_le_of_lipschitz`.
- **Used by**: `hasCauchyPVOn_finset_pow_inv_of_avoids_lip`, `contourIntegrand_finset_pow_inv_intervalIntegrable_of_avoids_lip`, `hasCauchyPVOn_add_higherOrderPolar_of_avoids_lip`, `hasCauchyPVOn_add_higherOrderPolarSum_of_avoids_lip`.
- **Visibility**: public
- **Lines**: 39–71
- **Notes**: >30 lines (33 lines); no sorry/axiom.

### `theorem measurableSet_cpvIntegrandOn_zero`
- **Type**: `{y : ℂ} (S : Finset ℂ) (γ : PiecewiseC1Path x y) (ε : ℝ) : MeasurableSet {t : ℝ | ∃ s ∈ S, ‖γ.toPath.extend t - s‖ ≤ ε}`
- **What**: The set of times t whose image γ(t) is within ε of some s ∈ S is measurable.
- **How**: Rewrite as the finite union `⋃ s∈S, {t | ‖γ(t)-s‖ ≤ ε}`; each set is the preimage of `Iic ε` under a continuous function, then `Finset.finite_toSet.measurableSet_biUnion`.
- **Hypotheses**: γ continuous (built into `PiecewiseC1Path`).
- **Uses from project**: `PiecewiseC1Path`.
- **Used by**: `aestronglyMeasurable_cpvIntegrandOn`.
- **Visibility**: public
- **Lines**: 76–86

### `theorem norm_cpvIntegrandOn_le_norm_contourIntegrand`
- **Type**: `{y : ℂ} (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (ε : ℝ) (t : ℝ) : ‖cpvIntegrandOn S f γ.toPath.extend ε t‖ ≤ ‖PiecewiseC1Path.contourIntegrand f γ t‖`
- **What**: Pointwise norm bound: the CPV integrand is either 0 (inside ε-ball of S) or equals the contour integrand.
- **How**: Unfold `cpvIntegrandOn`, `contourIntegrand`; `split_ifs` and use `norm_zero` / `rfl`.
- **Hypotheses**: none beyond signature.
- **Uses from project**: `cpvIntegrandOn`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path.extendedPath_eq`.
- **Used by**: `cpvIntegrandOn_intervalIntegrable_of_contourIntegrand`.
- **Visibility**: public
- **Lines**: 94–101

### `theorem aestronglyMeasurable_cpvIntegrandOn`
- **Type**: `{y : ℂ} (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (ε : ℝ) {μ : Measure ℝ} (h_contour_meas : AEStronglyMeasurable (PiecewiseC1Path.contourIntegrand f γ) μ) : AEStronglyMeasurable (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) μ`
- **What**: AE-strong-measurability of the CPV integrand from that of the contour integrand.
- **How**: Express CPV integrand as `Set.piecewise A 0 contourIntegrand` where A is measurable by `measurableSet_cpvIntegrandOn_zero`; conclude via `AEStronglyMeasurable.piecewise`.
- **Hypotheses**: contour integrand AE-strongly measurable.
- **Uses from project**: `cpvIntegrandOn`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path.extendedPath_eq`, `measurableSet_cpvIntegrandOn_zero`.
- **Used by**: `cpvIntegrandOn_intervalIntegrable_of_contourIntegrand`.
- **Visibility**: public
- **Lines**: 108–127

### `theorem cpvIntegrandOn_intervalIntegrable_of_contourIntegrand`
- **Type**: `{y : ℂ} (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (ε : ℝ) (h_contour_int : IntervalIntegrable (PiecewiseC1Path.contourIntegrand f γ) volume 0 1) : IntervalIntegrable (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1`
- **What**: From integrability of the contour integrand, deduce integrability of the CPV integrand.
- **How**: `IntervalIntegrable.mono_fun` using AE-measurability (`aestronglyMeasurable_cpvIntegrandOn`) and the pointwise norm bound (`norm_cpvIntegrandOn_le_norm_contourIntegrand`).
- **Hypotheses**: contour integrand interval-integrable on `[0,1]`.
- **Uses from project**: `cpvIntegrandOn`, `PiecewiseC1Path.contourIntegrand`, `aestronglyMeasurable_cpvIntegrandOn`, `norm_cpvIntegrandOn_le_norm_contourIntegrand`.
- **Used by**: `hasCauchyPVOn_add_higherOrderPolar_of_avoids_lip`, `hasCauchyPVOn_add_higherOrderPolarSum_of_avoids_lip`.
- **Visibility**: public
- **Lines**: 134–144

### `theorem hasCauchyPVOn_finset_pow_inv_of_avoids_lip`
- **Type**: `(S : Finset ℂ) (k : ℕ) (hk : 2 ≤ k) (c : ℂ → ℂ) (γ : PiecewiseC1Path x x) {δ : ℝ} (hδ_pos : 0 < δ) (hδ_bd : ∀ s ∈ S, ∀ t ∈ Icc (0:ℝ) 1, δ ≤ ‖γ t - s‖) {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) : HasCauchyPVOn S (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ 0`
- **What**: C-3 higher-order single-power avoidance form: ∑ c(s)/(z-s)^k has CPV zero on γ under Lipschitz + avoidance, auto-deriving interval-integrability.
- **How**: Apply `hasCauchyPVOn_finset_pow_inv_of_avoids` (from C4 file); the per-s integrability hypothesis is discharged via `intervalIntegrable_pow_inv_mul_deriv_of_avoids`.
- **Hypotheses**: k ≥ 2, δ-margin avoidance, Lipschitz.
- **Uses from project**: `HasCauchyPVOn`, `PiecewiseC1Path`, `hasCauchyPVOn_finset_pow_inv_of_avoids`, `intervalIntegrable_pow_inv_mul_deriv_of_avoids`, `PiecewiseC1Path.extendedPath_eq`.
- **Used by**: `hasCauchyPVOn_finset_pow_inv_of_avoids_lip_avoids`.
- **Visibility**: public
- **Lines**: 153–162

### `theorem hasCauchyPVOn_finset_pow_inv_of_avoids_lip_avoids`
- **Type**: `(S : Finset ℂ) (k : ℕ) (hk : 2 ≤ k) (c : ℂ → ℂ) (γ : PiecewiseC1Path x x) (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ s) {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) : HasCauchyPVOn S (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ 0`
- **What**: Same as previous but with the positive-margin δ auto-derived from pointwise avoidance.
- **How**: `avoids_finset_delta_bound` produces δ from pointwise avoidance, then forward to `hasCauchyPVOn_finset_pow_inv_of_avoids_lip`.
- **Hypotheses**: k ≥ 2, pointwise avoidance, Lipschitz.
- **Uses from project**: `HasCauchyPVOn`, `PiecewiseC1Path`, `avoids_finset_delta_bound`, `hasCauchyPVOn_finset_pow_inv_of_avoids_lip`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 167–173

### `theorem contourIntegrand_finset_pow_inv_intervalIntegrable_of_avoids_lip`
- **Type**: `(S : Finset ℂ) (k : ℕ) (c : ℂ → ℂ) (γ : PiecewiseC1Path x x) {δ : ℝ} (hδ_pos : 0 < δ) (hδ_bd : ∀ s ∈ S, ∀ t ∈ Icc (0:ℝ) 1, δ ≤ ‖γ t - s‖) {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) : IntervalIntegrable (PiecewiseC1Path.contourIntegrand (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ) volume 0 1`
- **What**: The full contour integrand `(∑ c(s)/(γ(t)-s)^k) · γ'(t)` is interval-integrable on `[0,1]`.
- **How**: Show each summand `c(s)/(γ(t)-s)^k · γ'(t)` is integrable via `intervalIntegrable_pow_inv_mul_deriv_of_avoids` plus `.const_mul`; then `IntervalIntegrable.sum` over S and rewrite `Finset.sum_apply` to commute the sum past the function abstraction.
- **Hypotheses**: δ-margin avoidance, Lipschitz.
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path.extendedPath_eq`, `intervalIntegrable_pow_inv_mul_deriv_of_avoids`.
- **Used by**: `hasCauchyPVOn_add_higherOrderPolar_of_avoids_lip`, `hasCauchyPVOn_add_higherOrderPolarSum_of_avoids_lip`.
- **Visibility**: public
- **Lines**: 180–217
- **Notes**: >30 lines (38 lines); intricate funext + Finset.sum_apply rearrangement.

### `theorem hasCauchyPVOn_add_higherOrderPolar_of_avoids_lip`
- **Type**: `(S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) {L : ℂ} {δ : ℝ} (hδ_pos : 0 < δ) (hδ_bd : ∀ s ∈ S, ∀ t ∈ Icc (0:ℝ) 1, δ ≤ ‖γ t - s‖) (h_f : HasCauchyPVOn S f γ L) (h_f_int : ∀ ε > 0, IntervalIntegrable (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1) (k : ℕ) (hk : 2 ≤ k) (c : ℂ → ℂ) {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) : HasCauchyPVOn S (fun z => f z + ∑ s ∈ S, c s / (z - s) ^ k) γ L`
- **What**: Adding the higher-order polar sum to f preserves CPV value L, with all integrability of the polar part auto-discharged.
- **How**: Forward to `hasCauchyPVOn_add_higherOrderPolar_of_avoids`; auto-derive `h_int_HO` per-s using `intervalIntegrable_pow_inv_mul_deriv_of_avoids` and CPV integrability via `cpvIntegrandOn_intervalIntegrable_of_contourIntegrand` + `contourIntegrand_finset_pow_inv_intervalIntegrable_of_avoids_lip`.
- **Hypotheses**: k ≥ 2, δ-margin, f's CPV and f's CPV-integrand integrability, Lipschitz.
- **Uses from project**: `HasCauchyPVOn`, `PiecewiseC1Path`, `cpvIntegrandOn`, `intervalIntegrable_pow_inv_mul_deriv_of_avoids`, `PiecewiseC1Path.extendedPath_eq`, `hasCauchyPVOn_add_higherOrderPolar_of_avoids`, `cpvIntegrandOn_intervalIntegrable_of_contourIntegrand`, `contourIntegrand_finset_pow_inv_intervalIntegrable_of_avoids_lip`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 223–247
- **Notes**: >20 lines.

### `theorem hasCauchyPVOn_add_higherOrderPolarSum_of_avoids_lip`
- **Type**: `(S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) {L : ℂ} {δ : ℝ} (hδ_pos : 0 < δ) (hδ_bd : ∀ s ∈ S, ∀ t ∈ Icc (0:ℝ) 1, δ ≤ ‖γ t - s‖) (h_f : HasCauchyPVOn S f γ L) (h_f_int : ∀ ε > 0, IntervalIntegrable (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1) (M : ℕ) (c_HO : ℕ → ℂ → ℂ) {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) : HasCauchyPVOn S (fun z => f z + ∑ k ∈ Finset.Ico 2 (M+1), ∑ s ∈ S, c_HO k s / (z - s) ^ k) γ L`
- **What**: Multi-power version: adding the double sum (over k ∈ [2,M] and over s ∈ S) preserves the CPV value, with all integrability auto-discharged.
- **How**: Forward to `hasCauchyPVOn_add_higherOrderPolarSum_of_avoids`; per-(k,s) integrability via `intervalIntegrable_pow_inv_mul_deriv_of_avoids`, CPV integrability via the contour bridge.
- **Hypotheses**: δ-margin, f's CPV and CPV-integrand integrability, Lipschitz.
- **Uses from project**: `HasCauchyPVOn`, `PiecewiseC1Path`, `cpvIntegrandOn`, `intervalIntegrable_pow_inv_mul_deriv_of_avoids`, `PiecewiseC1Path.extendedPath_eq`, `hasCauchyPVOn_add_higherOrderPolarSum_of_avoids`, `cpvIntegrandOn_intervalIntegrable_of_contourIntegrand`, `contourIntegrand_finset_pow_inv_intervalIntegrable_of_avoids_lip`.
- **Used by**: `generalizedResidueTheorem_higherOrder_avoids_closed_lip`.
- **Visibility**: public
- **Lines**: 251–276
- **Notes**: >20 lines.

### `theorem generalizedResidueTheorem_higherOrder_avoids_closed_lip`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) (hU_bounded : Bornology.IsBounded U) (S : Finset ℂ) (hS_in_U : ↑S ⊆ U) (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U) (f_simple : ℂ → ℂ) (hf_simple : DifferentiableOn ℂ f_simple (U \ ↑S)) (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f_simple s) (M : ℕ) (c_HO : ℕ → ℂ → ℂ) (h_simple_int : ∀ ε > 0, IntervalIntegrable (fun t => cpvIntegrandOn S f_simple γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1) (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0:ℝ) 1, γ.toPiecewiseC1Path t ≠ s) {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) : HasCauchyPVOn S (fun z => f_simple z + ∑ k ∈ Finset.Ico 2 (M+1), ∑ s ∈ S, c_HO k s / (z - s)^k) γ.toPiecewiseC1Path (2 * ↑Real.pi * I * ∑ s ∈ S, generalizedWindingNumber γ.toPiecewiseC1Path s * residue f_simple s)`
- **What**: C-4 closed null-homologous avoidance form, fully auto-discharged: residue theorem for f_simple + higher-order terms, with higher-order integrability assumptions eliminated.
- **How**: `avoids_finset_delta_bound` yields δ; then call `hasCauchyPVOn_add_higherOrderPolarSum_of_avoids_lip`, supplying the simple-pole residue base case `generalizedResidueTheorem_simplePoles_nullHomologous_closed`.
- **Hypotheses**: U open/bounded/nonempty, S ⊆ U, γ null-homologous immersion, f_simple differentiable off S with simple poles, pointwise avoidance, Lipschitz.
- **Uses from project**: `HasCauchyPVOn`, `PwC1Immersion`, `IsNullHomologous`, `HasSimplePoleAt`, `cpvIntegrandOn`, `generalizedWindingNumber`, `residue`, `avoids_finset_delta_bound`, `hasCauchyPVOn_add_higherOrderPolarSum_of_avoids_lip`, `generalizedResidueTheorem_simplePoles_nullHomologous_closed`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 294–318
- **Notes**: >20 lines; capstone theorem of file.

---

## File Summary

- **Declarations**: 10 theorems (all public, no axioms, no sorries).
- **Theme**: Convert pointwise avoidance + Lipschitz of γ into the integrability hypotheses required by the C3/C4 higher-order residue theorems, culminating in `generalizedResidueTheorem_higherOrder_avoids_closed_lip` — a fully auto-discharged closed-curve residue formula for `f_simple` + higher-order polar terms.
- **Key dependencies**: `HW33HigherOrderC4` (provides `hasCauchyPVOn_finset_pow_inv_of_avoids`, `hasCauchyPVOn_add_higherOrderPolar_of_avoids`, `hasCauchyPVOn_add_higherOrderPolarSum_of_avoids`, `avoids_finset_delta_bound`, `generalizedResidueTheorem_simplePoles_nullHomologous_closed`).
- **Internal call graph**: `intervalIntegrable_pow_inv_mul_deriv_of_avoids` is the workhorse; the contour integrability lemma builds on it; the final closed theorem chains through the Sum-lip wrapper.
- **Notes**: No `set_option`, no `sorry`, no `axiom`, no `TODO`. File closes its top-level `noncomputable section` at line 322 with `end`.
