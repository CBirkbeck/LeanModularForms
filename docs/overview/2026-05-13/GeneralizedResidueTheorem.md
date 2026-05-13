# Inventory: GeneralizedResidueTheorem.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheorem.lean`
Lines: 410

### `theorem remainder_differentiableOn_of_simplePoles`
- **Type**: `{U : Set ℂ} (hU : IsOpen U) (S : Finset ℂ) (hS_in_U : ↑S ⊆ U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S)) (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s) : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U \ (↑S : Set ℂ), g z = f z - principalPartSum S (fun s => residue f s) z`
- **What**: Packages the existence of a holomorphic remainder `g = f - principalPartSum S (residue f)` on all of `U` when `f` has simple poles at the points of `S`.
- **How**: One-line application of `sub_principalPartSum_corrected_differentiableOn`, providing the residue–coefficient match via `residue_eq_coeff_of_hasSimplePoleAt`.
- **Hypotheses**: `U` open, `S ⊆ U`, `f` holomorphic on `U \ S`, simple-pole hypothesis at each `s ∈ S`.
- **Uses from project**: `sub_principalPartSum_corrected_differentiableOn`, `principalPartSum`, `residue`, `HasSimplePoleAt`, `residue_eq_coeff_of_hasSimplePoleAt`.
- **Used by**: `generalizedResidueTheorem_simplePoles_convex`.
- **Visibility**: public
- **Lines**: 74-83
- **Notes**: thin wrapper

### `theorem generalizedResidueTheorem_simplePoles_structural`
- **Type**: `{U : Set ℂ} (_hU : IsOpen U) (S : Finset ℂ) (_hS_in_U : ↑S ⊆ U) (f : ℂ → ℂ) (_hf : DifferentiableOn ℂ f (U \ ↑S)) (γ : PiecewiseC1Path x x) (_hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s) (hγ_in_U : ∀ t ∈ Icc 0 1, γ t ∈ U) (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc 0 1, γ t ≠ s) (hδ : ∃ δ > 0, ...) (g : ℂ → ℂ) (_hg_diff : DifferentiableOn ℂ g U) (hg_agree : ∀ z ∈ U \ ↑S, g z = f z - principalPartSum S (residue f) z) (hg_zero : γ.contourIntegral g = 0) (h_rem_int h_pp_int hI : ...) : γ.contourIntegral f = ∑ s ∈ S, 2 * ↑π * I * generalizedWindingNumber γ s * residue f s`
- **What**: Structural form of the residue theorem for simple poles — the contour integral of `f` equals the winding-number-weighted residue sum, given a holomorphic remainder `g` agreeing with `f - pp` and having vanishing contour integral.
- **How**: Show `γ.contourIntegral g = γ.contourIntegral (f - pp)` via `intervalIntegral.integral_congr` on the curve (using `hg_agree` pointwise), so `γ.contourIntegral (f - pp) = 0`; then apply `contourIntegral_decomp_of_simple_poles` to split `f = (f - pp) + pp` and combine.
- **Hypotheses**: U open, S ⊆ U, f holomorphic on U \ S, γ avoids S with a uniform positive distance δ, integrability of remainder/principal-part/per-pole integrands, holomorphic remainder g agreeing off S with vanishing contour integral.
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.contourIntegral`, `PiecewiseC1Path.extendedPath_eq`, `PiecewiseC1Path.contourIntegrand`, `principalPartSum`, `residue`, `HasSimplePoleAt`, `generalizedWindingNumber`, `contourIntegral_decomp_of_simple_poles`.
- **Used by**: `generalizedResidueTheorem_simplePoles_convex`, `generalizedResidueTheorem_simplePoles_CPV_structural`.
- **Visibility**: public
- **Lines**: 97-139
- **Notes**: ~43 line proof; many hypotheses underscore-marked (passed via `contourIntegral_decomp_of_simple_poles`)

### `theorem generalizedResidueTheorem_simplePoles_convex`
- **Type**: `{U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty) (S : Finset ℂ) (hS_in_U : ↑S ⊆ U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S)) (γ : PiecewiseC1Path x x) (hSimplePoles ...) (hγ_in_U hγ_avoids hδ) (h_rem_int h_pp_int hI) : γ.contourIntegral f = ∑ s ∈ S, 2 * ↑π * I * generalizedWindingNumber γ s * residue f s`
- **What**: Generalized residue theorem for simple poles on a convex open set — the `hg_zero` hypothesis is discharged automatically via Cauchy's theorem on convex domains.
- **How**: Build `g` via `remainder_differentiableOn_of_simplePoles`; transport integrability of the remainder to integrability of `g` using `IntervalIntegrable.congr` and `hg_agree`; discharge `hg_zero` via `γ.contourIntegral_eq_zero_of_differentiableOn_convex_aux`; then apply `generalizedResidueTheorem_simplePoles_structural`.
- **Hypotheses**: U convex/open/nonempty, S ⊆ U, f holomorphic on U \ S, γ avoids S with positive distance, all interval-integrability hypotheses.
- **Uses from project**: `remainder_differentiableOn_of_simplePoles`, `generalizedResidueTheorem_simplePoles_structural`, `PiecewiseC1Path.contourIntegrand`, `PiecewiseC1Path.contourIntegral_eq_zero_of_differentiableOn_convex_aux`, `principalPartSum`, `residue`, `generalizedWindingNumber`.
- **Used by**: `generalizedResidueTheorem_simplePoles_convex_CPV`.
- **Visibility**: public
- **Lines**: 148-186
- **Notes**: ~17 line proof

### `theorem generalizedResidueTheorem_simplePoles_convex_alt`
- **Type**: same signature as the convex version (without explicit g).
- **What**: Alternative statement equivalent to the convex theorem, exposed as a direct reduction to the pre-existing `contourIntegral_eq_sum_winding_residues_convex` from MeromorphicCauchy with explicit residue–coefficient bookkeeping.
- **How**: Set `c s = residue f s`; produce a coefficient witness `(hSimplePoles s hs).coeff = c s` via `residue_eq_coeff_of_hasSimplePoleAt`; trivially `residue f s = c s`; then call `contourIntegral_eq_sum_winding_residues_convex`.
- **Hypotheses**: U convex/open/nonempty, S ⊆ U, f holomorphic on U \ S, γ avoids S with positive distance, all interval-integrability hypotheses.
- **Uses from project**: `contourIntegral_eq_sum_winding_residues_convex`, `residue_eq_coeff_of_hasSimplePoleAt`, `principalPartSum`, `residue`, `generalizedWindingNumber`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 193-221
- **Notes**: equivalence-of-statements lemma

### `theorem generalizedResidueTheorem`
- **Type**: `{U : Set ℂ} (_hU : IsOpen U) (S : Finset ℂ) (_hS_in_U : ↑S ⊆ U) (f : ℂ → ℂ) (_hf : DifferentiableOn ℂ f (U \ ↑S)) (γ : PwC1Immersion x x) (_h_null : IsNullHomologous γ U) (_hMero : ∀ s ∈ S, MeromorphicAt f s) (_hCondA : SatisfiesConditionA' γ f S (poleOrderAt f)) (_hCondB : SatisfiesConditionB γ f S) (hCancel : HasCauchyPVOn S (f - pp) γ.toPiecewiseC1Path 0) (hPV_sing : HasCauchyPVOn S pp γ.toPiecewiseC1Path (∑ ...)) (hI_sing hI_rem) : HasCauchyPVOn S f γ.toPiecewiseC1Path (2 * ↑π * I * ∑ s ∈ S, generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s)`
- **What**: The full Hungerbuhler-Wasem residue theorem (Theorem 3.3): for a meromorphic function on a null-homologous PwC1 immersion satisfying conditions (A') and (B), with the higher-order cancellation supplied as a hypothesis, the CPV equals the winding-number-weighted residue sum.
- **How**: Equate target value `2πi · ∑ w · res` with `∑ 2πi · w · res` via `Finset.mul_sum` and `Finset.sum_congr` (ring); then apply `hasCauchyPVOn_of_tendsto_sub` with cancellation `hCancel` and singular CPV `hPV_sing`.
- **Hypotheses**: U open, S ⊆ U, f holomorphic off S, γ null-homologous PwC1 immersion, meromorphic at S, (A')+(B), CPV vanishing of remainder, CPV of singular part, integrability of cutoff integrands.
- **Uses from project**: `PwC1Immersion`, `IsNullHomologous`, `MeromorphicAt`, `SatisfiesConditionA'`, `SatisfiesConditionB`, `poleOrderAt`, `HasCauchyPVOn`, `principalPartSum`, `residue`, `generalizedWindingNumber`, `cpvIntegrandOn`, `hasCauchyPVOn_of_tendsto_sub`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 274-307
- **Notes**: top-level "honest modular design" statement; depends on hypotheses (`hCancel`, `hPV_sing`) supplied externally

### `theorem generalizedResidueTheorem_simplePoles_convex_CPV`
- **Type**: same convex-domain simple-pole hypotheses, conclusion `HasCauchyPVOn S f γ (∑ ...)`.
- **What**: CPV-flavored version of the convex simple-pole residue theorem: produces a `HasCauchyPVOn` witness (suitable when the caller wants the CPV predicate rather than an equation of integrals).
- **How**: Apply `generalizedResidueTheorem_simplePoles_convex` to obtain the contour-integral equation, then transport via `hasCauchyPVOn_of_avoids` (CPV reduces to ordinary integral when γ avoids S).
- **Hypotheses**: U convex/open/nonempty, S ⊆ U, f holomorphic on U \ S, γ avoids S with positive distance, all interval-integrability hypotheses.
- **Uses from project**: `generalizedResidueTheorem_simplePoles_convex`, `HasCauchyPVOn`, `hasCauchyPVOn_of_avoids`, `principalPartSum`, `residue`, `generalizedWindingNumber`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 319-344
- **Notes**: avoidance-case CPV variant

### `theorem generalizedResidueTheorem_simplePoles_CPV_structural`
- **Type**: structural simple-pole hypotheses (including explicit `g`, `hg_zero`), conclusion `HasCauchyPVOn S f γ (∑ ...)`.
- **What**: Structural CPV variant of the simple-pole residue theorem — modular form taking `hg_zero` as an explicit input, returning a `HasCauchyPVOn` predicate.
- **How**: Apply `generalizedResidueTheorem_simplePoles_structural` to get the contour-integral equation, then transport via `hasCauchyPVOn_of_avoids`.
- **Hypotheses**: U open, S ⊆ U, f holomorphic on U \ S, γ avoids S with positive distance, holomorphic remainder g with vanishing contour integral, interval-integrability of remainder/principal-part/per-pole integrands.
- **Uses from project**: `generalizedResidueTheorem_simplePoles_structural`, `HasCauchyPVOn`, `hasCauchyPVOn_of_avoids`, `principalPartSum`, `residue`, `generalizedWindingNumber`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 354-382
- **Notes**: structural CPV variant

### `theorem conditions_automatic_for_simplePoles`
- **Type**: `(γ : PwC1Immersion x x) (f : ℂ → ℂ) (S : Finset ℂ) (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s) (hAngles : ∀ s ∈ S, ∀ t₀ ∈ Icc 0 1, γ t₀ = s → ∀ ht₀_Ioo, t₀ ∈ partition → ∃ p q, q ≠ 0 ∧ Coprime p q ∧ angleAtCrossing γ t₀ ht₀_Ioo = ↑p * π / ↑q) : SatisfiesConditionA' γ f S (fun _ => 1) ∧ SatisfiesConditionB γ f S`
- **What**: For simple poles, condition (A') (with pole order 1) and condition (B) hold automatically, given rational angles at crossings.
- **How**: One-line dispatch to `conditions_automatic_simple_poles` from FlatnessConditions.
- **Hypotheses**: simple-pole hypothesis at each s ∈ S, rational-angle hypothesis at each crossing.
- **Uses from project**: `PwC1Immersion`, `HasSimplePoleAt`, `angleAtCrossing`, `SatisfiesConditionA'`, `SatisfiesConditionB`, `conditions_automatic_simple_poles`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 391-400
- **Notes**: thin wrapper

### `theorem conditionA'_automatic_for_simplePoles`
- **Type**: `(γ : PwC1Immersion x x) (f : ℂ → ℂ) (S : Finset ℂ) (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s) : SatisfiesConditionA' γ f S (fun _ => 1)`
- **What**: Condition (A') of order 1 holds automatically for simple poles on any PwC1 immersion (no rational-angle hypothesis needed).
- **How**: One-line dispatch to `satisfiesConditionA'_of_simplePoles`.
- **Hypotheses**: simple-pole at each s ∈ S.
- **Uses from project**: `PwC1Immersion`, `HasSimplePoleAt`, `SatisfiesConditionA'`, `satisfiesConditionA'_of_simplePoles`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 404-408
- **Notes**: thin wrapper

## File Summary

Eight theorems building the simple-pole and full (A')/(B) versions of the Hungerbühler-Wasem generalized residue theorem. The core argument `generalizedResidueTheorem_simplePoles_structural` decomposes `f = g + pp` with a holomorphic remainder `g`; convex/CPV-form/full-version corollaries follow by discharging hypotheses (`hg_zero` via convex Cauchy; CPV via `hasCauchyPVOn_of_avoids`). The top-level `generalizedResidueTheorem` keeps higher-order cancellation as an explicit hypothesis (honest modular design). All theorems are public, no `sorry`/`axiom`/heartbeat overrides; no `Used by` within this file beyond `generalizedResidueTheorem_simplePoles_structural` (used by `_convex`) and `remainder_differentiableOn_of_simplePoles` (used by `_convex`).
