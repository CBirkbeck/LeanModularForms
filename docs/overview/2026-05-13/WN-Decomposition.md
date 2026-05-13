# WN-Decomposition.md — Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/WindingNumber/Decomposition.lean` (254 lines)

## Entries

### private lemma `no_endpoint_crossing_of_unique_interior`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (honly : …) : γ.toFun γ.a ≠ z₀ ∧ γ.toFun γ.b ≠ z₀`
- **What**: Endpoints of γ don't crash into z₀ when the unique crossing is interior.
- **How**: `refine ⟨fun h => ?_, …⟩`, apply `honly` at each endpoint and discharge by `linarith` against `ht₀.1`, `ht₀.2`.
- **Hypotheses**: interior `t₀`, uniqueness `honly`.
- **Uses-from-project**: `PiecewiseC1Immersion`.
- **Used by**: `cpv_exists_of_unique_crossing`.
- **Visibility**: private.
- **Lines**: 31–39.
- **Notes**: Helper.

### private lemma `cpv_exists_of_unique_crossing`
- **Type**: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ) … : CauchyPrincipalValueExists' (·⁻¹∘(· - z₀)) γ.toFun γ.a γ.b z₀`
- **What**: CPV of `(z-z₀)⁻¹` along γ exists when the curve crosses z₀ uniquely at t₀.
- **How**: Apply `cpv_exists_inv_sub`, supplying `no_endpoint_crossing_of_unique_interior` and rewriting via `honly t … hγt` to use `hC2`/`h_cont_deriv` at t₀.
- **Hypotheses**: measurability, `ContDiffAt ℝ 2`, continuous-derivative neighborhood, uniqueness.
- **Uses-from-project**: `cpv_exists_inv_sub`, `CauchyPrincipalValueExists'`, `no_endpoint_crossing_of_unique_interior`.
- **Used by**: `exp_pv_eq_exp_neg_crossing_angle`, `externalWindingContribution_isInt`.
- **Visibility**: private.
- **Lines**: 42–56.

### private lemma `cpv_inv_sub_eq_limit`
- **Type**: `(γ … L hL) : cauchyPrincipalValue' (·⁻¹) (γ.toFun · - z₀) γ.a γ.b 0 = L`
- **What**: Identifies the canonical-form CPV with its cutoff-integral limit.
- **How**: Congr the cutoff family via `hL.congr` using `sub_zero`, `deriv_sub_const`; unfold `cauchyPrincipalValue'`; finish with `hL'.limUnder_eq`.
- **Hypotheses**: `Tendsto` of cutoff integrals to L.
- **Uses-from-project**: `cauchyPrincipalValue'`, `PiecewiseC1Immersion`.
- **Used by**: `exp_pv_eq_exp_neg_crossing_angle`, `externalWindingContribution_isInt`.
- **Visibility**: private.
- **Lines**: 59–72.

### theorem `exp_pv_eq_exp_neg_crossing_angle`
- **Type**: `… : Complex.exp (cauchyPrincipalValue' (·⁻¹) (γ.toFun · - z₀) γ.a γ.b 0) = Complex.exp (-(I * angleAtCrossing γ t₀ ht₀))`
- **What**: FTC + direction-limit identity: exp of CPV equals exp(-iα) where α is the crossing angle.
- **How**: Obtain L from `cpv_exists_of_unique_crossing`; combine `tendsto_exp_cutoff_integral_crossing` with continuity of `Complex.exp`; finish by `tendsto_nhds_unique` (T₂ uniqueness).
- **Hypotheses**: closed curve, unique interior crossing, measurability, `ContDiffAt ℝ 2`, continuous-derivative neighborhood.
- **Uses-from-project**: `PiecewiseC1Immersion`, `cauchyPrincipalValue'`, `angleAtCrossing`, `tendsto_exp_cutoff_integral_crossing`.
- **Used by**: `externalWindingContribution_isInt`.
- **Visibility**: public.
- **Lines**: 83–98.
- **Notes**: Proof >10 lines; named lemmas `tendsto_exp_cutoff_integral_crossing`, `tendsto_nhds_unique`.

### private lemma `externalWindingContribution_eq_int_of_cpv_eq`
- **Type**: `… : externalWindingContribution γ z₀ t₀ ht₀ = n`
- **What**: If `CPV = L` and `L = -iα + n·2πi`, then `externalWindingContribution = n`.
- **How**: Unfold `externalWindingContribution`, `generalizedWindingNumber'`; rewrite `hPV_eq, hn`; reduce via `field_simp` (using `(Real.pi : ℂ) ≠ 0`) and `ring`.
- **Hypotheses**: π ≠ 0 (derived), CPV equation, integer offset.
- **Uses-from-project**: `externalWindingContribution`, `generalizedWindingNumber'`, `angleAtCrossing`.
- **Used by**: `externalWindingContribution_isInt`.
- **Visibility**: private.
- **Lines**: 102–111.

### theorem `externalWindingContribution_isInt`
- **Type**: `… : ∃ N : ℤ, externalWindingContribution γ z₀ t₀ ht₀ = N`
- **What**: External winding is an integer (key structural fact from H-W Prop 2.2).
- **How**: Extract L via `cpv_exists_of_unique_crossing`; identify CPV via `cpv_inv_sub_eq_limit`; obtain `n` from `Complex.exp_eq_exp_iff_exists_int` applied to `exp_pv_eq_exp_neg_crossing_angle`; finish with `externalWindingContribution_eq_int_of_cpv_eq`.
- **Hypotheses**: regularity bundle (closed, interior crossing, measurable, `ContDiffAt 2`, continuous-derivative neighborhood).
- **Uses-from-project**: `cpv_exists_of_unique_crossing`, `cpv_inv_sub_eq_limit`, `exp_pv_eq_exp_neg_crossing_angle`, `externalWindingContribution_eq_int_of_cpv_eq`.
- **Used by**: downstream H-W decomposition users.
- **Visibility**: public.
- **Lines**: 122–138.

### theorem `generalizedWindingNumber_eq_external_sub_angle`
- **Type**: `… : generalizedWindingNumber' γ.toFun γ.a γ.b z₀ = externalWindingContribution γ z₀ t₀ ht₀ - (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * Real.pi)`
- **What**: H-W Prop 2.2: gWN = N − α/(2π).
- **How**: `simp only [externalWindingContribution, add_sub_cancel_right]`.
- **Hypotheses**: interior `t₀`.
- **Uses-from-project**: `generalizedWindingNumber'`, `externalWindingContribution`, `angleAtCrossing`.
- **Used by**: `generalizedWindingNumber_eq_neg_angleContribution_single`, `externalWindingContribution_zero_of_windingNumber_eq`.
- **Visibility**: public.
- **Lines**: 143–148.

### theorem `generalizedWindingNumber_eq_neg_angleContribution_single`
- **Type**: `… (h_external : externalWindingContribution γ z₀ t₀ ht₀ = 0) : generalizedWindingNumber' γ.toFun γ.a γ.b z₀ = -((angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * Real.pi))`
- **What**: Single-crossing version of Prop 2.3 with vanishing external winding.
- **How**: Specialize `generalizedWindingNumber_eq_external_sub_angle`; rewrite `h_external, zero_sub`.
- **Hypotheses**: vanishing external winding; closed/unique/cross hypotheses present but unused.
- **Uses-from-project**: `generalizedWindingNumber_eq_external_sub_angle`.
- **Used by**: `generalizedWindingNumber_eq_neg_half_smooth_crossing`, `generalizedWindingNumber_eq_neg_corner_contribution`.
- **Visibility**: public.
- **Lines**: 153–162.

### theorem `generalizedWindingNumber_eq_neg_half_smooth_crossing`
- **Type**: `… (hsmooth : t₀ ∉ γ.toPiecewiseC1Curve.partition) (h_external : … = 0) : generalizedWindingNumber' γ.toFun γ.a γ.b z₀ = -(1/2)`
- **What**: Smooth crossing with zero external winding gives `-1/2`.
- **How**: Rewrite via `generalizedWindingNumber_eq_neg_angleContribution_single` and `angleAtCrossing_smooth`; close with `field_simp`.
- **Hypotheses**: smooth (not at partition), zero external winding.
- **Uses-from-project**: `angleAtCrossing_smooth`, `generalizedWindingNumber_eq_neg_angleContribution_single`.
- **Used by**: downstream applications.
- **Visibility**: public.
- **Lines**: 165–176.

### theorem `generalizedWindingNumber_eq_neg_corner_contribution`
- **Type**: `… (hangle : angleAtCrossing γ t₀ ht₀ = α) (h_external : … = 0) : generalizedWindingNumber' γ.toFun γ.a γ.b z₀ = -(α / (2 * Real.pi))`
- **What**: Corner crossing with prescribed angle and zero external winding.
- **How**: Rewrite via `generalizedWindingNumber_eq_neg_angleContribution_single`, then `hangle`.
- **Hypotheses**: angle equation, zero external winding.
- **Uses-from-project**: `generalizedWindingNumber_eq_neg_angleContribution_single`.
- **Used by**: corner applications.
- **Visibility**: public.
- **Lines**: 180–188.

### theorem `externalWindingContribution_zero_of_windingNumber_eq`
- **Type**: `… (h_eq : generalizedWindingNumber' … = -((angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * Real.pi))) : externalWindingContribution γ z₀ t₀ ht₀ = 0`
- **What**: External winding vanishes when gWN matches the angle-only formula.
- **How**: `simp only [externalWindingContribution, h_eq, neg_add_cancel]`.
- **Hypotheses**: gWN equation.
- **Uses-from-project**: `externalWindingContribution`, `generalizedWindingNumber'`, `angleAtCrossing`.
- **Used by**: homotopy/sector-model arguments.
- **Visibility**: public.
- **Lines**: 194–199.

### theorem `externalWindingContribution_translate`
- **Type**: `… : externalWindingContribution (γ.translate c) (z₀ + c) t₀ ht₀ = externalWindingContribution γ z₀ t₀ ht₀`
- **What**: External winding is translation-invariant.
- **How**: Unfold `externalWindingContribution`; use `angleAtCrossing_translate`; `congr 1`; reduce gWN equality to CPV equality via `change` + `unfold generalizedWindingNumber'`; rewrite integrand via `(γ.translate c).toFun t - (z₀ + c) = γ.toFun t - z₀` (proved with `ext`/`ring`).
- **Hypotheses**: interior `t₀`.
- **Uses-from-project**: `PiecewiseC1Immersion.translate`, `angleAtCrossing_translate`, `generalizedWindingNumber'`, `cauchyPrincipalValue'`.
- **Used by**: future translation arguments.
- **Visibility**: public.
- **Lines**: 202–219.
- **Notes**: Proof >10 lines; key lemmas `angleAtCrossing_translate`, definitional `change`.

### theorem `windingNumberWithAngles_union`
- **Type**: `… (hST : Disjoint S T) … : windingNumberWithAngles' γ z₀ (S ∪ T) … = windingNumberWithAngles' γ z₀ S … + windingNumberWithAngles' γ z₀ T …`
- **What**: Additivity of winding-with-angles over disjoint crossing finsets.
- **How**: Unfold `windingNumberWithAngles'`; `symm`; `convert Finset.sum_union`; supply explicit branching function for union; close with two `Finset.sum_bij` applications and `aesop`/`simp +decide`.
- **Hypotheses**: disjoint finsets, both contained in Ioo and on-curve.
- **Uses-from-project**: `windingNumberWithAngles'`, `angleAtCrossing`.
- **Used by**: aggregate multi-crossing winding identities.
- **Visibility**: public.
- **Lines**: 222–252.
- **Notes**: Proof >10 lines; key lemmas `Finset.sum_union`, `Finset.sum_bij`.

## File Summary
- **Total entries**: 12 (3 private helpers + 9 public theorems).
- **Key API**: `exp_pv_eq_exp_neg_crossing_angle`, `externalWindingContribution_isInt`, `generalizedWindingNumber_eq_external_sub_angle`, `generalizedWindingNumber_eq_neg_half_smooth_crossing`, `generalizedWindingNumber_eq_neg_corner_contribution`, `externalWindingContribution_zero_of_windingNumber_eq`, `externalWindingContribution_translate`, `windingNumberWithAngles_union`.
- **Unused**: None obviously dead; all private helpers feed public theorems in-file.
- **Sorries**: 0.
- **set_options**: None.
- **Long proofs (>10 lines)**: `exp_pv_eq_exp_neg_crossing_angle`, `externalWindingContribution_isInt`, `externalWindingContribution_translate`, `windingNumberWithAngles_union`.
- **Purpose**: Implements Hungerbühler–Wasem Proposition 2.2 decomposition. The generalized winding number splits into an integer external contribution `N` (the classical winding of a modified curve) and a crossing-angle term `−α/(2π)`. Provides specializations for smooth crossings (`−1/2`), corner crossings (`−α/(2π)`), translation invariance, and additivity over disjoint crossing parameter sets, equipping downstream files with the structural identities needed for the valence formula.
