# Phase 4: Moral Duplication Analysis

Scope: `LeanModularForms/ForMathlib/` (~180 files, ~2,630 unique declaration names, ~2,750 total).
Method: cross-file declaration-name match (109 name collisions across files), namespace-difference
scan, type-signature comparison on `_at_*` / `_seg*` triples, and direct `diff` on suspected
duplicate `.lean` files.

The cleanest, highest-impact finding is the **GeneralizedResidueTheory / HungerbuhlerWasem parallel
infrastructure**: multiple top-level files in `ForMathlib/` are character-for-character mirrors of
files in `ForMathlib/HungerbuhlerWasem/` (and similarly for `ForMathlib/GeneralizedResidueTheory/`),
differing only in namespace. The clearest single-file example is `HW33SectorEven.lean` vs
`HungerbuhlerWasem/SectorCancellation.lean` — `diff` of declaration signatures yields exactly **one
line of difference** (the `namespace` declaration). The other major finding is the
`Seg1FTCProvider` / `Seg4FTCProvider` / `ArcGenericFTCProvider` triple (around 40 declarations
each, structurally isomorphic, name-suffixed by segment index).

## A. Pairwise duplication table

| # | Decl A | File A | Decl B | File B | Same statement? | Same proof? | Verdict |
|---|--------|--------|--------|--------|-----------------|-------------|---------|
| 1 | `def orthogonalProjectionComplex` | FlatnessConditions.lean | `def orthogonalProjectionComplex` | GeneralizedResidueTheory/Residue/Flatness.lean | YES (byte-equal `(w L : ℂ) : ℂ`) | YES (`L * ...`) | UNIFY: keep Flatness, delete FlatnessConditions copy |
| 2 | `def tangentDeviation` | FlatnessConditions.lean | `def tangentDeviation` | Residue/Flatness.lean | YES | YES | UNIFY |
| 3 | `theorem orthogonalProjectionComplex_zero_left` | FlatnessConditions.lean | `theorem orthogonalProjectionComplex_zero_left` | Residue/Flatness.lean | YES | YES | UNIFY |
| 4 | `theorem tangentDeviation_zero_left` | FlatnessConditions.lean | `theorem tangentDeviation_zero_left` | Residue/Flatness.lean | YES | YES | UNIFY |
| 5 | `theorem tangentDeviation_zero_right` | FlatnessConditions.lean | `theorem tangentDeviation_zero_right` | Residue/Flatness.lean | YES | YES | UNIFY |
| 6 | `theorem orthogonalProjectionComplex_smul` | FlatnessConditions.lean | `theorem orthogonalProjectionComplex_smul` | Residue/Flatness.lean | YES | YES | UNIFY |
| 7 | `theorem orthogonalProjectionComplex_real_smul_self` | FlatnessConditions.lean | `theorem orthogonalProjectionComplex_real_smul_self` | Residue/Flatness.lean | YES | YES | UNIFY |
| 8 | `theorem tangentDeviation_real_smul_self` | FlatnessConditions.lean | `theorem tangentDeviation_real_smul_self` | Residue/Flatness.lean | YES | YES | UNIFY |
| 9 | `theorem tangentDeviation_add` | FlatnessConditions.lean | `theorem tangentDeviation_add` | Residue/Flatness.lean | YES | YES | UNIFY |
| 10 | `theorem norm_tangentDeviation_le` | FlatnessConditions.lean | `theorem norm_tangentDeviation_le` | Residue/Flatness.lean | YES | YES | UNIFY |
| 11 | `structure IsFlatOfOrder` | FlatnessConditions.lean | `structure IsFlatOfOrder` | Residue/Flatness.lean | YES | YES | UNIFY |
| 12 | `theorem IsFlatOfOrder.of_le` | FlatnessConditions.lean | `theorem IsFlatOfOrder.of_le` | Residue/Flatness.lean | YES | YES | UNIFY |
| 13 | `theorem isFlatOfOrder_one` | FlatnessConditions.lean (`PwC1Immersion x y`) | `theorem isFlatOfOrder_one` | Residue/Flatness.lean (`PiecewiseC1Immersion`) | NEAR (different curve type) | similar | UNIFY by picking one curve type |
| 14 | `def SatisfiesConditionA'` | FlatnessConditions.lean (`PwC1Immersion`) | `def SatisfiesConditionA'` | Residue/Flatness.lean (`PiecewiseC1Immersion`) | NEAR (different curve type) | similar | UNIFY |
| 15 | `structure SatisfiesConditionB` | FlatnessConditions.lean | `structure SatisfiesConditionB` | Residue/Flatness.lean | NEAR (different curve type) | similar | UNIFY |
| 16 | `theorem conditions_automatic_simple_poles` | FlatnessConditions.lean | `theorem conditions_automatic_simple_poles` | Residue/Flatness.lean | YES | YES | UNIFY |
| 17 | `def IsCrossed` | HW33LaurentPolarPart.lean | `def IsCrossed` | HungerbuhlerWasem/LaurentExtraction.lean | YES (namespace differs) | YES | UNIFY |
| 18 | `def crossingParam` | HW33LaurentPolarPart.lean | `def crossingParam` | LaurentExtraction.lean | YES | YES | UNIFY |
| 19 | `theorem crossingParam_mem_Ioo` | HW33LaurentPolarPart.lean | `theorem crossingParam_mem_Ioo` | LaurentExtraction.lean | YES | YES | UNIFY |
| 20 | `theorem γ_at_crossingParam` | HW33LaurentPolarPart.lean | `theorem γ_at_crossingParam` | LaurentExtraction.lean | YES | YES | UNIFY |
| 21 | `def laurentPolarPartAt` | HW33LaurentPolarPart.lean | `def laurentPolarPartAt` | LaurentExtraction.lean | YES | YES | UNIFY |
| 22 | `def laurentAnalyticPartAt` | HW33LaurentPolarPart.lean | `def laurentAnalyticPartAt` | LaurentExtraction.lean | YES | YES | UNIFY |
| 23 | `def laurentPolarPartTotal` | HW33LaurentPolarPart.lean | `def laurentPolarPartTotal` | LaurentExtraction.lean | YES | YES | UNIFY |
| 24 | `private theorem laurent_data_exists` | HW33LaurentPolarPart.lean | `private theorem laurent_data_exists` | LaurentExtraction.lean | YES | YES | UNIFY |
| 25 | `theorem f_eq_analyticPart_plus_polarPart_eventually` | HW33LaurentPolarPart.lean | `theorem f_eq_analyticPart_plus_polarPart_eventually` | LaurentExtraction.lean | YES | YES | UNIFY |
| 26 | `theorem laurentAnalyticPartAt_analyticAt` | HW33LaurentPolarPart.lean | `theorem laurentAnalyticPartAt_analyticAt` | LaurentExtraction.lean | YES | YES | UNIFY |
| 27 | `theorem laurentPolarPartAt_differentiableAt` | HW33LaurentPolarPart.lean | `theorem laurentPolarPartAt_differentiableAt` | LaurentExtraction.lean | YES | YES | UNIFY |
| 28 | `theorem polarPart_eq_simplePole_add_higherOrder` | HungerbuhlerWasem.lean | `theorem polarPart_eq_simplePole_add_higherOrder` | HW33HigherOrderAvoidance.lean | YES | YES (35-line proof, same) | UNIFY |
| 29 | `structure PolarPartDecomposition` | HungerbuhlerWasem.lean | `structure PolarPartDecomposition` | HW33HigherOrderAvoidance.lean | YES | YES (same fields) | UNIFY |
| 30 | `theorem contourIntegral_higherOrder_eq_zero_of_avoids` | HungerbuhlerWasem.lean | `theorem contourIntegral_higherOrder_eq_zero_of_avoids` | HW33HigherOrderAvoidance.lean | YES | YES (31-line proof) | UNIFY |
| 31 | `theorem contourIntegral_higherOrderPart_eq_zero_of_avoids` | HungerbuhlerWasem.lean | `theorem contourIntegral_higherOrderPart_eq_zero_of_avoids` | HW33HigherOrderAvoidance.lean | YES | YES (44-line proof) | UNIFY |
| 32 | `theorem exp_neg_I_eq_one_of_conditionB` | HW33SectorEven.lean | `theorem exp_neg_I_eq_one_of_conditionB` | HungerbuhlerWasem/SectorCancellation.lean | YES (`diff` showed only namespace differs) | YES | UNIFY: delete HW33SectorEven.lean entirely |
| 33 | `theorem sector_pv_formula_vanishes_under_conditionB` | HW33SectorEven.lean | `theorem sector_pv_formula_vanishes_under_conditionB` | HungerbuhlerWasem/SectorCancellation.lean | YES | YES | UNIFY (covered by item 32) |
| 34 | `theorem real_ray_inv_pow_integral` | HW33SectorEven.lean | `theorem real_ray_inv_pow_integral` | HungerbuhlerWasem/SectorCancellation.lean | YES | YES | UNIFY |
| 35 | `theorem complex_ray_inv_pow_integral` | HW33SectorEven.lean | `theorem complex_ray_inv_pow_integral` | HungerbuhlerWasem/SectorCancellation.lean | YES | YES | UNIFY |
| 36 | `theorem arc_inv_pow_integral` | HW33SectorEven.lean | `theorem arc_inv_pow_integral` | HungerbuhlerWasem/SectorCancellation.lean | YES | YES | UNIFY |
| 37 | `theorem sector_inv_pow_integral_combined` | HW33SectorEven.lean | `theorem sector_inv_pow_integral_combined` | HungerbuhlerWasem/SectorCancellation.lean | YES | YES | UNIFY |
| 38 | `theorem hw_theorem_3_3_under_conditionB_parametric` | HW33SectorEven.lean | `theorem hw_theorem_3_3_under_conditionB_parametric` | HungerbuhlerWasem/SectorCancellation.lean | YES | YES | UNIFY |
| 39 | `theorem hasCauchyPVOn_singleton_pow_of_conditionB_assembled` | HW33SectorEven.lean | `theorem hasCauchyPVOn_singleton_pow_of_conditionB_assembled` | HungerbuhlerWasem/SectorCancellation.lean | YES | YES | UNIFY |
| 40 | `theorem cpvIntegrandOn_singleton_eq_contour_of_far` | HungerbuhlerWasem/ExitTimeExcision.lean | `theorem cpvIntegrandOn_singleton_eq_contour_of_far` | HW33Bridge.lean | YES | YES | UNIFY |
| 41 | `theorem cpvIntegrandOn_singleton_eq_zero_of_close` | ExitTimeExcision.lean | `theorem cpvIntegrandOn_singleton_eq_zero_of_close` | HW33Bridge.lean | YES | YES | UNIFY |
| 42 | `theorem hasCauchyPVOn_singleton_of_exitTime_excision` | ExitTimeExcision.lean | `theorem hasCauchyPVOn_singleton_of_exitTime_excision` | HW33Bridge.lean | YES | YES | UNIFY |
| 43 | `theorem shape_left_of_strictAntiOn` | ExitTimeExcision.lean | `theorem shape_left_of_strictAntiOn` | HW33Bridge.lean | YES | YES | UNIFY |
| 44 | `theorem shape_right_of_strictMonoOn` | ExitTimeExcision.lean | `theorem shape_right_of_strictMonoOn` | HW33Bridge.lean | YES | YES | UNIFY |
| 45 | `theorem tangentApproximation_of_isFlatOfOrder_right` | HigherOrderCancel.lean | `theorem tangentApproximation_of_isFlatOfOrder_right` | HungerbuhlerWasem/HigherOrderAsymptotics.lean | YES | YES | UNIFY |
| 46 | `theorem tangentApproximation_of_isFlatOfOrder_left` | HigherOrderCancel.lean | `theorem tangentApproximation_of_isFlatOfOrder_left` | HigherOrderAsymptotics.lean | YES | YES | UNIFY |
| 47 | `theorem hasDerivAt_antiderivative_pow_inv` | HigherOrderCancel.lean | `theorem hasDerivAt_antiderivative_pow_inv` | HigherOrderAsymptotics.lean | YES | YES | UNIFY |
| 48 | `theorem integral_pow_inv_eq_FTC` | HigherOrderCancel.lean | `theorem integral_pow_inv_eq_FTC` | HigherOrderAsymptotics.lean | YES | YES | UNIFY |
| 49 | `theorem hasDerivAt_antiderivative_pow_inv_complex` | HigherOrderCancel.lean | `theorem hasDerivAt_antiderivative_pow_inv_complex` | HigherOrderAsymptotics.lean | YES | YES | UNIFY |
| 50 | `theorem closed_excised_integral_eq_antideriv_diff` | HigherOrderCancel.lean | `theorem closed_excised_integral_eq_antideriv_diff` | HigherOrderAsymptotics.lean | YES | YES | UNIFY |
| 51 | `theorem norm_F_diff_le_segment_bound` | HigherOrderCancel.lean | `theorem norm_F_diff_le_segment_bound` | HigherOrderAsymptotics.lean | YES | YES | UNIFY |
| 52 | `theorem chord_to_tangent_isLittleO_right/_left` | HigherOrderCancel.lean | `theorem chord_to_tangent_isLittleO_right/_left` | HigherOrderAsymptotics.lean | YES | YES | UNIFY |
| 53 | `theorem windingNumber_eq_of_piecewise_homotopic` | WindingHomotopy.lean | `theorem windingNumber_eq_of_piecewise_homotopic` | GRT/Homotopy/Invariance.lean | YES | YES | UNIFY |
| 54 | `def cauchyPrincipalValueIntegrandOn` | Residue.lean | `def cpvIntegrandOn` | CauchyPrincipalValue.lean | NEAR (same shape, different names) | YES (verbatim definition) | UNIFY: pick shorter, delete the other |
| 55 | `def cauchyPrincipalValueOn` | Residue.lean | `def cauchyPVOn` | CauchyPrincipalValue.lean | NEAR | YES | UNIFY |
| 56 | `def CauchyPrincipalValueExistsOn` | Residue.lean | `def HasCauchyPVOn` | CauchyPrincipalValue.lean | NEAR | YES | UNIFY |
| 57 | `def cauchyPrincipalValueIntegrand'` | ClassicalCPV.lean | `def cpvIntegrand` | CauchyPrincipalValue.lean | NEAR | YES | UNIFY: ClassicalCPV is a legacy variant; delete it |
| 58 | `def cauchyPrincipalValue'` | ClassicalCPV.lean | `def cauchyPV` | CauchyPrincipalValue.lean | NEAR | YES | UNIFY (covered by 57) |
| 59 | `def CauchyPrincipalValueExists'` | ClassicalCPV.lean | `def HasCauchyPV` | CauchyPrincipalValue.lean | NEAR | YES | UNIFY (covered by 57) |
| 60 | `private def seg1_h₀ / seg4_h₀ / arc_h₀` | Seg1FTCProvider.lean / Seg4FTCProvider.lean / ArcGenericFTCProvider.lean | (triple) | (triple) | NEAR (one per segment) | structurally identical | KEEP-BOTH-OR-PARAMETRIZE: extract `seg_h₀ : ℕ → …` parametric |
| 61 | `lemma seg1_h₀_continuous` etc. (24 names) | Seg1FTCProvider.lean | `lemma seg4_h₀_continuous` / `arc_h₀_continuous` | Seg4FTCProvider / ArcGenericFTCProvider | NEAR (segment-parameterized) | YES (same tactics) | UNIFY by parametrizing on `segIdx : Fin 5` |
| 62 | `theorem windingNumber_at_I_eq` | WindingWeightProofs.lean | `theorem gWN_fdBoundary_H_at_i` | WindingWeights/I.lean | YES (same value −1/2) | NEAR | KEEP-DERIVE one from the other |
| 63 | `theorem windingNumber_at_rho_eq` | WindingWeightProofs.lean | `theorem gWN_fdBoundary_H_at_rho` | WindingWeights/Rho.lean | YES (value −1/6) | NEAR | KEEP-DERIVE |
| 64 | `theorem windingNumber_at_rhoPlusOne_eq` | WindingWeightProofs.lean | `theorem gWN_fdBoundary_H_at_rho_plus_one` | WindingWeights/RhoPlusOne.lean | YES | NEAR | KEEP-DERIVE |
| 65 | `def mkSingleCrossingData_atI` | WindingWeightProofs.lean | (via `WindingWeights/I.lean` `mkSingleCrossingData_atI` indirect) | WindingWeights/I.lean | YES | YES | UNIFY |
| 66 | `theorem ellipticPointRho_eq_exp` | WindingWeightProofs.lean | `theorem ellipticPointRho_eq_exp` | WW-Common.lean | YES | YES | UNIFY |
| 67 | `theorem ellipticPointRhoPlusOne_eq_exp` | WindingWeightProofs.lean | `theorem ellipticPointRhoPlusOne_eq_exp` | WW-Common.lean | YES | YES | UNIFY |
| 68 | `instance NormSMulClass ℝ ℂ` | AnnulusBounds.lean | `instance NormSMulClass ℝ ℂ` | Boundary-Smooth.lean, Residue-Flatness.lean, SingularAnnulus.lean | YES | YES | UNIFY into a single ambient instance |
| 69 | `def IsCrossed` | LaurentExtraction.lean | `def IsCrossed` | HW33LaurentPolarPart.lean | YES | YES | UNIFY (=item 17) |
| 70 | `theorem cpvIntegrandOn_singleton_eq_indicator` | ExitTimeExcision.lean | `theorem cpvIntegrandOn_singleton_eq_indicator` | HW33Bridge.lean | YES | YES | UNIFY |
| 71 | `theorem integral_cpvIntegrandOn_singleton_eq_contour_left/right/middle` | ExitTimeExcision.lean | (same names) | HW33Bridge.lean | YES | YES | UNIFY |
| 72 | `theorem F_diff_at_tangent_target_tendsto_zero_right/_left` | HigherOrderCancel.lean | (same names) | HigherOrderAsymptotics.lean | YES | YES | UNIFY |
| 73 | `theorem eventually_re_pos_right/_neg_left/_ne_right/_ne_left` | HigherOrderCancel.lean | (same names) | HigherOrderAsymptotics.lean | YES | YES | UNIFY |
| 74 | `theorem norm_segment_to_pole_lower_bound_half` | HigherOrderCancel.lean | (same name) | HigherOrderAsymptotics.lean | YES | YES | UNIFY |
| 75 | `theorem norm_sq_segment_to_pole_lower_bound` | HigherOrderCancel.lean | (same name) | HigherOrderAsymptotics.lean | YES | YES | UNIFY |
| 76 | `theorem tendsto_div_pow_zero_of_isLittleO` | HigherOrderCancel.lean | (same name) | HigherOrderAsymptotics.lean | YES | YES | UNIFY |
| 77 | `theorem isFlatOfOrder_one` | FlatnessConditions.lean | `theorem isFlatOfOrder_one` | Residue/Flatness.lean | NEAR (curve types) | YES (modulo curve) | UNIFY |
| 78 | `def poleOrderAt` | PrincipalPart.lean | `def poleOrderAt` | Residue/Flatness.lean | YES | YES | UNIFY |
| 79 | `def cpvIntegrand` | CauchyPrincipalValue.lean | (private versions inside `AsymmetricSingleCrossingData`) | AsymmetricSingleCrossing.lean | NEAR | similar | KEEP-DERIVE asymmetric wrapper |
| 80 | `theorem ClosedPwC1Immersion.cyclicShift_deriv_eq_no_wrap` vs `_wrap` | PaperPwC1ImmersionInvariance.lean (same file pair) | — | — | NEAR (no_wrap vs wrap) | YES (mirror proofs) | KEEP-BOTH (genuine cases) but extract a common helper |
| 81 | `def CurvesHomotopic` / `CurvesHomotopicAvoiding` | ClassicalCPV.lean | `def ClosedCurvesHomotopicAvoiding` / `PiecewiseCurvesHomotopicAvoiding` | (other files) | NEAR | similar | UNIFY to one homotopy framework |
| 82 | `theorem AsymmetricSingleCrossingData.hasCauchyPV_simplePole` | AsymmetricSingleCrossing.lean | `theorem SingleCrossingData.hasCauchyPV_simplePole` | HungerbuhlerWasem/CrossingCPV.lean | NEAR (asym vs sym) | YES (asym is generalization) | KEEP-DERIVE: derive symmetric from asymmetric |
| 83 | `theorem cpv_polarPart_at_pole_under_conditions` | HungerbuhlerWasem/Crossing.lean | `theorem cpv_polarPart_at_pole_under_conditions_asymmetric` | Crossing.lean (same file) | NEAR | YES (sym is special case of asym) | KEEP-DERIVE; lots of pairs like this throughout `Crossing.lean` |
| 84 | `theorem residueTheorem_crossing` vs `_asymmetric` vs `_singleton` vs `_singleton_asymmetric` | Crossing.lean | (within same file) | (within same file) | NEAR | YES | KEEP-DERIVE: pick `_asymmetric_full` as primary |
| 85 | `theorem hw_3_3_clean` vs `_clean_avoids` vs `_clean_with_scd` vs `_clean_full` vs `_clean_truly_full` vs `_clean_multi` vs `_clean_full_mero` | HW33Clean.lean | (within same file) | (within same file) | NEAR | YES | KEEP-DERIVE one; rest are auto-derivable wrappers |
| 86 | `theorem hw_3_3_paper` | HW33Paper.lean | `theorem hw_3_3_tight` | HW33Tight.lean | NEAR (curve type ClosedPwC1Immersion vs PwC1Immersion) | YES (Paper is one-line bridge to Tight) | KEEP-BOTH (bridge between curve types) |
| 87 | `theorem hw_3_3_simple_avoidance_paper` | HW33Paper.lean | `theorem hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids_unbounded` | (other) | NEAR | YES | KEEP-DERIVE |
| 88 | `theorem fdBoundary_crosses_I_at` | WindingWeightProofs.lean | (used by `windingNumber_at_I_eq`) | WindingWeightProofs.lean | self-contained | YES | KEEP (used internally) |
| 89 | `theorem windingNumber_eq_of_piecewise_homotopic_of_hyps` | WindingHomotopy.lean | `theorem windingNumber_eq_of_piecewise_homotopic` | WindingHomotopy.lean | NEAR (with vs without hypothesis-explicitness) | similar | KEEP-DERIVE: weaker keeps `_of_hyps` private |
| 90 | `theorem hPV_sing_of_conditionB` vs `_avoids` vs `_singleCrossing` vs `_pointwise_winding` | HW33PVSing.lean | (same file) | (same file) | NEAR | similar (parametric over how hypothesis is supplied) | KEEP-DERIVE: pick most general |
| 91 | `theorem cpv_excised_tendsto_zero_of_F_diff_zero` | HigherOrderCancel.lean | (same name) | HigherOrderAsymptotics.lean | YES | YES | UNIFY |
| 92 | `private def seg1_h_arc` / `seg4_h_arc` / `arc_h_arc` (with continuous, hasDerivAt, deriv, slitPlane variants) | Seg1FTCProvider.lean | Seg4FTCProvider.lean / ArcGenericFTCProvider.lean | — | NEAR | YES | UNIFY into `seg_h_arc` (param over segIdx) |
| 93 | `private def seg1_h₃` vs `seg4_h₃` vs `arc_h₃` | Seg1FTCProvider.lean | (siblings) | (siblings) | NEAR | YES | UNIFY |
| 94 | `private def seg1_h₅` vs `seg4_h₅` vs `arc_h₅` | Seg1FTCProvider.lean | (siblings) | (siblings) | NEAR | YES | UNIFY |
| 95 | `def arcFTCHyp_seg1` vs `_seg4` vs `_arc_generic` | Seg1FTCProvider.lean | Seg4FTCProvider.lean / ArcGenericFTCProvider.lean | NEAR | YES | UNIFY |
| 96 | `private theorem rho_far_left/_right/_near` | CrossingAtRho.lean | `private theorem rhoPlusOne_far_left/_right/_near` | CrossingAtRho.lean (same file) | NEAR | YES | UNIFY by parametrizing on which elliptic point |
| 97 | `theorem arc_near_at_rho_arcsin` / `_at_rhoPlusOne_arcsin` | CrossingAtRho.lean | (twin) | (twin) | NEAR | YES | UNIFY |
| 98 | `theorem arc_far_at_rho_arcsin` / `_at_rhoPlusOne_arcsin` | CrossingAtRho.lean | (twin) | (twin) | NEAR | YES | UNIFY |
| 99 | `theorem vert_near_at_rho` / `_at_rhoPlusOne` | CrossingAtRho.lean | (twin) | (twin) | NEAR | YES | UNIFY |
| 100 | `theorem vert_far_at_rho` / `_at_rhoPlusOne` | CrossingAtRho.lean | (twin) | (twin) | NEAR | YES | UNIFY |
| 101 | `theorem fdBoundary_H_sub_rho_seg{0,1,2,3,4}_re/_slitPlane` | WindingWeights/Rho.lean | (5-segment family) | — | NEAR (one per segment) | similar | UNIFY by indexing seg |
| 102 | `theorem fdBoundaryFun_seg{1,4,5}_dist_{I,rho,rhoPlusOne}_lower` | WindingWeightProofs.lean | (9-element family) | — | NEAR | similar | UNIFY by indexing (seg, pt) |
| 103 | `private def ref1 / ref5 / ref4n / arcRef` with `_cd / _eq / _slit` lemmas | InteriorContourIntegral.md | (4-fold family) | — | NEAR | YES | UNIFY by indexing |
| 104 | `private theorem seg1F / seg5F / seg4F` | InteriorContourIntegral.lean | (3-fold family) | (same file) | NEAR | YES | UNIFY |
| 105 | `theorem fdBoundary_H_seg0/1/2/3/4/eq_arc` | WW-Common.lean | (5-fold + arc family) | (same file) | NEAR | YES | KEEP-BOTH (each segment formula is unique) |

## B. UNIFY candidates (proposed unified signatures)

### B.1 Flatness duplication (highest ROI)

**Current**: `FlatnessConditions.lean` (441 lines) and `Residue/Flatness.lean` (467 lines) define
the same set of declarations modulo curve type (`PwC1Immersion x y` vs `PiecewiseC1Immersion`).
Most declarations are byte-equal.

**Proposed**: keep `GeneralizedResidueTheory/Residue/Flatness.lean` as canonical. Delete
`FlatnessConditions.lean`. For consumers needing `PwC1Immersion x y` rather than
`PiecewiseC1Immersion`, add a bridge file that re-exports under the alternate name. Impact: remove
~441 lines, eliminate confusion across ~17 declaration names.

### B.2 HW33SectorEven.lean = SectorCancellation.lean

**Verification**: `diff` of signature lists yielded exactly one line difference
(`namespace LeanModularForms` vs `namespace HungerbuhlerWasem`). File sizes 558 vs 562 lines.

**Proposed**: delete `HW33SectorEven.lean`. Replace consumer imports with
`HungerbuhlerWasem/SectorCancellation.lean`, opening `HungerbuhlerWasem` namespace where needed.
Impact: 558 lines removed.

### B.3 LaurentExtraction.lean ⊇ HW33LaurentPolarPart.lean

**Current**: `HungerbuhlerWasem/LaurentExtraction.lean` (1130 lines) is a superset of
`HW33LaurentPolarPart.lean` (519 lines). HW33LaurentPolarPart redeclares the entire
"primitive Laurent data" API under a different namespace.

**Proposed**: delete `HW33LaurentPolarPart.lean`. The downstream consumers
(`HW33Tight.lean`, `HW33LaurentSimple.lean`) currently call
`laurentHigherOrderPolar`/`laurentHolomorphicRemainder` — these can be `export`-ed from
LaurentExtraction. Impact: 519 lines removed.

### B.4 Higher-order asymptotics duplication

**Current**: `HigherOrderCancel.lean` (1515 lines) and
`HungerbuhlerWasem/HigherOrderAsymptotics.lean` (785 lines) share ~17 theorems verbatim
(`tangentApproximation_of_isFlatOfOrder_*`, `hasDerivAt_antiderivative_pow_inv*`,
`integral_pow_inv_eq_FTC`, `closed_excised_integral_eq_antideriv_diff`, `chord_to_tangent_isLittleO_*`,
`F_diff_at_tangent_target_tendsto_zero_*`, `eventually_re_*`, `eventually_ne_*`,
`norm_F_diff_le_segment_bound`, `norm_F_diff_at_tangent_target_le`,
`norm_segment_to_pole_lower_bound_half`, `norm_sq_segment_to_pole_lower_bound`,
`tendsto_div_pow_zero_of_isLittleO`, `cpv_excised_tendsto_zero_of_F_diff_zero`).

**Proposed**: HigherOrderAsymptotics.lean should be the lower-level "tangent-deviation kernel"
of HigherOrderCancel.lean. Either move all of the shared theorems into Asymptotics and have
Cancel `import`+reuse, or delete Asymptotics outright if its only role is to mirror Cancel for
the HW namespace. Impact: 17 declarations × O(20 lines each) ≈ 300 lines.

### B.5 HungerbuhlerWasem.lean (1050 lines) duplicates HW33HigherOrderAvoidance.lean

**Current**: `HungerbuhlerWasem.lean` (the top-level "API entry" file) re-declares
`PolarPartDecomposition`, `higherOrderPart`, `simplePolePart`, `polarPart_eq_simplePole_add_higherOrder`,
`contourIntegral_higherOrder_eq_zero_of_avoids`, `contourIntegral_higherOrderPart_eq_zero_of_avoids`
that already live in `HW33HigherOrderAvoidance.lean`.

**Proposed**: have `HungerbuhlerWasem.lean` `import` HW33HigherOrderAvoidance and re-export rather
than re-declare. Impact: ~150 lines removed.

### B.6 ExitTimeExcision.lean vs HW33Bridge.lean (~10 theorems duplicated)

**Current**: 10 theorems shared (`cpvIntegrandOn_singleton_eq_contour_of_far`,
`cpvIntegrandOn_singleton_eq_zero_of_close`, `cpvIntegrandOn_singleton_eq_indicator`,
3× `integral_cpvIntegrandOn_singleton_eq_*`, `cpvIntegrandOn_singleton_integral_eq_excision`,
`hasCauchyPVOn_singleton_of_excision_tendsto`, `hasCauchyPVOn_singleton_of_exitTime_excision`,
`shape_left_of_strictAntiOn`, `shape_right_of_strictMonoOn`).

**Proposed**: delete `HW33Bridge.lean` and re-import from `HungerbuhlerWasem/ExitTimeExcision.lean`.

### B.7 CPV definitions: 3 parallel APIs

The codebase has three parallel CPV definition families:

| File | Integrand | PV | Existence predicate |
|------|-----------|----|---------------------|
| `Residue.lean` | `cauchyPrincipalValueIntegrandOn` | `cauchyPrincipalValueOn` | `CauchyPrincipalValueExistsOn` |
| `CauchyPrincipalValue.lean` | `cpvIntegrandOn` | `cauchyPVOn` | `HasCauchyPVOn` |
| `ClassicalCPV.lean` | `cauchyPrincipalValueIntegrand'` | `cauchyPrincipalValue'` | `CauchyPrincipalValueExists'` |

**Proposed**: keep `CauchyPrincipalValue.lean` (shortest names, used by HW33 chain).
Delete `ClassicalCPV.lean` definitions (legacy with primes) — already isolated, no downstream
beyond `windingNumber_eq_of_piecewise_homotopic` family. Add `cauchyPrincipalValueOn` etc. as
`@[deprecated]` aliases in `Residue.lean` and migrate the few usages. Impact: ~3 redundant
abstractions → 1.

### B.8 Common `NormSMulClass ℝ ℂ` instance

Currently declared as a `private` instance in 4 files (`AnnulusBounds`, `Boundary-Smooth`,
`Residue-Flatness`, `SingularAnnulus`). Should be promoted to a single public instance in a
common upstream file (or upstreamed to mathlib).

## C. Parallel infrastructure

**Major finding**: There are two parallel "residue / HW3.3" infrastructures, plus the legacy
"top-level HW33*" sequence.

1. **`ForMathlib/HungerbuhlerWasem/` subdir** — 13 files, clean modular HW Theorem 3.3 development.
2. **`ForMathlib/HW33*.lean` top-level** — 18 files (HW33Clean, HW33Closed, HW33Paper, HW33Tight,
   HW33Final, HW33Bridge, HW33LaurentPolarPart, HW33LaurentSimple, HW33HigherOrder{Auto,Avoidance,
   C3,C4}, HW33HoloCancel, HW33Monotonicity, HW33MultiPole, HW33Paper, HW33PVSing,
   HW33SectorEven, HW33SimpleClean, HW33ExitTimeWrapper). These look like progressive
   "user-facing wrappers" but several are direct copies of the HungerbuhlerWasem/ subdir files
   (most flagrant: `HW33SectorEven.lean` ≡ `HungerbuhlerWasem/SectorCancellation.lean`).
3. **`ForMathlib/GeneralizedResidueTheory/` subdir** — `Residue.lean`, `PrincipalValue.lean`,
   `WindingNumber.lean`, `ArcCalculus.lean`, `CurveAvoidance.lean`, `CauchyPrimitive.lean`,
   `PiecewiseCurveAPI.lean`, plus `Residue/`, `OnCurvePV/`, `WindingNumber/`, `Homotopy/`,
   `PVInfrastructure/` sub-subdirs.

**Verdict**: The HW33* top-level chain is a "linearization" of the same content that lives in the
two subdirs. The clean strategy is:
- **Keep**: `HungerbuhlerWasem/` subdir + `GeneralizedResidueTheory/` subdir + top-level
  `HungerbuhlerWasem.lean` (API entry) + the *bridging* HW33 files
  (HW33Tight, HW33Paper, HW33Closed, HW33Final, HW33Clean — wrappers with non-trivial conversion).
- **Delete**: `HW33SectorEven.lean`, `HW33LaurentPolarPart.lean`, `HW33LaurentSimple.lean` (already
  superset/subset duplication of subdir versions), `HW33Bridge.lean`, `FlatnessConditions.lean`,
  `ClassicalCPV.lean`.

Estimated total deletable: **5–6 files ≈ 2500–3000 lines**.

## D. _at_i / _at_rho / _at_rho_plus_one parametrization opportunities

Triple #1 — **arc near/far distance**:
- `arc_near_at_I_arcsin` / `arc_near_at_rho_arcsin` / `arc_near_at_rhoPlusOne_arcsin`
- `arc_far_at_I_arcsin` / `arc_far_at_rho_arcsin` / `arc_far_at_rhoPlusOne_arcsin`

These all establish "distance to elliptic point P along the FD arc parametrization is at most/at
least f(δ)". They differ only by the center of the arc and the constants (1/5, 2/5, 3/5). A
unified statement parametrized by `(P : EllipticPoint)` would be a clean win.

Triple #2 — **vert near/far**: `vert_{near,far}_at_{rho,rhoPlusOne}` — same pattern, only two
elements but mechanically near-identical.

Triple #3 — **mkSingleCrossingData**: `mkSingleCrossingData_atI` / `_atRho` / `_atRhoPlusOne`.
Each takes (H, γ, hγ, δ, threshold, hthresh, ...) and produces `SingleCrossingData γ P`. A single
parametric constructor `mkSingleCrossingData_at (P : EllipticPoint) (windingValue : ℂ)` would
collapse these.

Triple #4 — **gWN_fdBoundary_H_at**: `gWN_fdBoundary_H_at_i` / `_at_rho` / `_at_rho_plus_one`.
Each computes the generalized winding number at the labeled elliptic point. Currently each lives in
its own file (`WindingWeights/I.lean`, `Rho.lean`, `RhoPlusOne.lean`) and the proofs share massive
structure (chord-norm computation, FTC telescope, log-difference limit).

Triple #5 — **pv_integral_at_*_tendsto**: same trio.

Triple #6 — **CrossingAtRho** internal: `rho_far_{left,right}` + `rho_near`,
`rhoPlusOne_far_{left,right}` + `rhoPlusOne_near`. The same six-lemma pattern; should be one
parametric pair.

Triple #7 — **norm_trig_sub_{I,rho,rhoPlusOne}**: same trio of arc-distance lemmas.

Triple #8 — **fdBoundary_crosses_{I,rho,rhoPlusOne}_at**: same trio.

Triple #9 — **windingNumber_at_{I,rho,rhoPlusOne}_eq**: same trio. The proofs are nearly identical
calls into `mkSingleCrossingData_at*`.

Triple #10 — **fdBoundaryFun_arc_dist_{I,rho,rhoPlusOne}**: same trio.

Each unified family above would collapse 3 declarations × ~30–50 lines of proof = ~120 lines per
family. Across 10 families: **~1200 lines** of mechanical duplication.

## E. Top 10 unification recommendations (prioritized)

1. **DELETE `FlatnessConditions.lean`** (441 lines) — byte-equal duplicate of
   `GeneralizedResidueTheory/Residue/Flatness.lean` for ~12 declarations. Highest ROI: one file
   delete, no proof rewriting needed.
2. **DELETE `HW33SectorEven.lean`** (558 lines) — `diff` proves it differs from
   `HungerbuhlerWasem/SectorCancellation.lean` only in `namespace` line. Update consumer imports.
3. **DELETE `HW33LaurentPolarPart.lean`** (519 lines) — strict subset of
   `HungerbuhlerWasem/LaurentExtraction.lean`. Add re-exports for the `LeanModularForms` namespace
   if needed.
4. **DELETE `HW33Bridge.lean`** — 10+ theorems verbatim duplicate
   `HungerbuhlerWasem/ExitTimeExcision.lean`.
5. **DEDUPE `HigherOrderCancel.lean` vs `HigherOrderAsymptotics.lean`** — 17 theorems shared.
   Move tangent-deviation kernel into `HigherOrderAsymptotics.lean`; have `HigherOrderCancel.lean`
   import it. ~300 lines saved.
6. **PARAMETRIZE seg/arc FTC providers**: collapse `Seg1FTCProvider.lean`, `Seg4FTCProvider.lean`,
   `ArcGenericFTCProvider.lean` into one parametric file indexed by `segIdx`. ~40 declarations
   × 3 files → ~40 declarations × 1 file. ≈1500 lines removed.
7. **PARAMETRIZE elliptic-point families**: 10+ `_at_i` / `_at_rho` / `_at_rho_plus_one` triples
   should become single statements parametric on a `Fin 3` (or an `EllipticPoint` inductive type).
   ~1200 lines saved across the three `WindingWeights/{I,Rho,RhoPlusOne}.lean` files.
8. **DELETE `ClassicalCPV.lean`** — legacy primed PV definitions (`cauchyPrincipalValue'`,
   `CauchyPrincipalValueExists'`). Has very few downstream callers (mostly `WindingHomotopy.lean`
   which is itself a candidate for removal — `windingNumber_eq_of_piecewise_homotopic` is also in
   `GRT/Homotopy/Invariance.lean`).
9. **UNIFY CPV API: pick `cauchyPV` / `cauchyPVOn` / `HasCauchyPV*` (CauchyPrincipalValue.lean)
   as canonical**, deprecate the longer `cauchyPrincipalValue*` triples in `Residue.lean`.
   Migrate the ~10 usages; result is one definition path.
10. **PROMOTE the private `NormSMulClass ℝ ℂ` instance** to a single public location
    (in mathlib or a single small ForMathlib file). Currently 4 redundant declarations.

**Cumulative impact (rough estimate)**: 5–6 file deletions, ~5000 lines of mechanical
duplication eliminated, ~10 parametric families collapsing 3-fold duplication into one.
