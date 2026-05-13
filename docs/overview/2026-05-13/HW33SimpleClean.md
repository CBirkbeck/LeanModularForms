# Inventory: HW33SimpleClean.lean

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HW33SimpleClean.lean`

Namespace: `LeanModularForms`
Section: `noncomputable section`
Common variable: `{x : ℂ}`

### `theorem hw_3_3_simple_with_crossData`
- **Type**: `{U} (hU_open : IsOpen U) (hU_ne : U.Nonempty) (S : Finset ℂ) (hS_in_U : ↑S ⊆ U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S)) (γ : ClosedPwC1Immersion x) (h_null : IsNullHomologous γ.toPwC1Immersion U) (hSimple : ∀ s ∈ S, HasSimplePoleAt f s) (hCondA : SatisfiesConditionA' …) (hCondB : SatisfiesConditionB …) (h_polar_cancel : HasCauchyPVOn S (laurentHigherOrderPolar hCondB) γ … 0) (hI_polar) (hI_holo) (crossData : ∀ s ∈ S, SingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s) {δ} (hδ_pos) (h_avoid_pairs) (h_int_perpole) : HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path (2 * π * I * ∑ s ∈ S, generalizedWindingNumber γ s * residue f s)`
- **What**: HW Theorem 3.3 for the simple-pole case using paper-faithful piecewise-C¹ immersions, with crossings handled per-pole via `SingleCrossingData` plus a uniform pairwise avoidance margin δ. (Note the comment: `h_avoid_pairs` is unsatisfiable when γ truly crosses a pole — see `hw_3_3_simple_with_perPoleCPV` for the corrected formulation.)
- **How**: 5-step composition >10 lines: (1) derive `hMero` via `HasSimplePoleAt.meromorphicAt`; (2) discharge `h_holo_cancel` via `h_holo_cancel_of_conditionB`; (3) discharge `hPV_sing` via `hPV_sing_of_conditionB_singleCrossing` feeding `crossData`/avoidance/`h_int_perpole`; (4) derive sum-form `hI_sing` from `cpvIntegrandOn_finset_sum_intervalIntegrable` using `rfl` rewrite of `principalPartSum`; (5) close via `hw_3_3_paper`.
- **Hypotheses**: U open and nonempty; S finite in U; f differentiable off S; γ closed piecewise-C¹ immersion; γ null-homologous; every pole simple; conditions (A') and (B); polar/holo CPV cancellations and integrabilities; per-pole single-crossing data; uniform pairwise avoidance margin; per-pole CPV integrand integrability.
- **Uses from project**: `ClosedPwC1Immersion`, `IsNullHomologous`, `HasSimplePoleAt`, `HasSimplePoleAt.meromorphicAt`, `SatisfiesConditionA'`, `SatisfiesConditionB`, `HasCauchyPVOn`, `laurentHigherOrderPolar`, `laurentHolomorphicRemainder`, `cpvIntegrandOn`, `principalPartSum`, `SingleCrossingData`, `poleOrderAt`, `residue`, `generalizedWindingNumber`, `h_holo_cancel_of_conditionB`, `hPV_sing_of_conditionB_singleCrossing`, `cpvIntegrandOn_finset_sum_intervalIntegrable`, `hw_3_3_paper`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 91–164.
- **Notes**: >30 lines; large dependency on Phase 4 / Phase 5c dischargers. No sorry/TODO/axiom. Header comment notes hypothesis incompatibility — included for historical/comparison value.

### `theorem cpvIntegrandOn_div_sub_intervalIntegrable_of_mem`
- **Type**: `(γ : ClosedPwC1Immersion x) (S : Finset ℂ) {s : ℂ} (hs : s ∈ S) (c : ℂ) {ε : ℝ} (hε_pos : 0 < ε) : IntervalIntegrable (fun t => cpvIntegrandOn S (fun z => c / (z - s)) γ.…toPath.extend ε t) volume 0 1`
- **What**: The cutoff CPV integrand for the simple pole `c / (z - s)` (with `s ∈ S`) is interval-integrable on `[0,1]` for every cutoff radius ε > 0, with no avoidance hypothesis on γ.
- **How**: >10 lines, key lemmas: pointwise norm bound `‖cpvIntegrandOn …‖ ≤ ‖c‖/ε · ‖γ'(t)‖` via `split_ifs` on the cutoff (zero inside, `div_le_div_of_nonneg_left` outside since `‖γ(t)-s‖ > ε`); use `ClosedPwC1Curve.deriv_extend_intervalIntegrable` and `IntervalIntegrable.norm`, multiply by constant; combine measurability of the CPV integrand (`aestronglyMeasurable_cpvIntegrandOn` plus `stronglyMeasurable_deriv`) and close by `IntervalIntegrable.mono_fun`.
- **Hypotheses**: γ is a closed piecewise-C¹ immersion; s ∈ S; ε > 0.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Curve.deriv_extend_intervalIntegrable`, `cpvIntegrandOn`, `aestronglyMeasurable_cpvIntegrandOn`, `stronglyMeasurable_deriv`.
- **Used by**: `hw_3_3_simple_with_perPoleCPV` (via `h_per_pole_int`), `hw_3_3_simple_one_crossing_paper` indirectly through `hw_3_3_simple_with_perPoleCPV`.
- **Visibility**: public.
- **Lines**: 206–256.
- **Notes**: >30 lines; no sorry/TODO/axiom.

### `theorem hw_3_3_simple_with_perPoleCPV`
- **Type**: `{U} (hU_open) (hU_ne) (S) (hS_in_U) (f) (hf) (γ : ClosedPwC1Immersion x) (h_null) (hSimple) (hCondA) (hCondB) (h_polar_cancel) (hI_polar) (hI_holo) (h_per_pole_cpv : ∀ s ∈ S, HasCauchyPVOn S (fun z => residue f s / (z - s)) γ … (2 * π * I * generalizedWindingNumber γ s * residue f s)) : HasCauchyPVOn S f γ … (2 * π * I * ∑ s ∈ S, generalizedWindingNumber γ s * residue f s)`
- **What**: Corrected paper-faithful formulation of HW Theorem 3.3 in the simple-pole case: replaces the inconsistent `crossData/avoidance/h_int_perpole` block of `hw_3_3_simple_with_crossData` by per-pole multi-pole CPV witnesses directly, auto-discharging per-pole integrability.
- **How**: >10 lines: derive `hMero`; discharge `h_holo_cancel` via `h_holo_cancel_of_conditionB`; auto-discharge per-pole integrability via `cpvIntegrandOn_div_sub_intervalIntegrable_of_mem`; assemble `hPV_sing` via `HasCauchyPVOn.finset_sum`; derive sum-form `hI_sing` via `cpvIntegrandOn_finset_sum_intervalIntegrable`; close via `hw_3_3_paper`.
- **Hypotheses**: same scaffolding as the cross-data theorem but replacing crossing/avoidance with per-pole CPV witnesses.
- **Uses from project**: `ClosedPwC1Immersion`, `IsNullHomologous`, `HasSimplePoleAt`, `HasSimplePoleAt.meromorphicAt`, `SatisfiesConditionA'`, `SatisfiesConditionB`, `HasCauchyPVOn`, `HasCauchyPVOn.finset_sum`, `laurentHigherOrderPolar`, `laurentHolomorphicRemainder`, `cpvIntegrandOn`, `principalPartSum`, `cpvIntegrandOn_div_sub_intervalIntegrable_of_mem`, `cpvIntegrandOn_finset_sum_intervalIntegrable`, `h_holo_cancel_of_conditionB`, `generalizedWindingNumber`, `residue`, `poleOrderAt`, `hw_3_3_paper`.
- **Used by**: `hw_3_3_simple_with_perPoleCPV_avoids` (composes via per-pole CPV); `hw_3_3_simple_one_crossing_paper` (composes via per-pole CPV).
- **Visibility**: public.
- **Lines**: 274–343.
- **Notes**: >30 lines; no sorry/TODO/axiom.

### `theorem hw_3_3_simple_with_perPoleCPV_avoids`
- **Type**: `{U} (hU_open) (hU_ne) (S) (hS_in_U) (f) (hf) (γ : ClosedPwC1Immersion x) (h_null) (hSimple) (hCondA) (hCondB) (h_polar_cancel) (hI_polar) (hI_holo) (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc 0 1, γ t ≠ s) : HasCauchyPVOn S f γ … (2 * π * I * ∑ s ∈ S, generalizedWindingNumber γ s * residue f s)`
- **What**: Avoidance specialization of `hw_3_3_simple_with_perPoleCPV`: when γ avoids every pole, the per-pole CPV witnesses are auto-built and the conclusion follows.
- **How**: >10 lines: extract uniform avoidance margin δ via `avoids_finset_delta_bound`; per pole `s ∈ S` get `HasGeneralizedWindingNumber γ s …` via `hasGeneralizedWindingNumber_of_avoids` then upgrade to multi-pole CPV via `hasCauchyPVOn_div_sub_of_singleton_and_avoid_others`; close by feeding to `hw_3_3_simple_with_perPoleCPV`.
- **Hypotheses**: same scaffolding plus a uniform pointwise avoidance hypothesis `γ(t) ≠ s` for every pole and parameter.
- **Uses from project**: `ClosedPwC1Immersion`, `IsNullHomologous`, `HasSimplePoleAt`, `SatisfiesConditionA'`, `SatisfiesConditionB`, `HasCauchyPVOn`, `laurentHigherOrderPolar`, `laurentHolomorphicRemainder`, `cpvIntegrandOn`, `avoids_finset_delta_bound`, `HasGeneralizedWindingNumber`, `hasGeneralizedWindingNumber_of_avoids`, `hasCauchyPVOn_div_sub_of_singleton_and_avoid_others`, `generalizedWindingNumber`, `residue`, `poleOrderAt`, `hw_3_3_simple_with_perPoleCPV`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 358–404.
- **Notes**: >30 lines; no sorry/TODO/axiom.

### `theorem hw_3_3_simple_one_crossing_paper`
- **Type**: `{U} (hU_open) (hU_ne) (S) (hS_in_U) (f) (hf) (γ : ClosedPwC1Immersion x) (h_null) (hSimple) (hCondA) (hCondB) (h_polar_cancel) (hI_polar) (hI_holo) (s_star) (hs_star_in : s_star ∈ S) (hγ_avoids_others : ∀ s ∈ S, s ≠ s_star → ∀ t ∈ Icc 0 1, γ t ≠ s) (hw_star : HasGeneralizedWindingNumber γ s_star (generalizedWindingNumber γ s_star)) : HasCauchyPVOn S f γ … (2 * π * I * ∑ s ∈ S, generalizedWindingNumber γ s * residue f s)`
- **What**: HW Theorem 3.3 simple-pole case under the geometrically meaningful "at most one pole crossed" hypothesis: γ may cross the distinguished pole `s_star ∈ S` and must avoid all other poles. Per-pole integrability is auto-discharged.
- **How**: >10 lines, key lemmas: extract avoidance margin δ on `S.erase s_star` via `avoids_finset_delta_bound`; build `Lipschitz` constant via `ClosedPwC1Immersion.lipschitzWith_extend`; use `γ.preimage_countable S` (TIGHT-6) for the finite preimage; for each pole split into `s = s_star` (use `hw_star` + `hasCauchyPVOn_div_sub_of_singleton_and_avoid_others`) and `s ≠ s_star` (γ avoids s, build winding via `hasGeneralizedWindingNumber_of_avoids` and CPV via the continuous-on-image lemma `hasCauchyPVOn_continuousOn_of_countable_preimage`, then identify with the contour integral via `integral_simple_pole_eq_winding`); close via `hw_3_3_simple_with_perPoleCPV`.
- **Hypotheses**: usual condition (A')/(B)/null-homology/Phase-3 scaffolding, simple poles, distinguished pole `s_star ∈ S`, γ avoids every other pole pointwise on [0,1], existence of the generalized winding number at `s_star`.
- **Uses from project**: `ClosedPwC1Immersion`, `IsNullHomologous`, `HasSimplePoleAt`, `SatisfiesConditionA'`, `SatisfiesConditionB`, `HasCauchyPVOn`, `laurentHigherOrderPolar`, `laurentHolomorphicRemainder`, `cpvIntegrandOn`, `avoids_finset_delta_bound`, `HasGeneralizedWindingNumber`, `hasGeneralizedWindingNumber_of_avoids`, `hasCauchyPVOn_div_sub_of_singleton_and_avoid_others`, `hasCauchyPVOn_continuousOn_of_countable_preimage`, `integral_simple_pole_eq_winding`, `ClosedPwC1Immersion.lipschitzWith_extend`, `ClosedPwC1Immersion.preimage_countable`, `PiecewiseC1Path.extendedPath_eq`, `PiecewiseC1Path.contourIntegral`, `generalizedWindingNumber`, `residue`, `poleOrderAt`, `hw_3_3_simple_with_perPoleCPV`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 442–597.
- **Notes**: >30 lines; very long doc/explanatory comment block in the proof body; no sorry/TODO/axiom.

## File Summary

- 4 public theorems, 0 private/scoped, 0 sorry / 0 axiom / 0 TODO, 0 `set_option`.
- All four theorems are paper-faithful versions of HW Theorem 3.3 in the simple-pole case; they compose `hw_3_3_paper` (in `HW33Paper.lean`) with various oracles dischargers from Phase 4 (`h_holo_cancel_of_conditionB`), Phase 5c (`hPV_sing_of_conditionB_singleCrossing`), the cpv-integrand integrability lemma `cpvIntegrandOn_div_sub_intervalIntegrable_of_mem`, and avoidance / single-crossing CPV machinery (`HasCauchyPVOn.finset_sum`, `hasCauchyPVOn_div_sub_of_singleton_and_avoid_others`, `hasCauchyPVOn_continuousOn_of_countable_preimage`).
- All four theorems have signatures >30 lines and proofs ≥10 lines. The file imports `HW33Paper`, `HW33HoloCancel`, `HW33PVSing`, `HW33HigherOrderC3`, `MeromorphicBridge`.
- Total declarations: 4. (N1 = 4.)
