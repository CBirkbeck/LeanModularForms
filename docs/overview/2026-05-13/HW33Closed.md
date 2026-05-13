# HW33Closed.lean — Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HW33Closed.lean`
Lines: 133

## theorem/`LeanModularForms.hCancel_of_higherOrder_decomposition_under_B`
- **Type**: For `S : Finset ℂ`, `f : ℂ → ℂ`, `γ : PiecewiseC1Path x x`, complex-valued `h_polar`, `h_holo` such that `f z - principalPartSum S (residue f) z = h_polar z + h_holo z`, and assuming each piece has CPV zero plus interval-integrable cpv-integrands, concludes `HasCauchyPVOn S (f - principalPartSum S (residue f)) γ 0`.
- **What**: Discharges the `hCancel` oracle of `generalizedResidueTheorem` from a higher-order Laurent decomposition `polar + holomorphic` of `f - principalPartSum`.
- **How**: Apply `hCancel_of_decomposition` (from `GeneralizedResidueTheorem.lean`) after swapping the order with `add_comm` on `h_decomp`.
- **Hypotheses**: pointwise decomposition `h_decomp`; `HasCauchyPVOn S h_polar γ 0` and `HasCauchyPVOn S h_holo γ 0`; ε-uniform interval integrability of each cpv-integrand.
- **Uses-from-project**: `principalPartSum`, `residue`, `HasCauchyPVOn`, `cpvIntegrandOn`, `hCancel_of_decomposition` (`GeneralizedResidueTheorem.lean`).
- **Used by**: `generalizedResidueTheorem_higherOrder_under_B_closed` (this file).
- **Visibility**: public (in namespace `LeanModularForms`)
- **Lines**: 52–68

## theorem/`LeanModularForms.generalizedResidueTheorem_higherOrder_under_B_closed`
- **Type**: For an open `U`, finite `S ⊆ U`, `f` differentiable on `U \ S`, a paper-faithful `γ : PwC1Immersion x x` null-homologous in `U`, meromorphy at each `s ∈ S`, conditions (A') and (B), a higher-order Laurent decomposition (`h_polar + h_holo`) with both pieces having CPV zero (+ε-uniform integrability), and singular-side data `hPV_sing` + `hI_sing`, concludes the closed CPV residue formula `HasCauchyPVOn S f γ (2πi · Σ_s gWN(γ, s) · residue f s)`.
- **What**: **End-of-line user-facing form of HW Theorem 3.3 under condition (B).** Combines the higher-order discharge with `hPV_sing` and integrability oracles to produce the closed residue formula.
- **How**: Build the cpv-integrand integrability for the remainder by `(hI_polar + hI_holo).congr`, case-splitting `if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then ...`. Then apply `generalizedResidueTheorem` with `hCancel` discharged by `hCancel_of_higherOrder_decomposition_under_B`.
- **Hypotheses**: `IsOpen U`; `S ⊆ U`; `DifferentiableOn ℂ f (U \ S)`; `IsNullHomologous γ U`; `MeromorphicAt f s` for `s ∈ S`; `SatisfiesConditionA'` and `SatisfiesConditionB`; decomposition `h_decomp`; `HasCauchyPVOn S h_polar γ 0` and `HasCauchyPVOn S h_holo γ 0`; ε-uniform integrability of cpv-integrands for `h_polar`, `h_holo`; `hPV_sing` for the principal-part sum; `hI_sing` integrability.
- **Uses-from-project**: `generalizedResidueTheorem`, `principalPartSum`, `residue`, `HasCauchyPVOn`, `cpvIntegrandOn`, `PwC1Immersion`, `IsNullHomologous`, `MeromorphicAt`, `SatisfiesConditionA'`, `SatisfiesConditionB`, `generalizedWindingNumber`, `poleOrderAt`, `hCancel_of_higherOrder_decomposition_under_B`.
- **Used by**: `HW33Paper.lean` and TIGHT-targets downstream.
- **Visibility**: public (in namespace `LeanModularForms`)
- **Lines**: 84–129

## File Summary
Thin "closure" layer that converts a user-supplied higher-order Laurent decomposition `f − principalPartSum = h_polar + h_holo` into the `hCancel` oracle for `generalizedResidueTheorem`, then assembles the closed form of HW Theorem 3.3 under condition (B). Two declarations only; both wrap existing decomposition/`hCancel` machinery and `generalizedResidueTheorem` from `GeneralizedResidueTheorem.lean`. No real proofs beyond bookkeeping — heavy lifting is in `HW33SectorEven.lean` (B-closure) and the abstract residue theorem itself.
