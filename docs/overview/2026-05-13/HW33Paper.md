# HW33Paper.lean — Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HW33Paper.lean`
Lines: 126

## theorem/`LeanModularForms.hw_3_3_paper`
- **Type**: For an open `U`, `S : Finset ℂ ⊆ U`, `f : ℂ → ℂ` differentiable on `U \ S`, a paper-faithful `γ : ClosedPwC1Immersion x` null-homologous in `U` (via the legacy `γ.toPwC1Immersion`), `MeromorphicAt f s` at each `s ∈ S`, conditions (A') and (B), and the four cancellation+integrability oracles for `laurentHigherOrderPolar`/`laurentHolomorphicRemainder` plus singular-side `hPV_sing` + `hI_sing`, concludes the CPV residue formula `HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path (2πi · Σ gWN · residue f s)`.
- **What**: **HW Theorem 3.3 — paper-faithful curve form.** Same conclusion as the legacy `hw_3_3_tight`, but the curve type matches the paper exactly: partition includes endpoints `0`, `1`; `C¹` on closed sub-intervals; non-vanishing within-derivative on closed pieces.
- **How**: One-line bridge: invoke `hw_3_3_tight` after converting `γ : ClosedPwC1Immersion` to a `PwC1Immersion` via the canonical bridge `ClosedPwC1Immersion.toPwC1Immersion`; pass through every cancellation/integrability hypothesis unchanged.
- **Hypotheses**: `IsOpen U`; `S ⊆ U`; `DifferentiableOn ℂ f (U \ S)`; `IsNullHomologous γ.toPwC1Immersion U`; `∀ s ∈ S, MeromorphicAt f s`; `SatisfiesConditionA'` for `(γ.toPwC1Immersion, f, S, poleOrderAt)`; `SatisfiesConditionB`; CPV-zero for `laurentHigherOrderPolar` and `laurentHolomorphicRemainder`; ε-uniform interval integrability for each; `hPV_sing` and `hI_sing` for the principal-part sum.
- **Uses-from-project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.toPwC1Immersion`, `hw_3_3_tight`, `HasCauchyPVOn`, `cpvIntegrandOn`, `principalPartSum`, `residue`, `generalizedWindingNumber`, `IsNullHomologous`, `MeromorphicAt`, `SatisfiesConditionA'`, `SatisfiesConditionB`, `poleOrderAt`, `laurentHigherOrderPolar`, `laurentHolomorphicRemainder`.
- **Used by**: `hw_3_3_simple_avoidance_paper` (this file) — only as a peer entry point, not directly.
- **Visibility**: public (in namespace `LeanModularForms`)
- **Lines**: 48–84

## theorem/`LeanModularForms.hw_3_3_simple_avoidance_paper`
- **Type**: For an open nonempty `U`, finite `S ⊆ U`, `f` differentiable on `U \ S`, paper-faithful `γ : ClosedPwC1Immersion x` null-homologous in `U`, `f` has simple poles at every `s ∈ S`, and `γ` *avoids* every `s ∈ S` (`γ t ≠ s` for all `t ∈ [0,1]`), concludes `HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path (Σ 2πi · gWN · residue f s)`.
- **What**: **HW Theorem 3.3 — simple-pole avoidance, paper-faithful curve, fully closed.** All cancellation/integrability/Lipschitz/boundedness hypotheses are auto-discharged.
- **How**: Obtain a Lipschitz constant `K` for `γ`'s extend via `ClosedPwC1Immersion.lipschitzWith_extend`; pass to `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids_unbounded` (which lifts `hU_bounded` via TIGHT-12 `winding_eventually_zero_cocompact_of_lipschitz`).
- **Hypotheses**: `IsOpen U`; `U.Nonempty`; `S ⊆ U`; `DifferentiableOn ℂ f (U \ S)`; `IsNullHomologous γ.toPwC1Immersion U`; `HasSimplePoleAt f s` for `s ∈ S`; γ avoids every `s` on `[0,1]`.
- **Uses-from-project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.lipschitzWith_extend`, `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids_unbounded`, `HasSimplePoleAt`, `HasCauchyPVOn`, `IsNullHomologous`, `generalizedWindingNumber`, `residue`.
- **Used by**: User-facing endpoint — no callers in this file or downstream listed.
- **Visibility**: public (in namespace `LeanModularForms`)
- **Lines**: 106–122

## File Summary
Two paper-faithful entry points for HW Theorem 3.3 using `ClosedPwC1Immersion` instead of the legacy `PwC1Immersion`: the *general* form `hw_3_3_paper` (still requires the four cancellation/integrability oracles and the singular-side PV data, identical to the tight version) and the *simple-pole avoidance* form `hw_3_3_simple_avoidance_paper` (no auxiliary oracles — Lipschitz auto-derived from closed-piece `C¹` structure via `ClosedPwC1Immersion.lipschitzWith_extend`, with `hU_bounded` lifted by the TIGHT-12 cocompact result). Both are thin bridges; the substantive work lives in `hw_3_3_tight` (HW33Tight.lean) and `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids_unbounded`.
