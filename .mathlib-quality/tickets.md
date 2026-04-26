# Ticket Board: Chain 1 Extended (HW 3.3 Full Closure)

## Summary
- Total: 16 tickets (incl. sub-tickets A-1b, B-1 partial, B-6 partial)
- Done: A-1, A-1b, A-2, A-2-wrapper, B-1 (partial + cocompact-bounded + continuity), **B-2 full convex**, B-3, B-4, **B-5 (6 variants incl. convex full)**, B-6 (partial, Lipschitz auto-w₀), **D-1 (a/b/c/d all done)**
- Open: B-1 (full boundary case = integer-valued winding), CLEANUP-B, B-6 (full), C-1..C-4, CLEANUP-C, CLEANUP-FINAL
- Parallel capacity: 3 workers at peak (A, B-stream, C-stream all independent after A)

## Tickets

### [A-1] Piecewise C¹ image has Lebesgue measure zero

- **Status**: done (via `volume_image_lipschitz_real_zero` in `ForMathlib/CurveMeasureZero.lean`)
- **File**: `ForMathlib/CurveMeasureZero.lean`
- **Depends on**: none
- **Parallel**: yes
- **Description**: For Lipschitz `f : ℝ → ℂ` and any `s ⊆ ℝ`, the Lebesgue volume of
  `f '' s` in `ℂ` is zero. Uses `LipschitzWith.hausdorffMeasure_image_le` +
  `Real.hausdorffMeasure_of_finrank_lt` (Hausdorff-2 vanishes on ℝ) +
  `Measure.absolutelyContinuous_isAddHaarMeasure` (volume ≪ Hausdorff-2 on ℂ).
- **API**: `hausdorffMeasure_two_real_zero`, `hausdorffMeasure_two_lipschitz_image_zero`,
  `volume_image_lipschitz_real_zero`.
- **Follow-up**: wire to `PwC1Immersion` via Lipschitz-of-piecewise-C¹ (ticket A-1b below).

### [A-1b] Piecewise C¹ implies Lipschitz

- **Status**: done (via `lipschitzOnWith_of_nnnorm_deriv_le` in `ForMathlib/CurveMeasureZero.lean`)
- **File**: `ForMathlib/CurveMeasureZero.lean`
- **Depends on**: none
- **Description**: Foundational `LipschitzOnWith` helper from bounded derivative
  on a convex set, specialized from `Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le`.
  Full `PwC1Immersion` Lipschitz follows by gluing via partition (deferred — callers
  currently supply `LipschitzWith` directly via `exists_mem_not_mem_path_image_of_isOpen`).

### [A-2] w₀ existence in open U off the curve

- **Status**: done (via `exists_mem_not_mem_image_of_isOpen_of_lipschitz`)
- **File**: `ForMathlib/CurveMeasureZero.lean`
- **Depends on**: A-1
- **Parallel**: no (same file)
- **Description**: Given open nonempty `U ⊆ ℂ` and Lipschitz `f`, produces
  `w₀ ∈ U` not in `f '' s`. Uses A-1 + `IsOpen.measure_pos`.
- **API**: `exists_mem_not_mem_image_of_isOpen_of_lipschitz`.

### [B-1] h_winding_zero_near from null-hom + compact curve

- **Status**: partial done (outside-closure case + cocompact-bounded case +
  continuity); full boundary case open
- **File**: `ForMathlib/NullHomologous.lean`, `ForMathlib/GeneralizedWindingNumber.lean`
- **Depends on**: none
- **Parallel**: yes
- **Description**: Prove that for `γ` null-homologous in `U`, for any `w ∉ U`
  off the curve, there exists `ε > 0` such that for all `w' ∈ ball w ε`,
  `generalizedWindingNumber γ w' = 0`. Requires: winding is integer and
  continuous on ℂ \ γ.image, hence locally constant on connected components.
- **Done partial**:
  - `IsNullHomologous.winding_zero_nhds_of_not_mem_closure` — handles
    the case `w ∉ closure U` (the easy case; ball stays outside U).
  - `IsNullHomologous.winding_eventually_zero_cocompact_of_bounded` — for
    bounded U, winding eventually zero in `cocompact ℂ`.
  - `generalizedWindingNumber_continuousAt_of_avoids` — winding is
    continuous at any point off a Lipschitz PwC1 curve. Uses dominated
    convergence via `intervalIntegral.continuousAt_of_dominated_interval`.
- **Open**: boundary case `w ∈ closure U \ U` — needs **integer-valued winding**
  (local constancy requires this + continuity).
- **API**: `generalizedWindingNumber_eventually_zero_of_nullHomologous`.

### [B-2] h1 differentiability from regularity — DONE for convex U

- **Status**: done via `dixonH1_differentiableOn_of_regular_convex_full` for
  convex U (all oracles auto-discharged); general open U still has 2 oracles
- **File**: `ForMathlib/DixonDiff.lean`
- **Depends on**: D-1
- **Variants**:
  - `dixonH1_differentiableOn_of_regular`: takes `h_F'_meas` + `h_dslope_deriv_bound`
    as oracles
  - `dixonH1_differentiableOn_of_regular_convex`: drops `h_dslope_deriv_bound` via D-1c
  - `dixonH1_differentiableOn_of_regular_convex_full`: drops `h_F'_meas` via D-1d.
    **Fully closed for convex open U.**

### [D-1] dslope theory API — CLOSED

- **Status**: D-1 core + D-1a/b/c/d all done; B-2 full + B-5 full closed for convex U
- **File**: `ForMathlib/DslopeIntegral.lean`
- **Depends on**: none
- **Parallel**: yes
- **All Done**:
  - `Complex.dslope_eq_integral_deriv` — FTC representation
  - D-1a: `continuousOn_dslope_first_arg` — continuity in first arg
  - D-1b: `continuousOn_dslope_prod` — joint continuity on `U × U`
  - D-1c: `deriv_dslope_bounded_locally`/`_on_compact` — Cauchy estimates
  - **D-1d: `aestronglyMeasurable_deriv_dslope`** — AE measurability of
    `c ↦ deriv (dslope f c) w₀` via pointwise limit of continuous difference
    quotients (using D-1a + `HasDerivAt.tendsto_slope` +
    `aestronglyMeasurable_of_tendsto_ae`)
  - **B-2 convex wired**: `dixonH1_differentiableOn_of_regular_convex_full`
    auto-discharges all 6 oracles
  - **B-5 convex wired**: `dixonFunction_eq_zero_of_nullHomologous_convex_full`
    — only `h_winding_zero_near` (B-1 full) remains

### [B-3] h2 differentiability from regularity

- **Status**: done (via `dixonH2_differentiableAt_of_regular` in `ForMathlib/DixonDiff.lean`)
- **File**: `ForMathlib/DixonDiff.lean`
- **Depends on**: none
- **Parallel**: yes
- **Description**: Wraps `dixonH2_differentiableAt` deriving its 6 oracle
  hypotheses (integrability, boundedness, measurability) from:
  * `ContinuousOn f (γ.image)`
  * `LipschitzWith K γ.toPath.extend`
  via `stronglyMeasurable_deriv`, `norm_deriv_le_of_lipschitz`, and
  product-continuity.
- **API**: `dixonH2_differentiableAt_of_regular`.

### [B-4] dixonFunction eventually equals dixonH2 (auto)

- **Status**: done (via `dixonFunction_eventually_eq_dixonH2_of_nullHomologous` in `ForMathlib/DixonTheorem.lean`)
- **File**: `ForMathlib/DixonTheorem.lean`
- **Depends on**: B-1 cocompact (done)
- **Description**: For null-hom γ in bounded open U, the `h_winding_evt`
  hypothesis is discharged automatically via
  `IsNullHomologous.winding_eventually_zero_cocompact_of_bounded`.
- **API**: `dixonFunction_eventually_eq_dixonH2_of_nullHomologous`.

### [B-5] Dixon-zero aggregator

- **Status**: done with progressive variants
- **File**: `ForMathlib/DixonTheorem.lean`
- **Depends on**: takes B-1, B-2, B-3, B-4 as oracle hypotheses at most
- **Variants**:
  - `dixonFunction_eq_zero_of_nullHomologous` — base aggregator, all oracles explicit
  - `..._bounded` — drops `h_winding_evt` via B-4 auto-discharge (requires U bounded)
  - `..._autoH2` — also drops `h2_diff` via B-3 auto-discharge (Lipschitz γ)
  - `..._autoBounds` — also drops bounds (R, M_f, M_d) and integrability
    auto-discharged from continuity + Lipschitz. Only `h1_diff` (B-2) and
    `h_winding_zero_near` (B-1 full) remain as oracles.

### [CLEANUP-B] Run /cleanup on Dixon files

- **Status**: open
- **File**: `ForMathlib/DixonTheorem.lean`, `ForMathlib/DixonDiff.lean`
- **Depends on**: B-5

### [B-6] Close null-hom simple-pole theorem

- **Status**: open
- **File**: `ForMathlib/HigherOrderAssembly.lean`
- **Depends on**: A-2 ✅, B-5, CLEANUP-B
- **Description**: Upgrade `hasCauchyPVOn_simplePoles_nullHomologous_closed`
  to discharge the w₀ and Dixon-zero oracles using A-2 (done) and B-5.

### [C-1] Tangent-approximation around a crossing

- **Status**: open
- **File**: `ForMathlib/HigherOrderCancel.lean`
- **Depends on**: none
- **Parallel**: yes
- **API**: `tangentApproximation_of_isFlatOfOrder`.

### [C-2] Curve CPV reduces to line CPV under A'

- **Status**: open
- **File**: `ForMathlib/HigherOrderCancel.lean`
- **Depends on**: C-1
- **API**: `cpv_near_crossing_eq_cpv_tangent_of_flat`.

### [C-3] A'+B give higher-order cancellation

- **Status**: open
- **File**: `ForMathlib/HigherOrderCancel.lean`
- **Depends on**: C-2
- **API**: `higherOrder_cancel_of_A'_and_B`.

### [CLEANUP-C] Run /cleanup on HigherOrderCancel.lean

- **Status**: open
- **File**: `ForMathlib/HigherOrderCancel.lean`
- **Depends on**: C-1, C-2, C-3

### [C-4] Close higher-order HW 3.3 via A'/B

- **Status**: open
- **File**: `ForMathlib/HigherOrderAssembly.lean`
- **Depends on**: B-6, C-3, CLEANUP-C
- **Description**: Final fully-closed HW 3.3:
  `generalizedResidueTheorem_closed`.

### [CLEANUP-FINAL] Run /cleanup on all modified files

- **Status**: open
- **Depends on**: C-4
