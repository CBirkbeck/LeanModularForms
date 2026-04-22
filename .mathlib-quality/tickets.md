# Ticket Board: Chain 1 Extended (HW 3.3 Full Closure)

## Summary
- Total: 16 tickets (incl. sub-tickets A-1b, B-1 partial, B-6 partial)
- Done: A-1, A-2, A-2-wrapper, B-1 (partial, outside closure), B-6 (partial, Lipschitz auto-w₀)
- Open: A-1b, B-1 (full), B-2..B-5, CLEANUP-B, B-6 (full), C-1..C-4, CLEANUP-C, CLEANUP-FINAL
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

- **Status**: open
- **File**: `ForMathlib/CurveMeasureZero.lean` or `ForMathlib/PiecewiseC1Path.lean`
- **Depends on**: none
- **Description**: For `γ : PwC1Immersion x y`, `LipschitzWith K γ.toPath.extend`
  for some `K`. Uses bounded one-sided derivative limits at partition points +
  continuity of derivative on each smooth piece.

### [A-2] w₀ existence in open U off the curve

- **Status**: done (via `exists_mem_not_mem_image_of_isOpen_of_lipschitz`)
- **File**: `ForMathlib/CurveMeasureZero.lean`
- **Depends on**: A-1
- **Parallel**: no (same file)
- **Description**: Given open nonempty `U ⊆ ℂ` and Lipschitz `f`, produces
  `w₀ ∈ U` not in `f '' s`. Uses A-1 + `IsOpen.measure_pos`.
- **API**: `exists_mem_not_mem_image_of_isOpen_of_lipschitz`.

### [B-1] h_winding_zero_near from null-hom + compact curve

- **Status**: open
- **File**: `ForMathlib/DixonTheorem.lean`
- **Depends on**: none
- **Parallel**: yes
- **Description**: Prove that for `γ` null-homologous in `U`, for any `w ∉ U`
  off the curve, there exists `ε > 0` such that for all `w' ∈ ball w ε`,
  `generalizedWindingNumber γ w' = 0`. Requires: winding is integer and
  continuous on ℂ \ γ.image, hence locally constant on connected components.
- **Mathlib check**: winding integer off closed curve + continuity — these
  are NOT currently in pure FM and would need to be proved.
- **API**: `generalizedWindingNumber_eventually_zero_of_nullHomologous`.

### [B-2] h1 differentiability from regularity

- **Status**: open
- **File**: `ForMathlib/DixonDiff.lean`
- **Depends on**: none
- **Parallel**: yes
- **Description**: Wrap `dixonH1_differentiableOn` with hypotheses derivable
  from "γ PwC1Immersion + γ image ⊆ U + f differentiable on U + deriv γ
  bounded".
- **API**: `dixonH1_differentiableOn_of_regular`.

### [B-3] h2 differentiability from regularity

- **Status**: open
- **File**: `ForMathlib/DixonDiff.lean`
- **Depends on**: none
- **Parallel**: yes
- **Description**: Wrap `dixonH2_differentiableAt` similarly.
- **API**: `dixonH2_differentiableAt_of_regular`.

### [B-4] dixonFunction eventually equals dixonH2 (auto)

- **Status**: open
- **File**: `ForMathlib/DixonTheorem.lean`
- **Depends on**: B-1
- **Parallel**: no
- **Description**: Package `dixonFunction_eventually_eq_dixonH2` with
  hypotheses derived from null-hom + regularity.
- **API**: `dixonFunction_eventually_eq_dixonH2_of_nullHomologous`.

### [B-5] Dixon-zero aggregator

- **Status**: open
- **File**: `ForMathlib/DixonTheorem.lean`
- **Depends on**: B-1, B-2, B-3, B-4
- **Parallel**: no
- **Description**: Main aggregator
  `dixonFunction_eq_zero_of_nullHomologous`.

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
