# Ticket Board: Chain 1 Extended (HW 3.3 Full Closure)

## Summary
- Total: 12 tickets
- Open: 12 | In Progress: 0 | Done: 0
- Parallel capacity: 3 workers at peak (A, B-stream, C-stream all independent after A)

## Tickets

### [A-1] Piecewise C¹ image has Lebesgue measure zero

- **Status**: open
- **File**: `ForMathlib/CurveMeasureZero.lean` (new)
- **Depends on**: none
- **Parallel**: yes
- **Description**: Prove `MeasureTheory.volume (γ.toPath.extend '' Icc (0 : ℝ) 1) = 0`
  for `γ : PwC1Immersion x y` (using that γ is Lipschitz on each piece,
  image of Lipschitz has finite 1-D Hausdorff measure, hence zero 2-D
  Lebesgue measure).
- **Mathlib check**: `LipschitzOnWith.ae_lipschitzOnWith` exists;
  `MeasureTheory.volume_image_le_mul_lintegral_deriv` for Lipschitz; need
  to apply to each smooth piece.
- **API**: `piecewiseC1Immersion_image_volume_zero`
- **Naming**: `piecewiseC1Immersion_image_volume_zero` (snake_case).
- **Generality**: state for `PiecewiseC1Path` if possible (just needs C¹
  except finite points); fallback to `PwC1Immersion`.

### [A-2] w₀ existence in open U off the curve

- **Status**: open
- **File**: `ForMathlib/CurveMeasureZero.lean`
- **Depends on**: A-1
- **Parallel**: no (same file)
- **Description**: Given open nonempty `U ⊆ ℂ` with `γ.image ⊆ U`, prove
  `∃ w ∈ U, ∀ t ∈ Icc 0 1, γ t ≠ w`. Uses A-1: γ.image has measure 0,
  U has positive measure (since open nonempty), so `U \ γ.image ≠ ∅`.
- **API**: `exists_mem_not_mem_curve_of_isOpen`
- **Naming**: `exists_mem_not_mem_curve_of_isOpen`

### [B-1] h_winding_zero_near from null-hom + compact curve

- **Status**: open
- **File**: `ForMathlib/DixonTheorem.lean`
- **Depends on**: none
- **Parallel**: yes
- **Description**: Prove that for `γ` null-homologous in `U`, for any `w ∉ U`
  off the curve, there exists `ε > 0` such that for all `w' ∈ ball w ε`,
  `generalizedWindingNumber γ w' = 0`. Uses continuity of winding number
  off curve + null-hom (winding = 0 outside U) + openness of complement
  of curve image.
- **Mathlib check**: winding continuity is standard.
- **API**: `generalizedWindingNumber_eventually_zero_of_nullHomologous`

### [B-2] h1 differentiability from regularity

- **Status**: open
- **File**: `ForMathlib/DixonDiff.lean`
- **Depends on**: none
- **Parallel**: yes (can run alongside B-1, B-3)
- **Description**: Wrap `dixonH1_differentiableOn` with hypotheses derivable
  from "γ PwC1Immersion + γ image ⊆ U + f differentiable on U + deriv γ
  bounded". Package the parametric Leibniz conditions into a clean interface.
- **API**: `dixonH1_differentiableOn_of_regular`

### [B-3] h2 differentiability from regularity

- **Status**: open
- **File**: `ForMathlib/DixonDiff.lean`
- **Depends on**: none
- **Parallel**: yes
- **Description**: Wrap `dixonH2_differentiableAt` similarly.
- **API**: `dixonH2_differentiableAt_of_regular`

### [B-4] dixonFunction eventually equals dixonH2 (auto)

- **Status**: open
- **File**: `ForMathlib/DixonTheorem.lean`
- **Depends on**: B-1
- **Parallel**: no (depends on B-1)
- **Description**: Package `dixonFunction_eventually_eq_dixonH2` with
  hypotheses derived from null-hom + regularity. Uses B-1 to supply
  the winding-zero-near condition.
- **API**: `dixonFunction_eventually_eq_dixonH2_of_nullHomologous`

### [B-5] Dixon-zero aggregator

- **Status**: open
- **File**: `ForMathlib/DixonTheorem.lean`
- **Depends on**: B-1, B-2, B-3, B-4
- **Parallel**: no
- **Description**: The main aggregator:
  ```lean
  theorem dixonFunction_eq_zero_of_nullHomologous
      (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
      (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
      (hγ_in_U : ∀ t ∈ Icc 0 1, γ t ∈ U)
      (h_deriv_bd : ∃ D, ∀ t ∈ Icc 0 1, ‖deriv γ.toPath.extend t‖ ≤ D) :
      ∀ w, dixonFunction f U γ.toPiecewiseC1Path w = 0
  ```
  Chains B-1/2/3/4 + `dixonFunction_eq_zero_of_bounds` with automatically
  derived bounds on γ (from continuity on compact) and f∘γ (from continuity).

### [CLEANUP-B] Run /cleanup on Dixon files

- **Status**: open
- **File**: `ForMathlib/DixonTheorem.lean`, `ForMathlib/DixonDiff.lean`
- **Depends on**: B-5
- **Parallel**: no
- **Type**: cleanup

### [B-6] Close null-hom simple-pole theorem

- **Status**: open
- **File**: `ForMathlib/HigherOrderAssembly.lean`
- **Depends on**: A-2, B-5, CLEANUP-B
- **Parallel**: no
- **Description**: Upgrade `hasCauchyPVOn_simplePoles_nullHomologous_closed`
  to discharge the w₀ and Dixon-zero oracles using A-2 and B-5. Result:
  a fully-closed simple-pole null-homologous HW 3.3 with only the
  paper's hypotheses.

### [C-1] Tangent-approximation around a crossing

- **Status**: open
- **File**: `ForMathlib/HigherOrderCancel.lean` (add section)
- **Depends on**: none
- **Parallel**: yes
- **Description**: Given `γ : PwC1Immersion x y`, crossing at `t₀ ∈ Ioo 0 1`
  with tangent `L = deriv γ t₀ ≠ 0`, and flatness of order `n` (`IsFlatOfOrder`),
  prove that for small `|t - t₀|`, `γ t - γ t₀ = (t - t₀) · L + O((t - t₀)^{n+1})`.
  This is the curve-to-line approximation enabling sector reduction.
- **API**: `tangentApproximation_of_isFlatOfOrder`

### [C-2] Curve CPV reduces to line CPV under A'

- **Status**: open
- **File**: `ForMathlib/HigherOrderCancel.lean`
- **Depends on**: C-1
- **Parallel**: no (same file)
- **Description**: Given a pole of order `k` at `s`, flatness A' of order
  `≥ k`, prove that the CPV integral of `(z - s)^{-k}` along γ near the
  crossing equals the CPV along the tangent line plus a convergent
  remainder (which vanishes in the limit by flatness).
- **API**: `cpv_near_crossing_eq_cpv_tangent_of_flat`

### [C-3] A'+B give higher-order cancellation

- **Status**: open
- **File**: `ForMathlib/HigherOrderCancel.lean`
- **Depends on**: C-2
- **Parallel**: no
- **Description**: Combine C-2 + `higherOrder_sector_cancel_odd` +
  `higherOrder_sector_cancel_even_of_flat` to show that the higher-order
  Laurent coefficients (orders 2 through poleOrder) contribute zero to
  the CPV.
- **API**: `higherOrder_cancel_of_A'_and_B`

### [CLEANUP-C] Run /cleanup on HigherOrderCancel.lean

- **Status**: open
- **File**: `ForMathlib/HigherOrderCancel.lean`
- **Depends on**: C-1, C-2, C-3
- **Parallel**: no
- **Type**: cleanup

### [C-4] Close higher-order HW 3.3 via A'/B

- **Status**: open
- **File**: `ForMathlib/HigherOrderAssembly.lean`
- **Depends on**: B-6, C-3, CLEANUP-C
- **Parallel**: no
- **Description**: Compose B-6 (simple-pole null-hom closure) with C-3
  (higher-order cancellation under A'+B) into
  `generalizedResidueTheorem_closed` — the final fully-closed HW 3.3
  taking only: open U, f differentiable on U \ S, γ null-hom PwC1Immersion,
  SatisfiesConditionA', SatisfiesConditionB, endpoint/uniqueness technical
  conditions. No oracle hypotheses.

### [CLEANUP-FINAL] Run /cleanup on all modified files

- **Status**: open
- **File**: all modified files
- **Depends on**: C-4
- **Parallel**: no
- **Type**: cleanup
