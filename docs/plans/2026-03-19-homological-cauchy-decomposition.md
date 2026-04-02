# HomologicalCauchy.lean Decomposition Plan

> **For agentic workers:** Use superpowers:subagent-driven-development to implement.

**Goal:** Decompose all 8 proofs >50 lines into helper lemmas (target: main theorems <15 lines)

**File:** `LeanModularForms/GeneralizedResidueTheory/HomologicalCauchy.lean` (~2800 lines, 0 sorries, 0 warnings)

## Proofs to Decompose

| # | Proof | Lines | Target |
|---|-------|-------|--------|
| 1 | `ftc_piecewise_contour` | 142 | ~15 |
| 2 | `dixonFunction_tendsto_zero` | 155 | ~15 |
| 3 | `contourIntegral_eq_zero_of_meromorphic_residue_zero_finset_nh` | 227 | ~12 |
| 4 | `contourIntegral_eq_zero_of_meromorphic_residue_zero_nh` | 93 | ~12 |
| 5 | `dixonH1_eq` | 86 | ~12 |
| 6 | `dixonH2_differentiableAt` | 65 | ~15 |
| 7 | `integrand_intervalIntegrable_of_avoids` | 53 | ~35 |
| 8 | `isNullHomologous_of_convex` | 43 | ~30 |

## Phase 0: Shared Infrastructure

### S1: `PiecewiseC1Curve.mem_Ioo_of_mem_Icc_not_partition`
Appears 12 times. Proves `t ∈ Icc γ.a γ.b \ partition → t ∈ Ioo γ.a γ.b`.

### S3: `windingNumber_zero_on_ball_of_integer_continuous_connected`
Used in `dixonFunction_differentiable` and `dixonFunction_tendsto_zero`. The argument:
integer-valued + continuous on connected ball + value 0 at center → identically 0.

## Phase 1: Low-Level Helpers

### For Proof 1 (ftc_piecewise_contour):
- `ftc_base_case_no_interior_partition` — FTC on smooth sub-interval
- `partition_filter_card_lt_of_split` — Strict cardinality decrease when splitting

### For Proof 5 (dixonH1_eq):
- `dslope_expand_off_curve` — Pointwise dslope expansion
- `dixonH1_fgamma_div_integrable` — Integrability of f(γ(t))/(γ(t)-w)·γ'(t)

### For Proof 6 (dixonH2_differentiableAt):
- `infDist_lb_of_ball` — Distance lower bound for ball points (shared with dixonFunction_differentiable)
- `ball_avoids_curve_of_infDist` — Points in small ball miss the curve

## Phase 2: Mid-Level Helpers

### For Proof 2 (dixonFunction_tendsto_zero):
- `dist_lb_from_image_bound` — |γ(t) - w| ≥ |w| - R
- `dixonH2_norm_bound` — ‖h₂(w)‖ ≤ M_f·M_d·(b-a)/(‖w‖-R)
- `windingNumber_zero_of_large_norm` — n(γ,w) = 0 for large |w|

### For Proof 4 (single-pole nh):
- `regularPart_update_differentiableOn` — Updated regular part is DifferentiableOn U
- `contourIntegral_update_eq_contourIntegral_off_point` — Integral unchanged when γ avoids update point (shared with proof 3)

## Phase 3: High-Level Helpers

### For Proof 3 (finset_nh, 227 lines):
- `contourIntegral_sum_principalParts_eq_zero` — ∮ Σ pp_s = 0
- `analytic_correction_differentiableOn` — Corrected g is DifferentiableOn U

## Implementation Order

Phase 0 → Phase 1 → Phase 2 → Phase 3, with proofs 7 and 8 benefiting from Phase 0 only.
