# Convex → Null-Homologous Corollary Refactoring

**Goal:** Make all convex-domain theorems into corollaries of null-homologous versions.

## Phase 1: Create 5 missing NH versions (in HomologicalCauchy.lean)

| New theorem | Based on | Key change |
|-------------|----------|------------|
| `generalizedResidueTheorem'_nh` | `generalizedResidueTheorem'` | Replace FTC with Dixon |
| `generalizedResidueTheorem_nh` | `generalizedResidueTheorem` | Use nh' + cpv_exists_inv_sub |
| `generalizedResidueTheorem_higher_order_nh` | `_higher_order` | Use nh + limit arithmetic |
| `generalizedResidueTheorem_higher_order_simple_nh` | `_simple` | Corollary of nh |
| `holomorphic_cpv_tendsto_zero_nh` | `_on_convex` | Replace FTC with Dixon |

## Phase 2: Convert 16 convex theorems to corollaries (bottom-up)

**Layer 1 (leaves):** R1, R2, M1, M2, M3
**Layer 2:** G1, G2, P1, H1
**Layer 3:** G3, H2, H3
**Layer 4:** G4, G5, F1, F2

Each becomes: `apply nh_version; exact isNullHomologous_of_convex ...`

## Phase 3: Delete unused private helpers

- `holomorphic_closed_integral_zero` (2 copies)
- `contourIntegral_eq_zero_of_differentiableOn_convex`
- `holomorphic_integral_vanish_convex`

## Estimated savings: ~550-650 lines net
